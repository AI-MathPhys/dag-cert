"""Reproducible multi-seed benchmark; Python standard library only.

Run: python -m dag_mcts.benchmark --iterations 5000 --seeds 40
"""

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import statistics
import time

from .graph import feature_lattice, trap
from .search import BellmanMCTS, NaiveAllAncestors, TreeUCT
from .routing import RoutingMCTS


METHODS = ("tree_uct", "naive_all", "dag_path", "dag_sampled", "dag_full", "routing_snis")


def make_search(method, graph, exploration, extra_draws, seed,
                routing_epsilon=0.5, routing_decay=None):
    if method not in METHODS:
        raise ValueError(f"Unknown method {method!r}")
    if method == "routing_snis":
        return RoutingMCTS(graph, epsilon0=routing_epsilon, decay=routing_decay,
                           seed=seed + 3_000_017)
    if method == "tree_uct":
        return TreeUCT(graph, exploration)
    if method == "naive_all":
        return NaiveAllAncestors(graph, exploration)
    return BellmanMCTS(graph, exploration, extra_draws=extra_draws if method == "dag_sampled" else 0,
                       seed=seed + 2_000_003, full_backups=method == "dag_full")


def make_problem(name):
    if name == "trap":
        return trap()
    if name.startswith("lattice"):
        deterministic = name.endswith("_det")
        digits = name[len("lattice"):].removesuffix("_det")
        return feature_lattice(int(digits), noisy=not deterministic)
    raise ValueError(f"Unknown problem {name!r}")


def checkpoints_for(iterations):
    points = {iterations}
    power = 1
    while power <= iterations:
        points.update(n * power for n in (1, 3) if n * power <= iterations)
        power *= 10
    return sorted(points)


def run_one(problem, method, seed, iterations, exploration, extra_draws,
            routing_epsilon=0.5, routing_decay=None):
    started = time.perf_counter()
    search = make_search(method, problem.graph, exploration, extra_draws, seed,
                         routing_epsilon, routing_decay)
    oracle = problem.oracle(seed)
    init_seconds = time.perf_counter() - started
    optimum = problem.graph.optimal_values(problem.means)
    rows = []
    previous = 0
    elapsed = 0.0
    for checkpoint in checkpoints_for(iterations):
        started = time.perf_counter()
        for _ in range(previous, checkpoint):
            search.step(oracle)
        elapsed += time.perf_counter() - started
        # Evaluation is outside timed search and never changes its state.
        recommended = search.recommend()
        leaf = recommended[-1]
        first = recommended[1] if len(recommended) > 1 else recommended[0]
        leaf_regret = max(0.0, optimum[problem.graph.root] - problem.means[leaf])
        row = dict(problem=problem.name, method=method, seed=seed, iterations=checkpoint,
                   leaf_regret=leaf_regret,
                   root_regret=max(0.0, optimum[problem.graph.root] - optimum[first]),
                   optimal_leaf=int(leaf_regret < 1e-12),
                   recommendation=problem.graph.labels[leaf],
                   unique_leaves_sampled=sum(n > 0 for n in oracle.counts.values()),
                   materialized_nodes=search.materialized_nodes,
                   search_seconds=elapsed, init_seconds=init_seconds,
                   good_leaf_pulls=oracle.counts.get(3, 0) if problem.name == "trap" else "",
                   first_good_reward=oracle.first_reward.get(3, "") if problem.name == "trap" else "",
                   routing_epsilon=search.epsilon(checkpoint) if method == "routing_snis" else "",
                   routing_max_weight=search.max_weight if method == "routing_snis" else "",
                   routing_root_ess=search.effective_sample_size(problem.graph.root)
                   if method == "routing_snis" else "")
        row.update(search.work.to_dict())
        rows.append(row)
        previous = checkpoint
    return rows


def mean_interval(values):
    """Descriptive normal-approximation interval over independent seed replicates."""
    mean = statistics.mean(values)
    halfwidth = 1.96 * statistics.stdev(values) / math.sqrt(len(values)) if len(values) > 1 else 0
    return {"mean": mean, "ci95_halfwidth": halfwidth}


def summarize(rows, iterations):
    groups = {}
    for row in rows:
        groups.setdefault((row["problem"], row["method"], row["iterations"]), []).append(row)
    metrics = ("leaf_regret", "root_regret", "optimal_leaf", "work_units", "search_seconds",
               "value_writes", "backup_edge_reads", "ancestor_edge_reads", "extra_refreshes",
               "materialized_nodes", "unique_leaves_sampled")
    summaries = []
    for (problem, method, checkpoint), group in sorted(groups.items()):
        entry = dict(problem=problem, method=method, iterations=checkpoint, seeds=len(group))
        entry.update({metric: mean_interval([r[metric] for r in group]) for metric in metrics})
        summaries.append(entry)
    paired = []
    final = {(r["problem"], r["method"], r["seed"]): r for r in rows if r["iterations"] == iterations}
    for problem in sorted({r["problem"] for r in rows}):
        for anchor in ("dag_sampled", "routing_snis"):
            for comparator in METHODS:
                if comparator == anchor or (anchor == "dag_sampled" and comparator == "routing_snis"):
                    continue
                seeds = sorted(seed for p, method, seed in final
                               if p == problem and method == anchor
                               and (p, comparator, seed) in final)
                if not seeds:
                    continue
                entry = dict(problem=problem, comparison=anchor + " minus " + comparator)
                for metric in ("leaf_regret", "search_seconds", "work_units"):
                    differences = [final[problem, anchor, seed][metric] -
                                   final[problem, comparator, seed][metric] for seed in seeds]
                    entry[metric + "_difference"] = mean_interval(differences)
                paired.append(entry)
    return summaries, paired


def write_report(path, metadata, summaries, paired, rows):
    iterations = metadata["iterations"]
    lines = ["# Benchmark results", "",
             f"{metadata['seeds']} seeds, {iterations:,} oracle calls per method and problem; "
             f"exploration c={metadata['exploration']}, ancestor draws K={metadata['extra_draws']}.", "",
             f"Routing uses epsilon_t={metadata['routing_epsilon']} * t^(-alpha), with "
             f"alpha={metadata['routing_decay'] if metadata['routing_decay'] is not None else '1/(2H)'}. "
             "Its policy and value estimator differ from UCT/Bellman; this is a comparison of "
             "complete methods, not an isolated backup ablation. ESS is not used for selection.", "",
             "All algorithms receive the same known topology and action order. For each replicate, "
             "the kth reward at each canonical leaf is the same across methods. Planner randomness "
             "is separate. Method execution order is shuffled per seed to reduce timing-order effects.", "",
             "Intervals are descriptive mean +/- 1.96 standard errors across seeds, not simultaneous "
             "confidence sequences. Search timing includes selection, oracle sampling, ancestor selection, "
             "and backups; it excludes initialization, checkpoint scoring, plotting, and file I/O.", "",
             "| Problem | Method | Leaf regret (mean +/- 95% halfwidth) | Optimal leaf | Work units | Search seconds | Search nodes |",
             "|---|---|---:|---:|---:|---:|---:|"]
    for r in summaries:
        if r["iterations"] == iterations:
            lines.append(f"| {r['problem']} | {r['method']} | {r['leaf_regret']['mean']:.4f} +/- "
                         f"{r['leaf_regret']['ci95_halfwidth']:.4f} | {r['optimal_leaf']['mean']:.1%} | "
                         f"{r['work_units']['mean']:,.0f} | {r['search_seconds']['mean']:.4f} | "
                         f"{r['materialized_nodes']['mean']:,.0f} |")
    lines.extend(["", "Work units sum measured selection/backup/ancestor/policy/routing edge reads, "
                  "value writes, count writes, and routing-mass/weighted-statistic writes. "
                  "They exclude set operations, sorting, RNG internals and allocation; "
                  "they are an accounting proxy. Search nodes count algorithm statistic records, not "
                  "bytes; all methods also have access to the common DAG topology.", "",
                  "## Paired final leaf-regret differences", "",
                  "Negative differences favor the first method in each comparison. The same seeds are paired; these "
                  "intervals are descriptive and unadjusted for multiple comparisons.", "",
                  "| Problem | Comparison | Mean difference +/- 95% halfwidth |", "|---|---|---:|"])
    for r in paired:
        ci = r["leaf_regret_difference"]
        lines.append(f"| {r['problem']} | {r['comparison']} | {ci['mean']:.4f} +/- {ci['ci95_halfwidth']:.4f} |")
    failures = [r for r in rows if r["problem"] == "trap" and r["method"] == "naive_all"
                and r["iterations"] == iterations and r["first_good_reward"] == 0]
    if failures:
        stuck = sum(r["good_leaf_pulls"] == 1 for r in failures)
        lines.extend(["", f"Trap diagnostic: {len(failures)} replicates initially observed zero at the "
                      f"good leaf; naive-all sampled that leaf only once in {stuck}/{len(failures)} "
                      "of those replicates. This is the predicted starvation event, whose probability "
                      "under this initialization is 0.2."])
    lines.extend(["", "## Interpretation limits", "",
                  "- These are small synthetic, fully known DAGs. They are not feature-classifier results.",
                  "- Root-action regret can be zero for several insertion orders; terminal-leaf regret is primary.",
                  "- Bellman methods use max backups; tree UCT uses rollout means. The path/full Bellman "
                  "ablations isolate the ancestor scheduling effect from that change in estimator.",
                  "- Routing estimates historical behavior-policy values using self-normalized weights. "
                  "Its optimal-control guarantee needs the prescribed slow exploration decay. "
                  "Exact routing scans the sampled leaf's full ancestor closure; it does not cap update cost.",
                  "- The convergence proof is asymptotic. These experiments do not establish a rate "
                  "or universal speed advantage. Cheap oracles make bookkeeping prominent.",
                  "- The simulated reward landscape, c, initial values, and action order are fixed. "
                  "Broader sensitivity studies are needed before drawing general performance conclusions.", ""])
    path.write_text("\n".join(lines), encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--iterations", type=int, default=5000)
    parser.add_argument("--seeds", type=int, default=40)
    parser.add_argument("--seed-offset", type=int, default=0)
    parser.add_argument("--exploration", type=float, default=0.7)
    parser.add_argument("--extra-draws", type=int, default=4)
    parser.add_argument("--routing-epsilon", type=float, default=0.5)
    parser.add_argument("--routing-decay", type=float, default=None,
                        help="Default 1/(2H); must be positive and less than 1/H")
    parser.add_argument("--problems", nargs="+", default=["trap", "lattice6", "lattice8"])
    parser.add_argument("--methods", nargs="+", choices=METHODS, default=list(METHODS))
    parser.add_argument("--output", type=Path, default=Path("results/routing"))
    args = parser.parse_args(argv)
    if args.iterations < 1 or args.seeds < 2 or args.extra_draws < 0:
        parser.error("Need positive iterations, at least two seeds, and nonnegative extra draws")
    args.output.mkdir(parents=True, exist_ok=True)
    problems = [make_problem(name) for name in args.problems]
    metadata = {key: value for key, value in vars(args).items() if key != "output"}
    metadata.update(python=platform.python_version(), platform=platform.platform(),
                    checkpoints=checkpoints_for(args.iterations),
                    sources={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in sorted(Path(__file__).parent.glob("*.py"))},
                    graphs=[dict(name=p.name, states=len(p.graph), leaves=len(p.means),
                                 edges=sum(map(len, p.graph.children)),
                                 maximum_depth=max(p.graph.depth),
                                 routing_decay=args.routing_decay if args.routing_decay is not None
                                 else 1 / (2 * max(1, max(p.graph.depth)))) for p in problems])
    rows = []
    total = len(problems) * args.seeds
    completed = 0
    started = time.perf_counter()
    for problem in problems:
        for seed in range(args.seed_offset, args.seed_offset + args.seeds):
            methods = list(args.methods)
            random.Random(seed + 5_000_011).shuffle(methods)
            for method in methods:
                rows.extend(run_one(problem, method, seed, args.iterations,
                                    args.exploration, args.extra_draws,
                                    args.routing_epsilon, args.routing_decay))
            completed += 1
            if completed % 5 == 0 or completed == total:
                print(f"{completed}/{total} problem-seed groups; {time.perf_counter()-started:.1f}s", flush=True)
    summaries, paired = summarize(rows, args.iterations)
    with (args.output / "runs.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    (args.output / "summary.json").write_text(json.dumps(dict(metadata=metadata, summary=summaries,
                                                               paired_comparisons=paired), indent=2), encoding="utf-8")
    write_report(args.output / "REPORT.md", metadata, summaries, paired, rows)
    print(f"Results written to {args.output.resolve()}", flush=True)


if __name__ == "__main__":
    main()
