"""Experiment 4: Representation-Aware Exact-Regret Comparison & Paid Pre-Run Selector.

Compares three exact shared-support regret architectures (all exposing the identical
Theorem 2.2 exact-regret oracle on identical trajectories):
1. Direct-Graph-Regret: Quotient DAG MAX heaps for L_t(a) + global terminal upper-bound
   heap with bitmask outside-witness scan.
2. Charged-Dual-Covers (Theorem 3.1): Positive/negative dyadic interval covers over a
   shared binary segment tree + per-action and global indexed heaps.
3. Factorized-Regret: Retains intermediate quotient gates for S(a) and covers Z \\ S(a)
   using maximal support-disjoint internal gates.
4. Paid-Selector: Computes lightweight structural diagnostics inside the cold timer and
   dispatches to the predicted lowest-cost representation before rollout 1; validated
   both end-to-end (charging feature extraction) and via Leave-One-Family-Out (LOFO)
   cross-validation with zero test leakage.
"""
from __future__ import annotations

import argparse
import csv
import gc
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import statistics
import time

from dag_mcts.certified_uct import TranspositionUCT, UCTWork
from dag_mcts.compiled_retirement import leaf_order, quotient
from dag_mcts.graph import DAG, Problem
from dag_mcts.v2_benchmarks import (
    contiguous_window_dag,
    overlap_dag,
    samegame_depth_case,
    samegame_standard_endgame,
    structural_diagnostics,
)
from dag_mcts.v2_monitors import (
    ChargedDualCovers,
    DirectGraphRegretMonitor,
    FactorizedRegretMonitor,
)
from paper.uct_backup_families import funnel, wide_core
from paper.uct_frontier_families import catalog, coded


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/uct_v2_extensions/exp4_representation"

BASE_METHODS = ("direct-graph-regret", "dual-covers", "factorized-regret")
ALL_METHODS = (*BASE_METHODS, "paid-selector")
SEEDS = tuple(range(640001, 640005))  # 4 seeds x 2 counterbalanced repeats (8 runs/cell)
CAP = 50000
WALL_LIMIT_S = 1.0
DELTA = 0.05
C_UCT = 2.5
Q_CERT = 4


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract_paid_selector_features(graph: DAG, work: UCTWork) -> dict[str, float | int]:
    """Fast O(|V| + |E| + (|V|+|E|)*words) pre-run structural probe, fully charged to `work`."""
    qgraph, leaf_map, _ = quotient(graph, work)
    m = len(graph.leaves)
    h = max(1, (m - 1).bit_length() + 1)
    words = max(1, (m + 63) // 64)
    k = len(graph.children[graph.root])
    q_edges = sum(map(len, qgraph.children))
    q_internal = max(0, len(qgraph) - m - k - 1)

    # Compute root-action support bitmasks under both ID and DFS terminal layouts
    best_runs = math.inf
    for dfs in (False, True):
        leaves = leaf_order(graph, dfs, work)
        rank = {v: i for i, v in enumerate(leaves)}
        work.initialization += m
        masks = [0] * len(graph)
        for v in reversed(graph.order):
            ch = graph.children[v]
            if not ch:
                masks[v] = 1 << rank[v]
                work.statistic_writes += 1
            else:
                acc = 0
                for c in ch:
                    acc |= masks[c]
                    work.query_reads += words
                masks[v] = acc
                work.statistic_writes += words
        runs = 0
        for act in graph.children[graph.root]:
            x = masks[act]
            # Number of contiguous 1-runs in bitmask x equals popcount(x & ~(x << 1))!
            runs += (x & ~(x << 1)).bit_count()
            work.confidence_work += 2 * words
        if runs < best_runs:
            best_runs = runs

    # Count shared internal gates (in-degree >= 2 or out-degree >= 4 below action wrappers)
    first_wrap = qgraph.root - k
    shared_gates = sum(
        1 for v in range(first_wrap)
        if qgraph.children[v] and len(qgraph.parents[v]) >= 2
    )
    work.query_reads += max(1, first_wrap)

    est_dual_blocks = 2 * h * best_runs
    return {
        "leaves": m,
        "actions": k,
        "quot_edges": q_edges,
        "quot_internal": q_internal,
        "shared_gates": shared_gates,
        "best_root_runs": int(best_runs),
        "est_dual_blocks": int(est_dual_blocks),
        "frag_vs_qedges": est_dual_blocks / max(1, q_edges),
        "runs_per_action": best_runs / max(1, k),
    }


def choose_representation(feats: dict[str, float | int],
                          frag_threshold: float = 20.0,
                          direct_max_actions: int = 8) -> str:
    """Interpretable representation-selection rule over paid pre-run structural features."""
    # 1. Severe interval fragmentation across shared internal gates (e.g., Hadamard/parity grids
    #    where every linear layout forces Omega(r^3) dyadic blocks) -> Direct-Graph-Regret!
    if feats["shared_gates"] >= 16 and feats["frag_vs_qedges"] > frag_threshold:
        return "direct-graph-regret"
    # 2. Small action count with compact non-contiguous quotient graph -> Direct-Graph-Regret!
    if feats["actions"] <= direct_max_actions and feats["runs_per_action"] >= 2.5 and feats["quot_edges"] <= 250:
        return "direct-graph-regret"
    # 3. Default to Charged-Dual-Covers (O(log M) dyadic block maintenance + O(1) regret heap).
    return "dual-covers"


class PaidAdaptiveRegretMonitor:
    """Executes paid structural probe inside initialization and builds chosen exact-regret monitor."""

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box"):
        probe_work = UCTWork()
        self.features = extract_paid_selector_features(graph, probe_work)
        self.selected = choose_representation(self.features)
        if self.selected == "dual-covers":
            self.inner = ChargedDualCovers(graph, delta=delta, schedule=schedule, layout="best")
        elif self.selected == "factorized-regret":
            self.inner = FactorizedRegretMonitor(graph, delta=delta, schedule=schedule, mode="protected")
        else:
            self.inner = DirectGraphRegretMonitor(graph, delta=delta, schedule=schedule, mode="protected")
        # Add paid probe work into the inner monitor's work ledger!
        self.inner.work.initialization += probe_work.total
        self.probe_work = probe_work.total
        self.compile_work = self.inner.compile_work + probe_work.total
        self.work = self.inner.work
        self.evidence = self.inner.evidence
        self.info = {"selected": self.selected, **self.features}

    def step(self, leaf: int, reward: float) -> bool:
        return self.inner.step(leaf, reward)

    def query(self) -> tuple[int, float, float, float]:
        return self.inner.query()


CASES = (
    # Family group, config_name, builder_fn(seed)
    ("parity_grid", "coded_8", lambda s: coded(8, s)),
    ("parity_grid", "coded_16", lambda s: coded(16, s)),
    ("parity_grid", "coded_32", lambda s: coded(32, s)),
    ("contiguous_window", "window_64", lambda s: contiguous_window_dag(64, 16, seed=s, noisy=True)),
    ("contiguous_window", "window_256", lambda s: contiguous_window_dag(256, 24, seed=s, noisy=True)),
    ("contiguous_window", "window_1024", lambda s: contiguous_window_dag(1024, 32, seed=s, noisy=True)),
    ("common_core", "core_8", lambda s: wide_core(8, s)),
    ("common_core", "core_16", lambda s: wide_core(16, s)),
    ("common_core", "core_32", lambda s: wide_core(32, s)),
    ("catalog", "sparse_4", lambda s: catalog(4, s, "sparse")),
    ("catalog", "dense_4", lambda s: catalog(4, s, "dense")),
    ("dominated_funnel", "funnel_256", lambda s: funnel(256, s, exits=2)),
    ("dominated_funnel", "funnel_1024", lambda s: funnel(1024, s, exits=2)),
    ("overlap_dag", "overlap_256_rho50", lambda s: overlap_dag(256, 0.50, 0.36, seed=s, noisy=True)),
    ("samegame", "samegame_6x6_d3", lambda s: samegame_depth_case(6, 3, s, eps=0.08)),
    ("samegame", "samegame_std_d3", lambda s: samegame_standard_endgame(((s - 640001) % 20) + 1, depth=3, eps=0.05)),
)


def build_regret_monitor(graph: DAG, method: str):
    if method == "direct-graph-regret":
        return DirectGraphRegretMonitor(graph, delta=DELTA, schedule="box", mode="protected")
    if method == "dual-covers":
        return ChargedDualCovers(graph, delta=DELTA, schedule="box", layout="best")
    if method == "factorized-regret":
        return FactorizedRegretMonitor(graph, delta=DELTA, schedule="box", mode="protected")
    if method == "paid-selector":
        return PaidAdaptiveRegretMonitor(graph, delta=DELTA, schedule="box")
    raise ValueError(method)


def run_one(problem: Problem, eps: float, seed: int, method: str) -> dict:
    gc.collect()
    t0 = time.perf_counter()
    uct = TranspositionUCT(problem.graph, exploration=C_UCT, lazy=True)
    oracle = problem.oracle(seed)
    mon = build_regret_monitor(problem.graph, method)
    q = mon.query()
    certified = (not mon.evidence.conflict) and (q[1] <= eps)
    act = q[0] if certified else uct.recommend_action()
    t_init = time.perf_counter() - t0
    init_work = uct.work.total + mon.work.total
    dirty = False
    elapsed = t_init

    while not certified and not mon.evidence.conflict and uct.calls < CAP and elapsed < WALL_LIMIT_S:
        path, reward = uct.step(oracle)
        if mon.step(path[-1], reward):
            dirty = True
        if dirty and uct.calls % Q_CERT == 0:
            q = mon.query()
            dirty = False
            if not mon.evidence.conflict and q[1] <= eps:
                certified = True
                act = q[0]
        if not certified:
            act = uct.recommend_action()
        elapsed = time.perf_counter() - t0

    calls = uct.calls
    work = uct.work.total + mon.work.total - calls + getattr(oracle, "operations", 0)
    mon_work = mon.work.total
    comp_work = getattr(mon, "compile_work", 0)
    selected = getattr(mon, "selected", method)
    feats = getattr(mon, "features", None)
    del mon, uct
    end_s = time.perf_counter() - t0

    values = problem.graph.optimal_values(problem.means)
    opt = values[problem.graph.root]
    true_reg = max(0.0, opt - values[problem.graph.children[problem.graph.root][act]])
    if certified:
        assert true_reg <= eps + 1e-12

    returned = bool(certified and end_s <= WALL_LIMIT_S)
    return {
        "method": method,
        "selected": selected,
        "steps": calls,
        "certified": certified,
        "returned": returned,
        "init_ms": 1000.0 * t_init,
        "end_ms": 1000.0 * end_s,
        "restricted_ms": 1000.0 * (end_s if returned else WALL_LIMIT_S),
        "init_work": init_work,
        "compile_work": comp_work,
        "work": work,
        "monitor_work": mon_work,
        "true_regret": true_reg,
        "features": feats,
    }


def evaluate_lofo_selector(rows: list[dict]) -> dict:
    """Leave-One-Family-Out (LOFO) cross-validation tuning threshold grid on F-1 families."""
    # Group base-method runs by (family, config, seed)
    instances: dict[tuple[str, str, int], dict] = {}
    for r in rows:
        key = (r["family"], r["config"], r["seed"])
        inst = instances.setdefault(key, {"times": {}, "works": {}, "features": None})
        if r["method"] in BASE_METHODS:
            inst["times"].setdefault(r["method"], []).append(r["restricted_ms"])
            inst["works"].setdefault(r["method"], []).append(r["work"])
        elif r["method"] == "paid-selector" and r["features"] is not None:
            inst["features"] = r["features"]

    # Average repeats per (family, config, seed, method)
    clean = []
    for (fam, cfg, seed), d in sorted(instances.items()):
        if d["features"] is None or len(d["times"]) < len(BASE_METHODS):
            continue
        clean.append({
            "family": fam,
            "config": cfg,
            "seed": seed,
            "features": d["features"],
            "ms": {m: statistics.mean(d["times"][m]) for m in BASE_METHODS},
            "work": {m: statistics.mean(d["works"][m]) for m in BASE_METHODS},
        })

    families = sorted(set(x["family"] for x in clean))
    frag_grid = (12.0, 20.0, 30.0, 50.0)
    act_grid = (4, 6, 8, 10)

    held_out_ratios = []
    oracle_matches = 0
    by_family = {}

    for held_fam in families:
        train = [x for x in clean if x["family"] != held_fam]
        test = [x for x in clean if x["family"] == held_fam]

        # Pick (frag_th, act_th) minimizing geometric-mean work ratio vs per-instance best on train
        best_params = (1.6, 12)
        best_loss = math.inf
        for f_th in frag_grid:
            for a_th in act_grid:
                loss = sum(
                    math.log(x["work"][choose_representation(x["features"], f_th, a_th)]
                             / min(x["work"].values()))
                    for x in train
                ) / max(1, len(train))
                if loss < best_loss:
                    best_loss = loss
                    best_params = (f_th, a_th)

        fam_ratios = []
        fam_work_ratios = []
        for x in test:
            pred = choose_representation(x["features"], *best_params)
            best_m = min(BASE_METHODS, key=lambda m: x["work"][m])
            if pred == best_m:
                oracle_matches += 1
            r_ms = x["ms"][pred] / min(x["ms"].values())
            r_wk = x["work"][pred] / min(x["work"].values())
            fam_ratios.append(r_ms)
            fam_work_ratios.append(r_wk)
            held_out_ratios.append(r_ms)

        by_family[held_fam] = {
            "n_test": len(test),
            "chosen_params": {"frag_threshold": best_params[0], "direct_max_actions": best_params[1]},
            "median_time_ratio_to_oracle": statistics.median(fam_ratios),
            "median_work_ratio_to_oracle": statistics.median(fam_work_ratios),
        }

    return {
        "total_instances": len(clean),
        "lofo_work_oracle_accuracy": oracle_matches / max(1, len(clean)),
        "lofo_median_time_ratio_to_oracle": statistics.median(held_out_ratios) if held_out_ratios else 1.0,
        "by_held_out_family": by_family,
    }


def summarize(dest: Path) -> dict:
    rows = [json.loads(line) for line in (dest / "runs.jsonl").read_text().splitlines()]
    configs = [cfg for _, cfg, _ in CASES]
    summary_rows = []
    for fam, cfg, _ in CASES:
        c_rows = [r for r in rows if r["config"] == cfg]
        if not c_rows:
            continue
        for meth in ALL_METHODS:
            grp = [r for r in c_rows if r["method"] == meth]
            if not grp:
                continue
            dual_grp = [r for r in c_rows if r["method"] == "dual-covers"]
            dual_ms = statistics.median(r["restricted_ms"] for r in dual_grp)
            dual_wk = statistics.median(r["work"] for r in dual_grp)
            selected_counts: dict[str, int] = {}
            for r in grp:
                selected_counts[r["selected"]] = selected_counts.get(r["selected"], 0) + 1
            dom_sel = max(selected_counts.items(), key=lambda kv: kv[1])[0]
            summary_rows.append({
                "family": fam,
                "config": cfg,
                "method": meth,
                "dominant_selected": dom_sel,
                "n_runs": len(grp),
                "returned": sum(int(r["returned"]) for r in grp),
                "med_tau": statistics.median(r["steps"] for r in grp),
                "med_init_ms": statistics.median(r["init_ms"] for r in grp),
                "med_restricted_ms": statistics.median(r["restricted_ms"] for r in grp),
                "mean_restricted_ms": statistics.mean(r["restricted_ms"] for r in grp),
                "med_compile_work": statistics.median(r["compile_work"] for r in grp),
                "med_work": statistics.median(r["work"] for r in grp),
                "time_ratio_vs_dual": statistics.median(r["restricted_ms"] for r in grp) / max(1e-6, dual_ms),
                "work_ratio_vs_dual": statistics.median(r["work"] for r in grp) / max(1.0, dual_wk),
            })

    with (dest / "representation_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(summary_rows[0].keys()))
        writer.writeheader()
        writer.writerows(summary_rows)

    lofo = evaluate_lofo_selector(rows)
    (dest / "lofo_selector_audit.json").write_text(json.dumps(lofo, indent=2))
    (dest / "summary.json").write_text(json.dumps(lofo, indent=2))
    return lofo


def run(dest: Path = DEST, smoke: bool = False) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    cases = CASES[:4] if smoke else CASES
    seeds = SEEDS[:2] if smoke else SEEDS

    rng = random.Random(640999)
    blocks = []
    for c_idx in range(len(cases)):
        for seed in seeds:
            meths = list(ALL_METHODS)
            rng.shuffle(meths)
            blocks.append((c_idx, seed, 0, meths))
            if not smoke:
                blocks.append((c_idx, seed, 1, meths[::-1]))
    rng.shuffle(blocks)

    print(f"[Exp 4] Running {len(blocks)} counterbalanced representation blocks...", flush=True)
    with (dest / "runs.jsonl").open("w") as out:
        for idx, (c_idx, seed, rep, meths) in enumerate(blocks, 1):
            fam, cfg, builder = cases[c_idx]
            prob, eps = builder(seed)
            step_counts = []
            for pos, meth in enumerate(meths):
                row = run_one(prob, eps, seed, meth)
                row.update(family=fam, config=cfg, seed=seed, repeat=rep, position=pos)
                out.write(json.dumps(row) + "\n")
                if row["returned"]:
                    step_counts.append(row["steps"])
            # Verify exact stopping-time equivalence across all certified exact-regret representations!
            if len(step_counts) >= 2 and all(r == step_counts[0] for r in step_counts):
                pass
            elif len(step_counts) == len(meths):
                assert len(set(step_counts)) == 1, (cfg, seed, step_counts)
            if idx % 32 == 0 or idx == len(blocks):
                out.flush()
                print(f"  blocks: {idx}/{len(blocks)}", flush=True)

    manifest = {
        "experiment": "exp4_representation_selector",
        "smoke": smoke,
        "cases": [c[1] for c in cases],
        "methods": ALL_METHODS,
        "seeds": seeds,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "sha256_runs": digest(dest / "runs.jsonl"),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    if not smoke:
        agg = summarize(dest)
        print("[Exp 4] LOFO Selector Summary:", json.dumps(agg, indent=2), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEST)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()
    if args.summarize_only:
        print(json.dumps(summarize(args.out), indent=2))
    else:
        run(args.out, smoke=args.smoke)
