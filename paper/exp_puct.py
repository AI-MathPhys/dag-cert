"""Experiment 2: UCT vs. Fixed-Prior PUCT Confidence-Maintenance Architectures.

Evaluates two distinct regimes corresponding to Section 4 (Appendices E & F):
1. Part A — Deterministic Fixed-Prior Root-PUCT Work Separation (Theorem 4.1 / Cor. E.6):
   Evaluates puct_root_funnel(m) across m in {16, 64, 256, 1024, 4096} under
   unit_lambda (exact Theorem 4.1 parameterization), informative, and misleading
   strictly positive priors. Compares Graph-Eager, Protected-Selective,
   Decision-Selective, and Charged Dual Covers coupled within each prior.
2. Part B — Noisy Recursive-PUCT & Cross-Policy Comparison (Theorem 4.2 / Appendix F):
   Evaluates noisy Recursive-PUCT across uniform, informative, and misleading
   positive priors (plus a non-coupled TA-UCT reference) on noisy funnels
   (m=64, m=256 wide & narrow gap), noisy common core (r=16), parity grid (r=16),
   and overlapping-support DAG (M=256, rho=0.50). Directly quantifies strict
   nested-envelope change frequency vs. terminal revisits, parent deliveries,
   cold setup, total scalar work, peak memory, and wall-clock time.
   NOTE: Trajectories are coupled ONLY within each (case, policy_kind, prior_mode, seed)
   tuple; cross-policy UCT vs. PUCT runs generate distinct trajectories by design.
"""
from __future__ import annotations

import argparse
import csv
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import time
import tracemalloc

from dag_mcts.graph import DAG, Problem
from dag_mcts.puct import CertifiedSearchSession
from dag_mcts.v2_benchmarks import overlap_dag, puct_noisy_funnel, puct_root_funnel
from paper.uct_backup_families import binary_root
from paper.uct_frontier_families import coded


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/uct_v2_extensions/exp2_puct"

ROOT_SIZES = (16, 64, 256, 1024, 2048)
ROOT_PRIORS = ("unit_lambda", "informative", "misleading")
ROOT_METHODS = ("graph-eager", "protected-selective", "decision-selective", "dual-covers")
ROOT_SEEDS = tuple(range(620001, 620005))  # 4 seeds x 2 counterbalanced repeats (8 runs/cell)
ROOT_CAP = 120000
ROOT_WALL_S = 5.5

NOISY_PRIORS = ("uniform", "informative", "misleading")
NOISY_METHODS = ("graph-eager", "protected-selective", "decision-selective", "dual-covers")
NOISY_SEEDS = tuple(range(621001, 621005))  # 4 seeds x 2 counterbalanced repeats (8 runs/cell)
NOISY_CAP = 50000
NOISY_WALL_S = 1.0


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def wide_core_noisy(r: int = 16, seed: int = 0) -> tuple[Problem, float]:
    """Bernoulli shared common-core DAG with r+1 root actions and r^2 shared core leaves."""
    rows = [(), ()]
    leaves = list(range(2, r * r + 2))
    rows.extend([()] * (r * r))
    hub = binary_root(rows, leaves)
    actions = [1]
    priv_leaves = []
    for _ in range(r):
        own = len(rows)
        rows.append(())
        priv_leaves.append(own)
        actions.append(len(rows))
        rows.append((hub, own))
    random.Random(seed).shuffle(actions)
    rows[0] = tuple(actions)
    graph = DAG(rows)
    means = {1: 0.88}
    for z in leaves:
        means[z] = 0.16
    for z in priv_leaves:
        means[z] = 0.24
    return Problem(f"noisy_core_{r}", graph, means, ()), 0.12


def make_noisy_case(case_name: str, seed: int) -> tuple[Problem, float]:
    if case_name == "funnel_64_wide":
        return puct_noisy_funnel(64, seed=seed, gap=0.14, noisy=True)
    if case_name == "funnel_256_wide":
        return puct_noisy_funnel(256, seed=seed, gap=0.14, noisy=True)
    if case_name == "funnel_256_narrow":
        return puct_noisy_funnel(256, seed=seed, gap=0.07, noisy=True)
    if case_name == "core_16":
        return wide_core_noisy(16, seed=seed)
    if case_name == "coded_16":
        return coded(16, seed=seed)
    if case_name == "overlap_256_rho50":
        return overlap_dag(256, 0.50, 0.36, seed=seed, noisy=True)
    raise ValueError(f"Unknown noisy case: {case_name}")


NOISY_CASES = (
    "funnel_64_wide",
    "funnel_256_wide",
    "funnel_256_narrow",
    "core_16",
    "coded_16",
    "overlap_256_rho50",
)


def run_single(problem: Problem, eps: float, seed: int, policy_kind: str,
               prior_mode: str, method: str, delta: float, c_explore: float,
               schedule: str, cap: int, wall_limit: float,
               effective_m: int | None = None, q_cert: int = 1,
               measure_memory: bool = False) -> dict:
    gc.collect()
    if measure_memory:
        tracemalloc.start()
    t0 = time.perf_counter()
    sess = CertifiedSearchSession(
        problem, seed, policy_kind, method, eps,
        delta=delta, c_explore=c_explore, prior_mode=prior_mode,
        q_cert=q_cert, schedule=schedule, downstream="fixed_first",
        effective_m=effective_m,
    )
    t_init = time.perf_counter() - t0
    init_work = sess.work
    elapsed = t_init
    while (not sess.certified and not sess.monitor.evidence.conflict
           and sess.calls < cap and elapsed < wall_limit):
        sess.step()
        elapsed = time.perf_counter() - t0

    ev = sess.monitor.evidence
    b = getattr(sess.monitor, "bounds", None)
    calls = sess.calls
    cert = sess.certified
    act = sess.action
    work = sess.work
    pol_work = sess.policy.work.total
    mon_work = sess.monitor.work.total
    compile_work = getattr(sess.monitor, "compile_work", 0)
    messages = getattr(b, "messages", getattr(sess.monitor, "messages", 0))
    retired = getattr(b, "retired", 0)
    retired_root = getattr(b, "retired_root_actions", 0)
    dead_nodes = getattr(b, "dead_nodes", 0)
    skipped_dead = getattr(b, "skipped_dead", 0)
    first_cut = sess.first_cut
    first_root_cut = sess.first_root_cut
    strict_changes = ev.strict_changes
    lower_changes = ev.lower_changes
    upper_changes = ev.upper_changes
    conflict = ev.conflict

    # Dominated-exit revisit count (for funnel constructions where leaves 3 / 4 are dominated)
    dom_visits = sum(ev.counts[z] for z in problem.graph.leaves if problem.means[z] < 0.40)

    peak_kib = None
    if measure_memory:
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        peak_kib = peak / 1024.0

    del b, ev, sess
    end_s = time.perf_counter() - t0

    values = problem.graph.optimal_values(problem.means)
    opt_val = values[problem.graph.root]
    true_reg = max(0.0, opt_val - values[problem.graph.children[problem.graph.root][act]])
    if cert:
        assert true_reg <= eps + 1e-12

    returned = bool(cert and end_s <= wall_limit)
    return {
        "policy": policy_kind,
        "prior": prior_mode,
        "method": method,
        "steps": calls,
        "certified": cert,
        "returned": returned,
        "init_ms": 1000.0 * t_init,
        "end_ms": 1000.0 * end_s,
        "restricted_ms": 1000.0 * (end_s if returned else wall_limit),
        "init_work": init_work,
        "compile_work": compile_work,
        "work": work,
        "policy_work": pol_work,
        "monitor_work": mon_work,
        "messages": messages,
        "retired_edges": retired,
        "retired_root_actions": retired_root,
        "dead_nodes": dead_nodes,
        "skipped_dead_waves": skipped_dead,
        "first_cut": first_cut,
        "first_root_cut": first_root_cut,
        "strict_changes": strict_changes,
        "lower_changes": lower_changes,
        "upper_changes": upper_changes,
        "strict_change_rate": (strict_changes / calls) if calls > 0 else 0.0,
        "dominated_visits": dom_visits,
        "peak_kib": peak_kib,
        "true_regret": true_reg,
        "conflict": conflict,
    }


def verify_within_policy_coupling(dest: Path, smoke: bool = False) -> dict:
    """Verify exact trajectory & stopping coupling across numerical and decision-selective monitors."""
    checks = []
    # 1. Root-PUCT coupling check on m=256
    prob, eps = puct_root_funnel(256, seed=620001, alpha=0.25)
    for prior in (("unit_lambda",) if smoke else ROOT_PRIORS):
        c_exp = 3.0
        s_list = [
            CertifiedSearchSession(
                prob, 620001, "root_puct", m, eps,
                delta=0.05, c_explore=c_exp, prior_mode=prior,
                schedule="box", downstream="fixed_first", effective_m=3,
            )
            for m in ("graph-eager", "protected-selective", "decision-selective")
        ]
        while not s_list[0].certified and s_list[0].calls < 20000:
            outs = [s.step() for s in s_list]
            assert outs[0] == outs[1] == outs[2]
            assert s_list[0].certified == s_list[1].certified == s_list[2].certified
            assert s_list[0].query[0] == s_list[1].query[0] == s_list[2].query[0]
        checks.append({"regime": "root_puct", "prior": prior, "tau": s_list[0].calls, "coupled": True})

    # 2. Noisy Recursive-PUCT coupling check on funnel_64_wide
    nprob, neps = make_noisy_case("funnel_64_wide", seed=621001)
    for prior in (("uniform",) if smoke else NOISY_PRIORS):
        s_list = [
            CertifiedSearchSession(
                nprob, 621001, "recursive_puct", m, neps,
                delta=0.05, c_explore=2.5, prior_mode=prior,
                schedule="noisy_puct", q_cert=1,
            )
            for m in ("graph-eager", "protected-selective", "decision-selective")
        ]
        while not s_list[0].certified and s_list[0].calls < 15000:
            outs = [s.step() for s in s_list]
            assert outs[0] == outs[1] == outs[2]
            assert s_list[0].certified == s_list[1].certified == s_list[2].certified
            assert s_list[0].query[0] == s_list[1].query[0] == s_list[2].query[0]
        checks.append({"regime": "recursive_puct", "prior": prior, "tau": s_list[0].calls, "coupled": True})

    out = {"checks": checks, "all_coupled": True}
    (dest / "coupling_audit.json").write_text(json.dumps(out, indent=2))
    return out


def summarize(dest: Path) -> dict:
    root_runs = [json.loads(line) for line in (dest / "root_puct_runs.jsonl").read_text().splitlines()]
    noisy_runs = [json.loads(line) for line in (dest / "noisy_puct_runs.jsonl").read_text().splitlines()]
    mem_runs = [json.loads(line) for line in (dest / "memory_runs.jsonl").read_text().splitlines()]

    # Part A summary CSV
    root_rows = []
    for prior in ROOT_PRIORS:
        for m in ROOT_SIZES:
            for meth in ROOT_METHODS:
                grp = [r for r in root_runs if (r["prior"], r["m"], r["method"]) == (prior, m, meth)]
                if not grp:
                    continue
                eag_grp = [r for r in root_runs if (r["prior"], r["m"], r["method"]) == (prior, m, "graph-eager")]
                eag_work_med = statistics.median(r["work"] for r in eag_grp)
                eag_ms_med = statistics.median(r["restricted_ms"] for r in eag_grp)
                root_rows.append({
                    "prior": prior,
                    "m": m,
                    "method": meth,
                    "n_runs": len(grp),
                    "returned": sum(int(r["returned"]) for r in grp),
                    "med_tau": statistics.median(r["steps"] for r in grp),
                    "med_dom_visits": statistics.median(r["dominated_visits"] for r in grp),
                    "med_strict_changes": statistics.median(r["strict_changes"] for r in grp),
                    "med_messages": statistics.median(r["messages"] for r in grp),
                    "med_init_ms": statistics.median(r["init_ms"] for r in grp),
                    "med_restricted_ms": statistics.median(r["restricted_ms"] for r in grp),
                    "med_work": statistics.median(r["work"] for r in grp),
                    "med_monitor_work": statistics.median(r["monitor_work"] for r in grp),
                    "work_ratio_vs_eager": statistics.median(r["work"] for r in grp) / max(1.0, eag_work_med),
                    "time_ratio_vs_eager": statistics.median(r["restricted_ms"] for r in grp) / max(1e-6, eag_ms_med),
                })

    with (dest / "root_puct_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(root_rows[0].keys()))
        writer.writeheader()
        writer.writerows(root_rows)

    # Part B summary CSV (including peak memory from memory_runs)
    mem_lookup: dict[tuple[str, str, str, str], float] = {}
    for case in NOISY_CASES:
        for pol in ("recursive_puct", "uct"):
            priors = NOISY_PRIORS if pol == "recursive_puct" else ("none",)
            for pr in priors:
                for meth in NOISY_METHODS:
                    mgrp = [r["peak_kib"] for r in mem_runs
                            if (r["case"], r["policy"], r["prior"], r["method"]) == (case, pol, pr, meth)
                            and r["peak_kib"] is not None]
                    if mgrp:
                        mem_lookup[(case, pol, pr, meth)] = statistics.median(mgrp)

    noisy_rows = []
    for case in NOISY_CASES:
        for pol in ("recursive_puct", "uct"):
            priors = NOISY_PRIORS if pol == "recursive_puct" else ("none",)
            for pr in priors:
                eag_grp = [r for r in noisy_runs
                           if (r["case"], r["policy"], r["prior"], r["method"]) == (case, pol, pr, "graph-eager")]
                if not eag_grp:
                    continue
                eag_work = statistics.median(r["work"] for r in eag_grp)
                eag_mon_work = statistics.median(r["monitor_work"] for r in eag_grp)
                eag_ms = statistics.median(r["restricted_ms"] for r in eag_grp)
                for meth in NOISY_METHODS:
                    grp = [r for r in noisy_runs
                           if (r["case"], r["policy"], r["prior"], r["method"]) == (case, pol, pr, meth)]
                    if not grp:
                        continue
                    noisy_rows.append({
                        "case": case,
                        "policy": pol,
                        "prior": pr,
                        "method": meth,
                        "n_runs": len(grp),
                        "returned": sum(int(r["returned"]) for r in grp),
                        "med_tau": statistics.median(r["steps"] for r in grp),
                        "med_strict_changes": statistics.median(r["strict_changes"] for r in grp),
                        "med_strict_change_rate": statistics.median(r["strict_change_rate"] for r in grp),
                        "med_dom_visits": statistics.median(r["dominated_visits"] for r in grp),
                        "med_skipped_dead_waves": statistics.median(r["skipped_dead_waves"] for r in grp),
                        "med_messages": statistics.median(r["messages"] for r in grp),
                        "med_init_ms": statistics.median(r["init_ms"] for r in grp),
                        "med_restricted_ms": statistics.median(r["restricted_ms"] for r in grp),
                        "med_work": statistics.median(r["work"] for r in grp),
                        "med_monitor_work": statistics.median(r["monitor_work"] for r in grp),
                        "work_ratio_vs_eager": statistics.median(r["work"] for r in grp) / max(1.0, eag_work),
                        "mon_work_ratio_vs_eager": statistics.median(r["monitor_work"] for r in grp) / max(1.0, eag_mon_work),
                        "time_ratio_vs_eager": statistics.median(r["restricted_ms"] for r in grp) / max(1e-6, eag_ms),
                        "med_peak_kib": mem_lookup.get((case, pol, pr, meth), 0.0),
                    })

    with (dest / "noisy_puct_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(noisy_rows[0].keys()))
        writer.writeheader()
        writer.writerows(noisy_rows)

    summary = {
        "root_puct_total_runs": len(root_runs),
        "noisy_puct_total_runs": len(noisy_runs),
        "memory_runs": len(mem_runs),
        "root_puct_m1024_unit_lambda_work_ratio_dec_vs_eager": next(
            (r["work_ratio_vs_eager"] for r in root_rows
             if r["prior"] == "unit_lambda" and r["m"] == 1024 and r["method"] == "decision-selective"),
            None,
        ),
        "root_puct_m1024_unit_lambda_time_ratio_dec_vs_eager": next(
            (r["time_ratio_vs_eager"] for r in root_rows
             if r["prior"] == "unit_lambda" and r["m"] == 1024 and r["method"] == "decision-selective"),
            None,
        ),
        "root_puct_m2048_unit_lambda_work_ratio_dec_vs_eager": next(
            (r["work_ratio_vs_eager"] for r in root_rows
             if r["prior"] == "unit_lambda" and r["m"] == 2048 and r["method"] == "decision-selective"),
            None,
        ),
    }
    (dest / "summary.json").write_text(json.dumps(summary, indent=2))
    return summary


def run(dest: Path = DEST, smoke: bool = False) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    print("[Exp 2] Step 0: Verifying within-policy trajectory coupling...", flush=True)
    audit = verify_within_policy_coupling(dest, smoke=smoke)
    print(f"  PASS: {len(audit['checks'])} within-policy coupling checks passed.", flush=True)

    rng = random.Random(620999)
    root_sizes = (16, 256) if smoke else ROOT_SIZES
    root_priors = ("unit_lambda",) if smoke else ROOT_PRIORS
    root_seeds = ROOT_SEEDS[:2] if smoke else ROOT_SEEDS

    print("[Exp 2] Part A: Running deterministic Root-PUCT scaling benchmark...", flush=True)
    rblocks = []
    for prior in root_priors:
        for m in root_sizes:
            for seed in root_seeds:
                meths = list(ROOT_METHODS)
                rng.shuffle(meths)
                rblocks.append((prior, m, seed, 0, meths))
                rblocks.append((prior, m, seed, 1, meths[::-1]))
    rng.shuffle(rblocks)

    with (dest / "root_puct_runs.jsonl").open("w") as out:
        for idx, (prior, m, seed, rep, meths) in enumerate(rblocks, 1):
            prob, eps = puct_root_funnel(m, seed=seed, alpha=0.25)
            for pos, meth in enumerate(meths):
                row = run_single(
                    prob, eps, seed, "root_puct", prior, meth,
                    delta=0.05, c_explore=3.0, schedule="box",
                    cap=ROOT_CAP, wall_limit=ROOT_WALL_S, effective_m=3, q_cert=1,
                )
                row.update(m=m, seed=seed, repeat=rep, position=pos)
                out.write(json.dumps(row) + "\n")
            if idx % 30 == 0 or idx == len(rblocks):
                out.flush()
                print(f"  root_puct blocks: {idx}/{len(rblocks)}", flush=True)

    noisy_cases = ("funnel_64_wide", "coded_16") if smoke else NOISY_CASES
    noisy_priors = ("uniform", "misleading") if smoke else NOISY_PRIORS
    noisy_seeds = NOISY_SEEDS[:2] if smoke else NOISY_SEEDS

    print("[Exp 2] Part B: Running noisy Recursive-PUCT + TA-UCT benchmark...", flush=True)
    nblocks = []
    for case in noisy_cases:
        for seed in noisy_seeds:
            # Coupled blocks within each Recursive-PUCT prior
            for prior in noisy_priors:
                meths = list(NOISY_METHODS)
                rng.shuffle(meths)
                nblocks.append((case, "recursive_puct", prior, seed, 0, meths))
                nblocks.append((case, "recursive_puct", prior, seed, 1, meths[::-1]))
            # Separate coupled block for TA-UCT reference
            meths = list(NOISY_METHODS)
            rng.shuffle(meths)
            nblocks.append((case, "uct", "none", seed, 0, meths))
            nblocks.append((case, "uct", "none", seed, 1, meths[::-1]))
    rng.shuffle(nblocks)

    with (dest / "noisy_puct_runs.jsonl").open("w") as out:
        for idx, (case, pol, prior, seed, rep, meths) in enumerate(nblocks, 1):
            prob, eps = make_noisy_case(case, seed)
            c_exp = 2.5 if pol == "recursive_puct" else 2.0
            pmode = "uniform" if pol == "uct" else prior
            for pos, meth in enumerate(meths):
                row = run_single(
                    prob, eps, seed, pol, pmode, meth,
                    delta=0.05, c_explore=c_exp, schedule="noisy_puct",
                    cap=NOISY_CAP, wall_limit=NOISY_WALL_S, q_cert=4,
                )
                row["prior"] = prior
                row.update(case=case, seed=seed, repeat=rep, position=pos)
                out.write(json.dumps(row) + "\n")
            if idx % 48 == 0 or idx == len(nblocks):
                out.flush()
                print(f"  noisy_puct blocks: {idx}/{len(nblocks)}", flush=True)

    print("[Exp 2] Part C: Measuring peak memory (tracemalloc isolated from timing)...", flush=True)
    with (dest / "memory_runs.jsonl").open("w") as out:
        for case in noisy_cases:
            for seed in noisy_seeds[:2]:
                prob, eps = make_noisy_case(case, seed)
                for pol, prior in (*[("recursive_puct", p) for p in noisy_priors], ("uct", "none")):
                    c_exp = 2.5 if pol == "recursive_puct" else 2.0
                    pmode = "uniform" if pol == "uct" else prior
                    for meth in NOISY_METHODS:
                        row = run_single(
                            prob, eps, seed, pol, pmode, meth,
                            delta=0.05, c_explore=c_exp, schedule="noisy_puct",
                            cap=NOISY_CAP, wall_limit=NOISY_WALL_S, q_cert=4,
                            measure_memory=True,
                        )
                        row["prior"] = prior
                        row.update(case=case, seed=seed)
                        out.write(json.dumps(row) + "\n")
        out.flush()

    manifest = {
        "experiment": "exp2_puct",
        "smoke": smoke,
        "root_sizes": root_sizes,
        "root_priors": root_priors,
        "noisy_cases": noisy_cases,
        "noisy_priors": noisy_priors,
        "methods": NOISY_METHODS,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "sha256_root_puct": digest(dest / "root_puct_runs.jsonl"),
        "sha256_noisy_puct": digest(dest / "noisy_puct_runs.jsonl"),
        "sha256_memory": digest(dest / "memory_runs.jsonl"),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    if not smoke:
        agg = summarize(dest)
        print("[Exp 2] Summary:", json.dumps(agg, indent=2), flush=True)


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
