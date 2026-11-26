"""Experiment 1 & Pre-Step Equivalence Audit: Exact Shared-Support Regret vs. Conventional Certification.

Evaluates:
1. Pre-step step-by-step equivalence audit across NestedIntervals, Graph-Eager,
   Protected-Selective, Decision-Selective, Nested Dyadic Covers, Charged Dual Covers,
   and Factorized Regret against unoptimized brute-force DP references.
2. Common-trace statistical comparison (Panel A):
   Controlled support-overlap DAGs O_{M, K, rho, g} across M in {64, 256, 1024},
   overlap rho in {0.00, 0.25, 0.50, 0.75, 0.88, 1.00} (no-overlap rho=0 and
   identical-support rho=1.0 reported separately from partial overlap 0 < rho < 1),
   gaps g in {0.42, 0.32}, and both deterministic and Bernoulli rewards on a
   counterfactually continued TA-UCT trace until both certificates halt (up to CAP).
3. Counterbalanced end-to-end wall-clock comparison (Panel B):
   Cold end-to-end certification runs (including index compilation, rollouts,
   heap maintenance, queries, and disposal) comparing Conventional (Protected Graph
   and Dyadic Covers) vs. Exact Shared-Support Regret (Charged Dual Covers and
   Factorized Regret) halting at each certificate's own stopping time.
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

from joint_root_cert._core.certified_uct import TranspositionUCT, UCTWork
from joint_root_cert.search import CertifiedSearchSession, build_monitor
from joint_root_cert.benchmarks import (
    contiguous_window_dag,
    overlap_dag,
    puct_noisy_funnel,
    samegame_depth_case,
    samegame_standard_endgame,
    structural_diagnostics,
)
from joint_root_cert.certificates import (
    ChargedDualCovers,
    FactorizedRegretMonitor,
    MarginalGraphMonitor,
    NestedDyadicCovers,
    NestedIntervals,
    brute_force_exact_regret,
    brute_force_marginal,
)
from experiment.simulated.passive_uct.uct_frontier_families import coded


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v2_extensions/exp1_exact_regret"

SIZES = (64, 256, 1024)
OVERLAPS = (0.00, 0.25, 0.50, 0.75, 0.88, 1.00)
GAPS = (0.42, 0.32)
REWARD_MODES = ("deterministic", "bernoulli")
SEEDS = tuple(range(610001, 610007))  # 6 independent seeds per configuration
TRACE_CAP = 50000
BUDGETS = (500, 2000, 8000, 20000, 50000)

WALL_METHODS = ("quotient-protected", "dyadic-covers", "dual-covers", "factorized-regret")
WALL_SIZES = (64, 256, 1024)
WALL_GAPS = (0.42, 0.32)
WALL_SEEDS = tuple(range(610001, 610005))  # 4 seeds x 2 counterbalanced repeats (8 cold runs/cell)
WALL_CAP = 50000
WALL_LIMIT_S = 1.0
DELTA = 0.05
C_UCT = 3.0
Q_CERT = 4


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_equivalence_audit(dest: Path) -> dict:
    """Audit step-by-step oracle equivalence across synthetic and natural DAGs."""
    audit_cases = [
        ("overlap_64_rho0", *overlap_dag(64, 0.00, 0.42, seed=605001, noisy=True)),
        ("overlap_64_rho50", *overlap_dag(64, 0.50, 0.42, seed=605002, noisy=True)),
        ("overlap_64_rho88_det", *overlap_dag(64, 0.88, 0.42, seed=605003, noisy=False)),
        ("funnel_64", *puct_noisy_funnel(64, seed=605004, gap=0.14, noisy=True)),
        ("parity_8", *coded(8, seed=605005)),
        ("window_64", *contiguous_window_dag(64, 8, seed=605006, noisy=True)),
        ("samegame_5x5_d3", *samegame_depth_case(5, 3, seed=605007, eps=0.08)),
        ("samegame_std01_d3", *samegame_standard_endgame(1, depth=3, eps=0.05)),
    ]
    records = []
    total_rollouts = 0
    total_dp_checks = 0
    for label, prob, eps in audit_cases:
        seed = 77001
        num_methods = ("graph-eager", "protected-selective", "quotient-protected", "dyadic-covers")
        exact_methods = ("dual-covers", "dual-covers-id", "factorized-regret", "direct-graph-regret")
        uct = TranspositionUCT(prob.graph, exploration=3.0, lazy=True)
        oracle = prob.oracle(seed)
        monitors_num = [build_monitor(prob.graph, m, delta=DELTA, schedule="box") for m in num_methods]
        mon_dec = build_monitor(prob.graph, "decision-selective", delta=DELTA, schedule="box")
        monitors_ex = [build_monitor(prob.graph, m, delta=DELTA, schedule="box") for m in exact_methods]

        steps = 0
        checks = 0
        tau_marg = None
        tau_exact = None
        while steps < 5000 and (tau_marg is None or tau_exact is None):
            path, reward = uct.step(oracle)
            leaf = path[-1]
            steps += 1
            c_num = [m.step(leaf, reward) for m in monitors_num]
            c_dec = mon_dec.step(leaf, reward)
            c_ex = [m.step(leaf, reward) for m in monitors_ex]
            assert len(set(c_num)) == 1 and c_dec == c_num[0] and len(set(c_ex)) == 1

            q_nums = [m.query() for m in monitors_num]
            q_dec = mon_dec.query()
            q_exs = [m.query() for m in monitors_ex]

            for q in q_nums[1:]:
                assert q[0] == q_nums[0][0] and abs(q[1] - q_nums[0][1]) <= 1e-12
            assert q_dec[0] == q_nums[0][0]
            assert (q_dec[1] <= eps) == (q_nums[0][1] <= eps)
            for q in q_exs[1:]:
                assert q[0] == q_exs[0][0] and abs(q[1] - q_exs[0][1]) <= 1e-12
            assert q_exs[0][1] <= q_nums[0][1] + 1e-12

            if steps <= 32 or (steps & (steps - 1)) == 0 or q_nums[0][1] <= eps or q_exs[0][1] <= eps:
                ev = monitors_num[0].evidence
                assert not ev.conflict
                b_lead, b_gap, b_ints = brute_force_marginal(prob.graph, ev.lower, ev.upper)
                assert q_nums[0][0] == b_lead and abs(q_nums[0][1] - b_gap) <= 1e-12
                for m in monitors_num[:3]:
                    assert m.bounds.action_intervals() == b_ints
                e_best, e_reg, _ = brute_force_exact_regret(prob.graph, ev.lower, ev.upper)
                assert q_exs[0][0] == e_best and abs(q_exs[0][1] - e_reg) <= 1e-12
                checks += 1

            if tau_exact is None and q_exs[0][1] <= eps:
                tau_exact = steps
            if tau_marg is None and q_nums[0][1] <= eps:
                tau_marg = steps

        total_rollouts += steps
        total_dp_checks += checks
        records.append({
            "case": label,
            "steps_audited": steps,
            "dp_reference_checks": checks,
            "tau_exact": tau_exact,
            "tau_marginal": tau_marg,
            "conflicts": 0,
            "discrepancies": 0,
        })

    summary = {
        "cases": len(records),
        "total_rollouts_audited": total_rollouts,
        "total_dp_checks": total_dp_checks,
        "zero_discrepancies": True,
        "records": records,
    }
    (dest / "equivalence_audit.json").write_text(json.dumps(summary, indent=2))
    return summary


def run_common_trace_one(m: int, rho: float, gap: float, reward_mode: str, seed: int) -> dict:
    """Counterfactually continue a single TA-UCT trace until both certificates stop."""
    noisy = reward_mode == "bernoulli"
    problem, eps = overlap_dag(m, rho, gap, seed, noisy=noisy)
    graph = problem.graph
    values = graph.optimal_values(problem.means)
    opt_val = values[graph.root]
    action_true_regrets = [max(0.0, opt_val - values[c]) for c in graph.children[graph.root]]

    uct = TranspositionUCT(graph, exploration=C_UCT, lazy=True)
    oracle = problem.oracle(seed)
    mon_conv = MarginalGraphMonitor(graph, mode="protected", delta=DELTA, schedule="box", simplify=True)
    mon_exact = ChargedDualCovers(graph, delta=DELTA, schedule="box", layout="best")

    # Initial t = 0 check (captures identical supports S(a) == Z where R_0(a) == 0!)
    q_conv = mon_conv.query()
    q_exact = mon_exact.query()
    tau_conv: int | None = 0 if q_conv[1] <= eps else None
    act_conv: int | None = q_conv[0] if tau_conv is not None else None
    tau_exact: int | None = 0 if q_exact[1] <= eps else None
    act_exact: int | None = q_exact[0] if tau_exact is not None else None
    tau_marg_min: int | None = tau_conv

    dirty_conv = False
    dirty_exact = False
    while (tau_conv is None or tau_exact is None) and uct.calls < TRACE_CAP:
        path, reward = uct.step(oracle)
        leaf = path[-1]
        if tau_conv is None:
            if mon_conv.step(leaf, reward):
                dirty_conv = True
            if mon_conv.evidence.conflict:
                break
        if tau_exact is None:
            if mon_exact.step(leaf, reward):
                dirty_exact = True
            if mon_exact.evidence.conflict:
                break
        if uct.calls % Q_CERT == 0:
            if tau_conv is None and dirty_conv:
                dirty_conv = False
                q_conv = mon_conv.query()
                if q_conv[1] <= eps:
                    tau_conv = uct.calls
                    act_conv = q_conv[0]
                if tau_marg_min is None:
                    ints = mon_conv.bounds.action_intervals()
                    # Exact O(K) check of min_a max_{b != a} (U_b - L_a) via top-2 U_b values
                    if len(ints) <= 1:
                        mmin = 0.0
                    else:
                        u1, u2, u1_idx = -math.inf, -math.inf, -1
                        for b, (_, ub) in enumerate(ints):
                            if ub > u1:
                                u2, u1, u1_idx = u1, ub, b
                            elif ub > u2:
                                u2 = ub
                        mmin = min(
                            ((u2 if a == u1_idx else u1) - la)
                            for a, (la, _) in enumerate(ints)
                        )
                    if max(0.0, mmin) <= eps:
                        tau_marg_min = uct.calls
            if tau_exact is None and dirty_exact:
                dirty_exact = False
                q_exact = mon_exact.query()
                if q_exact[1] <= eps:
                    tau_exact = uct.calls
                    act_exact = q_exact[0]

    # Soundness check on every certified decision!
    if act_conv is not None:
        assert action_true_regrets[act_conv] <= eps + 1e-12
    if act_exact is not None:
        assert action_true_regrets[act_exact] <= eps + 1e-12
    if tau_conv is not None and tau_exact is not None:
        assert tau_exact <= tau_conv

    eff_conv = tau_conv if tau_conv is not None else TRACE_CAP
    eff_exact = tau_exact if tau_exact is not None else TRACE_CAP
    eff_mmin = tau_marg_min if tau_marg_min is not None else TRACE_CAP

    return {
        "M": m,
        "rho": rho,
        "gap": gap,
        "epsilon": eps,
        "reward_mode": reward_mode,
        "seed": seed,
        "tau_conv": tau_conv,
        "tau_exact": tau_exact,
        "tau_marg_min": tau_marg_min,
        "capped_conv": eff_conv,
        "capped_exact": eff_exact,
        "capped_marg_min": eff_mmin,
        "ratio_capped": (eff_exact / eff_conv) if eff_conv > 0 else 0.0,
        "ratio_uncensored": (tau_exact / tau_conv) if (tau_conv and tau_exact is not None) else None,
        "act_conv": act_conv,
        "act_exact": act_exact,
        "regret_conv": action_true_regrets[act_conv] if act_conv is not None else None,
        "regret_exact": action_true_regrets[act_exact] if act_exact is not None else None,
        "conflict": mon_conv.evidence.conflict,
        "dual_blocks": mon_exact.total_blocks,
    }


def run_wall_one(problem, eps: float, seed: int, method: str) -> dict:
    """Cold timed run of a single (policy + monitor) halting at its own stopping time."""
    gc.collect()
    t0 = time.perf_counter()
    sess = CertifiedSearchSession(
        problem, seed, "uct", method, eps,
        delta=DELTA, c_explore=C_UCT, q_cert=Q_CERT, schedule="box",
    )
    t_init = time.perf_counter() - t0
    init_work = sess.work
    elapsed = t_init
    while (not sess.certified and not sess.monitor.evidence.conflict
           and sess.calls < WALL_CAP and elapsed < WALL_LIMIT_S):
        sess.step()
        elapsed = time.perf_counter() - t0

    calls = sess.calls
    cert = sess.certified
    act = sess.action
    work = sess.work
    mon_work = sess.monitor.work.total
    conflict = sess.monitor.evidence.conflict
    del sess
    end_s = time.perf_counter() - t0

    values = problem.graph.optimal_values(problem.means)
    opt_val = values[problem.graph.root]
    true_reg = max(0.0, opt_val - values[problem.graph.children[problem.graph.root][act]])
    if cert:
        assert true_reg <= eps + 1e-12

    returned = bool(cert and end_s <= WALL_LIMIT_S)
    return {
        "method": method,
        "steps": calls,
        "certified": cert,
        "returned": returned,
        "init_ms": 1000.0 * t_init,
        "end_ms": 1000.0 * end_s,
        "restricted_ms": 1000.0 * (end_s if returned else WALL_LIMIT_S),
        "init_work": init_work,
        "work": work,
        "monitor_work": mon_work,
        "true_regret": true_reg,
        "conflict": conflict,
    }


def bootstrap_median_ci(values: list[float], seed: int = 9001, reps: int = 2000) -> tuple[float, float]:
    if not values:
        return (math.nan, math.nan)
    if len(values) == 1:
        return (values[0], values[0])
    rng = random.Random(seed)
    n = len(values)
    meds = sorted(statistics.median(values[rng.randrange(n)] for _ in range(n)) for _ in range(reps))
    return meds[int(0.025 * reps)], meds[int(0.975 * reps)]


def summarize(dest: Path) -> dict:
    traces = [json.loads(line) for line in (dest / "common_traces.jsonl").read_text().splitlines()]
    walls = [json.loads(line) for line in (dest / "wall_runs.jsonl").read_text().splitlines()]

    # 1. Per-(M, rho, gap, reward_mode) statistical summary CSV
    stat_rows = []
    for m in SIZES:
        for gap in GAPS:
            for reward_mode in REWARD_MODES:
                for rho in OVERLAPS:
                    grp = [r for r in traces if (r["M"], r["rho"], r["gap"], r["reward_mode"]) == (m, rho, gap, reward_mode)]
                    ratios = [r["ratio_capped"] for r in grp]
                    med_ratio = statistics.median(ratios)
                    q25 = sorted(ratios)[len(ratios) // 4]
                    q75 = sorted(ratios)[(3 * len(ratios)) // 4]
                    ci_lo, ci_hi = bootstrap_median_ci(ratios)
                    row = {
                        "M": m,
                        "rho": rho,
                        "gap": gap,
                        "reward_mode": reward_mode,
                        "n_seeds": len(grp),
                        "conv_certified": sum(r["tau_conv"] is not None for r in grp),
                        "exact_certified": sum(r["tau_exact"] is not None for r in grp),
                        "med_tau_conv": statistics.median(r["capped_conv"] for r in grp),
                        "med_tau_exact": statistics.median(r["capped_exact"] for r in grp),
                        "med_tau_marg_min": statistics.median(r["capped_marg_min"] for r in grp),
                        "med_ratio": med_ratio,
                        "q25_ratio": q25,
                        "q75_ratio": q75,
                        "ci95_lo": ci_lo,
                        "ci95_hi": ci_hi,
                    }
                    for b in BUDGETS:
                        row[f"conv_cert_at_{b}"] = sum(r["tau_conv"] is not None and r["tau_conv"] <= b for r in grp) / len(grp)
                        row[f"exact_cert_at_{b}"] = sum(r["tau_exact"] is not None and r["tau_exact"] <= b for r in grp) / len(grp)
                    stat_rows.append(row)

    with (dest / "statistical_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(stat_rows[0].keys()))
        writer.writeheader()
        writer.writerows(stat_rows)

    # 2. Per-(M, rho, gap, reward_mode, method) wall-clock summary CSV (averaging 2 counterbalanced repeats per seed first!)
    wall_rows = []
    for m in WALL_SIZES:
        for gap in WALL_GAPS:
            for reward_mode in REWARD_MODES:
                for rho in OVERLAPS:
                    # Pair by seed across methods
                    by_method_seed: dict[str, dict[int, float]] = {meth: {} for meth in WALL_METHODS}
                    by_method_work: dict[str, dict[int, float]] = {meth: {} for meth in WALL_METHODS}
                    by_method_ret: dict[str, int] = {meth: 0 for meth in WALL_METHODS}
                    by_method_tot: dict[str, int] = {meth: 0 for meth in WALL_METHODS}
                    for r in walls:
                        if (r["M"], r["rho"], r["gap"], r["reward_mode"]) == (m, rho, gap, reward_mode):
                            meth = r["method"]
                            by_method_tot[meth] += 1
                            by_method_ret[meth] += int(r["returned"])
                    for meth in WALL_METHODS:
                        for seed in WALL_SEEDS:
                            reps = [
                                r for r in walls
                                if (r["M"], r["rho"], r["gap"], r["reward_mode"], r["method"], r["seed"])
                                == (m, rho, gap, reward_mode, meth, seed)
                            ]
                            if reps:
                                by_method_seed[meth][seed] = statistics.mean(x["restricted_ms"] for x in reps)
                                by_method_work[meth][seed] = statistics.mean(x["work"] for x in reps)
                    if not by_method_seed[WALL_METHODS[0]]:
                        continue
                    for meth in WALL_METHODS:
                        times = list(by_method_seed[meth].values())
                        works = list(by_method_work[meth].values())
                        # Paired ratio against quotient-protected conventional baseline
                        paired_time_ratios = [
                            by_method_seed[meth][s] / max(1e-6, by_method_seed["quotient-protected"][s])
                            for s in WALL_SEEDS if s in by_method_seed[meth]
                        ]
                        ci_lo, ci_hi = bootstrap_median_ci(times)
                        wall_rows.append({
                            "M": m,
                            "rho": rho,
                            "gap": gap,
                            "reward_mode": reward_mode,
                            "method": meth,
                            "n_seeds": len(times),
                            "returned": by_method_ret[meth],
                            "total_runs": by_method_tot[meth],
                            "med_restricted_ms": statistics.median(times),
                            "mean_restricted_ms": statistics.mean(times),
                            "ci95_ms_lo": ci_lo,
                            "ci95_ms_hi": ci_hi,
                            "med_work": statistics.median(works),
                            "med_time_ratio_vs_conv_graph": statistics.median(paired_time_ratios),
                        })

    with (dest / "wall_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(wall_rows[0].keys()))
        writer.writeheader()
        writer.writerows(wall_rows)

    # Regime-separated aggregate summary (explicitly separating rho=0, 0<rho<1, and rho=1.0!)
    no_ov = [r["ratio_capped"] for r in traces if r["rho"] == 0.0]
    partial_ov = [r["ratio_capped"] for r in traces if 0.0 < r["rho"] < 1.0]
    ident_ov = [r["ratio_capped"] for r in traces if r["rho"] == 1.0]
    agg = {
        "total_trace_runs": len(traces),
        "total_wall_runs": len(walls),
        "no_overlap_rho0": {
            "count": len(no_ov),
            "median_tau_ratio": statistics.median(no_ov),
            "iqr": [sorted(no_ov)[len(no_ov) // 4], sorted(no_ov)[(3 * len(no_ov)) // 4]],
        },
        "partial_overlap_0_lt_rho_lt_1": {
            "count": len(partial_ov),
            "median_tau_ratio": statistics.median(partial_ov),
            "iqr": [sorted(partial_ov)[len(partial_ov) // 4], sorted(partial_ov)[(3 * len(partial_ov)) // 4]],
            "by_rho": {
                f"{rho:.2f}": statistics.median(r["ratio_capped"] for r in traces if r["rho"] == rho)
                for rho in (0.25, 0.50, 0.75, 0.88)
                if any(r["rho"] == rho for r in traces)
            },
        },
        "identical_support_rho1": {
            "count": len(ident_ov),
            "all_zero_samples_for_exact": all(r["tau_exact"] == 0 for r in traces if r["rho"] == 1.0),
            "median_tau_conv": statistics.median(r["capped_conv"] for r in traces if r["rho"] == 1.0),
        },
    }
    (dest / "summary.json").write_text(json.dumps(agg, indent=2))
    return agg


def run(dest: Path = DEST, smoke: bool = False, reuse_traces: bool = False) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    sizes = (64,) if smoke else SIZES
    overlaps = (0.00, 0.50, 1.00) if smoke else OVERLAPS
    gaps = (0.42,) if smoke else GAPS
    seeds = SEEDS[:2] if smoke else SEEDS
    wall_seeds = WALL_SEEDS[:2] if smoke else WALL_SEEDS

    if reuse_traces and (dest / "equivalence_audit.json").is_file() and (dest / "common_traces.jsonl").is_file():
        print("[Exp 1] Step 0 & Step 1: Reusing completed equivalence_audit.json and common_traces.jsonl.", flush=True)
    else:
        print("[Exp 1] Step 0: Running pre-step oracle equivalence audit...", flush=True)
        audit_summary = run_equivalence_audit(dest)
        print(f"  PASS: audited {audit_summary['total_rollouts_audited']:,} rollouts and "
              f"{audit_summary['total_dp_checks']:,} brute-force DP checks with 0 discrepancies.", flush=True)

        print("[Exp 1] Step 1: Running common-trace counterfactual statistical comparison...", flush=True)
        trace_tasks = [
            (m, rho, gap, rmode, seed)
            for m in sizes for gap in gaps for rmode in REWARD_MODES for rho in overlaps for seed in seeds
        ]
        with (dest / "common_traces.jsonl").open("w") as out:
            for idx, (m, rho, gap, rmode, seed) in enumerate(trace_tasks, 1):
                row = run_common_trace_one(m, rho, gap, rmode, seed)
                out.write(json.dumps(row) + "\n")
                if idx % 48 == 0 or idx == len(trace_tasks):
                    out.flush()
                    print(f"  traces: {idx}/{len(trace_tasks)}", flush=True)

    print("[Exp 1] Step 2: Running counterbalanced cold end-to-end wall-clock runs...", flush=True)
    rng = random.Random(610999)
    blocks = []
    for m in (sizes if smoke else WALL_SIZES):
        m_gaps = gaps if smoke else (WALL_GAPS if m == 256 else (WALL_GAPS[0],))
        for gap in m_gaps:
            for rmode in REWARD_MODES:
                for rho in overlaps:
                    for seed in wall_seeds:
                        meths = list(WALL_METHODS)
                        rng.shuffle(meths)
                        blocks.append((m, rho, gap, rmode, seed, 0, meths))
                        blocks.append((m, rho, gap, rmode, seed, 1, meths[::-1]))
    rng.shuffle(blocks)

    with (dest / "wall_runs.jsonl").open("w") as out:
        for idx, (m, rho, gap, rmode, seed, rep, meths) in enumerate(blocks, 1):
            noisy = rmode == "bernoulli"
            prob, eps = overlap_dag(m, rho, gap, seed, noisy=noisy)
            for pos, meth in enumerate(meths):
                row = run_wall_one(prob, eps, seed, meth)
                row.update(M=m, rho=rho, gap=gap, reward_mode=rmode, seed=seed, repeat=rep, position=pos)
                out.write(json.dumps(row) + "\n")
            if idx % 64 == 0 or idx == len(blocks):
                out.flush()
                print(f"  wall blocks: {idx}/{len(blocks)} ({idx * len(WALL_METHODS)} runs)", flush=True)

    manifest = {
        "experiment": "exp1_exact_regret",
        "smoke": smoke,
        "sizes": sizes,
        "overlaps": overlaps,
        "gaps": gaps,
        "reward_modes": REWARD_MODES,
        "trace_seeds": seeds,
        "wall_seeds": wall_seeds,
        "trace_cap": TRACE_CAP,
        "wall_limit_s": WALL_LIMIT_S,
        "delta": DELTA,
        "c_uct": C_UCT,
        "q_cert": Q_CERT,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "sha256_common_traces": digest(dest / "common_traces.jsonl"),
        "sha256_wall_runs": digest(dest / "wall_runs.jsonl"),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    if not smoke:
        agg = summarize(dest)
        print("[Exp 1] Summary:", json.dumps(agg, indent=2), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEST)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--summarize-only", action="store_true")
    parser.add_argument("--reuse-traces", action="store_true")
    args = parser.parse_args()
    if args.summarize_only:
        print(json.dumps(summarize(args.out), indent=2))
    else:
        run(args.out, smoke=args.smoke, reuse_traces=args.reuse_traces)
