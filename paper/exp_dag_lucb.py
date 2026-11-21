"""Experiment 6 (Strengthening): Active Witness-Guided Allocation (DAG-LUCB) & Theorem 2.4 Audit.

Evaluates:
1. Adaptive Transcript-Coupling Audit (Theorem 2.4):
   Verifies rollout-by-rollout identical paths, rewards, and stopping times across all three
   exact-regret representations (`WitnessDualCovers`, `WitnessDirectGraphRegret`, and
   `WitnessFactorizedRegret`) when driving the adaptive `ActiveDAGLUCBSession` controller
   under both Hoeffding (`box`) and Empirical Bernstein (`emp_bernstein`) schedules.
2. Statistical & Cold End-to-End Computational Comparison:
   Compares passive `TA-UCT + Exact Regret` (`passive_uct_exact`), active `Marginal-DAG-LUCB`
   (`marginal_dag_lucb`, which wastes challenger draws on shared high-payoff terminals), and
   active `Exact-Regret-DAG-LUCB` (`exact_lucb_dual` and `exact_lucb_direct`, which restrict
   challenger queries to Z \\ S(a*_t)) across:
   - Support-overlap DAGs (M in {64, 256}, rho in {0.00, 0.25, 0.50, 0.75, 0.88, 1.00},
     gap=0.32, deterministic and Bernoulli rewards),
   - Parity-grid DAGs (r in {8, 16}, demonstrating Theorem 2.4 representation duality inside
     an active pure-exploration loop),
   - Natural 15x15 SameGame endgames (boards 1..10 at depth 3 with Empirical Bernstein boxes).
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

from dag_mcts.puct import CertifiedSearchSession
from dag_mcts.v2_benchmarks import (
    contiguous_window_dag,
    overlap_dag,
    samegame_depth_case,
    samegame_standard_endgame,
)
from dag_mcts.v3_extensions import ActiveDAGLUCBSession
from paper.uct_frontier_families import coded


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/uct_v3_strengthening/exp6_dag_lucb"

CONTROLLERS = (
    "passive_uct_exact",
    "marginal_dag_lucb",
    "exact_lucb_dual",
    "exact_lucb_direct",
)

OVERLAPS = (0.00, 0.25, 0.50, 0.75, 0.88, 1.00)
SIZES = (64, 256)
REWARD_MODES = ("deterministic", "bernoulli")
SEEDS = tuple(range(660001, 660005))  # 4 seeds x 2 counterbalanced repeats

STEP_CAP = 36000
WALL_LIMIT_S = 1.0
DELTA = 0.05
Q_CERT = 4


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_adaptive_coupling_audit(dest: Path, smoke: bool = False) -> dict:
    """Empirically verify Theorem 2.4 adaptive rollout-transcript coupling."""
    cases = [
        ("overlap_64_rho00_box", *overlap_dag(64, 0.00, 0.32, 661001, noisy=True), "box"),
        ("overlap_64_rho50_box", *overlap_dag(64, 0.50, 0.32, 661002, noisy=True), "box"),
        ("overlap_64_rho88_eb", *overlap_dag(64, 0.88, 0.32, 661003, noisy=True), "emp_bernstein"),
        ("window_64_box", *contiguous_window_dag(64, 8, 661004, noisy=True), "box"),
        ("parity_8_box", *coded(8, seed=661005), "box"),
        ("samegame_5x5_d3_eb", *samegame_depth_case(5, 3, 630001, eps=0.10), "emp_bernstein"),
        ("samegame_std01_d3_eb", *samegame_standard_endgame(1, depth=3, eps=0.08), "emp_bernstein"),
    ]
    if smoke:
        cases = cases[:3]

    records = []
    total_steps = 0
    for label, prob, eps, sched in cases:
        seed = 88001
        methods = ("dual-covers", "direct-graph-regret", "factorized-regret")
        sessions = [
            ActiveDAGLUCBSession(prob, seed, m, eps, delta=DELTA, schedule=sched)
            for m in methods
        ]
        assert len({s.certified for s in sessions}) == 1
        assert len({s.action for s in sessions}) == 1
        steps = 0
        cap = 1000 if smoke else 4000
        while not sessions[0].certified and steps < cap:
            outs = [s.step() for s in sessions]
            steps += 1
            for o in outs[1:]:
                assert o[0] == outs[0][0], f"Path mismatch in {label} at step {steps}"
                assert o[1] == outs[0][1], f"Reward mismatch in {label} at step {steps}"
            assert len({s.certified for s in sessions}) == 1
            assert len({s.action for s in sessions}) == 1
            qs = [s.query for s in sessions]
            for q in qs[1:]:
                assert q[0] == qs[0][0]
                assert abs(q[1] - qs[0][1]) <= 1e-12
                assert q[2] == qs[0][2] and q[3] == qs[0][3]

        total_steps += steps
        records.append({
            "case": label,
            "schedule": sched,
            "steps_audited": steps,
            "certified": sessions[0].certified,
            "action": sessions[0].action,
            "work_dual_covers": sessions[0].work,
            "work_direct_graph": sessions[1].work,
            "work_factorized": sessions[2].work,
            "discrepancies": 0,
        })

    audit = {
        "cases": len(records),
        "total_adaptive_steps_audited": total_steps,
        "zero_discrepancies": True,
        "records": records,
    }
    (dest / "adaptive_coupling_audit.json").write_text(json.dumps(audit, indent=2))
    return audit


def run_one_controller(prob, eps: float, seed: int, controller: str,
                       schedule: str, c_uct: float, wall_limit: float, cap: int) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    opt = values[prob.graph.root]
    regrets = [max(0.0, opt - values[c]) for c in prob.graph.children[prob.graph.root]]

    t0 = time.perf_counter()
    if controller == "passive_uct_exact":
        sess = CertifiedSearchSession(
            prob, seed, "uct", "dual-covers", eps,
            delta=DELTA, c_explore=c_uct, q_cert=Q_CERT, schedule=schedule,
        )
    elif controller == "marginal_dag_lucb":
        sess = ActiveDAGLUCBSession(prob, seed, "marginal-graph", eps, delta=DELTA, schedule=schedule)
    elif controller == "exact_lucb_dual":
        sess = ActiveDAGLUCBSession(prob, seed, "dual-covers", eps, delta=DELTA, schedule=schedule)
    elif controller == "exact_lucb_direct":
        sess = ActiveDAGLUCBSession(prob, seed, "direct-graph-regret", eps, delta=DELTA, schedule=schedule)
    else:
        raise ValueError(f"Unknown controller: {controller}")

    t_init = time.perf_counter() - t0
    elapsed = t_init
    while (not sess.certified and not sess.monitor.evidence.conflict
           and sess.calls < cap and elapsed < wall_limit):
        sess.step()
        elapsed = time.perf_counter() - t0

    cert = sess.certified
    act = sess.action
    calls = sess.calls
    work = sess.work
    conflict = sess.monitor.evidence.conflict
    del sess
    total_s = time.perf_counter() - t0

    true_reg = regrets[act]
    if cert:
        assert true_reg <= eps + 1e-12, f"False certificate in {controller}: {true_reg} > {eps}"
    return {
        "controller": controller,
        "schedule": schedule,
        "certified": cert,
        "conflict": conflict,
        "false_certificate": bool(cert and true_reg > eps + 1e-12),
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "init_s": t_init,
        "total_s": total_s,
        "total_work": work,
        "final_simple_regret": true_reg,
    }


def build_tasks(smoke: bool = False) -> list[dict]:
    tasks = []
    if smoke:
        for rho in (0.00, 0.75, 1.00):
            prob, eps = overlap_dag(64, rho, 0.32, 660001, noisy=False)
            tasks.append({
                "suite": "overlap", "family": f"overlap_64_det_rho{int(round(rho*100)):02d}",
                "m": 64, "rho": rho, "reward_mode": "deterministic", "seed": 660001,
                "prob": prob, "eps": eps, "schedule": "box", "c_uct": 3.0,
            })
        p_par, e_par = coded(8, seed=660001)
        tasks.append({
            "suite": "parity", "family": "parity_8", "m": 64, "rho": 0.50,
            "reward_mode": "bernoulli", "seed": 660001, "prob": p_par, "eps": e_par,
            "schedule": "box", "c_uct": 3.0,
        })
        return tasks

    for m in SIZES:
        for mode in REWARD_MODES:
            noisy = mode == "bernoulli"
            for rho in OVERLAPS:
                for s in SEEDS:
                    prob, eps = overlap_dag(m, rho, 0.32, s, noisy=noisy)
                    tasks.append({
                        "suite": "overlap",
                        "family": f"overlap_{m}_{mode[:3]}_rho{int(round(rho*100)):02d}",
                        "m": m, "rho": rho, "reward_mode": mode, "seed": s,
                        "prob": prob, "eps": eps, "schedule": "box", "c_uct": 3.0,
                    })

    for r in (8, 16):
        for s in SEEDS:
            prob, eps = coded(r, seed=s)
            tasks.append({
                "suite": "parity",
                "family": f"parity_{r}",
                "m": len(prob.graph.leaves), "rho": 0.50, "reward_mode": "bernoulli", "seed": s,
                "prob": prob, "eps": eps, "schedule": "box", "c_uct": 3.0,
            })

    for idx in range(1, 11):
        game, eps = samegame_standard_endgame(idx, depth=3, eps=0.08)
        tasks.append({
            "suite": "samegame",
            "family": "samegame_std15x15_d3_eb",
            "m": len(game.graph.leaves), "rho": -1.0, "reward_mode": "samegame", "seed": 631000 + idx,
            "prob": game, "eps": eps, "schedule": "emp_bernstein", "c_uct": 0.7,
        })
    return tasks


def summarize(dest: Path) -> None:
    runs = [json.loads(line) for line in (dest / "runs.jsonl").read_text().splitlines() if line.strip()]
    audit = json.loads((dest / "adaptive_coupling_audit.json").read_text())

    rows = []
    families = sorted({r["family"] for r in runs})
    for fam in families:
        sub_f = [r for r in runs if r["family"] == fam]
        suite = sub_f[0]["suite"]
        m = sub_f[0]["m"]
        rho = sub_f[0]["rho"]
        mode = sub_f[0]["reward_mode"]
        for ctrl in CONTROLLERS:
            sub = [r for r in sub_f if r["controller"] == ctrl]
            if not sub:
                continue
            rows.append({
                "suite": suite,
                "family": fam,
                "m": m,
                "rho": rho,
                "reward_mode": mode,
                "controller": ctrl,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_steps": round(statistics.median(r["steps"] for r in sub), 1),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "median_work": round(statistics.median(r["total_work"] for r in sub), 1),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_by_family.csv").open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    # Overlap curve summary (aggregated across M in {64, 256} per reward_mode and rho)
    ov_rows = []
    ov_runs = [r for r in runs if r["suite"] == "overlap"]
    for mode in sorted({r["reward_mode"] for r in ov_runs}):
        for rho in sorted({r["rho"] for r in ov_runs if r["reward_mode"] == mode}):
            cell = {"reward_mode": mode, "rho": rho}
            for ctrl in CONTROLLERS:
                sub = [r for r in ov_runs if r["reward_mode"] == mode and r["rho"] == rho and r["controller"] == ctrl]
                cell[f"{ctrl}_cert"] = round(sum(1 for r in sub if r["certified"]) / len(sub), 4)
                cell[f"{ctrl}_med_steps"] = round(statistics.median(r["capped_steps"] for r in sub), 1)
                cell[f"{ctrl}_med_ms"] = round(1e3 * statistics.median(r["total_s"] for r in sub), 3)
            ov_rows.append(cell)

    if ov_rows:
        with (dest / "summary_overlap_curves.csv").open("w", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=list(ov_rows[0].keys()))
            writer.writeheader()
            writer.writerows(ov_rows)

    summary = {
        "total_runs": len(runs),
        "total_false_certificates": sum(r["false_certificates"] for r in rows),
        "adaptive_coupling_audit": {
            "cases": audit["cases"],
            "total_adaptive_steps_audited": audit["total_adaptive_steps_audited"],
            "zero_discrepancies": audit["zero_discrepancies"],
        },
        "overlap_curves": ov_rows,
        "by_family": rows,
    }
    (dest / "summary.json").write_text(json.dumps(summary, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEST)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()

    dest: Path = args.out
    dest.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(dest)
        return

    t_start = time.perf_counter()
    run_adaptive_coupling_audit(dest, smoke=args.smoke)

    tasks = build_tasks(smoke=args.smoke)
    repeats = 1 if args.smoke else 2
    wall_limit = 0.20 if args.smoke else WALL_LIMIT_S
    cap = 5000 if args.smoke else STEP_CAP

    # Warm-up
    wp, we = overlap_dag(64, 0.50, 0.32, 660001, noisy=False)
    for ctrl in CONTROLLERS:
        run_one_controller(wp, we, 660001, ctrl, "box", 3.0, 0.05, 500)

    runs_path = dest / "runs.jsonl"
    rng = random.Random(20261118)
    with runs_path.open("w") as fh:
        for t in tasks:
            for rep in range(repeats):
                order = list(CONTROLLERS)
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                for ctrl in order:
                    res = run_one_controller(
                        t["prob"], t["eps"], t["seed"] + 10000 * rep,
                        ctrl, t["schedule"], t["c_uct"], wall_limit, cap,
                    )
                    fh.write(json.dumps({
                        "suite": t["suite"],
                        "family": t["family"],
                        "m": t["m"],
                        "rho": t["rho"],
                        "reward_mode": t["reward_mode"],
                        "seed": t["seed"] + 10000 * rep,
                        "repeat": rep,
                        "eps": t["eps"],
                        **res,
                    }) + "\n")
                fh.flush()

    summarize(dest)
    manifest = {
        "experiment": "exp6_dag_lucb",
        "smoke": args.smoke,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "sha256_runs": digest(runs_path),
        "sha256_audit": digest(dest / "adaptive_coupling_audit.json"),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"Done exp6_dag_lucb in {manifest['elapsed_s']}s -> {dest}")


if __name__ == "__main__":
    main()
