"""Experiment 10 (ICML v4 Ablation): Inside-Witness Selection in Exact-Regret-DAG-LUCB.

Compares three choices of the inside-support witness `z_t^{in} in S(a*_t)` when paired
with the exact outside challenger witness `z_t^{out} = argmax_{z notin S(a*_t)} u_t(z)`
and exact stopping rule `R_t(a*_t) <= eps`:
1. `ucb` (Proposed optimistic inside witness): `argmax_{z in S(a*_t)} u_t(z)`
2. `lcb` (Certificate lower-bound witness): `argmax_{z in S(a*_t)} l_t(z)`
3. `mean` (Empirical plug-in witness): `argmax_{z in S(a*_t)} mu_hat_t(z)`

Demonstrates empirically why `lcb` stalls on multi-leaf supports (locking onto the first
mediocre leaf whose lower bound exceeds zero while leaving the true optimal leaf in S(a*_t)
unvisited at l_t = 0) and `mean` suffers premature lock-in after initial zero draws, whereas
`ucb` guarantees `u_t(z_t^{in}) = U_t(a*_t) >= V*(a*_t)` on the good event and certifies reliably.
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

from dag_mcts.graph import DAG, Problem
from dag_mcts.v2_benchmarks import (
    contiguous_window_dag,
    overlap_dag,
)
from dag_mcts.v4_baselines import (
    BoundedNoiseProblem,
    InsideWitnessDAGLUCBSession,
    samegame_midgame_case,
)


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/uct_v4_icml_baselines/exp10_inside_witness"

MODES = ("ucb", "mean", "lcb")
SEEDS = tuple(range(680001, 680007))  # 6 seeds x 2 counterbalanced repeats
DELTA = 0.05
STEP_CAP = 30000
WALL_LIMIT_S = 1.0


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _heterogeneous_support_dag(m: int = 128, k_actions: int = 8, seed: int = 0) -> tuple[Problem, float]:
    """Multi-leaf DAG where each root action reaches low, near-rival, and private leaves.

    Models heterogeneous subtrees where early lower-bound leaders inside S(a*_t) are
    near-rival decoys (~0.74), while the true optimal terminal (0.94) sits at a higher index
    inside S(a*_t) alongside shared hub leaves (~0.72).
    """
    rng = random.Random(seed * 31337 + m)
    rows: list[tuple[int, ...]] = [()]
    leaves = list(range(1, m + 1))
    rows.extend([()] * m)
    shared = leaves[: m // 2]
    priv = leaves[m // 2 :]
    per_act = len(priv) // k_actions
    actions = []
    means: dict[int, float] = {}
    for z in shared:
        means[z] = 0.35 + 0.38 * rng.random()
    means[shared[0]] = 0.74  # Shared near-rival decoy visited first by lowest leaf ID!

    for a in range(k_actions):
        block = priv[a * per_act : (a + 1) * per_act]
        for idx, z in enumerate(block):
            if a == 0 and idx == len(block) - 1:
                means[z] = 0.94  # True winner at high leaf ID inside S(a*)
            elif idx == 0:
                means[z] = 0.73 + 0.02 * rng.random()
            else:
                means[z] = 0.25 + 0.30 * rng.random()
        act = len(rows)
        rows.append(tuple(shared + block))
        actions.append(act)
    rng.shuffle(actions)
    rows[0] = tuple(actions)
    return BoundedNoiseProblem(f"hetero_inside_{m}", DAG(rows), means, noise_halfwidth=0.08), 0.03


def _decoy_trap_dag(m: int = 64, k_actions: int = 8, seed: int = 0) -> tuple[Problem, float]:
    """Bernoulli DAG where S(a*) contains low-ID near-rival decoy leaves alongside a high-ID optimum.

    Models subtrees with heterogeneous leaf quality where a rival action reaches mean ~0.80,
    while S(a*) contains both mediocre low-ID decoy leaves (~0.72, whose lower bound rises
    above 0 first after initial sweeps) and the true optimal leaf (0.95) at a higher leaf ID.
    Tests whether non-optimistic inside witnesses (`lcb`, `mean`) suffer premature lock-in.
    """
    rng = random.Random(seed * 41999 + m)
    rows: list[tuple[int, ...]] = [()]
    leaves = list(range(1, m + 1))
    rows.extend([()] * m)
    shared = leaves[: m // 2]
    priv = leaves[m // 2 :]
    per_act = len(priv) // k_actions
    actions = []
    means: dict[int, float] = {}
    for z in shared:
        means[z] = 0.25 + 0.35 * rng.random()

    for a in range(k_actions):
        block = priv[a * per_act : (a + 1) * per_act]
        for idx, z in enumerate(block):
            if a == 0 and idx == 0:
                means[z] = 0.80  # Private decoy inside S(a*) tied with best rival (0.80)!
            elif a == 0 and idx == len(block) - 1:
                means[z] = 0.95  # True optimal leaf inside S(a*) at higher leaf ID
            elif a == 1 and idx == 0:
                means[z] = 0.80  # Strong outside rival leaf in S(b) \ S(a*)
            else:
                means[z] = 0.25 + 0.35 * rng.random()
        act = len(rows)
        rows.append(tuple(shared + block))
        actions.append(act)
    rng.shuffle(actions)
    rows[0] = tuple(actions)
    return BoundedNoiseProblem(f"decoy_trap_{m}", DAG(rows), means, noise_halfwidth=0.02), 0.03


def build_tasks(smoke: bool = False) -> list[dict]:
    if smoke:
        p1, e1 = overlap_dag(64, 0.50, 0.32, 680001, noisy=True)
        p2, e2 = _decoy_trap_dag(16, 4, 680001)
        return [
            {"family": "overlap_64_rho50", "seed": 680001, "prob": p1, "eps": e1, "schedule": "box"},
            {"family": "decoy_trap_16", "seed": 680001, "prob": p2, "eps": e2, "schedule": "box"},
        ]

    tasks = []
    for s in SEEDS:
        pd, ed = _decoy_trap_dag(16, 4, s)
        tasks.append({
            "family": "decoy_trap_16",
            "seed": s, "prob": pd, "eps": ed, "schedule": "box",
        })
    for m in (64, 256):
        for s in SEEDS:
            ph, eh = _heterogeneous_support_dag(m, 8 if m == 64 else 16, s)
            tasks.append({
                "family": f"hetero_support_{m}",
                "seed": s, "prob": ph, "eps": eh, "schedule": "box",
            })
    for m in (64, 256):
        for rho in (0.00, 0.50, 0.75):
            for s in SEEDS:
                p, e = overlap_dag(m, rho, 0.32, s, noisy=True)
                tasks.append({
                    "family": f"overlap_{m}_rho{int(round(rho*100)):02d}",
                    "seed": s, "prob": p, "eps": e, "schedule": "box",
                })
    for m in (64, 256):
        for s in SEEDS:
            p, e = contiguous_window_dag(m, 16 if m == 256 else 8, s, noisy=True)
            tasks.append({
                "family": f"window_{m}",
                "seed": s, "prob": p, "eps": e, "schedule": "box",
            })
    for idx in range(1, 11):
        p, e, _ = samegame_midgame_case(idx, depth=4, tile_cap=62, eps=0.025, ref_samples=8192)
        tasks.append({
            "family": "samegame_mid15x15_d4_zero_contain",
            "seed": 681000 + idx, "prob": p, "eps": e, "schedule": "emp_bernstein",
        })
    return tasks


def run_one(prob, eps: float, seed: int, inside_mode: str,
            schedule: str, wall_limit: float, cap: int) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    opt = values[prob.graph.root]
    regrets = [max(0.0, opt - values[c]) for c in prob.graph.children[prob.graph.root]]

    t0 = time.perf_counter()
    sess = InsideWitnessDAGLUCBSession(
        prob, seed, eps, inside_mode=inside_mode, delta=DELTA, schedule=schedule,
    )
    elapsed = time.perf_counter() - t0
    while (not sess.certified and not sess.monitor.evidence.conflict
           and sess.calls < cap and elapsed < wall_limit):
        sess.step()
        elapsed = time.perf_counter() - t0

    cert = sess.certified
    act = sess.action
    calls = sess.calls
    work = sess.work
    del sess
    total_s = time.perf_counter() - t0

    true_reg = regrets[act]
    false_cert = bool(cert and true_reg > eps + 1e-12)
    assert not false_cert, f"False certificate in {inside_mode}: {true_reg} > {eps}"
    return {
        "inside_mode": inside_mode,
        "schedule": schedule,
        "certified": cert,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "total_s": total_s,
        "total_work": work,
        "final_simple_regret": true_reg,
    }


def summarize(dest: Path) -> None:
    runs = [json.loads(line) for line in (dest / "runs.jsonl").read_text().splitlines() if line.strip()]
    rows = []
    for fam in sorted({r["family"] for r in runs}):
        for mode in MODES:
            sub = [r for r in runs if r["family"] == fam and r["inside_mode"] == mode]
            if not sub:
                continue
            rows.append({
                "family": fam,
                "inside_mode": mode,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "mean_final_regret": round(statistics.mean(r["final_simple_regret"] for r in sub), 5),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_by_family.csv").open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    (dest / "summary.json").write_text(json.dumps({
        "total_runs": len(runs),
        "total_false_certificates": sum(r["false_certificates"] for r in rows),
        "by_family": rows,
    }, indent=2))


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
    tasks = build_tasks(smoke=args.smoke)
    repeats = 1 if args.smoke else 2
    wall_limit = 0.25 if args.smoke else WALL_LIMIT_S
    cap = 5000 if args.smoke else STEP_CAP

    wp, we = overlap_dag(64, 0.50, 0.32, 680001, noisy=True)
    for m in MODES:
        run_one(wp, we, 680001, m, "box", 0.05, 500)

    runs_path = dest / "runs.jsonl"
    rng = random.Random(20261120)
    with runs_path.open("w") as fh:
        for t in tasks:
            for rep in range(repeats):
                order = list(MODES)
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                for mode in order:
                    res = run_one(
                        t["prob"], t["eps"], t["seed"] + 10000 * rep,
                        mode, t["schedule"], wall_limit, cap,
                    )
                    fh.write(json.dumps({
                        "family": t["family"],
                        "seed": t["seed"] + 10000 * rep,
                        "repeat": rep,
                        "eps": t["eps"],
                        **res,
                    }) + "\n")
                fh.flush()

    summarize(dest)
    manifest = {
        "experiment": "exp10_inside_witness",
        "smoke": args.smoke,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "sha256_runs": digest(runs_path),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"Done exp10_inside_witness in {manifest['elapsed_s']}s -> {dest}")


if __name__ == "__main__":
    main()
