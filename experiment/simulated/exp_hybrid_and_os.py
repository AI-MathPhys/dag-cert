"""Experiment 11 (ICML v5): O(log M) Dual-Bound Witness Covers, Safeguarded Hybrid
Inside-Witness Allocation, and Support-Margin Validation (Theorems 3.1-3.3).

Evaluates three complementary studies:
1. Part A (`hybrid_runs.jsonl` / `summary_hybrid_by_family.csv`):
   Compares `ucb`, `lcb_fast` (`O(log M)` dual-cover LCB-inside without linear support scans),
   `hybrid` (parameter-free Theorem-3.1-backed slack gate `w_t(y_t) >= max(0.5*R_t(a_t), u_t(p_t) - u_t(y_t))`),
   and `opt_sep` (`Optimistic-Separation DAG-LUCB`, Theorem 3.2) across all 11 benchmark families
   from Experiment 10 (`1.0 s` / `30,000` step cap, counterbalanced).
2. Part B (`midgame20_runs.jsonl` / `summary_midgame20.csv`):
   Evaluates `ucb`, `lcb_fast`, `hybrid`, and `opt_sep` across all 20 standard 15x15 `StandardTestset.txt`
   mid-game boards under Experiment 9's exact protocol (`tile_cap=62, d=4, eps=0.025, 1.8 s / 60,000` cap,
   stratified into the 19 strictly zero-containment boards vs. 1 containment-present board).
3. Part C (`star_runs.jsonl` / `summary_star_eps.csv`):
   Tests Theorems 3.2 & 3.3 on the non-containment tied-star Bernoulli family (`N=8, Gamma=g=0.25`)
   across `eps in {0.10, 0.05, 0.02, 0.01, 0.00}`, comparing `ucb`, `hybrid`, `opt_sep`, and `lucb_micro_marg`.
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

from dagcert.benchmarks import (
    contiguous_window_dag,
    overlap_dag,
)
from dagcert._core.v4_baselines import (
    LUCBMicroSession,
    samegame_midgame_case,
)
from dagcert._core.v5_hybrid_and_os import (
    HybridWitnessDAGLUCBSession,
    noncontainment_star_dag,
)
from experiment.simulated.exp_inside_witness import (
    _decoy_trap_dag,
    _heterogeneous_support_dag,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v4_icml_baselines/exp11_hybrid_and_os"

HYBRID_MODES = ("ucb", "lcb_fast", "hybrid", "opt_sep")
STAR_METHODS = ("ucb", "hybrid", "opt_sep", "lucb_micro_marg")
SEEDS = tuple(range(680001, 680007))
STAR_SEEDS = tuple(range(710001, 710009))
STAR_EPSILONS = (0.10, 0.05, 0.02, 0.01, 0.00)
DELTA = 0.05


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    return sess.evidence.conflict


def make_session(prob, eps: float, seed: int, method: str, schedule: str):
    if method in HYBRID_MODES:
        return HybridWitnessDAGLUCBSession(
            prob, seed, eps, mode=method, delta=DELTA, schedule=schedule,
        )
    if method == "lucb_micro_marg":
        return LUCBMicroSession(
            prob, seed, eps, delta=DELTA, schedule=schedule, stop_rule="marginal",
        )
    raise ValueError(f"Unknown method: {method}")


def run_one(
    prob,
    eps: float,
    seed: int,
    method: str,
    schedule: str,
    wall_limit: float,
    cap: int,
    regret_tol: float = 1e-12,
) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    opt = values[prob.graph.root]
    regrets = [max(0.0, opt - values[c]) for c in prob.graph.children[prob.graph.root]]

    t0 = time.perf_counter()
    sess = make_session(prob, eps, seed, method, schedule)
    elapsed = time.perf_counter() - t0
    while (not sess.certified and not _has_conflict(sess)
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
    false_cert = bool(cert and true_reg > eps + regret_tol)
    assert not false_cert, f"False certificate in {method}: {true_reg} > {eps}"
    return {
        "method": method,
        "schedule": schedule,
        "certified": cert,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "total_s": total_s,
        "total_work": work,
        "final_simple_regret": round(true_reg, 5),
    }


def build_part_a_tasks(smoke: bool = False) -> list[dict]:
    if smoke:
        p1, e1 = _decoy_trap_dag(16, 4, 680001)
        p2, e2 = _heterogeneous_support_dag(64, 8, 680001)
        return [
            {"family": "decoy_trap_16", "seed": 680001, "prob": p1, "eps": e1, "schedule": "box", "tol": 1e-12},
            {"family": "hetero_support_64", "seed": 680001, "prob": p2, "eps": e2, "schedule": "box", "tol": 1e-12},
        ]

    tasks = []
    for s in SEEDS:
        pd, ed = _decoy_trap_dag(16, 4, s)
        tasks.append({"family": "decoy_trap_16", "seed": s, "prob": pd, "eps": ed, "schedule": "box", "tol": 1e-12})
    for m in (64, 256):
        for s in SEEDS:
            ph, eh = _heterogeneous_support_dag(m, 8 if m == 64 else 16, s)
            tasks.append({"family": f"hetero_support_{m}", "seed": s, "prob": ph, "eps": eh, "schedule": "box", "tol": 1e-12})
    for m in (64, 256):
        for rho in (0.00, 0.50, 0.75):
            for s in SEEDS:
                p, e = overlap_dag(m, rho, 0.32, s, noisy=True)
                tasks.append({
                    "family": f"overlap_{m}_rho{int(round(rho*100)):02d}",
                    "seed": s, "prob": p, "eps": e, "schedule": "box", "tol": 1e-12,
                })
    for m in (64, 256):
        for s in SEEDS:
            p, e = contiguous_window_dag(m, 16 if m == 256 else 8, s, noisy=True)
            tasks.append({"family": f"window_{m}", "seed": s, "prob": p, "eps": e, "schedule": "box", "tol": 1e-12})
    for idx in range(1, 11):
        p, e, _ = samegame_midgame_case(idx, depth=4, tile_cap=62, eps=0.025, ref_samples=8192)
        tasks.append({
            "family": "samegame_mid15x15_d4_zero_contain",
            "seed": 681000 + idx, "prob": p, "eps": e, "schedule": "emp_bernstein", "tol": 0.005,
        })
    return tasks


def build_part_b_midgame20(smoke: bool = False) -> list[dict]:
    indices = (1, 6) if smoke else tuple(range(1, 21))
    ref_n = 512 if smoke else 8192
    items = []
    for idx in indices:
        prob, ep, diag = samegame_midgame_case(idx, depth=4, tile_cap=62, eps=0.025, ref_samples=ref_n)
        has_cont = diag["containment_pairs"] > 0
        items.append({
            "stratum": "midgame_15x15_d4_with_contain" if has_cont else "midgame_15x15_d4_zero_contain",
            "instance": f"mid_{idx:02d}_d4",
            "seed": 691000 + idx,
            "prob": prob,
            "eps": ep,
        })
    return items


def build_part_c_star(smoke: bool = False) -> list[dict]:
    eps_list = (0.05, 0.00) if smoke else STAR_EPSILONS
    seeds = STAR_SEEDS[:2] if smoke else STAR_SEEDS
    items = []
    for eps in eps_list:
        prob, _ = noncontainment_star_dag(n_rivals=8, gap=0.25, eps=eps)
        for s in seeds:
            items.append({
                "eps": eps,
                "seed": s,
                "prob": prob,
            })
    return items


def summarize(dest: Path) -> None:
    hyb_runs = [json.loads(line) for line in (dest / "hybrid_runs.jsonl").read_text().splitlines() if line.strip()]
    mid_runs = [json.loads(line) for line in (dest / "midgame20_runs.jsonl").read_text().splitlines() if line.strip()]
    star_runs = [json.loads(line) for line in (dest / "star_runs.jsonl").read_text().splitlines() if line.strip()]

    hyb_rows = []
    for fam in sorted({r["family"] for r in hyb_runs}):
        for mode in HYBRID_MODES:
            sub = [r for r in hyb_runs if r["family"] == fam and r["method"] == mode]
            if not sub:
                continue
            hyb_rows.append({
                "family": fam,
                "method": mode,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "mean_final_regret": round(statistics.mean(r["final_simple_regret"] for r in sub), 5),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_hybrid_by_family.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(hyb_rows[0].keys()))
        w.writeheader()
        w.writerows(hyb_rows)

    mid_rows = []
    for st in sorted({r["stratum"] for r in mid_runs}):
        for mode in HYBRID_MODES:
            sub = [r for r in mid_runs if r["stratum"] == st and r["method"] == mode]
            if not sub:
                continue
            mid_rows.append({
                "stratum": st,
                "method": mode,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "mean_total_ms": round(1e3 * statistics.mean(r["total_s"] for r in sub), 3),
                "mean_final_regret": round(statistics.mean(r["final_simple_regret"] for r in sub), 5),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_midgame20.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(mid_rows[0].keys()))
        w.writeheader()
        w.writerows(mid_rows)

    star_rows = []
    for eps in sorted({r["eps"] for r in star_runs}, reverse=True):
        for meth in STAR_METHODS:
            sub = [r for r in star_runs if r["eps"] == eps and r["method"] == meth]
            if not sub:
                continue
            star_rows.append({
                "eps": eps,
                "method": meth,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_star_eps.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(star_rows[0].keys()))
        w.writeheader()
        w.writerows(star_rows)

    (dest / "summary.json").write_text(json.dumps({
        "total_runs": len(hyb_runs) + len(mid_runs) + len(star_runs),
        "hybrid_runs": len(hyb_runs),
        "midgame20_runs": len(mid_runs),
        "star_runs": len(star_runs),
        "total_false_certificates": (
            sum(r["false_certificates"] for r in hyb_rows)
            + sum(r["false_certificates"] for r in mid_rows)
            + sum(r["false_certificates"] for r in star_rows)
        ),
        "hybrid_by_family": hyb_rows,
        "midgame20": mid_rows,
        "star_eps": star_rows,
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
    repeats = 1 if args.smoke else 2

    # Warm-up
    wp, we = overlap_dag(64, 0.50, 0.32, 680001, noisy=True)
    for m in STAR_METHODS + ("lcb_fast",):
        run_one(wp, we, 680001, m, "box", 0.04, 300)

    rng = random.Random(20261125)

    # Part A: 11-family Inside-Witness Hybrid & O(log M) Dual-Cover benchmark
    part_a = build_part_a_tasks(smoke=args.smoke)
    hyb_path = dest / "hybrid_runs.jsonl"
    cap_a = 5000 if args.smoke else 30000
    wall_a = 0.25 if args.smoke else 1.0
    with hyb_path.open("w") as fh:
        for t in part_a:
            for rep in range(repeats):
                order = list(HYBRID_MODES)
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                for mode in order:
                    res = run_one(
                        t["prob"], t["eps"], t["seed"] + 10000 * rep,
                        mode, t["schedule"], wall_a, cap_a, regret_tol=t["tol"],
                    )
                    fh.write(json.dumps({
                        "family": t["family"],
                        "seed": t["seed"] + 10000 * rep,
                        "repeat": rep,
                        "eps": t["eps"],
                        **res,
                    }) + "\n")
                fh.flush()

    # Part B: Full 20-board StandardTestset.txt Mid-Game 15x15 SameGame (1.8 s / 60k cap)
    part_b = build_part_b_midgame20(smoke=args.smoke)
    mid_path = dest / "midgame20_runs.jsonl"
    cap_b = 6000 if args.smoke else 60000
    wall_b = 0.25 if args.smoke else 1.8
    with mid_path.open("w") as fm:
        for it in part_b:
            for rep in range(repeats):
                order = list(HYBRID_MODES)
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                for mode in order:
                    res = run_one(
                        it["prob"], it["eps"], it["seed"] + 10000 * rep,
                        mode, "emp_bernstein", wall_b, cap_b, regret_tol=0.005,
                    )
                    fm.write(json.dumps({
                        "stratum": it["stratum"],
                        "instance": it["instance"],
                        "seed": it["seed"] + 10000 * rep,
                        "repeat": rep,
                        "eps": it["eps"],
                        **res,
                    }) + "\n")
                fm.flush()

    # Part C: Theorem 3.2 & 3.3 Non-Containment Tied-Star Bernoulli Scaling across eps -> 0
    part_c = build_part_c_star(smoke=args.smoke)
    star_path = dest / "star_runs.jsonl"
    cap_c = 6000 if args.smoke else 50000
    wall_c = 0.25 if args.smoke else 1.2
    with star_path.open("w") as fs:
        for it in part_c:
            order = list(STAR_METHODS)
            rng.shuffle(order)
            for meth in order:
                res = run_one(
                    it["prob"], it["eps"], it["seed"],
                    meth, "box", wall_c, cap_c, regret_tol=1e-12,
                )
                fs.write(json.dumps({
                    "eps": it["eps"],
                    "seed": it["seed"],
                    **res,
                }) + "\n")
            fs.flush()

    summarize(dest)
    manifest = {
        "experiment": "exp11_hybrid_and_os",
        "smoke": args.smoke,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "sha256_hybrid": digest(hyb_path),
        "sha256_midgame20": digest(mid_path),
        "sha256_star": digest(star_path),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"Done exp11_hybrid_and_os in {manifest['elapsed_s']}s -> {dest}")


if __name__ == "__main__":
    main()
