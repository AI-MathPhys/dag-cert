#!/usr/bin/env python3
"""Experiment V9-1 (P0): Full 2x2 V33 vs. V34 Ablation on Overlapping Multi-Action DAGs.

Compares on identical paired intrinsic Gaussian tapes, physical clock (Eq. V33.1), and
globally certified numerical oracles:
  1. v33_full   : square-index refreshes {k^2}, all-action evidence (J_all nulls/batch)
  2. v33_sparse : four-power refreshes {4^k},   all-action evidence
  3. v33_local  : square-index refreshes {k^2}, action-local evidence (Thm. V34.1, J_max nulls/batch)
  4. v34_full   : four-power refreshes {4^k},   action-local evidence (Full V34)
  5. known_sigma_tracker : oracle known-sigma sequential tracker reference
  6. indep_student_os    : unknown-variance Student-t Optimistic-Separation baseline

Track A: Rank-2 exact cubic solver (Thm. V23.2--V23.3), K in {4, 16, 64}, unique & multi-answer,
         delta in {0.05, 0.01, 1e-4}.
Track B: General d=4, m=4 certified B&B solver (Lem. V22.1, Prop. V22.2), K in {4, 16, 32},
         delta in {0.05, 0.01}.
Also measures cold peak RAM (isolated tracemalloc probe) and end-to-end wall-clock cost
across physical evaluation latencies c_eval in {0, 0.01, 0.1, 1.0, 10.0} ms.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import time
import tracemalloc
from typing import Any

import numpy as np

from dag_mcts.v9_v34_tracker import (
    IntrinsicGaussianTape,
    make_general_d_dag,
    make_rank2_multi_action_dag,
    run_indep_heteroscedastic_os,
    run_known_sigma_info_tracker,
    run_v34_tracker,
)


ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = ROOT / "results/bayesian_ucd_v1/v9_exp1_v34_vs_v33_dag"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_track_a_job(job: tuple[int, bool, float, int]) -> list[dict[str, Any]]:
    K, multi_answer, delta, seed = job
    prob = make_rank2_multi_action_dag(K=K, multi_answer=multi_answer, seed=101 + K)
    regime = "multi" if multi_answer else "unique"
    rows: list[dict[str, Any]] = []

    configs = [
        ("v33_full", "square", False),
        ("v33_sparse", "four_power", False),
        ("v33_local", "square", True),
        ("v34_full", "four_power", True),
    ]
    for mname, sched, local in configs:
        tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)
        r = run_v34_tracker(
            prob,
            tape,
            delta=delta,
            method_name=mname,
            refresh_schedule=sched,
            action_local=local,
            hysteresis_scale=0.04,
            design_tol_scale=0.01,
            null_log_tol=1e-4,
            warm_start_cuts=True,
            max_samples=120_000,
        )
        # Verify Prop. V34.1 pathwise bounds explicitly on v34_full
        bound_design = prob.K * (1 + int(math.floor(math.log(max(1, r.batches), 4))))
        bound_null = prob.j_max * r.batches
        rows.append({
            "track": "rank2_cubic",
            "d": prob.d,
            "m": prob.m,
            "K": K,
            "j_all": prob.j_all,
            "j_max": prob.j_max,
            "regime": regime,
            "delta": delta,
            "seed": seed,
            "method": mname,
            "certified": r.certified,
            "is_correct": r.is_correct,
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "batches": r.batches,
            "design_calls": r.design_calls,
            "null_calls": r.null_calls,
            "design_refreshes": r.design_refreshes,
            "action_switches": r.action_switches,
            "design_ms": round(r.design_time_s * 1e3, 3),
            "null_ms": round(r.null_time_s * 1e3, 3),
            "total_ms": round(r.total_wall_s * 1e3, 3),
            "bnb_nodes": r.total_bnb_nodes,
            "prop_v34_bound_ok": bool(
                (r.design_calls <= bound_design and r.null_calls <= bound_null)
                if mname == "v34_full" else True
            ),
        })

    # Reference baselines on identical paired intrinsic Gaussian tapes
    for mname, runner in (
        ("known_sigma_tracker", lambda tp: run_known_sigma_info_tracker(prob, tp, delta=delta, max_samples=120_000)),
        ("indep_student_os", lambda tp: run_indep_heteroscedastic_os(prob, tp, delta=delta, max_samples=120_000)),
    ):
        tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)
        r = runner(tape)
        rows.append({
            "track": "rank2_cubic",
            "d": prob.d,
            "m": prob.m,
            "K": K,
            "j_all": prob.j_all,
            "j_max": prob.j_max,
            "regime": regime,
            "delta": delta,
            "seed": seed,
            "method": mname,
            "certified": r.certified,
            "is_correct": r.is_correct,
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "batches": r.batches,
            "design_calls": r.design_calls,
            "null_calls": r.null_calls,
            "design_refreshes": r.design_refreshes,
            "action_switches": r.action_switches,
            "design_ms": round(r.design_time_s * 1e3, 3),
            "null_ms": round(r.null_time_s * 1e3, 3),
            "total_ms": round(r.total_wall_s * 1e3, 3),
            "bnb_nodes": r.total_bnb_nodes,
            "prop_v34_bound_ok": True,
        })
    return rows


def _run_track_b_job(job: tuple[int, float, int]) -> list[dict[str, Any]]:
    K, delta, seed = job
    prob = make_general_d_dag(d=4, m=4, K=K, eps=0.03, seed=202 + K)
    rows: list[dict[str, Any]] = []
    configs = [
        ("v33_full", "square", False),
        ("v33_sparse", "four_power", False),
        ("v33_local", "square", True),
        ("v34_full", "four_power", True),
    ]
    for mname, sched, local in configs:
        tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)
        r = run_v34_tracker(
            prob,
            tape,
            delta=delta,
            method_name=mname,
            refresh_schedule=sched,
            action_local=local,
            hysteresis_scale=0.04,
            design_tol_scale=0.015,
            null_log_tol=0.5,
            warm_start_cuts=True,
            fast_qp_screen=True,
            predictable_gate=True,
            max_samples=120_000,
        )
        bound_design = prob.K * (1 + int(math.floor(math.log(max(1, r.batches), 4))))
        bound_null = prob.j_max * r.batches
        rows.append({
            "track": "gend_d4_bnb",
            "d": prob.d,
            "m": prob.m,
            "K": K,
            "j_all": prob.j_all,
            "j_max": prob.j_max,
            "regime": "unique",
            "delta": delta,
            "seed": seed,
            "method": mname,
            "certified": r.certified,
            "is_correct": r.is_correct,
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "batches": r.batches,
            "design_calls": r.design_calls,
            "null_calls": r.null_calls,
            "design_refreshes": r.design_refreshes,
            "action_switches": r.action_switches,
            "design_ms": round(r.design_time_s * 1e3, 3),
            "null_ms": round(r.null_time_s * 1e3, 3),
            "total_ms": round(r.total_wall_s * 1e3, 3),
            "bnb_nodes": r.total_bnb_nodes,
            "prop_v34_bound_ok": bool(
                (r.design_calls <= bound_design and r.null_calls <= bound_null)
                if mname == "v34_full" else True
            ),
        })

    for mname, runner in (
        ("known_sigma_tracker", lambda tp: run_known_sigma_info_tracker(prob, tp, delta=delta, max_samples=120_000)),
        ("indep_student_os", lambda tp: run_indep_heteroscedastic_os(prob, tp, delta=delta, max_samples=120_000)),
    ):
        tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)
        r = runner(tape)
        rows.append({
            "track": "gend_d4_bnb",
            "d": prob.d,
            "m": prob.m,
            "K": K,
            "j_all": prob.j_all,
            "j_max": prob.j_max,
            "regime": "unique",
            "delta": delta,
            "seed": seed,
            "method": mname,
            "certified": r.certified,
            "is_correct": r.is_correct,
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "batches": r.batches,
            "design_calls": r.design_calls,
            "null_calls": r.null_calls,
            "design_refreshes": r.design_refreshes,
            "action_switches": r.action_switches,
            "design_ms": round(r.design_time_s * 1e3, 3),
            "null_ms": round(r.null_time_s * 1e3, 3),
            "total_ms": round(r.total_wall_s * 1e3, 3),
            "bnb_nodes": r.total_bnb_nodes,
            "prop_v34_bound_ok": True,
        })
    return rows


def _measure_peak_memory(ks_rank2: list[int], ks_d4: list[int]) -> list[dict[str, Any]]:
    """Isolated tracemalloc probe (never run during timed runs!)."""
    mem_rows: list[dict[str, Any]] = []
    for K in ks_rank2:
        prob = make_rank2_multi_action_dag(K=K, multi_answer=False, seed=101 + K)
        for mname, sched, local in (("v33_full", "square", False), ("v34_full", "four_power", True)):
            tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=91000)
            tracemalloc.start()
            run_v34_tracker(prob, tape, delta=0.05, method_name=mname, refresh_schedule=sched, action_local=local, null_log_tol=1e-4, max_batches=4)
            _, peak = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            mem_rows.append({"track": "rank2_cubic", "K": K, "method": mname, "peak_kb": round(peak / 1024.0, 2)})
    for K in ks_d4:
        prob = make_general_d_dag(d=4, m=4, K=K, eps=0.03, seed=202 + K)
        for mname, sched, local in (("v33_full", "square", False), ("v34_full", "four_power", True)):
            tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=92000)
            tracemalloc.start()
            run_v34_tracker(prob, tape, delta=0.05, method_name=mname, refresh_schedule=sched, action_local=local, null_log_tol=0.5, fast_qp_screen=True, predictable_gate=True, max_batches=4)
            _, peak = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            mem_rows.append({"track": "gend_d4_bnb", "K": K, "method": mname, "peak_kb": round(peak / 1024.0, 2)})
    return mem_rows


def summarize(out_dir: Path) -> None:
    runs_path = out_dir / "v9_exp1_runs.jsonl"
    rows = [json.loads(line) for line in runs_path.read_text(encoding="utf-8").splitlines() if line.strip()]

    groups: dict[tuple[Any, ...], list[dict[str, Any]]] = defaultdict(list)
    for r in rows:
        key = (r["track"], r["K"], r["regime"], r["delta"], r["method"])
        groups[key].append(r)

    summary_rows: list[dict[str, Any]] = []
    for (track, K, regime, delta, method), grp in sorted(groups.items()):
        n = len(grp)
        certs = [r for r in grp if r["certified"]]
        false_certs = sum(1 for r in certs if not r["is_correct"])
        samples = [r["total_samples"] for r in grp]
        d_calls = [r["design_calls"] for r in grp]
        n_calls = [r["null_calls"] for r in grp]
        d_ms = [r["design_ms"] for r in grp]
        n_ms = [r["null_ms"] for r in grp]
        t_ms = [r["total_ms"] for r in grp]
        bound_ok = all(r.get("prop_v34_bound_ok", True) for r in grp)
        summary_rows.append({
            "track": track,
            "K": K,
            "regime": regime,
            "delta": delta,
            "method": method,
            "runs": n,
            "cert_rate": round(len(certs) / n, 4),
            "false_certs": false_certs,
            "med_samples": round(float(np.median(samples)), 1),
            "mean_samples": round(float(np.mean(samples)), 1),
            "med_batches": round(float(np.median([r["batches"] for r in grp])), 1),
            "med_design_calls": round(float(np.median(d_calls)), 1),
            "med_null_calls": round(float(np.median(n_calls)), 1),
            "med_design_ms": round(float(np.median(d_ms)), 2),
            "med_null_ms": round(float(np.median(n_ms)), 2),
            "med_total_ms": round(float(np.median(t_ms)), 2),
            "mean_switches": round(float(np.mean([r["action_switches"] for r in grp])), 2),
            "prop_v34_bound_ok": bound_ok,
        })

    csv_path = out_dir / "v9_exp1_summary.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)

    # Also build stacked wall-clock table across evaluation latencies c_eval in ms
    wall_rows: list[dict[str, Any]] = []
    for r in summary_rows:
        if r["method"] not in ("v33_full", "v33_sparse", "v33_local", "v34_full", "indep_student_os"):
            continue
        for c_eval_ms in (0.0, 0.01, 0.1, 1.0, 10.0):
            eval_ms = r["med_samples"] * c_eval_ms
            solver_ms = r["med_total_ms"]
            wall_rows.append({
                "track": r["track"],
                "K": r["K"],
                "regime": r["regime"],
                "delta": r["delta"],
                "method": r["method"],
                "c_eval_ms": c_eval_ms,
                "eval_ms": round(eval_ms, 2),
                "design_ms": r["med_design_ms"],
                "null_ms": r["med_null_ms"],
                "total_e2e_ms": round(eval_ms + solver_ms, 2),
            })
    wall_csv = out_dir / "v9_exp1_wallclock_stack.csv"
    with wall_csv.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(wall_rows[0].keys()))
        w.writeheader()
        w.writerows(wall_rows)

    print(f"Wrote {csv_path} ({len(summary_rows)} rows) and {wall_csv} ({len(wall_rows)} rows).")
    # Compact console highlight for delta=0.01 unique
    print("\n=== Highlight: Rank-2 Cubic (unique, delta=0.01) ===")
    for r in summary_rows:
        if r["track"] == "rank2_cubic" and r["regime"] == "unique" and abs(r["delta"] - 0.01) < 1e-9:
            print(
                f"  K={r['K']:2d} {r['method']:19s} cert={r['cert_rate']:.2f} err={r['false_certs']} "
                f"N={r['med_samples']:7.1f} d_call={r['med_design_calls']:5.1f} n_call={r['med_null_calls']:8.1f} "
                f"d_ms={r['med_design_ms']:7.1f} n_ms={r['med_null_ms']:8.1f} tot_ms={r['med_total_ms']:8.1f}"
            )
    print("\n=== Highlight: General d=4 B&B (unique, delta=0.01) ===")
    for r in summary_rows:
        if r["track"] == "gend_d4_bnb" and abs(r["delta"] - 0.01) < 1e-9:
            print(
                f"  K={r['K']:2d} {r['method']:19s} cert={r['cert_rate']:.2f} err={r['false_certs']} "
                f"N={r['med_samples']:7.1f} d_call={r['med_design_calls']:5.1f} n_call={r['med_null_calls']:8.1f} "
                f"d_ms={r['med_design_ms']:7.1f} n_ms={r['med_null_ms']:8.1f} tot_ms={r['med_total_ms']:8.1f}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=OUT_DIR)
    ap.add_argument("--workers", type=int, default=min(24, os.cpu_count() or 8))
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    args = ap.parse_args()

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    if args.smoke:
        ks_a = [4, 16]
        regimes_a = [False]
        deltas_a = [0.05]
        seeds_a = [9001, 9002]
        ks_b = [4, 16]
        deltas_b = [0.05]
        seeds_b = [9501, 9502]
    else:
        ks_a = [4, 16, 64]
        regimes_a = [False, True]
        deltas_a = [0.05, 0.01, 1e-4]
        seeds_a = [91000 + i for i in range(24)]
        ks_b = [4, 16, 32]
        deltas_b = [0.05, 0.01]
        seeds_b = [92000 + i for i in range(16)]

    jobs_a = [(K, ma, d, s) for K in ks_a for ma in regimes_a for d in deltas_a for s in seeds_a]
    jobs_b = [(K, d, s) for K in ks_b for d in deltas_b for s in seeds_b]
    print(f"Launching V9-1: {len(jobs_a)} Track-A jobs + {len(jobs_b)} Track-B jobs across {args.workers} workers...")

    all_rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(_run_track_a_job, j) for j in jobs_a] + [ex.submit(_run_track_b_job, j) for j in jobs_b]
        done = 0
        total = len(futs)
        for fut in as_completed(futs):
            all_rows.extend(fut.result())
            done += 1
            if done % max(1, total // 10) == 0 or done == total:
                print(f"  progress: {done}/{total} jobs ({time.perf_counter()-t0:.1f}s)", flush=True)

    # Sort deterministically for clean diffs/manifests
    all_rows.sort(key=lambda r: (r["track"], r["K"], r["regime"], r["delta"], r["seed"], r["method"]))
    runs_path = out_dir / "v9_exp1_runs.jsonl"
    with runs_path.open("w", encoding="utf-8") as fh:
        for r in all_rows:
            fh.write(json.dumps(r) + "\n")

    mem_rows = _measure_peak_memory(ks_a, ks_b)
    mem_path = out_dir / "v9_exp1_memory.csv"
    with mem_path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(mem_rows[0].keys()))
        w.writeheader()
        w.writerows(mem_rows)

    summarize(out_dir)
    wall = time.perf_counter() - t0
    manifest_files = {}
    for fname in ("v9_exp1_runs.jsonl", "v9_exp1_summary.csv", "v9_exp1_wallclock_stack.csv", "v9_exp1_memory.csv"):
        fp = out_dir / fname
        manifest_files[fname] = {"bytes": fp.stat().st_size, "sha256": _sha256(fp)}
    manifest = {
        "suite": "v9_exp1_v34_vs_v33_dag",
        "smoke": bool(args.smoke),
        "total_rows": len(all_rows),
        "wall_s": round(wall, 2),
        "files": manifest_files,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Completed V9-1 in {wall:.1f}s ({len(all_rows)} runs). Manifest written.")


if __name__ == "__main__":
    main()
