#!/usr/bin/env python3
"""Experiment V10-1: Native -O3 C++17 Certified B&B Scaling Across d in {2, 4, 6, 8}.

Directly extends V9-4 with our native `-O3 -std=c++17` outward-certified Branch-and-Bound
and Dual-QP kernel (`dag_mcts/_cpp_v34_bnb.cpp`):
  - Measures exact paired Python vs. C++17 speedup on identical observation tapes for
    d in {4, 6}, K in {4, 16}.
  - Sweeps log-enclosure tolerance zeta in {1.0, 0.1, 1e-3, 1e-5} across d in {2, 4, 6, 8},
    K in {4, 16}, bringing d=6 from tens of seconds down to sub-second / ~1s and pushing
    certified general-d unknown-variance tracking to d=8!
  - Verifies 0 false certificates and updated wall-clock break-even c_eval^* vs Student-t OS.
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
from typing import Any

import numpy as np

from dagcert._core.v9_v34_tracker import (
    ComponentPolyhedron,
    CppV34BnBRunner,
    HeteroscedasticDAGProblem,
    IntrinsicGaussianTape,
    make_general_d_dag,
    make_rank2_multi_action_dag,
    run_indep_heteroscedastic_os,
    run_v34_tracker,
)


ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = ROOT / "results/bayesian_ucd_v1/v10_exp1_cpp_v34_scaling"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _strip_2d_boundary(prob: HeteroscedasticDAGProblem) -> HeteroscedasticDAGProblem:
    comps_g = [
        [
            ComponentPolyhedron(
                action=c.action, terminal=c.terminal, A=c.A, b=c.b, feasible_point=c.feasible_point
            )
            for c in act_cs
        ]
        for act_cs in prob.components
    ]
    return HeteroscedasticDAGProblem(
        name=prob.name + "_bnb",
        H=prob.H,
        phi=prob.phi,
        supports=prob.supports,
        theta_star=prob.theta_star,
        sigma=prob.sigma,
        eps=prob.eps,
        basis_idx=prob.basis_idx,
        components=comps_g,
    )


def _run_job(job: tuple[int, int, float, int, str]) -> dict[str, Any]:
    d, K, zeta, seed, mname = job
    delta = 0.05
    if d == 2:
        prob_exact = make_rank2_multi_action_dag(K=K, multi_answer=False, sigma=(0.5, 2.0), eps=0.02, seed=404 + K)
        prob_bnb = _strip_2d_boundary(prob_exact)
    else:
        prob_bnb = make_general_d_dag(d=d, m=d, K=K, eps=0.03, seed=505 + 10 * d + K)

    if mname == "indep_student_os":
        tape_os = IntrinsicGaussianTape(prob_bnb.true_query_means, prob_bnb.sigma, seed=seed)
        r_os = run_indep_heteroscedastic_os(prob_bnb, tape_os, delta=delta, max_samples=150_000)
        return {
            "d": d, "K": K, "zeta": zeta, "seed": seed, "method": mname,
            "certified": r_os.certified, "is_correct": r_os.is_correct,
            "total_samples": r_os.total_samples, "batches": r_os.batches,
            "design_calls": 0, "null_calls": 0, "bnb_nodes": 0,
            "root_qp_screened": 0, "root_qp_frac": 0.0,
            "design_ms": 0.0, "null_ms": 0.0,
            "total_ms": round(r_os.total_wall_s * 1e3, 2), "ms_per_null": 0.0,
        }

    dtol = 0.015 if d >= 4 else 0.005
    cfg_map: dict[str, dict[str, Any]] = {
        "cpp_cold_bnb": dict(warm_start_cuts=False, fast_qp_screen=False, predictable_gate=False, use_cpp_bnb=True),
        "cpp_hybrid_qp_screened": dict(warm_start_cuts=True, fast_qp_screen=True, predictable_gate=False, use_cpp_bnb=True),
        "cpp_hybrid_qp_gated": dict(warm_start_cuts=True, fast_qp_screen=True, predictable_gate=True, use_cpp_bnb=True),
        "py_hybrid_qp_gated": dict(warm_start_cuts=True, fast_qp_screen=True, predictable_gate=True, use_cpp_bnb=False),
    }
    kw = cfg_map[mname]
    tape = IntrinsicGaussianTape(prob_bnb.true_query_means, prob_bnb.sigma, seed=seed)
    r = run_v34_tracker(
        prob_bnb,
        tape,
        delta=delta,
        method_name=mname,
        refresh_schedule="four_power",
        action_local=True,
        design_tol_scale=dtol,
        null_log_tol=zeta,
        max_samples=150_000,
        **kw,
    )
    return {
        "d": d,
        "K": K,
        "zeta": zeta,
        "seed": seed,
        "method": mname,
        "certified": r.certified,
        "is_correct": r.is_correct,
        "total_samples": r.total_samples,
        "batches": r.batches,
        "design_calls": r.design_calls,
        "null_calls": r.null_calls,
        "bnb_nodes": r.total_bnb_nodes,
        "root_qp_screened": r.root_qp_screened_nulls,
        "root_qp_frac": round(r.root_qp_screened_nulls / max(1, r.null_calls), 4),
        "design_ms": round(r.design_time_s * 1e3, 2),
        "null_ms": round(r.null_time_s * 1e3, 2),
        "total_ms": round(r.total_wall_s * 1e3, 2),
        "ms_per_null": round((r.null_time_s * 1e3) / max(1, r.null_calls), 3),
    }


def summarize(out_dir: Path) -> None:
    runs_path = out_dir / "v10_exp1_runs.jsonl"
    rows = [json.loads(l) for l in runs_path.read_text(encoding="utf-8").splitlines() if l.strip()]

    groups: dict[tuple[int, int, float, str], list[dict[str, Any]]] = defaultdict(list)
    for r in rows:
        groups[(r["d"], r["K"], r["zeta"], r["method"])].append(r)

    summary_rows: list[dict[str, Any]] = []
    for (d, K, zeta, meth), grp in sorted(groups.items()):
        n = len(grp)
        certs = [r for r in grp if r["certified"]]
        errs = sum(1 for r in certs if not r["is_correct"])
        summary_rows.append({
            "d": d,
            "K": K,
            "zeta": zeta,
            "method": meth,
            "runs": n,
            "cert_rate": round(len(certs) / n, 4),
            "false_certs": errs,
            "med_samples": round(float(np.median([r["total_samples"] for r in grp])), 1),
            "med_null_calls": round(float(np.median([r["null_calls"] for r in grp])), 1),
            "med_bnb_nodes": round(float(np.median([r["bnb_nodes"] for r in grp])), 1),
            "med_design_ms": round(float(np.median([r["design_ms"] for r in grp])), 2),
            "med_null_ms": round(float(np.median([r["null_ms"] for r in grp])), 2),
            "med_total_ms": round(float(np.median([r["total_ms"] for r in grp])), 2),
            "med_ms_per_null": round(float(np.median([r["ms_per_null"] for r in grp])), 3),
        })

    csv_path = out_dir / "v10_exp1_summary.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)

    # Compute exact paired Python vs C++17 speedups at zeta=0.1
    py_map = {(r["d"], r["K"]): r for r in summary_rows if r["method"] == "py_hybrid_qp_gated" and abs(r["zeta"] - 0.1) < 1e-9}
    cpp_map = {(r["d"], r["K"]): r for r in summary_rows if r["method"] == "cpp_hybrid_qp_gated" and abs(r["zeta"] - 0.1) < 1e-9}
    speedup_rows = []
    for key, r_cpp in sorted(cpp_map.items()):
        r_py = py_map.get(key)
        sp_tot = (r_py["med_total_ms"] / max(0.01, r_cpp["med_total_ms"])) if r_py else float("nan")
        sp_null = (r_py["med_null_ms"] / max(0.01, r_cpp["med_null_ms"])) if r_py else float("nan")
        speedup_rows.append({
            "d": key[0],
            "K": key[1],
            "py_total_ms": r_py["med_total_ms"] if r_py else "NA",
            "cpp_total_ms": r_cpp["med_total_ms"],
            "total_speedup_x": round(sp_tot, 2) if math.isfinite(sp_tot) else "NA",
            "py_null_ms": r_py["med_null_ms"] if r_py else "NA",
            "cpp_null_ms": r_cpp["med_null_ms"],
            "null_speedup_x": round(sp_null, 2) if math.isfinite(sp_null) else "NA",
            "cpp_med_samples": r_cpp["med_samples"],
        })
    sp_csv = out_dir / "v10_exp1_cpp_speedup.csv"
    with sp_csv.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(speedup_rows[0].keys()))
        w.writeheader()
        w.writerows(speedup_rows)

    print(f"Wrote {csv_path} ({len(summary_rows)} rows) and {sp_csv} ({len(speedup_rows)} rows).")
    print("\n=== C++17 vs Python Paired Speedup (zeta=0.1, Hybrid QP+Gated) ===")
    for s in speedup_rows:
        print(
            f"  d={s['d']} K={s['K']:2d} | Py={str(s['py_total_ms']):>9s} ms -> C++={s['cpp_total_ms']:7.1f} ms "
            f"(total {str(s['total_speedup_x']):>6s}x, null {str(s['null_speedup_x']):>6s}x) | N={s['cpp_med_samples']}"
        )
    print("\n=== Native C++17 Scaling Across d in {2, 4, 6, 8} (K=16) ===")
    for r in summary_rows:
        if r["K"] == 16 and r["method"] in ("cpp_cold_bnb", "cpp_hybrid_qp_gated", "indep_student_os"):
            print(
                f"  d={r['d']} zeta={r['zeta']:<6g} {r['method']:22s} cert={100*r['cert_rate']:5.1f}% err={r['false_certs']} "
                f"N={r['med_samples']:6.1f} nodes={r['med_bnb_nodes']:8.1f} tot_ms={r['med_total_ms']:7.1f} (des={r['med_design_ms']:6.1f} null={r['med_null_ms']:6.1f})"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=OUT_DIR)
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    args = ap.parse_args()

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    # Pre-compile shared library once before spawning worker pool!
    CppV34BnBRunner.ensure_loaded()

    t0 = time.perf_counter()
    jobs: list[tuple[int, int, float, int, str]] = []
    if args.smoke:
        spec = [(4, [4], [0.1], 2), (6, [4], [0.1], 2)]
    else:
        spec = [
            (2, [4, 16], [1.0, 0.1, 1e-3, 1e-5], 16),
            (4, [4, 16], [1.0, 0.1, 1e-3, 1e-5], 16),
            (6, [4, 16], [1.0, 0.1, 1e-3, 1e-5], 16),
            (8, [4, 16], [1.0, 0.1, 1e-3, 1e-5], 8),
        ]

    for d, Ks, zetas, n_seeds in spec:
        for K in Ks:
            for s in range(n_seeds):
                seed = 95000 + d * 1000 + K * 100 + s
                jobs.append((d, K, 0.1, seed, "indep_student_os"))
                if d in (4, 6) and s < 8:
                    jobs.append((d, K, 0.1, seed, "py_hybrid_qp_gated"))
                for zeta in zetas:
                    for mname in ("cpp_cold_bnb", "cpp_hybrid_qp_screened", "cpp_hybrid_qp_gated"):
                        jobs.append((d, K, zeta, seed, mname))

    # Heaviest first (Python d=6, then C++ d=8)
    jobs.sort(key=lambda j: (0 if j[4] == "py_hybrid_qp_gated" else 1, -j[0], -j[1], j[2]))
    print(f"[V10-1] Running {len(jobs)} C++17 B&B scaling jobs across {args.workers} workers...", flush=True)

    all_rows: list[dict[str, Any]] = []
    done = 0
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(_run_job, j) for j in jobs]
        for fut in as_completed(futs):
            all_rows.append(fut.result())
            done += 1
            if done % 100 == 0 or done == len(jobs):
                print(f"  [V10-1] {done}/{len(jobs)} jobs done ({time.perf_counter()-t0:.1f}s)", flush=True)

    runs_path = out_dir / "v10_exp1_runs.jsonl"
    all_rows.sort(key=lambda r: (r["d"], r["K"], -r["zeta"], r["method"], r["seed"]))
    with runs_path.open("w", encoding="utf-8") as fh:
        for r in all_rows:
            fh.write(json.dumps(r) + "\n")

    summarize(out_dir)

    manifest_files = ["v10_exp1_runs.jsonl", "v10_exp1_summary.csv", "v10_exp1_cpp_speedup.csv"]
    manifest = {
        "experiment": "v10_exp1_cpp_v34_scaling",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "total_runs": len(all_rows),
        "files": {f: {"sha256": _sha256(out_dir / f), "bytes": (out_dir / f).stat().st_size} for f in manifest_files},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"[V10-1] Completed in {manifest['elapsed_s']:.1f}s.")


if __name__ == "__main__":
    main()
