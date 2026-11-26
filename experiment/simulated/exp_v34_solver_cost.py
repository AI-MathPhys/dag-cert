#!/usr/bin/env python3
"""Experiment V9-4 (P1): Solver Accuracy, Cost of Certified Global Enclosures, & Break-Even.

Quantifies the explicit computational boundary of V34 (Prop. V34.1 & Cor. V34.2): what is
the real wall-clock and arithmetic cost of guaranteeing outward-certified global bounds
so the algorithm never stops on an incorrectly rounded or locally trapped likelihood?
  - Part A (Tolerance & Solver-Architecture Sweep across d in {2, 4, 6}, K in {4, 16}):
      Sweeps null log-enclosure tolerance zeta in {1.0, 0.1, 1e-3, 1e-5} (noting Prop. V32.1
      guarantees asymptotic optimality already for zeta <= 1.0 nat!) across:
        1. cold_bnb_certified  : cold B&B + cold Kelley design cuts (100% outward-certified)
        2. warm_bnb_certified  : Prop. V22.3 reused affine cuts + warm primal u_0
        3. hybrid_qp_screened  : Prop. V22.2 root-QP + e-factor-aware certified screening + warm cuts
        4. hybrid_qp_gated     : hybrid_qp_screened + Prop. V32.1 predictable batch gate
        5. exact_cubic_v23     : (for d=2) exact 7-candidate cubic projection (Thm. V23.2)
  - Part B (End-to-End Break-Even Frontier vs. Indep. Student-t OS):
      Computes the minimum per-evaluation latency c_eval^* (ms) at which certified V34 beats
      O(log M) Independent Student-t OS in total wall-clock time across d in {2, 4, 6} and K.
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

from joint_root_cert._core.v9_v34_tracker import (
    ComponentPolyhedron,
    HeteroscedasticDAGProblem,
    IntrinsicGaussianTape,
    make_general_d_dag,
    make_rank2_multi_action_dag,
    run_indep_heteroscedastic_os,
    run_v34_tracker,
)


ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = ROOT / "results/bayesian_ucd_v1/v9_exp4_solver_cost_of_validity"


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


def _run_single_method_job(job: tuple[int, int, float, int, str]) -> dict[str, Any]:
    d, K, zeta, seed, mname = job
    delta = 0.05
    if d == 2:
        prob_exact = make_rank2_multi_action_dag(K=K, multi_answer=False, sigma=(0.5, 2.0), eps=0.02, seed=404 + K)
        prob_bnb = _strip_2d_boundary(prob_exact)
    else:
        prob_exact = None
        prob_bnb = make_general_d_dag(d=d, m=d, K=K, eps=0.03, seed=505 + 10 * d + K)

    if mname == "indep_student_os":
        tape_os = IntrinsicGaussianTape(prob_bnb.true_query_means, prob_bnb.sigma, seed=seed)
        r_os = run_indep_heteroscedastic_os(prob_bnb, tape_os, delta=delta, max_samples=100_000)
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
    cfg_map: dict[str, tuple[HeteroscedasticDAGProblem, dict[str, Any]]] = {
        "cold_bnb_certified": (prob_bnb, dict(warm_start_cuts=False, fast_qp_screen=False, predictable_gate=False)),
        "warm_bnb_certified": (prob_bnb, dict(warm_start_cuts=True, fast_qp_screen=False, predictable_gate=False)),
        "hybrid_qp_screened": (prob_bnb, dict(warm_start_cuts=True, fast_qp_screen=True, predictable_gate=False)),
        "hybrid_qp_gated": (prob_bnb, dict(warm_start_cuts=True, fast_qp_screen=True, predictable_gate=True)),
    }
    if prob_exact is not None:
        cfg_map["exact_cubic_v23"] = (prob_exact, dict(warm_start_cuts=True, fast_qp_screen=False, predictable_gate=False))

    pr, kw = cfg_map[mname]
    tape = IntrinsicGaussianTape(pr.true_query_means, pr.sigma, seed=seed)
    r = run_v34_tracker(
        pr,
        tape,
        delta=delta,
        method_name=mname,
        refresh_schedule="four_power",
        action_local=True,
        design_tol_scale=dtol,
        null_log_tol=zeta,
        max_samples=100_000,
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
    runs_path = out_dir / "v9_exp4_runs.jsonl"
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
            "mean_root_qp_frac": round(float(np.mean([r["root_qp_frac"] for r in grp])), 4),
            "med_design_ms": round(float(np.median([r["design_ms"] for r in grp])), 2),
            "med_null_ms": round(float(np.median([r["null_ms"] for r in grp])), 2),
            "med_total_ms": round(float(np.median([r["total_ms"] for r in grp])), 2),
            "med_ms_per_null": round(float(np.median([r["ms_per_null"] for r in grp])), 3),
        })

    csv_path = out_dir / "v9_exp4_summary.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)

    be_rows: list[dict[str, Any]] = []
    os_map = {(r["d"], r["K"]): r for r in summary_rows if r["method"] == "indep_student_os"}
    for r in summary_rows:
        if abs(r["zeta"] - 0.1) > 1e-9 or r["method"] == "indep_student_os":
            continue
        r_os = os_map.get((r["d"], r["K"]))
        if r_os is None:
            continue
        saved_evals = float(r_os["med_samples"]) - float(r["med_samples"])
        extra_ms = float(r["med_total_ms"]) - float(r_os["med_total_ms"])
        ceval_star = max(0.0, extra_ms / saved_evals) if saved_evals > 0 else float("inf")
        be_rows.append({
            "d": r["d"],
            "K": r["K"],
            "method": r["method"],
            "os_med_samples": r_os["med_samples"],
            "v34_med_samples": r["med_samples"],
            "sample_speedup_vs_os": round(float(r_os["med_samples"]) / max(1.0, float(r["med_samples"])), 2),
            "v34_solver_ms": r["med_total_ms"],
            "os_solver_ms": r_os["med_total_ms"],
            "breakeven_ceval_ms": round(ceval_star, 4) if math.isfinite(ceval_star) else "inf",
        })
    be_csv = out_dir / "v9_exp4_breakeven.csv"
    with be_csv.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(be_rows[0].keys()))
        w.writeheader()
        w.writerows(be_rows)

    print(f"Wrote {csv_path} ({len(summary_rows)} rows) and {be_csv} ({len(be_rows)} rows).")
    print("\n=== Highlight: Solver Cost of Validity (K=16) ===")
    for r in summary_rows:
        if r["K"] == 16 and r["method"] != "indep_student_os":
            print(
                f"  d={r['d']} zeta={r['zeta']:<6g} {r['method']:20s} N={r['med_samples']:6.1f} "
                f"nodes={r['med_bnb_nodes']:7.1f} qp_scr={100*r['mean_root_qp_frac']:5.1f}% tot_ms={r['med_total_ms']:8.1f}"
            )
    print("\n=== Break-Even vs. Indep. Student OS (zeta=0.1) ===")
    for b in be_rows:
        print(
            f"  d={b['d']} K={b['K']:2d} {b['method']:20s} OS/V34={b['os_med_samples']:.0f}/{b['v34_med_samples']:.0f} "
            f"({b['sample_speedup_vs_os']:.2f}x) solver={b['v34_solver_ms']:8.1f}ms c_eval*={b['breakeven_ceval_ms']} ms"
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
    jobs: list[tuple[int, int, float, int, str]] = []
    if args.smoke:
        spec = [(2, [4], [1.0, 0.1], 2), (4, [4], [1.0, 0.1], 2)]
    else:
        spec = [
            (2, [4, 16], [1.0, 0.1, 1e-3, 1e-5], 16),
            (4, [4, 16], [1.0, 0.1, 1e-3, 1e-5], 16),
            (6, [4, 16], [1.0, 0.1, 1e-3, 1e-5], 8),
        ]

    for d, ks, zetas, n_seeds in spec:
        meths = ["cold_bnb_certified", "warm_bnb_certified", "hybrid_qp_screened", "hybrid_qp_gated"]
        if d == 2:
            meths.append("exact_cubic_v23")
        for K in ks:
            for z in zetas:
                for i in range(n_seeds):
                    seed = 99000 + i
                    for mname in meths:
                        jobs.append((d, K, z, seed, mname))
                    if abs(z - 0.1) < 1e-9:
                        jobs.append((d, K, z, seed, "indep_student_os"))

    # Schedule heaviest jobs first (d=6 first) for optimal load balancing across 24 cores!
    jobs.sort(key=lambda j: (-j[0], -j[1], j[2], j[4]))
    print(f"Launching V9-4: {len(jobs)} fine-grained tasks across {args.workers} workers...", flush=True)

    all_rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(_run_single_method_job, j) for j in jobs]
        done = 0
        total = len(futs)
        for fut in as_completed(futs):
            all_rows.append(fut.result())
            done += 1
            if done % max(1, total // 16) == 0 or done == total:
                print(f"  progress: {done}/{total} tasks ({time.perf_counter()-t0:.1f}s)", flush=True)

    all_rows.sort(key=lambda r: (r["d"], r["K"], r["zeta"], r["seed"], r["method"]))
    (out_dir / "v9_exp4_runs.jsonl").write_text("\n".join(json.dumps(r) for r in all_rows) + "\n", encoding="utf-8")

    summarize(out_dir)
    wall = time.perf_counter() - t0
    manifest_files = {}
    for fname in ("v9_exp4_runs.jsonl", "v9_exp4_summary.csv", "v9_exp4_breakeven.csv"):
        fp = out_dir / fname
        manifest_files[fname] = {"bytes": fp.stat().st_size, "sha256": _sha256(fp)}
    manifest = {
        "suite": "v9_exp4_solver_cost_of_validity",
        "smoke": bool(args.smoke),
        "total_rows": len(all_rows),
        "wall_s": round(wall, 2),
        "files": manifest_files,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Completed V9-4 in {wall:.1f}s ({len(all_rows)} runs). Manifest written.")


if __name__ == "__main__":
    main()
