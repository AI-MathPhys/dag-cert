#!/usr/bin/env python3
"""Experiment V9-2 (P0): Unknown Heteroscedastic Variance Information Efficiency.

Validates the genuinely new statistical regime of V33/V34: unknown heterogeneous Gaussian
query variances sigma_x in {0.25, 0.5, 1.0, 2.0, 4.0}.
  - Part A (Variance Spread Sweep at delta=0.05, 60 paired seeds/profile):
      Compares V34-Full (vanilla), V34-Gated (Prop. V32.1), Oracle Known-Sigma Tracker,
      Fixed-Nominal-Sigma (sigma=1) CD-Joint, and Independent Heteroscedastic Student-t OS
      across 6 variance regimes from (0.25, 0.25) to (0.25, 4.0), (4.0, 0.25), and (4.0, 4.0).
  - Part B (Asymptotic delta-Sweep & Empirical Cor. V34.1 Discovery Constant D_s):
      Sweeps delta in {0.10, 0.05, 0.01, 1e-3, 1e-5, 1e-8} on heteroscedastic rank-2 DAGs
      (60 seeds/cell) and delta in {0.10, 0.05, 0.01, 1e-3, 1e-5} on the d=3, m=4
      heteroscedastic proxy DAG sigma=(2.0, 2.0, 2.0, 0.35) (32 seeds/cell).
      Computes exact unknown-variance nuisance-KL limit C_*(theta, sigma) AND known-sigma
      limit I_*(theta, sigma), reporting E[tau_delta] / ((1/C_*) log(1/delta)) and fitting
      the empirical slope and discovery intercept D_hat of Cor. V34.1.
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
    HeteroscedasticDAGProblem,
    IntrinsicGaussianTape,
    compute_exact_nuisance_kl_rate,
    make_heteroscedastic_proxy_dag,
    make_rank2_multi_action_dag,
    run_indep_heteroscedastic_os,
    run_known_sigma_info_tracker,
    run_v34_tracker,
)


ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = ROOT / "results/bayesian_ucd_v1/v9_exp2_heteroscedastic_info"

SIGMA_PROFILES: dict[str, tuple[float, float]] = {
    "low_homosced_025_025": (0.25, 0.25),
    "mod_het_050_200": (0.50, 2.00),
    "balanced_100_100": (1.00, 1.00),
    "ext_het_fav_025_400": (0.25, 4.00),
    "ext_het_adv_400_025": (4.00, 0.25),
    "high_homosced_400_400": (4.00, 4.00),
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _compute_known_sigma_rate(prob: HeteroscedasticDAGProblem) -> float:
    """Compute exact known-sigma Gaussian information limit I_*(theta_*, sigma) via dense/FW."""
    from scipy.optimize import minimize

    H = prob.H
    U = H / prob.sigma[:, None]
    m, d = H.shape
    best_rate = 0.0
    for a in range(prob.K):
        comps = prob.components[a]
        if not comps:
            return math.inf
        # Check if theta_star is invalid for a
        if not prob.is_eps_optimal(a):
            continue
        sup = list(prob.supports[a])
        phi_S = prob.phi[sup]

        def rate_at_w(w: np.ndarray) -> float:
            M_w = U.T @ (w[:, None] * U) + 1e-10 * np.eye(d)
            M_inv = np.linalg.inv(M_w)
            min_d = math.inf
            for comp in comps:
                g_rows = prob.phi[comp.terminal][None, :] - phi_S
                rhs = prob.eps - g_rows @ prob.theta_star
                if float(np.max(rhs)) <= 0.0:
                    return 0.0
                if len(sup) == 1:
                    v0 = max(0.0, float(rhs[0]))
                    dist = 0.5 * v0 * v0 / float(g_rows[0] @ (M_inv @ g_rows[0]))
                else:
                    Gram = g_rows @ (M_inv @ g_rows.T)
                    q_d = np.zeros(len(sup))
                    dg = np.maximum(np.diag(Gram), 1e-14)
                    for _ in range(80):
                        q_d = np.maximum(0.0, q_d + (rhs - Gram @ q_d) / dg)
                    dist = max(0.0, float(q_d @ rhs - 0.5 * q_d @ (Gram @ q_d)))
                min_d = min(min_d, dist)
            return min_d

        if m == 2:
            for w1 in np.linspace(1e-4, 1.0 - 1e-4, 201):
                best_rate = max(best_rate, rate_at_w(np.array([w1, 1.0 - w1])))
        else:
            # Multi-start Frank-Wolfe over Delta_m
            w = np.full(m, 1.0 / m)
            for it in range(120):
                val = rate_at_w(w)
                best_rate = max(best_rate, val)
                # Finite-difference coordinate ascent on concave I_a(w)
                grads = np.zeros(m)
                eps_fd = 1e-4
                for x in range(m):
                    wp = w * (1.0 - eps_fd)
                    wp[x] += eps_fd
                    grads[x] = (rate_at_w(wp) - val) / eps_fd
                x_best = int(np.argmax(grads))
                step = 2.0 / (it + 4.0)
                w = (1.0 - step) * w
                w[x_best] += step
    return float(best_rate)


def _build_problem(profile_name: str) -> HeteroscedasticDAGProblem:
    if profile_name == "proxy_d3_m4_het":
        return make_heteroscedastic_proxy_dag([2.0, 2.0, 2.0, 0.35], eps=0.0)
    sig = SIGMA_PROFILES[profile_name]
    return make_rank2_multi_action_dag(
        K=4, multi_answer=False, sigma=sig, theta_star=(0.70, 0.45), eps=0.02, seed=303
    )


def _run_part_a_job(job: tuple[str, float, float, float, int]) -> list[dict[str, Any]]:
    profile_name, delta, c_star, i_star, seed = job
    prob = _build_problem(profile_name)
    rows: list[dict[str, Any]] = []

    methods = [
        ("v34_vanilla", lambda tp: run_v34_tracker(prob, tp, delta=delta, method_name="v34_vanilla", predictable_gate=False, null_log_tol=1e-4, max_samples=250_000)),
        ("v34_gated", lambda tp: run_v34_tracker(prob, tp, delta=delta, method_name="v34_gated", predictable_gate=True, null_log_tol=1e-4, max_samples=250_000)),
        ("known_sigma_tracker", lambda tp: run_known_sigma_info_tracker(prob, tp, delta=delta, method_name="known_sigma_tracker", max_samples=250_000)),
        ("cd_joint_nom_sig1", lambda tp: run_known_sigma_info_tracker(prob, tp, delta=delta, assumed_sigma=np.ones(prob.m), use_cd_joint=True, method_name="cd_joint_nom_sig1", max_samples=250_000)),
        ("indep_student_os", lambda tp: run_indep_heteroscedastic_os(prob, tp, delta=delta, method_name="indep_student_os", max_samples=250_000)),
    ]
    t_star_unknown = 1.0 / max(c_star, 1e-12)
    denom = t_star_unknown * math.log(1.0 / delta)

    for mname, fn in methods:
        tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)
        r = fn(tape)
        rows.append({
            "part": "A_spread",
            "profile": profile_name,
            "sigma": list(prob.sigma),
            "delta": delta,
            "seed": seed,
            "method": mname,
            "c_star_unknown": round(c_star, 6),
            "i_star_known": round(i_star, 6),
            "certified": r.certified,
            "is_correct": r.is_correct,
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "norm_ratio_unknown": round(r.total_samples / denom, 4),
            "design_calls": r.design_calls,
            "null_calls": r.null_calls,
            "total_ms": round(r.total_wall_s * 1e3, 2),
        })
    return rows


def _run_part_b_job(job: tuple[str, float, float, float, int]) -> list[dict[str, Any]]:
    profile_name, delta, c_star, i_star, seed = job
    prob = _build_problem(profile_name)
    is_proxy = profile_name == "proxy_d3_m4_het"
    ntol = 0.5 if is_proxy else 1e-4
    max_s = 600_000 if delta <= 1e-5 else 300_000
    rows: list[dict[str, Any]] = []

    methods = [
        ("v34_vanilla", lambda tp: run_v34_tracker(prob, tp, delta=delta, method_name="v34_vanilla", predictable_gate=False, fast_qp_screen=is_proxy, null_log_tol=ntol, max_samples=max_s, max_batches=500)),
        ("v34_gated", lambda tp: run_v34_tracker(prob, tp, delta=delta, method_name="v34_gated", predictable_gate=True, fast_qp_screen=is_proxy, null_log_tol=ntol, max_samples=max_s, max_batches=500)),
        ("known_sigma_tracker", lambda tp: run_known_sigma_info_tracker(prob, tp, delta=delta, method_name="known_sigma_tracker", max_samples=max_s)),
        ("indep_student_os", lambda tp: run_indep_heteroscedastic_os(prob, tp, delta=delta, method_name="indep_student_os", max_samples=max_s)),
    ]
    t_star_unknown = 1.0 / max(c_star, 1e-12)
    denom = t_star_unknown * math.log(1.0 / delta)

    for mname, fn in methods:
        tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)
        r = fn(tape)
        rows.append({
            "part": "B_delta_sweep",
            "profile": profile_name,
            "sigma": list(prob.sigma),
            "delta": delta,
            "seed": seed,
            "method": mname,
            "c_star_unknown": round(c_star, 6),
            "i_star_known": round(i_star, 6),
            "certified": r.certified,
            "is_correct": r.is_correct,
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "norm_ratio_unknown": round(r.total_samples / denom, 4),
            "design_calls": r.design_calls,
            "null_calls": r.null_calls,
            "total_ms": round(r.total_wall_s * 1e3, 2),
        })
    return rows


def _build_sym_compass_problem(sig: tuple[float, float]) -> HeteroscedasticDAGProblem:
    """Symmetric equal-radius overlapping 4-action compass DAG (0 containments, equal norms).

    Eliminates asymmetric-norm luck so fixed-nominal-sigma overconfidence at sigma=4 is exposed cleanly.
    """
    H = np.eye(2, dtype=float)
    angs = np.linspace(0.0, 2.0 * math.pi, 8, endpoint=False)
    phi = np.column_stack([np.cos(angs), np.sin(angs)])
    # Adjacent overlapping supports of size 3 sharing boundary vertices (0 containments!)
    # theta_* = (0.90, 0.90) points dead-center at z1=(0.707,0.707) (mean 1.273) while
    # shared boundary terminals z0=(1,0), z2=(0,1) have mean 0.900 => clean 0.373 margin!
    supports = ((0, 1, 2), (2, 3, 4), (4, 5, 6), (6, 7, 0))
    return HeteroscedasticDAGProblem(
        name=f"sym_compass_{sig[0]:g}_{sig[1]:g}",
        H=H,
        phi=phi,
        supports=supports,
        theta_star=np.array([0.90, 0.90], dtype=float),
        sigma=np.asarray(sig, dtype=float),
        eps=0.02,
    )


def _run_part_c_job(job: tuple[str, tuple[float, float], float, int]) -> list[dict[str, Any]]:
    prof_name, sig, delta, seed = job
    prob = _build_sym_compass_problem(sig)
    rows: list[dict[str, Any]] = []
    methods = [
        ("v34_vanilla", lambda tp: run_v34_tracker(prob, tp, delta=delta, method_name="v34_vanilla", predictable_gate=False, null_log_tol=1e-4, max_samples=250_000)),
        ("known_sigma_tracker", lambda tp: run_known_sigma_info_tracker(prob, tp, delta=delta, method_name="known_sigma_tracker", max_samples=250_000)),
        ("cd_joint_nom_sig1", lambda tp: run_known_sigma_info_tracker(prob, tp, delta=delta, assumed_sigma=np.ones(2), use_cd_joint=True, method_name="cd_joint_nom_sig1", max_samples=250_000)),
        ("indep_student_os", lambda tp: run_indep_heteroscedastic_os(prob, tp, delta=delta, method_name="indep_student_os", max_samples=250_000)),
    ]
    for mname, fn in methods:
        tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)
        r = fn(tape)
        rows.append({
            "part": "C_sym_compass",
            "profile": prof_name,
            "sigma": list(sig),
            "delta": delta,
            "seed": seed,
            "method": mname,
            "certified": r.certified,
            "is_correct": r.is_correct,
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "total_ms": round(r.total_wall_s * 1e3, 2),
        })
    return rows


def summarize(out_dir: Path) -> None:
    runs_path = out_dir / "v9_exp2_runs.jsonl"
    rows = [json.loads(line) for line in runs_path.read_text(encoding="utf-8").splitlines() if line.strip()]

    groups: dict[tuple[Any, ...], list[dict[str, Any]]] = defaultdict(list)
    for r in rows:
        groups[(r["part"], r["profile"], r["delta"], r["method"])].append(r)

    summary_rows: list[dict[str, Any]] = []
    for (part, prof, delta, meth), grp in sorted(groups.items()):
        n = len(grp)
        certs = [r for r in grp if r["certified"]]
        false_certs = sum(1 for r in certs if not r["is_correct"])
        samps = [r["total_samples"] for r in grp]
        ratios = [r["norm_ratio_unknown"] for r in grp]
        summary_rows.append({
            "part": part,
            "profile": prof,
            "delta": delta,
            "log_inv_delta": round(math.log(1.0 / delta), 4),
            "method": meth,
            "runs": n,
            "cert_rate": round(len(certs) / n, 4),
            "false_certs": false_certs,
            "false_cert_rate": round(false_certs / n, 4),
            "c_star_unknown": grp[0]["c_star_unknown"],
            "i_star_known": grp[0]["i_star_known"],
            "med_samples": round(float(np.median(samps)), 1),
            "mean_samples": round(float(np.mean(samps)), 1),
            "mean_norm_ratio_unknown": round(float(np.mean(ratios)), 4),
            "med_norm_ratio_unknown": round(float(np.median(ratios)), 4),
            "med_total_ms": round(float(np.median([r["total_ms"] for r in grp])), 2),
        })

    csv_path = out_dir / "v9_exp2_summary.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)

    # Fit Cor. V34.1 linear regression: E[tau_delta] ~ D_hat + slope_hat * log(1/delta)
    fit_rows: list[dict[str, Any]] = []
    b_groups: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for r in summary_rows:
        if r["part"] == "B_delta_sweep":
            b_groups[(r["profile"], r["method"])].append(r)
    for (prof, meth), pts in sorted(b_groups.items()):
        pts.sort(key=lambda z: z["log_inv_delta"])
        xs = np.array([z["log_inv_delta"] for z in pts], dtype=float)
        ys = np.array([z["mean_samples"] for z in pts], dtype=float)
        if len(xs) >= 2:
            slope, intercept = np.polyfit(xs, ys, 1)
            c_star = float(pts[0]["c_star_unknown"])
            t_star = 1.0 / max(c_star, 1e-12)
            fit_rows.append({
                "profile": prof,
                "method": meth,
                "c_star_unknown": c_star,
                "theoretical_slope_1_over_Cstar": round(t_star, 2),
                "empirical_slope": round(float(slope), 2),
                "slope_ratio_to_limit": round(float(slope / t_star), 3),
                "empirical_discovery_intercept_D": round(float(intercept), 1),
                "ratio_at_smallest_delta": pts[-1]["mean_norm_ratio_unknown"],
                "smallest_delta": pts[-1]["delta"],
            })
    fit_csv = out_dir / "v9_exp2_discovery_slope_fit.csv"
    if fit_rows:
        with fit_csv.open("w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(fit_rows[0].keys()))
            w.writeheader()
            w.writerows(fit_rows)

    print(f"Wrote {csv_path} ({len(summary_rows)} rows) and {fit_csv} ({len(fit_rows)} rows).")
    print("\n=== Part A: Variance Spread Sweep (delta=0.05) ===")
    for r in summary_rows:
        if r["part"] == "A_spread":
            print(
                f"  {r['profile']:22s} {r['method']:20s} cert={r['cert_rate']:.2f} err={r['false_certs']:2d}/{r['runs']} "
                f"mean_N={r['mean_samples']:8.1f} ratio={r['mean_norm_ratio_unknown']:6.2f}"
            )
    print("\n=== Part B: Cor. V34.1 Empirical Slope & Discovery Intercept ===")
    for fr in fit_rows:
        print(
            f"  {fr['profile']:20s} {fr['method']:20s} 1/C*={fr['theoretical_slope_1_over_Cstar']:6.1f} "
            f"emp_slope={fr['empirical_slope']:6.1f} ({fr['slope_ratio_to_limit']:.2f}x) "
            f"D_hat={fr['empirical_discovery_intercept_D']:7.1f} ratio@{fr['smallest_delta']}={fr['ratio_at_smallest_delta']:.2f}"
        )

    partc_path = out_dir / "v9_exp2_partC_runs.jsonl"
    if partc_path.exists():
        c_rows = [json.loads(l) for l in partc_path.read_text(encoding="utf-8").splitlines() if l.strip()]
        cg: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
        for r in c_rows:
            cg[(r["profile"], r["method"])].append(r)
        c_sum: list[dict[str, Any]] = []
        for (prof, meth), grp in sorted(cg.items()):
            n = len(grp)
            certs = [r for r in grp if r["certified"]]
            errs = sum(1 for r in certs if not r["is_correct"])
            c_sum.append({
                "profile": prof,
                "method": meth,
                "runs": n,
                "cert_rate": round(len(certs) / n, 4),
                "false_certs": errs,
                "false_cert_rate": round(errs / n, 4),
                "med_samples": round(float(np.median([r["total_samples"] for r in grp])), 1),
                "mean_samples": round(float(np.mean([r["total_samples"] for r in grp])), 1),
            })
        c_csv = out_dir / "v9_exp2_partC_summary.csv"
        with c_csv.open("w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(c_sum[0].keys()))
            w.writeheader()
            w.writerows(c_sum)
        print("\n=== Part C: Symmetric Overlapping Compass Nominal-Sigma Stress Test (delta=0.05) ===")
        for r in c_sum:
            print(
                f"  {r['profile']:18s} {r['method']:20s} cert={r['cert_rate']:.2f} "
                f"err={r['false_certs']:2d}/{r['runs']} ({100*r['false_cert_rate']:4.1f}%) mean_N={r['mean_samples']:8.1f}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=OUT_DIR)
    ap.add_argument("--workers", type=int, default=min(24, os.cpu_count() or 8))
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--part-c-only", action="store_true")
    args = ap.parse_args()

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    c_profiles = [
        ("sig_025_025", (0.25, 0.25)),
        ("sig_050_200", (0.50, 2.00)),
        ("sig_025_400", (0.25, 4.00)),
        ("sig_400_400", (4.00, 4.00)),
    ]
    if args.part_c_only:
        seeds_c = [95500 + i for i in range(60)]
        jobs_c = [(pname, sig, 0.05, s) for pname, sig in c_profiles for s in seeds_c]
        c_rows: list[dict[str, Any]] = []
        with ProcessPoolExecutor(max_workers=args.workers) as ex:
            for fut in as_completed([ex.submit(_run_part_c_job, j) for j in jobs_c]):
                c_rows.extend(fut.result())
        c_rows.sort(key=lambda r: (r["profile"], r["seed"], r["method"]))
        (out_dir / "v9_exp2_partC_runs.jsonl").write_text("\n".join(json.dumps(r) for r in c_rows) + "\n", encoding="utf-8")
        summarize(out_dir)
        # Update manifest with all files
        mpath = out_dir / "manifest.json"
        man = json.loads(mpath.read_text(encoding="utf-8")) if mpath.exists() else {"suite": "v9_exp2_heteroscedastic_info", "smoke": False}
        files_map = man.get("files", {})
        for fname in ("v9_exp2_runs.jsonl", "v9_exp2_summary.csv", "v9_exp2_discovery_slope_fit.csv", "v9_exp2_limits.json", "v9_exp2_partC_runs.jsonl", "v9_exp2_partC_summary.csv"):
            fp = out_dir / fname
            if fp.exists():
                files_map[fname] = {"bytes": fp.stat().st_size, "sha256": _sha256(fp)}
        man["files"] = files_map
        mpath.write_text(json.dumps(man, indent=2) + "\n", encoding="utf-8")
        print(f"Completed V9-2 Part C in {time.perf_counter()-t0:.1f}s. Manifest updated.")
        return
    # Precompute exact unknown-variance C_*(theta, sigma) & known-variance I_*(theta, sigma) once per profile!
    all_profiles = list(SIGMA_PROFILES.keys()) + ["proxy_d3_m4_het"]
    limits: dict[str, tuple[float, float]] = {}
    for pname in all_profiles:
        prob = _build_problem(pname)
        tol_c = 1e-3 if pname == "proxy_d3_m4_het" else 1e-5
        c_star, _, _ = compute_exact_nuisance_kl_rate(prob, tol=tol_c)
        i_star = _compute_known_sigma_rate(prob)
        limits[pname] = (c_star, i_star)
        print(f"  Profile {pname:22s}: C*_unknown={c_star:.5f} (1/C*={1/c_star:6.1f}), I*_known={i_star:.5f} (1/I*={1/i_star:6.1f})", flush=True)

    (out_dir / "v9_exp2_limits.json").write_text(
        json.dumps({k: {"c_star_unknown": v[0], "i_star_known": v[1]} for k, v in limits.items()}, indent=2) + "\n",
        encoding="utf-8",
    )

    if args.smoke:
        seeds_a = [93001, 93002, 93003]
        deltas_r2 = [0.05, 0.01]
        seeds_r2 = [94001, 94002, 94003]
        deltas_px = [0.05]
        seeds_px = [95001, 95002]
        profs_b_r2 = ["ext_het_fav_025_400"]
    else:
        seeds_a = [93000 + i for i in range(60)]
        deltas_r2 = [0.10, 0.05, 0.01, 1e-3, 1e-5, 1e-8]
        seeds_r2 = [94000 + i for i in range(60)]
        deltas_px = [0.10, 0.05, 0.01, 1e-3, 1e-5]
        seeds_px = [95000 + i for i in range(24)]
        profs_b_r2 = ["ext_het_fav_025_400", "mod_het_050_200"]

    jobs_a = [(p, 0.05, limits[p][0], limits[p][1], s) for p in SIGMA_PROFILES for s in seeds_a]
    jobs_b = (
        [(p, d, limits[p][0], limits[p][1], s) for p in profs_b_r2 for d in deltas_r2 for s in seeds_r2]
        + [("proxy_d3_m4_het", d, limits["proxy_d3_m4_het"][0], limits["proxy_d3_m4_het"][1], s) for d in deltas_px for s in seeds_px]
    )
    print(f"Launching V9-2: {len(jobs_a)} Part-A jobs + {len(jobs_b)} Part-B jobs across {args.workers} workers...")

    all_rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(_run_part_a_job, j) for j in jobs_a] + [ex.submit(_run_part_b_job, j) for j in jobs_b]
        done = 0
        total = len(futs)
        for fut in as_completed(futs):
            all_rows.extend(fut.result())
            done += 1
            if done % max(1, total // 10) == 0 or done == total:
                print(f"  progress: {done}/{total} jobs ({time.perf_counter()-t0:.1f}s)", flush=True)

    all_rows.sort(key=lambda r: (r["part"], r["profile"], r["delta"], r["seed"], r["method"]))
    runs_path = out_dir / "v9_exp2_runs.jsonl"
    with runs_path.open("w", encoding="utf-8") as fh:
        for r in all_rows:
            fh.write(json.dumps(r) + "\n")

    # Also execute Part C in standard full/smoke runs
    seeds_c = [95500 + i for i in range(3 if args.smoke else 60)]
    jobs_c = [(pname, sig, 0.05, s) for pname, sig in c_profiles for s in seeds_c]
    c_rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        for fut in as_completed([ex.submit(_run_part_c_job, j) for j in jobs_c]):
            c_rows.extend(fut.result())
    c_rows.sort(key=lambda r: (r["profile"], r["seed"], r["method"]))
    (out_dir / "v9_exp2_partC_runs.jsonl").write_text("\n".join(json.dumps(r) for r in c_rows) + "\n", encoding="utf-8")

    summarize(out_dir)
    wall = time.perf_counter() - t0
    manifest_files = {}
    for fname in ("v9_exp2_runs.jsonl", "v9_exp2_summary.csv", "v9_exp2_discovery_slope_fit.csv", "v9_exp2_limits.json", "v9_exp2_partC_runs.jsonl", "v9_exp2_partC_summary.csv"):
        fp = out_dir / fname
        if fp.exists():
            manifest_files[fname] = {"bytes": fp.stat().st_size, "sha256": _sha256(fp)}
    manifest = {
        "suite": "v9_exp2_heteroscedastic_info",
        "smoke": bool(args.smoke),
        "total_rows": len(all_rows),
        "wall_s": round(wall, 2),
        "files": manifest_files,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Completed V9-2 in {wall:.1f}s ({len(all_rows)} runs). Manifest written.")


if __name__ == "__main__":
    main()
