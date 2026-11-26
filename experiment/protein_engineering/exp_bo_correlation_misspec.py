"""Experiment 15 (ICML v6 Correlation & Kernel Misspecification):
1. Controlled 1D & 2D (within-support `rho_in` vs. cross-support `rho_out`) GP correlation
   sweep comparing independent `Exact-Regret-DAG-LUCB` and `Optimistic-Separation`,
   surrogate-guided `GP-Root-Info` (valid frequentist `NestedIntervals`), the frequentist
   Abbasi-Yadkori RKHS Enclosing Rectangular GP Box `B(C_t)`, and the Exact Ellipsoidal
   GP Certificate `R_t^{C}(a)` (plus nominal posterior GP counterparts).
2. GB1 4-kernel misspecification sensitivity ablation (`structured`, `hamming`,
   `oversmooth`, `scrambled_desc`) across all 10 GB1 campaigns x 6 seeds (`480` runs),
   verifying 0% false certificates under arbitrary kernel misspecification while
   quantifying discovery and certification efficiency degradation.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from concurrent.futures import ProcessPoolExecutor
import csv
import gc
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import platform
import statistics
import time

import numpy as np

from joint_root_cert import HybridWitnessDAGLUCBSession
from joint_root_cert._core.v6_bayesian_opt import (
    CorrelatedSupportDAGProblem,
    GPEllipsoidCertSession,
    GPGuidedRootCertSession,
    alt_protein_sequence_kernel,
)
from joint_root_cert.benchmarks import (
    GB1MutationCampaignProblem,
    gb1_mean_to_raw_fitness,
    real_world_problem_diagnostics,
)
from experiment.protein_engineering.exp_real_world_applications import GB1_SEEDS, GB1_TEMPLATES


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v4_icml_baselines/exp15_bo_correlation_and_misspec"

CORR_1D_LEVELS = (0.00, 0.25, 0.50, 0.75, 0.90)
CORR_2D_LEVELS = (0.00, 0.45, 0.90)

CORR_1D_METHODS = (
    "exact_dag_lucb",
    "opt_sep",
    "gp_root_freq",
    "rkhs_box",
    "rkhs_ellipsoid",
    "nominal_box",
    "nominal_ellipsoid",
)
CORR_2D_METHODS = (
    "opt_sep",
    "gp_root_freq",
    "rkhs_box",
    "rkhs_ellipsoid",
)
KERNEL_MODES = ("structured", "hamming", "oversmooth", "scrambled_desc")
MISSPEC_METHODS = ("gp_root_info", "gp_ucb")

DELTA = 0.05
CORR_EPS = 0.025
CORR_CAP = 16000
GB1_EPS = 0.010
GB1_CAP = 45000


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    return getattr(sess, "conflict", False)


def _run_corr_method(prob: CorrelatedSupportDAGProblem, eps: float, seed: int, method: str, cap: int) -> dict:
    gc.collect()
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    t0 = time.perf_counter()
    if method == "exact_dag_lucb":
        sess = HybridWitnessDAGLUCBSession(prob, seed, eps, mode="ucb", delta=DELTA, schedule="emp_bernstein")
    elif method == "opt_sep":
        sess = HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=DELTA, schedule="emp_bernstein")
    elif method == "gp_root_freq":
        sess = GPGuidedRootCertSession(
            prob, seed, eps, acquisition="gp_root_info", delta=DELTA, schedule="emp_bernstein",
            kernel=prob.kernel, prior_mean=prob.prior_mean, obs_std=prob.obs_std,
        )
    elif method == "rkhs_box":
        sess = GPEllipsoidCertSession(
            prob, seed, eps, kernel=prob.kernel, prior_mean=prob.prior_mean,
            obs_std=prob.obs_std, rkhs_bound=prob.rkhs_bound, mode="box", beta_mode="rkhs_exact", delta=DELTA,
        )
    elif method == "rkhs_ellipsoid":
        sess = GPEllipsoidCertSession(
            prob, seed, eps, kernel=prob.kernel, prior_mean=prob.prior_mean,
            obs_std=prob.obs_std, rkhs_bound=prob.rkhs_bound, mode="ellipsoid", beta_mode="rkhs_exact", delta=DELTA,
        )
    elif method == "nominal_box":
        sess = GPEllipsoidCertSession(
            prob, seed, eps, kernel=prob.kernel, prior_mean=prob.prior_mean,
            obs_std=prob.obs_std, rkhs_bound=prob.rkhs_bound, mode="box", beta_mode="nominal_gp", delta=DELTA,
        )
    elif method == "nominal_ellipsoid":
        sess = GPEllipsoidCertSession(
            prob, seed, eps, kernel=prob.kernel, prior_mean=prob.prior_mean,
            obs_std=prob.obs_std, rkhs_bound=prob.rkhs_bound, mode="ellipsoid", beta_mode="nominal_gp", delta=DELTA,
        )
    else:
        raise ValueError(f"Unknown correlation method: {method}")

    discover_step = -1
    call_idx = 0
    orig_sample = sess.oracle.sample

    def _tracked_sample(leaf: int) -> float:
        nonlocal discover_step, call_idx
        call_idx += 1
        if discover_step < 0 and float(prob.means[leaf]) >= opt_mu - eps - 1e-12:
            discover_step = call_idx
        return orig_sample(leaf)

    sess.oracle.sample = _tracked_sample

    while not sess.certified and not _has_conflict(sess) and sess.calls < cap:
        sess.step()

    cert = bool(sess.certified)
    act = int(sess.action)
    calls = int(sess.calls)
    gp_s = float(sess.gp.gp_time_s) if hasattr(sess, "gp") else 0.0
    max_gap = float(getattr(sess, "max_duality_gap", 0.0))
    del sess
    total_s = time.perf_counter() - t0

    true_reg = regrets[act]
    false_cert = bool(cert and true_reg > eps + 1e-12)
    if not method.startswith("nominal_"):
        assert not false_cert, f"False certificate in {method} on {prob.name}: {true_reg} > {eps}"

    return {
        "problem": prob.name,
        "rho_in": round(prob.rho_in, 2),
        "rho_out": round(prob.rho_out, 2),
        "inst_seed": seed,
        "method": method,
        "eps": eps,
        "true_rkhs_norm": round(prob.true_rkhs_norm, 4),
        "certified": cert,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "tau_discover_seq": discover_step if discover_step > 0 else cap,
        "discovered_eps_seq": discover_step > 0,
        "cap": cap,
        "max_duality_gap": round(max_gap, 9),
        "gp_time_s": round(gp_s, 6),
        "total_s": round(total_s, 6),
        "final_simple_regret": round(true_reg, 6),
    }


def _corr_1d_worker(task: tuple[float, int, int]) -> list[dict]:
    rho, inst_idx, cap = task
    prob = CorrelatedSupportDAGProblem(seed=inst_idx + 1, rho_in=rho, rho_out=rho)
    oracle_seed = 9100 + inst_idx
    return [_run_corr_method(prob, CORR_EPS, oracle_seed, m, cap) for m in CORR_1D_METHODS]


def _corr_2d_worker(task: tuple[float, float, int, int]) -> list[dict]:
    rho_in, rho_out, inst_idx, cap = task
    prob = CorrelatedSupportDAGProblem(seed=inst_idx + 1, rho_in=rho_in, rho_out=rho_out)
    oracle_seed = 9300 + inst_idx
    return [_run_corr_method(prob, CORR_EPS, oracle_seed, m, cap) for m in CORR_2D_METHODS]


def _gb1_misspec_worker(task: tuple[str, int, float, int]) -> list[dict]:
    start_seq, seed, wall_limit, cap = task
    prob = GB1MutationCampaignProblem(start_seq=start_seq, max_edits=3, panel="panel5")
    diag = real_world_problem_diagnostics(prob)
    gamma = float(diag["exterior_margin_gamma"])
    flat_gap = float(diag["flat_top2_gap"])
    ratio = gamma / max(1e-6, flat_gap)
    regime = "epistatic_ridge" if ratio >= 10.0 else "single_peak"
    seqs = [prob.variant_of_leaf[z] for z in prob.graph.leaves]

    values = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(values[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(values[c])) for c in root_ch]

    rows: list[dict] = []
    for k_mode in KERNEL_MODES:
        k_mat = alt_protein_sequence_kernel(seqs, mode=k_mode)
        for acq in MISSPEC_METHODS:
            gc.collect()
            t0 = time.perf_counter()
            sess = GPGuidedRootCertSession(
                prob, seed, GB1_EPS, acquisition=acq, delta=DELTA, schedule="emp_bernstein", kernel=k_mat
            )
            discover_step = -1
            best_queried_mu = 0.0
            call_idx = 0
            orig_sample = sess.oracle.sample

            def _tracked_sample(leaf: int) -> float:
                nonlocal discover_step, best_queried_mu, call_idx
                call_idx += 1
                mu_l = float(prob.means[leaf])
                if mu_l > best_queried_mu:
                    best_queried_mu = mu_l
                if discover_step < 0 and mu_l >= opt_mu - GB1_EPS - 1e-12:
                    discover_step = call_idx
                return orig_sample(leaf)

            sess.oracle.sample = _tracked_sample

            elapsed = time.perf_counter() - t0
            while (
                not sess.certified
                and not _has_conflict(sess)
                and sess.calls < cap
                and elapsed < wall_limit
            ):
                sess.step()
                elapsed = time.perf_counter() - t0

            cert = bool(sess.certified)
            act = int(sess.action)
            calls = int(sess.calls)
            gp_s = float(sess.gp.gp_time_s)
            del sess
            total_s = time.perf_counter() - t0

            sel_val = float(values[root_ch[act]])
            true_reg = regrets[act]
            false_cert = bool(cert and true_reg > GB1_EPS + 1e-12)
            assert not false_cert, f"False certificate under {k_mode}/{acq} on {start_seq}: {true_reg}"

            rows.append({
                "problem": prob.name,
                "start_seq": start_seq,
                "regime": regime,
                "gamma_over_flat": round(ratio, 3),
                "kernel_mode": k_mode,
                "method": acq,
                "seed": seed,
                "eps": GB1_EPS,
                "certified": cert,
                "false_certificate": false_cert,
                "steps": calls,
                "capped_steps": calls if cert else cap,
                "tau_discover_seq": discover_step if discover_step > 0 else cap,
                "discovered_eps_seq": discover_step > 0,
                "cap": cap,
                "gp_time_s": round(gp_s, 6),
                "total_s": round(total_s, 6),
                "selected_raw_fitness": round(gb1_mean_to_raw_fitness(sel_val), 4),
                "best_queried_raw_fitness": round(gb1_mean_to_raw_fitness(best_queried_mu), 4),
                "final_simple_regret": round(true_reg, 6),
            })
    return rows


def summarize(dest: Path) -> None:
    c1_runs = [json.loads(x) for x in (dest / "corr_1d_runs.jsonl").read_text().splitlines() if x.strip()]
    c2_runs = [json.loads(x) for x in (dest / "corr_2d_phase_runs.jsonl").read_text().splitlines() if x.strip()]
    ms_runs = [json.loads(x) for x in (dest / "gb1_misspec_runs.jsonl").read_text().splitlines() if x.strip()]

    # 1. 1D correlation summary
    c1_rows = []
    for rho in CORR_1D_LEVELS:
        for m in CORR_1D_METHODS:
            sub = [r for r in c1_runs if abs(r["rho_in"] - rho) < 1e-6 and r["method"] == m]
            if not sub:
                continue
            st = np.array([float(r["capped_steps"]) for r in sub])
            disc = np.array([float(r["tau_discover_seq"]) for r in sub])
            c1_rows.append({
                "rho": round(rho, 2),
                "method": m,
                "runs": len(sub),
                "mean_rkhs_norm": round(statistics.fmean(r["true_rkhs_norm"] for r in sub), 3),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                "median_discover_steps": round(float(np.median(disc)), 1),
                "median_capped_steps": round(float(np.median(st)), 1),
                "q25_capped_steps": round(float(np.percentile(st, 25)), 1),
                "q75_capped_steps": round(float(np.percentile(st, 75)), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 2),
                "max_duality_gap": max(r["max_duality_gap"] for r in sub),
            })
    with (dest / "summary_corr_1d.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(c1_rows[0].keys()))
        w.writeheader()
        w.writerows(c1_rows)

    # 2. 2D correlation phase summary
    c2_rows = []
    for rin in CORR_2D_LEVELS:
        for rout in CORR_2D_LEVELS:
            sub_cell = [
                r for r in c2_runs
                if abs(r["rho_in"] - rin) < 1e-6 and abs(r["rho_out"] - rout) < 1e-6
            ]
            if not sub_cell:
                continue
            os_med = float(np.median([r["capped_steps"] for r in sub_cell if r["method"] == "opt_sep"]))
            for m in CORR_2D_METHODS:
                sub = [r for r in sub_cell if r["method"] == m]
                st = np.array([float(r["capped_steps"]) for r in sub])
                disc = np.array([float(r["tau_discover_seq"]) for r in sub])
                med_s = float(np.median(st))
                c2_rows.append({
                    "rho_in": round(rin, 2),
                    "rho_out": round(rout, 2),
                    "method": m,
                    "runs": len(sub),
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                    "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                    "median_discover_steps": round(float(np.median(disc)), 1),
                    "median_capped_steps": round(med_s, 1),
                    "ratio_vs_opt_sep": round(med_s / max(1.0, os_med), 4),
                })
    with (dest / "summary_corr_2d_phase.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(c2_rows[0].keys()))
        w.writeheader()
        w.writerows(c2_rows)

    # 3. GB1 kernel misspecification summary
    ms_rows = []
    for stratum in ("all", "epistatic_ridge", "single_peak"):
        for acq in MISSPEC_METHODS:
            for k_mode in KERNEL_MODES:
                sub = [
                    r for r in ms_runs
                    if r["method"] == acq
                    and r["kernel_mode"] == k_mode
                    and (stratum == "all" or r["regime"] == stratum)
                ]
                if not sub:
                    continue
                disc = np.array([float(r["tau_discover_seq"]) for r in sub])
                st = np.array([float(r["capped_steps"]) for r in sub])
                ms_rows.append({
                    "stratum": stratum,
                    "method": acq,
                    "kernel_mode": k_mode,
                    "runs": len(sub),
                    "discover_rate": round(sum(1 for r in sub if r["discovered_eps_seq"]) / len(sub), 4),
                    "median_discover_steps": round(float(np.median(disc)), 1),
                    "q25_discover_steps": round(float(np.percentile(disc, 25)), 1),
                    "q75_discover_steps": round(float(np.percentile(disc, 75)), 1),
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                    "median_capped_steps": round(float(np.median(st)), 1),
                    "q25_capped_steps": round(float(np.percentile(st, 25)), 1),
                    "q75_capped_steps": round(float(np.percentile(st, 75)), 1),
                    "median_gp_ms": round(1e3 * statistics.median(r["gp_time_s"] for r in sub), 2),
                    "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 2),
                    "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                })
    with (dest / "summary_gb1_misspec.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(ms_rows[0].keys()))
        w.writeheader()
        w.writerows(ms_rows)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=14)
    args = ap.parse_args()

    dest = args.out
    dest.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(dest)
        return

    n_1d = 2 if args.smoke else 16
    n_2d = 2 if args.smoke else 12
    gb1_tmpls = GB1_TEMPLATES[:2] if args.smoke else GB1_TEMPLATES
    gb1_seeds = GB1_SEEDS[:1] if args.smoke else GB1_SEEDS
    corr_cap = 4000 if args.smoke else CORR_CAP
    gb1_cap = 8000 if args.smoke else GB1_CAP
    wall_lim = 2.0 if args.smoke else 12.0

    ctx = mp.get_context("spawn")
    t_start = time.perf_counter()

    c1_tasks = [(rho, idx, corr_cap) for rho in CORR_1D_LEVELS for idx in range(n_1d)]
    c2_tasks = [
        (rin, rout, idx, corr_cap)
        for rin in CORR_2D_LEVELS
        for rout in CORR_2D_LEVELS
        for idx in range(n_2d)
    ]
    ms_tasks = [(tmpl, seed, wall_lim, gb1_cap) for tmpl in gb1_tmpls for seed in gb1_seeds]

    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        c1_nested = list(ex.map(_corr_1d_worker, c1_tasks))
        c2_nested = list(ex.map(_corr_2d_worker, c2_tasks))
        ms_nested = list(ex.map(_gb1_misspec_worker, ms_tasks))

    c1_all = [r for grp in c1_nested for r in grp]
    c2_all = [r for grp in c2_nested for r in grp]
    ms_all = [r for grp in ms_nested for r in grp]

    f_c1 = dest / "corr_1d_runs.jsonl"
    f_c2 = dest / "corr_2d_phase_runs.jsonl"
    f_ms = dest / "gb1_misspec_runs.jsonl"
    f_c1.write_text("\n".join(json.dumps(r) for r in c1_all) + "\n")
    f_c2.write_text("\n".join(json.dumps(r) for r in c2_all) + "\n")
    f_ms.write_text("\n".join(json.dumps(r) for r in ms_all) + "\n")

    summarize(dest)

    manifest = {
        "suite": "exp15_bo_correlation_and_misspec",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "corr_1d_runs": len(c1_all),
        "corr_2d_runs": len(c2_all),
        "gb1_misspec_runs": len(ms_all),
        "sha256_corr_1d": digest(f_c1),
        "sha256_corr_2d": digest(f_c2),
        "sha256_gb1_misspec": digest(f_ms),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Completed exp15 in {manifest['elapsed_s']:.2f}s ({len(c1_all) + len(c2_all) + len(ms_all)} runs).")


if __name__ == "__main__":
    main()
