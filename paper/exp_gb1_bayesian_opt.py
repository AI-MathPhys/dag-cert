"""Experiment 14 (ICML v6 Bayesian Optimization): GP-Guided Acquisitions vs.
Exact-Regret Witness Allocation on Measured GB1 Combinatorial Protein Landscapes.

Evaluates the two cleanly separated Bayesian-optimization (BO) questions on the
ten 4-site GB1 protein-design campaigns (`panel5`, `eps=0.010`, `delta=0.05`, `45k` cap):

1. Part 1 (`bo_acquisition_runs.jsonl` -> `summary_bo_acquisitions.csv`, `summary_bo_by_regime.csv`):
   Holds the anytime-valid `NestedIntervals` (`emp_bernstein`) terminal confidence box and
   exact outside-support root stopping criterion `min_{a in A} R_t(a) <= eps` IDENTICAL
   across all methods, isolating acquisition efficiency (420 runs = 10 templates x 6 seeds x 7 methods):
   - `exact_dag_lucb`: Independent estimates + exact UCB/outside witnesses
   - `opt_sep`: Independent estimates + exterior-margin witnesses
   - `flat_lucb_root`: Independent estimates + flat terminal LUCB witnesses
   - `gp_ucb`: GP surrogate + highest posterior UCB
   - `gp_ei`: GP surrogate + Expected Improvement
   - `gp_ts`: GP surrogate + exact joint posterior Thompson sampling
   - `gp_root_info`: GP surrogate + root-certificate witness contraction
   Records BOTH sequence discovery (`tau_discover_seq`, `best_queried_raw_fitness`) and
   formal root-commitment certification (`certified`, `capped_steps`, `gp_time_ms`, `total_ms`).

2. Part 2 (`gp_bounds_runs.jsonl` -> `summary_gp_bounds.csv`):
   Separate probe replacing independent terminal bounds with GP-derived simultaneous
   rectangular confidence intervals (`nominal_gp` vs. frequentist `rkhs_calibrated` per
   Chowdhury & Gopalan 2017) across 160 runs (10 templates x 4 seeds x 4 configurations),
   auditing both sample savings and empirical false-certificate rates under real 4-site epistasis.
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
import random
import statistics
import time

import numpy as np

from dag_mcts.v5_hybrid_and_os import HybridWitnessDAGLUCBSession
from dag_mcts.v6_bayesian_opt import (
    DiscreteGPSurrogate,
    GPBoxCertSession,
    GPGuidedRootCertSession,
    protein_sequence_kernel,
)
from dag_mcts.v6_real_world import (
    FlatLUCBSession,
    GB1MutationCampaignProblem,
    gb1_mean_to_raw_fitness,
    real_world_problem_diagnostics,
)
from paper.exp_real_world_applications import GB1_SEEDS, GB1_TEMPLATES


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/uct_v4_icml_baselines/exp14_gb1_bayesian_opt"

ACQ_METHODS = (
    "exact_dag_lucb",
    "opt_sep",
    "flat_lucb_root",
    "gp_ucb",
    "gp_ei",
    "gp_ts",
    "gp_root_info",
)

GP_BOX_CONFIGS = (
    ("nominal_gp", "gp_ucb"),
    ("nominal_gp", "gp_root_info"),
    ("rkhs_calibrated", "gp_ucb"),
    ("rkhs_calibrated", "gp_root_info"),
)

DELTA = 0.05
EPS = 0.010
SCHEDULE = "emp_bernstein"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    if hasattr(sess, "evidence"):
        return sess.evidence.conflict
    return getattr(sess, "conflict", False)


def make_acq_session(prob: GB1MutationCampaignProblem, eps: float, seed: int, method: str, kernel: np.ndarray):
    if method == "exact_dag_lucb":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="ucb", delta=DELTA, schedule=SCHEDULE)
    if method == "opt_sep":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=DELTA, schedule=SCHEDULE)
    if method == "flat_lucb_root":
        return FlatLUCBSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE, stop_rule="root_exact")
    if method in ("gp_ucb", "gp_ei", "gp_ts", "gp_root_info"):
        return GPGuidedRootCertSession(
            prob, seed, eps, acquisition=method, delta=DELTA, schedule=SCHEDULE, kernel=kernel
        )
    raise ValueError(f"Unknown acquisition method: {method}")


def run_acq_one(
    prob: GB1MutationCampaignProblem,
    eps: float,
    seed: int,
    method: str,
    kernel: np.ndarray,
    wall_limit: float,
    cap: int,
) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(values[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(values[c])) for c in root_ch]

    t0 = time.perf_counter()
    sess = make_acq_session(prob, eps, seed, method, kernel)

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
        if discover_step < 0 and mu_l >= opt_mu - eps - 1e-12:
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
    gp_s = float(sess.gp.gp_time_s) if hasattr(sess, "gp") else 0.0
    del sess
    total_s = time.perf_counter() - t0

    sel_val = float(values[root_ch[act]])
    true_reg = regrets[act]
    false_cert = bool(cert and true_reg > eps + 1e-12)
    assert not false_cert, f"False certificate in {method} on {prob.name}: {true_reg} > {eps}"

    return {
        "problem": prob.name,
        "method": method,
        "seed": seed,
        "eps": eps,
        "certified": cert,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "tau_discover_seq": discover_step if discover_step > 0 else cap,
        "discovered_eps_seq": discover_step > 0,
        "cap": cap,
        "total_s": round(total_s, 6),
        "gp_time_s": round(gp_s, 6),
        "action_idx": act,
        "action_label": prob.action_labels[act],
        "selected_raw_fitness": round(gb1_mean_to_raw_fitness(sel_val), 4),
        "best_queried_raw_fitness": round(gb1_mean_to_raw_fitness(best_queried_mu), 4),
        "opt_raw_fitness": round(gb1_mean_to_raw_fitness(opt_mu), 4),
        "final_simple_regret": round(true_reg, 6),
    }


def run_gp_box_one(
    prob: GB1MutationCampaignProblem,
    eps: float,
    seed: int,
    beta_mode: str,
    acquisition: str,
    kernel: np.ndarray,
    rkhs_norm: float,
    wall_limit: float,
    cap: int,
) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(values[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(values[c])) for c in root_ch]

    t0 = time.perf_counter()
    # Bounded [0, 1] payoffs satisfy 0.5-sub-Gaussianity identically via Hoeffding's lemma
    sess = GPBoxCertSession(
        prob,
        seed,
        eps,
        acquisition=acquisition,
        beta_mode=beta_mode,
        rkhs_bound=rkhs_norm,
        subgaussian_r=0.5,
        delta=DELTA,
        kernel=kernel,
    )
    elapsed = time.perf_counter() - t0
    while (
        not sess.certified
        and not sess.conflict
        and sess.calls < cap
        and elapsed < wall_limit
    ):
        sess.step()
        elapsed = time.perf_counter() - t0

    cert = bool(sess.certified)
    conflict = bool(sess.conflict)
    act = int(sess.action)
    calls = int(sess.calls)
    info_gain = float(sess.gp.info_gain)
    gp_s = float(sess.gp.gp_time_s)
    del sess
    total_s = time.perf_counter() - t0

    sel_val = float(values[root_ch[act]])
    true_reg = regrets[act]
    false_cert = bool(cert and true_reg > eps + 1e-12)
    if beta_mode == "rkhs_calibrated":
        assert not false_cert, f"False certificate in RKHS-calibrated GP box on {prob.name}: {true_reg}"

    return {
        "problem": prob.name,
        "beta_mode": beta_mode,
        "acquisition": acquisition,
        "config": f"{beta_mode}__{acquisition}",
        "seed": seed,
        "eps": eps,
        "rkhs_norm": round(rkhs_norm, 4),
        "certified": cert,
        "conflict": conflict,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "cap": cap,
        "info_gain": round(info_gain, 4),
        "total_s": round(total_s, 6),
        "gp_time_s": round(gp_s, 6),
        "selected_raw_fitness": round(gb1_mean_to_raw_fitness(sel_val), 4),
        "final_simple_regret": round(true_reg, 6),
    }


def summarize(dest: Path) -> None:
    acq_runs = [json.loads(x) for x in (dest / "bo_acquisition_runs.jsonl").read_text().splitlines() if x.strip()]
    box_runs = [json.loads(x) for x in (dest / "gp_bounds_runs.jsonl").read_text().splitlines() if x.strip()]

    # 1. Overall & regime-stratified Level-1 BO acquisition comparison
    acq_rows = []
    for stratum in ("all", "epistatic_ridge", "single_peak"):
        for m in ACQ_METHODS:
            sub = [
                r for r in acq_runs
                if r["method"] == m and (stratum == "all" or r["regime"] == stratum)
            ]
            if not sub:
                continue
            acq_rows.append({
                "stratum": stratum,
                "method": m,
                "runs": len(sub),
                "discover_rate": round(sum(1 for r in sub if r["discovered_eps_seq"]) / len(sub), 4),
                "median_discover_steps": round(statistics.median(r["tau_discover_seq"] for r in sub), 1),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_gp_ms": round(1e3 * statistics.median(r["gp_time_s"] for r in sub), 2),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 2),
                "mean_best_queried_fitness": round(statistics.fmean(r["best_queried_raw_fitness"] for r in sub), 4),
                "mean_certified_action_fitness": round(statistics.fmean(r["selected_raw_fitness"] for r in sub), 4),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })
    with (dest / "summary_bo_acquisitions.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(acq_rows[0].keys()))
        w.writeheader()
        w.writerows(acq_rows)

    # 2. Per-template breakdown for Level-1 BO vs Exact-Regret witnesses
    tmpl_rows = []
    for tmpl in sorted({r["start_seq"] for r in acq_runs}):
        sub_t = [r for r in acq_runs if r["start_seq"] == tmpl]
        r0 = sub_t[0]
        row = {
            "start_seq": tmpl,
            "regime": r0["regime"],
            "gamma_over_flat": r0["gamma_over_flat"],
        }
        for m in ACQ_METHODS:
            sm = [r for r in sub_t if r["method"] == m]
            row[f"{m}_disc_med"] = round(statistics.median(r["tau_discover_seq"] for r in sm), 1)
            row[f"{m}_cert_med"] = round(statistics.median(r["capped_steps"] for r in sm), 1)
            row[f"{m}_cert_rate"] = round(sum(1 for r in sm if r["certified"]) / len(sm), 4)
        tmpl_rows.append(row)
    tmpl_rows.sort(key=lambda r: (r["gamma_over_flat"], r["start_seq"]))
    with (dest / "summary_bo_by_template.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(tmpl_rows[0].keys()))
        w.writeheader()
        w.writerows(tmpl_rows)

    # 3. Level-2 GP simultaneous confidence box summary
    box_rows = []
    for stratum in ("all", "epistatic_ridge", "single_peak"):
        for bm, acq in GP_BOX_CONFIGS:
            cfg = f"{bm}__{acq}"
            sub = [
                r for r in box_runs
                if r["config"] == cfg and (stratum == "all" or r["regime"] == stratum)
            ]
            if not sub:
                continue
            box_rows.append({
                "stratum": stratum,
                "beta_mode": bm,
                "acquisition": acq,
                "runs": len(sub),
                "mean_rkhs_norm": round(statistics.fmean(r["rkhs_norm"] for r in sub), 3),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "conflict_rate": round(sum(1 for r in sub if r["conflict"]) / len(sub), 4),
                "false_cert_rate": round(sum(1 for r in sub if r["false_certificate"]) / len(sub), 4),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 2),
            })
    with (dest / "summary_gp_bounds.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(box_rows[0].keys()))
        w.writeheader()
        w.writerows(box_rows)


def _run_template_job(
    job: tuple[int, str, tuple[int, ...], tuple[int, ...], int, float, float]
) -> tuple[list[dict], list[dict]]:
    t_idx, tmpl, seeds_acq, seeds_box, cap, wall_acq, wall_box = job
    rng = random.Random(2026111809 + 97 * t_idx)
    prob = GB1MutationCampaignProblem(start_seq=tmpl, max_edits=3, panel="panel5", noise_model="calibrated")
    diag = real_world_problem_diagnostics(prob)
    gof = round(float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"])), 3)
    regime = "epistatic_ridge" if gof >= 10.0 else "single_peak"

    seqs = [prob.variant_of_leaf[z] for z in prob.graph.leaves]
    kernel = protein_sequence_kernel(seqs)
    true_f = np.array([prob.means[z] for z in prob.graph.leaves], dtype=np.float64)
    rkhs_norm = DiscreteGPSurrogate(kernel).rkhs_norm(true_f)

    t_acq: list[dict] = []
    t_box: list[dict] = []

    for s in seeds_acq:
        order = list(ACQ_METHODS)
        rng.shuffle(order)
        for m in order:
            rec = run_acq_one(prob, EPS, s, m, kernel, wall_limit=wall_acq, cap=cap)
            rec.update({
                "start_seq": tmpl,
                "regime": regime,
                "gamma_over_flat": gof,
            })
            t_acq.append(rec)

    for s in seeds_box:
        b_order = list(GP_BOX_CONFIGS)
        rng.shuffle(b_order)
        for bm, acq in b_order:
            rec = run_gp_box_one(
                prob, EPS, s, bm, acq, kernel, rkhs_norm, wall_limit=wall_box, cap=cap
            )
            rec.update({
                "start_seq": tmpl,
                "regime": regime,
                "gamma_over_flat": gof,
            })
            t_box.append(rec)

    print(f"  [exp14] Completed template {tmpl} ({len(t_acq) + len(t_box)} runs)", flush=True)
    return t_acq, t_box


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

    tmpls = ("VDGV", "FDGV") if args.smoke else GB1_TEMPLATES
    seeds_acq = GB1_SEEDS[:1] if args.smoke else GB1_SEEDS
    seeds_box = GB1_SEEDS[:1] if args.smoke else GB1_SEEDS[:4]
    cap = 22000 if args.smoke else 45000
    wall_acq = 5.0 if args.smoke else 12.0
    wall_box = 5.0 if args.smoke else 12.0

    jobs = [
        (i, tmpl, seeds_acq, seeds_box, cap, wall_acq, wall_box)
        for i, tmpl in enumerate(tmpls)
    ]

    acq_rows: list[dict] = []
    box_rows: list[dict] = []
    with ProcessPoolExecutor(max_workers=min(10, len(jobs)), mp_context=mp.get_context("spawn")) as pool:
        for t_acq, t_box in pool.map(_run_template_job, jobs):
            acq_rows.extend(t_acq)
            box_rows.extend(t_box)

    acq_rows.sort(key=lambda r: (GB1_TEMPLATES.index(r["start_seq"]), r["seed"], ACQ_METHODS.index(r["method"])))
    box_rows.sort(key=lambda r: (GB1_TEMPLATES.index(r["start_seq"]), r["seed"], GP_BOX_CONFIGS.index((r["beta_mode"], r["acquisition"]))))

    acq_path = dest / "bo_acquisition_runs.jsonl"
    box_path = dest / "gp_bounds_runs.jsonl"
    acq_path.write_text("\n".join(json.dumps(r) for r in acq_rows) + "\n")
    box_path.write_text("\n".join(json.dumps(r) for r in box_rows) + "\n")

    summarize(dest)

    manifest = {
        "suite": "exp14_gb1_bayesian_opt",
        "smoke": bool(args.smoke),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "delta": DELTA,
        "eps": EPS,
        "schedule": SCHEDULE,
        "bo_acquisition_runs": len(acq_rows),
        "gp_bounds_runs": len(box_rows),
        "total_runs": len(acq_rows) + len(box_rows),
        "sha256_bo_acquisitions": digest(acq_path),
        "sha256_gp_bounds": digest(box_path),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Saved {manifest['total_runs']} GB1 Bayesian Optimization runs to {dest}!")


if __name__ == "__main__":
    main()
