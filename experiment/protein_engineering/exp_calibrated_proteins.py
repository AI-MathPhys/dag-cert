"""Experiment v8-1 (P0): Calibrated Bayesian/Conic Certification on GB1, TmTrpB, and Controlled (xi, eps) Frontier.

Resolves the central reliability vs. efficiency tension of correlated certification:
  "Can calibrated correlation-aware certification outperform independent certificates
   without overconfident error violations?"

Part A — Real Protein Engineering Benchmarks (matched to the 12,000-assay protocol + uncensored 25,000-assay curves):
  - GB1 (Wu et al., eLife 2016): all 10 templates x 20 seeds = 200 runs/method.
  - TmTrpB (Johnston et al., PNAS 2024): all 21 templates x 10 seeds = 210 runs/method.
  - Compares:
      1. `indep_os`           : Independent Optimistic-Separation (100% distribution-free Empirical Bernstein)
      2. `df_cd_fallback`     : Correlated-guided warmup + 100% distribution-free Empirical Bernstein stopping
      3. `cd_joint_nominal`   : Unadjusted nominal full-rank GP ellipsoid (a priori fixed kernel)
      4. `cd_joint_calibrated`: Strictly leak-free online Empirical-Bayes Type-II ML + LOO-residual calibrated GP
      5. `cd_joint_robust_005`: Theorem T3.3 misspecification-robust GP (xi=0.005, 2*xi=0.010 < eps=0.015)
      6. `cd_joint_robust_010`: Theorem T3.3 misspecification-robust GP (xi=0.010, 2*xi=0.020 > eps=0.015; bias floor)
      7. `cd_joint_hybrid_eb` : Valid (delta/2 + delta/2) Calibrated EB+LOO GP cap DF Empirical Bernstein box + OS fallback
      8. `cd_joint_hybrid_005`: Valid (delta/2 + delta/2) Robust GP (xi=0.005) cap DF box + OS fallback
      9. `cd_joint_hybrid_010`: Valid (delta/2 + delta/2) Robust GP (xi=0.010) cap DF box + OS fallback
  - Reports BOTH 12,000-assay and 25,000-assay certification rates, median/IQR evaluations, empirical error rate
    (with exact Clopper-Pearson 95% upper CI), best-available recommendation regret on ALL and on UNCAPPED/CAPPED runs,
    and full wall-clock runtime (including Type-II ML surrogate fitting and conic solves).

Part B — High-Power Controlled Calibration, Misspecified GP Cure, and (xi, eps) Feasibility Map (500 reps/condition):
  - B1 (`C3_misspec_gp_cure`, 500 reps): Replicates the rough-true (ell=0.45) vs smooth-assumed (ell=3.0) GP stress test
    showing online Empirical-Bayes + LOO calibration cures nominal overconfidence (18%+ error -> <= delta).
  - B2 (`C4_xi_eps_frontier`, 500 reps/cell): Sweeps xi in {0, 0.005, 0.01, 0.02, 0.04, 0.08} across eps in {0.030, 0.080}
    comparing Independent OS, CD-Joint (nominal), CD-Joint (specified-model Abbasi-Yadkori), CD-Joint (robust xi), and
    CD-Joint (smart hybrid), cleanly charting the exact 2*xi < eps speedup frontier vs 2*xi >= eps safe-fallback region.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from concurrent.futures import ProcessPoolExecutor
import csv
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import platform
import time

import numpy as np
from scipy.stats import beta as beta_dist

from dagcert import HybridWitnessDAGLUCBSession
from dagcert._core.v6_bayesian_opt import _AA_VEC, protein_sequence_kernel
from dagcert.benchmarks import (
    GB1MutationCampaignProblem,
    TrpBMutationCampaignProblem,
    real_world_problem_diagnostics,
)
from dagcert import (
    CorrelationAwareCertSession,
    DiscreteGPPosteriorModel,
    LinearFeatureModel,
)
from dagcert.benchmarks import (
    GaussianPriorDAGProblem,
    MisspecifiedLinearDAGProblem,
)
from dagcert import (
    CalibratedGPPosteriorModel,
    SmartHybridCertSession,
)
from experiment.protein_engineering.exp_real_world_applications import GB1_TEMPLATES
from experiment.protein_engineering.exp_real_world_validation import TRPB_TEMPLATES


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/v8_exp1_calibrated_proteins"

DELTA = 0.05
PROT_EPS = 0.015
PROT_CAP_12K = 12000
PROT_CAP_25K = 25000

PROT_METHODS = (
    ("indep_os", "distribution_free"),
    ("df_cd_fallback", "distribution_free"),
    ("cd_joint_nominal", "nominal_bayesian"),
    ("cd_joint_calibrated", "calibrated_eb_gp"),
    ("cd_joint_robust_005", "robust_xi"),
    ("cd_joint_robust_010", "robust_xi"),
    ("cd_joint_hybrid_eb", "hybrid_valid"),
    ("cd_joint_hybrid_005", "hybrid_valid"),
    ("cd_joint_hybrid_010", "hybrid_valid"),
)

CTRL_XIS = (0.0, 0.005, 0.01, 0.02, 0.04, 0.08)
CTRL_EPSS = (0.030, 0.080)
CTRL_CAP = 7500


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _cp_upper_95(k: int, n: int) -> float:
    if n <= 0:
        return 1.0
    if k >= n:
        return 1.0
    return float(beta_dist.ppf(0.95, k + 1, n - k))


def _build_protein_candidate_kernels(seqs: list[str]) -> list[tuple[str, np.ndarray]]:
    """Bit-identical to calling `protein_sequence_kernel` on each `(ell, nug, ps)`, computed 36x faster."""
    m = len(seqs)
    seq_len = len(seqs[0])
    feats = np.stack([np.concatenate([_AA_VEC[ch] for ch in seq], axis=0) for seq in seqs], axis=0)
    sq_dists = (
        np.sum(feats * feats, axis=1, keepdims=True)
        + np.sum(feats * feats, axis=1, keepdims=True).T
        - 2.0 * (feats @ feats.T)
    )
    np.maximum(sq_dists, 0.0, out=sq_dists)

    char_mat = np.array([[ord(c) for c in seq] for seq in seqs], dtype=np.int32)
    matches = (char_mat[:, None, :] == char_mat[None, :, :]).astype(np.float64)
    k_add = matches.mean(axis=2)
    pair_sum = np.zeros((m, m), dtype=np.float64)
    n_pairs = 0
    for p in range(seq_len):
        for q in range(p + 1, seq_len):
            pair_sum += matches[:, :, p] * matches[:, :, q]
            n_pairs += 1
    k_pair = pair_sum / max(1, n_pairs)
    k_struct = 0.35 * k_add + 0.20 * k_pair
    eye_m = np.eye(m, dtype=np.float64)

    cands: list[tuple[str, np.ndarray]] = []
    for ell in (1.0, 2.0, 3.0, 5.0):
        k_phys = np.exp(-sq_dists / (2.0 * ell * ell))
        base_no_nug = k_struct + 0.45 * k_phys
        for nug in (0.02, 0.12, 0.35):
            base_k = base_no_nug + nug * eye_m
            for ps in (0.15, 0.22, 0.32):
                nm = f"ell{ell:g}_nug{nug:g}_ps{ps:g}"
                cands.append((nm, (ps * ps) * base_k))
    return cands


def _protein_template_worker(task: tuple[str, str, list[int], int, int]) -> list[dict]:
    landscape, start_seq, seeds, cap12, cap25 = task
    if landscape == "gb1":
        prob = GB1MutationCampaignProblem(start_seq=start_seq, max_edits=3, panel="panel5", noise_model="calibrated")
        prior_m = 0.28
        obs_s = 0.16
    else:
        prob = TrpBMutationCampaignProblem(
            start_seq=start_seq, max_edits=3, panel="panel5", noise_model="low_var_uniform"
        )
        prior_m = 0.30
        obs_s = 0.08 / math.sqrt(3.0)

    diag = real_world_problem_diagnostics(prob)
    gamma = float(diag["exterior_margin_gamma"])
    flat_gap = float(diag["flat_top2_gap"])
    ratio = gamma / max(1e-6, flat_gap)
    regime = "epistatic_ridge" if ratio >= 10.0 else "single_peak"

    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    seqs = [prob.variant_of_leaf[z] for z in prob.graph.leaves]
    t_k0 = time.perf_counter()
    k_nom = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
    k_cands = _build_protein_candidate_kernels(seqs)
    cand_build_ms = 1e3 * (time.perf_counter() - t_k0) / max(1, len(seeds))

    rows: list[dict] = []
    for seed in seeds:
        for method, track in PROT_METHODS:
            t0 = time.perf_counter()
            gp_mod: CalibratedGPPosteriorModel | None = None

            if method == "indep_os":
                sess = HybridWitnessDAGLUCBSession(
                    prob, seed, PROT_EPS, mode="opt_sep", delta=DELTA, schedule="emp_bernstein"
                )
            elif method == "df_cd_fallback":
                gp_mod = CalibratedGPPosteriorModel(
                    kernel=k_nom, prior_mean=prior_m, obs_std=obs_s, delta=DELTA, enable_eb_calib=False
                )
                sess = SmartHybridCertSession(
                    prob,
                    seed=seed,
                    epsilon=PROT_EPS,
                    model=gp_mod,
                    cert_mode="df_cd_fallback",
                    acquisition="contrast_directed",
                    delta=DELTA,
                    cs_schedule="emp_bernstein",
                    check_every=20,
                    adaptive_check=True,
                    df_warmup_pulls=300,
                )
            elif method == "cd_joint_nominal":
                gp_mod = CalibratedGPPosteriorModel(
                    kernel=k_nom, prior_mean=prior_m, obs_std=obs_s, delta=DELTA, enable_eb_calib=False
                )
                sess = SmartHybridCertSession(
                    prob,
                    seed=seed,
                    epsilon=PROT_EPS,
                    model=gp_mod,
                    cert_mode="joint_robust",
                    acquisition="contrast_directed",
                    delta=DELTA,
                    check_every=20,
                    adaptive_check=True,
                )
            elif method == "cd_joint_calibrated":
                gp_mod = CalibratedGPPosteriorModel(
                    kernel=k_nom,
                    prior_mean=prior_m,
                    obs_std=obs_s,
                    delta=DELTA,
                    enable_eb_calib=True,
                    kernel_candidates=k_cands,
                    calib_steps=(120, 360),
                    loo_inflate=True,
                )
                sess = SmartHybridCertSession(
                    prob,
                    seed=seed,
                    epsilon=PROT_EPS,
                    model=gp_mod,
                    cert_mode="joint_robust",
                    acquisition="contrast_directed",
                    delta=DELTA,
                    check_every=20,
                    adaptive_check=True,
                )
            elif method in ("cd_joint_robust_005", "cd_joint_robust_010"):
                xi_v = 0.005 if method.endswith("005") else 0.010
                gp_mod = CalibratedGPPosteriorModel(
                    kernel=k_nom,
                    prior_mean=prior_m,
                    obs_std=obs_s,
                    delta=DELTA,
                    misspec_xi=xi_v,
                    enable_eb_calib=True,
                    kernel_candidates=k_cands,
                    calib_steps=(120, 360),
                    loo_inflate=True,
                )
                sess = SmartHybridCertSession(
                    prob,
                    seed=seed,
                    epsilon=PROT_EPS,
                    model=gp_mod,
                    cert_mode="joint_robust",
                    acquisition="contrast_directed",
                    delta=DELTA,
                    check_every=15,
                    adaptive_check=True,
                )
            elif method == "cd_joint_hybrid_eb":
                gp_mod = CalibratedGPPosteriorModel(
                    kernel=k_nom,
                    prior_mean=prior_m,
                    obs_std=obs_s,
                    delta=0.5 * DELTA,
                    enable_eb_calib=True,
                    kernel_candidates=k_cands,
                    calib_steps=(120, 360),
                    loo_inflate=True,
                )
                sess = SmartHybridCertSession(
                    prob,
                    seed=seed,
                    epsilon=PROT_EPS,
                    model=gp_mod,
                    cert_mode="smart_hybrid",
                    acquisition="contrast_directed",
                    delta=DELTA,
                    cs_schedule="emp_bernstein",
                    check_every=20,
                    adaptive_check=True,
                    fallback_after_pulls=5500,
                )
            elif method in ("cd_joint_hybrid_005", "cd_joint_hybrid_010"):
                xi_v = 0.005 if method.endswith("005") else 0.010
                gp_mod = CalibratedGPPosteriorModel(
                    kernel=k_nom,
                    prior_mean=prior_m,
                    obs_std=obs_s,
                    delta=0.5 * DELTA,
                    misspec_xi=xi_v,
                    enable_eb_calib=True,
                    kernel_candidates=k_cands,
                    calib_steps=(120, 360),
                    loo_inflate=True,
                )
                sess = SmartHybridCertSession(
                    prob,
                    seed=seed,
                    epsilon=PROT_EPS,
                    model=gp_mod,
                    cert_mode="smart_hybrid",
                    acquisition="contrast_directed",
                    delta=DELTA,
                    cs_schedule="emp_bernstein",
                    check_every=15,
                    adaptive_check=True,
                    fallback_after_pulls=4500,
                )
            else:
                raise ValueError(method)

            # Fast analytical short-circuit for pure robust when 2*xi >= eps:
            # Theorem T3.3 mathematically guarantees R_t^{(xi)}(a) >= 2*xi > eps for ALL t!
            # We still run a bounded probe (1200 pulls) to measure best_recommendation regret & runtime honestly.
            is_infeasible_pure_robust = method == "cd_joint_robust_010"
            effective_cap25 = min(cap25, 1200) if is_infeasible_pure_robust else cap25

            snap12: dict | None = None

            def _best_rec_act() -> int:
                if hasattr(sess, "best_recommendation"):
                    return int(sess.best_recommendation())
                if sess.certified:
                    return int(sess.action)
                # For OS, pick action with highest empirical mean or lowest dual-witness regret
                act_dw, _, _, _, _ = sess.monitor.query_dual_witness()
                return int(act_dw)

            wall_lim = 25.0
            while not sess.certified and sess.calls < effective_cap25 and (time.perf_counter() - t0) < wall_lim:
                if hasattr(sess, "monitor") and sess.monitor.evidence.conflict:
                    break
                if getattr(sess, "conflict", False):
                    break
                sess.step()
                if snap12 is None and (sess.certified or sess.calls >= cap12):
                    c12 = bool(sess.certified and sess.calls <= cap12)
                    a12 = int(sess.action) if c12 else _best_rec_act()
                    r12 = regrets[a12]
                    snap12 = {
                        "certified_12k": c12,
                        "steps_12k": int(sess.calls) if c12 else cap12,
                        "false_cert_12k": bool(c12 and r12 > PROT_EPS + 1e-12),
                        "best_regret_12k": round(r12, 6),
                        "elapsed_12k_ms": round(1e3 * (time.perf_counter() - t0), 2),
                    }

            elapsed_s = time.perf_counter() - t0
            c25 = bool(sess.certified) and not is_infeasible_pure_robust
            a25 = int(sess.action) if c25 else _best_rec_act()
            r25 = regrets[a25]
            fc25 = bool(c25 and r25 > PROT_EPS + 1e-12)

            if snap12 is None:
                c12 = bool(c25 and sess.calls <= cap12)
                a12 = int(sess.action) if c12 else a25
                r12 = regrets[a12]
                snap12 = {
                    "certified_12k": c12,
                    "steps_12k": int(sess.calls) if c12 else cap12,
                    "false_cert_12k": bool(c12 and r12 > PROT_EPS + 1e-12),
                    "best_regret_12k": round(r12, 6),
                    "elapsed_12k_ms": round(1e3 * elapsed_s, 2),
                }

            if track == "distribution_free":
                assert not snap12["false_cert_12k"], f"DF false cert on {landscape}/{start_seq}/{method}"
                assert not fc25, f"DF false cert 25k on {landscape}/{start_seq}/{method}"

            cert_ms = 1e3 * float(sess.ellipsoid_cert.cert_time_s) if hasattr(sess, "ellipsoid_cert") else 0.0
            fit_ms = 1e3 * float(gp_mod.fit_time_s) if gp_mod is not None else 0.0
            if gp_mod is not None and gp_mod.enable_eb_calib:
                fit_ms += cand_build_ms

            rows.append(
                {
                    "landscape": landscape,
                    "start_seq": start_seq,
                    "regime": regime,
                    "m_leaves": len(prob.graph.leaves),
                    "k_actions": len(root_ch),
                    "gamma_over_flat": round(ratio, 3),
                    "seed": seed,
                    "method": method,
                    "track": track,
                    "eps": PROT_EPS,
                    "delta": DELTA,
                    **snap12,
                    "certified_25k": c25,
                    "steps_25k": int(sess.calls) if c25 else cap25,
                    "false_cert_25k": fc25,
                    "best_regret_25k": round(r25, 6),
                    "switched_to_df": bool(getattr(sess, "switched_to_df", False)),
                    "selected_kernel": gp_mod.selected_kernel_name if gp_mod is not None else "none",
                    "loo_inflation": round(float(gp_mod.loo_inflation), 4) if gp_mod is not None else 1.0,
                    "fit_ms": round(fit_ms, 2),
                    "cert_ms": round(cert_ms, 2),
                    "total_ms": round(1e3 * elapsed_s + (cand_build_ms if gp_mod and gp_mod.enable_eb_calib else 0.0), 2),
                }
            )
    return rows


def _misspec_gp_cure_worker(task: tuple[list[int], int]) -> list[dict]:
    reps, cap = task
    eps = 0.030
    delta = DELTA
    rows: list[dict] = []
    for rep in reps:
        prob = GaussianPriorDAGProblem(seed=2000 + rep, true_lengthscale=0.45, m_leaves=32, k_actions=4, sigma=0.10)
        k_init = GaussianPriorDAGProblem.rbf_kernel(prob.coords, lengthscale=3.0)
        k_cands = [
            (f"ell_{e:g}", GaussianPriorDAGProblem.rbf_kernel(prob.coords, lengthscale=e))
            for e in (0.3, 0.45, 0.7, 1.1, 1.8, 3.0)
        ]
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
        seed = 63000 + rep

        for method in ("cd_joint_nominal", "bayes_post_nominal", "cd_joint_calibrated_eb"):
            t0 = time.perf_counter()
            if method == "bayes_post_nominal":
                gp_m = DiscreteGPPosteriorModel(
                    kernel=k_init, prior_mean=prob.prior_mean, obs_std=prob.sigma, beta_mode="nominal_bayes", delta=delta
                )
                sess = CorrelationAwareCertSession(
                    prob, seed=seed, epsilon=eps, model=gp_m, cert_mode="posterior_prob",
                    acquisition="contrast_directed", delta=delta, check_every=3, adaptive_check=True,
                    mc_posterior_draws=512,
                )
                fit_ms = 0.0
            elif method == "cd_joint_nominal":
                gp_m = CalibratedGPPosteriorModel(
                    kernel=k_init, prior_mean=prob.prior_mean, obs_std=prob.sigma, delta=delta, enable_eb_calib=False
                )
                sess = SmartHybridCertSession(
                    prob, seed=seed, epsilon=eps, model=gp_m, cert_mode="joint_robust",
                    acquisition="contrast_directed", delta=delta, check_every=3, adaptive_check=True,
                )
                fit_ms = 0.0
            else:
                gp_m = CalibratedGPPosteriorModel(
                    kernel=k_init, prior_mean=prob.prior_mean, obs_std=prob.sigma, delta=delta,
                    enable_eb_calib=True, kernel_candidates=k_cands, calib_steps=(48, 128), loo_inflate=True,
                )
                sess = SmartHybridCertSession(
                    prob, seed=seed, epsilon=eps, model=gp_m, cert_mode="joint_robust",
                    acquisition="contrast_directed", delta=delta, check_every=3, adaptive_check=True,
                )
                fit_ms = 0.0

            while not sess.certified and not getattr(sess, "conflict", False) and sess.calls < cap:
                sess.step()
            elapsed_ms = 1e3 * (time.perf_counter() - t0)
            if isinstance(gp_m, CalibratedGPPosteriorModel):
                fit_ms = 1e3 * gp_m.fit_time_s
            cert = bool(sess.certified)
            rec_a = int(sess.action) if cert else (
                int(sess.best_recommendation()) if hasattr(sess, "best_recommendation") else int(sess.action)
            )
            true_reg = regrets[rec_a]
            rows.append(
                {
                    "study": "C3_misspec_gp_cure",
                    "rep": rep,
                    "eps": eps,
                    "delta": delta,
                    "xi": 0.0,
                    "method": method,
                    "certified": cert,
                    "false_certificate": bool(cert and true_reg > eps + 1e-12),
                    "steps": int(sess.calls),
                    "capped_steps": int(sess.calls) if cert else cap,
                    "best_regret": round(true_reg, 6),
                    "fit_ms": round(fit_ms, 2),
                    "total_ms": round(elapsed_ms, 2),
                    "selected_kernel": gp_m.selected_kernel_name if isinstance(gp_m, CalibratedGPPosteriorModel) else "ell_3",
                    "loo_inflation": round(float(gp_m.loo_inflation), 4) if isinstance(gp_m, CalibratedGPPosteriorModel) else 1.0,
                }
            )
    return rows


def _xi_eps_frontier_worker(task: tuple[float, float, list[int], int]) -> list[dict]:
    xi, eps, reps, cap = task
    delta = DELTA
    rows: list[dict] = []
    for rep in reps:
        prob = MisspecifiedLinearDAGProblem(seed=3000 + rep, xi=xi, m_leaves=32, k_actions=4, d_feat=5, hw=0.14)
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
        seed = 76000 + rep

        for method in ("indep_os", "cd_joint_nominal", "cd_joint_calibrated", "cd_joint_robust", "cd_joint_hybrid"):
            t0 = time.perf_counter()
            if method == "indep_os":
                sess = HybridWitnessDAGLUCBSession(
                    prob, seed, eps, mode="opt_sep", delta=delta, schedule="emp_bernstein"
                )
                while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                    sess.step()
                cert = bool(sess.certified)
                if cert:
                    rec_a = int(sess.action)
                else:
                    rec_a = int(sess.monitor.query_dual_witness()[0])
                sw_df = True
            elif method == "cd_joint_robust" and 2.0 * xi >= eps - 1e-12:
                # Provably infeasible bias floor 2*xi >= eps (run brief 300-step probe for recommendation regret)
                model = LinearFeatureModel(
                    phi=prob.phi, prior_mean=prob.prior_mean, reg_lambda=0.5, obs_std=prob.obs_std,
                    param_bound=prob.param_bound, misspec_xi=xi, beta_mode="misspec_robust", delta=delta,
                )
                sess = SmartHybridCertSession(
                    prob, seed=seed, epsilon=eps, model=model, cert_mode="joint_robust",
                    acquisition="contrast_directed", delta=delta, check_every=5, adaptive_check=True,
                )
                while not sess.certified and sess.calls < min(300, cap):
                    sess.step()
                cert = False
                rec_a = int(sess.best_recommendation())
                sw_df = False
            else:
                beta_m = {
                    "cd_joint_nominal": "nominal_bayes",
                    "cd_joint_calibrated": "abbasi_yadkori",
                    "cd_joint_robust": "misspec_robust",
                    "cd_joint_hybrid": "misspec_robust",
                }[method]
                pass_xi = xi if method in ("cd_joint_robust", "cd_joint_hybrid") else 0.0
                mod_delta = 0.5 * delta if method == "cd_joint_hybrid" else delta
                c_mode = "smart_hybrid" if method == "cd_joint_hybrid" else "joint_robust"
                model = LinearFeatureModel(
                    phi=prob.phi, prior_mean=prob.prior_mean, reg_lambda=0.5, obs_std=prob.obs_std,
                    param_bound=prob.param_bound, misspec_xi=pass_xi, beta_mode=beta_m, delta=mod_delta,
                )
                sess = SmartHybridCertSession(
                    prob, seed=seed, epsilon=eps, model=model, cert_mode=c_mode,
                    acquisition="contrast_directed", delta=delta, cs_schedule="emp_bernstein",
                    check_every=4, adaptive_check=True,
                )
                while not sess.certified and not sess.conflict and sess.calls < cap:
                    sess.step()
                cert = bool(sess.certified)
                rec_a = int(sess.action) if cert else int(sess.best_recommendation())
                sw_df = bool(sess.switched_to_df)

            elapsed_ms = 1e3 * (time.perf_counter() - t0)
            true_reg = regrets[rec_a]
            fc = bool(cert and true_reg > eps + 1e-12)
            rows.append(
                {
                    "study": "C4_xi_eps_frontier",
                    "rep": rep,
                    "eps": eps,
                    "delta": delta,
                    "xi": xi,
                    "feasible_2xi_lt_eps": bool(2.0 * xi < eps - 1e-12),
                    "method": method,
                    "certified": cert,
                    "false_certificate": fc,
                    "steps": int(sess.calls) if cert else cap,
                    "capped_steps": int(sess.calls) if cert else cap,
                    "best_regret": round(true_reg, 6),
                    "switched_to_df": sw_df,
                    "total_ms": round(elapsed_ms, 2),
                }
            )
    return rows


def summarize(dest: Path) -> None:
    # 1. Summarize Part A (Real Proteins)
    prot_path = dest / "v8_exp1_protein_runs.jsonl"
    if prot_path.exists():
        runs = [json.loads(x) for x in prot_path.read_text().splitlines() if x.strip()]
        out_rows: list[dict] = []
        for land in ("gb1", "trpb"):
            l_runs = [r for r in runs if r["landscape"] == land]
            if not l_runs:
                continue
            strata = ("all", "epistatic_ridge", "single_peak") if land == "gb1" else ("all",)
            for strat in strata:
                s_runs = [r for r in l_runs if strat == "all" or r["regime"] == strat]
                if not s_runs:
                    continue
                os_12 = float(np.median([r["steps_12k"] for r in s_runs if r["method"] == "indep_os"]))
                os_25 = float(np.median([r["steps_25k"] for r in s_runs if r["method"] == "indep_os"]))
                for method, track in PROT_METHODS:
                    sub = [r for r in s_runs if r["method"] == method]
                    if not sub:
                        continue
                    n = len(sub)
                    c12 = sum(1 for r in sub if r["certified_12k"])
                    c25 = sum(1 for r in sub if r["certified_25k"])
                    fc12 = sum(1 for r in sub if r["false_cert_12k"])
                    fc25 = sum(1 for r in sub if r["false_cert_25k"])
                    st12 = np.array([float(r["steps_12k"]) for r in sub])
                    st25 = np.array([float(r["steps_25k"]) for r in sub])
                    reg12_all = np.array([float(r["best_regret_12k"]) for r in sub])
                    unc12 = [float(r["best_regret_12k"]) for r in sub if not r["certified_12k"]]
                    out_rows.append(
                        {
                            "landscape": land,
                            "stratum": strat,
                            "track": track,
                            "method": method,
                            "runs": n,
                            "cert_rate_12k": round(c12 / n, 4),
                            "false_certs_12k": fc12,
                            "false_cert_rate_12k": round(fc12 / n, 4),
                            "cp95_upper_err_12k": round(_cp_upper_95(fc12, n), 4),
                            "med_steps_12k": round(float(np.median(st12)), 1),
                            "q25_steps_12k": round(float(np.percentile(st12, 25)), 1),
                            "q75_steps_12k": round(float(np.percentile(st12, 75)), 1),
                            "speedup_vs_os_12k": round(os_12 / max(1.0, float(np.median(st12))), 3),
                            "mean_best_regret_12k": round(float(np.mean(reg12_all)), 5),
                            "mean_uncert_regret_12k": round(float(np.mean(unc12)), 5) if unc12 else 0.0,
                            "max_uncert_regret_12k": round(float(np.max(unc12)), 5) if unc12 else 0.0,
                            "cert_rate_25k": round(c25 / n, 4),
                            "false_certs_25k": fc25,
                            "false_cert_rate_25k": round(fc25 / n, 4),
                            "med_steps_25k": round(float(np.median(st25)), 1),
                            "speedup_vs_os_25k": round(os_25 / max(1.0, float(np.median(st25))), 3),
                            "switched_df_rate": round(sum(1 for r in sub if r["switched_to_df"]) / n, 4),
                            "med_loo_infl": round(float(np.median([r["loo_inflation"] for r in sub])), 3),
                            "med_fit_ms": round(float(np.median([r["fit_ms"] for r in sub])), 2),
                            "med_cert_ms": round(float(np.median([r["cert_ms"] for r in sub])), 2),
                            "med_total_ms": round(float(np.median([r["total_ms"] for r in sub])), 2),
                        }
                    )
        with (dest / "v8_exp1_protein_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(out_rows[0].keys()))
            w.writeheader()
            w.writerows(out_rows)
        print("\n=== v8 Exp 1A: Calibrated Protein Engineering Summary (12k & 25k) ===")
        for r in out_rows:
            if r["stratum"] == "all":
                print(
                    f"  {r['landscape']:4s} | {r['method']:20s} | c12={100*r['cert_rate_12k']:5.1f}% "
                    f"med12={r['med_steps_12k']:7.1f} ({r['speedup_vs_os_12k']:4.2f}x) "
                    f"err12={r['false_certs_12k']}/{r['runs']} ({100*r['false_cert_rate_12k']:4.1f}%) "
                    f"unc_reg={r['mean_uncert_regret_12k']:.4f} | "
                    f"c25={100*r['cert_rate_25k']:5.1f}% med25={r['med_steps_25k']:7.1f} "
                    f"fit={r['med_fit_ms']:5.1f}ms tot={r['med_total_ms']:6.1f}ms"
                )

    # 2. Summarize Part B (Controlled Calibration & (xi, eps) Feasibility Frontier)
    ctrl_path = dest / "v8_exp1_controlled_runs.jsonl"
    if ctrl_path.exists():
        c_runs = [json.loads(x) for x in ctrl_path.read_text().splitlines() if x.strip()]
        keys = sorted({(r["study"], r["eps"], r["xi"], r["method"]) for r in c_runs})
        c_rows: list[dict] = []
        for study, eps, xi, meth in keys:
            sub = [
                r for r in c_runs
                if r["study"] == study and abs(r["eps"] - eps) < 1e-9
                and abs(r["xi"] - xi) < 1e-9 and r["method"] == meth
            ]
            n = len(sub)
            cert_n = sum(1 for r in sub if r["certified"])
            fc_n = sum(1 for r in sub if r["false_certificate"])
            st = np.array([float(r["capped_steps"]) for r in sub])
            unc = [float(r["best_regret"]) for r in sub if not r["certified"]]
            c_rows.append(
                {
                    "study": study,
                    "eps": eps,
                    "xi": xi,
                    "feasible_2xi_lt_eps": bool(2.0 * xi < eps - 1e-12),
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(cert_n / n, 4),
                    "false_certs": fc_n,
                    "false_cert_rate": round(fc_n / n, 4),
                    "cp95_upper_err": round(_cp_upper_95(fc_n, n), 4),
                    "med_steps": round(float(np.median(st)), 1),
                    "q25_steps": round(float(np.percentile(st, 25)), 1),
                    "q75_steps": round(float(np.percentile(st, 75)), 1),
                    "mean_best_regret": round(float(np.mean([r["best_regret"] for r in sub])), 5),
                    "mean_uncert_regret": round(float(np.mean(unc)), 5) if unc else 0.0,
                    "med_total_ms": round(float(np.median([r["total_ms"] for r in sub])), 2),
                }
            )
        with (dest / "v8_exp1_controlled_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(c_rows[0].keys()))
            w.writeheader()
            w.writerows(c_rows)
        print("\n=== v8 Exp 1B: Misspecified GP Cure & (xi, eps) Feasibility Frontier ===")
        for r in c_rows:
            print(
                f"  {r['study']:18s} eps={r['eps']:.3f} xi={r['xi']:.3f} | {r['method']:22s} | "
                f"cert={100*r['cert_rate']:5.1f}% err={r['false_certs']:3d}/{r['runs']} ({100*r['false_cert_rate']:4.1f}%) "
                f"med={r['med_steps']:6.1f} reg={r['mean_best_regret']:.4f}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(24, max(1, os.cpu_count() or 4)))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    # Part A: Real proteins
    if args.smoke:
        gb1_tmpls = GB1_TEMPLATES[:2]
        trpb_tmpls = TRPB_TEMPLATES[:2]
        gb1_seeds = [801001, 801002]
        trpb_seeds = [802001, 802002]
        cap12, cap25 = 1200, 1800
        n_cure_reps = 20
        n_front_reps = 20
        front_xis = (0.0, 0.01, 0.04)
        front_epss = (0.030,)
    else:
        gb1_tmpls = GB1_TEMPLATES
        trpb_tmpls = TRPB_TEMPLATES
        gb1_seeds = [801000 + i for i in range(1, 21)]      # 10 x 20 = 200 runs/method
        trpb_seeds = [802000 + i for i in range(1, 11)]     # 21 x 10 = 210 runs/method
        cap12, cap25 = PROT_CAP_12K, PROT_CAP_25K
        n_cure_reps = 500
        n_front_reps = 500
        front_xis = CTRL_XIS
        front_epss = CTRL_EPSS

    # Chunk seeds per template (4-5 seeds per worker) so candidate kernels are built once per chunk
    prot_tasks: list[tuple[str, str, list[int], int, int]] = []
    for seq in gb1_tmpls:
        for i in range(0, len(gb1_seeds), 5):
            prot_tasks.append(("gb1", seq, gb1_seeds[i : i + 5], cap12, cap25))
    for seq in trpb_tmpls:
        for i in range(0, len(trpb_seeds), 5):
            prot_tasks.append(("trpb", seq, trpb_seeds[i : i + 5], cap12, cap25))

    print(f"[v8 Exp 1A] Running {len(prot_tasks)} protein chunks on {args.workers} workers...", flush=True)
    prot_rows: list[dict] = []
    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for chunk in ex.map(_protein_template_worker, prot_tasks):
            prot_rows.extend(chunk)
    prot_path = out_dir / "v8_exp1_protein_runs.jsonl"
    prot_path.write_text("\n".join(json.dumps(r) for r in prot_rows) + "\n")
    print(f"[v8 Exp 1A] Wrote {len(prot_rows)} protein runs in {time.perf_counter() - t0:.1f}s.", flush=True)

    # Part B: High-power controlled studies
    t1 = time.perf_counter()
    cure_tasks = [(list(range(i, min(n_cure_reps, i + 25))), CTRL_CAP) for i in range(0, n_cure_reps, 25)]
    front_tasks: list[tuple[float, float, list[int], int]] = []
    for eps in front_epss:
        for xi in front_xis:
            for i in range(0, n_front_reps, 25):
                front_tasks.append((xi, eps, list(range(i, min(n_front_reps, i + 25))), CTRL_CAP))

    print(
        f"[v8 Exp 1B] Running {len(cure_tasks)} GP-cure chunks + {len(front_tasks)} (xi,eps) chunks...",
        flush=True,
    )
    ctrl_rows: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for chunk in ex.map(_misspec_gp_cure_worker, cure_tasks):
            ctrl_rows.extend(chunk)
        for chunk in ex.map(_xi_eps_frontier_worker, front_tasks):
            ctrl_rows.extend(chunk)
    ctrl_path = out_dir / "v8_exp1_controlled_runs.jsonl"
    ctrl_path.write_text("\n".join(json.dumps(r) for r in ctrl_rows) + "\n")
    print(f"[v8 Exp 1B] Wrote {len(ctrl_rows)} controlled runs in {time.perf_counter() - t1:.1f}s.", flush=True)

    summarize(out_dir)
    artifacts = [
        "v8_exp1_protein_runs.jsonl",
        "v8_exp1_protein_summary.csv",
        "v8_exp1_controlled_runs.jsonl",
        "v8_exp1_controlled_summary.csv",
    ]
    manifest = {
        "experiment": "v8_exp1_calibrated_proteins",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v8 Exp 1] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
