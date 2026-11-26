"""Experiment v14: Proper Joint Gaussian Credible-Ellipsoid Stopping & Valid Anytime Direct
Posterior-Risk Stopping on Real Epistatic Protein Landscapes (GB1 and TmTrpB).

Addresses the stopping-radius validity question for the 410 paired protein campaigns
(10 GB1 templates x 20 seeds = 200; 21 TmTrpB templates x 10 seeds = 210; identical GP
prior, sequence kernel, noise model, paired observation tapes, eps=0.015, delta=0.05,
budget cap 25,000 simulated assays, zero hyperparameter or policy retuning).

Evaluates three priority acquisition policies (`cd_joint`, `gp_os`, `kg`) across five
explicitly separated stopping configurations (plus zero-GP `df_os` and DF-coupled
`gp_root_info_df` references under Condition D):

  - A_orig          : Original nominal radius `beta_t = sqrt(2 log(4 M t^2 / delta))`
                      (reproduces v13 Regime A bit-for-bit).
  - B_chi95         : Primary new comparison — proper 95% joint Gaussian contrast credible
                      ellipsoid `beta_0.95 = sqrt(chi2_{r, 0.95})`, where
                      `r = rank(H Sigma_t H) = M - 1` (no `t^2` correction; Algorithm 1
                      `CD-Joint` and `GP-OS` receive the stopping ellipsoid's radius `beta_0.95`,
                      matching the synthetic v12 protocol with zero retuning; `KG` is parameter-free).
  - C_chi90         : Sensitivity — proper 90% joint Gaussian contrast credible ellipsoid
                      `beta_0.90 = sqrt(chi2_{r, 0.90})`, `r = M - 1`, no `t^2` correction.
  - B_chi95_frozen  : Frozen-trajectory ablation — evaluates `beta_0.95 = sqrt(chi2_{r, 0.95})`
  - C_chi90_frozen    and `beta_0.90 = sqrt(chi2_{r, 0.90})` directly along the untouched
                      `A_orig` (`beta_nom`) trajectories of `CD-Joint` and `GP-OS` (exposing
                      radius-mismatch stalling when acquisition and stopping radii differ).
  - E_postrisk      : Valid anytime union-bound direct posterior-risk stopping
                      (Appendix E.2.3 protocol): fresh conditionally independent posterior draws
                      `N_MC = 4096` per check `j = 1, 2, ...`, auxiliary MC error spending
                      `eta_{j,a} = eta / (K * j * (j + 1))` with `eta = 0.01`, `delta_post = 0.04`
                      (`delta_post + eta = 0.05 = delta`), stopping iff
                      `min_a CP_{1 - eta_{j,a}}(k_fail(a), N_MC) <= delta_post`, evaluated along
                      the untouched frozen `A_orig` trajectories.
  - D_df_eb         : Formal distribution-free anytime-valid Empirical Bernstein stopping
                      (preserving the v13 Regime B frequentist comparison self-contained).

For every stopping rule and method, records certification rate, restricted mean assays [95% CI],
median among certified and all runs, paired `CD/KG`, `KG/Method`, and `Method/CD` ratios [95%
paired bootstrap CIs], actual root-decision regret, empirical coverage of the certified
root-regret bound (`true_regret <= cert_regret_bound`), exact joint contrast-ellipsoid coverage
(`Q_contrast(mu* - m_t) <= beta^2`), pointwise GP coverage, false-certificate rate + CP95 upper
bound, and acquisition/stopping compute times.
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
from scipy.linalg import cho_factor, cho_solve
from scipy.stats import beta as beta_dist, chi2

from dagcert import DualWitnessCovers
from dagcert.benchmarks import protein_sequence_kernel
from dagcert.benchmarks import (
    GB1MutationCampaignProblem,
    TrpBMutationCampaignProblem,
    real_world_problem_diagnostics,
)
from dagcert import JointEllipsoidCertifier, SupportStructure
from dagcert import (
    SharedGaussianPosterior,
    correlated_kg_log_scores,
)
from experiment.protein_engineering.exp_real_world_applications import GB1_TEMPLATES
from experiment.protein_engineering.exp_real_world_validation import TRPB_TEMPLATES
from experiment.protein_engineering.exp_matched_bed_vs_kg import (
    CAP_ASSAYS,
    DELTA,
    GB1_SEEDS,
    PRIMARY_EPS,
    TRPB_SEEDS,
    _bayes_check_schedule,
    _bootstrap_mean_ci,
    _check_bayes_ellipsoid,
    _cp_upper_95,
    _nominal_gp_beta,
    _paired_bootstrap_ratio_ci,
    _pointwise_coverage_diag,
    run_gp_root_info_df_and_df_os,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/v14_protein_credible_ellipsoid"

EPS = PRIMARY_EPS  # 0.015
MC_POSTRISK_DRAWS = 4096
MC_POSTRISK_ETA = 0.01
MC_POSTRISK_DELTA_POST = 0.04  # delta_post + eta == 0.05 == DELTA

PRIORITY_METHODS: tuple[str, ...] = ("kg", "gp_os", "cd_joint")
COND_D_METHODS: tuple[str, ...] = ("kg", "gp_os", "cd_joint", "gp_root_info_df", "df_os")

ALL_CONDITIONS: tuple[str, ...] = (
    "A_orig",
    "B_chi95",
    "C_chi90",
    "B_chi95_frozen",
    "C_chi90_frozen",
    "E_postrisk",
    "D_df_eb",
)

_POLICY_SEED_TAG: dict[str, int] = {
    "kg": 101,
    "gp_os": 202,
    "cd_joint": 303,
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contrast_rank_of_kernel(kernel: np.ndarray) -> int:
    """Exact rank r = rank(H K H), where H = I - 1 1^T / M projects onto contrasts."""
    m = int(kernel.shape[0])
    h_mat = np.eye(m, dtype=np.float64) - np.ones((m, m), dtype=np.float64) / float(m)
    kc = h_mat @ kernel @ h_mat
    eigs = np.linalg.eigvalsh(0.5 * (kc + kc.T))
    tol = max(1e-12, 1e-10 * float(np.max(np.abs(eigs))))
    return max(1, int(np.sum(eigs > tol)))


def chi2_credible_beta(contrast_rank: int, level: float) -> float:
    """Exact joint Gaussian credible-ellipsoid radius sqrt(chi2_{r, level}) (no t^2 factor)."""
    return math.sqrt(float(chi2.ppf(float(level), df=int(contrast_rank))))


def contrast_ellipsoid_coverage(
    means: np.ndarray,
    sigma_mat: np.ndarray,
    beta: float,
    true_means: np.ndarray,
) -> tuple[bool, float]:
    """Exact check of whether H (true_means - means) lies inside the projected beta-ellipsoid:

        Q_contrast(d) = min_{c in R} (d - c 1)^T Sigma^{-1} (d - c 1)
                      = d^T Sigma^{-1} d - (1^T Sigma^{-1} d)^2 / (1^T Sigma^{-1} 1) <= beta^2.

    Because root regret is shift-invariant, Q_contrast <= beta^2 is necessary and sufficient for
    true_means - c*1 to belong to the joint ellipsoid for some scalar shift c, which guarantees
    true_regret(a) <= R_t(a) simultaneously for every root action a.
    """
    d = np.asarray(true_means, dtype=np.float64) - np.asarray(means, dtype=np.float64)
    m = len(d)
    sym = 0.5 * (sigma_mat + sigma_mat.T)
    jit = 1e-13 * max(1.0, float(np.max(np.diag(sym))))
    c_fac, low = cho_factor(sym + jit * np.eye(m, dtype=np.float64))
    ones = np.ones(m, dtype=np.float64)
    rhs = np.column_stack([d, ones])
    sol = cho_solve((c_fac, low), rhs)
    x_d = sol[:, 0]
    x_1 = sol[:, 1]
    quad_d = float(d @ x_d)
    one_d = float(ones @ x_d)
    one_1 = max(1e-18, float(ones @ x_1))
    q_contrast = max(0.0, quad_d - (one_d * one_d) / one_1)
    dist = math.sqrt(q_contrast)
    return bool(dist <= float(beta) + 1e-9), dist


def cp_upper_exact(k_fail: int, n_trials: int, alpha: float) -> float:
    """Exact one-sided (1 - alpha) Clopper-Pearson upper confidence bound."""
    if n_trials <= 0 or k_fail >= n_trials:
        return 1.0
    return float(beta_dist.ppf(1.0 - float(alpha), int(k_fail) + 1, int(n_trials) - int(k_fail)))


def mc_postrisk_schedule(t_done: int, cap: int) -> bool:
    """Deterministic check schedule for Condition E (shared identically across all policies)."""
    if t_done == cap:
        return True
    if t_done <= 0:
        return False
    if t_done <= 500:
        return (t_done % 10) == 0
    if t_done <= 2000:
        return (t_done % 25) == 0
    return (t_done % 100) == 0


def eval_direct_posterior_risk_valid(
    means: np.ndarray,
    sigma_mat: np.ndarray,
    supports: tuple[np.ndarray, ...],
    eps: float,
    check_idx: int,
    n_mc: int,
    eta: float,
    delta_post: float,
    rng: np.random.Generator,
) -> tuple[bool, int, float, float]:
    """Valid anytime union-bound Monte Carlo direct posterior-risk test (Appendix E.2.3).

    Draws `n_mc` fresh conditionally independent Gaussian samples from N(means, sigma_mat),
    allocates MC error budget `eta_{j,a} = eta / (K * j * (j + 1))` at check index `j >= 1`,
    and stops iff `min_a CP_{1 - eta_{j,a}}(k_fail(a), n_mc) <= delta_post`.
    Under a correctly specified prior and likelihood, a union bound over all checks `j >= 1`
    and actions `a = 1..K` bounds prior-predictive decision error by `delta_post + eta`.
    """
    m = len(means)
    k_act = len(supports)
    sym = 0.5 * (sigma_mat + sigma_mat.T)
    jit = 1e-13 * max(1.0, float(np.max(np.diag(sym))))
    chol = np.linalg.cholesky(sym + jit * np.eye(m, dtype=np.float64))
    z = rng.standard_normal((m, int(n_mc)))
    draws = means[:, None] + (chol @ z)
    v_star = np.max(draws, axis=0)

    eta_ja = float(eta) / (float(k_act) * float(check_idx) * float(check_idx + 1))
    best_a = 0
    best_cp = 1.0
    best_q = 1.0
    for a, sup in enumerate(supports):
        v_a = np.max(draws[sup, :], axis=0)
        k_fail = int(np.sum((v_star - v_a) > (float(eps) + 1e-12)))
        cp_hi = cp_upper_exact(k_fail, int(n_mc), eta_ja)
        if cp_hi < best_cp or (cp_hi == best_cp and a < best_a):
            best_cp = cp_hi
            best_q = k_fail / float(n_mc)
            best_a = a
    return bool(best_cp <= float(delta_post)), int(best_a), float(best_q), float(best_cp)


def select_gp_arm_with_beta(
    policy: str,
    ss: SupportStructure,
    leaf_to_actions: list[list[int]],
    post: SharedGaussianPosterior,
    certifier: JointEllipsoidCertifier,
    beta: float,
    eps: float,
) -> int:
    """Select next terminal index `0..M-1` using the exact v13 policy rules with radius `beta`.

    Zero retuning: `beta` is strictly the stopping ellipsoid's radius (`_nominal_gp_beta` for
    `A_orig` / frozen streams; `sqrt(chi2_{r, 0.95})` or `sqrt(chi2_{r, 0.90})` for matched
    `B_chi95` / `C_chi90`). `kg` does not depend on `beta`.
    """
    means = post.mean
    if policy == "kg":
        scores = correlated_kg_log_scores(means, post.sigma_mat, post.obs_var, ss.costs, use_cpp=True)
        return int(np.argmax(scores))

    stds = post.stds()
    u_ell = means + beta * stds
    l_ell = means - beta * stds

    if policy == "gp_os":
        best_a = 0
        best_sep = -math.inf
        for a in range(ss.k):
            comp = ss.complements[a]
            u_in = float(np.max(u_ell[ss.supports[a]]))
            l_out = float(np.max(l_ell[comp])) if len(comp) else -math.inf
            sep = u_in - l_out
            if sep > best_sep:
                best_sep = sep
                best_a = a
        sup_b = ss.supports[best_a]
        comp_b = ss.complements[best_a]
        p_idx = int(sup_b[int(np.argmax(u_ell[sup_b]))])
        if len(comp_b) == 0:
            return p_idx
        q_idx = int(comp_b[int(np.argmax(u_ell[comp_b]))])
        return p_idx if float(stds[p_idx]) >= float(stds[q_idx]) else q_idx

    if policy == "cd_joint":
        y_opt = int(np.argmax(u_ell))
        best_sep = -math.inf
        b_t = leaf_to_actions[y_opt][0]
        for a in leaf_to_actions[y_opt]:
            comp = ss.complements[a]
            l_out = float(np.max(l_ell[comp])) if len(comp) else -math.inf
            sep = float(u_ell[y_opt]) - l_out
            if sep > best_sep:
                best_sep = sep
                b_t = a
        prev_eps = certifier.epsilon
        certifier.epsilon = float(eps)
        try:
            cb = certifier.certify_action_gp(
                action=b_t,
                means=means,
                sigma_mat=post.sigma_mat,
                beta=beta,
                stop_if_above_eps=True,
            )
        finally:
            certifier.epsilon = prev_eps
        z_t = cb.challenger_idx
        if z_t < 0:
            return y_opt
        gap_hat = float(means[z_t] - (cb.inside_weights @ means[cb.inside_indices]))
        if gap_hat <= 0.5 * eps:
            g = cb.contrast
        else:
            g = np.zeros(ss.m, dtype=np.float64)
            g[z_t] = 1.0
            g[y_opt] = -1.0
        sg = post.sigma_mat @ g
        dv = (sg * sg) / (post.obs_var + np.maximum(1e-18, np.diag(post.sigma_mat)))
        return int(np.argmax(dv / ss.costs))

    raise ValueError(f"Unknown policy: {policy!r}")


def _make_ellipsoid_record(
    base: dict,
    condition: str,
    method: str,
    certified: bool,
    steps: int,
    action: int,
    cert_regret_bound: float,
    beta_val: float,
    means: np.ndarray,
    sigma_mat: np.ndarray,
    stds: np.ndarray,
    true_means_vec: np.ndarray,
    regrets: list[float],
    eps: float,
    distinct_leaves: int,
    acq_time_s: float,
    cert_time_s: float,
    total_time_s: float,
) -> dict:
    tr = float(regrets[int(action)])
    pw_all, pw_maxz, pw_frac = _pointwise_coverage_diag(means, stds, beta_val, true_means_vec)
    joint_cov, contrast_maha = contrast_ellipsoid_coverage(means, sigma_mat, beta_val, true_means_vec)
    reg_bound_val = float(cert_regret_bound) if math.isfinite(cert_regret_bound) else float("nan")
    reg_bound_cov = bool((not math.isfinite(cert_regret_bound)) or (tr <= cert_regret_bound + 1e-9))
    return {
        **base,
        "condition": condition,
        "method": method,
        "certified": bool(certified),
        "steps": int(steps),
        "action": int(action),
        "beta_at_stop": round(float(beta_val), 4),
        "true_regret": round(tr, 6),
        "cert_regret_bound": round(reg_bound_val, 6) if math.isfinite(reg_bound_val) else None,
        "regret_bound_covered": bool(reg_bound_cov),
        "false_cert": bool(certified and tr > eps + 1e-12),
        "joint_contrast_covered": bool(joint_cov),
        "contrast_mahalanobis": round(float(contrast_maha), 4),
        "pointwise_all_covered": bool(pw_all),
        "pointwise_max_z_ratio": round(float(pw_maxz), 4),
        "pointwise_frac_covered": round(float(pw_frac), 4),
        "mc_risk_hat": None,
        "mc_cp_upper": None,
        "distinct_leaves": int(distinct_leaves),
        "acq_time_s": round(float(acq_time_s), 4),
        "cert_time_s": round(float(cert_time_s), 4),
        "total_time_s": round(float(total_time_s), 4),
    }


def _load_problem(landscape: str, start_seq: str) -> tuple:
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
    ratio = float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"]))
    regime_tag = "epistatic_ridge" if ratio >= 10.0 else "single_peak"

    ss = SupportStructure(prob.graph)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    true_means_vec = np.array([float(prob.means[z]) for z in ss.leaves], dtype=np.float64)

    seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
    kernel = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
    r_rank = contrast_rank_of_kernel(kernel)

    leaf_to_actions: list[list[int]] = [[] for _ in range(ss.m)]
    for a, sup in enumerate(ss.supports):
        for idx in sup:
            leaf_to_actions[int(idx)].append(a)

    return prob, ss, leaf_to_actions, kernel, prior_m, obs_s, regrets, true_means_vec, r_rank, regime_tag


def run_frozen_trajectory_multi_stop(
    prob,
    ss: SupportStructure,
    leaf_to_actions: list[list[int]],
    kernel: np.ndarray,
    prior_m: float,
    obs_s: float,
    regrets: list[float],
    true_means_vec: np.ndarray,
    r_rank: int,
    base: dict,
    seed: int,
    policy: str,
    eps: float,
    delta: float,
    cap: int,
    mc_draws: int,
    duplicate_chi2_as_matched: bool = False,
) -> list[dict]:
    """Run ONE fixed acquisition trajectory (`A_orig` beta_nom for cd_joint/gp_os, parameter-free
    for kg) and simultaneously evaluate:
      - A_orig          (sqrt(2 log(4 M t^2 / delta)))
      - B_chi95_frozen  (sqrt(chi2_{r, 0.95}))  [+ B_chi95 if duplicate_chi2_as_matched (kg)]
      - C_chi90_frozen  (sqrt(chi2_{r, 0.90}))  [+ C_chi90 if duplicate_chi2_as_matched (kg)]
      - E_postrisk      (valid anytime union-bound MC posterior risk, N_mc fresh draws/check)
      - D_df_eb         (formal distribution-free Empirical Bernstein stopping)
    """
    beta_95 = chi2_credible_beta(r_rank, 0.95)
    beta_90 = chi2_credible_beta(r_rank, 0.90)

    post = SharedGaussianPosterior(kernel, prior_m, obs_s, delta=delta, beta_mode="posterior_credible")
    certifier = JointEllipsoidCertifier(ss, epsilon=eps, solver="colgen_lazy", exact_linear_mean=False)
    df_mon = DualWitnessCovers(prob.graph, delta=delta, schedule="emp_bernstein", layout="best", track_separation=True)
    oracle = prob.oracle(seed)

    rng_seed = (int(seed) * 1000003 + _POLICY_SEED_TAG[policy] * 7919 + 4219) & 0xFFFFFFFFFFFFFFFF
    mc_rng = np.random.default_rng(rng_seed)

    rec: dict[str, dict | None] = {
        "A_orig": None,
        "B_chi95_frozen": None,
        "C_chi90_frozen": None,
        "E_postrisk": None,
        "D_df_eb": None,
    }
    mc_check_idx = 0
    t_start = time.perf_counter()
    acq_s = 0.0
    cert_s_ell = {"A_orig": 0.0, "B_chi95_frozen": 0.0, "C_chi90_frozen": 0.0}
    cert_s_mc = 0.0

    for step in range(1, cap + 1):
        t_done = step - 1

        # 1. Condition D (DF Empirical Bernstein) checked every step
        if rec["D_df_eb"] is None:
            act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
            if reg_df <= eps:
                tr = float(regrets[int(act_df)])
                rec["D_df_eb"] = {
                    **base,
                    "condition": "D_df_eb",
                    "method": policy,
                    "certified": True,
                    "steps": int(t_done),
                    "action": int(act_df),
                    "beta_at_stop": None,
                    "true_regret": round(tr, 6),
                    "cert_regret_bound": round(float(reg_df), 6),
                    "regret_bound_covered": bool(tr <= float(reg_df) + 1e-9),
                    "false_cert": bool(tr > eps + 1e-12),
                    "joint_contrast_covered": True,
                    "contrast_mahalanobis": None,
                    "pointwise_all_covered": True,
                    "pointwise_max_z_ratio": 0.0,
                    "pointwise_frac_covered": 1.0,
                    "mc_risk_hat": None,
                    "mc_cp_upper": None,
                    "distinct_leaves": int(np.sum(post.arm_counts > 0)),
                    "acq_time_s": round(acq_s, 4),
                    "cert_time_s": 0.0,
                    "total_time_s": round(time.perf_counter() - t_start, 4),
                }

        # 2. Ellipsoid conditions A_orig, C_chi90_frozen, B_chi95_frozen on identical check schedule
        if t_done > 0 and _bayes_check_schedule(t_done, cap) and (
            rec["A_orig"] is None or rec["C_chi90_frozen"] is None or rec["B_chi95_frozen"] is None
        ):
            means = post.mean
            stds = post.stds()
            for cname, bval in (
                ("A_orig", _nominal_gp_beta(ss.m, t_done, delta)),
                ("C_chi90_frozen", beta_90),
                ("B_chi95_frozen", beta_95),
            ):
                if rec[cname] is not None:
                    continue
                tc0 = time.perf_counter()
                ok, act_b, reg_b = _check_bayes_ellipsoid(certifier, ss, means, post.sigma_mat, stds, bval, eps)
                cert_s_ell[cname] += time.perf_counter() - tc0
                if ok:
                    rec[cname] = _make_ellipsoid_record(
                        base=base,
                        condition=cname,
                        method=policy,
                        certified=True,
                        steps=t_done,
                        action=act_b,
                        cert_regret_bound=reg_b,
                        beta_val=bval,
                        means=means,
                        sigma_mat=post.sigma_mat,
                        stds=stds,
                        true_means_vec=true_means_vec,
                        regrets=regrets,
                        eps=eps,
                        distinct_leaves=int(np.sum(post.arm_counts > 0)),
                        acq_time_s=acq_s,
                        cert_time_s=cert_s_ell[cname],
                        total_time_s=time.perf_counter() - t_start,
                    )

        # 3. Condition E (valid anytime union-bound direct posterior-risk)
        if t_done > 0 and rec["E_postrisk"] is None and mc_postrisk_schedule(t_done, cap):
            tc0 = time.perf_counter()
            mc_check_idx += 1
            ok_e, act_e, q_e, cp_e = eval_direct_posterior_risk_valid(
                post.mean,
                post.sigma_mat,
                ss.supports,
                eps,
                mc_check_idx,
                mc_draws,
                MC_POSTRISK_ETA,
                MC_POSTRISK_DELTA_POST,
                mc_rng,
            )
            cert_s_mc += time.perf_counter() - tc0
            if ok_e:
                tr = float(regrets[int(act_e)])
                rec["E_postrisk"] = {
                    **base,
                    "condition": "E_postrisk",
                    "method": policy,
                    "certified": True,
                    "steps": int(t_done),
                    "action": int(act_e),
                    "beta_at_stop": None,
                    "true_regret": round(tr, 6),
                    "cert_regret_bound": round(float(eps), 6),
                    "regret_bound_covered": bool(tr <= eps + 1e-12),
                    "false_cert": bool(tr > eps + 1e-12),
                    "joint_contrast_covered": None,
                    "contrast_mahalanobis": None,
                    "pointwise_all_covered": None,
                    "pointwise_max_z_ratio": None,
                    "pointwise_frac_covered": None,
                    "mc_risk_hat": round(float(q_e), 6),
                    "mc_cp_upper": round(float(cp_e), 6),
                    "distinct_leaves": int(np.sum(post.arm_counts > 0)),
                    "acq_time_s": round(acq_s, 4),
                    "cert_time_s": round(cert_s_mc, 4),
                    "total_time_s": round(time.perf_counter() - t_start, 4),
                }

        if all(v is not None for v in rec.values()):
            break

        # 4. Acquire next observation using exact v13 policy (beta_nom for cd_joint/gp_os, parameter-free kg)
        ta = time.perf_counter()
        beta_acq = _nominal_gp_beta(ss.m, step, delta)
        arm = select_gp_arm_with_beta(policy, ss, leaf_to_actions, post, certifier, beta_acq, eps)
        acq_s += time.perf_counter() - ta

        leaf = ss.leaves[arm]
        r = float(oracle.sample(leaf))
        post.observe(arm, r)
        df_mon.step(leaf, r)

    # Final cap evaluation for any uncertified condition
    means = post.mean
    stds = post.stds()
    emp_a = int(np.argmax([float(np.max(means[sup])) for sup in ss.supports]))
    distinct_end = int(np.sum(post.arm_counts > 0))
    wall_end = time.perf_counter() - t_start

    if rec["D_df_eb"] is None:
        act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
        ok_df = bool(reg_df <= eps)
        tr = float(regrets[int(act_df)])
        rec["D_df_eb"] = {
            **base,
            "condition": "D_df_eb",
            "method": policy,
            "certified": ok_df,
            "steps": int(cap),
            "action": int(act_df),
            "beta_at_stop": None,
            "true_regret": round(tr, 6),
            "cert_regret_bound": round(float(reg_df), 6),
            "regret_bound_covered": bool(tr <= float(reg_df) + 1e-9),
            "false_cert": bool(ok_df and tr > eps + 1e-12),
            "joint_contrast_covered": True,
            "contrast_mahalanobis": None,
            "pointwise_all_covered": True,
            "pointwise_max_z_ratio": 0.0,
            "pointwise_frac_covered": 1.0,
            "mc_risk_hat": None,
            "mc_cp_upper": None,
            "distinct_leaves": distinct_end,
            "acq_time_s": round(acq_s, 4),
            "cert_time_s": 0.0,
            "total_time_s": round(wall_end, 4),
        }

    for cname, bval in (
        ("A_orig", _nominal_gp_beta(ss.m, cap, delta)),
        ("C_chi90_frozen", beta_90),
        ("B_chi95_frozen", beta_95),
    ):
        if rec[cname] is None:
            tc0 = time.perf_counter()
            ok, act_b, reg_b = _check_bayes_ellipsoid(certifier, ss, means, post.sigma_mat, stds, bval, eps)
            cert_s_ell[cname] += time.perf_counter() - tc0
            rec_a = int(act_b) if ok else emp_a
            # If uncertified, evaluate the actual conic bound for the empirical recommended action too
            if not ok:
                ca_emp = certifier.certify_action_gp(rec_a, means, post.sigma_mat, bval, stop_if_above_eps=False)
                reg_b = float(ca_emp.regret)
            rec[cname] = _make_ellipsoid_record(
                base=base,
                condition=cname,
                method=policy,
                certified=ok,
                steps=cap,
                action=rec_a,
                cert_regret_bound=reg_b,
                beta_val=bval,
                means=means,
                sigma_mat=post.sigma_mat,
                stds=stds,
                true_means_vec=true_means_vec,
                regrets=regrets,
                eps=eps,
                distinct_leaves=distinct_end,
                acq_time_s=acq_s,
                cert_time_s=cert_s_ell[cname],
                total_time_s=time.perf_counter() - t_start,
            )

    if rec["E_postrisk"] is None:
        tc0 = time.perf_counter()
        mc_check_idx += 1
        ok_e, act_e, q_e, cp_e = eval_direct_posterior_risk_valid(
            means,
            post.sigma_mat,
            ss.supports,
            eps,
            mc_check_idx,
            mc_draws,
            MC_POSTRISK_ETA,
            MC_POSTRISK_DELTA_POST,
            mc_rng,
        )
        cert_s_mc += time.perf_counter() - tc0
        rec_a = int(act_e) if ok_e else emp_a
        tr = float(regrets[rec_a])
        rec["E_postrisk"] = {
            **base,
            "condition": "E_postrisk",
            "method": policy,
            "certified": ok_e,
            "steps": int(cap),
            "action": rec_a,
            "beta_at_stop": None,
            "true_regret": round(tr, 6),
            "cert_regret_bound": round(float(eps), 6) if ok_e else None,
            "regret_bound_covered": bool((not ok_e) or (tr <= eps + 1e-12)),
            "false_cert": bool(ok_e and tr > eps + 1e-12),
            "joint_contrast_covered": None,
            "contrast_mahalanobis": None,
            "pointwise_all_covered": None,
            "pointwise_max_z_ratio": None,
            "pointwise_frac_covered": None,
            "mc_risk_hat": round(float(q_e), 6),
            "mc_cp_upper": round(float(cp_e), 6),
            "distinct_leaves": distinct_end,
            "acq_time_s": round(acq_s, 4),
            "cert_time_s": round(cert_s_mc, 4),
            "total_time_s": round(time.perf_counter() - t_start, 4),
        }

    out = [rec[k] for k in ("A_orig", "B_chi95_frozen", "C_chi90_frozen", "E_postrisk", "D_df_eb")]
    if duplicate_chi2_as_matched:
        # KG has no beta parameter, so its trajectory for B_chi95 / C_chi90 is bit-identical to B/C_frozen
        out.append({**rec["B_chi95_frozen"], "condition": "B_chi95"})
        out.append({**rec["C_chi90_frozen"], "condition": "C_chi90"})
    return out


def run_matched_chi2_trajectory(
    prob,
    ss: SupportStructure,
    leaf_to_actions: list[list[int]],
    kernel: np.ndarray,
    prior_m: float,
    obs_s: float,
    regrets: list[float],
    true_means_vec: np.ndarray,
    r_rank: int,
    base: dict,
    seed: int,
    policy: str,
    condition: str,
    level: float,
    eps: float,
    delta: float,
    cap: int,
) -> dict:
    """Run Algorithm 1 (`cd_joint`) or `gp_os` with its radius matched to the stopping ellipsoid
    `beta = sqrt(chi2_{r, level})` (no `t^2` factor, zero retuning).
    """
    beta_val = chi2_credible_beta(r_rank, level)
    post = SharedGaussianPosterior(kernel, prior_m, obs_s, delta=delta, beta_mode="posterior_credible")
    certifier = JointEllipsoidCertifier(ss, epsilon=eps, solver="colgen_lazy", exact_linear_mean=False)
    oracle = prob.oracle(seed)

    t_start = time.perf_counter()
    acq_s = 0.0
    cert_s = 0.0
    for step in range(1, cap + 1):
        t_done = step - 1
        if t_done > 0 and _bayes_check_schedule(t_done, cap):
            tc0 = time.perf_counter()
            means = post.mean
            stds = post.stds()
            ok, act_b, reg_b = _check_bayes_ellipsoid(certifier, ss, means, post.sigma_mat, stds, beta_val, eps)
            cert_s += time.perf_counter() - tc0
            if ok:
                return _make_ellipsoid_record(
                    base=base,
                    condition=condition,
                    method=policy,
                    certified=True,
                    steps=t_done,
                    action=act_b,
                    cert_regret_bound=reg_b,
                    beta_val=beta_val,
                    means=means,
                    sigma_mat=post.sigma_mat,
                    stds=stds,
                    true_means_vec=true_means_vec,
                    regrets=regrets,
                    eps=eps,
                    distinct_leaves=int(np.sum(post.arm_counts > 0)),
                    acq_time_s=acq_s,
                    cert_time_s=cert_s,
                    total_time_s=time.perf_counter() - t_start,
                )

        ta = time.perf_counter()
        arm = select_gp_arm_with_beta(policy, ss, leaf_to_actions, post, certifier, beta_val, eps)
        acq_s += time.perf_counter() - ta
        post.observe(arm, float(oracle.sample(ss.leaves[arm])))

    tc0 = time.perf_counter()
    means = post.mean
    stds = post.stds()
    ok, act_b, reg_b = _check_bayes_ellipsoid(certifier, ss, means, post.sigma_mat, stds, beta_val, eps)
    cert_s += time.perf_counter() - tc0
    emp_a = int(np.argmax([float(np.max(means[sup])) for sup in ss.supports]))
    rec_a = int(act_b) if ok else emp_a
    if not ok:
        ca_emp = certifier.certify_action_gp(rec_a, means, post.sigma_mat, beta_val, stop_if_above_eps=False)
        reg_b = float(ca_emp.regret)
    return _make_ellipsoid_record(
        base=base,
        condition=condition,
        method=policy,
        certified=ok,
        steps=cap,
        action=rec_a,
        cert_regret_bound=reg_b,
        beta_val=beta_val,
        means=means,
        sigma_mat=post.sigma_mat,
        stds=stds,
        true_means_vec=true_means_vec,
        regrets=regrets,
        eps=eps,
        distinct_leaves=int(np.sum(post.arm_counts > 0)),
        acq_time_s=acq_s,
        cert_time_s=cert_s,
        total_time_s=time.perf_counter() - t_start,
    )


def _stream_worker(task: tuple[str, str, int, str, int, int]) -> list[dict]:
    landscape, start_seq, seed, stream, cap, mc_draws = task
    prob, ss, leaf_to_actions, kernel, prior_m, obs_s, regrets, true_means_vec, r_rank, regime_tag = _load_problem(
        landscape, start_seq
    )
    base = {
        "unit_id": f"{landscape}_{start_seq}_{seed}",
        "landscape": landscape,
        "start_seq": start_seq,
        "template_regime": regime_tag,
        "seed": int(seed),
        "m_leaves": int(ss.m),
        "k_actions": int(ss.k),
        "contrast_rank": int(r_rank),
        "eps": float(EPS),
    }

    if stream == "kg_all":
        return run_frozen_trajectory_multi_stop(
            prob,
            ss,
            leaf_to_actions,
            kernel,
            prior_m,
            obs_s,
            regrets,
            true_means_vec,
            r_rank,
            base,
            seed,
            policy="kg",
            eps=EPS,
            delta=DELTA,
            cap=cap,
            mc_draws=mc_draws,
            duplicate_chi2_as_matched=True,
        )

    if stream == "cd_matched":
        return [
            run_matched_chi2_trajectory(
                prob, ss, leaf_to_actions, kernel, prior_m, obs_s, regrets, true_means_vec, r_rank,
                base, seed, policy="cd_joint", condition="B_chi95", level=0.95, eps=EPS, delta=DELTA, cap=cap,
            ),
            run_matched_chi2_trajectory(
                prob, ss, leaf_to_actions, kernel, prior_m, obs_s, regrets, true_means_vec, r_rank,
                base, seed, policy="cd_joint", condition="C_chi90", level=0.90, eps=EPS, delta=DELTA, cap=cap,
            ),
        ]

    if stream == "gpos_matched":
        return [
            run_matched_chi2_trajectory(
                prob, ss, leaf_to_actions, kernel, prior_m, obs_s, regrets, true_means_vec, r_rank,
                base, seed, policy="gp_os", condition="B_chi95", level=0.95, eps=EPS, delta=DELTA, cap=cap,
            ),
            run_matched_chi2_trajectory(
                prob, ss, leaf_to_actions, kernel, prior_m, obs_s, regrets, true_means_vec, r_rank,
                base, seed, policy="gp_os", condition="C_chi90", level=0.90, eps=EPS, delta=DELTA, cap=cap,
            ),
        ]

    if stream == "frozen_and_df":
        rows: list[dict] = []
        for pol in ("cd_joint", "gp_os"):
            rows.extend(
                run_frozen_trajectory_multi_stop(
                    prob,
                    ss,
                    leaf_to_actions,
                    kernel,
                    prior_m,
                    obs_s,
                    regrets,
                    true_means_vec,
                    r_rank,
                    base,
                    seed,
                    policy=pol,
                    eps=EPS,
                    delta=DELTA,
                    cap=cap,
                    mc_draws=mc_draws,
                    duplicate_chi2_as_matched=False,
                )
            )
        # Preserve Condition D formal DF references (DF-OS & DF-coupled GP-Root-Info) self-contained
        df_ref_rows = run_gp_root_info_df_and_df_os(
            prob=prob,
            ss=ss,
            kernel=kernel,
            prior_mean=prior_m,
            obs_std=obs_s,
            regrets=regrets,
            seed=seed,
            eps_targets=(EPS,),
            cap=cap,
            delta=DELTA,
            landscape=landscape,
            start_seq=start_seq,
            regime_tag=regime_tag,
        )
        for r in df_ref_rows:
            rows.append(
                {
                    **base,
                    "condition": "D_df_eb",
                    "method": r["method"],
                    "certified": bool(r["certified"]),
                    "steps": int(r["steps"]),
                    "action": int(r["action"]),
                    "beta_at_stop": None,
                    "true_regret": float(r["true_regret"]),
                    "cert_regret_bound": round(float(EPS), 6) if r["certified"] else None,
                    "regret_bound_covered": bool((not r["certified"]) or (float(r["true_regret"]) <= EPS + 1e-12)),
                    "false_cert": bool(r["false_cert"]),
                    "joint_contrast_covered": True,
                    "contrast_mahalanobis": None,
                    "pointwise_all_covered": True,
                    "pointwise_max_z_ratio": 0.0,
                    "pointwise_frac_covered": 1.0,
                    "mc_risk_hat": None,
                    "mc_cp_upper": None,
                    "distinct_leaves": int(r["distinct_leaves"]),
                    "acq_time_s": float(r["acq_time_s"]),
                    "cert_time_s": float(r["cert_time_s"]),
                    "total_time_s": float(r["total_time_s"]),
                }
            )
        return rows

    raise ValueError(f"Unknown stream: {stream!r}")


def summarize(dest: Path) -> None:
    p_runs = dest / "v14_protein_credible_runs.jsonl"
    runs = [json.loads(line) for line in p_runs.read_text().splitlines() if line.strip()]

    summary_rows: list[dict] = []
    template_rows: list[dict] = []

    for cond in ALL_CONDITIONS:
        methods = COND_D_METHODS if cond == "D_df_eb" else PRIORITY_METHODS
        for land in ("gb1", "trpb"):
            cohort = [r for r in runs if r["condition"] == cond and r["landscape"] == land]
            if not cohort:
                continue
            kg_map = {r["unit_id"]: r for r in cohort if r["method"] == "kg"}
            cd_map = {r["unit_id"]: r for r in cohort if r["method"] == "cd_joint"}
            gpos_map = {r["unit_id"]: r for r in cohort if r["method"] == "gp_os"}

            for m_idx, method in enumerate(methods):
                sub = [r for r in cohort if r["method"] == method]
                if not sub:
                    continue
                n = len(sub)
                steps_arr = np.array([float(r["steps"]) for r in sub], dtype=np.float64)
                rm_pt, rm_lo, rm_hi = _bootstrap_mean_ci(steps_arr, seed=14000 + m_idx)
                cert_sub = [r for r in sub if r["certified"]]
                n_cert = len(cert_sub)
                n_err = sum(1 for r in sub if r["false_cert"])
                all_regs = np.array([float(r["true_regret"]) for r in sub], dtype=np.float64)
                cert_regs = (
                    np.array([float(r["true_regret"]) for r in cert_sub], dtype=np.float64)
                    if cert_sub
                    else np.zeros(0)
                )
                succ_med = float(np.median([float(r["steps"]) for r in cert_sub])) if cert_sub else float("nan")
                all_med = float(np.median(steps_arr))
                q25 = float(np.percentile(steps_arr, 25))
                q75 = float(np.percentile(steps_arr, 75))

                reg_cov_all = sum(1 for r in sub if r["regret_bound_covered"]) / n
                reg_cov_cert = (
                    sum(1 for r in cert_sub if r["regret_bound_covered"]) / n_cert if n_cert > 0 else float("nan")
                )
                dec_ok_all = sum(1 for r in sub if float(r["true_regret"]) <= EPS + 1e-12) / n

                joint_vals = [r["joint_contrast_covered"] for r in sub if r["joint_contrast_covered"] is not None]
                joint_cov = (sum(1 for v in joint_vals if v) / len(joint_vals)) if joint_vals else float("nan")
                maha_vals = [float(r["contrast_mahalanobis"]) for r in sub if r["contrast_mahalanobis"] is not None]
                mean_maha = float(np.mean(maha_vals)) if maha_vals else float("nan")
                beta_vals = [float(r["beta_at_stop"]) for r in sub if r["beta_at_stop"] is not None]
                mean_beta = float(np.mean(beta_vals)) if beta_vals else float("nan")

                pw_all_vals = [r["pointwise_all_covered"] for r in sub if r["pointwise_all_covered"] is not None]
                pw_all_cov = (sum(1 for v in pw_all_vals if v) / len(pw_all_vals)) if pw_all_vals else float("nan")
                pw_frac_vals = [float(r["pointwise_frac_covered"]) for r in sub if r["pointwise_frac_covered"] is not None]
                pw_frac_mean = float(np.mean(pw_frac_vals)) if pw_frac_vals else float("nan")

                acq_s_arr = np.array([float(r["acq_time_s"]) for r in sub], dtype=np.float64)
                cert_s_arr = np.array([float(r["cert_time_s"]) for r in sub], dtype=np.float64)
                tot_s_arr = np.array([float(r["total_time_s"]) for r in sub], dtype=np.float64)
                ms_per_step = 1000.0 * float(np.sum(acq_s_arr)) / max(1.0, float(np.sum(steps_arr)))

                m_map = {r["unit_id"]: r for r in sub}
                uids_kg = sorted(u for u in m_map if u in kg_map)
                if uids_kg:
                    m_st = np.array([float(m_map[u]["steps"]) for u in uids_kg], dtype=np.float64)
                    k_st = np.array([float(kg_map[u]["steps"]) for u in uids_kg], dtype=np.float64)
                    m_over_kg, m_over_kg_lo, m_over_kg_hi = _paired_bootstrap_ratio_ci(m_st, k_st, seed=14100 + m_idx)
                    kg_over_m, kg_over_m_lo, kg_over_m_hi = _paired_bootstrap_ratio_ci(k_st, m_st, seed=14200 + m_idx)
                else:
                    m_over_kg = m_over_kg_lo = m_over_kg_hi = float("nan")
                    kg_over_m = kg_over_m_lo = kg_over_m_hi = float("nan")

                uids_cd = sorted(u for u in m_map if u in cd_map)
                if uids_cd:
                    m_st_c = np.array([float(m_map[u]["steps"]) for u in uids_cd], dtype=np.float64)
                    c_st = np.array([float(cd_map[u]["steps"]) for u in uids_cd], dtype=np.float64)
                    m_over_cd, m_over_cd_lo, m_over_cd_hi = _paired_bootstrap_ratio_ci(m_st_c, c_st, seed=14300 + m_idx)
                else:
                    m_over_cd = m_over_cd_lo = m_over_cd_hi = float("nan")

                uids_gp = sorted(u for u in m_map if u in gpos_map)
                if uids_gp:
                    m_st_g = np.array([float(m_map[u]["steps"]) for u in uids_gp], dtype=np.float64)
                    g_st = np.array([float(gpos_map[u]["steps"]) for u in uids_gp], dtype=np.float64)
                    gpos_over_m, gpos_over_m_lo, gpos_over_m_hi = _paired_bootstrap_ratio_ci(
                        g_st, m_st_g, seed=14400 + m_idx
                    )
                else:
                    gpos_over_m = gpos_over_m_lo = gpos_over_m_hi = float("nan")

                summary_rows.append(
                    {
                        "condition": cond,
                        "landscape": land,
                        "method": method,
                        "runs": n,
                        "mean_contrast_rank": round(float(np.mean([r["contrast_rank"] for r in sub])), 1),
                        "mean_beta_at_stop": round(mean_beta, 3) if math.isfinite(mean_beta) else "",
                        "cert_rate": round(n_cert / n, 4),
                        "restricted_mean": round(rm_pt, 2),
                        "rm_ci95_lo": round(rm_lo, 2),
                        "rm_ci95_hi": round(rm_hi, 2),
                        "med_all": round(all_med, 1),
                        "q25_all": round(q25, 1),
                        "q75_all": round(q75, 1),
                        "med_certified": round(succ_med, 1) if math.isfinite(succ_med) else "",
                        "ratio_method_over_kg": round(m_over_kg, 4) if math.isfinite(m_over_kg) else "",
                        "ratio_method_over_kg_ci95_lo": round(m_over_kg_lo, 4) if math.isfinite(m_over_kg_lo) else "",
                        "ratio_method_over_kg_ci95_hi": round(m_over_kg_hi, 4) if math.isfinite(m_over_kg_hi) else "",
                        "speedup_kg_over_method": round(kg_over_m, 3) if math.isfinite(kg_over_m) else "",
                        "speedup_kg_over_method_ci95_lo": round(kg_over_m_lo, 3) if math.isfinite(kg_over_m_lo) else "",
                        "speedup_kg_over_method_ci95_hi": round(kg_over_m_hi, 3) if math.isfinite(kg_over_m_hi) else "",
                        "ratio_method_over_cd": round(m_over_cd, 3) if math.isfinite(m_over_cd) else "",
                        "ratio_method_over_cd_ci95_lo": round(m_over_cd_lo, 3) if math.isfinite(m_over_cd_lo) else "",
                        "ratio_method_over_cd_ci95_hi": round(m_over_cd_hi, 3) if math.isfinite(m_over_cd_hi) else "",
                        "speedup_gpos_over_method": round(gpos_over_m, 3) if math.isfinite(gpos_over_m) else "",
                        "speedup_gpos_over_method_ci95_lo": round(gpos_over_m_lo, 3) if math.isfinite(gpos_over_m_lo) else "",
                        "speedup_gpos_over_method_ci95_hi": round(gpos_over_m_hi, 3) if math.isfinite(gpos_over_m_hi) else "",
                        "false_certs": n_err,
                        "false_cert_rate": round(n_err / n, 4),
                        "cp95_upper_err": round(_cp_upper_95(n_err, n), 4),
                        "mean_root_regret_all": round(float(np.mean(all_regs)), 6),
                        "max_root_regret_all": round(float(np.max(all_regs)), 6),
                        "mean_root_regret_cert": round(float(np.mean(cert_regs)), 6) if len(cert_regs) else 0.0,
                        "decision_eps_ok_rate": round(dec_ok_all, 4),
                        "regret_bound_cov_all": round(reg_cov_all, 4),
                        "regret_bound_cov_cert": round(reg_cov_cert, 4) if math.isfinite(reg_cov_cert) else "",
                        "joint_contrast_cov": round(joint_cov, 4) if math.isfinite(joint_cov) else "",
                        "mean_contrast_maha": round(mean_maha, 3) if math.isfinite(mean_maha) else "",
                        "pointwise_all_cov": round(pw_all_cov, 4) if math.isfinite(pw_all_cov) else "",
                        "pointwise_frac_cov": round(pw_frac_mean, 4) if math.isfinite(pw_frac_mean) else "",
                        "mean_distinct_leaves": round(float(np.mean([r["distinct_leaves"] for r in sub])), 1),
                        "mean_acq_time_s": round(float(np.mean(acq_s_arr)), 3),
                        "mean_cert_time_s": round(float(np.mean(cert_s_arr)), 3),
                        "acq_ms_per_step": round(ms_per_step, 4),
                        "mean_total_time_s": round(float(np.mean(tot_s_arr)), 3),
                    }
                )

            if cond in ("A_orig", "B_chi95", "C_chi90", "E_postrisk"):
                for tmpl in sorted(set(r["start_seq"] for r in cohort)):
                    for method in PRIORITY_METHODS:
                        tsub = [r for r in cohort if r["start_seq"] == tmpl and r["method"] == method]
                        if not tsub:
                            continue
                        t_st = np.array([float(r["steps"]) for r in tsub], dtype=np.float64)
                        template_rows.append(
                            {
                                "condition": cond,
                                "landscape": land,
                                "start_seq": tmpl,
                                "template_regime": tsub[0]["template_regime"],
                                "m_leaves": tsub[0]["m_leaves"],
                                "k_actions": tsub[0]["k_actions"],
                                "contrast_rank": tsub[0]["contrast_rank"],
                                "method": method,
                                "runs": len(tsub),
                                "cert_rate": round(sum(1 for r in tsub if r["certified"]) / len(tsub), 4),
                                "restricted_mean": round(float(np.mean(t_st)), 1),
                                "med_all": round(float(np.median(t_st)), 1),
                                "false_certs": sum(1 for r in tsub if r["false_cert"]),
                                "mean_root_regret": round(float(np.mean([r["true_regret"] for r in tsub])), 6),
                                "joint_contrast_cov": (
                                    round(
                                        sum(1 for r in tsub if r["joint_contrast_covered"]) / len(tsub), 4
                                    )
                                    if tsub[0]["joint_contrast_covered"] is not None
                                    else ""
                                ),
                            }
                        )

    with (dest / "v14_protein_credible_summary.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)

    if template_rows:
        with (dest / "v14_protein_credible_per_template.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(template_rows[0].keys()))
            w.writeheader()
            w.writerows(template_rows)

    print("\n=== v14 Proper Joint Credible-Ellipsoid & Direct Posterior-Risk Protein Study ===")
    for land in ("gb1", "trpb"):
        print(f"\n================ {land.upper()} ================")
        for cond in ALL_CONDITIONS:
            sub_s = [r for r in summary_rows if r["condition"] == cond and r["landscape"] == land]
            if not sub_s:
                continue
            print(f"  --- {cond} (n={sub_s[0]['runs']}, r_avg={sub_s[0]['mean_contrast_rank']}, beta={sub_s[0]['mean_beta_at_stop']}) ---")
            for r in sub_s:
                print(
                    f"    {r['method']:16s} | cert={100*r['cert_rate']:5.1f}% | "
                    f"RM={r['restricted_mean']:8.1f} [{r['rm_ci95_lo']:7.1f},{r['rm_ci95_hi']:7.1f}] | "
                    f"med_ok={str(r['med_certified']):>7s} | "
                    f"KG/m={str(r['speedup_kg_over_method']):>5s}x [{str(r['speedup_kg_over_method_ci95_lo']):>5s},{str(r['speedup_kg_over_method_ci95_hi']):>5s}] | "
                    f"err={r['false_certs']:2d}/{r['runs']} max_r={r['max_root_regret_all']:.4f} | "
                    f"jcov={str(r['joint_contrast_cov']):>6s} pw={str(r['pointwise_all_cov']):>6s} rcov={r['regret_bound_cov_all']:.4f}"
                )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true", help="Fast smoke run (2 templates x 2 seeds, cap=2500)")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(56, max(1, (os.cpu_count() or 8) - 4)))
    ap.add_argument("--cap", type=int, default=CAP_ASSAYS)
    ap.add_argument("--mc-draws", type=int, default=MC_POSTRISK_DRAWS)
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    if args.smoke:
        gb1_tmpls = GB1_TEMPLATES[:2]
        trpb_tmpls = TRPB_TEMPLATES[:2]
        gb1_seeds = GB1_SEEDS[:2]
        trpb_seeds = TRPB_SEEDS[:2]
        cap = min(args.cap, 2500)
        mc_draws = min(args.mc_draws, 1024)
    else:
        gb1_tmpls = GB1_TEMPLATES
        trpb_tmpls = TRPB_TEMPLATES
        gb1_seeds = GB1_SEEDS
        trpb_seeds = TRPB_SEEDS
        cap = int(args.cap)
        mc_draws = int(args.mc_draws)

    # Order longest streams first (`kg_all` -> `cd_matched` -> `frozen_and_df` -> `gpos_matched`)
    # so multiprocess pool finishes cleanly with near-zero tail stragglers.
    instances: list[tuple[str, str, int]] = []
    for seq in gb1_tmpls:
        for seed in gb1_seeds:
            instances.append(("gb1", seq, seed))
    for seq in trpb_tmpls:
        for seed in trpb_seeds:
            instances.append(("trpb", seq, seed))

    tasks: list[tuple[str, str, int, str, int, int]] = []
    for stream in ("kg_all", "cd_matched", "frozen_and_df", "gpos_matched"):
        for land, seq, seed in instances:
            tasks.append((land, seq, seed, stream, cap, mc_draws))

    print(
        f"[v14 Protein Credible Ellipsoid] Launching {len(tasks)} stream tasks across {len(instances)} paired campaigns "
        f"(GB1={len(gb1_tmpls)}x{len(gb1_seeds)}, TrpB={len(trpb_tmpls)}x{len(trpb_seeds)}, "
        f"eps={EPS}, delta={DELTA}, cap={cap}, mc_draws={mc_draws}) on {args.workers} workers...",
        flush=True,
    )

    all_rows: list[dict] = []
    ctx = mp.get_context("spawn")
    done_cnt = 0
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for chunk in ex.map(_stream_worker, tasks):
            all_rows.extend(chunk)
            done_cnt += 1
            if done_cnt % 160 == 0 or done_cnt == len(tasks):
                print(
                    f"  [v14 progress] {done_cnt}/{len(tasks)} stream tasks complete "
                    f"({len(all_rows)} rows, elapsed {time.perf_counter() - t0:.1f}s)",
                    flush=True,
                )

    # Deterministic canonical sort order
    all_rows.sort(key=lambda r: (r["condition"], r["landscape"], r["start_seq"], r["seed"], r["method"]))
    p_runs = out_dir / "v14_protein_credible_runs.jsonl"
    p_runs.write_text("\n".join(json.dumps(r) for r in all_rows) + "\n")
    summarize(out_dir)

    artifacts = [
        "v14_protein_credible_runs.jsonl",
        "v14_protein_credible_summary.csv",
        "v14_protein_credible_per_template.csv",
    ]
    manifest = {
        "experiment": "v14_protein_credible_ellipsoid",
        "smoke": bool(args.smoke),
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "cap": cap,
        "delta": DELTA,
        "eps": EPS,
        "mc_draws": mc_draws,
        "mc_eta": MC_POSTRISK_ETA,
        "mc_delta_post": MC_POSTRISK_DELTA_POST,
        "n_gb1_instances": len(gb1_tmpls) * len(gb1_seeds),
        "n_trpb_instances": len(trpb_tmpls) * len(trpb_seeds),
        "total_condition_method_rows": len(all_rows),
        "conditions": list(ALL_CONDITIONS),
        "python": platform.python_version(),
        "files": {
            nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size}
            for nm in artifacts
            if (out_dir / nm).is_file()
        },
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v14 Protein Credible Ellipsoid] Complete ({len(all_rows)} rows) in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
