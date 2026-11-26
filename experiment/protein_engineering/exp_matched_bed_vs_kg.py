"""Experiment v13: Matched Bayesian Experimental Design vs. Correlated Knowledge Gradient
on Real Epistatic Protein Landscapes (GB1 and TmTrpB).

Directly tests whether the synthetic matched-model acquisition advantage of CD-Joint over
Correlated Knowledge Gradient (KG) and standard BO transfers to measured combinatorial
protein-fitness landscapes under two cleanly separated stopping regimes:

  - Datasets (410 paired campaign instances per method):
      * GB1 (Wu et al., eLife 2016): 10 templates x 20 seeds = 200 paired instances
        (`max_edits=3`, `panel='panel5'`, `noise_model='calibrated'`, M in [393, 540], K in [13, 19]).
      * TmTrpB (Johnston et al., PNAS 2024): 21 templates x 10 seeds = 210 paired instances
        (`max_edits=3`, `panel='panel5'`, `noise_model='low_var_uniform'`, M in [579, 670], K in [19, 20]).
  - Fixed shared GP prior, kernel, and observation model across ALL methods (zero online refitting):
      * Kernel: `protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)`.
      * GB1: `prior_mean=0.28`, `obs_std=0.16`.
      * TmTrpB: `prior_mean=0.30`, `obs_std=0.08 / sqrt(3)`.
  - Identical intrinsic noisy-observation tape per `(template, seed)` across all policies.
  - Confidence & accuracies: `delta = 0.05`, primary `eps = 0.015`, sensitivity `eps = 0.010`,
    budget cap `25,000` simulated assays per campaign.

Methods compared under the shared fixed GP model:
  1. `gp_ucb`            : GP-UCB (optimization-directed baseline)
  2. `kg`                : Exact Analytical Correlated Knowledge Gradient (Frazier-Powell-Dayanik 2009)
  3. `gp_root_info_gp`   : Existing graph-aware witness policy (GP-only variant for pure Regime A/B)
  4. `gp_os`             : Correlated GP-OS (Optimistic Separation on shared GP intervals)
  5. `cd_joint`          : Safeguarded Contrast-Directed Joint Acquisition (principal proposed method)

Two stopping regimes (plus DF-coupled / DF-confirmed references for Regime B):
  - Regime A (`bayes_ellipsoid`): Identical shared GP posterior and joint credible-ellipsoid root
    certificate (`beta_t = sqrt(2 log(4 M t^2 / delta))`, exact same check schedule & conic oracle).
    Reports actual root regret, false-certificate rate, and pointwise GP coverage to expose any
    kernel misspecification transparently.
  - Regime B (`df_emp_bernstein`): Identical formal bounded-observation Empirical Bernstein
    confidence sequences (`DualWitnessCovers(delta=0.05, schedule='emp_bernstein')`) and exact
    shared-support root certificate. Evaluates:
      (i)  All 5 unmodified GP acquisitions (`gp_ucb`, `kg`, `gp_root_info_gp`, `gp_os`, `cd_joint`),
      (ii) Existing DF-coupled `gp_root_info_df` (v6 canonical, clipped GP-UCB + DF outside witnesses),
      (iii) Pure distribution-free `df_os` (zero-GP Optimistic Separation lower-envelope reference),
      (iv) Two-phase DF-confirmed `cd_joint_df_confirm` and `kg_df_confirm` (Phase 1 Bayesian
           acquisition until Regime A certifies -> Phase 2 identical DF-OS confirmation).
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

from joint_root_cert import DualWitnessCovers, HybridWitnessDAGLUCBSession
from joint_root_cert.benchmarks import protein_sequence_kernel
from joint_root_cert.benchmarks import (
    GB1MutationCampaignProblem,
    TrpBMutationCampaignProblem,
    real_world_problem_diagnostics,
)
from joint_root_cert import JointEllipsoidCertifier, SupportStructure
from joint_root_cert import (
    SharedGaussianPosterior,
    correlated_kg_log_scores,
)
from experiment.protein_engineering.exp_real_world_applications import GB1_TEMPLATES
from experiment.protein_engineering.exp_real_world_validation import TRPB_TEMPLATES


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/v13_protein_bed_vs_kg"

DELTA = 0.05
PRIMARY_EPS = 0.015
SENS_EPS = 0.010
EPS_LIST: tuple[float, ...] = (PRIMARY_EPS, SENS_EPS)
CAP_ASSAYS = 25000

GB1_SEEDS: tuple[int, ...] = tuple(801000 + i for i in range(1, 21))   # 10 x 20 = 200
TRPB_SEEDS: tuple[int, ...] = tuple(802000 + i for i in range(1, 11))  # 21 x 10 = 210

# Core 5 matched GP-guided methods evaluated in Regime A and unmodified Regime B
MATCHED_GP_METHODS: tuple[str, ...] = (
    "gp_ucb",
    "kg",
    "gp_root_info_gp",
    "gp_os",
    "cd_joint",
)

# Full ordered method list for Regime B summary (pure GP + DF-coupled/confirmed references)
REGIME_B_METHODS: tuple[str, ...] = (
    "gp_ucb",
    "kg",
    "gp_root_info_gp",
    "gp_os",
    "cd_joint",
    "gp_root_info_df",
    "cd_joint_df_confirm",
    "gp_os_df_confirm",
    "kg_df_confirm",
    "df_os",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _cp_upper_95(k: int, n: int) -> float:
    if n <= 0 or k >= n:
        return 1.0
    return float(beta_dist.ppf(0.95, k + 1, n - k))


def _bootstrap_mean_ci(
    vals: np.ndarray,
    n_boot: int = 10_000,
    seed: int = 20261123,
) -> tuple[float, float, float]:
    n = len(vals)
    pt = float(np.mean(vals))
    if n <= 1:
        return (pt, pt, pt)
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, n, size=(n_boot, n))
    boot = np.mean(vals[idx], axis=1)
    lo, hi = np.percentile(boot, [2.5, 97.5])
    return (pt, float(lo), float(hi))


def _paired_bootstrap_ratio_ci(
    num_vals: np.ndarray,
    den_vals: np.ndarray,
    n_boot: int = 10_000,
    seed: int = 20261124,
) -> tuple[float, float, float]:
    """Paired bootstrap 95% CI for ratio of restricted means `mean(num) / mean(den)`."""
    n = len(num_vals)
    pt = float(np.mean(num_vals) / max(1e-12, float(np.mean(den_vals))))
    if n <= 1:
        return (pt, pt, pt)
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, n, size=(n_boot, n))
    num_b = np.mean(num_vals[idx], axis=1)
    den_b = np.maximum(1e-12, np.mean(den_vals[idx], axis=1))
    lo, hi = np.percentile(num_b / den_b, [2.5, 97.5])
    return (pt, float(lo), float(hi))


def _bayes_check_schedule(step: int, cap: int) -> bool:
    """Identical deterministic Regime A certificate check schedule across all policies."""
    if step == cap or step <= 50:
        return True
    if step <= 2000:
        return (step % 10) == 0
    return (step % 20) == 0


def _nominal_gp_beta(m: int, step: int, delta: float) -> float:
    """Exact time-uniform simultaneous Gaussian GP radius used across v7/v8/v11."""
    t_eff = max(1, int(step))
    return math.sqrt(2.0 * math.log(4.0 * float(m) * float(t_eff * t_eff) / float(delta)))


def _ucb_kappa(m: int, step: int, delta: float) -> float:
    """Standard Srinivas et al. (2012) finite-domain GP-UCB exploration schedule."""
    t_eff = max(1, int(step))
    return math.sqrt(2.0 * math.log(max(2.0, float(m) * (math.pi ** 2) * float(t_eff * t_eff) / (6.0 * float(delta)))))


def _check_bayes_ellipsoid(
    certifier: JointEllipsoidCertifier,
    ss: SupportStructure,
    means: np.ndarray,
    sigma_mat: np.ndarray,
    stds: np.ndarray,
    beta: float,
    eps: float,
) -> tuple[bool, int, float]:
    """Exact, policy-identical Regime A joint credible-ellipsoid root certificate check.

    Uses a 100%-sound center-mean lower-bound filter (`max_{z notin S(a)} m_z - max_{y in S(a)} m_y > eps`
    guarantees `R_t(a) > eps`), then invokes `JointEllipsoidCertifier.certify_action_gp` on every
    surviving candidate action ordered deterministically by enclosing-box approximate regret.
    """
    u_ell = means + beta * stds
    cands: list[tuple[float, int]] = []
    for a in range(ss.k):
        sup = ss.supports[a]
        comp = ss.complements[a]
        if len(comp) == 0:
            return True, a, 0.0
        m_in = float(np.max(means[sup]))
        m_out = float(np.max(means[comp]))
        # 100% sound lower bound at ellipsoid center f = m_t in E_t
        if m_out - m_in > eps:
            continue
        u_out = float(np.max(u_ell[comp]))
        cands.append((max(0.0, u_out - m_in), a))

    if not cands:
        best_emp = int(np.argmax([float(np.max(means[sup])) for sup in ss.supports]))
        return False, best_emp, math.inf

    cands.sort(key=lambda pair: (pair[0], pair[1]))
    best_a = cands[0][1]
    best_reg = math.inf
    prev_eps = certifier.epsilon
    certifier.epsilon = float(eps)
    try:
        for _, a in cands:
            ca = certifier.certify_action_gp(
                action=a,
                means=means,
                sigma_mat=sigma_mat,
                beta=beta,
                stop_if_above_eps=True,
            )
            if ca.regret <= eps:
                return True, int(a), float(ca.regret)
            if (ca.regret, a) < (best_reg, best_a):
                best_reg = float(ca.regret)
                best_a = int(a)
    finally:
        certifier.epsilon = prev_eps
    return False, int(best_a), float(best_reg)


def _pointwise_coverage_diag(
    means: np.ndarray,
    stds: np.ndarray,
    beta: float,
    true_means: np.ndarray,
) -> tuple[bool, float, float]:
    z_ratios = np.abs(means - true_means) / np.maximum(1e-12, beta * stds)
    max_z = float(np.max(z_ratios))
    frac = float(np.mean(z_ratios <= 1.0 + 1e-12))
    return bool(max_z <= 1.0 + 1e-12), max_z, frac


def _select_gp_arm(
    policy: str,
    step: int,
    ss: SupportStructure,
    leaf_to_actions: list[list[int]],
    post: SharedGaussianPosterior,
    certifier: JointEllipsoidCertifier,
    eps: float,
    delta: float,
) -> int:
    """Select next terminal index `0..M-1` strictly from the shared fixed GP posterior."""
    means = post.mean
    stds = post.stds()
    m = ss.m
    beta_nom = _nominal_gp_beta(m, step, delta)
    u_ell = means + beta_nom * stds
    l_ell = means - beta_nom * stds

    if policy == "gp_ucb":
        kappa = _ucb_kappa(m, step, delta)
        return int(np.argmax(means + kappa * stds))

    if policy == "kg":
        scores = correlated_kg_log_scores(means, post.sigma_mat, post.obs_var, ss.costs, use_cpp=True)
        return int(np.argmax(scores))

    if policy == "gp_root_info_gp":
        # Existing v7 GP witness policy: optimistic peak w*, containing action minimizing u_out,
        # wider of {w*, z_out}
        w_star = int(np.argmax(u_ell))
        best_sep = -math.inf
        b_t = leaf_to_actions[w_star][0]
        for a in leaf_to_actions[w_star]:
            comp = ss.complements[a]
            u_out = float(np.max(u_ell[comp])) if len(comp) else -math.inf
            sep = float(u_ell[w_star]) - u_out
            if sep > best_sep:
                best_sep = sep
                b_t = a
        comp_b = ss.complements[b_t]
        if len(comp_b) == 0:
            return w_star
        z_box = int(comp_b[int(np.argmax(u_ell[comp_b]))])
        return w_star if float(stds[w_star]) >= float(stds[z_box]) else z_box

    if policy == "gp_os":
        # Exact Optimistic Separation on shared GP intervals: b_t = argmax_a (U_t(a) - L_t^-(a))
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
        # Algorithm 1 / Eq. (9)-(10) Safeguarded Contrast-Directed Joint Acquisition.
        # On commuting protein DAGs where y_opt belongs to multiple root actions, selects the
        # containing action b_t by Optimistic Separation (u_ell[y_opt] - max_{z notin S(a)} l_ell[z])
        # so multi-answer ties favor the widest-margin containing commitment.
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
                beta=beta_nom,
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
            g = np.zeros(m, dtype=np.float64)
            g[z_t] = 1.0
            g[y_opt] = -1.0
        sg = post.sigma_mat @ g
        dv = (sg * sg) / (post.obs_var + np.maximum(1e-18, np.diag(post.sigma_mat)))
        return int(np.argmax(dv / ss.costs))

    raise ValueError(f"Unknown policy: {policy!r}")


def _run_df_confirmation_from_prefix(
    prob: GB1MutationCampaignProblem,
    ss: SupportStructure,
    seed: int,
    prefix_history: list[tuple[int, float]],
    eps: float,
    delta: float,
    cap: int,
    regrets: list[float],
    phase1_acq_s: float,
    phase1_total_s: float,
    landscape: str,
    start_seq: str,
    regime_tag: str,
    method_name: str,
) -> dict:
    """Replay Phase-1 GP prefix observations into fresh DF Empirical Bernstein monitor + paired
    oracle, then continue with identical O(log M) DF-OS witnesses until DF certifies or cap hits.
    """
    t0 = time.perf_counter()
    oracle = prob.oracle(seed)
    df_mon = DualWitnessCovers(prob.graph, delta=delta, schedule="emp_bernstein", layout="best", track_separation=True)
    distinct: set[int] = set()
    certified = False
    action = 0
    stop_step = cap

    for idx_step, (arm_idx, expected_r) in enumerate(prefix_history, start=1):
        leaf = ss.leaves[arm_idx]
        r = float(oracle.sample(leaf))
        # Exact paired intrinsic tape sanity check
        assert abs(r - expected_r) <= 1e-15, "Intrinsic observation tape mismatch!"
        distinct.add(arm_idx)
        df_mon.step(leaf, r)
        act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
        if reg_df <= eps:
            certified = True
            action = int(act_df)
            stop_step = idx_step
            break

    acq_p2_s = 0.0
    if not certified:
        ev = df_mon.evidence
        for step in range(len(prefix_history) + 1, cap + 1):
            ta = time.perf_counter()
            act_df, reg_df, _, _, p_leaf, q_leaf = df_mon.query_optimistic_separation()
            if reg_df <= eps:
                certified = True
                action = int(act_df)
                stop_step = step - 1
                break
            if q_leaf < 0:
                chosen_leaf = p_leaf
            else:
                w_p = float(ev.upper[p_leaf] - ev.lower[p_leaf])
                w_q = float(ev.upper[q_leaf] - ev.lower[q_leaf])
                chosen_leaf = p_leaf if (w_p, -p_leaf) >= (w_q, -q_leaf) else q_leaf
            acq_p2_s += time.perf_counter() - ta

            arm_idx = ss.leaf_to_idx[chosen_leaf]
            r = float(oracle.sample(chosen_leaf))
            distinct.add(arm_idx)
            df_mon.step(chosen_leaf, r)

        if not certified:
            act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
            action = int(act_df)
            if reg_df <= eps:
                certified = True
                stop_step = cap

    true_reg = float(regrets[action])
    p2_wall = time.perf_counter() - t0
    return {
        "unit_id": f"{landscape}_{start_seq}_{seed}",
        "landscape": landscape,
        "start_seq": start_seq,
        "template_regime": regime_tag,
        "seed": int(seed),
        "m_leaves": int(ss.m),
        "k_actions": int(ss.k),
        "stopping_regime": "df_emp_bernstein",
        "eps": float(eps),
        "method": method_name,
        "certified": bool(certified),
        "steps": int(stop_step),
        "action": int(action),
        "true_regret": round(true_reg, 6),
        "false_cert": bool(certified and true_reg > eps + 1e-12),
        "distinct_leaves": int(len(distinct)),
        "pointwise_all_covered": True,
        "pointwise_max_z_ratio": 0.0,
        "pointwise_frac_covered": 1.0,
        "acq_time_s": round(phase1_acq_s + acq_p2_s, 4),
        "cert_time_s": 0.0,
        "total_time_s": round(phase1_total_s + p2_wall, 4),
        "phase1_bayes_steps": int(len(prefix_history)),
    }


def run_single_instance_policy(
    prob: GB1MutationCampaignProblem,
    ss: SupportStructure,
    leaf_to_actions: list[list[int]],
    kernel: np.ndarray,
    prior_mean: float,
    obs_std: float,
    regrets: list[float],
    true_means_vec: np.ndarray,
    seed: int,
    policy: str,
    eps_targets: tuple[float, ...],
    cap: int,
    delta: float,
    landscape: str,
    start_seq: str,
    regime_tag: str,
    run_df_confirm: bool = False,
) -> list[dict]:
    """Run one matched GP-guided policy on a single `(template, seed)` instance.

    For policies whose acquisition rule is independent of `eps` and the stopping rule
    (`gp_ucb`, `kg`, `gp_root_info_gp`, `gp_os`), `eps_targets` may contain both `0.015` and
    `0.010` simultaneously in a single exact pass (bit-identical to separate runs). For
    `cd_joint`, whose safeguard depends on `0.5 * eps`, pass a 1-tuple `(eps,)` per call.
    """
    post = SharedGaussianPosterior(kernel, prior_mean, obs_std, delta=delta, beta_mode="posterior_credible")
    certifier = JointEllipsoidCertifier(ss, epsilon=eps_targets[0], solver="colgen_lazy", exact_linear_mean=False)
    df_mon = DualWitnessCovers(prob.graph, delta=delta, schedule="emp_bernstein", layout="best", track_separation=True)
    oracle = prob.oracle(seed)

    # Track exact stopping records per `(regime, eps)`
    bayes_rec: dict[float, dict | None] = {e: None for e in eps_targets}
    df_rec: dict[float, dict | None] = {e: None for e in eps_targets}
    bayes_prefix: dict[float, list[tuple[int, float]]] = {}
    history: list[tuple[int, float]] = []

    t_start = time.perf_counter()
    acq_s = 0.0
    cert_s = 0.0
    acq_eps = eps_targets[0]  # Only used by cd_joint (where len(eps_targets) == 1)

    for step in range(1, cap + 1):
        # 1. Check Regime B (DF Empirical Bernstein) on EVERY step
        if any(df_rec[e] is None for e in eps_targets):
            act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
            for e in eps_targets:
                if df_rec[e] is None and reg_df <= e:
                    tr = float(regrets[int(act_df)])
                    df_rec[e] = {
                        "certified": True,
                        "steps": int(step - 1),
                        "action": int(act_df),
                        "true_regret": round(tr, 6),
                        "false_cert": bool(tr > e + 1e-12),
                        "distinct_leaves": int(np.sum(post.arm_counts > 0)),
                        "pointwise_all_covered": True,
                        "pointwise_max_z_ratio": 0.0,
                        "pointwise_frac_covered": 1.0,
                        "acq_time_s": round(acq_s, 4),
                        "cert_time_s": 0.0,
                        "total_time_s": round(time.perf_counter() - t_start, 4),
                    }

        # 2. Check Regime A (Matched Bayesian joint ellipsoid) on identical schedule
        if any(bayes_rec[e] is None for e in eps_targets) and _bayes_check_schedule(step - 1 if step > 1 else 0, cap):
            # Evaluate at current completed pull count `t_done = step - 1` (skip t=0 before 1st pull unless trivial)
            t_done = step - 1
            if t_done > 0:
                tc0 = time.perf_counter()
                beta_nom = _nominal_gp_beta(ss.m, t_done, delta)
                means = post.mean
                stds = post.stds()
                for e in sorted(eps_targets, reverse=True):
                    if bayes_rec[e] is not None:
                        continue
                    ok, act_b, _ = _check_bayes_ellipsoid(certifier, ss, means, post.sigma_mat, stds, beta_nom, e)
                    if ok:
                        tr = float(regrets[act_b])
                        pw_all, pw_maxz, pw_frac = _pointwise_coverage_diag(means, stds, beta_nom, true_means_vec)
                        cert_s_now = cert_s + (time.perf_counter() - tc0)
                        bayes_rec[e] = {
                            "certified": True,
                            "steps": int(t_done),
                            "action": int(act_b),
                            "true_regret": round(tr, 6),
                            "false_cert": bool(tr > e + 1e-12),
                            "distinct_leaves": int(np.sum(post.arm_counts > 0)),
                            "pointwise_all_covered": pw_all,
                            "pointwise_max_z_ratio": round(pw_maxz, 4),
                            "pointwise_frac_covered": round(pw_frac, 4),
                            "acq_time_s": round(acq_s, 4),
                            "cert_time_s": round(cert_s_now, 4),
                            "total_time_s": round(time.perf_counter() - t_start, 4),
                        }
                        if run_df_confirm:
                            bayes_prefix[e] = list(history)
                cert_s += time.perf_counter() - tc0

        # Early exit if every target `(regime, eps)` has certified
        if all(bayes_rec[e] is not None for e in eps_targets) and all(df_rec[e] is not None for e in eps_targets):
            break

        # 3. Acquire next evaluation strictly from the shared GP posterior
        ta = time.perf_counter()
        arm = _select_gp_arm(policy, step, ss, leaf_to_actions, post, certifier, acq_eps, delta)
        acq_s += time.perf_counter() - ta

        leaf = ss.leaves[arm]
        r = float(oracle.sample(leaf))
        post.observe(arm, r)
        df_mon.step(leaf, r)
        if run_df_confirm:
            history.append((arm, r))

    # Final check at `t_done = cap` for any uncertified target
    if any(df_rec[e] is None for e in eps_targets):
        act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
        for e in eps_targets:
            if df_rec[e] is None:
                ok_df = bool(reg_df <= e)
                tr = float(regrets[int(act_df)])
                df_rec[e] = {
                    "certified": ok_df,
                    "steps": int(cap),
                    "action": int(act_df),
                    "true_regret": round(tr, 6),
                    "false_cert": bool(ok_df and tr > e + 1e-12),
                    "distinct_leaves": int(np.sum(post.arm_counts > 0)),
                    "pointwise_all_covered": True,
                    "pointwise_max_z_ratio": 0.0,
                    "pointwise_frac_covered": 1.0,
                    "acq_time_s": round(acq_s, 4),
                    "cert_time_s": 0.0,
                    "total_time_s": round(time.perf_counter() - t_start, 4),
                }

    if any(bayes_rec[e] is None for e in eps_targets):
        tc0 = time.perf_counter()
        beta_nom = _nominal_gp_beta(ss.m, cap, delta)
        means = post.mean
        stds = post.stds()
        emp_a = int(np.argmax([float(np.max(means[sup])) for sup in ss.supports]))
        pw_all, pw_maxz, pw_frac = _pointwise_coverage_diag(means, stds, beta_nom, true_means_vec)
        for e in sorted(eps_targets, reverse=True):
            if bayes_rec[e] is not None:
                continue
            ok, act_b, _ = _check_bayes_ellipsoid(certifier, ss, means, post.sigma_mat, stds, beta_nom, e)
            rec_a = int(act_b) if ok else emp_a
            tr = float(regrets[rec_a])
            bayes_rec[e] = {
                "certified": bool(ok),
                "steps": int(cap),
                "action": rec_a,
                "true_regret": round(tr, 6),
                "false_cert": bool(ok and tr > e + 1e-12),
                "distinct_leaves": int(np.sum(post.arm_counts > 0)),
                "pointwise_all_covered": pw_all,
                "pointwise_max_z_ratio": round(pw_maxz, 4),
                "pointwise_frac_covered": round(pw_frac, 4),
                "acq_time_s": round(acq_s, 4),
                "cert_time_s": round(cert_s + (time.perf_counter() - tc0), 4),
                "total_time_s": round(time.perf_counter() - t_start, 4),
            }
            if run_df_confirm:
                bayes_prefix[e] = list(history)
        cert_s += time.perf_counter() - tc0

    rows: list[dict] = []
    base = {
        "unit_id": f"{landscape}_{start_seq}_{seed}",
        "landscape": landscape,
        "start_seq": start_seq,
        "template_regime": regime_tag,
        "seed": int(seed),
        "m_leaves": int(ss.m),
        "k_actions": int(ss.k),
    }
    for e in eps_targets:
        rows.append({**base, "stopping_regime": "bayes_ellipsoid", "eps": float(e), "method": policy, **bayes_rec[e]})
        rows.append({**base, "stopping_regime": "df_emp_bernstein", "eps": float(e), "method": policy, **df_rec[e]})
        if run_df_confirm:
            conf_name = f"{policy}_df_confirm"
            rows.append(
                _run_df_confirmation_from_prefix(
                    prob=prob,
                    ss=ss,
                    seed=seed,
                    prefix_history=bayes_prefix[e],
                    eps=e,
                    delta=delta,
                    cap=cap,
                    regrets=regrets,
                    phase1_acq_s=float(bayes_rec[e]["acq_time_s"]),
                    phase1_total_s=float(bayes_rec[e]["total_time_s"]),
                    landscape=landscape,
                    start_seq=start_seq,
                    regime_tag=regime_tag,
                    method_name=conf_name,
                )
            )
    return rows


def run_gp_root_info_df_and_df_os(
    prob: GB1MutationCampaignProblem,
    ss: SupportStructure,
    kernel: np.ndarray,
    prior_mean: float,
    obs_std: float,
    regrets: list[float],
    seed: int,
    eps_targets: tuple[float, ...],
    cap: int,
    delta: float,
    landscape: str,
    start_seq: str,
    regime_tag: str,
) -> list[dict]:
    """Run existing DF-coupled `GP-Root-Info` (v6 canonical) and pure `DF-OS` under Regime B."""
    rows: list[dict] = []
    base = {
        "unit_id": f"{landscape}_{start_seq}_{seed}",
        "landscape": landscape,
        "start_seq": start_seq,
        "template_regime": regime_tag,
        "seed": int(seed),
        "m_leaves": int(ss.m),
        "k_actions": int(ss.k),
        "stopping_regime": "df_emp_bernstein",
    }

    # 1. Pure DF-OS (`Optimistic-Separation` on Empirical Bernstein, zero GP) — single pass for all eps!
    t0 = time.perf_counter()
    df_mon = DualWitnessCovers(prob.graph, delta=delta, schedule="emp_bernstein", layout="best", track_separation=True)
    oracle = prob.oracle(seed)
    ev = df_mon.evidence
    distinct: set[int] = set()
    os_rec: dict[float, dict | None] = {e: None for e in eps_targets}
    acq_s = 0.0
    for step in range(1, cap + 1):
        act_df, reg_df, _, _, p_leaf, q_leaf = df_mon.query_optimistic_separation()
        for e in eps_targets:
            if os_rec[e] is None and reg_df <= e:
                tr = float(regrets[int(act_df)])
                os_rec[e] = {
                    "certified": True,
                    "steps": int(step - 1),
                    "action": int(act_df),
                    "true_regret": round(tr, 6),
                    "false_cert": bool(tr > e + 1e-12),
                    "distinct_leaves": int(len(distinct)),
                    "pointwise_all_covered": True,
                    "pointwise_max_z_ratio": 0.0,
                    "pointwise_frac_covered": 1.0,
                    "acq_time_s": round(acq_s, 4),
                    "cert_time_s": 0.0,
                    "total_time_s": round(time.perf_counter() - t0, 4),
                }
        if all(os_rec[e] is not None for e in eps_targets):
            break
        ta = time.perf_counter()
        if q_leaf < 0:
            chosen_leaf = p_leaf
        else:
            w_p = float(ev.upper[p_leaf] - ev.lower[p_leaf])
            w_q = float(ev.upper[q_leaf] - ev.lower[q_leaf])
            chosen_leaf = p_leaf if (w_p, -p_leaf) >= (w_q, -q_leaf) else q_leaf
        acq_s += time.perf_counter() - ta
        r = float(oracle.sample(chosen_leaf))
        distinct.add(ss.leaf_to_idx[chosen_leaf])
        df_mon.step(chosen_leaf, r)

    act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
    for e in eps_targets:
        if os_rec[e] is None:
            ok = bool(reg_df <= e)
            tr = float(regrets[int(act_df)])
            os_rec[e] = {
                "certified": ok,
                "steps": int(cap),
                "action": int(act_df),
                "true_regret": round(tr, 6),
                "false_cert": bool(ok and tr > e + 1e-12),
                "distinct_leaves": int(len(distinct)),
                "pointwise_all_covered": True,
                "pointwise_max_z_ratio": 0.0,
                "pointwise_frac_covered": 1.0,
                "acq_time_s": round(acq_s, 4),
                "cert_time_s": 0.0,
                "total_time_s": round(time.perf_counter() - t0, 4),
            }
        rows.append({**base, "eps": float(e), "method": "df_os", **os_rec[e]})

    # 2. Existing DF-coupled `GP-Root-Info` (v6 canonical, uses `0.5 * eps` safeguard -> per eps)
    for e in eps_targets:
        t0 = time.perf_counter()
        post = SharedGaussianPosterior(kernel, prior_mean, obs_std, delta=delta, beta_mode="posterior_credible")
        df_mon = DualWitnessCovers(
            prob.graph, delta=delta, schedule="emp_bernstein", layout="best", track_separation=True
        )
        oracle = prob.oracle(seed)
        ev = df_mon.evidence
        acq_s = 0.0
        certified = False
        action = 0
        stop_step = cap
        for step in range(1, cap + 1):
            act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
            if reg_df <= e:
                certified = True
                action = int(act_df)
                stop_step = int(step - 1)
                break
            ta = time.perf_counter()
            kappa = _ucb_kappa(ss.m, step, delta)
            gp_ucb = post.mean + kappa * post.stds()
            freq_hi = np.array([ev.upper[z] for z in ss.leaves], dtype=np.float64)
            clipped = np.minimum(freq_hi, gp_ucb)
            best_b = 0
            best_sep = -math.inf
            best_in = 0
            for a, sup in enumerate(ss.supports):
                sub = clipped[sup]
                lp = int(np.argmax(sub))
                nlh = df_mon.neg_low_heaps[a]
                l_out = float(nlh.keys[nlh.top]) if nlh is not None else -math.inf
                sep_a = float(sub[lp]) - l_out
                if sep_a > best_sep:
                    best_sep = sep_a
                    best_b = a
                    best_in = int(sup[lp])
            z_in = ss.leaves[best_in]
            w_in = float(ev.upper[z_in] - ev.lower[z_in])
            if w_in <= 0.5 * e:
                phh = df_mon.pos_high_heaps[best_b]
                z_in = int(phh.leaves[phh.top])
                w_in = float(ev.upper[z_in] - ev.lower[z_in])
            nh = df_mon.neg_heaps[best_b]
            if nh is None:
                chosen_leaf = z_in
            else:
                z_out = int(nh.leaves[nh.top])
                w_out = float(ev.upper[z_out] - ev.lower[z_out])
                n_in = float(oracle.obs[z_in])
                n_out = float(oracle.obs[z_out])
                dw_in = w_in * (1.0 - math.sqrt((n_in + 1.0) / (n_in + 2.0)))
                dw_out = w_out * (1.0 - math.sqrt((n_out + 1.0) / (n_out + 2.0)))
                chosen_leaf = z_in if (dw_in, w_in, -z_in) >= (dw_out, w_out, -z_out) else z_out
            acq_s += time.perf_counter() - ta

            arm_idx = ss.leaf_to_idx[chosen_leaf]
            r = float(oracle.sample(chosen_leaf))
            post.observe(arm_idx, r)
            df_mon.step(chosen_leaf, r)

        if not certified:
            act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
            action = int(act_df)
            if reg_df <= e:
                certified = True
                stop_step = int(cap)
        tr = float(regrets[action])
        rows.append(
            {
                **base,
                "eps": float(e),
                "method": "gp_root_info_df",
                "certified": bool(certified),
                "steps": int(stop_step),
                "action": int(action),
                "true_regret": round(tr, 6),
                "false_cert": bool(certified and tr > e + 1e-12),
                "distinct_leaves": int(np.sum(post.arm_counts > 0)),
                "pointwise_all_covered": True,
                "pointwise_max_z_ratio": 0.0,
                "pointwise_frac_covered": 1.0,
                "acq_time_s": round(acq_s, 4),
                "cert_time_s": 0.0,
                "total_time_s": round(time.perf_counter() - t0, 4),
            }
        )
    return rows


def _instance_worker(task: tuple[str, str, int, tuple[float, ...], int]) -> list[dict]:
    landscape, start_seq, seed, eps_targets, cap = task
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

    leaf_to_actions: list[list[int]] = [[] for _ in range(ss.m)]
    for a, sup in enumerate(ss.supports):
        for idx in sup:
            leaf_to_actions[int(idx)].append(a)

    rows: list[dict] = []
    # 1. Eps-independent GP policies (single pass covers both regimes and all eps!)
    for pol in ("gp_ucb", "kg", "gp_root_info_gp", "gp_os"):
        rows.extend(
            run_single_instance_policy(
                prob=prob,
                ss=ss,
                leaf_to_actions=leaf_to_actions,
                kernel=kernel,
                prior_mean=prior_m,
                obs_std=obs_s,
                regrets=regrets,
                true_means_vec=true_means_vec,
                seed=seed,
                policy=pol,
                eps_targets=eps_targets,
                cap=cap,
                delta=DELTA,
                landscape=landscape,
                start_seq=start_seq,
                regime_tag=regime_tag,
                run_df_confirm=(pol in ("kg", "gp_os")),
            )
        )
    # 2. CD-Joint (safeguard depends on 0.5 * eps -> separate exact pass per eps)
    for e in eps_targets:
        rows.extend(
            run_single_instance_policy(
                prob=prob,
                ss=ss,
                leaf_to_actions=leaf_to_actions,
                kernel=kernel,
                prior_mean=prior_m,
                obs_std=obs_s,
                regrets=regrets,
                true_means_vec=true_means_vec,
                seed=seed,
                policy="cd_joint",
                eps_targets=(e,),
                cap=cap,
                delta=DELTA,
                landscape=landscape,
                start_seq=start_seq,
                regime_tag=regime_tag,
                run_df_confirm=True,
            )
        )
    # 3. DF-coupled GP-Root-Info (v6 canonical) and pure DF-OS under Regime B
    rows.extend(
        run_gp_root_info_df_and_df_os(
            prob=prob,
            ss=ss,
            kernel=kernel,
            prior_mean=prior_m,
            obs_std=obs_s,
            regrets=regrets,
            seed=seed,
            eps_targets=eps_targets,
            cap=cap,
            delta=DELTA,
            landscape=landscape,
            start_seq=start_seq,
            regime_tag=regime_tag,
        )
    )
    return rows


def summarize(dest: Path) -> None:
    p_runs = dest / "v13_protein_runs.jsonl"
    runs = [json.loads(line) for line in p_runs.read_text().splitlines() if line.strip()]
    eps_vals = sorted(set(float(r["eps"]) for r in runs), reverse=True)

    summary_rows: list[dict] = []
    template_rows: list[dict] = []

    for eps in eps_vals:
        for regime in ("bayes_ellipsoid", "df_emp_bernstein"):
            methods = MATCHED_GP_METHODS if regime == "bayes_ellipsoid" else REGIME_B_METHODS
            for land in ("gb1", "trpb"):
                cohort = [
                    r for r in runs
                    if r["landscape"] == land and r["stopping_regime"] == regime and abs(float(r["eps"]) - eps) < 1e-9
                ]
                if not cohort:
                    continue
                kg_map = {r["unit_id"]: r for r in cohort if r["method"] == "kg"}
                cd_map = {r["unit_id"]: r for r in cohort if r["method"] == "cd_joint"}
                df_os_map = {r["unit_id"]: r for r in cohort if r["method"] == "df_os"}

                for m_idx, method in enumerate(methods):
                    sub = [r for r in cohort if r["method"] == method]
                    if not sub:
                        continue
                    n = len(sub)
                    steps_arr = np.array([float(r["steps"]) for r in sub], dtype=np.float64)
                    rm_pt, rm_lo, rm_hi = _bootstrap_mean_ci(steps_arr, seed=13000 + m_idx)
                    cert_sub = [r for r in sub if r["certified"]]
                    n_cert = len(cert_sub)
                    n_err = sum(1 for r in sub if r["false_cert"])
                    all_regs = np.array([float(r["true_regret"]) for r in sub], dtype=np.float64)
                    cert_regs = np.array([float(r["true_regret"]) for r in cert_sub], dtype=np.float64) if cert_sub else np.zeros(0)
                    succ_med = float(np.median([float(r["steps"]) for r in cert_sub])) if cert_sub else float("nan")
                    all_med = float(np.median(steps_arr))
                    q25 = float(np.percentile(steps_arr, 25))
                    q75 = float(np.percentile(steps_arr, 75))
                    pw_cov = (
                        sum(1 for r in cert_sub if r["pointwise_all_covered"]) / len(cert_sub)
                        if cert_sub
                        else 1.0
                    )
                    acq_s_arr = np.array([float(r["acq_time_s"]) for r in sub], dtype=np.float64)
                    tot_s_arr = np.array([float(r["total_time_s"]) for r in sub], dtype=np.float64)
                    ms_per_step = 1000.0 * float(np.sum(acq_s_arr)) / max(1.0, float(np.sum(steps_arr)))

                    # Paired ratios against KG (`method / kg` and `kg / method`) and against CD-Joint
                    m_map = {r["unit_id"]: r for r in sub}
                    uids_kg = sorted(u for u in m_map if u in kg_map)
                    if uids_kg:
                        m_st = np.array([float(m_map[u]["steps"]) for u in uids_kg], dtype=np.float64)
                        k_st = np.array([float(kg_map[u]["steps"]) for u in uids_kg], dtype=np.float64)
                        r_over_kg, r_over_kg_lo, r_over_kg_hi = _paired_bootstrap_ratio_ci(m_st, k_st, seed=13100 + m_idx)
                        kg_over_m, kg_over_m_lo, kg_over_m_hi = _paired_bootstrap_ratio_ci(k_st, m_st, seed=13200 + m_idx)
                    else:
                        r_over_kg = r_over_kg_lo = r_over_kg_hi = float("nan")
                        kg_over_m = kg_over_m_lo = kg_over_m_hi = float("nan")

                    uids_cd = sorted(u for u in m_map if u in cd_map)
                    if uids_cd:
                        m_st_c = np.array([float(m_map[u]["steps"]) for u in uids_cd], dtype=np.float64)
                        c_st = np.array([float(cd_map[u]["steps"]) for u in uids_cd], dtype=np.float64)
                        m_over_cd, m_over_cd_lo, m_over_cd_hi = _paired_bootstrap_ratio_ci(m_st_c, c_st, seed=13300 + m_idx)
                    else:
                        m_over_cd = m_over_cd_lo = m_over_cd_hi = float("nan")

                    uids_os = sorted(u for u in m_map if u in df_os_map)
                    if uids_os and regime == "df_emp_bernstein":
                        m_st_o = np.array([float(m_map[u]["steps"]) for u in uids_os], dtype=np.float64)
                        o_st = np.array([float(df_os_map[u]["steps"]) for u in uids_os], dtype=np.float64)
                        os_over_m, os_over_m_lo, os_over_m_hi = _paired_bootstrap_ratio_ci(o_st, m_st_o, seed=13400 + m_idx)
                    else:
                        os_over_m = os_over_m_lo = os_over_m_hi = float("nan")

                    summary_rows.append(
                        {
                            "eps": eps,
                            "stopping_regime": regime,
                            "landscape": land,
                            "method": method,
                            "runs": n,
                            "cert_rate": round(n_cert / n, 4),
                            "restricted_mean": round(rm_pt, 2),
                            "rm_ci95_lo": round(rm_lo, 2),
                            "rm_ci95_hi": round(rm_hi, 2),
                            "med_all": round(all_med, 1),
                            "q25_all": round(q25, 1),
                            "q75_all": round(q75, 1),
                            "med_certified": round(succ_med, 1) if math.isfinite(succ_med) else "",
                            "ratio_method_over_kg": round(r_over_kg, 4) if math.isfinite(r_over_kg) else "",
                            "ratio_method_over_kg_ci95_lo": round(r_over_kg_lo, 4) if math.isfinite(r_over_kg_lo) else "",
                            "ratio_method_over_kg_ci95_hi": round(r_over_kg_hi, 4) if math.isfinite(r_over_kg_hi) else "",
                            "speedup_kg_over_method": round(kg_over_m, 3) if math.isfinite(kg_over_m) else "",
                            "speedup_kg_over_method_ci95_lo": round(kg_over_m_lo, 3) if math.isfinite(kg_over_m_lo) else "",
                            "speedup_kg_over_method_ci95_hi": round(kg_over_m_hi, 3) if math.isfinite(kg_over_m_hi) else "",
                            "ratio_method_over_cd": round(m_over_cd, 3) if math.isfinite(m_over_cd) else "",
                            "ratio_method_over_cd_ci95_lo": round(m_over_cd_lo, 3) if math.isfinite(m_over_cd_lo) else "",
                            "ratio_method_over_cd_ci95_hi": round(m_over_cd_hi, 3) if math.isfinite(m_over_cd_hi) else "",
                            "speedup_dfos_over_method": round(os_over_m, 3) if math.isfinite(os_over_m) else "",
                            "speedup_dfos_over_method_ci95_lo": round(os_over_m_lo, 3) if math.isfinite(os_over_m_lo) else "",
                            "speedup_dfos_over_method_ci95_hi": round(os_over_m_hi, 3) if math.isfinite(os_over_m_hi) else "",
                            "false_certs": n_err,
                            "false_cert_rate": round(n_err / n, 4),
                            "cp95_upper_err": round(_cp_upper_95(n_err, n), 4),
                            "mean_root_regret_all": round(float(np.mean(all_regs)), 6),
                            "max_root_regret_all": round(float(np.max(all_regs)), 6),
                            "mean_root_regret_cert": round(float(np.mean(cert_regs)), 6) if len(cert_regs) else 0.0,
                            "pointwise_gp_cov_at_stop": round(pw_cov, 4),
                            "mean_distinct_leaves": round(float(np.mean([r["distinct_leaves"] for r in sub])), 1),
                            "mean_acq_time_s": round(float(np.mean(acq_s_arr)), 3),
                            "med_acq_time_s": round(float(np.median(acq_s_arr)), 3),
                            "acq_ms_per_step": round(ms_per_step, 4),
                            "mean_total_time_s": round(float(np.mean(tot_s_arr)), 3),
                        }
                    )

                # Per-template breakdown for primary eps in Regime A & Regime B
                if abs(eps - PRIMARY_EPS) < 1e-9:
                    tmpls = sorted(set(r["start_seq"] for r in cohort))
                    for tmpl in tmpls:
                        for method in methods:
                            tsub = [r for r in cohort if r["start_seq"] == tmpl and r["method"] == method]
                            if not tsub:
                                continue
                            t_st = np.array([float(r["steps"]) for r in tsub], dtype=np.float64)
                            template_rows.append(
                                {
                                    "eps": eps,
                                    "stopping_regime": regime,
                                    "landscape": land,
                                    "start_seq": tmpl,
                                    "template_regime": tsub[0]["template_regime"],
                                    "m_leaves": tsub[0]["m_leaves"],
                                    "k_actions": tsub[0]["k_actions"],
                                    "method": method,
                                    "runs": len(tsub),
                                    "cert_rate": round(sum(1 for r in tsub if r["certified"]) / len(tsub), 4),
                                    "restricted_mean": round(float(np.mean(t_st)), 1),
                                    "med_all": round(float(np.median(t_st)), 1),
                                    "false_certs": sum(1 for r in tsub if r["false_cert"]),
                                    "mean_root_regret": round(float(np.mean([r["true_regret"] for r in tsub])), 6),
                                }
                            )

    with (dest / "v13_protein_summary.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)

    if template_rows:
        with (dest / "v13_protein_per_template.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(template_rows[0].keys()))
            w.writeheader()
            w.writerows(template_rows)

    print("\n=== v13 Matched Protein BED vs. Correlated KG Summary ===")
    for eps in eps_vals:
        for regime in ("bayes_ellipsoid", "df_emp_bernstein"):
            for land in ("gb1", "trpb"):
                sub_s = [
                    r for r in summary_rows
                    if abs(r["eps"] - eps) < 1e-9 and r["stopping_regime"] == regime and r["landscape"] == land
                ]
                if not sub_s:
                    continue
                print(f"\n--- {land.upper()} | {regime} | eps={eps:.3f} (n={sub_s[0]['runs']}) ---")
                for r in sub_s:
                    print(
                        f"  {r['method']:20s} | cert={100*r['cert_rate']:5.1f}% | "
                        f"RM={r['restricted_mean']:8.1f} [{r['rm_ci95_lo']:7.1f},{r['rm_ci95_hi']:7.1f}] | "
                        f"med_ok={str(r['med_certified']):>7s} | "
                        f"KG/m={str(r['speedup_kg_over_method']):>5s}x [{str(r['speedup_kg_over_method_ci95_lo']):>5s},{str(r['speedup_kg_over_method_ci95_hi']):>5s}] | "
                        f"err={r['false_certs']}/{r['runs']} reg={r['mean_root_regret_all']:.5f} | "
                        f"acq={r['mean_acq_time_s']:5.2f}s ({r['acq_ms_per_step']:.3f}ms/st)"
                    )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true", help="Fast smoke run (2 templates x 2 seeds, cap=2500)")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(48, max(1, (os.cpu_count() or 8) - 4)))
    ap.add_argument("--cap", type=int, default=CAP_ASSAYS)
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
        eps_targets = (PRIMARY_EPS, SENS_EPS)
    else:
        gb1_tmpls = GB1_TEMPLATES
        trpb_tmpls = TRPB_TEMPLATES
        gb1_seeds = GB1_SEEDS
        trpb_seeds = TRPB_SEEDS
        cap = int(args.cap)
        eps_targets = EPS_LIST

    tasks: list[tuple[str, str, int, tuple[float, ...], int]] = []
    for seq in gb1_tmpls:
        for seed in gb1_seeds:
            tasks.append(("gb1", seq, seed, eps_targets, cap))
    for seq in trpb_tmpls:
        for seed in trpb_seeds:
            tasks.append(("trpb", seq, seed, eps_targets, cap))

    print(
        f"[v13 Protein BED vs KG] Launching {len(tasks)} paired campaign instances "
        f"(GB1={len(gb1_tmpls)}x{len(gb1_seeds)}, TrpB={len(trpb_tmpls)}x{len(trpb_seeds)}, "
        f"eps={eps_targets}, cap={cap}) on {args.workers} workers...",
        flush=True,
    )
    all_rows: list[dict] = []
    ctx = mp.get_context("spawn")
    done_cnt = 0
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for chunk_rows in ex.map(_instance_worker, tasks):
            all_rows.extend(chunk_rows)
            done_cnt += 1
            if done_cnt % 40 == 0 or done_cnt == len(tasks):
                print(
                    f"  [v13 progress] {done_cnt}/{len(tasks)} instances complete "
                    f"({len(all_rows)} rows, elapsed {time.perf_counter() - t0:.1f}s)",
                    flush=True,
                )

    p_runs = out_dir / "v13_protein_runs.jsonl"
    p_runs.write_text("\n".join(json.dumps(r) for r in all_rows) + "\n")
    summarize(out_dir)

    artifacts = [
        "v13_protein_runs.jsonl",
        "v13_protein_summary.csv",
        "v13_protein_per_template.csv",
    ]
    manifest = {
        "experiment": "v13_protein_bed_vs_kg",
        "smoke": bool(args.smoke),
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "cap": cap,
        "delta": DELTA,
        "eps_list": list(eps_targets),
        "n_gb1_instances": len(gb1_tmpls) * len(gb1_seeds),
        "n_trpb_instances": len(trpb_tmpls) * len(trpb_seeds),
        "total_policy_runs": len(all_rows),
        "python": platform.python_version(),
        "files": {
            nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size}
            for nm in artifacts
            if (out_dir / nm).is_file()
        },
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v13 Protein BED vs KG] Complete ({len(all_rows)} runs) in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
