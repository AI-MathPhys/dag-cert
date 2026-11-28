"""Experiment v17: Margin-Aware Contrast-Directed Joint Acquisition (MA-CD-Joint & MA-CD-Joint-Safe).

Implements the two-phase controlled evaluation across all five matched-model benchmarks:
  - **Phase A (Disjoint Development Validation, ~100 paired campaigns/benchmark):**
      * Synthetic M=64 (25 fresh seeds 9000..9024 x 4 conditions = 100)
      * Fixed-feature synthetic d=8 anytime-valid (25 fresh seeds 9500..9524 x 4 conditions = 100)
      * Cached WorFBench (5 domains x 4 bases x 5 fresh seeds 790001..790005 = 100)
      * TmTrpB (21 templates x 5 fresh seeds 892001..892005 = 105)
      * GB1 (10 original templates x 10 fresh seeds 891001..891010 = 100)
  - **Phase B (Full Expanded Benchmarks — 5,050 paired campaigns/policy):**
      * Synthetic M=64 (1,000 campaigns, 95% joint credible ellipsoid)
      * Fixed-feature synthetic d=8 (1,000 campaigns, anytime-valid Abbasi-Yadkori ellipsoid)
      * Cached WorFBench (1,000 campaigns, 95% joint credible ellipsoid)
      * TmTrpB (1,050 campaigns, 95% joint credible ellipsoid)
      * GB1 (1,000 campaigns, 95% joint credible ellipsoid)

Compares six matched policies sharing identical posteriors, paired intrinsic tapes, and
exact conic stopping criteria (with fixed algorithmic settings across ALL domains):
  1. ``gp_os``
  2. ``gp_root_info``
  3. ``cd_joint``
  4. ``cd_joint_single_witness``
  5. ``ma_cd_joint``       (Margin-Aware CD-Joint with eps/2 safeguard)
  6. ``ma_cd_joint_safe``  (Alternating mandatory CD-Joint + MA-CD-Joint with eps/2 safeguard)

Records all eight mechanistic diagnostics and checkpoint trajectories at
t in {10, 25, 50, 100, 250, 500, 1000, 2000, 5000} (with active campaign counts), plus
10,000-resample stratified paired bootstrap 95% CIs for cost ratios against CD-Joint,
GP-OS, GP-Root-Info, and CD-Joint-Single-Witness (and hierarchical template-level CIs on
GB1 and TmTrpB).
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import json
import math
import multiprocessing as mp
from pathlib import Path
import sys
import time
from typing import Any, Sequence

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from dagcert import (
    JointEllipsoidCertifier,
    SharedGaussianPosterior,
    SupportStructure,
    check_ellipsoid_stopping,
    chi2_credible_beta,
    compute_mechanistic_snapshot,
    contrast_ellipsoid_coverage,
    contrast_rank_of_kernel,
    default_check_schedule,
    select_gp_arm_with_beta,
    select_margin_aware_query,
)
from dagcert._core.v12_bed_acquisition import (
    FixedFeatureGaussianOverlapProblem,
    GaussianPairedDeconfoundedProblem,
)
from dagcert.benchmarks import (
    WORFBENCH_TEST_NPZ_PATH,
    WorFBenchWorkflowProblem,
    hamming_workflow_kernel,
)
from experiment.analysis_v15_stats import (
    _boot_mean_ci,
    _boot_median_ci,
    _boot_ratio_ci,
    _hierarchical_template_boot_indices,
    _stratified_boot_indices,
    cp_two_sided_95,
    cp_upper_95,
    git_commit_hash,
    write_csv,
    write_manifest,
)
from experiment.protein_engineering.exp_matched_bed_vs_kg import (
    CAP_ASSAYS as PROT_CAP,
    DELTA as PROT_DELTA,
    GB1_SEEDS as PHASE_B_GB1_SEEDS,
    PRIMARY_EPS as PROT_EPS,
    _bayes_check_schedule,
)
from experiment.protein_engineering.exp_real_world_applications import (
    GB1_TEMPLATES as ORIG_GB1_TEMPLATES,
    WORFBENCH_BASES,
    WORFBENCH_DOMAINS,
)
from experiment.protein_engineering.exp_real_world_validation import (
    TRPB_TEMPLATES,
    _worfbench_leaf_costs_and_unseen_values,
)
from experiment.protein_engineering.exp_v15_protein_7method import (
    EXPANDED_TRPB_SEEDS as PHASE_B_TRPB_SEEDS,
    _load_protein_problem,
    predeclared_gb1_50_templates,
)
from experiment.agentic_workflows.exp_v15_worfbench_7method import (
    CAP as WF_CAP,
    DELTA as WF_DELTA,
    EPS as WF_EPS,
    LENGTHSCALE as WF_LEN,
    NUGGET_FRAC as WF_NUG,
    OBS_STD as WF_OBS_STD,
    PRIOR_MEAN as WF_PRIOR_MEAN,
    PRIOR_SCALE as WF_PRIOR_SCALE,
    _parse_workflow_config,
)
from experiment.simulated.exp_v15_synthetic_7method_and_ablations import (
    CAP as SYN_CAP,
    CONDITIONS as SYN_CONDITIONS,
    DELTA as SYN_DELTA,
    EPS as SYN_EPS,
)

DEST_BASE = ROOT / "results/bayesian_ucd_v1"

SIX_POLICIES: tuple[str, ...] = (
    "gp_os",
    "gp_root_info",
    "cd_joint",
    "cd_joint_single_witness",
    "ma_cd_joint",
    "ma_cd_joint_safe",
)

ALL_BENCHMARKS: tuple[str, ...] = (
    "synthetic_main64",
    "synthetic_confirm_freq_d8",
    "worfbench_cached",
    "trpb",
    "gb1",
)

CHECKPOINTS: tuple[int, ...] = (10, 25, 50, 100, 250, 500, 1000, 2000, 5000)


def _select_with_telemetry(
    *,
    policy: str,
    supports: SupportStructure,
    leaf_to_actions: list[list[int]],
    posterior: SharedGaussianPosterior,
    certifier: JointEllipsoidCertifier,
    beta: float,
    epsilon: float,
    step: int,
    delta: float,
    root_selection_mode: str,
    cd_stop_if_above_eps: bool,
    cert_cache: dict[int, Any] | None = None,
) -> tuple[int, dict[str, Any]]:
    """Run one matched acquisition step for any of the 6 policies and return ``(arm, meta)``."""
    means = posterior.mean
    sig = posterior.sigma_mat
    diag_sig = np.maximum(1e-18, np.diag(sig))
    stds = np.sqrt(diag_sig)
    costs = supports.costs
    m = supports.m
    u_ell = means + beta * stds

    if policy in ("ma_cd_joint", "ma_cd_joint_safe"):
        cached_rc = None
        if cert_cache is not None:
            y_opt_m = int(np.argmax(u_ell))
            cont_m = leaf_to_actions[y_opt_m]
            if cert_cache and int(next(iter(cert_cache.keys()))) in cont_m:
                kb = int(next(iter(cert_cache.keys())))
                cached_rc = (kb, cert_cache[kb])
            else:
                if root_selection_mode == "ucb_lcb_sep":
                    l_ell = means - beta * stds
                    kb = max(
                        cont_m,
                        key=lambda a: (
                            float(u_ell[y_opt_m])
                            - (float(np.max(l_ell[supports.complements[a]])) if len(supports.complements[a]) else -math.inf),
                            -a,
                        ),
                    )
                else:
                    kb = max(cont_m, key=lambda b: (float(np.max(means[supports.supports[b]])), -b))
                prev_eps = certifier.epsilon
                certifier.epsilon = float(epsilon)
                try:
                    cb_m = certifier.certify_action_gp(
                        action=int(kb),
                        means=means,
                        sigma_mat=sig,
                        beta=beta,
                        stop_if_above_eps=cd_stop_if_above_eps,
                    )
                finally:
                    certifier.epsilon = prev_eps
                cert_cache.clear()
                cert_cache[int(kb)] = cb_m
                cached_rc = (int(kb), cb_m)
        sel = select_margin_aware_query(
            supports=supports,
            leaf_to_actions=leaf_to_actions,
            posterior=posterior,
            certifier=certifier,
            beta=beta,
            epsilon=epsilon,
            step_idx=step - 1,
            safe=(policy == "ma_cd_joint_safe"),
            cd_stop_if_above_eps=cd_stop_if_above_eps,
            cached_root_cert=cached_rc,
            root_selection_mode=root_selection_mode,
            use_cpp=True,
        )
        return sel.arm, {
            "safeguard": sel.safeguard_triggered,
            "inside_support": sel.inside_support,
            "mixture_support": sel.mixture_support,
            "used_ma": sel.used_ma_query,
            "mandatory_cd": sel.mandatory_cd_step,
        }

    if policy == "cd_joint":
        y_opt = int(np.argmax(u_ell))
        containers = leaf_to_actions[y_opt]
        if cert_cache and int(next(iter(cert_cache.keys()))) in containers:
            b_t = int(next(iter(cert_cache.keys())))
            cb = cert_cache[b_t]
        else:
            if root_selection_mode == "ucb_lcb_sep":
                l_ell = means - beta * stds
                best_sep = -math.inf
                b_t = containers[0]
                for a in containers:
                    comp_a = supports.complements[a]
                    l_out = float(np.max(l_ell[comp_a])) if len(comp_a) else -math.inf
                    sep = float(u_ell[y_opt]) - l_out
                    if sep > best_sep:
                        best_sep = sep
                        b_t = a
            else:
                b_t = max(containers, key=lambda b: (float(np.max(means[supports.supports[b]])), -b))

            prev_eps = certifier.epsilon
            certifier.epsilon = float(epsilon)
            try:
                cb = certifier.certify_action_gp(
                    action=int(b_t),
                    means=means,
                    sigma_mat=sig,
                    beta=beta,
                    stop_if_above_eps=cd_stop_if_above_eps,
                )
            finally:
                certifier.epsilon = prev_eps
            if cert_cache is not None:
                cert_cache.clear()
                cert_cache[int(b_t)] = cb

        sup_b = supports.supports[b_t]
        z_t = int(cb.challenger_idx)
        if z_t < 0:
            arm = y_opt
            return arm, {
                "safeguard": False,
                "inside_support": bool(arm in sup_b),
                "mixture_support": 1,
                "used_ma": False,
                "mandatory_cd": False,
            }
        mix_s = int(np.sum(cb.inside_weights > 1e-6))
        gap_hat = float(cb.contrast @ means)
        sg_flag = bool(gap_hat > 0.5 * epsilon)
        if not sg_flag:
            g = cb.contrast
        else:
            g = np.zeros(m, dtype=np.float64)
            g[z_t] = 1.0
            g[y_opt] = -1.0
        sg_v = sig @ g
        dv = (sg_v * sg_v) / (posterior.obs_var + diag_sig)
        arm = int(np.argmax(dv / costs))
        return arm, {
            "safeguard": sg_flag,
            "inside_support": bool(np.any(sup_b == arm)),
            "mixture_support": mix_s,
            "used_ma": False,
            "mandatory_cd": False,
        }

    if policy == "cd_joint_single_witness":
        y_opt = int(np.argmax(u_ell))
        containers = leaf_to_actions[y_opt]
        if root_selection_mode == "ucb_lcb_sep":
            l_ell = means - beta * stds
            best_sep = -math.inf
            b_t = containers[0]
            for a in containers:
                comp_a = supports.complements[a]
                l_out = float(np.max(l_ell[comp_a])) if len(comp_a) else -math.inf
                sep = float(u_ell[y_opt]) - l_out
                if sep > best_sep:
                    best_sep = sep
                    b_t = a
        else:
            b_t = max(containers, key=lambda b: (float(np.max(means[supports.supports[b]])), -b))
        sup_b = supports.supports[b_t]
        comp_b = supports.complements[b_t]
        if len(comp_b) == 0:
            return y_opt, {
                "safeguard": False,
                "inside_support": True,
                "mixture_support": 1,
                "used_ma": False,
                "mandatory_cd": False,
            }
        sig_sc = sig[sup_b[:, None], comp_b[None, :]]
        q_mat = np.sqrt(np.maximum(1e-18, diag_sig[comp_b][None, :] + diag_sig[sup_b][:, None] - 2.0 * sig_sc))
        vert_scores = (means[comp_b][None, :] - means[sup_b][:, None]) + beta * q_mat
        best_y_pos = np.argmin(vert_scores, axis=0)
        vert_ub = vert_scores[best_y_pos, np.arange(len(comp_b))]
        worst_c = int(np.argmax(vert_ub))
        z_t = int(comp_b[worst_c])
        y_w = int(sup_b[int(best_y_pos[worst_c])])
        sg_flag = bool(float(means[z_t] - means[y_w]) > 0.5 * epsilon)
        g = np.zeros(m, dtype=np.float64)
        g[z_t] = 1.0
        g[y_opt if sg_flag else y_w] = -1.0
        sg_v = sig @ g
        dv = (sg_v * sg_v) / (posterior.obs_var + diag_sig)
        arm = int(np.argmax(dv / costs))
        return arm, {
            "safeguard": sg_flag,
            "inside_support": bool(np.any(sup_b == arm)),
            "mixture_support": 1,
            "used_ma": False,
            "mandatory_cd": False,
        }

    # gp_os / gp_root_info
    if policy == "gp_os" and root_selection_mode == "mean_tiebreak":
        # Match MatchedModelBEDSession (v15 synthetic) exact GP-OS convention (argmax lo[sup] inside)
        lo = means - beta * stds
        hi = means + beta * stds
        best_sep = -math.inf
        best_p, best_q, b_t = 0, -1, 0
        for a in range(supports.k):
            sup_a = supports.supports[a]
            comp_a = supports.complements[a]
            if len(comp_a) == 0:
                continue
            sep = float(np.max(hi[sup_a]) - np.max(lo[comp_a]))
            if sep > best_sep:
                best_sep = sep
                b_t = a
                best_p = int(sup_a[int(np.argmax(lo[sup_a]))])
                best_q = int(comp_a[int(np.argmax(hi[comp_a]))])
        if best_q < 0:
            arm = best_p
        else:
            sp = float(stds[best_p]) / math.sqrt(float(costs[best_p]))
            sq = float(stds[best_q]) / math.sqrt(float(costs[best_q]))
            arm = best_p if sp >= sq else best_q
        return arm, {
            "safeguard": False,
            "inside_support": bool(np.any(supports.supports[b_t] == arm)),
            "mixture_support": 1,
            "used_ma": False,
            "mandatory_cd": False,
        }

    arm = select_gp_arm_with_beta(
        policy, supports, leaf_to_actions, posterior, certifier, beta=beta, epsilon=epsilon, step=step, delta=delta
    )
    # Candidate root for inside-support fraction accounting (matching policy's own candidate root)
    if policy == "gp_os":
        l_ell = means - beta * stds
        b_t = max(
            range(supports.k),
            key=lambda a: float(np.max(u_ell[supports.supports[a]]))
            - (float(np.max(l_ell[supports.complements[a]])) if len(supports.complements[a]) else -math.inf),
        )
    else:
        w_star = int(np.argmax(u_ell))
        b_t = max(
            leaf_to_actions[w_star],
            key=lambda a: float(u_ell[w_star])
            - (float(np.max(u_ell[supports.complements[a]])) if len(supports.complements[a]) else -math.inf),
        )
    return arm, {
        "safeguard": False,
        "inside_support": bool(np.any(supports.supports[b_t] == arm)),
        "mixture_support": 1,
        "used_ma": False,
        "mandatory_cd": False,
    }


def _run_one_campaign(
    *,
    dataset: str,
    condition: str,
    domain: str,
    template_id: str,
    seed: int,
    policy: str,
    stopping_label: str,
    ss: SupportStructure,
    l2a: list[list[int]],
    kernel: np.ndarray,
    prior_mean: float,
    obs_std: float,
    beta_mode: str,
    rkhs_bound: float,
    contrast_rank: int,
    epsilon: float,
    delta: float,
    cap: int,
    oracle: Any,
    true_means_vec: np.ndarray,
    regrets: Sequence[float],
    is_eps_opt_leaf: np.ndarray,
    check_fn: Any,
    root_selection_mode: str,
    cd_stop_if_above_eps: bool,
    cache_cert_between_checks: bool = False,
    tok_vec: np.ndarray | None = None,
    act_test_vals: Sequence[float] | None = None,
    test_opt: float | None = None,
    record_checkpoints: bool = True,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Execute one matched campaign and return ``(campaign_row, trajectory_rows)``."""
    post = SharedGaussianPosterior(
        kernel=kernel,
        prior_mean=prior_mean,
        obs_std=obs_std,
        delta=delta,
        beta_mode=beta_mode,
        rkhs_bound=rkhs_bound,
        contrast_rank=contrast_rank,
    )
    certifier = JointEllipsoidCertifier(ss, epsilon=epsilon, solver="colgen_lazy", exact_linear_mean=False)
    cert_cache: dict[int, Any] | None = {} if cache_cert_between_checks else None

    ck_set = set(c for c in CHECKPOINTS if c <= cap) if record_checkpoints else set()
    traj_rows: list[dict[str, Any]] = []

    t_start = time.perf_counter()
    acq_s = 0.0
    cert_s = 0.0
    certified = False
    rec_action = 0
    reg_bound: float | None = None
    disc_step: int | None = None
    subopt_pulls = 0
    sg_count = 0
    inside_count = 0
    mix_sum = 0
    ma_count = 0
    mand_cd_count = 0
    cum_tokens = 0.0
    t_done = 0

    for step in range(1, cap + 1):
        t_done = step - 1
        beta_now = float(post.beta())

        if t_done > 0 and check_fn(t_done):
            if cert_cache is not None:
                cert_cache.clear()
            tc0 = time.perf_counter()
            ok, act_b, reg_b = check_ellipsoid_stopping(
                certifier, ss, post.mean, post.sigma_mat, beta_now, epsilon
            )
            cert_s += time.perf_counter() - tc0
            if ok:
                certified = True
                rec_action = int(act_b)
                reg_bound = float(reg_b)
                break

        ta0 = time.perf_counter()
        arm, meta = _select_with_telemetry(
            policy=policy,
            supports=ss,
            leaf_to_actions=l2a,
            posterior=post,
            certifier=certifier,
            beta=beta_now,
            epsilon=epsilon,
            step=step,
            delta=delta,
            root_selection_mode=root_selection_mode,
            cd_stop_if_above_eps=cd_stop_if_above_eps,
            cert_cache=cert_cache,
        )
        acq_s += time.perf_counter() - ta0

        if meta["safeguard"]:
            sg_count += 1
        if meta["inside_support"]:
            inside_count += 1
        mix_sum += int(meta["mixture_support"])
        if meta["used_ma"]:
            ma_count += 1
        if meta["mandatory_cd"]:
            mand_cd_count += 1

        leaf = ss.leaves[arm]
        y = float(oracle.sample(leaf))
        if tok_vec is not None:
            cum_tokens += float(tok_vec[arm])
        if is_eps_opt_leaf[arm]:
            if disc_step is None:
                disc_step = step
        else:
            subopt_pulls += 1

        post.observe(arm, y)

        if step in ck_set:
            snap = compute_mechanistic_snapshot(
                supports=ss,
                leaf_to_actions=l2a,
                posterior=post,
                certifier=certifier,
                true_leaf_means=true_means_vec,
                beta=float(post.beta()),
                epsilon=epsilon,
            )
            traj_rows.append(
                {
                    "dataset": dataset,
                    "condition": condition,
                    "template_id": template_id,
                    "seed": int(seed),
                    "acquisition_method": policy,
                    "checkpoint": int(step),
                    "active": True,
                    "inside_query_frac": round(inside_count / float(step), 5),
                    "safeguard_rate": round(sg_count / float(step), 5),
                    "ma_query_frac": round(ma_count / float(step), 5),
                    "best_eval_retained_fitness": round(snap["best_eval_retained_fitness"], 6)
                    if math.isfinite(snap["best_eval_retained_fitness"])
                    else None,
                    "retained_witness_margin": round(snap["retained_witness_margin"], 6)
                    if math.isfinite(snap["retained_witness_margin"])
                    else None,
                    "active_contrast_var": round(snap["active_contrast_var"], 8),
                    "std_cert_margin": round(snap["std_cert_margin"], 5)
                    if math.isfinite(snap["std_cert_margin"])
                    else None,
                    "std_cert_progress": round(snap["std_cert_progress"], 5),
                }
            )

    if not certified:
        t_done = cap
        beta_now = float(post.beta())
        tc0 = time.perf_counter()
        ok, act_b, reg_b = check_ellipsoid_stopping(
            certifier, ss, post.mean, post.sigma_mat, beta_now, epsilon
        )
        cert_s += time.perf_counter() - tc0
        if ok:
            certified = True
            rec_action = int(act_b)
            reg_bound = float(reg_b)
        else:
            rec_action = int(np.argmax([float(np.max(post.mean[sup])) for sup in ss.supports]))
            reg_bound = float(reg_b) if math.isfinite(reg_b) else None

    tot_s = time.perf_counter() - t_start
    n_evals = int(t_done) if certified else int(cap)
    beta_end = float(post.beta())
    true_reg = float(regrets[rec_action])
    false_cert = bool(certified and true_reg > epsilon + 1e-12)

    # Exact contrast-ellipsoid coverage (handles both full-rank and rank-d fixed-feature kernels)
    jcov, _ = contrast_ellipsoid_coverage(post.mean, post.sigma_mat, beta_end, true_means_vec)
    rcov = bool((reg_bound is None) or (true_reg <= reg_bound + 1e-9))

    # Final mechanistic snapshot at stop/cap
    final_snap = compute_mechanistic_snapshot(
        supports=ss,
        leaf_to_actions=l2a,
        posterior=post,
        certifier=certifier,
        true_leaf_means=true_means_vec,
        beta=beta_end,
        epsilon=epsilon,
    )

    hf1 = float(act_test_vals[rec_action]) if act_test_vals is not None else None
    hreg = max(0.0, float(test_opt - hf1)) if (test_opt is not None and hf1 is not None) else None

    row: dict[str, Any] = {
        "dataset": dataset,
        "condition": condition,
        "domain": domain,
        "template_id": template_id,
        "seed": int(seed),
        "acquisition_method": policy,
        "stopping_rule": stopping_label,
        "epsilon": float(epsilon),
        "delta": float(delta),
        "budget": int(cap),
        "n_evaluations": n_evals,
        "certified": bool(certified),
        "recommended_root": int(rec_action),
        "true_root_regret": round(true_reg, 6),
        "false_certificate": false_cert,
        "first_epsilon_optimal_discovery": int(disc_step) if disc_step is not None else int(cap),
        "discovered": bool(disc_step is not None),
        "joint_coverage": bool(jcov),
        "root_regret_bound_coverage": rcov,
        "cert_regret_bound": round(reg_bound, 6) if (reg_bound is not None and math.isfinite(reg_bound)) else None,
        "contrast_rank": int(contrast_rank),
        "beta_at_stop": round(beta_end, 4),
        "total_tokens": round(cum_tokens, 1),
        "heldout_f1": round(hf1, 5) if hf1 is not None else None,
        "heldout_regret": round(hreg, 5) if hreg is not None else None,
        "acquisition_time_s": round(acq_s, 5),
        "certificate_time_s": round(cert_s, 5),
        "total_runtime_s": round(tot_s, 5),
        "acq_ms_per_query": round(1e3 * acq_s / max(1, n_evals), 4),
        "safeguard_activations": int(sg_count),
        "safeguard_rate": round(sg_count / max(1, n_evals), 5),
        "inside_query_frac": round(inside_count / max(1, n_evals), 5),
        "ma_query_frac": round(ma_count / max(1, n_evals), 5),
        "mandatory_cd_frac": round(mand_cd_count / max(1, n_evals), 5),
        "mean_mixture_support": round(mix_sum / max(1, n_evals), 4),
        "proxy_query_frac": round(subopt_pulls / max(1, n_evals), 5),
        "final_best_eval_retained_fitness": round(final_snap["best_eval_retained_fitness"], 6)
        if math.isfinite(final_snap["best_eval_retained_fitness"])
        else None,
        "final_retained_witness_margin": round(final_snap["retained_witness_margin"], 6)
        if math.isfinite(final_snap["retained_witness_margin"])
        else None,
        "final_active_contrast_var": round(final_snap["active_contrast_var"], 8),
        "final_std_cert_margin": round(final_snap["std_cert_margin"], 5)
        if math.isfinite(final_snap["std_cert_margin"])
        else None,
    }
    return row, traj_rows


# ---------------------------------------------------------------------------
# Per-Benchmark Workers
# ---------------------------------------------------------------------------


def _synthetic_worker(task: tuple) -> tuple[str, list[dict[str, Any]], list[dict[str, Any]]]:
    task_id, dataset, cond_id, omega, rho, seeds, policies, cap, record_ck = task
    is_freq = dataset == "synthetic_confirm_freq_d8"
    beta_mode = "anytime_frequentist" if is_freq else "posterior_credible"
    stop_lbl = "anytime_frequentist_ay" if is_freq else "credible_ellipsoid_chi95"

    rows: list[dict[str, Any]] = []
    trajs: list[dict[str, Any]] = []
    for s in seeds:
        if is_freq:
            prob_seed = 8000 + s * 29 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
            obs_seed = 950000 + s * 107 + int(round(omega * 100)) * 17 + int(round(rho * 100)) * 5
            prob = FixedFeatureGaussianOverlapProblem(
                seed=prob_seed, overlap=omega, rho=rho, d_feat=8, target_margin=0.055, tau0=0.14, hw=0.14
            )
        else:
            prob_seed = 5000 + s * 17 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
            obs_seed = 920000 + s * 97 + int(round(omega * 100)) * 13 + int(round(rho * 100)) * 5
            prob = GaussianPairedDeconfoundedProblem(
                seed=prob_seed, overlap=omega, rho=rho, target_margin=0.055, tau0=0.14, hw=0.14
            )

        ss = SupportStructure(prob.graph)
        l2a = [[] for _ in range(ss.m)]
        for a, sup in enumerate(ss.supports):
            for idx in sup:
                l2a[int(idx)].append(a)
        vals = prob.graph.optimal_values(prob.means)
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in prob.graph.children[prob.graph.root]]
        true_means_vec = np.array([float(prob.means[lf]) for lf in ss.leaves], dtype=np.float64)
        is_eps_opt = (opt_mu - true_means_vec) <= (SYN_EPS + 1e-12)
        r_rank = contrast_rank_of_kernel(prob.kernel)

        for pol in policies:
            row, tr = _run_one_campaign(
                dataset=dataset,
                condition=cond_id,
                domain="synthetic",
                template_id=f"{cond_id}_s{s}",
                seed=s,
                policy=pol,
                stopping_label=stop_lbl,
                ss=ss,
                l2a=l2a,
                kernel=prob.kernel,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                beta_mode=beta_mode,
                rkhs_bound=prob.clean_rkhs_norm + 0.05,
                contrast_rank=r_rank,
                epsilon=SYN_EPS,
                delta=SYN_DELTA,
                cap=cap,
                oracle=prob.oracle(obs_seed),
                true_means_vec=true_means_vec,
                regrets=regrets,
                is_eps_opt_leaf=is_eps_opt,
                check_fn=lambda t: default_check_schedule(t, full_every_step=False),
                root_selection_mode="mean_tiebreak",
                cd_stop_if_above_eps=False,
                cache_cert_between_checks=True,
                record_checkpoints=record_ck,
            )
            rows.append(row)
            trajs.extend(tr)
    return task_id, rows, trajs


def _worfbench_worker(task: tuple) -> tuple[str, list[dict[str, Any]], list[dict[str, Any]]]:
    task_id, domain, base_name, base_cfg, max_u, seeds, policies, cap, record_ck = task
    prob = WorFBenchWorkflowProblem(domain=domain, base_config=base_cfg, max_upgrades=max_u)
    test_arch = dict(np.load(WORFBENCH_TEST_NPZ_PATH, allow_pickle=True))
    leaf_toks, _, act_test_vals, test_opt = _worfbench_leaf_costs_and_unseen_values(prob, test_arch)

    ss = SupportStructure(prob.graph)
    l2a = [[] for _ in range(ss.m)]
    for a, sup in enumerate(ss.supports):
        for idx in sup:
            l2a[int(idx)].append(a)
    vals = prob.graph.optimal_values(prob.means)
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in prob.graph.children[prob.graph.root]]
    true_means_vec = np.array([float(prob.means[lf]) for lf in ss.leaves], dtype=np.float64)
    is_eps_opt = (opt_mu - true_means_vec) <= (WF_EPS + 1e-12)
    tok_vec = np.array([float(leaf_toks[lf]) for lf in ss.leaves], dtype=np.float64)
    configs = [_parse_workflow_config(prob.leaf_workflow_name[lf]) for lf in ss.leaves]
    kernel = hamming_workflow_kernel(
        configs, prior_scale=WF_PRIOR_SCALE, lengthscale=WF_LEN, nugget_frac=WF_NUG
    )
    r_rank = contrast_rank_of_kernel(kernel)
    tmpl_id = f"{domain}__{base_name}"

    rows: list[dict[str, Any]] = []
    trajs: list[dict[str, Any]] = []
    for s in seeds:
        for pol in policies:
            row, tr = _run_one_campaign(
                dataset="worfbench_cached",
                condition=tmpl_id,
                domain=domain,
                template_id=tmpl_id,
                seed=s,
                policy=pol,
                stopping_label="credible_ellipsoid_chi95",
                ss=ss,
                l2a=l2a,
                kernel=kernel,
                prior_mean=WF_PRIOR_MEAN,
                obs_std=WF_OBS_STD,
                beta_mode="posterior_credible",
                rkhs_bound=1.0,
                contrast_rank=r_rank,
                epsilon=WF_EPS,
                delta=WF_DELTA,
                cap=cap,
                oracle=prob.oracle(s),
                true_means_vec=true_means_vec,
                regrets=regrets,
                is_eps_opt_leaf=is_eps_opt,
                check_fn=lambda t: default_check_schedule(t, full_every_step=False),
                root_selection_mode="ucb_lcb_sep",
                cd_stop_if_above_eps=True,
                cache_cert_between_checks=True,
                tok_vec=tok_vec,
                act_test_vals=act_test_vals,
                test_opt=test_opt,
                record_checkpoints=record_ck,
            )
            rows.append(row)
            trajs.extend(tr)
    return task_id, rows, trajs


def _protein_worker(task: tuple) -> tuple[str, list[dict[str, Any]], list[dict[str, Any]]]:
    task_id, landscape, start_seq, policies, seeds, cap, record_ck = task
    prob, ss, l2a, kernel, prior_m, obs_s, regrets, true_means_vec, is_eps_opt, r_rank, regime_tag = (
        _load_protein_problem(landscape, start_seq)
    )
    rows: list[dict[str, Any]] = []
    trajs: list[dict[str, Any]] = []
    for s in seeds:
        for pol in policies:
            row, tr = _run_one_campaign(
                dataset=landscape,
                condition=regime_tag,
                domain=landscape,
                template_id=start_seq,
                seed=s,
                policy=pol,
                stopping_label="credible_ellipsoid_chi95",
                ss=ss,
                l2a=l2a,
                kernel=kernel,
                prior_mean=prior_m,
                obs_std=obs_s,
                beta_mode="posterior_credible",
                rkhs_bound=1.0,
                contrast_rank=r_rank,
                epsilon=PROT_EPS,
                delta=PROT_DELTA,
                cap=cap,
                oracle=prob.oracle(s),
                true_means_vec=true_means_vec,
                regrets=regrets,
                is_eps_opt_leaf=is_eps_opt,
                check_fn=lambda t, c=cap: _bayes_check_schedule(t, c),
                root_selection_mode="ucb_lcb_sep",
                cd_stop_if_above_eps=True,
                record_checkpoints=record_ck,
            )
            rows.append(row)
            trajs.extend(tr)
    return task_id, rows, trajs


# ---------------------------------------------------------------------------
# Multi-Reference Paired Bootstrap Summary & Trajectory Aggregation
# ---------------------------------------------------------------------------


def summarize_ma_cohort(
    records: Sequence[dict[str, Any]],
    methods: Sequence[str],
    *,
    stratum_key: str,
    unit_keys: tuple[str, ...],
    hierarchical_key: str | None = None,
    include_workflow: bool = False,
    n_boot: int = 10000,
    boot_seed: int = 202617,
) -> list[dict[str, Any]]:
    """Compute standardized metrics + 95% paired bootstrap CIs vs. ALL FOUR requested comparators:
    ``cd_joint``, ``gp_os``, ``gp_root_info``, and ``cd_joint_single_witness``."""
    by_m: dict[str, dict[tuple, dict]] = {}
    for r in records:
        m = str(r["acquisition_method"])
        uid = tuple(r[k] for k in unit_keys)
        by_m.setdefault(m, {})[uid] = r

    present = [m for m in methods if m in by_m and len(by_m[m]) > 0]
    if not present:
        return []
    ref0 = "cd_joint" if "cd_joint" in by_m else present[0]
    canon_uids = sorted(by_m[ref0].keys())
    n = len(canon_uids)
    strata = np.array([str(by_m[ref0][u][stratum_key]) for u in canon_uids])
    boot_idx = _stratified_boot_indices(strata, n_boot=n_boot, seed=boot_seed)

    hier_idx = None
    if hierarchical_key is not None:
        tmpls = np.array([str(by_m[ref0][u][hierarchical_key]) for u in canon_uids])
        if len(set(tmpls.tolist())) > 1:
            hier_idx = _hierarchical_template_boot_indices(tmpls, n_boot=n_boot, seed=boot_seed + 91)

    refs: dict[str, np.ndarray | None] = {}
    for rname in ("cd_joint", "gp_os", "gp_root_info", "cd_joint_single_witness"):
        if rname in by_m and all(u in by_m[rname] for u in canon_uids):
            refs[rname] = np.array([float(by_m[rname][u]["n_evaluations"]) for u in canon_uids], dtype=np.float64)
        else:
            refs[rname] = None

    out: list[dict[str, Any]] = []
    for m in present:
        mmap = by_m[m]
        paired = all(u in mmap for u in canon_uids)
        uids = canon_uids if paired else sorted(mmap.keys())
        m_n = len(uids)
        m_boot = (
            boot_idx
            if paired
            else _stratified_boot_indices(
                np.array([str(mmap[u][stratum_key]) for u in uids]), n_boot=n_boot, seed=boot_seed + 13
            )
        )
        rows_m = [mmap[u] for u in uids]

        evals = np.array([float(r["n_evaluations"]) for r in rows_m], dtype=np.float64)
        certs = np.array([bool(r["certified"]) for r in rows_m], dtype=bool)
        errs = np.array([bool(r["false_certificate"]) for r in rows_m], dtype=bool)
        regs = np.array([float(r["true_root_regret"]) for r in rows_m], dtype=np.float64)
        acq_ms = np.array([float(r["acq_ms_per_query"]) for r in rows_m], dtype=np.float64)
        tot_s = np.array([float(r["total_runtime_s"]) for r in rows_m], dtype=np.float64)
        in_frac = np.array([float(r["inside_query_frac"]) for r in rows_m], dtype=np.float64)
        sg_rate = np.array([float(r["safeguard_rate"]) for r in rows_m], dtype=np.float64)
        ma_frac = np.array([float(r["ma_query_frac"]) for r in rows_m], dtype=np.float64)
        mix_sup = np.array([float(r["mean_mixture_support"]) for r in rows_m], dtype=np.float64)

        n_cert = int(np.sum(certs))
        n_err = int(np.sum(errs))
        cert_lo, cert_hi = cp_two_sided_95(n_cert, m_n)
        rm, rm_lo, rm_hi = _boot_mean_ci(evals, m_boot)
        med, med_lo, med_hi = _boot_median_ci(evals, m_boot)
        q25, q75 = np.percentile(evals, [25.0, 75.0])
        reg_m, reg_lo, reg_hi = _boot_mean_ci(regs, m_boot)
        rt_m, rt_lo, rt_hi = _boot_mean_ci(tot_s, m_boot)

        jcov_vals = [bool(r["joint_coverage"]) for r in rows_m if r["joint_coverage"] is not None]
        jcov = float(np.mean(jcov_vals)) if jcov_vals else float("nan")

        row: dict[str, Any] = {
            "acquisition_method": m,
            "n_campaigns": m_n,
            "n_certified": n_cert,
            "cert_rate": round(n_cert / float(m_n), 5),
            "cert_ci95_lo": round(cert_lo, 5),
            "cert_ci95_hi": round(cert_hi, 5),
            "restricted_mean": round(rm, 2),
            "rm_ci95_lo": round(rm_lo, 2),
            "rm_ci95_hi": round(rm_hi, 2),
            "capped_median": round(med, 2),
            "med_ci95_lo": round(med_lo, 2),
            "med_ci95_hi": round(med_hi, 2),
            "iqr_q25": round(float(q25), 2),
            "iqr_q75": round(float(q75), 2),
            "false_certificates": n_err,
            "false_cert_cp95_upper": round(cp_upper_95(n_err, m_n), 5),
            "mean_root_regret": round(reg_m, 6),
            "regret_ci95_lo": round(reg_lo, 6),
            "regret_ci95_hi": round(reg_hi, 6),
            "joint_coverage": round(jcov, 5) if math.isfinite(jcov) else None,
            "mean_inside_query_frac": round(float(np.mean(in_frac)), 5),
            "mean_safeguard_rate": round(float(np.mean(sg_rate)), 5),
            "mean_ma_query_frac": round(float(np.mean(ma_frac)), 5),
            "mean_mixture_support": round(float(np.mean(mix_sup)), 4),
            "mean_acq_ms_per_query": round(float(np.mean(acq_ms)), 4),
            "median_acq_ms_per_query": round(float(np.median(acq_ms)), 4),
            "mean_total_runtime_s": round(rt_m, 4),
            "runtime_ci95_lo": round(rt_lo, 4),
            "runtime_ci95_hi": round(rt_hi, 4),
        }

        # Cost ratios RM_method / RM_ref (< 1.0 means method uses fewer evaluations than ref!)
        for rname, tag in (
            ("cd_joint", "vs_cd"),
            ("gp_os", "vs_gpos"),
            ("gp_root_info", "vs_gri"),
            ("cd_joint_single_witness", "vs_cd_single"),
        ):
            ref_arr = refs[rname]
            if paired and ref_arr is not None:
                rat, r_lo, r_hi = _boot_ratio_ci(evals, ref_arr, m_boot)
                row[f"ratio_{tag}"] = round(rat, 4)
                row[f"ratio_{tag}_ci95_lo"] = round(r_lo, 4)
                row[f"ratio_{tag}_ci95_hi"] = round(r_hi, 4)
                if hier_idx is not None:
                    _, hr_lo, hr_hi = _boot_ratio_ci(evals, ref_arr, hier_idx)
                    row[f"hier_ratio_{tag}_ci95_lo"] = round(hr_lo, 4)
                    row[f"hier_ratio_{tag}_ci95_hi"] = round(hr_hi, 4)

        if hier_idx is not None:
            _, h_lo, h_hi = _boot_mean_ci(evals, hier_idx)
            row["hier_rm_ci95_lo"] = round(h_lo, 2)
            row["hier_rm_ci95_hi"] = round(h_hi, 2)

        if include_workflow:
            toks = np.array([float(r["total_tokens"]) for r in rows_m], dtype=np.float64)
            hf1 = np.array([float(r["heldout_f1"]) for r in rows_m], dtype=np.float64)
            hreg = np.array([float(r["heldout_regret"]) for r in rows_m], dtype=np.float64)
            tm, tm_lo, tm_hi = _boot_mean_ci(toks, m_boot)
            f1_m, f1_lo, f1_hi = _boot_mean_ci(hf1, m_boot)
            hr_m, hr_lo, hr_hi = _boot_mean_ci(hreg, m_boot)
            row.update(
                {
                    "mean_tokens": round(tm, 1),
                    "mean_tokens_ci95_lo": round(tm_lo, 1),
                    "mean_tokens_ci95_hi": round(tm_hi, 1),
                    "heldout_f1_mean": round(f1_m, 5),
                    "heldout_f1_ci95_lo": round(f1_lo, 5),
                    "heldout_f1_ci95_hi": round(f1_hi, 5),
                    "heldout_regret_mean": round(hr_m, 5),
                    "heldout_regret_ci95_lo": round(hr_lo, 5),
                    "heldout_regret_ci95_hi": round(hr_hi, 5),
                }
            )
        out.append(row)
    return out


def summarize_trajectories(traj_rows: Sequence[dict[str, Any]], dataset: str) -> list[dict[str, Any]]:
    if not traj_rows:
        return []
    df = pd.DataFrame(traj_rows)
    out: list[dict[str, Any]] = []
    for pol in SIX_POLICIES:
        sub_p = df[df["acquisition_method"] == pol]
        if sub_p.empty:
            continue
        for ck in CHECKPOINTS:
            sub = sub_p[sub_p["checkpoint"] == ck]
            if sub.empty:
                continue
            fit_vals = sub["best_eval_retained_fitness"].dropna().to_numpy(dtype=np.float64)
            marg_vals = sub["retained_witness_margin"].dropna().to_numpy(dtype=np.float64)
            var_vals = sub["active_contrast_var"].dropna().to_numpy(dtype=np.float64)
            std_m = sub["std_cert_margin"].dropna().to_numpy(dtype=np.float64)
            out.append(
                {
                    "dataset": dataset,
                    "acquisition_method": pol,
                    "checkpoint": int(ck),
                    "n_active": int(len(sub)),
                    "mean_best_eval_retained_fitness": round(float(np.mean(fit_vals)), 6) if len(fit_vals) else None,
                    "mean_retained_witness_margin": round(float(np.mean(marg_vals)), 6) if len(marg_vals) else None,
                    "mean_active_contrast_var": round(float(np.mean(var_vals)), 8) if len(var_vals) else None,
                    "mean_std_cert_margin": round(float(np.mean(std_m)), 5) if len(std_m) else None,
                    "mean_std_cert_progress": round(float(sub["std_cert_progress"].mean()), 5),
                    "mean_inside_query_frac": round(float(sub["inside_query_frac"].mean()), 5),
                    "mean_safeguard_rate": round(float(sub["safeguard_rate"].mean()), 5),
                    "mean_ma_query_frac": round(float(sub["ma_query_frac"].mean()), 5),
                }
            )
    return out


# ---------------------------------------------------------------------------
# Phase A & Phase B Task Builders + Checkpointed Execution
# ---------------------------------------------------------------------------


def _run_benchmark(
    *,
    bench: str,
    phase: str,
    out_dir: Path,
    workers: int,
    smoke: bool,
    resume: bool,
    n_boot: int,
) -> list[dict[str, Any]]:
    ckpt_dir = out_dir / f"_ckpt_{bench}"
    ckpt_dir.mkdir(parents=True, exist_ok=True)
    ctx = mp.get_context("spawn")

    # Build task list for this benchmark and phase
    tasks: list[tuple] = []
    worker_fn: Any = None
    is_phase_a = phase == "A"
    record_ck = True

    if bench in ("synthetic_main64", "synthetic_confirm_freq_d8"):
        worker_fn = _synthetic_worker
        cap = 1500 if smoke else SYN_CAP
        if is_phase_a:
            n_s = 3 if smoke else 25  # 25 x 4 = 100 disjoint dev campaigns
            base_s = 9500 if bench == "synthetic_confirm_freq_d8" else 9000
        else:
            n_s = 4 if smoke else 250  # 250 x 4 = 1,000 full expanded campaigns
            base_s = 5000 if bench == "synthetic_confirm_freq_d8" else 2000
        seeds = list(range(base_s, base_s + n_s))
        chunk = 2 if smoke else 5
        for cid, om, rh in SYN_CONDITIONS:
            for pol in SIX_POLICIES:
                for i in range(0, len(seeds), chunk):
                    s_ch = seeds[i : i + chunk]
                    tid = f"{bench}_{cid}_{pol}_{s_ch[0]}_{s_ch[-1]}"
                    tasks.append((tid, bench, cid, om, rh, s_ch, (pol,), cap, record_ck))

    elif bench == "worfbench_cached":
        worker_fn = _worfbench_worker
        cap = 2000 if smoke else WF_CAP
        if is_phase_a:
            seeds = list(range(790001, 790001 + (2 if smoke else 5)))  # 5 x 20 = 100 disjoint dev
        else:
            seeds = list(range(780001, 780001 + (2 if smoke else 50)))  # 50 x 20 = 1,000 full expanded
        chunk = 2 if smoke else 5
        for dom in WORFBENCH_DOMAINS:
            for bname, bcfg, max_u in WORFBENCH_BASES:
                for pol in SIX_POLICIES:
                    for i in range(0, len(seeds), chunk):
                        s_ch = seeds[i : i + chunk]
                        tid = f"wf_{dom}_{bname}_{pol}_{s_ch[0]}_{s_ch[-1]}"
                        tasks.append((tid, dom, bname, bcfg, max_u, s_ch, (pol,), cap, record_ck))

    elif bench == "trpb":
        worker_fn = _protein_worker
        cap = 2000 if smoke else PROT_CAP
        tmpls = TRPB_TEMPLATES[:3] if smoke else TRPB_TEMPLATES
        if is_phase_a:
            seeds = list(range(892001, 892001 + (2 if smoke else 5)))  # 5 x 21 = 105 disjoint dev
        else:
            seeds = list(PHASE_B_TRPB_SEEDS[:2] if smoke else PHASE_B_TRPB_SEEDS)  # 50 x 21 = 1,050
        chunk = 2 if smoke else 5
        for seq in tmpls:
            for pol in SIX_POLICIES:
                for i in range(0, len(seeds), chunk):
                    s_ch = seeds[i : i + chunk]
                    tid = f"trpb_{seq}_{pol}_{s_ch[0]}_{s_ch[-1]}"
                    tasks.append((tid, "trpb", seq, (pol,), s_ch, cap, record_ck))

    elif bench == "gb1":
        worker_fn = _protein_worker
        cap = 2000 if smoke else PROT_CAP
        if is_phase_a:
            tmpls = ORIG_GB1_TEMPLATES[:2] if smoke else ORIG_GB1_TEMPLATES
            seeds = list(range(891001, 891001 + (2 if smoke else 10)))  # 10 x 10 = 100 disjoint dev
        else:
            tmpls = predeclared_gb1_50_templates()[:2] if smoke else predeclared_gb1_50_templates()
            seeds = list(PHASE_B_GB1_SEEDS[:2] if smoke else PHASE_B_GB1_SEEDS)  # 20 x 50 = 1,000
        chunk = 2 if smoke else 5
        for seq in tmpls:
            for pol in SIX_POLICIES:
                for i in range(0, len(seeds), chunk):
                    s_ch = seeds[i : i + chunk]
                    tid = f"gb1_{seq}_{pol}_{s_ch[0]}_{s_ch[-1]}"
                    tasks.append((tid, "gb1", seq, (pol,), s_ch, cap, record_ck))
    else:
        raise ValueError(f"Unknown benchmark: {bench!r}")

    pending: list[tuple] = []
    done_rows: list[dict[str, Any]] = []
    done_trajs: list[dict[str, Any]] = []
    for t in tasks:
        tid = t[0]
        rec_p = ckpt_dir / f"{tid}_rec.parquet"
        tr_p = ckpt_dir / f"{tid}_traj.parquet"
        if resume and rec_p.is_file():
            done_rows.extend(pd.read_parquet(rec_p).to_dict(orient="records"))
            if tr_p.is_file():
                done_trajs.extend(pd.read_parquet(tr_p).to_dict(orient="records"))
        else:
            pending.append(t)

    t0 = time.perf_counter()
    print(
        f"[v17 Phase {phase} | {bench}] {len(pending)} pending / {len(tasks)} chunks on {workers} workers...",
        flush=True,
    )
    if pending:
        completed = 0
        with ProcessPoolExecutor(max_workers=workers, mp_context=ctx) as ex:
            futs = [ex.submit(worker_fn, t) for t in pending]
            for fut in as_completed(futs):
                tid, r_ch, tr_ch = fut.result()
                pd.DataFrame(r_ch).to_parquet(ckpt_dir / f"{tid}_rec.parquet", index=False)
                if tr_ch:
                    pd.DataFrame(tr_ch).to_parquet(ckpt_dir / f"{tid}_traj.parquet", index=False)
                done_rows.extend(r_ch)
                done_trajs.extend(tr_ch)
                completed += 1
                if completed % max(1, len(pending) // 10) == 0 or completed == len(pending):
                    print(
                        f"  [{bench}] {completed}/{len(pending)} chunks ({len(done_rows)} rows, {time.perf_counter() - t0:.1f}s)",
                        flush=True,
                    )

    # Save merged benchmark records & trajectories
    df_rec = pd.DataFrame(done_rows)
    df_rec.to_parquet(out_dir / f"v17_{bench}_records.parquet", index=False, compression="snappy")
    df_rec.to_csv(out_dir / f"v17_{bench}_records.csv", index=False)
    if done_trajs:
        df_tr = pd.DataFrame(done_trajs)
        df_tr.to_parquet(out_dir / f"v17_{bench}_trajectories.parquet", index=False, compression="snappy")
        tr_sum = summarize_trajectories(done_trajs, bench)
        write_csv(out_dir / f"v17_{bench}_trajectory_summary.csv", tr_sum)

    # Summarize benchmark (overall + per-condition on synthetic)
    is_syn = bench.startswith("synthetic_")
    is_prot = bench in ("gb1", "trpb")
    is_wf = bench == "worfbench_cached"
    stratum_k = "condition" if is_syn else ("template_id" if (is_prot or is_wf) else "condition")
    unit_k = ("condition", "seed") if is_syn else ("template_id", "seed")
    hier_k = "template_id" if is_prot else None

    sum_rows: list[dict[str, Any]] = []
    scopes = ("ALL", *[c[0] for c in SYN_CONDITIONS]) if is_syn else ("ALL",)
    for sc in scopes:
        sc_recs = done_rows if sc == "ALL" else [r for r in done_rows if r["condition"] == sc]
        s_list = summarize_ma_cohort(
            sc_recs,
            SIX_POLICIES,
            stratum_key=stratum_k,
            unit_keys=unit_k,
            hierarchical_key=hier_k,
            include_workflow=is_wf,
            n_boot=n_boot,
            boot_seed=202617,
        )
        for sr in s_list:
            sum_rows.append({"phase": phase, "dataset": bench, "scope": sc, **sr})

    write_csv(out_dir / f"v17_{bench}_summary.csv", sum_rows)

    print(f"\n=== Phase {phase} | {bench} (scope=ALL) ===", flush=True)
    for sr in [r for r in sum_rows if r["scope"] == "ALL"]:
        print(
            f"  {sr['acquisition_method']:24s} | cert={100*sr['cert_rate']:5.1f}% | "
            f"RM={sr['restricted_mean']:8.1f} [{sr['rm_ci95_lo']:8.1f},{sr['rm_ci95_hi']:8.1f}] | "
            f"vsCD={sr.get('ratio_vs_cd', float('nan')):.3f}x | vsOS={sr.get('ratio_vs_gpos', float('nan')):.3f}x | "
            f"vsGRI={sr.get('ratio_vs_gri', float('nan')):.3f}x | err={sr['false_certificates']} | "
            f"in%={100*sr['mean_inside_query_frac']:4.1f}% | sg%={100*sr['mean_safeguard_rate']:4.1f}% | "
            f"acq={sr['mean_acq_ms_per_query']:.2f}ms",
            flush=True,
        )
    if is_syn:
        print(f"  --- Condition D_both (overlap=0.75, rho=0.90) ---", flush=True)
        for sr in [r for r in sum_rows if r["scope"] == "D_both"]:
            print(
                f"  {sr['acquisition_method']:24s} | cert={100*sr['cert_rate']:5.1f}% | "
                f"RM={sr['restricted_mean']:8.1f} [{sr['rm_ci95_lo']:8.1f},{sr['rm_ci95_hi']:8.1f}] | "
                f"vsCD={sr.get('ratio_vs_cd', float('nan')):.3f}x | vsOS={sr.get('ratio_vs_gpos', float('nan')):.3f}x",
                flush=True,
            )
    return sum_rows


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--phase", choices=["A", "B"], required=True)
    ap.add_argument("--benchmarks", nargs="+", default=list(ALL_BENCHMARKS))
    ap.add_argument("--out-dir", type=Path, default=None)
    ap.add_argument("--workers", type=int, default=min(32, os.cpu_count() or 8))
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--resume", action="store_true")
    args = ap.parse_args()

    out_dir = (
        args.out_dir
        if args.out_dir is not None
        else DEST_BASE / (f"v17_ma_cd_joint_phase{args.phase.lower()}")
    )
    out_dir.mkdir(parents=True, exist_ok=True)
    n_boot = 1000 if args.smoke else 10000

    config = {
        "experiment": f"v17_ma_cd_joint_phase{args.phase.lower()}",
        "phase": args.phase,
        "git_commit": git_commit_hash(ROOT),
        "smoke": bool(args.smoke),
        "policies": list(SIX_POLICIES),
        "benchmarks": list(args.benchmarks),
        "checkpoints": list(CHECKPOINTS),
        "algorithmic_settings": {
            "witness_pool": "current conic mixture + top-4 posterior mean + top-4 UCB (deduplicated)",
            "quadrature": "9-point standard-normal Gauss-Hermite (exact up to degree 17)",
            "utility_psi": "Psi(h) = min(1, h / beta_t)",
            "query_shortlist_small": "all M candidates when M <= 100 (Synthetic, WorFBench)",
            "query_shortlist_large": "top-8 CD-Joint + top-8 inside-support KG + GP-OS + GP-Root-Info when M > 100 (GB1, TmTrpB)",
            "safeguard": "original mean_contrast > eps/2 safeguard overrides lookahead",
            "safe_schedule": "ma_cd_joint_safe takes mandatory original CD-Joint on even steps (t % 2 == 0)",
            "zero_per_domain_tuning": True,
        },
        "seed_cohorts": {
            "phase_A_disjoint_dev": {
                "synthetic_main64": "seeds 9000..9024 x 4 conds (100)",
                "synthetic_confirm_freq_d8": "seeds 9500..9524 x 4 conds (100)",
                "worfbench_cached": "seeds 790001..790005 x 20 strata (100)",
                "trpb": "seeds 892001..892005 x 21 templates (105)",
                "gb1": "seeds 891001..891010 x 10 orig templates (100)",
            },
            "phase_B_full_expanded": {
                "synthetic_main64": "seeds 2000..2249 x 4 conds (1,000)",
                "synthetic_confirm_freq_d8": "seeds 5000..5249 x 4 conds (1,000)",
                "worfbench_cached": "seeds 780001..780050 x 20 strata (1,000)",
                "trpb": "seeds 802001..802050 x 21 templates (1,050)",
                "gb1": "seeds 801001..801020 x 50 predeclared templates (1,000)",
            },
        },
    }
    (out_dir / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    t_all = time.perf_counter()
    all_summaries: list[dict[str, Any]] = []
    for bench in args.benchmarks:
        all_summaries.extend(
            _run_benchmark(
                bench=bench,
                phase=args.phase,
                out_dir=out_dir,
                workers=args.workers,
                smoke=args.smoke,
                resume=args.resume,
                n_boot=n_boot,
            )
        )

    # Combine all available per-benchmark summaries in out_dir into a master summary CSV
    master_rows: list[dict[str, Any]] = []
    for b in ALL_BENCHMARKS:
        sp = out_dir / f"v17_{b}_summary.csv"
        if sp.is_file():
            master_rows.extend(pd.read_csv(sp).to_dict(orient="records"))
    if master_rows:
        pd.DataFrame(master_rows).to_csv(
            out_dir / f"v17_phase{args.phase.lower()}_all_benchmarks_summary.csv", index=False
        )

    write_manifest(
        out_dir,
        f"v17_ma_cd_joint_phase{args.phase.lower()}",
        smoke=args.smoke,
        elapsed_s=time.perf_counter() - t_all,
        extra={"phase": args.phase, "benchmarks_run": list(args.benchmarks)},
    )
    print(f"\n[v17 Phase {args.phase}] Complete in {time.perf_counter() - t_all:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
