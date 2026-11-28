"""Experiment v15-A: Complete 7-Method Expanded Matched Protein Acquisition Benchmark (GB1 & TmTrpB).

Completes and expands the primary matched Gaussian acquisition benchmark (Condition B,
proper rank-corrected joint credible ellipsoid beta = sqrt(chi2_{M-1, 0.95}), eps = 0.015,
delta = 0.05, cap = 25,000, zero hyperparameter refitting) across ALL SEVEN acquisition methods:
  `gp_ucb`, `gp_ts`, `gp_ei`, `kg`, `gp_os`, `gp_root_info`, `cd_joint`.

Expanded, predeclared, diversity-first cohorts (strictly nesting the original 410-campaign cohort):
  - **GB1 (1,000 campaigns/method):** 50 predeclared templates x 20 seeds (801001..801020):
      * Original 10 templates (`VDGV`, `FDGV`, `LDGV`, `WDGV`, `YDGV`, `IDGV`, `ADGV`, `VDGA`,
        `VWGV`, `LWGV`) — exact nested 200-campaign continuity with Table 24!
      * Plus 40 additional eligible single-site mutants of wild-type `VDGV` (`panel5`, zero
        support containments, M >= 350, K >= 12): the first 10 lexicographically ordered measured
        1-mutants at each of the four sites (V39, D40, G41, V54), chosen strictly independently of
        fitness margins or algorithm performance.
  - **TmTrpB (1,050 campaigns/method):** Complete unselected 21-template neighborhood x 50 seeds
      (802001..802050) — first 10 seeds (802001..802010) give exact 210-campaign continuity!

Also completes the full **7 x 3 Acquisition-Stopping Factorial**:
  - `credible_ellipsoid_chi95` : All 7 methods x 1,000 GB1 + 1,050 TmTrpB campaigns
  - `direct_posterior_risk`    : Valid anytime union-bound MC posterior risk (N_MC=4096, eta=0.01,
                                 delta_post=0.04) evaluated along the exact matched trajectories
                                 for all 7 methods x 1,000 GB1 + 1,050 TmTrpB campaigns
  - `df_emp_bernstein`         : Formal distribution-free Empirical Bernstein stopping across all
                                 7 GP-only policies + DF-coupled `gp_root_info_df` + zero-GP `df_os`
                                 on the exact 410-campaign original cohort (10 GB1 x 20 + 21 TrpB x 10).

Supports crash-safe per-chunk checkpointing (`--resume`) and outputs standardized `.parquet` +
`.csv` campaign records, per-template breakdowns, stratified paired bootstrap 95% CIs, and
template-level hierarchical bootstrap 95% CIs (10,000 resamples).
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
from typing import Any

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from dagcert import (
    DualWitnessCovers,
    JointEllipsoidCertifier,
    SharedGaussianPosterior,
    SupportStructure,
    check_ellipsoid_stopping,
    chi2_credible_beta,
    contrast_ellipsoid_coverage,
    contrast_rank_of_kernel,
    eval_direct_posterior_risk_valid,
    mc_postrisk_schedule,
    select_gp_arm_with_beta,
)
from dagcert.benchmarks import (
    GB1_NPZ_PATH,
    GB1MutationCampaignProblem,
    TrpBMutationCampaignProblem,
    protein_sequence_kernel,
    real_world_problem_diagnostics,
)
from experiment.analysis_v15_stats import (
    SEVEN_METHODS,
    git_commit_hash,
    summarize_paired_cohort,
    write_campaign_records,
    write_csv,
    write_manifest,
)
from experiment.protein_engineering.exp_matched_bed_vs_kg import (
    CAP_ASSAYS,
    DELTA,
    GB1_SEEDS,
    PRIMARY_EPS,
    TRPB_SEEDS,
    _bayes_check_schedule,
    run_gp_root_info_df_and_df_os,
)
from experiment.protein_engineering.exp_real_world_applications import GB1_TEMPLATES as ORIG_GB1_TEMPLATES
from experiment.protein_engineering.exp_real_world_validation import TRPB_TEMPLATES

DEST = ROOT / "results/bayesian_ucd_v1/v15_protein_7method"

EPS = PRIMARY_EPS  # 0.015
MC_DRAWS = 4096
MC_ETA = 0.01
MC_DELTA_POST = 0.04

EXPANDED_GB1_SEEDS: tuple[int, ...] = GB1_SEEDS  # 20 seeds (801001..801020) x 50 templates = 1,000
EXPANDED_TRPB_SEEDS: tuple[int, ...] = tuple(802000 + i for i in range(1, 51))  # 50 seeds x 21 = 1,050

_POLICY_RNG_TAG: dict[str, int] = {
    "gp_ucb": 11,
    "gp_ts": 22,
    "gp_ei": 33,
    "kg": 101,
    "gp_os": 202,
    "gp_root_info": 252,
    "cd_joint": 303,
}


def predeclared_gb1_50_templates() -> tuple[str, ...]:
    """Predeclared, performance-independent 50-template GB1 cohort.

    Includes all 10 original templates plus the first 10 lexicographically ordered eligible
    measured single-site mutants of WT `VDGV` at each of the 4 mutated sites (V39, D40, G41, V54)
    satisfying `panel5` zero support containments, `M >= 350`, and `K >= 12`.
    """
    gb1_npz = np.load(GB1_NPZ_PATH, allow_pickle=True)
    variants = set(str(v) for v in gb1_npz["variants"])
    wt = "VDGV"
    aas = "ACDEFGHIKLMNPQRSTVWY"
    chosen = list(ORIG_GB1_TEMPLATES)
    chosen_set = set(chosen)
    for pos in range(4):
        added = 0
        for aa in aas:
            if aa == wt[pos]:
                continue
            seq = wt[:pos] + aa + wt[pos + 1 :]
            if seq in chosen_set or seq not in variants:
                continue
            prob = GB1MutationCampaignProblem(start_seq=seq, max_edits=3, panel="panel5")
            diag = real_world_problem_diagnostics(prob)
            if diag["containment_pairs"] == 0 and diag["leaves"] >= 350 and diag["root_actions"] >= 12:
                chosen.append(seq)
                chosen_set.add(seq)
                added += 1
                if added == 10:
                    break
        assert added == 10, f"Expected 10 extra templates at position {pos}, found {added}"
    assert len(chosen) == 50
    return tuple(chosen)


def _load_protein_problem(landscape: str, start_seq: str) -> tuple:
    if landscape == "gb1":
        prob = GB1MutationCampaignProblem(start_seq=start_seq, max_edits=3, panel="panel5", noise_model="calibrated")
        prior_m, obs_s = 0.28, 0.16
    else:
        prob = TrpBMutationCampaignProblem(start_seq=start_seq, max_edits=3, panel="panel5", noise_model="low_var_uniform")
        prior_m, obs_s = 0.30, 0.08 / math.sqrt(3.0)

    diag = real_world_problem_diagnostics(prob)
    ratio = float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"]))
    regime_tag = "epistatic_ridge" if ratio >= 10.0 else "single_peak"

    ss = SupportStructure(prob.graph)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    true_means_vec = np.array([float(prob.means[z]) for z in ss.leaves], dtype=np.float64)
    is_eps_opt_leaf = (opt_mu - true_means_vec) <= (EPS + 1e-12)

    seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
    kernel = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
    r_rank = contrast_rank_of_kernel(kernel)
    l2a: list[list[int]] = [[] for _ in range(ss.m)]
    for a, sup in enumerate(ss.supports):
        for idx in sup:
            l2a[int(idx)].append(a)
    return prob, ss, l2a, kernel, prior_m, obs_s, regrets, true_means_vec, is_eps_opt_leaf, r_rank, regime_tag


def _protein_stream_worker(task: tuple) -> tuple[str, list[dict[str, Any]]]:
    """Run one `(landscape, start_seq, policy, seeds_chunk)` task with B_chi95 + E_postrisk (+ optional D_df_eb)."""
    task_id, landscape, start_seq, policy, seeds, cap, mc_draws, orig_tmpl_set, orig_seed_set, run_df_on_orig = task
    prob, ss, l2a, kernel, prior_m, obs_s, regrets, true_means_vec, is_eps_opt_leaf, r_rank, regime_tag = (
        _load_protein_problem(landscape, start_seq)
    )
    beta_95 = chi2_credible_beta(r_rank, 1.0 - DELTA)
    rows: list[dict[str, Any]] = []

    def _make_row(
        *,
        seed: int,
        stop_rule: str,
        steps: int,
        certified: bool,
        action: int,
        reg_bound: float | None,
        beta_val: float | None,
        jcov: bool | None,
        disc_step: int | None,
        acq_s: float,
        cert_s: float,
        tot_s: float,
        subopt_pulls: int,
        total_pulls: int,
        is_orig: bool,
    ) -> dict[str, Any]:
        tr = float(regrets[action])
        rcov = bool((reg_bound is None) or (tr <= reg_bound + 1e-9))
        return {
            "dataset": landscape,
            "condition": regime_tag,
            "domain": landscape,
            "template_id": start_seq,
            "seed": int(seed),
            "acquisition_method": policy,
            "stopping_rule": stop_rule,
            "epsilon": EPS,
            "delta": DELTA,
            "budget": int(cap),
            "n_evaluations": int(steps) if certified else int(cap),
            "certified": bool(certified),
            "recommended_root": int(action),
            "true_root_regret": round(tr, 6),
            "false_certificate": bool(certified and tr > EPS + 1e-12),
            "first_epsilon_optimal_discovery": int(disc_step) if disc_step is not None else int(cap),
            "discovered": bool(disc_step is not None),
            "joint_coverage": jcov,
            "root_regret_bound_coverage": rcov,
            "cert_regret_bound": round(float(reg_bound), 6) if (reg_bound is not None and math.isfinite(reg_bound)) else None,
            "contrast_rank": int(r_rank),
            "beta_at_stop": round(float(beta_val), 4) if beta_val is not None else None,
            "total_tokens": 0.0,
            "heldout_f1": None,
            "heldout_regret": None,
            "acquisition_time_s": round(float(acq_s), 5),
            "certificate_time_s": round(float(cert_s), 5),
            "total_runtime_s": round(float(tot_s), 5),
            "safeguard_activations": 0,
            "mean_mixture_support": 1.0,
            "proxy_query_frac": round(subopt_pulls / max(1, total_pulls), 5),
            "is_orig_cohort": bool(is_orig),
        }

    for seed in seeds:
        is_orig = (start_seq in orig_tmpl_set) and (seed in orig_seed_set)
        track_df = bool(run_df_on_orig and is_orig)

        post = SharedGaussianPosterior(kernel, prior_m, obs_s, delta=DELTA, contrast_rank=r_rank)
        certifier = JointEllipsoidCertifier(ss, epsilon=EPS, solver="colgen_lazy", exact_linear_mean=False)
        df_mon = (
            DualWitnessCovers(prob.graph, delta=DELTA, schedule="emp_bernstein", layout="best", track_separation=True)
            if track_df
            else None
        )
        oracle = prob.oracle(seed)
        tag = _POLICY_RNG_TAG[policy]
        seq_code = sum((i + 1) * ord(ch) for i, ch in enumerate(start_seq))
        acq_rng = np.random.default_rng((seed * 1000003 + tag * 9176 + seq_code) & 0xFFFFFFFFFFFFFFFF)
        mc_rng = np.random.default_rng((seed * 1000003 + tag * 7919 + 42) & 0xFFFFFFFFFFFFFFFF)

        rec_b: dict[str, Any] | None = None
        rec_e: dict[str, Any] | None = None
        rec_d: dict[str, Any] | None = None if track_df else {}

        t_start = time.perf_counter()
        acq_s = 0.0
        cert_s_b = 0.0
        cert_s_e = 0.0
        cert_s_d = 0.0
        mc_check_idx = 0
        disc_step: int | None = None
        subopt_pulls = 0

        for step in range(1, cap + 1):
            t_done = step - 1

            # 1. Formal DF Empirical Bernstein (on original 410-campaign factorial cohort)
            if df_mon is not None and rec_d is None and t_done > 0:
                td0 = time.perf_counter()
                act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
                cert_s_d += time.perf_counter() - td0
                if reg_df <= EPS:
                    rec_d = _make_row(
                        seed=seed, stop_rule="df_emp_bernstein", steps=t_done, certified=True,
                        action=int(act_df), reg_bound=float(reg_df), beta_val=None, jcov=True,
                        disc_step=disc_step, acq_s=acq_s, cert_s=cert_s_d,
                        tot_s=time.perf_counter() - t_start, subopt_pulls=subopt_pulls,
                        total_pulls=t_done, is_orig=is_orig,
                    )

            # 2. Proper 95% joint contrast credible ellipsoid (exact v14 Condition B protocol)
            if rec_b is None and t_done > 0 and _bayes_check_schedule(t_done, cap):
                tb0 = time.perf_counter()
                ok_b, act_b, reg_b = check_ellipsoid_stopping(
                    certifier, ss, post.mean, post.sigma_mat, beta_95, EPS
                )
                cert_s_b += time.perf_counter() - tb0
                if ok_b:
                    jcov_b, _ = contrast_ellipsoid_coverage(post.mean, post.sigma_mat, beta_95, true_means_vec)
                    rec_b = _make_row(
                        seed=seed, stop_rule="credible_ellipsoid_chi95", steps=t_done, certified=True,
                        action=int(act_b), reg_bound=float(reg_b), beta_val=beta_95, jcov=jcov_b,
                        disc_step=disc_step, acq_s=acq_s, cert_s=cert_s_b,
                        tot_s=time.perf_counter() - t_start, subopt_pulls=subopt_pulls,
                        total_pulls=t_done, is_orig=is_orig,
                    )

            # 3. Valid anytime union-bound Monte Carlo direct posterior-risk check
            if rec_e is None and t_done > 0 and mc_postrisk_schedule(t_done, cap):
                mc_check_idx += 1
                te0 = time.perf_counter()
                ok_e, act_e, _, _ = eval_direct_posterior_risk_valid(
                    post.mean, post.sigma_mat, ss.supports, EPS, mc_check_idx,
                    n_mc=mc_draws, eta=MC_ETA, delta_post=MC_DELTA_POST, rng=mc_rng,
                )
                cert_s_e += time.perf_counter() - te0
                if ok_e:
                    rec_e = _make_row(
                        seed=seed, stop_rule="direct_posterior_risk", steps=t_done, certified=True,
                        action=int(act_e), reg_bound=EPS, beta_val=None, jcov=None,
                        disc_step=disc_step, acq_s=acq_s, cert_s=cert_s_e,
                        tot_s=time.perf_counter() - t_start, subopt_pulls=subopt_pulls,
                        total_pulls=t_done, is_orig=is_orig,
                    )

            if rec_b is not None and rec_e is not None and rec_d is not None:
                break

            ta0 = time.perf_counter()
            arm = select_gp_arm_with_beta(
                policy, ss, l2a, post, certifier, beta=beta_95, epsilon=EPS, step=step, delta=DELTA, rng=acq_rng
            )
            acq_s += time.perf_counter() - ta0

            leaf = ss.leaves[arm]
            y = float(oracle.sample(leaf))
            if is_eps_opt_leaf[arm]:
                if disc_step is None:
                    disc_step = step
            else:
                subopt_pulls += 1

            post.observe(arm, y)
            if df_mon is not None:
                df_mon.step(leaf, y)

        tot_end = time.perf_counter() - t_start
        emp_a = int(np.argmax([float(np.max(post.mean[sup])) for sup in ss.supports]))
        if rec_b is None:
            tb0 = time.perf_counter()
            ok_b, act_b, reg_b = check_ellipsoid_stopping(
                certifier, ss, post.mean, post.sigma_mat, beta_95, EPS
            )
            cert_s_b += time.perf_counter() - tb0
            jcov_b, _ = contrast_ellipsoid_coverage(post.mean, post.sigma_mat, beta_95, true_means_vec)
            rec_b = _make_row(
                seed=seed, stop_rule="credible_ellipsoid_chi95", steps=cap, certified=bool(ok_b),
                action=int(act_b) if ok_b else emp_a, reg_bound=float(reg_b), beta_val=beta_95,
                jcov=jcov_b, disc_step=disc_step, acq_s=acq_s, cert_s=cert_s_b, tot_s=tot_end,
                subopt_pulls=subopt_pulls, total_pulls=cap, is_orig=is_orig,
            )
        if rec_e is None:
            mc_check_idx += 1
            te0 = time.perf_counter()
            ok_e, act_e, _, _ = eval_direct_posterior_risk_valid(
                post.mean, post.sigma_mat, ss.supports, EPS, mc_check_idx,
                n_mc=mc_draws, eta=MC_ETA, delta_post=MC_DELTA_POST, rng=mc_rng,
            )
            cert_s_e += time.perf_counter() - te0
            rec_e = _make_row(
                seed=seed, stop_rule="direct_posterior_risk", steps=cap, certified=bool(ok_e),
                action=int(act_e) if ok_e else emp_a, reg_bound=EPS if ok_e else None,
                beta_val=None, jcov=None, disc_step=disc_step, acq_s=acq_s, cert_s=cert_s_e,
                tot_s=tot_end, subopt_pulls=subopt_pulls, total_pulls=cap, is_orig=is_orig,
            )
        rows.extend((rec_b, rec_e))
        if df_mon is not None:
            if rec_d is None:
                td0 = time.perf_counter()
                act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
                cert_s_d += time.perf_counter() - td0
                rec_d = _make_row(
                    seed=seed, stop_rule="df_emp_bernstein", steps=cap, certified=bool(reg_df <= EPS),
                    action=int(act_df), reg_bound=float(reg_df), beta_val=None, jcov=True,
                    disc_step=disc_step, acq_s=acq_s, cert_s=cert_s_d, tot_s=tot_end,
                    subopt_pulls=subopt_pulls, total_pulls=cap, is_orig=is_orig,
                )
            rows.append(rec_d)
    return task_id, rows


def _df_ref_worker(task: tuple) -> tuple[str, list[dict[str, Any]]]:
    """Run explicitly DF-coupled `gp_root_info_df` and zero-GP `df_os` on the 410 original cohort."""
    task_id, landscape, start_seq, seeds, cap = task
    prob, ss, _, kernel, prior_m, obs_s, regrets, true_means_vec, _, r_rank, regime_tag = _load_protein_problem(
        landscape, start_seq
    )
    out: list[dict[str, Any]] = []
    for seed in seeds:
        base = {
            "unit_id": f"{landscape}_{start_seq}_s{seed}",
            "landscape": landscape,
            "start_seq": start_seq,
            "template_regime": regime_tag,
            "seed": int(seed),
            "m_leaves": ss.m,
            "k_actions": ss.k,
        }
        ref_rows = run_gp_root_info_df_and_df_os(
            prob, ss, kernel, prior_m, obs_s, regrets, seed, (EPS,), cap, DELTA, landscape, start_seq, regime_tag
        )
        for rr in ref_rows:
            out.append(
                {
                    "dataset": landscape,
                    "condition": regime_tag,
                    "domain": landscape,
                    "template_id": start_seq,
                    "seed": int(seed),
                    "acquisition_method": str(rr["method"]),
                    "stopping_rule": "df_emp_bernstein",
                    "epsilon": EPS,
                    "delta": DELTA,
                    "budget": int(cap),
                    "n_evaluations": int(rr["steps"]) if rr["certified"] else int(cap),
                    "certified": bool(rr["certified"]),
                    "recommended_root": int(rr["action"]),
                    "true_root_regret": float(rr["true_regret"]),
                    "false_certificate": bool(rr["false_cert"]),
                    "first_epsilon_optimal_discovery": int(rr["steps"]),
                    "discovered": bool(rr["certified"]),
                    "joint_coverage": True,
                    "root_regret_bound_coverage": True,
                    "cert_regret_bound": EPS if rr["certified"] else None,
                    "contrast_rank": int(r_rank),
                    "beta_at_stop": None,
                    "total_tokens": 0.0,
                    "heldout_f1": None,
                    "heldout_regret": None,
                    "acquisition_time_s": float(rr["acq_time_s"]),
                    "certificate_time_s": float(rr["cert_time_s"]),
                    "total_runtime_s": float(rr["total_time_s"]),
                    "safeguard_activations": 0,
                    "mean_mixture_support": 1.0,
                    "proxy_query_frac": 0.0,
                    "is_orig_cohort": True,
                }
            )
    return task_id, out


def summarize(out_dir: Path, n_boot: int = 10000) -> None:
    df = pd.read_parquet(out_dir / "v15_protein_7method_records.parquet")
    recs = df.to_dict(orient="records")
    df_methods = (*SEVEN_METHODS, "gp_root_info_df", "df_os")

    summary_rows: list[dict[str, Any]] = []
    per_tmpl_rows: list[dict[str, Any]] = []

    for land in ("gb1", "trpb"):
        l_recs = [r for r in recs if r["dataset"] == land]
        if not l_recs:
            continue
        for tag, filt in (("expanded", lambda r: True), ("orig_cohort", lambda r: bool(r["is_orig_cohort"]))):
            for srule, mlist in (
                ("credible_ellipsoid_chi95", SEVEN_METHODS),
                ("direct_posterior_risk", SEVEN_METHODS),
                ("df_emp_bernstein", df_methods),
            ):
                sub = [r for r in l_recs if r["stopping_rule"] == srule and filt(r)]
                if not sub:
                    continue
                if srule == "df_emp_bernstein" and tag == "expanded":
                    # DF factorial runs on the exact original 410 cohort; skip duplicate tag
                    continue
                s_rows = summarize_paired_cohort(
                    sub,
                    mlist,
                    stratum_key="template_id",
                    unit_keys=("template_id", "seed"),
                    hierarchical_key="template_id",
                    n_boot=n_boot,
                    boot_seed=202630 if land == "gb1" else 202631,
                )
                for row in s_rows:
                    summary_rows.append({"landscape": land, "cohort": tag, "stopping_rule": srule, **row})

        # Per-template breakdown for primary B_chi95 expanded cohort
        sub_b = [r for r in l_recs if r["stopping_rule"] == "credible_ellipsoid_chi95"]
        tmpls = sorted(set(str(r["template_id"]) for r in sub_b))
        for tmpl in tmpls:
            t_recs = [r for r in sub_b if r["template_id"] == tmpl]
            t_sum = summarize_paired_cohort(
                t_recs,
                SEVEN_METHODS,
                stratum_key="template_id",
                unit_keys=("template_id", "seed"),
                n_boot=min(2000, n_boot),
                boot_seed=202635,
            )
            for row in t_sum:
                per_tmpl_rows.append(
                    {
                        "landscape": land,
                        "template_id": tmpl,
                        "is_orig_template": bool(any(bool(r["is_orig_cohort"]) for r in t_recs)),
                        **row,
                    }
                )

    write_csv(out_dir / "v15_protein_7method_summary.csv", summary_rows)
    write_csv(out_dir / "v15_protein_7method_per_template.csv", per_tmpl_rows)

    print("\n=== v15 Protein 7-Method Summary (B_chi95 & E_postrisk & D_df_eb) ===")
    sdf = pd.read_csv(out_dir / "v15_protein_7method_summary.csv")
    for (land, tag, srule), grp in sdf.groupby(["landscape", "cohort", "stopping_rule"], sort=False):
        print(f"\n  [{land.upper()} | {tag} | {srule}]")
        for _, r in grp.iterrows():
            jstr = f"{100*r['joint_coverage']:.1f}%" if pd.notna(r["joint_coverage"]) else "  ---"
            h_lo = r.get("hier_rm_ci95_lo", float("nan"))
            h_hi = r.get("hier_rm_ci95_hi", float("nan"))
            hstr = f" hier[{h_lo:.0f},{h_hi:.0f}]" if pd.notna(h_lo) else ""
            print(
                f"    {r['acquisition_method']:16s} | n={int(r['n_campaigns']):4d} | cert={100*r['cert_rate']:5.1f}% | "
                f"RM={r['restricted_mean']:7.1f} [{r['rm_ci95_lo']:7.1f},{r['rm_ci95_hi']:7.1f}]{hstr} | "
                f"m/CD={r['ratio_vs_cd'] if pd.notna(r['ratio_vs_cd']) else 0:.2f}x | err={int(r['false_certificates'])} | jcov={jstr}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--landscapes", choices=("all", "gb1", "trpb"), default="all")
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--resume", action="store_true", help="Resume from existing checkpoint JSONL")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--workers", type=int, default=min(36, os.cpu_count() or 8))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir, n_boot=1000 if args.smoke else 10000)
        return

    t0 = time.perf_counter()
    gb1_tmpls = ("VDGV", "FDGV") if args.smoke else predeclared_gb1_50_templates()
    trpb_tmpls = ("VFVS", "AFVS") if args.smoke else TRPB_TEMPLATES
    gb1_seeds = EXPANDED_GB1_SEEDS[:2] if args.smoke else EXPANDED_GB1_SEEDS
    trpb_seeds = EXPANDED_TRPB_SEEDS[:2] if args.smoke else EXPANDED_TRPB_SEEDS
    cap = 2000 if args.smoke else CAP_ASSAYS
    mc_draws = 512 if args.smoke else MC_DRAWS

    orig_gb1_set = set(ORIG_GB1_TEMPLATES)
    orig_trpb_set = set(TRPB_TEMPLATES)
    orig_gb1_seeds = set(GB1_SEEDS)
    orig_trpb_seeds = set(TRPB_SEEDS)

    config = {
        "experiment": "v15_protein_7method",
        "git_commit": git_commit_hash(ROOT),
        "smoke": bool(args.smoke),
        "epsilon": EPS,
        "delta": DELTA,
        "budget_cap": cap,
        "gb1_templates_50": list(gb1_tmpls),
        "gb1_orig_templates_10": list(ORIG_GB1_TEMPLATES),
        "gb1_selection_rule": "Original 10 templates + first 10 lexicographically ordered eligible measured 1-site mutants of WT VDGV at each of 4 sites (V39, D40, G41, V54; panel5, zero containment, M>=350, K>=12); zero algorithm-outcome peeking",
        "gb1_seeds": list(gb1_seeds),
        "trpb_templates_21": list(trpb_tmpls),
        "trpb_seeds": list(trpb_seeds),
        "trpb_orig_seeds_10": list(TRPB_SEEDS),
        "working_gp_hyperparameters": {
            "gb1": {"prior_mean": 0.28, "obs_std": 0.16},
            "trpb": {"prior_mean": 0.30, "obs_std": round(0.08 / math.sqrt(3.0), 8)},
            "kernel": "protein_sequence_kernel(prior_scale=0.22, lengthscale=3.0, nugget=0.02)",
            "credible_radius": "sqrt(chi2_{M-1, 0.95})",
            "hyperparameter_refitting": "disabled",
        },
        "methods": list(SEVEN_METHODS),
        "df_factorial_cohort": "Original 410 paired campaigns (10 GB1 x 20 seeds + 21 TmTrpB x 10 seeds) across all 7 GP-only methods + gp_root_info_df + df_os",
    }
    (out_dir / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    ckpt_path = out_dir / "v15_protein_checkpoint.jsonl"
    done_ids: set[str] = set()
    all_rows: list[dict[str, Any]] = []
    if args.resume and ckpt_path.is_file():
        with ckpt_path.open("r", encoding="utf-8") as fh:
            for line in fh:
                if line.strip():
                    obj = json.loads(line)
                    done_ids.add(obj["task_id"])
                    all_rows.extend(obj["rows"])
        print(f"[v15 Protein] Resumed {len(done_ids)} completed tasks ({len(all_rows)} rows).", flush=True)
    elif not args.resume and ckpt_path.is_file():
        ckpt_path.unlink()

    # Build tasks: schedule heavy policies (`kg`, `cd_joint`) first for best load balancing across workers!
    ordered_policies = ("kg", "cd_joint", "gp_ts", "gp_os", "gp_ei", "gp_root_info", "gp_ucb")
    stream_tasks: list[tuple] = []
    df_ref_tasks: list[tuple] = []

    if args.landscapes in ("all", "trpb"):
        chunk_s = 2 if args.smoke else 5
        for pol in ordered_policies:
            for tmpl in trpb_tmpls:
                for i in range(0, len(trpb_seeds), chunk_s):
                    sc = trpb_seeds[i : i + chunk_s]
                    tid = f"trpb__{tmpl}__{pol}__s{sc[0]}_{sc[-1]}"
                    if tid not in done_ids:
                        stream_tasks.append(
                            (tid, "trpb", tmpl, pol, sc, cap, mc_draws, orig_trpb_set, orig_trpb_seeds, True)
                        )
        for tmpl in trpb_tmpls:
            orig_s = [s for s in trpb_seeds if s in orig_trpb_seeds]
            if orig_s:
                tid = f"trpb__{tmpl}__df_refs__s{orig_s[0]}_{orig_s[-1]}"
                if tid not in done_ids:
                    df_ref_tasks.append((tid, "trpb", tmpl, orig_s, cap))

    if args.landscapes in ("all", "gb1"):
        chunk_s = 2 if args.smoke else 4
        for pol in ordered_policies:
            for tmpl in gb1_tmpls:
                for i in range(0, len(gb1_seeds), chunk_s):
                    sc = gb1_seeds[i : i + chunk_s]
                    tid = f"gb1__{tmpl}__{pol}__s{sc[0]}_{sc[-1]}"
                    if tid not in done_ids:
                        stream_tasks.append(
                            (tid, "gb1", tmpl, pol, sc, cap, mc_draws, orig_gb1_set, orig_gb1_seeds, True)
                        )
        for tmpl in gb1_tmpls:
            if tmpl in orig_gb1_set:
                orig_s = [s for s in gb1_seeds if s in orig_gb1_seeds]
                if orig_s:
                    tid = f"gb1__{tmpl}__df_refs__s{orig_s[0]}_{orig_s[-1]}"
                    if tid not in done_ids:
                        df_ref_tasks.append((tid, "gb1", tmpl, orig_s, cap))

    total_todo = len(stream_tasks) + len(df_ref_tasks)
    print(
        f"[v15 Protein] Launching {len(stream_tasks)} stream chunks + {len(df_ref_tasks)} DF-ref chunks "
        f"(landscapes={args.landscapes}, cap={cap}) on {args.workers} workers...",
        flush=True,
    )
    ctx = mp.get_context("spawn")
    done_now = 0
    with ckpt_path.open("a", encoding="utf-8") as ck_fh:
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
            futs = [ex.submit(_protein_stream_worker, t) for t in stream_tasks] + [
                ex.submit(_df_ref_worker, t) for t in df_ref_tasks
            ]
            for fut in as_completed(futs):
                tid, rows = fut.result()
                all_rows.extend(rows)
                ck_fh.write(json.dumps({"task_id": tid, "rows": rows}) + "\n")
                ck_fh.flush()
                done_now += 1
                if done_now % 50 == 0 or done_now == total_todo:
                    print(
                        f"  [Protein] {done_now}/{total_todo} chunks done ({len(all_rows)} rows, {time.perf_counter() - t0:.1f}s)",
                        flush=True,
                    )

    write_campaign_records(out_dir, "v15_protein_7method_records", all_rows)
    # Remove intermediate checkpoint once clean Parquet+CSV are written
    if ckpt_path.is_file():
        ckpt_path.unlink()

    summarize(out_dir, n_boot=1000 if args.smoke else 10000)
    write_manifest(
        out_dir,
        "v15_protein_7method",
        smoke=args.smoke,
        elapsed_s=time.perf_counter() - t0,
        extra={
            "n_total_rows": len(all_rows),
            "n_gb1_templates": len(gb1_tmpls),
            "n_gb1_seeds": len(gb1_seeds),
            "n_trpb_templates": len(trpb_tmpls),
            "n_trpb_seeds": len(trpb_seeds),
        },
    )
    print(f"[v15 Protein] Complete in {time.perf_counter() - t0:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
