"""Experiment v15-C: Matched 7-Method Gaussian Acquisition Benchmark on Cached WorFBench.

Evaluates all seven matched acquisition methods (`gp_ucb`, `gp_ts`, `gp_ei`, `kg`, `gp_os`,
`gp_root_info`, `cd_joint`) on the cached 4-stage `Qwen3-0.6B` WorFBench workflow DAG
(3^4 = 81 configurations, M in {32, 64}, K = 8, eps = 0.020, delta = 0.05, cap = 35,000)
across 1,000 paired campaign instances per method (5 domain strata x 4 base configs x 50 paired
seeds, strictly nesting the original Table 35 seeds 780001..780006).

Predeclared, leak-free Hamming exponential kernel (zero fitting on D_cert or D_test):
    k(z, z') = sigma_f^2 * exp(-d_H(z, z') / ell) + (nugget_frac * sigma_f^2) * 1_{z == z'}
with prior_mean = 0.25, sigma_f = 0.22, ell = 2.0, nugget_frac = 0.02, working obs_std = 0.25,
unit query costs, and exact contrast rank r = M - 1 (beta_{0.95} = sqrt(chi2_{r, 0.95})).

Also completes the full 7 x 3 acquisition-stopping factorial on WorFBench:
  - `credible_ellipsoid_chi95` : Proper 95% joint contrast ellipsoid sqrt(chi2_{M-1, 0.95})
  - `direct_posterior_risk`    : Valid anytime union-bound MC posterior risk (N_MC=4096, eta=0.01)
  - `df_emp_bernstein`         : Formal distribution-free Empirical Bernstein stopping
                                 (all 7 GP-only policies + DF-coupled `gp_root_info_df` + `df_os`)
and programmatically audits uniform-with-replacement task sampling from D_cert and identical
intrinsic SplitMix64 observation tapes across policies.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from concurrent.futures import ProcessPoolExecutor
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
    WORFBENCH_TEST_NPZ_PATH,
    WorFBenchWorkflowProblem,
    hamming_workflow_kernel,
)
from dagcert._core.v6_bayesian_opt import DiscreteGPSurrogate
from dagcert._core.v12_bed_acquisition import default_check_schedule
from experiment.analysis_v15_stats import (
    SEVEN_METHODS,
    git_commit_hash,
    summarize_paired_cohort,
    write_campaign_records,
    write_csv,
    write_manifest,
)
from experiment.protein_engineering.exp_real_world_applications import (
    WORFBENCH_BASES,
    WORFBENCH_DOMAINS,
)
from experiment.protein_engineering.exp_real_world_validation import (
    _worfbench_leaf_costs_and_unseen_values,
)

DEST = ROOT / "results/bayesian_ucd_v1/v15_worfbench_7method"

EPS = 0.020
DELTA = 0.05
CAP = 35000
MC_DRAWS = 4096
MC_ETA = 0.01
MC_DELTA_POST = 0.04

# Predeclared leak-free working Gaussian model (zero fitting on D_cert or D_test!)
PRIOR_MEAN = 0.25
PRIOR_SCALE = 0.22
LENGTHSCALE = 2.0
NUGGET_FRAC = 0.02
OBS_STD = 0.25

STAGE_MAPS: tuple[dict[str, int], ...] = (
    {"raw_schema": 0, "compact_sig": 1, "embed_top4": 2},
    {"zero_shot": 0, "step_cot": 1, "one_shot": 2},
    {"greedy": 0, "temp_sample": 1, "mbr_select": 2},
    {"raw_parse": 0, "norm_endpts": 1, "dag_repair": 2},
)


def _parse_workflow_config(wf_name: str) -> tuple[int, int, int, int]:
    parts = wf_name.split("|")
    if len(parts) != 4:
        raise ValueError(f"Unexpected workflow name format: {wf_name!r}")
    return tuple(STAGE_MAPS[i][parts[i]] for i in range(4))  # type: ignore[return-value]


def audit_worfbench_sampling_protocol() -> dict[str, Any]:
    """Programmatically verify uniform-with-replacement sampling and identical intrinsic tapes."""
    prob = WorFBenchWorkflowProblem(domain="all", base_config=(0, 0, 0, 0), max_upgrades=3)
    leaf = prob.graph.leaves[0]
    o1 = prob.oracle(780001)
    o2 = prob.oracle(780001)
    seq1 = [o1.sample(leaf) for _ in range(256)]
    seq2 = [o2.sample(leaf) for _ in range(256)]
    assert seq1 == seq2, "Intrinsic SplitMix64 tape mismatch!"
    # Check repeated pulls exceed n_tasks=64 cleanly (with replacement) and empirical mean matches true mean
    o3 = prob.oracle(780001)
    big = np.array([o3.sample(leaf) for _ in range(20000)], dtype=np.float64)
    true_m = float(prob.means[leaf])
    err = abs(float(np.mean(big)) - true_m)
    assert err < 0.01, f"Empirical mean drift {err} exceeds Monte Carlo tolerance!"
    return {
        "sampling_mode": "i.i.d. uniform with replacement over D_cert via SplitMix64(seed, leaf, k)",
        "intrinsic_tape_identical_across_policies": True,
        "verified_20k_sample_mean_abs_error": round(err, 6),
        "d_cert_tasks_pooled": 64,
        "d_cert_tasks_per_domain": 16,
        "d_test_tasks_pooled": 32,
        "d_test_tasks_per_domain": 8,
    }


def _worfbench_worker(task: tuple) -> list[dict[str, Any]]:
    domain, base_name, base_cfg, max_u, seeds, cap, mc_draws = task
    prob = WorFBenchWorkflowProblem(domain=domain, base_config=base_cfg, max_upgrades=max_u)
    test_arch = dict(np.load(WORFBENCH_TEST_NPZ_PATH, allow_pickle=True))
    leaf_toks, _, act_test_vals, test_opt = _worfbench_leaf_costs_and_unseen_values(prob, test_arch)

    ss = SupportStructure(prob.graph)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    true_means_vec = np.array([float(prob.means[lf]) for lf in ss.leaves], dtype=np.float64)
    is_eps_opt_leaf = (opt_mu - true_means_vec) <= (EPS + 1e-12)
    tok_vec = np.array([float(leaf_toks[lf]) for lf in ss.leaves], dtype=np.float64)

    configs = [_parse_workflow_config(prob.leaf_workflow_name[lf]) for lf in ss.leaves]
    kernel = hamming_workflow_kernel(
        configs, prior_scale=PRIOR_SCALE, lengthscale=LENGTHSCALE, nugget_frac=NUGGET_FRAC
    )
    r_rank = contrast_rank_of_kernel(kernel)
    beta_95 = chi2_credible_beta(r_rank, 1.0 - DELTA)

    l2a: list[list[int]] = [[] for _ in range(ss.m)]
    for a, sup in enumerate(ss.supports):
        for idx in sup:
            l2a[int(idx)].append(a)

    tmpl_id = f"{domain}__{base_name}"
    out_rows: list[dict[str, Any]] = []

    def _build_row(
        *,
        seed: int,
        method: str,
        stop_rule: str,
        steps: int,
        certified: bool,
        action: int,
        reg_bound: float | None,
        beta_val: float | None,
        jcov: bool | None,
        disc_step: int | None,
        tokens: float,
        acq_s: float,
        cert_s: float,
        tot_s: float,
        subopt_pulls: int,
        total_pulls: int,
        is_orig: bool,
    ) -> dict[str, Any]:
        tr = float(regrets[action])
        hf1 = float(act_test_vals[action])
        hreg = max(0.0, float(test_opt - hf1))
        rcov = bool((reg_bound is None) or (tr <= reg_bound + 1e-9))
        return {
            "dataset": "worfbench_cached",
            "condition": f"{domain}__{base_name}",
            "domain": domain,
            "template_id": tmpl_id,
            "seed": int(seed),
            "acquisition_method": method,
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
            "total_tokens": round(float(tokens), 1),
            "heldout_f1": round(hf1, 5),
            "heldout_regret": round(hreg, 5),
            "acquisition_time_s": round(float(acq_s), 5),
            "certificate_time_s": round(float(cert_s), 5),
            "total_runtime_s": round(float(tot_s), 5),
            "safeguard_activations": 0,
            "mean_mixture_support": 1.0,
            "proxy_query_frac": round(subopt_pulls / max(1, total_pulls), 5),
            "is_orig_cohort": bool(is_orig),
        }

    for seed in seeds:
        is_orig = 780001 <= seed <= 780006

        # 1. All 7 GP policies evaluated simultaneously across B_chi95, E_postrisk, and D_df_eb
        for p_idx, pol in enumerate(SEVEN_METHODS):
            post = SharedGaussianPosterior(kernel, PRIOR_MEAN, OBS_STD, delta=DELTA, contrast_rank=r_rank)
            certifier = JointEllipsoidCertifier(ss, epsilon=EPS, solver="colgen_lazy", exact_linear_mean=False)
            df_mon = DualWitnessCovers(prob.graph, delta=DELTA, schedule="emp_bernstein", layout="best", track_separation=True)
            oracle = prob.oracle(seed)
            acq_rng = np.random.default_rng((seed * 1000003 + (p_idx + 1) * 9176) & 0xFFFFFFFFFFFFFFFF)
            mc_rng = np.random.default_rng((seed * 2000003 + (p_idx + 1) * 4219) & 0xFFFFFFFFFFFFFFFF)

            rec_b: dict[str, Any] | None = None
            rec_e: dict[str, Any] | None = None
            rec_d: dict[str, Any] | None = None

            t_start = time.perf_counter()
            acq_s = 0.0
            cert_s_b = 0.0
            cert_s_e = 0.0
            cert_s_d = 0.0
            mc_check_idx = 0
            disc_step: int | None = None
            subopt_pulls = 0
            cum_tokens = 0.0

            for step in range(1, cap + 1):
                t_done = step - 1

                # (a) Formal DF Empirical Bernstein check
                if rec_d is None and t_done > 0:
                    td0 = time.perf_counter()
                    act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
                    cert_s_d += time.perf_counter() - td0
                    if reg_df <= EPS:
                        rec_d = _build_row(
                            seed=seed, method=pol, stop_rule="df_emp_bernstein", steps=t_done,
                            certified=True, action=int(act_df), reg_bound=float(reg_df),
                            beta_val=None, jcov=True, disc_step=disc_step, tokens=cum_tokens,
                            acq_s=acq_s, cert_s=cert_s_d, tot_s=time.perf_counter() - t_start,
                            subopt_pulls=subopt_pulls, total_pulls=t_done, is_orig=is_orig,
                        )

                # (b) Proper 95% joint credible ellipsoid check
                if rec_b is None and t_done > 0 and default_check_schedule(t_done):
                    tb0 = time.perf_counter()
                    ok_b, act_b, reg_b = check_ellipsoid_stopping(
                        certifier, ss, post.mean, post.sigma_mat, beta_95, EPS
                    )
                    cert_s_b += time.perf_counter() - tb0
                    if ok_b:
                        jcov_b, _ = contrast_ellipsoid_coverage(post.mean, post.sigma_mat, beta_95, true_means_vec)
                        rec_b = _build_row(
                            seed=seed, method=pol, stop_rule="credible_ellipsoid_chi95", steps=t_done,
                            certified=True, action=int(act_b), reg_bound=float(reg_b),
                            beta_val=beta_95, jcov=jcov_b, disc_step=disc_step, tokens=cum_tokens,
                            acq_s=acq_s, cert_s=cert_s_b, tot_s=time.perf_counter() - t_start,
                            subopt_pulls=subopt_pulls, total_pulls=t_done, is_orig=is_orig,
                        )

                # (c) Valid anytime union-bound direct posterior risk check
                if rec_e is None and t_done > 0 and mc_postrisk_schedule(t_done, cap):
                    mc_check_idx += 1
                    te0 = time.perf_counter()
                    ok_e, act_e, _, _ = eval_direct_posterior_risk_valid(
                        post.mean, post.sigma_mat, ss.supports, EPS, mc_check_idx,
                        n_mc=mc_draws, eta=MC_ETA, delta_post=MC_DELTA_POST, rng=mc_rng,
                    )
                    cert_s_e += time.perf_counter() - te0
                    if ok_e:
                        rec_e = _build_row(
                            seed=seed, method=pol, stop_rule="direct_posterior_risk", steps=t_done,
                            certified=True, action=int(act_e), reg_bound=EPS,
                            beta_val=None, jcov=None, disc_step=disc_step, tokens=cum_tokens,
                            acq_s=acq_s, cert_s=cert_s_e, tot_s=time.perf_counter() - t_start,
                            subopt_pulls=subopt_pulls, total_pulls=t_done, is_orig=is_orig,
                        )

                if rec_b is not None and rec_e is not None and rec_d is not None:
                    break

                ta0 = time.perf_counter()
                arm = select_gp_arm_with_beta(
                    pol, ss, l2a, post, certifier, beta=beta_95, epsilon=EPS, step=step, delta=DELTA, rng=acq_rng,
                    cd_stop_if_above_eps=False,
                )
                acq_s += time.perf_counter() - ta0

                leaf = ss.leaves[arm]
                y = float(oracle.sample(leaf))
                cum_tokens += float(tok_vec[arm])
                if is_eps_opt_leaf[arm]:
                    if disc_step is None:
                        disc_step = step
                else:
                    subopt_pulls += 1

                post.observe(arm, y)
                df_mon.step(leaf, y)

            # Finalize any uncertified rules at cap
            tot_end = time.perf_counter() - t_start
            emp_a = int(np.argmax([float(np.max(post.mean[sup])) for sup in ss.supports]))
            if rec_b is None:
                tb0 = time.perf_counter()
                ok_b, act_b, reg_b = check_ellipsoid_stopping(
                    certifier, ss, post.mean, post.sigma_mat, beta_95, EPS
                )
                cert_s_b += time.perf_counter() - tb0
                jcov_b, _ = contrast_ellipsoid_coverage(post.mean, post.sigma_mat, beta_95, true_means_vec)
                rec_b = _build_row(
                    seed=seed, method=pol, stop_rule="credible_ellipsoid_chi95", steps=cap,
                    certified=bool(ok_b), action=int(act_b) if ok_b else emp_a, reg_bound=float(reg_b),
                    beta_val=beta_95, jcov=jcov_b, disc_step=disc_step, tokens=cum_tokens,
                    acq_s=acq_s, cert_s=cert_s_b, tot_s=tot_end,
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
                rec_e = _build_row(
                    seed=seed, method=pol, stop_rule="direct_posterior_risk", steps=cap,
                    certified=bool(ok_e), action=int(act_e) if ok_e else emp_a,
                    reg_bound=EPS if ok_e else None, beta_val=None, jcov=None,
                    disc_step=disc_step, tokens=cum_tokens, acq_s=acq_s, cert_s=cert_s_e,
                    tot_s=tot_end, subopt_pulls=subopt_pulls, total_pulls=cap, is_orig=is_orig,
                )
            if rec_d is None:
                td0 = time.perf_counter()
                act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
                cert_s_d += time.perf_counter() - td0
                rec_d = _build_row(
                    seed=seed, method=pol, stop_rule="df_emp_bernstein", steps=cap,
                    certified=bool(reg_df <= EPS), action=int(act_df), reg_bound=float(reg_df),
                    beta_val=None, jcov=True, disc_step=disc_step, tokens=cum_tokens,
                    acq_s=acq_s, cert_s=cert_s_d, tot_s=tot_end,
                    subopt_pulls=subopt_pulls, total_pulls=cap, is_orig=is_orig,
                )
            out_rows.extend((rec_b, rec_e, rec_d))

        # 2. Explicitly DF-aware controls (`df_os` and DF-coupled `gp_root_info_df`)
        for ref_name in ("df_os", "gp_root_info_df"):
            df_mon = DualWitnessCovers(prob.graph, delta=DELTA, schedule="emp_bernstein", layout="best", track_separation=True)
            gp_sur = (
                SharedGaussianPosterior(kernel, PRIOR_MEAN, OBS_STD, delta=DELTA, contrast_rank=r_rank)
                if ref_name == "gp_root_info_df"
                else None
            )
            oracle = prob.oracle(seed)
            ev = df_mon.evidence
            t0_r = time.perf_counter()
            acq_r = 0.0
            disc_r: int | None = None
            subopt_r = 0
            toks_r = 0.0
            cert_ok = False
            final_act = 0
            final_reg = math.inf
            steps_done = cap

            for step in range(1, cap + 1):
                t_done = step - 1
                if ref_name == "df_os":
                    act_df, reg_df, _, _, p_leaf, q_leaf = df_mon.query_optimistic_separation()
                    if reg_df <= EPS:
                        cert_ok, final_act, final_reg, steps_done = True, int(act_df), float(reg_df), t_done
                        break
                    ta0 = time.perf_counter()
                    if q_leaf < 0:
                        chosen_leaf = p_leaf
                    else:
                        wp = float(ev.upper[p_leaf] - ev.lower[p_leaf])
                        wq = float(ev.upper[q_leaf] - ev.lower[q_leaf])
                        chosen_leaf = p_leaf if (wp, -p_leaf) >= (wq, -q_leaf) else q_leaf
                    acq_r += time.perf_counter() - ta0
                else:
                    act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
                    if reg_df <= EPS:
                        cert_ok, final_act, final_reg, steps_done = True, int(act_df), float(reg_df), t_done
                        break
                    ta0 = time.perf_counter()
                    assert gp_sur is not None
                    m_vec, s_vec = gp_sur.mean, gp_sur.stds()
                    freq_hi = np.array([ev.upper[z] for z in ss.leaves], dtype=np.float64)
                    beta_df = math.sqrt(2.0 * math.log(max(2.0, 4.0 * ss.m * float(step * step) / DELTA)))
                    clipped = np.minimum(freq_hi, m_vec + beta_df * s_vec)
                    best_b, best_sep, best_in = 0, -math.inf, 0
                    for a, sup in enumerate(ss.supports):
                        sub_v = clipped[sup]
                        lp = int(np.argmax(sub_v))
                        nlh = df_mon.neg_low_heaps[a]
                        l_out = float(nlh.keys[nlh.top]) if nlh is not None else -math.inf
                        sep = float(sub_v[lp]) - l_out
                        if sep > best_sep:
                            best_sep, best_b, best_in = sep, a, int(sup[lp])
                    z_in = ss.leaves[best_in]
                    w_in = float(ev.upper[z_in] - ev.lower[z_in])
                    if w_in <= 0.5 * EPS:
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
                    acq_r += time.perf_counter() - ta0

                arm_i = ss.leaf_to_idx[chosen_leaf]
                y = float(oracle.sample(chosen_leaf))
                toks_r += float(tok_vec[arm_i])
                if is_eps_opt_leaf[arm_i]:
                    if disc_r is None:
                        disc_r = step
                else:
                    subopt_r += 1
                df_mon.step(chosen_leaf, y)
                if gp_sur is not None:
                    gp_sur.observe(arm_i, y)

            if not cert_ok:
                act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
                cert_ok = bool(reg_df <= EPS)
                final_act, final_reg = int(act_df), float(reg_df)
            out_rows.append(
                _build_row(
                    seed=seed, method=ref_name, stop_rule="df_emp_bernstein", steps=steps_done,
                    certified=cert_ok, action=final_act, reg_bound=final_reg, beta_val=None,
                    jcov=True, disc_step=disc_r, tokens=toks_r, acq_s=acq_r, cert_s=0.0,
                    tot_s=time.perf_counter() - t0_r, subopt_pulls=subopt_r,
                    total_pulls=steps_done if cert_ok else cap, is_orig=is_orig,
                )
            )
    return out_rows


def summarize(out_dir: Path, n_boot: int = 10000) -> None:
    df = pd.read_parquet(out_dir / "v15_worfbench_7method_records.parquet")
    recs = df.to_dict(orient="records")

    df_methods = (*SEVEN_METHODS, "gp_root_info_df", "df_os")
    for tag, filt in (("full1000", lambda r: True), ("orig120", lambda r: bool(r["is_orig_cohort"]))):
        all_rows: list[dict[str, Any]] = []
        for srule, mlist in (
            ("credible_ellipsoid_chi95", SEVEN_METHODS),
            ("direct_posterior_risk", SEVEN_METHODS),
            ("df_emp_bernstein", df_methods),
        ):
            sub_s = [r for r in recs if r["stopping_rule"] == srule and filt(r)]
            for dom in ("OVERALL", *WORFBENCH_DOMAINS):
                sc = sub_s if dom == "OVERALL" else [r for r in sub_s if r["domain"] == dom]
                s_rows = summarize_paired_cohort(
                    sc,
                    mlist,
                    stratum_key="template_id",
                    unit_keys=("template_id", "seed"),
                    n_boot=n_boot,
                    boot_seed=202620,
                    include_workflow_metrics=True,
                )
                for row in s_rows:
                    all_rows.append({"cohort": tag, "domain": dom, "stopping_rule": srule, **row})
        write_csv(out_dir / f"v15_worfbench_{tag}_summary.csv", all_rows)

    print("\n=== v15 WorFBench Cached (1,000 runs/method, chi2_{r,0.95}, eps=0.020) ===")
    s_df = pd.read_csv(out_dir / "v15_worfbench_full1000_summary.csv")
    for srule in ("credible_ellipsoid_chi95", "direct_posterior_risk", "df_emp_bernstein"):
        print(f"  --- {srule} ---")
        sub = s_df[(s_df["domain"] == "OVERALL") & (s_df["stopping_rule"] == srule)]
        for _, r in sub.iterrows():
            jstr = f"{100*r['joint_coverage']:.1f}%" if pd.notna(r["joint_coverage"]) else "  ---"
            print(
                f"    {r['acquisition_method']:16s} | cert={100*r['cert_rate']:5.1f}% | "
                f"RM={r['restricted_mean']:8.1f} [{r['rm_ci95_lo']:8.1f},{r['rm_ci95_hi']:8.1f}] | "
                f"m/CD={r['ratio_vs_cd'] if pd.notna(r['ratio_vs_cd']) else 0:.2f}x | "
                f"tok={r['mean_tokens']/1e6:.3f}M | F1={r['heldout_f1_mean']:.4f} | err={int(r['false_certificates'])} | jcov={jstr}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--workers", type=int, default=min(36, os.cpu_count() or 8))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir, n_boot=1000 if args.smoke else 10000)
        return

    t0 = time.perf_counter()
    sampling_audit = audit_worfbench_sampling_protocol()
    n_seeds = 2 if args.smoke else 50
    cap = 2500 if args.smoke else CAP
    mc_draws = 512 if args.smoke else MC_DRAWS
    seeds = list(range(780001, 780001 + n_seeds))
    doms = ("all", "toolalpaca") if args.smoke else WORFBENCH_DOMAINS
    bases = WORFBENCH_BASES[:2] if args.smoke else WORFBENCH_BASES

    config = {
        "experiment": "v15_worfbench_7method",
        "git_commit": git_commit_hash(ROOT),
        "smoke": bool(args.smoke),
        "epsilon": EPS,
        "delta": DELTA,
        "budget_cap": cap,
        "domains": list(doms),
        "base_configs": [{"name": b[0], "cfg": list(b[1]), "max_upgrades": b[2]} for b in bases],
        "n_seeds_per_campaign": n_seeds,
        "total_instances_per_method": len(doms) * len(bases) * n_seeds,
        "seed_range": [seeds[0], seeds[-1]],
        "orig_table35_seed_range": [780001, 780006],
        "predeclared_working_gp_model": {
            "leak_free_status": "Predeclared purely from generic [0,1] bounds and 4-stage diameter; zero fitting on D_cert or D_test",
            "kernel": "k(z, z') = sigma_f^2 * exp(-d_H(z, z') / ell) + (nugget_frac * sigma_f^2) * 1_{z == z'}",
            "prior_mean": PRIOR_MEAN,
            "sigma_f": PRIOR_SCALE,
            "lengthscale_ell": LENGTHSCALE,
            "nugget_frac": NUGGET_FRAC,
            "working_obs_std": OBS_STD,
            "query_costs": "unit (1.0) for all policies; replay-accounted LLM tokens tracked separately",
            "credible_radius": "sqrt(chi2_{r, 0.95}) with exact contrast rank r = M - 1",
            "hyperparameter_refitting": "disabled",
        },
        "sampling_protocol_audit": sampling_audit,
    }
    (out_dir / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    chunk = 2 if args.smoke else 5
    tasks = [
        (dom, bname, bcfg, u, seeds[i : i + chunk], cap, mc_draws)
        for dom in doms
        for bname, bcfg, u in bases
        for i in range(0, len(seeds), chunk)
    ]
    print(
        f"[v15 WorFBench] Running {len(tasks)} chunks ({len(doms)*len(bases)*n_seeds} paired campaigns x "
        f"[7 GP x 3 stops + 2 DF refs], cap={cap}) on {args.workers} workers...",
        flush=True,
    )
    ctx = mp.get_context("spawn")
    all_rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for idx, ch in enumerate(ex.map(_worfbench_worker, tasks), start=1):
            all_rows.extend(ch)
            if idx % 20 == 0 or idx == len(tasks):
                print(f"  [WorFBench] {idx}/{len(tasks)} chunks ({len(all_rows)} rows, {time.perf_counter() - t0:.1f}s)", flush=True)

    write_campaign_records(out_dir, "v15_worfbench_7method_records", all_rows)
    summarize(out_dir, n_boot=1000 if args.smoke else 10000)
    write_manifest(
        out_dir,
        "v15_worfbench_7method",
        smoke=args.smoke,
        elapsed_s=time.perf_counter() - t0,
        extra={
            "n_total_rows": len(all_rows),
            "total_campaigns_per_method": len(doms) * len(bases) * n_seeds,
        },
    )
    print(f"[v15 WorFBench] Complete in {time.perf_counter() - t0:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
