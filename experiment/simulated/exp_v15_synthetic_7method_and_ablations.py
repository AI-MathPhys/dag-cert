"""Experiment v15-B: Expanded 1,000-Run 7-Method Matched Synthetic Benchmark & CD-Joint Ablations.

Completes the 7-method matched Gaussian acquisition matrix on synthetic search graphs
(M=64, K=8, Conditions A--D), expands sample size to 1,000 paired instances/method
(250 seeds x 4 conditions, strictly nesting the original 100-seed Table 7 & Table 9 cohorts),
documents every exact synthetic generator and baseline hyperparameter in a frozen `config.json`,
and adds two mechanistic ablations of CD-Joint's mathematical innovations:
  1. `cd_joint_no_safeguard`   : removes the `mean_contrast <= eps/2` safeguard.
  2. `cd_joint_single_witness` : restricts the inside dual weight `p in Delta(S(b_t))` to a
                                 single retained vertex `e_y` (retaining the safeguard).

Also evaluates valid anytime union-bound Monte Carlo direct posterior-risk stopping (`E_postrisk`)
alongside proper `sqrt(chi2_{63, 0.95})` credible-ellipsoid stopping (`B_chi95`), and expands the
fixed-feature `d=8` anytime-valid Abbasi-Yadkori frequentist study to all 7 methods x 1,000 instances.
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
    SupportStructure,
    eval_direct_posterior_risk_valid,
    mc_postrisk_schedule,
)
from dagcert._core.v12_bed_acquisition import (
    FixedFeatureGaussianOverlapProblem,
    GaussianPairedDeconfoundedProblem,
    MatchedModelBEDSession,
    default_check_schedule,
)
from experiment.analysis_v15_stats import (
    SEVEN_METHODS,
    git_commit_hash,
    summarize_paired_cohort,
    write_campaign_records,
    write_csv,
    write_manifest,
)

DEST = ROOT / "results/bayesian_ucd_v1/v15_synthetic_7method"

CONDITIONS: tuple[tuple[str, float, float], ...] = (
    ("A_indep", 0.0, 0.0),
    ("B_struct", 0.75, 0.0),
    ("C_stat", 0.0, 0.9),
    ("D_both", 0.75, 0.9),
)

MAIN_POLICIES: tuple[str, ...] = (
    *SEVEN_METHODS,
    "cd_joint_no_safeguard",
    "cd_joint_single_witness",
)

EPS = 0.025
DELTA = 0.05
CAP = 12000
MC_DRAWS = 4096
MC_ETA = 0.01
MC_DELTA_POST = 0.04


def _run_synthetic_stream(
    prob: Any,
    dataset_name: str,
    cond_id: str,
    seed: int,
    obs_seed: int,
    policy: str,
    beta_mode: str,
    cap: int,
    eval_postrisk: bool,
    is_orig: bool,
    mc_draws: int,
) -> list[dict[str, Any]]:
    """Run one matched synthetic trajectory, optionally tracking valid anytime E_postrisk simultaneously."""
    sess = MatchedModelBEDSession(
        problem=prob,
        obs_seed=obs_seed,
        policy=policy,
        epsilon=EPS,
        delta=DELTA,
        kernel=prob.kernel,
        prior_mean=prob.prior_mean,
        obs_std=prob.obs_std,
        beta_mode=beta_mode,
        rkhs_bound=prob.clean_rkhs_norm + 0.05,
        full_check_every_step=False,
        budget_checkpoints=(),
        eval_mc_draws=64,  # unused since checkpoints=() and track_mc_risk_stop=False
        track_mc_risk_stop=False,
    )

    stopping_label = "credible_ellipsoid_chi95" if beta_mode == "posterior_credible" else "anytime_frequentist_ay"
    mc_rng = np.random.default_rng((obs_seed * 1000003 + 7919) & 0xFFFFFFFFFFFFFFFF)
    mc_rec: dict[str, Any] | None = None
    mc_check_idx = 0
    mc_cert_time = 0.0

    t0 = time.perf_counter()
    while not sess.certified and sess.calls < cap:
        arm_idx = sess.select_query()
        leaf = sess.support_struct.leaves[arm_idx]
        reward = float(sess.oracle.sample(leaf))
        sess.calls += 1
        sess.total_cost += float(sess.support_struct.costs[arm_idx])

        if sess._is_eps_opt_leaf[arm_idx]:
            if sess.discovery_step is None:
                sess.discovery_step = int(sess.calls)
        else:
            sess.suboptimal_pulls += 1

        sess.posterior.observe(arm_idx, reward)

        if default_check_schedule(sess.calls, full_every_step=False) or (sess.calls == cap):
            sess._check_certificate()

        if eval_postrisk and mc_rec is None and mc_postrisk_schedule(sess.calls, cap):
            mc_check_idx += 1
            tc0 = time.perf_counter()
            ok_e, act_e, _, cp_e = eval_direct_posterior_risk_valid(
                sess.posterior.mean,
                sess.posterior.sigma_mat,
                sess.support_struct.supports,
                EPS,
                mc_check_idx,
                n_mc=mc_draws,
                eta=MC_ETA,
                delta_post=MC_DELTA_POST,
                rng=mc_rng,
            )
            mc_cert_time += time.perf_counter() - tc0
            if ok_e:
                tr_e = float(sess._true_action_regrets[int(act_e)])
                mc_rec = {
                    "dataset": dataset_name,
                    "condition": cond_id,
                    "domain": "synthetic",
                    "template_id": f"{cond_id}_s{seed}",
                    "seed": int(seed),
                    "acquisition_method": policy,
                    "stopping_rule": "direct_posterior_risk",
                    "epsilon": EPS,
                    "delta": DELTA,
                    "budget": int(cap),
                    "n_evaluations": int(sess.calls),
                    "certified": True,
                    "recommended_root": int(act_e),
                    "true_root_regret": round(tr_e, 6),
                    "false_certificate": bool(tr_e > EPS + 1e-12),
                    "first_epsilon_optimal_discovery": int(sess.discovery_step) if sess.discovery_step is not None else int(sess.calls),
                    "discovered": bool(sess.discovery_step is not None),
                    "joint_coverage": None,
                    "root_regret_bound_coverage": bool(tr_e <= EPS + 1e-12),
                    "cert_regret_bound": EPS,
                    "contrast_rank": int(sess.posterior.contrast_rank),
                    "beta_at_stop": None,
                    "total_tokens": 0.0,
                    "heldout_f1": None,
                    "heldout_regret": None,
                    "acquisition_time_s": round(float(sess.acq_time_s), 5),
                    "certificate_time_s": round(float(mc_cert_time), 5),
                    "total_runtime_s": round(float(time.perf_counter() - t0), 5),
                    "safeguard_activations": int(sess.safeguard_activations),
                    "mean_mixture_support": round(sess.mixture_support_sum / max(1, sess.mixture_steps), 4),
                    "proxy_query_frac": round(sess.suboptimal_pulls / max(1, sess.calls), 5),
                    "is_orig_cohort": bool(is_orig),
                }

    total_s = time.perf_counter() - t0
    if sess.certified:
        rec_action = int(sess.action)
    else:
        act_m = [float(np.max(sess.posterior.mean[sup])) for sup in sess.support_struct.supports]
        rec_action = int(np.argmax(act_m))
    true_reg = float(sess._true_action_regrets[rec_action])
    false_cert = bool(sess.certified and true_reg > EPS + 1e-12)

    # Exact projected contrast-ellipsoid coverage (handles both full-rank M=64 and rank-8 fixed-feature)
    beta_now = float(sess.posterior.beta())
    diff_vec = sess._true_leaf_means - sess.posterior.mean
    m_len = sess.posterior.m
    proj = np.eye(m_len, dtype=np.float64) - (1.0 / float(m_len))
    s_sym = 0.5 * (sess.posterior.sigma_mat + sess.posterior.sigma_mat.T)
    sc = proj @ s_sym @ proj
    evals, evecs = np.linalg.eigh(0.5 * (sc + sc.T))
    tol_c = max(1e-12, 1e-10 * float(np.max(np.abs(evals))))
    pos = evals > tol_c
    dc = proj @ diff_vec
    if np.any(pos):
        coords = evecs[:, pos].T @ dc
        q_contrast = float(np.sum((coords * coords) / evals[pos]))
    else:
        q_contrast = 0.0
    if np.any(~pos) and float(np.linalg.norm(evecs[:, ~pos].T @ dc)) > 1e-7:
        q_contrast = math.inf
    joint_cov = bool(q_contrast <= (beta_now * beta_now) + 1e-7)
    reg_bound = float(sess.current_regret) if math.isfinite(sess.current_regret) else None
    reg_bound_cov = bool((reg_bound is None) or (true_reg <= reg_bound + 1e-9))

    main_rec = {
        "dataset": dataset_name,
        "condition": cond_id,
        "domain": "synthetic",
        "template_id": f"{cond_id}_s{seed}",
        "seed": int(seed),
        "acquisition_method": policy,
        "stopping_rule": stopping_label,
        "epsilon": EPS,
        "delta": DELTA,
        "budget": int(cap),
        "n_evaluations": int(sess.calls) if sess.certified else int(cap),
        "certified": bool(sess.certified),
        "recommended_root": rec_action,
        "true_root_regret": round(true_reg, 6),
        "false_certificate": false_cert,
        "first_epsilon_optimal_discovery": int(sess.discovery_step) if sess.discovery_step is not None else int(cap),
        "discovered": bool(sess.discovery_step is not None),
        "joint_coverage": joint_cov,
        "root_regret_bound_coverage": reg_bound_cov,
        "cert_regret_bound": round(reg_bound, 6) if reg_bound is not None else None,
        "contrast_rank": int(sess.posterior.contrast_rank),
        "beta_at_stop": round(beta_now, 4),
        "total_tokens": 0.0,
        "heldout_f1": None,
        "heldout_regret": None,
        "acquisition_time_s": round(float(sess.acq_time_s), 5),
        "certificate_time_s": round(float(sess.cert_time_s), 5),
        "total_runtime_s": round(float(total_s), 5),
        "safeguard_activations": int(sess.safeguard_activations),
        "mean_mixture_support": round(sess.mixture_support_sum / max(1, sess.mixture_steps), 4),
        "proxy_query_frac": round(sess.suboptimal_pulls / max(1, sess.calls), 5),
        "is_orig_cohort": bool(is_orig),
    }

    out = [main_rec]
    if eval_postrisk:
        if mc_rec is None:
            # Final check at stop/cap if E_postrisk did not yet trigger
            mc_check_idx += 1
            tc0 = time.perf_counter()
            ok_e, act_e, _, _ = eval_direct_posterior_risk_valid(
                sess.posterior.mean,
                sess.posterior.sigma_mat,
                sess.support_struct.supports,
                EPS,
                mc_check_idx,
                n_mc=mc_draws,
                eta=MC_ETA,
                delta_post=MC_DELTA_POST,
                rng=mc_rng,
            )
            mc_cert_time += time.perf_counter() - tc0
            final_a = int(act_e) if ok_e else rec_action
            tr_e = float(sess._true_action_regrets[final_a])
            mc_rec = {
                **main_rec,
                "stopping_rule": "direct_posterior_risk",
                "n_evaluations": int(sess.calls) if ok_e else int(cap),
                "certified": bool(ok_e),
                "recommended_root": final_a,
                "true_root_regret": round(tr_e, 6),
                "false_certificate": bool(ok_e and tr_e > EPS + 1e-12),
                "joint_coverage": None,
                "root_regret_bound_coverage": bool((not ok_e) or (tr_e <= EPS + 1e-12)),
                "cert_regret_bound": EPS if ok_e else None,
                "beta_at_stop": None,
                "certificate_time_s": round(float(mc_cert_time), 5),
            }
        out.append(mc_rec)
    return out


def _main64_chunk_worker(task: tuple) -> list[dict[str, Any]]:
    cond_id, omega, rho, seeds, policies, cap, mc_draws = task
    rows: list[dict[str, Any]] = []
    for s in seeds:
        prob_seed = 5000 + s * 17 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
        obs_seed = 920000 + s * 97 + int(round(omega * 100)) * 13 + int(round(rho * 100)) * 5
        prob = GaussianPairedDeconfoundedProblem(
            seed=prob_seed, overlap=omega, rho=rho, target_margin=0.055, tau0=0.14, hw=0.14
        )
        is_orig = 2000 <= s < 2100
        for pol in policies:
            rows.extend(
                _run_synthetic_stream(
                    prob=prob,
                    dataset_name="synthetic_main64",
                    cond_id=cond_id,
                    seed=s,
                    obs_seed=obs_seed,
                    policy=pol,
                    beta_mode="posterior_credible",
                    cap=cap,
                    eval_postrisk=(pol in SEVEN_METHODS),
                    is_orig=is_orig,
                    mc_draws=mc_draws,
                )
            )
    return rows


def _confirm_freq_chunk_worker(task: tuple) -> list[dict[str, Any]]:
    cond_id, omega, rho, seeds, policies, cap = task
    rows: list[dict[str, Any]] = []
    for s in seeds:
        prob_seed = 8000 + s * 29 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
        obs_seed = 950000 + s * 107 + int(round(omega * 100)) * 17 + int(round(rho * 100)) * 5
        prob = FixedFeatureGaussianOverlapProblem(
            seed=prob_seed, overlap=omega, rho=rho, d_feat=8, target_margin=0.055, tau0=0.14, hw=0.14
        )
        is_orig = 5000 <= s < 5100
        for pol in policies:
            rows.extend(
                _run_synthetic_stream(
                    prob=prob,
                    dataset_name="synthetic_confirm_freq_d8",
                    cond_id=cond_id,
                    seed=s,
                    obs_seed=obs_seed,
                    policy=pol,
                    beta_mode="anytime_frequentist",
                    cap=cap,
                    eval_postrisk=False,
                    is_orig=is_orig,
                    mc_draws=64,
                )
            )
    return rows


def summarize(out_dir: Path, n_boot: int = 10000) -> None:
    df_main = pd.read_parquet(out_dir / "v15_synthetic_main64_records.parquet")
    df_cf = pd.read_parquet(out_dir / "v15_synthetic_confirm_freq_records.parquet")

    main_recs = df_main.to_dict(orient="records")
    cf_recs = df_cf.to_dict(orient="records")

    # 1. Primary 1,000-run & original 400-run 7-method summaries (pooled + per-condition)
    for tag, filt in (("full1000", lambda r: True), ("orig400", lambda r: bool(r["is_orig_cohort"]))):
        # Credible ellipsoid B_chi95
        sub_b = [r for r in main_recs if r["stopping_rule"] == "credible_ellipsoid_chi95" and filt(r)]
        rows_b: list[dict[str, Any]] = []
        for scope in ("ALL", *[c[0] for c in CONDITIONS]):
            sc_recs = sub_b if scope == "ALL" else [r for r in sub_b if r["condition"] == scope]
            sum_r = summarize_paired_cohort(
                sc_recs,
                MAIN_POLICIES,
                stratum_key="condition",
                unit_keys=("condition", "seed"),
                n_boot=n_boot,
                boot_seed=202615,
            )
            for row in sum_r:
                rows_b.append({"cohort": tag, "condition": scope, "stopping_rule": "credible_ellipsoid_chi95", **row})
        write_csv(out_dir / f"v15_synthetic_main64_{tag}_summary.csv", rows_b)

        # Direct posterior risk E_postrisk (7 methods)
        sub_e = [r for r in main_recs if r["stopping_rule"] == "direct_posterior_risk" and filt(r)]
        rows_e: list[dict[str, Any]] = []
        for scope in ("ALL", *[c[0] for c in CONDITIONS]):
            sc_recs = sub_e if scope == "ALL" else [r for r in sub_e if r["condition"] == scope]
            sum_r = summarize_paired_cohort(
                sc_recs,
                SEVEN_METHODS,
                stratum_key="condition",
                unit_keys=("condition", "seed"),
                n_boot=n_boot,
                boot_seed=202616,
            )
            for row in sum_r:
                rows_e.append({"cohort": tag, "condition": scope, "stopping_rule": "direct_posterior_risk", **row})
        write_csv(out_dir / f"v15_synthetic_postrisk_{tag}_summary.csv", rows_e)

        # Fixed-feature d=8 anytime-valid frequentist confirmation (7 methods)
        sub_c = [r for r in cf_recs if filt(r)]
        rows_c: list[dict[str, Any]] = []
        for scope in ("ALL", *[c[0] for c in CONDITIONS]):
            sc_recs = sub_c if scope == "ALL" else [r for r in sub_c if r["condition"] == scope]
            sum_r = summarize_paired_cohort(
                sc_recs,
                SEVEN_METHODS,
                stratum_key="condition",
                unit_keys=("condition", "seed"),
                n_boot=n_boot,
                boot_seed=202617,
            )
            for row in sum_r:
                rows_c.append({"cohort": tag, "condition": scope, "stopping_rule": "anytime_frequentist_ay", **row})
        write_csv(out_dir / f"v15_synthetic_confirm_freq_{tag}_summary.csv", rows_c)

    # Print crisp console summary
    print("\n=== v15 Synthetic Main64 (1,000 runs/method, chi2_{63,0.95}) ===")
    s_df = pd.read_csv(out_dir / "v15_synthetic_main64_full1000_summary.csv")
    for _, r in s_df[s_df["condition"] == "ALL"].iterrows():
        print(
            f"  {r['acquisition_method']:24s} | cert={100*r['cert_rate']:5.1f}% | "
            f"RM={r['restricted_mean']:7.1f} [{r['rm_ci95_lo']:7.1f},{r['rm_ci95_hi']:7.1f}] | "
            f"m/CD={r['ratio_vs_cd']:.2f}x [{r['ratio_vs_cd_ci95_lo']:.2f},{r['ratio_vs_cd_ci95_hi']:.2f}] | "
            f"err={int(r['false_certificates'])} | jcov={100*r['joint_coverage']:.1f}% | sg={100*r['mean_safeguard_rate']:.1f}% | supp={r['mean_mixture_support']:.2f}"
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
    n_seeds = 4 if args.smoke else 250
    cap = 1500 if args.smoke else CAP
    mc_draws = 512 if args.smoke else MC_DRAWS
    main_seeds = list(range(2000, 2000 + n_seeds))
    cf_seeds = list(range(5000, 5000 + n_seeds))

    config = {
        "experiment": "v15_synthetic_7method",
        "git_commit": git_commit_hash(ROOT),
        "smoke": bool(args.smoke),
        "epsilon": EPS,
        "delta": DELTA,
        "budget_cap": cap,
        "n_seeds_per_condition": n_seeds,
        "total_instances_per_method": 4 * n_seeds,
        "main64_seed_range": [main_seeds[0], main_seeds[-1]],
        "orig400_main64_seed_range": [2000, 2099],
        "confirm_freq_seed_range": [cf_seeds[0], cf_seeds[-1]],
        "orig400_confirm_freq_seed_range": [5000, 5099],
        "conditions": [{"id": c, "omega": om, "rho": rh} for c, om, rh in CONDITIONS],
        "generator_parameters": {
            "class": "GaussianPairedDeconfoundedProblem (M=64, K=8, 8 motifs/action, zero containments)",
            "shared_motifs_by_omega": {"0.0": 0, "0.75": 16},
            "private_motifs": "b in {6, 7} strictly private; motif peak placed at b=7 (+0.025)",
            "prior_mean": 0.48,
            "tau0": 0.14,
            "hw": 0.14,
            "obs_std": round(0.14 / math.sqrt(3.0), 8),
            "target_margin": 0.055,
            "kernel_formula": "K(rho) = tau0^2 * ((1 - rho) * I_64 + rho * kron(0.25*I_8 + 0.75*1_8*1_8^T, AR1(8, rho)))",
            "action_gaps_vec": [0.10, 0.045, 0.02575, -0.01, -0.025, -0.04, -0.055, -0.07],
            "fixed_feature_d": 8,
            "fixed_feature_rkhs_bound_margin": "+0.05 above exact ||theta*||_2",
        },
        "policy_definitions": {
            "gp_ucb": "argmax_x m_{t,x} + kappa_t * s_{t,x}, kappa_t = sqrt(2 log(M pi^2 t^2 / (6 delta))) (Srinivas et al. 2012), smallest index on ties",
            "gp_ts": "argmax_x mu_tilde_x, single joint draw mu_tilde ~ N(m_t, Sigma_t) via independent seeded RNG, smallest index on ties",
            "gp_ei": "argmax_x log(s_{t,x} * h((m_{t,x} - max_z m_{t,z}) / s_{t,x}) / c_x), exact underflow-free Mills-ratio log_h, smallest index on ties",
            "kg": "argmax_x log(KG_t(x) / c_x), exact Frazier-Powell-Dayanik (2009) O(M log M) convex upper envelope in log-space",
            "gp_os": "Optimistic Separation on shared posterior intervals with stopping beta: b_t = argmax_a (U_a - L^-_a), sample wider of {p_t, q_t}",
            "gp_root_info": "Global optimistic terminal w* = argmax_z u_z; b_t = argmax_{a ni w*} (u_{w*} - max_{z notin S(a)} u_z); z_box = argmax_{z notin S(b_t)} u_z; sample wider of {w*, z_box}",
            "cd_joint": "Algorithm 1 safeguarded contrast-directed acquisition with conic dual mixture p* in Delta(S(b_t)) and eps/2 safeguard",
            "cd_joint_no_safeguard": "CD-Joint ablation removing the mean_contrast <= eps/2 safeguard",
            "cd_joint_single_witness": "CD-Joint ablation restricting p in Delta(S(b_t)) to a single vertex e_y (retaining the eps/2 safeguard)",
        },
        "stopping_rules": {
            "credible_ellipsoid_chi95": "Exact conic regret <= eps under beta = sqrt(chi2_{r, 0.95}), r = 63, check schedule: every step t<=50, every 5 (t<=500), every 10 (t<=2000), every 20 (t>2000)",
            "direct_posterior_risk": f"Valid anytime union-bound MC: N_MC={mc_draws} fresh draws/check, eta={MC_ETA}/(K*j*(j+1)), delta_post={MC_DELTA_POST}",
            "anytime_frequentist_ay": "Abbasi-Yadkori self-normalized ellipsoid B + sqrt(2(gamma_t + log(1/delta))) on exact d=8 linear feature model",
        },
    }
    (out_dir / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    ctx = mp.get_context("spawn")
    chunk = 2 if args.smoke else 5

    # Stage A: Main64 (7 methods + 2 ablations = 9 policies x 4 conditions x 250 seeds)
    t_a = time.perf_counter()
    tasks_a = [
        (cid, om, rh, main_seeds[i : i + chunk], MAIN_POLICIES, cap, mc_draws)
        for cid, om, rh in CONDITIONS
        for i in range(0, len(main_seeds), chunk)
    ]
    print(f"[v15 Synthetic Main64] Running {len(tasks_a)} chunks ({4 * n_seeds * len(MAIN_POLICIES)} trajectories, cap={cap}) on {args.workers} workers...", flush=True)
    main_rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for idx, ch in enumerate(ex.map(_main64_chunk_worker, tasks_a), start=1):
            main_rows.extend(ch)
            if idx % 20 == 0 or idx == len(tasks_a):
                print(f"  [Main64] {idx}/{len(tasks_a)} chunks ({len(main_rows)} rows, {time.perf_counter() - t_a:.1f}s)", flush=True)
    write_campaign_records(out_dir, "v15_synthetic_main64_records", main_rows)

    # Stage B: ConfirmFreq d=8 (7 methods x 4 conditions x 250 seeds)
    t_b = time.perf_counter()
    tasks_b = [
        (cid, om, rh, cf_seeds[i : i + chunk], SEVEN_METHODS, cap)
        for cid, om, rh in CONDITIONS
        for i in range(0, len(cf_seeds), chunk)
    ]
    print(f"[v15 Synthetic ConfirmFreq d=8] Running {len(tasks_b)} chunks ({4 * n_seeds * len(SEVEN_METHODS)} trajectories, cap={cap}) on {args.workers} workers...", flush=True)
    cf_rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for idx, ch in enumerate(ex.map(_confirm_freq_chunk_worker, tasks_b), start=1):
            cf_rows.extend(ch)
            if idx % 20 == 0 or idx == len(tasks_b):
                print(f"  [ConfirmFreq] {idx}/{len(tasks_b)} chunks ({len(cf_rows)} rows, {time.perf_counter() - t_b:.1f}s)", flush=True)
    write_campaign_records(out_dir, "v15_synthetic_confirm_freq_records", cf_rows)

    summarize(out_dir, n_boot=1000 if args.smoke else 10000)
    write_manifest(
        out_dir,
        "v15_synthetic_7method",
        smoke=args.smoke,
        elapsed_s=time.perf_counter() - t0,
        extra={
            "n_main64_rows": len(main_rows),
            "n_confirm_freq_rows": len(cf_rows),
            "n_seeds_per_condition": n_seeds,
        },
    )
    print(f"[v15 Synthetic] Complete in {time.perf_counter() - t0:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
