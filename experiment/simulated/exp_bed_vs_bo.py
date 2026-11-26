"""Experiment v12: Decision-Aware Bayesian Experimental Design vs. Bayesian Optimization on Search DAGs.

Flagship matched-model acquisition comparison under identical Gaussian beliefs, identical paired
intrinsic observation tapes, identical numerical tolerances, and an identical root-action
certification stopping rule across seven acquisition policies:
  - Optimization-directed BO: `gp_ucb`, `gp_ts`, `gp_ei`, and exact analytical `kg`
    (Frazier-Powell-Dayanik 2009 Correlated Knowledge Gradient, underflow-free log-space)
  - Certification-directed: `gp_os` and `cd_joint`
  - Decision-risk oracle reference: `bayesian_voi` (Bayesian Root-Risk Value of Information)

Stages (following the prespecified execution order):
  1. `pilot`        : 10 separate pilot seeds/condition (40 instances) verifying posterior updates,
                      certificate calibration, capping mix, and timings before running test seeds.
  2. `main64`       : Primary M=64, K=8 full-rank overlap x correlation study (4 conditions A-D x
                      100 test seeds x 6 scalable policies = 2,400 runs; eps=0.025, delta=0.05,
                      cap=12,000; exact posterior credible ellipsoid; checkpoints t in
                      {50, 100, 250, 500, 1000, 2000, 5000}).
  3. `voi16`        : Small-problem M=16, K=4 Bayesian Root-Risk VOI reference study (4 conditions
                      A-D x 40 test seeds x all 7 policies = 1,120 runs; cap=1,000; N_y=32,
                      N_mu=2048; plus predetermined MC doubling stability audit N_y=64, N_mu=4096
                      on 40 instances & 200 states).
  4. `proxy5`       : Cost-sensitive M=5, K=2, d=3 proxy benchmark (cos in {0.50, 0.95} x
                      c_proxy in {0.25, 1.0, 4.0} x 80 paired seeds x all 7 policies = 3,360 runs
                      under exact posterior credible stopping + 3,360 runs under anytime-valid
                      Abbasi-Yadkori frequentist stopping).
  5. `confirm_freq` : Confirmatory M=64, K=8, d=8 fixed-feature Gaussian analysis (4 conditions x
                      100 test seeds x 6 scalable policies = 2,400 anytime-valid frequentist runs
                      paired directly against 2,400 posterior-credible runs on identical instances).
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
from scipy.stats import norm

from joint_root_cert._core.v12_bed_acquisition import (
    ALL_V12_POLICIES,
    FixedFeatureGaussianOverlapProblem,
    GaussianPairedDeconfoundedProblem,
    MatchedModelBEDSession,
    SharedGaussianPosterior,
    SmallOverlapCorrelationProblem,
    select_bayesian_root_voi,
)
from joint_root_cert import SupportStructure
from experiment.simulated.exp_factorial_and_proxy_sweep import TunableProxyDAGProblem


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/v12_bed_vs_bo"

SCALABLE_POLICIES = ("gp_ucb", "gp_ts", "gp_ei", "kg", "gp_os", "cd_joint")
ALL_SEVEN = ALL_V12_POLICIES

CONDITIONS: tuple[tuple[str, float, float], ...] = (
    ("A_indep", 0.0, 0.0),
    ("B_struct", 0.75, 0.0),
    ("C_stat", 0.0, 0.9),
    ("D_both", 0.75, 0.9),
)

MAIN_EPS = 0.025
MAIN_DELTA = 0.05
MAIN_CAP = 12000
MAIN_CHECKPOINTS = (50, 100, 250, 500, 1000, 2000, 5000)

VOI16_CAP = 1000
VOI16_CHECKPOINTS = (10, 25, 50, 100, 200, 400, 700, 1000)

PROXY_ALIGNS = (0.50, 0.95)
PROXY_COSTS = (0.25, 1.0, 4.0)
PROXY_EPS = 0.015
PROXY_DELTA = 0.05
PROXY_CAP = 1500
PROXY_REG_LAMBDA = 0.5


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _cp95_upper(k: int, n: int) -> float:
    if n <= 0:
        return 1.0
    if k >= n:
        return 1.0
    return float(beta_dist.ppf(0.95, k + 1, n - k))


def _bootstrap_mean_ci(vals: np.ndarray, n_boot: int = 10000, seed: int = 202612) -> tuple[float, float, float]:
    arr = np.asarray(vals, dtype=np.float64)
    mu = float(np.mean(arr))
    if len(arr) <= 1:
        return mu, mu, mu
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, len(arr), size=(n_boot, len(arr)))
    means = np.mean(arr[idx], axis=1)
    lo, hi = np.percentile(means, [2.5, 97.5])
    return mu, float(lo), float(hi)


def _bootstrap_paired_ratio_ci(
    num: np.ndarray, den: np.ndarray, n_boot: int = 10000, seed: int = 202613
) -> tuple[float, float, float]:
    """Paired bootstrap 95% CI on ratio of restricted means `mean(num) / mean(den)`."""
    a = np.asarray(num, dtype=np.float64)
    b = np.asarray(den, dtype=np.float64)
    pt = float(np.mean(a)) / max(1e-12, float(np.mean(b)))
    if len(a) <= 1:
        return pt, pt, pt
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, len(a), size=(n_boot, len(a)))
    ratios = np.mean(a[idx], axis=1) / np.maximum(1e-12, np.mean(b[idx], axis=1))
    lo, hi = np.percentile(ratios, [2.5, 97.5])
    return pt, float(lo), float(hi)


# ---------------------------------------------------------------------------
# Workers
# ---------------------------------------------------------------------------
def _main64_worker(task: tuple) -> list[dict]:
    cond_id, omega, rho, seeds, cap, policies, beta_mode, checkpoints = task
    rows: list[dict] = []
    for s in seeds:
        prob_seed = 5000 + s * 17 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
        obs_seed = 920000 + s * 97 + int(round(omega * 100)) * 13 + int(round(rho * 100)) * 5
        prob = GaussianPairedDeconfoundedProblem(
            seed=prob_seed, overlap=omega, rho=rho, target_margin=0.055, tau0=0.14, hw=0.14
        )
        for pol in policies:
            sess = MatchedModelBEDSession(
                problem=prob,
                obs_seed=obs_seed,
                policy=pol,
                epsilon=MAIN_EPS,
                delta=MAIN_DELTA,
                kernel=prob.kernel,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                beta_mode=beta_mode,
                rkhs_bound=prob.clean_rkhs_norm + 0.05,
                full_check_every_step=False,
                budget_checkpoints=checkpoints,
                eval_mc_draws=4096,
            )
            rec = sess.run(cap=cap)
            rec.update(
                {
                    "study": "main64",
                    "condition": cond_id,
                    "omega": omega,
                    "rho": rho,
                    "seed": s,
                    "beta_mode": beta_mode,
                    "cap": cap,
                    "contrast_rank": int(sess.posterior.contrast_rank),
                    "beta_final": round(float(sess.posterior.beta()), 4),
                }
            )
            rows.append(rec)
    return rows


def _voi16_worker(task: tuple) -> list[dict]:
    cond_id, omega, rho, seeds, cap, policies, voi_ny, voi_nmu, tag = task
    rows: list[dict] = []
    for s in seeds:
        prob_seed = 6000 + s * 19 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
        obs_seed = 930000 + s * 101 + int(round(omega * 100)) * 11 + int(round(rho * 100)) * 5
        prob = SmallOverlapCorrelationProblem(
            seed=prob_seed, overlap=omega, rho=rho, target_margin=0.055, tau0=0.14, hw=0.14
        )
        for pol in policies:
            sess = MatchedModelBEDSession(
                problem=prob,
                obs_seed=obs_seed,
                policy=pol,
                epsilon=MAIN_EPS,
                delta=MAIN_DELTA,
                kernel=prob.kernel,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                beta_mode="posterior_credible",
                full_check_every_step=True,
                budget_checkpoints=VOI16_CHECKPOINTS,
                eval_mc_draws=4096,
                voi_n_y=voi_ny,
                voi_n_mu=voi_nmu,
                track_mc_risk_stop=True,
            )
            rec = sess.run(cap=cap)
            rec.update(
                {
                    "study": tag,
                    "condition": cond_id,
                    "omega": omega,
                    "rho": rho,
                    "seed": s,
                    "beta_mode": "posterior_credible",
                    "cap": cap,
                    "voi_n_y": voi_ny,
                    "voi_n_mu": voi_nmu,
                    "contrast_rank": int(sess.posterior.contrast_rank),
                    "beta_final": round(float(sess.posterior.beta()), 4),
                }
            )
            rows.append(rec)
    return rows


def _voi16_step_agreement_worker(task: tuple) -> dict:
    """Measure direct single-step query selection agreement between (32, 2048) and (64, 4096) VOI."""
    cond_id, omega, rho, seeds = task
    total_states = 0
    exact_agree = 0
    top2_agree = 0
    score_corrs: list[float] = []

    q32 = norm.ppf((np.arange(32, dtype=np.float64) + 0.5) / 32.0)
    q64 = norm.ppf((np.arange(64, dtype=np.float64) + 0.5) / 64.0)

    for s in seeds:
        prob_seed = 6000 + s * 19 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
        obs_seed = 930000 + s * 101 + int(round(omega * 100)) * 11 + int(round(rho * 100)) * 5
        prob = SmallOverlapCorrelationProblem(
            seed=prob_seed, overlap=omega, rho=rho, target_margin=0.055, tau0=0.14, hw=0.14
        )
        ss = SupportStructure(prob.graph)
        post = SharedGaussianPosterior(prob.kernel, prob.prior_mean, prob.obs_std, delta=MAIN_DELTA)
        oracle = prob.oracle(obs_seed)
        rng = np.random.default_rng(770000 + s * 37 + int(round(omega * 100)))

        # Sample posterior states at t in {15, 30, 50, 75, 100} (after initial symmetry breaking)
        check_ts = {15, 30, 50, 75, 100}
        for t in range(101):
            if t in check_ts:
                z1 = rng.standard_normal((16, 1024))
                u1 = np.concatenate([z1, -z1], axis=1)
                z2 = rng.standard_normal((16, 2048))
                u2 = np.concatenate([z2, -z2], axis=1)
                c1, sc1, _, tail1 = select_bayesian_root_voi(
                    post.mean, post.sigma_mat, post.obs_var, ss.costs, ss.supports, ss.complements, MAIN_EPS, q32, u1
                )
                c2, sc2, _, tail2 = select_bayesian_root_voi(
                    post.mean, post.sigma_mat, post.obs_var, ss.costs, ss.supports, ss.complements, MAIN_EPS, q64, u2
                )
                total_states += 1
                if c1 == c2:
                    exact_agree += 1
                top2 = set(np.argsort(-sc2)[:2].tolist())
                if c1 in top2:
                    top2_agree += 1
                if np.std(sc1) > 1e-12 and np.std(sc2) > 1e-12 and (tail1 == tail2):
                    score_corrs.append(float(np.corrcoef(sc1, sc2)[0, 1]))
            if t < 100:
                arm = int(t % 16) if t < 16 else int(rng.integers(0, 16))
                post.observe(arm, float(oracle.sample(ss.leaves[arm])))

    return {
        "condition": cond_id,
        "total_states": total_states,
        "exact_agree": exact_agree,
        "top2_agree": top2_agree,
        "mean_score_corr": float(np.mean(score_corrs)) if score_corrs else 1.0,
    }


def _proxy5_worker(task: tuple) -> list[dict]:
    align, c_proxy, seeds, cap, beta_modes = task
    prob = TunableProxyDAGProblem(align=align, hw=0.16)
    costs = np.array([1.0, 1.0, 1.0, 1.0, float(c_proxy)], dtype=np.float64)
    # Exact conjugate linear-Gaussian prior matching `LinearFeatureModel(reg_lambda=0.5)`
    k_mat = (prob.obs_std ** 2 / PROXY_REG_LAMBDA) * (prob.phi @ prob.phi.T)
    rkhs_b = math.sqrt(PROXY_REG_LAMBDA) * prob.param_bound / prob.obs_std

    rows: list[dict] = []
    for beta_mode in beta_modes:
        for s in seeds:
            obs_seed = 940000 + s * 43 + int(round(align * 100)) * 7
            for pol in ALL_SEVEN:
                sess = MatchedModelBEDSession(
                    problem=prob,
                    obs_seed=obs_seed,
                    policy=pol,
                    epsilon=PROXY_EPS,
                    delta=PROXY_DELTA,
                    kernel=k_mat,
                    prior_mean=prob.prior_mean,
                    obs_std=prob.obs_std,
                    beta_mode=beta_mode,
                    rkhs_bound=rkhs_b,
                    contrast_rank=3,
                    costs=costs,
                    full_check_every_step=True,
                    budget_checkpoints=(10, 25, 50, 100, 250, 500),
                    eval_mc_draws=2048,
                    voi_n_y=32,
                    voi_n_mu=2048,
                    track_mc_risk_stop=(beta_mode == "posterior_credible"),
                )
                rec = sess.run(cap=cap)
                proxy_pulls = int(rec["arm_counts"][4])
                rec.update(
                    {
                        "study": f"proxy5_{beta_mode}",
                        "align": align,
                        "c_proxy": c_proxy,
                        "seed": s,
                        "beta_mode": beta_mode,
                        "cap": cap,
                        "proxy_pulls": proxy_pulls,
                        "proxy_arm_frac": round(proxy_pulls / max(1, int(rec["steps"])), 5),
                        "beta_final": round(float(sess.posterior.beta()), 4),
                    }
                )
                rows.append(rec)
    return rows


def _confirm_freq_worker(task: tuple) -> list[dict]:
    cond_id, omega, rho, seeds, cap, policies, beta_modes = task
    rows: list[dict] = []
    for s in seeds:
        prob_seed = 7000 + s * 23 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3
        obs_seed = 950000 + s * 107 + int(round(omega * 100)) * 13 + int(round(rho * 100)) * 5
        prob = FixedFeatureGaussianOverlapProblem(
            seed=prob_seed, overlap=omega, rho=rho, d_feat=8, target_margin=0.055, tau0=0.14, hw=0.14
        )
        for beta_mode in beta_modes:
            for pol in policies:
                sess = MatchedModelBEDSession(
                    problem=prob,
                    obs_seed=obs_seed,
                    policy=pol,
                    epsilon=MAIN_EPS,
                    delta=MAIN_DELTA,
                    kernel=prob.kernel,
                    prior_mean=prob.prior_mean,
                    obs_std=prob.obs_std,
                    beta_mode=beta_mode,
                    rkhs_bound=prob.clean_rkhs_norm + 0.05,
                    contrast_rank=prob.d_feat,
                    full_check_every_step=False,
                    budget_checkpoints=MAIN_CHECKPOINTS,
                    eval_mc_draws=2048,
                )
                rec = sess.run(cap=cap)
                rec.update(
                    {
                        "study": f"confirm_d8_{beta_mode}",
                        "condition": cond_id,
                        "omega": omega,
                        "rho": rho,
                        "seed": s,
                        "beta_mode": beta_mode,
                        "cap": cap,
                        "d_feat": prob.d_feat,
                        "rkhs_norm": round(prob.clean_rkhs_norm, 4),
                        "beta_final": round(float(sess.posterior.beta()), 4),
                    }
                )
                rows.append(rec)
    return rows


# ---------------------------------------------------------------------------
# Summaries
# ---------------------------------------------------------------------------
def _load_jsonl(path: Path) -> list[dict]:
    if not path.is_file():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def summarize_main_or_confirm(rows: list[dict], out_csv: Path, ck_csv: Path, policies: tuple[str, ...]) -> None:
    if not rows:
        return
    cond_ids = [c[0] for c in CONDITIONS] + ["ALL"]
    summary_rows: list[dict] = []
    ck_rows: list[dict] = []

    beta_modes = sorted({r["beta_mode"] for r in rows})
    for bm in beta_modes:
        bm_rows = [r for r in rows if r["beta_mode"] == bm]
        for cid in cond_ids:
            sub = bm_rows if cid == "ALL" else [r for r in bm_rows if r["condition"] == cid]
            if not sub:
                continue
            by_pol: dict[str, list[dict]] = {
                p: sorted([r for r in sub if r["policy"] == p], key=lambda x: (x["condition"], x["seed"]))
                for p in policies
            }
            cd_steps = np.array([r["restricted_steps"] for r in by_pol.get("cd_joint", [])], dtype=np.float64)
            kg_steps = np.array([r["restricted_steps"] for r in by_pol.get("kg", [])], dtype=np.float64)

            for p in policies:
                prs = by_pol.get(p, [])
                if not prs:
                    continue
                n = len(prs)
                r_steps = np.array([r["restricted_steps"] for r in prs], dtype=np.float64)
                r_cost = np.array([r["restricted_cost"] for r in prs], dtype=np.float64)
                certs = sum(1 for r in prs if r["certified"])
                errs = sum(1 for r in prs if r["false_certificate"])
                disc = np.array([r["discovery_step"] for r in prs], dtype=np.float64)
                pfrac = np.array([r["proxy_query_frac"] for r in prs], dtype=np.float64)
                acq_ms = np.array([r["acq_ms"] for r in prs], dtype=np.float64)
                acq_step_ms = np.array([r["acq_ms_per_step"] for r in prs], dtype=np.float64)
                tot_ms = np.array([r["total_ms"] for r in prs], dtype=np.float64)
                reg = np.array([r["final_regret"] for r in prs], dtype=np.float64)

                rm_mu, rm_lo, rm_hi = _bootstrap_mean_ci(r_steps)
                med_s = float(np.median(r_steps))
                iqr_lo, iqr_hi = np.percentile(r_steps, [25, 75])

                if len(cd_steps) == n and n > 0:
                    rat_cd, rat_cd_lo, rat_cd_hi = _bootstrap_paired_ratio_ci(r_steps, cd_steps)
                else:
                    rat_cd = rat_cd_lo = rat_cd_hi = float("nan")
                if len(kg_steps) == n and n > 0:
                    rat_kg, rat_kg_lo, rat_kg_hi = _bootstrap_paired_ratio_ci(r_steps, kg_steps)
                else:
                    rat_kg = rat_kg_lo = rat_kg_hi = float("nan")

                mc_cert_pct = 100.0 * sum(1 for r in prs if r.get("mc_risk_certified")) / n
                mc_err = sum(1 for r in prs if r.get("mc_risk_cert_error"))
                mc_rm = float(np.mean([r.get("mc_risk_cert_step", r["restricted_steps"]) for r in prs]))

                summary_rows.append(
                    {
                        "beta_mode": bm,
                        "condition": cid,
                        "policy": p,
                        "n": n,
                        "cert_pct": round(100.0 * certs / n, 2),
                        "errors": errs,
                        "err_pct": round(100.0 * errs / n, 3),
                        "cp95_err_upper_pct": round(100.0 * _cp95_upper(errs, n), 3),
                        "restricted_mean": round(rm_mu, 2),
                        "rm_ci95_lo": round(rm_lo, 2),
                        "rm_ci95_hi": round(rm_hi, 2),
                        "median_steps": round(med_s, 1),
                        "iqr_lo": round(float(iqr_lo), 1),
                        "iqr_hi": round(float(iqr_hi), 1),
                        "ratio_vs_cd": round(rat_cd, 3),
                        "ratio_vs_cd_lo": round(rat_cd_lo, 3),
                        "ratio_vs_cd_hi": round(rat_cd_hi, 3),
                        "ratio_vs_kg": round(rat_kg, 3),
                        "ratio_vs_kg_lo": round(rat_kg_lo, 3),
                        "ratio_vs_kg_hi": round(rat_kg_hi, 3),
                        "mean_regret": round(float(np.mean(reg)), 6),
                        "med_discovery_step": round(float(np.median(disc)), 1),
                        "mean_proxy_frac": round(float(np.mean(pfrac)), 4),
                        "med_acq_ms": round(float(np.median(acq_ms)), 2),
                        "med_acq_ms_per_step": round(float(np.median(acq_step_ms)), 4),
                        "med_total_ms": round(float(np.median(tot_ms)), 2),
                        "mc_risk_cert_pct": round(mc_cert_pct, 2),
                        "mc_risk_rm_steps": round(mc_rm, 2),
                        "mc_risk_errors": mc_err,
                        "mean_mc_voi_steps": round(float(np.mean([r.get("mc_voi_steps", 0) for r in prs])), 1),
                        "mean_tail_voi_steps": round(float(np.mean([r.get("tail_voi_steps", 0) for r in prs])), 1),
                    }
                )

                # Fixed-budget checkpoints
                ck_keys = sorted({int(k) for r in prs for k in r.get("checkpoints", {}).keys()})
                for ck in ck_keys:
                    k_str = str(ck)
                    risks = [r["checkpoints"][k_str]["posterior_root_risk"] for r in prs if k_str in r["checkpoints"]]
                    regs = [r["checkpoints"][k_str]["root_regret"] for r in prs if k_str in r["checkpoints"]]
                    c_fl = [r["checkpoints"][k_str]["certified"] for r in prs if k_str in r["checkpoints"]]
                    if not risks:
                        continue
                    rk_mu, rk_lo, rk_hi = _bootstrap_mean_ci(np.array(risks, dtype=np.float64), n_boot=4000)
                    ck_rows.append(
                        {
                            "beta_mode": bm,
                            "condition": cid,
                            "policy": p,
                            "budget_t": ck,
                            "n": len(risks),
                            "mean_post_risk": round(rk_mu, 5),
                            "risk_ci95_lo": round(rk_lo, 5),
                            "risk_ci95_hi": round(rk_hi, 5),
                            "med_post_risk": round(float(np.median(risks)), 5),
                            "mean_root_regret": round(float(np.mean(regs)), 6),
                            "cert_pct_at_t": round(100.0 * float(np.mean(c_fl)), 2),
                        }
                    )

    with out_csv.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)
    if ck_rows:
        with ck_csv.open("w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(ck_rows[0].keys()))
            w.writeheader()
            w.writerows(ck_rows)


def summarize_proxy(rows: list[dict], out_csv: Path) -> None:
    if not rows:
        return
    summary_rows: list[dict] = []
    beta_modes = sorted({r["beta_mode"] for r in rows})
    for bm in beta_modes:
        bm_rows = [r for r in rows if r["beta_mode"] == bm]
        for al in PROXY_ALIGNS:
            for cp in PROXY_COSTS:
                sub = [r for r in bm_rows if abs(r["align"] - al) < 1e-9 and abs(r["c_proxy"] - cp) < 1e-9]
                if not sub:
                    continue
                by_pol = {
                    p: sorted([r for r in sub if r["policy"] == p], key=lambda x: x["seed"])
                    for p in ALL_SEVEN
                }
                cd_cost = np.array([r["restricted_cost"] for r in by_pol.get("cd_joint", [])], dtype=np.float64)
                for p in ALL_SEVEN:
                    prs = by_pol.get(p, [])
                    if not prs:
                        continue
                    n = len(prs)
                    costs = np.array([r["restricted_cost"] for r in prs], dtype=np.float64)
                    steps = np.array([r["restricted_steps"] for r in prs], dtype=np.float64)
                    pfrac = np.array([r["proxy_arm_frac"] for r in prs], dtype=np.float64)
                    certs = sum(1 for r in prs if r["certified"])
                    errs = sum(1 for r in prs if r["false_certificate"])
                    cm, clo, chi = _bootstrap_mean_ci(costs)
                    rat, rlo, rhi = _bootstrap_paired_ratio_ci(costs, cd_cost) if len(cd_cost) == n else (float("nan"),) * 3
                    summary_rows.append(
                        {
                            "beta_mode": bm,
                            "align": al,
                            "c_proxy": cp,
                            "policy": p,
                            "n": n,
                            "cert_pct": round(100.0 * certs / n, 2),
                            "errors": errs,
                            "restricted_mean_cost": round(cm, 3),
                            "cost_ci95_lo": round(clo, 3),
                            "cost_ci95_hi": round(chi, 3),
                            "median_cost": round(float(np.median(costs)), 2),
                            "restricted_mean_steps": round(float(np.mean(steps)), 2),
                            "cost_ratio_vs_cd": round(rat, 3),
                            "cost_ratio_lo": round(rlo, 3),
                            "cost_ratio_hi": round(rhi, 3),
                            "mean_proxy_arm_frac": round(float(np.mean(pfrac)), 4),
                            "med_acq_ms_per_step": round(float(np.median([r["acq_ms_per_step"] for r in prs])), 4),
                        }
                    )
    with out_csv.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(summary_rows[0].keys()))
        w.writeheader()
        w.writerows(summary_rows)


def summarize_all(out_dir: Path) -> None:
    m64 = _load_jsonl(out_dir / "v12_main64_runs.jsonl")
    if m64:
        summarize_main_or_confirm(
            m64,
            out_dir / "v12_main64_summary.csv",
            out_dir / "v12_main64_checkpoints.csv",
            SCALABLE_POLICIES,
        )
    v16 = _load_jsonl(out_dir / "v12_voi16_runs.jsonl")
    if v16:
        summarize_main_or_confirm(
            v16,
            out_dir / "v12_voi16_summary.csv",
            out_dir / "v12_voi16_checkpoints.csv",
            ALL_SEVEN,
        )
    px5 = _load_jsonl(out_dir / "v12_proxy5_runs.jsonl")
    if px5:
        summarize_proxy(px5, out_dir / "v12_proxy5_summary.csv")
    cf = _load_jsonl(out_dir / "v12_confirm_freq_runs.jsonl")
    if cf:
        summarize_main_or_confirm(
            cf,
            out_dir / "v12_confirm_freq_summary.csv",
            out_dir / "v12_confirm_freq_checkpoints.csv",
            SCALABLE_POLICIES,
        )


def _write_manifest(out_dir: Path, smoke: bool, elapsed_s: float) -> None:
    cand = [
        "v12_pilot_summary.csv",
        "v12_main64_runs.jsonl",
        "v12_main64_summary.csv",
        "v12_main64_checkpoints.csv",
        "v12_voi16_runs.jsonl",
        "v12_voi16_summary.csv",
        "v12_voi16_checkpoints.csv",
        "v12_voi16_mc_audit.json",
        "v12_proxy5_runs.jsonl",
        "v12_proxy5_summary.csv",
        "v12_confirm_freq_runs.jsonl",
        "v12_confirm_freq_summary.csv",
        "v12_confirm_freq_checkpoints.csv",
    ]
    files = {}
    for nm in cand:
        p = out_dir / nm
        if p.is_file():
            files[nm] = {"sha256": _sha256(p), "bytes": p.stat().st_size}
    manifest = {
        "experiment": "v12_bed_vs_bo",
        "smoke": bool(smoke),
        "elapsed_s": round(elapsed_s, 2),
        "python": platform.python_version(),
        "files": files,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# Main Runner
# ---------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--stage",
        choices=("pilot", "main64", "voi16", "proxy5", "confirm_freq", "all"),
        default="all",
    )
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(28, max(1, os.cpu_count() or 4)))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize_all(out_dir)
        return

    t0 = time.perf_counter()
    ctx = mp.get_context("spawn")
    stages = ("pilot", "main64", "voi16", "proxy5", "confirm_freq") if args.stage == "all" else (args.stage,)

    # Stage 1: Pilot (separate pilot seeds 1000..1009, 10/condition)
    if "pilot" in stages:
        tp = time.perf_counter()
        p_seeds = list(range(1000, 1002 if args.smoke else 1010))
        p_cap = 2000 if args.smoke else MAIN_CAP
        tasks = [
            (cid, om, rh, p_seeds[i : i + 2], p_cap, SCALABLE_POLICIES, "posterior_credible", MAIN_CHECKPOINTS)
            for cid, om, rh in CONDITIONS
            for i in range(0, len(p_seeds), 2)
        ]
        print(f"[v12 Pilot] Running {len(tasks)} M=64 pilot chunks on {args.workers} workers...", flush=True)
        p_rows: list[dict] = []
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
            for ch in ex.map(_main64_worker, tasks):
                p_rows.extend(ch)
        (out_dir / "v12_pilot_runs.jsonl").write_text("\n".join(json.dumps(r) for r in p_rows) + "\n", encoding="utf-8")
        summarize_main_or_confirm(
            p_rows,
            out_dir / "v12_pilot_summary.csv",
            out_dir / "v12_pilot_checkpoints.csv",
            SCALABLE_POLICIES,
        )
        print(f"[v12 Pilot] Complete ({len(p_rows)} runs) in {time.perf_counter() - tp:.1f}s.", flush=True)

    # Stage 2: Main M=64, K=8 matched-model comparison (4 x 100 x 6 = 2,400 runs)
    if "main64" in stages:
        tm = time.perf_counter()
        n_seeds = 4 if args.smoke else 100
        cap = 1500 if args.smoke else MAIN_CAP
        seeds = list(range(2000, 2000 + n_seeds))
        chunk = 2 if args.smoke else 4
        tasks = [
            (cid, om, rh, seeds[i : i + chunk], cap, SCALABLE_POLICIES, "posterior_credible", MAIN_CHECKPOINTS)
            for cid, om, rh in CONDITIONS
            for i in range(0, len(seeds), chunk)
        ]
        print(f"[v12 Main64] Running {len(tasks)} chunks ({4 * n_seeds * 6} runs, cap={cap}) on {args.workers} workers...", flush=True)
        m_rows: list[dict] = []
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
            for ch in ex.map(_main64_worker, tasks):
                m_rows.extend(ch)
        (out_dir / "v12_main64_runs.jsonl").write_text("\n".join(json.dumps(r) for r in m_rows) + "\n", encoding="utf-8")
        summarize_main_or_confirm(
            m_rows,
            out_dir / "v12_main64_summary.csv",
            out_dir / "v12_main64_checkpoints.csv",
            SCALABLE_POLICIES,
        )
        print(f"[v12 Main64] Complete ({len(m_rows)} runs) in {time.perf_counter() - tm:.1f}s.", flush=True)

    # Stage 3: Small M=16, K=4 Bayesian Root-Risk VOI reference study + MC doubling audit
    if "voi16" in stages:
        tv = time.perf_counter()
        n_seeds = 2 if args.smoke else 40
        cap = 200 if args.smoke else VOI16_CAP
        seeds = list(range(3000, 3000 + n_seeds))
        ny, nmu = (16, 512) if args.smoke else (32, 2048)
        tasks = [
            (cid, om, rh, seeds[i : i + 2], cap, ALL_SEVEN, ny, nmu, "voi16")
            for cid, om, rh in CONDITIONS
            for i in range(0, len(seeds), 2)
        ]
        print(f"[v12 VOI16] Running {len(tasks)} chunks ({4 * n_seeds * 7} runs, cap={cap}, VOI={ny}x{nmu})...", flush=True)
        v_rows: list[dict] = []
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
            for ch in ex.map(_voi16_worker, tasks):
                v_rows.extend(ch)
        (out_dir / "v12_voi16_runs.jsonl").write_text("\n".join(json.dumps(r) for r in v_rows) + "\n", encoding="utf-8")
        summarize_main_or_confirm(
            v_rows,
            out_dir / "v12_voi16_summary.csv",
            out_dir / "v12_voi16_checkpoints.csv",
            ALL_SEVEN,
        )

        # Predetermined MC accuracy doubling audit: (32, 2048) -> (64, 4096) on first 10 seeds/cond (40 instances)
        n_aud = 2 if args.smoke else 10
        aud_seeds = list(range(3000, 3000 + n_aud))
        ny2, nmu2 = (32, 1024) if args.smoke else (64, 4096)
        aud_tasks = [
            (cid, om, rh, aud_seeds[i : i + 2], cap, ("bayesian_voi",), ny2, nmu2, "voi16_double_mc")
            for cid, om, rh in CONDITIONS
            for i in range(0, len(aud_seeds), 2)
        ]
        step_tasks = [(cid, om, rh, aud_seeds) for cid, om, rh in CONDITIONS]
        print(f"[v12 VOI16 MC Audit] Running doubled-MC ({ny2}x{nmu2}) trajectory + step-agreement audit...", flush=True)
        aud_rows: list[dict] = []
        step_res: list[dict] = []
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
            for ch in ex.map(_voi16_worker, aud_tasks):
                aud_rows.extend(ch)
            for sr in ex.map(_voi16_step_agreement_worker, step_tasks):
                step_res.append(sr)

        # Compare base (32, 2048) vs doubled (64, 4096) on identical audit seeds
        base_sub = [r for r in v_rows if r["policy"] == "bayesian_voi" and r["seed"] in set(aud_seeds)]
        base_rm = float(np.mean([r["restricted_steps"] for r in base_sub]))
        dbl_rm = float(np.mean([r["restricted_steps"] for r in aud_rows]))
        base_mc_rm = float(np.mean([r["mc_risk_cert_step"] for r in base_sub]))
        dbl_mc_rm = float(np.mean([r["mc_risk_cert_step"] for r in aud_rows]))
        tot_st = sum(x["total_states"] for x in step_res)
        tot_ex = sum(x["exact_agree"] for x in step_res)
        tot_t2 = sum(x["top2_agree"] for x in step_res)
        audit_report = {
            "base_mc": [ny, nmu],
            "doubled_mc": [ny2, nmu2],
            "n_audit_instances": len(aud_rows),
            "base_ellipsoid_rm": round(base_rm, 2),
            "doubled_ellipsoid_rm": round(dbl_rm, 2),
            "rel_diff_ellipsoid_pct": round(100.0 * abs(dbl_rm - base_rm) / max(1.0, base_rm), 2),
            "base_mc_risk_rm": round(base_mc_rm, 2),
            "doubled_mc_risk_rm": round(dbl_mc_rm, 2),
            "rel_diff_mc_risk_pct": round(100.0 * abs(dbl_mc_rm - base_mc_rm) / max(1.0, base_mc_rm), 2),
            "step_states_audited": tot_st,
            "step_exact_agree_pct": round(100.0 * tot_ex / max(1, tot_st), 2),
            "step_top2_agree_pct": round(100.0 * tot_t2 / max(1, tot_st), 2),
            "mean_score_corr": round(float(np.mean([x["mean_score_corr"] for x in step_res])), 4),
            "per_condition": step_res,
        }
        (out_dir / "v12_voi16_mc_audit.json").write_text(json.dumps(audit_report, indent=2) + "\n", encoding="utf-8")
        print(f"[v12 VOI16] Complete in {time.perf_counter() - tv:.1f}s | MC audit: {audit_report}", flush=True)

    # Stage 4: Cost-sensitive M=5, K=2, d=3 Proxy Benchmark (6 cells x 80 seeds x 7 policies x 2 stop rules)
    if "proxy5" in stages:
        tx = time.perf_counter()
        n_seeds = 4 if args.smoke else 80
        cap = 400 if args.smoke else PROXY_CAP
        seeds = list(range(4000, 4000 + n_seeds))
        chunk = 2 if args.smoke else 10
        beta_modes = ("posterior_credible", "anytime_frequentist")
        tasks = [
            (al, cp, seeds[i : i + chunk], cap, beta_modes)
            for al in PROXY_ALIGNS
            for cp in PROXY_COSTS
            for i in range(0, len(seeds), chunk)
        ]
        print(f"[v12 Proxy5] Running {len(tasks)} chunks ({6 * n_seeds * 7 * 2} runs) on {args.workers} workers...", flush=True)
        px_rows: list[dict] = []
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
            for ch in ex.map(_proxy5_worker, tasks):
                px_rows.extend(ch)
        (out_dir / "v12_proxy5_runs.jsonl").write_text("\n".join(json.dumps(r) for r in px_rows) + "\n", encoding="utf-8")
        summarize_proxy(px_rows, out_dir / "v12_proxy5_summary.csv")
        print(f"[v12 Proxy5] Complete ({len(px_rows)} runs) in {time.perf_counter() - tx:.1f}s.", flush=True)

    # Stage 5: Confirmatory Fixed-Feature M=64, K=8, d=8 Anytime-Valid Frequentist vs. Credible Stopping
    if "confirm_freq" in stages:
        tc = time.perf_counter()
        n_seeds = 4 if args.smoke else 100
        cap = 1500 if args.smoke else MAIN_CAP
        seeds = list(range(5000, 5000 + n_seeds))
        chunk = 2 if args.smoke else 5
        beta_modes = ("anytime_frequentist", "posterior_credible")
        tasks = [
            (cid, om, rh, seeds[i : i + chunk], cap, SCALABLE_POLICIES, beta_modes)
            for cid, om, rh in CONDITIONS
            for i in range(0, len(seeds), chunk)
        ]
        print(f"[v12 ConfirmFreq] Running {len(tasks)} chunks ({4 * n_seeds * 6 * 2} runs) on {args.workers} workers...", flush=True)
        cf_rows: list[dict] = []
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
            for ch in ex.map(_confirm_freq_worker, tasks):
                cf_rows.extend(ch)
        (out_dir / "v12_confirm_freq_runs.jsonl").write_text("\n".join(json.dumps(r) for r in cf_rows) + "\n", encoding="utf-8")
        summarize_main_or_confirm(
            cf_rows,
            out_dir / "v12_confirm_freq_summary.csv",
            out_dir / "v12_confirm_freq_checkpoints.csv",
            SCALABLE_POLICIES,
        )
        print(f"[v12 ConfirmFreq] Complete ({len(cf_rows)} runs) in {time.perf_counter() - tc:.1f}s.", flush=True)

    _write_manifest(out_dir, args.smoke, time.perf_counter() - t0)
    print(f"[v12] Finished stage={args.stage} in {time.perf_counter() - t0:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
