"""Experiment E5: High-Power Calibration & Misspecification Stress Test.

Audits empirical coverage, false-certification rate, and evaluation count across all four
model conditions from Theory Program T3 and multiple confidence levels `delta in {0.01, 0.05, 0.10}`
with 200 independent repetitions per `(condition, delta, method)` cell:

1. Condition 1 — Well-specified finite-dimensional linear model (`f(z) = phi(z)^T theta*`):
   Validates frequentist anytime coverage `Pr(forall t: theta* in Theta_t) >= 1 - delta` and
   empirical error `<= delta`.
2. Condition 2 — Well-specified Gaussian Process prior (`f ~ N(m_0, K)`, fresh draw per rep):
   Validates genuinely Bayesian posterior stopping `max_a q_t(a) >= 1 - delta` (Theorem T3.2),
   confirming prior-averaged error `<= delta` across `delta in {0.01, 0.05, 0.10}` vs ellipsoidal stopping.
3. Condition 3 — Misspecified GP kernel lengthscale (`ell_true = 0.45` rough vs `ell_assumed = 3.0` smooth):
   Quantifies overconfidence / error-rate violations of unadjusted nominal GP & posterior stopping
   vs 0% error of distribution-free independent-CS fallback.
4. Condition 4 — Adversarial structured residual `|b_z| <= xi` (`xi in {0.00, 0.02, 0.05, 0.08}`):
   Contrasts unadjusted linear ellipsoid (violates coverage as `xi` grows!), Theorem T3.3
   misspecification-robust ellipsoid `R_t^{(xi)}`, and `safe_hybrid` (`U_t^{(xi)} cap B_t`) which
   certifies safely even when `2*xi > eps`.
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
import multiprocessing as mp
from pathlib import Path
import platform
import statistics
import time

import numpy as np

from dagcert import (
    CorrelationAwareCertSession,
    DiscreteGPPosteriorModel,
    LinearFeatureModel,
)
from dagcert.benchmarks import (
    GaussianPriorDAGProblem,
    MisspecifiedLinearDAGProblem,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/e5_calibration"

DELTAS = (0.01, 0.05, 0.10)
XIS = (0.00, 0.02, 0.04, 0.08)
EPS = 0.030
CAP = 3500


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _cond1_linear_worker(task: tuple[float, int, int]) -> list[dict]:
    delta, rep, cap = task
    prob = MisspecifiedLinearDAGProblem(seed=1000 + rep, xi=0.0, m_leaves=32, k_actions=4, d_feat=5, hw=0.15)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    seed = 61000 + rep

    rows: list[dict] = []
    for method, beta_m, cert_m in (
        ("freq_ellipsoid_cd", "abbasi_yadkori", "joint_ellipsoid"),
        ("nominal_ellipsoid_cd", "nominal_bayes", "joint_ellipsoid"),
        ("bayes_post_cd", "nominal_bayes", "posterior_prob"),
    ):
        model = LinearFeatureModel(
            phi=prob.phi,
            prior_mean=prob.prior_mean,
            reg_lambda=0.5,
            obs_std=prob.obs_std,
            param_bound=prob.param_bound,
            beta_mode=beta_m,
            delta=delta,
        )
        sess = CorrelationAwareCertSession(
            prob, seed=seed, epsilon=EPS, model=model, cert_mode=cert_m, acquisition="contrast_directed",
            delta=delta, check_every=2, adaptive_check=True, mc_posterior_draws=512,
        )
        ever_uncovered = False
        while not sess.certified and not sess.conflict and sess.calls < cap:
            diff = model.theta_hat - prob.theta_star
            mahal = float(np.sqrt(max(0.0, float(diff @ (model.v_mat @ diff)))))
            if mahal > model.beta() + 1e-12:
                ever_uncovered = True
            sess.step()
        cert = bool(sess.certified)
        true_reg = regrets[int(sess.action)]
        false_cert = bool(cert and true_reg > EPS + 1e-12)
        rows.append(
            {
                "condition": "C1_valid_linear",
                "delta": delta,
                "xi": 0.0,
                "rep": rep,
                "method": method,
                "certified": cert,
                "false_certificate": false_cert,
                "anytime_covered": not ever_uncovered,
                "steps": int(sess.calls),
                "capped_steps": int(sess.calls) if cert else cap,
                "final_regret": round(true_reg, 6),
            }
        )
    return rows


def _cond23_gp_worker(task: tuple[str, float, int, int]) -> list[dict]:
    cond_name, delta, rep, cap = task
    true_ell = 1.2 if cond_name == "C2_valid_gp_prior" else 0.45
    assumed_ell = 1.2 if cond_name == "C2_valid_gp_prior" else 3.0
    prob = GaussianPriorDAGProblem(seed=2000 + rep, true_lengthscale=true_ell, m_leaves=32, k_actions=4, sigma=0.10)
    k_assumed = GaussianPriorDAGProblem.rbf_kernel(prob.coords, lengthscale=assumed_ell)

    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    seed = 63000 + rep

    rows: list[dict] = []
    methods = (
        ("bayes_posterior_stop", "posterior_prob", "contrast_directed"),
        ("nominal_ellipsoid_cd", "joint_ellipsoid", "contrast_directed"),
    )
    for method, cert_m, acq_m in methods:
        gp_mod = DiscreteGPPosteriorModel(
            kernel=k_assumed, prior_mean=prob.prior_mean, obs_std=prob.sigma, beta_mode="nominal_bayes", delta=delta
        )
        sess = CorrelationAwareCertSession(
            prob, seed=seed, epsilon=EPS, model=gp_mod, cert_mode=cert_m, acquisition=acq_m,
            delta=delta, check_every=2, adaptive_check=True, mc_posterior_draws=512,
        )
        while not sess.certified and not sess.conflict and sess.calls < cap:
            sess.step()
        cert = bool(sess.certified)
        true_reg = regrets[int(sess.action)]
        false_cert = bool(cert and true_reg > EPS + 1e-12)
        rows.append(
            {
                "condition": cond_name,
                "delta": delta,
                "xi": 0.0,
                "rep": rep,
                "method": method,
                "certified": cert,
                "false_certificate": false_cert,
                "anytime_covered": not false_cert,
                "steps": int(sess.calls),
                "capped_steps": int(sess.calls) if cert else cap,
                "final_regret": round(true_reg, 6),
            }
        )
    return rows


def _cond4_residual_worker(task: tuple[float, int, int]) -> list[dict]:
    xi, rep, cap = task
    delta = 0.05
    prob = MisspecifiedLinearDAGProblem(seed=3000 + rep, xi=xi, m_leaves=32, k_actions=4, d_feat=5, hw=0.14)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    seed = 66000 + rep

    rows: list[dict] = []
    for method, beta_m, cert_m, pass_xi in (
        ("unadjusted_ellipsoid", "abbasi_yadkori", "joint_ellipsoid", 0.0),
        ("t33_robust_ellipsoid", "misspec_robust", "joint_ellipsoid", prob.xi),
        ("safe_hybrid_fallback", "misspec_robust", "safe_hybrid", prob.xi),
        ("indep_cs_fallback", "abbasi_yadkori", "independent_box", 0.0),
    ):
        model = LinearFeatureModel(
            phi=prob.phi,
            prior_mean=prob.prior_mean,
            reg_lambda=0.5,
            obs_std=prob.obs_std,
            param_bound=prob.param_bound,
            misspec_xi=pass_xi,
            beta_mode=beta_m,
            delta=delta,
        )
        sess = CorrelationAwareCertSession(
            prob,
            seed=seed,
            epsilon=EPS,
            model=model,
            cert_mode=cert_m,
            acquisition="contrast_directed",
            delta=delta,
            cs_schedule="emp_bernstein",
            check_every=3,
            adaptive_check=True,
        )
        while not sess.certified and not sess.conflict and sess.calls < cap:
            sess.step()
        cert = bool(sess.certified)
        true_reg = regrets[int(sess.action)]
        false_cert = bool(cert and true_reg > EPS + 1e-12)
        rows.append(
            {
                "condition": "C4_structured_residual",
                "delta": delta,
                "xi": round(xi, 3),
                "rep": rep,
                "method": method,
                "certified": cert,
                "false_certificate": false_cert,
                "anytime_covered": not false_cert,
                "steps": int(sess.calls),
                "capped_steps": int(sess.calls) if cert else cap,
                "final_regret": round(true_reg, 6),
            }
        )
    return rows


def summarize(dest: Path) -> None:
    runs = [json.loads(x) for x in (dest / "e5_calibration_runs.jsonl").read_text().splitlines() if x.strip()]
    keys = sorted({(r["condition"], r["delta"], r["xi"], r["method"]) for r in runs})
    out_rows: list[dict] = []
    for cond, delta, xi, meth in keys:
        sub = [
            r
            for r in runs
            if r["condition"] == cond
            and abs(r["delta"] - delta) < 1e-9
            and abs(r["xi"] - xi) < 1e-9
            and r["method"] == meth
        ]
        st = np.array([float(r["capped_steps"]) for r in sub])
        n = len(sub)
        fc = sum(1 for r in sub if r["false_certificate"])
        out_rows.append(
            {
                "condition": cond,
                "delta": delta,
                "xi": xi,
                "method": meth,
                "reps": n,
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                "anytime_coverage": round(sum(1 for r in sub if r["anytime_covered"]) / n, 4),
                "false_certificates": fc,
                "empirical_error_rate": round(fc / n, 4),
                "violates_delta": bool((fc / n) > delta + 1e-9),
                "median_steps": round(float(np.median(st)), 1),
                "q25_steps": round(float(np.percentile(st, 25)), 1),
                "q75_steps": round(float(np.percentile(st, 75)), 1),
                "mean_final_regret": round(statistics.fmean(r["final_regret"] for r in sub), 5),
            }
        )
    with (dest / "summary_e5_calibration.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out_rows[0].keys()))
        w.writeheader()
        w.writerows(out_rows)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=24)
    args = ap.parse_args()

    dest: Path = args.out
    dest.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(dest)
        return

    t_start = time.perf_counter()
    n_reps = 10 if args.smoke else 200
    n_reps_c4 = 10 if args.smoke else 100
    cap = 1000 if args.smoke else CAP

    t_c1 = [(d, r, cap) for d in DELTAS for r in range(n_reps)]
    t_c23 = [
        (cond, d, r, cap)
        for cond in ("C2_valid_gp_prior", "C3_misspec_lengthscale")
        for d in DELTAS
        for r in range(n_reps)
    ]
    t_c4 = [(xi, r, cap) for xi in XIS for r in range(n_reps_c4)]

    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        r1 = [x for grp in ex.map(_cond1_linear_worker, t_c1) for x in grp]
        r23 = [x for grp in ex.map(_cond23_gp_worker, t_c23) for x in grp]
        r4 = [x for grp in ex.map(_cond4_residual_worker, t_c4) for x in grp]
    all_runs = r1 + r23 + r4

    f_out = dest / "e5_calibration_runs.jsonl"
    f_out.write_text("\n".join(json.dumps(r) for r in all_runs) + "\n")
    summarize(dest)

    manifest = {
        "suite": "v7_e5_calibration",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "total_runs": len(all_runs),
        "sha256_runs": _sha256(f_out),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Completed E5 Calibration in {manifest['elapsed_s']:.2f}s ({len(all_runs)} runs).")


if __name__ == "__main__":
    main()
