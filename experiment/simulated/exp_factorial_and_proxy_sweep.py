"""Experiment v8-3 (P1): Deconfounded 3-Factor Phase Diagram (Overlap x Correlation x Mismatch) & Proxy Mechanism Sweep.

Removes the low-rank confound from earlier 2D phase experiments by using a full-rank
M=64 terminal model (`DeconfoundedOverlapCorrelationProblem`) where:
  - rho = 0 gives strictly diagonal covariance K(0) = tau0^2 I_64 (zero cross-terminal information),
  - Every cell satisfies zero support containments and identical exterior margin Gamma_ext(a*),
  - Adversarial misspecification xi in {0.0, 0.015, 0.040} injects controlled residual bias |b_z| <= xi.

Part A — 48-Cell Deconfounded 3-Factor Factorial (4 omega x 4 rho x 3 xi, 16 seeds/cell):
  Evaluates a clean Certificate x Acquisition x Information-Model factorial:
    1. `indep_box__os`     : Distribution-free Empirical Bernstein box + Optimistic-Separation
    2. `diag_gp__os`       : Diagonal Gaussian ellipsoid K_diag + Optimistic-Separation (no correlation)
    3. `corr_gp__os`       : Full correlated GP ellipsoid K(rho) + Optimistic-Separation (cert gain only)
    4. `corr_gp__direct`   : Full correlated GP ellipsoid K(rho) + Direct-Witness acquisition
    5. `corr_gp__cd`       : Full correlated GP ellipsoid K(rho) + Contrast-Directed acquisition
    6. `robust_hybrid__cd` : Valid misspecification-robust Smart Hybrid (delta/2 + delta/2 DF fallback)
  Produces exact additive decomposition (overlap effect, Gaussian-vs-EB effect, correlation certificate
  effect, contrast-directed acquisition effect, and mismatch safety tradeoff).

Part B — Extended Low-Valued Proxy Mechanism Sweep (5 alignments x 5 cost ratios, 40 seeds/cell):
  Sweeps proxy-contrast cosine alignment cos(phi_proxy, g*) in {0.20, 0.50, 0.80, 0.95, 0.99} and
  proxy relative cost c_proxy / c_target in {0.25, 0.50, 1.0, 2.0, 4.0}, comparing cost-normalized
  CD-Joint, cost-agnostic CD-Joint, Direct-Witness Joint, and Independent OS.
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

from dagcert import DAG, Problem
from dagcert import HybridWitnessDAGLUCBSession
from dagcert import (
    CorrelationAwareCertSession,
    LinearFeatureModel,
)
from dagcert._core.v7_benchmarks import _UniformBoundedOracle
from dagcert._core.v8_unified_experiments import (
    CalibratedGPPosteriorModel,
    DeconfoundedOverlapCorrelationProblem,
    SmartHybridCertSession,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/v8_exp3_factorial_phase"

OMEGAS = (0.0, 0.25, 0.50, 0.75)
RHOS = (0.0, 0.30, 0.60, 0.90)
XIS = (0.0, 0.015, 0.045)
PHASE_EPS = 0.025
PHASE_DELTA = 0.05
PHASE_CAP = 12000

FACTORIAL_METHODS = (
    ("indep_box__os", "distribution_free"),
    ("diag_gp__os", "diagonal_gp"),
    ("corr_gp__ucb", "correlated_gp"),
    ("corr_gp__os", "correlated_gp"),
    ("corr_gp__cd", "correlated_gp"),
    ("robust_hybrid__cd", "hybrid_valid"),
)

PROXY_ALIGNS = (0.20, 0.50, 0.80, 0.95, 0.99)
PROXY_COST_RATIOS = (0.25, 0.50, 1.0, 2.0, 4.0)
PROXY_EPS = 0.015
PROXY_DELTA = 0.05
PROXY_CAP = 3500


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class TunableProxyDAGProblem(Problem):
    """5-terminal proxy DAG parameterized by exact proxy-contrast cosine alignment `align`."""

    def __init__(self, align: float, hw: float = 0.16) -> None:
        children: list[tuple[int, ...]] = [
            (1, 2),
            (3, 4, 5, 7),
            (4, 6, 7),
            (),
            (),
            (),
            (),
            (),
        ]
        labels = ["root", "a0", "a1", "z_in", "z_sh", "z_sub", "z_out", "z_proxy"]
        graph = DAG(children, root=0, labels=labels)

        # Active contrast g* = phi(z_out) - phi(z_in) = (0, 0.20, 0) -> unit direction e_2
        # Proxy feature has norm 0.95 with component `align` along -e_2 and `sqrt(1 - align^2)` along -e_1
        # (so proxy remains low-value and never acts as inside/outside witness!)
        a_clamped = max(0.05, min(0.995, float(align)))
        orth = math.sqrt(max(0.0, 1.0 - a_clamped * a_clamped))
        self.prior_mean = 0.50
        self.phi = np.array(
            [
                [0.98, -0.10, 0.00],                       # z_in
                [0.00, 0.00, 0.40],                        # z_sh
                [-0.35, 0.00, 0.00],                       # z_sub
                [0.98, +0.10, 0.00],                       # z_out
                [-0.95 * orth, -0.95 * a_clamped, 0.00],   # z_proxy (low mean, tunable alignment)
            ],
            dtype=np.float64,
        )
        self.theta_star = np.array([0.22, -0.22, 0.40], dtype=np.float64)
        self.param_bound = float(np.linalg.norm(self.theta_star)) + 0.05
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))
        f_vals = self.prior_mean + (self.phi @ self.theta_star)
        means = {3 + i: float(f_vals[i]) for i in range(5)}
        super().__init__(f"tunable_proxy_a{a_clamped:.2f}", graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)


def _phase_cell_worker(task: tuple[float, float, float, list[int], int]) -> list[dict]:
    omega, rho, xi, seeds, cap = task
    rows: list[dict] = []
    for s in seeds:
        prob = DeconfoundedOverlapCorrelationProblem(
            seed=5000 + s * 17 + int(round(omega * 100)) * 7 + int(round(rho * 100)) * 3,
            overlap=omega,
            rho=rho,
            mismatch_xi=xi,
            target_margin=0.055,
            hw=0.14,
        )
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

        k_full = prob.kernel
        k_diag = prob.diag_kernel
        run_seed = 850000 + s * 97 + int(round(omega * 100)) * 13

        for method, track in FACTORIAL_METHODS:
            t0 = time.perf_counter()
            if method == "indep_box__os":
                sess = HybridWitnessDAGLUCBSession(
                    prob, run_seed, PHASE_EPS, mode="opt_sep", delta=PHASE_DELTA, schedule="emp_bernstein"
                )
                while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                    sess.step()
                cert = bool(sess.certified)
                act = int(sess.action) if cert else int(sess.monitor.query_dual_witness()[0])
                cert_ms = 0.0
            elif method == "robust_hybrid__cd":
                gp_m = CalibratedGPPosteriorModel(
                    kernel=k_full,
                    prior_mean=prob.prior_mean,
                    obs_std=prob.obs_std,
                    delta=0.5 * PHASE_DELTA,
                    misspec_xi=xi,
                    enable_eb_calib=False,
                )
                sess = SmartHybridCertSession(
                    prob,
                    seed=run_seed,
                    epsilon=PHASE_EPS,
                    model=gp_m,
                    cert_mode="smart_hybrid",
                    acquisition="contrast_directed",
                    delta=PHASE_DELTA,
                    cs_schedule="emp_bernstein",
                    check_every=6,
                    adaptive_check=True,
                )
                while not sess.certified and not sess.conflict and sess.calls < cap:
                    sess.step()
                cert = bool(sess.certified)
                act = int(sess.action) if cert else int(sess.best_recommendation())
                cert_ms = 1e3 * float(sess.ellipsoid_cert.cert_time_s)
            else:
                k_use = k_diag if method == "diag_gp__os" else k_full
                acq = {
                    "diag_gp__os": "opt_sep_gp",
                    "corr_gp__ucb": "gp_ucb",
                    "corr_gp__os": "opt_sep_gp",
                    "corr_gp__cd": "contrast_directed",
                }[method]
                gp_m = CalibratedGPPosteriorModel(
                    kernel=k_use,
                    prior_mean=prob.prior_mean,
                    obs_std=prob.obs_std,
                    delta=PHASE_DELTA,
                    misspec_xi=0.0,
                    enable_eb_calib=False,
                )
                # Map `opt_sep_gp` cleanly: run SmartHybridCertSession with joint_robust stopping + GP opt-sep or witness
                if acq == "opt_sep_gp":
                    # Use GP-guided Optimistic-Separation: pick leaf from top optimistic-separation pair by GP std
                    sess = _GPOptSepSession(prob, run_seed, PHASE_EPS, gp_m, delta=PHASE_DELTA, check_every=6)
                else:
                    sess = SmartHybridCertSession(
                        prob,
                        seed=run_seed,
                        epsilon=PHASE_EPS,
                        model=gp_m,
                        cert_mode="joint_robust",
                        acquisition=acq,
                        delta=PHASE_DELTA,
                        check_every=6,
                        adaptive_check=True,
                    )
                while not sess.certified and not getattr(sess, "conflict", False) and sess.calls < cap:
                    sess.step()
                cert = bool(sess.certified)
                act = int(sess.action) if cert else int(sess.best_recommendation())
                cert_ms = 1e3 * float(sess.ellipsoid_cert.cert_time_s)

            elapsed_ms = 1e3 * (time.perf_counter() - t0)
            true_reg = regrets[act]
            fc = bool(cert and true_reg > PHASE_EPS + 1e-12)
            rows.append(
                {
                    "omega": omega,
                    "rho": rho,
                    "xi": xi,
                    "seed": s,
                    "method": method,
                    "track": track,
                    "certified": cert,
                    "false_certificate": fc,
                    "steps": int(sess.calls),
                    "capped_steps": int(sess.calls) if cert else cap,
                    "final_regret": round(true_reg, 6),
                    "cert_ms": round(cert_ms, 2),
                    "total_ms": round(elapsed_ms, 2),
                }
            )
    return rows


class _GPOptSepSession(SmartHybridCertSession):
    """Isolates certificate geometry from acquisition: evaluates joint GP ellipsoid certificate
    while sampling via Optimistic-Separation witnesses on GP marginal intervals (no contrast-directed)."""

    def __init__(self, problem: Problem, seed: int, epsilon: float, model: CalibratedGPPosteriorModel, delta: float, check_every: int = 6) -> None:
        super().__init__(
            problem=problem,
            seed=seed,
            epsilon=epsilon,
            model=model,
            cert_mode="joint_robust",
            acquisition="direct_witness",
            delta=delta,
            check_every=check_every,
            adaptive_check=True,
        )

    def _select_next_arm(self, means, psi, stds, beta, ucb):
        lo = means - beta * stds
        hi = means + beta * stds
        best_sep = -math.inf
        best_p, best_q = 0, -1
        for a in range(len(self.support_struct.supports)):
            sup = self.support_struct.supports[a]
            comp = self.support_struct.complements[a]
            if len(comp) == 0:
                continue
            sep = float(np.max(hi[sup]) - np.max(lo[comp]))
            if sep > best_sep:
                best_sep = sep
                best_p = int(sup[int(np.argmax(lo[sup]))])
                best_q = int(comp[int(np.argmax(hi[comp]))])
        if best_q < 0:
            return best_p
        return best_p if float(stds[best_p]) >= float(stds[best_q]) else best_q


def _proxy_sweep_worker(task: tuple[float, float, list[int], int]) -> list[dict]:
    align, cost_ratio, seeds, cap = task
    prob = TunableProxyDAGProblem(align=align, hw=0.16)
    costs = np.array([1.0, 1.0, 1.0, 1.0, float(cost_ratio)], dtype=np.float64)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    rows: list[dict] = []
    for s in seeds:
        run_seed = 860000 + s * 41 + int(round(align * 100)) * 7
        for method in ("cd_joint_costnorm", "cd_joint_uniform", "direct_witness_joint", "indep_os"):
            t0 = time.perf_counter()
            if method == "indep_os":
                sess = HybridWitnessDAGLUCBSession(
                    prob, run_seed, PROXY_EPS, mode="opt_sep", delta=PROXY_DELTA, schedule="emp_bernstein"
                )
                while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                    sess.step()
                obs = sess.oracle.obs
                proxy_pulls = int(obs[7])
                tot_cost = float(sum(obs[3 + i] * costs[i] for i in range(5)))
                cert = bool(sess.certified)
                act = int(sess.action)
            else:
                model = LinearFeatureModel(
                    phi=prob.phi,
                    prior_mean=prob.prior_mean,
                    reg_lambda=0.5,
                    obs_std=prob.obs_std,
                    param_bound=prob.param_bound,
                    beta_mode="abbasi_yadkori",
                    delta=PROXY_DELTA,
                )
                acq = "direct_witness" if method == "direct_witness_joint" else "contrast_directed"
                c_arg = costs if method == "cd_joint_costnorm" else np.ones(5, dtype=np.float64)
                sess = CorrelationAwareCertSession(
                    prob,
                    seed=run_seed,
                    epsilon=PROXY_EPS,
                    model=model,
                    cert_mode="joint_ellipsoid",
                    acquisition=acq,
                    delta=PROXY_DELTA,
                    costs=c_arg,
                    check_every=1,
                    adaptive_check=False,
                )
                while not sess.certified and not sess.conflict and sess.calls < cap:
                    sess.step()
                obs = sess.oracle.obs
                proxy_pulls = int(obs[7])
                tot_cost = float(sum(obs[3 + i] * costs[i] for i in range(5)))
                cert = bool(sess.certified)
                act = int(sess.action)
            true_reg = regrets[act]
            rows.append(
                {
                    "align": align,
                    "cost_ratio": cost_ratio,
                    "seed": s,
                    "method": method,
                    "certified": cert,
                    "false_certificate": bool(cert and true_reg > PROXY_EPS + 1e-12),
                    "steps": int(sess.calls),
                    "capped_steps": int(sess.calls) if cert else cap,
                    "total_cost": round(tot_cost if cert else float(cap) * max(1.0, cost_ratio), 3),
                    "proxy_pulls": proxy_pulls,
                    "proxy_frac": round(proxy_pulls / max(1, int(sess.calls)), 4),
                    "total_ms": round(1e3 * (time.perf_counter() - t0), 2),
                }
            )
    return rows


def summarize(dest: Path) -> None:
    # Part A
    pa = dest / "v8_exp3_phase_runs.jsonl"
    if pa.exists():
        runs = [json.loads(x) for x in pa.read_text().splitlines() if x.strip()]
        keys = sorted({(r["omega"], r["rho"], r["xi"], r["method"]) for r in runs})
        rows_a: list[dict] = []
        for om, rh, xi, meth in keys:
            sub = [
                r for r in runs
                if abs(r["omega"] - om) < 1e-9 and abs(r["rho"] - rh) < 1e-9
                and abs(r["xi"] - xi) < 1e-9 and r["method"] == meth
            ]
            n = len(sub)
            st = np.array([float(r["capped_steps"]) for r in sub])
            fc = sum(1 for r in sub if r["false_certificate"])
            rows_a.append(
                {
                    "omega": om,
                    "rho": rh,
                    "xi": xi,
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": fc,
                    "false_cert_rate": round(fc / n, 4),
                    "med_steps": round(float(np.median(st)), 1),
                    "mean_steps": round(float(np.mean(st)), 1),
                    "med_total_ms": round(float(np.median([r["total_ms"] for r in sub])), 2),
                }
            )
        with (dest / "v8_exp3_phase_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_a[0].keys()))
            w.writeheader()
            w.writerows(rows_a)

        # Print clean factorial marginal summary across xi
        print("\n=== v8 Exp 3A: Deconfounded 3-Factor Factorial Summary (by xi) ===")
        for xi in sorted({r["xi"] for r in rows_a}):
            print(f"  --- xi = {xi:.3f} ---")
            for meth, _ in FACTORIAL_METHODS:
                sub = [r for r in runs if abs(r["xi"] - xi) < 1e-9 and r["method"] == meth]
                if not sub:
                    continue
                n = len(sub)
                st = np.array([float(r["capped_steps"]) for r in sub])
                fc = sum(1 for r in sub if r["false_certificate"])
                print(
                    f"    {meth:20s} | cert={100*sum(1 for r in sub if r['certified'])/n:5.1f}% "
                    f"err={fc:3d}/{n} ({100*fc/n:4.1f}%) med={np.median(st):6.1f} mean={np.mean(st):6.1f}"
                )

    # Part B
    pb = dest / "v8_exp3_proxy_runs.jsonl"
    if pb.exists():
        runs = [json.loads(x) for x in pb.read_text().splitlines() if x.strip()]
        keys = sorted({(r["align"], r["cost_ratio"], r["method"]) for r in runs})
        rows_b: list[dict] = []
        for al, cr, meth in keys:
            sub = [
                r for r in runs
                if abs(r["align"] - al) < 1e-9 and abs(r["cost_ratio"] - cr) < 1e-9 and r["method"] == meth
            ]
            n = len(sub)
            rows_b.append(
                {
                    "align": al,
                    "cost_ratio": cr,
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": sum(1 for r in sub if r["false_certificate"]),
                    "med_steps": round(float(np.median([r["capped_steps"] for r in sub])), 1),
                    "med_cost": round(float(np.median([r["total_cost"] for r in sub])), 1),
                    "mean_proxy_frac": round(float(np.mean([r["proxy_frac"] for r in sub])), 4),
                }
            )
        with (dest / "v8_exp3_proxy_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_b[0].keys()))
            w.writeheader()
            w.writerows(rows_b)
        print("\n=== v8 Exp 3B: Proxy Alignment x Relative Cost Sweep (cost_ratio=1.0 slice) ===")
        for r in rows_b:
            if abs(r["cost_ratio"] - 1.0) < 1e-9:
                print(
                    f"  align={r['align']:.2f} | {r['method']:20s} | med_cost={r['med_cost']:6.1f} "
                    f"proxy_frac={100*r['mean_proxy_frac']:5.1f}%"
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
    if args.smoke:
        omegas = (0.0, 0.75)
        rhos = (0.0, 0.90)
        xis = (0.0, 0.045)
        n_phase_seeds = 3
        aligns = (0.20, 0.95)
        c_ratios = (0.50, 2.0)
        n_proxy_seeds = 6
    else:
        omegas = OMEGAS
        rhos = RHOS
        xis = XIS
        n_phase_seeds = 16
        aligns = PROXY_ALIGNS
        c_ratios = PROXY_COST_RATIOS
        n_proxy_seeds = 40

    ctx = mp.get_context("spawn")
    phase_tasks = []
    for om in omegas:
        for rh in rhos:
            for xi in xis:
                for i in range(0, n_phase_seeds, 4):
                    phase_tasks.append((om, rh, xi, list(range(i, min(n_phase_seeds, i + 4))), PHASE_CAP))
    print(f"[v8 Exp 3A] Running {len(phase_tasks)} phase tasks across {args.workers} workers...", flush=True)
    phase_rows: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_phase_cell_worker, phase_tasks):
            phase_rows.extend(ch)
    (out_dir / "v8_exp3_phase_runs.jsonl").write_text("\n".join(json.dumps(r) for r in phase_rows) + "\n")

    proxy_tasks = []
    for al in aligns:
        for cr in c_ratios:
            for i in range(0, n_proxy_seeds, 10):
                proxy_tasks.append((al, cr, list(range(i, min(n_proxy_seeds, i + 10))), PROXY_CAP))
    print(f"[v8 Exp 3B] Running {len(proxy_tasks)} proxy sweep tasks...", flush=True)
    proxy_rows: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_proxy_sweep_worker, proxy_tasks):
            proxy_rows.extend(ch)
    (out_dir / "v8_exp3_proxy_runs.jsonl").write_text("\n".join(json.dumps(r) for r in proxy_rows) + "\n")

    summarize(out_dir)
    artifacts = [
        "v8_exp3_phase_runs.jsonl",
        "v8_exp3_phase_summary.csv",
        "v8_exp3_proxy_runs.jsonl",
        "v8_exp3_proxy_summary.csv",
    ]
    manifest = {
        "experiment": "v8_exp3_factorial_phase",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v8 Exp 3] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
