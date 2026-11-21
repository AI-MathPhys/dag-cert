"""Experiment v8-2 (P0): Decision-Aware Information Tracking vs. Contrast-Directed Joint Certification.

Empirical verification of Theorem 2.8 (asymptotic optimality of Gaussian information tracking)
and practical compute-vs-sample-efficiency comparison across three regimes:

Part A — Small Exact Gaussian Instances (M in {5, 16, 32, 64}, d in {3, 4, 6, 8}):
  - Independently verifies characteristic time T_*^eps(theta) = 1 / I_*^eps(theta) via CVXPY QP
    and random Dirichlet design dominance checks (`verify_characteristic_rate_independently`).
  - Sweeps confidence delta in {0.10, 0.05, 0.02, 0.01, 0.005} (80 reps/cell) under exact
    Gaussian observations N(mu_z, sigma^2), comparing:
      1. `info_tracking`      : Regularized C-tracking directly optimizing I_*(theta_hat)
      2. `hybrid_cd_tracking` : Contrast-Directed warm-up -> Info-Tracking refinement
      3. `cd_joint`           : Contrast-Directed acquisition + exact joint conic stopping
      4. `gp_ucb_joint`       : GP-UCB acquisition + exact joint conic stopping
      5. `indep_gauss_os`     : Independent-coordinate Gaussian Optimistic-Separation
  - Reports E[tau_delta] / (T_*^eps(theta) * log(1/delta)), empirical error rate, and runtime.

Part B — Medium Overlapping Search DAGs (M in {128, 256, 512}, d in {8, 16, 32}):
  - Compares sample efficiency AND compute cost (tracker planning ms, conic cert ms, total ms)
    across 20 seeds per (M, d) scale.

Part C — Difficult Multiple-Answer Tied-Optima Instances (`MultiAnswerCommitmentDAGProblem`):
  - Multiple eps-optimal root actions where the statistically easiest action a* = argmax I_a(theta)
    differs from the nominal highest-mean action. Tests whether tracking identifies and certifies a*
    more reliably and faster than CD-Joint and Independent OS (60 reps).
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

from dag_mcts.graph import DAG, Problem
from dag_mcts.v7_bayesian_ucd import (
    CorrelationAwareCertSession,
    LinearFeatureModel,
    SupportStructure,
    compute_characteristic_rate,
)
from dag_mcts.v7_benchmarks import (
    MotivationalProxyDAGProblem,
    MultiAnswerCommitmentDAGProblem,
    ScalingDAGProblem,
    _GaussianOracle,
)
from dag_mcts.v8_unified_experiments import (
    RegularizedInfoTrackerSession,
    fast_characteristic_rate,
    verify_characteristic_rate_independently,
)


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/bayesian_ucd_v1/v8_exp2_info_tracking"

DELTAS = (0.10, 0.05, 0.02, 0.01, 0.005, 1e-4)
METHODS = ("info_tracking", "hybrid_cd_tracking", "cd_joint", "gp_ucb_joint", "indep_gauss_os")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ExactGaussianLinearDAG(Problem):
    """Exact Gaussian linear-feature DAG with zero support containments and calibrated margin."""

    def __init__(
        self,
        name: str,
        seed: int,
        m_leaves: int,
        k_actions: int,
        d_feat: int,
        sigma: float = 0.12,
        target_margin: float = 0.09,
    ) -> None:
        base = ScalingDAGProblem(
            seed=seed, m_leaves=m_leaves, k_actions=k_actions, d_feat=d_feat, support_style="compact"
        )
        self.prior_mean = 0.50
        self.phi = base.phi.copy()
        self.sigma = float(sigma)
        self.obs_std = float(sigma)

        # Calibrate theta_star so the exterior margin Gamma_ext(a*) is cleanly >= target_margin
        ss = SupportStructure(base.graph)
        rng = np.random.default_rng(seed * 7919 + 31)
        theta = rng.standard_normal(d_feat)
        theta /= max(1e-12, float(np.linalg.norm(theta)))
        f_raw = self.phi @ theta
        # Scale theta so exterior gap of winning action == target_margin
        vals_a = [float(np.max(f_raw[sup])) for sup in ss.supports]
        a_win = int(np.argmax(vals_a))
        comp_w = ss.complements[a_win]
        raw_gap = vals_a[a_win] - float(np.max(f_raw[comp_w]))
        if raw_gap < 0.04:
            # Boost winner private direction cleanly
            priv = np.setdiff1d(ss.supports[a_win], np.concatenate([ss.supports[b] for b in range(k_actions) if b != a_win]))
            if len(priv) > 0:
                dir_v = np.mean(self.phi[priv], axis=0) - np.mean(self.phi[comp_w], axis=0)
                dir_v /= max(1e-12, float(np.linalg.norm(dir_v)))
                theta = 0.5 * theta + 0.85 * dir_v
                f_raw = self.phi @ theta
                vals_a = [float(np.max(f_raw[sup])) for sup in ss.supports]
                a_win = int(np.argmax(vals_a))
                comp_w = ss.complements[a_win]
                raw_gap = max(1e-3, vals_a[a_win] - float(np.max(f_raw[comp_w])))
        theta *= target_margin / max(1e-4, raw_gap)
        self.theta_star = theta
        self.param_bound = float(np.linalg.norm(self.theta_star)) + 0.05
        f_vals = self.prior_mean + (self.phi @ self.theta_star)
        means = {base.graph.leaves[i]: float(f_vals[i]) for i in range(m_leaves)}
        super().__init__(name, base.graph, means, ())

    def oracle(self, seed: int) -> _GaussianOracle:
        return _GaussianOracle(len(self.graph), seed, self.means, self.sigma)


class GaussianProxyWrapper(Problem):
    """Wraps MotivationalProxyDAGProblem with exact Gaussian noise N(mu_z, sigma^2)."""

    def __init__(self, sigma: float = 0.10) -> None:
        base = MotivationalProxyDAGProblem(hw=0.18)
        self.prior_mean = base.prior_mean
        self.phi = base.phi.copy()
        self.theta_star = base.theta_star.copy()
        self.param_bound = base.param_bound
        self.sigma = float(sigma)
        self.obs_std = float(sigma)
        super().__init__("proxy_m5_d3_gauss", base.graph, dict(base.means), ())

    def oracle(self, seed: int) -> _GaussianOracle:
        return _GaussianOracle(len(self.graph), seed, self.means, self.sigma)


class IndependentGaussianOSSession:
    """Distribution-free independent-coordinate anytime Gaussian Optimistic-Separation baseline.

    Uses exact anytime sub-Gaussian confidence intervals:
        [hat_mu_z - rad_z, hat_mu_z + rad_z],  rad_z = sigma * sqrt(2 * log(2 * M * n_z * (n_z + 1) / delta) / n_z)
    which satisfies Pr(forall t, forall z: |hat_mu_z - mu_z| <= rad_z) >= 1 - delta via union bound.
    """

    def __init__(self, problem: Problem, seed: int, epsilon: float, sigma: float, delta: float = 0.05) -> None:
        self.problem = problem
        self.ss = SupportStructure(problem.graph)
        self.oracle = problem.oracle(seed)
        self.epsilon = float(epsilon)
        self.sigma = float(sigma)
        self.delta = float(delta)
        self.m = len(self.ss.leaves)
        self.k = len(self.ss.supports)
        self.counts = np.zeros(self.m, dtype=np.int64)
        self.sums = np.zeros(self.m, dtype=np.float64)
        self.lo = np.full(self.m, -1e9, dtype=np.float64)
        self.hi = np.full(self.m, 1e9, dtype=np.float64)
        self.calls = 0
        self.certified = False
        self.action = 0
        self.current_regret = math.inf
        self._init_idx = 0

    def _update_bounds(self, idx: int) -> None:
        n = int(self.counts[idx])
        mu = float(self.sums[idx]) / n
        # Anytime union bound over n >= 1 (sum 1/(n(n+1)) = 1) and m leaves
        rad = self.sigma * math.sqrt(2.0 * math.log(2.0 * self.m * n * (n + 1) / self.delta) / n)
        self.lo[idx] = mu - rad
        self.hi[idx] = mu + rad

    def _eval_and_pick(self) -> int:
        best_reg = math.inf
        best_a = 0
        best_p = 0
        best_q = -1
        for a in range(self.k):
            sup = self.ss.supports[a]
            comp = self.ss.complements[a]
            p_loc = int(np.argmax(self.lo[sup]))
            p_idx = int(sup[p_loc])
            if len(comp) == 0:
                reg = 0.0
                q_idx = -1
            else:
                q_loc = int(np.argmax(self.hi[comp]))
                q_idx = int(comp[q_loc])
                reg = max(0.0, float(self.hi[q_idx] - self.lo[p_idx]))
            if reg < best_reg:
                best_reg = reg
                best_a = a
                best_p = p_idx
                best_q = q_idx
        self.action = best_a
        self.current_regret = best_reg
        if best_reg <= self.epsilon:
            self.certified = True
            return best_p
        # Optimistic-Separation: pick action maximizing max_{y in S(a)} hi[y] - max_{z notin S(a)} lo[z]
        best_sep = -math.inf
        os_p, os_q = best_p, best_q
        for a in range(self.k):
            sup = self.ss.supports[a]
            comp = self.ss.complements[a]
            if len(comp) == 0:
                continue
            y_hi = int(sup[int(np.argmax(self.hi[sup]))])
            z_lo = int(comp[int(np.argmax(self.lo[comp]))])
            sep = float(self.hi[y_hi] - self.lo[z_lo])
            if sep > best_sep:
                best_sep = sep
                os_p = int(sup[int(np.argmax(self.lo[sup]))])
                os_q = int(comp[int(np.argmax(self.hi[comp]))])
        if os_q < 0:
            return os_p
        wp = float(self.hi[os_p] - self.lo[os_p])
        wq = float(self.hi[os_q] - self.lo[os_q])
        return os_p if wp >= wq else os_q

    def step(self) -> bool:
        if self.certified:
            return False
        if self._init_idx < self.m:
            idx = self._init_idx
            self._init_idx += 1
        else:
            idx = self._eval_and_pick()
            if self.certified:
                return False
        y = float(self.oracle.sample(self.ss.leaves[idx]))
        self.calls += 1
        self.counts[idx] += 1
        self.sums[idx] += y
        self._update_bounds(idx)
        if self._init_idx >= self.m:
            self._eval_and_pick()
        return True


def _build_small_instances() -> list[tuple[str, Problem, float]]:
    return [
        ("proxy_M5_d3", GaussianProxyWrapper(sigma=0.10), 0.015),
        ("gauss_M16_d4", ExactGaussianLinearDAG("gauss_M16_d4", seed=101, m_leaves=16, k_actions=4, d_feat=4, sigma=0.12, target_margin=0.09), 0.025),
        ("gauss_M32_d6", ExactGaussianLinearDAG("gauss_M32_d6", seed=102, m_leaves=32, k_actions=4, d_feat=6, sigma=0.12, target_margin=0.09), 0.025),
        ("gauss_M64_d8", ExactGaussianLinearDAG("gauss_M64_d8", seed=103, m_leaves=64, k_actions=8, d_feat=8, sigma=0.12, target_margin=0.09), 0.025),
    ]


def _run_one_method(
    prob: Problem,
    phi: np.ndarray,
    prior_mean: float,
    obs_std: float,
    param_bound: float,
    eps: float,
    delta: float,
    method: str,
    seed: int,
    cap: int,
    recompute_every: int = 12,
    outer_iters: int = 35,
    check_every: int = 4,
) -> dict:
    t0 = time.perf_counter()
    if method == "indep_gauss_os":
        sess = IndependentGaussianOSSession(prob, seed=seed, epsilon=eps, sigma=obs_std, delta=delta)
        while not sess.certified and sess.calls < cap:
            sess.step()
        elapsed_ms = 1e3 * (time.perf_counter() - t0)
        return {
            "certified": bool(sess.certified),
            "action": int(sess.action),
            "steps": int(sess.calls),
            "capped_steps": int(sess.calls) if sess.certified else cap,
            "tracker_ms": 0.0,
            "cert_ms": 0.0,
            "total_ms": round(elapsed_ms, 2),
        }

    if method in ("info_tracking", "hybrid_cd_tracking"):
        hyb = method == "hybrid_cd_tracking"
        sess = RegularizedInfoTrackerSession(
            prob,
            seed=seed,
            epsilon=eps,
            phi=phi,
            prior_mean=prior_mean,
            reg_lambda=0.01,
            obs_std=obs_std,
            param_bound=param_bound,
            delta=delta,
            recompute_every=recompute_every,
            outer_iters=outer_iters,
            check_every=check_every,
            adaptive_check=True,
            hybrid_cd_warmup=hyb,
            stop_threshold_mode="abbasi_yadkori",
        )
        while not sess.certified and not getattr(sess, "conflict", False) and sess.calls < cap:
            sess.step()
        elapsed_ms = 1e3 * (time.perf_counter() - t0)
        return {
            "certified": bool(sess.certified),
            "action": int(sess.action),
            "steps": int(sess.calls),
            "capped_steps": int(sess.calls) if sess.certified else cap,
            "tracker_ms": round(1e3 * float(sess.tracker_solve_time_s), 2),
            "cert_ms": round(1e3 * float(sess.certifier.cert_time_s), 2),
            "total_ms": round(elapsed_ms, 2),
        }

    acq = "contrast_directed" if method == "cd_joint" else "gp_ucb"
    model = LinearFeatureModel(
        phi=phi,
        prior_mean=prior_mean,
        reg_lambda=0.01,
        obs_std=obs_std,
        param_bound=param_bound,
        beta_mode="abbasi_yadkori",
        delta=delta,
    )
    sess = CorrelationAwareCertSession(
        prob,
        seed=seed,
        epsilon=eps,
        model=model,
        cert_mode="joint_ellipsoid",
        acquisition=acq,
        delta=delta,
        check_every=check_every,
        adaptive_check=True,
    )
    while not sess.certified and not sess.conflict and sess.calls < cap:
        sess.step()
    elapsed_ms = 1e3 * (time.perf_counter() - t0)
    return {
        "certified": bool(sess.certified),
        "action": int(sess.action),
        "steps": int(sess.calls),
        "capped_steps": int(sess.calls) if sess.certified else cap,
        "tracker_ms": 0.0,
        "cert_ms": round(1e3 * float(sess.ellipsoid_cert.cert_time_s), 2),
        "total_ms": round(elapsed_ms, 2),
    }


def _part_a_worker(task: tuple[str, float, list[int], int, float, int]) -> list[dict]:
    inst_name, delta, reps, cap, t_star, opt_target_a = task
    inst_map = {nm: (p, ep) for nm, p, ep in _build_small_instances()}
    prob, eps = inst_map[inst_name]
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    rows: list[dict] = []
    denom = max(1e-9, t_star * math.log(1.0 / delta))
    for rep in reps:
        seed = 820000 + rep * 37 + int(round(delta * 10000))
        for method in METHODS:
            res = _run_one_method(
                prob=prob,
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                eps=eps,
                delta=delta,
                method=method,
                seed=seed,
                cap=cap,
                recompute_every=18 if len(prob.graph.leaves) <= 32 else 24,
                outer_iters=20 if len(prob.graph.leaves) <= 32 else 18,
                check_every=3 if len(prob.graph.leaves) <= 32 else 6,
            )
            true_reg = regrets[res["action"]]
            fc = bool(res["certified"] and true_reg > eps + 1e-12)
            rows.append(
                {
                    "part": "A_small_exact_delta",
                    "instance": inst_name,
                    "m_leaves": len(prob.graph.leaves),
                    "d_feat": int(prob.phi.shape[1]),
                    "eps": eps,
                    "delta": delta,
                    "t_star": round(t_star, 4),
                    "opt_target_action": opt_target_a,
                    "rep": rep,
                    "method": method,
                    "certified": res["certified"],
                    "false_certificate": fc,
                    "action": res["action"],
                    "matched_opt_target": bool(res["action"] == opt_target_a),
                    "steps": res["steps"],
                    "capped_steps": res["capped_steps"],
                    "norm_ratio": round(res["capped_steps"] / denom, 4),
                    "final_regret": round(true_reg, 6),
                    "tracker_ms": res["tracker_ms"],
                    "cert_ms": res["cert_ms"],
                    "total_ms": res["total_ms"],
                }
            )
    return rows


def _part_b_worker(task: tuple[int, int, list[int], int]) -> list[dict]:
    m_leaves, d_feat, seeds, cap = task
    eps = 0.030
    delta = 0.05
    rows: list[dict] = []
    for s in seeds:
        prob = ExactGaussianLinearDAG(
            f"med_M{m_leaves}_d{d_feat}_s{s}",
            seed=s,
            m_leaves=m_leaves,
            k_actions=8,
            d_feat=d_feat,
            sigma=0.12,
            target_margin=0.09,
        )
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
        for method in METHODS:
            res = _run_one_method(
                prob=prob,
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                eps=eps,
                delta=delta,
                method=method,
                seed=830000 + s * 13,
                cap=cap,
                recompute_every=35 if m_leaves <= 256 else 60,
                outer_iters=12,
                check_every=10 if m_leaves <= 256 else 16,
            )
            true_reg = regrets[res["action"]]
            fc = bool(res["certified"] and true_reg > eps + 1e-12)
            rows.append(
                {
                    "part": "B_medium_overlap",
                    "instance": f"M{m_leaves}_d{d_feat}",
                    "m_leaves": m_leaves,
                    "d_feat": d_feat,
                    "eps": eps,
                    "delta": delta,
                    "rep": s,
                    "method": method,
                    "certified": res["certified"],
                    "false_certificate": fc,
                    "steps": res["steps"],
                    "capped_steps": res["capped_steps"],
                    "final_regret": round(true_reg, 6),
                    "tracker_ms": res["tracker_ms"],
                    "cert_ms": res["cert_ms"],
                    "total_ms": res["total_ms"],
                }
            )
    return rows


def _part_c_worker(task: tuple[list[int], int]) -> list[dict]:
    seeds, cap = task
    eps = 0.025
    delta = 0.05
    rows: list[dict] = []
    for s in seeds:
        prob = MultiAnswerCommitmentDAGProblem(seed=7100 + s, epsilon=eps, m_leaves=36, hw=0.16)
        ss = SupportStructure(prob.graph)
        # Compute exact characteristic rates per acceptable action to know the statistically easiest action a*
        rate_res = fast_characteristic_rate(
            phi=prob.phi, theta_star=prob.theta_star, support_struct=ss, epsilon=eps, sigma=prob.obs_std, n_outer_iters=35
        )
        easy_act = int(rate_res.target_action)
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
        top_mean_act = int(np.argmin(regrets))

        for method in METHODS:
            res = _run_one_method(
                prob=prob,
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                eps=eps,
                delta=delta,
                method=method,
                seed=840000 + s * 17,
                cap=cap,
                recompute_every=16,
                outer_iters=14,
                check_every=4,
            )
            true_reg = regrets[res["action"]]
            fc = bool(res["certified"] and true_reg > eps + 1e-12)
            rows.append(
                {
                    "part": "C_multi_answer_ties",
                    "instance": "multi_answer_M24_d5",
                    "m_leaves": len(prob.graph.leaves),
                    "d_feat": int(prob.phi.shape[1]),
                    "eps": eps,
                    "delta": delta,
                    "rep": s,
                    "method": method,
                    "easy_action": easy_act,
                    "top_mean_action": top_mean_act,
                    "certified": res["certified"],
                    "false_certificate": fc,
                    "action": res["action"],
                    "picked_easy_action": bool(res["certified"] and res["action"] == easy_act),
                    "t_star": round(float(rate_res.characteristic_time_kl1), 4),
                    "steps": res["steps"],
                    "capped_steps": res["capped_steps"],
                    "final_regret": round(true_reg, 6),
                    "tracker_ms": res["tracker_ms"],
                    "cert_ms": res["cert_ms"],
                    "total_ms": res["total_ms"],
                }
            )
    return rows


def summarize(dest: Path) -> None:
    # Part A summary
    pa = dest / "v8_exp2_partA_runs.jsonl"
    if pa.exists():
        runs = [json.loads(x) for x in pa.read_text().splitlines() if x.strip()]
        keys = sorted({(r["instance"], r["delta"], r["method"]) for r in runs})
        rows_a: list[dict] = []
        for inst, delta, meth in keys:
            sub = [r for r in runs if r["instance"] == inst and abs(r["delta"] - delta) < 1e-12 and r["method"] == meth]
            n = len(sub)
            st = np.array([float(r["capped_steps"]) for r in sub])
            nr = np.array([float(r["norm_ratio"]) for r in sub])
            rows_a.append(
                {
                    "instance": inst,
                    "delta": delta,
                    "t_star": sub[0]["t_star"],
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": sum(1 for r in sub if r["false_certificate"]),
                    "mean_steps": round(float(np.mean(st)), 1),
                    "med_steps": round(float(np.median(st)), 1),
                    "mean_norm_ratio": round(float(np.mean(nr)), 3),
                    "med_norm_ratio": round(float(np.median(nr)), 3),
                    "iqr_norm_ratio": round(float(np.percentile(nr, 75) - np.percentile(nr, 25)), 3),
                    "med_tracker_ms": round(float(np.median([r["tracker_ms"] for r in sub])), 2),
                    "med_total_ms": round(float(np.median([r["total_ms"] for r in sub])), 2),
                }
            )
        with (dest / "v8_exp2_partA_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_a[0].keys()))
            w.writeheader()
            w.writerows(rows_a)
        print("\n=== v8 Exp 2A: Asymptotic Information Efficiency E[tau]/(T_* log(1/delta)) ===")
        for r in rows_a:
            if r["delta"] in (0.10, 0.05, 0.005):
                print(
                    f"  {r['instance']:13s} d={r['delta']:5.3f} | {r['method']:18s} | "
                    f"cert={100*r['cert_rate']:5.1f}% err={r['false_certs']:2d}/{r['runs']} "
                    f"mean={r['mean_steps']:6.1f} ratio={r['mean_norm_ratio']:5.2f} "
                    f"tot={r['med_total_ms']:6.1f}ms"
                )

    # Part B summary
    pb = dest / "v8_exp2_partB_runs.jsonl"
    if pb.exists():
        runs = [json.loads(x) for x in pb.read_text().splitlines() if x.strip()]
        keys = sorted({(r["m_leaves"], r["d_feat"], r["method"]) for r in runs})
        rows_b: list[dict] = []
        for m_l, d_f, meth in keys:
            sub = [r for r in runs if r["m_leaves"] == m_l and r["d_feat"] == d_f and r["method"] == meth]
            n = len(sub)
            st = np.array([float(r["capped_steps"]) for r in sub])
            rows_b.append(
                {
                    "m_leaves": m_l,
                    "d_feat": d_f,
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": sum(1 for r in sub if r["false_certificate"]),
                    "med_steps": round(float(np.median(st)), 1),
                    "mean_steps": round(float(np.mean(st)), 1),
                    "med_tracker_ms": round(float(np.median([r["tracker_ms"] for r in sub])), 2),
                    "med_cert_ms": round(float(np.median([r["cert_ms"] for r in sub])), 2),
                    "med_total_ms": round(float(np.median([r["total_ms"] for r in sub])), 2),
                }
            )
        with (dest / "v8_exp2_partB_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_b[0].keys()))
            w.writeheader()
            w.writerows(rows_b)
        print("\n=== v8 Exp 2B: Medium Overlapping DAGs (Sample Efficiency vs Compute) ===")
        for r in rows_b:
            print(
                f"  M={r['m_leaves']:3d} d={r['d_feat']:2d} | {r['method']:18s} | "
                f"cert={100*r['cert_rate']:5.1f}% med={r['med_steps']:6.1f} "
                f"trk={r['med_tracker_ms']:6.1f}ms cert_ms={r['med_cert_ms']:6.1f}ms tot={r['med_total_ms']:7.1f}ms"
            )

    # Part C summary
    pc = dest / "v8_exp2_partC_runs.jsonl"
    if pc.exists():
        runs = [json.loads(x) for x in pc.read_text().splitlines() if x.strip()]
        rows_c: list[dict] = []
        for meth in METHODS:
            sub = [r for r in runs if r["method"] == meth]
            if not sub:
                continue
            n = len(sub)
            st = np.array([float(r["capped_steps"]) for r in sub])
            rows_c.append(
                {
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": sum(1 for r in sub if r["false_certificate"]),
                    "easy_action_rate": round(sum(1 for r in sub if r["picked_easy_action"]) / n, 4),
                    "med_steps": round(float(np.median(st)), 1),
                    "mean_steps": round(float(np.mean(st)), 1),
                    "q25_steps": round(float(np.percentile(st, 25)), 1),
                    "q75_steps": round(float(np.percentile(st, 75)), 1),
                    "med_total_ms": round(float(np.median([r["total_ms"] for r in sub])), 2),
                }
            )
        with (dest / "v8_exp2_partC_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_c[0].keys()))
            w.writeheader()
            w.writerows(rows_c)
        print("\n=== v8 Exp 2C: Multi-Answer Tied Optima (Easiest-Action Identification) ===")
        for r in rows_c:
            print(
                f"  {r['method']:18s} | cert={100*r['cert_rate']:5.1f}% easy_act={100*r['easy_action_rate']:5.1f}% "
                f"err={r['false_certs']}/{r['runs']} med={r['med_steps']:6.1f} mean={r['mean_steps']:6.1f} tot={r['med_total_ms']:6.1f}ms"
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
    small_insts = _build_small_instances()

    # Step 0: Independent CVXPY + Dirichlet verification of T_*^eps(theta) on every small instance!
    ver_rows: list[dict] = []
    t_star_map: dict[str, tuple[float, int]] = {}
    for nm, prob, eps in small_insts:
        ss = SupportStructure(prob.graph)
        ver = verify_characteristic_rate_independently(
            phi=prob.phi,
            theta_star=prob.theta_star,
            support_struct=ss,
            epsilon=eps,
            sigma=prob.obs_std,
            n_random_designs=120 if not args.smoke else 30,
            seed=2026,
        )
        ver_rows.append({"instance": nm, "m_leaves": len(prob.graph.leaves), "d_feat": int(prob.phi.shape[1]), "eps": eps, **ver})
        t_star_map[nm] = (float(ver["characteristic_time"]), int(ver["target_action"]))
        print(
            f"[Verify T_*] {nm:13s}: T_*={ver['characteristic_time']:.2f} "
            f"max_qp_diff={ver['max_qp_dual_diff']:.2e} dom_rand={ver['rate_dominates_random']:.3f}",
            flush=True,
        )
    (out_dir / "v8_exp2_tstar_verification.json").write_text(json.dumps(ver_rows, indent=2) + "\n")

    if args.smoke:
        deltas = (0.10, 0.01)
        n_a = 8
        cap_a = 2000
        med_cfgs = ((128, 8),)
        n_b = 4
        cap_b = 2500
        n_c = 8
        cap_c = 2000
    else:
        deltas = DELTAS
        n_a = 80
        cap_a = 6000
        med_cfgs = ((128, 8), (256, 16), (512, 32))
        n_b = 16
        cap_b = 6000
        n_c = 48
        cap_c = 3500

    ctx = mp.get_context("spawn")

    # Part A
    tasks_a = []
    for nm, _, _ in small_insts:
        ts, ta = t_star_map[nm]
        for d in deltas:
            for i in range(0, n_a, 10):
                tasks_a.append((nm, d, list(range(i, min(n_a, i + 10))), cap_a, ts, ta))
    print(f"[v8 Exp 2A] Launching {len(tasks_a)} tasks on {args.workers} workers...", flush=True)
    rows_a: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_part_a_worker, tasks_a):
            rows_a.extend(ch)
    (out_dir / "v8_exp2_partA_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows_a) + "\n")

    # Part B
    tasks_b = []
    for m_l, d_f in med_cfgs:
        for i in range(0, n_b, 4):
            tasks_b.append((m_l, d_f, list(range(1 + i, min(n_b, i + 4) + 1)), cap_b))
    print(f"[v8 Exp 2B] Launching {len(tasks_b)} tasks...", flush=True)
    rows_b: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_part_b_worker, tasks_b):
            rows_b.extend(ch)
    (out_dir / "v8_exp2_partB_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows_b) + "\n")

    # Part C
    tasks_c = [(list(range(i, min(n_c, i + 10))), cap_c) for i in range(0, n_c, 10)]
    print(f"[v8 Exp 2C] Launching {len(tasks_c)} tasks...", flush=True)
    rows_c: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_part_c_worker, tasks_c):
            rows_c.extend(ch)
    (out_dir / "v8_exp2_partC_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows_c) + "\n")

    summarize(out_dir)
    artifacts = [
        "v8_exp2_tstar_verification.json",
        "v8_exp2_partA_runs.jsonl",
        "v8_exp2_partA_summary.csv",
        "v8_exp2_partB_runs.jsonl",
        "v8_exp2_partB_summary.csv",
        "v8_exp2_partC_runs.jsonl",
        "v8_exp2_partC_summary.csv",
    ]
    manifest = {
        "experiment": "v8_exp2_info_tracking",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v8 Exp 2] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
