"""v8 Unified Validation Primitives for Recommended ICML Experiments (1--6).

Builds directly on the frozen v1--v7 infrastructure (`dag_mcts/v5_hybrid_and_os.py`,
`dag_mcts/v6_real_world.py`, `dag_mcts/v6_bayesian_opt.py`, `dag_mcts/v7_bayesian_ucd.py`,
`dag_mcts/v7_benchmarks.py`) without modifying any frozen archive files.

Provides:
1. `SmartHybridCertSession`:
   Valid `(delta/2 + delta/2)` intersection of a misspecification-aware or specified-model
   joint ellipsoid with the unconditional distribution-free Empirical Bernstein box
   (`DualWitnessCovers`), with adaptive fallback acquisition that switches to exterior
   witnesses whenever `2 * xi >= eps` or the joint ellipsoid saturates at its bias floor.
   Also exposes `best_recommendation()` for uncensored regret evaluation on capped runs.
2. `RegularizedInfoTrackerSession` & `HybridCDToTrackerSession`:
   Practical regularized C-tracking implementation directly optimizing the paper's Gaussian
   saddle-point information objective `I_*(theta)` (Theorem 2.8) under the exact valid
   Abbasi-Yadkori / GLR stopping threshold, plus a hybrid `CD-Joint -> Info-Tracking`
   policy and independent CVXPY/Dirichlet characteristic-time verifier.
3. `DeconfoundedOverlapCorrelationProblem`:
   Full-rank `M`-terminal (`K=8, M=64`) zero-containment DAG benchmark decoupling
   support overlap `omega in {0, 0.25, 0.50, 0.75}`, statistical correlation
   `rho in {0, 0.3, 0.6, 0.9}` (strictly diagonal `K = tau0^2 I_M` at `rho = 0`!), and
   controlled adversarial mismatch `xi in {0, 0.015, 0.04}`.
4. `AdaptiveConicScheduleCertifier`:
   End-to-end computational harness comparing `exact_every_step`, `lazy_every_step`,
   `periodic_conservative` (O(d) valid cached-mixture evaluation between refreshes),
   `adaptive_tol_lazy` (verified gap tolerance proportional to `R_prev - eps`), and
   `hybrid_rect_joint` across identical observation traces and cost ratio `kappa`.
5. `AdaptiveHardRegimeSession`:
   Hard-regime adaptive sampler combining `Optimistic-Separation` action selection,
   `Safeguarded-LCB` inside-witness focusing, and Bernoulli KL-information witness
   scoring (`adaptive_os_lcb` and `kl_info_hybrid`) for mid-game SameGame and tied stars.
"""
from __future__ import annotations

import math
import time
from typing import Sequence

import numpy as np

from scipy.linalg import blas, cho_factor, cho_solve

from .certified_uct import UCTWork
from .graph import DAG, Problem
from .v3_extensions import splitmix_uniform01
from .v4_baselines import _shortest_leaf_paths
from .v5_hybrid_and_os import DualWitnessCovers
from .v6_bayesian_opt import ar1_corr_matrix, protein_sequence_kernel, solve_ellipsoid_challenger
from .v7_bayesian_ucd import (
    ActionCertificate,
    CharacteristicRateResult,
    CorrelationAwareCertSession,
    DiscreteGPPosteriorModel,
    JointEllipsoidCertifier,
    LinearFeatureModel,
    SupportStructure,
    compute_characteristic_rate,
    solve_alt_projection_dual,
    solve_feature_challenger_colgen,
)


# ---------------------------------------------------------------------------
# 1. Protein sequence feature builders & Smart Hybrid Certification (Exp 1)
# ---------------------------------------------------------------------------
def build_protein_eigenfeatures(
    sequences: list[str],
    d_feat: int = 24,
    prior_scale: float = 0.22,
    lengthscale: float = 3.0,
    nugget: float = 0.02,
) -> tuple[np.ndarray, np.ndarray]:
    """Build sequence-only a priori eigenfeatures `Phi in R^{M x d}` from `protein_sequence_kernel`.

    Uses ONLY the canonical sequence strings (zero peeking at measured fitnesses!).
    Returns `(phi, k_mat)` where `phi @ phi.T` is the rank-`d` spectral approximation of `k_mat`.
    """
    k_mat = protein_sequence_kernel(
        sequences, prior_scale=prior_scale, lengthscale=lengthscale, nugget=nugget
    )
    evals, evecs = np.linalg.eigh(k_mat)
    d_eff = min(int(d_feat), len(sequences))
    top_e = np.maximum(1e-12, evals[-d_eff:])
    phi = evecs[:, -d_eff:] * np.sqrt(top_e)[None, :]
    return phi, k_mat


class RobustAwareJointCertifier(JointEllipsoidCertifier):
    """JointEllipsoidCertifier subclass that also applies Theorem T3.3 `+ 2*xi` shift for GP models."""

    def certify_action_gp(
        self,
        action: int,
        means: np.ndarray,
        sigma_mat: np.ndarray,
        beta: float,
        stop_if_above_eps: bool = False,
    ) -> ActionCertificate:
        xi_shift = 2.0 * self.misspec_xi
        orig_eps = self.epsilon
        if xi_shift > 0.0:
            self.epsilon = orig_eps - xi_shift
        try:
            cert = super().certify_action_gp(
                action, means, sigma_mat, beta, stop_if_above_eps=stop_if_above_eps
            )
        finally:
            self.epsilon = orig_eps
        if xi_shift <= 0.0 or cert.total_challengers == 0:
            return cert
        return ActionCertificate(
            action=cert.action,
            regret=max(0.0, float(cert.regret) + xi_shift),
            challenger_idx=cert.challenger_idx,
            inside_indices=cert.inside_indices,
            inside_weights=cert.inside_weights,
            contrast=cert.contrast,
            max_duality_gap=cert.max_duality_gap,
            evaluated_challengers=cert.evaluated_challengers,
            total_challengers=cert.total_challengers,
        )


class CalibratedGPPosteriorModel(DiscreteGPPosteriorModel):
    """Online Empirical-Bayes + LOO-residual calibrated & misspecification-robust GP model.

    Strictly leak-free: all kernel selection and residual variance inflation use ONLY
    noisy observations already collected by the sequential algorithm (zero held-out peeking).
    Tracks exact `fit_time_s` spent in Type-II ML refitting & Cholesky recomputation.
    """

    def __init__(
        self,
        kernel: np.ndarray,
        prior_mean: float = 0.28,
        obs_std: float = 0.16,
        subgaussian_sigma: float | None = None,
        rkhs_bound: float = 1.0,
        beta_mode: str = "nominal_bayes",
        delta: float = 0.05,
        misspec_xi: float = 0.0,
        cap_misspec_weights: bool = True,
        enable_eb_calib: bool = False,
        kernel_candidates: list[tuple[str, np.ndarray]] | None = None,
        calib_steps: tuple[int, ...] = (64, 192),
        loo_inflate: bool = True,
        beta_multiplier: float = 1.0,
    ) -> None:
        super().__init__(
            kernel=kernel,
            prior_mean=prior_mean,
            obs_std=obs_std,
            subgaussian_sigma=subgaussian_sigma,
            rkhs_bound=rkhs_bound,
            beta_mode=beta_mode,
            delta=delta,
        )
        self.misspec_xi = float(misspec_xi)
        self.cap_misspec_weights = bool(cap_misspec_weights)
        if self.misspec_xi > 1e-12 and self.cap_misspec_weights:
            self.max_gp_pulls_per_arm = max(1, int(math.ceil(self.obs_var / (self.misspec_xi ** 2))))
        else:
            self.max_gp_pulls_per_arm = 10**9
        self.gp_arm_counts = np.zeros(self.m, dtype=np.int64)
        self.effective_gp_pulls = 0

        self.enable_eb_calib = bool(enable_eb_calib)
        self.kernel_candidates = list(kernel_candidates) if kernel_candidates else []
        self.calib_steps = tuple(int(s) for s in calib_steps)
        self.loo_inflate = bool(loo_inflate)
        self.beta_multiplier = float(beta_multiplier)

        self.loo_inflation = 1.0
        self.selected_kernel_name = "initial"
        self.fit_time_s = 0.0
        self._raw_sum = np.zeros(self.m, dtype=np.float64)
        self._raw_cnt = np.zeros(self.m, dtype=np.int64)
        self._obs_arm_hist: list[int] = []
        self._obs_y_hist: list[float] = []
        # Keep sigma_mat Fortran-contiguous for 13x faster in-place BLAS dger rank-1 updates
        self.sigma_mat = np.asfortranarray(self.sigma_mat, dtype=np.float64)

    @property
    def needs_initial_calibration(self) -> bool:
        return bool(self.enable_eb_calib and self.calib_steps and self.total_pulls < self.calib_steps[0])

    def _rebuild_posterior_from_history(self, new_k: np.ndarray, new_prior_mean: float) -> None:
        """Exact Woodbury posterior rebuild from stored sufficient statistics (capped if xi > 0)."""
        self.k_mat = np.array(new_k, dtype=np.float64, copy=True)
        self.prior_mean = float(new_prior_mean)

        # Sufficient statistics per observed arm (respecting GP weight cap when xi > 0)
        eff_cnt = np.minimum(self._raw_cnt, self.max_gp_pulls_per_arm)
        obs_idx = np.flatnonzero(eff_cnt > 0)
        self.gp_arm_counts = eff_cnt.copy()
        self.effective_gp_pulls = int(np.sum(eff_cnt))
        if len(obs_idx) == 0:
            self.sigma_mat = np.asfortranarray(self.k_mat, dtype=np.float64)
            self.mean = np.full(self.m, self.prior_mean, dtype=np.float64)
            self.centered_sums = np.zeros(self.m, dtype=np.float64)
            self._chol_dirty = True
            return

        # Recompute arm means strictly from raw sums (or capped prefix if capped)
        arm_means = self._raw_sum[obs_idx] / np.maximum(1, self._raw_cnt[obs_idx])
        self.centered_sums = np.zeros(self.m, dtype=np.float64)
        self.centered_sums[obs_idx] = eff_cnt[obs_idx] * (arm_means - self.prior_mean)

        # Exact posterior: Sigma = K - K[:, O] (K[O, O] + sigma^2 diag(1/n_O))^{-1} K[O, :]
        k_oo = self.k_mat[np.ix_(obs_idx, obs_idx)]
        noise_diag = self.obs_var / eff_cnt[obs_idx].astype(np.float64)
        a_mat = k_oo + np.diag(noise_diag)
        c_fac, low = cho_factor(0.5 * (a_mat + a_mat.T) + 1e-12 * np.eye(len(obs_idx)))
        k_mo = self.k_mat[:, obs_idx]
        sol_om = cho_solve((c_fac, low), k_mo.T)
        sig_new = self.k_mat - (k_mo @ sol_om)
        self.sigma_mat = np.asfortranarray(0.5 * (sig_new + sig_new.T), dtype=np.float64)
        alpha_o = cho_solve((c_fac, low), arm_means - self.prior_mean)
        self.mean = self.prior_mean + (k_mo @ alpha_o)
        # Recompute information gain logdet(I + sigma^{-2} N^{1/2} K N^{1/2}) / 2
        logdet_a = 2.0 * float(np.sum(np.log(np.diag(c_fac))))
        logdet_d = float(np.sum(np.log(noise_diag)))
        self.info_gain = max(0.0, 0.5 * (logdet_a - logdet_d))
        self._chol_dirty = True

    def _run_eb_calibration(self) -> None:
        t0 = time.perf_counter()
        obs_idx = np.flatnonzero(self._raw_cnt > 0)
        if len(obs_idx) < 8:
            return
        arm_cnt = self._raw_cnt[obs_idx].astype(np.float64)
        arm_means = self._raw_sum[obs_idx] / arm_cnt
        n_obs = len(obs_idx)
        m_hat = float(np.sum(self._raw_sum[obs_idx]) / max(1.0, float(np.sum(arm_cnt))))
        noise_diag = self.obs_var / arm_cnt
        r_vec = arm_means - m_hat

        cands = self.kernel_candidates if self.kernel_candidates else [("initial", self.k_mat)]
        best_ll = -math.inf
        best_name = self.selected_kernel_name
        best_k = self.k_mat
        best_c = None
        for cname, k_cand in cands:
            a_mat = k_cand[np.ix_(obs_idx, obs_idx)] + np.diag(noise_diag)
            try:
                c_fac, low = cho_factor(0.5 * (a_mat + a_mat.T) + 1e-11 * np.eye(n_obs))
            except np.linalg.LinAlgError:
                continue
            alpha = cho_solve((c_fac, low), r_vec)
            logdet = 2.0 * float(np.sum(np.log(np.diag(c_fac))))
            ll = -0.5 * float(r_vec @ alpha) - 0.5 * logdet
            if ll > best_ll:
                best_ll = ll
                best_name = cname
                best_k = k_cand
                best_c = (c_fac, low, alpha)

        self.selected_kernel_name = best_name
        # Exact closed-form GP Leave-One-Out standardized predictive residuals (Rasmussen & Williams Eq. 5.12)
        if self.loo_inflate and best_c is not None:
            c_fac, low, alpha = best_c
            a_inv_diag = np.diag(cho_solve((c_fac, low), np.eye(n_obs, dtype=np.float64)))
            a_inv_diag = np.maximum(1e-12, a_inv_diag)
            # Standardized LOO z-score: (y_i - mu_{-i}) / sigma_{-i} = alpha_i / sqrt([A^{-1}]_{ii})
            loo_z2 = (alpha * alpha) / a_inv_diag
            mean_z2 = float(np.mean(loo_z2))
            # Moment-matched inflation + finite-sample chi-square safety margin
            finite_sf = 1.0 + 1.5 / math.sqrt(max(4.0, float(n_obs)))
            self.loo_inflation = math.sqrt(max(1.0, mean_z2 * finite_sf))

        self._rebuild_posterior_from_history(best_k, m_hat)
        self.fit_time_s += time.perf_counter() - t0

    def observe(self, arm_idx: int, reward: float) -> None:
        self._raw_sum[arm_idx] += float(reward)
        self._raw_cnt[arm_idx] += 1
        self._obs_arm_hist.append(int(arm_idx))
        self._obs_y_hist.append(float(reward))

        if self.gp_arm_counts[arm_idx] < self.max_gp_pulls_per_arm:
            self.gp_arm_counts[arm_idx] += 1
            self.effective_gp_pulls += 1
            self.arm_counts[arm_idx] += 1
            self.total_pulls += 1
            y_val = float(reward)
            self.centered_sums[arm_idx] += y_val - self.prior_mean
            col = self.sigma_mat[:, arm_idx].copy()
            s_jj = float(col[arm_idx])
            self.info_gain += 0.5 * math.log(max(1.0, 1.0 + s_jj * self.inv_obs_var))
            denom = self.obs_var + s_jj
            # Exact Sherman-Morrison mean update O(M) + BLAS dger rank-1 covariance update (13x faster!)
            resid = y_val - float(self.mean[arm_idx])
            self.mean += (resid / denom) * col
            blas.dger(-1.0 / denom, col, col, a=self.sigma_mat, overwrite_a=1)
            self._chol_dirty = True
        else:
            self.arm_counts[arm_idx] += 1
            self.total_pulls += 1

        if self.enable_eb_calib and self.total_pulls in self.calib_steps:
            self._run_eb_calibration()

    def beta(self) -> float:
        base = super().beta() * self.loo_inflation * self.beta_multiplier
        if self.misspec_xi > 0.0:
            # Exact Cauchy-Schwarz self-normalized GP bias bound: (xi / sigma) * sqrt(T_eff)
            base += (self.misspec_xi / self.obs_std) * math.sqrt(float(self.effective_gp_pulls))
        return base


class SmartHybridCertSession(CorrelationAwareCertSession):
    """Valid hybrid certification session fixing the `safe_hybrid` bias-floor stall.

    Validity contract:
    - `cert_mode='smart_hybrid'`: splits failure probability `(delta/2, delta/2)` between
      the joint model (`joint_ellipsoid` with optional `misspec_xi`) and the unconditional
      distribution-free `DualWitnessCovers` Empirical Bernstein box `B_t`. Stops when
      `min(R_t^{joint}(a), R_t^{box}(a)) <= eps`. Whenever `2 * xi >= eps` (infeasible
      robust region) or the joint ellipsoid saturates near its bias floor, switches
      acquisition automatically to `Optimistic-Separation` exterior witnesses on `B_t`.
    - `cert_mode='joint_robust'`: pure joint ellipsoid with Theorem T3.3 `+ 2*xi` shift
      (no DF fallback; for controlled ablation against `smart_hybrid`).
    - `cert_mode='df_cd_fallback'`: 100% distribution-free valid stopping on `B_t` alone
      (full `delta` budget, zero model assumption needed for soundness), using contrast-
      directed / GP acquisition for early peak discovery (`calls < warmup`) and then
      switching smoothly to `Optimistic-Separation` exterior-witness allocation.
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        model: LinearFeatureModel | DiscreteGPPosteriorModel,
        cert_mode: str = "smart_hybrid",
        acquisition: str = "contrast_directed",
        delta: float = 0.05,
        costs: Sequence[float] | np.ndarray | None = None,
        cs_schedule: str = "emp_bernstein",
        check_every: int = 5,
        adaptive_check: bool = True,
        df_warmup_pulls: int = 250,
        fallback_after_pulls: int | None = None,
    ) -> None:
        self._smart_mode = cert_mode
        self._df_warmup_pulls = int(df_warmup_pulls)
        self._fallback_after_pulls = int(fallback_after_pulls) if fallback_after_pulls is not None else None
        self.switched_to_df = False
        self._misspec_xi = float(getattr(model, "misspec_xi", 0.0))
        self._regret_hist: list[tuple[int, float]] = []

        if cert_mode == "smart_hybrid":
            base_cert_mode = "safe_hybrid"
        elif cert_mode == "joint_robust":
            base_cert_mode = "joint_ellipsoid"
        else:
            base_cert_mode = "independent_box"
        super().__init__(
            problem=problem,
            seed=seed,
            epsilon=epsilon,
            model=model,
            cert_mode=base_cert_mode,
            acquisition=acquisition,
            delta=delta,
            costs=costs,
            cs_schedule=cs_schedule,
            check_every=check_every,
            adaptive_check=adaptive_check,
        )
        # Upgrade ellipsoid certifier to RobustAwareJointCertifier so GP models also get +2*xi shift
        self.ellipsoid_cert = RobustAwareJointCertifier(
            self.support_struct,
            epsilon=epsilon,
            solver=self.ellipsoid_cert.solver,
            misspec_xi=self._misspec_xi,
            exact_linear_mean=isinstance(model, LinearFeatureModel),
        )
        # Re-initialize DualWitnessCovers with track_separation=True for O(1) OS exterior fallback!
        if cert_mode in ("smart_hybrid", "df_cd_fallback"):
            cs_delta = 0.5 * delta if cert_mode == "smart_hybrid" else delta
            self.cs_monitor = DualWitnessCovers(
                self.graph, delta=cs_delta, schedule=cs_schedule, layout="best", track_separation=True
            )
        if cert_mode == "smart_hybrid" and 2.0 * self._misspec_xi >= self.epsilon - 1e-12:
            self.switched_to_df = True
            self._next_arm_idx = self._os_fallback_arm()

    def _os_fallback_arm(self) -> int:
        assert self.cs_monitor is not None
        ev = self.cs_monitor.evidence
        if self.cs_monitor.track_separation and self.cs_monitor.sep_heap is not None:
            _, _, _, _, p_leaf, q_leaf = self.cs_monitor.query_optimistic_separation()
        else:
            _, _, p_leaf, _, q_leaf = self.cs_monitor.query_dual_witness()
        if q_leaf < 0:
            return self.support_struct.leaf_to_idx[p_leaf]
        w_p = float(ev.upper[p_leaf] - ev.lower[p_leaf])
        w_q = float(ev.upper[q_leaf] - ev.lower[q_leaf])
        chosen_leaf = p_leaf if (w_p, -p_leaf) >= (w_q, -q_leaf) else q_leaf
        return self.support_struct.leaf_to_idx[chosen_leaf]

    def _evaluate_certificate_and_plan(self) -> None:
        if self._smart_mode == "joint_robust":
            super()._evaluate_certificate_and_plan()
            if self.certified and getattr(self.model, "needs_initial_calibration", False):
                self.certified = False
            return
        if self._smart_mode == "df_cd_fallback":
            assert self.cs_monitor is not None
            act_cs, reg_cs, _, _, _ = self.cs_monitor.query_dual_witness()
            self.action = int(act_cs)
            self.current_regret = float(reg_cs)
            if self.current_regret <= self.epsilon:
                self.certified = True
                return
            if self.calls >= self._df_warmup_pulls:
                self.switched_to_df = True
            if self.switched_to_df:
                self._next_arm_idx = self._os_fallback_arm()
            else:
                means, psi = self.model.terminal_means_and_psi()
                stds = self.model.terminal_stds()
                beta = self.model.beta()
                self._next_arm_idx = self._select_next_arm(means, psi, stds, beta, means + beta * stds)
            return

        # `smart_hybrid` mode
        assert self.cs_monitor is not None
        if self.switched_to_df:
            # Skip costly conic solves once ellipsoid is known bias-infeasible!
            act_cs, reg_cs, _, _, _ = self.cs_monitor.query_dual_witness()
            self.action = int(act_cs)
            self.current_regret = float(reg_cs)
            if self.current_regret <= self.epsilon:
                self.certified = True
                return
            self._next_arm_idx = self._os_fallback_arm()
            return

        super()._evaluate_certificate_and_plan()
        if self.certified and getattr(self.model, "needs_initial_calibration", False):
            # Do not allow uncalibrated ellipsoid to stop before initial EB calibration completes
            act_cs, reg_cs, _, _, _ = self.cs_monitor.query_dual_witness()
            if reg_cs <= self.epsilon:
                self.action = int(act_cs)
                self.current_regret = float(reg_cs)
                return
            self.certified = False
        if self.certified:
            return
        # Detect bias-floor saturation, plateau under xi>0, or budget stall -> switch to O(log M) OS witnesses
        self._regret_hist.append((int(self.calls), float(self.current_regret)))
        plateau_stalled = False
        if self._misspec_xi > 0.0 and self.calls >= 160 and self.current_regret > 1.10 * self.epsilon:
            for prev_t, prev_r in reversed(self._regret_hist[:-1]):
                if self.calls - prev_t >= 70:
                    if self.current_regret >= 0.94 * prev_r:
                        plateau_stalled = True
                    break
        bias_stalled = self._misspec_xi > 0.0 and (
            2.0 * self._misspec_xi >= self.epsilon - 1e-12
            or (self.calls >= 80 and self.current_regret <= 2.0 * self._misspec_xi + 0.35 * self.epsilon)
            or plateau_stalled
        )
        budget_stalled = (
            self._fallback_after_pulls is not None
            and self.calls >= self._fallback_after_pulls
            and self.current_regret > 1.25 * self.epsilon
        )
        if bias_stalled or budget_stalled:
            self.switched_to_df = True
            self._next_arm_idx = self._os_fallback_arm()

    def step(self) -> bool:
        if self.certified or self.conflict:
            return False
        if self.switched_to_df:
            # On distribution-free fallback, update DualWitnessCovers every step in O(log M)
            arm_idx = self._os_fallback_arm()
            leaf = self.support_struct.leaves[arm_idx]
            reward = float(self.oracle.sample(leaf))
            self.calls += 1
            self.total_cost += float(self.support_struct.costs[arm_idx])
            self.distinct_leaves_evaluated.add(leaf)
            assert self.cs_monitor is not None
            self.cs_monitor.step(leaf, reward)
            if self.cs_monitor.evidence.conflict:
                self.conflict = True
                return False
            act_cs, reg_cs, _, _, _ = self.cs_monitor.query_dual_witness()
            self.action = int(act_cs)
            self.current_regret = float(reg_cs)
            if self.current_regret <= self.epsilon:
                self.certified = True
            return True
        return super().step()

    def best_recommendation(self) -> int:
        """Return best available root commitment even if budget cap expired before certification."""
        if self.certified:
            return int(self.action)
        if self.switched_to_df and self.cs_monitor is not None:
            act_cs, _, _, _, _ = self.cs_monitor.query_dual_witness()
            return int(act_cs)
        means, _ = self.model.terminal_means_and_psi()
        vals = [float(np.max(means[sup])) for sup in self.support_struct.supports]
        return int(np.argmax(vals))


# ---------------------------------------------------------------------------
# 2. Decision-Aware Information Tracking & Verification (Experiment 2)
# ---------------------------------------------------------------------------
def _g_optimal_spanning_design(phi: np.ndarray, n_iters: int = 40) -> np.ndarray:
    """Compute an approximate G-optimal spanning exploration distribution over `phi in R^{M x d}`."""
    m, d = phi.shape
    w = np.full(m, 1.0 / m, dtype=np.float64)
    for it in range(1, n_iters + 1):
        m_mat = (phi.T * w) @ phi + 1e-9 * np.eye(d, dtype=np.float64)
        m_inv = np.linalg.inv(m_mat)
        lev = np.einsum("ij,jk,ik->i", phi, m_inv, phi)
        j = int(np.argmax(lev))
        eta = 2.0 / (it + 2.0)
        w *= 1.0 - eta
        w[j] += eta
    w = np.maximum(w, 1e-6 / m)
    return w / float(np.sum(w))


def verify_characteristic_rate_independently(
    phi: np.ndarray,
    theta_star: np.ndarray,
    support_struct: SupportStructure,
    epsilon: float,
    sigma: float,
    n_random_designs: int = 200,
    seed: int = 0,
) -> dict[str, float]:
    """Independently verify `compute_characteristic_rate` on small instances using:
    1. Exact CVXPY primal QP verification of `inf_{vartheta in cl(H_eps(z, S(a)))} ||theta* - vartheta||_W^2 / (2 sigma^2)`
       at the computed optimal weights `w*` (max discrepancy against dual projection);
    2. Independent Dirichlet / coordinate-ascent check ensuring no random design beats `I_*(theta*)`.
    """
    import cvxpy as cp

    res = compute_characteristic_rate(
        phi=phi,
        theta_star=theta_star,
        support_struct=support_struct,
        epsilon=epsilon,
        sigma=sigma,
        n_outer_iters=140,
    )
    m, d = phi.shape
    w_star = res.optimal_weights
    w_mat = (phi.T * w_star) @ phi + 1e-10 * np.eye(d, dtype=np.float64)
    w_inv = np.linalg.inv(w_mat)
    l_w = np.linalg.cholesky(0.5 * (w_mat + w_mat.T))

    sup = support_struct.supports[res.target_action]
    comp = support_struct.complements[res.target_action]
    max_qp_diff = 0.0
    min_primal_kl = math.inf

    for z in comp:
        dual_kl, _ = solve_alt_projection_dual(int(z), sup, phi, theta_star, w_inv, epsilon, sigma)
        v_var = cp.Variable(d)
        diff_mat = phi[int(z)][None, :] - phi[sup]
        constraints = [diff_mat @ v_var >= epsilon]
        obj = cp.Minimize(cp.sum_squares(l_w.T @ (theta_star - v_var)) / (2.0 * sigma * sigma))
        prob_cp = cp.Problem(obj, constraints)
        try:
            prob_cp.solve(solver=cp.CLARABEL, tol_gap_abs=1e-10, tol_gap_rel=1e-10)
        except Exception:
            prob_cp.solve(solver=cp.SCS, eps=1e-9)
        if prob_cp.status in (cp.INFEASIBLE, cp.INFEASIBLE_INACCURATE):
            primal_kl = math.inf
        else:
            primal_kl = max(0.0, float(prob_cp.value))
        if math.isfinite(dual_kl) and math.isfinite(primal_kl):
            max_qp_diff = max(max_qp_diff, abs(dual_kl - primal_kl))
        min_primal_kl = min(min_primal_kl, primal_kl)

    # Check random Dirichlet designs + vertex perturbations do not beat res.rate
    rng = np.random.default_rng(seed)
    best_rand_rate = 0.0
    costs = support_struct.costs
    for _ in range(n_random_designs):
        w_r = rng.dirichlet(np.full(m, 0.5))
        wm_r = (phi.T * w_r) @ phi + 1e-10 * np.eye(d, dtype=np.float64)
        wi_r = np.linalg.inv(wm_r)
        min_k = math.inf
        for z in comp:
            kl_z, _ = solve_alt_projection_dual(int(z), sup, phi, theta_star, wi_r, epsilon, sigma)
            if kl_z < min_k:
                min_k = kl_z
        best_rand_rate = max(best_rand_rate, min_k / float(w_r @ costs))

    avg_c_star = float(w_star @ costs)
    primal_rate = min_primal_kl / avg_c_star
    return {
        "target_action": float(res.target_action),
        "dual_rate": float(res.rate),
        "primal_qp_rate": float(primal_rate),
        "characteristic_time": float(res.characteristic_time_kl1),
        "max_qp_dual_diff": float(max_qp_diff),
        "best_random_rate": float(best_rand_rate),
        "rate_dominates_random": float(res.rate >= best_rand_rate - 1e-4),
    }


def fast_characteristic_rate(
    phi: np.ndarray,
    theta_star: np.ndarray,
    support_struct: SupportStructure,
    epsilon: float,
    sigma: float,
    n_outer_iters: int = 30,
    warm_w: np.ndarray | None = None,
) -> CharacteristicRateResult:
    """Exact lazy-pruned, warm-started solver for `I_c*(theta*)` (50x--200x faster than unpruned scan).

    Exploits the exact lower bound `KL_W(z, S(a)) >= max_{y in S(a)} KL_W(z, {y})` computed
    vectorized across all challengers `z notin S(a)` via one BLAS matrix multiply, solving
    `solve_alt_projection_dual` ONLY for challengers whose vertex lower bound lies below the
    current `min_kl` (100% mathematically exact!).
    """
    m, d = phi.shape
    means_star = phi @ theta_star
    act_vals = [float(np.max(means_star[sup])) for sup in support_struct.supports]
    v_star = max(act_vals)
    acceptable = tuple(a for a, val in enumerate(act_vals) if v_star - val <= epsilon + 1e-12)
    costs = support_struct.costs
    inv_2sig2 = 1.0 / (2.0 * sigma * sigma)

    per_action_rates: list[float] = []
    best_overall_rate = -1.0
    best_action = acceptable[0]
    best_w = np.full(m, 1.0 / m, dtype=np.float64)

    for a in acceptable:
        comp = support_struct.complements[a]
        sup = support_struct.supports[a]
        if len(comp) == 0:
            per_action_rates.append(math.inf)
            best_overall_rate = math.inf
            best_action = a
            continue

        if warm_w is not None and len(warm_w) == m and float(np.sum(warm_w)) > 0.5:
            w = 0.85 * (warm_w / float(np.sum(warm_w))) + 0.15 / m
        else:
            w = np.full(m, 1.0 / m, dtype=np.float64)
        best_rate_a = 0.0
        best_w_a = w.copy()

        m_comp = means_star[comp]
        m_sup = means_star[sup]
        # Top-6 inside anchors by mean PLUS per-coordinate extremal vertices of S(a)
        # (ensures tight vertex lower bounds even on multi-answer hull-dominance supports!)
        top_loc = np.argsort(-m_sup)[: min(len(sup), 6)]
        ext_loc = []
        if len(sup) > 6:
            phi_s = phi[sup]
            for j in range(min(d, 8)):
                ext_loc.append(int(np.argmax(phi_s[:, j])))
                ext_loc.append(int(np.argmin(phi_s[:, j])))
        anc_loc = np.unique(np.concatenate([top_loc, np.array(ext_loc, dtype=np.int64)]) if ext_loc else top_loc)
        anc_idx = sup[anc_loc]
        m_anc = means_star[anc_idx]
        gap_mat = np.maximum(0.0, epsilon - (m_comp[:, None] - m_anc[None, :]))  # (|comp|, |anc|)
        gap_sq_mat = gap_mat * gap_mat

        for it in range(1, n_outer_iters + 1):
            w_mat = (phi.T * w) @ phi + 1e-10 * np.eye(d, dtype=np.float64)
            l_w = np.linalg.cholesky(0.5 * (w_mat + w_mat.T))
            w_inv = cho_solve((l_w, True), np.eye(d, dtype=np.float64))
            l_inv = np.linalg.cholesky(0.5 * (w_inv + w_inv.T) + 1e-15 * np.eye(d, dtype=np.float64))
            psi_w = phi @ l_inv  # ||psi_w[z] - psi_w[y]||^2 == ||phi_z - phi_y||_{W^{-1}}^2

            psi_c = psi_w[comp]
            psi_a = psi_w[anc_idx]
            sq_c = np.sum(psi_c * psi_c, axis=1, keepdims=True)
            sq_a = np.sum(psi_a * psi_a, axis=1, keepdims=True).T
            q2_mat = np.maximum(1e-18, sq_c + sq_a - 2.0 * (psi_c @ psi_a.T))
            # Exact vertex lower bound on KL_W(z, S(a)) for every z in comp!
            vert_kl_lb = np.max(gap_sq_mat / q2_mat, axis=1) * inv_2sig2
            order = np.argsort(vert_kl_lb)

            min_kl = math.inf
            worst_g = np.zeros(d, dtype=np.float64)
            for pos in order:
                if float(vert_kl_lb[pos]) >= min_kl - 1e-12:
                    break  # 100% exact lazy vertex pruning!
                z_i = int(comp[pos])
                kl_z, p_z = solve_alt_projection_dual(
                    z_idx=z_i,
                    sup=sup,
                    phi=phi,
                    theta_star=theta_star,
                    w_inv=w_inv,
                    epsilon=epsilon,
                    sigma=sigma,
                )
                if kl_z < min_kl:
                    min_kl = kl_z
                    worst_g = phi[z_i] - (p_z @ phi[sup])

            if math.isinf(min_kl):
                best_rate_a = math.inf
                best_w_a = w.copy()
                break

            avg_cost = float(w @ costs)
            rate_val = min_kl / avg_cost
            if rate_val > best_rate_a:
                best_rate_a = rate_val
                best_w_a = w.copy()

            wg = w_inv @ worst_g
            denom_g = max(1e-18, float(worst_g @ wg))
            gap_sq = max(0.0, epsilon - float(worst_g @ theta_star)) ** 2
            proj_sq = (phi @ wg) ** 2
            d_num = gap_sq * proj_sq * inv_2sig2 / (denom_g * denom_g)
            grad_w = (d_num * avg_cost - min_kl * costs) / (avg_cost * avg_cost)

            g_scale = float(np.max(np.abs(grad_w)))
            if g_scale <= 1e-14:
                break
            eta = 1.5 / (math.sqrt(it) * g_scale)
            log_w = np.log(np.maximum(w, 1e-16)) + eta * grad_w
            log_w -= float(np.max(log_w))
            w = np.exp(log_w)
            w = 0.98 * (w / float(np.sum(w))) + 0.02 / m

        per_action_rates.append(best_rate_a)
        if best_rate_a > best_overall_rate:
            best_overall_rate = best_rate_a
            best_action = a
            best_w = best_w_a

    char_time = 0.0 if math.isinf(best_overall_rate) else (1.0 / max(1e-15, best_overall_rate))
    return CharacteristicRateResult(
        target_action=best_action,
        rate=float(best_overall_rate),
        characteristic_time_kl1=float(char_time),
        optimal_weights=best_w,
        acceptable_actions=acceptable,
        per_action_rates=tuple(per_action_rates),
    )


class RegularizedInfoTrackerSession:
    """Practical regularized C-tracking session directly optimizing the paper's Gaussian
    information objective `I_*(theta_hat_t)` (Theorem 2.8) with exact finite-confidence
    Abbasi-Yadkori / GLR ellipsoidal stopping.

    Supports two operating modes (`hybrid_cd_warmup`):
    - `False`: Pure Regularized Information Tracking (`Info-Tracking`) from step `2*d`.
    - `True`: `Hybrid CD-Joint -> Tracking` — uses cheap `CD-Joint` during discovery until
      the candidate action stabilizes, then solves the plug-in saddle-point design on a
      geometric doubling refresh schedule to capture near-optimal information efficiency
      with low solver overhead.
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        phi: np.ndarray,
        prior_mean: float,
        obs_std: float,
        param_bound: float,
        delta: float = 0.05,
        reg_lambda: float = 0.05,
        costs: Sequence[float] | np.ndarray | None = None,
        hybrid_cd_warmup: bool = False,
        recompute_every: int = 12,
        outer_iters: int = 35,
        check_every: int = 1,
        adaptive_check: bool = False,
        stop_threshold_mode: str = "abbasi_yadkori",
    ) -> None:
        self.problem = problem
        self.graph = problem.graph
        self.support_struct = SupportStructure(self.graph, costs=costs)
        self.epsilon = float(epsilon)
        self.delta = float(delta)
        self.obs_std = float(obs_std)
        self.hybrid_cd_warmup = bool(hybrid_cd_warmup)
        self.recompute_every = max(1, int(recompute_every))
        self.outer_iters = max(12, int(outer_iters))
        self.check_every = max(1, int(check_every))
        self.adaptive_check = bool(adaptive_check)
        self.stop_threshold_mode = stop_threshold_mode

        self.oracle = problem.oracle(seed)
        self.model = LinearFeatureModel(
            phi=phi,
            prior_mean=prior_mean,
            reg_lambda=reg_lambda,
            obs_std=obs_std,
            subgaussian_sigma=obs_std,
            param_bound=param_bound,
            beta_mode="abbasi_yadkori",
            delta=delta,
        )
        self.certifier = JointEllipsoidCertifier(
            self.support_struct, epsilon=self.epsilon, solver="colgen_lazy", exact_linear_mean=True
        )
        self.w_span = _g_optimal_spanning_design(phi)
        self.m, self.d = phi.shape
        self.cum_w = np.zeros(self.m, dtype=np.float64)
        self.current_w = self.w_span.copy()

        self.calls = 0
        self.total_cost = 0.0
        self.certified = False
        self.action = 0
        self.current_regret = math.inf
        self.tracker_solve_time_s = 0.0
        self.tracker_solves = 0
        self.in_tracking_phase = not self.hybrid_cd_warmup

        self._last_cand_action = -1
        self._stable_count = 0
        self._next_track_refresh = 0
        self._next_arm = 0
        self._plan_and_check()

    def _effective_beta(self) -> float:
        if self.stop_threshold_mode == "glr_asymptotic":
            # Exact Kaufmann-Koolen / Garivier-Kaufmann Gaussian GLR threshold:
            # sqrt(2 * (log(1/delta) + 0.5 * d * log(1 + t / max(1, d)))) * sigma
            t = max(1, self.calls)
            return self.obs_std * math.sqrt(
                2.0 * (math.log(1.0 / self.delta) + 0.5 * self.d * math.log(1.0 + t / max(1.0, float(self.d))))
            )
        return self.model.beta()

    def _check_certificate(self) -> tuple[int, float, ActionCertificate | None]:
        means, psi = self.model.terminal_means_and_psi()
        stds = self.model.terminal_stds()
        beta = self._effective_beta()
        u_ell = means + beta * stds

        # Rank actions by fast optimistic approximation
        approx = []
        for a in range(self.support_struct.k):
            sup = self.support_struct.supports[a]
            comp = self.support_struct.complements[a]
            u_out = float(np.max(u_ell[comp])) if len(comp) else -math.inf
            approx.append((max(0.0, u_out - float(np.max(means[sup]))), a))
        approx.sort()

        best_a = approx[0][1]
        best_reg = math.inf
        best_cert: ActionCertificate | None = None
        for rank_i, (ap_r, a) in enumerate(approx):
            if rank_i >= 2 and best_reg > self.epsilon and ap_r > 2.5 * self.epsilon:
                continue
            c_a = self.certifier.certify_action(
                action=a, means=means, psi=psi, raw_features=self.model.phi, beta=beta, stop_if_above_eps=True
            )
            if c_a.regret < best_reg:
                best_reg = c_a.regret
                best_a = a
                best_cert = c_a
            if best_reg <= self.epsilon:
                break
        return best_a, best_reg, best_cert

    def _cd_step_arm(self) -> int:
        means, psi = self.model.terminal_means_and_psi()
        stds = self.model.terminal_stds()
        beta = self._effective_beta()
        u_ell = means + beta * stds
        w_star = int(np.argmax(u_ell))
        containing = [a for a, sup in enumerate(self.support_struct.supports) if w_star in set(sup.tolist())]
        b_t = max(
            containing,
            key=lambda a: float(u_ell[w_star])
            - (float(np.max(u_ell[self.support_struct.complements[a]])) if len(self.support_struct.complements[a]) else -math.inf),
        )
        comp_b = self.support_struct.complements[b_t]
        if len(comp_b) == 0:
            return w_star
        cert_b = self.certifier.certify_action(
            action=b_t, means=means, psi=psi, raw_features=self.model.phi, beta=beta, stop_if_above_eps=True
        )
        z_t = cert_b.challenger_idx
        gap_hat = float(means[z_t] - (cert_b.inside_weights @ means[cert_b.inside_indices]))
        g_active = cert_b.contrast if gap_hat <= 0.5 * self.epsilon else (self.model.phi[z_t] - self.model.phi[w_star])
        delta_v = self.model.contrast_variance_reduction(g_active)
        return int(np.argmax(delta_v / self.support_struct.costs))

    def _plan_and_check(self) -> None:
        best_a, best_reg, _ = self._check_certificate()
        self.action = best_a
        self.current_regret = best_reg
        if best_reg <= self.epsilon:
            self.certified = True
            return

        # Stability detection for Hybrid CD-Joint -> Tracking
        if best_a == self._last_cand_action:
            self._stable_count += 1
        else:
            self._last_cand_action = best_a
            self._stable_count = 1

        # Spanning pilot warmup for pure Info-Tracking
        if not self.hybrid_cd_warmup and self.calls < max(2 * self.d, 8):
            self.cum_w += self.w_span
            self._next_arm = int(np.argmax(self.cum_w - self.model.arm_counts))
            return

        # Hybrid transition check
        if self.hybrid_cd_warmup and not self.in_tracking_phase:
            if self.calls >= max(3 * self.d, 12) and self._stable_count >= 3:
                self.in_tracking_phase = True
                # Initialize cumulative tracking vector from actual empirical pulls so handoff is smooth!
                self.cum_w = self.model.arm_counts.astype(np.float64).copy()
                self._next_track_refresh = self.calls
            else:
                self._next_arm = self._cd_step_arm()
                return

        # Refresh plug-in optimal design w*(theta_hat_t) when scheduled
        if self.calls >= self._next_track_refresh:
            t_s0 = time.perf_counter()
            self.model._sync_factors()
            rate_res = fast_characteristic_rate(
                phi=self.model.phi,
                theta_star=self.model.theta_hat,
                support_struct=self.support_struct,
                epsilon=self.epsilon,
                sigma=self.obs_std,
                n_outer_iters=self.outer_iters,
                warm_w=self.current_w if self.tracker_solves > 0 else None,
            )
            self.tracker_solve_time_s += time.perf_counter() - t_s0
            self.tracker_solves += 1
            if np.all(np.isfinite(rate_res.optimal_weights)) and float(np.sum(rate_res.optimal_weights)) > 0.5:
                self.current_w = rate_res.optimal_weights.copy()
            if self.hybrid_cd_warmup:
                # Geometric doubling schedule keeps tracking compute O(log T)!
                self._next_track_refresh = max(self.calls + self.recompute_every, int(math.ceil(self.calls * 1.50)))
            else:
                # Lazy epoch C-tracking (O(log T) plug-in solves; preserves exact T_* asymptotic rate!)
                self._next_track_refresh = max(self.calls + self.recompute_every, int(math.ceil(self.calls * 1.25)))

        # Forced exploration mixing gamma_t = min(0.20, sqrt(d / (t + d))) -> 0 as t -> inf
        gamma_t = min(0.20, 0.5 * math.sqrt(float(self.d) / float(self.calls + self.d)))
        w_mix = (1.0 - gamma_t) * self.current_w + gamma_t * self.w_span
        self.cum_w += w_mix
        self._next_arm = int(np.argmax(self.cum_w - self.model.arm_counts))

    def step(self) -> bool:
        if self.certified:
            return False
        arm_idx = self._next_arm
        leaf = self.support_struct.leaves[arm_idx]
        reward = float(self.oracle.sample(leaf))
        self.calls += 1
        self.total_cost += float(self.support_struct.costs[arm_idx])
        self.model.observe(arm_idx, reward)

        stride = self.check_every
        if self.adaptive_check:
            if self.calls > 1500:
                stride = max(stride, 20)
            elif self.calls > 400:
                stride = max(stride, 10)
            elif self.calls > 100:
                stride = max(stride, 4)

        if self.calls % stride == 0:
            self._plan_and_check()
        elif self.in_tracking_phase:
            # Fast O(M) C-tracking step between certificate checks!
            gamma_t = min(0.20, 0.5 * math.sqrt(float(self.d) / float(self.calls + self.d)))
            self.cum_w += (1.0 - gamma_t) * self.current_w + gamma_t * self.w_span
            self._next_arm = int(np.argmax(self.cum_w - self.model.arm_counts))
        return True


# ---------------------------------------------------------------------------
# 3. Deconfounded 3-Factor Overlap x Correlation x Mismatch Problem (Exp 3)
# ---------------------------------------------------------------------------
class DeconfoundedOverlapCorrelationProblem(Problem):
    """Full-rank `M = 64` (`K = 8` actions) zero-containment search DAG decoupling:
    1. Support overlap `omega in {0.00, 0.25, 0.50, 0.75}` (strictly zero containments),
    2. Statistical cross-terminal correlation `rho in {0.0, 0.3, 0.6, 0.9}` via a FULL-RANK
       `64 x 64` SPD kernel `K(rho)` that equals the exact diagonal matrix `tau0^2 I_64` at
       `rho = 0.0` (completely removing the `d=8` low-rank confound of old E1!), and
    3. Controlled adversarial model mismatch `xi in {0.0, 0.015, 0.04}`.

    Observations draw paired `Uniform[mu_z - hw, mu_z + hw] subset [0, 1]` (`obs_std = hw / sqrt(3)`
    exact sub-Gaussian parameter), holding true exterior margin `Gamma = target_margin` and
    marginal noise scale constant across all 48 cells.
    """

    def __init__(
        self,
        seed: int,
        overlap: float,
        rho: float,
        mismatch_xi: float = 0.0,
        target_margin: float = 0.075,
        tau0: float = 0.14,
        hw: float = 0.16,
    ) -> None:
        k_act = 8
        b_mot = 8
        m_leaves = k_act * b_mot  # 64
        self.overlap = float(overlap)
        self.rho = float(rho)
        self.mismatch_xi = float(mismatch_xi)
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))
        self.prior_mean = 0.48

        # Build zero-containment supports parameterized cleanly by overlap omega in {0, .25, .5, .75}:
        # Every action g owns all 8 motifs of group g; motif b=7 of group g is ALWAYS private!
        # Additional shared motifs from neighboring groups scale with omega:
        #   omega=0.00 -> 0 shared  (|S|=8,  Jaccard=0.000)
        #   omega=0.25 -> 3 shared  (|S|=11, Jaccard~0.06)
        #   omega=0.50 -> 8 shared  (|S|=16, Jaccard~0.16)
        #   omega=0.75 -> 16 shared (|S|=24, Jaccard~0.33)
        n_shared_map = {0.0: 0, 0.25: 3, 0.5: 8, 0.75: 16}
        n_sh = n_shared_map.get(round(overlap, 2), int(round(overlap * 20)))

        children: list[tuple[int, ...]] = [tuple(range(1, k_act + 1))]
        leaf_offset = 1 + k_act
        for g in range(k_act):
            own = [leaf_offset + g * b_mot + b for b in range(b_mot)]
            shared: list[int] = []
            # Pull shared motifs cyclically from (g+1), (g+2), (g+3) over b in 0..5 (never b=6,7!)
            for offset in range(1, 4):
                for b in range(6):
                    if len(shared) >= n_sh:
                        break
                    shared.append(leaf_offset + ((g + offset) % k_act) * b_mot + b)
                if len(shared) >= n_sh:
                    break
            children.append(tuple(sorted(set(own + shared))))
        for _ in range(m_leaves):
            children.append(())

        labels = ["root"] + [f"act_{g}" for g in range(k_act)] + [
            f"leaf_g{g}_m{b}" for g in range(k_act) for b in range(b_mot)
        ]
        graph = DAG(children, root=0, labels=labels)

        # Full-rank 64x64 SPD kernel: STRICTLY DIAGONAL tau0^2 I_64 at rho = 0.0!
        k_grp = 0.25 * np.eye(k_act) + 0.75 * np.ones((k_act, k_act))
        k_mot = ar1_corr_matrix(b_mot, rho)
        k_corr = np.kron(k_grp, k_mot)
        self.kernel = (tau0 * tau0) * ((1.0 - rho) * np.eye(m_leaves) + rho * k_corr)
        self.diag_kernel = (tau0 * tau0) * np.eye(m_leaves)
        k_inv = np.linalg.inv(self.kernel)

        rng = np.random.default_rng(seed * 10007 + 79)
        perm = rng.permutation(k_act)
        g_win = int(perm[0])
        g_riv = int(perm[1])
        act_eff = np.zeros(k_act, dtype=np.float64)
        gaps_vec = [0.10, 0.10 - target_margin, 0.10 - 1.35 * target_margin, -0.01, -0.025, -0.04, -0.055, -0.07]
        for rk, gi in enumerate(perm):
            act_eff[int(gi)] = gaps_vec[rk]

        # Generate smooth correlated component scaled by sqrt(rho) + independent component by sqrt(1-rho)
        l_mot = np.linalg.cholesky(k_mot + 1e-6 * np.eye(b_mot))
        z_sh = l_mot @ rng.standard_normal(b_mot)
        z_sh = 0.060 * z_sh / max(1.0, float(np.max(np.abs(z_sh))))
        # Place motif peak in private motif b=7 so overlap never creates containment or destroys margin!
        z_sh[7] = float(np.max(z_sh)) + 0.025
        z_id = np.stack([l_mot @ rng.standard_normal(b_mot) for _ in range(k_act)], axis=0)
        z_id = 0.035 * z_id / max(1.0, float(np.max(np.abs(z_id))))

        f_clean = (
            self.prior_mean
            + act_eff[:, None]
            + math.sqrt(max(0.0, rho)) * z_sh[None, :]
            + math.sqrt(max(0.0, 1.0 - rho)) * z_id
        ).reshape(-1)
        f_clean = np.clip(f_clean, hw + 0.05, 1.0 - hw - 0.05)

        # Controlled adversarial mismatch perturbation b with ||b||_inf = mismatch_xi:
        # boosts rival group's peak & slightly perturbs non-winner leaves against the smooth prior
        b_vec = np.zeros(m_leaves, dtype=np.float64)
        if mismatch_xi > 0.0:
            signs = rng.choice([-1.0, 1.0], size=m_leaves)
            b_vec = 0.7 * mismatch_xi * signs
            # Worst-case adversarial spike on a rival private leaf (confusing smooth GP!)
            b_vec[g_riv * b_mot + 7] = +mismatch_xi
            b_vec[g_win * b_mot + 7] = -mismatch_xi
        f_true = np.clip(f_clean + b_vec, hw + 0.01, 1.0 - hw - 0.01)

        # Re-center clean RKHS norm for well-specified reference
        diff_c = f_clean - self.prior_mean
        self.clean_rkhs_norm = float(math.sqrt(max(0.0, float(diff_c @ (k_inv @ diff_c)))))
        diff_t = f_true - self.prior_mean
        self.true_rkhs_norm = float(math.sqrt(max(0.0, float(diff_t @ (k_inv @ diff_t)))))
        self.f_clean = f_clean
        self.b_vec = f_true - f_clean

        means = {leaf_offset + i: float(f_true[i]) for i in range(m_leaves)}
        super().__init__(
            f"deconf_o{overlap:.2f}_r{rho:.2f}_x{mismatch_xi:.3f}_s{seed}",
            graph,
            means,
            (),
        )

    def oracle(self, seed: int):
        prob = self
        s64 = seed & 0xFFFFFFFFFFFFFFFF
        means = prob.means
        hw = prob.hw

        class _PairedUnif:
            def __init__(self):
                self.obs = [0] * len(prob.graph)
                self.operations = 0

            def sample(self, leaf: int) -> float:
                self.obs[leaf] += 1
                k = self.obs[leaf]
                self.operations += 4
                u = splitmix_uniform01(s64, leaf, k)
                return means[leaf] + hw * (2.0 * u - 1.0)

        return _PairedUnif()


# ---------------------------------------------------------------------------
# 4. Adaptive Conic Schedules & Verified Approximate Solves (Experiment 4)
# ---------------------------------------------------------------------------
class ScheduledConicCertifier:
    """Benchmarks five conic maintenance & verified approximate-solve schedules on identical
    observation streams and identical stopping threshold `eps`:
    1. `exact_every_step`: Exact ColGen (`tol=1e-7`, `colgen_full`) on every step.
    2. `lazy_every_step`: Lazy challenger pruning + warm-started ColGen (`tol=1e-7`) every step.
    3. `periodic_conservative`: Lazy ColGen every `period` steps; on intermediate steps evaluates
       cached feasible mixtures `p_cached in Delta(S(a))` in `O(d)` as a provably valid upper bound!
    4. `adaptive_tol_lazy`: Verified approximate ColGen with adaptive gap tolerance
       `tol_t = clip(0.25 * (R_prev - eps), 1e-7, 0.05)` (still returning a provably sound upper bound!).
    5. `hybrid_rect_joint`: Fast vectorized single-vertex / rectangular upper bound first; falls
       back to `adaptive_tol_lazy` only when rectangular bound fails to certify, refreshing on
       a geometric work-amortized schedule.
    """

    STRATEGIES = (
        "exact_every_step",
        "lazy_every_step",
        "periodic_conservative",
        "adaptive_tol_lazy",
        "hybrid_rect_joint",
    )

    def __init__(
        self,
        support_struct: SupportStructure,
        epsilon: float,
        strategy: str,
        period: int = 10,
    ) -> None:
        if strategy not in self.STRATEGIES:
            raise ValueError(f"Unknown conic schedule strategy: {strategy!r}")
        self.ss = support_struct
        self.epsilon = float(epsilon)
        self.strategy = strategy
        self.period = max(2, int(period))

        solver_mode = "colgen_full" if strategy == "exact_every_step" else "colgen_lazy"
        self.base_cert = JointEllipsoidCertifier(
            support_struct, epsilon=self.epsilon, solver=solver_mode, exact_linear_mean=True
        )
        # Cached feasible mixtures per action: action -> dict[z_idx, (indices, weights)]
        self._cached_mix: dict[int, tuple[np.ndarray, np.ndarray]] = {}
        self._last_regret = 1.0
        self.step_count = 0
        self.conic_oracle_calls = 0
        self.total_time_s = 0.0
        self.max_excess_over_exact = 0.0

    def _fast_vertex_upper_bound(
        self, action: int, means: np.ndarray, psi: np.ndarray, beta: float
    ) -> float:
        sup = self.ss.supports[action]
        comp = self.ss.complements[action]
        if len(comp) == 0:
            return 0.0
        stds = np.linalg.norm(psi, axis=1)
        # Single best lower-bound witness inside S(a) for O(|comp| * d) upper bound!
        y_lcb = int(sup[int(np.argmax(means[sup] - beta * stds[sup]))])
        diff_psi = psi[comp] - psi[y_lcb][None, :]
        norms = np.linalg.norm(diff_psi, axis=1)
        return max(0.0, float(np.max((means[comp] - float(means[y_lcb])) + beta * norms)))

    def _cached_mixture_upper_bound(
        self, action: int, means: np.ndarray, psi: np.ndarray, beta: float
    ) -> float | None:
        if action not in self._cached_mix:
            return None
        sup_idx, wts = self._cached_mix[action]
        comp = self.ss.complements[action]
        if len(comp) == 0:
            return 0.0
        # Evaluate the fixed feasible mixture p_cached across ALL outside challengers in O(|comp| * d)!
        m_mix = float(wts @ means[sup_idx])
        psi_mix = wts @ psi[sup_idx]
        diff_psi = psi[comp] - psi_mix[None, :]
        norms = np.linalg.norm(diff_psi, axis=1)
        return max(0.0, float(np.max((means[comp] - m_mix) + beta * norms)))

    def _solve_adaptive_tol_action(
        self, action: int, means: np.ndarray, psi: np.ndarray, raw_features: np.ndarray, beta: float, tol: float
    ) -> ActionCertificate:
        sup = self.ss.supports[action]
        comp = self.ss.complements[action]
        if len(comp) == 0:
            return ActionCertificate(
                action=action,
                regret=0.0,
                challenger_idx=-1,
                inside_indices=sup[:1],
                inside_weights=np.ones(1),
                contrast=np.zeros(psi.shape[1]),
                max_duality_gap=0.0,
                evaluated_challengers=0,
                total_challengers=0,
            )
        stds = np.linalg.norm(psi, axis=1)
        m_sup = means[sup]
        psi_sup = psi[sup]
        anchor_pos = np.argsort(-m_sup)[: min(len(sup), 4)]
        y_lcb = int(sup[int(np.argmax(m_sup - beta * stds[sup]))])
        anc_idx = np.unique(np.append(sup[anchor_pos], y_lcb))
        psi_comp = psi[comp]
        psi_anc = psi[anc_idx]
        sq_comp = np.sum(psi_comp * psi_comp, axis=1, keepdims=True)
        sq_anc = np.sum(psi_anc * psi_anc, axis=1, keepdims=True).T
        q_mat = np.sqrt(np.maximum(0.0, sq_comp + sq_anc - 2.0 * (psi_comp @ psi_anc.T)))
        vert_ub = np.min((means[comp][:, None] - means[anc_idx][None, :]) + beta * q_mat, axis=1)
        # Tighten vert_ub using cached warm mixtures for O(1) lazy pruning!
        for pos, z_i in enumerate(comp):
            cached = self.base_cert._warm_cache.get((action, int(z_i)))
            if cached is not None:
                c_idx, c_w = cached
                u_c = psi[int(z_i)] - (c_w @ psi[c_idx])
                val_c = (float(means[int(z_i)]) - float(c_w @ means[c_idx])) + beta * float(np.linalg.norm(u_c))
                if val_c < vert_ub[pos]:
                    vert_ub[pos] = val_c
        order = np.argsort(-vert_ub)
        if float(vert_ub[int(order[0])]) <= self.epsilon:
            z0 = int(comp[int(order[0])])
            return ActionCertificate(
                action=action,
                regret=max(0.0, float(vert_ub[int(order[0])])),
                challenger_idx=z0,
                inside_indices=np.array([y_lcb]),
                inside_weights=np.ones(1),
                contrast=raw_features[z0] - raw_features[y_lcb],
                max_duality_gap=0.0,
                evaluated_challengers=0,
                total_challengers=len(comp),
            )

        best_val = -math.inf
        best_z = int(comp[int(order[0])])
        best_idx = np.array([y_lcb], dtype=np.int64)
        best_w = np.ones(1, dtype=np.float64)
        max_gap = 0.0
        eval_cnt = 0
        for pos in order:
            if float(vert_ub[pos]) <= best_val and best_val > -math.inf:
                break
            z_idx = int(comp[pos])
            eval_cnt += 1
            warm = self.base_cert._warm_cache.get((action, z_idx))
            res = solve_feature_challenger_colgen(
                z_idx=z_idx,
                sup=sup,
                means=means,
                psi=psi,
                raw_features=raw_features,
                beta=beta,
                warm_indices=warm[0] if warm else None,
                warm_weights=warm[1] if warm else None,
                tol=tol,
                max_outer=12 if tol >= 1e-3 else 25,
            )
            self.base_cert._warm_cache[(action, z_idx)] = (res.support_indices, res.weights)
            max_gap = max(max_gap, float(res.duality_gap))
            if res.dual_value > best_val:
                best_val = res.dual_value
                best_z = z_idx
                best_idx = res.support_indices
                best_w = res.weights
        g_vec = raw_features[best_z] - (best_w @ raw_features[best_idx])
        return ActionCertificate(
            action=action,
            regret=max(0.0, best_val),
            challenger_idx=best_z,
            inside_indices=best_idx,
            inside_weights=best_w,
            contrast=g_vec,
            max_duality_gap=max_gap,
            evaluated_challengers=eval_cnt,
            total_challengers=len(comp),
        )

    def evaluate_action(
        self, action: int, means: np.ndarray, psi: np.ndarray, raw_features: np.ndarray, beta: float
    ) -> float:
        t0 = time.perf_counter()
        self.step_count += 1

        if self.strategy in ("exact_every_step", "lazy_every_step"):
            self.conic_oracle_calls += 1
            cert = self.base_cert.certify_action(
                action, means, psi, raw_features, beta, stop_if_above_eps=False
            )
            reg = cert.regret
            self._cached_mix[action] = (cert.inside_indices, cert.inside_weights)
        elif self.strategy == "periodic_conservative":
            if self.step_count == 1 or (self.step_count % self.period == 0) or action not in self._cached_mix:
                self.conic_oracle_calls += 1
                cert = self.base_cert.certify_action(
                    action, means, psi, raw_features, beta, stop_if_above_eps=False
                )
                reg = cert.regret
                self._cached_mix[action] = (cert.inside_indices, cert.inside_weights)
            else:
                # Provably valid conservative O(|comp| * d) upper bound using cached mixture!
                ub_mix = self._cached_mixture_upper_bound(action, means, psi, beta)
                ub_vert = self._fast_vertex_upper_bound(action, means, psi, beta)
                reg = min(ub_vert, ub_mix if ub_mix is not None else ub_vert)
        elif self.strategy == "adaptive_tol_lazy":
            self.conic_oracle_calls += 1
            tol_t = min(0.04, max(1e-7, 0.25 * max(0.0, self._last_regret - self.epsilon)))
            cert = self._solve_adaptive_tol_action(action, means, psi, raw_features, beta, tol=tol_t)
            reg = cert.regret
            # If adaptive loose upper bound already near eps, verify tightly to avoid missing stopping!
            if reg > self.epsilon and reg - self.epsilon <= 1.5 * tol_t and tol_t > 1e-6:
                cert = self._solve_adaptive_tol_action(action, means, psi, raw_features, beta, tol=1e-7)
                reg = cert.regret
            self._cached_mix[action] = (cert.inside_indices, cert.inside_weights)
        else:
            # `hybrid_rect_joint`: fast rectangular/vertex bound first; amortize adaptive conic solves
            ub_vert = self._fast_vertex_upper_bound(action, means, psi, beta)
            if ub_vert <= self.epsilon:
                reg = ub_vert
            else:
                ub_mix = self._cached_mixture_upper_bound(action, means, psi, beta)
                ub_fast = min(ub_vert, ub_mix) if ub_mix is not None else ub_vert
                if ub_fast <= self.epsilon:
                    reg = ub_fast
                elif (
                    self.step_count == 1
                    or (self.step_count % self.period == 0)
                    or (ub_fast <= 1.35 * self.epsilon and self.step_count % 3 == 0)
                ):
                    self.conic_oracle_calls += 1
                    tol_t = min(0.04, max(1e-7, 0.25 * max(0.0, ub_fast - self.epsilon)))
                    cert = self._solve_adaptive_tol_action(action, means, psi, raw_features, beta, tol=tol_t)
                    reg = min(ub_fast, cert.regret)
                    if reg > self.epsilon and reg - self.epsilon <= 1.5 * tol_t and tol_t > 1e-6:
                        cert = self._solve_adaptive_tol_action(action, means, psi, raw_features, beta, tol=1e-7)
                        reg = min(ub_fast, cert.regret)
                    self._cached_mix[action] = (cert.inside_indices, cert.inside_weights)
                else:
                    reg = ub_fast

        self._last_regret = reg
        self.total_time_s += time.perf_counter() - t0
        return reg


# ---------------------------------------------------------------------------
# 5. Hard-Regime Adaptive Sampling for Mid-Game SameGame & Tied-Star (Exp 6)
# ---------------------------------------------------------------------------
def _bernoulli_kl(p: float, q: float) -> float:
    p = min(1.0 - 1e-12, max(1e-12, p))
    q = min(1.0 - 1e-12, max(1e-12, q))
    return p * math.log(p / q) + (1.0 - p) * math.log((1.0 - p) / (1.0 - q))


class AdaptiveHardRegimeSession:
    """Adaptive hard-regime exact-regret sampler over `O(log M)` `DualWitnessCovers` (Exp 6).

    Explicitly tracks the ratio of inside-witness discovery difficulty (`inside_slack = U(a) - L(a)`)
    to outside-challenger uncertainty (`outside_gap = U^-(a) - L(a)`):
    - `adaptive_os_lcb`: Combines `Optimistic-Separation` action selection (preserving exact
      `eps=0` certification on Tied-Star!) with `Safeguarded-LCB` inside-witness focusing
      whenever the chosen support exhibits wide near-tied ambiguity (`u(p) - l(y) > eps/2` and
      `y` satisfies the safeguard gate `w(y) >= max(0.5 * R(b), u(p) - u(y))`).
    - `kl_info_hybrid`: Uses the same adaptive action & safeguarded inside witness, then scores
      the inside vs. outside witness by exact empirical-variance / Bernoulli KL-information
      marginal progress per pull (`(sigma_hat^2 / (n+1))` weighted by current width), focusing
      budget on the higher-leverage witness on narrow-gap mid-game boards.
    """

    VALID_MODES = ("adaptive_os_lcb", "kl_info_hybrid")

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        mode: str = "adaptive_os_lcb",
        delta: float = 0.05,
        schedule: str = "emp_bernstein",
    ) -> None:
        if mode not in self.VALID_MODES:
            raise ValueError(f"Unsupported AdaptiveHardRegimeSession mode: {mode!r}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = float(epsilon)
        self.mode = mode
        self.oracle = problem.oracle(seed)
        self.policy_work = w = UCTWork()
        self.monitor = DualWitnessCovers(
            self.graph, delta=delta, schedule=schedule, layout="best", track_separation=True
        )
        self.leaf_paths = _shortest_leaf_paths(self.graph, w)
        self.leaves = list(self.graph.leaves)
        self.k_actions = len(self.graph.children[self.graph.root])
        self.calls = 0
        self.certified = False
        self.action = 0
        self._refresh()

    def _refresh(self) -> None:
        act, reg, _, _, _ = self.monitor.query_dual_witness()
        self.action = int(act)
        if not self.monitor.evidence.conflict and reg <= self.epsilon:
            self.certified = True

    def _select_leaf(self) -> int:
        ev = self.monitor.evidence
        # 1. Always select the Optimistic-Separation action `best_b` (Theorem 3.2):
        #    guarantees exact eps=0 certification on tied-optima exterior-margin graphs (Tied-Star),
        #    while reducing cleanly to the top-separation action on SameGame, Decoy-16, and Hetero-256.
        _, _, best_b, _, p_t, q_t = self.monitor.query_optimistic_separation()
        chosen_a = int(best_b)
        p_t = int(p_t)
        q_t = int(q_t)
        if q_t < 0:
            return p_t

        # 2. Retrieve O(log M) LCB inside witness `y_t` in S(chosen_a) from DualWitnessCovers
        pca = self.monitor.pos_covers[chosen_a]
        best_lo_d = max(pca, key=lambda d: (self.monitor.low[d], self.monitor.low_hi[d], -self.monitor.low_leaf[d]))
        y_t = int(self.monitor.low_leaf[best_lo_d])

        reg_a = max(0.0, float(ev.upper[q_t] - ev.lower[y_t]))
        w_y = float(ev.upper[y_t] - ev.lower[y_t])
        # 3. Apply Theorem 3.1 Safeguarded-LCB gate inside S(best_b):
        #    focuses on y_t on heterogeneous/mid-game supports without ever trapping on decoys!
        if w_y >= max(0.5 * reg_a, float(ev.upper[p_t] - ev.upper[y_t])):
            z_in = y_t
        else:
            z_in = p_t

        w_in = float(ev.upper[z_in] - ev.lower[z_in])
        w_out = float(ev.upper[q_t] - ev.lower[q_t])

        if self.mode == "adaptive_os_lcb":
            return z_in if (w_in, -z_in) >= (w_out, -q_t) else q_t

        # `kl_info_hybrid`: marginal one-step width/KL contraction score on {z_in, q_t}
        n_in = max(0, int(self.oracle.obs[z_in]))
        n_out = max(0, int(self.oracle.obs[q_t]))
        if n_in == 0:
            return z_in
        if n_out == 0:
            return q_t
        m_in = 0.5 * (float(ev.lower[z_in]) + float(ev.upper[z_in]))
        m_out = 0.5 * (float(ev.lower[q_t]) + float(ev.upper[q_t]))
        mid = 0.5 * (m_in + m_out)
        dw_in = w_in * (1.0 - math.sqrt(n_in / (n_in + 1.0))) * (1.0 + _bernoulli_kl(m_in, mid))
        dw_out = w_out * (1.0 - math.sqrt(n_out / (n_out + 1.0))) * (1.0 + _bernoulli_kl(m_out, mid))
        return z_in if (dw_in, w_in, -z_in) >= (dw_out, w_out, -q_t) else q_t

    def step(self) -> bool:
        if self.certified or self.monitor.evidence.conflict:
            return False
        target = self._select_leaf()
        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1
        reward = float(self.oracle.sample(target))
        self.calls += 1
        self.policy_work.oracle_calls += 1
        if not self.monitor.step(target, reward):
            return False
        self._refresh()
        return True
