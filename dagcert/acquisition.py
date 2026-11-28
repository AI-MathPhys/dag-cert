"""Decision-directed experimental design policies and high-level certification runner."""
from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
import math
from typing import Literal

import numpy as np
from scipy.stats import norm

from dagcert._core.v5_hybrid_and_os import DualWitnessCovers
from dagcert._core.v7_bayesian_ucd import JointEllipsoidCertifier, SupportStructure
from dagcert._core.v12_bed_acquisition import (
    ALL_V12_POLICIES,
    MatchedModelBEDSession,
    SharedGaussianPosterior,
    correlated_kg_log_scores,
    default_check_schedule,
    exact_correlated_kg_single,
    log_expected_pos_normal,
    noisy_gp_ei_log_scores,
    select_bayesian_root_voi,
)
from dagcert.certificates import check_ellipsoid_stopping
from dagcert.graph import DAG, SearchDAG
from dagcert.margin_aware import (
    GAUSS_HERMITE_9_NODES,
    GAUSS_HERMITE_9_WEIGHTS,
    MarginAwareSelection,
    build_query_shortlist,
    build_witness_pool,
    compute_exact_standardized_margin,
    compute_mechanistic_snapshot,
    select_margin_aware_query,
)
from dagcert.posteriors import (
    chi2_credible_beta,
    contrast_rank_of_kernel,
    eval_direct_posterior_risk_valid,
    mc_postrisk_schedule,
)


def _build_leaf_to_actions(ss: SupportStructure) -> list[list[int]]:
    l2a: list[list[int]] = [[] for _ in range(ss.m)]
    for a, sup in enumerate(ss.supports):
        for idx in sup:
            l2a[int(idx)].append(a)
    return l2a


def select_gp_arm_with_beta(
    policy: str,
    supports: SupportStructure,
    leaf_to_actions: list[list[int]],
    posterior: SharedGaussianPosterior,
    certifier: JointEllipsoidCertifier,
    beta: float,
    epsilon: float,
    step: int = 1,
    delta: float = 0.05,
    rng: np.random.Generator | None = None,
    use_cpp: bool = True,
    cd_stop_if_above_eps: bool = True,
) -> int:
    """Select the next terminal index ``0..M-1`` under a shared Gaussian posterior and radius ``beta``.

    Supports ``'cd_joint'``, ``'kg'``, ``'gp_os'``, ``'gp_root_info'``, ``'gp_ucb'``,
    ``'gp_ts'``, and ``'gp_ei'``.
    """
    means = posterior.mean
    costs = supports.costs
    m = supports.m

    if policy == "kg":
        scores = correlated_kg_log_scores(means, posterior.sigma_mat, posterior.obs_var, costs, use_cpp=use_cpp)
        return int(np.argmax(scores))

    stds = posterior.stds()
    if policy == "gp_ucb":
        t_eff = max(1, int(step))
        kappa = math.sqrt(2.0 * math.log(max(2.0, float(m) * (math.pi**2) * float(t_eff * t_eff) / (6.0 * delta))))
        return int(np.argmax(means + kappa * stds))

    if policy == "gp_ts":
        gen = rng if rng is not None else np.random.default_rng()
        draw = means + posterior.cholesky() @ gen.standard_normal(m)
        return int(np.argmax(draw))

    if policy == "gp_ei":
        return int(np.argmax(noisy_gp_ei_log_scores(means, stds, costs)))

    u_ell = means + beta * stds
    l_ell = means - beta * stds

    if policy in ("gp_root_info", "gp_root_info_gp"):
        w_star = int(np.argmax(u_ell))
        best_sep = -math.inf
        b_t = leaf_to_actions[w_star][0]
        for a in leaf_to_actions[w_star]:
            comp = supports.complements[a]
            u_out = float(np.max(u_ell[comp])) if len(comp) else -math.inf
            sep = float(u_ell[w_star]) - u_out
            if sep > best_sep:
                best_sep = sep
                b_t = a
        comp_b = supports.complements[b_t]
        if len(comp_b) == 0:
            return w_star
        z_box = int(comp_b[int(np.argmax(u_ell[comp_b]))])
        return w_star if float(stds[w_star]) >= float(stds[z_box]) else z_box

    if policy == "gp_os":
        best_a = 0
        best_sep = -math.inf
        for a in range(supports.k):
            comp = supports.complements[a]
            u_in = float(np.max(u_ell[supports.supports[a]]))
            l_out = float(np.max(l_ell[comp])) if len(comp) else -math.inf
            sep = u_in - l_out
            if sep > best_sep:
                best_sep = sep
                best_a = a
        sup_b = supports.supports[best_a]
        comp_b = supports.complements[best_a]
        p_idx = int(sup_b[int(np.argmax(u_ell[sup_b]))])
        if len(comp_b) == 0:
            return p_idx
        q_idx = int(comp_b[int(np.argmax(u_ell[comp_b]))])
        sp = float(stds[p_idx]) / math.sqrt(float(costs[p_idx]))
        sq = float(stds[q_idx]) / math.sqrt(float(costs[q_idx]))
        return p_idx if sp >= sq else q_idx

    if policy == "cd_joint":
        y_opt = int(np.argmax(u_ell))
        best_sep = -math.inf
        b_t = leaf_to_actions[y_opt][0]
        for a in leaf_to_actions[y_opt]:
            comp = supports.complements[a]
            l_out = float(np.max(l_ell[comp])) if len(comp) else -math.inf
            sep = float(u_ell[y_opt]) - l_out
            if sep > best_sep:
                best_sep = sep
                b_t = a
        prev_eps = certifier.epsilon
        certifier.epsilon = float(epsilon)
        try:
            cb = certifier.certify_action_gp(
                action=b_t,
                means=means,
                sigma_mat=posterior.sigma_mat,
                beta=beta,
                stop_if_above_eps=cd_stop_if_above_eps,
            )
        finally:
            certifier.epsilon = prev_eps
        z_t = cb.challenger_idx
        if z_t < 0:
            return y_opt
        gap_hat = float(means[z_t] - (cb.inside_weights @ means[cb.inside_indices]))
        if gap_hat <= 0.5 * epsilon:
            g = cb.contrast
        else:
            g = np.zeros(m, dtype=np.float64)
            g[z_t] = 1.0
            g[y_opt] = -1.0
        sg = posterior.sigma_mat @ g
        dv = (sg * sg) / (posterior.obs_var + np.maximum(1e-18, np.diag(posterior.sigma_mat)))
        return int(np.argmax(dv / costs))

    if policy == "cd_joint_single_witness":
        y_opt = int(np.argmax(u_ell))
        containers = leaf_to_actions[y_opt]
        b_t = max(containers, key=lambda b: (float(np.max(means[supports.supports[b]])), -b))
        sup = supports.supports[b_t]
        comp = supports.complements[b_t]
        if len(comp) == 0:
            return y_opt
        diag_all = np.maximum(1e-18, np.diag(posterior.sigma_mat))
        sig_sc = posterior.sigma_mat[sup[:, None], comp[None, :]]
        q_mat = np.sqrt(np.maximum(1e-18, diag_all[comp][None, :] + diag_all[sup][:, None] - 2.0 * sig_sc))
        vert_scores = (means[comp][None, :] - means[sup][:, None]) + beta * q_mat
        best_y_pos = np.argmin(vert_scores, axis=0)
        vert_ub = vert_scores[best_y_pos, np.arange(len(comp))]
        worst_c = int(np.argmax(vert_ub))
        z_t = int(comp[worst_c])
        y_w = int(sup[int(best_y_pos[worst_c])])
        g = np.zeros(m, dtype=np.float64)
        g[z_t] = 1.0
        g[y_w if float(means[z_t] - means[y_w]) <= 0.5 * epsilon else y_opt] = -1.0
        sg = posterior.sigma_mat @ g
        dv = (sg * sg) / (posterior.obs_var + diag_all)
        return int(np.argmax(dv / costs))

    if policy in ("ma_cd_joint", "ma_cd_joint_safe"):
        sel = select_margin_aware_query(
            supports=supports,
            leaf_to_actions=leaf_to_actions,
            posterior=posterior,
            certifier=certifier,
            beta=beta,
            epsilon=epsilon,
            step_idx=max(0, int(step) - 1),
            safe=(policy == "ma_cd_joint_safe"),
            cd_stop_if_above_eps=cd_stop_if_above_eps,
            root_selection_mode="ucb_lcb_sep",
            use_cpp=use_cpp,
        )
        return sel.arm

    raise ValueError(f"Unknown policy: {policy!r}")


class AcquisitionPolicy:
    """Base interface for Bayesian root-certification acquisition policies."""

    name: str = "base"

    def select(
        self,
        posterior: SharedGaussianPosterior,
        supports: SupportStructure,
        certifier: JointEllipsoidCertifier,
        *,
        beta: float | None = None,
        epsilon: float = 0.02,
        step: int = 1,
        delta: float = 0.05,
        leaf_to_actions: list[list[int]] | None = None,
    ) -> int:
        raise NotImplementedError


class CDJointPolicy(AcquisitionPolicy):
    """Safeguarded Contrast-Directed Joint Acquisition (Algorithm 1, Eq. 7)."""

    name = "cd_joint"

    def select(
        self,
        posterior: SharedGaussianPosterior,
        supports: SupportStructure,
        certifier: JointEllipsoidCertifier,
        *,
        beta: float | None = None,
        epsilon: float = 0.02,
        step: int = 1,
        delta: float = 0.05,
        leaf_to_actions: list[list[int]] | None = None,
    ) -> int:
        b = posterior.beta() if beta is None else float(beta)
        l2a = leaf_to_actions if leaf_to_actions is not None else _build_leaf_to_actions(supports)
        return select_gp_arm_with_beta("cd_joint", supports, l2a, posterior, certifier, b, epsilon, step, delta)


class CorrelatedKGPolicy(AcquisitionPolicy):
    """Exact analytical O(M log M) Correlated Knowledge Gradient (Frazier-Powell-Dayanik 2009)."""

    name = "kg"

    def __init__(self, use_cpp: bool = True) -> None:
        self.use_cpp = bool(use_cpp)

    def select(
        self,
        posterior: SharedGaussianPosterior,
        supports: SupportStructure,
        certifier: JointEllipsoidCertifier,
        *,
        beta: float | None = None,
        epsilon: float = 0.02,
        step: int = 1,
        delta: float = 0.05,
        leaf_to_actions: list[list[int]] | None = None,
    ) -> int:
        scores = correlated_kg_log_scores(
            posterior.mean, posterior.sigma_mat, posterior.obs_var, supports.costs, use_cpp=self.use_cpp
        )
        return int(np.argmax(scores))


class GPOSPolicy(AcquisitionPolicy):
    """Correlated GP Optimistic Separation policy."""

    name = "gp_os"

    def select(
        self,
        posterior: SharedGaussianPosterior,
        supports: SupportStructure,
        certifier: JointEllipsoidCertifier,
        *,
        beta: float | None = None,
        epsilon: float = 0.02,
        step: int = 1,
        delta: float = 0.05,
        leaf_to_actions: list[list[int]] | None = None,
    ) -> int:
        b = posterior.beta() if beta is None else float(beta)
        l2a = leaf_to_actions if leaf_to_actions is not None else _build_leaf_to_actions(supports)
        return select_gp_arm_with_beta("gp_os", supports, l2a, posterior, certifier, b, epsilon, step, delta)


class BayesianVOIPolicy(AcquisitionPolicy):
    """One-step Bayesian Root-Risk Value-of-Information reference policy (Eq. 5)."""

    name = "bayesian_voi"

    def __init__(self, n_y: int = 32, n_mu: int = 2048, seed: int = 0, use_cpp: bool = True) -> None:
        probs = (np.arange(int(n_y), dtype=np.float64) + 0.5) / float(n_y)
        self._y_quantiles = norm.ppf(probs)
        self._n_mu = int(n_mu)
        self._rng = np.random.default_rng(int(seed))
        self._use_cpp = bool(use_cpp)

    def select(
        self,
        posterior: SharedGaussianPosterior,
        supports: SupportStructure,
        certifier: JointEllipsoidCertifier,
        *,
        beta: float | None = None,
        epsilon: float = 0.02,
        step: int = 1,
        delta: float = 0.05,
        leaf_to_actions: list[list[int]] | None = None,
    ) -> int:
        half = self._n_mu // 2
        z_half = self._rng.standard_normal((posterior.m, half))
        u_crn = np.concatenate([z_half, -z_half], axis=1)
        if u_crn.shape[1] < self._n_mu:
            u_crn = np.concatenate([u_crn, self._rng.standard_normal((posterior.m, 1))], axis=1)
        chosen, _, _, _ = select_bayesian_root_voi(
            means=posterior.mean,
            sigma_mat=posterior.sigma_mat,
            obs_var=posterior.obs_var,
            costs=supports.costs,
            supports=supports.supports,
            complements=supports.complements,
            epsilon=epsilon,
            y_quantiles=self._y_quantiles,
            std_normals=u_crn,
            use_cpp=self._use_cpp,
        )
        return int(chosen)


class GPUCBPolicy(AcquisitionPolicy):
    """Finite-domain GP-UCB terminal-optimization baseline."""

    name = "gp_ucb"

    def select(self, posterior, supports, certifier, *, beta=None, epsilon=0.02, step=1, delta=0.05, leaf_to_actions=None):
        l2a = leaf_to_actions if leaf_to_actions is not None else _build_leaf_to_actions(supports)
        return select_gp_arm_with_beta("gp_ucb", supports, l2a, posterior, certifier, 1.0, epsilon, step, delta)


class GPTSPolicy(AcquisitionPolicy):
    """Gaussian Process Thompson Sampling baseline."""

    name = "gp_ts"

    def __init__(self, seed: int = 0) -> None:
        self._rng = np.random.default_rng(int(seed))

    def select(self, posterior, supports, certifier, *, beta=None, epsilon=0.02, step=1, delta=0.05, leaf_to_actions=None):
        l2a = leaf_to_actions if leaf_to_actions is not None else _build_leaf_to_actions(supports)
        return select_gp_arm_with_beta("gp_ts", supports, l2a, posterior, certifier, 1.0, epsilon, step, delta, rng=self._rng)


class NoisyGPEIPolicy(AcquisitionPolicy):
    """Noisy Expected Improvement (posterior-mean incumbent) baseline."""

    name = "gp_ei"

    def select(self, posterior, supports, certifier, *, beta=None, epsilon=0.02, step=1, delta=0.05, leaf_to_actions=None):
        l2a = leaf_to_actions if leaf_to_actions is not None else _build_leaf_to_actions(supports)
        return select_gp_arm_with_beta("gp_ei", supports, l2a, posterior, certifier, 1.0, epsilon, step, delta)


class MACDJointPolicy(AcquisitionPolicy):
    """Margin-Aware Contrast-Directed Joint Acquisition (MA-CD-Joint)."""

    name = "ma_cd_joint"

    def select(self, posterior, supports, certifier, *, beta=None, epsilon=0.02, step=1, delta=0.05, leaf_to_actions=None):
        b = posterior.beta() if beta is None else float(beta)
        l2a = leaf_to_actions if leaf_to_actions is not None else _build_leaf_to_actions(supports)
        return select_gp_arm_with_beta("ma_cd_joint", supports, l2a, posterior, certifier, b, epsilon, step, delta)


class MACDJointSafePolicy(AcquisitionPolicy):
    """Safe Alternating Margin-Aware Contrast-Directed Joint Acquisition (MA-CD-Joint-Safe)."""

    name = "ma_cd_joint_safe"

    def select(self, posterior, supports, certifier, *, beta=None, epsilon=0.02, step=1, delta=0.05, leaf_to_actions=None):
        b = posterior.beta() if beta is None else float(beta)
        l2a = leaf_to_actions if leaf_to_actions is not None else _build_leaf_to_actions(supports)
        return select_gp_arm_with_beta("ma_cd_joint_safe", supports, l2a, posterior, certifier, b, epsilon, step, delta)


def make_policy(name: str, seed: int = 0) -> AcquisitionPolicy:
    """Instantiate a named Bayesian acquisition policy."""
    registry: dict[str, Callable[[], AcquisitionPolicy]] = {
        "cd_joint": CDJointPolicy,
        "ma_cd_joint": MACDJointPolicy,
        "ma_cd_joint_safe": MACDJointSafePolicy,
        "kg": CorrelatedKGPolicy,
        "gp_os": GPOSPolicy,
        "bayesian_voi": lambda: BayesianVOIPolicy(seed=seed),
        "gp_ucb": GPUCBPolicy,
        "gp_ts": lambda: GPTSPolicy(seed=seed),
        "gp_ei": NoisyGPEIPolicy,
    }
    if name not in registry:
        raise ValueError(f"Unknown policy {name!r}; expected one of {sorted(registry)}")
    return registry[name]()


@dataclass
class CertificationResult:
    """Structured output returned by :func:`certify_root_action`."""

    certified: bool
    action: int
    steps: int
    total_cost: float
    regret_bound: float
    policy: str
    stopping: str
    posterior_mean: np.ndarray | None = None
    arm_counts: np.ndarray | None = None
    beta: float | None = None
    contrast_rank: int | None = None
    mc_risk_upper: float | None = None


def certify_root_action(
    dag: DAG | Sequence[Sequence[int]],
    observe_fn: Callable[[int], float],
    *,
    kernel: np.ndarray | None = None,
    prior_mean: float = 0.0,
    obs_std: float = 0.1,
    costs: Sequence[float] | np.ndarray | None = None,
    policy: str | AcquisitionPolicy = "cd_joint",
    stopping: Literal[
        "credible_ellipsoid",
        "anytime_frequentist",
        "direct_posterior_risk",
        "distribution_free",
    ] = "credible_ellipsoid",
    epsilon: float = 0.02,
    delta: float = 0.05,
    max_evals: int = 5000,
    rkhs_bound: float = 1.0,
    mc_draws: int = 4096,
    mc_eta: float = 0.01,
    df_schedule: Literal["emp_bernstein", "hoeffding"] = "emp_bernstein",
    seed: int = 0,
) -> CertificationResult:
    """Certify an ``epsilon``-optimal root action on a search DAG in a single function call.

    Parameters
    ----------
    dag:
        A :class:`SearchDAG` (or ``DAG``), or simply a sequence of root-action terminal support
        lists such as ``[[0, 1, 2], [1, 2, 3]]``.
    observe_fn:
        Callable ``observe_fn(terminal_idx) -> float`` returning one noisy evaluation of canonical
        terminal ``terminal_idx in 0..M-1``. For ``stopping="distribution_free"``, observations
        must lie in ``[0, 1]``.
    kernel:
        Optional ``(M, M)`` prior covariance matrix over terminal means. Required for Bayesian /
        fixed-feature stopping modes (defaults to ``0.25 * I_M`` if omitted in Gaussian modes).
    prior_mean, obs_std:
        Prior mean and known observation noise standard deviation for conjugate Gaussian modes.
    costs:
        Optional length-``M`` positive query costs (uniform ``1.0`` by default).
    policy:
        Acquisition policy name (``"cd_joint"``, ``"kg"``, ``"gp_os"``, ``"bayesian_voi"``,
        ``"gp_ucb"``, ``"gp_ts"``, ``"gp_ei"``, or ``"df_os"`` for distribution-free Optimistic
        Separation) or an :class:`AcquisitionPolicy` instance.
    stopping:
        Stopping criterion:
        - ``"credible_ellipsoid"``: rank-calibrated ``sqrt(chi2_{r, 1-delta})`` joint Gaussian
          contrast ellipsoid (exact prior-predictive validity under the specified Gaussian model).
        - ``"anytime_frequentist"``: anytime-valid self-normalized RKHS/linear ellipsoid
          ``B + sqrt(2(gamma_t + log(1/delta)))`` (uniform fixed-parameter validity).
        - ``"direct_posterior_risk"``: anytime union-bound Monte Carlo posterior-risk stopping
          with fresh draws per check (``delta_post = delta - mc_eta``).
        - ``"distribution_free"``: anytime-valid ``[0, 1]``-bounded Empirical Bernstein /
          Hoeffding confidence boxes with exact shared-support root regret (``DualWitnessCovers``).
    epsilon, delta:
        Target suboptimality tolerance and error probability.
    max_evals:
        Maximum number of calls to ``observe_fn``.
    """
    graph = dag if isinstance(dag, DAG) else SearchDAG.from_supports(dag)
    ss = SupportStructure(graph, costs=costs)
    pol_name = policy.name if isinstance(policy, AcquisitionPolicy) else str(policy)

    # Distribution-free [0, 1]-bounded regime (DualWitnessCovers + Optimistic Separation)
    if stopping == "distribution_free":
        df_mon = DualWitnessCovers(
            graph, delta=delta, schedule=df_schedule, layout="best", track_separation=True
        )
        ev = df_mon.evidence
        counts = np.zeros(ss.m, dtype=np.int64)
        total_cost = 0.0
        for step in range(1, max_evals + 1):
            act_df, reg_df, _, _, p_leaf, q_leaf = df_mon.query_optimistic_separation()
            if reg_df <= epsilon:
                return CertificationResult(
                    certified=True,
                    action=int(act_df),
                    steps=step - 1,
                    total_cost=total_cost,
                    regret_bound=float(reg_df),
                    policy="df_os" if pol_name in ("cd_joint", "df_os") else pol_name,
                    stopping=stopping,
                    arm_counts=counts,
                )
            if q_leaf < 0:
                chosen_leaf = p_leaf
            else:
                wp = float(ev.upper[p_leaf] - ev.lower[p_leaf])
                wq = float(ev.upper[q_leaf] - ev.lower[q_leaf])
                chosen_leaf = p_leaf if (wp, -p_leaf) >= (wq, -q_leaf) else q_leaf
            arm_idx = ss.leaf_to_idx[chosen_leaf]
            r = float(observe_fn(arm_idx))
            counts[arm_idx] += 1
            total_cost += float(ss.costs[arm_idx])
            df_mon.step(chosen_leaf, r)

        act_df, reg_df, _, _, _ = df_mon.query_dual_witness()
        return CertificationResult(
            certified=bool(reg_df <= epsilon),
            action=int(act_df),
            steps=max_evals,
            total_cost=total_cost,
            regret_bound=float(reg_df),
            policy="df_os" if pol_name in ("cd_joint", "df_os") else pol_name,
            stopping=stopping,
            arm_counts=counts,
        )

    # Correlated Gaussian / fixed-feature regimes
    k_mat = (0.25 * np.eye(ss.m, dtype=np.float64)) if kernel is None else np.asarray(kernel, dtype=np.float64)
    beta_mode = "anytime_frequentist" if stopping == "anytime_frequentist" else "posterior_credible"
    r_rank = contrast_rank_of_kernel(k_mat)
    post = SharedGaussianPosterior(
        kernel=k_mat,
        prior_mean=prior_mean,
        obs_std=obs_std,
        delta=delta,
        beta_mode=beta_mode,
        rkhs_bound=rkhs_bound,
        contrast_rank=r_rank,
    )
    certifier = JointEllipsoidCertifier(ss, epsilon=epsilon, solver="colgen_lazy", exact_linear_mean=False)
    pol_obj = policy if isinstance(policy, AcquisitionPolicy) else make_policy(pol_name, seed=seed)
    l2a = _build_leaf_to_actions(ss)

    mc_rng = np.random.default_rng((int(seed) * 1000003 + 4219) & 0xFFFFFFFFFFFFFFFF)
    mc_delta_post = max(1e-6, float(delta) - float(mc_eta))
    mc_check_idx = 0
    total_cost = 0.0

    for step in range(1, max_evals + 1):
        t_done = step - 1
        if stopping in ("credible_ellipsoid", "anytime_frequentist"):
            if t_done > 0 and default_check_schedule(t_done):
                b_now = post.beta()
                ok, act_b, reg_b = check_ellipsoid_stopping(
                    certifier, ss, post.mean, post.sigma_mat, b_now, epsilon
                )
                if ok:
                    return CertificationResult(
                        certified=True,
                        action=int(act_b),
                        steps=t_done,
                        total_cost=total_cost,
                        regret_bound=float(reg_b),
                        policy=pol_obj.name,
                        stopping=stopping,
                        posterior_mean=post.mean.copy(),
                        arm_counts=post.arm_counts.copy(),
                        beta=b_now,
                        contrast_rank=r_rank,
                    )
        elif stopping == "direct_posterior_risk":
            if t_done > 0 and mc_postrisk_schedule(t_done, max_evals):
                mc_check_idx += 1
                ok_e, act_e, _, cp_e = eval_direct_posterior_risk_valid(
                    post.mean,
                    post.sigma_mat,
                    ss.supports,
                    epsilon,
                    mc_check_idx,
                    n_mc=mc_draws,
                    eta=mc_eta,
                    delta_post=mc_delta_post,
                    rng=mc_rng,
                )
                if ok_e:
                    return CertificationResult(
                        certified=True,
                        action=int(act_e),
                        steps=t_done,
                        total_cost=total_cost,
                        regret_bound=float(epsilon),
                        policy=pol_obj.name,
                        stopping=stopping,
                        posterior_mean=post.mean.copy(),
                        arm_counts=post.arm_counts.copy(),
                        contrast_rank=r_rank,
                        mc_risk_upper=cp_e,
                    )
        else:
            raise ValueError(f"Unknown stopping rule: {stopping!r}")

        arm = pol_obj.select(
            post, ss, certifier, beta=post.beta(), epsilon=epsilon, step=step, delta=delta, leaf_to_actions=l2a
        )
        r = float(observe_fn(arm))
        post.observe(arm, r)
        total_cost += float(ss.costs[arm])

    # Final check at max_evals
    if stopping == "direct_posterior_risk":
        mc_check_idx += 1
        ok_e, act_e, _, cp_e = eval_direct_posterior_risk_valid(
            post.mean,
            post.sigma_mat,
            ss.supports,
            epsilon,
            mc_check_idx,
            n_mc=mc_draws,
            eta=mc_eta,
            delta_post=mc_delta_post,
            rng=mc_rng,
        )
        emp_a = int(np.argmax([float(np.max(post.mean[sup])) for sup in ss.supports]))
        return CertificationResult(
            certified=ok_e,
            action=int(act_e) if ok_e else emp_a,
            steps=max_evals,
            total_cost=total_cost,
            regret_bound=float(epsilon) if ok_e else math.inf,
            policy=pol_obj.name,
            stopping=stopping,
            posterior_mean=post.mean.copy(),
            arm_counts=post.arm_counts.copy(),
            contrast_rank=r_rank,
            mc_risk_upper=cp_e,
        )

    b_end = post.beta()
    ok, act_b, reg_b = check_ellipsoid_stopping(certifier, ss, post.mean, post.sigma_mat, b_end, epsilon)
    emp_a = int(np.argmax([float(np.max(post.mean[sup])) for sup in ss.supports]))
    return CertificationResult(
        certified=ok,
        action=int(act_b) if ok else emp_a,
        steps=max_evals,
        total_cost=total_cost,
        regret_bound=float(reg_b),
        policy=pol_obj.name,
        stopping=stopping,
        posterior_mean=post.mean.copy(),
        arm_counts=post.arm_counts.copy(),
        beta=b_end,
        contrast_rank=r_rank,
    )


__all__ = [
    "ALL_V12_POLICIES",
    "AcquisitionPolicy",
    "BayesianVOIPolicy",
    "CDJointPolicy",
    "CertificationResult",
    "CorrelatedKGPolicy",
    "GAUSS_HERMITE_9_NODES",
    "GAUSS_HERMITE_9_WEIGHTS",
    "GPOSPolicy",
    "GPTSPolicy",
    "GPUCBPolicy",
    "MACDJointPolicy",
    "MACDJointSafePolicy",
    "MarginAwareSelection",
    "MatchedModelBEDSession",
    "NoisyGPEIPolicy",
    "build_query_shortlist",
    "build_witness_pool",
    "certify_root_action",
    "compute_exact_standardized_margin",
    "compute_mechanistic_snapshot",
    "correlated_kg_log_scores",
    "default_check_schedule",
    "exact_correlated_kg_single",
    "log_expected_pos_normal",
    "make_policy",
    "noisy_gp_ei_log_scores",
    "select_bayesian_root_voi",
    "select_gp_arm_with_beta",
    "select_margin_aware_query",
]
