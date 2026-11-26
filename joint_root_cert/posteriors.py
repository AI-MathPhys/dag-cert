"""Gaussian posteriors, contrast-rank credible radii, coverage diagnostics, and direct posterior risk."""
from __future__ import annotations

from collections.abc import Sequence
import math

import numpy as np
from scipy.linalg import cho_factor, cho_solve
from scipy.stats import beta as beta_dist, chi2

from joint_root_cert._core.v6_bayesian_opt import DiscreteGPSurrogate
from joint_root_cert._core.v7_bayesian_ucd import DiscreteGPPosteriorModel, LinearFeatureModel
from joint_root_cert._core.v8_unified_experiments import CalibratedGPPosteriorModel
from joint_root_cert._core.v12_bed_acquisition import (
    SharedGaussianPosterior,
    clopper_pearson_upper,
    estimate_posterior_root_risks,
)


def contrast_rank_of_kernel(kernel: np.ndarray) -> int:
    """Exact rank ``r = rank(H K H)`` on the contrast subspace ``{1}^perp``.

    Here ``H = I_M - 1 1^T / M`` projects terminal vectors onto pairwise contrasts. For a
    strictly positive-definite ``M x M`` kernel (such as a sequence kernel with positive
    nugget), ``r = M - 1``. For a fixed-feature kernel ``K = Phi Phi^T`` of rank ``d``,
    ``r <= min(d, M - 1)``.
    """
    k_arr = np.asarray(kernel, dtype=np.float64)
    m = int(k_arr.shape[0])
    h_mat = np.eye(m, dtype=np.float64) - np.ones((m, m), dtype=np.float64) / float(m)
    kc = h_mat @ k_arr @ h_mat
    eigs = np.linalg.eigvalsh(0.5 * (kc + kc.T))
    tol = max(1e-12, 1e-10 * float(np.max(np.abs(eigs))))
    return max(1, int(np.sum(eigs > tol)))


def chi2_credible_beta(contrast_rank: int, level: float = 0.95) -> float:
    """Exact joint Gaussian credible-ellipsoid radius ``sqrt(chi2_{r, level})``.

    No ``t^2`` time correction is required for posterior-credible stopping under a correctly
    specified Bayesian model, because posterior conditioning already accounts for adaptive
    stopping (Appendix C.1).
    """
    return math.sqrt(float(chi2.ppf(float(level), df=int(contrast_rank))))


def nominal_gp_beta(m: int, step: int, delta: float = 0.05) -> float:
    """Nominal simultaneous Gaussian union-bound radius ``sqrt(2 log(4 M t^2 / delta))``.

    Included for reproducing the nominal-radius stopping controls in Section 3.2 / Appendix H.
    Note that this radius is *not* a rank-calibrated ``1 - delta`` joint credible ellipsoid.
    """
    t_eff = max(1, int(step))
    return math.sqrt(2.0 * math.log(4.0 * float(m) * float(t_eff * t_eff) / float(delta)))


def contrast_ellipsoid_coverage(
    means: np.ndarray,
    sigma_mat: np.ndarray,
    beta: float,
    true_means: np.ndarray,
) -> tuple[bool, float]:
    """Exact check of whether ``H (true_means - means)`` lies in the projected ``beta``-ellipsoid.

    Computes the shift-invariant contrast Mahalanobis distance

        Q_contrast(d) = min_{c in R} (d - c 1)^T Sigma^{-1} (d - c 1)
                      = d^T Sigma^{-1} d - (1^T Sigma^{-1} d)^2 / (1^T Sigma^{-1} 1).

    Returns ``(covered, sqrt(Q_contrast))``. Because root regret is shift-invariant,
    ``Q_contrast <= beta^2`` is necessary and sufficient for ``true_means - c*1`` to lie inside
    the joint ellipsoid for some scalar shift ``c``, deterministically guaranteeing
    ``true_regret(a) <= R_t(a)`` simultaneously for every root action ``a``.
    """
    d = np.asarray(true_means, dtype=np.float64) - np.asarray(means, dtype=np.float64)
    m = len(d)
    sym = 0.5 * (sigma_mat + sigma_mat.T)
    jit = 1e-13 * max(1.0, float(np.max(np.diag(sym))))
    c_fac, low = cho_factor(sym + jit * np.eye(m, dtype=np.float64))
    ones = np.ones(m, dtype=np.float64)
    sol = cho_solve((c_fac, low), np.column_stack([d, ones]))
    x_d = sol[:, 0]
    x_1 = sol[:, 1]
    quad_d = float(d @ x_d)
    one_d = float(ones @ x_d)
    one_1 = max(1e-18, float(ones @ x_1))
    q_contrast = max(0.0, quad_d - (one_d * one_d) / one_1)
    dist = math.sqrt(q_contrast)
    return bool(dist <= float(beta) + 1e-9), dist


def pointwise_coverage_diag(
    means: np.ndarray,
    stds: np.ndarray,
    beta: float,
    true_means: np.ndarray,
) -> tuple[bool, float, float]:
    """Check simultaneous pointwise terminal-wise coverage ``|m_z - mu*_z| <= beta * std_z``."""
    z_ratios = np.abs(np.asarray(means) - np.asarray(true_means)) / np.maximum(1e-12, float(beta) * np.asarray(stds))
    max_z = float(np.max(z_ratios))
    frac = float(np.mean(z_ratios <= 1.0 + 1e-12))
    return bool(max_z <= 1.0 + 1e-12), max_z, frac


def cp_upper_exact(k_fail: int, n_trials: int, alpha: float) -> float:
    """Exact one-sided ``(1 - alpha)`` Clopper-Pearson upper confidence bound."""
    if n_trials <= 0 or k_fail >= n_trials:
        return 1.0
    return float(beta_dist.ppf(1.0 - float(alpha), int(k_fail) + 1, int(n_trials) - int(k_fail)))


def mc_postrisk_schedule(t_done: int, cap: int) -> bool:
    """Deterministic check schedule for direct posterior-risk stopping."""
    if t_done == cap:
        return True
    if t_done <= 0:
        return False
    if t_done <= 500:
        return (t_done % 10) == 0
    if t_done <= 2000:
        return (t_done % 25) == 0
    return (t_done % 100) == 0


def eval_direct_posterior_risk_valid(
    means: np.ndarray,
    sigma_mat: np.ndarray,
    supports: Sequence[np.ndarray],
    eps: float,
    check_idx: int,
    n_mc: int = 4096,
    eta: float = 0.01,
    delta_post: float = 0.04,
    rng: np.random.Generator | None = None,
) -> tuple[bool, int, float, float]:
    """Valid anytime union-bound Monte Carlo direct posterior-risk test (Appendix C.1.1 / G.1.1).

    Draws ``n_mc`` fresh conditionally independent Gaussian samples from ``N(means, sigma_mat)``,
    allocates auxiliary MC error budget ``eta_{j,a} = eta / (K * j * (j + 1))`` at check index
    ``j >= 1``, and stops iff ``min_a CP_{1 - eta_{j,a}}(k_fail(a), n_mc) <= delta_post``.
    Under a correctly specified prior and likelihood, a union bound over all checks ``j >= 1``
    and root actions ``a`` controls total prior-predictive error by ``delta_post + eta``.

    Returns ``(certified, best_action, empirical_risk_hat, cp_upper_bound)``.
    """
    if rng is None:
        rng = np.random.default_rng()
    m = len(means)
    k_act = len(supports)
    sym = 0.5 * (sigma_mat + sigma_mat.T)
    jit = 1e-13 * max(1.0, float(np.max(np.diag(sym))))
    chol = np.linalg.cholesky(sym + jit * np.eye(m, dtype=np.float64))
    z = rng.standard_normal((m, int(n_mc)))
    draws = means[:, None] + (chol @ z)
    v_star = np.max(draws, axis=0)

    eta_ja = float(eta) / (float(k_act) * float(check_idx) * float(check_idx + 1))
    best_a = 0
    best_cp = 1.0
    best_q = 1.0
    for a, sup in enumerate(supports):
        v_a = np.max(draws[sup, :], axis=0)
        k_fail = int(np.sum((v_star - v_a) > (float(eps) + 1e-12)))
        cp_hi = cp_upper_exact(k_fail, int(n_mc), eta_ja)
        if cp_hi < best_cp or (cp_hi == best_cp and a < best_a):
            best_cp = cp_hi
            best_q = k_fail / float(n_mc)
            best_a = a
    return bool(best_cp <= float(delta_post)), int(best_a), float(best_q), float(best_cp)


__all__ = [
    "CalibratedGPPosteriorModel",
    "DiscreteGPPosteriorModel",
    "DiscreteGPSurrogate",
    "LinearFeatureModel",
    "SharedGaussianPosterior",
    "chi2_credible_beta",
    "clopper_pearson_upper",
    "contrast_ellipsoid_coverage",
    "contrast_rank_of_kernel",
    "cp_upper_exact",
    "estimate_posterior_root_risks",
    "eval_direct_posterior_risk_valid",
    "mc_postrisk_schedule",
    "nominal_gp_beta",
    "pointwise_coverage_diag",
]
