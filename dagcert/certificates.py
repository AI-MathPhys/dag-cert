"""Exact rectangular and ellipsoidal Joint Root Certification solvers."""
from __future__ import annotations

from collections.abc import Sequence
import math

import numpy as np

from dagcert._core.graph import DAG
from dagcert._core.retired_bounds import CanonicalIntervals, RetiredBounds
from dagcert._core.v2_monitors import (
    ChargedDualCovers,
    DirectGraphRegretMonitor,
    FactorizedRegretMonitor,
    MarginalGraphMonitor,
    NestedDyadicCovers,
    NestedIntervals,
    SelectiveDAGBounds,
    brute_force_exact_regret,
    brute_force_marginal,
)
from dagcert._core.v5_hybrid_and_os import DualWitnessCovers
from dagcert._core.v6_bayesian_opt import solve_ellipsoid_challenger
from dagcert._core.v7_bayesian_ucd import (
    ActionCertificate,
    ChallengerResult,
    CharacteristicRateResult,
    HullDominanceReport,
    JointEllipsoidCertifier,
    SupportStructure,
    caratheodory_prune,
    compute_hull_discrepancy,
    solve_alt_projection_dual,
    solve_feature_challenger_colgen,
    solve_feature_challenger_cvxpy,
    solve_feature_challenger_dense_afw,
    solve_primal_ellipsoid_regret,
)
from dagcert._core.v8_unified_experiments import (
    RobustAwareJointCertifier,
    ScheduledConicCertifier,
)


def exact_rectangular_regret(
    supports: Sequence[Sequence[int]] | SupportStructure | DAG,
    lower: Sequence[float] | np.ndarray,
    upper: Sequence[float] | np.ndarray,
) -> tuple[int, float, np.ndarray]:
    """Compute exact shared-support rectangular root regret (Theorem 2.2 / Eq. 5).

    For each root action ``a`` with reachable support ``S(a)`` and complement ``B_a = Z \\ S(a)``:

        R_t(a) = max(0, max_{z in B_a} u_t(z) - max_{y in S(a)} l_t(y))

    (and ``R_t(a) = 0`` when ``B_a`` is empty). Shared terminals cancel automatically because
    one common environment cannot simultaneously help a rival and harm ``a``.

    Returns
    -------
    best_action : int
        Root action minimizing exact worst-case regret (smallest index on ties).
    min_regret : float
        Minimum exact worst-case regret ``min_a R_t(a)``.
    regrets : np.ndarray
        Length-``K`` array of exact worst-case regrets for every root action.
    """
    lo = np.asarray(lower, dtype=np.float64)
    hi = np.asarray(upper, dtype=np.float64)
    if lo.shape != hi.shape or lo.ndim != 1:
        raise ValueError("lower and upper must be 1-D arrays of equal length M")
    m = len(lo)

    if isinstance(supports, DAG):
        supports = SupportStructure(supports)
    if isinstance(supports, SupportStructure):
        sup_list = supports.supports
        comp_list = supports.complements
    else:
        all_idx = np.arange(m, dtype=np.int64)
        sup_list = tuple(np.asarray(sorted(set(int(i) for i in s)), dtype=np.int64) for s in supports)
        comp_list = tuple(np.setdiff1d(all_idx, s, assume_unique=True) for s in sup_list)

    regrets = np.empty(len(sup_list), dtype=np.float64)
    for a, (sup, comp) in enumerate(zip(sup_list, comp_list)):
        if len(comp) == 0:
            regrets[a] = 0.0
        else:
            regrets[a] = max(0.0, float(np.max(hi[comp])) - float(np.max(lo[sup])))
    best_a = int(np.argmin(regrets))
    return best_a, float(regrets[best_a]), regrets


def check_ellipsoid_stopping(
    certifier: JointEllipsoidCertifier,
    supports: SupportStructure,
    means: np.ndarray,
    sigma_mat: np.ndarray,
    beta: float,
    epsilon: float,
    stds: np.ndarray | None = None,
) -> tuple[bool, int, float]:
    """Exact, sound joint-ellipsoid stopping check ``min_a R_t(a) <= epsilon``.

    Uses a 100%-sound center-mean lower-bound filter (``m_t in E_t`` implies
    ``max_{z notin S(a)} m_z - max_{y in S(a)} m_y <= R_t(a)``), then verifies surviving
    candidate actions via ``JointEllipsoidCertifier.certify_action_gp``.
    """
    if stds is None:
        stds = np.sqrt(np.maximum(1e-18, np.diag(sigma_mat)))
    u_ell = means + beta * stds
    cands: list[tuple[float, int]] = []
    for a in range(supports.k):
        sup = supports.supports[a]
        comp = supports.complements[a]
        if len(comp) == 0:
            return True, a, 0.0
        m_in = float(np.max(means[sup]))
        m_out = float(np.max(means[comp]))
        if m_out - m_in > epsilon:
            continue
        cands.append((max(0.0, float(np.max(u_ell[comp])) - m_in), a))

    if not cands:
        best_emp = int(np.argmax([float(np.max(means[sup])) for sup in supports.supports]))
        return False, best_emp, math.inf

    cands.sort(key=lambda pair: (pair[0], pair[1]))
    best_a = cands[0][1]
    best_reg = math.inf
    prev_eps = certifier.epsilon
    certifier.epsilon = float(epsilon)
    try:
        for _, a in cands:
            ca = certifier.certify_action_gp(
                action=a,
                means=means,
                sigma_mat=sigma_mat,
                beta=beta,
                stop_if_above_eps=True,
            )
            if ca.regret <= epsilon:
                return True, int(a), float(ca.regret)
            if (ca.regret, a) < (best_reg, best_a):
                best_reg = float(ca.regret)
                best_a = int(a)
    finally:
        certifier.epsilon = prev_eps
    return False, int(best_a), float(best_reg)


__all__ = [
    "ActionCertificate",
    "CanonicalIntervals",
    "ChallengerResult",
    "CharacteristicRateResult",
    "ChargedDualCovers",
    "DirectGraphRegretMonitor",
    "DualWitnessCovers",
    "FactorizedRegretMonitor",
    "HullDominanceReport",
    "JointEllipsoidCertifier",
    "MarginalGraphMonitor",
    "NestedDyadicCovers",
    "NestedIntervals",
    "RetiredBounds",
    "RobustAwareJointCertifier",
    "ScheduledConicCertifier",
    "SelectiveDAGBounds",
    "brute_force_exact_regret",
    "brute_force_marginal",
    "caratheodory_prune",
    "check_ellipsoid_stopping",
    "compute_hull_discrepancy",
    "exact_rectangular_regret",
    "solve_alt_projection_dual",
    "solve_ellipsoid_challenger",
    "solve_feature_challenger_colgen",
    "solve_feature_challenger_cvxpy",
    "solve_feature_challenger_dense_afw",
    "solve_primal_ellipsoid_regret",
]
