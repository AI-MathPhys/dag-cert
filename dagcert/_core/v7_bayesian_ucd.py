"""v7 Correlation-Aware Bayesian and Frequentist Certification over Overlapping Decision Supports.

Implements the modular five-component architecture for correlation-aware certification in
finite all-MAX search DAGs:
1. Support & Cost Structure (`SupportStructure`):
   Reachability sets `S(a)`, complements `Z \\ S(a)`, overlap metrics, and evaluation costs `c(x)`.
2. Exact Conic & Geometric Oracles (Theory Programs T1 & T2):
   - `caratheodory_prune`: Exact rank-nullspace reduction maintaining `|supp(p)| <= d + 1`.
   - `solve_feature_challenger_colgen`: Simplicial column-generation / active-set solver in `R^d`.
   - `solve_feature_challenger_dense_afw`: Dense away-step Frank-Wolfe baseline on `Delta(S)`.
   - `solve_feature_challenger_cvxpy`: Reference interior-point SOCP solver via `cvxpy`.
   - `solve_primal_ellipsoid_regret`: Multi-start SLSQP + dense grid primal verifier on `Theta_t`.
   - `compute_hull_discrepancy`: Exact and approximate feature-polytope dominance (`P_Z subseteq P_a`).
3. Valid Sequential Statistical Models (Theory Program T3):
   - `LinearFeatureModel` (Track A): Exact `O(d^2)` Sherman-Morrison RLS, Abbasi-Yadkori frequentist
     confidence ellipsoids, misspecification-valid capped-weight RLS ellipsoids (`|b_z| <= xi`),
     and Gaussian linear posteriors.
   - `DiscreteGPPosteriorModel` (Track B): Exact discrete-domain GP posterior `N(m_t, Sigma_t)` with
     Woodbury updates, RKHS frequentist ellipsoids, nominal Gaussian ellipsoids, and Monte Carlo
     posterior acceptable-action probabilities `q_t(a) = Pr(V*(f) - V(a; f) <= eps | D_t)`.
4. Correlation-Aware Active Experiment Selection (Theory Program T4):
   - `contrast_directed`: Safeguarded Contrast-Directed Certification (`Delta_t(g_t; x) / c(x)`).
   - `contrast_naive`: Unsafeguarded pure dual-contrast baseline (demonstrating suboptimal-witness stall).
   - `multi_contrast`: Urgency-weighted Multi-Contrast Design across candidate commitments and threats.
   - `bayes_ids`: Symmetric-MI Information-Directed Acquisition `I(Y_x; A_eps(f) | D_t) / c(x)`.
   - `direct_witness`: Witness-only restriction (`x in {y_t, z_t}`) isolating off-witness proxy gains.
   - `gp_ucb` / `gp_root_info`: Conventional BO and independent-witness baselines.
5. Information-Theoretic Complexity & Tracking (Theory Program T5):
   - `solve_alt_projection_dual`: Exact Lagrangian dual of quadratic projection onto `H_eps(z, S(a))`.
   - `compute_characteristic_rate`: Variational saddle-point solver for `I_c*(a; theta*)` and
     multiple-answer optimal commitment `max_{a in A_eps(theta*)} I_c*(a; theta*)`.
   - `maxmin_tracking`: Online plug-in saddle-point tracking allocation.
"""
from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
import logging
import math
import time

import numpy as np
from scipy.linalg import cho_solve, solve_triangular
from scipy.optimize import minimize

from .graph import DAG, Problem
from .v5_hybrid_and_os import DualWitnessCovers
from .v6_bayesian_opt import solve_ellipsoid_challenger


_LOGGER = logging.getLogger(__name__)


@dataclass(frozen=True, kw_only=True)
class ChallengerResult:
    """Primal-dual solution for a single outside challenger `D_t(z, S(a))`."""

    dual_value: float
    duality_gap: float
    weights: np.ndarray
    support_indices: np.ndarray
    contrast: np.ndarray
    iterations: int


@dataclass(frozen=True, kw_only=True)
class ActionCertificate:
    """Worst-case regret certificate and witness metadata for one root action."""

    action: int
    regret: float
    challenger_idx: int
    inside_indices: np.ndarray
    inside_weights: np.ndarray
    contrast: np.ndarray
    max_duality_gap: float
    evaluated_challengers: int
    total_challengers: int


@dataclass(frozen=True, kw_only=True)
class HullDominanceReport:
    """Feature-polytope dominance summary for a root action `a` (Theory Program T2)."""

    action: int
    support_size: int
    outside_size: int
    max_hull_dist_l2: float
    mean_hull_dist_l2: float
    dominated_outside_count: int
    zero_sample_exact: bool


@dataclass(frozen=True, kw_only=True)
class CharacteristicRateResult:
    """Information-theoretic rate `I_c*(a; theta*)` and optimal design `w*` (Theory Program T5)."""

    target_action: int
    rate: float
    characteristic_time_kl1: float
    optimal_weights: np.ndarray
    acceptable_actions: tuple[int, ...]
    per_action_rates: tuple[float, ...]


class SupportStructure:
    """Precomputed terminal reachability supports, complements, and evaluation costs for a DAG."""

    def __init__(self, graph: DAG, costs: MappingOrArray | None = None) -> None:
        self.graph = graph
        self.leaves: tuple[int, ...] = tuple(graph.leaves)
        self.m = len(self.leaves)
        self.leaf_to_idx: dict[int, int] = {z: i for i, z in enumerate(self.leaves)}

        reach: list[set[int]] = [set() for _ in range(len(graph))]
        for v in reversed(graph.order):
            ch = graph.children[v]
            if not ch:
                reach[v].add(v)
            else:
                for c in ch:
                    reach[v].update(reach[c])

        root_ch = graph.children[graph.root]
        self.k = len(root_ch)
        all_idx = set(range(self.m))
        supports: list[np.ndarray] = []
        complements: list[np.ndarray] = []
        support_sets: list[set[int]] = []
        for c in root_ch:
            sup_set = {self.leaf_to_idx[z] for z in reach[c]}
            sup_arr = np.array(sorted(sup_set), dtype=np.int64)
            comp_arr = np.array(sorted(all_idx - sup_set), dtype=np.int64)
            supports.append(sup_arr)
            complements.append(comp_arr)
            support_sets.append(sup_set)

        self.supports: tuple[np.ndarray, ...] = tuple(supports)
        self.complements: tuple[np.ndarray, ...] = tuple(complements)

        if costs is None:
            self.costs = np.ones(self.m, dtype=np.float64)
        elif isinstance(costs, dict):
            self.costs = np.array([float(costs[z]) for z in self.leaves], dtype=np.float64)
        else:
            arr = np.asarray(costs, dtype=np.float64)
            if arr.shape != (self.m,):
                raise ValueError(f"Expected costs shape {(self.m,)}, got {arr.shape}")
            self.costs = arr.copy()
        if np.any(self.costs <= 0.0):
            raise ValueError("Terminal evaluation costs must be strictly positive.")

        jaccards: list[float] = []
        containments = 0
        for i in range(self.k):
            for j in range(self.k):
                if i == j:
                    continue
                if support_sets[i].issubset(support_sets[j]):
                    containments += 1
                if i < j:
                    union_sz = len(support_sets[i] | support_sets[j])
                    inter_sz = len(support_sets[i] & support_sets[j])
                    jaccards.append(inter_sz / max(1, union_sz))
        self.mean_pairwise_jaccard = float(np.mean(jaccards)) if jaccards else 0.0
        self.containment_pairs = containments


MappingOrArray = dict[int, float] | Sequence[float] | np.ndarray


def caratheodory_prune(
    features_w: np.ndarray,
    means_w: np.ndarray,
    weights_w: np.ndarray,
    indices_w: np.ndarray,
    exact_linear_mean: bool = True,
    tol: float = 1e-13,
) -> tuple[np.ndarray, np.ndarray]:
    """Reduce active simplex support `(indices_w, weights_w)` to at most `d + 1` vertices
    (or `d + 2` when `means_w` is not an affine function of `features_w`) without changing
    `features_w^T weights_w` or `means_w^T weights_w`.
    """
    keep = weights_w > tol
    idx = indices_w[keep].copy()
    w = weights_w[keep].copy()
    if len(w) == 0:
        return indices_w[:1].copy(), np.ones(1, dtype=np.float64)
    w /= float(np.sum(w))

    d = int(features_w.shape[1])
    target_max = d + 1 if exact_linear_mean else d + 2

    while len(w) > target_max:
        sub_f = features_w[idx]  # (k, d)
        if exact_linear_mean:
            # Homogeneous constraints: [1^T; sub_f^T] delta = 0, shape (d + 1, k)
            mat = np.vstack([np.ones((1, len(w)), dtype=np.float64), sub_f.T])
        else:
            sub_m = means_w[idx]
            mat = np.vstack([np.ones((1, len(w)), dtype=np.float64), sub_m[None, :], sub_f.T])

        _, svals, vt = np.linalg.svd(mat, full_matrices=True)
        # Last row of V^T lies in the right nullspace because cols k > rows.
        rank = int(np.sum(svals > 1e-12 * max(1.0, float(svals[0]))))
        if rank >= len(w):
            break
        delta = vt[-1].copy()
        if np.max(delta) <= 1e-14:
            delta = -delta
        pos = delta > 1e-14
        if not np.any(pos):
            break
        ratios = w[pos] / delta[pos]
        alpha = float(np.min(ratios))
        w = np.maximum(0.0, w - alpha * delta)
        nz = w > tol
        if int(np.sum(nz)) == len(w):
            # Force drop of the tightest index
            pos_indices = np.flatnonzero(pos)
            drop_local = int(pos_indices[int(np.argmin(ratios))])
            nz[drop_local] = False
        idx = idx[nz]
        w = w[nz]
        w /= float(np.sum(w))

    return idx, w


def _solve_small_simplex_afw(
    m_z: float,
    m_w: np.ndarray,
    psi_z: np.ndarray,
    psi_w: np.ndarray,
    beta: float,
    init_p: np.ndarray,
    tol: float = 1e-6,
    max_iter: int = 45,
) -> tuple[np.ndarray, float, float, int]:
    """High-accuracy solver on a small active simplex `W` (`|W| <= d + 2`) in `R^d`.

    Combines Pairwise/Away-Step Frank-Wolfe with exact 1D Newton line search and a smooth
    active-set SLSQP polish when needed (handling non-smooth cone tips `psi_z in conv(psi_w)`
    to `< 1e-10` precision in microseconds).
    """
    k = len(m_w)
    if k == 1:
        diff = psi_z - psi_w[0]
        q = float(np.linalg.norm(diff))
        val = (m_z - float(m_w[0])) + beta * q
        return np.ones(1, dtype=np.float64), val, 0.0, 1

    p = np.maximum(0.0, init_p.copy())
    s_p = float(np.sum(p))
    if s_p <= 0.0:
        p = np.zeros(k, dtype=np.float64)
        p[0] = 1.0
    else:
        p /= s_p

    best_val = math.inf
    best_p = p.copy()
    best_gap = math.inf
    iters = 0

    for it in range(1, max_iter + 1):
        iters = it
        bar_psi = p @ psi_w
        u = psi_z - bar_psi
        quad0 = float(u @ u)
        q = math.sqrt(quad0) if quad0 > 0.0 else 0.0
        lin_term = m_z - float(p @ m_w)
        val = lin_term + beta * q
        if val < best_val:
            best_val = val
            best_p = p.copy()

        if q <= 1e-12:
            if val <= 0.0 or float(np.max(m_w) - np.min(m_w)) <= 1e-14:
                return best_p, best_val, 0.0, iters
            break

        grad = -m_w - (beta / q) * (psi_w @ u)
        fw_idx = int(np.argmin(grad))
        gp = float(grad @ p)
        fw_gap = gp - float(grad[fw_idx])
        if fw_gap < best_gap:
            best_gap = fw_gap
        if fw_gap <= tol:
            return best_p, best_val, max(0.0, fw_gap), iters

        # Avoid np.flatnonzero overhead on small k
        mask_act = p > 1e-14
        n_act = int(np.count_nonzero(mask_act))
        away_idx = int(np.argmax(np.where(mask_act, grad, -math.inf)))

        # Pairwise Frank-Wolfe direction moves mass directly from worst active vertex to best vertex
        if fw_idx != away_idx and n_act > 1:
            alpha_max = float(p[away_idx])
            a1 = float(m_w[away_idx] - m_w[fw_idx])
            d_psi = psi_w[fw_idx] - psi_w[away_idx]
            is_pw = True
        else:
            alpha_max = 1.0
            a1 = float(p @ m_w) - float(m_w[fw_idx])
            d_psi = psi_w[fw_idx] - bar_psi
            is_pw = False

        b1 = -2.0 * float(u @ d_psi)
        c2 = float(d_psi @ d_psi)

        q_hi = math.sqrt(max(1e-26, quad0 + b1 * alpha_max + c2 * alpha_max * alpha_max))
        deriv_hi = a1 + beta * (0.5 * b1 + c2 * alpha_max) / q_hi
        if deriv_hi <= 0.0:
            alpha = alpha_max
        else:
            lo_a, hi_a = 0.0, alpha_max
            alpha = 0.5 * alpha_max
            for _ in range(12):
                qa = math.sqrt(max(1e-26, quad0 + b1 * alpha + c2 * alpha * alpha))
                da = a1 + beta * (0.5 * b1 + c2 * alpha) / qa
                if abs(da) <= 1e-11:
                    break
                if da < 0.0:
                    lo_a = alpha
                else:
                    hi_a = alpha
                d2a = beta * max(0.0, c2 * quad0 - 0.25 * b1 * b1) / (qa * qa * qa)
                if d2a > 1e-16:
                    cand = alpha - da / d2a
                    alpha = cand if (lo_a < cand < hi_a) else 0.5 * (lo_a + hi_a)
                else:
                    alpha = 0.5 * (lo_a + hi_a)

        if is_pw:
            p[fw_idx] += alpha
            p[away_idx] = max(0.0, p[away_idx] - alpha)
        else:
            p *= (1.0 - alpha)
            p[fw_idx] += alpha
        p /= float(p.sum())

    # Only invoke SLSQP polish if PFW did not converge tightly (e.g., near a non-smooth cone tip q -> 0)
    if best_gap <= max(tol, 1e-5):
        return best_p, best_val, max(0.0, best_gap), iters

    cur_u = psi_z - (best_p @ psi_w)
    if float(np.linalg.norm(cur_u)) < 0.12:
        res_q = minimize(
            lambda x: 0.5 * float(np.sum((psi_z - (x @ psi_w)) ** 2)),
            best_p,
            jac=lambda x: -(psi_w @ (psi_z - (x @ psi_w))),
            method="SLSQP",
            bounds=[(0.0, 1.0)] * k,
            constraints={"type": "eq", "fun": lambda x: float(np.sum(x)) - 1.0, "jac": lambda _: np.ones(k)},
            options={"ftol": 1e-14, "maxiter": 40},
        )
        if res_q.success:
            p_q = np.maximum(0.0, res_q.x)
            if float(np.sum(p_q)) > 0.0:
                p_q /= float(np.sum(p_q))
                u_q = psi_z - (p_q @ psi_w)
                q_q = float(np.linalg.norm(u_q))
                val_q = (m_z - float(p_q @ m_w)) + beta * q_q
                if val_q < best_val:
                    best_val = val_q
                    best_p = p_q
                    if q_q <= 1e-9:
                        return best_p, best_val, 0.0, iters + int(res_q.nit)

    if best_gap > 1e-4:
        def smooth_obj(p_v: np.ndarray) -> tuple[float, np.ndarray]:
            u_v = psi_z - (p_v @ psi_w)
            q_s = math.sqrt(float(u_v @ u_v) + 1e-18)
            f_v = (m_z - float(p_v @ m_w)) + beta * q_s
            g_v = -m_w - (beta / q_s) * (psi_w @ u_v)
            return f_v, g_v

        res = minimize(
            lambda x: smooth_obj(x)[0],
            best_p,
            jac=lambda x: smooth_obj(x)[1],
            method="SLSQP",
            bounds=[(0.0, 1.0)] * k,
            constraints={"type": "eq", "fun": lambda x: float(np.sum(x)) - 1.0, "jac": lambda _: np.ones(k)},
            options={"ftol": 1e-12, "maxiter": 40},
        )
        if res.success:
            p_pol = np.maximum(0.0, res.x)
            s_pol = float(np.sum(p_pol))
            if s_pol > 0.0:
                p_pol /= s_pol
                u_pol = psi_z - (p_pol @ psi_w)
                q_pol = float(np.linalg.norm(u_pol))
                val_pol = (m_z - float(p_pol @ m_w)) + beta * q_pol
                if val_pol <= best_val:
                    best_val = val_pol
                    best_p = p_pol
                    if q_pol <= 1e-9:
                        best_gap = 0.0
                    else:
                        gr = -m_w - (beta / q_pol) * (psi_w @ u_pol)
                        best_gap = max(0.0, float(gr @ best_p) - float(np.min(gr)))
            iters += int(res.nit)

    return best_p, best_val, max(0.0, best_gap), iters


def solve_feature_challenger_colgen(
    z_idx: int,
    sup: np.ndarray,
    means: np.ndarray,
    psi: np.ndarray,
    raw_features: np.ndarray,
    beta: float,
    exact_linear_mean: bool = True,
    warm_indices: np.ndarray | None = None,
    warm_weights: np.ndarray | None = None,
    tol: float = 1e-6,
    max_outer: int = 24,
) -> ChallengerResult:
    """Simplicial Column-Generation + Caratheodory Active-Set solver (Theory Program T1.3).

    Minimizes over `p in Delta(S)`:
        `(means[z] - p^T means[S]) + beta * ||psi[z] - psi[S]^T p||_2`
    where `psi = Phi @ chol(V_t^{-1})` has dimension `(M, d)`.
    Maintains an active subset `W subseteq S` of cardinality `<= d + 1` via rank-nullspace
    Caratheodory pruning, pricing over all `y in S` with a single `O(|S| d)` matrix-vector product.
    """
    m_z = float(means[z_idx])
    psi_z = psi[z_idx]
    phi_z = raw_features[z_idx]

    if len(sup) == 1:
        y0 = int(sup[0])
        q = float(np.linalg.norm(psi_z - psi[y0]))
        val = (m_z - float(means[y0])) + beta * q
        return ChallengerResult(
            dual_value=val,
            duality_gap=0.0,
            weights=np.ones(1, dtype=np.float64),
            support_indices=sup.copy(),
            contrast=phi_z - raw_features[y0],
            iterations=1,
        )

    m_sup = means[sup]
    psi_sup = psi[sup]  # (|S|, d)

    # Initialize active working set (either warm-started or best vertex in S)
    if warm_indices is not None and warm_weights is not None and len(warm_indices) > 0:
        w_idx = warm_indices.copy()
        w_p = warm_weights.copy()
        w_p /= float(np.sum(w_p))
    else:
        diffs = psi_z[None, :] - psi_sup
        q_verts = np.linalg.norm(diffs, axis=1)
        v_scores = (m_z - m_sup) + beta * q_verts
        best_local = int(np.argmin(v_scores))
        w_idx = np.array([int(sup[best_local])], dtype=np.int64)
        w_p = np.ones(1, dtype=np.float64)

    total_iters = 0
    full_gap = math.inf
    dual_val = math.inf

    for _ in range(max_outer):
        w_p, dual_val, _, inner_it = _solve_small_simplex_afw(
            m_z=m_z,
            m_w=means[w_idx],
            psi_z=psi_z,
            psi_w=psi[w_idx],
            beta=beta,
            init_p=w_p,
            tol=0.5 * tol,
            max_iter=36,
        )
        total_iters += inner_it

        w_idx, w_p = caratheodory_prune(
            features_w=raw_features,
            means_w=means,
            weights_w=w_p,
            indices_w=w_idx,
            exact_linear_mean=exact_linear_mean,
        )

        bar_psi = w_p @ psi[w_idx]
        u = psi_z - bar_psi
        q = float(np.linalg.norm(u))
        dual_val = (m_z - float(w_p @ means[w_idx])) + beta * q

        if q <= 1e-11:
            if dual_val <= 0.0 or np.allclose(m_sup, m_sup[0], atol=1e-14):
                full_gap = 0.0
                break
            # Near cone tip q == 0 with non-constant means: pick unincluded inside arm with highest mean
            rem_mask = np.ones(len(sup), dtype=bool)
            active_set = set(w_idx.tolist())
            for loc_i, lf in enumerate(sup):
                if int(lf) in active_set:
                    rem_mask[loc_i] = False
            if not np.any(rem_mask):
                full_gap = 0.0
                break
            rem_indices = sup[rem_mask]
            enter_leaf = int(rem_indices[int(np.argmax(means[rem_indices]))])
            w_idx = np.append(w_idx, enter_leaf)
            w_p = np.append(w_p, 0.0)
            continue

        # Price across all y in S via O(|S| d) matrix-vector product
        grad_sup = -m_sup - (beta / q) * (psi_sup @ u)
        grad_dot_p = -float(w_p @ means[w_idx]) - (beta / q) * float(bar_psi @ u)

        enter_local = int(np.argmin(grad_sup))
        enter_leaf = int(sup[enter_local])
        full_gap = max(0.0, grad_dot_p - float(grad_sup[enter_local]))

        if full_gap <= tol:
            break

        active_set = set(w_idx.tolist())
        if enter_leaf in active_set:
            # Check whether any vertex outside active_set can strictly improve the objective
            best_out_leaf = -1
            best_out_grad = grad_dot_p - tol
            for loc_i, lf in enumerate(sup):
                if int(lf) not in active_set and float(grad_sup[loc_i]) < best_out_grad:
                    best_out_grad = float(grad_sup[loc_i])
                    best_out_leaf = int(lf)
            if best_out_leaf < 0:
                break
            enter_leaf = best_out_leaf

        w_idx = np.append(w_idx, enter_leaf)
        w_p = np.append(w_p, 0.0)

    # Guarantee Caratheodory sparsity |supp(p*)| <= d + 1 even if max_outer exhausted
    w_idx, w_p = caratheodory_prune(
        features_w=raw_features,
        means_w=means,
        weights_w=w_p,
        indices_w=w_idx,
        exact_linear_mean=exact_linear_mean,
    )
    bar_psi = w_p @ psi[w_idx]
    u = psi_z - bar_psi
    q = float(np.linalg.norm(u))
    dual_val = (m_z - float(w_p @ means[w_idx])) + beta * q
    # For clipped regret [D_t(z, S)]_+, any dual_val <= 1e-9 certifies exact 0.0 regret (zero gap).
    if dual_val <= 1e-9:
        full_gap = 0.0

    contrast = phi_z - (w_p @ raw_features[w_idx])
    return ChallengerResult(
        dual_value=float(dual_val),
        duality_gap=float(max(0.0, full_gap)),
        weights=w_p,
        support_indices=w_idx,
        contrast=contrast,
        iterations=total_iters,
    )


def solve_feature_challenger_dense_afw(
    z_idx: int,
    sup: np.ndarray,
    means: np.ndarray,
    psi: np.ndarray,
    raw_features: np.ndarray,
    beta: float,
    tol: float = 1e-8,
    max_iter: int = 80,
) -> ChallengerResult:
    """Dense away-step Frank-Wolfe directly over the full inside support `Delta(S)`."""
    m_z = float(means[z_idx])
    m_sup = means[sup]
    psi_z = psi[z_idx]
    psi_sup = psi[sup]

    diffs = psi_z[None, :] - psi_sup
    v_scores = (m_z - m_sup) + beta * np.linalg.norm(diffs, axis=1)
    init_p = np.zeros(len(sup), dtype=np.float64)
    init_p[int(np.argmin(v_scores))] = 1.0

    p, dual_val, gap, iters = _solve_small_simplex_afw(
        m_z=m_z,
        m_w=m_sup,
        psi_z=psi_z,
        psi_w=psi_sup,
        beta=beta,
        init_p=init_p,
        tol=tol,
        max_iter=max_iter,
    )
    nz = p > 1e-13
    if not np.any(nz):
        nz[int(np.argmax(p))] = True
    p_sub = p[nz] / float(np.sum(p[nz]))
    sup_sub = sup[nz]
    contrast = raw_features[z_idx] - (p_sub @ raw_features[sup_sub])
    return ChallengerResult(
        dual_value=float(dual_val),
        duality_gap=float(gap),
        weights=p_sub,
        support_indices=sup_sub,
        contrast=contrast,
        iterations=iters,
    )


def solve_feature_challenger_cvxpy(
    z_idx: int,
    sup: np.ndarray,
    means: np.ndarray,
    psi: np.ndarray,
    raw_features: np.ndarray,
    beta: float,
) -> ChallengerResult:
    """Reference interior-point Second-Order Cone Program (SOCP) via CVXPY.

    CVXPY is an optional dependency (``pip install "dagcert[audit]"``); the default
    column-generation solvers do not need it.
    """
    try:
        import cvxpy as cp
    except ImportError as exc:  # pragma: no cover - depends on the environment
        raise ImportError(
            "solver='cvxpy_socp' needs CVXPY; install it with `pip install \"dagcert[audit]\"`."
        ) from exc
    k = len(sup)
    p_var = cp.Variable(k, nonneg=True)
    m_z = float(means[z_idx])
    m_sup = means[sup]
    psi_z = psi[z_idx]
    psi_sup = psi[sup]

    u_expr = psi_z - psi_sup.T @ p_var
    obj = cp.Minimize((m_z - m_sup @ p_var) + beta * cp.norm2(u_expr))
    prob = cp.Problem(obj, [cp.sum(p_var) == 1.0])
    try:
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-10, tol_gap_rel=1e-10, tol_feas=1e-10)
    except cp.SolverError:
        prob.solve(solver=cp.SCS, eps=1e-9)

    if p_var.value is None:
        raise RuntimeError("CVXPY SOCP failed to return a feasible simplex solution.")
    p_val = np.maximum(0.0, np.asarray(p_var.value, dtype=np.float64))
    p_val /= float(np.sum(p_val))
    u_num = psi_z - (p_val @ psi_sup)
    dual_val = (m_z - float(p_val @ m_sup)) + beta * float(np.linalg.norm(u_num))
    nz = p_val > 1e-9
    if not np.any(nz):
        nz[int(np.argmax(p_val))] = True
    p_sub = p_val[nz] / float(np.sum(p_val[nz]))
    sup_sub = sup[nz]
    contrast = raw_features[z_idx] - (p_sub @ raw_features[sup_sub])
    return ChallengerResult(
        dual_value=float(dual_val),
        duality_gap=0.0,
        weights=p_sub,
        support_indices=sup_sub,
        contrast=contrast,
        iterations=1,
    )


def solve_primal_ellipsoid_regret(
    action: int,
    support_struct: SupportStructure,
    phi: np.ndarray,
    theta_hat: np.ndarray,
    v_mat: np.ndarray,
    beta: float,
    n_restarts: int = 24,
    dense_grid_per_axis: int = 0,
    seed: int = 0,
) -> float:
    """Independent primal maximization of `max_{theta in Theta_t} [max_z phi(z)^T theta - max_{y in S(a)} phi(y)^T theta]`
    for numerical audit in Experiment E0.

    Parameterizes `theta = theta_hat + beta * V_t^{-1/2} u` over the unit ball `||u||_2 <= 1`.
    """
    comp = support_struct.complements[action]
    sup = support_struct.supports[action]
    if len(comp) == 0:
        return 0.0

    d = phi.shape[1]
    v_inv = np.linalg.inv(v_mat)
    l_inv_t = np.linalg.cholesky(v_inv)  # V_t^{-1} = L L^T => theta = theta_hat + beta * L @ u

    def eval_regret_u(u_vec: np.ndarray) -> float:
        nrm = float(np.linalg.norm(u_vec))
        if nrm > 1.0:
            u_vec = u_vec / nrm
        theta = theta_hat + beta * (l_inv_t @ u_vec)
        vals = phi @ theta
        return max(0.0, float(np.max(vals[comp]) - np.max(vals[sup])))

    best = eval_regret_u(np.zeros(d, dtype=np.float64))
    rng = np.random.default_rng(seed)

    # Check analytical boundary directions aligned with outside-vs-inside contrasts
    for z in comp:
        for y in sup[: min(len(sup), 6)]:
            g = phi[z] - phi[y]
            ug = l_inv_t.T @ g
            ng = float(np.linalg.norm(ug))
            if ng > 1e-14:
                best = max(best, eval_regret_u(ug / ng))

    # Optional dense parameter-space grid for low-dimensional verification (d <= 3)
    if dense_grid_per_axis > 0 and d <= 3:
        ticks = np.linspace(-1.0, 1.0, dense_grid_per_axis)
        meshes = np.meshgrid(*([ticks] * d), indexing="ij")
        pts = np.stack([m.reshape(-1) for m in meshes], axis=1)
        radii = np.linalg.norm(pts, axis=1)
        inside_pts = pts[radii <= 1.0 + 1e-12]
        # Also project boundary points onto the sphere
        bdy_pts = pts[radii > 1e-12] / radii[radii > 1e-12, None]
        all_u = np.vstack([inside_pts, bdy_pts])
        thetas = theta_hat[:, None] + beta * (l_inv_t @ all_u.T)  # (d, N)
        f_all = phi @ thetas  # (M, N)
        reg_grid = np.max(f_all[comp, :], axis=0) - np.max(f_all[sup, :], axis=0)
        best = max(best, float(np.max(reg_grid)))

    # Multi-start smooth log-sum-exp homotopy + Nelder-Mead polish per outside z
    for z in comp:
        phi_z = phi[z]
        phi_sup = phi[sup]
        for r_idx in range(max(4, n_restarts // max(1, len(comp)))):
            if r_idx == 0:
                u0 = np.zeros(d, dtype=np.float64)
            else:
                raw = rng.standard_normal(d)
                u0 = raw / max(1.0, float(np.linalg.norm(raw))) * float(rng.uniform(0.5, 1.0))

            for tau in (25.0, 200.0):
                def smooth_neg_obj(u_var: np.ndarray, tau_val: float = tau) -> float:
                    theta = theta_hat + beta * (l_inv_t @ u_var)
                    s_vals = phi_sup @ theta
                    m_max = float(np.max(s_vals))
                    lse = m_max + math.log(float(np.sum(np.exp(tau_val * (s_vals - m_max))))) / tau_val
                    return -(float(phi_z @ theta) - lse)

                res = minimize(
                    smooth_neg_obj,
                    u0,
                    method="SLSQP",
                    constraints={"type": "ineq", "fun": lambda u_v: 1.0 - float(u_v @ u_v)},
                    options={"ftol": 1e-11, "maxiter": 120},
                )
                u0 = res.x
                best = max(best, eval_regret_u(u0))

            res_nm = minimize(
                lambda u_v: -eval_regret_u(u_v) + 10.0 * max(0.0, float(u_v @ u_v) - 1.0) ** 2,
                u0,
                method="Nelder-Mead",
                options={"xatol": 1e-9, "fatol": 1e-10, "maxiter": 300},
            )
            best = max(best, eval_regret_u(res_nm.x))

    return max(0.0, float(best))


def compute_hull_discrepancy(
    phi: np.ndarray,
    support_struct: SupportStructure,
    tol: float = 1e-8,
) -> list[HullDominanceReport]:
    """Compute exact feature-polytope discrepancy `eta_2(a) = max_{z notin S(a)} dist_2(phi(z), conv(Phi_{S(a)}))`
    for every root action (Theory Program T2.1 & T2.2).
    """
    zero_means = np.zeros(phi.shape[0], dtype=np.float64)
    reports: list[HullDominanceReport] = []
    for a in range(support_struct.k):
        sup = support_struct.supports[a]
        comp = support_struct.complements[a]
        if len(comp) == 0:
            reports.append(
                HullDominanceReport(
                    action=a,
                    support_size=len(sup),
                    outside_size=0,
                    max_hull_dist_l2=0.0,
                    mean_hull_dist_l2=0.0,
                    dominated_outside_count=0,
                    zero_sample_exact=True,
                )
            )
            continue
        dists = []
        dominated = 0
        for z in comp:
            res = solve_feature_challenger_colgen(
                z_idx=int(z),
                sup=sup,
                means=zero_means,
                psi=phi,
                raw_features=phi,
                beta=1.0,
                exact_linear_mean=True,
                tol=1e-10,
            )
            d_val = max(0.0, res.dual_value)
            dists.append(d_val)
            if d_val <= tol:
                dominated += 1
        max_d = float(np.max(dists))
        mean_d = float(np.mean(dists))
        reports.append(
            HullDominanceReport(
                action=a,
                support_size=len(sup),
                outside_size=len(comp),
                max_hull_dist_l2=max_d,
                mean_hull_dist_l2=mean_d,
                dominated_outside_count=dominated,
                zero_sample_exact=(dominated == len(comp)),
            )
        )
    return reports


class LinearFeatureModel:
    """Track A: Regularized Least-Squares linear feature model `f(z) = m_0 + phi(z)^T theta*`
    with `O(d^2)` Sherman-Morrison covariance updates and valid confidence ellipsoids.

    Supports:
    - `abbasi_yadkori`: Exact anytime frequentist confidence ellipsoid (Theorem T3.1).
    - `misspec_robust`: Misspecification-adjusted ellipsoid (`|b_z| <= xi`, Theorem T3.3) with
      per-terminal RLS weight capping `N_max(xi) = ceil(sigma^2 / xi^2)` so bias never diverges.
    - `nominal_bayes`: Gaussian linear posterior credible ellipsoid (`sqrt(chi2_{d, 1-delta})` or
      simultaneous Gaussian bound).
    """

    def __init__(
        self,
        phi: np.ndarray,
        prior_mean: float = 0.0,
        reg_lambda: float = 1.0,
        obs_std: float = 0.10,
        subgaussian_sigma: float | None = None,
        param_bound: float = 1.0,
        misspec_xi: float = 0.0,
        cap_misspec_weights: bool = True,
        beta_mode: str = "abbasi_yadkori",
        delta: float = 0.05,
    ) -> None:
        if beta_mode not in ("abbasi_yadkori", "misspec_robust", "nominal_bayes"):
            raise ValueError(f"Unknown LinearFeatureModel beta_mode: {beta_mode!r}")
        self.phi = np.asarray(phi, dtype=np.float64)
        self.m, self.d = self.phi.shape
        self.prior_mean = float(prior_mean)
        self.reg_lambda = float(reg_lambda)
        self.obs_std = float(obs_std)
        self.obs_var = float(obs_std * obs_std)
        self.subgaussian_sigma = float(obs_std if subgaussian_sigma is None else subgaussian_sigma)
        self.param_bound = float(param_bound)
        self.misspec_xi = float(misspec_xi)
        self.cap_misspec_weights = bool(cap_misspec_weights)
        self.beta_mode = beta_mode
        self.delta = float(delta)

        if self.misspec_xi > 1e-12 and self.cap_misspec_weights:
            self.max_rls_pulls_per_arm = max(1, int(math.ceil(self.obs_var / (self.misspec_xi ** 2))))
        else:
            self.max_rls_pulls_per_arm = 10**9

        self.v_mat = self.reg_lambda * np.eye(self.d, dtype=np.float64)
        self.v_inv = (1.0 / self.reg_lambda) * np.eye(self.d, dtype=np.float64)
        self.logdet_ratio = 0.0  # log(det(V_t) / lambda^d)
        self.xy_sum = np.zeros(self.d, dtype=np.float64)
        self.theta_hat = np.zeros(self.d, dtype=np.float64)

        self.arm_counts = np.zeros(self.m, dtype=np.int64)
        self.rls_arm_counts = np.zeros(self.m, dtype=np.int64)
        self.effective_rls_pulls = 0
        self.total_pulls = 0

        self._chol_dirty = True
        self._chol_v_inv = np.sqrt(1.0 / self.reg_lambda) * np.eye(self.d, dtype=np.float64)
        self._psi = self.phi @ self._chol_v_inv
        self._means = np.full(self.m, self.prior_mean, dtype=np.float64)

    def observe(self, arm_idx: int, reward: float) -> None:
        self.arm_counts[arm_idx] += 1
        self.total_pulls += 1

        if self.rls_arm_counts[arm_idx] >= self.max_rls_pulls_per_arm:
            return

        self.rls_arm_counts[arm_idx] += 1
        self.effective_rls_pulls += 1
        x = self.phi[arm_idx]
        y_centered = float(reward) - self.prior_mean

        vx = self.v_inv @ x
        denom = 1.0 + float(x @ vx)
        self.v_mat += np.outer(x, x)
        self.v_inv -= np.outer(vx, vx) / denom
        self.logdet_ratio += math.log(max(1.0, denom))
        self.xy_sum += y_centered * x
        self.theta_hat = self.v_inv @ self.xy_sum
        self._chol_dirty = True

    def _sync_factors(self) -> None:
        if not self._chol_dirty:
            return
        # Periodic numerical stabilization every 512 effective updates
        if self.effective_rls_pulls > 0 and self.effective_rls_pulls % 512 == 0:
            sym_v = 0.5 * (self.v_mat + self.v_mat.T)
            l_v = np.linalg.cholesky(sym_v)
            self.v_inv = cho_solve((l_v, True), np.eye(self.d, dtype=np.float64))
            self.logdet_ratio = 2.0 * float(np.sum(np.log(np.diag(l_v)))) - self.d * math.log(self.reg_lambda)
            self.theta_hat = self.v_inv @ self.xy_sum

        sym_inv = 0.5 * (self.v_inv + self.v_inv.T) + 1e-15 * np.eye(self.d, dtype=np.float64)
        self._chol_v_inv = np.linalg.cholesky(sym_inv)
        self._psi = self.phi @ self._chol_v_inv
        self._means = self.prior_mean + (self.phi @ self.theta_hat)
        self._chol_dirty = False

    def beta(self) -> float:
        """Confidence ellipsoid radius `beta_t` in the `||theta - theta_hat||_{V_t} <= beta_t` metric."""
        self._sync_factors()
        if self.beta_mode == "nominal_bayes":
            # Simultaneous Gaussian posterior credible scaling (scaled to V_t = sigma^2 Sigma_t^{-1})
            t = max(1, self.total_pulls + 1)
            return self.obs_std * math.sqrt(2.0 * math.log(4.0 * self.m * (t * t) / self.delta))

        base = math.sqrt(self.reg_lambda) * self.param_bound + self.subgaussian_sigma * math.sqrt(
            max(0.0, 2.0 * math.log(1.0 / self.delta) + self.logdet_ratio)
        )
        if self.beta_mode == "misspec_robust" and self.misspec_xi > 0.0:
            # Exact self-normalized bias bound ||sum_s alpha_s b_{z_s} phi(z_s)||_{V_t^{-1}} <= xi * sqrt(T_eff(t))
            return base + self.misspec_xi * math.sqrt(float(self.effective_rls_pulls))
        return base

    def terminal_means_and_psi(self) -> tuple[np.ndarray, np.ndarray]:
        self._sync_factors()
        return self._means, self._psi

    def terminal_stds(self) -> np.ndarray:
        """Unscaled Mahalanobis norms `||phi(z)||_{V_t^{-1}}`."""
        self._sync_factors()
        return np.linalg.norm(self._psi, axis=1)

    def contrast_variance_reduction(self, g_vec: np.ndarray) -> np.ndarray:
        """One-step reduction in `(g^T Sigma_t g)` from evaluating each terminal `x in Z`."""
        self._sync_factors()
        # With V_t = lambda I + sum phi phi^T (or precision proportional to sigma^{-2} V_t):
        # Delta_t(g; x) = sigma^2 * (g^T V_t^{-1} phi(x))^2 / (1 + phi(x)^T V_t^{-1} phi(x))
        vg = self.v_inv @ g_vec
        proj = self.phi @ vg
        lev = np.sum(self._psi * self._psi, axis=1)
        return self.obs_var * (proj * proj) / (1.0 + lev)

    def sample_posterior_values(self, n_draws: int, rng: np.random.Generator) -> np.ndarray:
        """Draw `(n_draws, M)` terminal value realizations from Bayesian posterior `N(theta_hat, sigma^2 V_t^{-1})`."""
        self._sync_factors()
        z = rng.standard_normal((self.d, n_draws))
        theta_draws = self.theta_hat[:, None] + self.obs_std * (self._chol_v_inv @ z)
        return (self.prior_mean + (self.phi @ theta_draws)).T


class DiscreteGPPosteriorModel:
    """Track B: Exact finite-domain Gaussian Process `f_Z ~ N(m_0, K)` with noisy observations
    `Y = f_x + N(0, sigma^2)` maintained via Sherman-Morrison / Woodbury updates.
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
    ) -> None:
        if beta_mode not in ("nominal_bayes", "rkhs_frequentist"):
            raise ValueError(f"Unknown DiscreteGPPosteriorModel beta_mode: {beta_mode!r}")
        self.k_mat = np.array(kernel, dtype=np.float64, copy=True)
        self.m = int(self.k_mat.shape[0])
        self.prior_mean = float(prior_mean)
        self.obs_std = float(obs_std)
        self.obs_var = float(obs_std * obs_std)
        self.inv_obs_var = 1.0 / self.obs_var
        self.subgaussian_sigma = float(obs_std if subgaussian_sigma is None else subgaussian_sigma)
        self.rkhs_bound = float(rkhs_bound)
        self.beta_mode = beta_mode
        self.delta = float(delta)

        self.mean = np.full(self.m, self.prior_mean, dtype=np.float64)
        self.sigma_mat = self.k_mat.copy()
        self.arm_counts = np.zeros(self.m, dtype=np.int64)
        self.centered_sums = np.zeros(self.m, dtype=np.float64)
        self.info_gain = 0.0
        self.total_pulls = 0

        self.raw_features = None  # Track B operates directly on Sigma_t (no M x M eye matrix)
        self._chol_dirty = True
        self._psi = None

    def observe(self, arm_idx: int, reward: float) -> None:
        self.arm_counts[arm_idx] += 1
        self.total_pulls += 1
        self.centered_sums[arm_idx] += float(reward) - self.prior_mean

        col = self.sigma_mat[:, arm_idx].copy()
        s_jj = float(col[arm_idx])
        self.info_gain += 0.5 * math.log(max(1.0, 1.0 + s_jj * self.inv_obs_var))
        denom = self.obs_var + s_jj
        self.sigma_mat -= np.outer(col, col) / denom
        self.mean = self.prior_mean + self.sigma_mat @ (self.centered_sums * self.inv_obs_var)
        self._chol_dirty = True

    def _sync_factors(self) -> None:
        if not self._chol_dirty and self._psi is not None:
            return
        sym = 0.5 * (self.sigma_mat + self.sigma_mat.T)
        eig_floor = 1e-13 * max(1.0, float(np.max(np.diag(sym))))
        self._psi = np.linalg.cholesky(sym + eig_floor * np.eye(self.m, dtype=np.float64))
        self._chol_dirty = False

    def beta(self) -> float:
        if self.beta_mode == "nominal_bayes":
            t = max(1, self.total_pulls + 1)
            return math.sqrt(2.0 * math.log(4.0 * self.m * (t * t) / self.delta))
        return self.rkhs_bound + (self.subgaussian_sigma / self.obs_std) * math.sqrt(
            max(0.0, 2.0 * (self.info_gain + math.log(1.0 / self.delta)))
        )

    def terminal_means_and_psi(self) -> tuple[np.ndarray, np.ndarray]:
        return self.mean, self.sigma_mat

    def terminal_stds(self) -> np.ndarray:
        return np.sqrt(np.maximum(1e-18, np.diag(self.sigma_mat)))

    def contrast_variance_reduction(self, g_vec: np.ndarray) -> np.ndarray:
        """One-step posterior variance reduction `(g^T Sigma_t e_x)^2 / (sigma^2 + Sigma_{t,xx})`."""
        sg = self.sigma_mat @ g_vec
        return (sg * sg) / (self.obs_var + np.maximum(1e-18, np.diag(self.sigma_mat)))

    def sample_posterior_values(self, n_draws: int, rng: np.random.Generator) -> np.ndarray:
        self._sync_factors()
        z = rng.standard_normal((self.m, n_draws))
        return (self.mean[:, None] + (self._psi @ z)).T


class JointEllipsoidCertifier:
    """Exact and lazy-pruned conic decision certifier over `Theta_t` (Theory Programs T1 & T3.3).

    Supports:
    - `solver='colgen_lazy'`: Warm-started Caratheodory column generation + lazy challenger upper bounds.
    - `solver='colgen_full'`: Caratheodory column generation evaluated on every outside challenger.
    - `solver='dense_afw'`: Dense away-step Frank-Wolfe evaluated on every outside challenger.
    - `solver='cvxpy_socp'`: Exact CVXPY SOCP solver.
    - `solver='vertex_approx'`: Conservative single-vertex upper bound `min_{y in S} [...]`.
    """

    VALID_SOLVERS = ("colgen_lazy", "colgen_full", "dense_afw", "cvxpy_socp", "vertex_approx")

    def __init__(
        self,
        support_struct: SupportStructure,
        epsilon: float,
        solver: str = "colgen_lazy",
        misspec_xi: float = 0.0,
        exact_linear_mean: bool = True,
    ) -> None:
        if solver not in self.VALID_SOLVERS:
            raise ValueError(f"Unsupported JointEllipsoidCertifier solver: {solver!r}")
        self.support_struct = support_struct
        self.epsilon = float(epsilon)
        self.solver = solver
        self.misspec_xi = float(misspec_xi)
        self.exact_linear_mean = exact_linear_mean

        # Warm-start cache `(action, z_idx) -> (support_indices, weights)`
        self._warm_cache: dict[tuple[int, int], tuple[np.ndarray, np.ndarray]] = {}
        self.cert_time_s = 0.0
        self.total_solver_iters = 0
        self.total_challengers_solved = 0
        self.total_challengers_considered = 0
        self.max_active_support_size = 0
        self.max_duality_gap = 0.0

    def certify_action_gp(
        self,
        action: int,
        means: np.ndarray,
        sigma_mat: np.ndarray,
        beta: float,
        stop_if_above_eps: bool = False,
    ) -> ActionCertificate:
        """Direct O(|S_nd|^2) GP-covariance conic certifier for Track B (`DiscreteGPPosteriorModel`),
        avoiding M x M Cholesky and eye-matrix allocations.
        """
        t0 = time.perf_counter()
        sup = self.support_struct.supports[action]
        comp = self.support_struct.complements[action]
        m_tot = len(means)
        if len(comp) == 0:
            self.cert_time_s += time.perf_counter() - t0
            return ActionCertificate(
                action=action,
                regret=0.0,
                challenger_idx=-1,
                inside_indices=sup[:1].copy(),
                inside_weights=np.ones(1, dtype=np.float64),
                contrast=np.zeros(m_tot, dtype=np.float64),
                max_duality_gap=0.0,
                evaluated_challengers=0,
                total_challengers=0,
            )

        diag_all = np.maximum(1e-18, np.diag(sigma_mat))
        stds_all = np.sqrt(diag_all)
        m_sup_full = means[sup]
        s_sup_full = stds_all[sup]

        # Sound dominance filter: inside terminals whose UCB is below max LCB in S(a)
        max_lo_s = float(np.max(m_sup_full - beta * s_sup_full))
        keep = (m_sup_full + beta * s_sup_full) >= max_lo_s - 1e-12
        sup_nd = sup[keep]
        if len(sup_nd) > 24:
            # Fast active top-24 inside pool by empirical mean + UCB for large protein supports;
            # any subset of S(a) yields a strictly valid upper bound on D_t(z, S(a))!
            top_u = np.argsort(-(means[sup_nd] + 0.5 * beta * stds_all[sup_nd]))[:24]
            sup_nd = sup_nd[top_u]

        m_s = means[sup_nd]
        sig_ss = sigma_mat[sup_nd[:, None], sup_nd[None, :]]
        diag_s = np.diag(sig_ss)
        diag_c = diag_all[comp]
        sig_sc = sigma_mat[sup_nd[:, None], comp[None, :]]

        q_mat = np.sqrt(np.maximum(1e-18, diag_c[None, :] + diag_s[:, None] - 2.0 * sig_sc))
        vert_scores = (means[comp][None, :] - m_s[:, None]) + beta * q_mat
        vert_ub = np.min(vert_scores, axis=0)
        best_y_local = np.argmin(vert_scores, axis=0)
        order = np.argsort(-vert_ub)
        self.total_challengers_considered += len(comp)

        if float(vert_ub[int(order[0])]) <= self.epsilon:
            p0 = int(order[0])
            z0 = int(comp[p0])
            y0 = int(sup_nd[int(best_y_local[p0])])
            g0 = np.zeros(m_tot, dtype=np.float64)
            g0[z0] = 1.0
            g0[y0] = -1.0
            self.cert_time_s += time.perf_counter() - t0
            return ActionCertificate(
                action=action,
                regret=max(0.0, float(vert_ub[p0])),
                challenger_idx=z0,
                inside_indices=np.array([y0], dtype=np.int64),
                inside_weights=np.ones(1, dtype=np.float64),
                contrast=g0,
                max_duality_gap=0.0,
                evaluated_challengers=0,
                total_challengers=len(comp),
            )

        best_val = -math.inf
        best_z = int(comp[int(order[0])])
        best_p = np.ones(1, dtype=np.float64)
        best_idx = sup_nd[:1]
        max_gap = 0.0
        eval_cnt = 0

        for rank_k, pos in enumerate(order):
            ub_z = float(vert_ub[pos])
            if ub_z <= best_val and best_val > -math.inf:
                break
            if stop_if_above_eps and rank_k >= 2 and best_val > self.epsilon:
                break
            z_idx = int(comp[pos])
            eval_cnt += 1
            self.total_challengers_solved += 1
            val_z, gap_z, p_z = solve_ellipsoid_challenger(
                float(means[z_idx]),
                m_s,
                float(diag_c[pos]),
                sig_sc[:, pos],
                sig_ss,
                beta,
                tol=1e-6,
                max_iter=28,
            )
            max_gap = max(max_gap, gap_z)
            if val_z > best_val:
                best_val = val_z
                best_z = z_idx
                nz = p_z > 1e-12
                if not np.any(nz):
                    nz[int(np.argmax(p_z))] = True
                best_p = p_z[nz] / float(np.sum(p_z[nz]))
                best_idx = sup_nd[nz]

        g_vec = np.zeros(m_tot, dtype=np.float64)
        g_vec[best_z] = 1.0
        g_vec[best_idx] = -best_p
        self.cert_time_s += time.perf_counter() - t0
        return ActionCertificate(
            action=action,
            regret=max(0.0, best_val),
            challenger_idx=best_z,
            inside_indices=best_idx,
            inside_weights=best_p,
            contrast=g_vec,
            max_duality_gap=max_gap,
            evaluated_challengers=eval_cnt,
            total_challengers=len(comp),
        )

    def certify_action(
        self,
        action: int,
        means: np.ndarray,
        psi: np.ndarray,
        raw_features: np.ndarray,
        beta: float,
        stop_if_above_eps: bool = False,
    ) -> ActionCertificate:
        t0 = time.perf_counter()
        sup = self.support_struct.supports[action]
        comp = self.support_struct.complements[action]
        if len(comp) == 0:
            d = raw_features.shape[1]
            self.cert_time_s += time.perf_counter() - t0
            return ActionCertificate(
                action=action,
                regret=0.0,
                challenger_idx=-1,
                inside_indices=sup[:1].copy(),
                inside_weights=np.ones(1, dtype=np.float64),
                contrast=np.zeros(d, dtype=np.float64),
                max_duality_gap=0.0,
                evaluated_challengers=0,
                total_challengers=0,
            )

        xi_shift = 2.0 * self.misspec_xi
        eff_eps = self.epsilon - xi_shift

        # Fast conservative upper bound per outside challenger using cached warm mixture or top-3 inside means
        m_sup = means[sup]
        psi_sup = psi[sup]
        anchor_pos = np.argsort(-m_sup)[: min(len(sup), 4)]
        anchor_m = m_sup[anchor_pos]
        anchor_psi = psi_sup[anchor_pos]

        # Vectorized pairwise upper bound across all z in comp against top-4 empirical inside anchors
        # Uses BLAS dot product ||a - b||^2 = ||a||^2 + ||b||^2 - 2 a^T b (zero 3D allocation!)
        psi_comp = psi[comp]
        sq_comp = np.sum(psi_comp * psi_comp, axis=1, keepdims=True)
        sq_anc = np.sum(anchor_psi * anchor_psi, axis=1, keepdims=True).T
        q_mat = np.sqrt(np.maximum(0.0, sq_comp + sq_anc - 2.0 * (psi_comp @ anchor_psi.T)))
        ub_scores = (means[comp][:, None] - anchor_m[None, :]) + beta * q_mat
        ub_vec = np.min(ub_scores, axis=1)
        best_anchor_local = np.argmin(ub_scores, axis=1)

        # Tighten ub_vec using cached sparse mixtures when using lazy mode
        if self.solver == "colgen_lazy":
            for pos, z_i in enumerate(comp):
                cached = self._warm_cache.get((action, int(z_i)))
                if cached is not None:
                    c_idx, c_w = cached
                    u_c = psi[int(z_i)] - (c_w @ psi[c_idx])
                    val_c = (float(means[int(z_i)]) - float(c_w @ means[c_idx])) + beta * float(np.linalg.norm(u_c))
                    if val_c < ub_vec[pos]:
                        ub_vec[pos] = val_c

        order = np.argsort(-ub_vec)
        self.total_challengers_considered += len(comp)

        if self.solver == "vertex_approx":
            # Full pairwise minimum over all y in S(a) via BLAS matrix multiply (zero 3D alloc)
            sq_sup = np.sum(psi_sup * psi_sup, axis=1, keepdims=True).T
            full_q = np.sqrt(np.maximum(0.0, sq_comp + sq_sup - 2.0 * (psi_comp @ psi_sup.T)))
            full_scores = (means[comp][:, None] - m_sup[None, :]) + beta * full_q
            min_y_pos = np.argmin(full_scores, axis=1)
            min_vals = full_scores[np.arange(len(comp)), min_y_pos]
            worst_pos = int(np.argmax(min_vals))
            z_star = int(comp[worst_pos])
            y_star = int(sup[int(min_y_pos[worst_pos])])
            reg = max(0.0, float(min_vals[worst_pos]) + xi_shift)
            self.max_active_support_size = max(self.max_active_support_size, 1)
            self.cert_time_s += time.perf_counter() - t0
            return ActionCertificate(
                action=action,
                regret=reg,
                challenger_idx=z_star,
                inside_indices=np.array([y_star], dtype=np.int64),
                inside_weights=np.ones(1, dtype=np.float64),
                contrast=raw_features[z_star] - raw_features[y_star],
                max_duality_gap=0.0,
                evaluated_challengers=len(comp),
                total_challengers=len(comp),
            )

        # Sound instant certificate if even the fast upper bound already certifies `<= eff_eps`
        if self.solver == "colgen_lazy" and float(ub_vec[int(order[0])]) <= eff_eps:
            pos0 = int(order[0])
            z0 = int(comp[pos0])
            cached = self._warm_cache.get((action, z0))
            if cached is not None:
                c_idx, c_w = cached
            else:
                y0 = int(sup[int(best_anchor_local[pos0])])
                c_idx = np.array([y0], dtype=np.int64)
                c_w = np.ones(1, dtype=np.float64)
            reg0 = max(0.0, float(ub_vec[pos0]) + xi_shift)
            self.cert_time_s += time.perf_counter() - t0
            return ActionCertificate(
                action=action,
                regret=reg0,
                challenger_idx=z0,
                inside_indices=c_idx,
                inside_weights=c_w,
                contrast=raw_features[z0] - (c_w @ raw_features[c_idx]),
                max_duality_gap=0.0,
                evaluated_challengers=0,
                total_challengers=len(comp),
            )

        best_val = -math.inf
        best_res: ChallengerResult | None = None
        best_z = int(comp[int(order[0])])
        max_gap = 0.0
        eval_cnt = 0

        for rank_k, pos in enumerate(order):
            z_idx = int(comp[pos])
            if self.solver == "colgen_lazy":
                # Sound pruning: if ub_vec[pos] <= best_val, z_idx cannot beat current worst challenger!
                if ub_vec[pos] <= best_val and best_val > -math.inf:
                    break
                if stop_if_above_eps and rank_k >= 2 and best_val > eff_eps:
                    break

            eval_cnt += 1
            self.total_challengers_solved += 1
            if self.solver in ("colgen_lazy", "colgen_full"):
                warm = self._warm_cache.get((action, z_idx)) if self.solver == "colgen_lazy" else None
                res = solve_feature_challenger_colgen(
                    z_idx=z_idx,
                    sup=sup,
                    means=means,
                    psi=psi,
                    raw_features=raw_features,
                    beta=beta,
                    exact_linear_mean=self.exact_linear_mean,
                    warm_indices=warm[0] if warm is not None else None,
                    warm_weights=warm[1] if warm is not None else None,
                )
                if self.solver == "colgen_lazy":
                    self._warm_cache[(action, z_idx)] = (res.support_indices, res.weights)
            elif self.solver == "dense_afw":
                res = solve_feature_challenger_dense_afw(
                    z_idx=z_idx,
                    sup=sup,
                    means=means,
                    psi=psi,
                    raw_features=raw_features,
                    beta=beta,
                )
            else:
                res = solve_feature_challenger_cvxpy(
                    z_idx=z_idx,
                    sup=sup,
                    means=means,
                    psi=psi,
                    raw_features=raw_features,
                    beta=beta,
                )

            self.total_solver_iters += res.iterations
            self.max_active_support_size = max(self.max_active_support_size, len(res.support_indices))
            max_gap = max(max_gap, res.duality_gap)
            self.max_duality_gap = max(self.max_duality_gap, res.duality_gap)

            if res.dual_value > best_val:
                best_val = res.dual_value
                best_res = res
                best_z = z_idx

        assert best_res is not None
        self.cert_time_s += time.perf_counter() - t0
        return ActionCertificate(
            action=action,
            regret=max(0.0, best_val + xi_shift),
            challenger_idx=best_z,
            inside_indices=best_res.support_indices,
            inside_weights=best_res.weights,
            contrast=best_res.contrast,
            max_duality_gap=max_gap,
            evaluated_challengers=eval_cnt,
            total_challengers=len(comp),
        )


def solve_alt_projection_dual(
    z_idx: int,
    sup: np.ndarray,
    phi: np.ndarray,
    theta_star: np.ndarray,
    w_inv: np.ndarray,
    epsilon: float,
    sigma: float,
) -> tuple[float, np.ndarray]:
    """Exact Lagrangian dual of the quadratic information projection onto `cl(H_eps(z, S(a)))`
    (Theory Program T5.1):

        inf_{vartheta : (phi(z)-phi(y))^T vartheta >= eps forall y in S} ||theta* - vartheta||_{W}^2 / (2 sigma^2)
      = sup_{p in Delta(S)} [eps - g(p)^T theta*]^+^2 / (2 sigma^2 g(p)^T W^{-1} g(p)).

    Returns `(kl_divergence, optimal_p)`. Returns `(math.inf, p)` if `H_eps(z, S(a))` is empty
    (convex-hull dominance `phi(z) in P_a`).
    """
    # Check whether g(p) = 0 is feasible (hull dominance -> H_eps is empty for eps >= 0)
    l_winv = np.linalg.cholesky(0.5 * (w_inv + w_inv.T) + 1e-15 * np.eye(phi.shape[1]))
    psi = phi @ l_winv
    means_star = phi @ theta_star

    # Notice: maximizing (eps - g(p)^T theta*) / ||g(p)||_{W^{-1}} is equivalent to finding the smallest
    # radius `r >= 0` such that `min_{p in Delta(S)} [g(p)^T theta* + r * ||g(p)||_{W^{-1}}] <= eps`!
    res0 = solve_feature_challenger_colgen(
        z_idx=z_idx,
        sup=sup,
        means=means_star,
        psi=psi,
        raw_features=phi,
        beta=0.0,
        tol=1e-10,
    )
    if res0.dual_value > epsilon - 1e-12:
        # theta* itself is already outside or on boundary of acceptability against z
        p_full = np.zeros(len(sup), dtype=np.float64)
        p_full[0] = 1.0
        return 0.0, p_full

    # Check minimum norm ||g(p)||_{W^{-1}}
    zero_m = np.zeros(phi.shape[0], dtype=np.float64)
    hull_chk = solve_feature_challenger_colgen(
        z_idx=z_idx, sup=sup, means=zero_m, psi=psi, raw_features=phi, beta=1.0, tol=1e-10
    )
    if hull_chk.dual_value <= 1e-9:
        p_full = np.zeros(len(sup), dtype=np.float64)
        pos_map = {int(v): i for i, v in enumerate(sup)}
        for idx_i, wt in zip(hull_chk.support_indices, hull_chk.weights):
            p_full[pos_map[int(idx_i)]] = float(wt)
        return math.inf, p_full

    # Exact Dinkelbach fractional-programming iteration for max_{p in Delta(S)} (eps - g(p)^T theta*) / ||g(p)||_{W^{-1}}:
    # At ratio r >= 0, F(r) = min_{p in Delta(S)} [g(p)^T theta* - eps + r * ||g(p)||_{W^{-1}}]; root F(r*) = 0
    # converges quadratically in 6-8 steps using our exact SOCP/ColGen oracle!
    y_best = int(np.argmax(means_star[sup]))
    g_init = psi[z_idx] - psi[int(sup[y_best])]
    q_init = max(1e-12, float(np.linalg.norm(g_init)))
    r_cur = max(0.0, (epsilon - (float(means_star[z_idx]) - float(means_star[int(sup[y_best])]))) / q_init)
    warm_i: np.ndarray | None = None
    warm_w: np.ndarray | None = None

    for _ in range(14):
        res_r = solve_feature_challenger_colgen(
            z_idx=z_idx,
            sup=sup,
            means=means_star,
            psi=psi,
            raw_features=phi,
            beta=r_cur,
            warm_indices=warm_i,
            warm_weights=warm_w,
            tol=1e-10,
        )
        warm_i, warm_w = res_r.support_indices, res_r.weights
        g_psi = psi[z_idx] - (warm_w @ psi[warm_i])
        q_val = float(np.linalg.norm(g_psi))
        num_val = epsilon - (float(means_star[z_idx]) - float(warm_w @ means_star[warm_i]))
        if q_val <= 1e-12:
            r_cur = 1e12
            break
        r_next = max(0.0, num_val / q_val)
        if abs(r_next - r_cur) <= 1e-9 * max(1.0, r_cur):
            r_cur = r_next
            break
        r_cur = r_next

    p_full = np.zeros(len(sup), dtype=np.float64)
    if warm_i is not None and warm_w is not None:
        pos_map = {int(v): i for i, v in enumerate(sup)}
        for idx_i, wt in zip(warm_i, warm_w):
            p_full[pos_map[int(idx_i)]] = float(wt)
    else:
        p_full[y_best] = 1.0

    kl_val = (r_cur * r_cur) / (2.0 * sigma * sigma)
    return float(kl_val), p_full


def compute_characteristic_rate(
    phi: np.ndarray,
    theta_star: np.ndarray,
    support_struct: SupportStructure,
    epsilon: float,
    sigma: float,
    n_outer_iters: int = 80,
) -> CharacteristicRateResult:
    """Compute the information-theoretic certification rate `I_c*(theta*)` (Theory Program T5.2 & T5.3)
    across all acceptable actions `a in A_eps(theta*)`.
    """
    m, d = phi.shape
    means_star = phi @ theta_star
    act_vals = [float(np.max(means_star[sup])) for sup in support_struct.supports]
    v_star = max(act_vals)
    acceptable = tuple(a for a, val in enumerate(act_vals) if v_star - val <= epsilon + 1e-12)
    costs = support_struct.costs

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

        # Optimize allocation w in Delta(Z) via exponentiated-gradient / mirror ascent on log-concave objective
        w = np.full(m, 1.0 / m, dtype=np.float64)
        best_rate_a = 0.0
        best_w_a = w.copy()

        for it in range(1, n_outer_iters + 1):
            w_mat = (phi.T * w) @ phi + 1e-10 * np.eye(d, dtype=np.float64)
            w_inv = np.linalg.inv(w_mat)

            min_kl = math.inf
            worst_g = np.zeros(d, dtype=np.float64)
            for z in comp:
                kl_z, p_z = solve_alt_projection_dual(
                    z_idx=int(z),
                    sup=sup,
                    phi=phi,
                    theta_star=theta_star,
                    w_inv=w_inv,
                    epsilon=epsilon,
                    sigma=sigma,
                )
                if kl_z < min_kl:
                    min_kl = kl_z
                    worst_g = phi[int(z)] - (p_z @ phi[sup])

            if math.isinf(min_kl):
                best_rate_a = math.inf
                best_w_a = w.copy()
                break

            avg_cost = float(w @ costs)
            rate_val = min_kl / avg_cost
            if rate_val > best_rate_a:
                best_rate_a = rate_val
                best_w_a = w.copy()

            # Supergradient of min_kl / (w^T c) w.r.t. w_x:
            # d/dw_x [num / den] = (d_num_x * den - num * c_x) / den^2
            # where d_num_x = [eps - g^T theta*]^2 * (g^T W^{-1} phi_x)^2 / (2 sigma^2 (g^T W^{-1} g)^2)
            wg = w_inv @ worst_g
            denom_g = max(1e-18, float(worst_g @ wg))
            gap_sq = max(0.0, epsilon - float(worst_g @ theta_star)) ** 2
            proj_sq = (phi @ wg) ** 2
            d_num = gap_sq * proj_sq / (2.0 * sigma * sigma * denom_g * denom_g)
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


class CorrelationAwareCertSession:
    """Unified, composable session combining Statistical Model + Certification Oracle + Acquisition Policy.

    Certificate modes (`cert_mode`):
    - `'joint_ellipsoid'`: Exact conic regret `R_t(a) <= eps` over `Theta_t` (with `+ 2*xi` if `misspec_xi > 0`).
    - `'enclosing_box'`: Enclosing rectangular confidence box `B(Theta_t)` at identical radius `beta_t`.
    - `'safe_hybrid'`: Simultaneous `(delta/2 + delta/2)` intersection `min(R_t^{(xi)}(a), R_t^{box}(a)) <= eps`.
    - `'independent_box'`: Distribution-free `DualWitnessCovers` confidence sequence stopping rule.
    - `'posterior_prob'`: Bayesian posterior stopping `max_a Pr(V*(f) - V(a;f) <= eps | D_t) >= 1 - delta`.

    Acquisition policies (`acquisition`):
    - `'contrast_directed'`: Safeguarded Contrast-Directed Certification (`Delta_t(g_t; x) / c(x)`).
    - `'contrast_naive'`: Unsafeguarded dual contrast (`Delta_t(g_t^{dual}; x) / c(x)`).
    - `'multi_contrast'`: Multi-Contrast Design across candidate commitments & top threats.
    - `'bayes_ids'`: Symmetric-MI Information-Directed Acquisition `I(Y_x; A_eps(f) | D_t) / c(x)`.
    - `'maxmin_tracking'`: Online plug-in T5 saddle-point design tracking.
    - `'direct_witness'`: Restricts queries to `{y_t, z_t}` directly (no off-witness proxies).
    - `'gp_ucb'`: Conventional UCB `argmax_x [m_t(x) + beta_t s_t(x)]`.
    - `'gp_root_info'`: Witness width reduction over inside/outside pair.

    Answer-selection rules (`answer_rule`):
    - `'min_regret'` (default, support-aware T5.3): Stops & commits to `argmin_a R_t(a)`.
    - `'greedy_emp'`: Restricts commitment strictly to `argmax_a V(a; hat_theta_t)`.
    """

    VALID_CERTS = ("joint_ellipsoid", "enclosing_box", "safe_hybrid", "independent_box", "posterior_prob")
    VALID_ACQS = (
        "contrast_directed",
        "contrast_naive",
        "multi_contrast",
        "bayes_ids",
        "maxmin_tracking",
        "direct_witness",
        "gp_ucb",
        "gp_root_info",
    )
    VALID_ANSWERS = ("min_regret", "greedy_emp")

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        model: LinearFeatureModel | DiscreteGPPosteriorModel,
        cert_mode: str = "joint_ellipsoid",
        acquisition: str = "contrast_directed",
        answer_rule: str = "min_regret",
        solver: str = "colgen_lazy",
        delta: float = 0.05,
        costs: MappingOrArray | None = None,
        cs_schedule: str = "emp_bernstein",
        check_every: int = 1,
        adaptive_check: bool = False,
        mc_posterior_draws: int = 512,
    ) -> None:
        if cert_mode not in self.VALID_CERTS:
            raise ValueError(f"Unsupported cert_mode: {cert_mode!r}")
        if acquisition not in self.VALID_ACQS:
            raise ValueError(f"Unsupported acquisition: {acquisition!r}")
        if answer_rule not in self.VALID_ANSWERS:
            raise ValueError(f"Unsupported answer_rule: {answer_rule!r}")

        self.problem = problem
        self.graph = problem.graph
        self.support_struct = SupportStructure(self.graph, costs=costs)
        self.epsilon = float(epsilon)
        self.delta = float(delta)
        self.model = model
        self.cert_mode = cert_mode
        self.acquisition = acquisition
        self.answer_rule = answer_rule
        self.check_every = max(1, int(check_every))
        self.adaptive_check = bool(adaptive_check)
        self.mc_posterior_draws = int(mc_posterior_draws)

        self.oracle = problem.oracle(seed)
        self.rng = np.random.default_rng((seed * 0x9E3779B97F4A7C15 + 101) & 0xFFFFFFFFFFFFFFFF)

        misspec_xi = getattr(model, "misspec_xi", 0.0)
        self._is_gp = isinstance(model, DiscreteGPPosteriorModel)
        raw_feats = None if self._is_gp else model.phi
        self._raw_features = raw_feats
        self.ellipsoid_cert = JointEllipsoidCertifier(
            self.support_struct,
            epsilon=self.epsilon,
            solver=solver,
            misspec_xi=misspec_xi if cert_mode in ("joint_ellipsoid", "safe_hybrid") else 0.0,
            exact_linear_mean=isinstance(model, LinearFeatureModel),
        )

        cs_delta = 0.5 * delta if cert_mode == "safe_hybrid" else delta
        if cert_mode == "safe_hybrid":
            # Union bound split delta/2 for ellipsoid + delta/2 for independent box
            self.model.delta = 0.5 * delta
        self.cs_monitor = (
            DualWitnessCovers(self.graph, delta=cs_delta, schedule=cs_schedule, layout="best")
            if cert_mode in ("independent_box", "safe_hybrid")
            else None
        )

        self.calls = 0
        self.total_cost = 0.0
        self.certified = False
        self.conflict = False
        self.action = 0
        self.current_regret = math.inf
        self.off_witness_pulls = 0
        self.distinct_leaves_evaluated: set[int] = set()
        self._tracking_weights = np.full(self.support_struct.m, 1.0 / self.support_struct.m, dtype=np.float64)
        self._next_arm_idx = 0

        self._evaluate_certificate_and_plan()

    def _candidate_actions(self, means: np.ndarray) -> list[int]:
        if self.answer_rule == "greedy_emp":
            emp_vals = [float(np.max(means[sup])) for sup in self.support_struct.supports]
            return [int(np.argmax(emp_vals))]
        return list(range(self.support_struct.k))

    def _evaluate_certificate_and_plan(self) -> None:
        means, psi = self.model.terminal_means_and_psi()
        stds = self.model.terminal_stds()
        beta = self.model.beta()
        u_ell = means + beta * stds
        l_ell = means - beta * stds

        cand_actions = self._candidate_actions(means)

        # 1. Evaluate active stopping rule
        best_a = cand_actions[0]
        best_reg = math.inf

        if self.cert_mode == "independent_box":
            assert self.cs_monitor is not None
            act_cs, reg_cs, _, _, _ = self.cs_monitor.query_dual_witness()
            if self.answer_rule == "min_regret":
                best_a = int(act_cs)
                best_reg = float(reg_cs)
            else:
                a0 = cand_actions[0]
                sup0 = self.support_struct.supports[a0]
                comp0 = self.support_struct.complements[a0]
                ev = self.cs_monitor.evidence
                l_in = max(float(ev.lower[self.support_struct.leaves[i]]) for i in sup0)
                u_out = max((float(ev.upper[self.support_struct.leaves[i]]) for i in comp0), default=-math.inf)
                best_a = a0
                best_reg = max(0.0, u_out - l_in)

        elif self.cert_mode == "enclosing_box":
            xi_pad = 2.0 * getattr(self.model, "misspec_xi", 0.0)
            for a in cand_actions:
                sup = self.support_struct.supports[a]
                comp = self.support_struct.complements[a]
                u_out = float(np.max(u_ell[comp])) if len(comp) else -math.inf
                reg_a = max(0.0, u_out - float(np.max(l_ell[sup])) + xi_pad)
                if reg_a < best_reg:
                    best_reg = reg_a
                    best_a = a

        elif self.cert_mode == "posterior_prob":
            draws = self.model.sample_posterior_values(self.mc_posterior_draws, self.rng)  # (S, M)
            v_star = np.max(draws, axis=1)  # (S,)
            best_q = -1.0
            for a in cand_actions:
                sup = self.support_struct.supports[a]
                v_a = np.max(draws[:, sup], axis=1)
                ok = (v_star - v_a) <= self.epsilon + 1e-12
                # Conservative finite-sample Monte Carlo lower adjustment so MC noise does not inflate q_t
                q_hat = float(np.mean(ok))
                mc_se = math.sqrt(max(0.0, q_hat * (1.0 - q_hat)) / self.mc_posterior_draws)
                q_lcb = q_hat - 1.96 * mc_se
                if q_lcb > best_q:
                    best_q = q_lcb
                    best_a = a
            best_reg = 0.0 if best_q >= (1.0 - self.delta) else (1.0 - best_q)

        else:
            # 'joint_ellipsoid' or 'safe_hybrid'
            # Order candidate actions by fast enclosing-box regret so certified actions are found immediately
            if len(cand_actions) > 1:
                approx_regs = []
                for a in cand_actions:
                    sup = self.support_struct.supports[a]
                    comp = self.support_struct.complements[a]
                    u_out = float(np.max(u_ell[comp])) if len(comp) else -math.inf
                    approx_regs.append((max(0.0, u_out - float(np.max(means[sup]))), a))
                approx_regs.sort()
                ordered_cands = [a for _, a in approx_regs]
            else:
                ordered_cands = cand_actions

            # Evaluate top-2 candidates accurately during run (and any candidate with approx_reg <= eps)
            for rank_i, a in enumerate(ordered_cands):
                if rank_i >= 2 and best_reg > self.epsilon and approx_regs[rank_i][0] > 2.5 * self.epsilon:
                    continue
                if self._is_gp:
                    cert_a = self.ellipsoid_cert.certify_action_gp(
                        action=a,
                        means=means,
                        sigma_mat=psi,
                        beta=beta,
                        stop_if_above_eps=True,
                    )
                else:
                    cert_a = self.ellipsoid_cert.certify_action(
                        action=a,
                        means=means,
                        psi=psi,
                        raw_features=self._raw_features,
                        beta=beta,
                        stop_if_above_eps=True,
                    )
                if cert_a.regret < best_reg:
                    best_reg = cert_a.regret
                    best_a = a
                if best_reg <= self.epsilon:
                    break

            if self.cert_mode == "safe_hybrid":
                assert self.cs_monitor is not None
                act_cs, reg_cs, _, _, _ = self.cs_monitor.query_dual_witness()
                if float(reg_cs) < best_reg and (self.answer_rule == "min_regret" or int(act_cs) in cand_actions):
                    best_reg = float(reg_cs)
                    best_a = int(act_cs)

        self.action = best_a
        self.current_regret = best_reg
        if self.cert_mode == "posterior_prob":
            if best_reg == 0.0:
                self.certified = True
                return
        elif best_reg <= self.epsilon:
            self.certified = True
            return

        # 2. Plan next experiment via selected Acquisition Policy
        self._next_arm_idx = self._select_next_arm(means, psi, stds, beta, u_ell)

    def _select_next_arm(
        self,
        means: np.ndarray,
        psi: np.ndarray,
        stds: np.ndarray,
        beta: float,
        u_ell: np.ndarray,
    ) -> int:
        costs = self.support_struct.costs

        if self.acquisition == "gp_ucb":
            return int(np.argmax(u_ell))

        # Optimistic inside witness w_t* = argmax_{w in Z} u_ell(w) and containing action b_t
        w_star = int(np.argmax(u_ell))
        if self.answer_rule == "greedy_emp":
            b_t = int(np.argmax([float(np.max(means[sup])) for sup in self.support_struct.supports]))
            sup_b = self.support_struct.supports[b_t]
            y_opt = int(sup_b[int(np.argmax(u_ell[sup_b]))])
        else:
            # Prefer action containing w_star with smallest exterior optimistic threat
            containing = [a for a, sup in enumerate(self.support_struct.supports) if w_star in set(sup.tolist())]
            best_sep = -math.inf
            b_t = containing[0]
            for a in containing:
                comp = self.support_struct.complements[a]
                u_out = float(np.max(u_ell[comp])) if len(comp) else -math.inf
                sep = float(u_ell[w_star]) - u_out
                if sep > best_sep:
                    best_sep = sep
                    b_t = a
            y_opt = w_star

        sup_b = self.support_struct.supports[b_t]
        comp_b = self.support_struct.complements[b_t]
        if len(comp_b) == 0:
            return y_opt

        if self.acquisition == "gp_root_info":
            z_box = int(comp_b[int(np.argmax(u_ell[comp_b]))])
            gain_y = float(stds[y_opt]) / costs[y_opt]
            gain_z = float(stds[z_box]) / costs[z_box]
            return y_opt if gain_y >= gain_z else z_box

        if self.acquisition == "bayes_ids":
            # Symmetric-MI Information-Directed Acquisition I(Y_x; A_eps(f) | D_t) / c(x) (Theory T4.4)
            draws = self.model.sample_posterior_values(256, self.rng)  # (S, M)
            v_star = np.max(draws, axis=1, keepdims=True)
            acc_mat = np.zeros((len(draws), self.support_struct.k), dtype=np.uint8)
            for a, sup in enumerate(self.support_struct.supports):
                acc_mat[:, a] = ((v_star[:, 0] - np.max(draws[:, sup], axis=1)) <= self.epsilon + 1e-12).astype(
                    np.uint8
                )
            # Group rows by acceptable-action bitmask
            powers = (1 << np.arange(min(self.support_struct.k, 60), dtype=np.uint64))
            codes = acc_mat[:, : len(powers)] @ powers
            uniq, inv, cnts = np.unique(codes, return_inverse=True, return_counts=True)
            if len(uniq) > 1:
                obs_var = self.model.obs_var
                tot_var = np.maximum(1e-16, np.var(draws, axis=0)) + obs_var
                cond_ent = np.zeros(self.support_struct.m, dtype=np.float64)
                for g_i, c_i in enumerate(cnts):
                    pi_g = float(c_i) / len(draws)
                    sub = draws[inv == g_i]
                    v_g = np.var(sub, axis=0) if c_i > 1 else np.zeros(self.support_struct.m, dtype=np.float64)
                    cond_ent += pi_g * np.log(np.maximum(1e-16, v_g + obs_var))
                mi = np.maximum(0.0, 0.5 * np.log(tot_var) - 0.5 * cond_ent)
                if float(np.max(mi)) > 1e-9:
                    scores = mi / costs
                    chosen = int(np.argmax(scores))
                    if self._is_gp:
                        cert_b = self.ellipsoid_cert.certify_action_gp(b_t, means, psi, beta, stop_if_above_eps=True)
                    else:
                        cert_b = self.ellipsoid_cert.certify_action(
                            b_t, means, psi, self._raw_features, beta, stop_if_above_eps=True
                        )
                    witness_set = set(cert_b.inside_indices.tolist()) | {cert_b.challenger_idx, y_opt}
                    if chosen not in witness_set:
                        self.off_witness_pulls += 1
                    return chosen
            # Fallback to safeguarded contrast when acceptable set has near-zero entropy
            acq_eff = "contrast_directed"
        else:
            acq_eff = self.acquisition

        if self._is_gp:
            cert_b = self.ellipsoid_cert.certify_action_gp(
                b_t, means, psi, beta, stop_if_above_eps=True
            )
            z_t = cert_b.challenger_idx
            g_dual = cert_b.contrast
            g_opt = np.zeros(self.support_struct.m, dtype=np.float64)
            g_opt[z_t] = 1.0
            g_opt[y_opt] = -1.0
        else:
            cert_b = self.ellipsoid_cert.certify_action(
                b_t, means, psi, self._raw_features, beta, stop_if_above_eps=True
            )
            z_t = cert_b.challenger_idx
            g_dual = cert_b.contrast
            g_opt = self._raw_features[z_t] - self._raw_features[y_opt]

        gap_hat_dual = float(means[z_t] - (cert_b.inside_weights @ means[cert_b.inside_indices]))

        if acq_eff == "contrast_naive":
            g_active = g_dual
        else:
            # Certifiability Safeguard (Theorem T4.2): `p_t*` can certify `D_t <= eps` only when its
            # empirical regret `gap_hat_dual <= 0.5 * eps` (which implies `rad_dual > 0.5 * eps` whenever
            # `D_t > eps`). Otherwise `p_t*` sits on a suboptimal inside witness, so switch immediately
            # to the optimistic contrast `g_opt = phi(z_t) - phi(y_opt)`.
            g_active = g_dual if gap_hat_dual <= 0.5 * self.epsilon else g_opt

        if acq_eff == "direct_witness":
            delta_v = self.model.contrast_variance_reduction(g_active)
            cand_w = np.unique(np.append(cert_b.inside_indices, [y_opt, z_t]))
            scores_w = delta_v[cand_w] / costs[cand_w]
            return int(cand_w[int(np.argmax(scores_w))])

        if acq_eff == "maxmin_tracking" and isinstance(self.model, LinearFeatureModel):
            # Plug-in T5 saddle-point design step toward optimal allocation w_t
            w_mat = (self.model.phi.T * self._tracking_weights) @ self.model.phi + 1e-8 * np.eye(self.model.d)
            w_inv = np.linalg.inv(w_mat)
            wg = w_inv @ g_active
            avg_c = float(self._tracking_weights @ costs)
            proj_sq = (self.model.phi @ wg) ** 2
            grad = proj_sq / max(1e-12, avg_c) - 0.15 * costs
            g_max = max(1e-12, float(np.max(np.abs(grad))))
            eta = 0.8 / (math.sqrt(self.calls + 1.0) * g_max)
            lw = np.log(np.maximum(self._tracking_weights, 1e-12)) + eta * grad
            lw -= float(np.max(lw))
            w_new = np.exp(lw)
            self._tracking_weights = 0.96 * (w_new / float(np.sum(w_new))) + 0.04 / self.support_struct.m
            deficit = self._tracking_weights * (self.calls + 1.0) - self.model.arm_counts
            chosen = int(np.argmax(deficit))
            witness_set = set(cert_b.inside_indices.tolist()) | {z_t, y_opt}
            if chosen not in witness_set:
                self.off_witness_pulls += 1
            return chosen

        if acq_eff == "multi_contrast":
            # Urgency-weighted Multi-Contrast Design across top-3 outside challengers + rival action (T4.3)
            total_score = 0.50 * (self.model.contrast_variance_reduction(g_active) / costs)
            # Top-2 additional outside threats against b_t
            comp_scores = (means[comp_b] - float(means[y_opt])) + beta * np.linalg.norm(
                psi[comp_b] - psi[y_opt][None, :], axis=1
            )
            top_pos = np.argsort(-comp_scores)[:3]
            w_sum = 0.0
            extra_score = np.zeros(self.support_struct.m, dtype=np.float64)
            for pos in top_pos:
                z_alt = int(comp_b[int(pos)])
                if z_alt == z_t:
                    continue
                urg = max(0.0, float(comp_scores[int(pos)]) - 0.5 * self.epsilon) ** 2 + 1e-8
                g_alt = self._raw_features[z_alt] - self._raw_features[y_opt]
                extra_score += urg * (self.model.contrast_variance_reduction(g_alt) / costs)
                w_sum += urg
            if w_sum > 0.0:
                total_score += 0.50 * (extra_score / w_sum)
            chosen = int(np.argmax(total_score))
        else:
            # Primary Safeguarded Contrast-Directed acquisition
            delta_v = self.model.contrast_variance_reduction(g_active)
            chosen = int(np.argmax(delta_v / costs))

        witness_set = set(cert_b.inside_indices.tolist()) | {z_t, y_opt}
        if chosen not in witness_set:
            self.off_witness_pulls += 1
        return chosen

    def step(self) -> bool:
        if self.certified or self.conflict:
            return False

        arm_idx = self._next_arm_idx
        leaf = self.support_struct.leaves[arm_idx]
        reward = float(self.oracle.sample(leaf))
        self.calls += 1
        self.total_cost += float(self.support_struct.costs[arm_idx])
        self.distinct_leaves_evaluated.add(leaf)

        self.model.observe(arm_idx, reward)
        if self.cs_monitor is not None:
            self.cs_monitor.step(leaf, reward)
            if self.cs_monitor.evidence.conflict:
                self.conflict = True
                return False

        stride = self.check_every
        if self.adaptive_check:
            if self.calls > 1500:
                stride = max(stride, 30)
            elif self.calls > 400:
                stride = max(stride, 15)
            elif self.calls > 80:
                stride = max(stride, 5)
        if self.calls % stride == 0:
            self._evaluate_certificate_and_plan()
        return not self.conflict


def build_worfbench_feature_matrix(
    problem: Problem,
    include_interactions: bool = True,
) -> np.ndarray:
    """Construct the exact categorical stage main-effects + pairwise-interactions feature matrix
    for WorFBench 4-stage `Qwen3-0.6B` workflows (Experiment E4):

        f(z) = theta_0 + sum_{j=1}^4 theta_{j, z_j} + sum_{1 <= j < k <= 4} theta_{jk, z_j, z_k}.

    Uses orthogonal Helmholtz / sum-to-zero contrasts per 3-choice stage (`2` contrasts/stage),
    yielding `d = 1 + 8 = 9` (main effects) or `d = 1 + 8 + 24 = 33` (main + pairwise interactions).
    """
    from .v6_real_world import WORFBENCH_MODULES

    mod_lookup = [{name: idx for idx, name in enumerate(WORFBENCH_MODULES[s])} for s in range(4)]
    # Orthonormalized 2D contrast coding for a 3-level categorical factor
    stage_code = np.array(
        [
            [-1.0 / math.sqrt(2.0), -1.0 / math.sqrt(6.0)],
            [1.0 / math.sqrt(2.0), -1.0 / math.sqrt(6.0)],
            [0.0, 2.0 / math.sqrt(6.0)],
        ],
        dtype=np.float64,
    )

    rows: list[np.ndarray] = []
    for z in problem.graph.leaves:
        wname = problem.leaf_workflow_name[z]
        parts = wname.split("|")
        cfg = [mod_lookup[s][parts[s]] for s in range(4)]
        main_vecs = [stage_code[cfg[s]] for s in range(4)]
        feats = [np.array([1.0], dtype=np.float64), *main_vecs]
        if include_interactions:
            for j in range(4):
                for k in range(j + 1, 4):
                    feats.append(np.outer(main_vecs[j], main_vecs[k]).reshape(-1) * 0.5)
        rows.append(np.concatenate(feats, axis=0))
    return np.stack(rows, axis=0)
