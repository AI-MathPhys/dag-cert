"""Growing Implicit Search DAGs: Conic Subtree-Envelope Joint Root Certification.

Implements the growing-DAG extension of Joint Root Certification (Appendix M):
  - Theorem M.1 (Exact Shared-Subtree Cancellation & Monotone Expansion):
    For any explored prefix-DAG G_t with boundary B_t = T_t union F_t and action
    boundary supports S_t(a), shared frontier subtrees v in S_t(a) cancel
    unconditionally even under hidden deeper transpositions below F_t.
  - Theorem M.2 (Conic Subtree-Envelope Duality & Dimension-Only Sparsity):
    Given a sound outer feature envelope Phi_hat(v) >= conv{phi(z) : z in L(v)}
    and residual bound xi_bar(v) >= max_{z in L(v)} xi(z), the split-envelope
    conic upper bound U_t(v, W_t(a)) is 100% provably sound, exact on expanded
    terminals T_t, decomposes into statistical contrast radius s_t^stat and
    structural envelope slack s_t^env, and admits an optimal inside witness
    mixture p* with |supp(p*)| <= d + 1 (independent of |Z| and |W_t(a)|).
  - Algorithm M.1 (Growing CD-Joint):
    Interleaves inside-witness safeguard expansion, slack-vs-radius outside
    challenger expansion (parameterized by balance factor eta in [0, inf]), and
    off-witness contrast-directed proxy measurement over expanded terminals T_t.
  - Matched growing-DAG comparators sharing the exact same prefix-DAG, ellipsoid,
    and deterministic per-leaf observation tapes:
      * ``growing_cd_joint``  (Algorithm M.1, configurable ``eta``)
      * ``growing_gp_os``     (shared-subtree conic certifier + LUCB endpoint queries)
      * ``growing_marginal``  (root certification WITHOUT shared-subtree cancellation)
      * ``growing_best_leaf`` (Pelissier et al. 2019-style best-leaf certification)
"""
from __future__ import annotations

from abc import ABC, abstractmethod
from collections import deque
from dataclasses import dataclass, field
import hashlib
import math
import time
from typing import Any, Callable, Hashable, Sequence

import numpy as np
from scipy.stats import chi2 as chi2_dist

from dagcert._core.v7_bayesian_ucd import (
    _solve_small_simplex_afw,
    caratheodory_prune,
)


# ---------------------------------------------------------------------------
# 1. Sound Outer Feature Envelopes (Theorem M.2)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SubtreeEnvelope:
    """Provably sound outer feature envelope Phi_hat(v) >= conv{phi(z) : z in L(v)}.

    Supports three sound representations (which reduce identically to a singleton
    ``{phi(z)}`` with zero slack on expanded terminals):
      1. ``kind == "point"``: Exact terminal feature vector ``center = phi(z)``.
      2. ``kind == "box"``: Axis-aligned box ``[box_lo, box_hi]`` with midpoint
         ``center = 0.5 * (box_lo + box_hi)`` and half-widths
         ``box_half = 0.5 * (box_hi - box_lo)``.
      3. ``kind == "group_sparse"``: Base vector ``base`` plus at most ``max_groups``
         (or exact ``max_groups`` when ``exact_count=True``) choices, at most one
         vector per group in ``groups`` (tuple of 2-D arrays ``(n_i, d)``), plus
         an optional residual axis-aligned box ``[-extra_half, +extra_half]`` for
         pairwise / higher-order interactions among remaining groups.

    An optional deterministic ``scalar_upper`` upper-bounds ``max_{z in L(v)} mu(z)``
    (e.g., exact combinatorial ceiling in SameGame lookahead).
    """

    kind: str
    center: np.ndarray
    residual: float = 0.0
    box_half: np.ndarray | None = None
    groups: tuple[np.ndarray, ...] | None = None
    group_mat: np.ndarray | None = None  # Fast uniform-shape (m, a, d) cache when all groups share len
    max_groups: int = 0
    exact_count: bool = False
    extra_half: np.ndarray | None = None
    scalar_upper: float = math.inf

    @staticmethod
    def point(phi: np.ndarray, residual: float = 0.0, scalar_upper: float = math.inf) -> "SubtreeEnvelope":
        vec = np.asarray(phi, dtype=np.float64)
        return SubtreeEnvelope(
            kind="point",
            center=vec,
            residual=float(max(0.0, residual)),
            scalar_upper=float(scalar_upper),
        )

    @staticmethod
    def box(
        lo: np.ndarray,
        hi: np.ndarray,
        residual: float = 0.0,
        scalar_upper: float = math.inf,
    ) -> "SubtreeEnvelope":
        lo_a = np.asarray(lo, dtype=np.float64)
        hi_a = np.asarray(hi, dtype=np.float64)
        hi_a = np.maximum(lo_a, hi_a)
        center = 0.5 * (lo_a + hi_a)
        half = 0.5 * (hi_a - lo_a)
        if float(np.max(half)) <= 1e-15:
            return SubtreeEnvelope.point(center, residual=residual, scalar_upper=scalar_upper)
        return SubtreeEnvelope(
            kind="box",
            center=center,
            residual=float(max(0.0, residual)),
            box_half=half,
            scalar_upper=float(scalar_upper),
        )

    @staticmethod
    def group_sparse(
        base: np.ndarray,
        groups: Sequence[np.ndarray],
        max_groups: int,
        *,
        exact_count: bool = False,
        extra_half: np.ndarray | None = None,
        residual: float = 0.0,
        scalar_upper: float = math.inf,
    ) -> "SubtreeEnvelope":
        base_a = np.asarray(base, dtype=np.float64)
        d = len(base_a)
        grp_tuple = tuple(np.atleast_2d(np.asarray(g, dtype=np.float64)) for g in groups if len(g) > 0)
        r = min(int(max_groups), len(grp_tuple))
        eh = (
            np.maximum(0.0, np.asarray(extra_half, dtype=np.float64))
            if extra_half is not None
            else np.zeros(d, dtype=np.float64)
        )
        if r <= 0 and float(np.max(eh)) <= 1e-15:
            return SubtreeEnvelope.point(base_a, residual=residual, scalar_upper=scalar_upper)

        # When every remaining group must be chosen (e.g., fixed-stage workflow / commuting lattice
        # where remaining stages = r), shift each group around its coordinate midpoint to halve
        # the displacement radius while preserving 100% soundness.
        if exact_count and r == len(grp_tuple) and r > 0:
            shifted_groups: list[np.ndarray] = []
            shift_sum = np.zeros(d, dtype=np.float64)
            box_lo = base_a.copy()
            box_hi = base_a.copy()
            for g in grp_tuple:
                g_lo = np.min(g, axis=0)
                g_hi = np.max(g, axis=0)
                mid = 0.5 * (g_lo + g_hi)
                shift_sum += mid
                shifted_groups.append(g - mid[None, :])
                box_lo += g_lo
                box_hi += g_hi
            center = base_a + shift_sum
            box_half = 0.5 * (box_hi - box_lo) + eh
            s_tuple = tuple(shifted_groups)
            gmat = (
                np.stack(s_tuple, axis=0)
                if len({g.shape[0] for g in s_tuple}) == 1
                else None
            )
            return SubtreeEnvelope(
                kind="group_sparse",
                center=center,
                residual=float(max(0.0, residual)),
                box_half=box_half,
                groups=s_tuple,
                group_mat=gmat,
                max_groups=r,
                exact_count=True,
                extra_half=eh if float(np.max(eh)) > 1e-15 else None,
                scalar_upper=float(scalar_upper),
            )

        # General k-remaining sparse envelope: center at base
        gmat = (
            np.stack(grp_tuple, axis=0)
            if len(grp_tuple) > 0 and len({g.shape[0] for g in grp_tuple}) == 1
            else None
        )
        return SubtreeEnvelope(
            kind="group_sparse",
            center=base_a,
            residual=float(max(0.0, residual)),
            box_half=None,
            groups=grp_tuple,
            group_mat=gmat,
            max_groups=r,
            exact_count=bool(exact_count),
            extra_half=eh if float(np.max(eh)) > 1e-15 else None,
            scalar_upper=float(scalar_upper),
        )

    def linear_max(self, theta: np.ndarray) -> float:
        """Exact support function ``max_{phi in Phi_hat(v)} phi^T theta``."""
        c_val = float(self.center @ theta)
        if self.kind == "point":
            return c_val
        if self.kind == "box":
            assert self.box_half is not None
            return c_val + float(self.box_half @ np.abs(theta))
        # group_sparse
        assert self.groups is not None
        r = self.max_groups
        extra = float(self.extra_half @ np.abs(theta)) if self.extra_half is not None else 0.0
        if r <= 0:
            return c_val + extra
        scores = np.array([float(np.max(g @ theta)) for g in self.groups], dtype=np.float64)
        if self.exact_count:
            if r >= len(scores):
                return c_val + float(np.sum(scores)) + extra
            top_r = np.partition(scores, len(scores) - r)[len(scores) - r :]
            return c_val + float(np.sum(top_r)) + extra
        pos = scores[scores > 0.0]
        if len(pos) == 0:
            return c_val + extra
        if r >= len(pos):
            return c_val + float(np.sum(pos)) + extra
        top_r = np.partition(pos, len(pos) - r)[len(pos) - r :]
        return c_val + float(np.sum(top_r)) + extra

    def optimistic_vertex_and_slack(
        self,
        theta_hat: np.ndarray,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        beta: float,
    ) -> tuple[np.ndarray, float, float]:
        """Compute an optimistic center ``phi_opt in Phi_hat(v)`` and 100% provably sound
        optimality-margin slack ``s_opt >= max_{phi in Phi_hat(v)} [(phi - phi_opt)^T theta_hat + beta ||phi - phi_opt||_{V^{-1}}]``.

        Returns ``(phi_opt, s_opt, lin_max)`` where ``lin_max = phi_opt @ theta_hat``.
        Crucially, ``s_opt`` self-collapses to ``0.0`` once ``V_t^{-1}`` identifies the
        best choices within ``Phi_hat(v)``, enabling depth-1 pruning of exponentially large
        dominated subtrees without ever expanding them (Theorem M.2(b)).
        """
        if self.kind == "point":
            return self.center, 0.0, float(self.center @ theta_hat)

        if self.kind == "box":
            assert self.box_half is not None
            sgn = np.where(theta_hat >= 0.0, 1.0, -1.0)
            phi_opt = self.center + sgn * self.box_half
            # Box width w_j = 2 * half_j; every delta_j in [0, w_j] pays -delta_j |theta_j| + beta delta_j sqrt(V^{-1}_{jj})
            margins = np.maximum(0.0, beta * v_inv_diag_sqrt - np.abs(theta_hat))
            s_opt = float((2.0 * self.box_half) @ margins)
            return phi_opt, s_opt, float(phi_opt @ theta_hat)

        # group_sparse
        assert self.groups is not None
        r = self.max_groups
        d = len(self.center)
        phi_opt = self.center.copy()
        s_opt = 0.0
        if self.extra_half is not None:
            sgn = np.where(theta_hat >= 0.0, 1.0, -1.0)
            phi_opt = phi_opt + sgn * self.extra_half
            margins = np.maximum(0.0, beta * v_inv_diag_sqrt - np.abs(theta_hat))
            s_opt += float((2.0 * self.extra_half) @ margins)

        if r <= 0:
            return phi_opt, s_opt, float(phi_opt @ theta_hat)

        if self.group_mat is not None:
            # Vectorized fast path for uniform-size groups: group_mat has shape (m, a, d)
            gmat = self.group_mat
            m, a_cnt, _ = gmat.shape
            all_sc = gmat @ theta_hat  # (m, a)
            best_a = np.argmax(all_sc, axis=1)  # (m,)
            best_scores = all_sc[np.arange(m), best_a]  # (m,)
            best_vecs = gmat[np.arange(m), best_a]  # (m, d)
            wg_all = gmat @ l_t.T  # (m, a, d)

            if self.exact_count:
                order = np.argsort(-best_scores, kind="mergesort")
                s_star = order[:r]
                s_out = order[r:]
                phi_opt = phi_opt + np.sum(best_vecs[s_star], axis=0)
                tau = float(best_scores[s_star[-1]])

                if a_cnt > 1:
                    diffs_w = wg_all[s_star] - wg_all[s_star, best_a[s_star]][:, None, :]  # (r, a, d)
                    lin_d = all_sc[s_star] - best_scores[s_star][:, None]  # (r, a)
                    norm_d = np.linalg.norm(diffs_w, axis=2)  # (r, a)
                    omega_in = np.maximum(0.0, np.max(lin_d + beta * norm_d, axis=1))
                else:
                    omega_in = np.zeros(len(s_star), dtype=np.float64)
                gv_norms = np.linalg.norm(wg_all[s_star, best_a[s_star]], axis=1)
                gamma_tilde = (tau - best_scores[s_star]) + beta * gv_norms - omega_in
                s_opt += float(np.sum(omega_in))

                if len(s_out) > 0:
                    norm_out = np.linalg.norm(wg_all[s_out], axis=2)  # (m-r, a)
                    alpha_out = np.max((all_sc[s_out] - tau) + beta * norm_out, axis=1)
                    alpha_sorted = np.sort(alpha_out)[::-1]
                    gamma_sorted = np.sort(gamma_tilde)[::-1]
                    q_max = min(len(alpha_sorted), len(gamma_sorted))
                    s_opt += float(np.sum(np.maximum(0.0, alpha_sorted[:q_max] + gamma_sorted[:q_max])))
                return phi_opt, s_opt, float(phi_opt @ theta_hat)

            # Vectorized exact_count == False
            pos_mask = best_scores > 0.0
            pos_idx = np.flatnonzero(pos_mask)
            if len(pos_idx) > r:
                pos_order = pos_idx[np.argsort(-best_scores[pos_idx], kind="mergesort")]
                s_star_real = pos_order[:r]
                n_zero_in = 0
                s_out_real = np.concatenate([pos_order[r:], np.flatnonzero(~pos_mask)])
                tau = float(best_scores[s_star_real[-1]])
            else:
                s_star_real = pos_idx
                n_zero_in = r - len(s_star_real)
                s_out_real = np.flatnonzero(~pos_mask)
                tau = 0.0

            if len(s_star_real) > 0:
                phi_opt = phi_opt + np.sum(best_vecs[s_star_real], axis=0)
                if a_cnt > 1:
                    diffs_w = wg_all[s_star_real] - wg_all[s_star_real, best_a[s_star_real]][:, None, :]
                    lin_d = all_sc[s_star_real] - best_scores[s_star_real][:, None]
                    omega_real = np.maximum(0.0, np.max(lin_d + beta * np.linalg.norm(diffs_w, axis=2), axis=1))
                else:
                    omega_real = np.zeros(len(s_star_real), dtype=np.float64)
                gv_norms = np.linalg.norm(wg_all[s_star_real, best_a[s_star_real]], axis=1)
                gamma_real = (tau - best_scores[s_star_real]) + beta * gv_norms - omega_real
                s_opt += float(np.sum(omega_real))
            else:
                gamma_real = np.empty(0, dtype=np.float64)

            gamma_all = (
                np.concatenate([gamma_real, np.full(n_zero_in, tau, dtype=np.float64)])
                if n_zero_in > 0
                else gamma_real
            )
            if len(s_out_real) > 0:
                norm_out = np.linalg.norm(wg_all[s_out_real], axis=2)
                alpha_real = np.max((all_sc[s_out_real] - tau) + beta * norm_out, axis=1)
            else:
                alpha_real = np.empty(0, dtype=np.float64)
            n_zero_out = r - n_zero_in
            alpha_all = (
                np.concatenate([alpha_real, np.full(n_zero_out, -tau, dtype=np.float64)])
                if n_zero_out > 0
                else alpha_real
            )
            if len(alpha_all) > 0 and len(gamma_all) > 0:
                alpha_sorted = np.sort(alpha_all)[::-1]
                gamma_sorted = np.sort(gamma_all)[::-1]
                q_max = min(len(alpha_sorted), len(gamma_sorted))
                s_opt += float(np.sum(np.maximum(0.0, alpha_sorted[:q_max] + gamma_sorted[:q_max])))
            return phi_opt, s_opt, float(phi_opt @ theta_hat)

        m = len(self.groups)
        best_vecs = np.empty((m, d), dtype=np.float64)
        best_scores = np.empty(m, dtype=np.float64)
        for i, g in enumerate(self.groups):
            sc = g @ theta_hat
            bi = int(np.argmax(sc))
            best_vecs[i] = g[bi]
            best_scores[i] = float(sc[bi])

        if self.exact_count:
            order = np.argsort(-best_scores, kind="mergesort")
            s_star = order[:r]
            s_out = order[r:]
            for idx in s_star:
                phi_opt = phi_opt + best_vecs[idx]
            tau = float(best_scores[s_star[-1]])

            # Within-group optimality slack omega_i for i in S*
            omega_in = np.zeros(len(s_star), dtype=np.float64)
            gamma_tilde = np.empty(len(s_star), dtype=np.float64)
            for k_i, idx in enumerate(s_star):
                g = self.groups[int(idx)]
                gv = best_vecs[idx]
                if len(g) > 1:
                    diffs = g - gv[None, :]
                    lin_d = diffs @ theta_hat
                    norm_d = np.linalg.norm(diffs @ l_t.T, axis=1)
                    omega_in[k_i] = max(0.0, float(np.max(lin_d + beta * norm_d)))
                gv_norm = float(np.linalg.norm(l_t @ gv))
                gamma_i = (tau - float(best_scores[idx])) + beta * gv_norm
                gamma_tilde[k_i] = gamma_i - omega_in[k_i]

            s_opt += float(np.sum(omega_in))
            if len(s_out) > 0:
                alpha_out = np.empty(len(s_out), dtype=np.float64)
                for k_j, idx in enumerate(s_out):
                    g = self.groups[int(idx)]
                    lin_g = (g @ theta_hat) - tau
                    norm_g = np.linalg.norm(g @ l_t.T, axis=1)
                    alpha_out[k_j] = float(np.max(lin_g + beta * norm_g))
                alpha_sorted = np.sort(alpha_out)[::-1]
                gamma_sorted = np.sort(gamma_tilde)[::-1]
                q_max = min(len(alpha_sorted), len(gamma_sorted))
                pair_gains = alpha_sorted[:q_max] + gamma_sorted[:q_max]
                s_opt += float(np.sum(np.maximum(0.0, pair_gains)))
            return phi_opt, s_opt, float(phi_opt @ theta_hat)

        # exact_count == False: augment conceptually with r dummy zero groups (score 0, norm 0)
        # Positive real groups compete with the r zero slots; S* takes top-r among (real + r zeros).
        pos_mask = best_scores > 0.0
        pos_idx = np.flatnonzero(pos_mask)
        if len(pos_idx) > r:
            pos_order = pos_idx[np.argsort(-best_scores[pos_idx], kind="mergesort")]
            s_star_real = pos_order[:r]
            n_zero_in = 0
            s_out_real = np.concatenate([pos_order[r:], np.flatnonzero(~pos_mask)])
            tau = float(best_scores[s_star_real[-1]])
        else:
            s_star_real = pos_idx
            n_zero_in = r - len(s_star_real)
            s_out_real = np.flatnonzero(~pos_mask)
            tau = 0.0

        for idx in s_star_real:
            phi_opt = phi_opt + best_vecs[idx]

        omega_list: list[float] = []
        gamma_list: list[float] = []
        for idx in s_star_real:
            g = self.groups[int(idx)]
            gv = best_vecs[idx]
            om = 0.0
            if len(g) > 1:
                diffs = g - gv[None, :]
                lin_d = diffs @ theta_hat
                norm_d = np.linalg.norm(diffs @ l_t.T, axis=1)
                om = max(0.0, float(np.max(lin_d + beta * norm_d)))
            omega_list.append(om)
            gv_norm = float(np.linalg.norm(l_t @ gv))
            gamma_list.append((tau - float(best_scores[idx])) + beta * gv_norm - om)
        # Dummy zero groups in S* have score 0, norm 0, omega 0 -> gamma = tau - 0 + 0 = tau (= 0)
        for _ in range(n_zero_in):
            gamma_list.append(tau)

        s_opt += float(sum(omega_list))
        alpha_list: list[float] = []
        for idx in s_out_real:
            g = self.groups[int(idx)]
            lin_g = (g @ theta_hat) - tau
            norm_g = np.linalg.norm(g @ l_t.T, axis=1)
            alpha_list.append(float(np.max(lin_g + beta * norm_g)))
        # Remaining (r - n_zero_in) dummy zero groups sit in S_out: score 0, norm 0 -> alpha = -tau
        for _ in range(r - n_zero_in):
            alpha_list.append(-tau)

        if alpha_list and gamma_list:
            alpha_sorted = np.sort(np.array(alpha_list, dtype=np.float64))[::-1]
            gamma_sorted = np.sort(np.array(gamma_list, dtype=np.float64))[::-1]
            q_max = min(len(alpha_sorted), len(gamma_sorted))
            s_opt += float(np.sum(np.maximum(0.0, alpha_sorted[:q_max] + gamma_sorted[:q_max])))

        return phi_opt, s_opt, float(phi_opt @ theta_hat)

    def worst_displacement(self, l_t: np.ndarray) -> np.ndarray:
        """Return a displacement vector ``delta in Delta_v`` with large ``||l_t @ delta||_2``
        for contrast-directed shrinking of the statistical envelope radius ``R_{V^{-1}}(Delta_v)``."""
        d = len(self.center)
        if self.kind == "point":
            return np.zeros(d, dtype=np.float64)
        if self.kind == "box":
            assert self.box_half is not None
            # Pick coordinate with largest half_j * ||l_t[:, j]||_2 (or top-eigenvector sign alignment)
            col_norms = np.linalg.norm(l_t, axis=0) * self.box_half
            j_star = int(np.argmax(col_norms))
            vec = np.zeros(d, dtype=np.float64)
            vec[j_star] = float(self.box_half[j_star])
            return vec
        assert self.groups is not None
        best_vec = np.zeros(d, dtype=np.float64)
        best_n = -1.0
        for g in self.groups:
            wg = g @ l_t.T
            norms = np.linalg.norm(wg, axis=1)
            idx = int(np.argmax(norms))
            if float(norms[idx]) > best_n:
                best_n = float(norms[idx])
                best_vec = g[idx]
        if self.extra_half is not None:
            col_norms = np.linalg.norm(l_t, axis=0) * self.extra_half
            j_star = int(np.argmax(col_norms))
            if float(col_norms[j_star]) > best_n:
                vec = np.zeros(d, dtype=np.float64)
                vec[j_star] = float(self.extra_half[j_star])
                return vec
        return best_vec

    def mahalanobis_radius(
        self,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        eigmax_sqrt: float,
    ) -> float:
        """Provably sound upper bound ``R_{V^{-1}}(Delta_v) >= max_{phi in Phi_hat(v)} ||phi - center||_{V^{-1}}``.

        ``l_t`` satisfies ``V^{-1} = L L^T`` with ``l_t = L^T`` so ``||x||_{V^{-1}} = ||l_t @ x||_2``.
        """
        if self.kind == "point":
            return 0.0
        if self.kind == "box":
            assert self.box_half is not None
            return _sound_box_radius(self.box_half, l_t, v_inv_diag_sqrt, eigmax_sqrt)

        # group_sparse
        assert self.groups is not None
        r = self.max_groups
        extra_r = (
            _sound_box_radius(self.extra_half, l_t, v_inv_diag_sqrt, eigmax_sqrt)
            if self.extra_half is not None
            else 0.0
        )
        if r <= 0:
            return extra_r
        # Per-group max Mahalanobis norm of any vector in the group
        grp_norms = np.empty(len(self.groups), dtype=np.float64)
        for i, g in enumerate(self.groups):
            # g has shape (n_i, d); whitened is (n_i, d) via g @ l_t.T
            wg = g @ l_t.T
            grp_norms[i] = float(np.max(np.linalg.norm(wg, axis=1)))
        if r >= len(grp_norms):
            sparse_r = float(np.sum(grp_norms)) + extra_r
        else:
            top_r = np.partition(grp_norms, len(grp_norms) - r)[len(grp_norms) - r :]
            sparse_r = float(np.sum(top_r)) + extra_r

        if self.box_half is not None:
            box_r = _sound_box_radius(self.box_half, l_t, v_inv_diag_sqrt, eigmax_sqrt)
            return min(sparse_r, box_r)
        return sparse_r


def _sound_box_radius(
    half: np.ndarray,
    l_t: np.ndarray,
    v_inv_diag_sqrt: np.ndarray,
    eigmax_sqrt: float,
) -> float:
    """100% sound upper bound on ``max_{|delta| <= half} ||l_t @ delta||_2``.

    Takes the minimum of three provably sound matrix-norm inequalities:
      1. Column triangle inequality: ``sum_j half_j * ||l_t[:, j]||_2``
      2. Spectral norm bound:        ``sqrt(lambda_max(V^{-1})) * ||half||_2``
      3. Row-l1 bound:               ``|| |l_t| @ half ||_2``
    """
    b1 = float(half @ v_inv_diag_sqrt)
    b2 = eigmax_sqrt * float(np.linalg.norm(half))
    b3 = float(np.linalg.norm(np.abs(l_t) @ half))
    return min(b1, b2, b3)


# ---------------------------------------------------------------------------
# 2. Implicit DAG Interface & Growing Prefix-DAG with Transposition Merging
# ---------------------------------------------------------------------------


def vectorized_group_sparse_opt_stats(
    site_vecs: np.ndarray,
    bases: np.ndarray,
    used_masks: np.ndarray,
    rems: np.ndarray,
    theta_hat: np.ndarray,
    l_t: np.ndarray,
    beta: float,
    step_cache: dict[str, Any],
    cache_key: str = "vec_gs_tbl",
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Exact vectorized computation of ``(phi_opt, s_opt, lin_max)`` for a batch of
    ``exact_count=True`` group-sparse states sharing site-variant tensor ``site_vecs (L, V, d)``.

    Produces bit-for-bit (<1e-14) parity with ``SubtreeEnvelope.optimistic_vertex_and_slack``
    at ~200x--500x speedup across large frontiers.
    """
    tbl = step_cache.get(cache_key)
    if tbl is None:
        n_sites, n_vars, _ = site_vecs.shape
        all_sc = site_vecs @ theta_hat  # (L, V)
        best_v = np.argmax(all_sc, axis=1)
        idx_l = np.arange(n_sites)
        best_sc = all_sc[idx_l, best_v]
        best_vecs = site_vecs[idx_l, best_v]
        wg = site_vecs @ l_t.T  # (L, V, d)
        wg_best = wg[idx_l, best_v]
        gv_norms = np.linalg.norm(wg_best, axis=1)
        if n_vars > 1:
            diffs_w = wg - wg_best[:, None, :]
            lin_d = all_sc - best_sc[:, None]
            omega_site = np.maximum(0.0, np.max(lin_d + beta * np.linalg.norm(diffs_w, axis=2), axis=1))
        else:
            omega_site = np.zeros(n_sites, dtype=np.float64)
        norm_all = np.linalg.norm(wg, axis=2)
        site_max_u = np.max(all_sc + beta * norm_all, axis=1)
        order = np.argsort(-best_sc, kind="mergesort")
        tbl = (
            order,
            best_sc[order],
            best_vecs[order],
            gv_norms[order],
            omega_site[order],
            site_max_u[order],
        )
        step_cache[cache_key] = tbl

    order, best_sc_o, best_vecs_o, gv_norms_o, omega_o, site_max_u_o = tbl
    avail = ~used_masks[:, order]  # (N, L)
    rank = np.cumsum(avail, axis=1)  # (N, L)
    in_star = avail & (rank <= rems[:, None])
    in_out = avail & (rank > rems[:, None])

    phi_opts = bases + in_star.astype(np.float64) @ best_vecs_o
    lin_maxs = phi_opts @ theta_hat

    last_idx = np.argmax(in_star & (rank == rems[:, None]), axis=1)
    tau = best_sc_o[last_idx]  # (N,)

    s_opts = in_star.astype(np.float64) @ omega_o
    if np.any(in_out):
        gamma_mat = np.where(
            in_star,
            (tau[:, None] - best_sc_o[None, :]) + beta * gv_norms_o[None, :] - omega_o[None, :],
            -1e30,
        )
        alpha_mat = np.where(in_out, site_max_u_o[None, :] - tau[:, None], -1e30)
        g_s = np.sort(gamma_mat, axis=1)[:, ::-1]
        a_s = np.sort(alpha_mat, axis=1)[:, ::-1]
        s_opts = s_opts + np.sum(np.maximum(0.0, a_s + g_s), axis=1)
    return phi_opts, s_opts, lin_maxs


class ImplicitDAG(ABC):
    """Abstract interface for an exponentially large implicit all-MAX search DAG."""

    @property
    @abstractmethod
    def feature_dim(self) -> int:
        """Fixed feature dimension ``d``."""

    @property
    @abstractmethod
    def n_root_actions(self) -> int:
        """Number of root actions ``K``."""

    @property
    @abstractmethod
    def total_leaf_count(self) -> int:
        """Exact or combinatorial count ``|Z|`` of reachable terminals (for reporting only)."""

    @abstractmethod
    def root_state(self) -> Hashable:
        """Canonical hashable identifier of the root state ``r``."""

    @abstractmethod
    def root_children(self) -> list[Hashable]:
        """Ordered list of length ``K`` giving the child state ``c_a`` of each root action."""

    @abstractmethod
    def is_terminal(self, state: Hashable) -> bool:
        """Whether ``state`` is a terminal leaf in ``Z``."""

    @abstractmethod
    def expand(self, state: Hashable) -> list[Hashable]:
        """Return canonical child states of non-terminal ``state``."""

    @abstractmethod
    def envelope(self, state: Hashable) -> SubtreeEnvelope:
        """Return a provably sound ``SubtreeEnvelope`` for ``state``."""

    def fast_optimistic_stats(
        self,
        state: Hashable,
        theta_hat: np.ndarray,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        beta: float,
        step_cache: dict[str, Any],
    ) -> tuple[np.ndarray, float, float] | None:
        """Optional fast exact equivalent of ``envelope(state).optimistic_vertex_and_slack(...)``
        that reuses per-step precomputed group scores/norms stored in ``step_cache`` (cleared
        automatically whenever ``posterior.n_obs`` or ``beta`` changes). Return ``None`` to use
        the generic ``SubtreeEnvelope.optimistic_vertex_and_slack`` path.
        """
        return None

    def batch_optimistic_stats(
        self,
        states: Sequence[Hashable],
        theta_hat: np.ndarray,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        beta: float,
        step_cache: dict[str, Any],
    ) -> tuple[np.ndarray, np.ndarray, np.ndarray] | None:
        """Optional vectorized exact equivalent of ``fast_optimistic_stats`` over a batch of
        non-terminal frontier states. Returns ``(phi_opts (N,d), s_opts (N,), lin_maxs (N,))``
        or ``None`` to fall back to per-node evaluation."""
        return None

    def leaf_cost(self, state: Hashable) -> float:
        """Evaluation cost ``c(z) > 0`` of querying terminal ``state`` (default 1.0)."""
        return 1.0

    def greedy_child_hint(self, state: Hashable, children: Sequence[Hashable], theta_hat: np.ndarray) -> Hashable:
        """Pick one promising child during initial root-to-leaf descent."""
        best_c = children[0]
        best_v = -math.inf
        for c in children:
            val = self.envelope(c).linear_max(theta_hat)
            if val > best_v:
                best_v = val
                best_c = c
        return best_c

    @abstractmethod
    def true_mean(self, state: Hashable) -> float:
        """True noiseless mean ``mu(z)`` of a terminal state ``z`` (used for oracle & evaluation)."""

    @abstractmethod
    def true_root_values(self) -> np.ndarray:
        """Length-``K`` array of true root values ``V(a) = max_{z in S(a)} mu(z)`` for regret audit."""

    def observe(self, state: Hashable, obs_std: float, seed: int, call_idx: int) -> float:
        """Deterministic paired-tape noisy observation of terminal ``state``.

        Keyed solely by ``(seed, canonical_state, call_idx)`` so every policy sees the
        exact same observation tape whenever it queries the same terminal ``state``.
        """
        mu = self.true_mean(state)
        if obs_std <= 0.0:
            return mu
        h = hashlib.blake2b(f"{seed}|{state!r}|{call_idx}".encode("utf-8"), digest_size=8).digest()
        sub_seed = int.from_bytes(h, "little")
        rng = np.random.default_rng(sub_seed)
        return float(mu + obs_std * rng.standard_normal())


class GrowingPrefixDAG:
    """Incrementally expanded prefix-DAG G_t with canonical transposition merging.

    Maintains:
      - ``state_to_id`` / ``id_to_state`` canonical node registry (0 = root, 1..K = root children)
      - ``expanded`` (I_t), ``terminals`` (T_t), ``frontier`` (F_t)
      - ``action_mask[nid]``: Python int bitmask of root actions ``a in {0..K-1}`` that can reach
        node ``nid`` in the current prefix-DAG ``G_t``. Updated incrementally in exact BFS
        whenever a new edge or transposition merge occurs!
    """

    def __init__(self, problem: ImplicitDAG) -> None:
        self.problem = problem
        self.k = problem.n_root_actions
        self.d = problem.feature_dim

        self.id_to_state: list[Hashable] = []
        self.state_to_id: dict[Hashable, int] = {}
        self.children: list[list[int]] = []
        self.envelopes: list[SubtreeEnvelope] = []
        self.is_term: list[bool] = []
        self.is_exp: list[bool] = []
        self.action_mask: list[int] = []

        self.terminals: list[int] = []
        self.frontier: set[int] = set()
        self.transposition_merges: int = 0
        self.n_expansions: int = 0

        # Materialize root and its K children
        root_id = self._register(problem.root_state(), mask=0)
        assert root_id == 0
        self.is_exp[0] = True
        self.frontier.discard(0)

        self.root_action_nodes: list[int] = []
        for a, c_state in enumerate(problem.root_children()):
            cid = self._register(c_state, mask=(1 << a))
            self.children[0].append(cid)
            self.root_action_nodes.append(cid)

    def _register(self, state: Hashable, mask: int) -> int:
        existing = self.state_to_id.get(state)
        if existing is not None:
            self.transposition_merges += 1
            self._propagate_mask(existing, mask)
            return existing
        nid = len(self.id_to_state)
        self.state_to_id[state] = nid
        self.id_to_state.append(state)
        self.children.append([])
        env = self.problem.envelope(state)
        self.envelopes.append(env)
        term = self.problem.is_terminal(state)
        self.is_term.append(term)
        self.is_exp.append(False)
        self.action_mask.append(mask)
        if term:
            self.terminals.append(nid)
        else:
            self.frontier.add(nid)
        return nid

    def _propagate_mask(self, start_id: int, add_mask: int) -> None:
        if (self.action_mask[start_id] | add_mask) == self.action_mask[start_id]:
            return
        q = deque([start_id])
        while q:
            u = q.popleft()
            new_m = self.action_mask[u] | add_mask
            if new_m == self.action_mask[u]:
                continue
            self.action_mask[u] = new_m
            for ch in self.children[u]:
                if (self.action_mask[ch] | add_mask) != self.action_mask[ch]:
                    q.append(ch)

    def expand_node(self, nid: int) -> list[int]:
        """Expand frontier node ``nid`` into its canonical children with transposition merging."""
        if self.is_exp[nid] or self.is_term[nid]:
            return self.children[nid]
        state = self.id_to_state[nid]
        mask = self.action_mask[nid]
        ch_states = self.problem.expand(state)
        self.is_exp[nid] = True
        self.frontier.discard(nid)
        self.n_expansions += 1
        out: list[int] = []
        seen_local: set[int] = set()
        for cs in ch_states:
            cid = self._register(cs, mask=mask)
            if cid not in seen_local:
                seen_local.add(cid)
                self.children[nid].append(cid)
                out.append(cid)
        return out

    def greedy_descent_to_leaf(self, start_id: int, theta_hat: np.ndarray, max_extra_exp: int) -> tuple[int, int]:
        """Descend one greedy path from frontier node ``start_id`` to a terminal leaf (at most D steps)."""
        cur = start_id
        start_exp = self.n_expansions
        steps = 0
        while not self.is_term[cur] and (self.n_expansions - start_exp) < max_extra_exp and steps < 64:
            steps += 1
            ch_ids = self.expand_node(cur)
            if not ch_ids:
                break
            term_ch = [c for c in ch_ids if self.is_term[c]]
            if term_ch:
                cur = max(term_ch, key=lambda c: float(self.envelopes[c].center @ theta_hat))
                break
            ch_states = [self.id_to_state[c] for c in ch_ids]
            pick_state = self.problem.greedy_child_hint(self.id_to_state[cur], ch_states, theta_hat)
            cur = self.state_to_id[pick_state]
        return cur, self.n_expansions - start_exp

    def ensure_initial_witnesses(self, theta_init: np.ndarray) -> list[int]:
        """Ensure every root action ``a`` reaches at least one expanded terminal in ``W_0(a)``."""
        initial_leaves: list[int] = []
        for a in range(self.k):
            bit = 1 << a
            existing_w = [tid for tid in self.terminals if self.action_mask[tid] & bit]
            if existing_w:
                initial_leaves.append(existing_w[0])
                continue
            cur = self.root_action_nodes[a]
            while not self.is_term[cur]:
                ch_ids = self.expand_node(cur)
                if not ch_ids:
                    break
                # Check if any child is already a terminal
                term_ch = [c for c in ch_ids if self.is_term[c]]
                if term_ch:
                    cur = term_ch[0]
                    break
                ch_states = [self.id_to_state[c] for c in ch_ids]
                pick_state = self.problem.greedy_child_hint(self.id_to_state[cur], ch_states, theta_init)
                cur = self.state_to_id[pick_state]
            if self.is_term[cur]:
                initial_leaves.append(cur)
        return initial_leaves

    @property
    def n_nodes(self) -> int:
        return len(self.id_to_state)

    @property
    def boundary_ids(self) -> list[int]:
        return list(self.terminals) + sorted(self.frontier)

    def action_witness_terminals(self, action: int) -> list[int]:
        bit = 1 << action
        return [tid for tid in self.terminals if self.action_mask[tid] & bit]

    def action_inside_frontier(self, action: int) -> list[int]:
        bit = 1 << action
        return [fid for fid in self.frontier if self.action_mask[fid] & bit]

    def action_excluded_boundary(self, action: int) -> list[int]:
        bit = 1 << action
        out = [tid for tid in self.terminals if not (self.action_mask[tid] & bit)]
        out.extend(fid for fid in self.frontier if not (self.action_mask[fid] & bit))
        return out

    def action_all_boundary(self, action: int) -> list[int]:
        bit = 1 << action
        out = [tid for tid in self.terminals if (self.action_mask[tid] & bit)]
        out.extend(fid for fid in self.frontier if (self.action_mask[fid] & bit))
        return out


# ---------------------------------------------------------------------------
# 3. Fixed-Dimension O(d^2) Linear / Bounded-Residual Sequential Ellipsoid
# ---------------------------------------------------------------------------


class GrowingLinearPosterior:
    """Dimension-only O(d^2) sequential confidence ellipsoid in R^d (independent of |Z|).

    Supports:
      - ``ellipsoid_mode == "abbasi_yadkori"``: Anytime-valid frequentist self-normalized
        ellipsoid with exact Lattimore-Szepesvari-Weisz bounded-residual inflation
        (Theorem M.3(a) & Appendix C.1).
      - ``ellipsoid_mode == "credible"``: Fixed-dimension Gaussian credible ellipsoid
        ``beta = sigma * sqrt(chi2_{d, 1-delta})`` (+ residual inflation when ``xi > 0``).
    """

    def __init__(
        self,
        d: int,
        *,
        obs_std: float = 0.15,
        prior_lambda: float = 1.0,
        prior_mean: np.ndarray | None = None,
        theta_norm_bound: float = 2.0,
        delta: float = 0.05,
        ellipsoid_mode: str = "abbasi_yadkori",
    ) -> None:
        self.d = int(d)
        self.obs_std = float(obs_std)
        self.prior_lambda = float(prior_lambda)
        self.theta_0 = (
            np.zeros(self.d, dtype=np.float64)
            if prior_mean is None
            else np.asarray(prior_mean, dtype=np.float64).copy()
        )
        self.theta_norm_bound = float(theta_norm_bound)
        self.delta = float(delta)
        self.ellipsoid_mode = str(ellipsoid_mode)

        self.v_mat = self.prior_lambda * np.eye(self.d, dtype=np.float64)
        self.v_inv = (1.0 / self.prior_lambda) * np.eye(self.d, dtype=np.float64)
        self.rhs = np.zeros(self.d, dtype=np.float64)
        self.theta_hat = self.theta_0.copy()
        self.logdet_ratio = 0.0
        self.n_obs = 0
        self.sum_xi_sq = 0.0

        self._chi2_sqrt = math.sqrt(float(chi2_dist.ppf(1.0 - self.delta, df=self.d)))
        self._dirty_factors = True
        self._l_t = np.eye(self.d, dtype=np.float64) / math.sqrt(self.prior_lambda)
        self._v_inv_diag_sqrt = np.full(self.d, 1.0 / math.sqrt(self.prior_lambda), dtype=np.float64)
        self._eigmax_sqrt = 1.0 / math.sqrt(self.prior_lambda)

    def update(self, phi: np.ndarray, y: float, xi: float = 0.0) -> None:
        """Exact O(d^2) Sherman-Morrison update."""
        x = np.asarray(phi, dtype=np.float64)
        vx = self.v_inv @ x
        quad = float(x @ vx)
        denom = 1.0 + max(0.0, quad)
        self.v_mat += np.outer(x, x)
        self.v_inv -= np.outer(vx, vx) / denom
        self.v_inv = 0.5 * (self.v_inv + self.v_inv.T)
        self.logdet_ratio += math.log(denom)
        self.rhs += x * (float(y) - float(x @ self.theta_0))
        self.theta_hat = self.theta_0 + self.v_inv @ self.rhs
        self.n_obs += 1
        if xi > 0.0:
            self.sum_xi_sq += float(xi) * float(xi)
        self._dirty_factors = True

    def _ensure_factors(self) -> None:
        if not self._dirty_factors:
            return
        # Symmetrize & guard tiny numerical drift
        sym = 0.5 * (self.v_inv + self.v_inv.T)
        try:
            l_mat = np.linalg.cholesky(sym)
        except np.linalg.LinAlgError:
            eigvals, eigvecs = np.linalg.eigh(sym)
            eigvals = np.maximum(1e-14, eigvals)
            sym = (eigvecs * eigvals) @ eigvecs.T
            self.v_inv = sym
            l_mat = np.linalg.cholesky(sym)
        self._l_t = l_mat.T
        self._v_inv_diag_sqrt = np.sqrt(np.maximum(1e-18, np.diag(sym)))
        # Exact largest eigenvalue of V_t^{-1}
        self._eigmax_sqrt = math.sqrt(max(1e-18, float(np.linalg.eigvalsh(sym)[-1])))
        self._dirty_factors = False

    @property
    def l_t(self) -> np.ndarray:
        self._ensure_factors()
        return self._l_t

    @property
    def v_inv_diag_sqrt(self) -> np.ndarray:
        self._ensure_factors()
        return self._v_inv_diag_sqrt

    @property
    def eigmax_sqrt(self) -> float:
        self._ensure_factors()
        return self._eigmax_sqrt

    def beta(self) -> float:
        """Current valid ellipsoid radius ``beta_t`` such that ``||theta* - theta_hat||_{V_t} <= beta_t``."""
        bias_infl = math.sqrt(self.sum_xi_sq) if self.sum_xi_sq > 0.0 else 0.0
        if self.ellipsoid_mode == "credible":
            return self.obs_std * self._chi2_sqrt + bias_infl
        # Anytime-valid Abbasi-Yadkori (2011) + Lattimore-Szepesvari-Weisz (2020) residual term
        rad_noise = self.obs_std * math.sqrt(
            max(0.0, self.logdet_ratio + 2.0 * math.log(1.0 / self.delta))
        )
        return rad_noise + math.sqrt(self.prior_lambda) * self.theta_norm_bound + bias_infl

    def norm_v_inv(self, vec: np.ndarray) -> float:
        return float(np.linalg.norm(self.l_t @ vec))

    def contains(self, theta_true: np.ndarray) -> bool:
        diff = np.asarray(theta_true, dtype=np.float64) - self.theta_hat
        quad = float(diff @ (self.v_mat @ diff))
        return math.sqrt(max(0.0, quad)) <= self.beta() + 1e-12


# ---------------------------------------------------------------------------
# 4. Exact Conic Subtree-Envelope Certifier (Theorems M.1 & M.2)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class EnvelopeChallengerResult:
    """Result of solving ``U_t(v, W_t(a))`` for one excluded boundary challenger ``v``."""

    node_id: int
    upper_bound: float
    point_dual: float
    env_slack: float
    stat_radius: float
    floor_bound: float
    witness_ids: np.ndarray
    witness_weights: np.ndarray
    contrast: np.ndarray
    scalar_clamped: bool = False


@dataclass(frozen=True)
class GrowingActionCertificate:
    """Prefix joint regret certificate for one root action ``a`` on ``G_t``."""

    action: int
    regret: float
    challenger_id: int
    env_slack: float
    stat_radius: float
    floor_bound: float
    witness_ids: np.ndarray
    witness_weights: np.ndarray
    contrast: np.ndarray
    n_excluded_boundary: int
    n_conic_solves: int


def _fast_simplex_pfw(
    m_z: float,
    m_w: np.ndarray,
    psi_z: np.ndarray,
    psi_w: np.ndarray,
    beta: float,
    init_p: np.ndarray,
    tol: float = 1e-4,
    max_iter: int = 40,
) -> tuple[np.ndarray, float]:
    """Pure NumPy pairwise Frank-Wolfe on the small active simplex (zero SciPy SLSQP overhead).
    Always returns a 100%-feasible simplex vector p in Delta(W) and its exact dual value."""
    k = len(m_w)
    if k == 1:
        q = float(np.linalg.norm(psi_z - psi_w[0]))
        return np.ones(1, dtype=np.float64), float((m_z - m_w[0]) + beta * q)
    p = np.asarray(init_p, dtype=np.float64).copy()
    p = np.maximum(0.0, p)
    s = float(p.sum())
    p = p / s if s > 0.0 else np.full(k, 1.0 / k, dtype=np.float64)
    best_p = p.copy()
    best_val = math.inf
    for _ in range(max_iter):
        bar_psi = p @ psi_w
        u = psi_z - bar_psi
        q = float(np.linalg.norm(u))
        val = (m_z - float(p @ m_w)) + beta * q
        if val < best_val:
            best_val = val
            best_p = p.copy()
        if q <= 1e-11:
            break
        grad = -m_w - (beta / q) * (psi_w @ u)
        fw_idx = int(np.argmin(grad))
        active = np.where(p > 1e-12)[0]
        if len(active) == 0:
            break
        aw_idx = int(active[int(np.argmax(grad[active]))])
        pw_gap = float(grad[aw_idx] - grad[fw_idx])
        if pw_gap <= tol:
            break
        fw_gap = float(p @ grad - grad[fw_idx])
        if fw_gap <= tol:
            break
        if pw_gap >= fw_gap and fw_idx != aw_idx:
            d_m = float(m_w[fw_idx] - m_w[aw_idx])
            d_psi = psi_w[fw_idx] - psi_w[aw_idx]
            alpha_max = float(p[aw_idx])
            is_pw = True
        else:
            d_m = float(m_w[fw_idx] - (p @ m_w))
            d_psi = psi_w[fw_idx] - bar_psi
            alpha_max = 1.0
            is_pw = False
        a1 = -d_m
        b1 = -2.0 * float(u @ d_psi)
        c2 = float(d_psi @ d_psi)
        quad0 = q * q
        if c2 <= 1e-18:
            alpha = alpha_max if a1 < 0.0 else 0.0
        else:
            # Check endpoint derivative; bisection/Newton in <= 8 steps
            q_end = math.sqrt(max(1e-26, quad0 + b1 * alpha_max + c2 * alpha_max * alpha_max))
            if a1 + beta * (0.5 * b1 + c2 * alpha_max) / q_end <= 0.0:
                alpha = alpha_max
            else:
                lo_a, hi_a = 0.0, alpha_max
                alpha = 0.5 * alpha_max
                for _ in range(8):
                    qa = math.sqrt(max(1e-26, quad0 + b1 * alpha + c2 * alpha * alpha))
                    da = a1 + beta * (0.5 * b1 + c2 * alpha) / qa
                    if abs(da) <= 1e-10:
                        break
                    if da < 0.0:
                        lo_a = alpha
                    else:
                        hi_a = alpha
                    alpha = 0.5 * (lo_a + hi_a)
        if alpha <= 1e-14:
            break
        if is_pw:
            p[fw_idx] += alpha
            p[aw_idx] = max(0.0, p[aw_idx] - alpha)
        else:
            p *= 1.0 - alpha
            p[fw_idx] += alpha
        p /= float(p.sum())
    return best_p, best_val


def solve_envelope_challenger(
    challenger_id: int,
    env: SubtreeEnvelope,
    witness_ids: np.ndarray,
    witness_phi: np.ndarray,
    witness_psi: np.ndarray,
    witness_m: np.ndarray,
    witness_xi: np.ndarray,
    posterior: GrowingLinearPosterior,
    beta: float,
    *,
    tol: float = 1e-6,
    max_colgen_iter: int = 12,
    precomputed_opt: tuple[np.ndarray, float, float] | None = None,
) -> EnvelopeChallengerResult:
    """Solve the provably sound conic split-envelope upper bound ``U_t(v, W_t(a))`` (Theorem M.2).

    Uses the optimistic-vertex decomposition ``phi_opt in argmax_{phi in Phi_hat(v)} phi^T theta_hat``
    with self-collapsing optimality-margin slack ``s_opt(v)`` (clamped above by the base-center
    split bound when tighter), maintaining Caratheodory sparsity ``|supp(p*)| <= d + 1``.
    """
    theta_hat = posterior.theta_hat
    l_t = posterior.l_t
    if precomputed_opt is not None:
        c_v, env_slack, lin_max = precomputed_opt
    else:
        c_v, env_slack, lin_max = env.optimistic_vertex_and_slack(
            theta_hat, l_t, posterior.v_inv_diag_sqrt, beta
        )
    m_c = lin_max
    psi_c = l_t @ c_v

    # Fast single-witness fallback when |W| == 1
    nw = len(witness_ids)
    if nw == 1:
        diff_psi = psi_c - witness_psi[0]
        stat_rad = beta * float(np.linalg.norm(diff_psi))
        pt_dual = (m_c - float(witness_m[0])) + stat_rad
        u_conic = pt_dual + env_slack + env.residual
        contrast = c_v - witness_phi[0]
        floor_b = (lin_max - float(witness_m[0])) + env.residual
        scalar_clamped = False
        if math.isfinite(env.scalar_upper):
            l_w = float(witness_m[0]) - beta * float(np.linalg.norm(witness_psi[0]))
            u_sc = env.scalar_upper - l_w
            if u_sc < u_conic:
                u_conic = u_sc
                scalar_clamped = True
        return EnvelopeChallengerResult(
            node_id=challenger_id,
            upper_bound=float(u_conic),
            point_dual=float(pt_dual),
            env_slack=float(env_slack),
            stat_radius=float(stat_rad),
            floor_bound=float(floor_b),
            witness_ids=witness_ids.copy(),
            witness_weights=np.ones(1, dtype=np.float64),
            contrast=contrast,
            scalar_clamped=scalar_clamped,
        )

    # Column generation over W_t(a): initialize with empirical best inside witness
    best_emp_local = int(np.argmax(witness_m))
    # Also add closest in whitened space if distinct
    dists = np.linalg.norm(witness_psi - psi_c[None, :], axis=1)
    closest_local = int(np.argmin(dists))
    active = [best_emp_local] if closest_local == best_emp_local else [best_emp_local, closest_local]
    p_act = np.ones(len(active), dtype=np.float64) / len(active)

    d = posterior.d
    het_xi = bool(float(np.max(witness_xi) - np.min(witness_xi)) > 1e-12)
    cara_cap = d + 2 if het_xi else d + 1

    best_val = math.inf
    best_active = list(active)
    best_p = p_act.copy()

    for _ in range(max_colgen_iter):
        act_arr = np.array(active, dtype=np.int64)
        if tol < 1e-5:
            p_act, val, _, _ = _solve_small_simplex_afw(
                m_z=m_c,
                m_w=witness_m[act_arr],
                psi_z=psi_c,
                psi_w=witness_psi[act_arr],
                beta=beta,
                init_p=p_act,
                tol=tol,
                max_iter=45,
            )
        else:
            p_act, val = _fast_simplex_pfw(
                m_z=m_c,
                m_w=witness_m[act_arr],
                psi_z=psi_c,
                psi_w=witness_psi[act_arr],
                beta=beta,
                init_p=p_act,
                tol=tol,
                max_iter=35,
            )
        if val < best_val:
            best_val = val
            best_active = list(active)
            best_p = p_act.copy()

        # Caratheodory prune to keep |active| <= d + 1 (or d + 2)
        if len(active) > cara_cap:
            sub_idx, sub_w = caratheodory_prune(
                features_w=witness_psi,
                means_w=witness_m,
                weights_w=p_act,
                indices_w=act_arr,
                exact_linear_mean=not het_xi,
            )
            active = [int(i) for i in sub_idx]
            p_act = sub_w
            act_arr = np.array(active, dtype=np.int64)
            bar_psi = p_act @ witness_psi[act_arr]
            u_vec = psi_c - bar_psi
            val_pruned = (m_c - float(p_act @ witness_m[act_arr])) + beta * float(np.linalg.norm(u_vec))
            if val_pruned <= best_val + 1e-10:
                best_val = val_pruned
                best_active = list(active)
                best_p = p_act.copy()

        bar_psi = p_act @ witness_psi[act_arr]
        u_vec = psi_c - bar_psi
        q = float(np.linalg.norm(u_vec))
        if q <= 1e-12:
            break

        # Exact Frank-Wolfe pricing across all witnesses in W_t(a)
        grad_all = -witness_m - (beta / q) * (witness_psi @ u_vec)
        cand_local = int(np.argmin(grad_all))
        gp = float(grad_all[act_arr] @ p_act)
        fw_gap = gp - float(grad_all[cand_local])
        if fw_gap <= tol or cand_local in active:
            break
        active.append(cand_local)
        p_act = np.append(p_act * 0.99, 0.01)

    # Final Caratheodory pruning on best solution to strictly enforce Theorem M.2 sparsity
    best_arr = np.array(best_active, dtype=np.int64)
    nz = best_p > 1e-10
    if not np.any(nz):
        nz[int(np.argmax(best_p))] = True
    best_arr = best_arr[nz]
    best_p = best_p[nz]
    best_p /= float(np.sum(best_p))
    if len(best_arr) > cara_cap:
        sub_idx, sub_w = caratheodory_prune(
            features_w=witness_psi,
            means_w=witness_m,
            weights_w=best_p,
            indices_w=best_arr,
            exact_linear_mean=not het_xi,
        )
        best_arr = sub_idx
        best_p = sub_w

    bar_phi = best_p @ witness_phi[best_arr]
    bar_psi = best_p @ witness_psi[best_arr]
    bar_m = float(best_p @ witness_m[best_arr])
    stat_rad = beta * float(np.linalg.norm(psi_c - bar_psi))
    pt_dual = (m_c - bar_m) + stat_rad
    u_conic = pt_dual + env_slack + env.residual
    floor_b = (lin_max - bar_m) + env.residual
    contrast = c_v - bar_phi

    scalar_clamped = False
    if math.isfinite(env.scalar_upper):
        # Sound scalar upper bound against the best individual inside witness lower bound
        l_in = float(np.max(witness_m - beta * np.linalg.norm(witness_psi, axis=1)))
        u_sc = env.scalar_upper - l_in
        if u_sc < u_conic:
            u_conic = u_sc
            scalar_clamped = True

    return EnvelopeChallengerResult(
        node_id=challenger_id,
        upper_bound=float(u_conic),
        point_dual=float(pt_dual),
        env_slack=float(env_slack),
        stat_radius=float(stat_rad),
        floor_bound=float(floor_b),
        witness_ids=witness_ids[best_arr].copy(),
        witness_weights=best_p.copy(),
        contrast=contrast,
        scalar_clamped=scalar_clamped,
    )


class GrowingEllipsoidCertifier:
    """Exact branch-and-bound conic envelope certifier for a growing prefix-DAG (Theorems M.1 & M.2).

    Caches per-node whitened centers, linear maxima, and Mahalanobis envelope radii keyed by
    ``posterior.n_obs`` so consecutive expansion steps only evaluate newly registered children
    and never repeat O(|B_t|) work across the K root actions.
    """

    def __init__(self, tol: float = 1e-6) -> None:
        self.tol = float(tol)
        self._cache_obs: int = -1
        self._cache_beta: float = -1.0
        self._step_cache: dict[str, Any] = {}
        # node_id -> (phi_opt, m_c, psi_c, env_slack, lin_max)
        self._node_cache: dict[int, tuple[np.ndarray, float, np.ndarray, float, float]] = {}

    def _prefetch_nodes(
        self,
        nids: Sequence[int],
        prefix: GrowingPrefixDAG,
        posterior: GrowingLinearPosterior,
        beta: float,
    ) -> None:
        if posterior.n_obs != self._cache_obs or abs(beta - self._cache_beta) > 1e-12:
            self._node_cache.clear()
            self._step_cache.clear()
            self._cache_obs = posterior.n_obs
            self._cache_beta = beta
        miss_pt: list[int] = []
        miss_fr: list[int] = []
        for nid in nids:
            if nid not in self._node_cache:
                if prefix.envelopes[nid].kind == "point":
                    miss_pt.append(nid)
                else:
                    miss_fr.append(nid)
        theta_hat = posterior.theta_hat
        l_t = posterior.l_t
        if miss_pt:
            phis = np.stack([prefix.envelopes[i].center for i in miss_pt], axis=0)
            lms = phis @ theta_hat
            psis = phis @ l_t.T
            for idx, nid in enumerate(miss_pt):
                lm = float(lms[idx])
                self._node_cache[nid] = (phis[idx], lm, psis[idx], 0.0, lm)
        if miss_fr:
            states = [prefix.id_to_state[i] for i in miss_fr]
            batched = prefix.problem.batch_optimistic_stats(
                states, theta_hat, l_t, posterior.v_inv_diag_sqrt, beta, self._step_cache
            )
            if batched is not None:
                phi_opts, s_opts, lin_maxs = batched
                psis = phi_opts @ l_t.T
                for idx, nid in enumerate(miss_fr):
                    lm = float(lin_maxs[idx])
                    self._node_cache[nid] = (phi_opts[idx], lm, psis[idx], float(s_opts[idx]), lm)

    def _node_stats(
        self,
        nid: int,
        prefix: GrowingPrefixDAG,
        posterior: GrowingLinearPosterior,
        beta: float | None = None,
    ) -> tuple[np.ndarray, float, np.ndarray, float, float]:
        b = posterior.beta() if beta is None else beta
        if posterior.n_obs != self._cache_obs or abs(b - self._cache_beta) > 1e-12:
            self._node_cache.clear()
            self._step_cache.clear()
            self._cache_obs = posterior.n_obs
            self._cache_beta = b
        cached = self._node_cache.get(nid)
        if cached is not None:
            return cached
        env = prefix.envelopes[nid]
        theta_hat = posterior.theta_hat
        l_t = posterior.l_t
        if env.kind == "point":
            phi_opt = env.center
            lin_max = float(phi_opt @ theta_hat)
            s_opt = 0.0
        else:
            fast = prefix.problem.fast_optimistic_stats(
                prefix.id_to_state[nid],
                theta_hat,
                l_t,
                posterior.v_inv_diag_sqrt,
                b,
                self._step_cache,
            )
            if fast is not None:
                phi_opt, s_opt, lin_max = fast
            else:
                phi_opt, s_opt, lin_max = env.optimistic_vertex_and_slack(
                    theta_hat, l_t, posterior.v_inv_diag_sqrt, b
                )
        psi_opt = l_t @ phi_opt
        val = (phi_opt, lin_max, psi_opt, s_opt, lin_max)
        self._node_cache[nid] = val
        return val

    def certify_action(
        self,
        action: int,
        prefix: GrowingPrefixDAG,
        posterior: GrowingLinearPosterior,
        beta: float,
        *,
        stop_if_above_eps: float | None = None,
    ) -> GrowingActionCertificate:
        w_ids_list = prefix.action_witness_terminals(action)
        excl_list = prefix.action_excluded_boundary(action)
        if not excl_list:
            return GrowingActionCertificate(
                action=action,
                regret=0.0,
                challenger_id=-1,
                env_slack=0.0,
                stat_radius=0.0,
                floor_bound=0.0,
                witness_ids=np.array(w_ids_list, dtype=np.int64),
                witness_weights=np.ones(max(1, len(w_ids_list)), dtype=np.float64) / max(1, len(w_ids_list)),
                contrast=np.zeros(posterior.d, dtype=np.float64),
                n_excluded_boundary=0,
                n_conic_solves=0,
            )
        if not w_ids_list:
            return GrowingActionCertificate(
                action=action,
                regret=math.inf,
                challenger_id=excl_list[0],
                env_slack=math.inf,
                stat_radius=0.0,
                floor_bound=math.inf,
                witness_ids=np.array([], dtype=np.int64),
                witness_weights=np.array([], dtype=np.float64),
                contrast=np.zeros(posterior.d, dtype=np.float64),
                n_excluded_boundary=len(excl_list),
                n_conic_solves=0,
            )

        w_ids = np.array(w_ids_list, dtype=np.int64)
        w_phi = np.stack([prefix.envelopes[i].center for i in w_ids_list], axis=0)
        w_xi = np.array([prefix.envelopes[i].residual for i in w_ids_list], dtype=np.float64)
        self._prefetch_nodes(w_ids_list, prefix, posterior, beta)
        self._prefetch_nodes(excl_list, prefix, posterior, beta)
        w_stats = [self._node_stats(i, prefix, posterior, beta) for i in w_ids_list]
        w_psi = np.stack([s[2] for s in w_stats], axis=0)
        w_m = np.array([s[1] for s in w_stats], dtype=np.float64) - w_xi

        # Fast sound center-mean lower-bound filter on expanded outside terminals (hoisted max!)
        emp_idx = int(np.argmax(w_m))
        m_emp = float(w_m[emp_idx])
        psi_emp = w_psi[emp_idx]
        max_w_raw = float(np.max(w_m + w_xi))
        l_in_best = float(np.max(w_m - beta * np.linalg.norm(w_psi, axis=1)))

        if stop_if_above_eps is not None:
            for vid in excl_list:
                if prefix.is_term[vid]:
                    _, m_c, _, _, _ = self._node_stats(vid, prefix, posterior, beta)
                    if m_c - max_w_raw - prefix.envelopes[vid].residual > stop_if_above_eps + 1e-12:
                        return GrowingActionCertificate(
                            action=action,
                            regret=math.inf,
                            challenger_id=vid,
                            env_slack=0.0,
                            stat_radius=0.0,
                            floor_bound=float(m_c - m_emp),
                            witness_ids=w_ids[emp_idx : emp_idx + 1].copy(),
                            witness_weights=np.ones(1, dtype=np.float64),
                            contrast=prefix.envelopes[vid].center - w_phi[emp_idx],
                            n_excluded_boundary=len(excl_list),
                            n_conic_solves=0,
                        )

        n_excl = len(excl_list)
        m_c_arr = np.empty(n_excl, dtype=np.float64)
        psi_c_arr = np.empty((n_excl, posterior.d), dtype=np.float64)
        env_sl_arr = np.empty(n_excl, dtype=np.float64)
        res_arr = np.empty(n_excl, dtype=np.float64)
        sc_arr = np.empty(n_excl, dtype=np.float64)
        for idx, vid in enumerate(excl_list):
            _, m_c, psi_c, s_opt, _ = self._node_stats(vid, prefix, posterior, beta)
            env = prefix.envelopes[vid]
            m_c_arr[idx] = m_c
            psi_c_arr[idx] = psi_c
            env_sl_arr[idx] = s_opt
            res_arr[idx] = env.residual
            sc_arr[idx] = env.scalar_upper

        u_single_arr = (
            (m_c_arr - m_emp)
            + beta * np.linalg.norm(psi_c_arr - psi_emp[None, :], axis=1)
            + env_sl_arr
            + res_arr
        )
        fin_sc = np.isfinite(sc_arr)
        if np.any(fin_sc):
            u_single_arr[fin_sc] = np.minimum(u_single_arr[fin_sc], sc_arr[fin_sc] - l_in_best)

        if stop_if_above_eps is not None and float(np.max(u_single_arr)) <= stop_if_above_eps:
            pos0 = int(np.argmax(u_single_arr))
            vid0 = excl_list[pos0]
            phi0, _, _, _, _ = self._node_stats(vid0, prefix, posterior, beta)
            return GrowingActionCertificate(
                action=action,
                regret=max(0.0, float(u_single_arr[pos0])),
                challenger_id=vid0,
                env_slack=float(env_sl_arr[pos0]),
                stat_radius=float(beta * np.linalg.norm(psi_c_arr[pos0] - psi_emp)),
                floor_bound=float(m_c_arr[pos0] - m_emp + res_arr[pos0]),
                witness_ids=w_ids[emp_idx : emp_idx + 1].copy(),
                witness_weights=np.ones(1, dtype=np.float64),
                contrast=phi0 - w_phi[emp_idx],
                n_excluded_boundary=n_excl,
                n_conic_solves=0,
            )

        vid_arr = np.array(excl_list, dtype=np.int64)
        order = np.lexsort((-vid_arr, -u_single_arr))

        best_res: EnvelopeChallengerResult | None = None
        best_val = -math.inf
        best_bar_psi: np.ndarray | None = None
        best_bar_m: float = m_emp
        n_solves = 0
        for pos in order:
            u_single = float(u_single_arr[pos])
            if u_single <= best_val + 1e-12:
                break
            if stop_if_above_eps is not None and u_single <= stop_if_above_eps + 1e-12:
                if best_res is None:
                    vid0 = excl_list[int(pos)]
                    phi0, _, _, _, _ = self._node_stats(vid0, prefix, posterior, beta)
                    return GrowingActionCertificate(
                        action=action,
                        regret=max(0.0, u_single),
                        challenger_id=vid0,
                        env_slack=float(env_sl_arr[pos]),
                        stat_radius=float(beta * np.linalg.norm(psi_c_arr[pos] - psi_emp)),
                        floor_bound=float(m_c_arr[pos] - m_emp + res_arr[pos]),
                        witness_ids=w_ids[emp_idx : emp_idx + 1].copy(),
                        witness_weights=np.ones(1, dtype=np.float64),
                        contrast=phi0 - w_phi[emp_idx],
                        n_excluded_boundary=n_excl,
                        n_conic_solves=n_solves,
                    )
                break
            # Fast O(d*|W|) 100%-sound primal lower-bound rejection when stop_if_above_eps is set:
            # any single feasible u in the unit ball gives D_t(v, W) >= min_{w in W} [(m_v - m_w) + beta*(psi_v - psi_w)^T u] + env_sl + res_v!
            if stop_if_above_eps is not None and prefix.is_term[excl_list[int(pos)]]:
                diff_emp = psi_c_arr[pos] - psi_emp
                dn = float(np.linalg.norm(diff_emp))
                if dn > 1e-12:
                    u_dir = diff_emp / dn
                    primal_lb = float(np.min((float(m_c_arr[pos]) - w_m) + beta * ((psi_c_arr[pos] - w_psi) @ u_dir))) + float(res_arr[pos])
                    if math.isfinite(float(sc_arr[pos])):
                        primal_lb = min(primal_lb, float(sc_arr[pos]) - m_emp)
                    if primal_lb > stop_if_above_eps + 1e-9:
                        vid_r = excl_list[int(pos)]
                        phi_r, _, _, _, _ = self._node_stats(vid_r, prefix, posterior, beta)
                        return GrowingActionCertificate(
                            action=action,
                            regret=math.inf,
                            challenger_id=vid_r,
                            env_slack=0.0,
                            stat_radius=beta * dn,
                            floor_bound=float(m_c_arr[pos] - m_emp + res_arr[pos]),
                            witness_ids=w_ids[emp_idx : emp_idx + 1].copy(),
                            witness_weights=np.ones(1, dtype=np.float64),
                            contrast=phi_r - w_phi[emp_idx],
                            n_excluded_boundary=n_excl,
                            n_conic_solves=n_solves,
                        )
            # Fast 100%-sound screening using the incumbent optimal witness mixture p*!
            if best_bar_psi is not None:
                u_inc = (
                    (float(m_c_arr[pos]) - best_bar_m)
                    + beta * float(np.linalg.norm(psi_c_arr[pos] - best_bar_psi))
                    + float(env_sl_arr[pos])
                    + float(res_arr[pos])
                )
                if math.isfinite(float(sc_arr[pos])):
                    u_inc = min(u_inc, float(sc_arr[pos]) - l_in_best)
                if u_inc <= best_val + 1e-12:
                    continue
            vid = excl_list[int(pos)]
            phi_opt, m_c, _, s_opt, lin_max = self._node_stats(vid, prefix, posterior, beta)
            res = solve_envelope_challenger(
                challenger_id=vid,
                env=prefix.envelopes[vid],
                witness_ids=w_ids,
                witness_phi=w_phi,
                witness_psi=w_psi,
                witness_m=w_m,
                witness_xi=w_xi,
                posterior=posterior,
                beta=beta,
                tol=self.tol,
                precomputed_opt=(phi_opt, s_opt, lin_max),
            )
            n_solves += 1
            if res.upper_bound > best_val:
                best_val = res.upper_bound
                best_res = res
                # Cache incumbent mixture (bar_psi, bar_m) for O(d) sound screening of remaining nodes
                w_local = np.searchsorted(w_ids, res.witness_ids)
                # Map global witness_ids back to local indices cleanly
                id_to_loc = {int(gid): li for li, gid in enumerate(w_ids_list)}
                loc_idx = np.array([id_to_loc[int(gid)] for gid in res.witness_ids], dtype=np.int64)
                best_bar_psi = res.witness_weights @ w_psi[loc_idx]
                best_bar_m = float(res.witness_weights @ w_m[loc_idx])
            if stop_if_above_eps is not None and best_val > stop_if_above_eps:
                best_val = math.inf
                break

        assert best_res is not None
        return GrowingActionCertificate(
            action=action,
            regret=max(0.0, float(best_res.upper_bound)),
            challenger_id=int(best_res.node_id),
            env_slack=float(best_res.env_slack),
            stat_radius=float(best_res.stat_radius),
            floor_bound=float(best_res.floor_bound),
            witness_ids=best_res.witness_ids,
            witness_weights=best_res.witness_weights,
            contrast=best_res.contrast,
            n_excluded_boundary=n_excl,
            n_conic_solves=n_solves,
        )

    def node_optimistic_upper(
        self,
        env: SubtreeEnvelope,
        posterior: GrowingLinearPosterior,
        beta: float,
        *,
        nid: int | None = None,
        prefix: GrowingPrefixDAG | None = None,
    ) -> tuple[float, float, float]:
        """Return ``(U_opt(v), env_slack(v), stat_radius_center(v))`` for optimistic/marginal bounds."""
        if nid is not None and prefix is not None:
            _, lin_max, psi_c, s_opt, _ = self._node_stats(nid, prefix, posterior, beta)
            stat_c = beta * float(np.linalg.norm(psi_c))
        else:
            phi_opt, s_opt, lin_max = env.optimistic_vertex_and_slack(
                posterior.theta_hat, posterior.l_t, posterior.v_inv_diag_sqrt, beta
            )
            stat_c = beta * float(np.linalg.norm(posterior.l_t @ phi_opt))
        u_opt = lin_max + stat_c + s_opt + env.residual
        if math.isfinite(env.scalar_upper):
            u_opt = min(u_opt, env.scalar_upper)
        return float(u_opt), float(s_opt), float(stat_c)

    def certify_all_actions(
        self,
        prefix: GrowingPrefixDAG,
        posterior: GrowingLinearPosterior,
        beta: float,
    ) -> tuple[GrowingActionCertificate, list[GrowingActionCertificate]]:
        certs = [self.certify_action(a, prefix, posterior, beta) for a in range(prefix.k)]
        best = min(certs, key=lambda c: (c.regret, c.action))
        return best, certs


# ---------------------------------------------------------------------------
# 5. Matched Growing-DAG Policies (Algorithm M.1 + 3 Matched Comparators)
# ---------------------------------------------------------------------------


@dataclass
class GrowingRunResult:
    """Complete per-campaign record returned by ``run_growing_campaign``."""

    policy: str
    eta: float
    certified: bool
    recommended_root: int
    n_evaluations: int
    n_expansions: int
    n_nodes: int
    n_terminals: int
    n_frontier: int
    transposition_merges: int
    total_leaf_count: int
    cert_regret_bound: float
    true_root_regret: float
    false_certificate: bool
    beta_at_stop: float
    mean_witness_support: float
    max_witness_support: int
    n_inside_expansions: int
    n_outside_expansions: int
    n_proxy_queries: int
    cert_time_s: float
    total_runtime_s: float
    stop_reason: str


def _select_cd_joint_leaf(
    contrast: np.ndarray,
    prefix: GrowingPrefixDAG,
    posterior: GrowingLinearPosterior,
    min_cosine: float = 0.25,
) -> tuple[int, bool]:
    """Select ``x_t in T_t`` maximizing contrast variance reduction per unit cost.

    Returns ``(best_tid, well_aligned)`` where ``well_aligned`` checks whether the best
    expanded terminal in ``T_t`` achieves ``V_t^{-1}``-cosine alignment ``>= min_cosine``
    with ``contrast``. When ``well_aligned`` is False and the challenger ``v_t*`` lies on
    the unexpanded frontier ``F_t``, expanding ``v_t*`` introduces new feature directions
    needed to identify ``contrast`` (preventing orthogonal-subspace stalls).
    """
    t_ids = prefix.terminals
    phis = np.stack([prefix.envelopes[tid].center for tid in t_ids], axis=0)  # (|T_t|, d)
    v_inv_g = posterior.v_inv @ contrast
    g_norm_sq = max(0.0, float(contrast @ v_inv_g))
    numer = (phis @ v_inv_g) ** 2
    v_inv_phi = phis @ posterior.v_inv
    quads = np.maximum(0.0, np.sum(phis * v_inv_phi, axis=1))
    costs = np.array([prefix.problem.leaf_cost(prefix.id_to_state[tid]) for tid in t_ids], dtype=np.float64)
    scores = numer / np.maximum(1e-18, costs * (posterior.obs_std ** 2 + quads))
    best_i = int(np.argmax(scores))
    if g_norm_sq <= 1e-24:
        return t_ids[best_i], False
    cos_sq = numer / np.maximum(1e-24, g_norm_sq * quads)
    max_cos = math.sqrt(max(0.0, float(np.max(cos_sq))))
    return t_ids[best_i], max_cos >= min_cosine


def _select_most_uncertain_leaf(
    cand_ids: Sequence[int],
    prefix: GrowingPrefixDAG,
    posterior: GrowingLinearPosterior,
) -> int:
    best_id = cand_ids[0]
    best_s = -1.0
    for tid in cand_ids:
        phi = prefix.envelopes[tid].center
        s = posterior.norm_v_inv(phi) / math.sqrt(max(1e-12, prefix.problem.leaf_cost(prefix.id_to_state[tid])))
        if s > best_s:
            best_s = s
            best_id = tid
    return best_id


def run_growing_campaign(
    problem: ImplicitDAG,
    *,
    policy: str = "growing_cd_joint",
    epsilon: float = 0.05,
    delta: float = 0.05,
    obs_std: float = 0.15,
    prior_lambda: float = 1.0,
    prior_mean: np.ndarray | None = None,
    theta_norm_bound: float = 2.0,
    ellipsoid_mode: str = "abbasi_yadkori",
    eta: float = 1.0,
    max_evaluations: int = 2000,
    max_expansions: int = 5000,
    seed: int = 0,
    cert_tol: float = 1e-4,
) -> GrowingRunResult:
    """Run one matched growing-DAG certification campaign on ``problem``.

    Policies:
      - ``"growing_cd_joint"``: Algorithm M.1 with Measure-vs-Expand parameter ``eta``
        (``eta=0.0`` is Expand-First; ``eta=1.0`` is Balanced; ``eta=math.inf`` is Measure-First).
      - ``"growing_gp_os"``: Shared-subtree conic envelope certifier (Theorems M.1 & M.2) +
        LUCB endpoint measurement (no off-witness proxy acquisition).
      - ``"growing_marginal"``: Marginal root certification WITHOUT shared-subtree cancellation.
      - ``"growing_best_leaf"``: Pelissier et al. (2019)-style best-leaf identification on the
        exact same growing DAG, feature envelopes, and conic ellipsoid.
    """
    t0 = time.perf_counter()
    cert_time = 0.0

    prefix = GrowingPrefixDAG(problem)
    posterior = GrowingLinearPosterior(
        d=problem.feature_dim,
        obs_std=obs_std,
        prior_lambda=prior_lambda,
        prior_mean=prior_mean,
        theta_norm_bound=theta_norm_bound,
        delta=delta,
        ellipsoid_mode=ellipsoid_mode,
    )
    certifier = GrowingEllipsoidCertifier(tol=cert_tol)

    # Deterministic per-leaf observation call counts (for exact paired tapes!)
    call_counts: dict[Hashable, int] = {}

    def query_leaf(tid: int) -> None:
        st = prefix.id_to_state[tid]
        cnt = call_counts.get(st, 0)
        call_counts[st] = cnt + 1
        y_val = problem.observe(st, obs_std=obs_std, seed=seed, call_idx=cnt)
        env = prefix.envelopes[tid]
        posterior.update(env.center, y_val, xi=env.residual)

    # Step 0: materialize at least one leaf per root action and collect 1 pilot draw per unique leaf
    init_leaves = prefix.ensure_initial_witnesses(posterior.theta_hat)
    for tid in dict.fromkeys(init_leaves):
        if posterior.n_obs >= max_evaluations:
            break
        query_leaf(tid)

    certified = False
    rec_root = 0
    final_bound = math.inf
    stop_reason = "budget_eval"

    support_sizes: list[int] = []
    n_inside_exp = 0
    n_outside_exp = 0
    n_proxy_queries = 0
    last_inside_refresh_obs = -1000000

    # Main interleaved expand/measure loop
    max_steps = max_evaluations + max_expansions + 20
    for _ in range(max_steps):
        beta = posterior.beta()
        tc0 = time.perf_counter()

        if policy in ("growing_cd_joint", "growing_gp_os"):
            # Identify empirical leader a_t = argmax_a m_in(a) first
            emp_vals: list[tuple[float, int]] = []
            for a_idx in range(prefix.k):
                wa = prefix.action_witness_terminals(a_idx)
                ma = (
                    max(
                        float(prefix.envelopes[tid].center @ posterior.theta_hat) - prefix.envelopes[tid].residual
                        for tid in wa
                    )
                    if wa
                    else -math.inf
                )
                emp_vals.append((ma, a_idx))
            emp_vals.sort(key=lambda pair: (-pair[0], pair[1]))
            target_a = emp_vals[0][1]

            # Full exact certificate for empirical leader; fast stop_if_above_eps check for rivals
            # (check rivals every step for n_obs <= 40, then every 10 obs or at budget end)
            target_cert = certifier.certify_action(target_a, prefix, posterior, beta)
            best_cert = target_cert
            check_rivals = (
                best_cert.regret > epsilon
                and (posterior.n_obs <= 40 or (posterior.n_obs % 10 == 0) or posterior.n_obs >= max_evaluations)
            )
            if check_rivals:
                for _, a_idx in emp_vals[1:]:
                    ca = certifier.certify_action(
                        a_idx, prefix, posterior, beta, stop_if_above_eps=epsilon
                    )
                    if ca.regret <= epsilon:
                        best_cert = ca
                        break
                    if (ca.regret, ca.action) < (best_cert.regret, best_cert.action):
                        best_cert = ca
            cert_time += time.perf_counter() - tc0

            rec_root = best_cert.action
            final_bound = best_cert.regret
            if len(target_cert.witness_ids) > 0:
                support_sizes.append(len(target_cert.witness_ids))

            if best_cert.regret <= epsilon:
                certified = True
                stop_reason = "certified"
                break

            if posterior.n_obs >= max_evaluations:
                stop_reason = "budget_eval"
                break

            # Identify best inside witness & inside frontier node with highest empirical linear max
            a_t = target_cert.action
            v_star = target_cert.challenger_id
            w_ids = prefix.action_witness_terminals(a_t)
            m_in = max(
                float(prefix.envelopes[tid].center @ posterior.theta_hat) - prefix.envelopes[tid].residual
                for tid in w_ids
            )
            in_frontier = prefix.action_inside_frontier(a_t)
            certifier._prefetch_nodes(in_frontier, prefix, posterior, beta)
            best_u_in = -1
            best_u_in_lin = -math.inf
            best_u_in_opt = -math.inf
            for fid in in_frontier:
                _, lin_m, psi_f, s_f, _ = certifier._node_stats(fid, prefix, posterior, beta)
                env_f = prefix.envelopes[fid]
                u_opt_f = lin_m + beta * float(np.linalg.norm(psi_f)) + s_f + env_f.residual
                if math.isfinite(env_f.scalar_upper):
                    u_opt_f = min(u_opt_f, env_f.scalar_upper)
                if lin_m > best_u_in_lin:
                    best_u_in_lin = lin_m
                    best_u_in = fid
                    best_u_in_opt = u_opt_f

            # With optimistic-vertex centering, s_opt = target_cert.env_slack is purely the
            # optimality-margin uncertainty (collapses to 0 as V_t^{-1} shrinks) while residual
            # is purely structural!
            v_is_frontier = v_star >= 0 and (v_star in prefix.frontier)
            if v_star >= 0:
                _, _, _, v_s_opt, _ = certifier._node_stats(v_star, prefix, posterior, beta)
                v_struct_sl = prefix.envelopes[v_star].residual
                v_unc_sl = v_s_opt
            else:
                v_struct_sl = 0.0
                v_unc_sl = 0.0
            stat_tot = target_cert.stat_radius + v_unc_sl
            has_warmup = posterior.n_obs >= max(posterior.d, prefix.k)

            # Rule 1: Inside epsilon/2 witness refresh — ONLY after basic warmup (n_obs >= d)
            # and strictly gated by ``inside_cooldown_ok`` (so inside descents never loop without
            # collecting new observations in between!). Descend ONE greedy path (<= D expansions):
            #   (a) when posterior mean theta_hat predicts a leaf inside S(a_t) at least eps/2
            #       better than current best expanded witness m_in, OR
            #   (b) when floor_bound > 0.5 * eps (statistically meaningful) and an inside frontier
            #       node has optimistic potential > m_in + 0.5 * eps.
            inside_cooldown_ok = (posterior.n_obs - last_inside_refresh_obs) >= max(posterior.d, 10)
            need_inside_exp = (
                has_warmup
                and inside_cooldown_ok
                and best_u_in >= 0
                and prefix.n_expansions < max_expansions
                and (
                    (best_u_in_lin > m_in + 0.5 * epsilon)
                    or (
                        target_cert.floor_bound > 0.5 * epsilon
                        and target_cert.floor_bound > 0.35 * target_cert.stat_radius
                        and best_u_in_opt > m_in + 0.5 * epsilon
                    )
                )
            )
            if need_inside_exp:
                _, used_exp = prefix.greedy_descent_to_leaf(
                    best_u_in, posterior.theta_hat, max_expansions - prefix.n_expansions
                )
                n_inside_exp += used_exp
                last_inside_refresh_obs = posterior.n_obs
                continue

            # Rule 2: Outside challenger expansion (controlled by balance parameter eta in [0, inf]):
            # - After basic warmup, if floor_bound > epsilon AND statistically meaningful
            #   (floor_bound > 0.35 * stat_radius), descend ONE greedy path to materialize that
            #   threatening leaf in <= D expansions so a superior rival can immediately take over.
            # - Structural residual (env.residual) triggers expansion when v_struct_sl > eta * stat_tot.
            # - Statistical envelope slack (s_opt) triggers single-node expansion ONLY when
            #   eta < inf AND either eta == 0 (Expand-First) OR after warmup when s_opt dominates
            #   eta * stat_radius AND point-contrast stat_radius has shrunk enough that expanding
            #   the coarse envelope is more efficient than further pure measurement!
            if (
                has_warmup
                and v_is_frontier
                and prefix.n_expansions < max_expansions
                and target_cert.floor_bound > epsilon
                and target_cert.floor_bound > 0.35 * target_cert.stat_radius
            ):
                _, used_exp = prefix.greedy_descent_to_leaf(
                    v_star, posterior.theta_hat, max_expansions - prefix.n_expansions
                )
                n_outside_exp += used_exp
                continue

            need_outside_exp = (
                v_is_frontier
                and prefix.n_expansions < max_expansions
                and (
                    (eta == 0.0)
                    or (v_struct_sl > eta * stat_tot)
                    or (
                        has_warmup
                        and math.isfinite(eta)
                        and target_cert.stat_radius <= 2.0 * epsilon / max(0.25, eta)
                        and v_unc_sl > eta * max(target_cert.stat_radius, 0.5 * epsilon)
                    )
                    or (target_cert.stat_radius + v_unc_sl <= 1e-9)
                )
            )
            if need_outside_exp:
                prefix.expand_node(v_star)
                n_outside_exp += 1
                continue

            # Rule 3: Measurement (targeting contrast g_t, or worst envelope displacement if v_unc_sl dominates)
            query_dir = target_cert.contrast
            if v_is_frontier and v_unc_sl > target_cert.stat_radius:
                disp = prefix.envelopes[v_star].worst_displacement(posterior.l_t)
                if float(np.linalg.norm(disp)) > 1e-12:
                    query_dir = disp

            if policy == "growing_cd_joint":
                if target_cert.stat_radius <= 0.25 * epsilon and v_unc_sl <= 0.25 * epsilon and w_ids:
                    u_w = [
                        float(prefix.envelopes[tid].center @ posterior.theta_hat)
                        + beta * posterior.norm_v_inv(prefix.envelopes[tid].center)
                        for tid in w_ids
                    ]
                    if max(u_w) - m_in > 0.5 * epsilon:
                        pick = w_ids[int(np.argmax(u_w))]
                        query_leaf(pick)
                        continue
                pick, aligned = _select_cd_joint_leaf(query_dir, prefix, posterior)
                if (not aligned) and v_is_frontier and prefix.n_expansions < max_expansions:
                    # Descend one greedy path from v_star to a terminal so T_t spans v_star's subspace in O(D)!
                    _, used_exp = prefix.greedy_descent_to_leaf(
                        v_star, posterior.theta_hat, max_expansions - prefix.n_expansions
                    )
                    n_outside_exp += used_exp
                    continue
                if pick != v_star and pick not in set(int(i) for i in target_cert.witness_ids):
                    n_proxy_queries += 1
                # Adaptive mini-batching when far from stopping (regret > 3*eps and post-warmup):
                # saves O(|F_t|) re-evaluations without changing the stopping criterion!
                n_batch = 1
                if has_warmup and best_cert.regret > 5.0 * epsilon:
                    n_batch = min(8, max_evaluations - posterior.n_obs)
                elif has_warmup and best_cert.regret > 3.0 * epsilon:
                    n_batch = min(4, max_evaluations - posterior.n_obs)
                for b_i in range(max(1, n_batch)):
                    if b_i > 0:
                        pick, _ = _select_cd_joint_leaf(query_dir, prefix, posterior)
                    query_leaf(pick)
            else:
                # growing_gp_os: LUCB endpoint query on {best_inside_witness, optimistic_outside_terminal}
                emp_w = max(
                    w_ids,
                    key=lambda tid: float(prefix.envelopes[tid].center @ posterior.theta_hat)
                    - prefix.envelopes[tid].residual,
                )
                cands = [emp_w]
                if v_star >= 0 and prefix.is_term[v_star]:
                    cands.append(v_star)
                else:
                    bit_a = 1 << a_t
                    out_terms = [tid for tid in prefix.terminals if not (prefix.action_mask[tid] & bit_a)]
                    if out_terms:
                        best_ot = max(
                            out_terms,
                            key=lambda tid: float(prefix.envelopes[tid].center @ posterior.theta_hat)
                            + beta * posterior.norm_v_inv(prefix.envelopes[tid].center)
                            + prefix.envelopes[tid].residual,
                        )
                        cands.append(best_ot)
                    else:
                        cands.extend(int(i) for i in target_cert.witness_ids if int(i) != emp_w)
                    # Only descend if existing terminals have no alignment with the active contrast
                    _, aligned = _select_cd_joint_leaf(query_dir, prefix, posterior)
                    if (not aligned) and v_is_frontier and prefix.n_expansions < max_expansions:
                        _, used_exp = prefix.greedy_descent_to_leaf(
                            v_star, posterior.theta_hat, max_expansions - prefix.n_expansions
                        )
                        n_outside_exp += used_exp
                        continue
                n_batch = 1
                if has_warmup and best_cert.regret > 5.0 * epsilon:
                    n_batch = min(8, max_evaluations - posterior.n_obs)
                elif has_warmup and best_cert.regret > 3.0 * epsilon:
                    n_batch = min(4, max_evaluations - posterior.n_obs)
                for _ in range(max(1, n_batch)):
                    pick = _select_most_uncertain_leaf(cands, prefix, posterior)
                    query_leaf(pick)

        elif policy == "growing_marginal":
            # Marginal root certification WITHOUT shared-subtree cancellation (vectorized!)
            b_ids = prefix.boundary_ids
            certifier._prefetch_nodes(b_ids, prefix, posterior, beta)
            nb = len(b_ids)
            b_lin = np.empty(nb, dtype=np.float64)
            b_stat = np.empty(nb, dtype=np.float64)
            b_sl = np.empty(nb, dtype=np.float64)
            b_res = np.empty(nb, dtype=np.float64)
            b_sc = np.empty(nb, dtype=np.float64)
            b_mask = np.empty(nb, dtype=np.int64)
            b_is_t = np.empty(nb, dtype=bool)
            for idx, vid in enumerate(b_ids):
                _, lm, psi_c, s_opt, _ = certifier._node_stats(vid, prefix, posterior, beta)
                env = prefix.envelopes[vid]
                b_lin[idx] = lm
                b_stat[idx] = beta * float(np.linalg.norm(psi_c))
                b_sl[idx] = s_opt
                b_res[idx] = env.residual
                b_sc[idx] = env.scalar_upper
                b_mask[idx] = prefix.action_mask[vid]
                b_is_t[idx] = prefix.is_term[vid]
            b_u = b_lin + b_stat + b_sl + b_res
            fin_b = np.isfinite(b_sc)
            if np.any(fin_b):
                b_u[fin_b] = np.minimum(b_u[fin_b], b_sc[fin_b])
            b_l = b_lin - b_stat - b_res

            action_l = np.full(prefix.k, -math.inf, dtype=np.float64)
            action_u = np.full(prefix.k, -math.inf, dtype=np.float64)
            action_best_l_node = [-1] * prefix.k
            action_best_u_node = [-1] * prefix.k
            action_best_u_slack = [0.0] * prefix.k
            action_best_u_stat = [0.0] * prefix.k
            action_best_u_res = [0.0] * prefix.k
            action_best_u_lin = [-math.inf] * prefix.k

            for a in range(prefix.k):
                bit_a = 1 << a
                in_a = (b_mask & bit_a) != 0
                in_a_t = in_a & b_is_t
                if np.any(in_a_t):
                    l_masked = np.where(in_a_t, b_l, -math.inf)
                    li = int(np.argmax(l_masked))
                    action_l[a] = float(b_l[li])
                    action_best_l_node[a] = b_ids[li]
                if np.any(in_a):
                    u_masked = np.where(in_a, b_u, -math.inf)
                    ui = int(np.argmax(u_masked))
                    action_u[a] = float(b_u[ui])
                    action_best_u_node[a] = b_ids[ui]
                    action_best_u_slack[a] = float(b_sl[ui])
                    action_best_u_stat[a] = float(b_stat[ui])
                    action_best_u_res[a] = float(b_res[ui])
                    action_best_u_lin[a] = float(b_lin[ui])

            marg_regs = np.zeros(prefix.k, dtype=np.float64)
            worst_rival = [0] * prefix.k
            for a in range(prefix.k):
                rivals = [b for b in range(prefix.k) if b != a]
                b_max = max(rivals, key=lambda b: action_u[b])
                worst_rival[a] = b_max
                marg_regs[a] = max(0.0, float(action_u[b_max] - action_l[a]))

            a_t = int(np.argmin(marg_regs))
            b_t = worst_rival[a_t]
            rec_root = a_t
            final_bound = float(marg_regs[a_t])
            support_sizes.append(1)
            cert_time += time.perf_counter() - tc0

            if final_bound <= epsilon:
                certified = True
                stop_reason = "certified"
                break
            if posterior.n_obs >= max_evaluations:
                stop_reason = "budget_eval"
                break

            # Expand optimistic unexpanded node on either b_t or a_t when residual/slack dominates
            v_rival = action_best_u_node[b_t]
            v_in = action_best_u_node[a_t]
            l_node = action_best_l_node[a_t]
            in_sl = action_best_u_slack[a_t]
            riv_sl = action_best_u_slack[b_t]
            in_res = action_best_u_res[a_t]
            riv_res = action_best_u_res[b_t]
            in_st = action_best_u_stat[a_t]
            riv_st = action_best_u_stat[b_t]
            has_warmup = posterior.n_obs >= max(posterior.d, prefix.k)
            inside_cooldown_ok = (posterior.n_obs - last_inside_refresh_obs) >= max(posterior.d, 10)

            l_env = prefix.envelopes[l_node]
            m_l = float(l_env.center @ posterior.theta_hat) - l_env.residual
            rival_floor = action_best_u_lin[b_t] + riv_res - m_l
            if (
                v_in in prefix.frontier
                and prefix.n_expansions < max_expansions
                and (
                    (in_res > eta * (in_st + in_sl))
                    or (
                        has_warmup
                        and inside_cooldown_ok
                        and in_sl >= riv_sl
                        and (
                            (math.isfinite(eta) and in_st <= epsilon / max(0.25, eta) and in_sl > eta * in_st)
                            or (rival_floor > 0.5 * epsilon and rival_floor > 0.35 * riv_st and action_best_u_lin[a_t] > m_l + 0.5 * epsilon)
                        )
                    )
                )
            ):
                if rival_floor > 0.5 * epsilon and in_res <= eta * (in_st + in_sl):
                    _, used_e = prefix.greedy_descent_to_leaf(
                        v_in, posterior.theta_hat, max_expansions - prefix.n_expansions
                    )
                    n_inside_exp += used_e
                    last_inside_refresh_obs = posterior.n_obs
                else:
                    prefix.expand_node(v_in)
                    n_inside_exp += 1
                    last_inside_refresh_obs = posterior.n_obs
                continue
            if (
                v_rival in prefix.frontier
                and prefix.n_expansions < max_expansions
                and (
                    (riv_res > eta * (riv_st + riv_sl))
                    or (has_warmup and rival_floor > epsilon and rival_floor > 0.35 * riv_st)
                    or (
                        has_warmup
                        and math.isfinite(eta)
                        and riv_st <= epsilon / max(0.25, eta)
                        and riv_sl > eta * riv_st
                    )
                )
            ):
                if rival_floor > epsilon and riv_res <= eta * (riv_st + riv_sl):
                    _, used_e = prefix.greedy_descent_to_leaf(
                        v_rival, posterior.theta_hat, max_expansions - prefix.n_expansions
                    )
                    n_outside_exp += used_e
                else:
                    prefix.expand_node(v_rival)
                    n_outside_exp += 1
                continue

            # Measure higher-uncertainty endpoint among l_node and rival's optimistic terminal
            cands = [l_node]
            if prefix.is_term[v_rival]:
                cands.append(v_rival)
            else:
                riv_terms = prefix.action_witness_terminals(b_t)
                if riv_terms:
                    best_rt = max(
                        riv_terms,
                        key=lambda tid: float(prefix.envelopes[tid].center @ posterior.theta_hat)
                        + beta * posterior.norm_v_inv(prefix.envelopes[tid].center),
                    )
                    cands.append(best_rt)
                elif v_rival in prefix.frontier and prefix.n_expansions < max_expansions:
                    prefix.expand_node(v_rival)
                    n_outside_exp += 1
                    continue
            n_batch = 1
            if has_warmup and final_bound > 5.0 * epsilon:
                n_batch = min(8, max_evaluations - posterior.n_obs)
            elif has_warmup and final_bound > 3.0 * epsilon:
                n_batch = min(4, max_evaluations - posterior.n_obs)
            for _ in range(max(1, n_batch)):
                pick = _select_most_uncertain_leaf(cands, prefix, posterior)
                query_leaf(pick)

        elif policy == "growing_best_leaf":
            # Pelissier et al. (2019)-style Best-Leaf Identification on the EXACT same growing DAG
            # and conic ellipsoid (generous comparator: gets correlated conic contrast + CD queries,
            # differing ONLY in certifying a single leaf y* instead of a root action!).
            t_ids = prefix.terminals
            t_phi = np.stack([prefix.envelopes[i].center for i in t_ids], axis=0)
            t_xi = np.array([prefix.envelopes[i].residual for i in t_ids], dtype=np.float64)
            t_m = (t_phi @ posterior.theta_hat) - t_xi
            best_local = int(np.argmax(t_m))
            y_star = t_ids[best_local]
            y_phi = t_phi[best_local]
            y_psi = posterior.l_t @ y_phi
            y_m = float(t_m[best_local])
            y_l = y_m - beta * float(np.linalg.norm(y_psi))

            # Find worst challenger v in B_t \ {y_star} (INCLUDES same-root leaves & subtrees!)
            b_ids = prefix.boundary_ids
            certifier._prefetch_nodes(b_ids, prefix, posterior, beta)
            nb = len(b_ids)
            b_phi = np.empty((nb, posterior.d), dtype=np.float64)
            b_m = np.empty(nb, dtype=np.float64)
            b_psi = np.empty((nb, posterior.d), dtype=np.float64)
            b_sl = np.empty(nb, dtype=np.float64)
            b_res = np.empty(nb, dtype=np.float64)
            b_sc = np.empty(nb, dtype=np.float64)
            for idx, vid in enumerate(b_ids):
                phi_opt, m_c, psi_c, s_opt, _ = certifier._node_stats(vid, prefix, posterior, beta)
                env = prefix.envelopes[vid]
                b_phi[idx] = phi_opt
                b_m[idx] = m_c
                b_psi[idx] = psi_c
                b_sl[idx] = s_opt
                b_res[idx] = env.residual
                b_sc[idx] = env.scalar_upper
            stat_arr = beta * np.linalg.norm(b_psi - y_psi[None, :], axis=1)
            u_arr = (b_m - y_m) + stat_arr + b_sl + b_res
            fin_b = np.isfinite(b_sc)
            if np.any(fin_b):
                u_arr[fin_b] = np.minimum(u_arr[fin_b], b_sc[fin_b] - y_l)
            for idx, vid in enumerate(b_ids):
                if vid == y_star:
                    u_arr[idx] = -math.inf
                    break
            best_i = int(np.argmax(u_arr))
            best_u = float(u_arr[best_i])
            if best_u > -math.inf:
                v_star = b_ids[best_i]
                best_env_sl = float(b_sl[best_i])
                best_stat_r = float(stat_arr[best_i])
                best_floor = float(b_m[best_i] - y_m + b_res[best_i])
                best_contrast = b_phi[best_i] - y_phi
            else:
                v_star = -1
                best_env_sl = 0.0
                best_stat_r = 0.0
                best_floor = 0.0
                best_contrast = np.zeros(posterior.d, dtype=np.float64)

            # Map certified leaf back to a root action reaching it
            mask_y = prefix.action_mask[y_star]
            rec_root = next((a for a in range(prefix.k) if mask_y & (1 << a)), 0)
            final_bound = max(0.0, float(best_u)) if v_star >= 0 else 0.0
            support_sizes.append(1)
            cert_time += time.perf_counter() - tc0

            if final_bound <= epsilon:
                certified = True
                stop_reason = "certified"
                break
            if posterior.n_obs >= max_evaluations:
                stop_reason = "budget_eval"
                break

            v_is_frontier = v_star >= 0 and (v_star in prefix.frontier)
            has_warmup = posterior.n_obs >= posterior.d
            if (
                v_is_frontier
                and prefix.n_expansions < max_expansions
                and best_floor > epsilon
                and best_floor > 0.35 * best_stat_r
            ):
                _, used_e = prefix.greedy_descent_to_leaf(
                    v_star, posterior.theta_hat, max_expansions - prefix.n_expansions
                )
                n_outside_exp += used_e
                continue
            v_res = prefix.envelopes[v_star].residual if v_star >= 0 else 0.0
            if (
                v_is_frontier
                and prefix.n_expansions < max_expansions
                and (
                    (eta == 0.0)
                    or (v_res > eta * (best_stat_r + best_env_sl))
                    or (
                        has_warmup
                        and math.isfinite(eta)
                        and best_stat_r <= 2.0 * epsilon / max(0.25, eta)
                        and best_env_sl > eta * max(best_stat_r, 0.5 * epsilon)
                    )
                    or (best_stat_r + best_env_sl <= 1e-9)
                )
            ):
                prefix.expand_node(v_star)
                n_outside_exp += 1
                continue

            pick, aligned = _select_cd_joint_leaf(best_contrast, prefix, posterior)
            if (not aligned) and v_is_frontier and prefix.n_expansions < max_expansions:
                _, used_e = prefix.greedy_descent_to_leaf(
                    v_star, posterior.theta_hat, max_expansions - prefix.n_expansions
                )
                n_outside_exp += used_e
                continue
            if pick != v_star and pick != y_star:
                n_proxy_queries += 1
            n_batch = 1
            if has_warmup and final_bound > 5.0 * epsilon:
                n_batch = min(8, max_evaluations - posterior.n_obs)
            elif has_warmup and final_bound > 3.0 * epsilon:
                n_batch = min(4, max_evaluations - posterior.n_obs)
            for b_i in range(max(1, n_batch)):
                if b_i > 0:
                    pick, _ = _select_cd_joint_leaf(best_contrast, prefix, posterior)
                query_leaf(pick)

        else:
            raise ValueError(f"Unknown growing policy: {policy!r}")

    else:
        stop_reason = "budget_steps"

    if not certified and prefix.n_expansions >= max_expansions and posterior.n_obs < max_evaluations:
        stop_reason = "budget_expand"

    true_vals = problem.true_root_values()
    true_regret = max(0.0, float(np.max(true_vals) - true_vals[rec_root]))
    false_cert = bool(certified and true_regret > epsilon + 1e-12)

    return GrowingRunResult(
        policy=policy,
        eta=float(eta),
        certified=certified,
        recommended_root=int(rec_root),
        n_evaluations=int(posterior.n_obs),
        n_expansions=int(prefix.n_expansions),
        n_nodes=int(prefix.n_nodes),
        n_terminals=int(len(prefix.terminals)),
        n_frontier=int(len(prefix.frontier)),
        transposition_merges=int(prefix.transposition_merges),
        total_leaf_count=int(problem.total_leaf_count),
        cert_regret_bound=float(final_bound),
        true_root_regret=float(true_regret),
        false_certificate=false_cert,
        beta_at_stop=float(posterior.beta()),
        mean_witness_support=float(np.mean(support_sizes)) if support_sizes else 1.0,
        max_witness_support=int(max(support_sizes)) if support_sizes else 1,
        n_inside_expansions=int(n_inside_exp),
        n_outside_expansions=int(n_outside_exp),
        n_proxy_queries=int(n_proxy_queries),
        cert_time_s=float(cert_time),
        total_runtime_s=float(time.perf_counter() - t0),
        stop_reason=stop_reason,
    )


# ---------------------------------------------------------------------------
# 6. Reusable Implicit Growing-DAG Benchmark Families
# ---------------------------------------------------------------------------


class CommutingUpgradeGrowingDAG(ImplicitDAG):
    """Exponentially large commuting multi-site upgrade DAG (Suite 1A).

    ``n_sites`` sites start at wildtype ``0``; each step upgrades one unmutated site
    to variant ``v in {1..n_variants}`` until ``depth`` sites are upgraded.
    Canonical state = sorted tuple of ``(site, variant)`` pairs, producing massive
    commuting transposition merges across root actions!

    Total leaves: ``|Z| = C(n_sites, depth) * n_variants^depth`` (up to ~6e7 at depth=10).
    Root actions ``K``: first upgrade choices ``(site_a, var_a)`` over top-``K`` initial
    moves (plus optional shared near-optimal plateau structure).
    """

    def __init__(
        self,
        *,
        n_sites: int = 8,
        depth: int = 4,
        n_variants: int = 3,
        n_root_actions: int = 6,
        d: int = 10,
        seed: int = 0,
        root_gap: float = 0.14,
        theta_norm: float = 1.6,
    ) -> None:
        self.n_sites = int(n_sites)
        self.depth = int(depth)
        self.n_variants = int(n_variants)
        self._d = int(d)
        self.seed = int(seed)

        rng = np.random.default_rng(seed)
        # Per-(site, variant) increment vectors g_{i,v} in R^d
        raw = rng.standard_normal((n_sites, n_variants, d))
        raw /= np.linalg.norm(raw, axis=2, keepdims=True)
        # Scale so terminal feature vector sum has O(1) norm
        self.site_vecs = raw / math.sqrt(float(depth))

        # True theta* with controlled norm and clear root-action gap
        theta = rng.standard_normal(d)
        theta = theta / float(np.linalg.norm(theta)) * theta_norm
        self.theta_true = theta

        # Build K root actions with BOTH genuine root-decision separation (gap >= root_gap)
        # AND massive commuting shared transpositions:
        #   - Action 0 = best move (s0, v0) at anchor site s0 (strictly optimal when n_sites > depth
        #     and rivals are suboptimal variants at s0 plus lower-ranked sites outside the top-depth set!)
        #   - Remaining K-1 actions mix (a) alternative variants at site s0 (correlated downstream sites!)
        #     and (b) non-top-depth sites (which commute & merge with Action 0 at depth 2 with huge overlap!).
        site_best = np.max(self.site_vecs @ theta, axis=1)  # (n_sites,)
        site_best_var = np.argmax(self.site_vecs @ theta, axis=1) + 1  # 1..n_variants
        site_order = np.argsort(-site_best, kind="mergesort")
        s0 = int(site_order[0])
        v0 = int(site_best_var[s0])

        chosen: list[tuple[int, int]] = [(s0, v0)]
        # Add alternative variants at s0 (up to min(2, n_variants - 1))
        for vp in range(1, n_variants + 1):
            if vp != v0 and len(chosen) < n_root_actions:
                chosen.append((s0, vp))
                if len(chosen) >= min(n_root_actions, 3):
                    break
        # Add commuting sites ranked outside the top-depth set (indices depth..n_sites-1)
        for s_bad in site_order[depth:]:
            if len(chosen) >= n_root_actions:
                break
            chosen.append((int(s_bad), int(site_best_var[int(s_bad)])))
        # Fill any remaining slots with alternative variants on top sites (strictly suboptimal variants!)
        for s_top in site_order[1:depth]:
            for vp in range(1, n_variants + 1):
                if len(chosen) >= n_root_actions:
                    break
                if vp != int(site_best_var[int(s_top)]) and (int(s_top), vp) not in chosen:
                    chosen.append((int(s_top), vp))

        # Calibrate true root gap V(a*) - max_{a != a*} V(a) to at least root_gap by shifting
        # suboptimal root-move vectors down along theta_true (keeping all top-depth shared sites intact!).
        unit_t = self.theta_true / max(1e-12, float(np.linalg.norm(self.theta_true)))
        t_norm = float(np.linalg.norm(self.theta_true))
        v_star = float(self._compute_root_values([chosen[0]])[0])
        for idx_r in range(1, len(chosen)):
            sr, vr = chosen[idx_r]
            vr_val = float(self._compute_root_values([(sr, vr)])[0])
            gap_r = v_star - vr_val
            if gap_r < root_gap:
                shift = (root_gap - gap_r) / t_norm
                self.site_vecs[sr, vr - 1] -= shift * unit_t
                # If sr is a non-top-depth site, shift its other variants too so sr stays below top-depth
                if sr in set(int(x) for x in site_order[depth:]):
                    for vp in range(1, n_variants + 1):
                        if vp != vr:
                            cur_g = float(self.site_vecs[sr, vp - 1] @ self.theta_true)
                            tgt_g = float(self.site_vecs[sr, vr - 1] @ self.theta_true)
                            if cur_g > tgt_g:
                                self.site_vecs[sr, vp - 1] -= ((cur_g - tgt_g + 0.02) / t_norm) * unit_t
                v_star = float(self._compute_root_values([chosen[0]])[0])

        # Shuffle root action order deterministically so optimal action is not always index 0
        perm = rng.permutation(len(chosen))
        self.root_moves: list[tuple[int, int]] = [chosen[int(i)] for i in perm]
        self._root_vals = self._compute_root_values(self.root_moves)
        # Exact count of depth-D leaves reachable from self.root_moves via DP over forbidden root moves
        forb_per_site = [0] * n_sites
        for s_m, _ in self.root_moves:
            forb_per_site[s_m] += 1
        dp = [0] * (depth + 1)
        dp[0] = 1
        for s_idx in range(n_sites):
            allowed = n_variants - forb_per_site[s_idx]
            for j in range(depth, 0, -1):
                dp[j] += dp[j - 1] * allowed
        all_leaves = math.comb(n_sites, depth) * (n_variants ** depth)
        self._total_leaves = all_leaves - dp[depth]
        self._state_meta: dict[Hashable, tuple[np.ndarray, np.ndarray, int]] = {}

    def _get_state_meta(self, state: Hashable) -> tuple[np.ndarray, np.ndarray, int]:
        meta = self._state_meta.get(state)
        if meta is not None:
            return meta
        base = np.zeros(self._d, dtype=np.float64)
        used = np.zeros(self.n_sites, dtype=bool)
        for s, v in state:
            base += self.site_vecs[s, v - 1]
            used[s] = True
        meta = (base, used, self.depth - len(state))
        self._state_meta[state] = meta
        return meta

    def greedy_child_hint(self, state: Hashable, children: Sequence[Hashable], theta_hat: np.ndarray) -> Hashable:
        sb = np.max(self.site_vecs @ theta_hat, axis=1)
        order = np.argsort(-sb, kind="mergesort")
        best_c = children[0]
        best_v = -math.inf
        for c in children:
            base, used, rem = self._get_state_meta(c)
            val = float(base @ theta_hat)
            if rem > 0:
                taken = 0
                for s in order:
                    if not used[int(s)]:
                        val += float(sb[int(s)])
                        taken += 1
                        if taken == rem:
                            break
            if val > best_v:
                best_v = val
                best_c = c
        return best_c

    def batch_optimistic_stats(
        self,
        states: Sequence[Hashable],
        theta_hat: np.ndarray,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        beta: float,
        step_cache: dict[str, Any],
    ) -> tuple[np.ndarray, np.ndarray, np.ndarray] | None:
        metas = [self._get_state_meta(st) for st in states]
        bases = np.stack([m[0] for m in metas], axis=0)
        used = np.stack([m[1] for m in metas], axis=0)
        rems = np.array([m[2] for m in metas], dtype=np.int64)
        return vectorized_group_sparse_opt_stats(
            self.site_vecs, bases, used, rems, theta_hat, l_t, beta, step_cache, cache_key="comm_vec"
        )

    def _compute_root_values(self, moves: Sequence[tuple[int, int]]) -> np.ndarray:
        # Exact optimal completion for any move (s, v) is closed-form in O(n_sites log n_sites)!
        site_best = np.max(self.site_vecs @ self.theta_true, axis=1)
        vals = np.empty(len(moves), dtype=np.float64)
        for i, (s, v) in enumerate(moves):
            rem = np.delete(site_best, s)
            top_rem = np.sort(rem)[-(self.depth - 1) :] if self.depth > 1 else np.array([0.0])
            vals[i] = float(self.site_vecs[s, v - 1] @ self.theta_true) + float(np.sum(top_rem))
        return vals

    @property
    def feature_dim(self) -> int:
        return self._d

    @property
    def n_root_actions(self) -> int:
        return len(self.root_moves)

    @property
    def total_leaf_count(self) -> int:
        return self._total_leaves

    def root_state(self) -> Hashable:
        return ()

    def root_children(self) -> list[Hashable]:
        return [(mv,) for mv in self.root_moves]

    def is_terminal(self, state: Hashable) -> bool:
        return len(state) >= self.depth

    def expand(self, state: Hashable) -> list[Hashable]:
        if len(state) >= self.depth:
            return []
        used = {s for s, _ in state}
        # Canonical transposition merging: sort tuple of (site, variant) pairs!
        out: list[Hashable] = []
        for s in range(self.n_sites):
            if s in used:
                continue
            for v in range(1, self.n_variants + 1):
                nxt = tuple(sorted(state + ((s, v),)))
                out.append(nxt)
        return out

    def envelope(self, state: Hashable) -> SubtreeEnvelope:
        base = np.zeros(self._d, dtype=np.float64)
        used = set()
        for s, v in state:
            base += self.site_vecs[s, v - 1]
            used.add(s)
        rem = self.depth - len(state)
        if rem <= 0:
            return SubtreeEnvelope.point(base, residual=0.0)
        groups = [self.site_vecs[s] for s in range(self.n_sites) if s not in used]
        return SubtreeEnvelope.group_sparse(
            base=base,
            groups=groups,
            max_groups=rem,
            exact_count=True,
            residual=0.0,
        )

    def fast_optimistic_stats(
        self,
        state: Hashable,
        theta_hat: np.ndarray,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        beta: float,
        step_cache: dict[str, Any],
    ) -> tuple[np.ndarray, float, float] | None:
        """Exact O(n_sites log n_sites) equivalent of ``optimistic_vertex_and_slack`` sharing
        a single per-observation BLAS evaluation of ``site_vecs`` across ALL frontier nodes!"""
        rem = self.depth - len(state)
        if rem <= 0:
            return None
        tbl = step_cache.get("commuting_tbl")
        if tbl is None:
            all_sc = self.site_vecs @ theta_hat  # (L, V)
            best_v = np.argmax(all_sc, axis=1)  # (L,)
            idx_l = np.arange(self.n_sites)
            best_sc = all_sc[idx_l, best_v]  # (L,)
            best_vecs = self.site_vecs[idx_l, best_v]  # (L, d)
            wg = self.site_vecs @ l_t.T  # (L, V, d)
            wg_best = wg[idx_l, best_v]  # (L, d)
            gv_norms = np.linalg.norm(wg_best, axis=1)  # (L,)
            if self.n_variants > 1:
                diffs_w = wg - wg_best[:, None, :]
                lin_d = all_sc - best_sc[:, None]
                omega_site = np.maximum(0.0, np.max(lin_d + beta * np.linalg.norm(diffs_w, axis=2), axis=1))
            else:
                omega_site = np.zeros(self.n_sites, dtype=np.float64)
            norm_all = np.linalg.norm(wg, axis=2)  # (L, V)
            # Precompute site_max_u = max_v (all_sc + beta * norm_all) so alpha(site, tau) = site_max_u - tau!
            site_max_u = np.max(all_sc + beta * norm_all, axis=1)  # (L,)
            site_order = np.argsort(-best_sc, kind="mergesort")
            tbl = (best_sc, best_vecs, gv_norms, omega_site, site_max_u, site_order)
            step_cache["commuting_tbl"] = tbl

        best_sc, best_vecs, gv_norms, omega_site, site_max_u, site_order = tbl
        base = np.zeros(self._d, dtype=np.float64)
        used = set()
        for s, v in state:
            base += self.site_vecs[s, v - 1]
            used.add(s)

        avail = [int(s) for s in site_order if int(s) not in used]
        s_star = avail[:rem]
        s_out = avail[rem:]
        phi_opt = base + np.sum(best_vecs[s_star], axis=0)
        lin_max = float(phi_opt @ theta_hat)
        tau = float(best_sc[s_star[-1]])

        om_in = omega_site[s_star]
        s_opt = float(np.sum(om_in))
        if s_out:
            gamma_tilde = (tau - best_sc[s_star]) + beta * gv_norms[s_star] - om_in
            alpha_out = site_max_u[s_out] - tau
            alpha_sorted = np.sort(alpha_out)[::-1]
            gamma_sorted = np.sort(gamma_tilde)[::-1]
            q_max = min(len(alpha_sorted), len(gamma_sorted))
            s_opt += float(np.sum(np.maximum(0.0, alpha_sorted[:q_max] + gamma_sorted[:q_max])))
        return phi_opt, s_opt, lin_max

    def true_mean(self, state: Hashable) -> float:
        return float(self.envelope(state).center @ self.theta_true)

    def true_root_values(self) -> np.ndarray:
        return self._root_vals.copy()


class SharedPlateauSeparationDAG(ImplicitDAG):
    """Exact instantiation of the Theorem M.3(c) Exponential Separation Family G_D.

    Structure (depth ``D >= 3``, ``K = 2`` root actions, ``d = 2``, ``|Z| = 3 * 2^{D-1}``):
      - Root action 0 reaches:
          * Exclusive near-optimal binary tree T_in (depth D-1, 2^{D-1} leaves, mu in [0.99, 1.00])
          * Shared ambiguous binary tree T_sh (depth D-1, 2^{D-1} leaves, mu = 0.95, internal
            epistatic residual bar_xi = 0.45 that resolves to 0.0 only at leaves!)
      - Root action 1 reaches:
          * The EXACT SAME shared subtree root u_sh (canonical transposition merge!)
          * Exclusive suboptimal binary tree T_bad (depth D-1, 2^{D-1} leaves, mu <= 0.45)

    Theorem M.3(c) proves:
      - ``growing_cd_joint`` cancels u_sh unconditionally -> O(D) expansions, O(d log(1/delta)) evals!
      - ``growing_marginal`` cannot cancel u_sh -> Omega(2^D) expansions!
      - ``growing_best_leaf`` must resolve all 2^{D-1} leaves of T_sh & T_in -> Omega(2^D) expansions!
    """

    def __init__(self, depth: int = 8, internal_residual: float = 0.45) -> None:
        if depth < 3:
            raise ValueError("depth must be >= 3")
        self.depth = int(depth)
        self.internal_residual = float(internal_residual)
        self.theta_true = np.array([1.0, 0.45], dtype=np.float64)
        self._leaves_per_tree = 1 << (self.depth - 1)

    @property
    def feature_dim(self) -> int:
        return 2

    @property
    def n_root_actions(self) -> int:
        return 2

    @property
    def total_leaf_count(self) -> int:
        return 3 * self._leaves_per_tree

    def root_state(self) -> Hashable:
        return ("root",)

    def root_children(self) -> list[Hashable]:
        return [("act", 0), ("act", 1)]

    def is_terminal(self, state: Hashable) -> bool:
        return state[0] == "tree" and state[2] == self.depth - 1

    def expand(self, state: Hashable) -> list[Hashable]:
        kind = state[0]
        if kind == "act":
            if state[1] == 0:
                return [("tree", "in", 0, 0), ("tree", "sh", 0, 0)]
            return [("tree", "sh", 0, 0), ("tree", "bad", 0, 0)]
        if kind == "tree":
            tag, lvl, idx = state[1], state[2], state[3]
            if lvl >= self.depth - 1:
                return []
            return [("tree", tag, lvl + 1, 2 * idx), ("tree", tag, lvl + 1, 2 * idx + 1)]
        return []

    def envelope(self, state: Hashable) -> SubtreeEnvelope:
        kind = state[0]
        if kind == "root":
            return SubtreeEnvelope.box(
                np.array([0.0, 0.0]), np.array([1.0, 1.0]), residual=self.internal_residual
            )
        if kind == "act":
            if state[1] == 0:
                return SubtreeEnvelope.box(
                    np.array([0.80, 0.0]), np.array([1.0, 0.0]), residual=self.internal_residual
                )
            return SubtreeEnvelope.box(
                np.array([0.0, 0.0]), np.array([0.80, 1.0]), residual=self.internal_residual
            )
        tag, lvl, idx = state[1], state[2], state[3]
        is_leaf = lvl == self.depth - 1
        if tag == "in":
            # All leaves lie in tight plateau [0.99, 1.00] along axis 0
            frac = idx / float(max(1, 1 << lvl))
            span = 1.0 / float(max(1, 1 << lvl))
            lo = np.array([0.99 + 0.01 * frac, 0.0])
            hi = np.array([0.99 + 0.01 * (frac + span), 0.0])
            if is_leaf:
                return SubtreeEnvelope.point(np.array([0.99 + 0.01 * (idx / float(max(1, self._leaves_per_tree - 1))), 0.0]))
            return SubtreeEnvelope.box(lo, hi, residual=0.0)
        if tag == "sh":
            # Shared tree: true leaves sit at (0.80, 0.0), internal nodes carry unresolved epistatic residual
            # (0.80 + 0.45 = 1.25 > 1.00), so Marginal & Best-Leaf must expand all 2^{D-1} leaves!
            if is_leaf:
                return SubtreeEnvelope.point(np.array([0.80, 0.0]), residual=0.0)
            return SubtreeEnvelope.point(np.array([0.80, 0.0]), residual=self.internal_residual)
        # tag == "bad": suboptimal tree along axis 1 (mu <= 0.45), hierarchical box partition
        frac = idx / float(max(1, 1 << lvl))
        span = 1.0 / float(max(1, 1 << lvl))
        if is_leaf:
            val = 0.90 + 0.10 * (idx / float(max(1, self._leaves_per_tree - 1)))
            return SubtreeEnvelope.point(np.array([0.0, val]), residual=0.0)
        return SubtreeEnvelope.box(
            np.array([0.0, 0.90 + 0.10 * frac]),
            np.array([0.0, 0.90 + 0.10 * (frac + span)]),
            residual=0.0,
        )

    def true_mean(self, state: Hashable) -> float:
        return float(self.envelope(state).center @ self.theta_true)

    def true_root_values(self) -> np.ndarray:
        return np.array([1.00, 0.80], dtype=np.float64)


__all__ = [
    "CommutingUpgradeGrowingDAG",
    "EnvelopeChallengerResult",
    "GrowingActionCertificate",
    "GrowingEllipsoidCertifier",
    "GrowingLinearPosterior",
    "GrowingPrefixDAG",
    "GrowingRunResult",
    "ImplicitDAG",
    "SharedPlateauSeparationDAG",
    "SubtreeEnvelope",
    "run_growing_campaign",
    "solve_envelope_challenger",
]
