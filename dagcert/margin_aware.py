"""Margin-Aware Contrast-Directed Joint Acquisition (MA-CD-Joint & MA-CD-Joint-Safe).

Implements the geometry-derived standardized-separation acquisition rule:
  - Standardized certification margin:
        H_t(z, p) = (eps - g_{z,p}^T m_t) / sqrt(g_{z,p}^T Sigma_t g_{z,p}),
        H_t(a)    = min_{z notin S(a)} max_{p in Delta(S(a))} H_t(z, p).
    Exact equivalence with the conic ellipsoid certificate:
        R_t(a) <= eps   <==>   H_t(a) >= beta_t.
  - One-step rank-1 Gaussian fantasy lookahead integrated via 9-point standard-normal
    Gauss-Hermite quadrature over a deduplicated retained witness pool
    (current conic mixture + top-4 posterior mean + top-4 UCB) with per-challenger
    witness reselection and active-bottleneck switching across all excluded challengers:
        alpha_t^MA(x) = (E_xi[Psi(H_{t+1}^{(x, xi)}(b_t))] - Psi(H_t(b_t))) / c_x,
        Psi(h) = min(1, h / beta_t).
  - Two controlled variants preserving the exact eps/2 safeguard and conic stopping rule:
      * ``ma_cd_joint``      : margin-aware lookahead with eps/2 safeguard override.
      * ``ma_cd_joint_safe`` : alternates mandatory CD-Joint steps (even steps) with
                               margin-aware lookahead (odd steps), inheriting the
                               finite-sample termination bound up to a factor of 2.
"""
from __future__ import annotations

from dataclasses import dataclass
import ctypes
import hashlib
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any

import numpy as np

from dagcert._core.v7_bayesian_ucd import (
    ActionCertificate,
    JointEllipsoidCertifier,
    SupportStructure,
)
from dagcert._core.v12_bed_acquisition import (
    SharedGaussianPosterior,
    correlated_kg_log_scores,
)

# Exact 9-point standard-normal Gauss-Hermite quadrature: E_{xi ~ N(0,1)}[f(xi)] ~= sum_k w_k f(xi_k)
_GH_X, _GH_W = np.polynomial.hermite.hermgauss(9)
GAUSS_HERMITE_9_NODES: np.ndarray = np.ascontiguousarray(math.sqrt(2.0) * _GH_X, dtype=np.float64)
GAUSS_HERMITE_9_WEIGHTS: np.ndarray = np.ascontiguousarray(_GH_W / math.sqrt(math.pi), dtype=np.float64)

_CPP_MA_SOURCE = Path(__file__).resolve().parent / "_native" / "_cpp_v17_ma.cpp"


class _CppV17MARunner:
    """Optional on-demand `-O3 -std=c++17` accelerator for MA-CD-Joint 9-point quadrature."""

    _lib = None
    _checked = False

    @classmethod
    def get_lib(cls):
        if cls._checked:
            return cls._lib
        cls._checked = True
        if not _CPP_MA_SOURCE.is_file():
            return None
        cxx = os.environ.get("CXX") or shutil.which("g++") or shutil.which("clang++")
        if not cxx:
            return None
        try:
            sha = hashlib.sha256(b"-ffp-contract=off" + _CPP_MA_SOURCE.read_bytes()).hexdigest()[:16]
            ext = ".dylib" if sys.platform == "darwin" else ".so"
            so_path = Path(tempfile.gettempdir()) / f"dag_mcts_v17_ma_{sha}{ext}"
            if not so_path.is_file():
                tmp_so = so_path.with_name(f"{so_path.stem}_{os.getpid()}.tmp{ext}")
                try:
                    subprocess.run(
                        [
                            cxx, "-O3", "-ffp-contract=off", "-march=native", "-std=c++17", "-Wall", "-Wextra", "-Werror",
                            "-shared", "-fPIC", str(_CPP_MA_SOURCE), "-o", str(tmp_so),
                        ],
                        check=True,
                        stderr=subprocess.DEVNULL,
                    )
                except subprocess.CalledProcessError:
                    subprocess.run(
                        [
                            cxx, "-O3", "-ffp-contract=off", "-std=c++17", "-Wall", "-Wextra",
                            "-shared", "-fPIC", str(_CPP_MA_SOURCE), "-o", str(tmp_so),
                        ],
                        check=True,
                        stderr=subprocess.DEVNULL,
                    )
                os.replace(tmp_so, so_path)
            lib = ctypes.CDLL(str(so_path))
            c_dbl_p = ctypes.POINTER(ctypes.c_double)
            lib.ma_cd_joint_quadrature.argtypes = [
                ctypes.c_int32,
                ctypes.c_int32,
                ctypes.c_int32,
                ctypes.c_int32,
                ctypes.c_double,
                c_dbl_p,
                c_dbl_p,
                c_dbl_p,
                c_dbl_p,
                c_dbl_p,
                c_dbl_p,
                c_dbl_p,
            ]
            lib.ma_cd_joint_quadrature.restype = None
            cls._lib = lib
        except Exception:
            cls._lib = None
        return cls._lib


def _ma_quadrature_expected_psi(
    d_zw: np.ndarray,
    s2_zw: np.ndarray,
    v_c: np.ndarray,
    v_w: np.ndarray,
    beta: float,
    *,
    use_cpp: bool = True,
) -> np.ndarray:
    """Compute E_xi[Psi(H_{t+1}^{(x,xi)}(b_t))] over all Q shortlisted queries (exact C++17 or NumPy)."""
    n_c, n_w = d_zw.shape
    n_q = v_c.shape[1]
    if use_cpp:
        lib = _CppV17MARunner.get_lib()
        if lib is not None:
            d_c = np.ascontiguousarray(d_zw, dtype=np.float64)
            s2_c = np.ascontiguousarray(s2_zw, dtype=np.float64)
            vc_c = np.ascontiguousarray(v_c, dtype=np.float64)
            vw_c = np.ascontiguousarray(v_w, dtype=np.float64)
            out = np.empty(n_q, dtype=np.float64)
            c_dbl_p = ctypes.POINTER(ctypes.c_double)
            lib.ma_cd_joint_quadrature(
                int(n_c),
                int(n_w),
                int(n_q),
                int(len(GAUSS_HERMITE_9_NODES)),
                float(beta),
                d_c.ctypes.data_as(c_dbl_p),
                s2_c.ctypes.data_as(c_dbl_p),
                vc_c.ctypes.data_as(c_dbl_p),
                vw_c.ctypes.data_as(c_dbl_p),
                GAUSS_HERMITE_9_NODES.ctypes.data_as(c_dbl_p),
                GAUSS_HERMITE_9_WEIGHTS.ctypes.data_as(c_dbl_p),
                out.ctypes.data_as(c_dbl_p),
            )
            return out

    # Pure-NumPy reference path (exact parity)
    q_zwx = v_c[:, None, :] - v_w[None, :, :]  # (n_c, W, Q)
    s2_post = s2_zw[:, :, None] - (q_zwx * q_zwx)
    zero_post = s2_post <= 1e-18
    inv_s_post = 1.0 / np.sqrt(np.where(zero_post, 1.0, s2_post))
    expected_psi = np.zeros(n_q, dtype=np.float64)
    has_zero = bool(np.any(zero_post))
    d_bcast = d_zw[:, :, None]
    for xi_k, wt_k in zip(GAUSS_HERMITE_9_NODES, GAUSS_HERMITE_9_WEIGHTS):
        num_k = d_bcast - float(xi_k) * q_zwx
        if has_zero:
            h_k = np.where(
                zero_post,
                np.where(num_k >= -1e-12, beta, -1e6 * beta),
                num_k * inv_s_post,
            )
        else:
            h_k = num_k * inv_s_post
        h_z = np.max(h_k, axis=1)
        h_root = np.min(h_z, axis=0)
        expected_psi += float(wt_k) * np.minimum(1.0, h_root / beta)
    return expected_psi


@dataclass(frozen=True)
class MarginAwareSelection:
    """Selected query arm together with mechanistic diagnostics for one acquisition step."""

    arm: int
    candidate_root: int
    challenger_idx: int
    cd_arm: int
    safeguard_triggered: bool
    mandatory_cd_step: bool
    used_ma_query: bool
    ma_gain: float
    inside_support: bool
    mixture_support: int
    active_contrast_var: float
    retained_witness_margin: float
    active_contrast_margin: float
    std_cert_margin: float


def compute_exact_standardized_margin(
    action: int,
    supports: SupportStructure,
    means: np.ndarray,
    sigma_mat: np.ndarray,
    epsilon: float,
    beta: float,
    certifier: JointEllipsoidCertifier | None = None,
) -> float:
    """Compute exact standardized margin ``H_t(a) = min_{z notin S(a)} max_{p in Delta(S(a))} H_t(z, p)``
    using the exact conic solver (for unit verification & diagnostic checkpoints).

    For any zero-variance contrast ``s_g^2 <= 1e-18``, returns ``+inf`` if ``eps - g^T m >= 0``
    else ``-inf``. Satisfies the exact equivalence ``R_t(a) <= eps <=> H_t(a) >= beta``.
    """
    sup = supports.supports[action]
    comp = supports.complements[action]
    if len(comp) == 0:
        return math.inf

    # Fast exact evaluation at the conic dual witness p* for each z (and vertex max)
    # Note: for fixed z, max_{p in Delta(S(a))} (eps - g^T m) / s_g >= beta <=> min_p (g^T m + beta s_g) <= eps.
    # For general H_t(a), use quasiconcave Dinkelbach bisection on lambda:
    #   H_t(a) >= lambda  <==>  min_p [ g_{z,p}^T m + lambda * s_g ] <= eps for all z notin S(a).
    cert = certifier if certifier is not None else JointEllipsoidCertifier(supports, epsilon=epsilon)

    def feasible(lam: float) -> bool:
        if lam <= 0.0:
            # At lambda = 0: max_z min_y (m_z - m_y) <= eps
            return float(np.max(means[comp]) - np.max(means[sup])) <= epsilon + 1e-12
        ca = cert.certify_action_gp(
            action=action,
            means=means,
            sigma_mat=sigma_mat,
            beta=lam,
            stop_if_above_eps=True,
        )
        return ca.regret <= epsilon + 1e-12

    # First check sign at lambda = 0
    max_m_diff = float(np.max(means[comp]) - np.max(means[sup]))
    if max_m_diff > epsilon + 1e-12:
        # H_t(a) < 0: negative margin; evaluate worst z across single vertices + conic mixture at beta
        diag_all = np.maximum(0.0, np.diag(sigma_mat))
        sig_sc = sigma_mat[sup[:, None], comp[None, :]]
        s2_mat = np.maximum(0.0, diag_all[comp][None, :] + diag_all[sup][:, None] - 2.0 * sig_sc)
        d_mat = epsilon - (means[comp][None, :] - means[sup][:, None])
        h_mat = np.where(
            s2_mat > 1e-18,
            d_mat / np.sqrt(np.maximum(1e-18, s2_mat)),
            np.where(d_mat >= -1e-12, math.inf, -math.inf),
        )
        return float(np.min(np.max(h_mat, axis=0)))

    # Nonnegative H_t(a): bracket & bisect via exact Dinkelbach equivalence!
    lo = 0.0
    hi = max(1.0, float(beta))
    if feasible(hi):
        for _ in range(12):
            if not feasible(hi):
                break
            lo = hi
            hi *= 2.0
            if hi > 1e6:
                return math.inf
    for _ in range(36):
        mid = 0.5 * (lo + hi)
        if feasible(mid):
            lo = mid
        else:
            hi = mid
        if hi - lo <= 1e-6 * max(1.0, abs(lo)):
            break
    return float(lo)


def build_witness_pool(
    sup: np.ndarray,
    means: np.ndarray,
    u_ell: np.ndarray,
    conic_indices: np.ndarray | None,
    conic_weights: np.ndarray | None,
    *,
    top_mean: int = 4,
    top_ucb: int = 4,
) -> tuple[list[np.ndarray], list[np.ndarray]]:
    """Build deduplicated retained witness pool ``W_t(b_t)``.

    Contains:
      1. Current optimal conic mixture ``(conic_indices, conic_weights)`` (if provided).
      2. Top-``top_mean`` retained terminals in ``sup`` by posterior mean.
      3. Top-``top_ucb`` retained terminals in ``sup`` by optimistic UCB ``means + beta * stds``.

    Returns ``(idx_list, wgt_list)`` where each entry represents a sparse simplex vector
    supported on ``idx_list[w]`` with weights ``wgt_list[w]``.
    """
    idx_list: list[np.ndarray] = []
    wgt_list: list[np.ndarray] = []
    seen_singletons: set[int] = set()

    # 1. Current optimal conic mixture
    if conic_indices is not None and conic_weights is not None and len(conic_indices) > 0:
        nz = conic_weights > 1e-9
        if np.any(nz):
            ci = np.asarray(conic_indices[nz], dtype=np.int64)
            cw = np.asarray(conic_weights[nz], dtype=np.float64)
            cw = cw / float(np.sum(cw))
            if len(ci) == 1:
                seen_singletons.add(int(ci[0]))
            idx_list.append(ci)
            wgt_list.append(cw)

    # 2. Top-k retained terminals by posterior mean
    k_m = min(int(top_mean), len(sup))
    if k_m > 0:
        order_m = np.argsort(-means[sup], kind="mergesort")[:k_m]
        for pos in order_m:
            arm = int(sup[int(pos)])
            if arm not in seen_singletons:
                seen_singletons.add(arm)
                idx_list.append(np.array([arm], dtype=np.int64))
                wgt_list.append(np.ones(1, dtype=np.float64))

    # 3. Top-k retained terminals by optimistic upper bound
    k_u = min(int(top_ucb), len(sup))
    if k_u > 0:
        order_u = np.argsort(-u_ell[sup], kind="mergesort")[:k_u]
        for pos in order_u:
            arm = int(sup[int(pos)])
            if arm not in seen_singletons:
                seen_singletons.add(arm)
                idx_list.append(np.array([arm], dtype=np.int64))
                wgt_list.append(np.ones(1, dtype=np.float64))

    return idx_list, wgt_list


def _gp_os_arm(
    supports: SupportStructure,
    means: np.ndarray,
    stds: np.ndarray,
    costs: np.ndarray,
    beta: float,
) -> int:
    hi = means + beta * stds
    lo = means - beta * stds
    best_a = 0
    best_sep = -math.inf
    for a in range(supports.k):
        comp = supports.complements[a]
        u_in = float(np.max(hi[supports.supports[a]]))
        l_out = float(np.max(lo[comp])) if len(comp) else -math.inf
        sep = u_in - l_out
        if sep > best_sep:
            best_sep = sep
            best_a = a
    sup_b = supports.supports[best_a]
    comp_b = supports.complements[best_a]
    p_idx = int(sup_b[int(np.argmax(hi[sup_b]))])
    if len(comp_b) == 0:
        return p_idx
    q_idx = int(comp_b[int(np.argmax(hi[comp_b]))])
    sp = float(stds[p_idx]) / math.sqrt(float(costs[p_idx]))
    sq = float(stds[q_idx]) / math.sqrt(float(costs[q_idx]))
    return p_idx if sp >= sq else q_idx


def _gp_root_info_arm(
    supports: SupportStructure,
    leaf_to_actions: list[list[int]],
    u_ell: np.ndarray,
    stds: np.ndarray,
    costs: np.ndarray,
) -> int:
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
    sw = float(stds[w_star]) / math.sqrt(float(costs[w_star]))
    sz = float(stds[z_box]) / math.sqrt(float(costs[z_box]))
    return w_star if sw >= sz else z_box


def build_query_shortlist(
    *,
    m: int,
    sup: np.ndarray,
    cd_scores: np.ndarray,
    means: np.ndarray,
    sigma_mat: np.ndarray,
    obs_var: float,
    costs: np.ndarray,
    supports: SupportStructure,
    leaf_to_actions: list[list[int]],
    stds: np.ndarray,
    u_ell: np.ndarray,
    beta: float,
    shortlist_threshold: int = 100,
    top_cd: int = 8,
    top_inside_kg: int = 8,
    use_cpp: bool = True,
) -> np.ndarray:
    """Return candidate query indices to evaluate in MA-CD-Joint lookahead.

    When ``m <= shortlist_threshold`` (Synthetic M=64, WorFBench M<=81), evaluates ALL
    ``M`` candidate queries. When ``m > shortlist_threshold`` (GB1/TmTrpB M~350--500),
    shortlists:
      - top-8 queries by original CD-Joint score ``dv / c_x``,
      - top-8 queries by inside-support correlated KG score over ``S(b_t)``,
      - the GP-OS recommended query,
      - the GP-Root-Info recommended query,
    deduplicated in canonical order.
    """
    if m <= shortlist_threshold:
        return np.arange(m, dtype=np.int64)

    picked: list[int] = []
    seen: set[int] = set()

    def _add(arm: int) -> None:
        if arm not in seen:
            seen.add(arm)
            picked.append(arm)

    # 1. Top-k original CD-Joint queries
    k_cd = min(int(top_cd), m)
    top_cd_idx = np.argsort(-cd_scores, kind="mergesort")[:k_cd]
    for a in top_cd_idx:
        _add(int(a))

    # 2. Top-k inside-support correlated Knowledge Gradient queries over S(b_t)
    if len(sup) > 0 and top_inside_kg > 0:
        sig_ss = sigma_mat[np.ix_(sup, sup)]
        kg_in = correlated_kg_log_scores(
            means[sup], sig_ss, obs_var, costs[sup], use_cpp=use_cpp
        )
        k_kg = min(int(top_inside_kg), len(sup))
        for pos in np.argsort(-kg_in, kind="mergesort")[:k_kg]:
            _add(int(sup[int(pos)]))

    # 3. GP-OS and GP-Root-Info recommended queries
    _add(_gp_os_arm(supports, means, stds, costs, beta))
    _add(_gp_root_info_arm(supports, leaf_to_actions, u_ell, stds, costs))

    return np.array(picked, dtype=np.int64)


def _eval_pool_standardized_margin(
    comp: np.ndarray,
    idx_list: list[np.ndarray],
    wgt_list: list[np.ndarray],
    means: np.ndarray,
    sigma_mat: np.ndarray,
    diag_sig: np.ndarray,
    epsilon: float,
    beta: float,
) -> tuple[float, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Precompute ``(cur_h_root, d_zw, s2_zw, m_W, sig_CW_full_W)`` for the witness pool.

    ``sig_W_all`` has shape ``(W, M)`` where row ``w`` is ``p_w^T Sigma_t``.
    """
    n_c = len(comp)
    n_w = len(idx_list)
    m_w = np.empty(n_w, dtype=np.float64)
    sig_w_all = np.empty((n_w, sigma_mat.shape[1]), dtype=np.float64)
    var_w = np.empty(n_w, dtype=np.float64)

    for w, (wi, ww) in enumerate(zip(idx_list, wgt_list)):
        if len(wi) == 1:
            j = int(wi[0])
            m_w[w] = float(means[j])
            row = sigma_mat[j]
            sig_w_all[w] = row
            var_w[w] = float(diag_sig[j])
        else:
            m_w[w] = float(ww @ means[wi])
            row = ww @ sigma_mat[wi]
            sig_w_all[w] = row
            var_w[w] = max(0.0, float(row[wi] @ ww))

    m_c = means[comp]
    sig_cw = sig_w_all[:, comp].T  # (n_c, W)
    d_zw = epsilon - (m_c[:, None] - m_w[None, :])  # (n_c, W)
    s2_zw = np.maximum(0.0, diag_sig[comp][:, None] + var_w[None, :] - 2.0 * sig_cw)  # (n_c, W)

    # Zero-variance handling: +beta (saturated to Psi=1) if d >= 0, else large negative
    zero_mask = s2_zw <= 1e-18
    safe_s = np.sqrt(np.where(zero_mask, 1.0, s2_zw))
    h_zw = np.where(zero_mask, np.where(d_zw >= -1e-12, beta, -1e6 * beta), d_zw / safe_s)
    cur_h_root = float(np.min(np.max(h_zw, axis=1))) if n_c > 0 else math.inf
    return cur_h_root, d_zw, s2_zw, sig_w_all, m_w


def select_margin_aware_query(
    *,
    supports: SupportStructure,
    leaf_to_actions: list[list[int]],
    posterior: SharedGaussianPosterior,
    certifier: JointEllipsoidCertifier,
    beta: float,
    epsilon: float,
    step_idx: int,
    safe: bool = False,
    top_mean: int = 4,
    top_ucb: int = 4,
    shortlist_threshold: int = 100,
    top_cd: int = 8,
    top_inside_kg: int = 8,
    cd_stop_if_above_eps: bool = False,
    cached_root_cert: tuple[int, ActionCertificate] | None = None,
    root_selection_mode: str = "mean_tiebreak",
    use_cpp: bool = True,
) -> MarginAwareSelection:
    """Execute one step of MA-CD-Joint (``safe=False``) or MA-CD-Joint-Safe (``safe=True``).

    Preserves:
      1. Exact original CD-Joint candidate-root & conic witness computation.
      2. Exact original ``eps/2`` safeguard overriding lookahead whenever triggered.
      3. For ``safe=True``: mandatory original CD-Joint queries on every even step
         (``step_idx % 2 == 0``), ensuring the finite-sample termination bound up to 2x.
      4. Vectorized 9-point Gauss-Hermite rank-1 fantasy lookahead maximizing expected
         saturated standardized certification margin ``Psi(H_{t+1}^{(x,xi)}(b_t))``.
      5. Fallback to ``x_cd`` whenever the approximate lookahead predicts no positive gain.
    """
    means = posterior.mean
    sig = posterior.sigma_mat
    diag_sig = np.maximum(1e-18, np.diag(sig))
    stds = np.sqrt(diag_sig)
    costs = supports.costs
    m = supports.m
    obs_var = posterior.obs_var

    u_ell = means + beta * stds
    y_opt = int(np.argmax(u_ell))
    containers = leaf_to_actions[y_opt]

    # Candidate root b_t: match existing MatchedModelBEDSession or select_gp_arm_with_beta exactly
    if cached_root_cert is not None and cached_root_cert[0] in containers:
        b_t, c_b = cached_root_cert
    else:
        if root_selection_mode == "ucb_lcb_sep":
            l_ell = means - beta * stds
            best_sep = -math.inf
            b_t = containers[0]
            for a in containers:
                comp_a = supports.complements[a]
                l_out = float(np.max(l_ell[comp_a])) if len(comp_a) else -math.inf
                sep = float(u_ell[y_opt]) - l_out
                if sep > best_sep:
                    best_sep = sep
                    b_t = a
        else:
            b_t = max(containers, key=lambda b: (float(np.max(means[supports.supports[b]])), -b))

        prev_eps = certifier.epsilon
        certifier.epsilon = float(epsilon)
        try:
            c_b = certifier.certify_action_gp(
                action=int(b_t),
                means=means,
                sigma_mat=sig,
                beta=beta,
                stop_if_above_eps=cd_stop_if_above_eps,
            )
        finally:
            certifier.epsilon = prev_eps

    sup = supports.supports[b_t]
    comp = supports.complements[b_t]
    z_t = int(c_b.challenger_idx)

    if z_t < 0 or len(comp) == 0:
        return MarginAwareSelection(
            arm=y_opt,
            candidate_root=int(b_t),
            challenger_idx=-1,
            cd_arm=y_opt,
            safeguard_triggered=False,
            mandatory_cd_step=False,
            used_ma_query=False,
            ma_gain=0.0,
            inside_support=bool(np.any(sup == y_opt)),
            mixture_support=1,
            active_contrast_var=0.0,
            retained_witness_margin=math.inf,
            active_contrast_margin=math.inf,
            std_cert_margin=math.inf,
        )

    # Original CD-Joint contrast & eps/2 safeguard
    g_dual = c_b.contrast
    mean_contrast = float(g_dual @ means)
    mix_supp = int(np.sum(c_b.inside_weights > 1e-6))
    sg_triggered = bool(mean_contrast > 0.5 * epsilon)

    if not sg_triggered:
        g_cd = g_dual
    else:
        g_cd = np.zeros(m, dtype=np.float64)
        g_cd[z_t] = 1.0
        g_cd[y_opt] = -1.0

    sg_cd = sig @ g_cd
    active_var = max(0.0, float(g_cd @ sg_cd))
    dv = (sg_cd * sg_cd) / (obs_var + diag_sig)
    cd_scores = dv / costs
    x_cd = int(np.argmax(cd_scores))

    # Mechanistic margins for telemetry
    ret_margin = float(np.max(means[sup]) - np.max(means[comp]))
    act_margin = float(epsilon - float(g_cd @ means))
    cur_h_dual = (
        (epsilon - mean_contrast) / math.sqrt(max(1e-18, float(g_dual @ (sig @ g_dual))))
        if float(g_dual @ (sig @ g_dual)) > 1e-18
        else (beta if epsilon >= mean_contrast else -1e6 * beta)
    )

    # 1. Safeguard override (preserved identically for both MA-CD-Joint and MA-CD-Joint-Safe)
    if sg_triggered:
        return MarginAwareSelection(
            arm=x_cd,
            candidate_root=int(b_t),
            challenger_idx=z_t,
            cd_arm=x_cd,
            safeguard_triggered=True,
            mandatory_cd_step=False,
            used_ma_query=False,
            ma_gain=0.0,
            inside_support=bool(np.any(sup == x_cd)),
            mixture_support=mix_supp,
            active_contrast_var=active_var,
            retained_witness_margin=ret_margin,
            active_contrast_margin=act_margin,
            std_cert_margin=float(cur_h_dual),
        )

    # 2. Mandatory CD-Joint steps for MA-CD-Joint-Safe (even steps: 0, 2, 4, ...)
    if safe and (int(step_idx) % 2 == 0):
        return MarginAwareSelection(
            arm=x_cd,
            candidate_root=int(b_t),
            challenger_idx=z_t,
            cd_arm=x_cd,
            safeguard_triggered=False,
            mandatory_cd_step=True,
            used_ma_query=False,
            ma_gain=0.0,
            inside_support=bool(np.any(sup == x_cd)),
            mixture_support=mix_supp,
            active_contrast_var=active_var,
            retained_witness_margin=ret_margin,
            active_contrast_margin=act_margin,
            std_cert_margin=float(cur_h_dual),
        )

    # 3. Build deduplicated retained witness pool & candidate query shortlist
    idx_list, wgt_list = build_witness_pool(
        sup=sup,
        means=means,
        u_ell=u_ell,
        conic_indices=c_b.inside_indices,
        conic_weights=c_b.inside_weights,
        top_mean=top_mean,
        top_ucb=top_ucb,
    )
    queries = build_query_shortlist(
        m=m,
        sup=sup,
        cd_scores=cd_scores,
        means=means,
        sigma_mat=sig,
        obs_var=obs_var,
        costs=costs,
        supports=supports,
        leaf_to_actions=leaf_to_actions,
        stds=stds,
        u_ell=u_ell,
        beta=beta,
        shortlist_threshold=shortlist_threshold,
        top_cd=top_cd,
        top_inside_kg=top_inside_kg,
        use_cpp=use_cpp,
    )

    # 4. Precompute d_g, s_g^2, and rank-1 fantasy update vectors v_x for all queries in shortlist
    cur_h_root, d_zw, s2_zw, sig_w_all, _ = _eval_pool_standardized_margin(
        comp=comp,
        idx_list=idx_list,
        wgt_list=wgt_list,
        means=means,
        sigma_mat=sig,
        diag_sig=diag_sig,
        epsilon=epsilon,
        beta=beta,
    )
    cur_psi = min(1.0, cur_h_root / beta)

    inv_denom_x = 1.0 / np.sqrt(obs_var + diag_sig[queries])  # (Q,)
    # v_x[z] = Sigma[z, x] / sqrt(obs_var + Sigma[x, x])
    v_c = sig[np.ix_(comp, queries)] * inv_denom_x[None, :]  # (n_c, Q)
    v_w = sig_w_all[:, queries] * inv_denom_x[None, :]  # (W, Q)

    # 5. Exact 9-point standard-normal Gauss-Hermite integration with witness reselection
    #    and dynamic bottleneck switching across all excluded challengers z in comp.
    expected_psi = _ma_quadrature_expected_psi(
        d_zw=d_zw, s2_zw=s2_zw, v_c=v_c, v_w=v_w, beta=beta, use_cpp=use_cpp
    )

    gains = (expected_psi - cur_psi) / costs[queries]
    best_pos = int(np.argmax(gains))
    best_gain = float(gains[best_pos])

    if best_gain > 1e-14:
        chosen = int(queries[best_pos])
        used_ma = True
    else:
        chosen = x_cd
        used_ma = False

    return MarginAwareSelection(
        arm=chosen,
        candidate_root=int(b_t),
        challenger_idx=z_t,
        cd_arm=x_cd,
        safeguard_triggered=False,
        mandatory_cd_step=False,
        used_ma_query=used_ma,
        ma_gain=best_gain,
        inside_support=bool(np.any(sup == chosen)),
        mixture_support=mix_supp,
        active_contrast_var=active_var,
        retained_witness_margin=ret_margin,
        active_contrast_margin=act_margin,
        std_cert_margin=float(cur_h_root),
    )


def compute_mechanistic_snapshot(
    *,
    supports: SupportStructure,
    leaf_to_actions: list[list[int]],
    posterior: SharedGaussianPosterior,
    certifier: JointEllipsoidCertifier,
    true_leaf_means: np.ndarray,
    beta: float,
    epsilon: float,
) -> dict[str, float]:
    """Compute standardized mechanistic diagnostics at an evaluation checkpoint ``t``."""
    means = posterior.mean
    sig = posterior.sigma_mat
    diag_sig = np.maximum(1e-18, np.diag(sig))
    stds = np.sqrt(diag_sig)
    u_ell = means + beta * stds

    y_opt = int(np.argmax(u_ell))
    containers = leaf_to_actions[y_opt]
    b_t = max(containers, key=lambda b: (float(np.max(means[supports.supports[b]])), -b))
    sup = supports.supports[b_t]
    comp = supports.complements[b_t]

    # 1. Best evaluated retained true fitness
    eval_mask = posterior.arm_counts[sup] > 0
    if np.any(eval_mask):
        best_eval_fit = float(np.max(true_leaf_means[sup[eval_mask]]))
    else:
        best_eval_fit = float("nan")

    # 2. Posterior retained witness margin: max_{y in S(b_t)} m_y - max_{z notin S(b_t)} m_z
    ret_margin = (
        float(np.max(means[sup]) - np.max(means[comp]))
        if len(comp) > 0
        else float("inf")
    )

    # 3. Active contrast variance & standardized certification margin over witness pool
    prev_eps = certifier.epsilon
    certifier.epsilon = float(epsilon)
    try:
        c_b = certifier.certify_action_gp(
            action=int(b_t),
            means=means,
            sigma_mat=sig,
            beta=beta,
            stop_if_above_eps=False,
        )
    finally:
        certifier.epsilon = prev_eps

    if c_b.challenger_idx < 0 or len(comp) == 0:
        act_var = 0.0
        std_margin = float(beta)
    else:
        g_dual = c_b.contrast
        act_var = max(0.0, float(g_dual @ (sig @ g_dual)))
        idx_list, wgt_list = build_witness_pool(
            sup=sup,
            means=means,
            u_ell=u_ell,
            conic_indices=c_b.inside_indices,
            conic_weights=c_b.inside_weights,
            top_mean=4,
            top_ucb=4,
        )
        std_margin, _, _, _, _ = _eval_pool_standardized_margin(
            comp=comp,
            idx_list=idx_list,
            wgt_list=wgt_list,
            means=means,
            sigma_mat=sig,
            diag_sig=diag_sig,
            epsilon=epsilon,
            beta=beta,
        )

    return {
        "best_eval_retained_fitness": best_eval_fit,
        "retained_witness_margin": ret_margin,
        "active_contrast_var": act_var,
        "std_cert_margin": std_margin,
        "std_cert_progress": min(1.0, std_margin / max(1e-12, beta)),
    }


__all__ = [
    "GAUSS_HERMITE_9_NODES",
    "GAUSS_HERMITE_9_WEIGHTS",
    "MarginAwareSelection",
    "build_query_shortlist",
    "build_witness_pool",
    "compute_exact_standardized_margin",
    "compute_mechanistic_snapshot",
    "select_margin_aware_query",
]
