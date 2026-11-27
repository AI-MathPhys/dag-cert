"""v12 Decision-Aware Bayesian Experimental Design vs. Bayesian Optimization on Search DAGs.

Implements a strictly controlled, shared-posterior experimental-design harness comparing
seven acquisition policies under identical Bayesian beliefs, identical paired intrinsic
Gaussian observation tapes, identical numerical tolerances, and an identical root-action
certification stopping rule:

  1. `gp_ucb`        : Standard GP-UCB (optimistic terminal value)
  2. `gp_ts`         : GP Thompson Sampling (joint posterior draw maximizer)
  3. `gp_ei`         : Noisy GP Expected Improvement (underflow-free log-EI / c_x)
  4. `kg`            : Exact Analytical Correlated Knowledge Gradient (Frazier-Powell-Dayanik 2009,
                       exact O(M log M) convex upper envelope in underflow-free log-space / c_x)
  5. `gp_os`         : Correlated GP-OS (Optimistic Separation on shared posterior intervals)
  6. `cd_joint`      : Safeguarded Contrast-Directed Joint Acquisition (variance reduction of
                       safeguarded conic dual contrast per unit cost)
  7. `bayesian_voi`  : Bayesian Root-Risk Value of Information targeting
                       alpha_t^VOI(x) = (rho_t - E_{Y_x|D_t}[rho_{t+1}]) / c_x,
                       using stratified normal quantiles + Common Random Numbers (CRN) and an
                       exact analytical Gaussian log-tail continuation once MC risk reaches 0.

Also provides:
  - `SharedGaussianPosterior`: exact conjugate GP / fixed-feature linear Gaussian posterior with
    Sherman-Morrison BLAS rank-1 updates, periodic Cholesky re-stabilization, exact information
    gain `gamma_t`, exact posterior credible ellipsoid radius `sqrt(chi2_{r, 1-delta})`, and
    exact anytime-valid self-normalized frequentist ellipsoid radius `B + sqrt(2(gamma_t + log(1/delta)))`.
  - `GaussianPairedProblemWrapper` & `SmallOverlapCorrelationProblem` (M=16, K=4) extending
    `DeconfoundedOverlapCorrelationProblem` (M=64, K=8) with exact paired Gaussian observation tapes.
  - `FixedFeatureGaussianOverlapProblem` (M=64, K=8, d=8): exact fixed-feature Gaussian setting
    for confirmatory anytime-valid frequentist stopping analysis.
"""
from __future__ import annotations

import ctypes
import hashlib
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Sequence

import numpy as np
from scipy.linalg import blas, cho_factor, cho_solve
from scipy.special import erfcx, log_ndtr
from scipy.stats import beta as beta_dist
from scipy.stats import chi2

from .graph import DAG, Problem
from .v3_extensions import splitmix_uniform01
from .v6_bayesian_opt import ar1_corr_matrix, solve_ellipsoid_challenger
from .v7_bayesian_ucd import (
    ActionCertificate,
    JointEllipsoidCertifier,
    SupportStructure,
)
from .v7_benchmarks import _GaussianOracle
from .v8_unified_experiments import DeconfoundedOverlapCorrelationProblem


_LOG_SQRT_2PI = 0.5 * math.log(2.0 * math.pi)
_INV_SQRT2 = 1.0 / math.sqrt(2.0)
_SQRT_PI_OVER_2 = math.sqrt(0.5 * math.pi)
_CPP_KG_SOURCE = Path(__file__).resolve().parents[1] / "_native" / "_cpp_v12_kg.cpp"


class _CppV12KGRunner:
    """Optional on-demand `-O3 -std=c++17` accelerator for Exact Analytical Correlated KG."""

    _lib = None
    _checked = False

    @classmethod
    def get_lib(cls):
        if cls._checked:
            return cls._lib
        cls._checked = True
        if not _CPP_KG_SOURCE.is_file():
            return None
        cxx = os.environ.get("CXX") or shutil.which("g++") or shutil.which("clang++")
        if not cxx:
            return None
        try:
            sha = hashlib.sha256(b"-ffp-contract=off" + _CPP_KG_SOURCE.read_bytes()).hexdigest()[:16]
            ext = ".dylib" if sys.platform == "darwin" else ".so"
            so_path = Path(tempfile.gettempdir()) / f"dag_mcts_v12_kg_{sha}{ext}"
            if not so_path.is_file():
                tmp_so = so_path.with_name(f"{so_path.stem}_{os.getpid()}.tmp{ext}")
                try:
                    subprocess.run(
                        [
                            cxx, "-O3", "-ffp-contract=off", "-march=native", "-std=c++17", "-Wall", "-Wextra", "-Werror",
                            "-shared", "-fPIC", str(_CPP_KG_SOURCE), "-o", str(tmp_so),
                        ],
                        check=True,
                        stderr=subprocess.DEVNULL,
                    )
                except subprocess.CalledProcessError:
                    subprocess.run(
                        [
                            cxx, "-O3", "-ffp-contract=off", "-std=c++17", "-Wall", "-Wextra", "-Werror",
                            "-shared", "-fPIC", str(_CPP_KG_SOURCE), "-o", str(tmp_so),
                        ],
                        check=True,
                    )
                tmp_so.replace(so_path)
            lib = ctypes.CDLL(str(so_path))
            dbl_p = ctypes.POINTER(ctypes.c_double)
            int_p = ctypes.POINTER(ctypes.c_int)
            lib.cpp_correlated_kg_log_scores.argtypes = [
                ctypes.c_int, dbl_p, dbl_p, ctypes.c_double, dbl_p, dbl_p
            ]
            lib.cpp_correlated_kg_log_scores.restype = None
            lib.cpp_voi_eval_candidate.argtypes = [
                ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                dbl_p, dbl_p, dbl_p, dbl_p, int_p, int_p, ctypes.c_double,
            ]
            lib.cpp_voi_eval_candidate.restype = ctypes.c_double
            cls._lib = lib
        except Exception:
            cls._lib = None
        return cls._lib


# ---------------------------------------------------------------------------
# 1. Underflow-Free Analytical Primitives: log_h(z), Noisy GP-EI, Exact Correlated KG
# ---------------------------------------------------------------------------
def log_expected_pos_normal(z: np.ndarray | float) -> np.ndarray:
    """Compute `log(z * Phi(z) + phi(z)) = log E[(Z + z)_+]` accurately for all `z in (-inf, +inf)`.

    Never underflows even for `z = -100` (where naive `z*Phi(z) + phi(z)` evaluates to `0.0`).
    """
    z_arr = np.asarray(z, dtype=np.float64)
    out = np.empty_like(z_arr, dtype=np.float64)

    # Case 1: z >= 10 -> z * Phi(z) + phi(z) == z + O(exp(-50))
    m_hi = z_arr >= 10.0
    if np.any(m_hi):
        zh = z_arr[m_hi]
        out[m_hi] = np.log(zh) + np.log1p(np.exp(-0.5 * zh * zh - _LOG_SQRT_2PI) / zh)

    # Case 2: -6.0 <= z < 10.0 -> direct evaluation via erfcx is exact to ~15 digits
    m_mid = (~m_hi) & (z_arr >= -6.0)
    if np.any(m_mid):
        zm = z_arr[m_mid]
        # Phi(z) = 0.5 * erfc(-z / sqrt(2)) = 0.5 * exp(-z^2/2) * erfcx(-z / sqrt(2)) for z <= 0
        # For z > 0, use Phi(z) = 1 - 0.5 * exp(-z^2/2) * erfcx(z / sqrt(2))
        pos = zm > 0.0
        val = np.empty_like(zm)
        if np.any(pos):
            zp = zm[pos]
            phi_p = np.exp(-0.5 * zp * zp - _LOG_SQRT_2PI)
            cdf_p = 1.0 - 0.5 * np.exp(-0.5 * zp * zp) * erfcx(zp * _INV_SQRT2)
            val[pos] = np.maximum(1e-300, zp * cdf_p + phi_p)
        neg = ~pos
        if np.any(neg):
            zn = zm[neg]
            # factor out phi(z) = exp(-z^2/2) / sqrt(2pi)
            # z*Phi(z) + phi(z) = phi(z) * (1 + z * sqrt(pi/2) * erfcx(-z / sqrt(2)))
            bracket = np.maximum(1e-300, 1.0 + zn * _SQRT_PI_OVER_2 * erfcx(-zn * _INV_SQRT2))
            val[neg] = np.exp(-0.5 * zn * zn - _LOG_SQRT_2PI) * bracket
        out[m_mid] = np.log(val)

    # Case 3: z < -6.0 -> asymptotic expansion of 1 + z * sqrt(pi/2) * erfcx(-z/sqrt(2))
    # Mills ratio: Phi(z) / phi(z) = -1/z + 1/z^3 - 3/z^5 + 15/z^7 - 105/z^9 + 945/z^11 - ...
    # Hence 1 + z * Phi(z)/phi(z) = 1/z^2 - 3/z^4 + 15/z^6 - 105/z^8 + 945/z^10 - ...
    m_lo = z_arr < -6.0
    if np.any(m_lo):
        zl = z_arr[m_lo]
        inv_z2 = 1.0 / (zl * zl)
        # Asymptotic series is accurate to < 1e-11 for |z| >= 6 (exact for |z| >= 10)
        # For -15 <= z < -6 use exact erfcx bracket with float64 safety; for z < -15 use asymptotic series
        m_mid_lo = zl >= -15.0
        log_b = np.empty_like(zl)
        if np.any(m_mid_lo):
            zml = zl[m_mid_lo]
            br = 1.0 + zml * _SQRT_PI_OVER_2 * erfcx(-zml * _INV_SQRT2)
            # Fallback to series if cancellation makes br tiny
            inv2 = 1.0 / (zml * zml)
            ser = inv2 * (1.0 - 3.0 * inv2 * (1.0 - 5.0 * inv2 * (1.0 - 7.0 * inv2)))
            br = np.where(br > 1e-12, br, ser)
            log_b[m_mid_lo] = np.log(np.maximum(1e-300, br))
        m_far = ~m_mid_lo
        if np.any(m_far):
            inv2 = inv_z2[m_far]
            ser = inv2 * (1.0 - 3.0 * inv2 * (1.0 - 5.0 * inv2 * (1.0 - 7.0 * inv2 * (1.0 - 9.0 * inv2))))
            log_b[m_far] = np.log(np.maximum(1e-300, ser))
        out[m_lo] = -0.5 * zl * zl - _LOG_SQRT_2PI + log_b

    return out


def _logsumexp_1d(vals: np.ndarray) -> float:
    if len(vals) == 0:
        return -math.inf
    m = float(np.max(vals))
    if not math.isfinite(m):
        return m
    return m + math.log(float(np.sum(np.exp(vals - m))))


def noisy_gp_ei_log_scores(
    means: np.ndarray,
    stds: np.ndarray,
    costs: np.ndarray,
) -> np.ndarray:
    """Underflow-free `log(EI_t(x) / c_x)` for noisy GP-EI over current best posterior mean."""
    m_star = float(np.max(means))
    m = len(means)
    out = np.full(m, -math.inf, dtype=np.float64)
    pos = stds > 1e-15
    if np.any(pos):
        s_p = stds[pos]
        z_p = (means[pos] - m_star) / s_p
        out[pos] = np.log(s_p) + log_expected_pos_normal(z_p) - np.log(costs[pos])
    return out


def exact_correlated_kg_single(a: np.ndarray, b: np.ndarray) -> tuple[float, float]:
    """Exact Frazier-Powell-Dayanik (2009) analytical Correlated Knowledge Gradient for one candidate.

    Computes both `(kg_value, log_kg_value)` for:
        KG(a, b) = E_Z[ max_i (a_i + b_i Z) ] - max_i a_i,   Z ~ N(0, 1).

    Uses exact O(M log M) convex upper envelope and underflow-free `log_expected_pos_normal`,
    so `log_kg_value` remains exact even when `kg_value` underflows float64 (< 1e-300).
    """
    n = len(a)
    if n <= 1:
        return 0.0, -math.inf

    # Sort by increasing slope b, breaking ties by DECREASING intercept a so the highest
    # line at each slope comes first.
    order = np.lexsort((-a, b))
    b_s = b[order]
    a_s = a[order]

    # Deduplicate near-identical slopes (keep strictly highest intercept)
    if float(b_s[-1] - b_s[0]) <= 1e-15:
        return 0.0, -math.inf

    hull_a: list[float] = []
    hull_b: list[float] = []
    # breakpoints[k] is intersection of hull line k-1 and hull line k
    hull_c: list[float] = []

    for i in range(n):
        bi = float(b_s[i])
        ai = float(a_s[i])
        if hull_b and abs(bi - hull_b[-1]) <= 1e-15:
            # Same slope; since sorted by descending a, earlier line dominates or equals
            continue
        while len(hull_b) >= 1:
            # Intersection with last line on hull:
            # a_last + b_last * c = ai + bi * c  =>  c = (a_last - ai) / (bi - b_last)
            c_new = (hull_a[-1] - ai) / (bi - hull_b[-1])
            if len(hull_c) >= 1 and c_new <= hull_c[-1] + 1e-15:
                hull_a.pop()
                hull_b.pop()
                hull_c.pop()
            else:
                hull_c.append(c_new)
                break
        hull_a.append(ai)
        hull_b.append(bi)

    L = len(hull_a)
    if L <= 1:
        return 0.0, -math.inf

    db = np.diff(np.asarray(hull_b, dtype=np.float64))  # strictly > 0
    neg_abs_c = -np.abs(np.asarray(hull_c, dtype=np.float64))
    log_terms = np.log(db) + log_expected_pos_normal(neg_abs_c)
    log_kg = _logsumexp_1d(log_terms)
    kg_val = math.exp(log_kg) if log_kg > -700.0 else 0.0
    return kg_val, log_kg


def correlated_kg_log_scores(
    means: np.ndarray,
    sigma_mat: np.ndarray,
    obs_var: float,
    costs: np.ndarray,
    use_cpp: bool = True,
) -> np.ndarray:
    """Compute exact underflow-free `log(KG_t(x) / c_x)` for all candidate queries `x = 0..M-1`."""
    m = len(means)
    if use_cpp:
        lib = _CppV12KGRunner.get_lib()
        if lib is not None:
            m_arr = np.ascontiguousarray(means, dtype=np.float64)
            # Symmetric matrix has identical rows & columns in both C and Fortran order
            s_arr = (
                sigma_mat
                if (sigma_mat.dtype == np.float64 and (sigma_mat.flags["C_CONTIGUOUS"] or sigma_mat.flags["F_CONTIGUOUS"]))
                else np.ascontiguousarray(sigma_mat, dtype=np.float64)
            )
            c_arr = np.ascontiguousarray(costs, dtype=np.float64)
            out = np.empty(m, dtype=np.float64)
            dbl_p = ctypes.POINTER(ctypes.c_double)
            lib.cpp_correlated_kg_log_scores(
                int(m),
                m_arr.ctypes.data_as(dbl_p),
                s_arr.ctypes.data_as(dbl_p),
                float(obs_var),
                c_arr.ctypes.data_as(dbl_p),
                out.ctypes.data_as(dbl_p),
            )
            return out

    diag_v = np.maximum(0.0, np.diag(sigma_mat))
    inv_sqrt_denom = 1.0 / np.sqrt(np.maximum(1e-18, diag_v + obs_var))
    # sigma_tilde[:, x] = Sigma[:, x] / sqrt(Sigma[x, x] + sigma^2)
    sigma_tilde = sigma_mat * inv_sqrt_denom[None, :]
    log_c = np.log(costs)

    scores = np.full(m, -math.inf, dtype=np.float64)
    for x in range(m):
        _, lkg = exact_correlated_kg_single(means, sigma_tilde[:, x])
        scores[x] = lkg - float(log_c[x])
    return scores


# ---------------------------------------------------------------------------
# 2. Bayesian Root-Risk Estimation & Value of Information (Eq. 8 of main.tex)
# ---------------------------------------------------------------------------
def estimate_posterior_root_risks(
    means: np.ndarray,
    chol_sigma: np.ndarray,
    supports: tuple[np.ndarray, ...],
    epsilon: float,
    std_normals: np.ndarray,
) -> np.ndarray:
    """Estimate `q_t(a) = Pr(mu_* - V(a) > eps | D_t)` for all root actions using draws `U (M, N_mu)`."""
    # samples: (M, N_mu)
    samples = means[:, None] + (chol_sigma @ std_normals)
    mu_star = np.max(samples, axis=0)
    k = len(supports)
    risks = np.empty(k, dtype=np.float64)
    for a in range(k):
        v_a = np.max(samples[supports[a]], axis=0)
        risks[a] = float(np.mean((mu_star - v_a) > epsilon))
    return risks


def _safe_cholesky(mat: np.ndarray) -> np.ndarray:
    """Numerically stable lower-triangular Cholesky / PSD square-root factor."""
    try:
        return np.linalg.cholesky(mat)
    except np.linalg.LinAlgError:
        pass
    sym = 0.5 * (mat + mat.T)
    m = sym.shape[0]
    scale = max(1e-12, float(np.max(np.abs(np.diag(sym)))))
    for jit in (1e-13, 1e-11, 1e-9, 1e-7):
        try:
            return np.linalg.cholesky(sym + (jit * scale) * np.eye(m, dtype=np.float64))
        except np.linalg.LinAlgError:
            continue
    # Eigenvalue fallback for rank-deficient covariances (e.g. d=3 features in M=5 proxy DAG!)
    evals, evecs = np.linalg.eigh(sym)
    evals = np.maximum(0.0, evals)
    return evecs * np.sqrt(evals)[None, :]


def _analytical_log_tail_root_risk(
    means: np.ndarray,
    sigma_mat: np.ndarray,
    supports: tuple[np.ndarray, ...],
    complements: tuple[np.ndarray, ...],
    epsilon: float,
) -> float:
    """Smooth exact-Gaussian tail upper-proxy on `log min_a q(a)` for rare-event VOI continuation.

    For each action `a`, pairs each outside terminal `z notin S(a)` against the best inside
    terminal `y_a = argmax_{y in S(a)} m_y` and computes the exact Gaussian log-exceedance
    `log Phi((m_z - m_{y_a} - eps) / sigma_{z - y_a})`, then takes the log-sum-exp union bound
    over `z notin S(a)` and the minimum over actions `a`. Never underflows even at `1e-300`.
    """
    diag_v = np.maximum(0.0, np.diag(sigma_mat))
    best_log_q = math.inf
    for a, sup in enumerate(supports):
        comp = complements[a]
        if len(comp) == 0:
            return -1e6
        y_a = int(sup[int(np.argmax(means[sup]))])
        var_diff = np.maximum(1e-18, diag_v[comp] + diag_v[y_a] - 2.0 * sigma_mat[comp, y_a])
        z_scores = (means[comp] - float(means[y_a]) - epsilon) / np.sqrt(var_diff)
        log_probs = log_ndtr(z_scores)
        log_q_a = _logsumexp_1d(log_probs)
        if log_q_a < best_log_q:
            best_log_q = log_q_a
    return float(best_log_q)


def select_bayesian_root_voi(
    means: np.ndarray,
    sigma_mat: np.ndarray,
    obs_var: float,
    costs: np.ndarray,
    supports: tuple[np.ndarray, ...],
    complements: tuple[np.ndarray, ...],
    epsilon: float,
    y_quantiles: np.ndarray,
    std_normals: np.ndarray,
    use_cpp: bool = True,
) -> tuple[int, np.ndarray, float, bool]:
    """Select next experiment maximizing Bayesian Root-Risk VOI per unit cost (Eq. 8).

        alpha_t^VOI(x) = (rho_t - E_{Y_x | D_t}[rho_{t+1}]) / c_x

    Uses stratified normal quantiles `y_quantiles` (length N_y) for the predictive observation
    and Common Random Numbers `std_normals` (shape M x N_mu) across all candidates `x`.
    Returns `(chosen_arm, scores, current_best_risk, used_tail_continuation)`.

    When direct MC risk hits 0 (true posterior risk << 1/N_mu while waiting for a conservative
    chi-square ellipsoid to certify), smoothly continues using exact analytical Gaussian
    log-tail root-risk VOI so the policy never degenerates to arbitrary index-0 tie-breaking.
    """
    m = len(means)
    k = len(supports)
    n_y = len(y_quantiles)
    n_mu = int(std_normals.shape[1])

    chol_cur = _safe_cholesky(sigma_mat)
    cur_risks = estimate_posterior_root_risks(means, chol_cur, supports, epsilon, std_normals)
    cur_best_risk = float(np.min(cur_risks))

    diag_v = np.maximum(0.0, np.diag(sigma_mat))
    inv_sqrt_denom = 1.0 / np.sqrt(np.maximum(1e-18, diag_v + obs_var))
    sigma_tilde = sigma_mat * inv_sqrt_denom[None, :]  # (M, M)

    lib = _CppV12KGRunner.get_lib() if use_cpp else None

    scores = np.full(m, -math.inf, dtype=np.float64)
    if cur_best_risk > 0.0:
        if lib is not None:
            m_arr = np.ascontiguousarray(means, dtype=np.float64)
            yq_arr = np.ascontiguousarray(y_quantiles, dtype=np.float64)
            offsets = np.zeros(k + 1, dtype=np.int32)
            flat_list: list[int] = []
            for a, sup in enumerate(supports):
                flat_list.extend(int(v) for v in sup)
                offsets[a + 1] = len(flat_list)
            idx_arr = np.asarray(flat_list, dtype=np.int32)
            dbl_p = ctypes.POINTER(ctypes.c_double)
            int_p = ctypes.POINTER(ctypes.c_int)
            for x in range(m):
                st = np.ascontiguousarray(sigma_tilde[:, x], dtype=np.float64)
                sig_next = sigma_mat - np.outer(st, st)
                chol_next = _safe_cholesky(sig_next)
                fluct = np.ascontiguousarray(chol_next @ std_normals, dtype=np.float64)
                exp_future = float(
                    lib.cpp_voi_eval_candidate(
                        int(m),
                        int(k),
                        int(n_y),
                        int(n_mu),
                        m_arr.ctypes.data_as(dbl_p),
                        st.ctypes.data_as(dbl_p),
                        fluct.ctypes.data_as(dbl_p),
                        yq_arr.ctypes.data_as(dbl_p),
                        offsets.ctypes.data_as(int_p),
                        idx_arr.ctypes.data_as(int_p),
                        float(epsilon),
                    )
                )
                scores[x] = (cur_best_risk - exp_future) / float(costs[x])
        else:
            for x in range(m):
                st = sigma_tilde[:, x]
                sig_next = sigma_mat - np.outer(st, st)
                chol_next = _safe_cholesky(sig_next)
                # Zero-mean posterior fluctuation matrix (M, N_mu) computed ONCE per candidate x!
                fluct = chol_next @ std_normals
                acc_best_risk = 0.0
                for j in range(n_y):
                    m_next = means + float(y_quantiles[j]) * st
                    samples = m_next[:, None] + fluct
                    mu_star = np.max(samples, axis=0)
                    min_r = 1.0
                    for a in range(k):
                        v_a = np.max(samples[supports[a]], axis=0)
                        r_a = float(np.mean((mu_star - v_a) > epsilon))
                        if r_a < min_r:
                            min_r = r_a
                    acc_best_risk += min_r
                exp_future = acc_best_risk / float(n_y)
                scores[x] = (cur_best_risk - exp_future) / float(costs[x])

        best_x = int(np.argmax(scores))
        if float(scores[best_x]) > 1e-12:
            return best_x, scores, cur_best_risk, False

    # Rare-event tail continuation: exact analytical Gaussian log-tail Bayesian root-risk VOI
    cur_log_tail = _analytical_log_tail_root_risk(means, sigma_mat, supports, complements, epsilon)
    tail_scores = np.full(m, -math.inf, dtype=np.float64)
    for x in range(m):
        st = sigma_tilde[:, x]
        sig_next = sigma_mat - np.outer(st, st)
        acc_log = 0.0
        for j in range(n_y):
            m_next = means + float(y_quantiles[j]) * st
            acc_log += _analytical_log_tail_root_risk(m_next, sig_next, supports, complements, epsilon)
        exp_log_next = acc_log / float(n_y)
        tail_scores[x] = (cur_log_tail - exp_log_next) / float(costs[x])
    best_x = int(np.argmax(tail_scores))
    return best_x, tail_scores, cur_best_risk, True


def clopper_pearson_upper(k_fail: int, n_trials: int, alpha: float = 0.01) -> float:
    """Exact one-sided (1 - alpha) Clopper-Pearson upper confidence bound on binomial proportion."""
    if k_fail >= n_trials:
        return 1.0
    return float(beta_dist.ppf(1.0 - alpha, k_fail + 1, n_trials - k_fail))


# ---------------------------------------------------------------------------
# 3. Shared Conjugate Gaussian Posterior with Exact Credible & Frequentist Radii
# ---------------------------------------------------------------------------
class SharedGaussianPosterior:
    """Exact conjugate Gaussian posterior `mu | D_t ~ N(m_t, Sigma_t)` shared identically
    across all acquisition policies.

    Supports two formally distinguished stopping ellipsoid radii (`beta_mode`):
      - `posterior_credible`: exact `sqrt(chi2_{r, 1-delta})` credible ellipsoid of contrast
        rank `r = rank(P_{perp 1} K P_{perp 1})` (Appendix `app:posterior-calibration`).
      - `anytime_frequentist`: exact anytime-valid Abbasi-Yadkori / Chowdhury-Gopalan
        self-normalized RKHS/linear ellipsoid `B_rkhs + sqrt(2 * (gamma_t + log(1/delta)))`,
        valid uniformly over all `t >= 1` for every fixed `mu` with `||mu - m_0||_{K^+} <= B_rkhs`.
    """

    def __init__(
        self,
        kernel: np.ndarray,
        prior_mean: float,
        obs_std: float,
        delta: float = 0.05,
        beta_mode: str = "posterior_credible",
        rkhs_bound: float = 1.0,
        contrast_rank: int | None = None,
    ) -> None:
        if beta_mode not in ("posterior_credible", "anytime_frequentist"):
            raise ValueError(f"Unknown beta_mode: {beta_mode!r}")
        self.k_mat = np.array(kernel, dtype=np.float64, copy=True)
        self.m = int(self.k_mat.shape[0])
        self.prior_mean = float(prior_mean)
        self.obs_std = float(obs_std)
        self.obs_var = float(obs_std * obs_std)
        self.inv_obs_var = 1.0 / self.obs_var
        self.delta = float(delta)
        self.beta_mode = beta_mode
        self.rkhs_bound = float(rkhs_bound)

        # Compute exact contrast rank r = rank(P_{perp 1} K P_{perp 1})
        if contrast_rank is None:
            proj = np.eye(self.m, dtype=np.float64) - (1.0 / self.m)
            k_c = proj @ self.k_mat @ proj
            svals = np.linalg.eigvalsh(0.5 * (k_c + k_c.T))
            tol = max(1e-12, 1e-10 * float(np.max(np.abs(svals))))
            self.contrast_rank = max(1, int(np.sum(svals > tol)))
        else:
            self.contrast_rank = max(1, int(contrast_rank))

        self._credible_beta = math.sqrt(float(chi2.ppf(1.0 - self.delta, df=self.contrast_rank)))

        self.mean = np.full(self.m, self.prior_mean, dtype=np.float64)
        self.sigma_mat = np.asfortranarray(self.k_mat, dtype=np.float64)
        self.arm_counts = np.zeros(self.m, dtype=np.int64)
        self.raw_sums = np.zeros(self.m, dtype=np.float64)
        self.info_gain = 0.0
        self.total_pulls = 0
        self._chol_dirty = True
        self._chol_cache: np.ndarray | None = None

    def observe(self, arm_idx: int, reward: float) -> None:
        y = float(reward)
        self.arm_counts[arm_idx] += 1
        self.raw_sums[arm_idx] += y
        self.total_pulls += 1

        col = self.sigma_mat[:, arm_idx].copy()
        s_jj = max(0.0, float(col[arm_idx]))
        self.info_gain += 0.5 * math.log(max(1.0, 1.0 + s_jj * self.inv_obs_var))
        denom = self.obs_var + s_jj
        resid = y - float(self.mean[arm_idx])
        self.mean += (resid / denom) * col
        blas.dger(-1.0 / denom, col, col, a=self.sigma_mat, overwrite_a=1)
        self._chol_dirty = True

        # Exact Woodbury re-stabilization every 512 pulls prevents any floating-point drift
        if self.total_pulls % 512 == 0:
            self.resync_exact()

    def resync_exact(self) -> None:
        """Exact batch Woodbury recomputation from sufficient statistics `(arm_counts, raw_sums)`."""
        obs_idx = np.flatnonzero(self.arm_counts > 0)
        if len(obs_idx) == 0:
            self.sigma_mat = np.asfortranarray(self.k_mat, dtype=np.float64)
            self.mean = np.full(self.m, self.prior_mean, dtype=np.float64)
            self.info_gain = 0.0
            self._chol_dirty = True
            return
        cnt = self.arm_counts[obs_idx].astype(np.float64)
        arm_means = self.raw_sums[obs_idx] / cnt
        noise_diag = self.obs_var / cnt
        k_oo = self.k_mat[np.ix_(obs_idx, obs_idx)]
        a_mat = 0.5 * (k_oo + k_oo.T) + np.diag(noise_diag)
        c_fac, low = cho_factor(a_mat + 1e-13 * np.eye(len(obs_idx), dtype=np.float64))
        k_mo = self.k_mat[:, obs_idx]
        sol_om = cho_solve((c_fac, low), k_mo.T)
        sig_new = self.k_mat - (k_mo @ sol_om)
        self.sigma_mat = np.asfortranarray(0.5 * (sig_new + sig_new.T), dtype=np.float64)
        alpha_o = cho_solve((c_fac, low), arm_means - self.prior_mean)
        self.mean = self.prior_mean + (k_mo @ alpha_o)
        logdet_a = 2.0 * float(np.sum(np.log(np.diag(c_fac))))
        logdet_d = float(np.sum(np.log(noise_diag)))
        self.info_gain = max(0.0, 0.5 * (logdet_a - logdet_d))
        self._chol_dirty = True

    def stds(self) -> np.ndarray:
        return np.sqrt(np.maximum(1e-18, np.diag(self.sigma_mat)))

    def cholesky(self) -> np.ndarray:
        if self._chol_dirty or self._chol_cache is None:
            self._chol_cache = _safe_cholesky(self.sigma_mat)
            self._chol_dirty = False
        return self._chol_cache

    def beta(self) -> float:
        if self.beta_mode == "posterior_credible":
            return self._credible_beta
        return self.rkhs_bound + math.sqrt(max(0.0, 2.0 * (self.info_gain + math.log(1.0 / self.delta))))

    def contrast_variance_reduction(self, g_vec: np.ndarray) -> np.ndarray:
        sg = self.sigma_mat @ g_vec
        return (sg * sg) / (self.obs_var + np.maximum(1e-18, np.diag(self.sigma_mat)))


# ---------------------------------------------------------------------------
# 4. Matched Benchmark Problem Generators (M=64, M=16, Fixed-Feature d=8)
# ---------------------------------------------------------------------------
class GaussianPairedDeconfoundedProblem(DeconfoundedOverlapCorrelationProblem):
    """Exact `DeconfoundedOverlapCorrelationProblem` (M=64, K=8, xi=0) equipped with
    exact paired intrinsic Gaussian observation tapes `Y_{x, n} = mu_x + sigma * Z_{x, n}`.
    """

    def __init__(
        self,
        seed: int,
        overlap: float,
        rho: float,
        target_margin: float = 0.055,
        tau0: float = 0.14,
        hw: float = 0.14,
    ) -> None:
        super().__init__(
            seed=seed,
            overlap=overlap,
            rho=rho,
            mismatch_xi=0.0,
            target_margin=target_margin,
            tau0=tau0,
            hw=hw,
        )

    def oracle(self, seed: int) -> _GaussianOracle:
        return _GaussianOracle(len(self.graph), seed, self.means, self.obs_std)


class SmallOverlapCorrelationProblem(Problem):
    """Scaled M=16, K=4 sibling of `DeconfoundedOverlapCorrelationProblem` for the
    Bayesian Root-Risk VOI reference study.

    Guarantees:
      - Zero support containments (`b=3` is strictly private for every root action).
      - `overlap = 0.00`: disjoint supports `|S(a)| = 4, |B_a| = 12`.
      - `overlap = 0.75`: overlapping supports `|S(a)| = 8, |B_a| = 8` (4 shared motifs from neighbors).
      - Full-rank 16x16 SPD covariance `K(rho)` strictly equal to `tau0^2 I_16` at `rho = 0`.
      - Exact paired intrinsic Gaussian observation tapes `N(mu_x, obs_std^2)`.
    """

    def __init__(
        self,
        seed: int,
        overlap: float,
        rho: float,
        target_margin: float = 0.055,
        tau0: float = 0.14,
        hw: float = 0.14,
    ) -> None:
        k_act = 4
        b_mot = 4
        m_leaves = k_act * b_mot  # 16
        self.overlap = float(overlap)
        self.rho = float(rho)
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))
        self.prior_mean = 0.48

        n_sh = 0 if overlap <= 1e-9 else 4  # 0 shared (|S|=4) vs 4 shared (|S|=8)
        children: list[tuple[int, ...]] = [tuple(range(1, k_act + 1))]
        leaf_offset = 1 + k_act
        for g in range(k_act):
            own = [leaf_offset + g * b_mot + b for b in range(b_mot)]
            shared: list[int] = []
            # Pull shared motifs cyclically from (g+1), (g+2) over b in 0..1 (never b=2,3!)
            for offset in (1, 2):
                for b in (0, 1):
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

        k_grp = 0.25 * np.eye(k_act) + 0.75 * np.ones((k_act, k_act))
        k_mot = ar1_corr_matrix(b_mot, rho)
        k_corr = np.kron(k_grp, k_mot)
        self.kernel = (tau0 * tau0) * ((1.0 - rho) * np.eye(m_leaves) + rho * k_corr)
        k_inv = np.linalg.inv(self.kernel)

        rng = np.random.default_rng(seed * 10007 + 131)
        perm = rng.permutation(k_act)
        act_eff = np.zeros(k_act, dtype=np.float64)
        gaps_vec = [0.10, 0.10 - target_margin, 0.10 - 1.45 * target_margin, -0.02]
        for rk, gi in enumerate(perm):
            act_eff[int(gi)] = gaps_vec[rk]

        l_mot = np.linalg.cholesky(k_mot + 1e-6 * np.eye(b_mot))
        z_sh = l_mot @ rng.standard_normal(b_mot)
        z_sh = 0.060 * z_sh / max(1.0, float(np.max(np.abs(z_sh))))
        z_sh[3] = float(np.max(z_sh)) + 0.025  # motif peak in private slot b=3
        z_id = np.stack([l_mot @ rng.standard_normal(b_mot) for _ in range(k_act)], axis=0)
        z_id = 0.035 * z_id / max(1.0, float(np.max(np.abs(z_id))))

        f_true = (
            self.prior_mean
            + act_eff[:, None]
            + math.sqrt(max(0.0, rho)) * z_sh[None, :]
            + math.sqrt(max(0.0, 1.0 - rho)) * z_id
        ).reshape(-1)
        f_true = np.clip(f_true, hw + 0.05, 1.0 - hw - 0.05)

        diff = f_true - self.prior_mean
        self.clean_rkhs_norm = float(math.sqrt(max(0.0, float(diff @ (k_inv @ diff)))))
        self.true_rkhs_norm = self.clean_rkhs_norm
        means = {leaf_offset + i: float(f_true[i]) for i in range(m_leaves)}
        super().__init__(f"small16_o{overlap:.2f}_r{rho:.2f}_s{seed}", graph, means, ())

    def oracle(self, seed: int) -> _GaussianOracle:
        return _GaussianOracle(len(self.graph), seed, self.means, self.obs_std)


class FixedFeatureGaussianOverlapProblem(Problem):
    """Fixed-feature Gaussian linear problem (`M=64, K=8, d=8`) for confirmatory anytime-valid
    frequentist stopping analysis.

    Reuses the exact `DeconfoundedOverlapCorrelationProblem` zero-containment graph supports
    for `omega in {0.0, 0.75}`, and projects the covariance & true mean onto a known `d=8`
    feature basis `Phi in R^{64 x 8}` (so `K = Phi Phi^T`, `mu = m_0 + Phi theta*` with exact
    known parameter norm `||theta*||_2 <= B`, making the Abbasi-Yadkori anytime-valid
    self-normalized ellipsoid `B + sqrt(2(gamma_t + log(1/delta)))` uniformly valid for every
    fixed `theta*` across all `t >= 1`).
    """

    def __init__(
        self,
        seed: int,
        overlap: float,
        rho: float,
        d_feat: int = 8,
        target_margin: float = 0.055,
        tau0: float = 0.14,
        hw: float = 0.14,
    ) -> None:
        base = GaussianPairedDeconfoundedProblem(
            seed=seed, overlap=overlap, rho=rho, target_margin=target_margin, tau0=tau0, hw=hw
        )
        self.overlap = base.overlap
        self.rho = base.rho
        self.hw = base.hw
        self.obs_std = base.obs_std
        self.prior_mean = base.prior_mean
        self.d_feat = int(d_feat)

        # Build clean rank-d feature basis from top eigenvectors of base.kernel (when rho>0)
        # or 8-block indicator basis (when rho=0, one orthogonal feature per action group!)
        m_leaves = len(base.graph.leaves)
        if rho <= 1e-9:
            # Strictly block-diagonal across the 8 groups so groups share zero statistical info
            phi = np.zeros((m_leaves, d_feat), dtype=np.float64)
            for g in range(8):
                for b in range(8):
                    # Mild deterministic intra-group loading preserving motif ordering
                    w_b = 0.75 + 0.25 * (b / 7.0)
                    phi[g * 8 + b, g] = tau0 * w_b
        else:
            evals, evecs = np.linalg.eigh(0.5 * (base.kernel + base.kernel.T))
            top_idx = np.argsort(-evals)[:d_feat]
            top_e = np.maximum(1e-10, evals[top_idx])
            phi = evecs[:, top_idx] * np.sqrt(top_e)[None, :]

        # Project base.f_clean - prior_mean cleanly onto col(phi) so linear model is EXACT (xi = 0)!
        rhs = base.f_clean - self.prior_mean
        theta_star, _, _, _ = np.linalg.lstsq(phi, rhs, rcond=None)
        f_proj = self.prior_mean + (phi @ theta_star)
        # Ensure exact exterior margin >= 0.045 so projected instances remain cleanly identifiable
        ss = SupportStructure(base.graph)
        act_vals = [float(np.max(f_proj[sup])) for sup in ss.supports]
        best_a = int(np.argmax(act_vals))
        comp_best = ss.complements[best_a]
        ext_gap = float(act_vals[best_a] - np.max(f_proj[comp_best]))
        if ext_gap < target_margin * 0.75 and ext_gap > 1e-6:
            scale = (target_margin / ext_gap)
            theta_star *= scale
            f_proj = self.prior_mean + (phi @ theta_star)

        self.phi = phi
        self.theta_star = theta_star
        self.kernel = phi @ phi.T
        self.clean_rkhs_norm = float(np.linalg.norm(theta_star))
        self.true_rkhs_norm = self.clean_rkhs_norm
        leaf_offset = 1 + 8
        means = {leaf_offset + i: float(f_proj[i]) for i in range(m_leaves)}
        super().__init__(f"lin{d_feat}_o{overlap:.2f}_r{rho:.2f}_s{seed}", base.graph, means, ())

    def oracle(self, seed: int) -> _GaussianOracle:
        return _GaussianOracle(len(self.graph), seed, self.means, self.obs_std)


# ---------------------------------------------------------------------------
# 5. Unified Matched-Model Certification Session Across All 7 Policies
# ---------------------------------------------------------------------------
ALL_V12_POLICIES = (
    "gp_ucb",
    "gp_ts",
    "gp_ei",
    "kg",
    "gp_os",
    "cd_joint",
    "bayesian_voi",
)


def default_check_schedule(t: int, full_every_step: bool = False) -> bool:
    """Identical deterministic certificate-check schedule shared by ALL policies."""
    if full_every_step:
        return True
    if t <= 50:
        return True
    if t <= 500:
        return (t % 5) == 0
    if t <= 2000:
        return (t % 10) == 0
    return (t % 20) == 0


class MatchedModelBEDSession:
    """Runs one acquisition policy under a strictly shared Gaussian posterior and common stopping rule.

    Guarantees:
      - Identical `SharedGaussianPosterior` state update for every policy.
      - Identical `JointEllipsoidCertifier.certify_action_gp` stopping check, schedule,
        tolerances, and tie-breaking for every policy.
      - Paired intrinsic observation tapes from `problem.oracle(obs_seed)`.
      - Independent acquisition RNG (`acq_seed`) and independent posterior-risk evaluation RNG
        (`eval_seed`), preventing any correlation between acquisition MC noise and reported risk.
    """

    def __init__(
        self,
        problem: Problem,
        obs_seed: int,
        policy: str,
        epsilon: float,
        delta: float,
        kernel: np.ndarray,
        prior_mean: float,
        obs_std: float,
        beta_mode: str = "posterior_credible",
        rkhs_bound: float = 1.0,
        contrast_rank: int | None = None,
        costs: Sequence[float] | np.ndarray | None = None,
        full_check_every_step: bool = False,
        budget_checkpoints: Sequence[int] = (50, 100, 250, 500, 1000, 2000, 5000),
        eval_mc_draws: int = 4096,
        voi_n_y: int = 32,
        voi_n_mu: int = 2048,
        track_mc_risk_stop: bool = False,
    ) -> None:
        if policy not in ALL_V12_POLICIES:
            raise ValueError(f"Unknown policy: {policy!r}")
        self.problem = problem
        self.graph = problem.graph
        self.support_struct = SupportStructure(self.graph, costs=costs)
        self.policy = policy
        self.epsilon = float(epsilon)
        self.delta = float(delta)
        self.full_check_every_step = bool(full_check_every_step)
        self.budget_checkpoints = tuple(sorted(set(int(b) for b in budget_checkpoints)))
        self.eval_mc_draws = int(eval_mc_draws)
        self.track_mc_risk_stop = bool(track_mc_risk_stop)

        self.oracle = problem.oracle(obs_seed)
        self.posterior = SharedGaussianPosterior(
            kernel=kernel,
            prior_mean=prior_mean,
            obs_std=obs_std,
            delta=delta,
            beta_mode=beta_mode,
            rkhs_bound=rkhs_bound,
            contrast_rank=contrast_rank,
        )
        self.certifier = JointEllipsoidCertifier(
            self.support_struct,
            epsilon=self.epsilon,
            solver="colgen_lazy",
            exact_linear_mean=False,
        )

        # True values & regrets for diagnostic metrics (NEVER used by any policy!)
        vals = self.graph.optimal_values(problem.means)
        root_ch = self.graph.children[self.graph.root]
        self._opt_mu = float(vals[self.graph.root])
        self._true_action_regrets = [max(0.0, self._opt_mu - float(vals[c])) for c in root_ch]
        self._true_leaf_means = np.array([float(problem.means[lf]) for lf in self.support_struct.leaves], dtype=np.float64)
        self._is_eps_opt_leaf = (self._opt_mu - self._true_leaf_means) <= (self.epsilon + 1e-12)
        self._leaf_to_actions: list[list[int]] = [[] for _ in range(self.posterior.m)]
        for a, sup in enumerate(self.support_struct.supports):
            for idx in sup:
                self._leaf_to_actions[int(idx)].append(a)

        # Dedicated independent RNGs
        self._acq_rng = np.random.default_rng((obs_seed * 1000003 + 17) & 0xFFFFFFFFFFFFFFFF)
        self._eval_rng = np.random.default_rng((obs_seed * 2000003 + 97) & 0xFFFFFFFFFFFFFFFF)
        self._eval_std_normals = self._eval_rng.standard_normal((self.posterior.m, self.eval_mc_draws))

        # Precompute stratified normal quantiles for Bayesian Root-Risk VOI
        from scipy.stats import norm

        probs = (np.arange(int(voi_n_y), dtype=np.float64) + 0.5) / float(voi_n_y)
        self._voi_y_quantiles = norm.ppf(probs)
        self._voi_n_mu = int(voi_n_mu)

        # Runtime state & telemetry
        self.calls = 0
        self.total_cost = 0.0
        self.certified = False
        self.action = 0
        self.current_regret = math.inf
        self.discovery_step: int | None = None
        self.suboptimal_pulls = 0
        self.acq_time_s = 0.0
        self.cert_time_s = 0.0
        self.mc_voi_steps = 0
        self.tail_voi_steps = 0

        # Secondary MC posterior-risk stopping diagnostic (with 99% Clopper-Pearson control)
        self.mc_risk_certified = False
        self.mc_risk_cert_step: int | None = None
        self.mc_risk_cert_cost: float | None = None
        self.mc_risk_cert_action: int = 0
        self.mc_risk_cert_ucb: float = 1.0

        # Cached latest certificates (used by CD-Joint and common stopping check)
        self._last_certs: list[ActionCertificate] = []
        self._checkpoint_records: dict[int, dict[str, float]] = {}

        # Initial certificate check at t = 0
        self._check_certificate()

    def _exact_check_action_certifies(
        self, action: int, means: np.ndarray, sigma_mat: np.ndarray, beta: float
    ) -> tuple[bool, float]:
        """100%-exact sound stopping check for whether `R_t(action) <= self.epsilon`.

        Uses:
          1. Exact O(M) center-mean primal lower bound (`m_t in C_t`): if
             `max_{z notin S(a)} m_z - max_{y in S(a)} m_y > eps`, then `R_t(a) > eps` is
             proved immediately with zero conic solves.
          2. Exact vectorized single-vertex upper bound: if `max_z min_y (...) <= eps`,
             certifies immediately with zero conic solves.
          3. Exact dual Frank-Wolfe only on challengers with `vert_ub > eps`, breaking as
             soon as any single challenger has certified lower bound `val_z - gap_z > eps`.
        """
        sup = self.support_struct.supports[action]
        comp = self.support_struct.complements[action]
        if len(comp) == 0:
            return True, 0.0

        # Step 1: exact primal lower bound at center m_t in C_t
        max_m_sup = float(np.max(means[sup]))
        max_m_comp = float(np.max(means[comp]))
        if max_m_comp - max_m_sup > self.epsilon + 1e-12:
            return False, max_m_comp - max_m_sup

        diag_all = np.maximum(1e-18, np.diag(sigma_mat))
        stds_all = np.sqrt(diag_all)
        m_sup_full = means[sup]
        s_sup_full = stds_all[sup]

        max_lo_s = float(np.max(m_sup_full - beta * s_sup_full))
        keep = (m_sup_full + beta * s_sup_full) >= max_lo_s - 1e-12
        sup_nd = sup[keep]
        if len(sup_nd) > 24:
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
        order = np.argsort(-vert_ub)

        # Step 2: instant sound certification if even vertex upper bound <= eps
        top_ub = float(vert_ub[int(order[0])])
        if top_ub <= self.epsilon:
            return True, max(0.0, top_ub)

        # Step 3: solve only challengers with vert_ub > eps; stop on first verified refutation
        best_val = -math.inf
        for pos in order:
            ub_z = float(vert_ub[pos])
            if ub_z <= self.epsilon:
                break
            z_idx = int(comp[pos])
            val_z, gap_z, _ = solve_ellipsoid_challenger(
                float(means[z_idx]),
                m_s,
                float(diag_c[pos]),
                sig_sc[:, pos],
                sig_ss,
                beta,
                tol=1e-6,
                max_iter=28,
            )
            if val_z > best_val:
                best_val = val_z
            if val_z > self.epsilon:
                # If duality gap makes lower bound uncertain, polish with tighter tol/iters
                if val_z - gap_z <= self.epsilon:
                    val_z, gap_z, _ = solve_ellipsoid_challenger(
                        float(means[z_idx]),
                        m_s,
                        float(diag_c[pos]),
                        sig_sc[:, pos],
                        sig_ss,
                        beta,
                        tol=1e-9,
                        max_iter=80,
                    )
                if val_z > self.epsilon:
                    return False, float(val_z)
        return True, max(0.0, best_val)

    def _check_certificate(self) -> None:
        t0 = time.perf_counter()
        means = self.posterior.mean
        sig = self.posterior.sigma_mat
        beta = self.posterior.beta()
        k = self.support_struct.k

        # Order actions by posterior mean value first (identical for all policies)
        act_means = [float(np.max(means[sup])) for sup in self.support_struct.supports]
        order = sorted(range(k), key=lambda a: (-act_means[a], a))

        self._cert_by_action = {}
        best_a = order[0]
        best_reg = math.inf
        for a in order:
            ok, reg_a = self._exact_check_action_certifies(a, means, sig, beta)
            if ok:
                self.action = int(a)
                self.current_regret = float(reg_a)
                self.certified = True
                break
            if (reg_a, a) < (best_reg, best_a):
                best_reg = reg_a
                best_a = a
        if not self.certified:
            self.action = int(best_a)
            self.current_regret = float(best_reg)
        self.cert_time_s += time.perf_counter() - t0

        if self.track_mc_risk_stop and not self.mc_risk_certified:
            chol = self.posterior.cholesky()
            risks = estimate_posterior_root_risks(
                means, chol, self.support_struct.supports, self.epsilon, self._eval_std_normals
            )
            best_ra = int(np.argmin(risks))
            k_fail = int(round(float(risks[best_ra]) * self.eval_mc_draws))
            cp_hi = clopper_pearson_upper(k_fail, self.eval_mc_draws, alpha=0.01)
            if cp_hi <= self.delta:
                self.mc_risk_certified = True
                self.mc_risk_cert_step = int(self.calls)
                self.mc_risk_cert_cost = float(self.total_cost)
                self.mc_risk_cert_action = best_ra
                self.mc_risk_cert_ucb = cp_hi

    def _record_checkpoint(self, step_t: int) -> None:
        chol = self.posterior.cholesky()
        risks = estimate_posterior_root_risks(
            self.posterior.mean,
            chol,
            self.support_struct.supports,
            self.epsilon,
            self._eval_std_normals,
        )
        min_risk = float(np.min(risks))
        rec_a = int(self.action) if self.certified else int(np.argmin(risks))
        self._checkpoint_records[step_t] = {
            "posterior_root_risk": round(min_risk, 6),
            "root_regret": round(float(self._true_action_regrets[rec_a]), 6),
            "certified": float(self.certified),
            "cost": round(float(self.total_cost), 4),
        }

    def select_query(self) -> int:
        """Select next terminal index `0..M-1` using `self.policy` on the shared posterior."""
        t0 = time.perf_counter()
        means = self.posterior.mean
        sig = self.posterior.sigma_mat
        stds = self.posterior.stds()
        costs = self.support_struct.costs
        m = self.posterior.m
        beta = self.posterior.beta()

        if self.policy == "gp_ucb":
            # Standard Srinivas et al. (2012) finite-domain GP-UCB exploration schedule
            t_eff = max(1, self.calls + 1)
            kappa = math.sqrt(2.0 * math.log(m * (math.pi ** 2) * (t_eff * t_eff) / (6.0 * self.delta)))
            chosen = int(np.argmax(means + kappa * stds))

        elif self.policy == "gp_ts":
            chol = self.posterior.cholesky()
            draw = means + chol @ self._acq_rng.standard_normal(m)
            chosen = int(np.argmax(draw))

        elif self.policy == "gp_ei":
            log_scores = noisy_gp_ei_log_scores(means, stds, costs)
            chosen = int(np.argmax(log_scores))

        elif self.policy == "kg":
            log_scores = correlated_kg_log_scores(means, sig, self.posterior.obs_var, costs)
            chosen = int(np.argmax(log_scores))

        elif self.policy == "gp_os":
            lo = means - beta * stds
            hi = means + beta * stds
            best_sep = -math.inf
            best_p, best_q = 0, -1
            for a in range(self.support_struct.k):
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
                chosen = best_p
            else:
                sp = float(stds[best_p]) / math.sqrt(float(costs[best_p]))
                sq = float(stds[best_q]) / math.sqrt(float(costs[best_q]))
                chosen = best_p if sp >= sq else best_q

        elif self.policy == "cd_joint":
            # Eq. (9)-(10) Safeguarded Contrast-Directed Acquisition on shared posterior
            # Refresh dual contrast for the single containing action on check steps (or if empty)
            ucb = means + beta * stds
            y_opt = int(np.argmax(ucb))
            containers = self._leaf_to_actions[y_opt]
            if not self._cert_by_action:
                # Pick containing action with best posterior mean (breaking ties by smallest action idx)
                best_b = max(containers, key=lambda b: (float(np.max(means[self.support_struct.supports[b]])), -b))
                c_b = self.certifier.certify_action_gp(
                    action=int(best_b), means=means, sigma_mat=sig, beta=beta, stop_if_above_eps=False
                )
                self._cert_by_action[int(best_b)] = c_b
            else:
                best_b = int(next(iter(self._cert_by_action.keys())))
                c_b = self._cert_by_action[best_b]
                if best_b not in containers:
                    best_b = max(containers, key=lambda b: (float(np.max(means[self.support_struct.supports[b]])), -b))
                    c_b = self.certifier.certify_action_gp(
                        action=int(best_b), means=means, sigma_mat=sig, beta=beta, stop_if_above_eps=False
                    )
                    self._cert_by_action[int(best_b)] = c_b
            if c_b.challenger_idx < 0:
                chosen = y_opt
            else:
                g_dual = c_b.contrast
                mean_contrast = float(g_dual @ means)
                if mean_contrast <= 0.5 * self.epsilon:
                    g_vec = g_dual
                else:
                    g_vec = np.zeros(m, dtype=np.float64)
                    g_vec[int(c_b.challenger_idx)] = 1.0
                    g_vec[y_opt] = -1.0
                vred = self.posterior.contrast_variance_reduction(g_vec)
                chosen = int(np.argmax(vred / costs))

        elif self.policy == "bayesian_voi":
            # Fresh antithetic CRN normal matrix per step, shared across ALL M candidates
            half = self._voi_n_mu // 2
            z_half = self._acq_rng.standard_normal((m, half))
            u_crn = np.concatenate([z_half, -z_half], axis=1)
            if u_crn.shape[1] < self._voi_n_mu:
                u_crn = np.concatenate([u_crn, self._acq_rng.standard_normal((m, 1))], axis=1)
            chosen, _, _, used_tail = select_bayesian_root_voi(
                means=means,
                sigma_mat=sig,
                obs_var=self.posterior.obs_var,
                costs=costs,
                supports=self.support_struct.supports,
                complements=self.support_struct.complements,
                epsilon=self.epsilon,
                y_quantiles=self._voi_y_quantiles,
                std_normals=u_crn,
            )
            if used_tail:
                self.tail_voi_steps += 1
            else:
                self.mc_voi_steps += 1
        else:
            raise AssertionError(f"Unhandled policy: {self.policy}")

        self.acq_time_s += time.perf_counter() - t0
        return chosen

    def run(self, cap: int) -> dict:
        """Run up to `cap` observations and return full structured metrics dictionary."""
        t_start = time.perf_counter()
        ck_set = set(self.budget_checkpoints)

        while not self.certified and self.calls < cap:
            arm_idx = self.select_query()
            leaf = self.support_struct.leaves[arm_idx]
            reward = float(self.oracle.sample(leaf))
            self.calls += 1
            self.total_cost += float(self.support_struct.costs[arm_idx])

            if self._is_eps_opt_leaf[arm_idx]:
                if self.discovery_step is None:
                    self.discovery_step = int(self.calls)
            else:
                self.suboptimal_pulls += 1

            self.posterior.observe(arm_idx, reward)

            should_check = (
                default_check_schedule(self.calls, full_every_step=self.full_check_every_step)
                or (self.calls in ck_set)
                or (self.calls == cap)
            )
            if should_check:
                self._check_certificate()

            if self.calls in ck_set:
                self._record_checkpoint(self.calls)

        # Finalize any checkpoints at or after certification by freezing the certified state
        if self.certified:
            chol = self.posterior.cholesky()
            risks = estimate_posterior_root_risks(
                self.posterior.mean,
                chol,
                self.support_struct.supports,
                self.epsilon,
                self._eval_std_normals,
            )
            final_min_risk = float(np.min(risks))
            final_reg = float(self._true_action_regrets[int(self.action)])
            frozen = {
                "posterior_root_risk": round(final_min_risk, 6),
                "root_regret": round(final_reg, 6),
                "certified": 1.0,
                "cost": round(float(self.total_cost), 4),
            }
            for ck in self.budget_checkpoints:
                if ck not in self._checkpoint_records and ck <= cap:
                    self._checkpoint_records[ck] = dict(frozen)

        total_s = time.perf_counter() - t_start
        if self.certified:
            rec_action = int(self.action)
        else:
            # Best root action by posterior mean when budget expires
            act_m = [float(np.max(self.posterior.mean[sup])) for sup in self.support_struct.supports]
            rec_action = int(np.argmax(act_m))
        true_reg = float(self._true_action_regrets[rec_action])
        false_cert = bool(self.certified and true_reg > self.epsilon + 1e-12)

        return {
            "policy": self.policy,
            "certified": bool(self.certified),
            "false_certificate": false_cert,
            "steps": int(self.calls),
            "restricted_steps": int(self.calls) if self.certified else int(cap),
            "total_cost": round(float(self.total_cost), 4),
            "restricted_cost": round(float(self.total_cost), 4),
            "action": rec_action,
            "final_regret": round(true_reg, 6),
            "discovery_step": int(self.discovery_step) if self.discovery_step is not None else int(cap),
            "discovered": bool(self.discovery_step is not None),
            "proxy_query_frac": round(self.suboptimal_pulls / max(1, self.calls), 5),
            "arm_counts": [int(c) for c in self.posterior.arm_counts.tolist()],
            "acq_ms": round(1e3 * self.acq_time_s, 3),
            "acq_ms_per_step": round(1e3 * self.acq_time_s / max(1, self.calls), 4),
            "cert_ms": round(1e3 * self.cert_time_s, 3),
            "total_ms": round(1e3 * total_s, 3),
            "mc_voi_steps": int(self.mc_voi_steps),
            "tail_voi_steps": int(self.tail_voi_steps),
            "mc_risk_certified": bool(self.mc_risk_certified),
            "mc_risk_cert_step": int(self.mc_risk_cert_step) if self.mc_risk_cert_step is not None else int(cap),
            "mc_risk_cert_cost": round(float(self.mc_risk_cert_cost), 4) if self.mc_risk_cert_cost is not None else round(float(self.total_cost), 4),
            "mc_risk_cert_error": bool(
                self.mc_risk_certified and self._true_action_regrets[self.mc_risk_cert_action] > self.epsilon + 1e-12
            ),
            "checkpoints": {str(k): v for k, v in sorted(self._checkpoint_records.items())},
        }
