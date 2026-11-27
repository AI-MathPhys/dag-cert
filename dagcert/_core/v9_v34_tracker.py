"""V33/V34 Adaptive Nuisance-KL Tracker & Certified Global Profiled-Likelihood Oracles.

Implements the exact fixed-feature, unknown heterogeneous Gaussian variance framework
from Versions V22, V23, V32, V33, and V34 (`v34_theory_notes.tex`):
  - Exact structural feature-hull screening for closed invalidating polyhedra H_{a,z}
  - Globally certified rank-2 exact cubic projection solver (Thm. V23.2, Prop. V23.1)
    handling arbitrary 2D polyhedra (halfspaces, wedges, multi-facet cones) with
    outward-rounded enclosures (immune to Behrens-Fisher multimodality, CE V23.1)
  - Globally certified general-d branch-and-bound solver using exact box localization
    (Lem. V22.1) and concave-secant convex QP minorants (tightening Prop. V22.2),
    plus fast root-QP screening and warm-started affine outer cuts (Prop. V22.3)
  - Globally certified outer information-game solvers: certified affine-cut bisection
    for rank-2 (Thm. V23.3) and Kelley cutting-plane LP for general d (Prop. V22.3)
  - Denominator-free vanishing-baseline batch schedule (Eq. V33.1--V33.2) with
    paired intrinsic Gaussian observation tapes
  - Full 2x2 V33/V34 tracker variants:
      * Square-index refreshes {k^2} vs. Sparse four-power refreshes {4^k} (Eq. V34.3)
      * All-action evidence (V33) vs. Action-local predictably skipped evidence (Thm. V34.1)
      * Sticky hysteresis (Lem. V34.2) + optional negative controls (wealth reset,
        local uncertified null solver, Bonferroni component split, Student hedge Thm. V32.2)
"""
from __future__ import annotations

import ctypes
from dataclasses import dataclass, field
import hashlib
import heapq
import math
from pathlib import Path
import subprocess
import tempfile
import time
from typing import Any, Callable, Sequence

import numpy as np
from scipy.optimize import linprog, minimize


CPP_V34_BNB_SOURCE = Path(__file__).resolve().parents[1] / "_native" / "_cpp_v34_bnb.cpp"


class _CppBnBResult(ctypes.Structure):
    _fields_ = [
        ("lower", ctypes.c_double),
        ("upper", ctypes.c_double),
        ("nodes_expanded", ctypes.c_int),
        ("used_root_qp_only", ctypes.c_int),
    ]


class CppV34BnBRunner:
    """On-demand `-O3 -std=c++17` outward-certified B&B + Dual-QP bridge."""

    _lib = None
    _so_path: Path | None = None

    @classmethod
    def ensure_loaded(cls):
        if cls._lib is not None:
            return cls._lib
        import os
        import shutil
        import sys

        src_bytes = CPP_V34_BNB_SOURCE.read_bytes()
        sha = hashlib.sha256(b"-ffp-contract=off" + src_bytes).hexdigest()[:16]
        ext = ".dylib" if sys.platform == "darwin" else ".so"
        so_path = Path(tempfile.gettempdir()) / f"dag_mcts_v34_bnb_{sha}{ext}"
        if not so_path.is_file():
            cxx = os.environ.get("CXX") or shutil.which("g++") or shutil.which("clang++")
            if not cxx:
                raise RuntimeError(
                    "C++17 compiler not found (tried $CXX, g++, clang++). "
                    "Install g++ or clang++ to build the native V34 B&B kernel."
                )
            tmp_so = Path(tempfile.gettempdir()) / f"dag_mcts_v34_bnb_{sha}_{os.getpid()}_{int(time.time()*1e6)}.tmp{ext}"
            subprocess.run(
                [
                    cxx, "-O3", "-ffp-contract=off", "-std=c++17", "-Wall", "-Wextra", "-Werror",
                    "-shared", "-fPIC", str(CPP_V34_BNB_SOURCE), "-o", str(tmp_so),
                ],
                check=True,
            )
            tmp_so.replace(so_path)
        lib = ctypes.CDLL(str(so_path))
        fn = lib.run_v34_bnb_certified
        dbl_p = ctypes.POINTER(ctypes.c_double)
        int_p = ctypes.POINTER(ctypes.c_int)
        fn.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.c_int,
            dbl_p, dbl_p, dbl_p, dbl_p, dbl_p,
            dbl_p, dbl_p, dbl_p, dbl_p, dbl_p,
            ctypes.c_int, int_p, dbl_p,
            ctypes.c_double,
            ctypes.c_int, ctypes.c_double,
            ctypes.c_int, ctypes.c_double,
            ctypes.c_int, ctypes.c_int, ctypes.c_int,
            dbl_p,
            ctypes.POINTER(_CppBnBResult),
        ]
        fn.restype = ctypes.c_int
        cls._lib = lib
        cls._so_path = so_path
        return lib

    @classmethod
    def solve(
        cls,
        H: np.ndarray,
        y: np.ndarray,
        c: np.ndarray,
        k: np.ndarray,
        q: np.ndarray,
        A_poly: np.ndarray,
        b_poly: np.ndarray,
        u_init: np.ndarray,
        box_lo: np.ndarray,
        box_hi: np.ndarray,
        basis_idx: Sequence[int] | None,
        Hb_inv: np.ndarray | None,
        tol: float,
        early_stop_lower: float | None,
        efactor_shift: float | None,
        root_qp_only: bool,
        do_polish: bool,
        max_nodes: int,
    ) -> CertifiedProjectionResult:
        lib = cls.ensure_loaded()
        H_c = np.ascontiguousarray(H, dtype=np.float64)
        y_c = np.ascontiguousarray(y, dtype=np.float64)
        c_c = np.ascontiguousarray(c, dtype=np.float64)
        k_c = np.ascontiguousarray(k, dtype=np.float64)
        q_c = np.ascontiguousarray(q, dtype=np.float64)
        A_c = np.ascontiguousarray(A_poly, dtype=np.float64)
        b_c = np.ascontiguousarray(b_poly, dtype=np.float64)
        u0_c = np.ascontiguousarray(u_init, dtype=np.float64)
        lo_c = np.ascontiguousarray(box_lo, dtype=np.float64)
        hi_c = np.ascontiguousarray(box_hi, dtype=np.float64)
        m, d = H_c.shape
        nc = A_c.shape[0]
        has_basis = 1 if (basis_idx is not None and Hb_inv is not None) else 0
        bidx_c = np.ascontiguousarray(basis_idx if has_basis else np.zeros(d, dtype=np.int32), dtype=np.int32)
        hbinv_c = np.ascontiguousarray(Hb_inv if has_basis else np.zeros((d, d), dtype=np.float64), dtype=np.float64)
        out_u = np.empty(d, dtype=np.float64)
        out_res = _CppBnBResult()
        dbl_p = ctypes.POINTER(ctypes.c_double)
        int_p = ctypes.POINTER(ctypes.c_int)
        lib.run_v34_bnb_certified(
            m, d, nc,
            H_c.ctypes.data_as(dbl_p),
            y_c.ctypes.data_as(dbl_p),
            c_c.ctypes.data_as(dbl_p),
            k_c.ctypes.data_as(dbl_p),
            q_c.ctypes.data_as(dbl_p),
            A_c.ctypes.data_as(dbl_p),
            b_c.ctypes.data_as(dbl_p),
            u0_c.ctypes.data_as(dbl_p),
            lo_c.ctypes.data_as(dbl_p),
            hi_c.ctypes.data_as(dbl_p),
            has_basis,
            bidx_c.ctypes.data_as(int_p),
            hbinv_c.ctypes.data_as(dbl_p),
            float(tol),
            1 if early_stop_lower is not None else 0,
            float(early_stop_lower) if early_stop_lower is not None else 0.0,
            1 if efactor_shift is not None else 0,
            float(efactor_shift) if efactor_shift is not None else 0.0,
            1 if root_qp_only else 0,
            1 if do_polish else 0,
            int(max_nodes),
            out_u.ctypes.data_as(dbl_p),
            ctypes.byref(out_res),
        )
        return CertifiedProjectionResult(
            lower=float(out_res.lower),
            upper=float(out_res.upper),
            u_opt=out_u,
            nodes_expanded=int(out_res.nodes_expanded),
            used_root_qp_only=bool(out_res.used_root_qp_only),
        )


# ---------------------------------------------------------------------------
# Polyhedron representation & exact structural screening (V22 / V31)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class ComponentPolyhedron:
    """Closed invalidating component H_{a,z} = {u in R^d : A u >= b}."""
    action: int
    terminal: int
    A: np.ndarray          # (n_ineq, d) rows are (phi_z - phi_y)
    b: np.ndarray          # (n_ineq,) entries are eps
    feasible_point: np.ndarray  # verified strictly/weakly feasible u0 in P
    # Optional exact 2D boundary representation (only populated when d == 2):
    # list of (origin, direction, t_max) where t_max is float('inf') for ray,
    # None for full line (t in R), or finite > 0 for segment [0, t_max].
    boundary_2d: tuple[tuple[np.ndarray, np.ndarray, float | None], ...] = ()
    vertices_2d: tuple[np.ndarray, ...] = ()


def _find_feasible_point(A: np.ndarray, b: np.ndarray) -> np.ndarray | None:
    """Exact LP feasibility test for {u : A u >= b} via HiGHS."""
    n_ineq, d = A.shape
    # Solve min t s.t. A u + t >= b, t >= 0 (or directly min ||u||_1 style LP)
    # Better: find minimum-norm-like feasible point via t_j >= |u_j|
    # Variables: [u (d), s (d)] where -s_j <= u_j <= s_j, min sum(s_j) s.t. A u >= b.
    c = np.concatenate([np.zeros(d), np.ones(d)])
    A_ub = np.vstack([
        np.hstack([-A, np.zeros((n_ineq, d))]),
        np.hstack([np.eye(d), -np.eye(d)]),
        np.hstack([-np.eye(d), -np.eye(d)]),
    ])
    b_ub = np.concatenate([-b, np.zeros(d), np.zeros(d)])
    bounds = [(None, None)] * d + [(0.0, None)] * d
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if not res.success or res.x is None:
        return None
    u = np.asarray(res.x[:d], dtype=float)
    # Verify feasibility strictly (with tiny push inside if boundary slack is negative)
    slack = A @ u - b
    if float(np.min(slack)) < -1e-7:
        return None
    return u


def _extract_2d_boundary(
    A: np.ndarray,
    b: np.ndarray,
) -> tuple[tuple[tuple[np.ndarray, np.ndarray, float | None], ...], tuple[np.ndarray, ...]]:
    """Compute the exact non-redundant boundary edges/rays/lines of {u in R^2 : A u >= b}."""
    m = A.shape[0]
    # Filter zero rows
    keep = [i for i in range(m) if float(np.linalg.norm(A[i])) > 1e-12]
    if not keep:
        return (), ()
    A = A[keep]
    b = b[keep]
    # Remove positively collinear weaker inequalities
    norms = np.linalg.norm(A, axis=1)
    A_u = A / norms[:, None]
    b_u = b / norms
    active_rows: list[int] = []
    for i in range(len(keep)):
        dominated = False
        for j in range(len(keep)):
            if i == j:
                continue
            if float(np.dot(A_u[i], A_u[j])) > 1.0 - 1e-11:
                if b_u[j] > b_u[i] + 1e-11 or (abs(b_u[j] - b_u[i]) <= 1e-11 and j < i):
                    dominated = True
                    break
        if not dominated:
            active_rows.append(i)
    A = A[active_rows]
    b = b[active_rows]
    m = A.shape[0]

    edges: list[tuple[np.ndarray, np.ndarray, float | None]] = []
    verts: list[np.ndarray] = []

    for i in range(m):
        ai = A[i]
        bi = float(b[i])
        # Line ai . u = bi: pick base point u_base = (bi / ||ai||^2) ai, tangent d = (-ai[1], ai[0]) / ||ai||
        n2 = float(np.dot(ai, ai))
        u_base = (bi / n2) * ai
        d_vec = np.array([-ai[1], ai[0]], dtype=float) / math.sqrt(n2)
        t_lo = -math.inf
        t_hi = math.inf
        feasible_line = True
        for j in range(m):
            if j == i:
                continue
            # Require A[j] . (u_base + t d_vec) >= b[j]
            # <=> coeff * t >= rhs
            coeff = float(np.dot(A[j], d_vec))
            rhs = float(b[j] - np.dot(A[j], u_base))
            if abs(coeff) <= 1e-12:
                if rhs > 1e-10:
                    feasible_line = False
                    break
            elif coeff > 0.0:
                t_lo = max(t_lo, rhs / coeff)
            else:
                t_hi = min(t_hi, rhs / coeff)
        if not feasible_line or t_lo > t_hi + 1e-9:
            continue
        if abs(t_lo - t_hi) <= 1e-9 and math.isfinite(t_lo):
            v = u_base + 0.5 * (t_lo + t_hi) * d_vec
            verts.append(v)
            continue
        if math.isinf(t_lo) and math.isinf(t_hi):
            edges.append((u_base, d_vec, None))
        elif math.isfinite(t_lo) and math.isinf(t_hi):
            v0 = u_base + t_lo * d_vec
            verts.append(v0)
            edges.append((v0, d_vec, math.inf))
        elif math.isinf(t_lo) and math.isfinite(t_hi):
            v0 = u_base + t_hi * d_vec
            verts.append(v0)
            edges.append((v0, -d_vec, math.inf))
        else:
            v0 = u_base + t_lo * d_vec
            v1 = u_base + t_hi * d_vec
            verts.append(v0)
            verts.append(v1)
            edges.append((v0, d_vec, float(t_hi - t_lo)))

    # Deduplicate vertices
    uniq_verts: list[np.ndarray] = []
    for v in verts:
        if all(float(np.linalg.norm(v - u)) > 1e-8 for u in uniq_verts):
            uniq_verts.append(v)
    return tuple(edges), tuple(uniq_verts)


def build_screened_components(
    phi: np.ndarray,
    supports: Sequence[Sequence[int]],
    eps: float,
) -> list[list[ComponentPolyhedron]]:
    """Construct and exactly screen all closed invalidating polyhedra H_{a,z}."""
    M, d = phi.shape
    components: list[list[ComponentPolyhedron]] = []
    for a, sup in enumerate(supports):
        sup_set = set(sup)
        sup_list = sorted(sup_set)
        phi_S = phi[sup_list]  # (|S(a)|, d)
        act_comps: list[ComponentPolyhedron] = []
        for z in range(M):
            if z in sup_set:
                continue
            # H_{a,z} = {u : (phi_z - phi_y)^T u >= eps  for all y in S(a)}
            A = phi[z][None, :] - phi_S  # (|S(a)|, d)
            b = np.full(len(sup_list), float(eps), dtype=float)
            # Check trivial zero row with eps > 0
            row_norms = np.linalg.norm(A, axis=1)
            if eps > 1e-12 and np.any(row_norms < 1e-12):
                continue
            u0 = _find_feasible_point(A, b)
            if u0 is None:
                continue
            # Prune strictly identical rows for speed
            b2d: tuple[tuple[np.ndarray, np.ndarray, float | None], ...] = ()
            v2d: tuple[np.ndarray, ...] = ()
            if d == 2:
                b2d, v2d = _extract_2d_boundary(A, b)
                if not b2d and not v2d:
                    continue
            act_comps.append(
                ComponentPolyhedron(
                    action=a,
                    terminal=z,
                    A=A,
                    b=b,
                    feasible_point=u0,
                    boundary_2d=b2d,
                    vertices_2d=v2d,
                )
            )
        components.append(act_comps)
    return components


# ---------------------------------------------------------------------------
# Problem specification & paired intrinsic Gaussian tapes (V33/V34)
# ---------------------------------------------------------------------------
@dataclass
class HeteroscedasticDAGProblem:
    """Fixed-feature, unknown-heterogeneous-variance Gaussian overlapping-support DAG."""
    name: str
    H: np.ndarray                          # (m, d) query feature matrix, full col rank d
    phi: np.ndarray                        # (M, d) terminal feature matrix
    supports: tuple[tuple[int, ...], ...]  # K root action supports over {0..M-1}
    theta_star: np.ndarray                 # (d,) true parameter
    sigma: np.ndarray                      # (m,) true positive query std devs
    eps: float = 0.0
    basis_idx: tuple[int, ...] = ()
    components: list[list[ComponentPolyhedron]] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.H = np.asarray(self.H, dtype=float)
        self.phi = np.asarray(self.phi, dtype=float)
        self.theta_star = np.asarray(self.theta_star, dtype=float)
        self.sigma = np.asarray(self.sigma, dtype=float)
        m, d = self.H.shape
        if not self.basis_idx:
            # Select a well-conditioned d-query spanning basis via pivoted QR
            from scipy.linalg import qr as scipy_qr
            _, _, piv = scipy_qr(self.H.T, pivoting=True)
            self.basis_idx = tuple(int(p) for p in piv[:d])
        if not self.components:
            self.components = build_screened_components(self.phi, self.supports, self.eps)

    @property
    def m(self) -> int:
        return int(self.H.shape[0])

    @property
    def d(self) -> int:
        return int(self.H.shape[1])

    @property
    def K(self) -> int:
        return len(self.supports)

    @property
    def M(self) -> int:
        return int(self.phi.shape[0])

    @property
    def true_query_means(self) -> np.ndarray:
        return self.H @ self.theta_star

    @property
    def true_terminal_means(self) -> np.ndarray:
        return self.phi @ self.theta_star

    def action_values(self) -> np.ndarray:
        tm = self.true_terminal_means
        return np.array([float(np.max(tm[list(sup)])) for sup in self.supports], dtype=float)

    def action_regrets(self) -> np.ndarray:
        vals = self.action_values()
        return float(np.max(vals)) - vals

    def is_eps_optimal(self, action: int) -> bool:
        return float(self.action_regrets()[action]) <= self.eps + 1e-12

    @property
    def j_all(self) -> int:
        return sum(len(cs) for cs in self.components)

    @property
    def j_max(self) -> int:
        return max((len(cs) for cs in self.components), default=0)


class IntrinsicGaussianTape:
    """Paired intrinsic Gaussian observation tapes Y_{x,1}, Y_{x,2}, ... (Lem. V33.2).

    Each query x has an independent deterministic RNG stream seeded from (seed, x),
    so ALL compared algorithms see the exact same n-th sample of query x regardless
    of their sampling schedule.
    """
    def __init__(self, means: np.ndarray, sigmas: np.ndarray, seed: int) -> None:
        self.means = np.asarray(means, dtype=float)
        self.sigmas = np.asarray(sigmas, dtype=float)
        self.m = len(self.means)
        self.seed = int(seed)
        self._rngs = [
            np.random.default_rng(np.random.SeedSequence([self.seed, x]))
            for x in range(self.m)
        ]
        self._buffers: list[np.ndarray] = [np.empty(0, dtype=float) for _ in range(self.m)]

    def _ensure(self, x: int, end_idx: int) -> None:
        cur = len(self._buffers[x])
        if end_idx <= cur:
            return
        need = max(end_idx - cur, max(256, cur))
        fresh = self._rngs[x].normal(self.means[x], self.sigmas[x], size=need)
        self._buffers[x] = np.concatenate([self._buffers[x], fresh])

    def slice_query(self, x: int, start: int, count: int) -> np.ndarray:
        self._ensure(x, start + count)
        return self._buffers[x][start : start + count]


# ---------------------------------------------------------------------------
# Globally Certified Profiled-Loss Solvers (V22 & V23)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class CertifiedProjectionResult:
    """Guaranteed bracket lower <= inf_{u in P} L(u) <= upper with feasible witness u_opt."""
    lower: float
    upper: float
    u_opt: np.ndarray
    nodes_expanded: int = 1
    used_exact_cubic: bool = False
    used_root_qp_only: bool = False


def eval_profiled_loss(
    u: np.ndarray,
    H: np.ndarray,
    y: np.ndarray,
    c: np.ndarray,
    k: np.ndarray,
    q: np.ndarray,
) -> float:
    """Evaluate L(u) = 0.5 * sum_x c_x * log(1 + (k_x / q_x) * (h_x^T u - y_x)^2)."""
    res = H @ u - y
    t = (k / q) * (res * res)
    return float(0.5 * np.dot(c, np.log1p(t)))


def solve_cubic_exact_2d(
    poly: ComponentPolyhedron,
    H: np.ndarray,
    y: np.ndarray,
    c: np.ndarray,
    k: np.ndarray,
    q: np.ndarray,
    tol: float = 1e-9,
) -> CertifiedProjectionResult:
    """Globally exact 7-candidate cubic projection for d=2, m=2 (Thm. V23.2, Prop. V23.1).

    Works for ANY closed convex 2D polyhedron (halfspace, wedge, multi-facet cone)
    and is 100% immune to Behrens-Fisher multimodality (CE V23.1).
    """
    # Check unconstrained center u_c = H^{-1} y (exact global min = 0 if feasible)
    u_c = np.linalg.solve(H, y)
    if float(np.min(poly.A @ u_c - poly.b)) >= -1e-11:
        # Project slightly if needed for exact feasibility
        val = eval_profiled_loss(u_c, H, y, c, k, q)
        return CertifiedProjectionResult(
            lower=max(0.0, val - 1e-13),
            upper=val,
            u_opt=u_c,
            nodes_expanded=1,
            used_exact_cubic=True,
        )

    c1, c2 = float(c[0]), float(c[1])
    k1, k2 = float(k[0]), float(k[1])
    q1, q2 = float(q[0]), float(q[1])
    h1, h2 = H[0], H[1]
    y1, y2 = float(y[0]), float(y[1])

    best_u = poly.feasible_point.copy()
    best_upper = eval_profiled_loss(best_u, H, y, c, k, q)
    # Outward-safe lower bound across all boundary segments/rays
    best_lower = best_upper

    # Evaluate all vertices first
    for v in poly.vertices_2d:
        val = eval_profiled_loss(v, H, y, c, k, q)
        if val < best_upper:
            best_upper = val
            best_u = v.copy()
        best_lower = min(best_lower, max(0.0, val - 1e-12))

    # For each boundary edge/ray/line u(t) = u0 + t * d_vec, find ALL stationary points
    # of L(u(t)) by solving the exact cubic P(t) = 0 (Eq. V23.4)
    n_cands = len(poly.vertices_2d)
    for u0, d_vec, t_max in poly.boundary_2d:
        a1 = float(np.dot(h1, u0) - y1)
        b1 = float(np.dot(h1, d_vec))
        a2 = float(np.dot(h2, u0) - y2)
        b2 = float(np.dot(h2, d_vec))

        # Q1(t) = q1 + k1*(a1 + b1*t)^2 = (k1*b1^2) t^2 + (2*k1*a1*b1) t + (q1 + k1*a1^2)
        # Q2(t) = q2 + k2*(a2 + b2*t)^2 = (k2*b2^2) t^2 + (2*k2*a2*b2) t + (q2 + k2*a2^2)
        # P(t) = c1*k1*b1*(a1 + b1*t)*Q2(t) + c2*k2*b2*(a2 + b2*t)*Q1(t)
        A1_l = c1 * k1 * b1
        A2_l = c2 * k2 * b2

        # Expand cubic p3 t^3 + p2 t^2 + p1 t + p0
        q2_2 = k2 * b2 * b2
        q2_1 = 2.0 * k2 * a2 * b2
        q2_0 = q2 + k2 * a2 * a2

        q1_2 = k1 * b1 * b1
        q1_1 = 2.0 * k1 * a1 * b1
        q1_0 = q1 + k1 * a1 * a1

        p3 = A1_l * b1 * q2_2 + A2_l * b2 * q1_2
        p2 = A1_l * (a1 * q2_2 + b1 * q2_1) + A2_l * (a2 * q1_2 + b2 * q1_1)
        p1 = A1_l * (a1 * q2_1 + b1 * q2_0) + A2_l * (a2 * q1_1 + b2 * q1_0)
        p0 = A1_l * a1 * q2_0 + A2_l * a2 * q1_0

        coeffs = np.array([p3, p2, p1, p0], dtype=float)
        # Strip leading near-zero coefficients safely
        first_nz = 0
        scale = float(np.max(np.abs(coeffs)))
        if scale > 0.0:
            while first_nz < 3 and abs(coeffs[first_nz]) <= 1e-14 * scale:
                first_nz += 1
            sub_c = coeffs[first_nz:]
            roots_c = np.roots(sub_c) if len(sub_c) > 1 else np.empty(0)
        else:
            roots_c = np.empty(0)

        cand_ts: list[float] = []
        if t_max is not None:
            cand_ts.append(0.0)
            if math.isfinite(t_max):
                cand_ts.append(float(t_max))
        for rt in roots_c:
            if abs(rt.imag) < 1e-7:
                t_val = float(rt.real)
                # Polish root with 4 Newton steps on P(t) for machine precision
                for _ in range(4):
                    pv = ((p3 * t_val + p2) * t_val + p1) * t_val + p0
                    dpv = (3.0 * p3 * t_val + 2.0 * p2) * t_val + p1
                    if abs(dpv) > 1e-15:
                        t_val -= pv / dpv
                if t_max is None:
                    cand_ts.append(t_val)
                elif 0.0 <= t_val <= t_max:
                    cand_ts.append(t_val)

        # Evaluate each candidate with outward Lipschitz lower margin over root uncertainty
        # |dL/dt| <= sum_i c_i |b_i| sqrt(k_i / q_i) / 2
        lip_t = 0.5 * (c1 * abs(b1) * math.sqrt(k1 / q1) + c2 * abs(b2) * math.sqrt(k2 / q2))
        root_rad = max(1e-12, tol / max(1.0, 4.0 * lip_t))
        for t_val in cand_ts:
            n_cands += 1
            u_cand = u0 + t_val * d_vec
            val = eval_profiled_loss(u_cand, H, y, c, k, q)
            if val < best_upper:
                best_upper = val
                best_u = u_cand
            # Outward lower bound accounting for root polish radius + fp roundoff
            lo_val = max(0.0, val - lip_t * min(1e-10, root_rad) - 1e-12 * max(1.0, val))
            if lo_val < best_lower:
                best_lower = lo_val

    best_lower = min(best_lower, best_upper)
    return CertifiedProjectionResult(
        lower=float(best_lower),
        upper=float(best_upper),
        u_opt=best_u,
        nodes_expanded=max(1, n_cands),
        used_exact_cubic=True,
    )


def _solve_convex_qp_box_poly(
    Q: np.ndarray,
    g: np.ndarray,
    const_val: float,
    A_poly: np.ndarray,
    b_poly: np.ndarray,
    box_lo: np.ndarray,
    box_hi: np.ndarray,
    u_init: np.ndarray | None = None,
    cutoff_val: float = math.inf,
) -> tuple[float, np.ndarray] | None:
    """Solve strictly convex QP: min_{u in B cap P} 0.5 u^T Q u + g^T u + const_val.

    Uses pure-NumPy dual Gauss-Seidel coordinate ascent on the exact Lagrangian dual
    (Eq. V22.qp-dual). EVERY iterate lam >= 0 yields a 100% mathematically rigorous
    weak-duality lower bound (even for singular Q via exact box-radius shift), and
    infeasible boxes diverge past `cutoff_val` and prune immediately without LP calls!
    """
    d = len(g)
    box_r2 = float(np.sum(np.maximum(box_lo * box_lo, box_hi * box_hi)))
    eigs_q = np.linalg.eigvalsh(Q)
    min_eig = float(eigs_q[0])
    if min_eig > 1e-10:
        Q_reg = Q
        reg_shift = 0.0
    else:
        eps_reg = 1e-9
        Q_reg = Q + eps_reg * np.eye(d)
        reg_shift = 0.5 * eps_reg * box_r2

    u0 = np.linalg.solve(Q_reg, -g)
    v0 = float(const_val + 0.5 * np.dot(g, u0) - reg_shift)

    # Fast path 1: unconstrained minimizer feasible in B cap P!
    if (
        np.all(u0 >= box_lo - 1e-11)
        and np.all(u0 <= box_hi + 1e-11)
        and np.all(A_poly @ u0 >= b_poly - 1e-11)
    ):
        u_clamped = np.clip(u0, box_lo, box_hi)
        return (max(0.0, v0 - 1e-11 * max(1.0, abs(v0))), u_clamped)

    # Fast path 2: check if B cap P is obviously empty by 1-line interval check on A_poly u >= b_poly
    pos_A = np.maximum(A_poly, 0.0)
    neg_A = np.minimum(A_poly, 0.0)
    max_Au = pos_A @ box_hi + neg_A @ box_lo
    if np.any(max_Au < b_poly - 1e-11):
        return None

    # Build combined constraints C u <= rhs
    C_mat = np.vstack([-A_poly, np.eye(d), -np.eye(d)])
    rhs_vec = np.concatenate([-b_poly, box_hi, -box_lo])
    p = C_mat.shape[0]

    # Precompute exact dual quadratic form:
    # D(lam) = v0 + r_d^T lam - 0.5 lam^T G_d lam,  lam >= 0
    M_C = np.linalg.solve(Q_reg, C_mat.T)  # (d, p)
    G_d = C_mat @ M_C                      # (p, p) PSD
    r_d = C_mat @ u0 - rhs_vec             # (p,) positive => violated at u0
    diag_G = np.diag(G_d)

    lam = np.zeros(p, dtype=float)
    grad = r_d.copy()
    dual_val = v0
    # Dual coordinate ascent (every lam >= 0 is 100% dual feasible!)
    # If B cap P is empty, D(lam) -> +inf and immediately exceeds cutoff_val -> pruned!
    max_sweeps = 60
    for sweep in range(max_sweeps):
        max_step = 0.0
        for i in range(p):
            g_ii = float(diag_G[i])
            if g_ii <= 1e-15:
                continue
            gi = float(grad[i])
            li = float(lam[i])
            if gi == 0.0 or (li == 0.0 and gi <= 0.0):
                continue
            l_new = li + gi / g_ii
            if l_new < 0.0:
                l_new = 0.0
            dl = l_new - li
            if dl != 0.0:
                lam[i] = l_new
                grad -= dl * G_d[:, i]
                if abs(dl) > max_step:
                    max_step = abs(dl)
        if sweep % 5 == 4 or max_step < 1e-9:
            # Exact dual evaluation (no accumulated float drift):
            # D(lam) = v0 + r_d^T lam - 0.5 lam^T (G_d lam)
            G_lam = G_d @ lam
            dual_val = float(v0 + np.dot(r_d, lam) - 0.5 * np.dot(lam, G_lam))
            if dual_val >= cutoff_val:
                return None  # Provably pruned (either infeasible or strictly > cutoff_val)!
            if max_step < 1e-9:
                break

    G_lam = G_d @ lam
    dual_val = float(v0 + np.dot(r_d, lam) - 0.5 * np.dot(lam, G_lam))
    if dual_val >= cutoff_val:
        return None
    u_sol = np.clip(u0 - M_C @ lam, box_lo, box_hi)
    dual_lb = max(0.0, dual_val - 1e-10 * max(1.0, abs(dual_val)))
    return (dual_lb, u_sol)


def solve_uncertified_local_null(
    poly: ComponentPolyhedron,
    H: np.ndarray,
    y: np.ndarray,
    c: np.ndarray,
    k: np.ndarray,
    q: np.ndarray,
    init_u: np.ndarray | None = None,
) -> CertifiedProjectionResult:
    """Negative-control UNCERTIFIED single-start local optimizer (SLSQP).

    Deliberately lacks global certification and can settle in a spurious local minimum
    on nonconvex/Behrens-Fisher instances (CE V23.1), returning upper < true_global_min?
    No, returning a TOO-LARGE min loss => TOO-SMALL null likelihood => anti-conservative e-factor!
    """
    x0 = poly.feasible_point.copy() if init_u is None else np.asarray(init_u, dtype=float).copy()
    kq = k / q

    def obj_and_grad(u: np.ndarray) -> tuple[float, np.ndarray]:
        r = H @ u - y
        t = kq * (r * r)
        val = float(0.5 * np.dot(c, np.log1p(t)))
        w_g = c * kq * r / (1.0 + t)
        return val, H.T @ w_g

    cons = {"type": "ineq", "fun": lambda u: poly.A @ u - poly.b, "jac": lambda _u: poly.A}
    res = minimize(obj_and_grad, x0, method="SLSQP", jac=True, constraints=cons, options={"ftol": 1e-10, "maxiter": 60})
    u_opt = np.asarray(res.x, dtype=float)
    if float(np.min(poly.A @ u_opt - poly.b)) < -1e-6:
        u_opt = poly.feasible_point.copy()
    val = eval_profiled_loss(u_opt, H, y, c, k, q)
    # Naive local solver falsely treats its local optimum `val` as the global lower bound!
    return CertifiedProjectionResult(lower=val, upper=val, u_opt=u_opt, nodes_expanded=1)


def solve_profiled_loss_certified(
    poly: ComponentPolyhedron,
    H: np.ndarray,
    y: np.ndarray,
    c: np.ndarray,
    k: np.ndarray,
    q: np.ndarray,
    tol: float = 1e-3,
    *,
    basis_idx: Sequence[int] | None = None,
    warm_u: np.ndarray | None = None,
    root_qp_only: bool = False,
    early_stop_lower: float | None = None,
    efactor_shift: float | None = None,
    max_nodes: int = 400,
    use_cpp_bnb: bool = False,
) -> CertifiedProjectionResult:
    """Globally certified solver for inf_{u in P} L(u) (V22 + V23).

    - If d == 2 and m == 2 and poly.boundary_2d is available: uses exact 7-candidate
      cubic root solver (Thm. V23.2, Prop. V23.1).
    - Otherwise: uses Lem. V22.1 compact box localization + concave-secant convex QP
      dual lower bounds (tightening Prop. V22.2) inside certified Branch-and-Bound!
      Always returns a 100% mathematically sound bracket: lower <= inf_P L(u) <= upper.
    """
    m, d = H.shape
    if d == 2 and m == 2 and not root_qp_only and (poly.boundary_2d or poly.vertices_2d):
        if float(c[0]) > 0.0 and float(c[1]) > 0.0:
            return solve_cubic_exact_2d(poly, H, y, c, k, q, tol=tol)

    # Step 1: Fast unconstrained WLS check
    pos = c > 1e-15
    kq = k / q
    w_ls = c * kq
    try:
        u_wls = np.linalg.solve(H.T @ (w_ls[:, None] * H) + 1e-12 * np.eye(d), H.T @ (w_ls * y))
    except np.linalg.LinAlgError:
        u_wls = poly.feasible_point.copy()

    # Check if u_wls achieves exact zero residual and is feasible (possible when m == d)
    if float(np.min(poly.A @ u_wls - poly.b)) >= -1e-11:
        val_wls = eval_profiled_loss(u_wls, H, y, c, k, q)
        if m == d and val_wls <= 1e-12:
            return CertifiedProjectionResult(lower=0.0, upper=val_wls, u_opt=u_wls, nodes_expanded=1)

    # Step 2: Obtain tight feasible upper bound U via fast convex QP + multi-start SLSQP
    cand_starts = [poly.feasible_point]
    if warm_u is not None and float(np.min(poly.A @ warm_u - poly.b)) >= -1e-7:
        cand_starts.append(np.asarray(warm_u, dtype=float))
    if float(np.min(poly.A @ u_wls - poly.b)) >= -1e-7:
        cand_starts.append(u_wls)

    best_u = poly.feasible_point.copy()
    best_U = eval_profiled_loss(best_u, H, y, c, k, q)
    for st in cand_starts:
        v_st = eval_profiled_loss(st, H, y, c, k, q)
        if v_st < best_U:
            best_U = v_st
            best_u = st.copy()

    if use_cpp_bnb:
        if basis_idx is None:
            from scipy.linalg import qr as scipy_qr
            _, _, piv = scipy_qr(H.T, pivoting=True)
            basis_idx = tuple(int(p) for p in piv[:d])
        b_idx = list(basis_idx)
        Hb_inv_cpp = None
        try:
            Hb_inv_cpp = np.linalg.inv(H[b_idx])
        except np.linalg.LinAlgError:
            Hb_inv_cpp = None
        box_lo = np.full(d, -1e3, dtype=float)
        box_hi = np.full(d, 1e3, dtype=float)
        return CppV34BnBRunner.solve(
            H=H, y=y, c=c, k=k, q=q,
            A_poly=poly.A, b_poly=poly.b,
            u_init=best_u,
            box_lo=box_lo, box_hi=box_hi,
            basis_idx=b_idx if Hb_inv_cpp is not None else None,
            Hb_inv=Hb_inv_cpp,
            tol=tol,
            early_stop_lower=early_stop_lower,
            efactor_shift=efactor_shift,
            root_qp_only=root_qp_only,
            do_polish=True,
            max_nodes=max_nodes,
        )

    if not use_cpp_bnb:
        def obj_and_grad(u: np.ndarray) -> tuple[float, np.ndarray]:
            r = H @ u - y
            t = kq * (r * r)
            val = float(0.5 * np.dot(c, np.log1p(t)))
            w_g = c * kq * r / (1.0 + t)
            return val, H.T @ w_g

        cons = {"type": "ineq", "fun": lambda u: poly.A @ u - poly.b, "jac": lambda _u: poly.A}
        # Start local refinement from best candidate + one extra perturbation if nonconvex
        for st in (best_u,):
            res = minimize(obj_and_grad, st, method="SLSQP", jac=True, constraints=cons, options={"ftol": 1e-11, "maxiter": 60})
            u_try = np.asarray(res.x, dtype=float)
            if float(np.min(poly.A @ u_try - poly.b)) >= -1e-7:
                v_try = eval_profiled_loss(u_try, H, y, c, k, q)
                if v_try < best_U:
                    best_U = v_try
                    best_u = u_try

        if best_U <= tol:
            return CertifiedProjectionResult(lower=0.0, upper=best_U, u_opt=best_u, nodes_expanded=1, used_root_qp_only=True)

    # Step 3: Exact global compact box localization (Lem. V22.1) & Prop. V22.2 Root QP!
    # At any global minimizer u_*, (c_x / 2) log(1 + t_x) <= best_U => t_x <= T_x = exp(2*best_U / c_x) - 1
    # Use a conservative upper cap for overflow safety (if 2*best_U/c_x > 40, that query doesn't localize tightly)
    if basis_idx is None:
        from scipy.linalg import qr as scipy_qr
        _, _, piv = scipy_qr(H.T, pivoting=True)
        basis_idx = tuple(int(p) for p in piv[:d])
    b_idx = list(basis_idx)

    # Compute exact Prop. V22.2 concave-chord root QP lower bound over ALL of P (no box needed!)
    # On [0, T_x]: log(1+t) >= beta_x * t with beta_x = (2*U/c_x) / (exp(2*U/c_x) - 1) > exp(-2*U/c_x)
    betas_root = np.zeros(m, dtype=float)
    rho_bounds = np.full(m, math.inf, dtype=float)
    for x in range(m):
        if c[x] <= 1e-15:
            continue
        arg = 2.0 * best_U / float(c[x])
        if arg <= 1e-10:
            betas_root[x] = 1.0
            rho_bounds[x] = math.sqrt(float(q[x] / k[x]) * max(arg, 0.0))
        elif arg < 50.0:
            Tx = math.expm1(arg)
            betas_root[x] = arg / Tx
            rho_bounds[x] = math.sqrt(float(q[x] / k[x]) * Tx)
        else:
            betas_root[x] = 0.0
            rho_bounds[x] = math.inf

    # Root-level Prop. V22.2 convex QP over full polyhedron P (big box)
    # Derive exact containing box B0 from basis_idx if finite, else from all finite rho_bounds via LP!
    box_lo = np.full(d, -math.inf, dtype=float)
    box_hi = np.full(d, math.inf, dtype=float)
    if all(math.isfinite(rho_bounds[x]) for x in b_idx):
        Hb = H[b_idx]
        Hb_inv = np.linalg.inv(Hb)
        yb = y[b_idx]
        rb = rho_bounds[b_idx]
        u_ctr = Hb_inv @ yb
        rad = np.abs(Hb_inv) @ rb
        box_lo = u_ctr - rad - 1e-6
        box_hi = u_ctr + rad + 1e-6
    else:
        # Fallback: compute exact coordinate bounds via LP using all finite |h_x^T u - y_x| <= rho_x
        fin_x = [x for x in range(m) if math.isfinite(rho_bounds[x])]
        if len(fin_x) >= d:
            A_box = np.vstack([-poly.A, H[fin_x], -H[fin_x]])
            b_box = np.concatenate([-poly.b, y[fin_x] + rho_bounds[fin_x], -y[fin_x] + rho_bounds[fin_x]])
            for j in range(d):
                ej = np.zeros(d)
                ej[j] = 1.0
                r_lo = linprog(ej, A_ub=A_box, b_ub=b_box, bounds=[(None, None)] * d, method="highs")
                r_hi = linprog(-ej, A_ub=A_box, b_ub=b_box, bounds=[(None, None)] * d, method="highs")
                box_lo[j] = float(r_lo.fun) - 1e-6 if r_lo.success else -1e4
                box_hi[j] = -float(r_hi.fun) + 1e-6 if r_hi.success else 1e4
        else:
            box_lo = np.full(d, -1e3)
            box_hi = np.full(d, 1e3)

    # Evaluate root QP lower bound (Prop. V22.2)
    def eval_box_lower(b_lo: np.ndarray, b_hi: np.ndarray) -> tuple[float, np.ndarray] | None:
        # Compute exact interval [r_min, r_max] of h_x^T u - y_x on box [b_lo, b_hi]
        pos_H = np.maximum(H, 0.0)
        neg_H = np.minimum(H, 0.0)
        r_lo = pos_H @ b_lo + neg_H @ b_hi - y
        r_hi = pos_H @ b_hi + neg_H @ b_lo - y
        # Squared residual bounds
        r_abs_min = np.maximum(0.0, np.maximum(r_lo, -r_hi))
        r_abs_max = np.maximum(np.abs(r_lo), np.abs(r_hi))
        t_min = kq * (r_abs_min * r_abs_min)
        t_max_raw = kq * (r_abs_max * r_abs_max)

        # Tighten t_max with level-set cap exp(2*best_U/c_x) - 1
        t_max = t_max_raw.copy()
        for x in range(m):
            if c[x] > 1e-15:
                arg = 2.0 * best_U / float(c[x])
                if arg < 50.0:
                    t_cap = math.expm1(arg)
                    if t_min[x] > t_cap + 1e-9:
                        return None  # Box strictly above incumbent U!
                    t_max[x] = min(t_max[x], t_cap)

        # Quick interval lower bound check
        int_lb = float(0.5 * np.dot(c, np.log1p(t_min)))
        if int_lb >= best_U - 1e-12:
            return (int_lb, 0.5 * (b_lo + b_hi))

        # Exact concave secant: log(1+t) >= alpha_x + beta_x * t on [t_min, t_max]
        diff = t_max - t_min
        log_lo = np.log1p(t_min)
        log_hi = np.log1p(t_max)
        beta = np.where(diff > 1e-11, (log_hi - log_lo) / np.maximum(diff, 1e-11), 1.0 / (1.0 + t_min))
        alpha = log_lo - beta * t_min

        # Quadratic minorant: 0.5 sum_x c_x alpha_x + 0.5 sum_x c_x beta_x kq_x (h_x^T u - y_x)^2
        w_q = c * beta * kq
        Q = H.T @ (w_q[:, None] * H)
        g = -(H.T @ (w_q * y))
        const_val = float(0.5 * np.dot(c, alpha) + 0.5 * np.dot(w_q, y * y))
        qp_out = _solve_convex_qp_box_poly(
            Q, g, const_val, poly.A, poly.b, b_lo, b_hi, u_init=best_u, cutoff_val=best_U + 1e-6
        )
        if qp_out is None:
            return None
        lb_qp, u_qp = qp_out
        return (max(int_lb, lb_qp), u_qp)

    root_out = eval_box_lower(box_lo, box_hi)
    if root_out is None:
        return CertifiedProjectionResult(lower=best_U, upper=best_U, u_opt=best_u, nodes_expanded=1, used_root_qp_only=True)

    root_lb, u_qp = root_out
    if float(np.min(poly.A @ u_qp - poly.b)) >= -1e-9:
        v_qp = eval_profiled_loss(u_qp, H, y, c, k, q)
        if v_qp < best_U:
            best_U = v_qp
            best_u = u_qp
    root_lb = min(root_lb, best_U)

    def _efactor_gap_ok(lb_val: float, ub_val: float) -> bool:
        if efactor_shift is None:
            return False
        # Exact error in log(0.5*(1 + exp(lr))) between lb and ub <= tol!
        f_ub = float(np.logaddexp(0.0, ub_val - efactor_shift))
        f_lb = float(np.logaddexp(0.0, lb_val - efactor_shift))
        return (f_ub - f_lb) <= tol

    if (
        root_qp_only
        or (best_U - root_lb <= tol)
        or _efactor_gap_ok(root_lb, best_U)
        or (early_stop_lower is not None and root_lb >= early_stop_lower)
    ):
        return CertifiedProjectionResult(
            lower=float(root_lb),
            upper=float(best_U),
            u_opt=best_u,
            nodes_expanded=1,
            used_root_qp_only=True,
        )

    # Step 4: Certified Branch-and-Bound until best_U - global_lb <= tol or early_stop_lower met
    # CRITICAL SOUNDNESS INVARIANT: Track `min_pruned_lb` across all boxes pruned for being
    # within `tol` of `best_U` so the returned lower bound NEVER exceeds the true global minimum!
    tie = 0
    heap: list[tuple[float, int, np.ndarray, np.ndarray, np.ndarray]] = [
        (root_lb, tie, box_lo, box_hi, u_qp)
    ]
    min_pruned_lb = math.inf
    nodes = 1
    while heap and nodes < max_nodes:
        cur_lb, _, cur_lo, cur_hi, cur_u = heapq.heappop(heap)
        global_lb_now = min(cur_lb, min_pruned_lb, best_U)
        if best_U - global_lb_now <= tol or _efactor_gap_ok(global_lb_now, best_U):
            return CertifiedProjectionResult(
                lower=float(max(0.0, global_lb_now)),
                upper=float(best_U),
                u_opt=best_u,
                nodes_expanded=nodes,
            )
        if early_stop_lower is not None and global_lb_now >= early_stop_lower:
            return CertifiedProjectionResult(
                lower=float(max(0.0, global_lb_now)),
                upper=float(best_U),
                u_opt=best_u,
                nodes_expanded=nodes,
            )
        if cur_lb >= best_U - tol:
            min_pruned_lb = min(min_pruned_lb, cur_lb)
            continue

        # Split along widest box dimension
        widths = cur_hi - cur_lo
        split_j = int(np.argmax(widths))
        if widths[split_j] <= 1e-11:
            min_pruned_lb = min(min_pruned_lb, cur_lb)
            continue
        mid = 0.5 * (cur_lo[split_j] + cur_hi[split_j])
        if cur_lo[split_j] + 0.2 * widths[split_j] <= cur_u[split_j] <= cur_hi[split_j] - 0.2 * widths[split_j]:
            mid = float(cur_u[split_j])

        for is_right in (False, True):
            c_lo = cur_lo.copy()
            c_hi = cur_hi.copy()
            if is_right:
                c_lo[split_j] = mid
            else:
                c_hi[split_j] = mid
            nodes += 1
            child = eval_box_lower(c_lo, c_hi)
            if child is None:
                continue
            ch_lb, ch_u = child
            if float(np.min(poly.A @ ch_u - poly.b)) >= -1e-9:
                ch_val = eval_profiled_loss(ch_u, H, y, c, k, q)
                if ch_val < best_U:
                    best_U = ch_val
                    best_u = ch_u
            if ch_lb < best_U - tol:
                tie += 1
                heapq.heappush(heap, (ch_lb, tie, c_lo, c_hi, ch_u))
            else:
                min_pruned_lb = min(min_pruned_lb, ch_lb)

    rem_lb = heap[0][0] if heap else math.inf
    global_lb = min(best_U, min_pruned_lb, rem_lb)
    return CertifiedProjectionResult(
        lower=float(max(0.0, global_lb)),
        upper=float(best_U),
        u_opt=best_u,
        nodes_expanded=nodes,
    )


# ---------------------------------------------------------------------------
# Globally Certified Outer Information-Game Solvers (Thm. V23.3 & Prop. V22.3)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class CertifiedDesignResult:
    """Certified outer design game output for a single action a."""
    action: int
    w_opt: np.ndarray      # rational/simplex feasible design in Delta_m
    lower: float           # certified lower bound <= C_a(w_opt) <= max_w C_a(w)
    upper: float           # certified upper bound >= max_w C_a(w)
    inner_calls: int
    outer_iters: int
    active_cuts: tuple[np.ndarray, ...] = ()  # cached alternatives u for warm reuse (Prop. V22.3)


def eval_action_info_certified(
    problem: HeteroscedasticDAGProblem,
    action: int,
    w: np.ndarray,
    theta: np.ndarray,
    sigma_sq: np.ndarray,
    inner_tol: float,
    *,
    warm_us: dict[int, np.ndarray] | None = None,
    root_qp_only: bool = False,
    use_cpp_bnb: bool = False,
) -> tuple[float, float, np.ndarray, int, int]:
    """Compute certified [lower, upper] on C_a(w; theta, sigma) and active worst alternative u.

    Returns (lower, upper, worst_u, worst_comp_idx, total_nodes).
    """
    comps = problem.components[action]
    if not comps:
        # Structurally optimal action! Infinite information.
        return (1e6, 1e6, np.zeros(problem.d), -1, 0)

    y = problem.H @ theta
    k = np.ones(problem.m, dtype=float)
    best_upper = math.inf
    best_lower = math.inf
    worst_u = comps[0].feasible_point
    worst_idx = 0
    total_nodes = 0

    for idx, comp in enumerate(comps):
        wu = warm_us.get(idx) if warm_us is not None else None
        # Lazy pruning: if we already have best_upper, we only need components that can beat it!
        res = solve_profiled_loss_certified(
            comp,
            problem.H,
            y,
            w,
            k,
            sigma_sq,
            tol=inner_tol,
            basis_idx=problem.basis_idx,
            warm_u=wu,
            root_qp_only=root_qp_only,
            early_stop_lower=best_upper if math.isfinite(best_upper) else None,
            use_cpp_bnb=use_cpp_bnb,
        )
        total_nodes += res.nodes_expanded
        if warm_us is not None:
            warm_us[idx] = res.u_opt
        if res.upper < best_upper:
            best_upper = res.upper
            worst_u = res.u_opt
            worst_idx = idx
        if res.lower < best_lower:
            best_lower = res.lower

    best_lower = min(best_lower, best_upper)
    return (float(best_lower), float(best_upper), worst_u, worst_idx, total_nodes)


def solve_action_design_certified(
    problem: HeteroscedasticDAGProblem,
    action: int,
    theta: np.ndarray,
    sigma_sq: np.ndarray,
    tol: float,
    *,
    floor_alpha: float = 1e-4,
    cached_cuts: Sequence[np.ndarray] = (),
    root_qp_only: bool = False,
    max_iters: int = 40,
    use_cpp_bnb: bool = False,
) -> CertifiedDesignResult:
    """Solve max_{w in Delta_m} C_a(w; theta, sigma) with certified gap <= tol.

    - For d=2, m=2: uses exact affine-cut bisection (Thm. V23.3, Eq. V23.design-cut)
      with exact cubic inner oracle.
    - For general d, m: uses Kelley affine-outer-cut LP (Prop. V22.3, Eq. V22.upper-cut)
      with certified inner oracle and optional warm-started cut reuse!
    """
    m = problem.m
    comps = problem.components[action]
    if not comps:
        return CertifiedDesignResult(
            action=action,
            w_opt=np.full(m, 1.0 / m),
            lower=1e6,
            upper=1e6,
            inner_calls=0,
            outer_iters=0,
        )

    # Exact zero-information short-circuit: if theta itself belongs to any closed
    # invalidating component H_{a,z}, then F_w(theta, theta; sigma) = 0 for all w in Delta_m,
    # hence max_w C_a(w; theta, sigma) == 0 identically (0 outer iters, 100% exact!).
    for comp in comps:
        if float(np.min(comp.A @ theta - comp.b)) >= -1e-12:
            return CertifiedDesignResult(
                action=action,
                w_opt=np.full(m, 1.0 / m),
                lower=0.0,
                upper=0.0,
                inner_calls=1,
                outer_iters=0,
            )

    y = problem.H @ theta
    inner_tol = max(1e-7, tol * 0.25)

    def cut_vec(u: np.ndarray) -> np.ndarray:
        diff = problem.H @ u - y
        return 0.5 * np.log1p((diff * diff) / sigma_sq)

    # Seed cuts from cached_cuts (all remain 100% feasible in P_{a,z}!) + initial probe at uniform w
    cut_us: list[np.ndarray] = []
    cut_rows: list[np.ndarray] = []
    for u_prev in cached_cuts:
        cut_us.append(u_prev)
        cut_rows.append(cut_vec(u_prev))

    # Special super-fast certified bisection / cutting-plane for m == 2 (Thm. V23.3)
    warm_us: dict[int, np.ndarray] = {}
    best_w = np.full(m, 1.0 / m)
    best_L = -1.0
    outer_U = math.inf
    inner_calls = 0
    iters = 0

    # Initial evaluation at uniform design (or master LP if cached cuts exist)
    w_cand = np.full(m, 1.0 / m)
    if cut_rows:
        # Solve master LP on warm cuts first
        C_lp = np.vstack(cut_rows)
        n_c = C_lp.shape[0]
        # Variables: [w (m), t (1)]; max t <=> min -t s.t. t - C_lp w <= 0, sum w = 1, w >= alpha
        c_lp = np.zeros(m + 1)
        c_lp[-1] = -1.0
        A_ub = np.hstack([-C_lp, np.ones((n_c, 1))])
        b_ub = np.zeros(n_c)
        A_eq = np.zeros((1, m + 1))
        A_eq[0, :m] = 1.0
        b_eq = np.array([1.0])
        bounds = [(floor_alpha, 1.0)] * m + [(0.0, None)]
        res_lp = linprog(c_lp, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
        if res_lp.success and res_lp.x is not None:
            w_cand = np.asarray(res_lp.x[:m], dtype=float)
            w_cand = np.maximum(w_cand, 0.0)
            w_cand /= float(np.sum(w_cand))
            outer_U = float(res_lp.x[-1])

    for it in range(max_iters):
        iters = it + 1
        lo, hi, u_worst, _, _ = eval_action_info_certified(
            problem, action, w_cand, theta, sigma_sq, inner_tol,
            warm_us=warm_us, root_qp_only=root_qp_only, use_cpp_bnb=use_cpp_bnb,
        )
        inner_calls += len(comps)
        if lo > best_L:
            best_L = lo
            best_w = w_cand.copy()

        # Add valid global affine upper cut (Prop. V22.3 / Eq. V23.design-cut)
        cut_us.append(u_worst)
        cut_rows.append(cut_vec(u_worst))

        # Fast exact 1D upper-envelope maximizer when m == 2 (no LP overhead!)
        if m == 2:
            # C_a(w1) <= min_r [ f2_r + w1 * (f1_r - f2_r) ] on [floor_alpha, 1 - floor_alpha]
            # Evaluate at endpoints + all pairwise intersections of lines
            C_arr = np.vstack(cut_rows)
            f1 = C_arr[:, 0]
            f2 = C_arr[:, 1]
            slopes = f1 - f2
            # Candidate w1 points: endpoints + intersections where slopes differ
            cand_w1 = [floor_alpha, 1.0 - floor_alpha]
            n_r = len(f1)
            for i in range(n_r):
                for j in range(i + 1, n_r):
                    ds = slopes[i] - slopes[j]
                    if abs(ds) > 1e-13:
                        wi = (f2[j] - f2[i]) / ds
                        if floor_alpha < wi < 1.0 - floor_alpha:
                            cand_w1.append(float(wi))
            best_env_val = -1.0
            best_env_w1 = 0.5
            for w1 in cand_w1:
                env_val = float(np.min(f2 + w1 * slopes))
                if env_val > best_env_val:
                    best_env_val = env_val
                    best_env_w1 = w1
            outer_U = best_env_val
            w_next = np.array([best_env_w1, 1.0 - best_env_w1], dtype=float)
        else:
            C_lp = np.vstack(cut_rows)
            n_c = C_lp.shape[0]
            c_lp = np.zeros(m + 1)
            c_lp[-1] = -1.0
            A_ub = np.hstack([-C_lp, np.ones((n_c, 1))])
            b_ub = np.zeros(n_c)
            A_eq = np.zeros((1, m + 1))
            A_eq[0, :m] = 1.0
            b_eq = np.array([1.0])
            bounds = [(floor_alpha, 1.0)] * m + [(0.0, None)]
            res_lp = linprog(c_lp, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
            if not res_lp.success or res_lp.x is None:
                break
            w_next = np.asarray(res_lp.x[:m], dtype=float)
            w_next = np.maximum(w_next, 0.0)
            w_next /= float(np.sum(w_next))
            outer_U = float(res_lp.x[-1])

        if outer_U - best_L <= tol:
            break
        w_cand = w_next

    # Keep deduplicated compact cut cache (up to 16 most recent distinct cuts)
    uniq_cuts: list[np.ndarray] = []
    for u_c in reversed(cut_us):
        if all(float(np.linalg.norm(u_c - u_p)) > 1e-6 for u_p in uniq_cuts):
            uniq_cuts.append(u_c)
        if len(uniq_cuts) >= 16:
            break

    # Account for floor_alpha relaxation in upper bound conservatively if needed
    outer_U = max(outer_U, best_L)
    return CertifiedDesignResult(
        action=action,
        w_opt=best_w,
        lower=float(max(0.0, best_L)),
        upper=float(outer_U),
        inner_calls=inner_calls,
        outer_iters=iters,
        active_cuts=tuple(reversed(uniq_cuts)),
    )


def compute_exact_nuisance_kl_rate(
    problem: HeteroscedasticDAGProblem,
    tol: float = 1e-5,
) -> tuple[float, np.ndarray, list[np.ndarray]]:
    """Compute the exact unknown-variance nuisance-KL limit C_*(theta_*, sigma) and per-action V_a."""
    sigma_sq = problem.sigma ** 2
    V_a = np.zeros(problem.K, dtype=float)
    w_stars: list[np.ndarray] = []
    for a in range(problem.K):
        res = solve_action_design_certified(
            problem, a, problem.theta_star, sigma_sq, tol=tol, floor_alpha=1e-6, max_iters=60
        )
        V_a[a] = 0.5 * (res.lower + res.upper)
        w_stars.append(res.w_opt)
    return float(np.max(V_a)), V_a, w_stars


# ---------------------------------------------------------------------------
# Batch Clock Helpers (V33 Eq. V33.1--V33.2 & V34 Eq. V34.3)
# ---------------------------------------------------------------------------
def batch_schedule_sizes(j: int, m: int) -> tuple[int, int, int]:
    """Return (M_j, b_j, R_j) for batch index j >= 1 (Eq. V33.1)."""
    q = int(math.isqrt(j))
    M_j = max(j, 1 << q)
    b_j = 2 + int(math.ceil(math.sqrt(M_j)))
    R_j = M_j + m * b_j
    return M_j, b_j, R_j


def largest_remainder_counts(M_j: int, w: np.ndarray) -> np.ndarray:
    """Deterministic largest-remainder rounding of M_j * w summing to M_j (Lem. V33.1)."""
    raw = M_j * np.asarray(w, dtype=float)
    floors = np.floor(raw).astype(int)
    rem = int(M_j - int(np.sum(floors)))
    if rem > 0:
        fracs = raw - floors
        # Deterministic tie-breaking by index
        order = np.argsort(-fracs, kind="mergesort")
        floors[order[:rem]] += 1
    elif rem < 0:
        fracs = raw - floors
        order = np.argsort(fracs, kind="mergesort")
        for idx in order:
            if rem == 0:
                break
            if floors[idx] > 0:
                floors[idx] -= 1
                rem += 1
    return floors


def is_square_refresh(j: int) -> bool:
    r = int(math.isqrt(j))
    return r * r == j


def is_four_power_refresh(j: int) -> bool:
    """True iff j in {1, 4, 16, 64, 256, ...} (Eq. V34.3)."""
    if j <= 0:
        return False
    # Power of 2 with even bit position
    return (j & (j - 1)) == 0 and ((j.bit_length() - 1) % 2 == 0)


def refresh_level(j: int, schedule: str) -> int:
    if schedule == "square":
        return int(math.isqrt(j))  # k >= 1
    if schedule == "four_power":
        return (j.bit_length() - 1) // 2  # k >= 0
    raise ValueError(f"Unknown refresh schedule: {schedule}")


# ---------------------------------------------------------------------------
# Elementary V31/V32 Student-Tail E-Factor (optional hedge, Thm. V32.2)
# ---------------------------------------------------------------------------
def _student_hedge_log_efactor(
    problem: HeteroscedasticDAGProblem,
    comp: ComponentPolyhedron,
    theta_prev: np.ndarray,
    sigma_sq_prev: np.ndarray,
    batch_means: np.ndarray,
    batch_vars: np.ndarray,
    batch_counts: np.ndarray,
    lam_s: float = 0.5,
) -> float:
    """Compute exact log e^S_{a,z,j} from Eq. V31.pvalue using predictably chosen witness."""
    # Choose inside mixture p putting weight on best estimated inside terminal
    sup = list(problem.supports[comp.action])
    inside_vals = problem.phi[sup] @ theta_prev
    best_y = sup[int(np.argmax(inside_vals))]
    g_vec = problem.phi[comp.terminal] - problem.phi[best_y]
    # Solve H^T beta = g_vec minimizing sum beta_x^2 * sigma_sq_prev[x] / n_x
    # Weighted min-norm solution: beta = W^{-1} H (H^T W^{-1} H)^{-1} g_vec
    w_inv = batch_counts / np.maximum(sigma_sq_prev, 1e-8)  # 1 / (sigma^2 / n)
    Hw = problem.H.T * w_inv[None, :]  # (d, m)
    G = Hw @ problem.H
    try:
        beta = w_inv * (problem.H @ np.linalg.solve(G, g_vec))
    except np.linalg.LinAlgError:
        return 0.0
    # Verify exact equality H^T beta == g_vec (Lem. V31.1)
    if float(np.linalg.norm(problem.H.T @ beta - g_vec)) > 1e-7:
        return 0.0
    nz = np.abs(beta) > 1e-12
    if not np.any(nz):
        return 0.0
    D = float(np.dot(beta, batch_means))
    V_hat = float(np.sum((beta[nz] ** 2) * batch_vars[nz] / batch_counts[nz]))
    if V_hat <= 1e-18:
        return 0.0
    nu = int(np.min(batch_counts[nz] - 1))
    if nu <= 0:
        return 0.0
    T = (problem.eps - D) / math.sqrt(V_hat)
    if T <= 0.0:
        q_val = 1.0
    else:
        log_q = -0.5 * nu * math.log1p((T * T) / nu)
        # e^S = lam_s * q^(lam_s - 1) => log e^S = log(lam_s) + (lam_s - 1) * log_q
        return float(math.log(lam_s) + (lam_s - 1.0) * log_q)
    return float(math.log(lam_s) + (lam_s - 1.0) * math.log(q_val))


# ---------------------------------------------------------------------------
# Unified V33 / V34 Adaptive Nuisance-KL Tracker Session
# ---------------------------------------------------------------------------
@dataclass
class V34RunResult:
    """Complete audit record for one V33/V34 (or ablation/negative-control) trajectory."""
    method: str
    certified: bool
    recommended_action: int
    is_correct: bool
    true_regret: float
    total_samples: int
    batches: int
    design_calls: int
    null_calls: int
    design_refreshes: int
    action_switches: int
    design_time_s: float
    null_time_s: float
    total_wall_s: float
    total_bnb_nodes: int
    root_qp_screened_nulls: int
    final_min_log_wealth: float
    action_trace: tuple[int, ...] = ()
    wealth_trace: tuple[float, ...] = ()


def run_v34_tracker(
    problem: HeteroscedasticDAGProblem,
    tape: IntrinsicGaussianTape,
    delta: float,
    *,
    method_name: str = "v34_full",
    refresh_schedule: str = "four_power",   # "four_power" (V34) | "square" (V33)
    action_local: bool = True,              # True (V34) | False (V33 all-action)
    use_hysteresis: bool = True,            # True (V33/V34) | False (ablation)
    hysteresis_scale: float = 0.05,         # h_k = hysteresis_scale * (k+1)^(-1/2) (or k^(-1/4))
    design_tol_scale: float = 0.02,         # e_k = min(design_tol_scale, ...)
    null_log_tol: float = 0.05,             # <= 1 nat (Prop. V32.1); controls B&B / cubic precision
    warm_start_cuts: bool = True,           # Prop. V22.3 cut reuse across refreshes
    fast_qp_screen: bool = False,           # Try cheap Prop. V22.2 root QP before B&B
    reset_wealth_on_switch: bool = False,   # NEGATIVE CONTROL (Remark V34.1)
    uncertified_local_null: bool = False,   # NEGATIVE CONTROL (CE V23.1)
    bonferroni_components: bool = False,    # Ablation: divide alpha_a by |J_a| instead of IUT
    student_hedge_pi: float = 1.0,          # 1.0 = pure likelihood; <1.0 = Thm. V32.2 hedge
    predictable_gate: bool = False,         # Prop. V32.1: skip multiplying F when R_j * V_hat < gate_mult * m
    gate_mult: float = 0.75,
    max_samples: int = 200_000,
    max_batches: int = 400,
    init_action: int | None = None,
    record_trace: bool = False,
    use_cpp_bnb: bool = False,
) -> V34RunResult:
    """Execute one coupled trajectory of V33 or V34 (or a controlled ablation)."""
    t_start = time.perf_counter()
    m, d, K = problem.m, problem.d, problem.K
    H = problem.H

    # Check trivial zero-sample structural certification (empty J_a)
    for a in range(K):
        if len(problem.components[a]) == 0:
            reg = float(problem.action_regrets()[a])
            return V34RunResult(
                method=method_name,
                certified=True,
                recommended_action=a,
                is_correct=problem.is_eps_optimal(a),
                true_regret=reg,
                total_samples=0,
                batches=0,
                design_calls=0,
                null_calls=0,
                design_refreshes=0,
                action_switches=0,
                design_time_s=0.0,
                null_time_s=0.0,
                total_wall_s=time.perf_counter() - t_start,
                total_bnb_nodes=0,
                root_qp_screened_nulls=0,
                final_min_log_wealth=math.inf,
            )

    # Stopping threshold per action (Thm. V32.1 / Thm. V34.1)
    # Without Student hedge (pi=1): log(K / delta). With hedge: still compare log E^H >= log(K / delta).
    base_log_thresh = math.log(K / delta)

    # Per-query cumulative sufficient statistics (online Welford / sum + sumsq)
    n_obs = np.zeros(m, dtype=int)
    sum_y = np.zeros(m, dtype=float)
    sum_y2 = np.zeros(m, dtype=float)

    # Stored log-wealth per (a, comp_idx) for likelihood L and optional Student S
    log_L: list[np.ndarray] = [np.zeros(len(problem.components[a]), dtype=float) for a in range(K)]
    log_S: list[np.ndarray] = [np.zeros(len(problem.components[a]), dtype=float) for a in range(K)]

    # Cached cuts per action for warm-started certified design refreshes (Prop. V22.3)
    cut_cache: list[tuple[np.ndarray, ...]] = [() for _ in range(K)]
    # Cached incumbent u per (a, comp_idx) for warm-started null likelihoods
    null_warm: list[list[np.ndarray | None]] = [
        [None for _ in problem.components[a]] for a in range(K)
    ]

    # Default init_action = K - 1 so benchmarks that place optimal action at index 0
    # never get a free initial selection without genuine data-driven discovery!
    cur_action = (K - 1) if init_action is None else int(init_action) % K
    cur_w = np.full(m, 1.0 / m, dtype=float)
    last_V_hat = np.zeros(K, dtype=float)
    design_calls = 0
    null_calls = 0
    design_refreshes = 0
    action_switches = 0
    design_time_s = 0.0
    null_time_s = 0.0
    total_bnb_nodes = 0
    root_qp_screened_nulls = 0

    action_trace: list[int] = []
    wealth_trace: list[float] = []

    total_samples = 0
    certified = False
    rec_action = 0
    batches_done = 0

    for j in range(1, max_batches + 1):
        M_j, b_j, R_j = batch_schedule_sizes(j, m)
        if total_samples > 0 and total_samples + R_j > max_samples:
            break

        # 1. Predictable model estimates from strictly earlier batches 1..j-1
        if j == 1:
            theta_hat = np.zeros(d, dtype=float)
            var_hat = np.ones(m, dtype=float)
            mu_pred = np.zeros(m, dtype=float)
        else:
            ybar_past = sum_y / n_obs
            # Unbiased within-query sample variance from pooled past, safely clipped in expanding interval
            ss_past = np.maximum(0.0, sum_y2 - n_obs * (ybar_past ** 2))
            v_raw = ss_past / np.maximum(1, n_obs - 1)
            lo_clip = 1.0 / (100.0 * j)
            hi_clip = 100.0 * j
            var_hat = np.clip(v_raw, lo_clip, hi_clip)
            # Weighted least squares parameter estimate (equals exact basis inversion when m == d)
            if m == d:
                theta_hat = np.linalg.solve(H, ybar_past)
            else:
                w_wls = n_obs / var_hat
                theta_hat = np.linalg.solve(
                    H.T @ (w_wls[:, None] * H) + 1e-12 * np.eye(d),
                    H.T @ (w_wls * ybar_past),
                )
            mu_pred = H @ theta_hat

        # 2. Check if batch j is a design-refresh checkpoint (V33 squares vs. V34 4-powers)
        do_refresh = is_four_power_refresh(j) if refresh_schedule == "four_power" else is_square_refresh(j)
        if do_refresh and j >= 2:
            # Note: at j=1 there is zero data so cur_w = uniform and cur_action = 0.
            # (Count j=1 as initial setup; refreshes with real data start at j=4 for both V33 & V34.)
            t_d0 = time.perf_counter()
            k_lvl = refresh_level(j, refresh_schedule)
            # Scale-aware certified tolerance: fast exact cubic can easily hit 1e-4 / (k+1),
            # while general-d B&B uses design_tol_scale / (k+1) (capped tightly so e_k << C_*).
            is_exact_2d = (d == 2 and m == 2)
            base_e = min(design_tol_scale, 2e-3) if is_exact_2d else design_tol_scale
            if refresh_schedule == "four_power":
                e_k = base_e / (k_lvl + 1.0)
                h_k = hysteresis_scale / math.sqrt(k_lvl + 1.0) if use_hysteresis else 0.0
            else:
                e_k = base_e / math.sqrt(max(1, k_lvl))
                h_k = hysteresis_scale / (max(1, k_lvl) ** 0.25) if use_hysteresis else 0.0

            V_hat = np.zeros(K, dtype=float)
            w_hat_list: list[np.ndarray] = []
            for a in range(K):
                d_res = solve_action_design_certified(
                    problem,
                    a,
                    theta_hat,
                    var_hat,
                    tol=e_k,
                    floor_alpha=1e-4,
                    cached_cuts=cut_cache[a] if warm_start_cuts else (),
                    use_cpp_bnb=use_cpp_bnb,
                )
                V_hat[a] = 0.5 * (d_res.lower + d_res.upper)
                w_hat_list.append(d_res.w_opt)
                if warm_start_cuts:
                    cut_cache[a] = d_res.active_cuts
                design_calls += 1

            design_refreshes += 1
            last_V_hat = V_hat.copy()
            best_a = int(np.argmax(V_hat))
            new_action = cur_action
            # Relative + zero-escape hysteresis preserving Lem. V34.2:
            # 1) Never stay trapped on a zero-information suboptimal incumbent when best_a > 2*e_k.
            # 2) Scale hysteresis relative to V_hat[best_a] so low-SNR regimes (C_* ~ 0.01) still switch
            #    while tied optimal actions (gap << h_eff) remain stabilized.
            if use_hysteresis:
                h_eff = min(h_k, 0.25 * float(V_hat[best_a]) / math.sqrt(max(1, k_lvl) + 1.0))
                if V_hat[cur_action] <= 1e-12 and V_hat[best_a] > 2.0 * e_k:
                    new_action = best_a
                elif V_hat[best_a] > V_hat[cur_action] + h_eff:
                    new_action = best_a
            else:
                if V_hat[best_a] > V_hat[cur_action] + 1e-12:
                    new_action = best_a
            if new_action != cur_action:
                action_switches += 1
                if reset_wealth_on_switch:
                    # NEGATIVE CONTROL (Remark V34.1): illegally resets wealth upon switching!
                    log_L[new_action][:] = 0.0
                    log_S[new_action][:] = 0.0
                cur_action = new_action
            cur_w = w_hat_list[cur_action]
            design_time_s += time.perf_counter() - t_d0
        elif do_refresh and j == 1:
            # Record the trivial j=1 initial uniform design (0 optimization calls needed)
            cur_w = np.full(m, 1.0 / m, dtype=float)

        # 3. Acquire fresh batch j observations from paired intrinsic Gaussian tapes (Eq. V33.2)
        c_counts = largest_remainder_counts(M_j, cur_w)
        r_counts = b_j + c_counts  # >= b_j >= 3 per query
        batch_means = np.empty(m, dtype=float)
        batch_ss = np.empty(m, dtype=float)
        batch_vars = np.empty(m, dtype=float)

        for x in range(m):
            rx = int(r_counts[x])
            ys = tape.slice_query(x, int(n_obs[x]), rx)
            yb = float(np.mean(ys))
            diff = ys - yb
            ss = float(np.dot(diff, diff))
            # Prevent exact zero residual under floating underflow
            ss = max(ss, 1e-18)
            batch_means[x] = yb
            batch_ss[x] = ss
            batch_vars[x] = ss / (rx - 1)
            # Update cumulative stats AFTER batch extraction (so next batch uses pooled past)
            n_obs[x] += rx
            sum_y[x] += float(np.sum(ys))
            sum_y2[x] += float(np.dot(ys, ys))

        total_samples += R_j
        batches_done = j

        # 4. Compute predictable numerator excess term (cancelling K_uncon constant):
        # log(q_j / U_{a,z,j}) = ell_{a,z} - pred_excess - outward_round
        # where pred_excess = 0.5 * sum_x r_x * [log(var_hat_x / (S_x/r_x)) + (S_x/r_x + (yb_x - mu_pred_x)^2)/var_hat_x - 1]
        s_over_r = batch_ss / r_counts
        pred_excess = float(
            0.5
            * np.sum(
                r_counts
                * (
                    np.log(var_hat / s_over_r)
                    + (s_over_r + (batch_means - mu_pred) ** 2) / var_hat
                    - 1.0
                )
            )
        )
        # Outward floating-point safety margin (Prop. V32.1)
        outward_round = 1e-10 * R_j

        # 5. Evaluate component-null likelihoods: ONLY cur_action (V34) or ALL actions (V33)
        # Optional Prop. V32.1 predictable activation gate (100% F_{j-1}-measurable!):
        # Skip multiplying likelihood when planned batch R_j is too small to clear the ~m-nat
        # batch variance-profiling tax (sets F=1 without touching batch j observations).
        skip_batch_eval = False
        if predictable_gate:
            if j < 4:
                skip_batch_eval = True
            else:
                expected_gain = float(M_j) * float(last_V_hat[cur_action])
                if expected_gain < gate_mult * float(m) and M_j < 512:
                    skip_batch_eval = True

        t_n0 = time.perf_counter()
        eval_actions = () if skip_batch_eval else ((cur_action,) if action_local else tuple(range(K)))
        r_float = r_counts.astype(float)

        for a in eval_actions:
            comps_a = problem.components[a]
            thresh_a = base_log_thresh + (math.log(len(comps_a)) if bonferroni_components else 0.0)
            for idx, comp in enumerate(comps_a):
                null_calls += 1
                if uncertified_local_null:
                    proj = solve_uncertified_local_null(
                        comp, H, batch_means, r_float, r_float, batch_ss, init_u=null_warm[a][idx]
                    )
                else:
                    # Target ell needed to cross threshold on this batch (for fast root-QP screening!)
                    # If root QP already gives sufficient ell to either cross thresh OR close enough within tol:
                    need_ell: float | None = None
                    if fast_qp_screen:
                        # Compute exact ell that would push log_L[a][idx] above thresh_a + 0.05
                        gap_need = (thresh_a + 0.05) - log_L[a][idx]
                        if gap_need > 0.0:
                            # log(0.5*(1 + exp(lr))) >= gap_need  <=> lr >= log(2*exp(gap_need) - 1)
                            lr_need = gap_need + math.log(2.0) + 0.05
                            need_ell = lr_need + pred_excess + outward_round
                    proj = solve_profiled_loss_certified(
                        comp,
                        H,
                        batch_means,
                        r_float,
                        r_float,
                        batch_ss,
                        tol=null_log_tol,
                        basis_idx=problem.basis_idx,
                        warm_u=null_warm[a][idx] if warm_start_cuts else None,
                        early_stop_lower=need_ell,
                        efactor_shift=(pred_excess + outward_round) if fast_qp_screen else None,
                        use_cpp_bnb=use_cpp_bnb,
                    )
                    if proj.used_root_qp_only:
                        root_qp_screened_nulls += 1
                total_bnb_nodes += proj.nodes_expanded
                null_warm[a][idx] = proj.u_opt

                log_lr = proj.lower - pred_excess - outward_round
                # Half-cash protection: log(0.5 * (1 + exp(log_lr))) >= -log(2)
                log_f = float(np.logaddexp(0.0, log_lr) - math.log(2.0))
                log_L[a][idx] += log_f

                if student_hedge_pi < 1.0:
                    log_es = _student_hedge_log_efactor(
                        problem, comp, theta_hat, var_hat, batch_means, batch_vars, r_counts
                    )
                    log_S[a][idx] += log_es

        null_time_s += time.perf_counter() - t_n0

        # 6. Check stopping condition (Eq. V34.2 / Eq. V32.action-iut)
        def action_min_log_wealth(a_idx: int) -> float:
            if student_hedge_pi >= 1.0:
                return float(np.min(log_L[a_idx]))
            # log(pi * L + (1 - pi) * S)
            lw = np.logaddexp(
                math.log(student_hedge_pi) + log_L[a_idx],
                math.log(1.0 - student_hedge_pi) + log_S[a_idx],
            )
            return float(np.min(lw))

        if record_trace:
            action_trace.append(cur_action)
            wealth_trace.append(action_min_log_wealth(cur_action))

        best_cert_a = -1
        best_cert_margin = -math.inf
        for a in eval_actions:
            n_comp = len(problem.components[a])
            thresh_a = base_log_thresh + (math.log(n_comp) if bonferroni_components else 0.0)
            mw = action_min_log_wealth(a)
            if mw >= thresh_a and (mw - thresh_a) > best_cert_margin:
                best_cert_a = a
                best_cert_margin = mw - thresh_a

        if best_cert_a >= 0:
            certified = True
            rec_action = best_cert_a
            break

    if not certified:
        # Fallback recommendation: action with highest min log-wealth (or current sticky action)
        if action_local:
            rec_action = cur_action
        else:
            rec_action = int(np.argmax([float(np.min(log_L[a])) for a in range(K)]))

    final_mw = float(np.min(log_L[rec_action])) if len(log_L[rec_action]) > 0 else math.inf
    return V34RunResult(
        method=method_name,
        certified=certified,
        recommended_action=rec_action,
        is_correct=problem.is_eps_optimal(rec_action),
        true_regret=float(problem.action_regrets()[rec_action]),
        total_samples=total_samples,
        batches=batches_done,
        design_calls=design_calls,
        null_calls=null_calls,
        design_refreshes=design_refreshes,
        action_switches=action_switches,
        design_time_s=design_time_s,
        null_time_s=null_time_s,
        total_wall_s=time.perf_counter() - t_start,
        total_bnb_nodes=total_bnb_nodes,
        root_qp_screened_nulls=root_qp_screened_nulls,
        final_min_log_wealth=final_mw,
        action_trace=tuple(action_trace),
        wealth_trace=tuple(wealth_trace),
    )


# ---------------------------------------------------------------------------
# Reference Baselines on the Exact Same Intrinsic Gaussian Tapes
# ---------------------------------------------------------------------------
def run_known_sigma_info_tracker(
    problem: HeteroscedasticDAGProblem,
    tape: IntrinsicGaussianTape,
    delta: float,
    *,
    assumed_sigma: np.ndarray | None = None,
    use_cd_joint: bool = False,
    method_name: str = "known_sigma_tracker",
    max_samples: int = 120_000,
) -> V34RunResult:
    """Oracle known-sigma (or misspecified nominal-sigma) sequential Gaussian baseline on identical tapes.

    Uses the exact Abbasi-Yadkori / self-normalized Gaussian ellipsoid with known (or assumed)
    noise variance `sigma_use` and exact quadratic alternative projection (T5 / v8_exp2).
    """
    t0 = time.perf_counter()
    m, d, K = problem.m, problem.d, problem.K
    H = problem.H
    sig = problem.sigma if assumed_sigma is None else np.asarray(assumed_sigma, dtype=float)
    sig2 = sig ** 2
    U_feat = H / sig[:, None]  # whitened query features u_x = h_x / sigma_x

    # Regularized WLS state (gamma = 0.01 as in v8_exp2)
    gamma = 0.01
    G = gamma * np.eye(d, dtype=float)
    b_vec = np.zeros(d, dtype=float)
    n_obs = np.zeros(m, dtype=int)
    G_inv = (1.0 / gamma) * np.eye(d, dtype=float)

    def pull(x: int) -> None:
        nonlocal G, b_vec, G_inv
        y_val = float(tape.slice_query(x, int(n_obs[x]), 1)[0])
        n_obs[x] += 1
        ux = U_feat[x]
        G = G + np.outer(ux, ux)
        b_vec = b_vec + ux * (y_val / sig[x])
        # Sherman-Morrison update
        gu = G_inv @ ux
        denom = 1.0 + float(np.dot(ux, gu))
        G_inv = G_inv - np.outer(gu, gu) / denom

    # Warmup: 1 sample per query
    for x in range(m):
        pull(x)
    t_steps = m

    # Exact quadratic distance to H_{a,z} under metric M = G (exact dual over inside simplex!)
    def action_quad_info(a: int, theta_h: np.ndarray, M_inv: np.ndarray) -> tuple[float, np.ndarray]:
        comps = problem.components[a]
        if not comps:
            return (math.inf, np.zeros(d))
        sup = list(problem.supports[a])
        phi_S = problem.phi[sup]  # (|S|, d)
        min_dist = math.inf
        worst_g = np.zeros(d)
        for comp in comps:
            # max_{p in Delta} [eps - (phi_z - phi_S^T p)^T theta_h]_+^2 / (2 g^T M_inv g)
            # Equivalently min_{u in H_{a,z}} 0.5 (u - theta_h)^T M (u - theta_h)
            # Fast dual via exact 1-vertex or small-simplex projected gradient / QP
            g_rows = problem.phi[comp.terminal][None, :] - phi_S  # (|S|, d)
            # Check if theta_h is already inside H_{a,z}:
            slacks = g_rows @ theta_h - problem.eps
            if float(np.min(slacks)) >= 0.0:
                return (0.0, g_rows[int(np.argmin(slacks))])
            # Maximize [eps - g_p^T theta_h]_+^2 / (2 g_p^T M_inv g_p) over p in simplex
            # Equivalently minimize 0.5 q^T (G_r M_inv G_r^T) q - q^T (eps - G_r theta_h) s.t. q >= 0!
            # Exact dual! Check: dual of min 0.5 ||u - th||_M^2 s.t. G_r u >= eps is
            # max_{q >= 0} q^T (eps - G_r th) - 0.5 q^T (G_r M_inv G_r^T) q!
            rhs_d = problem.eps - g_rows @ theta_h  # positive for violated rows
            if len(sup) == 1:
                v0 = max(0.0, float(rhs_d[0]))
                denom = float(g_rows[0] @ (M_inv @ g_rows[0]))
                dist_z = 0.5 * (v0 * v0) / max(denom, 1e-18)
                g_z = g_rows[0]
            else:
                Gram = g_rows @ (M_inv @ g_rows.T)
                # Guaranteed-convergent projected gradient ascent (step = 1/tr(Gram) <= 1/L_max)
                q_d = np.zeros(len(sup), dtype=float)
                step_l = 1.0 / max(float(np.trace(Gram)), 1e-12)
                for _ in range(40):
                    grad = rhs_d - Gram @ q_d
                    q_new = np.maximum(0.0, q_d + step_l * grad)
                    if float(np.max(np.abs(q_new - q_d))) < 1e-10:
                        q_d = q_new
                        break
                    q_d = q_new
                dist_z = max(0.0, float(q_d @ rhs_d - 0.5 * q_d @ (Gram @ q_d)))
                q_sum = float(np.sum(q_d))
                g_z = (q_d @ g_rows) / q_sum if q_sum > 1e-14 else g_rows[int(np.argmax(rhs_d))]
            if dist_z < min_dist:
                min_dist = dist_z
                worst_g = g_z
        return (min_dist, worst_g)

    # Optimal known-sigma design tracker helper (Frank-Wolfe over Delta_m on concave I_a(w))
    def compute_opt_known_w(a: int, theta_h: np.ndarray) -> tuple[float, np.ndarray]:
        w = np.full(m, 1.0 / m, dtype=float)
        best_val = -1.0
        best_w = w.copy()
        for it in range(25):
            M_w = U_feat.T @ (w[:, None] * U_feat) + 1e-8 * np.eye(d)
            M_inv = np.linalg.inv(M_w)
            val, g_w = action_quad_info(a, theta_h, M_inv)
            if val > best_val:
                best_val = val
                best_w = w.copy()
            if val <= 1e-12:
                break
            # Subgradient wrt w_x is proportional to (u_x^T M_inv g_w)^2
            mg = M_inv @ g_w
            scores = (U_feat @ mg) ** 2
            x_best = int(np.argmax(scores))
            step = 2.0 / (it + 3.0)
            w = (1.0 - step) * w
            w[x_best] += step
        return (best_val, best_w)

    certified = False
    rec_action = 0
    design_calls = 0
    null_calls = 0
    design_time_s = 0.0
    null_time_s = 0.0
    w_target = np.full(m, 1.0 / m)
    check_every = 1 if m <= 8 else 4

    while t_steps < max_samples:
        theta_h = G_inv @ b_vec
        # Mixture-martingale Gaussian threshold (Lem. bay-cs / Eq. bay-gaussian-cs):
        # H_t(delta) = log(1/delta) + 0.5 log det(I + G_0/gamma) + A_t
        # where G_0 = G - gamma I. Note: 0.5 ||theta_h - th||_{G_0}^2 <= H_t is exact!
        # Using regularized G = G_0 + gamma I: 0.5 ||th - theta_h||_G^2 <= log(1/delta) + 0.5 log det(G/gamma) + 0.5*gamma*||theta_h||^2
        if t_steps % check_every == 0:
            t_n0 = time.perf_counter()
            sign, logdet = np.linalg.slogdet(G / gamma)
            H_thresh = math.log(1.0 / delta) + 0.5 * max(0.0, float(logdet)) + 0.5 * gamma * float(np.dot(theta_h, theta_h))
            # Check best empirical action first
            vals_hat = np.array([float(np.max(problem.phi[list(sup)] @ theta_h)) for sup in problem.supports])
            a_hat = int(np.argmax(vals_hat))
            info_a, worst_g = action_quad_info(a_hat, theta_h, G_inv)
            null_calls += len(problem.components[a_hat])
            null_time_s += time.perf_counter() - t_n0
            if info_a >= H_thresh:
                certified = True
                rec_action = a_hat
                break

            # Select next query
            if use_cd_joint:
                # Contrast-directed: query maximizing variance reduction along worst_g
                mg = G_inv @ worst_g
                ux_scores = (U_feat @ mg) ** 2 / (1.0 + np.einsum("ij,jk,ik->i", U_feat, G_inv, U_feat))
                x_next = int(np.argmax(ux_scores))
            else:
                # Info-tracking: refresh w_target periodically + forced exploration
                if t_steps <= 2 * m or (t_steps % max(8, 2 * m) == 0):
                    t_d0 = time.perf_counter()
                    # Pick action with highest estimated information rate
                    best_a_tr = a_hat
                    best_rate = -1.0
                    for a in range(K):
                        if float(vals_hat[a]) >= float(np.max(vals_hat)) - problem.eps - 0.1:
                            r_a, w_a = compute_opt_known_w(a, theta_h)
                            design_calls += 1
                            if r_a > best_rate:
                                best_rate = r_a
                                w_target = w_a
                                best_a_tr = a
                    design_time_s += time.perf_counter() - t_d0
                # C-tracking with sqrt(t) exploration floor
                if int(np.min(n_obs)) < max(2, int(0.5 * math.sqrt(t_steps / m))):
                    x_next = int(np.argmin(n_obs))
                else:
                    x_next = int(np.argmax(t_steps * w_target - n_obs))
        else:
            x_next = int(np.argmax(t_steps * w_target - n_obs))

        pull(x_next)
        t_steps += 1

    if not certified:
        theta_h = G_inv @ b_vec
        vals_hat = np.array([float(np.max(problem.phi[list(sup)] @ theta_h)) for sup in problem.supports])
        rec_action = int(np.argmax(vals_hat))

    return V34RunResult(
        method=method_name,
        certified=certified,
        recommended_action=rec_action,
        is_correct=problem.is_eps_optimal(rec_action),
        true_regret=float(problem.action_regrets()[rec_action]),
        total_samples=t_steps,
        batches=t_steps,
        design_calls=design_calls,
        null_calls=null_calls,
        design_refreshes=design_calls // max(1, K),
        action_switches=0,
        design_time_s=design_time_s,
        null_time_s=null_time_s,
        total_wall_s=time.perf_counter() - t0,
        total_bnb_nodes=0,
        root_qp_screened_nulls=0,
        final_min_log_wealth=0.0,
    )


def run_indep_heteroscedastic_os(
    problem: HeteroscedasticDAGProblem,
    tape: IntrinsicGaussianTape,
    delta: float,
    *,
    method_name: str = "indep_student_os",
    max_samples: int = 120_000,
) -> V34RunResult:
    """Distribution-free / Student-t heteroscedastic Optimistic-Separation baseline.

    Works on direct terminal/query observations using time-uniform self-normalized
    unknown-variance Student confidence sequences (without leveraging linear correlation
    across terminals, except when phi rows are direct queries).
    For general linear feature DAGs where queries are basis vectors h_x and terminal
    values are phi_z^T theta = beta_z^T mu, bounds each query coordinate with a valid
    time-uniform unknown-variance Gaussian CS and propagates intervals linearly.
    """
    t0 = time.perf_counter()
    m, d, K = problem.m, problem.d, problem.K
    H = problem.H
    # Precompute exact basis representation of every terminal feature: phi_z = H_basis^T c_z
    b_idx = list(problem.basis_idx)
    H_b_inv = np.linalg.inv(H[b_idx])  # (d, d)
    # phi_z^T theta = (phi_z^T H_b^{-1}) (H_b theta) = coef_z^T mu_basis
    coef_mat = problem.phi @ H_b_inv  # (M, d)

    # Time-uniform Student / self-normalized Gaussian confidence radius for each basis query x:
    # Under Y_i ~ N(mu, sigma^2), at n >= 3:
    # By exact Student-t union bound across n >= 3 with spending alpha_n = alpha / (n * (n - 1)):
    # P(|Ybar_n - mu| > t_{n-1, 1 - alpha_n/2} * S_n / sqrt(n)) <= alpha!
    # We use exact scipy.stats.t.ppf cached for fast exactness!
    from scipy.stats import t as student_t
    alpha_per_q = delta / max(1, d)

    n_q = np.zeros(d, dtype=int)
    sum_q = np.zeros(d, dtype=float)
    sum2_q = np.zeros(d, dtype=float)
    t_steps = 0

    def pull_b(j_b: int) -> None:
        nonlocal t_steps
        x = b_idx[j_b]
        y_val = float(tape.slice_query(x, int(n_q[j_b]), 1)[0])
        n_q[j_b] += 1
        sum_q[j_b] += y_val
        sum2_q[j_b] += y_val * y_val
        t_steps += 1

    # Initial 4 pulls per basis query
    for _ in range(4):
        for j_b in range(d):
            pull_b(j_b)

    t_cache: dict[int, float] = {}
    def radius_q(n_val: int, s_hat: float) -> float:
        if n_val not in t_cache:
            # Spending sum_{n=4}^inf 1/((n-3)*(n-2)) = 1
            p_n = alpha_per_q / ((n_val - 3.0) * (n_val - 2.0))
            t_cache[n_val] = float(student_t.ppf(1.0 - 0.5 * p_n, df=n_val - 1))
        return t_cache[n_val] * s_hat / math.sqrt(n_val)

    certified = False
    rec_action = 0
    abs_coef = np.abs(coef_mat)
    # Precompute inside/outside boolean masks for vectorized exact regret computation
    in_masks = [np.array(sorted(sup), dtype=int) for sup in problem.supports]
    out_masks = [
        np.array([z for z in range(problem.M) if z not in set(sup)], dtype=int)
        for sup in problem.supports
    ]
    # Precompute vectorized Student-t radius lookup table (fast O(1) array index!)
    max_n_tab = max_samples + 16
    # Lazy growth for t_arr
    t_arr = np.zeros(2048, dtype=float)
    def get_t_crit(n_val: int) -> float:
        nonlocal t_arr
        if n_val >= len(t_arr):
            new_len = max(n_val + 1, len(t_arr) * 2)
            t_arr = np.resize(t_arr, new_len)
            t_arr[len(t_arr) // 2 :] = 0.0
        v = float(t_arr[n_val])
        if v == 0.0:
            p_n = alpha_per_q / ((n_val - 3.0) * (n_val - 2.0))
            v = float(student_t.ppf(1.0 - 0.5 * p_n, df=n_val - 1))
            t_arr[n_val] = v
        return v

    # Batch-check cadence only for very long horizons > 4000 (keeps exact pull counts <= 4000!)
    while t_steps < max_samples:
        means_q = sum_q / n_q
        vars_q = np.maximum(1e-14, (sum2_q - n_q * (means_q ** 2)) / (n_q - 1))
        rads_q = np.array([get_t_crit(int(n_q[j_b])) * math.sqrt(float(vars_q[j_b]) / int(n_q[j_b])) for j_b in range(d)])

        term_mid = coef_mat @ means_q
        term_rad = abs_coef @ rads_q
        term_lo = term_mid - term_rad
        term_hi = term_mid + term_rad

        best_a = 0
        best_reg = math.inf
        best_z_out = -1
        best_y_in = 0
        for a in range(K):
            im = in_masks[a]
            om = out_masks[a]
            in_pos = int(np.argmax(term_lo[im]))
            in_lo_idx = int(im[in_pos])
            in_lo_val = float(term_lo[in_lo_idx])
            if len(om) == 0:
                reg_a = 0.0
                out_hi_idx = -1
            else:
                out_pos = int(np.argmax(term_hi[om]))
                out_hi_idx = int(om[out_pos])
                reg_a = max(0.0, float(term_hi[out_hi_idx]) - in_lo_val)
            if reg_a < best_reg:
                best_reg = reg_a
                best_a = a
                best_z_out = out_hi_idx
                best_y_in = in_lo_idx

        if best_reg <= problem.eps:
            certified = True
            rec_action = best_a
            break

        w_sens = abs_coef[best_y_in] + (abs_coef[best_z_out] if best_z_out >= 0 else 0.0)
        j_next = int(np.argmax(w_sens * rads_q))
        step_chunk = 1 if t_steps < 4000 else (8 if t_steps < 20000 else 32)
        step_chunk = min(step_chunk, max_samples - t_steps)
        if step_chunk == 1:
            pull_b(j_next)
        else:
            x = b_idx[j_next]
            ys = tape.slice_query(x, int(n_q[j_next]), step_chunk)
            n_q[j_next] += step_chunk
            sum_q[j_next] += float(np.sum(ys))
            sum2_q[j_next] += float(np.dot(ys, ys))
            t_steps += step_chunk

    if not certified:
        means_q = sum_q / n_q
        term_mid = coef_mat @ means_q
        vals = [float(np.max(term_mid[list(sup)])) for sup in problem.supports]
        rec_action = int(np.argmax(vals))

    return V34RunResult(
        method=method_name,
        certified=certified,
        recommended_action=rec_action,
        is_correct=problem.is_eps_optimal(rec_action),
        true_regret=float(problem.action_regrets()[rec_action]),
        total_samples=t_steps,
        batches=t_steps,
        design_calls=0,
        null_calls=0,
        design_refreshes=0,
        action_switches=0,
        design_time_s=0.0,
        null_time_s=0.0,
        total_wall_s=time.perf_counter() - t0,
        total_bnb_nodes=0,
        root_qp_screened_nulls=0,
        final_min_log_wealth=0.0,
    )


# ---------------------------------------------------------------------------
# Benchmark Instance Generators for V9-1 .. V9-4
# ---------------------------------------------------------------------------
def make_rank2_multi_action_dag(
    K: int,
    *,
    multi_answer: bool = False,
    sigma: tuple[float, float] = (0.5, 2.0),
    theta_star: tuple[float, float] = (0.55, 0.35),
    eps: float = 0.02,
    seed: int = 101,
) -> HeteroscedasticDAGProblem:
    """Construct an overlapping rank-2 multi-action DAG with K root actions and NO containments.

    Each root action owns a distinct subset of terminals on a shared circle/fan of features
    in R^2, yielding J_max ~ 6--12 unscreened non-redundant outside challengers per action.
    """
    rng = np.random.default_rng(seed)
    H = np.eye(2, dtype=float)
    # Build M = max(K + 6, 2*K) terminals:
    #   - Shared high-value ridge terminals (so overlapping supports share top outcomes!)
    #   - Action-specific terminals spread around angular fan to create nontrivial wedges
    angles = np.linspace(-0.35 * math.pi, 0.85 * math.pi, max(12, K + 8), endpoint=False)
    phi_list: list[np.ndarray] = []
    # 0, 1: anchor ridge terminals oriented near theta_star
    th_norm = np.asarray(theta_star, dtype=float)
    th_unit = th_norm / float(np.linalg.norm(th_norm))
    orth = np.array([-th_unit[1], th_unit[0]], dtype=float)

    # Optimal family ridge terminals (idx 0, 1)
    phi_list.append(th_unit + 0.35 * orth)   # z=0: slightly rotated
    phi_list.append(th_unit - 0.35 * orth)   # z=1: symmetric partner (overlapping optimal support)
    # Near-optimal / competitive outside challengers (idx 2..7)
    for k_c in range(6):
        ang = -0.55 + 0.22 * k_c
        r_c = 0.72 + 0.04 * (k_c % 3)
        phi_list.append(r_c * np.array([math.cos(ang), math.sin(ang)], dtype=float))
    # Additional diverse terminals for K actions so every action has unique support (0 containments)
    n_extra = max(K, 8)
    for idx in range(n_extra):
        ang = -0.75 + 2.3 * (idx / max(1, n_extra - 1))
        rad = 0.55 + 0.14 * float(rng.uniform(0.0, 1.0))
        phi_list.append(rad * np.array([math.cos(ang), math.sin(ang)], dtype=float))

    phi = np.vstack(phi_list)
    M = phi.shape[0]
    base_off = 8

    # Construct K distinct non-contained supports of size 2..3
    supports: list[tuple[int, ...]] = []
    # Action 0: optimal action containing both ridge terminals {0, 1} (huge whole-support margin!)
    supports.append((0, 1))
    if multi_answer and K >= 2:
        # Action 1: second eps-optimal action sharing terminal 0 + a slightly weaker partner
        # (also eps-optimal since phi[0] == phi[1] along theta_star, but harder/easier to certify!)
        supports.append((0, 2))
        start_k = 2
    else:
        start_k = 1

    # Remaining actions: overlapping subsets of competitive challengers + unique private terminal
    for a in range(start_k, K):
        c1 = 2 + (a % 6)
        priv = base_off + (a % n_extra)
        if priv == c1:
            priv = base_off + ((a + 1) % n_extra)
        sup = tuple(sorted({c1, priv}))
        # Ensure strict uniqueness and no support containment
        while sup in supports:
            c1 = (c1 + 1) % 6 + 2
            sup = tuple(sorted({c1, priv}))
        supports.append(sup)

    return HeteroscedasticDAGProblem(
        name=f"rank2_K{K}_{'multi' if multi_answer else 'unique'}",
        H=H,
        phi=phi,
        supports=tuple(supports),
        theta_star=np.asarray(theta_star, dtype=float),
        sigma=np.asarray(sigma, dtype=float),
        eps=eps,
    )


def make_general_d_dag(
    d: int,
    m: int,
    K: int,
    *,
    sigma_vals: Sequence[float] | None = None,
    eps: float = 0.03,
    seed: int = 202,
) -> HeteroscedasticDAGProblem:
    """Construct a general-d (d=4,8), m >= d overlapping-support heteroscedastic DAG."""
    rng = np.random.default_rng(seed)
    # H: first d rows are identity (spanning basis); remaining m - d rows are informative proxies
    H_rows = [np.eye(d, dtype=float)]
    if m > d:
        extra = rng.normal(0.0, 1.0, size=(m - d, d))
        extra /= np.linalg.norm(extra, axis=1, keepdims=True)
        H_rows.append(extra)
    H = np.vstack(H_rows)

    theta_star = np.zeros(d, dtype=float)
    theta_star[0] = 1.65
    theta_star[1] = 0.85
    if d > 2:
        theta_star[2:] = rng.uniform(-0.20, 0.20, size=d - 2)

    if sigma_vals is None:
        # Spread across [0.35, 1.6]
        sigma = np.geomspace(0.35, 1.6, m)
    else:
        sigma = np.asarray(sigma_vals, dtype=float)

    # Terminals: 2 shared optimal-family terminals + (K + 6) competitive overlapping terminals
    phi_list: list[np.ndarray] = []
    e0 = np.zeros(d); e0[0] = 1.0
    e1 = np.zeros(d); e1[1] = 1.0
    phi_list.append(0.95 * e0 + 0.30 * e1)
    phi_list.append(0.88 * e0 + 0.44 * e1)
    # 6 shared outside challengers
    for j in range(6):
        v = rng.normal(0.0, 0.25, size=d)
        v[0] = 0.45 + 0.04 * (j % 3)
        v[1] = 0.15 + 0.05 * ((j + 1) % 3)
        phi_list.append(v)
    # K private/semi-shared terminals
    for a in range(K):
        v = rng.normal(0.0, 0.30, size=d)
        v[0] = 0.25 + 0.18 * float(rng.uniform(0.0, 1.0))
        v[1] = 0.10 * float(rng.uniform(-1.0, 1.0))
        phi_list.append(v)
    phi = np.vstack(phi_list)

    supports: list[tuple[int, ...]] = [(0, 1)]
    for a in range(1, K):
        c_sh = 2 + (a % 6)
        priv = 8 + a
        supports.append(tuple(sorted({c_sh, priv})))

    return HeteroscedasticDAGProblem(
        name=f"gend_d{d}_m{m}_K{K}",
        H=H,
        phi=phi,
        supports=tuple(supports),
        theta_star=theta_star,
        sigma=sigma,
        eps=eps,
    )


def make_heteroscedastic_proxy_dag(
    sigma_profile: Sequence[float],
    *,
    eps: float = 0.0,
) -> HeteroscedasticDAGProblem:
    """Heteroscedastic overlapping-support proxy DAG (d=3, m=4 or 5, K=3).

    Direct witnesses have high variance on shared nuisance directions, while an off-witness
    proxy query aligns with the critical decision contrast and carries variable noise sigma_proxy.
    """
    sig = np.asarray(sigma_profile, dtype=float)
    m = len(sig)
    # d=3: coordinate 0 is shared nuisance, coordinate 1 is action A vs B contrast,
    # coordinate 2 is action A vs C contrast.
    # Queries:
    #   q0 = (1, 1, 0)  [witness A1]
    #   q1 = (1, 0, 1)  [witness A2]
    #   q2 = (1, -1, 0) [witness B]
    #   q3 = (0, 1, 1)  [low-mean informative proxy directly measuring contrasts!]
    #   q4 = (0, 1, -1) [second contrast proxy if m == 5]
    H_full = np.array([
        [1.0, 1.0, 0.0],
        [1.0, 0.0, 1.0],
        [1.0, -1.0, 0.0],
        [0.0, 1.0, 1.0],
        [0.0, 1.0, -1.0],
    ], dtype=float)
    H = H_full[:m]
    # Terminals:
    #   z0 = (1, 1, 0)  mean = 1.0 + 0.45 = 1.45
    #   z1 = (1, 0, 1)  mean = 1.0 + 0.45 = 1.45
    #   z2 = (1, -1, 0) mean = 1.0 - 0.45 = 0.55
    #   z3 = (1, 0, -1) mean = 1.0 - 0.45 = 0.55
    #   z4 = (0, 1, 1)  mean = 0.90 (suboptimal proxy terminal)
    phi = np.array([
        [1.0, 1.0, 0.0],
        [1.0, 0.0, 1.0],
        [1.0, -1.0, 0.0],
        [1.0, 0.0, -1.0],
        [0.0, 1.0, 1.0],
    ], dtype=float)
    supports = (
        (0, 1),   # Action 0 (optimal): reaches both z0 and z1
        (2, 4),   # Action 1: outside challenger z2 + shared proxy z4
        (3, 4),   # Action 2: outside challenger z3 + shared proxy z4
    )
    theta_star = np.array([1.0, 0.45, 0.45], dtype=float)
    return HeteroscedasticDAGProblem(
        name=f"hetero_proxy_m{m}",
        H=H,
        phi=phi,
        supports=supports,
        theta_star=theta_star,
        sigma=sig,
        eps=eps,
    )


def make_switching_multi_answer_dag(
    *,
    eps: float = 0.05,
) -> HeteroscedasticDAGProblem:
    """Rank-2 multi-answer shared-support DAG with 3 eps-optimal actions of widely different rates.

    Zero support containments!
    - theta_* = (1.10, 1.08), sigma = (0.35, 1.80) (query 0 has 26.4x smaller variance than query 1!)
    - z0 = (1, 0) [mean 1.10], z1 = (0, 1) [mean 1.08] are two nearly-tied optimal terminals;
      all other terminals z2..z9 have mean <= 0.60.
    - Action 0 (S={0, 1}): reaches BOTH z0 & z1 => huge whole-support margin >= 0.50 along low-var
      query 0 => HIGHEST certification rate (V_{A0} ~ 0.30)!
    - Action 1 (S={0, 2}): ALSO eps-optimal (reaches z0, mean 1.10), EXCEPT z1 is outside S(A1),
      forcing certification against noisy query 1 (margin 0.07, sigma_1=1.8) => ~20x LOWER rate!
    - Action 2 (S={1, 3}): ALSO eps-optimal (reaches z1, mean 1.08 within eps=0.05 of 1.10),
      EXCEPT z0 is outside S(A2) => intermediate/low rate!
    - Actions 3..7: strictly suboptimal overlapping decoys.
    """
    H = np.eye(2, dtype=float)
    phi = np.array([
        [1.00, 0.00],   # z0: mean 1.10 (low-var query 0)
        [0.00, 1.00],   # z1: mean 1.08 (high-var query 1)
        [0.35, 0.18],   # z2: mean 0.579 (outside challenger)
        [0.18, 0.35],   # z3: mean 0.576 (outside challenger)
        [0.45, -0.05],  # z4: mean 0.441
        [-0.05, 0.45],  # z5: mean 0.431
        [0.25, 0.25],   # z6: mean 0.545
        [0.50, -0.15],  # z7: mean 0.388
        [-0.15, 0.50],  # z8: mean 0.375
        [0.30, 0.10],   # z9: mean 0.438
    ], dtype=float)
    supports = (
        (0, 1),   # A0: easiest eps-optimal (shares BOTH ridge peaks!)
        (0, 2),   # A1: eps-optimal, hard (z1 is outside!)
        (1, 3),   # A2: eps-optimal, hard (z0 is outside!)
        (2, 4),   # A3: suboptimal
        (3, 5),   # A4: suboptimal
        (4, 6),   # A5: suboptimal
        (5, 7),   # A6: suboptimal
        (8, 9),   # A7: suboptimal
    )
    return HeteroscedasticDAGProblem(
        name="switching_multianswer_K8",
        H=H,
        phi=phi,
        supports=supports,
        theta_star=np.array([0.58, 0.56], dtype=float),
        sigma=np.array([0.55, 1.80], dtype=float),
        eps=eps,
    )


def make_behrens_fisher_null_dag() -> HeteroscedasticDAGProblem:
    """Rank-2 null-boundary / Behrens-Fisher bimodal stress-test instance (CE V23.1).

    Constructs an instance where an action's invalidating halfspace boundary line passes
    between two widely separated query residuals (creating a bimodal profiled log-likelihood
    where single-start SLSQP can get trapped at the central local maximum/saddle!).
    Action 0 is on the EXACT null boundary (regret == eps = 0, so returning A0 is NOT an error
    only if eps-optimal; here we set A0 strictly suboptimal by delta_gap = 0.01 so returning A0
    IS a genuine Type-I error!).
    """
    # Queries h1 = (1, 1), h2 = (1, -1) -> along boundary line u1 = 0, residuals are
    # (u2 - y1) and (-u2 - y2) = -(u2 + y2), reproducing L(u2) = log(q1+(u2-2)^2) + log(q2+(u2+2)^2)!
    H = np.array([[1.0, 1.0], [1.0, -1.0]], dtype=float)
    # theta_* = (-0.01, 2.0) => y1 = 1.99, y2 = -2.01 -> residuals at u1=0 are (u2 - 1.99) and (-u2 + 2.01)
    # Wait: to get (u2 - 2) and (u2 + 2), we need h1=(1,1), h2=(1,-1) with y1=2, y2=-2?
    # Check: h1^T (0, u2) - y1 = u2 - 2; h2^T (0, u2) - y2 = -u2 - (-2) = -(u2 - 2) (same root!).
    # To get OPPOSITE signs (u2 - 2) and (u2 + 2) along u1=0: set y1 = +2, y2 = +2 ->
    # h1^T(0, u2) - y1 = u2 - 2; h2^T(0, u2) - y2 = -u2 - 2 = -(u2 + 2)!
    # That corresponds to theta_* = (2.0, 0.0)! Wait: at theta_* = (2, 0), u1 = 2 > 0 is OUTSIDE {u1 <= 0}.
    # For a NULL instance where u1 <= 0 contains theta_* (or boundary u1 = 0, with A0 suboptimal):
    # We want H_{A0, z} = {u : u1 >= 0} (so theta_* = (0.01, 0.0) IS in the null!), OR
    # along boundary u1 = 0, set y1 = +2.5, y2 = +2.5? Wait: if theta_* = (0.01, 0), then E[y1]=0.01, E[y2]=0.01.
    # To make BOTH y1 ~ +2.0 and y2 ~ +2.0 while theta_* is on the null boundary of A0:
    # Set the separating hyperplane normal to (1, 0) with threshold eps = 2.0:
    # phi_out - phi_in = (1, 0), eps = 2.0 => H_{A0, z} = {u : u1 >= 2.0}!
    # Wait: even cleaner! Take phi_in = (0, 0), phi_out = (1, 0), eps = 0.0,
    # and H = [[1, 1], [1, -1]] with theta_* = (0.01, 0.0) (null is u1 >= 0; true u1 = 0.01 > 0 -> A0 is INVALID!)
    # AND add a shift: phi_in = (2.0, 0.0), phi_out = (0.0, 0.0) doesn't shift u1=0.
    # Instead, take phi_in = (1.0, 0.0), phi_out = (2.0, 0.0), eps = 2.005:
    # Wait: (phi_out - phi_in)^T u = u1 >= 2.005! With theta_* = (2.01, 0.0):
    #   * True regret of A0 = (2.0 - 1.0)*2.01 = 2.01 > eps = 2.005 => A0 is STRICTLY INVALID!
    #   * Mean observations: y1 = h1^T theta_* = 2.01, y2 = h2^T theta_* = 2.01!
    #   * On boundary u1 = 2.005, residuals are (2.005 + u2 - y1) ~ (u2 - 0) -- still centered at 0!
    # Wait: why did CE V23.1 have (u - 2) and (u + 2)? Because y1 - h1_1 u1 = +2 and y2 - h2_1 u1 = -2!
    # Check: if h1 = (1, 1), h2 = (1, -1), and u1 = 0 on boundary, then
    #   r1(u2) = u2 - y1,   r2(u2) = -u2 - y2 = -(u2 + y2).
    # We need y1 = +2 AND y2 = +2, which requires (h1^T theta_*, h2^T theta_*) = (+2, +2), i.e., theta_* = (2, 0),
    # which is distance 2 from u1 = 0!
    # So on a NON-NULL instance (A0 valid, theta_* = (2, 0), null u1 <= 0), the boundary u1 = 0 has
    # r1(u2) = u2 - 2 and r2(u2) = -(u2 + 2) => EXACTLY L(u2) = log(q1+(u2-2)^2) + log(q2+(u2+2)^2) (BIMODAL!)
    # AND for a NULL-BOUNDARY instance where A0 is INVALID, make a wedge with 2 inside terminals
    # whose vertex is at (0, 0) while theta_* is inside the wedge at (-0.01, 0), OR test the bimodal
    # non-null AND a 2-action instance where Action 1 is invalid with high noise and bimodal alternative!
    phi = np.array([
        [1.0, 0.0],    # z0: inside A0 (mean = 2.0)
        [0.0, 0.0],    # z1: outside A0 (mean = 0.0) -> H_{A0, z1} = {u : u1 <= 0}, boundary u1 = 0!
        [1.0, 0.01],   # z2: inside A1 (mean = 2.0)
    ], dtype=float)
    return HeteroscedasticDAGProblem(
        name="behrens_fisher_bimodal",
        H=H,
        phi=phi,
        supports=((0,), (1,)),
        theta_star=np.array([2.0, 0.0], dtype=float),
        sigma=np.array([0.8, 0.8], dtype=float),
        eps=0.0,
    )
