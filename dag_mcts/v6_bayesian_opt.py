"""v6 Bayesian Optimization Extensions: GP-Guided Acquisitions & GP Confidence Boxes
for Shared-Support Root Certification on Combinatorial Protein Landscapes.

Implements two cleanly separated methodological levels connecting Gaussian-process (GP)
Bayesian optimization (BO) to exact shared-support root certification:

1. Level 1 (`GPGuidedRootCertSession` — BO-guided sampling + valid frequentist root certificate):
   Retains the exact anytime-valid `NestedIntervals` terminal confidence box and
   `DualWitnessCovers` outside-support root stopping rule `min_{a in A} R_t(a) <= eps`
   (preserving 100% frequentist `(eps, delta)` soundness regardless of GP misspecification),
   while selecting terminals via an exact discrete-domain GP surrogate over the `M`
   protein sequences:
   - `gp_ucb`: Standard GP-UCB `argmax_{z in Z} (m_t(z) + sqrt(beta_t) * s_t(z))`
   - `gp_ei`: Standard Expected Improvement `argmax_{z in Z} EI_t(z)`
   - `gp_ts`: Exact joint GP Thompson sampling `argmax_{z in Z} f_tilde_t(z)` via Matheron's rule
   - `gp_root_info`: Surrogate-guided root-regret witness allocation, using clipped GP
     upper bounds to identify the candidate commitment and inside peak `z_t^{in,GP}` without
     exhausting `S(a*)` while querying exact outside challengers `q_t notin S(b_t)` to
     certify `R_t(b_t) <= eps`.

2. Level 2 Probe (`GPBoxCertSession` — GP-derived simultaneous confidence boxes):
   Replaces independent terminal intervals with nested GP simultaneous confidence intervals
   `[m_t(z) - sqrt(beta_t) s_t(z), m_t(z) + sqrt(beta_t) s_t(z)]` inside the exact
   outside-support regret identity, contrasting nominal Bayesian GP bounds against
   RKHS-norm-calibrated frequentist simultaneous bounds (Chowdhury & Gopalan, 2017).
"""
from __future__ import annotations

import math
import time

import numpy as np
from scipy.linalg import cho_factor, cho_solve, solve_triangular

from .certified_uct import UCTWork
from .graph import DAG, Problem
from .v3_extensions import splitmix_uniform01
from .v4_baselines import _shortest_leaf_paths
from .v5_hybrid_and_os import DualWitnessCovers


# Standardized 5-D physicochemical amino-acid descriptors:
# (Kyte-Doolittle hydropathy, normalized van der Waals volume, net charge pH 7,
#  Grantham polarity, aromaticity indicator)
_AA_RAW_PROPS: dict[str, tuple[float, float, float, float, float]] = {
    "A": (1.8, 0.14, 0.0, 8.1, 0.0),
    "C": (2.5, 0.30, 0.0, 5.5, 0.0),
    "D": (-3.5, 0.30, -1.0, 13.0, 0.0),
    "E": (-3.5, 0.47, -1.0, 12.3, 0.0),
    "F": (2.8, 0.77, 0.0, 5.2, 1.0),
    "G": (-0.4, 0.00, 0.0, 9.0, 0.0),
    "H": (-3.2, 0.58, 0.1, 10.4, 1.0),
    "I": (4.5, 0.64, 0.0, 5.2, 0.0),
    "K": (-3.9, 0.68, 1.0, 11.3, 0.0),
    "L": (3.8, 0.64, 0.0, 4.9, 0.0),
    "M": (1.9, 0.63, 0.0, 5.7, 0.0),
    "N": (-3.5, 0.35, 0.0, 11.6, 0.0),
    "P": (-1.6, 0.36, 0.0, 8.0, 0.0),
    "Q": (-3.5, 0.51, 0.0, 10.5, 0.0),
    "R": (-4.5, 0.81, 1.0, 10.5, 0.0),
    "S": (-0.8, 0.18, 0.0, 9.2, 0.0),
    "T": (-0.7, 0.35, 0.0, 8.6, 0.0),
    "V": (4.2, 0.47, 0.0, 5.9, 0.0),
    "W": (-0.9, 1.00, 0.0, 5.4, 1.0),
    "Y": (-1.3, 0.80, 0.0, 6.2, 1.0),
}


def _standardized_aa_table() -> dict[str, np.ndarray]:
    keys = sorted(_AA_RAW_PROPS)
    mat = np.array([_AA_RAW_PROPS[k] for k in keys], dtype=np.float64)
    mu = mat.mean(axis=0, keepdims=True)
    sd = mat.std(axis=0, keepdims=True) + 1e-12
    normed = (mat - mu) / sd
    return {k: normed[i] for i, k in enumerate(keys)}


_AA_VEC = _standardized_aa_table()


def protein_sequence_kernel(
    sequences: list[str],
    prior_scale: float = 0.22,
    lengthscale: float = 3.0,
    nugget: float = 0.02,
) -> np.ndarray:
    """Positive-definite additive + pairwise-epistasis + physicochemical RBF kernel over 4-site sequences."""
    m = len(sequences)
    seq_len = len(sequences[0])

    # 1. Physicochemical RBF component
    feats = np.stack(
        [np.concatenate([_AA_VEC[ch] for ch in seq], axis=0) for seq in sequences],
        axis=0,
    )  # (M, 5 * seq_len)
    sq_dists = (
        np.sum(feats * feats, axis=1, keepdims=True)
        + np.sum(feats * feats, axis=1, keepdims=True).T
        - 2.0 * (feats @ feats.T)
    )
    np.maximum(sq_dists, 0.0, out=sq_dists)
    k_phys = np.exp(-sq_dists / (2.0 * lengthscale * lengthscale))

    # 2. Combinatorial position-match + pairwise-epistasis component
    char_mat = np.array([[ord(c) for c in seq] for seq in sequences], dtype=np.int32)  # (M, L)
    matches = (char_mat[:, None, :] == char_mat[None, :, :]).astype(np.float64)       # (M, M, L)
    k_add = matches.mean(axis=2)
    pair_sum = np.zeros((m, m), dtype=np.float64)
    n_pairs = 0
    for p in range(seq_len):
        for q in range(p + 1, seq_len):
            pair_sum += matches[:, :, p] * matches[:, :, q]
            n_pairs += 1
    k_pair = pair_sum / max(1, n_pairs)

    k_base = 0.35 * k_add + 0.20 * k_pair + 0.45 * k_phys + nugget * np.eye(m, dtype=np.float64)
    return (prior_scale * prior_scale) * k_base


def alt_protein_sequence_kernel(
    sequences: list[str],
    mode: str = "structured",
    prior_scale: float = 0.22,
    nugget: float = 0.02,
) -> np.ndarray:
    """Protein sequence kernels for kernel-misspecification sensitivity studies:
    - `structured`: default additive + pairwise-epistasis + physicochemical RBF (`ell = 3.0`)
    - `hamming`: 1st-order normalized Hamming similarity only (`k_add + nugget * I`)
    - `oversmooth`: deliberately misspecified over-smooth RBF (`ell = 25.0`, no site-match terms)
    - `scrambled_desc`: deliberately misspecified RBF (`ell = 1.8`) over cyclically deranged
      amino-acid descriptors (mapping hydrophobic residues to charged/polar vectors and vice versa).
    """
    if mode == "structured":
        return protein_sequence_kernel(sequences, prior_scale=prior_scale, lengthscale=3.0, nugget=nugget)

    m = len(sequences)
    if mode == "hamming":
        char_mat = np.array([[ord(c) for c in seq] for seq in sequences], dtype=np.int32)
        k_add = (char_mat[:, None, :] == char_mat[None, :, :]).astype(np.float64).mean(axis=2)
        return (prior_scale * prior_scale) * (k_add + nugget * np.eye(m, dtype=np.float64))

    keys = sorted(_AA_VEC)
    if mode == "oversmooth":
        table = _AA_VEC
        ell = 25.0
    elif mode == "scrambled_desc":
        # Deterministic derangement shifting sorted amino acids by +7 positions
        table = {k: _AA_VEC[keys[(i + 7) % len(keys)]] for i, k in enumerate(keys)}
        ell = 1.8
    else:
        raise ValueError(f"Unknown protein kernel mode: {mode!r}")

    feats = np.stack(
        [np.concatenate([table[ch] for ch in seq], axis=0) for seq in sequences],
        axis=0,
    )
    sq_dists = (
        np.sum(feats * feats, axis=1, keepdims=True)
        + np.sum(feats * feats, axis=1, keepdims=True).T
        - 2.0 * (feats @ feats.T)
    )
    np.maximum(sq_dists, 0.0, out=sq_dists)
    k_rbf = np.exp(-sq_dists / (2.0 * ell * ell))
    return (prior_scale * prior_scale) * (k_rbf + nugget * np.eye(m, dtype=np.float64))


class DiscreteGPSurrogate:
    """Exact discrete-domain Gaussian Process maintained in O(M^2) per observation via Sherman-Morrison."""

    def __init__(
        self,
        kernel: np.ndarray,
        prior_mean: float = 0.28,
        obs_std: float = 0.16,
        refresh_every: int = 1500,
    ):
        self.m = int(kernel.shape[0])
        self.prior_mean = float(prior_mean)
        self.obs_std = float(obs_std)
        self.obs_var = float(obs_std * obs_std)
        self.inv_obs_var = 1.0 / self.obs_var
        self.refresh_every = int(refresh_every)

        self.K = np.array(kernel, dtype=np.float64, copy=True)
        self.L0 = np.linalg.cholesky(self.K)
        eye = np.eye(self.m, dtype=np.float64)
        self.K_inv = cho_solve((self.L0, True), eye)

        self.counts = np.zeros(self.m, dtype=np.float64)
        self.centered_sums = np.zeros(self.m, dtype=np.float64)
        self.mean = np.full(self.m, self.prior_mean, dtype=np.float64)
        self.Sigma = self.K.copy()
        self._diag_std = np.sqrt(np.maximum(1e-16, np.diag(self.Sigma)))
        self._pending_counts: dict[int, float] = {}
        self.info_gain = 0.0  # Exact 0.5 * log det(I + sigma^-2 K diag(n))
        self.updates = 0
        self.gp_time_s = 0.0

    def rkhs_norm(self, f_vals: np.ndarray) -> float:
        """Exact RKHS norm sqrt((f - m_0)^T K^{-1} (f - m_0)) on the finite domain."""
        diff = np.asarray(f_vals, dtype=np.float64) - self.prior_mean
        return float(math.sqrt(max(0.0, float(diff @ (self.K_inv @ diff)))))

    def flush(self) -> None:
        if not self._pending_counts:
            return
        t0 = time.perf_counter()
        u_idx = np.array(sorted(self._pending_counts.keys()), dtype=np.int64)
        dn = np.array([self._pending_counts[int(i)] for i in u_idx], dtype=np.float64)
        self._pending_counts.clear()

        d_u = dn * self.inv_obs_var
        if len(u_idx) == 1:
            j = int(u_idx[0])
            dj = float(d_u[0])
            col = self.Sigma[:, j].copy()
            s_jj = float(col[j])
            self.info_gain += 0.5 * math.log(max(1.0, 1.0 + dj * s_jj))
            denom = (1.0 / dj) + s_jj
            self.Sigma -= ((1.0 / denom) * col)[:, None] * col[None, :]
        else:
            c_mat = self.Sigma[:, u_idx]  # (M, r)
            a_mat = self.Sigma[np.ix_(u_idx, u_idx)].copy()
            a_mat[np.diag_indices(len(u_idx))] += 1.0 / d_u
            l_a = np.linalg.cholesky(a_mat)
            self.info_gain += float(np.sum(np.log(np.diag(l_a))) + 0.5 * np.sum(np.log(d_u)))
            w_mat = solve_triangular(l_a, c_mat.T, lower=True, check_finite=False)
            self.Sigma -= w_mat.T @ w_mat

        self.mean = self.prior_mean + self.Sigma @ (self.centered_sums * self.inv_obs_var)
        self._diag_std = np.sqrt(np.maximum(1e-16, np.diag(self.Sigma)))
        self.gp_time_s += time.perf_counter() - t0

    def observe(self, idx: int, y: float, batch_after: int = 250, batch_stride: int = 50) -> None:
        self.counts[idx] += 1.0
        self.centered_sums[idx] += (y - self.prior_mean)
        self._pending_counts[idx] = self._pending_counts.get(idx, 0.0) + 1.0
        self.updates += 1

        if self.updates <= batch_after or (self.updates % batch_stride == 0):
            self.flush()

    def std(self) -> np.ndarray:
        return self._diag_std

    def sample_thompson(self, rng: np.random.Generator) -> np.ndarray:
        """Exact O(M^2) draw from N(mean, Sigma) via Matheron's Gaussian conditioning identity."""
        self.flush()
        t0 = time.perf_counter()
        z0 = rng.standard_normal(self.m)
        g = rng.standard_normal(self.m)
        u = self.L0 @ z0
        d_vec = self.counts * self.inv_obs_var
        v = d_vec * u + np.sqrt(d_vec) * g
        draw = self.mean + u - (self.Sigma @ v)
        self.gp_time_s += time.perf_counter() - t0
        return draw


def _std_norm_pdf_cdf(z: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    pdf = (1.0 / math.sqrt(2.0 * math.pi)) * np.exp(-0.5 * np.clip(z * z, 0.0, 100.0))
    # Vectorized erf approximation (Abramowitz & Stegun 7.1.26, max error 1.5e-7)
    sign = np.where(z >= 0.0, 1.0, -1.0)
    x = np.abs(z) / math.sqrt(2.0)
    t = 1.0 / (1.0 + 0.3275911 * x)
    poly = t * (
        0.254829592
        + t * (-0.284496736 + t * (1.421413741 + t * (-1.453152027 + t * 1.061405429)))
    )
    erf_approx = sign * (1.0 - poly * np.exp(-np.clip(x * x, 0.0, 100.0)))
    cdf = 0.5 * (1.0 + erf_approx)
    return pdf, cdf


def _build_action_support_indices(graph: DAG, leaves: list[int]) -> list[np.ndarray]:
    leaf_to_idx = {z: i for i, z in enumerate(leaves)}
    reach: list[set[int]] = [set() for _ in range(len(graph))]
    for v in reversed(graph.order):
        ch = graph.children[v]
        if not ch:
            reach[v].add(v)
        else:
            for c in ch:
                reach[v].update(reach[c])
    supports = []
    for c in graph.children[graph.root]:
        idxs = sorted(leaf_to_idx[z] for z in reach[c])
        supports.append(np.array(idxs, dtype=np.int64))
    return supports


class GPGuidedRootCertSession:
    """Level-1 BO-guided sampling with exact frequentist shared-support root certification.

    Uses the exact same `NestedIntervals` + `DualWitnessCovers` stopping rule as
    `Exact-Regret-DAG-LUCB` and `Optimistic-Separation`, guaranteeing identical
    frequentist `(eps, delta)` soundness under arbitrary surrogate misspecification.
    """

    VALID_ACQ = ("gp_ucb", "gp_ei", "gp_ts", "gp_root_info")

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        acquisition: str = "gp_ucb",
        delta: float = 0.05,
        schedule: str = "emp_bernstein",
        kernel: np.ndarray | None = None,
        prior_mean: float = 0.28,
        obs_std: float = 0.16,
    ):
        if acquisition not in self.VALID_ACQ:
            raise ValueError(f"Unsupported GP acquisition: {acquisition!r}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = float(epsilon)
        self.delta = float(delta)
        self.acquisition = acquisition
        self.oracle = problem.oracle(seed)
        self.policy_work = w = UCTWork()
        self.monitor = DualWitnessCovers(
            self.graph,
            delta=delta,
            schedule=schedule,
            layout="best",
            track_separation=True,
        )
        self.leaf_paths = _shortest_leaf_paths(self.graph, w)
        self.leaves = list(self.graph.leaves)
        self.leaf_to_idx = {z: i for i, z in enumerate(self.leaves)}
        self.action_supports = _build_action_support_indices(self.graph, self.leaves)

        if kernel is None:
            seqs = [problem.variant_of_leaf[z] for z in self.leaves]
            kernel = protein_sequence_kernel(seqs)
        t_k0 = time.perf_counter()
        self.gp = DiscreteGPSurrogate(kernel, prior_mean=prior_mean, obs_std=obs_std)
        self.gp.gp_time_s += time.perf_counter() - t_k0
        self.rng = np.random.default_rng((seed * 0x9E3779B97F4A7C15 + 17) & 0xFFFFFFFFFFFFFFFF)

        self.calls = 0
        init_act, init_reg, _, _, _ = self.monitor.query_dual_witness()
        self.certified = bool(init_reg <= self.epsilon)
        self.action = int(init_act)

    def _select_leaf(self) -> int:
        t0 = time.perf_counter()
        t_step = self.calls + 1
        m_vec = self.gp.mean
        s_vec = self.gp.std()
        beta_sqrt = math.sqrt(2.0 * math.log(max(2.0, len(self.leaves) * (t_step ** 2) * math.pi ** 2 / (6.0 * self.delta))))

        if self.acquisition == "gp_ucb":
            scores = m_vec + beta_sqrt * s_vec
            best_idx = int(np.argmax(scores))
            self.gp.gp_time_s += time.perf_counter() - t0
            return self.leaves[best_idx]

        if self.acquisition == "gp_ei":
            # Standard Expected Improvement over current highest posterior mean
            f_best = float(np.max(m_vec)) if self.calls > 0 else self.gp.prior_mean
            imp = m_vec - f_best
            z = imp / np.maximum(s_vec, 1e-12)
            pdf, cdf = _std_norm_pdf_cdf(z)
            ei = np.maximum(0.0, imp * cdf + s_vec * pdf)
            # Break initial symmetry deterministically toward first unvisited anchor/leaf
            best_idx = int(np.argmax(ei))
            self.gp.gp_time_s += time.perf_counter() - t0
            return self.leaves[best_idx]

        if self.acquisition == "gp_ts":
            # Reuse posterior draw across mini-batch steps after initial 250-step discovery phase
            if self.calls <= 250 or (self.calls % 25 == 0) or not hasattr(self, "_cached_ts"):
                self._cached_ts = self.gp.sample_thompson(self.rng)
            t1 = time.perf_counter()
            best_idx = int(np.argmax(self._cached_ts))
            self.gp.gp_time_s += time.perf_counter() - t1
            return self.leaves[best_idx]

        # `gp_root_info`: Surrogate-guided root-certificate witness allocation
        ev = self.monitor.evidence
        freq_hi = np.array([ev.upper[z] for z in self.leaves], dtype=np.float64)
        clipped_gp_ucb = np.minimum(freq_hi, m_vec + beta_sqrt * s_vec)

        best_b = 0
        best_sep = -math.inf
        best_in_idx = 0
        for a, sup in enumerate(self.action_supports):
            sub_vals = clipped_gp_ucb[sup]
            local_pos = int(np.argmax(sub_vals))
            u_in_gp = float(sub_vals[local_pos])
            nlh = self.monitor.neg_low_heaps[a]
            l_out = float(nlh.keys[nlh.top]) if nlh is not None else -math.inf
            sep_a = u_in_gp - l_out
            if sep_a > best_sep:
                best_sep = sep_a
                best_b = a
                best_in_idx = int(sup[local_pos])

        z_in = self.leaves[best_in_idx]
        w_in = float(ev.upper[z_in] - ev.lower[z_in])
        # Completeness safeguard: if GP-selected inside peak is already narrower than eps/2,
        # fall back to frequentist optimistic witness p_t(best_b) so misspecification never stalls
        if w_in <= 0.5 * self.epsilon:
            phh = self.monitor.pos_high_heaps[best_b]
            z_in = int(phh.leaves[phh.top])
            w_in = float(ev.upper[z_in] - ev.lower[z_in])

        nh = self.monitor.neg_heaps[best_b]
        if nh is None:
            self.gp.gp_time_s += time.perf_counter() - t0
            return z_in
        z_out = int(nh.leaves[nh.top])
        w_out = float(ev.upper[z_out] - ev.lower[z_out])

        # Expected one-step frequentist regret-boundary contraction Delta w(z)
        n_in = float(self.oracle.obs[z_in])
        n_out = float(self.oracle.obs[z_out])
        dw_in = w_in * (1.0 - math.sqrt((n_in + 1.0) / (n_in + 2.0)))
        dw_out = w_out * (1.0 - math.sqrt((n_out + 1.0) / (n_out + 2.0)))

        chosen = z_in if (dw_in, w_in, -z_in) >= (dw_out, w_out, -z_out) else z_out
        self.gp.gp_time_s += time.perf_counter() - t0
        return chosen

    def step(self) -> bool:
        if self.certified or self.monitor.evidence.conflict:
            return False
        target = self._select_leaf()
        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1

        reward = self.oracle.sample(target)
        self.calls += 1
        self.policy_work.oracle_calls += 1
        self.gp.observe(self.leaf_to_idx[target], reward)
        if not self.monitor.step(target, reward):
            return False

        act, reg, _, _, _ = self.monitor.query_dual_witness()
        self.action = int(act)
        if reg <= self.epsilon:
            self.certified = True
        return True


class GPBoxCertSession:
    """Level-2 Empirical Probe: GP-derived simultaneous rectangular confidence intervals
    plugged into the exact outside-support regret certificate `R_t^{GP}(a)`.

    Supports two radius schedules `beta_mode`:
    - `nominal_gp`: Bayesian posterior simultaneous bound `sqrt(2 log(4 M (t+1)^2 / delta))`
      (exact under a well-specified Gaussian process draw `f ~ GP(m_0, K)`).
    - `rkhs_calibrated`: Frequentist RKHS simultaneous confidence sequence
      `(B_rkhs + (R_sub / sigma_obs) * sqrt(2 * (gamma_t + 1 + log(1 / delta)))) * s_t(z)`
      with `R_sub = 0.5` for `[0, 1]`-bounded observations (Chowdhury & Gopalan, ICML 2017).
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        acquisition: str = "gp_root_info",
        beta_mode: str = "nominal_gp",
        rkhs_bound: float = 1.0,
        subgaussian_r: float = 0.5,
        delta: float = 0.05,
        kernel: np.ndarray | None = None,
    ):
        if acquisition not in ("gp_ucb", "gp_root_info"):
            raise ValueError(f"Unsupported GPBoxCertSession acquisition: {acquisition!r}")
        if beta_mode not in ("nominal_gp", "rkhs_calibrated"):
            raise ValueError(f"Unsupported GPBoxCertSession beta_mode: {beta_mode!r}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = float(epsilon)
        self.delta = float(delta)
        self.acquisition = acquisition
        self.beta_mode = beta_mode
        self.rkhs_bound = float(rkhs_bound)
        self.subgaussian_r = float(subgaussian_r)
        self.oracle = problem.oracle(seed)

        self.leaves = list(self.graph.leaves)
        self.m = len(self.leaves)
        self.leaf_to_idx = {z: i for i, z in enumerate(self.leaves)}
        self.action_supports = _build_action_support_indices(self.graph, self.leaves)
        all_idx = set(range(self.m))
        self.action_complements = [
            np.array(sorted(all_idx - set(sup.tolist())), dtype=np.int64)
            for sup in self.action_supports
        ]

        if kernel is None:
            seqs = [problem.variant_of_leaf[z] for z in self.leaves]
            kernel = protein_sequence_kernel(seqs)
        self.gp = DiscreteGPSurrogate(kernel)

        self.lo = np.zeros(self.m, dtype=np.float64)
        self.hi = np.ones(self.m, dtype=np.float64)
        self.conflict = False
        self.calls = 0
        self.certified = False
        self.action = 0
        self._refresh_box_and_check_stop()

    def _beta_sqrt(self) -> float:
        t = self.calls + 1
        if self.beta_mode == "nominal_gp":
            return math.sqrt(2.0 * math.log(4.0 * self.m * (t ** 2) / self.delta))
        return self.rkhs_bound + (self.subgaussian_r / self.gp.obs_std) * math.sqrt(
            2.0 * (self.gp.info_gain + 1.0 + math.log(1.0 / self.delta))
        )

    def _refresh_box_and_check_stop(self) -> tuple[int, float]:
        rad = self._beta_sqrt() * self.gp.std()
        raw_lo = np.clip(self.gp.mean - rad, 0.0, 1.0)
        raw_hi = np.clip(self.gp.mean + rad, 0.0, 1.0)
        new_lo = np.maximum(self.lo, raw_lo)
        new_hi = np.minimum(self.hi, raw_hi)
        if np.any(new_lo > new_hi + 1e-12):
            self.conflict = True
            return self.action, math.inf
        self.lo = new_lo
        self.hi = new_hi

        best_a = 0
        best_reg = math.inf
        for a, (sup, comp) in enumerate(zip(self.action_supports, self.action_complements)):
            l_in = float(np.max(self.lo[sup]))
            u_out = float(np.max(self.hi[comp])) if len(comp) else -math.inf
            reg_a = max(0.0, u_out - l_in)
            if reg_a < best_reg:
                best_reg = reg_a
                best_a = a
        self.action = best_a
        if best_reg <= self.epsilon:
            self.certified = True
        return best_a, best_reg

    def step(self) -> bool:
        if self.certified or self.conflict:
            return False
        if self.acquisition == "gp_ucb":
            idx = int(np.argmax(self.hi))
        else:
            # Optimistic-Separation / Root-Info directly over the GP confidence box
            best_b = 0
            best_sep = -math.inf
            in_idx = 0
            for a, (sup, comp) in enumerate(zip(self.action_supports, self.action_complements)):
                sub_hi = self.hi[sup]
                loc = int(np.argmax(sub_hi))
                u_in = float(sub_hi[loc])
                l_out = float(np.max(self.lo[comp])) if len(comp) else -math.inf
                if u_in - l_out > best_sep:
                    best_sep = u_in - l_out
                    best_b = a
                    in_idx = int(sup[loc])
            comp_b = self.action_complements[best_b]
            out_idx = int(comp_b[int(np.argmax(self.hi[comp_b]))])
            w_in = float(self.hi[in_idx] - self.lo[in_idx])
            w_out = float(self.hi[out_idx] - self.lo[out_idx])
            idx = in_idx if w_in >= w_out else out_idx

        leaf = self.leaves[idx]
        reward = self.oracle.sample(leaf)
        self.calls += 1
        self.gp.observe(idx, reward)
        if not self.gp._pending_counts:
            self._refresh_box_and_check_stop()
        return not self.conflict


def solve_ellipsoid_challenger(
    m_z: float,
    m_S: np.ndarray,
    sig_zz: float,
    sig_Sz: np.ndarray,
    sig_SS: np.ndarray,
    radius: float,
    tol: float = 1e-7,
    max_iter: int = 36,
) -> tuple[float, float, np.ndarray]:
    """Exact primal-dual solver for worst-case challenger excess over a GP confidence ellipsoid:

        D_t(z, S) = max_{f in C_t} (f_z - max_{y in S} f_y)
                  = min_{p in Delta(S)} [m_z - p^T m_S + r * sqrt(sig_zz - 2 p^T sig_Sz + p^T sig_SS p)].

    Uses away-step Frank-Wolfe with safeguarded 1D Newton line search on Delta(S).
    Because `g_z(p)` is a valid dual upper bound for every feasible `p in Delta(S)`,
    the returned `best_dual` is unconditionally sound (>= true `D_t(z, S)`), and
    `best_gap = g_z(p) - L_prim(p)` certifies numerical optimality via the analytical
    primal witness `f*(p)_S = -grad_p g_z(p)`.
    """
    k = len(m_S)
    if k == 1:
        q = math.sqrt(max(1e-18, sig_zz - 2.0 * float(sig_Sz[0]) + float(sig_SS[0, 0])))
        return m_z - float(m_S[0]) + radius * q, 0.0, np.ones(1, dtype=np.float64)

    diag_S = np.diag(sig_SS)
    q_vert = np.sqrt(np.maximum(1e-18, sig_zz + diag_S - 2.0 * sig_Sz))
    vert_vals = m_z - m_S + radius * q_vert
    best_y = int(np.argmin(vert_vals))
    p = np.zeros(k, dtype=np.float64)
    p[best_y] = 1.0

    best_dual = float(vert_vals[best_y])
    best_p = p.copy()
    best_gap = math.inf

    for _ in range(max_iter):
        sp = sig_SS @ p
        quad = max(1e-18, sig_zz - 2.0 * float(p @ sig_Sz) + float(p @ sp))
        q = math.sqrt(quad)
        dual_val = m_z - float(p @ m_S) + radius * q
        if dual_val < best_dual:
            best_dual = dual_val
            best_p = p.copy()

        grad = -m_S + (radius / q) * (sp - sig_Sz)
        fw_idx = int(np.argmin(grad))
        gp_dot = float(grad @ p)
        fw_gap = gp_dot - float(grad[fw_idx])
        if fw_gap < best_gap:
            best_gap = fw_gap
        if fw_gap <= tol:
            return best_dual, max(0.0, fw_gap), best_p

        active = np.flatnonzero(p > 1e-14)
        away_idx = int(active[int(np.argmax(grad[active]))])
        away_gap = float(grad[away_idx]) - gp_dot

        if fw_gap >= away_gap or len(active) <= 1 or p[away_idx] >= 1.0 - 1e-14:
            d = -p.copy()
            d[fw_idx] += 1.0
            alpha_max = 1.0
        else:
            p_aw = float(p[away_idx])
            d = p.copy()
            d[away_idx] -= 1.0
            alpha_max = p_aw / (1.0 - p_aw)

        sd = sig_SS @ d
        lin = -float(d @ m_S)
        b1 = 2.0 * float(d @ (sp - sig_Sz))
        c2 = max(0.0, float(d @ sd))

        q_hi = math.sqrt(max(1e-18, quad + b1 * alpha_max + c2 * alpha_max * alpha_max))
        deriv_hi = lin + radius * (0.5 * b1 + c2 * alpha_max) / q_hi
        if deriv_hi <= 0.0:
            alpha = alpha_max
        else:
            lo_a, hi_a = 0.0, alpha_max
            alpha = 0.5 * alpha_max
            for _ in range(12):
                qa = math.sqrt(max(1e-18, quad + b1 * alpha + c2 * alpha * alpha))
                da = lin + radius * (0.5 * b1 + c2 * alpha) / qa
                if abs(da) <= 1e-10:
                    break
                if da < 0.0:
                    lo_a = alpha
                else:
                    hi_a = alpha
                d2a = radius * max(0.0, c2 * quad - 0.25 * b1 * b1) / (qa * qa * qa)
                if d2a > 1e-14:
                    cand = alpha - da / d2a
                    alpha = cand if (lo_a < cand < hi_a) else 0.5 * (lo_a + hi_a)
                else:
                    alpha = 0.5 * (lo_a + hi_a)

        p = np.maximum(0.0, p + alpha * d)
        p /= float(p.sum())

    return best_dual, max(0.0, best_gap), best_p


def ar1_corr_matrix(n: int, rho: float) -> np.ndarray:
    """Strictly positive-definite Ornstein-Uhlenbeck / AR(1) correlation matrix `rho^|i-j|`."""
    if rho <= 0.0:
        return np.eye(n, dtype=np.float64)
    idx = np.arange(n, dtype=np.float64)
    return np.power(float(rho), np.abs(idx[:, None] - idx[None, :]))


def build_structured_corr_kernel(
    k_act: int,
    b_mot: int,
    rho_in: float,
    rho_out: float,
    tau0: float = 0.14,
    w_act: float = 0.25,
) -> np.ndarray:
    """Positive-definite Kronecker kernel over `M = k_act * b_mot` terminals separating:
    - per-action main-effect variance (`w_act`),
    - within-support motif correlation `rho_in` (`AR(1)` over `b = 0..b_mot-1`), and
    - cross-support motif transfer correlation `rho_out` across distinct root commitments.
    Every terminal has identical prior variance `tau0^2` for all `(rho_in, rho_out) in [0, 0.98]^2`.
    """
    m = k_act * b_mot
    k_act_main = np.kron(np.eye(k_act), np.ones((b_mot, b_mot)))
    k_grp_share = (1.0 - rho_out) * np.eye(k_act) + rho_out * np.ones((k_act, k_act))
    k_mot = ar1_corr_matrix(b_mot, rho_in)
    k_base = w_act * k_act_main + (1.0 - w_act) * np.kron(k_grp_share, k_mot) + 1e-4 * np.eye(m)
    return (tau0 * tau0) * k_base


class CorrelatedSupportDAGProblem(Problem):
    """Controlled zero-containment shared-support DAG (`K = 8` actions, `M = 64` terminals)
    with independently tunable within-support (`rho_in`) and cross-support (`rho_out`)
    GP value correlations and paired `[0, 1]`-bounded uniform observations.

    Because `Uniform[-hw, +hw]` is exact `sigma_obs`-sub-Gaussian (`hw / sqrt(3)`) by
    Hoeffding's lemma (`sinh(x)/x <= exp(x^2/6)`), both `NestedIntervals(emp_bernstein)`
    and the finite-dimensional Abbasi-Yadkori (2011, Thm. 1) RKHS confidence ellipsoid
    `C_t = {f : (f - m_t)^T Sigma_t^{-1} (f - m_t) <= r_t^2}` with
    `r_t = B_rkhs + sqrt(2 * (gamma_t + log(1/delta)))` are strictly anytime-valid
    `(1 - delta)` frequentist confidence sets.
    """

    def __init__(
        self,
        seed: int,
        rho_in: float,
        rho_out: float,
        action_gap: float = 0.095,
        tau0: float = 0.14,
        hw: float = 0.16,
    ):
        k_act = 8
        b_mot = 8
        m_leaves = k_act * b_mot
        children: list[tuple[int, ...]] = [tuple(range(1, k_act + 1))]
        leaf_offset = 1 + k_act
        for g in range(k_act):
            own = [leaf_offset + g * b_mot + b for b in range(b_mot)]
            sh1 = [leaf_offset + ((g + 1) % k_act) * b_mot + b for b in (0, 1)]
            sh2 = [leaf_offset + ((g + 2) % k_act) * b_mot + b for b in (2,)]
            children.append(tuple(sorted(own + sh1 + sh2)))
        for _ in range(m_leaves):
            children.append(())

        labels = ["root"] + [f"act_{g}" for g in range(k_act)] + [
            f"leaf_g{g}_m{b}" for g in range(k_act) for b in range(b_mot)
        ]
        graph = DAG(children, root=0, labels=labels)

        self.rho_in = float(rho_in)
        self.rho_out = float(rho_out)
        self.kernel = build_structured_corr_kernel(k_act, b_mot, rho_in, rho_out, tau0=tau0)
        k_inv = np.linalg.inv(self.kernel)

        rng = np.random.default_rng(seed * 10007 + 31)
        perm = rng.permutation(k_act)
        alpha_act = np.array([
            0.090,
            0.090 - action_gap,
            0.090 - 1.35 * action_gap,
            -0.010,
            -0.025,
            -0.040,
            -0.055,
            -0.070,
        ], dtype=np.float64)
        act_effect = np.zeros(k_act, dtype=np.float64)
        for rank_i, g_i in enumerate(perm):
            act_effect[int(g_i)] = alpha_act[rank_i]

        l_mot = np.linalg.cholesky(ar1_corr_matrix(b_mot, rho_in) + 1e-6 * np.eye(b_mot))
        z_shared_mot = l_mot @ rng.standard_normal(b_mot)
        z_shared_mot = 0.065 * z_shared_mot / max(1.0, float(np.max(np.abs(z_shared_mot))))
        b_best = int(rng.choice([4, 5, 6, 7]))
        z_shared_mot[b_best] = float(np.max(z_shared_mot)) + 0.025

        z_idio = np.stack([l_mot @ rng.standard_normal(b_mot) for _ in range(k_act)], axis=0)
        z_idio = 0.045 * z_idio / max(1.0, float(np.max(np.abs(z_idio))))

        f_mat = (
            0.48
            + act_effect[:, None]
            + math.sqrt(rho_out) * z_shared_mot[None, :]
            + math.sqrt(1.0 - rho_out) * z_idio
        )
        f_vec = np.clip(f_mat.reshape(-1), hw + 0.01, 1.0 - hw - 0.01)

        diff = f_vec - 0.48
        self.true_rkhs_norm = float(math.sqrt(max(0.0, float(diff @ (k_inv @ diff)))))
        self.rkhs_bound = self.true_rkhs_norm + 1e-6
        self.prior_mean = 0.48
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))
        self.action_labels = tuple(f"act_{g}" for g in range(k_act))

        means = {leaf_offset + i: float(f_vec[i]) for i in range(m_leaves)}
        super().__init__(f"corr_dag_in{rho_in:.2f}_out{rho_out:.2f}_s{seed}", graph, means, ())

    def oracle(self, seed: int):
        prob = self
        s64 = seed & 0xFFFFFFFFFFFFFFFF
        means = prob.means
        hw = prob.hw

        class _PairedUniformOracle:
            def __init__(self):
                self.obs = [0] * len(prob.graph)
                self.operations = 0

            def sample(self, leaf: int) -> float:
                self.obs[leaf] += 1
                k = self.obs[leaf]
                self.operations += 4
                u = splitmix_uniform01(s64, leaf, k)
                return means[leaf] + hw * (2.0 * u - 1.0)

        return _PairedUniformOracle()


class GPEllipsoidCertSession:
    """Head-to-head comparison between the exact confidence ellipsoid `C_t` (`mode='ellipsoid'`)
    and its tightest axis-aligned enclosing box `B(C_t)` (`mode='box'`) at the identical
    simultaneous radius `r_t`.

    Supports both:
    - `beta_mode='rkhs_exact'`: anytime-valid frequentist Abbasi-Yadkori RKHS ellipsoid radius
      `r_t = B_rkhs + (R_sub / sigma_obs) * sqrt(2 * (gamma_t + log(1/delta)))`
    - `beta_mode='nominal_gp'`: nominal Gaussian posterior radius `sqrt(2 log(4 M (t+1)^2 / delta))`
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        kernel: np.ndarray,
        prior_mean: float = 0.48,
        obs_std: float = 0.092376,
        rkhs_bound: float = 2.5,
        subgaussian_r: float | None = None,
        mode: str = "ellipsoid",
        beta_mode: str = "rkhs_exact",
        delta: float = 0.05,
    ):
        if mode not in ("box", "ellipsoid"):
            raise ValueError(f"Unsupported GPEllipsoidCertSession mode: {mode!r}")
        if beta_mode not in ("rkhs_exact", "nominal_gp"):
            raise ValueError(f"Unsupported GPEllipsoidCertSession beta_mode: {beta_mode!r}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = float(epsilon)
        self.delta = float(delta)
        self.mode = mode
        self.beta_mode = beta_mode
        self.rkhs_bound = float(rkhs_bound)
        self.subgaussian_r = float(obs_std if subgaussian_r is None else subgaussian_r)
        self.oracle = problem.oracle(seed)

        self.leaves = list(self.graph.leaves)
        self.m = len(self.leaves)
        self.action_supports = _build_action_support_indices(self.graph, self.leaves)
        all_idx = set(range(self.m))
        self.action_complements = [
            np.array(sorted(all_idx - set(sup.tolist())), dtype=np.int64)
            for sup in self.action_supports
        ]
        self.gp = DiscreteGPSurrogate(kernel, prior_mean=prior_mean, obs_std=obs_std)
        self.calls = 0
        self.certified = False
        self.conflict = False
        self.action = 0
        self.max_duality_gap = 0.0
        self._last_target = 0
        self._refresh()

    def _radius(self) -> float:
        if self.beta_mode == "nominal_gp":
            t = self.calls + 1
            return math.sqrt(2.0 * math.log(4.0 * self.m * (t * t) / self.delta))
        return self.rkhs_bound + (self.subgaussian_r / self.gp.obs_std) * math.sqrt(
            2.0 * (self.gp.info_gain + math.log(1.0 / self.delta))
        )

    def _action_ellipsoid_regret(
        self, a: int, r: float, stop_if_above_eps: bool = True
    ) -> tuple[float, int, np.ndarray]:
        t0 = time.perf_counter()
        sup = self.action_supports[a]
        comp = self.action_complements[a]
        m_vec = self.gp.mean
        sig = self.gp.Sigma
        m_S_full = m_vec[sup]
        s_S_full = self.gp.std()[sup]

        max_lo_S = float(np.max(m_S_full - r * s_S_full))
        keep_mask = (m_S_full + r * s_S_full) >= max_lo_S - 1e-12
        sup_nd = sup[keep_mask]
        m_S = m_vec[sup_nd]
        sig_SS = sig[sup_nd[:, None], sup_nd[None, :]]
        diag_S = sig_SS.diagonal()
        diag_comp = sig[comp, comp]
        sig_S_comp = sig[sup_nd[:, None], comp[None, :]]

        q_mat = np.sqrt(np.maximum(1e-18, diag_comp[None, :] + diag_S[:, None] - 2.0 * sig_S_comp))
        vert_ub = np.min(m_vec[comp][None, :] - m_S[:, None] + r * q_mat, axis=0)
        order = np.argsort(-vert_ub)

        if float(vert_ub[int(order[0])]) <= self.epsilon:
            p_full = np.zeros(len(sup), dtype=np.float64)
            p_full[0] = 1.0
            self.gp.gp_time_s += time.perf_counter() - t0
            return max(0.0, float(vert_ub[int(order[0])])), int(comp[int(order[0])]), p_full

        best_val = -math.inf
        best_z = int(comp[int(order[0])])
        best_p_nd = np.zeros(len(sup_nd), dtype=np.float64)
        best_p_nd[0] = 1.0

        for rank_k, pos in enumerate(order):
            ub_z = float(vert_ub[pos])
            if ub_z <= best_val and best_val > -math.inf:
                break
            # Sound early exit: when already > epsilon, solving top-2 challengers suffices
            # for acquisition; full verification runs automatically whenever best_val <= epsilon!
            if stop_if_above_eps and rank_k >= 2 and best_val > self.epsilon:
                break
            z_idx = int(comp[pos])
            val_z, gap_z, p_z = solve_ellipsoid_challenger(
                float(m_vec[z_idx]),
                m_S,
                float(sig[z_idx, z_idx]),
                sig_S_comp[:, pos],
                sig_SS,
                r,
            )
            if gap_z > self.max_duality_gap:
                self.max_duality_gap = gap_z
            if val_z > best_val:
                best_val = val_z
                best_z = z_idx
                best_p_nd = p_z

        p_full = np.zeros(len(sup), dtype=np.float64)
        p_full[keep_mask] = best_p_nd
        self.gp.gp_time_s += time.perf_counter() - t0
        return max(0.0, best_val), best_z, p_full

    def _refresh(self) -> None:
        r = self._radius()
        m_vec = self.gp.mean
        s_vec = self.gp.std()
        lo = m_vec - r * s_vec
        hi = m_vec + r * s_vec

        best_b = 0
        best_sep = -math.inf
        in_ucb_idx = 0
        for a, (sup, comp) in enumerate(zip(self.action_supports, self.action_complements)):
            sub_hi = hi[sup]
            loc = int(np.argmax(sub_hi))
            sep_a = float(sub_hi[loc]) - float(np.max(lo[comp]))
            if sep_a > best_sep:
                best_sep = sep_a
                best_b = a
                in_ucb_idx = int(sup[loc])

        if self.mode == "box":
            best_a = 0
            best_reg = math.inf
            for a, (sup, comp) in enumerate(zip(self.action_supports, self.action_complements)):
                reg_a = max(0.0, float(np.max(hi[comp])) - float(np.max(lo[sup])))
                if reg_a < best_reg:
                    best_reg = reg_a
                    best_a = a
            self.action = best_a
            if best_reg <= self.epsilon:
                self.certified = True
                return
            comp_b = self.action_complements[best_b]
            out_idx = int(comp_b[int(np.argmax(hi[comp_b]))])
            self._last_target = in_ucb_idx if s_vec[in_ucb_idx] >= s_vec[out_idx] else out_idx
            return

        reg_b, z_out_b, p_b = self._action_ellipsoid_regret(best_b, r, stop_if_above_eps=True)
        best_a = best_b
        best_reg = reg_b
        emp_lead = int(np.argmax([float(np.max(m_vec[sup])) for sup in self.action_supports]))
        if best_reg > self.epsilon and emp_lead != best_b:
            reg_e, _, _ = self._action_ellipsoid_regret(emp_lead, r, stop_if_above_eps=True)
            if reg_e < best_reg:
                best_reg = reg_e
                best_a = emp_lead
        self.action = best_a
        if best_reg <= self.epsilon:
            self.certified = True
            return

        t0 = time.perf_counter()
        sup_b = self.action_supports[best_b]
        v = np.zeros(self.m, dtype=np.float64)
        v[z_out_b] = 1.0
        v[sup_b] = -p_b
        sv = self.gp.Sigma @ v
        delta_var = (sv * sv) / (self.gp.obs_var + np.diag(self.gp.Sigma))
        dir_idx = int(np.argmax(delta_var))

        q_cur = math.sqrt(max(1e-18, float(v @ sv)))
        q_next = math.sqrt(max(0.0, float(v @ sv) - float(delta_var[dir_idx])))
        gain_dir = r * (q_cur - q_next)
        s_in = float(s_vec[in_ucb_idx])
        gain_ucb = r * s_in * (1.0 - 1.0 / math.sqrt(1.0 + (s_in * s_in) / self.gp.obs_var))
        self._last_target = in_ucb_idx if (in_ucb_idx != dir_idx and gain_ucb > 1.15 * gain_dir) else dir_idx
        self.gp.gp_time_s += time.perf_counter() - t0

    def step(self) -> bool:
        if self.certified:
            return False
        idx = self._last_target
        reward = self.oracle.sample(self.leaves[idx])
        self.calls += 1
        self.gp.observe(idx, reward, batch_after=100, batch_stride=25)
        if not self.gp._pending_counts:
            self._refresh()
        return True
