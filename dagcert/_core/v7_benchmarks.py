"""v7 Synthetic, Geometric, Proxy, Calibration, and Scaling Benchmark Generators.

Provides controlled all-MAX search DAG benchmarks for Experiments E0, E1, E2, E5, and E6:
- `MotivationalProxyDAGProblem`: 5-terminal illustrative DAG where a low-mean proxy terminal
  carries 40x higher Fisher information on the active inside/outside contrast than either witness.
- `OverlapCorrelationDAGProblem` (E1): Controlled 2D `(overlap, correlation)` DAG generator with
  exact exterior-margin matching (`Gamma_ext(a*) = target_margin` across all cells) so correlation
  never confounds underlying decision difficulty.
- `HullDominanceDAGProblem` (E2 Families A & B): Disjoint-support DAGs where outside terminals lie
  at exact Euclidean distance `eta >= 0` from the optimal action's feature polytope `P_{a*}`.
- `OffWitnessProxyDAGProblem` (E2 Family C1): Multi-branch DAGs with dedicated diagnostic proxy
  configurations on suboptimal branches.
- `MultiAnswerCommitmentDAGProblem` (E2 Family C2 / Theory T5.3): Multiple `eps`-optimal root
  commitments where the highest-mean action is hard to certify while a near-optimal sibling has
  small hull discrepancy.
- `MisspecifiedLinearDAGProblem` & `GaussianPriorDAGProblem` (E5): Calibration and adversarial
  residual `|b_z| <= xi` stress-test problems with Gaussian and bounded sub-Gaussian noise.
- `ScalingDAGProblem` (E6): Configurable `(M, K, d, support_style)` generator up to `M = 4096`.
"""
from __future__ import annotations

import math

import numpy as np

from .graph import DAG, Problem
from .v3_extensions import splitmix_uniform01


def _box_muller_normal(seed64: int, leaf: int, pull_idx: int) -> float:
    """Deterministic standard normal draw from `SplitMix64` uniform pairs."""
    u1 = max(1e-15, min(1.0 - 1e-15, splitmix_uniform01(seed64, leaf, 2 * pull_idx - 1)))
    u2 = splitmix_uniform01(seed64, leaf, 2 * pull_idx)
    return math.sqrt(-2.0 * math.log(u1)) * math.cos(2.0 * math.pi * u2)


class _UniformBoundedOracle:
    """Deterministic paired `[0, 1]`-bounded uniform noise oracle (`hw / sqrt(3)`-sub-Gaussian)."""

    def __init__(self, n_nodes: int, seed: int, means: dict[int, float], hw: float) -> None:
        self.obs = [0] * n_nodes
        self.operations = 0
        self._s64 = seed & 0xFFFFFFFFFFFFFFFF
        self._means = means
        self._hw = float(hw)

    def sample(self, leaf: int) -> float:
        self.obs[leaf] += 1
        k = self.obs[leaf]
        self.operations += 4
        u = splitmix_uniform01(self._s64, leaf, k)
        return self._means[leaf] + self._hw * (2.0 * u - 1.0)


class _GaussianOracle:
    """Deterministic paired Gaussian noise oracle `Y = mu_z + N(0, sigma^2)`."""

    def __init__(self, n_nodes: int, seed: int, means: dict[int, float], sigma: float) -> None:
        self.obs = [0] * n_nodes
        self.operations = 0
        self._s64 = seed & 0xFFFFFFFFFFFFFFFF
        self._means = means
        self._sigma = float(sigma)

    def sample(self, leaf: int) -> float:
        self.obs[leaf] += 1
        k = self.obs[leaf]
        self.operations += 6
        z = _box_muller_normal(self._s64, leaf, k)
        return self._means[leaf] + self._sigma * z


class MotivationalProxyDAGProblem(Problem):
    """5-terminal motivational DAG ('The first experiment I would actually run').

    Structure (`K = 2` actions with overlapping supports, `M = 5` terminals, `d = 3` latent features):
    - `S(a_0) = {z_in, z_sh, z_sub, z_proxy}`
    - `S(a_1) = {z_out, z_sh, z_proxy}`
    - `z_in` and `z_out` share 99% variance along nuisance mode `theta_1` (`rho = 0.980`),
      differing solely along `theta_2` (`phi(z_out) - phi(z_in) = (0, -0.20, 0)`).
    - `z_proxy` is a low-value diagnostic configuration reachable from both branches with
      smaller prior norm (`0.75 < 0.995`) and the lowest true mean (`0.3125`), so it is NEVER
      selected as `y_opt`, `z_t`, or a dual witness in `p_t*`, yet it probes `(0, -0.75, 0)`
      directly—delivering `(0.75 / 0.10)^2 = 56.25x` higher Fisher information on the active
      `z_out - z_in` contrast per observation than sampling `z_in` or `z_out`.
    """

    def __init__(self, hw: float = 0.18) -> None:
        # 0=root, 1=a0, 2=a1, 3=z_in, 4=z_sh, 5=z_sub, 6=z_out, 7=z_proxy
        children: list[tuple[int, ...]] = [
            (1, 2),
            (3, 4, 5, 7),
            (4, 6, 7),
            (),
            (),
            (),
            (),
            (),
        ]
        labels = ["root", "a0", "a1", "z_in", "z_sh", "z_sub", "z_out", "z_proxy"]
        graph = DAG(children, root=0, labels=labels)

        self.prior_mean = 0.50
        self.phi = np.array(
            [
                [0.99, -0.10, 0.00],   # z_in (leaf 3): winner in a0
                [0.00, 0.00, 0.42],    # z_sh (leaf 4): high-value shared terminal
                [-0.30, 0.00, 0.00],   # z_sub (leaf 5): suboptimal private terminal in a0
                [0.99, +0.10, 0.00],   # z_out (leaf 6): correlated outside challenger in a1
                [-0.65, -0.70, 0.00],  # z_proxy (leaf 7): low-mean diagnostic proxy (0 weight in p*)
            ],
            dtype=np.float64,
        )
        self.theta_star = np.array([0.24, -0.22, 0.42], dtype=np.float64)
        self.param_bound = float(np.linalg.norm(self.theta_star)) + 0.05
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))

        f_vals = self.prior_mean + (self.phi @ self.theta_star)
        means = {3 + i: float(f_vals[i]) for i in range(5)}
        super().__init__("motivational_proxy_dag", graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)


class OverlapCorrelationDAGProblem(Problem):
    """Experiment E1: Controlled 2D `(overlap, correlation)` DAG with matched exterior margin.

    Guarantees:
    1. Zero support containments (`S(b) not subseteq S(a)` for all `a != b`), because every root
       action owns dedicated private terminals.
    2. Controlled support overlap `overlap in [0, 0.75]` via a shared pool of terminals wired to
       cyclic subsets of actions.
    3. Controlled cross-terminal feature correlation `rho in [0, 0.90]` via shared motif basis
       vectors vs idiosyncratic action-specific directions.
    4. Exact exterior support margin `Gamma_ext(a*) = V(a*) - max_{z notin S(a*)} mu_z = target_margin`
       across ALL `(overlap, rho)` cells, preventing correlation from confounding true gaps.
    """

    def __init__(
        self,
        seed: int,
        overlap: float,
        rho: float,
        m_leaves: int = 128,
        k_actions: int = 8,
        d_feat: int = 8,
        target_margin: float = 0.065,
        hw: float = 0.16,
    ) -> None:
        if not (0.0 <= overlap <= 0.85):
            raise ValueError(f"overlap must lie in [0, 0.85], got {overlap}")
        if not (0.0 <= rho <= 0.98):
            raise ValueError(f"rho must lie in [0, 0.98], got {rho}")

        rng = np.random.default_rng(seed * 104729 + 19)
        leaf_offset = 1 + k_actions

        # Partition M terminals into K private blocks + a shared pool wired to multiple actions
        # Ensure at least 4 private terminals per action so zero-containment always holds.
        n_shared = int(round(m_leaves * min(0.80, 1.15 * overlap)))
        n_priv_per_act = max(4, (m_leaves - n_shared) // k_actions)
        n_priv_total = n_priv_per_act * k_actions
        n_shared = m_leaves - n_priv_total

        act_leaf_sets: list[set[int]] = [set() for _ in range(k_actions)]
        leaf_owner = np.zeros(m_leaves, dtype=np.int64)
        leaf_slot = np.zeros(m_leaves, dtype=np.int64)

        for g in range(k_actions):
            for b in range(n_priv_per_act):
                idx = g * n_priv_per_act + b
                act_leaf_sets[g].add(leaf_offset + idx)
                leaf_owner[idx] = g
                leaf_slot[idx] = b

        # Shared leaves belong to `fanout` actions controlled by `overlap`
        fanout = max(2, min(k_actions - 1, int(round(1.0 + (k_actions - 2) * (overlap / 0.75)))))
        for s_i in range(n_shared):
            idx = n_priv_total + s_i
            base_g = s_i % k_actions
            leaf_owner[idx] = base_g
            leaf_slot[idx] = n_priv_per_act + (s_i // k_actions)
            for off in range(fanout):
                act_leaf_sets[(base_g + off) % k_actions].add(leaf_offset + idx)

        children: list[tuple[int, ...]] = [tuple(range(1, k_actions + 1))]
        for g in range(k_actions):
            children.append(tuple(sorted(act_leaf_sets[g])))
        for _ in range(m_leaves):
            children.append(())

        labels = (
            ["root"]
            + [f"act_{g}" for g in range(k_actions)]
            + [f"leaf_{i}" for i in range(m_leaves)]
        )
        graph = DAG(children, root=0, labels=labels)

        # Build feature matrix Phi in R^{M x d} with controlled cross-support correlation `rho`
        # Coordinate 0 separates action commitments mildly; coordinates 1..d-1 carry motif features.
        d_sub = max(2, d_feat - 1)
        n_slots = int(np.max(leaf_slot)) + 1
        shared_motifs = rng.standard_normal((n_slots, d_sub))
        shared_motifs /= np.maximum(1e-12, np.linalg.norm(shared_motifs, axis=1, keepdims=True))

        phi = np.zeros((m_leaves, d_feat), dtype=np.float64)
        winner_act = int(rng.integers(0, k_actions))
        rival_act = (winner_act + 1) % k_actions

        for i in range(m_leaves):
            g = int(leaf_owner[i])
            sl = int(leaf_slot[i])
            idio = rng.standard_normal(d_sub)
            idio /= max(1e-12, float(np.linalg.norm(idio)))
            vec_sub = math.sqrt(rho) * shared_motifs[sl] + math.sqrt(1.0 - rho) * idio
            vec_sub /= max(1e-12, float(np.linalg.norm(vec_sub)))

            # Private leaves of winner_act have positive loading on coord 0
            is_in_winner = (leaf_offset + i) in act_leaf_sets[winner_act]
            is_private_winner = (i < n_priv_total) and (g == winner_act)
            if is_private_winner and sl == 0:
                c0 = 0.55
            elif is_in_winner:
                c0 = 0.15
            elif g == rival_act and sl == 0:
                c0 = 0.10
            else:
                c0 = -0.10
            phi[i, 0] = c0
            phi[i, 1:] = math.sqrt(max(0.05, 1.0 - c0 * c0)) * vec_sub

        # Construct theta* and calibrate coord 0 exactly so exterior margin == target_margin
        theta_sub = rng.standard_normal(d_sub)
        theta_sub = 0.14 * (theta_sub / max(1e-12, float(np.linalg.norm(theta_sub))))
        # Align shared_motifs[0] positively with theta_sub so slot 0 is competitive in both winner & rival
        if float(shared_motifs[0] @ theta_sub) < 0.0:
            theta_sub = -theta_sub

        sup_win = np.array([z - leaf_offset for z in sorted(act_leaf_sets[winner_act])], dtype=np.int64)
        comp_win = np.array(
            [i for i in range(m_leaves) if (leaf_offset + i) not in act_leaf_sets[winner_act]],
            dtype=np.int64,
        )

        # Binary search on theta_0 > 0 so max_{y in S(a*)} phi_y^T theta - max_{z notin S(a*)} phi_z^T theta == target_margin
        lo_t0, hi_t0 = 0.0, 0.80
        for _ in range(36):
            mid = 0.5 * (lo_t0 + hi_t0)
            cand_theta = np.concatenate([[mid], theta_sub])
            vals = phi @ cand_theta
            gap = float(np.max(vals[sup_win]) - np.max(vals[comp_win]))
            if gap < target_margin:
                lo_t0 = mid
            else:
                hi_t0 = mid
        theta_star = np.concatenate([[0.5 * (lo_t0 + hi_t0)], theta_sub])

        raw_vals = phi @ theta_star
        # Rescale mildly if needed to stay strictly inside [hw + 0.02, 1 - hw - 0.02] while keeping exact margin
        span = float(np.max(np.abs(raw_vals)))
        max_allowed = 0.48 - hw
        if span > max_allowed:
            scale = max_allowed / span
            theta_star *= scale

        prior_mean = 0.50
        f_vec = prior_mean + (phi @ theta_star)
        actual_margin = float(np.max(f_vec[sup_win]) - np.max(f_vec[comp_win]))

        self.overlap_target = float(overlap)
        self.rho = float(rho)
        self.phi = phi
        self.theta_star = theta_star
        self.prior_mean = prior_mean
        self.param_bound = float(np.linalg.norm(theta_star)) + 0.05
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))
        self.exterior_margin = actual_margin
        self.optimal_action = winner_act

        means = {leaf_offset + i: float(f_vec[i]) for i in range(m_leaves)}
        name = f"e1_ov{overlap:.2f}_rho{rho:.2f}_m{m_leaves}_d{d_feat}_s{seed}"
        super().__init__(name, graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)


class HullDominanceDAGProblem(Problem):
    """Experiment E2 (Families A & B): Disjoint-support DAG (`S(a) cap S(b) = empty`) where
    outside terminals lie at exact Euclidean distance `eta >= 0` from `P_{a*} = conv(Phi_{S(a*)})`.

    - When `eta == 0.0` (Family A), `P_Z subseteq P_{a*}`, so Theorem T2.1 predicts universal
      zero-sample certification (`R_0(a*) = 0`) regardless of `M`, whereas independent-terminal
      methods must sample all `M - d_simplex` outside terminals individually.
    - When `eta > 0.0` (Family B), outside terminals are displaced along an orthogonal coordinate
      by distance `eta`, testing Theorem T2.2--T2.3 as `eta` increases.
    """

    def __init__(
        self,
        seed: int,
        eta: float,
        m_leaves: int = 64,
        k_actions: int = 4,
        d_feat: int = 4,
        hw: float = 0.16,
    ) -> None:
        if d_feat < 3:
            raise ValueError("d_feat must be at least 3")
        rng = np.random.default_rng(seed * 65537 + 7)
        leaf_offset = 1 + k_actions
        d_hull = d_feat - 1  # Last coordinate carries orthogonal hull discrepancy `eta`

        # Action 0 owns `d_hull` orthonormal vertices spanning R^{d_hull}_{>=0} plus extra interior points
        n_a0 = max(d_hull, m_leaves // k_actions)
        rem = m_leaves - n_a0
        sizes = [n_a0]
        for g in range(1, k_actions):
            sz = rem // (k_actions - g)
            sizes.append(sz)
            rem -= sz

        children: list[tuple[int, ...]] = [tuple(range(1, k_actions + 1))]
        phi = np.zeros((m_leaves, d_feat), dtype=np.float64)

        cur = 0
        # Inside vertices for action 0: standard basis vectors in R^{d_hull} (scaled by 0.8)
        basis_pts = 0.80 * np.eye(d_hull, dtype=np.float64)
        for j in range(n_a0):
            if j < d_hull:
                phi[cur, :d_hull] = basis_pts[j]
            else:
                w = rng.dirichlet(np.ones(d_hull))
                phi[cur, :d_hull] = w @ basis_pts
            phi[cur, d_hull] = 0.0
            cur += 1
        children.append(tuple(range(leaf_offset, leaf_offset + n_a0)))

        # Outside actions 1..K-1: convex combinations of `basis_pts` + exact orthogonal shift `eta`
        for g in range(1, k_actions):
            start_c = cur
            sz = sizes[g]
            for j in range(sz):
                w = rng.dirichlet(np.full(d_hull, 1.5))
                phi[cur, :d_hull] = w @ basis_pts
                phi[cur, d_hull] = float(eta)
                cur += 1
            children.append(tuple(range(leaf_offset + start_c, leaf_offset + cur)))

        for _ in range(m_leaves):
            children.append(())

        labels = (
            ["root"]
            + [f"act_{g}" for g in range(k_actions)]
            + [f"leaf_{i}" for i in range(m_leaves)]
        )
        graph = DAG(children, root=0, labels=labels)

        # True parameter theta*: positive highest on vertex 0 of action 0, negative on orthogonal axis
        theta_star = np.zeros(d_feat, dtype=np.float64)
        theta_star[0] = 0.30
        theta_star[1:d_hull] = 0.22
        theta_star[d_hull] = -0.20

        self.prior_mean = 0.50
        self.eta = float(eta)
        self.phi = phi
        self.theta_star = theta_star
        self.param_bound = float(np.linalg.norm(theta_star)) + 0.05
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))

        f_vec = np.clip(self.prior_mean + (phi @ theta_star), hw + 0.01, 1.0 - hw - 0.01)
        means = {leaf_offset + i: float(f_vec[i]) for i in range(m_leaves)}
        super().__init__(f"e2_hull_eta{eta:.3f}_m{m_leaves}_s{seed}", graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)


class OffWitnessProxyDAGProblem(Problem):
    """Experiment E2 (Family C1): Multi-branch DAG with informative off-witness proxy terminals.

    Actions `0..(K-2)` compete for optimality: their high-value leaves load heavily (`sqrt(1 - gamma^2)`)
    onto shared nuisance modes and weakly (`gamma`) onto the decision-contrast subspace `R^2`.
    Action `K - 1` is a strictly suboptimal branch whose terminals load directly onto the `R^2`
    decision-contrast subspace (`proxy_snr` gain), making non-winning third-branch terminals the
    statistically optimal experiments for certifying the winning commitment!
    """

    def __init__(
        self,
        seed: int,
        gamma: float = 0.22,
        m_leaves: int = 48,
        k_actions: int = 4,
        d_feat: int = 6,
        hw: float = 0.16,
    ) -> None:
        rng = np.random.default_rng(seed * 99991 + 3)
        leaf_offset = 1 + k_actions
        per_act = m_leaves // k_actions
        d_nuis = d_feat - 2

        children: list[tuple[int, ...]] = [tuple(range(1, k_actions + 1))]
        phi = np.zeros((m_leaves, d_feat), dtype=np.float64)

        nuis_common = rng.standard_normal(d_nuis)
        nuis_common /= float(np.linalg.norm(nuis_common))

        # Competing actions 0..K-2
        angles = np.linspace(0.0, math.pi * 0.75, k_actions - 1)
        for g in range(k_actions - 1):
            start_i = g * per_act
            # Also share 2 leaves with next competing action so supports overlap
            own_ids = [leaf_offset + start_i + b for b in range(per_act)]
            nxt_g = (g + 1) % (k_actions - 1)
            sh_ids = [leaf_offset + nxt_g * per_act + per_act - 1]
            children.append(tuple(sorted(set(own_ids + sh_ids))))

            sig_dir = np.array([math.cos(angles[g]), math.sin(angles[g])], dtype=np.float64)
            for b in range(per_act):
                idx = start_i + b
                jitter = 0.15 * rng.standard_normal(d_nuis)
                v_nuis = nuis_common + jitter * (0.0 if b == 0 else 1.0)
                v_nuis /= float(np.linalg.norm(v_nuis))
                scale_b = 1.0 if b == 0 else float(rng.uniform(0.65, 0.92))
                phi[idx, :2] = gamma * scale_b * sig_dir
                phi[idx, 2:] = math.sqrt(1.0 - gamma * gamma) * v_nuis

        # Proxy branch K - 1: strictly suboptimal mean, pure probe of decision subspace R^2!
        start_p = (k_actions - 1) * per_act
        children.append(tuple(range(leaf_offset + start_p, leaf_offset + m_leaves)))
        proxy_angles = np.linspace(0.0, math.pi, m_leaves - start_p, endpoint=False)
        for j, idx in enumerate(range(start_p, m_leaves)):
            ang = proxy_angles[j]
            # Negative loading along nuisance + strong unit loading on R^2
            phi[idx, :2] = -0.92 * np.array([math.cos(ang), math.sin(ang)], dtype=np.float64)
            phi[idx, 2:] = -0.35 * nuis_common

        for _ in range(m_leaves):
            children.append(())

        labels = (
            ["root"]
            + [f"act_{g}" for g in range(k_actions - 1)]
            + ["act_proxy"]
            + [f"leaf_{i}" for i in range(m_leaves)]
        )
        graph = DAG(children, root=0, labels=labels)

        theta_star = np.zeros(d_feat, dtype=np.float64)
        theta_star[:2] = np.array([0.28, -0.06], dtype=np.float64)  # Action 0 wins over Action 1, 2
        theta_star[2:] = 0.22 * nuis_common

        self.prior_mean = 0.52
        self.gamma = float(gamma)
        self.phi = phi
        self.theta_star = theta_star
        self.param_bound = float(np.linalg.norm(theta_star)) + 0.05
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))
        self.proxy_leaf_indices = tuple(range(start_p, m_leaves))

        f_vec = np.clip(self.prior_mean + (phi @ theta_star), hw + 0.01, 1.0 - hw - 0.01)
        means = {leaf_offset + i: float(f_vec[i]) for i in range(m_leaves)}
        super().__init__(f"e2_proxy_gam{gamma:.2f}_s{seed}", graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)


class MultiAnswerCommitmentDAGProblem(Problem):
    """Experiment E2 (Family C2 / Theory T5.3): Multiple `eps`-optimal commitments.

    - Action `a_0` has the strictly highest true value `V(a_0)` (`0` simple regret), but sits on an
      isolated orthogonal feature axis requiring extensive direct sampling to certify against `a_2`.
    - Action `a_1` is slightly lower (`V(a_0) - V(a_1) = 0.55 * eps <= eps`, so `a_1 in A_eps(theta*)`
      is a completely valid `eps`-optimal commitment!) AND its feature polytope nearly encloses
      `S(a_0) cup S(a_2)` (`eta_2(a_1) << eta_2(a_0)`).
    """

    def __init__(
        self,
        seed: int,
        epsilon: float = 0.030,
        m_leaves: int = 36,
        hw: float = 0.16,
    ) -> None:
        rng = np.random.default_rng(seed * 49157 + 11)
        k_actions = 3
        d_feat = 4
        leaf_offset = 1 + k_actions

        # a_0: 4 isolated leaves along axis 0
        # a_1: 16 leaves spanning axes (0, 1, 2) whose convex hull nearly contains a_0 and a_2!
        # a_2: 16 rival suboptimal leaves inside conv(axes 1, 2)
        n0, n1 = 4, 16
        n2 = m_leaves - n0 - n1
        children: list[tuple[int, ...]] = [
            (1, 2, 3),
            tuple(range(leaf_offset, leaf_offset + n0)),
            tuple(range(leaf_offset + n0, leaf_offset + n0 + n1)),
            tuple(range(leaf_offset + n0 + n1, leaf_offset + m_leaves)),
        ]
        for _ in range(m_leaves):
            children.append(())

        phi = np.zeros((m_leaves, d_feat), dtype=np.float64)
        # Action 0: isolated orthogonal leaf along axis 0 (must separate across sqrt(2) from Action 2)
        phi[0] = np.array([1.00, 0.00, 0.00, 0.00], dtype=np.float64)
        for i in range(1, n0):
            phi[i] = np.array([0.80 - 0.05 * i, 0.0, 0.0, 0.0], dtype=np.float64)

        # Action 1: vertices spanning (0.91*e0, e1, e2) -> strictly encloses Action 2 in conv(e1, e2)
        # AND lies within Euclidean distance 0.09 of Action 0's peak!
        verts_1 = np.array(
            [
                [0.91, 0.00, 0.00, 0.00],
                [0.00, 1.00, 0.00, 0.00],
                [0.00, 0.00, 1.00, 0.00],
            ],
            dtype=np.float64,
        )
        for j in range(n1):
            if j < 3:
                phi[n0 + j] = verts_1[j]
            else:
                w = rng.dirichlet(np.ones(3))
                phi[n0 + j] = w @ verts_1

        # Action 2: rival suboptimal leaves inside conv(e1, e2) (distance 0 to P_{a_1}, distance ~1.3 to a_0!)
        for j in range(n2):
            t_mix = float(rng.uniform(0.15, 0.85))
            phi[n0 + n1 + j] = t_mix * verts_1[1] + (1.0 - t_mix) * verts_1[2]

        # V(a_0) - V(a_1) = 0.09 * t0 = 0.65 * epsilon <= epsilon; V(a_0) - V(a_2) = 1.45 * epsilon > epsilon
        t0 = (0.65 * epsilon) / 0.09
        theta_star = np.array([t0, t0 - 1.45 * epsilon, t0 - 1.55 * epsilon, 0.0], dtype=np.float64)

        labels = ["root", "a0_greedy", "a1_hull_easy", "a2_subopt"] + [f"leaf_{i}" for i in range(m_leaves)]
        graph = DAG(children, root=0, labels=labels)

        self.prior_mean = 0.45
        self.phi = phi
        self.theta_star = theta_star
        self.param_bound = float(np.linalg.norm(theta_star)) + 0.05
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))

        f_vec = np.clip(self.prior_mean + (phi @ theta_star), hw + 0.01, 1.0 - hw - 0.01)
        means = {leaf_offset + i: float(f_vec[i]) for i in range(m_leaves)}
        super().__init__(f"e2_multianswer_eps{epsilon:.3f}_s{seed}", graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)


class MisspecifiedLinearDAGProblem(Problem):
    """Experiment E5: Linear feature DAG with adversarial structured residual `|b_z| <= xi`.

    Specifically places `+xi` on the best outside challenger and `-xi` on inside terminals of `a*`
    so naive unadjusted linear ellipsoids become overconfident when `xi > 0`, testing Theorem T3.3.
    """

    def __init__(
        self,
        seed: int,
        xi: float = 0.0,
        m_leaves: int = 48,
        k_actions: int = 6,
        d_feat: int = 6,
        hw: float = 0.15,
    ) -> None:
        base = OverlapCorrelationDAGProblem(
            seed=seed,
            overlap=0.35,
            rho=0.75,
            m_leaves=m_leaves,
            k_actions=k_actions,
            d_feat=d_feat,
            target_margin=0.055,
            hw=hw,
        )
        leaf_offset = 1 + k_actions
        phi = base.phi.copy()
        theta_star = base.theta_star.copy()
        lin_vals = base.prior_mean + (phi @ theta_star)

        # Construct adversarial bounded residual b_z in [-xi, +xi] narrowing the true margin by 2*xi
        win_act = base.optimal_action
        win_leaves = set(base.graph.children[1 + win_act])
        b_vec = np.zeros(m_leaves, dtype=np.float64)
        for i in range(m_leaves):
            if (leaf_offset + i) in win_leaves:
                b_vec[i] = -float(xi)
            else:
                b_vec[i] = +float(xi)

        f_vec = np.clip(lin_vals + b_vec, hw + 0.01, 1.0 - hw - 0.01)
        self.prior_mean = base.prior_mean
        self.phi = phi
        self.theta_star = theta_star
        self.residual_b = f_vec - lin_vals
        self.xi = float(np.max(np.abs(self.residual_b)))
        self.param_bound = base.param_bound
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))

        means = {leaf_offset + i: float(f_vec[i]) for i in range(m_leaves)}
        super().__init__(f"e5_misspec_xi{xi:.3f}_s{seed}", base.graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)


class GaussianPriorDAGProblem(Problem):
    """Experiment E5: Exact Gaussian-process draw `f ~ N(m_0, K)` with Gaussian observation noise
    `Y ~ N(f_z, sigma^2)` for auditing Bayesian posterior stopping (`max_a q_t(a) >= 1 - delta`)
    and kernel lengthscale misspecification.
    """

    def __init__(
        self,
        seed: int,
        true_lengthscale: float = 1.2,
        m_leaves: int = 40,
        k_actions: int = 5,
        sigma: float = 0.10,
    ) -> None:
        rng = np.random.default_rng(seed * 131071 + 29)
        leaf_offset = 1 + k_actions
        per_act = m_leaves // k_actions

        children: list[tuple[int, ...]] = [tuple(range(1, k_actions + 1))]
        for g in range(k_actions):
            own = [leaf_offset + g * per_act + b for b in range(per_act)]
            sh = [leaf_offset + ((g + 1) % k_actions) * per_act + b for b in range(min(2, per_act - 1))]
            children.append(tuple(sorted(set(own + sh))))
        for _ in range(m_leaves):
            children.append(())

        labels = ["root"] + [f"act_{g}" for g in range(k_actions)] + [f"leaf_{i}" for i in range(m_leaves)]
        graph = DAG(children, root=0, labels=labels)

        coords = rng.uniform(-2.0, 2.0, size=(m_leaves, 3))
        self.coords = coords
        self.prior_mean = 0.50
        self.sigma = float(sigma)
        self.true_kernel = self.rbf_kernel(coords, lengthscale=true_lengthscale)

        l_true = np.linalg.cholesky(self.true_kernel)
        f_draw = self.prior_mean + (l_true @ rng.standard_normal(m_leaves))
        means = {leaf_offset + i: float(f_draw[i]) for i in range(m_leaves)}
        super().__init__(f"e5_gp_ell{true_lengthscale:.2f}_s{seed}", graph, means, ())

    @staticmethod
    def rbf_kernel(coords: np.ndarray, lengthscale: float, scale: float = 0.18, nugget: float = 1e-4) -> np.ndarray:
        sq = (
            np.sum(coords * coords, axis=1, keepdims=True)
            + np.sum(coords * coords, axis=1, keepdims=True).T
            - 2.0 * (coords @ coords.T)
        )
        np.maximum(sq, 0.0, out=sq)
        return (scale * scale) * (np.exp(-sq / (2.0 * lengthscale * lengthscale)) + nugget * np.eye(len(coords)))

    def oracle(self, seed: int) -> _GaussianOracle:
        return _GaussianOracle(len(self.graph), seed, self.means, self.sigma)


class ScalingDAGProblem(Problem):
    """Experiment E6: Large-scale configurable `(M, K, d, support_style)` search DAG up to `M = 4096`."""

    def __init__(
        self,
        seed: int,
        m_leaves: int = 1024,
        k_actions: int = 8,
        d_feat: int = 16,
        support_style: str = "compact",
        hw: float = 0.16,
    ) -> None:
        if support_style not in ("compact", "fragmented"):
            raise ValueError(f"Unknown support_style: {support_style!r}")
        rng = np.random.default_rng(seed * 524287 + 41)
        leaf_offset = 1 + k_actions
        block = max(2, m_leaves // k_actions)

        children: list[tuple[int, ...]] = [tuple(range(1, k_actions + 1))]
        for g in range(k_actions):
            own = [leaf_offset + i for i in range(g * block, min(m_leaves, (g + 1) * block))]
            if g == k_actions - 1:
                own = [leaf_offset + i for i in range(g * block, m_leaves)]
            if support_style == "compact":
                extra_cnt = max(1, block // 4)
                nxt_start = ((g + 1) % k_actions) * block
                extra = [leaf_offset + ((nxt_start + j) % m_leaves) for j in range(extra_cnt)]
            else:
                # Fragmented: each action reaches ~35% of all terminals scattered across the graph
                extra_cnt = max(2, int(0.25 * m_leaves))
                extra = [leaf_offset + int(x) for x in rng.choice(m_leaves, size=extra_cnt, replace=False)]
            children.append(tuple(sorted(set(own + extra))))
        for _ in range(m_leaves):
            children.append(())

        labels = ["root"] + [f"a_{g}" for g in range(k_actions)] + [f"z_{i}" for i in range(m_leaves)]
        graph = DAG(children, root=0, labels=labels)

        phi = rng.standard_normal((m_leaves, d_feat))
        phi /= np.maximum(1e-12, np.linalg.norm(phi, axis=1, keepdims=True))
        # Boost action 0's private anchor
        phi[0] *= 0.5
        phi[0, 0] = 0.86
        theta_star = np.zeros(d_feat, dtype=np.float64)
        theta_star[0] = 0.26
        theta_star[1:] = 0.16 * rng.standard_normal(d_feat - 1) / math.sqrt(max(1, d_feat - 1))

        self.prior_mean = 0.50
        self.phi = phi
        self.theta_star = theta_star
        self.param_bound = float(np.linalg.norm(theta_star)) + 0.05
        self.hw = float(hw)
        self.obs_std = float(hw / math.sqrt(3.0))

        f_vec = np.clip(self.prior_mean + (phi @ theta_star), hw + 0.01, 1.0 - hw - 0.01)
        means = {leaf_offset + i: float(f_vec[i]) for i in range(m_leaves)}
        super().__init__(f"e6_scale_m{m_leaves}_k{k_actions}_d{d_feat}_{support_style}", graph, means, ())

    def oracle(self, seed: int) -> _UniformBoundedOracle:
        return _UniformBoundedOracle(len(self.graph), seed, self.means, self.hw)
