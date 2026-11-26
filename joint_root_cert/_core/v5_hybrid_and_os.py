"""v5 Extensions: O(log M) Dual-Bound Witness Covers, Safeguarded Hybrid Inside-Witness
Allocation, and Optimistic-Separation DAG-LUCB (Theorems 3.1-3.3).

Implements:
1. `DualWitnessCovers`: Charged Dual Covers augmented with lower-bound witness argmax tracking
   `(low[d], low_hi[d], low_leaf[d])` along the shared dyadic segment tree so that all three
   canonical witnesses `(p_t, y_t, q_t)`—optimistic inside `argmax_{z in S(a)} (u_t(z), -z)`,
   certificate inside `argmax_{z in S(a)} (l_t(z), u_t(z), -z)`, and optimistic outside
   `argmax_{z notin S(a)} (u_t(z), -z)`—are maintained in `O(log M)` segment-tree updates and
   `O(b_a^+)` block queries without `O(|S(a)|)` support scans. Optionally maintains the
   optimistic-separation index `J_t(a) = U_t(a) - L_t^-(a)` (`track_separation=True`).
2. `HybridWitnessDAGLUCBSession`: Evaluates `ucb`, `lcb_fast` (`O(log M)` LCB-inside),
   `hybrid` (Theorem-3.1-preserving slack gate `w_t(y_t) >= max(0.5 * R_t(a_t), u_t(p_t) - u_t(y_t))`),
   `hybrid_dom` (challenger-dominance + slack gate `u_t(y_t) > u_t(q_t)` or slack gate),
   and `opt_sep` (`Optimistic-Separation DAG-LUCB` of Theorem 3.2).
3. `noncontainment_star_dag`: Exact Bernoulli non-containment tied-star family of Theorem 3.3
   (`S_A = {p, q}`, `S_{B_i} = {p, r_i}`, `mu_p = mu_q = 1/2`, `mu_{r_i} = 1/2 - g`).
"""
from __future__ import annotations

import math

from .certified_uct import IndexedMaxHeap, UCTWork
from .compiled_retirement import leaf_order
from .graph import DAG, Problem
from .v2_monitors import (
    IndexedMinHeap,
    NestedIntervals,
    _complement_runs,
    _dyadic_blocks,
    _heap_merge_runs,
)
from .v3_extensions import SplitMixProblem, WitnessMaxHeap
from .v4_baselines import _shortest_leaf_paths


class DualWitnessCovers:
    """Charged Dual Covers exposing `(a_t, R_t(a_t), p_t, y_t, q_t)` in O(log M) work.

    Also supports `query_optimistic_separation()` returning `(b_t, J_t(b_t), p_t(b_t), q_t(b_t))`
    for `b_t = argmax_a (U_t(a) - L_t^-(a))` when `track_separation=True`.
    """

    def __init__(
        self,
        graph: DAG,
        delta: float = 0.05,
        schedule: str = "box",
        layout: str = "best",
        track_separation: bool = False,
    ):
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule)
        self.track_separation = track_separation

        m = len(graph.leaves)
        self.size = 1 << max(0, (m - 1).bit_length())
        root_ch = graph.children[graph.root]
        self.num_actions = len(root_ch)

        modes = (False, True) if layout == "best" else ((True,) if layout == "dfs" else (False,))
        cands = []
        for dfs in modes:
            leaves = leaf_order(graph, dfs, w)
            rank = {v: i for i, v in enumerate(leaves)}
            w.initialization += m
            runs: list[tuple[tuple[int, int], ...]] = [()] * len(graph)
            for v in reversed(graph.order):
                ch = graph.children[v]
                w.edge_reads += len(ch)
                if not ch:
                    j = rank[v]
                    runs[v] = ((j, j + 1),)
                elif len(ch) == 1:
                    runs[v] = runs[ch[0]]
                else:
                    runs[v] = _heap_merge_runs([runs[c] for c in ch], w)
            pc, nc = [], []
            for c in root_ch:
                pr = runs[c]
                nr = _complement_runs(pr, m, w)
                pc.append(_dyadic_blocks(pr, self.size, w))
                nc.append(_dyadic_blocks(nr, self.size, w))
            tot = sum(map(len, pc)) + sum(map(len, nc))
            cands.append((tot, dfs, leaves, rank, pc, nc))
            w.statistic_writes += sum(map(len, runs)) + len(runs)

        (self.total_blocks, _, self.leaves, self.rank,
         self.pos_covers, self.neg_covers) = min(cands, key=lambda x: (x[0], x[1]))

        # Segment tree arrays over [1 .. 2*size - 1]
        self.low = [-math.inf] * (2 * self.size)
        self.low_hi = [-math.inf] * (2 * self.size)
        self.low_leaf = [10**9] * (2 * self.size)
        self.high = [-math.inf] * (2 * self.size)
        self.high_leaf = [10**9] * (2 * self.size)

        for j, orig_z in enumerate(self.leaves):
            idx = self.size + j
            self.low[idx] = 0.0
            self.low_hi[idx] = 1.0
            self.low_leaf[idx] = orig_z
            self.high[idx] = 1.0
            self.high_leaf[idx] = orig_z

        for d in reversed(range(1, self.size)):
            lc, rc = 2 * d, 2 * d + 1
            if (self.low[lc], self.low_hi[lc], -self.low_leaf[lc]) >= (
                self.low[rc], self.low_hi[rc], -self.low_leaf[rc]
            ):
                self.low[d] = self.low[lc]
                self.low_hi[d] = self.low_hi[lc]
                self.low_leaf[d] = self.low_leaf[lc]
            else:
                self.low[d] = self.low[rc]
                self.low_hi[d] = self.low_hi[rc]
                self.low_leaf[d] = self.low_leaf[rc]

            if (self.high[lc], -self.high_leaf[lc]) >= (self.high[rc], -self.high_leaf[rc]):
                self.high[d], self.high_leaf[d] = self.high[lc], self.high_leaf[lc]
            else:
                self.high[d], self.high_leaf[d] = self.high[rc], self.high_leaf[rc]
        w.initialization += 12 * self.size + m

        self.pos_subs: list[list[tuple[int, int]]] = [[] for _ in range(2 * self.size)]
        self.neg_subs: list[list[tuple[int, int]]] = [[] for _ in range(2 * self.size)]
        self.pos_heaps: list[IndexedMaxHeap] = []
        self.neg_heaps: list[WitnessMaxHeap | None] = []

        self.pos_high_heaps: list[WitnessMaxHeap] = []
        self.neg_low_heaps: list[IndexedMaxHeap | None] = []
        init_reg: list[float] = []
        init_sep: list[float] = []

        for a in range(self.num_actions):
            pca = self.pos_covers[a]
            nca = self.neg_covers[a]
            for idx, d in enumerate(pca):
                self.pos_subs[d].append((a, idx))
            for idx, d in enumerate(nca):
                self.neg_subs[d].append((a, idx))

            ph = IndexedMaxHeap([self.low[d] for d in pca], w)
            self.pos_heaps.append(ph)

            if nca:
                nh = WitnessMaxHeap([self.high[d] for d in nca], [self.high_leaf[d] for d in nca], w)
                self.neg_heaps.append(nh)
                init_reg.append(max(0.0, nh.vals[nh.top] - ph.keys[ph.top]))
            else:
                self.neg_heaps.append(None)
                init_reg.append(0.0)

            if track_separation:
                phh = WitnessMaxHeap([self.high[d] for d in pca], [self.high_leaf[d] for d in pca], w)
                self.pos_high_heaps.append(phh)
                if nca:
                    nlh = IndexedMaxHeap([self.low[d] for d in nca], w)
                    self.neg_low_heaps.append(nlh)
                    init_sep.append(phh.vals[phh.top] - nlh.keys[nlh.top])
                else:
                    self.neg_low_heaps.append(None)
                    init_sep.append(math.inf)

        self.regret_heap = IndexedMinHeap(init_reg, w) if self.num_actions else None
        self.sep_heap = (
            WitnessMaxHeap(init_sep, list(range(self.num_actions)), w)
            if (track_separation and self.num_actions)
            else None
        )
        self.compile_work = w.total

    def step(self, leaf: int, reward: float) -> bool:
        iv = self.evidence.observe(leaf, reward)
        if iv is None:
            return False
        d = self.size + self.rank[leaf]
        lo, hi = iv
        lhi, ll = hi, leaf
        hl = leaf
        touched: set[int] = set()
        sep_touched: set[int] = set()

        while True:
            self.work.query_reads += 5
            lo_val_changed = (lo != self.low[d])
            lo_wit_changed = lo_val_changed or (lhi != self.low_hi[d]) or (ll != self.low_leaf[d])
            hi_changed = (hi != self.high[d]) or (hl != self.high_leaf[d])
            if not lo_wit_changed and not hi_changed:
                break

            if lo_wit_changed:
                self.low[d] = lo
                self.low_hi[d] = lhi
                self.low_leaf[d] = ll
                self.work.statistic_writes += 3
                if lo_val_changed:
                    for a, idx in self.pos_subs[d]:
                        self.work.edge_reads += 1
                        self.pos_heaps[a].update(idx, lo)
                        touched.add(a)
                    if self.track_separation:
                        for a, idx in self.neg_subs[d]:
                            self.work.edge_reads += 1
                            nlh = self.neg_low_heaps[a]
                            assert nlh is not None
                            nlh.update(idx, lo)
                            sep_touched.add(a)

            if hi_changed:
                self.high[d] = hi
                self.high_leaf[d] = hl
                self.work.statistic_writes += 2
                for a, idx in self.neg_subs[d]:
                    self.work.edge_reads += 1
                    nh = self.neg_heaps[a]
                    assert nh is not None
                    nh.update(idx, hi, hl)
                    touched.add(a)
                if self.track_separation:
                    for a, idx in self.pos_subs[d]:
                        self.work.edge_reads += 1
                        self.pos_high_heaps[a].update(idx, hi, hl)
                        sep_touched.add(a)

            if d == 1:
                break
            d //= 2
            lc, rc = 2 * d, 2 * d + 1
            if (self.low[lc], self.low_hi[lc], -self.low_leaf[lc]) >= (
                self.low[rc], self.low_hi[rc], -self.low_leaf[rc]
            ):
                lo, lhi, ll = self.low[lc], self.low_hi[lc], self.low_leaf[lc]
            else:
                lo, lhi, ll = self.low[rc], self.low_hi[rc], self.low_leaf[rc]

            if (self.high[lc], -self.high_leaf[lc]) >= (self.high[rc], -self.high_leaf[rc]):
                hi, hl = self.high[lc], self.high_leaf[lc]
            else:
                hi, hl = self.high[rc], self.high_leaf[rc]
            self.work.query_reads += 8
            self.work.heap_comparisons += 2

        if self.regret_heap is not None:
            for a in touched:
                nh = self.neg_heaps[a]
                if nh is None:
                    reg = 0.0
                else:
                    ph = self.pos_heaps[a]
                    reg = max(0.0, nh.vals[nh.top] - ph.keys[ph.top])
                    self.work.query_reads += 2
                self.regret_heap.update(a, reg)

        if self.sep_heap is not None:
            for a in sep_touched:
                nlh = self.neg_low_heaps[a]
                if nlh is None:
                    sep = math.inf
                else:
                    phh = self.pos_high_heaps[a]
                    sep = phh.vals[phh.top] - nlh.keys[nlh.top]
                    self.work.query_reads += 2
                self.sep_heap.update(a, sep, a)
        return True

    def query_dual_witness(self) -> tuple[int, float, int, int, int]:
        """Return `(a_t, R_t(a_t), p_t, y_t, q_t)` over `O(b_{a_t}^+)` dyadic blocks."""
        self.work.query_reads += 3
        if self.regret_heap is None:
            return (-1, 0.0, -1, -1, -1)
        best = self.regret_heap.top
        reg = self.regret_heap.keys[best]
        pca = self.pos_covers[best]
        best_hi_d = max(pca, key=lambda d: (self.high[d], -self.high_leaf[d]))
        best_lo_d = max(pca, key=lambda d: (self.low[d], self.low_hi[d], -self.low_leaf[d]))
        self.work.query_reads += 5 * len(pca)
        self.work.heap_comparisons += 2 * len(pca)
        p_t = self.high_leaf[best_hi_d]
        y_t = self.low_leaf[best_lo_d]
        nh = self.neg_heaps[best]
        q_t = -1 if nh is None else nh.leaves[nh.top]
        return (best, reg, p_t, y_t, q_t)

    def query_optimistic_separation(self) -> tuple[int, float, int, float, int, int]:
        """Return `(a_stop, R_t(a_stop), b_t, J_t(b_t), p_t(b_t), q_t(b_t))` for Theorem 3.2."""
        if not self.track_separation or self.sep_heap is None or self.regret_heap is None:
            raise RuntimeError("Separation tracking disabled")
        self.work.query_reads += 4
        a_stop = self.regret_heap.top
        reg = self.regret_heap.keys[a_stop]
        b_t = self.sep_heap.top
        j_val = self.sep_heap.vals[b_t]
        phh = self.pos_high_heaps[b_t]
        p_b = phh.leaves[phh.top]
        nh = self.neg_heaps[b_t]
        q_b = -1 if nh is None else nh.leaves[nh.top]
        return (a_stop, reg, b_t, j_val, p_b, q_b)


class HybridWitnessDAGLUCBSession:
    """Active exact-regret DAG-LUCB session supporting O(log M) safeguarded inside witnesses
    and Optimistic-Separation DAG-LUCB (Theorem 3.2).

    Supported `mode` values:
    - `'ucb'`: `z_t^{in} = p_t` (Theorem 3.1 baseline, identical trajectory to `ActiveDAGLUCBSession`)
    - `'lcb_fast'`: `z_t^{in} = y_t` via `O(log M)` `DualWitnessCovers` (no O(|S(a)|) scan)
    - `'hybrid'`: Theorem-3.1-preserving parameter-free slack gate:
        `z_t^{in} = y_t` if `w_t(y_t) >= max(0.5 * R_t(a_t), u_t(p_t) - u_t(y_t))` else `p_t`
    - `'opt_sep'`: Optimistic-Separation DAG-LUCB (Theorem 3.2): selects action
        `b_t = argmax_a (U_t(a) - L_t^-(a))` and samples wider of `(p_t(b_t), q_t(b_t))`,
        stopping on `min_a R_t(a) <= eps`.
    """

    VALID_MODES = ("ucb", "lcb_fast", "hybrid", "opt_sep")

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        mode: str = "hybrid",
        delta: float = 0.05,
        schedule: str = "box",
    ):
        if mode not in self.VALID_MODES:
            raise ValueError(f"Unknown mode {mode!r}; expected one of {self.VALID_MODES}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.mode = mode
        self.oracle = problem.oracle(seed)
        self.policy_work = UCTWork()
        self.leaf_paths = _shortest_leaf_paths(self.graph, self.policy_work)
        self.monitor = DualWitnessCovers(
            self.graph,
            delta=delta,
            schedule=schedule,
            layout="best",
            track_separation=(mode == "opt_sep"),
        )
        self.calls = 0
        self._refresh()

    def _refresh(self) -> None:
        if self.mode == "opt_sep":
            self._sep_state = self.monitor.query_optimistic_separation()
            a_stop, reg = self._sep_state[0], self._sep_state[1]
        else:
            self._dual_state = self.monitor.query_dual_witness()
            a_stop, reg = self._dual_state[0], self._dual_state[1]
        self.certified = (not self.monitor.evidence.conflict) and (reg <= self.epsilon)
        self.action = a_stop

    def _choose_target(self) -> int:
        ev = self.monitor.evidence
        if self.mode == "opt_sep":
            _, _, _, _, p_b, q_b = self._sep_state
            if q_b < 0:
                return p_b
            self.policy_work.query_reads += 4
            w_p = ev.upper[p_b] - ev.lower[p_b]
            w_q = ev.upper[q_b] - ev.lower[q_b]
            return p_b if w_p >= w_q else q_b

        _, reg, p_t, y_t, q_t = self._dual_state
        if self.mode == "ucb":
            z_in = p_t
        elif self.mode == "lcb_fast":
            z_in = y_t
        else:  # hybrid
            u_p = ev.upper[p_t]
            u_y = ev.upper[y_t]
            l_y = ev.lower[y_t]
            w_y = u_y - l_y
            self.policy_work.query_reads += 4
            z_in = y_t if (w_y >= max(0.5 * reg, u_p - u_y)) else p_t

        if q_t < 0:
            return z_in
        self.policy_work.query_reads += 4
        w_in = ev.upper[z_in] - ev.lower[z_in]
        w_out = ev.upper[q_t] - ev.lower[q_t]
        return z_in if w_in >= w_out else q_t

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.monitor.evidence.conflict:
            raise RuntimeError("HybridWitnessDAGLUCBSession already terminated")
        target = self._choose_target()
        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1
        reward = self.oracle.sample(target)
        self.calls += 1
        self.policy_work.oracle_calls += 1
        self.monitor.step(target, reward)
        self._refresh()
        return path, reward

    @property
    def work(self) -> int:
        return (
            self.policy_work.total
            + self.monitor.work.total
            - self.calls
            + getattr(self.oracle, "operations", 0)
        )


def noncontainment_star_dag(
    n_rivals: int = 8,
    gap: float = 0.22,
    eps: float = 0.01,
) -> tuple[Problem, float]:
    """Construct the non-containment tied-star Bernoulli DAG of Theorem 3.3.

    Root has `1 + n_rivals` actions:
    - Action `A` (`a = 0`): support `S_A = {p, q}` with `mu_p = mu_q = 0.5`
    - Actions `B_i` (`i = 1..n_rivals`): support `S_{B_i} = {p, r_i}` with `mu_{r_i} = 0.5 - gap`

    Properties:
    - Every root action has true optimal value `0.5` (no unique optimal root action!).
    - Zero support containments (`S(b) not subseteq S(a)` for all `a != b`).
    - Best exterior separation is `Gamma = max_a (max_{z in S(a)} mu_z - max_{z notin S(a)} mu_z) = gap`
      (attained uniquely by `A`, whose support `{p, q}` contains *every* globally best terminal!).
    """
    if not (0.0 < gap < 0.5):
        raise ValueError("gap must lie in (0, 0.5)")
    # Node 0: root
    # Leaf 1: p, Leaf 2: q, Leaves 3 .. 2 + n_rivals: r_1 .. r_{n_rivals}
    p_leaf = 1
    q_leaf = 2
    r_leaves = [3 + i for i in range(n_rivals)]
    first_action = 3 + n_rivals
    rows: list[tuple[int, ...]] = [()]
    rows.extend([()] * (2 + n_rivals))  # leaves 1 .. 2 + n_rivals

    actions = [first_action + i for i in range(1 + n_rivals)]
    rows[0] = tuple(actions)
    # Place B_1..B_{n_rivals} first and S_A = {p, q} last so tie-breaking never favors A!
    for r_z in r_leaves:
        rows.append((p_leaf, r_z))
    rows.append((p_leaf, q_leaf))

    means: dict[int, float] = {p_leaf: 0.5, q_leaf: 0.5}
    for r_z in r_leaves:
        means[r_z] = 0.5 - gap

    dag = DAG(rows, root=0)
    prob = SplitMixProblem(f"star_n{n_rivals}_g{int(round(gap*100)):02d}", dag, means, reward_kind=1)
    return prob, eps
