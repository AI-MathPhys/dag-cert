"""Nested-box confidence monitors, protected vs. decision retirement, and exact regret.

Implements the three explicit certification oracle contracts of the v2 manuscript:
1. Numerical oracle: returns exact marginal intervals (L_t(a), U_t(a)) for all a in A,
   supporting full-incidence Graph-Eager, Protected-Root Graph-Selective
   (Theorem 2.5), and nested-box Dyadic Covers.
2. Leader-and-stop decision oracle: returns the canonical lower-bound leader and
   marginal stopping gap, supporting root-action retirement (Theorem 2.6).
3. Exact shared-support regret oracle (Theorem 2.2): returns min_a R_t(a) and its
   canonical minimizer via Charged Dual Covers (Theorem 3.1), Gate-Factorized
   Dual Circuits, or Direct Graph + Terminal Witness Maintenance.
"""
from __future__ import annotations

from collections import deque
import heapq
import math

from .certified_uct import IndexedMaxHeap, UCTWork
from .compiled_retirement import cover_compile, leaf_order, quotient
from .graph import DAG


class IndexedMinHeap:
    """Bounded-size min-heap with exact lowest-ID tie-breaking and UCTWork accounting."""

    def __init__(self, keys, work: UCTWork):
        self.keys = list(keys)
        self.ids = list(range(len(self.keys)))
        self.positions = list(range(len(self.keys)))
        self.work = work
        work.initialization += 3 * len(self.keys)
        self.rebuild()

    def _better(self, a: int, b: int) -> bool:
        self.work.heap_comparisons += 1
        return self.keys[a] < self.keys[b] or (self.keys[a] == self.keys[b] and a < b)

    def _swap(self, i: int, j: int) -> None:
        a, b = self.ids[i], self.ids[j]
        self.ids[i], self.ids[j] = b, a
        self.positions[a], self.positions[b] = j, i
        self.work.heap_writes += 4

    def _down(self, i: int) -> None:
        size = len(self.ids)
        while 2 * i + 1 < size:
            child = 2 * i + 1
            if child + 1 < size and self._better(self.ids[child + 1], self.ids[child]):
                child += 1
            if not self._better(self.ids[child], self.ids[i]):
                break
            self._swap(i, child)
            i = child

    def rebuild(self) -> None:
        for i in reversed(range(len(self.ids) // 2)):
            self._down(i)

    def update(self, item: int, key: float) -> None:
        old = self.keys[item]
        self.keys[item] = key
        self.work.heap_writes += 1
        pos = self.positions[item]
        if key < old:
            while pos and self._better(item, self.ids[(pos - 1) // 2]):
                parent = (pos - 1) // 2
                self._swap(pos, parent)
                pos = parent
        elif key > old:
            self._down(pos)

    @property
    def top(self) -> int:
        return self.ids[0]


class NestedIntervals:
    """Explicit time-uniform nested terminal confidence box [l_t(z), u_t(z)].

    Supports four concentration schedules:
    - 'box': beta(n) = sqrt(ln(4 * M * n^2 / delta) / (2 * n))  [Eq. (terminal-box), (v2radius)]
    - 'noisy_puct': beta(n) = sqrt(ln(4 * M * n * (n + 1) / delta) / (2 * n))  [Thm. (puct-noisy-main)]
    - 'legacy': beta(n) = sqrt(ln(pi^2 * M * n^2 / (3 * delta)) / (2 * n))  [CanonicalIntervals]
    - 'emp_bernstein': Waudby-Smith & Ramdas (2024, Prop. 2) time-uniform predictable
      plug-in Empirical Bernstein supermartingale confidence sequence using Ville's
      maximal inequality (threshold ln(2M/delta), psi_E(lam) = -ln(1 - lam) - lam),
      achieving O(ln(M/delta)/n) shrinkage on zero/low-variance streams and variance-adaptive
      O(sqrt(sigma_z^2 ln(M/delta) / n)) shrinkage on noisy streams with exact simultaneous
      (1 - delta) coverage across all z in Z and all adaptive times t >= 1.
    """

    def __init__(self, graph: DAG, work: UCTWork, delta: float = 0.05,
                 schedule: str = "box", effective_m: int | None = None):
        if not 0.0 < delta <= 0.5:
            raise ValueError("Need delta in (0, 0.5]")
        if schedule not in ("box", "noisy_puct", "legacy", "emp_bernstein"):
            raise ValueError(f"Unknown confidence schedule: {schedule}")
        self.graph = graph
        self.work = work
        self.delta = delta
        self.schedule = schedule
        m = len(graph.leaves) if effective_m is None else effective_m
        if m < 1:
            raise ValueError("Need at least one terminal")
        self.num_terminals = m
        if schedule in ("box", "noisy_puct"):
            self.log_constant = math.log(4.0 * m / delta)
        elif schedule == "emp_bernstein":
            self.log_constant = math.log(2.0 * m / delta)
        else:
            self.log_constant = math.log((math.pi ** 2) * m / (3.0 * delta))
        size = len(graph)
        self.counts = [0] * size
        self.sums = [0.0] * size
        if schedule == "emp_bernstein":
            self.eb_sum_lam = [0.0] * size
            self.eb_sum_lam_x = [0.0] * size
            self.eb_sum_v_psi = [0.0] * size
            self.eb_var_acc = [0.25] * size
        else:
            self.eb_sum_lam = None
            self.eb_sum_lam_x = None
            self.eb_sum_v_psi = None
            self.eb_var_acc = None
        self.lower = [0.0] * size
        self.upper = [1.0] * size
        self.evaluations = 0
        self.strict_changes = 0
        self.lower_changes = 0
        self.upper_changes = 0
        self.conflict = False
        work.initialization += (9 if schedule == "emp_bernstein" else 5) * size + 4

    def radius(self, n: int) -> float:
        if self.schedule == "noisy_puct":
            num = self.log_constant + math.log(n) + math.log(n + 1)
        else:
            num = self.log_constant + 2.0 * math.log(n)
        return math.sqrt(num / (2.0 * n))

    def observe(self, leaf: int, reward: float) -> tuple[float, float] | None:
        if self.graph.children[leaf] or not math.isfinite(reward) or not 0.0 <= reward <= 1.0:
            raise ValueError("Observation must be a finite [0, 1] draw at a terminal leaf")
        prev_n = self.counts[leaf]
        n = prev_n + 1
        self.counts[leaf] = n
        old_l, old_u = self.lower[leaf], self.upper[leaf]
        if self.eb_sum_lam is not None:
            # Predictable prior-1/2 mean and variance BEFORE observing X_n:
            hat_mu_prev = (0.5 + self.sums[leaf]) / n
            sigma2_prev = self.eb_var_acc[leaf] / n
            lam = min(0.75, math.sqrt(2.0 * self.log_constant / (sigma2_prev * n * math.log(n + 1.0))))
            psi = -math.log(1.0 - lam) - lam
            v_n = (reward - hat_mu_prev) ** 2
            self.sums[leaf] += reward
            hat_mu_curr = (0.5 + self.sums[leaf]) / (n + 1.0)
            self.eb_var_acc[leaf] += (reward - hat_mu_curr) ** 2
            self.eb_sum_lam[leaf] += lam
            self.eb_sum_lam_x[leaf] += lam * reward
            self.eb_sum_v_psi[leaf] += v_n * psi
            denom = self.eb_sum_lam[leaf]
            center = self.eb_sum_lam_x[leaf] / denom
            width = (self.log_constant + self.eb_sum_v_psi[leaf]) / denom
            lo = max(old_l, center - width, 0.0)
            hi = min(old_u, center + width, 1.0)
            self.work.oracle_calls += 1
            self.evaluations += 1
            self.work.statistic_writes += 6
            self.work.confidence_work += 16
        else:
            self.sums[leaf] += reward
            self.work.oracle_calls += 1
            self.work.statistic_writes += 2
            self.evaluations += 1
            self.work.confidence_work += 9
            rad = self.radius(n)
            mean = self.sums[leaf] / n
            lo = max(old_l, mean - rad, 0.0)
            hi = min(old_u, mean + rad, 1.0)
        self.lower[leaf], self.upper[leaf] = lo, hi
        self.work.statistic_writes += 2
        if lo > hi:
            self.conflict = True
            return None
        dl = int(lo != old_l)
        du = int(hi != old_u)
        if dl or du:
            self.strict_changes += 1
            self.lower_changes += dl
            self.upper_changes += du
            return lo, hi
        return None


class SelectiveDAGBounds:
    """Exact MAX confidence maintenance with explicit protected-output vs. decision modes.

    Modes:
    - 'eager': no edge retirement; updates both lower and upper heaps on all incidences.
    - 'protected': retires strictly dominated internal edges (v, j) for v not in protected_parents
      (by default protected_parents = {root}, protecting every original root action interval
      as required by Theorem 2.5), releasing only vertices with zero active incoming references.
    - 'decision': also retires strictly dominated root-action edges (root, b) once
      U_t(b) < max_{a in A_active \\ {b}} L_t(a) (Theorem 2.6), releasing unreachable subgraphs
      and maintaining the canonical leader and stopping gap over A_active in O(1) query time.
    """

    def __init__(self, graph: DAG, work: UCTWork, mode: str = "protected",
                 protected_vertices: tuple[int, ...] | None = None):
        if mode not in ("eager", "protected", "decision"):
            raise ValueError(f"Invalid maintenance mode: {mode}")
        self.graph = graph
        self.work = work
        self.mode = mode
        size = len(graph)
        self.lower = [0.0] * size
        self.upper = [1.0] * size
        self.leader = [0 if row else -1 for row in graph.children]
        self.live = [True] * size
        self.queued = [False] * size
        self.head = [-1] * size
        self.indegree = [0] * size
        self.parent: list[int] = []
        self.child: list[int] = []
        self.action: list[int] = []
        self.prev: list[int] = []
        self.next: list[int] = []
        self.active: list[bool] = []
        self.outgoing: list[list[int]] = [[] for _ in graph.children]

        # Protected nodes have an implicit external reference so they are never garbage-collected.
        if protected_vertices is None:
            if mode == "decision":
                protected_set = {graph.root}
            else:
                protected_set = {graph.root, *graph.children[graph.root]}
        else:
            protected_set = set(protected_vertices) | {graph.root}
        self.protected_set = frozenset(protected_set)
        # At which parents may outgoing edges be pruned?
        # In 'protected' mode, root's outgoing edges (the root actions) are protected outputs;
        # in 'decision' mode, root's outgoing edges can also be retired!
        self.prunable_parent = [
            mode != "eager" and not (mode == "protected" and v == graph.root)
            for v in range(size)
        ]

        self.low_heap = [IndexedMaxHeap([0.0] * len(row), work) if row else None
                         for row in graph.children]
        self.high_heap = [IndexedMaxHeap([1.0] * len(row), work) if row else None
                          for row in graph.children]
        self.min_upper = [
            IndexedMinHeap([1.0] * len(row), work) if (row and self.prunable_parent[v]) else None
            for v, row in enumerate(graph.children)
        ]

        self.messages = 0
        self.retired = 0
        self.retired_root_actions = 0
        self.dead_nodes = 0
        self.publications = 0
        self.skipped_dead = 0
        self.endpoint_changes = [0] * size
        self.changed_outputs: list[int] = []

        work.initialization += 14 * size + 8
        for p, row in enumerate(graph.children):
            for a, c in enumerate(row):
                e = len(self.parent)
                self.parent.append(p)
                self.child.append(c)
                self.action.append(a)
                self.prev.append(-1)
                self.next.append(self.head[c])
                self.active.append(True)
                if self.head[c] != -1:
                    self.prev[self.head[c]] = e
                self.head[c] = e
                self.indegree[c] += 1
                self.outgoing[p].append(e)
                work.initialization += 12

    def _unlink(self, edge: int) -> None:
        c, before, after = self.child[edge], self.prev[edge], self.next[edge]
        if before == -1:
            self.head[c] = after
        else:
            self.next[before] = after
        if after != -1:
            self.prev[after] = before
        self.active[edge] = False
        self.indegree[c] -= 1
        self.retired += 1
        if self.parent[edge] == self.graph.root:
            self.retired_root_actions += 1
        self.work.edge_reads += 3
        self.work.statistic_writes += 5

    def _release(self, start: int) -> None:
        if self.mode == "eager" or self.indegree[start] > 0 or start in self.protected_set:
            return
        pending = [start]
        self.work.statistic_writes += 1
        while pending:
            node = pending.pop()
            self.work.query_reads += 2
            if not self.live[node] or node in self.protected_set or self.indegree[node] > 0:
                continue
            self.live[node] = False
            self.dead_nodes += 1
            self.work.statistic_writes += 2
            for edge in self.outgoing[node]:
                self.work.edge_reads += 1
                if not self.active[edge]:
                    continue
                c = self.child[edge]
                self._unlink(edge)
                if self.indegree[c] == 0 and c not in self.protected_set:
                    pending.append(c)
                    self.work.statistic_writes += 1

    def _cut(self, node: int, best_lo: float) -> None:
        mheap = self.min_upper[node]
        if mheap is None:
            return
        while True:
            self.work.query_reads += 2
            a = mheap.top
            # If u_t(j) < max_{k in E_live(v)} l_t(k), then l_t(j) <= u_t(j) < best_lo,
            # so best_lo is guaranteed to be achieved by a distinct live child k != j!
            if mheap.keys[a] >= best_lo:
                return
            edge = self.outgoing[node][a]
            assert self.active[edge]
            child = self.child[edge]
            self._unlink(edge)
            self.low_heap[node].update(a, -math.inf)
            self.high_heap[node].update(a, -math.inf)
            mheap.update(a, math.inf)
            self._release(child)

    def _record(self, node: int, lower: float, upper: float) -> bool:
        old_l, old_u = self.lower[node], self.upper[node]
        self.work.query_reads += 2
        if lower == old_l and upper == old_u:
            return False
        assert old_l <= lower <= upper <= old_u + 1e-15, (node, old_l, lower, upper, old_u)
        self.lower[node], self.upper[node] = lower, upper
        self.publications += 1
        self.endpoint_changes[node] += int(lower != old_l) + int(upper != old_u)
        if node in self.protected_set:
            self.changed_outputs.append(node)
        self.work.statistic_writes += 4
        return True

    def publish(self, leaf: int, lower: float, upper: float) -> None:
        if self.graph.children[leaf]:
            raise ValueError("Only canonical terminals accept direct evidence")
        self.changed_outputs.clear()
        if not self._record(leaf, lower, upper):
            return
        if not self.live[leaf]:
            self.skipped_dead += 1
            self.work.statistic_writes += 1
            return
        # Propagate in topological reverse-rank order using a min-heap over (-rank[v])
        # so multi-parent diamond waves coalesce cleanly once per affected ancestor!
        rank = self.graph.rank
        heap: list[tuple[int, int]] = [(-rank[leaf], leaf)]
        self.queued[leaf] = True
        self.work.statistic_writes += 2
        while heap:
            _, node = heapq.heappop(heap)
            self.work.heap_comparisons += 1
            self.queued[node] = False
            self.work.statistic_writes += 2
            if not self.live[node]:
                continue
            edges = []
            edge = self.head[node]
            self.work.query_reads += 1
            while edge != -1:
                edges.append(edge)
                edge = self.next[edge]
                self.work.edge_reads += 1
                self.work.statistic_writes += 1
            for edge in edges:
                self.work.edge_reads += 1
                if not self.active[edge]:
                    continue
                p, a = self.parent[edge], self.action[edge]
                if not self.live[p]:
                    continue
                self.messages += 1
                self.work.edge_reads += 2
                lheap = self.low_heap[p]
                hheap = self.high_heap[p]
                self.work.query_reads += 4
                if lheap.keys[a] != self.lower[node]:
                    lheap.update(a, self.lower[node])
                if hheap.keys[a] != self.upper[node]:
                    hheap.update(a, self.upper[node])
                    if self.min_upper[p] is not None:
                        self.min_upper[p].update(a, self.upper[node])
                lo = lheap.keys[lheap.top]
                self.leader[p] = lheap.top
                if self.min_upper[p] is not None:
                    self._cut(p, lo)
                hi = hheap.keys[hheap.top]
                self.work.query_reads += 3
                if self._record(p, lo, hi) and not self.queued[p]:
                    heapq.heappush(heap, (-rank[p], p))
                    self.work.heap_comparisons += 1
                    self.queued[p] = True
                    self.work.statistic_writes += 2

    def query(self) -> tuple[int, float, float, float]:
        """Return (canonical_leader, marginal_gap, root_lower, root_upper) in O(1) heap reads."""
        root = self.graph.root
        row = self.graph.children[root]
        self.work.query_reads += 2
        if not row:
            return (-1, 0.0, self.lower[root], self.upper[root])
        if len(row) == 1:
            return (0, 0.0, self.lower[root], self.upper[root])
        lheap = self.low_heap[root]
        hheap = self.high_heap[root]
        best = lheap.top
        best_lo = lheap.keys[best]
        top_u = hheap.top
        if top_u != best:
            rival_hi = hheap.keys[top_u]
            self.work.query_reads += 3
        else:
            sec = hheap.second()
            rival_hi = hheap.keys[sec] if sec is not None else -math.inf
            self.work.query_reads += 4
        gap = max(0.0, rival_hi - best_lo)
        return (best, gap, self.lower[root], self.upper[root])

    def action_intervals(self) -> list[tuple[float, float]]:
        """Return numerical [(L_t(a), U_t(a))]_{a in A}; supported only when root is protected."""
        if self.mode == "decision":
            raise RuntimeError("Decision-selective mode retires root actions; numerical intervals are unsupported")
        row = self.graph.children[self.graph.root]
        self.work.query_reads += 2 * len(row)
        return [(self.lower[c], self.upper[c]) for c in row]


class MarginalGraphMonitor:
    """Marginal-interval or decision-only DAG monitor with optional paid quotienting."""

    def __init__(self, graph: DAG, mode: str = "protected", delta: float = 0.05,
                 schedule: str = "box", simplify: bool = False,
                 effective_m: int | None = None):
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule,
                                        effective_m=effective_m)
        if simplify:
            circuit, self.mapping, self.info = quotient(graph, w)
        else:
            circuit = graph
            self.mapping = {leaf: leaf for leaf in graph.leaves}
            self.info = {"order": "raw", "entries": sum(map(len, graph.children))}
            w.initialization += len(graph.leaves)
        self.compile_work = w.total
        self.bounds = SelectiveDAGBounds(circuit, w, mode=mode)
        self.info.update(nodes=len(circuit), edges=sum(map(len, circuit.children)), mode=mode)

    def step(self, leaf: int, reward: float) -> bool:
        interval = self.evidence.observe(leaf, reward)
        if interval is None:
            return False
        self.bounds.publish(self.mapping[leaf], *interval)
        return True

    def query(self) -> tuple[int, float, float, float]:
        return self.bounds.query()

    def recommend_midpoint(self) -> int:
        """Anytime midpoint leader over active/protected actions."""
        root = self.bounds.graph.root
        row = self.bounds.graph.children[root]
        if not row:
            return -1
        best_a, best_val = 0, -math.inf
        for a, e in enumerate(self.bounds.outgoing[root]):
            self.work.query_reads += 2
            if not self.bounds.active[e]:
                continue
            c = row[a]
            mid = 0.5 * (self.bounds.lower[c] + self.bounds.upper[c])
            if mid > best_val:
                best_a, best_val = a, mid
        return best_a


def _heap_merge_runs(child_runs: list[tuple[tuple[int, int], ...]], work: UCTWork) -> tuple[tuple[int, int], ...]:
    """Merge k sorted disjoint run lists using a binary heap in O(A_v log(2 + k)) operations."""
    k = len(child_runs)
    if k == 0:
        return ()
    if k == 1:
        work.query_reads += 1
        return child_runs[0]
    heap: list[tuple[int, int, int, int]] = []
    for idx, runs in enumerate(child_runs):
        work.query_reads += 1
        if runs:
            lo, hi = runs[0]
            heapq.heappush(heap, (lo, hi, idx, 0))
            work.heap_comparisons += max(1, len(heap).bit_length())
            work.statistic_writes += 1
    merged: list[tuple[int, int]] = []
    while heap:
        lo, hi, idx, pos = heapq.heappop(heap)
        work.heap_comparisons += max(1, len(heap).bit_length())
        work.query_reads += 2
        if merged and lo <= merged[-1][1]:
            if hi > merged[-1][1]:
                merged[-1] = (merged[-1][0], hi)
                work.statistic_writes += 1
            work.heap_comparisons += 2
        else:
            merged.append((lo, hi))
            work.statistic_writes += 1
            work.heap_comparisons += 1
        nxt = pos + 1
        if nxt < len(child_runs[idx]):
            nlo, nhi = child_runs[idx][nxt]
            heapq.heappush(heap, (nlo, nhi, idx, nxt))
            work.heap_comparisons += max(1, len(heap).bit_length())
            work.statistic_writes += 1
    return tuple(merged)


def _dyadic_blocks(runs: tuple[tuple[int, int], ...], size: int, work: UCTWork) -> tuple[int, ...]:
    """Decompose sorted disjoint runs on [0, M) into canonical dyadic blocks in [1, 2*size)."""
    blocks: list[int] = []
    for lo, hi in runs:
        a = lo + size
        b = hi + size
        work.query_reads += 2
        left: list[int] = []
        right: list[int] = []
        while a < b:
            work.query_reads += 2
            work.heap_comparisons += 2
            if a & 1:
                left.append(a)
                a += 1
                work.statistic_writes += 1
            if b & 1:
                b -= 1
                right.append(b)
                work.statistic_writes += 1
            a //= 2
            b //= 2
        blocks.extend(left)
        blocks.extend(reversed(right))
    return tuple(blocks)


def _complement_runs(runs: tuple[tuple[int, int], ...], m: int, work: UCTWork) -> tuple[tuple[int, int], ...]:
    """Compute disjoint maximal contiguous runs of [0, m) \\ union(runs)."""
    prev = 0
    comp: list[tuple[int, int]] = []
    for lo, hi in runs:
        work.query_reads += 2
        work.heap_comparisons += 1
        if prev < lo:
            comp.append((prev, lo))
            work.statistic_writes += 1
        prev = hi
    if prev < m:
        comp.append((prev, m))
        work.statistic_writes += 1
    return tuple(comp)


class NestedDyadicCovers:
    """Marginal root-interval dyadic covers monitor using NestedIntervals."""

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box",
                 layout: str = "best", effective_m: int | None = None):
        if layout not in ("id", "dfs", "best"):
            raise ValueError(f"Unknown terminal layout mode: {layout}")
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule,
                                        effective_m=effective_m)
        m = len(graph.leaves)
        self.size = 1 << max(0, (m - 1).bit_length())
        root_children = graph.children[graph.root]
        self.num_actions = len(root_children)

        modes = (False, True) if layout == "best" else ((True,) if layout == "dfs" else (False,))
        candidates = []
        for dfs in modes:
            leaves = leaf_order(graph, dfs, w)
            rank = {v: i for i, v in enumerate(leaves)}
            w.initialization += len(leaves)
            runs: list[tuple[tuple[int, int], ...]] = [()] * len(graph)
            for v in reversed(graph.order):
                ch = graph.children[v]
                w.edge_reads += len(ch)
                if not ch:
                    j = rank[v]
                    runs[v] = ((j, j + 1),)
                    w.statistic_writes += 1
                elif len(ch) == 1:
                    runs[v] = runs[ch[0]]
                    w.statistic_writes += 1
                else:
                    runs[v] = _heap_merge_runs([runs[c] for c in ch], w)
            groups: dict[tuple[tuple[int, int], ...], int] = {}
            covers: list[tuple[int, ...]] = []
            actions: list[int] = []
            for c in root_children:
                pr = runs[c]
                w.query_reads += 1 + len(pr)
                if pr not in groups:
                    groups[pr] = len(covers)
                    covers.append(_dyadic_blocks(pr, self.size, w))
                actions.append(groups[pr])
            candidates.append((sum(map(len, covers)), dfs, leaves, rank, covers, actions))
            w.statistic_writes += sum(map(len, runs)) + len(runs)

        (self.entries, chosen_dfs, self.leaves, self.rank,
         self.covers, self.actions) = min(candidates, key=lambda x: (x[0], x[1]))

        self.low = [0.0] * (2 * self.size)
        self.high = [-1.0] * (2 * self.size)
        for j in range(m):
            self.high[self.size + j] = 1.0
        for d in reversed(range(1, self.size)):
            self.high[d] = max(self.high[2 * d], self.high[2 * d + 1])
        w.initialization += 6 * self.size + m + len(self.covers)
        self.compile_work = w.total
        self.info = {
            "order": "dfs" if chosen_dfs else "id",
            "entries": self.entries,
            "unique_supports": len(self.covers),
        }

    def step(self, leaf: int, reward: float) -> bool:
        interval = self.evidence.observe(leaf, reward)
        if interval is None:
            return False
        d = self.size + self.rank[leaf]
        lo, hi = interval
        while True:
            self.work.query_reads += 2
            if (lo, hi) == (self.low[d], self.high[d]):
                break
            self.low[d], self.high[d] = lo, hi
            self.work.statistic_writes += 2
            if d == 1:
                break
            d //= 2
            lo = max(self.low[2 * d], self.low[2 * d + 1])
            hi = max(self.high[2 * d], self.high[2 * d + 1])
            self.work.query_reads += 4
            self.work.heap_comparisons += 2
        return True

    def query(self) -> tuple[int, float, float, float]:
        if not self.covers:
            return (-1, 0.0, self.low[1], self.high[1])
        lower: list[float] = []
        upper: list[float] = []
        for cover in self.covers:
            lower.append(max(self.low[d] for d in cover))
            upper.append(max(self.high[d] for d in cover))
            self.work.query_reads += 2 * len(cover) + 2
            self.work.heap_comparisons += 2 * len(cover)
        # Canonical lowest-action-ID tie breaking on max L_t(a):
        best = max(range(len(self.actions)), key=lambda a: (lower[self.actions[a]], -a))
        best_lo = lower[self.actions[best]]
        gap = max((upper[g] - best_lo for j, g in enumerate(self.actions) if j != best), default=0.0)
        self.work.query_reads += 2 * len(self.actions) + 3
        return (best, max(0.0, gap), best_lo, max(upper))


class ChargedDualCovers:
    """Charged exact shared-support regret monitor via positive/negative dyadic covers (Thm. 3.1).

    Maintains:
    - Shared binary segment tree storing lower-bound maxima (for C_a^+) and upper-bound maxima (for C_a^-).
    - Two IndexedMaxHeaps per root action (over C_a^+ and non-empty C_a^-).
    - One global IndexedMinHeap over exact robust regrets R_t(a) = [max_{z notin S(a)} u_t(z) - L_t(a)]_+,
      with canonical lowest-action-ID tie-breaking.
    """

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box",
                 layout: str = "id", effective_m: int | None = None):
        if layout not in ("id", "dfs", "best"):
            raise ValueError(f"Unknown terminal layout mode: {layout}")
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule,
                                        effective_m=effective_m)
        m = len(graph.leaves)
        self.size = 1 << max(0, (m - 1).bit_length())
        root_children = graph.children[graph.root]
        self.num_actions = len(root_children)

        modes = (False, True) if layout == "best" else ((True,) if layout == "dfs" else (False,))
        candidates = []
        for dfs in modes:
            leaves = leaf_order(graph, dfs, w)
            rank = {v: i for i, v in enumerate(leaves)}
            w.initialization += len(leaves)
            runs: list[tuple[tuple[int, int], ...]] = [()] * len(graph)
            for v in reversed(graph.order):
                ch = graph.children[v]
                w.edge_reads += len(ch)
                if not ch:
                    j = rank[v]
                    runs[v] = ((j, j + 1),)
                    w.statistic_writes += 1
                elif len(ch) == 1:
                    runs[v] = runs[ch[0]]
                    w.statistic_writes += 1
                else:
                    runs[v] = _heap_merge_runs([runs[c] for c in ch], w)
            pos_covers = []
            neg_covers = []
            total_runs = 0
            for c in root_children:
                pr = runs[c]
                total_runs += len(pr)
                nr = _complement_runs(pr, m, w)
                pos_covers.append(_dyadic_blocks(pr, self.size, w))
                neg_covers.append(_dyadic_blocks(nr, self.size, w))
            total_blocks = sum(map(len, pos_covers)) + sum(map(len, neg_covers))
            candidates.append((total_blocks, dfs, leaves, rank, total_runs, pos_covers, neg_covers))
            # Charge temporary run-list release as required by Theorem 3.1.
            w.statistic_writes += sum(map(len, runs)) + len(runs)

        (self.total_blocks, chosen_dfs, self.leaves, self.rank,
         self.root_runs, self.pos_covers, self.neg_covers) = min(candidates, key=lambda x: (x[0], x[1]))

        self.low = [0.0] * (2 * self.size)
        self.high = [-math.inf] * (2 * self.size)
        for j in range(m):
            self.high[self.size + j] = 1.0
        for d in reversed(range(1, self.size)):
            self.low[d] = max(self.low[2 * d], self.low[2 * d + 1])
            self.high[d] = max(self.high[2 * d], self.high[2 * d + 1])
        w.initialization += 6 * self.size + m

        # Reverse block-to-action subscriptions N_t^+ and N_t^-.
        self.pos_subs: list[list[tuple[int, int]]] = [[] for _ in range(2 * self.size)]
        self.neg_subs: list[list[tuple[int, int]]] = [[] for _ in range(2 * self.size)]
        self.pos_heaps: list[IndexedMaxHeap] = []
        self.neg_heaps: list[IndexedMaxHeap | None] = []
        init_regrets: list[float] = []

        for a in range(self.num_actions):
            pc = self.pos_covers[a]
            nc = self.neg_covers[a]
            for idx, d in enumerate(pc):
                self.pos_subs[d].append((a, idx))
                w.statistic_writes += 1
            for idx, d in enumerate(nc):
                self.neg_subs[d].append((a, idx))
                w.statistic_writes += 1
            pheap = IndexedMaxHeap([self.low[d] for d in pc], w)
            self.pos_heaps.append(pheap)
            if nc:
                nheap = IndexedMaxHeap([self.high[d] for d in nc], w)
                self.neg_heaps.append(nheap)
                la = pheap.keys[pheap.top]
                ua_out = nheap.keys[nheap.top]
                init_regrets.append(max(0.0, ua_out - la))
            else:
                # S(a) == Z: identically zero robust regret!
                self.neg_heaps.append(None)
                init_regrets.append(0.0)

        self.regret_heap = IndexedMinHeap(init_regrets, w) if self.num_actions else None
        self.compile_work = w.total
        self.messages = 0
        self.affected_action_updates = 0
        self.info = {
            "order": "dfs" if chosen_dfs else "id",
            "root_runs": self.root_runs,
            "pos_blocks": sum(map(len, self.pos_covers)),
            "neg_blocks": sum(map(len, self.neg_covers)),
            "total_blocks": self.total_blocks,
        }

    def step(self, leaf: int, reward: float) -> bool:
        interval = self.evidence.observe(leaf, reward)
        if interval is None:
            return False
        d = self.size + self.rank[leaf]
        lo, hi = interval
        touched: set[int] = set()
        while True:
            old_lo, old_hi = self.low[d], self.high[d]
            self.work.query_reads += 2
            lo_changed = lo != old_lo
            hi_changed = hi != old_hi
            if not lo_changed and not hi_changed:
                break
            if lo_changed:
                self.low[d] = lo
                self.work.statistic_writes += 1
                for a, idx in self.pos_subs[d]:
                    self.messages += 1
                    self.work.edge_reads += 1
                    self.pos_heaps[a].update(idx, lo)
                    touched.add(a)
            if hi_changed:
                self.high[d] = hi
                self.work.statistic_writes += 1
                for a, idx in self.neg_subs[d]:
                    self.messages += 1
                    self.work.edge_reads += 1
                    nheap = self.neg_heaps[a]
                    assert nheap is not None
                    nheap.update(idx, hi)
                    touched.add(a)
            if d == 1:
                break
            d //= 2
            lo = max(self.low[2 * d], self.low[2 * d + 1])
            hi = max(self.high[2 * d], self.high[2 * d + 1])
            self.work.query_reads += 4
            self.work.heap_comparisons += 2

        if self.regret_heap is not None:
            for a in touched:
                self.affected_action_updates += 1
                nheap = self.neg_heaps[a]
                if nheap is None:
                    reg = 0.0
                else:
                    pheap = self.pos_heaps[a]
                    la = pheap.keys[pheap.top]
                    ua_out = nheap.keys[nheap.top]
                    self.work.query_reads += 2
                    reg = max(0.0, ua_out - la)
                self.regret_heap.update(a, reg)
        return True

    def query(self) -> tuple[int, float, float, float]:
        """Return (canonical_regret_minimizer, min_regret, minimizer_L, global_U) in O(1)."""
        self.work.query_reads += 3
        if self.regret_heap is None:
            return (-1, 0.0, self.low[1], self.high[1])
        best = self.regret_heap.top
        reg = self.regret_heap.keys[best]
        pheap = self.pos_heaps[best]
        la = pheap.keys[pheap.top]
        return (best, reg, la, self.high[1])

    def action_regrets(self) -> list[float]:
        if self.regret_heap is None:
            return []
        self.work.query_reads += self.num_actions
        return list(self.regret_heap.keys)


class FactorizedRegretMonitor:
    """Incidence-sensitive gate-factorized exact-regret monitor (for Experiment 4).

    Retains the quotient MAX gates of the input DAG for positive supports S(a),
    and covers each complement Z \\ S(a) using maximal support-disjoint existing
    gates (gates g with S(g) subseteq Z \\ S(a)), charging word-level bitmask
    operations explicitly during compilation.
    """

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box",
                 mode: str = "protected", effective_m: int | None = None):
        if mode not in ("eager", "protected"):
            raise ValueError("FactorizedRegretMonitor requires 'eager' or 'protected' gate mode")
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule,
                                        effective_m=effective_m)
        base, leaf_map, _ = quotient(graph, w)
        m = len(graph.leaves)
        words = max(1, (m + 63) // 64)
        inv_leaf = {alias: j for j, (_, alias) in enumerate(sorted(leaf_map.items()))}
        self.mapping = leaf_map

        # Compute terminal support bitmasks on the quotient circuit, charging word operations.
        masks = [0] * len(base)
        popcounts = [0] * len(base)
        for v in reversed(base.order):
            ch = base.children[v]
            if not ch:
                bit = inv_leaf[v]
                masks[v] = 1 << bit
                popcounts[v] = 1
                w.statistic_writes += 1
            else:
                acc = 0
                for c in ch:
                    acc |= masks[c]
                    w.query_reads += words
                    w.statistic_writes += words
                masks[v] = acc
                popcounts[v] = acc.bit_count()
                w.confidence_work += words

        # Candidate gates for covering complements: internal gates + leaves, largest support first.
        base_root = base.root
        pos_action_nodes = [base.children[w_id][0] for w_id in base.children[base_root]]
        candidate_gates = [v for v in range(len(base)) if v != base_root and v not in base.children[base_root]]
        candidate_gates.sort(key=lambda v: (-popcounts[v], v))
        w.heap_comparisons += len(candidate_gates) * max(1, len(candidate_gates).bit_length())

        rows = [ base.children[v] for v in range(base_root) ]  # drop old unary action wrappers & root
        # Rebuild clean outputs: pos_out[a] and optional neg_out[a].
        full_mask = (1 << m) - 1
        self.num_actions = len(pos_action_nodes)
        self.pos_out: list[int] = []
        self.neg_out: list[int | None] = []
        neg_cover_sizes: list[int] = []

        # Map old vertex IDs < base_root identically (note action wrappers in quotient() were appended just before root).
        first_wrapper = base_root - self.num_actions
        rows = list(base.children[:first_wrapper])
        bit_to_leaf = {j: alias for alias, j in inv_leaf.items()}
        internal_gates = [v for v in candidate_gates if v < first_wrapper and base.children[v]]

        for a, pnode in enumerate(pos_action_nodes):
            self.pos_out.append(pnode)
            comp = full_mask ^ masks[pnode]
            w.query_reads += words
            if comp == 0:
                self.neg_out.append(None)
                neg_cover_sizes.append(0)
                continue
            rem = comp
            chosen: list[int] = []
            for g in internal_gates:
                if (rem & (rem - 1)) == 0:
                    # At most one uncovered terminal remains; extract it directly below in O(1)!
                    break
                mg = masks[g]
                w.query_reads += 2 * words
                w.heap_comparisons += 2
                # Gate g is admissible iff S(g) is disjoint from S(a) and covers >=1 uncovered complement leaf.
                if (mg & masks[pnode]) == 0 and (mg & rem) != 0:
                    chosen.append(g)
                    rem &= ~mg
                    w.statistic_writes += words + 1
                    if rem == 0:
                        break
            while rem:
                lsb = rem & -rem
                chosen.append(bit_to_leaf[lsb.bit_length() - 1])
                rem ^= lsb
                w.statistic_writes += 1
            neg_cover_sizes.append(len(chosen))
            if len(chosen) == 1:
                self.neg_out.append(chosen[0])
            else:
                nid = len(rows)
                rows.append(tuple(chosen))
                self.neg_out.append(nid)
                w.initialization += 8 + 6 * len(chosen)

        # Add a synthetic top root gathering all protected positive and negative output gates.
        outputs_dedup = list(dict.fromkeys(
            list(self.pos_out) + [n for n in self.neg_out if n is not None]
        ))
        super_root = len(rows)
        rows.append(tuple(outputs_dedup))
        w.initialization += 8 + 6 * len(outputs_dedup)
        circuit = DAG(rows, root=super_root)

        self.compile_work = w.total
        self.bounds = SelectiveDAGBounds(circuit, w, mode=mode,
                                         protected_vertices=tuple(outputs_dedup))

        # Subscribe output gates to actions so changed L_t(a) or U_t^out(a) updates regret_heap.
        self.pos_watchers: dict[int, list[int]] = {}
        self.neg_watchers: dict[int, list[int]] = {}
        init_regrets: list[float] = []
        for a in range(self.num_actions):
            p = self.pos_out[a]
            self.pos_watchers.setdefault(p, []).append(a)
            n = self.neg_out[a]
            if n is None:
                init_regrets.append(0.0)
            else:
                self.neg_watchers.setdefault(n, []).append(a)
                init_regrets.append(max(0.0, self.bounds.upper[n] - self.bounds.lower[p]))
            w.statistic_writes += 2

        self.regret_heap = IndexedMinHeap(init_regrets, w) if self.num_actions else None
        self.info = {
            "nodes": len(circuit),
            "edges": sum(map(len, circuit.children)),
            "neg_incidences": sum(neg_cover_sizes),
            "pos_gates": len(set(self.pos_out)),
            "mode": mode,
        }

    def step(self, leaf: int, reward: float) -> bool:
        interval = self.evidence.observe(leaf, reward)
        if interval is None:
            return False
        self.bounds.publish(self.mapping[leaf], *interval)
        if self.regret_heap is not None and self.bounds.changed_outputs:
            touched: set[int] = set()
            for g in self.bounds.changed_outputs:
                if g in self.pos_watchers:
                    touched.update(self.pos_watchers[g])
                    self.work.query_reads += len(self.pos_watchers[g])
                if g in self.neg_watchers:
                    touched.update(self.neg_watchers[g])
                    self.work.query_reads += len(self.neg_watchers[g])
            for a in touched:
                n = self.neg_out[a]
                if n is None:
                    reg = 0.0
                else:
                    p = self.pos_out[a]
                    reg = max(0.0, self.bounds.upper[n] - self.bounds.lower[p])
                    self.work.query_reads += 2
                self.regret_heap.update(a, reg)
        return True

    def query(self) -> tuple[int, float, float, float]:
        self.work.query_reads += 3
        if self.regret_heap is None:
            r = self.bounds.graph.root
            return (-1, 0.0, self.bounds.lower[r], self.bounds.upper[r])
        best = self.regret_heap.top
        reg = self.regret_heap.keys[best]
        la = self.bounds.lower[self.pos_out[best]]
        r = self.bounds.graph.root
        return (best, reg, la, self.bounds.upper[r])

    def action_regrets(self) -> list[float]:
        if self.regret_heap is None:
            return []
        self.work.query_reads += self.num_actions
        return list(self.regret_heap.keys)


class DirectGraphRegretMonitor:
    """Direct uncompiled graph maintenance + sorted terminal upper-heap complement scan.

    Avoids building either dyadic block covers or synthetic complement gates:
    - Maintains L_t(a) directly on the quotient DAG via SelectiveDAGBounds.
    - Maintains a global IndexedMaxHeap of terminal upper bounds u_t(z) and bitmask
      memberships S(a), finding max_{z notin S(a)} u_t(z) at query time with a
      cached outside-witness shortcut per action.
    """

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box",
                 mode: str = "protected", effective_m: int | None = None):
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule,
                                        effective_m=effective_m)
        circuit, self.mapping, self.info = quotient(graph, w)
        m = len(graph.leaves)
        words = max(1, (m + 63) // 64)
        self.leaf_rank = {leaf: idx for idx, leaf in enumerate(graph.leaves)}

        # Compute action membership bitmasks directly on original graph.
        node_masks = [0] * len(graph)
        for v in reversed(graph.order):
            ch = graph.children[v]
            if not ch:
                node_masks[v] = 1 << self.leaf_rank[v]
                w.statistic_writes += 1
            else:
                acc = 0
                for c in ch:
                    acc |= node_masks[c]
                    w.query_reads += words
                node_masks[v] = acc
                w.statistic_writes += words
        full_mask = (1 << m) - 1
        self.action_masks = [node_masks[c] for c in graph.children[graph.root]]
        self.full_support = [mask == full_mask for mask in self.action_masks]
        self.term_upper_heap = IndexedMaxHeap([1.0] * m, w)
        self.compile_work = w.total
        self.bounds = SelectiveDAGBounds(circuit, w, mode=mode)
        self.num_actions = len(self.action_masks)
        self.info.update(nodes=len(circuit), edges=sum(map(len, circuit.children)), mode=mode)

    def step(self, leaf: int, reward: float) -> bool:
        interval = self.evidence.observe(leaf, reward)
        if interval is None:
            return False
        self.bounds.publish(self.mapping[leaf], *interval)
        self.term_upper_heap.update(self.leaf_rank[leaf], interval[1])
        return True

    def _max_outside(self, a: int) -> float:
        if self.full_support[a]:
            return -math.inf
        mask = self.action_masks[a]
        # Fast path: check global top terminal first!
        top_j = self.term_upper_heap.top
        self.work.query_reads += 2
        if not ((mask >> top_j) & 1):
            return self.term_upper_heap.keys[top_j]
        # Otherwise scan outside terminals directly over keys array.
        keys = self.term_upper_heap.keys
        best_u = -math.inf
        for j, u in enumerate(keys):
            self.work.query_reads += 1
            self.work.heap_comparisons += 1
            if not ((mask >> j) & 1) and u > best_u:
                best_u = u
        return best_u

    def query(self) -> tuple[int, float, float, float]:
        root = self.bounds.graph.root
        row = self.bounds.graph.children[root]
        if not row:
            return (-1, 0.0, self.bounds.lower[root], self.bounds.upper[root])
        top_j = self.term_upper_heap.top
        top_u = self.term_upper_heap.keys[top_j]
        self.work.query_reads += 2

        best_a = 0
        best_reg = math.inf
        best_la = 0.0
        # Actions not containing top_j immediately have max_{z notin S(a)} u_t(z) == top_u in O(1).
        # Only actions containing top_j need a fallback scan, and if >2 actions contain top_j,
        # sorting or scanning descending terminal indices once avoids O(K * M) work!
        holders = [a for a in range(len(row)) if not self.full_support[a] and ((self.action_masks[a] >> top_j) & 1)]
        self.work.query_reads += len(row)
        sorted_leaves: list[int] | None = None
        if len(holders) > 2:
            keys = self.term_upper_heap.keys
            sorted_leaves = sorted(range(len(keys)), key=lambda j: -keys[j])
            self.work.heap_comparisons += len(keys) * max(1, len(keys).bit_length())

        for a, c in enumerate(row):
            la = self.bounds.lower[c]
            self.work.query_reads += 1
            if self.full_support[a]:
                reg = 0.0
            elif not ((self.action_masks[a] >> top_j) & 1):
                reg = max(0.0, top_u - la)
            elif sorted_leaves is not None:
                mask = self.action_masks[a]
                keys = self.term_upper_heap.keys
                ua_out = -math.inf
                for j in sorted_leaves:
                    self.work.query_reads += 1
                    self.work.heap_comparisons += 1
                    if not ((mask >> j) & 1):
                        ua_out = keys[j]
                        break
                reg = max(0.0, ua_out - la)
            else:
                reg = max(0.0, self._max_outside(a) - la)
            self.work.heap_comparisons += 1
            if reg < best_reg:
                best_reg = reg
                best_a = a
                best_la = la
        return (best_a, best_reg, best_la, self.bounds.upper[root])


def brute_force_marginal(graph: DAG, lower: list[float], upper: list[float]) -> tuple[int, float, list[tuple[float, float]]]:
    """Unoptimized exact DP reference for audit and unit testing."""
    lo = list(lower)
    hi = list(upper)
    for v in reversed(graph.order):
        ch = graph.children[v]
        if ch:
            lo[v] = max(lo[c] for c in ch)
            hi[v] = max(hi[c] for c in ch)
    row = graph.children[graph.root]
    if not row:
        return -1, 0.0, []
    intervals = [(lo[c], hi[c]) for c in row]
    # Canonical lowest-action-ID tie breaking on max L_t(a):
    best = max(range(len(row)), key=lambda a: (intervals[a][0], -a))
    gap = max((intervals[b][1] - intervals[best][0] for b in range(len(row)) if b != best), default=0.0)
    return best, max(0.0, gap), intervals


def brute_force_exact_regret(graph: DAG, lower: list[float], upper: list[float]) -> tuple[int, float, list[float]]:
    """Unoptimized exact shared-support regret reference (Theorem 2.2)."""
    supports: dict[int, set[int]] = {}
    for v in reversed(graph.order):
        ch = graph.children[v]
        if not ch:
            supports[v] = {v}
        else:
            s: set[int] = set()
            for c in ch:
                s.update(supports[c])
            supports[v] = s
    all_leaves = set(graph.leaves)
    row = graph.children[graph.root]
    if not row:
        return -1, 0.0, []
    regrets: list[float] = []
    for c in row:
        sa = supports[c]
        la = max(lower[z] for z in sa)
        outside = all_leaves - sa
        if not outside:
            regrets.append(0.0)
        else:
            ua_out = max(upper[z] for z in outside)
            regrets.append(max(0.0, ua_out - la))
    best = min(range(len(row)), key=lambda a: (regrets[a], a))
    return best, regrets[best], regrets
