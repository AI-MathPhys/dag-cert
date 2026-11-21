"""v3 Strengthening Extensions: Empirical Bernstein, Active Witness DAG-LUCB, and C++17 Kernels.

Implements:
1. Canonical Witness-Enabled Monitors (`WitnessDualCovers`, `WitnessDirectGraphRegret`,
   `WitnessFactorizedRegret`, `WitnessMarginalGraph`), supporting both Hoeffding (`box`)
   and time-uniform Maurer-Pontil Empirical Bernstein (`emp_bernstein`) nested boxes and
   returning exact `(best_action, gap_or_regret, z_in, z_out)` with canonical `(u_t(z), -z)`
   tie-breaking so adaptive controllers satisfy Theorem 2.4 transcript equivalence.
2. Active Pure-Exploration DAG Controllers (`ExactRegretDAGLUCB` and `MarginalDAGLUCB`)
   that steer rollouts directly to the optimistic inside/outside regret witnesses rather
   than passive UCT/PUCT exploration.
3. On-demand `-O3 -std=c++17` shared-library compiler and `ctypes` bridge (`CppKernelRunner`)
   plus `SplitMixProblem` for bit-exact Python <-> C++17 replay and native microsecond timing.
"""
from __future__ import annotations

from collections import deque
import ctypes
import hashlib
import heapq
import math
from pathlib import Path
import subprocess
import tempfile

from .certified_uct import IndexedMaxHeap, UCTWork
from .compiled_retirement import leaf_order, quotient
from .graph import DAG, Problem
from .v2_monitors import (
    IndexedMinHeap,
    NestedIntervals,
    _complement_runs,
    _dyadic_blocks,
    _heap_merge_runs,
)


CPP_SOURCE = Path(__file__).resolve().parent / "_cpp_kernels.cpp"


def splitmix_uniform01(seed: int, leaf: int, obs_index: int) -> float:
    """Exact 64-bit SplitMix64 draw matching `splitmix_uniform01` in `_cpp_kernels.cpp`."""
    mask = 0xFFFFFFFFFFFFFFFF
    z = (seed + 0x9E3779B97F4A7C15 * (leaf + 1) + 0xBF58476D1CE4E5B9 * obs_index) & mask
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & mask
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & mask
    z = (z ^ (z >> 31)) & mask
    return (z >> 11) * (1.0 / 9007199254740992.0)


class SplitMixProblem(Problem):
    """Problem wrapper using stateless SplitMix64 terminal tapes for exact Python/C++ parity."""

    def __init__(self, name: str, graph: DAG, means: dict[int, float], reward_kind: int = 1):
        # reward_kind: 0 = deterministic, 1 = bernoulli, 2 = uniform +-0.01
        det = graph.leaves if reward_kind == 0 else ()
        super().__init__(name, graph, means, det)
        self.reward_kind = reward_kind

    def oracle(self, seed: int):
        prob = self
        s64 = seed & 0xFFFFFFFFFFFFFFFF

        class _Oracle:
            def __init__(self):
                self.obs = [0] * len(prob.graph)
                self.operations = 0

            def sample(self, leaf: int) -> float:
                self.obs[leaf] += 1
                k = self.obs[leaf]
                mu = prob.means[leaf]
                if prob.reward_kind == 0:
                    return mu
                u = splitmix_uniform01(s64, leaf, k)
                if prob.reward_kind == 1:
                    return 1.0 if u < mu else 0.0
                return min(1.0, max(0.0, mu + 0.01 * (2.0 * u - 1.0)))

        return _Oracle()


class _CppRunResult(ctypes.Structure):
    _fields_ = [
        ("init_ns", ctypes.c_int64),
        ("total_ns", ctypes.c_int64),
        ("steps", ctypes.c_int64),
        ("work", ctypes.c_int64),
        ("messages", ctypes.c_int64),
        ("retired", ctypes.c_int64),
        ("strict_changes", ctypes.c_int64),
        ("action", ctypes.c_int),
        ("certified", ctypes.c_int),
    ]


class CppKernelRunner:
    """Compiles `_cpp_kernels.cpp` with `g++ -O3 -std=c++17` into tempdir and binds ctypes."""

    _lib = None
    _so_path: Path | None = None

    METHOD_CODES = {
        "graph-eager": 0,
        "protected-selective": 1,
        "decision-selective": 2,
        "dual-covers": 3,
        "direct-graph-regret": 4,
    }
    POLICY_CODES = {
        "uct": 0,
        "root_puct": 1,
    }
    SCHEDULE_CODES = {
        "box": 0,
        "emp_bernstein": 1,
    }

    @classmethod
    def ensure_loaded(cls):
        if cls._lib is not None:
            return cls._lib
        import os
        import shutil
        import sys

        src_bytes = CPP_SOURCE.read_bytes()
        sha = hashlib.sha256(src_bytes).hexdigest()[:16]
        ext = ".dylib" if sys.platform == "darwin" else ".so"
        so_path = Path(tempfile.gettempdir()) / f"dag_mcts_cpp_kernels_{sha}{ext}"
        if not so_path.is_file():
            cxx = os.environ.get("CXX") or shutil.which("g++") or shutil.which("clang++")
            if not cxx:
                raise RuntimeError(
                    "C++17 compiler not found (tried $CXX, g++, clang++). "
                    "Install g++ or clang++ (e.g. `sudo apt install g++` or Xcode Command Line Tools) "
                    "to build native C++17 kernels."
                )
            tmp_so = so_path.with_name(f"{so_path.stem}_{os.getpid()}.tmp{ext}")
            subprocess.run(
                [
                    cxx, "-O3", "-std=c++17", "-Wall", "-Wextra", "-Werror",
                    "-shared", "-fPIC", str(CPP_SOURCE), "-o", str(tmp_so),
                ],
                check=True,
            )
            tmp_so.replace(so_path)
        lib = ctypes.CDLL(str(so_path))
        fn = lib.run_certified_kernel
        fn.argtypes = [
            ctypes.c_int,
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_double),
            ctypes.c_int,
            ctypes.c_uint64,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_double,
            ctypes.c_double,
            ctypes.c_double,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.POINTER(_CppRunResult),
        ]
        fn.restype = ctypes.c_int
        cls._lib = lib
        cls._so_path = so_path
        return lib

    @classmethod
    def run(cls, problem: Problem, seed: int, policy_kind: str, method: str,
            epsilon: float, delta: float = 0.05, c_explore: float = 2.0,
            q_cert: int = 1, schedule: str = "box", effective_m: int | None = None,
            cap: int = 200000, reward_kind: int | None = None) -> dict:
        lib = cls.ensure_loaded()
        g = problem.graph
        n = len(g)
        offsets = [0]
        cols: list[int] = []
        for row in g.children:
            cols.extend(row)
            offsets.append(len(cols))
        means_arr = [0.0] * n
        for z, val in problem.means.items():
            means_arr[z] = float(val)
        if reward_kind is None:
            if hasattr(problem, "reward_kind"):
                reward_kind = problem.reward_kind
            elif len(problem.deterministic) == len(g.leaves):
                reward_kind = 0
            elif "coded" in problem.name:
                reward_kind = 2
            else:
                reward_kind = 1

        c_offsets = (ctypes.c_int * len(offsets))(*offsets)
        c_cols = (ctypes.c_int * max(1, len(cols)))(*(cols if cols else [0]))
        c_means = (ctypes.c_double * n)(*means_arr)
        res = _CppRunResult()
        rc = lib.run_certified_kernel(
            n,
            g.root,
            c_offsets,
            c_cols,
            c_means,
            int(reward_kind),
            ctypes.c_uint64(seed & 0xFFFFFFFFFFFFFFFF),
            cls.POLICY_CODES[policy_kind],
            cls.METHOD_CODES[method],
            cls.SCHEDULE_CODES[schedule],
            float(epsilon),
            float(delta),
            float(c_explore),
            int(q_cert),
            int(0 if effective_m is None else effective_m),
            int(cap),
            ctypes.byref(res),
        )
        if rc != 0:
            raise RuntimeError(f"C++ kernel failed with status {rc}")
        return {
            "init_us": res.init_ns / 1000.0,
            "total_us": res.total_ns / 1000.0,
            "init_ms": res.init_ns / 1e6,
            "end_ms": res.total_ns / 1e6,
            "steps": int(res.steps),
            "work": int(res.work),
            "messages": int(res.messages),
            "retired": int(res.retired),
            "strict_changes": int(res.strict_changes),
            "action": int(res.action),
            "certified": bool(res.certified),
        }


class WitnessMaxHeap:
    """Indexed max-heap keyed by `(value, -leaf_id)` with exact tie-breaking."""

    def __init__(self, vals: list[float], leaves: list[int], work: UCTWork):
        self.vals = list(vals)
        self.leaves = list(leaves)
        self.ids = list(range(len(self.vals)))
        self.positions = list(range(len(self.vals)))
        self.work = work
        work.initialization += 4 * len(self.vals)
        for i in reversed(range(len(self.ids) // 2)):
            self._down(i)

    def _better(self, a: int, b: int) -> bool:
        self.work.heap_comparisons += 1
        va, vb = self.vals[a], self.vals[b]
        if va != vb:
            return va > vb
        la, lb = self.leaves[a], self.leaves[b]
        if la != lb:
            return la < lb
        return a < b

    def _swap(self, i: int, j: int) -> None:
        a, b = self.ids[i], self.ids[j]
        self.ids[i], self.ids[j] = b, a
        self.positions[a], self.positions[b] = j, i
        self.work.heap_writes += 4

    def _down(self, i: int) -> None:
        size = len(self.ids)
        while 2 * i + 1 < size:
            ch = 2 * i + 1
            if ch + 1 < size and self._better(self.ids[ch + 1], self.ids[ch]):
                ch += 1
            if not self._better(self.ids[ch], self.ids[i]):
                break
            self._swap(i, ch)
            i = ch

    def update(self, item: int, val: float, leaf: int) -> None:
        old_v, old_l = self.vals[item], self.leaves[item]
        self.vals[item] = val
        self.leaves[item] = leaf
        self.work.heap_writes += 2
        if val == old_v and leaf == old_l:
            return
        pos = self.positions[item]
        up = (val > old_v) or (val == old_v and leaf < old_l)
        if up:
            while pos and self._better(item, self.ids[(pos - 1) // 2]):
                par = (pos - 1) // 2
                self._swap(pos, par)
                pos = par
        else:
            self._down(pos)

    @property
    def top(self) -> int:
        return self.ids[0]

    def second(self) -> int | None:
        if len(self.ids) < 2:
            return None
        if len(self.ids) == 2 or self._better(self.ids[1], self.ids[2]):
            return self.ids[1]
        return self.ids[2]


class _WitnessDAGBounds:
    """Quotient-DAG MAX propagator tracking `(lower[v], upper[v], upper_leaf[v])`."""

    def __init__(self, circuit: DAG, leaf_to_orig: dict[int, int], work: UCTWork,
                 protected_vertices: tuple[int, ...] | None = None):
        self.graph = circuit
        self.work = work
        n = len(circuit)
        self.lower = [0.0] * n
        self.upper = [1.0] * n
        self.upper_leaf = [10**9] * n
        for c_leaf, orig_leaf in leaf_to_orig.items():
            self.upper_leaf[c_leaf] = orig_leaf

        # Initialize internal upper_leaf in reverse topological order
        for v in reversed(circuit.order):
            row = circuit.children[v]
            if row:
                self.upper_leaf[v] = min(self.upper_leaf[c] for c in row)
                work.initialization += len(row)

        if protected_vertices is None:
            self.protected_set = frozenset({circuit.root, *circuit.children[circuit.root]})
        else:
            self.protected_set = frozenset(set(protected_vertices) | {circuit.root})

        self.low_heap = [IndexedMaxHeap([0.0] * len(row), work) if row else None
                         for row in circuit.children]
        self.high_heap = [
            WitnessMaxHeap([1.0] * len(row), [self.upper_leaf[c] for c in row], work) if row else None
            for row in circuit.children
        ]
        self.rev_edges: list[list[tuple[int, int]]] = [[] for _ in range(n)]
        for p, row in enumerate(circuit.children):
            for a, c in enumerate(row):
                self.rev_edges[c].append((p, a))
                work.initialization += 2
        self.queued = [False] * n
        self.changed_outputs: list[int] = []
        self.messages = 0
        work.initialization += 8 * n

    def publish(self, c_leaf: int, orig_leaf: int, lo: float, hi: float) -> None:
        self.changed_outputs.clear()
        if self.lower[c_leaf] == lo and self.upper[c_leaf] == hi:
            return
        self.lower[c_leaf] = lo
        self.upper[c_leaf] = hi
        self.upper_leaf[c_leaf] = orig_leaf
        if c_leaf in self.protected_set:
            self.changed_outputs.append(c_leaf)
        rank = self.graph.rank
        heap: list[tuple[int, int]] = [(-rank[c_leaf], c_leaf)]
        self.queued[c_leaf] = True
        self.work.statistic_writes += 3
        while heap:
            _, u = heapq.heappop(heap)
            self.queued[u] = False
            self.work.heap_comparisons += 1
            for p, a in self.rev_edges[u]:
                self.messages += 1
                self.work.edge_reads += 2
                lh = self.low_heap[p]
                hh = self.high_heap[p]
                if lh.keys[a] != self.lower[u]:
                    lh.update(a, self.lower[u])
                if hh.vals[a] != self.upper[u] or hh.leaves[a] != self.upper_leaf[u]:
                    hh.update(a, self.upper[u], self.upper_leaf[u])
                nlo = lh.keys[lh.top]
                top_h = hh.top
                nhi = hh.vals[top_h]
                nwit = hh.leaves[top_h]
                self.work.query_reads += 3
                if (self.lower[p] != nlo or self.upper[p] != nhi or self.upper_leaf[p] != nwit):
                    self.lower[p] = nlo
                    self.upper[p] = nhi
                    self.upper_leaf[p] = nwit
                    self.work.statistic_writes += 3
                    if p in self.protected_set:
                        self.changed_outputs.append(p)
                    if not self.queued[p]:
                        heapq.heappush(heap, (-rank[p], p))
                        self.queued[p] = True
                        self.work.heap_comparisons += 1


class WitnessMarginalGraph:
    """Marginal root-interval monitor exposing `(leader, gap, z_in_leader, z_in_challenger)`."""

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box"):
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule)
        circuit, self.mapping, _ = quotient(graph, w)
        inv = {alias: orig for orig, alias in self.mapping.items()}
        self.compile_work = w.total
        self.bounds = _WitnessDAGBounds(circuit, inv, w)

    def step(self, leaf: int, reward: float) -> bool:
        iv = self.evidence.observe(leaf, reward)
        if iv is None:
            return False
        self.bounds.publish(self.mapping[leaf], leaf, *iv)
        return True

    def query_witness(self) -> tuple[int, float, int, int]:
        root = self.bounds.graph.root
        row = self.bounds.graph.children[root]
        self.work.query_reads += 2
        if not row:
            return (-1, 0.0, -1, -1)
        if len(row) == 1:
            return (0, 0.0, self.bounds.upper_leaf[row[0]], -1)
        lh = self.bounds.low_heap[root]
        best = lh.top
        best_lo = lh.keys[best]
        # Canonical challenger: argmax_{b != best} (U_t(b), -b)
        chal = max((b for b in range(len(row)) if b != best),
                   key=lambda b: (self.bounds.upper[row[b]], -b))
        self.work.query_reads += 2 * len(row)
        gap = max(0.0, self.bounds.upper[row[chal]] - best_lo)
        return (best, gap, self.bounds.upper_leaf[row[best]], self.bounds.upper_leaf[row[chal]])


class WitnessDualCovers:
    """Charged Dual Covers monitor exposing canonical `(best_a, reg, z_in, z_out)`."""

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box", layout: str = "best"):
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule)
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

        self.low = [0.0] * (2 * self.size)
        self.high = [-math.inf] * (2 * self.size)
        self.high_leaf = [10**9] * (2 * self.size)
        for j, orig_z in enumerate(self.leaves):
            self.high[self.size + j] = 1.0
            self.high_leaf[self.size + j] = orig_z
        for d in reversed(range(1, self.size)):
            self.low[d] = max(self.low[2 * d], self.low[2 * d + 1])
            l_key = (self.high[2 * d], -self.high_leaf[2 * d])
            r_key = (self.high[2 * d + 1], -self.high_leaf[2 * d + 1])
            if l_key >= r_key:
                self.high[d], self.high_leaf[d] = self.high[2 * d], self.high_leaf[2 * d]
            else:
                self.high[d], self.high_leaf[d] = self.high[2 * d + 1], self.high_leaf[2 * d + 1]
        w.initialization += 8 * self.size + m

        self.pos_subs: list[list[tuple[int, int]]] = [[] for _ in range(2 * self.size)]
        self.neg_subs: list[list[tuple[int, int]]] = [[] for _ in range(2 * self.size)]
        self.pos_heaps: list[IndexedMaxHeap] = []
        self.neg_heaps: list[WitnessMaxHeap | None] = []
        init_reg: list[float] = []

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

        self.regret_heap = IndexedMinHeap(init_reg, w) if self.num_actions else None
        self.compile_work = w.total

    def step(self, leaf: int, reward: float) -> bool:
        iv = self.evidence.observe(leaf, reward)
        if iv is None:
            return False
        d = self.size + self.rank[leaf]
        lo, hi = iv
        hl = leaf
        touched: set[int] = set()
        while True:
            self.work.query_reads += 3
            lc = (lo != self.low[d])
            hc = (hi != self.high[d]) or (hl != self.high_leaf[d])
            if not lc and not hc:
                break
            if lc:
                self.low[d] = lo
                self.work.statistic_writes += 1
                for a, idx in self.pos_subs[d]:
                    self.work.edge_reads += 1
                    self.pos_heaps[a].update(idx, lo)
                    touched.add(a)
            if hc:
                self.high[d] = hi
                self.high_leaf[d] = hl
                self.work.statistic_writes += 2
                for a, idx in self.neg_subs[d]:
                    self.work.edge_reads += 1
                    nh = self.neg_heaps[a]
                    assert nh is not None
                    nh.update(idx, hi, hl)
                    touched.add(a)
            if d == 1:
                break
            d //= 2
            lo = max(self.low[2 * d], self.low[2 * d + 1])
            l_key = (self.high[2 * d], -self.high_leaf[2 * d])
            r_key = (self.high[2 * d + 1], -self.high_leaf[2 * d + 1])
            if l_key >= r_key:
                hi, hl = self.high[2 * d], self.high_leaf[2 * d]
            else:
                hi, hl = self.high[2 * d + 1], self.high_leaf[2 * d + 1]
            self.work.query_reads += 6
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
        return True

    def query_witness(self) -> tuple[int, float, int, int]:
        self.work.query_reads += 3
        if self.regret_heap is None:
            return (-1, 0.0, -1, -1)
        best = self.regret_heap.top
        reg = self.regret_heap.keys[best]
        # Inside witness z_in over O(log M) positive dyadic blocks:
        pca = self.pos_covers[best]
        best_d = max(pca, key=lambda d: (self.high[d], -self.high_leaf[d]))
        self.work.query_reads += 2 * len(pca)
        self.work.heap_comparisons += len(pca)
        z_in = self.high_leaf[best_d]
        nh = self.neg_heaps[best]
        z_out = -1 if nh is None else nh.leaves[nh.top]
        return (best, reg, z_in, z_out)


class WitnessDirectGraphRegret:
    """Direct Quotient-Graph + Terminal Witness Heap exact-regret monitor."""

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box"):
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule)
        circuit, self.mapping, _ = quotient(graph, w)
        inv = {alias: orig for orig, alias in self.mapping.items()}
        m = len(graph.leaves)
        words = max(1, (m + 63) // 64)
        self.leaf_rank = {leaf: j for j, leaf in enumerate(graph.leaves)}

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
        self.term_upper = WitnessMaxHeap([1.0] * m, list(graph.leaves), w)
        self.compile_work = w.total
        self.bounds = _WitnessDAGBounds(circuit, inv, w)

    def step(self, leaf: int, reward: float) -> bool:
        iv = self.evidence.observe(leaf, reward)
        if iv is None:
            return False
        self.bounds.publish(self.mapping[leaf], leaf, *iv)
        self.term_upper.update(self.leaf_rank[leaf], iv[1], leaf)
        return True

    def query_witness(self) -> tuple[int, float, int, int]:
        root = self.bounds.graph.root
        row = self.bounds.graph.children[root]
        if not row:
            return (-1, 0.0, -1, -1)
        top_j = self.term_upper.top
        top_u = self.term_upper.vals[top_j]
        top_z = self.term_upper.leaves[top_j]
        self.work.query_reads += 3

        holders = [a for a in range(len(row)) if not self.full_support[a] and ((self.action_masks[a] >> top_j) & 1)]
        sorted_j: list[int] | None = None
        if len(holders) > 2:
            vals = self.term_upper.vals
            lvs = self.term_upper.leaves
            sorted_j = sorted(range(len(vals)), key=lambda j: (-vals[j], lvs[j]))
            self.work.heap_comparisons += len(vals) * max(1, len(vals).bit_length())

        best_a = 0
        best_reg = math.inf
        best_z_out = -1
        for a, c in enumerate(row):
            la = self.bounds.lower[c]
            self.work.query_reads += 1
            if self.full_support[a]:
                reg, z_out = 0.0, -1
            elif not ((self.action_masks[a] >> top_j) & 1):
                reg, z_out = max(0.0, top_u - la), top_z
            elif sorted_j is not None:
                mask = self.action_masks[a]
                ua_out, z_out = -math.inf, -1
                for j in sorted_j:
                    self.work.query_reads += 1
                    self.work.heap_comparisons += 1
                    if not ((mask >> j) & 1):
                        ua_out = self.term_upper.vals[j]
                        z_out = self.term_upper.leaves[j]
                        break
                reg = max(0.0, ua_out - la)
            else:
                mask = self.action_masks[a]
                ua_out, z_out = -math.inf, 10**9
                for j, uval in enumerate(self.term_upper.vals):
                    self.work.query_reads += 1
                    self.work.heap_comparisons += 1
                    if not ((mask >> j) & 1):
                        lz = self.term_upper.leaves[j]
                        if (uval, -lz) > (ua_out, -z_out):
                            ua_out, z_out = uval, lz
                reg = max(0.0, ua_out - la)
            if reg < best_reg:
                best_reg = reg
                best_a = a
                best_z_out = z_out
        return (best_a, best_reg, self.bounds.upper_leaf[row[best_a]], best_z_out)


class WitnessFactorizedRegret:
    """Gate-factorized exact-regret monitor exposing canonical `(best_a, reg, z_in, z_out)`."""

    def __init__(self, graph: DAG, delta: float = 0.05, schedule: str = "box"):
        self.graph = graph
        self.work = w = UCTWork()
        self.evidence = NestedIntervals(graph, w, delta=delta, schedule=schedule)
        base, leaf_map, _ = quotient(graph, w)
        m = len(graph.leaves)
        words = max(1, (m + 63) // 64)
        inv_orig = {alias: orig for orig, alias in leaf_map.items()}
        inv_bit = {alias: j for j, (_, alias) in enumerate(sorted(leaf_map.items()))}
        bit_to_alias = {j: alias for alias, j in inv_bit.items()}
        self.mapping = leaf_map

        masks = [0] * len(base)
        popcounts = [0] * len(base)
        for v in reversed(base.order):
            ch = base.children[v]
            if not ch:
                masks[v] = 1 << inv_bit[v]
                popcounts[v] = 1
            else:
                acc = 0
                for c in ch:
                    acc |= masks[c]
                    w.query_reads += words
                masks[v] = acc
                popcounts[v] = acc.bit_count()

        base_root = base.root
        pos_nodes = [base.children[w_id][0] for w_id in base.children[base_root]]
        first_wrap = base_root - len(pos_nodes)
        internal = [v for v in range(first_wrap) if base.children[v]]
        internal.sort(key=lambda v: (-popcounts[v], v))
        w.heap_comparisons += len(internal) * max(1, len(internal).bit_length())

        rows = list(base.children[:first_wrap])
        full_mask = (1 << m) - 1
        self.num_actions = len(pos_nodes)
        self.pos_out: list[int] = []
        self.neg_out: list[int | None] = []

        for pnode in pos_nodes:
            self.pos_out.append(pnode)
            comp = full_mask ^ masks[pnode]
            if comp == 0:
                self.neg_out.append(None)
                continue
            rem = comp
            chosen: list[int] = []
            for g in internal:
                if (rem & (rem - 1)) == 0:
                    break
                mg = masks[g]
                w.query_reads += 2 * words
                if (mg & masks[pnode]) == 0 and (mg & rem) != 0:
                    chosen.append(g)
                    rem &= ~mg
                    if rem == 0:
                        break
            while rem:
                lsb = rem & -rem
                chosen.append(bit_to_alias[lsb.bit_length() - 1])
                rem ^= lsb
            if len(chosen) == 1:
                self.neg_out.append(chosen[0])
            else:
                nid = len(rows)
                rows.append(tuple(chosen))
                self.neg_out.append(nid)
                w.initialization += 8 + 6 * len(chosen)

        outputs = list(dict.fromkeys(list(self.pos_out) + [n for n in self.neg_out if n is not None]))
        super_root = len(rows)
        rows.append(tuple(outputs))
        circuit = DAG(rows, root=super_root)
        self.compile_work = w.total
        self.bounds = _WitnessDAGBounds(circuit, inv_orig, w, protected_vertices=tuple(outputs))

        self.pos_watch: dict[int, list[int]] = {}
        self.neg_watch: dict[int, list[int]] = {}
        init_reg: list[float] = []
        for a in range(self.num_actions):
            p = self.pos_out[a]
            self.pos_watch.setdefault(p, []).append(a)
            n = self.neg_out[a]
            if n is None:
                init_reg.append(0.0)
            else:
                self.neg_watch.setdefault(n, []).append(a)
                init_reg.append(max(0.0, self.bounds.upper[n] - self.bounds.lower[p]))
        self.regret_heap = IndexedMinHeap(init_reg, w) if self.num_actions else None

    def step(self, leaf: int, reward: float) -> bool:
        iv = self.evidence.observe(leaf, reward)
        if iv is None:
            return False
        self.bounds.publish(self.mapping[leaf], leaf, *iv)
        if self.regret_heap is not None and self.bounds.changed_outputs:
            touched: set[int] = set()
            for g in self.bounds.changed_outputs:
                if g in self.pos_watch:
                    touched.update(self.pos_watch[g])
                if g in self.neg_watch:
                    touched.update(self.neg_watch[g])
            for a in touched:
                n = self.neg_out[a]
                reg = 0.0 if n is None else max(0.0, self.bounds.upper[n] - self.bounds.lower[self.pos_out[a]])
                self.regret_heap.update(a, reg)
        return True

    def query_witness(self) -> tuple[int, float, int, int]:
        self.work.query_reads += 3
        if self.regret_heap is None:
            return (-1, 0.0, -1, -1)
        best = self.regret_heap.top
        reg = self.regret_heap.keys[best]
        z_in = self.bounds.upper_leaf[self.pos_out[best]]
        n = self.neg_out[best]
        z_out = -1 if n is None else self.bounds.upper_leaf[n]
        return (best, reg, z_in, z_out)


def build_witness_monitor(graph: DAG, method: str, delta: float = 0.05, schedule: str = "box"):
    if method == "dual-covers":
        return WitnessDualCovers(graph, delta=delta, schedule=schedule, layout="best")
    if method == "direct-graph-regret":
        return WitnessDirectGraphRegret(graph, delta=delta, schedule=schedule)
    if method == "factorized-regret":
        return WitnessFactorizedRegret(graph, delta=delta, schedule=schedule)
    if method == "marginal-graph":
        return WitnessMarginalGraph(graph, delta=delta, schedule=schedule)
    raise ValueError(f"Unknown witness monitor method: {method}")


class ActiveDAGLUCBSession:
    """Active witness-guided pure-exploration controller on a DAG (Theorem 2.4).

    Supports both:
    - `marginal-graph` (`Marginal-DAG-LUCB`): compares canonical leader and marginal challenger,
      routing observations to whichever optimistic witness in S(leader) or S(challenger)
      currently has the wider confidence interval.
    - `dual-covers` / `direct-graph-regret` / `factorized-regret` (`Exact-Regret-DAG-LUCB`):
      compares the inside optimistic witness z_in in S(a*_t) against the OUTSIDE challenger
      witness z_out in Z \\ S(a*_t), never wasting challenger draws on shared terminals!
    """

    def __init__(self, problem: Problem, seed: int, monitor_method: str,
                 epsilon: float, delta: float = 0.05, schedule: str = "box"):
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.oracle = problem.oracle(seed)
        self.policy_work = UCTWork()
        self.monitor = build_witness_monitor(self.graph, monitor_method, delta=delta, schedule=schedule)

        # Precompute canonical shortest root-to-terminal path for every leaf via BFS.
        parent_step: dict[int, int] = {self.graph.root: -1}
        q = deque([self.graph.root])
        while q:
            u = q.popleft()
            self.policy_work.edge_reads += len(self.graph.children[u])
            for c in self.graph.children[u]:
                if c not in parent_step:
                    parent_step[c] = u
                    q.append(c)
                    self.policy_work.statistic_writes += 1
        self.leaf_paths: dict[int, tuple[int, ...]] = {}
        for z in self.graph.leaves:
            cur = z
            rev = []
            while cur != -1:
                rev.append(cur)
                cur = parent_step[cur]
            self.leaf_paths[z] = tuple(reversed(rev))
            self.policy_work.initialization += len(rev)

        self.calls = 0
        self.query = self.monitor.query_witness()
        self.certified = (not self.monitor.evidence.conflict) and (self.query[1] <= epsilon)
        self.action = self.query[0]

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.monitor.evidence.conflict:
            raise RuntimeError("ActiveDAGLUCBSession already terminated")
        best_a, _, z_in, z_out = self.query
        ev = self.monitor.evidence
        if z_out < 0:
            target = z_in
        else:
            w_in = ev.upper[z_in] - ev.lower[z_in]
            w_out = ev.upper[z_out] - ev.lower[z_out]
            self.policy_work.query_reads += 4
            self.policy_work.heap_comparisons += 1
            target = z_in if w_in >= w_out else z_out
        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1
        reward = self.oracle.sample(target)
        self.calls += 1
        self.policy_work.oracle_calls += 1
        self.monitor.step(target, reward)
        self.query = self.monitor.query_witness()
        self.certified = (not ev.conflict) and (self.query[1] <= self.epsilon)
        self.action = self.query[0]
        return path, reward

    @property
    def work(self) -> int:
        return (self.policy_work.total + self.monitor.work.total - self.calls
                + getattr(self.oracle, "operations", 0))
