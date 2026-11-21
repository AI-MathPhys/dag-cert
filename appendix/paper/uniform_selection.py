"""Paid fresh-uniform LUCB selection on validated sliding-window DAGs.

Both backends use max/count tournament trees and query-boundary publications.
The only difference is a global range index versus materialized reusable
inside/outside tournament heaps. No terminal means enter either backend.
"""
import random
from dag_mcts.certified_uct import UCTWork, IndexedMaxHeap
from paper.implicit_support import Topology, ImplicitSearch
from paper.sampling_confidence_allcount import MixtureIntervals
from paper.reuse_heaps import xor_ranges


class CountTree:
    def __init__(self, values, w):
        self.w = w; self.n = len(values); self.size = 1 << (self.n-1).bit_length()
        self.value = [-1]*(2*self.size); self.count = [0]*(2*self.size)
        w.initialization += 4*self.size+3
        for i, v in enumerate(values):
            self.value[self.size+i] = v; self.count[self.size+i] = int(v >= 0)
            w.statistic_writes += 2
        for p in range(self.size-1, 0, -1): self._pull(p)

    def _pull(self, p):
        v = self.value; c = self.count; l = 2*p; r = l+1
        m = max(v[l], v[r]); n = (c[l] if v[l] == m else 0)+(c[r] if v[r] == m else 0)
        self.w.query_reads += 6; self.w.heap_comparisons += 4
        changed = m != v[p] or n != c[p]
        v[p] = m; c[p] = n; self.w.heap_writes += 2
        return changed

    def update(self, i, v):
        p = self.size+i; self.w.query_reads += 1
        if self.value[p] == v: return
        self.value[p] = v; self.count[p] = int(v >= 0); self.w.heap_writes += 2
        p //= 2
        while p:
            if not self._pull(p): break
            p //= 2

    def cover(self, ranges):
        """Disjoint tree nodes in descending leaf-rank order."""
        out = []
        for a, b in reversed(ranges):
            left = []; right = []; a += self.size; b += self.size
            self.w.query_reads += 2
            while a < b:
                self.w.query_reads += 2; self.w.heap_comparisons += 2
                if a & 1: left.append(a); a += 1; self.w.statistic_writes += 1
                if b & 1: b -= 1; right.append(b); self.w.statistic_writes += 1
                a //= 2; b //= 2
            out.extend(right); out.extend(reversed(left))
            self.w.statistic_writes += len(left)+len(right)
        return out

    def select(self, nodes, rng=None, rank=None):
        """Return maximum and uniform maximizer (or deterministic order statistic)."""
        maximum = -1; total = 0; w = self.w
        for p in nodes:
            v = self.value[p]; w.query_reads += 2; w.heap_comparisons += 2
            if v > maximum: maximum = v; total = self.count[p]
            elif v == maximum: total += self.count[p]
        if total == 0: return -1, None
        k = rng.randrange(total) if rank is None else rank; w.score_evaluations += int(rank is None)
        if not 0 <= k < total: raise IndexError(k)
        for p in nodes:
            w.query_reads += 2; w.heap_comparisons += 2
            if self.value[p] != maximum: continue
            if k >= self.count[p]: k -= self.count[p]; continue
            while p < self.size:
                r = 2*p+1; n = self.count[r] if self.value[r] == maximum else 0
                w.query_reads += 2; w.heap_comparisons += 2
                if k < n: p = r
                else: k -= n; p = r-1
            return maximum, p-self.size
        raise AssertionError('bad max/count tree')


class WindowCandidates:
    def __init__(self, A, w):
        self.A = A; self.w = w
        self.left = IndexedMaxHeap([(0, j) for j in range(A)], w)
        self.right = IndexedMaxHeap([(0, -j) for j in range(A, 2*A-1)], w)
        w.initialization += 2*(2*A-1)

    def update(self, j, lo):
        if j < self.A: self.left.update(j, (lo, j))
        else: self.right.update(j-self.A, (lo, -j))

    def eligible(self):
        l = self.left.keys[self.left.top]; r = self.right.keys[self.right.top]
        m = max(l[0], r[0]); end = l[1]+1 if l[0] == m else 0
        start = -r[1]-self.A+1 if r[0] == m else self.A
        self.w.query_reads += 8; self.w.heap_comparisons += 4
        if end >= start: end = self.A; start = self.A
        return m, end, start

    def select(self, rng, fixed=False):
        m, end, start = self.eligible(); n = end+self.A-start
        k = 0 if fixed else rng.randrange(n); self.w.score_evaluations += int(not fixed)
        return (k if k < end else start+k-end), m


class UniformIndex:
    def __init__(self, graph, w, scale, method, seed, fixed=False):
        if method not in ('uniform_range', 'uniform_reuse'): raise ValueError(method)
        self.w = w; self.method = method; self.topology = Topology(graph, w, 8)
        t = self.topology; self.A = len(graph.children[graph.root]); L = len(t.leaves)
        if L != 2*self.A-1: raise ValueError('requires sliding-window supports')
        for a in range(self.A):
            rs = t.ranges[graph.children[graph.root][a]]; w.query_reads += 4
            if rs != ((a, a+self.A),): raise ValueError('requires exact rank windows')
        # Descending ranks coincide with canonical ID order in the replay family.
        if any(t.leaves[j] <= t.leaves[j+1] for j in range(L-1)):
            raise ValueError('this implementation requires reverse canonical leaf IDs')
        w.query_reads += 2*(L-1)
        self.lower = [0]*L; self.upper = [scale]*L; self.pending = {}
        self.candidates = WindowCandidates(self.A, w); self.rng = random.Random(1177000+seed)
        self.fixed = fixed; self.tree = CountTree(self.upper, w) if method == 'uniform_range' else None
        self.groups = None; self.active = None; self.queries = self.flushes = 0
        self.delta_atoms = self.moved_atoms = self.switches = self.rebuilds = self.upper_changes = 0
        self.selection_work = self.partition_work = 0
        w.initialization += 2*L+18

    def publish(self, leaf, lo, hi):
        self.pending[leaf] = (lo, hi); self.w.statistic_writes += 3

    def flush(self):
        for leaf, (lo, hi) in self.pending.items():
            j = self.topology.rank[leaf]; self.w.query_reads += 5
            if not self.lower[j] <= lo <= hi <= self.upper[j]: raise ValueError('non-nested interval')
            if lo != self.lower[j]:
                self.lower[j] = lo; self.candidates.update(j, lo); self.w.statistic_writes += 1
            if hi != self.upper[j]:
                self.upper[j] = hi; self.upper_changes += 1; self.w.statistic_writes += 2
                if self.tree is not None: self.tree.update(j, hi)
                elif self.groups is not None:
                    self.groups[int(self.active <= j < self.active+self.A)].update(j, hi)
                    self.w.query_reads += 2
            self.flushes += 1
        self.w.statistic_writes += len(self.pending)+1; self.pending.clear()

    def _switch(self, a):
        w = self.w; start = w.total; L = len(self.upper); w.query_reads += 2
        if self.active == a: self.partition_work += w.total-start; return
        changes = () if self.active is None else xor_ranges(((self.active, self.active+self.A),), ((a, a+self.A),), w)
        D = sum(h-l for l, h in changes); w.query_reads += 2*len(changes)
        self.delta_atoms += D; self.switches += self.active is not None
        if self.groups is None or D*L.bit_length() > L:
            keys = [[], []]
            for j, u in enumerate(self.upper):
                side = int(a <= j < a+self.A); keys[side].append(u); keys[1-side].append(-1)
                w.query_reads += 3; w.statistic_writes += 2
            self.groups = [CountTree(xs, w) for xs in keys]; self.rebuilds += 1
        else:
            for l, h in changes:
                for j in range(l, h):
                    new = int(a <= j < a+self.A)
                    self.groups[1-new].update(j, -1); self.groups[new].update(j, self.upper[j])
                    self.moved_atoms += 1; w.query_reads += 3
        self.active = a; w.statistic_writes += 4
        self.partition_work += w.total-start

    def query(self):
        self.flush(); start = self.w.total; a, lo = self.candidates.select(self.rng, self.fixed)
        if self.tree is not None:
            x = self.tree.select(self.tree.cover(((a, a+self.A),)), self.rng)
            y = self.tree.select(self.tree.cover(((0, a), (a+self.A, len(self.upper)))), self.rng)
        else:
            before = self.partition_work; self._switch(a)
            start += self.partition_work-before
            x = self.groups[1].select([1], self.rng); y = self.groups[0].select([1], self.rng)
        self.selection_work += self.w.total-start; self.queries += 1
        self.w.query_reads += 2
        return a, lo, (x[0], -self.topology.leaves[x[1]]), (y[0], -self.topology.leaves[y[1]])


class UniformSearch(ImplicitSearch):
    def __init__(self, p, c, seed, method):
        self.g = p.graph; self.work = UCTWork(); w = self.work
        w.initialization += 16*len(self.g)+10*sum(map(len, self.g.children))+4*len(self.g.leaves)
        self.index = UniformIndex(self.g, w, c['scale'], method, seed, c.get('fixed_candidate', False))
        self.ev = MixtureIntervals(self.g, w, c['delta'], c['scale']); self.oracle = p.oracle(seed)
        self.tolerance = round(c['epsilon']*c['scale']); self.calls = 0; self.decision = self.pair = None
        if abs(self.tolerance-c['epsilon']*c['scale']) > 1e-10: raise ValueError('require exact grid tolerance')
