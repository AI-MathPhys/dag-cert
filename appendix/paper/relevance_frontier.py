"""Paid, reusable relevance frontiers for exact shared-support LUCB queries.

No means enter the indexes.  All four backends share the same interval
compiler, upper/lower tournament indexes, candidate policy and evidence.
The frontier is only a shortcut; its failed checks and bounded construction
attempts are charged, and exact range queries answer every miss.
"""
import math
import random

from dag_mcts.certified_uct import UCTWork
from paper.uniform_selection import CountTree
from paper.sampling_confidence_allcount import MixtureIntervals

METHODS = ('range_memo', 'lazy_cover', 'cert_heap', 'frontier')


def merge(xs, w):
    # Charge comparison sorting explicitly, rather than assume free ordering.
    from functools import cmp_to_key
    def cmp(a, b):
        w.heap_comparisons += 1
        return (a > b) - (a < b)
    out = []
    for lo, hi in sorted(xs, key=cmp_to_key(cmp)):
        w.query_reads += 2; w.statistic_writes += 1
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(hi, out[-1][1]))
            w.heap_comparisons += 2
        else:
            out.append((lo, hi)); w.heap_comparisons += 1
    return tuple(out)


class Compiled:
    """Paid DAG compilation; root intervals only are retained after validation.

    Intermediate interval unions are paid and then released. This can be
    expensive on arbitrary DAGs and is common to all measured backends.
    """
    def __init__(self, g, w):
        self.leaves = g.leaves; self.rank = {v: j for j, v in enumerate(g.leaves)}
        self.parent = [-1] * len(g); rows = [None] * len(g)
        w.initialization += 3*len(g)+2*len(self.leaves)
        for v in g.order:
            for c in g.children[v]:
                w.edge_reads += 1; w.query_reads += 1
                if self.parent[c] < 0:
                    self.parent[c] = v; w.statistic_writes += 1
        for v in reversed(g.order):
            if not g.children[v]:
                j = self.rank[v]; rows[v] = ((j, j+1),); w.statistic_writes += 1
            else:
                xs = []
                for c in g.children[v]:
                    xs.extend(rows[c]); w.edge_reads += 1
                    w.query_reads += len(rows[c]); w.statistic_writes += len(rows[c])
                rows[v] = merge(xs, w)
        self.inside = tuple(rows[a] for a in g.children[g.root]); outside = []
        for rs in self.inside:
            prev = 0; comp = []
            for lo, hi in rs:
                w.query_reads += 2; w.heap_comparisons += 1
                if prev < lo: comp.append((prev, lo)); w.statistic_writes += 1
                prev = hi
            if prev < len(self.leaves): comp.append((prev, len(self.leaves)))
            outside.append(tuple(comp)); w.statistic_writes += len(comp)+1
        self.outside = tuple(outside)
        # Releasing the temporary compilation is also charged.
        w.statistic_writes += sum(map(len, rows)) + len(rows)

    def contains(self, a, j, w):
        rs = self.inside[a]; lo = 0; hi = len(rs)
        w.query_reads += 2
        while lo < hi:
            mid = (lo+hi)//2; w.query_reads += 1; w.heap_comparisons += 1
            if rs[mid][0] <= j: lo = mid+1
            else: hi = mid
        w.query_reads += 1; w.heap_comparisons += 2
        return lo > 0 and j < rs[lo-1][1]

    def classify(self, a, lo, hi, w):
        rs = self.inside[a]; left = 0; right = len(rs)
        w.query_reads += 2
        while left < right:
            mid = (left+right)//2; w.query_reads += 1; w.heap_comparisons += 1
            if rs[mid][1] <= lo: left = mid+1
            else: right = mid
        w.query_reads += 2; w.heap_comparisons += 4
        if left == len(rs) or rs[left][0] >= hi: return 0
        return 1 if rs[left][0] <= lo and hi <= rs[left][1] else -1


class Index:
    def __init__(self, g, w, scale, method, seed, cap=12, slack=0.025):
        if method not in METHODS: raise ValueError(method)
        self.w = w; self.method = method; self.top = Compiled(g, w)
        self.lower = [0]*len(g.leaves); self.upper = [scale]*len(g.leaves)
        self.lt = CountTree(self.lower, w); self.ut = CountTree(self.upper, w)
        self.rng = random.Random(seed+791901); self.scale = scale
        self.covers = {}; self.memo = {}; self.views = {}; self.revision = 0
        self.F = None; self.threshold = scale+1; self.cap = cap
        self.slack = max(1, math.ceil(slack*scale)); self.attempt_at = 1; self.backoff = 1
        self.witnesses = None; self.q = 0
        self.stats = dict(builds=0, aborts=0, attempts=0, hits=0, misses=0,
                          certificate_work=0, build_work=0, fallback_work=0,
                          frontier_size=0, peak_frontier=0, key_changes=0,
                          cover_entries=0, view_repairs=0, memo_hits=0, service_work=0)
        self.episodes = []
        w.initialization += 2*len(self.upper)+40

    def publish(self, j, lo, hi):
        w = self.w; w.query_reads += 4; w.heap_comparisons += 4
        if not self.lower[j] <= lo <= hi <= self.upper[j]: raise ValueError('non-nested')
        if lo != self.lower[j]: self.lower[j] = lo; self.lt.update(j, lo); w.statistic_writes += 1
        if hi != self.upper[j]:
            self.upper[j] = hi; self.ut.update(j, hi); self.revision += 1
            self.stats['key_changes'] += 1; w.statistic_writes += 2

    def candidate(self):
        # Lower-max leaf, then a uniformly random containing root action.
        # This need not be uniform over all lower-optimal actions, but always
        # selects one of them. Every backend uses this identical policy.
        lo, j = self.lt.select([1], self.rng); A = len(self.top.inside)
        for _ in range(16):
            a = self.rng.randrange(A); self.w.score_evaluations += 1
            if self.top.contains(a, j, self.w): return a, lo
        owners = []
        for a in range(A):
            if self.top.contains(a, j, self.w): owners.append(a); self.w.statistic_writes += 1
        self.w.score_evaluations += 1
        return owners[self.rng.randrange(len(owners))], lo

    def cover(self, a):
        self.w.query_reads += 1
        if a not in self.covers:
            self.covers[a] = (self.ut.cover(self.top.outside[a]), self.ut.cover(self.top.inside[a]))
            self.stats['cover_entries'] += sum(map(len, self.covers[a])); self.w.statistic_writes += 1
        return self.covers[a]

    def maxima(self, nodes):
        out = []; best = -1; w = self.w
        for p in nodes:
            v = self.ut.value[p]; w.query_reads += 1; w.heap_comparisons += 2
            if v > best: w.statistic_writes += len(out); out = []; best = v
            if v == best: out.append(p); w.statistic_writes += 1
        return out

    def ranged(self, a):
        covers = self.cover(a); nodes = tuple(self.maxima(ns) for ns in covers)
        return nodes

    def lazy(self, a):
        """Per-candidate cover tournaments persist across candidate switches.

        Stale keys are upper bounds. Refresh only possible top blocks. All
        tied blocks are re-read, so fresh uniform ties remain exact.
        """
        w = self.w; w.query_reads += 1
        if a not in self.views:
            covers = self.cover(a)
            self.views[a] = [(ns, CountTree([self.ut.value[p] for p in ns], w)) if ns else (ns, None)
                             for ns in covers]
            w.query_reads += sum(map(len, covers)); w.statistic_writes += 2
        result = []
        for ns, tree in self.views[a]:
            if tree is None: result.append([]); continue
            while True:
                old, k = tree.select([1], rank=0); val = self.ut.value[ns[k]]
                w.query_reads += 2; w.heap_comparisons += 1
                if val == old: break
                tree.update(k, val); self.stats['view_repairs'] += 1
            best = val; stack = [1]; nodes = []; w.statistic_writes += 1
            while stack:
                p = stack.pop(); w.query_reads += 2; w.heap_comparisons += 2
                if tree.value[p] < best: continue
                if p >= tree.size:
                    k = p-tree.size
                    if k >= len(ns): continue
                    val = self.ut.value[ns[k]]; w.query_reads += 2
                    if val == best: nodes.append(ns[k]); w.statistic_writes += 1
                    else: tree.update(k, val); self.stats['view_repairs'] += 1
                else:
                    stack.extend((2*p+1, 2*p)); w.statistic_writes += 2
            # Cover arrays already follow descending terminal order.
            result.append(nodes)
        return result

    def heap(self, a):
        w = self.w; best = [-1, -1]; out = [[], []]
        if self.witnesses:
            for j in self.witnesses:
                if j is None: continue
                side = int(self.top.contains(a, j, w)); best[side] = max(best[side], self.upper[j])
                w.query_reads += 1; w.heap_comparisons += 1; w.statistic_writes += 1
        stack = [(1, 0, self.ut.size)]; w.statistic_writes += 3
        while stack:
            p, lo, hi = stack.pop(); key = self.ut.value[p]
            w.query_reads += 4; w.heap_comparisons += 3
            if lo >= len(self.upper) or key < min(best): continue
            side = self.top.classify(a, lo, min(hi, len(self.upper)), w)
            if side >= 0:
                if key > best[side]:
                    w.statistic_writes += len(out[side]); out[side] = []; best[side] = key
                if key == best[side]: out[side].append(p); w.statistic_writes += 1
            else:
                mid = (lo+hi)//2; stack.extend(((2*p, lo, mid), (2*p+1, mid, hi)))
                w.statistic_writes += 6
        return out

    def build(self, theta):
        w = self.w; start = w.total; self.stats['attempts'] += 1
        H = self.ut.size.bit_length()-1; limit = 2*(self.cap+1)*(H+1)+1
        stack = [1]; found = []; visits = 0; w.statistic_writes += 1
        while stack and visits < limit:
            p = stack.pop(); visits += 1; w.query_reads += 2; w.heap_comparisons += 2
            if self.ut.value[p] < theta: continue
            if p >= self.ut.size:
                found.append(p-self.ut.size); w.statistic_writes += 1
                if len(found) > self.cap: break
            else: stack.extend((2*p, 2*p+1)); w.statistic_writes += 2
        success = not stack and len(found) <= self.cap
        w.statistic_writes += len(stack)
        if success:
            w.statistic_writes += len(self.F or [])+len(found)+4
            self.F = found; self.threshold = theta; self.stats['builds'] += 1
            self.stats['frontier_size'] = len(found)
            self.stats['peak_frontier'] = max(self.stats['peak_frontier'], len(found))
            self.episodes.append(dict(start=self.q, threshold=theta, size=len(found), hits=0, misses=0,
                                      frontier=list(found), initial_upper=[self.upper[j] for j in found]))
            w.query_reads += len(found); w.statistic_writes += 2*len(found)
        else: self.stats['aborts'] += 1; w.statistic_writes += len(found)
        self.stats['build_work'] += w.total-start
        return success

    def shortcut(self, a):
        start = self.w.total; out = [[], []]; best = [-1, -1]; w = self.w
        for j in self.F:
            side = int(self.top.contains(a, j, w)); key = self.upper[j]
            w.query_reads += 1; w.heap_comparisons += 2
            if key > best[side]:
                w.statistic_writes += len(out[side]); out[side] = []; best[side] = key
            if key == best[side]: out[side].append(self.ut.size+j); w.statistic_writes += 1
        ok = min(best) >= self.threshold
        w.heap_comparisons += 2; w.query_reads += 1
        self.stats['certificate_work'] += w.total-start
        if self.episodes: self.episodes[-1]['hits' if ok else 'misses'] += 1
        return out if ok else None

    def query(self):
        self.q += 1; a, lo = self.candidate(); w = self.w
        start = w.total; nodes = None; saved = self.memo.get(a)
        w.query_reads += 2
        memo_hit = saved is not None and saved[0] == self.revision
        if memo_hit:
            nodes = saved[1]; self.stats['memo_hits'] += 1
        if not memo_hit and self.method == 'frontier' and self.F is not None:
            nodes = self.shortcut(a)
        shortcut_hit = not memo_hit and nodes is not None
        if shortcut_hit: self.stats['hits'] += 1
        if nodes is None and self.method == 'lazy_cover': nodes = self.lazy(a)
        elif nodes is None and self.method == 'cert_heap': nodes = self.heap(a)
        elif nodes is None:
            b = w.total; nodes = self.ranged(a); self.stats['fallback_work'] += w.total-b
            if self.method == 'frontier': self.stats['misses'] += 1
        if not memo_hit:
            if saved is not None: w.statistic_writes += sum(map(len,saved[1]))
            self.memo[a] = (self.revision,nodes); w.statistic_writes += 3
        # Exactly two fresh uniform draws in canonical descending rank order.
        x = self.ut.select(nodes[1], self.rng); y = self.ut.select(nodes[0], self.rng)
        self.witnesses = (x[1], y[1]); w.statistic_writes += 2
        if self.method == 'frontier' and not memo_hit and not shortcut_hit and self.q >= self.attempt_at and y[1] is not None:
            theta = min(x[0], y[0])-self.slack
            if self.F is not None: theta = min(theta, self.threshold-self.slack)
            if 0 <= theta < self.threshold:
                self.build(theta)
            self.attempt_at = self.q + self.backoff; self.backoff *= 2
            w.statistic_writes += 2
        self.stats['service_work'] += w.total-start
        return a, lo, x, y, w.total-start


class Search:
    def __init__(self, p, c, seed, method):
        self.g = p.graph; self.w = UCTWork(); w = self.w
        w.initialization += 16*len(self.g)+10*sum(map(len, self.g.children))+4*len(self.g.leaves)
        self.idx = Index(self.g, w, c['K'], method, seed, c.get('cap', 12), c.get('slack', .025))
        self.ev = MixtureIntervals(self.g, w, c['delta'], c['K']); self.oracle = p.oracle(seed)
        self.tol = round(c['epsilon']*c['K']); self.N = 0
        if abs(self.tol-c['epsilon']*c['K']) > 1e-9 or c['K']*c['epsilon'] <= 2:
            raise ValueError('require exact grid epsilon and K epsilon > 2')

    def query(self):
        a, lo, x, y, cost = self.idx.query()
        good = y[1] is None or y[0] <= lo+self.tol
        self.pair = (x[1], y[1]); self.w.query_reads += 2; self.w.heap_comparisons += 1
        return a, good, lo, x, y

    def observe(self, j):
        leaf = self.g.leaves[j]; v = leaf; w = self.w
        while v != self.g.root:
            v = self.idx.top.parent[v]; w.edge_reads += 1; w.query_reads += 1
        reward = self.oracle.sample(leaf); self.N += 1
        interval = self.ev.observe(leaf, reward)
        if self.ev.conflict: raise ArithmeticError('empty confidence intersection')
        if interval is not None: self.idx.publish(j, *interval)
        return j, reward, interval

    def block(self, cadence):
        pair = self.pair; obs = [self.observe(pair[k % 2]) for k in range(cadence)]
        self.w.statistic_writes += len(obs)
        return obs, self.query()
