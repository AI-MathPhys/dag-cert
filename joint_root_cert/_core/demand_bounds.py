"""Exact arbitrary-node MAX queries with demand or compiled maintenance.

These backends maintain confidence endpoints, not UCT return statistics.
All consume the same monotone terminal endpoints. Existing benchmark sources
are deliberately unchanged. Work counters are a documented scalar RAM proxy.
"""
import math

from .certified_uct import IndexedMaxHeap
from .retired_bounds import RetiredBounds


class DecisionQueries:
    def _query_init(self, graph, work, scale):
        self.graph, self.work, self.scale = graph, work, scale
        self.epoch = 0
        self.query_epoch = [-1] * len(graph)
        self.query_cache = [None] * len(graph)
        self.work.initialization += 2 * len(graph) + 4

    def query(self, node=None):
        node = self.graph.root if node is None else node
        self.work.query_reads += 2
        if self.query_epoch[node] == self.epoch:
            return self.query_cache[node]
        lo, hi = self.interval(node)
        row = self.graph.children[node]
        if not row:
            answer = (-1, 0., lo / self.scale, hi / self.scale)
        else:
            # Demand pruning may leave strictly dominated children stale. The
            # clipped decision tuple is exact without refreshing those children.
            pairs = self.decision_children(node)
            a = max(range(len(row)), key=lambda i: pairs[i][0])
            rival = max((u for i, (_, u) in enumerate(pairs) if i != a), default=lo)
            answer = (a, max(0., (rival-pairs[a][0])/self.scale), lo/self.scale, hi/self.scale)
            self.work.query_reads += 3 * len(row) + 3
        self.query_cache[node], self.query_epoch[node] = answer, self.epoch
        self.work.statistic_writes += 2
        return answer


class EagerQueries(DecisionQueries):
    """Existing optimized canonical propagation, now with any-node queries."""
    def __init__(self, graph, work, scale=1, cut=False):
        self._query_init(graph, work, scale)
        self.bounds = RetiredBounds(graph, work, 'cut' if cut else 'eager', scale)

    def publish(self, leaf, lo, hi):
        changed = (lo, hi) != (self.bounds.lower[leaf], self.bounds.upper[leaf])
        self.bounds.publish(leaf, lo, hi)
        self.epoch += changed
        self.work.query_reads += 2; self.work.statistic_writes += int(changed)

    def interval(self, node):
        self.work.query_reads += 2
        return self.bounds.lower[node], self.bounds.upper[node]

    def decision_children(self, node):
        self.work.query_reads += 2 * len(self.graph.children[node])
        return [(self.bounds.lower[c], self.bounds.upper[c]) for c in self.graph.children[node]]


class DemandBounds(DecisionQueries):
    """No reverse updates. Refresh requested dependencies once per changed epoch.

    Permanent local cuts remain valid if a discarded region is queried later.
    No global 'dead' flag is used, so arbitrary future node requests are allowed.
    """
    def __init__(self, graph, work, scale=1, prune=True):
        self._query_init(graph, work, scale)
        self.lower, self.upper = [0]*len(graph), [scale]*len(graph)
        self.stamp = [0]*len(graph)
        self.active = [list(row) for row in graph.children]
        self.prune = prune
        self.visited_edges = self.refreshed = self.retired = 0
        work.initialization += 4*len(graph)+sum(map(len, graph.children))+4

    def publish(self, leaf, lo, hi):
        if self.graph.children[leaf]:
            raise ValueError('Only terminals accept observations')
        old_l, old_u = self.lower[leaf], self.upper[leaf]
        self.work.query_reads += 3
        if (lo, hi) == (old_l, old_u):
            return
        if not old_l <= lo <= hi <= old_u:
            raise ValueError('Endpoints must form nested nonempty intervals')
        self.lower[leaf], self.upper[leaf] = lo, hi
        self.epoch += 1; self.stamp[leaf] = self.epoch
        self.work.statistic_writes += 4

    def interval(self, node):
        pending = [(node, False)]
        self.work.statistic_writes += 1
        while pending:
            v, finish = pending.pop()
            self.work.query_reads += 2
            if self.stamp[v] == self.epoch:
                continue
            if not self.graph.children[v]:
                self.stamp[v] = self.epoch; self.work.statistic_writes += 1
                continue
            if not finish:
                row = self.active[v]
                keep = []
                for c in row:
                    self.visited_edges += 1; self.work.edge_reads += 1
                    self.work.query_reads += 2
                    if self.prune and self.upper[c] < self.lower[v]:
                        self.retired += 1
                    else:
                        keep.append(c); self.work.statistic_writes += 1
                self.active[v] = keep
                pending.append((v, True))
                pending.extend((c, False) for c in reversed(keep))
                self.work.statistic_writes += len(keep)+2
            else:
                row = self.active[v]
                lo = max(self.lower[c] for c in row)
                hi = max(self.upper[c] for c in row)
                keep = [c for c in row if not self.prune or self.upper[c] >= lo]
                self.retired += len(row)-len(keep)
                self.active[v] = keep
                self.lower[v], self.upper[v], self.stamp[v] = lo, hi, self.epoch
                self.refreshed += 1
                self.work.edge_reads += 2*len(row)
                self.work.query_reads += 3*len(row)
                self.work.statistic_writes += len(keep)+4
        return self.lower[node], self.upper[node]

    def decision_children(self, node):
        self.work.query_reads += 2*len(self.graph.children[node])
        return [(self.lower[c], self.upper[c]) for c in self.graph.children[node]]


def terminal_order(graph, work, reverse=False, numeric=False):
    if numeric:
        work.initialization += len(graph.leaves)
        return list(graph.leaves)
    pending, seen, leaves = [graph.root], set(), []
    while pending:
        v = pending.pop(); work.query_reads += 2
        if v in seen: continue
        seen.add(v); work.statistic_writes += 1
        if graph.children[v]:
            row = graph.children[v]
            pending.extend(row if reverse else reversed(row))
            work.edge_reads += len(row); work.statistic_writes += len(row)
        else:
            leaves.append(v); work.statistic_writes += 1
    return leaves


def compile_runs(graph, work, reverse=False, numeric=False):
    """Hash-cons exact terminal supports as sorted disjoint half-open runs.

    Merge child runs directly: no dense terminal sets or closure are built.
    Indexed heaps expose comparisons/writes to the common work accounting.
    Python hash-table operations have expected constant overhead per run key;
    hashing and possible equality traversal are conservatively charged linearly.
    """
    leaf_index = {v:i for i,v in enumerate(terminal_order(graph, work, reverse, numeric))}
    descriptors, lookup = [], {}
    ids = [-1]*len(graph)
    work.initialization += len(graph)+2*len(leaf_index)
    merge_inputs = 0
    for v in reversed(graph.order):
        row = graph.children[v]
        if not row:
            i = leaf_index[v]; merged = ((i, i+1),)
            work.initialization += 2
        else:
            children = [descriptors[ids[c]] for c in row]
            pos = [0]*len(row)
            heap = IndexedMaxHeap([-runs[0][0] for runs in children], work)
            merged = []
            work.initialization += 3*len(row)
            while heap.keys[heap.top] != -math.inf:
                a = heap.top; start, end = children[a][pos[a]]
                merge_inputs += 1
                work.query_reads += 5
                if merged and start <= merged[-1][1]:
                    merged[-1] = (merged[-1][0], max(merged[-1][1], end))
                else:
                    merged.append((start, end))
                pos[a] += 1
                work.statistic_writes += 3
                heap.update(a, -children[a][pos[a]][0] if pos[a] < len(children[a]) else -math.inf)
            merged = tuple(merged)
            work.initialization += len(merged)
        work.query_reads += 4*len(merged)+1
        index = lookup.get(merged)
        if index is None:
            index = len(descriptors); descriptors.append(merged); lookup[merged] = index
            work.initialization += 2*len(merged)+2
        ids[v] = index; work.statistic_writes += 1
    return leaf_index, ids, descriptors, merge_inputs


class MaxIndex:
    """Shared balanced terminal index, with changed-value early stopping."""
    def __init__(self, leaves, scale, work):
        self.base = 1 << (max(1, leaves)-1).bit_length()
        self.leaves, self.work = leaves, work
        self.lower, self.upper = [-math.inf]*(2*self.base), [-math.inf]*(2*self.base)
        for i in range(leaves):
            self.lower[self.base+i], self.upper[self.base+i] = 0, scale
        work.initialization += 4*self.base+2*leaves+3
        self.rebuild()

    def rebuild(self):
        for p in range(self.base-1, 0, -1):
            self.lower[p] = max(self.lower[2*p], self.lower[2*p+1])
            self.upper[p] = max(self.upper[2*p], self.upper[2*p+1])
            self.work.query_reads += 4; self.work.statistic_writes += 2

    def update(self, leaf, lo, hi):
        p = self.base+leaf
        self.lower[p], self.upper[p] = lo, hi
        self.work.statistic_writes += 2
        while p > 1:
            p //= 2
            a = max(self.lower[2*p], self.lower[2*p+1])
            b = max(self.upper[2*p], self.upper[2*p+1])
            self.work.query_reads += 6
            if (a, b) == (self.lower[p], self.upper[p]):
                break
            self.lower[p], self.upper[p] = a, b
            self.work.statistic_writes += 2

    def cover(self, start, end):
        result = []; start += self.base; end += self.base
        while start < end:
            self.work.query_reads += 2
            if start & 1: result.append(start); start += 1
            if end & 1: end -= 1; result.append(end)
            start //= 2; end //= 2
            self.work.statistic_writes += 4
        self.work.initialization += len(result)
        return result


class LazyMaxIndex(MaxIndex):
    """Demand evaluation of the compiled balanced circuit; no update bubbling."""
    def __init__(self, leaves, scale, work):
        super().__init__(leaves, scale, work)
        self.stamp = [0]*(2*self.base)
        self.active = [3]*(2*self.base)
        self.refreshed = self.visited_edges = self.retired = 0
        self.reconciled = 0
        work.initialization += 4*self.base+3

    def assign(self, leaf, lo, hi, epoch):
        p = self.base+leaf
        self.lower[p], self.upper[p], self.stamp[p] = lo, hi, epoch
        self.work.statistic_writes += 3

    def refresh(self, node, epoch, guard=None):
        pending = [(node, False)]
        self.work.statistic_writes += 1
        while pending:
            p, finish = pending.pop(); self.work.query_reads += 2
            if self.stamp[p] == epoch or self.reconciled == epoch: continue
            if guard is not None: guard()
            if p >= self.base:
                self.stamp[p] = epoch; self.work.statistic_writes += 1
                continue
            children = [2*p+i for i in (0,1) if self.active[p] & (1<<i)]
            self.work.query_reads += 2
            if not finish:
                pending.append((p, True)); self.work.statistic_writes += 1
                for c in children:
                    self.visited_edges += 1; self.work.query_reads += 2
                    if self.upper[c] < self.lower[p]:
                        self.active[p] &= ~(1 << (c & 1)); self.retired += 1
                        self.work.statistic_writes += 1
                    else:
                        pending.append((c, False)); self.work.statistic_writes += 1
            else:
                self.lower[p] = max(self.lower[c] for c in children)
                self.upper[p] = max(self.upper[c] for c in children)
                for c in children:
                    if self.upper[c] < self.lower[p]:
                        self.active[p] &= ~(1 << (c & 1)); self.retired += 1
                        self.work.statistic_writes += 1
                self.stamp[p] = epoch; self.refreshed += 1
                self.work.query_reads += 3*len(children)
                self.work.statistic_writes += 3


class RangeBounds(DecisionQueries):
    """Compressed compilation plus eager or batched shared-index maintenance.

    Batch mode coalesces repeated terminal updates and selects between point
    repairs and a full bottom-up index rebuild using a public size threshold.
    All queryable nodes are compiled; equivalent supports share one value cache.
    """
    def __init__(self, graph, work, scale=1, batch=False, lazy=False, reverse=False, numeric=False):
        self._query_init(graph, work, scale)
        self.mapping, self.ids, runs, self.merge_inputs = compile_runs(graph, work, reverse, numeric)
        self.index = (LazyMaxIndex if lazy else MaxIndex)(len(graph.leaves), scale, work)
        self.covers = [tuple(p for a,b in support for p in self.index.cover(a,b)) for support in runs]
        self.run_count = sum(map(len, runs)); self.supports = len(runs)
        self.cover_entries = sum(map(len, self.covers))
        self.cache, self.stamp = [(0,scale)]*len(runs), [0]*len(runs)
        self.lower, self.upper = [0]*len(graph), [scale]*len(graph)
        self.pending, self.batch, self.lazy = {}, batch, lazy
        self.flushes = self.rebuilds = self.coalesced_updates = 0
        work.initialization += 2*len(runs)+2*len(graph)+len(self.covers)+7

    def publish(self, leaf, lo, hi):
        if self.graph.children[leaf]: raise ValueError('Only terminals accept evidence')
        self.work.query_reads += 3
        if (lo,hi) == (self.lower[leaf], self.upper[leaf]): return
        if not self.lower[leaf] <= lo <= hi <= self.upper[leaf]: raise ValueError('Non-nested interval')
        self.lower[leaf], self.upper[leaf] = lo, hi
        self.epoch += 1; self.work.statistic_writes += 3
        i = self.mapping[leaf]; self.work.query_reads += 1
        if self.lazy:
            self.index.assign(i, lo, hi, self.epoch)
        elif self.batch:
            self.pending[i] = (lo, hi); self.work.statistic_writes += 1
        else:
            self.index.update(i, lo, hi)

    def _flush(self):
        self.work.query_reads += 1
        if not self.pending: return
        self.flushes += 1; self.coalesced_updates += len(self.pending)
        if len(self.pending)*max(1, self.index.base.bit_length()-1) >= self.index.base:
            for i, (lo,hi) in self.pending.items():
                self.index.lower[self.index.base+i], self.index.upper[self.index.base+i] = lo, hi
                self.work.query_reads += 3; self.work.statistic_writes += 2
            self.index.rebuild(); self.rebuilds += 1
        else:
            for i, (lo,hi) in self.pending.items():
                self.work.query_reads += 3; self.index.update(i,lo,hi)
        self.work.statistic_writes += len(self.pending)+1
        self.pending.clear()

    def interval(self, node):
        if self.batch: self._flush()
        i = self.ids[node]; self.work.query_reads += 2
        if self.stamp[i] != self.epoch:
            cover = self.covers[i]
            if self.lazy:
                for p in cover: self.index.refresh(p, self.epoch)
            self.cache[i] = (max(self.index.lower[p] for p in cover), max(self.index.upper[p] for p in cover))
            self.stamp[i] = self.epoch
            self.work.query_reads += 2*len(cover)
            self.work.statistic_writes += 3
        return self.cache[i]

    def decision_children(self, node):
        return [self.interval(c) for c in self.graph.children[node]]


class _FlatGraph:
    def __init__(self, children): self.children, self.root = children, 0
    def __len__(self): return len(self.children)


class FlatQueries(DecisionQueries):
    """Explicit terminal incidence with identical-support sharing as a control."""
    def __init__(self, graph, work, scale=1):
        self._query_init(graph, work, scale)
        self.mapping, self.ids, supports, self.merge_inputs = compile_runs(graph, work)
        self.offset = len(supports)
        rows = [tuple(self.offset+i for a,b in runs for i in range(a,b)) for runs in supports]
        rows += [() for _ in graph.leaves]
        self.compiled_edges = sum(map(len,rows)); self.supports = len(supports)
        work.initialization += len(rows)+self.compiled_edges
        self.bounds = RetiredBounds(_FlatGraph(rows), work, 'eager', scale)

    def publish(self, leaf, lo, hi):
        i = self.offset+self.mapping[leaf]
        changed = (lo,hi) != (self.bounds.lower[i],self.bounds.upper[i])
        self.bounds.publish(i,lo,hi); self.epoch += changed
        self.work.query_reads += 3; self.work.statistic_writes += int(changed)

    def interval(self, node):
        i = self.ids[node]; self.work.query_reads += 3
        return self.bounds.lower[i], self.bounds.upper[i]

    def decision_children(self, node):
        return [self.interval(c) for c in self.graph.children[node]]


class MultiRangeBounds(DecisionQueries):
    """Two shared indexes, deterministic opposing DFS orders, shorter cover per node.

    Both compilations and both update streams are charged. This avoids treating
    the failure of one terminal ordering as a lower bound for compression.
    """
    def __init__(self, graph, work, scale=1):
        self._query_init(graph, work, scale)
        self.backends = [RangeBounds(graph, work, scale, batch=True, reverse=reverse) for reverse in (False,True)]
        self.choice = [min(range(2), key=lambda j:len(self.backends[j].covers[self.backends[j].ids[v]])) for v in range(len(graph))]
        work.initialization += 5*len(graph)+2

    def publish(self, leaf, lo, hi):
        for backend in self.backends: backend.publish(leaf,lo,hi)
        self.epoch = self.backends[0].epoch; self.work.statistic_writes += 1

    def interval(self, node):
        self.work.query_reads += 1
        return self.backends[self.choice[node]].interval(node)

    def decision_children(self, node):
        return [self.interval(c) for c in self.graph.children[node]]


class _RepairLimit(Exception):
    pass


class AdaptiveRangeBounds(RangeBounds):
    """Cap demand work in an epoch, then repair the index on excess.

    The cap uses only index size and the number of pending distinct terminals.
    It counts actual instrumented refresh work, including freshness checks.
    A partial refresh leaves sound cached bounds and can safely be abandoned.
    This adapts refresh strategy for one fixed compiled representation; it does
    not choose an optimal representation or improve UCT sample allocation.
    """
    def __init__(self, graph, work, scale=1):
        super().__init__(graph, work, scale, lazy=True)
        self.budget_epoch = -1
        self.refresh_spent = 0
        self.refresh_cap = 0
        self.fallbacks = 0
        self.recent = set()
        work.initialization += 4

    def publish(self, leaf, lo, hi):
        before = self.epoch
        super().publish(leaf,lo,hi)
        if self.epoch != before:
            self.pending[self.mapping[leaf]] = (lo,hi)
            self.recent.add(self.mapping[leaf])
            self.work.query_reads += 2; self.work.statistic_writes += 2

    def _repair(self):
        # The size threshold matches Range-batch, but point paths must run to
        # the root: a partly refreshed parent can be correct while its ancestor
        # is stale, so an unchanged-parent early exit would be unsound here.
        index = self.index
        height = max(1,index.base.bit_length()-1)
        self.flushes += 1; self.coalesced_updates += len(self.pending)
        if len(self.pending)*height >= index.base:
            index.rebuild(); self.rebuilds += 1
        else:
            for leaf in self.pending:
                p = index.base+leaf
                self.work.query_reads += 1
                while p > 1:
                    p //= 2
                    index.lower[p] = max(index.lower[2*p],index.lower[2*p+1])
                    index.upper[p] = max(index.upper[2*p],index.upper[2*p+1])
                    self.work.query_reads += 4; self.work.statistic_writes += 2
        self.work.statistic_writes += len(self.pending)+1
        self.pending.clear()
        self.index.reconciled = self.epoch
        self.fallbacks += 1; self.work.statistic_writes += 2

    def interval(self, node):
        if self.budget_epoch != self.epoch:
            height = max(1,self.index.base.bit_length()-1)
            # Charge this phase only for changes since the preceding query
            # phase. Older deferred repair debt is amortized at its one flush.
            self.refresh_cap = 8*min(self.index.base,len(self.recent)*height)
            self.work.statistic_writes += len(self.recent)
            self.recent.clear()
            self.refresh_spent = 0; self.budget_epoch = self.epoch
            self.work.query_reads += 3; self.work.statistic_writes += 3
        i = self.ids[node]; self.work.query_reads += 2
        if self.stamp[i] != self.epoch:
            cover = self.covers[i]
            for p in cover:
                before = self.work.total
                def guard():
                    self.work.query_reads += 2
                    if self.refresh_spent+self.work.total-before > self.refresh_cap:
                        raise _RepairLimit
                try:
                    self.index.refresh(p,self.epoch,guard)
                except _RepairLimit:
                    self.refresh_spent += self.work.total-before
                    self._repair()
                    break
                self.refresh_spent += self.work.total-before
            self.cache[i] = (max(self.index.lower[p] for p in cover),max(self.index.upper[p] for p in cover))
            self.stamp[i] = self.epoch
            self.work.query_reads += 2*len(cover); self.work.statistic_writes += 3
        return self.cache[i]


METHODS = ('eager', 'cut', 'demand', 'flat', 'range_eager', 'range_batch', 'range_demand', 'range_batch2', 'range_adaptive')


def make_backend(graph, work, method, scale=1):
    if method == 'eager': return EagerQueries(graph, work, scale)
    if method == 'cut': return EagerQueries(graph, work, scale, True)
    if method in ('demand', 'demand_uncut'): return DemandBounds(graph, work, scale, method=='demand')
    if method == 'flat': return FlatQueries(graph, work, scale)
    if method == 'range_batch2': return MultiRangeBounds(graph, work, scale)
    if method == 'range_adaptive': return AdaptiveRangeBounds(graph, work, scale)
    if method == 'range_numeric': return RangeBounds(graph, work, scale, batch=True, numeric=True)
    if method in ('range_eager', 'range_batch', 'range_demand'):
        return RangeBounds(graph, work, scale, method=='range_batch', method=='range_demand')
    raise ValueError(method)
