"""Finite-resolution, arbitrary-node MAX confidence maintenance.

All publications are nested integer intervals in [0, scale]. Queries flush a
coalesced reverse worklist, without computing ancestor closures. The heap mode
is a batching/early-exit sharing control with identical message scheduling.
Neither mode changes sampling or UCT return statistics.
"""
from collections import deque
import math

from .certified_uct import IndexedMaxHeap


class LocalBuckets:
    def __init__(self, graph, work, scale=40, mode="bucket", priority=None):
        if not isinstance(scale, int) or scale < 1 or mode not in ("bucket", "heap"):
            raise ValueError("Need a positive integer scale and bucket/heap mode")
        self.graph, self.work, self.scale, self.mode = graph, work, scale, mode
        n = len(graph)
        self.lower, self.upper = [0]*n, [scale]*n
        self.sent_lower, self.sent_upper = [0]*n, [scale]*n
        self.leader = [0 if row else -1 for row in graph.children]
        self.incoming = [[] for _ in range(n)]
        self.pending = [{} for _ in range(n)]
        self.queued, self.queue = [False]*n, deque()
        self.child_upper = [[scale]*len(row) for row in graph.children]
        self.counts, self.heaps, self.ranks = [None]*n, [None]*n, [None]*n
        self.top, self.second = [scale]*n, [scale]*n
        self.endpoint_changes, self.messages, self.cursor_steps = [0]*n, 0, 0
        work.initialization += 15*n
        for v, row in enumerate(graph.children):
            for a, c in enumerate(row):
                self.incoming[c].append((v, a))
                work.initialization += 4
            if not row:
                continue
            if mode == "bucket":
                counts = [0]*(scale+1); counts[scale] = len(row)
                self.counts[v] = counts
                work.initialization += scale+2
            else:
                ranks = [priority[c] if priority is not None else a for a,c in enumerate(row)]
                self.ranks[v] = ranks
                self.heaps[v] = IndexedMaxHeap([(scale, -r) for r in ranks], work)
                work.initialization += 2*len(row)

    def _enqueue(self, node):
        self.work.query_reads += 1
        if not self.queued[node]:
            self.queued[node] = True; self.queue.append(node)
            self.work.statistic_writes += 2

    def publish(self, leaf, lo, hi):
        self.work.query_reads += 4
        if (self.graph.children[leaf] or not isinstance(lo, int) or not isinstance(hi, int)
                or not self.lower[leaf] <= lo <= hi <= self.upper[leaf]):
            raise ValueError("Publication must be a nested integer terminal interval")
        if (lo, hi) != (self.lower[leaf], self.upper[leaf]):
            self.lower[leaf], self.upper[leaf] = lo, hi
            self.work.statistic_writes += 2
            self._enqueue(leaf)

    def _repair_upper(self, v):
        pending = self.pending[v]
        if not pending:
            return
        if self.mode == "bucket":
            counts, old = self.counts[v], self.child_upper[v]
            for a, hi in pending.items():
                counts[old[a]] -= 1; counts[hi] += 1; old[a] = hi
                self.work.statistic_writes += 3; self.work.query_reads += 2
            top = self.top[v]
            self.work.query_reads += 1
            while not counts[top]:
                top -= 1; self.cursor_steps += 1
                self.work.query_reads += 1; self.work.statistic_writes += 1
            self.top[v] = top
            if len(self.graph.children[v]) > 1:
                if counts[top] > 1:
                    second = top
                else:
                    second = min(self.second[v], top-1)
                    self.work.query_reads += 1
                    while not counts[second]:
                        second -= 1; self.cursor_steps += 1
                        self.work.query_reads += 1; self.work.statistic_writes += 1
                self.second[v] = second
            self.upper[v] = top
            self.work.statistic_writes += 3
        else:
            heap, ranks = self.heaps[v], self.ranks[v]
            # Pay the cheaper estimated point-update or full-rebuild repair.
            if len(pending)*max(1, math.ceil(math.log2(len(heap.ids)+1))) >= len(heap.ids):
                for a, hi in pending.items():
                    heap.keys[a] = (hi, -ranks[a]); self.child_upper[v][a] = hi
                    self.work.heap_writes += 2
                heap.rebuild(); self.work.rebuild_entries += len(heap.ids)
            else:
                for a, hi in pending.items():
                    heap.update(a, (hi, -ranks[a])); self.child_upper[v][a] = hi
                    self.work.heap_writes += 1
            self.upper[v] = heap.keys[heap.top][0]
            self.work.query_reads += 2; self.work.statistic_writes += 1
        self.work.statistic_writes += len(pending)
        pending.clear()

    def flush(self):
        while self.queue:
            v = self.queue.popleft(); self.queued[v] = False
            self.work.statistic_writes += 2
            if self.graph.children[v]:
                self._repair_upper(v)
            lo, hi = self.lower[v], self.upper[v]
            dl, du = lo != self.sent_lower[v], hi != self.sent_upper[v]
            self.work.query_reads += 4
            if not (dl or du):
                continue
            self.sent_lower[v], self.sent_upper[v] = lo, hi
            self.endpoint_changes[v] += int(dl)+int(du)
            self.work.statistic_writes += 3
            for p, a in self.incoming[v]:
                self.messages += 1; self.work.edge_reads += 1
                old = self.lower[p]
                self.work.query_reads += 3
                if dl and (lo > old or (lo == old and a < self.leader[p])):
                    self.lower[p], self.leader[p] = lo, a
                    self.work.statistic_writes += 2
                if du:
                    self.pending[p][a] = hi
                    self.work.statistic_writes += 1
                if du or self.lower[p] != old:
                    self._enqueue(p)

    def query(self, node=None):
        self.flush()
        v = self.graph.root if node is None else node
        row, a = self.graph.children[v], self.leader[v]
        self.work.query_reads += 7
        if len(row) < 2:
            gap = 0
        else:
            if self.mode == "bucket":
                rival = self.second[v] if self.child_upper[v][a] == self.top[v] else self.top[v]
            else:
                heap = self.heaps[v]
                rival = heap.keys[heap.second() if heap.top == a else heap.top][0]
            gap = max(0, rival-self.lower[v])
        return (a, gap/self.scale, self.lower[v]/self.scale, self.upper[v]/self.scale)


class LazyLocalHeap:
    """Demand-driven stale-upper witnesses, shared evidence and numeric heaps.

Lower endpoints use monotone reverse messages. Upper publications cost O(1).
An unchanged maximum witness certifies the entire cached maximum. Large failed
witness batches trigger a paid scan/rebuild. Upper ties use a configurable
structural priority, while recommended actions always use original action IDs.
"""
    def __init__(self, graph, work, scale=40, priority=None):
        self.graph, self.work, self.scale = graph, work, scale
        n = len(graph)
        self.lower, self.upper = [0]*n, [scale]*n
        self.leader = [0 if r else -1 for r in graph.children]
        self.incoming = [[] for _ in range(n)]
        self.heaps, self.ranks = [None]*n, [None]*n
        self.stamp, self.epoch = [-1]*n, 0
        self.pending = {}
        self.rebuilds = 0
        work.initialization += 9*n
        for v, row in enumerate(graph.children):
            for a,c in enumerate(row):
                self.incoming[c].append((v,a)); work.initialization += 3
            if row:
                ranks = [priority[c] if priority is not None else a for a,c in enumerate(row)]
                self.ranks[v] = ranks
                self.heaps[v] = IndexedMaxHeap([(scale,-r) for r in ranks],work)
                work.initialization += 2*len(row)

    def publish(self, leaf, lo, hi):
        self.work.query_reads += 4
        if (self.graph.children[leaf] or not self.lower[leaf] <= lo <= hi <= self.upper[leaf]):
            raise ValueError("Need nested terminal intervals")
        if (lo,hi) != (self.lower[leaf],self.upper[leaf]):
            if lo != self.lower[leaf]:
                self.pending[leaf] = lo
            self.lower[leaf],self.upper[leaf] = lo,hi
            self.epoch += 1; self.work.statistic_writes += 4

    def _lower_flush(self):
        queue = deque(self.pending); queued = set(queue)
        self.work.statistic_writes += 2*len(queue)
        self.pending.clear()
        while queue:
            c = queue.popleft(); queued.remove(c)
            self.work.statistic_writes += 2
            for p,a in self.incoming[c]:
                self.work.edge_reads += 1; self.work.query_reads += 3
                old, new = self.lower[p], self.lower[c]
                if new > old or (new == old and a < self.leader[p]):
                    self.lower[p],self.leader[p] = new,a
                    self.work.statistic_writes += 2
                    if new > old and p not in queued:
                        queued.add(p); queue.append(p); self.work.statistic_writes += 2

    def _upper(self, v):
        self.work.query_reads += 3
        row = self.graph.children[v]
        if not row or self.stamp[v] == self.epoch:
            return self.upper[v]
        heap, ranks = self.heaps[v], self.ranks[v]
        repairs = 0
        while True:
            a = heap.top; hi = self._upper(row[a])
            self.work.query_reads += 3
            if hi == heap.keys[a][0]:
                break
            heap.update(a,(hi,-ranks[a])); repairs += 1
            if repairs*max(1,math.ceil(math.log2(len(row)+1))) >= len(row):
                for b,c in enumerate(row):
                    heap.keys[b] = (self._upper(c),-ranks[b]); self.work.heap_writes += 1
                heap.rebuild(); self.rebuilds += 1
                break
        self.upper[v] = heap.keys[heap.top][0]; self.stamp[v] = self.epoch
        self.work.statistic_writes += 2
        return self.upper[v]

    def query(self, node=None):
        self._lower_flush()
        v = self.graph.root if node is None else node
        row, a = self.graph.children[v], self.leader[v]
        if not row:
            self.work.query_reads += 4
            return -1,0.,self.lower[v]/self.scale,self.upper[v]/self.scale
        # A local decision necessarily demands the action bounds it reports.
        highs = [self._upper(c) for c in row]
        rival = max((u for b,u in enumerate(highs) if b != a),default=self.lower[v])
        self.work.query_reads += 3*len(row)+4
        return a,max(0,rival-self.lower[v])/self.scale,self.lower[v]/self.scale,max(highs)/self.scale
