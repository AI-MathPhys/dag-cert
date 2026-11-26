"""Root-exact MAX confidence maintenance by permanent reverse-edge retirement.

All modes share canonical terminal evidence. `eager` keeps every incidence;
`cut` unlinks locally dominated incidences; `live` also releases outgoing
subscriptions of states no longer reachable from the root. No ancestor closure
is built. This backend does not allocate samples or alter UCT return statistics.
"""
from collections import deque
import math

from .certified_uct import IndexedMaxHeap


class RetiredBounds:
    def __init__(self, graph, work, mode="live", scale=1):
        if mode not in ("eager", "cut", "live") or scale <= 0:
            raise ValueError("Invalid maintenance mode or interval scale")
        self.graph, self.work, self.mode, self.scale = graph, work, mode, scale
        size = len(graph)
        self.lower, self.upper = [0]*size, [scale]*size
        self.leader = [0 if row else -1 for row in graph.children]
        self.live, self.queued = [True]*size, [False]*size
        self.head, self.indegree = [-1]*size, [0]*size
        self.parent, self.child, self.action = [], [], []
        self.prev, self.next, self.active = [], [], []
        self.outgoing = [[] for _ in graph.children]
        self.high = [IndexedMaxHeap([scale]*len(row), work) if row else None
                     for row in graph.children]
        self.minimum = ([IndexedMaxHeap([-scale]*len(row), work) if row else None
                         for row in graph.children] if mode != "eager" else None)
        self.messages = self.retired = self.dead_nodes = self.publications = 0
        self.endpoint_changes = [0]*size
        self.skipped_dead = self.incoming_copies = 0
        work.initialization += 12*size+8
        for p, row in enumerate(graph.children):
            for a, c in enumerate(row):
                e = len(self.parent)
                self.parent.append(p); self.child.append(c); self.action.append(a)
                self.prev.append(-1); self.next.append(self.head[c]); self.active.append(True)
                if self.head[c] != -1:
                    self.prev[self.head[c]] = e
                self.head[c] = e; self.indegree[c] += 1
                self.outgoing[p].append(e)
                work.initialization += 12

    def _unlink(self, edge):
        """Intrusive reverse list: constant RAM work, including shared children."""
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
        self.work.edge_reads += 3
        self.work.statistic_writes += 5

    def _release(self, child):
        """Release each unreachable node once; preserve multiply referenced nodes."""
        if self.mode != "live" or self.indegree[child] or child == self.graph.root:
            return
        pending = [child]
        self.work.statistic_writes += 1
        while pending:
            node = pending.pop()
            self.work.query_reads += 2
            if not self.live[node]:
                continue
            self.live[node] = False; self.dead_nodes += 1
            self.work.statistic_writes += 2
            for edge in self.outgoing[node]:
                self.work.edge_reads += 1
                if not self.active[edge]:
                    continue
                c = self.child[edge]
                self._unlink(edge)
                if not self.indegree[c]:
                    pending.append(c)
                    self.work.statistic_writes += 1

    def _cut(self, node, limit):
        heap = self.minimum[node]
        while True:
            self.work.query_reads += 2
            a = heap.top
            # Strict inequality preserves maximizers and fixed action-ID ties.
            if -heap.keys[a] >= limit:
                return
            edge = self.outgoing[node][a]
            assert self.active[edge]
            child = self.child[edge]
            self._unlink(edge)
            self.high[node].update(a, -math.inf)
            heap.update(a, -math.inf)
            self._release(child)

    def _record(self, node, lower, upper):
        old_l, old_u = self.lower[node], self.upper[node]
        self.work.query_reads += 2
        if lower == old_l and upper == old_u:
            return False
        assert old_l <= lower <= upper <= old_u
        self.lower[node], self.upper[node] = lower, upper
        self.publications += 1
        self.endpoint_changes[node] += int(lower != old_l)+int(upper != old_u)
        self.work.statistic_writes += 4
        return True

    def publish(self, leaf, lower, upper):
        if self.graph.children[leaf]:
            raise ValueError("Only canonical terminals accept evidence")
        changed = self._record(leaf, lower, upper)
        if not changed:
            return
        if not self.live[leaf]:
            self.skipped_dead += 1
            self.work.statistic_writes += 1
            return
        pending = deque([leaf]); self.queued[leaf] = True
        self.work.statistic_writes += 2
        while pending:
            node = pending.popleft(); self.queued[node] = False
            self.work.statistic_writes += 2
            if not self.live[node]:
                continue
            # Snapshot handles recursive unsubscription during this delivery.
            edges = []; edge = self.head[node]
            self.work.query_reads += 1
            while edge != -1:
                edges.append(edge); edge = self.next[edge]
                self.incoming_copies += 1
                self.work.edge_reads += 1; self.work.statistic_writes += 1
            for edge in edges:
                self.work.edge_reads += 1
                if not self.active[edge]:
                    continue
                p, a = self.parent[edge], self.action[edge]
                self.messages += 1
                self.work.edge_reads += 2
                lo = self.lower[p]
                if self.lower[node] > lo or (self.lower[node] == lo and a < self.leader[p]):
                    lo = self.lower[node]; self.leader[p] = a
                    self.work.statistic_writes += 1
                heap = self.high[p]
                self.work.query_reads += 5
                if heap.keys[a] != self.upper[node]:
                    heap.update(a, self.upper[node])
                    if self.minimum is not None:
                        self.minimum[p].update(a, -self.upper[node])
                if self.minimum is not None:
                    self._cut(p, lo)
                hi = heap.keys[heap.top]
                self.work.query_reads += 2
                if self._record(p, lo, hi) and not self.queued[p]:
                    pending.append(p); self.queued[p] = True
                    self.work.statistic_writes += 2

    def query(self):
        """Exact full-DP root leader, clipped rival gap, and root endpoints.

        Retired root actions may have stale bounds. Those bounds are strictly
        below a surviving lower bound forever and cannot change this query.
        Arbitrary inactive-node interval queries are deliberately unsupported.
        """
        root = self.graph.root; row = self.graph.children[root]
        self.work.query_reads += 2
        if not row:
            return (-1, 0., self.lower[root]/self.scale, self.upper[root]/self.scale)
        a = max(range(len(row)), key=lambda i: self.lower[row[i]])
        gap = max((self.upper[c]-self.lower[row[a]] for i,c in enumerate(row) if i != a), default=0)
        self.work.query_reads += 2*len(row)+3
        return (a, max(0., gap/self.scale), self.lower[root]/self.scale, self.upper[root]/self.scale)


class CanonicalIntervals:
    """Identical real observations, confidence schedule and grid for every backend."""
    def __init__(self, graph, work, delta=.05, scale=1, geometric=False):
        if not 0 < delta < .5 or scale < 1:
            raise ValueError("Invalid evidence parameters")
        self.graph, self.work, self.scale, self.geometric = graph, work, scale, geometric
        self.counts, self.sums = [0]*len(graph), [0.]*len(graph)
        self.lower, self.upper = [0.]*len(graph), [1.]*len(graph)
        self.next_count = [1]*len(graph)
        self.log_constant = math.log(math.pi**2*len(graph.leaves)/(3*delta))
        self.evaluations = 0; self.conflict = False
        work.initialization += 5*len(graph)+3

    def observe(self, leaf, reward):
        if self.graph.children[leaf] or not math.isfinite(reward) or not 0 <= reward <= 1:
            raise ValueError("A real bounded observation of a terminal is required")
        self.counts[leaf] += 1; self.sums[leaf] += reward
        self.work.oracle_calls += 1; self.work.statistic_writes += 2
        n = self.counts[leaf]
        self.work.confidence_work += 1
        if n < self.next_count[leaf]:
            return None
        self.next_count[leaf] = n+(n+3)//4 if self.geometric else n+1
        self.evaluations += 1
        self.work.statistic_writes += 4; self.work.confidence_work += 8
        radius = math.sqrt((self.log_constant+2*math.log(n))/(2*n))
        lo = max(self.lower[leaf], self.sums[leaf]/n-radius, 0.)
        hi = min(self.upper[leaf], self.sums[leaf]/n+radius, 1.)
        self.lower[leaf], self.upper[leaf] = lo, hi
        if lo > hi:
            self.conflict = True
            return None
        if self.scale != 1:
            lo = max(0, math.floor(math.nextafter(self.scale*lo, -math.inf)))
            hi = min(self.scale, math.ceil(math.nextafter(self.scale*hi, math.inf)))
            self.work.confidence_work += 4
        return lo, hi
