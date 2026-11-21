"""Shared-ancestor confidence backpropagation around ordinary edge-statistic UCT.

One observation updates one canonical terminal stream. Only numerical confidence
endpoints are sent to other parents; rollout means/counts remain path-local.
Outward integer-grid bounds and monotone intersections bound lifetime messages.
"""

from collections import deque
import math

from .certified_uct import IndexedMaxHeap, TranspositionUCT


class SharedBounds:
    def __init__(self, graph, work, epsilon=.05, delta=.05, mode="event", quantized=True):
        if not 0 < epsilon < 1 or not 0 < delta < .5:
            raise ValueError("Need epsilon in (0,1) and delta in (0,.5)")
        if mode not in ("event", "full", "path"):
            raise ValueError("Unknown propagation mode")
        self.graph, self.work = graph, work
        self.epsilon, self.delta, self.mode = epsilon, delta, mode
        self.quantized = quantized
        self.scale = math.ceil(4 / epsilon) if quantized else 1
        self.lower = [0] * len(graph)
        self.upper = [self.scale] * len(graph)
        self.raw_lower, self.raw_upper = [0.] * len(graph), [1.] * len(graph)
        self.versions = [0] * len(graph)
        self.generation = [0] * len(graph)
        self.action, self.conflict = None, False
        self.gap_bound = 1.
        self.parent_messages = self.node_publications = self.leaf_changes = 0
        self.max_queue = self.dp_passes = 0
        self.per_node_publications = [0] * len(graph)
        self.log_constant = math.log(math.pi ** 2 * len(graph.leaves) / (3 * delta))
        self.incoming = None
        self.low_heaps = self.high_heaps = None
        self.queued = None
        work.initialization += 8 * len(graph) + 12
        if mode == "event":
            self.incoming = [[] for _ in graph.children]
            for parent, children in enumerate(graph.children):
                for action, child in enumerate(children):
                    self.incoming[child].append((parent, action))
                    work.initialization += 2
            self.low_heaps = [IndexedMaxHeap([0]*len(row), work) if row else None
                              for row in graph.children]
            self.high_heaps = [IndexedMaxHeap([self.scale]*len(row), work) if row else None
                               for row in graph.children]
            self.queued = [False] * len(graph)
            work.initialization += 4 * len(graph)
        degree = len(graph.children[graph.root])
        if degree <= 1:
            self.action, self.gap_bound = (0 if degree else -1), 0.

    def _publish(self, node, lower, upper):
        if lower == self.lower[node] and upper == self.upper[node]:
            return False
        assert lower >= self.lower[node] and upper <= self.upper[node]
        self.lower[node], self.upper[node] = lower, upper
        self.node_publications += 1
        self.generation[node] = self.node_publications
        self.per_node_publications[node] += 1
        self.work.statistic_writes += 3
        return True

    def _scan_node(self, node):
        children = self.graph.children[node]
        if not children:
            return
        lower = max(self.lower[c] for c in children)
        upper = max(self.upper[c] for c in children)
        stamp = max(self.generation[c] for c in children)
        self.work.confidence_work += 3 * len(children) + 2
        # Scanned variants deliberately do not build reverse incidence lists.
        if stamp != self.versions[node]:
            self.versions[node] = stamp
            self.work.statistic_writes += 1
        self._publish(node, lower, upper)

    def _propagate(self, leaf):
        queue = deque([leaf])
        self.queued[leaf] = True
        self.work.statistic_writes += 2
        while queue:
            self.max_queue = max(self.max_queue, len(queue))
            child = queue.popleft()
            self.queued[child] = False
            self.work.statistic_writes += 2
            for parent, action in self.incoming[child]:
                self.parent_messages += 1
                self.work.edge_reads += 1
                lo, hi = self.low_heaps[parent], self.high_heaps[parent]
                self.work.confidence_work += 2
                if lo.keys[action] != self.lower[child]:
                    lo.update(action, self.lower[child])
                if hi.keys[action] != self.upper[child]:
                    hi.update(action, self.upper[child])
                self.versions[parent] = max(self.versions[parent],self.generation[child])
                self.work.statistic_writes += 1
                self.work.query_reads += 2
                if self._publish(parent, lo.keys[lo.top], hi.keys[hi.top]):
                    if not self.queued[parent]:
                        queue.append(parent)
                        self.queued[parent] = True
                        self.work.statistic_writes += 2

    def _certify(self):
        root = self.graph.root
        children = self.graph.children[root]
        if len(children) <= 1:
            return
        if self.mode == "event":
            lo, hi = self.low_heaps[root], self.high_heaps[root]
            action = lo.top
            rival = hi.top if hi.top != action else hi.second()
            gap = hi.keys[rival] - lo.keys[action]
            self.work.query_reads += 4
        else:
            action = max(range(len(children)), key=lambda a:self.lower[children[a]])
            gap = max(self.upper[c] for a,c in enumerate(children) if a != action) - self.lower[children[action]]
            self.work.confidence_work += 2 * len(children)
        self.gap_bound = max(0., gap / self.scale)
        if self.gap_bound <= self.epsilon:
            self.action = action

    def observe(self, leaf, count, total, path):
        radius = math.sqrt((self.log_constant + 2 * math.log(count)) / (2 * count))
        mean = total / count
        self.raw_lower[leaf] = max(self.raw_lower[leaf], mean-radius, 0.)
        self.raw_upper[leaf] = min(self.raw_upper[leaf], mean+radius, 1.)
        self.work.confidence_work += 8
        self.work.statistic_writes += 2
        if self.raw_lower[leaf] > self.raw_upper[leaf]:
            # An empty intersection can occur only outside simultaneous coverage.
            # Stop with an explicit alarm, never label this a valid certificate.
            self.conflict = True
            return
        if self.quantized:
            lower = max(0, math.floor(math.nextafter(self.scale*self.raw_lower[leaf], -math.inf)))
            upper = min(self.scale, math.ceil(math.nextafter(self.scale*self.raw_upper[leaf], math.inf)))
            self.work.confidence_work += 4
        else:
            lower, upper = self.raw_lower[leaf], self.raw_upper[leaf]
        changed = self._publish(leaf, lower, upper)
        self.leaf_changes += int(changed)
        if self.mode == "event" and changed:
            self._propagate(leaf)
        elif self.mode == "full" and changed:
            # Strong full-DP control skips every unchanged quantized observation.
            self.dp_passes += 1
            for node in reversed(self.graph.order):
                self._scan_node(node)
        elif self.mode == "path":
            # Revisit the path even on unchanged leaves: off-path evidence may
            # have changed a child while this parent remained stale.
            for node in reversed(path[:-1]):
                self._scan_node(node)
        if changed or self.mode == "path":
            self._certify()


class SharedCertificateUCT(TranspositionUCT):
    """UCT on non-dominated actions, with shared numeric confidence backups.

`prune=False` is the same-monitor transposition-UCT allocation control.
`mode='full'` has identical decisions to event propagation in exact arithmetic.
`mode='path'` keeps valid but possibly stale off-path bounds.
"""
    def __init__(self, graph, exploration=.7, epsilon=.05, delta=.05,
                 mode="event", quantized=True, prune=True, pooled=False):
        super().__init__(graph, exploration=exploration)
        self.bounds = SharedBounds(graph, self.work, epsilon, delta, mode, quantized)
        self.prune, self.pooled = prune, pooled
        self.active = [list(range(len(row))) for row in graph.children]
        self.dead = [[False]*len(row) for row in graph.children]
        self.seen_versions = [-1]*len(graph)
        self.removed_edges = self.offpath_prunes = 0
        self.last_path = set()
        self.work.initialization += 2*sum(map(len,graph.children)) + 2*len(graph)
        if pooled:
            self.state_counts, self.state_means = [0]*len(graph), [0.]*len(graph)
            self.work.initialization += 2*len(graph)

    @property
    def stopped(self):
        bounds = getattr(self, "bounds", None)
        return bounds is not None and (bounds.action is not None or bounds.conflict)

    def _prune(self, node):
        if not self.prune:
            return
        if self.seen_versions[node] == self.bounds.versions[node]:
            return
        self.seen_versions[node] = self.bounds.versions[node]
        self.work.statistic_writes += 1
        active = self.active[node]
        i = 0
        while i < len(active):
            action = active[i]
            child = self.graph.children[node][action]
            self.work.confidence_work += 2
            if self.bounds.upper[child] < self.bounds.lower[node]:
                active[i] = active[-1]
                active.pop()
                self.dead[node][action] = True
                self.removed_edges += 1
                self.offpath_prunes += int(child not in self.last_path)
                self.work.statistic_writes += 3
                if node == self.graph.root:
                    self.recommendation.update(action, -math.inf)
                    self.most_visited.update(action, -math.inf)
            else:
                i += 1
        if not active:
            raise AssertionError("Consistent MAX intervals cannot eliminate every action")

    def _score(self, node, action, x):
        if not self.pooled:
            return super()._score(node, action, x)
        self.work.score_evaluations += 1
        return self.state_means[self.graph.children[node][action]] + self.slopes[node][action]*x

    def _select(self, node):
        if not self.prune:
            return super()._select(node)
        self._prune(node)
        degree = len(self.counts[node])
        while self.untried[node] < degree and self.dead[node][self.untried[node]]:
            self.untried[node] += 1
            self.work.edge_reads += 1
        if self.untried[node] < degree:
            action = self.untried[node]
            self.untried[node] += 1
            self.work.edge_reads += 1
            return action
        x = math.sqrt(math.log1p(self.visits[node]))
        best, value = -1, -math.inf
        self.work.full_scans += 1
        for action in self.active[node]:
            score = self._score(node, action, x)
            self.work.edge_reads += 1
            if score > value or (score == value and action < best):
                best, value = action, score
        return best

    def step(self, oracle):
        if self.stopped:
            return None
        result = super().step(oracle)
        path, reward = result
        self.last_path = set(path)
        self.work.statistic_writes += len(path)
        if self.pooled:
            for node in path:
                self.state_counts[node] += 1
                self.state_means[node] += (reward-self.state_means[node])/self.state_counts[node]
                self.work.statistic_writes += 2
            for action, child in enumerate(self.graph.children[self.graph.root]):
                value=self.state_means[child] if self.state_counts[child] else -math.inf
                self.recommendation.update(action, -math.inf if self.dead[self.graph.root][action] else value)
                self.work.query_reads += 1
        leaf = path[-1]
        self.bounds.observe(leaf, self.leaf_counts[leaf], self.leaf_sums[leaf], path)
        if self.graph.children[self.graph.root] and not self.bounds.conflict:
            self._prune(self.graph.root)
        return result

    def recommend_action(self, visits=False):
        self.work.query_reads += 1
        if self.bounds.action is not None:
            return self.bounds.action
        if not self.graph.children[self.graph.root]:
            return -1
        return self.most_visited.top if visits else self.recommendation.top
