"""Exact lazy UCB selection on a canonical DAG, plus optional PAC root stopping.

Computation certificates bound unrefreshed UCB scores; statistical certificates
bound terminal means. The former preserve the reference UCT policy exactly.
No rollout reward is copied to an untraversed incoming edge.
"""

from dataclasses import dataclass
import math

from .certificates import validate_operators


@dataclass
class UCTWork:
    initialization: int = 0
    edge_reads: int = 0
    score_evaluations: int = 0
    heap_comparisons: int = 0
    heap_writes: int = 0
    statistic_writes: int = 0
    confidence_work: int = 0
    oracle_calls: int = 0
    query_reads: int = 0
    lazy_refreshes: int = 0
    full_scans: int = 0
    rebuild_entries: int = 0
    certified_selections: int = 0
    budget_fallbacks: int = 0

    @property
    def total(self):
        # Refresh/scan/rebuild/certificate/fallback counters are diagnostic only.
        return (self.initialization + self.edge_reads + self.score_evaluations +
                self.heap_comparisons + self.heap_writes + self.statistic_writes +
                self.confidence_work + self.oracle_calls + self.query_reads)


class IndexedMaxHeap:
    """Bounded-size heap; exact fixed action-ID tie breaking, no stale entries."""

    def __init__(self, keys, work):
        self.keys = list(keys)
        self.ids = list(range(len(keys)))
        self.positions = list(range(len(keys)))
        self.work = work
        work.initialization += 3 * len(keys)
        self.rebuild()

    def _better(self, a, b):
        self.work.heap_comparisons += 1
        return self.keys[a] > self.keys[b] or (self.keys[a] == self.keys[b] and a < b)

    def _swap(self, i, j):
        a, b = self.ids[i], self.ids[j]
        self.ids[i], self.ids[j] = b, a
        self.positions[a], self.positions[b] = j, i
        self.work.heap_writes += 4

    def _down(self, i):
        size = len(self.ids)
        while 2 * i + 1 < size:
            child = 2 * i + 1
            if child + 1 < size and self._better(self.ids[child + 1], self.ids[child]):
                child += 1
            if not self._better(self.ids[child], self.ids[i]):
                break
            self._swap(i, child)
            i = child

    def rebuild(self):
        for i in reversed(range(len(self.ids) // 2)):
            self._down(i)

    def update(self, action, key):
        old = self.keys[action]
        self.keys[action] = key
        self.work.heap_writes += 1
        pos = self.positions[action]
        if key > old:
            while pos and self._better(action, self.ids[(pos - 1) // 2]):
                parent = (pos - 1) // 2
                self._swap(pos, parent)
                pos = parent
        else:
            self._down(pos)

    @property
    def top(self):
        return self.ids[0]

    def second(self):
        if len(self.ids) < 2:
            return None
        if len(self.ids) == 2 or self._better(self.ids[1], self.ids[2]):
            return self.ids[1]
        return self.ids[2]


class RootCertificate:
    """Common monitor: full DAG confidence DP only at global doubling epochs.

    Finite known deterministic transitions, independent bounded terminal streams.
    No means/gaps are given to this object. Intervals are valid at all local n.
    """

    def __init__(self, graph, operators, work, delta=.05, epsilon=.05):
        if not 0 < delta < .5 or not 0 < epsilon < 1:
            raise ValueError("Need delta in (0,.5) and epsilon in (0,1)")
        self.graph, self.operators, self.work = graph, operators, work
        self.delta, self.epsilon = delta, epsilon
        self.lower, self.upper = [0.] * len(graph), [1.] * len(graph)
        self.action = None
        self.epoch = 0
        self.gap_bound = 1.
        work.initialization += 2 * len(graph) + 5

    def refresh(self, counts, sums, calls):
        graph, work = self.graph, self.work
        alpha = self.delta / len(graph.leaves)
        for leaf in graph.leaves:
            n = counts[leaf]
            if n:
                radius = math.sqrt((math.log(math.pi ** 2 / (3 * alpha)) + 2 * math.log(n)) / (2 * n))
                mean = sums[leaf] / n
                self.lower[leaf], self.upper[leaf] = max(0., mean-radius), min(1., mean+radius)
            work.confidence_work += 5
        for node in reversed(graph.order):
            row = graph.children[node]
            if row:
                op = min if self.operators[node] == "min" else max
                self.lower[node] = op(self.lower[c] for c in row)
                self.upper[node] = op(self.upper[c] for c in row)
                work.confidence_work += 2 * len(row) + 2
        row = graph.children[graph.root]
        if not row:
            self.action, self.gap_bound = -1, 0.
        elif len(row) == 1:
            self.action, self.gap_bound = 0, 0.
        else:
            # Root is a maximizing decision, even when internal gates are MIN.
            best = max(range(len(row)), key=lambda a:self.lower[row[a]])
            rival = max(self.upper[c] for a, c in enumerate(row) if a != best)
            self.gap_bound = max(0., rival - self.lower[row[best]])
            if self.gap_bound <= self.epsilon:
                self.action = best
            work.confidence_work += 2 * len(row)
        self.epoch = calls


class TranspositionUCT:
    """Shared canonical outgoing-edge rollout means, with local-edge UCB counts.

    ``lazy`` changes only action-maximization computation. ``certify`` adds an
    identical monitor and stopping rule to either allocator. Default search is
    all-MAX, but fixed internal MIN gates are supported with a MAX root.
    """

    def __init__(self, graph, exploration=.7, lazy=False, certify=False,
                 delta=.05, epsilon=.05, operators=None, lazy_min_degree=8):
        if not math.isfinite(exploration) or exploration <= 0:
            raise ValueError("Exploration must be positive and finite")
        self.graph, self.exploration, self.lazy = graph, exploration, lazy
        if not isinstance(lazy_min_degree,int) or lazy_min_degree<2:
            raise ValueError("Lazy minimum degree must be an integer >= 2")
        self.lazy_nodes = [lazy and len(row)>=lazy_min_degree for row in graph.children]
        self.operators = validate_operators(graph, operators)
        if graph.children[graph.root] and self.operators[graph.root] != "max":
            raise ValueError("Best-action task uses a MAX root")
        self.work = UCTWork()
        self.counts = [[0] * len(row) for row in graph.children]
        self.means = [[0.] * len(row) for row in graph.children]
        self.slopes = [[exploration] * len(row) for row in graph.children]
        self.visits, self.untried = [0] * len(graph), [0] * len(graph)
        self.leaf_counts, self.leaf_sums = [0] * len(graph), [0.] * len(graph)
        self.calls = 0
        self.caps = [exploration] * len(graph)
        self.stamps = [[-1] * len(row) if self.lazy_nodes[v] else []
                       for v,row in enumerate(graph.children)] if lazy else None
        edges = sum(map(len, graph.children))
        self.work.initialization += 6 * len(graph) + 3 * edges + (edges if lazy else 0)
        # Build an eligible node's heap only after all its edges have been tried.
        self.heaps = [None] * len(graph) if lazy else None
        root_degree = len(graph.children[graph.root])
        # Identical bounded heaps in both methods make recommendation queries O(1).
        self.recommendation = IndexedMaxHeap([-math.inf] * root_degree, self.work)
        self.most_visited = IndexedMaxHeap([0] * root_degree, self.work)
        self.monitor = RootCertificate(graph, self.operators, self.work, delta, epsilon) if certify else None
        if self.monitor and root_degree <= 1:
            self.monitor.action = 0 if root_degree else -1
            self.monitor.gap_bound = 0.

    @property
    def stopped(self):
        return self.monitor is not None and self.monitor.action is not None

    def _score(self, node, action, x):
        self.work.score_evaluations += 1
        direction = -1 if self.operators[node] == "min" else 1
        return direction * self.means[node][action] + self.slopes[node][action] * x

    def _key(self, node, action, x):
        direction = -1 if self.operators[node] == "min" else 1
        return direction * self.means[node][action] + (self.slopes[node][action] - self.caps[node]) * x

    def _padding(self, node, x):
        # Conservative roundoff cushion. Near ties use the reference full scan.
        return 32 * math.ulp(max(1., abs(self.caps[node] * x), self.exploration))

    def _scan(self, node, x):
        self.work.full_scans += 1
        best, value = 0, -math.inf
        for action in range(len(self.counts[node])):
            self.work.edge_reads += 1
            score = self._score(node, action, x)
            if score > value:
                best, value = action, score
        return best

    def _rebuild(self, node, x):
        heap = self.heaps[node]
        self.caps[node] = self.exploration / math.sqrt(min(self.counts[node]))
        self.work.edge_reads += len(self.counts[node])
        for a in range(len(heap.keys)):
            heap.keys[a] = self._key(node, a, x)
            self.stamps[node][a] = self.visits[node]
            self.work.rebuild_entries += 1
            self.work.edge_reads += 1
            self.work.heap_writes += 2
        heap.rebuild()

    def _select(self, node):
        degree = len(self.counts[node])
        if self.untried[node] < degree:
            action = self.untried[node]
            self.untried[node] += 1
            self.work.edge_reads += 1
            return action
        x = math.sqrt(math.log1p(self.visits[node]))
        if not self.lazy_nodes[node]:
            return self._scan(node, x)
        heap = self.heaps[node]
        common, padding = self.caps[node] * x, self._padding(node, x)
        started_work = self.work.edge_reads+self.work.score_evaluations+self.work.heap_comparisons+self.work.heap_writes
        while True:
            spent = self.work.edge_reads+self.work.score_evaluations+self.work.heap_comparisons+self.work.heap_writes-started_work
            if spent>4*degree:
                self.work.budget_fallbacks += 1
                best = self._scan(node,x)
                self._rebuild(node,x)
                return best
            a, second = heap.top, heap.second()
            self.work.edge_reads += 2
            score = self._score(node, a, x)
            if second is None or score > heap.keys[second] + common + padding:
                self.work.certified_selections += 1
                return a
            if self.stamps[node][a] == self.visits[node]:
                # A stale runner-up bound can coincide with the fresh maximum.
                # Tighten it before falling back for genuine numerical/tie ambiguity.
                if self.stamps[node][second] != self.visits[node]:
                    self.work.score_evaluations += 1
                    heap.update(second, self._key(node, second, x))
                    self.stamps[node][second] = self.visits[node]
                    self.work.lazy_refreshes += 1
                    continue
                best = self._scan(node, x)
                self._rebuild(node, x)
                return best
            heap.update(a, self._key(node, a, x))
            self.stamps[node][a] = self.visits[node]
            self.work.lazy_refreshes += 1

    def step(self, oracle):
        if self.stopped:
            return None
        node, edges, path = self.graph.root, [], [self.graph.root]
        while self.graph.children[node]:
            action = self._select(node)
            edges.append((node, action))
            node = self.graph.children[node][action]
            path.append(node)
        reward = oracle.sample(node)
        if not math.isfinite(reward) or not 0 <= reward <= 1:
            raise ValueError("Rewards must lie in [0,1]")
        self.calls += 1
        self.work.oracle_calls += 1
        self.leaf_counts[node] += 1
        self.leaf_sums[node] += reward
        self.work.statistic_writes += 2
        for parent, action in reversed(edges):
            self.visits[parent] += 1
            self.counts[parent][action] += 1
            n = self.counts[parent][action]
            self.means[parent][action] += (reward - self.means[parent][action]) / n
            self.slopes[parent][action] = self.exploration / math.sqrt(n)
            self.work.statistic_writes += 4
            if self.lazy_nodes[parent] and self.untried[parent] == len(self.counts[parent]):
                total = self.visits[parent]
                x = math.sqrt(math.log1p(total))
                if self.heaps[parent] is None:
                    keys = [self._key(parent,a,x) for a in range(len(self.counts[parent]))]
                    self.heaps[parent] = IndexedMaxHeap(keys,self.work)
                    self.stamps[parent] = [total]*len(keys)
                    self.work.edge_reads += len(keys)
                    self.work.statistic_writes += len(keys)
                elif total & (total-1) == 0:
                    self._rebuild(parent, x)
                else:
                    self.heaps[parent].update(action, self._key(parent, action, x))
                    self.stamps[parent][action] = total
                    self.work.statistic_writes += 1
        if edges:
            action = edges[0][1]
            self.recommendation.update(action, self.means[self.graph.root][action])
            self.most_visited.update(action, self.counts[self.graph.root][action])
        if self.monitor and self.calls & (self.calls-1) == 0:
            self.monitor.refresh(self.leaf_counts, self.leaf_sums, self.calls)
        return tuple(path), reward

    def recommend_action(self, visits=False):
        self.work.query_reads += 1
        if self.stopped:
            return self.monitor.action
        if not self.graph.children[self.graph.root]:
            return -1
        return self.most_visited.top if visits else self.recommendation.top

    @property
    def materialized_nodes(self):
        return len(self.graph)


class StatePooledUCT(TranspositionUCT):
    """Additional transposition-aware control: pooled child-state rollout means.

    Exploration denominators remain local outgoing-edge counts. This is a
    distinct pooling policy, not the exact-equivalence reference for lazy UCT.
    """

    def __init__(self, graph, **kwargs):
        if kwargs.get("lazy"):
            raise ValueError("State pooling changes unselected scores; lazy edge cache is inapplicable")
        super().__init__(graph, **kwargs)
        self.state_counts, self.state_means = [0] * len(graph), [0.] * len(graph)
        self.work.initialization += 2 * len(graph)

    def _score(self, node, action, x):
        self.work.score_evaluations += 1
        child = self.graph.children[node][action]
        direction = -1 if self.operators[node] == "min" else 1
        return direction * self.state_means[child] + self.slopes[node][action] * x

    def step(self, oracle):
        result = super().step(oracle)
        if result is not None:
            path, reward = result
            for node in path:
                self.state_counts[node] += 1
                self.state_means[node] += (reward-self.state_means[node]) / self.state_counts[node]
                self.work.statistic_writes += 2
            # Root child pooling may change through off-root paths in general DAGs.
            # Refresh all root recommendations rather than hiding that cost.
            for action, child in enumerate(self.graph.children[self.graph.root]):
                self.recommendation.update(action, self.state_means[child] if self.state_counts[child] else -math.inf)
                self.work.query_reads += 1
        return result
