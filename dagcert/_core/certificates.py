"""Sequential terminal tests and one-time threshold certificates on MIN/MAX DAGs.

The mathematical specification is paper/certificates/theory.tex. Sampling and
certificate propagation are separate: the monitor can certify an existing
sampler without changing its decisions. A certificate is never an extra sample.
"""

from dataclasses import dataclass
import math
import random

from .graph import DAG, Problem


def validate_operators(graph, operators=None):
    ops = tuple(operators) if operators is not None else ("max",) * len(graph)
    if len(ops) != len(graph) or any(op not in ("min", "max") for op in ops):
        raise ValueError("Provide one min/max operator per node")
    return ops


def node_values(graph, operators, means):
    values = [0.] * len(graph)
    for node in reversed(graph.order):
        row = graph.children[node]
        values[node] = ((min if operators[node] == "min" else max)(values[c] for c in row)
                        if row else means[node])
    return values


def terminal_order(graph, seed=0):
    """Linear-time degree buckets; random ties are fixed before observing data."""
    leaves = list(graph.leaves)
    random.Random(seed).shuffle(leaves)
    buckets = [[] for _ in range(len(graph))]
    for leaf in leaves:
        buckets[len(graph.parents[leaf])].append(leaf)
    return tuple(leaf for bucket in reversed(buckets) for leaf in bucket)


def test_radius(checkpoint, alpha):
    """Checkpoint j has n=2**j; sum of its two-sided error budgets is alpha."""
    return math.sqrt(math.log(math.pi ** 2 * (checkpoint + 1) ** 2 / (3 * alpha))
                     / (2 * (1 << checkpoint)))


@dataclass
class CertificateWork:
    initialization: int = 0
    sample_updates: int = 0
    confidence_tests: int = 0
    propagation_edges: int = 0
    state_updates: int = 0
    selection_reads: int = 0
    ancestor_edges: int = 0
    backup_edges: int = 0

    @property
    def total(self):
        return sum(vars(self).values())


class CertificateMonitor:
    """Status 0=unknown, +1=above threshold, -1=below threshold.

    event: propagate only a newly resolved sign, each edge at most once.
    full: recompute interval bounds on the complete ancestor closure at each
          dyadic checkpoint; same terminal tests and error allocation.
    """

    def __init__(self, graph, operators=None, threshold=.5, delta=.05, seed=0,
                 mode="event", order=None):
        if not math.isfinite(threshold) or not 0 < threshold < 1:
            raise ValueError("threshold must lie strictly between zero and one")
        if not math.isfinite(delta) or not 0 < delta < .5:
            raise ValueError("delta must lie strictly between zero and one half")
        if mode not in ("event", "full"):
            raise ValueError("Unknown propagation mode")
        self.graph = graph
        self.operators = validate_operators(graph, operators)
        self.threshold, self.delta, self.mode = threshold, delta, mode
        self.order = terminal_order(graph, seed) if order is None else tuple(order)
        if len(self.order) != len(graph.leaves) or set(self.order) != set(graph.leaves):
            raise ValueError("Order must contain each terminal exactly once")
        size = len(graph)
        self.alpha = [0.] * size
        for rank, leaf in enumerate(self.order):
            self.alpha[leaf] = delta / ((rank + 1) * (rank + 2))
        self.counts = [0] * size
        self.sums = [0.] * size
        self.status = [0] * size
        self.resolved_children = [0] * size
        self.lower = [0.] * size
        self.upper = [1.] * size
        self.work = CertificateWork(initialization=8 * size + 2 * len(graph.leaves))
        self.observations = 0

    @property
    def decision(self):
        return self.status[self.graph.root]

    def observe(self, leaf, reward):
        if self.graph.children[leaf]:
            raise ValueError("Only terminal observations are allowed")
        if not math.isfinite(reward) or not 0 <= reward <= 1:
            raise ValueError("Rewards must be finite and bounded in [0,1]")
        self.observations += 1
        self.work.sample_updates += 1
        if self.status[leaf] or self.decision:
            return
        self.counts[leaf] += 1
        self.sums[leaf] += reward
        self.work.sample_updates += 2
        n = self.counts[leaf]
        if n & (n - 1):
            return
        j = n.bit_length() - 1
        radius = test_radius(j, self.alpha[leaf])
        mean = self.sums[leaf] / n
        # Non-nested tests make behavior well-defined even off the good event.
        self.lower[leaf] = max(0., mean - radius)
        self.upper[leaf] = min(1., mean + radius)
        self.work.confidence_tests += 1
        self.work.state_updates += 2
        sign = 1 if self.lower[leaf] > self.threshold else (
            -1 if self.upper[leaf] < self.threshold else 0)
        if sign:
            self.status[leaf] = sign
            self.work.state_updates += 1
        if self.mode == "full":
            self._full_refresh(leaf)
        elif sign:
            self._propagate(leaf)

    def _propagate(self, leaf):
        pending = [leaf]
        while pending:
            child = pending.pop()
            for parent in self.graph.parents[child]:
                self.work.propagation_edges += 1
                if self.status[parent]:
                    continue
                self.resolved_children[parent] += 1
                self.work.state_updates += 1
                decisive = 1 if self.operators[parent] == "max" else -1
                if self.status[child] == decisive:
                    self.status[parent] = decisive
                elif self.resolved_children[parent] == len(self.graph.children[parent]):
                    self.status[parent] = -decisive
                if self.status[parent]:
                    self.work.state_updates += 1
                    pending.append(parent)

    def _full_refresh(self, leaf):
        ancestors, pending = set(), [leaf]
        while pending:
            child = pending.pop()
            for parent in self.graph.parents[child]:
                self.work.ancestor_edges += 1
                if parent not in ancestors:
                    ancestors.add(parent)
                    pending.append(parent)
        for parent in sorted(ancestors, key=self.graph.rank.__getitem__, reverse=True):
            row = self.graph.children[parent]
            op = min if self.operators[parent] == "min" else max
            self.work.backup_edges += 2 * len(row)
            self.lower[parent] = op(self.lower[c] for c in row)
            self.upper[parent] = op(self.upper[c] for c in row)
            self.work.state_updates += 2
            sign = 1 if self.lower[parent] > self.threshold else (
                -1 if self.upper[parent] < self.threshold else 0)
            if sign and not self.status[parent]:
                self.status[parent] = sign
                self.work.state_updates += 1


class CertificateSearch:
    """Finish one terminal test at a time, in static decreasing-fanout order."""

    def __init__(self, graph, operators=None, threshold=.5, delta=.05, seed=0,
                 mode="event", oracle_ids=None):
        self.graph = graph
        self.monitor = CertificateMonitor(graph, operators, threshold, delta, seed, mode)
        self.order = self.monitor.order
        self.oracle_ids = tuple(range(len(graph))) if oracle_ids is None else tuple(oracle_ids)
        if len(self.oracle_ids) != len(graph):
            raise ValueError("One oracle mapping entry required per node")
        self.position = 0
        self.current = None
        self.calls = 0

    @property
    def decision(self):
        return self.monitor.decision

    def step(self, oracle):
        if self.decision:
            return None
        monitor = self.monitor
        while self.current is None or monitor.status[self.current]:
            if self.position == len(self.order):
                raise RuntimeError("Unresolved root with no relevant terminal")
            leaf = self.order[self.position]
            self.position += 1
            monitor.work.selection_reads += 1
            # A terminal whose every immediate parent is resolved is irrelevant.
            parents = self.graph.parents[leaf]
            monitor.work.selection_reads += len(parents)
            if parents and all(monitor.status[p] for p in parents):
                continue
            self.current = leaf
        reward = oracle.sample(self.oracle_ids[self.current])
        self.calls += 1
        monitor.observe(self.current, reward)
        return self.oracle_ids[self.current], reward


def unfolded_size(graph):
    paths = [0] * len(graph)
    paths[graph.root] = 1
    for node in graph.order:
        for child in graph.children[node]:
            paths[child] += paths[node]
    return sum(paths)


def unfold(graph, operators=None, max_nodes=50000):
    """Explicit independent-history comparator; never merges terminal copies."""
    operators = validate_operators(graph, operators)
    if unfolded_size(graph) > max_nodes:
        raise ValueError("Unfolding exceeds the declared size cap")
    source, rows, ops = [graph.root], [], []
    index = 0
    while index < len(source):
        node = source[index]
        row = []
        for child in graph.children[node]:
            row.append(len(source))
            source.append(child)
        rows.append(tuple(row))
        ops.append(operators[node])
        index += 1
    return DAG(rows), tuple(ops), tuple(source)


def sunflower(petals=32, gap=.15, core_positive=True):
    """MIN_i MAX(z,x_i), with one shared z and distinct private terminals."""
    if petals < 2 or not 0 < gap <= .25:
        raise ValueError("Need at least two petals and gap in (0,.25]")
    core = petals + 1
    rows = [tuple(range(1, petals + 1))]
    rows.extend((core, core + 1 + i) for i in range(petals))
    rows.extend(() for _ in range(petals + 1))
    graph = DAG(rows)
    means = {core: .5 + (gap if core_positive else -gap)}
    means.update({core + 1 + i: .25 for i in range(petals)})
    operators = ("min",) + ("max",) * (len(graph) - 1)
    name = f"sunflower_{petals}_{'positive' if core_positive else 'negative'}"
    return Problem(name, graph, means), operators, .5


def diamond_chain(depth=8, gap=.15, positive=False):
    """Width-two layers, all-MAX; exponentially many histories share one leaf."""
    if depth < 1 or not 0 < gap <= .25:
        raise ValueError("Invalid depth or gap")
    leaf = 1 + 2 * depth
    rows = [(1, 2)]
    for level in range(depth):
        children = (1 + 2 * (level + 1), 2 + 2 * (level + 1)) if level + 1 < depth else (leaf,)
        rows.extend((children, children))
    rows.append(())
    graph = DAG(rows)
    problem = Problem(f"diamond_{depth}_{'positive' if positive else 'negative'}", graph,
                      {leaf: .5 + (gap if positive else -gap)})
    return problem, ("max",) * len(graph), .5
