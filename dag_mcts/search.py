"""Baselines and sampled-ancestor Bellman MCTS (see docs/theory.md).

    Local traversal counts control exploration.
    Shared leaf samples estimate rewards.
    Internal Bellman refreshes are computations, never extra observations.
"""

from dataclasses import asdict, dataclass, field
import math
import random


@dataclass
class Work:
    oracle_calls: int = 0
    selection_edge_reads: int = 0
    backup_edge_reads: int = 0
    ancestor_edge_reads: int = 0
    policy_edge_reads: int = 0
    routing_edge_reads: int = 0
    routing_stat_writes: int = 0
    value_writes: int = 0
    traversal_count_writes: int = 0
    statistic_count_writes: int = 0
    extra_refreshes: int = 0

    def to_dict(self):
        result = asdict(self)
        # A transparent work proxy, not CPU instructions or a complexity theorem.
        result["work_units"] = (self.selection_edge_reads + self.backup_edge_reads
                                + self.ancestor_edge_reads + self.value_writes
                                + self.traversal_count_writes + self.statistic_count_writes
                                + self.policy_edge_reads + self.routing_edge_reads
                                + self.routing_stat_writes)
        return result


def _check_parameters(exploration, initial):
    if not math.isfinite(exploration) or exploration <= 0:
        raise ValueError("Exploration must be strictly positive and finite")
    if not math.isfinite(initial) or not 0 <= initial <= 1:
        raise ValueError("Initial values must lie in [0, 1]")


def _ucb_action(values, counts, total, exploration):
    """Fixed action order resolves ties; each untried edge is tried first."""
    for action, count in enumerate(counts):
        if count == 0:
            return action
    log_total = math.log1p(total)
    return max(range(len(values)),
               key=lambda a: values[a] + exploration * math.sqrt(log_total / counts[a]))


def _ancestors(graph, leaf, work):
    """Distinct strict ancestors, counted once even with multiple paths."""
    ancestors = set()
    pending = [leaf]
    while pending:
        s = pending.pop()
        for parent in graph.parents[s]:
            work.ancestor_edge_reads += 1
            if parent not in ancestors:
                ancestors.add(parent)
                pending.append(parent)
    return ancestors


def sample_extra_ancestors(graph, leaf, path, draws, rng, work):
    """At most `draws` extra nodes, with O(draws * H) parent-edge reads.

    Each draw picks a length uniformly from 1..longest_root_to_leaf_depth,
    then takes uniformly random parent edges, stopping early at the root.
    Path members and duplicate endpoints are discarded. This distribution is
    NOT uniform over ancestors. No ancestor closure or inclusion weights needed.
    """
    extra = set()
    height = graph.depth[leaf]
    if height == 0:
        return extra
    for _ in range(draws):
        s = leaf
        for _ in range(rng.randint(1, height)):
            parents = graph.parents[s]
            if not parents:
                break
            s = rng.choice(parents)
            work.ancestor_edge_reads += 1
        if s not in path:
            extra.add(s)
    return extra


class BellmanMCTS:
    """Shared leaf means, local-edge UCB, sampled or full Bellman refreshes.

    Every actual path is refreshed. `extra_draws=0` is the path-only ablation;
    `full_backups=True` refreshes every distinct ancestor instead of sampling.
    The max backup, rather than a rollout mean, is the deliberate MCTS variant.
    """

    def __init__(self, graph, exploration=0.7, initial=0.5, extra_draws=4,
                 seed=0, full_backups=False, operators=None):
        _check_parameters(exploration, initial)
        if not isinstance(extra_draws, int) or extra_draws < 0:
            raise ValueError("extra_draws must be a nonnegative integer")
        self.graph = graph
        from .certificates import validate_operators
        self.operators = validate_operators(graph, operators)
        self.exploration = exploration
        self.extra_draws = extra_draws
        self.full_backups = full_backups
        self.rng = random.Random(seed)
        self.values = [initial] * len(graph)
        self.visits = [0] * len(graph)
        self.edge_counts = [[0] * len(row) for row in graph.children]
        self.leaf_counts = [0] * len(graph)
        self.work = Work()

    def step(self, oracle):
        graph = self.graph
        s = graph.root
        path = [s]
        while graph.children[s]:
            children = graph.children[s]
            self.work.selection_edge_reads += len(children)
            direction = -1 if self.operators[s] == "min" else 1
            action = _ucb_action([direction * self.values[c] for c in children], self.edge_counts[s],
                                 self.visits[s], self.exploration)
            self.visits[s] += 1
            self.edge_counts[s][action] += 1
            self.work.traversal_count_writes += 2
            s = children[action]
            path.append(s)
        reward = oracle.sample(s)
        self.work.oracle_calls += 1
        self.visits[s] += 1
        self.work.traversal_count_writes += 1
        self.leaf_counts[s] += 1
        self.work.statistic_count_writes += 1
        self.values[s] += (reward - self.values[s]) / self.leaf_counts[s]
        self.work.value_writes += 1
        path_set = set(path)
        if self.full_backups:
            refresh = _ancestors(graph, s, self.work)
            self.work.extra_refreshes += len(refresh - path_set)
        else:
            extra = sample_extra_ancestors(graph, s, path_set, self.extra_draws,
                                           self.rng, self.work)
            self.work.extra_refreshes += len(extra)
            refresh = set(path[:-1]) | extra
        # Reverse topological order: refreshed children precede their parents.
        # Skipped children can be stale; the proof explicitly permits this.
        for node in sorted(refresh, key=graph.rank.__getitem__, reverse=True):
            children = graph.children[node]
            self.work.backup_edge_reads += len(children)
            op = min if self.operators[node] == "min" else max
            self.values[node] = op(self.values[c] for c in children)
            self.work.value_writes += 1
        return tuple(path), reward

    def recommend(self):
        """Greedy path from cached values; does not refresh or query the oracle."""
        path = [self.graph.root]
        while self.graph.children[path[-1]]:
            op = min if self.operators[path[-1]] == "min" else max
            path.append(op(self.graph.children[path[-1]], key=self.values.__getitem__))
        return tuple(path)

    @property
    def materialized_nodes(self):
        return len(self.graph)


class NaiveAllAncestors:
    """Intentionally unsound baseline: every ancestor receives the raw reward.

    Child *global* update counts are used as UCB denominators, including updates
    arriving through another parent. Even forcing locally untried actions once
    does not prevent the trap after the first two rollouts.
    """

    def __init__(self, graph, exploration=0.7, initial=0.5):
        _check_parameters(exploration, initial)
        self.graph = graph
        self.exploration = exploration
        self.values = [initial] * len(graph)
        self.update_counts = [0] * len(graph)
        self.edge_counts = [[0] * len(row) for row in graph.children]
        self.work = Work()

    def step(self, oracle):
        graph = self.graph
        s = graph.root
        path = [s]
        while graph.children[s]:
            children = graph.children[s]
            self.work.selection_edge_reads += len(children)
            untried = next((a for a, n in enumerate(self.edge_counts[s]) if n == 0), None)
            if untried is not None:
                action = untried
            else:
                action = _ucb_action([self.values[c] for c in children],
                                     [self.update_counts[c] for c in children],
                                     self.update_counts[s], self.exploration)
            self.edge_counts[s][action] += 1
            self.work.traversal_count_writes += 1
            s = children[action]
            path.append(s)
        reward = oracle.sample(s)
        self.work.oracle_calls += 1
        ancestors = _ancestors(graph, s, self.work)
        self.work.extra_refreshes += len(ancestors - set(path))
        for node in ancestors | {s}:
            self.update_counts[node] += 1
            self.work.statistic_count_writes += 1
            self.values[node] += (reward - self.values[node]) / self.update_counts[node]
            self.work.value_writes += 1
        return tuple(path), reward

    def recommend(self):
        path = [self.graph.root]
        while self.graph.children[path[-1]]:
            children = self.graph.children[path[-1]]
            counts = self.edge_counts[path[-1]]
            tried = [a for a, n in enumerate(counts) if n]
            action = max(tried, key=lambda a: self.values[children[a]]) if tried else 0
            path.append(children[action])
        return tuple(path)

    @property
    def materialized_nodes(self):
        return len(self.graph)


@dataclass
class _TreeNode:
    state: int
    count: int = 0
    mean: float = 0.5
    children: dict = field(default_factory=dict)


class TreeUCT:
    """Classical UCT on unfolded histories, with empirical rollout-mean backups.

    Each history has separate statistics even if its final state is shared.
    Nodes are created lazily along complete trajectories; topology is known.
    Recommendation greedily follows the highest empirical mean of visited arms.
    """

    def __init__(self, graph, exploration=0.7, initial=0.5, operators=None):
        _check_parameters(exploration, initial)
        self.graph = graph
        from .certificates import validate_operators
        self.operators = validate_operators(graph, operators)
        self.exploration = exploration
        self.initial = initial
        self.root = _TreeNode(graph.root, mean=initial)
        self.work = Work()
        self._size = 1

    def step(self, oracle):
        node = self.root
        nodes = [node]
        while self.graph.children[node.state]:
            children = self.graph.children[node.state]
            self.work.selection_edge_reads += len(children)
            counts = [node.children[a].count if a in node.children else 0
                      for a in range(len(children))]
            values = [node.children[a].mean if a in node.children else self.initial
                      for a in range(len(children))]
            if self.operators[node.state] == "min":
                values = [-value for value in values]
            action = _ucb_action(values, counts, node.count, self.exploration)
            if action not in node.children:
                node.children[action] = _TreeNode(children[action], mean=self.initial)
                self._size += 1
            node = node.children[action]
            nodes.append(node)
        reward = oracle.sample(node.state)
        self.work.oracle_calls += 1
        for current in reversed(nodes):
            current.count += 1
            current.mean += (reward - current.mean) / current.count
            self.work.value_writes += 1
            self.work.traversal_count_writes += 1
        return tuple(current.state for current in nodes), reward

    def recommend(self):
        node = self.root
        path = [node.state]
        while self.graph.children[path[-1]]:
            if node is not None and node.children:
                op = min if self.operators[node.state] == "min" else max
                action = op(sorted(node.children), key=lambda a: node.children[a].mean)
                node = node.children[action]
                path.append(node.state)
            else:
                # Only relevant before a complete rollout has been observed.
                path.append(self.graph.children[path[-1]][0])
                node = None
        return tuple(path)

    @property
    def materialized_nodes(self):
        return self._size
