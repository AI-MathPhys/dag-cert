"""Known deterministic transitions and separately held, hidden reward oracles."""

from collections import deque
from dataclasses import dataclass
import math
import random


class DAG:
    """Rooted finite DAG. Child position is the action ID; order breaks ties.

    Search sees topology only. Reward means are held by LeafOracle, not here.
    Duplicate edges, cycles, disconnected states, and invalid indices are rejected.
    """

    def __init__(self, children, root=0, labels=None):
        self.children = tuple(tuple(row) for row in children)
        size = len(self.children)
        if not size or not 0 <= root < size:
            raise ValueError("Graph must have a valid root")
        self.root = root
        parents = [[] for _ in range(size)]
        for s, row in enumerate(self.children):
            if len(set(row)) != len(row):
                raise ValueError("Duplicate edges are not supported")
            for child in row:
                if not isinstance(child, int) or not 0 <= child < size:
                    raise ValueError("Invalid child index")
                parents[child].append(s)
        self.parents = tuple(tuple(row) for row in parents)
        indegree = [len(row) for row in parents]
        pending = deque(s for s, degree in enumerate(indegree) if degree == 0)
        order = []
        while pending:
            s = pending.popleft()
            order.append(s)
            for child in self.children[s]:
                indegree[child] -= 1
                if indegree[child] == 0:
                    pending.append(child)
        if len(order) != size:
            raise ValueError("Graph must be acyclic")
        reached = {root}
        for s in order:
            if s in reached:
                reached.update(self.children[s])
        if len(reached) != size or self.parents[root]:
            raise ValueError("Every state must be reachable from the root")
        self.order = tuple(order)
        self.rank = [0] * size
        self.depth = [0] * size
        for i, s in enumerate(order):
            self.rank[s] = i
            for child in self.children[s]:
                self.depth[child] = max(self.depth[child], self.depth[s] + 1)
        self.leaves = tuple(s for s, row in enumerate(self.children) if not row)
        self.labels = tuple(labels) if labels is not None else tuple(map(str, range(size)))
        if len(self.labels) != size:
            raise ValueError("One label is required per state")

    def __len__(self):
        return len(self.children)

    def optimal_values(self, means):
        """Evaluation utility; algorithms never call this method."""
        if set(means) != set(self.leaves):
            raise ValueError("Provide exactly one mean per terminal leaf")
        values = [0.0] * len(self)
        for s in reversed(self.order):
            values[s] = max((values[c] for c in self.children[s]), default=means.get(s, 0.0))
        return values


class LeafOracle:
    """Independent per-leaf streams; the kth sample of a leaf is paired across methods.

    All sampling and planner random generators are separate. A deterministic leaf
    returns its mean; all other leaves have Bernoulli rewards. No reward mean is
    passed to the search constructors.
    """

    def __init__(self, means, seed=0, deterministic=()):
        if any(not math.isfinite(mu) or not 0 <= mu <= 1 for mu in means.values()):
            raise ValueError("Means must be finite and in [0, 1]")
        self.means = dict(means)
        self.deterministic = frozenset(deterministic)
        if not self.deterministic <= self.means.keys():
            raise ValueError("Unknown deterministic leaf")
        self.rng = {s: random.Random((seed + 1) * 1_000_003 + (s + 1) * 9_176)
                    for s in means}
        self.counts = {s: 0 for s in means}
        self.first_reward = {}

    def sample(self, leaf):
        mu = self.means[leaf]
        reward = mu if leaf in self.deterministic else float(self.rng[leaf].random() < mu)
        self.counts[leaf] += 1
        self.first_reward.setdefault(leaf, reward)
        return reward


@dataclass(frozen=True)
class Problem:
    name: str
    graph: DAG
    means: dict
    deterministic: tuple = ()

    def oracle(self, seed):
        return LeafOracle(self.means, seed, self.deterministic)


def trap():
    """A -> good/shared; B -> shared. A's first good observation can be zero."""
    return Problem("trap", DAG(((1, 2), (3, 4), (4,), (), ()),
                               labels=("root", "A", "B", "good", "shared")),
                   {3: 0.8, 4: 0.5}, (4,))


def feature_lattice(features=7, noisy=True):
    """Every subset has a stop leaf; all insertion orders transpose.

    Three useful features have a joint benefit; irrelevant features cost 0.04.
    The unique optimal terminal subset is {0,1,2}, with reward mean 0.8.
    This is a synthetic reward landscape, not a classifier benchmark.
    """
    if not 3 <= features <= 12:
        raise ValueError("Use between 3 and 12 features for this small benchmark")
    subsets = 1 << features
    children = []
    means = {}
    labels = []
    for mask in range(subsets):
        # Add actions before stop, a fixed ordering shared by all methods.
        children.append(tuple(mask | (1 << bit) for bit in range(features)
                              if not mask & (1 << bit)) + (subsets + mask,))
        labels.append("{" + ",".join(str(i) for i in range(features) if mask & (1 << i)) + "}")
        useful = (mask & 7).bit_count()
        irrelevant = mask.bit_count() - useful
        means[subsets + mask] = max(0.0, 0.20 + 0.12 * useful + 0.24 * (useful == 3) - 0.04 * irrelevant)
    children.extend(() for _ in range(subsets))
    labels.extend("stop " + label for label in labels[:subsets])
    name = f"lattice_{features}_{'bernoulli' if noisy else 'deterministic'}"
    return Problem(name, DAG(children, labels=labels), means,
                   () if noisy else tuple(means))
