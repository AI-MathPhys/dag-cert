"""End-to-end callers for frozen confidence-maintenance backends.

UCT keeps its original edge statistics. The optimistic caller uses only the
public query interface. Neither caller reads oracle means. The root-only flat
monitor is an intentionally strong control for known all-MAX best-leaf search.
"""
import math
import random
import zipfile
from pathlib import Path

from .batched_witness_cab import BatchedWitnessCAB, FastQuotientRange
from .certificate_batch import CertificateBatch
from .certified_uct import IndexedMaxHeap, TranspositionUCT, UCTWork
from .demand_bounds import EagerQueries
from .graph import DAG, Problem, LeafOracle
from .retired_bounds import CanonicalIntervals
from .uct_problems import shared_fanout


class FlatMonitor:
    """Root-value monitor only; no claim to answer arbitrary-node decisions."""
    def __init__(self, graph, work, scale=1):
        self.graph, self.work = graph, work
        self.mapping = {v: i for i, v in enumerate(graph.leaves)}
        self.upper = IndexedMaxHeap([1.] * len(graph.leaves), work)
        self.lower = 0.
        work.initialization += len(graph.leaves) * 2 + 3

    def publish(self, leaf, lo, hi):
        self.work.query_reads += 3
        self.lower = max(self.lower, lo)
        i = self.mapping[leaf]
        if self.upper.keys[i] != hi:
            self.upper.update(i, hi)
        self.work.statistic_writes += 1

    def query(self, node=None):
        if node is not None and node != self.graph.root:
            raise ValueError('FlatMonitor supports only the root value')
        self.work.query_reads += 3
        hi = self.upper.keys[self.upper.top]
        return -1, hi-self.lower, self.lower, hi


def make_backend(graph, work, method):
    return {'witness': BatchedWitnessCAB, 'qrange': FastQuotientRange,
            'eager': EagerQueries, 'cab': CertificateBatch,
            'flat': FlatMonitor}[method](graph, work)


def subset_graph(features):
    n = 1 << features
    rows = [tuple(mask | (1 << bit) for bit in range(features)
                  if not mask & (1 << bit)) + (n+mask,) for mask in range(n)]
    rows.extend(() for _ in range(n))
    return DAG(rows)


class FeatureTask:
    """Fixed split, training-only normalization and nearest-centroid classifier.

    A draw selects one held-out example with replacement. Each subset therefore
    has a fixed bounded reward distribution conditional on the split. Its mean
    is finite validation accuracy times a prespecified sparsity factor. This is
    not a population-generalization guarantee or an AlphaFUSE reproduction.
    """
    def __init__(self, name, split_seed, data_dir=None):
        import numpy as np
        self.np = np
        folder = Path(data_dir or Path(__file__).resolve().parents[1]/'data'/'uci')
        with zipfile.ZipFile(folder/(name+'.zip')) as archive:
            lines = archive.read(name+'.data').decode().strip().splitlines()
        rows = [line.split(',') for line in lines if line.strip()]
        if name == 'iris':
            x = np.array([r[:-1] for r in rows], dtype=float)
            labels = {s: i for i, s in enumerate(sorted({r[-1] for r in rows}))}
            y = np.array([labels[r[-1]] for r in rows])
        else:
            # First six columns fixed before evaluation, not chosen by accuracy.
            x = np.array([r[1:7] for r in rows], dtype=float)
            y = np.array([int(r[0])-1 for r in rows])
        self.features = x.shape[1]
        self.name = name+str(self.features)
        rng = random.Random(split_seed)
        train, valid = [], []
        for label in sorted(set(y)):
            ids = [i for i in range(len(y)) if y[i] == label]
            rng.shuffle(ids); cut = int(.7*len(ids))
            train.extend(ids[:cut]); valid.extend(ids[cut:])
        self.train_ids, self.valid_ids = train, valid
        self.xtrain, self.ytrain = x[train], y[train]
        self.xvalid, self.yvalid = x[valid], y[valid]
        self.graph = subset_graph(self.features)
        self.offset = 1 << self.features
        self.penalty = .02
        # Evaluation only. Search oracles receive training/validation arrays,
        # never this table; construction is outside timed search.
        self.means = {}
        evaluator = FeatureOracle(self, 0, 'cached')
        for leaf in self.graph.leaves:
            evaluator.fit(leaf)
            self.means[leaf] = evaluator.cache[leaf][2]

    def oracle(self, seed, cost='cached'):
        return FeatureOracle(self, seed, cost)


class FeatureOracle:
    def __init__(self, task, seed, cost):
        self.np, self.graph = task.np, task.graph
        self.xtrain, self.ytrain = task.xtrain, task.ytrain
        self.xvalid, self.yvalid = task.xvalid, task.yvalid
        self.features, self.offset, self.penalty = task.features, task.offset, task.penalty
        self.rng = {v: random.Random((seed+1)*1000003+(v+1)*9176)
                    for v in self.graph.leaves}
        self.cache = {}; self.cost = cost; self.fits = 0; self.operations = 0
        self.classes = self.np.unique(self.ytrain)

    def fit(self, leaf):
        np = self.np
        mask = leaf-self.offset
        cols = [i for i in range(self.features) if mask & (1 << i)]
        factor = 1-self.penalty*len(cols)/self.features
        if cols:
            x = self.xtrain[:, cols]
            center, scale = x.mean(axis=0), x.std(axis=0)
            scale = np.where(scale == 0, 1., scale)
            x = (x-center)/scale
            centroids = np.array([x[self.ytrain == c].mean(axis=0) for c in self.classes])
            z = (self.xvalid[:, cols]-center)/scale
            predictions = self.classes[((z[:, None, :]-centroids[None, :, :])**2).sum(axis=2).argmin(axis=1)]
            self.operations += 10*len(x)*len(cols)+5*len(z)*len(cols)*len(self.classes)
        else:
            counts = [(self.ytrain == c).sum() for c in self.classes]
            predictions = np.full(len(self.yvalid), self.classes[np.argmax(counts)])
            self.operations += len(self.ytrain)*len(self.classes)+len(self.yvalid)
        correct = predictions == self.yvalid
        self.cache[leaf] = correct, factor, float(correct.mean()*factor)
        self.fits += 1

    def sample(self, leaf):
        if leaf not in self.cache or self.cost == 'refit':
            self.fit(leaf)
        correct, factor, _ = self.cache[leaf]
        self.operations += 3
        return float(correct[self.rng[leaf].randrange(len(correct))])*factor


def task_spec(name, split_seed):
    if name in ('iris', 'wine'):
        return FeatureTask(name, split_seed)
    if name == 'fanout':
        return shared_fanout(64)
    raise ValueError(name)


class SearchSession:
    def __init__(self, graph, oracle, method, policy='uct', epsilon=.15, delta=.05):
        if method == 'flat' and policy != 'uct':
            raise ValueError('The flat control cannot supply local policy queries')
        self.graph, self.oracle, self.policy = graph, oracle, policy
        self.epsilon, self.delta = epsilon, delta
        self.work = UCTWork()
        self.bounds = make_backend(graph, self.work, method)
        self.evidence = CanonicalIntervals(graph, self.work, delta=delta)
        self.uct = TranspositionUCT(graph) if policy == 'uct' else None
        self.visits = [0]*len(graph)
        self.best_leaf = graph.leaves[0]; self.best_lower = 0.
        self.calls = 0; self.certified = False; self.last = None
        # Parent routes make sparse forced coverage possible without a terminal
        # oracle shortcut. Every 2^k-th round cycles through canonical leaves.
        self.parent = [-1]*len(graph); self.force_index = 0
        for v in graph.order:
            for c in graph.children[v]:
                if self.parent[c] == -1: self.parent[c] = v
        self.work.initialization += 2*len(graph)+sum(map(len, graph.children))

    @property
    def total_work(self):
        # UCT and evidence both count the same oracle invocation; count it once.
        return (self.work.total + (self.uct.work.total-self.uct.work.oracle_calls if self.uct else 0)
                + getattr(self.oracle, 'operations', 0))

    def _optimistic_path(self):
        t = self.calls+1
        if t & (t-1) == 0:
            leaf = self.graph.leaves[self.force_index % len(self.graph.leaves)]
            self.force_index += 1; path = [leaf]
            while path[-1] != self.graph.root: path.append(self.parent[path[-1]])
            path.reverse(); self.work.edge_reads += len(path)
            return path
        path = [self.graph.root]
        while self.graph.children[path[-1]]:
            row = self.graph.children[path[-1]]
            pairs = [self.bounds.query(c) for c in row]
            # Optimism, then fewer canonical visits, then fixed action order.
            a = max(range(len(row)), key=lambda i: (pairs[i][3], -self.visits[row[i]], -i))
            self.work.query_reads += 3*len(row)
            path.append(row[a]); self.work.edge_reads += 1
        return path

    def step(self):
        if self.certified or self.evidence.conflict: return None
        if self.uct:
            path, reward = self.uct.step(self.oracle)
        else:
            path = self._optimistic_path(); reward = self.oracle.sample(path[-1])
        leaf = path[-1]; self.calls += 1
        for v in path: self.visits[v] += 1
        self.work.statistic_writes += len(path)
        pair = self.evidence.observe(leaf, reward)
        if pair is not None:
            self.bounds.publish(leaf, *pair)
            if pair[0] > self.best_lower:
                self.best_lower, self.best_leaf = pair[0], leaf
            self.work.query_reads += 1; self.work.statistic_writes += 2
        self.last = self.bounds.query(self.graph.root)
        self.certified = not self.evidence.conflict and self.last[3]-self.best_lower <= self.epsilon
        return tuple(path), reward, self.last[2:], self.best_leaf, self.certified
