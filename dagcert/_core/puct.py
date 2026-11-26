"""Fixed-prior Root-PUCT and Noisy Recursive-PUCT policies on rooted DAGs.

Implements:
1. RootPUCT (Section 4.1 / Appendix E, Eq. (root-puct-main), (v2puct)):
   1 initial observation per root action, then at integer time t >= K selects
   argmax_i [ hat_mu_i(t) + lambda_i * sqrt(t) / (1 + n_i(t)) ] with canonical
   lowest-action-ID tie-breaking, and traverses a fixed deterministic or local-PUCT
   downstream path on the unmodified sampling DAG.
2. RecursivePUCT (Section 4.2 / Appendix F, Eq. (recursive-puct-main), (v35puct)):
   Shared transposition visit count n = sum_e N_{v,e}(n) >= 0 at every internal
   vertex v, selecting argmax_e [ Q_{v,e}(n) + lambda_{v,e} * sqrt(n) / (1 + N_{v,e}(n)) ]
   with Q_{v,e} in [0, 1] maintained as the running average of backed-up bounded
   terminal rewards along traversed edges.
3. CertifiedSearchSession:
   Unified trajectory-coupled runner pairing TA-UCT, Root-PUCT, or Recursive-PUCT
   with any marginal, decision-selective, or exact-regret monitor.
"""
from __future__ import annotations

import math

from .certified_uct import IndexedMaxHeap, TranspositionUCT, UCTWork
from .graph import DAG
from .v2_monitors import (
    ChargedDualCovers,
    DirectGraphRegretMonitor,
    FactorizedRegretMonitor,
    MarginalGraphMonitor,
    NestedDyadicCovers,
)


def make_priors(graph: DAG, mode: str = "uniform", means: dict[int, float] | None = None,
                c_puct: float = 2.0) -> list[list[float]]:
    """Construct strictly positive edge weights lambda_{v,e} = c_v * p_{v,e} > 0.

    Modes:
    - 'uniform': p_{v,e} = 1 / |E(v)| at every nonterminal vertex v (scaled by c_puct;
      if mode == 'unit_root', lambda_{v,e} = 1.0 as in Appendix E's three-arm theorem).
    - 'unit_lambda': lambda_{v,e} = 1.0 identically (equivalent to p_e = 1/K, c_v = K).
    - 'informative': concentrates 60% prior mass on the highest-true-value outgoing edge
      at each vertex and distributes 40% uniformly across remaining edges (strictly > 0).
      Used exclusively as a prespecified synthetic prior-sensitivity condition; means
      are never passed into the search/monitor algorithms themselves.
    - 'misleading': concentrates 70% prior mass on the lowest-true-value (or largest-fanout
      dominated) outgoing edge and distributes 30% uniformly across remaining edges
      (strictly > 0), testing whether selective pruning survives adversarial prior traffic.
    """
    if mode not in ("uniform", "unit_lambda", "informative", "misleading"):
        raise ValueError(f"Unknown prior mode: {mode}")
    values = graph.optimal_values(means) if means is not None and mode in ("informative", "misleading") else None
    lambdas: list[list[float]] = []
    for v, row in enumerate(graph.children):
        deg = len(row)
        if deg == 0:
            lambdas.append([])
        elif deg == 1:
            lambdas.append([1.0 if mode == "unit_lambda" else c_puct])
        elif mode == "unit_lambda":
            lambdas.append([1.0] * deg)
        elif mode == "uniform":
            lambdas.append([c_puct / deg] * deg)
        else:
            assert values is not None, f"Prior mode '{mode}' requires benchmark means to define synthetic prior"
            child_vals = [values[c] for c in row]
            if mode == "informative":
                target = max(range(deg), key=lambda a: (child_vals[a], -a))
                fav_mass = 0.60
            else:
                # Favor the worst-value child (breaking ties toward larger subtree out-degree).
                target = min(range(deg), key=lambda a: (child_vals[a], -len(graph.children[row[a]]), a))
                fav_mass = 0.70
            rem_mass = (1.0 - fav_mass) / (deg - 1)
            probs = [fav_mass if a == target else rem_mass for a in range(deg)]
            lambdas.append([c_puct * p for p in probs])
    return lambdas


class RootPUCT:
    """Exact fixed-prior Root-PUCT policy (Section 4.1 / Appendix E, Eq. (v2puct))."""

    def __init__(self, graph: DAG, lambdas: list[list[float]] | None = None,
                 c_puct: float = 3.0, downstream: str = "fixed_first"):
        if downstream not in ("fixed_first", "local_puct"):
            raise ValueError(f"Unknown downstream traversal mode: {downstream}")
        self.graph = graph
        self.downstream = downstream
        self.work = UCTWork()
        if lambdas is None:
            lambdas = make_priors(graph, "uniform", c_puct=c_puct)
        self.lambdas = [list(row) for row in lambdas]
        for row in self.lambdas:
            if any(not math.isfinite(x) or x <= 0.0 for x in row):
                raise ValueError("All PUCT prior weights lambda_{v,e} must be finite and > 0")

        self.counts = [[0] * len(row) for row in graph.children]
        self.means = [[0.0] * len(row) for row in graph.children]
        self.visits = [0] * len(graph)
        self.calls = 0
        edges = sum(map(len, graph.children))
        self.work.initialization += 4 * len(graph) + 3 * edges

        root_deg = len(graph.children[graph.root])
        self.recommendation = IndexedMaxHeap([-math.inf] * root_deg, self.work) if root_deg else None
        self.most_visited = IndexedMaxHeap([0] * root_deg, self.work) if root_deg else None

    def _select_root(self) -> int:
        root = self.graph.root
        counts = self.counts[root]
        k = len(counts)
        if self.calls < k:
            self.work.edge_reads += 1
            return self.calls
        sqrt_t = math.sqrt(self.calls)
        means = self.means[root]
        lams = self.lambdas[root]
        best_a = 0
        best_score = -math.inf
        for a in range(k):
            self.work.edge_reads += 1
            self.work.score_evaluations += 1
            score = means[a] + lams[a] * sqrt_t / (1 + counts[a])
            if score > best_score:
                best_score = score
                best_a = a
        return best_a

    def _select_internal(self, node: int) -> int:
        deg = len(self.counts[node])
        if deg == 1 or self.downstream == "fixed_first":
            self.work.edge_reads += 1
            return 0
        n = self.visits[node]
        sqrt_n = math.sqrt(n)
        means = self.means[node]
        counts = self.counts[node]
        lams = self.lambdas[node]
        best_a = 0
        best_score = -math.inf
        for a in range(deg):
            self.work.edge_reads += 1
            self.work.score_evaluations += 1
            score = means[a] + lams[a] * sqrt_n / (1 + counts[a])
            if score > best_score:
                best_score = score
                best_a = a
        return best_a

    def step(self, oracle) -> tuple[tuple[int, ...], float]:
        node = self.graph.root
        edges: list[tuple[int, int]] = []
        path = [node]
        if self.graph.children[node]:
            a0 = self._select_root()
            edges.append((node, a0))
            node = self.graph.children[node][a0]
            path.append(node)
            while self.graph.children[node]:
                a = self._select_internal(node)
                edges.append((node, a))
                node = self.graph.children[node][a]
                path.append(node)

        reward = oracle.sample(node)
        if not math.isfinite(reward) or not 0.0 <= reward <= 1.0:
            raise ValueError("Rewards must lie in [0, 1]")
        self.calls += 1
        self.work.oracle_calls += 1
        self.visits[node] += 1
        self.work.statistic_writes += 1

        for parent, action in reversed(edges):
            self.visits[parent] += 1
            self.counts[parent][action] += 1
            cnt = self.counts[parent][action]
            self.means[parent][action] += (reward - self.means[parent][action]) / cnt
            self.work.statistic_writes += 3

        if edges and self.recommendation is not None:
            a0 = edges[0][1]
            self.recommendation.update(a0, self.means[self.graph.root][a0])
            self.most_visited.update(a0, self.counts[self.graph.root][a0])
        return tuple(path), reward

    def recommend_action(self, visits: bool = False) -> int:
        self.work.query_reads += 1
        if self.recommendation is None:
            return -1
        return self.most_visited.top if visits else self.recommendation.top


class RecursivePUCT:
    """Exact fixed-positive-prior Recursive-PUCT on a rooted DAG (Section 4.2 / Appendix F).

    At vertex v with local prior visit count n = sum_e N_{v,e}(n) >= 0, selects
    argmax_e [ Q_{v,e}(n) + lambda_{v,e} * sqrt(n) / (1 + N_{v,e}(n)) ] with canonical
    lowest-action-ID tie-breaking and Q_{v,e}(0) = q_init in [0, 1].
    """

    def __init__(self, graph: DAG, lambdas: list[list[float]] | None = None,
                 c_puct: float = 2.0, q_init: float = 0.5):
        if not 0.0 <= q_init <= 1.0:
            raise ValueError("Initial Q value must lie in [0, 1]")
        self.graph = graph
        self.q_init = q_init
        self.work = UCTWork()
        if lambdas is None:
            lambdas = make_priors(graph, "uniform", c_puct=c_puct)
        self.lambdas = [list(row) for row in lambdas]
        for row in self.lambdas:
            if any(not math.isfinite(x) or x <= 0.0 for x in row):
                raise ValueError("All PUCT prior weights lambda_{v,e} must be finite and > 0")

        self.counts = [[0] * len(row) for row in graph.children]
        self.q_values = [[q_init] * len(row) for row in graph.children]
        self.visits = [0] * len(graph)
        self.calls = 0
        edges = sum(map(len, graph.children))
        self.work.initialization += 4 * len(graph) + 3 * edges

        root_deg = len(graph.children[graph.root])
        self.recommendation = IndexedMaxHeap([-math.inf] * root_deg, self.work) if root_deg else None
        self.most_visited = IndexedMaxHeap([0] * root_deg, self.work) if root_deg else None

    def _select(self, node: int) -> int:
        deg = len(self.counts[node])
        if deg == 1:
            self.work.edge_reads += 1
            return 0
        n = self.visits[node]
        sqrt_n = math.sqrt(n)
        qs = self.q_values[node]
        cnts = self.counts[node]
        lams = self.lambdas[node]
        best_a = 0
        best_score = -math.inf
        for a in range(deg):
            self.work.edge_reads += 1
            self.work.score_evaluations += 1
            score = qs[a] + lams[a] * sqrt_n / (1 + cnts[a])
            if score > best_score:
                best_score = score
                best_a = a
        return best_a

    def step(self, oracle) -> tuple[tuple[int, ...], float]:
        node = self.graph.root
        edges: list[tuple[int, int]] = []
        path = [node]
        while self.graph.children[node]:
            a = self._select(node)
            edges.append((node, a))
            node = self.graph.children[node][a]
            path.append(node)

        reward = oracle.sample(node)
        if not math.isfinite(reward) or not 0.0 <= reward <= 1.0:
            raise ValueError("Rewards must lie in [0, 1]")
        self.calls += 1
        self.work.oracle_calls += 1
        self.visits[node] += 1
        self.work.statistic_writes += 1

        for parent, action in reversed(edges):
            self.visits[parent] += 1
            self.counts[parent][action] += 1
            cnt = self.counts[parent][action]
            if cnt == 1:
                self.q_values[parent][action] = reward
            else:
                self.q_values[parent][action] += (reward - self.q_values[parent][action]) / cnt
            self.work.statistic_writes += 3

        if edges and self.recommendation is not None:
            a0 = edges[0][1]
            self.recommendation.update(a0, self.q_values[self.graph.root][a0])
            self.most_visited.update(a0, self.counts[self.graph.root][a0])
        return tuple(path), reward

    def recommend_action(self, visits: bool = False) -> int:
        self.work.query_reads += 1
        if self.recommendation is None:
            return -1
        return self.most_visited.top if visits else self.recommendation.top


def build_monitor(graph: DAG, method: str, delta: float = 0.05,
                  schedule: str = "box", effective_m: int | None = None):
    """Factory for all v2 marginal, decision-selective, and exact-regret monitors."""
    if method == "graph-eager":
        return MarginalGraphMonitor(graph, mode="eager", delta=delta, schedule=schedule,
                                    simplify=False, effective_m=effective_m)
    if method == "quotient-eager":
        return MarginalGraphMonitor(graph, mode="eager", delta=delta, schedule=schedule,
                                    simplify=True, effective_m=effective_m)
    if method == "protected-selective":
        return MarginalGraphMonitor(graph, mode="protected", delta=delta, schedule=schedule,
                                    simplify=False, effective_m=effective_m)
    if method == "quotient-protected":
        return MarginalGraphMonitor(graph, mode="protected", delta=delta, schedule=schedule,
                                    simplify=True, effective_m=effective_m)
    if method == "decision-selective":
        return MarginalGraphMonitor(graph, mode="decision", delta=delta, schedule=schedule,
                                    simplify=False, effective_m=effective_m)
    if method == "quotient-decision":
        return MarginalGraphMonitor(graph, mode="decision", delta=delta, schedule=schedule,
                                    simplify=True, effective_m=effective_m)
    if method == "dyadic-covers":
        return NestedDyadicCovers(graph, delta=delta, schedule=schedule, layout="best",
                                  effective_m=effective_m)
    if method == "dual-covers":
        return ChargedDualCovers(graph, delta=delta, schedule=schedule, layout="best",
                                 effective_m=effective_m)
    if method == "dual-covers-id":
        return ChargedDualCovers(graph, delta=delta, schedule=schedule, layout="id",
                                 effective_m=effective_m)
    if method == "factorized-regret":
        return FactorizedRegretMonitor(graph, delta=delta, schedule=schedule, mode="protected",
                                       effective_m=effective_m)
    if method == "factorized-eager":
        return FactorizedRegretMonitor(graph, delta=delta, schedule=schedule, mode="eager",
                                       effective_m=effective_m)
    if method == "direct-graph-regret":
        return DirectGraphRegretMonitor(graph, delta=delta, schedule=schedule, mode="protected",
                                        effective_m=effective_m)
    raise ValueError(f"Unknown monitor method: {method}")


class CertifiedSearchSession:
    """Unified certified search pairing any DAG bandit policy with any confidence monitor."""

    def __init__(self, problem, seed: int, policy_kind: str, monitor_method: str,
                 epsilon: float, delta: float = 0.05, c_explore: float = 2.0,
                 prior_mode: str = "uniform", q_cert: int = 1,
                 schedule: str = "box", downstream: str = "fixed_first",
                 effective_m: int | None = None):
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.q_cert = q_cert
        self.oracle = problem.oracle(seed)

        if policy_kind == "uct":
            self.policy = TranspositionUCT(self.graph, exploration=c_explore, lazy=True)
        elif policy_kind == "root_puct":
            lambdas = make_priors(self.graph, prior_mode, means=problem.means, c_puct=c_explore)
            self.policy = RootPUCT(self.graph, lambdas=lambdas, c_puct=c_explore, downstream=downstream)
        elif policy_kind == "recursive_puct":
            lambdas = make_priors(self.graph, prior_mode, means=problem.means, c_puct=c_explore)
            self.policy = RecursivePUCT(self.graph, lambdas=lambdas, c_puct=c_explore)
        else:
            raise ValueError(f"Unknown policy_kind: {policy_kind}")

        self.monitor = build_monitor(self.graph, monitor_method, delta=delta,
                                     schedule=schedule, effective_m=effective_m)
        self.query = self.monitor.query()
        self.certified = (not self.monitor.evidence.conflict) and (self.query[1] <= epsilon)
        self.action = self.query[0] if self.certified else self.policy.recommend_action()
        self.first_cut: int | None = None
        self.first_root_cut: int | None = None
        self._dirty_since_query = False
        self.monitor.work.initialization += 2 * len(self.graph.leaves)

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.monitor.evidence.conflict:
            raise RuntimeError("CertifiedSearchSession already terminated")
        path, reward = self.policy.step(self.oracle)
        leaf = path[-1]
        if self.monitor.step(leaf, reward):
            self._dirty_since_query = True
        self.monitor.work.query_reads += 2
        if self.policy.calls % self.q_cert == 0 and self._dirty_since_query:
            self.query = self.monitor.query()
            self._dirty_since_query = False
        self.certified = (not self.monitor.evidence.conflict) and (self.query[1] <= self.epsilon)
        self.action = self.query[0] if self.certified else self.policy.recommend_action()
        b = getattr(self.monitor, "bounds", None)
        if b is not None:
            if self.first_cut is None and b.retired > 0:
                self.first_cut = self.policy.calls
            if self.first_root_cut is None and b.retired_root_actions > 0:
                self.first_root_cut = self.policy.calls
        return path, reward

    @property
    def calls(self) -> int:
        return self.policy.calls

    @property
    def work(self) -> int:
        # Avoid double-counting the single physical oracle call per step.
        return (self.policy.work.total + self.monitor.work.total - self.policy.calls
                + getattr(self.oracle, "operations", 0))
