"""Routing-weighted Monte Carlo control with a provably slow exploration decay.

See paper/routing/main.tex. The ratio estimator is NOT finite-sample unbiased.
ESS is diagnostic only. This method computes the full sampled-leaf ancestor
closure, unlike the bounded extra work of sampled Bellman ancestor refreshes.
"""

import math
import random

from .search import Work, _ancestors


def routing_masses(graph, leaf, policy_row, work=None):
    """P_b(terminal leaf | start at s) for leaf and every strict ancestor.

    policy_row(s) returns a probability tuple aligned with graph.children[s].
    Its policy must stay frozen throughout this calculation. Nonancestors have
    mass zero, so they need no storage or statistic update. Topological ranks,
    rather than node IDs or path lengths, determine the recursion order.
    """
    if graph.children[leaf]:
        raise ValueError("Routing endpoint must be terminal")
    work = Work() if work is None else work
    ancestors = _ancestors(graph, leaf, work)
    masses = {leaf: 1.0}
    work.routing_stat_writes += 1
    for state in sorted(ancestors, key=graph.rank.__getitem__, reverse=True):
        row = policy_row(state)
        children = graph.children[state]
        if len(row) != len(children):
            raise ValueError("Policy row must match the child list")
        masses[state] = sum(probability * masses.get(child, 0.0)
                            for child, probability in zip(children, row))
        work.routing_edge_reads += len(children)
        work.routing_stat_writes += 1
    return masses


class RoutingMCTS:
    """Full routing SNIS updates under a frozen epsilon-greedy Markov policy.

    epsilon_t = epsilon0 * t**(-decay), with 0 < decay * H < 1 when H > 0.
    Default decay=1/(2H) ensures the martingale strong law used in the proof.
    A statistic update is not a visit. Rewards depend only on terminal state;
    transitions are known and deterministic, and intermediate rewards are zero.
    """

    def __init__(self, graph, epsilon0=0.5, decay=None, initial=0.5, seed=0):
        height = max(graph.depth)
        decay = 1.0 / (2 * max(1, height)) if decay is None else decay
        if not math.isfinite(epsilon0) or not 0 < epsilon0 <= 1:
            raise ValueError("epsilon0 must be finite and in (0, 1]")
        if not math.isfinite(decay) or decay <= 0 or (height and decay * height >= 1):
            raise ValueError("Need positive finite decay and decay * maximum_depth < 1")
        if not math.isfinite(initial) or not 0 <= initial <= 1:
            raise ValueError("Initial values must lie in [0, 1]")
        self.graph = graph
        self.epsilon0 = epsilon0
        self.decay = decay
        self.rng = random.Random(seed)
        self.round = 0
        self.values = [initial] * len(graph)
        self.weight_sum = [0.0] * len(graph)
        self.weighted_reward_sum = [0.0] * len(graph)
        self.weight_square_sum = [0.0] * len(graph)
        self.visits = [0] * len(graph)
        self.edge_counts = [[0] * len(row) for row in graph.children]
        self.work = Work()
        self.max_weight = 0.0

    @property
    def materialized_nodes(self):
        return len(self.graph)

    def epsilon(self, round_number):
        if round_number < 1:
            raise ValueError("Rounds start at one")
        return self.epsilon0 * round_number ** (-self.decay)

    def effective_sample_size(self, state):
        squares = self.weight_square_sum[state]
        return self.weight_sum[state] ** 2 / squares if squares else 0.0

    def step(self, oracle):
        self.round += 1
        epsilon = self.epsilon(self.round)
        graph = self.graph
        # No value mutation until ALL routing masses have been computed. Thus
        # lazy off-path policy rows use the same pre-rollout value snapshot.
        policy = {}
        greedy = {}

        def policy_row(state):
            if state not in policy:
                children = graph.children[state]
                action = max(range(len(children)), key=lambda i: self.values[children[i]])
                self.work.policy_edge_reads += len(children)
                greedy[state] = action
                row = [epsilon / len(children)] * len(children)
                row[action] += 1.0 - epsilon
                policy[state] = tuple(row)
            return policy[state]

        state = graph.root
        path = [state]
        while graph.children[state]:
            policy_row(state)
            action = (self.rng.randrange(len(graph.children[state]))
                      if self.rng.random() < epsilon else greedy[state])
            self.edge_counts[state][action] += 1
            self.work.traversal_count_writes += 1
            self.work.selection_edge_reads += 1
            state = graph.children[state][action]
            path.append(state)
        for visited in path:
            self.visits[visited] += 1
            self.work.traversal_count_writes += 1
        reward = oracle.sample(state)
        self.work.oracle_calls += 1
        masses = routing_masses(graph, state, policy_row, self.work)
        normalizer = masses[graph.root]
        if not normalizer > 0 or not math.isfinite(normalizer):
            raise ArithmeticError("Routing probability underflowed; rescale routing masses")
        for ancestor, mass in masses.items():
            weight = mass / normalizer
            self.weight_sum[ancestor] += weight
            self.weighted_reward_sum[ancestor] += weight * reward
            self.weight_square_sum[ancestor] += weight * weight
            self.values[ancestor] = (self.weighted_reward_sum[ancestor]
                                     / self.weight_sum[ancestor])
            self.max_weight = max(self.max_weight, weight)
            self.work.routing_stat_writes += 3
            self.work.value_writes += 1
        return tuple(path), reward

    def recommend(self):
        state = self.graph.root
        path = [state]
        while self.graph.children[state]:
            state = max(self.graph.children[state], key=self.values.__getitem__)
            path.append(state)
        return tuple(path)
