"""Small noisy shared DAG: all four trajectory-coupled UCT monitors follow identical observations."""
from __future__ import annotations

import random

from joint_root_cert import TrajectoryCoupledUCT
from joint_root_cert.graph import DAG, Problem


class _BoundedProblem(Problem):
    def oracle(self, seed: int):
        p = self

        class _Oracle:
            def __init__(self) -> None:
                self.rng = {v: random.Random((seed + 1) * 1000003 + v * 9176) for v in p.graph.leaves}

            def sample(self, j: int) -> float:
                return p.means[j] + 0.01 * (2.0 * self.rng[j].random() - 1.0)

        return _Oracle()


def make_coded_dag(k: int = 4, seed: int = 433101) -> tuple[Problem, float]:
    """Hadamard coordinate catalog DAG with shared terminal supports."""
    rows: list[tuple[int, ...]] = [()]
    grid: list[list[int]] = []
    for _ in range(k):
        grid.append(list(range(len(rows), len(rows) + k)))
        rows.extend([()] * k)
    groups: list[int] = []
    for cells in grid + list(map(list, zip(*grid))):
        groups.append(len(rows))
        rows.append(tuple(cells))
    actions: list[int] = []
    for axis in range(2):
        for a in range(1, k):
            for parity in (0, 1):
                actions.append(len(rows))
                rows.append(tuple(groups[axis * k + i] for i in range(k) if (a & i).bit_count() % 2 == parity))
    winner = len(rows)
    rows.append(())
    actions.append(winner)
    random.Random(seed).shuffle(actions)
    rows[0] = tuple(actions)
    means = {j: 0.02 for row in grid for j in row}
    means[winner] = 0.99
    return _BoundedProblem("coded coordinate catalog", DAG(rows), means), 0.20


def main() -> None:
    problem, epsilon = make_coded_dag(4, 433101)
    methods = ("graph-eager", "graph-live", "cover-live", "covers")
    searches = [TrajectoryCoupledUCT(problem, 433101, method, epsilon) for method in methods]
    for _ in range(10000):
        observations = [search.step() for search in searches]
        assert all(x == observations[0] for x in observations)
        assert all(search.query == searches[0].query for search in searches)
        if searches[0].certified:
            assert all(search.certified for search in searches)
            break
    else:
        raise RuntimeError("Demonstration did not certify within its rollout cap")
    for method, search in zip(methods, searches):
        print(f"{method:12s} action={search.action} rollouts={search.uct.calls} work={search.work}")


if __name__ == "__main__":
    main()
