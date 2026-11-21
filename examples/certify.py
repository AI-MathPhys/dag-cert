"""Small noisy shared DAG: all four monitors follow the same UCT observations."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from dag_mcts.compiled_retirement import Search
from paper.uct_frontier_families import coded


def main():
    problem, epsilon = coded(4, 433101)
    methods = ('graph-eager', 'graph-live', 'cover-live', 'covers')
    searches = [Search(problem, 433101, method, epsilon) for method in methods]
    for _ in range(10000):
        observations = [search.step() for search in searches]
        assert all(x == observations[0] for x in observations)
        assert all(search.query == searches[0].query for search in searches)
        if searches[0].certified:
            assert all(search.certified for search in searches)
            break
    else:
        raise RuntimeError('Demonstration did not certify within its rollout cap')
    for method, search in zip(methods, searches):
        print(f'{method:12s} action={search.action} rollouts={search.uct.calls} work={search.work}')


if __name__ == '__main__':
    main()
