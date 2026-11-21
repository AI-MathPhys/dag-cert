"""Prospectively frozen matched-work test of clearing admission and abort."""
import argparse
from collections import defaultdict
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import random
import time

from dag_mcts.graph import DAG, Problem
from paper.escrow_clearing import GuardedSearch, METHODS
from paper.frontier_sampling import Search
from paper.frontier_sampling_benchmark import WB
from paper.relevance_frontier_benchmark import make_problem, digest

SEEDS = tuple(range(162101, 162107))
SPECS = (('lattice', 0), ('thinned', 0), ('thinned', 1), ('scrambled', 1),
         ('fragmented', 0), ('fragmented', 1), ('window', 1), ('flat', 0))


def config(family, level, price):
    return dict(id=f'{family}-{level}-c{price}', family=family, features=8 if family=='scrambled' else 6+level,
                M=(128, 256)[level], A=(64, 256)[level], epsilon=(.1,.05)[level],
                delta=(.05,.01)[level], K=(160,64000)[level], oracle_cost=price,
                max_work=102400000, max_observations=65536, cap=12)


def problem(c, seed):
    if c['family'] not in ('thinned','scrambled'):
        return make_problem(c, seed)
    # Retain at least one incoming insertion edge per nonempty subset.
    # Random inconsequential-feature penalties and useful feature identities
    # vary the stationary landscape independently of the observation tape.
    rng = random.Random(seed + 610870)
    k = c['features']
    count = 1 << k
    rows = [[] for _ in range(count)]
    for subset in range(1, count):
        parents = [subset ^ (1 << j) for j in range(k) if subset & (1 << j)]
        forced = rng.choice(parents)
        for parent in parents:
            if parent == forced or rng.random() < .65:
                rows[parent].append(subset)
    useful = sum(1 << j for j in rng.sample(range(k), 3))
    penalties = [rng.uniform(.025,.055) for _ in range(k)]
    means = {}
    terminals = list(range(count,2*count))
    if c['family']=='scrambled':
        rng.shuffle(terminals)
    for subset in range(count):
        rows[subset].append(terminals[subset])
        n = (subset & useful).bit_count()
        cost = sum(penalties[j] for j in range(k) if subset & (1 << j) and not useful & (1 << j))
        means[terminals[subset]] = max(.01, .20 + .12*n + .24*(n==3) - cost + rng.uniform(-.01,.01))
    return Problem(c['id'], DAG(rows + [() for _ in range(count)]), means)


def measure(c, seed, method):
    p = problem(c, seed)
    g = p.graph
    topology = hashlib.sha256(repr(g.children).encode()).hexdigest()
    environment = hashlib.sha256(repr((g.children, sorted(p.means.items()), seed)).encode()).hexdigest()
    truth = g.optimal_values(p.means)
    start = time.perf_counter()
    if method in ('old_clear32','range32'):
        engine = 'frontier_clear32' if method == 'old_clear32' else 'range_lucb32'
        search = Search(p,c,seed,engine)
    else:
        search = GuardedSearch(p,c,seed,method)
    point = search.query()
    seconds = time.perf_counter() - start
    ordinary = hashlib.sha256()
    ordinary.update(repr(point).encode())
    # Keep an ordinary-only transcript: tentative observations/queries never
    # enter it. On failed interventions it must exactly match Range to decision.
    while not point[1] and search.w.total < c['max_work'] and search.w.oracle_calls < c['max_observations']:
        remaining = c['max_observations'] - search.w.oracle_calls
        old_q = search.idx.q
        old_logical = search.N
        start = time.perf_counter()
        obs,point = search.step(remaining)
        seconds += time.perf_counter() - start
        if search.idx.q != old_q and search.N > old_logical:
            ordinary.update(repr((obs, point)).encode())
    # Capped attempts must also pay outstanding rollback/disposal.
    if isinstance(search,GuardedSearch) and search.trial is not None:
        start = time.perf_counter()
        search.close('abort_cap')
        seconds += time.perf_counter()-start
    regret = truth[0] - truth[g.children[0][point[0]]]
    assert not point[1] or regret <= c['epsilon']+1e-12
    meta = None
    if isinstance(search,GuardedSearch):
        meta = dict(search.meta, monitor=search.monitor_cost, pilot=search.pilot_cost)
    return dict(case=c['id'], family=c['family'], seed=seed, method=method,
                topology=topology, environment=environment, work=search.w.total,
                certified=point[1] and search.w.total<=c['max_work'],
                regret=regret, action=point[0], physical=search.w.oracle_calls,
                logical=search.N, seconds=seconds, queries=search.idx.q,
                fields=asdict(search.w), ordinary=ordinary.hexdigest(), meta=meta,
                old=dict(search.controller) if method=='old_clear32' else None)


def sources():
    files = ('paper/escrow_policy_protocol.txt','paper/escrow_benchmark.py','paper/escrow_clearing.py',
             'paper/frontier_sampling.py','paper/frontier_sampling_benchmark.py',
             'paper/relevance_frontier.py','paper/relevance_frontier_benchmark.py',
             'paper/uniform_selection.py','paper/sampling_confidence_allcount.py',
             'dag_mcts/retired_bounds.py','dag_mcts/graph.py','dag_mcts/certified_uct.py')
    return {f:digest(f) for f in files}


def run(out):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    configurations = [config(f,l,p) for f,l in SPECS for p in (1,64)]
    manifest = dict(completed=False, sources=sources(), methods=METHODS, seeds=SEEDS,
                    configs=configurations, work_budgets=WB, timing_repetitions=1)
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2))
    jobs = [(c,z,m) for c in configurations for z in SEEDS for m in METHODS]
    random.Random(1620099).shuffle(jobs)
    with (out/'runs.jsonl').open('w') as stream:
        for i,(c,z,m) in enumerate(jobs,1):
            result = measure(c,z,m)
            stream.write(json.dumps(result,separators=(',',':'))+'\n')
            stream.flush()
            if i % 20 == 0:
                print(i,'/',len(jobs),flush=True)
    assert sources()==manifest['sources']
    manifest.update(completed=True,runs=len(jobs),outcome_hash=digest(out/'runs.jsonl'))
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',required=True)
    run(ap.parse_args().out)
