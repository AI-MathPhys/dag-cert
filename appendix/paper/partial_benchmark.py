"""Fresh paired DAG cohort for partial admission and abort decisions."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import time

from paper import escrow_benchmark as prior
from paper.partial_clearing import PartialSearch
from paper.escrow_clearing import GuardedSearch
from paper.frontier_sampling import Search
from dag_mcts.graph import Problem

METHODS = ('range32','old_clear32','guarded','partial','full_price','plain_abort')
SEEDS = tuple(range(173101,173109))
SETTINGS = prior.SPECS + (('fragmented_sparse',1), ('fragmented_dense',1),
                          ('fragmented_shoulder',1))


def config(family,level,price):
    c = prior.config(family,level,price)
    if family in ('fragmented_sparse','fragmented_dense'):
        c['family'] = 'fragmented'
        c['density'] = .25 if family=='fragmented_sparse' else .75
    if family=='fragmented_shoulder':
        c['family'] = 'fragmented'
        c['shoulder'] = True
    return c


def measure(c,seed,method):
    # Independent construction seeds for the new density/shoulder families.
    # The per-leaf reward tape and solver RNG still use the declared seed.
    offsets={'fragmented_sparse':21000,'fragmented_dense':31000,'fragmented_shoulder':41000}
    graph_seed=seed+offsets.get(c['id'].split('-')[0],0)
    problem = prior.problem(c,graph_seed)
    if c.get('shoulder'):
        rng = random.Random(graph_seed+303)
        means = dict(problem.means)
        for leaf in rng.sample([x for x,v in means.items() if v<.7],8):
            means[leaf] = rng.uniform(.49,.64)
        problem = Problem(c['id'],problem.graph,means)
    g = problem.graph
    truth = g.optimal_values(problem.means)
    environment = hashlib.sha256(repr((g.children,sorted(problem.means.items()),seed)).encode()).hexdigest()
    topo = hashlib.sha256(repr(g.children).encode()).hexdigest()
    start = time.perf_counter()
    if method in ('range32','old_clear32'):
        engine = 'range_lucb32' if method=='range32' else 'frontier_clear32'
        search = Search(problem,c,seed,engine)
    elif method=='guarded':
        search = GuardedSearch(problem,c,seed)
    else:
        search = PartialSearch(problem,c,seed,method)
    point = search.query()
    elapsed = time.perf_counter()-start
    chain = hashlib.sha256(repr(point).encode())
    while (not point[1] and search.w.total<c['max_work'] and
           search.w.oracle_calls<c['max_observations']):
        left = c['max_observations']-search.w.oracle_calls
        previous = search.idx.q,search.N
        start = time.perf_counter()
        obs,point = search.step(left)
        elapsed += time.perf_counter()-start
        if previous[0]!=search.idx.q and search.N>previous[1]:
            chain.update(repr((obs,point)).encode())
    if isinstance(search, GuardedSearch) and search.trial is not None:
        start=time.perf_counter()
        search.close('abort_cap')
        elapsed+=time.perf_counter()-start
    regret=truth[0]-truth[g.children[0][point[0]]]
    assert not point[1] or regret<=c['epsilon']+1e-12
    meta=None
    if isinstance(search,GuardedSearch):
        meta=dict(search.meta,monitor=search.monitor_cost,pilot=search.pilot_cost)
    return dict(case=c['id'],seed=seed,method=method,environment=environment,topology=topo,
                work=search.w.total,seconds=elapsed,physical=search.w.oracle_calls,logical=search.N,
                certified=bool(point[1] and search.w.total<=c['max_work']),action=point[0],
                regret=regret,queries=search.idx.q,ordinary=chain.hexdigest(),meta=meta,
                old=dict(search.controller) if method=='old_clear32' else None)


def sources():
    files = (*prior.sources(), 'paper/partial_clearing.py','paper/partial_benchmark.py',
             'paper/partial_protocol.txt','tests/test_partial_clearing.py')
    return {p:prior.digest(p) for p in files}


def run(out):
    out=Path(out)
    out.mkdir(parents=True,exist_ok=False)
    cases=[config(f,l,p) for f,l in SETTINGS for p in (1,64)]
    manifest=dict(completed=False,sources=sources(),settings=cases,seeds=SEEDS,methods=METHODS,
                  budgets=prior.WB,timing_repetitions=1)
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2))
    jobs=[(c,z,m) for c in cases for z in SEEDS for m in METHODS]
    random.Random(1730077).shuffle(jobs)
    with (out/'runs.jsonl').open('w') as stream:
        for i,(c,z,m) in enumerate(jobs,1):
            stream.write(json.dumps(measure(c,z,m),separators=(',',':'))+'\n')
            stream.flush()
            if i%50==0:
                print(i,'/',len(jobs),flush=True)
    assert sources()==manifest['sources']
    manifest.update(completed=True,runs=len(jobs),outcome_hash=prior.digest(out/'runs.jsonl'))
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',required=True)
    run(parser.parse_args().out)
