"""Frozen, cold-start complete-decision study of paid relevance frontiers."""
import argparse
from dataclasses import asdict
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import sys
import time

from dag_mcts.graph import DAG, Problem, feature_lattice
from dag_mcts.demand_benchmark import retained_bytes
from paper.relevance_frontier import Search, METHODS

WORK_BUDGETS = (100000, 400000, 1600000, 6400000, 25600000, 102400000)
TIME_BUDGETS = (.1, .5, 2., 10., 30., 120.)


def make_problem(c, seed):
    if c['family'] == 'lattice': return feature_lattice(c['features'], noisy=True)
    rng = random.Random(seed+830018); M = c['M']; A = c['A']
    # Shared balanced binary sub-DAG. Canonical leaf IDs are terminal order.
    rows = [tuple(range(1, A+1))]+[() for _ in range(A)]
    blocks = {}
    def build(lo, hi):
        v = len(rows); rows.append(()); blocks[(lo, hi)] = v
        if hi-lo > 1:
            mid = (lo+hi)//2; rows[v] = (build(lo, mid), build(mid, hi))
        return v
    build(0, M)
    elite = sorted(rng.sample(range(M), 4)); masks = []
    for a in range(A):
        if c['family'] == 'window':
            start = rng.randrange(M); mask = {(start+j) % M for j in range(M//2)}
        else:
            mask = {j for j in range(M) if rng.random() < c.get('density', .5)}
            if c['family'] == 'fragmented':
                mask.difference_update(elite); mask.update(rng.sample(elite, 2))
        masks.append(mask)
    # Guarantee full terminal reachability without creating a universal action.
    covered = set().union(*masks)
    for j in set(range(M))-covered: masks[j % A].add(j)
    def cover(mask, lo, hi):
        count = sum(j in mask for j in range(lo, hi))
        if not count: return []
        if count == hi-lo: return [blocks[(lo, hi)]]
        mid = (lo+hi)//2; return cover(mask, lo, mid)+cover(mask, mid, hi)
    for a, mask in enumerate(masks): rows[a+1] = tuple(cover(mask, 0, M))
    # Remove unused segment-tree nodes; all methods receive identical input.
    seen = {0}; stack = [0]
    while stack:
        for v in rows[stack.pop()]:
            if v not in seen: seen.add(v); stack.append(v)
    ids = {v: i for i, v in enumerate(sorted(seen))}
    g = DAG([tuple(ids[x] for x in rows[v]) for v in sorted(seen)])
    leaf_by_rank = [ids[blocks[(j, j+1)]] for j in range(M)]
    if c['family'] == 'flat': vals = [.5+.02*rng.random() for _ in range(M)]
    else: vals = [.70 if j in elite else .05+.20*rng.random() for j in range(M)]
    return Problem(c['id'], g, dict(zip(leaf_by_rank, vals)))


def configurations(smoke=False):
    if smoke:
        return [dict(id='development', family='fragmented', M=32, A=12,
                     epsilon=.1, delta=.1, K=80, cadence=4, cap=12, slack=.025,
                     max_work=6400000, max_observations=40000)]
    cs = []
    for family in ('fragmented', 'window', 'flat', 'lattice'):
        for level in range(3):
            c = dict(id=f'{family}-{level}', family=family, M=(128,256,512)[level],
                     A=(64,256,1024)[level], features=6+level,
                     epsilon=(.10,.05,.05)[level], delta=(.05,.05,.01)[level],
                     K=(80,160,320)[level], cadence=4, cap=12, slack=.025,
                     max_work=102400000, max_observations=131072)
            cs.append(c)
    return cs


def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sources():
    paths = ['paper/relevance_frontier.py', 'paper/relevance_frontier_benchmark.py',
             'paper/relevance_frontier_protocol.txt', 'paper/uniform_selection.py',
             'paper/sampling_confidence_allcount.py', 'dag_mcts/graph.py',
             'dag_mcts/certified_uct.py', 'tests/test_relevance_frontier.py']
    return {p: digest(p) for p in paths}


def measure(c, seed, method, repetition):
    p = make_problem(c, seed); truth = p.graph.optimal_values(p.means)
    start = time.perf_counter(); s = Search(p, c, seed, method); point = s.query()
    elapsed = time.perf_counter()-start; initial_work = s.w.total
    initial_seconds = elapsed; chain = hashlib.sha256(); checkpoints = []
    work_points = {}; wall_points = {}; previous = None
    profile = []; queried = set(); dirty_queries = 0; last_revision = {}
    initial_memory = retained_bytes(s.idx, (p.graph, s.w))
    def checkpoint(obs):
        nonlocal previous, dirty_queries
        a, good = point[:2]; regret = truth[0]-truth[p.graph.children[0][a]]
        if good and regret > c['epsilon']+1e-12: raise AssertionError(('invalid', regret))
        chain.update(repr((obs,point)).encode())
        checkpoints.append(chain.hexdigest()); queried.add(a)
        if last_revision.get(a, -1) != s.idx.revision: dirty_queries += 1
        last_revision[a] = s.idx.revision
        current = dict(work=s.w.total, seconds=elapsed, observations=s.N,
                       certified=good, action=a, regret=regret)
        for b in WORK_BUDGETS:
            if str(b) not in work_points and s.w.total > b: work_points[str(b)] = previous
        for b in TIME_BUDGETS:
            if str(b) not in wall_points and elapsed > b: wall_points[str(b)] = previous
        previous = current
        profile.append([s.w.total,s.idx.stats['service_work'],a,s.idx.revision])
    checkpoint([])
    while not point[1] and s.w.total <= c['max_work'] and s.N < c['max_observations']:
        start = time.perf_counter(); obs, point = s.block(c['cadence'])
        elapsed += time.perf_counter()-start; checkpoint(obs)
    for b in WORK_BUDGETS:
        if str(b) not in work_points:
            work_points[str(b)] = previous if point[1] else dict(censored=True,last=previous)
    for b in TIME_BUDGETS:
        if str(b) not in wall_points:
            wall_points[str(b)] = previous if point[1] else dict(censored=True,last=previous)
    return dict(config=c['id'], seed=seed, method=method, repetition=repetition,
                certified=point[1], within_budget=point[1] and s.w.total<=c['max_work'],
                work=s.w.total, seconds=elapsed, observations=s.N, queries=s.idx.q,
                initial_work=initial_work, initial_seconds=initial_seconds,
                candidates=len(queried), dirty_queries=dirty_queries,
                work_points=work_points, wall_points=wall_points, last=previous,
                stats=s.idx.stats, episodes=s.idx.episodes, fields=asdict(s.w), profile=profile,
                nodes=len(p.graph), edges=sum(map(len,p.graph.children)), leaves=len(p.graph.leaves),
                max_intervals=max(map(len,s.idx.top.inside)),
                initial_index_bytes=initial_memory, index_bytes=retained_bytes(s.idx,(p.graph,s.w)),
                memory_bytes=retained_bytes(s,(p.graph,s.w)), prefixes=checkpoints)


def run(out, smoke=False):
    folder = Path(out); folder.mkdir(parents=True, exist_ok=False)
    cs = configurations(smoke); seeds = [141001] if smoke else [141101,141102]
    reps = 1 if smoke else 2
    manifest = dict(completed=False, smoke=smoke, configurations=cs, seeds=seeds,
                    repetitions=reps, methods=METHODS, sources=sources(),
                    work_budgets=WORK_BUDGETS, wall_budgets=TIME_BUDGETS,
                    environment=dict(python=sys.version, platform=platform.platform()))
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))
    jobs = [(c,seed,m,rep) for c in cs for seed in seeds for m in METHODS for rep in range(reps)]
    random.Random(202611012).shuffle(jobs); reference = {}; start = time.perf_counter()
    with (folder/'runs.jsonl').open('w') as stream:
        for k,(c,seed,m,rep) in enumerate(jobs,1):
            result = measure(c,seed,m,rep); key=(c['id'],seed)
            old = reference.get(key,[]); new=result['prefixes']; n=min(len(old),len(new))
            assert old[:n] == new[:n], ('trace mismatch',key,m,rep)
            if len(new)>len(old): reference[key]=new
            stream.write(json.dumps(result,separators=(',',':'))+'\n'); stream.flush()
            print(k,'/',len(jobs),c['id'],seed,m,rep,'done',result['within_budget'],
                  'N',result['observations'],'W',result['work'],'s',round(result['seconds'],3),
                  'hits',result['stats']['hits'],'elapsed',round(time.perf_counter()-start,1),flush=True)
    assert sources()==manifest['sources']
    manifest.update(completed=True,runs=len(jobs),output_sha256=digest(folder/'runs.jsonl'))
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))


if __name__ == '__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);ap.add_argument('--smoke',action='store_true')
    args=ap.parse_args();run(args.out,args.smoke)
