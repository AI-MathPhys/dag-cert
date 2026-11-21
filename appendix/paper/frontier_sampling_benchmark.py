"""Factorial sampler/backend evaluation, with a batched range control."""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import platform
import random
import sys
import time

from dag_mcts.demand_benchmark import retained_bytes
from paper.frontier_sampling import Search,METHODS
from paper.relevance_frontier_benchmark import make_problem,digest

WB=(100000,400000,1600000,6400000,25600000,102400000)
TB=(.1,.5,2.,10.,30.,120.)


def configurations(smoke=False):
    if smoke:return [dict(id='development',family='fragmented',M=64,A=16,features=5,
                         epsilon=.1,delta=.1,K=160,cap=12,clear_multiplier=64,oracle_cost=1,
                         max_work=16000000,max_observations=65536)]
    cs=[]
    for family in ('fragmented','window','flat','lattice'):
        for level in range(2):
            for cost in (1,64):
                cs.append(dict(id=f'{family}-{level}-c{cost}',family=family,M=(128,256)[level],
                    A=(64,256)[level],features=6+level,epsilon=(.10,.05)[level],
                    delta=(.05,.01)[level],K=(160,64000)[level],cap=12,clear_multiplier=64,
                    oracle_cost=cost,max_work=102400000,max_observations=65536))
    return cs


def sources():
    paths=('paper/frontier_sampling.py','paper/frontier_sampling_benchmark.py',
           'paper/frontier_sampling_protocol.txt','tests/test_frontier_sampling.py',
           'paper/relevance_frontier.py','paper/relevance_frontier_benchmark.py',
           'paper/sampling_confidence_allcount.py','paper/uniform_selection.py',
           'dag_mcts/graph.py','dag_mcts/certified_uct.py')
    return {p:digest(p) for p in paths}


def measure(c,seed,method,rep):
    p=make_problem(c,seed);truth=p.graph.optimal_values(p.means)
    start=time.perf_counter();s=Search(p,c,seed,method);point=s.query();elapsed=time.perf_counter()-start
    setup_work=s.w.total;setup_seconds=elapsed;chain=hashlib.sha256();prefixes=[];profile=[]
    wp={};tp={};previous=None
    def checkpoint(obs):
        nonlocal previous
        a,good=point[:2];regret=truth[p.graph.root]-truth[p.graph.children[p.graph.root][a]]
        if good:assert regret<=c['epsilon']+1e-12,(c['id'],method,regret)
        fingerprint=point[:3] if good else point
        chain.update(repr((obs,fingerprint)).encode());prefixes.append(chain.hexdigest())
        profile.append([s.w.total,s.idx.stats['service_work'],s.N,a,good])
        current=dict(work=s.w.total,seconds=elapsed,N=s.N,certified=good,regret=regret,action=a)
        for b in WB:
            if str(b) not in wp and s.w.total>b:wp[str(b)]=previous
        for b in TB:
            if str(b) not in tp and elapsed>b:tp[str(b)]=previous
        previous=current
    checkpoint([])
    while not point[1] and s.w.total<=c['max_work'] and s.N<c['max_observations']:
        start=time.perf_counter();obs,point=s.step(c['max_observations']-s.N)
        elapsed+=time.perf_counter()-start;checkpoint(obs)
    for b in WB:
        if str(b) not in wp:wp[str(b)]=previous if point[1] else dict(censored=True,last=previous)
    for b in TB:
        if str(b) not in tp:tp[str(b)]=previous if point[1] else dict(censored=True,last=previous)
    assert s.w.oracle_calls==s.N
    return dict(config=c['id'],seed=seed,method=method,repetition=rep,certified=point[1],
        within_budget=point[1] and s.w.total<=c['max_work'],work=s.w.total,seconds=elapsed,
        observations=s.N,queries=s.idx.q,work_points=wp,wall_points=tp,last=previous,
        setup_work=setup_work,setup_seconds=setup_seconds,controller=s.controller,stats=s.idx.stats,
        fields=asdict(s.w),index_bytes=retained_bytes(s.idx,(p.graph,s.w)),
        memory_bytes=retained_bytes(s,(p.graph,s.w)),frontier_size=len(s.idx.F or []),
        max_intervals=max(map(len,s.idx.top.inside)),nodes=len(p.graph),edges=sum(map(len,p.graph.children)),
        leaves=len(p.graph.leaves),prefixes=prefixes,profile=profile)


def run(out,smoke=False):
    f=Path(out);f.mkdir(exist_ok=False,parents=True);cs=configurations(smoke)
    seeds=[151001] if smoke else [151101,151102];reps=1 if smoke else 2
    m=dict(completed=False,smoke=smoke,configurations=cs,seeds=seeds,repetitions=reps,
           methods=METHODS,sources=sources(),work_budgets=WB,wall_budgets=TB,
           environment=dict(python=sys.version,platform=platform.platform()))
    (f/'manifest.json').write_text(json.dumps(m,indent=2))
    jobs=[(c,z,b,r) for c in cs for z in seeds for b in METHODS for r in range(reps)]
    random.Random(202611014).shuffle(jobs);ref={};start=time.perf_counter()
    with (f/'runs.jsonl').open('w') as out:
        for i,(c,z,b,r) in enumerate(jobs,1):
            row=measure(c,z,b,r)
            group=('clearing32' if b.endswith('32') else 'clearing4') if '_clear' in b else 'batched' if b=='range_lucb32' else 'ordinary'
            key=(c['id'],z,group);old=ref.get(key);new=row['prefixes']
            if old is not None:
                n=min(len(old),len(new));assert old[:n]==new[:n],('paired sampling mismatch',key,b)
            if old is None or len(new)>len(old):ref[key]=new
            out.write(json.dumps(row,separators=(',',':'))+'\n');out.flush()
            print(i,'/',len(jobs),c['id'],z,b,r,'done',row['within_budget'],'N',row['observations'],
                  'W',row['work'],'s',round(row['seconds'],3),'clear',row['controller']['success'],
                  'phaseN',row['controller']['extra_observations'],'hits',row['stats']['hits'],
                  'elapsed',round(time.perf_counter()-start,1),flush=True)
    assert sources()==m['sources'];m.update(completed=True,runs=len(jobs),output_sha256=digest(f/'runs.jsonl'))
    (f/'manifest.json').write_text(json.dumps(m,indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);ap.add_argument('--smoke',action='store_true')
    a=ap.parse_args();run(a.out,a.smoke)
