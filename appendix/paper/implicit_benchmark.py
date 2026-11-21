"""Paid large-DAG experiment and a separate identical-publication stress trace."""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import random
import time
import numpy as np

from dag_mcts.certified_uct import UCTWork
from dag_mcts.completion_accuracy import sha,update_observations
from dag_mcts.demand_benchmark import retained_bytes
from paper.implicit_support import ImplicitSearch,SupportIndex,METHODS,EMPTY
from paper.implicit_problems import configurations,make_problem,interval_problem

WB=(1000000,4000000,16000000)
TB=(.1,.5,2.,10.)


def sources():
    names=['paper/implicit_support.py','paper/implicit_problems.py','paper/implicit_benchmark.py',
           'paper/implicit_support_protocol.txt','tests/test_implicit_support.py',
           'paper/sampling_confidence_allcount.py','paper/sampling_confidence.py']
    return {p.as_posix():sha(p) for p in list(Path('dag_mcts').glob('*.py'))+[Path(s) for s in names]}


class Reference:
    """Independent root reachability bitsets and NumPy terminal scans, untimed."""
    def __init__(self,p,c):
        g=p.graph;self.g=g;self.leaves=np.array(g.leaves,dtype=np.int64)
        self.rank={v:i for i,v in enumerate(g.leaves)}
        reach=[0]*len(g)
        for a,v in enumerate(g.children[g.root]):reach[v]|=1<<a
        for v in g.order:
            if v==g.root:continue
            for x in g.children[v]:reach[x]|=reach[v]
        self.masks=[reach[x] for x in g.leaves]
        self.owner=np.array([(x&-x).bit_length()-1 for x in self.masks])
        self.low=np.zeros(len(g.leaves),dtype=np.int64)
        self.high=np.full(len(g.leaves),c['scale'],dtype=np.int64)
        self.cache={};self.truth=g.optimal_values(p.means);self.e=round(c['epsilon']*c['scale'])

    def check(self,pubs,point):
        for leaf,lo,hi in pubs:self.low[self.rank[leaf]]=lo;self.high[self.rank[leaf]]=hi
        maximum=int(self.low.max());a=int(self.owner[self.low==maximum].min())
        if a not in self.cache:
            self.cache[a]=np.array([bool(mask&(1<<a)) for mask in self.masks])
        inside=self.cache[a]
        def best(mask):
            indices=np.flatnonzero(mask)
            if not len(indices):return EMPTY
            i=indices[int(np.argmax(self.high[indices]))]
            return int(self.high[i]),-int(self.leaves[i])
        x,y=best(inside),best(~inside);ok=y==EMPTY or y[0]<=maximum+self.e
        assert point==(a,ok,maximum,x,y),(point,(a,ok,maximum,x,y))
        regret=self.truth[self.g.root]-self.truth[self.g.children[self.g.root][a]]
        return regret


def measure(p,c,seed,method):
    start=time.perf_counter();s=ImplicitSearch(p,c,seed,method);point=s.query();elapsed=time.perf_counter()-start
    setup_work=s.work.total;setup_seconds=elapsed
    initial_memory=retained_bytes(s,(p.graph,s.work));ref=Reference(p,c)
    digest=hashlib.sha256();prefixes=[];work_points={};wall_points={};previous=None
    candidates=set();last_work=0;peak_block=setup_work
    def checkpoint(point,pubs,obs):
        nonlocal previous,last_work,peak_block
        regret=ref.check(pubs,point)
        if point[1]:assert regret<=c['epsilon']+1e-12
        update_observations(digest,obs);digest.update(repr((pubs,point)).encode());prefixes.append(digest.hexdigest())
        candidates.add(point[0]);work=s.work.total;peak_block=max(peak_block,work-last_work);last_work=work
        current=dict(N=s.calls,work=work,seconds=elapsed,certified=point[1],action=point[0],regret=regret)
        for b in WB:
            if str(b) not in work_points and work>b:work_points[str(b)]=previous
        for b in TB:
            if str(b) not in wall_points and elapsed>b:wall_points[str(b)]=previous
        previous=current
    checkpoint(point,[],[])
    while not point[1] and s.work.total<=c['max_work']:
        start=time.perf_counter();obs,point,pubs=s.block(c['cadence']);elapsed+=time.perf_counter()-start
        checkpoint(point,pubs,obs)
    for b in WB:
        if str(b) not in work_points:work_points[str(b)]=previous
    for b in TB:
        if str(b) not in wall_points:
            wall_points[str(b)]=previous if point[1] else {'unknown_after_work_cap':True,'last':previous}
    assert s.work.oracle_calls==s.calls
    assert s.work.total<=max(setup_work,c['max_work']+peak_block)
    return dict(config=c['id'],seed=seed,method=method,certified=point[1],
        within_budget=point[1] and s.work.total<=c['max_work'],N=s.calls,work=s.work.total,seconds=elapsed,
        setup_work=setup_work,setup_seconds=setup_seconds,work_points=work_points,wall_points=wall_points,
        initial_memory_bytes=initial_memory,memory_bytes=retained_bytes(s,(p.graph,s.work)),
        nodes=len(p.graph),edges=sum(map(len,p.graph.children)),leaves=len(p.graph.leaves),
        atoms=len(s.index.atom_keys),unknown_nodes=sum(r is None for r in s.index.topology.ranges),
        fallbacks=s.index.topology.fallbacks,view_builds=s.index.view_builds,repairs=s.index.repairs,
        upper_changes=s.index.upper_changes,queries=s.index.queries,candidates=len(candidates),
        fields=asdict(s.work),peak_block=peak_block,prefixes=prefixes,last=previous)


def online(out,limit=None):
    f=Path(out);f.mkdir(parents=True,exist_ok=False);cs=configurations()
    if limit is not None:cs=cs[:limit]
    m=dict(completed=False,smoke=limit is not None,configurations=cs,methods=METHODS,seeds=[108000,108001,108002],
           sources=sources(),work_budgets=WB,wall_budgets=TB)
    (f/'manifest.json').write_text(json.dumps(m,indent=2))
    warm=dict(cs[0],L=64,A=8,max_work=20000)
    for method in METHODS:measure(make_problem(warm,107999),warm,107999,method)
    jobs=[(c,seed,method) for c in cs for seed in m['seeds'] for method in METHODS]
    random.Random(20261106).shuffle(jobs);start=time.perf_counter()
    with (f/'runs.jsonl').open('w') as output:
        for j,(c,seed,method) in enumerate(jobs,1):
            r=measure(make_problem(c,seed),c,seed,method)
            output.write(json.dumps(r,separators=(',',':'))+'\n');output.flush()
            print(j,'/',len(jobs),c['id'],method,seed,'done',r['within_budget'],'N',r['N'],
                  'W',r['work'],'s',round(r['seconds'],2),'elapsed',round(time.perf_counter()-start,1),flush=True)
    assert m['sources']==sources()
    m.update(completed=True,runs=len(jobs),output_sha256=sha(f/'runs.jsonl'))
    (f/'manifest.json').write_text(json.dumps(m,indent=2))


def maintenance(out):
    f=Path(out);f.mkdir(parents=True,exist_ok=False)
    m=dict(completed=False,sources=sources(),sizes=[64,256,1024,4096],methods=METHODS)
    (f/'manifest.json').write_text(json.dumps(m,indent=2));records=[]
    for A in m['sizes']:
        p=interval_problem(2*A-1,A);g=p.graph
        hashes=[]
        for method in METHODS:
            w=UCTWork();start=time.perf_counter();w.initialization+=16*len(g)+10*sum(map(len,g.children))
            s=SupportIndex(g,w,40,method);setup=w.total;elapsed=time.perf_counter()-start
            h=hashlib.sha256();cs=set()
            for i,leaf in enumerate(reversed(g.leaves[A-1:])):
                start=time.perf_counter();s.publish(leaf,28,32);point=s.query();elapsed+=time.perf_counter()-start
                assert point[0]==A-1-i;cs.add(point[0]);h.update(repr(point).encode())
            r=dict(A=A,L=len(g.leaves),nodes=len(g),edges=sum(map(len,g.children)),method=method,
                   work=w.total,setup_work=setup,seconds=elapsed,memory_bytes=retained_bytes(s,(g,w)),
                   builds=s.view_builds,repairs=s.repairs,candidates=len(cs),atoms=len(s.atom_keys),sha256=h.hexdigest())
            records.append(r);hashes.append(h.hexdigest());print('maintenance',r,flush=True)
        assert len(set(hashes))==1
    (f/'runs.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
    assert m['sources']==sources();m.update(completed=True,output_sha256=sha(f/'runs.jsonl'))
    (f/'manifest.json').write_text(json.dumps(m,indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=('online','maintenance'),required=True)
    ap.add_argument('--out',required=True);ap.add_argument('--limit',type=int);a=ap.parse_args()
    if a.mode=='online':online(a.out,a.limit)
    else:maintenance(a.out)
