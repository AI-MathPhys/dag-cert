"""Separate all-count control; original H/G source and cohort remain frozen."""
import argparse
import json
import math
from pathlib import Path
import random
import time

from dag_mcts.certified_uct import TranspositionUCT,UCTWork
from dag_mcts.retired_bounds import CanonicalIntervals
from dag_mcts.persistent_queries import PersistentQueries
from dag_mcts.maintenance_regimes import make_problem
from dag_mcts.completion_accuracy import sha
from paper.sampling_confidence import Search,RoutedSampler,SAMPLERS,configurations
from paper.stopping_diagnostic import cases
import paper.sampling_confidence_benchmark as base

ALL_SAMPLERS=SAMPLERS+('uct_c14','lazy_uct_c14')
METHODS=tuple(f'{s}_{b}' for s in ALL_SAMPLERS for b in ('H','M'))


class MixtureIntervals(CanonicalIntervals):
    def __init__(self,g,w,delta=.05,scale=40):
        super().__init__(g,w,delta,scale)
        self.log_ratio=math.log(len(g.leaves)/delta);w.initialization+=2

    def observe(self,leaf,reward):
        if self.graph.children[leaf] or not math.isfinite(reward) or not 0<=reward<=1:
            raise ValueError('Need a bounded canonical observation')
        self.counts[leaf]+=1;self.sums[leaf]+=reward
        w=self.work;w.oracle_calls+=1;w.statistic_writes+=2;w.confidence_work+=1
        n=self.counts[leaf];self.next_count[leaf]=n+1;self.evaluations+=1
        w.statistic_writes+=4;w.confidence_work+=11
        radius=math.sqrt((n+1)/(2*n*n)*(self.log_ratio+.5*math.log1p(n)))
        lo=max(self.lower[leaf],self.sums[leaf]/n-radius,0.)
        hi=min(self.upper[leaf],self.sums[leaf]/n+radius,1.)
        self.lower[leaf],self.upper[leaf]=lo,hi
        if lo>hi:self.conflict=True;return None
        if self.scale!=1:
            lo=max(0,math.floor(math.nextafter(self.scale*lo,-math.inf)))
            hi=min(self.scale,math.ceil(math.nextafter(self.scale*hi,math.inf)))
            w.confidence_work+=4
        return lo,hi


class AllCountSearch(Search):
    def __init__(self,p,c,seed,method):
        if method.endswith('_H') and '_c14_' not in method:
            super().__init__(p,c,seed,method);return
        assert method.endswith(('_H','_M'))
        self.g=p.graph;self.work=UCTWork();w=self.work;g=self.g
        w.initialization+=16*len(g)+10*sum(map(len,g.children))+4*len(g.leaves)
        self.service=PersistentQueries(g,w,'bucket',c['scale'],round(c['scale']*c['epsilon']))
        self.sampling,self.bound=method.rsplit('_',1)
        exploration=1.4 if self.sampling.endswith('_c14') else .7
        self.sampling=self.sampling.removesuffix('_c14')
        self.ev=(MixtureIntervals if self.bound=='M' else CanonicalIntervals)(g,w,c['delta'],c['scale'])
        self.sampler=(TranspositionUCT(g,exploration=exploration,lazy=self.sampling=='lazy_uct') if self.sampling in ('uct','lazy_uct')
                      else RoutedSampler(g,w,self.service,self.sampling))
        self.oracle=p.oracle(seed);self.calls=0
        self.nodes=[v for v,row in enumerate(g.children) if len(row)>1];w.initialization+=len(g)


def sources():
    d=base.sources()
    for p in ('paper/sampling_confidence_allcount.py','paper/sampling_confidence_allcount_amendment.txt',
              'tests/test_sampling_confidence_allcount.py'):d[p]=sha(p)
    return d


def run_diagnostic(out,limit=None):
    items,inputs,_=cases()
    if limit is not None:items=items[:limit]
    f=Path(out);f.mkdir(parents=True,exist_ok=False)
    m=dict(completed=False,records=len(items),sources=sources(),inputs=inputs,smoke=limit is not None,bounds=['H','M'])
    (f/'manifest.json').write_text(json.dumps(m,indent=2));start=time.perf_counter()
    old_factory=base.GeometricIntervals;base.GeometricIntervals=MixtureIntervals
    try:
        with (f/'records.jsonl').open('w') as output:
            for i,(cohort,c,seed,old) in enumerate(items,1):
                r=base.diagnose_one(make_problem(c,seed),c,seed,old)
                for key in ('first','details'):r[key]['M']=r[key].pop('G')
                r['cohort']=cohort;output.write(json.dumps(r,separators=(',',':'))+'\n');output.flush()
                print('mixture diagnostic',i,'/',len(items),c['id'],seed,r['first'],
                      'elapsed',round(time.perf_counter()-start,1),flush=True)
    finally:base.GeometricIntervals=old_factory
    m.update(completed=True,output_sha256={'records.jsonl':sha(f/'records.jsonl')})
    (f/'manifest.json').write_text(json.dumps(m,indent=2))


def run_benchmark(out,limit=None):
    f=Path(out);f.mkdir(parents=True,exist_ok=False);cs=configurations()
    if limit is not None:cs=cs[:limit]
    m=dict(completed=False,configurations=cs,methods=METHODS,seeds=[107000,107001,107002],sources=sources(),
           work_budgets=base.WORK_BUDGETS,wall_budgets=base.WALL_BUDGETS,smoke=limit is not None,bounds=['H','M'])
    (f/'manifest.json').write_text(json.dumps(m,indent=2));old_factory=base.Search;base.Search=AllCountSearch
    try:
        warm=dict(cs[0],max_work=10000)
        for method in METHODS:base.measure(make_problem(warm,106999),warm,106999,method)
        jobs=[(c,seed,method) for c in cs for seed in m['seeds'] for method in METHODS]
        random.Random(20261104).shuffle(jobs);start=time.perf_counter()
        with (f/'runs.jsonl').open('w') as output:
            for i,(c,seed,method) in enumerate(jobs,1):
                r=base.measure(make_problem(c,seed),c,seed,method)
                r['exploration']=1.4 if '_c14_' in method else .7 if r['sampler'] in ('uct','lazy_uct') else None
                output.write(json.dumps(r,separators=(',',':'))+'\n');output.flush()
                print('mixture benchmark',i,'/',len(jobs),c['id'],seed,method,'done',r['within_max_budget'],
                      'N',r['observations'],'W',r['work'],'s',round(r['seconds'],3),
                      'elapsed',round(time.perf_counter()-start,1),flush=True)
    finally:base.Search=old_factory
    m.update(completed=True,runs=len(jobs),output_sha256={'runs.jsonl':sha(f/'runs.jsonl')})
    (f/'manifest.json').write_text(json.dumps(m,indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=('diagnostic','benchmark','all'),required=True)
    ap.add_argument('--out',required=True);ap.add_argument('--limit',type=int);args=ap.parse_args()
    if args.mode=='diagnostic':run_diagnostic(args.out,args.limit)
    elif args.mode=='benchmark':run_benchmark(args.out,args.limit)
    else:
        run_diagnostic(args.out+'_diagnostic',args.limit)
        run_benchmark(args.out+'_benchmark',args.limit)
