"""Prespecified single-host serial timing benchmark for the prospective frontier gate."""
import argparse
import hashlib
import json
import platform
import random
import time
from pathlib import Path
from paper.peg_fragment_benchmark import ROOT,digest
from paper.peg_fragment_models import fragmented
from paper.peg_precision import problem as tight
from paper.samegame_gate import game_cases, Game, exact
from paper.frontier_gate_race import solve,SECONDS

BASE=('persistent','compact','range','early','static','blind')
DEFAULT=ROOT/'results/frontier_gate_v1'
def cases():
    for seed in range(229101,229107):
        for law in ('constant','bernoulli'):
            for good in (1,4):yield dict(family='wide',seed=seed,good=good,eps=.05,law=law)
            yield dict(family='middle',seed=seed,good=2,eps=.025,law=law)
        for good in (1,2):
            for eps in (.05,.02,.01):
                yield dict(family='narrow',seed=seed,good=good,eps=eps,law='constant')
    yield from game_cases()
def caseid(s):
    return '-'.join(str(s[k]) for k in ('family','seed','good','eps','law') if k in s)
def frag(s):
    if s['family']=='narrow':return tight(s['seed'],s['good'],s['eps'])
    wide=s['family']=='wide'
    return fragmented(s['seed'],s['good'],1.25*s['eps']/.05,s['law'],256 if wide else 128,32 if wide else 8)
def run_one(s,method):
    game='board' in s
    if method=='dp':
        start=time.perf_counter();vals,n=exact(s['board'],s['h']);elapsed=time.perf_counter()-start
        return dict(seconds=elapsed,work=None,status='certified' if elapsed<=SECONDS else 'wall',
                    action=vals.index(max(vals)) if elapsed<=SECONDS else None,values=list(map(str,vals)),states=n)
    cfg=dict(epsilon=s['eps'],delta=.05 if game else .01,
             K=64000 if game or s['family']=='wide' else round(1/s['eps'])**4,cap=12,oracle_cost=1)
    if game:
        factory=lambda:Game(s['board'],s['h'])
    else:
        p=frag(s);factory=lambda:p
    return solve(factory,cfg,s['seed'],method)
def run(dest):
    specs=list(cases())
    dest.mkdir(parents=True,exist_ok=True)
    if any(dest.iterdir()):raise ValueError('Use a fresh output directory')
    paths=['paper/'+f for f in ('frontier_gate_benchmark.py','frontier_gate_protocol.txt','frontier_gate_features.py',
           'frontier_gate_race.py','frontier_gate_model.json','fit_frontier_gate.py','samegame_gate.py',
           'peg_fragment_models.py','peg_precision.py','cold_decision_solvers.py','compact_partial.py','partial_clearing.py',
           'escrow_clearing.py','frontier_sampling.py','relevance_frontier.py','uniform_selection.py',
           'sampling_confidence_allcount.py')]
    paths+=['data/samegame/StandardTestset.txt','dag_mcts/graph.py','dag_mcts/retired_bounds.py','dag_mcts/certified_uct.py']
    (dest/'manifest.json').write_text(json.dumps(dict(cases=specs,python=platform.python_version(),platform=platform.platform(),
                                      source={f:digest(ROOT/f) for f in paths}),indent=2))
    blocks=[]
    for i,sp in enumerate(specs):
        order=list(BASE)+(['dp'] if 'board' in sp else [])
        random.Random(230902+i).shuffle(order)
        blocks.extend([(sp,0,order),(sp,1,order[::-1])])
    random.Random(231801).shuffle(blocks)
    with (dest/'runs.jsonl').open('x') as f:
        for i,(sp,rep,order) in enumerate(blocks):
            for pos,m in enumerate(order):
                rec=run_one(sp,m);rec.update(case=caseid(sp),method=m,repeat=rep,position=pos)
                f.write(json.dumps(rec)+'\n');f.flush()
            if (i+1)%16==0:print(i+1,'/',len(blocks),flush=True)
    (dest/'complete.json').write_text(json.dumps(dict(records=sum(len(b[2]) for b in blocks),sha256=digest(dest/'runs.jsonl'))))
if __name__=='__main__':
    arg=argparse.ArgumentParser();arg.add_argument('--out',type=Path,default=DEFAULT)
    run(arg.parse_args().out)

