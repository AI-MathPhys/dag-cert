"""Secondary deterministic precision stress study, run separately from the primary cohort."""
from collections import defaultdict
from pathlib import Path
import argparse
import json
import math
import platform
import random
import statistics
import time
from dag_mcts.graph import DAG,Problem
from paper.peg_fragment_benchmark import COMMON,ROOT,digest
from paper.cold_decision_solvers import create
from paper.report_peg_fragment import ratio
DEFAULT=ROOT/'results/peg_precision_v1'
LIMIT=204800000
PULLS=524288

def problem(seed,g,eps):
    rng=random.Random(seed);a=2*g;M=128
    perm=list(range(a));rng.shuffle(perm)
    sets=[set(perm[:g]),set(perm[g:])]
    values=[.70,.70-1.25*eps]
    for i in range((M-2)//2):
        half=set(rng.sample(perm,g))
        sets.extend((set(perm),set(perm)) if i%8==0 else (half,set(perm)-half))
        values.extend((rng.uniform(.05,.25),rng.uniform(.05,.25)))
    pairs=list(range(M//2));rng.shuffle(pairs)
    ranks=[j for k in pairs for j in (2*k,2*k+1)]
    rows=[tuple(range(1,a+1))]
    rows.extend(tuple(1+a+j for j,k in enumerate(ranks) if i in sets[k]) for i in range(a))
    graph=DAG(rows+[()]*M)
    return Problem('precision',graph,{a+1+j:values[k] for j,k in enumerate(ranks)},graph.leaves)

def one(spec,method):
    seed,g,eps=spec['seed'],spec['good'],spec['epsilon']
    p=problem(seed,g,eps)
    values=p.graph.optimal_values(p.means)
    vals=[values[a] for a in p.graph.children[0]]
    assert sum(max(vals)-v<=eps+1e-12 for v in vals)==g
    k=round(1/eps)**4
    config=dict(epsilon=eps,delta=.01,K=k,cap=12,oracle_cost=1)
    start=time.perf_counter();s=create(p,config,seed,method);q=s.query();seal=None;trial=None
    while (not q[1] and s.w.total<LIMIT and s.w.oracle_calls<PULLS and time.perf_counter()-start<15):
        trial=getattr(s,'trial',None)
        _,q=s.step(PULLS-s.w.oracle_calls)
        if seal is None and getattr(s,'meta',{}).get('seal'):
            seal=dict(draws=s.w.oracle_calls,work=s.w.total,size=len(s.idx.F))
    if getattr(s,'trial',None):s.close('abort_cap')
    elapsed=time.perf_counter()-start
    status=('wall' if elapsed>15 else 'work' if s.w.total>LIMIT or (not q[1] and s.w.total>=LIMIT)
            else 'certified' if q[1] else 'draw')
    a=q[0] if status=='certified' else None
    if a is not None:
        assert max(vals)-vals[a]<=eps+1e-12
        if getattr(s,'meta',{}).get('decision'):
            assert trial.outside.value[1]-trial.inside_lower<=s.tol
        else:
            inside={j for lo,hi in s.idx.top.inside[a] for j in range(lo,hi)}
            assert max(s.idx.upper[j] for j in range(128) if j not in inside)-max(s.idx.lower[j] for j in inside)<=s.tol
    return dict(method=method,spec=spec,case=f'{seed}-{g}-{eps}',status=status,action=a,seconds=elapsed,
                work=s.w.total,draws=s.w.oracle_calls,counts=s.ev.counts,seal=seal,queries=s.idx.q,
                meta=getattr(s,'meta',None))

def run(out):
    out.mkdir(parents=True,exist_ok=True)
    if any(out.iterdir()):raise ValueError('Use a fresh output directory')
    specs=[dict(seed=seed,good=g,epsilon=e) for seed in range(217101,217105) for g in (1,2) for e in (.05,.02,.01,.005)]
    frozen=json.loads((ROOT/'results/peg_fragment_v1/manifest.json').read_text())['source']
    for f in ('paper/peg_precision.py','paper/peg_precision_protocol.txt','paper/report_peg_fragment.py'):
        frozen[f]=digest(ROOT/f)
    (out/'manifest.json').write_text(json.dumps(dict(cases=specs,source=frozen,platform=platform.platform()),indent=2))
    blocks=[]
    for i,sp in enumerate(specs):
        order=list(COMMON);random.Random(218501+i).shuffle(order)
        blocks.extend([(sp,0,order),(sp,1,order[::-1])])
    random.Random(218901).shuffle(blocks)
    with (out/'runs.jsonl').open('x') as f:
        for i,(sp,rep,order) in enumerate(blocks):
            for m in order:
                r=one(sp,m);r['repeat']=rep
                f.write(json.dumps(r)+'\n');f.flush()
            if (i+1)%8==0:print(i+1,'/',len(blocks),flush=True)
    (out/'complete.json').write_text(json.dumps(dict(records=len(blocks)*len(COMMON),sha256=digest(out/'runs.jsonl'))))
def report(out):
    rec=[json.loads(l) for l in (out/'runs.jsonl').read_text().splitlines()]
    stamp=json.loads((out/'complete.json').read_text())
    assert len(rec)==stamp['records'] and stamp['sha256']==digest(out/'runs.jsonl')
    keyed={(r['case'],r['repeat'],r['method']):r for r in rec}
    for (c,i,m),r in keyed.items():
        if m=='range' and r['status']=='certified':
            b=keyed[c,i,'direct']
            if b['status']=='certified':
                assert (r['counts'],r['queries'],r['action'])==(b['counts'],b['queries'],b['action'])
    s={}
    for e in (None,.05,.02,.01,.005):
        rows=[r for r in rec if e is None or r['spec']['epsilon']==e]
        methods={}
        for m in COMMON:
            rr=[r for r in rows if r['method']==m];cc=[r for r in rr if r['status']=='certified']
            pairs=defaultdict(list)
            for r in rr:pairs[r['case']].append(r)
            assert all(len(p)==2 for p in pairs.values())
            seals=[r for r in rr if r['seal']]
            methods[m]=dict(completed=sum(all(r['status']=='certified' for r in pp) for pp in pairs.values()),
                cases=len(pairs),certified_runs=len(cc),seal_runs=len(seals),
                post_fraction=statistics.median(1-r['seal']['draws']/r['draws'] for r in seals) if seals else None,
                seconds=statistics.median(r['seconds'] for r in cc) if cc else None,
                restricted=statistics.mean(r['seconds'] if r['status']=='certified' else 15 for r in rr),
                wall=[sum(r['seconds']<=t for r in cc) for t in (.5,2,8,15)],
                work=[sum(r['work']<=w for r in cc) for w in (1600000,6400000,25600000,102400000,204800000)])
        ratios={m+'/'+ref:ratio(rows,m,ref) for m in ('compact','direct') for ref in ('range','persistent')}
        ratios.update({m+'/'+ref+':work':ratio(rows,m,ref,'work') for m in ('compact','direct') for ref in ('range','persistent')})
        s[str(e)]=dict(methods=methods,ratios=ratios)
    (out/'summary.json').write_text(json.dumps(s,indent=2))
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--report',action='store_true');parser.add_argument('--out',type=Path,default=DEFAULT)
    args=parser.parse_args();report(args.out) if args.report else run(args.out)

