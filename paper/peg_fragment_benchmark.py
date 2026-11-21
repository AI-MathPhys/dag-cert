"""python -m paper.peg_fragment_benchmark --out results/peg_fragment_v1"""
import argparse
import hashlib
import json
import platform
import random
import time
from pathlib import Path
from paper.peg_fragment_models import PegProblem,positions,fragmented,exact_peg
from paper.cold_decision_solvers import create
ROOT=Path(__file__).resolve().parents[1]
COMMON=('range','compact','direct','persistent')
WORK_CAP=25_600_000
DRAW_CAP=131_072
DEADLINE=8.
def cases():
    for kind,b,h in positions():
        yield dict(domain='peg',group=kind,board=b,depth=h,seed=211001+b*7+h)
    for seed in range(212101,212107):
        for good in (1,4):
            for gap in (1.25,3):
                for noise in ('constant','bernoulli'):
                    yield dict(domain='fragment',group=noise,seed=seed,good=good,gap=gap)
def name(c):
    return '-'.join(str(c[k]) for k in sorted(c))
def run_one(c,method):
    peg=c['domain']=='peg'
    # Fragment topology and reward tapes are the supplied immutable input.
    if not peg:p=fragmented(c['seed'],c['good'],c['gap'],c['group'])
    cfg=dict(epsilon=.05,delta=.05 if peg else .01,K=64000,cap=12,oracle_cost=1)
    start=time.perf_counter()
    if method=='dp':
        actions,states=exact_peg(c['board'],c['depth'])
        elapsed=time.perf_counter()-start
        return dict(seconds=elapsed,status='certified' if elapsed<=DEADLINE else 'wall',
                    action=actions.index(max(actions)) if elapsed<=DEADLINE else None,dp_states=states,
                    values=[str(v) for v in actions],work=None,draws=0)
    if peg:p=PegProblem(c['board'],c['depth'])
    s=create(p,cfg,c['seed'],method)
    physical=s.oracle
    def work():
        return s.w.total+(p.build_work+physical.operations if peg else 0)
    def limits():
        if work()>WORK_CAP:return 'work'
        if time.perf_counter()-start>DEADLINE:return 'wall'
        return None
    q=s.query();seal=None;oldtrial=None;conflict=False
    while True:
        if limits() or q[1] or getattr(s,'abstain',False) or s.w.oracle_calls>=DRAW_CAP:break
        oldtrial=getattr(s,'trial',None)
        try:
            _,q=s.step(DRAW_CAP-s.w.oracle_calls)
        except ArithmeticError:
            if not (s.ev.conflict or (getattr(s,'trial',None) and s.trial.evidence.conflict)):raise
            conflict=True;break
        if seal is None and getattr(s,'meta',{}).get('seal'):
            seal=dict(query=s.idx.q,draws=s.w.oracle_calls,work=work(),seconds=time.perf_counter()-start,
                      size=len(s.idx.F))
    if getattr(s,'trial',None) is not None:s.close('abort_cap')
    charged=work();elapsed=time.perf_counter()-start
    status=('conflict' if conflict else 'wall' if elapsed>DEADLINE else 'work' if charged>WORK_CAP
            else 'certified' if q[1] else 'abstain' if getattr(s,'abstain',False) else 'draw')
    action=q[0] if status=='certified' else None
    # Audit outside the timer by scanning the terminal memberships independently.
    box=None
    if action is not None:
        if getattr(s,'meta',{}).get('decision'):
            if oldtrial is None:raise AssertionError('missing private witness')
            box=(oldtrial.inside_lower,oldtrial.outside.value[1])
        else:
            spans=s.idx.top.inside[action];members={j for l,r in spans for j in range(l,r)}
            box=(max(s.idx.lower[j] for j in members),
                 max((u for j,u in enumerate(s.idx.upper) if j not in members),default=-1))
        if box[1]-box[0]>s.tol:raise AssertionError('invalid certificate')
    if peg and physical.calls!=s.w.oracle_calls:raise AssertionError('physical draws')
    final_lower=max(s.idx.lower)
    return dict(seconds=elapsed,work=charged,draws=s.w.oracle_calls,status=status,action=action,box=box,
                queries=s.idx.q,seal=seal,meta=getattr(s,'meta',None),switches=getattr(s.idx,'switches',None),
                terminals=len(p.graph.leaves),vertices=len(p.graph),rng_counts=s.ev.counts,
                final_possible=sum(u>=final_lower for u in s.idx.upper),
                rollout_jumps=physical.jumps if peg else None)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(folder,domain=None):
    folder.mkdir(parents=True,exist_ok=True)
    if any(folder.iterdir()):raise ValueError('Use a fresh output directory')
    specs=[c for c in cases() if domain is None or c['domain']==domain]
    paths=['paper/'+n for n in ('peg_fragment_protocol.txt','peg_fragment_models.py','cold_decision_solvers.py',
           'peg_fragment_benchmark.py','compact_partial.py','partial_clearing.py','escrow_clearing.py',
           'frontier_sampling.py','relevance_frontier.py','uniform_selection.py','sampling_confidence_allcount.py')]
    paths.extend(['dag_mcts/graph.py','dag_mcts/certified_uct.py'])
    manifest=dict(cases=specs,platform=platform.platform(),python=platform.python_version(),
                  source={f:digest(ROOT/f) for f in paths})
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))
    blocks=[]
    for i,c in enumerate(specs):
        methods=list(COMMON)+( ['fixed','dp'] if c['domain']=='peg' else [])
        random.Random(214001+i).shuffle(methods)
        blocks.extend([(c,0,methods),(c,1,methods[::-1])])
    random.Random(214902).shuffle(blocks)
    with (folder/'runs.jsonl').open('x') as out:
        for i,(c,rep,methods) in enumerate(blocks):
            for pos,m in enumerate(methods):
                rec=run_one(c,m)
                rec.update(case=name(c),spec=c,method=m,repeat=rep,position=pos)
                out.write(json.dumps(rec)+'\n');out.flush()
            if (i+1)%8==0:print(i+1,'/',len(blocks),'blocks',flush=True)
    (folder/'complete.json').write_text(json.dumps({'records':sum(len(b[2]) for b in blocks),
           'sha256':digest(folder/'runs.jsonl')},indent=2))
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--domain',choices=('peg','fragment'))
    args=parser.parse_args();run(args.out,args.domain)

