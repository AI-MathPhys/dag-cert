"""Isolate paid evidence transfer for every fresh case that passed the frozen gate."""
import argparse
import json
import random
import time
from pathlib import Path
from paper.frontier_gate_race import Lane,AuditedCompact,policy_value,checkpoint,DRAWS,SECONDS,BUDGET
from paper.frontier_gate_benchmark import DEFAULT,ROOT,caseid,frag,solve,Game,digest
OUT=ROOT/'results/frontier_gate_warm_v1'

class WarmLane(Lane):
    def __init__(self,p,c,seed,base):
        s=AuditedCompact(p,c,seed);b=base.engine
        self.engine=s;self.oracle=s.oracle;w=s.w
        for name in ('counts','sums','lower','upper','next_count'):
            setattr(s.ev,name,list(getattr(b.ev,name)))
        w.query_reads+=5*len(s.g);w.statistic_writes+=5*len(s.g)+8
        s.N=b.N;s.ev.evaluations=b.ev.evaluations
        stream_name='tapes' if hasattr(self.oracle,'tapes') else 'rng'
        source=getattr(base.oracle,stream_name);target=getattr(self.oracle,stream_name)
        self.copied=0
        for j,leaf in enumerate(s.g.leaves):
            w.query_reads+=3
            if b.ev.counts[leaf]:
                target[leaf].setstate(source[leaf].getstate())
                w.query_reads+=627;w.statistic_writes+=627;self.copied+=1
            s.idx.publish(j,b.idx.lower[j],b.idx.upper[j])
        # The range caller has no historical misses or paid range queries.
        # Keep its local probe clock and credit cold, exactly as in the control.
        self.point=s.query();self.conflict=False;self.peak=0;self.seal_at=None

def fork_race(factory,c,seed,variant):
    """Run a full protected solve. Both variants keep persistent on a negative gate."""
    if variant not in ('warm','screen'):raise ValueError('expected warm or screen')
    start=time.perf_counter();p=factory();build=getattr(p,'build',0)
    b=Lane(p,c,seed,'persistent');a=None;fee=0;dispatch=12;charged=0;gate=None;h=0;eligible=None
    checkpoint_q=checkpoint(len(p.graph.leaves))
    while True:
        cost=build+b.work+dispatch+fee+charged+(a.work if a else 0)
        draws=b.draws+(a.draws if a else 0)
        if (b.point[1] or b.conflict or (a and (a.point[1] or a.conflict)) or
            cost>=BUDGET or draws>=DRAWS or time.perf_counter()-start>=SECONDS):break
        if gate is None and b.engine.idx.q>=checkpoint_q:
            gate=False
            if 32<=(build+b.work)//16:
                gate=policy_value(b,'early',len(p.graph.leaves),c['epsilon'])[0];fee=32
            if gate and variant=='screen':
                spans=b.engine.idx.top.inside;extra=2*len(spans)+4
                if fee+extra<=(build+b.work)//16:
                    fee+=extra;eligible=max(map(len,spans))>=8
                else:eligible=False
                gate=eligible
        pc=build+b.work;cc=charged+(a.work if a else 0)
        if gate and cc<=pc:
            if a is None:a=WarmLane(p,c,seed,b) if variant=='warm' else Lane(p,c,seed,'compact')
            else:a.advance(DRAWS-draws)
            charged+=8;h=max(h,a.work+charged-cc)
        else:
            b.advance(DRAWS-draws);dispatch+=8
    winner=a if a and a.point[1] else b if b.point[1] else None
    action=winner.point[0] if winner else None;box=None
    if winner:
        _,_,lo,_,y=winner.point
        box=winner.private if y is None else (lo,y[0])
        assert box[1]-box[0]<=winner.engine.tol
    pc=build+b.work;cc=charged+(a.work if a else 0);draws=b.draws+(a.draws if a else 0)
    assert cc<=pc+h and fee<=pc/16 and dispatch<=20+.01*pc
    copied=getattr(a,'copied',0);sealed=bool(a and a.seal_at)
    conflict=b.conflict or bool(a and a.conflict)
    pdrop=b.retire(p,c);cdrop=a.retire(p,c) if a else 0
    work=pc+cc+dispatch+fee+pdrop+cdrop
    elapsed=time.perf_counter()-start
    status=('conflict' if conflict else 'wall' if elapsed>SECONDS else 'work' if work>BUDGET
            else 'certified' if winner else 'draw' if draws>=DRAWS else 'work')
    return dict(status=status,action=action if status=='certified' else None,seconds=elapsed,work=work,
                draws=draws,copied=copied,alt_seal=sealed,quantum=h,alt_won=winner is a and a is not None,
                pdrop=pdrop,cdrop=cdrop,C=cc,prefix_or_full_P=pc,eligible=eligible,fee=fee,
                box=box if status=='certified' else None,gate_active=bool(gate))

def run(dest=OUT):
    allspec=json.loads((DEFAULT/'manifest.json').read_text())['cases']
    rows=[json.loads(l) for l in (DEFAULT/'runs.jsonl').read_text().splitlines()]
    early={(r['case'],r['repeat']):r['gate'] for r in rows if r['method']=='early'}
    specs=[s for s in allspec if all(early[caseid(s),i] and early[caseid(s),i]['admit'] for i in (0,1))]
    dest.mkdir(parents=True,exist_ok=True)
    if any(dest.iterdir()):raise ValueError('fresh output required')
    manifests=json.loads((DEFAULT/'manifest.json').read_text())['source']
    for f in ('paper/frontier_gate_warm.py','paper/frontier_gate_warm_protocol.txt','paper/frontier_gate_race.py'):
        manifests[f]=digest(ROOT/f)
    (dest/'manifest.json').write_text(json.dumps(dict(cases=specs,source=manifests),indent=2))
    blocks=[]
    for i,s in enumerate(specs):
        order=['warm','screen','early','persistent'];random.Random(234101+i).shuffle(order)
        blocks.extend([(s,0,order),(s,1,order[::-1])])
    random.Random(234901).shuffle(blocks)
    with (dest/'runs.jsonl').open('x') as f:
        for s,i,order in blocks:
            game='board' in s
            if game:
                board=tuple(map(tuple,s['board']));factory=lambda:Game(board,s['h'])
            else:
                p=frag(s);factory=lambda:p
            c=dict(epsilon=s['eps'],K=64000 if game or s['family']=='wide' else round(1/s['eps'])**4,
                   delta=.05 if game else .01,cap=12,oracle_cost=1)
            for m in order:
                r=fork_race(factory,c,s['seed'],m) if m in ('warm','screen') else solve(factory,c,s['seed'],m)
                r.update(method=m,case=caseid(s),repeat=i,family=s['family']);f.write(json.dumps(r)+'\n');f.flush()
    (dest/'complete.json').write_text(json.dumps(dict(n=len(specs)*8,sha256=digest(dest/'runs.jsonl'))))
if __name__=='__main__':
    arg=argparse.ArgumentParser();arg.add_argument('--out',type=Path,default=OUT);run(arg.parse_args().out)

