"""Serial held-out timing for pre-seal dispatch and shared tree-repair ablations."""
import argparse
import json
import platform
import random
import time
from pathlib import Path

from paper.compact_pre import FastPreCompact, FastPreRange
from paper.compact_side_benchmark import (TimedLane, config, factory as broad_factory,
    ROOT, digest, caseid, SECONDS, DRAWS, BUDGET)
from paper.compact_side_structural import problem as overlap_problem
from paper.paused_benchmark import endgame
from paper.samegame_gate import standard

DEST = ROOT/'results/compact_pre_v1'
METHODS = ('compact','range','side_compact','miss_only','core_compact','fast','core_range','fast_range')


def cases():
    boards = standard()
    for i,seed in enumerate(range(321101,321109)):
        law = ('constant','bernoulli')[i%2]
        yield dict(family='wide',seed=seed,eps=.05,law=law,good=1)
        for size,actions,eps in ((192,4,.0125),(128,8,1/60)):
            law=('constant','bernoulli')[(i+(actions==8))%2]
            for profile in ('sharp','shoulder'):
                yield dict(family='layout'+str(actions),seed=seed,M=size,A=actions,
                           eps=eps,law=law,good=2,profile=profile)
        yield dict(family='narrow',seed=seed,eps=.01,law='constant',good=2)
        yield dict(family='large',seed=seed,eps=.05,law='bernoulli')
        board,path=endgame(boards[(i+16)%len(boards)],seed)
        yield dict(family='samegame',seed=seed,eps=.02,board=board,path=path,source=(i+16)%len(boards)+1,h=3)
        for eps in (.02,.0125):
            yield dict(family='overlap',seed=seed,eps=eps,law='constant')


def factory(s):
    if s['family']=='overlap':
        problem,_=overlap_problem(s)
        return lambda:problem
    return broad_factory(s)


class ProfileLane(TimedLane):
    def __init__(self,p,c,seed,method):
        if method in ('compact','range','side_compact'):
            super().__init__(p,c,seed,method)
            return
        receipts = method in ('miss_only','fast','fast_range')
        fused = method!='miss_only'
        if method in ('core_range','fast_range'):
            engine=FastPreRange(p,c,seed,receipts,fused)
        elif method in ('miss_only','core_compact','fast'):
            engine=FastPreCompact(p,c,seed,receipts,fused)
        else:
            raise ValueError(method)
        self.engine=engine
        self.oracle=engine.oracle
        self.account=engine.account
        self.point=engine.query()
        self.peak=0
        self.seal_at=None
        self.conflict=False


def fast_run(make,c,seed,method,*,clock_cap=SECONDS):
    start=time.perf_counter()
    p=make()
    build=getattr(p,'build',0)
    lane=ProfileLane(p,c,seed,method)
    while (not lane.point[1] and not lane.conflict and build+lane.work<BUDGET
           and lane.draws<DRAWS and time.perf_counter()-start<clock_cap):
        lane.advance(DRAWS-lane.draws)
    action,good,lower,_,outside=lane.point
    box=None
    if good:
        box=lane.private if outside is None else (lower,outside[0])
        assert box[1]-box[0]<=lane.engine.tol
    conflict=lane.conflict
    draws,queries=lane.draws,lane.engine.idx.q
    kernel=build+lane.work
    logical=build+lane.engine.w.total+getattr(lane.oracle,'operations',0)
    info=vars(lane.account).copy() if lane.account else {}
    meta=dict(getattr(lane.engine,'meta',{}))
    drop=lane.retire(p,c)
    elapsed=time.perf_counter()-start
    work=kernel+drop
    status=('conflict' if conflict else 'wall' if elapsed>clock_cap else 'work' if work>BUDGET
            else 'certified' if good else 'draw' if draws>=DRAWS else 'work')
    return dict(status=status,work=work,seconds=elapsed,draws=draws,queries=queries,logical=logical,drop=drop,
                action=action if status=='certified' else None,box=box if status=='certified' else None,
                account=info,meta=meta)


def run(dest):
    specs=list(cases())
    dest.mkdir(parents=True,exist_ok=True)
    if any(dest.iterdir()):
        raise ValueError('use an empty output directory')
    base=ROOT/'results/compact_side_overlap_v1/manifest.json'
    sources=dict(json.loads(base.read_text())['source'])
    for name in ('compact_pre.py','compact_pre_benchmark.py','compact_pre_protocol.txt'):
        path='paper/'+name
        sources[path]=digest(ROOT/path)
    assert all(digest(ROOT/f)==h for f,h in sources.items())
    (dest/'manifest.json').write_text(json.dumps(dict(cases=specs,methods=METHODS,source=sources,
                    python=platform.python_version(),platform=platform.platform(),repeats=4),indent=2))
    blocks=[]
    for i,s in enumerate(specs):
        for pair in range(2):
            order=list(METHODS)
            random.Random(322101+i+7919*pair).shuffle(order)
            blocks.extend(((s,2*pair,order),(s,2*pair+1,order[::-1])))
    random.Random(322909).shuffle(blocks)
    with (dest/'runs.jsonl').open('x') as out:
        for b,(s,rep,order) in enumerate(blocks,1):
            make,c=factory(s),config(s)
            for pos,m in enumerate(order):
                row=fast_run(make,c,s['seed'],m)
                row.update(method=m,case=caseid(s),repeat=rep,position=pos)
                out.write(json.dumps(row)+'\n')
                out.flush()
            if b%16==0:
                print(b,'/',len(blocks),'blocks',flush=True)
    (dest/'complete.json').write_text(json.dumps(dict(records=len(blocks)*len(METHODS),
                                         sha256=digest(dest/'runs.jsonl'))))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,default=DEST)
    run(parser.parse_args().out)

