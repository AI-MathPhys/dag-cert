"""Cold, counterbalanced time-to-certification comparison with fused eager repair."""
import argparse
import json
import platform
import random
import time
from pathlib import Path

from paper.batched_repair import BatchedCompact, BatchedRange
from paper.compact_pre_benchmark import (ProfileLane, ROOT, DEST as ARCHIVE, factory, config,
                                         caseid, digest, BUDGET, DRAWS, SECONDS)

DEST=ROOT/'results/batched_repair_v1'
METHODS=('core_compact','batch_compact','core_range','batch_range')


def cases():
    manifest=json.loads((ARCHIVE/'manifest.json').read_text())
    for s in manifest['cases']:
        yield dict(s,cohort='archive')
    for i,seed in enumerate(range(337101,337109)):
        a=4 if i%2==0 else 8
        yield dict(family='layout'+str(a),seed=seed,M=192 if a==4 else 128,A=a,eps=.0125 if a==4 else 1/60,
                   law=('constant','bernoulli')[(i//2)%2],profile=('sharp','shoulder')[i//4],
                   good=2,cohort='fresh')
        yield dict(family='large',seed=seed,eps=.05,law='bernoulli',cohort='fresh')
        yield dict(family='overlap',seed=seed,eps=.0125,law='constant',cohort='fresh')


class RepairLane(ProfileLane):
    def __init__(self,p,c,seed,method):
        if method.startswith('core_'):
            return super().__init__(p,c,seed,method)
        cls={'batch_range':BatchedRange,'batch_compact':BatchedCompact}[method]
        engine=cls(p,c,seed)
        self.engine=engine
        self.oracle=engine.oracle
        self.account=engine.account
        self.point=engine.query()
        self.peak=0
        self.seal_at=None
        self.conflict=False


def solve(make,c,seed,method):
    start=time.perf_counter()
    start_cpu=time.process_time()
    p=make()
    build=getattr(p,'build',0)
    lane=RepairLane(p,c,seed,method)
    while (not lane.point[1] and not lane.conflict and build+lane.work<BUDGET
           and lane.draws<DRAWS and time.perf_counter()-start<SECONDS):
        lane.advance(DRAWS-lane.draws)
    action,good,lo,_,out=lane.point
    box=None
    if good:
        box=lane.private if out is None else (lo,out[0])
        assert box[1]-box[0]<=lane.engine.tol
    draws,queries=lane.draws,lane.engine.idx.q
    kernel=build+lane.work
    account=vars(lane.account).copy()
    meta=dict(getattr(lane.engine,'meta',{}))
    drop=lane.retire(p,c)
    elapsed=time.perf_counter()-start
    cpu=time.process_time()-start_cpu
    work=kernel+drop
    status=('conflict' if lane.conflict else 'wall' if elapsed>SECONDS else 'work' if work>BUDGET
            else 'certified' if good else 'draw' if draws>=DRAWS else 'work')
    return dict(status=status,work=work,seconds=elapsed,cpu=cpu,draws=draws,queries=queries,drop=drop,
                action=action if status=='certified' else None,box=box if status=='certified' else None,
                account=account,meta=meta)


def run(dest):
    specs=list(cases())
    dest.mkdir(parents=True,exist_ok=False)
    sources=dict(json.loads((ARCHIVE/'manifest.json').read_text())['source'])
    for f in ('batched_repair.py','batched_repair_benchmark.py','batched_repair_protocol.txt','ancestor_repair_replay.py'):
        sources['paper/'+f]=digest(ROOT/'paper'/f)
    assert all(digest(ROOT/f)==h for f,h in sources.items())
    manifest=dict(cases=specs,source=sources,methods=METHODS,python=platform.python_version(),
                  platform=platform.platform(),archive=digest(ARCHIVE/'runs.jsonl'),reps=4)
    (dest/'manifest.json').write_text(json.dumps(manifest,indent=2))
    blocks=[]
    for i,s in enumerate(specs):
        for k in range(2):
            order=list(METHODS)
            random.Random(338101+i+k*7919).shuffle(order)
            blocks.extend(((s,2*k,order),(s,2*k+1,order[::-1])))
    random.Random(339901).shuffle(blocks)
    with (dest/'runs.jsonl').open('x') as file:
        for n,(s,rep,order) in enumerate(blocks,1):
            make,c=factory(s),config(s)
            for pos,m in enumerate(order):
                row=solve(make,c,s['seed'],m)
                row.update(case=caseid(s),method=m,repeat=rep,position=pos)
                file.write(json.dumps(row)+'\n')
                file.flush()
            if n%16==0:
                print(n,'/',len(blocks),'blocks',flush=True)
    (dest/'complete.json').write_text(json.dumps(dict(records=len(blocks)*len(METHODS),
                                         sha256=digest(dest/'runs.jsonl'))))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,default=DEST)
    run(parser.parse_args().out)

