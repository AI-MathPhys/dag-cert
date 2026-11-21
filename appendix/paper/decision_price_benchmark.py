"""Cold matched comparisons of threshold-only, exact and price-free policies."""
import json
import os
import platform
import random
import time

from paper.decision_price import DecisionLane, ENGINES
from paper.repair_policy_clock import (ARCHIVE, ROOT, DEST as CLOCK, BUDGET, DRAWS, SECONDS,
                                      config, factory, caseid, digest, endpoint, audit_action, status)

DEST = ROOT/'results/decision_price_v1'


def population():
    for spec in json.loads((ARCHIVE/'manifest.json').read_text())['cases']:
        yield dict(tag='cohort',case=caseid(spec),s=spec,tie=spec['seed'],reps=2)
    witness = json.loads((CLOCK/'construction.json').read_text())['witness']['spec']
    for tie in (witness['seed'],*range(355101,355117)):
        yield dict(tag='selected' if tie==witness['seed'] else 'witness-retie',
                   case=f'witness-{tie}',s=witness,tie=tie,reps=1)
    for i in range(4):
        s=dict(family='layout4',M=224,A=4,good=2,eps=1/80,
               law=('constant','bernoulli')[i%2],profile=('sharp','shoulder')[i//2],
               seed=355001+i,cohort='distribution')
        for tie in range(355101,355117):
            yield dict(tag='fresh',case=f'fresh-{i}-{tie}',s=s,tie=tie,reps=1)


def solve(make,cfg,tie,method):
    start = time.perf_counter()
    cpu = time.process_time()
    p = make()
    lane = DecisionLane(p,cfg,tie,method)
    build = getattr(p,'build',0)
    while (not lane.point[1] and not lane.conflict and build+lane.work<BUDGET
           and lane.draws<DRAWS and time.perf_counter()-start<SECONDS):
        lane.advance(DRAWS-lane.draws)
    row = endpoint(lane,p,cfg)
    row.update(seconds=time.perf_counter()-start,cpu=time.process_time()-cpu)
    row['status'] = status(row,lane.conflict,row['seconds'])
    audit_action(p,row,cfg)
    return row


def run():
    specs = list(population())
    old = json.loads((CLOCK/'manifest.json').read_text())
    files = dict(old['source'])
    for name in ('decision_price.py','decision_price_benchmark.py','decision_price_protocol.txt'):
        files['paper/'+name] = digest(ROOT/'paper'/name)
    assert all(digest(ROOT/f)==h for f,h in files.items())
    DEST.mkdir(exist_ok=False)
    methods=list(ENGINES)
    manifest=dict(specs=specs,sources=files,methods=methods,python=platform.python_version(),
                  platform=platform.platform(),processor=platform.processor(),
                  logical_cpus=os.cpu_count(),caps=[BUDGET,DRAWS,SECONDS])
    (DEST/'manifest.json').write_text(json.dumps(manifest,indent=2))
    rng=random.Random(358977)
    blocks=[]
    for obj in specs:
        order=methods.copy()
        rng.shuffle(order)
        blocks.append((obj,0,order))
        if obj['reps']==2:
            blocks.append((obj,1,order[::-1]))
    rng.shuffle(blocks)
    with (DEST/'runs.jsonl').open('x') as out:
        for i,(obj,rep,order) in enumerate(blocks,1):
            s=obj['s']
            make,cfg=factory(s),config(s)
            for pos,m in enumerate(order):
                r=solve(make,cfg,obj['tie'],m)
                r.update(case=obj['case'],tag=obj['tag'],method=m,repeat=rep,position=pos)
                out.write(json.dumps(r)+'\n')
                out.flush()
            if i%16==0:
                print(i,'/',len(blocks),'blocks',flush=True)
    (DEST/'complete.json').write_text(json.dumps(dict(rows=len(blocks)*len(methods),
                                                     sha256=digest(DEST/'runs.jsonl'))))


if __name__=='__main__':
    run()
