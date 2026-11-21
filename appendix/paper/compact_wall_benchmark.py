"""Counterbalanced, repeated cold-solve wall and CPU benchmark."""
import argparse
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import sys
import time

from paper.partial_benchmark import sources as previous_sources
from paper.compact_partial import solver
from paper.wall_time_common import make_input,execute,fingerprint

METHODS=('range','fast_range','partial','batch_partial','fast_partial')
SEEDS=tuple(range(184101,184109))
SETTINGS=(('fragmented',1),('fragmented_sparse',1),('fragmented_dense',1),('fragmented_shoulder',1),
          ('fragmented',0),('lattice',0),('scrambled',1),('flat',0))
PRICES=(1,64)
WALL=(.02,.05,.1,.2,.3,.5,1,2)
WORK=(100000,400000,1600000,6400000,25600000,102400000)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sources():
    files=(*previous_sources(), 'paper/compact_wall_protocol.txt','paper/compact_wall_benchmark.py',
           'paper/wall_time_common.py','paper/compact_partial.py','tests/test_compact_partial.py')
    return {p:digest(p) for p in files}


def run(out):
    folder=Path(out)
    folder.mkdir(parents=True,exist_ok=False)
    manifest=dict(completed=False,sources=sources(),methods=METHODS,seeds=SEEDS,settings=SETTINGS,
                  prices=PRICES,repeats=5,wall_budgets=WALL,work_budgets=WORK,python=sys.version,
                  platform=platform.platform(),cpu=platform.processor(),gc_thresholds=gc.get_threshold(),
                  timer=time.get_clock_info('perf_counter').implementation)
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))
    # Interpreter warmup only. All measured solvers start from new state.
    c,p=make_input('fragmented',0,1,173101)
    for m in METHODS:
        execute(p,c,173101,m,solver)
    cases=[(f,l,z,price) for f,l in SETTINGS for z in SEEDS for price in PRICES]
    blocks=[(i,rep) for i in range(len(cases)) for rep in range(5)]
    rng=random.Random(1840123)
    rng.shuffle(blocks)
    labels=[]
    for i in range(len(cases)):
        names=list(METHODS)
        rng.shuffle(names)
        labels.append(names)
    with (folder/'runs.jsonl').open('w') as stream:
        for k,(i,rep) in enumerate(blocks,1):
            family,level,z,price=cases[i]
            c,p=make_input(family,level,price,z)
            env=fingerprint(p,z)
            truth=p.graph.optimal_values(p.means)
            order=(0,1,4,2,3)
            if (z-SEEDS[0])%2:order=order[::-1]
            for pos,v in enumerate(order):
                method=labels[i][(v+rep)%5]
                gc.collect()
                cpu_start=time.process_time_ns()
                start=time.perf_counter_ns()
                search,point=execute(p,c,z,method,solver)
                seconds=(time.perf_counter_ns()-start)*1e-9
                cpu=(time.process_time_ns()-cpu_start)*1e-9
                loss=truth[p.graph.root]-truth[p.graph.children[p.graph.root][point[0]]]
                assert not point[1] or loss<=c['epsilon']+1e-12
                meta=getattr(search,'meta',None)
                record=dict(case=c['id'],seed=z,method=method,rep=rep,pos=pos,fingerprint=env,
                            work=search.w.total,physical=search.w.oracle_calls,logical=search.N,
                            queries=search.idx.q,action=point[0],regret=loss,seconds=seconds,cpu=cpu,
                            certified=bool(point[1] and search.w.total<=c['max_work']),meta=meta)
                stream.write(json.dumps(record,separators=(',',':'))+'\n')
                del search
            stream.flush()
            if k%32==0:print(k,'/',len(blocks),'timing blocks',flush=True)
    assert sources()==manifest['sources']
    manifest.update(completed=True,runs=len(blocks)*5,sha256=digest(folder/'runs.jsonl'))
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',required=True)
    run(parser.parse_args().out)
