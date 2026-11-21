"""Prespecified cold timings, independent coupling replay and memory measurement."""
import argparse
import gc
import hashlib
import json
import platform
import random
import time
import tracemalloc
from pathlib import Path
from dag_mcts.compiled_retirement import Search
from dag_mcts.certified_uct import TranspositionUCT
from paper.uct_frontier_families import make,describe
from paper.audit_uct_backup import direct

ROOT=Path(__file__).resolve().parents[1]
DEST=ROOT/'results/uct_frontier_v1'
METHODS=('graph-eager','graph-live','cover-live','covers')
SEEDS=tuple(range(433101,433105))
CASES=(('sparse',4),('sparse',8),('dense',4),('dense',8),
       ('coded',8),('coded',16),('coded',32),('samegame',4),('samegame',5),
       ('lattice',5),('funnel',64))
EFFORTS=(0,512)
WALL=(.001,.010,.100,.500,2.)
CAP=500000
SOURCES=('dag_mcts/compiled_retirement.py','paper/uct_frontier_families.py',
         'paper/uct_frontier_study.py','paper/uct_frontier_protocol.txt',
         'dag_mcts/certified_uct.py','dag_mcts/graph.py','dag_mcts/retired_bounds.py',
         'dag_mcts/onpolicy_backup.py','paper/relevance_frontier.py','paper/uniform_selection.py',
         'paper/samegame_gate.py','paper/uct_backup_families.py')
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def one(p,eps,seed,method,effort):
    gc.collect()
    start=time.perf_counter()
    lane=Search(p,seed,method,eps,effort)
    init=time.perf_counter()-start
    previous=(0,0,False);checkpoints=[]
    def cross(elapsed):
        while len(checkpoints)<len(WALL) and WALL[len(checkpoints)]<elapsed:
            checkpoints.append(previous)
    cross(init)
    init_work=lane.work
    elapsed=init
    while not lane.certified and not lane.monitor.evidence.conflict and lane.uct.calls<CAP and elapsed<WALL[-1]:
        lane.step()
        elapsed=time.perf_counter()-start
        cross(elapsed)
        if not lane.certified and not lane.monitor.evidence.conflict:
            previous=(lane.action,lane.uct.calls,False)
    calls,cert,action=lane.uct.calls,lane.certified,lane.action
    m=lane.monitor;b=getattr(m,'bounds',None)
    result=dict(steps=calls,work=lane.work,init_seconds=init,init_work=init_work,
        monitor_work=m.work.total,allocator_work=lane.uct.work.total,
        oracle_work=getattr(lane.oracle,'operations',0)+lane.extra_work,
        first_cut=lane.first_cut,conflict=m.evidence.conflict,
        messages=getattr(b,'messages',None),retired=getattr(b,'retired',None),
        dead=getattr(b,'dead_nodes',None),
        circuit=getattr(m,'info',{}),compile_work=getattr(m,'compile_work',None),
        certified_at=calls if cert else None,final_gap=lane.query[1])
    # Counters outside the definition of certification computation are recorded
    # before disposal, so timing includes this small, common reporting block.
    del m,b
    release=time.perf_counter()
    del lane
    end=time.perf_counter()-start
    cross(end)
    returned=bool(cert and end<=WALL[-1])
    if returned:previous=(action,calls,True)
    checkpoints.extend([previous]*(len(WALL)-len(checkpoints)))
    values=p.graph.optimal_values(p.means);best=values[p.graph.root]
    regrets=[max(0.,best-values[p.graph.children[p.graph.root][a]]) for a,_,_ in checkpoints]
    valid=not cert or best-values[p.graph.children[p.graph.root][action]]<=eps+1e-12
    result.update(end_seconds=end,retire_seconds=end-(release-start),returned=returned,
                  restricted=end if returned else WALL[-1],checkpoints=checkpoints,
                  regrets=regrets,valid=valid,method=method,effort=effort,epsilon=eps)
    return result

def run():
    DEST.mkdir(exist_ok=False)
    blocks=[]
    rng=random.Random(433000)
    for f,n in CASES:
        for seed in SEEDS:
            for effort in EFFORTS:
                methods=list(METHODS);rng.shuffle(methods)
                blocks.extend([(f,n,seed,effort,0,methods),(f,n,seed,effort,1,methods[::-1])])
    rng.shuffle(blocks)
    manifest=dict(cases=CASES,seeds=SEEDS,efforts=EFFORTS,methods=METHODS,wall=WALL,cap=CAP,
                  repeats=2,python=platform.python_version(),platform=platform.platform(),
                  sources={s:digest(ROOT/s) for s in SOURCES})
    (DEST/'manifest.json').write_text(json.dumps(manifest,indent=2))
    with (DEST/'runs.jsonl').open('x') as out:
        for i,(family,size,seed,effort,repeat,methods) in enumerate(blocks,1):
            p,eps=make(family,size,seed);meta=describe(p)
            for position,method in enumerate(methods):
                row=one(p,eps,seed,method,effort)
                row.update(family=family,size=size,seed=seed,repeat=repeat,position=position,graph=meta)
                out.write(json.dumps(row)+'\n');out.flush()
            print(i,len(blocks),family,size,seed,effort,flush=True)
    (DEST/'complete.json').write_text(json.dumps(dict(rows=4*len(blocks),sha256=digest(DEST/'runs.jsonl'))))

def verify():
    manifest=json.loads((DEST/'manifest.json').read_text())
    for s,h in manifest['sources'].items():
        assert digest(ROOT/s)==h,s

def audit(memory=False):
    verify()
    rows=[json.loads(l) for l in (DEST/'runs.jsonl').read_text().splitlines()]
    filename='memory.jsonl' if memory else 'coupling.jsonl'
    with (DEST/filename).open('x') as out:
        for family,size in CASES:
            for seed in SEEDS:
                group=[r for r in rows if (r['family'],r['size'],r['seed'])==(family,size,seed)]
                steps=max(r['steps'] for r in group)
                p,eps=make(family,size,seed)
                if memory:
                    for method in METHODS:
                        gc.collect();tracemalloc.start()
                        lane=Search(p,seed,method,eps,0)
                        initial=tracemalloc.get_traced_memory()[1]
                        for t in range(steps):
                            if lane.certified or lane.monitor.evidence.conflict:break
                            lane.step()
                        current,peak=tracemalloc.get_traced_memory()
                        count=lane.uct.calls
                        del lane;tracemalloc.stop()
                        out.write(json.dumps(dict(family=family,size=size,seed=seed,method=method,
                              steps=count,initial_peak=initial,peak_bytes=peak,retained_bytes=current))+'\n')
                        out.flush()
                else:
                    lanes=[Search(p,seed,m,eps,0) for m in METHODS]
                    uct=TranspositionUCT(p.graph,exploration=2.);oracle=p.oracle(seed)
                    h=hashlib.sha256();checks=0
                    by_step={}
                    for r in group:by_step.setdefault(r['steps'],[]).append(r)
                    for t in range(1,steps+1):
                        ref=uct.step(oracle)
                        values=[x.step() for x in lanes]
                        assert all(v==ref for v in values),(family,size,seed,t,'path')
                        q=lanes[0].query
                        assert all(x.query==q and x.action==lanes[0].action and x.certified==lanes[0].certified for x in lanes)
                        if t<=8 or t&(t-1)==0 or t==steps or lanes[0].certified:
                            assert q==direct(p.graph,lanes[0].monitor.evidence),(family,size,seed,t,q)
                            checks+=1
                        h.update(repr((ref,q,lanes[0].action,lanes[0].certified)).encode())
                        for r in by_step.get(t,()):
                            lane=lanes[METHODS.index(r['method'])]
                            assert lane.work+3*r['effort']*t==r['work'],(r,lane.work)
                            assert bool(r['certified_at'])==lane.certified
                        if lanes[0].certified:
                            assert t==steps
                    # Same allocator state and same canonical observation counts.
                    for lane in lanes:
                        assert lane.uct.counts==uct.counts
                    out.write(json.dumps(dict(family=family,size=size,seed=seed,steps=steps,
                              checks=checks,sha256=h.hexdigest()))+'\n');out.flush()
                print(filename,family,size,seed,steps,flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--audit',action='store_true')
    parser.add_argument('--memory',action='store_true');parser.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    if args.verify:verify()
    elif args.audit or args.memory:audit(args.memory)
    else:run()

