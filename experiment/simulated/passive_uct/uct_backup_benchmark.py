"""Cold end-to-end UCT timings; observation generation is inside each measured run."""
import gc
import hashlib
import json
import platform
import random
import time
from pathlib import Path

from joint_root_cert._core.onpolicy_backup import MonitoredUCT
from experiment.simulated.passive_uct.uct_backup_families import fixture

ROOT = Path(__file__).resolve().parents[3]
DEST = ROOT/'results/uct_backup_v1'
METHODS = ('eager','live','flat','covers')
SEEDS = tuple(range(421001,421009))
WALL = (.001,.010,.100,.500,2.)
CAP = 200000
CASES = tuple((f,n) for f,sizes in (
    ('two-exit',(16,64,256,1024)),('funnel',(64,256)),('live-best',(64,256)),
    ('fixed-gap',(64,256)),('noisy',(256,)),('core',(8,16,32)),
    ('lattice',(6,)),('merge',(32,))) for n in sizes)
SOURCES = ('paper/uct_backup_protocol.txt','paper/uct_backup_benchmark.py',
           'paper/uct_backup_families.py','dag_mcts/onpolicy_backup.py','dag_mcts/graph.py',
           'dag_mcts/certified_uct.py','dag_mcts/retired_bounds.py','dag_mcts/maintenance_replay.py',
           'dag_mcts/root_flat_control.py','paper/relevance_frontier.py','paper/uniform_selection.py')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run_one(problem,epsilon,seed,method):
    # Collect cycles left by other workloads outside the timed call.
    gc.collect()
    start = time.perf_counter()
    lane = MonitoredUCT(problem,seed,method,epsilon)
    init = time.perf_counter()-start
    checkpoints = []
    previous = (0,0,False)
    def before(elapsed):
        while len(checkpoints)<len(WALL) and WALL[len(checkpoints)]<elapsed:
            checkpoints.append(previous)
    before(init)
    setup_work = lane.work
    if not lane.certified:
        previous = (lane.action,0,False)
    elapsed = init
    while (not lane.certified and not lane.monitor.evidence.conflict and
           lane.uct.calls<CAP and elapsed<WALL[-1]):
        lane.step()
        elapsed = time.perf_counter()-start
        before(elapsed)
        if not lane.certified and not lane.monitor.evidence.conflict:
            previous = (lane.action,lane.uct.calls,False)
    calls,action,cert,work = lane.uct.calls,lane.action,lane.certified,lane.work
    conflict = lane.monitor.evidence.conflict
    bounds = getattr(lane.monitor,'bounds',None)
    messages = getattr(bounds,'messages',None)
    retirements = getattr(bounds,'retired',None)
    nodes = getattr(lane.monitor,'compiled_edges',getattr(lane.monitor,'entries',None))
    del bounds
    release = time.perf_counter()
    del lane
    end = time.perf_counter()-start
    before(end)
    if cert and end<=WALL[-1]:
        previous = (action,calls,True)
    checkpoints.extend([previous]*(len(WALL)-len(checkpoints)))
    values = problem.graph.optimal_values(problem.means)
    children = problem.graph.children[problem.graph.root]
    regrets = [max(0.,values[problem.graph.root]-values[children[a]]) for a,_,_ in checkpoints]
    if cert:
        assert values[problem.graph.root]-values[children[action]]<=epsilon+1e-12
    return dict(steps=calls,work=work,init_work=setup_work,init_seconds=init,
                decision_seconds=elapsed,retire_seconds=end-(release-start),end_seconds=end,
                returned=bool(cert and end<=WALL[-1]),cert_at_step=calls if cert else None,
                restricted=end if cert and end<=WALL[-1] else WALL[-1],conflict=conflict,
                checkpoints=checkpoints,regrets=regrets,messages=messages,retired=retirements,
                compiled_entries=nodes)


def run():
    DEST.mkdir(exist_ok=False)
    order = random.Random(421880)
    blocks = []
    for family,size in CASES:
        for seed in SEEDS:
            methods = list(METHODS)
            order.shuffle(methods)
            blocks.extend(((family,size,seed,0,methods),(family,size,seed,1,methods[::-1])))
    order.shuffle(blocks)
    manifest = dict(cases=CASES,seeds=SEEDS,methods=METHODS,seconds=WALL,rollout_cap=CAP,
                    python=platform.python_version(),platform=platform.platform(),repeats=2,
                    sources={s:digest(ROOT/s) for s in SOURCES})
    (DEST/'manifest.json').write_text(json.dumps(manifest,indent=2))
    with (DEST/'runs.jsonl').open('x') as out:
        for i,(family,size,seed,repeat,methods) in enumerate(blocks,1):
            problem,eps = fixture(family,size,seed)
            for pos,method in enumerate(methods):
                row = run_one(problem,eps,seed,method)
                row.update(family=family,size=size,seed=seed,repeat=repeat,position=pos,
                           method=method,epsilon=eps)
                out.write(json.dumps(row)+'\n')
                out.flush()
            if i%16==0:print(i,'/',len(blocks),flush=True)
    (DEST/'complete.json').write_text(json.dumps(dict(rows=len(blocks)*len(METHODS),
                                        runs=digest(DEST/'runs.jsonl')),indent=2))


if __name__=='__main__':run()
