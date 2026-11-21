"""Fresh entropy tapes for three cold, coupled pricing policies."""
import json
import os
import platform
import random
import struct
import time

from dag_mcts.graph import DAG, Problem
from paper.decision_price import DecisionLane, ENGINES
from paper.immediate_pricing import ImmediateCompact
from paper.decision_price_benchmark import (BUDGET, DRAWS, SECONDS, ROOT, factory, config,
                                            digest, endpoint, status, audit_action)

DEST = ROOT/'results/uniform_price_v1'
METHODS = ('reference', 'immediate', 'threshold')


def interleaved(m, seed):
    """Two non-equivalent supports, one common terminal, two exclusive prospects."""
    order = list(range(m))
    random.Random(seed).shuffle(order)
    sides = [[3+2*j+s for j in range(m)] + [3+2*m] for s in (0,1)]
    graph = DAG([(1,2), *(tuple(s) for s in sides), *([()]*(2*m+1))])
    values = {3+2*j+s: ((.34-.016*s) if i==0 else .02+.14*i/m)
              for j,i in enumerate(order) for s in (0,1)}
    values[3+2*m] = .001
    return Problem('interleaved', graph, values, graph.leaves)


def specs():
    for i,m in enumerate((16,16,24,32)):
        yield dict(name=f'paired-{m}-{381001+i}', family='paired', m=m, seed=381001+i, eps=1/80)
    for i in range(4):
        yield dict(name=f'fragment-{382001+i}',family='layout4',M=224,A=4,good=2,
                   law=('constant','bernoulli')[i%2],profile=('sharp','shoulder')[i//2],
                   seed=382001+i,eps=1/80,cohort='uniform')


class Tape(random.Random):
    """The public tie source. The same charged rank primitive is used in each arm."""
    def __init__(self, data):
        self.data = data
        self.offset = 0

    def randrange(self, n):
        if not 0 < n <= 2**32:
            raise ValueError('invalid tie width')
        cutoff = 2**32 - 2**32 % n
        while True:
            x, = struct.unpack_from('<I',self.data,self.offset)
            self.offset += 4
            if x < cutoff:
                return x % n


def run_one(s,tape,seed,method):
    make = (lambda:interleaved(s['m'],s['seed'])) if s['family']=='paired' else factory(s)
    cfg = config(s)
    start = time.perf_counter()
    p = make()
    lane = DecisionLane.__new__(DecisionLane)
    cls = ImmediateCompact if method=='immediate' else ENGINES[method]
    lane.engine = cls(p,cfg,seed)
    lane.oracle, lane.account = lane.engine.oracle, lane.engine.account
    rng = Tape(tape)
    lane.engine.idx.rng = rng
    lane.point = lane.engine.query()
    lane.peak, lane.seal_at, lane.conflict = 0,None,False
    while (not lane.point[1] and not lane.conflict and getattr(p,'build',0)+lane.work < BUDGET
           and lane.draws < DRAWS and time.perf_counter()-start < SECONDS):
        lane.advance(DRAWS-lane.draws)
    row = endpoint(lane,p,cfg)
    row['seconds'] = time.perf_counter()-start
    row['status'] = status(row,lane.conflict,row['seconds'])
    row['tie_bytes'] = rng.offset
    audit_action(p,row,cfg)
    return row


def run():
    DEST.mkdir(exist_ok=False)
    graphs = list(specs())
    masks = []
    for i in range(16):
        data = os.urandom(1<<20)
        masks.append(data)
    order = random.Random(382911)
    blocks = []
    for s in graphs:
        for i in range(len(masks)):
            methods=list(METHODS)
            order.shuffle(methods)
            blocks.extend([(s,i,0,methods),(s,i,1,methods[::-1])])
    order.shuffle(blocks)
    manifest=dict(graphs=graphs,python=platform.python_version(),caps=[BUDGET,DRAWS,SECONDS],
                  tapes=len(masks),order_seed=382911,source=digest(ROOT/'paper/uniform_price_benchmark.py'))
    (DEST/'manifest.json').write_text(json.dumps(manifest,indent=2))
    used=[0]*len(masks)
    with (DEST/'runs.jsonl').open('x') as out:
        for block,(s,i,r,methods) in enumerate(blocks,1):
            for pos,method in enumerate(methods):
                row=run_one(s,masks[i],383001+i,method)
                used[i]=max(used[i],row['tie_bytes'])
                row.update(graph=s['name'],tape=i,method=method,repeat=r,position=pos)
                out.write(json.dumps(row)+'\n')
                out.flush()
            if block%32==0: print(block,'/',len(blocks),flush=True)
    for i,n in enumerate(used):
        (DEST/f'ties-{i:02}.bin').write_bytes(masks[i][:n])
    (DEST/'complete.json').write_text(json.dumps(dict(rows=3*len(blocks),sha256=digest(DEST/'runs.jsonl'),
        tapes={f'ties-{i:02}.bin':digest(DEST/f'ties-{i:02}.bin') for i in range(len(used))}),indent=2))


if __name__=='__main__':
    run()
