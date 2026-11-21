"""Matched neighboring prospects, with a common logical problem in each pair."""
import json
import os
import platform
import random
from paper.structural_price_benchmark import measured
from paper.neighbor_price_condition import predict

from paper.decision_price_benchmark import config
from paper.structural_price_graphs import layout, logical_fixture, switched
from paper.uniform_price_benchmark import BUDGET, DRAWS, SECONDS, METHODS, ROOT, digest

DEST = ROOT / 'results/neighbor_price_v1'


def fixtures():
    for i, size in enumerate((160,176,184,192,208,224)):
        seed = 403001+i
        s = dict(family='layout4', A=4, good=2, M=size, seed=seed, eps=1/80,
                 law='constant', profile='sharp', cohort='fixed-neighbors')
        base = logical_fixture(s)
        rng = random.Random(seed+31000)
        switches = [rng.randrange(2) for _ in range(size//2)]
        for label, ordering in (('interleaved',base),('short-runs',layout(base,'short-runs'))):
            graph = switched(layout(ordering,'neighbors'),switches)
            ranks = sorted(range(size),key=lambda j:graph.means[graph.graph.leaves[j]],reverse=True)
            assert ranks[0]^ranks[1]==1
            yield dict(s,name=f'{seed}-{label}',layout=label),graph


def run():
    DEST.mkdir(exist_ok=False)
    graphs = list(fixtures())
    predictions = {s['name']: predict(g, config(s)) for s, g in graphs}
    (DEST/'predictions.json').write_text(json.dumps(predictions, indent=2))
    sources = ('neighbor_price_protocol.txt','neighbor_price_benchmark.py','neighbor_price_condition.py',
               'structural_price_benchmark.py','uniform_price_proof.py',
               'structural_price_graphs.py','structural_price_condition.py',
               'uniform_price_benchmark.py','decision_price.py','immediate_pricing.py')
    manifest = dict(graphs=[s for s,_ in graphs], tapes=12, methods=METHODS,
                    caps=[BUDGET,DRAWS,SECONDS], python=platform.python_version(),
                    platform=platform.platform(), source={n:digest(ROOT/'paper'/n) for n in sources},
                    predictions=digest(DEST/'predictions.json'))
    (DEST/'manifest.json').write_text(json.dumps(manifest, indent=2))
    tapes = [os.urandom(1<<20) for _ in range(12)]
    used = [0]*len(tapes)
    rng = random.Random(403720)
    blocks = []
    for s, graph in graphs:
        for i in range(len(tapes)):
            order = list(METHODS)
            rng.shuffle(order)
            blocks.extend(((s,graph,i,0,order),(s,graph,i,1,order[::-1])))
    rng.shuffle(blocks)
    with (DEST/'runs.jsonl').open('x') as out:
        for b,(s,graph,i,r,order) in enumerate(blocks,1):
            for pos,m in enumerate(order):
                row = measured(s,graph,tapes[i],i,m)
                used[i] = max(used[i],row['tie_bytes'])
                row.update(graph=s['name'],method=m,tape=i,repeat=r,position=pos)
                out.write(json.dumps(row)+'\n')
                out.flush()
            if b%32==0: print(b,'/',len(blocks),flush=True)
    for i,n in enumerate(used):
        (DEST/f'ties-{i:02}.bin').write_bytes(tapes[i][:n])
    (DEST/'complete.json').write_text(json.dumps(dict(rows=3*len(blocks),
        runs=digest(DEST/'runs.jsonl'), tapes={f'ties-{i:02}.bin':digest(DEST/f'ties-{i:02}.bin')
        for i in range(len(used))}),indent=2))


if __name__=='__main__':
    run()
