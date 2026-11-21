"""Paired index-layout experiment; freeze every prediction before drawing ranks."""
import json
import os
import platform
import random
from unittest.mock import patch

from paper.decision_price_benchmark import config
from paper.structural_price_condition import check
from paper.structural_price_graphs import layout, logical_fixture, switched
from paper.uniform_price_benchmark import BUDGET, DRAWS, SECONDS, METHODS, ROOT, digest, run_one

DEST = ROOT / 'results/structural_price_v1'


def fixtures():
    for i, size in enumerate((176, 176, 192, 192)):
        seed = 394001 + i
        s = dict(family='layout4', A=4, good=2, M=size, seed=seed, eps=1/80,
                 law='constant', profile='sharp', cohort='matched-layout')
        base = logical_fixture(s)
        rng = random.Random(seed + 19000)
        switches = [rng.randrange(2) for _ in range(size//2)]
        for kind in ('spread', 'neighbors', 'short-runs'):
            problem = switched(layout(base, kind), switches)
            yield dict(s, name=f'{seed}-{kind}', layout=kind), problem


def measured(s, problem, tape, tape_id, method):
    with patch('paper.uniform_price_benchmark.factory', return_value=lambda: problem):
        return run_one(s, tape, 395001+tape_id, method)


def run():
    DEST.mkdir(exist_ok=False)
    graphs = list(fixtures())
    predictions = {s['name']: check(g, config(s)) for s, g in graphs}
    (DEST/'predictions.json').write_text(json.dumps(predictions, indent=2))
    sources = ('structural_price_protocol.txt','structural_price_benchmark.py',
               'structural_price_graphs.py','structural_price_condition.py',
               'uniform_price_benchmark.py','decision_price.py','immediate_pricing.py')
    manifest = dict(graphs=[s for s,_ in graphs], tapes=12, methods=METHODS,
                    caps=[BUDGET,DRAWS,SECONDS], python=platform.python_version(),
                    platform=platform.platform(), source={n:digest(ROOT/'paper'/n) for n in sources},
                    predictions=digest(DEST/'predictions.json'))
    (DEST/'manifest.json').write_text(json.dumps(manifest, indent=2))
    tapes = [os.urandom(1<<20) for _ in range(12)]
    used = [0]*len(tapes)
    rng = random.Random(394720)
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
