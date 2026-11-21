"""Separate feasible overlap family; decisions use the unchanged Compact implementation."""
import json
import platform
import random
from pathlib import Path

from dag_mcts.graph import DAG, Problem
from paper.compact_side_benchmark import ROOT, METHODS, config, run_one, caseid, digest

DEST = ROOT/'results/compact_side_overlap_v1'


def cover_size(bits):
    """Count complete dyadic blocks in a Boolean mask, padding with false leaves."""
    size = 1 << (len(bits)-1).bit_length()
    level = list(bits)+[False]*(size-len(bits))
    count = 0
    while len(level)>1:
        parent=[]
        for x,y in zip(level[::2],level[1::2]):
            count += int(x!=y)
            parent.append(x and y)
        level = parent
    return count+int(level[0])


def problem(s):
    rng = random.Random(s['seed'])
    while True:
        owners=[]
        for group in ((0,), (1,), (0,1))*4:
            owners.extend([group]*rng.randint(7,17))
        sets = [[a in o for o in owners] for a in (0,1)]
        sizes = [cover_size([x==inside for x in bits]) for bits in sets for inside in (True,False)]
        if min(sizes)>=8:
            break
    good = rng.randrange(2)
    best, rival = (rng.choice([j for j,v in enumerate(owners) if v==(a,)]) for a in (good,1-good))
    means = {3+j:rng.uniform(.08,.25) for j in range(len(owners))}
    means[3+best],means[3+rival] = .70,.70-1.25*s['eps']
    rows=[(1,2)]+[tuple(j+3 for j,x in enumerate(bits) if x) for bits in sets]+[()]*len(owners)
    return Problem('overlap',DAG(rows),means,tuple(means)),sizes


def run():
    specs=[dict(family='overlap',seed=seed,eps=eps,law='constant')
           for seed in range(307101,307109) for eps in (.04,.02,.0125)]
    DEST.mkdir(parents=True,exist_ok=True)
    if any(DEST.iterdir()):
        raise ValueError('use an empty output folder')
    paths=json.loads((ROOT/'results/compact_side_v1/manifest.json').read_text())['source']
    sources=dict(paths)
    for f in ('paper/compact_side_structural.py','paper/compact_side_overlap_protocol.txt'):
        sources[f]=digest(ROOT/f)
    assert all(digest(ROOT/f)==h for f,h in sources.items())
    manifest=dict(cases=specs,methods=METHODS,source=sources,platform=platform.platform(),python=platform.python_version())
    (DEST/'manifest.json').write_text(json.dumps(manifest,indent=2))
    blocks=[]
    for i,s in enumerate(specs):
        order=list(METHODS)
        random.Random(308101+i).shuffle(order)
        blocks.extend(((s,0,order),(s,1,order[::-1])))
    random.Random(308909).shuffle(blocks)
    with (DEST/'runs.jsonl').open('x') as out:
        for block,(s,rep,order) in enumerate(blocks,1):
            p,sizes=problem(s)
            for pos,m in enumerate(order):
                r=run_one(lambda:p,config(s),s['seed'],m)
                r.update(method=m,case=caseid(s),repeat=rep,position=pos,cover_sizes=sizes)
                out.write(json.dumps(r)+'\n')
                out.flush()
            if block%12==0:
                print(block,'/',len(blocks),'blocks',flush=True)
    (DEST/'complete.json').write_text(json.dumps(dict(records=len(specs)*2*len(METHODS),
                                        sha256=digest(DEST/'runs.jsonl'))))


if __name__=='__main__':
    run()

