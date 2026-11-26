"""Fresh matched stopping-horizon intervention on the two-exit funnel."""
import argparse
import json
import random
from pathlib import Path
from experiment.simulated.passive_uct.uct_backup_benchmark import ROOT,DEST as PRIMARY,METHODS,WALL,CAP,run_one,digest
from experiment.simulated.passive_uct.audit_uct_backup import coupled
from experiment.simulated.passive_uct.uct_backup_families import funnel

DEST=PRIMARY/'gap-study'
GAPS=(200,75,35)
SEEDS=tuple(range(423001,423009))


def fixture(family,size,seed):
    if family!='gap-test': raise ValueError(family)
    p,_=funnel(256,seed,exits=2,gap=size/1000)
    return p,.025


def run():
    DEST.mkdir(exist_ok=False)
    primary=json.loads((PRIMARY/'manifest.json').read_text())
    assert all(digest(ROOT/s)==h for s,h in primary['sources'].items())
    sources=dict(primary['sources'])
    for name in ('paper/uct_backup_gap.py','paper/uct_backup_gap_protocol.txt','paper/audit_uct_backup.py'):
        sources[name]=digest(ROOT/name)
    (DEST/'manifest.json').write_text(json.dumps(dict(gaps=GAPS,seeds=SEEDS,caps=[CAP,WALL[-1]],sources=sources),indent=2))
    rng=random.Random(423880)
    blocks=[]
    for gap in GAPS:
        for seed in SEEDS:
            order=list(METHODS)
            rng.shuffle(order)
            blocks.extend(((gap,seed,0,order),(gap,seed,1,order[::-1])))
    rng.shuffle(blocks)
    with (DEST/'runs.jsonl').open('x') as out:
        for i,(gap,seed,rep,order) in enumerate(blocks,1):
            p,eps=fixture('gap-test',gap,seed)
            for pos,m in enumerate(order):
                row=run_one(p,eps,seed,m)
                row.update(family='gap-test',size=gap,seed=seed,repeat=rep,method=m,position=pos,epsilon=eps)
                out.write(json.dumps(row)+'\n')
                out.flush()
            if i%8==0:print(i,'/',len(blocks),flush=True)
    (DEST/'complete.json').write_text(json.dumps(dict(rows=len(blocks)*len(METHODS),runs=digest(DEST/'runs.jsonl')),indent=2))


def verify(replay=False):
    man=json.loads((DEST/'manifest.json').read_text())
    assert all(digest(ROOT/s)==v for s,v in man['sources'].items())
    complete=json.loads((DEST/'complete.json').read_text())
    assert complete['runs']==digest(DEST/'runs.jsonl')
    rows=[json.loads(x) for x in (DEST/'runs.jsonl').read_text().splitlines()]
    assert len(rows)==complete['rows']==len(GAPS)*len(SEEDS)*8
    result=[]
    for gap in GAPS:
        for seed in SEEDS:
            group=[r for r in rows if r['size']==gap and r['seed']==seed]
            assert {(r['method'],r['repeat']) for r in group}=={(m,i) for m in METHODS for i in (0,1)}
            result.append(coupled('gap-test',gap,seed,group,fixture))
        print('audited gap',gap/1000,flush=True)
    path=DEST/'coupled.jsonl'
    if replay:
        assert result==[json.loads(x) for x in path.read_text().splitlines()]
    else:
        path.write_text(''.join(json.dumps(r)+'\n' for r in result))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--replay',action='store_true')
    args=parser.parse_args()
    if args.verify or args.replay: verify(args.replay)
    else:run()
