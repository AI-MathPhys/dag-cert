"""Prespecified held-out fragmented graph comparison, independent of validation ranks."""
import json
import os
import random
from paper.uniform_price_benchmark import METHODS, ROOT, run_one, digest, BUDGET, DRAWS, SECONDS

DEST=ROOT/'results/fragment_sign_v1'


def specs():
    for i,(size,profile) in enumerate((m,p) for p in ('sharp','shoulder') for m in (192,224,256)):
        seed=389001+i
        yield dict(name=f'{profile}-{size}-{seed}',family='layout4',M=size,A=4,good=2,
                   law='constant',profile=profile,seed=seed,eps=1/80,cohort='fragment-sign')


def run():
    DEST.mkdir(exist_ok=False)
    graphs=list(specs())
    tapes=[os.urandom(1<<20) for _ in range(12)]
    used=[0]*len(tapes)
    rng=random.Random(389721)
    blocks=[]
    for s in graphs:
        for i in range(len(tapes)):
            order=list(METHODS)
            rng.shuffle(order)
            blocks.extend([(s,i,0,order),(s,i,1,order[::-1])])
    rng.shuffle(blocks)
    (DEST/'manifest.json').write_text(json.dumps(dict(graphs=graphs,tapes=len(tapes),
        methods=METHODS,caps=[BUDGET,DRAWS,SECONDS],protocol=digest(ROOT/'paper/fragment_sign_protocol.txt')),indent=2))
    with (DEST/'runs.jsonl').open('x') as out:
        for k,(s,i,rep,order) in enumerate(blocks,1):
            for pos,method in enumerate(order):
                r=run_one(s,tapes[i],390001+i,method)
                used[i]=max(used[i],r['tie_bytes'])
                r.update(graph=s['name'],tape=i,repeat=rep,method=method,position=pos)
                out.write(json.dumps(r)+'\n')
                out.flush()
            if k%24==0:print(k,'/',len(blocks),flush=True)
    for i,n in enumerate(used):
        (DEST/f'ties-{i:02}.bin').write_bytes(tapes[i][:n])
    (DEST/'complete.json').write_text(json.dumps(dict(rows=3*len(blocks),sha256=digest(DEST/'runs.jsonl'),
        tapes={f'ties-{i:02}.bin':digest(DEST/f'ties-{i:02}.bin') for i in range(len(tapes))}),indent=2))


if __name__=='__main__':
    run()
