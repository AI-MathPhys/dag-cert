"""Anytime-valid graphwise lower bounds on the signed expectation under independent fresh ranks."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import json
import math
from multiprocessing import freeze_support

from paper.fragment_sign_audit import RankBits, audit
from paper.fragment_sign_bounds import originals, bounds
from paper.fragment_sign_benchmark import DEST
from paper.decision_price_benchmark import digest

ALPHA=.01/6
BATCH=32
MAX_SAMPLES=2400
MARGIN=1000


def worker(s):
    rng=RankBits()
    result=audit(s,rng)
    return result,rng.used()


def run():
    directory=DEST/'validation'
    directory.mkdir(exist_ok=False)
    summary=[]
    with ProcessPoolExecutor(max_workers=6) as pool:
        for s in originals():
            g=s['seed'];limits=bounds(s)
            direction=1 if g not in (378004,355003) else -1
            cap=limits['negative_bound' if direction==1 else 'positive_bound']
            logsum=n=0
            log_e=None
            data_path=directory/f'{g}.bin'
            rows_path=directory/f'{g}.jsonl'
            with rows_path.open('x') as out,data_path.open('xb') as stream:
                while n<MAX_SAMPLES:
                    for row,bits in pool.map(worker,[s]*min(BATCH,MAX_SAMPLES-n)):
                        y=max(-cap,row['low'] if direction==1 else -row['high'])
                        assert y>-cap, 'zero betting capital'
                        logsum+=math.log1p(y/cap)
                        row.update(offset=stream.tell(),length=len(bits),score=y)
                        stream.write(bits)
                        out.write(json.dumps(row)+'\n')
                        n+=1
                    lower=cap*math.expm1((logsum+math.log(ALPHA))/n)
                    log_e=logsum-n*math.log1p(MARGIN/cap)
                    if lower>MARGIN:break
                    if n%256==0:print(g,n,round(lower),flush=True)
            summary.append(dict(seed=g,direction=direction,n=n,bounds=limits,lower=lower,log_e=log_e,
                                rows_sha=digest(rows_path),tape_sha=digest(data_path)))
            print('result',g,n,round(lower),flush=True)
            (directory/'summary.json').write_text(json.dumps(summary,indent=2))


def replay():
    directory=DEST/'validation'
    results=json.loads((directory/'summary.json').read_text())
    assert len(results)==6
    for s,r in zip(originals(),results):
        g=s['seed'];b=bounds(s);assert b==r['bounds']
        cap=b['negative_bound' if r['direction']==1 else 'positive_bound']
        path=directory/f'{g}.jsonl';tapefile=directory/f'{g}.bin'
        assert digest(path)==r['rows_sha'] and digest(tapefile)==r['tape_sha']
        rows=[json.loads(line) for line in path.read_text().splitlines()]
        with tapefile.open('rb') as f:
            for i in (0,len(rows)-1):
                x=rows[i];f.seek(x['offset'])
                rng=RankBits(f.read(x['length']))
                assert all(x[k]==v for k,v in audit(s,rng).items())
        scores=[max(-cap,x['low'] if r['direction']==1 else -x['high']) for x in rows]
        assert scores==[x['score'] for x in rows]
        logsum=0.
        for y in scores:
            logsum+=math.log1p(y/cap)
        L=cap*math.expm1((logsum+math.log(ALPHA))/len(scores))
        assert L==r['lower'] and len(rows)==r['n']
    print('checked six graph bounds, sealed transcripts, endpoints, and confidence sequences')


if __name__=='__main__':
    freeze_support()
    parser=argparse.ArgumentParser()
    parser.add_argument('--replay',action='store_true')
    if parser.parse_args().replay:replay()
    else:run()
