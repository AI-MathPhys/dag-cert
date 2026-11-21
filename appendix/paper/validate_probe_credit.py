"""Independent entropy-prefix audit for the two previously open expectations."""
import argparse
import json
import math
from pathlib import Path

from paper.fragment_sign_audit import RankBits
from paper.neighbor_price_benchmark import fixtures,config
from paper.probe_credit import SweepBound
from paper.probe_credit_audit import audit,exception_floor
from paper.probe_credit_benchmark import DEST,digest


def validate(replay=False):
    dest=DEST/'validation'
    if not replay:
        dest.mkdir(exist_ok=False)
    summaries={}
    for s,g in fixtures():
        if s['M'] not in (208,224) or s['layout']!='interleaved':
            continue
        guard=SweepBound(g,config(s))
        floor=exception_floor(guard,g)
        name=s['name']
        records=dest/(name+'.jsonl')
        bits=dest/(name+'.bin')
        old=records.read_text().splitlines() if replay else None
        packed=bits.read_bytes() if replay else None
        offset=0
        sumlog=0.
        ncovered=0
        first128=0
        sumscore=0
        min_projection=[None,None]
        sweeps=[]
        if not replay:
            out=records.open('x')
            raw=bits.open('xb')
        try:
            for i in range(3000):
                if replay:
                    prior=json.loads(old[i])
                    size=prior['bytes']
                    rng=RankBits(packed[offset:offset+size])
                else:
                    rng=RankBits()
                rec=audit(g,guard,rng)
                data=rng.used()
                rec['bytes']=len(data)
                assert rec['score']>=-floor
                if replay:
                    assert rec==prior and len(data)==size
                else:
                    raw.write(data)
                    out.write(json.dumps(rec)+'\n')
                offset+=len(data)
                n=i+1
                ncovered+=rec['covered']
                if i<128:first128+=rec['covered']
                sweeps.append(rec['sweep'])
                for j in range(2):
                    value=rec['forecast'][j]
                    if min_projection[j] is None or value<min_projection[j]:min_projection[j]=value
                sumscore+=rec['score']
                sumlog+=math.log1p(rec['score']/floor) if rec['score']>-floor else -math.inf
                if n%128==0 or n==3000:
                    lower=floor*math.expm1((sumlog+math.log(.005))/n)
                    if lower>0 or n==3000:break
                    if not replay:
                        out.flush();raw.flush()
            if replay:assert len(old)==n and len(packed)==offset
        finally:
            if not replay:out.close();raw.close()
        summaries[name]=dict(n=n,covered=ncovered,first128_covered=first128,
                             score_mean=sumscore/n,loss_bound=floor,mean_lower=lower,
                             min_projection=min_projection,sweep_range=[min(sweeps),max(sweeps)],
                             records_sha256=digest(records),ranks_sha256=digest(bits))
        print(name,summaries[name],flush=True)
    result=dest/'summary.json'
    if replay:
        assert summaries==json.loads(result.read_text())
    else:
        result.write_text(json.dumps(summaries,indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--replay',action='store_true')
    validate(p.parse_args().replay)
