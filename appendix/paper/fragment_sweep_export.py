"""Build compact queue tables for the first-saturation relaxation on a sharp DAG."""
import argparse
import json
import math
from bisect import bisect_right
from pathlib import Path
from paper.fragment_sign_bounds import originals,Supply
from paper.fragment_sweep_model import queues


def export(s,dest):
    model=Supply(s)
    H=1<<model.h
    cs,leaves=queues(s,512)
    covers=[model.e.idx.cover(a) for a in range(4)]
    def lis(side):
        tails=[]
        for node in side:
            first,width=node,1
            while first<H: first*=2; width*=2
            values=set()
            for j in range(first-H,min(model.M,first-H+width)):
                for b in range(1,513):
                    key=leaves[j].at(b)[1]
                    if key<model.K: values.add(key)
                    if key<(model.mu[model.R]-1e-7)*model.K:break
            changes=sorted((bisect_right(tails,key),key) for key in values)
            for idx,key in changes:
                if idx==len(tails):tails.append(key)
                else:tails[idx]=min(tails[idx],key)
        return len(tails)
    ordered_lis=max(sum(lis(side) for side in group) for group in covers)
    warm_floor=hot_floor=0
    penalties=[]
    first_cold={}
    for g in cs:
        counts=[]
        for j in g['members']:
            b=0
            while leaves[j].at(b)[1]==model.K:
                b+=1
                ev=leaves[j].at(b)[3]
                for typ,seq in enumerate(ev):
                    n=len(seq)
                    if n<4:continue
                    margin=4*n-32-4*model.h
                    if typ==1:
                        assert seq[0]==model.K
                        margin=min(7*n-32-4*model.h,4*n-29-model.h)
                    floor=min(0,margin)
                    if model.mu[j]<.3 and b==1 and typ==1:
                        first_cold[j]=[n,min(seq),leaves[j].at(1)[1]]
                    else:hot_floor+=floor
                    if typ==1 and n>=5 and model.mu[j]<.3 and b==1:
                        # Unless one of the last two first visits in its aligned 32-leaf
                        # subtree, a third unvisited upper K strictly clips the low depth.
                        improved=4*n-29-model.h
                        penalties.append(improved-floor)
                        floor=improved
                    warm_floor+=floor
            counts.append(b)
        g['initial']=[list(leaves[j].at(b)[:2]) for j,b in zip(g['members'],counts)]
        g['revision_sum']=[sum(sum(len(leaves[j].at(k)[3][d]) for k in range(1,b+1))
                               for j,b in zip(g['members'],counts)) for d in (0,1)]
        picks=[]
        for high,j,b in g['heads']:
            low2,up2,_,events=leaves[j].at(b+1)
            update=[]
            for seq in events:
                n=len(seq)
                if high >= (model.mu[model.R]-1e-7)*model.K and 4<=n<16:
                    warm_floor+=min(0,4*n-32-4*model.h)
                    hot_floor+=min(0,4*n-32-4*model.h)
                update.append([n,min(seq,default=0),max(seq,default=0)])
            picks.append((high,j,low2,up2,update))
        g['picks']=picks
        del g['heads']
    exceptions=2*math.ceil(model.M/32)
    warm_floor-=sum(sorted(penalties,reverse=True)[:exceptions])
    dest.write_text(json.dumps(dict(Q=512,H=H,h=model.h,M=model.M,K=model.K,lis=ordered_lis,
                                    first_cold=first_cold,hot_floor=hot_floor,
                                    covers=covers,fee=model.cover_fee,hotJoin=(model.W^model.R).bit_length(),
                                    classes=cs,warm_floor=warm_floor)))


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('seed',type=int)
    ap.add_argument('output',type=Path)
    opt=ap.parse_args()
    export(next(s for s in originals() if s['seed']==opt.seed),opt.output)
