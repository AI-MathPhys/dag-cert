"""Search for reachable adverse rank prefixes on the two development inputs."""
import json
import random
import struct
from pathlib import Path

from paper.decision_price import ThresholdCompact
from paper.neighbor_price_benchmark import fixtures,config,measured
from paper.probe_credit_benchmark import DEST
from paper.probe_credit import SweepBound
from paper.probe_credit_audit import audit
from paper.uniform_price_benchmark import Tape


class ScriptedRanks:
    def __init__(self,seed):
        self.order=random.Random(seed)
        self.next=None
        self.owner=None
        self.raw=bytearray()

    def randrange(self,n):
        v=self.next
        self.next=None
        if v is None and n==4 and self.owner is not None:
            v=self.owner
        if v is None:v=self.order.randrange(n)
        assert 0<=v<n
        self.raw.extend(struct.pack('<I',v))
        return v


def trace(spec,g,seed,target,mode):
    engine=ThresholdCompact(g,config(spec),seed)
    idx=engine.idx
    leaves=g.graph.leaves
    masks=[sum(1<<a for a,children in enumerate(g.graph.children[1:5]) if j in children) for j in leaves]
    hot=set(sorted(range(len(leaves)),key=lambda j:g.means[leaves[j]],reverse=True)[:2])
    rng=ScriptedRanks(seed)
    weights=[rng.order.random() for j in leaves]
    idx.rng=rng
    for tree,is_lower in ((idx.lt,True),(idx.ut,False)):
        original=tree.select
        def choose(nodes,local_rng,rank=None,*,tree=tree,orig=original,is_lower=is_lower):
            best=max(tree.value[n] for n in nodes)
            indices=[]
            for node in nodes:
                if tree.value[node]!=best:continue
                i=node
                width=1
                while i<tree.size:i*=2;width*=2
                indices.extend(j for j in range(i-tree.size+width-1,i-tree.size-1,-1)
                               if tree.value[tree.size+j]==best)
            if is_lower:
                j=max(indices,key=lambda j:(j not in hot,weights[j]))
                allowed=[a for a in range(4) if masks[j]&(1<<a)]
                # Spend the early sweep drawing both sides of a different cut
                # inside the target; later keep choosing the depleted cut.
                remaining=any(idx.upper[u]==engine.c['K'] and masks[u]&(1<<target) for u in range(len(leaves)))
                favor=[a for a in allowed if (a!=target)==remaining]
                rng.owner=(favor or allowed)[seed%len(favor or allowed)]
            else:
                def priority(j):
                    favored=bool(masks[j]&(1<<target))
                    tiebreak=weights[j] if mode==0 else j if mode==1 else -j
                    return favored,j not in hot,tiebreak
                j=max(indices,key=priority)
            rng.next=indices.index(j)
            return orig(nodes,local_rng,rank)
        tree.select=choose
    engine.query()
    while not engine.point[1] and not engine.ended:
        engine.step(32)
    while not engine.point[1]:
        engine.step(32)
    return bytes(rng.raw)


def run():
    out=DEST/'witness'
    out.mkdir(exist_ok=True)
    report={}
    for s,g in fixtures():
        if s['M'] not in (208,224) or s['layout']!='interleaved':continue
        bound=SweepBound(g,config(s))
        chosen=None
        for seed in (1,2):
            for target in range(4):
                for mode in (0,1,2):
                    data=trace(s,g,seed,target,mode)
                    rec=audit(g,bound,Tape(data),early=False)
                    slack=rec['probes'][0][1]
                    if chosen is None or slack<chosen[0]:chosen=slack,data,rec
        slack,data,rec=chosen
        (out/(s['name']+'.bin')).write_bytes(data)
        rows=[measured(s,g,data,0,m) for m in ('immediate','threshold')]
        assert rows[0]['draws']==rows[1]['draws'] and all(x['status']=='certified' for x in rows)
        report[s['name']]=dict(slack=slack,rec=rec,gap=rows[0]['work']-rows[1]['work'],bytes=len(data))
        print(s['name'],slack,report[s['name']]['gap'],flush=True)
    (out/'summary.json').write_text(json.dumps(report,indent=2))


if __name__=='__main__':
    run()
