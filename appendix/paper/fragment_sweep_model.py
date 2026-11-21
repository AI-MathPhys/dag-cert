"""Queues used to bound public blocks in the original deterministic fragmented generator."""
from paper.uniform_price_proof import Leaf
from paper.decision_price_benchmark import config,factory
import math


def queues(spec, limit):
    problem=factory(spec)()
    cfg=config(spec)
    leaves=problem.graph.leaves
    masks=[sum(1<<a for a,children in enumerate(problem.graph.children[1:5]) if j in children)
           for j in leaves]
    profile=[Leaf(problem.means[j],cfg['K'],math.log(len(leaves)/cfg['delta'])) for j in leaves]
    classes=[]
    for mask in sorted(set(masks)):
        members=[i for i,m in enumerate(masks) if m==mask]
        counts={i:0 for i in members}
        for i in members:
            while profile[i].at(counts[i])[1]==cfg['K']:
                counts[i]+=1
        warm=sum(counts.values())
        heads=[]
        for _ in range(limit+1):
            keys=[profile[i].at(counts[i])[1] for i in members]
            high=max(keys)
            assert keys.count(high)==1, 'post-saturation within-class tie'
            j=members[keys.index(high)]
            heads.append((high,j,counts[j]))
            counts[j]+=1
        classes.append(dict(mask=mask,members=members,warm=warm,heads=heads))
    return classes,profile
