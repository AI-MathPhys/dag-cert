"""Two hidden regimes with identical support at every canonical leaf."""
import json
import random
from dataclasses import dataclass
from unittest.mock import patch
from dag_mcts.graph import LeafOracle, Problem
from paper.prefix_routing_benchmark import DEST, METHODS, EXTENSIONS, base, problem, RoutedLane


class TwinOracle(LeafOracle):
    def __init__(self,means,seed,values,other,alpha):
        super().__init__(means,seed+710003)
        self.values=values
        self.other=other
        self.alpha=alpha

    def sample(self,leaf):
        x=self.other[leaf] if self.rng[leaf].random()<self.alpha else self.values[leaf]
        self.counts[leaf]+=1
        self.first_reward.setdefault(leaf,x)
        return x


@dataclass(frozen=True,kw_only=True)
class TwinProblem(Problem):
    values:dict
    other:dict
    alpha:float

    def oracle(self,seed):
        return TwinOracle(self.means,seed,self.values,self.other,self.alpha)


def run():
    pair=json.loads((base.DEST/'same_graph.json').read_text())['selected']
    graphs=[problem(pair[k]['spec']) for k in ('a','b')]
    assert graphs[0][0].graph.children==graphs[1][0].graph.children
    rng=random.Random(379321)
    seeds=rng.sample(range(10_000_000,2**31),24)
    blocks=[(a,i,t) for a in (.05,.45) for i in range(2) for t in seeds]
    rng.shuffle(blocks)
    record=dict(blocks=blocks,methods=METHODS,source=base.digest(base.ROOT/'paper/overlap_prefix_benchmark.py'),
                protocol=base.digest(base.ROOT/'paper/overlap_prefix_protocol.txt'))
    with (DEST/'overlap_manifest.json').open('x') as f:json.dump(record,f)
    dest=DEST/'overlap_runs.jsonl'
    with patch.dict(base.ENGINES,EXTENSIONS),patch.object(base,'DecisionLane',RoutedLane),dest.open('x') as out:
        for j,(alpha,i,t) in enumerate(blocks,1):
            p,cfg=graphs[i]
            other=graphs[1-i][0].means
            means={k:(1-alpha)*x+alpha*other[k] for k,x in p.means.items()}
            twin=TwinProblem(p.name,p.graph,means,(),values=p.means,other=other,alpha=alpha)
            order=list(METHODS)
            rng.shuffle(order)
            for pos,m in enumerate(order):
                r=base.solve(lambda:twin,cfg,t,m)
                r.update(tag='overlap',graph=pair['a']['spec']['seed'],shift=(.05,.09)[i],tie=t,
                         noise=str(alpha),method=m,position=pos)
                out.write(json.dumps(r)+'\n')
                out.flush()
            if j%24==0:print(j,'/',len(blocks),'overlap blocks',flush=True)
    (DEST/'overlap_complete.json').write_text(json.dumps(dict(rows=len(blocks)*len(METHODS),sha256=base.digest(dest))))


if __name__=='__main__':
    from paper.overlap_prefix_benchmark import run as package_run
    package_run()
