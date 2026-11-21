"""Matched external budgets for two prefix selectors and five fixed policies."""
import json
import platform
import random
from dataclasses import replace
from unittest.mock import patch
from paper import decision_price_benchmark as base
from paper.decision_price_stress import problem, CreditAtAdmission
from paper.decision_price_holdout import MixedProblem
from paper.prefix_routing import KnownRangeSelector, OnlineSelector, RoutedLane

DEST=base.ROOT/'results/prefix_routing_v1'
METHODS=('reference','threshold','bare','credit','credit-all','interval','online')
EXTENSIONS={'credit-all':CreditAtAdmission,'interval':KnownRangeSelector,'online':OnlineSelector}


def design():
    rng=random.Random(378851)
    selected=json.loads((base.DEST/'same_graph.json').read_text())['selected']
    original=selected['a']['spec']
    graphs=[('selected',original,rng.sample(range(10_000_000,2**31),24))]
    for i in range(8):
        a=(4,8)[i%2]
        spec=dict(original,seed=378001+i,M=(192 if a==4 else 256),A=a,family=f'layout{a}',
                  profile=('sharp','shoulder')[(i//2)%2])
        graphs.append(('transfer',spec,rng.sample(range(10_000_000,2**31),3)))
    groups=[dict(tag=tag,s=dict(s,shift=shift),noise=noise,tie=tie)
            for tag,s,seeds in graphs for tie in seeds for shift in (.05,.09)
            for noise in ('constant','mixed','bernoulli')]
    rng.shuffle(groups)
    for g in groups:
        order=list(METHODS)
        rng.shuffle(order)
        g['order']=order
    return groups


def make_input(s,noise):
    p,c=problem(s)
    if noise=='mixed':
        p=MixedProblem(p.name,p.graph,p.means,p.deterministic)
    elif noise=='bernoulli':
        p=replace(p,deterministic=())
    return p,c


def run():
    groups=design()
    DEST.mkdir(exist_ok=False)
    names=['prefix_routing.py','prefix_routing_benchmark.py','prefix_routing_protocol.txt']
    man=dict(groups=groups,methods=METHODS,caps=[base.BUDGET,base.DRAWS,base.SECONDS],
             python=platform.python_version(),processor=platform.processor(),
             sources={n:base.digest(base.ROOT/'paper'/n) for n in names},
             parent=base.digest(base.DEST/'manifest.json'))
    (DEST/'manifest.json').write_text(json.dumps(man,indent=2))
    out=DEST/'runs.jsonl'
    with patch.dict(base.ENGINES,EXTENSIONS),patch.object(base,'DecisionLane',RoutedLane),out.open('x') as f:
        for i,g in enumerate(groups,1):
            p,c=make_input(g['s'],g['noise'])
            for pos,m in enumerate(g['order']):
                r=base.solve(lambda:p,c,g['tie'],m)
                r.update(tag=g['tag'],graph=g['s']['seed'],shift=g['s']['shift'],tie=g['tie'],
                         noise=g['noise'],method=m,position=pos)
                f.write(json.dumps(r)+'\n')
                f.flush()
            if i%24==0:print(i,'/',len(groups),'matched cases',flush=True)
    (DEST/'complete.json').write_text(json.dumps(dict(rows=len(groups)*len(METHODS),sha256=base.digest(out))))


if __name__=='__main__':
    from paper.prefix_routing_benchmark import run as package_run
    package_run()
