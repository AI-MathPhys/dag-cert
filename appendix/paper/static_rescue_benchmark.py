"""Fresh paired study. python -m paper.static_rescue_benchmark --out NEW"""
import argparse
import json
import platform
import random
from pathlib import Path
from dag_mcts.graph import Problem
from paper.frontier_gate_benchmark import frag
from paper.peg_fragment_models import fragmented
from paper.peg_fragment_benchmark import ROOT,digest
from paper.frontier_gate_race import solve
from paper.static_rescue import MODEL_PATH,controller

DEFAULT=ROOT/'results/static_rescue_v1'
METHODS=('persistent','compact','static','rescue','geometry','union','retry_all')
def cases():
    for seed in range(260101,260109):
        for law in ('constant','bernoulli'):
            for good in (1,4):
                yield dict(family='wide',seed=seed,good=good,eps=.05,law=law)
            yield dict(family='middle',seed=seed,good=2,eps=.025,law=law)
        for good in (1,2):
            for eps in (.05,.02,.01):
                yield dict(family='narrow',seed=seed,good=good,eps=eps,law='constant')
        for eps in (.0125,.025):
            for law in (('constant','bernoulli') if eps==.0125 else ('constant',)):
                for profile in ('sharp','shoulder'):
                    yield dict(family='matched',seed=seed,good=2,eps=eps,law=law,profile=profile)

def caseid(s):
    return '-'.join(str(s[k]) for k in ('family','seed','good','eps','law','profile') if k in s)

def problem(s):
    if s['family']!='matched':return frag(s)
    p=fragmented(s['seed'],2,1.25*s['eps']/.05,s['law'],192,4)
    if s['profile']=='sharp':return p
    means=dict(p.means);rng=random.Random(s['seed']+4901)
    for j in rng.sample([j for j,m in means.items() if m<.3],14):
        means[j]=.70-rng.uniform(1.6,2.65)*s['eps']
    return Problem('shoulder',p.graph,means,p.deterministic)

def run(folder):
    specs=list(cases());model=json.loads(MODEL_PATH.read_text())
    folder.mkdir(parents=True,exist_ok=True)
    if any(folder.iterdir()):raise ValueError('Use a fresh output directory')
    paths=['paper/'+f for f in ('static_rescue.py','static_rescue_model.json','static_rescue_protocol.txt','fit_static_rescue.py',
           'static_rescue_benchmark.py','frontier_gate_benchmark.py','frontier_gate_features.py','frontier_gate_race.py',
           'frontier_gate_model.json','cold_decision_solvers.py','peg_precision.py','peg_fragment_models.py',
           'compact_partial.py','partial_clearing.py','escrow_clearing.py','frontier_sampling.py',
           'relevance_frontier.py','uniform_selection.py','sampling_confidence_allcount.py')]
    paths+=['dag_mcts/graph.py','dag_mcts/certified_uct.py','dag_mcts/retired_bounds.py']
    manifest=dict(cases=specs,methods=METHODS,source={f:digest(ROOT/f) for f in paths},
                  python=platform.python_version(),platform=platform.platform())
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))
    blocks=[]
    for i,s in enumerate(specs):
        order=list(METHODS);random.Random(260901+i).shuffle(order)
        blocks.extend([(s,0,order),(s,1,order[::-1])])
    random.Random(261503).shuffle(blocks)
    with (folder/'runs.jsonl').open('x') as out:
        for i,(s,repeat,order) in enumerate(blocks):
            p=problem(s)
            cfg=dict(epsilon=s['eps'],delta=.01,cap=12,oracle_cost=1,
                     K=64000 if s['family']=='wide' else round(1/s['eps'])**4)
            for pos,method in enumerate(order):
                gate=controller(model,method) if method not in ('persistent','compact','static') else None
                r=solve(lambda:p,cfg,s['seed'],method,controller=gate)
                r.update(case=caseid(s),method=method,repeat=repeat,position=pos)
                out.write(json.dumps(r)+'\n');out.flush()
            if (i+1)%20==0:print(i+1,'/',len(blocks),'blocks',flush=True)
    (folder/'complete.json').write_text(json.dumps(dict(records=len(blocks)*len(METHODS),sha256=digest(folder/'runs.jsonl'))))
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=DEFAULT)
    run(parser.parse_args().out)

