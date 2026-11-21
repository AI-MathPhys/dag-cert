"""Fresh targeted validation of a funded census; python -m paper.census_rescue_benchmark --out NEW."""
import argparse
import json
import platform
import random
from pathlib import Path
from dag_mcts.graph import Problem
from paper.static_rescue_benchmark import caseid,ROOT,digest
from paper.static_rescue import controller,MODEL_PATH
from paper.frontier_gate_race import solve
from paper.peg_fragment_models import fragmented
from paper.census_rescue import Census

DEFAULT=ROOT/'results/census_rescue_v1'
METHODS=('persistent','compact','static','union','census','retry_all')
def cases():
    for seed in range(274101,274109):
        for m,a,g,e in ((192,4,2,.0125),(128,8,2,1/60),(256,16,1,.0125)):
            for law in (('constant','bernoulli') if a<16 else ('constant',)):
                for profile in ('sharp','shoulder'):
                    yield dict(family='layout'+str(a),seed=seed,M=m,A=a,good=g,eps=e,law=law,profile=profile)
def problem(s):
    p=fragmented(s['seed'],s['good'],1.25*s['eps']/.05,s['law'],s['M'],s['A'])
    if s['profile']=='sharp':return p
    means=dict(p.means);rng=random.Random(s['seed']+4901)
    for leaf in rng.sample([k for k,v in means.items() if v<.3],14):
        means[leaf]=.70-rng.uniform(1.6,2.65)*s['eps']
    return Problem('shoulder',p.graph,means,p.deterministic)
def run(folder):
    model=json.loads(MODEL_PATH.read_text());specs=list(cases())
    folder.mkdir(parents=True,exist_ok=True)
    if any(folder.iterdir()):raise ValueError('Use a fresh output directory')
    paths=json.loads((ROOT/'results/static_rescue_v1/manifest.json').read_text())['source']
    paths=dict.fromkeys(paths)
    for f in ('paper/census_rescue_benchmark.py','paper/census_rescue.py','paper/census_rescue_protocol.txt'):paths[f]=None
    (folder/'manifest.json').write_text(json.dumps(dict(cases=specs,methods=METHODS,source={f:digest(ROOT/f) for f in paths},
        python=platform.python_version(),platform=platform.platform()),indent=2))
    blocks=[]
    for i,s in enumerate(specs):
        order=list(METHODS);random.Random(274901+i).shuffle(order)
        blocks.extend([(s,0,order),(s,1,order[::-1])])
    random.Random(275503).shuffle(blocks)
    with (folder/'runs.jsonl').open('x') as out:
        for i,(s,repeat,order) in enumerate(blocks):
            p=problem(s);cfg=dict(epsilon=s['eps'],delta=.01,cap=12,oracle_cost=1,K=round(1/s['eps'])**4)
            for pos,m in enumerate(order):
                gate=Census(model) if m=='census' else controller(model,m) if m in ('union','retry_all') else None
                r=solve(lambda:p,cfg,s['seed'],m,controller=gate)
                r.update(case=caseid(s),method=m,repeat=repeat,position=pos)
                out.write(json.dumps(r)+'\n');out.flush()
            if (i+1)%16==0:print(i+1,'/',len(blocks),'blocks',flush=True)
    (folder/'complete.json').write_text(json.dumps(dict(records=len(blocks)*len(METHODS),sha256=digest(folder/'runs.jsonl'))))
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=DEFAULT);run(ap.parse_args().out)

