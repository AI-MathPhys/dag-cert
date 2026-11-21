"""Fixed-topology replication. Freeze the design before drawing any new tapes."""
import json
import random
from statistics import mean
from unittest.mock import patch
from dag_mcts.graph import Problem,LeafOracle
from paper.decision_price_benchmark import DEST, ROOT, ENGINES, solve, BUDGET, digest
from paper.decision_price_stress import problem,CreditAtAdmission

METHODS=('reference','threshold','bare','credit','credit-all')
N=32


class MixedOracle(LeafOracle):
    def sample(self,leaf):
        rng=self.rng[leaf]
        mu=self.means[leaf]
        value=float(rng.random()<mu) if rng.random()<.01 else mu
        self.counts[leaf]+=1
        self.first_reward.setdefault(leaf,value)
        return value


class MixedProblem(Problem):
    def oracle(self,seed):
        return MixedOracle(self.means,seed+900001,self.deterministic)


def run():
    selected=json.loads((DEST/'same_graph.json').read_text())['selected']
    s=[selected[key]['spec'] for key in ('a','b')]
    rng=random.Random(361022)
    ties=rng.sample(range(10_000_000,2**31),N)
    groups=[(noise,i,t) for noise in (False,True) for i in range(2) for t in ties]
    rng.shuffle(groups)
    manifest=dict(ties=ties,source=digest(ROOT/'paper/decision_price_holdout.py'),
                  specs=s,mixture=[7,1],methods=METHODS,contamination=[0,.01],
                  estimand='mean signed difference in capped certification loss within seed, with 7:1 law weights')
    path=DEST/'holdout_manifest.json'
    with path.open('x') as f:json.dump(manifest,f,indent=2)
    out=DEST/'holdout.jsonl'
    with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}),out.open('x') as f:
        for i,(noise,law,tie) in enumerate(groups,1):
            p,c=problem(s[law])
            if noise:p=MixedProblem(p.name,p.graph,p.means,p.deterministic)
            order=list(METHODS)
            rng.shuffle(order)
            for pos,m in enumerate(order):
                row=solve(lambda:p,c,tie,m)
                row.update(law=law,tie=tie,noise=noise,method=m,position=pos)
                f.write(json.dumps(row)+'\n')
                f.flush()
            if i%24==0:print(i,'/',len(groups),'holdout blocks',flush=True)
    (DEST/'holdout_complete.json').write_text(json.dumps(dict(rows=5*len(groups),sha256=digest(out))))
    summarize()


def summarize():
    path=DEST/'holdout.jsonl'
    assert digest(path)==json.loads((DEST/'holdout_complete.json').read_text())['sha256']
    rows=[json.loads(l) for l in path.read_text().splitlines()]
    by={(r['noise'],r['tie'],r['law'],r['method']):r for r in rows}
    seeds=json.loads((DEST/'holdout_manifest.json').read_text())['ties']
    assert len(by)==len(rows)==N*len(METHODS)*4
    def loss(r):return r['work'] if r['status']=='certified' else BUDGET
    rng=random.Random(361023)
    resamples=[rng.choices(range(N),k=N) for _ in range(4000)]
    results={}
    for noise in (False,True):
        out={}
        for m in METHODS:
            vals=[];gaps=[];completed=0;seals=0
            for t in seeds:
                rs=[by[noise,t,law,m] for law in range(2)]
                r0=[by[noise,t,law,'reference'] for law in range(2)]
                completed+=sum(r['status']=='certified' for r in rs)
                seals+=sum(r['meta']['seal'] for r in rs)
                vals.append((7*loss(rs[0])+loss(rs[1]))/8)
                gaps.append(vals[-1]-(7*loss(r0[0])+loss(r0[1]))/8)
            boots=sorted(sum(gaps[i] for i in js)/N for js in resamples)
            out[m]=dict(mean_loss=mean(vals),mean_gap=mean(gaps),ci=[boots[99],boots[3899]],
                        certified=completed,seals=seals)
        results[str(noise)]=out
    (DEST/'holdout_summary.json').write_text(json.dumps(results,indent=2))
    print(results,flush=True)


if __name__=='__main__':
    from paper.decision_price_holdout import run as package_run
    package_run()
