"""Retrospective, hash-matched stopping diagnostic; no maintenance speed claim."""
import argparse
from collections import defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import time

from dag_mcts.completion_accuracy import trace, sha
from dag_mcts.maintenance_regimes import make_problem

RULES=('original','any_numeric','shared_support')
FOLDERS=('root_completion_frozen','fine_accuracy_frozen')
MATCH=('observations','completed','observations_sha256','publications_sha256',
       'answers_sha256','requests')


class RootRules:
    """Exact integer reference; no reward means enter this evaluator."""
    def __init__(self,g,scale,tolerance):
        self.g,self.scale,self.tolerance=g,scale,tolerance
        self.low=[0]*len(g);self.high=[scale]*len(g)
        self.supports=[None]*len(g);union_inputs=0
        for v in reversed(g.order):
            if not g.children[v]:self.supports[v]=frozenset((v,))
            else:
                union_inputs+=sum(len(self.supports[c]) for c in g.children[v])
                self.supports[v]=frozenset().union(*(self.supports[c] for c in g.children[v]))
        self.actions=g.children[g.root]
        if not self.actions:raise ValueError('Root must have at least one action')
        full=self.supports[g.root]
        self.outside=[full-self.supports[c] for c in self.actions]
        self.structure=dict(nodes=len(g),edges=sum(map(len,g.children)),leaves=len(full),
            root_actions=len(self.actions),support_memberships=sum(map(len,self.supports)),
            support_union_input_visits=union_inputs,
            complement_memberships=sum(map(len,self.outside)),
            action_support_sizes=[len(self.supports[c]) for c in self.actions],
            complement_sizes=list(map(len,self.outside)),
            full_support_actions=[a for a,s in enumerate(self.outside) if not s],
            distinct_root_supports=len({self.supports[c] for c in self.actions}))

    def block(self,pubs):
        for leaf,lo,hi in pubs:
            assert not self.g.children[leaf]
            assert self.low[leaf]<=lo<=hi<=self.high[leaf]
            self.low[leaf],self.high[leaf]=lo,hi
        for v in reversed(self.g.order):
            row=self.g.children[v]
            if row:
                self.low[v]=max(self.low[c] for c in row)
                self.high[v]=max(self.high[c] for c in row)
        ls=[self.low[c] for c in self.actions]
        us=[self.high[c] for c in self.actions]
        candidate=max(range(len(ls)),key=ls.__getitem__)
        # Top two original action uppers retain multiplicities and tied actions.
        order=sorted(range(len(us)),key=lambda a:(-us[a],a))[:2]
        numeric=[];shared=[]
        for a in range(len(ls)):
            rival=(us[order[0]] if order[0]!=a else us[order[1]] if len(order)>1 else 0)
            numeric.append(max(0,rival-ls[a]))
            shared.append(max(0,max((self.high[x] for x in self.outside[a]),default=0)-ls[a]))
        passing=dict(original=([candidate] if numeric[candidate]<=self.tolerance else []),
                     any_numeric=[a for a,x in enumerate(numeric) if x<=self.tolerance],
                     shared_support=[a for a,x in enumerate(shared) if x<=self.tolerance])
        assert all(s<=n for s,n in zip(shared,numeric))
        assert not passing['original'] or passing['any_numeric']
        assert set(passing['any_numeric'])<=set(passing['shared_support'])
        return dict(candidate=candidate,low=ls,upper=us,numeric_gap=numeric,
                    shared_gap=shared,passing=passing)

    def countermodel(self,action):
        """Endpoint assignment realizing the largest root regret for action."""
        s=self.supports[self.actions[action]]
        return {x:self.low[x] if x in s else self.high[x] for x in self.g.leaves}


def cases():
    result=[];inputs={};frozen={}
    for name in FOLDERS:
        folder=Path('results')/name;m=json.loads((folder/'manifest.json').read_text())
        assert m['completed']
        for p,h in m['sources'].items():assert sha(p)==h,p;frozen[p]=h
        for p,h in m['output_sha256'].items():assert sha(folder/p)==h,p
        for p in ('manifest.json','audits.jsonl','runs.jsonl'):inputs[(folder/p).as_posix()]=sha(folder/p)
        byid={c['id']:c for c in m['configurations']};groups=defaultdict(list)
        for line in (folder/'audits.jsonl').read_text().splitlines():
            r=json.loads(line);groups[r['config'],r['seed']].append(r)
        for (cid,seed),rs in groups.items():
            for r in rs:
                for key in MATCH:assert r[key]==rs[0][key],(name,cid,seed,key)
            result.append((name,byid[cid],seed,rs[0]))
    # Priority affects execution order only; every case remains in the analysis.
    result.sort(key=lambda x:(not x[1]['topology'].startswith('lattice'),x[1]['epsilon']!=.05,x[0],x[1]['id'],x[2]))
    return result,inputs,frozen


def diagnose(p,c,seed,reference,checkpoint_sink=None):
    g=p.graph;start=time.perf_counter();rules=RootRules(g,c['scale'],round(c['epsilon']*c['scale']))
    setup_seconds=time.perf_counter()-start
    pre=rules.block([]);first={m:None for m in RULES};counts={m:0 for m in RULES}
    truth=g.optimal_values(p.means);invalid=[];previous={m:set() for m in ('any_numeric','shared_support')}
    checkpoint_hash=hashlib.sha256();scans=0
    for b in reference['blocks']:
        assert g.root in b['queries'];point=rules.block(b['pubs']);step=b['step'];scans+=1
        expected=next(answer for node,answer in b['expected'] if node==g.root)
        assert (point['candidate'],bool(point['passing']['original']))==tuple(expected),(c,seed,step)
        for m in RULES:
            passing=point['passing'][m];counts[m]+=bool(passing)
            if m in previous:
                assert previous[m]<=set(passing);previous[m]=set(passing)
            for a in passing:
                if truth[g.root]-truth[g.children[g.root][a]]>c['epsilon']+1e-12:
                    invalid.append(dict(rule=m,step=step,action=a))
            if passing and first[m] is None:
                a=passing[0]
                first[m]=dict(observations=step,action=a,
                    regret=truth[g.root]-truth[g.children[g.root][a]],
                    numeric_gap=point['numeric_gap'][a],shared_gap=point['shared_gap'][a])
        point.update(step=step,config=c['id'],seed=seed)
        encoded=json.dumps(point,separators=(',',':'))+'\n';checkpoint_hash.update(encoded.encode())
        if checkpoint_sink is not None:checkpoint_sink.write(encoded)
    assert not invalid,invalid[:3]
    assert (first['original'] is not None)==reference['completed']
    if reference['completed']:assert first['original']['observations']==reference['observations']
    for a,b in zip(RULES,RULES[1:]):
        if first[a] is not None:assert first[b] is not None and first[b]['observations']<=first[a]['observations']
    # Independently realize each last-query shared regret using a full MAX DP.
    for a,gap in enumerate(point['shared_gap']):
        vals=g.optimal_values(rules.countermodel(a))
        assert vals[g.root]-vals[g.children[g.root][a]]==gap
    return dict(config=c['id'],seed=seed,topology=c['topology'],epsilon=c['epsilon'],
        scale=c['scale'],delta=c['delta'],grid_margin=c.get('grid_margin'),
        original_horizon=reference['observations'],first=first,root_queries=scans,
        passing_queries=counts,pre_observation_passing=pre['passing'],structure=rules.structure,
        last=point,invalid_certificates=len(invalid),checkpoints_sha256=checkpoint_hash.hexdigest(),
        support_setup_seconds=setup_seconds,
        reference_shared_leaf_reads=scans*rules.structure['complement_memberships'],
        observations_sha256=reference['observations_sha256'],
        publications_sha256=reference['publications_sha256'],original_answers_sha256=reference['answers_sha256'])


def run(out,limit=None):
    items,inputs,frozen=cases()
    if limit is not None:items=items[:limit]
    folder=Path(out);folder.mkdir(parents=True,exist_ok=False)
    sources=dict(frozen)
    for p in ('paper/stopping_diagnostic.py','paper/stopping_diagnostic_protocol.txt','tests/test_stopping_diagnostic.py'):
        sources[p]=sha(p)
    manifest=dict(completed=False,kind='retrospective stopping diagnostic',records=len(items),
        inputs=inputs,sources=sources,rules=RULES,smoke=limit is not None)
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))
    start=time.perf_counter()
    with (folder/'records.jsonl').open('w') as output,gzip.open(folder/'root_checkpoints.jsonl.gz','wt') as checkpoints:
        for i,(name,c,seed,old) in enumerate(items,1):
            p=make_problem(c,seed);ref=trace(p,c,seed,old['observations'])
            for key in MATCH:assert ref[key]==old[key],(name,c['id'],seed,key)
            assert not ref['invalid']
            row=diagnose(p,c,seed,ref,checkpoints);row['cohort']=name
            output.write(json.dumps(row,separators=(',',':'))+'\n');output.flush()
            print(i,'/',len(items),c['id'],seed,'stops',
                  {m:None if x is None else x['observations'] for m,x in row['first'].items()},
                  'elapsed',round(time.perf_counter()-start,1),flush=True)
    manifest.update(completed=True,output_sha256={p.name:sha(p) for p in
                    (folder/'records.jsonl',folder/'root_checkpoints.jsonl.gz')})
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);ap.add_argument('--limit',type=int)
    args=ap.parse_args();run(args.out,args.limit)
