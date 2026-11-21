"""Frozen-observation diagnosis followed by sequential equal-compute trials."""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import random
import time

from dag_mcts.completion_accuracy import DPReference,common_init,requests,update_observations,update_answers,sha
from dag_mcts.demand_benchmark import retained_bytes
from dag_mcts.maintenance_regimes import make_problem
from dag_mcts.certified_uct import UCTWork
from paper.stopping_diagnostic import cases,RootRules
from paper.sampling_confidence import GeometricIntervals,Search,METHODS,configurations

WORK_BUDGETS=(250000,1000000,4000000,16000000)
WALL_BUDGETS=(.05,.2,1.,4.)


def sources():
    paths=list(Path('dag_mcts').glob('*.py'))+[Path(x) for x in (
        'paper/sampling_confidence.py','paper/sampling_confidence_benchmark.py',
        'paper/sampling_confidence_protocol.txt','paper/stopping_diagnostic.py',
        'tests/test_sampling_confidence.py')]
    paths+=list(Path('data/uci').glob('*.zip'))
    return {p.as_posix():sha(p) for p in paths}


def diagnose_one(p,c,seed,old):
    g=p.graph;w,sampler,oracle,h,nodes=common_init(p,c,seed)
    geo=GeometricIntervals(g,UCTWork(),c['delta'],c['scale']);e=round(c['epsilon']*c['scale'])
    refs={b:DPReference(g,c['scale'],e,p.means) for b in ('H','G')}
    first={b:None for b in refs};pub_last={b:{} for b in refs}
    obs_hash=hashlib.sha256();pub_hash=hashlib.sha256();ans_hash=hashlib.sha256()
    for base in range(0,old['observations'],c['cadence']):
        step=base+c['cadence'];observations=[];pubs={b:[] for b in refs}
        for _ in range(c['cadence']):
            path,reward=sampler.step(oracle);leaf=path[-1];observations.append((path,reward))
            for b,ev in (('H',h),('G',geo)):
                pair=ev.observe(leaf,reward)
                if ev.conflict:raise ArithmeticError('Diagnostic confidence conflict')
                if pair is not None:pubs[b].append((leaf,*pair));pub_last[b][leaf]=pair
        qs=requests(g,nodes,step,c['cadence'])
        for b,ref in refs.items():
            answers=ref.block(pubs[b],qs)
            if first[b] is None and g.root in ref.cache:
                first[b]=dict(observations=step,action=ref.cache[g.root][0])
            if b=='H':update_answers(ans_hash,step,answers)
        update_observations(obs_hash,observations);pub_hash.update(repr((step,pubs['H'])).encode())
    actual=dict(observations_sha256=obs_hash.hexdigest(),publications_sha256=pub_hash.hexdigest(),
                answers_sha256=ans_hash.hexdigest(),requests=refs['H'].requests)
    for k,v in actual.items():assert v==old[k],(c['id'],seed,k)
    assert bool(first['H'])==old['completed']
    if first['H']:assert first['H']['observations']==old['observations']
    assert all(not r.invalid for r in refs.values())
    details={}
    for b,ev in (('H',h),('G',geo)):
        rules=RootRules(g,c['scale'],e);point=rules.block([(v,*bounds) for v,bounds in pub_last[b].items()])
        a=point['candidate'];support=rules.supports[g.children[g.root][a]]
        witness=max(sorted(support),key=lambda x:rules.low[x])
        blockers=[x for x in rules.outside[a] if rules.high[x]>point['low'][a]+e]
        details[b]=dict(root=point,incumbent_terminal=witness,incumbent_count=ev.counts[witness],
            blockers=[dict(leaf=x,count=ev.counts[x],lower=rules.low[x],upper=rules.high[x],
                           true_mean=p.means[x]) for x in sorted(blockers)],
            evaluations=ev.evaluations,unobserved=sum(ev.counts[x]==0 for x in g.leaves))
    return dict(config=c['id'],seed=seed,topology=c['topology'],epsilon=c['epsilon'],scale=c['scale'],
                delta=c['delta'],horizon=old['observations'],first=first,details=details,
                counts=[[x,h.counts[x]] for x in g.leaves],hashes=actual)


def diagnostic(out,limit=None):
    items,inputs,_=cases()
    if limit is not None:items=items[:limit]
    folder=Path(out);folder.mkdir(parents=True,exist_ok=False)
    m=dict(completed=False,records=len(items),sources=sources(),inputs=inputs,smoke=limit is not None)
    (folder/'manifest.json').write_text(json.dumps(m,indent=2));start=time.perf_counter()
    with (folder/'records.jsonl').open('w') as f:
        for i,(cohort,c,seed,old) in enumerate(items,1):
            r=diagnose_one(make_problem(c,seed),c,seed,old);r['cohort']=cohort
            f.write(json.dumps(r,separators=(',',':'))+'\n');f.flush()
            print('diagnostic',i,'/',len(items),c['id'],seed,r['first'],'elapsed',round(time.perf_counter()-start,1),flush=True)
    m.update(completed=True,output_sha256={'records.jsonl':sha(folder/'records.jsonl')})
    (folder/'manifest.json').write_text(json.dumps(m,indent=2))


def measure(p,c,seed,method):
    start=time.perf_counter();search=Search(p,c,seed,method);elapsed=time.perf_counter()-start
    setup_work=search.total_work;setup_seconds=elapsed
    excluded=(p.graph,search.work)
    if search.sampling in ('uct','lazy_uct'):excluded+= (search.sampler.work,)
    initial_memory=retained_bytes((search.sampler,search.service,search.ev),excluded)
    ref=DPReference(p.graph,c['scale'],round(c['epsilon']*c['scale']),p.means)
    truth=p.graph.optimal_values(p.means);obs_hash=hashlib.sha256();answer_hash=hashlib.sha256()
    wb=WORK_BUDGETS+((64000000,) if c['max_work']>16000000 else ())
    tb=WALL_BUDGETS+((16.,) if c['max_work']>16000000 else ())
    work_points={};wall_points={};previous=None;previous_work=setup_work;previous_time=elapsed
    peak_batch_work=0;steps=0;point=None;cert=False
    while search.total_work<=c['max_work']:
        start=time.perf_counter();pubs,observations,qs,answers,cert=search.block(c['cadence'])
        spent=search.total_work;elapsed+=time.perf_counter()-start
        peak_batch_work=max(peak_batch_work,spent-previous_work);previous_work=spent
        expected=ref.block(pubs,qs);assert answers==expected,(c['id'],seed,method)
        assert not ref.invalid
        update_observations(obs_hash,observations);update_answers(answer_hash,search.calls,answers)
        root_answer=next(answer for v,answer in answers if v==p.graph.root);a=root_answer[0]
        b=search.service.backend;row=p.graph.children[p.graph.root]
        gap=max(0,max((b.upper[v] for i,v in enumerate(row) if i!=a),default=0)-b.lower[row[a]])/c['scale']
        point=dict(observations=search.calls,work=spent,seconds=elapsed,certified=cert,action=a,
                   gap=gap,regret=truth[p.graph.root]-truth[row[a]])
        for budget in wb:
            if str(budget) not in work_points and spent>budget:work_points[str(budget)]=previous
        for budget in tb:
            if str(budget) not in wall_points and elapsed>budget:wall_points[str(budget)]=previous
        previous=point;steps+=1
        if cert:break
    for budget in wb:
        if str(budget) not in work_points:work_points[str(budget)]=point
    for budget in tb:
        if str(budget) not in wall_points:wall_points[str(budget)]=point
    last_work=search.total_work
    assert search.work.oracle_calls==search.calls
    assert last_work<=max(c['max_work']+peak_batch_work,setup_work)
    return dict(config=c['id'],seed=seed,method=method,sampler=search.sampling,bound=search.bound,
        certified=cert,within_max_budget=bool(cert and point['work']<=c['max_work']),
        observations=search.calls,work=last_work,seconds=elapsed,setup_work=setup_work,setup_seconds=setup_seconds,
        max_work=c['max_work'],work_points=work_points,wall_points=wall_points,last=point,
        initial_memory_bytes=initial_memory,memory_bytes=retained_bytes((search.sampler,search.service,search.ev),excluded),
        confidence_evaluations=search.ev.evaluations,counts=[[x,search.ev.counts[x]] for x in p.graph.leaves],
        observations_sha256=obs_hash.hexdigest(),answers_sha256=answer_hash.hexdigest(),
        fields=asdict(search.work),sampler_fields=asdict(search.sampler.work) if search.sampling in ('uct','lazy_uct') else None,
        peak_batch_work=peak_batch_work,requests=ref.requests,invalid=ref.invalid)


def benchmark(out,limit=None):
    folder=Path(out);folder.mkdir(parents=True,exist_ok=False);cs=configurations()
    if limit is not None:cs=cs[:limit]
    m=dict(completed=False,configurations=cs,methods=METHODS,seeds=[107000,107001,107002],
           sources=sources(),work_budgets=WORK_BUDGETS,wall_budgets=WALL_BUDGETS,smoke=limit is not None)
    (folder/'manifest.json').write_text(json.dumps(m,indent=2))
    warm=dict(cs[0],max_work=10000)
    for method in METHODS:measure(make_problem(warm,106999),warm,106999,method)
    jobs=[(c,seed,method) for c in cs for seed in m['seeds'] for method in METHODS]
    random.Random(20261103).shuffle(jobs);start=time.perf_counter()
    with (folder/'runs.jsonl').open('w') as f:
        for i,(c,seed,method) in enumerate(jobs,1):
            p=make_problem(c,seed);r=measure(p,c,seed,method)
            f.write(json.dumps(r,separators=(',',':'))+'\n');f.flush()
            print('benchmark',i,'/',len(jobs),c['id'],seed,method,'done',r['within_max_budget'],
                  'N',r['observations'],'W',r['work'],'s',round(r['seconds'],3),
                  'elapsed',round(time.perf_counter()-start,1),flush=True)
    m.update(completed=True,runs=len(jobs),output_sha256={'runs.jsonl':sha(folder/'runs.jsonl')})
    (folder/'manifest.json').write_text(json.dumps(m,indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=('diagnostic','benchmark','all'),required=True)
    ap.add_argument('--out',required=True);ap.add_argument('--limit',type=int)
    args=ap.parse_args()
    if args.mode=='diagnostic':diagnostic(args.out,args.limit)
    elif args.mode=='benchmark':benchmark(args.out,args.limit)
    else:
        diagnostic(args.out+'_diagnostic',args.limit)
        benchmark(args.out+'_benchmark',args.limit)
