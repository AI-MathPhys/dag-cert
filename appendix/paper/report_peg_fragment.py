"""Validate exact decisions, summarize paired cold timings, preserve every cap."""
from collections import defaultdict,Counter
from fractions import Fraction
from pathlib import Path
import json
import math
import statistics as st
import numpy as np
from paper.peg_fragment_benchmark import ROOT, cases,name,COMMON,digest
from paper.peg_fragment_models import PegProblem,fragmented,exact_peg

def geometry(c):
    if c['domain']=='peg':
        p=PegProblem(c['board'],c['depth'])
        vals,states=exact_peg(c['board'],c['depth'])
        h0=max(vals);good=sum(h0-v<=Fraction(1,20) for v in vals)
        g=p.graph;tops=[]
        for a in g.children[0]:
            seen={a};todo=[a]
            while todo:
                for z in g.children[todo.pop()]:
                    if z not in seen:seen.add(z);todo.append(z)
            tops.append(seen&set(g.leaves))
        share=sum(sum(j in s for s in tops)>=2 for j in g.leaves)/len(g.leaves)
        return dict(actions=len(vals),good=good,values=list(map(str,vals)),states=states,
                    terminals=len(g.leaves),shared_fraction=share)
    p=fragmented(c['seed'],c['good'],c['gap'],c['group'])
    vs=p.graph.optimal_values(p.means);vals=[vs[a] for a in p.graph.children[0]]
    good=sum(max(vals)-x<=.05 for x in vals)
    if good!=c['good']:raise AssertionError('incorrect construction')
    return dict(actions=len(vals),good=good,values=list(map(str,vals)),terminals=len(p.means))

def ratio(rows,who,ref,field='seconds'):
    paired=defaultdict(dict)
    for r in rows:
        if r['method'] in (who,ref):paired[r['case'],r['repeat']][r['method']]=r
    vals=defaultdict(list); sample={}
    for (k,_),pair in paired.items():
        a,b=pair[who],pair[ref]
        if a['status']==b['status']=='certified':
            vals[k].append(a[field]/b[field])
        sample[k]=a['spec'].get('board',a['spec']['seed'])
    logs={k:math.log(st.median(v)) for k,v in vals.items() if len(v)==2}
    if not logs:return dict(n=0)
    by=defaultdict(list)
    for k,v in logs.items():by[sample[k]].append(v)
    clusters=sorted(set(sample.values()))
    sums=np.array([sum(by[s]) for s in clusters]); ns=np.array([len(by[s]) for s in clusters])
    ix=np.random.default_rng(215903).integers(0,len(clusters),(10000,len(clusters)))
    den=ns[ix].sum(axis=1);ok=den>0
    ci=np.exp(np.quantile(sums[ix].sum(axis=1)[ok]/den[ok],[.025,.975])).tolist() if sum(ns>0)>=2 else None
    return dict(n=len(logs),wins=sum(v<0 for v in logs.values()),gm=math.exp(st.mean(logs.values())),interval=ci)

def summarize(rows):
    methods={}
    for m in sorted({r['method'] for r in rows}):
        rs=[r for r in rows if r['method']==m];cc=[r for r in rs if r['status']=='certified']
        cases=defaultdict(list)
        for r in rs:cases[r['case']].append(r)
        if any(len(v)!=2 for v in cases.values()):raise AssertionError('incomplete pair')
        seals=[r for r in rs if r.get('seal')]
        methods[m]=dict(cases=len(cases),finished=sum(all(a['status']=='certified' for a in v) for v in cases.values()),
                        certified_runs=len(cc),status=dict(Counter(r['status'] for r in rs)),
                        seconds=st.median(r['seconds'] for r in cc) if cc else None,
                        restricted=st.mean(r['seconds'] if r['status']=='certified' else 8. for r in rs),
                        seal_runs=len(seals),sealed_cases=len({r['case'] for r in seals}),
                        seal_sizes=dict(Counter(r['seal']['size'] for r in seals)),
                        post_fraction=st.median(1-r['seal']['draws']/r['draws'] for r in seals) if seals else None,
                        median_draws=st.median(r['draws'] for r in cc) if cc else None,
                        wall=[sum(r['seconds']<=cap for r in cc) for cap in (.1,.5,2,8)],
                        work=None if m=='dp' else [sum(r['work']<=cap for r in cc) for cap in (400000,1600000,6400000,25600000)])
    comparisons={}
    for m in methods:
        if m!='range':
            comparisons[m+'/range']=ratio(rows,m,'range')
            if m!='dp':comparisons[m+'/range:work']=ratio(rows,m,'range','work')
        if m in ('compact','direct'):comparisons[m+'/persistent']=ratio(rows,m,'persistent')
    return dict(methods=methods,ratios=comparisons)

def report(folder):
    rec=[json.loads(l) for l in (folder/'runs.jsonl').read_text().splitlines()]
    stamp=json.loads((folder/'complete.json').read_text())
    assert stamp['records']==len(rec) and stamp['sha256']==digest(folder/'runs.jsonl')
    specs=json.loads((folder/'manifest.json').read_text())['cases']
    truth={name(c):geometry(c) for c in specs}
    comparisons=0;maxerr=0.
    for r in rec:
        t=truth[r['case']];vals=list(map(Fraction,t['values']))
        if r['method']=='dp':assert r['values']==t['values']
        if r['status']=='certified':
            err=max(vals)-vals[r['action']];assert err<=Fraction(1,20);maxerr=max(maxerr,float(err))
            comparisons+=1
        else:assert r['action'] is None
    bypair={(r['case'],r['repeat'],r['method']):r for r in rec}
    coupled=0
    for (k,i,m),r in bypair.items():
        if m=='range':
            b=bypair[k,i,'direct']
            if r['status']==b['status']=='certified':
                assert (r['rng_counts'],r['action'],r['draws'],r['queries'])==(b['rng_counts'],b['action'],b['draws'],b['queries'])
                coupled+=1
    sets={'peg':[r for r in rec if r['spec']['domain']=='peg'],
          'fragment':[r for r in rec if r['spec']['domain']=='fragment']}
    for k in ('opening','midgame','constant','bernoulli'):
        sets[k]=[r for r in rec if r['spec']['group']==k]
    for key in ('depth','gap','good'):
        for val in sorted({r['spec'][key] for r in rec if key in r['spec']}):
            sets[key+str(val)]=[r for r in rec if r['spec'].get(key)==val]
    for d in ('peg','fragment'):
        for m in ('compact','direct'):
            bycase=defaultdict(list)
            for r in sets[d]:
                if r['method']==m:bycase[r['case']].append(r)
            issealed={k for k,rr in bycase.items() if all(r['seal'] for r in rr)}
            for yes in (True,False):
                subset=[r for r in sets[d] if (r['case'] in issealed)==yes]
                if subset:sets[f'{d}:{m}:seal={yes}']=subset
    summary={k:summarize(v) for k,v in sets.items() if v}
    validation=dict(certified=comparisons,max_regret=maxerr,coupled_completed=coupled,geom=truth)
    (folder/'audit.json').write_text(json.dumps(validation,indent=2))
    (folder/'summary.json').write_text(json.dumps(summary,indent=2))
    return summary

if __name__=='__main__':
    import argparse
    arg=argparse.ArgumentParser();arg.add_argument('--out',type=Path,default=ROOT/'results/peg_fragment_v1')
    report(arg.parse_args().out)

