"""Fit only on decisions declined by the frozen static rule, with no fresh cases in memory."""
import hashlib
import json
import statistics as st
import time
from collections import defaultdict
from paper.static_rescue import ROOT,STATIC,SIGNALS,MODEL_PATH,feature,static_choice,review_query
from paper.frontier_gate_race import Lane
from paper.peg_fragment_models import fragmented
from paper.peg_precision import problem as narrow
from paper.frontier_gate_benchmark import frag,caseid
from paper.frontier_gate_features import checkpoint

def rows(positive=False):
    paths={};dataset=[]
    for cohort in ('peg_fragment_v1','peg_precision_v1','frontier_gate_v1'):
        folder=ROOT/'results'/cohort
        path=folder/'runs.jsonl';paths[str(path.relative_to(ROOT))]=hashlib.sha256(path.read_bytes()).hexdigest()
        manifest=json.loads((folder/'manifest.json').read_text())
        if cohort=='frontier_gate_v1':specs={caseid(sp):sp for sp in manifest['cases']}
        grouped=defaultdict(lambda:defaultdict(list))
        for r in map(json.loads,path.read_text().splitlines()):
            if r['method'] in ('compact','persistent'):grouped[r['case']][r['method']].append(r)
        for key,rs in grouped.items():
            sp=specs[key] if cohort=='frontier_gate_v1' else rs['persistent'][0]['spec']
            if 'board' in sp or sp.get('domain')=='peg':continue
            seed=sp['seed']
            if cohort=='peg_fragment_v1':
                p=fragmented(seed,sp['good'],sp['gap'],sp['group']);eps=.05;k=64000
            elif cohort=='peg_precision_v1':
                eps=sp['epsilon'];p=narrow(seed,sp['good'],eps);k=round(1/eps)**4
            else:
                p=frag(sp);eps=sp['eps'];k=64000 if sp['family']=='wide' else round(1/eps)**4
            lane=Lane(p,dict(K=k,epsilon=eps,delta=.01,cap=12,oracle_cost=1),seed,'persistent')
            m=len(p.graph.leaves)
            while not lane.point[1] and lane.engine.idx.q<checkpoint(m):lane.advance(32)
            if lane.point[1] or static_choice(lane)[0]!=positive:continue
            while not positive and not lane.point[1] and lane.engine.idx.q<review_query(m):lane.advance(32)
            if lane.point[1]:continue
            # The counterfactual uses no information about rewards at selection time.
            # Censored persistent costs are lower bounds without the disposal tariff.
            def cost(r):return r['work'] if r['status']=='certified' else r.get('prefix_or_full_P',r['work'])
            pw=st.median(cost(r) for r in rs['persistent'])
            cw=st.median(cost(r) for r in rs['compact'])
            cdone=all(r['status']=='certified' for r in rs['compact'])
            sealed=all((r.get('seal') is not None if 'seal' in r else r.get('base_seal') is not None) for r in rs['compact'])
            proxy=min(2*pw,cw+max(cw,lane.work)) if cdone else 2*pw
            known=cdone and (not sealed or all(r['status']=='certified' for r in rs['persistent']) or cw<pw)
            dataset.append(dict(cohort=cohort,seed=seed,key=key,gain=1-proxy/pw,known=known,
                profitable=bool(cdone and sealed and cw<pw),
                features={f:feature(lane,f) for f in STATIC+SIGNALS}))
    return dataset,paths

def fit(data,dynamic):
    # A rescue is allowed only with actual early evidence on its decision path.
    keys=STATIC+SIGNALS if dynamic else STATIC
    def visit(sub,depth,has_evidence):
        mass=sum(r['gain']-.04 for r in sub)
        supported=len(sub)>=6 and len({r['seed'] for r in sub})>=3 and sum(r['profitable'] for r in sub)*2>=len(sub)
        allow=supported and (has_evidence or not dynamic) and mass>0
        best=(mass if allow else 0,{'admit':allow,'n':len(sub)})
        if depth==0 or len(sub)<12:return best
        for k in keys:
            # For fixed training rows the midpoints give the same partitions
            # as their left endpoints, with less sensitivity to integer counts.
            vals=sorted({r['features'][k] for r in sub})
            for a,b in zip(vals,vals[1:]):
                t=(a+b)/2
                low=[r for r in sub if r['features'][k]<=t];high=[r for r in sub if r['features'][k]>t]
                if min(len(low),len(high))<6:continue
                l=visit(low,depth-1,has_evidence or k in SIGNALS);h=visit(high,depth-1,has_evidence or k in SIGNALS)
                score=l[0]+h[0]-.30
                if score>best[0]+1e-9:
                    best=(score,dict(feature=k,threshold=t,left=l[1],right=h[1]))
        return best
    return visit(data,2,False)[1]

def fit_veto(data):
    best=(0,{'admit':False,'n':len(data)})
    for k in SIGNALS:
        values=sorted({r['features'][k] for r in data})
        for a,b in zip(values,values[1:]):
            t=(a+b)/2
            for left in (True,False):
                subset=[r for r in data if (r['features'][k]<=t)==left]
                if len(subset)<6 or len({r['seed'] for r in subset})<3:continue
                if any(not r['known'] or r['profitable'] for r in subset):continue
                score=sum(-r['gain']-.04 for r in subset)-.3
                if score>best[0]+1e-9:best=(score,dict(feature=k,threshold=t,left={'admit':left},right={'admit':not left}))
    return best[1]

def main():
    start=time.perf_counter();data,paths=rows();pos,_=rows(True);t=time.perf_counter()
    model=dict(sources=paths,review_cases=len(data),static_yes_cases=len(pos),rescue=fit(data,True),geometry=fit(data,False),veto=fit_veto(pos))
    MODEL_PATH.write_text(json.dumps(model,indent=2))
    print(json.dumps(model,indent=2));print('replay, fit seconds',t-start,time.perf_counter()-t)
if __name__=='__main__':main()

