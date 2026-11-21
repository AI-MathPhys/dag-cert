"""Summaries retain cap failures and distinguish joint from all-input endpoints."""
from collections import Counter,defaultdict
import json
from statistics import median
from paper.decision_price_benchmark import DEST, ENGINES, SECONDS, BUDGET, digest


def load():
    man=json.loads((DEST/'manifest.json').read_text())
    stamp=json.loads((DEST/'complete.json').read_text())
    rows=[json.loads(x) for x in (DEST/'runs.jsonl').read_text().splitlines()]
    assert len(rows)==stamp['rows'] and digest(DEST/'runs.jsonl')==stamp['sha256']
    g=defaultdict(lambda:defaultdict(list))
    for r in rows:
        g[r['case']][r['method']].append(r)
    for obj in man['specs']:
        k=obj['case']
        assert set(g[k])==set(ENGINES)
        for m,rr in g[k].items():
            assert sorted(r['repeat'] for r in rr)==list(range(obj['reps']))
            if len(rr)==2:
                assert sum(r['position'] for r in rr)==len(ENGINES)-1
            for r in rr:
                assert r['regret'] is None or r['regret']<=obj['s']['eps']+1e-12
    return man,g


def summarize(specs,g):
    out={}
    keys=[s['case'] for s in specs]
    for m in ENGINES:
        rr=[r for k in keys for r in g[k][m]]
        totals=Counter(r['status'] for r in rr)
        returns=sum(all(x['status']=='certified' for x in g[k][m]) for k in keys)
        out[m]=dict(status=totals,completed=returns,inputs=len(keys),
                    mean_work=sum(r['work'] for r in rr)/len(rr),
                    mean_penalty=sum(r['work'] if r['status']=='certified' else BUDGET for r in rr)/len(rr),
                    restricted_seconds=sum(r['seconds'] if r['status']=='certified' else SECONDS for r in rr)/len(rr),
                    launches=sum(bool(g[k][m][0]['meta']['launch']) for k in keys),
                    seals=sum(bool(g[k][m][0]['meta']['seal']) for k in keys),
                    max_work_overshoot=max(max(0,r['work']-BUDGET) for r in rr))
        if m=='threshold':
            out[m].update(deferred=sum(g[k][m][0]['account']['deferred_groups'] for k in keys),
                          refined=sum(g[k][m][0]['account']['refinements'] for k in keys),
                          refine_inputs=sum(g[k][m][0]['account']['refinements']>0 for k in keys),
                          peak=max(g[k][m][0]['account']['peak_pending'] for k in keys))
    base='reference'
    for m in ENGINES:
        if m==base:continue
        pairs=[(g[k][base],g[k][m]) for k in keys
               if all(r['status']=='certified' for name in (base,m) for r in g[k][name])]
        vals=[(median(x['work'] for x in a),median(x['work'] for x in b)) for a,b in pairs]
        times=[median(x['seconds'] for x in b)/median(x['seconds'] for x in a) for a,b in pairs]
        if vals:
            out[m]['vs_reference']=dict(joint=len(vals),work_ratio=sum(b for a,b in vals)/sum(a for a,b in vals),
                        wins=sum(b<a for a,b in vals),losses=sum(b>a for a,b in vals),
                        median_time_ratio=median(times),faster=sum(t<1 for t in times))
    return out


def main():
    man,g=load()
    cohorts=defaultdict(list)
    for obj in man['specs']:
        cohorts[obj['tag']].append(obj)
        s=obj['s']
        if obj['tag']=='cohort':
            name=s['cohort']+('_overlap' if s['family']=='overlap' else '_broad')
            cohorts[name].append(obj)
        if obj['tag']=='fresh':
            cohorts[s['law']+'_'+s['profile']].append(obj)
    result={k:summarize(v,g) for k,v in cohorts.items()}
    (DEST/'summary.json').write_text(json.dumps(result,indent=2))
    for k in ('cohort','selected','witness-retie','fresh'):
        print(k,[(m,s['completed'],round(s['mean_work']),s['seals']) for m,s in result[k].items()])


if __name__=='__main__':
    main()
