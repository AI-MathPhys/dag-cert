"""Accuracy, realized-time, and replay-to-implementation accounting checks."""
import json
import statistics as st
from collections import Counter,defaultdict
from fractions import Fraction

from paper.batched_repair_benchmark import DEST,METHODS,ROOT,config,caseid,factory,digest
from paper.ancestor_repair_replay import DEST as REPLAY
from paper.report_ancestor_repair import bill
from paper.report_compact_pre import load as old_load,paired,topology,WORK,WALL
from paper.samegame_gate import exact


def load():
    manifest=json.loads((DEST/'manifest.json').read_text())
    assert all(digest(ROOT/f)==h for f,h in manifest['source'].items())
    assert digest(ROOT/'results/compact_pre_v1/runs.jsonl')==manifest['archive']
    specs={caseid(s):s for s in manifest['cases']}
    lines=(DEST/'runs.jsonl').read_text().splitlines()
    stamp=json.loads((DEST/'complete.json').read_text())
    assert digest(DEST/'runs.jsonl')==stamp['sha256'] and len(lines)==stamp['records']==len(specs)*4*len(METHODS)
    groups=defaultdict(lambda:defaultdict(dict))
    for line in lines:
        r=json.loads(line)
        g=groups[r['case']][r['repeat']]
        assert r['method'] not in g
        g[r['method']]=r
    return specs,groups


def audit(specs,groups):
    archived,old=old_load()
    source=REPLAY/'cases.jsonl'
    assert json.loads((REPLAY/'complete.json').read_text())['sha256']==digest(source)
    tapes={(r['case'],r['method']):r for r in map(json.loads,source.read_text().splitlines())}
    hashes=defaultdict(set)
    tally=Counter();worst=0.
    for k,s in specs.items():
        p=factory(s)()
        hashes[s['cohort']].add(topology(p))
        if 'board' in s:
            v,_=exact(tuple(map(tuple,s['board'])),s['h'])
            vals=[(x+p.B)/p.scale for x in v]
            eps=Fraction(str(s['eps']))
        else:
            v=p.graph.optimal_values(p.means)
            vals=[v[a] for a in p.graph.children[p.graph.root]]
            eps=s['eps']+1e-12
        assert set(groups[k])==set(range(4))
        for group in groups[k].values():
            assert set(group)==set(METHODS)
            for m,r in group.items():
                if r['status']=='certified':
                    regret=max(vals)-vals[r['action']]
                    assert regret<=eps and r['work']<=WORK[-1] and r['seconds']<=WALL[-1] and r['draws']<=262144
                    assert r['box'][1]-r['box'][0]<=round(config(s)['K']*s['eps'])
                    worst=max(worst,float(regret));tally['valid_certificates']+=1
                else:
                    assert r['action'] is None and r['box'] is None
                name=m.split('_')[-1]
                if s['cohort']=='archive' and r['status'] in ('draw','certified'):
                    raw=old[k][0]['core_'+name]
                    for f in ('status','queries','draws','action','box','meta'):
                        assert raw[f]==r[f],(k,m,f)
                    if m.startswith('batch'):
                        trace=tapes[k,'core_'+name]
                        setup=32+(2*len(p.graph.children[p.graph.root])+4 if name=='compact' else 0)
                        expected=bill(trace)['strong_bill']+setup+8*trace['ordinary_blocks']+r['drop']-raw['drop']
                        assert r['work']==expected,(k,m,r['work'],expected)
                        tally['exact_replay_bills']+=1
                    else:
                        assert r['work']==raw['work']
                        tally['archived_eager_bills']+=1
            for name in ('compact','range'):
                x,y=group['batch_'+name],group['core_'+name]
                if x['status'] in ('certified','draw') and y['status'] in ('certified','draw'):
                    assert all(x[f]==y[f] for f in ('status','action','box','draws','queries','meta'))
                    tally['paired_outcomes']+=1
    return dict(tally=tally,max_regret=worst,distinct_topologies={k:len(v) for k,v in hashes.items()},
                topology_overlap=len(hashes['archive']&hashes['fresh']))


def summarize(specs,groups):
    result={}
    for name in ('compact','range'):
        base='core_'+name
        batch='batch_'+name
        x=[g[batch] for reps in groups.values() for g in reps.values()]
        y=[g[base] for reps in groups.values() for g in reps.values()]
        joint={k:g for k,g in groups.items() if all(r[batch]['status']==r[base]['status']=='certified' for r in g.values())}
        cpu_joint={k:g for k,g in joint.items() if all(r[batch]['cpu']>0 and r[base]['cpu']>0 for r in g.values())}
        def case_ratio(group,field):
            return st.median(r[batch][field]/r[base][field] for r in group.values())
        med_time=[case_ratio(group,'seconds') for group in joint.values()]
        med_work=[case_ratio(group,'work') for group in groups.values()]
        def meters(rs):
            cc=[r for r in rs if r['status']=='certified']
            return dict(statuses=Counter(r['status'] for r in rs),work=sum(r['work'] for r in rs),
                restricted=st.mean(r['seconds'] if r['status']=='certified' else WALL[-1] for r in rs),
                budgets=[sum(r['work']<=b for r in cc) for b in WORK],
                times=[sum(r['seconds']<=t for r in cc) for t in WALL])
        result[name]=dict(cases=len(groups),eager=meters(y),batch=meters(x),joint=len(joint),
            eager_done=sum(all(r[base]['status']=='certified' for r in reps.values()) for reps in groups.values()),
            batch_done=sum(all(r[batch]['status']=='certified' for r in reps.values()) for reps in groups.values()),
            pooled_work=sum(r['work'] for r in x)/sum(r['work'] for r in y),
            pooled_time=(sum(r[batch]['seconds'] for g in joint.values() for r in g.values())/
                         sum(r[base]['seconds'] for g in joint.values() for r in g.values())) if joint else None,
            median_work=st.median(med_work),median_time=st.median(med_time) if med_time else None,
            ratios={f:paired(cpu_joint if f=='cpu' else groups,specs,batch,base,f)
                    for f in ('work','seconds','cpu')})
    return result


def run():
    specs,groups=load()
    validated=audit(specs,groups)
    sets={}
    for cohort in ('archive','fresh'):
        for part in ('broad','overlap'):
            sets[cohort+'_'+part]={k:v for k,v in groups.items() if specs[k]['cohort']==cohort
                                   and (specs[k]['family']=='overlap')==(part=='overlap')}
        for family in {s['family'] for s in specs.values() if s['cohort']==cohort and s['family']!='overlap'}:
            sets[cohort+'_'+family]={k:v for k,v in groups.items() if specs[k]['cohort']==cohort and specs[k]['family']==family}
        for label,priced in (('active_clock',True),('no_clock',False)):
            sets[cohort+'_'+label]={k:v for k,v in sets[cohort+'_broad'].items()
                if bool(v[0]['batch_compact']['account']['priced_blocks'])==priced}
    summary={k:summarize(specs,g) for k,g in sets.items() if g}
    (DEST/'audit.json').write_text(json.dumps(validated,indent=2))
    (DEST/'summary.json').write_text(json.dumps(summary,indent=2))
    return validated


if __name__=='__main__':
    print(run(),flush=True)

