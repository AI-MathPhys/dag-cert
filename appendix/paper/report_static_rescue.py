"""Check decisions, counterfactual paths, event recovery, resource caps and paired effects."""
import argparse
import hashlib
import json
import math
import statistics as st
from collections import Counter,defaultdict
from pathlib import Path
import numpy as np
from paper.static_rescue_benchmark import ROOT,DEFAULT,METHODS,caseid,problem,digest

def median(values):return st.median(values) if values else None

def cheaper(a,p):
    if a['status']=='certified' and p['status']=='certified':return a['work']<p['work']
    # Persistent is a protected 32-draw process; the independent physical limit
    # is a multiple of its block size. Ignore cleanup on the censored reference.
    if a['status']=='certified' and p['prefix_or_full_P']>=a['work']:return True
    return None

def seal_win(c,p):
    if c['status']=='certified' and c['base_seal'] is None:return False
    return cheaper(c,p) if c['status']=='certified' and c['base_seal'] is not None else None

def paired(cases,specs,method,reference,field):
    logs={}
    for key,reps in cases.items():
        pairs=[(reps[i][method],reps[i][reference]) for i in (0,1)]
        if all(r['status']=='certified' for pair in pairs for r in pair):
            logs[key]=math.log(st.median([a[field]/b[field] for a,b in pairs]))
    if not logs:return dict(joint=0,ratio=None,ci=None)
    clusters=sorted({specs[k]['seed'] for k in cases})
    obs=defaultdict(list)
    for k,v in logs.items():obs[specs[k]['seed']].append(v)
    sums=np.array([sum(obs[s]) for s in clusters]);nums=np.array([len(obs[s]) for s in clusters])
    sample=np.random.default_rng(265901).integers(len(clusters),size=(10000,len(clusters)))
    ns=nums[sample].sum(axis=1);ok=ns>0
    ci=np.exp(np.quantile(sums[sample].sum(axis=1)[ok]/ns[ok],[.025,.975])).tolist() if sum(nums>0)>=2 else None
    return dict(joint=len(logs),ratio=math.exp(st.mean(logs.values())),ci=ci,wins=sum(v<0 for v in logs.values()))

def admitted(r):return bool(r['gate'] and r['gate']['admit'])

def metrics(cases,specs):
    methods={}
    for m in METHODS:
        rr=[rs[m] for reps in cases.values() for rs in reps.values()]
        cc=[r for r in rr if r['status']=='certified']
        methods[m]=dict(cases_done=sum(all(rs[m]['status']=='certified' for rs in reps.values()) for reps in cases.values()),
                        runs=len(rr),statuses=dict(Counter(r['status'] for r in rr)),
                        restricted=st.mean(r['seconds'] if r['status']=='certified' else 12 for r in rr),
                        seconds=median([r['seconds'] for r in cc]),
                        work_counts=[sum(r['work']<=x for r in cc) for x in (1600000,6400000,25600000,102400000)],
                        wall_counts=[sum(r['seconds']<=x for r in cc) for x in (.1,.5,2,8,12)])
    payoffs={}
    for m in ('static','rescue','geometry','union','retry_all'):
        tally=Counter();prefix=[];draws=[];extra_vs_geom=Counter()
        for key,reps in cases.items():
            rs=reps[0];ref=rs['persistent'];r=rs[m]
            win=seal_win(rs['compact'],ref)
            chosen=admitted(r);old=admitted(rs['static']); added=chosen and not old
            realized=cheaper(r,ref)
            tally['admitted']+=chosen;tally['extra']+=added
            tally['unknown']+=win is None;tally['target']+=win is True
            tally['caught']+=chosen and win is True
            tally['target_added']+=added and win is True
            tally['extra_non_target']+=added and win is False
            tally['extra_unknown']+=added and win is None
            tally['extra_cheaper']+=added and realized is True
            tally['extra_not_cheaper']+=added and realized is False
            tally['extra_unordered']+=added and realized is None
            delivered=r['status']=='certified' and r['lane']=='compact' and r['alt_seal'] is not None and realized is True
            tally['extra_delivered']+=added and delivered
            if added:
                if ref['status']=='certified':prefix.append(r['gate']['prefix_work']/ref['work'])
                draws.append(r['gate']['prefix_draws'])
            if chosen and not admitted(rs['geometry']):
                extra_vs_geom['count']+=1;extra_vs_geom['target']+=win is True
                extra_vs_geom['cheaper']+=realized is True;extra_vs_geom['worse']+=realized is False
                extra_vs_geom['unknown']+=realized is None;extra_vs_geom['delivered']+=delivered
        payoffs[m]=dict(tally=tally,beyond_geometry=extra_vs_geom,median_prefix_fraction=median(prefix),median_extra_draws=median(draws))
    ratios={}
    for m,ref in [('union','static'),('union','persistent'),('union','geometry'),('rescue','static'),('geometry','static'),
                  ('static','persistent'),('retry_all','static'),('compact','persistent'),('union','compact')]:
        for f in ('work','seconds'):ratios[m+'/'+ref+':'+f]=paired(cases,specs,m,ref,f)
    return dict(inputs=len(cases),methods=methods,payoffs=payoffs,ratios=ratios)

def run(folder):
    manifest=json.loads((folder/'manifest.json').read_text());specs={caseid(s):s for s in manifest['cases']}
    for path,h in manifest['source'].items():
        if digest(ROOT/path)!=h:assert digest(folder/'frozen_source'/path)==h
    stamp=json.loads((folder/'complete.json').read_text())
    rows=[json.loads(l) for l in (folder/'runs.jsonl').read_text().splitlines()]
    assert len(rows)==len(specs)*2*len(METHODS)==stamp['records'] and stamp['sha256']==digest(folder/'runs.jsonl')
    groups=defaultdict(lambda:defaultdict(dict))
    for r in rows:
        target=groups[r['case']][r['repeat']];assert r['method'] not in target
        target[r['method']]=r
    checked=protected=static_paths=reference_paths=matched_paths=delayed_bounds=0;worst=0.;maxratio=0.;maxdebt=0.
    profiles={};truth={};fingerprints=set()
    for k,rep in groups.items():
        sp=specs[k];p=problem(sp);v=p.graph.optimal_values(p.means)
        vals=[v[a] for a in p.graph.children[0]]
        good=[j for j,val in enumerate(vals) if max(vals)-val<=sp['eps']+1e-12]
        assert len(good)==sp['good']
        topology=hashlib.sha256(repr(p.graph.children).encode()).hexdigest();fingerprints.add(topology)
        truth[k]=dict(values=vals,good=good,topology=topology)
        if sp['family']=='matched':
            profilekey=(sp['seed'],sp['eps'],sp['law']);fp=(topology,good)
            if profilekey in profiles:assert profiles[profilekey]==fp
            profiles[profilekey]=fp
        for rs in rep.values():
            assert set(rs)==set(METHODS)
            ref=rs['persistent'];static=rs['static']
            for m,r in rs.items():
                ok=r['status']=='certified'
                if ok:
                    gap=max(vals)-vals[r['action']];worst=max(worst,gap);checked+=1
                    assert gap<=sp['eps']+1e-12
                    K=64000 if sp['family']=='wide' else round(1/sp['eps'])**4
                    assert r['box'][1]-r['box'][0]<=round(K*sp['eps'])
                else:assert r['action'] is None and r['box'] is None
                if m in ('persistent','compact'):continue
                assert r['C']<=r['prefix_or_full_P']+r['quantum'] and r['debt']<=r['quantum']
                assert r['fee']<=32 and r['fee']<=r['prefix_or_full_P']/16
                maxdebt=max(maxdebt,r['debt']/max(1,r['prefix_or_full_P']))
                if ok and ref['status']=='certified':
                    assert r['work']<=2.01*ref['work']+52+r['quantum']+r['cdrop']+r['pdrop']
                    if not admitted(r):assert r['work']<=1.01*ref['work']+52
                    protected+=1;maxratio=max(maxratio,r['work']/ref['work'])
                if ok and admitted(static) and m!='static':
                    assert admitted(r)
                    if static['status']=='certified':
                        fields=('work','action','box','C','base_draws','alt_draws','lane','fee')
                        assert all(r[f]==static[f] for f in fields);static_paths+=1
                if ok:
                    winner=ref if r['lane']=='base' else rs['compact']
                    if winner['status']=='certified':
                        draws=r['base_draws'] if r['lane']=='base' else r['alt_draws']
                        assert (r['action'],r['box'],draws)==(winner['action'],winner['box'],winner['base_draws'])
                        reference_paths+=1
                if m=='union':
                    assert admitted(r)==(admitted(rs['rescue']) or admitted(rs['geometry']))
                if m in ('rescue','geometry','union') and r['status']!='wall':
                    base=rs['retry_all'] if admitted(r) and not admitted(static) else static
                    if base['status']!='wall':
                        fields=('status','work','action','box','base_draws','alt_draws','C','fee')
                        assert all(r[f]==base[f] for f in fields);matched_paths+=1
                    if ok and static['status']=='certified' and admitted(r) and not admitted(static):
                        assert r['work']-static['work']<=r['prefix_or_full_P']+r['quantum']+r['cdrop']+r['pdrop']
                        if r['lane']=='base':assert r['work']-static['work']==r['C']+r['cdrop']
                        delayed_bounds+=1
    sets={'all':groups}
    for family in ('wide','middle','narrow','matched'):
        sets[family]={k:v for k,v in groups.items() if specs[k]['family']==family}
    for eps in (.01,.02,.05):
        sets['narrow_'+str(eps)]={k:v for k,v in sets['narrow'].items() if specs[k]['eps']==eps}
    for profile in ('sharp','shoulder'):
        sets['matched_'+profile]={k:v for k,v in sets['matched'].items() if specs[k]['profile']==profile}
    summary={k:metrics(cs,specs) for k,cs in sets.items()}
    flips=Counter()
    for s in specs.values():
        if s.get('profile')!='sharp':continue
        a=groups[caseid(s)][0];b=groups[caseid(dict(s,profile='shoulder'))][0]
        flips['pairs']+=1
        for m in ('union','geometry','rescue'):
            flips[m]+=admitted(a[m])!=admitted(b[m])
        if admitted(a['union'])!=admitted(b['union']):
            for x in (a,b):
                target=seal_win(x['compact'],x['persistent'])
                payoff=cheaper(x['retry_all'],x['persistent'])
                for label,val in (('seal',target),('payoff',payoff)):
                    result='unknown' if val is None else ('correct' if admitted(x['union'])==val else 'incorrect')
                    flips[label+'_'+result]+=1
    (folder/'summary.json').write_text(json.dumps(summary,indent=2))
    (folder/'audit.json').write_text(json.dumps(dict(certificates=checked,worst_regret=worst,paired_bound=protected,
        static_positive_matches=static_paths,reference_winners=reference_paths,max_work_ratio=maxratio,
        max_unfunded_fraction=maxdebt,matched_pairs=flips,matched_schedule_checks=matched_paths,
        delayed_bound_checks=delayed_bounds,distinct_topologies=len(fingerprints),truth=truth),indent=2))
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=DEFAULT);run(ap.parse_args().out)

