"""Paid-work, outcome and clustered timing audit for the held-out pre-seal comparison."""
import hashlib
import json
import math
import statistics
from collections import Counter,defaultdict
from fractions import Fraction

import numpy as np

from paper.compact_pre_benchmark import DEST, METHODS, ROOT, config, digest, factory, caseid
from paper.report_compact_side import WORK, WALL
from paper.samegame_gate import exact


def load():
    manifest=json.loads((DEST/'manifest.json').read_text())
    assert all(digest(ROOT/f)==h for f,h in manifest['source'].items())
    specs={caseid(s):s for s in manifest['cases']}
    lines=(DEST/'runs.jsonl').read_text().splitlines()
    stamp=json.loads((DEST/'complete.json').read_text())
    assert stamp['sha256']==digest(DEST/'runs.jsonl') and len(lines)==stamp['records']==len(specs)*4*len(METHODS)
    groups=defaultdict(lambda:defaultdict(dict))
    for line in lines:
        r=json.loads(line)
        g=groups[r['case']][r['repeat']]
        assert r['method'] not in g
        g[r['method']]=r
    return specs,groups


def topology(p):
    return hashlib.sha256(repr(p.graph.children).encode()).hexdigest()


def audit(specs,groups):
    from paper.compact_side_benchmark import factory as earlier
    from paper.compact_side_structural import problem as overlap
    from paper.samegame_gate import game_cases
    old=set()
    boards={tuple(map(tuple,s['board'])) for s in game_cases()}
    for name in ('compact_side_v1','compact_side_overlap_v1','compact_side_repeat_v1'):
        manifest=json.loads((ROOT/'results'/name/'manifest.json').read_text())
        for s in manifest['cases']:
            old.add(topology(earlier(s)() if name=='compact_side_v1' else overlap(s)[0]))
            if 'board' in s:
                boards.add(tuple(map(tuple,s['board'])))
    new_top=defaultdict(set)
    tally=Counter()
    worst=0.
    for k,s in specs.items():
        p=factory(s)()
        part='overlap' if s['family']=='overlap' else 'broad'
        new_top[part].add(topology(p))
        if 'board' in s:
            board=tuple(map(tuple,s['board']))
            assert board not in boards
            values,_=exact(board,s['h'])
            vals=[(v+p.B)/p.scale for v in values]
            eps=Fraction(str(s['eps']))
        else:
            truth=p.graph.optimal_values(p.means)
            vals=[truth[a] for a in p.graph.children[0]]
            eps=s['eps']+1e-12
        assert set(groups[k])==set(range(4))
        for group in groups[k].values():
            assert set(group)==set(METHODS)
            for m,r in group.items():
                a=r['account']
                assert r['work']==r['logical']+r['drop']+a.get('extra',0)-a.get('saved',0)
                assert a.get('saved',0)==a.get('pre_saved',0)+a.get('post_saved',0)
                if r['status']=='certified':
                    assert r['work']<=WORK[-1] and r['seconds']<=WALL[-1] and r['draws']<=262144
                    assert r['box'][1]-r['box'][0]<=round(config(s)['K']*s['eps'])
                    regret=max(vals)-vals[r['action']]
                    assert regret<=eps
                    worst=max(worst,float(regret))
                    tally['certificates']+=1
                else:
                    assert r['box'] is None and r['action'] is None
                if m in ('range','compact'):
                    continue
                ref=group['range' if m in ('fast_range','core_range') else 'compact']
                if r['status'] in ('certified','draw') and ref['status'] in ('certified','draw'):
                    for f in ('status','draws','queries','action','box','meta','logical'):
                        assert r[f]==ref[f],(k,m,f)
                    tally['coupled_endpoints']+=1
    return dict(tally=tally,max_regret=worst,
        distinct={part:len(x) for part,x in new_top.items()},
        overlapping_archived={part:len(x&old) for part,x in new_top.items()})


def paired(groups,specs,method,ref,field):
    by_seed=defaultdict(list)
    all_seeds={specs[k]['seed'] for k in groups}
    for k,reps in groups.items():
        if all(rs[method]['status']==rs[ref]['status']=='certified' for rs in reps.values()):
            ratios=[rs[method][field]/rs[ref][field] for rs in reps.values()]
            by_seed[specs[k]['seed']].append(math.log(statistics.median(ratios)))
    logs=[v for xs in by_seed.values() for v in xs]
    if not logs:
        return dict(joint=0,ratio=None,ci=None,wins=0)
    seeds=sorted(all_seeds)
    sums=np.array([sum(by_seed[s]) for s in seeds])
    counts=np.array([len(by_seed[s]) for s in seeds])
    draw=np.random.default_rng(265901).integers(len(seeds),size=(10000,len(seeds)))
    denom=counts[draw].sum(axis=1)
    keep=denom>0
    ci=(np.exp(np.quantile(sums[draw].sum(axis=1)[keep]/denom[keep],[.025,.975])).tolist()
        if np.count_nonzero(counts)>=2 else None)
    return dict(joint=len(logs),ratio=math.exp(statistics.mean(logs)),ci=ci,wins=sum(x<0 for x in logs))


def summarize(groups,specs):
    methods={}
    for m in METHODS:
        rr=[r[m] for reps in groups.values() for r in reps.values()]
        cc=[r for r in rr if r['status']=='certified']
        first=[r[0][m] for r in groups.values()]
        methods[m]=dict(done=sum(all(r[m]['status']=='certified' for r in reps.values()) for reps in groups.values()),
            work=[sum(r['work']<=b for r in cc) for b in WORK],wall=[sum(r['seconds']<=b for r in cc) for b in WALL],
            restricted=statistics.mean(r['seconds'] if r['status']=='certified' else 12 for r in rr),
            statuses=Counter(r['status'] for r in rr),pre_cases=sum(r['account'].get('pre_hits',0)>0 for r in first),
            counters={f:sum(r['account'].get(f,0) for r in first) for f in ('pre_hits','post_hits','saved','extra','build_work')})
    ratios={}
    for m,ref in [('fast','compact'),('fast','side_compact'),('fast','range'),('fast','core_compact'),
                  ('fast','fast_range'),('fast','miss_only'),('miss_only','side_compact'),('miss_only','compact'),
                  ('core_compact','compact'),('side_compact','compact'),('core_range','range'),
                  ('fast_range','core_range'),('fast_range','range'),('compact','range')]:
        for field in ('work','seconds'):
            ratios[m+'/'+ref+':'+field]=paired(groups,specs,m,ref,field)
    return dict(n=len(groups),methods=methods,ratios=ratios)


def run():
    specs,groups=load()
    info=audit(specs,groups)
    sets={'broad':{k:g for k,g in groups.items() if specs[k]['family']!='overlap'}}
    for fam in {s['family'] for s in specs.values()}:
        sets[fam]={k:g for k,g in groups.items() if specs[k]['family']==fam}
    for eps in (.02,.0125):
        sets['overlap_'+str(eps)]={k:g for k,g in sets['overlap'].items() if specs[k]['eps']==eps}
    report={f:summarize(g,specs) for f,g in sets.items()}
    (DEST/'summary.json').write_text(json.dumps(report,indent=2))
    (DEST/'audit.json').write_text(json.dumps(info,indent=2))
    return info

if __name__=='__main__':
    print(run())

