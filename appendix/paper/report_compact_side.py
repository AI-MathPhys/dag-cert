"""Verify protocol, work decomposition, accuracy and paired held-out outcomes."""
import json
import statistics
from collections import Counter, defaultdict
from fractions import Fraction

from paper.compact_side_benchmark import DEST, METHODS, factory, config, caseid, digest, ROOT
from paper.report_static_rescue import paired
from paper.samegame_gate import exact, game_cases

WORK = (1_600_000,6_400_000,25_600_000,102_400_000)
WALL = (.1,.5,2.,8.,12.)


def load(dest=DEST):
    manifest = json.loads((dest/'manifest.json').read_text())
    for f,h in manifest['source'].items():
        assert digest(ROOT/f)==h,f
    specs = {caseid(s):s for s in manifest['cases']}
    lines = (dest/'runs.jsonl').read_text().splitlines()
    stamp = json.loads((dest/'complete.json').read_text())
    assert len(specs)==len(manifest['cases'])
    assert len(lines)==stamp['records']==len(specs)*len(METHODS)*2
    assert stamp['sha256']==digest(dest/'runs.jsonl')
    groups = defaultdict(lambda:defaultdict(dict))
    for line in lines:
        r=json.loads(line)
        group=groups[r['case']][r['repeat']]
        assert r['method'] not in group
        group[r['method']]=r
    return specs,groups


def audit(specs,groups,make=factory):
    from paper.paused_benchmark import factory as old_factory
    import hashlib
    old=json.loads((ROOT/'results/paused_fresh_v2/manifest.json').read_text())['cases']
    def graph_hash(p):
        return hashlib.sha256(repr(p.graph.children).encode()).hexdigest()
    old_hashes={graph_hash(old_factory(s)()) for s in old}
    old_boards={tuple(map(tuple,s['board'])) for s in old if 'board' in s}
    old_boards.update(tuple(map(tuple,s['board'])) for s in game_cases())
    new_hashes=set()
    tally=Counter()
    worst=0.
    for k,s in specs.items():
        problem=make(s)()
        new_hashes.add(graph_hash(problem))
        if 'board' in s:
            board=tuple(map(tuple,s['board']))
            assert board not in old_boards
            vals,_=exact(board,s['h'])
            vals=[(v+problem.B)/problem.scale for v in vals]
            eps=Fraction(str(s['eps']))
        else:
            truth=problem.graph.optimal_values(problem.means)
            vals=[truth[a] for a in problem.graph.children[problem.graph.root]]
            eps=s['eps']+1e-12
        assert set(groups[k])=={0,1}
        for group in groups[k].values():
            assert set(group)==set(METHODS)
            for m,r in group.items():
                a=r['account']
                assert r['work']==r['logical']+r['drop']+a.get('extra',0)-a.get('saved',0)
                assert a.get('saved',0)==a.get('pre_saved',0)+a.get('post_saved',0)
                if r['status']=='certified':
                    assert r['draws']<=262144 and r['work']<=WORK[-1] and r['seconds']<=12
                    assert r['box'][1]-r['box'][0]<=round(config(s)['K']*s['eps'])
                    regret=max(vals)-vals[r['action']]
                    assert regret<=eps
                    worst=max(worst,float(regret))
                    tally['valid_certificates']+=1
                else:
                    assert r['action'] is None and r['box'] is None
                if not a:
                    continue
                ref=group['range' if m=='side_range' else 'compact']
                if r['status'] in ('certified','draw') and ref['status'] in ('certified','draw'):
                    for key in ('action','box','queries','draws','status','meta','logical'):
                        assert r[key]==ref[key],(k,m,key,r[key],ref[key])
                    assert ref['work']-r['work']==a['saved']-a['extra']-(r['drop']-ref['drop'])
                    tally['equal_endpoints_and_logical_bills']+=1
    assert not (new_hashes & old_hashes)
    return dict(counts=tally,max_regret=worst,distinct_ordered_graphs=len(new_hashes),
                overlap_previous_holdout=len(new_hashes & old_hashes))


def summarize(specs,groups):
    methods={}
    for m in METHODS:
        rr=[group[m] for reps in groups.values() for group in reps.values()]
        cc=[r for r in rr if r['status']=='certified']
        first=[g[0][m] for g in groups.values()]
        methods[m]=dict(done=sum(all(group[m]['status']=='certified' for group in reps.values())
                             for reps in groups.values()),statuses=Counter(r['status'] for r in rr),
            restricted=statistics.mean(r['seconds'] if r['status']=='certified' else 12 for r in rr),
            work=[sum(r['work']<=b for r in cc) for b in WORK],
            wall=[sum(r['seconds']<=b for r in cc) for b in WALL],
            launches=sum(bool(r['meta'].get('launch')) for r in first),
            seals=sum(bool(r['meta'].get('seal')) for r in first),
            pre_cases=sum(r['account'].get('pre_hits',0)>0 for r in first),
            post_cases=sum(r['account'].get('post_hits',0)>0 for r in first),
            counters={f:sum(r['account'].get(f,0) for r in first) for f in
                ('pre_hits','post_hits','saved','extra','pre_saved','post_saved','build_work')})
    ratios={}
    for m,ref in [('compact','range'),('side_compact','compact'),('side_compact','range'),('side_compact','side_range'),
                  ('side_range','range'),('side_compact','pre_only'),('post_only','compact'),('pre_only','compact')]:
        for field in ('work','seconds'):
            ratios[m+'/'+ref+':'+field]=paired(groups,specs,m,ref,field)
    return dict(n=len(groups),methods=methods,ratios=ratios)


def run(overlap=False):
    dest=DEST
    make=factory
    if overlap:
        from paper import compact_side_structural as structure
        dest=structure.DEST
        make=lambda s:lambda:structure.problem(s)[0]
    specs,groups=load(dest)
    results={'all':summarize(specs,groups)}
    for fam in {s['family'] for s in specs.values()}:
        results[fam]=summarize(specs,{k:v for k,v in groups.items() if specs[k]['family']==fam})
    if overlap:
        for eps in sorted({s['eps'] for s in specs.values()}):
            results[str(eps)]=summarize(specs,{k:v for k,v in groups.items() if specs[k]['eps']==eps})
    validation=audit(specs,groups,make)
    (dest/'audit.json').write_text(json.dumps(validation,indent=2))
    (dest/'summary.json').write_text(json.dumps(results,indent=2))
    return validation

if __name__=='__main__':
    import sys
    print(run('--overlap' in sys.argv))

