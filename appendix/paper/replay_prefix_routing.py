"""Recreate representative selected routes and the exact prefix-access calculation."""
import json
from collections import Counter
from unittest.mock import patch
from paper.audit_compact_side_paths import capture
from paper.prefix_information import race
from paper.prefix_routing_benchmark import DEST, base, EXTENSIONS, make_input, RoutedLane
from paper.overlap_prefix_benchmark import TwinProblem,problem


def check(p,c,r):
    a=RoutedLane(p,c,r['tie'],r['method'])
    b=RoutedLane(p,c,r['tie'],r['meta']['prefix_route'])
    buf=[capture(x) for x in (a,b)]
    counts=Counter()
    while not a.point[1] and not a.conflict and a.draws<base.DRAWS and max(a.work,b.work)<base.BUDGET:
        for lane,seq in zip((a,b),buf):
            seq.clear()
            lane.advance(base.DRAWS-lane.draws)
        assert a.point==b.point and a.conflict==b.conflict and buf[0]==buf[1]
        assert a.work-b.work==a.account.selector_work
        assert a.engine.idx.rng.getstate()==b.engine.idx.rng.getstate()
        assert a.engine.meta['phase_calls']==b.engine.meta['phase_calls']
        if a.engine.meta['probe_draws'] is not None:
            assert a.engine.route==r['meta']['prefix_route'] and a.engine.meta['inspected']==r['meta']['inspected']
        counts['steps']+=1
        counts['draws']+=len(buf[0])
    for lane in (a,b):del lane.oracle.sample
    new=base.endpoint(a,p,c)
    base.endpoint(b,p,c)
    if r['status']!='wall':
        assert (new['work'],new['draws'])==(r['work'],r['draws'])
    return counts


def main():
    tests={}
    for name in ('runs.jsonl','overlap_runs.jsonl'):
        for l in (DEST/name).read_text().splitlines():
            r=json.loads(l)
            if r['method'] in ('interval','online'):
                key=(r['tag'],r['noise'],r['shift'],r['method'])
                tests.setdefault(key,r)
    manifest=json.loads((DEST/'manifest.json').read_text())
    specs={g['s']['seed']:g['s'] for g in manifest['groups']}
    pair=json.loads((base.DEST/'same_graph.json').read_text())['selected']
    total=Counter()
    with patch.dict(base.ENGINES,EXTENSIONS):
        for r in tests.values():
            s=dict(specs[r['graph']],shift=r['shift'])
            if r['tag']=='overlap':
                i=int(r['shift']==.09)
                p,c=problem(pair[('a','b')[i]]['spec'])
                other=problem(pair[('b','a')[i]]['spec'])[0].means
                alpha=float(r['noise'])
                means={k:(1-alpha)*x+alpha*other[k] for k,x in p.means.items()}
                p=TwinProblem(p.name,p.graph,means,(),values=p.means,other=other,alpha=alpha)
            else:p,c=make_input(s,r['noise'])
            total.update(check(p,c,r))
    assert race()==json.loads((DEST/'race.json').read_text())
    print('cases',len(tests),'same-route checks',dict(total),'exact information/access values verified')
    (DEST/'replay.json').write_text(json.dumps(dict(cases=len(tests),**total)))


if __name__=='__main__':
    main()
