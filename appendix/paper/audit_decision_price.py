"""Untimed lockstep certification of the threshold-only policy on common budgets."""
import json
from collections import Counter

from paper.audit_compact_side_paths import capture
from paper.decision_price import DecisionLane
from paper.decision_price_benchmark import DEST, population, factory, config, BUDGET, DRAWS, digest


def check(obj, problem=None):
    s=obj['s']
    p=factory(s)() if problem is None else problem
    cfg=config(s)
    build=getattr(p,'build',0)
    r,t=[DecisionLane(p,cfg,obj['tie'],m) for m in ('reference','threshold')]
    streams=[capture(x) for x in (r,t)]
    counts=Counter()
    while not r.point[1] and not r.conflict and r.draws<DRAWS and build+max(r.work,t.work)<BUDGET:
        for lane,buf in zip((r,t),streams):
            buf.clear()
            lane.advance(DRAWS-lane.draws)
        a,b=r.engine,t.engine
        assert r.point==t.point and r.draws==t.draws and streams[0]==streams[1]
        assert r.conflict==t.conflict and a.idx.stats==b.idx.stats and a.idx.q==b.idx.q
        assert a.ended==b.ended and (a.trial is None)==(b.trial is None)
        for key in ('launch','scans','rejects','parks','abort_progress','abort_hard','abort_dense',
                    'seal','decision','phase_work','phase_calls','replays','salvage'):
            assert a.meta.get(key)==b.meta.get(key),(key,obj['case'])
        if not a.ended and a.can_clear:
            low=b.w.total+b.bounds.correction
            assert low<=a.w.total<=low+b.bounds.width
            counts['bill_checks']+=1
        if a.trial is not None:
            lo,hi=b.bounds.interval()
            assert lo<=a.budget<=hi and a.spent==b.spent
            assert (a.trial.todo,a.trial.high,a.trial.retained)==(b.trial.todo,b.trial.high,b.trial.retained)
            counts['private_checks']+=1
        counts['steps']+=1
        counts['draws']+=len(streams[0])
    assert r.engine.idx.rng.getstate()==t.engine.idx.rng.getstate()
    assert r.engine.ev.counts==t.engine.ev.counts and r.engine.ev.sums==t.engine.ev.sums
    assert getattr(r,'private',None)==getattr(t,'private',None)
    for lane in (r,t):
        del lane.oracle.sample
        lane.retire(p,cfg)
    return counts


def run():
    total=Counter()
    out=DEST/'audit.jsonl'
    with out.open('x') as file:
        for i,obj in enumerate(population(),1):
            c=check(obj)
            file.write(json.dumps(dict(case=obj['case'],tag=obj['tag'],counts=c))+'\n')
            total.update(c)
            if i%24==0: print(i,'paired paths',flush=True)
    (DEST/'audit_complete.json').write_text(json.dumps(dict(counts=total,sha256=digest(out)),indent=2))
    print(total,flush=True)


if __name__=='__main__':
    run()
