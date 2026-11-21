"""Replay physical draws and cost-sensitive sampler transitions outside the timed runs."""
import json
import sys
from collections import Counter

from paper.compact_side_benchmark import DEST, TimedLane, factory, config, BUDGET, DRAWS
from paper.report_compact_side import load


def capture(lane):
    draws=[]
    oracle=lane.oracle
    ordinary=oracle.sample
    def observe(leaf):
        reward=ordinary(leaf)
        draws.append((leaf,reward))
        return reward
    oracle.sample=observe
    return draws


def equal_state(b,o):
    left,right=b.engine,o.engine
    assert b.point==o.point and left.w==right.w
    assert left.idx.q==right.idx.q and left.idx.revision==right.idx.revision
    assert left.idx.witnesses==right.idx.witnesses and left.idx.stats==right.idx.stats
    assert getattr(left,'meta',None)==getattr(right,'meta',None)
    for key in ('budget','pilot_cost','monitor_cost','next_probe','ended'):
        assert getattr(left,key,None)==getattr(right,key,None)
    lt,rt=getattr(left,'trial',None),getattr(right,'trial',None)
    assert (lt is None)==(rt is None)
    if lt is not None:
        assert (lt.samples,lt.todo,lt.high,lt.retained)==(rt.samples,rt.todo,rt.high,rt.retained)


def replay(overlap=False):
    dest=DEST
    make=factory
    if overlap:
        from paper import compact_side_structural as structure
        dest=structure.DEST
        make=lambda s:lambda:structure.problem(s)[0]
    specs,groups=load(dest)
    tally=Counter()
    for k,s in specs.items():
        prob=make(s)()
        build=getattr(prob,'build',0)
        c=config(s)
        for reference,other in (('compact','side_compact'),('range','side_range')):
            b=TimedLane(prob,c,s['seed'],reference)
            o=TimedLane(prob,c,s['seed'],other)
            bd,od=capture(b),capture(o)
            equal_state(b,o)
            while not b.point[1] and not b.conflict and b.draws<DRAWS and build+max(b.work,o.work)<BUDGET:
                bd.clear()
                od.clear()
                b.advance(DRAWS-b.draws)
                o.advance(DRAWS-o.draws)
                equal_state(b,o)
                assert bd==od and b.draws==o.draws
                tally['matched_steps']+=1
                tally['matched_physical_observations']+=len(bd)
                tally['private_steps']+=int(getattr(b.engine,'trial',None) is not None)
            assert b.engine.idx.rng.getstate()==o.engine.idx.rng.getstate()
            assert b.engine.ev.counts==o.engine.ev.counts and b.engine.ev.sums==o.engine.ev.sums
            assert getattr(b,'private',None)==getattr(o,'private',None)
            for lane,m in ((b,reference),(o,other)):
                raw=groups[k][0][m]
                # The oracle hook is audit-only; do not charge it to a solve.
                del lane.oracle.sample
                if raw['status'] in ('certified','draw') and (lane.point[1] or lane.draws==DRAWS):
                    assert lane.draws==raw['draws'] and lane.engine.idx.q==raw['queries']
                    assert build+lane.work==raw['work']-raw['drop']
                    tally['raw_endpoints']+=1
                lane.retire(prob,c)
            tally['paired_replays']+=1
    (dest/'path_audit.json').write_text(json.dumps(tally,indent=2))
    return tally

if __name__=='__main__':
    print(replay('--overlap' in sys.argv),flush=True)

