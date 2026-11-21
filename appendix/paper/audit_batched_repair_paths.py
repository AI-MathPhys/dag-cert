"""Independent eager/batch lockstep replay outside all wall timers."""
import json
from collections import Counter
from paper.audit_compact_side_paths import capture
from paper.batched_repair_benchmark import RepairLane,DEST,config,factory,BUDGET,DRAWS
from paper.report_batched_repair import load


def equal(b,o,clock):
    left,right=b.engine,o.engine
    assert b.point==o.point and b.conflict==o.conflict
    assert left.idx.q==right.idx.q and left.idx.revision==right.idx.revision
    assert left.idx.witnesses==right.idx.witnesses and left.idx.stats==right.idx.stats
    assert getattr(left,'meta',None)==getattr(right,'meta',None)
    if clock:
        assert left.w==right.w
    for attr in ('budget','pilot_cost','monitor_cost','next_probe','ended'):
        assert getattr(left,attr,None)==getattr(right,attr,None)
    lt,rt=getattr(left,'trial',None),getattr(right,'trial',None)
    assert (lt is None)==(rt is None)
    if lt is not None:
        assert (lt.samples,lt.todo,lt.high,lt.retained)==(rt.samples,rt.todo,rt.high,rt.retained)
    for t in ('ut','lt'):
        a,b_tree=getattr(left.idx,t),getattr(right.idx,t)
        assert a.value==b_tree.value and a.count==b_tree.count


def replay():
    specs,groups=load()
    out=Counter()
    for i,(k,s) in enumerate(specs.items(),1):
        p=factory(s)()
        build=getattr(p,'build',0)
        cfg=config(s)
        for kind in ('compact','range'):
            eager=RepairLane(p,cfg,s['seed'],'core_'+kind)
            batch=RepairLane(p,cfg,s['seed'],'batch_'+kind)
            e,b=capture(eager),capture(batch)
            equal(eager,batch,True)
            while (not eager.point[1] and not eager.conflict and eager.draws<DRAWS
                   and build+max(eager.work,batch.work)<BUDGET):
                e.clear();b.clear()
                priced=batch.engine.can_clear and not batch.engine.ended
                eager.advance(DRAWS-eager.draws)
                batch.advance(DRAWS-batch.draws)
                equal(eager,batch,priced)
                assert e==b and eager.draws==batch.draws
                out['steps']+=1
                out['clock_checked_steps']+=int(priced)
                out['physical_draws']+=len(e)
                out['private_steps']+=int(getattr(eager.engine,'trial',None) is not None)
            assert eager.engine.idx.rng.getstate()==batch.engine.idx.rng.getstate()
            assert eager.engine.ev.counts==batch.engine.ev.counts and eager.engine.ev.sums==batch.engine.ev.sums
            assert getattr(eager,'private',None)==getattr(batch,'private',None)
            for lane,m in ((eager,'core_'+kind),(batch,'batch_'+kind)):
                del lane.oracle.sample
                raw=groups[k][0][m]
                if raw['status'] in ('draw','certified') and (lane.point[1] or lane.draws==DRAWS):
                    assert raw['work']-raw['drop']==build+lane.work
                    assert raw['draws']==lane.draws and raw['queries']==lane.engine.idx.q
                    out['raw_endpoints']+=1
                lane.retire(p,cfg)
            out['paired_replays']+=1
        if i%20==0:print(i,'/',len(specs),'path checks',flush=True)
    (DEST/'path_audit.json').write_text(json.dumps(out,indent=2))
    return out


if __name__=='__main__':
    print(replay(),flush=True)

