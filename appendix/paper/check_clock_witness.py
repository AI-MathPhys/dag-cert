"""Recheck the constructed finite run against eager repair and both physical clocks."""
import json
from paper.audit_batched_repair_paths import equal
from paper.audit_compact_side_paths import capture
from paper.batched_repair_benchmark import RepairLane
from paper.repair_clock_witness import verify
from paper.repair_policy_clock import DEST, ClockLane, config, factory, BUDGET, DRAWS, digest


def check():
    witness = json.loads((DEST/'construction.json').read_text())['witness']
    assert witness is not None
    s = witness['spec']
    fresh = verify(s)
    assert json.loads(json.dumps(fresh)) == witness
    row = fresh['comparison']
    r,b = row['ends'].values()
    p,cfg = factory(s)(),config(s)
    cfg['cap'] = s.get('frontier_cap',cfg['cap'])
    instance = dict(children=p.graph.children,rewards_hex={k:v.hex() for k,v in p.means.items()},
                    tie_seed=s['seed'],configuration=cfg)
    fixture = DEST/'witness_instance.json'
    fixture.write_text(json.dumps(instance,separators=(',',':')))
    ref = ClockLane(p,cfg,s['seed'],'reference')
    eager = RepairLane(p,cfg,s['seed'],'core_compact')
    streams = [capture(lane) for lane in (ref,eager)]
    steps = draws = 0
    while not ref.point[1] and not ref.conflict:
        assert ref.draws<DRAWS and ref.work+getattr(p,'build',0)<BUDGET
        priced = ref.engine.can_clear and not ref.engine.ended
        for tape,lane in zip(streams,(ref,eager)):
            tape.clear()
            lane.advance(DRAWS-lane.draws)
        equal(ref,eager,priced)
        assert streams[0]==streams[1]
        steps+=1
        draws+=len(streams[0])
    assert draws==r['draws'] and ref.engine.idx.rng.getstate()==eager.engine.idx.rng.getstate()
    totals=[]
    for lane in (ref,eager):
        del lane.oracle.sample
        total = getattr(p,'build',0)+lane.work+lane.retire(p,cfg)
        totals.append(total)
    assert totals[0]==r['work']
    lp,rp = row['shared_probe']
    assert lp['point']==rp['point'] and lp['tie']==rp['tie']
    for g in (lp,rp):
        assert g['budget']==min(2*g['credit'],g['common']//3)
    margins = {}
    for name, ev in zip(('reference','physical'),row['first_branch']):
        if ev['kind']=='private':
            # Doubling handles the half-integer progress term exactly.
            margins[name] = (2*(4*(ev['spent']+26)-ev['budget'])*ev['forecast']
                             - 3*ev['budget']*round(2*ev['progress']))
        else:
            margins[name] = min(ev['budget'],ev['earnings'])-ev['estimate']
    assert margins['reference']<0<margins['physical']
    assert r['work'] < min(b['work'],fresh['unpriced']['work'],totals[1])
    assert row['first_observation']['index']==row['common_draws']+1
    assert r['regret']==b['regret']==fresh['unpriced']['regret']==0
    out=dict(checked_steps=steps,checked_draws=draws,reference=totals[0],fused_eager=totals[1],
             physical=b['work'],physical_unpriced=fresh['unpriced']['work'],guard_margins=margins,
             instance_sha256=digest(fixture),checker_sha256=digest(DEST.parent.parent/'paper/check_clock_witness.py'),
             construction_sha256=digest(DEST/'construction.json'))
    (DEST/'witness_check.json').write_text(json.dumps(out,indent=2))
    print(out)


if __name__ == '__main__':
    check()
