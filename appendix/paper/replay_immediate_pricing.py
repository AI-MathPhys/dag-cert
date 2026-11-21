"""Finite reachability proof and interval checker, outside the timed benchmark."""
import json
import math
from collections import Counter
from contextlib import ExitStack
from unittest.mock import patch

from paper.audit_compact_side_paths import capture
from paper.audit_batched_repair_paths import equal
from paper.decision_price import DecisionLane, ENGINES
from paper.decision_price_benchmark import BUDGET, DRAWS, config, digest, endpoint, factory
from paper.repair_policy_clock import audit_action
from paper.escrow_clearing import GuardedSearch
from paper.immediate_pricing import ImmediateCompact, ImmediateTree
from paper.immediate_pricing_benchmark import DEST, inputs
from paper.index_repayment_audit import Audit
from paper.partial_clearing import PartialTrial


def noise_cell(value, limit, forecast_uses, parking_uses, cfg, terminals):
    """Enclose every reward prefix at one sampled leaf by the two extreme streams."""
    scale, eps = cfg['K'], cfg['epsilon']
    log_ratio = math.log(terminals/cfg['delta'])
    radius = 2.0**-32
    while radius >= 2.0**-48:
        signals = [value-radius, value+radius]
        sums = [0., 0.]
        lows, highs = [0., 0.], [1., 1.]
        mean_bounds = {}
        stable = 0 < signals[0] < signals[1] < 1
        for n in range(1, limit+1):
            r = math.sqrt((n+1)/(2*n*n)*(log_ratio+.5*math.log1p(n)))
            keys, means = [], []
            for i, signal in enumerate(signals):
                sums[i] += signal
                mean = sums[i]/n
                means.append(mean)
                lows[i] = max(lows[i], mean-r, 0.)
                highs[i] = min(highs[i], mean+r, 1.)
                keys.append((max(0, math.floor(math.nextafter(scale*lows[i], -math.inf))),
                             min(scale, math.ceil(math.nextafter(scale*highs[i], math.inf)))))
            mean_bounds[n] = means
            if keys[0] != keys[1] or lows[1] > highs[0]:
                stable = False
                break
        if stable:
            for n, theta, public in [(*key, True) for key in forecast_uses] + [
                    (*key, False) for key in parking_uses]:
                a, b = mean_bounds[n]
                # Include theta if interior, since the absolute gap changes monotonicity there.
                values = [a, b] + ([theta] if a < theta < b else [])
                outputs = []
                for mean in values:
                    gap = max(abs(mean-theta)-1/scale, eps/4)
                    logarithm = math.log1p(max(32,n) if public else n)
                    target = math.ceil((log_ratio+.5*logarithm)/(2*gap*gap))
                    outputs.append((mean >= theta-eps, target))
                if len(set(outputs)) != 1:
                    stable = False
                    break
        if stable:
            return radius
        radius /= 2
    raise AssertionError('no verified positive reward interval')


def check(obj):
    p, cfg = factory(obj['s'])(), config(obj['s'])
    z = next(x for x in p.graph.leaves if p.means[x] < .3)
    with patch.dict(ENGINES, immediate=ImmediateCompact):
        lanes = [DecisionLane(p, cfg, obj['tie'], m) for m in ('reference','immediate','threshold')]
    full, immediate, deferred = lanes
    streams = [capture(lane) for lane in lanes]
    audit = Audit(deferred)
    amb = Counter()
    uses, parks = set(), set()
    price = ImmediateTree.price_group
    forecast = GuardedSearch.forecast
    expensive = PartialTrial.pending_is_expensive

    def inspect_price(tree, side, events, old, new):
        if len(events) < 4:
            return price(tree, side, events, old, new)
        profile = tree.profile
        start = profile.cursor[side]
        first, last = events[0][0], events[-1][0]
        mid, _, c0 = profile.lookup(side, first, start)
        end, _, c1 = profile.lookup(side, last, mid)
        pulls, cost = price(tree, side, events, old, new)
        assert profile.cursor[side] == end
        point = cost-c0-c1-14
        if point:
            boundary = profile.h if profile.inc else 0
            kmin = 0 if mid == boundary else 1 if end == boundary else len(events)
            lo = 7*len(events) + 3*(abs(end-start)+kmin)
            assert lo <= point
            amb.update(groups=1, scan=point, scan_lower=lo)
        return pulls, cost

    def inspect_forecast(engine):
        n = engine.ev.counts[z]
        if engine is full.engine and n:
            uses.add((n, engine.point[2]/cfg['K']))
        return forecast(engine)

    def inspect_parking(trial):
        if (trial.owner is full.engine and trial.todo and trial.current_count >= 32
                and p.graph.leaves[trial.todo[-1]] == z):
            parks.add((trial.evidence.counts[z], trial.theta/cfg['K']))
        return expensive(trial)

    steps = 0
    closed_at = None
    with ExitStack() as stack:
        audit.instrument(stack)
        stack.enter_context(patch.object(ImmediateTree, 'price_group', inspect_price))
        stack.enter_context(patch.object(GuardedSearch, 'forecast', inspect_forecast))
        stack.enter_context(patch.object(PartialTrial, 'pending_is_expensive', inspect_parking))
        while not full.point[1]:
            assert not full.conflict and full.draws < DRAWS and max(l.work for l in lanes) + getattr(p,'build',0) < BUDGET
            for lane, buf in zip(lanes, streams):
                buf.clear()
                lane.advance(DRAWS-lane.draws)
            assert streams[0] == streams[1] == streams[2]
            equal(full, immediate, True)
            assert full.point == deferred.point and full.draws == deferred.draws
            assert full.engine.ended == deferred.engine.ended
            if full.engine.ended and closed_at is None:
                closed_at = full.draws
            a, b = full.engine.trial, deferred.engine.trial
            assert (a is None) == (b is None)
            if a is not None:
                assert (a.todo,a.retained,a.high,a.samples) == (b.todo,b.retained,b.high,b.samples)
            steps += 1
    assert all(l.engine.idx.rng.getstate() == full.engine.idx.rng.getstate() for l in lanes)
    assert all(l.engine.ev.sums == full.engine.ev.sums for l in lanes)
    live = len(deferred.engine.bounds.pending)
    limit = full.oracle.counts[z]
    assert limit > 0
    radius = noise_cell(p.means[z], limit, uses, parks, cfg, len(p.graph.leaves))
    for lane in lanes:
        del lane.oracle.sample  # retire the production object, without the diagnostic hook
    rows = [endpoint(l, p, cfg) for l in lanes]
    assert all(r['box'] == rows[0]['box'] and r['work'] <= BUDGET for r in rows)
    for row in rows:
        row['status'] = 'certified'
        audit_action(p, row, cfg)
    c = audit.count
    refinements = rows[2]['account']['refinements']
    assert amb['groups'] == rows[2]['account']['deferred_groups']
    drop = rows[2]['drop']-rows[1]['drop']
    charges = sum(c[k] for k in ('storage','refinement','comparisons','setup')) + drop
    gap = rows[1]['work']-rows[2]['work']
    assert gap == amb['scan']-charges
    return dict(graph=obj['graph'], case=obj['case'], tie=obj['tie'], steps=steps, draws=rows[0]['draws'],
                action=rows[0]['action'], box=list(rows[0]['box']), full=rows[0]['work'], immediate=rows[1]['work'],
                deferred=rows[2]['work'], initiate=rows[2]['meta'].get('start_N'), closed_at=closed_at,
                gap=gap, groups=amb['groups'],
                refinements=refinements, live=live, released=amb['groups']-refinements-live,
                scan=amb['scan'], scan_lower=amb['scan_lower'], storage=c['storage'], refinement=c['refinement'],
                predicates=c['comparisons'], setup=c['setup'], disposal=drop, exact_launch=audit.launch and audit.launch['exact'],
                index_margin=amb['scan_lower']-c['storage']-c['refinement']-c['comparisons']-c['setup']-64,
                variable_leaf=z, mean=p.means[z], leaf_draws=limit, reward_radius=radius,
                forecast_tests=len(uses), parking_tests=len(parks),
                topology=digest_graph(p.graph.children))


def digest_graph(children):
    import hashlib
    return hashlib.sha256(json.dumps(children).encode()).hexdigest()


def run():
    cases = [o for o in inputs() if o['graph']=='fresh-0' or o['tag']=='confirmation']
    rows = [check(obj) for obj in cases]
    assert len(rows)==32
    timed = {}
    for line in (DEST/'runs.jsonl').read_text().splitlines():
        r = json.loads(line)
        if r['repeat']==0:
            timed[r['case'],r['method']] = r
    for row in rows:
        for m, col in [('reference','full'),('immediate','immediate'),('threshold','deferred')]:
            r = timed[row['case'],m]
            assert (r['status'],r['work'],r['draws'],r['action']) == (
                'certified',row[col],row['draws'],row['action'])
    payload = json.dumps(rows, indent=2)
    path = DEST/'reachability.json'
    if path.exists():
        for new, old in zip(rows,json.loads(path.read_text()),strict=True):
            assert new==old, (new['case'], {k:(v,old.get(k)) for k,v in new.items() if v!=old.get(k)})
    else:
        path.write_text(payload)
    print('verified',len(rows),'tapes',digest(path))


if __name__=='__main__':
    run()
