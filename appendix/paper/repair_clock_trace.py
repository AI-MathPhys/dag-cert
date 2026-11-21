"""Untimed paired event audit. Distinguish a changed price from a changed decision."""
import hashlib
import json
from itertools import zip_longest

from paper.audit_compact_side_paths import capture
from paper.repair_policy_clock import (ARCHIVE, DEST, METHODS, ClockLane, config, factory, caseid,
                                      endpoint, status, audit_action, digest, DRAWS, BUDGET)


def tie_signature(s):
    return hashlib.sha256(repr(s.idx.rng.getstate()).encode()).hexdigest()


def instrument(lane):
    s = lane.engine
    gate, plan, step = s.try_launch, s.plan, s.trial_step
    events = []
    current = {}

    def inspect_plan():
        p = plan()
        if p:
            current.update(estimate=p.partial_estimate, earnings=p.earnings, deferred=list(p.deferred))
        return p

    def inspect_gate():
        current.clear()
        q = s.idx.q
        credit = s.idx.stats['fallback_work']
        logical = s.w.total - s.pilot_cost - s.monitor_cost - 24
        physical = logical + s.account.extra - s.account.saved + 6
        draws = lane.draws
        point = s.point
        signature = tie_signature(s)
        before = s.meta['scans']
        gate()
        selected = physical if s.physical else logical
        budget = min(2 * credit, selected // 3)
        if s.trial is not None:
            assert s.meta['start_work'] == selected and s.budget == budget
            assert 0 <= s.spent <= s.setup_bound
        events.append(dict(kind='probe', q=q, draws=draws, choice='launch' if s.trial else 'ordinary',
                           scanned=s.meta['scans'] != before, point=point, tie=signature, common=selected,
                           logical=logical, physical=physical, credit=credit, budget=budget,
                           floor=s.setup_bound+s.draw_bound+48, **current))

    def inspect_trial(n):
        t = s.trial
        draws = lane.draws
        before = s.meta['parks']
        spent = s.spent
        pending = t.todo[-1] if t.todo else None
        forecast = t.total_pred
        progress = t.progress()
        before_samples = t.samples
        possible = t.possible_size
        obs, result = step(n)
        reason = 'continue'
        if s.trial is None:
            reason = next(k for k in ('abort_dense','abort_progress','abort_hard','decision','seal') if s.meta[k])
        events.append(dict(kind='private', q=s.idx.q, draws=draws, end=lane.draws,
                           choice=reason, park=s.meta['parks']-before, spent=spent, pending=pending,
                           budget=s.budget, samples=t.samples, before_samples=before_samples,
                           forecast=forecast, progress=progress, possible=possible))
        return obs, result

    s.try_launch, s.plan, s.trial_step = inspect_gate, inspect_plan, inspect_trial
    return events


def trace(spec, method, lane_type=ClockLane):
    p, cfg = factory(spec)(), config(spec)
    if 'frontier_cap' in spec:
        cfg['cap'] = spec['frontier_cap']
    lane = lane_type(p, cfg, spec['seed'], method)
    observations = capture(lane)
    assert lane.draws == 0
    events = instrument(lane)
    build = getattr(p, 'build', 0)
    while (not lane.point[1] and not lane.conflict and build+lane.work < BUDGET and lane.draws < DRAWS):
        lane.advance(DRAWS-lane.draws)
    assert lane.draws == len(observations)
    for name in ('try_launch','plan','trial_step'):
        delattr(lane.engine, name)
    del lane.oracle.sample
    row = endpoint(lane, p, cfg)
    row['status'] = status(row, lane.conflict, 0)
    audit_action(p, row, cfg)
    return row, events, observations


def semantics(e):
    if e is None:
        return None
    return e['kind'], e['choice'], e.get('park', 0), e['draws'], e.get('end')


def compare(s, lanes=None):
    left, right = lanes or [trace(s,m) for m in METHODS]
    rows, events, observations = zip(left, right)
    price = branch = different = last_probe = None
    for a, b in zip_longest(*events):
        if a and b and a['kind'] == b['kind'] == 'probe':
            assert a['point'] == b['point'] and a['tie'] == b['tie']
            last_probe = [a,b]
        if price is None and a and b and a['kind'] == b['kind'] == 'probe':
            if 'estimate' in a and 'estimate' in b and a['budget'] != b['budget']:
                price = [a,b]
        if semantics(a) != semantics(b):
            branch = [a,b]
            break
    for i, (a,b) in enumerate(zip(*observations), 1):
        if a != b:
            different = dict(index=i, reference=a, physical=b)
            assert a[0] != b[0], 'shared prefix and leaf must receive the same reward'
            break
    prefix = min(map(len, observations)) if different is None else different['index']-1
    prefix_only = different is None and len(observations[0]) != len(observations[1])
    if branch is None and not prefix_only:
        assert different is None
    return dict(case=caseid(s), cohort=s['cohort'], family=s['family'], first_price=price,
                first_branch=branch, shared_probe=last_probe if branch else None,
                first_observation=different, common_draws=prefix,
                strict_prefix=prefix_only, ends=dict(zip(METHODS,rows)))


def run():
    cases = json.loads((ARCHIVE/'manifest.json').read_text())['cases']
    path = DEST/'trace.jsonl'
    with path.open('x') as out:
        for i,s in enumerate(cases,1):
            row = compare(s)
            out.write(json.dumps(row)+'\n')
            out.flush()
            if i%16==0:
                print(i,'/',len(cases),'trace pairs',flush=True)
    (DEST/'trace_complete.json').write_text(json.dumps(dict(cases=len(cases), sha256=digest(path),
                     source=digest(DEST.parent.parent/'paper/repair_clock_trace.py'))))


if __name__ == '__main__':
    run()
