"""Lockstep replay of real TA-UCT, its four monitors, and direct root DP."""
import argparse
import hashlib
import json
import struct

from dag_mcts.certified_uct import TranspositionUCT
from dag_mcts.onpolicy_backup import MonitoredUCT
from paper.uct_backup_benchmark import DEST,ROOT,CASES,SEEDS,METHODS,digest
from paper.uct_backup_families import fixture


def direct(graph,evidence):
    low,high = list(evidence.lower),list(evidence.upper)
    for v in reversed(graph.order):
        children = graph.children[v]
        if children:
            low[v] = max(low[c] for c in children)
            high[v] = max(high[c] for c in children)
    root = graph.root
    row = graph.children[root]
    action = max(range(len(row)),key=lambda a:low[row[a]])
    gap = max((high[c]-low[row[action]] for a,c in enumerate(row) if a!=action),default=0.)
    return action,max(0.,gap),low[root],high[root]


def coupled(family,size,seed,rows,make=fixture):
    problem,eps = make(family,size,seed)
    certs = {r['cert_at_step'] for r in rows if r['cert_at_step'] is not None}
    assert len(certs)<=1
    last = max(r['steps'] for r in rows)
    reference = TranspositionUCT(problem.graph,exploration=2.)
    oracle = problem.oracle(seed)
    lanes = {m:MonitoredUCT(problem,seed,m,eps) for m in METHODS}
    timeline = [(0,False)]
    stops = {(r['method'],r['steps']):r['work'] for r in rows}
    history = hashlib.sha256()
    eager = lanes['eager'].monitor.bounds
    live = lanes['live'].monitor.bounds
    cone = None
    if family in ('funnel','two-exit','fixed-gap','noisy','live-best','gap-test'):
        cone = next(c for c in problem.graph.children[0] if problem.graph.children[c])
    cut = None
    later_visits = later_deliveries = 0
    full_checks = 0
    for lane in lanes.values():
        assert lane.query==direct(problem.graph,lane.monitor.evidence)
    for step in range(1,last+1):
        expected = reference.step(oracle)
        prior = eager.messages
        for m,lane in lanes.items():
            assert lane.step()==expected
            assert lane.uct.recommendation.top==reference.recommendation.top
            if (m,step) in stops:
                assert lane.work==stops[m,step]
        primary = lanes['live']
        assert all((l.query,l.action,l.certified,l.monitor.evidence.conflict)==
                   (primary.query,primary.action,primary.certified,primary.monitor.evidence.conflict)
                   for l in lanes.values())
        path,reward = expected
        timeline.append((primary.action,primary.certified))
        if cut is not None and path[1]==cone:
            later_visits+=1
            later_deliveries+=eager.messages-prior
        if cone is not None and cut is None and not live.live[cone]:
            cut=step
        if step<=8 or step & (step-1)==0 or step==last:
            assert direct(problem.graph,primary.monitor.evidence)==primary.query
            full_checks+=1
        history.update(struct.pack('!I',len(path)))
        history.update(struct.pack('!'+str(len(path))+'I',*path))
        history.update(struct.pack('!didd i?',reward,primary.query[0],primary.query[1],
                                   primary.query[3],primary.action,primary.certified))
        history.update(struct.pack('!d',primary.query[2]))
        if primary.certified or primary.monitor.evidence.conflict:
            assert step==last
    assert all(l.uct.counts==reference.counts and l.uct.means==reference.means and
               l.uct.leaf_counts==reference.leaf_counts for l in lanes.values())
    assert certs==({last} if lanes['live'].certified else set())
    for r in rows:
        for a,n,cert in r['checkpoints']:
            assert timeline[n]==(a,cert)
    return dict(family=family,size=size,seed=seed,steps=last,certified=lanes['live'].certified,
                root_action=lanes['live'].action,digest=history.hexdigest(),dp_checks=full_checks,
                cone_cut=cut,later_cone_visits=later_visits,later_eager_messages=later_deliveries,
                eager_messages=eager.messages,live_messages=live.messages,
                work={m:l.work for m,l in lanes.items()})


def audit(replay=False):
    manifest = json.loads((DEST/'manifest.json').read_text())
    complete = json.loads((DEST/'complete.json').read_text())
    assert all(digest(ROOT/s)==v for s,v in manifest['sources'].items())
    assert complete['runs']==digest(DEST/'runs.jsonl')
    rows = [json.loads(x) for x in (DEST/'runs.jsonl').read_text().splitlines()]
    assert len(rows)==complete['rows']==len(CASES)*len(SEEDS)*len(METHODS)*2
    output = DEST/'coupled.jsonl'
    expected = output.read_text().splitlines() if replay else None
    result = []
    for family,size in CASES:
        for seed in SEEDS:
            group = [r for r in rows if (r['family'],r['size'],r['seed'])==(family,size,seed)]
            assert {(r['method'],r['repeat']) for r in group}=={(m,i) for m in METHODS for i in (0,1)}
            row = coupled(family,size,seed,group)
            if replay:assert row==json.loads(expected[len(result)])
            result.append(row)
        print(family,size,'coupled',len(result),flush=True)
    if not replay:
        output.write_text(''.join(json.dumps(r)+'\n' for r in result))
    else:
        assert len(expected)==len(result)
    print(sum(r['steps'] for r in result),'coupled steps',sum(r['dp_checks'] for r in result),'direct DP checks')


if __name__=='__main__':
    cli=argparse.ArgumentParser()
    cli.add_argument('--replay',action='store_true')
    audit(cli.parse_args().replay)
