"""Matched sibling challenge: verify all triples, proof bounds and counter replay."""
import argparse
import csv
import json
from statistics import mean
from unittest.mock import patch

from paper.decision_price import ThresholdCompact, ThresholdTree
from paper.neighbor_price_benchmark import DEST, METHODS, ROOT, fixtures, measured, predict, config, digest, BUDGET, SECONDS
from paper.neighbor_price_family import neighbor_family
from paper.report_structural_price import logical_signature
from paper.structural_price_benchmark import fixtures as original_fixtures
from paper.structural_price_condition import check


def mechanism(spec,graph,tape,old,pred):
    """Untimed single-tape check of real pre-probe charges, outside the trial."""
    stats = dict(dominant=0,probes=[])
    price,launch = ThresholdTree.price_group,ThresholdCompact.try_launch
    sweep,height = old['sweep'],old['height']
    def group(tree,side,events,peer_old,peer_new):
        pulls,cost = price(tree,side,events,peer_old,peer_new)
        if tree.account.batch_blocks>sweep and min(x for x,_ in events)>=max(peer_old,peer_new):
            assert pulls==height*len(events)
            stats['dominant']+=len(events)
        return pulls,cost
    def probe(engine):
        previous = engine.account.branch_checks
        launch(engine)
        if engine.account.branch_checks!=previous:
            q = engine.idx.q
            slack = engine.bounds.base-6*engine.idx.stats['fallback_work']
            stats['probes'].append(dict(q=q,slack=slack,dominant=stats['dominant']))
            if 'clip' in pred and q in (256,512):
                i = 0 if q==256 else 1
                assert slack>=pred['clip'][i] and stats['dominant']>=pred['leaders'][i]
    with patch.object(ThresholdTree,'price_group',group), patch.object(ThresholdCompact,'try_launch',probe):
        r = measured(spec,graph,tape,0,'threshold')
    return r,stats


def report(replay=False):
    manifest = json.loads((DEST/'manifest.json').read_text())
    complete = json.loads((DEST/'complete.json').read_text())
    pred = json.loads((DEST/'predictions.json').read_text())
    assert all(digest(ROOT/'paper'/n)==v for n,v in manifest['source'].items())
    assert digest(DEST/'predictions.json')==manifest['predictions']
    assert digest(DEST/'runs.jsonl')==complete['runs']
    assert all(digest(DEST/n)==v for n,v in complete['tapes'].items())
    rows = [json.loads(l) for l in (DEST/'runs.jsonl').read_text().splitlines()]
    lookup = {(r['graph'],r['tape'],r['repeat'],r['method']):r for r in rows}
    graphs, tapes, audits, signatures = [], [], {}, {}
    n = manifest['tapes']
    assert len(lookup)==len(rows)==complete['rows']==12*3*2*n
    for spec,graph in fixtures():
        name = spec['name']
        signature = logical_signature(graph)
        assert signatures.setdefault(spec['seed'],signature)==signature
        old = check(graph,config(spec))
        z = predict(graph,config(spec))
        assert z==pred[name] and old['join']==1
        w = max(graph.graph.leaves,key=graph.means.__getitem__)
        owners = [a for a,ch in enumerate(graph.graph.children[1:5]) if w in ch]
        inside = []
        for a in owners:
            mask = [int(j in graph.graph.children[a+1]) for j in graph.graph.leaves]
            inside.append(sum(v and (i==0 or not mask[i-1]) for i,v in enumerate(mask)))
        stat = dict(graph=name,M=spec['M'],layout=spec['layout'],old=z['old'],predicted=z['sign'],
                    bound=z['bound'],winning_owner_eligible=max(inside)>=8)
        outcomes = []
        for i in range(n):
            first = [lookup[name,i,0,m] for m in METHODS]
            for rep in (0,1):
                triple = [lookup[name,i,rep,m] for m in METHODS]
                if all(r['status']=='certified' for r in triple):
                    assert len({(r['action'],tuple(r['box']),r['draws'],r['tie_bytes'],r['queries']) for r in triple})==1
                    assert all(r['regret']<=spec['eps'] for r in triple)
                    deferred = triple[2]
                    gap = triple[1]['work']-deferred['work']
                    if z['sign']=='deferred':
                        lo,hi = deferred['meta']['allowance_bounds']
                        assert gap>=z['bound'] and lo==hi==2*deferred['meta']['range_credit']
                        assert deferred['account']['refinements']==0 and deferred['meta']['launch']==1
                    if z['sign']=='immediate':
                        assert gap<=-z['bound'] and not deferred['meta']['launch']
                    if rep and all(r['status']=='certified' for r in first):
                        assert [r['work'] for r in first]==[r['work'] for r in triple]
            scored = lambda r: r['work'] if r['status']=='certified' else BUDGET
            record = dict(graph=name,tape=i,joint=all(r['status']=='certified' for r in first),
                          gap=scored(first[1])-scored(first[2]),launch=first[2]['meta']['launch'],
                          refinements=first[2]['account']['refinements'])
            tapes.append(record)
            outcomes.append(record)
        if replay:
            tape = (DEST/'ties-00.bin').read_bytes()
            for m in METHODS:
                if m=='threshold':
                    actual,audits[name] = mechanism(spec,graph,tape,old,z)
                else:
                    actual = measured(spec,graph,tape,0,m)
                actual = json.loads(json.dumps(actual))
                expected = lookup[name,0,0,m]
                assert all(actual[k]==expected[k] for k in ('action','box','draws','work','drop','status','tie_bytes'))
        gaps = [r['gap'] for r in outcomes]
        stat.update(deferred_wins=sum(x>0 for x in gaps),mean_gap=mean(gaps),min_gap=min(gaps),
                    max_gap=max(gaps),launches=sum(r['launch'] for r in outcomes))
        for m in METHODS:
            group = [r for r in rows if r['graph']==name and r['method']==m]
            stat[m+'_returns'] = sum(r['status']=='certified' for r in group)
            stat[m+'_work'] = mean(r['work'] if r['status']=='certified' else BUDGET for r in group)
            stat[m+'_seconds'] = mean(r['seconds'] if r['status']=='certified' else SECONDS for r in group)
        graphs.append(stat)
        print(name,z['sign'],stat['deferred_wins'],round(stat['mean_gap']),
              *(round(stat[m+'_seconds'],3) for m in METHODS))
    for filename,data in [('per_graph.csv',graphs),('paired_tapes.csv',tapes)]:
        with (DEST/filename).open('w',newline='') as out:
            writer = csv.DictWriter(out,fieldnames=data[0])
            writer.writeheader()
            writer.writerows(data)
    dev = {s['name']:predict(g,config(s)) for s,g in original_fixtures() if s['layout']=='neighbors'}
    (DEST/'development.json').write_text(json.dumps(dev,indent=2))
    (DEST/'free_masks.json').write_text(json.dumps([neighbor_family(m) for m in (176,192)],indent=2))
    if replay:
        (DEST/'mechanism.json').write_text(json.dumps(audits,indent=2))


if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--replay',action='store_true')
    report(parser.parse_args().replay)
