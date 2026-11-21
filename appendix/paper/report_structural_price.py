"""Verify frozen predictions against coupled endpoints; regenerate the matched results."""
import argparse
import csv
import json
import math
from collections import Counter
from statistics import mean

from paper.structural_price_benchmark import DEST, ROOT, METHODS, BUDGET, SECONDS, fixtures, measured, digest
from paper.structural_price_condition import check
from paper.decision_price_benchmark import config
from paper.uniform_price_proof import Leaf


def logical_signature(g):
    return sorted((tuple(a for a,children in enumerate(g.graph.children[1:5]) if x in children),
                   g.means[x]) for x in g.graph.leaves)


def simple_clipping(spec, graph, z, p=256):
    m, j = z['M'], z['join']
    cfg = config(spec)
    values = [graph.means[x] for x in graph.graph.leaves]
    w, r = sorted(range(m),key=values.__getitem__,reverse=True)[:2]
    curves = [Leaf(v,cfg['K'],math.log(m/cfg['delta'])) for v in values]
    warm = [next(b for b in range(1,p) if c.at(b)[1]<cfg['K']) for c in curves]
    cold = [u for u in range(m) if u not in (w,r)]
    revisions = sum(len(curves[u].at(1)[3][1]) for u in cold)
    lost = [sum(16-len(curves[u].at(b)[3][side]) for u in (w,r) for b in range(1,2*p+1))
            for side in (0,1)]
    s = sum(warm)-z['sweep']
    slacks = []
    for q in (p,2*p):
        t = q-1
        hot = 16*(2*t-m+2)
        nu = revisions + max(0,hot-lost[1])
        nl = max(0,hot-lost[0])
        credit = z['cover_fee']
        for b in range(q):
            low = max(0,z['kmin']-2*b)
            high = min(z['kmax'],max(0,sum(warm)-b-min(b,s)))
            writes = max(min(2*z['kmax']-y,y+2*z['lis']) for y in range(low,high+1))
            credit += 3*z['kmax']+1+writes
        slacks.append(36*32*t+12*(nu+j*nl+(j-1)*32*(t-z['sweep']))-5*credit)
    # Explicit scalar guard for the simplified theorem, independently of a timed solver.
    assert z['cold_clear']>0 and z['pre_return']>0
    anchor_floor = max(curves[u].at(1)[1]/cfg['K'] for u in cold) + z['cold_clear']
    assert anchor_floor>max(cfg['epsilon'], max(values[u] for u in cold)+1e-7+cfg['epsilon'])
    assert z['early']>0 and z['funding']>=0 and z['forecast']>=0 and min(slacks)>=0
    return slacks


def report(replay=False):
    manifest = json.loads((DEST/'manifest.json').read_text())
    complete = json.loads((DEST/'complete.json').read_text())
    assert all(digest(ROOT/'paper'/f)==h for f,h in manifest['source'].items())
    assert manifest['predictions']==digest(DEST/'predictions.json')
    assert complete['runs']==digest(DEST/'runs.jsonl')
    assert all(digest(DEST/f)==h for f,h in complete['tapes'].items())
    predictions = json.loads((DEST/'predictions.json').read_text())
    rows = [json.loads(s) for s in (DEST/'runs.jsonl').read_text().splitlines()]
    lookup = {(r['graph'],r['method'],r['tape'],r['repeat']):r for r in rows}
    n = manifest['tapes']
    assert len(lookup)==len(rows)==complete['rows']==12*len(METHODS)*2*n
    by_seed, graphs, tapes, proof = {}, [], [], {}
    for spec, graph in fixtures():
        name = spec['name']
        signature = logical_signature(graph)
        assert by_seed.setdefault(spec['seed'],signature)==signature
        z = check(graph,config(spec))
        assert z==predictions[name]
        if z['sign']=='deferred':
            proof[name] = simple_clipping(spec,graph,z)
        matches, wins, launches, gains = 0,0,0,[]
        record = dict(graph=name, M=z['M'],layout=spec['layout'], predicted=z['sign'],
                      guaranteed_WI_minus_WD=(z['bound'] if z['sign']=='deferred' else
                                                -z['bound'] if z['sign']=='immediate' else None))
        for i in range(n):
            first = {m:lookup[name,m,i,0] for m in METHODS}
            if replay and i==0:
                data = (DEST/'ties-00.bin').read_bytes()
                for m in METHODS:
                    actual = json.loads(json.dumps(measured(spec,graph,data,i,m)))
                    assert all(actual[k]==first[m][k] for k in
                               ('work','draws','action','box','tie_bytes','drop','status'))
            for rep in range(2):
                triple = [lookup[name,m,i,rep] for m in METHODS]
                if all(r['status']=='certified' for r in triple):
                    assert all(r['regret'] is not None and r['regret']<=spec['eps'] for r in triple)
                    assert len({(r['action'],tuple(r['box']),r['draws'],r['queries'],r['tie_bytes'])
                                for r in triple})==1
                    gap = triple[1]['work']-triple[2]['work']
                    if z['sign']=='deferred':
                        assert gap>=z['bound'] and triple[2]['meta']['launch']==1
                        assert triple[2]['account']['refinements']==0
                    if z['sign']=='immediate':
                        assert gap<=-z['bound'] and triple[2]['meta']['launch']==0
                if rep==1:
                    for m,r in zip(METHODS,triple):
                        if r['status']==first[m]['status']=='certified': assert r['work']==first[m]['work']
            joint = all(r['status']=='certified' for r in first.values())
            score = lambda r: r['work'] if r['status']=='certified' else BUDGET
            gap = score(first['immediate'])-score(first['threshold'])
            gains.append(gap)
            launches += first['threshold']['meta']['launch']
            wins += gap>0
            matches += joint
            tapes.append(dict(graph=name,tape=i,joint=joint,gap=gap,
                              launched=first['threshold']['meta']['launch'],
                              refined=first['threshold']['account']['refinements']))
        record.update(joint=matches,deferred_wins=wins,launches=launches,
                      mean_gap=mean(gains),min_gap=min(gains),max_gap=max(gains))
        for m in METHODS:
            group = [r for r in rows if r['graph']==name and r['method']==m]
            record[m+'_returns'] = sum(r['status']=='certified' for r in group)
            record[m+'_work'] = mean(r['work'] if r['status']=='certified' else BUDGET for r in group)
            record[m+'_seconds'] = mean(r['seconds'] if r['status']=='certified' else SECONDS for r in group)
        graphs.append(record)
    for file,group in [('per_graph.csv',graphs),('paired_tapes.csv',tapes)]:
        with (DEST/file).open('w',newline='') as out:
            writer = csv.DictWriter(out,fieldnames=group[0])
            writer.writeheader()
            writer.writerows(group)
    (DEST/'simple_clipping.json').write_text(json.dumps(proof,indent=2))
    print('completed',Counter(r['status'] for r in rows))
    for r in graphs:
        print(r['graph'],r['predicted'],r['deferred_wins'],r['launches'],
              round(r['mean_gap']),*(round(r[m+'_seconds'],3) for m in METHODS))


if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--replay',action='store_true')
    report(parser.parse_args().replay)
