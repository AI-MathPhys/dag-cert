"""Capped time-to-certification summaries and same-route meter reconciliation."""
from collections import Counter, defaultdict
from statistics import mean, median
import json
import random

from paper.prefix_routing_benchmark import DEST, METHODS, base


def load(stem):
    runs=DEST/('overlap_runs.jsonl' if stem else 'runs.jsonl')
    stamp=json.loads((DEST/(stem+'complete.json')).read_text())
    rows=[json.loads(l) for l in runs.read_text().splitlines()]
    assert len(rows)==stamp['rows'] and base.digest(runs)==stamp['sha256']
    if stem:
        groups=json.loads((DEST/'overlap_manifest.json').read_text())['blocks']
        design={(str(a),(.05,.09)[i],t) for a,i,t in groups}
        assert {(r['noise'],r['shift'],r['tie']) for r in rows}==design
    else:
        groups=json.loads((DEST/'manifest.json').read_text())['groups']
        expected={(g['tag'],g['s']['seed'],g['noise'],g['s']['shift'],g['tie'],m,pos)
                  for g in groups for pos,m in enumerate(g['order'])}
        assert {(r['tag'],r['graph'],r['noise'],r['shift'],r['tie'],r['method'],r['position']) for r in rows}==expected
    return rows


def loss(r):return r['work'] if r['status']=='certified' else base.BUDGET


def review(rows):
    table=defaultdict(dict)
    for r in rows:
        k=(r['graph'],r['tie'],r['shift'])
        assert r['method'] not in table[k]
        table[k][r['method']]=r
    assert all(set(case)==set(METHODS) for case in table.values())
    audit=Counter()
    for case in table.values():
        for m in ('interval','online'):
            r=case[m]; meta=r['meta']
            assert meta['probe_draws']==96 and 0<meta['inspected']<=96
            fixed=case[meta['prefix_route']]
            if r['status']==fixed['status'] and r['draws']==fixed['draws']:
                for key in ('action','box','regret','queries'):
                    assert r[key]==fixed[key]
                for key in ('start_N','seal','phase_work','phase_calls','launch','decision'):
                    assert r['meta'][key]==fixed['meta'][key]
                assert (r['work']-r['drop']-fixed['work']+fixed['drop'])==r['account']['selector_work']
                audit['matched']+=1
            else:audit['cap_mismatch']+=1
    stats={}
    tag=rows[0]['tag']
    clusters=defaultdict(list)
    for g,t,s in table:clusters[g if tag=='transfer' else t].append((g,t,s))
    rng=random.Random(378882)
    ids=list(clusters)
    resamples=[rng.choices(ids,k=len(ids)) for _ in range(4000)]
    for m in METHODS:
        rs=[case[m] for case in table.values()]
        def weighted(keys,fn):
            return sum((7 if k[2]==.05 else 1)*fn(table[k]) for k in keys)/(4*len(keys))
        by={c:weighted(keys,lambda z:loss(z[m])-loss(z['reference'])) for c,keys in clusters.items()}
        boots=sorted(mean(by[c] for c in sample) for sample in resamples)
        item=dict(mean_loss=weighted(table,lambda z:loss(z[m])),mean_work=weighted(table,lambda z:z[m]['work']),
                  restricted_seconds=weighted(table,lambda z:z[m]['seconds'] if z[m]['status']=='certified' else base.SECONDS),
                  full_gap=mean(by.values()),ci=[boots[99],boots[3899]],status=Counter(r['status'] for r in rs),
                  low_loss=mean(loss(r) for r in rs if r['shift']==.05),high_loss=mean(loss(r) for r in rs if r['shift']==.09),
                  max_regret=max((r['regret'] for r in rs if r['regret'] is not None),default=None))
        if m in ('interval','online'):
            item.update(choices=Counter(f"{r['shift']}-{r['meta']['prefix_route']}" for r in rs),
                        reasons=Counter(r['meta']['prefix_reason'] for r in rs),
                        mean_inspected=mean(r['meta']['inspected'] for r in rs),
                        mean_fee=mean(r['account']['selector_work'] for r in rs),
                        mean_added_total=mean(r['work']-table[r['graph'],r['tie'],r['shift']][r['meta']['prefix_route']]['work'] for r in rs))
            contrasts={}
            for fixed in ('bare','credit-all'):
                diff={c:weighted(keys,lambda z:loss(z[m])-loss(z[fixed])) for c,keys in clusters.items()}
                reps=sorted(sum(diff[c] for c in sample)/len(sample) for sample in resamples)
                contrasts[fixed]=[mean(diff.values()),reps[99],reps[3899]]
            item['fixed_contrasts']=contrasts
        stats[m]=item
    out=dict(clusters=len(ids),cases=len(table),audit=audit,methods=stats)
    for fixed,label in (('bare','bare'),('credit','post')):
        timing={}
        for shift in (.05,.09):
            gap={c:mean(loss(table[k]['credit-all'])-loss(table[k][fixed]) for k in keys if k[2]==shift)
                 for c,keys in clusters.items()}
            reps=sorted(sum(gap[c] for c in sample)/len(sample) for sample in resamples)
            starts=Counter(str(z['credit-all']['meta']['start_N'])+' / '+str(z[fixed]['meta']['start_N'])
                           for k,z in table.items() if k[2]==shift)
            timing[str(shift)]=dict(gap=mean(gap.values()),ci=[reps[99],reps[3899]],start_draws=starts)
        out['credit_all_minus_'+label]=timing
    return out


def main(stem=''):
    rows=load(stem)
    result=defaultdict(list)
    for r in rows:result[r['tag']+'_'+r['noise']].append(r)
    summary={k:review(group) for k,group in result.items()}
    (DEST/(stem+'summary.json')).write_text(json.dumps(summary,indent=2))
    for k,x in summary.items():
        print(k,x['audit'],[(m,round(x['methods'][m]['mean_loss'])) for m in METHODS],flush=True)


if __name__=='__main__':
    import sys
    main('overlap_' if '--overlap' in sys.argv else '')
