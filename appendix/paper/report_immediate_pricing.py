"""Paired graph-level certification endpoints, with all nondecisions retained."""
import csv
import json
from collections import Counter, defaultdict
from statistics import mean, median

from paper.immediate_pricing_benchmark import BUDGET, SECONDS, DEST, METHODS, digest


def summarize(rows):
    success = [r for r in rows if r['status']=='certified']
    return dict(runs=len(rows), certified=len(success), actual_work=mean(r['work'] for r in rows),
                work_loss=mean(r['work'] if r['status']=='certified' else BUDGET for r in rows),
                time_loss=mean(r['seconds'] if r['status']=='certified' else SECONDS for r in rows),
                return_work=mean(r['work'] for r in success) if success else None,
                return_seconds=mean(r['seconds'] for r in success) if success else None)


def report():
    archive=DEST/'runs.jsonl'
    complete=json.loads((DEST/'complete.json').read_text())
    assert complete['sha256']==digest(archive)
    rows=[json.loads(s) for s in archive.read_text().splitlines()]
    specs={o['case']:o for o in json.loads((DEST/'manifest.json').read_text())['specs']}
    assert len(rows)==complete['rows']==6*len(specs)
    pairs=defaultdict(dict)
    for r in rows:
        group=pairs[r['case'],r['repeat']]
        assert r['method'] not in group
        group[r['method']]=r
    independent=defaultdict(list)
    for (case, rep), group in pairs.items():
        assert set(group)==set(METHODS)
        if all(r['status'] in ('certified','draw') for r in group.values()):
            assert len({(r['status'],r['draws'],r['action'],tuple(r['box'] or ())) for r in group.values()})==1
        if rep==0:
            independent[group['reference']['tag']].append(group)
    # Collect graph endpoints over both measured repetitions.
    per_graph=defaultdict(lambda: defaultdict(list))
    for r in rows:
        per_graph[r['tag'],r['graph']][r['method']].append(r)
    previous = [json.loads(line) for line in (DEST.parent/'index_repayment_v1/cases.jsonl').read_text().splitlines()]
    for old in previous:
        for rep in (0, 1):
            g = pairs[old['case'], rep]
            if all(r['status']==old['status'] for r in g.values()):
                assert g['reference']['work']==old['full'] and g['threshold']['work']==old['threshold']
    graph_rows=[]
    for (tag,graph), runs in sorted(per_graph.items()):
        spec=specs[runs['reference'][0]['case']]['s']
        for method,rr in runs.items():
            graph_rows.append(dict(tag=tag,graph=graph,epsilon=spec['eps'],graph_seed=spec['seed'],
                                   method=method,**summarize(rr)))
    with (DEST/'per_graph.csv').open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=graph_rows[0])
        writer.writeheader()
        writer.writerows(graph_rows)
    cohorts={}
    for tag, groups in independent.items():
        joint=[g for g in groups if all(r['status']=='certified' for r in g.values())]
        paired_time=[]
        for g in joint:
            case=g['reference']['case']
            reps=[pairs[(case,k)] for k in (0,1)]
            if all(r[m]['status']=='certified' for r in reps for m in METHODS):
                paired_time.append(mean(r['threshold']['seconds'] for r in reps)/
                                   mean(r['immediate']['seconds'] for r in reps))
        totals={m:sum(g[m]['work'] for g in joint) for m in METHODS}
        wins=Counter('deferred' if g['threshold']['work']<g['immediate']['work'] else
                     'immediate' if g['threshold']['work']>g['immediate']['work'] else 'tie' for g in joint)
        cohorts[tag]=dict(cases=len(groups),joint=len(joint),work=totals,wins=wins,
                          time_pairs=len(paired_time),median_deferred_over_immediate_time=median(paired_time),
                          all_runs={m:summarize([r for r in rows if r['tag']==tag and r['method']==m])
                                    for m in METHODS})
    (DEST/'summary.json').write_text(json.dumps(dict(cohorts=cohorts,graphs=graph_rows),indent=2))
    print(json.dumps(cohorts,indent=2))
    tex=DEST.parents[1]/'paper/certificates'
    tex.mkdir(parents=True, exist_ok=True)
    table=[r'\begingroup\footnotesize\setlength{\tabcolsep}{3pt}',
           r'\begin{longtable}{@{}lrrrrrrr@{}}',
           r'\caption{Mean charged certification loss (millions) and time to certification (seconds) by graph and accuracy. F, I and D denote full, immediate and deferred. The final column counts certifications per method over both repetitions when the three counts agree. Nondecisions enter at 102.4 million units and 12 seconds. Actual work, conditional return times and separate completion counts are in \texttt{per\_graph.csv}.}\label{tab:all-immediate}\\',
           r'\toprule Graph / input & $W_F$ & $W_I$ & $W_D$ & $t_F$ & $t_I$ & $t_D$ & Returns\\\midrule\endfirsthead',
           r'\toprule Graph / input & $W_F$ & $W_I$ & $W_D$ & $t_F$ & $t_I$ & $t_D$ & Returns\\\midrule\endhead']
    for (tag,graph),runs in sorted(per_graph.items()):
        stats=[summarize(runs[m]) for m in METHODS]
        rates=[f"{s['certified']}/{s['runs']}" for s in stats]
        cells=[graph.replace('_',r'\_')] + [f"{s['work_loss']/1e6:.4f}" for s in stats] + [
             f"{s['time_loss']:.3f}" for s in stats]+ [rates[0] if len(set(rates))==1 else ','.join(rates)]
        table.append(' & '.join(cells)+r'\\')
    table.append(r'\bottomrule\end{longtable}\endgroup')
    (tex/'immediate_graph_table.tex').write_text('\n'.join(table)+'\n')


if __name__=='__main__':
    report()
