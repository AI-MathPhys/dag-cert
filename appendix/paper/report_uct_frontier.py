"""Descriptive prespecified summaries; timing repetitions are paired within seed."""
import csv
import json
from collections import defaultdict
from pathlib import Path
from statistics import mean,median
from paper.uct_frontier_study import DEST,METHODS,WALL,CASES,verify

def write(name,rows):
    with (DEST/name).open('w',newline='') as out:
        w=csv.DictWriter(out,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def run():
    verify()
    rows=[json.loads(l) for l in (DEST/'runs.jsonl').read_text().splitlines()]
    groups=defaultdict(list)
    for r in rows:groups[(r['family'],r['size'],r['seed'],r['effort'],r['method'])].append(r)
    graph=[]
    for (f,n,s,e,m),rs in sorted(groups.items()):
        q=dict(family=f,size=n,seed=s,effort=e,method=m,runs=len(rs),
               completed=sum(r['returned'] for r in rs),
               restricted_ms=1000*mean(r['restricted'] for r in rs),
               init_ms=1000*mean(r['init_seconds'] for r in rs),
               mean_rollouts=mean(r['steps'] for r in rs),
               certificate_rollout=next((r['certified_at'] for r in rs if r['certified_at']),None),
               certified_work=mean(r['work'] for r in rs) if all(r['returned'] for r in rs) else None,
               mean_prefix_work=mean(r['work'] for r in rs),first_cut=rs[0]['first_cut'],
               message_prefix=mean(r['messages'] for r in rs) if rs[0]['messages'] is not None else None,
               original_nodes=rs[0]['graph']['nodes'],original_edges=rs[0]['graph']['edges'],
               distinct_supports=rs[0]['graph']['unique_supports'],
               circuit_edges=rs[0]['circuit'].get('edges'),layout=rs[0]['circuit'].get('order'))
        graph.append(q)
    write('per_graph.csv',graph)
    summary=[];walls=[];pairs=[]
    for f,n in CASES:
        for effort in (0,512):
            for method in METHODS:
                rs=[r for r in rows if (r['family'],r['size'],r['effort'],r['method'])==(f,n,effort,method)]
                summary.append(dict(family=f,size=n,effort=effort,method=method,runs=len(rs),
                      completed=sum(r['returned'] for r in rs),
                      restricted_ms=1000*mean(r['restricted'] for r in rs),
                      init_ms=1000*mean(r['init_seconds'] for r in rs),
                      certified_work=mean(r['work'] for r in rs) if all(r['returned'] for r in rs) else None))
                for i,budget in enumerate(WALL):
                    walls.append(dict(family=f,size=n,effort=effort,method=method,budget_ms=1000*budget,
                        mean_regret=mean(r['regrets'][i] for r in rs),
                        certified=sum(r['checkpoints'][i][2] for r in rs),
                        no_rollout=sum(r['checkpoints'][i][1]==0 for r in rs)))
            for other in ('graph-eager','cover-live','covers'):
                a=[r for r in graph if (r['family'],r['size'],r['effort'],r['method'])==(f,n,effort,'graph-live')]
                b=[r for r in graph if (r['family'],r['size'],r['effort'],r['method'])==(f,n,effort,other)]
                diffs=[y['restricted_ms']-x['restricted_ms'] for x,y in zip(a,b)]
                ratios=[x['restricted_ms']/y['restricted_ms'] for x,y in zip(a,b)]
                pairs.append(dict(family=f,size=n,effort=effort,comparator=other,
                        median_ms_saved=median(diffs),median_time_ratio=median(ratios),
                        winning_seeds=sum(d>0 for d in diffs),tied_seeds=sum(d==0 for d in diffs),seeds=len(a)))
    write('summary.csv',summary);write('wall_regret.csv',walls);write('paired.csv',pairs)
    overall=dict(rows=len(rows),completed=sum(r['returned'] for r in rows),
                 invalid_certificates=sum(not r['valid'] for r in rows),
                 confidence_conflicts=sum(r['conflict'] for r in rows))
    for name in ('coupling','memory'):
        path=DEST/(name+'.jsonl')
        if path.exists():
            audit=[json.loads(l) for l in path.read_text().splitlines()]
            overall[name+'_rows']=len(audit)
            if name=='coupling':
                overall['coupled_rollouts']=sum(r['steps'] for r in audit)
                overall['direct_dp_checks']=sum(r['checks'] for r in audit)
    (DEST/'summary.json').write_text(json.dumps(overall,indent=2))
    print(json.dumps(overall,indent=2))
    for f,n in CASES:
        rs=[r for r in summary if (r['family'],r['size'],r['effort'])==(f,n,0)]
        print(f,n,' | '.join(f"{r['method']} {r['restricted_ms']:.1f}ms {r['completed']}/8" for r in rs))

if __name__=='__main__':run()

