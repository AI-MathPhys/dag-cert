"""Forecast audit, uncensored paired endpoints and matched graph-level results."""
import csv
import json
from collections import defaultdict
from statistics import mean
from paper.fragment_sign_audit import audit
from paper.fragment_sign_benchmark import DEST,BUDGET,SECONDS
from paper.uniform_price_benchmark import Tape


def run():
    specs=json.loads((DEST/'manifest.json').read_text())['graphs']
    rows=[json.loads(l) for l in (DEST/'runs.jsonl').read_text().splitlines()]
    assert len(rows)==432
    all_runs={(r['graph'],r['tape'],r['method'],r['repeat']):r for r in rows}
    cases=[];graphs=[]
    for s in specs:
        graph=s['name']; g=[]
        for i in range(12):
            data=(DEST/f'ties-{i:02}.bin').read_bytes()
            early=audit(s,Tape(data),True)
            audit_row=audit(s,Tape(data))
            methods={m:[all_runs[graph,i,m,k] for k in range(2)] for m in ('reference','immediate','threshold')}
            for k in range(2):
                if all(rs[k]['status']=='certified' for rs in methods.values()):
                    assert len({(rs[k]['draws'],rs[k]['action'],rs[k]['tie_bytes']) for rs in methods.values()})==1
            gap=methods['immediate'][0]['work']-methods['threshold'][0]['work']
            joint=all(rs[0]['status']=='certified' for rs in methods.values())
            if joint:assert audit_row['low']<=gap<=audit_row['high']
            actual='deferred' if gap>0 else 'immediate' if gap<0 else 'tie'
            prior='deferred' if s['profile']=='sharp' and s['M']<=224 else 'immediate'
            g.append(dict(graph=graph,tape=i,prior=prior,predicted=early['sign'],actual=actual,joint=joint,
                          gap=gap,correct=early['sign']==actual,prior_correct=prior==actual,
                          lower_at_launch=early['lower'],exact_at_launch=early['exact'],launch_q=early['q'],
                          scan=audit_row['scan'],storage=audit_row['storage'],checks=audit_row['checks'],
                          refinements=audit_row['refinements'],live_fee=audit_row['live_fee']))
        record=dict(graph=graph,tapes=len(g),prior=g[0]['prior'],prior_correct=sum(x['prior_correct'] for x in g),
                    early_correct=sum(x['correct'] for x in g),sufficient_positive=sum(x['predicted']=='deferred' for x in g),
                    wins=sum(x['actual']=='deferred' for x in g),mean_gap=mean(x['gap'] for x in g))
        for m in ('reference','immediate','threshold'):
            rs=[r for r in rows if r['graph']==graph and r['method']==m]
            record[m+'_returns']=sum(r['status']=='certified' for r in rs)
            record[m+'_work']=mean(r['work'] if r['status']=='certified' else BUDGET for r in rs)
            record[m+'_seconds']=mean(r['seconds'] if r['status']=='certified' else SECONDS for r in rs)
        graphs.append(record);cases.extend(g)
    for name,content in [('per_graph',graphs),('predictions',cases)]:
        with (DEST/(name+'.csv')).open('w',newline='') as file:
            w=csv.DictWriter(file,fieldnames=content[0]);w.writeheader();w.writerows(content)
    print([(g['graph'],g['early_correct'],g['mean_gap']) for g in graphs])


if __name__=='__main__':run()
