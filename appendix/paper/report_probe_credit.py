"""Replay the new matched cohort and reconcile sweep forecasts and capped results."""
import argparse
import csv
import json
from statistics import mean
from paper.probe_credit_benchmark import DEST,ROOT,METHODS,BUDGET,SECONDS,fixtures,measured,config,digest,pre_run
from paper.probe_credit import SweepBound
from paper.probe_credit_audit import audit
from paper.report_structural_price import logical_signature
from paper.uniform_price_benchmark import Tape


def report(replay=False):
    manifest=json.loads((DEST/'manifest.json').read_text())
    complete=json.loads((DEST/'complete.json').read_text())
    predictions=json.loads((DEST/'predictions.json').read_text())
    assert all(digest(ROOT/'paper'/n)==v for n,v in manifest['source'].items())
    assert digest(DEST/'predictions.json')==manifest['predictions']
    assert digest(DEST/'runs.jsonl')==complete['runs']
    assert all(digest(DEST/k)==v for k,v in complete['tapes'].items())
    rows=[json.loads(v) for v in (DEST/'runs.jsonl').read_text().splitlines()]
    index={(r['graph'],r['tape'],r['repeat'],r['method']):r for r in rows}
    assert len(index)==len(rows)==complete['rows']==864
    summaries=[]
    audits=[]
    signatures={}
    for spec,g in fixtures():
        name=spec['name']
        sig=logical_signature(g)
        assert signatures.setdefault(spec['seed'],sig)==sig
        label=pre_run(spec,g)
        assert label==predictions[name]
        positive=spec['layout']=='interleaved'
        bound=SweepBound(g,config(spec)) if positive else None
        rec=dict(graph=name,M=spec['M'],layout=spec['layout'])
        gaps=[]
        clipped=[]
        covers=[]
        scores=[]
        tight=[]
        for i in range(12):
            tape=(DEST/f'ties-{i:02}.bin').read_bytes()
            first=[index[name,i,0,m] for m in METHODS]
            for rep in (0,1):
                triple=[index[name,i,rep,m] for m in METHODS]
                if all(r['status']=='certified' for r in triple):
                    assert len({(r['action'],tuple(r['box']),r['draws'],r['tie_bytes'],r['queries']) for r in triple})==1
                    assert all(r['regret']<=spec['eps'] for r in triple)
                    if label['sign']=='immediate':
                        assert triple[2]['work']-triple[1]['work']>=label['margin']
                        assert not triple[2]['meta']['launch']
                    if rep and all(r['status']=='certified' for r in first):
                        assert [r['work'] for r in first]==[r['work'] for r in triple]
            score=lambda r:r['work'] if r['status']=='certified' else BUDGET
            gap=score(first[1])-score(first[2])
            gaps.append(gap)
            if positive:
                info=audit(g,bound,Tape(tape),early=False)
                assert info['score']>=-label['loss']
                if all(r['status']=='certified' for r in first):
                    assert info['score']<=gap and info['audit_lower']<=gap<=info['audit_lower']+128
                clipped.append(info['probes'][0][1]>=0)
                covers.append(info['covered'])
                scores.append(info['score'])
                tight.append(info['forecast'][0])
                audits.append(dict(graph=name,tape=i,gap=gap,**info))
            if replay and i==0:
                for r,m in zip(first,METHODS):
                    actual=json.loads(json.dumps(measured(spec,g,tape,i,m)))
                    assert all(actual[k]==r[k] for k in ('work','drop','draws','queries','action','box','tie_bytes','status'))
        rec.update(mean_gap=mean(gaps),deferred_wins=sum(v>0 for v in gaps),min_gap=min(gaps),max_gap=max(gaps),
                   sweep_covers=sum(covers) if positive else None,
                   first_clips=sum(clipped) if positive else None,
                   min_forecast=min(tight) if positive else None)
        for m in METHODS:
            group=[r for r in rows if r['graph']==name and r['method']==m]
            rec[m+'_returns']=sum(r['status']=='certified' for r in group)
            rec[m+'_work']=mean(r['work'] if r['status']=='certified' else BUDGET for r in group)
            rec[m+'_seconds']=mean(r['seconds'] if r['status']=='certified' else SECONDS for r in group)
        summaries.append(rec)
        print(name,round(rec['mean_gap']),rec['deferred_wins'],rec['sweep_covers'],rec['first_clips'],flush=True)
    with (DEST/'per_graph.csv').open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=summaries[0])
        writer.writeheader()
        writer.writerows(summaries)
    (DEST/'probe_audit.json').write_text(json.dumps(audits,indent=2))


if __name__=='__main__':
    cli=argparse.ArgumentParser()
    cli.add_argument('--replay',action='store_true')
    report(cli.parse_args().replay)
