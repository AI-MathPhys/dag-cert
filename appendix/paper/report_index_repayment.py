"""Exact tariff decomposition, prospectively observable signs, and a free routing ceiling."""
from collections import Counter, defaultdict
import json
from statistics import median
from paper.index_repayment_audit import DEST, ROOT, digest


def subset(rows):
    counts=Counter()
    classes=defaultdict(Counter)
    for r in rows:
        counts.update(r['counts'])
        for k,v in r['classes'].items():
            classes[k].update(v)
    return dict(inputs=len(rows),full=sum(r['full'] for r in rows),counts=counts,classes=classes)


def predictions(rows,key,eligible=lambda r:True):
    tally=Counter()
    leads=[]
    fees=[]
    for r in rows:
        if not eligible(r):continue
        tally['inputs']+=1
        x=r[key]
        if x is None or (key=='launch' and not x['exact']):
            tally['not_applicable']+=1
            continue
        tally['available']+=1
        if x['sign']=='abstain':
            tally['abstain']+=1
            continue
        truth='threshold' if r['counts']['saving']>0 else 'full' if r['counts']['saving']<0 else 'tie'
        tally[x['sign']]+=1
        tally['right' if x['sign']==truth else 'wrong']+=1
        if x['sign']=='threshold':
            tally['threshold_correct']+=int(truth=='threshold')
            fees.append((x['lo']-64)/max(1,x['groups']))
        leads.append(r['draws']-x['draws'])
    return dict(counts=tally,median_lead=median(leads) if leads else None,
                min_lead=min(leads) if leads else None,
                median_positive_slack_per_long=median(fees) if fees else None,
                positive_after_monitor={fee:sum(s>fee for s in fees) for fee in (0,8,16)})


def hindsight():
    folder=ROOT/'results/prefix_routing_v1'
    stamp=json.loads((folder/'complete.json').read_text())
    source=folder/'runs.jsonl'
    assert digest(source)==stamp['sha256']
    costs=defaultdict(dict)
    for line in source.read_text().splitlines():
        r=json.loads(line)
        if r['tag']=='transfer' and r['method'] in ('bare','credit-all'):
            assert r['status']=='certified'
            costs[r['noise'],r['graph'],r['tie'],r['shift']][r['method']]=r['work']
    out={}
    for noise in ('constant','mixed','bernoulli'):
        cells=[(7 if k[3]==.05 else 1, v) for k,v in costs.items() if k[0]==noise]
        assert len(cells)==48 and all(len(v)==2 for w,v in cells)
        weight=sum(w for w,v in cells)
        fixed=min(sum(w*v[m] for w,v in cells)/weight for m in ('bare','credit-all'))
        oracle=sum(w*min(v.values()) for w,v in cells)/weight
        out[noise]=dict(fixed=fixed,oracle=oracle,headroom=1-oracle/fixed)
    return dict(source=stamp['sha256'],settings=out)


def tex_table(result):
    groups=[result[tag]['joint'] for tag in ('cohort','fresh')]
    rows=[
        ('Full per-event scan work',lambda c:c['point']),
        ('Additional bound construction',lambda c:c['screen']-c['bound']),
        ('Record retention',lambda c:-c['storage']),
        ('Refinements',lambda c:-c['refinement']),
        ('Comparisons and rechecks',lambda c:-c['comparisons']),
        ('Setup difference',lambda c:-c['setup']),
        ('Retirement of live records and profiles',lambda c:-c['live_retirement']),
        ('Other disposal difference',lambda c:c['live_retirement']-c['disposal']),
        ('Net saving',lambda c:c['saving'])]
    lines=[label+' & '+' & '.join(f"{value(g['counts'])/1e6:+.3f}" for g in groups)+r'\\'
           for label,value in rows]
    src=r'''\begin{table}[ht]\centering\small
\caption{Reconciled full-minus-threshold work (millions) on joint certifications.
Both columns use one run per input. A positive entry favors threshold pricing.
Live-record retirement is measured by the difference in the disposal walk with
the pending records present and absent, outside all search timers.}
\label{tab:repair-bridge}
\begin{tabular}{@{}lrr@{}}\toprule
Component & Original (100) & Transfer (64)\\ \midrule
'''+ '\n'.join(lines[:-1])+ '\n'+r'\midrule'+'\n'+lines[-1]+'\n'+r'\bottomrule\end{tabular}\end{table}'+'\n'
    return src


def main(write_table=False):
    path=DEST/'cases.jsonl'
    stamp=json.loads((DEST/'complete.json').read_text())
    rows=[json.loads(l) for l in path.read_text().splitlines()]
    assert digest(path)==stamp['sha256'] and len(rows)==stamp['rows']==168
    result={}
    for tag in ('cohort','fresh'):
        rs=[r for r in rows if r['tag']==tag]
        done=[r for r in rs if r['status']=='certified']
        result[tag]=dict(all=subset(rs),joint=subset(done),
                         admitted=subset([r for r in done if r['launch']]),
                         never_admitted=subset([r for r in done if not r['launch']]),
                         prefix=predictions(rs,'prefix'),
                         prefix_active=predictions(rs,'prefix',lambda r:r['prefix'] is not None and not r['prefix'].get('closed_screen')),
                         launch=predictions(done,'launch'))
    result['hindsight']=hindsight()
    (DEST/'summary.json').write_text(json.dumps(result,indent=2))
    if write_table:
        (ROOT/'paper/certificates/index_repayment_table.tex').write_text(tex_table(result))
    for tag in ('cohort','fresh'):
        print(tag,result[tag]['all']['counts'],result[tag]['prefix'],result[tag]['launch'])


if __name__=='__main__':
    import sys
    main('--table' in sys.argv)
