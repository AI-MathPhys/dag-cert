"""Aggregate counterfactual bills only from verified archived endpoints."""
import hashlib
import json
import statistics
from collections import Counter
from paper.ancestor_repair_replay import ARCHIVE, DEST, ROOT


def bill(row):
    c=Counter(row['low'])+Counter(row['high'])
    assert c['eager']==c['clock_verified_pulls']
    assert c['eager']>=c['distinct_eager']>=c['batch_visits']>=c['batch_changed']
    w=row['work']
    naked=w-12*c['eager']-2*c['events']+12*c['batch_visits']+2*c['dirty_leaves']
    free=Counter(row['clock_free'])
    always_base=naked+c['book']+c['setup']
    base=always_base-free['setup']-2*free['events']
    return dict(**c,work=w,free_clock=naked,active_book=c['book']-2*free['events'],
                active_setup=c['setup']-free['setup'],active_price=c['strong_price']-free['strong_price'],
                active_events=c['events']-free['events'],
                point_bill=base+c['point_price']-free['point_price'],
                strong_bill=base+c['strong_price']-free['strong_price'],
                cert_bill=base+c['cert_price']-free['cert_price'],
                always_strong=always_base+c['strong_price'],always_cert=always_base+c['cert_price'],
                menu_base=base+c['oracle_strong_price']-free['oracle_strong_price'],
                menu_full=base+c['oracle_cert_price']-free['oracle_cert_price'])


def summarize(rows):
    bills=[bill(r) for r in rows]
    t=Counter()
    for b in bills:
        t.update(b)
    return dict(cases=len(rows),capped=sum(r['status']!='certified' for r in rows),totals=dict(t),
        batch_gain=1-t['strong_bill']/t['work'],
        median_batch_gain=statistics.median(1-b['strong_bill']/b['work'] for b in bills),
        batch_wins=sum(b['strong_bill']<b['work'] for b in bills),
        cert_gain=1-t['cert_bill']/t['strong_bill'],
        median_cert_gain=statistics.median(1-b['cert_bill']/b['strong_bill'] for b in bills),
        cert_wins=sum(b['cert_bill']<b['strong_bill'] for b in bills),
        menu_gain=1-t['menu_full']/t['menu_base'],
        always_gain=1-t['always_cert']/t['always_strong'],
        # Descriptive ceilings for this explicit materialization and tariff.
        residual_parent_ceiling=12*t['batch_visits']/t['strong_bill'],
        unchanged_parent_ceiling=12*(t['batch_visits']-t['batch_changed'])/t['strong_bill'],
        free_residual_ceiling=(12*t['batch_visits']+t['active_price']+t['active_setup']+t['active_book'])/t['strong_bill'],
        pure_repair_coalesced=1-t['batch_visits']/max(1,t['eager']),
        price_sensitivity={str(x):1-(t['free_clock']+x*(t['cert_bill']-t['free_clock']))/
            (t['free_clock']+x*(t['strong_bill']-t['free_clock'])) for x in (.5,1,2)})


def run():
    manifest=json.loads((DEST/'manifest.json').read_text())
    stamp=json.loads((DEST/'complete.json').read_text())
    def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest(DEST/'cases.jsonl')==stamp['sha256']
    assert digest(ARCHIVE/'runs.jsonl')==manifest['archive_sha256']
    assert digest(ROOT/'paper/ancestor_repair_replay.py')==manifest['code_sha256']
    assert digest(ROOT/'paper/ancestor_repair_protocol.txt')==manifest['protocol_sha256']
    rows=[json.loads(line) for line in (DEST/'cases.jsonl').read_text().splitlines()]
    assert len(rows)==stamp['records']==160 and len({(r['method'],r['case']) for r in rows})==160
    out={}
    for m in ('core_compact','core_range'):
        subset=[r for r in rows if r['method']==m]
        sets={'broad':[r for r in subset if r['family']!='overlap'],
              'overlap':[r for r in subset if r['family']=='overlap']}
        for fam in {r['family'] for r in subset}:
            sets[fam]=[r for r in subset if r['family']==fam]
        for eps in (.02,.0125):
            sets['overlap_'+str(eps)]=[r for r in sets['overlap'] if r['epsilon']==eps]
        out[m]={k:summarize(v) for k,v in sets.items()}
    (DEST/'summary.json').write_text(json.dumps(out,indent=2))
    return out


def table(out):
    lines=[r'\begin{table}[t]\centering\small',
       r'\caption{Public index repairs on the recorded observation paths. Pull counts are pooled millions across the inputs. Batch counts include the first unchanged parent. Extra saving compares the paid two-leaf certificate with the strong clock-aware batch, as a percentage of total work.}',
       r'\label{tab:ancestor-replay}',r'\begin{tabular}{@{}llrrrrr@{}}\toprule',
       r'Sampler & Cohort & Eager pulls & Batch pulls & Changed & Batch saving & Extra saving\\\midrule']
    for m,label in [('core_compact','Compact'),('core_range','Range')]:
        for part in ('broad','overlap'):
            v=out[m][part];t=v['totals']
            vals=[f"{t[x]/1e6:.2f}" for x in ('eager','batch_visits','batch_changed')]
            lines.append(f'{label} & {part.capitalize()} & '+' & '.join(vals)+
                ' & '+f"{100*v['batch_gain']:.1f}"+r'\% & '+f"{100*v['cert_gain']:.2f}"+r'\%\\')
    lines.append(r'\bottomrule\end{tabular}\end{table}')
    (ROOT/'paper/certificates/ancestor_repair_table.tex').write_text('\n'.join(lines)+'\n')


if __name__=='__main__':
    table(run())

