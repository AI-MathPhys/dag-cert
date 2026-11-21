"""Summarize the matched experiment without conditioning away resource stops."""
import csv
import argparse
import json
from collections import defaultdict
from statistics import mean
from paper.uniform_price_benchmark import DEST, BUDGET, SECONDS, METHODS, digest, run_one


def summarize(replay=False):
    manifest=json.loads((DEST/'manifest.json').read_text())
    complete=json.loads((DEST/'complete.json').read_text())
    assert digest(DEST/'runs.jsonl')==complete['sha256']
    for name,sha in complete['tapes'].items():
        assert digest(DEST/name)==sha
    rows=[json.loads(s) for s in (DEST/'runs.jsonl').read_text().splitlines()]
    assert len(rows)==complete['rows']==len(manifest['graphs'])*manifest['tapes']*6
    paired=defaultdict(dict)
    for r in rows:
        key=r['graph'],r['tape'],r['repeat']
        assert r['method'] not in paired[key]
        paired[key][r['method']]=r
    summary=[]
    for s in manifest['graphs']:
        if replay:
            data=(DEST/'ties-00.bin').read_bytes()
            for m in METHODS:
                new=run_one(s,data,383001,m)
                old=paired[s['name'],0,0][m]
                assert all(new[k]==old[k] for k in ('work','draws','tie_bytes','action','status'))
        groups=[paired[s['name'],i,rep] for i in range(manifest['tapes']) for rep in range(2)]
        gaps=[]
        for g in groups:
            assert set(g)==set(METHODS)
            if all(r['status']=='certified' for r in g.values()):
                assert len({(r['action'],r['draws'],tuple(r['box']),r['tie_bytes']) for r in g.values()})==1
            if g['reference']['repeat']==0:
                cost=lambda r: r['work'] if r['status']=='certified' else BUDGET
                gaps.append(cost(g['immediate'])-cost(g['threshold']))
        record=dict(graph=s['name'],tapes=len(gaps),positive=sum(v>0 for v in gaps),
                    zero=gaps.count(0),mean_gap=mean(gaps),min_gap=min(gaps),max_gap=max(gaps))
        for m in METHODS:
            runs=[g[m] for g in groups]
            ok=[r for r in runs if r['status']=='certified']
            record[m+'_returns']=len(ok)
            record[m+'_work']=mean(r['work'] if r['status']=='certified' else BUDGET for r in runs)
            record[m+'_seconds']=mean(r['seconds'] if r['status']=='certified' else SECONDS for r in runs)
            record[m+'_actual_work']=mean(r['work'] for r in runs)
        summary.append(record)
    with (DEST/'per_graph.csv').open('w',newline='') as out:
        w=csv.DictWriter(out,fieldnames=list(summary[0]))
        w.writeheader()
        w.writerows(summary)
    proof=json.loads((DEST/'uniform_proof.json').read_text())
    lines=[r'\begin{table}[ht]\centering\small',
           r'\caption{Exhaustive public-state certificate. The warm column counts completed blocks; the probe column lists every layer at which the verifier permits admission. A blank bound means no positive certificate was obtained.}\label{tab:uniform-proof}',
           r'\begin{tabular}{@{}lrrrr@{}}\toprule Graph & Warm & States visited & Probes & Lower bound on $W_I-W_D$\\\midrule']
    for r in proof:
        probes=', '.join(str(q) for q in r.get('probe_margins',{}))
        lower=f"{r['lower']:,}" if r.get('certified') else '---'
        lines.append(f"{r['graph']} & {r.get('warm','---')} & {r.get('visited','---')} & {probes or '---'} & {lower}"+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{table}',
              r'\paragraph{Fresh-rank experiments.} We froze four interleaved inputs and four independently specified fragmented graph--law inputs, crossing sharp/shoulder profiles with constant/Bernoulli rewards. Each graph receives the same 16 independent OS entropy tapes. Rejecting the incomplete residue class of a 32-bit word gives a uniform rank for every adaptively requested tie width. All methods receive the same terminal streams and the same tape on a graph. Two cold repetitions in reversed within-triple orders give 768 runs. Elapsed time includes consuming the stored tie tape and releasing the search state; generating the shared environment tapes is outside timing. The limits are 102.4 million work units, 262,144 draws and 12 seconds. Across graphs the tapes are coupled, not independent replications of topology.',
              r'\begin{table}[ht]\centering\small',
              r'\caption{Work to certification (millions) and elapsed seconds, averaged across both repetitions. F, I and D denote full, immediate and deferred. Wins counts fresh tapes with smaller D work than I. An unfinished run incurs the relevant cap.}\label{tab:uniform-timing}',
              r'\setlength{\tabcolsep}{4pt}\begin{tabular}{@{}lrrrrrrr@{}}\toprule Graph & $W_F$ & $W_I$ & $W_D$ & $t_F$ & $t_I$ & $t_D$ & Wins/16\\\midrule']
    for r in summary:
        cells=[r['graph']]+[f"{r[m+'_work']/1e6:.4f}" for m in METHODS]+[
            f"{r[m+'_seconds']:.3f}" for m in METHODS]+[str(r['positive'])]
        lines.append(' & '.join(cells)+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{table}',
              r'The per-graph CSV also gives actual charges, return counts, and the minimum and maximum paired difference. The raw rows and consumed entropy prefixes are in \path{results/uniform_price_v1}; \path{paper/uniform_price_proof.py} reproduces the proof without reading those measurements.']
    folder=DEST.parents[1]/'paper/certificates'
    folder.mkdir(parents=True,exist_ok=True)
    (folder/'uniform_price_table.tex').write_text('\n'.join(lines)+'\n')
    print(json.dumps(summary,indent=2))
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--replay',action='store_true',help='replay one stored common entropy tape per graph')
    summarize(parser.parse_args().replay)
