"""Render the original-graph inference and held-out matched results."""
import csv
import json
from paper.fragment_sign_benchmark import DEST, ROOT


def write():
    validation=json.loads((DEST/'validation/summary.json').read_text())
    assert len(validation)==6
    sweep={r['seed']:r for r in json.loads((DEST/'sweep.json').read_text())}
    rows=list(csv.DictReader((DEST/'per_graph.csv').open()))
    lines=[r'\begin{table}[ht]\centering\small',
           r'\caption{Original graph expectations. Each signed figure in the fourth column is a simultaneous one-sided 99\% familywise confidence bound for the uncapped mean $\mathbb E[W_I-W_D]$, rounded conservatively to whole units. The last column gives the separate all-history guarantees.}\label{tab:fragment-means}',
           r'\begin{tabular}{@{}rlrrl@{}}\toprule Seed & Profile & Independent tapes & Bound on mean & All-history bound\\\midrule']
    for r in validation:
        s=r['seed']
        bound=int(r['lower'])
        signed=(r'$\ge '+f'{bound:,}'+r'$') if r['direction']==1 else (r'$\le -'+f'{bound:,}'+r'$')
        proof=(r'$\ge '+str(sweep[s]['conditional_gain'])+'$' if s in sweep and sweep[s]['certified'] else '---')
        if s==355003:
            assert json.loads((DEST/'shoulder.json').read_text())['remaining']==0
            proof=r'$\le-60$'
        lines.append(f"{s} & {'shoulder' if s==355003 else 'sharp'} & {r['n']} & {signed} & {proof}"+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{table}',
              r'\paragraph{Transfer protocol.} The graph-only prior favors deferred for sharp profiles of at most 224 leaves. The prefix rule favors deferred only when by query 256 an exactly clipped launch has occurred with positive endpoint-only margin after the full 64-unit disposal reserve. All other cases select immediate. Both were fixed before measuring the new graphs. The prefix check uses solely the ordinary evidence and index endpoints up to admission; it was evaluated off the timed path. These are predictions for two fixed routes, not measured savings for a paid switching solver.',
              r'\begin{table}[ht]\centering\small',
              r'\caption{New fragmented graphs under the original work, draw and wall caps. Means of two serial cold repetitions on each of 12 independent entropy tapes; times in seconds, work in millions. F, I and D denote full, immediate and deferred. The last column counts wins for D.}\label{tab:fragment-transfer}',
              r'\setlength{\tabcolsep}{3.5pt}\begin{tabular}{@{}lrrrrrrr@{}}\toprule Graph & $W_F$ & $W_I$ & $W_D$ & $t_F$ & $t_I$ & $t_D$ & Wins/12\\\midrule']
    for r in rows:
        names=('reference','immediate','threshold')
        values=[r['graph']]+[f"{float(r[n+'_work'])/1e6:.4f}" for n in names]+[
            f"{float(r[n+'_seconds']):.3f}" for n in names]+[r['wins']]
        lines.append(' & '.join(values)+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{table}',
              r'All 432 runs certified. Both rules matched all 72 paired signs; the 24 predictions for D had positive admission margins. On the new 256-terminal sharp input an uncertain launch led to about 2,304 charged predicate iterations and 137 refinements per tape. On the shoulder inputs records survived to retirement. The 192-terminal sharp graph favored D in work but I in mean elapsed time.',
              r'\paragraph{Reproduction.} The frozen protocol, raw timings, forecasts, public-state certificates, simultaneous intervals and entropy transcripts are in \path{results/fragment_sign_v1} and the replay package. Run \path{python -B -m paper.check_fragment_sweep --seed 378001} for the positive proof and \path{python -B -m paper.fragment_shoulder} for the reversal. Both use Node.js for the finite recursion. Run \path{python -B -m paper.validate_fragment_sign --replay} to check the statistical evidence.']
    (ROOT/'paper/certificates/fragment_sign_tables.tex').write_text('\n'.join(lines)+'\n')


if __name__=='__main__':write()
