"""Build the manuscript table directly from the paired endpoint records."""
import json
from statistics import mean
from paper.decision_price_benchmark import DEST, ROOT


def main():
    s=json.loads((DEST/'summary.json').read_text())
    c=json.loads((DEST/'credit_summary.json').read_text())
    family=json.loads((DEST/'family.json').read_text())['selected']
    extra=json.loads((DEST/'credit_complete.json').read_text())['family']
    body=[]
    for mode,label in [('reference','Full reference price'),('threshold','Threshold-only price'),
                       ('physical','Physical, still reconstruct'),('bare','Bare physical'),
                       ('credit','Credit after admission'),('credit-all','Credit at admission')]:
        if mode=='credit-all':
            work,seals,fresh,retie=(c['cohort']['work'],c['cohort']['seals'],c['fresh']['work'],
                                   c['witness-retie']['work'])
            constructed=mean(r['work'] for r in extra)
        else:
            work,seals=s['cohort'][mode]['mean_work'],s['cohort'][mode]['seals']
            fresh=s['fresh'][mode]['mean_work']
            retie=s['witness-retie'][mode]['mean_work']
            constructed=None if mode=='physical' else mean(r[mode]['work'] for r in family['runs'])
        cells=[label,f'{work/1e6:.3f}',str(seals),f'{fresh/1e6:.3f}',f'{retie/1e6:.3f}',
               '---' if constructed is None else f'{constructed/1e6:.3f}']
        body.append(' & '.join(cells)+r'\\')
    tex=r'''\begin{table*}[t]\centering\small
\caption{Mean charged work in millions, including capped runs. Original inputs
are equally weighted after averaging repeats. The last two columns are selected
graphs averaged over 16 and eight tie seeds, respectively. The policies that
reproduce reference decisions are listed first.}
\label{tab:decision-controls}
\begin{tabular}{@{}lrrrrr@{}}\toprule
Policy & Frozen (104) & Frozen seals & Fresh (64) & Selected (224 leaves) & Selected (232 leaves)\\
\midrule
'''+ '\n'.join(body)+r'''
\bottomrule\end{tabular}\end{table*}
'''
    (ROOT/'paper/certificates/decision_price_table.tex').write_text(tex)


if __name__=='__main__':
    main()
