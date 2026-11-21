"""Build selector and common-support tables from the complete paired records."""
import json
from paper.prefix_routing_benchmark import DEST, METHODS, base


def build():
    main=json.loads((DEST/'summary.json').read_text())
    other=json.loads((DEST/'overlap_summary.json').read_text())
    cases=[('Original',main,'selected_'),('Transfer',main,'transfer_'),('Twin support',other,'overlap_')]
    tex=r'''\begin{table}[ht]\centering\small
\caption{Mean capped work in millions, including abstentions at the work cap.
Within a graph, lower and higher background shifts have weights $7/8$ and
$1/8$. Transfer graphs are equally weighted. Columns give full pricing,
threshold-only pricing, bare pricing, credit after admission, credit at
admission, the known-range rule, and the online rule.}
\label{tab:prefix-costs}
\begin{tabular}{@{}llrrrrrrr@{}}\toprule
Cohort & Rewards & Full & Threshold & Bare & Post & All & Ranges & Online\\ \midrule
'''
    for group,data,prefix in cases:
        labels=(('constant','constant'),('mixed',r'1\% swap-to-Bernoulli'),('bernoulli','Bernoulli'))
        if group=='Twin support':labels=(('0.05',r'$\alpha=.05$'),('0.45',r'$\alpha=.45$'))
        for noise,label in labels:
            methods=data[prefix+noise]['methods']
            tex+=' & '.join([group,label]+[f"{methods[m]['mean_loss']/1e6:.3f}" for m in METHODS])+r'\\'+'\n'
    tex+=r'\bottomrule\end{tabular}\end{table}'+'\n'
    (base.ROOT/'paper/certificates/prefix_cost_table.tex').write_text(tex)


if __name__=='__main__':
    build()
