"""Typeset the paid-work and measured-time results after the independent outcome audit."""
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

from paper.batched_repair_benchmark import ROOT,DEST
from paper.report_batched_repair import load

TEX=ROOT/'paper/certificates'


def build():
    out=json.loads((DEST/'summary.json').read_text())
    specs,groups=load()
    lines=[r'\begin{table}[ht]\centering\small',
           r'\caption{Batched divided by fused eager. Work ratios include capped prefixes. Elapsed ratios use joint completions. Pooled elapsed uses total elapsed time across the matched repetitions, while the median gives equal weight to each input.}',
           r'\label{tab:actual-batch}',r'\begin{tabular}{@{}llrrrrr@{}}\toprule',
           r'Inputs & Sampler & Joint & Pooled work & Median work & Pooled time & Median time\\\midrule']
    for part,label in [('archive_broad','Archived broad'),('archive_overlap','Archived overlap'),
                       ('fresh_broad','Fresh broad'),('fresh_overlap','Fresh overlap')]:
        for name in ('compact','range'):
            v=out[part][name]
            vals=[v['pooled_work'],v['median_work'],v['pooled_time'],v['median_time']]
            lines.append(label+' & '+name.capitalize()+' & '+f"{v['joint']}/{v['cases']}"+
                         ' & '+' & '.join(f'{x:.3f}' if x is not None else '--' for x in vals)+r'\\')
    lines.append(r'\bottomrule\end{tabular}\end{table}')
    (TEX/'batched_repair_table.tex').write_text('\n'.join(lines)+'\n')
    fig,axes=plt.subplots(1,2,figsize=(8.8,3.5),sharey=True)
    styles=[('core_compact','Compact, eager','#087597','--'),('batch_compact','Compact, batch','#087597','-'),
            ('core_range','Range, eager','#995188','--'),('batch_range','Range, batch','#995188','-')]
    for ax,overlap in zip(axes,(False,True)):
        for m,label,color,style in styles:
            rr=[r[m] for k,g in groups.items() if specs[k]['cohort']=='archive' and
                (specs[k]['family']=='overlap')==overlap for r in g.values()]
            times=sorted(r['seconds'] for r in rr if r['status']=='certified')
            x=np.r_[.001,[t for t in times if .001<t<12],12]
            ax.step(x,np.searchsorted(times,x,side='right')/len(rr),where='post',
                    color=color,linestyle=style,linewidth=1.5,label=label)
        ax.set(title='Overlap stress test' if overlap else 'Broad cohort',xscale='log',xlim=(.001,12),
               ylim=(0,1.03),xlabel='Elapsed seconds')
        ax.grid(alpha=.18)
    axes[0].set_ylabel('Fraction certified')
    fig.legend(*axes[0].get_legend_handles_labels(),loc='lower center',ncol=2,frameon=False,fontsize=8)
    fig.subplots_adjust(bottom=.30,top=.89,left=.083,right=.98,wspace=.10)
    fig.savefig(TEX/'batched_repair_elapsed.png',dpi=165)
    plt.close(fig)


if __name__=='__main__':
    build()

