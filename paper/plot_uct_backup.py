"""Paired cold certification plots for the manuscript."""
import argparse
import csv
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

COLORS = {'eager':'#4a5261','live':'#bc4629','flat':'#376d9c','covers':'#19795e'}
NAMES = {'eager':'Edge-eager','live':'Selective','flat':'Explicit supports','covers':'Shared covers'}
MARKERS = {'eager':'s','live':'o','flat':'^','covers':'D'}


def topology(out):
    # The binary routes are contracted in the schematic.
    fig,axes=plt.subplots(1,2,figsize=(6.8,2.48))
    for ax in axes:
        ax.set(xlim=(0,10),ylim=(0,9))
        ax.axis('off')
    def label(ax,x,y,s,color='#203a50',bg='white'):
        ax.text(x,y,s,ha='center',va='center',fontsize=8,color=color,zorder=3,
                bbox=dict(boxstyle='round,pad=.2',facecolor=bg,edgecolor=color,linewidth=.7))
    def line(ax,x,y,u,v,color='#67727a',dashed=False):
        ax.plot((x,u),(y,v),color=color,lw=1.1,ls='--' if dashed else '-',zorder=1)
    ax=axes[0]
    ax.set_title('A. A dominated branch can lose all subscriptions',fontsize=9)
    label(ax,4.5,7.6,'root')
    for x,s in [(1.1,'$b$'),(3.3,'$b-g$'),(7.2,'$C$')]:
        line(ax,4.5,7.6,x,5.9,'#ac452a' if s=='$C$' else '#67727a',s=='$C$')
        label(ax,x,5.9,s)
    ax.text(3.9,4.25,'binary paths',ha='center',va='center',fontsize=7)
    for x in (5.3,6.1,8.3,9.1):
        line(ax,7.2,5.7,x,3.15)
        label(ax,x,3.1,'$p$')
        line(ax,x,3.0,5.7 if x<7 else 8.7,1.6)
    label(ax,5.7,1.5,'1/8',bg='#f1f5f6')
    label(ax,8.7,1.5,'3/8',bg='#f1f5f6')
    ax.text(.4,.25,'Each low exit has $m/2$ bottom parents.',fontsize=8)
    ax=axes[1]
    ax.set_title('B. Distinct root supports share a common core',fontsize=9)
    label(ax,4.8,7.6,'root')
    for x,s in [(1.1,'1'),(4.1,'$B_1$'),(8.0,'$B_r$')]:
        label(ax,x,5.9,s)
        line(ax,4.8,7.6,x,5.9)
    ax.text(6.05,5.9,'...',ha='center')
    for x,target,s in ((4.1,2.0,'private 0'),(8.0,9.,'private 0')):
        line(ax,x,5.9,target,2.1)
        label(ax,target,2.1,s)
        line(ax,x,5.9,5.8,3.5)
    label(ax,5.8,3.5,'shared hub')
    line(ax,5.8,3.5,5.8,1.5)
    label(ax,5.8,1.5,'$r^2$ zero terminals',bg='#f1f5f6')
    ax.text(.4,.25,'Each explicit losing support lists the entire core.',fontsize=8)
    fig.tight_layout(pad=.3)
    fig.savefig(out/'uct_constructions.pdf',bbox_inches='tight')
    plt.close(fig)


def run(data,out):
    with (data/'certification.csv').open(newline='') as fp:
        rows = list(csv.DictReader(fp))
    fig,axes = plt.subplots(1,2,figsize=(6.7,2.58))
    for ax,case,title,xlabel in zip(axes,('two-exit','core'),
            ('Two low exits','Overlapping root supports'),('Bottom parents','Losing actions')):
        for method in COLORS:
            group = [r for r in rows if r['family']==case and r['method']==method]
            x = [int(r['size']) for r in group]
            y = [float(r['rmst_ms']) for r in group]
            ax.plot(x,y,color=COLORS[method],marker=MARKERS[method],markersize=4,
                    label=NAMES[method],lw=1.5)
        ax.set_xscale('log',base=2)
        ax.set_yscale('log')
        ticks = (10,20,50,100,250) if case=='two-exit' else (5,10,20,50)
        ax.set_yticks(ticks,labels=[str(tick) for tick in ticks])
        ax.set_ylim((9,330) if case=='two-exit' else (4.5,90))
        ax.set_xticks(x,labels=[str(n) for n in x])
        ax.set_xlabel(xlabel,fontsize=9)
        ax.set_title(title,fontsize=10)
        ax.tick_params(labelsize=8)
        ax.spines[['top','right']].set_visible(False)
        ax.grid(axis='y',which='major',alpha=.25)
    axes[0].set_ylabel('Mean time to certify (ms)',fontsize=9)
    fig.legend(*axes[0].get_legend_handles_labels(),loc='lower center',ncols=4,fontsize=8,
               frameon=False,bbox_to_anchor=(.5,-.015))
    fig.tight_layout(rect=(0,.13,1,1))
    out.mkdir(exist_ok=True,parents=True)
    fig.savefig(out/'uct_certification.pdf',bbox_inches='tight')
    plt.close(fig)
    topology(out)


if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    parser=argparse.ArgumentParser()
    parser.add_argument('--data',type=Path,default=root/'results/uct_backup_v1')
    parser.add_argument('--out',type=Path,default=root/'paper/certificates/figures')
    args=parser.parse_args()
    run(args.data,args.out)
