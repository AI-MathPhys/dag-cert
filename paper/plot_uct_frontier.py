"""Standalone vector figures from the frozen summary CSVs."""
import argparse
import csv
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def run(data,out):
    data,out=Path(data),Path(out);out.mkdir(parents=True,exist_ok=True)
    rows=list(csv.DictReader((data/'per_graph.csv').open()))
    methods=('graph-eager','graph-live','cover-live','covers')
    labels=('Graph eager','Graph selective','Compiled selective','Covers')
    colors=('#536878','#d55e00','#0072b2','#009e73')
    plt.rcParams.update({'font.size':9,'axes.spines.top':False,'axes.spines.right':False,
                         'pdf.fonttype':42,'ps.fonttype':42})
    fig,axes=plt.subplots(1,2,figsize=(7.0,2.65),layout='constrained',
                          gridspec_kw={'width_ratios':[1,1.35]})
    ax=axes[0]
    for m,label,c in zip(methods,labels,colors):
        ys=[]
        for k in (8,16,32):
            vals=[float(r['restricted_ms']) for r in rows if r['family']=='coded'
                  and int(r['size'])==k and r['method']==m and r['effort']=='0']
            ys.append(np.mean(vals))
        ax.plot((8,16,32),ys,'o-',label=label,color=c,ms=4)
    ax.set_xscale('log',base=2);ax.set_yscale('log')
    ax.set_xticks((8,16,32),('8','16','32'))
    ax.set_yticks((20,100,500),(20,100,500))
    ax.set_xlabel('Coordinate size r');ax.set_ylabel('Certification time (ms)')
    ax.set_title('(a) Every-layout construction')
    ax.legend(fontsize=7,frameon=False,loc='upper left')
    ax=axes[1]
    cases=[]
    for r in rows:
        key=r['family'],int(r['size'])
        if key not in cases:cases.append(key)
    names={'coded':'Code','dense':'Dense','sparse':'Sparse','samegame':'Game','lattice':'Lattice','funnel':'Funnel'}
    for i,(f,n) in enumerate(cases):
        seeds=sorted(set(r['seed'] for r in rows if r['family']==f and int(r['size'])==n))
        ratios=[]
        for j,seed in enumerate(seeds):
            rs=[r for r in rows if (r['family'],int(r['size']),r['seed'],r['effort'])==(f,n,seed,'0')]
            ours=next(float(r['restricted_ms']) for r in rs if r['method']=='graph-live')
            best=min(float(r['restricted_ms']) for r in rs if r['method']!='graph-live')
            ratios.append(ours/best)
            ax.scatter(i+(j-1.5)*.12,ours/best,s=13,color=colors[1],alpha=.65)
        ax.plot([i-.25,i+.25],[np.median(ratios)]*2,color='black',lw=1.2)
    ax.axhline(1,color='gray',ls='--',lw=1)
    ax.set_xticks(range(len(cases)),[f'{names[f]} {n}' for f,n in cases],rotation=55,ha='right',fontsize=7)
    ax.set_ylabel('Selective / fastest other method')
    ax.set_title('(b) Paired restricted-time ratios')
    fig.savefig(out/'uct_frontier.pdf');fig.savefig(out/'uct_frontier.png',dpi=170)
    plt.close(fig)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--data',default='results/uct_frontier_v1')
    p.add_argument('--out',default='paper/certificates/figures')
    a=p.parse_args();run(a.data,a.out)

