"""Regenerate the ICML figures from the frozen paired comparisons."""
import argparse
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

ROOT = Path(__file__).resolve().parents[1]
CLOCK = 'repair_policy_clock_v1'
BLUE, ORANGE, INK, GREY = '#195A87', '#9B4A15', '#202B32', '#66737D'


def read(path):
    return json.loads(path.read_text())


def rows(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def finish(fig, dest, name):
    # Fixed figure dimensions give consistent type sizes at column width.
    fig.savefig(dest / (name+'.pdf'), metadata={'Creator':'Matplotlib','CreationDate':None})
    fig.savefig(dest / (name+'.png'), dpi=220)
    plt.close(fig)


def witness(data, dest):
    case = read(data/CLOCK/'construction.json')['witness']['comparison']
    check = read(data/CLOCK/'witness_check.json')
    g = case['shared_probe']
    obs = case['first_observation']
    branch = case['first_branch'][0]
    fig, (ax,bars) = plt.subplots(1,2,figsize=(6.72,2.22),gridspec_kw={'width_ratios':[1.45,1]})
    fig.subplots_adjust(left=.015,right=.985,top=.84,bottom=.19,wspace=.25)
    ax.set(xlim=(0,1),ylim=(0,1))
    ax.axis('off')
    ax.set_title('(a)   A shared history, then two decisions',loc='left')
    ax.text(.01,.88,f"Query {g[0]['q']}   ·   {g[0]['draws']:,} draws",weight='bold')
    ax.text(.01,.75,'Same witnesses. Both clocks open a trial.')
    ax.plot([.055,.055],[.43,.67],color=GREY,lw=1.7)
    ax.scatter([.055],[.54],color=INK,s=17,zorder=3)
    ax.text(.105,.54,f"Progress check at draw {branch['draws']:,}",va='center',weight='bold')
    for y, col, label, leaf in [(.30,BLUE,'Reference continues',obs['reference'][0]),(.073,ORANGE,'Physical aborts',obs['physical'][0])]:
        ax.plot([.055,.055,.12],[.43,y,y],color=col,lw=1.5,solid_capstyle='round')
        ax.text(.15,y,f'{label}   →   vertex {leaf}',color=col,va='center',weight='bold')
    ax.text(.01,-.14,f"First different observation: draw {obs['index']:,}.",color=GREY)
    bars.set_title('(b)   Work to certification',loc='left')
    selected=read(data/'decision_price_v1/summary.json')['selected']
    extra=read(data/'decision_price_v1/credit_summary.json')['selected']
    methods=[('Full price','reference',BLUE),('Threshold','threshold','#33795F'),
             ('Physical','physical',ORANGE),('Unpriced','bare',GREY),('Credit post','credit','#754768'),
             ('Credit all','credit-all','#574278')]
    assert selected['reference']['mean_work']==check['reference']
    for i,(label,key,color) in enumerate(methods):
        y=len(methods)-1-i
        value=(extra['work'] if key=='credit-all' else selected[key]['mean_work'])/1e6
        bars.barh(y,value,color=color,height=.72)
        bars.text(.10,y,label,va='center',color='white',fontsize=7)
        bars.text(value+.11,y,f'{value:.2f}',va='center',fontsize=8)
    bars.set(xlim=(0,8.05),ylim=(-.50,5.55),yticks=[],xticks=[0,2,4,6,8],xlabel='Charged work (millions)')
    finish(fig,dest,'pricing_witness')


def incidence(data,dest):
    t=rows(data/CLOCK/'trace.jsonl')
    subsets=[('Original broad',False,False),('New broad',True,False),
             ('Original overlap',False,True),('New overlap',True,True)]
    fig,ax=plt.subplots(figsize=(3.27,2.20))
    fig.subplots_adjust(left=.36,right=.96,bottom=.25,top=.82)
    for i,(name,fresh,overlap) in enumerate(subsets):
        group=[r for r in t if (r['cohort']=='fresh')==fresh and (r['family']=='overlap')==overlap]
        n=len(group)
        price=sum(bool(r['first_price']) for r in group)
        obs=sum(bool(r['first_observation']) for r in group)
        assert obs==sum(bool(r['first_branch']) for r in group)
        y=3-i
        ax.barh(y,100,color='#E7EBED',height=.56)
        ax.barh(y,100*price/n,color='#8DAFC6',height=.56)
        ax.barh(y,100*obs/n,color=ORANGE,height=.56)
        ax.text(98,y,f'{obs}/{n}',ha='right',va='center',fontsize=8,weight='bold')
    ax.set(yticks=range(4),yticklabels=[r[0] for r in subsets][::-1],xlim=(0,100),
           xticks=[0,25,50,75,100],xlabel='Fraction of inputs (%)')
    ax.legend(handles=[Patch(color='#8DAFC6',label='Allowance only'),Patch(color=ORANGE,label='Draw')],
              loc='lower left',bbox_to_anchor=(-.02,1.0),ncol=2,frameon=False,
              borderaxespad=0,handlelength=.9,columnspacing=1.0)
    ax.set_ylim(-.52,3.52)
    finish(fig,dest,'pricing_incidence')


def batching(data,dest):
    s=read(data/'batched_repair_v1/summary.json')
    fig,ax=plt.subplots(figsize=(3.27,2.35))
    fig.subplots_adjust(left=.36,right=.97,bottom=.22,top=.79)
    groups=[('Original broad','archive_broad'),('New broad','fresh_broad'),
            ('Original overlap','archive_overlap'),('New overlap','fresh_overlap')]
    ax.axvline(1,color=GREY,lw=.85,ls='--')
    for i,(_,cohort) in enumerate(groups):
        for sampler,dy,col,mark in [('compact',.13,BLUE,'o'),('range',-.13,ORANGE,'s')]:
            z=s[cohort][sampler]['ratios']['seconds']
            l,h=z['ci']
            y=3-i+dy
            ax.hlines(y,l,h,color=col,lw=1.4)
            ax.scatter(z['ratio'],y,s=19,marker=mark,color=col,zorder=3)
    ax.set(ylabel='',yticks=range(4),yticklabels=[p[0] for p in groups][::-1],ylim=(-.6,3.6),
           xlim=(.54,1.08),xticks=[.6,.7,.8,.9,1],xlabel='Time ratio  ·  batch / fused eager')
    ax.xaxis.set_major_formatter(FuncFormatter(lambda x,_: f'{x:.1f}'))
    handles=[Line2D([],[],color=c,marker=m,lw=1.3,label=n) for n,c,m in
             [('Compact',BLUE,'o'),('Range',ORANGE,'s')]]
    ax.legend(handles=handles,loc='lower left',bbox_to_anchor=(-.02,.99),ncol=2,frameon=False,
              borderaxespad=0,handlelength=1.1,columnspacing=1.1)
    finish(fig,dest,'pricing_batching')


def mixture_weights(data,dest):
    folder=data/'decision_price_v1'
    mix=read(folder/'same_graph.json')['selected']
    a,b=mix['a']['runs'],mix['b']['runs']
    fig,ax=plt.subplots(figsize=(3.27,2.04))
    fig.subplots_adjust(left=.30,right=.95,top=.91,bottom=.29)
    intervals=[]
    methods=[('Credit all','credit-all',ORANGE),('Threshold','threshold',BLUE),
             ('Credit post','credit',GREY),('Bare','bare','#33795F')]
    for i,(name,m,color) in enumerate(methods):
        x=sum(r[m]['work']-r['reference']['work'] for r in a)
        y=sum(r[m]['work']-r['reference']['work'] for r in b)
        if min(x,y)>0:
            lo,hi=0,1
        elif max(x,y)<=0:
            continue
        else:
            cross=-y/(x-y)
            lo,hi=(cross,1) if x>0 else (0,cross)
            ax.scatter(cross,i,color=color,s=16)
        intervals.append((lo,hi))
        ax.hlines(i,lo,hi,color=color,lw=3)
    lo=max(x[0] for x in intervals)
    hi=min(x[1] for x in intervals)
    ax.axvspan(lo,hi,color='#d8ddd9',zorder=0)
    ax.axvline(7/8,color=INK,ls=':',lw=.9)
    ax.set(xlim=(0,1.01),ylim=(-.5,3.6),yticks=range(4),yticklabels=[x[0] for x in methods],
           xlabel='Probability of the +0.05 reward law',xticks=[0,.25,.5,.75,1])
    finish(fig,dest,'pricing_mixture')


def repayment(data, dest):
    audit = read(data / 'index_repayment_v1' / 'summary.json')
    labels = ['Exact, scan avoided', 'Ambiguous bounds', 'Both use shortcuts',
              'Run overhead', 'Net saving']
    fig, ax = plt.subplots(figsize=(3.27, 2.21))
    fig.subplots_adjust(left=.37, right=.96, bottom=.20, top=.83)
    for cohort, offset, color, marker, name in (
            ('cohort', -.12, BLUE, 'o', 'Original'),
            ('fresh', .12, ORANGE, 's', 'Transfer')):
        run = audit[cohort]['joint']
        counts, groups = run['counts'], run['classes']
        deferred = groups['deferred-scan']['gross'] - (
            counts['storage'] + counts['refinement'] + counts['live_retirement'])
        overhead = -(counts['comparisons'] + counts['setup']
                     + counts['disposal'] - counts['live_retirement'])
        terms = [groups['collapsed-scan']['gross'], deferred,
                 groups['bulk-independent']['gross'] + groups['bulk-stationary']['gross'],
                 overhead]
        assert sum(terms) == counts['saving']
        for i, charge in enumerate(terms + [sum(terms)]):
            x = 100 * charge / run['full']
            ax.plot([0, x], [i + offset] * 2, color=color, lw=1)
            ax.plot(x, i + offset, marker, color=color, ms=4, label=name if i == 0 else None)
    ax.axvline(0, color=GREY, lw=.7)
    ax.axhline(3.5, color='#BCC3C8', lw=.6)
    ax.set(yticks=range(len(labels)), yticklabels=labels, ylim=(4.5, -.5),
           xlim=(-1.16, 3.05), xticks=[-1, 0, 1, 2, 3], xlabel='Saving (% of full-pricing work)')
    ax.tick_params(axis='y', labelsize=7.2, pad=2)
    ax.legend(loc='lower center', bbox_to_anchor=(.5, .98), ncol=2, frameon=False,
              fontsize=7.5, handlelength=1, columnspacing=1)
    finish(fig, dest, 'pricing_repayment')


def three_graphs(data, dest):
    rows = read(data / 'immediate_pricing_v1' / 'summary.json')['graphs']
    labels = ['Sharp, constant', 'Sharp, Bernoulli', 'Shoulder, constant', 'Shoulder, Bernoulli']
    fig, ax = plt.subplots(figsize=(3.27, 2.21))
    fig.subplots_adjust(left=.36, right=.96, top=.82, bottom=.25)
    for i, graph in enumerate(f'fresh-{i}' for i in range(4)):
        work = {r['method']:r['actual_work'] for r in rows if r['graph']==graph}
        for method, offset, color, marker, label in (
                ('reference', -.13, BLUE, 'o', 'vs full'), ('immediate', .13, ORANGE, 's', 'vs immediate')):
            x = 100*(1-work['threshold']/work[method])
            ax.plot([0,x], [i+offset]*2, lw=1, color=color)
            ax.plot(x,i+offset,marker,ms=4,color=color,label=label if i==0 else None)
    ax.axvline(0,color=GREY,lw=.7)
    ax.set(yticks=range(4),yticklabels=labels,ylim=(3.5,-.5),xlabel='Work saved by deferral (%)')
    ax.tick_params(axis='y',labelsize=7.1,pad=2)
    ax.legend(loc='lower center',bbox_to_anchor=(.45,1.01),ncol=2,frameon=False,
              fontsize=7.5,handlelength=1,columnspacing=1)
    finish(fig,dest,'pricing_three_graphs')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--data',type=Path,default=ROOT/'results')
    ap.add_argument('--out',type=Path,default=ROOT/'paper/certificates/figures')
    args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    plt.rcParams.update({'font.size':8,'axes.titlesize':8.5,'axes.titleweight':'bold',
                         'axes.titlepad':6,'axes.spines.top':False,'axes.spines.right':False,
                         'axes.spines.left':False,'axes.edgecolor':'#A9B2B8','axes.labelcolor':INK,
                         'text.color':INK,'xtick.color':INK,'ytick.color':INK,'ytick.major.size':0,
                         'xtick.major.size':2,'pdf.fonttype':42,'font.family':'DejaVu Sans'})
    for plot in (witness,incidence,batching,mixture_weights,noise_replication,prefix_selectors,repayment,three_graphs):
        plot(args.data,args.out)


def noise_replication(data,dest):
    z=read(data/'decision_price_v1/holdout_summary.json')['True']
    methods=[('Threshold','threshold',BLUE),('Bare','bare',GREY),
             ('Credit post','credit',ORANGE),('Credit all','credit-all','#754768')]
    fig,ax=plt.subplots(figsize=(3.27,2.18))
    fig.subplots_adjust(left=.29,right=.96,bottom=.27,top=.92)
    ax.axvline(0,color=INK,lw=.8,ls='--')
    for i,(name,m,c) in enumerate(methods):
        y=3-i
        lo,hi=z[m]['ci']
        ax.hlines(y,lo/1000,hi/1000,color=c,lw=1.6)
        ax.scatter(z[m]['mean_gap']/1000,y,color=c,s=22,zorder=3)
    ax.set(xlim=(-750,600),ylim=(-.55,3.55),xticks=[-600,-300,0,300,600],
           yticks=range(4),yticklabels=[v[0] for v in methods][::-1],
           xlabel='Alternative − full work (thousands)')
    finish(fig,dest,'pricing_noise')


def prefix_selectors(data,dest):
    summary=read(data/'prefix_routing_v1/summary.json')
    fixed=('reference','threshold','bare','credit','credit-all')
    fig,ax=plt.subplots(figsize=(3.27,2.55))
    fig.subplots_adjust(left=.40,right=.97,bottom=.23,top=.86)
    labels=[]
    for i,(tag,noise) in enumerate((t,n) for t in ('selected','transfer')
                                   for n in ('constant','mixed','bernoulli')):
        z=summary[tag+'_'+noise]['methods']
        best=min(z[m]['mean_loss'] for m in fixed)
        labels.append(('Original' if tag=='selected' else 'Transfer')+' · '+
                      {'constant':'fixed','mixed':'1%','bernoulli':'Bern.'}[noise])
        for m,dy,marker,col in [('interval',.12,'o',BLUE),('online',-.12,'s',ORANGE)]:
            ax.scatter(100*(z[m]['mean_loss']/best-1),5-i+dy,marker=marker,color=col,s=20,zorder=3)
    ax.axvline(0,color=GREY,lw=1,ls='--')
    ax.axhline(2.5,color='#D3D9DD',lw=.7)
    ax.set(yticks=range(6),yticklabels=labels[::-1],ylim=(-.5,5.5),
           xlabel='Work vs. best fixed rule (%)')
    handles=[Line2D([],[],marker=m,color=c,linestyle='none',label=s) for s,c,m in
             [('Known ranges',BLUE,'o'),('Online',ORANGE,'s')]]
    ax.legend(handles=handles,loc='lower center',bbox_to_anchor=(.35,.99),
              ncol=2,frameon=False,handletextpad=.2,columnspacing=.6)
    finish(fig,dest,'pricing_prefix')


if __name__=='__main__':
    main()
