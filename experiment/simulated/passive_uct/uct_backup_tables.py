"""Generate the per-case LaTeX tables from the archived summaries and audits."""
import csv
import json
from statistics import mean
from experiment.simulated.passive_uct.uct_backup_benchmark import ROOT,DEST,METHODS,CASES
from experiment.simulated.passive_uct.uct_backup_gap import DEST as GAP_DIR,GAPS

PAPER=ROOT/'paper/certificates'
NAMES={'two-exit':'Two exits','funnel':'One exit','live-best':'Winning fanout',
       'fixed-gap':'Fixed gap','noisy':'Noisy','core':'Common core','merge':'Merge','lattice':'Lattice'}


def read(path):
    with path.open(newline='') as fp:
        return list(csv.DictReader(fp))


def table(filename,legend,label,fmt,heading,body,small=r'\small'):
    source = '\n'.join((r'\begin{table}[t]',r'\centering'+small,r'\setlength{\tabcolsep}{3pt}',
                       r'\caption{'+legend+'}',r'\label{'+label+'}',
                       r'\begin{tabular}{'+fmt+r'}\toprule',heading+r'\\\midrule',*body,
                       r'\bottomrule\end{tabular}',r'\end{table}'))
    (PAPER/filename).write_text(source+'\n')


def run():
    times=read(DEST/'certification.csv')
    regrets=read(DEST/'wall_regret.csv')
    aud=[json.loads(l) for l in (DEST/'coupled.jsonl').read_text().splitlines()]
    certrows,regrows=[],[]
    for f,n in CASES:
        group={r['method']:r for r in times if (r['family'],int(r['size']))==(f,n)}
        g=[r for r in aud if (r['family'],r['size'])==(f,n)]
        horizon=round(mean(r['steps'] for r in g)) if all(r['certified'] for r in g) else '--'
        counts='/'.join(group[m]['completed'] for m in METHODS)
        certrows.append(' & '.join([NAMES[f],str(n),str(horizon),
                   *[f"{float(group[m]['rmst_ms']):.1f}" for m in METHODS],counts])+r'\\')
        regrows.append(' & '.join([NAMES[f],str(n),*[f"{float(next(r['mean_regret'] for r in regrets if (r['family'],int(r['size']),r['method'],int(r['milliseconds']))==(f,n,m,t))):.3f}" for t in (1,10,100) for m in METHODS]])+r'\\')
    table('uct_backup_cert_table.tex','Primary cohort. Restricted mean certification time in ms, with all nonreturns scored at 2,000 ms. $N$ is the mean audited first certificate rollout where the common trajectory reached it. Returns are counts out of 16 per backend, in column order.','tab:ta-cert','lr r rrrr c',r'Family & Size & $N$ & Eager & Selective & Flat & Covers & Returns',certrows)
    header=(r'Family & Size & \multicolumn{4}{c}{1 ms} & \multicolumn{4}{c}{10 ms} & \multicolumn{4}{c}{100 ms}\\'
            +' & & '+' & '.join(['E','S','F','C']*3))
    table('uct_backup_regret_table.tex',r'Mean anytime simple regret at equal wall deadlines. E, S, F and C denote edge-eager, selective, flat and covers. Values are rounded to three decimals. All 500-ms and 2,000-ms means were exactly zero.','tab:ta-regret','lr '+'r'*12,header,regrows,r'\small')
    gtimes=read(GAP_DIR/'certification.csv')
    gaud=[json.loads(l) for l in (GAP_DIR/'coupled.jsonl').read_text().splitlines()]
    grows=[]
    for gap in GAPS:
        s=[r for r in gaud if r['size']==gap]
        rm={r['method']:float(r['rmst_ms']) for r in gtimes if int(r['size'])==gap}
        avg=lambda k:mean(r[k] for r in s)
        cuts=[r['cone_cut'] for r in s if r['cone_cut'] is not None]
        work=mean(r['work']['eager'] for r in s)/mean(r['work']['live'] for r in s)
        grows.append(' & '.join([f'{gap/1000:.3f}',f"{avg('steps'):.0f}",str(round(mean(cuts))) if cuts else '--',
                    f"{avg('later_cone_visits'):.0f}",f"{avg('later_eager_messages'):.0f}",f'{work:.3f}',
                    *[f'{rm[m]:.1f}' for m in METHODS]])+r'\\')
    table('uct_backup_gap_table.tex',r'Follow-up at width 256 and $\epsilon=.025$. Post-cut visits and messages are from the actual UCT trace. Work ratio is eager divided by selective through certification; times are mean ms including retirement.','tab:ta-gap','r'*10,r'Gap & Rolls & Cut & Revisits & Deliveries & Work ratio & Eager & Selective & Flat & Covers',grows)


if __name__=='__main__':run()
