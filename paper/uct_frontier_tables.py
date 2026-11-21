"""Tables include capped runs and native/elevated observation costs."""
import csv
import json
from pathlib import Path
from statistics import mean
from paper.uct_frontier_study import DEST,ROOT,CASES,METHODS

def run():
    rows=list(csv.DictReader((DEST/'summary.csv').open()))
    target=ROOT/'paper/certificates'
    s=[r'\begin{center}\small',r'\begin{tabular}{llrrrr}',r'\toprule',
       r'Case & Observation surcharge & Graph eager & Graph selective & Compiled selective & Covers \\',
       r'\midrule']
    names={'coded':'Coded','dense':'Dense','sparse':'Sparse','samegame':'SameGame','lattice':'Lattice','funnel':'Funnel'}
    for f,n in CASES:
        for effort in (0,512):
            vals=[]
            for m in METHODS:
                r=next(r for r in rows if (r['family'],int(r['size']),int(r['effort']),r['method'])==(f,n,effort,m))
                vals.append(f"{float(r['restricted_ms']):.1f} ({r['completed']}/8)")
            s.append(f"{names[f]} {n} & {effort} & "+' & '.join(vals)+r' \\')
    s.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
    (target/'uct_frontier_time_table.tex').write_text('\n'.join(s)+'\n')
    memory=DEST/'memory.jsonl'
    if memory.exists():
        ms=[json.loads(l) for l in memory.read_text().splitlines()]
        s=[r'\begin{center}\small',r'\begin{tabular}{lrrrr}',r'\toprule',
           r'Case & Graph eager & Graph selective & Compiled selective & Covers \\',r'\midrule']
        for f,n in CASES:
            vals=[mean(r['peak_bytes']/1048576 for r in ms if (r['family'],r['size'],r['method'])==(f,n,m)) for m in METHODS]
            s.append(f"{names[f]} {n} & "+' & '.join(f'{v:.3f}' for v in vals)+r' \\')
        s.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
        (target/'uct_frontier_memory_table.tex').write_text('\n'.join(s)+'\n')

if __name__=='__main__':run()

