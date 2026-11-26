"""Per-case time-to-certification and equal-wall root regret, with caps retained."""
import csv
import json
from statistics import mean,median
from experiment.simulated.passive_uct.uct_backup_benchmark import DEST,ROOT,CASES,SEEDS,METHODS,WALL,digest


def write_csv(path,records):
    with path.open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=records[0])
        writer.writeheader()
        writer.writerows(records)


def report(dest=DEST,cases=CASES,seeds=SEEDS):
    manifest=json.loads((dest/'manifest.json').read_text())
    complete=json.loads((dest/'complete.json').read_text())
    assert complete['runs']==digest(dest/'runs.jsonl')
    assert all(digest(ROOT/s)==v for s,v in manifest['sources'].items())
    rows=[json.loads(l) for l in (dest/'runs.jsonl').read_text().splitlines()]
    assert len(rows)==complete['rows']==2*len(cases)*len(seeds)*len(METHODS)
    times,regrets,pairs=[],[],[]
    for family,size in cases:
        case=[r for r in rows if (r['family'],r['size'])==(family,size)]
        by_method={}
        for method in METHODS:
            group=[r for r in case if r['method']==method]
            assert len(group)==2*len(seeds)
            good=[r for r in group if r['returned']]
            row=dict(family=family,size=size,method=method,completed=len(good),runs=len(group),
                     rmst_ms=1000*mean(r['restricted'] for r in group),
                     certified_ms=1000*mean(r['end_seconds'] for r in good) if good else None,
                     init_ms=1000*mean(r['init_seconds'] for r in group),
                     retire_ms=1000*mean(r['retire_seconds'] for r in group),
                     mean_first_step=mean(r['cert_at_step'] for r in good) if good else None,
                     mean_cert_work=mean(r['work'] for r in good) if good else None,
                     alarms=sum(r['conflict'] for r in group))
            times.append(row)
            by_method[method]=row
            for i,wall in enumerate(WALL):
                regrets.append(dict(family=family,size=size,method=method,milliseconds=round(1000*wall),
                    mean_regret=mean(r['regrets'][i] for r in group),
                    worst_regret=max(r['regrets'][i] for r in group),
                    mean_rollouts=mean(r['checkpoints'][i][1] for r in group),
                    no_rollout=sum(r['checkpoints'][i][1]==0 for r in group),
                    certified=sum(r['checkpoints'][i][2] for r in group),runs=len(group)))
        for method in ('eager','flat','covers'):
            # Ratio of restricted means and paired seed differences answer different questions.
            diffs=[]
            for seed in seeds:
                pair=[r for r in case if r['seed']==seed]
                values={m:mean(r['restricted'] for r in pair if r['method']==m) for m in (method,'live')}
                diffs.append(1000*(values[method]-values['live']))
            pairs.append(dict(family=family,size=size,baseline=method,
                rmst_ratio=by_method[method]['rmst_ms']/by_method['live']['rmst_ms'],
                paired_median_ms=median(diffs),positive_seeds=sum(x>0 for x in diffs),
                negative_seeds=sum(x<0 for x in diffs)))
        print(family,size,*[(m,round(by_method[m]['rmst_ms'],1),by_method[m]['completed']) for m in METHODS])
    write_csv(dest/'certification.csv',times)
    write_csv(dest/'wall_regret.csv',regrets)
    write_csv(dest/'paired.csv',pairs)


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--gap',action='store_true')
    if parser.parse_args().gap:
        from experiment.simulated.passive_uct.uct_backup_gap import DEST as GAP_DIR,GAPS,SEEDS as GAP_SEEDS
        report(GAP_DIR,[('gap-test',g) for g in GAPS],GAP_SEEDS)
    else:
        report()
