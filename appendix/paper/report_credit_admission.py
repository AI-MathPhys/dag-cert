"""Credit-at-admission control with its contemporaneous reference."""
import json
from collections import defaultdict
from statistics import median
from paper.decision_price_benchmark import DEST,population,digest,SECONDS


def report():
    stamp=json.loads((DEST/'credit_complete.json').read_text())
    file=DEST/'credit_pairs.jsonl'
    rows=[json.loads(l) for l in file.read_text().splitlines()]
    assert len(rows)==stamp['rows'] and digest(file)==stamp['sha256']
    pairs=defaultdict(lambda:defaultdict(list))
    for r in rows:pairs[r['case']][r['method']].append(r)
    groups=defaultdict(list)
    for o in population():
        group=pairs[o['case']]
        assert set(group)=={'reference','credit-all'}
        assert all(len(rr)==o['reps'] for rr in group.values())
        groups[o['tag']].append(group)
    summary={}
    for tag,gs in groups.items():
        wins=losses=joint=seals=launches=done=0
        time_ratios=[]
        totals=[0,0]
        restricted=[0,0]
        for g in gs:
            ref,new=g['reference'],g['credit-all']
            seals+=new[0]['meta']['seal']
            launches+=new[0]['meta']['launch']
            done+=all(r['status']=='certified' for r in new)
            for j,rr in enumerate((ref,new)):
                restricted[j]+=sum(r['seconds'] if r['status']=='certified' else SECONDS for r in rr)/len(rr)
                totals[j]+=sum(r['work'] for r in rr)/len(rr)
            if all(r['status']=='certified' for rr in (ref,new) for r in rr):
                joint+=1
                wins+=new[0]['work']<ref[0]['work']
                losses+=new[0]['work']>ref[0]['work']
                time_ratios.append(median(r['seconds'] for r in new)/median(r['seconds'] for r in ref))
        summary[tag]=dict(inputs=len(gs),completed=done,joint=joint,work=totals[1]/len(gs),
                          ratio=totals[1]/totals[0],seals=seals,launches=launches,wins=wins,losses=losses,
                          restricted_time_ratio=restricted[1]/restricted[0],median_time_ratio=median(time_ratios))
    (DEST/'credit_summary.json').write_text(json.dumps(summary,indent=2))
    print(summary)


if __name__=='__main__':
    report()
