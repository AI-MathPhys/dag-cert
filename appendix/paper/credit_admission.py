"""Additional control: use earned scan credit for admission as well as continuation."""
from unittest.mock import patch
import json
import random

from paper.decision_price import BareCompact, ENGINES
from paper.partial_clearing import PartialTrial
from paper.decision_price_benchmark import (DEST, ROOT, config, factory, population, solve, digest)
from paper.decision_price_family import setup,execute


class CreditAtAdmission(BareCompact):
    def try_launch(self):
        idx = self.idx
        self.next_probe *= 2
        credit = idx.stats['fallback_work']
        self.account.extra += 6
        scan_price = 68*len(self.g.leaves)+96
        if (self.point[2]<=self.tol or len(idx.top.inside[self.point[0]])<8 or
                self.pilot_cost+scan_price>credit//8):
            return
        self.w.score_evaluations+=scan_price
        self.pilot_cost+=scan_price
        self.meta['scans']+=1
        p=self.plan()
        if p is None:
            return
        budget=2*credit
        if budget<self.setup_bound+self.draw_bound+48:
            return
        if p.partial_estimate>min(budget,p.earnings):
            self.meta['rejects']+=1
            return
        self.budget=budget
        self.campaign_start=self.w.total
        self.meta.update(launch=1,start_N=self.N,range_credit=credit,estimate=p.partial_estimate,
                         full_estimate=p.full_estimate,earnings=p.earnings,budget=budget,
                         deferred=len(p.deferred),parks=0,salvage=0)
        self.trial=PartialTrial(self,p)
        assert self.spent<=self.setup_bound


def run():
    blocks=[]
    rng=random.Random(357693)
    for o in population():
        order=['reference','credit-all']
        rng.shuffle(order)
        blocks.append((o,0,order))
        if o['reps']==2:blocks.append((o,1,order[::-1]))
    rng.shuffle(blocks)
    path=DEST/'credit_pairs.jsonl'
    with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}),path.open('x') as file:
        for i,(obj,rep,order) in enumerate(blocks,1):
            s=obj['s']
            make,c=factory(s),config(s)
            for pos,m in enumerate(order):
                row=solve(make,c,obj['tie'],m)
                row.update(case=obj['case'],tag=obj['tag'],method=m,repeat=rep,position=pos)
                file.write(json.dumps(row)+'\n')
                file.flush()
            if i%40==0:print(i,'credit pairs',flush=True)
        fam=json.loads((DEST/'family.json').read_text())['selected']
        local=[]
        if fam:
            p,c=setup(fam['seed'],fam['size'],fam['shift'],fam['inverse'])
            local=[execute(p,c,t,'credit-all') for t in fam['ties']]
    (DEST/'credit_complete.json').write_text(json.dumps(dict(sha256=digest(path),rows=2*len(blocks),
                   family=local,source=digest(ROOT/'paper/credit_admission.py')),indent=2))


if __name__=='__main__':
    from paper.credit_admission import run as package_run
    package_run()
