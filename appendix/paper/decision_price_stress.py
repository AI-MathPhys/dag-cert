"""Bounded search for premature admission by the more permissive credit rule."""
from dataclasses import replace
from fractions import Fraction
from unittest.mock import patch
import json

from paper.credit_admission import CreditAtAdmission, ENGINES, factory, config, DEST, execute, setup


def problem(s):
    p=factory(s)()
    return replace(p,means={k:v+s['shift'] if v<.3 else v for k,v in p.means.items()}), config(s)


def run():
    fam=json.loads((DEST/'family.json').read_text())['selected']
    extra=json.loads((DEST/'credit_complete.json').read_text())['family']
    left=[dict(r,**{'credit-all':v}) for r,v in zip(fam['runs'],extra,strict=True)]
    methods=tuple(left[0])
    screened=[]
    candidates=[]
    found=None
    with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}):
        for seed in (356021,356022):
            for a in (8,4,16):
                for size in (96,128,160,192,224,256):
                    for shift in (0,.05,-.04,.09):
                        spec=dict(family='layout'+str(a),seed=seed,M=size,A=a,good=2,eps=1/80,
                                  profile='sharp',law='constant',shift=shift)
                        p,c=problem(spec)
                        rd=execute(p,c,seed,'reference',512)
                        cd=execute(p,c,seed,'credit-all',512)
                        screened.append([seed,a,size,shift,rd['start_N'],cd['start_N'],rd['seal'],cd['seal']])
                        if cd['start_N'] is None or (rd['start_N']==cd['start_N'] and rd['seal']==cd['seal']):
                            continue
                        base={m:execute(p,c,seed,m) for m in ('reference','credit-all')}
                        if any(v['status']!='certified' for v in base.values()):continue
                        if base['credit-all']['work']<=base['reference']['work']:continue
                        ts=list(range(356901,356909))
                        pop=[{m:execute(p,c,t,m) for m in methods} for t in ts]
                        candidates.append(dict(spec=spec,ties=ts,runs=pop))
                        if not all(v['status']=='certified' for r in pop for v in r.values()):continue
                        for k in range(17):
                            # Explicit rational mixture weight on the positive-admission graph.
                            sums={m:k*sum(r[m]['work'] for r in left)+(16-k)*sum(r[m]['work'] for r in pop) for m in methods}
                            if sums['reference']<min(sums[m] for m in methods if m!='reference'):
                                found=dict(right=candidates[-1],left_weight=k,denominator=16,sums=sums)
                                break
                        if found:break
                    if found:break
                if found:break
            if found:break
    (DEST/'stress.json').write_text(json.dumps(dict(screened=screened,candidates=candidates,selected=found)))
    print('extended search',len(screened),'candidates',len(candidates),'strict mixture',bool(found),flush=True)


if __name__=='__main__':
    run()
