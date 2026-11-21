"""Separate finite construction search; outcomes never enter the frozen cohorts."""
import json
from dataclasses import replace
from paper.decision_price_benchmark import (DEST, DecisionLane, factory, config, BUDGET, DRAWS,
                                           endpoint, audit_action, status)


def setup(seed,size,shift,inverse):
    spec=dict(family='layout4',A=4,M=size,seed=seed,good=2,eps=1/inverse,
              law='constant',profile='sharp')
    p=factory(spec)()
    p=replace(p,means={i:(v+shift if v<.3 else v) for i,v in p.means.items()})
    return p,config(spec)


def execute(p,cfg,seed,method,until=None):
    lane=DecisionLane(p,cfg,seed,method)
    e=lane.engine
    while not lane.point[1] and not lane.conflict and lane.work<BUDGET and lane.draws<DRAWS:
        if until is not None and (e.ended or (e.idx.q>until and e.trial is None)):
            break
        lane.advance(DRAWS-lane.draws)
    if until is not None:
        m=dict(e.meta)
        lane.retire(p,cfg)
        return m
    row=endpoint(lane,p,cfg)
    row['status']=status(row,lane.conflict,0)
    audit_action(p,row,cfg)
    return dict(work=row['work'],status=row['status'],regret=row['regret'],draws=row['draws'],
                seal=row['meta']['seal'],start=row['meta']['start_N'])


def search():
    # Screen early-launch differences; validate the first robust result on a
    # finite uniform tie law. Work/draw caps only: wall time is not an oracle.
    search_ties=list(range(356801,356809))
    attempts=[]
    candidates=[]
    found=None
    for seed in (352101,356001,356002,356003):
        for size in (224,208,192,232,200,216,180,240):
            for shift in (.025,.05,.075,.10,0.,-.025):
                p,c=setup(seed,size,shift,80)
                ref=execute(p,c,seed,'reference',512)
                if not ref['seal']: continue
                bare=execute(p,c,seed,'bare',512)
                attempts.append([seed,size,shift,ref['start_N'],bare['start_N']])
                if bare['start_N'] is not None and bare['start_N']<=ref['start_N']:continue
                ms=('reference','bare','credit','threshold')
                first={m:execute(p,c,seed,m) for m in ms}
                if any(v['status']!='certified' for v in first.values()):continue
                if first['threshold']['work']>=min(first[m]['work'] for m in ('bare','credit')):continue
                pop=[{m:execute(p,c,t,m) for m in ms} for t in search_ties]
                cand=dict(seed=seed,size=size,shift=shift,inverse=80,first=first,ties=search_ties,runs=pop)
                candidates.append(cand)
                if all(v['status']=='certified' for r in pop for v in r.values()):
                    means={m:sum(r[m]['work'] for r in pop)/len(pop) for m in ms}
                    if max(means['reference'],means['threshold'])<min(means['bare'],means['credit']):
                        found=cand
                        break
            if found:break
        if found:break
    out=dict(screened_with_reference_seal=attempts,candidates=candidates,selected=found)
    (DEST/'family.json').write_text(json.dumps(out,indent=2))
    print('family',len(attempts),len(candidates),None if found is None else
          (found['seed'],found['size'],found['shift']),flush=True)


if __name__=='__main__':
    search()
