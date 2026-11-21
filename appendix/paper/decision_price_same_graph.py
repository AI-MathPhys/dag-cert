"""Check whether the two admission regimes coexist on identical visible topology."""
from fractions import Fraction
from unittest.mock import patch
import json
from paper.decision_price_stress import DEST, CreditAtAdmission, problem, execute, ENGINES


def mixture(a,b):
    ms=tuple(a[0])
    # Solve the strict affine inequalities exactly over the graph-law weight.
    lo,hi=Fraction(0),Fraction(1)
    for m in ms:
        if m=='reference':continue
        x=sum(r[m]['work']-r['reference']['work'] for r in a)
        y=sum(r[m]['work']-r['reference']['work'] for r in b)
        if x<=0 and y<=0:return None
        if y<=0:lo=max(lo,Fraction(-y,x-y))
        if x<=0:hi=min(hi,Fraction(y,y-x))
    return [str(lo),str(hi)] if lo<hi else None


def main():
    fam=json.loads((DEST/'family.json').read_text())['selected']
    extra=json.loads((DEST/'credit_complete.json').read_text())['family']
    left=dict(runs=[dict(r,**{'credit-all':v}) for r,v in zip(fam['runs'],extra,strict=True)],
              spec=dict(family='layout4',seed=fam['seed'],M=fam['size'],A=4,good=2,
                        eps=1/80,profile='sharp',law='constant',shift=fam['shift']),ties=fam['ties'])
    right=json.loads((DEST/'stress.json').read_text())['selected']['right']
    log=[]
    candidates=[]
    hit=None
    with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}):
        for source in (left,right):
            methods=tuple(source['runs'][0])
            for j in range(-4,25):
                s=dict(source['spec'],shift=j*.01)
                if abs(s['shift']-source['spec']['shift'])<1e-8:continue
                p,c=problem(s)
                t=source['ties'][0]
                pre={m:execute(p,c,t,m,512) for m in ('reference','credit-all','bare')}
                log.append([s,[(m,k['start_N'],k['seal']) for m,k in pre.items()]])
                if all((k['start_N'],k['seal'])==(pre['reference']['start_N'],pre['reference']['seal']) for k in pre.values()):continue
                first={m:execute(p,c,t,m) for m in methods}
                if any(k['status']!='certified' for k in first.values()):continue
                if not mixture(source['runs'],[first]*len(source['ties'])):continue
                runs=[first]+[{m:execute(p,c,t,m) for m in methods} for t in source['ties'][1:]]
                cand=dict(spec=s,ties=source['ties'],runs=runs)
                candidates.append(cand)
                if not all(x['status']=='certified' for r in runs for x in r.values()):continue
                interval=mixture(source['runs'],runs)
                if interval:
                    hit=dict(a=source,b=cand,interval=interval)
                    break
            if hit:break
    (DEST/'same_graph.json').write_text(json.dumps(dict(screened=log,candidates=candidates,selected=hit)))
    print('same topology',len(log),'candidate laws',len(candidates),'positive',bool(hit),flush=True)


if __name__=='__main__':
    main()
