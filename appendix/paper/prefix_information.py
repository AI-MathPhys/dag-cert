"""Exact finite public-prefix acquisition costs for the overlapping-law race."""
import json
import math
from fractions import Fraction as F
from math import comb
from paper.prefix_routing_benchmark import DEST


def race(h=32):
    low,high=F(9,100),F(11,100)
    gain=100/low-1000
    loss=1000-100/high
    def posterior(n,k):
        a=low**k*(1-low)**(n-k)
        b=high**k*(1-high)**(n-k)
        return a/(a+b)
    minimum=min(gain,loss)/2
    binomial=sum(comb(h,k)*min(gain*low**k*(1-low)**(h-k),
                              loss*high**k*(1-high)**(h-k))/2 for k in range(h+1))
    def raw(q):
        future={}
        for n in range(h,-1,-1):
            now={}
            for k in range(n+1):
                rho=posterior(n,k)
                risk=min(rho*gain,(1-rho)*loss)
                if n<h:
                    p=rho*low+(1-rho)*high
                    risk=min(risk,q+p*future[k+1]+(1-p)*future[k])
                now[k]=risk
            future=now
        return future[0]
    exact={str(q):str(raw(q)) for q in (F(0),F(1,100),F(1,10),F(1))}
    assert F(exact['0'])==binomial and F(exact['1'])==minimum
    kl=float(low)*math.log(float(low/high))+float(1-low)*math.log(float((1-low)/(1-high)))
    threshold=max(k for k in range(h+1) if posterior(h,k)*gain>=(1-posterior(h,k))*loss)
    return dict(h=h,rates=[float(low),float(high)],G=str(gain),L=str(loss),count_cut=threshold,
                constant=str(minimum),free_count=str(binomial),gross_count_value=float(minimum-binomial),
                raw_risk={q:float(F(x)) for q,x in exact.items()},raw_exact=exact,kl=kl,
                pinsker_lower=float(minimum)*(1-math.sqrt(h*kl/2)))


if __name__=='__main__':
    out=race()
    (DEST/'race.json').write_text(json.dumps(out,indent=2))
    print({k:v for k,v in out.items() if k not in ('raw_exact','free_count')})
