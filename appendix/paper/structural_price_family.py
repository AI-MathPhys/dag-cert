"""Verify the mask-independent constants of the complementary-pair corollary."""
import json
import math

from paper.structural_price_benchmark import DEST
from paper.uniform_price_proof import Leaf


def complementary_pairs(m):
    assert m in (176,192)
    h, eps, k = 8, 1/80, 80**4
    log_ratio = math.log(m/.01)
    hot = [Leaf(v,k,log_ratio) for v in (.70,.684375)]
    cold = [Leaf(.01+.02*i/(m-1),k,log_ratio) for i in range(1,m-1)]
    upper = [c.at(1)[1] for c in cold]
    assert all(a<b for a,b in zip(upper,upper[1:]))
    assert all(c.at(1)[0]==0 and c.at(1)[1]<(.684375-1e-7)*k for c in cold)
    nstar = min(len(c.at(1)[3][1]) for c in cold)
    warm = [next(b for b in range(1,32) if c.at(b)[1]<k) for c in hot]
    initial = m-2+sum(warm)
    paired = math.ceil((m//2-1+min(warm))/2)
    sweep = initial-paired
    fee = 32*m+8
    scan = 68*m+96
    def credit(q):
        result = fee
        for t in range(q):
            hi = min(m,max(0,initial-t-min(t,paired)))
            writes = max(min(2*m-y,y+8) for y in range(max(0,m-2*t),hi+1))
            result += 3*m+1+writes
        return result
    lost = [0,0]
    debt = 0
    for j,c in enumerate(hot):
        for b in range(1,513):
            for side,changes in enumerate(c.at(b)[3]):
                n = len(changes)
                assert b<=warm[j] or n==16
                lost[side] += 16-n
                if n>=4:
                    debt += max(0,32+4*h-4*n)
    clipping = []
    for q in (256,512):
        t = q-1
        hot_draws = 16*(2*t-m+2)
        nu = (m-2)*nstar+max(0,hot_draws-lost[1])
        nl = max(0,hot_draws-lost[0])
        clipping.append(36*32*t+12*(nu+h*nl+(h-1)*32*(t-sweep))-5*credit(q))
    def radius(b):
        n = 16*b
        return math.sqrt((n+1)/(2*n*n)*(log_ratio+.5*math.log1p(n)))
    t = 511
    eta = 1e-7+2/k
    theta_lo = .70-radius(t-sweep+warm[0])-eta
    theta_hi = .70-radius(t)+eta
    assert theta_lo>max(max(upper)/k,.03+eps+eta)
    assert min(1,.684375+radius(t)-eta)>theta_hi+eps
    useful = sum(v-1e-7>=theta_hi-eps for v in (.70,.684375))
    nprec = math.ceil(2*(log_ratio+.5*math.log1p(1/eps**2))/eps**2)
    misses = 512-sum(warm)
    cmin = (3*m+1)*misses
    member = 16+2*(m//2).bit_length()
    earnings = useful*(nprec-16*t)/32*misses/512*max(0,4*m-6*member)
    # 2000 bounds one private draw plus 48 under the stated tariff.
    setup = 104*m+152
    upper_cost = setup+max(2*nprec*member/32,2000)
    gamma = min(4*nstar-29-h,7*nstar-32-4*h)
    margin = (m-6)*gamma-debt-156
    assert min(8*scan-credit(128),*clipping,cmin-16*scan,
               min(2*cmin,earnings)-upper_cost,margin)>0
    return dict(M=m,sweep=sweep,early=8*scan-credit(128),clipping=clipping,
                funding=cmin-16*scan,forecast=min(2*cmin,earnings)-upper_cost,
                nstar=nstar,hot_debt=debt,bound=margin)


if __name__=='__main__':
    stats = [complementary_pairs(m) for m in (176,192)]
    (DEST/'complementary_pairs.json').write_text(json.dumps(stats,indent=2))
    print(stats)
