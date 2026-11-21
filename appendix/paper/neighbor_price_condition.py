"""History-uniform lower price when both prospects are in one index region."""
from math import log
from paper.structural_price_condition import check
from paper.uniform_price_proof import Leaf


class HotCurve:
    """Rounded extrema of each local 16-draw visit; index zero is unsampled."""
    def __init__(self, mean, grid, log_ratio, horizon):
        leaf = Leaf(mean,grid,log_ratio)
        self.lower, self.upper = [0], [grid]
        self.count = [[0],[0]]
        self.smallest = [[0],[grid]]
        for visit in range(1,horizon+1):
            lo,hi,_,events = leaf.at(visit)
            self.lower.append(lo)
            self.upper.append(hi)
            for side,keys in enumerate(events):
                self.count[side].append(len(keys))
                self.smallest[side].append(min(keys) if keys else 0)
        self.warm = next(b for b,u in enumerate(self.upper) if u<grid)

    def leader(self, side, visit, peer):
        """Revisions whose entire group reaches the root under the endpoint test."""
        if self.smallest[side][visit]>=peer:
            return self.count[side][visit]
        return 0


def dominant_revisions(curves, m, sweep, probes):
    """Worst post-sweep credit over the two possible local counts at the sweep bound."""
    w,r = curves
    total = 2*sweep-m+2
    minimum = {q:None for q in probes}
    overlap = {q:0 for q in probes}
    for a in range(max(w.warm,total-sweep),min(sweep,total-r.warm)+1):
        b = total-a
        revisions = 0
        disputed = 0
        for block in range(sweep+1,max(probes)):
            x,y = a+block-sweep,b+block-sweep
            for side,peer_w,peer_r in ((0,w.lower[x],r.lower[y]),
                                       (1,w.upper[x-1],r.upper[y-1])):
                left = w.leader(side,x,peer_r)
                right = r.leader(side,y,peer_w)
                revisions += left+right
                disputed += not (left or right)
            q = block+1
            if q in minimum:
                current = minimum[q]
                minimum[q] = revisions if current is None else min(current,revisions)
                overlap[q] = max(overlap[q],disputed)
    assert all(v is not None for v in minimum.values())
    return minimum,overlap


def predict(problem,cfg,p=256):
    base = check(problem,cfg,p)
    if base.get('join')!=1 or base.get('sign')!='abstain':
        return dict(sign=base['sign'],bound=base['bound'],old=base['sign'])
    m,h = base['M'],base['height']
    means = sorted(problem.means.values(),reverse=True)
    curves = [HotCurve(mu,cfg['K'],log(m/cfg['delta']),2*p) for mu in means[:2]]
    probes = (p,2*p)
    if probes[0]-1<base['sweep']:
        return dict(sign='abstain',bound=None,old=base['sign'])
    leaders,crossings = dominant_revisions(curves,m,base['sweep'],probes)
    added = [12*(h-1)*leaders[q] for q in probes]
    clip = [price+bonus for price,bonus in zip(base['clip'],added)]
    cold_top = Leaf(means[2],cfg['K'],log(m/cfg['delta'])).at(1)[1]/cfg['K']
    anchor_low = base['cold_clear']+cold_top
    scalar_guards = (anchor_low>max(cfg['epsilon'],means[2]+1e-7+cfg['epsilon'])
                     and means[0]+1e-7+2/cfg['K']+cfg['epsilon']<1)
    ok = (scalar_guards and min(base['min_intervals'])>=8 and base['early']>0 and min(clip)>=0
          and base['funding']>=0 and base['forecast']>=0 and base['pre_return']>0
          and base['cold_clear']>0 and base['margin']>0)
    return dict(sign='deferred' if ok else 'abstain',bound=base['margin'] if ok else None,
                old=base['sign'],base_clip=base['clip'],leaders=[leaders[q] for q in probes],
                overlap=[crossings[q] for q in probes],clip=clip)
