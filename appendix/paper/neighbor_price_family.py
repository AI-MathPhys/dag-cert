"""All owner masks on complementary sibling pairs, using common geometry bounds."""
from math import log
from paper.neighbor_price_condition import HotCurve, dominant_revisions
from paper.structural_price_family import complementary_pairs
from paper.uniform_price_proof import Leaf


def neighbor_family(m):
    # Move the second endpoint prospect of the spread construction to rank 1,
    # keeping the interior cold means and their relative order.
    common = complementary_pairs(m)
    p, h, grid = 256, 8, 80**4
    probes = (p,2*p)
    log_ratio = log(m/.01)
    curves = [HotCurve(mu,grid,log_ratio,2*p) for mu in (.70,.684375)]
    cold = [Leaf(.01+.02*i/(m-1),grid,log_ratio) for i in range(1,m-1)]
    changes = sum(len(c.at(1)[3][1]) for c in cold)
    lost = [sum(16-n for c in curves for n in c.count[side][1:]) for side in (0,1)]
    leaders,crossings = dominant_revisions(curves,m,common['sweep'],probes)
    prices = []
    for q in probes:
        t = q-1
        hot_draws = 16*(2*t-m+2)
        nu = changes+max(0,hot_draws-lost[1])
        nl = max(0,hot_draws-lost[0])
        # Both covers together have M singleton blocks. Each of the four
        # actions costs at most 8M+2 to build both covers; LIS bound is four.
        base = (36*32*t+17*nu+16*nl+(23+4*h-5*(3*m+1)-10*4)*q
                -5*(32*m+8)-4*m)
        prices.append(base+12*(h-1)*leaders[q])
    assert min(prices)>=0 and common['bound']>0
    return dict(M=m,clips=prices,crossings=[crossings[q] for q in probes],
                leaders=[leaders[q] for q in probes],bound=common['bound'])


if __name__=='__main__':
    print([neighbor_family(m) for m in (176,192)])
