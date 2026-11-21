"""Conditional lower bound on the policy bill at a future probe after the public sweep."""
import math
from paper.neighbor_price_condition import HotCurve
from paper.structural_price_condition import check, run_fee
from paper.immediate_pricing import ImmediateCompact


class SweepBound:
    """Offline analysis of the given graph. No diagnostic feeds back into Compact."""
    def __init__(self, graph, cfg, probes=(256,512)):
        self.cfg = cfg
        self.z = check(graph,cfg,probes[0])
        self.probes = probes
        leaves = graph.graph.leaves
        self.m = len(leaves)
        self.w,self.r = sorted(range(self.m),key=lambda j:graph.means[leaves[j]],reverse=True)[:2]
        assert self.w^self.r==1 and self.z['height']<=8
        engine = ImmediateCompact(graph,cfg,1)
        ordered = [graph.means[leaves[j]] for j in (self.w,self.r)]
        self.curves = [HotCurve(v,cfg['K'],engine.ev.log_ratio,max(probes)) for v in ordered]
        self.fees = []
        for action in range(4):
            runs = engine.idx.top.inside[action]+engine.idx.top.outside[action]
            self.fees.append(2+sum(run_fee(x,y,engine.idx.ut.size) for x,y in runs))
        self.memo = {}

    def suffix(self,a,b,blocks):
        cache_key = a,b,blocks
        if cache_key not in self.memo:
            h,k,l = self.z['height'],self.z['kmax'],self.z['lis']
            w,r = self.curves
            total = 0
            for i in range(1,blocks+1):
                x,y=a+i,b+i
                assert min(w.count[0][x],r.count[0][y],w.count[1][x],r.count[1][y])==16
                dominant = (w.leader(0,x,r.lower[y])+r.leader(0,y,w.lower[x])+
                            w.leader(1,x,r.upper[y-1])+r.leader(1,y,w.upper[x-1]))
                total += (36*32+17*32+16*32+23+4*h-5*(3*k+1)-10*l+12*(h-1)*dominant)
            self.memo[cache_key] = total
        return self.memo[cache_key]

    def project(self,engine):
        t = engine.idx.q-1
        cfg,idx = self.cfg,engine.idx
        assert idx.ut.value[1]<cfg['K'] and t<self.probes[0]-1
        leaves=engine.g.leaves
        a,b=(engine.ev.counts[leaves[j]]//16 for j in (self.w,self.r))
        assert a+b==2*t-self.m+2
        credit=idx.stats['fallback_work']
        slack=engine.w.total-engine.monitor_cost-engine.pilot_cost-24-6*credit
        # Winner lists evicted during the suffix cover all appended winners
        # except the final four lists. The initial lists can only help.
        unpaid=sum(fee for j,fee in enumerate(self.fees) if j not in idx.covers)
        forecast=[slack-5*unpaid-4*self.m+self.suffix(a,b,q-1-t) for q in self.probes]
        return dict(sweep=t,visits=[a,b],prefix_slack=slack,unbuilt_fee=unpaid,forecast=forecast)

    def launch_guard(self):
        q=self.probes[-1]
        t=q-1
        z=self.z
        K,eps=self.cfg['K'],self.cfg['epsilon']
        # The stronger deferred clipping test may fail. For admission it
        # suffices that the lower budget itself pays the forecast and floor.
        cmin=(3*z['kmin']+1)*(q-sum(c.warm for c in self.curves))
        m=z['M']
        nprec=math.ceil(2*(math.log(m/self.cfg['delta'])+.5*math.log1p(1/eps**2))/eps**2)
        membership=max(16+2*b.bit_length() for b in z['max_intervals'])
        setup=104*m+152
        estimate=setup+max(2*nprec*membership/32,1+2*(m+5)+16*z['height']+176)
        # Use the unconditional join-one bound at the last probe.
        lower_allowance=min(2*cmin,(6*cmin+z['clip'][-1])//3)
        return min(lower_allowance-estimate,z['forecast'])

    def loss_bound(self):
        # At most one trial ending by normal closure; unlaunched by the
        # second probe is impossible under the verified guard.
        q=self.probes[-1]
        assert self.z['early']>0 and self.z['funding']>=0 and self.z['pre_return']>0
        assert self.z['cold_clear']>0 and min(self.z['min_intervals'])>=8 and self.launch_guard()>=0
        max_credit=self.z['cover_fee']+(5*self.z['kmax']+1)*q
        max_draws=math.ceil(2*max_credit/36)+1
        groups=4*(q-1)
        # One hard-budget check per attempted draw, plus progress/parking
        # checks per 32-draw call. An empty/terminal call is allowed.
        tests=max_draws+3*(math.ceil(max_draws/32)+2)+6
        return groups*(32+48+4*self.z['height']+12+8)+8*tests+60+64

