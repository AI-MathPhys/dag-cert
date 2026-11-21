"""Tie-independent bounds on the signed uncapped work in the archived fragmented graphs."""
import json
import math
from collections import Counter

from paper.immediate_pricing import ImmediateCompact
from paper.decision_price_benchmark import config, factory

SLACK = 1.e-7   # exceeds deterministic summation error on the finite completion horizon


def originals():
    for size,seed in ((224,355001),(192,378001),(224,378002),(224,378003),(256,378004),(224,355003)):
        yield dict(name=str(seed),family='layout4',M=size,A=4,good=2,law='constant',
                   profile='shoulder' if seed==355003 else 'sharp',seed=seed,eps=1/80,cohort='original-sign')


class Supply:
    def __init__(self,s):
        self.s=s
        p=factory(s)()
        cfg=config(s)
        self.e=ImmediateCompact(p,cfg,1)
        self.K,self.eps=cfg['K'],cfg['epsilon']
        self.M=len(p.graph.leaves)
        self.h=(self.M-1).bit_length()
        self.mu=[p.means[x] for x in p.graph.leaves]
        self.W,self.R=sorted(range(self.M),key=self.mu.__getitem__,reverse=True)[:2]
        self.owners=[frozenset(a for a,children in enumerate(p.graph.children[1:5]) if x in children)
                     for x in p.graph.leaves]
        assert self.owners[self.W].isdisjoint(self.owners[self.R])
        self.ks=[]
        self.cover_fee=0
        for a in range(4):
            before=self.e.w.total
            self.ks.append(sum(map(len,self.e.idx.cover(a))))
            self.cover_fee+=self.e.w.total-before   # includes cover lookup; safe upper bound
        self.slack=SLACK+2/self.K
        self.log=math.log(self.M/cfg['delta'])

    def radius(self,b):
        n=16*b
        return math.sqrt((n+1)/(2*n*n)*(self.log+.5*math.log1p(n))) if n else math.inf

    def quota(self,j,v,limit):
        """Upper bound on consecutive local blocks starting at a key >= v, truncated at limit."""
        lo,hi=0,limit
        while lo<hi:
            k=(lo+hi)//2
            if self.mu[j]+self.radius(k)+self.slack>=v:
                lo=k+1
            else:
                hi=k
        return lo

    def minvis(self,j,t):
        """One witness per block on the side containing j has priority at least j's end key."""
        peers=[i for i in range(self.M) if i!=j and self.owners[i]&self.owners[j]]
        lo,hi=0,t
        while lo<hi:
            b=(lo+hi)//2
            key=min(1.,self.mu[j]+self.radius(b)-self.slack)
            if b+sum(self.quota(i,key,t) for i in peers)>=t: hi=b
            else: lo=b+1
        return lo

    def max_credit(self,q):
        return (5*max(self.ks)+1)*q+self.cover_fee

    def sharp(self):
        h=self.h
        cold=[i for i in range(self.M) if i not in (self.W,self.R)]
        for q in (256,512,1024,2048):
            t=q-1
            # Each side contains one prospect. Count its competitors' possible visits.
            cold_v=self.mu[self.R]-SLACK
            visits={i:self.quota(i,cold_v,t) for i in cold}
            if self.M+sum(self.quota(i,1.,t) for i in (self.W,self.R))>t:continue
            nw=self.minvis(self.W,t)
            low=self.mu[self.W]-self.radius(nw)-self.slack
            high=self.mu[self.W]-self.radius(t)+self.slack
            if low<=max(self.mu[i] for i in cold)+self.eps+SLACK:continue
            # At the probe both hot lower-key candidates have zero forecast at the
            # anchor itself for at least one of them (regardless of which is larger).
            hot_keys=[self.mu[j]+self.radius(t)-self.slack for j in (self.W,self.R)]
            if min(hot_keys)-high<=self.eps:continue  # need a common completed campaign
            z=sum(self.quota(i,1.,t) for i in (self.W,self.R))
            # Every upper declines strictly per block after leaving saturation, at
            # least through q. The derivative bound below uses monotone radii and
            # an explicit check of adjacent blocks at the least favorable spacing.
            assert all(self.radius(b)-self.radius(b+1)>2*self.slack for b in range(1,q))
            cmin=(3*min(self.ks)+1)*(q-z)
            scan=68*self.M+96
            scans=0
            for k in range(2,q.bit_length()-1):
                if self.max_credit(2**k)>=8*(scans+1)*scan:scans+=1
            if cmin<8*(scans+1)*scan:continue
            precision=math.ceil(2*(self.log+.5*math.log1p(1/self.eps**2))/self.eps**2)
            membership=max(16+2*len(side).bit_length() for side in self.e.idx.top.inside)
            hold=2*precision/32*membership
            estimate=self.e.setup_bound+hold+78*sum(max(1,math.ceil((self.log+.5*math.log1p(max(32,16*visits[i])))/
                        (2*max(low-self.mu[i]-SLACK-1/self.K,self.eps/4)**2))-16) for i in cold)
            earnings=sum(v-SLACK>=high-self.eps for v in self.mu)*max(0,precision-16*t)/32*((q-z)/q)*(
                       4*min(self.ks)-6*membership)
            allowance=min(2*cmin,(36*32*t+cmin)//3)
            if max(estimate,self.e.setup_bound+self.e.draw_bound+48)>allowance or estimate>earnings:continue
            # Before normal closure there are <=4t records. A refinement cancels
            # its own scan, so only storage, the 12-unit refinement fee and its
            # 8-unit recheck can be lost per record. The private loop can run at
            # most 1+n/32 steps with n draws, each paying >=36 before the next draw.
            records=4*t
            extra_checks=2*q.bit_length()+3+(1+2/32)*(2*self.max_credit(q)/36+1)
            neg=math.ceil(records*(32+48+4*h+20)+8*extra_checks+60+64)
            pos=records*(80-h)+64
            return dict(Q=q,negative_bound=neg,positive_bound=pos,cmin=cmin,
                        allowance=allowance,estimate=estimate,earnings=earnings,theta_min=low)
        raise AssertionError('could not bound the launch horizon')

    def shoulder(self):
        # If no trial has started by this checkpoint, fix the monotone anchor.
        # Each later unresolved block must use an outside upper witness above anchor+epsilon.
        t=8192
        mins=[self.minvis(i,t) for i in range(self.M)]
        lo=max(self.mu[i]-self.radius(b)-self.slack for i,b in enumerate(mins))
        assert lo>self.mu[self.R]+SLACK
        # Only the two winning candidates are now possible; terminals with the
        # same owners as the winner can never be outside. Ensure no quota is clipped.
        left=0
        for i in range(self.M):
            if self.owners[i]==self.owners[self.W]:continue
            n=self.quota(i,lo+self.eps-2/self.K,1<<18)
            assert n<1<<18
            left+=max(0,n-mins[i])
        limit=t+left+1
        # The last possible launch and retirement both have <= limit public blocks.
        # A live record only increases the disposal bill; extra fixed fields differ by <=64.
        return dict(stop_or_launch_by=limit,theta_min=lo,positive_bound=4*limit*(80-self.h)+64)


def bounds(s):
    model=Supply(s)
    return model.sharp() if s['profile']=='sharp' else model.shoulder()


if __name__=='__main__':
    print(json.dumps({s['name']:bounds(s) for s in originals()},indent=2))
