"""Compact with direct frontier detection; one persistent or fixed candidate."""
import random
from dag_mcts.certified_uct import UCTWork
from paper.compact_partial import FastPartial, FastRange, PairedKernel, CompactFrontier
from paper.frontier_sampling import Work
from paper.relevance_frontier import Compiled
from paper.sampling_confidence_allcount import MixtureIntervals
from paper.uniform_selection import CountTree

class OwnerFrontier(CompactFrontier):
    """Pay once per frontier anchor for the same rejection and fallback choices."""
    def __init__(self,idx):
        super().__init__(idx)
        self.owners={}
    def candidate(self,anchor):
        idx=self.idx
        total=len(idx.top.inside)
        idx.w.query_reads+=1
        if anchor not in self.owners:
            bits=tuple(idx.top.contains(a,anchor,idx.w) for a in range(total))
            self.owners[anchor]=bits,[a for a,bit in enumerate(bits) if bit]
            idx.w.statistic_writes+=4*total+4
        bits,owners=self.owners[anchor]
        for _ in range(16):
            a=idx.rng.randrange(total)
            idx.w.score_evaluations+=1;idx.w.query_reads+=1
            if bits[a]:return a
        idx.w.score_evaluations+=1
        return owners[idx.rng.randrange(len(owners))]

class DirectCompact(FastPartial):
    def step(self,remaining):
        idx=self.idx
        self.w.query_reads+=2
        if idx.F is None and idx.q>=self.next_probe:
            self.next_probe*=2
            theta=self.point[2]
            self.meta['scans']+=1
            self.w.statistic_writes+=2
            if theta>0:
                members=[]
                for j in reversed(range(len(idx.upper))):
                    self.w.query_reads+=1;self.w.heap_comparisons+=1
                    if idx.upper[j]>=theta:
                        members.append(j);self.w.statistic_writes+=2
                        if len(members)>idx.cap:break
                if len(members)<=idx.cap:
                    idx.install(members,theta)
                    self.compact=OwnerFrontier(idx)
                    self.meta.update(seal=1,start_N=self.N,frontier_size=len(members))
        return self.ordinary(remaining)

class Partition:
    def __init__(self,g,w,seed,scale):
        self.top=Compiled(g,w)
        self.w=w;self.rng=random.Random(seed+791901)
        self.upper=[scale]*len(g.leaves);self.lower=[0]*len(g.leaves)
        self.best=0;self.anchor=0;self.layouts={}
        self.active=None;self.switches=0;self.q=0
        w.initialization+=2*len(g.leaves)+12
    def activate(self,a):
        if a not in self.layouts:
            groups=[[],[]];lookup=[]
            for j in range(len(self.upper)):
                side=int(self.top.contains(a,j,self.w))
                lookup.append((side,len(groups[side])))
                groups[side].append(j)
            self.layouts[a]=groups,lookup
            self.w.statistic_writes+=4*len(lookup)+4
        self.groups,self.lookup=self.layouts[a]
        self.trees=[CountTree([self.upper[j] for j in group],self.w) if group else None
                    for group in self.groups]
        self.inside_lower=max(self.lower[j] for j in self.groups[1])
        self.w.query_reads+=2*len(self.upper);self.w.heap_comparisons+=len(self.groups[1])
        self.w.statistic_writes+=3*len(self.upper)+4
        self.switches+=self.active is not None
        self.active=a
    def publish(self,j,lo,hi):
        self.w.query_reads+=5;self.w.heap_comparisons+=7
        if not self.lower[j]<=lo<=hi<=self.upper[j]:raise ValueError('non-nested')
        side,offset=self.lookup[j]
        if self.upper[j]!=hi:self.trees[side].update(offset,hi)
        self.lower[j]=lo;self.upper[j]=hi
        if lo>self.best:self.best,self.anchor=lo,j
        if side:self.inside_lower=max(self.inside_lower,lo)
        self.w.statistic_writes+=5
    def witness(self,side):
        if not self.trees[side]:return -1,None
        hi,k=self.trees[side].select([1],self.rng)
        self.w.query_reads+=1
        return hi,self.groups[side][k]

class Persistent(PairedKernel):
    def __init__(self,p,c,seed,fixed=False):
        self.g=p.graph;self.c=c;self.w=Work();self.N=0;self.fixed=fixed
        self.w.initialization+=16*len(self.g)+10*sum(map(len,self.g.children))+4*len(self.g.leaves)
        self.idx=Partition(self.g,self.w,seed,c['K'])
        self.ev=MixtureIntervals(self.g,self.w,c['delta'],c['K'])
        self.oracle=p.oracle(seed);self.tol=round(c['epsilon']*c['K'])
        if c['epsilon']*c['K']<=2 or abs(self.tol-c['epsilon']*c['K'])>1e-9:raise ValueError('grid tolerance')
        self.abstain=False
        self.idx.activate(self.idx.rng.randrange(len(self.idx.top.inside)))
    def query(self):
        i=self.idx;i.q+=1
        if not self.fixed and i.best>i.trees[1].value[1]:
            owners=[a for a in range(len(i.top.inside)) if i.top.contains(a,i.anchor,self.w)]
            self.w.statistic_writes+=len(owners);self.w.score_evaluations+=1
            i.activate(owners[i.rng.randrange(len(owners))])
        x,y=i.witness(1),i.witness(0)
        self.w.query_reads+=5;self.w.heap_comparisons+=4
        good=y[1] is None or y[0]<=i.inside_lower+self.tol
        self.abstain=self.fixed and not good and i.best>x[0]+self.tol
        self.pair=x[1],y[1]
        self.point=i.active,good,i.inside_lower,x,y
        return self.point
    def step(self,remaining):
        return self.ordinary(remaining)

def create(p,c,seed,method):
    if method=='range':return FastRange(p,c,seed)
    if method=='compact':return FastPartial(p,c,seed)
    if method=='direct':return DirectCompact(p,c,seed)
    if method in ('fixed','persistent'):return Persistent(p,c,seed,fixed=method=='fixed')
    raise ValueError(method)

