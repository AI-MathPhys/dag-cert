"""Paid threshold-clearing sampling and permanent decision frontiers.

Threshold classification changes observations; shared evidence and the
anytime confidence event are unchanged. No confidence in the pilot forecast
is required for correctness. Failed campaigns return to ordinary LUCB.
"""
from dataclasses import dataclass
from functools import cmp_to_key
import random

from dag_mcts.certified_uct import UCTWork
from paper.relevance_frontier import Index
from paper.sampling_confidence_allcount import MixtureIntervals
from paper.uniform_selection import CountTree

METHODS=('range_lucb4','range_lucb32','frontier_lucb4','range_clear','frontier_clear',
         'range_clear32','frontier_clear32')


@dataclass
class Work(UCTWork):
    observation_overhead: int = 0

    @property
    def total(self): return super().total+self.observation_overhead


class PermanentIndex(Index):
    def __init__(self,g,w,scale,seed,enabled,cap=12):
        super().__init__(g,w,scale,'range_memo',seed,cap)
        self.enabled=enabled;self.stats['frontier_terminal_answers']=0

    def install(self,core,theta):
        start=self.w.total
        self.w.statistic_writes+=len(self.F or [])+len(core)+2
        self.F=list(core);self.threshold=theta;self.stats['builds']+=1
        self.stats['frontier_size']=len(core);self.stats['peak_frontier']=max(self.stats['peak_frontier'],len(core))
        self.stats['service_work']+=self.w.total-start

    def decision_frontier(self,a,lo):
        w=self.w;start=w.total;out=[[],[]];best=[-1,-1]
        if lo<self.threshold:raise AssertionError('lost monotone lower anchor')
        for j in self.F:
            side=int(self.top.contains(a,j,w));key=self.upper[j]
            w.query_reads+=1;w.heap_comparisons+=2
            if key>best[side]:w.statistic_writes+=len(out[side]);out[side]=[];best[side]=key
            if key==best[side]:out[side].append(self.ut.size+j);w.statistic_writes+=1
        if best[1]<self.threshold:raise AssertionError('anchor not in complete frontier')
        w.heap_comparisons+=2
        self.stats['certificate_work']+=w.total-start
        return out,best[0]<self.threshold

    def query(self):
        self.q+=1;a,lo=self.candidate();w=self.w;start=w.total
        saved=self.memo.get(a);w.query_reads+=2
        bounded=False
        if saved is not None and saved[0]==self.revision:
            nodes=saved[1];self.stats['memo_hits']+=1
        else:
            if self.enabled and self.F is not None:
                nodes,bounded=self.decision_frontier(a,lo);self.stats['hits']+=1
            else:
                before=w.total;nodes=self.ranged(a);self.stats['fallback_work']+=w.total-before
                self.stats['misses']+=1
            if not bounded:
                if saved is not None:w.statistic_writes+=sum(map(len,saved[1]))
                self.memo[a]=(self.revision,nodes);w.statistic_writes+=3
        x=self.ut.select(nodes[1],self.rng)
        if bounded:
            # The omitted maximum is below theta <= global lower. This is
            # a valid terminal decision, not a claimed exact outside witness.
            y=(self.threshold,None);self.stats['frontier_terminal_answers']+=1
        else:y=self.ut.select(nodes[0],self.rng)
        self.witnesses=(x[1],y[1]);w.statistic_writes+=2
        self.stats['service_work']+=w.total-start
        return a,lo,x,y


class Search:
    def __init__(self,p,c,seed,method):
        if method not in METHODS:raise ValueError(method)
        self.g=p.graph;self.c=c;self.method=method;self.w=Work();w=self.w
        w.initialization+=16*len(self.g)+10*sum(map(len,self.g.children))+4*len(self.g.leaves)
        self.idx=PermanentIndex(self.g,w,c['K'],seed,method.startswith('frontier'),c.get('cap',12))
        self.ev=MixtureIntervals(self.g,w,c['delta'],c['K']);self.oracle=p.oracle(seed)
        self.N=0;self.tol=round(c['epsilon']*c['K'])
        if c['K']*c['epsilon']<=2 or abs(self.tol-c['epsilon']*c['K'])>1e-9:raise ValueError('grid tolerance')
        self.clear_enabled='_clear' in method;self.pilot_at=4 if method.endswith('clear32') else 32;self.probe_at=1
        self.attempted=False;self.mask=None;self.pending=None;self.core=[];self.theta=None
        self.clear_rng=random.Random(seed+111901);self.clear_limit=c.get('clear_multiplier',64)*len(self.g.leaves)
        self.controller=dict(pilots=0,launched=0,success=0,abort_dense=0,abort_budget=0,
                             stopped_during_clear=0,extra_observations=0,controller_work=0,
                             pilot_work=0,mask_work=0,start_N=None,end_N=None,threshold=None,
                             final_core=0,retired=0)
        w.initialization+=25

    def observe(self,j,clearing=False):
        leaf=self.g.leaves[j];v=leaf;w=self.w
        while v!=self.g.root:
            v=self.idx.top.parent[v];w.edge_reads+=1;w.query_reads+=1
        reward=self.oracle.sample(leaf);self.N+=1
        interval=self.ev.observe(leaf,reward)
        w.observation_overhead+=self.c.get('oracle_cost',1)-1
        if self.ev.conflict:raise ArithmeticError('empty confidence interval')
        if interval is not None:self.idx.publish(j,*interval)
        if clearing:self.controller['extra_observations']+=1
        return j,reward,interval

    def cleanup(self,reason):
        if self.mask is None:return
        start=self.w.total
        self.w.statistic_writes+=len(self.mask.value)+len(self.mask.count)+len(self.core)+5
        self.mask=None;self.pending=None;self.core=[]
        self.controller[reason]+=1;self.controller['end_N']=self.N
        self.controller['controller_work']+=self.w.total-start

    def finish_clear(self):
        w=self.w;start=w.total
        def cmp(a,b):w.heap_comparisons+=1;return (b>a)-(b<a)
        core=sorted(self.core,key=cmp_to_key(cmp));w.statistic_writes+=len(core)
        self.controller['final_core']=len(core)
        self.controller['retired']=len(self.idx.upper)-len(core)
        self.controller['controller_work']+=w.total-start
        if self.idx.enabled:self.idx.install(core,self.theta)
        self.cleanup('success')
        self.w.statistic_writes+=len(core)
        self.controller['controller_work']+=len(core)

    def pilot(self):
        # Forecast admission only. Neither empirical labels nor its forecast
        # are used as confidence certificates.
        if not self.clear_enabled or self.attempted or self.idx.q<self.pilot_at:return
        w=self.w;start=w.total;self.pilot_at*=2;self.controller['pilots']+=1;w.statistic_writes+=2
        a,_,lo,_,_=self.point;w.query_reads+=3
        if lo<=self.tol or len(self.idx.top.inside[a])<8:
            self.controller['pilot_work']+=w.total-start;self.controller['controller_work']+=w.total-start;return
        threshold=lo/self.c['K'];estimated=0;unseen=False
        for leaf in self.g.leaves:
            n=self.ev.counts[leaf];w.query_reads+=2;w.heap_comparisons+=2
            if not n:unseen=True;break
            mean=self.ev.sums[leaf]/n;w.score_evaluations+=1
            if mean>=threshold-self.c['epsilon']:estimated+=1;w.statistic_writes+=1
        passed=not unseen and estimated<=self.idx.cap
        w.heap_comparisons+=2
        self.controller['pilot_work']+=w.total-start;self.controller['controller_work']+=w.total-start
        if not passed:return
        self.attempted=True;self.theta=lo;self.controller['launched']+=1
        self.controller['threshold']=lo/self.c['K'];self.controller['start_N']=self.N
        start=w.total;values=[];self.core=[]
        for j,(low,high) in enumerate(zip(self.idx.lower,self.idx.upper)):
            w.query_reads+=2;w.heap_comparisons+=2
            if low>=lo:self.core.append(j);values.append(-1)
            elif high<lo:values.append(-1)
            else:values.append(high)
            w.statistic_writes+=2
        self.mask=CountTree(values,w);w.statistic_writes+=len(values)+5
        self.controller['mask_work']+=w.total-start;self.controller['controller_work']+=w.total-start
        if len(self.core)>self.idx.cap:self.cleanup('abort_dense')
        elif self.mask.value[1]<self.theta:self.finish_clear()

    def query(self):
        a,lo,x,y=self.idx.query();w=self.w;w.query_reads+=2;w.heap_comparisons+=1
        good=y[1] is None or y[0]<=lo+self.tol
        self.pair=(x[1],y[1]);self.point=(a,good,lo,x,y)
        if good:self.cleanup('stopped_during_clear')
        elif self.method=='frontier_lucb4' and self.idx.F is None and self.idx.q>=self.probe_at:
            before=w.total
            if lo>0:self.idx.build(lo)
            self.probe_at*=2;w.statistic_writes+=1
            self.idx.stats['service_work']+=w.total-before
        return self.point

    def clear_step(self,limit):
        w=self.w;obs=[]
        for _ in range(min(32,limit)):
            before=w.total
            if self.pending is None:
                if self.mask.value[1]<self.theta:
                    self.finish_clear();break
                _,self.pending=self.mask.select([1],self.clear_rng);w.statistic_writes+=1
            self.controller['controller_work']+=w.total-before
            j=self.pending;obs.append(self.observe(j,clearing=True))
            before=w.total;w.query_reads+=2;w.heap_comparisons+=2
            if self.idx.lower[j]>=self.theta or self.idx.upper[j]<self.theta:
                if self.idx.lower[j]>=self.theta:self.core.append(j);w.statistic_writes+=1
                self.mask.update(j,-1);self.pending=None;w.statistic_writes+=1
            self.controller['controller_work']+=w.total-before
            before=w.total;w.query_reads+=3;w.heap_comparisons+=3
            self.controller['controller_work']+=w.total-before
            if len(self.core)>self.idx.cap:self.cleanup('abort_dense');break
            if self.mask.value[1]<self.theta:self.finish_clear();break
            if self.controller['extra_observations']>=self.clear_limit:self.cleanup('abort_budget');break
        return obs

    def step(self,remaining):
        self.pilot()
        if self.mask is not None:obs=self.clear_step(remaining)
        else:
            cadence=32 if self.method.endswith('32') else 4
            pair=self.pair;obs=[self.observe(pair[k%2]) for k in range(min(cadence,remaining))]
        self.w.statistic_writes+=len(obs)
        return obs,self.query()
