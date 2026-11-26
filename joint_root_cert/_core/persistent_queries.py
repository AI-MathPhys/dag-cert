"""Complete repeated best-action service with globally shared evidence.

Candidate construction is paid. Successful answers persist under nested
intervals. Every control gets the same answer cache; only maintenance differs.
Uses existing truth-watch and exact-query kernels, not a new watching primitive.
"""
from collections import deque
from .demand_threshold import DemandThreshold
from .local_buckets import LocalBuckets, LazyLocalHeap
from .batched_witness_cab import FastQuotientRange
from .demand_bounds import EagerQueries


class LowerCandidates:
    def __init__(self,graph,work):
        self.graph,self.work=graph,work
        self.lower=[0]*len(graph)
        self.leader=[0 if r else -1 for r in graph.children]
        self.parents=[[] for _ in graph.children]
        for v,row in enumerate(graph.children):
            for a,c in enumerate(row):self.parents[c].append((v,a))
        self.pending={}
        work.initialization+=3*len(graph)+2*sum(map(len,graph.children))
        self.messages=0

    def publish(self,leaf,lo):
        self.work.query_reads+=1
        if lo>self.lower[leaf]:
            self.lower[leaf]=lo;self.pending[leaf]=lo
            self.work.statistic_writes+=2

    def flush(self):
        queue=deque(self.pending);queued=set(queue)
        self.work.statistic_writes+=2*len(queue);self.pending.clear()
        while queue:
            c=queue.popleft();queued.remove(c);self.work.statistic_writes+=2
            for v,a in self.parents[c]:
                self.messages+=1;self.work.edge_reads+=1;self.work.query_reads+=3
                new,old=self.lower[c],self.lower[v]
                if new>old or (new==old and a<self.leader[v]):
                    self.lower[v],self.leader[v]=new,a;self.work.statistic_writes+=2
                    if new>old and v not in queued:
                        queue.append(v);queued.add(v);self.work.statistic_writes+=2


class PersistentQueries:
    METHODS=('truth','direct','bucket','lazy','qrange','eager')
    def __init__(self,graph,work,method='truth',scale=40,tolerance=8):
        if method not in self.METHODS or not 2<tolerance<scale:
            raise ValueError('Invalid service parameters')
        self.graph,self.work,self.method,self.scale,self.tolerance=graph,work,method,scale,tolerance
        self.answers={};self.hits=self.requests=0
        work.initialization+=6
        if method in ('truth','direct'):
            self.lower=LowerCandidates(graph,work)
            self.backend=DemandThreshold(graph,work,scale,'watch' if method=='truth' else 'direct')
        else:
            factory={'bucket':LocalBuckets,'lazy':LazyLocalHeap,'qrange':FastQuotientRange,'eager':EagerQueries}[method]
            self.backend=factory(graph,work,scale)

    def publish(self,leaf,lo,hi):
        self.backend.publish(leaf,lo,hi)
        if self.method in ('truth','direct'):self.lower.publish(leaf,lo)

    def query(self,node):
        self.requests+=1;self.work.query_reads+=2
        if node in self.answers:
            self.hits+=1
            return self.answers[node]
        row=self.graph.children[node]
        if self.method in ('truth','direct'):
            self.lower.flush()
            a=self.lower.leader[node]
            lo=self.lower.lower[node]
            ok=True
            for b,c in enumerate(row):
                self.work.edge_reads+=1
                if b!=a and self.backend.has_high(c,lo+self.tolerance+1):
                    ok=False;break
        else:
            a,gap,_,_=self.backend.query(node)
            ok=gap<=self.tolerance/self.scale
        result=(a,ok)
        if ok:
            self.answers[node]=result;self.work.statistic_writes+=1
        return result

    def final_sweep(self):
        """Identical final decision requests; cached valid answers remain legal.

        Do not force exact-value queries on one control when the actual service
        only requests an epsilon-good decision. Every requested repair is paid.
        """
        return [(v,self.query(v)) for v,row in enumerate(self.graph.children) if row]
