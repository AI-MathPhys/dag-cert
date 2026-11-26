"""W-CAB2: coalesced publication history and a shared fused decision adapter.

Canonical terminal endpoints remain current after every publication. Temporal
history/dirty certificates are prepared once per changed terminal at the next
query. A guarded escape compiles CAB on the same quotient as Q-Range.
"""
from .witness_cab import WitnessCAB, _CompileRequired
from .quotient_range import QuotientRange
from .certificate_batch import CertificateBatch
from .graph import DAG


def fused_decision(groups,interval,work,scale,terminal=None):
    """One traversal; preserve original IDs, multiplicity and upper ties."""
    if not groups:
        lo,hi=interval(terminal);work.query_reads+=2
        return -1,0.,lo/scale,hi/scale
    best=top=second=-1;leader=top_id=-1;action=-1;multiple=False
    for i,(q,a,duplicate) in enumerate(groups):
        lo,hi=interval(q)
        if lo>best:best,leader,action,multiple=lo,i,a,duplicate
        if hi>top:second,top,top_id=top,hi,i
        elif hi>second:second=hi
    rival=top if multiple or leader!=top_id else second
    if rival<0:rival=best
    # Keep the same assembly charge as the frozen grouped adapter; the fused
    # traversal is a runtime optimization, not an invented work-counter saving.
    work.query_reads+=4*len(groups)+4
    return action,max(0.,(rival-best)/scale),best/scale,top/scale


class FastQuotientRange(QuotientRange):
    def query(self,node=None):
        node=self.graph.root if node is None else node;epoch=self.core.epoch
        self.work.query_reads+=3
        if self.query_epoch[node]==epoch:return self.query_cache[node]
        answer=fused_decision(self.groups[node],self.core.interval,self.work,self.scale,self.ids[node])
        self.query_cache[node]=answer;self.query_epoch[node]=epoch;self.work.statistic_writes+=2
        return answer


class PreparedQuotientCAB(FastQuotientRange):
    """Paid CAB compilation on an existing quotient; no original support build."""
    def __init__(self,front):
        self.graph,self.work,self.scale=front.graph,front.work,front.scale
        self.ids,self.groups=front.ids,front.groups
        self.query_epoch=[-1]*len(self.graph);self.query_cache=[None]*len(self.graph)
        self.quotient=DAG(front.children,root=self.ids[self.graph.root])
        self.work.initialization+=2*len(self.graph)+4+16*len(front.children)+10*sum(map(len,front.children))
        self.core=CertificateBatch(self.quotient,self.work,self.scale)
        for leaf in self.graph.leaves:
            q=self.ids[leaf];self.work.query_reads+=3
            self.core.publish(q,front.lower[q],front.upper[q])
        self.core._flush()

    def synchronize(self):self.core._flush()


class BatchedWitnessCAB(WitnessCAB):
    def __init__(self,graph,work,scale=1,coalesce=True,credit=32,guard_stride=32):
        super().__init__(graph,work,scale,credit=credit,guard_stride=guard_stride)
        self.coalesce=coalesce;self.pending_inputs={}
        self.prepared_inputs=self.prepared_lowers=self.preparations=self.prepare_work=0
        work.initialization+=7;self.initial_cost+=7
        if not coalesce:self.publish=super().publish

    def publish(self,leaf,lo,hi):
        if self.graph.children[leaf]:raise ValueError('Only terminal evidence is accepted')
        self.floor_allowance+=1;self.fuel+=self.credit
        i=self.ids[leaf];old=self.lower[i];top=self.upper[i]
        self.work.query_reads+=4
        if (lo,hi)==(old,top):return
        if not old<=lo<=hi<=top:raise ValueError('Nested nonempty endpoints required')
        # No cache is read while a batch is open. One new epoch per nonempty
        # publication batch therefore invalidates precisely the same decisions.
        self.work.query_reads+=2
        if not self.pending_inputs:
            self.epoch+=1;self.work.statistic_writes+=1
        if i not in self.pending_inputs:
            self.pending_inputs[i]=old;self.work.statistic_writes+=1
        self.lower[i],self.upper[i]=lo,hi;self.work.statistic_writes+=2

    def _prepare(self):
        self.work.query_reads+=1
        if not self.pending_inputs:return
        before=self.work.total;self.preparations+=1
        for i,old in self.pending_inputs.items():
            self._guard();lo=self.lower[i]
            self.prepared_inputs+=1;self.work.query_reads+=2
            if lo>old:
                while self.values and self.values[-1]<=lo:
                    self.values.pop();self.times.pop()
                    self.work.query_reads+=1;self.work.statistic_writes+=2
                self.values.append(lo);self.times.append(self.epoch)
                self.global_lower=max(self.global_lower,lo);self._dirty(i)
                self.prepared_lowers+=1;self.stack_peak=max(self.stack_peak,len(self.times))
                self.work.query_reads+=2;self.work.statistic_writes+=5
        self.work.statistic_writes+=len(self.pending_inputs)+1
        self.pending_inputs.clear();self.prepare_work+=self.work.total-before

    def interval(self,v):
        # A fresh/terminal read needs no individual guard: the query's finite
        # group scan is checked at completion. Stale work retains node guards.
        self.work.query_reads+=2
        if not self.children[v] or self.stamp[v]==self.epoch:return self.lower[v],self.upper[v]
        self._guard()
        if self._certificate(v):return self.lower[v],self.upper[v]
        stack=[(v,False)];self.work.statistic_writes+=1
        while stack:
            q,finish=stack.pop();self._guard();self.work.query_reads+=2
            if not self.children[q] or self.stamp[q]==self.epoch:continue
            if finish:self._finish(q);continue
            if q!=v and self._certificate(q):continue
            row=self.children[q];self.expansions+=1
            stack.append((q,True));stack.extend((c,False) for c in reversed(row))
            self.work.statistic_writes+=len(row)+1;self.work.edge_reads+=len(row)
        return self.lower[v],self.upper[v]

    def _compile(self):
        before=self.work.total;self.fallback=PreparedQuotientCAB(self)
        self.restore_work=self.work.total-before;self.switches=1;self.mode='quotient_cab'
        self.publish=self.fallback.publish;self.query=self.fallback.query
        self.work.statistic_writes+=4

    def query(self,node=None):
        node=self.graph.root if node is None else node
        self.work.query_reads+=2
        if self.query_epoch[node]==self.epoch:
            self.floor_allowance+=1;self.fuel+=self.credit
            self.work.query_reads+=1;self.controller_work+=1
            return self.query_cache[node]
        allowance=1+len(self.groups[node]);self.floor_allowance+=allowance
        self.fuel+=self.credit*allowance
        before=self.work.total;self.limit=before+self.fuel
        self.work.query_reads+=3;self.controller_work+=3
        try:
            self._prepare()
            answer=fused_decision(self.groups[node],self.interval,self.work,self.scale,self.ids[node])
            self.query_cache[node],self.query_epoch[node]=answer,self.epoch
            self.work.statistic_writes+=3
            end=self.work.total
            if end>self.limit:raise _CompileRequired()
        except _CompileRequired:
            self.guard_aborts+=1;spent=self.work.total-before
            self.fuel-=spent;self.front_work+=spent
            self._compile();return self.fallback.query(node)
        spent=end-before;self.fuel-=spent;self.front_work+=spent
        return answer

    def synchronize(self):
        if self.fallback:self.fallback.synchronize()
