"""Witness-first CAB: a small exact MAX quotient and one guarded compilation.

No backend racing, reverse-heap probation, or periodic mode switches. A
monotone lower-update stack certifies unchanged local lower maxima without
enumerating ancestors or compiling terminal-support closures.
"""
from bisect import bisect_right

from .certificate_batch import CertificateBatch


class _CompileRequired(Exception):
    pass


class WitnessCAB:
    def __init__(self,graph,work,scale=1,compress=True,credit=32,guard_stride=32):
        if scale<1 or credit<1 or guard_stride<1:raise ValueError('Invalid configuration')
        self.graph,self.work,self.scale=graph,work,scale
        self.ids=[-1]*len(graph);self.children=[];self.leaf_nodes=[]
        self.lower=[];self.upper=[];self.low_witness=[];self.high_witness=[]
        self.stamp=[];pool={};self.groups=[None]*len(graph)
        self.epoch=0;self.global_lower=0;self.times=[];self.values=[]
        self.query_epoch=[-1]*len(graph);self.query_cache=[None]*len(graph)
        self.initial_cost=work.total
        self.size=len(graph)+sum(map(len,graph.children))+1
        work.initialization+=4*len(graph)+30
        for v in reversed(graph.order):
            row=graph.children[v]
            if not row:
                i=len(self.children);self.children.append(())
                self.leaf_nodes.append(v);self.ids[v]=i
                self.lower.append(0);self.upper.append(scale)
                self.low_witness.append(i);self.high_witness.append(i);self.stamp.append(0)
                work.initialization+=9
                self.groups[v]=()
                continue
            positions={}
            for a,c in enumerate(row):
                q=self.ids[c]
                if q in positions:
                    first,_=positions[q];positions[q]=(first,True)
                else:positions[q]=(a,False)
                work.query_reads+=3;work.statistic_writes+=2
            distinct=tuple(positions)
            key=frozenset(distinct) if compress else None
            work.query_reads+=4*len(distinct)+2
            if compress and len(distinct)==1:i=distinct[0]
            elif compress and key in pool:i=pool[key]
            else:
                i=len(self.children);self.children.append(distinct);self.leaf_nodes.append(-1)
                self.lower.append(0);self.upper.append(scale);self.stamp.append(0)
                first=distinct[0]
                self.low_witness.append(self.low_witness[first]);self.high_witness.append(self.high_witness[first])
                if compress:pool[key]=i
                work.initialization+=9+len(distinct)
            self.ids[v]=i
            self.groups[v]=tuple((q,a,multiple) for q,(a,multiple) in positions.items())
            work.initialization+=3*len(positions)+1
        self.compiled_nodes=len(self.children)
        self.parents=[[] for _ in self.children]
        for parent,row in enumerate(self.children):
            for child in row:self.parents[child].append(parent)
        self.dirty=[False]*self.compiled_nodes;self.dirty_nodes=[]
        self.lower_synced_epoch=0;self.lower_serial=0
        self.lower_seen=[0]*self.compiled_nodes
        self.lower_repairs=self.lower_messages=self.lower_repair_work=0
        work.initialization+=4*self.compiled_nodes+2*sum(map(len,self.children))+6
        self.group_entries=sum(map(len,self.groups));self.stack_peak=0
        self.credit=credit;self.guard_stride=guard_stride
        self.startup_credit=64
        self.fuel=self.startup_credit*self.size;self.floor_allowance=0;self.front_work=0
        self.probes=self.cert_hits=self.cert_attempts=self.expansions=0
        self.controller_work=self.restore_work=self.switches=self.guard_aborts=0
        self.fallback=None;self.mode='witness';self.initial_cost=work.total-self.initial_cost

    def publish(self,leaf,lo,hi):
        if self.graph.children[leaf]:raise ValueError('Only terminal evidence is accepted')
        self.floor_allowance+=1;self.fuel+=self.credit
        i=self.ids[leaf];old=self.lower[i];top=self.upper[i]
        self.work.query_reads+=4
        if (lo,hi)==(old,top):return
        if not old<=lo<=hi<=top:raise ValueError('Nested nonempty endpoints required')
        self.lower[i],self.upper[i]=lo,hi;self.epoch+=1
        self.work.statistic_writes+=3
        if lo>old:
            while self.values and self.values[-1]<=lo:
                self.values.pop();self.times.pop()
                self.work.query_reads+=1;self.work.statistic_writes+=2
            self.values.append(lo);self.times.append(self.epoch)
            self.global_lower=max(self.global_lower,lo)
            self._dirty(i)
            self.stack_peak=max(self.stack_peak,len(self.times))
            self.work.query_reads+=2;self.work.statistic_writes+=5

    def _guard(self):
        self.probes+=1;self.work.query_reads+=1;self.controller_work+=1
        if self.probes%self.guard_stride==0:
            self.work.query_reads+=2;self.controller_work+=2
            if self.work.total>self.limit:raise _CompileRequired()

    def _certificate(self,v):
        self.cert_attempts+=1;self.work.query_reads+=4
        hi=self.upper[v]
        if self.upper[self.high_witness[v]]!=hi:return False
        self.work.query_reads+=1
        if self.lower_synced_epoch==self.epoch:
            self.stamp[v]=self.epoch;self.work.statistic_writes+=1
            self.cert_hits+=1;return True
        witness=self.low_witness[v]
        self.work.query_reads+=2
        if self.lower[witness]==self.global_lower:
            if self.lower[v]<self.global_lower:
                self.lower[v]=self.global_lower;self._dirty(v)
            self.work.query_reads+=1;self.work.statistic_writes+=1
        else:
            index=bisect_right(self.times,self.stamp[v])
            # Charge the binary-search comparison upper bound, including C code.
            self.work.query_reads+=len(self.times).bit_length()+2
            if index<len(self.times) and self.values[index]>self.lower[v]:
                self._repair_lower()
        self.stamp[v]=self.epoch;self.work.statistic_writes+=1
        self.cert_hits+=1
        return True

    def _dirty(self,v):
        self.work.query_reads+=1
        if not self.dirty[v]:
            self.dirty[v]=True;self.dirty_nodes.append(v)
            self.work.statistic_writes+=2

    def _repair_lower(self):
        """Propagate pending maxima in decreasing seed order, once per node.

        Every raised cache is also a seed: a certificate must not hide a
        propagation obligation behind an already increased intermediate node.
        Sorting is admitted before execution, with a charged comparison bound.
        """
        before=self.work.total;n=len(self.dirty_nodes)
        sort_cost=n*(n.bit_length()+4)+4
        self.work.query_reads+=2
        if self.work.total+sort_cost>self.limit:raise _CompileRequired()
        seeds=sorted(self.dirty_nodes,key=self.lower.__getitem__,reverse=True)
        self.work.query_reads+=sort_cost
        self.dirty_nodes=[];self.lower_serial+=1;self.lower_repairs+=1
        serial=self.lower_serial
        for v in seeds:self.dirty[v]=False
        for seed in seeds:
            stack=[seed]
            while stack:
                v=stack.pop();self._guard();self.work.query_reads+=2
                if self.lower_seen[v]==serial:continue
                self.lower_seen[v]=serial;self.work.statistic_writes+=1
                value=self.lower[v]
                for parent in self.parents[v]:
                    self.lower_messages+=1
                    self.work.edge_reads+=1;self.work.query_reads+=2
                    if self.lower[parent]<value:
                        self.lower[parent]=value;self.low_witness[parent]=self.low_witness[v]
                        stack.append(parent);self.work.statistic_writes+=3
        self.lower_synced_epoch=self.epoch;self.work.statistic_writes+=1
        self.lower_repair_work+=self.work.total-before

    def _finish(self,v):
        row=self.children[v]
        low=max(row,key=self.lower.__getitem__);high=max(row,key=self.upper.__getitem__)
        if self.lower[v]<self.lower[low]:self._dirty(v)
        self.work.query_reads+=1
        self.lower[v]=self.lower[low];self.upper[v]=self.upper[high]
        self.low_witness[v]=self.low_witness[low];self.high_witness[v]=self.high_witness[high]
        self.stamp[v]=self.epoch
        self.work.query_reads+=2*len(row)+4;self.work.statistic_writes+=5

    def interval(self,v):
        self._guard();self.work.query_reads+=2
        if not self.children[v] or self.stamp[v]==self.epoch:return self.lower[v],self.upper[v]
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

    def _front_query(self,node):
        groups=self.groups[node]
        if not groups:
            q=self.ids[node];self.work.query_reads+=3
            return (-1,0.,self.lower[q]/self.scale,self.upper[q]/self.scale)
        pairs=[self.interval(q) for q,_,_ in groups]
        leader=max(range(len(groups)),key=lambda i:pairs[i][0])
        lower=pairs[leader][0];upper=max(u for _,u in pairs)
        rival=max((u for i,(_,u) in enumerate(pairs) if i!=leader or groups[i][2]),default=lower)
        self.work.query_reads+=4*len(groups)+4
        return (groups[leader][1],max(0.,(rival-lower)/self.scale),lower/self.scale,upper/self.scale)

    def _compile(self):
        before=self.work.total
        self.fallback=CertificateBatch(self.graph,self.work,self.scale)
        for leaf in self.graph.leaves:
            q=self.ids[leaf];self.work.query_reads+=3
            self.fallback.publish(leaf,self.lower[q],self.upper[q])
        self.fallback._flush()
        self.restore_work=self.work.total-before;self.switches=1;self.mode='cab'
        # The settled backend has no per-call controller wrapper from now on.
        self.publish=self.fallback.publish;self.query=self.fallback.query
        self.work.statistic_writes+=4

    def query(self,node=None):
        node=self.graph.root if node is None else node
        self.work.query_reads+=2
        if self.query_epoch[node]==self.epoch:
            self.floor_allowance+=1;self.fuel+=self.credit
            self.work.query_reads+=1;self.controller_work+=1
            return self.query_cache[node]
        allowance=1+len(self.graph.children[node]);self.floor_allowance+=allowance
        self.fuel+=self.credit*allowance
        before=self.work.total;self.limit=before+self.fuel
        self.work.query_reads+=3;self.controller_work+=3
        try:
            answer=self._front_query(node)
            self.query_cache[node],self.query_epoch[node]=answer,self.epoch
            self.work.statistic_writes+=3
            if self.work.total>self.limit:raise _CompileRequired()
        except _CompileRequired:
            self.guard_aborts+=1;spent=self.work.total-before
            self.fuel-=spent;self.front_work+=spent
            self._compile()
            return self.fallback.query(node)
        spent=self.work.total-before;self.fuel-=spent;self.front_work+=spent
        return answer

    def synchronize(self):
        if self.fallback is not None:self.fallback._flush()

