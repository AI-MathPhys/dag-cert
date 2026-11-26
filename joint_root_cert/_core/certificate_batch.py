"""Certificate-aware batching with level-coalesced deferred MAX repairs.

Certificates read canonical evidence. Cached upper witnesses are allowed to
be stale and are revalidated; their invalidation never causes reverse traffic.
Every failed certificate flushes ALL outstanding debt in level order. A cell
is visited once in that flush and only after a changed child (or terminal).
The comparison theorem concerns actual Range-batch cell visits, not its
worst-case repair envelope. Existing frozen backends remain unchanged.
"""
from .demand_bounds import DecisionQueries, MaxIndex, compile_runs


class CertificateBatch(DecisionQueries):
    def __init__(self,graph,work,scale=1,certificates=True,audit=False):
        self._query_init(graph,work,scale)
        self.mapping,self.ids,self.runs,self.merge_inputs=compile_runs(graph,work)
        self.index=MaxIndex(len(graph.leaves),scale,work)
        self.covers=[tuple(p for a,b in runs for p in self.index.cover(a,b)) for runs in self.runs]
        self.supports=len(self.runs);self.cover_entries=sum(map(len,self.covers))
        self.run_count=sum(map(len,self.runs))
        self.cache=[(0,scale)]*self.supports;self.stamp=[0]*self.supports
        self.lower=[0]*len(graph);self.upper=[scale]*len(graph)
        self.leaf_nodes=[0]*len(graph.leaves)
        for leaf,i in self.mapping.items():self.leaf_nodes[i]=leaf
        b=self.index.base
        self.witness=[-1]*(2*b)
        for i in range(len(graph.leaves)):self.witness[b+i]=i
        for p in range(b-1,0,-1):
            c=2*p if self.index.upper[2*p]>=self.index.upper[2*p+1] else 2*p+1
            self.witness[p]=self.witness[c]
        self.cache_witness=[runs[0][0] for runs in self.runs]
        self.single=[runs[0][0] if len(runs)==1 and runs[0][1]-runs[0][0]==1 else -1 for runs in self.runs]
        self.seen=[0]*(2*b);self.repair_serial=0
        self.pending={};self.pending_max_lower=0
        self.pending_min=len(graph.leaves);self.pending_max=-1
        self.global_lower=0;self.global_winner=0;self.flush_epoch=0
        self.certificates=certificates
        self.flushes=self.repair_visits=self.repair_leaves=self.repair_work=0
        self.cert_attempts=self.cert_hits=self.cert_work=self.direct_hits=self.window_hits=0
        self.peak_pending=0
        self.audit_batches=[] if audit else None
        work.initialization+=2*len(graph)+6*self.supports+len(self.covers)+len(graph.leaves)+4*b+3*(b-1)+23

    def publish(self,leaf,lo,hi):
        if self.graph.children[leaf]:raise ValueError('Only terminal evidence is accepted')
        self.work.query_reads+=3
        if (lo,hi)==(self.lower[leaf],self.upper[leaf]):return
        if not self.lower[leaf]<=lo<=hi<=self.upper[leaf]:raise ValueError('Nested nonempty endpoints required')
        self.lower[leaf],self.upper[leaf]=lo,hi;self.epoch+=1
        i=self.mapping[leaf];self.pending[i]=(lo,hi)
        self.pending_max_lower=max(self.pending_max_lower,lo)
        self.pending_min=min(self.pending_min,i);self.pending_max=max(self.pending_max,i)
        if lo>self.global_lower:self.global_lower,self.global_winner=lo,i
        self.peak_pending=max(self.peak_pending,len(self.pending))
        self.work.query_reads+=6;self.work.statistic_writes+=10

    def _contains(self,support,position):
        # Exact membership without scanning a full terminal incidence list.
        runs=self.runs[support];left,right=0,len(runs)
        while left<right:
            mid=(left+right)//2;a,b=runs[mid]
            self.work.query_reads+=3
            if position<a:right=mid
            elif position>=b:left=mid+1
            else:return True
        return False

    def _certificate(self,i):
        before=self.work.total;self.cert_attempts+=1
        lo,hi=self.cache[i];witness=self.cache_witness[i]
        runs=self.runs[i];self.work.query_reads+=5
        self.work.query_reads+=3
        if self.stamp[i]>=self.flush_epoch and (self.pending_max<runs[0][0] or self.pending_min>=runs[-1][1]):
            self.cert_work+=self.work.total-before;self.cert_hits+=1;self.window_hits+=1
            return lo,hi
        result=None
        if self.upper[self.leaf_nodes[witness]]==hi:
            # Do not forget older changes after another query flushed the index.
            self.work.query_reads+=3
            if self.stamp[i]>=self.flush_epoch and self.pending_max_lower<=lo:
                result=(lo,hi)
            elif lo==self.global_lower or self._contains(i,self.global_winner):
                result=(self.global_lower,hi)
        self.cert_work+=self.work.total-before
        if result is not None:self.cert_hits+=1
        return result

    def _flush(self):
        self.work.query_reads+=1
        if not self.pending:return
        before=self.work.total;self.flushes+=1;self.repair_serial+=1
        serial=self.repair_serial;index=self.index;b=index.base
        frontier=[];visited=[] if self.audit_batches is not None else None
        leaves=tuple(self.pending) if self.audit_batches is not None else None
        self.repair_leaves+=len(self.pending)
        for i,(lo,hi) in self.pending.items():
            p=b+i;index.lower[p],index.upper[p]=lo,hi
            self.work.query_reads+=3;self.work.statistic_writes+=2
            if p>1:
                p//=2;self.work.query_reads+=1
                if self.seen[p]!=serial:
                    self.seen[p]=serial;frontier.append(p);self.work.statistic_writes+=2
        while frontier:
            following=[]
            for p in frontier:
                if visited is not None:visited.append(p)
                self.repair_visits+=1
                left,right=2*p,2*p+1
                lo=max(index.lower[left],index.lower[right])
                hi=max(index.upper[left],index.upper[right])
                c=left if index.upper[left]>=index.upper[right] else right
                witness=self.witness[c]
                # A candidate need not be valid. Prefer a valid tied candidate
                # when cheap, but NEVER propagate a witness-only change upward.
                other=right if c==left else left
                self.work.query_reads+=9
                if (witness<0 or self.upper[self.leaf_nodes[witness]]!=hi) and index.upper[other]==hi:
                    witness=self.witness[other];self.work.query_reads+=2
                self.witness[p]=witness;self.work.statistic_writes+=1
                self.work.query_reads+=2
                if (lo,hi)!=(index.lower[p],index.upper[p]):
                    index.lower[p],index.upper[p]=lo,hi;self.work.statistic_writes+=2
                    if p>1:
                        parent=p//2;self.work.query_reads+=1
                        if self.seen[parent]!=serial:
                            self.seen[parent]=serial;following.append(parent);self.work.statistic_writes+=2
            frontier=following;self.work.statistic_writes+=1
        if self.audit_batches is not None:
            self.audit_batches.append(dict(epoch=self.epoch,leaves=leaves,visited=tuple(visited)))
        self.work.statistic_writes+=len(self.pending)+5
        self.pending.clear();self.pending_max_lower=0;self.flush_epoch=self.epoch
        self.pending_min=len(self.leaf_nodes);self.pending_max=-1
        self.repair_work+=self.work.total-before

    def interval(self,node):
        i=self.ids[node];self.work.query_reads+=2
        if self.stamp[i]==self.epoch:return self.cache[i]
        single=self.single[i];self.work.query_reads+=1
        if self.certificates and single>=0:
            leaf=self.leaf_nodes[single];answer=(self.lower[leaf],self.upper[leaf])
            self.cache_witness[i]=single;self.direct_hits+=1
            self.work.query_reads+=3;self.work.statistic_writes+=1
        else:
            answer=None
            if self.certificates and self.pending:answer=self._certificate(i)
            if answer is None:
                self._flush()
                lo,hi=-float('inf'),-float('inf');witness=-1;valid=False
                for p in self.covers[i]:
                    lo=max(lo,self.index.lower[p]);value=self.index.upper[p]
                    self.work.query_reads+=2
                    if value>hi or (value==hi and not valid):
                        candidate=self.witness[p]
                        candidate_valid=candidate>=0 and self.upper[self.leaf_nodes[candidate]]==value
                        self.work.query_reads+=3
                        if value>hi or candidate_valid:
                            hi,witness,valid=value,candidate,candidate_valid
                answer=(lo,hi);self.cache_witness[i]=witness;self.work.statistic_writes+=1
        self.cache[i],self.stamp[i]=answer,self.epoch;self.work.statistic_writes+=3
        return answer

    def decision_children(self,node):return [self.interval(c) for c in self.graph.children[node]]


class AuditedRangeBatch:
    """Untimed audit wrapper for the unchanged reference's actual repair visits.

    Delegates to the existing RangeBounds and wraps index.update/rebuild. The
    visiting kernels below are verbatim equivalents of MaxIndex, with visits
    recorded separately. This object is never used in reported timings.
    """
    def __init__(self,graph,work,scale=1):
        from .demand_bounds import RangeBounds
        self.backend=RangeBounds(graph,work,scale,batch=True)
        self.visits=[];self.leaves=[];index=self.backend.index
        original_rebuild=index.rebuild
        def rebuild():
            self.visits.extend(range(index.base-1,0,-1));original_rebuild()
        def update(leaf,lo,hi):
            p=index.base+leaf;index.lower[p],index.upper[p]=lo,hi
            work.statistic_writes+=2
            while p>1:
                p//=2;self.visits.append(p)
                a=max(index.lower[2*p],index.lower[2*p+1])
                b=max(index.upper[2*p],index.upper[2*p+1]);work.query_reads+=6
                if (a,b)==(index.lower[p],index.upper[p]):break
                index.lower[p],index.upper[p]=a,b;work.statistic_writes+=2
        index.rebuild=rebuild;index.update=update

    def publish(self,*args):return self.backend.publish(*args)

    def _record_pending(self):self.leaves.extend(self.backend.pending)

    def query(self,*args):
        self._record_pending();return self.backend.query(*args)

    def interval(self,*args):
        self._record_pending();return self.backend.interval(*args)
