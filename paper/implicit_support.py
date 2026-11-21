"""Exact support-aware LUCB with bounded interval compilation and shared indexes.

All methods implement the same root policy. No full descendant-support closure.
Unknown compiled supports use a single-action DFS fallback, paid and uncached
across action changes. Baselines receive identical compilation and atom sharing.
"""
from bisect import bisect_left
from collections import OrderedDict
from functools import cmp_to_key

from dag_mcts.certified_uct import UCTWork,IndexedMaxHeap
from paper.sampling_confidence_allcount import MixtureIntervals

METHODS=('atom_scan','lazy_views','range_index')
EMPTY=(-1,0)


def paid_sort(xs,w):
    def cmp(a,b):
        w.heap_comparisons+=1
        return (a>b)-(a<b)
    result=sorted(xs,key=cmp_to_key(cmp));w.statistic_writes+=len(result)
    return result


def merge_ranges(ranges,w,cap=None):
    out=[]
    for lo,hi in paid_sort(ranges,w):
        w.query_reads+=2
        if out and lo<=out[-1][1]:out[-1]=(out[-1][0],max(out[-1][1],hi))
        else:out.append((lo,hi))
        w.statistic_writes+=1
    return None if cap is not None and len(out)>cap else tuple(out)


class Topology:
    def __init__(self,g,w,cap=8):
        self.g,self.w,self.cap=g,w,cap;L=len(g.leaves)
        seen=set();leaves=[];stack=[g.root]
        while stack:
            v=stack.pop();w.query_reads+=1;w.statistic_writes+=1
            if v in seen:continue
            seen.add(v);w.statistic_writes+=1
            if not g.children[v]:leaves.append(v);w.statistic_writes+=1
            for c in reversed(g.children[v]):stack.append(c);w.edge_reads+=1;w.statistic_writes+=1
        self.leaves=tuple(leaves);self.rank={v:i for i,v in enumerate(self.leaves)}
        self.ranges=[None]*len(g);self.owner=[len(g.children[g.root])]*len(g)
        self.parent=[-1]*len(g);w.initialization+=4*len(g)+2*L
        for a,v in enumerate(g.children[g.root]):
            self.owner[v]=min(a,self.owner[v]);w.query_reads+=1;w.statistic_writes+=1
        for v in g.order:
            for c in g.children[v]:
                w.edge_reads+=1;w.query_reads+=2
                if self.parent[c]<0:self.parent[c]=v;w.statistic_writes+=1
                if v!=g.root and self.owner[v]<self.owner[c]:
                    self.owner[c]=self.owner[v];w.statistic_writes+=1
        for v in reversed(g.order):
            row=g.children[v]
            if not row:
                i=self.rank[v];self.ranges[v]=((i,i+1),);w.statistic_writes+=1
            else:
                pieces=[];known=True
                for c in row:
                    w.edge_reads+=1;w.query_reads+=1
                    if self.ranges[c] is None:known=False;break
                    pieces.extend(self.ranges[c]);w.statistic_writes+=len(self.ranges[c])
                if known:self.ranges[v]=merge_ranges(pieces,w,cap);w.statistic_writes+=1
        # All leaves of each atom have identical membership in every root arm.
        roots=[self.ranges[v] for v in g.children[g.root]];w.query_reads+=len(roots)
        if all(r is not None for r in roots):
            edges={0,L}
            for ranges in roots:
                for lo,hi in ranges:edges.add(lo);edges.add(hi);w.statistic_writes+=2
            self.boundaries=paid_sort(edges,w)
        else:
            self.boundaries=list(range(L+1));w.initialization+=L+1
        self.boundary_rank={x:i for i,x in enumerate(self.boundaries)}
        self.atom_of=[0]*L
        for k,(lo,hi) in enumerate(zip(self.boundaries,self.boundaries[1:])):
            for i in range(lo,hi):self.atom_of[i]=k;w.statistic_writes+=1
        w.initialization+=len(self.boundaries)+L
        self.last_action=None;self.last_ranges=None;self.fallbacks=0

    def action_ranges(self,a):
        w=self.w;w.query_reads+=2
        if a==self.last_action:return self.last_ranges
        v=self.g.children[self.g.root][a];rs=self.ranges[v]
        if rs is None:
            self.fallbacks+=1;seen=set();marked=[False]*len(self.leaves);stack=[v]
            w.initialization+=len(marked);w.statistic_writes+=1
            while stack:
                x=stack.pop();w.query_reads+=1;w.statistic_writes+=1
                if x in seen:continue
                seen.add(x);w.statistic_writes+=1
                if not self.g.children[x]:marked[self.rank[x]]=True;w.statistic_writes+=1
                for c in self.g.children[x]:stack.append(c);w.edge_reads+=1;w.statistic_writes+=1
            out=[];start=None
            for i,flag in enumerate(marked+[False]):
                w.query_reads+=1
                if flag and start is None:start=i
                if not flag and start is not None:out.append((start,i));start=None;w.statistic_writes+=1
            rs=tuple(out)
        result=tuple((self.boundary_rank[lo],self.boundary_rank[hi]) for lo,hi in rs)
        w.query_reads+=2*len(rs);w.statistic_writes+=len(rs)+2
        self.last_action,self.last_ranges=a,result
        return result


class MaxTree:
    def __init__(self,values,w):
        self.w=w;self.size=1
        while self.size<len(values):self.size*=2
        self.tree=[EMPTY]*(2*self.size);w.initialization+=2*self.size
        self.tree[self.size:self.size+len(values)]=values;w.statistic_writes+=len(values)
        for i in range(self.size-1,0,-1):
            self.tree[i]=max(self.tree[2*i],self.tree[2*i+1]);w.heap_comparisons+=1;w.statistic_writes+=1

    def update(self,i,value):
        w=self.w;i+=self.size;self.tree[i]=value;w.statistic_writes+=1;i//=2
        while i:
            value=max(self.tree[2*i],self.tree[2*i+1]);w.heap_comparisons+=1;w.query_reads+=2
            if value==self.tree[i]:break
            self.tree[i]=value;w.statistic_writes+=1;i//=2

    def query(self,lo,hi):
        w=self.w;ans=EMPTY;lo+=self.size;hi+=self.size
        while lo<hi:
            w.query_reads+=2
            if lo%2:ans=max(ans,self.tree[lo]);lo+=1;w.heap_comparisons+=1;w.query_reads+=1
            if hi%2:hi-=1;ans=max(ans,self.tree[hi]);w.heap_comparisons+=1;w.query_reads+=1
            lo//=2;hi//=2
        return ans


class SupportIndex:
    def __init__(self,g,w,scale,mode,cap=8):
        if mode not in METHODS:raise ValueError(mode)
        self.g,self.w,self.scale,self.mode=g,w,scale,mode
        self.topology=Topology(g,w,cap);t=self.topology;L=len(t.leaves)
        self.lower=[0]*L;self.upper=[scale]*L;w.initialization+=2*L
        self.lower_heap=IndexedMaxHeap([(0,-t.owner[x],-x) for x in t.leaves],w)
        self.heaps=[];self.atom_keys=[]
        for lo,hi in zip(t.boundaries,t.boundaries[1:]):
            keys=[(scale,-t.leaves[i]) for i in range(lo,hi)]
            heap=IndexedMaxHeap(keys,w) if hi-lo>1 else None
            self.heaps.append(heap);self.atom_keys.append(heap.keys[heap.top] if heap is not None else keys[0])
            w.initialization+=3+len(keys);w.query_reads+=2
        self.tree=MaxTree(self.atom_keys,w) if mode=='range_index' else None
        self.views=OrderedDict();self.view_builds=self.repairs=self.upper_changes=self.queries=0

    def publish(self,leaf,lo,hi):
        t=self.topology;w=self.w;i=t.rank[leaf];w.query_reads+=4
        if not self.lower[i]<=lo<=hi<=self.upper[i]:raise ValueError('Need nested integer intervals')
        if lo!=self.lower[i]:
            self.lower[i]=lo;self.lower_heap.update(i,(lo,-t.owner[leaf],-leaf));w.statistic_writes+=1
        if hi!=self.upper[i]:
            self.upper[i]=hi;w.statistic_writes+=1;k=t.atom_of[i];heap=self.heaps[k]
            if heap is not None:
                heap.update(i-t.boundaries[k],(hi,-leaf));key=heap.keys[heap.top]
            else:key=(hi,-leaf)
            w.query_reads+=3
            if key!=self.atom_keys[k]:
                self.atom_keys[k]=key;self.upper_changes+=1;w.statistic_writes+=1
                if self.tree is not None:self.tree.update(k,key)

    def candidate(self):
        self.w.query_reads+=4
        i=self.lower_heap.top
        return self.topology.owner[self.topology.leaves[i]],self.lower[i]

    def _partition(self,rs):
        inside=[];outside=[];j=0;w=self.w
        for k in range(len(self.atom_keys)):
            while j<len(rs) and k>=rs[j][1]:j+=1;w.query_reads+=1
            good=j<len(rs) and rs[j][0]<=k<rs[j][1];w.query_reads+=3
            (inside if good else outside).append(k);w.statistic_writes+=1
        return inside,outside

    def _lazy_max(self,view):
        ids,heap=view;w=self.w
        if not ids:return EMPTY
        while True:
            i=heap.top;k=ids[i];key=self.atom_keys[k];w.query_reads+=4
            if heap.keys[i]==key:return key
            assert heap.keys[i]>=key
            heap.update(i,key);self.repairs+=1

    def query(self):
        self.queries+=1;a,lo=self.candidate();w=self.w
        rs=None if self.mode=='lazy_views' and a in self.views else self.topology.action_ranges(a)
        if self.mode=='range_index':
            inside=outside=EMPTY;prev=0
            for l,h in rs:
                inside=max(inside,self.tree.query(l,h));outside=max(outside,self.tree.query(prev,l))
                prev=h;w.heap_comparisons+=2
            outside=max(outside,self.tree.query(prev,len(self.atom_keys)));w.heap_comparisons+=1
        elif self.mode=='atom_scan':
            inside=outside=EMPTY;j=0
            for k,key in enumerate(self.atom_keys):
                while j<len(rs) and k>=rs[j][1]:j+=1;w.query_reads+=1
                good=j<len(rs) and rs[j][0]<=k<rs[j][1];w.query_reads+=4;w.heap_comparisons+=1
                if good:inside=max(inside,key)
                else:outside=max(outside,key)
        else:
            w.query_reads+=1
            if a not in self.views:
                if len(self.views)>=32:self.views.popitem(last=False);w.statistic_writes+=1
                ids=self._partition(rs);views=[]
                for group_ids in ids:
                    views.append((group_ids,IndexedMaxHeap([self.atom_keys[k] for k in group_ids],w)))
                    w.query_reads+=len(group_ids)
                self.views[a]=views;self.view_builds+=1;w.statistic_writes+=1
            self.views.move_to_end(a);w.statistic_writes+=2
            inside,outside=map(self._lazy_max,self.views[a])
        return a,lo,inside,outside


class ImplicitSearch:
    def __init__(self,p,c,seed,method):
        self.g=p.graph;self.work=UCTWork();w=self.work
        w.initialization+=16*len(self.g)+10*sum(map(len,self.g.children))+4*len(self.g.leaves)
        self.index=SupportIndex(self.g,w,c['scale'],method,c.get('interval_cap',8))
        self.ev=MixtureIntervals(self.g,w,c['delta'],c['scale']);self.oracle=p.oracle(seed)
        self.tolerance=round(c['epsilon']*c['scale']);self.calls=0;self.decision=None;self.pair=None

    def query(self):
        a,lo,x,y=self.index.query();self.work.query_reads+=2
        good=y==EMPTY or y[0]<=lo+self.tolerance
        self.pair=(-x[1],-y[1]) if not good else None
        self.decision=(a,good)
        return a,good,lo,x,y

    def observe(self,leaf):
        w=self.work;t=self.index.topology;path=[leaf];v=leaf;w.statistic_writes+=1
        while v!=self.g.root:v=t.parent[v];path.append(v);w.edge_reads+=1;w.statistic_writes+=1
        path.reverse();w.statistic_writes+=len(path)
        reward=self.oracle.sample(leaf);self.calls+=1
        pair=self.ev.observe(leaf,reward)
        if self.ev.conflict:raise ArithmeticError('Abort on empty confidence interval')
        if pair is not None:self.index.publish(leaf,*pair)
        self.last_publication=(leaf,*pair) if pair is not None else None
        return tuple(path),reward

    def block(self,cadence=32):
        pair=self.pair;observations=[];pubs=[]
        for i in range(cadence):
            observations.append(self.observe(pair[i%2]))
            if self.last_publication is not None:pubs.append(self.last_publication)
        self.work.statistic_writes+=len(pubs)
        return observations,self.query(),pubs
