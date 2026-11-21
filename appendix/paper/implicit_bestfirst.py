"""A bounded exact maximum search for fragmented root supports."""
import argparse
from dag_mcts.certified_uct import UCTWork
from dag_mcts.completion_accuracy import sha
from paper.sampling_confidence_allcount import MixtureIntervals
from paper.implicit_support import EMPTY,SupportIndex
from paper.implicit_witness import WitnessIndex,WitnessSearch
import paper.implicit_benchmark as base


class BestFirstIndex(WitnessIndex):
    def __init__(self,g,w,scale,cap=8):
        super().__init__(g,w,scale,'witness_range',cap)
        self.probes=self.aborts=0;w.initialization+=2

    def _position(self,rs,k):
        lo=0;hi=len(rs);w=self.w
        while lo<hi:
            m=(lo+hi)//2;w.query_reads+=1;w.heap_comparisons+=1
            if rs[m][0]<=k:lo=m+1
            else:hi=m
        return lo-1

    def _best(self,rs,wanted,start,allowance):
        w=self.w;G=len(self.atom_keys);stack=[(1,0,self.tree.size)];answer=EMPTY
        w.statistic_writes+=1
        while stack:
            w.query_reads+=1
            if w.total-start>allowance:return None
            node,lo,hi=stack.pop();self.probes+=1;w.statistic_writes+=1;w.query_reads+=2
            key=self.tree.tree[node]
            if lo>=G or key<=answer:continue
            hi=min(hi,G);j=self._position(rs,lo);w.query_reads+=3
            all_in=j>=0 and rs[j][1]>=hi
            all_out=(j<0 or rs[j][1]<=lo) and (j+1==len(rs) or rs[j+1][0]>=hi)
            if (wanted and all_out) or (not wanted and all_in):continue
            if (wanted and all_in) or (not wanted and all_out):
                answer=key;continue
            k=self.topology.atom_of[self.topology.rank[-key[1]]];j=self._position(rs,k);w.query_reads+=4
            inside=j>=0 and k<rs[j][1]
            if inside==wanted:answer=key;continue
            # Original node span is a power of two; clamp only for membership.
            depth=node.bit_length()-1;span=self.tree.size>>depth
            mid=lo+span//2;left=(2*node,lo,mid);right=(2*node+1,mid,lo+span)
            w.query_reads+=2;w.heap_comparisons+=1;w.statistic_writes+=2
            if self.tree.tree[2*node]>=self.tree.tree[2*node+1]:stack.extend((right,left))
            else:stack.extend((left,right))
        return answer

    def query(self):
        a,lo=self.candidate();w=self.w;w.query_reads+=1;old=self.witnesses.get(a)
        if old is not None:
            good=True
            for key in old:
                w.query_reads+=3
                if key!=EMPTY and self.upper[self.topology.rank[-key[1]]]!=key[0]:good=False
            if good:self.hits+=1;self.queries+=1;return a,lo,*old
        self.misses+=1;rs=self.topology.action_ranges(a);G=len(self.atom_keys)
        allowance=5*min(G,(2*len(rs)+1)*max(1,G.bit_length()));w.query_reads+=3
        start=w.total;x=self._best(rs,True,start,allowance)
        y=self._best(rs,False,start,allowance) if x is not None else None
        if x is None or y is None:
            self.aborts+=1;mode=self.mode
            if (2*len(rs)+1)*max(1,G.bit_length())>G:self.mode='atom_scan';self.scan_fallbacks+=1
            try:result=SupportIndex.query(self)
            finally:self.mode=mode
        else:self.queries+=1;result=(a,lo,x,y)
        self.witnesses[a]=result[2:];w.statistic_writes+=1
        return result


class BestFirstSearch(WitnessSearch):
    def __init__(self,p,c,seed,method):
        if method!='bestfirst':super().__init__(p,c,seed,method);return
        self.g=p.graph;self.work=UCTWork();w=self.work
        w.initialization+=16*len(self.g)+10*sum(map(len,self.g.children))+4*len(self.g.leaves)
        self.index=BestFirstIndex(self.g,w,c['scale'],c.get('interval_cap',8))
        self.ev=MixtureIntervals(self.g,w,c['delta'],c['scale']);self.oracle=p.oracle(seed)
        self.tolerance=round(c['epsilon']*c['scale']);self.calls=0;self.decision=None;self.pair=None


def run(out):
    old_search,old_methods,old_config,old_sources,old_measure=base.ImplicitSearch,base.METHODS,base.configurations,base.sources,base.measure
    current=[]
    def sources():
        d=old_sources()
        for p in ('paper/implicit_witness.py','paper/implicit_witness_amendment.txt','tests/test_implicit_witness.py',
                  'paper/implicit_bestfirst.py','paper/implicit_bestfirst_amendment.txt','tests/test_implicit_bestfirst.py'):d[p]=sha(p)
        return d
    def factory(p,c,seed,method):
        s=BestFirstSearch(p,c,seed,method);current.append(s);return s
    def measure(p,c,seed,method):
        r=old_measure(p,c,seed,method);idx=current.pop().index
        r['index_memory_bytes']=base.retained_bytes(idx,(p.graph,idx.w))
        for name in ('hits','misses','scan_fallbacks','probes','aborts'):r[name]=getattr(idx,name,0)
        return r
    base.ImplicitSearch=factory;base.METHODS=('lazy_views','witness_scan','witness_range','bestfirst')
    base.configurations=lambda:[c for c in old_config() if c['epsilon']==.1]
    base.sources=sources;base.measure=measure
    try:base.online(out)
    finally:base.ImplicitSearch,base.METHODS,base.configurations,base.sources,base.measure=old_search,old_methods,old_config,old_sources,old_measure


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args();run(a.out)
