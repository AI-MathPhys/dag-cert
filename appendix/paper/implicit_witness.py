"""Paid monotone maximum certificates; same cache offered to the scan baseline."""
import argparse
from dag_mcts.certified_uct import UCTWork
from dag_mcts.completion_accuracy import sha
from paper.sampling_confidence_allcount import MixtureIntervals
from paper.implicit_support import ImplicitSearch,SupportIndex,EMPTY
import paper.implicit_benchmark as base


class WitnessIndex(SupportIndex):
    def __init__(self,g,w,scale,mode,cap=8):
        super().__init__(g,w,scale,'range_index' if mode=='witness_range' else 'atom_scan',cap)
        self.witnesses={};self.hits=self.misses=self.scan_fallbacks=0;w.initialization+=4

    def query(self):
        a,lo=self.candidate();w=self.w;w.query_reads+=1
        old=self.witnesses.get(a)
        if old is not None:
            valid=True
            for key in old:
                w.query_reads+=3
                if key!=EMPTY and self.upper[self.topology.rank[-key[1]]]!=key[0]:valid=False
            if valid:
                self.hits+=1;self.queries+=1
                return a,lo,*old
        self.misses+=1
        old_mode=self.mode
        if old_mode=='range_index':
            rs=self.topology.action_ranges(a);G=len(self.atom_keys);w.query_reads+=3
            if (2*len(rs)+1)*max(1,G.bit_length())>G:
                self.mode='atom_scan';self.scan_fallbacks+=1
        try:result=super().query()
        finally:self.mode=old_mode
        self.witnesses[a]=result[2:];w.statistic_writes+=1
        return result


class WitnessSearch(ImplicitSearch):
    def __init__(self,p,c,seed,method):
        if not method.startswith('witness_'):super().__init__(p,c,seed,method);return
        self.g=p.graph;self.work=UCTWork();w=self.work
        w.initialization+=16*len(self.g)+10*sum(map(len,self.g.children))+4*len(self.g.leaves)
        self.index=WitnessIndex(self.g,w,c['scale'],method,c.get('interval_cap',8))
        self.ev=MixtureIntervals(self.g,w,c['delta'],c['scale']);self.oracle=p.oracle(seed)
        self.tolerance=round(c['epsilon']*c['scale']);self.calls=0;self.decision=None;self.pair=None


def run(out):
    old_search,old_methods,old_config,old_sources,old_measure=base.ImplicitSearch,base.METHODS,base.configurations,base.sources,base.measure
    def sources():
        d=old_sources()
        for p in ('paper/implicit_witness.py','paper/implicit_witness_amendment.txt','tests/test_implicit_witness.py'):d[p]=sha(p)
        return d
    current=[]
    def factory(p,c,seed,method):
        s=WitnessSearch(p,c,seed,method);current.append(s);return s
    def measure(p,c,seed,method):
        r=old_measure(p,c,seed,method);idx=current.pop().index
        r['index_memory_bytes']=base.retained_bytes(idx,(p.graph,idx.w))
        r['witness_hits']=getattr(idx,'hits',0);r['witness_misses']=getattr(idx,'misses',0)
        r['scan_fallbacks']=getattr(idx,'scan_fallbacks',0)
        return r
    base.ImplicitSearch=factory;base.METHODS=('lazy_views','range_index','witness_scan','witness_range')
    base.configurations=lambda:[c for c in old_config() if c['epsilon']==.1]
    base.sources=sources;base.measure=measure
    try:base.online(out)
    finally:
        base.ImplicitSearch,base.METHODS,base.configurations,base.sources,base.measure=old_search,old_methods,old_config,old_sources,old_measure


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args();run(a.out)
