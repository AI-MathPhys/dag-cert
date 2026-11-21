"""A memory-bounded exact support cache offered equally to both final methods."""
import argparse
from collections import OrderedDict
from types import MethodType
from dag_mcts.completion_accuracy import sha
from paper.implicit_support import Topology
from paper.implicit_bestfirst import BestFirstSearch
import paper.implicit_benchmark as base


def cached_ranges(t,a):
    w=t.w;w.query_reads+=1
    if t.ranges[t.g.children[t.g.root][a]] is not None:return Topology.action_ranges(t,a)
    w.query_reads+=1
    if a in t.support_cache:
        t.support_hits+=1;t.support_cache.move_to_end(a);w.statistic_writes+=2
        t.last_action,t.last_ranges=a,t.support_cache[a];w.statistic_writes+=2
        return t.last_ranges
    rs=Topology.action_ranges(t,a)
    while t.support_entries+len(rs)>len(t.leaves):
        _,old=t.support_cache.popitem(last=False);t.support_entries-=len(old);w.statistic_writes+=2
    t.support_cache[a]=rs;t.support_entries+=len(rs);w.statistic_writes+=2
    return rs


class CachedSearch(BestFirstSearch):
    def __init__(self,p,c,seed,method):
        super().__init__(p,c,seed,'bestfirst' if method=='cached_bestfirst' else 'lazy_views')
        t=self.index.topology;t.support_cache=OrderedDict();t.support_entries=t.support_hits=0
        t.action_ranges=MethodType(cached_ranges,t);self.work.initialization+=6


def run(out):
    old_search,old_methods,old_config,old_sources,old_measure=base.ImplicitSearch,base.METHODS,base.configurations,base.sources,base.measure
    current=[]
    def sources():
        d=old_sources()
        for p in ('paper/implicit_witness.py','paper/implicit_bestfirst.py','paper/implicit_cached.py',
                  'paper/implicit_cache_amendment.txt','paper/implicit_bestfirst_amendment.txt',
                  'tests/test_implicit_cached.py','tests/test_implicit_bestfirst.py'):d[p]=sha(p)
        return d
    def factory(p,c,seed,method):
        s=CachedSearch(p,c,seed,method);current.append(s);return s
    def measure(p,c,seed,method):
        r=old_measure(p,c,seed,method);s=current.pop();idx=s.index;t=idx.topology
        r['index_memory_bytes']=base.retained_bytes(idx,(p.graph,idx.w))
        for name in ('hits','misses','scan_fallbacks','probes','aborts'):r[name]=getattr(idx,name,0)
        r['support_cache_entries']=t.support_entries;r['support_cache_hits']=t.support_hits
        assert t.support_entries<=len(t.leaves)
        return r
    base.ImplicitSearch=factory;base.METHODS=('cached_lazy','cached_bestfirst')
    base.configurations=lambda:[c for c in old_config() if c['epsilon']==.1]
    base.sources=sources;base.measure=measure
    try:base.online(out)
    finally:base.ImplicitSearch,base.METHODS,base.configurations,base.sources,base.measure=old_search,old_methods,old_config,old_sources,old_measure


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args();run(a.out)
