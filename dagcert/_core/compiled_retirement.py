"""Representation controls with identical cached MAX maintenance and retirement.

The UCT graph and canonical evidence are unchanged. Only the monitor circuit
is compiled. All compiler candidates are paid before choosing a layout.
"""
from .graph import DAG
from .certified_uct import UCTWork, TranspositionUCT
from .retired_bounds import CanonicalIntervals, RetiredBounds
from .onpolicy_backup import CompiledCovers
from dagcert._core._interval_utils import merge


def quotient(graph, work):
    """Hash-cons identical gates and bypass unary gates; preserve root action IDs."""
    rows, intern, alias, leaves = [], {}, {}, {}
    for v in reversed(graph.order):
        children = graph.children[v]
        work.edge_reads += len(children)
        if not children:
            alias[v] = len(rows)
            leaves[v] = len(rows)
            rows.append(())
        elif v != graph.root:
            key = tuple(sorted(set(alias[c] for c in children)))
            # Upper bound on comparison sorting, plus traversal and hashing.
            work.heap_comparisons += len(children)*max(1,len(children).bit_length())
            work.query_reads += 2*len(children)
            if len(key)==1:
                alias[v] = key[0]
            elif key in intern:
                alias[v] = intern[key]
            else:
                alias[v] = intern[key] = len(rows)
                rows.append(key)
        work.statistic_writes += 2
    actions = []
    for v in graph.children[graph.root]:
        actions.append(len(rows))
        rows.append((alias[v],))
    root = len(rows)
    rows.append(tuple(actions))
    work.initialization += 8*len(rows)+6*sum(map(len,rows))
    work.statistic_writes += len(alias)+len(intern)
    return DAG(rows,root=root),leaves,dict(order='structural',entries=sum(map(len,rows)))


def leaf_order(graph, dfs, work):
    if not dfs:
        work.query_reads += len(graph.leaves)
        return graph.leaves
    order, seen, pending = [],set(),[graph.root]
    while pending:
        v=pending.pop()
        work.query_reads += 2
        if v in seen:
            continue
        seen.add(v)
        work.statistic_writes += 1
        if graph.children[v]:
            pending.extend(reversed(graph.children[v]))
            work.edge_reads += len(graph.children[v])
        else:
            order.append(v)
    work.statistic_writes += len(seen)+len(order)
    return tuple(order)


def cover_compile(graph, work):
    """Try ID and topology DFS leaf layouts, select fewer root block incidences."""
    candidates=[]
    for dfs in (False,True):
        leaves=leaf_order(graph,dfs,work)
        rank={v:i for i,v in enumerate(leaves)}
        spans=[()] * len(graph)
        size=1 << (len(leaves)-1).bit_length()
        for v in reversed(graph.order):
            children=graph.children[v]
            work.edge_reads += len(children)
            if not children:
                i=rank[v]; spans[v]=((i,i+1),)
            elif len(children)==1:
                spans[v]=spans[children[0]]
            else:
                parts=[p for c in children for p in spans[c]]
                work.query_reads += len(parts)
                spans[v]=merge(parts,work)
            work.statistic_writes += 1
        covers=[]
        for v in graph.children[graph.root]:
            blocks=[]
            for lo,hi in spans[v]:
                lo+=size; hi+=size
                while lo<hi:
                    work.query_reads += 2
                    if lo&1: blocks.append(lo);lo+=1
                    if hi&1: hi-=1;blocks.append(hi)
                    lo//=2;hi//=2
            covers.append(tuple(sorted(blocks)))
            work.heap_comparisons += len(blocks)*max(1,len(blocks).bit_length())
            work.statistic_writes += len(blocks)
        candidates.append((sum(map(len,covers)),dfs,leaves,size,covers))
        work.statistic_writes += sum(map(len,spans))+len(spans)+len(rank)
    entries,dfs,leaves,size,covers=min(candidates,key=lambda x:(x[0],x[1]))
    rows=[];nodes={};mapping={}
    def build(block):
        work.query_reads += 1
        if block in nodes:
            return nodes[block]
        if block>=size:
            node=len(rows);rows.append(())
            mapping[leaves[block-size]]=node
        else:
            a,b=build(2*block),build(2*block+1)
            node=len(rows);rows.append((a,b))
        nodes[block]=node
        work.statistic_writes += 3
        return node
    actions=[];groups={}
    for cover in covers:
        if cover not in groups:
            ids=tuple(build(b) for b in cover)
            if len(ids)==1:
                groups[cover]=ids[0]
            else:
                groups[cover]=len(rows);rows.append(ids)
        actions.append(len(rows));rows.append((groups[cover],))
        work.query_reads += len(cover)+1
    root=len(rows);rows.append(tuple(actions))
    work.initialization += 8*len(rows)+6*sum(map(len,rows))
    work.statistic_writes += sum(c[0] for c in candidates)+len(nodes)+len(groups)
    return DAG(rows,root=root),mapping,dict(order='dfs' if dfs else 'id',
                entries=entries,candidate_entries=[c[0] for c in candidates])


class CircuitMonitor:
    def __init__(self,graph,method,delta=.05):
        self.work=w=UCTWork()
        self.evidence=CanonicalIntervals(graph,w,delta)
        circuit,self.mapping,self.info=(cover_compile(graph,w) if method=='cover-live'
                                        else quotient(graph,w))
        self.compile_work=w.total
        self.bounds=RetiredBounds(circuit,w,'eager' if method=='graph-eager' else 'live')
        self.info.update(nodes=len(circuit),edges=sum(map(len,circuit.children)))
    def step(self,leaf,reward):
        interval=self.evidence.observe(leaf,reward)
        if interval is not None:
            self.bounds.publish(self.mapping[leaf],*interval)
    def query(self):
        return self.bounds.query()


class Search:
    def __init__(self,problem,seed,method,epsilon,effort=0):
        self.uct=TranspositionUCT(problem.graph,exploration=2.)
        self.oracle=problem.oracle(seed)
        self.monitor=(CompiledCovers(problem.graph,.05) if method=='covers'
                      else CircuitMonitor(problem.graph,method))
        self.epsilon=epsilon
        self.query=self.monitor.query()
        self.action=self.uct.recommend_action()
        self.certified=self.query[1]<=epsilon
        self.first_cut=None
        self.effort=effort
        self.extra_work=0
        self.sink=0
        self.monitor.work.initialization += 2*len(problem.graph.leaves)
    def step(self):
        path,reward=self.uct.step(self.oracle)
        # A declared CPU evaluation surcharge. It changes neither the sample nor RNG.
        z=path[-1]+self.uct.calls
        for _ in range(self.effort):
            z=(1664525*z+1013904223)&0xffffffff
        self.sink=z
        self.extra_work+=3*self.effort
        j=path[-1];ev=self.monitor.evidence
        old=ev.lower[j],ev.upper[j]
        self.monitor.step(j,reward)
        self.monitor.work.query_reads+=4
        if old!=(ev.lower[j],ev.upper[j]):
            self.query=self.monitor.query()
        self.certified=not ev.conflict and self.query[1]<=self.epsilon
        self.action=self.query[0] if self.certified else self.uct.recommend_action()
        b=getattr(self.monitor,'bounds',None)
        if self.first_cut is None and b is not None and b.retired:
            self.first_cut=self.uct.calls
        return path,reward
    @property
    def work(self):
        return (self.uct.work.total+self.monitor.work.total-self.uct.calls+
                self.extra_work+getattr(self.oracle,'operations',0))

