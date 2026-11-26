"""Exact root-confidence monitors on the ordinary transposition-aware UCT policy."""
from .certified_uct import TranspositionUCT, UCTWork
from .maintenance_replay import Replay
from .retired_bounds import CanonicalIntervals
from .root_flat_control import FlatReplay


class CompiledCovers:
    """Compile terminal supports to interned dyadic covers of one shared max tree."""
    def __init__(self, graph, delta):
        self.work = w = UCTWork()
        self.evidence = CanonicalIntervals(graph, w, delta)
        count = len(graph.leaves)
        self.size = 1 << (count-1).bit_length()
        self.rank = {leaf:j for j,leaf in enumerate(graph.leaves)}
        from dagcert._core._interval_utils import CountTree, merge
        intervals = [()] * len(graph)
        w.initialization += len(graph)+2*count
        for v in reversed(graph.order):
            children = graph.children[v]
            if not children:
                j = self.rank[v]
                intervals[v] = ((j,j+1),)
            elif len(children)==1:
                intervals[v] = intervals[children[0]]
            else:
                parts = [part for child in children for part in intervals[child]]
                w.edge_reads += len(children)
                w.query_reads += len(parts)
                intervals[v] = merge(parts,w)
            w.statistic_writes += 1
        groups = {}
        self.w = w  # CountTree.cover uses the shared tariff ledger.
        self.covers = []
        self.actions = []
        for v in graph.children[graph.root]:
            spans = intervals[v]
            w.query_reads += 1+len(spans)
            if spans not in groups:
                groups[spans] = len(self.covers)
                self.covers.append(tuple(CountTree.cover(self,spans)))
            self.actions.append(groups[spans])
        w.statistic_writes += len(self.actions)+len(intervals)
        self.low = [0.]*(2*self.size)
        self.high = [-1.]*(2*self.size)
        self.high[self.size:self.size+count] = [1.]*count
        for i in reversed(range(1,self.size)):
            self.high[i] = max(self.high[2*i],self.high[2*i+1])
        w.initialization += 6*self.size+count+len(self.covers)
        self.entries = sum(map(len,self.covers))

    def step(self,leaf,reward):
        interval = self.evidence.observe(leaf,reward)
        if interval is None:
            return
        i = self.size+self.rank[leaf]
        lo,hi = interval
        while True:
            self.work.query_reads += 2
            if (lo,hi)==(self.low[i],self.high[i]):
                return
            self.low[i],self.high[i] = lo,hi
            self.work.statistic_writes += 2
            if i==1:
                return
            i //= 2
            lo = max(self.low[2*i],self.low[2*i+1])
            hi = max(self.high[2*i],self.high[2*i+1])
            self.work.query_reads += 4
            self.work.heap_comparisons += 2

    def query(self):
        if not self.covers:
            return -1,0.,self.low[1],self.high[1]
        lower,upper = [],[]
        for cover in self.covers:
            lower.append(max(self.low[i] for i in cover))
            upper.append(max(self.high[i] for i in cover))
            self.work.query_reads += 2*len(cover)+2
            self.work.heap_comparisons += 2*len(cover)
        action = max(range(len(self.actions)),key=lambda a:lower[self.actions[a]])
        best = lower[self.actions[action]]
        gap = max((upper[g]-best for j,g in enumerate(self.actions) if j!=action),default=0.)
        self.work.query_reads += 2*len(self.actions)+3
        return action,max(0.,gap),best,max(upper)


class MonitoredUCT:
    """A monitor may stop the sampler. It never selects any rollout edge."""
    def __init__(self,problem,seed,method,epsilon,exploration=2.,delta=.05):
        self.uct = TranspositionUCT(problem.graph,exploration=exploration)
        self.oracle = problem.oracle(seed)
        self.epsilon = epsilon
        if method in ('eager','live'):
            self.monitor = Replay(problem.graph,method,delta=delta)
        elif method=='flat':
            # The archived compiler uses the default .05 confidence level.
            if delta!=.05:
                raise ValueError('flat control requires delta=.05')
            self.monitor = FlatReplay(problem.graph)
        elif method=='covers':
            self.monitor = CompiledCovers(problem.graph,delta)
        else:
            raise ValueError(method)
        self.query = self.monitor.query()
        self.action = self.uct.recommend_action()
        self.certified = self.query[1]<=epsilon
        if self.certified:
            self.action = self.query[0]
        self.monitor.work.initialization += len(problem.graph.leaves)*2

    def step(self):
        if self.certified or self.monitor.evidence.conflict:
            raise RuntimeError('search already terminated')
        path,reward = self.uct.step(self.oracle)
        j = path[-1]
        ev = self.monitor.evidence
        old = ev.lower[j],ev.upper[j]
        self.monitor.step(j,reward)
        self.monitor.work.query_reads += 4
        if old!=(ev.lower[j],ev.upper[j]):
            self.query = self.monitor.query()
        self.certified = not ev.conflict and self.query[1]<=self.epsilon
        self.action = self.query[0] if self.certified else self.uct.recommend_action()
        return path,reward

    @property
    def work(self):
        # Both legacy ledgers book the same oracle call. The physical draw is unique.
        return self.uct.work.total+self.monitor.work.total-self.uct.calls

