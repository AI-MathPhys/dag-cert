"""Cold search implementations for the wall-time study.

Both Range and Partial use the same paired observation kernel. Once a
permanent frontier exists, Compact Partial reads flat endpoint arrays and
memoizes inside/outside partitions of that immutable set. The pre-seal
ledger and witness RNG have the same semantics as the reference solver.
"""
import math
from functools import partial

from paper.escrow_clearing import RewardBuffer
from paper.frontier_sampling import Search
from paper.partial_clearing import PartialSearch


class CompactFrontier:
    """A fixed frontier, sorted in the reference's descending terminal order."""
    def __init__(self, idx):
        self.idx = idx
        self.members = idx.F
        self.parts = {}
        idx.w.initialization += 4

    def maximum(self, keys, members):
        w = self.idx.w
        best = -1
        ties = []
        for j in members:
            value = keys[j]
            if value > best:
                best = value
                ties = [j]
            elif value == best:
                ties.append(j)
        # Upper tariff includes replacement, tie-list writes and disposal.
        w.query_reads += len(members)
        w.heap_comparisons += 2*len(members)
        w.statistic_writes += 2*len(members)+1
        return best,ties

    def choose(self, ties):
        self.idx.w.score_evaluations += 1
        return ties[self.idx.rng.randrange(len(ties))]

    def sides(self, a):
        idx = self.idx
        idx.w.query_reads += 1
        if a not in self.parts:
            inside, outside = [], []
            for j in self.members:
                group = inside if idx.top.contains(a,j,idx.w) else outside
                group.append(j)
            self.parts[a] = inside,outside
            # Both formation and eventual release of the lists are paid.
            idx.w.statistic_writes += 2*len(self.members)+4
        return self.parts[a]

    def candidate(self, anchor):
        # Exactly the reference rejection draws, followed by the same uniform
        # containing-action fallback in ascending action order.
        idx = self.idx
        actions = len(idx.top.inside)
        for _ in range(16):
            a = idx.rng.randrange(actions)
            idx.w.score_evaluations += 1
            if idx.top.contains(a,anchor,idx.w):
                return a
        owners = [a for a in range(actions) if idx.top.contains(a,anchor,idx.w)]
        idx.w.statistic_writes += len(owners)
        idx.w.score_evaluations += 1
        return owners[idx.rng.randrange(len(owners))]

    def query(self):
        idx = self.idx
        idx.q += 1
        lo,ties = self.maximum(idx.lower,self.members)
        a = self.candidate(self.choose(ties))
        inside,outside = self.sides(a)
        high,xt = self.maximum(idx.upper,inside)
        out,yt = self.maximum(idx.upper,outside)
        x = high,self.choose(xt)
        if out < idx.threshold:
            y = idx.threshold,None
        else:
            y = out,self.choose(yt)
        idx.witnesses = x[1],y[1]
        idx.w.statistic_writes += 2
        return a,lo,x,y


class PairedKernel:
    """Specialize only the ordinary fixed-pair block. Trials keep their own kernel."""
    def prepare_range_scan(self):
        # No copy of the values. Both methods receive exactly this service.
        self.idx.maxima = partial(scan_blocks, self.idx.ut.value, self.w)
        self.w.initialization += 3

    def book_block(self, draws, rounded, hops, list_writes, flat_updates):
        w=self.w
        self.N+=draws
        self.ev.evaluations+=draws
        w.edge_reads+=hops
        w.query_reads+=hops+2*flat_updates
        w.oracle_calls+=draws
        w.statistic_writes+=6*draws+list_writes+2*flat_updates
        w.confidence_work+=12*draws+4*rounded
        w.heap_comparisons+=3*flat_updates
        w.observation_overhead+=(self.c['oracle_cost']-1)*draws

    def ordinary(self, remaining):
        count = min(32,remaining)
        if isinstance(self.oracle,RewardBuffer):
            # Replayed draws must refund their physical price in queue order.
            obs=[self.observe(self.pair[k%2]) for k in range(count)]
            self.w.statistic_writes+=len(obs)
            return obs,self.query()

        g,idx,ev,w = self.g,self.idx,self.ev,self.w
        pair = self.pair
        leaves = (g.leaves[pair[0]],g.leaves[pair[1]])
        sample = self.oracle.sample
        log_ratio, scale = ev.log_ratio, ev.scale
        parents,root = idx.top.parent,g.root
        compact = getattr(self,'compact',None) is not None
        publish = idx.publish
        obs = []
        hops = 0
        for k in range(count):
            side=k&1
            j,leaf=pair[side],leaves[side]
            v=leaf
            while v!=root:
                v=parents[v]
                hops+=1
            reward=sample(leaf)
            if not math.isfinite(reward) or not 0<=reward<=1:
                self.book_block(k,k,hops,0,k if compact else 0)
                self.N+=1  # physical stream already advanced
                raise ValueError('Need a bounded canonical observation')
            n=ev.counts[leaf]+1
            total=ev.sums[leaf]+reward
            ev.counts[leaf],ev.sums[leaf],ev.next_count[leaf]=n,total,n+1
            radius=math.sqrt((n+1)/(2*n*n)*(log_ratio+.5*math.log1p(n)))
            mean=total/n
            lo=max(ev.lower[leaf],mean-radius,0.)
            hi=min(ev.upper[leaf],mean+radius,1.)
            ev.lower[leaf],ev.upper[leaf]=lo,hi
            if lo>hi:
                self.book_block(k+1,k,hops,0,k if compact else 0)
                ev.conflict=True
                raise ArithmeticError('empty confidence interval')
            low=max(0,math.floor(math.nextafter(scale*lo,-math.inf)))
            high=min(scale,math.ceil(math.nextafter(scale*hi,math.inf)))
            if compact:
                if not idx.lower[j]<=low<=high<=idx.upper[j]:
                    raise ValueError('non-nested')
                idx.lower[j],idx.upper[j]=low,high
            else:
                publish(j,low,high)
            obs.append((j,reward,(low,high)))
        # The reference charges one oracle, six statistic writes and sixteen
        # confidence operations per draw, plus the caller's observation list.
        self.book_block(count,count,hops,count,count if compact else 0)
        return obs,self.query()


class FastRange(PairedKernel,Search):
    def __init__(self,p,c,seed):
        super().__init__(p,c,seed,'range_lucb32')
        self.prepare_range_scan()

    def step(self,remaining):
        return self.ordinary(remaining)


class FastPartial(PairedKernel,PartialSearch):
    def __init__(self,p,c,seed,*,compact=True):
        self.use_compact=compact
        self.compact=None
        super().__init__(p,c,seed,'partial')
        self.prepare_range_scan()

    def step(self,remaining):
        if not self.ended and self.trial is None:
            self.w.query_reads+=12
            self.monitor_cost+=12
            if self.idx.q>=self.next_probe:
                self.try_launch()
        if self.trial is not None:
            return self.trial_step(remaining)
        return self.ordinary(remaining)

    def query(self):
        if self.idx.F is None or not self.use_compact:
            return super().query()
        if self.compact is None:
            self.compact=CompactFrontier(self.idx)
        a,lo,x,y=self.compact.query()
        self.w.query_reads+=2
        self.w.heap_comparisons+=1
        good=y[1] is None or y[0]<=lo+self.tol
        self.pair=x[1],y[1]
        self.point=(a,good,lo,x,y)
        return self.point


def solver(p,c,seed,method):
    if method=='range':
        return Search(p,c,seed,'range_lucb32')
    if method=='partial':
        return PartialSearch(p,c,seed,'partial')
    if method=='fast_range':
        return FastRange(p,c,seed)
    if method in ('fast_partial','batch_partial'):
        return FastPartial(p,c,seed,compact=method=='fast_partial')
    raise ValueError(method)


def scan_blocks(values,w,nodes):
    """Exact cover scan with the reference ledger, updated once per scan."""
    out=[]
    best=-1
    writes=0
    for p in nodes:
        value=values[p]
        if value>best:
            writes+=len(out)+1
            out=[p]
            best=value
        elif value==best:
            out.append(p)
            writes+=1
    w.query_reads+=len(nodes)
    w.heap_comparisons+=2*len(nodes)
    w.statistic_writes+=writes
    return out
