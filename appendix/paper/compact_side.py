"""Exact per-side reuse for Compact's cost-sensitive sampler and for range LUCB."""
from dataclasses import dataclass

from paper.compact_partial import CompactFrontier, FastRange
from paper.frontier_gate_race import AuditedCompact

MIN_COVER = 8
MIN_SEALED_SIDE = 4


@dataclass
class Receipt:
    node: int
    blocker: int
    writes: int


class SideAccount:
    """Keep physical overhead separate from the sampler's original logical bill."""
    def __init__(self):
        self.extra = 24
        self.saved = 0
        self.purchases = 0
        self.pre_hits = 0
        self.post_hits = 0
        self.pre_saved = 0
        self.post_saved = 0
        self.build_work = 0


class CoverSides:
    """A receipt is valid only while the same unordered witness pair is updated."""
    def __init__(self, idx, account):
        self.idx = idx
        self.account = account
        self.pair = None
        self.age = 0
        self.records = {}

    def query_boundary(self, pair):
        self.account.extra += 6
        if pair is None or None in pair:
            pair = None
        elif pair[0] > pair[1]:
            pair = (pair[1],pair[0])
        if pair == self.pair:
            self.age += 1
        else:
            self.pair, self.age = pair, 1
            self.records.clear()  # entry disposal is prepaid at insertion

    def contains(self, node, terminal):
        leaf = self.idx.ut.size + terminal
        return leaf >> (leaf.bit_length()-node.bit_length()) == node

    def ranged(self, action):
        idx, account = self.idx, self.account
        covers = idx.cover(action)
        account.extra += 4
        if self.age < 3 or self.pair is None:
            return tuple(idx.maxima(ns) for ns in covers)
        record = self.records.get(action)
        if record is not None:
            winners = []
            for ns, receipt in zip(covers,record):
                account.extra += 7
                if receipt is not None and idx.ut.value[receipt.node] > receipt.blocker:
                    # All other cover values are unchanged. Replay the exact
                    # reads, comparisons and writes of the avoided cover scan.
                    idx.w.query_reads += len(ns)
                    idx.w.heap_comparisons += 2*len(ns)
                    idx.w.statistic_writes += receipt.writes
                    saved = 3*len(ns)+receipt.writes
                    account.saved += saved
                    account.pre_saved += saved
                    account.pre_hits += 1
                    winners.append([receipt.node])
                else:
                    winners.append(idx.maxima(ns))
            return tuple(winners)
        prices = []
        winners = []
        for ns in covers:
            writes = idx.w.statistic_writes
            winners.append(idx.maxima(ns))
            prices.append(idx.w.statistic_writes-writes)
        account.extra += 10
        if min(map(len,covers))<MIN_COVER or any(len(ns)!=1 for ns in winners):
            return tuple(winners)
        w0, w1 = (ns[0] for ns in winners)
        x, y = self.pair
        # Disjoint opposite-side blocks. If each contains one hot terminal,
        # no other block in either cover can change in this epoch.
        if not ((self.contains(w0,x) and self.contains(w1,y)) or
                (self.contains(w0,y) and self.contains(w1,x))):
            return tuple(winners)
        price = 4*sum(map(len,covers))+40
        if account.build_work+price > idx.stats['fallback_work']//16:
            return tuple(winners)
        account.extra += price
        account.build_work += price
        account.purchases += 1
        record = []
        for ns,win,writes in zip(covers,winners,prices):
            node = win[0]
            blocker = max((idx.ut.value[p] for p in ns if p!=node),default=-1)
            record.append(Receipt(node,blocker,writes))
        self.records[action] = record
        return tuple(winners)


class SealedSides(CompactFrontier):
    """The lower candidate remains unchanged. Reuse a strict upper winner per side."""
    def __init__(self, idx, account):
        super().__init__(idx)
        self.account = account
        self.cache = {}  # side lists are owned throughout by CompactFrontier.parts
        account.extra += 8

    def maximum(self, keys, members):
        self.account.extra += 2
        if keys is self.idx.lower or len(members)<MIN_SEALED_SIDE:
            return super().maximum(keys,members)
        account = self.account
        key = id(members)
        account.extra += 6
        receipt = self.cache.get(key)
        if receipt is not None:
            winner, blocker = receipt
            if keys[winner] > blocker:
                saved = 5*len(members)+1
                self.idx.w.query_reads += len(members)
                self.idx.w.heap_comparisons += 2*len(members)
                self.idx.w.statistic_writes += 2*len(members)+1
                account.saved += saved
                account.post_saved += saved
                account.post_hits += 1
                return keys[winner], [winner]
        value,ties = super().maximum(keys,members)
        if len(ties)==1:
            winner = ties[0]
            # On a failed receipt do not rebuild at every use of a crowded side.
            if receipt is None or receipt[0]!=winner:
                account.extra += 4*len(members)+10
                blocker = max((keys[j] for j in members if j!=winner),default=-1)
                self.cache[key] = (winner,blocker)
        return value,ties


class SideCompact(AuditedCompact):
    def __init__(self, problem, config, seed, mode):
        super().__init__(problem,config,seed)
        self.account = SideAccount()
        self.pre = CoverSides(self.idx,self.account) if mode in ('both','pre') else None
        self.use_post = mode in ('both','post')
        if self.pre is not None:
            self.idx.ranged = self.pre.ranged

    def query(self):
        self.account.extra += 2
        if self.idx.F is None:
            if self.pre is not None:
                self.pre.query_boundary(getattr(self,'pair',None))
        elif self.compact is None and self.use_post and len(self.idx.F)>=MIN_SEALED_SIDE:
            self.compact = SealedSides(self.idx,self.account)
        return super().query()


class SideRange(FastRange):
    def __init__(self, problem, config, seed):
        super().__init__(problem,config,seed)
        self.account = SideAccount()
        self.pre = CoverSides(self.idx,self.account)
        self.idx.ranged = self.pre.ranged

    def query(self):
        self.pre.query_boundary(getattr(self,'pair',None))
        return super().query()

