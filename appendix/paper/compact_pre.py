"""Miss-only receipts for the original Compact controller, with a shared repair kernel."""
from typing import NamedTuple

from paper.compact_partial import FastRange
from paper.compact_side import MIN_COVER, MIN_SEALED_SIDE, SideAccount, SealedSides
from paper.frontier_gate_race import AuditedCompact
from paper.uniform_selection import CountTree


class FusedTree(CountTree):
    """Run the same pull loop, posting its exact counters once per publication."""
    @classmethod
    def from_tree(cls, tree):
        result = cls.__new__(cls)
        result.w, result.n, result.size = tree.w, tree.n, tree.size
        result.value, result.count = tree.value, tree.count
        return result

    def update(self, i, value):
        values, counts, w = self.value, self.count, self.w
        node = self.size + i
        w.query_reads += 1
        if values[node] == value:
            return
        values[node], counts[node] = value, int(value >= 0)
        node //= 2
        pulls = 0
        while node:
            left = 2*node
            right = left+1
            a,b = values[left],values[right]
            if a>b:
                high, ties = a,counts[left]
            elif a<b:
                high, ties = b,counts[right]
            else:
                high, ties = a,counts[left]+counts[right]
            pulls += 1
            if high==values[node] and ties==counts[node]:
                break
            values[node],counts[node] = high,ties
            node //= 2
        # Includes the final unchanged parent and its logical writes.
        w.query_reads += 6*pulls
        w.heap_comparisons += 4*pulls
        w.heap_writes += 2+2*pulls


class MissReceipt(NamedTuple):
    winners: tuple
    blockers: tuple
    lengths: tuple
    writes: tuple
    reads_both: int
    writes_both: int
    bill_both: int


class MissSides:
    """Only blocks ending in a range miss can have changed the upper revision."""
    def __init__(self, idx, account):
        self.idx = idx
        self.account = account
        self.pair = None
        self.age = 0
        self.records = {}

    @staticmethod
    def contains(block, leaf):
        return leaf >> (leaf.bit_length()-block.bit_length()) == block

    def ranged(self, action):
        idx,account = self.idx,self.account
        outside,inside = idx.cover(action)
        # idx.witnesses still holds the preceding public query's pair.
        pair = idx.witnesses
        if pair is not None and pair[0] is not None and pair[1] is not None:
            if pair[0]>pair[1]:
                pair = pair[1],pair[0]
        else:
            pair = None
        account.extra += 8
        # Every intervening memo hit saw the last miss's revision. Otherwise
        # no candidate could have cached that newer revision yet. Any fresh
        # publication is therefore confined to the pair just observed.
        if pair==self.pair:
            self.age += 1
        else:
            if self.records:
                self.records.clear()
            self.pair, self.age = pair,1
        maxima = idx.maxima
        if self.age<3 or pair is None:
            return maxima(outside),maxima(inside)
        record = self.records.get(action)
        w = idx.w
        if record is not None:
            values = idx.ut.value
            wins = record.winners
            ok_out = values[wins[0][0]] > record.blockers[0]
            ok_in = values[wins[1][0]] > record.blockers[1]
            account.extra += 14
            if ok_out and ok_in:
                w.query_reads += record.reads_both
                w.heap_comparisons += 2*record.reads_both
                w.statistic_writes += record.writes_both
                account.saved += record.bill_both
                account.pre_saved += record.bill_both
                account.pre_hits += 2
                return wins
            if not ok_out and not ok_in:
                return maxima(outside),maxima(inside)
            i = 0 if ok_out else 1
            n, writes = record.lengths[i], record.writes[i]
            w.query_reads += n
            w.heap_comparisons += 2*n
            w.statistic_writes += writes
            skipped = 3*n+writes
            account.saved += skipped
            account.pre_saved += skipped
            account.pre_hits += 1
            if ok_out:
                return wins[0],maxima(inside)
            return maxima(outside),wins[1]

        n0,n1 = len(outside),len(inside)
        account.extra += 6
        price = 4*(n0+n1)+40
        if min(n0,n1)<MIN_COVER or account.build_work+price>idx.stats['fallback_work']//16:
            return maxima(outside),maxima(inside)
        old = w.statistic_writes
        out = maxima(outside)
        mid = w.statistic_writes
        inn = maxima(inside)
        winners = out,inn
        if len(out)!=1 or len(inn)!=1:
            return winners
        x,y = idx.ut.size+pair[0],idx.ut.size+pair[1]
        p,q = out[0],inn[0]
        account.extra += 10
        if not ((self.contains(p,x) and self.contains(q,y)) or
                (self.contains(p,y) and self.contains(q,x))):
            return winners
        values = idx.ut.value
        blockers = (max((values[j] for j in outside if j!=p),default=-1),
                    max((values[j] for j in inside if j!=q),default=-1))
        writes = w.statistic_writes-old
        self.records[action]=MissReceipt(winners,blockers,(n0,n1),(mid-old,w.statistic_writes-mid),
                                         n0+n1,writes,3*(n0+n1)+writes)
        account.extra += price
        account.build_work += price
        account.purchases += 1
        return winners


def configure(search, receipts, fused):
    search.account=SideAccount()
    idx=search.idx
    if fused:
        idx.ut,idx.lt=FusedTree.from_tree(idx.ut),FusedTree.from_tree(idx.lt)
        search.account.extra+=24  # two handles, reusing the existing arrays
    if receipts:
        search.miss_sides=MissSides(idx,search.account)
        idx.ranged=search.miss_sides.ranged


class FastPreCompact(AuditedCompact):
    def __init__(self,p,c,seed,receipts=True,fused=True):
        super().__init__(p,c,seed)
        configure(self,receipts,fused)
        self.side_enabled=receipts

    def close(self, reason):
        super().close(reason)
        if reason=='seal' and self.side_enabled and len(self.idx.F)>=MIN_SEALED_SIDE:
            # No per-query wrapper. Activate after the private bill has closed.
            self.compact=SealedSides(self.idx,self.account)


class FastPreRange(FastRange):
    def __init__(self,p,c,seed,receipts=True,fused=True):
        super().__init__(p,c,seed)
        configure(self,receipts,fused)

