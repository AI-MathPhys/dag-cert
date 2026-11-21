"""Exact pricing with the moving-peer envelope and immediate fallback on ambiguity."""
from paper.batched_repair import BatchTree
from paper.repair_policy_clock import PolicyCompact


class ImmediateTree(BatchTree):
    def price_group(self, side, events, peer_old, peer_new):
        if len(events) < 4:
            return super().price_group(side, events, peer_old, peer_new)
        profile = self.profile
        start = profile.cursor[side]
        first, last = events[0][0], events[-1][0]
        middle, a, first_cost = profile.lookup(side, first, start)
        end, b, last_cost = profile.lookup(side, last, middle)
        profile.cursor[side] = end
        low = profile.depth(min(a, b), max(peer_old, peer_new), min(first, last))
        high = profile.depth(max(a, b), min(peer_old, peer_new), max(first, last))
        charge = first_cost + last_cost + 14
        if low == high:
            return len(events) * low, charge
        pos = start
        pulls = 0
        for key, peer in events:
            pos, cold, cost = profile.lookup(side, key, pos)
            pulls += profile.depth(cold, peer, key)
            charge += cost + 5
        return pulls, charge


class ImmediateCompact(PolicyCompact):
    def prepare_batch(self, compact):
        # Install each index once, for the same setup tariff as the full-price reference.
        idx = self.idx
        idx.lt = ImmediateTree.from_index(idx.lt, True, self.account)
        idx.ut = ImmediateTree.from_index(idx.ut, False, self.account)
        self.can_clear = compact and any(len(side) >= 8 for side in idx.top.inside)
        self.batch_open = False
        self.account.extra += 32 + (2 * len(idx.top.inside) + 4 if compact else 0)
        self.account.batch_blocks = 0
        self.account.priced_blocks = 0
