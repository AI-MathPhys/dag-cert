"""Exact support-aware LUCB with one reusable pair of lazy atom heaps.

Masked fixed-size indexed heaps support paid membership deletion/insertion.
Only symmetric-difference atoms move. Large moves rebuild in linear work.
"""
from collections import OrderedDict
from types import MethodType
from dag_mcts.certified_uct import UCTWork, IndexedMaxHeap
from paper.implicit_support import SupportIndex, ImplicitSearch, EMPTY
from paper.implicit_cached import cached_ranges
from paper.sampling_confidence_allcount import MixtureIntervals


def xor_ranges(left, right, work):
    """Linear merge of sorted interval endpoint streams, returning their XOR."""
    a = [x for r in left for x in r]
    b = [x for r in right for x in r]
    work.statistic_writes += len(a)+len(b)
    i = j = 0; parity = False; start = None; out = []
    while i < len(a) or j < len(b):
        x = min(a[i] if i < len(a) else float('inf'), b[j] if j < len(b) else float('inf'))
        flips = 0; work.query_reads += 4; work.heap_comparisons += 1
        if i < len(a) and a[i] == x:
            i += 1; flips += 1
        if j < len(b) and b[j] == x:
            j += 1; flips += 1
        if flips % 2:
            if parity:
                out.append((start, x)); work.statistic_writes += 1
            else:
                start = x
            parity = not parity
    assert not parity
    return tuple(out)


class ReuseIndex(SupportIndex):
    def __init__(self, graph, work, scale, cap=8):
        super().__init__(graph, work, scale, 'lazy_views', cap)
        self.active_action = None; self.active_ranges = ()
        self.membership = None; self.groups = None
        self.switches = self.moved_atoms = self.rebuilds = self.delta_atoms = 0
        work.initialization += 8

    def _build(self, rs):
        w = self.w; G = len(self.atom_keys)
        membership = [False]*G; w.initialization += G
        for lo, hi in rs:
            for k in range(lo, hi):
                membership[k] = True; w.statistic_writes += 1
        keys = [[], []]
        for k, key in enumerate(self.atom_keys):
            side = int(membership[k]); keys[side].append(key); keys[1-side].append(EMPTY)
            w.query_reads += 2; w.statistic_writes += 2
        self.membership = membership
        self.groups = [IndexedMaxHeap(xs, w) for xs in keys]
        self.rebuilds += 1; w.statistic_writes += 3

    def _change(self, a):
        w = self.w; rs = self.topology.action_ranges(a); G = len(self.atom_keys)
        if self.groups is None:
            self._build(rs)
        else:
            changes = xor_ranges(self.active_ranges, rs, w)
            D = sum(hi-lo for lo, hi in changes); w.query_reads += 2*len(changes)+2
            self.delta_atoms += D; self.switches += 1
            if D*max(1, G.bit_length()) > G:
                self._build(rs)
            else:
                for lo, hi in changes:
                    for k in range(lo, hi):
                        old = int(self.membership[k]); new = 1-old
                        self.groups[old].update(k, EMPTY)
                        self.groups[new].update(k, self.atom_keys[k])
                        self.membership[k] = bool(new); self.moved_atoms += 1
                        w.query_reads += 3; w.statistic_writes += 1
        self.active_action = a; self.active_ranges = rs; w.statistic_writes += 2

    def _maximum(self, heap):
        w = self.w
        while True:
            k = heap.top; stored = heap.keys[k]; w.query_reads += 3
            if stored == EMPTY:
                return EMPTY
            current = self.atom_keys[k]; w.query_reads += 1
            if stored == current:
                return current
            assert stored > current
            heap.update(k, current); self.repairs += 1

    def query(self):
        self.queries += 1; a, lo = self.candidate(); self.w.query_reads += 1
        if a != self.active_action:
            self._change(a)
        outside = self._maximum(self.groups[0]); inside = self._maximum(self.groups[1])
        return a, lo, inside, outside


class ReuseSearch(ImplicitSearch):
    def __init__(self, p, c, seed, method='reuse'):
        self.g = p.graph; self.work = UCTWork(); w = self.work
        w.initialization += 16*len(self.g)+10*sum(map(len, self.g.children))+4*len(self.g.leaves)
        self.index = ReuseIndex(self.g, w, c['scale'], c.get('interval_cap', 8))
        self.ev = MixtureIntervals(self.g, w, c['delta'], c['scale']); self.oracle = p.oracle(seed)
        self.tolerance = round(c['epsilon']*c['scale']); self.calls = 0; self.decision = None; self.pair = None
        t = self.index.topology; t.support_cache = OrderedDict(); t.support_entries = t.support_hits = 0
        t.action_ranges = MethodType(cached_ranges, t); w.initialization += 6
