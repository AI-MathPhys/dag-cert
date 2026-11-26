"""Paid interval merging and max/count tournament tree utilities for graph certification."""
from __future__ import annotations

from functools import cmp_to_key


def merge(xs, w):
    """Merge sorted half-open leaf intervals while charging comparison/write work."""
    def cmp(a, b):
        w.heap_comparisons += 1
        return (a > b) - (a < b)

    out = []
    for lo, hi in sorted(xs, key=cmp_to_key(cmp)):
        w.query_reads += 2
        w.statistic_writes += 1
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(hi, out[-1][1]))
            w.heap_comparisons += 2
        else:
            out.append((lo, hi))
            w.heap_comparisons += 1
    return tuple(out)


class CountTree:
    """Charged max/count tournament tree over leaf rank intervals."""

    def __init__(self, values, w):
        self.w = w
        self.n = len(values)
        self.size = 1 << (self.n - 1).bit_length()
        self.value = [-1] * (2 * self.size)
        self.count = [0] * (2 * self.size)
        w.initialization += 4 * self.size + 3
        for i, v in enumerate(values):
            self.value[self.size + i] = v
            self.count[self.size + i] = int(v >= 0)
            w.statistic_writes += 2
        for p in range(self.size - 1, 0, -1):
            self._pull(p)

    def _pull(self, p):
        v = self.value
        c = self.count
        l = 2 * p
        r = l + 1
        m = max(v[l], v[r])
        n = (c[l] if v[l] == m else 0) + (c[r] if v[r] == m else 0)
        self.w.query_reads += 6
        self.w.heap_comparisons += 4
        changed = m != v[p] or n != c[p]
        v[p] = m
        c[p] = n
        self.w.heap_writes += 2
        return changed

    def update(self, i, v):
        p = self.size + i
        self.w.query_reads += 1
        if self.value[p] == v:
            return
        self.value[p] = v
        self.count[p] = int(v >= 0)
        self.w.heap_writes += 2
        p //= 2
        while p:
            if not self._pull(p):
                break
            p //= 2

    def cover(self, ranges):
        out = []
        for a, b in reversed(ranges):
            left = []
            right = []
            a += self.size
            b += self.size
            self.w.query_reads += 2
            while a < b:
                self.w.query_reads += 2
                self.w.heap_comparisons += 2
                if a & 1:
                    left.append(a)
                    a += 1
                    self.w.statistic_writes += 1
                if b & 1:
                    b -= 1
                    right.append(b)
                    self.w.statistic_writes += 1
                a //= 2
                b //= 2
            out.extend(right)
            out.extend(reversed(left))
            self.w.statistic_writes += len(left) + len(right)
        return out

    def select(self, nodes, rng=None, rank=None):
        maximum = -1
        total = 0
        w = self.w
        for p in nodes:
            v = self.value[p]
            w.query_reads += 2
            w.heap_comparisons += 2
            if v > maximum:
                maximum = v
                total = self.count[p]
            elif v == maximum:
                total += self.count[p]
        if total == 0:
            return -1, None
        k = rng.randrange(total) if rank is None else rank
        w.score_evaluations += int(rank is None)
        if not 0 <= k < total:
            raise IndexError(k)
        for p in nodes:
            w.query_reads += 2
            w.heap_comparisons += 2
            if self.value[p] != maximum:
                continue
            if k >= self.count[p]:
                k -= self.count[p]
                continue
            while p < self.size:
                r = 2 * p + 1
                n = self.count[r] if self.value[r] == maximum else 0
                w.query_reads += 2
                w.heap_comparisons += 2
                if k < n:
                    p = r
                else:
                    k -= n
                    p = r - 1
            return maximum, p - self.size
        raise AssertionError("bad max/count tree")
