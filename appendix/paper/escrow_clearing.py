"""Speculative threshold clearing with a paid admission scan and refundable evidence.

Range is paused at an ordinary failed query. A private confidence overlay can
seal a frontier, certify its incumbent, or release the original Range caller
with its RNG and query witnesses untouched. Buffered rewards are FIFO per leaf.
"""
from collections import deque
from copy import copy
from dataclasses import dataclass
import math

from paper.frontier_sampling import Search
from paper.uniform_selection import CountTree

METHODS = ('range32', 'old_clear32', 'guarded', 'admission_only', 'budget_only')
FIELDS = ('counts', 'sums', 'lower', 'upper', 'next_count')


class RewardBuffer:
    """Past draws are usable by the ordinary caller in original stream order."""
    def __init__(self, source, work, backlog, count):
        self.source = source
        self.work = work
        self.backlog = backlog
        self.left = count
        self.replayed = False

    def sample(self, leaf):
        # Only an aborted caller with outstanding draws pays this dispatch.
        self.work.query_reads += 2
        queue = self.backlog.get(leaf)
        self.replayed = bool(queue)
        if self.replayed:
            self.left -= 1
            return queue.popleft()
        return self.source.sample(leaf)


@dataclass
class Forecast:
    predictions: list
    high_count: int
    estimate: int


class Trial:
    def __init__(self, search, forecast):
        self.owner = search
        self.evidence = copy(search.ev)
        for name in FIELDS:
            setattr(self.evidence, name, {})
        self.latest = {}
        self.buffer = {}
        self.pred = forecast.predictions
        self.todo = [j for j, n in enumerate(self.pred) if n]
        self.total_pred = sum(self.pred)
        self.done_pred = 0
        if self.todo:
            # Start with the terminal most likely to consume the budget.
            pos = max(range(len(self.todo)), key=lambda k: self.pred[self.todo[k]])
            self.todo[pos], self.todo[-1] = self.todo[-1], self.todo[pos]
        self.current_count = self.samples = 0
        self.incumbent = search.point[0]
        self.theta = self.inside_lower = search.point[2]
        spans = search.idx.top.inside[self.incumbent]
        self.inside = []
        outside = []
        pos = 0
        for j, upper in enumerate(search.idx.upper):
            while pos < len(spans) and spans[pos][1] <= j:
                pos += 1
            inside = pos < len(spans) and spans[pos][0] <= j
            self.inside.append(inside)
            outside.append(-1 if inside else upper)
        self.high = sum(low >= self.theta for low in search.idx.lower)
        # Includes lists, interval scan, hardest-first scan, evidence overlay
        # creation and a prepayment for their disposal on every exit.
        search.w.initialization += 40 * len(outside) + 48
        self.outside = CountTree(outside, search.w)
        search.w.statistic_writes += len(self.outside.value) + len(self.outside.count)

    def draw(self):
        s = self.owner
        j = self.todo[-1]
        leaf = s.g.leaves[j]
        if leaf not in self.buffer:
            self.buffer[leaf] = deque()
            for name in FIELDS:
                getattr(self.evidence, name)[leaf] = getattr(s.ev, name)[leaf]
            s.w.statistic_writes += 12
        v = leaf
        while v != s.g.root:
            v = s.idx.top.parent[v]
            s.w.edge_reads += 1
            s.w.query_reads += 1
        reward = s.oracle.sample(leaf)
        self.buffer[leaf].append(reward)
        low, high = self.evidence.observe(leaf, reward) or (None, None)
        if self.evidence.conflict:
            raise ArithmeticError('empty confidence intersection during trial')
        self.latest[j] = (low, high)
        s.w.observation_overhead += s.c['oracle_cost'] - 1
        # Includes sparse-map accesses, FIFO append and future pop/disposal,
        # target classification, progress, witness maintenance and root test.
        s.w.query_reads += 12
        s.w.heap_comparisons += 10
        s.w.statistic_writes += 14
        self.samples += 1
        self.current_count += 1
        if self.inside[j]:
            self.inside_lower = max(self.inside_lower, low)
        else:
            self.outside.update(j, high)
        if high < self.theta or low >= self.theta:
            self.high += low >= self.theta
            self.todo.pop()
            self.done_pred += self.pred[j]
            self.current_count = 0
        return j, reward, (low, high)

    def determined(self):
        return self.outside.value[1] <= self.inside_lower + self.owner.tol

    def progress(self):
        partial = min(self.current_count, self.pred[self.todo[-1]] / 2) if self.todo else 0
        return self.done_pred + partial

    def commit(self):
        s = self.owner
        for j, interval in self.latest.items():
            leaf = s.g.leaves[j]
            for name in FIELDS:
                getattr(s.ev, name)[leaf] = getattr(self.evidence, name)[leaf]
            s.w.query_reads += 5
            s.w.statistic_writes += 5
            s.idx.publish(j, *interval)
        s.ev.evaluations = self.evidence.evaluations
        core = [j for j in reversed(range(len(s.idx.lower))) if s.idx.lower[j] >= self.theta]
        s.w.query_reads += len(s.idx.lower)
        s.w.heap_comparisons += len(s.idx.lower)
        s.w.statistic_writes += len(core) + 1
        s.idx.install(core, self.theta)
        s.N += self.samples


class GuardedSearch(Search):
    def __init__(self, problem, config, seed, policy='guarded'):
        super().__init__(problem, config, seed, 'frontier_clear32')
        self.policy = policy
        self.trial = None
        self.ended = False
        self.next_probe = 4
        self.pilot_cost = 0
        self.monitor_cost = 0
        self.campaign_start = 0
        self.budget = 0
        self.meta = dict(launch=0, seal=0, decision=0, abort_hard=0, abort_progress=0,
                         abort_dense=0, abort_cap=0, rejects=0, scans=0, phase_calls=0,
                         phase_work=0, start_N=None, start_work=None, range_credit=None,
                         estimate=None, frontier_size=0, replays=0, buffered_draws=0)
        self.w.initialization += 24

    def forecast(self):
        idx = self.idx
        theta = self.point[2] / self.c['K']
        pred = []
        high_count = 0
        # Plug-in projected radius crossing at the observed mean. This is a
        # work forecast only. Limits prevent a near-zero empirical gap blowup.
        for j, leaf in enumerate(self.g.leaves):
            count = self.ev.counts[leaf]
            if not count:
                return None
            mean = self.ev.sums[leaf] / count
            high_count += mean >= theta - self.c['epsilon']
            unresolved = idx.lower[j] < self.point[2] <= idx.upper[j]
            gap = max(abs(mean - theta) - 1 / self.c['K'], self.c['epsilon'] / 4)
            target = (self.ev.log_ratio + 0.5 * math.log1p(max(32, count))) / (2 * gap * gap)
            pred.append(max(1, math.ceil(target) - count) if unresolved else 0)
        estimate = self.setup_bound + (self.c['oracle_cost'] + 77) * sum(pred)
        return Forecast(pred, high_count, estimate)

    @property
    def setup_bound(self):
        return 96 * len(self.g.leaves) + 128

    def try_launch(self):
        M = len(self.g.leaves)
        idx = self.idx
        self.next_probe *= 2
        credit = idx.stats['fallback_work']
        scan_price = 32 * M + 32
        if (self.point[2] <= self.tol or len(idx.top.inside[self.point[0]]) < 8 or
                self.pilot_cost + scan_price > credit // 8):
            return
        # All scans pay a fixed upper price even on an early unseen leaf.
        self.w.score_evaluations += scan_price
        self.pilot_cost += scan_price
        self.meta['scans'] += 1
        forecast = self.forecast()
        if forecast is None or forecast.high_count > self.idx.cap:
            return
        common = self.w.total - self.pilot_cost - self.monitor_cost - 24
        budget = min(2 * credit, common // 3)
        if budget < self.setup_bound + self.draw_bound + 32:
            return
        if self.policy != 'budget_only' and forecast.estimate > budget:
            self.meta['rejects'] += 1
            return
        self.budget = budget
        self.campaign_start = self.w.total
        self.meta.update(launch=1, start_N=self.N, start_work=common, range_credit=credit,
                         estimate=forecast.estimate, budget=budget)
        self.trial = Trial(self, forecast)
        assert self.spent <= self.setup_bound

    @property
    def draw_bound(self):
        # dag.depth is longest-path depth, so bounds every canonical route.
        # Use stored graph size as a safe route upper bound without scanning.
        return self.c['oracle_cost'] + 2 * len(self.g) + 16 * (len(self.g.leaves)-1).bit_length() + 128

    @property
    def spent(self):
        return self.w.total - self.campaign_start

    def close(self, reason):
        t = self.trial
        self.w.statistic_writes += 8
        if reason.startswith('abort') and t.samples:
            self.oracle = RewardBuffer(self.oracle, self.w, t.buffer, t.samples)
            self.observe = self.consume_buffer
        elif reason == 'seal':
            t.commit()
            self.meta['frontier_size'] = len(self.idx.F)
        self.meta[reason] += 1
        self.meta['phase_work'] = self.spent
        self.meta['phase_calls'] = t.samples
        self.ended = True
        self.trial = None
        if reason != 'seal':
            assert self.meta['phase_work'] <= self.budget

    def consume_buffer(self, j, clearing=False):
        buffer = self.oracle
        answer = super().observe(j, clearing)
        self.meta['buffered_draws'] += 1
        if buffer.replayed:
            self.meta['replays'] += 1
            self.w.oracle_calls -= 1
            self.w.observation_overhead -= self.c['oracle_cost'] - 1
        if not buffer.left:
            self.oracle = buffer.source
            self.observe = super().observe
        return answer

    def trial_step(self, remaining):
        t = self.trial
        observations = []
        # Reserve the block check, the next draw, and close. ALL exits release
        # prepaid structures. On a seal the commit is separately measured.
        self.w.query_reads += 4
        if (self.policy != 'admission_only' and t.samples >= 64 and t.todo and
                (4 * self.spent - self.budget) * t.total_pred > 3 * self.budget * t.progress()):
            self.close('abort_progress')
            return observations, self.point
        for _ in range(min(32, remaining)):
            if not t.todo:
                break
            if self.spent + self.draw_bound + 24 > self.budget:
                self.close('abort_hard')
                return observations, self.point
            before = self.w.total
            observations.append(t.draw())
            assert self.w.total - before <= self.draw_bound
            if t.determined():
                candidate = t.incumbent
                point = (candidate, True, t.inside_lower, None, None)
                self.close('decision')
                self.point = point
                return observations, point
            if t.high > self.idx.cap:
                self.close('abort_dense')
                return observations, self.point
        if not t.todo:
            self.close('seal')
            return observations, self.query()
        return observations, self.point

    def step(self, remaining):
        if not self.ended and self.trial is None:
            # Fixed charge covers scheduling, credit lookup, admission guards.
            self.w.query_reads += 12
            self.monitor_cost += 12
            if self.idx.q >= self.next_probe:
                self.try_launch()
        if self.trial is not None:
            return self.trial_step(remaining)
        pair = self.pair
        obs = [self.observe(pair[k % 2]) for k in range(min(32, remaining))]
        self.w.statistic_writes += len(obs)
        return obs, self.query()
