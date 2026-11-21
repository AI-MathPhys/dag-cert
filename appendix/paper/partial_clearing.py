"""Budgeted partial-frontier clearing on shared all-MAX terminal evidence."""
from dataclasses import dataclass
from heapq import nlargest
import math

from paper.escrow_clearing import GuardedSearch, Trial, FIELDS


@dataclass
class PartialPlan:
    predictions: list
    deferred: tuple
    high_count: int
    full_estimate: int
    partial_estimate: int
    earnings: float
    holding_price: float


class PartialTrial(Trial):
    """A retained terminal needs no statistical classification."""
    def __init__(self, search, plan):
        super().__init__(search, plan)
        self.retained = set(plan.deferred)
        self.holding_price = plan.holding_price
        self.todo = [j for j in self.todo if j not in self.retained]
        self.total_pred = sum(self.pred[j] for j in self.todo)
        search.w.initialization += 8 * len(self.pred) + 24

    @property
    def possible_size(self):
        # Undecided, already high, and retained are disjoint.
        return self.high + len(self.todo) + len(self.retained)

    def park_pending(self):
        j = self.todo.pop()
        self.retained.add(j)
        self.done_pred += self.pred[j]
        self.current_count = 0
        self.owner.w.statistic_writes += 6

    def pending_is_expensive(self):
        """Reprice the pending leaf after at least one block of local data."""
        if not self.todo or self.current_count < 32:
            return False
        s = self.owner
        leaf = s.g.leaves[self.todo[-1]]
        n = self.evidence.counts[leaf]
        mean = self.evidence.sums[leaf] / n
        gap = max(abs(mean-self.theta/s.c['K'])-1/s.c['K'], s.c['epsilon']/4)
        target = math.ceil((self.evidence.log_ratio+.5*math.log1p(n))/(2*gap*gap))
        return (target-n)*(s.c['oracle_cost']+77) > self.holding_price

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
        # Include *every* upper endpoint at/above the anchor, even when the
        # lower endpoint still lies below it. Descending order couples ties.
        core = [j for j in reversed(range(len(s.idx.upper))) if s.idx.upper[j] >= self.theta]
        s.w.query_reads += len(s.idx.upper)
        s.w.heap_comparisons += len(s.idx.upper)
        s.w.statistic_writes += len(core) + 1
        assert len(core) == self.possible_size and len(core) <= s.idx.cap
        s.idx.install(core, self.theta)
        s.N += self.samples


class PartialSearch(GuardedSearch):
    """One paid trial. Both ablations keep the same ledger and hard limit."""
    @property
    def setup_bound(self):
        return 104 * len(self.g.leaves) + 152

    def plan(self):
        base = super().forecast()
        if base is None or base.high_count > self.idx.cap:
            return None
        a, _, anchor, _, _ = self.point
        price = self.c['oracle_cost'] + 77
        eps = self.c['epsilon']
        # Project precision-limited incumbent/rival pulls. The comparison is
        # a forecast and never participates in the statistical decision.
        precision_count = math.ceil(2 * (self.ev.log_ratio + .5 * math.log1p(1/eps**2)) / eps**2)
        future_pulls = sum(max(0, precision_count - self.ev.counts[x]) for x in self.g.leaves
                           if self.ev.sums[x] / self.ev.counts[x] >= anchor/self.c['K'] - eps)
        misses = future_pulls / 32 * self.idx.stats['misses'] / self.idx.q
        membership = 16 + 2 * len(self.idx.top.inside[a]).bit_length()
        hold = misses * membership
        known_high = sum(low >= anchor for low in self.idx.lower)
        # Never borrow slots already needed by verified high terminals.
        slots = max(0,min(4,self.idx.cap-known_high))
        choices = nlargest(slots, ((n,-j) for j,n in enumerate(base.predictions)
                                    if n and n*price > hold))
        deferred = tuple(-neg_j for n,neg_j in choices)
        residual = sum(base.predictions) - sum(n for n,_ in choices)
        members = min(self.idx.cap, max(known_high,base.high_count) + len(deferred))
        covers = self.idx.covers.get(a)
        blocks = 0 if covers is None else sum(map(len,covers))
        earnings = misses * max(0,4*blocks-membership*members)
        return PartialPlan(base.predictions, deferred, base.high_count,
                           base.estimate, self.setup_bound+price*residual, earnings, hold)

    def try_launch(self):
        idx = self.idx
        self.next_probe *= 2
        credit = idx.stats['fallback_work']
        # Fixed tariff covers both linear passes, the top-four selection and
        # forecast arithmetic; even an early failed scan pays it in full.
        scan_price = 68 * len(self.g.leaves) + 96
        if (self.point[2] <= self.tol or len(idx.top.inside[self.point[0]]) < 8 or
                self.pilot_cost + scan_price > credit // 8):
            return
        self.w.score_evaluations += scan_price
        self.pilot_cost += scan_price
        self.meta['scans'] += 1
        plan = self.plan()
        if plan is None:
            return
        common = self.w.total - self.pilot_cost - self.monitor_cost - 24
        budget = min(2*credit,common//3)
        if budget < self.setup_bound + self.draw_bound + 48:
            return
        if self.policy == 'full_price':
            admit = plan.full_estimate <= budget
        else:
            admit = plan.partial_estimate <= min(budget,plan.earnings)
        if not admit:
            self.meta['rejects'] += 1
            return
        self.budget = budget
        self.campaign_start = self.w.total
        self.meta.update(launch=1, start_N=self.N, start_work=common, range_credit=credit,
                         estimate=plan.partial_estimate, full_estimate=plan.full_estimate,
                         earnings=plan.earnings, budget=budget, deferred=len(plan.deferred),
                         parks=0, salvage=0)
        self.trial = PartialTrial(self,plan)
        assert self.spent <= self.setup_bound

    def frontier_or_abort(self, reason):
        t = self.trial
        if self.policy != 'plain_abort' and t.possible_size <= self.idx.cap:
            self.meta['salvage'] += 1
            self.close('seal')
            return self.query()
        self.close(reason)
        return self.point

    def trial_step(self, remaining):
        t = self.trial
        obs = []
        self.w.query_reads += 26  # includes the local reforecast and all review tests
        if t.high + len(t.retained) > self.idx.cap:
            self.close('abort_dense')
            return obs,self.point
        slow = (t.samples >= 64 and t.todo and
                (4*self.spent-self.budget)*t.total_pred > 3*self.budget*t.progress())
        if slow and t.possible_size <= self.idx.cap:
            return obs,self.frontier_or_abort('abort_progress')
        can_park = (self.policy != 'plain_abort' and t.high+len(t.retained)<self.idx.cap and
                    t.pending_is_expensive() and self.spent+14 <= self.budget)
        if can_park:
            t.park_pending()
            self.meta['parks'] += 1
        elif slow:
            return obs,self.frontier_or_abort('abort_progress')
        for _ in range(min(32,remaining)):
            if not t.todo:
                break
            if self.spent+self.draw_bound+40 > self.budget:
                return obs,self.frontier_or_abort('abort_hard')
            before = self.w.total
            obs.append(t.draw())
            assert self.w.total-before <= self.draw_bound
            if t.determined():
                point = (t.incumbent,True,t.inside_lower,None,None)
                self.close('decision')
                self.point = point
                return obs,point
            if t.high+len(t.retained) > self.idx.cap:
                self.close('abort_dense')
                return obs,self.point
        if not t.todo:
            self.close('seal')
            return obs,self.query()
        return obs,self.point
