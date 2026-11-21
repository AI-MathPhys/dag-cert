"""Branch-equivalent repair pricing and cheaper alternative Compact policies."""
from paper.batched_repair import BatchTree, BatchedCompact
from paper.partial_clearing import PartialTrial
from paper.repair_policy_clock import PolicyCompact, PhysicalCompact, ClockLane


class BareCompact(PhysicalCompact):
    def __init__(self, problem, cfg, seed):
        super().__init__(problem, cfg, seed)
        self.can_clear = False   # disables reconstruction, not the structural launch test


class CreditCompact(BareCompact):
    def try_launch(self):
        super().try_launch()
        if self.trial is not None:
            self.budget = 2 * self.idx.stats['fallback_work']
            self.meta['budget'] = self.budget
            self.w.query_reads += 2
            self.w.statistic_writes += 1


class RepairBounds:
    """The logical work counter books the lower endpoint of each group."""
    def __init__(self, account):
        self.account = account
        self.pending = []
        self.correction = self.width = 0
        self.base = self.cap = 0
        self.account.extra += 12
        for name in ('deferred_groups','refinements','branch_checks','peak_pending'):
            setattr(account,name,0)

    def defer(self, profile, side, start, events, low, high):
        n = len(events)
        width = (high-low)*n
        self.pending.append((profile,side,start,tuple(events),low*n,width))
        self.width += 12*width
        self.account.extra += 32+3*n+4*profile.h   # includes release of a stale profile
        self.account.deferred_groups += 1
        self.account.peak_pending = max(self.account.peak_pending,len(self.pending))

    def refine(self):
        profile,side,pos,events,lower,width = self.pending.pop()
        pulls = charge = 0
        for x,peer in events:
            pos,cold,price = profile.lookup(side,x,pos)
            pulls += profile.depth(cold,peer,x)
            charge += price+5
        assert lower <= pulls <= lower+width
        self.correction += 12*(pulls-lower)
        self.width -= 12*width
        self.account.refinements += 1
        self.account.extra += 12+charge

    def interval(self):
        lower = self.base+self.correction
        return min(self.cap,lower//3), min(self.cap,(lower+self.width)//3)

    def decide(self, predicate):
        self.account.branch_checks += 1
        while True:
            lo,hi = self.interval()
            self.account.extra += 8
            left = predicate(lo)
            if lo==hi or left==predicate(hi):
                return left
            self.refine()


class ThresholdTree(BatchTree):
    def price_group(self, side, events, peer_old, peer_new):
        if len(events)<4:
            return super().price_group(side,events,peer_old,peer_new)
        profile = self.profile
        pos = profile.cursor[side]
        first,last = events[0][0],events[-1][0]
        mid,a,c0 = profile.lookup(side,first,pos)
        end,b,c1 = profile.lookup(side,last,mid)
        profile.cursor[side] = end
        low = profile.depth(min(a,b),max(peer_old,peer_new),min(first,last))
        high = profile.depth(max(a,b),min(peer_old,peer_new),max(first,last))
        if low != high:
            self.bounds.defer(profile,side,pos,events,low,high)
        return low*len(events), c0+c1+14


class ThresholdCompact(BatchedCompact):
    def __init__(self,p,c,seed):
        super().__init__(p,c,seed)
        self.bounds = RepairBounds(self.account)
        if self.can_clear:
            for name,inc in (('lt',True),('ut',False)):
                tree = ThresholdTree.from_index(getattr(self.idx,name),inc,self.account)
                tree.bounds = self.bounds
                setattr(self.idx,name,tree)
                self.account.extra += 24

    def try_launch(self):
        idx = self.idx
        self.next_probe *= 2
        credit = idx.stats['fallback_work']
        scan_price = 68*len(self.g.leaves)+96
        self.account.extra += 6
        if (self.point[2]<=self.tol or len(idx.top.inside[self.point[0]])<8
                or self.pilot_cost+scan_price>credit//8):
            return
        self.w.score_evaluations += scan_price
        self.pilot_cost += scan_price
        self.meta['scans'] += 1
        plan = self.plan()
        if plan is None:
            return
        b = self.bounds
        b.base = self.w.total-self.pilot_cost-self.monitor_cost-24
        b.cap = 2*credit
        floor = self.setup_bound+self.draw_bound+48
        if not b.decide(lambda v: v>=floor):
            return
        if plan.partial_estimate>plan.earnings or not b.decide(lambda v: v>=plan.partial_estimate):
            self.meta['rejects'] += 1
            return
        lo,hi = b.interval()
        self.exact_budget = lo==hi
        self.budget = hi   # upper bound for the inherited close assertion
        self.campaign_start = self.w.total
        self.meta.update(launch=1,start_N=self.N,range_credit=credit,estimate=plan.partial_estimate,
                         full_estimate=plan.full_estimate,earnings=plan.earnings,
                         allowance_bounds=(lo,hi),deferred=len(plan.deferred),parks=0,salvage=0)
        self.trial = PartialTrial(self,plan)
        assert self.spent<=self.setup_bound

    def trial_step(self, remaining):
        if self.exact_budget:
            return super().trial_step(remaining)
        b = self.bounds
        lo,hi = b.interval()
        if lo==hi:
            self.exact_budget = True
            self.budget = lo
            return super().trial_step(remaining)
        # Match PartialSearch's phases. Every budget read is a monotone predicate.
        t = self.trial
        obs = []
        self.w.query_reads += 26
        if t.high+len(t.retained)>self.idx.cap:
            self.close('abort_dense')
            return obs,self.point
        s = self.spent
        slow = t.samples>=64 and t.todo and b.decide(
            lambda v: (4*s-v)*t.total_pred>3*v*t.progress())
        if slow and t.possible_size<=self.idx.cap:
            return obs,self.frontier_or_abort('abort_progress')
        if (t.high+len(t.retained)<self.idx.cap and t.pending_is_expensive()
                and b.decide(lambda v: s+14<=v)):
            t.park_pending()
            self.meta['parks'] += 1
        elif slow:
            return obs,self.frontier_or_abort('abort_progress')
        for _ in range(min(32,remaining)):
            if not t.todo:
                break
            minimum = self.spent+self.draw_bound+40
            if not b.decide(lambda v: v>=minimum):
                return obs,self.frontier_or_abort('abort_hard')
            before = self.w.total
            obs.append(t.draw())
            assert self.w.total-before<=self.draw_bound
            if t.determined():
                point = t.incumbent,True,t.inside_lower,None,None
                self.close('decision')
                self.point = point
                return obs,point
            if t.high+len(t.retained)>self.idx.cap:
                self.close('abort_dense')
                return obs,self.point
        if not t.todo:
            self.close('seal')
            return obs,self.query()
        return obs,self.point

    def close(self, reason):
        super().close(reason)
        # Release charges are prepaid in defer. No future probe after this trial.
        self.bounds.pending.clear()


ENGINES = dict(reference=PolicyCompact,physical=PhysicalCompact,bare=BareCompact,
               credit=CreditCompact,threshold=ThresholdCompact)


class DecisionLane(ClockLane):
    def __init__(self,problem,cfg,seed,method):
        self.engine = ENGINES[method](problem,cfg,seed)
        self.oracle = self.engine.oracle
        self.account = self.engine.account
        self.point = self.engine.query()
        self.peak = 0
        self.seal_at = None
        self.conflict = False
