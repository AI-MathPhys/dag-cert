"""Paid, irrevocable route selection from the ordinary prefix of Compact."""
from statistics import median
from paper.credit_admission import CreditAtAdmission
from paper.decision_price import BareCompact, DecisionLane


class RoutedLane(DecisionLane):
    @property
    def work(self):
        # The admission rules see their original meters. Selector work is
        # charged to the same external budget and cannot finance a trial.
        return super().work + getattr(self.account, 'selector_work', 0)


class PrefixCompact(BareCompact):
    def __init__(self, problem, cfg, seed):
        super().__init__(problem,cfg,seed)
        self.route=None
        self.account.selector_work=12
        self.meta.update(prefix_route=None,prefix_reason=None,inspected=0,probe_draws=None)

    def lock(self,route,reason):
        assert self.route is None and self.trial is None
        self.route=route
        self.meta.update(prefix_route=route,prefix_reason=reason)
        self.account.selector_work+=8

    def ordinary(self,remaining):
        obs,result=super().ordinary(remaining)
        self.account.selector_work+=2
        if self.route is None:
            self.inspect(obs)
        return obs,result

    def try_launch(self):
        self.account.selector_work+=4
        if self.meta['probe_draws'] is None:
            self.meta['probe_draws']=self.w.oracle_calls
            if self.route is None:
                self.finish_prefix()
        if self.route=='credit-all':
            CreditAtAdmission.try_launch(self)
        else:
            BareCompact.try_launch(self)


class KnownRangeSelector(PrefixCompact):
    def inspect(self,obs):
        for _,reward,_ in obs:
            self.meta['inspected']+=1
            # One read, four comparisons, loop/counter and branching.
            self.account.selector_work+=8
            if .10<=reward<.14:
                self.lock('credit-all','low-exclusive')
                break
            if .30<reward<=.34:
                self.lock('bare','high-exclusive')
                break

    def finish_prefix(self):
        self.lock('bare','fallback')


class OnlineSelector(PrefixCompact):
    def __init__(self,p,c,seed):
        super().__init__(p,c,seed)
        self.sampled={}
        self.account.selector_work+=4

    def inspect(self,obs):
        for leaf,reward,_ in obs:
            count,total=self.sampled.get(leaf,(0,0.))
            self.sampled[leaf]=(count+1,total+reward)
            self.meta['inspected']+=1
            self.account.selector_work+=12  # reads, lookup, arithmetic and writes

    def finish_prefix(self):
        estimates=[total/n for n,total in self.sampled.values() if n>=4]
        k=len(estimates)
        self.account.selector_work+=8+8*len(self.sampled)+3*k*k.bit_length()
        self.sampled.clear()
        if k<4:
            self.lock('bare','fallback')
            return
        score=median(estimates)
        self.meta['prefix_score']=score
        self.lock('credit-all' if score<=.22 else 'bare','median')
