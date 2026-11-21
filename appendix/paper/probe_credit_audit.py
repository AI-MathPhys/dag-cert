"""Sweep and first-probe witnesses. Counterfactual scans never enter either bill."""
from unittest.mock import patch

from paper.decision_price import ThresholdCompact, RepairBounds
from paper.neighbor_price_condition import predict


def exception_floor(bound,graph):
    # If 512 clips on every path, uncertainty can cause losses only on the
    # first probe's groups or trial. Every later hot group has 16 changes.
    z = bound.z
    bound.loss_bound()
    exact_later = predict(graph,bound.cfg)['clip'][-1]>=0
    if not exact_later:
        return bound.loss_bound()
    p=bound.probes[0]
    groups=4*(p-1)-bound.m+2
    max_credit=z['cover_fee']+(5*z['kmax']+1)*p
    draws=(2*max_credit+35)//36+1
    checks=draws+3*((draws+31)//32+2)+6
    return groups*(32+48+4*z['height']+20)+8*checks+124


def audit(graph,bound,rng,*,early=True):
    e=ThresholdCompact(graph,bound.cfg,1)
    e.idx.rng=rng
    e.query()
    original_defer=RepairBounds.defer
    original_refine=RepairBounds.refine
    original_probe=ThresholdCompact.try_launch
    balance=0
    refined=0
    witness=None
    probes=[]
    def keep(bounds,profile,side,start,events,low,high):
        nonlocal balance
        pos=start
        price=0
        for threshold,_ in events:
            pos,_,fee=profile.lookup(side,threshold,pos)
            price+=fee+5
        balance+=price-(32+3*len(events)+4*profile.h)
        original_defer(bounds,profile,side,start,events,low,high)
    def refine(bounds):
        nonlocal refined
        before=e.account.extra
        original_refine(bounds)
        refined+=e.account.extra-before
    def attempt(engine):
        q=engine.idx.q
        prior=engine.w.total-engine.monitor_cost-engine.pilot_cost-24
        c=engine.idx.stats['fallback_work']
        if q in bound.probes:
            probes.append([q,prior-6*c])
        original_probe(engine)
    with patch.object(RepairBounds,'defer',keep),patch.object(RepairBounds,'refine',refine),patch.object(ThresholdCompact,'try_launch',attempt):
        while not e.point[1] and not e.ended:
            if witness is None and e.idx.ut.value[1]<bound.cfg['K']:
                witness=bound.project(e)
                witness['balance']=balance
                witness['lower']=balance-156
                witness['covered']=min(witness['forecast'])>=0
                if early and witness['covered']:
                    return dict(witness,score=witness['lower'],probes=[])
            e.step(32)
            if e.trial is not None and e.exact_budget:
                # Normal closure is inevitable. No further tests or tickets.
                break
        assert witness is not None and e.meta['launch']
        for q,value in probes:
            assert value>=witness['forecast'][bound.probes.index(q)], (q,value,witness)
        checks=e.account.branch_checks+e.account.refinements
        lower=balance-refined-8*checks-60-64
        if witness['covered']:
            assert e.account.refinements==0 and lower>=witness['lower']
        return dict(witness,score=witness['lower'] if witness['covered'] else lower,
                    audit_lower=lower,probes=probes,refinements=e.account.refinements)

