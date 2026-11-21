"""Uncapped paired-price bounds from one Compact prefix; diagnostics never finance the trial."""
import os
import random
from unittest.mock import patch

from paper.decision_price import RepairBounds, ThresholdCompact
from paper.frontier_gate_race import dispose_cells
from paper.decision_price_benchmark import config, factory


class RankBits(random.Random):
    def __init__(self,data=None):
        self.stream=bytearray(data or b'')
        self.fixed=data is not None
        self.bits=0

    def randrange(self,n):
        if n<=0:raise ValueError('empty tie')
        width=(n-1).bit_length()
        if not width:return 0
        while True:
            end=(self.bits+width+7)//8
            if end>len(self.stream):
                if self.fixed:raise ValueError('incomplete stored tape')
                self.stream.extend(os.urandom(4096))
            offset=self.bits%8
            word=int.from_bytes(self.stream[self.bits//8:end],'little')
            self.bits+=width
            rank=(word>>offset)&((1<<width)-1)
            if rank<n:return rank

    def used(self):
        return bytes(self.stream[:(self.bits+7)//8])


def audit(s,rng,prediction_only=False):
    p=factory(s)()
    cfg=config(s)
    engine=ThresholdCompact(p,cfg,1)
    engine.idx.rng=rng
    engine.query()
    scan=lower=storage=refine_fee=0
    prediction=None
    initial=12+48*int(engine.can_clear)
    bd=engine.bounds
    defer=RepairBounds.defer
    refine=RepairBounds.refine
    launch=ThresholdCompact.try_launch
    def keep(bounds,profile,side,start,events,lo,hi):
        nonlocal scan,lower,storage
        pos=start
        cost=0
        boundary=profile.h if profile.inc else 0
        for i,(key,peer) in enumerate(events):
            pos,_,units=profile.lookup(side,key,pos)
            if not i:mid=pos
            cost+=units+5
        n=len(events)
        kmin=n if pos!=boundary else int(mid!=boundary)
        safe=7*n+3*(abs(pos-start)+kmin)
        assert safe<=cost
        lower+=safe
        scan+=cost
        storage+=32+3*n+4*profile.h
        defer(bounds,profile,side,start,events,lo,hi)
    def pay(bounds):
        nonlocal refine_fee
        before=engine.account.extra
        refine(bounds)
        refine_fee+=engine.account.extra-before
    def probe(obj):
        nonlocal prediction
        launch(obj)
        if obj.trial is not None and obj.idx.q<=256:
            checks=obj.account.branch_checks+obj.account.refinements
            margin=lower-storage-refine_fee-8*checks-initial-64
            prediction=dict(q=obj.idx.q,exact=obj.exact_budget,lower=margin,
                            sign='deferred' if obj.exact_budget and margin>0 else 'immediate')
    with patch.object(RepairBounds,'defer',keep),patch.object(RepairBounds,'refine',pay),patch.object(ThresholdCompact,'try_launch',probe):
        while not engine.point[1] and not engine.ended:
            engine.step(32)
            if prediction_only and (prediction or engine.idx.q>256):break
            if engine.trial is not None and engine.exact_budget:break
    if prediction_only:return prediction or dict(q=None,exact=False,lower=None,sign='immediate')
    launched=bool(engine.meta['launch'])
    # An exact open trial will release records on closure with no further pricing.
    live_fee=0
    if not launched:
        assert engine.point[1]
        pending=bd.pending
        shared=(p,p.graph,cfg)
        with_records=dispose_cells(engine,shared)
        try:
            bd.pending=[]
            live_fee=with_records-dispose_cells(engine,shared)
        finally:bd.pending=pending
    checks=engine.account.branch_checks+engine.account.refinements
    center=scan-storage-refine_fee-8*checks-initial-live_fee
    return dict(center=center,low=center-64,high=center+64,q=engine.idx.q,launch=launched,
                exact=prediction and prediction['exact'],checks=checks,records=engine.account.deferred_groups,
                refinements=engine.account.refinements,live_fee=live_fee,scan=scan,storage=storage,
                refine_fee=refine_fee,prediction=prediction)
