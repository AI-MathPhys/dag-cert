"""Untimed audit of the frozen pair. Observation and comparison policies are unchanged."""
import json
from collections import Counter, defaultdict
from contextlib import ExitStack
from unittest.mock import patch
from paper.batched_repair import BatchTree
from paper.frontier_gate_race import dispose_cells
from paper.decision_price import DecisionLane, RepairBounds, ThresholdCompact, ThresholdTree
from paper.decision_price_benchmark import (ROOT, DEST as ARCHIVE, population, config, factory,
    BUDGET, DRAWS, endpoint, status, digest)

DEST=ROOT/'results/index_repayment_v1'
FULL=BatchTree.price_group
BOUND=ThresholdTree.price_group
REFINE=RepairBounds.refine
DECIDE=RepairBounds.decide
LAUNCH=ThresholdCompact.try_launch


def sign(lo,hi):
    return 'threshold' if lo>0 else 'full' if hi<0 else 'abstain'


class Audit:
    def __init__(self,lane):
        self.lane=lane
        self.count=Counter()
        self.classes=defaultdict(Counter)
        self.prefix=None
        self.launch=None
        self.count['setup']=12+48*int(lane.engine.can_clear)

    def snapshot(self):
        c=self.count
        debit=c['storage']+c['refinement']+c['comparisons']+c['setup']
        lo=c['lower']-debit
        hi=c['upper']-debit
        return dict(lo=lo,hi=hi,sign=sign(lo-64,hi+64),draws=self.lane.draws,
                    groups=c['long'],pending=len(self.lane.engine.bounds.pending))

    def price(self,tree,side,events,peer_old,peer_new):
        n=len(events)
        c=self.count
        if n<4:
            pulls,price=BOUND(tree,side,events,peer_old,peer_new)
            c['short']+=1
            c['common_short']+=price
            return pulls,price
        prof=tree.profile
        pos=prof.cursor[side]
        first,last=events[0][0],events[-1][0]
        mid,a,c0=prof.lookup(side,first,pos)
        end,b,c1=prof.lookup(side,last,mid)
        independent=a==b and a<=prof.join
        stationary=peer_old==peer_new
        bulk=independent or (stationary and prof.depth(a,peer_old,first)==prof.depth(b,peer_old,last))
        premium=6*int(stationary and not independent)
        screen=c0+c1+8+premium+3*int(bulk)
        low=prof.depth(min(a,b),max(peer_old,peer_new),min(first,last))
        high=prof.depth(max(a,b),min(peer_old,peer_new),max(first,last))
        storage=0 if low==high else 32+3*n+4*prof.h
        if bulk:
            assert not storage
            kind='bulk-independent' if independent else 'bulk-stationary'
            lower=upper=premium-3
        else:
            kind='deferred-scan' if storage else 'collapsed-scan'
            movement=abs(end-pos)
            exhausted=prof.h if prof.inc else 0
            kmin=0 if mid==exhausted else 1 if end==exhausted else n
            kmax=0 if mid==exhausted else n-1 if end==exhausted else n
            lower=7*n+3*(movement+kmin)+premium-6
            upper=7*n+3*(movement+kmax)+premium-6
        # Test the endpoint-only inequalities against the opposite kernel
        # after the prospective calculation. Restore its cursor before continuing.
        try:
            _,full=FULL(tree,side,events,peer_old,peer_new)
            assert prof.cursor[side]==end
        finally:
            prof.cursor[side]=pos
        oldest=tree.account.extra
        pulls,bound=BOUND(tree,side,events,peer_old,peer_new)
        assert prof.cursor[side]==end and bound==c0+c1+14
        assert tree.account.extra-oldest==storage
        point=full-screen
        assert not bulk or point==0
        assert lower<=full-bound<=upper
        c.update(long=1,lower=lower,upper=upper,point=point,screen=screen,bound=bound,
                 storage=storage,group_net=full-bound)
        self.classes[kind].update(groups=1,events=n,gross=full-bound,storage=storage,
                                  positive=int(lower>storage),nonpositive=int(upper<=storage),
                                  unresolved=int(lower<=storage<upper))
        return pulls,bound

    def instrument(self,stack):
        observe=self
        def price(tree,*args):
            return observe.price(tree,*args)
        def refine(b):
            old=b.account.extra
            REFINE(b)
            observe.count['refinement']+=b.account.extra-old
        def decide(b,predicate):
            old=b.account.extra
            before=observe.count['refinement']
            ans=DECIDE(b,predicate)
            observe.count['comparisons']+=b.account.extra-old-(observe.count['refinement']-before)
            return ans
        def launch(engine):
            LAUNCH(engine)
            if engine.trial is not None:
                assert observe.launch is None
                observe.launch=observe.snapshot()
                observe.launch['exact']=engine.exact_budget
        for cls,name,func in ((ThresholdTree,'price_group',price),(RepairBounds,'refine',refine),
                              (RepairBounds,'decide',decide),(ThresholdCompact,'try_launch',launch)):
            stack.enter_context(patch.object(cls,name,func))


def audit_case(obj,pair):
    s=obj['s']
    cfg=config(s)
    p=factory(s)()
    lane=DecisionLane(p,cfg,obj['tie'],'threshold')
    study=Audit(lane)
    build=getattr(p,'build',0)
    with ExitStack() as stack:
        study.instrument(stack)
        while not lane.point[1] and not lane.conflict and build+lane.work<BUDGET and lane.draws<DRAWS:
            lane.advance(DRAWS-lane.draws)
            if (study.prefix is None and lane.account.batch_blocks==64 and
                    not lane.engine.ended and lane.engine.trial is None and not lane.point[1]):
                study.prefix=study.snapshot()
                if not lane.engine.can_clear:
                    study.prefix['sign']='full'
                    study.prefix['closed_screen']=True
    c=study.count
    assert c['comparisons']==8*(lane.account.branch_checks+lane.account.refinements)
    assert study.classes['deferred-scan']['groups']==lane.account.deferred_groups
    bounds=lane.engine.bounds
    pending=bounds.pending
    c['retired_records']=len(pending)
    c['record_slots']=sum(9+4*len(g[3]) for g in pending)
    shared=(p,p.graph,cfg)
    original=dispose_cells(lane.engine,shared)
    try:
        bounds.pending=[]
        c['live_retirement']=original-dispose_cells(lane.engine,shared)
    finally:
        bounds.pending=pending
    assert c['live_retirement']>=c['record_slots']
    row=endpoint(lane,p,cfg)
    assert status(row,lane.conflict,0)==pair['threshold']['status']
    for name in ('work','drop','draws','box','action','queries','account','meta'):
        # JSON normalizes diagnostic tuples in the two allowance fields.
        assert json.loads(json.dumps(row[name]))==pair['threshold'][name],(obj['case'],name)
    base=pair['reference']
    assert (row['draws'],row['action'])==(base['draws'],base['action'])
    c['disposal']=row['drop']-base['drop']
    c['saving']=c['point']+c['screen']-c['bound']-c['storage']-c['refinement']-c['comparisons']-c['setup']-c['disposal']
    assert c['saving']==base['work']-row['work'],(obj['case'],c['saving'],base['work']-row['work'])
    if study.launch is not None and study.launch['exact'] and base['status']=='certified':
        assert abs(c['disposal'])<=64
        assert study.launch['lo']-64<=c['saving']<=study.launch['hi']+64
    return dict(tag=obj['tag'],case=obj['case'],seed=s['seed'],status=base['status'],draws=row['draws'],
                full=base['work'],threshold=row['work'],counts=c,classes=study.classes,
                prefix=study.prefix,launch=study.launch,refinements=row['account']['refinements'])


def main(dest=DEST):
    data=ARCHIVE/'runs.jsonl'
    assert digest(data)==json.loads((ARCHIVE/'complete.json').read_text())['sha256']
    archive=defaultdict(dict)
    for line in data.read_text().splitlines():
        r=json.loads(line)
        if r['repeat']==0 and r['method'] in ('threshold','reference'):
            archive[r['case']][r['method']]=r
    specs=[o for o in population() if o['tag'] in ('fresh','cohort')]
    dest.mkdir(exist_ok=False)
    out=dest/'cases.jsonl'
    (dest/'manifest.json').write_text(json.dumps(dict(archive=digest(data),cases=[o['case'] for o in specs],
          protocol=digest(ROOT/'paper/index_repayment_protocol.txt'),source=digest(ROOT/'paper/index_repayment_audit.py'))))
    with out.open('x') as f:
        for i,o in enumerate(specs,1):
            rec=audit_case(o,archive[o['case']])
            f.write(json.dumps(rec)+'\n')
            f.flush()
            if i%24==0:print(i,'/',len(specs),'reconciled',flush=True)
    (dest/'complete.json').write_text(json.dumps(dict(rows=len(specs),sha256=digest(out))))


if __name__=='__main__':
    main()
