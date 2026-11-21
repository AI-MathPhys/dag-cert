"""Paired cold certification under identical work, wall and physical observation caps."""
import argparse
import json
import platform
import random
import time
from pathlib import Path

from dag_mcts.graph import Problem
from paper.census_rescue_benchmark import problem as layout_problem
from paper.cold_decision_solvers import create
from paper.compact_side import SideCompact, SideRange
from paper.frontier_gate_race import AuditedCompact, Lane, BUDGET, DRAWS, SECONDS
from paper.paused_benchmark import endgame, factory as earlier_factory
from paper.peg_fragment_benchmark import ROOT, digest
from paper.samegame_gate import standard
from paper.static_rescue_benchmark import caseid
from paper.wall_time_common import make_input

DEST = ROOT/'results/compact_side_v1'
METHODS = ('compact','range','side_compact','side_range','pre_only','post_only')


def cases():
    boards = standard()
    for offset,seed in enumerate(range(301101,301109)):
        for law in ('constant','bernoulli'):
            yield dict(family='wide',seed=seed,eps=.05,law=law,good=1)
        for size,actions,eps in ((192,4,.0125),(128,8,1/60)):
            law = ('constant','bernoulli')[(offset+(actions==8))%2]
            for profile in ('sharp','shoulder'):
                yield dict(family='layout'+str(actions),seed=seed,M=size,A=actions,
                           good=2,eps=eps,law=law,profile=profile)
        yield dict(family='narrow',seed=seed,eps=.01,law='constant',good=2)
        yield dict(family='six_near',seed=seed,M=160,A=8,good=1,eps=.02,
                   law=('constant','bernoulli')[offset%2],profile='sharp')
        yield dict(family='large',seed=seed,eps=.05,law='bernoulli')
        board,path = endgame(boards[8+offset],seed)
        yield dict(family='samegame',seed=seed,eps=.02,board=board,path=path,source=9+offset,h=3)


def factory(s):
    if s['family']=='large':
        _,p = make_input('fragmented',1,1,s['seed'])
        return lambda:p
    if s['family']=='six_near':
        p = layout_problem(s)
        rng = random.Random(s['seed']+730311)
        means = p.means.copy()
        for j in rng.sample([j for j,v in means.items() if v<.3],6):
            means[j] = .70-rng.uniform(1.6,2.65)*s['eps']
        p = Problem('six_near',p.graph,means,p.deterministic)
        return lambda:p
    return earlier_factory(s)


def config(s):
    k = 64000 if s['family'] in ('wide','large','samegame') else round(1/s['eps'])**4
    return dict(epsilon=s['eps'],K=k,cap=12,delta=.01,oracle_cost=1)


class TimedLane(Lane):
    def __init__(self,p,c,seed,method):
        if method=='compact':
            engine = AuditedCompact(p,c,seed)
        elif method=='range':
            engine = create(p,c,seed,'range')
        elif method=='side_range':
            engine = SideRange(p,c,seed)
        else:
            mode = {'side_compact':'both','pre_only':'pre','post_only':'post'}[method]
            engine = SideCompact(p,c,seed,mode)
        self.engine = engine
        self.oracle = engine.oracle
        self.account = getattr(engine,'account',None)
        self.point = engine.query()
        self.peak = 0
        self.seal_at = None
        self.conflict = False

    @property
    def work(self):
        reported = super().work
        if self.account is None:
            return reported
        return reported + self.account.extra - self.account.saved

    def retire(self,problem,config):
        idx = self.engine.idx
        cost = super().retire(problem,config)
        # The paid disposal walk precedes breaking the instance method cycles.
        idx.__dict__.pop('ranged', None)
        self.account = None
        return cost


def run_one(make,c,seed,method,*,clock_cap=SECONDS):
    start = time.perf_counter()
    p = make()
    build = getattr(p,'build',0)
    lane = TimedLane(p,c,seed,method)
    while (not lane.point[1] and not lane.conflict and build+lane.work<BUDGET
           and lane.draws<DRAWS and time.perf_counter()-start<clock_cap):
        lane.advance(DRAWS-lane.draws)
    good = lane.point[1]
    box = None
    if good:
        action,_,lower,_,outside = lane.point
        box = lane.private if outside is None else (lower,outside[0])
        assert box[1]-box[0]<=lane.engine.tol
    action = lane.point[0] if good else None
    conflict = lane.conflict
    draws = lane.draws
    kernel = build+lane.work
    logical = build+lane.engine.w.total+getattr(lane.oracle,'operations',0)
    info = vars(lane.account).copy() if lane.account else {}
    meta = dict(getattr(lane.engine,'meta',{}))
    queries = lane.engine.idx.q
    drop = lane.retire(p,c)
    elapsed = time.perf_counter()-start
    work = kernel+drop
    status = ('conflict' if conflict else 'wall' if elapsed>clock_cap else 'work' if work>BUDGET
              else 'certified' if good else 'draw' if draws>=DRAWS else 'work')
    return dict(status=status,work=work,seconds=elapsed,draws=draws,queries=queries,logical=logical,
                drop=drop,action=action if status=='certified' else None,
                box=box if status=='certified' else None,meta=meta,account=info)


def run(dest):
    specs = list(cases())
    dest.mkdir(parents=True,exist_ok=True)
    if any(dest.iterdir()):
        raise ValueError('use a fresh output directory')
    paths = set(json.loads((ROOT/'results/paused_fresh_v2/manifest.json').read_text())['source'])
    paths.update('paper/'+f for f in ('compact_side.py','compact_side_benchmark.py','compact_side_protocol.txt',
                'wall_time_common.py','partial_benchmark.py','escrow_benchmark.py','report_peg_fragment.py'))
    # Include the generator hashes from the earlier matching large-DAG study.
    paths.update(json.loads((ROOT/'results/compact_wall_frozen/manifest.json').read_text())['sources'])
    manifest = dict(cases=specs,methods=METHODS,source={f:digest(ROOT/f) for f in sorted(paths)},
                    python=platform.python_version(),platform=platform.platform())
    (dest/'manifest.json').write_text(json.dumps(manifest,indent=2))
    blocks=[]
    for i,s in enumerate(specs):
        order=list(METHODS)
        random.Random(302101+i).shuffle(order)
        blocks.extend(((s,0,order),(s,1,order[::-1])))
    random.Random(302909).shuffle(blocks)
    with (dest/'runs.jsonl').open('x') as out:
        for b,(s,repeat,order) in enumerate(blocks,1):
            make,c = factory(s),config(s)
            for pos,m in enumerate(order):
                r=run_one(make,c,s['seed'],m)
                r.update(method=m,case=caseid(s),repeat=repeat,position=pos)
                out.write(json.dumps(r)+'\n')
                out.flush()
            if b%16==0:
                print(b,'/',len(blocks),'blocks',flush=True)
    (dest/'complete.json').write_text(json.dumps(dict(records=2*len(specs)*len(METHODS),
                                          sha256=digest(dest/'runs.jsonl'))))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,default=DEST)
    run(parser.parse_args().out)

