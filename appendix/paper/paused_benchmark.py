"""Development replay followed by a separate, frozen frontier-replacement holdout."""
import argparse
import json
import platform
import random
from collections import defaultdict
from pathlib import Path

from paper.census_rescue_benchmark import DEFAULT as PREVIOUS, problem as fragmented_problem
from paper.frontier_gate_race import solve
from paper.paused_frontier import ScheduledCensus, solve_pause
from paper.peg_fragment_benchmark import ROOT, digest
from paper.report_static_rescue import cheaper, seal_win
from paper.samegame_gate import Game, Moves, standard, tiles
from paper.static_rescue import MODEL_PATH
from paper.static_rescue_benchmark import caseid, problem as standard_problem

METHODS = ('persistent','compact','range','direct','static','census','warm_pause','replace','blockers','blockers_all')
LOSS_METHODS = ('persistent','census','warm_pause','replace')

def losses():
    manifest = json.loads((PREVIOUS/'manifest.json').read_text())
    rows = defaultdict(dict)
    for line in (PREVIOUS/'runs.jsonl').read_text().splitlines():
        row = json.loads(line)
        if row['repeat']==0:
            rows[row['case']][row['method']] = row
    selected = []
    for s in manifest['cases']:
        r = rows[caseid(s)]
        if seal_win(r['compact'],r['persistent']) is True and cheaper(r['census'],r['persistent']) is False:
            selected.append(s)
    assert len(selected)==16
    return selected

def endgame(board, seed):
    """Use a new random legal trajectory, taking the first small branching endgame."""
    moves = Moves()
    for attempt in range(100):
        rng = random.Random(seed + attempt*1009)
        state = board
        path = []
        while actions := moves(state):
            if tiles(state)<=30 and len(actions)>=3:
                return state,path
            action = rng.randrange(len(actions))
            path.append(action)
            state = actions[action][0]
    raise ValueError('no eligible endgame')

def fresh():
    boards = standard()
    for i, seed in enumerate(range(287101,287109)):
        for law in ('constant','bernoulli'):
            yield dict(family='wide',seed=seed,eps=.05,law=law,good=1)
        for size,actions,eps in ((192,4,.0125),(128,8,1/60)):
            law = ('constant','bernoulli')[(i + (actions==8))%2]
            for profile in ('sharp','shoulder'):
                yield dict(family='layout'+str(actions),seed=seed,M=size,A=actions,eps=eps,
                           law=law,good=2,profile=profile)
        yield dict(family='narrow',seed=seed,eps=.01,law='constant',good=2)
        board,path = endgame(boards[i],seed)
        yield dict(family='samegame',seed=seed,eps=.02,board=board,path=path,source=i+1,h=3)

def factory(s):
    if s['family']=='samegame':
        board = tuple(map(tuple,s['board']))
        return lambda: Game(board,s['h'])
    p = fragmented_problem(s) if s['family'].startswith('layout') else standard_problem(s)
    return lambda: p

def run(phase,dest):
    if phase=='fresh' and not (ROOT/'results/paused_revision_v1/complete.json').exists():
        raise ValueError('finish the revised loss replay first')
    specs = list(fresh()) if phase=='fresh' else losses()
    methods = METHODS if phase=='fresh' else ('persistent','blockers') if phase=='revision' else LOSS_METHODS
    model = json.loads(MODEL_PATH.read_text())
    dest.mkdir(parents=True,exist_ok=True)
    if any(dest.iterdir()):
        raise ValueError('use an empty results directory')
    sources = list(json.loads((PREVIOUS/'manifest.json').read_text())['source'])
    sources += ['paper/'+s for s in ('paused_frontier.py','paused_benchmark.py','paused_protocol.txt',
        'frontier_gate_warm.py','samegame_gate.py')]
    sources += ['data/samegame/StandardTestset.txt']
    manifest = dict(phase=phase,cases=specs,methods=methods,python=platform.python_version(),
                    platform=platform.platform(),source={f:digest(ROOT/f) for f in sources},
                    parent_trace=digest(PREVIOUS/'runs.jsonl'))
    (dest/'manifest.json').write_text(json.dumps(manifest,indent=2))
    blocks = []
    for i,s in enumerate(specs):
        order = list(methods)
        random.Random(288101+i).shuffle(order)
        blocks.extend([(s,0,order),(s,1,order[::-1])])
    random.Random(288909).shuffle(blocks)
    with (dest/'runs.jsonl').open('x') as out:
        for block,(s,repeat,order) in enumerate(blocks,1):
            make = factory(s)
            k = 64000 if s['family'] in ('wide','samegame') else round(1/s['eps'])**4
            cfg = dict(epsilon=s['eps'],K=k,delta=.01,oracle_cost=1,cap=12)
            for pos,m in enumerate(order):
                if m in ('replace','replace_all','warm_pause','blockers','blockers_all'):
                    r = solve_pause(make,cfg,s['seed'],model,m)
                else:
                    r = solve(make,cfg,s['seed'],m,controller=ScheduledCensus(model) if m=='census' else None)
                r.update(method=m,case=caseid(s),repeat=repeat,position=pos)
                out.write(json.dumps(r)+'\n')
                out.flush()
            if block%8==0:
                print(block,'/',len(blocks),'blocks',flush=True)
    (dest/'complete.json').write_text(json.dumps(dict(records=len(blocks)*len(methods),
                                          sha256=digest(dest/'runs.jsonl'))))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('phase',choices=('losses','revision','fresh'))
    parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    version = 'v2' if args.phase=='fresh' else 'v1'
    run(args.phase,args.out or ROOT/('results/paused_'+args.phase+'_'+version))

