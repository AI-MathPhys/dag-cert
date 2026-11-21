"""Search for and verify a finite reachable separation. Not an incidence study."""
import json

from paper.repair_clock_trace import compare, trace
from paper.repair_policy_clock import (DEST, ClockLane, METHODS, config, factory, caseid,
                                      BUDGET, DRAWS, digest)


class UnpricedLane(ClockLane):
    def __init__(self, p, cfg, seed, method):
        super().__init__(p, cfg, seed, 'physical')
        # This flag only requests reconstruction in BatchBlocks.ordinary.
        # PartialSearch.try_launch uses the real graph and its own screen.
        self.engine.can_clear = False


def family():
    # Difficult near-optimal competitors prolong the post-trial public phase.
    for seed in range(352101,352113):
        for m in (128,160,192,96,224):
            for inverse in (60,40,80,48,64,32,100):
                yield dict(family='layout4', M=m, A=4, good=2, eps=1/inverse, law='constant',
                           profile='sharp', seed=seed, cohort='construction')


def disposition(s, method):
    p, cfg = factory(s)(), config(s)
    cfg['cap'] = s.get('frontier_cap',cfg['cap'])
    lane = ClockLane(p, cfg, s['seed'], method)
    e = lane.engine
    close = e.close
    size = None
    def observe_close(reason):
        nonlocal size
        size = e.trial.possible_size
        close(reason)
    e.close = observe_close
    while not (lane.point[1] or lane.conflict or e.ended or e.idx.q>512 or
               lane.draws>=DRAWS or getattr(p,'build',0)+lane.work>=BUDGET):
        lane.advance(DRAWS-lane.draws)
    m = dict(e.meta)
    m['size_on_close'] = size
    del e.close
    lane.retire(p,cfg)
    return m


def verify(s):
    left, right = [trace(s,m) for m in METHODS]
    row = compare(s,(left,right))
    a,b = row['ends'].values()
    if not (row['first_branch'] and row['first_observation']
            and a['status']==b['status']=='certified' and a['work'] < b['work']):
        return None
    bare = trace(s,'physical',UnpricedLane)[0]
    return dict(spec=s, comparison=row, unpriced=bare,
                cheaper_than_unpriced=bare['status']=='certified' and a['work'] < bare['work'])


def search():
    sources = list(map(json.loads,(DEST/'trace.jsonl').read_text().splitlines()))
    from paper.repair_policy_clock import ARCHIVE
    specs = {caseid(s):s for s in json.loads((ARCHIVE/'manifest.json').read_text())['cases']}
    attempts = []
    best = None

    def candidate(s):
        nonlocal best
        result = verify(s)
        if result:
            best = result if best is None or result['cheaper_than_unpriced'] else best
            return result['cheaper_than_unpriced']
        return False

    for row in sources:
        a,b = row['ends'].values()
        if row['first_observation'] and a['work']<b['work'] and candidate(specs[row['case']]):
            break
    else:
        affected = [dict(specs[row['case']],cohort='construction') for row in sources
                    if row['first_observation'] and row['family'].startswith('layout')]
        from itertools import chain
        def screen(s):
            ms = [disposition(s,m) for m in METHODS]
            attempts.append(dict(s=s, outcomes=[[m['launch'],m['seal'],m['phase_calls'],m['size_on_close']]
                                                for m in ms]))
            return ms
        for i,s in enumerate(chain(affected,family()),1):
            ar,br = screen(s)
            if ar['seal'] and (not br['seal'] or ar['start_N'] != br['start_N']) and candidate(s):
                break
            # Choose a frontier capacity between the two remaining sizes.
            # A full rerun is essential: capacity also enters the launch forecast.
            x,y = ar['size_on_close'],br['size_on_close']
            if x is not None and y is not None and x < y and not br['seal']:
                found = False
                for cap in sorted({x,(x+y)//2,y-1}):
                    spec = dict(s,frontier_cap=max(1,cap))
                    a,b = screen(spec)
                    if a['seal'] and (not b['seal'] or a['start_N'] != b['start_N']) and candidate(spec):
                        found = True
                        break
                if found:
                    break
            if i%40==0:
                print(i,'construction prefixes',flush=True)
    (DEST/'construction.json').write_text(json.dumps(dict(search=attempts,witness=best,
                          source=digest(DEST.parent.parent/'paper/repair_clock_witness.py')),indent=2))
    print('construction',len(attempts),best and (best['spec'],best['cheaper_than_unpriced']),flush=True)


if __name__ == '__main__':
    from paper.repair_clock_witness import search as run
    run()
