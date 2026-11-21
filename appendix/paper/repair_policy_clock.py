"""Use one batch implementation and change only Compact's policy-visible bill."""
import json
import platform
import random
import time

from paper.batched_repair_benchmark import DEST as ARCHIVE, RepairLane, config, factory, caseid, digest
from paper.compact_pre_benchmark import ROOT, DRAWS, BUDGET, SECONDS
from paper.batched_repair import BatchedCompact

DEST = ROOT / 'results/repair_policy_clock_v1'
METHODS = ('reference', 'physical')


class PolicyCompact(BatchedCompact):
    physical = False

    def try_launch(self):
        # Both arms read the same meters and pay the same tariff. The inherited
        # gate only needs a different origin for common work, never private debits.
        self.account.extra += 6
        difference = self.account.extra - self.account.saved
        offset = difference if self.physical else 0
        self.w.observation_overhead += offset
        try:
            super().try_launch()
            if self.trial is not None:
                self.campaign_start -= offset
        finally:
            self.w.observation_overhead -= offset


class PhysicalCompact(PolicyCompact):
    physical = True


class ClockLane(RepairLane):
    def __init__(self, problem, cfg, seed, method):
        self.engine = {'reference': PolicyCompact, 'physical': PhysicalCompact}[method](problem, cfg, seed)
        self.oracle = self.engine.oracle
        self.account = self.engine.account
        self.point = self.engine.query()
        self.peak = 0
        self.seal_at = None
        self.conflict = False


def endpoint(lane, problem, cfg):
    action, good, lower, _, outside = lane.point
    box = None
    if good:
        box = lane.private if outside is None else (lower, outside[0])
        assert box[1] - box[0] <= lane.engine.tol
        # Keep exact-value audit outside the timers and meters (see run).
    row = dict(draws=lane.draws, queries=lane.engine.idx.q, action=action if good else None,
               box=box, meta=dict(lane.engine.meta), account=vars(lane.account).copy())
    kernel = getattr(problem, 'build', 0) + lane.work
    row['drop'] = lane.retire(problem, cfg)
    assert row['drop'] > 0, 'retirement must recognize the engine as a project object'
    row['work'] = kernel + row['drop']
    return row


def status(row, conflict, elapsed):
    if conflict:
        return 'conflict'
    if elapsed > SECONDS:
        return 'wall'
    if row['work'] > BUDGET:
        return 'work'
    if row['box'] is not None:
        return 'certified'
    return 'draw' if row['draws'] >= DRAWS else 'work'


def audit_action(p, row, cfg):
    if row['status'] != 'certified':
        row.update(action=None, box=None, regret=None)
        return
    if hasattr(p, 'scale'):
        from paper.samegame_gate import exact
        scores, _ = exact(p.start, p.h)
        values = [(x+p.B)/p.scale for x in scores]
    else:
        all_values = p.graph.optimal_values(p.means)
        values = [all_values[a] for a in p.graph.children[p.graph.root]]
    row['regret'] = float(max(values) - values[row['action']])
    assert row['regret'] <= cfg['epsilon'] + 1e-12


def solve(make, cfg, seed, method):
    start = time.perf_counter()
    cpu = time.process_time()
    p = make()
    lane = ClockLane(p, cfg, seed, method)
    build = getattr(p, 'build', 0)
    while (not lane.point[1] and not lane.conflict and build + lane.work < BUDGET
           and lane.draws < DRAWS and time.perf_counter() - start < SECONDS):
        lane.advance(DRAWS - lane.draws)
    row = endpoint(lane, p, cfg)
    row.update(seconds=time.perf_counter() - start, cpu=time.process_time() - cpu)
    row['status'] = status(row, lane.conflict, row['seconds'])
    audit_action(p, row, cfg)
    return row


def run():
    old = json.loads((ARCHIVE / 'manifest.json').read_text())
    files = dict(old['source'])
    for name in ('repair_policy_clock.py', 'repair_clock_protocol.txt'):
        files['paper/' + name] = digest(ROOT / 'paper' / name)
    assert all(digest(ROOT / f) == h for f, h in files.items())
    specs = old['cases']
    DEST.mkdir(exist_ok=False)
    manifest = dict(cases=specs, methods=METHODS, source=files, reps=2,
                    python=platform.python_version(), platform=platform.platform(),
                    archive=digest(ARCHIVE / 'runs.jsonl'), caps=[BUDGET, DRAWS, SECONDS])
    (DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2))
    rng = random.Random(351103)
    blocks = []
    for s in specs:
        order = list(METHODS)
        rng.shuffle(order)
        blocks.extend([(s, 0, order), (s, 1, order[::-1])])
    rng.shuffle(blocks)
    with (DEST / 'runs.jsonl').open('x') as out:
        for i, (s, rep, order) in enumerate(blocks, 1):
            make, cfg = factory(s), config(s)
            for pos, method in enumerate(order):
                row = solve(make, cfg, s['seed'], method)
                row.update(case=caseid(s), method=method, repeat=rep, position=pos)
                out.write(json.dumps(row) + '\n')
                out.flush()
            if i % 20 == 0:
                print(i, '/', len(blocks), 'blocks', flush=True)
    (DEST / 'complete.json').write_text(json.dumps(dict(rows=2*len(blocks), sha256=digest(DEST / 'runs.jsonl'))))


if __name__ == '__main__':
    # The shared disposal tariff traverses objects in the paper namespace.
    from paper.repair_policy_clock import run as package_run
    package_run()
