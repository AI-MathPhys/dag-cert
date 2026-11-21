"""Pause dense witness maintenance while an exactly verified frontier can serve it."""
import time

from paper.census_rescue import Census
from paper.cold_decision_solvers import Persistent
from paper.frontier_gate_features import checkpoint
from paper.frontier_gate_race import Lane, BUDGET, DRAWS, SECONDS
from paper.frontier_gate_warm import WarmLane
from paper.frontier_sampling import Work
from paper.uniform_selection import CountTree


class ScheduledCensus(Census):
    """On tiny DAGs the nominal second checkpoint may already have passed."""
    def funded_review(self, lane, later, credit):
        admit, details, next_query, fee = super().funded_review(lane, later, credit)
        if next_query is not None and next_query <= lane.engine.idx.q:
            next_query = None
        return admit, details, next_query, fee


class SparseView:
    """Share the dense verifier's arrays, RNG and evidence. Only its trees go stale."""

    def __init__(self, dense, members, blockers=None):
        self.dense = dense
        self.top = dense.top
        self.threshold = dense.best
        self.members = members  # decreasing ranks match CountTree's right-first selection
        self.blockers = blockers
        self.price = 6 * len(members) + 18

    def publish(self, j, lower, upper):
        d = self.dense
        if not d.lower[j] <= lower <= upper <= d.upper[j]:
            raise ValueError('non-nested publication')
        d.lower[j], d.upper[j] = lower, upper
        if lower > d.best:
            d.best, d.anchor = lower, j
        if d.lookup[j][0]:
            d.inside_lower = max(d.inside_lower, lower)
        # Charge the dense flat-publication tariff in full, without tree repair.
        d.w.query_reads += 5
        d.w.heap_comparisons += 7
        d.w.statistic_writes += 5

    def witnesses(self):
        d = self.dense
        peaks = [-1, -1]
        ties = [[], []]
        for j, side in self.members:
            value = d.upper[j]
            if value > peaks[side]:
                peaks[side] = value
                ties[side] = [j]
            elif value == peaks[side]:
                ties[side].append(j)
        ambiguous = (min(peaks) < self.threshold if self.blockers is None else
                     any(peaks[i] <= self.blockers[i] for i in (0, 1)))
        if ambiguous or peaks[1] < d.best:
            return None  # no RNG has been consumed; dense must answer this query
        d.w.query_reads += self.price
        return tuple((peaks[i], ties[i][d.rng.randrange(len(ties[i]))]) for i in (1, 0))

    def repair(self):
        d = self.dense
        scratch = Work()
        for side, group in enumerate(d.groups):
            old = d.trees[side]
            # Charge gathering values, releasing the old arrays and temporary lists.
            scratch.statistic_writes += 4 * len(group) + len(old.value) + len(old.count) + 12
            tree = CountTree([d.upper[j] for j in group], scratch)
            tree.w = d.w
            d.trees[side] = tree
        return scratch.total + self.price + 2 * len(self.members) + 16


class PausedVerifier(Persistent):
    def query(self):
        if not isinstance(self.idx, SparseView):
            return super().query()
        view = self.idx
        pair = view.witnesses()
        if pair is None:
            self.idx = view.dense
            repair = view.repair()
            self.repair_cost += repair
            self.repairs += 1
            if repair > self.reserve:
                raise AssertionError('underfunded repair')
            return super().query()
        d = view.dense
        d.q += 1
        self.sparse_queries += 1
        self.saved_floor += self.saving_floor
        x, y = pair
        self.pair = x[1], y[1]
        good = y[0] <= d.inside_lower + self.tol
        self.point = d.active, good, d.inside_lower, x, y
        return self.point

    def try_frontier(self, grant, use_blockers):
        """Buy at most one installation; failed scans use no samples or RNG."""
        d = self.idx
        size = len(d.upper)
        scan = (14 if use_blockers else 5) * size + 32
        reserve = 64 * size + 256
        if scan + reserve > grant:
            return 0, False
        if not all(d.trees) or d.best <= 0:
            return scan, False
        members = []
        blockers = [-1, -1] if use_blockers else None
        threshold = d.best / self.c['K'] - self.c['epsilon']
        for j in reversed(range(size)):
            side = d.lookup[j][0]
            if use_blockers:
                leaf = self.g.leaves[j]
                n = self.ev.counts[leaf]
                keep = j in self.pair or not n or self.ev.sums[leaf] / n >= threshold
            else:
                keep = d.upper[j] >= d.best
            if keep:
                members.append((j, side))
                if len(members) > self.c['cap']:
                    return scan, False
            elif use_blockers:
                blockers[side] = max(blockers[side], d.upper[j])
        depths = sum(tree.size.bit_length() - 1 for tree in d.trees)
        advantage = 29 + 4 * depths - (6 * len(members) + 18)
        if advantage <= 0 or len({side for _, side in members}) != 2:
            return scan, False
        self.reserve = reserve
        self.saving_floor = advantage
        self.frontier_size = len(members)
        self.installations += 1
        self.idx = SparseView(d, members, blockers)
        return scan + reserve, True


class PausedLane(Lane):
    def __init__(self, p, config, seed):
        s = PausedVerifier(p, config, seed)
        s.sparse_queries = s.repair_cost = s.reserve = s.saving_floor = s.frontier_size = 0
        s.saved_floor = s.installations = s.repairs = 0
        self.engine = s
        self.oracle = s.oracle
        self.point = s.query()
        self.peak = 0
        self.seal_at = None
        self.conflict = False


def solve_pause(factory, config, seed, model, method='replace'):
    """replace uses a path-matched frontier; warm_pause is a one-credit Compact fork."""
    if method not in ('replace', 'replace_all', 'blockers', 'blockers_all', 'warm_pause'):
        raise ValueError(method)
    start = time.perf_counter()
    problem = factory()
    build = getattr(problem, 'build', 0)
    use_view = method != 'warm_pause'
    base = PausedLane(problem, config, seed) if use_view else Lane(problem, config, seed, 'persistent')
    gate = ScheduledCensus(model)
    monitor = 0
    dispatch = 12
    probe_spend = 0
    spent = 0
    probe_count = 0
    credit = 0
    fork_work = fork_draws = fork_drop = max_step = copied = 0
    fork = None
    review = checkpoint(len(problem.graph.leaves))
    later = False
    next_probe = review if method.endswith('_all') else None
    if method.endswith('_all'):
        review = None
    opened_at = None
    gate_log = None
    while True:
        pw = build + base.work
        trial_work = spent + (fork.work if fork is not None else fork_work)
        total = pw + dispatch + monitor + probe_spend + trial_work + fork_drop
        draws = base.draws + (fork.draws if fork is not None else fork_draws)
        if base.point[1] or (fork and fork.point[1]) or base.conflict or (fork and fork.conflict):
            break
        if total >= BUDGET or draws >= DRAWS or time.perf_counter() - start >= SECONDS:
            break
        if fork is not None:
            if trial_work < credit:
                old = fork.work
                fork.advance(DRAWS - draws)
                spent += 8
                max_step = max(max_step, fork.work - old + 8)
                continue
            fork_work, fork_draws = fork.work, fork.draws
            fork_drop = fork.retire(problem, config)
            fork = None
            continue
        if review is not None and base.engine.idx.q >= review:
            if pw // 16 >= 32:
                monitor = 32
                available = max(0, pw // 100 - (dispatch - 12))
                admit, features, review, fee = gate.funded_review(base, later, available)
                assert 0 <= fee <= available
                dispatch += fee
                gate_log = dict(admit=admit, features=features, prefix_work=pw, prefix_draws=base.draws)
                if admit:
                    next_probe = base.engine.idx.q
                later = True
            else:
                review = None
        if next_probe is not None and not isinstance(base.engine.idx, SparseView) and base.engine.idx.q >= next_probe:
            if method == 'warm_pause':
                opened_at = pw
                credit = pw
                fork = WarmLane(problem, config, seed, base)
                copied = fork.copied
                spent = 8
                max_step = fork.work + spent
                next_probe = None
                continue
            use_blockers = method.startswith('blockers')
            charge, opened = base.engine.try_frontier(pw // 16 - probe_spend, use_blockers)
            probe_spend += charge
            probe_count += int(charge != 0)
            if opened and opened_at is None:
                opened_at = pw
            idx = base.engine.idx.dense if opened else base.engine.idx
            next_probe = None if opened and not use_blockers else 2 * (idx.q - 1) + 1
        base.advance(DRAWS - draws)
        dispatch += 8

    winner = fork if fork is not None and fork.point[1] else base if base.point[1] else None
    action = None
    box = None
    if winner:
        action, _, lower, _, outside = winner.point
        box = winner.private if outside is None else (lower, outside[0])
        if box[1] - box[0] > winner.engine.tol:
            raise AssertionError('invalid stopping witness')
    conflict = base.conflict or bool(fork and fork.conflict)
    base_draws = base.draws
    pw = build + base.work
    info = dict(sparse_queries=0, repair=0, saving_floor=0, frontier_size=0, reserve=0,
                saved_floor=0, installations=0, repairs=0)
    if use_view:
        s = base.engine
        info.update(sparse_queries=s.sparse_queries, repair=s.repair_cost, saving_floor=s.saving_floor,
                    frontier_size=s.frontier_size, reserve=s.reserve,
                    saved_floor=s.saved_floor, installations=s.installations, repairs=s.repairs)
        if isinstance(s.idx, SparseView):
            s.idx = s.idx.dense  # discard view; its slot release was prepaid
    if fork is not None:
        fork_work, fork_draws = fork.work, fork.draws
        fork_drop = fork.retire(problem, config)
    base_drop = base.retire(problem, config)
    elapsed = time.perf_counter() - start
    work = pw + dispatch + monitor + probe_spend + spent + fork_work + fork_drop + base_drop
    status = ('conflict' if conflict else 'wall' if elapsed > SECONDS else 'work' if work > BUDGET
              else 'certified' if winner else 'draw' if base_draws + fork_draws >= DRAWS else 'work')
    return dict(status=status, action=action if status=='certified' else None,
                box=box if status=='certified' else None, work=work, seconds=elapsed,
                base_draws=base_draws, alt_draws=fork_draws, base_work=pw, base_drop=base_drop,
                fork_work=spent+fork_work, fork_drop=fork_drop, quantum=max_step, copied=copied,
                opened_at=opened_at, gate=gate_log, scans=probe_count, probe_spend=probe_spend,
                dispatch=dispatch, monitor=monitor, winner=('fork' if winner is not None and winner is fork else
                'base' if winner else None), **info)

