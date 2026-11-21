"""Self-contained, non-destructive reproduction commands for Certifying UCT on DAGs."""
import argparse
from contextlib import contextmanager
import hashlib
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
FROZEN = ROOT / 'results'


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def execute(*args, cwd=ROOT):
    subprocess.run([sys.executable, '-B', *map(str, args)], cwd=cwd, check=True)


@contextmanager
def patch(module, **values):
    old = {key: getattr(module, key) for key in values}
    for key, value in values.items():
        setattr(module, key, value)
    try:
        yield
    finally:
        for key, value in old.items():
            setattr(module, key, value)


def output_dir(value, *, fresh=False):
    path = Path(value).resolve()
    protected = [ROOT / n for n in ('results', 'dag_mcts', 'paper', 'tests', 'reference', 'appendix')]
    if path == ROOT or any(path == p or p in path.parents for p in protected):
        raise ValueError('Outputs must not overwrite repository sources or frozen records')
    if fresh and path.exists():
        raise FileExistsError(f'Choose a new output directory: {path}')
    path.mkdir(parents=True, exist_ok=not fresh)
    return path


def verify():
    manifest = json.loads((ROOT / 'artifact_manifest.json').read_text())
    for name, expected in manifest['files'].items():
        if digest(ROOT / name) != expected:
            raise ValueError(f'Artifact checksum mismatch: {name}')
    for name in ('uct_backup_v1', 'uct_backup_v1/gap-study', 'uct_frontier_v1'):
        folder = FROZEN / name
        manifest = json.loads((folder / 'manifest.json').read_text())
        for source, expected in manifest['sources'].items():
            if digest(ROOT / source) != expected:
                raise ValueError(f'Frozen source mismatch: {source}')
        stamp = json.loads((folder / 'complete.json').read_text())
        if digest(folder / 'runs.jsonl') != stamp.get('sha256', stamp.get('runs')):
            raise ValueError(f'Raw result checksum mismatch: {name}')
        count = sum(1 for _ in (folder / 'runs.jsonl').open())
        if count != stamp['rows']:
            raise ValueError(f'Raw result row count mismatch: {name}')
    print('PASS: all bundled artifact bytes, frozen UCT sources and raw run counts', flush=True)


def tests():
    execute('-m', 'unittest', 'tests.test_compiled_retirement',
            'tests.test_onpolicy_backup', 'tests.test_retired_bounds', 'tests.test_reproduction')


def summaries(out, data=FROZEN):
    from paper import report_uct_backup as backup, report_uct_frontier as frontier
    from paper import uct_backup_gap as gap, uct_frontier_study as study
    data = Path(data).resolve()
    out = output_dir(out)
    for name in ('uct_backup_v1', 'uct_frontier_v1'):
        shutil.copytree(data / name, out / name, dirs_exist_ok=True)
    backup.report(out / 'uct_backup_v1')
    backup.report(out / 'uct_backup_v1/gap-study', [('gap-test', g) for g in gap.GAPS], gap.SEEDS)
    with patch(frontier, DEST=out / 'uct_frontier_v1'), patch(study, DEST=out / 'uct_frontier_v1'):
        frontier.run()
    if data != FROZEN:
        print(f'Summaries of fresh measurements written to {out}', flush=True)
        return
    expected = {
        'uct_backup_v1': ('certification.csv', 'wall_regret.csv', 'paired.csv'),
        'uct_backup_v1/gap-study': ('certification.csv', 'wall_regret.csv', 'paired.csv'),
        'uct_frontier_v1': ('per_graph.csv', 'summary.csv', 'wall_regret.csv', 'paired.csv', 'summary.json')}
    count = 0
    for folder, names in expected.items():
        for name in names:
            actual, saved = out / folder / name, FROZEN / folder / name
            same = (json.loads(actual.read_text()) == json.loads(saved.read_text())
                    if name.endswith('.json') else actual.read_bytes() == saved.read_bytes())
            if not same:
                raise ValueError(f'Regenerated summary differs: {folder}/{name}')
            count += 1
    print(f'PASS: {count} summaries match (CSV bytes; JSON values)', flush=True)


def tables(out):
    from paper import uct_backup_tables as backup, uct_frontier_tables as frontier
    out = output_dir(out)
    with patch(backup, PAPER=out):
        backup.run()
    # The frozen frontier writer builds ROOT/paper/certificates internally.
    scratch = out / 'frontier_writer'
    (scratch / 'paper/certificates').mkdir(parents=True, exist_ok=True)
    with patch(frontier, ROOT=scratch):
        frontier.run()
    for path in (scratch / 'paper/certificates').glob('*.tex'):
        shutil.copyfile(path, out / path.name)
    expected = list((ROOT / 'reference/tables').glob('*.tex'))
    for path in expected:
        # Generated TeX uses the host newline convention; compare its actual text.
        if (out / path.name).read_text() != path.read_text():
            raise ValueError(f'Regenerated table differs: {path.name}')
    print(f'PASS: {len(expected)} UCT tables match the manuscript', flush=True)


def figures(out, appendix=False, data=FROZEN):
    data = Path(data).resolve()
    out = output_dir(out)
    execute('paper/plot_uct_backup.py', '--data', data / 'uct_backup_v1', '--out', out)
    execute('paper/plot_uct_frontier.py', '--data', data / 'uct_frontier_v1', '--out', out)
    if appendix:
        execute('appendix/paper/plot_priced_search.py', '--data', ROOT / 'appendix/results',
                '--out', out / 'appendix')
    print(f'Figures written to {out}', flush=True)


def replay(study, out):
    verify()
    out = output_dir(out, fresh=True)
    if study in ('backup', 'all'):
        from paper import audit_uct_backup, uct_backup_gap
        audit_uct_backup.audit(replay=True)
        uct_backup_gap.verify(replay=True)
    if study in ('frontier', 'all'):
        from paper import uct_frontier_study as frontier
        target = out / 'uct_frontier_v1'
        target.mkdir()
        for name in ('manifest.json', 'runs.jsonl'):
            shutil.copyfile(FROZEN / 'uct_frontier_v1' / name, target / name)
        with patch(frontier, DEST=target):
            frontier.audit()
        got = [json.loads(line) for line in (target / 'coupling.jsonl').read_text().splitlines()]
        want = [json.loads(line) for line in (FROZEN / 'uct_frontier_v1/coupling.jsonl').read_text().splitlines()]
        if got != want:
            raise ValueError('Frontier coupling replay differs from frozen audit')
        print(f'PASS: {sum(row["steps"] for row in got):,} frontier rollout decisions replayed', flush=True)
    (out / 'passed.json').write_text(json.dumps({'study': study, 'matched_frozen_replays': True}, indent=2))


def diagnostics(kind, out):
    from paper import uct_frontier_study as frontier, uct_frontier_mechanism as mechanism
    out = output_dir(out, fresh=True)
    for name in ('manifest.json', 'runs.jsonl'):
        shutil.copyfile(FROZEN / 'uct_frontier_v1' / name, out / name)
    if kind == 'memory':
        with patch(frontier, DEST=out):
            frontier.audit(memory=True)
        print('Memory is a fresh measurement; it is not expected to be byte-identical.')
    else:
        with patch(mechanism, DEST=out):
            mechanism.run()
        got = [json.loads(x) for x in (out / 'mechanism.jsonl').read_text().splitlines()]
        want = [json.loads(x) for x in (FROZEN / 'uct_frontier_v1/mechanism.jsonl').read_text().splitlines()]
        if got != want:
            raise ValueError('Mechanism work replay differs')
        print('PASS: all matched-prefix work diagnostics')


def compare_summary(actual, expected, path='summary', roundoff=None):
    """Exact structure/counts; a tight tolerance for recomputed statistical floats."""
    if roundoff is None:
        roundoff = []
    if type(actual) is not type(expected):
        raise ValueError(f'Summary type mismatch at {path}')
    if isinstance(expected, dict):
        if actual.keys() != expected.keys():
            raise ValueError(f'Summary keys mismatch at {path}')
        for key in expected:
            compare_summary(actual[key], expected[key], f'{path}.{key}', roundoff)
    elif isinstance(expected, list):
        if len(actual) != len(expected):
            raise ValueError(f'Summary length mismatch at {path}')
        for i, (a, e) in enumerate(zip(actual, expected)):
            compare_summary(a, e, f'{path}[{i}]', roundoff)
    elif actual != expected:
        if not isinstance(expected, float) or not math.isclose(actual, expected, rel_tol=1e-12, abs_tol=1e-12):
            raise ValueError(f'Summary value mismatch at {path}: {actual!r} != {expected!r}')
        roundoff.append({'path': path, 'actual': actual, 'expected': expected,
                         'absolute_difference': abs(actual - expected)})
    return roundoff


def appendix_check(out):
    """Run legacy writers in a disposable copy, preserving the frozen archive."""
    out = output_dir(out, fresh=True)
    shutil.copytree(ROOT / 'appendix', out, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns('__pycache__'))
    for module in ('paper.report_ancestor_repair', 'paper.report_batched_repair'):
        execute('-m', module, cwd=out)
    roundoff = []
    for folder in ('ancestor_repair_replay_v2', 'batched_repair_v1'):
        got = json.loads((out / 'results' / folder / 'summary.json').read_text())
        saved = json.loads((ROOT / 'appendix/results' / folder / 'summary.json').read_text())
        compare_summary(got, saved, folder, roundoff)
    report = {'float_absolute_and_relative_tolerance': 1e-12,
              'exact_counts_and_structure': True, 'roundoff': roundoff}
    (out / 'summary_comparison.json').write_text(json.dumps(report, indent=2))
    print(f'PASS: historical summaries match; {len(roundoff)} statistical float roundoffs, '
          f'max absolute difference {max((r["absolute_difference"] for r in roundoff), default=0):.3g}; '
          'counts and frozen files unchanged', flush=True)


def benchmark(study, out, smoke=False):
    from paper import uct_backup_benchmark as backup, uct_backup_gap as gap
    from paper import uct_frontier_study as frontier
    out = output_dir(out, fresh=True)
    if study in ('backup', 'all'):
        values = {'DEST': out / 'uct_backup_v1'}
        if smoke:
            values.update(CASES=(('funnel', 16),), SEEDS=(421001,), WALL=(.001, .01, .1), CAP=2000)
        with patch(backup, **values):
            backup.run()
        if not smoke:
            with patch(gap, DEST=out / 'uct_backup_v1/gap-study', PRIMARY=out / 'uct_backup_v1'):
                gap.run()
    if study in ('frontier', 'all'):
        values = {'DEST': out / 'uct_frontier_v1'}
        if smoke:
            values.update(CASES=(('coded', 8), ('samegame', 4)), SEEDS=(433101,),
                          EFFORTS=(0,), WALL=(.001, .01, .1), CAP=2000)
        with patch(frontier, **values):
            frontier.run()
    (out / 'reproduction.json').write_text(json.dumps({'study': study, 'smoke': smoke,
        'note': 'Fresh measurements. Timings and capped rollout counts depend on the host.'}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('verify', 'test', 'quickcheck'):
        sub.add_parser(name)
    for name in ('summaries', 'tables', 'figures', 'replay', 'benchmark', 'memory', 'mechanism', 'appendix-check'):
        p = sub.add_parser(name)
        p.add_argument('--out', default=str(ROOT / 'build' / name))
        if name in ('benchmark', 'replay'):
            p.add_argument('--study', choices=('backup', 'frontier', 'all'), default='all')
        if name == 'benchmark':
            p.add_argument('--smoke', action='store_true')
        if name == 'figures':
            p.add_argument('--appendix', action='store_true')
        if name in ('figures', 'summaries'):
            p.add_argument('--data', default=str(FROZEN))
    args = parser.parse_args()
    if args.command == 'verify': verify()
    elif args.command == 'test': tests()
    elif args.command == 'summaries': summaries(args.out, args.data)
    elif args.command == 'tables': tables(args.out)
    elif args.command == 'figures': figures(args.out, args.appendix, args.data)
    elif args.command == 'replay': replay(args.study, args.out)
    elif args.command == 'benchmark': benchmark(args.study, args.out, args.smoke)
    elif args.command == 'appendix-check': appendix_check(args.out)
    elif args.command in ('memory', 'mechanism'): diagnostics(args.command, args.out)
    else:
        verify()
        tests()
        summaries(ROOT / 'build/summaries')
        tables(ROOT / 'build/tables')
        figures(ROOT / 'build/figures', appendix=True)
        execute('examples/certify.py')


if __name__ == '__main__':
    main()
