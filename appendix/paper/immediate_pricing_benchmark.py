"""Cold three-method comparisons. Run serially from the project root."""
import json
import platform
import random
from unittest.mock import patch

from paper.decision_price import ENGINES
from paper.decision_price_benchmark import (BUDGET, DRAWS, SECONDS, ROOT, config, digest,
                                            factory, population, solve)
from paper.immediate_pricing import ImmediateCompact

DEST = ROOT / 'results/immediate_pricing_v1'
METHODS = ('reference', 'immediate', 'threshold')


def inputs():
    for obj in population():
        if obj['tag'] in ('cohort', 'fresh'):
            graph = obj['case'] if obj['tag'] == 'cohort' else obj['case'].rsplit('-', 1)[0]
            yield dict(obj, graph=graph)
    for i, size in enumerate((192, 224, 224, 256)):
        spec = dict(family='layout4', M=size, A=4, good=2, eps=1/80, law='constant',
                    profile='sharp', seed=378001+i, cohort='confirmation')
        for tie in range(378101, 378105):
            graph = f'confirm-{size}-{spec["seed"]}'
            yield dict(tag='confirmation', graph=graph, case=f'{graph}-{tie}',
                       s=spec, tie=tie, reps=2)


def run():
    DEST.mkdir(exist_ok=False)
    specs = list(inputs())
    rng = random.Random(378877)
    blocks = []
    for obj in specs:
        order = list(METHODS)
        rng.shuffle(order)
        blocks.extend([(obj, 0, order), (obj, 1, order[::-1])])
    rng.shuffle(blocks)
    files = ('paper/immediate_pricing.py', 'paper/immediate_pricing_benchmark.py',
             'paper/immediate_pricing_protocol.txt', 'paper/decision_price.py',
             'paper/batched_repair.py', 'paper/repair_policy_clock.py')
    manifest = dict(caps=[BUDGET, DRAWS, SECONDS], methods=METHODS, specs=specs,
                    repetitions=2, order_seed=378877, python=platform.python_version(),
                    platform=platform.platform(), sources={f:digest(ROOT/f) for f in files})
    (DEST/'manifest.json').write_text(json.dumps(manifest, indent=2))
    count = 0
    with patch.dict(ENGINES, immediate=ImmediateCompact), (DEST/'runs.jsonl').open('x') as out:
        for i, (obj, rep, order) in enumerate(blocks, 1):
            for position, method in enumerate(order):
                result = solve(factory(obj['s']), config(obj['s']), obj['tie'], method)
                result.update(tag=obj['tag'], graph=obj['graph'], case=obj['case'], repeat=rep,
                              position=position, tie=obj['tie'], method=method)
                out.write(json.dumps(result)+'\n')
                out.flush()
                count += 1
            if i % 50 == 0:
                print(i, '/', len(blocks), flush=True)
    assert count == len(specs)*2*len(METHODS)
    (DEST/'complete.json').write_text(json.dumps(dict(rows=count, sha256=digest(DEST/'runs.jsonl'))))


if __name__=='__main__':
    run()
