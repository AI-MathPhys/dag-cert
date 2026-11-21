import json
import random
import unittest

from paper.fragment_sign_audit import RankBits, audit
from paper.fragment_sign_bounds import originals
from paper.fragment_sign_benchmark import DEST


class FragmentSignTests(unittest.TestCase):
    def test_recorded_bits_reject_and_couple(self):
        # First two bits encode 3 and are rejected at width three. Next two encode 2.
        tape=RankBits(bytes([11]))
        self.assertEqual(tape.randrange(1),0)
        self.assertEqual(tape.randrange(3),2)
        self.assertEqual(tape.bits,4)

    def test_prefix_bound_encloses_full_return_with_both_launch_types(self):
        study=DEST.parent/'immediate_pricing_v1/runs.jsonl'
        cases={378001:'confirm-192-378001-378101',378004:'confirm-256-378004-378101'}
        rows=[json.loads(s) for s in study.read_text().splitlines()]
        for spec in originals():
            if spec['seed'] not in cases:continue
            pair={r['method']:r for r in rows if r['case']==cases[spec['seed']] and r['repeat']==0}
            result=audit(spec,random.Random(378101+791901))
            gap=pair['immediate']['work']-pair['threshold']['work']
            self.assertLessEqual(result['low'],gap)
            self.assertLessEqual(gap,result['high'])
            self.assertEqual(result['exact'],spec['seed']==378001)

