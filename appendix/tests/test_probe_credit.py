import json
import unittest
from pathlib import Path

from paper.neighbor_price_benchmark import fixtures as old_fixtures, config, DEST as old_dir
from paper.probe_credit_benchmark import fixtures, DEST
from paper.probe_credit import SweepBound
from paper.probe_credit_audit import audit,exception_floor
from paper.uniform_price_benchmark import Tape


class ProbeCreditTest(unittest.TestCase):
    def test_sweep_forecast_is_an_early_lower_bound(self):
        for s,g in old_fixtures():
            if s['layout']!='interleaved' or s['M'] not in (208,224):continue
            bound=SweepBound(g,config(s))
            tape=(old_dir/'ties-00.bin').read_bytes()
            full=audit(g,bound,Tape(tape),early=False)
            short=Tape(tape)
            first=audit(g,bound,short)
            self.assertEqual(first['score'],full['score'])
            self.assertTrue(first['covered'])
            expected={208:(109,132273,240484),224:(117,51219,248564)}
            self.assertEqual((first['sweep'],first['forecast'][0],exception_floor(bound,g)),expected[s['M']])
            self.assertLess(first['forecast'][0],full['probes'][0][1])
            # The certificate does not require any words after the sweep.
            replay=audit(g,bound,Tape(tape[:short.offset]))
            self.assertEqual(first,replay)

    def test_unclipped_loss_without_refinement(self):
        cases=json.loads((DEST/'probe_audit.json').read_text())
        s,g=next((s,g) for s,g in fixtures() if s['M']==236 and s['layout']=='interleaved')
        case=next(r for r in cases if r['graph']==s['name'] and r['gap']<0)
        data=(DEST/f"ties-{case['tape']:02}.bin").read_bytes()
        bound=SweepBound(g,config(s))
        score=audit(g,bound,Tape(data),early=False)
        self.assertFalse(score['covered'])
        self.assertLess(score['probes'][0][1],0)
        self.assertEqual(score['refinements'],0)
        self.assertLessEqual(-bound.loss_bound(),score['score'])
        self.assertLessEqual(score['score'],case['gap'])
        self.assertLessEqual(case['gap']-score['score'],128)

