import itertools
import unittest

from paper.decision_price_benchmark import config
from paper.immediate_pricing import ImmediateCompact
from paper.report_structural_price import logical_signature, simple_clipping
from paper.structural_price_benchmark import fixtures
from paper.structural_price_condition import check, cold_records, pair_bounds
from paper.structural_price_graphs import switched


class StructuralPriceTest(unittest.TestCase):
    def test_free_owner_assignments(self):
        from paper.structural_price_family import complementary_pairs
        self.assertEqual([complementary_pairs(m)['bound'] for m in (176,192)],[198,246])

    def test_interval_extrema_against_production_covers(self):
        spec, graph = next(fixtures())
        engine = ImmediateCompact(graph,config(spec),1)
        tree = engine.idx.ut
        for original in itertools.product((0,1), repeat=6):
            fees, runs = [], []
            for orientations in itertools.product((0,1), repeat=3):
                seq = [original[j ^ orientations[j//2]] for j in range(6)]
                ranges = [[],[]]
                start = 0
                for end in range(1,len(seq)+1):
                    if end==len(seq) or seq[end]!=seq[start]:
                        ranges[seq[start]].append((start,end))
                        start=end
                before = tree.w.total
                tree.cover(ranges[0])
                tree.cover(ranges[1])
                fees.append(tree.w.total-before+2)
                runs.append(len(ranges[1]))
            self.assertEqual(pair_bounds(original,tree.size),(max(fees),min(runs),max(runs)))

    def test_one_key_per_cover_block_with_ties(self):
        # Blocks {0,1}, {2,3}, {4,5}, in descending production order.
        for values in itertools.product((0,1),repeat=6):
            choices = [{None,values[j],values[j+1]} for j in (4,2,0)]
            lengths = []
            for sequence in itertools.product(*choices):
                keys = [v for v in sequence if v is not None]
                if keys==sorted(keys):
                    lengths.append(len(keys))
            self.assertEqual(cold_records((6,5,4),8,dict(enumerate(values))),max(lengths))

    def test_whole_sibling_orbit_certificate(self):
        for spec,graph in fixtures():
            cfg = config(spec)
            z = check(graph,cfg)
            opposite = switched(graph,[True]*(spec['M']//2))
            self.assertEqual(logical_signature(opposite), logical_signature(graph))
            self.assertEqual(check(opposite,cfg), z)
            expected = {'spread':'deferred','short-runs':'immediate','neighbors':'abstain'}
            self.assertEqual(z['sign'],expected[spec['layout']])
            if z['sign']=='deferred':
                self.assertTrue(all(margin>0 for margin in simple_clipping(spec,graph,z)))

