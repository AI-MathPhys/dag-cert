import unittest

from paper.neighbor_price_benchmark import fixtures, config
from paper.neighbor_price_condition import HotCurve, dominant_revisions, predict
from paper.neighbor_price_family import neighbor_family
from paper.structural_price_graphs import switched


def scripted_curve(lower,upper,last_low_threshold,last_upper_threshold):
    curve = HotCurve.__new__(HotCurve)
    curve.warm = 1
    curve.lower = lower
    curve.upper = upper
    curve.smallest = [[0,0,last_low_threshold],[0,0,last_upper_threshold]]
    curve.count = [[0,0,16],[0,0,16]]
    return curve


class NeighborPriceTest(unittest.TestCase):
    def test_overlap_and_tie_in_production_guard(self):
        # A single possible allocation at the sweep, followed by one block.
        w = scripted_curve([0,2,5],[10,8,4],3,5)
        r = scripted_curve([0,3,4],[10,7,6],4,7)
        got,crossings = dominant_revisions((w,r),2,1,(3,))
        self.assertEqual((got[3],crossings[3]),(0,2))
        w.smallest[1][2] = r.upper[1]
        got,crossings = dominant_revisions((w,r),2,1,(3,))
        self.assertEqual((got[3],crossings[3]),(16,1))

    def test_group_counts_and_whole_sibling_orbit(self):
        for spec,g in fixtures():
            cfg = config(spec)
            z = predict(g,cfg)
            other = switched(g,[True]*(spec['M']//2))
            self.assertEqual(z,predict(other,cfg))
            if 'leaders' in z:
                for q,B,D in zip((256,512),z['overlap'],z['leaders']):
                    # On these complements the initial sweep bound is common.
                    sweep = (3*spec['M'])//4+5
                    self.assertGreaterEqual(D,16*(2*(q-1-sweep)-B))
        for m,bound,early in [(176,198,107829),(192,246,5781)]:
            result = neighbor_family(m)
            self.assertEqual(result['bound'],bound)
            self.assertEqual(result['clips'][0],early)
            self.assertEqual(result['crossings'],[4,4])

