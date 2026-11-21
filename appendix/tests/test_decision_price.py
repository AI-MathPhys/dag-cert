"""Indivisible threshold equality and ambiguity that requires paid refinement."""
import unittest
from types import SimpleNamespace
from paper.ancestor_repair_replay import Profile
from paper.decision_price import RepairBounds


class DecisionPriceTests(unittest.TestCase):
    def test_equality_refines_once_and_reuses_result(self):
        # Pair in distinct halves. At depth one the changing leaf ties its
        # immutable sibling on one event; ties can change the tie count.
        tree=SimpleNamespace(size=4,value=[0,10,4,10,2,4,3,10])
        profile=Profile(tree,(0,2),True)
        events=((3,3),(4,3))
        b=RepairBounds(SimpleNamespace(extra=0))
        b.base=120
        b.cap=100
        b.defer(profile,0,0,events,1,2)
        self.assertEqual(b.interval(),(40,48))
        self.assertTrue(b.decide(lambda v: v>=40))
        self.assertEqual(b.account.refinements,0)
        self.assertTrue(b.decide(lambda v: v>=44))
        self.assertEqual(b.account.refinements,1)
        self.assertEqual(b.interval(),(44,44))
        self.assertFalse(b.decide(lambda v: v>44))
        self.assertEqual(b.account.refinements,1)

    def test_scan_credit_clips_every_possible_price(self):
        b=RepairBounds(SimpleNamespace(extra=0))
        b.base,b.width,b.cap=300,120,80
        self.assertEqual(b.interval(),(80,80))
        self.assertTrue(b.decide(lambda v: v<=80))
        self.assertEqual(b.account.refinements,0)


if __name__=='__main__':
    unittest.main()
