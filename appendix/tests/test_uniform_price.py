import struct
import unittest
from types import SimpleNamespace

from paper.ancestor_repair_replay import Profile
from paper.immediate_pricing import ImmediateTree
from paper.uniform_price_benchmark import Tape
from paper.uniform_price_proof import group_lower


class UniformPriceTests(unittest.TestCase):
    def test_uniform_rank_rejects_incomplete_residue_class(self):
        rng = Tape(struct.pack('<III', 2**32-1, 5, 0))
        self.assertEqual(rng.randrange(3), 2)
        self.assertEqual(rng.offset, 8)
        self.assertEqual(rng.randrange(1), 0)

    def test_transition_bound_against_production_scan_ledger(self):
        for inc in (True,False):
            for gap in (0,3,20):
                keys = [8,8+gap,4,0,2,3,7,7]
                pair = (0,1)
                direction = 1 if inc else -1
                replacements = [keys[j]+direction*6 for j in pair]
                updates = []
                events_by_side = []
                for j in pair:
                    changes = [max(keys[j]+direction*i, keys[j]+direction*(i+1)) for i in range(6)]
                    # Alternate draws, side 0 first.
                    events = [(k,keys[1-j]+direction*(i+j)) for i,k in enumerate(changes)]
                    events_by_side.append(events)
                    updates.append((replacements[j],replacements[j],None,(changes,changes)))
                tree = SimpleNamespace(size=8,value=[0]*8 + keys)
                for node in range(7,0,-1):
                    tree.value[node]=max(tree.value[2*node:2*node+2])
                p = Profile(tree,pair,inc)
                charge=0
                for side,events in enumerate(events_by_side):
                    start=p.cursor[side]
                    mid,_,c0=p.lookup(side,events[0][0],start)
                    _,_,c1=p.lookup(side,events[-1][0],mid)
                    _,cost=ImmediateTree.price_group(SimpleNamespace(profile=p),side,events,
                                                     keys[1-side],replacements[1-side])
                    scan=cost-c0-c1-14
                    if scan:
                        charge+=scan-32-3*len(events)-4*p.h
                self.assertLessEqual(group_lower(keys,pair,updates,inc,p.h),charge)
