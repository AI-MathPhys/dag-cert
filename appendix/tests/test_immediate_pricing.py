"""Check the exact scan price, strict tie boundary and final cursor separately."""
import unittest
from types import SimpleNamespace

from paper.ancestor_repair_replay import Profile
from paper.immediate_pricing import ImmediateTree


class ImmediatePriceTests(unittest.TestCase):
    def test_endpoint_and_fallback_tariffs_in_both_directions(self):
        tree = SimpleNamespace(size=4, value=[0, 10, 4, 10, 2, 4, 3, 10])
        for increasing in (True, False):
            for keys, ambiguous in (([1, 2, 4, 6], True), ([1, 2, 2, 3], False)):
                keys = keys if increasing else keys[::-1]
                events = [(key, key) for key in keys]
                profile = Profile(tree, (0, 2), increasing)
                start = profile.cursor[0]
                mid, _, c0 = profile.lookup(0, keys[0], start)
                end, _, c1 = profile.lookup(0, keys[-1], mid)
                pos = start
                expected_pulls = scan = 0
                for key, peer in events:
                    pos, cold, cost = profile.lookup(0, key, pos)
                    expected_pulls += profile.depth(cold, peer, key)
                    scan += cost + 5
                result = ImmediateTree.price_group(SimpleNamespace(profile=profile), 0, events,
                                                   keys[0], keys[-1])
                self.assertEqual(result, (expected_pulls, c0+c1+14+(scan if ambiguous else 0)))
                self.assertEqual(profile.cursor[0], end)
                self.assertEqual(end, pos)
