import unittest
from fractions import Fraction
from types import SimpleNamespace
from paper.prefix_information import race
from paper.prefix_routing import KnownRangeSelector,OnlineSelector


def empty(cls):
    s=cls.__new__(cls)
    s.route=None
    s.trial=None
    s.account=SimpleNamespace(selector_work=0)
    s.meta={'inspected':0}
    if cls is OnlineSelector:s.sampled={}
    return s


class PrefixTests(unittest.TestCase):
    def test_known_support_is_strict_and_stops_inspection(self):
        for x,route in ((.1,'credit-all'),(.34,'bare')):
            s=empty(KnownRangeSelector)
            s.inspect([(0,r,None) for r in (0,1,.14,.3,.70,x,.12)])
            self.assertEqual(s.route,route)
            self.assertEqual(s.meta['inspected'],6)
            self.assertEqual(s.account.selector_work,6*8+8)

    def test_fallback_and_pooled_terminal_statistic(self):
        s=empty(KnownRangeSelector)
        s.inspect([(1,.22,None)])
        s.finish_prefix()
        self.assertEqual((s.route,s.meta['prefix_reason']),('bare','fallback'))
        for k,route in ((3,'bare'),(4,'credit-all')):
            s=empty(OnlineSelector)
            s.inspect([(i,.20,None) for i in range(k) for _ in range(4)])
            s.finish_prefix()
            self.assertEqual(s.route,route)
            self.assertFalse(s.sampled)

    def test_exact_raw_and_indexed_prices(self):
        r=race()
        self.assertEqual(r['count_cut'],4)
        self.assertEqual(Fraction(r['raw_exact']['1']),Fraction(r['constant']))
        self.assertEqual(Fraction(r['raw_exact']['0']),Fraction(r['free_count']))
        self.assertGreater(r['gross_count_value'],1)


if __name__=='__main__':unittest.main()
