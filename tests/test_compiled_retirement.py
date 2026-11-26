import unittest
from joint_root_cert import DAG,Problem
from joint_root_cert._core.compiled_retirement import Search,cover_compile
from joint_root_cert._core.certified_uct import UCTWork
from experiment.simulated.passive_uct.audit_uct_backup import direct
from experiment.simulated.passive_uct.uct_frontier_families import make,describe

class CompiledTest(unittest.TestCase):
    def test_coupled_noncontiguous_overlap(self):
        p=Problem('overlap',DAG(((1,2,3),(4,6),(5,6),(4,5,6),(),(),())),{4:.9,5:.3,6:.1},(4,5,6))
        lanes=[Search(p,900,m,.1) for m in ('graph-eager','graph-live','cover-live','covers')]
        for t in range(15000):
            val=[x.step() for x in lanes]
            self.assertTrue(all(x==val[0] for x in val))
            q=direct(p.graph,lanes[0].monitor.evidence)
            self.assertTrue(all(x.query==q for x in lanes))
            if lanes[0].certified:break
        self.assertTrue(lanes[0].certified)
        self.assertGreater(lanes[2].monitor.bounds.retired,0)

    def test_coded_signatures_and_distinct_supports(self):
        for k in (4,8):
            p,e=make('coded',k,900)
            d=describe(p)
            self.assertEqual(d['unique_supports'],4*(k-1)+1)
            signatures=[]
            for i in range(k):
                for j in range(k):
                    signatures.append(tuple((a&coord).bit_count()%2==parity for coord in (i,j)
                                            for a in range(1,k) for parity in (0,1)))
            self.assertEqual(min(sum(a!=b for a,b in zip(x,y)) for i,x in enumerate(signatures)
                                 for y in signatures[i+1:]),k)
    def test_natural_rewards_and_truth(self):
        p,e=make('samegame',4,431002)
        self.assertTrue(all(0<=v<=1 for v in p.means.values()))
        oracle=p.oracle(900)
        self.assertTrue(all(0<=oracle.sample(j)<=1 for j in p.graph.leaves for _ in range(20)))

    def test_quotient_removes_funnel(self):
        p,e=make('funnel',64,900)
        lane=Search(p,900,'graph-live',e)
        self.assertLess(lane.monitor.info['edges'],10)
    def test_cost_surcharge_keeps_tape(self):
        p,e=make('coded',4,900)
        a,b=Search(p,900,'cover-live',e,0),Search(p,900,'cover-live',e,5)
        for i in range(100):
            self.assertEqual(a.step(),b.step())
        self.assertEqual(b.work-a.work,1500)

if __name__=='__main__':unittest.main()

