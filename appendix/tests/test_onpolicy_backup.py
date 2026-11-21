import unittest

from dag_mcts.graph import DAG,Problem
from dag_mcts.onpolicy_backup import CompiledCovers,MonitoredUCT
from paper.audit_uct_backup import direct
from paper.uct_backup_benchmark import METHODS
from paper.uct_backup_families import fixture,funnel,wide_core


class OnlineBackupTests(unittest.TestCase):
    def test_compiled_shared_and_noncontiguous_supports(self):
        # Actions 0 and 1 have identical supports, and action 2 overlaps both.
        graph = DAG([(1,2,3),(4,6),(4,6),(5,6),(),(),()])
        monitor = CompiledCovers(graph,.05)
        self.assertEqual(len(monitor.covers),2)
        for i in range(100):
            for leaf,reward in ((4,.85),(5,.10),(6,.4)):
                monitor.step(leaf,reward)
                self.assertEqual(monitor.query(),direct(graph,monitor.evidence))

    def test_path_coupled_through_first_certificate(self):
        p,eps = funnel(16,7,exits=2)
        lanes = [MonitoredUCT(p,7,m,eps) for m in METHODS]
        while not lanes[0].certified:
            events=[l.step() for l in lanes]
            self.assertTrue(all(event==events[0] for event in events))
            self.assertEqual(len({(l.action,l.query,l.certified) for l in lanes}),1)
            self.assertEqual(lanes[0].query,direct(p.graph,lanes[0].monitor.evidence))
        self.assertLess(lanes[0].uct.calls,10000)
        for l in lanes:
            self.assertEqual(l.uct.counts,lanes[0].uct.counts)
            self.assertEqual(l.oracle.counts,{j:l.uct.leaf_counts[j] for j in p.graph.leaves})

    def test_moving_fanout_preserves_root_rollouts(self):
        low,eps = funnel(8,13)
        best,_ = funnel(8,13,placement='best')
        a,b = [MonitoredUCT(p,17,'live',eps) for p in (low,best)]
        while not a.certified:
            pa,ra = a.step()
            pb,rb = b.step()
            self.assertEqual((low.graph.children[0].index(pa[1]),pa[-1],ra),
                             (best.graph.children[0].index(pb[1]),pb[-1],rb))
            self.assertEqual((a.action,a.query,a.certified),(b.action,b.query,b.certified))
        win_cone = next(c for c in best.graph.children[0] if best.graph.children[c])
        self.assertTrue(b.monitor.bounds.live[win_cone])

    def test_cross_action_bypass_is_one_evidence_stream(self):
        base,eps=funnel(16,18,exits=2)
        rows=list(base.graph.children)
        rows[0]=rows[0]+(3,)
        graph=DAG(rows)
        p=Problem('bypass',graph,base.means,graph.leaves)
        lanes=[MonitoredUCT(p,18,m,eps) for m in METHODS]
        routes=set()
        while not lanes[0].certified:
            events=[l.step() for l in lanes]
            self.assertTrue(all(event==events[0] for event in events))
            self.assertEqual(len({(l.query,l.action,l.certified) for l in lanes}),1)
            if events[0][0][-1]==3:
                routes.add(events[0][0][1])
        self.assertEqual(len(routes),2)
        for l in lanes:
            self.assertEqual(l.monitor.evidence.counts[3],l.oracle.counts[3])

    def test_materialized_vs_factored_sizes(self):
        r=8
        p,eps=wide_core(r,31)
        flat=MonitoredUCT(p,31,'flat',eps)
        cover=MonitoredUCT(p,31,'covers',eps)
        self.assertEqual(flat.monitor.compiled_edges,(r+1)+1+r*(r*r+1))
        self.assertLess(cover.monitor.entries,flat.monitor.compiled_edges)

