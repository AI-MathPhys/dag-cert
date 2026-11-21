"""Partial seal correctness, stopping alternatives, and rollback accounting."""
import unittest

from paper.escrow_benchmark import config,problem
from paper.frontier_sampling import Search
from paper.partial_clearing import PartialSearch


class PartialTests(unittest.TestCase):
    def launch(self, seed=162102):
        c=config('fragmented',1,64)
        p=problem(c,seed)
        g=PartialSearch(p,c,seed,'partial')
        r=Search(p,c,seed,'range_lucb32')
        self.assertEqual(g.query(),r.query())
        while not g.meta['launch']:
            old=g.idx.q
            obs,point=g.step(65536)
            if old!=g.idx.q:
                self.assertEqual((obs,point),r.step(65536))
            self.assertFalse(point[1])
        return g,r

    def test_unresolved_retained_members_and_failed_witnesses(self):
        g,_=self.launch()
        initial=set(g.trial.retained)
        theta=g.trial.theta
        while g.trial:
            g.step(65536)
        self.assertTrue(initial)
        self.assertEqual(g.meta['seal'],1)
        self.assertTrue(initial<=set(g.idx.F))
        self.assertTrue(any(g.idx.lower[j]<theta<=g.idx.upper[j] for j in initial))
        while not g.point[1]:
            a,_,lo,x,y=g.point
            inside={j for l,h in g.idx.top.inside[a] for j in range(l,h)}
            outside=set(range(len(g.idx.upper)))-inside
            self.assertIn(x[1],inside)
            self.assertIn(y[1],outside)
            self.assertEqual(x[0],max(g.idx.upper[j] for j in inside))
            self.assertEqual(y[0],max(g.idx.upper[j] for j in outside))
            g.step(65536)
        self.assertTrue(all(u<theta or j in g.idx.F for j,u in enumerate(g.idx.upper)))

    def test_hard_abort_matches_full_work_identity_at_price_64(self):
        g,r=self.launch()
        g.budget=g.spent+g.draw_bound+40
        while g.trial:
            g.step(65536)
        self.assertEqual(g.meta['abort_hard'],1)
        self.assertLessEqual(g.meta['phase_work'],g.budget)
        while not r.point[1]:
            self.assertEqual(g.step(65536),r.step(65536))
        extra=24+g.monitor_cost+g.pilot_cost+g.meta['phase_work']+2*g.meta['buffered_draws']-64*g.meta['replays']
        self.assertEqual(g.w.total-r.w.total,extra)
        self.assertLessEqual(g.w.total,1.554*r.w.total+24)

    def test_tight_budget_seals_all_possible_members_instead_of_aborting(self):
        g,_=self.launch()
        while g.trial.possible_size>g.idx.cap:
            g.trial_step(1)
        t=g.trial
        self.assertTrue(t.todo)
        candidates=t.possible_size
        g.budget=g.spent+g.draw_bound
        g.trial_step(1)
        self.assertEqual(g.meta['salvage'],1)
        self.assertEqual(g.meta['frontier_size'],candidates)
        self.assertTrue(all(j in g.idx.F or u<g.idx.threshold for j,u in enumerate(g.idx.upper)))

    def test_progress_veto_abandons_large_frontier(self):
        g,r=self.launch()
        while g.trial.samples<64:
            g.trial_step(32)
        g.trial.total_pred=10**12
        g.trial.holding_price=10**12
        g.budget=2*g.spent
        g.trial_step(32)
        self.assertEqual(g.meta['abort_progress'],1)
        self.assertEqual(g.step(65536),r.step(65536))

    def test_pending_leaf_can_be_parked_without_claiming_it_is_high(self):
        g,_=self.launch()
        t=g.trial
        while t.current_count<32 and t.possible_size>g.idx.cap:
            g.trial_step(1)
        self.assertGreaterEqual(t.current_count,32)
        j=t.todo[-1]
        # Isolate the branch's retention-price comparison on a real interval.
        t.holding_price=0
        g.trial_step(1)
        self.assertIn(j,t.retained)
        while g.trial:
            g.step(65536)
        self.assertIn(j,g.idx.F)
        self.assertGreaterEqual(g.meta['parks'],1)
