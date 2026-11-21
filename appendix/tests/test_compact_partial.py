"""Fused observation accounting and exact post-seal ranks."""
import unittest
from paper.wall_time_common import make_input
from paper.compact_partial import solver,CompactFrontier,scan_blocks
from paper.frontier_sampling import Work


class CompactTests(unittest.TestCase):
    def test_cover_scan_preserves_every_tied_block_and_charge(self):
        c,p=make_input('fragmented',1,1,173101)
        a=solver(p,c,173101,'range')
        for keys in ([8,8,8,8],[5,2,7,7],[4,3,2,1],[1,2,3,4],[]):
            nodes=list(range(len(keys)))
            a.idx.ut.value[:len(keys)]=keys
            before=a.w.total
            expected=a.idx.maxima(nodes)
            w=Work()
            self.assertEqual(scan_blocks(keys,w,nodes),expected)
            self.assertEqual(w.total,a.w.total-before)

    def test_fused_raw_intervals_and_reference_ledger_each_boundary(self):
        for price in (1,64):
            c,p=make_input('lattice',0,price,173101)
            old,fast=[solver(p,c,173101,m) for m in ('range','fast_range')]
            self.assertEqual(old.query(),fast.query())
            while not old.point[1]:
                k=5 if old.N==0 else 32
                self.assertEqual(old.step(k),fast.step(k))
                self.assertEqual(old.w.total+3,fast.w.total)
                self.assertEqual(old.ev.evaluations,fast.ev.evaluations)
                self.assertEqual(old.ev.lower,fast.ev.lower)
                self.assertEqual(old.ev.upper,fast.ev.upper)

    def test_partial_preserves_paid_draws_and_ranks_through_seal(self):
        for family in ('fragmented','fragmented_shoulder'):
            c,p=make_input(family,1,64,173101)
            old,fast=[solver(p,c,173101,m) for m in ('partial','fast_partial')]
            self.assertEqual(old.query(),fast.query())
            while not old.point[1]:
                obs,point=old.step(65536-old.w.oracle_calls)
                other,test=fast.step(65536-fast.w.oracle_calls)
                self.assertEqual(obs,other)
                self.assertEqual(point[:3],test[:3])
                if not point[1]:self.assertEqual(point,test)
            self.assertIsNotNone(fast.compact)
            self.assertEqual(old.idx.F,fast.idx.F)
            self.assertEqual(old.ev.counts,fast.ev.counts)
            self.assertEqual(old.idx.upper,fast.idx.upper)
            self.assertEqual(old.idx.lower,fast.idx.lower)

    def test_all_ties_and_terminal_bound_match_range(self):
        c,p=make_input('lattice',0,1,173101)
        a,b=[solver(p,c,113,'range') for _ in range(2)]
        members=list(reversed(range(0,len(a.g.leaves),7)))
        for s in (a,b):
            for j in range(len(s.g.leaves)):
                s.idx.publish(j,35 if j in members else 0,90 if j in members else 31)
            s.idx.install(members,32)
        compact=CompactFrontier(b.idx)
        for _ in range(150):
            ra,lo,x,y=a.idx.query()
            rb,lb,xx,yy=compact.query()
            self.assertEqual((ra,lo,x),(rb,lb,xx))
            if y[0]>=32:self.assertEqual(y,yy)
            else:self.assertEqual(yy,(32,None))
        self.assertGreater(len(compact.parts),1)

    def test_aborted_trial_refunds_replay_against_fast_range(self):
        c,p=make_input('fragmented',1,64,173101)
        a=solver(p,c,173101,'fast_partial')
        r=solver(p,c,173101,'fast_range')
        self.assertEqual(a.query(),r.query())
        while a.trial is None:
            before=a.idx.q
            result=a.step(65536)
            if a.idx.q!=before:self.assertEqual(result,r.step(65536))
            self.assertFalse(a.ended)
        a.budget=a.spent+a.draw_bound+40
        while a.trial:a.step(65536)
        self.assertEqual(a.meta['abort_hard'],1)
        while not r.point[1]:
            self.assertEqual(a.step(65536),r.step(65536))
        extra=24+a.monitor_cost+a.pilot_cost+a.meta['phase_work']+2*a.meta['buffered_draws']-64*a.meta['replays']
        self.assertEqual(a.w.total-r.w.total,extra)
        self.assertLessEqual(a.w.total,1.554*r.w.total+24)
