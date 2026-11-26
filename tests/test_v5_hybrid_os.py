import unittest

from dagcert import DAG, Problem
from dagcert.benchmarks import contiguous_window_dag, overlap_dag, structural_diagnostics
from dagcert import ActiveDAGLUCBSession
from dagcert.tracking import InsideWitnessDAGLUCBSession
from dagcert._core.v5_hybrid_and_os import (
    HybridWitnessDAGLUCBSession,
    noncontainment_star_dag,
)


class V5HybridAndOSTests(unittest.TestCase):
    def test_dual_witness_covers_bit_exact_parity_with_ucb_and_scanned_lcb(self):
        for prob, eps in (
            overlap_dag(64, 0.75, 0.32, 701001, noisy=True),
            contiguous_window_dag(64, 8, 701002, noisy=True),
        ):
            # 1. Exact UCB-inside parity with ActiveDAGLUCBSession
            s_ref_ucb = ActiveDAGLUCBSession(prob, 42, "dual-covers", eps, delta=0.05, schedule="box")
            s_new_ucb = HybridWitnessDAGLUCBSession(prob, 42, eps, mode="ucb", delta=0.05, schedule="box")
            while not s_ref_ucb.certified and s_ref_ucb.calls < 4000:
                p1, r1 = s_ref_ucb.step()
                p2, r2 = s_new_ucb.step()
                self.assertEqual(p1, p2)
                self.assertEqual(r1, r2)
                self.assertEqual(s_ref_ucb.certified, s_new_ucb.certified)
            self.assertEqual(s_ref_ucb.action, s_new_ucb.action)
            self.assertEqual(s_ref_ucb.calls, s_new_ucb.calls)

            # 2. Exact LCB-inside parity with InsideWitnessDAGLUCBSession('lcb')
            s_ref_lcb = InsideWitnessDAGLUCBSession(prob, 42, eps, inside_mode="lcb", delta=0.05, schedule="box")
            s_new_lcb = HybridWitnessDAGLUCBSession(prob, 42, eps, mode="lcb_fast", delta=0.05, schedule="box")
            while not s_ref_lcb.certified and s_ref_lcb.calls < 4000:
                p1, r1 = s_ref_lcb.step()
                p2, r2 = s_new_lcb.step()
                self.assertEqual(p1, p2)
                self.assertEqual(r1, r2)
                self.assertEqual(s_ref_lcb.certified, s_new_lcb.certified)
            self.assertEqual(s_ref_lcb.action, s_new_lcb.action)
            self.assertEqual(s_ref_lcb.calls, s_new_lcb.calls)

    def test_hybrid_escapes_decoy_lockin_where_lcb_stalls(self):
        # Same rival-tied private decoy construction as test_v4_baselines:
        # Action 0 -> {3: 0.75 (decoy), 4: 0.95 (winner)}, Action 1 -> {5: 0.75}
        g = DAG(((1, 2), (3, 4), (5,), (), (), ()))
        prob = Problem("decoy_hybrid_test", g, {3: 0.75, 4: 0.95, 5: 0.75}, g.leaves)
        eps = 0.02

        s_lcb = HybridWitnessDAGLUCBSession(prob, 7, eps, mode="lcb_fast", delta=0.05, schedule="box")
        s_hyb = HybridWitnessDAGLUCBSession(prob, 7, eps, mode="hybrid", delta=0.05, schedule="box")

        for s in (s_lcb, s_hyb):
            while not s.certified and s.calls < 5000:
                s.step()

        self.assertFalse(s_lcb.certified)
        self.assertEqual(s_lcb.calls, 5000)
        self.assertTrue(s_hyb.certified)
        self.assertEqual(s_hyb.action, 0)
        self.assertLess(s_hyb.calls, 4000)

    def test_optimistic_separation_exact_eps0_on_noncontainment_star(self):
        prob, _ = noncontainment_star_dag(n_rivals=4, gap=0.35, eps=0.0)
        diag = structural_diagnostics(prob.graph)
        self.assertEqual(diag["containment_pairs"], 0)
        vals = prob.graph.optimal_values(prob.means)
        root_vals = [vals[c] for c in prob.graph.children[prob.graph.root]]
        # Every root action is optimal (tied at 0.5)
        self.assertTrue(all(abs(v - 0.5) < 1e-12 for v in root_vals))

        # At eps = 0.0, Optimistic-Separation DAG-LUCB (Theorem 3.2) certifies finitely!
        s_os = HybridWitnessDAGLUCBSession(prob, 703001, 0.0, mode="opt_sep", delta=0.05, schedule="box")
        while not s_os.certified and s_os.calls < 8000:
            s_os.step()
        self.assertTrue(s_os.certified)
        self.assertEqual(s_os.action, 4)  # Only S_A = {p, q} (placed last at index 4) contains both best terminals!


if __name__ == "__main__":
    unittest.main()
