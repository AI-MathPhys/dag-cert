"""Unit tests for v2 nested-box monitors, exact shared-support regret, and PUCT policies."""
from __future__ import annotations

import math
import random
import unittest

from dag_mcts.certified_uct import UCTWork
from dag_mcts.graph import DAG, Problem
from dag_mcts.puct import CertifiedSearchSession, RecursivePUCT, RootPUCT, build_monitor, make_priors
from dag_mcts.v2_benchmarks import (
    contiguous_window_dag,
    overlap_dag,
    puct_noisy_funnel,
    puct_root_funnel,
    samegame_depth_case,
    samegame_standard_endgame,
    structural_diagnostics,
)
from dag_mcts.v2_monitors import (
    ChargedDualCovers,
    DirectGraphRegretMonitor,
    FactorizedRegretMonitor,
    IndexedMinHeap,
    MarginalGraphMonitor,
    NestedDyadicCovers,
    NestedIntervals,
    brute_force_exact_regret,
    brute_force_marginal,
)
from paper.uct_frontier_families import coded


class V2ExtensionsTests(unittest.TestCase):
    def test_indexed_min_heap_tie_breaking_and_updates(self):
        w = UCTWork()
        h = IndexedMinHeap([0.4, 0.2, 0.2, 0.5], w)
        self.assertEqual(h.top, 1)
        h.update(1, 0.3)
        self.assertEqual(h.top, 2)
        h.update(3, 0.1)
        self.assertEqual(h.top, 3)
        h.update(0, 0.1)
        # Canonical lowest-ID tie-breaking: item 0 beats item 3 on exact tie!
        self.assertEqual(h.top, 0)

    def test_nested_intervals_monotonicity_and_conflict(self):
        g = DAG(((1, 2), (), ()))
        w = UCTWork()
        ev = NestedIntervals(g, w, delta=0.05, schedule="box")
        rng = random.Random(42)
        prev_l, prev_u = 0.0, 1.0
        for _ in range(150):
            r = float(rng.random() < 0.65)
            ev.observe(1, r)
            self.assertFalse(ev.conflict)
            self.assertGreaterEqual(ev.lower[1], prev_l)
            self.assertLessEqual(ev.upper[1], prev_u)
            prev_l, prev_u = ev.lower[1], ev.upper[1]

        # Force non-stationary adversarial switch (100 ones then 100 zeros) to trigger conflict alarm
        ev2 = NestedIntervals(g, UCTWork(), delta=0.25, schedule="box")
        for _ in range(100):
            ev2.observe(1, 1.0)
        for _ in range(200):
            ev2.observe(1, 0.0)
        self.assertTrue(ev2.conflict)

    def test_numerical_and_decision_oracle_equivalence_step_by_step(self):
        problem, eps = overlap_dag(64, 0.50, 0.42, seed=600101, noisy=True)
        numerical_methods = ("graph-eager", "protected-selective", "quotient-protected", "dyadic-covers")
        sessions = [
            CertifiedSearchSession(problem, 600101, "uct", m, eps, delta=0.05, c_explore=3.0, q_cert=1)
            for m in (*numerical_methods, "decision-selective")
        ]
        while not sessions[0].certified and sessions[0].calls < 30000:
            steps = [s.step() for s in sessions]
            self.assertTrue(all(st == steps[0] for st in steps))
            c_step = sessions[0].calls
            # All numerical monitors match query leader, gap, stopping bit, and action on every rollout
            base_q = sessions[0].query
            for s in sessions[1:4]:
                self.assertEqual(s.query[0], base_q[0])
                self.assertAlmostEqual(s.query[1], base_q[1], places=12)
                self.assertEqual(s.certified, sessions[0].certified)
                self.assertEqual(s.action, sessions[0].action)
            # Decision-selective matches canonical leader and stopping bit on every step!
            dec = sessions[4]
            self.assertEqual(dec.query[0], base_q[0])
            self.assertEqual(dec.certified, sessions[0].certified)
            if dec.certified:
                self.assertEqual(dec.action, sessions[0].action)
            if c_step <= 32 or (c_step & (c_step - 1)) == 0 or c_step % 64 == 0 or sessions[0].certified:
                ev = sessions[0].monitor.evidence
                ref_leader, ref_gap, ref_intervals = brute_force_marginal(problem.graph, ev.lower, ev.upper)
                for s in sessions[:3]:
                    self.assertEqual(s.monitor.bounds.action_intervals(), ref_intervals)
                self.assertEqual(base_q[0], ref_leader)
                self.assertAlmostEqual(base_q[1], ref_gap, places=12)
        self.assertTrue(sessions[0].certified)

    def test_exact_regret_monitors_match_brute_force_and_dominate_marginal(self):
        cases = [
            overlap_dag(64, 0.0, 0.42, seed=601001, noisy=True),
            overlap_dag(64, 0.50, 0.42, seed=601002, noisy=True),
            overlap_dag(64, 0.75, 0.42, seed=601003, noisy=False),
            coded(8, seed=601004),
            contiguous_window_dag(64, 8, seed=601005, noisy=True),
            samegame_standard_endgame(1, depth=3, eps=0.05),
        ]
        exact_methods = ("dual-covers", "dual-covers-id", "factorized-regret", "direct-graph-regret")
        for problem, eps in cases:
            sessions = [
                CertifiedSearchSession(problem, 7001, "uct", m, eps, delta=0.05, c_explore=3.0, q_cert=1)
                for m in (*exact_methods, "quotient-protected")
            ]
            # Step all exact-regret sessions in lockstep
            exact_sess = sessions[:4]
            for t in range(1, 800):
                if exact_sess[0].certified:
                    break
                steps = [s.step() for s in exact_sess]
                self.assertTrue(all(st == steps[0] for st in steps))
                base_q = exact_sess[0].query
                for s in exact_sess[1:]:
                    self.assertEqual(s.query[0], base_q[0])
                    self.assertAlmostEqual(s.query[1], base_q[1], places=12)
                    self.assertEqual(s.certified, exact_sess[0].certified)
                if t <= 24 or (t & (t - 1)) == 0 or t % 64 == 0 or exact_sess[0].certified:
                    ev = exact_sess[0].monitor.evidence
                    ref_best, ref_reg, ref_all = brute_force_exact_regret(problem.graph, ev.lower, ev.upper)
                    _, marg_gap, _ = brute_force_marginal(problem.graph, ev.lower, ev.upper)
                    self.assertLessEqual(ref_reg, marg_gap + 1e-12)
                    self.assertEqual(base_q[0], ref_best)
                    self.assertAlmostEqual(base_q[1], ref_reg, places=12)
                    for a, want in enumerate(ref_all):
                        self.assertAlmostEqual(exact_sess[0].monitor.action_regrets()[a], want, places=12)
                        self.assertAlmostEqual(exact_sess[2].monitor.action_regrets()[a], want, places=12)

        # Verify identical-support immediate certification (rho = 1.0 -> tau_exact == 0)
        ident_prob, ident_eps = overlap_dag(64, 1.0, 0.42, seed=601099, noisy=True)
        ident_exact = CertifiedSearchSession(ident_prob, 1, "uct", "dual-covers", ident_eps)
        ident_marg = CertifiedSearchSession(ident_prob, 1, "uct", "quotient-protected", ident_eps)
        self.assertTrue(ident_exact.certified)
        self.assertEqual(ident_exact.calls, 0)
        self.assertFalse(ident_marg.certified)

    def test_root_puct_deterministic_work_separation(self):
        # Validate Theorem 4.1 / Corollary E.6 on m = 16 vs m = 256
        ratios = []
        for m in (16, 256):
            prob, eps = puct_root_funnel(m, seed=0, alpha=0.25)
            eager = CertifiedSearchSession(
                prob, 1, "root_puct", "graph-eager", eps,
                delta=0.05, c_explore=3.0, prior_mode="unit_lambda",
                schedule="box", downstream="fixed_first", effective_m=3,
            )
            dec = CertifiedSearchSession(
                prob, 1, "root_puct", "decision-selective", eps,
                delta=0.05, c_explore=3.0, prior_mode="unit_lambda",
                schedule="box", downstream="fixed_first", effective_m=3,
            )
            while not eager.certified:
                p1 = eager.step()
                p2 = dec.step()
                self.assertEqual(p1, p2)
                self.assertEqual(eager.certified, dec.certified)
            self.assertEqual(eager.action, dec.action)
            self.assertEqual(dec.monitor.bounds.retired_root_actions, 1)
            ratios.append(eager.work / dec.work)
        self.assertGreater(ratios[1], ratios[0])
        self.assertGreater(ratios[1], 2.0)

    def test_recursive_puct_coupling_and_priors(self):
        prob, eps = puct_noisy_funnel(32, seed=808, gap=0.14, noisy=True)
        for prior in ("uniform", "informative", "misleading"):
            s_eag = CertifiedSearchSession(
                prob, 99, "recursive_puct", "graph-eager", eps,
                delta=0.05, c_explore=2.0, prior_mode=prior, schedule="noisy_puct",
            )
            s_prot = CertifiedSearchSession(
                prob, 99, "recursive_puct", "protected-selective", eps,
                delta=0.05, c_explore=2.0, prior_mode=prior, schedule="noisy_puct",
            )
            s_dec = CertifiedSearchSession(
                prob, 99, "recursive_puct", "decision-selective", eps,
                delta=0.05, c_explore=2.0, prior_mode=prior, schedule="noisy_puct",
            )
            for _ in range(800):
                if s_eag.certified:
                    break
                r1 = s_eag.step()
                r2 = s_prot.step()
                r3 = s_dec.step()
                self.assertEqual(r1, r2)
                self.assertEqual(r1, r3)
                self.assertEqual(s_eag.certified, s_prot.certified)
                self.assertEqual(s_eag.certified, s_dec.certified)

    def test_factorized_vs_dual_covers_incidence_separation_on_parity_grid(self):
        prob, _ = coded(16, seed=42)
        dual = ChargedDualCovers(prob.graph, delta=0.05, layout="best")
        fact = FactorizedRegretMonitor(prob.graph, delta=0.05, mode="protected")
        # On 16x16 parity grid, FactorizedRegretMonitor uses dramatically fewer incidences/compile work!
        self.assertLess(fact.info["neg_incidences"], dual.info["neg_blocks"] // 4)
        self.assertLess(fact.compile_work, dual.compile_work)

    def test_samegame_depth3_diagnostics(self):
        game, _ = samegame_depth_case(6, 3, seed=510001)
        diag = structural_diagnostics(game.graph)
        self.assertGreater(diag["leaf_transposition_rate"], 0.20)
        self.assertGreater(diag["mean_membership"], 1.20)


if __name__ == "__main__":
    unittest.main()
