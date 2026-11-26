"""Unit tests for v3 strengthening modules: Empirical Bernstein, Active DAG-LUCB, and C++17 kernels."""
from __future__ import annotations

import random
import unittest

from joint_root_cert._core.certified_uct import UCTWork
from joint_root_cert import DAG
from joint_root_cert import CertifiedSearchSession
from joint_root_cert.benchmarks import (
    contiguous_window_dag,
    overlap_dag,
    puct_root_funnel,
    samegame_standard_endgame,
)
from joint_root_cert import NestedIntervals
from joint_root_cert._core.v3_extensions import (
    ActiveDAGLUCBSession,
    CppKernelRunner,
    SplitMixProblem,
)
from experiment.simulated.passive_uct.uct_frontier_families import coded


class V3StrengtheningTests(unittest.TestCase):
    def test_empirical_bernstein_nesting_fast_rate_and_coverage(self):
        g = DAG(((1, 2), (), ()))
        ev_box = NestedIntervals(g, UCTWork(), delta=0.05, schedule="box")
        ev_eb = NestedIntervals(g, UCTWork(), delta=0.05, schedule="emp_bernstein")

        # 1. Zero-variance / low-variance stream: EB shrinks much faster than Hoeffding!
        rng = random.Random(101)
        prev_l, prev_u = 0.0, 1.0
        for _ in range(80):
            r = 0.22 + 0.01 * (2.0 * rng.random() - 1.0)
            ev_box.observe(1, r)
            ev_eb.observe(1, r)
            self.assertFalse(ev_eb.conflict)
            self.assertGreaterEqual(ev_eb.lower[1], prev_l)
            self.assertLessEqual(ev_eb.upper[1], prev_u)
            prev_l, prev_u = ev_eb.lower[1], ev_eb.upper[1]

        width_box = ev_box.upper[1] - ev_box.lower[1]
        width_eb = ev_eb.upper[1] - ev_eb.lower[1]
        self.assertLess(width_eb, 0.45 * width_box)

        # 2. Simultaneous coverage sanity check over 120 independent Bernoulli trials (delta = 0.05)
        violations = 0
        means = {1: 0.30, 2: 0.75}
        for trial in range(120):
            trng = random.Random(9000 + trial)
            ev = NestedIntervals(g, UCTWork(), delta=0.05, schedule="emp_bernstein")
            bad = False
            for _ in range(100):
                leaf = 1 if trng.random() < 0.5 else 2
                r = 1.0 if trng.random() < means[leaf] else 0.0
                ev.observe(leaf, r)
                if ev.conflict or not (ev.lower[leaf] <= means[leaf] <= ev.upper[leaf]):
                    bad = True
                    break
            if bad:
                violations += 1
        self.assertLessEqual(violations, 8)

    def test_adaptive_dag_lucb_transcript_coupling_and_overlap_gain(self):
        cases = [
            overlap_dag(64, 0.50, 0.42, seed=710001, noisy=True),
            overlap_dag(64, 0.75, 0.42, seed=710002, noisy=False),
            coded(8, seed=710003),
            contiguous_window_dag(64, 8, seed=710004, noisy=True),
            samegame_standard_endgame(5, depth=3, eps=0.08),
        ]
        exact_methods = ("dual-covers", "direct-graph-regret", "factorized-regret")
        for prob, eps in cases:
            for sched in ("box", "emp_bernstein"):
                sessions = [
                    ActiveDAGLUCBSession(prob, 8801, m, eps, delta=0.05, schedule=sched)
                    for m in exact_methods
                ]
                while not sessions[0].certified and sessions[0].calls < 2000:
                    outs = [s.step() for s in sessions]
                    # Theorem 2.4: identical adaptive paths, rewards, witness queries, and stopping!
                    self.assertTrue(all(o == outs[0] for o in outs))
                    q0 = sessions[0].query
                    for s in sessions[1:]:
                        self.assertEqual(s.query[0], q0[0])
                        self.assertAlmostEqual(s.query[1], q0[1], places=12)
                        self.assertEqual(s.query[2], q0[2])
                        self.assertEqual(s.query[3], q0[3])
                        self.assertEqual(s.certified, sessions[0].certified)

        # Verify Exact-Regret-DAG-LUCB strictly beats Marginal-DAG-LUCB on overlapping supports!
        prob_ov, eps_ov = overlap_dag(64, 0.75, 0.42, seed=710099, noisy=True)
        ex_lucb = ActiveDAGLUCBSession(prob_ov, 42, "dual-covers", eps_ov, delta=0.05, schedule="box")
        mg_lucb = ActiveDAGLUCBSession(prob_ov, 42, "marginal-graph", eps_ov, delta=0.05, schedule="box")
        while not ex_lucb.certified and ex_lucb.calls < 10000:
            ex_lucb.step()
        while not mg_lucb.certified and mg_lucb.calls < 10000:
            mg_lucb.step()
        self.assertTrue(ex_lucb.certified)
        self.assertLess(ex_lucb.calls, mg_lucb.calls // 3)

    def test_cpp_kernels_exact_replay_parity_with_python(self):
        # 1. TA-UCT parity on overlap_dag (noisy Bernoulli via SplitMixProblem)
        base_prob, eps = overlap_dag(64, 0.50, 0.42, seed=720001, noisy=True)
        sm_prob = SplitMixProblem("sm_overlap", base_prob.graph, base_prob.means, reward_kind=1)
        for meth in ("graph-eager", "protected-selective", "decision-selective", "dual-covers", "direct-graph-regret"):
            # Note: Python TranspositionUCT(lazy=False) matches C++ exact UCB scan bit-for-bit
            py_sess = CertifiedSearchSession(
                sm_prob, 12345, "uct", meth, eps,
                delta=0.05, c_explore=3.0, q_cert=4, schedule="box",
            )
            py_sess.policy.lazy = False
            py_sess.policy.lazy_nodes = [False] * len(sm_prob.graph)
            while not py_sess.certified and py_sess.calls < 20000:
                py_sess.step()
            cpp_res = CppKernelRunner.run(
                sm_prob, 12345, "uct", meth, eps,
                delta=0.05, c_explore=3.0, q_cert=4, schedule="box", cap=20000,
            )
            self.assertEqual(cpp_res["certified"], py_sess.certified)
            self.assertEqual(cpp_res["steps"], py_sess.calls)
            self.assertEqual(cpp_res["action"], py_sess.action)
            self.assertEqual(cpp_res["strict_changes"], py_sess.monitor.evidence.strict_changes)
            if meth in ("graph-eager", "protected-selective", "decision-selective"):
                self.assertEqual(cpp_res["messages"], py_sess.monitor.bounds.messages)
                self.assertEqual(cpp_res["retired"], py_sess.monitor.bounds.retired)

        # 2. Root-PUCT parity on deterministic funnel (m = 64)
        p_prob, p_eps = puct_root_funnel(64, seed=720002, alpha=0.25)
        sm_puct = SplitMixProblem("sm_puct", p_prob.graph, p_prob.means, reward_kind=0)
        for meth in ("graph-eager", "protected-selective", "decision-selective", "dual-covers"):
            py_s = CertifiedSearchSession(
                sm_puct, 99, "root_puct", meth, p_eps,
                delta=0.05, c_explore=3.0, prior_mode="unit_lambda",
                q_cert=1, schedule="box", downstream="fixed_first", effective_m=3,
            )
            while not py_s.certified and py_s.calls < 30000:
                py_s.step()
            cpp_r = CppKernelRunner.run(
                sm_puct, 99, "root_puct", meth, p_eps,
                delta=0.05, c_explore=3.0, q_cert=1, schedule="box",
                effective_m=3, cap=30000,
            )
            self.assertEqual(cpp_r["steps"], py_s.calls)
            self.assertEqual(cpp_r["action"], py_s.action)
            self.assertEqual(cpp_r["certified"], py_s.certified)


if __name__ == "__main__":
    unittest.main()
