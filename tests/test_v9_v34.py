"""Unit tests verifying V22/V23/V32/V33/V34 certified oracles and adaptive tracker."""
from __future__ import annotations

import math
import unittest

import numpy as np

from joint_root_cert._core.v9_v34_tracker import (
    ComponentPolyhedron,
    HeteroscedasticDAGProblem,
    IntrinsicGaussianTape,
    batch_schedule_sizes,
    compute_exact_nuisance_kl_rate,
    eval_profiled_loss,
    is_four_power_refresh,
    is_square_refresh,
    largest_remainder_counts,
    make_behrens_fisher_null_dag,
    make_general_d_dag,
    make_heteroscedastic_proxy_dag,
    make_rank2_multi_action_dag,
    make_switching_multi_answer_dag,
    run_indep_heteroscedastic_os,
    run_known_sigma_info_tracker,
    run_v34_tracker,
    solve_action_design_certified,
    solve_cubic_exact_2d,
    solve_profiled_loss_certified,
    solve_uncertified_local_null,
)


class TestV9V34Tracker(unittest.TestCase):
    def test_behrens_fisher_bimodal_exact_vs_local_trap(self) -> None:
        """CE V23.1: Both exact cubic & B&B find global min log(16); single-start local traps at log(25)."""
        # H = [[1, 1], [1, -1]], y = [2, 2], c = [2, 2], k = [1, 1], q = [1, 1], P = {u1 <= 0}
        # Along boundary u1 = 0: L(u2) = log(1 + (u2 - 2)^2) + log(1 + (u2 + 2)^2)
        # Global min at u2 = +-sqrt(3): L = log(16) = 2.772588722239781; saddle at u2 = 0: log(25) = 3.21887582
        prob = make_behrens_fisher_null_dag()
        comp = prob.components[0][0]  # {u : -u1 >= 0} = {u1 <= 0}
        H = prob.H
        y = np.array([2.0, 2.0])
        c = np.array([2.0, 2.0])
        k = np.array([1.0, 1.0])
        q = np.array([1.0, 1.0])

        exact_min = math.log(16.0)
        res_cubic = solve_cubic_exact_2d(comp, H, y, c, k, q, tol=1e-9)
        self.assertLessEqual(res_cubic.lower, exact_min + 1e-9)
        self.assertGreaterEqual(res_cubic.upper, exact_min - 1e-9)
        self.assertAlmostEqual(res_cubic.upper, exact_min, places=7)
        self.assertAlmostEqual(abs(float(res_cubic.u_opt[1])), math.sqrt(3.0), places=5)

        # Force general-d B&B by passing a copy without 2D boundary
        comp_no2d = ComponentPolyhedron(
            action=comp.action, terminal=comp.terminal, A=comp.A, b=comp.b,
            feasible_point=np.array([0.0, 0.0]),
        )
        res_bnb = solve_profiled_loss_certified(comp_no2d, H, y, c, k, q, tol=1e-3, max_nodes=300)
        self.assertLessEqual(res_bnb.lower, exact_min + 1e-8)
        self.assertGreaterEqual(res_bnb.upper, exact_min - 1e-8)
        self.assertLessEqual(res_bnb.upper - res_bnb.lower, 1e-3 + 1e-9)
        self.assertAlmostEqual(res_bnb.upper, exact_min, places=3)

        # Single-start local optimizer from symmetric saddle (0, 0) fails (traps at log(25)!)
        res_loc = solve_uncertified_local_null(comp_no2d, H, y, c, k, q, init_u=np.array([0.0, 0.0]))
        self.assertGreater(res_loc.lower, exact_min + 0.40)

    def test_cubic_and_bnb_agree_on_random_2d_wedges(self) -> None:
        """Exact cubic solver and general-d B&B agree across random 2D wedges & multi-facet cones."""
        prob = make_rank2_multi_action_dag(K=8, multi_answer=True, seed=7)
        y = prob.true_query_means
        c = np.array([12.0, 27.0])
        k = np.array([12.0, 27.0])
        q = np.array([4.5, 42.0])
        for comp in prob.components[0][:4]:
            r_c = solve_cubic_exact_2d(comp, prob.H, y, c, k, q, tol=1e-8)
            comp_g = ComponentPolyhedron(
                action=comp.action, terminal=comp.terminal, A=comp.A, b=comp.b,
                feasible_point=comp.feasible_point,
            )
            r_b = solve_profiled_loss_certified(comp_g, prob.H, y, c, k, q, tol=1e-3, max_nodes=400)
            self.assertLessEqual(r_b.lower, r_c.upper + 1e-7)
            self.assertLessEqual(r_c.lower, r_b.upper + 1e-7)
            self.assertLessEqual(r_b.upper - r_b.lower, 1e-3 + 1e-8)

    def test_outer_design_certification_and_warm_cut_reuse(self) -> None:
        """Thm. V23.3 / Prop. V22.3: Certified outer design brackets true grid max & warm reuse preserves validity."""
        prob = make_rank2_multi_action_dag(K=4, multi_answer=False, seed=11)
        sig2 = prob.sigma ** 2
        res = solve_action_design_certified(prob, 0, prob.theta_star, sig2, tol=1e-4, floor_alpha=1e-4)
        # Dense grid reference on w1 in [1e-4, 1 - 1e-4]
        grid_best = 0.0
        for w1 in np.linspace(1e-4, 1.0 - 1e-4, 201):
            w = np.array([w1, 1.0 - w1])
            vals = [
                solve_cubic_exact_2d(comp, prob.H, prob.true_query_means, w, np.ones(2), sig2).upper
                for comp in prob.components[0]
            ]
            grid_best = max(grid_best, min(vals))
        self.assertLessEqual(res.lower, grid_best + 1e-4)
        self.assertGreaterEqual(res.upper, grid_best - 1e-4)
        self.assertLessEqual(res.upper - res.lower, 1e-4 + 1e-8)

        # Warm reuse on slightly perturbed model uses <= cold iters and preserves bracket
        th_p = prob.theta_star + np.array([0.02, -0.01])
        r_cold = solve_action_design_certified(prob, 0, th_p, sig2, tol=1e-3)
        r_warm = solve_action_design_certified(prob, 0, th_p, sig2, tol=1e-3, cached_cuts=res.active_cuts)
        self.assertLessEqual(r_warm.lower, r_cold.upper + 1e-6)
        self.assertLessEqual(r_cold.lower, r_warm.upper + 1e-6)
        self.assertLessEqual(r_warm.outer_iters, r_cold.outer_iters + 1)

    def test_lem_v33_count_domination_and_v34_pathwise_call_bounds(self) -> None:
        """Lem. V33.1 count domination & Prop. V34.1 pathwise solver-call bounds on full multi-action run."""
        # Count domination check
        rng = np.random.default_rng(42)
        for j in (1, 2, 4, 9, 16, 64, 100):
            for m in (2, 4, 8):
                M_j, b_j, R_j = batch_schedule_sizes(j, m)
                w = rng.dirichlet(np.ones(m))
                c = largest_remainder_counts(M_j, w)
                self.assertEqual(int(np.sum(c)), M_j)
                r = b_j + c
                self.assertTrue(np.all(r >= M_j * w - 1e-12))
                self.assertEqual(int(np.sum(r)), R_j)

        # Full V34 vs V33 comparison on paired intrinsic tapes (K=8)
        prob = make_rank2_multi_action_dag(K=8, multi_answer=True, seed=19)
        tape_33 = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=1001)
        tape_34 = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=1001)

        r33 = run_v34_tracker(prob, tape_33, delta=0.05, method_name="v33", refresh_schedule="square", action_local=False)
        r34 = run_v34_tracker(prob, tape_34, delta=0.05, method_name="v34", refresh_schedule="four_power", action_local=True)

        self.assertTrue(r33.certified and r33.is_correct)
        self.assertTrue(r34.certified and r34.is_correct)
        # Prop. V34.1 pathwise bounds!
        self.assertLessEqual(r34.design_calls, prob.K * (1 + int(math.floor(math.log(max(1, r34.batches), 4)))))
        self.assertLessEqual(r34.null_calls, prob.j_max * r34.batches)
        # V34 dramatically reduces null calls vs V33 on K=8!
        self.assertLess(r34.null_calls, r33.null_calls / 3.0)

    def test_general_d_v34_and_baselines_certify_soundly(self) -> None:
        """General d=3 proxy & d=4 overlapping DAG certify cleanly across V34, Student hedge, & baselines."""
        prob = make_heteroscedastic_proxy_dag([2.0, 2.0, 2.0, 0.35], eps=0.0)
        C_star, V_a, _ = compute_exact_nuisance_kl_rate(prob, tol=1e-4)
        self.assertGreater(C_star, 0.01)
        self.assertEqual(int(np.argmax(V_a)), 0)

        t1 = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=55)
        t2 = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=55)
        t3 = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=55)
        t4 = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=55)

        r_v34 = run_v34_tracker(prob, t1, delta=0.05, method_name="v34", null_log_tol=0.5, fast_qp_screen=True, predictable_gate=True)
        r_hedge = run_v34_tracker(prob, t2, delta=0.05, method_name="v34_hedge", null_log_tol=0.5, student_hedge_pi=0.5, fast_qp_screen=True, predictable_gate=True)
        r_known = run_known_sigma_info_tracker(prob, t3, delta=0.05)
        r_os = run_indep_heteroscedastic_os(prob, t4, delta=0.05)

        for r in (r_v34, r_hedge, r_known, r_os):
            self.assertTrue(r.certified, f"{r.method} failed to certify")
            self.assertTrue(r.is_correct, f"{r.method} returned wrong action")


if __name__ == "__main__":
    unittest.main()
