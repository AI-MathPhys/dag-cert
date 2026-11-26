"""Unit tests for v10 Strengthening: Native C++17 V34 B&B Parity/Soundness & Real Heteroscedastic Bridge."""
from __future__ import annotations

import math
import unittest

import numpy as np

from joint_root_cert._core.v9_v34_tracker import (
    CppV34BnBRunner,
    IntrinsicGaussianTape,
    eval_profiled_loss,
    make_behrens_fisher_null_dag,
    make_general_d_dag,
    run_v34_tracker,
    solve_cubic_exact_2d,
    solve_profiled_loss_certified,
)


class TestV10Strengthening(unittest.TestCase):
    def test_cpp_bnb_behrens_fisher_bimodal_soundness(self) -> None:
        """Native C++17 B&B must bracket exact global minimum on Behrens-Fisher bimodal nulls with 0 violation."""
        p_bf = make_behrens_fisher_null_dag()
        poly = p_bf.components[0][0]
        H3 = np.vstack([p_bf.H, np.array([[1.0, 1.0]])])
        rng = np.random.default_rng(1001)
        for _ in range(25):
            y2 = rng.normal(0.0, 3.0, size=2)
            c2 = rng.uniform(5.0, 40.0, size=2)
            q2 = rng.uniform(0.5, 10.0, size=2)
            k2 = c2.copy()
            r_cub = solve_cubic_exact_2d(poly, p_bf.H, y2, c2, k2, q2, tol=1e-9)
            r_cpp = solve_profiled_loss_certified(
                poly,
                H3,
                np.array([y2[0], y2[1], 0.0]),
                np.array([c2[0], c2[1], 0.0]),
                np.array([k2[0], k2[1], 1.0]),
                np.array([q2[0], q2[1], 1.0]),
                tol=1e-4,
                basis_idx=(0, 1),
                use_cpp_bnb=True,
                max_nodes=2000,
            )
            # Outward soundness: cpp.lower <= exact_min <= cpp.upper
            self.assertLessEqual(r_cpp.lower, r_cub.upper + 1e-7)
            self.assertGreaterEqual(r_cpp.upper, r_cub.lower - 1e-7)
            # Witness feasibility
            self.assertGreaterEqual(float(np.min(poly.A @ r_cpp.u_opt - poly.b)), -1e-7)

    def test_cpp_vs_python_bnb_general_d_parity(self) -> None:
        """Native C++17 B&B matches pure-Python certified B&B brackets across d=4 and d=6 polyhedra."""
        for d in (4, 6):
            prob = make_general_d_dag(d=d, m=d, K=4, eps=0.03, seed=10000 + d)
            poly = prob.components[0][0]
            rng = np.random.default_rng(2000 + d)
            for _ in range(5):
                y = prob.true_query_means + rng.normal(0.0, 0.5, size=d)
                c = rng.uniform(8.0, 25.0, size=d)
                k = c.copy()
                q = rng.uniform(2.0, 15.0, size=d)
                r_py = solve_profiled_loss_certified(
                    poly, prob.H, y, c, k, q, tol=0.05, basis_idx=prob.basis_idx, use_cpp_bnb=False
                )
                r_cpp = solve_profiled_loss_certified(
                    poly, prob.H, y, c, k, q, tol=0.05, basis_idx=prob.basis_idx, use_cpp_bnb=True
                )
                # Mutually consistent brackets: cpp.lower <= py.upper and py.lower <= cpp.upper
                self.assertLessEqual(r_cpp.lower, r_py.upper + 1e-6)
                self.assertLessEqual(r_py.lower, r_cpp.upper + 1e-6)
                # Exact loss at reported witness matches upper
                v_w = eval_profiled_loss(r_cpp.u_opt, prob.H, y, c, k, q)
                self.assertAlmostEqual(v_w, r_cpp.upper, places=6)

    def test_cpp_v34_tracker_certifies_d4_d6_d8(self) -> None:
        """End-to-end V34 tracker with C++17 B&B certifies cleanly and accurately on d=4, 6, 8."""
        for d, K in [(4, 4), (6, 4), (8, 4)]:
            prob = make_general_d_dag(d=d, m=d, K=K, eps=0.03, seed=94000 + 10 * d + K)
            tape = IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=77 + d)
            res = run_v34_tracker(
                prob,
                tape,
                delta=0.05,
                method_name=f"cpp_v34_d{d}",
                refresh_schedule="four_power",
                action_local=True,
                design_tol_scale=0.015,
                null_log_tol=0.1,
                warm_start_cuts=True,
                fast_qp_screen=True,
                predictable_gate=True,
                use_cpp_bnb=True,
                max_samples=100_000,
            )
            self.assertTrue(res.certified)
            self.assertTrue(res.is_correct)
            self.assertGreater(res.total_samples, 0)
            self.assertLess(res.total_wall_s, 15.0)


if __name__ == "__main__":
    unittest.main()
