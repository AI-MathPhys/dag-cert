"""Unit tests for v4 external BAI baselines, C++17 SameGame playouts, and inside-witness rules."""
from __future__ import annotations

import ctypes
import unittest

from joint_root_cert import DAG, Problem
from joint_root_cert.benchmarks import (
    overlap_dag,
    samegame_standard_endgame,
)
from joint_root_cert import ActiveDAGLUCBSession
from joint_root_cert._core.v4_baselines import (
    CppSameGameRunner,
    InsideWitnessDAGLUCBSession,
    LUCBMicroSession,
    UGapEMCTSSession,
    VarDEDAGSession,
    samegame_midgame_case,
)


class V4BaselinesTests(unittest.TestCase):
    def test_cpp_samegame_means_match_exact_python_dp_and_zero_containment(self):
        # 1. Verify C++17 playout distribution matches exact Python uniform-playout DP
        game, _ = samegame_standard_endgame(1, depth=3, eps=0.08)
        lib = CppSameGameRunner.ensure_loaded()
        leaves = game.graph.leaves
        m = len(leaves)

        cell_offsets = [0]
        flat_cells: list[int] = []
        col_offsets = [0]
        col_lens: list[int] = []
        ncols_list: list[int] = []
        points_list: list[int] = []
        for leaf in leaves:
            board, pts, _ = game.states[leaf]
            ncols_list.append(len(board))
            points_list.append(int(pts))
            for col in board:
                col_lens.append(len(col))
                flat_cells.extend(col)
            cell_offsets.append(len(flat_cells))
            col_offsets.append(len(col_lens))

        out_means = (ctypes.c_double * m)()
        lib.cpp_samegame_batch_means(
            m,
            (ctypes.c_int * len(cell_offsets))(*cell_offsets),
            (ctypes.c_uint8 * max(1, len(flat_cells)))(*(flat_cells if flat_cells else [0])),
            (ctypes.c_int * len(col_offsets))(*col_offsets),
            (ctypes.c_uint8 * max(1, len(col_lens)))(*(col_lens if col_lens else [0])),
            (ctypes.c_int * m)(*ncols_list),
            (ctypes.c_int * m)(*points_list),
            int(game.B),
            1.0 / float(game.scale),
            16384,
            ctypes.c_uint64(123456789),
            out_means,
        )
        for idx, leaf in enumerate(leaves):
            self.assertAlmostEqual(float(out_means[idx]), game.means[leaf], delta=0.004)

        # 2. Verify mid-game 15x15 case has large DAG and strictly zero support containment
        prob_mid, eps_mid, diag = samegame_midgame_case(2, depth=4, tile_cap=70, eps=0.04, ref_samples=512)
        self.assertGreater(len(prob_mid.graph), 500)
        self.assertEqual(diag["containment_pairs"], 0)
        self.assertEqual(eps_mid, 0.04)

    def test_external_structured_bai_baselines_soundness_and_2x2_separation(self):
        prob, eps = overlap_dag(64, 0.75, 0.42, seed=740001, noisy=True)
        values = prob.graph.optimal_values(prob.means)
        opt = values[prob.graph.root]
        regrets = [max(0.0, opt - values[c]) for c in prob.graph.children[prob.graph.root]]

        s_lm_marg = LUCBMicroSession(prob, 42, eps, delta=0.05, schedule="box", stop_rule="marginal")
        s_lm_ex = LUCBMicroSession(prob, 42, eps, delta=0.05, schedule="box", stop_rule="exact")
        s_ug_marg = UGapEMCTSSession(prob, 42, eps, delta=0.05, schedule="box", mode="dag", stop_rule="marginal")
        s_ug_ex = UGapEMCTSSession(prob, 42, eps, delta=0.05, schedule="box", mode="dag", stop_rule="exact")
        s_ug_tree = UGapEMCTSSession(prob, 42, eps, delta=0.05, schedule="box", mode="tree", stop_rule="marginal")
        s_vd_marg = VarDEDAGSession(prob, 42, eps, delta=0.05, schedule="emp_bernstein", witness_mode="marginal")
        s_vd_ex = VarDEDAGSession(prob, 42, eps, delta=0.05, schedule="emp_bernstein", witness_mode="exact")
        s_ours = ActiveDAGLUCBSession(prob, 42, "dual-covers", eps, delta=0.05, schedule="box")

        for sess in (s_lm_marg, s_lm_ex, s_ug_marg, s_ug_ex, s_ug_tree, s_vd_marg, s_vd_ex, s_ours):
            while not sess.certified and sess.calls < 15000:
                sess.step()
            if sess.certified:
                self.assertLessEqual(regrets[sess.action], eps + 1e-12)

        # Verify 2-stage sample reduction:
        # (LUCB-micro + Marginal) > (LUCB-micro + Exact Stop) > (Exact-Regret-DAG-LUCB)
        self.assertTrue(s_ours.certified)
        self.assertTrue(s_lm_ex.certified)
        self.assertLess(s_lm_ex.calls, s_lm_marg.calls)
        self.assertLess(s_ours.calls, s_lm_ex.calls)
        self.assertLess(s_ug_marg.calls, s_ug_tree.calls)

    def test_inside_witness_lcb_stall_vs_ucb_certification(self):
        # Root has two actions:
        # Action 0 -> leaves (3, 4) with means 0.75 (tried first by lower ID!) and 0.95 (true winner)
        # Action 1 -> leaf (5,) with mean 0.75
        # At eps = 0.02, R_t(0) = 2*beta(n) < 0.25 + beta(n) = R_t(1) once n >= 35,
        # so LCB-inside stays locked on leaf 3 (0.75 == 0.75) and fails to certify within 5000 steps,
        # whereas UCB-inside explores leaf 4 (0.95) and certifies in ~900 steps!
        g = DAG(((1, 2), (3, 4), (5,), (), (), ()))
        prob = Problem("inside_witness_test", g, {3: 0.75, 4: 0.95, 5: 0.75}, g.leaves)
        eps = 0.02

        s_ucb = InsideWitnessDAGLUCBSession(prob, 7, eps, inside_mode="ucb", delta=0.05, schedule="box")
        s_lcb = InsideWitnessDAGLUCBSession(prob, 7, eps, inside_mode="lcb", delta=0.05, schedule="box")
        s_mean = InsideWitnessDAGLUCBSession(prob, 7, eps, inside_mode="mean", delta=0.05, schedule="box")

        while not s_ucb.certified and s_ucb.calls < 5000:
            s_ucb.step()
        while not s_lcb.certified and s_lcb.calls < 5000:
            s_lcb.step()
        while not s_mean.certified and s_mean.calls < 5000:
            s_mean.step()

        # UCB-inside certifies optimal action 0 cleanly, whereas LCB-inside gets stuck!
        self.assertTrue(s_ucb.certified)
        self.assertEqual(s_ucb.action, 0)
        self.assertLess(s_ucb.calls, 2500)
        self.assertFalse(s_lcb.certified)
        self.assertEqual(s_lcb.calls, 5000)


if __name__ == "__main__":
    unittest.main()
