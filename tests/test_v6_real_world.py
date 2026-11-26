"""Unit tests for v6 real-world benchmarks (`GB1`, `TrpB`, `WorFBench`) and `FlatLUCBSession`."""
from __future__ import annotations

import statistics
import unittest

from joint_root_cert.tracking import LUCBMicroSession
from joint_root_cert._core.v5_hybrid_and_os import HybridWitnessDAGLUCBSession, noncontainment_star_dag
from joint_root_cert._core.v6_bayesian_opt import (
    CorrelatedSupportDAGProblem,
    DiscreteGPSurrogate,
    GPBoxCertSession,
    GPEllipsoidCertSession,
    GPGuidedRootCertSession,
    alt_protein_sequence_kernel,
    protein_sequence_kernel,
    solve_ellipsoid_challenger,
)
from joint_root_cert._core.v6_real_world import (
    FlatLUCBSession,
    GB1MutationCampaignProblem,
    TRPB_NPZ_PATH,
    TrpBMutationCampaignProblem,
    WORFBENCH_NPZ_PATH,
    WorFBenchWorkflowProblem,
    gb1_mean_to_raw_fitness,
    real_world_problem_diagnostics,
)


class TestV6RealWorld(unittest.TestCase):
    def test_flat_lucb_soundness_and_star_separation(self):
        """Flat-LUCB (both terminal and root_exact stop) stalls when top-2 leaves tie inside S(A)."""
        prob, _ = noncontainment_star_dag(n_rivals=6, gap=0.25, eps=0.05)

        opt_sess = HybridWitnessDAGLUCBSession(prob, 901, 0.02, mode="opt_sep", schedule="box")
        while not opt_sess.certified and opt_sess.calls < 4000:
            opt_sess.step()
        self.assertTrue(opt_sess.certified)

        for stop_rule in ("terminal", "root_exact"):
            flat_sess = FlatLUCBSession(prob, 901, 0.08, schedule="box", stop_rule=stop_rule)
            while not flat_sess.certified and flat_sess.calls < 8000:
                flat_sess.step()
            if flat_sess.certified:
                vals = prob.graph.optimal_values(prob.means)
                v_star = vals[prob.graph.root]
                v_rec = vals[prob.graph.children[prob.graph.root][flat_sess.action]]
                self.assertLessEqual(v_star - v_rec, 0.08 + 1e-12)
            self.assertLess(opt_sess.calls, flat_sess.calls)

    def test_gb1_zero_containment_and_unbiased_assay_oracles(self):
        """GB1 mutagenesis DAGs have zero support containments and unbiased replicates across all 3 noise models."""
        for start_seq in ("VDGV", "FDGV", "LDGV", "ADGV"):
            prob = GB1MutationCampaignProblem(start_seq=start_seq, max_edits=3, panel="panel4")
            diag = real_world_problem_diagnostics(prob)
            self.assertEqual(diag["containment_pairs"], 0, f"Containment found on {start_seq}")
            self.assertGreater(diag["leaves"], diag["root_actions"])
            self.assertGreater(diag["leaf_transposition_rate"], 0.40)

        for nm in ("calibrated", "bernoulli", "low_var_uniform"):
            prob = GB1MutationCampaignProblem(start_seq="FDGV", max_edits=3, panel="panel4", noise_model=nm)
            max_leaf = max(prob.graph.leaves, key=lambda z: prob.means[z])
            self.assertEqual(prob.variant_of_leaf[max_leaf], "FWAA")
            self.assertAlmostEqual(
                gb1_mean_to_raw_fitness(prob.means[max_leaf]),
                prob.raw_fitness[max_leaf],
                places=4,
            )
            oracle = prob.oracle(12345)
            stds = []
            for z in (prob.graph.leaves[0], max_leaf):
                draws = [oracle.sample(z) for _ in range(4000)]
                self.assertTrue(all(0.0 <= x <= 1.0 for x in draws))
                stds.append(statistics.pstdev(draws))
                self.assertGreater(stds[-1], 0.02)
                self.assertLess(abs(statistics.fmean(draws) - prob.means[z]), 0.02)
            if nm == "low_var_uniform":
                # Constant half-width 0.08 across interior variants -> identical theoretical std ~0.0462
                self.assertLess(abs(stds[0] - stds[1]), 0.004)

    def test_gb1_certification_beats_marginal_and_flat_root_on_ridge(self):
        """Exact-regret methods beat LUCB-micro on FDGV and both Flat-LUCB variants on ADGV ridge."""
        p_fdgv = GB1MutationCampaignProblem(start_seq="FDGV", max_edits=3, panel="panel4")
        s_hyb = HybridWitnessDAGLUCBSession(p_fdgv, 501, 0.015, mode="hybrid", schedule="emp_bernstein")
        s_mrg = LUCBMicroSession(p_fdgv, 501, 0.015, schedule="emp_bernstein", stop_rule="marginal")
        while not s_hyb.certified and s_hyb.calls < 12000:
            s_hyb.step()
        while not s_mrg.certified and s_mrg.calls < 20000:
            s_mrg.step()
        self.assertTrue(s_hyb.certified)
        self.assertLess(s_hyb.calls * 1.5, s_mrg.calls)

        p_adgv = GB1MutationCampaignProblem(start_seq="ADGV", max_edits=3, panel="panel5")
        s_opt = HybridWitnessDAGLUCBSession(p_adgv, 502, 0.010, mode="opt_sep", schedule="emp_bernstein")
        s_flt_term = FlatLUCBSession(p_adgv, 502, 0.010, schedule="emp_bernstein", stop_rule="terminal")
        s_flt_root = FlatLUCBSession(p_adgv, 502, 0.010, schedule="emp_bernstein", stop_rule="root_exact")
        for sess in (s_opt, s_flt_term, s_flt_root):
            while not sess.certified and sess.calls < 20000:
                sess.step()
        self.assertTrue(s_opt.certified)
        self.assertLess(s_opt.calls, s_flt_term.calls)
        self.assertLess(s_opt.calls, s_flt_root.calls)

    def test_trpb_measured_landscape_zero_containment(self):
        """Measured 4-site TmTrpB enzyme landscape produces zero-containment DAGs and unbiased assays."""
        self.assertTrue(TRPB_NPZ_PATH.is_file(), f"Missing {TRPB_NPZ_PATH}")
        for start_seq in ("VFVS", "VLVS", "VFVA", "IFVS"):
            prob = TrpBMutationCampaignProblem(
                start_seq=start_seq, max_edits=3, panel="panel5", noise_model="low_var_uniform"
            )
            diag = real_world_problem_diagnostics(prob)
            self.assertEqual(diag["containment_pairs"], 0, f"Containment found on TrpB {start_seq}")
            self.assertGreater(diag["leaves"], 300)
            self.assertGreater(diag["leaf_transposition_rate"], 0.40)

        prob = TrpBMutationCampaignProblem(start_seq="IFVS", max_edits=3, panel="panel5", noise_model="low_var_uniform")
        max_leaf = max(prob.graph.leaves, key=lambda z: prob.means[z])
        self.assertAlmostEqual(
            gb1_mean_to_raw_fitness(prob.means[max_leaf], prob.fitness_max),
            prob.raw_fitness[max_leaf],
            places=4,
        )
        oracle = prob.oracle(31415)
        draws = [oracle.sample(max_leaf) for _ in range(3000)]
        self.assertTrue(all(0.0 <= x <= 1.0 for x in draws))
        self.assertLess(abs(statistics.fmean(draws) - prob.means[max_leaf]), 0.01)

    def test_worfbench_zero_containment_and_upgrade_depth_sweep(self):
        """WorFBench workflow DAGs have zero containments across all domains and upgrade depths d=1..4."""
        self.assertTrue(WORFBENCH_NPZ_PATH.is_file(), f"Missing {WORFBENCH_NPZ_PATH}")
        for dom in ("all", "toolbench", "toolalpaca", "seal_tools", "webshop"):
            prob = WorFBenchWorkflowProblem(domain=dom, base_config=(0, 0, 0, 0), max_upgrades=3)
            diag = real_world_problem_diagnostics(prob)
            self.assertEqual(diag["containment_pairs"], 0)
            self.assertEqual(diag["root_actions"], 8)
            self.assertEqual(diag["leaves"], 64)
            self.assertGreater(diag["leaf_transposition_rate"], 0.50)

        expected_leaves = {1: 8, 2: 32, 3: 64, 4: 80}
        jaccards = []
        for d_up in (1, 2, 3, 4):
            prob = WorFBenchWorkflowProblem(domain="all", base_config=(0, 0, 0, 0), max_upgrades=d_up)
            diag = real_world_problem_diagnostics(prob)
            self.assertEqual(diag["containment_pairs"], 0)
            self.assertEqual(diag["leaves"], expected_leaves[d_up])
            jaccards.append(diag["mean_pairwise_jaccard"])
        self.assertEqual(jaccards[0], 0.0)
        self.assertTrue(jaccards[0] < jaccards[1] < jaccards[2] < jaccards[3])

        prob = WorFBenchWorkflowProblem(domain="all", base_config=(0, 0, 0, 0), max_upgrades=3)
        oracle = prob.oracle(777)
        z0 = max(prob.graph.leaves, key=lambda z: prob.means[z])
        draws = [oracle.sample(z0) for _ in range(5000)]
        self.assertTrue(all(0.0 <= x <= 1.0 for x in draws))
        self.assertLess(abs(statistics.fmean(draws) - prob.means[z0]), 0.015)

    def test_gp_surrogate_exactness_and_bo_root_certification(self):
        """Sherman-Morrison GP matches exact batch GP and GP-Root-Info beats standard GP-UCB on certification."""
        import numpy as np

        prob = GB1MutationCampaignProblem(start_seq="FDGV", max_edits=3, panel="panel4")
        leaves = list(prob.graph.leaves)
        seqs = [prob.variant_of_leaf[z] for z in leaves]
        k_mat = protein_sequence_kernel(seqs)
        gp = DiscreteGPSurrogate(k_mat)

        rng = np.random.default_rng(42)
        for _ in range(35):
            idx = int(rng.integers(0, len(leaves)))
            y = float(prob.means[leaves[idx]] + 0.05 * rng.standard_normal())
            gp.observe(idx, y)

        # Verify Sherman-Morrison posterior matches batch precision inversion to < 1e-11
        prec = gp.K_inv + np.diag(gp.counts / gp.obs_var)
        sigma_batch = np.linalg.inv(prec)
        mean_batch = gp.prior_mean + sigma_batch @ (gp.centered_sums / gp.obs_var)
        self.assertLess(float(np.max(np.abs(gp.Sigma - sigma_batch))), 1e-11)
        self.assertLess(float(np.max(np.abs(gp.mean - mean_batch))), 1e-11)

        # Verify Matheron Thompson sampling empirical mean & marginal std
        ts_draws = np.stack([gp.sample_thompson(rng) for _ in range(600)], axis=0)
        self.assertLess(float(np.max(np.abs(ts_draws.mean(axis=0) - gp.mean))), 0.03)

        # Verify GP-Root-Info certifies on FDGV while standard GP-UCB locks onto terminal exploitation
        s_ri = GPGuidedRootCertSession(prob, 601, 0.015, acquisition="gp_root_info", schedule="emp_bernstein")
        s_ucb = GPGuidedRootCertSession(prob, 601, 0.015, acquisition="gp_ucb", schedule="emp_bernstein")
        while not s_ri.certified and s_ri.calls < 12000:
            s_ri.step()
        while not s_ucb.certified and s_ucb.calls < 12000:
            s_ucb.step()
        self.assertTrue(s_ri.certified)
        self.assertLess(s_ri.calls, s_ucb.calls)

        vals = prob.graph.optimal_values(prob.means)
        v_star = vals[prob.graph.root]
        v_rec = vals[prob.graph.children[prob.graph.root][s_ri.action]]
        self.assertLessEqual(v_star - v_rec, 0.015 + 1e-12)

    def test_ellipsoid_regret_duality_and_correlated_dag_dominance(self):
        """Exact ellipsoid solver has zero duality gap and strictly dominates enclosing GP box."""
        import math
        import numpy as np
        from scipy.optimize import minimize

        sigma3 = np.array([
            [0.040, 0.028, 0.028],
            [0.028, 0.040, 0.004],
            [0.028, 0.004, 0.040],
        ], dtype=np.float64)
        m3 = np.array([0.52, 0.55, 0.55], dtype=np.float64)
        rad = 3.0
        ell_val, gap, p_opt = solve_ellipsoid_challenger(
            float(m3[0]), m3[1:], float(sigma3[0, 0]), sigma3[1:, 0], sigma3[1:, 1:], rad, tol=1e-9
        )
        slsqp = minimize(
            lambda p: float(m3[0] - p @ m3[1:])
            + rad * math.sqrt(float(sigma3[0, 0] - 2.0 * (p @ sigma3[1:, 0]) + p @ sigma3[1:, 1:] @ p)),
            x0=np.array([0.5, 0.5]),
            bounds=[(0.0, 1.0), (0.0, 1.0)],
            constraints={"type": "eq", "fun": lambda p: float(np.sum(p) - 1.0)},
            tol=1e-12,
        )
        pair_val = min(
            m3[0] - m3[1] + rad * math.sqrt(sigma3[0, 0] + sigma3[1, 1] - 2.0 * sigma3[0, 1]),
            m3[0] - m3[2] + rad * math.sqrt(sigma3[0, 0] + sigma3[2, 2] - 2.0 * sigma3[0, 2]),
        )
        box_val = min(
            m3[0] - m3[1] + rad * (math.sqrt(sigma3[0, 0]) + math.sqrt(sigma3[1, 1])),
            m3[0] - m3[2] + rad * (math.sqrt(sigma3[0, 0]) + math.sqrt(sigma3[2, 2])),
        )
        self.assertLess(gap, 1e-8)
        self.assertAlmostEqual(ell_val, float(slsqp.fun), places=6)
        self.assertLess(ell_val, pair_val - 0.10)
        self.assertLess(pair_val, box_val - 0.50)

        prob = CorrelatedSupportDAGProblem(seed=2, rho_in=0.85, rho_out=0.85)
        diag = real_world_problem_diagnostics(prob)
        self.assertEqual(diag["containment_pairs"], 0)
        self.assertEqual(diag["leaves"], 64)

        s_box = GPEllipsoidCertSession(
            prob, 201, 0.025, kernel=prob.kernel, prior_mean=prob.prior_mean,
            obs_std=prob.obs_std, rkhs_bound=prob.rkhs_bound, mode="box", beta_mode="rkhs_exact",
        )
        s_ell = GPEllipsoidCertSession(
            prob, 201, 0.025, kernel=prob.kernel, prior_mean=prob.prior_mean,
            obs_std=prob.obs_std, rkhs_bound=prob.rkhs_bound, mode="ellipsoid", beta_mode="rkhs_exact",
        )
        while not s_box.certified and s_box.calls < 14000:
            s_box.step()
        while not s_ell.certified and s_ell.calls < 14000:
            s_ell.step()
        self.assertTrue(s_ell.certified)
        self.assertLess(s_ell.calls, s_box.calls)
        vals = prob.graph.optimal_values(prob.means)
        v_star = vals[prob.graph.root]
        self.assertLessEqual(v_star - vals[prob.graph.children[prob.graph.root][s_ell.action]], 0.025 + 1e-12)

    def test_protein_kernel_misspecification_preserves_soundness(self):
        """All 4 protein kernels are SPD and preserve frequentist root soundness under misspecification."""
        import numpy as np

        prob = GB1MutationCampaignProblem(start_seq="FDGV", max_edits=3, panel="panel4")
        leaves = list(prob.graph.leaves)
        seqs = [prob.variant_of_leaf[z] for z in leaves]
        vals = prob.graph.optimal_values(prob.means)
        v_star = vals[prob.graph.root]

        for k_mode in ("structured", "hamming", "oversmooth", "scrambled_desc"):
            k_mat = alt_protein_sequence_kernel(seqs, mode=k_mode)
            eig_min = float(np.min(np.linalg.eigvalsh(k_mat)))
            self.assertGreater(eig_min, 1e-6, f"Kernel {k_mode} not SPD: min eig={eig_min}")
            sess = GPGuidedRootCertSession(
                prob, 707, 0.015, acquisition="gp_root_info", schedule="emp_bernstein", kernel=k_mat
            )
            while not sess.certified and sess.calls < 12000:
                sess.step()
            if sess.certified:
                v_rec = vals[prob.graph.children[prob.graph.root][sess.action]]
                self.assertLessEqual(v_star - v_rec, 0.015 + 1e-12)


if __name__ == "__main__":
    unittest.main()
