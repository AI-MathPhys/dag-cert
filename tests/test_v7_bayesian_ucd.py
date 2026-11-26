"""Unit tests for v7 Correlation-Aware Bayesian and Frequentist Certification (`v7_bayesian_ucd`)."""
from __future__ import annotations

import math
import unittest

import cvxpy as cp
import numpy as np

from dagcert import DAG, Problem
from dagcert import HybridWitnessDAGLUCBSession
from dagcert.benchmarks import WorFBenchWorkflowProblem
from dagcert._core.v7_bayesian_ucd import (
    CorrelationAwareCertSession,
    JointEllipsoidCertifier,
    LinearFeatureModel,
    SupportStructure,
    build_worfbench_feature_matrix,
    compute_characteristic_rate,
    compute_hull_discrepancy,
    solve_alt_projection_dual,
    solve_feature_challenger_cvxpy,
    solve_primal_ellipsoid_regret,
)
from dagcert.benchmarks import (
    HullDominanceDAGProblem,
    MisspecifiedLinearDAGProblem,
    MotivationalProxyDAGProblem,
    MultiAnswerCommitmentDAGProblem,
)


class TestV7BayesianUCD(unittest.TestCase):
    def test_t1_primal_dual_socp_and_caratheodory_sparsity(self) -> None:
        """T1.1--T1.3: ColGen, Dense-AFW, CVXPY SOCP, and Primal Maximization agree and obey ordering."""
        rng = np.random.default_rng(20261118)
        # Include an action with full support S(a) = Z to verify empty-complement zero regret
        children = [
            (1, 2, 3),
            (4, 5, 6, 7, 8),
            (6, 7, 9, 10, 11),
            (4, 5, 6, 7, 8, 9, 10, 11),  # S(a_2) = Z
            *([()] * 8),
        ]
        graph = DAG(children, root=0)
        sup_struct = SupportStructure(graph)
        d = 3

        for trial in range(8):
            phi = rng.standard_normal((8, d))
            a_mat = rng.standard_normal((d, d))
            v_mat = 0.5 * np.eye(d) + a_mat.T @ a_mat
            v_inv = np.linalg.inv(v_mat)
            l_inv = np.linalg.cholesky(v_inv)
            psi = phi @ l_inv
            theta_hat = 0.3 * rng.standard_normal(d)
            means = phi @ theta_hat
            beta = float(rng.uniform(0.5, 2.0))
            stds = np.linalg.norm(psi, axis=1)

            cert_colgen = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="colgen_full")
            cert_lazy = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="colgen_lazy")
            cert_afw = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="dense_afw")
            cert_socp = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="cvxpy_socp")
            cert_vert = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="vertex_approx")

            # Empty complement S(a_2) = Z must return 0.0
            r_full_sup = cert_colgen.certify_action(2, means, psi, phi, beta)
            self.assertEqual(r_full_sup.regret, 0.0)

            for a in (0, 1):
                c_cg = cert_colgen.certify_action(a, means, psi, phi, beta)
                c_lz = cert_lazy.certify_action(a, means, psi, phi, beta)
                c_fw = cert_afw.certify_action(a, means, psi, phi, beta)
                c_sc = cert_socp.certify_action(a, means, psi, phi, beta)
                c_vt = cert_vert.certify_action(a, means, psi, phi, beta)
                prim = solve_primal_ellipsoid_regret(
                    a, sup_struct, phi, theta_hat, v_mat, beta, dense_grid_per_axis=25, seed=trial
                )

                sup = sup_struct.supports[a]
                comp = sup_struct.complements[a]
                r_box = max(0.0, float(np.max((means + beta * stds)[comp]) - np.max((means - beta * stds)[sup])))

                self.assertAlmostEqual(c_cg.regret, c_sc.regret, places=5)
                self.assertAlmostEqual(c_lz.regret, c_sc.regret, places=5)
                self.assertAlmostEqual(c_fw.regret, c_sc.regret, places=5)
                self.assertAlmostEqual(prim, c_sc.regret, places=4)
                # Ordering: R_ellipsoid <= R_vertex <= R_box
                self.assertLessEqual(c_cg.regret, c_vt.regret + 1e-7)
                self.assertLessEqual(c_vt.regret, r_box + 1e-7)
                # Caratheodory sparsity: |supp(p*)| <= d + 1
                self.assertLessEqual(len(c_cg.inside_indices), d + 1)

    def test_t2_exact_hull_dominance_zero_sample_certification(self) -> None:
        """T2.1: Exact convex-hull dominance certifies in 0 samples regardless of M on disjoint supports."""
        for m_leaves in (16, 64):
            prob = HullDominanceDAGProblem(seed=3, eta=0.0, m_leaves=m_leaves, k_actions=4, d_feat=4)
            sup_struct = SupportStructure(prob.graph)
            reports = compute_hull_discrepancy(prob.phi, sup_struct)
            self.assertTrue(reports[0].zero_sample_exact)
            self.assertLessEqual(reports[0].max_hull_dist_l2, 1e-8)

            model = LinearFeatureModel(
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                reg_lambda=1.0,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                beta_mode="abbasi_yadkori",
                delta=0.05,
            )
            sess = CorrelationAwareCertSession(
                prob, seed=101, epsilon=0.01, model=model, cert_mode="joint_ellipsoid", acquisition="contrast_directed"
            )
            self.assertTrue(sess.certified)
            self.assertEqual(sess.calls, 0)
            self.assertEqual(sess.action, 0)

            # Enclosing box and independent Optimistic-Separation cannot certify at t = 0
            os_sess = HybridWitnessDAGLUCBSession(prob, 101, 0.01, mode="opt_sep", schedule="emp_bernstein")
            self.assertFalse(os_sess.certified)

    def test_motivational_proxy_dag_off_witness_sampling(self) -> None:
        """Motivational Toy: Contrast-Directed queries low-mean z_proxy and beats witnesses/boxes."""
        prob = MotivationalProxyDAGProblem(hw=0.18)
        eps = 0.015

        model_cd = LinearFeatureModel(
            phi=prob.phi,
            prior_mean=prob.prior_mean,
            reg_lambda=0.02,
            obs_std=prob.obs_std,
            param_bound=prob.param_bound,
            beta_mode="abbasi_yadkori",
        )
        sess_cd = CorrelationAwareCertSession(
            prob, seed=7, epsilon=eps, model=model_cd, cert_mode="joint_ellipsoid", acquisition="contrast_directed"
        )
        while not sess_cd.certified and not sess_cd.conflict and sess_cd.calls < 4000:
            sess_cd.step()
        self.assertTrue(sess_cd.certified)
        self.assertEqual(sess_cd.action, 0)
        # Verify heavy use of off-witness proxy leaf (index 4 -> leaf 8)
        self.assertGreater(int(model_cd.arm_counts[4]), int(0.5 * sess_cd.calls))

        # Direct-witness restriction (cannot query z_proxy) requires far more samples
        model_dw = LinearFeatureModel(
            phi=prob.phi,
            prior_mean=prob.prior_mean,
            reg_lambda=0.02,
            obs_std=prob.obs_std,
            param_bound=prob.param_bound,
            beta_mode="abbasi_yadkori",
        )
        sess_dw = CorrelationAwareCertSession(
            prob, seed=7, epsilon=eps, model=model_dw, cert_mode="joint_ellipsoid", acquisition="direct_witness"
        )
        while not sess_dw.certified and not sess_dw.conflict and sess_dw.calls < 4000:
            sess_dw.step()
        self.assertLess(sess_cd.calls * 5, sess_dw.calls)

        # Independent Optimistic-Separation also requires far more samples
        sess_os = HybridWitnessDAGLUCBSession(prob, 7, eps, mode="opt_sep", schedule="emp_bernstein")
        while not sess_os.certified and sess_os.calls < 5000:
            sess_os.step()
        self.assertLess(sess_cd.calls * 5, sess_os.calls)

    def test_t4_safeguard_prevents_suboptimal_inside_witness_stalling(self) -> None:
        """Safeguarded contrast escapes suboptimal well-measured inside witness where naive contrast stalls."""
        # S(a0) = {y_sub (leaf 3), y_good (leaf 4)}, S(a1) = {z_out (leaf 5)}
        children = [(1, 2), (3, 4), (5,), (), (), ()]
        graph = DAG(children, root=0)
        phi = np.eye(3, dtype=np.float64)
        means = {3: 0.50, 4: 0.80, 5: 0.60}

        class _DetProblem(Problem):
            def oracle(self_p, seed: int):
                class _Orac:
                    def __init__(self) -> None:
                        self.obs = [0] * 6

                    def sample(self, leaf: int) -> float:
                        self.obs[leaf] += 1
                        return means[leaf]

                return _Orac()

        prob = _DetProblem("stall_test", graph, means, ())

        def make_preloaded_model() -> LinearFeatureModel:
            m = LinearFeatureModel(phi=phi, prior_mean=0.0, reg_lambda=1.0, obs_std=0.12, param_bound=1.2)
            # Preload 500 pulls on y_sub (idx 0) and z_out (idx 2) so g_dual = e_2 - e_0 has tiny variance
            for _ in range(500):
                m.observe(0, 0.50)
                m.observe(2, 0.60)
            return m

        m_naive = make_preloaded_model()
        s_naive = CorrelationAwareCertSession(
            prob, seed=1, epsilon=0.02, model=m_naive, cert_mode="joint_ellipsoid", acquisition="contrast_naive"
        )
        for _ in range(60):
            if s_naive.certified:
                break
            s_naive.step()
        self.assertFalse(s_naive.certified)
        self.assertEqual(int(m_naive.arm_counts[1]), 0)  # Never touched y_good!

        m_safe = make_preloaded_model()
        s_safe = CorrelationAwareCertSession(
            prob, seed=1, epsilon=0.02, model=m_safe, cert_mode="joint_ellipsoid", acquisition="contrast_directed"
        )
        while not s_safe.certified and s_safe.calls < 120:
            s_safe.step()
        self.assertTrue(s_safe.certified)
        self.assertEqual(s_safe.action, 0)
        self.assertGreater(int(m_safe.arm_counts[1]), 10)

    def test_t3_misspecification_identity_and_safe_hybrid(self) -> None:
        """T3.3: Robust misspecification certificate + safe_hybrid preserves soundness when 2*xi > eps."""
        prob = MisspecifiedLinearDAGProblem(seed=5, xi=0.04, m_leaves=24, k_actions=4, d_feat=4)
        model = LinearFeatureModel(
            phi=prob.phi,
            prior_mean=prob.prior_mean,
            reg_lambda=1.0,
            obs_std=prob.obs_std,
            param_bound=prob.param_bound,
            misspec_xi=prob.xi,
            beta_mode="misspec_robust",
        )
        # Here 2*xi = 0.08 > eps = 0.03, so pure linear model can never certify, while safe_hybrid succeeds soundly!
        sess = CorrelationAwareCertSession(
            prob,
            seed=19,
            epsilon=0.03,
            model=model,
            cert_mode="safe_hybrid",
            acquisition="contrast_directed",
            check_every=20,
        )
        while not sess.certified and sess.calls < 8000:
            sess.step()
        if sess.certified:
            vals = prob.graph.optimal_values(prob.means)
            v_star = float(vals[prob.graph.root])
            v_act = float(vals[prob.graph.children[prob.graph.root][sess.action]])
            self.assertLessEqual(v_star - v_act, 0.03 + 1e-12)

    def test_t5_alt_projection_dual_matches_cvxpy_qp_and_multianswer(self) -> None:
        """T5.1--T5.3: Variational dual matches CVXPY QP projection onto cl(H_eps(z, S(a))), and min_regret wins."""
        prob = MultiAnswerCommitmentDAGProblem(seed=11, epsilon=0.030, m_leaves=24)
        sup_struct = SupportStructure(prob.graph)
        d = prob.phi.shape[1]
        w = np.full(sup_struct.m, 1.0 / sup_struct.m)
        w_mat = (prob.phi.T * w) @ prob.phi + 1e-6 * np.eye(d)
        w_inv = np.linalg.inv(w_mat)

        # Verify solve_alt_projection_dual against direct CVXPY Quadratic Program on Action 0 vs outside z
        sup0 = sup_struct.supports[0]
        z_test = int(sup_struct.complements[0][0])
        kl_dual, _ = solve_alt_projection_dual(
            z_idx=z_test,
            sup=sup0,
            phi=prob.phi,
            theta_star=prob.theta_star,
            w_inv=w_inv,
            epsilon=0.030,
            sigma=prob.obs_std,
        )

        v_th = cp.Variable(d)
        diff = v_th - prob.theta_star
        constraints = [(prob.phi[z_test] - prob.phi[int(y)]) @ v_th >= 0.030 for y in sup0]
        qp = cp.Problem(cp.Minimize(cp.quad_form(diff, w_mat) / (2.0 * prob.obs_std ** 2)), constraints)
        qp.solve(solver=cp.CLARABEL, tol_gap_abs=1e-10, tol_gap_rel=1e-10)
        self.assertAlmostEqual(kl_dual, float(qp.value), places=5)

        # Characteristic rate should strongly favor acceptable action 1 (near-hull) over greedy action 0
        rate_res = compute_characteristic_rate(prob.phi, prob.theta_star, sup_struct, 0.030, prob.obs_std, n_outer_iters=30)
        self.assertEqual(rate_res.target_action, 1)
        self.assertGreater(rate_res.per_action_rates[1], 3.0 * rate_res.per_action_rates[0])

        # Verify WorFBench feature builder dimensions
        wf_prob = WorFBenchWorkflowProblem(domain="all", max_upgrades=3)
        f_inter = build_worfbench_feature_matrix(wf_prob, include_interactions=True)
        f_main = build_worfbench_feature_matrix(wf_prob, include_interactions=False)
        self.assertEqual(f_inter.shape, (len(wf_prob.graph.leaves), 33))
        self.assertEqual(f_main.shape, (len(wf_prob.graph.leaves), 9))


if __name__ == "__main__":
    unittest.main()
