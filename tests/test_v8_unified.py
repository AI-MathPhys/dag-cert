"""Unit tests for v8 Unified Validation Primitives (Experiments 1--6)."""
from __future__ import annotations

import unittest

import numpy as np

from joint_root_cert.benchmarks import noncontainment_star_dag
from joint_root_cert.benchmarks import real_world_problem_diagnostics
from joint_root_cert import LinearFeatureModel, SupportStructure
from joint_root_cert.benchmarks import MisspecifiedLinearDAGProblem, MotivationalProxyDAGProblem, ScalingDAGProblem
from joint_root_cert._core.v8_unified_experiments import (
    AdaptiveHardRegimeSession,
    DeconfoundedOverlapCorrelationProblem,
    RegularizedInfoTrackerSession,
    ScheduledConicCertifier,
    SmartHybridCertSession,
    verify_characteristic_rate_independently,
)


class TestV8Unified(unittest.TestCase):
    def test_smart_hybrid_resolves_infeasible_bias_floor_without_false_certs(self):
        """SmartHybridCertSession certifies via distribution-free fallback when 2*xi >= eps."""
        prob = MisspecifiedLinearDAGProblem(seed=11, xi=0.05, m_leaves=24, k_actions=4, d_feat=5, hw=0.14)
        vals = prob.graph.optimal_values(prob.means)
        opt_mu = float(vals[prob.graph.root])
        root_ch = prob.graph.children[prob.graph.root]

        model = LinearFeatureModel(
            phi=prob.phi,
            prior_mean=prob.prior_mean,
            reg_lambda=0.5,
            obs_std=prob.obs_std,
            param_bound=prob.param_bound,
            misspec_xi=0.05,
            beta_mode="misspec_robust",
            delta=0.05,
        )
        sess = SmartHybridCertSession(
            prob,
            seed=901,
            epsilon=0.04,
            model=model,
            cert_mode="smart_hybrid",
            acquisition="contrast_directed",
            delta=0.05,
        )
        self.assertTrue(sess.switched_to_df)
        while not sess.certified and not sess.conflict and sess.calls < 6000:
            sess.step()
        self.assertTrue(sess.certified)
        self.assertLessEqual(opt_mu - float(vals[root_ch[sess.action]]), 0.04 + 1e-12)

    def test_info_tracker_and_independent_cvxpy_rate_verification(self):
        """RegularizedInfoTrackerSession & Hybrid CD->Tracker certify soundly and rate matches CVXPY."""
        prob = MotivationalProxyDAGProblem(hw=0.14)
        ss = SupportStructure(prob.graph)
        ver = verify_characteristic_rate_independently(
            phi=prob.phi,
            theta_star=prob.theta_star,
            support_struct=ss,
            epsilon=0.015,
            sigma=prob.obs_std,
            n_random_designs=80,
            seed=7,
        )
        self.assertLess(ver["max_qp_dual_diff"], 1e-4)
        self.assertGreaterEqual(ver["rate_dominates_random"], 0.5)

        vals = prob.graph.optimal_values(prob.means)
        opt_mu = float(vals[prob.graph.root])
        root_ch = prob.graph.children[prob.graph.root]

        for hyb in (False, True):
            sess = RegularizedInfoTrackerSession(
                prob,
                seed=205,
                epsilon=0.015,
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                delta=0.05,
                hybrid_cd_warmup=hyb,
                recompute_every=8,
                outer_iters=30,
            )
            while not sess.certified and sess.calls < 400:
                sess.step()
            self.assertTrue(sess.certified)
            self.assertLessEqual(opt_mu - float(vals[root_ch[sess.action]]), 0.015 + 1e-12)

    def test_deconfounded_problem_diagonal_at_rho_zero_and_zero_containments(self):
        """DeconfoundedOverlapCorrelationProblem has strictly diagonal K at rho=0 and 0 containments."""
        for ov in (0.0, 0.25, 0.50, 0.75):
            p0 = DeconfoundedOverlapCorrelationProblem(seed=1, overlap=ov, rho=0.0, mismatch_xi=0.0)
            diag = real_world_problem_diagnostics(p0)
            self.assertEqual(diag["containment_pairs"], 0)
            off_diag = p0.kernel - np.diag(np.diag(p0.kernel))
            self.assertLess(float(np.max(np.abs(off_diag))), 1e-14)
            if ov == 0.0:
                self.assertAlmostEqual(diag["mean_pairwise_jaccard"], 0.0, places=6)
            else:
                self.assertGreater(diag["mean_pairwise_jaccard"], 0.0)

        p_hi = DeconfoundedOverlapCorrelationProblem(seed=1, overlap=0.5, rho=0.9, mismatch_xi=0.04)
        self.assertAlmostEqual(float(np.max(np.abs(p_hi.b_vec))), 0.04, places=3)

    def test_scheduled_conic_certifiers_always_sound_upper_bounds(self):
        """All 5 ScheduledConicCertifier strategies produce provably sound upper bounds >= exact."""
        prob = ScalingDAGProblem(seed=17, m_leaves=64, k_actions=4, d_feat=6, support_style="compact")
        ss = SupportStructure(prob.graph)
        oracle = prob.oracle(117)
        model = LinearFeatureModel(
            phi=prob.phi, prior_mean=prob.prior_mean, reg_lambda=0.5, obs_std=prob.obs_std,
            param_bound=prob.param_bound, beta_mode="abbasi_yadkori", delta=0.05,
        )
        rng = np.random.default_rng(17)
        snaps = []
        for _ in range(12):
            for _ in range(5):
                idx = int(rng.integers(0, len(ss.leaves)))
                model.observe(idx, oracle.sample(ss.leaves[idx]))
            m, psi = model.terminal_means_and_psi()
            snaps.append((m.copy(), psi.copy(), float(model.beta())))

        certs = {st: ScheduledConicCertifier(ss, epsilon=0.03, strategy=st, period=4) for st in ScheduledConicCertifier.STRATEGIES}
        for m, psi, beta in snaps:
            exact_r = certs["exact_every_step"].evaluate_action(0, m, psi, prob.phi, beta)
            for st in ("lazy_every_step", "periodic_conservative", "adaptive_tol_lazy", "hybrid_rect_joint"):
                r_st = certs[st].evaluate_action(0, m, psi, prob.phi, beta)
                # Every approximate/cached feasible mixture must be a valid UPPER bound (>= exact - numerical tol)
                self.assertGreaterEqual(r_st, exact_r - 1e-4, f"{st} underestimated exact regret: {r_st} < {exact_r}")

    def test_adaptive_hard_regime_certifies_tied_star_eps_zero(self):
        """AdaptiveHardRegimeSession certifies non-containment tied-star at exact eps=0."""
        prob, _ = noncontainment_star_dag(n_rivals=6, gap=0.25, eps=0.0)
        vals = prob.graph.optimal_values(prob.means)
        opt_mu = float(vals[prob.graph.root])
        root_ch = prob.graph.children[prob.graph.root]

        for mode in AdaptiveHardRegimeSession.VALID_MODES:
            sess = AdaptiveHardRegimeSession(prob, seed=401, epsilon=0.0, mode=mode, schedule="box")
            while not sess.certified and sess.calls < 8000:
                sess.step()
            self.assertTrue(sess.certified, f"{mode} failed on tied-star eps=0")
            self.assertLessEqual(opt_mu - float(vals[root_ch[sess.action]]), 1e-12)


if __name__ == "__main__":
    unittest.main()
