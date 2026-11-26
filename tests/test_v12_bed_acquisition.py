"""Unit tests for v12 Decision-Aware Bayesian Experimental Design vs. BO primitives."""
from __future__ import annotations

import math
import unittest

import numpy as np
from scipy.stats import norm

from joint_root_cert._core.v12_bed_acquisition import (
    ALL_V12_POLICIES,
    FixedFeatureGaussianOverlapProblem,
    GaussianPairedDeconfoundedProblem,
    MatchedModelBEDSession,
    SharedGaussianPosterior,
    SmallOverlapCorrelationProblem,
    correlated_kg_log_scores,
    exact_correlated_kg_single,
    log_expected_pos_normal,
    noisy_gp_ei_log_scores,
    select_bayesian_root_voi,
)
from joint_root_cert import SupportStructure
from experiment.simulated.exp_factorial_and_proxy_sweep import TunableProxyDAGProblem


class TestV12BedAcquisition(unittest.TestCase):
    def test_log_expected_pos_normal_no_underflow(self) -> None:
        zs = np.array([-40.0, -15.0, -8.0, -3.0, -0.5, 0.0, 0.5, 3.0, 15.0])
        vals = log_expected_pos_normal(zs)
        self.assertTrue(np.all(np.isfinite(vals)))
        # Compare mid-range against direct scipy formula
        for z in (-3.0, -0.5, 0.0, 0.5, 3.0):
            exact = math.log(z * norm.cdf(z) + norm.pdf(z))
            self.assertAlmostEqual(float(log_expected_pos_normal(z)), exact, places=10)
        # Asymptotic check at z = -40: phi(z)/z^2
        z_far = -40.0
        asym = -0.5 * z_far * z_far - 0.5 * math.log(2.0 * math.pi) - 2.0 * math.log(abs(z_far))
        self.assertAlmostEqual(float(log_expected_pos_normal(z_far)), asym, places=2)

    def test_exact_correlated_kg_matches_monte_carlo(self) -> None:
        rng = np.random.default_rng(2026)
        m = 12
        a = rng.normal(0.5, 0.08, size=m)
        b = rng.normal(0.0, 0.05, size=m)
        kg_exact, log_kg = exact_correlated_kg_single(a, b)
        z = rng.standard_normal(400_000)
        vals = np.max(a[:, None] + b[:, None] * z[None, :], axis=0)
        kg_mc = float(np.mean(vals) - np.max(a))
        self.assertAlmostEqual(kg_exact, kg_mc, delta=4e-4)
        self.assertAlmostEqual(math.exp(log_kg), kg_exact, places=10)

        # Extreme tail case: never underflows in log-space!
        a_far = np.array([1.0, 0.0, -0.2])
        b_far = np.array([0.0, 0.02, -0.02])
        _, lkg_far = exact_correlated_kg_single(a_far, b_far)
        self.assertTrue(math.isfinite(lkg_far))
        self.assertLess(lkg_far, -500.0)

    def test_shared_gaussian_posterior_matches_batch_woodbury(self) -> None:
        prob = SmallOverlapCorrelationProblem(seed=7, overlap=0.75, rho=0.9)
        post = SharedGaussianPosterior(
            kernel=prob.kernel,
            prior_mean=prob.prior_mean,
            obs_std=prob.obs_std,
            delta=0.05,
            beta_mode="posterior_credible",
        )
        rng = np.random.default_rng(99)
        for _ in range(120):
            arm = int(rng.integers(0, 16))
            y = float(prob.means[5 + arm] + prob.obs_std * rng.standard_normal())
            post.observe(arm, y)

        m_inc = post.mean.copy()
        s_inc = post.sigma_mat.copy()
        ig_inc = float(post.info_gain)
        post.resync_exact()
        self.assertLess(float(np.max(np.abs(m_inc - post.mean))), 1e-11)
        self.assertLess(float(np.max(np.abs(s_inc - post.sigma_mat))), 1e-11)
        self.assertAlmostEqual(ig_inc, float(post.info_gain), places=8)

    def test_small16_and_fixed_feature_geometry_invariants(self) -> None:
        for om in (0.0, 0.75):
            for rh in (0.0, 0.9):
                p16 = SmallOverlapCorrelationProblem(seed=11, overlap=om, rho=rh)
                ss = SupportStructure(p16.graph)
                self.assertEqual(ss.m, 16)
                self.assertEqual(ss.k, 4)
                # Zero containment check
                for a in range(ss.k):
                    sa = set(ss.supports[a].tolist())
                    for b in range(ss.k):
                        if a != b:
                            sb = set(ss.supports[b].tolist())
                            self.assertFalse(sb.issubset(sa))
                if rh == 0.0:
                    off = p16.kernel - np.diag(np.diag(p16.kernel))
                    self.assertLess(float(np.max(np.abs(off))), 1e-15)

        pf = FixedFeatureGaussianOverlapProblem(seed=5, overlap=0.75, rho=0.9, d_feat=8)
        self.assertEqual(pf.phi.shape, (64, 8))
        self.assertGreater(pf.clean_rkhs_norm, 0.0)

    def test_bayesian_voi_prefers_informative_cheap_proxy(self) -> None:
        prob = TunableProxyDAGProblem(align=0.95, hw=0.16)
        ss = SupportStructure(prob.graph, costs=[1.0, 1.0, 1.0, 1.0, 0.25])
        # Linear Gaussian prior K = (sigma^2 / lambda) * Phi Phi^T
        reg_lam = 0.5
        k_mat = (prob.obs_std ** 2 / reg_lam) * (prob.phi @ prob.phi.T)
        post = SharedGaussianPosterior(
            kernel=k_mat,
            prior_mean=prob.prior_mean,
            obs_std=prob.obs_std,
            delta=0.05,
            beta_mode="posterior_credible",
        )
        rng = np.random.default_rng(123)
        y_q = norm.ppf((np.arange(32) + 0.5) / 32.0)
        u_crn = rng.standard_normal((5, 2048))
        chosen_cpp, scores_cpp, cur_risk, used_tail = select_bayesian_root_voi(
            means=post.mean,
            sigma_mat=post.sigma_mat,
            obs_var=post.obs_var,
            costs=ss.costs,
            supports=ss.supports,
            complements=ss.complements,
            epsilon=0.015,
            y_quantiles=y_q,
            std_normals=u_crn,
            use_cpp=True,
        )
        chosen_py, scores_py, _, _ = select_bayesian_root_voi(
            means=post.mean,
            sigma_mat=post.sigma_mat,
            obs_var=post.obs_var,
            costs=ss.costs,
            supports=ss.supports,
            complements=ss.complements,
            epsilon=0.015,
            y_quantiles=y_q,
            std_normals=u_crn,
            use_cpp=False,
        )
        self.assertEqual(chosen_cpp, chosen_py)
        self.assertLess(float(np.max(np.abs(scores_cpp - scores_py))), 1e-12)
        self.assertGreater(cur_risk, 0.05)
        self.assertFalse(used_tail)
        # Proxy is arm index 4; with alignment 0.95 and cost 0.25 it must dominate VOI/cost!
        self.assertEqual(chosen_cpp, 4, f"Expected proxy arm 4, got {chosen_cpp}, scores={scores_cpp}")

    def test_all_seven_policies_run_cleanly_on_shared_posterior(self) -> None:
        prob = SmallOverlapCorrelationProblem(seed=3, overlap=0.75, rho=0.9)
        for pol in ALL_V12_POLICIES:
            sess = MatchedModelBEDSession(
                problem=prob,
                obs_seed=777,
                policy=pol,
                epsilon=0.025,
                delta=0.05,
                kernel=prob.kernel,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                beta_mode="posterior_credible",
                full_check_every_step=True,
                budget_checkpoints=(10, 25),
                eval_mc_draws=512,
                voi_n_y=16,
                voi_n_mu=256,
                track_mc_risk_stop=True,
            )
            res = sess.run(cap=40)
            self.assertEqual(res["policy"], pol)
            self.assertGreaterEqual(res["steps"], 1)
            self.assertIn("10", res["checkpoints"])
            self.assertIn("25", res["checkpoints"])

    def test_kg_and_ei_log_scores_finite(self) -> None:
        prob = GaussianPairedDeconfoundedProblem(seed=1, overlap=0.75, rho=0.9)
        post = SharedGaussianPosterior(prob.kernel, prob.prior_mean, prob.obs_std)
        costs = np.ones(64, dtype=np.float64)
        ei = noisy_gp_ei_log_scores(post.mean, post.stds(), costs)
        kg_cpp = correlated_kg_log_scores(post.mean, post.sigma_mat, post.obs_var, costs, use_cpp=True)
        kg_py = correlated_kg_log_scores(post.mean, post.sigma_mat, post.obs_var, costs, use_cpp=False)
        self.assertTrue(np.all(np.isfinite(ei)))
        self.assertTrue(np.all(np.isfinite(kg_cpp)))
        self.assertLess(float(np.max(np.abs(kg_cpp - kg_py))), 1e-11)

    def test_fast_exact_stopping_matches_exhaustive_certifier(self) -> None:
        prob = SmallOverlapCorrelationProblem(seed=9, overlap=0.75, rho=0.9)
        sess = MatchedModelBEDSession(
            problem=prob,
            obs_seed=42,
            policy="cd_joint",
            epsilon=0.025,
            delta=0.05,
            kernel=prob.kernel,
            prior_mean=prob.prior_mean,
            obs_std=prob.obs_std,
            beta_mode="posterior_credible",
        )
        rng = np.random.default_rng(7)
        for step in range(250):
            arm = int(rng.integers(0, 16))
            sess.posterior.observe(arm, float(sess.oracle.sample(sess.support_struct.leaves[arm])))
            if step % 25 == 0:
                m = sess.posterior.mean
                s = sess.posterior.sigma_mat
                b = sess.posterior.beta()
                for a in range(sess.support_struct.k):
                    fast_ok, _ = sess._exact_check_action_certifies(a, m, s, b)
                    full_c = sess.certifier.certify_action_gp(a, m, s, b, stop_if_above_eps=False)
                    self.assertEqual(fast_ok, full_c.regret <= sess.epsilon)


if __name__ == "__main__":
    unittest.main()
