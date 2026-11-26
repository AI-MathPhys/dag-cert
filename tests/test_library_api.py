"""Unit tests for the public `dagcert` Python library API."""
from __future__ import annotations

import math
import unittest

import numpy as np

from dagcert import (
    BayesianVOIPolicy,
    CDJointPolicy,
    CorrelatedKGPolicy,
    GPOSPolicy,
    JointEllipsoidCertifier,
    SearchDAG,
    SharedGaussianPosterior,
    SupportStructure,
    certify_root_action,
    chi2_credible_beta,
    contrast_ellipsoid_coverage,
    contrast_rank_of_kernel,
    exact_rectangular_regret,
    make_policy,
)
from dagcert.benchmarks import (
    GB1_TEMPLATES,
    TRPB_TEMPLATES,
    GB1MutationCampaignProblem,
    TrpBMutationCampaignProblem,
    WorFBenchWorkflowProblem,
)


class TestDagCertLibraryAPI(unittest.TestCase):
    def test_search_dag_from_supports_and_regrets(self) -> None:
        dag = SearchDAG.from_supports([[0, 1], [1, 2]], action_labels=["a1", "a2"], leaf_labels=["z1", "zAB", "z2"])
        sups = dag.root_supports()
        self.assertEqual(len(sups), 2)
        self.assertEqual(sups[0].tolist(), [0, 1])
        self.assertEqual(sups[1].tolist(), [1, 2])
        regs = dag.root_regrets([0.75, 0.60, 0.40])
        self.assertAlmostEqual(float(regs[0]), 0.0, places=12)
        self.assertAlmostEqual(float(regs[1]), 0.15, places=12)
        ov = dag.support_overlap_matrix()
        self.assertAlmostEqual(float(ov[0, 1]), 1.0 / 3.0, places=12)

    def test_exact_rectangular_regret_cancels_shared_outcome(self) -> None:
        # Exact Figure 1b example from the manuscript (accepts both raw supports and SearchDAG)
        for sup_obj in ([[0, 1], [1, 2]], SearchDAG.from_supports([[0, 1], [1, 2]])):
            best_a, min_reg, regs = exact_rectangular_regret(
                supports=sup_obj,
                lower=[0.72, 0.40, 0.30],
                upper=[0.80, 0.95, 0.55],
            )
            self.assertEqual(best_a, 0)
            self.assertAlmostEqual(min_reg, 0.0, places=12)
            self.assertAlmostEqual(float(regs[1]), 0.40, places=12)

    def test_contrast_rank_and_mahalanobis_shift_invariance(self) -> None:
        rng = np.random.default_rng(7)
        a_mat = rng.standard_normal((10, 10))
        k_spd = a_mat @ a_mat.T / 10.0 + 0.1 * np.eye(10)
        r = contrast_rank_of_kernel(k_spd)
        self.assertEqual(r, 9)
        b95 = chi2_credible_beta(r, 0.95)
        b90 = chi2_credible_beta(r, 0.90)
        self.assertGreater(b95, b90)
        m = rng.standard_normal(10)
        t = rng.standard_normal(10)
        _, d1 = contrast_ellipsoid_coverage(m, k_spd, b95, t)
        _, d2 = contrast_ellipsoid_coverage(m, k_spd, b95, t + 9.5)
        self.assertAlmostEqual(d1, d2, places=8)

    def test_policy_objects_and_high_level_certify_root_action(self) -> None:
        dag = SearchDAG.from_supports([[0, 1, 2], [1, 2, 3]])
        ss = SupportStructure(dag)
        k_mat = 0.04 * np.eye(4) + 0.01 * np.ones((4, 4))
        post = SharedGaussianPosterior(k_mat, prior_mean=0.5, obs_std=0.08, delta=0.05)
        cert = JointEllipsoidCertifier(ss, epsilon=0.05, solver="colgen_lazy")

        for pol in (CDJointPolicy(), CorrelatedKGPolicy(), GPOSPolicy(), BayesianVOIPolicy(n_y=8, n_mu=128, seed=1)):
            arm = pol.select(post, ss, cert, epsilon=0.05)
            self.assertIn(arm, range(4))
        self.assertEqual(make_policy("cd_joint").name, "cd_joint")

        true_means = np.array([0.85, 0.65, 0.60, 0.42])
        for mode in ("credible_ellipsoid", "anytime_frequentist", "direct_posterior_risk", "distribution_free"):
            rng = np.random.default_rng(123)
            if mode == "distribution_free":
                obs = lambda z, _r=rng: float(np.clip(true_means[z] + 0.05 * _r.uniform(-1, 1), 0.0, 1.0))
            else:
                obs = lambda z, _r=rng: float(true_means[z] + 0.07 * _r.standard_normal())
            res = certify_root_action(
                dag=dag,
                observe_fn=obs,
                kernel=k_mat,
                prior_mean=0.5,
                obs_std=0.07,
                policy="cd_joint",
                stopping=mode,
                epsilon=0.05,
                delta=0.05,
                max_evals=1200,
                mc_draws=1024,
                seed=5,
            )
            self.assertTrue(res.certified, f"Expected certification under {mode}")
            self.assertEqual(res.action, 0)
            self.assertGreater(res.steps, 0)

    def test_bundled_domain_benchmarks_accessible(self) -> None:
        self.assertEqual(len(GB1_TEMPLATES), 10)
        self.assertEqual(len(TRPB_TEMPLATES), 21)
        gb1 = GB1MutationCampaignProblem(GB1_TEMPLATES[0], 3, "panel5")
        trpb = TrpBMutationCampaignProblem(TRPB_TEMPLATES[0], 3, "panel5")
        wf = WorFBenchWorkflowProblem("all")
        self.assertGreater(len(gb1.graph.leaves), 300)
        self.assertGreater(len(trpb.graph.leaves), 500)
        self.assertEqual(len(wf.graph.leaves), 64)


if __name__ == "__main__":
    unittest.main()
