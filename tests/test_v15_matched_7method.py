"""Unit and parity tests for the v15 7-method matched benchmarks, ablations, and Cholesky downdate."""
from __future__ import annotations

import unittest

import numpy as np

from dagcert import (
    JointEllipsoidCertifier,
    SharedGaussianPosterior,
    SupportStructure,
    chi2_credible_beta,
    contrast_rank_of_kernel,
    select_gp_arm_with_beta,
)
from dagcert._core.v12_bed_acquisition import (
    GaussianPairedDeconfoundedProblem,
    MatchedModelBEDSession,
)
from dagcert.benchmarks import (
    GB1MutationCampaignProblem,
    hamming_workflow_kernel,
    protein_sequence_kernel,
)
from experiment.agentic_workflows.exp_v15_worfbench_7method import audit_worfbench_sampling_protocol
from experiment.protein_engineering.exp_v15_protein_7method import predeclared_gb1_50_templates


class TestV15Matched7Method(unittest.TestCase):
    def test_cpp_cholesky_rank1_downdate_exact_parity(self) -> None:
        prob = GB1MutationCampaignProblem(start_seq="ADGV", max_edits=3, panel="panel5", noise_model="calibrated")
        ss = SupportStructure(prob.graph)
        seqs = [prob.variant_of_leaf[lf] for lf in ss.leaves]
        k_mat = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
        post = SharedGaussianPosterior(k_mat, 0.28, 0.16, delta=0.05)
        _ = post.cholesky()
        rng = np.random.default_rng(1234)
        for step in range(120):
            post.observe(int(rng.integers(0, ss.m)), float(rng.uniform(0.1, 0.9)))
            l_mat = post.cholesky()
            if step in (0, 25, 75, 119):
                err = float(np.max(np.abs(l_mat @ l_mat.T - post.sigma_mat)))
                self.assertLess(err, 1e-11)

    def test_gp_root_info_and_cd_joint_ablations_run_and_differ(self) -> None:
        prob = GaussianPairedDeconfoundedProblem(seed=5001, overlap=0.75, rho=0.9, target_margin=0.055, tau0=0.14, hw=0.14)
        recs = {}
        for pol in ("gp_root_info", "cd_joint", "cd_joint_no_safeguard", "cd_joint_single_witness"):
            sess = MatchedModelBEDSession(
                problem=prob,
                obs_seed=920001,
                policy=pol,
                epsilon=0.025,
                delta=0.05,
                kernel=prob.kernel,
                prior_mean=prob.prior_mean,
                obs_std=prob.obs_std,
                beta_mode="posterior_credible",
                budget_checkpoints=(),
                eval_mc_draws=64,
            )
            recs[pol] = sess.run(cap=400)
            self.assertIn("joint_coverage", recs[pol])
            self.assertIn("root_regret_bound_coverage", recs[pol])
            self.assertIn("safeguard_activations", recs[pol])
            self.assertIn("mean_mixture_support", recs[pol])
        self.assertEqual(recs["cd_joint_no_safeguard"]["safeguard_activations"], 0)
        self.assertAlmostEqual(recs["cd_joint_single_witness"]["mean_mixture_support"], 1.0, places=6)

    def test_hamming_workflow_kernel_strictly_spd_full_contrast_rank(self) -> None:
        configs = [(a, b, c, d) for a in range(3) for b in range(3) for c in range(3) for d in range(3)]
        k_mat = hamming_workflow_kernel(configs, prior_scale=0.22, lengthscale=2.0, nugget_frac=0.02)
        self.assertEqual(k_mat.shape, (81, 81))
        self.assertEqual(contrast_rank_of_kernel(k_mat), 80)
        self.assertGreater(float(np.min(np.linalg.eigvalsh(k_mat))), 0.0)

    def test_worfbench_sampling_with_replacement_audit(self) -> None:
        rep = audit_worfbench_sampling_protocol()
        self.assertTrue(rep["intrinsic_tape_identical_across_policies"])
        self.assertLess(rep["verified_20k_sample_mean_abs_error"], 0.01)

    def test_predeclared_gb1_50_templates_unique_and_nests_orig10(self) -> None:
        tmpls = predeclared_gb1_50_templates()
        self.assertEqual(len(tmpls), 50)
        self.assertEqual(len(set(tmpls)), 50)
        self.assertEqual(tmpls[:10], ("VDGV", "FDGV", "LDGV", "WDGV", "YDGV", "IDGV", "ADGV", "VDGA", "VWGV", "LWGV"))


if __name__ == "__main__":
    unittest.main()
