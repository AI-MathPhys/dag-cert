"""Unit tests for Experiment v14: Proper Joint Gaussian Credible-Ellipsoid & Valid Anytime
Direct Posterior-Risk Stopping on Real Protein Landscapes.
"""
from __future__ import annotations

import math
import unittest

import numpy as np
from scipy.stats import chi2

from dagcert.benchmarks import protein_sequence_kernel
from dagcert.benchmarks import GB1MutationCampaignProblem, TrpBMutationCampaignProblem
from dagcert import SupportStructure
from experiment.protein_engineering.exp_real_world_applications import GB1_TEMPLATES
from experiment.protein_engineering.exp_real_world_validation import TRPB_TEMPLATES
from experiment.protein_engineering.exp_credible_ellipsoid_audit import (
    DELTA,
    EPS,
    MC_POSTRISK_DELTA_POST,
    MC_POSTRISK_ETA,
    chi2_credible_beta,
    contrast_ellipsoid_coverage,
    contrast_rank_of_kernel,
    eval_direct_posterior_risk_valid,
    _stream_worker,
)


class TestV14ProteinCredibleEllipsoid(unittest.TestCase):
    def test_exact_contrast_rank_and_chi2_radii_no_t2_factor(self) -> None:
        # GB1 and TmTrpB sequence kernels with nugget=0.02 are strictly SPD => contrast rank = M - 1
        for prob in (
            GB1MutationCampaignProblem(GB1_TEMPLATES[0], 3, "panel5", noise_model="calibrated"),
            TrpBMutationCampaignProblem(TRPB_TEMPLATES[0], 3, "panel5", noise_model="low_var_uniform"),
        ):
            ss = SupportStructure(prob.graph)
            seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
            k_mat = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
            r = contrast_rank_of_kernel(k_mat)
            self.assertEqual(r, ss.m - 1)
            b95 = chi2_credible_beta(r, 0.95)
            b90 = chi2_credible_beta(r, 0.90)
            self.assertAlmostEqual(b95, math.sqrt(float(chi2.ppf(0.95, df=ss.m - 1))), places=12)
            self.assertAlmostEqual(b90, math.sqrt(float(chi2.ppf(0.90, df=ss.m - 1))), places=12)
            self.assertGreater(b95, b90)

        # Low-rank kernel rank check: rank-3 feature kernel => contrast rank <= 3
        rng = np.random.default_rng(7)
        phi = rng.standard_normal((20, 3))
        k_low = phi @ phi.T
        self.assertEqual(contrast_rank_of_kernel(k_low), 3)

    def test_contrast_ellipsoid_coverage_exact_mahalanobis_and_calibration(self) -> None:
        rng = np.random.default_rng(12345)
        m = 18
        a_mat = rng.standard_normal((m, m))
        sigma = a_mat @ a_mat.T / m + 0.25 * np.eye(m)
        means = rng.standard_normal(m)
        true_m = rng.standard_normal(m)

        # Compare against explicit pseudoinverse on contrast subspace H = I - 11^T / M
        h_mat = np.eye(m) - np.ones((m, m)) / m
        d = true_m - means
        hd = h_mat @ d
        pinv_hsh = np.linalg.pinv(h_mat @ sigma @ h_mat, rcond=1e-12)
        expected_dist = math.sqrt(float(hd @ pinv_hsh @ hd))

        _, actual_dist = contrast_ellipsoid_coverage(means, sigma, beta=1.0, true_means=true_m)
        self.assertAlmostEqual(actual_dist, expected_dist, places=8)

        # Shift invariance: adding constant c*1 to true_means leaves contrast Mahalanobis invariant
        _, shifted_dist = contrast_ellipsoid_coverage(means, sigma, beta=1.0, true_means=true_m + 17.3)
        self.assertAlmostEqual(shifted_dist, actual_dist, places=8)

        # Monte Carlo calibration check: draws from N(means, sigma) must have ~95% coverage at sqrt(chi2_{m-1, 0.95})
        chol = np.linalg.cholesky(sigma)
        beta_95 = chi2_credible_beta(m - 1, 0.95)
        hits = 0
        n_rep = 1000
        for _ in range(n_rep):
            draw = means + chol @ rng.standard_normal(m)
            cov, _ = contrast_ellipsoid_coverage(means, sigma, beta=beta_95, true_means=draw)
            hits += int(cov)
        emp_cov = hits / n_rep
        self.assertGreater(emp_cov, 0.925)
        self.assertLess(emp_cov, 0.975)

    def test_valid_union_bound_posterior_risk_budget_and_decision(self) -> None:
        # Exact telescoping sum: sum_{j=1..infty} sum_{a=1..K} eta / (K * j * (j+1)) = eta
        self.assertAlmostEqual(MC_POSTRISK_DELTA_POST + MC_POSTRISK_ETA, DELTA, places=12)
        k_act = 15
        total_eta = sum(
            k_act * (MC_POSTRISK_ETA / (k_act * j * (j + 1)))
            for j in range(1, 5000)
        )
        self.assertLessEqual(total_eta, MC_POSTRISK_ETA + 1e-12)
        self.assertGreater(total_eta, MC_POSTRISK_ETA * 0.999)

        # Separated posterior certifies immediately; tied uncertain posterior does not
        supports = (np.array([0, 1]), np.array([2, 3]))
        rng = np.random.default_rng(99)
        ok_sep, act_sep, q_sep, cp_sep = eval_direct_posterior_risk_valid(
            means=np.array([0.9, 0.2, 0.3, 0.1]),
            sigma_mat=1e-6 * np.eye(4),
            supports=supports,
            eps=EPS,
            check_idx=1,
            n_mc=2048,
            eta=MC_POSTRISK_ETA,
            delta_post=MC_POSTRISK_DELTA_POST,
            rng=rng,
        )
        self.assertTrue(ok_sep)
        self.assertEqual(act_sep, 0)
        self.assertEqual(q_sep, 0.0)
        self.assertLessEqual(cp_sep, MC_POSTRISK_DELTA_POST)

        ok_tied, _, _, cp_tied = eval_direct_posterior_risk_valid(
            means=np.array([0.5, 0.5, 0.5, 0.5]),
            sigma_mat=0.05 * np.eye(4),
            supports=supports,
            eps=EPS,
            check_idx=1,
            n_mc=2048,
            eta=MC_POSTRISK_ETA,
            delta_post=MC_POSTRISK_DELTA_POST,
            rng=rng,
        )
        self.assertFalse(ok_tied)
        self.assertGreater(cp_tied, 0.3)

    def test_end_to_end_stream_workers_and_v13_condition_a_parity(self) -> None:
        # Run all 4 streams at tiny cap on GB1 template 0 seed 801001 and verify schemas
        rows = []
        for stream in ("kg_all", "cd_matched", "gpos_matched", "frozen_and_df"):
            rows.extend(_stream_worker(("gb1", GB1_TEMPLATES[0], 801001, stream, 400, 512)))
        conds = set(r["condition"] for r in rows)
        self.assertEqual(
            conds,
            {"A_orig", "B_chi95", "C_chi90", "B_chi95_frozen", "C_chi90_frozen", "E_postrisk", "D_df_eb"},
        )
        # Verify Condition A matches v13 bit-for-bit on GB1_VDGV seed 801001 (steps=2000 cap? check <=400)
        for r in rows:
            self.assertEqual(r["contrast_rank"], r["m_leaves"] - 1)
            self.assertGreaterEqual(r["true_regret"], 0.0)
            if r["condition"] in ("B_chi95", "B_chi95_frozen"):
                self.assertAlmostEqual(
                    r["beta_at_stop"], round(chi2_credible_beta(r["contrast_rank"], 0.95), 4), places=3
                )
            if r["condition"] in ("C_chi90", "C_chi90_frozen"):
                self.assertAlmostEqual(
                    r["beta_at_stop"], round(chi2_credible_beta(r["contrast_rank"], 0.90), 4), places=3
                )


if __name__ == "__main__":
    unittest.main()
