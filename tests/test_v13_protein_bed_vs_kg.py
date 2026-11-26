"""Unit tests for v13 matched protein BED vs. Correlated KG benchmark."""
from __future__ import annotations

import math
import unittest

import numpy as np

from dagcert.benchmarks import protein_sequence_kernel
from dagcert.benchmarks import GB1MutationCampaignProblem, TrpBMutationCampaignProblem
from dagcert import JointEllipsoidCertifier, SupportStructure
from dagcert import SharedGaussianPosterior, correlated_kg_log_scores
from experiment.protein_engineering.exp_matched_bed_vs_kg import (
    _check_bayes_ellipsoid,
    _nominal_gp_beta,
    run_gp_root_info_df_and_df_os,
    run_single_instance_policy,
)


class TestV13ProteinBedVsKg(unittest.TestCase):
    def test_intrinsic_observation_tape_identical_across_policies(self) -> None:
        """Intrinsic noise tape returns exact same k-th observation per leaf regardless of order."""
        prob = GB1MutationCampaignProblem("FDGV", max_edits=3, panel="panel5", noise_model="calibrated")
        leaves = prob.graph.leaves[:10]
        o1 = prob.oracle(801001)
        o2 = prob.oracle(801001)
        seq1 = {z: [o1.sample(z) for _ in range(5)] for z in leaves}
        # Interleave reverse order in o2
        seq2 = {z: [] for z in leaves}
        for _ in range(5):
            for z in reversed(leaves):
                seq2[z].append(o2.sample(z))
        for z in leaves:
            self.assertEqual(seq1[z], seq2[z])

    def test_cpp_correlated_kg_exact_parity_on_protein_kernel(self) -> None:
        """C++17 7-pivot pre-filtered Correlated KG matches pure Python on real protein GP."""
        prob = GB1MutationCampaignProblem("ADGV", max_edits=3, panel="panel5", noise_model="calibrated")
        ss = SupportStructure(prob.graph)
        seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
        k_mat = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
        post = SharedGaussianPosterior(k_mat, prior_mean=0.28, obs_std=0.16, delta=0.05)
        oracle = prob.oracle(801001)
        for i in range(60):
            idx = (i * 19) % ss.m
            post.observe(idx, oracle.sample(ss.leaves[idx]))
        c_scores = correlated_kg_log_scores(post.mean, post.sigma_mat, post.obs_var, ss.costs, use_cpp=True)
        p_scores = correlated_kg_log_scores(post.mean, post.sigma_mat, post.obs_var, ss.costs, use_cpp=False)
        self.assertLess(float(np.max(np.abs(c_scores - p_scores))), 1e-6)
        self.assertEqual(int(np.argmax(c_scores)), int(np.argmax(p_scores)))

    def test_single_pass_multi_eps_matches_standalone_runs(self) -> None:
        """Multi-eps single pass for eps-independent policies matches standalone single-eps runs bit-for-bit."""
        prob = TrpBMutationCampaignProblem("VFVS", max_edits=3, panel="panel5", noise_model="low_var_uniform")
        ss = SupportStructure(prob.graph)
        seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
        k_mat = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
        true_mu = np.array([float(prob.means[z]) for z in ss.leaves], dtype=np.float64)
        l2a: list[list[int]] = [[] for _ in range(ss.m)]
        for a, sup in enumerate(ss.supports):
            for idx in sup:
                l2a[int(idx)].append(a)

        joint_rows = run_single_instance_policy(
            prob, ss, l2a, k_mat, 0.30, 0.08 / math.sqrt(3.0), regrets, true_mu,
            seed=802001, policy="gp_os", eps_targets=(0.015, 0.010), cap=600, delta=0.05,
            landscape="trpb", start_seq="VFVS", regime_tag="single_peak", run_df_confirm=False,
        )
        for eps in (0.015, 0.010):
            solo_rows = run_single_instance_policy(
                prob, ss, l2a, k_mat, 0.30, 0.08 / math.sqrt(3.0), regrets, true_mu,
                seed=802001, policy="gp_os", eps_targets=(eps,), cap=600, delta=0.05,
                landscape="trpb", start_seq="VFVS", regime_tag="single_peak", run_df_confirm=False,
            )
            for reg_name in ("bayes_ellipsoid", "df_emp_bernstein"):
                r_j = next(r for r in joint_rows if r["stopping_regime"] == reg_name and abs(r["eps"] - eps) < 1e-9)
                r_s = next(r for r in solo_rows if r["stopping_regime"] == reg_name and abs(r["eps"] - eps) < 1e-9)
                self.assertEqual(r_j["certified"], r_s["certified"])
                self.assertEqual(r_j["steps"], r_s["steps"])
                self.assertEqual(r_j["action"], r_s["action"])
                self.assertEqual(r_j["distinct_leaves"], r_s["distinct_leaves"])

    def test_all_methods_and_df_confirmation_end_to_end(self) -> None:
        """All 5 matched GP policies, DF-confirm handoffs, GP-Root-Info (DF), and DF-OS run cleanly."""
        prob = TrpBMutationCampaignProblem("VFVS", max_edits=3, panel="panel5", noise_model="low_var_uniform")
        ss = SupportStructure(prob.graph)
        seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
        k_mat = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
        true_mu = np.array([float(prob.means[z]) for z in ss.leaves], dtype=np.float64)
        l2a: list[list[int]] = [[] for _ in range(ss.m)]
        for a, sup in enumerate(ss.supports):
            for idx in sup:
                l2a[int(idx)].append(a)

        rows = []
        for pol in ("gp_ucb", "kg", "gp_root_info_gp", "gp_os", "cd_joint"):
            rows.extend(
                run_single_instance_policy(
                    prob, ss, l2a, k_mat, 0.30, 0.08 / math.sqrt(3.0), regrets, true_mu,
                    seed=802001, policy=pol, eps_targets=(0.015,), cap=600, delta=0.05,
                    landscape="trpb", start_seq="VFVS", regime_tag="single_peak",
                    run_df_confirm=(pol in ("cd_joint", "kg")),
                )
            )
        rows.extend(
            run_gp_root_info_df_and_df_os(
                prob, ss, k_mat, 0.30, 0.08 / math.sqrt(3.0), regrets,
                seed=802001, eps_targets=(0.015,), cap=600, delta=0.05,
                landscape="trpb", start_seq="VFVS", regime_tag="single_peak",
            )
        )
        # CD-Joint and KG should both certify VFVS cleanly under Regime A within 600 assays with 0 error
        for pol in ("cd_joint", "kg", "gp_os"):
            r_b = next(r for r in rows if r["method"] == pol and r["stopping_regime"] == "bayes_ellipsoid")
            self.assertTrue(r_b["certified"], f"{pol} failed to certify VFVS within 600 assays")
            self.assertFalse(r_b["false_cert"])
            self.assertLessEqual(r_b["true_regret"], 0.015 + 1e-12)
        # Verify DF-confirm rows produced
        names = {(r["stopping_regime"], r["method"]) for r in rows}
        self.assertIn(("df_emp_bernstein", "cd_joint_df_confirm"), names)
        self.assertIn(("df_emp_bernstein", "kg_df_confirm"), names)
        self.assertIn(("df_emp_bernstein", "gp_root_info_df"), names)
        self.assertIn(("df_emp_bernstein", "df_os"), names)

    def test_exact_bayes_certifier_matches_exhaustive_check(self) -> None:
        """Center-mean filter in `_check_bayes_ellipsoid` never misses a certifying action."""
        prob = TrpBMutationCampaignProblem("VFVS", max_edits=3, panel="panel5", noise_model="low_var_uniform")
        ss = SupportStructure(prob.graph)
        seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
        k_mat = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
        post = SharedGaussianPosterior(k_mat, 0.30, 0.08 / math.sqrt(3.0), delta=0.05)
        oracle = prob.oracle(802001)
        cert = JointEllipsoidCertifier(ss, epsilon=0.015, solver="colgen_lazy", exact_linear_mean=False)
        for step in range(1, 280):
            idx = (step * 17) % ss.m
            post.observe(idx, oracle.sample(ss.leaves[idx]))
        beta = _nominal_gp_beta(ss.m, 280, 0.05)
        ok_fast, _, _ = _check_bayes_ellipsoid(cert, ss, post.mean, post.sigma_mat, post.stds(), beta, 0.015)
        ok_all = any(
            cert.certify_action_gp(a, post.mean, post.sigma_mat, beta, stop_if_above_eps=True).regret <= 0.015
            for a in range(ss.k)
        )
        self.assertEqual(ok_fast, ok_all)


if __name__ == "__main__":
    unittest.main()
