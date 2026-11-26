"""Unit tests for v11 statistical validity ablation, 36-campaign live WorFBench harness, and independent oracle audit."""
from __future__ import annotations

import math
import unittest

import numpy as np
import pytest

from dagcert import SupportStructure
from experiment.protein_engineering.exp_validity_ablation import _cp_upper_95, _paired_bootstrap_ci
from experiment.agentic_workflows.exp_live_qwen3_36campaigns import (
    BASE_SPECS,
    _build_workflow_dag,
    _partition_disjoint_pools,
)
from experiment.simulated.exp_independent_oracle_audit import (
    audit_a_conic_regret_socp,
    audit_b_characteristic_rate_qp,
    audit_c1_v34_profiled_oracles,
    audit_c2_supermartingale_null_mc,
    audit_d_charged_dual_covers,
)


class TestV11Audit(unittest.TestCase):
    def test_independent_conic_socp_and_qp(self) -> None:
        res_a = audit_a_conic_regret_socp(n_instances=16, seed=101)
        self.assertTrue(res_a["passed"], f"Audit A failed: {res_a}")
        self.assertEqual(res_a["caratheodory_violations"], 0)

        res_b = audit_b_characteristic_rate_qp(n_dags=8, seed=102)
        self.assertTrue(res_b["passed"], f"Audit B failed: {res_b}")
        self.assertEqual(res_b["dom_failures"], 0)

    @pytest.mark.native  # also compares against the C++17 branch-and-bound
    def test_v34_oracles_and_supermartingale_null(self) -> None:
        res_c1 = audit_c1_v34_profiled_oracles(n_random=20, n_bimodal=10, seed=103)
        self.assertTrue(res_c1["passed"], f"Audit C1 failed: {res_c1}")
        self.assertEqual(res_c1["cubic_lb_violations"], 0)
        self.assertEqual(res_c1["py_bnb_lb_violations"], 0)
        self.assertEqual(res_c1["cpp_bnb_lb_violations"], 0)

        res_c2 = audit_c2_supermartingale_null_mc(n_draws=10_000, seed=104)
        self.assertTrue(res_c2["passed"], f"Audit C2 failed: {res_c2}")
        self.assertLessEqual(res_c2["max_mean_F"], 1.05)

    def test_charged_dual_covers_vs_bruteforce(self) -> None:
        res_d = audit_d_charged_dual_covers(n_dags=10, steps_per_dag=30, seed=105)
        self.assertTrue(res_d["passed"], f"Audit D failed: {res_d}")
        self.assertEqual(res_d["action_mismatches"], 0)
        self.assertEqual(res_d["witness_mismatches"], 0)

    def test_worfbench_disjoint_pools_and_zero_containment(self) -> None:
        fake_items = [
            {
                "id": f"task_{i}",
                "conversations": [
                    {"content": "sys"},
                    {"content": f"task {i}"},
                    {"content": "Node:\n1. a\nEdges:\n(START,1) (1,END)"},
                ],
            }
            for i in range(60)
        ]
        pools = _partition_disjoint_pools(fake_items, n_splits=3)
        self.assertEqual(len(pools), 3)
        all_ids = [t["id"] for p in pools for t in p]
        self.assertEqual(len(all_ids), len(set(all_ids)))  # Strictly disjoint across splits!
        # Strictly disjoint from exemplar [0], D_cal [1:17], and D_test [17:25]
        for i in range(25):
            self.assertNotIn(f"task_{i}", set(all_ids))

        for _, b_cfg in BASE_SPECS:
            dag, cfgs, _ = _build_workflow_dag(b_cfg)
            ss = SupportStructure(dag)
            self.assertEqual(ss.k, 4)
            self.assertEqual(ss.m, 10)
            self.assertEqual(ss.containment_pairs, 0)
            self.assertEqual(len(cfgs), 10)

    def test_statistical_helpers(self) -> None:
        # Exact Clopper-Pearson 95% upper bound for 0/200 is 1 - 0.05^(1/200) ~ 0.01487
        ub = _cp_upper_95(0, 200)
        self.assertAlmostEqual(ub, 1.0 - 0.05 ** (1.0 / 200.0), places=5)
        a = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        b = np.array([5.0, 10.0, 15.0, 20.0, 25.0])
        pt, lo, hi = _paired_bootstrap_ci(a, b, lambda x, y: float(np.median(x / y)), n_boot=500)
        self.assertAlmostEqual(pt, 2.0, places=6)
        self.assertAlmostEqual(lo, 2.0, places=6)
        self.assertAlmostEqual(hi, 2.0, places=6)


if __name__ == "__main__":
    unittest.main()
