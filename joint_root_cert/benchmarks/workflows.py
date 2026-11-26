"""Agentic workflow configuration benchmarks (WorFBench + Qwen3-0.6B)."""
from __future__ import annotations

from pathlib import Path

from joint_root_cert._core.v6_real_world import (
    DATA_DIR,
    WORFBENCH_NPZ_PATH,
    WorFBenchWorkflowProblem,
)
from joint_root_cert._core.v7_bayesian_ucd import build_worfbench_feature_matrix

WORFBENCH_TEST_NPZ_PATH: Path = DATA_DIR / "worfbench_qwen3_test_81x32.npz"
WORFBENCH_DOMAINS: tuple[str, ...] = ("toolbench", "toolalpaca", "seal_tools", "webshop")

__all__ = [
    "WORFBENCH_DOMAINS",
    "WORFBENCH_NPZ_PATH",
    "WORFBENCH_TEST_NPZ_PATH",
    "WorFBenchWorkflowProblem",
    "build_worfbench_feature_matrix",
]
