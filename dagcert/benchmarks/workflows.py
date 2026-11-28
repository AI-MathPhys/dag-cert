"""Agentic workflow configuration benchmarks (WorFBench + Qwen3-0.6B)."""
from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path

import numpy as np

from dagcert._core.v6_real_world import (
    DATA_DIR,
    WORFBENCH_NPZ_PATH,
    WorFBenchWorkflowProblem,
)
from dagcert._core.v7_bayesian_ucd import build_worfbench_feature_matrix

WORFBENCH_TEST_NPZ_PATH: Path = DATA_DIR / "worfbench_qwen3_test_81x32.npz"
WORFBENCH_DOMAINS: tuple[str, ...] = ("toolbench", "toolalpaca", "seal_tools", "webshop")


def hamming_workflow_kernel(
    configs: Sequence[Sequence[int]],
    prior_scale: float = 0.22,
    lengthscale: float = 2.0,
    nugget_frac: float = 0.02,
) -> np.ndarray:
    """Strictly positive-definite Hamming exponential kernel over 4-stage workflows.

    Computes ``k(z, z') = sigma_f^2 * exp(-d_H(z, z') / ell) + (nugget_frac * sigma_f^2) * 1_{z == z'}``
    where ``d_H(z, z')`` is the Hamming distance across categorical workflow stages.
    Strictly positive definite (exact contrast rank ``M - 1``) for every ``lengthscale > 0``
    and ``nugget_frac > 0``.
    """
    arr = np.asarray(configs, dtype=np.int32)
    if arr.ndim != 2:
        raise ValueError("configs must be a 2-D array of shape (M, n_stages)")
    m = int(arr.shape[0])
    d_h = np.sum(arr[:, None, :] != arr[None, :, :], axis=2).astype(np.float64)
    sf2 = float(prior_scale) * float(prior_scale)
    k_mat = sf2 * np.exp(-d_h / float(lengthscale)) + (float(nugget_frac) * sf2) * np.eye(m, dtype=np.float64)
    return 0.5 * (k_mat + k_mat.T)


__all__ = [
    "WORFBENCH_DOMAINS",
    "WORFBENCH_NPZ_PATH",
    "WORFBENCH_TEST_NPZ_PATH",
    "WorFBenchWorkflowProblem",
    "build_worfbench_feature_matrix",
    "hamming_workflow_kernel",
]
