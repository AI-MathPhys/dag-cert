"""Passive trajectory-coupled UCT/PUCT certification and native C++17 maintenance kernels."""
from __future__ import annotations

from dagcert._core.compiled_retirement import (
    CircuitMonitor,
    Search as TrajectoryCoupledUCT,
    cover_compile,
    leaf_order,
    quotient,
)
from dagcert._core.puct import (
    CertifiedSearchSession,
    RecursivePUCT,
    RootPUCT,
    build_monitor,
    make_priors,
)
from dagcert._core.v3_extensions import (
    CppKernelRunner,
    SplitMixProblem,
    WitnessDirectGraphRegret,
    WitnessDualCovers,
    WitnessFactorizedRegret,
    WitnessMarginalGraph,
    WitnessMaxHeap,
    build_witness_monitor,
    splitmix_uniform01,
)
from dagcert._core.v4_baselines import CppSameGameRunner

__all__ = [
    "CertifiedSearchSession",
    "CircuitMonitor",
    "CppKernelRunner",
    "CppSameGameRunner",
    "RecursivePUCT",
    "RootPUCT",
    "SplitMixProblem",
    "TrajectoryCoupledUCT",
    "WitnessDirectGraphRegret",
    "WitnessDualCovers",
    "WitnessFactorizedRegret",
    "WitnessMarginalGraph",
    "WitnessMaxHeap",
    "build_monitor",
    "build_witness_monitor",
    "cover_compile",
    "leaf_order",
    "make_priors",
    "quotient",
    "splitmix_uniform01",
]
