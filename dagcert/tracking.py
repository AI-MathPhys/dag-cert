"""Information-optimal, unknown-variance (V34), hybrid, and active exact-regret trackers."""
from __future__ import annotations

from dagcert._core.v3_extensions import ActiveDAGLUCBSession
from dagcert._core.v4_baselines import (
    InsideWitnessDAGLUCBSession,
    LUCBMicroSession,
    UGapEMCTSSession,
    VarDEDAGSession,
)
from dagcert._core.v5_hybrid_and_os import HybridWitnessDAGLUCBSession
from dagcert._core.v6_bayesian_opt import (
    GPBoxCertSession,
    GPEllipsoidCertSession,
    GPGuidedRootCertSession,
)
from dagcert._core.v6_real_world import FlatLUCBSession
from dagcert._core.v7_bayesian_ucd import (
    CorrelationAwareCertSession,
    compute_characteristic_rate,
)
from dagcert._core.v8_unified_experiments import (
    AdaptiveHardRegimeSession,
    RegularizedInfoTrackerSession,
    SmartHybridCertSession,
    fast_characteristic_rate,
    verify_characteristic_rate_independently,
)
from dagcert._core.v9_v34_tracker import (
    CertifiedDesignResult,
    CertifiedProjectionResult,
    ComponentPolyhedron,
    CppV34BnBRunner,
    IntrinsicGaussianTape,
    V34RunResult,
    batch_schedule_sizes,
    build_screened_components,
    compute_exact_nuisance_kl_rate,
    eval_action_info_certified,
    eval_profiled_loss,
    is_four_power_refresh,
    is_square_refresh,
    largest_remainder_counts,
    refresh_level,
    run_indep_heteroscedastic_os,
    run_known_sigma_info_tracker,
    run_v34_tracker,
    solve_action_design_certified,
    solve_cubic_exact_2d,
    solve_profiled_loss_certified,
    solve_uncertified_local_null,
)

__all__ = [
    "ActiveDAGLUCBSession",
    "AdaptiveHardRegimeSession",
    "CertifiedDesignResult",
    "CertifiedProjectionResult",
    "ComponentPolyhedron",
    "CorrelationAwareCertSession",
    "CppV34BnBRunner",
    "FlatLUCBSession",
    "GPBoxCertSession",
    "GPEllipsoidCertSession",
    "GPGuidedRootCertSession",
    "HybridWitnessDAGLUCBSession",
    "InsideWitnessDAGLUCBSession",
    "IntrinsicGaussianTape",
    "LUCBMicroSession",
    "RegularizedInfoTrackerSession",
    "SmartHybridCertSession",
    "UGapEMCTSSession",
    "V34RunResult",
    "VarDEDAGSession",
    "batch_schedule_sizes",
    "build_screened_components",
    "compute_characteristic_rate",
    "compute_exact_nuisance_kl_rate",
    "eval_action_info_certified",
    "eval_profiled_loss",
    "fast_characteristic_rate",
    "is_four_power_refresh",
    "is_square_refresh",
    "largest_remainder_counts",
    "refresh_level",
    "run_indep_heteroscedastic_os",
    "run_known_sigma_info_tracker",
    "run_v34_tracker",
    "solve_action_design_certified",
    "solve_cubic_exact_2d",
    "solve_profiled_loss_certified",
    "solve_uncertified_local_null",
    "verify_characteristic_rate_independently",
]
