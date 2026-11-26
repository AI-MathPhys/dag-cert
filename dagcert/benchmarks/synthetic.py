"""Synthetic search-DAG, overlap/correlation, proxy, heteroscedastic, SameGame, and routing benchmarks."""
from __future__ import annotations

from dagcert._core.v2_benchmarks import (
    contiguous_window_dag,
    load_standard_samegame_boards,
    overlap_dag,
    puct_noisy_funnel,
    puct_root_funnel,
    samegame_depth_case,
    samegame_standard_endgame,
    structural_diagnostics,
)
from dagcert._core.v4_baselines import (
    BoundedNoiseProblem,
    FastSameGameProblem,
    samegame_midgame_case,
    stochastic_routing_dag,
)
from dagcert._core.v5_hybrid_and_os import noncontainment_star_dag
from dagcert._core.v6_bayesian_opt import (
    CorrelatedSupportDAGProblem,
    ar1_corr_matrix,
    build_structured_corr_kernel,
)
from dagcert._core.v7_benchmarks import (
    GaussianPriorDAGProblem,
    HullDominanceDAGProblem,
    MisspecifiedLinearDAGProblem,
    MotivationalProxyDAGProblem,
    MultiAnswerCommitmentDAGProblem,
    OffWitnessProxyDAGProblem,
    OverlapCorrelationDAGProblem,
    ScalingDAGProblem,
)
from dagcert._core.v8_unified_experiments import DeconfoundedOverlapCorrelationProblem
from dagcert._core.v9_v34_tracker import (
    HeteroscedasticDAGProblem,
    make_behrens_fisher_null_dag,
    make_general_d_dag,
    make_heteroscedastic_proxy_dag,
    make_rank2_multi_action_dag,
    make_switching_multi_answer_dag,
)
from dagcert._core.v12_bed_acquisition import (
    FixedFeatureGaussianOverlapProblem,
    GaussianPairedDeconfoundedProblem,
    SmallOverlapCorrelationProblem,
)

__all__ = [
    "BoundedNoiseProblem",
    "CorrelatedSupportDAGProblem",
    "DeconfoundedOverlapCorrelationProblem",
    "FastSameGameProblem",
    "FixedFeatureGaussianOverlapProblem",
    "GaussianPairedDeconfoundedProblem",
    "GaussianPriorDAGProblem",
    "HeteroscedasticDAGProblem",
    "HullDominanceDAGProblem",
    "MisspecifiedLinearDAGProblem",
    "MotivationalProxyDAGProblem",
    "MultiAnswerCommitmentDAGProblem",
    "OffWitnessProxyDAGProblem",
    "OverlapCorrelationDAGProblem",
    "ScalingDAGProblem",
    "SmallOverlapCorrelationProblem",
    "ar1_corr_matrix",
    "build_structured_corr_kernel",
    "contiguous_window_dag",
    "load_standard_samegame_boards",
    "make_behrens_fisher_null_dag",
    "make_general_d_dag",
    "make_heteroscedastic_proxy_dag",
    "make_rank2_multi_action_dag",
    "make_switching_multi_answer_dag",
    "noncontainment_star_dag",
    "overlap_dag",
    "puct_noisy_funnel",
    "puct_root_funnel",
    "samegame_depth_case",
    "samegame_midgame_case",
    "samegame_standard_endgame",
    "stochastic_routing_dag",
    "structural_diagnostics",
]
