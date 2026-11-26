"""Real epistatic combinatorial protein-fitness benchmarks (GB1 and TmTrpB)."""
from __future__ import annotations

from dagcert._core.v6_bayesian_opt import (
    alt_protein_sequence_kernel,
    protein_sequence_kernel,
)
from dagcert._core.v6_real_world import (
    GB1_NPZ_PATH,
    GB1_PANELS,
    TRPB_NPZ_PATH,
    TRPB_PANELS,
    GB1MutationCampaignProblem,
    TrpBMutationCampaignProblem,
    gb1_mean_to_raw_fitness,
    real_world_problem_diagnostics,
)
from dagcert._core.v8_unified_experiments import build_protein_eigenfeatures

GB1_TEMPLATES: tuple[str, ...] = (
    "VDGV",  # Wild-type GB1 (epistatic ridge)
    "FDGV",  # V39F
    "LDGV",  # V39L
    "WDGV",  # V39W
    "YDGV",  # V39Y
    "IDGV",  # V39I (epistatic ridge)
    "ADGV",  # V39A (epistatic ridge)
    "VDGA",  # V54A
    "VWGV",  # D40W
    "LWGV",  # V39L+D40W (epistatic ridge)
)


def _build_trpb_templates() -> tuple[str, ...]:
    parent = "VFVS"
    panel = TRPB_PANELS["panel5"]
    out = [parent]
    for pos in range(4):
        for aa in panel:
            if aa != parent[pos]:
                chars = list(parent)
                chars[pos] = aa
                out.append("".join(chars))
    return tuple(out)


TRPB_TEMPLATES: tuple[str, ...] = _build_trpb_templates()

__all__ = [
    "GB1MutationCampaignProblem",
    "GB1_NPZ_PATH",
    "GB1_PANELS",
    "GB1_TEMPLATES",
    "TRPB_NPZ_PATH",
    "TRPB_PANELS",
    "TRPB_TEMPLATES",
    "TrpBMutationCampaignProblem",
    "alt_protein_sequence_kernel",
    "build_protein_eigenfeatures",
    "gb1_mean_to_raw_fitness",
    "protein_sequence_kernel",
    "real_world_problem_diagnostics",
]
