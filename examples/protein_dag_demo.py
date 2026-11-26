"""Protein engineering example: certifying an initial GB1 mutation on a canonical 3-edit DAG."""
from __future__ import annotations

from joint_root_cert import SupportStructure, certify_root_action
from joint_root_cert.benchmarks import (
    GB1MutationCampaignProblem,
    protein_sequence_kernel,
)


def main() -> None:
    prob = GB1MutationCampaignProblem(start_seq="ADGV", max_edits=3, panel="panel5", noise_model="calibrated")
    ss = SupportStructure(prob.graph)
    seqs = [prob.variant_of_leaf[z] for z in ss.leaves]
    kernel = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
    oracle = prob.oracle(seed=801001)

    res = certify_root_action(
        dag=prob.graph,
        observe_fn=lambda idx: float(oracle.sample(ss.leaves[idx])),
        kernel=kernel,
        prior_mean=0.28,
        obs_std=0.16,
        policy="cd_joint",
        stopping="direct_posterior_risk",
        epsilon=0.015,
        delta=0.05,
        max_evals=1000,
        mc_draws=2048,
        seed=801001,
    )
    true_regrets = prob.graph.optimal_values(prob.means)
    opt_val = float(true_regrets[prob.graph.root])
    chosen_node = prob.graph.children[prob.graph.root][res.action]
    reg = max(0.0, opt_val - float(true_regrets[chosen_node]))
    print(
        f"GB1 ADGV (M={ss.m} variants, K={ss.k} first mutations): "
        f"certified={res.certified} in {res.steps} assays | "
        f"action={res.action} ({prob.graph.labels[chosen_node]}) | true_regret={reg:.5f}"
    )


if __name__ == "__main__":
    main()
