"""Correlated proxy example: CD-Joint queries a low-valued proxy terminal to certify the root."""
from __future__ import annotations

import numpy as np

from joint_root_cert import certify_root_action
from joint_root_cert.benchmarks import MotivationalProxyDAGProblem


def main() -> None:
    prob = MotivationalProxyDAGProblem()
    ss_leaves = prob.graph.leaves
    oracle = prob.oracle(seed=42)
    kernel = prob.phi @ prob.phi.T + 1e-6 * np.eye(len(ss_leaves))
    res = certify_root_action(
        dag=prob.graph,
        observe_fn=lambda idx: float(oracle.sample(ss_leaves[idx])),
        kernel=kernel,
        prior_mean=0.5,
        obs_std=prob.obs_std,
        policy="cd_joint",
        stopping="credible_ellipsoid",
        epsilon=0.02,
        delta=0.05,
        max_evals=2000,
    )
    proxy_frac = float(res.arm_counts[-1]) / max(1, res.steps)
    print(
        f"CD-Joint certified action={res.action} in {res.steps} evals "
        f"(low-valued proxy query share: {100 * proxy_frac:.1f}%, arm counts={res.arm_counts.tolist()})"
    )


if __name__ == "__main__":
    main()
