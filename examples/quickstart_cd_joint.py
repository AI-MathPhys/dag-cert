"""Quickstart example: Joint Root Certification with the `dagcert` Python library.

Demonstrates:
  1. Exact shared-support cancellation (Figure 1b of the paper).
  2. Certifying an epsilon-optimal root action on an overlapping correlated DAG using
     CD-Joint, Correlated KG, Correlated GP-OS, and Distribution-Free Optimistic Separation.
"""
from __future__ import annotations

import numpy as np

from dagcert import SearchDAG, certify_root_action, exact_rectangular_regret


def main() -> None:
    # 1. Exact shared-support cancellation (Figure 1b)
    # Action 0 reaches {z1, z_AB}; Action 1 reaches {z_AB, z2}.
    best_a, min_reg, regrets = exact_rectangular_regret(
        supports=[[0, 1], [1, 2]],
        lower=[0.72, 0.40, 0.30],
        upper=[0.80, 0.95, 0.55],
    )
    print(f"Figure 1b exact outside-support regret: best_action={best_a}, regrets={regrets.tolist()}")

    # 2. Correlated overlapping search DAG (4 root actions, 8 canonical terminals)
    dag = SearchDAG.from_supports(
        supports=[
            [0, 1, 2, 3],
            [1, 2, 4, 5],
            [2, 3, 5, 6],
            [3, 4, 6, 7],
        ],
        action_labels=["commit_A", "commit_B", "commit_C", "commit_D"],
    )
    true_means = np.array([0.84, 0.68, 0.64, 0.60, 0.56, 0.52, 0.48, 0.44])
    idx = np.arange(8, dtype=float)
    kernel = 0.04 * np.exp(-np.abs(idx[:, None] - idx[None, :]) / 2.5) + 0.005 * np.eye(8)

    print("\nMatched-model certification under 95% joint contrast credible ellipsoid:")
    for policy in ("cd_joint", "gp_os", "kg"):
        rng = np.random.default_rng(2026)
        res = certify_root_action(
            dag=dag,
            observe_fn=lambda z, r=rng: float(true_means[z] + 0.08 * r.standard_normal()),
            kernel=kernel,
            prior_mean=0.55,
            obs_std=0.08,
            policy=policy,
            stopping="credible_ellipsoid",
            epsilon=0.03,
            delta=0.05,
            max_evals=2000,
        )
        print(
            f"  {policy:10s} | certified={res.certified} | action={res.action} | "
            f"evals={res.steps:4d} | reg_bound={res.regret_bound:.4f} (rank={res.contrast_rank})"
        )

    # 3. Formal distribution-free [0, 1]-bounded certification (no GP assumptions)
    rng = np.random.default_rng(2026)
    res_df = certify_root_action(
        dag=dag,
        observe_fn=lambda z: float(np.clip(true_means[z] + 0.12 * rng.uniform(-1, 1), 0.0, 1.0)),
        stopping="distribution_free",
        epsilon=0.03,
        delta=0.05,
        max_evals=5000,
    )
    print(
        f"\nDistribution-free (Emp. Bernstein): certified={res_df.certified} | "
        f"action={res_df.action} | evals={res_df.steps} | reg_bound={res_df.regret_bound:.4f}"
    )


if __name__ == "__main__":
    main()
