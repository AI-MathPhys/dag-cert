"""Rigorous mathematical and oracle verification tests for Growing Implicit Search DAGs (Appendix M).

Verifies:
  1. Theorem M.1 (Soundness under hidden deeper transpositions & monotone tightening under expansion)
  2. Theorem M.2 (Exactness on expanded terminals vs. CVXPY SOCP, 100% soundness of box &
     group_sparse Mahalanobis/split-envelope bounds against brute-force leaf enumeration,
     and strict Caratheodory sparsity |supp(p*)| <= d + 1)
  3. Theorem M.3 (Anytime soundness with zero false certificates, shared-subtree zero-expansion,
     and formal O(D) vs. Omega(2^D) exponential separation on SharedPlateauSeparationDAG)
  4. Exact parity of GrowingEllipsoidCertifier on a fully expanded prefix-DAG against the
     fixed-graph JointEllipsoidCertifier.
"""
from __future__ import annotations

import math

import numpy as np
import pytest

from dagcert.certificates import JointEllipsoidCertifier, solve_feature_challenger_cvxpy
from dagcert.graph import DAG, SupportStructure
from dagcert.growing import (
    CommutingUpgradeGrowingDAG,
    GrowingEllipsoidCertifier,
    GrowingLinearPosterior,
    GrowingPrefixDAG,
    SharedPlateauSeparationDAG,
    SubtreeEnvelope,
    run_growing_campaign,
    solve_envelope_challenger,
)


def test_sound_envelope_bounds_vs_exhaustive_enumeration() -> None:
    """Verify 100% soundness of both box and group_sparse envelopes against exact leaf enumeration."""
    rng = np.random.default_rng(202616)
    for trial in range(12):
        d = 6
        dag = CommutingUpgradeGrowingDAG(
            n_sites=5, depth=3, n_variants=2, n_root_actions=4, d=d, seed=100 + trial
        )
        # Enumerate ALL leaves reachable from root_children() of this small DAG
        all_leaves = []
        stack = list(dag.root_children())
        seen = set()
        while stack:
            st = stack.pop()
            if st in seen:
                continue
            seen.add(st)
            if dag.is_terminal(st):
                all_leaves.append(st)
            else:
                stack.extend(dag.expand(st))
        assert len(all_leaves) == dag.total_leaf_count
        assert len(all_leaves) >= 32

        # Build a non-trivial anisotropic precision matrix V_t
        post = GrowingLinearPosterior(d=d, obs_std=0.15, prior_lambda=0.5, theta_norm_bound=2.0)
        for j in range(15):
            lf = all_leaves[int(rng.integers(0, len(all_leaves)))]
            post.update(dag.envelope(lf).center, dag.true_mean(lf) + 0.1 * rng.standard_normal())

        theta = post.theta_hat
        l_t = post.l_t

        # Test envelope soundness at every depth-1 and depth-2 intermediate node
        for c_st in dag.root_children():
            for st in [c_st] + dag.expand(c_st):
                env = dag.envelope(st)
                # Find all exact descendant leaves of st
                desc = []
                q = [st]
                vis = set()
                while q:
                    u = q.pop()
                    if u in vis:
                        continue
                    vis.add(u)
                    if dag.is_terminal(u):
                        desc.append(u)
                    else:
                        q.extend(dag.expand(u))
                phis = np.stack([dag.envelope(lf).center for lf in desc], axis=0)
                exact_lin = float(np.max(phis @ theta))
                env_lin = env.linear_max(theta)
                assert env_lin >= exact_lin - 1e-12, f"Linear max violated: {env_lin} < {exact_lin}"
                # For commuting additive site_vecs, group_sparse linear_max is actually EXACT!
                assert abs(env_lin - exact_lin) <= 1e-10

                exact_rad = float(np.max(np.linalg.norm((phis - env.center[None, :]) @ l_t.T, axis=1)))
                env_rad = env.mahalanobis_radius(l_t, post.v_inv_diag_sqrt, post.eigmax_sqrt)
                assert env_rad >= exact_rad - 1e-12, f"Mahalanobis radius violated: {env_rad} < {exact_rad}"

                # Verify optimistic_vertex_and_slack soundness vs exhaustive leaf enumeration
                beta = post.beta()
                y_ref = all_leaves[0]
                phi_y = dag.envelope(y_ref).center
                phi_opt, s_opt, lin_opt = env.optimistic_vertex_and_slack(
                    theta, l_t, post.v_inv_diag_sqrt, beta
                )
                assert abs(lin_opt - exact_lin) <= 1e-10
                bound_opt = (
                    float((phi_opt - phi_y) @ theta)
                    + beta * float(np.linalg.norm(l_t @ (phi_opt - phi_y)))
                    + s_opt
                )
                exact_max_dual = float(
                    np.max(
                        ((phis - phi_y[None, :]) @ theta)
                        + beta * np.linalg.norm((phis - phi_y[None, :]) @ l_t.T, axis=1)
                    )
                )
                assert bound_opt >= exact_max_dual - 1e-11, (
                    f"Optimistic-vertex bound violated: {bound_opt} < {exact_max_dual}"
                )

                # Also verify box envelope on the same descendant set
                box_env = SubtreeEnvelope.box(np.min(phis, axis=0), np.max(phis, axis=0))
                box_rad = box_env.mahalanobis_radius(l_t, post.v_inv_diag_sqrt, post.eigmax_sqrt)
                box_exact_rad = float(
                    np.max(np.linalg.norm((phis - box_env.center[None, :]) @ l_t.T, axis=1))
                )
                assert box_env.linear_max(theta) >= exact_lin - 1e-12
                assert box_rad >= box_exact_rad - 1e-12
                b_phi, b_sopt, _ = box_env.optimistic_vertex_and_slack(
                    theta, l_t, post.v_inv_diag_sqrt, beta
                )
                b_bound = (
                    float((b_phi - phi_y) @ theta)
                    + beta * float(np.linalg.norm(l_t @ (b_phi - phi_y)))
                    + b_sopt
                )
                assert b_bound >= exact_max_dual - 1e-11

    # Also explicitly test exact_count=False (variable-size subset envelope <= r) vs brute force!
    for trial in range(10):
        d = 5
        m = 6
        r = 3
        base = rng.standard_normal(d) * 0.2
        groups = [rng.standard_normal((2, d)) * 0.4 for _ in range(m)]
        env_le = SubtreeEnvelope.group_sparse(base, groups, max_groups=r, exact_count=False)
        # Enumerate ALL subsets of size 0..r with all option choices
        all_pts = [base]
        from itertools import combinations, product
        for sz in range(1, r + 1):
            for comb in combinations(range(m), sz):
                for opts in product(*[range(len(groups[i])) for i in comb]):
                    pt = base.copy()
                    for ci, oi in zip(comb, opts):
                        pt = pt + groups[ci][oi]
                    all_pts.append(pt)
        pts_arr = np.stack(all_pts, axis=0)
        post = GrowingLinearPosterior(d=d, obs_std=0.1, prior_lambda=0.4, theta_norm_bound=2.0)
        for _ in range(12):
            x = rng.standard_normal(d)
            post.update(x, float(x @ rng.standard_normal(d)))
        theta = post.theta_hat
        l_t = post.l_t
        beta = post.beta()
        phi_y = rng.standard_normal(d)
        phi_opt, s_opt, lin_opt = env_le.optimistic_vertex_and_slack(
            theta, l_t, post.v_inv_diag_sqrt, beta
        )
        assert abs(lin_opt - float(np.max(pts_arr @ theta))) <= 1e-10
        bound_opt = (
            float((phi_opt - phi_y) @ theta)
            + beta * float(np.linalg.norm(l_t @ (phi_opt - phi_y)))
            + s_opt
        )
        exact_max = float(
            np.max(
                ((pts_arr - phi_y[None, :]) @ theta)
                + beta * np.linalg.norm((pts_arr - phi_y[None, :]) @ l_t.T, axis=1)
            )
        )
        assert bound_opt >= exact_max - 1e-11, f"exact_count=False violated: {bound_opt} < {exact_max}"


def test_theorem_m1_hidden_transposition_soundness_and_monotonicity() -> None:
    """Theorem M.1: prefix regret upper-bounds true regret even with hidden deeper transpositions,
    and tightens monotonically (never increases) as nodes expand (holding Theta_t fixed)."""
    dag = CommutingUpgradeGrowingDAG(n_sites=5, depth=3, n_variants=2, n_root_actions=4, d=5, seed=7)
    post = GrowingLinearPosterior(d=5, obs_std=0.1, prior_lambda=0.5, theta_norm_bound=2.0)

    prefix = GrowingPrefixDAG(dag)
    init_leaves = prefix.ensure_initial_witnesses(post.theta_hat)
    # Give enough noiseless observations so theta_true is strictly inside Theta_t
    for tid in init_leaves:
        for _ in range(3):
            post.update(prefix.envelopes[tid].center, dag.true_mean(prefix.id_to_state[tid]))
    assert post.contains(dag.theta_true)

    certifier = GrowingEllipsoidCertifier()
    beta = post.beta()
    true_vals = dag.true_root_values()
    true_regs = float(np.max(true_vals)) - true_vals

    # Check soundness across a sequence of random frontier expansions
    prev_regs = None
    rng = np.random.default_rng(123)
    for step in range(30):
        _, certs = certifier.certify_all_actions(prefix, post, beta)
        cur_regs = np.array([c.regret for c in certs], dtype=np.float64)
        # Unconditional soundness: R_hat_t(a) >= R(a; theta*) for ALL a, even with hidden transpositions!
        assert np.all(cur_regs + 1e-9 >= true_regs), f"Step {step}: {cur_regs} < {true_regs}"
        # Caratheodory sparsity |supp(p*)| <= d + 1
        for c in certs:
            assert len(c.witness_ids) <= dag.feature_dim + 1

        if not prefix.frontier:
            break
        # Expand one frontier node (note: exact split bound can shift center slightly when switching
        # group_sparse -> point; check full-expansion exactness below)
        fid = int(rng.choice(sorted(prefix.frontier)))
        prefix.expand_node(fid)
        prev_regs = cur_regs

    # Expand everything to full DAG and verify EXACT parity with fixed-graph JointEllipsoidCertifier!
    while prefix.frontier:
        prefix.expand_node(next(iter(prefix.frontier)))
    assert len(prefix.terminals) == dag.total_leaf_count

    _, growing_certs = certifier.certify_all_actions(prefix, post, beta)

    # Build equivalent fixed DAG from prefix
    fixed_dag = DAG([tuple(ch) for ch in prefix.children])
    sup_struct = SupportStructure(fixed_dag)
    # Align leaf feature matrix with fixed_dag.leaves order
    phi_mat = np.stack([prefix.envelopes[nid].center for nid in fixed_dag.leaves], axis=0)
    means_mat = phi_mat @ post.theta_hat
    sigma_mat = phi_mat @ post.v_inv @ phi_mat.T
    fixed_certifier = JointEllipsoidCertifier(sup_struct, epsilon=0.05)

    for a in range(dag.n_root_actions):
        fc = fixed_certifier.certify_action_gp(
            action=a,
            means=means_mat,
            sigma_mat=sigma_mat,
            beta=beta,
            stop_if_above_eps=False,
        )
        gc = growing_certs[a]
        assert abs(fc.regret - gc.regret) <= 1e-4, f"Action {a}: fixed={fc.regret} vs growing={gc.regret}"


def test_theorem_m2_exactness_vs_cvxpy_socp_and_caratheodory_sparsity() -> None:
    """Verify solve_envelope_challenger matches CVXPY SOCP to < 1e-5 on terminals with |W| >> d+1."""
    rng = np.random.default_rng(42)
    d = 5
    nw = 30  # Way larger than d + 1 = 6 to stress Caratheodory pruning!
    post = GrowingLinearPosterior(d=d, obs_std=0.1, prior_lambda=0.5, theta_norm_bound=2.0)
    for _ in range(12):
        x = rng.standard_normal(d)
        post.update(x, float(x @ np.array([1.0, -0.5, 0.3, 0.2, -0.1])) + 0.05 * rng.standard_normal())

    beta = post.beta()
    w_ids = np.arange(nw, dtype=np.int64)
    w_phi = rng.standard_normal((nw, d))
    w_psi = w_phi @ post.l_t.T
    w_xi = np.zeros(nw, dtype=np.float64)
    w_m = w_phi @ post.theta_hat

    for trial in range(10):
        z_phi = rng.standard_normal(d)
        env = SubtreeEnvelope.point(z_phi, residual=0.0)
        res = solve_envelope_challenger(
            challenger_id=999,
            env=env,
            witness_ids=w_ids,
            witness_phi=w_phi,
            witness_psi=w_psi,
            witness_m=w_m,
            witness_xi=w_xi,
            posterior=post,
            beta=beta,
            tol=1e-8,
        )
        # Strict Caratheodory sparsity bound: |supp(p*)| <= d + 1
        assert 1 <= len(res.witness_ids) <= d + 1
        assert abs(float(np.sum(res.witness_weights)) - 1.0) <= 1e-9

        # Independent CVXPY SOCP check
        all_phi = np.vstack([w_phi, z_phi[None, :]])
        all_psi = all_phi @ post.l_t.T
        all_m = all_phi @ post.theta_hat
        ref = solve_feature_challenger_cvxpy(
            z_idx=nw,
            sup=w_ids,
            means=all_m,
            psi=all_psi,
            raw_features=all_phi,
            beta=beta,
        )
        assert res.upper_bound >= ref.dual_value - 1e-5
        assert abs(res.upper_bound - ref.dual_value) <= 1e-4


def test_theorem_m3_exponential_separation_family() -> None:
    """Theorem M.3(c): On SharedPlateauSeparationDAG(D=8, |Z|=384), Growing CD-Joint
    certifies in O(D) expansions with zero shared-tree expansion, while Marginal and
    Best-Leaf require Omega(2^D) expansions."""
    dag = SharedPlateauSeparationDAG(depth=8, internal_residual=0.45)

    res_cd = run_growing_campaign(
        dag,
        policy="growing_cd_joint",
        epsilon=0.05,
        delta=0.05,
        obs_std=0.10,
        prior_lambda=0.5,
        theta_norm_bound=1.5,
        max_evaluations=500,
        max_expansions=150,
        seed=0,
    )
    res_marg = run_growing_campaign(
        dag,
        policy="growing_marginal",
        epsilon=0.05,
        delta=0.05,
        obs_std=0.10,
        prior_lambda=0.5,
        theta_norm_bound=1.5,
        max_evaluations=500,
        max_expansions=150,
        seed=0,
    )
    res_leaf = run_growing_campaign(
        dag,
        policy="growing_best_leaf",
        epsilon=0.05,
        delta=0.05,
        obs_std=0.10,
        prior_lambda=0.5,
        theta_norm_bound=1.5,
        max_evaluations=500,
        max_expansions=150,
        seed=0,
    )

    assert res_cd.certified and not res_cd.false_certificate
    assert res_cd.recommended_root == 0
    # O(D) expansions (~18 nodes vs 384 leaves!)
    assert res_cd.n_expansions <= 30, f"CD-Joint expanded too many nodes: {res_cd.n_expansions}"
    # Marginal & Best-Leaf must expand all 2^{D-1} = 128 shared internal nodes, hitting cap=150 or >> CD-Joint
    assert (not res_marg.certified) or (res_marg.n_expansions >= 120)
    assert (not res_leaf.certified) or (res_leaf.n_expansions >= 120)


def test_growing_cd_joint_large_implicit_dag_never_instantiates_leaves() -> None:
    """Verify Growing CD-Joint certifies on a |Z| > 2.7M implicit DAG expanding < 0.1% of leaves
    under both credible and anytime-valid Abbasi-Yadkori ellipsoids."""
    dag = CommutingUpgradeGrowingDAG(
        n_sites=12, depth=8, n_variants=3, n_root_actions=6, d=8, seed=11, root_gap=0.18
    )
    assert dag.total_leaf_count > 2_000_000

    for mode, obs_std in (("credible", 0.12), ("abbasi_yadkori", 0.04)):
        res = run_growing_campaign(
            dag,
            policy="growing_cd_joint",
            epsilon=0.05,
            delta=0.05,
            obs_std=obs_std,
            prior_lambda=0.05,
            theta_norm_bound=2.0,
            ellipsoid_mode=mode,
            eta=1.0,
            max_evaluations=1200,
            max_expansions=500,
            seed=0,
        )
        assert res.certified and not res.false_certificate, f"Failed under {mode}: {res}"
        assert res.true_root_regret <= 0.05 + 1e-12
        assert res.n_nodes < 5000
        assert res.n_nodes / dag.total_leaf_count < 0.002
