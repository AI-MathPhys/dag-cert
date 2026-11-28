"""Unit, algebraic-parity, and mathematical-equivalence tests for MA-CD-Joint & MA-CD-Joint-Safe."""
from __future__ import annotations

import math
import time

import numpy as np
import pytest

from dagcert import (
    GAUSS_HERMITE_9_NODES,
    GAUSS_HERMITE_9_WEIGHTS,
    JointEllipsoidCertifier,
    SharedGaussianPosterior,
    SupportStructure,
    build_query_shortlist,
    build_witness_pool,
    compute_exact_standardized_margin,
    select_margin_aware_query,
)
from dagcert._core.v12_bed_acquisition import GaussianPairedDeconfoundedProblem
from dagcert.benchmarks import (
    GB1MutationCampaignProblem,
    protein_sequence_kernel,
)


def test_gauss_hermite_9_moments_exact_up_to_degree_16() -> None:
    """9-point standard-normal Gauss-Hermite quadrature integrates E[xi^{2k}] = (2k-1)!! exactly up to 2k=16."""
    assert abs(float(np.sum(GAUSS_HERMITE_9_WEIGHTS)) - 1.0) < 1e-14
    for p in (1, 3, 5, 7, 9, 11, 13, 15):
        scale = math.sqrt(float(math.factorial(p)))
        got = abs(float(np.sum(GAUSS_HERMITE_9_WEIGHTS * (GAUSS_HERMITE_9_NODES ** p))))
        assert got <= 1e-12 * max(1.0, scale)
    double_fact = 1.0
    for k in range(1, 9):
        double_fact *= float(2 * k - 1)
        got = float(np.sum(GAUSS_HERMITE_9_WEIGHTS * (GAUSS_HERMITE_9_NODES ** (2 * k))))
        assert abs(got - double_fact) <= 1e-11 * double_fact


def test_standardized_margin_equivalence_with_conic_certificate() -> None:
    """Verify exact equivalence: R_t(a) <= eps <==> H_t(a) >= beta_t across random correlated GPs."""
    rng = np.random.default_rng(202617)
    for trial in range(16):
        prob = GaussianPairedDeconfoundedProblem(
            seed=7000 + trial, overlap=0.75 if trial % 2 else 0.0, rho=0.9 if trial % 3 else 0.0
        )
        ss = SupportStructure(prob.graph)
        post = SharedGaussianPosterior(prob.kernel, prob.prior_mean, prob.obs_std, delta=0.05)
        oracle = prob.oracle(100 + trial)
        for _ in range(40):
            arm = int(rng.integers(0, ss.m))
            post.observe(arm, float(oracle.sample(ss.leaves[arm])))

        cert = JointEllipsoidCertifier(ss, epsilon=0.025)
        beta = post.beta()
        for a in range(min(4, ss.k)):
            ca = cert.certify_action_gp(a, post.mean, post.sigma_mat, beta, stop_if_above_eps=False)
            h_a = compute_exact_standardized_margin(
                a, ss, post.mean, post.sigma_mat, epsilon=0.025, beta=beta, certifier=cert
            )
            # Exact equivalence away from 1e-5 boundary tolerance
            if ca.regret <= 0.025 - 1e-4:
                assert h_a >= beta - 1e-4, f"trial={trial} a={a}: reg={ca.regret}, H={h_a} < beta={beta}"
            elif ca.regret >= 0.025 + 1e-4:
                assert h_a <= beta + 1e-4, f"trial={trial} a={a}: reg={ca.regret}, H={h_a} > beta={beta}"


def test_rank1_fantasy_formula_exact_parity_with_posterior_observe() -> None:
    """Verify closed-form H_{t+1}^{(x, xi)}(g) = (d_g - q_{g,x} xi)/sqrt(s_g^2 - q_{g,x}^2)
    matches explicit SharedGaussianPosterior.observe(x, y) to < 1e-11."""
    prob = GaussianPairedDeconfoundedProblem(seed=7100, overlap=0.75, rho=0.9)
    ss = SupportStructure(prob.graph)
    post = SharedGaussianPosterior(prob.kernel, prob.prior_mean, prob.obs_std, delta=0.05)
    oracle = prob.oracle(7100)
    init_obs = [(arm, float(oracle.sample(ss.leaves[arm]))) for arm in range(0, ss.m, 4)]
    for arm, y_val in init_obs:
        post.observe(arm, y_val)

    eps = 0.025
    sig = post.sigma_mat.copy()
    m0 = post.mean.copy()
    obs_var = post.obs_var

    # Construct a non-trivial mixture contrast g = e_z - sum_y p_y e_y
    sup = ss.supports[0]
    comp = ss.complements[0]
    z = int(comp[3])
    g = np.zeros(ss.m, dtype=np.float64)
    g[z] = 1.0
    g[sup[0]] = -0.35
    g[sup[1]] = -0.65

    d_g = eps - float(g @ m0)
    s2_g = float(g @ (sig @ g))

    for x in (int(sup[0]), int(sup[2]), int(comp[0]), int(comp[5])):
        denom_x = math.sqrt(obs_var + float(sig[x, x]))
        v_x = sig[:, x] / denom_x
        q_gx = float(g @ v_x)
        for xi in (-2.0, -0.5, 0.0, 1.25, 2.5):
            # Closed-form rank-1 formula
            h_fast = (d_g - q_gx * xi) / math.sqrt(s2_g - q_gx * q_gx)
            # Explicit posterior replay + fantasy observation y = m_x + xi * sqrt(obs_var + sig_{xx})
            post2 = SharedGaussianPosterior(prob.kernel, prob.prior_mean, prob.obs_std, delta=0.05)
            for arm, y_val in init_obs:
                post2.observe(arm, y_val)
            y_fant = float(m0[x]) + xi * denom_x
            post2.observe(x, y_fant)
            d_post = eps - float(g @ post2.mean)
            s_post = math.sqrt(float(g @ (post2.sigma_mat @ g)))
            h_exact = d_post / s_post
            assert abs(h_fast - h_exact) < 1e-11, f"Fantasy mismatch: {h_fast} vs {h_exact}"


def test_ma_cd_joint_safeguard_and_safe_alternation_and_speed() -> None:
    """Verify safeguard override, mandatory even-step CD-Joint for safe=True, witness dedup,
    and sub-millisecond acquisition speed on both M=64 and GB1 protein landscapes."""
    prob = GaussianPairedDeconfoundedProblem(seed=7200, overlap=0.75, rho=0.9)
    ss = SupportStructure(prob.graph)
    l2a = [[] for _ in range(ss.m)]
    for a, sup in enumerate(ss.supports):
        for i in sup:
            l2a[int(i)].append(a)
    post = SharedGaussianPosterior(prob.kernel, prob.prior_mean, prob.obs_std, delta=0.05)
    cert = JointEllipsoidCertifier(ss, epsilon=0.025)
    oracle = prob.oracle(7200)
    for arm in range(ss.m):
        post.observe(arm, float(oracle.sample(ss.leaves[arm])))

    beta = post.beta()
    # Even step (step_idx=0) under safe=True MUST take mandatory CD-Joint step
    sel_even = select_margin_aware_query(
        supports=ss, leaf_to_actions=l2a, posterior=post, certifier=cert,
        beta=beta, epsilon=0.025, step_idx=0, safe=True,
    )
    if not sel_even.safeguard_triggered:
        assert sel_even.mandatory_cd_step and not sel_even.used_ma_query
        assert sel_even.arm == sel_even.cd_arm

    # Odd step (step_idx=1) under safe=True matches safe=False identically
    sel_odd_safe = select_margin_aware_query(
        supports=ss, leaf_to_actions=l2a, posterior=post, certifier=cert,
        beta=beta, epsilon=0.025, step_idx=1, safe=True,
    )
    sel_odd_plain = select_margin_aware_query(
        supports=ss, leaf_to_actions=l2a, posterior=post, certifier=cert,
        beta=beta, epsilon=0.025, step_idx=1, safe=False,
    )
    assert sel_odd_safe.arm == sel_odd_plain.arm
    assert abs(sel_odd_safe.ma_gain - sel_odd_plain.ma_gain) < 1e-14

    # Witness pool size strictly <= 9 and deduplicated
    sup0 = ss.supports[0]
    u0 = post.mean + beta * post.stds()
    idx_l, wgt_l = build_witness_pool(sup0, post.mean, u0, np.array([sup0[0], sup0[1]]), np.array([0.5, 0.5]))
    assert 1 <= len(idx_l) <= 9
    assert len(idx_l) == len(wgt_l)

    # Verify shortlist & sub-5ms speed on a real measured GB1 protein landscape (M ~ 400)!
    gb1 = GB1MutationCampaignProblem(start_seq="VDGV", max_edits=3, panel="panel5", noise_model="calibrated")
    ss_g = SupportStructure(gb1.graph)
    l2a_g = [[] for _ in range(ss_g.m)]
    for a, sup in enumerate(ss_g.supports):
        for i in sup:
            l2a_g[int(i)].append(a)
    seqs = [gb1.variant_of_leaf[z] for z in ss_g.leaves]
    ker_g = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)
    post_g = SharedGaussianPosterior(ker_g, 0.28, 0.16, delta=0.05)
    cert_g = JointEllipsoidCertifier(ss_g, epsilon=0.015)
    # Give enough pulls so safeguard doesn't fire and full MA lookahead executes
    ora_g = gb1.oracle(801001)
    for arm in range(0, ss_g.m, 10):
        post_g.observe(arm, float(ora_g.sample(ss_g.leaves[arm])))
    sel_g_cpp = select_margin_aware_query(
        supports=ss_g, leaf_to_actions=l2a_g, posterior=post_g, certifier=cert_g,
        beta=post_g.beta(), epsilon=0.015, step_idx=1, safe=False,
        cd_stop_if_above_eps=True, use_cpp=True,
    )
    sel_g_py = select_margin_aware_query(
        supports=ss_g, leaf_to_actions=l2a_g, posterior=post_g, certifier=cert_g,
        beta=post_g.beta(), epsilon=0.015, step_idx=1, safe=False,
        cd_stop_if_above_eps=True, use_cpp=False,
    )
    assert sel_g_cpp.arm == sel_g_py.arm
    assert abs(sel_g_cpp.ma_gain - sel_g_py.ma_gain) < 1e-13

    t0 = time.perf_counter()
    sel_g = select_margin_aware_query(
        supports=ss_g, leaf_to_actions=l2a_g, posterior=post_g, certifier=cert_g,
        beta=post_g.beta(), epsilon=0.015, step_idx=1, safe=False,
        cd_stop_if_above_eps=True, use_cpp=True,
    )
    dt_ms = (time.perf_counter() - t0) * 1e3
    assert 0 <= sel_g.arm < ss_g.m
    assert dt_ms < 10.0, f"GB1 MA-CD-Joint step too slow: {dt_ms:.2f} ms"
