"""Experiment E0 (Numerical Oracle Audit) & Motivational Proxy Toy Benchmark.

1. Part A (E0 — Exact Correlated Certificate Audit):
   Generates 200 random synthetic ellipsoids and overlapping-support DAGs across
   M in {4, 6, 8, 12}, d in {2, 3, 5}, plus edge cases (empty complement S(a) = Z
   and exact convex-hull containment P_Z subseteq P_a). Verifies:
   - Exact agreement between reference CVXPY SOCP, Caratheodory Column Generation,
     Dense Away-Step Frank-Wolfe, and independent Primal Ellipsoid Maximization
     (with dense parameter-space grid check for d in {2, 3}).
   - Zero ordering violations: R_ellipsoid <= R_vertex <= R_enclosing_box.
   - 100% Caratheodory sparsity compliance: |supp(p*)| <= d + 1.

2. Part B (Motivational Proxy Toy — "The First Experiment"):
   Evaluates `MotivationalProxyDAGProblem` across 50 seeds comparing:
   - `exact_dag_lucb` (independent box, UCB witness)
   - `opt_sep` (independent box, optimistic separation)
   - `enclosing_box_cd` (enclosing box B(Theta_t) + contrast acquisition)
   - `gp_ucb_joint` (joint ellipsoid + conventional UCB acquisition)
   - `direct_witness_joint` (joint ellipsoid + witness-only restriction)
   - `contrast_directed_joint` (joint ellipsoid + safeguarded contrast-directed)
   - `bayes_ids_joint` (joint ellipsoid + posterior acceptable-set MI)
   - `maxmin_tracking_joint` (joint ellipsoid + T5 plug-in saddle-point tracker)
   Also exports a detailed step-by-step single-seed trajectory comparing enclosing-box
   width, joint ellipsoidal regret, contrast variance, and terminal pulls for Figure 1.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from concurrent.futures import ProcessPoolExecutor
import csv
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import platform
import statistics
import time

import numpy as np

from joint_root_cert import DAG
from joint_root_cert import HybridWitnessDAGLUCBSession
from joint_root_cert._core.v7_bayesian_ucd import (
    CorrelationAwareCertSession,
    JointEllipsoidCertifier,
    LinearFeatureModel,
    SupportStructure,
    compute_characteristic_rate,
    solve_primal_ellipsoid_regret,
)
from joint_root_cert.benchmarks import MotivationalProxyDAGProblem


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/e0_and_toy"

TOY_METHODS = (
    "exact_dag_lucb",
    "opt_sep",
    "enclosing_box_cd",
    "gp_ucb_joint",
    "direct_witness_joint",
    "contrast_directed_joint",
    "bayes_ids_joint",
    "maxmin_tracking_joint",
)
TOY_EPS = 0.015
TOY_CAP = 4000
DELTA = 0.05


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _e0_worker(task: tuple[int, int, int, str]) -> dict:
    trial_id, m_leaves, d_feat, case_type = task
    rng = np.random.default_rng(2026000 + trial_id * 7919)

    if case_type == "empty_complement":
        k_act = 2
        leaf_off = 1 + k_act
        children = [
            (1, 2),
            tuple(range(leaf_off, leaf_off + m_leaves)),
            tuple(range(leaf_off, leaf_off + max(2, m_leaves // 2))),
            *([()] * m_leaves),
        ]
    else:
        k_act = 3
        leaf_off = 1 + k_act
        sup_sz = max(d_feat + 1, (m_leaves * 2) // 3)
        sup_sz = min(m_leaves - 1, sup_sz)
        s0 = sorted(int(x) for x in rng.choice(m_leaves, size=sup_sz, replace=False))
        s1 = sorted(int(x) for x in rng.choice(m_leaves, size=sup_sz, replace=False))
        all_cov = set(s0) | set(s1)
        rem = [i for i in range(m_leaves) if i not in all_cov]
        s2 = sorted(set(rem) | set(int(x) for x in rng.choice(m_leaves, size=max(2, sup_sz // 2), replace=False)))
        children = [
            (1, 2, 3),
            tuple(leaf_off + i for i in s0),
            tuple(leaf_off + i for i in s1),
            tuple(leaf_off + i for i in s2),
            *([()] * m_leaves),
        ]

    graph = DAG(children, root=0)
    sup_struct = SupportStructure(graph)

    if case_type == "hull_contained":
        sup0 = sup_struct.supports[0]
        comp0 = sup_struct.complements[0]
        phi = np.zeros((m_leaves, d_feat), dtype=np.float64)
        phi[sup0] = rng.standard_normal((len(sup0), d_feat))
        for z in comp0:
            w = rng.dirichlet(np.ones(len(sup0)))
            phi[int(z)] = w @ phi[sup0]
    else:
        phi = rng.standard_normal((m_leaves, d_feat))

    a_mat = rng.standard_normal((d_feat, d_feat))
    v_mat = 0.25 * np.eye(d_feat) + a_mat.T @ a_mat
    v_inv = np.linalg.inv(v_mat)
    l_inv = np.linalg.cholesky(v_inv)
    psi = phi @ l_inv
    theta_hat = 0.35 * rng.standard_normal(d_feat)
    means = phi @ theta_hat
    beta = float(rng.uniform(0.4, 2.2))
    stds = np.linalg.norm(psi, axis=1)

    cert_socp = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="cvxpy_socp")
    cert_cg = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="colgen_full")
    cert_lazy = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="colgen_lazy")
    cert_afw = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="dense_afw")
    cert_vt = JointEllipsoidCertifier(sup_struct, epsilon=0.02, solver="vertex_approx")

    a_target = 0
    r_socp = cert_socp.certify_action(a_target, means, psi, phi, beta)
    r_cg = cert_cg.certify_action(a_target, means, psi, phi, beta)
    r_lazy = cert_lazy.certify_action(a_target, means, psi, phi, beta)
    r_afw = cert_afw.certify_action(a_target, means, psi, phi, beta)
    r_vt = cert_vt.certify_action(a_target, means, psi, phi, beta)

    grid_n = 25 if d_feat <= 3 else 0
    r_prim = solve_primal_ellipsoid_regret(
        a_target, sup_struct, phi, theta_hat, v_mat, beta, dense_grid_per_axis=grid_n, seed=trial_id
    )

    sup0 = sup_struct.supports[a_target]
    comp0 = sup_struct.complements[a_target]
    r_box = (
        0.0
        if len(comp0) == 0
        else max(0.0, float(np.max((means + beta * stds)[comp0]) - np.max((means - beta * stds)[sup0])))
    )

    err_cg = abs(r_cg.regret - r_socp.regret)
    err_lazy = abs(r_lazy.regret - r_socp.regret)
    err_afw = abs(r_afw.regret - r_socp.regret)
    err_prim = abs(r_prim - r_socp.regret)

    order_ok = (r_socp.regret <= r_vt.regret + 1e-6) and (r_vt.regret <= r_box + 1e-6)
    cara_ok = len(r_cg.inside_indices) <= d_feat + 1

    return {
        "trial_id": trial_id,
        "case_type": case_type,
        "m": m_leaves,
        "d": d_feat,
        "regret_socp": round(r_socp.regret, 9),
        "regret_colgen": round(r_cg.regret, 9),
        "regret_lazy": round(r_lazy.regret, 9),
        "regret_afw": round(r_afw.regret, 9),
        "regret_primal": round(r_prim, 9),
        "regret_vertex": round(r_vt.regret, 9),
        "regret_box": round(r_box, 9),
        "err_colgen_vs_socp": err_cg,
        "err_lazy_vs_socp": err_lazy,
        "err_afw_vs_socp": err_afw,
        "err_primal_vs_socp": err_prim,
        "box_over_ellipsoid_ratio": round(r_box / max(1e-6, r_socp.regret), 4) if r_socp.regret > 1e-6 else 1.0,
        "active_support_size": len(r_cg.inside_indices),
        "caratheodory_ok": cara_ok,
        "ordering_ok": order_ok,
        "max_duality_gap": r_cg.max_duality_gap,
    }


def _toy_worker(task: tuple[int, int]) -> list[dict]:
    seed, cap = task
    prob = MotivationalProxyDAGProblem(hw=0.18)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    rows: list[dict] = []
    for method in TOY_METHODS:
        t0 = time.perf_counter()
        if method == "exact_dag_lucb":
            sess = HybridWitnessDAGLUCBSession(prob, seed, TOY_EPS, mode="ucb", delta=DELTA, schedule="emp_bernstein")
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                sess.step()
            arm_counts = [sess.oracle.obs[lf] for lf in prob.graph.leaves]
            off_w = 0
        elif method == "opt_sep":
            sess = HybridWitnessDAGLUCBSession(
                prob, seed, TOY_EPS, mode="opt_sep", delta=DELTA, schedule="emp_bernstein"
            )
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                sess.step()
            arm_counts = [sess.oracle.obs[lf] for lf in prob.graph.leaves]
            off_w = 0
        else:
            model = LinearFeatureModel(
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                reg_lambda=0.02,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                beta_mode="abbasi_yadkori",
                delta=DELTA,
            )
            if method == "enclosing_box_cd":
                cert_m, acq_m = "enclosing_box", "contrast_directed"
            elif method == "gp_ucb_joint":
                cert_m, acq_m = "joint_ellipsoid", "gp_ucb"
            elif method == "direct_witness_joint":
                cert_m, acq_m = "joint_ellipsoid", "direct_witness"
            elif method == "contrast_directed_joint":
                cert_m, acq_m = "joint_ellipsoid", "contrast_directed"
            elif method == "bayes_ids_joint":
                cert_m, acq_m = "joint_ellipsoid", "bayes_ids"
            elif method == "maxmin_tracking_joint":
                cert_m, acq_m = "joint_ellipsoid", "maxmin_tracking"
            else:
                raise ValueError(method)

            sess = CorrelationAwareCertSession(
                prob, seed=seed, epsilon=TOY_EPS, model=model, cert_mode=cert_m, acquisition=acq_m, delta=DELTA
            )
            while not sess.certified and not sess.conflict and sess.calls < cap:
                sess.step()
            arm_counts = [int(x) for x in model.arm_counts.tolist()]
            off_w = int(sess.off_witness_pulls)

        elapsed_s = time.perf_counter() - t0
        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        true_reg = regrets[act]
        false_cert = bool(cert and true_reg > TOY_EPS + 1e-12)
        assert not false_cert, f"False cert on toy {method} seed={seed}: {true_reg} > {TOY_EPS}"

        proxy_pulls = int(arm_counts[4])
        rows.append(
            {
                "seed": seed,
                "method": method,
                "certified": cert,
                "false_certificate": false_cert,
                "steps": calls,
                "capped_steps": calls if cert else cap,
                "proxy_pulls": proxy_pulls,
                "proxy_frac": round(proxy_pulls / max(1, calls), 4),
                "z_in_pulls": int(arm_counts[0]),
                "z_sh_pulls": int(arm_counts[1]),
                "z_out_pulls": int(arm_counts[3]),
                "off_witness_pulls": off_w,
                "total_ms": round(1e3 * elapsed_s, 3),
            }
        )
    return rows


def _record_toy_trajectory(seed: int = 7) -> list[dict]:
    """Record step-by-step certificate evolution on MotivationalProxyDAGProblem for Figure 1."""
    prob = MotivationalProxyDAGProblem(hw=0.18)
    sup_struct = SupportStructure(prob.graph)
    cert_eval = JointEllipsoidCertifier(sup_struct, epsilon=TOY_EPS, solver="colgen_full")
    g_true = prob.phi[3] - prob.phi[0]

    traj: list[dict] = []
    for method, acq in (
        ("contrast_directed_joint", "contrast_directed"),
        ("direct_witness_joint", "direct_witness"),
        ("gp_ucb_joint", "gp_ucb"),
    ):
        model = LinearFeatureModel(
            phi=prob.phi,
            prior_mean=prob.prior_mean,
            reg_lambda=0.02,
            obs_std=prob.obs_std,
            param_bound=prob.param_bound,
            beta_mode="abbasi_yadkori",
            delta=DELTA,
        )
        sess = CorrelationAwareCertSession(
            prob, seed=seed, epsilon=TOY_EPS, model=model, cert_mode="joint_ellipsoid", acquisition=acq, delta=DELTA
        )
        max_steps = 160
        for step_i in range(max_steps + 1):
            means, psi = model.terminal_means_and_psi()
            stds = model.terminal_stds()
            beta = model.beta()
            c0 = cert_eval.certify_action(0, means, psi, prob.phi, beta)
            sup0 = sup_struct.supports[0]
            comp0 = sup_struct.complements[0]
            r_box = max(0.0, float(np.max((means + beta * stds)[comp0]) - np.max((means - beta * stds)[sup0])))
            contrast_std = float(math.sqrt(max(0.0, float(g_true @ (model.v_inv @ g_true))))) * model.obs_std
            traj.append(
                {
                    "method": method,
                    "step": step_i,
                    "joint_regret_a0": round(c0.regret, 6),
                    "enclosing_box_regret_a0": round(r_box, 6),
                    "contrast_posterior_std": round(contrast_std, 6),
                    "z_in_marginal_std": round(float(stds[0]) * model.obs_std, 6),
                    "proxy_pulls": int(model.arm_counts[4]),
                    "z_in_pulls": int(model.arm_counts[0]),
                    "z_out_pulls": int(model.arm_counts[3]),
                    "certified": bool(sess.certified),
                }
            )
            if sess.certified or step_i == max_steps:
                break
            sess.step()
    return traj


def summarize(dest: Path) -> None:
    e0_rows = [json.loads(x) for x in (dest / "e0_audit_runs.jsonl").read_text().splitlines() if x.strip()]
    toy_rows = [json.loads(x) for x in (dest / "toy_runs.jsonl").read_text().splitlines() if x.strip()]

    # E0 summary
    e0_summary = {
        "total_instances": len(e0_rows),
        "max_err_colgen_vs_socp": max(r["err_colgen_vs_socp"] for r in e0_rows),
        "max_err_lazy_vs_socp": max(r["err_lazy_vs_socp"] for r in e0_rows),
        "max_err_afw_vs_socp": max(r["err_afw_vs_socp"] for r in e0_rows),
        "max_err_primal_vs_socp": max(r["err_primal_vs_socp"] for r in e0_rows),
        "ordering_violations": sum(1 for r in e0_rows if not r["ordering_ok"]),
        "caratheodory_violations": sum(1 for r in e0_rows if not r["caratheodory_ok"]),
        "median_box_over_ellipsoid": round(
            statistics.median(r["box_over_ellipsoid_ratio"] for r in e0_rows if r["case_type"] == "random"), 4
        ),
        "max_duality_gap": max(r["max_duality_gap"] for r in e0_rows),
    }
    (dest / "summary_e0_audit.json").write_text(json.dumps(e0_summary, indent=2) + "\n")

    # Toy summary CSV
    toy_summary: list[dict] = []
    os_med = float(np.median([r["capped_steps"] for r in toy_rows if r["method"] == "opt_sep"]))
    for m in TOY_METHODS:
        sub = [r for r in toy_rows if r["method"] == m]
        if not sub:
            continue
        st = np.array([float(r["capped_steps"]) for r in sub])
        pf = np.array([float(r["proxy_frac"]) for r in sub])
        med_s = float(np.median(st))
        toy_summary.append(
            {
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                "median_steps": round(med_s, 1),
                "q25_steps": round(float(np.percentile(st, 25)), 1),
                "q75_steps": round(float(np.percentile(st, 75)), 1),
                "mean_steps": round(float(np.mean(st)), 1),
                "speedup_vs_opt_sep": round(os_med / max(1.0, med_s), 2),
                "mean_proxy_frac": round(float(np.mean(pf)), 4),
                "mean_z_out_pulls": round(float(np.mean([r["z_out_pulls"] for r in sub])), 1),
            }
        )
    with (dest / "summary_toy.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(toy_summary[0].keys()))
        w.writeheader()
        w.writerows(toy_summary)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=20)
    args = ap.parse_args()

    dest: Path = args.out
    dest.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(dest)
        return

    t_start = time.perf_counter()

    # Build E0 task list (200 total in full mode; 16 in smoke mode)
    e0_tasks: list[tuple[int, int, int, str]] = []
    if args.smoke:
        combos = [(4, 2, "random"), (8, 3, "random"), (12, 5, "random"), (8, 3, "hull_contained"), (6, 2, "empty_complement")]
        for idx, (m, d, ct) in enumerate(combos * 3):
            e0_tasks.append((idx, m, d, ct))
        n_toy_seeds = 6
        toy_cap = 1500
    else:
        tid = 0
        for m in (4, 6, 8, 12):
            for d in (2, 3, 5):
                if d >= m:
                    continue
                for _ in range(16):
                    e0_tasks.append((tid, m, d, "random"))
                    tid += 1
        for _ in range(16):
            e0_tasks.append((tid, 10, 3, "hull_contained"))
            tid += 1
        for _ in range(8):
            e0_tasks.append((tid, 8, 3, "empty_complement"))
            tid += 1
        n_toy_seeds = 50
        toy_cap = TOY_CAP

    toy_tasks = [(100 + s, toy_cap) for s in range(n_toy_seeds)]

    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        e0_all = list(ex.map(_e0_worker, e0_tasks))
        toy_nested = list(ex.map(_toy_worker, toy_tasks))
    toy_all = [r for grp in toy_nested for r in grp]
    traj_rows = _record_toy_trajectory(seed=7)

    # Also compute exact T5 information-theoretic lower bound on the motivational toy
    toy_prob = MotivationalProxyDAGProblem(hw=0.18)
    toy_ss = SupportStructure(toy_prob.graph)
    rate_res = compute_characteristic_rate(
        toy_prob.phi, toy_prob.theta_star, toy_ss, TOY_EPS, toy_prob.obs_std, n_outer_iters=60
    )
    kl_val = (1.0 - DELTA) * np.log((1.0 - DELTA) / DELTA) + DELTA * np.log(DELTA / (1.0 - DELTA))
    t5_info = {
        "target_action": rate_res.target_action,
        "characteristic_rate": round(rate_res.rate, 6),
        "lower_bound_steps_delta05": round(float(kl_val / max(1e-12, rate_res.rate)), 2),
        "optimal_weights": [round(float(x), 4) for x in rate_res.optimal_weights],
    }

    f_e0 = dest / "e0_audit_runs.jsonl"
    f_toy = dest / "toy_runs.jsonl"
    f_traj = dest / "toy_trajectory.csv"
    f_e0.write_text("\n".join(json.dumps(r) for r in e0_all) + "\n")
    f_toy.write_text("\n".join(json.dumps(r) for r in toy_all) + "\n")
    with f_traj.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(traj_rows[0].keys()))
        w.writeheader()
        w.writerows(traj_rows)
    (dest / "toy_t5_lower_bound.json").write_text(json.dumps(t5_info, indent=2) + "\n")

    summarize(dest)

    manifest = {
        "suite": "v7_e0_and_toy",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "e0_instances": len(e0_all),
        "toy_runs": len(toy_all),
        "sha256_e0": _sha256(f_e0),
        "sha256_toy": _sha256(f_toy),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Completed E0 + Toy in {manifest['elapsed_s']:.2f}s ({len(e0_all)} E0 + {len(toy_all)} toy runs).")


if __name__ == "__main__":
    main()
