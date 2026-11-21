"""Experiment E2: Feature-Hull Dominance, Off-Witness Proxy Sampling, and Multiple Acceptable Answers.

Directly validates Theory Programs T2, T4, and T5 across four controlled families:
- Family A (Exact Convex-Hull Dominance, T2.1): Disjoint supports with `eta = 0`, sweeping
  `M in {16, 32, 64, 128, 256}` — verifies 0-sample certification vs `Theta(M)` independent scaling.
- Family B (Approximate Hull Dominance, T2.2--T2.3): Sweeps geometric discrepancy
  `eta in {0.0, 0.005, 0.01, 0.02, 0.04, 0.08, 0.16, 0.32}` at `M = 64, d = 4`.
- Family C1 (Informative Off-Witness Proxies, T4): Multi-branch DAGs where diagnostic proxy
  terminals on a strictly suboptimal third branch carry clean information about the winning contrast.
  Compares `opt_sep`, `enclosing_box_cd`, `gp_ucb_joint`, `direct_witness_joint`,
  `contrast_directed_joint`, `multi_contrast_joint`, `bayes_ids_joint`, `maxmin_tracking_joint`.
- Family C2 (Multiple Acceptable Root Commitments, T5.3): Compares greedy empirical commitment
  (`greedy_emp`) vs support-aware minimum-regret commitment (`min_regret`) alongside exact
  variational characteristic-time lower bounds `kl(1-delta, delta) / I*(a; theta*)`.
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
import multiprocessing as mp
from pathlib import Path
import platform
import statistics
import time

import numpy as np

from dag_mcts.v5_hybrid_and_os import HybridWitnessDAGLUCBSession
from dag_mcts.v7_bayesian_ucd import (
    CorrelationAwareCertSession,
    LinearFeatureModel,
    SupportStructure,
    compute_characteristic_rate,
    compute_hull_discrepancy,
)
from dag_mcts.v7_benchmarks import (
    HullDominanceDAGProblem,
    MultiAnswerCommitmentDAGProblem,
    OffWitnessProxyDAGProblem,
)


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/bayesian_ucd_v1/e2_geometry_and_proxy"

DELTA = 0.05
FAM_A_MS = (16, 32, 64, 128, 256)
FAM_B_ETAS = (0.0, 0.005, 0.01, 0.02, 0.04, 0.08, 0.16, 0.32)
FAM_C1_GAMMAS = (0.14, 0.22, 0.35)
CAP = 12000


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_hull_task(task: tuple[str, int, float, int]) -> list[dict]:
    family, m_leaves, eta, inst_idx = task
    prob = HullDominanceDAGProblem(seed=inst_idx + 1, eta=eta, m_leaves=m_leaves, k_actions=4, d_feat=4)
    ss = SupportStructure(prob.graph)
    hull_rep = compute_hull_discrepancy(prob.phi, ss)[0]
    eps = 0.020
    oracle_seed = 51000 + inst_idx * 17 + m_leaves
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    rows: list[dict] = []
    for method in ("opt_sep", "enclosing_box_cd", "gp_ucb_joint", "contrast_directed_joint", "multi_contrast_joint"):
        if method == "opt_sep":
            sess = HybridWitnessDAGLUCBSession(
                prob, oracle_seed, eps, mode="opt_sep", delta=DELTA, schedule="emp_bernstein"
            )
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < CAP:
                sess.step()
        else:
            model = LinearFeatureModel(
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                reg_lambda=0.5,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                beta_mode="abbasi_yadkori",
                delta=DELTA,
            )
            cert_m, acq_m = {
                "enclosing_box_cd": ("enclosing_box", "contrast_directed"),
                "gp_ucb_joint": ("joint_ellipsoid", "gp_ucb"),
                "contrast_directed_joint": ("joint_ellipsoid", "contrast_directed"),
                "multi_contrast_joint": ("joint_ellipsoid", "multi_contrast"),
            }[method]
            sess = CorrelationAwareCertSession(
                prob, seed=oracle_seed, epsilon=eps, model=model, cert_mode=cert_m, acquisition=acq_m, delta=DELTA,
                check_every=1, adaptive_check=True,
            )
            while not sess.certified and not sess.conflict and sess.calls < CAP:
                sess.step()

        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        false_cert = bool(cert and regrets[act] > eps + 1e-12)
        assert not false_cert, f"False cert in E2 {family}/{method}: {regrets[act]} > {eps}"
        rows.append(
            {
                "family": family,
                "m": m_leaves,
                "eta": eta,
                "measured_hull_dist": round(hull_rep.max_hull_dist_l2, 6),
                "inst_idx": inst_idx,
                "method": method,
                "certified": cert,
                "false_certificate": false_cert,
                "steps": calls,
                "capped_steps": calls if cert else CAP,
            }
        )
    return rows


def _run_proxy_task(task: tuple[float, int]) -> list[dict]:
    gamma, inst_idx = task
    prob = OffWitnessProxyDAGProblem(seed=inst_idx + 1, gamma=gamma, m_leaves=48, k_actions=4, d_feat=6)
    eps = 0.020
    oracle_seed = 54000 + inst_idx * 23 + int(round(gamma * 100))
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    methods = (
        "opt_sep",
        "enclosing_box_cd",
        "gp_ucb_joint",
        "direct_witness_joint",
        "contrast_directed_joint",
        "multi_contrast_joint",
        "bayes_ids_joint",
        "maxmin_tracking_joint",
    )
    proxy_set = set(prob.proxy_leaf_indices)
    rows: list[dict] = []
    for method in methods:
        if method == "opt_sep":
            sess = HybridWitnessDAGLUCBSession(
                prob, oracle_seed, eps, mode="opt_sep", delta=DELTA, schedule="emp_bernstein"
            )
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < CAP:
                sess.step()
            proxy_pulls = sum(sess.oracle.obs[prob.graph.leaves[i]] for i in proxy_set)
            off_w = 0
        else:
            model = LinearFeatureModel(
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                reg_lambda=0.05,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                beta_mode="abbasi_yadkori",
                delta=DELTA,
            )
            cert_m, acq_m = {
                "enclosing_box_cd": ("enclosing_box", "contrast_directed"),
                "gp_ucb_joint": ("joint_ellipsoid", "gp_ucb"),
                "direct_witness_joint": ("joint_ellipsoid", "direct_witness"),
                "contrast_directed_joint": ("joint_ellipsoid", "contrast_directed"),
                "multi_contrast_joint": ("joint_ellipsoid", "multi_contrast"),
                "bayes_ids_joint": ("joint_ellipsoid", "bayes_ids"),
                "maxmin_tracking_joint": ("joint_ellipsoid", "maxmin_tracking"),
            }[method]
            sess = CorrelationAwareCertSession(
                prob,
                seed=oracle_seed,
                epsilon=eps,
                model=model,
                cert_mode=cert_m,
                acquisition=acq_m,
                delta=DELTA,
                check_every=1,
                adaptive_check=True,
            )
            while not sess.certified and not sess.conflict and sess.calls < CAP:
                sess.step()
            proxy_pulls = int(sum(int(model.arm_counts[i]) for i in proxy_set))
            off_w = int(sess.off_witness_pulls)

        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        false_cert = bool(cert and regrets[act] > eps + 1e-12)
        assert not false_cert, f"False cert in E2 proxy {method}: {regrets[act]} > {eps}"
        rows.append(
            {
                "family": "C1_proxy",
                "gamma": gamma,
                "inst_idx": inst_idx,
                "method": method,
                "certified": cert,
                "false_certificate": false_cert,
                "steps": calls,
                "capped_steps": calls if cert else CAP,
                "proxy_branch_pulls": proxy_pulls,
                "proxy_branch_frac": round(proxy_pulls / max(1, calls), 4),
                "off_witness_pulls": off_w,
            }
        )
    return rows


def _run_multianswer_task(inst_idx: int) -> list[dict]:
    eps = 0.045
    prob = MultiAnswerCommitmentDAGProblem(seed=inst_idx + 1, epsilon=eps, m_leaves=36, hw=0.10)
    ss = SupportStructure(prob.graph)
    rate_res = compute_characteristic_rate(prob.phi, prob.theta_star, ss, eps, prob.obs_std, n_outer_iters=45)
    kl_val = (1.0 - DELTA) * np.log((1.0 - DELTA) / DELTA) + DELTA * np.log(DELTA / (1.0 - DELTA))
    lb_greedy = float(kl_val / max(1e-12, rate_res.per_action_rates[0]))
    lb_support = float(kl_val / max(1e-12, rate_res.per_action_rates[1]))

    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    oracle_seed = 58000 + inst_idx * 29

    rows: list[dict] = []
    for label, acq, ans_rule in (
        ("greedy_answer_cd", "contrast_directed", "greedy_emp"),
        ("support_aware_cd", "contrast_directed", "min_regret"),
        ("support_aware_mc", "multi_contrast", "min_regret"),
        ("opt_sep_indep", "opt_sep", "min_regret"),
    ):
        if acq == "opt_sep":
            sess = HybridWitnessDAGLUCBSession(
                prob, oracle_seed, eps, mode="opt_sep", delta=DELTA, schedule="emp_bernstein"
            )
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < CAP:
                sess.step()
        else:
            model = LinearFeatureModel(
                phi=prob.phi,
                prior_mean=prob.prior_mean,
                reg_lambda=0.05,
                obs_std=prob.obs_std,
                param_bound=prob.param_bound,
                beta_mode="abbasi_yadkori",
                delta=DELTA,
            )
            sess = CorrelationAwareCertSession(
                prob,
                seed=oracle_seed,
                epsilon=eps,
                model=model,
                cert_mode="joint_ellipsoid",
                acquisition=acq,
                answer_rule=ans_rule,
                delta=DELTA,
                check_every=1,
                adaptive_check=True,
            )
            while not sess.certified and not sess.conflict and sess.calls < CAP:
                sess.step()

        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        true_reg = regrets[act]
        false_cert = bool(cert and true_reg > eps + 1e-12)
        assert not false_cert, f"False cert in E2 C2 {label}: {true_reg} > {eps}"
        rows.append(
            {
                "family": "C2_multianswer",
                "inst_idx": inst_idx,
                "method": label,
                "certified": cert,
                "false_certificate": false_cert,
                "chosen_action": act,
                "true_regret": round(true_reg, 5),
                "steps": calls,
                "capped_steps": calls if cert else CAP,
                "t5_lb_greedy_a0": round(lb_greedy, 2),
                "t5_lb_support_a1": round(lb_support, 2),
            }
        )
    return rows


def summarize(dest: Path) -> None:
    hull_runs = [json.loads(x) for x in (dest / "e2_hull_runs.jsonl").read_text().splitlines() if x.strip()]
    proxy_runs = [json.loads(x) for x in (dest / "e2_proxy_runs.jsonl").read_text().splitlines() if x.strip()]
    ma_runs = [json.loads(x) for x in (dest / "e2_multianswer_runs.jsonl").read_text().splitlines() if x.strip()]

    # Family A & B summary
    h_rows: list[dict] = []
    for fam in ("A_exact_hull", "B_approx_hull"):
        sub_f = [r for r in hull_runs if r["family"] == fam]
        keys = sorted({(r["m"], r["eta"]) for r in sub_f})
        for m_val, eta_val in keys:
            cell = [r for r in sub_f if r["m"] == m_val and abs(r["eta"] - eta_val) < 1e-9]
            for meth in sorted({r["method"] for r in cell}):
                sub = [r for r in cell if r["method"] == meth]
                st = np.array([float(r["capped_steps"]) for r in sub])
                h_rows.append(
                    {
                        "family": fam,
                        "m": m_val,
                        "eta": eta_val,
                        "measured_hull_dist": round(statistics.fmean(r["measured_hull_dist"] for r in sub), 5),
                        "method": meth,
                        "runs": len(sub),
                        "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                        "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                        "median_steps": round(float(np.median(st)), 1),
                        "q25_steps": round(float(np.percentile(st, 25)), 1),
                        "q75_steps": round(float(np.percentile(st, 75)), 1),
                    }
                )
    with (dest / "summary_e2_hull.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(h_rows[0].keys()))
        w.writeheader()
        w.writerows(h_rows)

    # Family C1 proxy summary
    p_rows: list[dict] = []
    for gam in FAM_C1_GAMMAS:
        cell = [r for r in proxy_runs if abs(r["gamma"] - gam) < 1e-9]
        if not cell:
            continue
        dw_med = float(np.median([r["capped_steps"] for r in cell if r["method"] == "direct_witness_joint"]))
        for meth in sorted({r["method"] for r in cell}):
            sub = [r for r in cell if r["method"] == meth]
            st = np.array([float(r["capped_steps"]) for r in sub])
            med_s = float(np.median(st))
            p_rows.append(
                {
                    "gamma": gam,
                    "method": meth,
                    "runs": len(sub),
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                    "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                    "median_steps": round(med_s, 1),
                    "q25_steps": round(float(np.percentile(st, 25)), 1),
                    "q75_steps": round(float(np.percentile(st, 75)), 1),
                    "speedup_vs_direct_witness": round(dw_med / max(1.0, med_s), 2),
                    "mean_proxy_branch_frac": round(statistics.fmean(r["proxy_branch_frac"] for r in sub), 4),
                }
            )
    with (dest / "summary_e2_proxy.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(p_rows[0].keys()))
        w.writeheader()
        w.writerows(p_rows)

    # Family C2 multi-answer summary
    ma_rows: list[dict] = []
    for meth in ("greedy_answer_cd", "support_aware_cd", "support_aware_mc", "opt_sep_indep"):
        sub = [r for r in ma_runs if r["method"] == meth]
        if not sub:
            continue
        st = np.array([float(r["capped_steps"]) for r in sub])
        ma_rows.append(
            {
                "method": meth,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                "frac_chose_hull_action_a1": round(sum(1 for r in sub if r["chosen_action"] == 1) / len(sub), 4),
                "median_steps": round(float(np.median(st)), 1),
                "q25_steps": round(float(np.percentile(st, 25)), 1),
                "q75_steps": round(float(np.percentile(st, 75)), 1),
                "median_t5_lb_a0": round(statistics.median(r["t5_lb_greedy_a0"] for r in sub), 2),
                "median_t5_lb_a1": round(statistics.median(r["t5_lb_support_a1"] for r in sub), 2),
            }
        )
    with (dest / "summary_e2_multianswer.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(ma_rows[0].keys()))
        w.writeheader()
        w.writerows(ma_rows)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=24)
    args = ap.parse_args()

    dest: Path = args.out
    dest.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(dest)
        return

    t_start = time.perf_counter()
    n_inst = 2 if args.smoke else 20

    hull_tasks: list[tuple[str, int, float, int]] = []
    for m_val in FAM_A_MS:
        for idx in range(n_inst):
            hull_tasks.append(("A_exact_hull", m_val, 0.0, idx))
    for eta_val in FAM_B_ETAS:
        for idx in range(n_inst):
            hull_tasks.append(("B_approx_hull", 64, eta_val, idx))

    proxy_tasks = [(gam, idx) for gam in FAM_C1_GAMMAS for idx in range(n_inst)]
    ma_tasks = list(range(n_inst))

    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        hull_nested = list(ex.map(_run_hull_task, hull_tasks))
        proxy_nested = list(ex.map(_run_proxy_task, proxy_tasks))
        ma_nested = list(ex.map(_run_multianswer_task, ma_tasks))

    hull_all = [r for grp in hull_nested for r in grp]
    proxy_all = [r for grp in proxy_nested for r in grp]
    ma_all = [r for grp in ma_nested for r in grp]

    f_h = dest / "e2_hull_runs.jsonl"
    f_p = dest / "e2_proxy_runs.jsonl"
    f_m = dest / "e2_multianswer_runs.jsonl"
    f_h.write_text("\n".join(json.dumps(r) for r in hull_all) + "\n")
    f_p.write_text("\n".join(json.dumps(r) for r in proxy_all) + "\n")
    f_m.write_text("\n".join(json.dumps(r) for r in ma_all) + "\n")

    summarize(dest)

    manifest = {
        "suite": "v7_e2_geometry_and_proxy",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "hull_runs": len(hull_all),
        "proxy_runs": len(proxy_all),
        "multianswer_runs": len(ma_all),
        "sha256_hull": _sha256(f_h),
        "sha256_proxy": _sha256(f_p),
        "sha256_multianswer": _sha256(f_m),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        f"Completed E2 Geometry & Proxy in {manifest['elapsed_s']:.2f}s "
        f"({len(hull_all) + len(proxy_all) + len(ma_all)} runs)."
    )


if __name__ == "__main__":
    main()
