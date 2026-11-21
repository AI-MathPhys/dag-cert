"""Experiment E4: Agentic Workflow Certification on WorFBench (`Qwen3-0.6B`).

Models the `81 = 3^4` canonical 4-stage `Qwen3-0.6B` + `Qwen3-Embedding-0.6B` workflows via the
categorical stage main-effects + pairwise-interactions feature representation (`d = 33`):

    f(z) = theta_0 + sum_{j=1}^4 theta_{j, z_j} + sum_{1 <= j < k <= 4} theta_{jk, z_j, z_k}.

Strictly preserves the split between certification tasks (`worfbench_qwen3_81x64.npz`, 64 tasks)
and held-out unseen test tasks (`worfbench_qwen3_test_81x32.npz`, 32 tasks, with exact measured
per-workflow input + output LLM token costs `c(z)`).

Evaluates:
1. Correlation calibration audit: cross-validated `R^2` and Pearson `r` of main-effects (`d=9`)
   and main+interaction (`d=33`) models on real workflow F1 scores across all domains.
2. Cost-agnostic vs cost-normalized (`Delta_t(g_t; x) / c(x)`) Contrast-Directed acquisition under
   both nominal Bayesian linear-ellipsoid stopping and distribution-free frequentist CS fallback,
   compared against `Flat-LUCB + Root Cert`, `Optimistic-Separation`, and `GP-UCB + Joint Cert`.
3. Reports total LLM tokens to certify, distinct workflows evaluated, certification rate,
   empirical error rate, and unseen `D_test` F1 generalization of the certified commitment.
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
from dag_mcts.v6_real_world import (
    FlatLUCBSession,
    WorFBenchWorkflowProblem,
)
from dag_mcts.v7_bayesian_ucd import (
    CorrelationAwareCertSession,
    LinearFeatureModel,
    build_worfbench_feature_matrix,
)
from paper.exp_real_world_applications import WORFBENCH_BASES, WORFBENCH_DOMAINS
from paper.exp_real_world_validation import _worfbench_leaf_costs_and_unseen_values


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/bayesian_ucd_v1/e4_worfbench"
TEST_NPZ_PATH = ROOT / "dag_mcts/data/worfbench_qwen3_test_81x32.npz"

E4_METHODS = (
    ("flat_lucb_root", "frequentist", False),
    ("opt_sep", "frequentist", False),
    ("contrast_freq_uniform", "frequentist", False),
    ("contrast_freq_costnorm", "frequentist", True),
    ("gp_ucb_joint_nom", "nominal_bayesian", False),
    ("contrast_joint_uniform", "nominal_bayesian", False),
    ("contrast_joint_costnorm", "nominal_bayesian", True),
    ("bayes_post_costnorm", "nominal_bayesian", True),
)
DELTA = 0.05
WF_EPS = 0.025
WF_CAP = 12000


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _calibration_audit() -> list[dict]:
    """Audit out-of-sample workflow correlation calibration (5-fold CV over workflows)."""
    rows: list[dict] = []
    for dom in WORFBENCH_DOMAINS:
        prob = WorFBenchWorkflowProblem(domain=dom, base_config=(0, 0, 0, 0), max_upgrades=4)
        y = np.array([float(prob.means[z]) for z in prob.graph.leaves], dtype=np.float64)
        for model_name, inter in (("main_effects_d9", False), ("main_plus_pair_d33", True)):
            phi = build_worfbench_feature_matrix(prob, include_interactions=inter)
            n, d = phi.shape
            rng = np.random.default_rng(2026)
            perm = rng.permutation(n)
            preds = np.zeros(n, dtype=np.float64)
            lam = 1.0 if inter else 0.25
            for fold in range(5):
                te = perm[fold::5]
                tr = np.setdiff1d(perm, te)
                w = np.linalg.solve(phi[tr].T @ phi[tr] + lam * np.eye(d), phi[tr].T @ y[tr])
                preds[te] = phi[te] @ w
            ss_res = float(np.sum((y - preds) ** 2))
            ss_tot = float(np.sum((y - np.mean(y)) ** 2))
            r2 = 1.0 - ss_res / max(1e-12, ss_tot)
            corr = float(np.corrcoef(y, preds)[0, 1]) if np.std(preds) > 1e-12 else 0.0
            max_res = float(np.max(np.abs(y - preds)))
            mae = float(np.mean(np.abs(y - preds)))
            rows.append(
                {
                    "domain": dom,
                    "feature_model": model_name,
                    "n_workflows": n,
                    "feature_dim": d,
                    "cv5_r2": round(r2, 4),
                    "cv5_pearson_r": round(corr, 4),
                    "cv5_mae": round(mae, 4),
                    "cv5_max_residual": round(max_res, 4),
                }
            )
    return rows


def _worfbench_worker(task: tuple[str, str, tuple[int, int, int, int], int, int, int]) -> list[dict]:
    domain, base_tag, base_cfg, max_up, seed, cap = task
    prob = WorFBenchWorkflowProblem(domain=domain, base_config=base_cfg, max_upgrades=max_up)
    test_archive = dict(np.load(TEST_NPZ_PATH))
    leaf_toks, _, act_test_vals, test_opt = _worfbench_leaf_costs_and_unseen_values(prob, test_archive)
    phi = build_worfbench_feature_matrix(prob, include_interactions=True)

    # Fixed domain-agnostic prior parameters (NO peeking at true workflow means!)
    prior_m = 0.45
    obs_s = 0.22
    tok_vec = np.array([leaf_toks[z] for z in prob.graph.leaves], dtype=np.float64)
    norm_tok = tok_vec / float(np.mean(tok_vec))

    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    rows: list[dict] = []
    for method, track, cost_norm in E4_METHODS:
        t0 = time.perf_counter()
        if method == "flat_lucb_root":
            sess = FlatLUCBSession(prob, seed, WF_EPS, delta=DELTA, schedule="emp_bernstein", stop_rule="root_exact")
            while not sess.certified and not sess.evidence.conflict and sess.calls < cap:
                sess.step()
            obs_map = sess.oracle.obs
        elif method == "opt_sep":
            sess = HybridWitnessDAGLUCBSession(prob, seed, WF_EPS, mode="opt_sep", delta=DELTA, schedule="emp_bernstein")
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                sess.step()
            obs_map = sess.oracle.obs
        else:
            model = LinearFeatureModel(
                phi=phi,
                prior_mean=prior_m,
                reg_lambda=1.5,
                obs_std=obs_s,
                param_bound=1.0,
                beta_mode="nominal_bayes",
                delta=DELTA,
            )
            cert_m, acq_m = {
                "contrast_freq_uniform": ("independent_box", "contrast_directed"),
                "contrast_freq_costnorm": ("independent_box", "contrast_directed"),
                "gp_ucb_joint_nom": ("joint_ellipsoid", "gp_ucb"),
                "contrast_joint_uniform": ("joint_ellipsoid", "contrast_directed"),
                "contrast_joint_costnorm": ("joint_ellipsoid", "contrast_directed"),
                "bayes_post_costnorm": ("posterior_prob", "contrast_directed"),
            }[method]
            costs_arg = norm_tok if cost_norm else np.ones(len(prob.graph.leaves), dtype=np.float64)
            sess = CorrelationAwareCertSession(
                prob,
                seed=seed,
                epsilon=WF_EPS,
                model=model,
                cert_mode=cert_m,
                acquisition=acq_m,
                delta=DELTA,
                costs=costs_arg,
                cs_schedule="emp_bernstein",
                check_every=5,
                mc_posterior_draws=512,
            )
            while not sess.certified and not sess.conflict and sess.calls < cap:
                sess.step()
            obs_map = sess.oracle.obs

        elapsed_s = time.perf_counter() - t0
        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        distinct_wf = sum(1 for z in prob.graph.leaves if obs_map[z] > 0)
        total_toks = float(sum(obs_map[z] * leaf_toks[z] for z in prob.graph.leaves))
        true_reg = regrets[act]
        false_cert = bool(cert and true_reg > WF_EPS + 1e-12)
        if track == "frequentist":
            assert not false_cert, f"Frequentist false cert on WorFBench {domain}/{method}: {true_reg}"

        unseen_f1 = act_test_vals[act]
        unseen_reg = max(0.0, test_opt - unseen_f1)
        rows.append(
            {
                "domain": domain,
                "base_config": "".join(map(str, base_cfg)),
                "seed": seed,
                "method": method,
                "track": track,
                "cost_normalized": cost_norm,
                "eps": WF_EPS,
                "certified": cert,
                "false_certificate": false_cert,
                "steps": calls,
                "capped_steps": calls if cert else cap,
                "distinct_workflows": distinct_wf,
                "total_llm_tokens": round(total_toks, 1),
                "mean_tokens_per_eval": round(total_toks / max(1, calls), 1),
                "final_cert_regret": round(true_reg, 5),
                "unseen_test_f1": round(unseen_f1, 5),
                "unseen_test_regret": round(unseen_reg, 5),
                "total_ms": round(1e3 * elapsed_s, 2),
            }
        )
    return rows


def summarize(dest: Path) -> None:
    runs = [json.loads(x) for x in (dest / "e4_worfbench_runs.jsonl").read_text().splitlines() if x.strip()]
    out_rows: list[dict] = []
    os_tok = float(np.median([r["total_llm_tokens"] for r in runs if r["method"] == "opt_sep"]))
    os_steps = float(np.median([r["capped_steps"] for r in runs if r["method"] == "opt_sep"]))
    for method, track, cost_norm in E4_METHODS:
        sub = [r for r in runs if r["method"] == method]
        if not sub:
            continue
        st = np.array([float(r["capped_steps"]) for r in sub])
        tok = np.array([float(r["total_llm_tokens"]) for r in sub])
        dwf = np.array([float(r["distinct_workflows"]) for r in sub])
        med_t = float(np.median(tok))
        med_s = float(np.median(st))
        out_rows.append(
            {
                "track": track,
                "method": method,
                "cost_normalized": cost_norm,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                "false_cert_rate": round(sum(1 for r in sub if r["false_certificate"]) / len(sub), 4),
                "median_steps": round(med_s, 1),
                "median_distinct_workflows": round(float(np.median(dwf)), 1),
                "median_llm_tokens": round(med_t, 0),
                "q25_llm_tokens": round(float(np.percentile(tok, 25)), 0),
                "q75_llm_tokens": round(float(np.percentile(tok, 75)), 0),
                "mean_tokens_per_eval": round(statistics.fmean(r["mean_tokens_per_eval"] for r in sub), 1),
                "token_speedup_vs_opt_sep": round(os_tok / max(1.0, med_t), 2),
                "step_speedup_vs_opt_sep": round(os_steps / max(1.0, med_s), 2),
                "mean_unseen_test_f1": round(statistics.fmean(r["unseen_test_f1"] for r in sub), 4),
                "mean_unseen_test_regret": round(statistics.fmean(r["unseen_test_regret"] for r in sub), 4),
            }
        )
    with (dest / "summary_e4_worfbench.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out_rows[0].keys()))
        w.writeheader()
        w.writerows(out_rows)


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
    cal_rows = _calibration_audit()
    with (dest / "summary_e4_calibration.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(cal_rows[0].keys()))
        w.writeheader()
        w.writerows(cal_rows)

    if args.smoke:
        doms = ("all", "toolalpaca")
        bases = WORFBENCH_BASES[:1]
        seeds = (8101,)
        cap = 2500
    else:
        doms = WORFBENCH_DOMAINS
        bases = WORFBENCH_BASES
        seeds = (8101, 8102, 8103, 8104)
        cap = WF_CAP

    tasks = [(d, b_tag, b_cfg, m_up, s, cap) for d in doms for (b_tag, b_cfg, m_up) in bases for s in seeds]
    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        nested = list(ex.map(_worfbench_worker, tasks))
    all_runs = [r for grp in nested for r in grp]

    f_out = dest / "e4_worfbench_runs.jsonl"
    f_out.write_text("\n".join(json.dumps(r) for r in all_runs) + "\n")
    summarize(dest)

    manifest = {
        "suite": "v7_e4_worfbench",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "total_runs": len(all_runs),
        "sha256_runs": _sha256(f_out),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Completed E4 WorFBench in {manifest['elapsed_s']:.2f}s ({len(all_runs)} runs).")


if __name__ == "__main__":
    main()
