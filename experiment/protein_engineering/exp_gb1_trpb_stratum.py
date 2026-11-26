"""Experiment E3: Real Protein Engineering Benchmarks (GB1 & Complete 21-Template TmTrpB).

Evaluates the exact six-method factorial design separating correlated modeling, root-aware
acquisition, and joint ellipsoidal/posterior certification across:
1. All 10 GB1 templates (`Wu et al., eLife 2016`; epistatic ridge vs single-peak), and
2. The complete, unselected 21-template TmTrpB neighborhood (`Johnston et al., PNAS 2024`).

Strict scientific separation (NO held-out landscape peeking!):
- **Frequentist-Valid Track** (0% false-certificate guarantee independent of GP misspecification):
  1. `flat_lucb_root` (Correlated: No, Root-aware: No, Joint cert: No)
  2. `opt_sep` (Correlated: No, Root-aware: Yes, Joint cert: No)
  3. `gp_ucb_freq_cert` (Correlated: Yes, Root-aware: No, Joint cert: No — GP-UCB + independent CS)
  4. `gp_root_info_freq` (Correlated: Yes, Root-aware: Yes, Joint cert: No — GP-Root-Info + independent CS)
  5. `contrast_directed_freq` (Correlated: Yes, Root-aware: Yes, Joint cert: No — Contrast-Directed + safe CS fallback)
- **Nominal Bayesian Surrogate Track** (explicitly separated; audited for empirical failure rate):
  6. `joint_gp_ucb_nom` (Correlated: Yes, Root-aware: No, Joint cert: Yes — GP-UCB + joint GP ellipsoid)
  7. `joint_gp_cd_nom` (Correlated: Yes, Root-aware: Yes, Joint cert: Yes — Contrast-Directed + joint GP ellipsoid)
  8. `bayes_post_cd` (Correlated: Yes, Root-aware: Yes, Joint cert: Bayesian posterior `q_t(a) >= 1 - delta`)

Prior hyperparameters (`prior_scale=0.22`, `prior_mean=0.28`, `obs_std=0.16` on `[0, 1]` scale)
are fixed a priori without touching held-out fitness landscapes.
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

from dagcert import HybridWitnessDAGLUCBSession
from dagcert._core.v6_bayesian_opt import GPGuidedRootCertSession, protein_sequence_kernel
from dagcert._core.v6_real_world import (
    FlatLUCBSession,
    GB1MutationCampaignProblem,
    TrpBMutationCampaignProblem,
    real_world_problem_diagnostics,
)
from dagcert import (
    CorrelationAwareCertSession,
    DiscreteGPPosteriorModel,
)
from experiment.protein_engineering.exp_real_world_applications import GB1_TEMPLATES
from experiment.protein_engineering.exp_real_world_validation import TRPB_TEMPLATES


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/e3_proteins"

E3_METHODS = (
    # Frequentist-valid track (independent CS stopping)
    ("flat_lucb_root", "frequentist"),
    ("opt_sep", "frequentist"),
    ("gp_ucb_freq_cert", "frequentist"),
    ("gp_root_info_freq", "frequentist"),
    ("contrast_directed_freq", "frequentist"),
    # Nominal Bayesian surrogate track (joint GP ellipsoid / posterior stopping)
    ("joint_gp_ucb_nom", "nominal_bayesian"),
    ("joint_gp_cd_nom", "nominal_bayesian"),
    ("bayes_post_cd", "nominal_bayesian"),
)
DELTA = 0.05
PROT_EPS = 0.015
PROT_CAP = 12000


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _protein_worker(task: tuple[str, str, int, int]) -> list[dict]:
    landscape, start_seq, seed, cap = task
    if landscape == "gb1":
        prob = GB1MutationCampaignProblem(start_seq=start_seq, max_edits=3, panel="panel5", noise_model="calibrated")
        prior_m = 0.28
        obs_s = 0.16
    else:
        prob = TrpBMutationCampaignProblem(
            start_seq=start_seq, max_edits=3, panel="panel5", noise_model="low_var_uniform"
        )
        prior_m = 0.30
        obs_s = 0.08 / np.sqrt(3.0)

    diag = real_world_problem_diagnostics(prob)
    gamma = float(diag["exterior_margin_gamma"])
    flat_gap = float(diag["flat_top2_gap"])
    ratio = gamma / max(1e-6, flat_gap)
    regime = "epistatic_ridge" if ratio >= 10.0 else "single_peak"

    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    seqs = [prob.variant_of_leaf[z] for z in prob.graph.leaves]
    # Fixed a priori domain kernel (no peeking at true fitnesses!)
    k_mat = protein_sequence_kernel(seqs, prior_scale=0.22, lengthscale=3.0, nugget=0.02)

    rows: list[dict] = []
    for method, track in E3_METHODS:
        t0 = time.perf_counter()
        discover_step = -1
        call_idx = 0

        if method == "flat_lucb_root":
            sess = FlatLUCBSession(prob, seed, PROT_EPS, delta=DELTA, schedule="emp_bernstein", stop_rule="root_exact")
        elif method == "opt_sep":
            sess = HybridWitnessDAGLUCBSession(prob, seed, PROT_EPS, mode="opt_sep", delta=DELTA, schedule="emp_bernstein")
        elif method == "gp_ucb_freq_cert":
            sess = GPGuidedRootCertSession(
                prob, seed, PROT_EPS, acquisition="gp_ucb", delta=DELTA, schedule="emp_bernstein",
                kernel=k_mat, prior_mean=prior_m, obs_std=obs_s,
            )
        elif method == "gp_root_info_freq":
            sess = GPGuidedRootCertSession(
                prob, seed, PROT_EPS, acquisition="gp_root_info", delta=DELTA, schedule="emp_bernstein",
                kernel=k_mat, prior_mean=prior_m, obs_std=obs_s,
            )
        else:
            gp_mod = DiscreteGPPosteriorModel(
                kernel=k_mat,
                prior_mean=prior_m,
                obs_std=obs_s,
                beta_mode="nominal_bayes",
                delta=DELTA,
            )
            cert_m, acq_m, check_ev = {
                "contrast_directed_freq": ("independent_box", "contrast_directed", 12),
                "joint_gp_ucb_nom": ("joint_ellipsoid", "gp_ucb", 12),
                "joint_gp_cd_nom": ("joint_ellipsoid", "contrast_directed", 12),
                "bayes_post_cd": ("posterior_prob", "contrast_directed", 10),
            }[method]
            sess = CorrelationAwareCertSession(
                prob,
                seed=seed,
                epsilon=PROT_EPS,
                model=gp_mod,
                cert_mode=cert_m,
                acquisition=acq_m,
                delta=DELTA,
                cs_schedule="emp_bernstein",
                check_every=10,
                adaptive_check=True,
                mc_posterior_draws=512,
            )

        orig_sample = sess.oracle.sample

        def _tracked_sample(leaf: int, _orig=orig_sample) -> float:
            nonlocal discover_step, call_idx
            call_idx += 1
            if discover_step < 0 and float(prob.means[leaf]) >= opt_mu - PROT_EPS - 1e-12:
                discover_step = call_idx
            return _orig(leaf)

        sess.oracle.sample = _tracked_sample

        wall_lim = 8.0
        while not sess.certified and sess.calls < cap and (time.perf_counter() - t0) < wall_lim:
            if hasattr(sess, "monitor") and sess.monitor.evidence.conflict:
                break
            if hasattr(sess, "evidence") and sess.evidence.conflict:
                break
            if getattr(sess, "conflict", False):
                break
            sess.step()

        elapsed_s = time.perf_counter() - t0
        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        true_reg = regrets[act]
        false_cert = bool(cert and true_reg > PROT_EPS + 1e-12)
        if track == "frequentist":
            assert not false_cert, f"Frequentist false cert on {landscape}/{start_seq}/{method}: {true_reg}"

        cert_s = float(sess.ellipsoid_cert.cert_time_s) if hasattr(sess, "ellipsoid_cert") else 0.0
        rows.append(
            {
                "landscape": landscape,
                "start_seq": start_seq,
                "regime": regime,
                "m_leaves": len(prob.graph.leaves),
                "k_actions": len(root_ch),
                "gamma_over_flat": round(ratio, 3),
                "seed": seed,
                "method": method,
                "track": track,
                "eps": PROT_EPS,
                "certified": cert,
                "false_certificate": false_cert,
                "steps": calls,
                "capped_steps": calls if cert else cap,
                "discover_steps": discover_step if discover_step > 0 else cap,
                "discovered": discover_step > 0,
                "final_regret": round(true_reg, 6),
                "cert_ms": round(1e3 * cert_s, 2),
                "total_ms": round(1e3 * elapsed_s, 2),
            }
        )
    return rows


def summarize(dest: Path) -> None:
    runs = [json.loads(x) for x in (dest / "e3_protein_runs.jsonl").read_text().splitlines() if x.strip()]
    out_rows: list[dict] = []
    for land in ("gb1", "trpb"):
        l_runs = [r for r in runs if r["landscape"] == land]
        if not l_runs:
            continue
        strata = ("all", "epistatic_ridge", "single_peak") if land == "gb1" else ("all",)
        for strat in strata:
            s_runs = [r for r in l_runs if strat == "all" or r["regime"] == strat]
            if not s_runs:
                continue
            os_med = float(np.median([r["capped_steps"] for r in s_runs if r["method"] == "opt_sep"]))
            for method, track in E3_METHODS:
                sub = [r for r in s_runs if r["method"] == method]
                if not sub:
                    continue
                st = np.array([float(r["capped_steps"]) for r in sub])
                ds = np.array([float(r["discover_steps"]) for r in sub])
                med_s = float(np.median(st))
                out_rows.append(
                    {
                        "landscape": land,
                        "stratum": strat,
                        "track": track,
                        "method": method,
                        "runs": len(sub),
                        "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                        "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                        "false_cert_rate": round(sum(1 for r in sub if r["false_certificate"]) / len(sub), 4),
                        "median_discover_steps": round(float(np.median(ds)), 1),
                        "median_steps": round(med_s, 1),
                        "q25_steps": round(float(np.percentile(st, 25)), 1),
                        "q75_steps": round(float(np.percentile(st, 75)), 1),
                        "speedup_vs_opt_sep": round(os_med / max(1.0, med_s), 2),
                        "mean_final_regret": round(statistics.fmean(r["final_regret"] for r in sub), 5),
                        "median_total_ms": round(statistics.median(r["total_ms"] for r in sub), 1),
                    }
                )
    with (dest / "summary_e3_proteins.csv").open("w", newline="") as fh:
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
    if args.smoke:
        gb1_t = GB1_TEMPLATES[:2]
        trpb_t = TRPB_TEMPLATES[:2]
        seeds = (7001,)
        cap = 2000
    else:
        gb1_t = GB1_TEMPLATES
        trpb_t = TRPB_TEMPLATES
        seeds = (7001, 7002, 7003, 7004)
        cap = PROT_CAP

    tasks = [("gb1", t, s, cap) for t in gb1_t for s in seeds] + [
        ("trpb", t, s, cap) for t in trpb_t for s in seeds
    ]
    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        nested = list(ex.map(_protein_worker, tasks))
    all_runs = [r for grp in nested for r in grp]

    f_out = dest / "e3_protein_runs.jsonl"
    f_out.write_text("\n".join(json.dumps(r) for r in all_runs) + "\n")
    summarize(dest)

    manifest = {
        "suite": "v7_e3_proteins",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "total_runs": len(all_runs),
        "sha256_runs": _sha256(f_out),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Completed E3 Proteins in {manifest['elapsed_s']:.2f}s ({len(all_runs)} runs).")


if __name__ == "__main__":
    main()
