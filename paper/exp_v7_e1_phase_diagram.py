"""Experiment E1: Central 2D Phase Diagram (Graph Overlap x Value Correlation).

Constructs controlled zero-containment search DAGs (`M = 128`, `K = 8`, `d = 8`, `delta = 0.05`)
while varying two orthogonal factors:
- Support overlap `omega in {0.00, 0.25, 0.50, 0.75}`
- Feature correlation `rho in {0.00, 0.30, 0.60, 0.90}`

with 20 independently generated instances per cell (`320` instances) and exact exterior support
margin matching (`Gamma_ext(a*) = 0.065`) across all cells so correlation never confounds true
decision difficulty. Also runs sensitivity checks at `eps = 0.01`, `M = 256`, and `d in {4, 16}`,
and explicitly evaluates the negative-control corner `(omega = 0, rho = 0)`.
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
from dag_mcts.v6_real_world import FlatLUCBSession
from dag_mcts.v7_bayesian_ucd import (
    CorrelationAwareCertSession,
    LinearFeatureModel,
    SupportStructure,
)
from dag_mcts.v7_benchmarks import OverlapCorrelationDAGProblem


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/bayesian_ucd_v1/e1_phase_diagram"

OVERLAPS = (0.00, 0.25, 0.50, 0.75)
RHOS = (0.00, 0.30, 0.60, 0.90)
E1_METHODS = (
    "flat_lucb_root",
    "exact_dag_lucb",
    "opt_sep",
    "enclosing_box_cd",
    "gp_ucb_joint",
    "contrast_directed_joint",
    "multi_contrast_joint",
    "maxmin_tracking_joint",
)
DELTA = 0.05
MAIN_EPS = 0.030
MAIN_CAP = 12000


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_e1_instance(task: tuple[str, float, float, int, int, int, float, int, tuple[str, ...]]) -> list[dict]:
    cohort, overlap, rho, m_leaves, k_act, d_feat, eps, inst_idx, methods = task
    prob = OverlapCorrelationDAGProblem(
        seed=inst_idx + 1,
        overlap=overlap,
        rho=rho,
        m_leaves=m_leaves,
        k_actions=k_act,
        d_feat=d_feat,
        target_margin=0.065,
        hw=0.16,
    )
    ss = SupportStructure(prob.graph)
    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
    oracle_seed = 41000 + inst_idx * 31 + int(round(overlap * 100)) * 7 + int(round(rho * 100))
    cap = MAIN_CAP

    rows: list[dict] = []
    for method in methods:
        t0 = time.perf_counter()
        if method == "flat_lucb_root":
            sess = FlatLUCBSession(prob, oracle_seed, eps, delta=DELTA, schedule="emp_bernstein", stop_rule="root_exact")
            while not sess.certified and not sess.evidence.conflict and sess.calls < cap:
                sess.step()
            off_w = 0
            cert_s = 0.0
        elif method == "exact_dag_lucb":
            sess = HybridWitnessDAGLUCBSession(prob, oracle_seed, eps, mode="ucb", delta=DELTA, schedule="emp_bernstein")
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                sess.step()
            off_w = 0
            cert_s = 0.0
        elif method == "opt_sep":
            sess = HybridWitnessDAGLUCBSession(
                prob, oracle_seed, eps, mode="opt_sep", delta=DELTA, schedule="emp_bernstein"
            )
            while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                sess.step()
            off_w = 0
            cert_s = 0.0
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
                "maxmin_tracking_joint": ("joint_ellipsoid", "maxmin_tracking"),
            }[method]
            check_ev = 2 if m_leaves <= 128 else 4
            sess = CorrelationAwareCertSession(
                prob,
                seed=oracle_seed,
                epsilon=eps,
                model=model,
                cert_mode=cert_m,
                acquisition=acq_m,
                delta=DELTA,
                check_every=check_ev,
                adaptive_check=True,
            )
            while not sess.certified and not sess.conflict and sess.calls < cap:
                sess.step()
            off_w = int(sess.off_witness_pulls)
            cert_s = float(sess.ellipsoid_cert.cert_time_s)

        elapsed_s = time.perf_counter() - t0
        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        true_reg = regrets[act]
        false_cert = bool(cert and true_reg > eps + 1e-12)
        assert not false_cert, f"False certificate in E1 {method} on {prob.name}: {true_reg} > {eps}"

        rows.append(
            {
                "cohort": cohort,
                "overlap": round(overlap, 2),
                "rho": round(rho, 2),
                "mean_jaccard": round(ss.mean_pairwise_jaccard, 4),
                "containment_pairs": ss.containment_pairs,
                "exterior_margin": round(prob.exterior_margin, 5),
                "m": m_leaves,
                "k": k_act,
                "d": d_feat,
                "eps": eps,
                "inst_idx": inst_idx,
                "method": method,
                "certified": cert,
                "false_certificate": false_cert,
                "steps": calls,
                "capped_steps": calls if cert else cap,
                "off_witness_pulls": off_w,
                "cert_ms": round(1e3 * cert_s, 2),
                "total_ms": round(1e3 * elapsed_s, 2),
            }
        )
    return rows


def summarize(dest: Path) -> None:
    runs = [json.loads(x) for x in (dest / "e1_phase_runs.jsonl").read_text().splitlines() if x.strip()]

    # 1. Main 4x4 phase diagram summary
    phase_rows: list[dict] = []
    main_runs = [r for r in runs if r["cohort"] == "main_m128_d8_eps03"]
    for ov in OVERLAPS:
        for rho in RHOS:
            cell = [r for r in main_runs if abs(r["overlap"] - ov) < 1e-6 and abs(r["rho"] - rho) < 1e-6]
            if not cell:
                continue
            os_med = float(np.median([r["capped_steps"] for r in cell if r["method"] == "opt_sep"]))
            box_med = float(np.median([r["capped_steps"] for r in cell if r["method"] == "enclosing_box_cd"]))
            for m in E1_METHODS:
                sub = [r for r in cell if r["method"] == m]
                if not sub:
                    continue
                st = np.array([float(r["capped_steps"]) for r in sub])
                med_s = float(np.median(st))
                phase_rows.append(
                    {
                        "overlap": ov,
                        "rho": rho,
                        "mean_jaccard": round(statistics.fmean(r["mean_jaccard"] for r in sub), 3),
                        "mean_exterior_margin": round(statistics.fmean(r["exterior_margin"] for r in sub), 4),
                        "method": m,
                        "runs": len(sub),
                        "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                        "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                        "median_steps": round(med_s, 1),
                        "q25_steps": round(float(np.percentile(st, 25)), 1),
                        "q75_steps": round(float(np.percentile(st, 75)), 1),
                        "ratio_vs_opt_sep": round(med_s / max(1.0, os_med), 4),
                        "speedup_vs_opt_sep": round(os_med / max(1.0, med_s), 2),
                        "speedup_vs_enclosing_box": round(box_med / max(1.0, med_s), 2),
                    }
                )
    with (dest / "summary_e1_phase.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(phase_rows[0].keys()))
        w.writeheader()
        w.writerows(phase_rows)

    # 2. Sensitivity cohorts summary (eps=0.01, M=256, d=4, d=16)
    sens_cohorts = sorted({r["cohort"] for r in runs if r["cohort"] != "main_m128_d8_eps03"})
    sens_rows: list[dict] = []
    for coh in sens_cohorts:
        c_runs = [r for r in runs if r["cohort"] == coh]
        combos = sorted({(r["overlap"], r["rho"]) for r in c_runs})
        for ov, rho in combos:
            cell = [r for r in c_runs if abs(r["overlap"] - ov) < 1e-6 and abs(r["rho"] - rho) < 1e-6]
            os_med = float(np.median([r["capped_steps"] for r in cell if r["method"] == "opt_sep"]))
            for m in sorted({r["method"] for r in cell}):
                sub = [r for r in cell if r["method"] == m]
                st = np.array([float(r["capped_steps"]) for r in sub])
                med_s = float(np.median(st))
                sens_rows.append(
                    {
                        "cohort": coh,
                        "overlap": ov,
                        "rho": rho,
                        "m": sub[0]["m"],
                        "d": sub[0]["d"],
                        "eps": sub[0]["eps"],
                        "method": m,
                        "runs": len(sub),
                        "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                        "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                        "median_steps": round(med_s, 1),
                        "speedup_vs_opt_sep": round(os_med / max(1.0, med_s), 2),
                    }
                )
    if sens_rows:
        with (dest / "summary_e1_sensitivity.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(sens_rows[0].keys()))
            w.writeheader()
            w.writerows(sens_rows)


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
    n_main = 2 if args.smoke else 20
    n_sens = 2 if args.smoke else 10

    tasks: list[tuple[str, float, float, int, int, int, float, int, tuple[str, ...]]] = []
    for ov in OVERLAPS:
        for rho in RHOS:
            for idx in range(n_main):
                tasks.append(("main_m128_d8_eps03", ov, rho, 128, 8, 8, MAIN_EPS, idx, E1_METHODS))

    sens_methods = ("opt_sep", "enclosing_box_cd", "gp_ucb_joint", "contrast_directed_joint", "multi_contrast_joint")
    # Sensitivity slices at corners + high-structure regime: (0,0), (0,0.9), (0.75,0), (0.75,0.9)
    for ov, rho in ((0.00, 0.00), (0.00, 0.90), (0.75, 0.00), (0.75, 0.90)):
        for idx in range(n_sens):
            tasks.append(("sens_eps01", ov, rho, 128, 8, 8, 0.010, idx, sens_methods))
            tasks.append(("sens_m256", ov, rho, 256, 8, 8, MAIN_EPS, idx, sens_methods))
            tasks.append(("sens_d4", ov, rho, 128, 8, 4, MAIN_EPS, idx, sens_methods))
            tasks.append(("sens_d16", ov, rho, 128, 8, 16, MAIN_EPS, idx, sens_methods))

    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        nested = list(ex.map(_run_e1_instance, tasks))
    all_runs = [r for grp in nested for r in grp]

    f_out = dest / "e1_phase_runs.jsonl"
    f_out.write_text("\n".join(json.dumps(r) for r in all_runs) + "\n")
    summarize(dest)

    manifest = {
        "suite": "v7_e1_phase_diagram",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "total_runs": len(all_runs),
        "sha256_runs": _sha256(f_out),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Completed E1 Phase Diagram in {manifest['elapsed_s']:.2f}s ({len(all_runs)} runs).")


if __name__ == "__main__":
    main()
