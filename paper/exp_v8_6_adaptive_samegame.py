"""Experiment v8-6 (P2): Hard-Regime Adaptive Sampling on Mid-Game SameGame, Tied-Star, Decoy-16, & Hetero-256.

Evaluates whether adaptive hard-regime sampling (`Adaptive-OS-LCB` and `KL-Info-Hybrid`)
bridges the tradeoff between:
  - `Optimistic-Separation` (excels on tied-optima exterior-margin regimes like Tied-Star eps=0),
  - `Safeguarded-LCB` / `LCB-fast` (excels on decoy/heterogeneous inside-ambiguity traps), and
  - `Exact-Regret-DAG-LUCB` / `VarDE-Exact` (best on narrow-gap 15x15 mid-game SameGame boards).

Benchmarks (matched Empirical Bernstein `delta=0.05` confidence intervals, paired reward tapes):
  1. Part A — Mid-Game 15x15 SameGame (`StandardTestset.txt` boards 1..20, `tile_cap=62, d=4, eps=0.025`,
     1.8s / 60,000 cap, stratified into the 19 strictly zero-containment boards vs 1 containment board,
     3 paired seeds per board = 57 zero-containment runs/method).
  2. Part B — Non-Containment Tied-Star (`N=8, Gamma=g=0.25`) across `eps in {0.05, 0.02, 0.01, 0.00}`
     (16 seeds/cell) verifying exact `eps=0` certification preservation!
  3. Part C — Decoy-16 & Hetero-256 inside-witness stress tests (16 seeds each).
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from concurrent.futures import ProcessPoolExecutor
import csv
import gc
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import platform
import time

import numpy as np

from dag_mcts.v4_baselines import (
    VarDEDAGSession,
    samegame_midgame_case,
)
from dag_mcts.v5_hybrid_and_os import (
    HybridWitnessDAGLUCBSession,
    noncontainment_star_dag,
)
from dag_mcts.v8_unified_experiments import AdaptiveHardRegimeSession
from paper.exp_inside_witness import (
    _decoy_trap_dag,
    _heterogeneous_support_dag,
)


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/bayesian_ucd_v1/v8_exp6_adaptive_samegame"

METHODS = (
    "exact_dag_lucb",
    "lcb_fast",
    "safeguarded_lcb",
    "opt_sep",
    "varde_exact",
    "adaptive_os_lcb",
    "kl_info_hybrid",
)
DELTA = 0.05
STAR_EPS = (0.05, 0.02, 0.01, 0.00)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _make_session(prob, eps: float, seed: int, method: str):
    if method == "exact_dag_lucb":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="ucb", delta=DELTA, schedule="emp_bernstein")
    if method == "lcb_fast":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="lcb_fast", delta=DELTA, schedule="emp_bernstein")
    if method == "safeguarded_lcb":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="hybrid", delta=DELTA, schedule="emp_bernstein")
    if method == "opt_sep":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=DELTA, schedule="emp_bernstein")
    if method == "varde_exact":
        return VarDEDAGSession(prob, seed, eps, delta=DELTA, schedule="emp_bernstein", witness_mode="exact")
    if method in ("adaptive_os_lcb", "kl_info_hybrid"):
        return AdaptiveHardRegimeSession(prob, seed, eps, mode=method, delta=DELTA, schedule="emp_bernstein")
    raise ValueError(method)


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    return sess.evidence.conflict


def _run_all_methods(prob, eps: float, seed: int, cap: int, wall_limit: float, meta: dict) -> list[dict]:
    vals = prob.graph.optimal_values(prob.means)
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in prob.graph.children[prob.graph.root]]

    rows: list[dict] = []
    for method in METHODS:
        gc.collect()
        t0 = time.perf_counter()
        sess = _make_session(prob, eps, seed, method)
        while not sess.certified and not _has_conflict(sess) and sess.calls < cap and (time.perf_counter() - t0) < wall_limit:
            sess.step()
        elapsed_s = time.perf_counter() - t0
        cert = bool(sess.certified)
        act = int(sess.action)
        calls = int(sess.calls)
        true_reg = regrets[act]
        # Allow tiny Monte Carlo reference-mean sampling tolerance (0.004) only on SameGame ref_samples
        reg_tol = 0.005 if meta["suite"] == "midgame_samegame" else 1e-12
        fc = bool(cert and true_reg > eps + reg_tol)
        if meta["suite"] != "midgame_samegame":
            assert not fc, f"False cert in {method} on {meta}: reg={true_reg} > eps={eps}"
        rows.append(
            {
                **meta,
                "seed": seed,
                "eps": eps,
                "method": method,
                "certified": cert,
                "false_certificate": fc,
                "steps": calls,
                "capped_steps": calls if cert else cap,
                "wall_ms": round(1e3 * elapsed_s, 2),
                "capped_wall_ms": round(1e3 * (elapsed_s if cert else wall_limit), 2),
                "final_regret": round(true_reg, 6),
            }
        )
    return rows


def _samegame_board_worker(task: tuple[int, list[int], int, float, int]) -> list[dict]:
    board_idx, seeds, cap, wall_lim, ref_s = task
    prob, ep, diag = samegame_midgame_case(board_idx, depth=4, tile_cap=62, eps=0.025, ref_samples=ref_s)
    zc = bool(diag.get("containment_pairs", 0) == 0)
    meta = {
        "suite": "midgame_samegame",
        "instance": f"mid_{board_idx:02d}_d4",
        "zero_containment": zc,
        "m_leaves": len(prob.graph.leaves),
    }
    rows: list[dict] = []
    for s in seeds:
        rows.extend(_run_all_methods(prob, ep, s, cap=cap, wall_limit=wall_lim, meta=meta))
    return rows


def _synthetic_hard_worker(task: tuple[str, float, list[int], int, float]) -> list[dict]:
    suite, eps, seeds, cap, wall_lim = task
    rows: list[dict] = []
    for s in seeds:
        if suite == "tied_star":
            prob, _ = noncontainment_star_dag(n_rivals=8, gap=0.25, eps=eps)
            ep = eps
            meta = {"suite": "tied_star", "instance": f"star_eps{eps:.2f}", "zero_containment": True, "m_leaves": len(prob.graph.leaves)}
        elif suite == "decoy_16":
            prob, ep = _decoy_trap_dag(16, 4, s)
            meta = {"suite": "decoy_16", "instance": "decoy_16", "zero_containment": True, "m_leaves": len(prob.graph.leaves)}
        else:
            prob, ep = _heterogeneous_support_dag(256, 16, s)
            meta = {"suite": "hetero_256", "instance": "hetero_256", "zero_containment": True, "m_leaves": len(prob.graph.leaves)}
        rows.extend(_run_all_methods(prob, ep, s, cap=cap, wall_limit=wall_lim, meta=meta))
    return rows


def summarize(dest: Path) -> None:
    path = dest / "v8_exp6_runs.jsonl"
    if not path.exists():
        return
    runs = [json.loads(x) for x in path.read_text().splitlines() if x.strip()]
    out_rows: list[dict] = []

    groups: list[tuple[str, list[dict]]] = [
        ("midgame_samegame_19zc", [r for r in runs if r["suite"] == "midgame_samegame" and r["zero_containment"]]),
        ("midgame_samegame_all20", [r for r in runs if r["suite"] == "midgame_samegame"]),
        ("decoy_16", [r for r in runs if r["suite"] == "decoy_16"]),
        ("hetero_256", [r for r in runs if r["suite"] == "hetero_256"]),
    ]
    for ep in sorted({r["eps"] for r in runs if r["suite"] == "tied_star"}):
        groups.append((f"tied_star_eps{ep:.2f}", [r for r in runs if r["suite"] == "tied_star" and abs(r["eps"] - ep) < 1e-9]))

    for g_name, g_runs in groups:
        if not g_runs:
            continue
        edl_med = float(np.median([r["capped_steps"] for r in g_runs if r["method"] == "exact_dag_lucb"]))
        for meth in METHODS:
            sub = [r for r in g_runs if r["method"] == meth]
            if not sub:
                continue
            n = len(sub)
            st = np.array([float(r["capped_steps"]) for r in sub])
            wm = np.array([float(r["capped_wall_ms"]) for r in sub])
            out_rows.append(
                {
                    "group": g_name,
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": sum(1 for r in sub if r["false_certificate"]),
                    "med_steps": round(float(np.median(st)), 1),
                    "mean_steps": round(float(np.mean(st)), 1),
                    "q25_steps": round(float(np.percentile(st, 25)), 1),
                    "q75_steps": round(float(np.percentile(st, 75)), 1),
                    "speedup_vs_edl": round(edl_med / max(1.0, float(np.median(st))), 3),
                    "med_wall_ms": round(float(np.median(wm)), 2),
                }
            )
    with (dest / "v8_exp6_summary.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(out_rows[0].keys()))
        w.writeheader()
        w.writerows(out_rows)

    print("\n=== v8 Exp 6: Hard-Regime Adaptive Sampling Summary ===")
    for r in out_rows:
        print(
            f"  {r['group']:23s} | {r['method']:16s} | cert={100*r['cert_rate']:5.1f}% "
            f"med={r['med_steps']:7.1f} ({r['speedup_vs_edl']:4.2f}x) wall={r['med_wall_ms']:6.1f}ms"
        )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(16, max(1, os.cpu_count() or 4)))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    if args.smoke:
        boards = [6, 7]
        sg_seeds = [691001]
        sg_cap, sg_wall, ref_s = 12000, 0.6, 512
        star_eps = (0.05, 0.00)
        syn_seeds = [710001, 710002]
        syn_cap, syn_wall = 15000, 0.6
    else:
        boards = list(range(1, 21))
        sg_seeds = [691000, 691100, 691200]  # 3 seeds/board -> 57 zero-containment runs/method
        sg_cap, sg_wall, ref_s = 60000, 1.8, 8192
        star_eps = STAR_EPS
        syn_seeds = list(range(710001, 710017))  # 16 seeds/cell
        syn_cap, syn_wall = 40000, 1.8

    ctx = mp.get_context("spawn")
    sg_tasks = [(b, [s + b for s in sg_seeds], sg_cap, sg_wall, ref_s) for b in boards]
    syn_tasks = []
    for ep in star_eps:
        for i in range(0, len(syn_seeds), 4):
            syn_tasks.append(("tied_star", ep, syn_seeds[i : i + 4], syn_cap, syn_wall))
    for suite in ("decoy_16", "hetero_256"):
        for i in range(0, len(syn_seeds), 4):
            syn_tasks.append((suite, 0.05, syn_seeds[i : i + 4], syn_cap, syn_wall))

    print(f"[v8 Exp 6] Running {len(sg_tasks)} SameGame board tasks + {len(syn_tasks)} hard synthetic tasks...", flush=True)
    rows: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_samegame_board_worker, sg_tasks):
            rows.extend(ch)
        for ch in ex.map(_synthetic_hard_worker, syn_tasks):
            rows.extend(ch)

    (out_dir / "v8_exp6_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows) + "\n")
    summarize(out_dir)
    artifacts = ["v8_exp6_runs.jsonl", "v8_exp6_summary.csv"]
    manifest = {
        "experiment": "v8_exp6_adaptive_samegame",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v8 Exp 6] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
