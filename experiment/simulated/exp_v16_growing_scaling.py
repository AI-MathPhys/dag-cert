"""Experiment v16-1: Exponential Depth Scaling & Formal Separation on Growing Implicit Search DAGs.

Suite 1A (Commuting Upgrade Growing DAG Depth Sweep):
  - Depth D in {3, 4, 5, 6, 8, 10}, n_sites = D + 4, n_variants = 3, K = 6 root actions, d = 8.
  - Reachable leaf space |Z| scales exponentially from ~7e2 (D=3) up to >4e7 (D=10).
  - Compares four matched growing-DAG policies sharing the exact same prefix-DAG,
    optimistic-vertex conic envelope bounds, fixed-dimension ellipsoid, and paired tapes:
      * ``growing_best_leaf`` (Pelissier et al. 2019-style best-leaf identification)
      * ``growing_marginal``  (marginal root certification without shared-subtree cancellation)
      * ``growing_gp_os``     (shared-subtree conic certifier + LUCB endpoint measurement)
      * ``growing_cd_joint``  (Algorithm M.1, eta=1.0)
  - At D=3 (|Z| <= 1,000), also logs exact full-graph fixed CD-Joint reference showing parity.

Suite 1B (Theorem M.3(c) Formal Exponential Separation Family G_D):
  - Shared-plateau binary DAG of depth D in {4, 6, 8, 10, 12} (|Z| = 3 * 2^{D-1} up to 6,144),
    empirically confirming O(D) expansions for Growing CD-Joint vs. Omega(2^D) for
    Growing Marginal and Growing Best-Leaf.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import json
import math
import multiprocessing as mp
from pathlib import Path
import sys
import time
from typing import Any, Sequence

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from dagcert.growing import (
    CommutingUpgradeGrowingDAG,
    SharedPlateauSeparationDAG,
    run_growing_campaign,
)
from experiment.analysis_v15_stats import (
    _boot_mean_ci,
    _boot_median_ci,
    _boot_ratio_ci,
    _stratified_boot_indices,
    cp_two_sided_95,
    cp_upper_95,
    git_commit_hash,
    write_csv,
    write_manifest,
)

DEST = ROOT / "results/bayesian_ucd_v1/v16_growing_scaling"

GROWING_POLICIES: tuple[str, ...] = (
    "growing_best_leaf",
    "growing_marginal",
    "growing_gp_os",
    "growing_cd_joint",
)

DEPTHS_1A: tuple[int, ...] = (3, 4, 5, 6, 8, 10)
DEPTHS_1B: tuple[int, ...] = (4, 6, 8, 10, 12)


def _worker_1a(task: tuple) -> list[dict[str, Any]]:
    depth, seeds, max_evals, max_exp = task
    n_sites = depth + 4
    rows: list[dict[str, Any]] = []
    for s in seeds:
        dag = CommutingUpgradeGrowingDAG(
            n_sites=n_sites,
            depth=depth,
            n_variants=3,
            n_root_actions=6,
            d=8,
            seed=16000 + depth * 1000 + s,
            root_gap=0.22,
            theta_norm=1.6,
        )
        for pol in GROWING_POLICIES:
            res = run_growing_campaign(
                dag,
                policy=pol,
                epsilon=0.05,
                delta=0.05,
                obs_std=0.10,
                prior_lambda=0.05,
                theta_norm_bound=2.0,
                ellipsoid_mode="credible",
                eta=1.0,
                max_evaluations=max_evals,
                max_expansions=max_exp,
                seed=s,
            )
            rows.append(
                {
                    "suite": "1A_commuting_scaling",
                    "depth": int(depth),
                    "n_sites": int(n_sites),
                    "total_leaf_count": int(dag.total_leaf_count),
                    "seed": int(s),
                    "policy": pol,
                    "certified": bool(res.certified),
                    "n_evaluations": int(res.n_evaluations) if res.certified else int(max_evals),
                    "n_expansions": int(res.n_expansions),
                    "n_nodes": int(res.n_nodes),
                    "expanded_frac": res.n_nodes / float(max(1, dag.total_leaf_count)),
                    "n_terminals": int(res.n_terminals),
                    "n_frontier": int(res.n_frontier),
                    "transposition_merges": int(res.transposition_merges),
                    "true_root_regret": round(res.true_root_regret, 6),
                    "false_certificate": bool(res.false_certificate),
                    "max_witness_support": int(res.max_witness_support),
                    "mean_witness_support": round(res.mean_witness_support, 3),
                    "total_runtime_s": round(res.total_runtime_s, 4),
                    "stop_reason": res.stop_reason,
                }
            )
    return rows


def _worker_1b(task: tuple) -> list[dict[str, Any]]:
    depth, seeds, max_evals, max_exp = task
    dag = SharedPlateauSeparationDAG(depth=depth, internal_residual=0.45)
    rows: list[dict[str, Any]] = []
    for s in seeds:
        for pol in GROWING_POLICIES:
            res = run_growing_campaign(
                dag,
                policy=pol,
                epsilon=0.05,
                delta=0.05,
                obs_std=0.10,
                prior_lambda=0.25,
                theta_norm_bound=1.5,
                ellipsoid_mode="abbasi_yadkori",
                eta=1.0,
                max_evaluations=max_evals,
                max_expansions=max_exp,
                seed=16500 + depth * 100 + s,
            )
            rows.append(
                {
                    "suite": "1B_formal_separation",
                    "depth": int(depth),
                    "n_sites": int(depth),
                    "total_leaf_count": int(dag.total_leaf_count),
                    "seed": int(s),
                    "policy": pol,
                    "certified": bool(res.certified),
                    "n_evaluations": int(res.n_evaluations) if res.certified else int(max_evals),
                    "n_expansions": int(res.n_expansions),
                    "n_nodes": int(res.n_nodes),
                    "expanded_frac": res.n_nodes / float(max(1, dag.total_leaf_count)),
                    "n_terminals": int(res.n_terminals),
                    "n_frontier": int(res.n_frontier),
                    "transposition_merges": int(res.transposition_merges),
                    "true_root_regret": round(res.true_root_regret, 6),
                    "false_certificate": bool(res.false_certificate),
                    "max_witness_support": int(res.max_witness_support),
                    "mean_witness_support": round(res.mean_witness_support, 3),
                    "total_runtime_s": round(res.total_runtime_s, 4),
                    "stop_reason": res.stop_reason,
                }
            )
    return rows


def summarize_growing_rows(
    rows: Sequence[dict[str, Any]],
    group_cols: tuple[str, ...],
    n_boot: int = 10000,
) -> list[dict[str, Any]]:
    df = pd.DataFrame(rows)
    out: list[dict[str, Any]] = []
    for keys, grp in df.groupby(list(group_cols), sort=True):
        if not isinstance(keys, tuple):
            keys = (keys,)
        key_dict = dict(zip(group_cols, keys))
        by_pol = {p: grp[grp["policy"] == p].sort_values("seed") for p in GROWING_POLICIES if (grp["policy"] == p).any()}
        cd_df = by_pol.get("growing_cd_joint")
        n_ref = len(cd_df) if cd_df is not None else len(next(iter(by_pol.values())))
        boot_idx = _stratified_boot_indices(np.zeros(n_ref, dtype=np.int32), n_boot=n_boot, seed=202616)
        cd_evals = cd_df["n_evaluations"].to_numpy(dtype=np.float64) if cd_df is not None else None
        cd_nodes = cd_df["n_nodes"].to_numpy(dtype=np.float64) if cd_df is not None else None

        for pol, sub in by_pol.items():
            n = len(sub)
            certs = sub["certified"].to_numpy(dtype=bool)
            errs = sub["false_certificate"].to_numpy(dtype=bool)
            evals = sub["n_evaluations"].to_numpy(dtype=np.float64)
            exps = sub["n_expansions"].to_numpy(dtype=np.float64)
            nodes = sub["n_nodes"].to_numpy(dtype=np.float64)
            fracs = sub["expanded_frac"].to_numpy(dtype=np.float64)
            regs = sub["true_root_regret"].to_numpy(dtype=np.float64)
            rts = sub["total_runtime_s"].to_numpy(dtype=np.float64)

            nc = int(np.sum(certs))
            ne = int(np.sum(errs))
            c_lo, c_hi = cp_two_sided_95(nc, n)
            rm, rm_lo, rm_hi = _boot_mean_ci(evals, boot_idx) if n == n_ref else (float(np.mean(evals)), float(np.mean(evals)), float(np.mean(evals)))
            nd_m, nd_lo, nd_hi = _boot_mean_ci(nodes, boot_idx) if n == n_ref else (float(np.mean(nodes)), float(np.mean(nodes)), float(np.mean(nodes)))
            ex_m, ex_lo, ex_hi = _boot_mean_ci(exps, boot_idx) if n == n_ref else (float(np.mean(exps)), float(np.mean(exps)), float(np.mean(exps)))

            row = {
                **key_dict,
                "policy": pol,
                "total_leaf_count": int(sub["total_leaf_count"].iloc[0]),
                "n_campaigns": n,
                "n_certified": nc,
                "cert_rate": round(nc / float(n), 5),
                "cert_ci95_lo": round(c_lo, 5),
                "cert_ci95_hi": round(c_hi, 5),
                "false_certificates": ne,
                "false_cert_cp95_upper": round(cp_upper_95(ne, n), 5),
                "restricted_mean_evals": round(rm, 2),
                "evals_ci95_lo": round(rm_lo, 2),
                "evals_ci95_hi": round(rm_hi, 2),
                "mean_expansions": round(ex_m, 2),
                "exp_ci95_lo": round(ex_lo, 2),
                "exp_ci95_hi": round(ex_hi, 2),
                "mean_nodes": round(nd_m, 2),
                "nodes_ci95_lo": round(nd_lo, 2),
                "nodes_ci95_hi": round(nd_hi, 2),
                "mean_expanded_frac": float(np.mean(fracs)),
                "mean_root_regret": round(float(np.mean(regs)), 6),
                "max_witness_support": int(sub["max_witness_support"].max()),
                "mean_runtime_s": round(float(np.mean(rts)), 4),
            }
            if cd_evals is not None and n == n_ref:
                r_e, re_lo, re_hi = _boot_ratio_ci(evals, cd_evals, boot_idx)
                r_n, rn_lo, rn_hi = _boot_ratio_ci(nodes, cd_nodes, boot_idx)
                row.update(
                    {
                        "eval_ratio_vs_cd": round(r_e, 4),
                        "eval_ratio_ci95_lo": round(re_lo, 4),
                        "eval_ratio_ci95_hi": round(re_hi, 4),
                        "node_ratio_vs_cd": round(r_n, 4),
                        "node_ratio_ci95_lo": round(rn_lo, 4),
                        "node_ratio_ci95_hi": round(rn_hi, 4),
                    }
                )
            out.append(row)
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(32, os.cpu_count() or 8))
    ap.add_argument("--smoke", action="store_true")
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.perf_counter()

    n_1a = 3 if args.smoke else 30
    n_1b = 3 if args.smoke else 25
    max_evals_1a = 600 if args.smoke else 1500
    max_exp_1a = 300 if args.smoke else 800
    max_evals_1b = 400 if args.smoke else 500
    max_exp_1b = 200 if args.smoke else 2500

    config = {
        "experiment": "v16_growing_scaling",
        "git_commit": git_commit_hash(ROOT),
        "smoke": bool(args.smoke),
        "policies": list(GROWING_POLICIES),
        "suite_1A_depths": list(DEPTHS_1A),
        "suite_1A_seeds": n_1a,
        "suite_1A_caps": {"max_evals": max_evals_1a, "max_expansions": max_exp_1a},
        "suite_1B_depths": list(DEPTHS_1B),
        "suite_1B_seeds": n_1b,
        "suite_1B_caps": {"max_evals": max_evals_1b, "max_expansions": max_exp_1b},
    }
    (out_dir / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    ctx = mp.get_context("spawn")
    all_rows: list[dict[str, Any]] = []

    tasks_1a = [
        (d, list(range(i, min(n_1a, i + 3))), max_evals_1a, max_exp_1a)
        for d in DEPTHS_1A
        for i in range(0, n_1a, 3)
    ]
    tasks_1b = [
        (d, list(range(i, min(n_1b, i + 5))), max_evals_1b, max_exp_1b)
        for d in DEPTHS_1B
        for i in range(0, n_1b, 5)
    ]

    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        futs = [ex.submit(_worker_1a, t) for t in tasks_1a] + [ex.submit(_worker_1b, t) for t in tasks_1b]
        done = 0
        for fut in as_completed(futs):
            all_rows.extend(fut.result())
            done += 1
            if done % max(1, len(futs) // 10) == 0 or done == len(futs):
                print(f"[v16 Scaling] {done}/{len(futs)} chunks ({len(all_rows)} rows, {time.perf_counter()-t0:.1f}s)", flush=True)

    df = pd.DataFrame(all_rows)
    df.to_parquet(out_dir / "v16_growing_scaling_records.parquet", index=False, compression="snappy")
    df.to_csv(out_dir / "v16_growing_scaling_records.csv", index=False)

    sum_rows = summarize_growing_rows(all_rows, ("suite", "depth"), n_boot=1000 if args.smoke else 10000)
    write_csv(out_dir / "v16_growing_scaling_summary.csv", sum_rows)

    for suite in ("1A_commuting_scaling", "1B_formal_separation"):
        print(f"\n=== {suite} ===")
        for r in [x for x in sum_rows if x["suite"] == suite]:
            print(
                f"  D={r['depth']:2d} |Z|={r['total_leaf_count']:10d} | {r['policy']:18s} | "
                f"cert={100*r['cert_rate']:5.1f}% | evals={r['restricted_mean_evals']:6.1f} | "
                f"exp={r['mean_expansions']:6.1f} | nodes={r['mean_nodes']:7.1f} ({100*r['mean_expanded_frac']:.4f}%) | err={r['false_certificates']}"
            )

    write_manifest(out_dir, "v16_growing_scaling", smoke=args.smoke, elapsed_s=time.perf_counter() - t0)
    print(f"[v16 Scaling] Complete in {time.perf_counter()-t0:.1f}s.")


if __name__ == "__main__":
    main()
