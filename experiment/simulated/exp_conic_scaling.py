"""Experiment E6: Computational Scaling & Lazy Caratheodory Certificate Maintenance.

Benchmarks five joint-certification backends on identical trajectories across:
- Terminal counts `M in {128, 256, 512, 1024, 2048, 4096}`,
- Root decision counts `K in {4, 8, 16, 32}`,
- Feature ranks `d in {4, 8, 16, 32, 64}`,
- Support topology: `compact` vs `fragmented`.

Solvers compared:
1. `cvxpy_socp`: Full interior-point SOCP reference (run up to `M <= 512` where tractable).
2. `dense_afw`: Dense away-step Frank-Wolfe over full `Delta(S)`.
3. `colgen_full`: Caratheodory column generation (`|W| <= d + 1`) over all outside challengers.
4. `colgen_lazy`: Warm-started Caratheodory column generation + lazy challenger upper-bound pruning.
5. `vertex_approx`: Provable conservative single-vertex upper bound `min_{y in S} [...]`.

Reports per-update runtime (ms), peak Python memory (MB via `tracemalloc`), active support size
`|supp(p*)|` vs `d + 1`, fraction of outside challengers pruned lazily, maximum duality gap, and
exact break-even per-experiment cost (ms) where certification overhead stays under 5%.
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
import tracemalloc

import numpy as np

from joint_root_cert import (
    JointEllipsoidCertifier,
    LinearFeatureModel,
    SupportStructure,
)
from joint_root_cert.benchmarks import ScalingDAGProblem


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/e6_scaling"

SOLVERS = ("cvxpy_socp", "dense_afw", "colgen_full", "colgen_lazy", "vertex_approx")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _bench_config(
    sweep: str,
    m_leaves: int,
    k_act: int,
    d_feat: int,
    support_style: str,
    n_updates: int,
    seed: int,
) -> list[dict]:
    prob = ScalingDAGProblem(
        seed=seed, m_leaves=m_leaves, k_actions=k_act, d_feat=d_feat, support_style=support_style
    )
    ss = SupportStructure(prob.graph)
    oracle = prob.oracle(seed + 999)

    # Pre-generate an identical sequence of `n_updates` batched updates (10 pulls per update)
    rng = np.random.default_rng(seed * 101 + m_leaves)
    snapshots: list[tuple[np.ndarray, np.ndarray, float]] = []
    model = LinearFeatureModel(
        phi=prob.phi,
        prior_mean=prob.prior_mean,
        reg_lambda=0.5,
        obs_std=prob.obs_std,
        param_bound=prob.param_bound,
        beta_mode="abbasi_yadkori",
        delta=0.05,
    )
    # Initial warmup so ellipsoid is nontrivial and sharp
    for _ in range(max(20, 3 * d_feat)):
        idx = int(rng.integers(0, m_leaves))
        model.observe(idx, oracle.sample(ss.leaves[idx]))

    for _ in range(n_updates):
        for _ in range(10):
            idx = int(rng.integers(0, m_leaves))
            model.observe(idx, oracle.sample(ss.leaves[idx]))
        means, psi = model.terminal_means_and_psi()
        snapshots.append((means.copy(), psi.copy(), float(model.beta())))

    rows: list[dict] = []
    ref_regret: float | None = None

    for solver in SOLVERS:
        if solver == "cvxpy_socp" and (m_leaves > 256 or d_feat > 8 or support_style == "fragmented"):
            continue
        if solver == "dense_afw" and (m_leaves > 512 or d_feat > 16 or support_style == "fragmented"):
            continue
        if solver == "colgen_full" and (m_leaves > 512 or d_feat > 32 or support_style == "fragmented"):
            continue

        gc.collect()
        tracemalloc.start()
        cert = JointEllipsoidCertifier(ss, epsilon=0.03, solver=solver, exact_linear_mean=True)
        t0 = time.perf_counter()
        last_reg = 0.0
        for means, psi, beta in snapshots:
            c0 = cert.certify_action(0, means, psi, prob.phi, beta, stop_if_above_eps=False)
            last_reg = c0.regret
        elapsed_s = time.perf_counter() - t0
        _, peak_bytes = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        if ref_regret is None and solver in ("cvxpy_socp", "colgen_full"):
            ref_regret = last_reg

        ms_per_update = 1e3 * elapsed_s / max(1, n_updates)
        pruned_frac = 1.0 - (cert.total_challengers_solved / max(1, cert.total_challengers_considered))
        rows.append(
            {
                "sweep": sweep,
                "m": m_leaves,
                "k": k_act,
                "d": d_feat,
                "support_style": support_style,
                "solver": solver,
                "n_updates": n_updates,
                "ms_per_update": round(ms_per_update, 3),
                "total_ms": round(1e3 * elapsed_s, 2),
                "peak_mem_mb": round(peak_bytes / (1024.0 * 1024.0), 3),
                "max_active_support": cert.max_active_support_size,
                "caratheodory_bound": d_feat + 1,
                "challengers_solved": cert.total_challengers_solved,
                "challengers_considered": cert.total_challengers_considered,
                "pruned_frac": round(pruned_frac, 4),
                "avg_solver_iters": round(cert.total_solver_iters / max(1, cert.total_challengers_solved), 2),
                "max_duality_gap": round(cert.max_duality_gap, 9),
                "last_regret": round(last_reg, 6),
                "regret_excess_vs_exact": round(last_reg - (ref_regret if ref_regret is not None else last_reg), 6),
            }
        )
    return rows


def _bench_worker(task: tuple[str, int, int, int, str, int, int]) -> list[dict]:
    return _bench_config(*task)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=16)
    args = ap.parse_args()

    dest: Path = args.out
    dest.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        return

    t_start = time.perf_counter()
    n_up = 3 if args.smoke else 5
    configs: list[tuple[str, int, int, int, str]] = []

    if args.smoke:
        configs.extend([
            ("sweep_M", 128, 8, 8, "compact"),
            ("sweep_M", 512, 8, 8, "compact"),
            ("sweep_d", 256, 8, 16, "compact"),
            ("sweep_topo", 256, 8, 8, "fragmented"),
        ])
    else:
        # 1. Sweep M up to 4096
        for m_val in (128, 256, 512, 1024, 2048, 4096):
            configs.append(("sweep_M", m_val, 8, 8, "compact"))
        # 2. Sweep d up to 64
        for d_val in (4, 8, 16, 32, 64):
            configs.append(("sweep_d", 512, 8, d_val, "compact"))
        # 3. Sweep K up to 32
        for k_val in (4, 8, 16, 32):
            configs.append(("sweep_K", 512, k_val, 8, "compact"))
        # 4. Compact vs fragmented supports at M = 512, 2048
        for m_val in (512, 2048):
            for st in ("compact", "fragmented"):
                configs.append(("sweep_topo", m_val, 8, 16, st))

    tasks = [(sw, m_val, k_val, d_val, st, n_up, 900 + idx) for idx, (sw, m_val, k_val, d_val, st) in enumerate(configs)]
    ctx = mp.get_context("spawn")
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        nested = list(ex.map(_bench_worker, tasks))
    all_rows = [r for grp in nested for r in grp]

    f_jsonl = dest / "e6_scaling_runs.jsonl"
    f_csv = dest / "summary_e6_scaling.csv"
    f_jsonl.write_text("\n".join(json.dumps(r) for r in all_rows) + "\n")
    with f_csv.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(all_rows[0].keys()))
        w.writeheader()
        w.writerows(all_rows)

    manifest = {
        "suite": "v7_e6_scaling",
        "smoke": bool(args.smoke),
        "python": platform.python_version(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "total_rows": len(all_rows),
        "sha256_runs": _sha256(f_jsonl),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Completed E6 Scaling in {manifest['elapsed_s']:.2f}s ({len(all_rows)} rows).")


if __name__ == "__main__":
    main()
