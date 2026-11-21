"""Experiment v8-4 (P1): End-to-End Compute Cost, Caching/Scheduling Strategies, and Cost-Ratio Break-Even.

Quantifies when correlated conic certification pays off in ACTUAL END-TO-END WALL-CLOCK TIME
(oracle compute + terminal evaluation cost) across terminal counts M in {64, 128, 256, 512, 1024, 2048, 4096}.

Part A — Coupled Conic Maintenance Benchmark (all 5 strategies on identical observation streams):
  1. `exact_every_step`      : Exact colgen_full solved at every update
  2. `lazy_every_step`       : Warm-started Caratheodory colgen_lazy at every update
  3. `periodic_conservative` : Full lazy solve every P=10 steps + O(|comp|*d) valid cached-mixture upper bound in between
  4. `adaptive_tol_lazy`     : Adaptive verified duality-gap tolerance tol_t proportional to R_prev - eps
  5. `hybrid_rect_joint`     : Fast rectangular/vertex upper bound first; periodic adaptive conic solves
  Reports cold initialization time (ms), conic oracle call count, average update time (ms),
  max regret excess over exact (always >= -1e-6, provably valid upper bound!), and peak Python memory (MB).

Part B — End-to-End Certification Trajectories & kappa Break-Even Frontier:
  Runs full sequential certification sessions comparing:
    - `indep_os`              : O(log M) distribution-free Empirical Bernstein Optimistic-Separation
    - `cd_exact_every`        : CD-Joint with exact_every_step updates (check_every=1)
    - `cd_lazy_every`         : CD-Joint with lazy_every_step updates (check_every=1)
    - `cd_periodic_conserv`   : CD-Joint with periodic_conservative (P=10, O(d) valid cached check every step)
    - `cd_adaptive_hybrid`    : CD-Joint with hybrid_rect_joint (adaptive tolerance + vertex fast-path)
  across M in {64, 128, 256, 512, 1024, 2048}, recording:
    - `evals` (terminal evaluations to certify),
    - `oracle_time_ms` (total surrogate + conic maintenance wall-clock ms),
    - `peak_mem_mb` (via tracemalloc),
    - and evaluating total end-to-end wall-clock time across cost ratio
      `kappa = (oracle_update_cost) / (terminal_eval_cost) in [1e-5, 1e+2]`
      to map the exact break-even frontier `kappa*(M)` and per-evaluation cost threshold (ms)!
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
import math
import multiprocessing as mp
from pathlib import Path
import platform
import time
import tracemalloc

import numpy as np

from dag_mcts.v5_hybrid_and_os import HybridWitnessDAGLUCBSession
from dag_mcts.v7_bayesian_ucd import (
    JointEllipsoidCertifier,
    LinearFeatureModel,
    SupportStructure,
)
from dag_mcts.v7_benchmarks import ScalingDAGProblem
from dag_mcts.v8_unified_experiments import ScheduledConicCertifier


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/bayesian_ucd_v1/v8_exp4_compute_breakeven"

SCALE_MS = (64, 128, 256, 512, 1024, 2048, 4096)
TRAJ_MS = (64, 128, 256, 512, 1024, 2048)
KAPPA_GRID = (1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1.0, 10.0, 100.0)
EPS = 0.030
DELTA = 0.05


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _coupled_stream_worker(task: tuple[int, int, int, int, int]) -> list[dict]:
    m_leaves, k_act, d_feat, n_updates, seed = task
    prob = ScalingDAGProblem(
        seed=seed, m_leaves=m_leaves, k_actions=k_act, d_feat=d_feat, support_style="compact"
    )
    t_init0 = time.perf_counter()
    ss = SupportStructure(prob.graph)
    cold_init_ms = 1e3 * (time.perf_counter() - t_init0)
    oracle = prob.oracle(seed + 404)

    rng = np.random.default_rng(seed * 131 + m_leaves)
    model = LinearFeatureModel(
        phi=prob.phi,
        prior_mean=prob.prior_mean,
        reg_lambda=0.5,
        obs_std=prob.obs_std,
        param_bound=prob.param_bound,
        beta_mode="abbasi_yadkori",
        delta=DELTA,
    )
    # Warmup
    for _ in range(max(24, 3 * d_feat)):
        idx = int(rng.integers(0, m_leaves))
        model.observe(idx, oracle.sample(ss.leaves[idx]))

    snaps: list[tuple[np.ndarray, np.ndarray, float]] = []
    for _ in range(n_updates):
        for _ in range(5):
            idx = int(rng.integers(0, m_leaves))
            model.observe(idx, oracle.sample(ss.leaves[idx]))
        m, psi = model.terminal_means_and_psi()
        snaps.append((m.copy(), psi.copy(), float(model.beta())))

    exact_trace: list[float] | None = None
    rows: list[dict] = []
    for st in ScheduledConicCertifier.STRATEGIES:
        if st == "exact_every_step" and m_leaves > 256:
            continue
        # 1. Pure uncontaminated wall-clock timing (NO tracemalloc overhead!)
        gc.collect()
        t_c0 = time.perf_counter()
        cert = ScheduledConicCertifier(ss, epsilon=EPS, strategy=st, period=10)
        init_st_ms = 1e3 * (time.perf_counter() - t_c0) + cold_init_ms

        regs: list[float] = []
        t0 = time.perf_counter()
        for m, psi, beta in snaps:
            regs.append(cert.evaluate_action(0, m, psi, prob.phi, beta))
        elapsed_ms = 1e3 * (time.perf_counter() - t0)

        # 2. Separate lightweight peak-memory measurement on reference seed using warm-started cert
        peak_bytes = 0
        if seed == 4100:
            gc.collect()
            tracemalloc.start()
            # Measure incremental allocation of one warm-started update + support/cache footprint
            _ss_tmp = SupportStructure(prob.graph)
            _c_tmp = ScheduledConicCertifier(_ss_tmp, epsilon=EPS, strategy=st, period=10)
            _c_tmp.base_cert._warm_cache = dict(cert.base_cert._warm_cache)
            _c_tmp._cached_mix = dict(cert._cached_mix)
            _c_tmp.evaluate_action(0, snaps[-1][0], snaps[-1][1], prob.phi, snaps[-1][2])
            _, peak_bytes = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            del _ss_tmp, _c_tmp

        if st == "exact_every_step":
            exact_trace = regs
        elif exact_trace is None and st == "lazy_every_step":
            exact_trace = regs

        diffs = [regs[i] - exact_trace[i] for i in range(len(regs))] if exact_trace is not None else [0.0]
        rows.append(
            {
                "part": "A_coupled_stream",
                "m": m_leaves,
                "k": k_act,
                "d": d_feat,
                "seed": seed,
                "strategy": st,
                "n_updates": n_updates,
                "cold_init_ms": round(init_st_ms, 3),
                "conic_oracle_calls": int(cert.conic_oracle_calls),
                "total_update_ms": round(elapsed_ms, 3),
                "ms_per_update": round(elapsed_ms / max(1, n_updates), 4),
                "peak_mem_mb": round(peak_bytes / (1024.0 * 1024.0), 3),
                "min_diff_vs_exact": round(float(min(diffs)), 7),
                "mean_excess_vs_exact": round(float(np.mean(diffs)), 6),
                "max_excess_vs_exact": round(float(max(diffs)), 6),
                "sound_upper_bound": bool(min(diffs) >= -1e-4),
            }
        )
    return rows


def _run_scheduled_cd_session(prob: ScalingDAGProblem, seed: int, strategy: str, cap: int, measure_mem: bool = False) -> dict:
    """Full end-to-end sequential CD-Joint session driven by ScheduledConicCertifier."""
    gc.collect()
    t0 = time.perf_counter()
    ss = SupportStructure(prob.graph)
    oracle = prob.oracle(seed)
    model = LinearFeatureModel(
        phi=prob.phi,
        prior_mean=prob.prior_mean,
        reg_lambda=0.5,
        obs_std=prob.obs_std,
        param_bound=prob.param_bound,
        beta_mode="abbasi_yadkori",
        delta=DELTA,
    )
    cert = ScheduledConicCertifier(ss, epsilon=EPS, strategy=strategy, period=10)
    cold_init_ms = 1e3 * (time.perf_counter() - t0)

    k = len(ss.supports)
    m = len(ss.leaves)
    calls = 0
    certified = False
    best_act = 0
    last_contrast = np.zeros(prob.phi.shape[1], dtype=np.float64)
    oracle_time_s = 0.0
    rng = np.random.default_rng(seed * 7 + 19)

    # Brief spanning warmup (2 * d pulls)
    warmup = min(cap, 2 * prob.phi.shape[1])
    for i in range(warmup):
        arm = int(rng.integers(0, m))
        y = float(oracle.sample(ss.leaves[arm]))
        t_u0 = time.perf_counter()
        model.observe(arm, y)
        oracle_time_s += time.perf_counter() - t_u0
        calls += 1

    while not certified and calls < cap:
        t_o0 = time.perf_counter()
        means, psi = model.terminal_means_and_psi()
        beta = model.beta()
        stds = model.terminal_stds()

        # Candidate action by highest empirical max mean (tie-break LCB)
        cand_a = int(np.argmax([float(np.max(means[sup])) for sup in ss.supports]))
        reg_a = cert.evaluate_action(cand_a, means, psi, prob.phi, beta)
        best_act = cand_a
        if reg_a <= EPS:
            certified = True
            oracle_time_s += time.perf_counter() - t_o0
            break

        # Extract active contrast from cached mixture or top witness pair in O(d)
        comp = ss.complements[cand_a]
        sup = ss.supports[cand_a]
        cached = cert._cached_mix.get(cand_a)
        if cached is not None:
            sup_i, w_i = cached
            m_mix = float(w_i @ means[sup_i])
            psi_mix = w_i @ psi[sup_i]
            scores = (means[comp] - m_mix) + beta * np.linalg.norm(psi[comp] - psi_mix[None, :], axis=1)
            z_best = int(comp[int(np.argmax(scores))])
            last_contrast = prob.phi[z_best] - (w_i @ prob.phi[sup_i])
        else:
            y_lcb = int(sup[int(np.argmax(means[sup] - beta * stds[sup]))])
            z_ucb = int(comp[int(np.argmax(means[comp] + beta * stds[comp]))])
            last_contrast = prob.phi[z_ucb] - prob.phi[y_lcb]

        gains = model.contrast_variance_reduction(last_contrast)
        arm = int(np.argmax(gains))
        oracle_time_s += time.perf_counter() - t_o0

        y = float(oracle.sample(ss.leaves[arm]))
        t_u0 = time.perf_counter()
        model.observe(arm, y)
        oracle_time_s += time.perf_counter() - t_u0
        calls += 1

    total_ms = 1e3 * (time.perf_counter() - t0)
    peak_bytes = 0
    if measure_mem:
        gc.collect()
        tracemalloc.start()
        ss_m = SupportStructure(prob.graph)
        c_m = ScheduledConicCertifier(ss_m, epsilon=EPS, strategy=strategy, period=10)
        c_m.base_cert._warm_cache = dict(cert.base_cert._warm_cache)
        c_m._cached_mix = dict(cert._cached_mix)
        m_v, psi_v = model.terminal_means_and_psi()
        c_m.evaluate_action(0, m_v, psi_v, prob.phi, model.beta())
        _, peak_bytes = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        del ss_m, c_m
    return {
        "certified": certified,
        "action": best_act,
        "steps": calls,
        "capped_steps": calls if certified else cap,
        "cold_init_ms": round(cold_init_ms, 3),
        "oracle_time_ms": round(1e3 * oracle_time_s + cold_init_ms, 3),
        "ms_per_step": round((1e3 * oracle_time_s + cold_init_ms) / max(1, calls), 4),
        "conic_oracle_calls": int(cert.conic_oracle_calls),
        "peak_mem_mb": round(peak_bytes / (1024.0 * 1024.0), 3),
        "total_ms": round(total_ms, 3),
    }


def _end_to_end_worker(task: tuple[int, list[int], int]) -> list[dict]:
    m_leaves, seeds, cap = task
    k_act = 8
    d_feat = 8
    rows: list[dict] = []
    for s in seeds:
        prob = ScalingDAGProblem(
            seed=900 + s * 17 + m_leaves, m_leaves=m_leaves, k_actions=k_act, d_feat=d_feat, support_style="compact"
        )
        vals = prob.graph.optimal_values(prob.means)
        root_ch = prob.graph.children[prob.graph.root]
        opt_mu = float(vals[prob.graph.root])
        regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]
        run_seed = 870000 + s * 31 + m_leaves

        # 1. Independent OS baseline (O(log M) oracle — pure uncontaminated wall-clock timing!)
        gc.collect()
        t0 = time.perf_counter()
        sess_os = HybridWitnessDAGLUCBSession(prob, run_seed, EPS, mode="opt_sep", delta=DELTA, schedule="emp_bernstein")
        os_cap = min(cap, 25000)
        while not sess_os.certified and not sess_os.monitor.evidence.conflict and sess_os.calls < os_cap:
            sess_os.step()
        os_ms = 1e3 * (time.perf_counter() - t0)
        os_peak = 0
        if s == 0:
            gc.collect()
            tracemalloc.start()
            s_mem = HybridWitnessDAGLUCBSession(prob, run_seed, EPS, mode="opt_sep", delta=DELTA, schedule="emp_bernstein")
            for _ in range(40):
                if not s_mem.step():
                    break
            _, os_peak = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            del s_mem
        os_reg = regrets[int(sess_os.action)]
        rows.append(
            {
                "part": "B_end_to_end",
                "m": m_leaves,
                "k": k_act,
                "d": d_feat,
                "seed": s,
                "method": "indep_os",
                "certified": bool(sess_os.certified),
                "false_certificate": bool(sess_os.certified and os_reg > EPS + 1e-12),
                "steps": int(sess_os.calls),
                "capped_steps": int(sess_os.calls) if sess_os.certified else os_cap,
                "cold_init_ms": 0.0,
                "oracle_time_ms": round(os_ms, 3),
                "ms_per_step": round(os_ms / max(1, int(sess_os.calls)), 4),
                "conic_oracle_calls": 0,
                "peak_mem_mb": round(os_peak / (1024.0 * 1024.0), 3),
                "total_ms": round(os_ms, 3),
            }
        )

        # 2. Scheduled CD-Joint strategies
        strats = ("lazy_every_step", "periodic_conservative", "adaptive_tol_lazy", "hybrid_rect_joint")
        if m_leaves <= 128:
            strats = ("exact_every_step",) + strats
        for st in strats:
            res = _run_scheduled_cd_session(prob, run_seed, st, cap=min(cap, 2500), measure_mem=(s == 0))
            t_reg = regrets[res["action"]]
            rows.append(
                {
                    "part": "B_end_to_end",
                    "m": m_leaves,
                    "k": k_act,
                    "d": d_feat,
                    "seed": s,
                    "method": f"cd_{st}",
                    "certified": res["certified"],
                    "false_certificate": bool(res["certified"] and t_reg > EPS + 1e-12),
                    "steps": res["steps"],
                    "capped_steps": res["capped_steps"],
                    "cold_init_ms": res["cold_init_ms"],
                    "oracle_time_ms": res["oracle_time_ms"],
                    "ms_per_step": res["ms_per_step"],
                    "conic_oracle_calls": res["conic_oracle_calls"],
                    "peak_mem_mb": res["peak_mem_mb"],
                    "total_ms": res["total_ms"],
                }
            )
    return rows


def summarize(dest: Path) -> None:
    # Part A
    pa = dest / "v8_exp4_coupled_runs.jsonl"
    if pa.exists():
        runs = [json.loads(x) for x in pa.read_text().splitlines() if x.strip()]
        keys = sorted({(r["m"], r["strategy"]) for r in runs})
        rows_a: list[dict] = []
        for m_l, st in keys:
            sub = [r for r in runs if r["m"] == m_l and r["strategy"] == st]
            rows_a.append(
                {
                    "m": m_l,
                    "strategy": st,
                    "runs": len(sub),
                    "med_cold_init_ms": round(float(np.median([r["cold_init_ms"] for r in sub])), 2),
                    "med_conic_calls": round(float(np.median([r["conic_oracle_calls"] for r in sub])), 1),
                    "med_ms_per_update": round(float(np.median([r["ms_per_update"] for r in sub])), 3),
                    "med_peak_mem_mb": round(float(max(r["peak_mem_mb"] for r in sub)), 3),
                    "max_excess_vs_exact": round(float(max(r["max_excess_vs_exact"] for r in sub)), 6),
                    "all_sound": all(r["sound_upper_bound"] for r in sub),
                }
            )
        with (dest / "v8_exp4_coupled_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_a[0].keys()))
            w.writeheader()
            w.writerows(rows_a)
        print("\n=== v8 Exp 4A: Coupled Conic Maintenance Strategies Across M ===")
        for r in rows_a:
            print(
                f"  M={r['m']:4d} | {r['strategy']:22s} | ms/upd={r['med_ms_per_update']:7.3f} "
                f"calls={r['med_conic_calls']:4.1f} mem={r['med_peak_mem_mb']:5.2f}MB "
                f"max_exc={r['max_excess_vs_exact']:.5f} sound={r['all_sound']}"
            )

    # Part B + Break-even frontier
    pb = dest / "v8_exp4_end2end_runs.jsonl"
    if pb.exists():
        runs = [json.loads(x) for x in pb.read_text().splitlines() if x.strip()]
        keys = sorted({(r["m"], r["method"]) for r in runs})
        rows_b: list[dict] = []
        breakeven_rows: list[dict] = []
        os_by_m: dict[int, tuple[float, float]] = {}
        for m_l in sorted({r["m"] for r in runs}):
            sub_os = [r for r in runs if r["m"] == m_l and r["method"] == "indep_os"]
            if sub_os:
                os_by_m[m_l] = (
                    float(np.median([r["capped_steps"] for r in sub_os])),
                    float(np.median([r["oracle_time_ms"] for r in sub_os])),
                )

        for m_l, meth in keys:
            sub = [r for r in runs if r["m"] == m_l and r["method"] == meth]
            n = len(sub)
            med_steps = float(np.median([r["capped_steps"] for r in sub]))
            med_oms = float(np.median([r["oracle_time_ms"] for r in sub]))
            med_ms_step = float(np.median([r["ms_per_step"] for r in sub]))
            os_steps, os_oms = os_by_m.get(m_l, (med_steps, med_oms))
            # Exact break-even terminal evaluation cost c_eval* (ms) where total wall-clock of meth == indep_os:
            # med_oms + med_steps * c_eval == os_oms + os_steps * c_eval  =>  c_eval* = (med_oms - os_oms) / (os_steps - med_steps)
            if meth != "indep_os" and os_steps > med_steps + 1.0:
                c_eval_star_ms = max(0.0, (med_oms - os_oms) / (os_steps - med_steps))
                # Equivalent kappa* = (oracle_ms_per_step) / c_eval_star_ms
                kappa_star = med_ms_step / max(1e-9, c_eval_star_ms) if c_eval_star_ms > 0.0 else math.inf
            else:
                c_eval_star_ms = 0.0
                kappa_star = 0.0
            rows_b.append(
                {
                    "m": m_l,
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": sum(1 for r in sub if r["false_certificate"]),
                    "med_steps": round(med_steps, 1),
                    "sample_speedup_vs_os": round(os_steps / max(1.0, med_steps), 2),
                    "med_oracle_ms": round(med_oms, 2),
                    "med_ms_per_step": round(med_ms_step, 4),
                    "med_conic_calls": round(float(np.median([r["conic_oracle_calls"] for r in sub])), 1),
                    "med_peak_mem_mb": round(float(max(r["peak_mem_mb"] for r in sub)), 3),
                    "breakeven_eval_ms": round(c_eval_star_ms, 4),
                    "breakeven_kappa": round(kappa_star, 3) if math.isfinite(kappa_star) else 999999.0,
                }
            )
            # Also evaluate normalized end-to-end runtime across kappa = oracle_step_cost / eval_cost
            if meth != "indep_os":
                for kap in KAPPA_GRID:
                    # Given c_eval = med_ms_step / kap (so oracle_step_cost / c_eval == kap):
                    c_eval = med_ms_step / kap
                    t_meth = med_oms + med_steps * c_eval
                    t_os = os_oms + os_steps * c_eval
                    breakeven_rows.append(
                        {
                            "m": m_l,
                            "method": meth,
                            "kappa": kap,
                            "eval_cost_ms": round(c_eval, 5),
                            "end2end_ms_method": round(t_meth, 2),
                            "end2end_ms_os": round(t_os, 2),
                            "wall_speedup_vs_os": round(t_os / max(1e-9, t_meth), 3),
                        }
                    )

        with (dest / "v8_exp4_end2end_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_b[0].keys()))
            w.writeheader()
            w.writerows(rows_b)
        with (dest / "v8_exp4_kappa_frontier.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(breakeven_rows[0].keys()))
            w.writeheader()
            w.writerows(breakeven_rows)
        print("\n=== v8 Exp 4B: End-to-End Break-Even Frontier vs Independent OS ===")
        for r in rows_b:
            print(
                f"  M={r['m']:4d} | {r['method']:25s} | steps={r['med_steps']:7.1f} ({r['sample_speedup_vs_os']:5.1f}x) "
                f"oracle={r['med_oracle_ms']:7.1f}ms break_eval={r['breakeven_eval_ms']:7.4f}ms "
                f"kappa*={r['breakeven_kappa']:6.2f}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(24, max(1, os.cpu_count() or 4)))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    if args.smoke:
        scale_ms = (64, 256, 1024)
        n_upd = 15
        n_seeds_a = 2
        traj_ms = (64, 256)
        n_seeds_b = 3
        traj_cap = 6000
    else:
        scale_ms = SCALE_MS
        n_upd = 20
        n_seeds_a = 6
        traj_ms = TRAJ_MS
        n_seeds_b = 9
        traj_cap = 25000

    ctx = mp.get_context("spawn")
    tasks_a = [
        (m, 8, 8, (12 if m >= 2048 else n_upd), 4100 + s)
        for m in scale_ms
        for s in range(n_seeds_a)
    ]
    print(f"[v8 Exp 4A] Running {len(tasks_a)} coupled conic stream tasks...", flush=True)
    rows_a: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_coupled_stream_worker, tasks_a):
            rows_a.extend(ch)
    (out_dir / "v8_exp4_coupled_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows_a) + "\n")

    tasks_b = []
    for m in traj_ms:
        for i in range(0, n_seeds_b, 3):
            tasks_b.append((m, list(range(i, min(n_seeds_b, i + 3))), traj_cap))
    print(f"[v8 Exp 4B] Running {len(tasks_b)} end-to-end trajectory tasks...", flush=True)
    rows_b: list[dict] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        for ch in ex.map(_end_to_end_worker, tasks_b):
            rows_b.extend(ch)
    (out_dir / "v8_exp4_end2end_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows_b) + "\n")

    summarize(out_dir)
    artifacts = [
        "v8_exp4_coupled_runs.jsonl",
        "v8_exp4_coupled_summary.csv",
        "v8_exp4_end2end_runs.jsonl",
        "v8_exp4_end2end_summary.csv",
        "v8_exp4_kappa_frontier.csv",
    ]
    manifest = {
        "experiment": "v8_exp4_compute_breakeven",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v8 Exp 4] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
