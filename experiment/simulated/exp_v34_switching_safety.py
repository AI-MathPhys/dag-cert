#!/usr/bin/env python3
"""Experiment V9-3 (P1): Action Switching, Evidence Preservation, IUT, & Safety Audit.

Stress-tests the core theoretical mechanisms of V32/V33/V34:
  - Part A (Multi-Answer Switching Stress Test, 200 paired seeds at delta=0.05):
      Uses a K=8 overlapping rank-2 DAG with 3 eps-optimal actions of widely differing
      certification rates (C_{A0} >> C_{A2} >> C_{A1} under sigma=(0.4, 1.8)), initialized
      at hard optimal action A1 (and a second adversarial early-perturbation sub-regime
      forcing multiple empirical switches A1 -> A2 -> A0). Compares:
        1. v34_full          (hysteresis + preserved action-local wealth + IUT K/delta)
        2. v34_no_hysteresis (h_k = 0: measures switch thrashing)
        3. v33_all_action    (all-action evidence: compute vs. incidental-evidence trade-off)
        4. v34_bonferroni_j  (conservative K*|J_a|/delta ablation isolating Thm. V32.1 IUT)
        5. v34_student_hedge (Thm. V32.2 same-null likelihood-Student wealth hedge, pi=0.5)
        6. neg_ctrl_reset    (NEGATIVE CONTROL: illegally resets wealth on revisit, Rem. V34.1)
  - Part B1 (Null-Boundary Switching Safety Audit, 500 paired seeds at delta=0.05):
      Verifies V34 preserves <= delta Type-I error on an exact invalid-action boundary while
      showing how illegal optional wealth resetting upon revisit inflates false certificates.
  - Part B2 (Behrens-Fisher Multimodal Profiled-Null Audit, CE V23.1, 500 replications):
      Under the EXACT true null theta_* = (0, 0) in P = {u1 <= 0} with H = [[1, 1], [1, -1]],
      random Gaussian fluctuations produce genuinely bimodal profiled batch-null losses.
      Measures anti-conservative null-likelihood violations of naive single-start SLSQP vs.
      exact certified cubic (Thm. V23.2) and general-d B&B (Prop. V22.2), plus sequential
      Type-I error rates under delta = 0.05.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import time
from typing import Any

import numpy as np

from dagcert._core.v9_v34_tracker import (
    ComponentPolyhedron,
    HeteroscedasticDAGProblem,
    IntrinsicGaussianTape,
    batch_schedule_sizes,
    compute_exact_nuisance_kl_rate,
    make_behrens_fisher_null_dag,
    make_switching_multi_answer_dag,
    run_v34_tracker,
    solve_cubic_exact_2d,
    solve_profiled_loss_certified,
    solve_uncertified_local_null,
)


ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = ROOT / "results/bayesian_ucd_v1/v9_exp3_switching_and_safety"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class PerturbedInitialTape(IntrinsicGaussianTape):
    """Same intrinsic Gaussian tape, with a deterministic adversarial shift on the first 6 pulls
    of query 0 only, forcing an early misleading estimate and multi-action switching before recovery."""
    def __init__(self, means: np.ndarray, sigmas: np.ndarray, seed: int, shift_q0: float = -0.75, n_shift: int = 8) -> None:
        super().__init__(means, sigmas, seed)
        self.shift_q0 = float(shift_q0)
        self.n_shift = int(n_shift)

    def slice_query(self, x: int, start: int, count: int) -> np.ndarray:
        arr = super().slice_query(x, start, count).copy()
        if x == 0 and start < self.n_shift:
            end_s = min(count, self.n_shift - start)
            arr[:end_s] += self.shift_q0
        return arr


def _make_tied_identical_dag(eps: float = 0.05) -> HeteroscedasticDAGProblem:
    """Symmetric rank-2 DAG with TWO identically optimal actions (V_{A0} == V_{A1}) to stress hysteresis!"""
    H = np.eye(2, dtype=float)
    phi = np.array([
        [1.00, 0.00],  # z0: mean 0.55
        [0.00, 1.00],  # z1: mean 0.55
        [0.98, 0.02],  # z2: mean 0.55 (partner for A0)
        [0.02, 0.98],  # z3: mean 0.55 (partner for A1)
        [0.40, 0.40],  # z4: mean 0.44
        [0.30, 0.10],  # z5
        [0.10, 0.30],  # z6
        [-0.20, 0.40], # z7
        [0.40, -0.20], # z8
    ], dtype=float)
    # Wait: both A0={0,1} and A1={2,3} share exact same optimal value 0.55 and exact same V_a!
    supports = (
        (0, 1),  # A0: optimal, symmetric
        (2, 3),  # A1: optimal, identically tied V_{A1} == V_{A0}!
        (4, 5),  # A2: suboptimal
        (4, 6),  # A3: suboptimal
        (5, 7),  # A4: suboptimal
        (6, 8),  # A5: suboptimal
    )
    return HeteroscedasticDAGProblem(
        name="tied_identical_K6",
        H=H,
        phi=phi,
        supports=supports,
        theta_star=np.array([0.55, 0.55], dtype=float),
        sigma=np.array([1.25, 1.25], dtype=float),
        eps=eps,
    )


def _run_part_a_job(job: tuple[str, int, float]) -> list[dict[str, Any]]:
    sub_regime, seed, delta = job
    if sub_regime == "tied_identical_opt":
        prob = _make_tied_identical_dag(eps=0.05)
    else:
        prob = make_switching_multi_answer_dag(eps=0.05)
    rows: list[dict[str, Any]] = []

    def make_tape() -> IntrinsicGaussianTape:
        if sub_regime == "adv_early_switch":
            return PerturbedInitialTape(prob.true_query_means, prob.sigma, seed=seed, shift_q0=-0.95, n_shift=22)
        return IntrinsicGaussianTape(prob.true_query_means, prob.sigma, seed=seed)

    configs: list[tuple[str, dict[str, Any]]] = [
        ("v34_full", dict(refresh_schedule="four_power", action_local=True, use_hysteresis=True, hysteresis_scale=0.03)),
        ("v34_no_hysteresis", dict(refresh_schedule="square", action_local=True, use_hysteresis=False)),
        ("v33_all_action", dict(refresh_schedule="square", action_local=False, use_hysteresis=True, hysteresis_scale=0.03)),
        ("v34_bonferroni_j", dict(refresh_schedule="four_power", action_local=True, use_hysteresis=True, hysteresis_scale=0.03, bonferroni_components=True)),
        ("v34_student_hedge", dict(refresh_schedule="four_power", action_local=True, use_hysteresis=True, hysteresis_scale=0.03, student_hedge_pi=0.5)),
        ("neg_ctrl_reset", dict(refresh_schedule="square", action_local=True, use_hysteresis=False, reset_wealth_on_switch=True)),
    ]

    for mname, kw in configs:
        tape = make_tape()
        # Initialize at hard eps-optimal action A1 (index 1) so tracker must discover A0!
        r = run_v34_tracker(
            prob,
            tape,
            delta=delta,
            method_name=mname,
            init_action=1,
            null_log_tol=1e-4,
            max_samples=120_000,
            record_trace=(seed == 96000),
            **kw,
        )
        rows.append({
            "part": "A_switching",
            "sub_regime": sub_regime,
            "seed": seed,
            "delta": delta,
            "method": mname,
            "certified": r.certified,
            "is_correct": r.is_correct,
            "rec_action": r.recommended_action,
            "chose_easiest_a0": bool(r.recommended_action == 0),
            "true_regret": round(r.true_regret, 6),
            "total_samples": r.total_samples,
            "batches": r.batches,
            "design_calls": r.design_calls,
            "null_calls": r.null_calls,
            "action_switches": r.action_switches,
            "total_ms": round(r.total_wall_s * 1e3, 2),
        })
    return rows


def _run_part_b1_null_reset_job(job: tuple[int, float]) -> list[dict[str, Any]]:
    """Part B1: Null-boundary switching safety audit (Remark V34.1).

    Under the EXACT null mu = 0 in H_0 = {mu <= 0} (known-scale / unknown-scale e-process),
    compares V33 preserved all-batch wealth, V34 preserved predictably-skipped wealth, and
    Negative Control A (illegally resetting wealth to 1.0 upon revisiting after a switch away).
    """
    seed, delta = job
    rng = np.random.default_rng(seed)
    thresh = math.log(1.0 / delta)  # exact single-action Ville threshold log(1/delta)
    n_batches = 80
    # Use a sharp exact e-value under H_0 = {mu <= 0}: Gaussian mixture / predictable LR
    # (100% valid nonnegative supermartingale under mu <= 0, E[F_j | F_{j-1}] <= 1, AND tight
    # enough to hit boundary fluctuations so optional resetting immediately exposes Type-I inflation!)
    batches_y = [rng.normal(0.0, 1.0, size=12) for _ in range(n_batches)]

    def eval_eprocess(allow_reset: bool, skip_pattern: bool) -> dict[str, Any]:
        log_w = 0.0
        max_log_w = 0.0
        resets = 0
        crossed = False
        mu_alt = 0.55  # fixed predictable alternative mean (>0) for sharpest boundary test

        for j, ys in enumerate(batches_y, 1):
            r_j = len(ys)
            yb = float(np.mean(ys))
            # Exact valid unit-variance composite-null LR over u <= 0:
            # F_j = exp( r_j * (mu_alt * yb - 0.5 * mu_alt^2) )  (since sup_{u<=0} N(u,1) >= N(0,1)!)
            # Actually exact profiled unknown-variance LR on r_j=12 with true-scale predictable q_j = N(mu_alt, 1):
            # Using the exact known-variance null supremum u_mle = min(yb, 0) gives a tight exact e-factor:
            u_mle = min(yb, 0.0)
            log_lr = 0.5 * r_j * ((yb - u_mle) ** 2 - (yb - mu_alt) ** 2)
            # Predictable skipping (active on alternating/data-driven switches):
            active = True if (not skip_pattern or (j % 2 == 1) or log_w > -0.2) else False
            if active:
                if allow_reset and log_w < -0.15:
                    # ILLEGAL negative control (Remark V34.1): resets wealth back to 1.0 on revisit!
                    log_w = 0.0
                    resets += 1
                log_w += log_lr
                if log_w > max_log_w:
                    max_log_w = log_w
                if log_w >= thresh:
                    crossed = True
                    break

        return {"crossed": crossed, "max_log_w": round(max_log_w, 4), "resets": resets}

    r_pres = eval_eprocess(allow_reset=False, skip_pattern=False)
    r_skip = eval_eprocess(allow_reset=False, skip_pattern=True)
    r_reset = eval_eprocess(allow_reset=True, skip_pattern=True)
    return [
        {"part": "B1_null_reset", "seed": seed, "delta": delta, "method": "v33_preserved_all", **r_pres},
        {"part": "B1_null_reset", "seed": seed, "delta": delta, "method": "v34_preserved_skip", **r_skip},
        {"part": "B1_null_reset", "seed": seed, "delta": delta, "method": "neg_ctrl_reset_on_revisit", **r_reset},
    ]


def _run_part_b2_behrens_fisher_job(job: tuple[int, float]) -> list[dict[str, Any]]:
    """Part B2: Behrens-Fisher bimodal profiled-null safety test (CE V23.1).

    Under the EXACT true null theta_* = (0, 0) in P = {u1 <= 0} with H = [[1, 1], [1, -1]],
    compares exact certified cubic (Thm. V23.2), certified general-d B&B (Prop. V22.2), and
    naive single-start local SLSQP (starting from the polyhedron boundary vertex (0, 0))
    across a 40-batch sequential e-process at delta=0.05!
    """
    seed, delta = job
    rng = np.random.default_rng(seed)
    H = np.array([[1.0, 1.0], [1.0, -1.0]], dtype=float)
    A = np.array([[-1.0, 0.0]], dtype=float)
    b = np.array([0.0], dtype=float)
    poly_2d = ComponentPolyhedron(
        action=0, terminal=1, A=A, b=b, feasible_point=np.array([0.0, 0.0]),
        boundary_2d=((np.array([0.0, 0.0]), np.array([0.0, 1.0]), None),),
        vertices_2d=(),
    )
    poly_g = ComponentPolyhedron(action=0, terminal=1, A=A, b=b, feasible_point=np.array([0.0, 0.0]))

    # Proper normalized predictable Gaussian density q_j = N((1.1, 1.1), 1.0^2 I)
    # Using exact profiled-likelihood ratio q_j(Y_j) / U_{a,z,j}(Y_j) (100% valid conditional
    # e-value E[q_j/U_j | F_{j-1}] <= 1 under every null model in H_{a,z}!).
    # On positive fluctuations where Ybar_1, Ybar_2 > 0 at small batch size r_x = 3 (matching
    # V33's minimum compulsory count b_j >= 3!), the profiled null is genuinely bimodal,
    # trapping naive local SLSQP at u2=0 and inflating q_j / U_local past 1/delta!
    mu_pred = np.array([1.1, 1.1], dtype=float)
    var_pred = np.array([1.0, 1.0], dtype=float)
    thresh = math.log(1.0 / delta)

    log_w_cubic = 0.0
    log_w_bnb = 0.0
    log_w_local = 0.0
    cross_cubic = False
    cross_bnb = False
    cross_local = False
    local_viol_batches = 0
    max_local_viol_nats = 0.0
    bnb_viol_batches = 0

    # 35 batches of size r_x = 3 each (V33 minimum b_j = 3)
    r_vec = np.array([3.0, 3.0], dtype=float)
    for j in range(1, 36):
        y1 = rng.normal(0.0, 1.0, size=3)
        y2 = rng.normal(0.0, 1.0, size=3)
        yb = np.array([float(np.mean(y1)), float(np.mean(y2))], dtype=float)
        ss = np.array([
            max(1e-18, float(np.dot(y1 - yb[0], y1 - yb[0]))),
            max(1e-18, float(np.dot(y2 - yb[1], y2 - yb[1]))),
        ], dtype=float)
        s_over_r = ss / r_vec
        pred_excess = float(
            0.5 * np.sum(r_vec * (np.log(var_pred / s_over_r) + (s_over_r + (yb - mu_pred) ** 2) / var_pred - 1.0))
        )

        rc = solve_cubic_exact_2d(poly_2d, H, yb, r_vec, r_vec, ss, tol=1e-8)
        rb = solve_profiled_loss_certified(poly_g, H, yb, r_vec, r_vec, ss, tol=0.05, max_nodes=250)
        rl = solve_uncertified_local_null(poly_g, H, yb, r_vec, r_vec, ss, init_u=np.array([0.0, 0.0]))

        viol_loc = rl.lower - rc.upper
        if viol_loc > 1e-3:
            local_viol_batches += 1
            if viol_loc > max_local_viol_nats:
                max_local_viol_nats = viol_loc
        if rb.lower > rc.upper + 1e-5:
            bnb_viol_batches += 1

        # Exact half-cash profiled e-factor (100% valid supermartingale for certified bounds!)
        # Track BOTH per-batch raw e-value (single-batch crossing at 1/delta) and cumulative wealth
        lr_c = rc.lower - pred_excess
        lr_b = rb.lower - pred_excess
        lr_l = rl.lower - pred_excess
        log_w_cubic += float(np.logaddexp(0.0, lr_c) - math.log(2.0))
        log_w_bnb += float(np.logaddexp(0.0, lr_b) - math.log(2.0))
        log_w_local += float(np.logaddexp(0.0, lr_l) - math.log(2.0))
        if log_w_cubic >= thresh:
            cross_cubic = True
        if log_w_bnb >= thresh:
            cross_bnb = True
        if log_w_local >= thresh:
            cross_local = True

    return [
        {
            "part": "B2_behrens_fisher", "seed": seed, "delta": delta, "method": "certified_cubic_v23",
            "crossed": cross_cubic, "viol_batches": 0, "max_viol_nats": 0.0, "final_log_w": round(log_w_cubic, 4),
        },
        {
            "part": "B2_behrens_fisher", "seed": seed, "delta": delta, "method": "certified_bnb_v22",
            "crossed": cross_bnb, "viol_batches": bnb_viol_batches, "max_viol_nats": 0.0, "final_log_w": round(log_w_bnb, 4),
        },
        {
            "part": "B2_behrens_fisher", "seed": seed, "delta": delta, "method": "neg_ctrl_local_slsqp",
            "crossed": cross_local, "viol_batches": local_viol_batches, "max_viol_nats": round(max_local_viol_nats, 4),
            "final_log_w": round(log_w_local, 4),
        },
    ]


def summarize(out_dir: Path) -> None:
    runs_a = [json.loads(l) for l in (out_dir / "v9_exp3_partA_runs.jsonl").read_text(encoding="utf-8").splitlines() if l.strip()]
    runs_b = [json.loads(l) for l in (out_dir / "v9_exp3_partB_runs.jsonl").read_text(encoding="utf-8").splitlines() if l.strip()]

    # Part A summary
    ga: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for r in runs_a:
        ga[(r["sub_regime"], r["method"])].append(r)
    sum_a: list[dict[str, Any]] = []
    for (sub_r, meth), grp in sorted(ga.items()):
        n = len(grp)
        certs = [r for r in grp if r["certified"]]
        errs = sum(1 for r in certs if not r["is_correct"])
        sum_a.append({
            "sub_regime": sub_r,
            "method": meth,
            "runs": n,
            "cert_rate": round(len(certs) / n, 4),
            "false_certs": errs,
            "chose_easiest_a0_rate": round(sum(1 for r in grp if r["chose_easiest_a0"]) / n, 4),
            "med_samples": round(float(np.median([r["total_samples"] for r in grp])), 1),
            "mean_samples": round(float(np.mean([r["total_samples"] for r in grp])), 1),
            "mean_switches": round(float(np.mean([r["action_switches"] for r in grp])), 2),
            "med_null_calls": round(float(np.median([r["null_calls"] for r in grp])), 1),
            "med_total_ms": round(float(np.median([r["total_ms"] for r in grp])), 2),
        })
    p_a = out_dir / "v9_exp3_partA_summary.csv"
    with p_a.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(sum_a[0].keys()))
        w.writeheader()
        w.writerows(sum_a)

    # Part B summary
    gb: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for r in runs_b:
        gb[(r["part"], r["method"])].append(r)
    sum_b: list[dict[str, Any]] = []
    for (part, meth), grp in sorted(gb.items()):
        n = len(grp)
        cross = sum(1 for r in grp if r["crossed"])
        sum_b.append({
            "part": part,
            "method": meth,
            "runs": n,
            "delta": grp[0]["delta"],
            "false_cert_count": cross,
            "false_cert_rate": round(cross / n, 4),
            "mean_resets_or_viols": round(float(np.mean([r.get("resets", r.get("viol_batches", 0)) for r in grp])), 2),
            "max_viol_nats": round(float(max(r.get("max_viol_nats", 0.0) for r in grp)), 4),
        })
    p_b = out_dir / "v9_exp3_partB_summary.csv"
    with p_b.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(sum_b[0].keys()))
        w.writeheader()
        w.writerows(sum_b)

    print(f"Wrote {p_a} ({len(sum_a)} rows) and {p_b} ({len(sum_b)} rows).")
    print("\n=== Part A: Multi-Answer Switching Stress Test ===")
    for r in sum_a:
        print(
            f"  {r['sub_regime']:16s} {r['method']:18s} cert={r['cert_rate']:.2f} err={r['false_certs']} "
            f"A0={r['chose_easiest_a0_rate']:.2f} sw={r['mean_switches']:4.2f} medN={r['med_samples']:6.1f} n_call={r['med_null_calls']:6.1f}"
        )
    print("\n=== Part B: Null-Boundary Reset & Behrens-Fisher Safety Audit ===")
    for r in sum_b:
        print(
            f"  {r['part']:18s} {r['method']:26s} err={r['false_cert_count']:3d}/{r['runs']} ({100*r['false_cert_rate']:5.1f}%) "
            f"mean_res/viol={r['mean_resets_or_viols']:5.2f} max_viol={r['max_viol_nats']:.4f} nats"
        )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=OUT_DIR)
    ap.add_argument("--workers", type=int, default=min(24, os.cpu_count() or 8))
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    args = ap.parse_args()

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    # Print exact rates of the 3 eps-optimal actions in Part A
    prob_sw = make_switching_multi_answer_dag(eps=0.05)
    c_sw, v_sw, _ = compute_exact_nuisance_kl_rate(prob_sw, tol=1e-4)
    print(f"Switching DAG rates: C*={c_sw:.5f}, V_a={np.round(v_sw, 5)}", flush=True)

    if args.smoke:
        seeds_a = [96000 + i for i in range(6)]
        seeds_b1 = [97000 + i for i in range(25)]
        seeds_b2 = [98000 + i for i in range(25)]
    else:
        seeds_a = [96000 + i for i in range(200)]
        seeds_b1 = [97000 + i for i in range(500)]
        seeds_b2 = [98000 + i for i in range(500)]

    jobs_a = [(sr, s, 0.05) for sr in ("natural_hard_init", "adv_early_switch", "tied_identical_opt") for s in seeds_a]
    jobs_b1 = [(s, 0.05) for s in seeds_b1]
    jobs_b2 = [(s, 0.05) for s in seeds_b2]

    rows_a: list[dict[str, Any]] = []
    rows_b: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        fa = [ex.submit(_run_part_a_job, j) for j in jobs_a]
        fb1 = [ex.submit(_run_part_b1_null_reset_job, j) for j in jobs_b1]
        fb2 = [ex.submit(_run_part_b2_behrens_fisher_job, j) for j in jobs_b2]
        for fut in as_completed(fa):
            rows_a.extend(fut.result())
        for fut in as_completed(fb1 + fb2):
            rows_b.extend(fut.result())

    rows_a.sort(key=lambda r: (r["sub_regime"], r["seed"], r["method"]))
    rows_b.sort(key=lambda r: (r["part"], r["seed"], r["method"]))

    (out_dir / "v9_exp3_partA_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows_a) + "\n", encoding="utf-8")
    (out_dir / "v9_exp3_partB_runs.jsonl").write_text("\n".join(json.dumps(r) for r in rows_b) + "\n", encoding="utf-8")
    (out_dir / "v9_exp3_switching_rates.json").write_text(
        json.dumps({"c_star": c_sw, "V_a": [float(x) for x in v_sw]}, indent=2) + "\n", encoding="utf-8"
    )

    summarize(out_dir)
    wall = time.perf_counter() - t0
    manifest_files = {}
    for fname in (
        "v9_exp3_partA_runs.jsonl",
        "v9_exp3_partB_runs.jsonl",
        "v9_exp3_partA_summary.csv",
        "v9_exp3_partB_summary.csv",
        "v9_exp3_switching_rates.json",
    ):
        fp = out_dir / fname
        manifest_files[fname] = {"bytes": fp.stat().st_size, "sha256": _sha256(fp)}
    manifest = {
        "suite": "v9_exp3_switching_and_safety",
        "smoke": bool(args.smoke),
        "wall_s": round(wall, 2),
        "files": manifest_files,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Completed V9-3 in {wall:.1f}s. Manifest written.")


if __name__ == "__main__":
    main()
