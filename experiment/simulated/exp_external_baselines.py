"""Experiment 8 (ICML v4): External Structured Pure-Exploration Baselines & 2x2 Decomposition.

Compares established structured Best-Arm Identification (BAI) methods from the literature
against `Exact-Regret-DAG-LUCB` under matched `(eps, delta)`, identical terminal reward tapes,
and identical nested confidence boxes (`box` and `emp_bernstein`):
- `ugape_mcts_tree_marg`: Kaufmann & Koolen (NeurIPS 2017) tree-unrolled `UGapE-MCTS` (Marginal stop)
- `ugape_mcts_dag_marg`: Kaufmann & Koolen (2017) DAG-pooled `UGapE-MCTS` (native Marginal stop)
- `ugape_mcts_dag_exact`: DAG-pooled `UGapE-MCTS` + our Exact-Regret stop (2x2 certificate isolation)
- `lucb_micro_marg`: Huang, Ajallooeian, Szepesvari, & Muller (ALT 2017) `LUCB-micro` (Marginal stop)
- `lucb_micro_exact`: `LUCB-micro` + our Exact-Regret stop (2x2 certificate isolation)
- `varde_marg`: Variance-decrement allocation (inspired by VarDE, ICML 2026) + Marginal witnesses/stop
- `varde_exact`: Variance-decrement allocation + Exact-Regret witnesses/stop
- `ta_uct_exact`: Passive `TA-UCT` + `ChargedDualCovers` (Exact-Regret stop)
- `exact_dag_lucb`: Proposed `Exact-Regret-DAG-LUCB` (`WitnessDualCovers`)

Directly isolates:
(1) How much gain comes from the Exact Shared-Support Certificate alone (holding external
    samplers `LUCB-micro` and `UGapE-MCTS` fixed), and
(2) How much additional gain comes from `Exact-Regret-DAG-LUCB`'s outside-support challenger
    sampling (`Z \\ S(a*_t)` vs. shared-leaf challenger waste in `LUCB-micro` / `UGapE-MCTS`).
"""
from __future__ import annotations

import argparse
import csv
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import time
import tracemalloc

from joint_root_cert import CertifiedSearchSession
from joint_root_cert.benchmarks import (
    contiguous_window_dag,
    overlap_dag,
)
from joint_root_cert import ActiveDAGLUCBSession
from joint_root_cert.tracking import (
    LUCBMicroSession,
    UGapEMCTSSession,
    VarDEDAGSession,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v4_icml_baselines/exp8_external_baselines"

CORE_METHODS = (
    "lucb_micro_marg",
    "lucb_micro_exact",
    "ugape_mcts_dag_marg",
    "ugape_mcts_dag_exact",
    "varde_marg",
    "varde_exact",
    "ta_uct_exact",
    "exact_dag_lucb",
)
M64_EXTRA = ("ugape_mcts_tree_marg",)

OVERLAPS = (0.00, 0.25, 0.50, 0.75, 0.88)
SEEDS = tuple(range(682001, 682005))  # 4 seeds x 2 counterbalanced repeats = 8 runs/cell
DELTA = 0.05
STEP_CAP = 36000
WALL_LIMIT_S = 1.0


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_session(prob, eps: float, seed: int, method: str, schedule: str):
    if method == "lucb_micro_marg":
        return LUCBMicroSession(prob, seed, eps, delta=DELTA, schedule=schedule, stop_rule="marginal")
    if method == "lucb_micro_exact":
        return LUCBMicroSession(prob, seed, eps, delta=DELTA, schedule=schedule, stop_rule="exact")
    if method == "ugape_mcts_dag_marg":
        return UGapEMCTSSession(prob, seed, eps, delta=DELTA, schedule=schedule, mode="dag", stop_rule="marginal")
    if method == "ugape_mcts_dag_exact":
        return UGapEMCTSSession(prob, seed, eps, delta=DELTA, schedule=schedule, mode="dag", stop_rule="exact")
    if method == "ugape_mcts_tree_marg":
        return UGapEMCTSSession(prob, seed, eps, delta=DELTA, schedule=schedule, mode="tree", stop_rule="marginal")
    if method == "varde_marg":
        return VarDEDAGSession(prob, seed, eps, delta=DELTA, schedule=schedule, witness_mode="marginal")
    if method == "varde_exact":
        return VarDEDAGSession(prob, seed, eps, delta=DELTA, schedule=schedule, witness_mode="exact")
    if method == "ta_uct_exact":
        return CertifiedSearchSession(
            prob, seed, "uct", "dual-covers", eps,
            delta=DELTA, c_explore=3.0, q_cert=4, schedule=schedule,
        )
    if method == "exact_dag_lucb":
        return ActiveDAGLUCBSession(prob, seed, "dual-covers", eps, delta=DELTA, schedule=schedule)
    raise ValueError(f"Unknown method: {method}")


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    return sess.evidence.conflict


def run_one(prob, eps: float, seed: int, method: str,
            schedule: str, wall_limit: float, cap: int, measure_mem: bool = False) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    opt = values[prob.graph.root]
    regrets = [max(0.0, opt - values[c]) for c in prob.graph.children[prob.graph.root]]

    if measure_mem:
        tracemalloc.start()
    t0 = time.perf_counter()
    sess = make_session(prob, eps, seed, method, schedule)
    elapsed = time.perf_counter() - t0
    while (not sess.certified and not _has_conflict(sess)
           and sess.calls < cap and elapsed < wall_limit):
        sess.step()
        elapsed = time.perf_counter() - t0

    cert = sess.certified
    act = sess.action
    calls = sess.calls
    work = sess.work
    peak_kib = 0.0
    if measure_mem:
        _, peak_bytes = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        peak_kib = peak_bytes / 1024.0
    del sess
    total_s = time.perf_counter() - t0

    true_reg = regrets[act]
    false_cert = bool(cert and true_reg > eps + 1e-12)
    assert not false_cert, f"False certificate in {method}: {true_reg} > {eps}"
    return {
        "method": method,
        "schedule": schedule,
        "certified": cert,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "total_s": total_s,
        "total_work": work,
        "peak_kib": round(peak_kib, 2),
        "final_simple_regret": true_reg,
    }


def build_tasks(smoke: bool = False) -> list[dict]:
    if smoke:
        p1, e1 = overlap_dag(64, 0.75, 0.32, 682001, noisy=True)
        p2, e2 = contiguous_window_dag(64, 8, 682001, noisy=True)
        return [
            {
                "suite": "overlap_64_box", "family": "overlap_64_box_rho75",
                "m": 64, "rho": 0.75, "seed": 682001, "prob": p1, "eps": e1,
                "schedule": "box", "methods": CORE_METHODS + M64_EXTRA,
            },
            {
                "suite": "window_box", "family": "window_64_box",
                "m": 64, "rho": 0.50, "seed": 682001, "prob": p2, "eps": e2,
                "schedule": "box", "methods": CORE_METHODS,
            },
        ]

    tasks = []
    # 1. Overlap M = 64 (includes Tree-unrolled UGapE-MCTS!) & M = 256 under Hoeffding
    for m in (64, 256):
        meths = CORE_METHODS + M64_EXTRA if m == 64 else CORE_METHODS
        for rho in OVERLAPS:
            for s in SEEDS:
                p, e = overlap_dag(m, rho, 0.32, s, noisy=True)
                tasks.append({
                    "suite": f"overlap_{m}_box",
                    "family": f"overlap_{m}_box_rho{int(round(rho*100)):02d}",
                    "m": m, "rho": rho, "seed": s, "prob": p, "eps": e,
                    "schedule": "box", "methods": meths,
                })

    # 2. Contiguous Window M = 256 (zero support containment, 50% window overlap)
    for s in SEEDS:
        p, e = contiguous_window_dag(256, 16, s, noisy=True)
        tasks.append({
            "suite": "window_256_box",
            "family": "window_256_box",
            "m": 256, "rho": 0.50, "seed": s, "prob": p, "eps": e,
            "schedule": "box", "methods": CORE_METHODS,
        })

    # 3. Overlap M = 256 under Empirical Bernstein (rho in {0.50, 0.75, 0.88})
    for rho in (0.50, 0.75, 0.88):
        for s in SEEDS:
            p, e = overlap_dag(256, rho, 0.32, s, noisy=True)
            tasks.append({
                "suite": "overlap_256_eb",
                "family": f"overlap_256_eb_rho{int(round(rho*100)):02d}",
                "m": 256, "rho": rho, "seed": s, "prob": p, "eps": e,
                "schedule": "emp_bernstein", "methods": CORE_METHODS,
            })
    return tasks


def summarize(dest: Path) -> None:
    runs = [json.loads(line) for line in (dest / "runs.jsonl").read_text().splitlines() if line.strip()]
    mems = [json.loads(line) for line in (dest / "memory_runs.jsonl").read_text().splitlines() if line.strip()]

    mem_lookup: dict[tuple[str, str], float] = {}
    for fam in {r["family"] for r in mems}:
        for meth in {r["method"] for r in mems if r["family"] == fam}:
            vals = [r["peak_kib"] for r in mems if r["family"] == fam and r["method"] == meth]
            mem_lookup[(fam, meth)] = round(statistics.median(vals), 1)

    all_methods_order = CORE_METHODS + M64_EXTRA
    rows = []
    for fam in sorted({r["family"] for r in runs}):
        sub_f = [r for r in runs if r["family"] == fam]
        suite = sub_f[0]["suite"]
        m = sub_f[0]["m"]
        rho = sub_f[0]["rho"]
        sched = sub_f[0]["schedule"]
        for meth in all_methods_order:
            sub = [r for r in sub_f if r["method"] == meth]
            if not sub:
                continue
            rows.append({
                "suite": suite,
                "family": fam,
                "m": m,
                "rho": rho,
                "schedule": sched,
                "method": meth,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "median_work": round(statistics.median(r["total_work"] for r in sub), 1),
                "median_peak_kib": mem_lookup.get((fam, meth), 0.0),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_by_family.csv").open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    # 2x2 Factorial `(Sampler x Certificate)` summary across overlap_256_box
    fac_rows = []
    ov256 = [r for r in rows if r["suite"] == "overlap_256_box"]
    for rho in sorted({r["rho"] for r in ov256}):
        sub = {r["method"]: r for r in ov256 if r["rho"] == rho}
        if not sub:
            continue
        fac_rows.append({
            "rho": rho,
            "lucb_micro_marg_steps": sub["lucb_micro_marg"]["median_capped_steps"],
            "lucb_micro_marg_ms": sub["lucb_micro_marg"]["median_total_ms"],
            "lucb_micro_exact_steps": sub["lucb_micro_exact"]["median_capped_steps"],
            "lucb_micro_exact_ms": sub["lucb_micro_exact"]["median_total_ms"],
            "ugape_dag_marg_steps": sub["ugape_mcts_dag_marg"]["median_capped_steps"],
            "ugape_dag_marg_ms": sub["ugape_mcts_dag_marg"]["median_total_ms"],
            "ugape_dag_exact_steps": sub["ugape_mcts_dag_exact"]["median_capped_steps"],
            "ugape_dag_exact_ms": sub["ugape_mcts_dag_exact"]["median_total_ms"],
            "varde_exact_steps": sub["varde_exact"]["median_capped_steps"],
            "varde_exact_ms": sub["varde_exact"]["median_total_ms"],
            "ta_uct_exact_steps": sub["ta_uct_exact"]["median_capped_steps"],
            "ta_uct_exact_ms": sub["ta_uct_exact"]["median_total_ms"],
            "exact_dag_lucb_steps": sub["exact_dag_lucb"]["median_capped_steps"],
            "exact_dag_lucb_ms": sub["exact_dag_lucb"]["median_total_ms"],
        })
    if fac_rows:
        with (dest / "summary_2x2_overlap256.csv").open("w", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=list(fac_rows[0].keys()))
            writer.writeheader()
            writer.writerows(fac_rows)

    (dest / "summary.json").write_text(json.dumps({
        "total_runs": len(runs),
        "total_memory_runs": len(mems),
        "total_false_certificates": sum(r["false_certificates"] for r in rows),
        "factorial_overlap256": fac_rows,
        "by_family": rows,
    }, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEST)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()

    dest: Path = args.out
    dest.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(dest)
        return

    t_start = time.perf_counter()
    tasks = build_tasks(smoke=args.smoke)
    repeats = 1 if args.smoke else 2
    wall_limit = 0.20 if args.smoke else WALL_LIMIT_S
    cap = 5000 if args.smoke else STEP_CAP

    wp, we = overlap_dag(64, 0.50, 0.32, 682001, noisy=True)
    for meth in CORE_METHODS + M64_EXTRA:
        run_one(wp, we, 682001, meth, "box", 0.04, 400)

    runs_path = dest / "runs.jsonl"
    mem_path = dest / "memory_runs.jsonl"
    rng = random.Random(20261121)

    with runs_path.open("w") as fh:
        for t in tasks:
            for rep in range(repeats):
                order = list(t["methods"])
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                for meth in order:
                    res = run_one(
                        t["prob"], t["eps"], t["seed"] + 10000 * rep,
                        meth, t["schedule"], wall_limit, cap, measure_mem=False,
                    )
                    fh.write(json.dumps({
                        "suite": t["suite"],
                        "family": t["family"],
                        "m": t["m"],
                        "rho": t["rho"],
                        "seed": t["seed"] + 10000 * rep,
                        "repeat": rep,
                        "eps": t["eps"],
                        **res,
                    }) + "\n")
                fh.flush()

    # Dedicated isolated tracemalloc pass (1 seed per family so timers above were never perturbed)
    seen_fams = set()
    with mem_path.open("w") as fm:
        for t in tasks:
            if t["family"] in seen_fams:
                continue
            seen_fams.add(t["family"])
            for meth in t["methods"]:
                res = run_one(
                    t["prob"], t["eps"], t["seed"],
                    meth, t["schedule"], 0.25 if not args.smoke else 0.10,
                    min(cap, 4000), measure_mem=True,
                )
                fm.write(json.dumps({
                    "family": t["family"],
                    "m": t["m"],
                    "rho": t["rho"],
                    **res,
                }) + "\n")
            fm.flush()

    summarize(dest)
    manifest = {
        "experiment": "exp8_external_baselines",
        "smoke": args.smoke,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "sha256_runs": digest(runs_path),
        "sha256_memory": digest(mem_path),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"Done exp8_external_baselines in {manifest['elapsed_s']}s -> {dest}")


if __name__ == "__main__":
    main()
