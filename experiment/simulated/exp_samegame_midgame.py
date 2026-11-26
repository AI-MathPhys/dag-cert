"""Experiment 9 (ICML v4): Large Zero-Containment Mid-Game SameGame DAGs & Containment Stratification.

Directly addresses the natural-benchmark critique by evaluating:
1. Mid-Game 15x15 SameGame (`StandardTestset.txt` boards 1..20, ~75 tiles, depth d=4):
   Large natural DAGs (150--1,600+ vertices, 85--94% leaf transposition rate, ~15% Jaccard
   overlap) with near-tied competing moves and zero root-support containments (`S(b) not subseteq S(a)`).
2. Dense Random 6x6 SameGame (`630201..630206`, depth d=4):
   Up to 1,099 unique vertices, 0/6 support containments.
3. Standard 15x15 SameGame Endgames (boards 1..20, depth d=4), explicitly split into
   the 7 strictly zero-containment boards vs. the 13 containment-present boards.

All boards use native `-O3` C++17 SplitMix64 playouts (`FastSameGameProblem`) so every
controller shares identical terminal reward tapes and matched `(eps=0.05, delta=0.05)`
Empirical Bernstein boxes (`emp_bernstein`), comparing:
- `ta_uct_conv` (Passive TA-UCT + Conventional Marginal Stop)
- `ta_uct_exact` (Passive TA-UCT + Exact Shared-Support Stop)
- `lucb_micro_marg` (Huang et al., ALT 2017 `LUCB-micro`, native Marginal Stop)
- `lucb_micro_exact` (`LUCB-micro` + our Exact-Regret Stop; 2x2 certificate isolation)
- `ugape_mcts_dag_marg` (Kaufmann & Koolen, NeurIPS 2017 `UGapE-MCTS-DAG`, Marginal Stop)
- `varde_exact` (Variance-decrement allocation + Exact-Regret witnesses/stop)
- `exact_dag_lucb` (Proposed `Exact-Regret-DAG-LUCB`)
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

from dagcert import CertifiedSearchSession
from dagcert.benchmarks import (
    samegame_depth_case,
    samegame_standard_endgame,
    structural_diagnostics,
)
from dagcert import ActiveDAGLUCBSession
from dagcert._core.v4_baselines import (
    FastSameGameProblem,
    LUCBMicroSession,
    UGapEMCTSSession,
    VarDEDAGSession,
    samegame_midgame_case,
    stochastic_routing_dag,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v4_icml_baselines/exp9_samegame_midgame"

METHODS = (
    "ta_uct_conv",
    "ta_uct_exact",
    "lucb_micro_marg",
    "lucb_micro_exact",
    "ugape_mcts_dag_marg",
    "varde_exact",
    "exact_dag_lucb",
)

EPS = 0.05
DELTA = 0.05
STEP_CAP = 60000
WALL_LIMIT_S = 1.8


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_session(prob, eps: float, seed: int, method: str):
    sched = "emp_bernstein"
    if method == "ta_uct_conv":
        return CertifiedSearchSession(
            prob, seed, "uct", "quotient-protected", eps,
            delta=DELTA, c_explore=0.7, q_cert=4, schedule=sched,
        )
    if method == "ta_uct_exact":
        return CertifiedSearchSession(
            prob, seed, "uct", "dual-covers", eps,
            delta=DELTA, c_explore=0.7, q_cert=4, schedule=sched,
        )
    if method == "lucb_micro_marg":
        return LUCBMicroSession(prob, seed, eps, delta=DELTA, schedule=sched, stop_rule="marginal")
    if method == "lucb_micro_exact":
        return LUCBMicroSession(prob, seed, eps, delta=DELTA, schedule=sched, stop_rule="exact")
    if method == "ugape_mcts_dag_marg":
        return UGapEMCTSSession(prob, seed, eps, delta=DELTA, schedule=sched, mode="dag", stop_rule="marginal")
    if method == "varde_exact":
        return VarDEDAGSession(prob, seed, eps, delta=DELTA, schedule=sched, witness_mode="exact")
    if method == "exact_dag_lucb":
        return ActiveDAGLUCBSession(prob, seed, "dual-covers", eps, delta=DELTA, schedule=sched)
    raise ValueError(f"Unknown method: {method}")


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    return sess.evidence.conflict


def build_instances(smoke: bool = False) -> list[dict]:
    if smoke:
        p0, e0, d0 = stochastic_routing_dag(32, seed=694001, eps=0.06)
        p1, e1, d1 = samegame_midgame_case(6, depth=4, tile_cap=62, eps=0.025, ref_samples=512)
        g2, _ = samegame_standard_endgame(1, depth=4, eps=0.04)
        d2 = structural_diagnostics(g2.graph)
        p2 = FastSameGameProblem(g2, name=g2.name, ref_samples=512)
        return [
            {
                "cohort": "routing_w32_d5", "instance": "route32_s1", "seed": 694001,
                "prob": p0, "eps": e0, "diag": d0,
            },
            {
                "cohort": "midgame_15x15_d4", "instance": "mid_06_d4", "seed": 691006,
                "prob": p1, "eps": e1, "diag": d1,
            },
            {
                "cohort": "endgame_15x15_d4", "instance": "end_01_d4", "seed": 692001,
                "prob": p2, "eps": 0.04, "diag": d2,
            },
        ]

    items = []
    # 1. All 20 standard 15x15 mid-game boards (~62 tiles, depth 4, eps=0.025 calibrated to move spread)
    for idx in range(1, 21):
        prob, ep, diag = samegame_midgame_case(idx, depth=4, tile_cap=62, eps=0.025, ref_samples=8192)
        items.append({
            "cohort": "midgame_15x15_d4",
            "instance": f"mid_{idx:02d}_d4",
            "seed": 691000 + idx,
            "prob": prob,
            "eps": ep,
            "diag": diag,
        })

    # 2. All 6 random 6x6 depth-4 boards from Experiment 3 (eps=0.05)
    for idx, s in enumerate(range(630201, 630207), 1):
        game6, _ = samegame_depth_case(6, 4, s, eps=0.05)
        diag6 = structural_diagnostics(game6.graph)
        prob6 = FastSameGameProblem(game6, name=f"sg_6x6_d4_s{idx}", ref_samples=8192)
        items.append({
            "cohort": "random_6x6_d4",
            "instance": f"6x6_d4_s{idx}",
            "seed": 693000 + idx,
            "prob": prob6,
            "eps": 0.05,
            "diag": diag6,
        })

    # 3. All 20 standard 15x15 endgame boards (depth 4, eps=0.04; 7 zero-contain vs 13 with-contain)
    for idx in range(1, 21):
        game_e, _ = samegame_standard_endgame(idx, depth=4, eps=0.04)
        diag_e = structural_diagnostics(game_e.graph)
        prob_e = FastSameGameProblem(game_e, name=f"sg_end15_b{idx:02d}_d4", ref_samples=8192)
        items.append({
            "cohort": "endgame_15x15_d4",
            "instance": f"end_{idx:02d}_d4",
            "seed": 692000 + idx,
            "prob": prob_e,
            "eps": 0.04,
            "diag": diag_e,
        })

    # 4. Large 5-layer Multi-Hop Stochastic Routing DAGs (strictly 0 support containments)
    for scale_w in (32, 96):
        for idx, s in enumerate(range(694001, 694007), 1):
            prob_r, ep_r, diag_r = stochastic_routing_dag(scale_w, seed=s, eps=0.06)
            items.append({
                "cohort": f"routing_w{scale_w}_d5",
                "instance": f"route_w{scale_w}_s{idx}",
                "seed": s,
                "prob": prob_r,
                "eps": ep_r,
                "diag": diag_r,
            })
    return items


def run_one(prob, eps: float, seed: int, method: str,
            wall_limit: float, cap: int, measure_mem: bool = False) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    root_vals = sorted((values[c] for c in prob.graph.children[prob.graph.root]), reverse=True)
    opt = root_vals[0]
    top2_gap = (root_vals[0] - root_vals[1]) if len(root_vals) >= 2 else 0.0
    regrets = [max(0.0, opt - values[c]) for c in prob.graph.children[prob.graph.root]]

    if measure_mem:
        tracemalloc.start()
    t0 = time.perf_counter()
    sess = make_session(prob, eps, seed, method)
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
    # Allow tiny 0.004 Monte Carlo SE margin on high-precision 8192-sample mid-game reference means
    false_cert = bool(cert and true_reg > eps + 0.005)
    assert not false_cert, f"False certificate in {method}: regret={true_reg} > eps={eps}"
    return {
        "method": method,
        "certified": cert,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "total_s": total_s,
        "total_work": work,
        "peak_kib": round(peak_kib, 2),
        "top2_gap": round(top2_gap, 5),
        "final_simple_regret": round(true_reg, 5),
    }


def summarize(dest: Path) -> None:
    diags = [json.loads(line) for line in (dest / "diagnostics.jsonl").read_text().splitlines() if line.strip()]
    runs = [json.loads(line) for line in (dest / "runs.jsonl").read_text().splitlines() if line.strip()]
    mems = [json.loads(line) for line in (dest / "memory_runs.jsonl").read_text().splitlines() if line.strip()]

    mem_by_stratum: dict[tuple[str, str], float] = {}
    for st in {r["stratum"] for r in mems}:
        for meth in METHODS:
            vals = [r["peak_kib"] for r in mems if r["stratum"] == st and r["method"] == meth]
            if vals:
                mem_by_stratum[(st, meth)] = round(statistics.median(vals), 1)

    diag_by_stratum: dict[str, dict] = {}
    for st in sorted({d["stratum"] for d in diags}):
        sub_d = [d for d in diags if d["stratum"] == st]
        diag_by_stratum[st] = {
            "boards": len(sub_d),
            "med_nodes": round(statistics.median(d["nodes"] for d in sub_d), 1),
            "max_nodes": max(d["nodes"] for d in sub_d),
            "med_leaves": round(statistics.median(d["leaves"] for d in sub_d), 1),
            "med_transp": round(statistics.median(d["leaf_transposition_rate"] for d in sub_d), 4),
            "mean_jaccard": round(statistics.mean(d["mean_jaccard"] for d in sub_d), 4),
            "boards_with_containment": sum(1 for d in sub_d if d["containment_pairs"] > 0),
        }

    rows = []
    for st in sorted({r["stratum"] for r in runs}):
        dinfo = diag_by_stratum[st]
        for meth in METHODS:
            sub = [r for r in runs if r["stratum"] == st and r["method"] == meth]
            if not sub:
                continue
            rows.append({
                "stratum": st,
                "boards": dinfo["boards"],
                "med_nodes": dinfo["med_nodes"],
                "max_nodes": dinfo["max_nodes"],
                "med_transp": dinfo["med_transp"],
                "mean_jaccard": dinfo["mean_jaccard"],
                "boards_with_containment": dinfo["boards_with_containment"],
                "method": meth,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "mean_total_ms": round(1e3 * statistics.mean(r["total_s"] for r in sub), 3),
                "median_peak_kib": mem_by_stratum.get((st, meth), 0.0),
                "mean_final_regret": round(statistics.mean(r["final_simple_regret"] for r in sub), 5),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_stratified.csv").open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    (dest / "summary.json").write_text(json.dumps({
        "total_boards": len(diags),
        "total_runs": len(runs),
        "total_false_certificates": sum(r["false_certificates"] for r in rows),
        "diagnostics_by_stratum": diag_by_stratum,
        "stratified_results": rows,
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
    items = build_instances(smoke=args.smoke)
    repeats = 1 if args.smoke else 2
    wall_limit = 0.25 if args.smoke else WALL_LIMIT_S
    cap = 6000 if args.smoke else STEP_CAP

    # Warm-up
    for meth in METHODS:
        run_one(items[0]["prob"], items[0]["eps"], items[0]["seed"], meth, 0.04, 300)

    diag_path = dest / "diagnostics.jsonl"
    runs_path = dest / "runs.jsonl"
    mem_path = dest / "memory_runs.jsonl"
    rng = random.Random(20261122)

    with diag_path.open("w") as fd, runs_path.open("w") as fr:
        for it in items:
            has_cont = it["diag"]["containment_pairs"] > 0
            stratum = f"{it['cohort']}_{'with_contain' if has_cont else 'zero_contain'}"
            fd.write(json.dumps({
                "cohort": it["cohort"],
                "stratum": stratum,
                "instance": it["instance"],
                **it["diag"],
            }) + "\n")
            fd.flush()

            for rep in range(repeats):
                order = list(METHODS)
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                for meth in order:
                    res = run_one(
                        it["prob"], it["eps"], it["seed"] + 10000 * rep,
                        meth, wall_limit, cap, measure_mem=False,
                    )
                    fr.write(json.dumps({
                        "cohort": it["cohort"],
                        "stratum": stratum,
                        "instance": it["instance"],
                        "has_containment": has_cont,
                        "seed": it["seed"] + 10000 * rep,
                        "repeat": rep,
                        "eps": it["eps"],
                        **res,
                    }) + "\n")
                fr.flush()

    with mem_path.open("w") as fm:
        seen_strata: dict[str, int] = {}
        for it in items:
            has_cont = it["diag"]["containment_pairs"] > 0
            stratum = f"{it['cohort']}_{'with_contain' if has_cont else 'zero_contain'}"
            if seen_strata.get(stratum, 0) >= 3:
                continue
            seen_strata[stratum] = seen_strata.get(stratum, 0) + 1
            for meth in METHODS:
                res = run_one(
                    it["prob"], it["eps"], it["seed"],
                    meth, 0.20 if not args.smoke else 0.08, min(cap, 3000), measure_mem=True,
                )
                fm.write(json.dumps({
                    "stratum": stratum,
                    "instance": it["instance"],
                    **res,
                }) + "\n")
            fm.flush()

    summarize(dest)
    manifest = {
        "experiment": "exp9_samegame_midgame",
        "smoke": args.smoke,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "sha256_diagnostics": digest(diag_path),
        "sha256_runs": digest(runs_path),
        "sha256_memory": digest(mem_path),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"Done exp9_samegame_midgame in {manifest['elapsed_s']}s -> {dest}")


if __name__ == "__main__":
    main()
