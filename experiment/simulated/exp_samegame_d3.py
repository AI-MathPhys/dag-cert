"""Experiment 3: Larger Natural Transposition-Rich SameGame Search DAGs (Depths 3 & 4).

Evaluates:
1. Unselected 3-color SameGame boards at deeper lookahead horizons:
   - 5x5 depth 3 (8 seeds), 6x6 depth 3 (8 seeds), 6x6 depth 4 (8 seeds)
2. All 20 standard 15x15 SameGame benchmark endgames (StandardTestset.txt) at both depth 3 and depth 4.

Reports:
- Exact structural diagnostics: unique DAG vertices, edges, leaves, unrolled tree paths,
  path transposition rate, pairwise support Jaccard overlap, strict/equal support
  containments S(b) subseteq S(a), and support fragmentation.
- Common-trace statistical comparison: tau_exact vs. tau_conv and certification rates
  at fixed rollout budgets on natural SameGame transpositions.
- Counterbalanced cold end-to-end certification time, anytime simple regret across
  (10 ms, 50 ms, 250 ms, 750 ms, 1500 ms) deadlines, scalar work, and peak memory
  across Quotient-Eager, Quotient-Protected, Quotient-Decision, Dyadic Covers,
  Charged Dual Covers, and Factorized Regret.
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

from dagcert._core.certified_uct import TranspositionUCT
from dagcert import CertifiedSearchSession
from dagcert.benchmarks import (
    samegame_depth_case,
    samegame_standard_endgame,
    structural_diagnostics,
)
from dagcert.certificates import ChargedDualCovers, MarginalGraphMonitor


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v2_extensions/exp3_samegame"

BOARD_FAMILIES = (
    ("samegame_5x5_d3", 5, 3, 0.10, tuple(range(630001, 630007))),
    ("samegame_6x6_d3", 6, 3, 0.10, tuple(range(630101, 630107))),
    ("samegame_6x6_d4", 6, 4, 0.10, tuple(range(630201, 630207))),
)
STD_INDICES = tuple(range(1, 21))
STD_EPS = 0.08

METHODS = (
    "quotient-eager",
    "quotient-protected",
    "quotient-decision",
    "dyadic-covers",
    "dual-covers",
    "factorized-regret",
)
TRACE_CAP = 24000
WALL_DEADLINES = (0.010, 0.050, 0.250, 0.500, 1.000)
WALL_CAP = 36000
DELTA = 0.05
C_UCT = 0.7
Q_CERT = 4


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_instances(smoke: bool = False) -> list[tuple[str, str, int, object, float]]:
    """Return list of (family, instance_id, rollout_seed, game, eps)."""
    items = []
    if smoke:
        g1, e1 = samegame_depth_case(5, 3, 630001, eps=0.08)
        items.append(("samegame_5x5_d3", "5x5_d3_s1", 630001, g1, e1))
        g2, e2 = samegame_standard_endgame(1, depth=3, eps=0.05)
        items.append(("samegame_std15x15_d3", "std_01_d3", 631001, g2, e2))
        return items

    for fam, side, depth, eps, seeds in BOARD_FAMILIES:
        for idx, s in enumerate(seeds, 1):
            game, ep = samegame_depth_case(side, depth, s, eps=eps)
            items.append((fam, f"{side}x{side}_d{depth}_s{idx}", s, game, ep))
    for idx in STD_INDICES:
        game3, ep3 = samegame_standard_endgame(idx, depth=3, eps=STD_EPS)
        items.append(("samegame_std15x15_d3", f"std_{idx:02d}_d3", 631000 + idx, game3, ep3))
    for idx in STD_INDICES:
        game4, ep4 = samegame_standard_endgame(idx, depth=4, eps=STD_EPS)
        items.append(("samegame_std15x15_d4", f"std_{idx:02d}_d4", 632000 + idx, game4, ep4))
    return items


def run_common_trace(game, eps: float, seed: int) -> dict:
    graph = game.graph
    values = graph.optimal_values(game.means)
    opt = values[graph.root]
    regrets = [max(0.0, opt - values[c]) for c in graph.children[graph.root]]

    uct = TranspositionUCT(graph, exploration=C_UCT, lazy=True)
    oracle = game.oracle(seed)
    mc = MarginalGraphMonitor(graph, mode="protected", delta=DELTA, schedule="box", simplify=True)
    me = ChargedDualCovers(graph, delta=DELTA, schedule="box", layout="best")

    qc = mc.query()
    qe = me.query()
    tau_conv = 0 if qc[1] <= eps else None
    act_conv = qc[0] if tau_conv is not None else None
    tau_exact = 0 if qe[1] <= eps else None
    act_exact = qe[0] if tau_exact is not None else None

    dirty = False
    while (tau_conv is None or tau_exact is None) and uct.calls < TRACE_CAP:
        path, reward = uct.step(oracle)
        c1 = mc.step(path[-1], reward)
        c2 = me.step(path[-1], reward)
        assert c1 == c2
        if mc.evidence.conflict:
            break
        if c1:
            dirty = True
        if dirty and uct.calls % Q_CERT == 0:
            dirty = False
            if tau_conv is None:
                qc = mc.query()
                if qc[1] <= eps:
                    tau_conv = uct.calls
                    act_conv = qc[0]
            if tau_exact is None:
                qe = me.query()
                if qe[1] <= eps:
                    tau_exact = uct.calls
                    act_exact = qe[0]

    if act_conv is not None:
        assert regrets[act_conv] <= eps + 1e-12
    if act_exact is not None:
        assert regrets[act_exact] <= eps + 1e-12
    if tau_conv is not None and tau_exact is not None:
        assert tau_exact <= tau_conv

    eff_c = tau_conv if tau_conv is not None else TRACE_CAP
    eff_e = tau_exact if tau_exact is not None else TRACE_CAP
    return {
        "tau_conv": tau_conv,
        "tau_exact": tau_exact,
        "capped_conv": eff_c,
        "capped_exact": eff_e,
        "ratio_capped": (eff_e / eff_c) if eff_c > 0 else 0.0,
        "conflict": mc.evidence.conflict,
    }


def run_timed(game, eps: float, seed: int, method: str, measure_memory: bool = False) -> dict:
    gc.collect()
    if measure_memory:
        tracemalloc.start()
    t0 = time.perf_counter()
    sess = CertifiedSearchSession(
        game, seed, "uct", method, eps,
        delta=DELTA, c_explore=C_UCT, q_cert=Q_CERT, schedule="box",
    )
    t_init = time.perf_counter() - t0
    init_work = sess.work
    prev_act = sess.action if sess.certified else 0
    checkpoints: list[int] = []

    def cross(el: float) -> None:
        while len(checkpoints) < len(WALL_DEADLINES) and WALL_DEADLINES[len(checkpoints)] < el:
            checkpoints.append(prev_act)

    cross(t_init)
    elapsed = t_init
    while (not sess.certified and not sess.monitor.evidence.conflict
           and sess.calls < WALL_CAP and elapsed < WALL_DEADLINES[-1]):
        sess.step()
        elapsed = time.perf_counter() - t0
        cross(elapsed)
        if not sess.certified and not sess.monitor.evidence.conflict:
            prev_act = sess.action

    calls = sess.calls
    cert = sess.certified
    act = sess.action
    work = sess.work
    mon_work = sess.monitor.work.total
    b = getattr(sess.monitor, "bounds", None)
    retired = getattr(b, "retired", 0)
    messages = getattr(b, "messages", getattr(sess.monitor, "messages", 0))

    peak_kib = None
    if measure_memory:
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        peak_kib = peak / 1024.0

    del b, sess
    end_s = time.perf_counter() - t0
    cross(end_s)
    returned = bool(cert and end_s <= WALL_DEADLINES[-1])
    if returned:
        prev_act = act
    checkpoints.extend([prev_act] * (len(WALL_DEADLINES) - len(checkpoints)))

    values = game.graph.optimal_values(game.means)
    opt = values[game.graph.root]
    ch = game.graph.children[game.graph.root]
    reg_curve = [max(0.0, opt - values[ch[a]]) for a in checkpoints]
    final_reg = max(0.0, opt - values[ch[act]])
    if cert:
        assert final_reg <= eps + 1e-12

    return {
        "method": method,
        "steps": calls,
        "certified": cert,
        "returned": returned,
        "init_ms": 1000.0 * t_init,
        "end_ms": 1000.0 * end_s,
        "restricted_ms": 1000.0 * (end_s if returned else WALL_DEADLINES[-1]),
        "init_work": init_work,
        "work": work,
        "monitor_work": mon_work,
        "messages": messages,
        "retired_edges": retired,
        "peak_kib": peak_kib,
        "regrets": reg_curve,
        "final_regret": final_reg,
    }


def summarize(dest: Path) -> dict:
    struct_rows = [json.loads(line) for line in (dest / "diagnostics_and_traces.jsonl").read_text().splitlines()]
    wall_rows = [json.loads(line) for line in (dest / "wall_runs.jsonl").read_text().splitlines()]
    mem_rows = [json.loads(line) for line in (dest / "memory_runs.jsonl").read_text().splitlines()]

    families = sorted(set(r["family"] for r in struct_rows))
    diag_csv = []
    for fam in families:
        grp = [r for r in struct_rows if r["family"] == fam]
        diag_csv.append({
            "family": fam,
            "n_instances": len(grp),
            "med_nodes": statistics.median(r["nodes"] for r in grp),
            "max_nodes": max(r["nodes"] for r in grp),
            "med_edges": statistics.median(r["edges"] for r in grp),
            "max_edges": max(r["edges"] for r in grp),
            "med_leaves": statistics.median(r["leaves"] for r in grp),
            "med_leaf_transposition_rate": statistics.median(r["leaf_transposition_rate"] for r in grp),
            "med_mean_membership": statistics.median(r["mean_membership"] for r in grp),
            "med_mean_jaccard": statistics.median(r["mean_jaccard"] for r in grp),
            "instances_with_containment": sum(r["containment_pairs"] > 0 for r in grp),
            "conv_certified": sum(r["tau_conv"] is not None for r in grp),
            "exact_certified": sum(r["tau_exact"] is not None for r in grp),
            "med_tau_conv": statistics.median(r["capped_conv"] for r in grp),
            "med_tau_exact": statistics.median(r["capped_exact"] for r in grp),
            "med_tau_ratio": statistics.median(r["ratio_capped"] for r in grp),
        })

    with (dest / "structural_and_trace_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(diag_csv[0].keys()))
        writer.writeheader()
        writer.writerows(diag_csv)

    perf_csv = []
    for fam in families:
        for meth in METHODS:
            grp = [r for r in wall_rows if (r["family"], r["method"]) == (fam, meth)]
            mgrp = [r["peak_kib"] for r in mem_rows if (r["family"], r["method"]) == (fam, meth) and r["peak_kib"] is not None]
            if not grp:
                continue
            perf_csv.append({
                "family": fam,
                "method": meth,
                "n_runs": len(grp),
                "returned": sum(int(r["returned"]) for r in grp),
                "med_restricted_ms": statistics.median(r["restricted_ms"] for r in grp),
                "mean_restricted_ms": statistics.mean(r["restricted_ms"] for r in grp),
                "med_work": statistics.median(r["work"] for r in grp),
                "med_peak_kib": statistics.median(mgrp) if mgrp else 0.0,
                "regret_10ms": statistics.mean(r["regrets"][0] for r in grp),
                "regret_50ms": statistics.mean(r["regrets"][1] for r in grp),
                "regret_250ms": statistics.mean(r["regrets"][2] for r in grp),
                "regret_500ms": statistics.mean(r["regrets"][3] for r in grp),
                "regret_1000ms": statistics.mean(r["regrets"][4] for r in grp),
            })

    with (dest / "performance_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(perf_csv[0].keys()))
        writer.writeheader()
        writer.writerows(perf_csv)

    out = {
        "total_instances": len(struct_rows),
        "total_wall_runs": len(wall_rows),
        "families": diag_csv,
    }
    (dest / "summary.json").write_text(json.dumps(out, indent=2))
    return out


def run(dest: Path = DEST, smoke: bool = False) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    print("[Exp 3] Building deeper SameGame DAG instances...", flush=True)
    instances = build_instances(smoke=smoke)
    print(f"  built {len(instances)} instances across {len(set(x[0] for x in instances))} families.", flush=True)

    print("[Exp 3] Step 1: Computing structural diagnostics & common-trace stopping...", flush=True)
    with (dest / "diagnostics_and_traces.jsonl").open("w") as out:
        for idx, (fam, inst_id, seed, game, eps) in enumerate(instances, 1):
            diag = structural_diagnostics(game.graph)
            tr = run_common_trace(game, eps, seed)
            row = {"family": fam, "instance": inst_id, "seed": seed, "epsilon": eps, **diag, **tr}
            out.write(json.dumps(row) + "\n")
            if idx % 10 == 0 or idx == len(instances):
                out.flush()
                print(f"  traces: {idx}/{len(instances)}", flush=True)

    print("[Exp 3] Step 2: Running counterbalanced cold wall-clock & anytime-regret runs...", flush=True)
    rng = random.Random(630999)
    blocks = []
    for idx, (fam, inst_id, seed, game, eps) in enumerate(instances):
        meths = list(METHODS)
        rng.shuffle(meths)
        blocks.append((idx, 0, meths))
        if not smoke:
            blocks.append((idx, 1, meths[::-1]))
    rng.shuffle(blocks)

    with (dest / "wall_runs.jsonl").open("w") as out:
        for b_i, (idx, rep, meths) in enumerate(blocks, 1):
            fam, inst_id, seed, game, eps = instances[idx]
            for pos, meth in enumerate(meths):
                row = run_timed(game, eps, seed, meth, measure_memory=False)
                row.update(family=fam, instance=inst_id, seed=seed, repeat=rep, position=pos)
                out.write(json.dumps(row) + "\n")
            if b_i % 20 == 0 or b_i == len(blocks):
                out.flush()
                print(f"  wall blocks: {b_i}/{len(blocks)}", flush=True)

    print("[Exp 3] Step 3: Measuring isolated peak memory...", flush=True)
    with (dest / "memory_runs.jsonl").open("w") as out:
        mem_subset = instances if smoke else [inst for i, inst in enumerate(instances) if i % 4 == 0]
        for fam, inst_id, seed, game, eps in mem_subset:
            for meth in METHODS:
                row = run_timed(game, eps, seed, meth, measure_memory=True)
                row.update(family=fam, instance=inst_id, seed=seed)
                out.write(json.dumps(row) + "\n")
        out.flush()

    manifest = {
        "experiment": "exp3_samegame_d3",
        "smoke": smoke,
        "methods": METHODS,
        "trace_cap": TRACE_CAP,
        "wall_deadlines": WALL_DEADLINES,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "sha256_traces": digest(dest / "diagnostics_and_traces.jsonl"),
        "sha256_wall": digest(dest / "wall_runs.jsonl"),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    if not smoke:
        agg = summarize(dest)
        print("[Exp 3] Summary completed:", len(agg["families"]), "families.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEST)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()
    if args.summarize_only:
        print(json.dumps(summarize(args.out), indent=2))
    else:
        run(args.out, smoke=args.smoke)
