"""Experiment 5 (Strengthening): Time-Uniform Empirical Bernstein vs. Hoeffding Boxes.

Evaluates predictable plug-in Empirical Bernstein confidence sequences (Waudby-Smith & Ramdas,
2024, Prop. 2; schedule='emp_bernstein') against time-uniform Hoeffding boxes (schedule='box')
for both Conventional Marginal certification and Exact Shared-Support Regret certification across:
1. All 58 deeper SameGame instances from Experiment 3:
   - 5x5 depth 3 (6 boards), 6x6 depth 3 (6 boards), 6x6 depth 4 (6 boards),
   - All 20 standard 15x15 endgames (StandardTestset.txt) at depth 3 and depth 4.
2. Controlled Bernoulli support-overlap DAGs (M=256, gap=0.32, rho in {0.00, 0.50, 0.75, 0.88})
   testing high-variance binary rewards alongside low-variance SameGame playouts.

Audits 100% empirical soundness (zero false certificates: true_regret <= eps on every certified run)
and measures both common-trace sample reductions and counterbalanced cold wall-clock speedups.
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

from joint_root_cert._core.certified_uct import TranspositionUCT
from joint_root_cert import CertifiedSearchSession
from joint_root_cert.benchmarks import (
    overlap_dag,
    samegame_depth_case,
    samegame_standard_endgame,
)
from joint_root_cert.certificates import ChargedDualCovers, MarginalGraphMonitor


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v3_strengthening/exp5_emp_bernstein"

BOARD_FAMILIES = (
    ("samegame_5x5_d3", 5, 3, 0.10, tuple(range(630001, 630007))),
    ("samegame_6x6_d3", 6, 3, 0.10, tuple(range(630101, 630107))),
    ("samegame_6x6_d4", 6, 4, 0.10, tuple(range(630201, 630207))),
)
STD_INDICES = tuple(range(1, 21))
STD_EPS = 0.08

OVERLAP_RHOS = (0.00, 0.50, 0.75, 0.88)
OVERLAP_SEEDS = tuple(range(610001, 610007))

COMBOS = (
    ("hoeff_conv", "quotient-protected", "box"),
    ("hoeff_exact", "dual-covers", "box"),
    ("eb_conv", "quotient-protected", "emp_bernstein"),
    ("eb_exact", "dual-covers", "emp_bernstein"),
)

SG_TRACE_CAP = 24000
OV_TRACE_CAP = 50000
WALL_LIMIT_S = 1.0
WALL_CAP = 36000
DELTA = 0.05
Q_CERT = 4


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_instances(smoke: bool = False) -> list[tuple[str, str, int, object, float, float, int]]:
    """Return list of (family, instance_id, seed, problem, eps, c_uct, trace_cap)."""
    items = []
    if smoke:
        g1, e1 = samegame_depth_case(5, 3, 630001, eps=0.10)
        items.append(("samegame_5x5_d3", "5x5_d3_s1", 630001, g1, e1, 0.7, 4000))
        g2, e2 = samegame_depth_case(6, 3, 630101, eps=0.10)
        items.append(("samegame_6x6_d3", "6x6_d3_s1", 630101, g2, e2, 0.7, 4000))
        g3, e3 = samegame_standard_endgame(1, depth=3, eps=0.08)
        items.append(("samegame_std15x15_d3", "std_01_d3", 631001, g3, e3, 0.7, 4000))
        p4, e4 = overlap_dag(256, 0.75, 0.32, 610001, noisy=True)
        items.append(("overlap_256_bernoulli_rho75", "ov256_r75_s1", 610001, p4, e4, 3.0, 6000))
        return items

    for fam, side, depth, eps, seeds in BOARD_FAMILIES:
        for idx, s in enumerate(seeds, 1):
            game, ep = samegame_depth_case(side, depth, s, eps=eps)
            items.append((fam, f"{side}x{side}_d{depth}_s{idx}", s, game, ep, 0.7, SG_TRACE_CAP))
    for idx in STD_INDICES:
        game3, ep3 = samegame_standard_endgame(idx, depth=3, eps=STD_EPS)
        items.append(("samegame_std15x15_d3", f"std_{idx:02d}_d3", 631000 + idx, game3, ep3, 0.7, SG_TRACE_CAP))
    for idx in STD_INDICES:
        game4, ep4 = samegame_standard_endgame(idx, depth=4, eps=STD_EPS)
        items.append(("samegame_std15x15_d4", f"std_{idx:02d}_d4", 632000 + idx, game4, ep4, 0.7, SG_TRACE_CAP))
    for rho in OVERLAP_RHOS:
        fam = f"overlap_256_bernoulli_rho{int(round(rho * 100)):02d}"
        for idx, s in enumerate(OVERLAP_SEEDS, 1):
            prob, ep = overlap_dag(256, rho, 0.32, s, noisy=True)
            items.append((fam, f"ov256_r{int(round(rho * 100)):02d}_s{idx}", s, prob, ep, 3.0, OV_TRACE_CAP))
    return items


def run_common_trace(prob, eps: float, seed: int, c_uct: float, cap: int) -> dict:
    graph = prob.graph
    values = graph.optimal_values(prob.means)
    opt = values[graph.root]
    regrets = [max(0.0, opt - values[c]) for c in graph.children[graph.root]]

    uct = TranspositionUCT(graph, exploration=c_uct, lazy=True)
    oracle = prob.oracle(seed)
    monitors = {
        "hoeff_conv": MarginalGraphMonitor(graph, mode="protected", delta=DELTA, schedule="box", simplify=True),
        "hoeff_exact": ChargedDualCovers(graph, delta=DELTA, schedule="box", layout="best"),
        "eb_conv": MarginalGraphMonitor(graph, mode="protected", delta=DELTA, schedule="emp_bernstein", simplify=True),
        "eb_exact": ChargedDualCovers(graph, delta=DELTA, schedule="emp_bernstein", layout="best"),
    }

    taus: dict[str, int | None] = {}
    acts: dict[str, int | None] = {}
    for k, mon in monitors.items():
        q = mon.query()
        if q[1] <= eps:
            taus[k] = 0
            acts[k] = q[0]
        else:
            taus[k] = None
            acts[k] = None

    dirty = {k: False for k in monitors}
    while any(v is None for v in taus.values()) and uct.calls < cap:
        path, reward = uct.step(oracle)
        leaf = path[-1]
        for k, mon in monitors.items():
            if taus[k] is None:
                if mon.step(leaf, reward):
                    dirty[k] = True
                if mon.evidence.conflict:
                    taus[k] = -1  # conflict sentinel
        if uct.calls % Q_CERT == 0:
            for k, mon in monitors.items():
                if taus[k] is None and dirty[k]:
                    dirty[k] = False
                    q = mon.query()
                    if q[1] <= eps:
                        taus[k] = uct.calls
                        acts[k] = q[0]

    conflicts = sum(1 for v in taus.values() if v == -1)
    false_certs = 0
    clean_taus: dict[str, int | None] = {}
    for k, v in taus.items():
        if v is not None and v >= 0:
            clean_taus[k] = v
            act = acts[k]
            assert act is not None
            if regrets[act] > eps + 1e-12:
                false_certs += 1
                raise AssertionError(f"False certificate in {k}: regret={regrets[act]} > eps={eps}")
        else:
            clean_taus[k] = None

    # Exact regret never requires more samples than conventional under the same schedule:
    if clean_taus["hoeff_conv"] is not None and clean_taus["hoeff_exact"] is not None:
        assert clean_taus["hoeff_exact"] <= clean_taus["hoeff_conv"]
    if clean_taus["eb_conv"] is not None and clean_taus["eb_exact"] is not None:
        assert clean_taus["eb_exact"] <= clean_taus["eb_conv"]

    eff = {k: (v if v is not None else cap) for k, v in clean_taus.items()}
    return {
        "cap": cap,
        "tau_hoeff_conv": clean_taus["hoeff_conv"],
        "tau_hoeff_exact": clean_taus["hoeff_exact"],
        "tau_eb_conv": clean_taus["eb_conv"],
        "tau_eb_exact": clean_taus["eb_exact"],
        "capped_hoeff_conv": eff["hoeff_conv"],
        "capped_hoeff_exact": eff["hoeff_exact"],
        "capped_eb_conv": eff["eb_conv"],
        "capped_eb_exact": eff["eb_exact"],
        "ratio_eb_vs_hoeff_exact": eff["eb_exact"] / eff["hoeff_exact"] if eff["hoeff_exact"] > 0 else 1.0,
        "ratio_eb_exact_vs_hoeff_conv": eff["eb_exact"] / eff["hoeff_conv"] if eff["hoeff_conv"] > 0 else 1.0,
        "conflicts": conflicts,
        "false_certificates": false_certs,
    }


def run_timed(prob, eps: float, seed: int, combo_key: str, method: str,
              schedule: str, c_uct: float, wall_limit: float) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    opt = values[prob.graph.root]
    regrets = [max(0.0, opt - values[c]) for c in prob.graph.children[prob.graph.root]]

    t0 = time.perf_counter()
    sess = CertifiedSearchSession(
        prob, seed, "uct", method, eps,
        delta=DELTA, c_explore=c_uct, q_cert=Q_CERT, schedule=schedule,
    )
    elapsed = time.perf_counter() - t0
    while (not sess.certified and not sess.monitor.evidence.conflict
           and sess.calls < WALL_CAP and elapsed < wall_limit):
        sess.step()
        elapsed = time.perf_counter() - t0
    cert = sess.certified
    act = sess.action
    calls = sess.calls
    work = sess.work
    conflict = sess.monitor.evidence.conflict
    del sess
    total_s = time.perf_counter() - t0

    true_reg = regrets[act]
    if cert:
        assert true_reg <= eps + 1e-12, f"False certificate {combo_key}: {true_reg} > {eps}"
    return {
        "combo": combo_key,
        "method": method,
        "schedule": schedule,
        "certified": cert,
        "conflict": conflict,
        "false_certificate": bool(cert and true_reg > eps + 1e-12),
        "steps": calls,
        "total_s": total_s,
        "total_work": work,
        "final_simple_regret": true_reg,
    }


def summarize(dest: Path) -> None:
    traces = [json.loads(line) for line in (dest / "common_traces.jsonl").read_text().splitlines() if line.strip()]
    walls = [json.loads(line) for line in (dest / "wall_runs.jsonl").read_text().splitlines() if line.strip()]

    fams = sorted({r["family"] for r in traces})
    trace_rows = []
    for fam in fams:
        sub = [r for r in traces if r["family"] == fam]
        n = len(sub)
        trace_rows.append({
            "family": fam,
            "instances": n,
            "cert_hoeff_conv": round(sum(1 for r in sub if r["tau_hoeff_conv"] is not None) / n, 4),
            "cert_hoeff_exact": round(sum(1 for r in sub if r["tau_hoeff_exact"] is not None) / n, 4),
            "cert_eb_conv": round(sum(1 for r in sub if r["tau_eb_conv"] is not None) / n, 4),
            "cert_eb_exact": round(sum(1 for r in sub if r["tau_eb_exact"] is not None) / n, 4),
            "median_capped_hoeff_conv": round(statistics.median(r["capped_hoeff_conv"] for r in sub), 1),
            "median_capped_hoeff_exact": round(statistics.median(r["capped_hoeff_exact"] for r in sub), 1),
            "median_capped_eb_conv": round(statistics.median(r["capped_eb_conv"] for r in sub), 1),
            "median_capped_eb_exact": round(statistics.median(r["capped_eb_exact"] for r in sub), 1),
            "median_ratio_eb_vs_hoeff_exact": round(statistics.median(r["ratio_eb_vs_hoeff_exact"] for r in sub), 4),
            "median_ratio_eb_exact_vs_hoeff_conv": round(statistics.median(r["ratio_eb_exact_vs_hoeff_conv"] for r in sub), 4),
            "conflicts": sum(r["conflicts"] for r in sub),
            "false_certificates": sum(r["false_certificates"] for r in sub),
        })

    with (dest / "summary_traces.csv").open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(trace_rows[0].keys()))
        writer.writeheader()
        writer.writerows(trace_rows)

    wall_rows = []
    for fam in sorted({r["family"] for r in walls}):
        for combo_key, _, _ in COMBOS:
            sub = [r for r in walls if r["family"] == fam and r["combo"] == combo_key]
            if not sub:
                continue
            wall_rows.append({
                "family": fam,
                "combo": combo_key,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 3),
                "median_steps": round(statistics.median(r["steps"] for r in sub), 1),
                "median_work": round(statistics.median(r["total_work"] for r in sub), 1),
                "mean_final_regret": round(statistics.mean(r["final_simple_regret"] for r in sub), 5),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_wall.csv").open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(wall_rows[0].keys()))
        writer.writeheader()
        writer.writerows(wall_rows)

    key_findings = {
        "total_common_traces": len(traces),
        "total_wall_runs": len(walls),
        "total_false_certificates": sum(r["false_certificates"] for r in trace_rows) + sum(r["false_certificates"] for r in wall_rows),
        "total_conflicts": sum(r["conflicts"] for r in trace_rows),
        "traces_by_family": trace_rows,
        "wall_by_family": wall_rows,
    }
    (dest / "summary.json").write_text(json.dumps(key_findings, indent=2))


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
    instances = build_instances(smoke=args.smoke)
    repeats = 1 if args.smoke else 2
    wall_limit = 0.20 if args.smoke else WALL_LIMIT_S

    # Warm up JIT/imports/allocators
    w_prob, w_eps = samegame_depth_case(5, 3, 630001, eps=0.10)
    for key, meth, sched in COMBOS:
        run_timed(w_prob, w_eps, 630001, key, meth, sched, 0.7, 0.05)

    traces_path = dest / "common_traces.jsonl"
    wall_path = dest / "wall_runs.jsonl"
    rng = random.Random(20261117)

    with traces_path.open("w") as ft, wall_path.open("w") as fw:
        for idx, (fam, inst_id, seed, prob, eps, c_uct, cap) in enumerate(instances, 1):
            tr = run_common_trace(prob, eps, seed, c_uct, cap)
            ft.write(json.dumps({"family": fam, "instance": inst_id, "seed": seed, "eps": eps, **tr}) + "\n")
            ft.flush()

            # Counterbalanced timed runs across the 4 (certificate, schedule) combinations
            # On 20-board SameGame cohorts, 1 counterbalanced order per board already gives 20 paired runs;
            # on 6-seed families, run `repeats` counterbalanced orders (12 runs/combo).
            fam_repeats = 1 if (not args.smoke and fam.startswith("samegame_std15x15")) else repeats
            for rep in range(fam_repeats):
                order = list(COMBOS)
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                for key, meth, sched in order:
                    wr = run_timed(prob, eps, seed + 10000 * rep, key, meth, sched, c_uct, wall_limit)
                    fw.write(json.dumps({
                        "family": fam,
                        "instance": inst_id,
                        "seed": seed + 10000 * rep,
                        "repeat": rep,
                        "eps": eps,
                        **wr,
                    }) + "\n")
                fw.flush()

    summarize(dest)
    manifest = {
        "experiment": "exp5_emp_bernstein",
        "smoke": args.smoke,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "sha256_common_traces": digest(traces_path),
        "sha256_wall_runs": digest(wall_path),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"Done exp5_emp_bernstein in {manifest['elapsed_s']}s -> {dest}")


if __name__ == "__main__":
    main()
