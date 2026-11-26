"""Experiment 7 (Strengthening): Native -O3 C++17 Micro-Kernels & Interpreter-Free Scaling.

Eliminates Python interpreter constant-factor concerns by benchmarking native `-O3 -std=c++17`
implementations (`dag_mcts/_cpp_kernels.cpp`, timed via `std::chrono::steady_clock` including
cold allocation/compilation and RAII disposal) after verifying bit-exact replay parity with Python.

Evaluates four core regimes (8 seeds x 2 counterbalanced repeats = 16 cold C++17 runs/cell):
1. Suite A (UCT Horizon-Gap Intervention & Frontier Sparsity Paradox):
   `funnel_2exit` (exact Table 2 construction, m=256, gap in {0.200, 0.075, 0.035}) and
   `shared_2exit` (`puct_noisy_funnel`, m=256, gap in {0.200, 0.075, 0.035}) under TA-UCT.
2. Suite B (Uncensored Deterministic Root-PUCT Polynomial Separation up to m=4096):
   `puct_root_funnel` across m in {16, 64, 256, 1024, 4096} (Theorem 4.1).
3. Suite C (Every-Layout Parity Grid Lower Bound, r in {8, 16, 32}):
   `coded(r)` with M in {65, 257, 1025} leaves comparing `direct-graph-regret`,
   `protected-selective`, `graph-eager`, and `dual-covers` (Theorem 4.5).
4. Suite D (Support-Overlap Exact Regret + Empirical Bernstein in Native C++17):
   Bernoulli `overlap_dag` (M=256, gap=0.32, rho in {0.00, 0.50, 0.75, 0.88, 1.00})
   under both `box` and `emp_bernstein` schedules.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import time

from dagcert import CertifiedSearchSession
from dagcert.benchmarks import (
    overlap_dag,
    puct_noisy_funnel,
    puct_root_funnel,
)
from dagcert.search import CppKernelRunner, SplitMixProblem
from experiment.simulated.passive_uct.uct_backup_families import funnel
from experiment.simulated.passive_uct.uct_frontier_families import coded


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v3_strengthening/exp7_cpp_kernels"

SEEDS = tuple(range(670001, 670009))  # 8 seeds x 2 counterbalanced repeats = 16 runs/cell
DELTA = 0.05


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_parity_audit(dest: Path, smoke: bool = False) -> dict:
    """Verify bit-exact stopping, action, strict-change, message, and retirement parity."""
    p_ov, e_ov = overlap_dag(64, 0.75, 0.42, seed=671001, noisy=True)
    p_fn, e_fn = puct_noisy_funnel(64, seed=671002, gap=0.14, noisy=True)
    p_cd, e_cd = coded(8, seed=671003)
    p_rt, e_rt = puct_root_funnel(64, seed=671004, alpha=0.25)

    cases = [
        ("overlap_64_box", SplitMixProblem("ov_box", p_ov.graph, p_ov.means, 1), e_ov,
         "uct", 3.0, 4, "box", 0, ("graph-eager", "protected-selective", "decision-selective", "dual-covers", "direct-graph-regret")),
        ("overlap_64_eb", SplitMixProblem("ov_eb", p_ov.graph, p_ov.means, 1), e_ov,
         "uct", 3.0, 4, "emp_bernstein", 0, ("graph-eager", "protected-selective", "decision-selective", "dual-covers", "direct-graph-regret")),
        ("parity_8_box", SplitMixProblem("cd_box", p_cd.graph, p_cd.means, 2), e_cd,
         "uct", 3.0, 4, "box", 0, ("graph-eager", "protected-selective", "decision-selective", "dual-covers", "direct-graph-regret")),
        ("uct_funnel_64", SplitMixProblem("fn_box", p_fn.graph, p_fn.means, 1), e_fn,
         "uct", 0.7, 1, "box", 0, ("graph-eager", "protected-selective", "decision-selective", "dual-covers")),
        ("root_puct_64", SplitMixProblem("rt_box", p_rt.graph, p_rt.means, 0), e_rt,
         "root_puct", 3.0, 1, "box", 3, ("graph-eager", "protected-selective", "decision-selective", "dual-covers")),
    ]
    if smoke:
        cases = cases[:2]

    records = []
    cap = 5000 if smoke else 30000
    for label, sm_prob, eps, policy, c_exp, q_cert, sched, eff_m, methods in cases:
        seed = 54321
        for meth in methods:
            if policy == "uct":
                py_s = CertifiedSearchSession(
                    sm_prob, seed, "uct", meth, eps,
                    delta=DELTA, c_explore=c_exp, q_cert=q_cert, schedule=sched,
                )
                py_s.policy.lazy = False
                py_s.policy.lazy_nodes = [False] * len(sm_prob.graph)
            else:
                py_s = CertifiedSearchSession(
                    sm_prob, seed, "root_puct", meth, eps,
                    delta=DELTA, c_explore=c_exp, prior_mode="unit_lambda",
                    q_cert=q_cert, schedule=sched, downstream="fixed_first", effective_m=eff_m,
                )
            t_py0 = time.perf_counter()
            while not py_s.certified and py_s.calls < cap:
                py_s.step()
            py_ms = 1e3 * (time.perf_counter() - t_py0)

            cpp_r = CppKernelRunner.run(
                sm_prob, seed, policy, meth, eps,
                delta=DELTA, c_explore=c_exp, q_cert=q_cert,
                schedule=sched, effective_m=eff_m, cap=cap,
            )
            assert cpp_r["certified"] == py_s.certified, f"{label}/{meth}: certified mismatch"
            assert cpp_r["steps"] == py_s.calls, f"{label}/{meth}: steps {cpp_r['steps']} != {py_s.calls}"
            assert cpp_r["action"] == py_s.action, f"{label}/{meth}: action mismatch"
            assert cpp_r["strict_changes"] == py_s.monitor.evidence.strict_changes
            if meth in ("graph-eager", "protected-selective", "decision-selective"):
                assert cpp_r["messages"] == py_s.monitor.bounds.messages
                assert cpp_r["retired"] == py_s.monitor.bounds.retired

            cpp_ms = cpp_r["end_ms"]
            records.append({
                "case": label,
                "method": meth,
                "steps": cpp_r["steps"],
                "certified": cpp_r["certified"],
                "python_ms": round(py_ms, 3),
                "cpp_ms": round(cpp_ms, 4),
                "cpp_speedup_over_python": round(py_ms / max(cpp_ms, 1e-6), 1),
                "discrepancies": 0,
            })

    audit = {
        "checks": len(records),
        "zero_discrepancies": True,
        "median_cpp_speedup_over_python": round(statistics.median(r["cpp_speedup_over_python"] for r in records), 1),
        "records": records,
    }
    (dest / "parity_audit.json").write_text(json.dumps(audit, indent=2))
    return audit


def build_tasks(smoke: bool = False) -> list[dict]:
    seeds = SEEDS[:2] if smoke else SEEDS
    tasks = []

    # Suite A: UCT Horizon-Gap Intervention (exact Table 2 funnel_2exit & shared_2exit, eps=0.025)
    for gap in ((0.200, 0.035) if smoke else (0.200, 0.075, 0.035)):
        for s in seeds:
            p1, _ = funnel(256, s, noisy=False, placement="low", exits=2, gap=gap)
            tasks.append({
                "suite": "uct_funnel_gap",
                "family": f"table2_funnel256_g{int(round(gap*1000)):03d}",
                "param": gap, "m": 256, "seed": s,
                "sm_prob": SplitMixProblem("f2", p1.graph, p1.means, 0),
                "eps": 0.025, "policy": "uct", "c_explore": 2.0, "q_cert": 1,
                "schedule": "box", "effective_m": 0, "cap": 60000 if smoke else 200000,
                "methods": ("graph-eager", "protected-selective", "decision-selective", "dual-covers"),
            })
            p2, e2 = puct_noisy_funnel(256, s, gap=gap, noisy=True)
            tasks.append({
                "suite": "uct_shared_funnel_gap",
                "family": f"shared_funnel256_g{int(round(gap*1000)):03d}",
                "param": gap, "m": 256, "seed": s,
                "sm_prob": SplitMixProblem("sf2", p2.graph, p2.means, 1),
                "eps": max(0.04, e2), "policy": "uct", "c_explore": 0.7, "q_cert": 1,
                "schedule": "box", "effective_m": 0, "cap": 60000 if smoke else 200000,
                "methods": ("graph-eager", "protected-selective", "decision-selective", "dual-covers"),
            })

    # Suite B: Uncensored Deterministic Root-PUCT Scaling up to m = 4096
    for m in ((16, 256) if smoke else (16, 64, 256, 1024, 4096)):
        for s in seeds:
            p, e = puct_root_funnel(m, seed=s, alpha=0.25)
            tasks.append({
                "suite": "root_puct_scaling",
                "family": f"root_puct_m{m:04d}",
                "param": float(m), "m": m, "seed": s,
                "sm_prob": SplitMixProblem("rp", p.graph, p.means, 0),
                "eps": e, "policy": "root_puct", "c_explore": 3.0, "q_cert": 1,
                "schedule": "box", "effective_m": 3, "cap": 60000 if smoke else 300000,
                "methods": ("graph-eager", "protected-selective", "decision-selective", "dual-covers"),
            })

    # Suite C: Every-Layout Parity Grid (r in {8, 16, 32})
    for r in ((8, 16) if smoke else (8, 16, 32)):
        for s in seeds:
            p, e = coded(r, seed=s)
            tasks.append({
                "suite": "parity_grid",
                "family": f"parity_r{r:02d}",
                "param": float(r), "m": len(p.graph.leaves), "seed": s,
                "sm_prob": SplitMixProblem("cd", p.graph, p.means, 2),
                "eps": e, "policy": "uct", "c_explore": 3.0, "q_cert": 4,
                "schedule": "box", "effective_m": 0, "cap": 20000 if smoke else 100000,
                "methods": ("graph-eager", "protected-selective", "decision-selective", "dual-covers", "direct-graph-regret"),
            })

    # Suite D: Support-Overlap Exact Regret + Empirical Bernstein in C++17
    for sched in (("box", "emp_bernstein") if not smoke else ("box",)):
        for rho in ((0.00, 0.75) if smoke else (0.00, 0.50, 0.75, 0.88, 1.00)):
            for s in seeds:
                p, e = overlap_dag(256, rho, 0.32, s, noisy=True)
                tasks.append({
                    "suite": f"overlap_{sched}",
                    "family": f"overlap256_{sched}_rho{int(round(rho*100)):02d}",
                    "param": rho, "m": 256, "seed": s,
                    "sm_prob": SplitMixProblem("ov", p.graph, p.means, 1),
                    "eps": e, "policy": "uct", "c_explore": 3.0, "q_cert": 4,
                    "schedule": sched, "effective_m": 0, "cap": 20000 if smoke else 80000,
                    "methods": ("protected-selective", "dual-covers", "direct-graph-regret"),
                })
    return tasks


def summarize(dest: Path) -> None:
    runs = [json.loads(line) for line in (dest / "runs.jsonl").read_text().splitlines() if line.strip()]
    audit = json.loads((dest / "parity_audit.json").read_text())

    rows = []
    for fam in sorted({r["family"] for r in runs}):
        sub_f = [r for r in runs if r["family"] == fam]
        suite = sub_f[0]["suite"]
        param = sub_f[0]["param"]
        m = sub_f[0]["m"]
        methods_present = []
        for cand in ("graph-eager", "protected-selective", "decision-selective", "dual-covers", "direct-graph-regret"):
            if any(r["method"] == cand for r in sub_f):
                methods_present.append(cand)
        for meth in methods_present:
            sub = [r for r in sub_f if r["method"] == meth]
            rows.append({
                "suite": suite,
                "family": fam,
                "param": param,
                "m": m,
                "method": meth,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_steps": round(statistics.median(r["steps"] for r in sub), 1),
                "median_init_us": round(statistics.median(r["init_us"] for r in sub), 2),
                "median_total_us": round(statistics.median(r["total_us"] for r in sub), 2),
                "median_total_ms": round(statistics.median(r["end_ms"] for r in sub), 4),
                "median_work": round(statistics.median(r["work"] for r in sub), 1),
                "median_messages": round(statistics.median(r["messages"] for r in sub), 1),
                "median_retired": round(statistics.median(r["retired"] for r in sub), 1),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })

    with (dest / "summary_by_family.csv").open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    summary = {
        "total_cpp_runs": len(runs),
        "total_false_certificates": sum(r["false_certificates"] for r in rows),
        "parity_audit": {
            "checks": audit["checks"],
            "zero_discrepancies": audit["zero_discrepancies"],
            "median_cpp_speedup_over_python": audit["median_cpp_speedup_over_python"],
        },
        "by_family": rows,
    }
    (dest / "summary.json").write_text(json.dumps(summary, indent=2))


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
    CppKernelRunner.ensure_loaded()
    run_parity_audit(dest, smoke=args.smoke)

    tasks = build_tasks(smoke=args.smoke)
    repeats = 1 if args.smoke else 2
    runs_path = dest / "runs.jsonl"
    rng = random.Random(20261119)

    with runs_path.open("w") as fh:
        for t in tasks:
            sm_prob: SplitMixProblem = t["sm_prob"]
            values = sm_prob.graph.optimal_values(sm_prob.means)
            opt = values[sm_prob.graph.root]
            regrets = [max(0.0, opt - values[c]) for c in sm_prob.graph.children[sm_prob.graph.root]]

            for rep in range(repeats):
                order = list(t["methods"])
                rng.shuffle(order)
                if rep % 2 == 1:
                    order.reverse()
                run_seed = t["seed"] + 10000 * rep
                for meth in order:
                    res = CppKernelRunner.run(
                        sm_prob, run_seed, t["policy"], meth, t["eps"],
                        delta=DELTA, c_explore=t["c_explore"], q_cert=t["q_cert"],
                        schedule=t["schedule"], effective_m=t["effective_m"], cap=t["cap"],
                    )
                    act = res["action"]
                    true_reg = regrets[act] if 0 <= act < len(regrets) else 1.0
                    false_cert = bool(res["certified"] and true_reg > t["eps"] + 1e-12)
                    assert not false_cert, f"False C++ certificate in {t['family']}/{meth}"
                    fh.write(json.dumps({
                        "suite": t["suite"],
                        "family": t["family"],
                        "param": t["param"],
                        "m": t["m"],
                        "seed": run_seed,
                        "repeat": rep,
                        "method": meth,
                        "schedule": t["schedule"],
                        "false_certificate": false_cert,
                        **res,
                    }) + "\n")
                fh.flush()

    summarize(dest)
    manifest = {
        "experiment": "exp7_cpp_kernels",
        "smoke": args.smoke,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "elapsed_s": round(time.perf_counter() - t_start, 2),
        "sha256_runs": digest(runs_path),
        "sha256_parity_audit": digest(dest / "parity_audit.json"),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"Done exp7_cpp_kernels in {manifest['elapsed_s']}s -> {dest}")


if __name__ == "__main__":
    main()
