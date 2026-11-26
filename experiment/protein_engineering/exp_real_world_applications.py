"""Experiment 12 (ICML v6): Real-World Shared-Support Certification Benchmarks
(Combinatorial Protein Engineering on Measured GB1 & Multi-Stage LLM Agent Workflows on WorFBench).

Evaluates 7 methods under matched `(eps, delta)` (`delta = 0.05`), identical
time-uniform Empirical Bernstein (`emp_bernstein`) nested terminal confidence boxes,
and paired deterministic SplitMix64 observation streams:
  - `flat_lucb`: Flat Best-Arm Identification (`LUCB1` over `Z`, ignoring the root-action graph)
  - `lucb_micro_marg`: `LUCB-micro` (Huang et al., ALT 2017) with DAG transposition pooling
  - `ugape_dag_marg`: `UGapE-MCTS` (Kaufmann & Koolen, NeurIPS 2017) on the DAG
  - `varde_exact`: Variance-decrement allocation (inspired by VarDE, ICML 2026) + exact witnesses
  - `exact_dag_lucb`: `Exact-Regret-DAG-LUCB` (`UCB-inside`, Theorem 3.1)
  - `safeguarded_lcb`: `Safeguarded-LCB` (`DualWitnessCovers` slack gate)
  - `opt_sep`: `Optimistic-Separation DAG-LUCB` (Theorem 3.2)

Three experimental parts:
1. Part A (`gb1_campaigns_runs.jsonl`):
   10 real 4-site GB1 starting sequences (`VDGV` [wild-type], `FDGV`, `LDGV`, `WDGV`,
   `YDGV`, `IDGV`, `ADGV`, `VDGA`, `VWGV`, `LWGV`) from Wu et al. (*eLife* 2016) under
   3-round combinatorial mutagenesis (`panel5`, `K = 18..19`, `M = 393..540` measured
   variants, strictly zero support containments), spanning both single-peak shared
   epistasis (`Gamma / Delta_flat in [1.0, 3.1]`, up to `8.76x` wild-type binding `FWAA`)
   and multi-sequence epistatic ridges (`Gamma / Delta_flat in [13.2, 36.0]`).
2. Part B (`gb1_panel_sweep_runs.jsonl`):
   Library-scale & overlap sweep across focused codon panels `panel4` (`M ~ 260`),
   `panel5` (`M ~ 490`), `panel6` (`M ~ 850`), and `panel8` (`M ~ 1,805`) on `FDGV`,
   `VDGV`, and `ADGV`.
3. Part C (`worfbench_runs.jsonl`):
   Behaviorally exact 4-stage `Qwen3-0.6B` + `Qwen3-Embedding-0.6B` agentic workflow
   commitment across `WorFBench` (*ICLR 2025*) held-out graph-planning tasks (`all`,
   `toolbench`, `toolalpaca`, `seal_tools`, `webshop`; `K = 8`, `M = 32..64` canonical
   workflows, strictly zero support containments), where each pull evaluates a real
   held-out task with the official `WorFEval` subgraph-matching F1 metric.
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

from joint_root_cert.tracking import (
    LUCBMicroSession,
    UGapEMCTSSession,
    VarDEDAGSession,
)
from joint_root_cert import HybridWitnessDAGLUCBSession
from joint_root_cert._core.v6_real_world import (
    FlatLUCBSession,
    GB1MutationCampaignProblem,
    WorFBenchWorkflowProblem,
    gb1_mean_to_raw_fitness,
    real_world_problem_diagnostics,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v4_icml_baselines/exp12_real_world"

METHODS = (
    "flat_lucb",
    "lucb_micro_marg",
    "ugape_dag_marg",
    "varde_exact",
    "exact_dag_lucb",
    "safeguarded_lcb",
    "opt_sep",
)

GB1_TEMPLATES = (
    "VDGV",  # Wild-type GB1 (epistatic ridge: Gamma / flat_gap = 13.2x)
    "FDGV",  # V39F (reaches global #1 binder FWAA = 8.762x WT; Gamma / flat_gap = 3.1x)
    "LDGV",  # V39L (reaches LWCA = 7.229x WT; Gamma / flat_gap = 1.5x)
    "WDGV",  # V39W (reaches WWCA = 7.282x WT; Gamma / flat_gap = 2.5x)
    "YDGV",  # V39Y (reaches YWCA = 6.981x WT; Gamma / flat_gap = 2.6x)
    "IDGV",  # V39I (epistatic ridge: Gamma / flat_gap = 36.0x)
    "ADGV",  # V39A (epistatic ridge: Gamma / flat_gap = 18.8x)
    "VDGA",  # V54A (reaches WWCA = 7.282x WT; Gamma / flat_gap = 1.0x control)
    "VWGV",  # D40W (reaches WWCA = 7.282x WT; Gamma / flat_gap = 2.3x)
    "LWGV",  # V39L+D40W (epistatic ridge: Gamma / flat_gap = 32.9x)
)

GB1_SEEDS = tuple(range(760001, 760007))       # 6 seeds/template -> 420 runs in Part A
SWEEP_PANELS = ("panel4", "panel5", "panel6", "panel8")
SWEEP_TEMPLATES = ("FDGV", "VDGV", "ADGV")
SWEEP_SEEDS = tuple(range(770001, 770005))     # 4 seeds/cell -> 336 runs in Part B

WORFBENCH_DOMAINS = ("all", "toolbench", "toolalpaca", "seal_tools", "webshop")
WORFBENCH_BASES = (
    ("default_0000_u3", (0, 0, 0, 0), 3),
    ("default_0000_u2", (0, 0, 0, 0), 2),
    ("compact_1000_u3", (1, 0, 0, 0), 3),
    ("cot_0100_u3", (0, 1, 0, 0), 3),
)
WORFBENCH_SEEDS = tuple(range(780001, 780007))  # 6 seeds/campaign -> 840 runs in Part C

DELTA = 0.05
SCHEDULE = "emp_bernstein"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    return sess.evidence.conflict


def make_session(prob, eps: float, seed: int, method: str):
    if method == "flat_lucb":
        return FlatLUCBSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE)
    if method == "lucb_micro_marg":
        return LUCBMicroSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE, stop_rule="marginal")
    if method == "ugape_dag_marg":
        return UGapEMCTSSession(
            prob, seed, eps, delta=DELTA, schedule=SCHEDULE, mode="dag", stop_rule="marginal"
        )
    if method == "varde_exact":
        return VarDEDAGSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE, witness_mode="exact")
    if method == "exact_dag_lucb":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="ucb", delta=DELTA, schedule=SCHEDULE)
    if method == "safeguarded_lcb":
        return HybridWitnessDAGLUCBSession(
            prob, seed, eps, mode="hybrid", delta=DELTA, schedule=SCHEDULE
        )
    if method == "opt_sep":
        return HybridWitnessDAGLUCBSession(
            prob, seed, eps, mode="opt_sep", delta=DELTA, schedule=SCHEDULE
        )
    raise ValueError(f"Unknown method: {method}")


def run_one(
    prob,
    eps: float,
    seed: int,
    method: str,
    wall_limit: float,
    cap: int,
) -> dict:
    gc.collect()
    values = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt = values[prob.graph.root]
    regrets = [max(0.0, opt - values[c]) for c in root_ch]

    t0 = time.perf_counter()
    sess = make_session(prob, eps, seed, method)
    elapsed = time.perf_counter() - t0
    while (
        not sess.certified
        and not _has_conflict(sess)
        and sess.calls < cap
        and elapsed < wall_limit
    ):
        sess.step()
        elapsed = time.perf_counter() - t0

    cert = bool(sess.certified)
    act = int(sess.action)
    calls = int(sess.calls)
    work = int(sess.work)
    del sess
    total_s = time.perf_counter() - t0

    sel_val = values[root_ch[act]]
    true_reg = regrets[act]
    false_cert = bool(cert and true_reg > eps + 1e-12)
    assert not false_cert, f"False certificate in {method} on {prob.name}: {true_reg} > {eps}"

    rec: dict = {
        "problem": prob.name,
        "method": method,
        "seed": seed,
        "eps": eps,
        "certified": cert,
        "false_certificate": false_cert,
        "steps": calls,
        "capped_steps": calls if cert else cap,
        "cap": cap,
        "total_s": round(total_s, 6),
        "total_work": work,
        "action_idx": act,
        "action_label": prob.action_labels[act],
        "v_star": round(opt, 6),
        "selected_action_value": round(sel_val, 6),
        "final_simple_regret": round(true_reg, 6),
    }
    if hasattr(prob, "raw_fitness"):
        opt_fit = gb1_mean_to_raw_fitness(opt)
        sel_fit = gb1_mean_to_raw_fitness(sel_val)
        rec["opt_raw_fitness"] = round(opt_fit, 4)
        rec["selected_raw_fitness"] = round(sel_fit, 4)
        rec["raw_fitness_regret"] = round(max(0.0, opt_fit - sel_fit), 4)
    elif hasattr(prob, "base_mean_f1"):
        rec["base_mean_f1"] = round(prob.base_mean_f1, 5)
        rec["opt_f1"] = round(opt, 5)
        rec["selected_f1"] = round(sel_val, 5)
        rec["f1_gain_over_base"] = round(sel_val - prob.base_mean_f1, 5)
    return rec


def summarize(dest: Path) -> None:
    gb1_runs = [
        json.loads(line)
        for line in (dest / "gb1_campaigns_runs.jsonl").read_text().splitlines()
        if line.strip()
    ]
    sweep_runs = [
        json.loads(line)
        for line in (dest / "gb1_panel_sweep_runs.jsonl").read_text().splitlines()
        if line.strip()
    ]
    wf_runs = [
        json.loads(line)
        for line in (dest / "worfbench_runs.jsonl").read_text().splitlines()
        if line.strip()
    ]

    # 1. GB1 overall + ridge/single-peak stratified method summary
    gb1_method_rows = []
    for stratum in ("all", "epistatic_ridge", "single_peak"):
        for m in METHODS:
            sub = [
                r
                for r in gb1_runs
                if r["method"] == m
                and (stratum == "all" or r["regime"] == stratum)
            ]
            if not sub:
                continue
            gb1_method_rows.append({
                "stratum": stratum,
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "mean_capped_steps": round(statistics.fmean(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 2),
                "mean_selected_raw_fitness": round(
                    statistics.fmean(r["selected_raw_fitness"] for r in sub), 4
                ),
                "mean_raw_fitness_regret": round(
                    statistics.fmean(r["raw_fitness_regret"] for r in sub), 4
                ),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })
    with (dest / "summary_gb1_by_method.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(gb1_method_rows[0].keys()))
        w.writeheader()
        w.writerows(gb1_method_rows)

    # 2. GB1 per-template summary (for ridge-ratio scatter & appendix table)
    tmpl_rows = []
    for tmpl in GB1_TEMPLATES:
        sub_t = [r for r in gb1_runs if r["start_seq"] == tmpl]
        if not sub_t:
            continue
        for m in METHODS:
            sub = [r for r in sub_t if r["method"] == m]
            if not sub:
                continue
            r0 = sub[0]
            tmpl_rows.append({
                "start_seq": tmpl,
                "regime": r0["regime"],
                "leaves": r0["leaves"],
                "root_actions": r0["root_actions"],
                "gamma": r0["exterior_margin_gamma"],
                "flat_gap": r0["flat_top2_gap"],
                "gamma_over_flat": r0["gamma_over_flat"],
                "opt_raw_fitness": r0["opt_raw_fitness"],
                "method": m,
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "mean_selected_raw_fitness": round(
                    statistics.fmean(r["selected_raw_fitness"] for r in sub), 4
                ),
            })
    with (dest / "summary_gb1_by_template.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(tmpl_rows[0].keys()))
        w.writeheader()
        w.writerows(tmpl_rows)

    # 3. GB1 codon-panel / library-scale sweep summary
    sw_rows = []
    for pan in SWEEP_PANELS:
        sub_p = [r for r in sweep_runs if r["panel"] == pan]
        if not sub_p:
            continue
        for m in METHODS:
            sub = [r for r in sub_p if r["method"] == m]
            if not sub:
                continue
            sw_rows.append({
                "panel": pan,
                "mean_leaves": round(statistics.fmean(r["leaves"] for r in sub), 1),
                "mean_jaccard": round(statistics.fmean(r["mean_pairwise_jaccard"] for r in sub), 4),
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "mean_selected_raw_fitness": round(
                    statistics.fmean(r["selected_raw_fitness"] for r in sub), 4
                ),
            })
    with (dest / "summary_gb1_panel_sweep.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(sw_rows[0].keys()))
        w.writeheader()
        w.writerows(sw_rows)

    # 4. WorFBench per-domain + overall summary
    wf_dom_rows = []
    for dom in ("OVERALL", *WORFBENCH_DOMAINS):
        for m in METHODS:
            sub = [
                r
                for r in wf_runs
                if r["method"] == m and (dom == "OVERALL" or r["domain"] == dom)
            ]
            if not sub:
                continue
            wf_dom_rows.append({
                "domain": dom,
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "mean_capped_steps": round(statistics.fmean(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 2),
                "mean_selected_f1": round(statistics.fmean(r["selected_f1"] for r in sub), 4),
                "mean_f1_gain_over_base": round(
                    statistics.fmean(r["f1_gain_over_base"] for r in sub), 4
                ),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })
    with (dest / "summary_worfbench_by_domain.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(wf_dom_rows[0].keys()))
        w.writeheader()
        w.writerows(wf_dom_rows)


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

    rng = random.Random(20261118)

    # ---------------- Part A: Real GB1 Starting Templates ----------------
    templates_a = ("VDGV", "FDGV") if args.smoke else GB1_TEMPLATES
    seeds_a = GB1_SEEDS[:1] if args.smoke else GB1_SEEDS
    cap_a = 16000 if args.smoke else 45000
    wall_a = 0.6 if args.smoke else 1.6
    eps_a = 0.010

    gb1_rows = []
    for tmpl in templates_a:
        prob = GB1MutationCampaignProblem(start_seq=tmpl, max_edits=3, panel="panel5")
        diag = real_world_problem_diagnostics(prob)
        assert diag["containment_pairs"] == 0
        gamma_over_flat = round(
            float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"])), 3
        )
        regime = "epistatic_ridge" if gamma_over_flat >= 10.0 else "single_peak"
        for s in seeds_a:
            order = list(METHODS)
            rng.shuffle(order)
            for m in order:
                rec = run_one(prob, eps_a, s, m, wall_limit=wall_a, cap=cap_a)
                rec.update({
                    "start_seq": tmpl,
                    "panel": "panel5",
                    "regime": regime,
                    "leaves": diag["leaves"],
                    "root_actions": diag["root_actions"],
                    "mean_pairwise_jaccard": diag["mean_pairwise_jaccard"],
                    "exterior_margin_gamma": diag["exterior_margin_gamma"],
                    "flat_top2_gap": diag["flat_top2_gap"],
                    "gamma_over_flat": gamma_over_flat,
                })
                gb1_rows.append(rec)

    gb1_rows.sort(key=lambda r: (r["start_seq"], r["seed"], METHODS.index(r["method"])))
    gb1_path = dest / "gb1_campaigns_runs.jsonl"
    gb1_path.write_text("\n".join(json.dumps(r) for r in gb1_rows) + "\n")

    # ---------------- Part B: GB1 Codon-Panel / Scale Sweep ----------------
    panels_b = ("panel4", "panel5") if args.smoke else SWEEP_PANELS
    tmpls_b = ("FDGV",) if args.smoke else SWEEP_TEMPLATES
    seeds_b = SWEEP_SEEDS[:1] if args.smoke else SWEEP_SEEDS
    cap_b = 16000 if args.smoke else 50000
    wall_b = 0.6 if args.smoke else 1.8
    eps_b = 0.015

    sweep_rows = []
    for pan in panels_b:
        for tmpl in tmpls_b:
            prob = GB1MutationCampaignProblem(start_seq=tmpl, max_edits=3, panel=pan)
            diag = real_world_problem_diagnostics(prob)
            assert diag["containment_pairs"] == 0
            for s in seeds_b:
                order = list(METHODS)
                rng.shuffle(order)
                for m in order:
                    rec = run_one(prob, eps_b, s, m, wall_limit=wall_b, cap=cap_b)
                    rec.update({
                        "start_seq": tmpl,
                        "panel": pan,
                        "leaves": diag["leaves"],
                        "root_actions": diag["root_actions"],
                        "mean_pairwise_jaccard": diag["mean_pairwise_jaccard"],
                        "exterior_margin_gamma": diag["exterior_margin_gamma"],
                        "flat_top2_gap": diag["flat_top2_gap"],
                    })
                    sweep_rows.append(rec)

    sweep_rows.sort(
        key=lambda r: (
            SWEEP_PANELS.index(r["panel"]),
            r["start_seq"],
            r["seed"],
            METHODS.index(r["method"]),
        )
    )
    sweep_path = dest / "gb1_panel_sweep_runs.jsonl"
    sweep_path.write_text("\n".join(json.dumps(r) for r in sweep_rows) + "\n")

    # ---------------- Part C: Real WorFBench LLM Workflows ----------------
    doms_c = ("all", "toolbench") if args.smoke else WORFBENCH_DOMAINS
    bases_c = WORFBENCH_BASES[:1] if args.smoke else WORFBENCH_BASES
    seeds_c = WORFBENCH_SEEDS[:1] if args.smoke else WORFBENCH_SEEDS
    cap_c = 12000 if args.smoke else 35000
    wall_c = 0.5 if args.smoke else 1.4
    eps_c = 0.020

    wf_rows = []
    for dom in doms_c:
        for b_tag, b_cfg, max_u in bases_c:
            prob = WorFBenchWorkflowProblem(
                domain=dom,
                base_config=b_cfg,
                max_upgrades=max_u,
                name=f"worfbench_{dom}_{b_tag}",
            )
            diag = real_world_problem_diagnostics(prob)
            assert diag["containment_pairs"] == 0
            gamma_over_flat = round(
                float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"])), 3
            )
            for s in seeds_c:
                order = list(METHODS)
                rng.shuffle(order)
                for m in order:
                    rec = run_one(prob, eps_c, s, m, wall_limit=wall_c, cap=cap_c)
                    rec.update({
                        "domain": dom,
                        "campaign": b_tag,
                        "leaves": diag["leaves"],
                        "root_actions": diag["root_actions"],
                        "mean_pairwise_jaccard": diag["mean_pairwise_jaccard"],
                        "exterior_margin_gamma": diag["exterior_margin_gamma"],
                        "flat_top2_gap": diag["flat_top2_gap"],
                        "gamma_over_flat": gamma_over_flat,
                    })
                    wf_rows.append(rec)

    wf_rows.sort(
        key=lambda r: (
            WORFBENCH_DOMAINS.index(r["domain"]),
            r["campaign"],
            r["seed"],
            METHODS.index(r["method"]),
        )
    )
    wf_path = dest / "worfbench_runs.jsonl"
    wf_path.write_text("\n".join(json.dumps(r) for r in wf_rows) + "\n")

    summarize(dest)

    manifest = {
        "suite": "exp12_real_world",
        "smoke": bool(args.smoke),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "delta": DELTA,
        "schedule": SCHEDULE,
        "gb1_runs": len(gb1_rows),
        "gb1_sweep_runs": len(sweep_rows),
        "worfbench_runs": len(wf_rows),
        "total_runs": len(gb1_rows) + len(sweep_rows) + len(wf_rows),
        "sha256_gb1_campaigns": digest(gb1_path),
        "sha256_gb1_panel_sweep": digest(sweep_path),
        "sha256_worfbench": digest(wf_path),
    }
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        f"Saved {manifest['total_runs']} runs to {dest} "
        f"(GB1={len(gb1_rows)}, Sweep={len(sweep_rows)}, WorFBench={len(wf_rows)})."
    )


if __name__ == "__main__":
    main()
