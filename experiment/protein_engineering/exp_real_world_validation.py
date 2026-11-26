"""Experiment 13 (ICML v6 Validation): Factorial `Flat-LUCB + Root Certificate` Control,
GB1 Assay-Noise Robustness, Unselected 21-Template TrpB Landscape, and WorFBench
Overlap Sweep, Unseen-Task Generalization, & Live Online Qwen3-0.6B Cost Audit.

Addresses the four validation & interpretation questions for the real-world applications:
1. Part A (`factorial_runs.jsonl` -> `summary_factorial.csv`):
   Clean factorial separation of *Decision Abstraction* (`Flat-LUCB [Terminal Stop]` ->
   `Flat-LUCB + Root Certificate`) versus *Graph-Aware Witness Allocation*
   (`Flat-LUCB + Root Certificate` -> `Exact-Regret-DAG-LUCB` / `Optimistic-Separation`)
   across all 10 GB1 templates and all 20 WorFBench campaigns.
2. Part B (`gb1_noise_runs.jsonl` -> `summary_gb1_noise_models.csv`):
   Repeats the 10-template GB1 experiment across three observation models sharing the
   exact same normalized means `mu_z` (`calibrated`, `bernoulli`, `low_var_uniform`),
   computing right-censored lower-bounded ratios `tau_Flat / tau_OS` and Spearman rank
   correlations against the measured epistatic ridge ratio `Gamma / Delta_flat`.
3. Part C (`trpb_runs.jsonl` -> `summary_trpb.csv`):
   Evaluates the independent combinatorially complete 4-site TmTrpB active-site enzyme
   landscape (Johnston et al., *PNAS* 2024; 159,129 stop-free variants across V183, F184,
   V227, S228) across the complete, unselected 21-variant neighborhood consisting of
   parent `VFVS` plus all 20 single-site mutants into `panel5 = ('A','G','I','K','L')`.
4. Part D (`worfbench_overlap_gen_runs.jsonl` -> `summary_worfbench_overlap.csv`,
   `summary_worfbench_unseen_gen.csv`, `summary_worfbench_live_online.csv`):
   - Controlled support-overlap sweep varying allowed stage upgrades `d in {1, 2, 3, 4}`
     (`M in {8, 32, 64, 80}`, Jaccard `0.00 -> 0.24`, zero support containments),
   - Out-of-sample generalization of certified commitments from `D_cert` (64 tasks) onto
     the strictly disjoint unseen test set `D_test` (32 tasks) plus per-pull token costs,
   - Summary of the 8 genuine live online `Qwen3-0.6B` + `WorFEval` runs (`worfbench_live_online_runs.jsonl`).
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

import numpy as np

from dagcert.tracking import LUCBMicroSession, VarDEDAGSession
from dagcert import HybridWitnessDAGLUCBSession
from dagcert._core.v6_real_world import (
    FlatLUCBSession,
    GB1MutationCampaignProblem,
    TRPB_PANELS,
    TrpBMutationCampaignProblem,
    WORFBENCH_NPZ_PATH,
    WorFBenchWorkflowProblem,
    gb1_mean_to_raw_fitness,
    real_world_problem_diagnostics,
)
from experiment.protein_engineering.exp_real_world_applications import (
    GB1_SEEDS,
    GB1_TEMPLATES,
    WORFBENCH_BASES,
    WORFBENCH_DOMAINS,
    WORFBENCH_SEEDS,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/uct_v4_icml_baselines/exp13_real_world_validation"
TEST_NPZ_PATH = ROOT / "dagcert/benchmarks/data/worfbench_qwen3_test_81x32.npz"

FACTORIAL_METHODS = (
    "flat_lucb_term",
    "flat_lucb_root",
    "lucb_micro_marg",
    "varde_exact",
    "safeguarded_lcb",
    "exact_dag_lucb",
    "opt_sep",
)

NOISE_MODELS = ("calibrated", "bernoulli", "low_var_uniform")
NOISE_METHODS = ("flat_lucb_term", "flat_lucb_root", "lucb_micro_marg", "exact_dag_lucb", "opt_sep")
NOISE_SEEDS = tuple(range(790001, 790005))  # 4 seeds/cell across 10 templates x 3 noise models

# Complete, unselected 21-variant TrpB neighborhood: parent VFVS + all 20 1-mutants into panel5
def _prespecified_trpb_templates() -> tuple[str, ...]:
    parent = "VFVS"
    panel = TRPB_PANELS["panel5"]
    out = [parent]
    for pos in range(4):
        for aa in panel:
            if aa != parent[pos]:
                chars = list(parent)
                chars[pos] = aa
                out.append("".join(chars))
    return tuple(out)


TRPB_TEMPLATES = _prespecified_trpb_templates()
TRPB_SEEDS = tuple(range(800001, 800005))  # 4 seeds x 21 templates x 5 methods = 420 runs
OVERLAP_SEEDS = tuple(range(805001, 805007))
DELTA = 0.05
SCHEDULE = "emp_bernstein"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _spearman_rho(xs: list[float], ys: list[float]) -> float:
    def _ranks(vals: list[float]) -> list[float]:
        indexed = sorted(enumerate(vals), key=lambda t: t[1])
        ranks = [0.0] * len(vals)
        i = 0
        while i < len(indexed):
            j = i
            while j + 1 < len(indexed) and indexed[j + 1][1] == indexed[i][1]:
                j += 1
            avg_r = 0.5 * (i + j) + 1.0
            for k in range(i, j + 1):
                ranks[indexed[k][0]] = avg_r
            i = j + 1
        return ranks

    rx, ry = _ranks(xs), _ranks(ys)
    mx, my = statistics.fmean(rx), statistics.fmean(ry)
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    den = (sum((a - mx) ** 2 for a in rx) * sum((b - my) ** 2 for b in ry)) ** 0.5
    return num / den if den > 0 else 0.0


def _has_conflict(sess) -> bool:
    if hasattr(sess, "monitor"):
        return sess.monitor.evidence.conflict
    return sess.evidence.conflict


def make_session(prob, eps: float, seed: int, method: str):
    if method == "flat_lucb_term":
        return FlatLUCBSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE, stop_rule="terminal")
    if method == "flat_lucb_root":
        return FlatLUCBSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE, stop_rule="root_exact")
    if method == "lucb_micro_marg":
        return LUCBMicroSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE, stop_rule="marginal")
    if method == "varde_exact":
        return VarDEDAGSession(prob, seed, eps, delta=DELTA, schedule=SCHEDULE, witness_mode="exact")
    if method == "exact_dag_lucb":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="ucb", delta=DELTA, schedule=SCHEDULE)
    if method == "safeguarded_lcb":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="hybrid", delta=DELTA, schedule=SCHEDULE)
    if method == "opt_sep":
        return HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=DELTA, schedule=SCHEDULE)
    raise ValueError(f"Unknown method: {method}")


def run_one(
    prob,
    eps: float,
    seed: int,
    method: str,
    wall_limit: float,
    cap: int,
    leaf_cost_tokens: dict[int, float] | None = None,
    leaf_cost_calls: dict[int, float] | None = None,
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
    obs_vec = list(sess.oracle.obs)
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
        "action_idx": act,
        "action_label": prob.action_labels[act],
        "v_star": round(opt, 6),
        "selected_action_value": round(sel_val, 6),
        "final_simple_regret": round(true_reg, 6),
    }
    if leaf_cost_tokens is not None and leaf_cost_calls is not None:
        est_toks = sum(obs_vec[z] * leaf_cost_tokens[z] for z in prob.graph.leaves)
        est_gcalls = sum(obs_vec[z] * leaf_cost_calls[z] for z in prob.graph.leaves)
        rec["estimated_llm_tokens"] = round(est_toks, 1)
        rec["estimated_gen_calls"] = round(est_gcalls, 1)
    if hasattr(prob, "raw_fitness"):
        fmax = getattr(prob, "fitness_max", 8.761966133117676)
        rec["opt_raw_fitness"] = round(gb1_mean_to_raw_fitness(opt, fmax), 4)
        rec["selected_raw_fitness"] = round(gb1_mean_to_raw_fitness(sel_val, fmax), 4)
    return rec


def summarize(dest: Path) -> None:
    fac_runs = [json.loads(x) for x in (dest / "factorial_runs.jsonl").read_text().splitlines() if x.strip()]
    noi_runs = [json.loads(x) for x in (dest / "gb1_noise_runs.jsonl").read_text().splitlines() if x.strip()]
    trp_runs = [json.loads(x) for x in (dest / "trpb_runs.jsonl").read_text().splitlines() if x.strip()]
    ovg_runs = [json.loads(x) for x in (dest / "worfbench_overlap_gen_runs.jsonl").read_text().splitlines() if x.strip()]

    # 1. Factorial summary (GB1 all / ridge / single_peak + WorFBench overall & per-domain)
    fac_rows = []
    for bench in ("gb1_all", "gb1_epistatic_ridge", "gb1_single_peak", "worfbench_overall",
                  "worfbench_all", "worfbench_toolbench", "worfbench_toolalpaca",
                  "worfbench_seal_tools", "worfbench_webshop"):
        for m in FACTORIAL_METHODS:
            if bench == "gb1_all":
                sub = [r for r in fac_runs if r["benchmark"] == "gb1" and r["method"] == m]
            elif bench.startswith("gb1_"):
                reg = bench[4:]
                sub = [r for r in fac_runs if r["benchmark"] == "gb1" and r.get("regime") == reg and r["method"] == m]
            elif bench == "worfbench_overall":
                sub = [r for r in fac_runs if r["benchmark"] == "worfbench" and r["method"] == m]
            else:
                dom = bench[len("worfbench_"):]
                sub = [r for r in fac_runs if r["benchmark"] == "worfbench" and r.get("domain") == dom and r["method"] == m]
            if not sub:
                continue
            row = {
                "cohort": bench,
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_total_ms": round(1e3 * statistics.median(r["total_s"] for r in sub), 2),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            }
            if "estimated_llm_tokens" in sub[0]:
                row["median_llm_tokens"] = round(statistics.median(r["estimated_llm_tokens"] for r in sub), 0)
                row["median_gen_calls"] = round(statistics.median(r["estimated_gen_calls"] for r in sub), 1)
            else:
                row["median_llm_tokens"] = 0.0
                row["median_gen_calls"] = 0.0
            if "unseen_test_v_action" in sub[0]:
                row["mean_cert_val"] = round(statistics.fmean(r["selected_action_value"] for r in sub), 4)
                row["mean_unseen_test_val"] = round(statistics.fmean(r["unseen_test_v_action"] for r in sub), 4)
                row["mean_unseen_test_regret"] = round(statistics.fmean(r["unseen_test_regret"] for r in sub), 4)
            else:
                row["mean_cert_val"] = round(statistics.fmean(r["selected_action_value"] for r in sub), 4)
                row["mean_unseen_test_val"] = -1.0
                row["mean_unseen_test_regret"] = -1.0
            fac_rows.append(row)
    with (dest / "summary_factorial.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(fac_rows[0].keys()))
        w.writeheader()
        w.writerows(fac_rows)

    # 2. GB1 Noise-Model Robustness + Spearman Rank Correlation of Ridge Effect
    noi_rows = []
    corr_rows = []
    for nm in NOISE_MODELS:
        sub_nm = [r for r in noi_runs if r["noise_model"] == nm]
        if not sub_nm:
            continue
        # Per-stratum summary
        for stratum in ("all", "epistatic_ridge", "single_peak"):
            for m in NOISE_METHODS:
                sub = [
                    r for r in sub_nm
                    if r["method"] == m and (stratum == "all" or r["regime"] == stratum)
                ]
                if not sub:
                    continue
                noi_rows.append({
                    "noise_model": nm,
                    "stratum": stratum,
                    "method": m,
                    "runs": len(sub),
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                    "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                    "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                })
        # Compute Spearman rho across templates between Gamma / Delta_flat and censored tau_Flat / tau_OS
        tmpls = sorted({r["start_seq"] for r in sub_nm})
        xs_g, ys_term, ys_root = [], [], []
        for t in tmpls:
            st = [r for r in sub_nm if r["start_seq"] == t]
            xs_g.append(float(st[0]["gamma_over_flat"]))
            med_os = statistics.median(r["capped_steps"] for r in st if r["method"] == "opt_sep")
            med_ft = statistics.median(r["capped_steps"] for r in st if r["method"] == "flat_lucb_term")
            med_fr = statistics.median(r["capped_steps"] for r in st if r["method"] == "flat_lucb_root")
            ys_term.append(med_ft / med_os)
            ys_root.append(med_fr / med_os)
        corr_rows.append({
            "noise_model": nm,
            "n_templates": len(tmpls),
            "spearman_flat_term_vs_ridge": round(_spearman_rho(xs_g, ys_term), 4),
            "spearman_flat_root_vs_ridge": round(_spearman_rho(xs_g, ys_root), 4),
        })
    with (dest / "summary_gb1_noise_models.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(noi_rows[0].keys()))
        w.writeheader()
        w.writerows(noi_rows)
    with (dest / "summary_gb1_ridge_correlations.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(corr_rows[0].keys()))
        w.writeheader()
        w.writerows(corr_rows)

    # 3. TrpB 21-template summary (all + ridge >= 5x + single_peak < 5x)
    trp_rows = []
    for stratum in ("all_21_templates", "ridge_ge_5x", "single_peak_lt_5x"):
        for m in NOISE_METHODS:
            sub = [
                r for r in trp_runs
                if r["method"] == m and (
                    stratum == "all_21_templates"
                    or (stratum == "ridge_ge_5x" and r["gamma_over_flat"] >= 5.0)
                    or (stratum == "single_peak_lt_5x" and r["gamma_over_flat"] < 5.0)
                )
            ]
            if not sub:
                continue
            trp_rows.append({
                "stratum": stratum,
                "n_templates": len({r["start_seq"] for r in sub}),
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "mean_selected_raw_fitness": round(statistics.fmean(r["selected_raw_fitness"] for r in sub), 4),
                "false_certificates": sum(1 for r in sub if r["false_certificate"]),
            })
    with (dest / "summary_trpb.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(trp_rows[0].keys()))
        w.writeheader()
        w.writerows(trp_rows)

    # 4. WorFBench upgrade-depth overlap sweep (d = 1..4)
    ov_rows = []
    for d_up in sorted({int(r["max_upgrades"]) for r in ovg_runs}):
        sub_d = [r for r in ovg_runs if int(r["max_upgrades"]) == d_up]
        for m in NOISE_METHODS:
            sub = [r for r in sub_d if r["method"] == m]
            if not sub:
                continue
            ov_rows.append({
                "max_upgrades": d_up,
                "leaves": sub[0]["leaves"],
                "mean_jaccard": sub[0]["mean_pairwise_jaccard"],
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "median_capped_steps": round(statistics.median(r["capped_steps"] for r in sub), 1),
                "median_llm_tokens": round(statistics.median(r["estimated_llm_tokens"] for r in sub), 0),
                "mean_unseen_test_f1": round(statistics.fmean(r["unseen_test_v_action"] for r in sub), 4),
            })
    with (dest / "summary_worfbench_overlap_sweep.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(ov_rows[0].keys()))
        w.writeheader()
        w.writerows(ov_rows)

    # 5. Live online Qwen3-0.6B summary if present
    live_path = dest / "worfbench_live_online_runs.jsonl"
    if live_path.is_file():
        live_runs = [json.loads(x) for x in live_path.read_text().splitlines() if x.strip()]
        live_rows = []
        for m in ("opt_sep", "flat_lucb_root", "flat_lucb_term", "lucb_micro_marg"):
            sub = [r for r in live_runs if r["method"] == m]
            if not sub:
                continue
            live_rows.append({
                "method": m,
                "runs": len(sub),
                "cert_rate": round(sum(1 for r in sub if r["certified"]) / len(sub), 4),
                "mean_steps": round(statistics.fmean(r["capped_steps"] for r in sub), 1),
                "mean_live_tokens": round(statistics.fmean(r["live_total_tokens"] for r in sub), 0),
                "mean_live_gen_calls": round(statistics.fmean(r["live_gen_calls"] for r in sub), 1),
                "mean_live_infer_s": round(statistics.fmean(r["live_infer_s"] for r in sub), 2),
            })
        with (dest / "summary_worfbench_live_online.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(live_rows[0].keys()))
            w.writeheader()
            w.writerows(live_rows)


def _worfbench_leaf_costs_and_unseen_values(
    prob: WorFBenchWorkflowProblem,
    test_archive: dict[str, np.ndarray],
) -> tuple[dict[int, float], dict[int, float], list[float], float]:
    """Compute per-leaf mean LLM tokens, gen calls, and unseen-test action values."""
    wfs = [str(w) for w in test_archive["workflows"]]
    wf_to_idx = {w: i for i, w in enumerate(wfs)}
    test_doms = [str(d) for d in test_archive["domains"]]
    if prob.domain == "all":
        cols = np.arange(test_archive["scores"].shape[1], dtype=np.int64)
    else:
        cols = np.array([j for j, d in enumerate(test_doms) if d == prob.domain], dtype=np.int64)

    in_tok = test_archive["in_tokens"][:, cols]
    out_tok = test_archive["out_tokens"][:, cols]
    gen_c = test_archive["gen_calls"]
    test_sc = test_archive["scores"][:, cols]

    leaf_toks: dict[int, float] = {}
    leaf_calls: dict[int, float] = {}
    leaf_test_means: dict[int, float] = {}
    for z in prob.graph.leaves:
        wname = prob.leaf_workflow_name[z]
        wi = wf_to_idx[wname]
        leaf_toks[z] = float(np.mean(in_tok[wi] + out_tok[wi]))
        leaf_calls[z] = float(gen_c[wi])
        leaf_test_means[z] = float(np.mean(test_sc[wi]))

    test_vals = prob.graph.optimal_values(leaf_test_means)
    root_ch = prob.graph.children[prob.graph.root]
    act_test_vals = [float(test_vals[c]) for c in root_ch]
    test_opt = float(test_vals[prob.graph.root])
    return leaf_toks, leaf_calls, act_test_vals, test_opt


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

    rng = random.Random(2026111805)
    test_archive = dict(np.load(TEST_NPZ_PATH))

    # ---------------- Part A: Factorial Control (GB1 + WorFBench + Unseen Generalization) ----------------
    fac_rows = []
    tmpls_a = ("VDGV", "FDGV") if args.smoke else GB1_TEMPLATES
    seeds_gb1 = GB1_SEEDS[:1] if args.smoke else GB1_SEEDS
    cap_gb1 = 16000 if args.smoke else 45000
    wall_gb1 = 0.6 if args.smoke else 1.8

    for tmpl in tmpls_a:
        prob = GB1MutationCampaignProblem(start_seq=tmpl, max_edits=3, panel="panel5", noise_model="calibrated")
        diag = real_world_problem_diagnostics(prob)
        gof = round(float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"])), 3)
        regime = "epistatic_ridge" if gof >= 10.0 else "single_peak"
        for s in seeds_gb1:
            order = list(FACTORIAL_METHODS)
            rng.shuffle(order)
            for m in order:
                rec = run_one(prob, 0.010, s, m, wall_limit=wall_gb1, cap=cap_gb1)
                rec.update({
                    "benchmark": "gb1",
                    "start_seq": tmpl,
                    "regime": regime,
                    "gamma_over_flat": gof,
                })
                fac_rows.append(rec)

    doms_w = ("all", "toolalpaca") if args.smoke else WORFBENCH_DOMAINS
    bases_w = WORFBENCH_BASES[:1] if args.smoke else WORFBENCH_BASES
    seeds_w = WORFBENCH_SEEDS[:1] if args.smoke else WORFBENCH_SEEDS
    cap_w = 12000 if args.smoke else 35000
    wall_w = 0.5 if args.smoke else 1.5

    for dom in doms_w:
        for b_tag, b_cfg, max_u in bases_w:
            prob = WorFBenchWorkflowProblem(domain=dom, base_config=b_cfg, max_upgrades=max_u, name=f"wf_{dom}_{b_tag}")
            diag = real_world_problem_diagnostics(prob)
            leaf_toks, leaf_calls, act_test_vals, test_opt = _worfbench_leaf_costs_and_unseen_values(prob, test_archive)
            for s in seeds_w:
                order = list(FACTORIAL_METHODS)
                rng.shuffle(order)
                for m in order:
                    rec = run_one(
                        prob, 0.020, s, m, wall_limit=wall_w, cap=cap_w,
                        leaf_cost_tokens=leaf_toks, leaf_cost_calls=leaf_calls,
                    )
                    act_v_test = act_test_vals[rec["action_idx"]]
                    rec.update({
                        "benchmark": "worfbench",
                        "domain": dom,
                        "campaign": b_tag,
                        "leaves": diag["leaves"],
                        "unseen_test_v_star": round(test_opt, 5),
                        "unseen_test_v_action": round(act_v_test, 5),
                        "unseen_test_regret": round(max(0.0, test_opt - act_v_test), 5),
                    })
                    fac_rows.append(rec)

    fac_rows.sort(key=lambda r: (r["benchmark"], r["problem"], r["seed"], FACTORIAL_METHODS.index(r["method"])))
    fac_path = dest / "factorial_runs.jsonl"
    fac_path.write_text("\n".join(json.dumps(r) for r in fac_rows) + "\n")

    # ---------------- Part B: GB1 3-Noise-Model Sensitivity ----------------
    noi_rows = []
    tmpls_b = ("VDGV", "FDGV") if args.smoke else GB1_TEMPLATES
    seeds_b = NOISE_SEEDS[:1] if args.smoke else NOISE_SEEDS
    cap_b = 16000 if args.smoke else 45000
    wall_b = 0.6 if args.smoke else 1.8

    for nm in NOISE_MODELS:
        for tmpl in tmpls_b:
            prob = GB1MutationCampaignProblem(start_seq=tmpl, max_edits=3, panel="panel5", noise_model=nm)
            diag = real_world_problem_diagnostics(prob)
            gof = round(float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"])), 3)
            regime = "epistatic_ridge" if gof >= 10.0 else "single_peak"
            for s in seeds_b:
                order = list(NOISE_METHODS)
                rng.shuffle(order)
                for m in order:
                    rec = run_one(prob, 0.010, s, m, wall_limit=wall_b, cap=cap_b)
                    rec.update({
                        "noise_model": nm,
                        "start_seq": tmpl,
                        "regime": regime,
                        "gamma_over_flat": gof,
                    })
                    noi_rows.append(rec)

    noi_rows.sort(key=lambda r: (NOISE_MODELS.index(r["noise_model"]), r["start_seq"], r["seed"], NOISE_METHODS.index(r["method"])))
    noi_path = dest / "gb1_noise_runs.jsonl"
    noi_path.write_text("\n".join(json.dumps(r) for r in noi_rows) + "\n")

    # ---------------- Part C: Unselected 21-Template TrpB Enzyme Landscape ----------------
    trp_rows = []
    tmpls_c = ("VFVS", "VLVS") if args.smoke else TRPB_TEMPLATES
    seeds_c = TRPB_SEEDS[:1] if args.smoke else TRPB_SEEDS
    cap_c = 16000 if args.smoke else 45000
    wall_c = 0.6 if args.smoke else 1.8

    for tmpl in tmpls_c:
        prob = TrpBMutationCampaignProblem(start_seq=tmpl, max_edits=3, panel="panel5", noise_model="low_var_uniform")
        diag = real_world_problem_diagnostics(prob)
        assert diag["containment_pairs"] == 0
        gof = round(float(diag["exterior_margin_gamma"]) / max(1e-6, float(diag["flat_top2_gap"])), 3)
        for s in seeds_c:
            order = list(NOISE_METHODS)
            rng.shuffle(order)
            for m in order:
                rec = run_one(prob, 0.010, s, m, wall_limit=wall_c, cap=cap_c)
                rec.update({
                    "start_seq": tmpl,
                    "leaves": diag["leaves"],
                    "root_actions": diag["root_actions"],
                    "exterior_margin_gamma": diag["exterior_margin_gamma"],
                    "flat_top2_gap": diag["flat_top2_gap"],
                    "gamma_over_flat": gof,
                })
                trp_rows.append(rec)

    trp_rows.sort(key=lambda r: (TRPB_TEMPLATES.index(r["start_seq"]), r["seed"], NOISE_METHODS.index(r["method"])))
    trp_path = dest / "trpb_runs.jsonl"
    trp_path.write_text("\n".join(json.dumps(r) for r in trp_rows) + "\n")

    # ---------------- Part D: WorFBench Upgrade-Depth Overlap Sweep (d = 1..4) ----------------
    ovg_rows = []
    depths_d = (1, 3) if args.smoke else (1, 2, 3, 4)
    seeds_d = OVERLAP_SEEDS[:1] if args.smoke else OVERLAP_SEEDS
    doms_d = ("all",) if args.smoke else ("all", "toolbench", "toolalpaca", "seal_tools", "webshop")

    for d_up in depths_d:
        for dom in doms_d:
            prob = WorFBenchWorkflowProblem(domain=dom, base_config=(0, 0, 0, 0), max_upgrades=d_up)
            diag = real_world_problem_diagnostics(prob)
            assert diag["containment_pairs"] == 0
            leaf_toks, leaf_calls, act_test_vals, test_opt = _worfbench_leaf_costs_and_unseen_values(prob, test_archive)
            for s in seeds_d:
                order = list(NOISE_METHODS)
                rng.shuffle(order)
                for m in order:
                    rec = run_one(
                        prob, 0.020, s, m, wall_limit=wall_w, cap=cap_w,
                        leaf_cost_tokens=leaf_toks, leaf_cost_calls=leaf_calls,
                    )
                    act_v_test = act_test_vals[rec["action_idx"]]
                    rec.update({
                        "domain": dom,
                        "max_upgrades": d_up,
                        "leaves": diag["leaves"],
                        "mean_pairwise_jaccard": diag["mean_pairwise_jaccard"],
                        "unseen_test_v_star": round(test_opt, 5),
                        "unseen_test_v_action": round(act_v_test, 5),
                        "unseen_test_regret": round(max(0.0, test_opt - act_v_test), 5),
                    })
                    ovg_rows.append(rec)

    ovg_rows.sort(key=lambda r: (r["max_upgrades"], r["domain"], r["seed"], NOISE_METHODS.index(r["method"])))
    ovg_path = dest / "worfbench_overlap_gen_runs.jsonl"
    ovg_path.write_text("\n".join(json.dumps(r) for r in ovg_rows) + "\n")

    summarize(dest)

    manifest = {
        "suite": "exp13_real_world_validation",
        "smoke": bool(args.smoke),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "delta": DELTA,
        "schedule": SCHEDULE,
        "factorial_runs": len(fac_rows),
        "gb1_noise_runs": len(noi_rows),
        "trpb_runs": len(trp_rows),
        "worfbench_overlap_runs": len(ovg_rows),
        "total_runs": len(fac_rows) + len(noi_rows) + len(trp_rows) + len(ovg_rows),
        "sha256_factorial": digest(fac_path),
        "sha256_gb1_noise": digest(noi_path),
        "sha256_trpb": digest(trp_path),
        "sha256_worfbench_overlap": digest(ovg_path),
    }
    live_path = dest / "worfbench_live_online_runs.jsonl"
    if live_path.is_file() and not args.smoke:
        manifest["sha256_worfbench_live_online"] = digest(live_path)
    (dest / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Saved {manifest['total_runs']} validation runs to {dest}!")


if __name__ == "__main__":
    main()
