#!/usr/bin/env python3
"""Deterministic export of tidy CSVs for the 4 unified ICML main-paper figures.

Reads only the frozen JSONL logs under results/ without modifying any archived
benchmark outputs, writing clean per-instance, ECDF, and quantile summaries.
"""
from __future__ import annotations

import collections
import csv
import json
from pathlib import Path
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
RESULTS_DIR = REPO_ROOT / "results"
OUT_DIRS = [
    RESULTS_DIR / "uct_v4_icml_baselines" / "icml_figures_data",
    REPO_ROOT.parent / "dag-uct-latex" / "reproduce" / "data" / "icml_figures_data",
]


def load_jsonl(rel_path: str) -> list[dict]:
    path = RESULTS_DIR / rel_path
    with path.open("r", encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def write_csv(filename: str, fieldnames: list[str], rows: list[dict]) -> None:
    for out_dir in OUT_DIRS:
        if not out_dir.parents[1].exists():
            continue
        out_dir.mkdir(parents=True, exist_ok=True)
        out_path = out_dir / filename
        with out_path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)


def export_fig2_overlap() -> None:
    runs = load_jsonl("uct_v4_icml_baselines/exp8_external_baselines/runs.jsonl")
    methods = [
        "lucb_micro_marg",
        "lucb_micro_exact",
        "ugape_mcts_dag_marg",
        "exact_dag_lucb",
        "varde_exact",
    ]
    rows: list[dict] = []
    for suite in ("overlap_256_box", "overlap_256_eb"):
        for method in methods:
            for rho in (0.0, 0.25, 0.5, 0.75, 0.88):
                sub = [
                    r for r in runs
                    if r["suite"] == suite and r["method"] == method and float(r["rho"]) == rho
                ]
                if not sub:
                    continue
                ms = np.array([r["total_s"] * 1000.0 for r in sub], dtype=float)
                st = np.array([r["steps"] for r in sub], dtype=float)
                cert = np.array([1.0 if r["certified"] else 0.0 for r in sub], dtype=float)
                rows.append({
                    "suite": suite,
                    "method": method,
                    "rho": rho,
                    "n_runs": len(sub),
                    "cert_rate": round(float(cert.mean()), 4),
                    "ms_med": round(float(np.median(ms)), 3),
                    "ms_q25": round(float(np.percentile(ms, 25)), 3),
                    "ms_q75": round(float(np.percentile(ms, 75)), 3),
                    "steps_med": round(float(np.median(st)), 1),
                    "steps_q25": round(float(np.percentile(st, 25)), 1),
                    "steps_q75": round(float(np.percentile(st, 75)), 1),
                })
    write_csv(
        "fig2a_overlap_sweep.csv",
        [
            "suite", "method", "rho", "n_runs", "cert_rate",
            "ms_med", "ms_q25", "ms_q75", "steps_med", "steps_q25", "steps_q75",
        ],
        rows,
    )


def export_fig2_paired_and_midgame() -> None:
    r9 = load_jsonl("uct_v4_icml_baselines/exp9_samegame_midgame/runs.jsonl")
    r11m = load_jsonl("uct_v4_icml_baselines/exp11_hybrid_and_os/midgame20_runs.jsonl")

    # Panel 2b: paired per-instance runtime ratios vs lucb_micro_marg
    strata = [
        "endgame_15x15_d4_zero_contain",
        "random_6x6_d4_zero_contain",
        "routing_w32_d5_zero_contain",
        "routing_w96_d5_zero_contain",
    ]
    ratio_rows: list[dict] = []
    for stratum in strata:
        sub = [r for r in r9 if r["stratum"] == stratum]
        by_im: dict[tuple[str, str], list[float]] = collections.defaultdict(list)
        by_im_steps: dict[tuple[str, str], list[float]] = collections.defaultdict(list)
        for r in sub:
            by_im[(str(r["instance"]), r["method"])].append(r["total_s"] * 1000.0)
            by_im_steps[(str(r["instance"]), r["method"])].append(float(r["steps"]))
        instances = sorted({str(r["instance"]) for r in sub})
        for inst in instances:
            base_ms = float(np.median(by_im[(inst, "lucb_micro_marg")]))
            base_st = float(np.median(by_im_steps[(inst, "lucb_micro_marg")]))
            for method in ("ugape_mcts_dag_marg", "varde_exact", "exact_dag_lucb"):
                m_ms = float(np.median(by_im[(inst, method)]))
                m_st = float(np.median(by_im_steps[(inst, method)]))
                ratio_rows.append({
                    "stratum": stratum,
                    "instance": inst,
                    "method": method,
                    "method_ms": round(m_ms, 3),
                    "baseline_ms": round(base_ms, 3),
                    "time_ratio": round(m_ms / base_ms, 5),
                    "steps_ratio": round(m_st / base_st, 5),
                })
    write_csv(
        "fig2b_paired_instance_ratios.csv",
        ["stratum", "instance", "method", "method_ms", "baseline_ms", "time_ratio", "steps_ratio"],
        ratio_rows,
    )

    # Panel 2c & 2d & 3c: hard mid-game 15x15 zero-containment individual runs
    mid_rows: list[dict] = []
    for r in r9:
        if r["stratum"] != "midgame_15x15_d4_zero_contain":
            continue
        if r["method"] not in ("lucb_micro_marg", "ugape_mcts_dag_marg", "varde_exact", "exact_dag_lucb"):
            continue
        mid_rows.append({
            "source": "exp9",
            "method": r["method"],
            "instance": str(r["instance"]),
            "seed": int(r["seed"]),
            "repeat": int(r["repeat"]),
            "certified": int(bool(r["certified"])),
            "total_ms": round(float(r["total_s"]) * 1000.0, 3),
            "steps": int(r["steps"]),
        })
    for r in r11m:
        if r["stratum"] != "midgame_15x15_d4_zero_contain":
            continue
        mid_rows.append({
            "source": "exp11",
            "method": f"inside_{r['method']}",
            "instance": str(r["instance"]),
            "seed": int(r["seed"]),
            "repeat": int(r["repeat"]),
            "certified": int(bool(r["certified"])),
            "total_ms": round(float(r["total_s"]) * 1000.0, 3),
            "steps": int(r["steps"]),
        })
    write_csv(
        "fig2cd_midgame_runs.csv",
        ["source", "method", "instance", "seed", "repeat", "certified", "total_ms", "steps"],
        mid_rows,
    )


def export_fig_app_inside_and_star() -> None:
    r11h = load_jsonl("uct_v4_icml_baselines/exp11_hybrid_and_os/hybrid_runs.jsonl")
    r10 = load_jsonl("uct_v4_icml_baselines/exp10_inside_witness/runs.jsonl")
    r11s = load_jsonl("uct_v4_icml_baselines/exp11_hybrid_and_os/star_runs.jsonl")

    rows: list[dict] = []
    for fam in ("decoy_trap_16", "window_64", "window_256", "hetero_support_64", "hetero_support_256", "samegame_mid15x15_d4_zero_contain"):
        for method in ("ucb", "hybrid", "lcb_fast", "opt_sep"):
            sub = [r for r in r11h if r["family"] == fam and r["method"] == method]
            ms = np.array([r["total_s"] * 1000.0 for r in sub], dtype=float)
            st = np.array([r["steps"] for r in sub], dtype=float)
            cert = np.array([1.0 if r["certified"] else 0.0 for r in sub], dtype=float)
            cert_ms = ms[cert > 0.5]
            rows.append({
                "family": fam,
                "method": method,
                "n_runs": len(sub),
                "cert_rate": round(float(cert.mean()), 4),
                "ms_med": round(float(np.median(ms)), 3),
                "ms_q25": round(float(np.percentile(ms, 25)), 3),
                "ms_q75": round(float(np.percentile(ms, 75)), 3),
                "cond_ms_med": round(float(np.median(cert_ms)), 3) if len(cert_ms) else -1.0,
                "steps_med": round(float(np.median(st)), 1),
                "steps_q25": round(float(np.percentile(st, 25)), 1),
                "steps_q75": round(float(np.percentile(st, 75)), 1),
            })
        sub10 = [r for r in r10 if r["family"] == fam and r["inside_mode"] == "lcb"]
        if sub10:
            ms = np.array([r["total_s"] * 1000.0 for r in sub10], dtype=float)
            st = np.array([r["steps"] for r in sub10], dtype=float)
            cert = np.array([1.0 if r["certified"] else 0.0 for r in sub10], dtype=float)
            cert_ms = ms[cert > 0.5]
            rows.append({
                "family": fam,
                "method": "lcb_scan",
                "n_runs": len(sub10),
                "cert_rate": round(float(cert.mean()), 4),
                "ms_med": round(float(np.median(ms)), 3),
                "ms_q25": round(float(np.percentile(ms, 25)), 3),
                "ms_q75": round(float(np.percentile(ms, 75)), 3),
                "cond_ms_med": round(float(np.median(cert_ms)), 3) if len(cert_ms) else -1.0,
                "steps_med": round(float(np.median(st)), 1),
                "steps_q25": round(float(np.percentile(st, 25)), 1),
                "steps_q75": round(float(np.percentile(st, 75)), 1),
            })
    write_csv(
        "fig_app_inside_regimes.csv",
        [
            "family", "method", "n_runs", "cert_rate",
            "ms_med", "ms_q25", "ms_q75", "cond_ms_med",
            "steps_med", "steps_q25", "steps_q75",
        ],
        rows,
    )

    star_rows: list[dict] = []
    for eps in sorted({float(r["eps"]) for r in r11s}, reverse=True):
        for method in ("opt_sep", "ucb", "hybrid", "lucb_micro_marg"):
            sub = [r for r in r11s if float(r["eps"]) == eps and r["method"] == method]
            st = np.array([r["steps"] for r in sub], dtype=float)
            ms = np.array([r["total_s"] * 1000.0 for r in sub], dtype=float)
            cert = np.array([1.0 if r["certified"] else 0.0 for r in sub], dtype=float)
            star_rows.append({
                "eps": eps,
                "method": method,
                "n_runs": len(sub),
                "cert_rate": round(float(cert.mean()), 4),
                "steps_med": round(float(np.median(st)), 1),
                "steps_q25": round(float(np.percentile(st, 25)), 1),
                "steps_q75": round(float(np.percentile(st, 75)), 1),
                "ms_med": round(float(np.median(ms)), 3),
            })
    write_csv(
        "fig_app_star_eps_sweep.csv",
        ["eps", "method", "n_runs", "cert_rate", "steps_med", "steps_q25", "steps_q75", "ms_med"],
        star_rows,
    )


def export_fig4_cpp() -> None:
    r7 = load_jsonl("uct_v3_strengthening/exp7_cpp_kernels/runs.jsonl")
    rows: list[dict] = []
    for suite in ("root_puct_scaling", "parity_grid", "overlap_emp_bernstein", "uct_funnel_gap"):
        fams = sorted({r["family"] for r in r7 if r["suite"] == suite})
        for fam in fams:
            methods = sorted({r["method"] for r in r7 if r["suite"] == suite and r["family"] == fam})
            for method in methods:
                sub = [r for r in r7 if r["suite"] == suite and r["family"] == fam and r["method"] == method]
                end_ms = np.array([r["end_ms"] for r in sub], dtype=float)
                init_ms = np.array([r["init_ms"] for r in sub], dtype=float)
                st = np.array([r["steps"] for r in sub], dtype=float)
                rows.append({
                    "suite": suite,
                    "family": fam,
                    "param": sub[0]["param"],
                    "m": int(sub[0]["m"]),
                    "method": method,
                    "n_runs": len(sub),
                    "end_ms_med": round(float(np.median(end_ms)), 4),
                    "end_ms_q25": round(float(np.percentile(end_ms, 25)), 4),
                    "end_ms_q75": round(float(np.percentile(end_ms, 75)), 4),
                    "init_ms_med": round(float(np.median(init_ms)), 4),
                    "steps_med": round(float(np.median(st)), 1),
                })
    write_csv(
        "fig4_cpp_maintenance.csv",
        [
            "suite", "family", "param", "m", "method", "n_runs",
            "end_ms_med", "end_ms_q25", "end_ms_q75", "init_ms_med", "steps_med",
        ],
        rows,
    )


def export_fig3_real_world() -> None:
    exp13_dir = RESULTS_DIR / "uct_v4_icml_baselines" / "exp13_real_world_validation"
    if not (exp13_dir / "factorial_runs.jsonl").is_file():
        return
    fac = load_jsonl("uct_v4_icml_baselines/exp13_real_world_validation/factorial_runs.jsonl")
    trp = load_jsonl("uct_v4_icml_baselines/exp13_real_world_validation/trpb_runs.jsonl")
    gb1 = [r for r in fac if r["benchmark"] == "gb1"]
    wf = [r for r in fac if r["benchmark"] == "worfbench"]

    # 3a: individual GB1 factorial campaign runs (including flat_lucb_term & flat_lucb_root)
    gb1_out = [
        {
            "start_seq": r["start_seq"],
            "regime": r["regime"],
            "method": r["method"],
            "seed": int(r["seed"]),
            "certified": int(bool(r["certified"])),
            "steps": int(r["steps"]),
            "capped_steps": int(r["capped_steps"]),
            "total_ms": round(float(r["total_s"]) * 1000.0, 3),
            "selected_raw_fitness": float(r["selected_raw_fitness"]),
            "opt_raw_fitness": float(r["opt_raw_fitness"]),
        }
        for r in gb1
    ]
    write_csv(
        "fig3a_gb1_factorial_runs.csv",
        [
            "start_seq", "regime", "method", "seed", "certified",
            "steps", "capped_steps", "total_ms", "selected_raw_fitness", "opt_raw_fitness",
        ],
        gb1_out,
    )

    # 3b: per-template ridge ratios across BOTH GB1 (10 templates) and TrpB (21 unselected templates)
    ridge_rows: list[dict] = []
    for landscape, runs in (("gb1", gb1), ("trpb", trp)):
        templates = sorted({r["start_seq"] for r in runs})
        for tmpl in templates:
            sub_t = [r for r in runs if r["start_seq"] == tmpl]
            r0 = sub_t[0]
            med_by_m = {
                m: float(np.median([r["capped_steps"] for r in sub_t if r["method"] == m]))
                for m in {r["method"] for r in sub_t}
            }
            cert_by_m = {
                m: float(np.mean([1.0 if r["certified"] else 0.0 for r in sub_t if r["method"] == m]))
                for m in {r["method"] for r in sub_t}
            }
            ref_steps = med_by_m["opt_sep"]
            ridge_rows.append({
                "landscape": landscape,
                "start_seq": tmpl,
                "gamma_over_flat": float(r0["gamma_over_flat"]),
                "opt_raw_fitness": float(r0["opt_raw_fitness"]),
                "opt_sep_steps": round(ref_steps, 1),
                "exact_ucb_steps": round(med_by_m["exact_dag_lucb"], 1),
                "flat_term_steps": round(med_by_m["flat_lucb_term"], 1),
                "flat_root_steps": round(med_by_m["flat_lucb_root"], 1),
                "lucb_marg_steps": round(med_by_m["lucb_micro_marg"], 1),
                "flat_term_over_os": round(med_by_m["flat_lucb_term"] / ref_steps, 4),
                "flat_root_over_os": round(med_by_m["flat_lucb_root"] / ref_steps, 4),
                "marg_over_os": round(med_by_m["lucb_micro_marg"] / ref_steps, 4),
                "flat_term_cert_rate": round(cert_by_m["flat_lucb_term"], 4),
                "flat_root_cert_rate": round(cert_by_m["flat_lucb_root"], 4),
                "marg_cert_rate": round(cert_by_m["lucb_micro_marg"], 4),
            })
    ridge_rows.sort(key=lambda r: (r["landscape"], r["gamma_over_flat"], r["start_seq"]))
    write_csv(
        "fig3b_protein_ridges.csv",
        [
            "landscape", "start_seq", "gamma_over_flat", "opt_raw_fitness",
            "opt_sep_steps", "exact_ucb_steps", "flat_term_steps", "flat_root_steps", "lucb_marg_steps",
            "flat_term_over_os", "flat_root_over_os", "marg_over_os",
            "flat_term_cert_rate", "flat_root_cert_rate", "marg_cert_rate",
        ],
        ridge_rows,
    )

    # 3c: individual WorFBench factorial runs (including flat_lucb_term & flat_lucb_root + unseen test F1)
    wf_out = [
        {
            "domain": r["domain"],
            "campaign": r["campaign"],
            "method": r["method"],
            "seed": int(r["seed"]),
            "certified": int(bool(r["certified"])),
            "steps": int(r["steps"]),
            "capped_steps": int(r["capped_steps"]),
            "total_ms": round(float(r["total_s"]) * 1000.0, 3),
            "estimated_llm_tokens": float(r["estimated_llm_tokens"]),
            "selected_f1": float(r["selected_action_value"]),
            "unseen_test_f1": float(r["unseen_test_v_action"]),
        }
        for r in wf
    ]
    write_csv(
        "fig3c_worfbench_factorial_runs.csv",
        [
            "domain", "campaign", "method", "seed", "certified",
            "steps", "capped_steps", "total_ms", "estimated_llm_tokens",
            "selected_f1", "unseen_test_f1",
        ],
        wf_out,
    )

    # 3d: genuine live online Qwen3-0.6B runs + per-campaign paired ratios
    live_rel = "uct_v4_icml_baselines/exp13_real_world_validation/worfbench_live_online_runs.jsonl"
    if (RESULTS_DIR / live_rel).is_file():
        live_runs = load_jsonl(live_rel)
        live_out = [
            {
                "method": r["method"],
                "seed": int(r["seed"]),
                "certified": int(bool(r["certified"])),
                "steps": int(r["steps"]),
                "capped_steps": int(r["capped_steps"]),
                "cap": int(r["cap"]),
                "live_total_tokens": int(r["live_total_tokens"]),
                "live_gen_calls": int(r["live_gen_calls"]),
                "live_infer_s": round(float(r["live_infer_s"]), 3),
                "action_label": str(r["action_label"]),
            }
            for r in live_runs
        ]
        write_csv(
            "fig3d_worfbench_live_runs.csv",
            [
                "method", "seed", "certified", "steps", "capped_steps", "cap",
                "live_total_tokens", "live_gen_calls", "live_infer_s", "action_label",
            ],
            live_out,
        )

    pair_rows: list[dict] = []
    for dom in ("all", "toolbench", "toolalpaca", "seal_tools", "webshop"):
        sub_d = [r for r in wf if r["domain"] == dom]
        campaigns = sorted({r["campaign"] for r in sub_d})
        for camp in campaigns:
            sub_c = [r for r in sub_d if r["campaign"] == camp]
            base_st = float(np.median([r["capped_steps"] for r in sub_c if r["method"] == "lucb_micro_marg"]))
            for method in ("flat_lucb_term", "flat_lucb_root", "varde_exact", "safeguarded_lcb", "exact_dag_lucb", "opt_sep"):
                m_st = float(np.median([r["capped_steps"] for r in sub_c if r["method"] == method]))
                pair_rows.append({
                    "domain": dom,
                    "campaign": camp,
                    "method": method,
                    "method_steps": round(m_st, 1),
                    "baseline_steps": round(base_st, 1),
                    "steps_ratio": round(m_st / base_st, 5),
                })
    write_csv(
        "fig3d_worfbench_paired.csv",
        ["domain", "campaign", "method", "method_steps", "baseline_steps", "steps_ratio"],
        pair_rows,
    )

    # 3cd (BO): GB1 Bayesian optimization sequence discovery vs root certification
    bo_rel = "uct_v4_icml_baselines/exp14_gb1_bayesian_opt/bo_acquisition_runs.jsonl"
    if (RESULTS_DIR / bo_rel).is_file():
        bo_runs = load_jsonl(bo_rel)
        bo_out = [
            {
                "start_seq": r["start_seq"],
                "regime": r["regime"],
                "method": r["method"],
                "seed": int(r["seed"]),
                "certified": int(bool(r["certified"])),
                "steps": int(r["steps"]),
                "capped_steps": int(r["capped_steps"]),
                "tau_discover_seq": int(r["tau_discover_seq"]),
                "discovered_eps_seq": int(bool(r["discovered_eps_seq"])),
                "gp_ms": round(float(r["gp_time_s"]) * 1000.0, 3),
                "total_ms": round(float(r["total_s"]) * 1000.0, 3),
            }
            for r in bo_runs
        ]
        write_csv(
            "fig3cd_gb1_bo_runs.csv",
            [
                "start_seq", "regime", "method", "seed", "certified",
                "steps", "capped_steps", "tau_discover_seq", "discovered_eps_seq",
                "gp_ms", "total_ms",
            ],
            bo_out,
        )
        bo_sum = []
        for m in ("gp_root_info", "opt_sep", "exact_dag_lucb", "flat_lucb_root", "gp_ts", "gp_ei", "gp_ucb"):
            sub = [r for r in bo_runs if r["method"] == m]
            if not sub:
                continue
            disc = np.array([float(r["tau_discover_seq"]) for r in sub])
            cert_s = np.array([float(r["capped_steps"]) for r in sub])
            cert_r = float(np.mean([1.0 if r["certified"] else 0.0 for r in sub]))
            bo_sum.append({
                "method": m,
                "n_runs": len(sub),
                "discover_rate": round(float(np.mean([1.0 if r["discovered_eps_seq"] else 0.0 for r in sub])), 4),
                "discover_med": round(float(np.median(disc)), 1),
                "discover_q25": round(float(np.percentile(disc, 25)), 1),
                "discover_q75": round(float(np.percentile(disc, 75)), 1),
                "cert_rate": round(cert_r, 4),
                "cert_med": round(float(np.median(cert_s)), 1),
                "cert_q25": round(float(np.percentile(cert_s, 25)), 1),
                "cert_q75": round(float(np.percentile(cert_s, 75)), 1),
                "gp_ms_med": round(float(np.median([float(r["gp_time_s"]) * 1000.0 for r in sub])), 2),
                "total_ms_med": round(float(np.median([float(r["total_s"]) * 1000.0 for r in sub])), 2),
            })
        write_csv(
            "fig3c_gb1_bo_summary.csv",
            [
                "method", "n_runs", "discover_rate", "discover_med", "discover_q25", "discover_q75",
                "cert_rate", "cert_med", "cert_q25", "cert_q75", "gp_ms_med", "total_ms_med",
            ],
            bo_sum,
        )

    # exp15: Controlled GP correlation (1D & 2D) + GB1 kernel misspecification
    c1_rel = "uct_v4_icml_baselines/exp15_bo_correlation_and_misspec/corr_1d_runs.jsonl"
    if (RESULTS_DIR / c1_rel).is_file():
        c1_runs = load_jsonl(c1_rel)
        c1_rows = []
        for rho in (0.0, 0.25, 0.5, 0.75, 0.9):
            for m in ("exact_dag_lucb", "opt_sep", "gp_root_freq", "rkhs_box", "rkhs_ellipsoid", "nominal_box", "nominal_ellipsoid"):
                sub = [r for r in c1_runs if abs(float(r["rho_in"]) - rho) < 1e-6 and r["method"] == m]
                if not sub:
                    continue
                st = np.array([float(r["capped_steps"]) for r in sub])
                disc = np.array([float(r["tau_discover_seq"]) for r in sub])
                c1_rows.append({
                    "rho": round(rho, 2),
                    "method": m,
                    "n_runs": len(sub),
                    "cert_rate": round(float(np.mean([1.0 if r["certified"] else 0.0 for r in sub])), 4),
                    "steps_med": round(float(np.median(st)), 1),
                    "steps_q25": round(float(np.percentile(st, 25)), 1),
                    "steps_q75": round(float(np.percentile(st, 75)), 1),
                    "discover_med": round(float(np.median(disc)), 1),
                })
        write_csv(
            "fig_bo_corr_1d.csv",
            ["rho", "method", "n_runs", "cert_rate", "steps_med", "steps_q25", "steps_q75", "discover_med"],
            c1_rows,
        )

    c2_rel = "uct_v4_icml_baselines/exp15_bo_correlation_and_misspec/corr_2d_phase_runs.jsonl"
    if (RESULTS_DIR / c2_rel).is_file():
        c2_runs = load_jsonl(c2_rel)
        c2_rows = []
        for rin in (0.0, 0.45, 0.9):
            for rout in (0.0, 0.45, 0.9):
                cell = [
                    r for r in c2_runs
                    if abs(float(r["rho_in"]) - rin) < 1e-6 and abs(float(r["rho_out"]) - rout) < 1e-6
                ]
                if not cell:
                    continue
                os_med = float(np.median([float(r["capped_steps"]) for r in cell if r["method"] == "opt_sep"]))
                for m in ("opt_sep", "gp_root_freq", "rkhs_box", "rkhs_ellipsoid"):
                    sub = [r for r in cell if r["method"] == m]
                    st = np.array([float(r["capped_steps"]) for r in sub])
                    med = float(np.median(st))
                    c2_rows.append({
                        "rho_in": round(rin, 2),
                        "rho_out": round(rout, 2),
                        "method": m,
                        "cert_rate": round(float(np.mean([1.0 if r["certified"] else 0.0 for r in sub])), 4),
                        "steps_med": round(med, 1),
                        "ratio_vs_opt_sep": round(med / max(1.0, os_med), 4),
                    })
        write_csv(
            "fig_bo_corr_2d.csv",
            ["rho_in", "rho_out", "method", "cert_rate", "steps_med", "ratio_vs_opt_sep"],
            c2_rows,
        )

    ms_rel = "uct_v4_icml_baselines/exp15_bo_correlation_and_misspec/gb1_misspec_runs.jsonl"
    if (RESULTS_DIR / ms_rel).is_file():
        ms_runs = load_jsonl(ms_rel)
        ms_rows = []
        for acq in ("gp_root_info", "gp_ucb"):
            for k_mode in ("structured", "hamming", "oversmooth", "scrambled_desc"):
                sub = [r for r in ms_runs if r["method"] == acq and r["kernel_mode"] == k_mode]
                if not sub:
                    continue
                disc = np.array([float(r["tau_discover_seq"]) for r in sub])
                st = np.array([float(r["capped_steps"]) for r in sub])
                ms_rows.append({
                    "method": acq,
                    "kernel_mode": k_mode,
                    "n_runs": len(sub),
                    "discover_med": round(float(np.median(disc)), 1),
                    "discover_q25": round(float(np.percentile(disc, 25)), 1),
                    "discover_q75": round(float(np.percentile(disc, 75)), 1),
                    "cert_rate": round(float(np.mean([1.0 if r["certified"] else 0.0 for r in sub])), 4),
                    "cert_med": round(float(np.median(st)), 1),
                    "cert_q25": round(float(np.percentile(st, 25)), 1),
                    "cert_q75": round(float(np.percentile(st, 75)), 1),
                    "false_certificates": sum(1 for r in sub if r["false_certificate"]),
                })
        write_csv(
            "fig_bo_gb1_misspec.csv",
            [
                "method", "kernel_mode", "n_runs", "discover_med", "discover_q25", "discover_q75",
                "cert_rate", "cert_med", "cert_q25", "cert_q75", "false_certificates",
            ],
            ms_rows,
        )


def main() -> None:
    export_fig2_overlap()
    export_fig2_paired_and_midgame()
    export_fig3_real_world()
    export_fig4_cpp()
    export_fig_app_inside_and_star()
    print("Exported unified ICML figure CSVs to:", [str(p) for p in OUT_DIRS])


if __name__ == "__main__":
    main()
