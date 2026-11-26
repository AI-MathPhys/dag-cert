"""Generate all seven supplementary vector PDF figures referenced by `manuscript/joint_cert_manuscript.tex`.

Reads exclusively from SHA-256-verified archived summary CSVs under `results/bayesian_ucd_v1/`
and writes the exact manuscript filenames into `figures/`:
  1. `supp_protein_credibility_audit.pdf`       (Fig. 9  — v14 proper chi2_{M-1,.95} & coverage)
  2. `supp_live_workflow_validation.pdf`        (Fig. 10 — v11_2 36-campaign live Qwen3-0.6B)
  3. `supp_information_tracking.pdf`            (Fig. 11 — v8_2 info tracking vs. CD-Joint)
  4. `supp_protein_calibration_robustness.pdf`  (Fig. 12 — v8_1 protein calibration & xi frontier)
  5. `supp_eprocess_safety_and_compute.pdf`     (Fig. 13 — v9_3/v9_1 wealth reset, IUT, d=4 K=32)
  6. `supp_sparse_variance_tracking.pdf`        (Fig. 14 — v9_1/v9_2 K=64 compute & hetero stress)
  7. `supp_native_solver_and_workflows.pdf`     (Fig. 15 — v10_1/2/3 C++ B&B, GB1 het., 8-camp live)
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
BAY = ROOT / "results/bayesian_ucd_v1"
DEFAULT_OUT = ROOT / "figures"

NAVY = "#244665"
TEAL = "#0D9488"
AMBER = "#D97706"
BLUE = "#2563EB"
RED = "#DC2626"
SLATE = "#475569"
GREEN = "#15803D"


def _csv(path: Path) -> list[dict]:
    with path.open("r", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def _setup_mpl() -> None:
    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 8.0,
            "axes.titlesize": 8.4,
            "axes.labelsize": 7.8,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )


def _clean_ax(ax: plt.Axes, grid_axis: str = "y") -> None:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_linewidth(0.8)
    ax.spines["bottom"].set_linewidth(0.8)
    ax.tick_params(labelsize=7.3, length=2.6, width=0.7)
    ax.grid(axis=grid_axis, linestyle="-", linewidth=0.45, color="#E5E7EB", zorder=0)
    ax.set_axisbelow(True)


def fig9_protein_credibility_audit(out_dir: Path) -> None:
    rows = _csv(BAY / "v14_protein_credible_ellipsoid/v14_protein_credible_summary.csv")
    lk = {(r["landscape"], r["condition"], r["method"]): r for r in rows}
    methods = ("kg", "gp_os", "cd_joint")
    labels = ("Corr. KG", "GP-OS", "CD-Joint")
    cols = (NAVY, AMBER, TEAL)

    fig, axes = plt.subplots(1, 3, figsize=(10.2, 3.05))
    fig.subplots_adjust(left=0.065, right=0.985, top=0.84, bottom=0.19, wspace=0.30)

    for idx, (land, title) in enumerate((("gb1", "(a) GB1 ($n=200$, $\\chi^2_{r,.95}$)"), ("trpb", "(b) TmTrpB ($n=210$, $\\chi^2_{r,.95}$)"))):
        ax = axes[idx]
        _clean_ax(ax, "y")
        xs = np.arange(3)
        vals = [float(lk[(land, "B_chi95", m)]["restricted_mean"]) / 1000.0 for m in methods]
        lo = [max(0.0, vals[i] - float(lk[(land, "B_chi95", m)]["rm_ci95_lo"]) / 1000.0) for i, m in enumerate(methods)]
        hi = [max(0.0, float(lk[(land, "B_chi95", m)]["rm_ci95_hi"]) / 1000.0 - vals[i]) for i, m in enumerate(methods)]
        certs = [100.0 * float(lk[(land, "B_chi95", m)]["cert_rate"]) for m in methods]
        bars = ax.bar(xs, vals, width=0.58, color=cols, edgecolor="white", zorder=3)
        ax.errorbar(xs, vals, yerr=[lo, hi], fmt="none", ecolor="#111827", elinewidth=0.9, capsize=2.5, zorder=4)
        ymax = 29.5 if land == "gb1" else 12.2
        ax.set_ylim(0, ymax)
        ax.set_xticks(xs)
        ax.set_xticklabels(labels)
        ax.set_ylabel("Restricted mean assays ($\\times 10^3$)")
        ax.set_title(title, fontweight="bold")
        for b, v, h, c in zip(bars, vals, hi, certs):
            cap = "*" if c < 0.5 else ""
            ax.text(b.get_x() + b.get_width() / 2, v + h + ymax * 0.025, f"{v:.1f}k{cap}\n({c:.0f}%)",
                    ha="center", va="bottom", fontsize=6.8, color="#1F2937")

    ax3 = axes[2]
    _clean_ax(ax3, "y")
    x = np.arange(2)
    w = 0.24
    for mi, (m, lbl, col) in enumerate(zip(methods, labels, cols)):
        covs = [100.0 * float(lk[(l, "B_chi95", m)]["joint_contrast_cov"]) for l in ("gb1", "trpb")]
        bars = ax3.bar(x + (mi - 1) * w, covs, width=w, color=col, edgecolor="white", label=lbl, zorder=3)
        for b, cv in zip(bars, covs):
            ax3.text(b.get_x() + b.get_width() / 2, cv + 2.0, f"{cv:.0f}%", ha="center", va="bottom", fontsize=6.6)
    ax3.axhline(95.0, color=RED, linestyle="--", linewidth=0.9, zorder=2)
    ax3.text(1.42, 96.5, "95% nominal", color=RED, fontsize=6.5, ha="right", fontweight="bold")
    ax3.set_ylim(0, 112)
    ax3.set_xticks(x)
    ax3.set_xticklabels(["GB1", "TmTrpB"])
    ax3.set_ylabel("Joint contrast coverage (%)")
    ax3.set_title("(c) Simultaneous $\\mu^*$ coverage", fontweight="bold")
    ax3.legend(frameon=False, fontsize=6.6, loc="upper left", ncol=1)

    fig.savefig(out_dir / "supp_protein_credibility_audit.pdf", dpi=300)
    plt.close(fig)


def fig10_live_workflow_validation(out_dir: Path) -> None:
    rows = [r for r in _csv(BAY / "v11_exp2_live_worfbench_36campaigns/v11_exp2_live_summary.csv") if r["scope_kind"] == "ALL"]
    lk = {r["method"]: r for r in rows}
    methods = ("indep_os", "eb_acq_df_stop", "cd_joint_calibrated")
    labels = ("DF-OS\n(formal DF)", "GP+DF\n(formal DF)", "EB+LOO\n(model-based)")
    cols = (SLATE, AMBER, TEAL)

    fig, axes = plt.subplots(1, 3, figsize=(10.2, 3.0))
    fig.subplots_adjust(left=0.07, right=0.985, top=0.84, bottom=0.22, wspace=0.33)
    xs = np.arange(3)

    # (a) Cert rate
    ax = axes[0]
    _clean_ax(ax, "y")
    certs = [100.0 * float(lk[m]["cert_rate"]) for m in methods]
    bars = ax.bar(xs, certs, width=0.56, color=cols, edgecolor="white", zorder=3)
    for b, c, m in zip(bars, certs, methods):
        ax.text(b.get_x() + b.get_width() / 2, c + 3.0, f"{int(lk[m]['certified_count'])}/36", ha="center", va="bottom", fontsize=7.2, fontweight="bold")
    ax.set_ylim(0, 118)
    ax.set_xticks(xs)
    ax.set_xticklabels(labels, fontsize=7.0)
    ax.set_ylabel("Certified by 60 evals (%)")
    ax.set_title("(a) Live certifications (36 campaigns)", fontweight="bold")

    # (b) Median fresh tokens
    ax = axes[1]
    _clean_ax(ax, "y")
    toks = [float(lk[m]["med_live_tokens"]) / 1000.0 for m in methods]
    bars = ax.bar(xs, toks, width=0.56, color=cols, edgecolor="white", zorder=3)
    for b, v, m in zip(bars, toks, methods):
        star = "*" if int(lk[m]["certified_count"]) == 0 else ""
        ax.text(b.get_x() + b.get_width() / 2, v + 0.9, f"{v:.1f}k{star}", ha="center", va="bottom", fontsize=7.2)
    ax.set_ylim(0, 38.0)
    ax.set_xticks(xs)
    ax.set_xticklabels(labels, fontsize=7.0)
    ax.set_ylabel("Median fresh tokens ($\\times 10^3$)")
    ax.set_title("(b) Uncached Qwen3-0.6B tokens", fontweight="bold")

    # (c) Held-out unseen F1
    ax = axes[2]
    _clean_ax(ax, "y")
    f1s = [float(lk[m]["mean_unseen_test_f1"]) for m in methods]
    bars = ax.bar(xs, f1s, width=0.56, color=cols, edgecolor="white", zorder=3)
    for b, v in zip(bars, f1s):
        ax.text(b.get_x() + b.get_width() / 2, v + 0.012, f"{v:.4f}", ha="center", va="bottom", fontsize=7.0)
    ax.set_ylim(0, 0.56)
    ax.set_xticks(xs)
    ax.set_xticklabels(labels, fontsize=7.0)
    ax.set_ylabel("Mean held-out $D_{\\mathrm{test}}$ $F_1$")
    ax.set_title("(c) Unseen workflow generalization", fontweight="bold")

    fig.savefig(out_dir / "supp_live_workflow_validation.pdf", dpi=300)
    plt.close(fig)


def fig11_information_tracking(out_dir: Path) -> None:
    rows_a = [r for r in _csv(BAY / "v8_exp2_info_tracking/v8_exp2_partA_summary.csv") if r["instance"] == "proxy_M5_d3"]
    rows_b = _csv(BAY / "v8_exp2_info_tracking/v8_exp2_partB_summary.csv")
    rows_c = _csv(BAY / "v8_exp2_info_tracking/v8_exp2_partC_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(10.4, 3.05))
    fig.subplots_adjust(left=0.065, right=0.985, top=0.84, bottom=0.20, wspace=0.33)

    # (a) Proxy DAG normalized counts vs T_*^eps across delta
    ax = axes[0]
    _clean_ax(ax, "y")
    deltas = sorted({float(r["delta"]) for r in rows_a}, reverse=True)
    lka = {(float(r["delta"]), r["method"]): float(r["med_norm_ratio"]) for r in rows_a}
    x = np.arange(len(deltas))
    for m, lbl, col, mk in (
        ("info_tracking", "Info-Tracking", TEAL, "o"),
        ("hybrid_cd_tracking", "Hybrid CD$\\to$Track", BLUE, "s"),
        ("cd_joint", "CD-Joint", AMBER, "^"),
    ):
        ys = [lka[(d, m)] for d in deltas]
        ax.plot(x, ys, marker=mk, linewidth=1.6, markersize=4.8, color=col, label=lbl, zorder=4)
    ax.axhline(1.0, color=SLATE, linestyle="--", linewidth=0.8, label="$T_*^\\varepsilon$ lower bound")
    ax.set_xticks(x)
    ax.set_xticklabels([f"{d:g}" for d in deltas])
    ax.set_xlabel("Confidence level $\\delta$")
    ax.set_ylabel("Median $\\tau / (T_*^\\varepsilon \\log(1/\\delta))$")
    ax.set_title("(a) Proxy DAG rate ratio", fontweight="bold")
    ax.legend(frameon=False, fontsize=6.2, loc="upper right")

    # (b) Medium Gaussian DAGs
    ax = axes[1]
    _clean_ax(ax, "y")
    scales = sorted({int(r["m_leaves"]) for r in rows_b})
    lkb = {(int(r["m_leaves"]), r["method"]): float(r["med_steps"]) for r in rows_b}
    x = np.arange(len(scales))
    w = 0.24
    for mi, (m, lbl, col) in enumerate((("indep_gauss_os", "Indep. OS", SLATE), ("cd_joint", "CD-Joint", AMBER), ("info_tracking", "Info-Track", TEAL))):
        ys = [lkb[(s, m)] for s in scales]
        ax.bar(x + (mi - 1) * w, ys, width=w, color=col, edgecolor="white", label=lbl, zorder=3)
    ax.set_xticks(x)
    ax.set_xticklabels([f"M={s}" for s in scales])
    ax.set_ylabel("Median evaluations")
    ax.set_title("(b) Medium Gaussian DAGs", fontweight="bold")
    ax.legend(frameon=False, fontsize=6.4, loc="upper left")

    # (c) Multi-answer tied optima
    ax = axes[2]
    _clean_ax(ax, "y")
    lkc = {r["method"]: float(r["med_steps"]) for r in rows_c}
    ms = ("indep_gauss_os", "cd_joint", "hybrid_cd_tracking", "info_tracking")
    lbls = ("Indep. OS*", "CD-Joint", "Hybrid", "Info-Track")
    cols = (SLATE, AMBER, BLUE, TEAL)
    xs = np.arange(len(ms))
    ys = [lkc[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.58, color=cols, edgecolor="white", zorder=3)
    ax.set_yscale("log")
    for b, v in zip(bars, ys):
        ax.text(b.get_x() + b.get_width() / 2, v * 1.15, f"{v:.0f}", ha="center", va="bottom", fontsize=6.8)
    ax.set_ylim(10, 9000)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=6.8)
    ax.set_ylabel("Median evaluations (log)")
    ax.set_title("(c) Multiple-correct-answer cohort", fontweight="bold")

    fig.savefig(out_dir / "supp_information_tracking.pdf", dpi=300)
    plt.close(fig)


def fig12_protein_calibration_robustness(out_dir: Path) -> None:
    prows = [r for r in _csv(BAY / "v8_exp1_calibrated_proteins/v8_exp1_protein_summary.csv") if r["stratum"] == "all"]
    crows = _csv(BAY / "v8_exp1_calibrated_proteins/v8_exp1_controlled_summary.csv")
    lkp = {(r["landscape"], r["method"]): float(r["med_steps_25k"]) for r in prows}

    fig, axes = plt.subplots(1, 3, figsize=(10.4, 3.05))
    fig.subplots_adjust(left=0.065, right=0.985, top=0.84, bottom=0.20, wspace=0.33)

    # (a) DF-OS vs EB+LOO on GB1 & TmTrpB
    ax = axes[0]
    _clean_ax(ax, "y")
    x = np.arange(2)
    w = 0.34
    v_os = [lkp[("gb1", "indep_os")] / 1000.0, lkp[("trpb", "indep_os")] / 1000.0]
    v_eb = [lkp[("gb1", "cd_joint_calibrated")] / 1000.0, lkp[("trpb", "cd_joint_calibrated")] / 1000.0]
    b1 = ax.bar(x - w / 2, v_os, width=w, color=SLATE, edgecolor="white", label="Formal DF-OS", zorder=3)
    b2 = ax.bar(x + w / 2, v_eb, width=w, color=TEAL, edgecolor="white", label="Calib. EB+LOO", zorder=3)
    for b, v in list(zip(b1, v_os)) + list(zip(b2, v_eb)):
        ax.text(b.get_x() + b.get_width() / 2, v + 0.45, f"{v:.1f}k", ha="center", va="bottom", fontsize=6.9)
    ax.set_ylim(0, 19.5)
    ax.set_xticks(x)
    ax.set_xticklabels(["GB1 (n=200)", "TmTrpB (n=210)"])
    ax.set_ylabel("Median assays ($\\times 10^3$)")
    ax.set_title("(a) DF-OS vs. model-based EB+LOO", fontweight="bold")
    ax.legend(frameon=False, fontsize=6.5, loc="upper left")

    # (b) Rough-GP misspecification cure (C3)
    ax = axes[1]
    _clean_ax(ax, "y")
    c3 = {r["method"]: 100.0 * float(r["false_cert_rate"]) for r in crows if r["study"] == "C3_misspec_gp_cure"}
    ms = ("bayes_post_nominal", "cd_joint_nominal", "cd_joint_calibrated_eb")
    lbls = ("Nom. Bayes", "Nom. CD-Joint", "EB+LOO")
    cols = (RED, AMBER, TEAL)
    xs = np.arange(3)
    ys = [c3[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.56, color=cols, edgecolor="white", zorder=3)
    for b, v in zip(bars, ys):
        ax.text(b.get_x() + b.get_width() / 2, v + 1.2, f"{v:.1f}%", ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax.axhline(5.0, color=SLATE, linestyle="--", linewidth=0.8)
    ax.set_ylim(0, 46)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=6.9)
    ax.set_ylabel("False certificates (%)")
    ax.set_title("(b) Rough-GP stress (n=500)", fontweight="bold")

    # (c) Bounded-residual (xi, eps=0.03) frontier (C4)
    ax = axes[2]
    _clean_ax(ax, "y")
    c4 = [r for r in crows if r["study"] == "C4_xi_eps_frontier"]
    xis = sorted({float(r["xi"]) for r in c4})
    lk4 = {(float(r["xi"]), r["method"]): 100.0 * float(r["cert_rate"]) for r in c4}
    for m, lbl, col, mk in (
        ("cd_joint_robust", "Robust ellipsoid", AMBER, "o"),
        ("cd_joint_hybrid", "Safe hybrid (DF fallback)", TEAL, "s"),
        ("indep_os", "Formal DF-OS", SLATE, "^"),
    ):
        ys = [lk4[(xi, m)] for xi in xis]
        ax.plot(xis, ys, marker=mk, linewidth=1.6, markersize=4.8, color=col, label=lbl, zorder=4)
    ax.axvline(0.015, color=RED, linestyle=":", linewidth=0.95)
    ax.text(0.0175, 58, "$2\\xi = \\varepsilon$", color=RED, fontsize=6.9, fontweight="bold")
    ax.set_ylim(-5, 112)
    ax.set_xlabel("Residual bound $\\xi$ ($\\varepsilon=0.030$)")
    ax.set_ylabel("Completion rate (%)")
    ax.set_title("(c) Bounded-residual $\\xi$ frontier", fontweight="bold")
    ax.legend(frameon=False, fontsize=6.4, loc="center right")

    fig.savefig(out_dir / "supp_protein_calibration_robustness.pdf", dpi=300)
    plt.close(fig)


def fig13_eprocess_safety_and_compute(out_dir: Path) -> None:
    r_b = _csv(BAY / "v9_exp3_switching_and_safety/v9_exp3_partB_summary.csv")
    r_a = _csv(BAY / "v9_exp3_switching_and_safety/v9_exp3_partA_summary.csv")
    r_v91 = _csv(BAY / "v9_exp1_v34_vs_v33_dag/v9_exp1_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(10.4, 3.05))
    fig.subplots_adjust(left=0.065, right=0.985, top=0.84, bottom=0.22, wspace=0.33)

    # (a) Null-boundary wealth reset vs preserved
    ax = axes[0]
    _clean_ax(ax, "y")
    b1 = {r["method"]: 100.0 * float(r["false_cert_rate"]) for r in r_b if r["part"] == "B1_null_reset"}
    ms = ("neg_ctrl_reset_on_revisit", "v33_preserved_all", "v34_preserved_skip")
    lbls = ("Invalid\nreset", "Preserved\n(V33)", "Preserved\nskip (V34)")
    cols = (RED, NAVY, TEAL)
    xs = np.arange(3)
    ys = [b1[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.56, color=cols, edgecolor="white", zorder=3)
    ax.axhline(5.0, color=SLATE, linestyle="--", linewidth=0.85, alpha=0.65, zorder=2)
    for b, v in zip(bars, ys):
        ax.text(
            b.get_x() + b.get_width() / 2,
            v + 1.2,
            f"{v:.1f}%",
            ha="center",
            va="bottom",
            fontsize=7.0,
            fontweight="bold",
            bbox=dict(facecolor="white", edgecolor="none", pad=0.6, alpha=0.9),
            zorder=5,
        )
    ax.set_ylim(0, 47)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=6.9)
    ax.set_ylabel("Null false certificates (%)")
    ax.set_title("(a) Wealth preservation (n=500)", fontweight="bold")

    # (b) Hard-init switch cohort null-component solves
    ax = axes[1]
    _clean_ax(ax, "y")
    a_nat = {r["method"]: float(r["med_null_calls"]) for r in r_a if r["sub_regime"] == "natural_hard_init"}
    ms = ("v33_all_action", "v34_bonferroni_j", "v34_full")
    lbls = ("Dense\nall-action", "Action-local\nBonferroni", "Action-local\nIUT (V34)")
    cols = (NAVY, AMBER, TEAL)
    ys = [a_nat[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.56, color=cols, edgecolor="white", zorder=3)
    for b, v in zip(bars, ys):
        ax.text(b.get_x() + b.get_width() / 2, v + 12, f"{v:.0f}", ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax.set_ylim(0, 520)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=6.9)
    ax.set_ylabel("Median null-component solves")
    ax.set_title("(b) Hard-switch cohort (K=8)", fontweight="bold")

    # (c) General d=4, K=32 total compute (delta=0.01)
    ax = axes[2]
    _clean_ax(ax, "y")
    d4 = {r["method"]: float(r["med_total_ms"]) / 1000.0 for r in r_v91 if r["track"] == "gend_d4_bnb" and int(r["K"]) == 32 and abs(float(r["delta"]) - 0.01) < 1e-6}
    ms = ("v33_full", "v33_sparse", "v34_full")
    lbls = ("Dense\n(V33)", "Sparse\nrefresh", "Sparse +\nlocal (V34)")
    cols = (NAVY, AMBER, TEAL)
    ys = [d4[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.56, color=cols, edgecolor="white", zorder=3)
    for b, v in zip(bars, ys):
        ax.text(b.get_x() + b.get_width() / 2, v + 1.4, f"{v:.1f}s", ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax.set_ylim(0, 62)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=6.9)
    ax.set_ylabel("Median total compute (s)")
    ax.set_title("(c) General $d=4, K=32$ compute", fontweight="bold")

    fig.savefig(out_dir / "supp_eprocess_safety_and_compute.pdf", dpi=300)
    plt.close(fig)


def fig14_sparse_variance_tracking(out_dir: Path) -> None:
    r_v91 = _csv(BAY / "v9_exp1_v34_vs_v33_dag/v9_exp1_summary.csv")
    r_v92c = _csv(BAY / "v9_exp2_heteroscedastic_info/v9_exp2_partC_summary.csv")

    fig, axes = plt.subplots(1, 2, figsize=(9.6, 3.1))
    fig.subplots_adjust(left=0.075, right=0.985, top=0.84, bottom=0.22, wspace=0.30)

    # (a) K=64 rank-2 cold computation (delta=0.01, unique optimum)
    ax = axes[0]
    _clean_ax(ax, "y")
    k64 = {r["method"]: float(r["med_total_ms"]) / 1000.0 for r in r_v91 if r["track"] == "rank2_cubic" and int(r["K"]) == 64 and r["regime"] == "unique" and abs(float(r["delta"]) - 0.01) < 1e-6}
    ms = ("v33_full", "v33_sparse", "v33_local", "v34_full")
    lbls = ("Dense\n(V33)", "Sparse\nonly", "Local\nonly", "Sparse+Local\n(V34)")
    cols = (NAVY, AMBER, BLUE, TEAL)
    xs = np.arange(4)
    ys = [k64[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.58, color=cols, edgecolor="white", zorder=3)
    for b, v in zip(bars, ys):
        ax.text(b.get_x() + b.get_width() / 2, v + 0.8, f"{v:.2f}s", ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax.set_ylim(0, 38)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=7.0)
    ax.set_ylabel("Median cold wall time (s)")
    ax.set_title("(a) $K=64$ rank-2 ablation ($\\delta=.01$)", fontweight="bold")

    # (b) Heteroscedastic stress error rates across 4 noise profiles
    ax = axes[1]
    _clean_ax(ax, "y")
    profs = ("sig_025_025", "sig_050_200", "sig_025_400", "sig_400_400")
    plbls = ("(.25, .25)", "(.50, 2.0)", "(.25, 4.0)", "(4.0, 4.0)")
    lk = {(r["profile"], r["method"]): 100.0 * float(r["false_cert_rate"]) for r in r_v92c}
    x = np.arange(4)
    w = 0.34
    y_nom = [lk[(p, "cd_joint_nom_sig1")] for p in profs]
    y_v34 = [lk[(p, "v34_vanilla")] for p in profs]
    b1 = ax.bar(x - w / 2, y_nom, width=w, color=RED, edgecolor="white", label="Nominal fixed-$\\sigma$", zorder=3)
    b2 = ax.bar(x + w / 2, y_v34, width=w, color=TEAL, edgecolor="white", label="Unknown-var. V34", zorder=3)
    ax.axhline(5.0, color=SLATE, linestyle="--", linewidth=0.85, alpha=0.65, zorder=2)
    for b, v in zip(b1, y_nom):
        ax.text(
            b.get_x() + b.get_width() / 2,
            v + 1.5,
            f"{v:.0f}%",
            ha="center",
            va="bottom",
            fontsize=6.9,
            color=RED,
            fontweight="bold",
            bbox=dict(facecolor="white", edgecolor="none", pad=0.5, alpha=0.9),
            zorder=5,
        )
    for b, v in zip(b2, y_v34):
        ax.text(
            b.get_x() + b.get_width() / 2,
            v + 1.5,
            f"{v:.0f}%",
            ha="center",
            va="bottom",
            fontsize=6.9,
            color=TEAL,
            bbox=dict(facecolor="white", edgecolor="none", pad=0.5, alpha=0.9),
            zorder=5,
        )
    ax.set_ylim(0, 72)
    ax.set_xticks(x)
    ax.set_xticklabels(plbls, fontsize=7.0)
    ax.set_xlabel("True noise profile $(\\sigma_{\\mathrm{in}}, \\sigma_{\\mathrm{out}})$")
    ax.set_ylabel("False certificates (%)")
    ax.set_title("(b) Heteroscedastic variance stress", fontweight="bold")
    ax.legend(frameon=False, fontsize=6.6, loc="upper left")

    fig.savefig(out_dir / "supp_sparse_variance_tracking.pdf", dpi=300)
    plt.close(fig)


def fig15_native_solver_and_workflows(out_dir: Path) -> None:
    r1 = _csv(BAY / "v10_exp1_cpp_v34_scaling/v10_exp1_cpp_speedup.csv")
    r2 = _csv(BAY / "v10_exp2_real_heteroscedastic_v34/v10_exp2_summary.csv")
    r3 = _csv(BAY / "v10_exp3_live_worfbench_expanded/v10_exp3_live_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(10.4, 3.05))
    fig.subplots_adjust(left=0.065, right=0.985, top=0.84, bottom=0.22, wspace=0.33)

    # (a) Python vs C++17 B&B wall time on paired configs
    ax = axes[0]
    _clean_ax(ax, "y")
    paired = [r for r in r1 if r["py_total_ms"] != "NA"]
    x = np.arange(len(paired))
    w = 0.34
    py_s = [float(r["py_total_ms"]) / 1000.0 for r in paired]
    cpp_s = [float(r["cpp_total_ms"]) / 1000.0 for r in paired]
    ax.bar(x - w / 2, py_s, width=w, color=SLATE, edgecolor="white", label="Python B&B", zorder=3)
    b_cpp = ax.bar(x + w / 2, cpp_s, width=w, color=TEAL, edgecolor="white", label="C++17 B&B", zorder=3)
    ax.set_yscale("log")
    for b, r in zip(b_cpp, paired):
        ax.text(b.get_x() + b.get_width() / 2, float(r["cpp_total_ms"]) / 1000.0 * 1.35, f"{float(r['total_speedup_x']):.0f}x",
                ha="center", va="bottom", fontsize=6.6, color=TEAL, fontweight="bold")
    ax.set_ylim(0.05, 220)
    ax.set_xticks(x)
    ax.set_xticklabels([f"d={r['d']}\nK={r['K']}" for r in paired], fontsize=6.8)
    ax.set_ylabel("Median wall time (s, log)")
    ax.set_title("(a) Certified B&B speedup", fontweight="bold")
    ax.legend(frameon=False, fontsize=6.4, loc="upper left")

    # (b) Projected heteroscedastic GB1 median assays
    ax = axes[1]
    _clean_ax(ax, "y")
    gb1_p = {r["method"]: float(r["med_samples"]) for r in r2 if r["dataset"] == "gb1" and r["track"] == "projected_fixed_feat"}
    ms = ("indep_student_os", "calibrated_eb_loo", "v34_full_cpp")
    lbls = ("Student-t\nOS*", "Calib.\nEB+LOO", "V34\n(C++)")
    cols = (SLATE, AMBER, TEAL)
    xs = np.arange(3)
    ys = [gb1_p[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.56, color=cols, edgecolor="white", zorder=3)
    ax.set_yscale("log")
    for b, v in zip(bars, ys):
        ax.text(b.get_x() + b.get_width() / 2, v * 1.2, f"{v:.0f}", ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax.set_ylim(80, 120000)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=6.9)
    ax.set_ylabel("Median assays (log)")
    ax.set_title("(b) Projected heteroscedastic GB1", fontweight="bold")

    # (c) 8-campaign live Qwen3 fresh tokens
    ax = axes[2]
    _clean_ax(ax, "y")
    lk3 = {r["method"]: float(r["med_live_tokens"]) / 1000.0 for r in r3 if r["scope"] == "ALL"}
    ms = ("indep_os", "cd_joint_hybrid", "cd_joint_calibrated")
    lbls = ("DF-OS*\n(0/8)", "Hybrid EB\n(8/8)", "Calib. EB\n(8/8)")
    cols = (SLATE, BLUE, TEAL)
    ys = [lk3[m] for m in ms]
    bars = ax.bar(xs, ys, width=0.56, color=cols, edgecolor="white", zorder=3)
    for b, v in zip(bars, ys):
        ax.text(b.get_x() + b.get_width() / 2, v + 1.8, f"{v:.1f}k", ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax.set_ylim(0, 84)
    ax.set_xticks(xs)
    ax.set_xticklabels(lbls, fontsize=6.9)
    ax.set_ylabel("Median fresh tokens ($\\times 10^3$)")
    ax.set_title("(c) 8-campaign live Qwen3-0.6B", fontweight="bold")

    fig.savefig(out_dir / "supp_native_solver_and_workflows.pdf", dpi=300)
    plt.close(fig)


def generate_all(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    _setup_mpl()
    for fn in (
        fig9_protein_credibility_audit,
        fig10_live_workflow_validation,
        fig11_information_tracking,
        fig12_protein_calibration_robustness,
        fig13_eprocess_safety_and_compute,
        fig14_sparse_variance_tracking,
        fig15_native_solver_and_workflows,
    ):
        fn(out_dir)
    print(f"Generated all 7 manuscript supplementary PDFs in {out_dir}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    generate_all(args.out_dir)


if __name__ == "__main__":
    main()
