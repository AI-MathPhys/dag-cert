#!/usr/bin/env python3
"""Publication figure generator for Correlation-Aware Bayesian Certification over Overlapping Supports.

Canvas geometry matches `iclr2027_conference.sty` (`\\textwidth = 5.50 in = 396 pt`) with
captions in `\\small` (9.0 pt Times). All figures save at exact 5.50 in width so rendered glyphs
stay 7.0--8.0 pt sans-serif, colorblind-safe, and print-legible.

Generates 6 unified main-paper PDF figures (plus PNG QA renders in `--out-dir` only):
1. `fig1_concept_and_toy.pdf`: Concept schematic (decision overlap + statistical correlation +
   off-witness proxy) + live E0 motivational toy trajectory & 50-seed comparison.
2. `fig2_phase_diagram.pdf`: Central 2D Phase Diagram (`Overlap x Correlation` heatmap of speedup vs
   independent `Optimistic-Separation`, paired with marginal slices & sensitivity bars).
3. `fig3_geometry_and_proxy.pdf`: E2 exact hull dominance (`M` scaling -> 0 pulls), approximate hull
   discrepancy sweep (`eta`), off-witness proxy speedup, and T5.3 multiple-answer commitment.
4. `fig4_real_world_applications.pdf`: E3 real protein design (`GB1` & complete 21-template `TmTrpB`)
   + E4 `WorFBench` `Qwen3-0.6B` LLM token savings and feature-model CV R^2 calibration.
5. `fig5_calibration_and_misspec.pdf`: E5 empirical error rates across `delta in {0.01, 0.05, 0.10}`
   (well-specified linear, well-specified GP posterior, misspecified kernel) and structured residual
   `xi` stress test (`unadjusted` vs `T3.3 robust` vs `safe hybrid`).
6. `fig6_computational_scaling.pdf`: E6 runtime scaling (`M` up to 4096), Caratheodory active support
   sparsity (`|supp(p*)| <= d + 1` up to `d = 64`), and lazy challenger pruning rates.
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import matplotlib as mpl
mpl.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
import numpy as np


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DATA = ROOT / "results/bayesian_ucd_v1"
DEFAULT_OUT = ROOT / "results/bayesian_ucd_v1/figures"

PALETTE = {
    "cd_joint": "#0B5394",     # Contrast-Directed + Joint Ellipsoid (hero blue)
    "mc_joint": "#0E8A74",     # Multi-Contrast + Joint Ellipsoid (teal)
    "track": "#7A3E9D",        # MaxMin-Tracking / T5 (violet)
    "bayes_post": "#1B7837",   # Bayesian Posterior stopping (green)
    "ids": "#2B8CBE",          # Bayes-IDS (sky blue)
    "dw_joint": "#B8860B",     # Direct-Witness + Joint (ochre)
    "gp_ucb": "#D55E00",       # GP-UCB + Joint (vermilion)
    "box": "#CC79A7",          # Enclosing Box (magenta)
    "opt_sep": "#5C6B73",      # Independent Optimistic-Separation (slate)
    "flat": "#B8332A",         # Flat-LUCB / failure alert (crimson)
    "safe": "#0E8A74",         # Safe Hybrid / Robust T3.3
    "ink": "#1F2933",
    "muted": "#6B7785",
    "grid": "#E5E9F0",
    "panel_bg": "#F8FAFC",
}

mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
    "mathtext.fontset": "dejavusans",
    "font.size": 7.4,
    "axes.titlesize": 7.4,
    "axes.labelsize": 7.3,
    "xtick.labelsize": 6.8,
    "ytick.labelsize": 6.8,
    "legend.fontsize": 6.4,
    "axes.linewidth": 0.72,
    "xtick.major.width": 0.68,
    "ytick.major.width": 0.68,
    "xtick.major.size": 2.6,
    "ytick.major.size": 2.6,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "svg.fonttype": "none",
})


def load_csv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def style_axis(ax: plt.Axes, grid_axis: str = "y") -> None:
    ax.patch.set_facecolor("none")
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_color(PALETTE["ink"])
    ax.spines["bottom"].set_color(PALETTE["ink"])
    ax.tick_params(colors=PALETTE["ink"], pad=2.0)
    if grid_axis in ("x", "y", "both"):
        ax.grid(True, which="major", axis=grid_axis, color=PALETTE["grid"], linewidth=0.52, zorder=0)
    ax.set_axisbelow(True)


def add_header(ax: plt.Axes, tag: str, title: str, y_pad: float = 1.045, fontsize: float = 7.3) -> None:
    ax.text(
        0.0, y_pad, f"({tag}) {title}",
        transform=ax.transAxes,
        fontsize=fontsize, fontweight="bold", color=PALETTE["ink"],
        ha="left", va="bottom", clip_on=False,
    )


def save_fig(fig: plt.Figure, out_dir: Path, stem: str, latex_dir: Path | None = None) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_dir / f"{stem}.pdf", format="pdf")
    fig.savefig(out_dir / f"{stem}.png", format="png", dpi=240)
    if latex_dir is not None:
        latex_dir.mkdir(parents=True, exist_ok=True)
        fig.savefig(latex_dir / f"{stem}.pdf", format="pdf")
    plt.close(fig)


# ===========================================================================
# FIGURE 1: Concept Schematic + Motivational Off-Witness Proxy Demonstration
# ===========================================================================
def build_fig1(data_dir: Path, out_dir: Path, latex_dir: Path | None) -> None:
    traj = load_csv(data_dir / "e0_and_toy/toy_trajectory.csv")
    toy_sum = load_csv(data_dir / "e0_and_toy/summary_toy.csv")
    t5_lb = json.loads((data_dir / "e0_and_toy/toy_t5_lower_bound.json").read_text())

    fig = plt.figure(figsize=(5.50, 3.80))
    gs_top = fig.add_gridspec(1, 2, left=0.04, right=0.98, top=0.92, bottom=0.55, wspace=0.28, width_ratios=[1.08, 1.0])
    gs_bot = fig.add_gridspec(1, 2, left=0.17, right=0.98, top=0.41, bottom=0.11, wspace=0.35, width_ratios=[1.12, 0.92])

    # Panel (a): Schematic of correlated DAG + off-witness proxy
    ax0 = fig.add_subplot(gs_top[0, 0])
    ax0.set_xlim(0, 1)
    ax0.set_ylim(0, 1)
    ax0.axis("off")
    ax0.add_patch(FancyBboxPatch(
        (0.01, 0.01), 0.98, 0.97,
        boxstyle="round,pad=0.01,rounding_size=0.03",
        facecolor=PALETTE["panel_bg"], edgecolor="#D5DCE4", linewidth=0.75, zorder=0,
    ))
    add_header(ax0, "a", "Overlapping DAG + proxy contrast", y_pad=1.03)

    def node(cx, cy, w, h, lbl, fc, ec, tc="#FFFFFF", fs=6.4):
        ax0.add_patch(FancyBboxPatch(
            (cx - w / 2, cy - h / 2), w, h,
            boxstyle="round,pad=0.008,rounding_size=0.025",
            facecolor=fc, edgecolor=ec, linewidth=0.82, zorder=3,
        ))
        ax0.text(cx, cy, lbl, ha="center", va="center", fontsize=fs, fontweight="bold", color=tc, zorder=4)

    node(0.50, 0.87, 0.25, 0.13, "Root $s_0$", "#334E68", "#1F2933")
    node(0.28, 0.61, 0.27, 0.13, "Action $a_0$", PALETTE["cd_joint"], PALETTE["cd_joint"])
    node(0.72, 0.61, 0.27, 0.13, "Action $a_1$", PALETTE["opt_sep"], PALETTE["opt_sep"])
    node(0.14, 0.29, 0.21, 0.23, "$z_{\\mathrm{in}}$\n0.76", "#EBF3FA", PALETTE["cd_joint"], tc=PALETTE["cd_joint"], fs=6.2)
    node(0.38, 0.29, 0.20, 0.23, "$z_{\\mathrm{sh}}$\n0.68", "#FFF3E6", PALETTE["gp_ucb"], tc="#9C4200", fs=6.2)
    node(0.62, 0.29, 0.21, 0.23, "$z_{\\mathrm{out}}$\n0.72", "#F1F3F5", PALETTE["opt_sep"], tc=PALETTE["ink"], fs=6.2)
    node(0.86, 0.29, 0.22, 0.23, "$z_{\\mathrm{proxy}}$\n0.50*", "#E6F4EA", PALETTE["bayes_post"], tc=PALETTE["bayes_post"], fs=6.1)

    for (x0, y0), (x1, y1), col, ls in [
        ((0.43, 0.80), (0.31, 0.68), PALETTE["ink"], "-"),
        ((0.57, 0.80), (0.69, 0.68), PALETTE["ink"], "-"),
        ((0.23, 0.54), (0.15, 0.42), PALETTE["cd_joint"], "-"),
        ((0.31, 0.54), (0.37, 0.42), PALETTE["gp_ucb"], "-"),
        ((0.68, 0.54), (0.43, 0.42), PALETTE["gp_ucb"], "-"),
        ((0.71, 0.54), (0.63, 0.42), PALETTE["opt_sep"], "-"),
        ((0.77, 0.54), (0.85, 0.42), PALETTE["bayes_post"], "--"),
        ((0.36, 0.54), (0.79, 0.41), PALETTE["bayes_post"], ":"),
    ]:
        ax0.add_patch(FancyArrowPatch(
            (x0, y0), (x1, y1), arrowstyle="-|>", mutation_scale=7.0,
            color=col, linewidth=0.82, linestyle=ls, zorder=2,
        ))
    ax0.text(
        0.50, 0.05,
        "$\\rho(z_{\\mathrm{in}},z_{\\mathrm{out}})=0.98$;  $z_{\\mathrm{proxy}}$ gives $49\\times$ contrast info",
        ha="center", va="bottom", fontsize=5.8, color=PALETTE["muted"],
    )

    # Panel (b): Regret trajectory (Joint Ellipsoid vs Enclosing Box on seed=7)
    ax1 = fig.add_subplot(gs_top[0, 1])
    style_axis(ax1, "both")
    add_header(ax1, "b", "Certificate collapse (seed 7)")
    for meth, col, ls, lbl in [
        ("contrast_directed_joint", PALETTE["cd_joint"], "-", "Contrast-Dir. (Joint)"),
        ("direct_witness_joint", PALETTE["dw_joint"], "--", "Direct-Witness (Joint)"),
        ("gp_ucb_joint", PALETTE["gp_ucb"], ":", "GP-UCB (Joint)"),
    ]:
        sub = [r for r in traj if r["method"] == meth]
        ax1.plot([int(r["step"]) for r in sub], [float(r["joint_regret_a0"]) for r in sub],
                 color=col, linestyle=ls, linewidth=1.5, label=lbl, zorder=4)
    sub_cd = [r for r in traj if r["method"] == "contrast_directed_joint"]
    ax1.plot(
        [int(r["step"]) for r in sub_cd],
        [float(r["enclosing_box_regret_a0"]) for r in sub_cd],
        color=PALETTE["box"], linestyle="-.", linewidth=1.3, label="Enclosing Box $\\mathcal{B}(\\Theta_t)$", zorder=3,
    )
    ax1.axhline(0.015, color=PALETTE["flat"], linestyle="--", linewidth=0.82, label="$\\varepsilon=0.015$", zorder=2)
    ax1.set_yscale("log")
    ax1.set_xlim(0, 130)
    ax1.set_ylim(0.008, 4.0)
    ax1.set_xlabel("Evaluations $t$")
    ax1.set_ylabel("Certificate $R_t(a_0)$")
    ax1.legend(frameon=False, loc="upper right", fontsize=5.8, handlelength=1.5, labelspacing=0.22)

    # Panel (c): 50-seed median evaluations to certify (log scale)
    ax2 = fig.add_subplot(gs_bot[0, 0])
    style_axis(ax2, "x")
    add_header(ax2, "c", "50-seed evaluations to certify")
    order = [
        ("maxmin_tracking_joint", "MaxMin-Track", PALETTE["track"]),
        ("contrast_directed_joint", "Contrast-Dir.", PALETTE["cd_joint"]),
        ("bayes_ids_joint", "Bayes-IDS", PALETTE["ids"]),
        ("direct_witness_joint", "Direct-Witness", PALETTE["dw_joint"]),
        ("opt_sep", "Opt-Sep (Indep.)", PALETTE["opt_sep"]),
        ("gp_ucb_joint", "GP-UCB (Joint)", PALETTE["gp_ucb"]),
        ("enclosing_box_cd", "Enclosing Box*", PALETTE["box"]),
    ]
    row_map = {r["method"]: r for r in toy_sum}
    y_pos = np.arange(len(order))
    meds = [float(row_map[k]["median_steps"]) for k, _, _ in order]
    q25 = [float(row_map[k]["q25_steps"]) for k, _, _ in order]
    q75 = [float(row_map[k]["q75_steps"]) for k, _, _ in order]
    cols = [c for _, _, c in order]
    bars = ax2.barh(y_pos, meds, color=cols, height=0.64, alpha=0.92, zorder=3)
    ax2.errorbar(
        meds, y_pos,
        xerr=[np.maximum(0.0, np.array(meds) - np.array(q25)), np.maximum(0.0, np.array(q75) - np.array(meds))],
        fmt="none", ecolor=PALETTE["ink"], elinewidth=0.85, capsize=1.8, zorder=4,
    )
    lb_val = float(t5_lb["lower_bound_steps_delta05"])
    ax2.axvline(lb_val, color=PALETTE["ink"], linestyle=":", linewidth=0.95, zorder=2)
    ax2.text(lb_val * 1.18, -0.68, f"T5 LB ({lb_val:.1f})", fontsize=5.8, color=PALETTE["ink"], va="center")
    ax2.set_xscale("log")
    ax2.set_xlim(2.0, 22000.0)
    ax2.set_yticks(y_pos)
    ax2.set_yticklabels([lbl for _, lbl, _ in order], fontsize=6.4)
    ax2.set_ylim(6.65, -1.05)
    ax2.set_xlabel("Median evals (IQR; *46% cert.)")
    for b, m_val, u_val in zip(bars, meds, q75):
        anchor = max(m_val, u_val) * 1.18
        ax2.text(anchor, b.get_y() + b.get_height() / 2, f"{m_val:.0f}", va="center", fontsize=6.1, color=PALETTE["ink"])

    # Panel (d): Off-witness proxy query fraction vs outside-challenger pulls
    ax3 = fig.add_subplot(gs_bot[0, 1])
    style_axis(ax3, "y")
    add_header(ax3, "d", "Proxy vs. challenger pulls")
    sub_order = [
        ("maxmin_tracking_joint", "Track"),
        ("contrast_directed_joint", "CD"),
        ("bayes_ids_joint", "IDS"),
        ("direct_witness_joint", "Witn."),
        ("opt_sep", "Opt-S"),
        ("gp_ucb_joint", "UCB"),
    ]
    x_pos = np.arange(len(sub_order))
    p_frac = [100.0 * float(row_map[k]["mean_proxy_frac"]) for k, _ in sub_order]
    z_out_frac = [100.0 * float(row_map[k]["mean_z_out_pulls"]) / max(1.0, float(row_map[k]["mean_steps"])) for k, _ in sub_order]
    w_bar = 0.37
    ax3.bar(x_pos - w_bar / 2, p_frac, width=w_bar, color=PALETTE["bayes_post"], label="Proxy $z_{\\mathrm{proxy}}$", zorder=3)
    ax3.bar(x_pos + w_bar / 2, z_out_frac, width=w_bar, color=PALETTE["opt_sep"], alpha=0.82, label="Challenger $z_{\\mathrm{out}}$", zorder=3)
    ax3.set_xticks(x_pos)
    ax3.set_xticklabels([lbl for _, lbl in sub_order], fontsize=6.2, rotation=20, ha="right")
    ax3.set_ylabel("Share of pulls (%)")
    ax3.set_ylim(0, 96)
    ax3.legend(frameon=False, loc="upper right", fontsize=5.9)

    save_fig(fig, out_dir, "fig1_concept_and_toy", latex_dir)


# ===========================================================================
# FIGURE 2: Experiment E1 Central 2D Phase Diagram (Overlap x Correlation)
# ===========================================================================
def build_fig2(data_dir: Path, out_dir: Path, latex_dir: Path | None) -> None:
    rows = load_csv(data_dir / "e1_phase_diagram/summary_e1_phase.csv")
    sens = load_csv(data_dir / "e1_phase_diagram/summary_e1_sensitivity.csv")

    overlaps = sorted({float(r["overlap"]) for r in rows})
    rhos = sorted({float(r["rho"]) for r in rows})
    mat_speedup = np.zeros((len(overlaps), len(rhos)), dtype=float)
    mat_steps = np.zeros((len(overlaps), len(rhos)), dtype=float)
    for r in rows:
        if r["method"] == "contrast_directed_joint":
            i = overlaps.index(float(r["overlap"]))
            j = rhos.index(float(r["rho"]))
            mat_speedup[i, j] = float(r["speedup_vs_opt_sep"])
            mat_steps[i, j] = float(r["median_steps"])

    fig = plt.figure(figsize=(5.50, 3.05))
    gs = fig.add_gridspec(
        1, 3,
        left=0.10, right=0.985, bottom=0.19, top=0.86,
        wspace=0.52, width_ratios=[1.20, 1.0, 1.0],
    )

    # Panel (a): 4x4 Heatmap of Speedup vs Independent Opt-Sep
    ax0 = fig.add_subplot(gs[0, 0])
    add_header(ax0, "a", "Speedup vs. Opt-Sep", fontsize=7.2)
    im = ax0.imshow(mat_speedup, origin="lower", cmap="YlGnBu", aspect="auto", vmin=10.0, vmax=float(np.max(mat_speedup)))
    ax0.set_xticks(range(len(rhos)))
    ax0.set_xticklabels([f"{r:.1f}" for r in rhos])
    ax0.set_yticks(range(len(overlaps)))
    ax0.set_yticklabels([f"{o:.2f}" for o in overlaps])
    ax0.set_xlabel("Correlation $\\rho$")
    ax0.set_ylabel("Support overlap $\\omega$")
    mid_val = 0.56 * float(np.max(mat_speedup)) + 4.0
    for i in range(len(overlaps)):
        for j in range(len(rhos)):
            v = mat_speedup[i, j]
            col_txt = "#FFFFFF" if v >= mid_val else PALETTE["ink"]
            ax0.text(j, i, f"{v:.1f}x\n({mat_steps[i, j]:.0f})", ha="center", va="center", fontsize=5.8, fontweight="bold", color=col_txt)
    cbar = fig.colorbar(im, ax=ax0, fraction=0.048, pad=0.04)
    cbar.ax.tick_params(labelsize=6.0, pad=1.5)

    # Panel (b): Method scaling across correlation rho at high overlap (omega = 0.75)
    ax1 = fig.add_subplot(gs[0, 1])
    style_axis(ax1, "both")
    add_header(ax1, "b", "Evals vs. $\\rho$ ($\\omega=0.75$)", fontsize=7.2)
    for meth, lbl, col, mk in [
        ("opt_sep", "Opt-Sep (Indep.)", PALETTE["opt_sep"], "s"),
        ("enclosing_box_cd", "Enclosing Box", PALETTE["box"], "^"),
        ("gp_ucb_joint", "GP-UCB (Joint)", PALETTE["gp_ucb"], "D"),
        ("multi_contrast_joint", "Multi-Contrast", PALETTE["mc_joint"], "v"),
        ("contrast_directed_joint", "Contrast-Dir.", PALETTE["cd_joint"], "o"),
    ]:
        sub = sorted([r for r in rows if abs(float(r["overlap"]) - 0.75) < 1e-6 and r["method"] == meth], key=lambda x: float(x["rho"]))
        xs = [float(r["rho"]) for r in sub]
        ys = [float(r["median_steps"]) for r in sub]
        ax1.plot(xs, ys, color=col, marker=mk, markersize=4.0, linewidth=1.4, label=lbl, zorder=4)
    ax1.set_yscale("log")
    ax1.set_ylim(28, 20000)
    ax1.set_xlabel("Correlation $\\rho$")
    ax1.set_ylabel("Median evaluations")
    ax1.set_xticks(rhos)
    ax1.set_xticklabels([f"{r:.1f}" for r in rhos])
    ax1.legend(frameon=False, loc="lower left", fontsize=5.6, handlelength=1.4, labelspacing=0.18)

    # Panel (c): Sensitivity across eps=0.01, M=256, d=4, d=16 at (omega=0.75, rho=0.90)
    ax2 = fig.add_subplot(gs[0, 2])
    style_axis(ax2, "y")
    add_header(ax2, "c", "Sensitivity", fontsize=7.2)
    cohs = [
        ("sens_d4", "$d{=}4$"),
        ("main", "Base\n($d{=}8$)"),
        ("sens_d16", "$d{=}16$"),
        ("sens_m256", "$M=$\n256"),
        ("sens_eps01", "$\\varepsilon=$\n.01"),
    ]
    cd_sp, mc_sp = [], []
    for ck, _ in cohs:
        if ck == "main":
            r_cd = [r for r in rows if abs(float(r["overlap"]) - 0.75) < 1e-6 and abs(float(r["rho"]) - 0.90) < 1e-6 and r["method"] == "contrast_directed_joint"][0]
            r_mc = [r for r in rows if abs(float(r["overlap"]) - 0.75) < 1e-6 and abs(float(r["rho"]) - 0.90) < 1e-6 and r["method"] == "multi_contrast_joint"][0]
        else:
            r_cd = [r for r in sens if r["cohort"] == ck and abs(float(r["overlap"]) - 0.75) < 1e-6 and abs(float(r["rho"]) - 0.90) < 1e-6 and r["method"] == "contrast_directed_joint"][0]
            r_mc = [r for r in sens if r["cohort"] == ck and abs(float(r["overlap"]) - 0.75) < 1e-6 and abs(float(r["rho"]) - 0.90) < 1e-6 and r["method"] == "multi_contrast_joint"][0]
        cd_sp.append(float(r_cd["speedup_vs_opt_sep"]))
        mc_sp.append(float(r_mc["speedup_vs_opt_sep"]))
    x_c = np.arange(len(cohs))
    ax2.bar(x_c - 0.19, cd_sp, width=0.36, color=PALETTE["cd_joint"], label="Contrast-Dir.", zorder=3)
    ax2.bar(x_c + 0.19, mc_sp, width=0.36, color=PALETTE["mc_joint"], label="Multi-Contrast", zorder=3)
    ax2.axhline(1.0, color=PALETTE["muted"], linestyle="--", linewidth=0.75)
    ax2.set_xticks(x_c)
    ax2.set_xticklabels([lbl for _, lbl in cohs], fontsize=6.0)
    ax2.set_ylabel("Speedup vs. Opt-Sep ($\\times$)")
    ax2.set_ylim(0, 265)
    ax2.legend(frameon=False, loc="upper right", fontsize=5.7)

    save_fig(fig, out_dir, "fig2_phase_diagram", latex_dir)


# ===========================================================================
# FIGURE 3: Experiment E2 Geometry, Off-Witness Proxies & Multiple Answers
# ===========================================================================
def build_fig3(data_dir: Path, out_dir: Path, latex_dir: Path | None) -> None:
    hull = load_csv(data_dir / "e2_geometry_and_proxy/summary_e2_hull.csv")
    proxy = load_csv(data_dir / "e2_geometry_and_proxy/summary_e2_proxy.csv")
    ma = load_csv(data_dir / "e2_geometry_and_proxy/summary_e2_multianswer.csv")

    fig = plt.figure(figsize=(5.50, 3.70))
    gs_top = fig.add_gridspec(1, 2, left=0.10, right=0.98, top=0.92, bottom=0.56, wspace=0.34)
    gs_bot = fig.add_gridspec(1, 2, left=0.175, right=0.98, top=0.41, bottom=0.12, wspace=0.36, width_ratios=[1.08, 0.96])

    # Panel (a): Family A Exact Hull Dominance (M scaling)
    ax0 = fig.add_subplot(gs_top[0, 0])
    style_axis(ax0, "both")
    add_header(ax0, "a", "Exact hull dominance ($\\eta=0$)")
    for meth, lbl, col, mk in [
        ("opt_sep", "Opt-Sep (Indep.)", PALETTE["opt_sep"], "s"),
        ("enclosing_box_cd", "Enclosing Box", PALETTE["box"], "^"),
        ("contrast_directed_joint", "Joint Ellip. (0 pulls)", PALETTE["cd_joint"], "o"),
    ]:
        sub = sorted([r for r in hull if r["family"] == "A_exact_hull" and r["method"] == meth], key=lambda x: int(x["m"]))
        xs = [int(r["m"]) for r in sub]
        ys = [max(0.8, float(r["median_steps"])) for r in sub]
        ax0.plot(xs, ys, color=col, marker=mk, markersize=4.0, linewidth=1.45, label=lbl, zorder=4)
    ax0.set_xscale("log", base=2)
    ax0.set_yscale("log")
    ax0.set_yticks([1, 10, 100, 1000, 10000])
    ax0.set_yticklabels(["0*", "10", "100", "1k", "10k"])
    ax0.set_ylim(0.45, 25000)
    ax0.set_xlabel("Number of terminals $M$")
    ax0.set_ylabel("Median evaluations")
    ax0.legend(frameon=False, loc="center right", fontsize=5.9)

    # Panel (b): Family B Approximate Hull Discrepancy sweep (eta)
    ax1 = fig.add_subplot(gs_top[0, 1])
    style_axis(ax1, "both")
    add_header(ax1, "b", "Hull discrepancy $\\eta_2(a^*)$")
    for meth, lbl, col, mk in [
        ("opt_sep", "Opt-Sep (Indep.)", PALETTE["opt_sep"], "s"),
        ("enclosing_box_cd", "Enclosing Box", PALETTE["box"], "^"),
        ("gp_ucb_joint", "GP-UCB (Joint)", PALETTE["gp_ucb"], "D"),
        ("contrast_directed_joint", "Contrast-Dir. (Joint)", PALETTE["cd_joint"], "o"),
    ]:
        sub = sorted([r for r in hull if r["family"] == "B_approx_hull" and r["method"] == meth], key=lambda x: float(x["eta"]))
        xs = [float(r["measured_hull_dist"]) for r in sub]
        ys = [max(0.8, float(r["median_steps"])) for r in sub]
        ax1.plot(xs, ys, color=col, marker=mk, markersize=3.7, linewidth=1.4, label=lbl, zorder=4)
    ax1.set_yscale("log")
    ax1.set_yticks([1, 10, 100, 1000, 10000])
    ax1.set_yticklabels(["0*", "10", "100", "1k", "10k"])
    ax1.set_ylim(0.45, 25000)
    ax1.set_xlabel("Hull distance $\\eta_2(a^*)$")
    ax1.set_ylabel("Median evaluations")
    ax1.legend(frameon=False, loc="lower right", fontsize=5.7)

    # Panel (c): Family C1 Off-Witness Proxy DAG (gamma = 0.22)
    ax2 = fig.add_subplot(gs_bot[0, 0])
    style_axis(ax2, "x")
    add_header(ax2, "c", "Proxy DAG ($\\gamma=0.22$)")
    c1_order = [
        ("contrast_directed_joint", "Contrast-Dir.", PALETTE["cd_joint"]),
        ("multi_contrast_joint", "Multi-Contrast", PALETTE["mc_joint"]),
        ("direct_witness_joint", "Direct-Witness", PALETTE["dw_joint"]),
        ("maxmin_tracking_joint", "MaxMin-Track", PALETTE["track"]),
        ("bayes_ids_joint", "Bayes-IDS", PALETTE["ids"]),
        ("gp_ucb_joint", "GP-UCB (Joint)", PALETTE["gp_ucb"]),
        ("opt_sep", "Opt-Sep (Indep.)", PALETTE["opt_sep"]),
    ]
    p_map = {r["method"]: r for r in proxy if abs(float(r["gamma"]) - 0.22) < 1e-6}
    yp = np.arange(len(c1_order))
    ms = [float(p_map[k]["median_steps"]) for k, _, _ in c1_order]
    ax2.barh(yp, ms, color=[c for _, _, c in c1_order], height=0.64, zorder=3)
    ax2.set_xscale("log")
    ax2.set_xlim(60, 28000)
    ax2.set_yticks(yp)
    ax2.set_yticklabels([l for _, l, _ in c1_order], fontsize=6.3)
    ax2.invert_yaxis()
    ax2.set_xlabel("Median evals ($M=48, d=6$)")
    for i_b, mv in enumerate(ms):
        ax2.text(mv * 1.15, i_b, f"{mv:.0f}", va="center", fontsize=6.0, color=PALETTE["ink"])

    # Panel (d): Family C2 Multiple Acceptable Actions (T5.3)
    ax3 = fig.add_subplot(gs_bot[0, 1])
    style_axis(ax3, "y")
    add_header(ax3, "d", "Multiple answers (T5.3)")
    ma_map = {r["method"]: r for r in ma}
    c2_order = [
        ("support_aware_cd", "Supp-Aw.\n(CD)", PALETTE["cd_joint"]),
        ("support_aware_mc", "Supp-Aw.\n(MC)", PALETTE["mc_joint"]),
        ("greedy_answer_cd", "Greedy\n(CD)", PALETTE["gp_ucb"]),
        ("opt_sep_indep", "Opt-Sep\n(Indep.)", PALETTE["opt_sep"]),
    ]
    x_ma = np.arange(len(c2_order))
    vals_ma = [float(ma_map[k]["median_steps"]) for k, _, _ in c2_order]
    ax3.bar(x_ma, vals_ma, width=0.56, color=[c for _, _, c in c2_order], zorder=3)
    lb_a0 = float(ma_map["greedy_answer_cd"]["median_t5_lb_a0"])
    lb_a1 = float(ma_map["support_aware_cd"]["median_t5_lb_a1"])
    ax3.axhline(lb_a0, color=PALETTE["gp_ucb"], linestyle="--", linewidth=0.9, label=f"LB($a_0$)={lb_a0:.1f}")
    ax3.axhline(lb_a1, color=PALETTE["cd_joint"], linestyle=":", linewidth=1.0, label=f"LB($a_1$)={lb_a1:.2f}")
    ax3.set_yscale("log")
    ax3.set_ylim(0.35, 32000)
    ax3.set_xticks(x_ma)
    ax3.set_xticklabels([l for _, l, _ in c2_order], fontsize=6.1)
    ax3.set_ylabel("Median evaluations")
    ax3.legend(frameon=False, loc="upper left", fontsize=5.8)
    for i_b, mv in enumerate(vals_ma):
        ax3.text(i_b, mv * 1.22, f"{mv:.0f}", ha="center", va="bottom", fontsize=6.1, color=PALETTE["ink"])

    save_fig(fig, out_dir, "fig3_geometry_and_proxy", latex_dir)


# ===========================================================================
# FIGURE 4: Experiments E3 (GB1 & 21-Template TmTrpB) & E4 (WorFBench)
# ===========================================================================
def build_fig4(data_dir: Path, out_dir: Path, latex_dir: Path | None) -> None:
    prot = load_csv(data_dir / "e3_proteins/summary_e3_proteins.csv")
    wf = load_csv(data_dir / "e4_worfbench/summary_e4_worfbench.csv")
    wf_cal = load_csv(data_dir / "e4_worfbench/summary_e4_calibration.csv")

    fig = plt.figure(figsize=(5.50, 3.80))
    gs_top = fig.add_gridspec(1, 2, left=0.105, right=0.98, top=0.92, bottom=0.56, wspace=0.34)
    gs_bot = fig.add_gridspec(1, 2, left=0.185, right=0.98, top=0.40, bottom=0.11, wspace=0.40, width_ratios=[1.08, 0.95])

    # Panel (a): E3 Protein benchmarks (GB1 all vs TmTrpB 21 templates)
    ax0 = fig.add_subplot(gs_top[0, 0])
    style_axis(ax0, "y")
    add_header(ax0, "a", "E3: GB1 & 21-tmpl. TmTrpB")
    p_methods = [
        ("flat_lucb_root", "Flat\n+RC", PALETTE["flat"]),
        ("opt_sep", "Opt-\nSep", PALETTE["opt_sep"]),
        ("gp_root_info_freq", "GP-Rt\n(Freq)", PALETTE["dw_joint"]),
        ("joint_gp_ucb_nom", "UCB\n(Joint)", PALETTE["gp_ucb"]),
        ("joint_gp_cd_nom", "CD\n(Joint)", PALETTE["cd_joint"]),
        ("bayes_post_cd", "Post\n(Bayes)", PALETTE["bayes_post"]),
    ]
    gb1_map = {r["method"]: r for r in prot if r["landscape"] == "gb1" and r["stratum"] == "all"}
    trp_map = {r["method"]: r for r in prot if r["landscape"] == "trpb" and r["stratum"] == "all"}
    x_p = np.arange(len(p_methods))
    w_p = 0.36
    ax0.bar(x_p - w_p / 2, [float(gb1_map[k]["median_steps"]) for k, _, _ in p_methods], width=w_p,
            color=PALETTE["cd_joint"], alpha=0.90, label="GB1 (10 tmpl.)", zorder=3)
    ax0.bar(x_p + w_p / 2, [float(trp_map[k]["median_steps"]) for k, _, _ in p_methods], width=w_p,
            color=PALETTE["mc_joint"], alpha=0.90, label="TmTrpB (21 tmpl.)", zorder=3)
    ax0.set_yscale("log")
    ax0.set_ylim(280, 42000)
    ax0.set_xticks(x_p)
    ax0.set_xticklabels([l for _, l, _ in p_methods], fontsize=5.8)
    ax0.set_ylabel("Median assays to certify")
    ax0.legend(frameon=False, loc="upper center", ncol=2, fontsize=5.7, columnspacing=0.8, handletextpad=0.35)

    # Panel (b): E3 Empirical error rate vs certification speed trade-off (honest audit!)
    ax1 = fig.add_subplot(gs_top[0, 1])
    style_axis(ax1, "both")
    add_header(ax1, "b", "E3: Speed vs. error ($\\delta=5\\%$)")
    for land, mk in (("gb1", "o"), ("trpb", "s")):
        lmap = gb1_map if land == "gb1" else trp_map
        for k, lbl, col in p_methods:
            r = lmap[k]
            xs = float(r["median_steps"])
            ys = 100.0 * float(r["false_cert_rate"])
            ax1.scatter(xs, ys, color=col, marker=mk, s=26, zorder=4,
                        label=(lbl.replace("\n", " ") if land == "gb1" else None))
    ax1.axhline(5.0, color=PALETTE["flat"], linestyle="--", linewidth=0.85, label="Target $\\delta=5\\%$")
    ax1.set_xscale("log")
    ax1.set_xlim(320, 16000)
    ax1.set_ylim(-1.2, 20.5)
    ax1.set_xlabel("Median assays (circle: GB1, sq.: TmTrpB)")
    ax1.set_ylabel("False-cert rate (%)")
    ax1.legend(frameon=False, loc="upper right", fontsize=5.4, ncol=2, handletextpad=0.15, columnspacing=0.45)

    # Panel (c): E4 WorFBench LLM Tokens to Certify
    ax2 = fig.add_subplot(gs_bot[0, 0])
    style_axis(ax2, "x")
    add_header(ax2, "c", "E4: WorFBench LLM tokens")
    wf_map = {r["method"]: r for r in wf}
    wf_order = [
        ("bayes_post_costnorm", "Post-CD (Cost)", PALETTE["bayes_post"]),
        ("contrast_joint_costnorm", "CD-Joint (Cost)", PALETTE["cd_joint"]),
        ("contrast_joint_uniform", "CD-Joint (Unif)", PALETTE["ids"]),
        ("opt_sep", "Opt-Sep (Freq)", PALETTE["opt_sep"]),
        ("gp_ucb_joint_nom", "GP-UCB (Joint)", PALETTE["gp_ucb"]),
        ("contrast_freq_uniform", "CD + Indep. CS", PALETTE["dw_joint"]),
        ("flat_lucb_root", "Flat+RC (Freq)", PALETTE["flat"]),
    ]
    yw = np.arange(len(wf_order))
    toks_k = [float(wf_map[k]["median_llm_tokens"]) / 1e3 for k, _, _ in wf_order]
    ax2.barh(yw, toks_k, color=[c for _, _, c in wf_order], height=0.64, zorder=3)
    ax2.set_xscale("log")
    ax2.set_xlim(22, 18000)
    ax2.set_yticks(yw)
    ax2.set_yticklabels([l for _, l, _ in wf_order], fontsize=6.1)
    ax2.invert_yaxis()
    ax2.set_xlabel("Median LLM tokens (thousands)")
    for i_b, tk in enumerate(toks_k):
        ax2.text(tk * 1.15, i_b, f"{tk:.0f}k", va="center", fontsize=6.0, color=PALETTE["ink"])

    # Panel (d): E4 Feature-model out-of-sample CV R^2 calibration across WorFBench domains
    ax3 = fig.add_subplot(gs_bot[0, 1])
    style_axis(ax3, "y")
    add_header(ax3, "d", "E4: Workflow feature $R^2$")
    doms = ["all", "toolbench", "toolalpaca", "seal_tools", "webshop"]
    dom_lbl = ["All", "ToolB", "ToolA", "Seal", "WebS"]
    r2_main = [float([r for r in wf_cal if r["domain"] == d and r["feature_model"] == "main_effects_d9"][0]["cv5_r2"]) for d in doms]
    r2_pair = [float([r for r in wf_cal if r["domain"] == d and r["feature_model"] == "main_plus_pair_d33"][0]["cv5_r2"]) for d in doms]
    xd = np.arange(len(doms))
    ax3.bar(xd - 0.19, r2_main, width=0.36, color=PALETTE["ids"], label="Main ($d=9$)", zorder=3)
    ax3.bar(xd + 0.19, r2_pair, width=0.36, color=PALETTE["cd_joint"], label="Main+pair ($d=33$)", zorder=3)
    ax3.set_xticks(xd)
    ax3.set_xticklabels(dom_lbl, fontsize=6.2)
    ax3.set_ylim(0.55, 1.13)
    ax3.set_yticks([0.6, 0.7, 0.8, 0.9, 1.0])
    ax3.set_ylabel("5-fold CV $R^2$")
    ax3.legend(frameon=False, loc="upper center", ncol=2, fontsize=5.5, columnspacing=0.6, handletextpad=0.3)

    save_fig(fig, out_dir, "fig4_real_world_applications", latex_dir)


# ===========================================================================
# FIGURE 5: Experiment E5 Calibration & Misspecification Stress Test
# ===========================================================================
def build_fig5(data_dir: Path, out_dir: Path, latex_dir: Path | None) -> None:
    rows = load_csv(data_dir / "e5_calibration/summary_e5_calibration.csv")

    fig = plt.figure(figsize=(5.50, 3.05))
    gs = fig.add_gridspec(1, 3, left=0.09, right=0.985, bottom=0.18, top=0.86, wspace=0.38)

    # Panel (a): Well-specified Linear & GP Prior empirical error vs nominal delta
    ax0 = fig.add_subplot(gs[0, 0])
    style_axis(ax0, "both")
    add_header(ax0, "a", "Well-specified (C1, C2)", fontsize=7.2)
    deltas = [0.01, 0.05, 0.10]
    ax0.plot([0, 11], [0, 11], color=PALETTE["muted"], linestyle="--", linewidth=0.85, label="Nominal $y=\\delta$")
    for cond, meth, lbl, col, mk in [
        ("C1_valid_linear", "freq_ellipsoid_cd", "Linear Freq (T3.1)", PALETTE["cd_joint"], "o"),
        ("C2_valid_gp_prior", "bayes_posterior_stop", "GP Post. (T3.2)", PALETTE["bayes_post"], "s"),
        ("C2_valid_gp_prior", "nominal_ellipsoid_cd", "GP Nom. Ellip.", PALETTE["ids"], "^"),
    ]:
        sub = sorted([r for r in rows if r["condition"] == cond and r["method"] == meth], key=lambda x: float(x["delta"]))
        xs = [100.0 * float(r["delta"]) for r in sub]
        ys = [100.0 * float(r["empirical_error_rate"]) for r in sub]
        ax0.plot(xs, ys, color=col, marker=mk, markersize=4.2, linewidth=1.4, label=lbl, zorder=4)
    ax0.set_xlim(0, 11)
    ax0.set_ylim(-0.5, 12.0)
    ax0.set_xlabel("Target level $\\delta$ (%)")
    ax0.set_ylabel("Empirical error rate (%)")
    ax0.legend(frameon=False, loc="upper left", fontsize=5.6, handlelength=1.4)

    # Panel (b): Misspecified Kernel Lengthscale (C3) overconfidence
    ax1 = fig.add_subplot(gs[0, 1])
    style_axis(ax1, "y")
    add_header(ax1, "b", "Misspecified GP (C3)", fontsize=7.2)
    c3_post = sorted([r for r in rows if r["condition"] == "C3_misspec_lengthscale" and r["method"] == "bayes_posterior_stop"], key=lambda x: float(x["delta"]))
    c3_ell = sorted([r for r in rows if r["condition"] == "C3_misspec_lengthscale" and r["method"] == "nominal_ellipsoid_cd"], key=lambda x: float(x["delta"]))
    x_d = np.arange(len(deltas))
    ax1.bar(x_d - 0.18, [100.0 * float(r["empirical_error_rate"]) for r in c3_post], width=0.34,
            color=PALETTE["flat"], label="Bayes Post.", zorder=3)
    ax1.bar(x_d + 0.18, [100.0 * float(r["empirical_error_rate"]) for r in c3_ell], width=0.34,
            color=PALETTE["gp_ucb"], label="Nom. Ellip.", zorder=3)
    ax1.plot(x_d, [100.0 * d for d in deltas], color=PALETTE["ink"], linestyle="--", marker="_", markersize=8, linewidth=1.0, label="Allowed $\\delta$", zorder=4)
    ax1.set_xticks(x_d)
    ax1.set_xticklabels([f"{int(100*d)}%" for d in deltas])
    ax1.set_ylim(0, 52)
    ax1.set_xlabel("Nominal target $\\delta$")
    ax1.set_ylabel("False-cert rate (%)")
    ax1.legend(frameon=False, loc="upper left", fontsize=5.6, handlelength=1.4)

    # Panel (c): Structured Residual |b_z| <= xi stress test (C4, delta = 0.05)
    ax2 = fig.add_subplot(gs[0, 2])
    style_axis(ax2, "both")
    add_header(ax2, "c", "Residual $|b_z|\\leq\\xi$ (C4)", fontsize=7.2)
    for meth, lbl, col, mk in [
        ("unadjusted_ellipsoid", "Unadjusted Ellip.", PALETTE["flat"], "x"),
        ("t33_robust_ellipsoid", "T3.3 Robust Ellip.", PALETTE["cd_joint"], "o"),
        ("safe_hybrid_fallback", "Safe Hybrid ($\\mathcal{U}\\cap\\mathcal{B}$)", PALETTE["safe"], "s"),
    ]:
        sub = sorted([r for r in rows if r["condition"] == "C4_structured_residual" and r["method"] == meth], key=lambda x: float(x["xi"]))
        xs = [float(r["xi"]) for r in sub]
        ys = [100.0 * float(r["empirical_error_rate"]) for r in sub]
        ax2.plot(xs, ys, color=col, marker=mk, markersize=4.3, linewidth=1.45, label=lbl, zorder=4)
    ax2.axhline(5.0, color=PALETTE["ink"], linestyle="--", linewidth=0.85, label="Target $\\delta=5\\%$")
    ax2.set_xticks([0.0, 0.02, 0.04, 0.08])
    ax2.set_xticklabels(["0", ".02", ".04", ".08"])
    ax2.set_ylim(-0.6, 14.5)
    ax2.set_xlabel("Residual bound $\\xi$")
    ax2.set_ylabel("False-cert rate (%)")
    ax2.legend(frameon=False, loc="upper left", fontsize=5.5, handlelength=1.4)

    save_fig(fig, out_dir, "fig5_calibration_and_misspec", latex_dir)


# ===========================================================================
# FIGURE 6: Experiment E6 Computational Scaling & Caratheodory Sparsity
# ===========================================================================
def build_fig6(data_dir: Path, out_dir: Path, latex_dir: Path | None) -> None:
    rows = load_csv(data_dir / "e6_scaling/summary_e6_scaling.csv")

    fig = plt.figure(figsize=(5.50, 3.05))
    gs = fig.add_gridspec(1, 3, left=0.095, right=0.985, bottom=0.19, top=0.86, wspace=0.38)

    # Panel (a): Runtime per update vs M up to 4096
    ax0 = fig.add_subplot(gs[0, 0])
    style_axis(ax0, "both")
    add_header(ax0, "a", "Update time vs. $M$", fontsize=7.2)
    for solv, lbl, col, mk in [
        ("cvxpy_socp", "CVXPY SOCP", PALETTE["flat"], "s"),
        ("dense_afw", "Dense AFW", PALETTE["gp_ucb"], "^"),
        ("colgen_full", "ColGen Full", PALETTE["dw_joint"], "D"),
        ("colgen_lazy", "Lazy ColGen", PALETTE["cd_joint"], "o"),
        ("vertex_approx", "Vertex Approx", PALETTE["safe"], "v"),
    ]:
        sub = sorted([r for r in rows if r["sweep"] == "sweep_M" and r["solver"] == solv], key=lambda x: int(x["m"]))
        if not sub:
            continue
        ax0.plot([int(r["m"]) for r in sub], [float(r["ms_per_update"]) for r in sub],
                 color=col, marker=mk, markersize=3.8, linewidth=1.4, label=lbl, zorder=4)
    ax0.set_xscale("log", base=2)
    ax0.set_yscale("log")
    ax0.set_ylim(0.3, 120000)
    ax0.set_xticks([128, 512, 2048])
    ax0.set_xticklabels(["128", "512", "2048"])
    ax0.set_xlabel("Terminals $M$ ($K=8, d=8$)")
    ax0.set_ylabel("Runtime / update (ms)")
    ax0.legend(frameon=False, loc="lower right", bbox_to_anchor=(1.02, 0.33), fontsize=5.3, handlelength=1.3, labelspacing=0.16)

    # Panel (b): Caratheodory active support vs rank d (with d+1 theoretical ceiling)
    ax1 = fig.add_subplot(gs[0, 1])
    style_axis(ax1, "both")
    add_header(ax1, "b", "Sparsity vs. rank $d$", fontsize=7.2)
    sub_lz = sorted([r for r in rows if r["sweep"] == "sweep_d" and r["solver"] == "colgen_lazy"], key=lambda x: int(x["d"]))
    sub_cf = sorted([r for r in rows if r["sweep"] == "sweep_d" and r["solver"] == "colgen_full"], key=lambda x: int(x["d"]))
    ds = [int(r["d"]) for r in sub_lz]
    ax1.plot(ds, [d + 1 for d in ds], color=PALETTE["flat"], linestyle="--", linewidth=1.15, label="Bound $d+1$ (T1.3)", zorder=3)
    ax1.plot(ds, [int(r["max_active_support"]) for r in sub_lz], color=PALETTE["cd_joint"], marker="o", markersize=4.2, linewidth=1.45, label="Lazy ColGen", zorder=4)
    ax1.plot([int(r["d"]) for r in sub_cf], [int(r["max_active_support"]) for r in sub_cf], color=PALETTE["dw_joint"], marker="D", markersize=3.6, linewidth=1.25, linestyle=":", label="Full ColGen", zorder=4)
    ax1.set_xscale("log", base=2)
    ax1.set_yscale("log", base=2)
    ax1.set_xticks(ds)
    ax1.set_xticklabels([str(d) for d in ds])
    ax1.set_yticks([4, 8, 16, 32, 64])
    ax1.set_yticklabels(["4", "8", "16", "32", "64"])
    ax1.set_ylim(3.2, 92)
    ax1.set_xlabel("Feature rank $d$ ($M=512$)")
    ax1.set_ylabel("Max $|\\mathrm{supp}(p^*)|$")
    ax1.legend(frameon=False, loc="upper left", fontsize=5.5, handlelength=1.4)

    # Panel (c): Lazy challenger pruning rate & compact vs fragmented topology
    ax2 = fig.add_subplot(gs[0, 2])
    style_axis(ax2, "y")
    add_header(ax2, "c", "Lazy pruning", fontsize=7.2)
    sub_top = [r for r in rows if r["sweep"] == "sweep_topo" and r["solver"] == "colgen_lazy"]
    cats = [(512, "compact", "512\nComp"), (512, "fragmented", "512\nFrag"), (2048, "compact", "2048\nComp"), (2048, "fragmented", "2048\nFrag")]
    pruned = []
    ms_vals = []
    for mv, st, _ in cats:
        hit = [r for r in sub_top if int(r["m"]) == mv and r["support_style"] == st]
        pruned.append(100.0 * float(hit[0]["pruned_frac"]) if hit else 0.0)
        ms_vals.append(float(hit[0]["ms_per_update"]) if hit else 0.0)
    xc = np.arange(len(cats))
    bars = ax2.bar(xc, pruned, width=0.55, color=[PALETTE["cd_joint"], PALETTE["mc_joint"], PALETTE["cd_joint"], PALETTE["mc_joint"]], zorder=3)
    ax2.set_xticks(xc)
    ax2.set_xticklabels([l for _, _, l in cats], fontsize=6.1)
    ax2.set_ylim(0, 120)
    ax2.set_yticks([0, 25, 50, 75, 100])
    ax2.set_ylabel("Pruned lazily (%)")
    for b, pr, ms_v in zip(bars, pruned, ms_vals):
        lbl_t = f"{ms_v/1000:.1f}s" if ms_v >= 1000 else f"{ms_v:.0f}ms"
        ax2.text(b.get_x() + b.get_width() / 2, pr + 2.2, f"{pr:.0f}%\n({lbl_t})", ha="center", va="bottom", fontsize=5.5, color=PALETTE["ink"])

    save_fig(fig, out_dir, "fig6_computational_scaling", latex_dir)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--latex-figures-dir", type=Path, default=None)
    args = ap.parse_args()

    build_fig1(args.data_dir, args.out_dir, args.latex_figures_dir)
    build_fig2(args.data_dir, args.out_dir, args.latex_figures_dir)
    build_fig3(args.data_dir, args.out_dir, args.latex_figures_dir)
    build_fig4(args.data_dir, args.out_dir, args.latex_figures_dir)
    build_fig5(args.data_dir, args.out_dir, args.latex_figures_dir)
    build_fig6(args.data_dir, args.out_dir, args.latex_figures_dir)
    dests = [str(args.out_dir)] + ([str(args.latex_figures_dir)] if args.latex_figures_dir else [])
    print(f"Generated 6 publication figures in {dests}.")


if __name__ == "__main__":
    main()
