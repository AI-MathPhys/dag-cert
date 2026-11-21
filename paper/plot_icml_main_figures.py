#!/usr/bin/env python3
"""Generate the 4 unified ICML main-paper figures from frozen benchmark CSVs.

Canvas geometry matches iclr2027_conference.sty (\\textwidth = 5.50 in = 396 pt)
with captions in \\small (9.0 pt Times). All figures save at exact 5.50 in width
without tight-bbox rescaling so rendered glyphs remain 7.2--8.2 pt sans-serif
(just slightly smaller than the 9.0 pt figure caption and strictly >= 7.0 pt).
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path
import sys

import matplotlib as mpl
mpl.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
import numpy as np

# ---------------------------------------------------------------------------
# Unified semantic colorblind-safe palette (constant identity across all figs)
# ---------------------------------------------------------------------------
PALETTE = {
    "exact": "#0B5394",        # Exact-Regret-DAG-LUCB (UCB-inside hero)
    "hybrid": "#0E8A74",       # Safeguarded-LCB (parameter-free hybrid)
    "varde": "#7A3E9D",        # VarDE-Exact
    "ugape": "#D55E00",        # UGapE-DAG
    "lucb": "#5C6B73",         # LUCB-micro (marginal)
    "lcb": "#B8860B",          # LCB-inside / LCB-fast
    "opt_sep": "#2B8CBE",      # Optimistic-Separation
    "dual_cover": "#0B5394",   # Charged Dual Covers
    "dec_sel": "#0E8A74",      # Decision-Selective
    "direct_graph": "#D55E00", # Direct Graph Regret
    "eager": "#5C6B73",        # Graph-Eager
    "ink": "#1F2933",          # Dark neutral ink
    "muted": "#6B7785",        # Secondary gray
    "grid": "#E5E9F0",         # Subtle guide rule
    "panel_bg": "#F8FAFC",     # Schematic subtle fill
    "alert_red": "#B8332A",    # False-challenger highlight
    "flat_lucb": "#B8332A",    # Flat-LUCB (terminal stop)
    "flat_root": "#D55E00",    # Flat-LUCB + Exact Root Certificate
    "gp_root": "#1B7837",      # GP-Root-Info (surrogate + root witness)
    "gp_ts": "#CC79A7",        # GP-Thompson Sampling
    "gp_ei": "#8C510A",        # GP-Expected Improvement
}

mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
    "font.size": 7.8,
    "axes.titlesize": 8.0,
    "axes.labelsize": 7.8,
    "xtick.labelsize": 7.3,
    "ytick.labelsize": 7.3,
    "legend.fontsize": 7.3,
    "axes.linewidth": 0.75,
    "xtick.major.width": 0.70,
    "ytick.major.width": 0.70,
    "xtick.minor.width": 0.50,
    "ytick.minor.width": 0.50,
    "xtick.major.size": 3.0,
    "ytick.major.size": 3.0,
    "xtick.minor.size": 1.8,
    "ytick.minor.size": 1.8,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "svg.fonttype": "none",
})


def load_csv(data_dir: Path, name: str) -> list[dict[str, str]]:
    with (data_dir / name).open("r", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def det_offsets(n: int, half_span: float) -> np.ndarray:
    if n <= 1:
        return np.zeros(n, dtype=float)
    return np.linspace(-half_span, half_span, n)


def style_axis(ax: plt.Axes, grid_axis: str = "both") -> None:
    ax.patch.set_facecolor("none")
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_color(PALETTE["ink"])
    ax.spines["bottom"].set_color(PALETTE["ink"])
    ax.tick_params(colors=PALETTE["ink"], pad=2.5)
    if grid_axis in ("x", "y", "both"):
        ax.grid(True, which="major", axis=grid_axis, color=PALETTE["grid"], linewidth=0.55, zorder=0)
    ax.set_axisbelow(True)


def add_panel_header(ax: plt.Axes, tag: str, title: str, y_pad: float = 1.055) -> None:
    ax.text(
        0.0, y_pad, f"({tag})  {title}",
        transform=ax.transAxes,
        fontsize=8.0, fontweight="bold", color=PALETTE["ink"],
        ha="left", va="bottom", clip_on=False,
    )


def save_both(fig: plt.Figure, out_dirs: list[Path], stem: str, qa_dir: Path | None) -> list[Path]:
    saved: list[Path] = []
    fig.canvas.draw()
    if qa_dir is not None:
        qa_dir.mkdir(parents=True, exist_ok=True)
        try:
            from audit_panel_alignment import require_matplotlib_panel_alignment

            require_matplotlib_panel_alignment(
                fig,
                json_out=qa_dir / f"{stem}.alignment.json",
                overlay_svg=qa_dir / f"{stem}.alignment.svg",
                strict=True,
            )
        except ImportError:
            pass
        fig.savefig(qa_dir / f"{stem}.svg", format="svg")
        fig.savefig(qa_dir / f"{stem}.png", format="png", dpi=600)
    for out_dir in out_dirs:
        out_dir.mkdir(parents=True, exist_ok=True)
        pdf_path = out_dir / f"{stem}.pdf"
        fig.savefig(pdf_path, format="pdf")
        saved.append(pdf_path)
    plt.close(fig)
    return saved


# ===========================================================================
# FIGURE 1: Concept + Toy Certificate Failure + Witness & Cover Pipeline (2x2)
# ===========================================================================
def build_fig1_concept(out_dirs: list[Path], qa_dir: Path | None) -> list[Path]:
    fig = plt.figure(figsize=(5.50, 3.12))
    gs = fig.add_gridspec(
        2, 2,
        left=0.025, right=0.975, bottom=0.035, top=0.915,
        wspace=0.10, hspace=0.28,
        width_ratios=[1.0, 1.0], height_ratios=[1.0, 1.0],
    )
    axes = [
        fig.add_subplot(gs[0, 0]),
        fig.add_subplot(gs[0, 1]),
        fig.add_subplot(gs[1, 0]),
        fig.add_subplot(gs[1, 1]),
    ]
    for ax in axes:
        ax.set_xlim(0.0, 1.0)
        ax.set_ylim(0.0, 1.0)
        ax.axis("off")
        ax.add_patch(FancyBboxPatch(
            (0.015, 0.02), 0.97, 0.94,
            boxstyle="round,pad=0.01,rounding_size=0.03",
            facecolor=PALETTE["panel_bg"], edgecolor="#D5DCE4", linewidth=0.75, zorder=0,
        ))

    def draw_node(ax_i, cx, cy, w, h, label, fc, ec, tc="#FFFFFF", fw="bold", fs=7.5):
        box = FancyBboxPatch(
            (cx - w / 2, cy - h / 2), w, h,
            boxstyle="round,pad=0.01,rounding_size=0.028",
            facecolor=fc, edgecolor=ec, linewidth=0.9, zorder=3,
        )
        ax_i.add_patch(box)
        ax_i.text(cx, cy, label, ha="center", va="center", fontsize=fs, fontweight=fw, color=tc, zorder=4)

    # ---- Panel (a): Small DAG with shared strong terminal ----
    ax = axes[0]
    add_panel_header(ax, "a", "Search DAG with shared terminal zsh", y_pad=1.01)
    draw_node(ax, 0.50, 0.83, 0.28, 0.14, "Root s0", "#334E68", "#1F2933", fs=7.5)
    draw_node(ax, 0.27, 0.54, 0.30, 0.14, "Action a1", PALETTE["exact"], PALETTE["exact"], fs=7.5)
    draw_node(ax, 0.73, 0.54, 0.30, 0.14, "Action a2", PALETTE["lucb"], PALETTE["lucb"], fs=7.5)

    draw_node(ax, 0.17, 0.22, 0.26, 0.24, "z1\n[.72, .78]", "#EBF3FA", PALETTE["exact"], tc=PALETTE["exact"], fs=7.2)
    draw_node(ax, 0.50, 0.22, 0.28, 0.24, "zsh\n[.65, .95]", "#FFF3E6", PALETTE["ugape"], tc="#9C4200", fs=7.2)
    draw_node(ax, 0.83, 0.22, 0.26, 0.24, "z2\n[.35, .55]", "#F1F3F5", PALETTE["lucb"], tc=PALETTE["ink"], fs=7.2)

    for (x0, y0), (x1, y1), col in [
        ((0.42, 0.75), (0.30, 0.63), PALETTE["ink"]),
        ((0.58, 0.75), (0.70, 0.63), PALETTE["ink"]),
        ((0.23, 0.46), (0.18, 0.36), PALETTE["exact"]),
        ((0.33, 0.46), (0.45, 0.36), PALETTE["ugape"]),
        ((0.67, 0.46), (0.55, 0.36), PALETTE["ugape"]),
        ((0.77, 0.46), (0.82, 0.36), PALETTE["lucb"]),
    ]:
        ax.add_patch(FancyArrowPatch(
            (x0, y0), (x1, y1),
            arrowstyle="-|>,head_length=3.5,head_width=2.2",
            linewidth=0.95, color=col, zorder=2,
        ))

    # ---- Panel (b): Marginal certificate keeps zsh as false challenger ----
    ax = axes[1]
    add_panel_header(ax, "b", "Marginal bounds double-count zsh", y_pad=1.01)

    def val_to_x(v: float) -> float:
        return 0.42 + (v - 0.30) / 0.70 * 0.50

    ax.plot([val_to_x(0.30), val_to_x(1.00)], [0.23, 0.23], color=PALETTE["ink"], lw=0.75)
    for v in (0.4, 0.6, 0.8, 1.0):
        xv = val_to_x(v)
        ax.plot([xv, xv], [0.20, 0.23], color=PALETTE["ink"], lw=0.75)
        ax.text(xv, 0.16, f"{v:.1f}", ha="center", va="top", fontsize=7.2, color=PALETTE["muted"])

    ax.text(0.05, 0.77, "Action a1", fontsize=7.4, fontweight="bold", color=PALETTE["exact"], va="center")
    ax.plot([val_to_x(0.72), val_to_x(0.95)], [0.77, 0.77], color=PALETTE["exact"], lw=2.8, solid_capstyle="round")
    ax.scatter([val_to_x(0.72)], [0.77], s=24, color=PALETTE["exact"], zorder=4)

    ax.text(0.05, 0.56, "Action a2 (zsh)", fontsize=7.4, fontweight="bold", color=PALETTE["alert_red"], va="center")
    ax.plot([val_to_x(0.65), val_to_x(0.95)], [0.56, 0.56], color=PALETTE["alert_red"], lw=2.8, solid_capstyle="round")
    ax.scatter([val_to_x(0.95)], [0.56], s=24, color=PALETTE["alert_red"], zorder=4)

    xl, xu = val_to_x(0.72), val_to_x(0.95)
    ax.annotate(
        "", xy=(xu, 0.39), xytext=(xl, 0.39),
        arrowprops=dict(arrowstyle="<->", color=PALETTE["alert_red"], lw=1.1),
    )
    ax.text(0.05, 0.39, "False gap .23 > \u03b5", fontsize=7.3, fontweight="bold", color=PALETTE["alert_red"], va="center")

    # ---- Panel (c): Exact regret removes inside-support competition ----
    ax = axes[2]
    add_panel_header(ax, "c", "Exact regret excludes shared support", y_pad=1.01)
    ax.plot([val_to_x(0.30), val_to_x(1.00)], [0.23, 0.23], color=PALETTE["ink"], lw=0.75)
    for v in (0.4, 0.6, 0.8, 1.0):
        xv = val_to_x(v)
        ax.plot([xv, xv], [0.20, 0.23], color=PALETTE["ink"], lw=0.75)
        ax.text(xv, 0.16, f"{v:.1f}", ha="center", va="top", fontsize=7.2, color=PALETTE["muted"])

    ax.text(0.05, 0.79, "Inside L(a1) = .72", fontsize=7.4, fontweight="bold", color=PALETTE["exact"], va="center")
    ax.plot([val_to_x(0.72), val_to_x(0.78)], [0.79, 0.79], color=PALETTE["exact"], lw=2.8, solid_capstyle="round")
    ax.scatter([val_to_x(0.72)], [0.79], s=24, color=PALETTE["exact"], zorder=4)

    ax.text(0.05, 0.59, "zsh in S(a1): drop", fontsize=7.3, color=PALETTE["muted"], va="center")
    ax.plot([val_to_x(0.65), val_to_x(0.95)], [0.59, 0.59], color="#CBD5E1", lw=2.0, ls="--")

    ax.text(0.05, 0.39, "Out u(z2) = .55", fontsize=7.4, fontweight="bold", color=PALETTE["hybrid"], va="center")
    ax.plot([val_to_x(0.35), val_to_x(0.55)], [0.39, 0.39], color=PALETTE["hybrid"], lw=2.8, solid_capstyle="round")
    ax.scatter([val_to_x(0.55)], [0.39], s=24, color=PALETTE["hybrid"], zorder=4)
    ax.text(0.76, 0.39, "R(a1) = 0", fontsize=7.4, fontweight="bold", color=PALETTE["hybrid"], va="center")

    # ---- Panel (d): Witness sampling & dual covers ----
    ax = axes[3]
    add_panel_header(ax, "d", "Witness & dual-cover loop", y_pad=1.01)
    draw_node(ax, 0.50, 0.79, 0.88, 0.18, "1. Pick leader at = argmin R(a)", "#EBF3FA", PALETTE["exact"], tc=PALETTE["ink"], fs=7.4)
    draw_node(ax, 0.50, 0.50, 0.88, 0.18, "2. Query wider of zin in S(at), qt out", "#E8F6F3", PALETTE["hybrid"], tc=PALETTE["ink"], fs=7.4)
    draw_node(ax, 0.50, 0.21, 0.90, 0.18, "3. Update dual covers; test \u2264 \u03b5", "#F4ECF7", PALETTE["varde"], tc=PALETTE["ink"], fs=7.4)

    for y0, y1 in ((0.69, 0.60), (0.40, 0.31)):
        ax.add_patch(FancyArrowPatch(
            (0.50, y0), (0.50, y1),
            arrowstyle="-|>,head_length=3.4,head_width=2.2",
            linewidth=1.0, color=PALETTE["ink"], zorder=2,
        ))

    return save_both(fig, out_dirs, "fig1_concept_overview", qa_dir)


# ===========================================================================
# FIGURE 2: Main Statistical & Zero-Containment Natural Benchmark Performance
# ===========================================================================
def build_fig2_statistical(data_dir: Path, out_dirs: list[Path], qa_dir: Path | None) -> list[Path]:
    fig = plt.figure(figsize=(5.50, 4.38))
    gs = fig.add_gridspec(
        2, 2,
        left=0.115, right=0.980, bottom=0.100, top=0.835,
        wspace=0.51, hspace=0.46,
        width_ratios=[1.0, 1.0], height_ratios=[1.0, 1.0],
    )
    ax_a = fig.add_subplot(gs[0, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[1, 0])
    ax_d = fig.add_subplot(gs[1, 1])

    legend_handles = [
        Line2D([0], [0], color=PALETTE["exact"], marker="o", lw=1.6, ms=4.5, label="Exact-Regret-DAG-LUCB"),
        Line2D([0], [0], color=PALETTE["hybrid"], marker="D", lw=1.5, ls="--", ms=4.0, label="Safeguarded-LCB"),
        Line2D([0], [0], color=PALETTE["varde"], marker="^", lw=1.5, ms=4.5, label="VarDE-Exact"),
        Line2D([0], [0], color=PALETTE["ugape"], marker="s", lw=1.5, ms=4.2, label="UGapE-DAG"),
        Line2D([0], [0], color=PALETTE["lucb"], marker="v", lw=1.5, ms=4.5, label="LUCB-micro"),
    ]
    fig.legend(
        handles=legend_handles, loc="upper center", bbox_to_anchor=(0.53, 0.992),
        ncol=3, frameon=False, handlelength=1.8, columnspacing=1.1, handletextpad=0.45,
        fontsize=7.4,
    )

    # ---- Panel (a): Overlap sweep (M=256, Hoeffding box) ----
    style_axis(ax_a, "both")
    add_panel_header(ax_a, "a", "Overlap sweep (M = 256)", y_pad=1.055)
    ov_rows = [r for r in load_csv(data_dir, "fig2a_overlap_sweep.csv") if r["suite"] == "overlap_256_box"]
    series_cfg = [
        ("lucb_micro_marg", PALETTE["lucb"], "v", "-"),
        ("ugape_mcts_dag_marg", PALETTE["ugape"], "s", "-"),
        ("varde_exact", PALETTE["varde"], "^", "-"),
        ("exact_dag_lucb", PALETTE["exact"], "o", "-"),
    ]
    ax_a.axhline(1000.0, color=PALETTE["muted"], ls=":", lw=0.8, zorder=1)
    ax_a.text(0.53, 1180.0, "1.0 s", fontsize=7.2, color=PALETTE["muted"], va="bottom", ha="left")

    for method, color, marker, ls in series_cfg:
        pts = sorted([r for r in ov_rows if r["method"] == method], key=lambda x: float(x["rho"]))
        xs = np.array([float(r["rho"]) for r in pts])
        med = np.array([float(r["ms_med"]) for r in pts])
        q25 = np.array([float(r["ms_q25"]) for r in pts])
        q75 = np.array([float(r["ms_q75"]) for r in pts])
        cert = np.array([float(r["cert_rate"]) for r in pts])

        ax_a.fill_between(xs, q25, q75, color=color, alpha=0.16, linewidth=0, zorder=2)
        ax_a.plot(xs, med, color=color, ls=ls, lw=1.55, zorder=3)
        uncens = cert > 0.0
        cens = ~uncens
        if np.any(uncens):
            ax_a.scatter(xs[uncens], med[uncens], color=color, marker=marker, s=22, zorder=4)
        if np.any(cens):
            ax_a.scatter(xs[cens], med[cens], facecolors="#FFFFFF", edgecolors=color, marker=marker, lw=1.2, s=24, zorder=4)

    ax_a.set_yscale("log")
    ax_a.set_ylim(42.0, 1750.0)
    ax_a.set_yticks([50, 100, 250, 500, 1000])
    ax_a.set_yticklabels(["50", "100", "250", "500", "1k"])
    ax_a.minorticks_off()
    ax_a.set_xlim(-0.04, 0.93)
    ax_a.set_xticks([0.0, 0.25, 0.50, 0.75, 0.88])
    ax_a.set_xticklabels(["0", ".25", ".50", ".75", ".88"])
    ax_a.set_xlabel("Support overlap \u03c1")
    ax_a.set_ylabel("Cert. time (ms)")

    # ---- Panel (b): Paired per-instance runtime ratio vs LUCB-micro ----
    style_axis(ax_b, "x")
    add_panel_header(ax_b, "b", "Zero-containment ratio", y_pad=1.055)
    rat_rows = load_csv(data_dir, "fig2b_paired_instance_ratios.csv")
    strata_order = [
        ("endgame_15x15_d4_zero_contain", "15x15 end"),
        ("random_6x6_d4_zero_contain", "6x6 d=4"),
        ("routing_w32_d5_zero_contain", "Route W32"),
        ("routing_w96_d5_zero_contain", "Route W96"),
    ]
    ax_b.axvline(1.0, color=PALETTE["ink"], ls="--", lw=0.85, zorder=1)
    method_offsets = [
        ("ugape_mcts_dag_marg", +0.22, PALETTE["ugape"], "s"),
        ("varde_exact", 0.00, PALETTE["varde"], "^"),
        ("exact_dag_lucb", -0.22, PALETTE["exact"], "o"),
    ]
    for row_idx, (st_key, _) in enumerate(strata_order):
        y_base = 3 - row_idx
        for m_key, dy, color, marker in method_offsets:
            vals = np.sort(np.array([
                float(r["time_ratio"]) for r in rat_rows
                if r["stratum"] == st_key and r["method"] == m_key
            ]))
            offsets = det_offsets(len(vals), 0.045)
            ax_b.scatter(vals, np.full_like(vals, y_base + dy) + offsets, color=color, alpha=0.38, s=11, linewidths=0, zorder=2)
            med = float(np.median(vals))
            q25, q75 = float(np.percentile(vals, 25)), float(np.percentile(vals, 75))
            ax_b.plot([q25, q75], [y_base + dy, y_base + dy], color=color, lw=1.6, zorder=3)
            ax_b.scatter([med], [y_base + dy], color=color, marker=marker, s=26, edgecolors="#FFFFFF", linewidths=0.4, zorder=4)

    ax_b.set_xscale("log")
    ax_b.set_xlim(0.33, 1.32)
    ax_b.set_xticks([0.4, 0.6, 0.8, 1.0, 1.2])
    ax_b.set_xticklabels(["0.4x", "0.6x", "0.8x", "1.0x", "1.2x"])
    ax_b.minorticks_off()
    ax_b.set_yticks([3, 2, 1, 0])
    ax_b.set_yticklabels([lbl for _, lbl in strata_order])
    ax_b.set_ylim(-0.52, 3.52)
    ax_b.set_xlabel("Time / LUCB-micro (log)")

    # ---- Panel (c): Hard mid-game SameGame certification vs time budget ----
    style_axis(ax_c, "both")
    add_panel_header(ax_c, "c", "Mid-game cert. vs budget", y_pad=1.055)
    mid_rows = load_csv(data_dir, "fig2cd_midgame_runs.csv")
    grid_t = np.linspace(0.0, 1.80, 181)
    curve_specs = [
        ("exp9", "lucb_micro_marg", PALETTE["lucb"], "-"),
        ("exp9", "ugape_mcts_dag_marg", PALETTE["ugape"], "-"),
        ("exp9", "varde_exact", PALETTE["varde"], "-."),
        ("exp9", "exact_dag_lucb", PALETTE["exact"], "-"),
        ("exp11", "inside_hybrid", PALETTE["hybrid"], "--"),
    ]
    for src, m_key, color, ls in curve_specs:
        sub = [r for r in mid_rows if r["source"] == src and r["method"] == m_key]
        n_tot = len(sub)
        cert_times = np.array([float(r["total_ms"]) / 1000.0 for r in sub if int(r["certified"]) == 1])
        frac = np.array([np.sum(cert_times <= t) / n_tot * 100.0 for t in grid_t])
        ax_c.step(grid_t, frac, where="post", color=color, ls=ls, lw=1.55, zorder=3)

    ax_c.set_xlim(0.0, 1.82)
    ax_c.set_ylim(0.0, 52.0)
    ax_c.set_xticks([0.0, 0.5, 1.0, 1.5, 1.8])
    ax_c.set_yticks([0, 15, 30, 45])
    ax_c.set_xlabel("Wall-clock budget (s)")
    ax_c.set_ylabel("Certified runs (%)")

    # ---- Panel (d): Conditional time among certified mid-game runs ----
    style_axis(ax_d, "x")
    add_panel_header(ax_d, "d", "Time given certification", y_pad=1.055)
    cond_specs = [
        ("exp11", "inside_hybrid", "Safeguard", PALETTE["hybrid"], "D"),
        ("exp9", "exact_dag_lucb", "Exact LUCB", PALETTE["exact"], "o"),
        ("exp9", "varde_exact", "VarDE-Ex.", PALETTE["varde"], "^"),
        ("exp9", "ugape_mcts_dag_marg", "UGapE-DAG", PALETTE["ugape"], "s"),
        ("exp9", "lucb_micro_marg", "LUCB-mic.", PALETTE["lucb"], "v"),
    ]
    for idx, (src, m_key, lbl, color, marker) in enumerate(cond_specs):
        y_pos = 4 - idx
        sub = [r for r in mid_rows if r["source"] == src and r["method"] == m_key]
        vals = np.sort(np.array([float(r["total_ms"]) for r in sub if int(r["certified"]) == 1]))
        offsets = det_offsets(len(vals), 0.11)
        ax_d.scatter(vals, np.full_like(vals, y_pos) + offsets, color=color, alpha=0.38, s=13, linewidths=0, zorder=2)
        med = float(np.median(vals))
        q25, q75 = float(np.percentile(vals, 25)), float(np.percentile(vals, 75))
        ax_d.plot([q25, q75], [y_pos, y_pos], color=color, lw=1.8, zorder=3)
        ax_d.scatter([med], [y_pos], color=color, marker=marker, s=28, edgecolors="#FFFFFF", linewidths=0.45, zorder=4)

    ax_d.set_xscale("log")
    ax_d.set_xlim(55.0, 2150.0)
    ax_d.set_xticks([80, 200, 500, 1400])
    ax_d.set_xticklabels(["80", "200", "500", "1.4k"])
    ax_d.minorticks_off()
    ax_d.set_yticks([4, 3, 2, 1, 0])
    ax_d.set_yticklabels([s[2] for s in cond_specs])
    ax_d.set_ylim(-0.55, 4.55)
    ax_d.set_xlabel("Cert. time | certified (ms)")

    return save_both(fig, out_dirs, "fig2_statistical_performance", qa_dir)


# ===========================================================================
# APPENDIX DIAGNOSTIC FIGURE: Inside-Witness Mechanism, Hybrid & Tied-Star
# ===========================================================================
def build_fig_app_inside_witness(data_dir: Path, out_dirs: list[Path], qa_dir: Path | None) -> list[Path]:
    fig = plt.figure(figsize=(5.50, 2.58))
    gs = fig.add_gridspec(
        1, 3,
        left=0.045, right=0.980, bottom=0.185, top=0.785,
        wspace=0.47, width_ratios=[1.0, 1.0, 1.0],
    )
    ax_a = fig.add_subplot(gs[0, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[0, 2])

    legend_handles = [
        Line2D([0], [0], color=PALETTE["exact"], marker="o", lw=1.5, ms=4.3, label="UCB-inside (Exact LUCB)"),
        Line2D([0], [0], color=PALETTE["hybrid"], marker="D", lw=1.5, ls="--", ms=4.0, label="Safeguarded-LCB"),
        Line2D([0], [0], color=PALETTE["lcb"], marker="p", lw=1.5, ls=":", ms=4.5, label="LCB-fast"),
        Line2D([0], [0], color=PALETTE["opt_sep"], marker="h", lw=1.5, ls="-.", ms=4.5, label="Opt.-Separation"),
    ]
    fig.legend(
        handles=legend_handles, loc="upper center", bbox_to_anchor=(0.51, 0.99),
        ncol=4, frameon=False, handlelength=1.6, columnspacing=0.80, handletextpad=0.38,
        fontsize=7.2,
    )

    # ---- Panel (a): Schematic of slack gate on decoy vs wide support ----
    ax_a.set_xlim(0.0, 1.0)
    ax_a.set_ylim(0.0, 1.0)
    ax_a.axis("off")
    ax_a.add_patch(FancyBboxPatch(
        (0.01, 0.01), 0.98, 0.98,
        boxstyle="round,pad=0.01,rounding_size=0.035",
        facecolor=PALETTE["panel_bg"], edgecolor="#D5DCE4", linewidth=0.75, zorder=0,
    ))
    add_panel_header(ax_a, "a", "Slack-gate rule", y_pad=1.055)

    ax_a.text(0.07, 0.89, "Decoy trap:", fontsize=7.3, fontweight="bold", color=PALETTE["ink"])
    ax_a.text(0.07, 0.77, "yt", fontsize=7.2, fontweight="bold", color=PALETTE["lcb"], va="center")
    ax_a.plot([0.28, 0.48], [0.77, 0.77], color=PALETTE["lcb"], lw=2.5, solid_capstyle="round")
    ax_a.text(0.07, 0.65, "pt", fontsize=7.2, fontweight="bold", color=PALETTE["exact"], va="center")
    ax_a.plot([0.24, 0.90], [0.65, 0.65], color=PALETTE["exact"], lw=2.5, solid_capstyle="round")
    ax_a.text(0.07, 0.52, "Gate fails \u2192 pick pt", fontsize=7.1, fontweight="bold", color=PALETTE["hybrid"])

    ax_a.plot([0.07, 0.93], [0.47, 0.47], color="#D5DCE4", lw=0.75)

    ax_a.text(0.07, 0.36, "Wide support:", fontsize=7.3, fontweight="bold", color=PALETTE["ink"])
    ax_a.text(0.07, 0.25, "yt", fontsize=7.2, fontweight="bold", color=PALETTE["lcb"], va="center")
    ax_a.plot([0.28, 0.84], [0.25, 0.25], color=PALETTE["lcb"], lw=2.5, solid_capstyle="round")
    ax_a.text(0.07, 0.14, "pt", fontsize=7.2, fontweight="bold", color=PALETTE["exact"], va="center")
    ax_a.plot([0.25, 0.89], [0.14, 0.14], color=PALETTE["exact"], lw=2.5, solid_capstyle="round")
    ax_a.text(0.07, 0.03, "Gate holds \u2192 pick yt", fontsize=7.1, fontweight="bold", color=PALETTE["hybrid"])

    # ---- Panel (b): Certification rate across diagnostic stress regimes ----
    style_axis(ax_b, "x")
    add_panel_header(ax_b, "b", "Stress-test rate", y_pad=1.055)
    reg_rows = load_csv(data_dir, "fig_app_inside_regimes.csv")
    star_rows = [r for r in load_csv(data_dir, "fig_app_star_eps_sweep.csv") if float(r["eps"]) == 0.0]

    regimes = [
        ("decoy_trap_16", "Decoy-16"),
        ("window_64", "Win-64"),
        ("hetero_support_256", "Het-256"),
        ("star_eps0", "Star \u03b5=0"),
    ]
    m_styles = [
        ("ucb", +0.21, PALETTE["exact"], "o"),
        ("hybrid", +0.07, PALETTE["hybrid"], "D"),
        ("lcb_fast", -0.07, PALETTE["lcb"], "p"),
        ("opt_sep", -0.21, PALETTE["opt_sep"], "h"),
    ]
    for r_idx, (r_key, _) in enumerate(regimes):
        y0 = 3 - r_idx
        for m_key, dy, color, marker in m_styles:
            if r_key == "star_eps0":
                match = [r for r in star_rows if r["method"] == m_key]
            else:
                match = [r for r in reg_rows if r["family"] == r_key and r["method"] == m_key]
            if not match:
                continue
            rate = float(match[0]["cert_rate"]) * 100.0
            ax_b.plot([0.0, rate], [y0 + dy, y0 + dy], color=color, lw=1.1, alpha=0.45, zorder=2)
            ax_b.scatter([rate], [y0 + dy], color=color, marker=marker, s=24, zorder=3)

    ax_b.set_xlim(-4.0, 108.0)
    ax_b.set_xticks([0, 50, 100])
    ax_b.set_yticks([3, 2, 1, 0])
    ax_b.set_yticklabels([lbl for _, lbl in regimes])
    ax_b.set_ylim(-0.48, 3.48)
    ax_b.set_xlabel("Certified runs (%)")

    # ---- Panel (c): Mid-game SameGame time-budget curves across inside rules ----
    style_axis(ax_c, "both")
    add_panel_header(ax_c, "c", "Mid-game budget", y_pad=1.055)
    mid_rows = load_csv(data_dir, "fig2cd_midgame_runs.csv")
    grid_t = np.linspace(0.0, 1.80, 181)
    c_specs = [
        ("exp11", "inside_lcb_fast", PALETTE["lcb"], ":"),
        ("exp11", "inside_hybrid", PALETTE["hybrid"], "--"),
        ("exp11", "inside_ucb", PALETTE["exact"], "-"),
        ("exp11", "inside_opt_sep", PALETTE["opt_sep"], "-."),
    ]
    for src, m_key, color, ls in c_specs:
        sub = [r for r in mid_rows if r["source"] == src and r["method"] == m_key]
        cert_t = np.array([float(r["total_ms"]) / 1000.0 for r in sub if int(r["certified"]) == 1])
        frac = np.array([np.sum(cert_t <= t) / len(sub) * 100.0 for t in grid_t])
        ax_c.step(grid_t, frac, where="post", color=color, ls=ls, lw=1.55, zorder=3)

    ax_c.set_xlim(0.0, 1.82)
    ax_c.set_ylim(0.0, 54.0)
    ax_c.set_xticks([0.0, 0.6, 1.2, 1.8])
    ax_c.set_yticks([0, 20, 40])
    ax_c.set_xlabel("Wall-clock budget (s)")
    ax_c.set_ylabel("Certified (%)")

    return save_both(fig, out_dirs, "fig_app_inside_witness", qa_dir)


# ===========================================================================
# FIGURE 4: End-to-End Computational Maintenance (-O3 C++17, Coupled Traces)
# ===========================================================================
def build_fig4_computational(data_dir: Path, out_dirs: list[Path], qa_dir: Path | None) -> list[Path]:
    fig = plt.figure(figsize=(5.50, 2.55))
    gs = fig.add_gridspec(
        1, 3,
        left=0.090, right=0.982, bottom=0.190, top=0.785,
        wspace=0.45, width_ratios=[1.0, 1.0, 1.0],
    )
    ax_a = fig.add_subplot(gs[0, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[0, 2])

    cpp_rows = load_csv(data_dir, "fig4_cpp_maintenance.csv")

    legend_handles = [
        Line2D([0], [0], color=PALETTE["dual_cover"], marker="o", lw=1.5, ms=4.3, label="Dual Covers"),
        Line2D([0], [0], color=PALETTE["dec_sel"], marker="D", lw=1.5, ls="--", ms=4.0, label="Decision-Sel."),
        Line2D([0], [0], color=PALETTE["direct_graph"], marker="s", lw=1.5, ms=4.2, label="Direct Graph"),
        Line2D([0], [0], color=PALETTE["eager"], marker="v", lw=1.5, ms=4.3, label="Graph-Eager"),
    ]
    fig.legend(
        handles=legend_handles, loc="upper center", bbox_to_anchor=(0.53, 0.99),
        ncol=4, frameon=False, handlelength=1.6, columnspacing=0.95, handletextpad=0.4,
        fontsize=7.3,
    )

    # ---- Panel (a): C++17 Root-PUCT scaling ----
    style_axis(ax_a, "y")
    add_panel_header(ax_a, "a", "Root-PUCT scaling", y_pad=1.055)
    puct_rows = [r for r in cpp_rows if r["suite"] == "root_puct_scaling"]
    for method, color, marker, ls in [
        ("graph-eager", PALETTE["eager"], "v", "-"),
        ("decision-selective", PALETTE["dec_sel"], "D", "--"),
        ("dual-covers", PALETTE["dual_cover"], "o", "-"),
    ]:
        pts = sorted([r for r in puct_rows if r["method"] == method], key=lambda x: int(x["m"]))
        ms_x = np.array([int(r["m"]) for r in pts], dtype=float)
        med = np.array([float(r["end_ms_med"]) for r in pts])
        q25 = np.array([float(r["end_ms_q25"]) for r in pts])
        q75 = np.array([float(r["end_ms_q75"]) for r in pts])
        ax_a.fill_between(ms_x, q25, q75, color=color, alpha=0.18, linewidth=0, zorder=2)
        ax_a.plot(ms_x, med, color=color, ls=ls, lw=1.55, marker=marker, ms=4.2, zorder=3)

    ax_a.text(90.0, 224.0, "10.4x faster", fontsize=7.1, fontweight="bold", color=PALETTE["dec_sel"], ha="center", va="center")
    ax_a.set_xscale("log", base=4)
    ax_a.set_yscale("log")
    ax_a.set_xticks([16, 64, 256, 1024, 4096])
    ax_a.set_xticklabels(["16", "64", "256", "1k", "4k"])
    ax_a.set_yticks([1, 10, 100, 500])
    ax_a.set_yticklabels(["1", "10", "100", "500"])
    ax_a.minorticks_off()
    ax_a.set_ylim(0.35, 850.0)
    ax_a.set_xlabel("Funnel fan-in m")
    ax_a.set_ylabel("C++ time (ms)")

    # ---- Panel (b): Representation inversion on Parity Grid ----
    style_axis(ax_b, "y")
    add_panel_header(ax_b, "b", "Parity-grid cost", y_pad=1.055)
    par_rows = [r for r in cpp_rows if r["suite"] == "parity_grid"]
    for method, color, marker, ls in [
        ("dual-covers", PALETTE["dual_cover"], "o", "-"),
        ("direct-graph-regret", PALETTE["direct_graph"], "s", "-"),
        ("graph-eager", PALETTE["eager"], "v", "-"),
        ("decision-selective", PALETTE["dec_sel"], "D", "--"),
    ]:
        pts = sorted([r for r in par_rows if r["method"] == method], key=lambda x: int(float(x["param"])))
        rs = np.array([float(r["param"]) for r in pts], dtype=float)
        med = np.array([float(r["end_ms_med"]) for r in pts])
        q25 = np.array([float(r["end_ms_q25"]) for r in pts])
        q75 = np.array([float(r["end_ms_q75"]) for r in pts])
        ax_b.fill_between(rs, q25, q75, color=color, alpha=0.16, linewidth=0, zorder=2)
        ax_b.plot(rs, med, color=color, ls=ls, lw=1.5, marker=marker, ms=4.1, zorder=3)

    ax_b.text(8.2, 5.5, "5.2 ms init", fontsize=7.1, fontweight="bold", color=PALETTE["dual_cover"], ha="left", va="center")
    ax_b.set_xscale("log", base=2)
    ax_b.set_yscale("log")
    ax_b.set_xticks([8, 16, 32])
    ax_b.set_xticklabels(["8", "16", "32"])
    ax_b.set_yticks([0.5, 2, 8])
    ax_b.set_yticklabels(["0.5", "2", "8"])
    ax_b.minorticks_off()
    ax_b.set_ylim(0.30, 15.0)
    ax_b.set_xlabel("Parity grid rank r")
    ax_b.set_ylabel("C++ time (ms)")

    # ---- Panel (c): UCT funnel horizon crossover vs Graph-Eager ----
    style_axis(ax_c, "both")
    add_panel_header(ax_c, "c", "UCT horizon ratio", y_pad=1.055)
    uct_rows = [r for r in cpp_rows if r["suite"] == "uct_funnel_gap"]
    fam_keys = ["table2_funnel256_g200", "table2_funnel256_g075", "table2_funnel256_g035"]
    eager_map = {
        fk: float([r for r in uct_rows if r["family"] == fk and r["method"] == "graph-eager"][0]["end_ms_med"])
        for fk in fam_keys
    }
    ax_c.axhline(1.0, color=PALETTE["eager"], ls="--", lw=0.85, zorder=1)
    x_idx = np.array([0, 1, 2], dtype=float)
    for method, color, marker, ls in [
        ("decision-selective", PALETTE["dec_sel"], "D", "--"),
        ("dual-covers", PALETTE["dual_cover"], "o", "-"),
    ]:
        ratios = np.array([
            float([r for r in uct_rows if r["family"] == fk and r["method"] == method][0]["end_ms_med"]) / eager_map[fk]
            for fk in fam_keys
        ])
        ax_c.plot(x_idx, ratios, color=color, ls=ls, lw=1.55, marker=marker, ms=4.3, zorder=3)

    ax_c.set_xlim(-0.25, 2.25)
    ax_c.set_ylim(0.22, 1.28)
    ax_c.set_xticks([0, 1, 2])
    ax_c.set_xticklabels(["3.1k", "14.9k", "37.2k"])
    ax_c.set_yticks([0.4, 0.7, 1.0, 1.2])
    ax_c.set_yticklabels(["0.4x", "0.7x", "1.0x", "1.2x"])
    ax_c.set_xlabel("Coupled rollouts T")
    ax_c.set_ylabel("Time / Eager")

    return save_both(fig, out_dirs, "fig4_computational_efficiency", qa_dir)


# ===========================================================================
# FIGURE 3: Real-World Applications — Protein Engineering, BO & Agent Workflows (2x2)
# ===========================================================================
def build_fig3_real_world(data_dir: Path, out_dirs: list[Path], qa_dir: Path | None) -> list[Path]:
    if not (data_dir / "fig3a_gb1_factorial_runs.csv").is_file():
        return []

    fig = plt.figure(figsize=(5.50, 4.44))
    gs = fig.add_gridspec(
        2, 2,
        left=0.125, right=0.980, bottom=0.100, top=0.818,
        wspace=0.54, hspace=0.47,
        width_ratios=[1.0, 1.0], height_ratios=[1.0, 1.0],
    )
    ax_a = fig.add_subplot(gs[0, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[1, 0])
    ax_d = fig.add_subplot(gs[1, 1])

    legend_handles = [
        Line2D([0], [0], color=PALETTE["gp_root"], marker="h", lw=1.6, ms=4.4, label="GP-Root-Info"),
        Line2D([0], [0], color=PALETTE["opt_sep"], marker="P", lw=1.6, ms=4.5, label="Optimistic-Sep"),
        Line2D([0], [0], color=PALETTE["exact"], marker="o", lw=1.6, ms=4.3, label="Exact-Regret-LUCB"),
        Line2D([0], [0], color=PALETTE["hybrid"], marker="D", lw=1.5, ls="--", ms=4.0, label="Safeguarded-LCB"),
        Line2D([0], [0], color=PALETTE["flat_root"], marker="s", lw=1.5, ls="--", ms=4.1, label="Flat-LUCB + Root"),
        Line2D([0], [0], color=PALETTE["flat_lucb"], marker="X", lw=1.5, ms=4.4, label="Flat-LUCB (Term.)"),
        Line2D([0], [0], color=PALETTE["lucb"], marker="v", lw=1.5, ls=":", ms=4.3, label="LUCB-micro"),
        Line2D([0], [0], color=PALETTE["gp_ts"], marker="p", lw=1.5, ls="--", ms=4.3, label="GP-UCB / TS"),
    ]
    fig.legend(
        handles=legend_handles, loc="upper center", bbox_to_anchor=(0.53, 0.994),
        ncol=4, frameon=False, handlelength=1.60, columnspacing=0.80, handletextpad=0.36,
        labelspacing=0.34, fontsize=7.15,
    )

    # ---- Panel (a): GB1 protein campaigns — Certified fraction vs assay budget ----
    style_axis(ax_a, "both")
    add_panel_header(ax_a, "a", "GB1 protein cert. vs assays", y_pad=1.055)
    gb1_runs = load_csv(data_dir, "fig3a_gb1_factorial_runs.csv")
    grid_k = np.linspace(0.0, 45.0, 226)
    ecdf_specs = [
        ("lucb_micro_marg", PALETTE["lucb"], ":"),
        ("flat_lucb_term", PALETTE["flat_lucb"], "-"),
        ("flat_lucb_root", PALETTE["flat_root"], "--"),
        ("safeguarded_lcb", PALETTE["hybrid"], "--"),
        ("exact_dag_lucb", PALETTE["exact"], "-"),
        ("opt_sep", PALETTE["opt_sep"], "-"),
    ]
    for m_key, color, ls in ecdf_specs:
        sub = [r for r in gb1_runs if r["method"] == m_key]
        n_tot = max(1, len(sub))
        cert_k = np.array([float(r["steps"]) / 1000.0 for r in sub if int(r["certified"]) == 1])
        frac = np.array([np.sum(cert_k <= b) / n_tot * 100.0 for b in grid_k])
        ax_a.step(grid_k, frac, where="post", color=color, ls=ls, lw=1.5, zorder=3)

    if (data_dir / "fig3cd_gb1_bo_runs.csv").is_file():
        bo_runs = load_csv(data_dir, "fig3cd_gb1_bo_runs.csv")
        for m_key, color, ls in (
            ("gp_ts", PALETTE["gp_ts"], "--"),
            ("gp_root_info", PALETTE["gp_root"], "-"),
        ):
            sub = [r for r in bo_runs if r["method"] == m_key]
            n_tot = max(1, len(sub))
            cert_k = np.array([float(r["steps"]) / 1000.0 for r in sub if int(r["certified"]) == 1])
            frac = np.array([np.sum(cert_k <= b) / n_tot * 100.0 for b in grid_k])
            ax_a.step(grid_k, frac, where="post", color=color, ls=ls, lw=1.55, zorder=4)

    ax_a.set_xlim(0.0, 45.5)
    ax_a.set_ylim(-2.0, 105.0)
    ax_a.set_xticks([0, 15, 30, 45])
    ax_a.set_xticklabels(["0", "15k", "30k", "45k"])
    ax_a.set_yticks([0, 25, 50, 75, 100])
    ax_a.set_xlabel("Binding assays")
    ax_a.set_ylabel("Certified runs (%)")

    # ---- Panel (b): GB1 BO — Sequence Discovery vs Root Certification Dumbbell ----
    style_axis(ax_b, "x")
    add_panel_header(ax_b, "b", "BO discovery vs root cert.", y_pad=1.055)
    if (data_dir / "fig3c_gb1_bo_summary.csv").is_file():
        bo_sum = {r["method"]: r for r in load_csv(data_dir, "fig3c_gb1_bo_summary.csv")}
        bo_rows_cfg = [
            ("gp_root_info", "GP-Root", PALETTE["gp_root"]),
            ("opt_sep", "Opt.-Sep", PALETTE["opt_sep"]),
            ("exact_dag_lucb", "Exact LUCB", PALETTE["exact"]),
            ("flat_lucb_root", "Flat+Root", PALETTE["flat_root"]),
            ("gp_ts", "GP-TS", PALETTE["gp_ts"]),
            ("gp_ei", "GP-EI", PALETTE["gp_ei"]),
            ("gp_ucb", "GP-UCB", PALETTE["lcb"]),
        ]
        n_bo = len(bo_rows_cfg) - 1
        for idx, (m_key, _, color) in enumerate(bo_rows_cfg):
            if m_key not in bo_sum:
                continue
            y_pos = n_bo - idx
            r = bo_sum[m_key]
            d_med = max(10.0, float(r["discover_med"]))
            c_med = float(r["cert_med"])
            c_rate = float(r["cert_rate"])
            ax_b.plot([d_med, c_med], [y_pos, y_pos], color=color, lw=1.45, alpha=0.72, zorder=2)
            ax_b.scatter([d_med], [y_pos], color=color, marker="d", s=22, zorder=3)
            if c_rate >= 0.90:
                ax_b.scatter([c_med], [y_pos], color=color, marker="o", s=26, edgecolors="#FFFFFF", linewidths=0.4, zorder=4)
            else:
                ax_b.scatter([c_med], [y_pos], facecolors="#FFFFFF", edgecolors=color, marker=">", lw=1.2, s=28, zorder=4)

        db_handles = [
            Line2D([0], [0], color="none", marker="d", markerfacecolor=PALETTE["ink"], markeredgecolor=PALETTE["ink"], ms=4.0, label="Find"),
            Line2D([0], [0], color="none", marker="o", markerfacecolor=PALETTE["ink"], markeredgecolor=PALETTE["ink"], ms=4.1, label="Cert."),
        ]
        ax_b.legend(
            handles=db_handles, loc="center left", bbox_to_anchor=(0.35, 0.56), frameon=False,
            handletextpad=0.18, labelspacing=0.18, borderaxespad=0.10, fontsize=7.05,
        )
        ax_b.set_xscale("log")
        ax_b.set_xlim(18.0, 68000.0)
        ax_b.set_xticks([30, 300, 3000, 45000])
        ax_b.set_xticklabels(["30", "300", "3k", "45k"])
        ax_b.minorticks_off()
        ax_b.set_yticks(list(range(n_bo, -1, -1)))
        ax_b.set_yticklabels([lbl for _, lbl, _ in bo_rows_cfg])
        ax_b.set_ylim(-0.55, n_bo + 0.55)
        ax_b.set_xlabel("Assays (log)")

    # ---- Panel (c): WorFBench (Qwen3-0.6B) — Certified fraction vs task evals ----
    style_axis(ax_c, "both")
    add_panel_header(ax_c, "c", "WorFBench cert. vs evals", y_pad=1.055)
    wf_runs = load_csv(data_dir, "fig3c_worfbench_factorial_runs.csv")
    grid_w = np.linspace(0.0, 35.0, 176)
    for m_key, color, ls in ecdf_specs:
        sub = [r for r in wf_runs if r["method"] == m_key]
        n_tot = max(1, len(sub))
        cert_w = np.array([float(r["steps"]) / 1000.0 for r in sub if int(r["certified"]) == 1])
        frac = np.array([np.sum(cert_w <= b) / n_tot * 100.0 for b in grid_w])
        ax_c.step(grid_w, frac, where="post", color=color, ls=ls, lw=1.5, zorder=3)

    ax_c.set_xlim(0.0, 35.5)
    ax_c.set_ylim(-2.0, 105.0)
    ax_c.set_xticks([0, 10, 20, 35])
    ax_c.set_xticklabels(["0", "10k", "20k", "35k"])
    ax_c.set_yticks([0, 25, 50, 75, 100])
    ax_c.set_xlabel("Held-out task evals")
    ax_c.set_ylabel("Certified runs (%)")

    # ---- Panel (d): WorFBench cumulative Qwen3-0.6B LLM tokens to certify ----
    style_axis(ax_d, "x")
    add_panel_header(ax_d, "d", "Qwen3 LLM tokens to cert.", y_pad=1.055)
    tok_order = [
        ("opt_sep", "Opt.-Sep", PALETTE["opt_sep"], "P"),
        ("exact_dag_lucb", "Exact LUCB", PALETTE["exact"], "o"),
        ("flat_lucb_root", "Flat+Root", PALETTE["flat_root"], "s"),
        ("flat_lucb_term", "Flat-LUCB", PALETTE["flat_lucb"], "X"),
        ("lucb_micro_marg", "LUCB-mic.", PALETTE["lucb"], "v"),
    ]
    all_mtoks = []
    camp_keys = sorted({(r["domain"], r["campaign"]) for r in wf_runs})
    for idx, (m_key, _, color, marker) in enumerate(tok_order):
        y_pos = 4 - idx
        c_meds = []
        c_certs = []
        for dom, camp in camp_keys:
            sub_c = [r for r in wf_runs if r["domain"] == dom and r["campaign"] == camp and r["method"] == m_key]
            if not sub_c:
                continue
            c_meds.append(float(np.median([float(r["estimated_llm_tokens"]) / 1e6 for r in sub_c])))
            c_certs.append(float(np.mean([int(r["certified"]) for r in sub_c])))
        if not c_meds:
            continue
        vals = np.array(c_meds)
        certs = np.array(c_certs)
        order_i = np.argsort(vals)
        vals = vals[order_i]
        certs = certs[order_i]
        all_mtoks.extend(vals.tolist())
        offs = det_offsets(len(vals), 0.11)
        unc = certs > 0.5
        cen = ~unc
        if np.any(unc):
            ax_d.scatter(vals[unc], np.full(np.sum(unc), y_pos) + offs[unc], color=color, alpha=0.40, s=11, linewidths=0, zorder=2)
        if np.any(cen):
            ax_d.scatter(vals[cen], np.full(np.sum(cen), y_pos) + offs[cen], facecolors="#FFFFFF", edgecolors=color, marker=">", lw=0.75, s=13, alpha=0.65, zorder=2)
        med = float(np.median(vals))
        q25, q75 = float(np.percentile(vals, 25)), float(np.percentile(vals, 75))
        ax_d.plot([q25, q75], [y_pos, y_pos], color=color, lw=1.65, zorder=3)
        if float(np.mean(certs)) > 0.5:
            ax_d.scatter([med], [y_pos], color=color, marker=marker, s=27, edgecolors="#FFFFFF", linewidths=0.45, zorder=4)
        else:
            ax_d.scatter([med], [y_pos], facecolors="#FFFFFF", edgecolors=color, marker=">", lw=1.2, s=29, zorder=4)

    xmin = max(0.25, min(all_mtoks) * 0.72) if all_mtoks else 0.4
    xmax = max(all_mtoks) * 1.32 if all_mtoks else 25.0
    ax_d.set_xscale("log")
    ax_d.set_xlim(xmin, xmax)
    ax_d.set_xticks([0.6, 2.0, 6.0, 18.0])
    ax_d.set_xticklabels(["0.6M", "2M", "6M", "18M"])
    ax_d.minorticks_off()
    ax_d.set_yticks([4, 3, 2, 1, 0])
    ax_d.set_yticklabels([lbl for _, lbl, _, _ in tok_order])
    ax_d.set_ylim(-0.55, 4.55)
    ax_d.set_xlabel("Qwen3 LLM tokens (log)")

    return save_both(fig, out_dirs, "fig3_real_world_applications", qa_dir)


# ===========================================================================
# APPENDIX FIGURE: Correlated GP Ellipsoids, Kernel Misspecification & Ridges
# ===========================================================================
def build_fig_app_bo_correlation(data_dir: Path, out_dirs: list[Path], qa_dir: Path | None) -> list[Path]:
    if not (data_dir / "fig_bo_corr_1d.csv").is_file():
        return []

    fig = plt.figure(figsize=(5.50, 4.48))
    gs = fig.add_gridspec(
        2, 2,
        left=0.155, right=0.980, bottom=0.100, top=0.822,
        wspace=0.52, hspace=0.48,
        width_ratios=[1.0, 1.0], height_ratios=[1.0, 1.0],
    )
    ax_a = fig.add_subplot(gs[0, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[1, 0])
    ax_d = fig.add_subplot(gs[1, 1])

    legend_handles = [
        Line2D([0], [0], color=PALETTE["exact"], marker="o", lw=1.6, ms=4.3, label="RKHS Ellipsoid"),
        Line2D([0], [0], color=PALETTE["ugape"], marker="s", lw=1.5, ls="--", ms=4.1, label="RKHS Enclosing Box"),
        Line2D([0], [0], color=PALETTE["gp_root"], marker="h", lw=1.5, ms=4.3, label="GP-Root (Freq. Box)"),
        Line2D([0], [0], color=PALETTE["opt_sep"], marker="P", lw=1.5, ls="-.", ms=4.4, label="Optimistic-Sep"),
    ]
    fig.legend(
        handles=legend_handles, loc="upper center", bbox_to_anchor=(0.54, 0.992),
        ncol=2, frameon=False, handlelength=1.7, columnspacing=1.2, handletextpad=0.42,
        labelspacing=0.32, fontsize=7.25,
    )

    # ---- Panel (a): 1D Controlled GP Correlation Sweep ----
    style_axis(ax_a, "y")
    add_panel_header(ax_a, "a", "GP correlation & ellipsoid", y_pad=1.055)
    c1_rows = load_csv(data_dir, "fig_bo_corr_1d.csv")
    c1_specs = [
        ("rkhs_box", PALETTE["ugape"], "s", "--"),
        ("opt_sep", PALETTE["opt_sep"], "P", "-."),
        ("gp_root_freq", PALETTE["gp_root"], "h", "-"),
        ("rkhs_ellipsoid", PALETTE["exact"], "o", "-"),
    ]
    for m_key, color, marker, ls in c1_specs:
        pts = sorted([r for r in c1_rows if r["method"] == m_key], key=lambda x: float(x["rho"]))
        if not pts:
            continue
        xs = np.array([float(r["rho"]) for r in pts])
        med = np.array([float(r["steps_med"]) / 1000.0 for r in pts])
        q25 = np.array([float(r["steps_q25"]) / 1000.0 for r in pts])
        q75 = np.array([float(r["steps_q75"]) / 1000.0 for r in pts])
        cert = np.array([float(r["cert_rate"]) for r in pts])
        ax_a.fill_between(xs, q25, q75, color=color, alpha=0.14, linewidth=0, zorder=2)
        ax_a.plot(xs, med, color=color, ls=ls, lw=1.55, zorder=3)
        unc = cert > 0.5
        cen = ~unc
        if np.any(unc):
            ax_a.scatter(xs[unc], med[unc], color=color, marker=marker, s=22, zorder=4)
        if np.any(cen):
            ax_a.scatter(xs[cen], med[cen], facecolors="#FFFFFF", edgecolors=color, marker=marker, lw=1.2, s=24, zorder=4)

    ax_a.set_xlim(-0.04, 0.94)
    ax_a.set_ylim(0.0, 17.2)
    ax_a.set_xticks([0.0, 0.25, 0.50, 0.75, 0.90])
    ax_a.set_xticklabels(["0", ".25", ".50", ".75", ".90"])
    ax_a.set_yticks([0, 4, 8, 12, 16])
    ax_a.set_yticklabels(["0", "4k", "8k", "12k", "16k"])
    ax_a.set_xlabel("Correlation \u03c1")
    ax_a.set_ylabel("Cert. evals")

    # ---- Panel (b): 2D Within vs Cross-Support Correlation Phase Grid ----
    style_axis(ax_b, "none")
    add_panel_header(ax_b, "b", "Ellipsoid / Opt.-Sep ratio", y_pad=1.055)
    c2_rows = load_csv(data_dir, "fig_bo_corr_2d.csv")
    levels = [0.0, 0.45, 0.9]
    mat = np.ones((3, 3), dtype=float)
    for i_r, rin in enumerate(levels):
        for j_c, rout in enumerate(levels):
            match = [
                r for r in c2_rows
                if abs(float(r["rho_in"]) - rin) < 1e-6
                and abs(float(r["rho_out"]) - rout) < 1e-6
                and r["method"] == "rkhs_ellipsoid"
            ]
            if match:
                mat[i_r, j_c] = float(match[0]["ratio_vs_opt_sep"])

    im = ax_b.imshow(mat, cmap="PuBu_r", vmin=0.35, vmax=1.85, aspect="auto", origin="lower")
    for i_r in range(3):
        for j_c in range(3):
            val = mat[i_r, j_c]
            txt_c = "#FFFFFF" if val < 0.85 else PALETTE["ink"]
            ax_b.text(
                j_c, i_r, f"{val:.2f}x",
                ha="center", va="center", fontsize=7.3, fontweight="bold", color=txt_c,
            )
    ax_b.set_xticks([0, 1, 2])
    ax_b.set_xticklabels(["0", ".45", ".90"])
    ax_b.set_yticks([0, 1, 2])
    ax_b.set_yticklabels(["0", ".45", ".90"])
    ax_b.set_xlabel("Cross-support \u03c1 (out)")
    ax_b.set_ylabel("Within \u03c1 (in)")

    # ---- Panel (c): GB1 GP Kernel Misspecification Ablation ----
    style_axis(ax_c, "x")
    add_panel_header(ax_c, "c", "GB1 kernel misspecification", y_pad=1.055)
    ms_rows = load_csv(data_dir, "fig_bo_gb1_misspec.csv")
    k_specs = [
        ("structured", "Structured", PALETTE["gp_root"]),
        ("hamming", "Hamming", PALETTE["exact"]),
        ("scrambled_desc", "Scrambled", PALETTE["ugape"]),
        ("oversmooth", "Over-smooth", PALETTE["alert_red"]),
    ]
    for idx, (k_key, _, color) in enumerate(k_specs):
        y_pos = 3 - idx
        match = [r for r in ms_rows if r["method"] == "gp_root_info" and r["kernel_mode"] == k_key]
        if not match:
            continue
        r = match[0]
        d_med = max(20.0, float(r["discover_med"]))
        c_med = float(r["cert_med"])
        c_rate = float(r["cert_rate"])
        ax_c.plot([d_med, c_med], [y_pos, y_pos], color=color, lw=1.55, alpha=0.80, zorder=2)
        ax_c.scatter([d_med], [y_pos], color=color, marker="d", s=22, zorder=3)
        if c_rate > 0.5:
            ax_c.scatter([c_med], [y_pos], color=color, marker="o", s=27, edgecolors="#FFFFFF", linewidths=0.4, zorder=4)
        else:
            ax_c.scatter([c_med], [y_pos], facecolors="#FFFFFF", edgecolors=color, marker=">", lw=1.2, s=28, zorder=4)

    ax_c.set_xscale("log")
    ax_c.set_xlim(40.0, 65000.0)
    ax_c.set_xticks([100, 1000, 10000, 45000])
    ax_c.set_xticklabels(["100", "1k", "10k", "45k"])
    ax_c.minorticks_off()
    ax_c.set_yticks([3, 2, 1, 0])
    ax_c.set_yticklabels([lbl for _, lbl, _ in k_specs])
    ax_c.set_ylim(-0.52, 3.52)
    ax_c.set_xlabel("GB1 assays (Find \u2192 Cert.)")

    # ---- Panel (d): GB1 (10) + Unselected 21-template TrpB Ridge Scatter ----
    style_axis(ax_d, "none")
    add_panel_header(ax_d, "d", "GB1 & TrpB ridge effect", y_pad=1.055)
    ridge_rows = load_csv(data_dir, "fig3b_protein_ridges.csv")
    ax_d.axhline(1.0, color=PALETTE["ink"], ls="--", lw=0.85, zorder=1)
    for l_key, color, unc_marker in (
        ("trpb", PALETTE["varde"], "s"),
        ("gb1", PALETTE["flat_root"], "o"),
    ):
        sub_l = [r for r in ridge_rows if r["landscape"] == l_key]
        if not sub_l:
            continue
        xs_arr = np.array([max(0.85, min(95.0, float(r["gamma_over_flat"]))) for r in sub_l])
        ys_arr = np.array([float(r["flat_root_over_os"]) for r in sub_l])
        c_arr = np.array([float(r["flat_root_cert_rate"]) for r in sub_l])
        unc = c_arr > 0.5
        cen = ~unc
        if np.any(unc):
            ax_d.scatter(xs_arr[unc], ys_arr[unc], color=color, marker=unc_marker, s=20, alpha=0.88, zorder=3)
        if np.any(cen):
            ax_d.scatter(xs_arr[cen], ys_arr[cen], facecolors="#FFFFFF", edgecolors=color, marker="^", lw=1.15, s=25, zorder=4)

    in_handles = [
        Line2D([0], [0], color="none", marker="o", markerfacecolor=PALETTE["flat_root"], markeredgecolor=PALETTE["flat_root"], ms=4.0, label="GB1"),
        Line2D([0], [0], color="none", marker="s", markerfacecolor=PALETTE["varde"], markeredgecolor=PALETTE["varde"], ms=3.8, label="TrpB"),
        Line2D([0], [0], color="none", marker="^", markerfacecolor="#FFFFFF", markeredgecolor=PALETTE["ink"], markeredgewidth=1.1, ms=4.3, label=">45k"),
    ]
    ax_d.legend(
        handles=in_handles, loc="upper left", bbox_to_anchor=(0.01, 1.01), ncol=3, frameon=False,
        columnspacing=0.55, handletextpad=0.18, borderaxespad=0.10, fontsize=7.05,
    )
    ax_d.set_xscale("log")
    ax_d.set_yscale("log")
    ax_d.set_xlim(0.72, 115.0)
    ax_d.set_ylim(0.62, 8.2)
    ax_d.set_xticks([1, 3, 10, 30, 90])
    ax_d.set_xticklabels(["1x", "3x", "10x", "30x", "90x"])
    ax_d.set_yticks([1, 2, 4])
    ax_d.set_yticklabels(["1x", "2x", "4x"])
    ax_d.minorticks_off()
    ax_d.set_xlabel("Ridge ratio \u0393 / \u0394f")
    ax_d.set_ylabel("Flat+Root / Opt.-Sep")

    return save_both(fig, out_dirs, "fig_app_bo_correlation", qa_dir)


def _default_data_dir() -> Path:
    here = Path(__file__).resolve().parent
    for cand in (
        here / "data" / "icml_figures_data",
        here.parent / "results" / "uct_v4_icml_baselines" / "icml_figures_data",
    ):
        if cand.exists():
            return cand
    return here / "data" / "icml_figures_data"


def _default_out_dirs() -> list[Path]:
    here = Path(__file__).resolve().parent
    if (here.parent / "main.tex").exists():
        return [here.parent / "figures"]
    dirs = [here.parent / "results" / "uct_v4_icml_baselines" / "figures"]
    sibling_latex = here.parent.parent / "dag-uct-latex" / "figures"
    if sibling_latex.parent.exists():
        dirs.append(sibling_latex)
    return dirs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=None,
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        action="append",
        default=None,
    )
    parser.add_argument(
        "--qa-dir",
        type=Path,
        default=None,
        help="Optional scratch directory for strict panel-alignment QA manifests.",
    )
    args = parser.parse_args()
    data_dir = args.data_dir or _default_data_dir()
    out_dirs = args.out_dir or _default_out_dirs()

    paths: list[Path] = []
    paths.extend(build_fig1_concept(out_dirs, args.qa_dir))
    paths.extend(build_fig2_statistical(data_dir, out_dirs, args.qa_dir))
    paths.extend(build_fig3_real_world(data_dir, out_dirs, args.qa_dir))
    paths.extend(build_fig4_computational(data_dir, out_dirs, args.qa_dir))
    paths.extend(build_fig_app_inside_witness(data_dir, out_dirs, args.qa_dir))
    paths.extend(build_fig_app_bo_correlation(data_dir, out_dirs, args.qa_dir))
    print("Generated figures:", [str(p) for p in paths])


if __name__ == "__main__":
    main()
