#!/usr/bin/env python3
"""Publication figure generator for v11 Statistical Validity Audit & 36-Campaign Live Replication.

Generates `fig_v11_validity_ablation_and_live36.pdf` (+ 260-DPI QA PNG), matching `iclr2027_conference.sty`
(`\\textwidth = 5.50 in`), Okabe-Ito colorblind-safe palette, zero overlaps:
  (a) P0 Protein Certificate-Validity Factorial on GB1 & TmTrpB (25k medians):
      Separates Formal DF (`OS`, `EB+DF`, `Strict EB&DF`), Bounded-Residual (`Rob.005`), and
      Empirically Calibrated Model-Based (`EB+LOO`).
  (b) P0 Exact Coupled-Stream Replay (holding observation streams 100% identical):
      Shows the two-way synergy: on `os_stream` EB+LOO saves only 1.30--1.62x; on `eb_stream`
      DF stalls (0% at 25k) while EB+LOO stops at 2.9k / 4.4k.
  (c) P1 36-Campaign 4-Domain Fresh Live Qwen3-0.6B Replication (cap=60):
      Fresh LLM tokens (k) & certification rate across TB, TA, ST, WS, and ALL (`0/36` DF vs `36/36` EB).
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib as mpl
mpl.use("Agg")
from matplotlib.patches import Patch
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATA = ROOT / "results/bayesian_ucd_v1"
DEFAULT_OUT = ROOT / "results/bayesian_ucd_v1/figures"

PAL = {
    "df": "#5C6B73",
    "df_alt": "#8899A6",
    "df_strict": "#2B5B84",
    "rob": "#B8860B",
    "eb": "#0E8A74",
    "nom": "#D55E00",
    "ink": "#1F2933",
    "grid": "#E5E9F0",
}

mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
    "mathtext.fontset": "dejavusans",
    "font.size": 6.7,
    "axes.titlesize": 6.5,
    "axes.labelsize": 6.5,
    "xtick.labelsize": 5.6,
    "ytick.labelsize": 5.6,
    "legend.fontsize": 4.9,
    "axes.linewidth": 0.72,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})


def load_csv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def style_axis(ax: plt.Axes, grid_axis: str = "y") -> None:
    ax.patch.set_facecolor("none")
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_color(PAL["ink"])
    ax.spines["bottom"].set_color(PAL["ink"])
    ax.tick_params(colors=PAL["ink"], pad=1.8)
    ax.grid(True, which="major", axis=grid_axis, color=PAL["grid"], linewidth=0.5, zorder=0)
    ax.set_axisbelow(True)


def add_header(ax: plt.Axes, tag: str, title: str, y_pad: float = 1.05) -> None:
    ax.text(0.0, y_pad, f"({tag}) {title}", transform=ax.transAxes, ha="left", va="bottom",
            fontsize=6.4, fontweight="bold", color=PAL["ink"])


def plot_v11(data_dir: Path, out_dir: Path) -> None:
    s1a = load_csv(data_dir / "v11_exp1_protein_validity_ablation/v11_exp1_interactive_summary.csv")
    s1b = load_csv(data_dir / "v11_exp1_protein_validity_ablation/v11_exp1_replay_summary.csv")
    s2 = load_csv(data_dir / "v11_exp2_live_worfbench_36campaigns/v11_exp2_live_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.38))
    fig.subplots_adjust(left=0.075, right=0.985, bottom=0.25, top=0.83, wspace=0.35)

    # ------------------------------------------------------------------
    # Panel (a): P0 Interactive Validity Factorial (25k median assays, GB1 & TmTrpB)
    # ------------------------------------------------------------------
    ax = axes[0]
    style_axis(ax, "y")
    add_header(ax, "a", "P0 Validity ablation (25k)")
    m_specs = [
        ("os_df_stop", "OS\n(DF)", PAL["df"]),
        ("eb_pure_df_stop", "EB acq\n(DF)", PAL["df_alt"]),
        ("eb_acq_eb_and_df_strict", "Strict\nEB&DF", PAL["df_strict"]),
        ("eb_acq_rob005_stop", "Rob.\n.005", PAL["rob"]),
        ("eb_acq_eb_stop", "EB+LOO\n(Mod.)", PAL["eb"]),
    ]
    x = np.arange(len(m_specs))
    w = 0.36
    gb1_m = [float(next(r for r in s1a if r["landscape"] == "gb1" and r["method"] == m)["med_steps_25k"]) / 1000.0 for m, _, _ in m_specs]
    trp_m = [float(next(r for r in s1a if r["landscape"] == "trpb" and r["method"] == m)["med_steps_25k"]) / 1000.0 for m, _, _ in m_specs]
    cols = [c for _, _, c in m_specs]
    ax.bar(x - w / 2, gb1_m, width=w, color=cols, edgecolor="white", linewidth=0.5, zorder=3)
    ax.bar(x + w / 2, trp_m, width=w, color=cols, alpha=0.48, edgecolor=cols, linewidth=0.55, hatch="///", zorder=3)
    for i, (g, t) in enumerate(zip(gb1_m, trp_m)):
        if g >= 24.9 and t >= 24.9:
            ax.text(i, 25.6, "25k\n(cap)", ha="center", va="bottom", fontsize=4.3, fontweight="bold", color=cols[i], linespacing=0.95)
        else:
            ax.text(i - w / 2 - 0.02, g + 0.45, f"{g:.1f}", ha="center", va="bottom", fontsize=4.2, fontweight="bold", color=cols[i])
            ax.text(i + w / 2 + 0.03, t + 0.45, f"{t:.1f}", ha="center", va="bottom", fontsize=4.2, color=cols[i])
    ax.set_xticks(x)
    ax.set_xticklabels([lbl for _, lbl, _ in m_specs], fontsize=5.0)
    ax.set_ylabel("Med. assays (k, cap 25k)")
    ax.set_ylim(0, 32.0)
    ax.legend(
        handles=[
            Patch(facecolor=PAL["df"], edgecolor="white", label="GB1 (solid)"),
            Patch(facecolor=PAL["df"], alpha=0.48, edgecolor=PAL["df"], hatch="///", label="TrpB (hatch)"),
        ],
        frameon=False, loc="upper right", fontsize=4.5, handlelength=1.1, labelspacing=0.18,
    )

    # ------------------------------------------------------------------
    # Panel (b): P0 Exact Coupled-Stream Replay (OS stream vs EB stream synergy)
    # ------------------------------------------------------------------
    ax = axes[1]
    style_axis(ax, "y")
    add_header(ax, "b", "Coupled-stream replay")
    rep_specs = [
        ("os_stream", "DF_EmpBernstein", "OS str.\nDF", PAL["df"]),
        ("os_stream", "Calibrated_EBLOO", "OS str.\nEB+LOO", PAL["nom"]),
        ("eb_stream", "DF_EmpBernstein", "EB str.\nDF", PAL["df_alt"]),
        ("eb_stream", "Calibrated_EBLOO", "EB str.\nEB+LOO", PAL["eb"]),
    ]
    rx = np.arange(len(rep_specs))
    gb1_r = [float(next(r for r in s1b if r["landscape"] == "gb1" and r["stream"] == st and r["rule"] == rl)["med_steps"]) / 1000.0 for st, rl, _, _ in rep_specs]
    trp_r = [float(next(r for r in s1b if r["landscape"] == "trpb" and r["stream"] == st and r["rule"] == rl)["med_steps"]) / 1000.0 for st, rl, _, _ in rep_specs]
    rcols = [c for _, _, _, c in rep_specs]
    ax.bar(rx - w / 2, gb1_r, width=w, color=rcols, edgecolor="white", linewidth=0.5, zorder=3)
    ax.bar(rx + w / 2, trp_r, width=w, color=rcols, alpha=0.48, edgecolor=rcols, linewidth=0.55, hatch="///", zorder=3)
    for i, (g, t) in enumerate(zip(gb1_r, trp_r)):
        if g >= 24.9 and t >= 24.9:
            ax.text(i, 25.6, "25k\n(0%)", ha="center", va="bottom", fontsize=4.3, fontweight="bold", color=rcols[i], linespacing=0.95)
        else:
            ax.text(i - w / 2 - 0.02, g + 0.45, f"{g:.1f}", ha="center", va="bottom", fontsize=4.3, fontweight="bold", color=rcols[i])
            ax.text(i + w / 2 + 0.03, t + 0.45, f"{t:.1f}", ha="center", va="bottom", fontsize=4.3, color=rcols[i])
    ax.axvline(1.5, color="#CBD5E1", linestyle="--", linewidth=0.7, zorder=1)
    ax.text(0.5, 33.0, "1.3–1.6×", ha="center", va="top", fontsize=4.8, fontweight="bold", color=PAL["nom"])
    ax.text(2.5, 33.0, "Synergy", ha="center", va="top", fontsize=4.8, fontweight="bold", color=PAL["eb"])
    ax.set_xticks(rx)
    ax.set_xticklabels([lbl for _, _, lbl, _ in rep_specs], fontsize=5.0)
    ax.set_ylabel("Med. stop time (k)")
    ax.set_ylim(0, 34.8)

    # ------------------------------------------------------------------
    # Panel (c): P1 36-Campaign 4-Domain Live Qwen3-0.6B Replication (cap=60)
    # ------------------------------------------------------------------
    ax = axes[2]
    style_axis(ax, "y")
    add_header(ax, "c", "Live Qwen3 (n=36)")
    dom_specs = [
        ("toolbench", "TB"),
        ("toolalpaca", "TA"),
        ("seal_tools", "ST"),
        ("webshop", "WS"),
        ("ALL", "ALL"),
    ]
    dx = np.arange(len(dom_specs))
    bw = 0.26
    m_live = [
        ("indep_os", "OS (0% DF)", PAL["df"]),
        ("eb_acq_df_stop", "EB+DF (0%)", PAL["df_strict"]),
        ("cd_joint_calibrated", "EB (100% Mod.)", PAL["eb"]),
    ]
    for k_i, (m_k, m_lbl, m_col) in enumerate(m_live):
        toks_k = []
        for sc_k, _ in dom_specs:
            row = next(r for r in s2 if r["scope"] == sc_k and r["method"] == m_k)
            toks_k.append(float(row["med_live_tokens"]) / 1000.0)
        pos = dx + (k_i - 1) * bw
        ax.bar(pos, toks_k, width=bw, color=m_col, edgecolor="white", linewidth=0.45, label=m_lbl, zorder=3)
        if m_k == "cd_joint_calibrated":
            for xi, tk in zip(pos, toks_k):
                ax.text(xi + 0.02, tk + 0.8, f"{tk:.0f}k", ha="center", va="bottom", fontsize=4.2, fontweight="bold", color=m_col)
    ax.set_xticks(dx)
    ax.set_xticklabels([lbl for _, lbl in dom_specs], fontsize=5.2)
    ax.set_ylabel("Med. fresh tokens (k)")
    ax.set_ylim(0, 52.0)
    ax.legend(frameon=False, loc="upper right", ncol=1, fontsize=4.4, handlelength=1.0, labelspacing=0.16)

    out_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_dir / "fig_v11_validity_ablation_and_live36.pdf", format="pdf", dpi=300)
    fig.savefig(out_dir / "fig_v11_validity_ablation_and_live36.png", format="png", dpi=260)
    plt.close(fig)
    print(f"Wrote v11 figure to {out_dir}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    plot_v11(args.data_dir, args.out_dir)


if __name__ == "__main__":
    main()
