#!/usr/bin/env python3
"""Publication figure generator for the v9 V33/V34 Adaptive Nuisance-KL Validation Suite.

Canvas geometry matches `iclr2027_conference.sty` (`\\textwidth = 5.50 in = 396 pt`),
colorblind-safe Okabe-Ito palette, vector PDF (`pdf.fonttype = 42`), zero-collision layout.
Generates 2 three-panel figures (PDF + 260-DPI QA PNG):
  1. `fig_v9_1_v34_vs_v33_and_heteroscedastic.pdf` (V9-1 Wall-clock vs K, V9-2 delta-sweep & nominal failure)
  2. `fig_v9_2_switching_and_validity_cost.pdf`    (V9-3 Safety/Reset/Behrens-Fisher, Switching/IUT, V9-4 Cost of Validity)
"""
from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import matplotlib as mpl
mpl.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DATA = ROOT / "results/bayesian_ucd_v1"
DEFAULT_OUT = ROOT / "results/bayesian_ucd_v1/figures"

PAL = {
    "v34": "#0B5394",       # Hero blue (V34-Full)
    "v34_g": "#0E8A74",     # Teal (V34-Gated / Hybrid QP)
    "v33_loc": "#2B8CBE",   # Sky (V33+Local / Warm B&B)
    "v33_sp": "#B8860B",    # Ochre (V33+Sparse)
    "v33": "#D55E00",       # Vermilion (V33-Full / Cold B&B)
    "known": "#7A3E9D",     # Violet (Oracle Known-sigma)
    "os": "#5C6B73",        # Slate (Indep Student-t OS)
    "err": "#B8332A",       # Crimson (Violation / Neg control)
    "ink": "#1F2933",
    "grid": "#E5E9F0",
}

mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
    "mathtext.fontset": "dejavusans",
    "font.size": 7.0,
    "axes.titlesize": 7.1,
    "axes.labelsize": 6.9,
    "xtick.labelsize": 6.3,
    "ytick.labelsize": 6.3,
    "legend.fontsize": 5.5,
    "axes.linewidth": 0.72,
    "xtick.major.width": 0.65,
    "ytick.major.width": 0.65,
    "xtick.major.size": 2.3,
    "ytick.major.size": 2.3,
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
    if grid_axis in ("x", "y", "both"):
        ax.grid(True, which="major", axis=grid_axis, color=PAL["grid"], linewidth=0.5, zorder=0)
    ax.set_axisbelow(True)


def add_header(ax: plt.Axes, tag: str, title: str, y_pad: float = 1.05) -> None:
    ax.text(
        0.0, y_pad, f"({tag}) {title}",
        transform=ax.transAxes, ha="left", va="bottom",
        fontsize=6.7, fontweight="bold", color=PAL["ink"],
    )


def _save_fig(fig: plt.Figure, out_dir: Path, stem: str) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_dir / f"{stem}.pdf", format="pdf", dpi=300)
    fig.savefig(out_dir / f"{stem}.png", format="png", dpi=260)
    plt.close(fig)


# ---------------------------------------------------------------------------
# Figure 1 (P0): V34 vs V33 Scaling Across K & Unknown-Variance Efficiency
# ---------------------------------------------------------------------------
def plot_fig1(data_dir: Path, out_dir: Path) -> None:
    s1 = load_csv(data_dir / "v9_exp1_v34_vs_v33_dag/v9_exp1_summary.csv")
    s2 = load_csv(data_dir / "v9_exp2_heteroscedastic_info/v9_exp2_summary.csv")
    s2c_p = data_dir / "v9_exp2_heteroscedastic_info/v9_exp2_partC_summary.csv"
    s2c = load_csv(s2c_p) if s2c_p.exists() else []

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.28))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.22, top=0.83, wspace=0.40)

    # Panel (a): Cold solver wall-clock time (ms) vs K in {4, 16, 64} (rank-2, unique, delta=0.01)
    ax = axes[0]
    style_axis(ax, "y")
    add_header(ax, "a", r"Solver cost vs. $K$ ($\delta=.01$)")
    ks = [4, 16, 64]
    x = np.arange(len(ks))
    w = 0.20
    meths = [
        ("v33_full", "V33 Full", PAL["v33"]),
        ("v33_sparse", "V33+Sp.", PAL["v33_sp"]),
        ("v33_local", "V33+Loc.", PAL["v33_loc"]),
        ("v34_full", "V34 Full", PAL["v34"]),
    ]
    sub1 = [r for r in s1 if r["track"] == "rank2_cubic" and r["regime"] == "unique" and abs(float(r["delta"]) - 0.01) < 1e-9]
    for idx, (m, lbl, col) in enumerate(meths):
        vals = [float(next(r for r in sub1 if int(r["K"]) == K and r["method"] == m)["med_total_ms"]) for K in ks]
        offs = (idx - 1.5) * w
        ax.bar(x + offs, vals, width=w * 0.92, color=col, edgecolor="white", linewidth=0.4, label=lbl, zorder=3)
    # Annotate 50.4x speedup at K=64
    v33_64 = float(next(r for r in sub1 if int(r["K"]) == 64 and r["method"] == "v33_full")["med_total_ms"])
    v34_64 = float(next(r for r in sub1 if int(r["K"]) == 64 and r["method"] == "v34_full")["med_total_ms"])
    sp_64 = v33_64 / max(1.0, v34_64)
    ax.text(2 + 1.5 * w, v34_64 * 1.25, f"{sp_64:.0f}×", ha="center", va="bottom", fontsize=5.8, fontweight="bold", color=PAL["v34"])
    ax.set_yscale("log")
    ax.set_ylim(50, 120000)
    ax.set_xticks(x)
    ax.set_xticklabels([f"K={K}" for K in ks])
    ax.set_ylabel("Median solver ms (log)")
    ax.legend(frameon=False, loc="upper left", ncol=2, columnspacing=0.5, handlelength=0.9, fontsize=5.0, borderaxespad=0.15)

    # Panel (b): Unknown-variance asymptotic efficiency vs log(1/delta) on ext_het_fav (sigma=(0.25, 4.0))
    ax = axes[1]
    style_axis(ax, "y")
    add_header(ax, "b", r"Heterosced. $\sigma=(.25,4)$")
    sub2 = [r for r in s2 if r["part"] == "B_delta_sweep" and r["profile"] == "ext_het_fav_025_400"]
    deltas = sorted({float(r["delta"]) for r in sub2}, reverse=True)
    xs = [math.log(1.0 / d) for d in deltas]
    curves = [
        ("v34_vanilla", "V34 (unk. σ)", PAL["v34"], "-", "o"),
        ("v34_gated", "V34 Gated", PAL["v34_g"], "--", "s"),
        ("known_sigma_tracker", "Known σ*", PAL["known"], "-.", "^"),
        ("indep_student_os", "Student OS", PAL["os"], ":", "D"),
    ]
    for m, lbl, col, ls, mk in curves:
        ys = [float(next(r for r in sub2 if abs(float(r["delta"]) - d) < 1e-12 and r["method"] == m)["mean_norm_ratio_unknown"]) for d in deltas]
        ax.plot(xs, ys, color=col, linestyle=ls, marker=mk, markersize=2.9, linewidth=1.2, label=lbl, zorder=4)
    ax.axhline(1.0, color=PAL["ink"], linestyle="--", linewidth=0.85, zorder=2)
    ax.text(xs[-1], 1.12, "Nuisance limit (1.0)", ha="right", va="bottom", fontsize=5.2, color=PAL["ink"])
    ax.set_yscale("log")
    ax.set_ylim(0.85, 2200)
    ax.set_xlabel(r"$\log(1/\delta)$")
    ax.set_ylabel(r"$\mathbb{E}[\tau_\delta]\,/\,(C_*^{-1}\log(1/\delta))$")
    ax.legend(frameon=False, loc="center", bbox_to_anchor=(0.48, 0.50), fontsize=5.1, handlelength=1.1, labelspacing=0.22)

    # Panel (c): Nominal sigma=1 failure vs V34 safety across sigma=(.25..4) (Symmetric Compass)
    ax = axes[2]
    style_axis(ax, "y")
    if s2c:
        add_header(ax, "c", r"$\sigma$-stress ($\delta=5\%$)")
        profs = [
            ("sig_025_025", ".25,.25"),
            ("sig_050_200", ".5,2"),
            ("sig_025_400", ".25,4"),
            ("sig_400_400", "4,4"),
        ]
        px = np.arange(len(profs))
        bw = 0.36
        err_nom = [100.0 * float(next(r for r in s2c if r["profile"] == p and r["method"] == "cd_joint_nom_sig1")["false_cert_rate"]) for p, _ in profs]
        err_v34 = [100.0 * float(next(r for r in s2c if r["profile"] == p and r["method"] == "v34_vanilla")["false_cert_rate"]) for p, _ in profs]
        ax.bar(px - bw / 2, err_nom, width=bw, color=PAL["err"], edgecolor="white", linewidth=0.5, label=r"CD-J ($\sigma\equiv 1$)", zorder=3)
        ax.bar(px + bw / 2, err_v34, width=bw, color=PAL["v34"], edgecolor="white", linewidth=0.5, label="V34 (unk. σ)", zorder=3)
        ax.axhline(5.0, color=PAL["ink"], linestyle="--", linewidth=0.85, zorder=4)
        ax.text(-0.42, 6.8, r"$\delta=5\%$", ha="left", va="bottom", fontsize=5.3, color=PAL["ink"])
        for i, v in enumerate(err_nom):
            if v > 0.1:
                ax.text(i - bw / 2, v + 1.5, f"{v:.0f}%", ha="center", va="bottom", fontsize=5.5, fontweight="bold", color=PAL["err"])
        ax.set_xticks(px)
        ax.set_xticklabels([lbl for _, lbl in profs], fontsize=5.8)
        ax.set_xlabel(r"True $(\sigma_1,\sigma_2)$")
        ax.set_ylabel("False cert. rate (%)")
        ax.set_ylim(0, max(52.0, max(err_nom) * 1.25))
        ax.legend(frameon=False, loc="upper left", fontsize=5.3, handlelength=0.95)

    _save_fig(fig, out_dir, "fig_v9_1_v34_vs_v33_and_heteroscedastic")


# ---------------------------------------------------------------------------
# Figure 2 (P1): Safety Controls, Switching/IUT, & Cost of Certified Validity
# ---------------------------------------------------------------------------
def plot_fig2(data_dir: Path, out_dir: Path) -> None:
    s3a = load_csv(data_dir / "v9_exp3_switching_and_safety/v9_exp3_partA_summary.csv")
    s3b = load_csv(data_dir / "v9_exp3_switching_and_safety/v9_exp3_partB_summary.csv")
    s4 = load_csv(data_dir / "v9_exp4_solver_cost_of_validity/v9_exp4_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.28))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.22, top=0.83, wspace=0.40)

    # Panel (a): Null-boundary wealth preservation audit (n=500, delta=5%)
    ax = axes[0]
    style_axis(ax, "y")
    add_header(ax, "a", "Wealth reset audit (n=500)")
    b1 = {r["method"]: r for r in s3b if r["part"] == "B1_null_reset"}
    b2 = {r["method"]: r for r in s3b if r["part"] == "B2_behrens_fisher"}
    keys = [
        ("v33_preserved_all", "V33\nPres.", PAL["v33_loc"]),
        ("v34_preserved_skip", "V34\nSkip", PAL["v34"]),
        ("neg_ctrl_reset_on_revisit", "Reset\n(Bad)", PAL["err"]),
    ]
    bx = np.arange(len(keys))
    vals = [100.0 * float(b1[k]["false_cert_rate"]) for k, _, _ in keys]
    cols = [c for _, _, c in keys]
    ax.bar(bx, vals, width=0.55, color=cols, edgecolor="white", linewidth=0.5, zorder=3)
    ax.axhline(5.0, color=PAL["ink"], linestyle="--", linewidth=0.85, zorder=4)
    ax.text(1.42, 6.2, r"$\delta=5\%$", ha="center", va="bottom", fontsize=5.3, color=PAL["ink"])
    for i, v in enumerate(vals):
        if v < 5.0:
            ax.text(i, v + 0.35, f"{v:.1f}%", ha="center", va="bottom", fontsize=4.9, fontweight="bold", color=cols[i])
        else:
            ax.text(i, v + 1.2, f"{v:.1f}%", ha="center", va="bottom", fontsize=5.8, fontweight="bold", color=cols[i])
    # Compact callout for B2 Behrens-Fisher max violation
    max_bf = float(b2["neg_ctrl_local_slsqp"]["max_viol_nats"])
    ax.text(
        0.04, 0.72,
        f"Bimodal null:\nLocal +{max_bf:.1f} nats\nCert. 0.0 nats",
        transform=ax.transAxes, fontsize=5.0, va="top", ha="left",
        bbox=dict(boxstyle="round,pad=0.25", facecolor="#F8FAFC", edgecolor="#CBD5E1", linewidth=0.6),
    )
    ax.set_xticks(bx)
    ax.set_xticklabels([l for _, l, _ in keys], fontsize=5.8)
    ax.set_ylabel("False cert. rate (%)")
    ax.set_ylim(0, 48.0)

    # Panel (b): Switching & IUT ablation (n=200/regime) - Null calls across 3 regimes
    ax = axes[1]
    style_axis(ax, "y")
    add_header(ax, "b", "Switching null calls (n=200)")
    regs = [
        ("natural_hard_init", "Hard\ninit"),
        ("adv_early_switch", "Adv.\nswitch"),
        ("tied_identical_opt", "Tied\nopt."),
    ]
    rx = np.arange(len(regs))
    bw = 0.25
    ms = [
        ("v33_all_action", "V33 All", PAL["v33"]),
        ("v34_bonferroni_j", "V34 Bonf.", PAL["v33_sp"]),
        ("v34_full", "V34 IUT", PAL["v34"]),
    ]
    for idx, (m, lbl, col) in enumerate(ms):
        ys = [float(next(r for r in s3a if r["sub_regime"] == rg and r["method"] == m)["med_null_calls"]) for rg, _ in regs]
        ax.bar(rx + (idx - 1) * bw, ys, width=bw * 0.92, color=col, edgecolor="white", linewidth=0.4, label=lbl, zorder=3)
    ax.set_yscale("log")
    ax.set_ylim(25, 3200)
    ax.set_xticks(rx)
    ax.set_xticklabels([l for _, l in regs], fontsize=5.8)
    ax.set_ylabel("Median null solves (log)")
    ax.legend(frameon=False, loc="upper right", fontsize=5.2, handlelength=0.9, borderaxespad=0.15)

    # Panel (c): Cost of Certified Validity across tolerance zeta (d=4, K=16)
    ax = axes[2]
    style_axis(ax, "both")
    add_header(ax, "c", r"Validity ($d{=}4,K{=}16$)")
    sub4 = [r for r in s4 if int(r["d"]) == 4 and int(r["K"]) == 16 and r["method"] != "indep_student_os"]
    zetas = sorted({float(r["zeta"]) for r in sub4}, reverse=True)
    # Also plot d=2 exact_cubic reference for scale!
    sub4_d2 = [r for r in s4 if int(r["d"]) == 2 and int(r["K"]) == 16 and r["method"] == "exact_cubic_v23"]
    s_curves = [
        ("cold_bnb_certified", "Cold B&B", PAL["v33"], "--", "o"),
        ("hybrid_qp_screened", "Hyb. QP", PAL["v33_loc"], "-.", "s"),
        ("hybrid_qp_gated", "Hyb. Gated", PAL["v34_g"], "-", "^"),
    ]
    for m, lbl, col, ls, mk in s_curves:
        pts = [(float(r["zeta"]), float(r["med_total_ms"])) for r in sorted([z for z in sub4 if z["method"] == m], key=lambda u: float(u["zeta"]), reverse=True)]
        if pts:
            ax.plot([p[0] for p in pts], [p[1] for p in pts], color=col, linestyle=ls, marker=mk, markersize=3.0, linewidth=1.2, label=lbl, zorder=4)
    if sub4_d2:
        pts2 = [(float(r["zeta"]), float(r["med_total_ms"])) for r in sorted(sub4_d2, key=lambda u: float(u["zeta"]), reverse=True)]
        ax.plot([p[0] for p in pts2], [p[1] for p in pts2], color=PAL["v34"], linestyle=":", marker="D", markersize=2.8, linewidth=1.2, label="Cubic (d=2)", zorder=4)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_ylim(100, 90000)
    ax.invert_xaxis()  # Loose (1.0 nat) -> Tight (1e-5 nat) left to right
    ax.set_xlabel(r"Log-enclosure tol. $\zeta$ (nats)")
    ax.set_ylabel("Median solver ms (log)")
    ax.legend(frameon=False, loc="center left", bbox_to_anchor=(0.0, 0.34), fontsize=5.0, handlelength=1.1, labelspacing=0.2)

    _save_fig(fig, out_dir, "fig_v9_2_switching_and_validity_cost")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    plot_fig1(args.data_dir, args.out_dir)
    plot_fig2(args.data_dir, args.out_dir)
    print(f"Wrote both v9 publication figures to {args.out_dir}")


if __name__ == "__main__":
    main()
