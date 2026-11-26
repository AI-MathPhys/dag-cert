#!/usr/bin/env python3
"""Publication figure generator for the v8 Unified Validation Suite (Experiments 1--6).

Canvas geometry matches `iclr2027_conference.sty` (`\\textwidth = 5.50 in = 396 pt`)
with colorblind-safe Okabe-Ito palette, vector PDF (`pdf.fonttype = 42`), and strict
zero-collision spacing. Generates 4 multi-panel figures (PDF + 300-DPI QA PNG):
  1. `fig_v8_1_calibrated_proteins_frontier.pdf` (Exp 1: Calibrated GB1/TmTrpB, 500-rep GP Cure, (xi, eps) Frontier)
  2. `fig_v8_2_info_tracking_efficiency.pdf`     (Exp 2: E[tau]/(T_* log(1/delta)) curve, M-scale tradeoff, Multi-Answer ties)
  3. `fig_v8_3_deconfounded_phase_proxy.pdf`     (Exp 3: Deconfounded omega x rho heatmap, 6-method factorial, Proxy align x cost)
  4. `fig_v8_4_compute_live_samegame.pdf`        (Exp 4/5/6: Conic schedules M<=4096, kappa break-even, Fresh Live Qwen3-0.6B)
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

PALETTE = {
    "cd_joint": "#0B5394",     # Hero blue (CD-Joint / calibrated)
    "hybrid": "#0E8A74",       # Teal (Smart Hybrid / safe fallback)
    "track": "#7A3E9D",        # Violet (Info-Tracking)
    "hyb_trk": "#2B8CBE",      # Sky blue (Hybrid CD->Tracking)
    "nominal": "#D55E00",      # Vermilion (Unadjusted nominal / GP-UCB)
    "robust": "#B8860B",       # Ochre (Pure robust xi)
    "post": "#B8332A",         # Crimson (Posterior stopping / failure)
    "os": "#5C6B73",           # Slate (Independent OS)
    "diag": "#CC79A7",         # Magenta (Diagonal Gaussian box)
    "ink": "#1F2933",
    "muted": "#6B7785",
    "grid": "#E5E9F0",
    "shade": "#EDF4FB",
}

mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
    "mathtext.fontset": "dejavusans",
    "font.size": 7.1,
    "axes.titlesize": 7.2,
    "axes.labelsize": 7.0,
    "xtick.labelsize": 6.5,
    "ytick.labelsize": 6.5,
    "legend.fontsize": 6.0,
    "axes.linewidth": 0.72,
    "xtick.major.width": 0.65,
    "ytick.major.width": 0.65,
    "xtick.major.size": 2.4,
    "ytick.major.size": 2.4,
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
    ax.spines["left"].set_color(PALETTE["ink"])
    ax.spines["bottom"].set_color(PALETTE["ink"])
    ax.tick_params(colors=PALETTE["ink"], pad=1.8)
    if grid_axis in ("x", "y", "both"):
        ax.grid(True, which="major", axis=grid_axis, color=PALETTE["grid"], linewidth=0.5, zorder=0)
    ax.set_axisbelow(True)


def add_header(ax: plt.Axes, tag: str, title: str, y_pad: float = 1.05) -> None:
    ax.text(
        0.0, y_pad, f"({tag}) {title}",
        transform=ax.transAxes,
        ha="left", va="bottom",
        fontsize=7.2, fontweight="bold", color=PALETTE["ink"],
    )


def _save_fig(fig: plt.Figure, out_dir: Path, stem: str) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_dir / f"{stem}.pdf", format="pdf", dpi=300)
    fig.savefig(out_dir / f"{stem}.png", format="png", dpi=260)
    plt.close(fig)


# ---------------------------------------------------------------------------
# Figure 1: Calibrated Protein Engineering, Misspecified GP Cure, & (xi, eps) Frontier
# ---------------------------------------------------------------------------
def plot_fig1(data_dir: Path, out_dir: Path) -> None:
    d1 = data_dir / "v8_exp1_calibrated_proteins"
    prot_rows = load_csv(d1 / "v8_exp1_protein_summary.csv")
    ctrl_rows = load_csv(d1 / "v8_exp1_controlled_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.28))
    fig.subplots_adjust(left=0.08, right=0.985, bottom=0.22, top=0.83, wspace=0.38)

    # Panel (a): Real GB1 (n=200) & TmTrpB (n=210) uncensored 25k medians
    ax = axes[0]
    style_axis(ax, "y")
    add_header(ax, "a", "Proteins (25k uncens.)")
    m_order = [
        ("indep_os", "Indep. OS", PALETTE["os"]),
        ("cd_joint_nominal", "Nom. GP", PALETTE["nominal"]),
        ("cd_joint_calibrated", "Calib. EB", PALETTE["cd_joint"]),
        ("cd_joint_hybrid_eb", "Hybrid EB", PALETTE["hybrid"]),
        ("cd_joint_robust_005", "Rob. .005", PALETTE["robust"]),
    ]
    x = np.arange(len(m_order))
    w = 0.37
    gb1_map = {r["method"]: float(r["med_steps_25k"]) for r in prot_rows if r["landscape"] == "gb1" and r["stratum"] == "all"}
    trp_map = {r["method"]: float(r["med_steps_25k"]) for r in prot_rows if r["landscape"] == "trpb" and r["stratum"] == "all"}
    g_vals = [gb1_map[m] / 1000.0 for m, _, _ in m_order]
    t_vals = [trp_map[m] / 1000.0 for m, _, _ in m_order]
    ax.bar(x - w / 2, g_vals, width=w, color=PALETTE["cd_joint"], edgecolor="white", linewidth=0.5, label="GB1 (200)", zorder=3)
    ax.bar(x + w / 2, t_vals, width=w, color=PALETTE["hybrid"], edgecolor="white", linewidth=0.5, alpha=0.88, label="TrpB (210)", zorder=3)
    ax.set_xticks(x)
    ax.set_xticklabels([lbl for _, lbl, _ in m_order], rotation=28, ha="right", fontsize=5.8)
    ax.set_ylabel("Median assays (×1k)")
    ax.set_ylim(0, 19.8)
    ax.legend(frameon=False, loc="upper right", handlelength=1.0, borderaxespad=0.2)
    ax.text(2.0, max(g_vals[2], t_vals[2]) + 0.45, "4.8×", ha="center", va="bottom", fontsize=5.6, fontweight="bold", color=PALETTE["cd_joint"])
    ax.text(3.0, max(g_vals[3], t_vals[3]) + 0.45, "5.0×", ha="center", va="bottom", fontsize=5.6, fontweight="bold", color=PALETTE["hybrid"])

    # Panel (b): 500-rep Misspecified GP Cure (false certificate rate %)
    ax = axes[1]
    style_axis(ax, "y")
    add_header(ax, "b", "Misspec. GP (n=500)")
    c3 = {r["method"]: r for r in ctrl_rows if r["study"] == "C3_misspec_gp_cure"}
    b_keys = [
        ("bayes_post_nominal", "Post.\nNom.", PALETTE["post"]),
        ("cd_joint_nominal", "Ellip.\nNom.", PALETTE["nominal"]),
        ("cd_joint_calibrated_eb", "Calib.\nEB+LOO", PALETTE["cd_joint"]),
    ]
    bx = np.arange(len(b_keys))
    err_pct = [100.0 * float(c3[k]["false_cert_rate"]) for k, _, _ in b_keys]
    cols = [c for _, _, c in b_keys]
    ax.bar(bx, err_pct, width=0.55, color=cols, edgecolor="white", linewidth=0.6, zorder=3)
    ax.axhline(5.0, color=PALETTE["ink"], linestyle="--", linewidth=0.85, zorder=4)
    ax.text(2.38, 6.2, r"$\delta=5\%$", ha="right", va="bottom", fontsize=5.9, color=PALETTE["ink"])
    for i, v in enumerate(err_pct):
        lbl = f"{v:.1f}%" if v > 0 else "0.0%"
        ax.text(i, v + 1.2, lbl, ha="center", va="bottom", fontsize=6.0, fontweight="bold", color=cols[i])
    ax.set_xticks(bx)
    ax.set_xticklabels([lbl for _, lbl, _ in b_keys], fontsize=6.0)
    ax.set_ylabel("False cert. rate (%)")
    ax.set_ylim(0, 46.0)

    # Panel (c): (xi, eps=0.030) Feasibility Frontier (500 reps/cell)
    ax = axes[2]
    style_axis(ax, "y")
    add_header(ax, "c", r"$(\xi,\varepsilon)$ frontier ($\varepsilon=.03$)")
    c4 = [r for r in ctrl_rows if r["study"] == "C4_xi_eps_frontier" and abs(float(r["eps"]) - 0.030) < 1e-6]
    xis = sorted({float(r["xi"]) for r in c4})
    xi_pos = np.arange(len(xis))
    # Shade infeasible bias-floor zone 2*xi >= 0.03 (xi >= 0.015, between idx 2 and 3)
    ax.axvspan(2.5, len(xis) - 0.4, color="#FCEAEA", alpha=0.65, zorder=1)
    ax.axvline(2.5, color=PALETTE["post"], linestyle=":", linewidth=0.9, zorder=2)
    ax.text(3.95, 1150, r"$2\xi\geq\varepsilon$", fontsize=5.8, color=PALETTE["post"], ha="center", va="center", fontweight="bold")

    series = [
        ("indep_os", "OS", PALETTE["os"], "--", "o"),
        ("cd_joint_robust", "Robust", PALETTE["robust"], "-.", "^"),
        ("cd_joint_hybrid", "Hybrid", PALETTE["hybrid"], "-", "s"),
        ("cd_joint_nominal", "Nominal", PALETTE["nominal"], ":", "D"),
    ]
    for meth, lbl, col, ls, mk in series:
        ys = []
        for xi_v in xis:
            row = next(r for r in c4 if abs(float(r["xi"]) - xi_v) < 1e-9 and r["method"] == meth)
            ys.append(float(row["med_steps"]))
        ax.plot(xi_pos, ys, color=col, linestyle=ls, marker=mk, markersize=3.2, linewidth=1.25, label=lbl, zorder=4)
    ax.set_yscale("log")
    ax.set_ylim(75, 42000)
    ax.set_xticks(xi_pos)
    ax.set_xticklabels([f"{x_v:g}" for x_v in xis], fontsize=5.8)
    ax.set_xlabel(r"Residual bound $\xi$")
    ax.set_ylabel("Median evals (log)")
    ax.legend(frameon=False, loc="upper left", ncol=2, columnspacing=0.6, handlelength=1.15, fontsize=5.4, borderaxespad=0.15)

    _save_fig(fig, out_dir, "fig_v8_1_calibrated_proteins_frontier")


# ---------------------------------------------------------------------------
# Figure 2: Information-Tracking Asymptotic Efficiency, Compute Tradeoff, & Ties
# ---------------------------------------------------------------------------
def plot_fig2(data_dir: Path, out_dir: Path) -> None:
    d2 = data_dir / "v8_exp2_info_tracking"
    pa = load_csv(d2 / "v8_exp2_partA_summary.csv")
    pb = load_csv(d2 / "v8_exp2_partB_summary.csv")
    pc = load_csv(d2 / "v8_exp2_partC_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.25))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.21, top=0.83, wspace=0.39)

    # Panel (a): E[tau] / (T_* log(1/delta)) vs log(1/delta) on proxy_M5_d3
    ax = axes[0]
    style_axis(ax, "y")
    add_header(ax, "a", "Info efficiency (proxy)")
    sub = [r for r in pa if r["instance"] == "proxy_M5_d3"]
    deltas = sorted({float(r["delta"]) for r in sub}, reverse=True)
    xs = [math.log(1.0 / d) for d in deltas]
    curves = [
        ("info_tracking", "Info-Track", PALETTE["track"], "-", "o"),
        ("hybrid_cd_tracking", "Hyb. Track", PALETTE["hyb_trk"], "--", "s"),
        ("cd_joint", "CD-Joint", PALETTE["cd_joint"], "-.", "^"),
        ("indep_gauss_os", "Indep. OS", PALETTE["os"], ":", "D"),
    ]
    for meth, lbl, col, ls, mk in curves:
        ys = [float(next(r for r in sub if abs(float(r["delta"]) - d) < 1e-12 and r["method"] == meth)["mean_norm_ratio"]) for d in deltas]
        ax.plot(xs, ys, color=col, linestyle=ls, marker=mk, markersize=3.2, linewidth=1.25, label=lbl, zorder=4)
    ax.axhline(1.0, color=PALETTE["ink"], linestyle="--", linewidth=0.85, zorder=2)
    ax.text(xs[-1], 1.13, "Lower bound (1.0)", ha="right", va="bottom", fontsize=5.6, color=PALETTE["ink"])
    ax.set_yscale("log")
    ax.set_ylim(0.85, 550)
    ax.set_xlabel(r"$\log(1/\delta)$")
    ax.set_ylabel(r"$\mathbb{E}[\tau_\delta]\,/\,(T_*^\varepsilon \log(1/\delta))$")
    ax.legend(frameon=False, loc="center right", bbox_to_anchor=(1.0, 0.54), fontsize=5.4, handlelength=1.15, labelspacing=0.25)

    # Panel (b): Medium Overlapping DAGs (M=128, 256, 512) compute vs samples
    ax = axes[1]
    style_axis(ax, "both")
    add_header(ax, "b", "Samples vs. compute")
    for m_val, mk in ((128, "o"), (256, "s"), (512, "^")):
        for meth, col in (("cd_joint", PALETTE["cd_joint"]), ("hybrid_cd_tracking", PALETTE["hyb_trk"]), ("info_tracking", PALETTE["track"])):
            row = next((r for r in pb if int(r["m_leaves"]) == m_val and r["method"] == meth), None)
            if row is None:
                continue
            ax.scatter(float(row["med_total_ms"]), float(row["med_steps"]), color=col, marker=mk, s=24, zorder=4)
            if meth == "cd_joint":
                ax.text(float(row["med_total_ms"]), float(row["med_steps"]) * 1.24, f"M={m_val}", fontsize=5.2, color=PALETTE["ink"], ha="center", va="bottom")
    # Connect same-method trajectories across M
    for meth, lbl, col in (("cd_joint", "CD-Joint", PALETTE["cd_joint"]), ("hybrid_cd_tracking", "Hyb. Track", PALETTE["hyb_trk"]), ("info_tracking", "Info-Track", PALETTE["track"])):
        pts = [(float(r["med_total_ms"]), float(r["med_steps"])) for r in sorted(pb, key=lambda z: int(z["m_leaves"])) if r["method"] == meth]
        ax.plot([p[0] for p in pts], [p[1] for p in pts], color=col, linewidth=1.0, alpha=0.8, label=lbl, zorder=3)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Median runtime (ms)")
    ax.set_ylabel("Median evals")
    ax.set_xlim(65, 9500)
    ax.set_ylim(200, 9000)
    ax.legend(frameon=False, loc="lower right", fontsize=5.5, handlelength=1.1)

    # Panel (c): Multi-Answer Tied Optima (n=48)
    ax = axes[2]
    style_axis(ax, "y")
    add_header(ax, "c", "Tied optima (n=48)")
    c_map = {r["method"]: r for r in pc}
    m_c = [
        ("info_tracking", "Info-\nTrack", PALETTE["track"]),
        ("hybrid_cd_tracking", "Hyb.\nTrack", PALETTE["hyb_trk"]),
        ("gp_ucb_joint", "GP-UCB\n+Joint", PALETTE["nominal"]),
        ("cd_joint", "CD-\nJoint", PALETTE["cd_joint"]),
        ("indep_gauss_os", "Indep.\nOS*", PALETTE["os"]),
    ]
    cx = np.arange(len(m_c))
    vals = [float(c_map[k]["med_steps"]) for k, _, _ in m_c]
    cols = [c for _, _, c in m_c]
    ax.bar(cx, vals, width=0.58, color=cols, edgecolor="white", linewidth=0.5, zorder=3)
    ax.set_yscale("log")
    ax.set_ylim(20, 6500)
    for i, v in enumerate(vals):
        lbl = ">3.5k" if v >= 3500 else f"{v:.0f}"
        ax.text(i, v * 1.12, lbl, ha="center", va="bottom", fontsize=5.7, fontweight="bold", color=cols[i])
    ax.set_xticks(cx)
    ax.set_xticklabels([lbl for _, lbl, _ in m_c], fontsize=5.7)
    ax.set_ylabel("Median evals (log)")

    _save_fig(fig, out_dir, "fig_v8_2_info_tracking_efficiency")


# ---------------------------------------------------------------------------
# Figure 3: Deconfounded Phase Diagram, 6-Method Factorial, & Proxy Sweep
# ---------------------------------------------------------------------------
def plot_fig3(data_dir: Path, out_dir: Path) -> None:
    d3 = data_dir / "v8_exp3_factorial_phase"
    ph = load_csv(d3 / "v8_exp3_phase_summary.csv")
    px = load_csv(d3 / "v8_exp3_proxy_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.25))
    fig.subplots_adjust(left=0.08, right=0.985, bottom=0.22, top=0.83, wspace=0.40)

    # Panel (a): Deconfounded omega x rho speedup heatmap at xi=0 (OS / CD-Joint)
    ax = axes[0]
    add_header(ax, "a", r"Deconfounded ($\xi=0$)")
    omegas = sorted({float(r["omega"]) for r in ph})
    rhos = sorted({float(r["rho"]) for r in ph})
    mat = np.zeros((len(omegas), len(rhos)))
    for i, om in enumerate(omegas):
        for j, rh in enumerate(rhos):
            r_os = next(r for r in ph if abs(float(r["omega"]) - om) < 1e-9 and abs(float(r["rho"]) - rh) < 1e-9 and abs(float(r["xi"])) < 1e-9 and r["method"] == "indep_box__os")
            r_cd = next(r for r in ph if abs(float(r["omega"]) - om) < 1e-9 and abs(float(r["rho"]) - rh) < 1e-9 and abs(float(r["xi"])) < 1e-9 and r["method"] == "corr_gp__cd")
            mat[i, j] = float(r_os["med_steps"]) / max(1.0, float(r_cd["med_steps"]))
    im = ax.imshow(mat, origin="lower", cmap="YlGnBu", vmin=3.4, vmax=6.0, aspect="auto")
    for i in range(len(omegas)):
        for j in range(len(rhos)):
            v = mat[i, j]
            tc = "white" if v >= 4.8 else PALETTE["ink"]
            ax.text(j, i, f"{v:.1f}×", ha="center", va="center", fontsize=6.0, fontweight="bold", color=tc)
    ax.set_xticks(range(len(rhos)))
    ax.set_xticklabels([f"{r:g}" for r in rhos], fontsize=6.0)
    ax.set_yticks(range(len(omegas)))
    ax.set_yticklabels([f"{o:g}" for o in omegas], fontsize=6.0)
    ax.set_xlabel(r"Correlation $\rho$")
    ax.set_ylabel(r"Overlap $\omega$")

    # Panel (b): 6-method factorial decomposition (xi=0 vs xi=0.045)
    ax = axes[1]
    style_axis(ax, "y")
    add_header(ax, "b", "Factorial decomp.")
    f_meths = [
        ("indep_box__os", "Indep\nOS"),
        ("corr_gp__ucb", "Corr\nUCB"),
        ("diag_gp__os", "Diag\nOS"),
        ("corr_gp__os", "Corr\nOS"),
        ("corr_gp__cd", "Corr\nCD"),
        ("robust_hybrid__cd", "Rob.\nHyb."),
    ]
    fx = np.arange(len(f_meths))
    w = 0.37
    v0, v45 = [], []
    for k, _ in f_meths:
        s0 = [float(r["med_steps"]) for r in ph if abs(float(r["xi"])) < 1e-9 and r["method"] == k]
        s45 = [float(r["med_steps"]) for r in ph if abs(float(r["xi"]) - 0.045) < 1e-9 and r["method"] == k]
        v0.append(float(np.median(s0)) / 1000.0)
        v45.append(float(np.median(s45)) / 1000.0)
    ax.bar(fx - w / 2, v0, width=w, color=PALETTE["cd_joint"], edgecolor="white", linewidth=0.5, label=r"$\xi=0$", zorder=3)
    ax.bar(fx + w / 2, v45, width=w, color=PALETTE["hybrid"], edgecolor="white", linewidth=0.5, alpha=0.85, label=r"$\xi=.045$", zorder=3)
    ax.set_xticks(fx)
    ax.set_xticklabels([lbl for _, lbl in f_meths], fontsize=5.6)
    ax.set_ylabel("Median evals (×1k)")
    ax.set_ylim(0, 8.8)
    ax.legend(frameon=False, loc="upper center", bbox_to_anchor=(0.48, 0.99), fontsize=5.6, handlelength=1.0)

    # Panel (c): Proxy alignment x relative cost speedup (Direct-Witness / CD-CostNorm)
    ax = axes[2]
    add_header(ax, "c", "Proxy cost speedup")
    aligns = sorted({float(r["align"]) for r in px})
    c_rats = sorted({float(r["cost_ratio"]) for r in px})
    pmat = np.zeros((len(aligns), len(c_rats)))
    for i, al in enumerate(aligns):
        for j, cr in enumerate(c_rats):
            r_dw = next(r for r in px if abs(float(r["align"]) - al) < 1e-9 and abs(float(r["cost_ratio"]) - cr) < 1e-9 and r["method"] == "direct_witness_joint")
            r_cn = next(r for r in px if abs(float(r["align"]) - al) < 1e-9 and abs(float(r["cost_ratio"]) - cr) < 1e-9 and r["method"] == "cd_joint_costnorm")
            pmat[i, j] = float(r_dw["med_cost"]) / max(0.1, float(r_cn["med_cost"]))
    ax.imshow(np.log10(np.maximum(1.0, pmat)), origin="lower", cmap="BuPu", vmin=0.0, vmax=1.8, aspect="auto")
    for i in range(len(aligns)):
        for j in range(len(c_rats)):
            v = pmat[i, j]
            tc = "white" if math.log10(max(1.0, v)) >= 0.95 else PALETTE["ink"]
            txt = f"{v:.0f}×" if v >= 10 else f"{v:.1f}×"
            ax.text(j, i, txt, ha="center", va="center", fontsize=5.6, fontweight="bold", color=tc)
    ax.set_xticks(range(len(c_rats)))
    ax.set_xticklabels([f"{c:g}" for c in c_rats], fontsize=5.8)
    ax.set_yticks(range(len(aligns)))
    ax.set_yticklabels([f"{a:.2f}" for a in aligns], fontsize=5.8)
    ax.set_xlabel(r"$c_{\mathrm{proxy}} / c_{\mathrm{target}}$")
    ax.set_ylabel(r"$\cos(\phi_{\mathrm{proxy}}, g^*)$")

    _save_fig(fig, out_dir, "fig_v8_3_deconfounded_phase_proxy")


# ---------------------------------------------------------------------------
# Figure 4: Conic Compute Schedules, kappa Break-Even, & Live Qwen3-0.6B
# ---------------------------------------------------------------------------
def plot_fig4(data_dir: Path, out_dir: Path) -> None:
    d4 = data_dir / "v8_exp4_compute_breakeven"
    d5 = data_dir / "v8_exp5_fresh_worfbench_live"
    c4a = load_csv(d4 / "v8_exp4_coupled_summary.csv")
    c4k = load_csv(d4 / "v8_exp4_kappa_frontier.csv")
    c5_live_p = d5 / "v8_exp5_live_summary.csv"
    c5_off_p = d5 / "v8_exp5_offline_summary.csv"

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.28))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.22, top=0.83, wspace=0.40)

    # Panel (a): Conic update latency across M=64..4096
    ax = axes[0]
    style_axis(ax, "y")
    add_header(ax, "a", "Conic update scaling")
    strats = [
        ("exact_every_step", "Exact", PALETTE["post"], ":", "x"),
        ("lazy_every_step", "Lazy", PALETTE["nominal"], "-.", "o"),
        ("periodic_conservative", "Periodic", PALETTE["robust"], "--", "^"),
        ("adaptive_tol_lazy", "Adapt. Tol", PALETTE["hyb_trk"], "-", "s"),
        ("hybrid_rect_joint", "Hyb. Rect", PALETTE["hybrid"], "-", "D"),
    ]
    for st, lbl, col, ls, mk in strats:
        sub = sorted([r for r in c4a if r["strategy"] == st], key=lambda z: int(z["m"]))
        if not sub:
            continue
        ms = [int(r["m"]) for r in sub]
        ys = [float(r["med_ms_per_update"]) for r in sub]
        ax.plot(ms, ys, color=col, linestyle=ls, marker=mk, markersize=3.0, linewidth=1.2, label=lbl, zorder=4)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_ylim(0.08, 3800)
    ax.set_xlabel("Terminals $M$")
    ax.set_ylabel("ms / update")
    ax.legend(frameon=False, loc="lower right", fontsize=5.1, handlelength=1.1, labelspacing=0.2, borderaxespad=0.15)

    # Panel (b): End-to-end wall-clock speedup vs kappa = oracle_step / eval_cost (M=256)
    ax = axes[1]
    style_axis(ax, "both")
    add_header(ax, "b", r"Break-even vs. $\kappa$ ($M=256$)")
    target_m = 256
    for meth, lbl, col, ls in (
        ("cd_hybrid_rect_joint", "Hyb. Rect", PALETTE["hybrid"], "-"),
        ("cd_periodic_conservative", "Periodic", PALETTE["robust"], "--"),
        ("cd_lazy_every_step", "Lazy", PALETTE["nominal"], "-."),
    ):
        sub = sorted([r for r in c4k if int(r["m"]) == target_m and r["method"] == meth], key=lambda z: float(z["kappa"]))
        if not sub:
            continue
        ks = [float(r["kappa"]) for r in sub]
        sp = [float(r["wall_speedup_vs_os"]) for r in sub]
        ax.plot(ks, sp, color=col, linestyle=ls, marker="o", markersize=2.8, linewidth=1.25, label=lbl, zorder=4)
    ax.axhline(1.0, color=PALETTE["ink"], linestyle="--", linewidth=0.85, zorder=2)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_ylim(0.24, 30.0)
    ax.set_xlabel(r"$\kappa = c_{\mathrm{oracle}} / c_{\mathrm{eval}}$")
    ax.set_ylabel("Wall speedup vs. OS")
    ax.text(2e-5, 1.25, "LLM / Wet-lab", fontsize=5.3, color=PALETTE["hybrid"], fontweight="bold")
    ax.text(35, 0.28, "Game\nrollout", fontsize=5.2, color=PALETTE["post"], ha="right", va="bottom")
    ax.legend(frameon=False, loc="lower left", fontsize=5.3, handlelength=1.1, labelspacing=0.22)

    # Panel (c): Live Qwen3-0.6B wall-clock seconds & tokens (or offline tokens if live absent)
    ax = axes[2]
    style_axis(ax, "y")
    if c5_live_p.exists():
        add_header(ax, "c", "Live Qwen3-0.6B")
        c5l = {r["method"]: r for r in load_csv(c5_live_p)}
        l_order = [
            ("indep_os", "Indep.\nOS", PALETTE["os"]),
            ("cd_joint_nominal", "Nom.\nCD", PALETTE["nominal"]),
            ("cd_joint_calibrated", "Calib.\nCD", PALETTE["cd_joint"]),
            ("cd_joint_hybrid", "Hybrid\nCD", PALETTE["hybrid"]),
        ]
        lx = np.arange(len(l_order))
        toks = [float(c5l[k]["med_live_tokens"]) / 1000.0 for k, _, _ in l_order if k in c5l]
        cols = [c for k, _, c in l_order if k in c5l]
        lbls = [l for k, l, _ in l_order if k in c5l]
        ax.bar(lx[: len(toks)], toks, width=0.56, color=cols, edgecolor="white", linewidth=0.5, zorder=3)
        for i, (k, _, col) in enumerate(l_order):
            if k not in c5l:
                continue
            v = float(c5l[k]["med_live_tokens"]) / 1000.0
            cr = float(c5l[k]["live_cert_rate"])
            tag = f"{v:.0f}k" + ("" if cr >= 0.99 else "*")
            ax.text(i, v + max(toks) * 0.03, tag, ha="center", va="bottom", fontsize=5.8, fontweight="bold", color=col)
        ax.set_xticks(lx[: len(toks)])
        ax.set_xticklabels(lbls, fontsize=5.8)
        ax.set_ylabel("Fresh live tokens (×1k)")
        ax.set_ylim(0, max(toks) * 1.24)
    elif c5_off_p.exists():
        add_header(ax, "c", "WorFBench (n=200)")
        c5o = {r["method"]: r for r in load_csv(c5_off_p)}
        o_order = [
            ("indep_os", "OS", PALETTE["os"]),
            ("cd_joint_nominal", "Nom.", PALETTE["nominal"]),
            ("cd_joint_calibrated", "Calib.", PALETTE["cd_joint"]),
            ("cd_joint_hybrid", "Hyb.", PALETTE["hybrid"]),
        ]
        ox = np.arange(len(o_order))
        toks = [float(c5o[k]["med_llm_tokens"]) / 1000.0 for k, _, _ in o_order]
        cols = [c for _, _, c in o_order]
        ax.bar(ox, toks, width=0.56, color=cols, edgecolor="white", linewidth=0.5, zorder=3)
        ax.set_xticks(ox)
        ax.set_xticklabels([l for _, l, _ in o_order], fontsize=6.0)
        ax.set_ylabel("Median tokens (×1k)")

    _save_fig(fig, out_dir, "fig_v8_4_compute_live_samegame")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()

    plot_fig1(args.data_dir, args.out_dir)
    plot_fig2(args.data_dir, args.out_dir)
    plot_fig3(args.data_dir, args.out_dir)
    plot_fig4(args.data_dir, args.out_dir)
    print(f"Wrote all 4 v8 publication figures to {args.out_dir}")


if __name__ == "__main__":
    main()
