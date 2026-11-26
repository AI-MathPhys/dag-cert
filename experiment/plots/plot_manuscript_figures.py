"""Generate every figure of the manuscript (Figures 1-15) as vector PDFs.

Each figure is drawn at its final printed size in the shared ICLR style
(`paper_style.py`) and reads only the SHA-256-verified archives under `results/`.
Nothing is hard-coded from the manuscript text: where the paper quotes a number,
the same number is recomputed here from the archive.

  Fig.  1  fig1_concept_overview.pdf (+ .png)       schematic (worked example of the introduction)
  Fig.  2  fig2_decision_relevant_information.pdf   exp1, e0
  Fig.  3  fig3_protein_stopping_regimes.pdf        v14, v13
  Fig.  4  fig4_acquisition_and_latency.pdf         v12
  Fig.  5  fig5_overlap_mechanism.pdf               exp1, exp8
  Fig.  6  fig6_correlation_factorial.pdf           v8_3
  Fig.  7  fig7_overlap_crossover.pdf               exp8
  Fig.  8  fig8_inside_witness.pdf                  exp11
  Fig.  9  supp_protein_credibility_audit.pdf       v14
  Fig. 10  supp_live_workflow_validation.pdf        v11_2
  Fig. 11  supp_information_tracking.pdf            v8_2
  Fig. 12  supp_protein_calibration_robustness.pdf  v8_1
  Fig. 13  supp_eprocess_safety_and_compute.pdf     v9_3, v9_1
  Fig. 14  supp_sparse_variance_tracking.pdf        v9_1, v9_2
  Fig. 15  supp_native_solver_and_workflows.pdf     v10_1, v10_2, v10_3
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
import warnings
from pathlib import Path

import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import Ellipse, FancyBboxPatch, Patch
from matplotlib.ticker import FixedLocator, FuncFormatter, NullFormatter, NullLocator

sys.path.insert(0, str(Path(__file__).resolve().parent))
import paper_style as ps  # noqa: E402
from paper_style import BAD, BLUE, INK, MUTED, ORANGE, OURS, PINK, REF  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
RES = ROOT / "results"
BAY = RES / "bayesian_ucd_v1"
V2 = RES / "uct_v2_extensions"
V4 = RES / "uct_v4_icml_baselines"
DEFAULT_OUT = ROOT / "figures"

RHOS = (0.0, 0.25, 0.5, 0.75, 0.88)


def _csv(path: Path) -> list[dict]:
    with path.open("r", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def _jsonl(path: Path) -> list[dict]:
    with path.open("r", encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def _k(v: float, nd: int = 1) -> str:
    return f"{v / 1000.0:.{nd}f}k"


def _plain_log(ax, axis: str, ticks, fmt="{:g}") -> None:
    a = ax.yaxis if axis == "y" else ax.xaxis
    a.set_major_locator(FixedLocator(list(ticks)))
    a.set_major_formatter(FuncFormatter(lambda v, _: fmt.format(v)))
    a.set_minor_locator(NullLocator())
    a.set_minor_formatter(NullFormatter())


# ----------------------------------------------------------------------------
# Shared data loaders
# ----------------------------------------------------------------------------
def _overlap_ratio() -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Exact/marginal stopping ratio at M=256 (Bernoulli): mean over the two gap settings, and their range."""
    rows = [r for r in _csv(V2 / "exp1_exact_regret/statistical_summary.csv")
            if r["M"] == "256" and r["reward_mode"] == "bernoulli"]
    per_gap = {}
    for r in rows:
        per_gap.setdefault(float(r["gap"]), {})[float(r["rho"])] = float(r["med_ratio"])
    mat = np.array([[per_gap[g][rho] for rho in RHOS] for g in sorted(per_gap)])
    return mat.mean(axis=0), mat.min(axis=0), mat.max(axis=0)


def _overlap_axis(ax) -> None:
    ax.set_xlim(-0.04, 0.92)
    ax.set_xticks(RHOS)
    ax.set_xticklabels(["0", ".25", ".5", ".75", ".88"])


# ----------------------------------------------------------------------------
# Main text
# ----------------------------------------------------------------------------
def fig1_concept_overview(out: Path) -> None:
    """Schematic of the paper: shared-outcome DAG -> joint root certificate -> contrast-directed acquisition.

    Panels (a)-(b) use the worked example of the introduction (intervals
    [.72,.80], [.40,.95], [.30,.55]); panel (c) is an illustrative geometry.
    """
    soft_green, soft_orange = "#DDF1EA", "#FBEBD0"
    fig, (ax, bx, cx) = ps.figure(3, height=1.36, gridspec_kw={"width_ratios": [1.0, 1.3, 1.12]})

    # (a) the search DAG ------------------------------------------------------
    ps.panel(ax, "a", "Search DAG, shared outcome")
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")
    pos = {"root": (0.5, 0.92), "a1": (0.26, 0.60), "a2": (0.74, 0.60),
           "z1": (0.12, 0.25), "zs": (0.50, 0.25), "z2": (0.88, 0.25)}
    ax.add_patch(FancyBboxPatch((0.0, 0.13), 0.64, 0.24, boxstyle="round,pad=0,rounding_size=0.05",
                                facecolor=soft_green, edgecolor="none", zorder=1))
    ax.add_patch(FancyBboxPatch((0.76, 0.13), 0.24, 0.24, boxstyle="round,pad=0,rounding_size=0.05",
                                facecolor=soft_orange, edgecolor="none", zorder=1))
    for s, t, col in (("root", "a1", OURS), ("root", "a2", ps.AXIS), ("a1", "z1", OURS), ("a1", "zs", OURS),
                      ("a2", "zs", ps.AXIS), ("a2", "z2", ps.AXIS)):
        ax.annotate("", xy=pos[t], xytext=pos[s], zorder=2,
                    arrowprops=dict(arrowstyle="-|>", color=col, linewidth=1.0, shrinkA=6.5, shrinkB=6.5, mutation_scale=6))
    for key, text, edge in (("root", "start", ps.AXIS), ("a1", "$a_1$", OURS), ("a2", "$a_2$", ps.AXIS),
                            ("z1", "$z_1$", OURS), ("zs", "$z_s$", OURS), ("z2", "$z_2$", ORANGE)):
        ax.text(*pos[key], text, ha="center", va="center", fontsize=7.5, zorder=4,
                bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor=edge, linewidth=0.9))
    ax.text(0.32, 0.055, "retained by $a_1$", ha="center", va="center", fontsize=6.8)
    ax.text(0.88, 0.055, "excluded", ha="center", va="center", fontsize=6.8)

    # (b) the certificate -----------------------------------------------------
    ps.panel(bx, "b", "Joint root certificate for $a_1$")
    rows = (("$z_1$", 2, 0.72, 0.80, OURS), ("$z_s$", 1, 0.40, 0.95, OURS), ("$z_2$", 0, 0.30, 0.55, ORANGE))
    for _, y, lo, hi, col in rows:
        bx.plot([lo, hi], [y, y], color=col, linewidth=4.2, solid_capstyle="round", zorder=3)
        bx.annotate(f"{lo:.2f}".lstrip("0"), (lo, y), xytext=(-5, 0), textcoords="offset points", ha="right",
                    va="center", fontsize=6.4)
        bx.annotate(f"{hi:.2f}".lstrip("0"), (hi, y), xytext=(5, 0), textcoords="offset points", ha="left",
                    va="center", fontsize=6.4)
    bx.plot([0.72, 0.72], [-0.45, 2.3], color=OURS, linestyle=(0, (1.5, 2)), linewidth=0.8, zorder=2)
    arrow = dict(arrowstyle="<|-|>", linewidth=0.9, shrinkA=0, shrinkB=0, mutation_scale=5)
    bx.annotate("", xy=(0.95, 1.5), xytext=(0.72, 1.5), arrowprops=dict(color=BAD, **arrow), zorder=4)
    bx.text(0.69, 1.5, "marginal gap .23", ha="right", va="center", fontsize=6.4, linespacing=1.0)
    bx.annotate("", xy=(0.72, 0.5), xytext=(0.55, 0.5), arrowprops=dict(color=OURS, **arrow), zorder=4)
    bx.text(0.52, 0.5, "certified: .55 < .72", ha="right", va="center", fontsize=6.4,
            linespacing=1.0)
    bx.set_xlim(0.0, 1.05)
    bx.set_ylim(-0.5, 2.45)
    bx.set_yticks([2, 1, 0])
    bx.set_yticklabels(["$z_1$", "$z_s$", "$z_2$"])
    bx.set_xticks([0.25, 0.5, 0.75, 1.0])
    bx.set_xticklabels([".25", ".5", ".75", "1"])
    bx.tick_params(axis="y", length=0)
    bx.spines["left"].set_visible(False)
    bx.set_xlabel("Plausible terminal value")

    # (c) the experiment ------------------------------------------------------
    ps.panel(cx, "c", "CD-Joint: shrink the contrast")
    off, centre = 0.12, np.array([1.0, 0.48])  # schematic axes: the boundary is mu_z = mu_y + eps
    xs = np.array([-0.5, 2.5])
    cx.fill_between(xs, xs - off, 3.0, color=soft_orange, linewidth=0, zorder=1)
    cx.plot(xs, xs - off, color=ORANGE, linewidth=0.9, zorder=2)
    cx.add_patch(Ellipse(centre, 1.0, 0.68, angle=45, facecolor="none", edgecolor=MUTED, linewidth=0.9,
                         linestyle=(0, (3, 2)), zorder=3))
    cx.add_patch(Ellipse(centre, 0.90, 0.19, angle=45, facecolor=OURS, alpha=0.30, edgecolor="none", zorder=4))
    cx.add_patch(Ellipse(centre, 0.90, 0.19, angle=45, facecolor="none", edgecolor=OURS, linewidth=1.1, zorder=5))
    g = np.array([-1.0, 1.0]) / np.sqrt(2.0)
    for sign in (1.0, -1.0):
        cx.annotate("", xy=centre + sign * 0.115 * g, xytext=centre + sign * 0.33 * g, zorder=6,
                    arrowprops=dict(arrowstyle="-|>", color=INK, linewidth=0.9, shrinkA=0, shrinkB=0, mutation_scale=6))
    cx.text(0.03, 0.97, "$a_1$ invalid", transform=cx.transAxes, ha="left", va="top", fontsize=6.6)
    cx.text(0.97, 0.97, "prior", transform=cx.transAxes, ha="right", va="top", fontsize=6.6, color=MUTED)
    cx.text(0.97, 0.03, "queries shrink\ncontrast $g$", transform=cx.transAxes, ha="right", va="bottom",
            fontsize=6.6, linespacing=1.0)
    cx.set_xlim(0.2, 1.7)
    cx.set_ylim(0.06, 0.92)
    cx.set_aspect("equal", adjustable="datalim")
    cx.set_xticks([])
    cx.set_yticks([])
    cx.set_xlabel("Best retained value $\\mu_y$")
    cx.set_ylabel("Excluded value $\\mu_z$")

    with warnings.catch_warnings():  # the equal-aspect panel adjusts its own data limits
        warnings.simplefilter("ignore", UserWarning)
        fig.savefig(out / "fig1_concept_overview.png", dpi=300)
        ps.save(fig, out / "fig1_concept_overview.pdf")


def fig2_decision_relevant_information(out: Path) -> None:
    mean, lo, hi = _overlap_ratio()
    toy = {r["method"]: r for r in _csv(BAY / "e0_and_toy/summary_toy.csv")}

    fig, (ax, bx) = ps.figure(2, height=1.3, gridspec_kw={"width_ratios": [1.0, 1.0]})

    ps.panel(ax, "a", "Shared support changes stopping")
    ax.grid(color=ps.GRID, linewidth=0.5)
    ax.fill_between(RHOS, lo, hi, color=OURS, alpha=0.18, linewidth=0)
    ax.plot(RHOS, mean, color=OURS, marker="o", markeredgecolor="white", markeredgewidth=0.7, zorder=4)
    ax.axhline(1.0, color=MUTED, linestyle=(0, (4, 2.5)), linewidth=0.7, zorder=2)
    ps.label(ax, 0.90, 1.0, "marginal stopping", dy=-2.5, ha="right", va="top", size=6.4, color=MUTED)
    ps.label(ax, RHOS[-1], mean[-1], f"{mean[-1]:.3f}", dy=5, dx=1, ha="center")
    _overlap_axis(ax)
    ax.set_ylim(0, 1.12)
    ax.set_yticks([0, 0.5, 1.0])
    ax.set_xlabel("Root-support overlap $\\rho$")
    ax.set_ylabel("Exact / marginal queries")

    ps.panel(bx, "b", "A low-value proxy is informative")
    ps.xgrid(bx)
    names = ("Direct witness", "Bayes-IDS", "CD-Joint")
    keys = ("direct_witness_joint", "bayes_ids_joint", "contrast_directed_joint")
    vals = [100.0 * float(toy[k]["mean_proxy_frac"]) for k in keys]
    ys = np.arange(3)[::-1]
    bx.barh(ys, vals, height=0.56, color=(REF, ORANGE, OURS), linewidth=0, zorder=3)
    for y, v in zip(ys, vals):
        bx.annotate(f"{v:.1f}%", (v, y), xytext=(3, 0), textcoords="offset points", va="center", fontsize=6.8)
    bx.set_yticks(ys)
    bx.set_yticklabels(names)
    bx.set_xlim(0, 100)
    bx.set_xticks([0, 25, 50, 75, 100])
    bx.set_xlabel("Queries assigned to the proxy (%)")
    ps.save(fig, out / "fig2_decision_relevant_information.pdf")


PROTEIN_METHODS = (("kg", "KG", BLUE), ("gp_os", "GP-OS", ORANGE), ("cd_joint", "CD-Joint", OURS))
LANDSCAPES = (("gb1", "GB1"), ("trpb", "TmTrpB"))


def _grouped(ax, groups: int, series: int, width: float = 0.8):
    w = width / series
    base = np.arange(groups)
    return [base + (i - (series - 1) / 2) * w for i in range(series)], w


def fig3_protein_stopping_regimes(out: Path) -> None:
    v14 = {(r["condition"], r["landscape"], r["method"]): r
           for r in _csv(BAY / "v14_protein_credible_ellipsoid/v14_protein_credible_summary.csv")}
    v13 = {(r["landscape"], r["method"]): r for r in _csv(BAY / "v13_protein_bed_vs_kg/v13_protein_summary.csv")
           if r["stopping_regime"] == "df_emp_bernstein" and abs(float(r["eps"]) - 0.015) < 1e-9}

    fig, (ax, bx, cx) = ps.figure(3, height=1.22)
    xs3, w3 = _grouped(ax, 2, 3, width=0.78)

    for axis, cond, scale, title, ylabel, fmt in (
        (ax, "B_chi95", 1000.0, "Joint credible ellipsoid", "Mean assays ($\\times 10^3$)", "{:.1f}"),
        (bx, "E_postrisk", 1.0, "Direct posterior-risk stop", "Mean assays", "{:.0f}"),
    ):
        ps.ygrid(axis)
        for (m, _, col), x in zip(PROTEIN_METHODS, xs3):
            rows = [v14[(cond, land, m)] for land, _ in LANDSCAPES]
            vals = [float(r["restricted_mean"]) / scale for r in rows]
            ps.bars(axis, x, vals, col, width=w3 * 0.9,
                    lo=[float(r["rm_ci95_lo"]) / scale for r in rows],
                    hi=[float(r["rm_ci95_hi"]) / scale for r in rows],
                    labels=[fmt.format(v) for v in vals], label_size=6.0)
        axis.set_xticks(range(2))
        axis.set_xticklabels([n for _, n in LANDSCAPES])
        axis.set_ylabel(ylabel)
    ps.panel(ax, "a", "Joint credible ellipsoid")
    ps.panel(bx, "b", "Direct posterior-risk stop")
    ax.set_ylim(0, 29.5)
    ax.set_yticks([0, 10, 20])
    bx.set_ylim(0, 290)
    bx.set_yticks([0, 100, 200])

    ps.panel(cx, "c", "Distribution-free stop")
    ps.ygrid(cx)
    df_methods = PROTEIN_METHODS + (("gp_root_info_df", "GP-Root-Info (DF-aware)", PINK), ("df_os", "DF-OS", REF))
    xs5, w5 = _grouped(cx, 2, 5, width=0.86)
    for (m, _, col), x in zip(df_methods, xs5):
        vals = [100.0 * float(v13[(land, m)]["cert_rate"]) for land, _ in LANDSCAPES]
        ps.bars(cx, x, vals, col, width=w5 * 0.9, labels=["" if v > 99.5 else f"{v:.0f}" for v in vals], label_size=6.0)
    cx.set_xticks(range(2))
    cx.set_xticklabels([n for _, n in LANDSCAPES])
    cx.set_ylim(0, 165)
    cx.set_yticks([0, 50, 100])
    cx.set_ylabel("Certified by 25k (%)")

    # Legends sit inside the panels: this figure shares a main-text page with Table 4.
    kw = dict(handlelength=0.9, handleheight=0.7, labelspacing=0.2, borderaxespad=0.0, fontsize=6.6)
    ax.legend([Patch(color=c) for _, _, c in PROTEIN_METHODS], [n for _, n, _ in PROTEIN_METHODS],
              loc="upper right", **kw)
    cx.legend([Patch(color=c) for _, _, c in df_methods[3:]], ["GP-Root-Info (DF-aware)", "DF-OS"],
              loc="upper center", **kw)
    ps.save(fig, out / "fig3_protein_stopping_regimes.pdf")


# ----------------------------------------------------------------------------
# Appendix G
# ----------------------------------------------------------------------------
def fig4_acquisition_and_latency(out: Path) -> None:
    rows = {(r["condition"], r["policy"]): r for r in _csv(BAY / "v12_bed_vs_bo/v12_main64_summary.csv")
            if r["beta_mode"] == "posterior_credible"}
    conds = (("A_indep", "A", "(0, 0)"), ("B_struct", "B", "(.75, 0)"), ("C_stat", "C", "(0, .9)"), ("D_both", "D", "(.75, .9)"))
    pols = (("kg", "Correlated KG", BLUE), ("cd_joint", "CD-Joint", OURS))

    fig, (ax, bx) = ps.figure(2, height=1.95)
    ps.panel(ax, "a", "Evaluations to certification")
    ps.ygrid(ax)
    xs, w = _grouped(ax, 4, 2, width=0.68)
    for (p, name, col), x in zip(pols, xs):
        rs = [rows[(c, p)] for c, _, _ in conds]
        vals = [float(r["restricted_mean"]) / 1000.0 for r in rs]
        ps.bars(ax, x, vals, col, width=w * 0.9, legend=name,
                lo=[float(r["rm_ci95_lo"]) / 1000.0 for r in rs], hi=[float(r["rm_ci95_hi"]) / 1000.0 for r in rs],
                labels=[f"{v:.1f}" for v in vals], label_size=6.2)
    ax.set_xticks(range(4))
    ax.set_xticklabels([f"{a}\n{b}" for _, a, b in conds])
    ax.set_xlabel("Condition (overlap $\\omega$, correlation $\\rho$)")
    ax.set_ylabel("Restricted mean evaluations ($\\times 10^3$)")
    ax.set_ylim(0, 8.4)
    ax.set_yticks([0, 2, 4, 6, 8])
    ax.legend(loc="upper right", ncol=2)

    ps.panel(bx, "b", "Evaluation-latency crossover")
    bx.grid(color=ps.GRID, linewidth=0.5)
    c = np.linspace(0, 10, 101)
    model = {}
    for p, name, col in pols:
        r = rows[("ALL", p)]
        tau, acq = float(r["restricted_mean"]), float(r["med_acq_ms_per_step"])
        model[p] = (tau / 1000.0, tau * acq / 1000.0)  # seconds per ms of latency, fixed seconds
        slope, icpt = model[p]
        bx.plot(c, icpt + slope * c, color=col, zorder=4, label=name)
    cross = (model["cd_joint"][1] - model["kg"][1]) / (model["kg"][0] - model["cd_joint"][0])
    ycross = model["kg"][1] + model["kg"][0] * cross
    bx.plot([cross, cross], [0, ycross], color=MUTED, linestyle=(0, (1.5, 2)), linewidth=0.8, zorder=3)
    bx.plot([cross], [ycross], marker="o", color=INK, markersize=3.6, zorder=5)
    ps.label(bx, cross, ycross, f"crossover at {cross:.1f} ms", dx=5, dy=-11, ha="left", va="top", size=6.6)
    bx.set_xlim(0, 10)
    bx.set_ylim(0, 56)
    bx.set_yticks([0, 20, 40])
    bx.set_xlabel("Evaluation latency (ms)")
    bx.set_ylabel("Modelled total time (s)")
    bx.legend(loc="upper left", handlelength=1.8)
    ps.save(fig, out / "fig4_acquisition_and_latency.pdf")


def fig5_overlap_mechanism(out: Path) -> None:
    mean, lo, hi = _overlap_ratio()
    er = {float(r["rho"]): r for r in _csv(V4 / "icml_figures_data/fig2a_overlap_sweep.csv")
          if r["suite"] == "overlap_256_box" and r["method"] == "exact_dag_lucb"}

    fig, (ax, bx) = ps.figure(2, height=1.85)
    ps.panel(ax, "a", "Passive stopping ratio")
    ax.grid(color=ps.GRID, linewidth=0.5)
    ax.fill_between(RHOS, lo, hi, color=OURS, alpha=0.18, linewidth=0)
    ax.plot(RHOS, mean, color=OURS, marker="o", markeredgecolor="white", markeredgewidth=0.7, zorder=4)
    for rho, v in zip(RHOS[2:], mean[2:]):
        ps.label(ax, rho, v, f"{v:.3f}", dy=4, dx=3, ha="left", size=6.4)
    _overlap_axis(ax)
    ax.set_xlim(-0.04, 1.0)
    ax.set_ylim(0, 1.12)
    ax.set_yticks([0, 0.25, 0.5, 0.75, 1.0])
    ax.set_xlabel("Support overlap $\\rho$")
    ax.set_ylabel("Exact / marginal observations")

    ps.panel(bx, "b", "Active exact-regret sampler (ER)")
    bx.grid(color=ps.GRID, linewidth=0.5)
    med = np.array([float(er[r]["steps_med"]) for r in RHOS]) / 1000.0
    q25 = np.array([float(er[r]["steps_q25"]) for r in RHOS]) / 1000.0
    q75 = np.array([float(er[r]["steps_q75"]) for r in RHOS]) / 1000.0
    bx.errorbar(RHOS, med, yerr=[med - q25, q75 - med], color=BLUE, marker="s", markeredgecolor="white",
                markeredgewidth=0.7, ecolor=INK, elinewidth=0.7, capsize=1.6, zorder=4)
    for rho, v in zip(RHOS, med):
        ps.label(bx, rho, v, f"{v:.1f}", dy=4, dx=3, ha="left", size=6.4)
    _overlap_axis(bx)
    bx.set_xlim(-0.04, 1.0)
    bx.set_ylim(0, 14)
    bx.set_yticks([0, 4, 8, 12])
    bx.set_xlabel("Support overlap $\\rho$")
    bx.set_ylabel("ER observations ($\\times 10^3$)")
    ps.save(fig, out / "fig5_overlap_mechanism.pdf")


def fig6_correlation_factorial(out: Path) -> None:
    runs = [r for r in _jsonl(BAY / "v8_exp3_factorial_phase/v8_exp3_phase_runs.jsonl") if abs(r["xi"]) < 1e-12]
    methods = (
        ("indep_box__os", "Empirical-Bernstein OS", REF),
        ("diag_gp__os", "Diagonal Gaussian OS", ORANGE),
        ("corr_gp__os", "Correlated GP OS", BLUE),
        ("corr_gp__cd", "CD-Joint", OURS),
    )
    fig, (ax,) = ps.figure(1, height=1.55, width=4.3)
    ps.xgrid(ax)
    ys = np.arange(len(methods))[::-1]
    for y, (m, _, col) in zip(ys, methods):
        steps = np.array([r["capped_steps"] for r in runs if r["method"] == m], dtype=float)
        med, q25, q75 = np.median(steps), np.percentile(steps, 25), np.percentile(steps, 75)
        ax.barh(y, med, height=0.56, color=col, linewidth=0, zorder=3)
        ax.plot([q25, q75], [y, y], color=INK, linewidth=0.7, zorder=4)
        ax.plot([q25, q75], [y, y], linestyle="none", marker="|", color=INK, markersize=3.2, markeredgewidth=0.7, zorder=4)
        ax.annotate(f"{med:,.0f}", (max(med, q75), y), xytext=(4, 0), textcoords="offset points", va="center", fontsize=6.8)
    ax.set_yticks(ys)
    ax.set_yticklabels([n for _, n, _ in methods])
    ax.set_xlim(0, 9000)
    ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:,.0f}"))
    ax.set_xlabel("Median evaluations to certification (lower is better)")
    ps.save(fig, out / "fig6_correlation_factorial.pdf")


def fig7_overlap_crossover(out: Path) -> None:
    rows = {float(r["rho"]): r for r in _csv(V4 / "exp8_external_baselines/summary_2x2_overlap256.csv")}
    cap = 1000.0
    er = [float(rows[r]["exact_dag_lucb_ms"]) for r in RHOS]
    lucb = [float(rows[r]["lucb_micro_marg_ms"]) for r in RHOS]
    done = [v < cap for v in lucb]

    fig, (ax,) = ps.figure(1, height=1.9, width=3.7)
    ax.grid(color=ps.GRID, linewidth=0.5)
    ax.set_yscale("log")
    ax.axhline(cap, color=MUTED, linestyle=(0, (4, 2.5)), linewidth=0.7, zorder=2)
    ps.label(ax, 0.0, cap, "1 s cap", dy=2.5, ha="left", size=6.4, color=MUTED)
    n_done = sum(done)
    ax.plot(RHOS[:n_done + 1], [min(v, cap) for v in lucb[:n_done + 1]], color=ORANGE, zorder=3)
    ax.plot(RHOS[n_done:], [cap] * (len(RHOS) - n_done), color=ORANGE, linestyle=(0, (1.5, 2)), zorder=3)
    ax.plot([r for r, d in zip(RHOS, done) if d], [v for v, d in zip(lucb, done) if d], linestyle="none",
            marker="s", color=ORANGE, markeredgecolor="white", markeredgewidth=0.7, zorder=4)
    ax.plot([r for r, d in zip(RHOS, done) if not d], [cap] * (len(RHOS) - n_done), linestyle="none", marker="^",
            markerfacecolor="white", markeredgecolor=ORANGE, markeredgewidth=1.0, markersize=5, zorder=4)
    ax.plot(RHOS, er, color=OURS, marker="o", markeredgecolor="white", markeredgewidth=0.7, zorder=5)
    _overlap_axis(ax)
    ax.set_ylim(40, 1700)
    _plain_log(ax, "y", (50, 100, 300, 1000))
    ax.set_xlabel("Support overlap $\\rho$")
    ax.set_ylabel("Cold time to certification (ms)")
    handles = [
        Line2D([], [], color=OURS, marker="o", markeredgecolor="white", markeredgewidth=0.7),
        Line2D([], [], color=ORANGE, marker="s", markeredgecolor="white", markeredgewidth=0.7),
        Line2D([], [], linestyle="none", marker="^", markerfacecolor="white", markeredgecolor=ORANGE, markeredgewidth=1.0),
    ]
    ax.legend(handles, ["Exact-Regret-DAG-LUCB", "LUCB-micro (marginal)", "LUCB-micro, capped"],
              loc="lower left", borderaxespad=0.6, handlelength=2.0)
    ps.save(fig, out / "fig7_overlap_crossover.pdf")


def fig8_inside_witness(out: Path) -> None:
    fam = {(r["family"], r["method"]): 100.0 * float(r["cert_rate"])
           for r in _csv(V4 / "exp11_hybrid_and_os/summary_hybrid_by_family.csv")}
    star = {r["method"]: 100.0 * float(r["cert_rate"])
            for r in _csv(V4 / "exp11_hybrid_and_os/summary_star_eps.csv") if abs(float(r["eps"])) < 1e-12}
    tasks = (("decoy_trap_16", "Decoy-16"), ("window_64", "Window-64"), ("hetero_support_256", "Hetero-256"), (None, "Tied-Star"))
    methods = (("ucb", "UCB-inside", BLUE), ("hybrid", "Safeguarded-LCB", OURS), ("opt_sep", "Optimistic-Separation", ORANGE))

    fig, (ax,) = ps.figure(1, height=1.8, width=4.3)
    ps.ygrid(ax)
    xs, w = _grouped(ax, len(tasks), len(methods), width=0.72)
    for (m, name, col), x in zip(methods, xs):
        vals = [star[m] if f is None else fam[(f, m)] for f, _ in tasks]
        ps.bars(ax, x, vals, col, width=w * 0.9, legend=name, labels=[f"{v:.0f}" for v in vals], label_size=6.2)
    ax.set_xticks(range(len(tasks)))
    ax.set_xticklabels([n for _, n in tasks])
    ax.set_ylim(0, 114)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_ylabel("Certified trials (%)")
    h, l = ax.get_legend_handles_labels()
    ps.legend_below(fig, h, l)
    ps.save(fig, out / "fig8_inside_witness.pdf")


# ----------------------------------------------------------------------------
# Appendices H-L (external figures referenced as supp_*.pdf)
# ----------------------------------------------------------------------------
def fig9_protein_credibility_audit(out: Path) -> None:
    lk = {(r["landscape"], r["method"]): r
          for r in _csv(BAY / "v14_protein_credible_ellipsoid/v14_protein_credible_summary.csv") if r["condition"] == "B_chi95"}
    names = [n for _, n, _ in PROTEIN_METHODS]
    cols = [c for _, _, c in PROTEIN_METHODS]

    fig, axes = ps.figure(3, height=1.95)
    xs = np.arange(3)
    for ax, letter, (land, lname), n, ymax in zip(axes[:2], "ab", LANDSCAPES, (200, 210), (31.0, 12.6)):
        rs = [lk[(land, m)] for m, _, _ in PROTEIN_METHODS]
        vals = [float(r["restricted_mean"]) / 1000.0 for r in rs]
        ps.panel(ax, letter, f"{lname} ($n={n}$)")
        ps.ygrid(ax)
        ps.bars(ax, xs, vals, cols, width=0.58,
                lo=[float(r["rm_ci95_lo"]) / 1000.0 for r in rs], hi=[float(r["rm_ci95_hi"]) / 1000.0 for r in rs],
                labels=[f"{v:.1f}k\n{100 * float(r['cert_rate']):.0f}% cert." for v, r in zip(vals, rs)], label_size=6.2)
        ax.set_xticks(xs)
        ax.set_xticklabels(names)
        ax.set_ylim(0, ymax)
        ax.set_ylabel("Restricted mean assays ($\\times 10^3$)")

    cx = axes[2]
    ps.panel(cx, "c", "Simultaneous coverage")
    ps.ygrid(cx)
    gx, w = _grouped(cx, 2, 3, width=0.78)
    for (m, name, col), x in zip(PROTEIN_METHODS, gx):
        cov = [100.0 * float(lk[(land, m)]["joint_contrast_cov"]) for land, _ in LANDSCAPES]
        ps.bars(cx, x, cov, col, width=w * 0.9, labels=[f"{v:.0f}" for v in cov], label_size=6.2, legend=name)
    ps.reference(cx, 95.0, "95% nominal")
    cx.set_xticks(range(2))
    cx.set_xticklabels([n for _, n in LANDSCAPES])
    cx.set_ylim(0, 112)
    cx.set_yticks([0, 25, 50, 75, 100])
    cx.set_ylabel("Joint contrast coverage (%)")
    ps.save(fig, out / "supp_protein_credibility_audit.pdf")


def fig10_live_workflow_validation(out: Path) -> None:
    lk = {r["method"]: r for r in _csv(BAY / "v11_exp2_live_worfbench_36campaigns/v11_exp2_live_summary.csv")
          if r["scope_kind"] == "ALL"}
    methods = ("indep_os", "eb_acq_df_stop", "cd_joint_calibrated")
    ticks = ("DF-OS", "GP+DF", "EB+LOO")
    cols = (REF, ORANGE, OURS)
    xs = np.arange(3)
    rs = [lk[m] for m in methods]

    fig, (ax, bx, cx) = ps.figure(3, height=1.85)
    for a in (ax, bx, cx):
        ps.ygrid(a)
        a.set_xticks(xs)
        a.set_xticklabels(ticks)

    ps.panel(ax, "a", "Certified by 60 evaluations")
    vals = [100.0 * float(r["cert_rate"]) for r in rs]
    ps.bars(ax, xs, vals, cols, width=0.58,
            lo=[100.0 * float(r["cert_cp95_lo"]) for r in rs], hi=[100.0 * float(r["cert_cp95_hi"]) for r in rs],
            labels=[f"{int(r['certified_count'])}/{int(r['campaigns'])}" for r in rs])
    ax.set_ylim(0, 118)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_ylabel("Campaigns certified (%)")

    ps.panel(bx, "b", "Fresh inference tokens")
    vals = [float(r["med_live_tokens"]) / 1000.0 for r in rs]
    ps.bars(bx, xs, vals, cols, width=0.58,
            lo=[float(r["q25_live_tokens"]) / 1000.0 for r in rs], hi=[float(r["q75_live_tokens"]) / 1000.0 for r in rs],
            labels=[f"{v:.1f}k" for v in vals])
    bx.set_ylim(0, 44)
    bx.set_ylabel("Median tokens ($\\times 10^3$)")

    ps.panel(cx, "c", "Held-out task quality")
    vals = [float(r["mean_unseen_test_f1"]) for r in rs]
    ps.bars(cx, xs, vals, cols, width=0.58, labels=[f"{v:.3f}" for v in vals])
    cx.set_ylim(0, 0.56)
    cx.set_ylabel("Mean held-out $F_1$")
    ps.save(fig, out / "supp_live_workflow_validation.pdf")


def fig11_information_tracking(out: Path) -> None:
    rows_a = [r for r in _csv(BAY / "v8_exp2_info_tracking/v8_exp2_partA_summary.csv") if r["instance"] == "proxy_M5_d3"]
    rows_b = _csv(BAY / "v8_exp2_info_tracking/v8_exp2_partB_summary.csv")
    rows_c = {r["method"]: r for r in _csv(BAY / "v8_exp2_info_tracking/v8_exp2_partC_summary.csv")}
    style = {
        "indep_gauss_os": ("Independent OS", REF, "D"),
        "cd_joint": ("CD-Joint", OURS, "o"),
        "hybrid_cd_tracking": ("Hybrid CD$\\rightarrow$Track", PINK, "s"),
        "info_tracking": ("Info-Tracking", BLUE, "^"),
    }

    fig, (ax, bx, cx) = ps.figure(3, height=1.95)

    ps.panel(ax, "a", "Proxy DAG rate ratio")
    ax.grid(color=ps.GRID, linewidth=0.5)
    deltas = sorted({float(r["delta"]) for r in rows_a}, reverse=True)
    lka = {(float(r["delta"]), r["method"]): float(r["med_norm_ratio"]) for r in rows_a}
    x = np.arange(len(deltas))
    for m in ("cd_joint", "hybrid_cd_tracking", "info_tracking"):
        _, col, mk = style[m]
        ax.plot(x, [lka[(d, m)] for d in deltas], color=col, marker=mk, markeredgecolor="white", markeredgewidth=0.7, zorder=4)
    ax.axhline(1.0, color=MUTED, linestyle=(0, (4, 2.5)), linewidth=0.7, zorder=2)
    ps.label(ax, x[-1], 1.0, "lower bound", dy=2, ha="right", size=6.4, color=MUTED)
    ax.set_xticks(x)
    ax.set_xticklabels([f"{d:g}".replace("0.", ".") if d >= 0.001 else "$10^{-4}$" for d in deltas])
    ax.set_ylim(0, 13)
    ax.set_yticks([0, 4, 8, 12])
    ax.set_xlabel("Confidence level $\\delta$")
    ax.set_ylabel("Median $\\tau\\,/\\,(T^{\\varepsilon}_{*}\\log(1/\\delta))$")

    ps.panel(bx, "b", "Medium Gaussian DAGs")
    ps.ygrid(bx)
    scales = sorted({int(r["m_leaves"]) for r in rows_b})
    lkb = {(int(r["m_leaves"]), r["method"]): float(r["med_steps"]) / 1000.0 for r in rows_b}
    gx, w = _grouped(bx, len(scales), 3, width=0.78)
    for m, x in zip(("indep_gauss_os", "cd_joint", "info_tracking"), gx):
        _, col, _ = style[m]
        vals = [lkb[(s, m)] for s in scales]
        ps.bars(bx, x, vals, col, width=w * 0.9)
    bx.set_xticks(range(len(scales)))
    bx.set_xticklabels([f"$M={s}$" for s in scales])
    bx.set_ylim(0, 5.6)
    bx.set_ylabel("Median evaluations ($\\times 10^3$)")

    ps.panel(cx, "c", "Multiple correct answers")
    ps.xgrid(cx)
    cx.grid(axis="x", which="major", color=ps.GRID, linewidth=0.5)
    order = ("indep_gauss_os", "cd_joint", "hybrid_cd_tracking", "info_tracking")
    ys = np.arange(len(order))[::-1]
    cx.set_xscale("log")
    for y, m in zip(ys, order):
        _, col, mk = style[m]
        r = rows_c[m]
        med, q25, q75 = float(r["med_steps"]), float(r["q25_steps"]), float(r["q75_steps"])
        capped = float(r["cert_rate"]) == 0.0
        cx.plot([q25, q75], [y, y], color=col, linewidth=1.6, solid_capstyle="round", zorder=3)
        cx.plot([med], [y], marker=mk, color="white" if capped else col, markeredgecolor=col if capped else "white",
                markeredgewidth=1.0 if capped else 0.7, markersize=5.2, zorder=4)
        txt = f"{med:,.0f} (cap)" if capped else f"{med:,.0f}"
        cx.annotate(txt, (max(med, q75), y), xytext=(-5 if capped else 5, 6 if capped else 0), textcoords="offset points",
                    va="center", ha="right" if capped else "left", fontsize=6.6)
    cx.set_yticks(ys)
    cx.set_yticklabels(["Indep. OS", "CD-Joint", "Hybrid", "Info-Track"])
    cx.set_ylim(-0.6, len(order) - 0.4)
    cx.set_xlim(20, 6000)
    _plain_log(cx, "x", (30, 100, 300, 1000, 3000), "{:,.0f}")
    cx.set_xlabel("Median evaluations (log scale)")

    handles = [Line2D([], [], color=style[m][1], marker=style[m][2], markeredgecolor="white", markeredgewidth=0.7)
               for m in order]
    fig.legend(handles, [style[m][0] for m in order], loc="outside lower center", ncol=4, handlelength=2.0)
    ps.save(fig, out / "supp_information_tracking.pdf")


def fig12_protein_calibration_robustness(out: Path) -> None:
    prows = {(r["landscape"], r["method"]): r
             for r in _csv(BAY / "v8_exp1_calibrated_proteins/v8_exp1_protein_summary.csv") if r["stratum"] == "all"}
    crows = _csv(BAY / "v8_exp1_calibrated_proteins/v8_exp1_controlled_summary.csv")

    fig, (ax, bx, cx) = ps.figure(3, height=1.95)

    ps.panel(ax, "a", "Assays to certification")
    ps.ygrid(ax)
    gx, w = _grouped(ax, 2, 2, width=0.7)
    for (m, name, col), x in zip((("indep_os", "Formal DF-OS", REF), ("cd_joint_calibrated", "Calibrated EB+LOO", OURS)), gx):
        vals = [float(prows[(land, m)]["med_steps_25k"]) / 1000.0 for land, _ in LANDSCAPES]
        ps.bars(ax, x, vals, col, width=w * 0.9, labels=[f"{v:.1f}k" for v in vals], legend=name)
    ax.set_xticks(range(2))
    ax.set_xticklabels([n for _, n in LANDSCAPES])
    ax.set_ylim(0, 25.5)
    ax.set_yticks([0, 5, 10, 15, 20])
    ax.set_ylabel("Median assays ($\\times 10^3$)")
    ax.legend(loc="upper left", borderaxespad=0.0)

    ps.panel(bx, "b", "Rough-kernel stress")
    ps.ygrid(bx)
    c3 = {r["method"]: r for r in crows if r["study"] == "C3_misspec_gp_cure"}
    ms = ("bayes_post_nominal", "cd_joint_nominal", "cd_joint_calibrated_eb")
    vals = [100.0 * float(c3[m]["false_cert_rate"]) for m in ms]
    ps.bars(bx, np.arange(3), vals, (BAD, ORANGE, OURS), width=0.58, labels=[f"{v:.1f}%" for v in vals])
    ps.reference(bx, 5.0, "$\\delta=5\\%$")
    bx.set_xticks(range(3))
    bx.set_xticklabels(["Nominal\nBayes", "Nominal\nCD-Joint", "EB+LOO"])
    bx.set_ylim(0, 46)
    bx.set_ylabel("False certificates (%)")

    ps.panel(cx, "c", "Bounded-residual frontier")
    cx.grid(color=ps.GRID, linewidth=0.5)
    c4 = [r for r in crows if r["study"] == "C4_xi_eps_frontier"]
    xis = sorted({float(r["xi"]) for r in c4})
    lk4 = {(float(r["xi"]), r["method"]): 100.0 * float(r["cert_rate"]) for r in c4}
    cx.axvline(0.015, color=MUTED, linestyle=(0, (1.5, 2)), linewidth=0.8, zorder=2)
    cx.annotate("$2\\xi=\\varepsilon$", (0.015, 18), xytext=(3, 0), textcoords="offset points", fontsize=6.6,
                color=MUTED, va="center")
    for m, name, col, mk in (
        ("indep_os", "Formal DF-OS", REF, "D"),
        ("cd_joint_hybrid", "Safe hybrid", PINK, "s"),
        ("cd_joint_robust", "Robust ellipsoid", BLUE, "o"),
    ):
        cx.plot(xis, [lk4[(xi, m)] for xi in xis], color=col, marker=mk, markeredgecolor="white", markeredgewidth=0.7,
                label=name, zorder=4)
    cx.set_xlim(-0.004, 0.084)
    cx.set_xticks([0, 0.02, 0.04, 0.06, 0.08])
    cx.set_xticklabels(["0", ".02", ".04", ".06", ".08"])
    cx.set_ylim(-6, 112)
    cx.set_yticks([0, 25, 50, 75, 100])
    cx.set_xlabel("Residual bound $\\xi$")
    cx.set_ylabel("Completion rate (%)")
    cx.legend(loc="center right", bbox_to_anchor=(1.0, 0.56), handlelength=2.0)
    ps.save(fig, out / "supp_protein_calibration_robustness.pdf")


def fig13_eprocess_safety_and_compute(out: Path) -> None:
    r_b = {r["method"]: r for r in _csv(BAY / "v9_exp3_switching_and_safety/v9_exp3_partB_summary.csv")
           if r["part"] == "B1_null_reset"}
    r_a = {r["method"]: float(r["med_null_calls"])
           for r in _csv(BAY / "v9_exp3_switching_and_safety/v9_exp3_partA_summary.csv")
           if r["sub_regime"] == "natural_hard_init"}
    d4 = {r["method"]: float(r["med_total_ms"]) / 1000.0
          for r in _csv(BAY / "v9_exp1_v34_vs_v33_dag/v9_exp1_summary.csv")
          if r["track"] == "gend_d4_bnb" and int(r["K"]) == 32 and abs(float(r["delta"]) - 0.01) < 1e-6}
    xs = np.arange(3)

    fig, (ax, bx, cx) = ps.figure(3, height=1.95)
    for a in (ax, bx, cx):
        ps.ygrid(a)
        a.set_xticks(xs)

    ps.panel(ax, "a", "Wealth preservation")
    ms = ("neg_ctrl_reset_on_revisit", "v33_preserved_all", "v34_preserved_skip")
    vals = [100.0 * float(r_b[m]["false_cert_rate"]) for m in ms]
    ps.bars(ax, xs, vals, (BAD, BLUE, OURS), width=0.58, labels=[f"{v:.1f}%" for v in vals])
    ps.reference(ax, 100.0 * float(r_b[ms[0]]["delta"]), "$\\delta=5\\%$")
    ax.set_xticklabels(["Invalid\nreset", "Preserved\n(V33)", "Preserved\nskip (V34)"])
    ax.set_ylim(0, 47)
    ax.set_ylabel("Null false certificates (%)")

    ps.panel(bx, "b", "Hard-switch cohort")
    vals = [r_a[m] for m in ("v33_all_action", "v34_bonferroni_j", "v34_full")]
    ps.bars(bx, xs, vals, (BLUE, ORANGE, OURS), width=0.58, labels=[f"{v:.0f}" for v in vals])
    bx.set_xticklabels(["Dense\nall-action", "Local\nBonferroni", "Local IUT\n(V34)"])
    bx.set_ylim(0, 520)
    bx.set_ylabel("Median null-component solves")

    ps.panel(cx, "c", "General $d=4$, $K=32$")
    vals = [d4[m] for m in ("v33_full", "v33_sparse", "v34_full")]
    ps.bars(cx, xs, vals, (BLUE, ORANGE, OURS), width=0.58, labels=[f"{v:.1f} s" for v in vals])
    cx.set_xticklabels(["Dense\n(V33)", "Sparse\nrefresh", "Sparse+local\n(V34)"])
    cx.set_ylim(0, 62)
    cx.set_ylabel("Median total compute (s)")
    ps.save(fig, out / "supp_eprocess_safety_and_compute.pdf")


def fig14_sparse_variance_tracking(out: Path) -> None:
    k64 = {r["method"]: float(r["med_total_ms"]) / 1000.0
           for r in _csv(BAY / "v9_exp1_v34_vs_v33_dag/v9_exp1_summary.csv")
           if r["track"] == "rank2_cubic" and int(r["K"]) == 64 and r["regime"] == "unique"
           and abs(float(r["delta"]) - 0.01) < 1e-6}
    lk = {(r["profile"], r["method"]): 100.0 * float(r["false_cert_rate"])
          for r in _csv(BAY / "v9_exp2_heteroscedastic_info/v9_exp2_partC_summary.csv")}

    fig, (ax, bx) = ps.figure(2, height=1.95, gridspec_kw={"width_ratios": [1.0, 1.15]})

    ps.panel(ax, "a", "$K=64$ rank-two ablation")
    ps.ygrid(ax)
    ms = ("v33_full", "v33_sparse", "v33_local", "v34_full")
    vals = [k64[m] for m in ms]
    ps.bars(ax, np.arange(4), vals, (BLUE, ORANGE, PINK, OURS), width=0.58, labels=[f"{v:.2f} s" for v in vals])
    ax.set_xticks(range(4))
    ax.set_xticklabels(["Dense\n(V33)", "Sparse\nonly", "Local\nonly", "Sparse+local\n(V34)"])
    ax.set_ylim(0, 39)
    ax.set_ylabel("Median cold wall time (s)")

    ps.panel(bx, "b", "Heteroscedastic variance stress")
    ps.ygrid(bx)
    profs = ("sig_025_025", "sig_050_200", "sig_025_400", "sig_400_400")
    gx, w = _grouped(bx, 4, 2, width=0.7)
    for (m, name, col), x in zip((("cd_joint_nom_sig1", "Nominal fixed-$\\sigma$", BAD),
                                  ("v34_vanilla", "Unknown-variance V34", OURS)), gx):
        vals = [lk[(p, m)] for p in profs]
        ps.bars(bx, x, vals, col, width=w * 0.9, labels=[f"{v:.0f}%" for v in vals], legend=name)
    ps.reference(bx, 5.0, "$\\delta=5\\%$")
    bx.set_xticks(range(4))
    bx.set_xticklabels(["(.25, .25)", "(.5, 2)", "(.25, 4)", "(4, 4)"])
    bx.set_ylim(0, 72)
    bx.set_xlabel("True noise profile $(\\sigma_{\\mathrm{in}},\\sigma_{\\mathrm{out}})$")
    bx.set_ylabel("False certificates (%)")
    bx.legend(loc="upper left", borderaxespad=0.0)
    ps.save(fig, out / "supp_sparse_variance_tracking.pdf")


def fig15_native_solver_and_workflows(out: Path) -> None:
    paired = [r for r in _csv(BAY / "v10_exp1_cpp_v34_scaling/v10_exp1_cpp_speedup.csv") if r["py_total_ms"] != "NA"]
    gb1 = {r["method"]: r for r in _csv(BAY / "v10_exp2_real_heteroscedastic_v34/v10_exp2_summary.csv")
           if r["dataset"] == "gb1" and r["track"] == "projected_fixed_feat"}
    live = {r["method"]: r for r in _csv(BAY / "v10_exp3_live_worfbench_expanded/v10_exp3_live_summary.csv")
            if r["scope"] == "ALL"}

    fig, (ax, bx, cx) = ps.figure(3, height=1.95)

    # (a) paired Python / C++ wall time: dumbbells on a log axis (no bars: a log axis has no zero baseline).
    ps.panel(ax, "a", "Certified B&B wall time")
    ax.grid(axis="y", color=ps.GRID, linewidth=0.5)
    ax.tick_params(axis="x", length=0)
    ax.set_yscale("log")
    for i, r in enumerate(paired):
        py, cpp = float(r["py_total_ms"]) / 1000.0, float(r["cpp_total_ms"]) / 1000.0
        ax.plot([i, i], [cpp, py], color=ps.AXIS, linewidth=0.9, zorder=3)
        ax.plot([i], [py], marker="D", color=REF, markeredgecolor="white", markeredgewidth=0.7, markersize=4.6, zorder=4)
        ax.plot([i], [cpp], marker="o", color=OURS, markeredgecolor="white", markeredgewidth=0.7, markersize=5.0, zorder=4)
        ax.annotate(f"{float(r['total_speedup_x']):.0f}$\\times$", (i, np.sqrt(py * cpp)), xytext=(4, 0),
                    textcoords="offset points", va="center", fontsize=6.6)
    ax.set_xticks(range(len(paired)))
    ax.set_xticklabels([f"$d={r['d']}$\n$K={r['K']}$" for r in paired])
    ax.set_xlim(-0.5, len(paired) - 0.3)
    ax.set_ylim(0.04, 400)
    _plain_log(ax, "y", (0.1, 1, 10, 100))
    ax.set_ylabel("Median wall time (s, log scale)")
    ax.legend([Line2D([], [], linestyle="none", marker="D", color=REF, markeredgecolor="white"),
               Line2D([], [], linestyle="none", marker="o", color=OURS, markeredgecolor="white")],
              ["Python", "C++17"], loc="upper left", ncol=2, borderaxespad=0.0, handletextpad=0.1, columnspacing=0.8)

    # (b) projected heteroscedastic GB1: lollipop-free dot plot on a log axis.
    ps.panel(bx, "b", "Projected heteroscedastic GB1")
    bx.grid(axis="y", color=ps.GRID, linewidth=0.5)
    bx.tick_params(axis="x", length=0)
    bx.set_yscale("log")
    for i, (m, col, mk) in enumerate((("indep_student_os", REF, "D"), ("calibrated_eb_loo", OURS, "s"), ("v34_full_cpp", BLUE, "o"))):
        v = float(gb1[m]["med_samples"])
        capped = float(gb1[m]["cert_rate"]) < 0.5
        bx.plot([i], [v], marker=mk, markersize=5.6, color="white" if capped else col,
                markeredgecolor=col if capped else "white", markeredgewidth=1.0 if capped else 0.7, zorder=4)
        ps.label(bx, i, v, f"{v:,.0f}" + ("\n(cap)" if capped else ""), dy=5)
    bx.set_xticks(range(3))
    bx.set_xticklabels(["Student-$t$\nOS", "Calibrated\nEB+LOO", "V34\n(C++)"])
    bx.set_xlim(-0.6, 2.6)
    bx.set_ylim(100, 400000)
    _plain_log(bx, "y", (100, 1000, 10000, 100000), "{:,.0f}")
    bx.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"$10^{{{int(round(np.log10(v)))}}}$"))
    bx.set_ylabel("Median assays (log scale)")

    ps.panel(cx, "c", "Eight live campaigns")
    ps.ygrid(cx)
    ms = ("indep_os", "cd_joint_hybrid", "cd_joint_calibrated")
    vals = [float(live[m]["med_live_tokens"]) / 1000.0 for m in ms]
    runs = [int(live[m]["runs"]) for m in ms]
    cert = [round(float(live[m]["live_cert_rate"]) * n) for m, n in zip(ms, runs)]
    ps.bars(cx, np.arange(3), vals, (REF, PINK, OURS), width=0.58,
            labels=[f"{v:.1f}k\n{c}/{n} cert." for v, c, n in zip(vals, cert, runs)], label_size=6.2)
    cx.set_xticks(range(3))
    cx.set_xticklabels(["DF-OS", "Hybrid\nEB", "Calibrated\nEB+LOO"])
    cx.set_ylim(0, 92)
    cx.set_yticks([0, 20, 40, 60, 80])
    cx.set_ylabel("Median fresh tokens ($\\times 10^3$)")
    ps.save(fig, out / "supp_native_solver_and_workflows.pdf")


FIGURES = (
    fig1_concept_overview,
    fig2_decision_relevant_information,
    fig3_protein_stopping_regimes,
    fig4_acquisition_and_latency,
    fig5_overlap_mechanism,
    fig6_correlation_factorial,
    fig7_overlap_crossover,
    fig8_inside_witness,
    fig9_protein_credibility_audit,
    fig10_live_workflow_validation,
    fig11_information_tracking,
    fig12_protein_calibration_robustness,
    fig13_eprocess_safety_and_compute,
    fig14_sparse_variance_tracking,
    fig15_native_solver_and_workflows,
)


def generate_all(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    ps.setup()
    for fn in FIGURES:
        fn(out_dir)
    print(f"Generated {len(FIGURES)} manuscript figure PDFs (Figures 1-15) in {out_dir}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    generate_all(args.out_dir)


if __name__ == "__main__":
    main()
