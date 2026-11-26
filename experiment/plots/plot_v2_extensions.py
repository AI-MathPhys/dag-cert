"""Generate publication-ready figures for the v2 Exact-Regret, PUCT, SameGame, and Selector suites.

Design conventions (matching plot_uct_backup.py and plot_uct_frontier.py):
- Exact 5.50 in canvas width (1.00x scale in ICLR LaTeX) so 8.0-8.5 pt fonts render
  at exact nominal sizes without rescaling distortion.
- Okabe-Ito colorblind-safe palette, open top/right spines, zero text collisions.
- Generates:
  1. exact_regret_efficiency.pdf (Experiment 1: Statistical & Computational Efficiency vs. Overlap)
  2. puct_transfer.pdf (Experiments 2-4: Root-PUCT Scaling, Noisy Priors, & Representation Selection)
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
import statistics

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DATA = ROOT / "results/uct_v2_extensions"
DEFAULT_OUT = ROOT / "results/uct_v2_extensions/figures"

NAVY = "#1B4F72"      # Graph-Eager / M=64
VERMILION = "#D35400" # Protected/Graph-Selective / M=256
TEAL = "#117864"      # Decision-Selective / Factorized-Regret / M=1024
PURPLE = "#6C3483"    # Charged Dual Covers / Dyadic Covers
GOLD = "#B7950B"      # Paid-Selector / Direct-Graph-Regret
SLATE = "#4A5568"


def setup_rc() -> None:
    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
        "mathtext.fontset": "dejavusans",
        "font.size": 8.1,
        "axes.titlesize": 8.5,
        "axes.titleweight": "bold",
        "axes.labelsize": 8.2,
        "xtick.labelsize": 8.0,
        "ytick.labelsize": 8.0,
        "legend.fontsize": 8.0,
        "axes.linewidth": 0.8,
        "xtick.major.width": 0.8,
        "ytick.major.width": 0.8,
        "xtick.major.size": 3.0,
        "ytick.major.size": 3.0,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.edgecolor": "#4A5568",
        "axes.labelcolor": "#1A202C",
        "text.color": "#1A202C",
        "xtick.color": "#1A202C",
        "ytick.color": "#1A202C",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })


def load_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def plot_exact_regret_efficiency(data_dir: Path, out_dir: Path) -> None:
    stat_rows = load_csv(data_dir / "exp1_exact_regret" / "statistical_summary.csv")
    wall_rows = load_csv(data_dir / "exp1_exact_regret" / "wall_summary.csv")

    fig = plt.figure(figsize=(5.50, 2.52))
    ax_a = fig.add_axes([0.105, 0.20, 0.375, 0.57])
    ax_b = fig.add_axes([0.605, 0.20, 0.375, 0.57])

    # Panel (a): Statistical efficiency tau_exact / tau_conv vs. support overlap rho
    ax = ax_a
    ax.axhline(1.0, color=SLATE, linestyle="--", linewidth=0.85, zorder=1)
    size_styles = [
        (64, "$M = 64$", NAVY, "o", "-"),
        (256, "$M = 256$", VERMILION, "s", "-"),
        (1024, "$M = 1024$", TEAL, "^", "-."),
    ]
    rhos_partial = sorted({float(r["rho"]) for r in stat_rows if float(r["rho"]) < 1.0})

    for m, label, color, marker, ls in size_styles:
        meds, err_lo, err_hi = [], [], []
        for rho in rhos_partial:
            sub = [r for r in stat_rows if int(r["M"]) == m and abs(float(r["rho"]) - rho) < 1e-6]
            med = statistics.median(float(r["med_ratio"]) for r in sub)
            q25 = statistics.median(float(r["q25_ratio"]) for r in sub)
            q75 = statistics.median(float(r["q75_ratio"]) for r in sub)
            meds.append(med)
            err_lo.append(max(0.0, med - q25))
            err_hi.append(max(0.0, q75 - med))
        ax.errorbar(rhos_partial, meds, yerr=[err_lo, err_hi], label=label, color=color,
                    marker=marker, linestyle=ls, linewidth=1.4, markersize=4.1,
                    elinewidth=0.9, capsize=2.0, zorder=3)

    # Separated identical-support point at rho = 1.0 (tau_exact = 0)
    ax.plot([0.94, 0.94], [-0.04, 0.62], color="#CBD5E0", linestyle=":", linewidth=0.8, zorder=1)
    ax.scatter([1.0], [0.0], color=PURPLE, marker="D", s=26, zorder=4)
    ax.annotate("Identical\n($\\tau_{\\mathrm{exact}}=0$)", xy=(1.0, 0.04), xytext=(0.64, 0.76),
                fontsize=8.0, color=PURPLE,
                arrowprops=dict(arrowstyle="->", lw=0.75, color=PURPLE,
                                connectionstyle="arc3,rad=-0.12", shrinkA=4, shrinkB=4))

    ax.set_xlim(-0.04, 1.06)
    ax.set_ylim(-0.05, 1.12)
    ax.set_xticks([0.0, 0.25, 0.50, 0.75, 1.00])
    ax.set_xticklabels(["0", "0.25", "0.50", "0.75", "1.0"])
    ax.set_xlabel("Root-support overlap $\\rho$")
    ax.set_ylabel("Stopping ratio $\\tau_{\\mathrm{exact}} / \\tau_{\\mathrm{conv}}$")
    ax.set_title("(a) Statistical sample efficiency", loc="left", pad=5)
    ax.legend(loc="lower left", bbox_to_anchor=(0.01, 0.02), frameon=False,
              handlelength=1.35, labelspacing=0.24, borderpad=0.1)

    # Panel (b): Computational efficiency — End-to-end runtime vs. overlap at M = 256 (Bernoulli, gap=0.42)
    ax = ax_b
    all_rhos = sorted({float(r["rho"]) for r in wall_rows})
    meth_styles = [
        ("quotient-protected", "Conv. Graph", NAVY, "o", "--"),
        ("dyadic-covers", "Conv. Covers", SLATE, "D", ":"),
        ("dual-covers", "Exact Dual Covers", PURPLE, "s", "-"),
        ("factorized-regret", "Exact Factorized", TEAL, "^", "-"),
    ]
    avail_gaps = sorted({float(r["gap"]) for r in wall_rows if int(r["M"]) == 256})
    target_gap = avail_gaps[-1]

    for key, label, color, marker, ls in meth_styles:
        ys = []
        for rho in all_rhos:
            sub = [
                float(r["med_restricted_ms"])
                for r in wall_rows
                if int(r["M"]) == 256
                and abs(float(r["gap"]) - target_gap) < 1e-6
                and r["reward_mode"] == "bernoulli"
                and abs(float(r["rho"]) - rho) < 1e-6
                and r["method"] == key
            ]
            ys.append(statistics.median(sub) if sub else float("nan"))
        ax.plot(all_rhos, ys, label=label, color=color, marker=marker,
                linestyle=ls, linewidth=1.4, markersize=4.1, zorder=3)

    ax.set_yscale("log")
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.set_xlim(-0.04, 1.06)
    ax.set_xticks([0.0, 0.25, 0.50, 0.75, 1.00])
    ax.set_xticklabels(["0", "0.25", "0.50", "0.75", "1.0"])
    ax.set_xlabel("Root-support overlap $\\rho$ ($M=256$)")
    ax.set_ylabel("End-to-end cert. time (ms)")
    ax.set_title("(b) End-to-end runtime", loc="left", pad=5)

    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", bbox_to_anchor=(0.52, 0.99),
               ncol=4, frameon=False, handlelength=1.4, columnspacing=0.85, handletextpad=0.35)

    fig.savefig(out_dir / "exact_regret_efficiency.pdf")
    plt.close(fig)


def plot_puct_transfer(data_dir: Path, out_dir: Path) -> None:
    root_rows = load_csv(data_dir / "exp2_puct" / "root_puct_summary.csv")
    noisy_rows = load_csv(data_dir / "exp2_puct" / "noisy_puct_summary.csv")
    rep_rows = load_csv(data_dir / "exp4_representation" / "representation_summary.csv")

    fig = plt.figure(figsize=(5.50, 2.55))
    ax_a = fig.add_axes([0.100, 0.20, 0.215, 0.56])
    ax_b = fig.add_axes([0.430, 0.20, 0.215, 0.56])
    ax_c = fig.add_axes([0.775, 0.20, 0.205, 0.56])

    # Panel (a): Deterministic Root-PUCT uncensored polynomial work separation (m in 16..1024)
    ax = ax_a
    sizes = [16, 64, 256, 1024]
    puct_styles = [
        ("graph-eager", "Graph-Eager", NAVY, "o", "-"),
        ("protected-selective", "Protected-Sel.", VERMILION, "s", "--"),
        ("decision-selective", "Decision-Sel.", TEAL, "^", "-"),
        ("dual-covers", "Dual Covers", PURPLE, "D", "-."),
    ]
    for key, label, color, marker, ls in puct_styles:
        ys = [
            float(next(r["med_work"] for r in root_rows
                       if r["prior"] == "unit_lambda" and int(r["m"]) == m and r["method"] == key))
            / 1e6
            for m in sizes
        ]
        ax.plot(sizes, ys, label=label, color=color, marker=marker,
                linestyle=ls, linewidth=1.35, markersize=3.9)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.set_xlim(12, 1350)
    ax.set_xticks([16, 64, 256, 1024])
    ax.set_xticklabels(["16", "64", "256", "1k"])
    ax.set_xlabel("Funnel width $m$")
    ax.set_ylabel("Scalar work ($10^6$ ops)")
    ax.set_title("(a) Root-PUCT scaling", loc="left", pad=5)

    # Panel (b): Noisy Recursive-PUCT monitor work ratio vs. Graph-Eager across priors (funnel_256_narrow)
    ax = ax_b
    regimes = [
        ("recursive_puct", "informative", "Inf."),
        ("recursive_puct", "uniform", "Unif."),
        ("recursive_puct", "misleading", "Misl."),
        ("uct", "none", "UCT"),
    ]
    xs = list(range(len(regimes)))
    ax.axhline(1.0, color=SLATE, linestyle="--", linewidth=0.80, zorder=1)
    ax.axvline(2.5, color="#CBD5E0", linestyle=":", linewidth=0.80, zorder=1)
    bar_w = 0.24
    bar_methods = [
        ("protected-selective", VERMILION, -bar_w),
        ("decision-selective", TEAL, 0.0),
        ("dual-covers", PURPLE, bar_w),
    ]
    for key, color, offset in bar_methods:
        vals = []
        for pol, pr, _ in regimes:
            match = [
                float(r["mon_work_ratio_vs_eager"])
                for r in noisy_rows
                if r["case"] == "funnel_256_narrow" and r["policy"] == pol
                and r["prior"] == pr and r["method"] == key
            ]
            vals.append(match[0] if match else 1.0)
        ax.bar([x + offset for x in xs], vals, width=bar_w, color=color, alpha=0.88, zorder=3)

    ax.set_ylim(0.0, 1.26)
    ax.set_xticks(xs)
    ax.set_xticklabels([lbl for _, _, lbl in regimes])
    ax.set_xlabel("PUCT prior / UCT ref.")
    ax.set_ylabel("Monitor work vs. Eager")
    ax.set_title("(b) Noisy funnel ($m=256$)", loc="left", pad=5)

    # Panel (c): Representation-aware exact-regret runtime ratio vs. Dual Covers
    ax = ax_c
    rep_configs = [
        ("coded_32", "Coded 32"),
        ("coded_16", "Coded 16"),
        ("window_64", "Win. 64"),
        ("core_32", "Core 32"),
        ("overlap_256_rho50", "Ovlp. 256"),
    ]
    ys_pos = list(range(len(rep_configs)))
    ax.axvline(1.0, color=SLATE, linestyle="--", linewidth=0.80, zorder=1)
    rep_styles = [
        ("direct-graph-regret", "Direct Graph", NAVY, "o", -0.19),
        ("factorized-regret", "Factorized", TEAL, "^", 0.0),
        ("paid-selector", "Paid Selector", GOLD, "D", 0.19),
    ]
    for key, lbl, color, marker, off in rep_styles:
        rx, ry = [], []
        for idx, (cfg, _) in enumerate(rep_configs):
            match = [float(r["time_ratio_vs_dual"]) for r in rep_rows
                     if r["config"] == cfg and r["method"] == key]
            if match:
                rx.append(match[0])
                ry.append(idx + off)
        ax.scatter(rx, ry, color=color, marker=marker, s=22, zorder=3, label=lbl)

    ax.set_xscale("log")
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.set_yticks(ys_pos)
    ax.set_yticklabels([lbl for _, lbl in rep_configs])
    ax.set_ylim(-0.55, 4.55)
    ax.invert_yaxis()
    ax.set_xlim(0.48, 3.1)
    ax.set_xticks([0.5, 1.0, 2.0])
    ax.set_xticklabels(["0.5", "1.0", "2.0"])
    ax.set_xlabel("Time vs. Dual Covers")
    ax.set_title("(c) Repr. selection", loc="left", pad=5)

    # Unified top legend combining PUCT & Selector markers cleanly
    h1, _ = ax_a.get_legend_handles_labels()
    h3, _ = ax_c.get_legend_handles_labels()
    handles = [h1[0], h1[1], h1[2], h1[3], h3[2]]
    labels = ["Graph-Eager", "Protected-Sel.", "Decision/Fact.", "Dual Covers", "Paid Selector"]
    fig.legend(handles, labels, loc="upper center", bbox_to_anchor=(0.50, 0.99),
               ncol=5, frameon=False, handlelength=1.2, columnspacing=0.72, handletextpad=0.3)

    fig.savefig(out_dir / "puct_transfer.pdf")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    setup_rc()
    plot_exact_regret_efficiency(args.data, args.out)
    plot_puct_transfer(args.data, args.out)
    print(f"Saved exact_regret_efficiency.pdf and puct_transfer.pdf to {args.out}")


if __name__ == "__main__":
    main()
