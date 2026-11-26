"""Generate publication-ready 3-panel synthesis figure for the v3 strengthening suites.

Design conventions (matching plot_uct_backup.py, plot_uct_frontier.py, and plot_v2_extensions.py):
- Exact 5.50 in canvas width (1.00x scale in ICLR LaTeX) with 8.0-8.5 pt DejaVu Sans fonts.
- Generates `strengthening_synthesis.pdf`:
  * Panel (a): Deeper SameGame certification rate across Hoeffding vs. Empirical Bernstein
    and Conventional vs. Exact Regret (Experiment 5).
  * Panel (b): Active Witness-Guided Allocation (`Exact-Regret-DAG-LUCB` vs. `Marginal-DAG-LUCB`
    vs. passive `TA-UCT + Exact Regret`) runtime across overlap rho (Experiment 6).
  * Panel (c): Native `-O3` C++17 uncensored wall-clock scaling up to m = 4096 under Root-PUCT
    (Experiment 7).
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path
import statistics

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DATA = ROOT / "results/uct_v3_strengthening"
DEFAULT_OUT = ROOT / "results/uct_v3_strengthening/figures"

NAVY = "#1B4F72"
VERMILION = "#D35400"
TEAL = "#117864"
PURPLE = "#6C3483"
GOLD = "#B7950B"
SLATE = "#4A5568"


def setup_rc() -> None:
    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
        "mathtext.fontset": "dejavusans",
        "font.size": 8.0,
        "axes.titlesize": 8.4,
        "axes.titleweight": "bold",
        "axes.labelsize": 8.1,
        "xtick.labelsize": 8.0,
        "ytick.labelsize": 8.0,
        "legend.fontsize": 7.8,
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


def plot_strengthening_synthesis(data_dir: Path, out_dir: Path) -> None:
    eb_wall = load_csv(data_dir / "exp5_emp_bernstein" / "summary_wall.csv")
    lucb_ov = load_csv(data_dir / "exp6_dag_lucb" / "summary_overlap_curves.csv")
    cpp_rows = load_csv(data_dir / "exp7_cpp_kernels" / "summary_by_family.csv")

    fig = plt.figure(figsize=(5.50, 2.95))
    ax_a = fig.add_axes([0.095, 0.175, 0.220, 0.48])
    ax_b = fig.add_axes([0.430, 0.175, 0.220, 0.48])
    ax_c = fig.add_axes([0.765, 0.175, 0.210, 0.48])

    # Panel (a): Empirical Bernstein + Exact Regret on SameGame (Cert. rate %)
    ax = ax_a
    sg_fams = [
        ("samegame_6x6_d3", "6x6\nd=3"),
        ("samegame_std15x15_d3", "15x15\nd=3"),
        ("samegame_std15x15_d4", "15x15\nd=4"),
    ]
    xs = list(range(len(sg_fams)))
    bw = 0.185
    combos = [
        ("hoeff_conv", "Hoeff. Conv.", NAVY, -1.5 * bw),
        ("hoeff_exact", "Hoeff. Exact", VERMILION, -0.5 * bw),
        ("eb_conv", "EB Conv.", TEAL, 0.5 * bw),
        ("eb_exact", "EB Exact", PURPLE, 1.5 * bw),
    ]
    for ckey, clbl, col, off in combos:
        vals = []
        for fam, _ in sg_fams:
            m = [100.0 * float(r["cert_rate"]) for r in eb_wall
                 if r["family"] == fam and r["combo"] == ckey]
            vals.append(m[0] if m else 0.0)
        ax.bar([x + off for x in xs], vals, width=bw, color=col, alpha=0.90, label=clbl, zorder=3)

    ax.set_ylim(0, 112)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_xticks(xs)
    ax.set_xticklabels([lbl for _, lbl in sg_fams])
    ax.set_ylabel("Certified in 1 s (%)")
    ax.set_title("(a) Variance-adaptive CS", loc="left", pad=5)
    ax.legend(loc="lower left", bbox_to_anchor=(-0.08, 1.16), ncol=2, frameon=False,
              handlelength=0.85, columnspacing=0.50, handletextpad=0.28, labelspacing=0.20)

    # Panel (b): Active Witness Allocation (DAG-LUCB) runtime vs. overlap rho
    ax = ax_b
    rhos = sorted({float(r["rho"]) for r in lucb_ov})
    ctrl_styles = [
        ("passive_uct_exact_med_ms", "TA-UCT + Exact", NAVY, "o", "--"),
        ("marginal_dag_lucb_med_ms", "Marg. LUCB", VERMILION, "s", ":"),
        ("exact_lucb_dual_med_ms", "Exact LUCB", PURPLE, "D", "-"),
    ]
    for col_key, lbl, col, mk, ls in ctrl_styles:
        ys = []
        for rho in rhos:
            sub = [float(r[col_key]) for r in lucb_ov
                   if abs(float(r["rho"]) - rho) < 1e-6 and r["reward_mode"] == "bernoulli"]
            if not sub:
                sub = [float(r[col_key]) for r in lucb_ov if abs(float(r["rho"]) - rho) < 1e-6]
            ys.append(max(0.6, statistics.median(sub)))
        ax.plot(rhos, ys, label=lbl, color=col, marker=mk, linestyle=ls,
                linewidth=1.35, markersize=3.8, zorder=3)

    ax.set_yscale("log")
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.set_xlim(-0.05, 1.06)
    ax.set_xticks([0.0, 0.5, 1.0])
    ax.set_xticklabels(["0", "0.5", "1.0"])
    ax.set_xlabel("Support overlap $\\rho$")
    ax.set_ylabel("Med. cert. time (ms)")
    ax.set_title("(b) Active DAG-LUCB", loc="left", pad=5)
    ax.legend(loc="lower left", bbox_to_anchor=(-0.05, 1.16), ncol=1, frameon=False,
              handlelength=1.20, handletextpad=0.3, labelspacing=0.15)

    # Panel (c): Native -O3 C++17 uncensored Root-PUCT wall-clock scaling (m in 16..4096)
    ax = ax_c
    sizes = [16, 64, 256, 1024, 4096]
    cpp_styles = [
        ("graph-eager", "C++ Eager", NAVY, "o", "-"),
        ("decision-selective", "C++ Dec.-Sel.", TEAL, "^", "-"),
        ("dual-covers", "C++ Dual", PURPLE, "D", "-."),
    ]
    for mkey, lbl, col, mk, ls in cpp_styles:
        ys = [
            float(next(r["median_total_ms"] for r in cpp_rows
                       if r["suite"] == "root_puct_scaling"
                       and int(r["m"]) == m and r["method"] == mkey))
            for m in sizes
        ]
        ax.plot(sizes, ys, label=lbl, color=col, marker=mk, linestyle=ls,
                linewidth=1.35, markersize=3.8, zorder=3)

    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.set_xlim(11, 5800)
    ax.set_xticks([16, 256, 4096])
    ax.set_xticklabels(["16", "256", "4k"])
    ax.set_xlabel("Funnel width $m$")
    ax.set_ylabel("Native C++17 time (ms)")
    ax.set_title("(c) C++17 PUCT", loc="left", pad=5)
    ax.legend(loc="lower left", bbox_to_anchor=(-0.05, 1.16), ncol=1, frameon=False,
              handlelength=1.20, handletextpad=0.3, labelspacing=0.15)

    fig.savefig(out_dir / "strengthening_synthesis.pdf")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    setup_rc()
    plot_strengthening_synthesis(args.data, args.out)
    print(f"Saved strengthening_synthesis.pdf to {args.out}")


if __name__ == "__main__":
    main()
