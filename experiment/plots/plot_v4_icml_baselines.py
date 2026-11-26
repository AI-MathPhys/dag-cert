"""Generate publication-ready 3-panel figure for the v4 ICML External Baselines & Zero-Containment suites.

Design conventions:
- Exact 5.50 in canvas width (1.00x scale in LaTeX) with 8.0-8.4 pt DejaVu Sans fonts.
- Generates `external_baselines_natural.pdf`:
  * Panel (a): 2x2 `(Sampler x Certificate)` factorial across overlap rho (M=256), comparing
    `LUCB-micro` (Marginal vs. Exact Stop), `UGapE-DAG` (Exact Stop), and `Exact-Regret-DAG-LUCB`.
  * Panel (b): Strictly Zero-Containment (`S(b) not subseteq S(a)`) large natural DAGs
    (Mid-Game 15x15 SameGame, Multi-Hop Routing DAGs, and 0-containment 15x15 Endgames).
  * Panel (c): Inside-witness selection ablation (`UCB` vs. `Mean` vs. `LCB`) inside
    `Exact-Regret-DAG-LUCB`.
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DATA = ROOT / "results/uct_v4_icml_baselines"
DEFAULT_OUT = ROOT / "results/uct_v4_icml_baselines/figures"

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
        "axes.titlesize": 8.3,
        "axes.titleweight": "bold",
        "axes.labelsize": 8.1,
        "xtick.labelsize": 7.9,
        "ytick.labelsize": 8.0,
        "legend.fontsize": 7.6,
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


def plot_external_baselines_natural(data_dir: Path, out_dir: Path) -> None:
    fac_rows = load_csv(data_dir / "exp8_external_baselines" / "summary_2x2_overlap256.csv")
    nat_rows = load_csv(data_dir / "exp9_samegame_midgame" / "summary_stratified.csv")
    ins_rows = load_csv(data_dir / "exp10_inside_witness" / "summary_by_family.csv")
    hyb_path = data_dir / "exp11_hybrid_and_os" / "summary_hybrid_by_family.csv"
    hyb_rows = load_csv(hyb_path) if hyb_path.is_file() else []

    fig = plt.figure(figsize=(5.50, 3.00))
    ax_a = fig.add_axes([0.095, 0.18, 0.215, 0.47])
    ax_b = fig.add_axes([0.430, 0.18, 0.225, 0.47])
    ax_c = fig.add_axes([0.770, 0.18, 0.210, 0.47])

    # Panel (a): 2x2 Sampler x Certificate median steps vs. overlap rho (M=256)
    ax = ax_a
    rhos = [float(r["rho"]) for r in fac_rows]
    curves = [
        ("lucb_micro_exact_steps", "LUCB-micro + Ex", NAVY, "o", ":"),
        ("ugape_dag_marg_steps", "UGapE-DAG", VERMILION, "s", "--"),
        ("ta_uct_exact_steps", "TA-UCT + Ex", TEAL, "^", "-."),
        ("exact_dag_lucb_steps", "Exact DAG-LUCB", PURPLE, "D", "-"),
    ]
    for ckey, lbl, col, mk, ls in curves:
        ys = [max(100.0, float(r[ckey])) / 1000.0 for r in fac_rows]
        ax.plot(rhos, ys, label=lbl, color=col, marker=mk, linestyle=ls,
                linewidth=1.35, markersize=3.7, zorder=3)

    ax.set_yscale("log")
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.set_xlim(-0.05, 0.94)
    ax.set_xticks([0.0, 0.25, 0.5, 0.88])
    ax.set_xticklabels(["0", ".25", ".5", ".88"])
    ax.set_xlabel("Support overlap $\\rho$")
    ax.set_ylabel("Med. samples ($10^3$)")
    ax.set_title("(a) 2x2 sampler vs. cert.", loc="left", pad=5)
    ax.legend(loc="lower left", bbox_to_anchor=(-0.08, 1.16), ncol=1, frameon=False,
              handlelength=1.20, handletextpad=0.28, labelspacing=0.14)

    # Panel (b): Strictly Zero-Containment Large Natural DAGs (median time ms, log scale)
    ax = ax_b
    candidate_strata = [
        ("endgame_15x15_d4_zero_contain", "SG15\n0-C"),
        ("random_6x6_d4_zero_contain", "SG6\nd=4"),
        ("routing_w32_d5_zero_contain", "Rt\n313"),
        ("routing_w96_d5_zero_contain", "Rt\n889"),
    ]
    present = [(st, lbl) for st, lbl in candidate_strata
               if any(r["stratum"] == st for r in nat_rows)]
    xs = list(range(len(present)))
    bw = 0.19
    nat_methods = [
        ("ta_uct_exact", "TA-UCT Ex", TEAL, -1.5 * bw),
        ("lucb_micro_marg", "LUCB-micro", NAVY, -0.5 * bw),
        ("ugape_mcts_dag_marg", "UGapE-DAG", VERMILION, 0.5 * bw),
        ("exact_dag_lucb", "Exact LUCB", PURPLE, 1.5 * bw),
    ]
    for mkey, mlbl, col, off in nat_methods:
        vals = []
        for st, _ in present:
            m = [float(r["median_total_ms"]) for r in nat_rows
                 if r["stratum"] == st and r["method"] == mkey]
            vals.append(m[0] if m else 1.0)
        ax.bar([x + off for x in xs], vals, width=bw, color=col, alpha=0.90, label=mlbl, zorder=3)

    ax.set_yscale("log")
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.set_ylim(30, 2400)
    ax.set_xticks(xs)
    ax.set_xticklabels([lbl for _, lbl in present])
    ax.set_ylabel("Med. time (ms) [0-contain]")
    ax.set_title("(b) Zero-containment DAGs", loc="left", pad=5)
    ax.legend(loc="lower left", bbox_to_anchor=(-0.06, 1.16), ncol=2, frameon=False,
              handlelength=0.85, columnspacing=0.45, handletextpad=0.25, labelspacing=0.18)

    # Panel (c): Inside-witness rule ablation & safeguarded hybrid (certification rate %)
    ax = ax_c
    ins_fams = [
        ("decoy_trap_16", "Dc\n16"),
        ("window_64", "Wn\n64"),
        ("hetero_support_256", "Ht\n256"),
        ("samegame_mid15x15_d4_zero_contain", "SG\nMid"),
    ]
    ins_present = [(fm, lbl) for fm, lbl in ins_fams
                   if any(r["family"] == fm for r in ins_rows)]
    ixs = list(range(len(ins_present)))
    ibw = 0.19
    ins_modes = [
        ("ucb", "UCB", PURPLE, -1.5 * ibw, "exp10"),
        ("mean", "Mean", GOLD, -0.5 * ibw, "exp10"),
        ("lcb", "LCB", VERMILION, 0.5 * ibw, "exp10"),
        ("hybrid", "Hybrid", TEAL, 1.5 * ibw, "exp11"),
    ]
    for mode, mlbl, col, off, src in ins_modes:
        vals = []
        for fm, _ in ins_present:
            if src == "exp10":
                m = [100.0 * float(r["cert_rate"]) for r in ins_rows
                     if r["family"] == fm and r["inside_mode"] == mode]
            else:
                m = [100.0 * float(r["cert_rate"]) for r in hyb_rows
                     if r["family"] == fm and r["method"] == mode]
            vals.append(m[0] if m else 0.0)
        ax.bar([x + off for x in ixs], vals, width=ibw, color=col, alpha=0.90, label=mlbl, zorder=3)

    ax.set_ylim(0, 112)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_xticks(ixs)
    ax.set_xticklabels([lbl for _, lbl in ins_present])
    ax.set_ylabel("Certified (%)")
    ax.set_title("(c) Inside witness", loc="left", pad=5)
    ax.legend(loc="lower left", bbox_to_anchor=(-0.08, 1.16), ncol=2, frameon=False,
              handlelength=0.80, columnspacing=0.45, handletextpad=0.24, labelspacing=0.18)

    fig.savefig(out_dir / "external_baselines_natural.pdf")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    setup_rc()
    plot_external_baselines_natural(args.data, args.out)
    print(f"Saved external_baselines_natural.pdf to {args.out}")


if __name__ == "__main__":
    main()
