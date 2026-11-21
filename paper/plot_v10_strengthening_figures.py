#!/usr/bin/env python3
"""Publication figure generator for v10 Strengthening Suite.

Generates `fig_v10_cpp_real_live.pdf` (+ 260-DPI QA PNG), matching `iclr2027_conference.sty`
(`\\textwidth = 5.50 in`), Okabe-Ito colorblind-safe palette, zero overlaps:
  (a) Native -O3 C++17 vs Python certified B&B scaling across d in {2, 4, 6, 8} (K=16)
  (b) Real-world heteroscedastic V34 bridge on GB1 & WorFBench (projected vs unprojected residual)
  (c) Expanded uncached live Qwen3-0.6B WorFBench cohort (8 paired campaigns / 24 live runs)
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib as mpl
mpl.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATA = ROOT / "results/bayesian_ucd_v1"
DEFAULT_OUT = ROOT / "results/bayesian_ucd_v1/figures"

PAL = {
    "cpp": "#0B5394",
    "cpp_cold": "#2B8CBE",
    "py": "#D55E00",
    "eb": "#0E8A74",
    "nom": "#B8332A",
    "os": "#5C6B73",
    "ochre": "#B8860B",
    "ink": "#1F2933",
    "grid": "#E5E9F0",
}

mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
    "mathtext.fontset": "dejavusans",
    "font.size": 6.9,
    "axes.titlesize": 6.7,
    "axes.labelsize": 6.7,
    "xtick.labelsize": 6.0,
    "ytick.labelsize": 6.0,
    "legend.fontsize": 5.1,
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
            fontsize=6.6, fontweight="bold", color=PAL["ink"])


def plot_v10(data_dir: Path, out_dir: Path) -> None:
    s1 = load_csv(data_dir / "v10_exp1_cpp_v34_scaling/v10_exp1_summary.csv")
    s2 = load_csv(data_dir / "v10_exp2_real_heteroscedastic_v34/v10_exp2_summary.csv")
    s3 = load_csv(data_dir / "v10_exp3_live_worfbench_expanded/v10_exp3_live_summary.csv")

    fig, axes = plt.subplots(1, 3, figsize=(5.50, 2.25))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.22, top=0.83, wspace=0.40)

    # Panel (a): C++17 vs Python B&B scaling across d in {2, 4, 6, 8} (K=16, zeta=0.1)
    ax = axes[0]
    style_axis(ax, "y")
    add_header(ax, "a", r"C++17 B&B ($K{=}16,\zeta{=}.1$)")
    ds = [2, 4, 6, 8]
    x = np.arange(len(ds))
    cpp_g = [float(next(r for r in s1 if int(r["d"]) == d and int(r["K"]) == 16 and abs(float(r["zeta"]) - 0.1) < 1e-9 and r["method"] == "cpp_hybrid_qp_gated")["med_total_ms"]) for d in ds]
    cpp_c = [float(next(r for r in s1 if int(r["d"]) == d and int(r["K"]) == 16 and abs(float(r["zeta"]) - 0.1) < 1e-9 and r["method"] == "cpp_cold_bnb")["med_total_ms"]) for d in ds]
    py_pts = []
    for i, d in enumerate(ds):
        matches = [r for r in s1 if int(r["d"]) == d and int(r["K"]) == 16 and abs(float(r["zeta"]) - 0.1) < 1e-9 and r["method"] == "py_hybrid_qp_gated"]
        if matches:
            py_pts.append((i, float(matches[0]["med_total_ms"])))
    ax.plot(x, cpp_c, color=PAL["cpp_cold"], linestyle="--", marker="s", markersize=3.0, linewidth=1.2, label="C++ Cold B&B", zorder=4)
    ax.plot(x, cpp_g, color=PAL["cpp"], linestyle="-", marker="o", markersize=3.2, linewidth=1.35, label="C++ Hyb.+Gate", zorder=5)
    if py_pts:
        ax.plot([p[0] for p in py_pts], [p[1] for p in py_pts], color=PAL["py"], linestyle=":", marker="^", markersize=3.4, linewidth=1.25, label="Py Hyb.+Gate", zorder=4)
        # Annotate 55x speedup at d=6
        p6 = [p[1] for p in py_pts if p[0] == 2]
        if p6:
            sp = p6[0] / cpp_g[2]
            ax.annotate(f"{sp:.0f}×", xy=(2, cpp_g[2]), xytext=(1.55, cpp_g[2] * 6.5),
                        fontsize=5.6, fontweight="bold", color=PAL["cpp"],
                        arrowprops=dict(arrowstyle="->", color=PAL["cpp"], lw=0.7))
    ax.set_yscale("log")
    ax.set_ylim(50, 90000)
    ax.set_xticks(x)
    ax.set_xticklabels([f"d={d}" for d in ds])
    ax.set_ylabel("Median solver ms (log)")
    ax.legend(frameon=False, loc="upper left", fontsize=4.9, handlelength=1.1, labelspacing=0.2)

    # Panel (b): Real heteroscedastic GB1 (projected fixed features, authentic Wu et al. shot noise)
    ax = axes[1]
    style_axis(ax, "y")
    add_header(ax, "b", "GB1 het. bridge (proj.)")
    sub_gb = [r for r in s2 if r["dataset"] == "gb1" and r["track"] == "projected_fixed_feat"]
    m_order = [
        ("v34_full_cpp", "V34\nFull", PAL["cpp"]),
        ("v34_gated_cpp", "V34\nGate", PAL["cpp_cold"]),
        ("calibrated_eb_loo", "Calib.\nEB", PAL["eb"]),
        ("indep_student_os", "Stud.\nOS", PAL["os"]),
    ]
    bx = np.arange(len(m_order))
    vals = [float(next(r for r in sub_gb if r["method"] == m)["med_samples"]) for m, _, _ in m_order]
    cols = [c for _, _, c in m_order]
    ax.bar(bx, vals, width=0.58, color=cols, edgecolor="white", linewidth=0.5, zorder=3)
    for i, v in enumerate(vals):
        lbl = f"{v/1000:.1f}k" if v >= 1000 else f"{v:.0f}"
        ax.text(i, v * 1.15, lbl, ha="center", va="bottom", fontsize=5.3, fontweight="bold", color=cols[i])
    ax.set_yscale("log")
    ax.set_ylim(50, max(vals) * 3.5)
    ax.set_xticks(bx)
    ax.set_xticklabels([l for _, l, _ in m_order], fontsize=5.5)
    ax.set_ylabel("Median assays (log)")

    # Panel (c): Expanded Live Uncached Qwen3-0.6B Certification (ALL 8 paired campaigns = 24 live runs)
    ax = axes[2]
    style_axis(ax, "y")
    add_header(ax, "c", "Live Qwen3 (n=8)")
    sub_l = [r for r in s3 if r["scope"] == "ALL"]
    l_order = [
        ("indep_os", "Indep.\nOS", PAL["os"]),
        ("cd_joint_calibrated", "Calib.\nEB", PAL["eb"]),
        ("cd_joint_hybrid", "Hybrid\nEB", PAL["cpp"]),
    ]
    lx = np.arange(len(l_order))
    toks = [float(next(r for r in sub_l if r["method"] == m)["med_live_tokens"]) / 1000.0 for m, _, _ in l_order]
    certs = [100.0 * float(next(r for r in sub_l if r["method"] == m)["live_cert_rate"]) for m, _, _ in l_order]
    lcols = [c for _, _, c in l_order]
    ax.bar(lx, toks, width=0.55, color=lcols, edgecolor="white", linewidth=0.5, zorder=3)
    for i, (tk, ct) in enumerate(zip(toks, certs)):
        ax.text(i, tk + max(toks) * 0.03, f"{tk:.1f}k\n({ct:.0f}%)", ha="center", va="bottom",
                fontsize=5.2, fontweight="bold", color=lcols[i])
    ax.set_ylim(0, max(toks) * 1.32)
    ax.set_xticks(lx)
    ax.set_xticklabels([l for _, l, _ in l_order], fontsize=5.6)
    ax.set_ylabel("Med. fresh tokens (k)")

    out_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_dir / "fig_v10_cpp_real_live.pdf", format="pdf", dpi=300)
    fig.savefig(out_dir / "fig_v10_cpp_real_live.png", format="png", dpi=260)
    plt.close(fig)
    print(f"Wrote v10 figure to {out_dir}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    plot_v10(args.data_dir, args.out_dir)


if __name__ == "__main__":
    main()
