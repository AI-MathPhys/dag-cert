"""Generate the flagship 3-panel publication figure for v12: Decision-Aware BED vs. BO on Search DAGs.

Panel (a): Matched-model certification efficiency (M=64, K=8, cap 12k, n=100/cond) — restricted mean
           evaluations with 95% paired bootstrap CIs across Conditions A-D for GP-UCB, Correlated KG,
           GP-OS, and CD-Joint under identical shared Gaussian posterior & credible ellipsoid stopping.
Panel (b): Bayesian minimum root risk `min_a q_t(a)` vs. evaluation budget on the M=16, K=4 VOI
           reference study (Conditions C/D or pooled ALL, n=160) comparing GP-UCB, KG, GP-OS,
           CD-Joint, and Bayesian Root-Risk VOI against the delta=0.05 reference threshold.
Panel (c): Cost-sensitive low-valued proxy benchmark (M=5, K=2, d=3, n=80/cell) — total certification
           cost (log scale) and proxy-query allocation fraction across alignment {0.50, 0.95} and
           proxy price {0.25, 1, 4} for KG, CD-Joint, and Bayesian Root-Risk VOI.
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[2]
V12_DIR = ROOT / "results/bayesian_ucd_v1/v12_bed_vs_bo"
DEFAULT_OUT = ROOT / "results/bayesian_ucd_v1/figures"

COLORS = {
    "gp_ucb": "#6B7280",       # slate grey
    "gp_ts": "#9CA3AF",        # light grey
    "gp_ei": "#A8A29E",        # warm grey
    "kg": "#D97706",           # amber / orange
    "gp_os": "#2563EB",        # royal blue
    "cd_joint": "#0D9488",     # teal
    "bayesian_voi": "#9333EA", # purple
}

LABELS = {
    "gp_ucb": "GP-UCB",
    "gp_ts": "GP-TS",
    "gp_ei": "Noisy GP-EI",
    "kg": "Correlated KG",
    "gp_os": "GP-OS",
    "cd_joint": "CD-Joint",
    "bayesian_voi": "Bayesian VOI",
}


def _read_csv(path: Path) -> list[dict]:
    with path.open("r", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def _style_ax(ax: plt.Axes) -> None:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_linewidth(0.8)
    ax.spines["bottom"].set_linewidth(0.8)
    ax.tick_params(labelsize=7.5, length=3.0, width=0.7)
    ax.grid(axis="y", linestyle="-", linewidth=0.45, color="#E5E7EB", zorder=0)
    ax.set_axisbelow(True)


def make_figure(data_dir: Path, out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    main_rows = _read_csv(data_dir / "v12_main64_summary.csv")
    voi_ck = _read_csv(data_dir / "v12_voi16_checkpoints.csv")
    proxy_rows = _read_csv(data_dir / "v12_proxy5_summary.csv")

    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 8.0,
            "axes.titlesize": 8.5,
            "axes.labelsize": 8.0,
            "legend.fontsize": 6.8,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )

    fig, axes = plt.subplots(1, 3, figsize=(10.2, 3.35), gridspec_kw={"width_ratios": [1.18, 1.02, 1.15]})
    fig.subplots_adjust(left=0.06, right=0.99, top=0.84, bottom=0.19, wspace=0.29)

    # -----------------------------------------------------------------------
    # Panel (a): M=64 matched-model restricted mean certification cost
    # -----------------------------------------------------------------------
    ax = axes[0]
    _style_ax(ax)
    cond_order = [("A_indep", "A\n(0, 0)"), ("B_struct", "B\n(.75, 0)"), ("C_stat", "C\n(0, .9)"), ("D_both", "D\n(.75, .9)")]
    pols_a = ["gp_ucb", "kg", "gp_os", "cd_joint"]
    lookup_a = {
        (r["condition"], r["policy"]): r
        for r in main_rows
        if r["beta_mode"] == "posterior_credible"
    }

    x = np.arange(len(cond_order), dtype=np.float64)
    w = 0.19
    offsets = np.linspace(-1.5 * w, 1.5 * w, len(pols_a))

    for idx_p, pol in enumerate(pols_a):
        vals, lo_e, hi_e, certs = [], [], [], []
        for cid, _ in cond_order:
            r = lookup_a[(cid, pol)]
            mu = float(r["restricted_mean"]) / 1000.0
            lo = float(r["rm_ci95_lo"]) / 1000.0
            hi = float(r["rm_ci95_hi"]) / 1000.0
            vals.append(mu)
            lo_e.append(max(0.0, mu - lo))
            hi_e.append(max(0.0, hi - mu))
            certs.append(float(r["cert_pct"]))
        bars = ax.bar(
            x + offsets[idx_p],
            vals,
            width=w * 0.92,
            color=COLORS[pol],
            edgecolor="white",
            linewidth=0.4,
            label=LABELS[pol],
            zorder=3,
        )
        ax.errorbar(
            x + offsets[idx_p],
            vals,
            yerr=[lo_e, hi_e],
            fmt="none",
            ecolor="#111827",
            elinewidth=0.75,
            capsize=1.8,
            capthick=0.7,
            zorder=4,
        )
        # Annotate CD-Joint values and 0% cap marker cleanly above bars
        for bi, bar in enumerate(bars):
            h = bar.get_height()
            if pol == "gp_ucb" and certs[bi] < 5.0:
                ax.text(
                    bar.get_x() + bar.get_width() / 2.0,
                    h + 0.18,
                    "0%",
                    ha="center",
                    va="bottom",
                    fontsize=5.8,
                    color="#4B5563",
                    fontweight="bold",
                )
            elif pol == "cd_joint":
                ax.text(
                    bar.get_x() + bar.get_width() / 2.0,
                    h + hi_e[bi] + 0.22,
                    f"{h:.1f}k",
                    ha="center",
                    va="bottom",
                    fontsize=5.8,
                    color="#0F766E",
                    fontweight="bold",
                )

    ax.axhline(12.0, linestyle="--", linewidth=0.7, color="#9CA3AF", zorder=2)
    ax.set_xticks(x)
    ax.set_xticklabels([lbl for _, lbl in cond_order], fontsize=7.2)
    ax.set_ylabel("Restricted mean evals (×1k)")
    ax.set_ylim(0, 16.0)
    ax.set_yticks([0, 3, 6, 9, 12])
    ax.set_title("(a) Matched-model M=64 (cap 12k)", fontweight="bold", pad=8)
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, 1.02), ncol=2, frameon=False, handlelength=1.0, columnspacing=0.8, fontsize=6.6)

    # -----------------------------------------------------------------------
    # Panel (b): Bayesian root risk vs evaluation budget (M=16 VOI reference)
    # -----------------------------------------------------------------------
    ax = axes[1]
    _style_ax(ax)
    pols_b = ["gp_ucb", "kg", "gp_os", "cd_joint", "bayesian_voi"]
    styles_b = {
        "gp_ucb": ("-", "o", 1.3),
        "kg": ("-", "s", 1.5),
        "gp_os": ("-", "^", 1.4),
        "cd_joint": ("-", "D", 1.7),
        "bayesian_voi": ("--", "v", 1.7),
    }

    # Plot pooled across all 4 conditions (n=160) on M=16 VOI reference study
    for pol in pols_b:
        sub = sorted(
            [r for r in voi_ck if r["beta_mode"] == "posterior_credible" and r["condition"] == "ALL" and r["policy"] == pol],
            key=lambda r: int(r["budget_t"]),
        )
        if not sub:
            continue
        ts = np.array([int(r["budget_t"]) for r in sub], dtype=np.float64)
        mu = np.maximum(1e-4, np.array([float(r["mean_post_risk"]) for r in sub], dtype=np.float64))
        lo = np.maximum(1e-4, np.array([float(r["risk_ci95_lo"]) for r in sub], dtype=np.float64))
        hi = np.maximum(1e-4, np.array([float(r["risk_ci95_hi"]) for r in sub], dtype=np.float64))
        ls, mk, lw = styles_b[pol]
        ax.plot(ts, mu, linestyle=ls, marker=mk, markersize=3.2, linewidth=lw, color=COLORS[pol], label=LABELS[pol], zorder=4)
        ax.fill_between(ts, lo, hi, color=COLORS[pol], alpha=0.12, linewidth=0, zorder=2)

    ax.axhline(0.05, linestyle=":", linewidth=0.9, color="#DC2626", zorder=3)
    ax.text(980, 0.056, r"$\delta=0.05$", ha="right", va="bottom", fontsize=6.5, color="#DC2626")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(9, 1100)
    ax.set_ylim(2e-4, 1.05)
    ax.set_xticks([10, 25, 50, 100, 200, 400, 1000])
    ax.get_xaxis().set_major_formatter(matplotlib.ticker.ScalarFormatter())
    ax.set_xlabel("Evaluation budget $t$")
    ax.set_ylabel(r"Posterior root risk $\min_a q_t(a)$")
    ax.set_title("(b) Bayesian root risk vs. budget (M=16)", fontweight="bold", pad=8)
    ax.legend(loc="lower left", frameon=True, facecolor="white", framealpha=0.88, edgecolor="#E5E7EB", handlelength=1.6)

    # -----------------------------------------------------------------------
    # Panel (c): Cost-sensitive low-valued proxy benchmark (M=5, K=2, d=3)
    # -----------------------------------------------------------------------
    ax = axes[2]
    _style_ax(ax)
    cells = [
        (0.50, 0.25, ".50\nc=.25"),
        (0.50, 1.0, ".50\nc=1"),
        (0.50, 4.0, ".50\nc=4"),
        (0.95, 0.25, ".95\nc=.25"),
        (0.95, 1.0, ".95\nc=1"),
        (0.95, 4.0, ".95\nc=4"),
    ]
    pols_c = ["kg", "cd_joint", "bayesian_voi"]
    lookup_c = {
        (round(float(r["align"]), 2), round(float(r["c_proxy"]), 2), r["policy"]): r
        for r in proxy_rows
        if r["beta_mode"] == "posterior_credible"
    }

    xc = np.arange(len(cells), dtype=np.float64)
    wc = 0.25
    offs_c = np.linspace(-wc, wc, len(pols_c))

    for idx_p, pol in enumerate(pols_c):
        vals, lo_e, hi_e, pfs = [], [], [], []
        for al, cp, _ in cells:
            r = lookup_c[(al, cp, pol)]
            mu = float(r["restricted_mean_cost"])
            lo = float(r["cost_ci95_lo"])
            hi = float(r["cost_ci95_hi"])
            vals.append(mu)
            lo_e.append(max(0.0, mu - lo))
            hi_e.append(max(0.0, hi - mu))
            pfs.append(100.0 * float(r["mean_proxy_arm_frac"]))
        bars = ax.bar(
            xc + offs_c[idx_p],
            vals,
            width=wc * 0.90,
            color=COLORS[pol],
            edgecolor="white",
            linewidth=0.4,
            label=LABELS[pol],
            zorder=3,
        )
        ax.errorbar(
            xc + offs_c[idx_p],
            vals,
            yerr=[lo_e, hi_e],
            fmt="none",
            ecolor="#111827",
            elinewidth=0.7,
            capsize=1.6,
            capthick=0.65,
            zorder=4,
        )
        # Annotate proxy-query allocation % cleanly above bars (zero neighbor overlap)
        if pol in ("cd_joint", "kg"):
            for bi, bar in enumerate(bars):
                h = bar.get_height()
                hi_top = h + hi_e[bi]
                if pol == "kg":
                    txt_y = hi_top * 1.32
                    x_shift = -0.07
                else:
                    # Lift short valley bar labels cleanly above neighboring bars if needed
                    txt_y = max(hi_top * 1.18, 2.35 if bi == 3 else 0.0)
                    if bi == 0:
                        txt_y = 10.6
                    elif bi == 1:
                        txt_y = 19.2
                    elif bi == 2:
                        txt_y = 44.0
                    elif bi == 4:
                        txt_y = 5.4
                    elif bi == 5:
                        txt_y = 15.5
                    x_shift = 0.04
                ax.text(
                    bar.get_x() + bar.get_width() / 2.0 + x_shift,
                    txt_y,
                    f"{pfs[bi]:.0f}%",
                    ha="center",
                    va="bottom",
                    fontsize=5.0,
                    color="#92400E" if pol == "kg" else "#0F766E",
                    fontweight="bold",
                )

    ax.axvline(2.5, linestyle="--", linewidth=0.7, color="#CBD5E1", zorder=2)
    ax.text(1.0, 260, r"$\cos=0.50$", ha="center", va="top", fontsize=6.4, color="#475569", fontweight="bold")
    ax.text(4.0, 260, r"$\cos=0.95$", ha="center", va="top", fontsize=6.4, color="#475569", fontweight="bold")
    ax.set_yscale("log")
    ax.set_xticks(xc)
    ax.set_xticklabels([lbl for _, _, lbl in cells], fontsize=6.5)
    ax.set_ylabel("Total cert. cost (log scale)")
    ax.set_ylim(0.35, 340)
    ax.set_title("(c) Cost-aware proxy (M=5, % proxy)", fontweight="bold", pad=8)
    ax.legend(loc="upper right", bbox_to_anchor=(1.0, 0.90), frameon=True, facecolor="white", framealpha=0.90, edgecolor="#E5E7EB", handlelength=1.0, fontsize=6.3)

    pdf_out = out_dir / "fig_v12_bed_vs_bo.pdf"
    png_out = out_dir / "fig_v12_bed_vs_bo.png"
    fig.savefig(pdf_out, format="pdf")
    fig.savefig(png_out, format="png", dpi=300)
    plt.close(fig)
    print(f"Wrote {pdf_out} and {png_out}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=V12_DIR)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    make_figure(args.data_dir, args.out_dir)


if __name__ == "__main__":
    main()
