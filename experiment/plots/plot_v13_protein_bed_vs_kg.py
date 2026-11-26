"""Generate publication 2x2 figure for v13: Matched Protein BED vs. Correlated KG (GB1 & TmTrpB).

Row 1 (GB1, n=200 paired campaigns) and Row 2 (TmTrpB, n=210 paired campaigns), eps=0.015, delta=0.05:
  - Left column  (Regime A): Matched Bayesian joint credible-ellipsoid stopping (fixed GP prior/kernel).
  - Right column (Regime B): Formal distribution-free Empirical Bernstein stopping (exact shared-support).
Bars show restricted mean simulated assays (capped at 25,000) with 95% bootstrap CIs and exact
certification rates annotated cleanly next to each bar.
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
V13_DIR = ROOT / "results/bayesian_ucd_v1/v13_protein_bed_vs_kg"
DEFAULT_OUT = ROOT / "results/bayesian_ucd_v1/figures"

COLORS = {
    "gp_ucb": "#6B7280",               # slate grey
    "kg": "#D97706",                   # amber / orange
    "gp_root_info_gp": "#2E7D32",      # forest green
    "gp_os": "#2563EB",                # royal blue
    "cd_joint": "#0D9488",             # teal (principal)
    "gp_root_info_df": "#2E7D32",      # forest green (DF-coupled)
    "cd_joint_df_confirm": "#14B8A6",  # light teal (DF-confirmed)
    "kg_df_confirm": "#F59E0B",        # light amber (DF-confirmed)
    "df_os": "#334155",                # dark navy-slate (zero-GP DF baseline)
}

LABELS_A = {
    "gp_ucb": "GP-UCB",
    "kg": "Correlated KG",
    "gp_root_info_gp": "GP-Root-Info",
    "gp_os": "Correlated GP-OS",
    "cd_joint": "CD-Joint",
}

LABELS_B = {
    "gp_ucb": "GP-UCB (GP-only)",
    "kg": "Correlated KG (GP-only)",
    "gp_os": "GP-OS (GP-only)",
    "cd_joint": "CD-Joint (GP-only)",
    "kg_df_confirm": r"KG $\to$ DF-OS",
    "cd_joint_df_confirm": r"CD-Joint $\to$ DF-OS",
    "gp_root_info_df": "GP-Root-Info (DF)",
    "df_os": "DF-OS (no GP)",
}


def _read_csv(path: Path) -> list[dict]:
    with path.open("r", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def _style_ax(ax: plt.Axes) -> None:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_linewidth(0.8)
    ax.spines["bottom"].set_linewidth(0.8)
    ax.tick_params(labelsize=7.4, length=2.8, width=0.7)
    ax.grid(axis="x", linestyle="-", linewidth=0.45, color="#E5E7EB", zorder=0)
    ax.set_axisbelow(True)


def make_figure(data_dir: Path, out_dir: Path, eps: float = 0.015) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = [r for r in _read_csv(data_dir / "v13_protein_summary.csv") if abs(float(r["eps"]) - eps) < 1e-9]
    lookup = {(r["landscape"], r["stopping_regime"], r["method"]): r for r in rows}

    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 8.0,
            "axes.titlesize": 8.4,
            "axes.labelsize": 7.8,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )

    fig, axes = plt.subplots(2, 2, figsize=(9.6, 4.65))
    fig.subplots_adjust(left=0.16, right=0.98, top=0.91, bottom=0.11, wspace=0.45, hspace=0.42)

    methods_a = ["gp_ucb", "kg", "gp_root_info_gp", "gp_os", "cd_joint"]
    methods_b = [
        "gp_ucb",
        "kg",
        "cd_joint",
        "kg_df_confirm",
        "cd_joint_df_confirm",
        "gp_root_info_df",
        "df_os",
    ]

    datasets = [
        ("gb1", r"GB1 ($n=200$)", "a", "b"),
        ("trpb", r"TmTrpB ($n=210$)", "c", "d"),
    ]

    for row_i, (land, dlabel, tag_a, tag_b) in enumerate(datasets):
        # ------------------------------------------------------------------
        # Left panel: Regime A — Matched Bayesian stopping
        # ------------------------------------------------------------------
        ax_a = axes[row_i, 0]
        _style_ax(ax_a)
        y_a = np.arange(len(methods_a), dtype=np.float64)
        vals_a, lo_a, hi_a, certs_a = [], [], [], []
        for m in methods_a:
            r = lookup[(land, "bayes_ellipsoid", m)]
            mu = float(r["restricted_mean"]) / 1000.0
            lo = float(r["rm_ci95_lo"]) / 1000.0
            hi = float(r["rm_ci95_hi"]) / 1000.0
            vals_a.append(mu)
            lo_a.append(max(0.0, mu - lo))
            hi_a.append(max(0.0, hi - mu))
            certs_a.append(100.0 * float(r["cert_rate"]))

        bars = ax_a.barh(
            y_a,
            vals_a,
            height=0.62,
            color=[COLORS[m] for m in methods_a],
            edgecolor="white",
            linewidth=0.5,
            zorder=3,
        )
        ax_a.errorbar(
            vals_a,
            y_a,
            xerr=[lo_a, hi_a],
            fmt="none",
            ecolor="#111827",
            elinewidth=0.85,
            capsize=2.0,
            capthick=0.75,
            zorder=4,
        )
        xmax_a = max(vals_a[i] + hi_a[i] for i in range(len(vals_a)))
        ax_a.set_xlim(0.0, xmax_a * 1.42)
        ax_a.set_yticks(y_a)
        ax_a.set_yticklabels([LABELS_A[m] for m in methods_a])
        ax_a.invert_yaxis()
        ax_a.set_title(f"({tag_a}) {dlabel} — Bayesian stopping", fontweight="bold", fontsize=8.2, pad=5.0)
        if row_i == 1:
            ax_a.set_xlabel("Restricted mean assays ($\\times 10^3$, lower is better)")

        cd_row = lookup[(land, "bayes_ellipsoid", "cd_joint")]
        ratio_kg_cd = float(cd_row["speedup_kg_over_method"])

        for bi, (bar, m) in enumerate(zip(bars, methods_a)):
            x_end = vals_a[bi] + hi_a[bi]
            val_str = f"{vals_a[bi]:.2f}k" if xmax_a < 2.5 else f"{vals_a[bi]:.1f}k"
            cert_str = f" ({certs_a[bi]:.0f}%)" if certs_a[bi] < 99.95 else ""
            if m == "cd_joint":
                txt = f"{val_str}{cert_str}  [{ratio_kg_cd:.2f}$\\times$ vs KG]"
                col = "#0F766E"
                fw = "bold"
            else:
                txt = f"{val_str}{cert_str}"
                col = "#374151"
                fw = "normal"
            ax_a.text(
                x_end + xmax_a * 0.025,
                bar.get_y() + bar.get_height() / 2.0,
                txt,
                va="center",
                ha="left",
                fontsize=6.6,
                color=col,
                fontweight=fw,
            )

        # ------------------------------------------------------------------
        # Right panel: Regime B — Formal distribution-free stopping
        # ------------------------------------------------------------------
        ax_b = axes[row_i, 1]
        _style_ax(ax_b)
        y_b = np.arange(len(methods_b), dtype=np.float64)
        vals_b, lo_b, hi_b, certs_b = [], [], [], []
        for m in methods_b:
            r = lookup[(land, "df_emp_bernstein", m)]
            mu = float(r["restricted_mean"]) / 1000.0
            lo = float(r["rm_ci95_lo"]) / 1000.0
            hi = float(r["rm_ci95_hi"]) / 1000.0
            vals_b.append(mu)
            lo_b.append(max(0.0, mu - lo))
            hi_b.append(max(0.0, hi - mu))
            certs_b.append(100.0 * float(r["cert_rate"]))

        hatches = ["//" if m in ("gp_ucb", "kg", "cd_joint") else "" for m in methods_b]
        bars_b = ax_b.barh(
            y_b,
            vals_b,
            height=0.64,
            color=[COLORS[m] for m in methods_b],
            edgecolor="white",
            linewidth=0.5,
            zorder=3,
        )
        for bar, ht in zip(bars_b, hatches):
            if ht:
                bar.set_hatch(ht)
                bar.set_alpha(0.78)
        ax_b.errorbar(
            vals_b,
            y_b,
            xerr=[lo_b, hi_b],
            fmt="none",
            ecolor="#111827",
            elinewidth=0.85,
            capsize=1.8,
            capthick=0.7,
            zorder=4,
        )
        ax_b.axvline(25.0, color="#DC2626", linestyle="--", linewidth=0.75, alpha=0.65, zorder=2)
        ax_b.axhline(2.5, color="#9CA3AF", linestyle=":", linewidth=0.7, zorder=2)
        ax_b.set_xlim(0.0, 35.5)
        ax_b.set_xticks([0, 5, 10, 15, 20, 25])
        ax_b.set_yticks(y_b)
        ax_b.set_yticklabels([LABELS_B[m] for m in methods_b])
        ax_b.invert_yaxis()
        ax_b.set_title(f"({tag_b}) {dlabel} — Distribution-free stopping", fontweight="bold", fontsize=8.2, pad=5.0)
        if row_i == 1:
            ax_b.set_xlabel("Restricted mean assays ($\\times 10^3$, cap $25$k)")

        for bi, (bar, m) in enumerate(zip(bars_b, methods_b)):
            x_end = vals_b[bi] + hi_b[bi]
            cap_star = "*" if certs_b[bi] < 1.0 else ""
            txt = f"{vals_b[bi]:.1f}k{cap_star} ({certs_b[bi]:.0f}%)"
            fw = "bold" if m in ("gp_root_info_df", "df_os") else "normal"
            col = "#1F2937" if fw == "bold" else "#4B5563"
            ax_b.text(
                x_end + 0.45,
                bar.get_y() + bar.get_height() / 2.0,
                txt,
                va="center",
                ha="left",
                fontsize=6.0,
                color=col,
                fontweight=fw,
                bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.4, "alpha": 0.85},
                zorder=5,
            )

    out_pdf = out_dir / "fig_v13_protein_bed_vs_kg.pdf"
    out_png = out_dir / "fig_v13_protein_bed_vs_kg.png"
    fig.savefig(out_pdf, dpi=300)
    fig.savefig(out_png, dpi=220)
    plt.close(fig)
    print(f"Saved {out_pdf} and {out_png}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=V13_DIR)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--eps", type=float, default=0.015)
    args = ap.parse_args()
    make_figure(args.data_dir, args.out_dir, eps=args.eps)


if __name__ == "__main__":
    main()
