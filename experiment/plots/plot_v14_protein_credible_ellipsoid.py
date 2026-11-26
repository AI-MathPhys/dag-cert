"""Generate publication 2x3 figure for v14: Proper Joint Gaussian Credible-Ellipsoid &
Valid Anytime Direct Posterior-Risk Stopping on Real Protein Landscapes (GB1 & TmTrpB).

Row 1: GB1 (n=200 paired campaigns, mean contrast rank r=486.1, beta_0.95=23.18).
Row 2: TmTrpB (n=210 paired campaigns, mean contrast rank r=582.3, beta_0.95=25.29).
Columns:
  - Col 1 (a, d): Stopping-rule sensitivity of restricted mean assays (x10^3, cap 25k) across
                  Conditions A (nominal radius), B (proper chi2_{r,0.95}), C (proper chi2_{r,0.90}),
                  and D (formal DF Empirical Bernstein, unmodified GP acquisitions + DF-OS marker).
  - Col 2 (b, e): Valid anytime union-bound direct posterior-risk stopping (Condition E,
                  delta_post=0.04, eta=0.01, N_MC=4096): restricted mean assays with observed
                  real-landscape decision error counts & rates annotated directly.
  - Col 3 (c, f): Empirical coverage audit comparing joint contrast-ellipsoid coverage of mu*
                  (0% under A_orig vs. 46-84% under proper chi2_{r,0.95}, exposing real-data GP
                  misspecification) against actual root-decision accuracy (<= eps).
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
V14_DIR = ROOT / "results/bayesian_ucd_v1/v14_protein_credible_ellipsoid"
DEFAULT_OUT = ROOT / "results/bayesian_ucd_v1/figures"

COLORS = {
    "kg": "#D97706",        # amber / orange
    "gp_os": "#2563EB",     # royal blue
    "cd_joint": "#0D9488",  # teal (principal)
    "df_os": "#334155",     # dark slate
}

METHOD_LABELS = {
    "kg": "Correlated KG",
    "gp_os": "Correlated GP-OS",
    "cd_joint": "CD-Joint",
}


def _read_csv(path: Path) -> list[dict]:
    with path.open("r", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def _style_ax(ax: plt.Axes) -> None:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_linewidth(0.8)
    ax.spines["bottom"].set_linewidth(0.8)
    ax.tick_params(labelsize=7.1, length=2.6, width=0.7)
    ax.grid(axis="x", linestyle="-", linewidth=0.45, color="#E5E7EB", zorder=0)
    ax.set_axisbelow(True)


def make_figure(data_dir: Path, out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = _read_csv(data_dir / "v14_protein_credible_summary.csv")
    lookup = {(r["landscape"], r["condition"], r["method"]): r for r in rows}

    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 7.6,
            "axes.titlesize": 8.0,
            "axes.labelsize": 7.4,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )

    fig, axes = plt.subplots(2, 3, figsize=(11.2, 5.15), gridspec_kw={"width_ratios": [1.55, 1.0, 1.05]})
    fig.subplots_adjust(left=0.105, right=0.985, top=0.875, bottom=0.105, wspace=0.35, hspace=0.40)

    methods = ("kg", "gp_os", "cd_joint")
    conds_col1 = (
        ("A_orig", "A: Nominal\n(v13)"),
        ("B_chi95", r"B: $\chi^2_{r,.95}$" + "\n(matched)"),
        ("C_chi90", r"C: $\chi^2_{r,.90}$" + "\n(matched)"),
        ("D_df_eb", "D: Formal DF\n(GP-only)"),
    )
    datasets = (
        ("gb1", r"GB1 ($n=200$, $\bar{r}=486$)", ("a", "b", "c")),
        ("trpb", r"TmTrpB ($n=210$, $\bar{r}=582$)", ("d", "e", "f")),
    )

    for row_i, (land, dlabel, tags) in enumerate(datasets):
        # ------------------------------------------------------------------
        # Col 1: Ellipsoid & DF stopping sensitivity (A, B, C, D)
        # ------------------------------------------------------------------
        ax1 = axes[row_i, 0]
        _style_ax(ax1)
        n_c = len(conds_col1)
        group_y = np.arange(n_c, dtype=np.float64) * 1.15
        offsets = (-0.28, 0.0, 0.28)
        bar_h = 0.25

        for mi, m in enumerate(methods):
            ys = group_y + offsets[mi]
            vals, lo, hi, certs = [], [], [], []
            for cname, _ in conds_col1:
                r = lookup[(land, cname, m)]
                mu = float(r["restricted_mean"]) / 1000.0
                ci_l = float(r["rm_ci95_lo"]) / 1000.0
                ci_h = float(r["rm_ci95_hi"]) / 1000.0
                vals.append(mu)
                lo.append(max(0.0, mu - ci_l))
                hi.append(max(0.0, ci_h - mu))
                certs.append(100.0 * float(r["cert_rate"]))

            bars = ax1.barh(
                ys,
                vals,
                height=bar_h,
                color=COLORS[m],
                edgecolor="white",
                linewidth=0.45,
                label=METHOD_LABELS[m] if row_i == 0 else None,
                zorder=3,
            )
            # Hatch the unmodified GP-only D_df_eb bar for visual consistency with v13
            bars[-1].set_hatch("//")
            bars[-1].set_alpha(0.76)

            ax1.errorbar(
                vals,
                ys,
                xerr=[lo, hi],
                fmt="none",
                ecolor="#111827",
                elinewidth=0.75,
                capsize=1.4,
                capthick=0.65,
                zorder=4,
            )

            for ci_idx, (bar, val, h_err, cert) in enumerate(zip(bars, vals, hi, certs)):
                x_end = val + h_err
                cname = conds_col1[ci_idx][0]
                cap_s = "*" if cert < 0.5 else ""
                val_txt = f"{val:.2f}k" if val < 1.0 else f"{val:.1f}k"
                cert_txt = f" ({cert:.0f}%)" if cert < 99.95 else ""
                extra = ""
                if m == "cd_joint" and cname in ("A_orig", "B_chi95"):
                    sp = float(lookup[(land, cname, "cd_joint")]["speedup_kg_over_method"])
                    extra = f" [{sp:.2f}x]"
                ax1.text(
                    x_end + 0.35,
                    bar.get_y() + bar.get_height() / 2.0,
                    f"{val_txt}{cap_s}{cert_txt}{extra}",
                    va="center",
                    ha="left",
                    fontsize=5.65,
                    color="#0F766E" if (m == "cd_joint" and cname != "D_df_eb") else "#374151",
                    fontweight="bold" if (m == "cd_joint" and cname in ("A_orig", "B_chi95")) else "normal",
                    bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.35, "alpha": 0.85},
                    zorder=5,
                )

        # Reference marker for zero-GP DF-OS in Condition D row
        dfos_mu = float(lookup[(land, "D_df_eb", "df_os")]["restricted_mean"]) / 1000.0
        ax1.plot(
            [dfos_mu],
            [group_y[-1]],
            marker="D",
            markersize=4.5,
            color=COLORS["df_os"],
            markeredgecolor="white",
            markeredgewidth=0.5,
            linestyle="none",
            label="DF-OS (no GP, 100%)" if row_i == 0 else None,
            zorder=6,
        )

        ax1.axvline(25.0, color="#DC2626", linestyle="--", linewidth=0.7, alpha=0.65, zorder=2)
        ax1.set_xlim(0.0, 36.5)
        ax1.set_xticks([0, 5, 10, 15, 20, 25])
        ax1.set_yticks(group_y)
        ax1.set_yticklabels([lbl for _, lbl in conds_col1], fontsize=6.8)
        ax1.invert_yaxis()
        ax1.set_title(f"({tags[0]}) {dlabel} — Ellipsoid & DF stopping", fontweight="bold", pad=5.0)
        if row_i == 1:
            ax1.set_xlabel(r"Restricted mean assays ($\times 10^3$, cap $25$k; lower better)")

        # ------------------------------------------------------------------
        # Col 2: Condition E — Valid Anytime Direct Posterior-Risk Stopping
        # ------------------------------------------------------------------
        ax2 = axes[row_i, 1]
        _style_ax(ax2)
        y2 = np.arange(len(methods), dtype=np.float64)
        v2, lo2, hi2, errs2, n2 = [], [], [], [], []
        for m in methods:
            r = lookup[(land, "E_postrisk", m)]
            mu = float(r["restricted_mean"])
            v2.append(mu)
            lo2.append(max(0.0, mu - float(r["rm_ci95_lo"])))
            hi2.append(max(0.0, float(r["rm_ci95_hi"]) - mu))
            errs2.append(int(r["false_certs"]))
            n2.append(int(r["runs"]))

        bars2 = ax2.barh(
            y2,
            v2,
            height=0.56,
            color=[COLORS[m] for m in methods],
            edgecolor="white",
            linewidth=0.5,
            zorder=3,
        )
        ax2.errorbar(
            v2,
            y2,
            xerr=[lo2, hi2],
            fmt="none",
            ecolor="#111827",
            elinewidth=0.8,
            capsize=1.8,
            capthick=0.7,
            zorder=4,
        )
        xmax2 = max(v2[i] + hi2[i] for i in range(len(methods)))
        ax2.set_xlim(0.0, xmax2 * 1.98)
        ax2.set_yticks(y2)
        ax2.set_yticklabels(["KG", "GP-OS", "CD-Joint"], fontsize=7.0)
        ax2.invert_yaxis()
        ax2.set_title(f"({tags[1]}) Cond. E: Direct post.-risk (100% cert.)", fontweight="bold", pad=5.0)
        if row_i == 1:
            ax2.set_xlabel(r"Restricted mean assays (frozen traj., $\delta_{\rm post}=.04$)")

        for bar, val, h_err, n_err, n_tot in zip(bars2, v2, hi2, errs2, n2):
            pct = 100.0 * n_err / n_tot
            ax2.text(
                val + h_err + xmax2 * 0.03,
                bar.get_y() + bar.get_height() / 2.0,
                f"{val:.0f} ({n_err}/{n_tot} err, {pct:.1f}%)",
                va="center",
                ha="left",
                fontsize=6.0,
                color="#B91C1C" if pct > 4.95 else "#374151",
                fontweight="bold" if pct > 4.95 else "normal",
                zorder=5,
            )

        # ------------------------------------------------------------------
        # Col 3: Empirical Coverage Audit (Joint Ellipsoid vs Decision Acc.)
        # ------------------------------------------------------------------
        ax3 = axes[row_i, 2]
        _style_ax(ax3)
        cov_conds = (
            ("A_orig", "A: Nom.\n(joint)"),
            ("B_chi95", r"B: $\chi^2_{.95}$" + "\n(joint)"),
            ("C_chi90", r"C: $\chi^2_{.90}$" + "\n(joint)"),
            ("E_postrisk", "E: Risk\n(dec. ok)"),
        )
        y3 = np.arange(len(cov_conds), dtype=np.float64) * 1.12
        for mi, m in enumerate(methods):
            ys3 = y3 + offsets[mi]
            cvals = []
            for cname, _ in cov_conds:
                r = lookup[(land, cname, m)]
                if cname == "E_postrisk":
                    cvals.append(100.0 * float(r["decision_eps_ok_rate"]))
                else:
                    cvals.append(100.0 * float(r["joint_contrast_cov"]))
            bars3 = ax3.barh(
                ys3,
                cvals,
                height=bar_h,
                color=COLORS[m],
                edgecolor="white",
                linewidth=0.45,
                zorder=3,
            )
            bars3[-1].set_hatch("..")
            for bar, cv in zip(bars3, cvals):
                ax3.text(
                    cv + 1.8,
                    bar.get_y() + bar.get_height() / 2.0,
                    f"{cv:.1f}%" if cv > 0 else "0%",
                    va="center",
                    ha="left",
                    fontsize=5.6,
                    color="#374151",
                    bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.25, "alpha": 0.85},
                    zorder=5,
                )

        ax3.axvline(95.0, color="#DC2626", linestyle="--", linewidth=0.75, alpha=0.7, zorder=2)
        ax3.text(94.0, -0.45, "95%", color="#DC2626", fontsize=5.8, ha="right", va="bottom", fontweight="bold")
        ax3.set_xlim(0.0, 124.0)
        ax3.set_xticks([0, 25, 50, 75, 100])
        ax3.set_yticks(y3)
        ax3.set_yticklabels([lbl for _, lbl in cov_conds], fontsize=6.7)
        ax3.invert_yaxis()
        ax3.set_title(f"({tags[2]}) Empirical coverage vs. 95% nominal", fontweight="bold", pad=5.0)
        if row_i == 1:
            ax3.set_xlabel(r"Empirical rate (%): joint $\mu^*$ or $r_{\mu^*}\leq\varepsilon$")

    handles, labels = axes[0, 0].get_legend_handles_labels()
    # Ensure bar policies appear first, followed by DF-OS diamond marker
    order = [i for i, lbl in enumerate(labels) if not lbl.startswith("DF-OS")] + [
        i for i, lbl in enumerate(labels) if lbl.startswith("DF-OS")
    ]
    fig.legend(
        [handles[i] for i in order],
        [labels[i] for i in order],
        loc="upper center",
        bbox_to_anchor=(0.52, 0.985),
        ncol=4,
        frameon=False,
        fontsize=7.6,
        handlelength=1.4,
        columnspacing=1.6,
    )

    out_pdf = out_dir / "fig_v14_protein_credible_ellipsoid.pdf"
    out_png = out_dir / "fig_v14_protein_credible_ellipsoid.png"
    fig.savefig(out_pdf, dpi=300)
    fig.savefig(out_png, dpi=220)
    plt.close(fig)
    print(f"Saved {out_pdf} and {out_png}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data-dir", type=Path, default=V14_DIR)
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    make_figure(args.data_dir, args.out_dir)


if __name__ == "__main__":
    main()
