"""Shared ICLR figure style for every manuscript figure.

All figures are drawn at their final printed size (the ICLR text block is 5.5 in
wide), so the font sizes below are the sizes that appear on the page: no
down-scaling in LaTeX. Text is set in Arial (DejaVu Sans where Arial is missing).

Colour follows the entity, not its position in a panel, using the orange/purple
palette of the LogiCA figures: our method is burnt orange, its variants light
orange, competing methods are shades of purple, and distribution-free reference
baselines are grey. Every series is also identified by an axis label, a marker
shape, or a legend entry, never by colour alone.
"""
from __future__ import annotations

from typing import Iterable, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.axes import Axes
from matplotlib.figure import Figure

TEXT_WIDTH = 5.5  # ICLR text block, inches

# Font sizes are multiplied by FONT_SCALE and figure heights by HEIGHT_SCALE, so the
# whole set can be enlarged in one place.
FONT_SCALE = 1.2
HEIGHT_SCALE = 1.12

# Entity colours (names are historical roles, not hues).
OURS = "#C8501E"  # CD-Joint and its calibrated / unknown-variance variants (burnt orange)
BLUE = "#563D8C"  # correlated KG; dense (V33) reference implementation (deep purple)
ORANGE = "#9A63DB"  # GP-OS and other single-mechanism ablations (mid purple)
PINK = "#EBA06B"  # hybrid / tracking variants of our method (light orange)
BAD = "#D4B9EA"  # deliberately invalid or nominal (uncalibrated) controls (light purple)
REF = "#8C8B96"  # distribution-free reference baselines (grey)
EDGE = "#2E1F4F"  # outline of bars and patches
INK = "#1A1A1A"
MUTED = "#55535F"
GRID = "#E6E4EA"
AXIS = "#1A1A1A"


def fs(size: float) -> float:
    """Scale a hard-coded font size."""
    return size * FONT_SCALE


def setup() -> None:
    plt.rcParams.update(
        {
            "font.family": "sans-serif",
            "font.sans-serif": ["Arial", "Helvetica", "Liberation Sans", "DejaVu Sans"],
            "mathtext.fontset": "custom",
            "mathtext.rm": "Arial",
            "mathtext.it": "Arial:italic",
            "mathtext.bf": "Arial:bold",
            "mathtext.sf": "Arial",
            "mathtext.fallback": "stixsans",
            "font.size": fs(7.5),
            "axes.titlesize": fs(7.8),
            "axes.titleweight": "bold",
            "axes.labelsize": fs(7.5),
            "xtick.labelsize": fs(7.0),
            "ytick.labelsize": fs(7.0),
            "legend.fontsize": fs(7.0),
            "text.color": INK,
            "axes.labelcolor": INK,
            "axes.edgecolor": AXIS,
            "xtick.color": AXIS,
            "ytick.color": AXIS,
            "xtick.labelcolor": INK,
            "ytick.labelcolor": INK,
            "axes.linewidth": 0.8,
            "xtick.major.width": 0.8,
            "ytick.major.width": 0.8,
            "xtick.major.size": 3.0,
            "ytick.major.size": 3.0,
            "xtick.minor.size": 1.5,
            "ytick.minor.size": 1.5,
            "xtick.minor.width": 0.4,
            "ytick.minor.width": 0.4,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.axisbelow": True,
            "lines.linewidth": 1.8,
            "lines.markersize": 5.0,
            "patch.edgecolor": EDGE,
            "legend.frameon": False,
            "legend.handlelength": 1.3,
            "legend.handletextpad": 0.45,
            "legend.columnspacing": 1.2,
            "legend.borderaxespad": 0.2,
            "hatch.linewidth": 0.5,
            "figure.dpi": 150,
            "savefig.dpi": 300,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
            "figure.constrained_layout.use": True,
            "figure.constrained_layout.h_pad": 0.03,
            "figure.constrained_layout.w_pad": 0.03,
            "figure.constrained_layout.wspace": 0.06,
        }
    )


def figure(ncols: int = 1, height: float = 1.85, width: float = TEXT_WIDTH, scale_height: bool = True,
           **kw) -> tuple[Figure, list[Axes]]:
    """A one-row figure; main-text figures pass scale_height=False to keep the page budget."""
    fig, axes = plt.subplots(1, ncols, figsize=(width, height * (HEIGHT_SCALE if scale_height else 1.0)), **kw)
    axes = [axes] if ncols == 1 else list(axes)
    return fig, axes


def panel(ax: Axes, letter: str | None, title: str) -> None:
    """Left-aligned bold panel heading, e.g. "(a) Title"."""
    head = f"({letter}) {title}" if letter else title
    ax.set_title(head, loc="left", pad=5.0)


def ygrid(ax: Axes) -> None:
    ax.grid(axis="y", color=GRID, linewidth=0.7)


def xgrid(ax: Axes) -> None:
    ax.grid(axis="x", color=GRID, linewidth=0.7)


def label(ax: Axes, x: float, y: float, text: str, *, dy: float = 2.0, dx: float = 0.0, ha: str = "center",
          va: str = "bottom", size: float = 6.6, color: str = INK, weight: str = "normal") -> None:
    ax.annotate(text, (x, y), xytext=(dx, dy), textcoords="offset points", ha=ha, va=va,
                fontsize=fs(size), color=color, fontweight=weight, linespacing=1.05, zorder=6,
                bbox=dict(boxstyle="square,pad=0.08", facecolor="white", edgecolor="none", alpha=0.85))


def bars(ax: Axes, xs: Sequence[float], vals: Sequence[float], colors: Sequence[str] | str, *, width: float = 0.6,
         lo: Sequence[float] | None = None, hi: Sequence[float] | None = None,
         labels: Iterable[str] | None = None, label_size: float = 6.6, legend: str | None = None,
         hatch: str | None = None):
    """Vertical bars from a zero baseline with optional asymmetric intervals and value labels."""
    cont = ax.bar(xs, vals, width=width, color=colors, edgecolor=EDGE, linewidth=0.6, zorder=3, label=legend)
    if hatch:
        for b in cont:
            b.set_hatch(hatch)
            b.set_edgecolor("white")
    tops = list(vals)
    if lo is not None and hi is not None:
        err = [[max(0.0, v - a) for v, a in zip(vals, lo)], [max(0.0, b - v) for v, b in zip(vals, hi)]]
        ax.errorbar(xs, vals, yerr=err, fmt="none", ecolor=INK, elinewidth=0.8, capsize=2.0, capthick=0.8, zorder=4)
        tops = [max(v, b) for v, b in zip(vals, hi)]
    if labels is not None:
        for x, t, s in zip(xs, tops, labels):
            if s:
                label(ax, x, t, s, size=label_size)
    return cont


def reference(ax: Axes, y: float, text: str, *, x: float = 0.99, va: str = "bottom", color: str = MUTED,
              dy: float = 1.5) -> None:
    """Dashed horizontal reference level with a right-aligned in-plot label."""
    ax.axhline(y, color=color, linestyle=(0, (4, 2.5)), linewidth=0.9, zorder=2)
    ax.annotate(text, (x, y), xycoords=("axes fraction", "data"), xytext=(0, dy if va == "bottom" else -dy),
                textcoords="offset points", ha="right", va=va, fontsize=fs(6.4), color=color, zorder=6)


def legend_below(fig: Figure, handles, labels, ncol: int | None = None) -> None:
    fig.legend(handles, labels, loc="outside lower center", ncol=ncol or len(labels))


def save(fig: Figure, path) -> None:
    fig.savefig(path)
    plt.close(fig)
