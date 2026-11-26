"""Backward-compatible entry point.

All manuscript figures (Figures 2-15, including the seven `supp_*.pdf` files this
script used to draw) are now generated in one shared style by
`plot_manuscript_figures.py`; this wrapper simply delegates to it.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from plot_manuscript_figures import generate_all, main  # noqa: E402,F401

if __name__ == "__main__":
    main()
