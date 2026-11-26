"""Agentic Workflows: Offline WorFBench 81-configuration factorial & overlap/depth controls.

Reproduces Table 5 (offline rows) and Appendix I Tables 35--36 & 48 by delegating to the
paired WorFBench sections of `exp_real_world_applications` (`exp12`) and
`exp_real_world_validation` (`exp13`).
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def _run(rel_script: str, extra: list[str]) -> None:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT)
    subprocess.run([sys.executable, "-B", str(ROOT / rel_script), *extra], cwd=ROOT, env=env, check=True)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=None)
    args = ap.parse_args()

    extra: list[str] = []
    if args.smoke:
        extra.append("--smoke")
    if args.summarize_only:
        extra.append("--summarize-only")

    for tag, script in (
        ("exp12_offline_factorial", "experiment/protein_engineering/exp_real_world_applications.py"),
        ("exp13_overlap_and_live", "experiment/protein_engineering/exp_real_world_validation.py"),
    ):
        call_args = list(extra)
        if args.out_dir is not None:
            call_args.extend(["--out", str(args.out_dir / tag)])
        _run(script, call_args)


if __name__ == "__main__":
    main()
