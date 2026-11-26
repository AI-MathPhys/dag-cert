#!/usr/bin/env python3
"""Bundle Wu et al. (eLife 2016) 4-site GB1 empirical fitness data into compact NPZ.

Reads the public FLIP / Wu et al. (2016) `four_mutations_full_data.csv.zip` archive
(149,361 experimentally measured 4-site GB1 variants across positions V39, D40, G41, V54)
and writes `dagcert/benchmarks/data/gb1_wu2016_measured.npz` storing:
  - variants: U4 array of 149,361 4-letter amino-acid strings
  - fitness:  float32 array of experimental binding fitness scores (WT VDGV = 1.0, max = 8.761966)
  - count_in: int32 array of input sequencing read counts
  - count_sel: int32 array of selected sequencing read counts
"""
from __future__ import annotations

import argparse
from pathlib import Path
import tempfile
import zipfile
import numpy as np
import pandas as pd

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = REPO_ROOT / "dagcert" / "benchmarks" / "data" / "gb1_wu2016_measured.npz"
FLIP_URL = "https://raw.githubusercontent.com/J-SNACKKB/FLIP/main/splits/gb1/four_mutations_full_data.csv.zip"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zip-path", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()

    zip_path = args.zip_path
    if zip_path is None or not zip_path.exists():
        import requests
        zip_path = Path(tempfile.gettempdir()) / "gb1_flip_wu2016.zip"
        print(f"Downloading Wu et al. (2016) GB1 dataset from {FLIP_URL} ...", flush=True)
        r = requests.get(FLIP_URL, timeout=60)
        r.raise_for_status()
        zip_path.write_bytes(r.content)

    with zipfile.ZipFile(zip_path) as zf:
        with zf.open(zf.namelist()[0]) as handle:
            df = pd.read_csv(
                handle,
                usecols=["Variants", "Count input", "Count selected", "Fitness"],
                low_memory=False,
            )

    df = df.sort_values("Variants").reset_index(drop=True)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        args.out,
        variants=df["Variants"].to_numpy(dtype="U4"),
        fitness=df["Fitness"].to_numpy(dtype=np.float32),
        count_in=df["Count input"].to_numpy(dtype=np.int32),
        count_sel=df["Count selected"].to_numpy(dtype=np.int32),
    )
    print(
        f"Saved {args.out} ({args.out.stat().st_size / 1024:.1f} KiB): "
        f"{len(df)} variants, max fitness={df['Fitness'].max():.6f}"
    )


if __name__ == "__main__":
    main()
