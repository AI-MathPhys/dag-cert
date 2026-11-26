#!/usr/bin/env python3
"""Bundle Johnston et al. (PNAS 2024) 4-site TrpB active-site fitness data into NPZ.

Reads `TrpB4.csv` from the Arnold Lab SSMuLA archive (Zenodo record 15203754 /
DOI 10.5281/zenodo.13910505), filters out nonsense stop-codon variants (`# Stop == 0`),
and writes `joint_root_cert/benchmarks/data/trpb_johnston2024_measured.npz` storing all 159,129
experimentally measured 4-site TmTrpB variants across active-site residues
V183, F184, V227, and S228 (parent `VFVS` fitness = 0.408074, global max `AIKG` = 1.0).
"""
from __future__ import annotations

import argparse
from pathlib import Path
import tarfile
import tempfile

import numpy as np
import pandas as pd


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = REPO_ROOT / "joint_root_cert" / "benchmarks" / "data" / "trpb_johnston2024_measured.npz"
ZENODO_TAR_URL = "https://zenodo.org/api/records/15203754/files/data.tar.gz/content"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv-path", type=Path, default=None)
    parser.add_argument("--tar-path", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()

    if args.csv_path is not None and args.csv_path.is_file():
        df = pd.read_csv(args.csv_path, usecols=["AAs", "# Stop", "fitness"])
    else:
        tar_path = args.tar_path
        if tar_path is None or not tar_path.is_file():
            import requests

            tar_path = Path(tempfile.gettempdir()) / "ssmula_data.tar.gz"
            print(f"Downloading Johnston et al. (2024) SSMuLA archive from {ZENODO_TAR_URL} ...", flush=True)
            r = requests.get(ZENODO_TAR_URL, timeout=180)
            r.raise_for_status()
            tar_path.write_bytes(r.content)
        with tarfile.open(tar_path, "r:gz") as tf:
            member = tf.getmember("data/TrpB/fitness_landscape/TrpB4.csv")
            with tf.extractfile(member) as fh:
                assert fh is not None
                df = pd.read_csv(fh, usecols=["AAs", "# Stop", "fitness"])

    df = df[df["# Stop"] == 0].sort_values("AAs").reset_index(drop=True)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        args.out,
        variants=df["AAs"].to_numpy(dtype="U4"),
        fitness=np.clip(df["fitness"].to_numpy(dtype=np.float32), 0.0, 1.0),
    )
    print(
        f"Saved {args.out} ({args.out.stat().st_size / 1024:.1f} KiB): "
        f"{len(df)} stop-free TrpB variants, max fitness={df['fitness'].max():.6f}"
    )


if __name__ == "__main__":
    main()
