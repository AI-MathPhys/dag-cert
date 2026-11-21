#!/usr/bin/env python3
"""Fetch and rebuild external benchmark datasets & Hugging Face models from public sources.

All compact preprocessed benchmark archives (`dag_mcts/data/*.npz`, 1.7 MB total, and
`appendix/data/samegame/StandardTestset.txt`) are already bundled in this repository so
all offline verification, tests, and CPU experiments run out of the box without network
access. Use this script to:

  1. Verify bundled data archives & check optional Hugging Face model cache (`--check`).
  2. Freshly download raw upstream datasets from their original public repositories and
     rebuild the compact `.npz` files from scratch:
       - GB1 (Wu et al., eLife 2016) via FLIP GitHub (`--proteins`)
       - TmTrpB (Johnston et al., PNAS 2024) via Arnold Lab SSMuLA Zenodo record 15203754 (`--proteins`)
       - WorFBench gold trajectories (4 domains) via `zjunlp/WorfBench` GitHub (`--worfbench-tasks`)
  3. Pre-download `Qwen/Qwen3-0.6B` and `Qwen/Qwen3-Embedding-0.6B` from Hugging Face Hub
     for running fresh uncached live LLM certification suites (`--models`).
  4. Optionally regenerate `dag_mcts/data/worfbench_qwen3_81x64.npz` and
     `dag_mcts/data/worfbench_qwen3_test_81x32.npz` from scratch via local Qwen3 inference
     (`--rebuild-worfbench`; requires `requirements-live-llm.txt`).

Examples:
    python scripts/fetch_data.py --check
    python scripts/fetch_data.py --proteins --worfbench-tasks
    python scripts/fetch_data.py --all
    python scripts/fetch_data.py --proteins --out-dir build/rebuilt_data
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT / "dag_mcts" / "data"
WORFBENCH_RAW_DIR = DATA_DIR / "worfbench_raw"
SAMEGAME_PATH = ROOT / "appendix" / "data" / "samegame" / "StandardTestset.txt"

WORFBENCH_DOMAINS = ("toolbench", "toolalpaca", "seal_tools", "webshop")
HF_MODELS = ("Qwen/Qwen3-0.6B", "Qwen/Qwen3-Embedding-0.6B")

BUNDLED_FILES: tuple[tuple[str, Path, str], ...] = (
    ("GB1 measured fitness (Wu et al. 2016)", DATA_DIR / "gb1_wu2016_measured.npz", "FLIP GitHub"),
    ("TmTrpB measured fitness (Johnston et al. 2024)", DATA_DIR / "trpb_johnston2024_measured.npz", "Zenodo 15203754"),
    ("WorFBench Qwen3-0.6B cal matrix (81x64)", DATA_DIR / "worfbench_qwen3_81x64.npz", "zjunlp/WorfBench + Qwen3-0.6B"),
    ("WorFBench Qwen3-0.6B test matrix (81x32)", DATA_DIR / "worfbench_qwen3_test_81x32.npz", "zjunlp/WorfBench + Qwen3-0.6B"),
    ("SameGame 20-board StandardTestset", SAMEGAME_PATH, "Bundled v1 archive"),
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_py(args: list[str]) -> None:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT)
    env.pop("PYTHONSAFEPATH", None)
    subprocess.run([sys.executable, "-B", *args], cwd=ROOT, env=env, check=True)


def check_status() -> int:
    print("=== Bundled Benchmark Datasets ===")
    missing = 0
    for label, path, source in BUNDLED_FILES:
        if path.is_file():
            kb = path.stat().st_size / 1024.0
            print(f"  [OK]      {path.relative_to(ROOT)} ({kb:6.1f} KiB, sha256={_sha256(path)[:12]}...)  [{label}]")
        else:
            missing += 1
            print(f"  [MISSING] {path.relative_to(ROOT)}  [{label}; source: {source}]")

    print("\n=== Optional Raw WorFBench Trajectories (for live LLM suites) ===")
    for dom in WORFBENCH_DOMAINS:
        p = WORFBENCH_RAW_DIR / f"{dom}_graph_eval.json"
        if p.is_file():
            n = len(json.loads(p.read_text(encoding="utf-8")))
            print(f"  [CACHED]  {p.relative_to(ROOT)} ({n} tasks)")
        else:
            print(f"  [REMOTE]  {p.relative_to(ROOT)} (auto-fetched on demand, or run --worfbench-tasks)")

    print("\n=== Optional Hugging Face Models (for live Qwen3-0.6B suites v8_5 / v10_3 / v11_2) ===")
    try:
        from huggingface_hub import try_to_load_from_cache

        for repo_id in HF_MODELS:
            hit = try_to_load_from_cache(repo_id=repo_id, filename="config.json")
            status = "[CACHED]" if isinstance(hit, str) and Path(hit).is_file() else "[NOT CACHED]"
            print(f"  {status:12s} {repo_id}")
    except ImportError:
        print("  [SKIP]    huggingface_hub not installed (install requirements-live-llm.txt for live LLM suites)")

    print("\n=== Optional Native C++17 Compiler (for exp7, v9/v10 C++17 B&B, & SameGame) ===")
    import shutil

    cxx = os.environ.get("CXX") or shutil.which("g++") or shutil.which("clang++")
    if cxx:
        print(f"  [OK]      {cxx}")
    else:
        print("  [MISSING] No g++/clang++ found on PATH (Python-only paths still work)")

    return 1 if missing else 0


def fetch_proteins(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    gb1_out = out_dir / "gb1_wu2016_measured.npz"
    trpb_out = out_dir / "trpb_johnston2024_measured.npz"
    print(f"[1/2] Fetching & building GB1 (Wu et al. 2016) -> {gb1_out}")
    _run_py(["paper/build_gb1_dataset.py", "--out", str(gb1_out)])
    print(f"[2/2] Fetching & building TmTrpB (Johnston et al. 2024) -> {trpb_out}")
    _run_py(["paper/build_trpb_dataset.py", "--out", str(trpb_out)])


def fetch_worfbench_tasks() -> None:
    import requests

    WORFBENCH_RAW_DIR.mkdir(parents=True, exist_ok=True)
    for dom in WORFBENCH_DOMAINS:
        url = f"https://raw.githubusercontent.com/zjunlp/WorfBench/main/gold_traj/{dom}/graph_eval.json"
        dest = WORFBENCH_RAW_DIR / f"{dom}_graph_eval.json"
        print(f"Downloading WorFBench {dom} trajectories from {url} ...")
        resp = requests.get(url, timeout=60)
        resp.raise_for_status()
        items = resp.json()
        dest.write_text(json.dumps(items), encoding="utf-8")
        print(f"  Saved {dest.relative_to(ROOT)} ({len(items)} tasks)")


def fetch_hf_models() -> None:
    try:
        from huggingface_hub import snapshot_download
    except ImportError as exc:
        raise SystemExit(
            "Missing `huggingface_hub`. Install live-LLM dependencies first:\n"
            "  python -m pip install -r requirements-live-llm.txt"
        ) from exc

    for repo_id in HF_MODELS:
        print(f"Downloading Hugging Face model `{repo_id}` into local HF cache ...")
        local_dir = snapshot_download(repo_id=repo_id)
        print(f"  Cached at {local_dir}")


def rebuild_worfbench_matrices() -> None:
    print("[1/2] Rebuilding WorFBench 81x64 calibration matrix via Qwen3-0.6B ...")
    _run_py(["paper/build_worfbench_llm_matrix.py"])
    print("[2/2] Rebuilding WorFBench 81x32 unseen test matrix via Qwen3-0.6B ...")
    _run_py(["paper/build_worfbench_test_and_live.py", "--phase1-only"])


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--check", action="store_true", help="Verify bundled datasets, HF cache, and C++17 compiler")
    ap.add_argument("--proteins", action="store_true", help="Download raw GB1 & TmTrpB data and rebuild .npz files")
    ap.add_argument("--worfbench-tasks", action="store_true", help="Download raw 4-domain WorFBench gold trajectory JSONs")
    ap.add_argument("--models", action="store_true", help="Pre-download Qwen3-0.6B & Qwen3-Embedding-0.6B from Hugging Face")
    ap.add_argument(
        "--rebuild-worfbench",
        action="store_true",
        help="Re-run Qwen3-0.6B inference to regenerate dag_mcts/data/worfbench_qwen3_*.npz (slow on CPU)",
    )
    ap.add_argument(
        "--all",
        action="store_true",
        help="Run --proteins, --worfbench-tasks, and --models (all external downloads)",
    )
    ap.add_argument(
        "--out-dir",
        type=Path,
        default=DATA_DIR,
        help=f"Output directory for rebuilt protein .npz files (default: {DATA_DIR.relative_to(ROOT)})",
    )
    args = ap.parse_args()

    if not any((args.check, args.proteins, args.worfbench_tasks, args.models, args.rebuild_worfbench, args.all)):
        ap.print_help()
        print()
        raise SystemExit(check_status())

    if args.all or args.proteins:
        fetch_proteins(args.out_dir)
    if args.all or args.worfbench_tasks:
        fetch_worfbench_tasks()
    if args.all or args.models:
        fetch_hf_models()
    if args.rebuild_worfbench:
        rebuild_worfbench_matrices()
    if args.check:
        raise SystemExit(check_status())


if __name__ == "__main__":
    main()
