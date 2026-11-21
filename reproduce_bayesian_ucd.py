"""Reproducibility entrypoint for Correlation-Aware Bayesian & Unknown-Variance V34 suites (v7--v11).

Runs verification, unit testing, summary regeneration, publication figure generation, and
smoke/full benchmark execution for all unified correlation-aware, unknown-variance,
C++17 acceleration, live LLM, and pre-submission audit suites (`results/bayesian_ucd_v1/`):
- v7 (E0--E6): Toy proxy, overlap x correlation phase diagram, hull/multi-answer, proteins,
  WorFBench, calibration/misspecification, and scaling
- v8 (v8_1--v8_6): Calibrated proteins, info-tracking vs CD-Joint, deconfounded factorial,
  amortized conic break-even, fresh uncached live Qwen3-0.6B, and hard-regime SameGame
- v9 (v9_1--v9_4): Unknown-variance V34 vs V33 sparse refresh, heteroscedastic efficiency,
  switching/IUT/null-safety/Behrens-Fisher audits, and certified solver cost of validity
- v10 (v10_1--v10_3): Native C++17 B&B scaling, real heteroscedastic bridge, and 24-run live LLM
- v11 (v11_1--v11_3): P0 real-data validity ablation, P1 36-campaign 4-domain live Qwen3-0.6B,
  and P2 zero-shared-code independent numerical-oracle verification audit
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
RES_DIR = ROOT / "results/bayesian_ucd_v1"

SUITES: dict[str, tuple[str, str, tuple[tuple[str, str], ...]]] = {
    "e0": (
        "paper/exp_v7_e0_and_toy.py",
        "e0_and_toy",
        (("sha256_e0", "e0_audit_runs.jsonl"), ("sha256_toy", "toy_runs.jsonl")),
    ),
    "e1": (
        "paper/exp_v7_e1_phase_diagram.py",
        "e1_phase_diagram",
        (("sha256_runs", "e1_phase_runs.jsonl"),),
    ),
    "e2": (
        "paper/exp_v7_e2_geometry_and_proxy.py",
        "e2_geometry_and_proxy",
        (
            ("sha256_hull", "e2_hull_runs.jsonl"),
            ("sha256_proxy", "e2_proxy_runs.jsonl"),
            ("sha256_multianswer", "e2_multianswer_runs.jsonl"),
        ),
    ),
    "e3": (
        "paper/exp_v7_e3_proteins.py",
        "e3_proteins",
        (("sha256_runs", "e3_protein_runs.jsonl"),),
    ),
    "e4": (
        "paper/exp_v7_e4_worfbench.py",
        "e4_worfbench",
        (("sha256_runs", "e4_worfbench_runs.jsonl"),),
    ),
    "e5": (
        "paper/exp_v7_e5_calibration.py",
        "e5_calibration",
        (("sha256_runs", "e5_calibration_runs.jsonl"),),
    ),
    "e6": (
        "paper/exp_v7_e6_scaling.py",
        "e6_scaling",
        (("sha256_runs", "e6_scaling_runs.jsonl"),),
    ),
}

V8_SUITES: dict[str, tuple[str, str]] = {
    "v8_1": ("paper/exp_v8_1_calibrated_proteins.py", "v8_exp1_calibrated_proteins"),
    "v8_2": ("paper/exp_v8_2_info_tracking.py", "v8_exp2_info_tracking"),
    "v8_3": ("paper/exp_v8_3_factorial_phase.py", "v8_exp3_factorial_phase"),
    "v8_4": ("paper/exp_v8_4_compute_breakeven.py", "v8_exp4_compute_breakeven"),
    "v8_5": ("paper/exp_v8_5_fresh_worfbench_live.py", "v8_exp5_fresh_worfbench_live"),
    "v8_6": ("paper/exp_v8_6_adaptive_samegame.py", "v8_exp6_adaptive_samegame"),
}

V9_SUITES: dict[str, tuple[str, str]] = {
    "v9_1": ("paper/exp_v9_1_v34_vs_v33_dag.py", "v9_exp1_v34_vs_v33_dag"),
    "v9_2": ("paper/exp_v9_2_heteroscedastic_info.py", "v9_exp2_heteroscedastic_info"),
    "v9_3": ("paper/exp_v9_3_switching_and_safety.py", "v9_exp3_switching_and_safety"),
    "v9_4": ("paper/exp_v9_4_solver_cost_of_validity.py", "v9_exp4_solver_cost_of_validity"),
}

V10_SUITES: dict[str, tuple[str, str]] = {
    "v10_1": ("paper/exp_v10_1_cpp_v34_scaling.py", "v10_exp1_cpp_v34_scaling"),
    "v10_2": ("paper/exp_v10_2_real_heteroscedastic_v34.py", "v10_exp2_real_heteroscedastic_v34"),
    "v10_3": ("paper/exp_v10_3_live_worfbench_expanded.py", "v10_exp3_live_worfbench_expanded"),
}

V11_SUITES: dict[str, tuple[str, str]] = {
    "v11_1": ("paper/exp_v11_1_protein_validity_ablation.py", "v11_exp1_protein_validity_ablation"),
    "v11_2": ("paper/exp_v11_2_live_worfbench_36campaigns.py", "v11_exp2_live_worfbench_36campaigns"),
    "v11_3": ("paper/exp_v11_3_independent_oracle_audit.py", "v11_exp3_independent_oracle_audit"),
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_py(args: list[str]) -> None:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT)
    env.pop("PYTHONSAFEPATH", None)
    subprocess.run([sys.executable, "-B", *args], cwd=ROOT, env=env, check=True)


def cmd_verify(_args: argparse.Namespace) -> None:
    for key, (_, subdir, checks) in SUITES.items():
        mdir = RES_DIR / subdir
        mpath = mdir / "manifest.json"
        if not mpath.is_file():
            raise SystemExit(f"Missing manifest for {key}: {mpath}")
        manifest = json.loads(mpath.read_text())
        if manifest.get("smoke"):
            raise SystemExit(f"Manifest {mpath} was generated in --smoke mode")
        for hash_key, fname in checks:
            fpath = mdir / fname
            if not fpath.is_file():
                raise SystemExit(f"Missing log file: {fpath}")
            actual = _sha256(fpath)
            if actual != manifest[hash_key]:
                raise SystemExit(f"SHA-256 mismatch for {fpath}: {actual} != {manifest[hash_key]}")
    for key, (_, subdir) in {**V8_SUITES, **V9_SUITES, **V10_SUITES, **V11_SUITES}.items():
        mdir = RES_DIR / subdir
        mpath = mdir / "manifest.json"
        if not mpath.is_file():
            raise SystemExit(f"Missing manifest for {key}: {mpath}")
        manifest = json.loads(mpath.read_text())
        if manifest.get("smoke"):
            raise SystemExit(f"Manifest {mpath} was generated in --smoke mode")
        files_map = manifest.get("files", {})
        if not files_map:
            raise SystemExit(f"Empty files map in {mpath}")
        for fname, meta in files_map.items():
            fpath = mdir / fname
            if not fpath.is_file():
                raise SystemExit(f"Missing artifact for {key}: {fpath}")
            actual = _sha256(fpath)
            if actual != meta["sha256"]:
                raise SystemExit(f"SHA-256 mismatch for {fpath}: {actual} != {meta['sha256']}")
    print("PASS: all v7 (E0--E6), v8 (v8_1--v8_6), v9 (v9_1--v9_4), v10 (v10_1--v10_3), and v11 (v11_1--v11_3) manifests verified.")


def cmd_test(_args: argparse.Namespace) -> None:
    _run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v7_*.py", "-v"])
    _run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v8_*.py", "-v"])
    _run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v9_*.py", "-v"])
    _run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v10_*.py", "-v"])
    _run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v11_*.py", "-v"])


def cmd_summaries(_args: argparse.Namespace) -> None:
    for script, _, _ in SUITES.values():
        _run_py([script, "--summarize-only"])
    for script, _ in {**V8_SUITES, **V9_SUITES, **V10_SUITES, **V11_SUITES}.values():
        _run_py([script, "--summarize-only"])


def cmd_figures(args: argparse.Namespace) -> None:
    extra = ["--out-dir", str(args.out)] if args.out else []
    _run_py(["paper/plot_v7_bayesian_ucd.py", *extra])
    _run_py(["paper/plot_v8_unified_figures.py", *extra])
    _run_py(["paper/plot_v9_v34_figures.py", *extra])
    _run_py(["paper/plot_v10_strengthening_figures.py", *extra])
    _run_py(["paper/plot_v11_audit_figures.py", *extra])


def cmd_benchmark(args: argparse.Namespace) -> None:
    all_keys = (
        list(SUITES.keys())
        + list(V8_SUITES.keys())
        + list(V9_SUITES.keys())
        + list(V10_SUITES.keys())
        + list(V11_SUITES.keys())
    )
    targets = [args.only] if args.only else all_keys
    v8_11 = {**V8_SUITES, **V9_SUITES, **V10_SUITES, **V11_SUITES}
    for key in targets:
        if key in SUITES:
            script, _, _ = SUITES[key]
            extra: list[str] = []
            if args.smoke:
                extra.extend(["--smoke", "--out", str(Path(args.smoke_dir) / key)])
            _run_py([script, *extra])
        else:
            script, _ = v8_11[key]
            extra = ["--smoke", "--out-dir", str(Path(args.smoke_dir) / key)] if args.smoke else []
            _run_py([script, *extra])


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="command", required=True)
    sub.add_parser("verify", help="Verify SHA-256 manifests for all v7--v11 suites")
    sub.add_parser("test", help="Run v7--v11 unit tests")
    sub.add_parser("summaries", help="Regenerate CSV/JSON summaries from JSONL logs")

    p_fig = sub.add_parser("figures", help="Regenerate publication PDF figures")
    p_fig.add_argument("--out", type=Path, default=None)

    p_b = sub.add_parser("benchmark", help="Run v7--v11 benchmark suites")
    p_b.add_argument("--smoke", action="store_true")
    p_b.add_argument(
        "--smoke-dir",
        type=Path,
        default=Path(tempfile.gettempdir()) / "bayesian_ucd_smoke",
    )
    p_b.add_argument(
        "--only",
        choices=tuple(SUITES.keys())
        + tuple(V8_SUITES.keys())
        + tuple(V9_SUITES.keys())
        + tuple(V10_SUITES.keys())
        + tuple(V11_SUITES.keys()),
        default=None,
    )

    args = ap.parse_args()
    {
        "verify": cmd_verify,
        "test": cmd_test,
        "summaries": cmd_summaries,
        "figures": cmd_figures,
        "benchmark": cmd_benchmark,
    }[args.command](args)


if __name__ == "__main__":
    main()
