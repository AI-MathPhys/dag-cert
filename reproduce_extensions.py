"""Reproducibility entrypoint for all v2, v3, and v4 extension benchmark suites.

Preserves 100% of the frozen v1 archive verified by `reproduce.py`, while providing
checksum verification, unit testing, summary regeneration, figure plotting, and
smoke/full benchmark execution for:
- v2 suites (`results/uct_v2_extensions/`: exp1..exp4),
- v3 strengthening suites (`results/uct_v3_strengthening/`: exp5..exp7), and
- v4 ICML external-baseline & zero-containment suites (`results/uct_v4_icml_baselines/`: exp8..exp10).
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
EXT_V2_DIR = ROOT / "results/uct_v2_extensions"
EXT_V3_DIR = ROOT / "results/uct_v3_strengthening"
EXT_V4_DIR = ROOT / "results/uct_v4_icml_baselines"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_py(args: list[str]) -> None:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT)
    env.pop("PYTHONSAFEPATH", None)
    subprocess.run([sys.executable, "-B", *args], cwd=ROOT, env=env, check=True)


def _verify_group(base_dir: Path, expected: dict[str, tuple[str, ...]]) -> None:
    for sub, pairs in expected.items():
        mdir = base_dir / sub
        mpath = mdir / "manifest.json"
        if not mpath.is_file():
            raise SystemExit(f"Missing manifest: {mpath}")
        manifest = json.loads(mpath.read_text())
        if manifest.get("smoke"):
            raise SystemExit(f"Manifest {mpath} was generated in --smoke mode, not full mode")
        for i in range(0, len(pairs), 2):
            key, fname = pairs[i], pairs[i + 1]
            fpath = mdir / fname
            if not fpath.is_file():
                raise SystemExit(f"Missing frozen log: {fpath}")
            actual = sha256(fpath)
            if actual != manifest[key]:
                raise SystemExit(f"SHA-256 mismatch for {fpath}: {actual} != {manifest[key]}")


def cmd_verify(args) -> None:
    # 1. Verify original frozen v1 archive is untouched
    run_py(["reproduce.py", "verify"])

    # 2. Verify all 4 v2 extension manifests and SHA-256 data digests
    expected_v2 = {
        "exp1_exact_regret": ("sha256_common_traces", "common_traces.jsonl", "sha256_wall_runs", "wall_runs.jsonl"),
        "exp2_puct": ("sha256_root_puct", "root_puct_runs.jsonl", "sha256_noisy_puct", "noisy_puct_runs.jsonl", "sha256_memory", "memory_runs.jsonl"),
        "exp3_samegame": ("sha256_traces", "diagnostics_and_traces.jsonl", "sha256_wall", "wall_runs.jsonl"),
        "exp4_representation": ("sha256_runs", "runs.jsonl"),
    }
    _verify_group(EXT_V2_DIR, expected_v2)

    # 3. Verify all 3 v3 strengthening manifests and SHA-256 data digests
    expected_v3 = {
        "exp5_emp_bernstein": ("sha256_common_traces", "common_traces.jsonl", "sha256_wall_runs", "wall_runs.jsonl"),
        "exp6_dag_lucb": ("sha256_runs", "runs.jsonl", "sha256_audit", "adaptive_coupling_audit.json"),
        "exp7_cpp_kernels": ("sha256_runs", "runs.jsonl", "sha256_parity_audit", "parity_audit.json"),
    }
    _verify_group(EXT_V3_DIR, expected_v3)

    # 4. Verify all 6 v4/v5/v6 ICML external-baseline, zero-containment, hybrid, & real-world manifests
    expected_v4 = {
        "exp8_external_baselines": ("sha256_runs", "runs.jsonl", "sha256_memory", "memory_runs.jsonl"),
        "exp9_samegame_midgame": ("sha256_diagnostics", "diagnostics.jsonl", "sha256_runs", "runs.jsonl", "sha256_memory", "memory_runs.jsonl"),
        "exp10_inside_witness": ("sha256_runs", "runs.jsonl"),
        "exp11_hybrid_and_os": ("sha256_hybrid", "hybrid_runs.jsonl", "sha256_midgame20", "midgame20_runs.jsonl", "sha256_star", "star_runs.jsonl"),
        "exp12_real_world": (
            "sha256_gb1_campaigns", "gb1_campaigns_runs.jsonl",
            "sha256_gb1_panel_sweep", "gb1_panel_sweep_runs.jsonl",
            "sha256_worfbench", "worfbench_runs.jsonl",
        ),
        "exp13_real_world_validation": (
            "sha256_factorial", "factorial_runs.jsonl",
            "sha256_gb1_noise", "gb1_noise_runs.jsonl",
            "sha256_trpb", "trpb_runs.jsonl",
            "sha256_worfbench_overlap", "worfbench_overlap_gen_runs.jsonl",
            "sha256_worfbench_live_online", "worfbench_live_online_runs.jsonl",
        ),
        "exp14_gb1_bayesian_opt": (
            "sha256_bo_acquisitions", "bo_acquisition_runs.jsonl",
            "sha256_gp_bounds", "gp_bounds_runs.jsonl",
        ),
        "exp15_bo_correlation_and_misspec": (
            "sha256_corr_1d", "corr_1d_runs.jsonl",
            "sha256_corr_2d", "corr_2d_phase_runs.jsonl",
            "sha256_gb1_misspec", "gb1_misspec_runs.jsonl",
        ),
    }
    _verify_group(EXT_V4_DIR, expected_v4)

    print("PASS: v1 frozen archive, 4 v2 suites, 3 v3 suites, and 8 v4/v5/v6 ICML suites verified.")


def cmd_test(args) -> None:
    run_py(["reproduce.py", "test"])
    run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v2_*.py", "-v"])
    run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v3_*.py", "-v"])
    run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v4_*.py", "-v"])
    run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v5_*.py", "-v"])
    run_py(["-m", "unittest", "discover", "-s", "tests", "-p", "test_v6_*.py", "-v"])


def cmd_summaries(args) -> None:
    for script in (
        "paper/exp_exact_regret.py",
        "paper/exp_puct.py",
        "paper/exp_samegame_d3.py",
        "paper/exp_representation_selector.py",
        "paper/exp_emp_bernstein.py",
        "paper/exp_dag_lucb.py",
        "paper/exp_cpp_kernels.py",
        "paper/exp_external_baselines.py",
        "paper/exp_samegame_midgame.py",
        "paper/exp_inside_witness.py",
        "paper/exp_hybrid_and_os.py",
        "paper/exp_real_world_applications.py",
        "paper/exp_real_world_validation.py",
        "paper/exp_gb1_bayesian_opt.py",
        "paper/exp_bo_correlation_and_misspec.py",
    ):
        run_py([script, "--summarize-only"])
    run_py(["paper/export_icml_figure_data.py"])


def cmd_figures(args) -> None:
    out_args = ["--out", str(args.out)] if args.out else []
    icml_out_args = ["--out-dir", str(args.out)] if args.out else []
    run_py(["paper/plot_icml_main_figures.py", *icml_out_args])
    run_py(["paper/plot_v2_extensions.py", *out_args])
    run_py(["paper/plot_v3_strengthening.py", *out_args])
    run_py(["paper/plot_v4_icml_baselines.py", *out_args])


def cmd_benchmark(args) -> None:
    mapping = {
        "exp1": "paper/exp_exact_regret.py",
        "exp2": "paper/exp_puct.py",
        "exp3": "paper/exp_samegame_d3.py",
        "exp4": "paper/exp_representation_selector.py",
        "exp5": "paper/exp_emp_bernstein.py",
        "exp6": "paper/exp_dag_lucb.py",
        "exp7": "paper/exp_cpp_kernels.py",
        "exp8": "paper/exp_external_baselines.py",
        "exp9": "paper/exp_samegame_midgame.py",
        "exp10": "paper/exp_inside_witness.py",
        "exp11": "paper/exp_hybrid_and_os.py",
        "exp12": "paper/exp_real_world_applications.py",
        "exp13": "paper/exp_real_world_validation.py",
        "exp14": "paper/exp_gb1_bayesian_opt.py",
        "exp15": "paper/exp_bo_correlation_and_misspec.py",
    }
    targets = [args.only] if args.only else list(mapping.keys())
    for key in targets:
        extra = []
        if args.smoke:
            extra.extend(["--smoke", "--out", str(Path(args.smoke_dir) / key)])
        run_py([mapping[key], *extra])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("verify", help="Verify frozen v1, v2, v3, and v4 benchmark archives")
    sub.add_parser("test", help="Run all v1, v2, v3, and v4 unit test suites")
    sub.add_parser("summaries", help="Regenerate CSV/JSON summaries from frozen v2, v3, and v4 JSONL logs")

    p_fig = sub.add_parser("figures", help="Generate v2, v3, and v4 publication PDF figures")
    p_fig.add_argument("--out", type=Path, default=None)

    p_bench = sub.add_parser("benchmark", help="Run v2, v3, and v4 experimental suites")
    p_bench.add_argument("--smoke", action="store_true", help="Run fast smoke verification into --smoke-dir")
    p_bench.add_argument(
        "--smoke-dir",
        type=Path,
        default=Path(tempfile.gettempdir()) / "dag_uct_ext_smoke",
    )
    p_bench.add_argument(
        "--only",
        choices=("exp1", "exp2", "exp3", "exp4", "exp5", "exp6", "exp7", "exp8", "exp9", "exp10", "exp11", "exp12", "exp13", "exp14", "exp15"),
        default=None,
    )

    args = parser.parse_args()
    {
        "verify": cmd_verify,
        "test": cmd_test,
        "summaries": cmd_summaries,
        "figures": cmd_figures,
        "benchmark": cmd_benchmark,
    }[args.command](args)


if __name__ == "__main__":
    main()
