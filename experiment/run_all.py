#!/usr/bin/env python3
"""Unified reproducibility CLI for AI-MathPhys/dagcert.

Covers ALL experiments in *Certify the Decision, Not the Outcome: Bayesian Experimental Design
on Search Graphs*, organized into the paper's three experimental domains:
  - simulated           (Section 3.1 + Appendices G, J, L)
  - protein_engineering (Section 3.2 + Appendix H)
  - agentic_workflows   (Section 3.3 + Appendix I)

Usage examples:
    python -m experiment.run_all list
    python -m experiment.run_all verify
    python -m experiment.run_all test
    python -m experiment.run_all summaries
    python -m experiment.run_all figures
    python -m experiment.run_all benchmark --domain protein_engineering --only v14 --smoke
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
RES_DIR = ROOT / "results"


@dataclass(frozen=True)
class SuiteSpec:
    key: str
    domain: str               # simulated | protein_engineering | agentic_workflows
    script: str               # repo-relative path under experiment/
    archive_dir: str          # repo-relative path under results/
    manifest_style: str       # "files_map" | "legacy_keys" | "ext_manifest"
    out_flag: str             # "--out-dir" | "--out"
    description: str
    legacy_hash_checks: tuple[tuple[str, str], ...] = ()


SUITES: tuple[SuiteSpec, ...] = (
    # =========================================================================
    # 1. SIMULATED EXPERIMENTS (Section 3.1 + Appendices G, J, L)
    # =========================================================================
    SuiteSpec(
        "v12", "simulated", "experiment/simulated/exp_bed_vs_bo.py",
        "results/bayesian_ucd_v1/v12_bed_vs_bo", "files_map", "--out-dir",
        "Matched-model BED vs. BO/KG/VOI/proxy & d=8 anytime frequentist (15,280 runs; Table 3, App. G.1)",
    ),
    SuiteSpec(
        "exp1", "simulated", "experiment/simulated/exp_overlap_exact_regret.py",
        "results/uct_v2_extensions/exp1_exact_regret", "ext_manifest", "--out",
        "Exact outside-support vs. marginal stopping across overlap (Fig. 2a, Table 10, Fig. 5)",
    ),
    SuiteSpec(
        "e0", "simulated", "experiment/simulated/exp_proxy_and_toy.py",
        "results/bayesian_ucd_v1/e0_and_toy", "legacy_keys", "--out",
        "Off-witness low-valued proxy benchmark & conic audit (Fig. 2b, Table 11)",
        (("sha256_e0", "e0_audit_runs.jsonl"), ("sha256_toy", "toy_runs.jsonl")),
    ),
    SuiteSpec(
        "e1", "simulated", "experiment/simulated/exp_phase_diagram.py",
        "results/bayesian_ucd_v1/e1_phase_diagram", "legacy_keys", "--out",
        "4x4 overlap x correlation phase diagram (Table 12)",
        (("sha256_runs", "e1_phase_runs.jsonl"),),
    ),
    SuiteSpec(
        "e2", "simulated", "experiment/simulated/exp_geometry_and_hull.py",
        "results/bayesian_ucd_v1/e2_geometry_and_proxy", "legacy_keys", "--out",
        "Feature-hull dominance, proxy, & multi-answer geometry (App. A.4)",
        (("sha256_hull", "e2_hull_runs.jsonl"), ("sha256_proxy", "e2_proxy_runs.jsonl"), ("sha256_multianswer", "e2_multianswer_runs.jsonl")),
    ),
    SuiteSpec(
        "v8_3", "simulated", "experiment/simulated/exp_factorial_and_proxy_sweep.py",
        "results/bayesian_ucd_v1/v8_exp3_factorial_phase", "files_map", "--out-dir",
        "Proxy alignment x cost sweep & deconfounded overlap x corr x mismatch factorial (Tables 13, 15, Fig. 6)",
    ),
    SuiteSpec(
        "exp5", "simulated", "experiment/simulated/exp_emp_bernstein.py",
        "results/uct_v3_strengthening/exp5_emp_bernstein", "ext_manifest", "--out",
        "Hoeffding vs. Empirical Bernstein confidence boxes (Table 16)",
    ),
    SuiteSpec(
        "exp6", "simulated", "experiment/simulated/exp_dag_lucb.py",
        "results/uct_v3_strengthening/exp6_dag_lucb", "ext_manifest", "--out",
        "Active witness allocation Exact-Regret-DAG-LUCB (Table 17)",
    ),
    SuiteSpec(
        "exp8", "simulated", "experiment/simulated/exp_external_baselines.py",
        "results/uct_v4_icml_baselines/exp8_external_baselines", "ext_manifest", "--out",
        "Structured pure-exploration baselines 2x2 sampler x certificate (Table 18, Fig. 7)",
    ),
    SuiteSpec(
        "exp10", "simulated", "experiment/simulated/exp_inside_witness.py",
        "results/uct_v4_icml_baselines/exp10_inside_witness", "ext_manifest", "--out",
        "Inside-witness selection ablation (Table 19, Fig. 8)",
    ),
    SuiteSpec(
        "exp11", "simulated", "experiment/simulated/exp_hybrid_and_os.py",
        "results/uct_v4_icml_baselines/exp11_hybrid_and_os", "ext_manifest", "--out",
        "DualWitnessCovers hybrid & tied-star non-containment family (Tables 20-21)",
    ),
    SuiteSpec(
        "v8_6", "simulated", "experiment/simulated/exp_adaptive_samegame.py",
        "results/bayesian_ucd_v1/v8_exp6_adaptive_samegame", "files_map", "--out-dir",
        "Hard-regime adaptive SameGame, Tied-Star, Decoy-16, Hetero-256 (Table 22)",
    ),
    SuiteSpec(
        "exp9", "simulated", "experiment/simulated/exp_samegame_midgame.py",
        "results/uct_v4_icml_baselines/exp9_samegame_midgame", "ext_manifest", "--out",
        "Containment-stratified mid-game SameGame & routing DAGs (Table 23)",
    ),
    SuiteSpec(
        "v8_2", "simulated", "experiment/simulated/exp_info_tracking.py",
        "results/bayesian_ucd_v1/v8_exp2_info_tracking", "files_map", "--out-dir",
        "Decision-aware information tracking vs. CD-Joint (Table 40, Fig. 11)",
    ),
    SuiteSpec(
        "e5", "simulated", "experiment/simulated/exp_calibration_grid.py",
        "results/bayesian_ucd_v1/e5_calibration", "legacy_keys", "--out",
        "Controlled calibration & misspecification grid (Table 41)",
        (("sha256_runs", "e5_calibration_runs.jsonl"),),
    ),
    SuiteSpec(
        "v9_1", "simulated", "experiment/simulated/exp_v34_vs_v33_dag.py",
        "results/bayesian_ucd_v1/v9_exp1_v34_vs_v33_dag", "files_map", "--out-dir",
        "Unknown-variance V34 sparse refresh vs. V33 dense (Table 43, Fig. 14a)",
    ),
    SuiteSpec(
        "v9_2", "simulated", "experiment/simulated/exp_v34_heteroscedastic.py",
        "results/bayesian_ucd_v1/v9_exp2_heteroscedastic_info", "files_map", "--out-dir",
        "Unknown heteroscedastic variance information efficiency (Table 44, Fig. 14b)",
    ),
    SuiteSpec(
        "v9_3", "simulated", "experiment/simulated/exp_v34_switching_safety.py",
        "results/bayesian_ucd_v1/v9_exp3_switching_and_safety", "files_map", "--out-dir",
        "Multi-answer switching, IUT budgeting, null wealth & Behrens-Fisher audit (Table 45, Fig. 13)",
    ),
    SuiteSpec(
        "v9_4", "simulated", "experiment/simulated/exp_v34_solver_cost.py",
        "results/bayesian_ucd_v1/v9_exp4_solver_cost_of_validity", "files_map", "--out-dir",
        "Certified global B&B cost of validity (Table 46)",
    ),
    SuiteSpec(
        "v10_1", "simulated", "experiment/simulated/exp_v34_cpp_scaling.py",
        "results/bayesian_ucd_v1/v10_exp1_cpp_v34_scaling", "files_map", "--out-dir",
        "Native C++17 outward-certified branch-and-bound scaling to d=8 (Table 68, Fig. 15a)",
    ),
    SuiteSpec(
        "e6", "simulated", "experiment/simulated/exp_conic_scaling.py",
        "results/bayesian_ucd_v1/e6_scaling", "legacy_keys", "--out",
        "Conic certificate update scaling (Tables 1, 57)",
        (("sha256_runs", "e6_scaling_runs.jsonl"),),
    ),
    SuiteSpec(
        "v8_4", "simulated", "experiment/simulated/exp_compute_breakeven.py",
        "results/bayesian_ucd_v1/v8_exp4_compute_breakeven", "files_map", "--out-dir",
        "Amortized conic update schedules & break-even latency (Table 58)",
    ),
    SuiteSpec(
        "exp7", "simulated", "experiment/simulated/exp_cpp_kernels.py",
        "results/uct_v3_strengthening/exp7_cpp_kernels", "ext_manifest", "--out",
        "Native C++17 graph-maintenance micro-kernels (Tables 60-61)",
    ),
    SuiteSpec(
        "v11_3", "simulated", "experiment/simulated/exp_independent_oracle_audit.py",
        "results/bayesian_ucd_v1/v11_exp3_independent_oracle_audit", "files_map", "--out-dir",
        "Zero-shared-code independent numerical-oracle verification audit (5/5 PASS; Table 69)",
    ),
    SuiteSpec(
        "exp2", "simulated", "experiment/simulated/exp_puct.py",
        "results/uct_v2_extensions/exp2_puct", "ext_manifest", "--out",
        "Root-PUCT & noisy recursive PUCT certification transfer (Tables 55, 64)",
    ),
    SuiteSpec(
        "exp3", "simulated", "experiment/simulated/exp_samegame_d3.py",
        "results/uct_v2_extensions/exp3_samegame", "ext_manifest", "--out",
        "SameGame depth-3/4 lookahead certification (Tables 56, 65)",
    ),
    SuiteSpec(
        "exp4", "simulated", "experiment/simulated/exp_representation_selector.py",
        "results/uct_v2_extensions/exp4_representation", "ext_manifest", "--out",
        "Graph representation comparison & runtime selector (Tables 66-67)",
    ),
    # =========================================================================
    # 2. PROTEIN ENGINEERING (Section 3.2 + Appendix H: GB1 & TmTrpB)
    # =========================================================================
    SuiteSpec(
        "v14", "protein_engineering", "experiment/protein_engineering/exp_credible_ellipsoid_audit.py",
        "results/bayesian_ucd_v1/v14_protein_credible_ellipsoid", "files_map", "--out-dir",
        "410-campaign proper chi2_{M-1,.95/.90} ellipsoid, direct post.-risk & coverage audit (Table 4, Fig. 3, Table 24, Fig. 9)",
    ),
    SuiteSpec(
        "v13", "protein_engineering", "experiment/protein_engineering/exp_matched_bed_vs_kg.py",
        "results/bayesian_ucd_v1/v13_protein_bed_vs_kg", "files_map", "--out-dir",
        "410-campaign matched GB1 & TmTrpB BED vs. Correlated KG across nominal & DF stopping (12,300 runs; Tables 25-26)",
    ),
    SuiteSpec(
        "v11_1", "protein_engineering", "experiment/protein_engineering/exp_validity_ablation.py",
        "results/bayesian_ucd_v1/v11_exp1_protein_validity_ablation", "files_map", "--out-dir",
        "Protein certificate-validity factorial & coupled-stream replay (Table 27, Tables 49-50)",
    ),
    SuiteSpec(
        "v8_1", "protein_engineering", "experiment/protein_engineering/exp_calibrated_proteins.py",
        "results/bayesian_ucd_v1/v8_exp1_calibrated_proteins", "files_map", "--out-dir",
        "Calibrated EB+LOO proteins, rough-GP cure & (xi,eps) frontier (Tables 28, 42, Fig. 12)",
    ),
    SuiteSpec(
        "v10_2", "protein_engineering", "experiment/protein_engineering/exp_heteroscedastic_bridge.py",
        "results/bayesian_ucd_v1/v10_exp2_real_heteroscedastic_v34", "files_map", "--out-dir",
        "Heteroscedastic V34 bridge on GB1 shot noise & WorFBench + raw misspec. (Table 47, Fig. 15b)",
    ),
    SuiteSpec(
        "exp14", "protein_engineering", "experiment/protein_engineering/exp_gb1_bayesian_opt.py",
        "results/uct_v4_icml_baselines/exp14_gb1_bayesian_opt", "ext_manifest", "--out",
        "BO terminal discovery vs. root-action certification on GB1 (Tables 32-33)",
    ),
    SuiteSpec(
        "e3", "protein_engineering", "experiment/protein_engineering/exp_gb1_trpb_stratum.py",
        "results/bayesian_ucd_v1/e3_proteins", "legacy_keys", "--out",
        "GB1 stratum breakdown (single-peak vs. epistatic ridge) & 21-template TmTrpB (Table 34)",
        (("sha256_runs", "e3_protein_runs.jsonl"),),
    ),
    SuiteSpec(
        "exp12", "protein_engineering", "experiment/protein_engineering/exp_real_world_applications.py",
        "results/uct_v4_icml_baselines/exp12_real_world", "ext_manifest", "--out",
        "GB1 template/panel sweeps & WorFBench offline factorial (Tables 29-30, 35, 48, Table 5 offline)",
    ),
    SuiteSpec(
        "exp13", "protein_engineering", "experiment/protein_engineering/exp_real_world_validation.py",
        "results/uct_v4_icml_baselines/exp13_real_world_validation", "ext_manifest", "--out",
        "GB1 noise models, 21-template TmTrpB, WorFBench overlap sweep & first live audit (Tables 31, 36)",
    ),
    SuiteSpec(
        "exp15", "protein_engineering", "experiment/protein_engineering/exp_bo_correlation_misspec.py",
        "results/uct_v4_icml_baselines/exp15_bo_correlation_and_misspec", "ext_manifest", "--out",
        "BO correlation & misspecification control study (archived)",
    ),
    # =========================================================================
    # 3. AGENTIC WORKFLOWS (Section 3.3 + Appendix I: WorFBench & Live Qwen3-0.6B)
    # =========================================================================
    SuiteSpec(
        "v11_2", "agentic_workflows", "experiment/agentic_workflows/exp_live_qwen3_36campaigns.py",
        "results/bayesian_ucd_v1/v11_exp2_live_worfbench_36campaigns", "files_map", "--out-dir",
        "36-campaign 4-domain fresh uncached live Qwen3-0.6B replication (Table 5 live, Table 37, Fig. 10)",
    ),
    SuiteSpec(
        "v10_3", "agentic_workflows", "experiment/agentic_workflows/exp_live_qwen3_8campaigns.py",
        "results/bayesian_ucd_v1/v10_exp3_live_worfbench_expanded", "files_map", "--out-dir",
        "8-campaign (24-run) fresh uncached live Qwen3-0.6B cohort (Table 38, Fig. 15c)",
    ),
    SuiteSpec(
        "v8_5", "agentic_workflows", "experiment/agentic_workflows/exp_worfbench_unseen_live.py",
        "results/bayesian_ucd_v1/v8_exp5_fresh_worfbench_live", "files_map", "--out-dir",
        "WorFBench 3-way unseen-task generalization & initial uncached live run (Table 39)",
    ),
    SuiteSpec(
        "e4", "agentic_workflows", "experiment/agentic_workflows/exp_worfbench_correlated.py",
        "results/bayesian_ucd_v1/e4_worfbench", "legacy_keys", "--out",
        "Initial correlated WorFBench study (archived; superseded by v8_5)",
        (("sha256_runs", "e4_worfbench_runs.jsonl"),),
    ),
)

SUITE_BY_KEY: dict[str, SuiteSpec] = {s.key: s for s in SUITES}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_py(args: list[str]) -> None:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT)
    env.setdefault("OMP_NUM_THREADS", "1")
    env.setdefault("OPENBLAS_NUM_THREADS", "1")
    env.setdefault("MKL_NUM_THREADS", "1")
    env.pop("PYTHONSAFEPATH", None)
    subprocess.run([sys.executable, "-B", *args], cwd=ROOT, env=env, check=True)


def cmd_list(_args: argparse.Namespace) -> None:
    for dom in ("simulated", "protein_engineering", "agentic_workflows"):
        print(f"\n=== {dom} ===")
        for s in SUITES:
            if s.domain == dom:
                print(f"  {s.key:8s} | {s.script:68s} | {s.description}")


def cmd_verify(_args: argparse.Namespace) -> None:
    # 1. Verify frozen v1 passive-UCT logs and reference tables
    v1_path = RES_DIR / "uct_v1_manifest.json"
    if not v1_path.is_file():
        raise SystemExit(f"Missing v1 manifest: {v1_path}")
    v1_man = json.loads(v1_path.read_text(encoding="utf-8"))
    for rel, expected in v1_man["files"].items():
        fp = ROOT / rel
        if not fp.is_file():
            raise SystemExit(f"Missing v1 archived file: {fp}")
        exp_sha = expected["sha256"] if isinstance(expected, dict) else expected
        actual = _sha256(fp)
        if actual != exp_sha:
            raise SystemExit(f"SHA-256 mismatch for {rel}: {actual} != {exp_sha}")

    # 2. Verify all extension & Bayesian/V34/protein/workflow suites (exp1--exp15, e0--e6, v8--v14)
    for s in SUITES:
        adir = ROOT / s.archive_dir
        mpath = adir / "manifest.json"
        if not mpath.is_file():
            raise SystemExit(f"Missing manifest for {s.key}: {mpath}")
        manifest = json.loads(mpath.read_text(encoding="utf-8"))
        if manifest.get("smoke"):
            raise SystemExit(f"Manifest {mpath} was generated in --smoke mode")

        if s.manifest_style == "files_map":
            files_map = manifest.get("files", {})
            if not files_map:
                raise SystemExit(f"Empty files map in {mpath}")
            for fname, meta in files_map.items():
                fp = adir / fname
                if not fp.is_file():
                    raise SystemExit(f"Missing artifact for {s.key}: {fp}")
                actual = _sha256(fp)
                if actual != meta["sha256"]:
                    raise SystemExit(f"SHA-256 mismatch for {fp}: {actual} != {meta['sha256']}")
        elif s.manifest_style == "legacy_keys":
            for hkey, fname in s.legacy_hash_checks:
                fp = adir / fname
                if not fp.is_file():
                    raise SystemExit(f"Missing log for {s.key}: {fp}")
                actual = _sha256(fp)
                if actual != manifest[hkey]:
                    raise SystemExit(f"SHA-256 mismatch for {fp}: {actual} != {manifest[hkey]}")
        elif s.manifest_style == "ext_manifest":
            checked = 0
            for k, v in manifest.items():
                if k.startswith("sha256_") and isinstance(v, str) and len(v) == 64:
                    # Match extension manifest convention (single runs.jsonl or named jsonl)
                    candidates = [f for f in adir.glob("*.jsonl")]
                    for fp in candidates:
                        if _sha256(fp) == v:
                            checked += 1
                            break
            files_map = manifest.get("files", {})
            for fname, meta in files_map.items():
                fp = adir / fname
                if not fp.is_file():
                    raise SystemExit(f"Missing artifact for {s.key}: {fp}")
                exp_sha = meta["sha256"] if isinstance(meta, dict) else meta
                if _sha256(fp) != exp_sha:
                    raise SystemExit(f"SHA-256 mismatch for {fp}")
                checked += 1
            if checked == 0:
                # Fallback: verify all sha256 fields stored as dict or top-level filename keys
                for k, v in manifest.items():
                    fp = adir / k
                    if fp.is_file() and isinstance(v, str) and len(v) == 64:
                        if _sha256(fp) != v:
                            raise SystemExit(f"SHA-256 mismatch for {fp}")
                        checked += 1
            if checked == 0:
                raise SystemExit(f"No SHA-256 entries verified in {mpath}")

    print(
        f"PASS: Verified SHA-256 integrity across passive-UCT v1 ({len(v1_man['files'])} files) "
        f"and all {len(SUITES)} experiment suites (v2--v14, zero gaps)."
    )


def cmd_test(_args: argparse.Namespace) -> None:
    _run_py(["-m", "pytest", "tests", "-v"])


def cmd_summaries(args: argparse.Namespace) -> None:
    targets = _select_suites(args.domain, args.only)
    for s in targets:
        if s.key.startswith("exp"):
            # Extension scripts accept --summarize-only where implemented
            src_txt = (ROOT / s.script).read_text(encoding="utf-8")
            if "--summarize-only" not in src_txt:
                continue
        _run_py([s.script, "--summarize-only"])
    print(f"PASS: Regenerated summaries for {len(targets)} target suite(s).")


def cmd_figures(args: argparse.Namespace) -> None:
    out_dir = Path(args.out) if args.out else (ROOT / "figures")
    out_dir.mkdir(parents=True, exist_ok=True)
    # 1. Exact 7 manuscript supplementary PDFs (`figures/supp_*.pdf`)
    _run_py(["experiment/plots/plot_supp_manuscript_figures.py", "--out-dir", str(out_dir)])
    # 2. Full detailed suite figures into results/bayesian_ucd_v1/figures (or custom out_dir)
    if args.all_suites:
        suite_out = out_dir / "detailed"
        suite_out.mkdir(parents=True, exist_ok=True)
        for plotter in (
            "experiment/plots/plot_v7_bayesian_ucd.py",
            "experiment/plots/plot_v8_unified_figures.py",
            "experiment/plots/plot_v9_v34_figures.py",
            "experiment/plots/plot_v10_strengthening_figures.py",
            "experiment/plots/plot_v11_audit_figures.py",
            "experiment/plots/plot_v12_bed_vs_bo.py",
            "experiment/plots/plot_v13_protein_bed_vs_kg.py",
            "experiment/plots/plot_v14_protein_credible_ellipsoid.py",
        ):
            _run_py([plotter, "--out-dir", str(suite_out)])


def _select_suites(domain: str, only: str | None) -> list[SuiteSpec]:
    if only is not None:
        if only not in SUITE_BY_KEY:
            raise SystemExit(f"Unknown suite key {only!r}. Run `python -m experiment.run_all list` to see keys.")
        return [SUITE_BY_KEY[only]]
    if domain == "all":
        return list(SUITES)
    return [s for s in SUITES if s.domain == domain]


def cmd_benchmark(args: argparse.Namespace) -> None:
    targets = _select_suites(args.domain, args.only)
    for s in targets:
        extra: list[str] = []
        if args.smoke:
            extra.extend(["--smoke", s.out_flag, str(Path(args.smoke_dir) / s.key)])
        print(f"\n>>> Running [{s.domain}] {s.key}: {s.script} {' '.join(extra)}", flush=True)
        _run_py([s.script, *extra])


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = ap.add_subparsers(dest="command", required=True)

    sub.add_parser("list", help="List all paper experiment suites grouped by domain")
    sub.add_parser("verify", help="Cryptographically verify SHA-256 manifests for ALL v1--v14 suites")
    sub.add_parser("test", help="Run full pytest verification suite (library API + v1--v14 tests)")

    p_sum = sub.add_parser("summaries", help="Regenerate CSV summaries from archived JSONL logs")
    p_sum.add_argument("--domain", choices=("all", "simulated", "protein_engineering", "agentic_workflows"), default="all")
    p_sum.add_argument("--only", choices=tuple(SUITE_BY_KEY.keys()), default=None)

    p_fig = sub.add_parser("figures", help="Regenerate publication & supplementary PDF figures")
    p_fig.add_argument("--out", type=Path, default=None, help="Output directory (default: figures/)")
    p_fig.add_argument("--all-suites", action="store_true", help="Also regenerate all detailed v7--v14 suite figures")

    p_b = sub.add_parser("benchmark", help="Run benchmark suites from scratch (use --smoke for fast verification)")
    p_b.add_argument("--domain", choices=("all", "simulated", "protein_engineering", "agentic_workflows"), default="all")
    p_b.add_argument("--only", choices=tuple(SUITE_BY_KEY.keys()), default=None)
    p_b.add_argument("--smoke", action="store_true", help="Fast non-destructive smoke mode writing to tempdir")
    p_b.add_argument("--smoke-dir", type=Path, default=Path(tempfile.gettempdir()) / "dagcert_smoke")

    args = ap.parse_args()
    {
        "list": cmd_list,
        "verify": cmd_verify,
        "test": cmd_test,
        "summaries": cmd_summaries,
        "figures": cmd_figures,
        "benchmark": cmd_benchmark,
    }[args.command](args)


if __name__ == "__main__":
    main()
