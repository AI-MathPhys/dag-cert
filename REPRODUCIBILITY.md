# Reproducibility Guide & Complete Artifact Map

This document maps **every table (Tables 1–69) and every figure (Figures 1–15)** of **Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs** ([`manuscript/Joint_cert_manuscript.pdf`](manuscript/Joint_cert_manuscript.pdf)) to its executable script under `experiment/`, its SHA-256-verified archive under `results/`, and its reproduction command via `experiment/run_all.py`.

**Coverage status: 100% complete — zero missing experiments, logs, supplementary figures, or formalizations.**
All 41 extension/Bayesian/protein/workflow suites (`exp1`–`exp15`, `e0`–`e6`, `v8_1`–`v8_6`, `v9_1`–`v9_4`, `v10_1`–`v10_3`, `v11_1`–`v11_3`, `v12`, `v13`, `v14`), the frozen passive-UCT v1 archive (`results/uct_v1_manifest.json`), all seven supplementary vector PDFs (`figures/supp_*.pdf`), and the Lean 4 formalizations (`lean/`) are included and verified in this repository. (Tables 2 and 6 are conceptual validity-regime summaries requiring no experimental archive.)

Appendix letters follow the compiled PDF: A–F (theory & methods), **G** (simulated experiments), **H** (protein engineering), **I** (agentic workflows), **J** (extended validation & unknown variance), **K** (algorithms), **L** (computational performance & independent oracle audit).

---

## 1. Environment, Library & Data Setup

```bash
python -m pip install -e ".[dev,audit]"      # Core library + pytest + CVXPY/Clarabel oracle tests
# Optional for fresh uncached live Qwen3-0.6B runs (v8_5, v10_3, v11_2):
python -m pip install -e ".[all]"
```

- All source and data paths are repository-relative and resolved through the installed `joint_root_cert` package.
- Compact benchmark archives (`joint_root_cert/benchmarks/data/*.npz`, 1.7 MB) and the 20-board SameGame set (`joint_root_cert/benchmarks/data/samegame/StandardTestset.txt`) are bundled in Git so offline verification, all 88 unit tests, and CPU suites run without network access.
- Every upstream dataset and model (FLIP GB1, Zenodo 15203754 TmTrpB, `zjunlp/WorfBench` gold trajectories, `Qwen/Qwen3-0.6B`, `Qwen/Qwen3-Embedding-0.6B`) can be checked, fetched, or rebuilt with `python scripts/fetch_data.py`.
- For multi-process CPU experiments, pin single-threaded BLAS (`OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1`); `experiment/run_all.py` sets these automatically.

### One-Command Integrity & Test Checks

```bash
python scripts/fetch_data.py --check     # Verify bundled datasets, HF cache, and C++17 compiler
python experiment/run_all.py verify      # SHA-256 check across passive-UCT v1 (31 files) + all 41 suites
python experiment/run_all.py test        # Run all 88 pytest unit, parity, API & oracle tests
python experiment/run_all.py figures     # Regenerate all 7 manuscript `figures/supp_*.pdf` files
```

---

## 2. Complete Domain-by-Domain Artifact Map

Re-run any suite with:

```bash
python experiment/run_all.py benchmark --only <key>            # full run
python experiment/run_all.py benchmark --only <key> --smoke    # fast non-destructive check (tempdir)
python experiment/run_all.py summaries --only <key>            # rebuild CSV summaries from archived JSONL
```

### Domain 1: Simulated Experiments (`experiment/simulated/`)

Covers Section 2.3, Section 3.1, Appendix G, Appendix J, and Appendix L.

| Key | Manuscript Evidence | Script (`experiment/simulated/`) | Verified Archive (`results/`) |
|---|---|---|---|
| `v12` | **Table 3** (§3.1); **Tables 7, 8, 9, 14, 59; Fig. 4** (App. G.1, L.1) — 15,280-run matched-model BED vs. Correlated KG, GP-OS, VOI, BO & $d=8$ anytime frequentist + latency crossover | `exp_bed_vs_bo.py` | `bayesian_ucd_v1/v12_bed_vs_bo/` |
| `exp1` | **Fig. 2a, Table 10, Fig. 5** (§3.1, App. G.2) — exact outside-support vs. marginal stopping across overlap | `exp_overlap_exact_regret.py` | `uct_v2_extensions/exp1_exact_regret/` |
| `e0` | **Fig. 2b, Table 11** (§3.1, App. G.3) — off-witness low-valued proxy benchmark & conic audit | `exp_proxy_and_toy.py` | `bayesian_ucd_v1/e0_and_toy/` |
| `e1` | **Table 12** (App. G.3) — $4\times 4$ overlap $\times$ correlation phase diagram | `exp_phase_diagram.py` | `bayesian_ucd_v1/e1_phase_diagram/` |
| `e2` | Supports App. A.4 — feature-hull dominance, proxy & multi-answer geometry | `exp_geometry_and_hull.py` | `bayesian_ucd_v1/e2_geometry_and_proxy/` |
| `v8_3` | **Tables 13, 15; Fig. 6** (§3.1, App. G.3) — proxy alignment $\times$ cost sweep & deconfounded overlap $\times$ correlation $\times$ mismatch factorial | `exp_factorial_and_proxy_sweep.py` | `bayesian_ucd_v1/v8_exp3_factorial_phase/` |
| `exp5` | **Table 16** (App. G.4) — Hoeffding vs. Empirical Bernstein confidence boxes | `exp_emp_bernstein.py` | `uct_v3_strengthening/exp5_emp_bernstein/` |
| `exp6` | **Table 17** (App. G.4) — active witness allocation Exact-Regret-DAG-LUCB | `exp_dag_lucb.py` | `uct_v3_strengthening/exp6_dag_lucb/` |
| `exp8` | **Table 18, Fig. 7** (App. G.4) — structured pure-exploration baselines ($2\times 2$ sampler $\times$ certificate) | `exp_external_baselines.py` | `uct_v4_icml_baselines/exp8_external_baselines/` |
| `exp10` | **Table 19, Fig. 8** (App. G.4) — inside-witness selection ablation | `exp_inside_witness.py` | `uct_v4_icml_baselines/exp10_inside_witness/` |
| `exp11` | **Tables 20, 21** (App. G.4) — `DualWitnessCovers` hybrid & tied-star non-containment family | `exp_hybrid_and_os.py` | `uct_v4_icml_baselines/exp11_hybrid_and_os/` |
| `v8_6` | **Table 22** (App. G.5) — hard-regime adaptive SameGame, Tied-Star, Decoy-16, Hetero-256 | `exp_adaptive_samegame.py` | `bayesian_ucd_v1/v8_exp6_adaptive_samegame/` |
| `exp9` | **Table 23** (App. G.5) — containment-stratified mid-game SameGame & routing DAGs | `exp_samegame_midgame.py` | `uct_v4_icml_baselines/exp9_samegame_midgame/` |
| `v8_2` | **Table 40, Fig. 11** (App. J.1) — decision-aware information tracking ($T_*^\varepsilon$) vs. CD-Joint | `exp_info_tracking.py` | `bayesian_ucd_v1/v8_exp2_info_tracking/` |
| `e5` | **Table 41** (App. J.2) — controlled calibration & misspecification grid | `exp_calibration_grid.py` | `bayesian_ucd_v1/e5_calibration/` |
| `v9_1` | **Table 43, Figs. 13c & 14a** (App. J.3) — unknown-variance V34 sparse refresh + action-local vs. V33 dense | `exp_v34_vs_v33_dag.py` | `bayesian_ucd_v1/v9_exp1_v34_vs_v33_dag/` |
| `v9_2` | **Table 44, Fig. 14b** (App. J.3) — unknown heteroscedastic variance information efficiency & stress | `exp_v34_heteroscedastic.py` | `bayesian_ucd_v1/v9_exp2_heteroscedastic_info/` |
| `v9_3` | **Table 45, Figs. 13a–b** (App. J.3) — multi-answer switching, IUT budgeting, null wealth & Behrens–Fisher audit | `exp_v34_switching_safety.py` | `bayesian_ucd_v1/v9_exp3_switching_and_safety/` |
| `v9_4` | **Table 46** (App. J.3) — certified global branch-and-bound cost of validity | `exp_v34_solver_cost.py` | `bayesian_ucd_v1/v9_exp4_solver_cost_of_validity/` |
| `e6` | **Tables 1, 57** (§2.3, App. L.1) — conic certificate update scaling up to $M=4{,}096$ | `exp_conic_scaling.py` | `bayesian_ucd_v1/e6_scaling/` |
| `v8_4` | **Table 58** (App. L.1) — amortized conic update schedules & evaluation-latency break-even | `exp_compute_breakeven.py` | `bayesian_ucd_v1/v8_exp4_compute_breakeven/` |
| `exp7` | **Tables 60, 61** (App. L.2) — native C++17 graph-maintenance micro-kernels | `exp_cpp_kernels.py` | `uct_v3_strengthening/exp7_cpp_kernels/` |
| `exp2` | **Tables 55, 64** (App. J.5, L.4) — Root-PUCT & noisy recursive PUCT certification transfer | `exp_puct.py` | `uct_v2_extensions/exp2_puct/` |
| `exp3` | **Tables 56, 65** (App. J.5, L.4) — SameGame depth-3/4 lookahead certification | `exp_samegame_d3.py` | `uct_v2_extensions/exp3_samegame/` |
| `exp4` | **Tables 66, 67** (App. L.4) — graph representation comparison & runtime selector | `exp_representation_selector.py` | `uct_v2_extensions/exp4_representation/` |
| `v10_1` | **Table 68, Fig. 15a** (App. L.5) — native C++17 outward-certified branch-and-bound scaling to $d=8$ | `exp_v34_cpp_scaling.py` | `bayesian_ucd_v1/v10_exp1_cpp_v34_scaling/` |
| `v11_3` | **Table 69** (App. L.6) — zero-shared-code independent numerical-oracle verification audit ($5/5$ pass) | `exp_independent_oracle_audit.py` | `bayesian_ucd_v1/v11_exp3_independent_oracle_audit/` |
| `passive_uct/` | **Tables 51–54, 62–63** (App. J.5, L.3) — frozen passive TA-UCT coupled certification, gap intervention, frontier timing & peak memory (1,920 runs; 3,826,797 boundaries) | `passive_uct/{uct_backup_*,uct_frontier_*,audit_uct_backup,report_*}.py` | `uct_backup_v1/`, `uct_frontier_v1/`, `reference/tables/`, `uct_v1_manifest.json` |

---

### Domain 2: Protein Engineering (`experiment/protein_engineering/`)

Covers Section 3.2, Appendix H, and Appendix J.2/J.4 on measured four-site GB1 (Wu et al. 2016) and TmTrpB (Johnston et al. 2024) combinatorial landscapes.

| Key | Manuscript Evidence | Script (`experiment/protein_engineering/`) | Verified Archive (`results/`) |
|---|---|---|---|
| `v14` | **Fig. 3, Table 4** (§3.2); **Table 24, Fig. 9** (App. H.3) — 410-campaign proper $\sqrt{\chi^2_{M-1,.95/.90}}$ joint credible ellipsoid, valid anytime direct posterior-risk MC & simultaneous contrast coverage audit | `exp_credible_ellipsoid_audit.py` | `bayesian_ucd_v1/v14_protein_credible_ellipsoid/` |
| `v13` | **Table 4 (DF rows), Fig. 3c** (§3.2); **Tables 25, 26** (App. H.2, H.4) — 12,300-run matched GB1 & TmTrpB acquisition comparison (CD-Joint, Correlated KG, GP-OS, GP-Root-Info, GP-UCB) under nominal & DF stopping | `exp_matched_bed_vs_kg.py` | `bayesian_ucd_v1/v13_protein_bed_vs_kg/` |
| `v11_1` | **Table 27** (§3.2, App. H.5); **Tables 49, 50** (App. J.4) — protein certificate-validity factorial & coupled-stream replay ($91.5\%$ / $82.9\%$ terminal vs. $100\%$ root-regret coverage) | `exp_validity_ablation.py` | `bayesian_ucd_v1/v11_exp1_protein_validity_ablation/` |
| `v8_1` | **Table 28** (App. H.5); **Table 42, Fig. 12** (App. J.2) — calibrated EB+LOO proteins, rough-GP cure & $(\xi,\varepsilon)$ bounded-residual frontier | `exp_calibrated_proteins.py` | `bayesian_ucd_v1/v8_exp1_calibrated_proteins/` |
| `v10_2` | **Table 47, Fig. 15b** (App. J.4) — heteroscedastic V34 bridge on GB1 shot noise & WorFBench + raw misspecification stress | `exp_heteroscedastic_bridge.py` | `bayesian_ucd_v1/v10_exp2_real_heteroscedastic_v34/` |
| `exp12` | **Tables 29, 30, 48** (App. H.6, J.4) — GB1 template & panel sweeps (+ WorFBench offline factorial) | `exp_real_world_applications.py` | `uct_v4_icml_baselines/exp12_real_world/` |
| `exp13` | **Table 31** (App. H.6) — GB1 noise-model ablation & 21-template TmTrpB (+ WorFBench overlap) | `exp_real_world_validation.py` | `uct_v4_icml_baselines/exp13_real_world_validation/` |
| `exp14` | **Tables 32, 33** (App. H.6) — BO terminal discovery vs. root-action certification on GB1 | `exp_gb1_bayesian_opt.py` | `uct_v4_icml_baselines/exp14_gb1_bayesian_opt/` |
| `e3` | **Table 34** (App. H.6) — GB1 stratum breakdown (single-peak vs. epistatic ridge) & 21-template TmTrpB | `exp_gb1_trpb_stratum.py` | `bayesian_ucd_v1/e3_proteins/` |
| `exp15` | Archived BO correlation & misspecification control study | `exp_bo_correlation_misspec.py` | `uct_v4_icml_baselines/exp15_bo_correlation_and_misspec/` |

Dataset builders: `experiment/protein_engineering/build_gb1_dataset.py`, `build_trpb_dataset.py` (invoked by `scripts/fetch_data.py --proteins`).

---

### Domain 3: Agentic Workflows (`experiment/agentic_workflows/`)

Covers Section 3.3 and Appendix I on WorFBench ($3^4=81$ workflows) and fresh uncached `Qwen/Qwen3-0.6B` execution.

| Key | Manuscript Evidence | Script (`experiment/agentic_workflows/`) | Verified Archive (`results/`) |
|---|---|---|---|
| `v11_2` | **Table 5 (live rows)** (§3.3); **Table 37, Fig. 10** (App. I) — 36-campaign, 4-domain fresh uncached live Qwen3-0.6B replication ($0/36$ DF vs. $36/36$ EB+LOO in 24 evals / 14,291 tokens) | `exp_live_qwen3_36campaigns.py` | `bayesian_ucd_v1/v11_exp2_live_worfbench_36campaigns/` |
| `v10_3` | **Table 38, Fig. 15c** (App. I) — 8-campaign (24-run) fresh uncached live Qwen3-0.6B cohort | `exp_live_qwen3_8campaigns.py` | `bayesian_ucd_v1/v10_exp3_live_worfbench_expanded/` |
| `v8_5` | **Table 39** (App. I) — WorFBench 3-way unseen-task generalization & initial uncached live audit | `exp_worfbench_unseen_live.py` | `bayesian_ucd_v1/v8_exp5_fresh_worfbench_live/` |
| `exp12` / `exp13` | **Table 5 (offline rows)** (§3.3); **Tables 35, 36** (App. I) — WorFBench offline factorial ($1{,}937$ evals / $0.95\text{ M}$ tokens) & overlap sweep | `exp_worfbench_offline_and_overlap.py` (wrapper around `exp12`/`exp13`) | `uct_v4_icml_baselines/exp12_real_world/`, `exp13_real_world_validation/` |
| `e4` | Archived initial correlated WorFBench study (superseded by `v8_5`) | `exp_worfbench_correlated.py` | `bayesian_ucd_v1/e4_worfbench/` |

Dataset builders: `experiment/agentic_workflows/build_worfbench_llm_matrix.py`, `build_worfbench_test_and_live.py` (invoked by `scripts/fetch_data.py --rebuild-worfbench`).

---

## 3. Manuscript Figures Map (`figures/` & `experiment/plots/`)

Main-text Figures 1–3 and Appendix Figures 4–8 are rendered natively via TikZ/PGFPlots inside `manuscript/joint_cert_manuscript.tex` directly from the archived summary numbers; all **seven** external vector PDFs (`figures/supp_*.pdf`) included by `manuscript/joint_cert_manuscript.tex` are generated directly from the SHA-256-verified CSVs by `python experiment/run_all.py figures`:

| Manuscript Figure | File in `figures/` | Backing Suites | Plotter (`experiment/plots/`) |
|---|---|---|---|
| **Fig. 1** (Concept overview) | `fig1_concept_overview.png` (README banner) / TikZ in LaTeX | Analytic example (`examples/quickstart_cd_joint.py`) | — |
| **Fig. 2** (Overlap & proxy mechanisms) | TikZ in LaTeX | `exp1`, `e0` | `plot_v2_extensions.py`, `plot_v7_bayesian_ucd.py` |
| **Fig. 3** (Protein 3-regime comparison) | TikZ in LaTeX | `v14`, `v13` | `plot_v14_protein_credible_ellipsoid.py`, `plot_v13_protein_bed_vs_kg.py` |
| **Figs. 4–8** (App. G plots) | TikZ in LaTeX (detailed PDFs via `--all-suites`) | `v12`, `exp1`, `v8_3`, `exp8`, `exp10` | `plot_v12_bed_vs_bo.py`, `plot_v8_unified_figures.py`, `plot_v4_icml_baselines.py` |
| **Fig. 9** (App. H.3) | `figures/supp_protein_credibility_audit.pdf` | `v14` | `plot_supp_manuscript_figures.py` |
| **Fig. 10** (App. I) | `figures/supp_live_workflow_validation.pdf` | `v11_2` | `plot_supp_manuscript_figures.py` |
| **Fig. 11** (App. J.1) | `figures/supp_information_tracking.pdf` | `v8_2` | `plot_supp_manuscript_figures.py` |
| **Fig. 12** (App. J.2) | `figures/supp_protein_calibration_robustness.pdf` | `v8_1` | `plot_supp_manuscript_figures.py` |
| **Fig. 13** (App. J.3) | `figures/supp_eprocess_safety_and_compute.pdf` | `v9_3`, `v9_1` | `plot_supp_manuscript_figures.py` |
| **Fig. 14** (App. J.3) | `figures/supp_sparse_variance_tracking.pdf` | `v9_1`, `v9_2` | `plot_supp_manuscript_figures.py` |
| **Fig. 15** (App. L.5) | `figures/supp_native_solver_and_workflows.pdf` | `v10_1`, `v10_2`, `v10_3` | `plot_supp_manuscript_figures.py` |

Pass `--all-suites` to `python experiment/run_all.py figures --all-suites` to also generate every detailed per-suite diagnostic figure into `figures/detailed/`.

---

## 4. Verification Contracts

1. **Cryptographic integrity (`python experiment/run_all.py verify`).** Verifies SHA-256 digests of all 31 files in the frozen passive-UCT v1 archive (`results/uct_v1_manifest.json`) and every `manifest.json` across all 41 suites (`exp1`–`exp15`, `e0`–`e6`, `v8`–`v14`), asserting that no archived manifest was produced in `--smoke` mode.
2. **Automated unit, parity, API & oracle tests (`python experiment/run_all.py test`).** Executes all 88 tests across `tests/test_*.py`, covering the public `joint_root_cert` API, bit-exact C++17 vs. Python parity (correlated KG, certified B&B, graph-maintenance kernels, SameGame DP), exact minimax duality against CVXPY/Clarabel, Behrens–Fisher bimodal soundness, and disjoint WorFBench task splits.
3. **Non-destructive execution.** `verify`, `test`, `list`, and `benchmark --smoke` never modify `results/`. Individual scripts under `experiment/` also accept `--out-dir <path>` (or `--out <path>`), `--smoke`, `--summarize-only`, and `--workers <N>`.
4. **Deterministic trajectories vs. host-dependent timing.** All random seeds, paired noise tapes, query counts, certification decisions, and SHA-256 manifests are deterministic. Wall-clock latency and peak Python memory depend on host CPU and compiler flags.
