# Reproduction Scope and Verification Contracts

This document maps the tables and figures of **Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs** ([`manuscript/Joint_cert_manuscript.pdf`](manuscript/Joint_cert_manuscript.pdf)) to archived logs and commands. Table and figure numbers are those of the compiled PDF; appendix letters are A–L (G synthetic experiments, H proteins, I workflows, J extended validation, K algorithms, L computational performance).

## 1. Environment and Data

- All source and data paths are repository-relative.
- Compact benchmark archives (`dag_mcts/data/`, 1.7 MB) and SameGame boards (`appendix/data/samegame/StandardTestset.txt`) are bundled in Git, so verification, unit tests and CPU experiments run offline.
- Every upstream dataset and model (FLIP GB1, Zenodo 15203754 TmTrpB, `zjunlp/WorfBench` gold trajectories, `Qwen/Qwen3-0.6B`, `Qwen/Qwen3-Embedding-0.6B`) can be downloaded and rebuilt with `python scripts/fetch_data.py`.
- `requirements.txt`, `requirements.lock` and `reproduce.py` are hashed by `artifact_manifest.json` and must stay byte-identical (source provenance in `provenance.json`). Use `requirements-full.txt` for all CPU suites and `requirements-live-llm.txt` for the live Qwen3-0.6B runs.

## 2. Results Not Covered by This Repository

| Paper content | Tables / figures | Missing |
|---|---|---|
| Matched-model acquisition benchmark (CD-Joint vs. correlated KG, GP-OS, GP-UCB, TS, EI, Bayesian root-risk VOI; $15{,}280$ runs), including the cost-sensitive proxy benchmark and the derived latency crossover | Tables 3, 7, 8, 9, 14, 59; Fig. 4 | code and logs |
| Matched protein acquisition benchmark on GB1 and TmTrpB ($12{,}300$ runs), regimes A and B, direct posterior-risk stopping | Table 4, Fig. 3, Tables 25, 26 | code and logs |
| Rank-corrected joint credible ellipsoid and coverage audit | Table 24, Fig. 9 | code and logs |
| Lean formalizations (`lean/`) | AI Use and Reproducibility statements | directory |
| Supplementary figure files `figures/supp_*.pdf` | Figs. 9–15 | the plotters here write earlier layouts under other names; data for Figs. 10–15 is archived |

Tables 2 and 6 are conceptual (validity regimes) and need no data.

## 3. Artifact-to-Manuscript Map

### Correlated, unknown-variance, native-solver, live-LLM and audit suites (`reproduce_bayesian_ucd.py`)

Archives are under `results/bayesian_ucd_v1/`. Re-run any row with `python -B reproduce_bayesian_ucd.py benchmark --only <key>`.

| Key | Manuscript evidence | Archive |
|---|---|---|
| `e0` | Off-witness proxy benchmark (Fig. 2b, Table 11) | `e0_and_toy/` |
| `e1` | $4\times4$ overlap × correlation phase diagram (Table 12) | `e1_phase_diagram/` |
| `e2` | Feature-hull, proxy and multi-answer geometry checks (supports App. A.4; no table) | `e2_geometry_and_proxy/` |
| `e3` | GB1 stratum breakdown and 21-template TmTrpB (Table 34) | `e3_proteins/` |
| `e4` | Initial correlated WorFBench study (superseded by `v8_5`; no table) | `e4_worfbench/` |
| `e5` | Calibration and misspecification grid (Table 41) | `e5_calibration/` |
| `e6` | Conic solver scaling (Tables 1, 57) | `e6_scaling/` |
| `v8_1` | Calibrated protein certification (Table 28); calibration cure and $(\xi,\varepsilon)$ frontier (Table 42, Fig. 12) | `v8_exp1_calibrated_proteins/` |
| `v8_2` | Information tracking vs. CD-Joint (Table 40, Fig. 11) | `v8_exp2_info_tracking/` |
| `v8_3` | Proxy alignment × cost sweep (Table 13); deconfounded overlap × correlation × mismatch factorial (Table 15, Fig. 6) | `v8_exp3_factorial_phase/` |
| `v8_4` | Amortized conic update schedules and break-even latency (Table 58) | `v8_exp4_compute_breakeven/` |
| `v8_5` | WorFBench unseen-task generalization and first live run (Table 39) | `v8_exp5_fresh_worfbench_live/` |
| `v8_6` | Hard-regime adaptive sampling on SameGame, Tied-Star, Decoy, Hetero (Table 22) | `v8_exp6_adaptive_samegame/` |
| `v9_1` | Square vs. sparse refresh × all-action vs. action-local evidence (Table 43, Fig. 14a) | `v9_exp1_v34_vs_v33_dag/` |
| `v9_2` | Unknown heteroscedastic variance efficiency (Table 44) | `v9_exp2_heteroscedastic_info/` |
| `v9_3` | Multi-answer switching, intersection–union budgeting, null-boundary safety (Table 45, Fig. 13) | `v9_exp3_switching_and_safety/` |
| `v9_4` | Cost of certified global validity (Table 46) | `v9_exp4_solver_cost_of_validity/` |
| `v10_1` | Native C++17 branch-and-bound scaling (Table 68, Fig. 15a) | `v10_exp1_cpp_v34_scaling/` |
| `v10_2` | Heteroscedastic bridge on GB1 and WorFBench (Table 47, Figs. 14b, 15b) | `v10_exp2_real_heteroscedastic_v34/` |
| `v10_3` | Eight-campaign live Qwen3-0.6B cohort (Table 38, Fig. 15c) | `v10_exp3_live_worfbench_expanded/` |
| `v11_1` | Protein certificate-validity factorial and coupled-stream replay (Table 27; inputs to Tables 49–50; §3.2 coverage figures) | `v11_exp1_protein_validity_ablation/` |
| `v11_2` | 36-campaign live Qwen3-0.6B replication (Table 5 live rows, Table 37, Fig. 10) | `v11_exp2_live_worfbench_36campaigns/` |
| `v11_3` | Independent numerical-oracle audit (Table 69) | `v11_exp3_independent_oracle_audit/` |

### Independent-observation, baseline and application suites (`reproduce_extensions.py`)

Re-run any row with `python -B reproduce_extensions.py benchmark --only <key>`.

| Key | Manuscript evidence | Archive |
|---|---|---|
| `exp1` | Exact vs. marginal stopping across overlap (Fig. 2a, Table 10, Fig. 5) | `results/uct_v2_extensions/exp1_exact_regret/` |
| `exp2` | Root-PUCT and noisy recursive PUCT (Tables 55, 64) | `results/uct_v2_extensions/exp2_puct/` |
| `exp3` | SameGame lookahead (Tables 56, 65) | `results/uct_v2_extensions/exp3_samegame/` |
| `exp4` | Representation comparison and selector (Tables 66, 67) | `results/uct_v2_extensions/exp4_representation/` |
| `exp5` | Hoeffding vs. empirical-Bernstein boxes (Table 16) | `results/uct_v3_strengthening/exp5_emp_bernstein/` |
| `exp6` | Active witness allocation (Table 17) | `results/uct_v3_strengthening/exp6_dag_lucb/` |
| `exp7` | Native maintenance kernels (Tables 60, 61) | `results/uct_v3_strengthening/exp7_cpp_kernels/` |
| `exp8` | Structured pure-exploration baselines, $2\times2$ sampler × certificate (Table 18, Fig. 7) | `results/uct_v4_icml_baselines/exp8_external_baselines/` |
| `exp9` | Containment-stratified SameGame and routing DAGs (Table 23) | `results/uct_v4_icml_baselines/exp9_samegame_midgame/` |
| `exp10` | Inside-witness selection ablation (Table 19, Fig. 8) | `results/uct_v4_icml_baselines/exp10_inside_witness/` |
| `exp11` | DualWitnessCovers hybrid and tied-star family (Tables 20, 21) | `results/uct_v4_icml_baselines/exp11_hybrid_and_os/` |
| `exp12` | GB1 templates and panel sweep; WorFBench factorial (Tables 29, 30, 35, 48; Table 5 offline rows) | `results/uct_v4_icml_baselines/exp12_real_world/` |
| `exp13` | GB1 noise models, TmTrpB, WorFBench overlap sweep and first live audit (Tables 31, 36) | `results/uct_v4_icml_baselines/exp13_real_world_validation/` |
| `exp14` | Bayesian optimization vs. exact-regret sampling on GB1 (Tables 32, 33) | `results/uct_v4_icml_baselines/exp14_gb1_bayesian_opt/` |
| `exp15` | BO correlation and misspecification study (archived; not tabulated in this paper) | `results/uct_v4_icml_baselines/exp15_bo_correlation_and_misspec/` |

### Frozen passive-UCT archive (`reproduce.py`)

| Manuscript evidence | Inputs | Reproduction |
|---|---|---|
| Coupled UCT certification and anytime regret (Tables 52–54) | `results/uct_backup_v1/runs.jsonl` | `reproduce.py summaries`, `replay --study backup` |
| Stopping-horizon intervention (Table 51) | `results/uct_backup_v1/gap-study/` | same commands |
| Strong-compiler timing (Table 62) | `results/uct_frontier_v1/` | `summaries`, `replay --study frontier` |
| Frontier work and retirement | `results/uct_frontier_v1/mechanism.jsonl` | `reproduce.py mechanism` |
| Peak Python memory (Table 63) | `results/uct_frontier_v1/memory.jsonl` | `reproduce.py memory` (host-dependent) |
| Generated LaTeX tables | `reference/tables/` | `reproduce.py tables` |

The `appendix/` directory is a separate earlier pricing/controller archive. It is not cited by this paper; `reproduce.py appendix-check --out build/appendix-01` verifies it (see `appendix/ORIGINAL_REPLAY_README.txt`).

## 4. Verification Guarantees

- **Non-destructive.** `verify`, `test`, `quickcheck`, `appendix-check` and `benchmark --smoke` write only to `build/` or the OS temporary directory and never modify `results/`.
- **Deterministic replay vs. host-dependent timing.** The frozen replay checks 3,826,797 rollout boundaries against independent full dynamic-programming checks. Fresh runs preserve seeds, method order, accuracy, confidence and evaluation caps; wall-clock seconds, memory and wall-capped completion rates depend on the host and should not be compared pairwise with archived runs.
