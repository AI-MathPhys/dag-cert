# Reproduction Scope & Verification Contracts

This document maps every claim, table, and figure in **Shared-Support and Bayesian Certification in Search Graphs** ([`manuscript/DAG_Cert_manuscript.pdf`](manuscript/DAG_Cert_manuscript.pdf)) to its reproducible inputs, checksummed logs, and verification commands.

## 1. Environment & Data Independence

- All source and data paths are strictly repository-relative; no external workstation paths, private caches, or `fuse` mounts are used.
- Compact preprocessed benchmark archives (`dag_mcts/data/`, 1.7 MB) and SameGame boards (`appendix/data/samegame/StandardTestset.txt`) are bundled in Git so all offline verification, unit tests, and CPU experiments work out of the box.
- Every upstream public dataset and model (FLIP GB1, Zenodo 15203754 TmTrpB, `zjunlp/WorfBench` 4-domain gold trajectories, `Qwen/Qwen3-0.6B`, and `Qwen/Qwen3-Embedding-0.6B`) can be downloaded and rebuilt from scratch on any machine via `python scripts/fetch_data.py`.
- Frozen v1 dependency files (`requirements.txt`, `requirements.lock`) and `reproduce.py` remain byte-identical to `artifact_manifest.json` (source provenance commit `58fbd2e86031a2d90b289e10d232335f80132772`). Use `requirements-full.txt` for all v1–v11 CPU suites and `requirements-live-llm.txt` for optional uncached live `Qwen3-0.6B` runs.

## 2. Complete Artifact-to-Manuscript Map

### Correlation-Aware, Unknown-Variance V34, C++17 B&B, Live LLM & Pre-Submission Audit Suites (`reproduce_bayesian_ucd.py`)

| Manuscript Evidence | Archived Inputs (`results/bayesian_ucd_v1/`) | Verification & Reproduction |
|---|---|---|
| Core conic regret, overlap × correlation phase, hull/proxy geometry, initial proteins & WorFBench, scaling (`E0`–`E6`, App. O) | `e0_and_toy/` .. `e6_scaling/` | `reproduce_bayesian_ucd.py verify`, `benchmark --only e0`..`e6` |
| Calibrated proteins, 500-rep rough-GP cure & $(\xi,\varepsilon)$ frontier (Fig. 4, App. O) | `v8_exp1_calibrated_proteins/` | `benchmark --only v8_1` |
| Decision-aware Info-Tracking vs. `CD-Joint` & exact $T_*^\varepsilon$ verification (Fig. 3, App. O) | `v8_exp2_info_tracking/` | `benchmark --only v8_2` |
| Deconfounded $4\times 4\times 3$ overlap × correlation × mismatch factorial & proxy sweep (App. O) | `v8_exp3_factorial_phase/` | `benchmark --only v8_3` |
| Amortized conic update schedules ($M\le 4096$) & wall-clock break-even frontier (Fig. 3, App. O) | `v8_exp4_compute_breakeven/` | `benchmark --only v8_4` |
| 3-way disjoint WorFBench offline generalization ($n=200$) & initial live `Qwen3-0.6B` proof-of-concept (Table 2, App. O) | `v8_exp5_fresh_worfbench_live/` | `benchmark --only v8_5` |
| Hard-regime adaptive sampling on 20 mid-game SameGame boards & Tied-Star (App. O) | `v8_exp6_adaptive_samegame/` | `benchmark --only v8_6` |
| Unknown-variance V34 vs. V33 sparse four-power refresh & action-local evidence ($K\le 64$, Fig. 3, App. P) | `v9_exp1_v34_vs_v33_dag/` | `benchmark --only v9_1` |
| Heteroscedastic Gaussian information efficiency ($\delta\in[10^{-8},.10]$, App. P) | `v9_exp2_heteroscedastic_info/` | `benchmark --only v9_2` |
| Multi-answer switching, IUT vs. Bonferroni, null wealth & Behrens–Fisher global audit (App. P) | `v9_exp3_switching_and_safety/` | `benchmark --only v9_3` |
| Certified global B&B solver cost of validity ($d\in\{2,4,6\}$, App. P) | `v9_exp4_solver_cost_of_validity/` | `benchmark --only v9_4` |
| Native `-O3` C++17 outward-certified B&B scaling up to $d=8$ (App. Q, Fig. 8a) | `v10_exp1_cpp_v34_scaling/` | `benchmark --only v10_1` |
| Real heteroscedastic GB1 (Wu et al. shot noise) & WorFBench V34 bridge + raw misspec. audit (Table 2, App. Q, Table 50) | `v10_exp2_real_heteroscedastic_v34/` | `benchmark --only v10_2` |
| Expanded 8-campaign (24-run) live `Qwen3-0.6B` ToolAlpaca cohort (App. Q, Table 51) | `v10_exp3_live_worfbench_expanded/` | `benchmark --only v10_3` |
| **P0**: Real-data certificate-validity ablation & coupled-stream replay on raw GB1 ($200$) & TmTrpB ($210$) (Table 2, App. R, Table 52, Fig. 9a–b) | `v11_exp1_protein_validity_ablation/` | `benchmark --only v11_1` |
| **P1**: 36-campaign 4-domain fresh uncached live `Qwen3-0.6B` WorFBench replication (Table 2, App. R, Table 53, Fig. 9c) | `v11_exp2_live_worfbench_36campaigns/` | `benchmark --only v11_2` |
| **P2**: Zero-shared-code independent numerical-oracle verification audit (`5/5 PASS`, App. R, Table 54) | `v11_exp3_independent_oracle_audit/` | `benchmark --only v11_3` |

### Independent-Terminal, Active `DAG-LUCB`, External Baselines & BO Suites (`reproduce_extensions.py`)

| Manuscript Evidence | Archived Inputs | Verification & Reproduction |
|---|---|---|
| Exact shared-support regret, PUCT transfer, deeper SameGame, representation selector (`exp1`–`exp4`) | `results/uct_v2_extensions/` | `reproduce_extensions.py verify`, `benchmark --only exp1`..`exp4` |
| Empirical Bernstein, active `Exact-Regret-DAG-LUCB`, native C++17 kernel parity (`exp5`–`exp7`) | `results/uct_v3_strengthening/` | `benchmark --only exp5`..`exp7` |
| External BAI baselines (`LUCB-micro`, `UGapE-MCTS`, `VarDE-DAG`), mid-game SameGame, inside-witness, `DualWitnessCovers`/`OS`, GB1/TmTrpB/WorFBench, GP BO & RKHS ellipsoids (`exp8`–`exp15`) | `results/uct_v4_icml_baselines/` | `benchmark --only exp8`..`exp15` |

### Frozen v1 UCT Archive & Historical Appendix (`reproduce.py`)

| Manuscript Evidence | Inputs | Reproduction |
|---|---|---|
| Original on-policy certification and regret | `results/uct_backup_v1/runs.jsonl` | `reproduce.py summaries`, `replay --study backup` |
| Fixed-accuracy gap follow-up | `results/uct_backup_v1/gap-study/` | Same commands |
| Strong shared compiler, noisy overlapping supports, SameGame and controls | `results/uct_frontier_v1/` | `summaries`, `replay --study frontier` |
| Initial/cumulative frontier work and retirement | `results/uct_frontier_v1/mechanism.jsonl` | `reproduce.py mechanism` |
| Peak Python allocated memory | `results/uct_frontier_v1/memory.jsonl` | `reproduce.py memory` (host-dependent) |
| Three UCT figure PDFs & five UCT tables | Primary and frontier summary CSVs | `reproduce.py figures`, `reproduce.py tables` |
| Historical pricing figures & ancestor-repair/batching summaries | `appendix/results/` | `reproduce.py figures --appendix`, `reproduce.py appendix-check --out build/appendix-01` |

## 3. Verification & Safety Guarantees

- **Non-destructive verification and smoke runs:** `verify`, `test`, `quickcheck`, `appendix-check`, and `benchmark --smoke` write only to `build/` or the OS temporary directory (`--smoke-dir`) and never modify archived manifests under `results/`.
- **Exact deterministic replay vs. hardware-dependent timings:** Full v1 replay checks **3,826,797** rollout boundaries against independent full-DP checks. On a new machine, fresh runs preserve seeds, method ordering, accuracy, confidence, and evaluation caps; wall-clock seconds, memory usage, and wall-capped completion rates depend on host hardware and should not be compared as paired wall-time measurements against archived runs.
- **Historical pricing archive (`appendix/`):** Isolated from the main UCT/DAG-certification evidence; first run `python -B reproduce.py appendix-check --out build/appendix-01` and execute any additional historical commands from `build/appendix-01/` (see `appendix/ORIGINAL_REPLAY_README.txt`).
