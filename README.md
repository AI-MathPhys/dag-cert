# Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs (`joint-root-cert`)

[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Python 3.10+](https://img.shields.io/badge/python-3.10%2B-blue.svg)](requirements-full.txt)
[![Manuscript](https://img.shields.io/badge/Manuscript-PDF-red.svg)](manuscript/Joint_cert_manuscript.pdf)

Research code, bundled datasets, archived run logs, and reproduction commands for **Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs**.

- **Manuscript:** [`manuscript/Joint_cert_manuscript.pdf`](manuscript/Joint_cert_manuscript.pdf) (LaTeX source: [`manuscript/joint_cert_manuscript.tex`](manuscript/joint_cert_manuscript.tex))
- **Artifact-to-paper map:** [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md) lists, table by table, which archived logs and which command back each result.
- **Coverage:** most of the paper is covered by archived, checksummed logs. A few results are not in this repository yet; see [Coverage and known gaps](#coverage-and-known-gaps) before relying on it for the headline comparison.

<p align="center">
  <img src="figures/fig1_concept_overview.png" width="94%" alt="Shared outcomes change what can invalidate a root decision"/>
</p>

*Shared outcomes change what can invalidate a root decision (the idea of Figure 1 in the paper): a terminal that the chosen action can still reach cannot count against it, so only excluded outcomes matter.*

---

## What the Paper Does

In sequential decision-making, an initial action can be optimal without its best continuation being known. Many search spaces are directed acyclic graphs: different action sequences reach the same outcome, so root actions have **overlapping sets of continuations**, and evidence about outcomes is often **correlated**.

The paper introduces **Joint Root Certification**: certify that a root action $a$ keeps access to an $\varepsilon$-optimal outcome.

> A commitment can be invalidated only by an *excluded* outcome that beats *every retained continuation* by more than $\varepsilon$ under the *same* plausible environment.

Marginal action-value comparisons evaluate competing actions under different plausible environments and keep an unnecessary gap on shared outcomes. The paper derives an exact sparse ellipsoidal minimax representation of this decision regret, shows that greedily sampling the active contrast can stall, and introduces **CD-Joint**, a safeguarded Bayesian experimental-design policy with finite-sample cost guarantees under fixed-feature models.

### Where the main ideas live in the code

| Paper concept | Implementation |
|---|---|
| All-MAX search DAG, terminal reward streams | [`dag_mcts/graph.py`](dag_mcts/graph.py) |
| Exact shared-support (rectangular) root regret, Hoeffding and empirical-Bernstein boxes | [`dag_mcts/v2_monitors.py`](dag_mcts/v2_monitors.py), [`dag_mcts/retired_bounds.py`](dag_mcts/retired_bounds.py) |
| Active exact-regret sampling, witness covers, Optimistic Separation (OS) | [`dag_mcts/v3_extensions.py`](dag_mcts/v3_extensions.py), [`dag_mcts/v5_hybrid_and_os.py`](dag_mcts/v5_hybrid_and_os.py) |
| Ellipsoidal conic regret, lazy column generation, characteristic-time solver | [`dag_mcts/v7_bayesian_ucd.py`](dag_mcts/v7_bayesian_ucd.py) |
| CD-Joint (contrast-directed joint acquisition), calibrated EB+LOO GP stopping, bounded-residual ellipsoids, information tracking | [`dag_mcts/v8_unified_experiments.py`](dag_mcts/v8_unified_experiments.py) |
| GP surrogate and BO acquisitions (GP-UCB, EI, Thompson, Root-Info) | [`dag_mcts/v6_bayesian_opt.py`](dag_mcts/v6_bayesian_opt.py) |
| Unknown-variance Gaussian tracking and certified branch-and-bound | [`dag_mcts/v9_v34_tracker.py`](dag_mcts/v9_v34_tracker.py), [`dag_mcts/_cpp_v34_bnb.cpp`](dag_mcts/_cpp_v34_bnb.cpp) |
| Passive UCT/PUCT certification and graph maintenance kernels | [`dag_mcts/search.py`](dag_mcts/search.py), [`dag_mcts/puct.py`](dag_mcts/puct.py), [`dag_mcts/_cpp_kernels.cpp`](dag_mcts/_cpp_kernels.cpp) |
| GB1, TmTrpB and WorFBench problem interfaces | [`dag_mcts/v6_real_world.py`](dag_mcts/v6_real_world.py) |

### Results in the paper that this repository's archives reproduce

| Paper location | Result | Archive |
|---|---|---|
| §3.1, Fig. 2a, Table 10 | Exact outside-support stopping needs $0.054\times$ the observations of marginal stopping at $M=256$, overlap $.88$ ($18.4\times$) | `results/uct_v2_extensions/exp1_exact_regret/` |
| §3.1, Fig. 2b, Table 11 | CD-Joint puts $76.8\%$ of queries on a low-valued proxy vs. $0.6\%$ for direct-witness sampling | `results/bayesian_ucd_v1/e0_and_toy/` |
| §3.1, Table 13 | Proxy-alignment and cost sweep, up to $48.5\times$ lower median cost | `results/bayesian_ucd_v1/v8_exp3_factorial_phase/` |
| §3.2, Table 27 | Empirical-Bayes protein study: terminal-wise coverage $91.5\%$ / $82.9\%$, root-regret-bound coverage $100\%$ over 410 campaigns | `results/bayesian_ucd_v1/v11_exp1_protein_validity_ablation/` |
| §3.3, Table 5 (offline), Table 35 | WorFBench offline: OS certifies $100\%$ in $1{,}937$ median evaluations | `results/uct_v4_icml_baselines/exp12_real_world/`, `exp13_real_world_validation/` |
| §3.3, Table 5 (live), Table 37, Fig. 10 | 36 fresh uncached Qwen3-0.6B campaigns: DF stopping $0/36$, EB+LOO $36/36$ in a median of $24$ evaluations | `results/bayesian_ucd_v1/v11_exp2_live_worfbench_36campaigns/` |
| App. L, Table 69 | Independent numerical-oracle audit, 5/5 pass | `results/bayesian_ucd_v1/v11_exp3_independent_oracle_audit/` |

---

## Coverage and Known Gaps

The archives here cover Tables 1, 5, 10–13, 15–23, 27–58 and 60–69 and Figures 2, 5–8 and 10–15 of the paper. The following are **not in this repository yet**:

| Paper content | Location in paper | Status |
|---|---|---|
| Matched-model acquisition benchmark: CD-Joint vs. correlated knowledge gradient, GP-OS, GP-UCB, Thompson, EI and Bayesian root-risk VOI under one Gaussian posterior and one stopping rule ($15{,}280$ runs). This is the headline $2.14\times$ result, the $1.65\times$ anytime-valid confirmation, and the $2.6$ ms latency crossover. | §3.1, Table 3; App. G.1, Tables 7–9, Fig. 4; Table 14; Table 59 | No code and no logs. No correlated-KG or root-risk-VOI implementation exists in `dag_mcts/`. |
| Matched protein acquisition benchmark on GB1 and TmTrpB ($12{,}300$ runs), including the joint-ellipsoid, direct posterior-risk and distribution-free regimes | §3.2, Fig. 3, Table 4; App. H.2 and H.4, Tables 25–26 | No code and no logs. |
| Rank-corrected credible ellipsoid ($\sqrt{\chi^2_{M-1,.95}}$) and coverage audit | §3.2; App. H.3, Table 24, Fig. 9 | No code and no logs. |
| Lean formalizations | AI Use and Reproducibility statements, supplementary introduction (`lean/`) | Directory absent. |
| Supplementary figure files `figures/supp_*.pdf` (Figs. 9–15) | App. H–L | The plotting scripts here write earlier layouts under different file names from the same archived data (Figs. 10–15); Fig. 9 has no data here. The LaTeX source therefore does not compile from this repository alone. |

The Reproducibility Statement in the current PDF still points to `github.com/AI-MathPhys/dag-cert`; this repository is `github.com/AI-MathPhys/joint-root-cert`.

---

## Quickstart

Tested on Python 3.12 / 3.13 (Linux and macOS; the pure-Python paths also run on Windows).

### 1. Clone and install

```bash
git clone https://github.com/AI-MathPhys/joint-root-cert.git
cd joint-root-cert

python3 -m venv .venv
source .venv/bin/activate   # Windows PowerShell: .\.venv\Scripts\Activate.ps1

python -m pip install -r requirements-full.txt
```

Optional extras:

- **Live uncached Qwen3-0.6B workflows** (`v8_5`, `v10_3`, `v11_2`): `python -m pip install -r requirements-live-llm.txt`
- **Native C++17 kernels** (`exp7`, SameGame playouts, branch-and-bound in `v9`/`v10`/`v11_3`): a `g++` or `clang++` on the path (or `$CXX`).
- **Minimal frozen environment** for `reproduce.py verify` only: `python -m pip install -r requirements.lock`

### 2. Verify archives and run the tests (about a minute)

```bash
# Bundled datasets, optional Hugging Face cache, C++17 compiler:
python scripts/fetch_data.py --check

# SHA-256 manifests of every archived experiment:
python -B reproduce.py verify
python -B reproduce_extensions.py verify
python -B reproduce_bayesian_ucd.py verify

# 72 unit tests (23 frozen UCT + 25 extension + 24 Bayesian/unknown-variance):
python -B reproduce_extensions.py test
python -B reproduce_bayesian_ucd.py test

# Minimal coupled certification demo:
python -B examples/certify.py
```

---

## Reproducing the Paper

Three command-line entry points cover the archived experiments. None of them overwrites `results/` during verification or smoke runs.

| Entry point | Suites | Scope |
|---|---|---|
| [`reproduce.py`](reproduce.py) | frozen UCT archive | Passive TA-UCT certification, selective pruning, strong-compiler timing and memory (1,920 runs; 3,826,797 rollout boundaries replayed) |
| [`reproduce_extensions.py`](reproduce_extensions.py) | `exp1`–`exp15` | Exact regret vs. marginal stopping, PUCT, SameGame, empirical Bernstein, active exact-regret sampling, C++ kernels, structured pure-exploration baselines, inside-witness ablations, GB1 / TmTrpB / WorFBench distribution-free studies, GP Bayesian optimization |
| [`reproduce_bayesian_ucd.py`](reproduce_bayesian_ucd.py) | `e0`–`e6`, `v8_1`–`v8_6`, `v9_1`–`v9_4`, `v10_1`–`v10_3`, `v11_1`–`v11_3` | Correlated conic regret and CD-Joint, calibration and misspecification, information tracking, unknown-variance tracking, native branch-and-bound, live LLM replication, independent oracle audit |

### Fast paths (minutes, CPU only)

```bash
# Frozen UCT archive: checksums, tests, tables and figures into build/
python -B reproduce.py quickcheck

# Regenerate all summary CSVs from archived JSONL logs
python -B reproduce_extensions.py summaries
python -B reproduce_bayesian_ucd.py summaries

# Regenerate figures from archived data
python -B reproduce_extensions.py figures --out build/figures_ext
python -B reproduce_bayesian_ucd.py figures --out build/figures_bayesian

# Smoke-run individual suites (writes to the OS temp directory)
python -B reproduce.py benchmark --smoke --out build/smoke-v1
python -B reproduce_extensions.py benchmark --smoke --only exp11
python -B reproduce_bayesian_ucd.py benchmark --smoke --only v11_3
```

### Paper section to suite

Table and figure numbers refer to the compiled manuscript PDF. The full table-by-table list is in [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md).

| Paper section | Tables / figures | Suite keys | Re-run command |
|---|---|---|---|
| §2.3 conic certificate cost; App. L.1 | Tables 1, 57, 58 | `e6`, `v8_4` | `python -B reproduce_bayesian_ucd.py benchmark --only e6` |
| §3.1 structural vs. statistical information; App. G.2–G.3 | Fig. 2, Tables 10–13, 15, Figs. 5–6 | `exp1`, `e0`, `e1`, `v8_3` | `python -B reproduce_extensions.py benchmark --only exp1` |
| App. G.4–G.5 independent-observation baselines, witness ablations, natural DAGs | Tables 16–23, Figs. 7–8 | `exp5`, `exp6`, `exp8`–`exp11`, `v8_6` | `python -B reproduce_extensions.py benchmark --only exp8` |
| §3.2 calibration and external validity; App. H.5 | Tables 27–28 | `v11_1`, `v8_1` | `python -B reproduce_bayesian_ucd.py benchmark --only v11_1` |
| App. H.6 extended GB1 / TmTrpB comparisons | Tables 29–34 | `exp12`–`exp14`, `e3` | `python -B reproduce_extensions.py benchmark --only exp12` |
| §3.3 agentic workflows; App. I | Table 5, Tables 35–39, Fig. 10 | `exp12`, `exp13`, `v8_5`, `v10_3`, `v11_2` | `python -B reproduce_bayesian_ucd.py benchmark --only v11_2` (needs `requirements-live-llm.txt`) |
| App. J.1–J.2 information tracking, calibration, bounded residuals | Tables 40–42, Figs. 11–12 | `v8_2`, `e5`, `v8_1` | `python -B reproduce_bayesian_ucd.py benchmark --only v8_2` |
| App. J.3–J.4 unknown variance, heteroscedastic bridge, cross-application validity | Tables 43–50, Figs. 13–14 | `v9_1`–`v9_4`, `v10_2`, `v11_1`, `exp12` | `python -B reproduce_bayesian_ucd.py benchmark --only v9_1` |
| App. J.5 passive UCT / PUCT / SameGame | Tables 51–56 | frozen UCT archive, `exp2`, `exp3` | `python -B reproduce.py replay --study all --out build/replay-01` |
| App. L.2–L.4 native kernels, compiler and memory protocols, representation selection | Tables 60–67 | `exp7`, frozen UCT archive, `exp2`–`exp4` | `python -B reproduce_extensions.py benchmark --only exp7` |
| App. L.5–L.6 native branch-and-bound, independent oracle audit | Tables 68–69, Fig. 15 | `v10_1`, `v11_3` | `python -B reproduce_bayesian_ucd.py benchmark --only v11_3` |
| §3.1 matched-model acquisition; §3.2 matched protein acquisition | Tables 3–4, 7–9, 14, 24–26, 59; Figs. 3–4, 9 | none | not in this repository (see [Coverage and known gaps](#coverage-and-known-gaps)) |

Individual scripts under `paper/exp_v8_*.py` through `paper/exp_v11_*.py` accept `--out-dir <path>`, `--smoke`, `--summarize-only` and `--workers <N>`, so any experiment can be re-run into `build/` without touching the archived manifests.

---

## External Data (`scripts/fetch_data.py`)

The four compact preprocessed `.npz` archives in `dag_mcts/data/` (1.7 MB) and the 20-board SameGame set are in Git, so verification, tests and CPU experiments run offline. Every upstream source can be downloaded and rebuilt:

| Dataset / asset | Upstream source | Bundled file | Rebuild command |
|---|---|---|---|
| GB1 (149,361 four-site variants; Wu et al. 2016) | [FLIP](https://github.com/J-SNACKKB/FLIP) | `dag_mcts/data/gb1_wu2016_measured.npz` | `python scripts/fetch_data.py --proteins` |
| TmTrpB (159,129 four-site variants; Johnston et al. 2024) | [Zenodo 15203754](https://zenodo.org/records/15203754) | `dag_mcts/data/trpb_johnston2024_measured.npz` | `python scripts/fetch_data.py --proteins` |
| WorFBench raw trajectories (4 domains) | [zjunlp/WorfBench](https://github.com/zjunlp/WorfBench) | cached to `dag_mcts/data/worfbench_raw/` | `python scripts/fetch_data.py --worfbench-tasks` |
| Qwen3-0.6B and Qwen3-Embedding-0.6B | Hugging Face Hub | local Hugging Face cache | `python scripts/fetch_data.py --models` |
| WorFBench 81×64 and 81×32 score matrices | generated from the two rows above | `dag_mcts/data/worfbench_qwen3_*.npz` | `python scripts/fetch_data.py --rebuild-worfbench` |

Use `--out-dir build/rebuilt_data` to rebuild next to the bundled files and compare, and `--all` to fetch everything. Set `HF_HUB_OFFLINE=1` after fetching the tasks and models to run the live suites without network access.

---

## Repository Structure

```text
joint-root-cert/
├── manuscript/                     # Paper PDF and LaTeX source
├── dag_mcts/                       # Core library (Python, native C++17 kernels, bundled data)
│   ├── graph.py                    # Finite all-MAX DAG and terminal reward streams
│   ├── retired_bounds.py           # Confidence intervals and strict retirement
│   ├── v2_monitors.py              # Hoeffding and empirical-Bernstein boxes, exact regret
│   ├── v3_extensions.py            # Active Exact-Regret-DAG-LUCB, C++17 ctypes bridge
│   ├── v4_baselines.py             # LUCB-micro, UGapE-MCTS, VarDE-DAG, SameGame, routing
│   ├── v5_hybrid_and_os.py         # DualWitnessCovers, Safeguarded-LCB, Optimistic Separation
│   ├── v6_real_world.py            # GB1, TmTrpB and WorFBench problems, Flat-LUCB controls
│   ├── v6_bayesian_opt.py          # GP surrogate, GP-UCB / EI / TS / Root-Info
│   ├── v7_bayesian_ucd.py          # Conic regret, column generation, characteristic time
│   ├── v8_unified_experiments.py   # CD-Joint, calibrated EB+LOO GP, information tracking
│   ├── v9_v34_tracker.py           # Unknown-variance tracker, branch-and-bound bridge
│   ├── _cpp_*.cpp                  # Native maintenance, SameGame and branch-and-bound kernels
│   └── data/                       # Bundled benchmark .npz files
├── paper/                          # Experiment runners (exp_*.py), dataset builders, plotters
├── results/                        # Archived, SHA-256-verified logs, summaries and manifests
├── reference/tables/               # Generated LaTeX tables for the passive UCT study
├── tests/                          # 72 unit, parity and oracle tests
├── examples/certify.py             # Minimal certification example
├── scripts/fetch_data.py           # Check, download and rebuild external data and models
├── appendix/                       # Separate earlier pricing/controller archive (not cited by this paper)
├── reproduce.py                    # Frozen UCT archive: verify, replay, tables, figures
├── reproduce_extensions.py         # exp1–exp15: verify, test, summaries, figures, benchmark
├── reproduce_bayesian_ucd.py       # e0–e6, v8–v11: verify, test, summaries, figures, benchmark
├── requirements-full.txt           # Full CPU dependencies
├── requirements-live-llm.txt       # Optional PyTorch / Transformers extras for live suites
├── requirements.txt / .lock        # Frozen minimal environment (hashed by artifact_manifest.json)
├── artifact_manifest.json          # Checksums of the frozen UCT archive
├── REPRODUCIBILITY.md              # Table-by-table artifact map and verification contracts
└── VALIDATION.md                   # Protocol notes for the frozen UCT archive
```

The `vN` prefixes in module and suite names are development stages of the codebase, not paper sections; the tables above and `REPRODUCIBILITY.md` give the correspondence.

---

## Interpretation and Statistical Scope

- **Validity depends on the stopping model.** Bounded-observation Hoeffding and empirical-Bernstein boxes are distribution-free; fixed-feature and Gaussian confidence sequences rely on their model; bounded-residual ellipsoids require a misspecification bound $|b|\le\xi$; calibrated EB+LOO stopping is model-based and does not inherit distribution-free validity (Table 2 and App. C of the paper).
- **Protein experiments** simulate noisy assays against published GB1 and TmTrpB fitness measurements; no new wet-lab experiments were run. **Live workflow experiments** run fresh uncached Qwen3-0.6B inference on task pools disjoint from calibration.
- **Timing.** Wall-clock times and wall-capped completion counts depend on the host; statistical trajectories, operation counts and SHA-256 manifests are deterministic.
