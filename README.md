# Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs (`dagcert`)

[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Python 3.10+](https://img.shields.io/badge/python-3.10%2B-blue.svg)](pyproject.toml)
[![Manuscript](https://img.shields.io/badge/Manuscript-PDF-red.svg)](manuscript/Joint_cert_manuscript.pdf)
[![Lean 4](https://img.shields.io/badge/Formalization-Lean%204-purple.svg)](lean/)

Installable Python library (`dagcert`), full experimental suite (`experiment/`), bundled benchmark datasets, SHA-256-verified run archives (`results/`), Lean 4 formalizations (`lean/`), and complete reproduction scripts for **Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs**.

- **Manuscript:** [`manuscript/Joint_cert_manuscript.pdf`](manuscript/Joint_cert_manuscript.pdf) (LaTeX source: [`manuscript/joint_cert_manuscript.tex`](manuscript/joint_cert_manuscript.tex))
- **Artifact-to-paper map:** [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md) maps every table (Tables 1–69) and figure (Figures 1–15) to its archived logs and reproduction command — **100% coverage with zero missing experiments**.
- **Formal mathematics:** [`lean/`](lean/) contains Lean 4 proofs of 10 of the paper's 62 numbered results, including both main-text theorems; see [`lean/README.md`](lean/README.md) for the status of each.

<p align="center">
  <img src="figures/fig1_concept_overview.png" width="94%" alt="Shared outcomes change what can invalidate a root decision"/>
</p>

*Shared outcomes change what can invalidate a root decision (Figure 1 of the manuscript): a terminal that the chosen action can still reach cannot count against it, so only excluded outcomes matter.*

---

## Overview

In sequential decision-making, an initial commitment can be certified as $\varepsilon$-optimal long before its best full continuation is known. Many real search spaces — combinatorial protein design, agentic workflow configuration, routing, and puzzle lookahead — are **directed acyclic graphs (DAGs)** in which different action sequences reach overlapping terminal sets, and evidence about terminal outcomes is **statistically correlated**.

**Joint Root Certification** directly certifies that a root action $a$ retains access to an $\varepsilon$-optimal terminal outcome:

> A commitment can be invalidated only by an *excluded* terminal $z \notin S(a)$ that beats *every retained continuation* $y \in S(a)$ by more than $\varepsilon$ under the *same* plausible environment.

Key methodological contributions implemented in `dagcert`:

1. **Structural sharing (exact outside-support regret):** Evaluating all outcomes under a single common environment cancels shared continuations, replacing loose marginal action-value bounds with exact outside-vs-inside certificates.
2. **Statistical sharing (sparse ellipsoidal dual & CD-Joint):** Under correlated Gaussian or fixed-feature uncertainty sets, worst-case decision regret admits an exact sparse conic dual (supported on at most $d+1$ inside witnesses). **CD-Joint** (Contrast-Directed Joint acquisition) targets the variance of the active outside–inside contrast, exploiting even low-valued but informative off-witness proxies while safeguarding against inside-witness stalling.
3. **Stopping-regime awareness:** The library supports matched Bayesian joint credible ellipsoids (with exact contrast rank $r = \operatorname{rank}(\text{contrast } \Sigma)$ and radius $\sqrt{\chi^2_{r,1-\delta}}$), direct posterior-risk stopping, anytime-valid fixed-feature ellipsoids, unknown-variance sparse-refresh tracking (V34) with native C++17 outward-certified branch-and-bound, calibrated EB+LOO GP stopping, and formal distribution-free (Hoeffding / Empirical Bernstein) confidence boxes.

---

## Installation & Python Library Quickstart

Tested on Python 3.10–3.13 (Linux and macOS; pure-Python paths also run on Windows).

### 1. Install `dagcert`

```bash
git clone https://github.com/AI-MathPhys/dagcert.git
cd dagcert

python3 -m venv .venv
source .venv/bin/activate   # Windows PowerShell: .\.venv\Scripts\Activate.ps1

# Core library (numpy, scipy, matplotlib, requests)
python -m pip install -e .

# Optional extras:
python -m pip install -e ".[dev,audit]"   # pytest + CVXPY/Clarabel independent oracle audits
python -m pip install -e ".[all]"         # adds PyTorch / Transformers for live Qwen3-0.6B suites
```

> **Native C++17 accelerators (optional, automatic):** If `g++` or `clang++` (or `$CXX`) is on `PATH`, the library automatically compiles and caches four `-O3` C++17 shared libraries in `dagcert/_native/` (exact correlated KG, outward-certified branch-and-bound for unknown-variance tracking, graph-maintenance kernels, and SameGame playouts). Every accelerator has a bit-parity pure-Python fallback.

### 2. Minimal Library Usage

```python
import numpy as np
from dagcert import (
    SearchDAG,
    certify_root_action,
    exact_rectangular_regret,
)

# 1. Exact shared-support rectangular certificate (Figure 1b)
# Root action 0 reaches {0, 1}; root action 1 reaches {1, 2}. Shared terminal 1 cancels!
dag = SearchDAG.from_supports([{0, 1}, {1, 2}])
lo = np.array([0.72, 0.40, 0.30])
hi = np.array([0.80, 0.95, 0.55])
best_a, min_reg, regrets = exact_rectangular_regret(dag, lo, hi)
print(f"Best root action: {best_a}, exact regrets: {regrets.tolist()}")
# -> Best root action: 0, exact regrets: [0.0, 0.4]

# 2. Decision-aware Bayesian experimental design (CD-Joint vs. GP-OS vs. Correlated KG)
rng = np.random.default_rng(7)
dag = SearchDAG.from_supports([{0, 1, 2, 3}, {2, 3, 4, 5}, {4, 5, 6, 7}])
features = rng.normal(size=(8, 4))
kernel = features @ features.T + 0.05 * np.eye(8)
true_means = np.array([0.78, 0.72, 0.55, 0.50, 0.48, 0.42, 0.40, 0.35])

for policy in ("cd_joint", "gp_os", "kg"):
    noise = np.random.default_rng(123)
    res = certify_root_action(
        dag=dag,
        observe_fn=lambda z, r=noise: float(true_means[z] + r.normal(0.0, 0.15)),
        kernel=kernel,
        prior_mean=0.5,
        obs_std=0.15,
        policy=policy,
        stopping="credible_ellipsoid",   # rank-corrected sqrt(chi2_{r, 1-delta})
        epsilon=0.03,
        delta=0.05,
        max_evals=500,
    )
    print(f"{policy:9s} | certified={res.certified} | action={res.action} | evals={res.steps}")
```

### 3. Library Architecture (`dagcert/`)

| Module | Paper Concepts | Key Public Exports |
|---|---|---|
| [`dagcert/graph.py`](dagcert/graph.py) | Finite all-MAX search DAG, shared root supports, support overlap | `SearchDAG` (`.from_supports`, `.root_supports`, `.root_regrets`, `.support_overlap_matrix`), `DAG`, `Problem`, `SupportStructure` |
| [`dagcert/certificates.py`](dagcert/certificates.py) | Exact rectangular regret, conic ellipsoidal dual, dual witness covers, bounded residuals | `exact_rectangular_regret`, `JointEllipsoidCertifier`, `check_ellipsoid_stopping`, `DualWitnessCovers`, `CanonicalIntervals`, `NestedIntervals`, `RobustAwareJointCertifier` |
| [`dagcert/posteriors.py`](dagcert/posteriors.py) | Conjugate Gaussian posterior, contrast rank $r$, $\sqrt{\chi^2_{r,1-\delta}}$, valid anytime posterior-risk MC | `SharedGaussianPosterior`, `contrast_rank_of_kernel`, `chi2_credible_beta`, `contrast_ellipsoid_coverage`, `eval_direct_posterior_risk_valid` |
| [`dagcert/acquisition.py`](dagcert/acquisition.py) | Decision-aware BED & BO baselines under matched posteriors | `certify_root_action`, `MatchedModelBEDSession`, `CDJointPolicy`, `CorrelatedKGPolicy`, `GPOSPolicy`, `BayesianVOIPolicy`, `GPUCBPolicy`, `GPTSPolicy`, `NoisyGPEIPolicy` |
| [`dagcert/tracking.py`](dagcert/tracking.py) | Optimal information tracking ($T_*^\varepsilon$), unknown-variance sparse V34 tracker | `RegularizedInfoTrackerSession`, `run_v34_tracker`, `CppV34BnBRunner`, `compute_characteristic_rate`, `solve_action_design_certified` |
| [`dagcert/search.py`](dagcert/search.py) | Passive trajectory-coupled UCT/PUCT certification monitors | `TrajectoryCoupledUCT`, `RootPUCT`, `RecursivePUCT`, `CertifiedSearchSession`, `CppKernelRunner` |
| [`dagcert/benchmarks/`](dagcert/benchmarks/) | Bundled synthetic, GB1/TmTrpB protein, WorFBench workflow & SameGame DAG loaders | `OverlapCorrelationDAGProblem`, `OffWitnessProxyDAGProblem`, `GB1MutationCampaignProblem`, `TrpBMutationCampaignProblem`, `WorFBenchWorkflowProblem`, `load_standard_samegame_boards` |
| [`dagcert/_native/`](dagcert/_native/) | Optional auto-compiled `-O3` C++17 accelerators | `_cpp_v12_kg.cpp`, `_cpp_v34_bnb.cpp`, `_cpp_kernels.cpp`, `_cpp_samegame.cpp` |

Standalone runnable library examples live in [`examples/`](examples/):

```bash
python examples/quickstart_cd_joint.py   # Fig. 1b + CD-Joint vs. GP-OS vs. KG + distribution-free
python examples/correlated_proxy.py      # Low-valued off-witness proxy allocation (Fig. 2b)
python examples/protein_dag_demo.py      # GB1 combinatorial mutation DAG certification
python examples/certify.py               # Trajectory-coupled passive UCT monitor parity
```

---

## Headline Paper Results (Complete Coverage)

Every main-paper and appendix result is backed by executable code in `experiment/` and SHA-256-verified logs in `results/`.

| Paper Location | Finding | Domain & Suite |
|---|---|---|
| §2.3, Table 1 | Lazy conic certificate updates scale from $0.70\text{ ms}$ ($M=64$) to $25.7\text{ ms}$ ($M=4{,}096$) | `simulated` (`e6`) |
| §3.1, Table 3; App. G.1 (Tables 7–9, Fig. 4) | Matched-model $M=64, K=8$ factorial: CD-Joint needs **$2{,}358$** vs. Correlated KG **$5{,}056$** capped evals (**$2.14\times$** reduction; $2.53\times$ with overlap + correlation); **$1.65\times$** under anytime-valid $d=8$ frequentist stopping | `simulated` (`v12`) |
| §3.1, Fig. 2a, Table 10 | Exact outside-support stopping needs **$0.054\times$** the queries of marginal stopping at $M=256$, overlap $.88$ (**$18.4\times$**) | `simulated` (`exp1`) |
| §3.1, Fig. 2b, Tables 11 & 13 | CD-Joint routes **$76.8\%$** of queries to a low-valued proxy vs. **$0.6\%$** for direct-witness sampling; up to **$48.5\times$** lower median cost | `simulated` (`e0`, `v8_3`) |
| §3.2, Fig. 3, Table 4; App. H (Tables 24–26, Fig. 9) | 410 paired GB1 ($n=200$) & TmTrpB ($n=210$) campaigns: under rank-corrected $\sqrt{\chi^2_{r,.95}}$ ellipsoid, CD-Joint needs **$17{,}678$** [70%] / **$3{,}629$** [100%] assays vs. KG **$25{,}000^*$** [0%] / **$9{,}337$** [85.7%] (**$2.57\times$** on TmTrpB); ranking reverses under direct posterior risk (KG **$130$/$63$** vs. CD-Joint **$240$/$92$**) and independent-arm DF ($0\%$ for GP-only CD-Joint) | `protein_engineering` (`v14`, `v13`) |
| §3.2, Table 27 | Empirical-Bayes protein audit: simultaneous terminal coverage $91.5\%$ / $82.9\%$, yet **$100\%$** root-regret-bound coverage across 410 campaigns | `protein_engineering` (`v11_1`) |
| §3.3, Table 5 (offline), Table 35 | WorFBench offline ($3^4=81$ workflows): OS certifies **$100\%$** in **$1{,}937$** median evals ($0.95\text{ M}$ tokens) vs. Flat-LUCB **$8{,}486$** ($4.78\text{ M}$ tokens) at identical held-out $F_1 = 0.529$ | `agentic_workflows` (`exp12`) |
| §3.3, Table 5 (live), Table 37, Fig. 10 | 36 fresh uncached Qwen3-0.6B campaigns across 4 domains: formal DF stops **$0/36$** by 60 evals; model-based EB+LOO certifies **$36/36$** in median **$24$** evals (**$14{,}291$** tokens, held-out $F_1 = 0.4717$) | `agentic_workflows` (`v11_2`) |
| App. J.3, Table 43, Fig. 14a | Unknown-variance sparse-refresh + action-local IUT tracker (V34): **$50.4\times$** speedup at $K=64$, rank 2 ($34.0\text{ s} \to 0.675\text{ s}$) | `simulated` (`v9_1`) |
| App. L.5–L.6, Tables 68–69, Fig. 15 | Native C++17 outward-certified B&B achieves **$31$–$82\times$** end-to-end speedup; zero-shared-code independent numerical-oracle audit passes **$5/5$** checks | `simulated` (`v10_1`, `v11_3`) |

---

## Reproducing the Paper (`experiment/`)

All experiments rely directly on the installed `dagcert` package and are organized into three domain folders mirroring Section 3 of the paper, plus unified plotting (`experiment/plots/`) and CLI (`experiment/run_all.py`):

- [`experiment/simulated/`](experiment/simulated/) — Section 3.1 + Appendices G, J, L (27 suites + `passive_uct/` v1 archive)
- [`experiment/protein_engineering/`](experiment/protein_engineering/) — Section 3.2 + Appendix H (10 GB1 & TmTrpB suites)
- [`experiment/agentic_workflows/`](experiment/agentic_workflows/) — Section 3.3 + Appendix I (WorFBench offline & live Qwen3-0.6B suites)
- [`experiment/plots/`](experiment/plots/) — Manuscript supplementary figures (`figures/supp_*.pdf`) and detailed suite figures

### Fast Verification (~2 minutes, CPU only, offline)

```bash
# 1. Check bundled datasets, optional Hugging Face cache, and C++17 compiler
python scripts/fetch_data.py --check

# 2. Cryptographically verify SHA-256 manifests for ALL archived suites (v1--v14, zero gaps)
python experiment/run_all.py verify

# 3. Run all 88 unit, parity, library-API, and independent-oracle tests
python experiment/run_all.py test

# 4. Regenerate all 7 manuscript supplementary PDF figures (`figures/supp_*.pdf`)
python experiment/run_all.py figures
```

### Running Individual Domains or Suites

```bash
# List all 41 suites grouped by domain
python experiment/run_all.py list

# Fast non-destructive smoke tests (writes only to OS tempdir, never modifies results/)
python experiment/run_all.py benchmark --only v12 --smoke
python experiment/run_all.py benchmark --only v14 --smoke
python experiment/run_all.py benchmark --only e4  --smoke

# Re-run a full suite (or regenerate its CSV summaries from archived JSONL logs)
python experiment/run_all.py summaries --only v14
python experiment/run_all.py benchmark --domain protein_engineering --only v14
```

### Paper Section to Suite Key Map

See [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md) for the complete table-by-table mapping across Tables 1–69 and Figures 1–15.

| Paper Section | Tables / Figures | Domain | Suite Keys |
|---|---|---|---|
| §2.3, App. L.1 (conic update scaling & break-even) | Tables 1, 57, 58 | `simulated` | `e6`, `v8_4` |
| §3.1, App. G.1, App. L.1 (matched BED vs. KG/VOI/BO & $d=8$ anytime) | Table 3, Tables 7–9, 14, 59; Fig. 4 | `simulated` | `v12` |
| §3.1, App. G.2–G.3 (structural overlap & correlated proxy mechanisms) | Fig. 2, Tables 10–13, 15; Figs. 5–6 | `simulated` | `exp1`, `e0`, `e1`, `e2`, `v8_3` |
| App. G.4–G.5 (DF baselines, witness ablations, SameGame & routing) | Tables 16–23; Figs. 7–8 | `simulated` | `exp5`, `exp6`, `exp8`–`exp11`, `v8_6` |
| §3.2, App. H.1–H.4 (matched GB1 & TmTrpB BED vs. KG & $\chi^2_{r,.95}$ audit) | Fig. 3, Table 4, Tables 24–26; Fig. 9 | `protein_engineering` | `v14`, `v13` |
| §3.2, App. H.5–H.6 (calibration, validity ablation, extended GB1/TmTrpB) | Tables 27–34; Fig. 12 | `protein_engineering` | `v11_1`, `v8_1`, `exp12`–`exp14`, `e3` |
| §3.3, App. I (WorFBench offline & live uncached Qwen3-0.6B workflows) | Table 5, Tables 35–39; Figs. 10, 15c | `agentic_workflows` | `exp12`, `exp13`, `v11_2`, `v10_3`, `v8_5` |
| App. J.1–J.4 (info tracking, unknown variance V34, heteroscedastic bridge) | Tables 40–50; Figs. 11–14, 15b | `simulated` / `protein_engineering` | `v8_2`, `e5`, `v8_1`, `v9_1`–`v9_4`, `v10_2`, `v11_1` |
| App. J.5, L.2–L.4 (passive UCT/PUCT, C++ maintenance kernels, memory) | Tables 51–56, 60–67 | `simulated` | `passive_uct/`, `exp2`–`exp4`, `exp7` |
| App. L.5–L.6 (native C++17 B&B scaling, independent oracle audit) | Tables 68–69; Fig. 15a | `simulated` | `v10_1`, `v11_3` |

---

## External Data & Models (`scripts/fetch_data.py`)

Four compact preprocessed `.npz` archives (`dagcert/benchmarks/data/`, 1.7 MB) and the 20-board SameGame set are bundled in Git so installation, verification, unit tests, and all CPU experiments run offline. Every upstream source can also be downloaded and rebuilt from scratch:

| Dataset / Asset | Upstream Source | Bundled File | Rebuild Command |
|---|---|---|---|
| GB1 (149,361 four-site variants; Wu et al. 2016) | [FLIP](https://github.com/J-SNACKKB/FLIP) | `dagcert/benchmarks/data/gb1_wu2016_measured.npz` | `python scripts/fetch_data.py --proteins` |
| TmTrpB (159,129 four-site variants; Johnston et al. 2024) | [Zenodo 15203754](https://zenodo.org/records/15203754) | `dagcert/benchmarks/data/trpb_johnston2024_measured.npz` | `python scripts/fetch_data.py --proteins` |
| WorFBench raw trajectories (4 domains) | [zjunlp/WorfBench](https://github.com/zjunlp/WorfBench) | cached in `dagcert/benchmarks/data/worfbench_raw/` | `python scripts/fetch_data.py --worfbench-tasks` |
| `Qwen/Qwen3-0.6B` & `Qwen/Qwen3-Embedding-0.6B` | Hugging Face Hub | local Hugging Face cache | `python scripts/fetch_data.py --models` |
| WorFBench $81\times 64$ & $81\times 32$ score matrices | generated from above | `dagcert/benchmarks/data/worfbench_qwen3_*.npz` | `python scripts/fetch_data.py --rebuild-worfbench` |

Pass `--out-dir build/rebuilt_data` to rebuild alongside the bundled files for comparison, or `--all` to fetch everything. After caching models and trajectories, set `HF_HUB_OFFLINE=1` to run live LLM suites offline.

---

## Lean 4 Formalizations (`lean/`)

The [`lean/`](lean/) directory holds Lean 4 + Mathlib proofs of 10 of the paper's 62 numbered results, with no `sorry` and no added axioms: both main-text theorems, the exact regret geometry of Appendix A, and Appendix B except the restart bound. [`lean/README.md`](lean/README.md) gives the status of every result and states what each formal statement assumes.

- [`Basic.lean`](lean/JointRootCert/Basic.lean), [`JointSet.lean`](lean/JointRootCert/JointSet.lean) — decision model and joint-set reduction (§2.1, Lemma `lem:bay-reduction`).
- [`Rectangular.lean`](lean/JointRootCert/Rectangular.lean) — exact rectangular shared-support certificate and anytime-valid commitment (Theorem `thm:shared-regret`, Corollary `cor:shared-regret-pac`).
- [`Minimax.lean`](lean/JointRootCert/Minimax.lean), [`Ellipsoid.lean`](lean/JointRootCert/Ellipsoid.lean), [`Sparse.lean`](lean/JointRootCert/Sparse.lean) — exact joint ellipsoidal certificate with rank(L)+1 sparse witnesses, via Hahn–Banach separation and Carathéodory (Theorem `thm:bay-main-dual`).
- [`FeatureHull.lean`](lean/JointRootCert/FeatureHull.lean) — feature-hull dominance (Theorem `thm:t2-hull`).
- [`Acquisition.lean`](lean/JointRootCert/Acquisition.lean) — contrast variance-reduction score (`eq:main-contrast-acquisition`).
- [`ActiveWidth.lean`](lean/JointRootCert/ActiveWidth.lean) — width lemmas for exact-regret and optimistic-separation sampling (Lemmas `lem:active-width`, `lem:active-os-width`).
- [`ActiveBounds.lean`](lean/JointRootCert/ActiveBounds.lean) — confidence-width inversion, Safeguarded-LCB width and the counting argument behind the active sample bounds (Lemma `lem:active-inversion`, Theorem `thm:active-er`).
- [`Potential.lean`](lean/JointRootCert/Potential.lean), [`CDJoint.lean`](lean/JointRootCert/CDJoint.lean) — finite-sample cost of safeguarded CD-Joint (Theorem `thm:t4-finite-sample`), proved as a width lemma, a one-step bound and the cumulative cost bound.

Build with `cd lean && lake exe cache get && lake build` (Lean toolchain pinned in [`lean/lean-toolchain`](lean/lean-toolchain)).

---

## Repository Structure

```text
dagcert/
├── dagcert/                         # Installable Python library (`pip install dagcert` / `-e .`)
│   ├── graph.py                     # SearchDAG, SupportStructure, regret & overlap utilities
│   ├── certificates.py              # Rectangular, conic ellipsoidal, witness-cover & DF bounds
│   ├── posteriors.py                # SharedGaussianPosterior, contrast rank, chi2 beta, post.-risk MC
│   ├── acquisition.py               # certify_root_action, CD-Joint, Correlated KG, GP-OS, VOI, BO
│   ├── tracking.py                  # Info-tracking (T_*^eps) & V34 unknown-variance sparse tracker
│   ├── search.py                    # Trajectory-coupled passive UCT & PUCT certification
│   ├── benchmarks/                  # Synthetic, GB1/TmTrpB, WorFBench & SameGame loaders + data/
│   ├── _native/                     # Optional auto-compiled -O3 C++17 accelerators
│   └── _core/                       # Verified low-level numerical engines
├── experiment/                      # Complete paper experiments organized by domain
│   ├── run_all.py                   # Unified CLI: list, verify, test, summaries, figures, benchmark
│   ├── simulated/                   # §3.1 + App. G, J, L (27 suites + passive_uct/ v1 archive)
│   ├── protein_engineering/         # §3.2 + App. H (10 GB1 & TmTrpB suites)
│   ├── agentic_workflows/           # §3.3 + App. I (WorFBench offline & live Qwen3-0.6B suites)
│   └── plots/                       # Generates all 7 `figures/supp_*.pdf` + detailed suite plots
├── examples/                        # Standalone library quickstart & domain demos
├── tests/                           # 88 unit, parity, library-API & oracle tests (v1--v14)
├── results/                         # SHA-256-verified run archives, CSV summaries & manifests
├── figures/                         # README overview PNG + all 7 `supp_*.pdf` manuscript figures
├── scripts/fetch_data.py            # Offline verifier & upstream data/model rebuild utility
├── lean/                            # Lean 4 + Mathlib formal proofs (status in lean/README.md)
├── manuscript/                      # Paper PDF & LaTeX source
├── reference/tables/                # Reference LaTeX tables for passive UCT archive
├── pyproject.toml                   # Package metadata and optional extras
├── CITATION.cff                     # Machine-readable citation metadata
└── REPRODUCIBILITY.md               # Complete Table 1--69 & Figure 1--15 artifact map
```

---

## Statistical Scope & Notes

- **Validity depends on the stopping model.** Bounded-observation Hoeffding and Empirical Bernstein boxes are distribution-free; fixed-feature ellipsoids and unknown-variance nuisance-KL e-processes provide anytime frequentist coverage under their respective parametric assumptions; bounded-residual ellipsoids require a misspecification bound $|b|\le\xi$; Bayesian credible ellipsoids, direct posterior risk, and EB+LOO stopping are model-based and do not inherit distribution-free validity (Table 2 and Appendix C).
- **Protein & live-LLM experiments.** Protein benchmarks simulate noisy assays against published measured GB1 and TmTrpB landscapes (no new wet-lab experiments). Live workflow suites execute fresh, uncached `Qwen3-0.6B` inference on task pools strictly disjoint from calibration.
- **Determinism vs. timing.** Statistical trajectories, operation counts, and SHA-256 manifests are deterministic; wall-clock times and wall-capped rates depend on host hardware.

---

## Citation

If you use `dagcert` or this codebase in your research, please cite the accompanying manuscript (see also [`CITATION.cff`](CITATION.cff)):

```bibtex
@misc{pelissier2026dagcert,
  title  = {Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs},
  author = {P{\'e}lissier, Aur{\'e}lien},
  year   = {2026},
  url    = {https://github.com/AI-MathPhys/dagcert}
}
```
