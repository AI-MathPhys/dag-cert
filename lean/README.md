# Lean 4 formalization

Machine-checked proofs, against [Mathlib](https://github.com/leanprover-community/mathlib4), of results from **Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs** ([manuscript](../manuscript/Joint_cert_manuscript.pdf)).

**Status: 10 of the 62 numbered results are proved and 52 are open.** The goal is all 62. Everything in this directory compiles with no `sorry` and no added axioms (the proved theorems depend only on `propext`, `Classical.choice` and `Quot.sound`). The proved part is both main-text theorems, all of Appendix A, and Appendix B except the restart bound. Two theorems (CD-Joint cost, active sample bounds) are proved as separate lemmas rather than as one statement about a formal model of the algorithm; their rows in the table say exactly what is assumed.

## Build

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib (once)
lake build
```

Toolchain `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0` (pinned in `lake-manifest.json`).

## Files

| File | Content |
|---|---|
| `JointRootCert/Basic.lean` | Decision model: global optimum, root value, regret, challenger advantage; outside-inside reduction for one environment |
| `JointRootCert/JointSet.lean` | Joint-set reduction for an arbitrary set of environments |
| `JointRootCert/Rectangular.lean` | Exact rectangular certificate, comparison with marginal bounds, anytime-valid commitment |
| `JointRootCert/Minimax.lean` | Minimax identity over a Euclidean ball and the simplex, with weak and strong duality |
| `JointRootCert/Ellipsoid.lean` | Exact joint ellipsoidal certificate; feasible mixtures as upper bounds |
| `JointRootCert/Sparse.lean` | Optimal inside mixtures with at most rank(L)+1 nonzero entries |
| `JointRootCert/FeatureHull.lean` | Feature-hull dominance, exact and approximate |
| `JointRootCert/Acquisition.lean` | Variance reduction of a fixed contrast; the rank-one downdate is Gaussian conditioning |
| `JointRootCert/ActiveWidth.lean` | Width charged to the selected terminal for exact-regret and optimistic-separation sampling |
| `JointRootCert/Potential.lean` | Coercive design matrices: the V⁻¹ quadratic form, Cauchy-Schwarz and triangle inequalities, matrix determinant lemma for a rank-one update |
| `JointRootCert/CDJoint.lean` | Finite-sample cost of safeguarded CD-Joint: width of the safeguarded contrast, one-step bound, cumulative cost bound |
| `JointRootCert/ActiveBounds.lean` | Confidence-width inversion, Safeguarded-LCB width, counting argument and explicit sample bound for active sampling |

## How statements are modelled

- A root action is its support `S : Finset Z`, nonempty, over a finite nonempty terminal type `Z`. An environment is a function `f : Z → ℝ`.
- Worst-case regret over a set `C` of environments is stated two ways: as a certificate (`∀ f ∈ C, regret S f ≤ ε ↔ …`) and as a value (`sSup`), the latter where the supremum exists.
- The ellipsoid is `m + L(B₂(β))` for a linear map `L` between finite-dimensional real inner product spaces; `Lᵀ` is `LinearMap.adjoint L`. No rank condition is assumed.
- The manuscript proves the minimax identity by Sion's theorem. Here it is proved from the Hahn-Banach separation theorem in Mathlib, so no minimax theorem is assumed.
- Feature-hull dominance takes features in a real normed space and parameters in its continuous dual, which gives the dual-norm statement directly.
- The anytime-valid corollary takes simultaneous coverage as a hypothesis (`P {ω | ∃ t, μ ∉ C t ω} ≤ δ`) and allows an arbitrary path-dependent stopping time and recommendation. The coverage statements themselves (Appendix C) are open.
- Two unnumbered displays are also proved: the first equality of `eq:robust-definition` (`robustRegret_eq`) and the contrast score `eq:main-contrast-acquisition` (`contrast_variance_reduction`, `condCov_precision`).

## Result-by-result status

Rows follow the order of the LaTeX source. "open" means not yet formalized.

| # | Where | Result | Label | Status | Lean |
|---|---|---|---|---|---|
| 1 | Main text | Theorem: Exact joint ellipsoidal certificate and sparse witnesses | `thm:bay-main-dual` | proved | `Ellipsoid.lean`: `ellipsoid_certificate_iff`, `robustRegret_ellipsoid`, `adv_le_ellObj`; `Sparse.lean`: `ellipsoid_sparse_witness`; minimax identity in `Minimax.lean`. The sharpness example for rank+1 is not formalized. |
| 2 | Main text | Theorem: Finite-sample cost of safeguarded CD-Joint | `thm:t4-finite-sample` | proved | `CDJoint.lean`: `cd_joint_cost` (the cost bound `eq:t4-bound`), `cd_step`, `cd_width` (`eq:cd-width-lemma`), `contrast_l1`; linear algebra in `Potential.lean`. Proved as separate lemmas whose hypotheses are the conditions Algorithm 1 guarantees at each uncertified step; they are not assembled into one statement about a formal model of the algorithm, the two presentations of the contrast norm (`‖Lᵀg‖` and `√(gᵀV⁻¹g)`) are not identified, and coverage of the self-normalized radius is assumed (Appendix C). |
| 3 | App. A | Lemma: Joint-set reduction | `lem:bay-reduction` | proved | `JointSet.lean`: `robust_regret_le_iff`, `robustRegret_eq` |
| 4 | App. A | Theorem: Exact rectangular shared-support certificate | `thm:shared-regret` | proved | `Rectangular.lean`: `rect_isGreatest`, `robustRegret_box`, `robustRegret_box_full`, `rectCert_le_iff`, `rectCert_le_marginal` |
| 5 | App. A | Corollary: Anytime-valid root commitment | `cor:shared-regret-pac` | proved | `Rectangular.lean`: `anytime_valid_commitment`, `anytime_valid_commitment_box` |
| 6 | App. A | Theorem: Feature-hull dominance | `thm:t2-hull` | proved | `FeatureHull.lean`: `feature_hull_dominance`, `regret_le_of_hull_dist` |
| 7 | App. B | Theorem: Finite-sample support-sensitive acquisition | `thm:active-er` | proved | `ActiveBounds.lean`: `stopping_time_le_sum_budget` (counting argument), `active_sample_bound` (explicit bound), `active_sg_width` (Safeguarded-LCB); `ActiveWidth.lean`: `active_width`, `active_os_width`. Proved as separate lemmas: the three bounds are the instances of `active_sample_bound` with the thresholds supplied by the three width lemmas, not three statements about a formal model of Algorithm 2. Assumed: the nested interval after `n` observations has width at most `2β(n)`, and simultaneous coverage (both Appendix C). |
| 8 | App. B | Lemma: Width charged to each selected terminal | `lem:active-width` | proved | `ActiveWidth.lean`: `active_width` |
| 9 | App. B | Lemma: Explicit confidence-width inversion | `lem:active-inversion` | proved | `ActiveBounds.lean`: `width_inversion`, `width_inversion_nat`. Proved without the monotonicity-by-derivative step: the width is shown to be below `r` at every count above the threshold. |
| 10 | App. B | Lemma: Width charged by optimistic-separation sampling | `lem:active-os-width` | proved | `ActiveWidth.lean`: `active_os_width` |
| 11 | App. B | Theorem: Certified restart bound | `thm:active-restart` | open |  |
| 12 | App. C | Lemma: Full-domain confidence sequence | `lem:bay-cs` | open |  |
| 13 | App. C | Lemma: Anytime validity and nesting of terminal boxes | `lem:nested-interval-valid` | open |  |
| 14 | App. C | Proposition: Valid misspecification-aware ellipsoid and safe intersection | `thm:t3-misspec` | open |  |
| 15 | App. D | Theorem: One inside witness and Bernoulli information limit | `thm:ast-main` | open |  |
| 16 | App. D | Theorem: Correlated Gaussian information limit | `thm:bay-main-optimal` | open |  |
| 17 | App. D | Lemma: Stopped Bernoulli change of measure | `lem:active-com` | open |  |
| 18 | App. D | Theorem: Scalar information projection for a fixed root answer | `thm:active-kl-projection` | open |  |
| 19 | App. D | Theorem: Non-containment tied-star lower bound | `thm:active-star-lb` | open |  |
| 20 | App. D | Proposition: A support-margin versus information tradeoff | `prop:ast-gap-tradeoff` | open |  |
| 21 | App. D | Proposition: A discovery cost absent from the characteristic time | `prop:ast-discovery` | open |  |
| 22 | App. D | Lemma: Screened projection | `lem:bay-projection` | open |  |
| 23 | App. D | Lemma: Distance and certification | `lem:bay-distance-certificate` | open |  |
| 24 | App. D | Proposition: Finite-confidence discovery, frozen confirmation, and safeguard | `prop:bay-finite` | open |  |
| 25 | App. D | Lemma: Elementary logarithmic budget inversion | `lem:bay-fc-inversion` | open |  |
| 26 | App. D | Theorem: Explicit discovery and a frozen near-optimal plan | `thm:v10g-discovery` | open |  |
| 27 | App. D | Proposition: Conditional safety and a finite-mean reference design | `prop:v10g-safety-fallback` | open |  |
| 28 | App. D | Theorem: Correlated finite-confidence discovery and confirmation | `thm:v10g-expectation` | open |  |
| 29 | App. D | Corollary: Finite-confidence correlated confirmation bound | `cor:v10g-target` | open |  |
| 30 | App. D | Theorem: Action-local optional evaluation and intersection-union root coverage | `thm:v34-action-local` | open |  |
| 31 | App. D | Theorem: Sparse four-power nuisance-KL tracking with unknown variances | `thm:v34-adaptive` | open |  |
| 32 | App. D | Theorem: Matching unknown-variance converse with a unique correct action | `thm:v34-converse-main` | open |  |
| 33 | App. D | Proposition: Global solver-call reduction under sparse refreshes and action-local evidence | `prop:v34-work` | open |  |
| 34 | App. D | Lemma: Uniform stability of the nuisance-KL information game | `lem:v34-transport` | open |  |
| 35 | App. D | Lemma: A uniform batch log-likelihood comparison | `lem:v34-batch-comparison` | open |  |
| 36 | App. D | Lemma: Explicit intrinsic-tape Gaussian concentration | `lem:v34-concentration` | open |  |
| 37 | App. D | Theorem: Unknown-variance nuisance-KL lower bound for one correct answer | `thm:v34-converse` | open |  |
| 38 | App. E | Proposition: Safe permanent retirement | `prop:uct-coupling` | open |  |
| 39 | App. E | Theorem: Selective vs. eager maintenance separations on UCT and Root-PUCT funnels | `thm:onpolicy-uct` | open |  |
| 40 | App. E | Theorem: Wide Common-Core Support Compilation Cost | `thm:ta-core` | open |  |
| 41 | App. E | Lemma: Uniform finite-horizon count bounds | `lem:v2counts` | open |  |
| 42 | App. E | Corollary: Fixed gaps versus a shrinking gap | `cor:v2countscales` | open |  |
| 43 | App. E | Lemma: Nesting and actual endpoint changes | `lem:v2strict` | open |  |
| 44 | App. E | Theorem: A sharp certification-horizon scale | `thm:v2horizon` | open |  |
| 45 | App. E | Proposition: Uniformly early retirement and changing revisits | `prop:v2postcut` | open |  |
| 46 | App. E | Theorem: Root-PUCT work separation from uninformative initialization | `thm:v2separation` | open |  |
| 47 | App. E | Corollary: One explicit polynomial instance | `cor:v2quarter` | open |  |
| 48 | App. E | Proposition: The family does not lower-bound all numerical oracles | `prop:v2escape` | open |  |
| 49 | App. E | Theorem: Support-sensitive certification under recursive PUCT | `thm:puct-noisy-main` | open |  |
| 50 | App. E | Theorem: Uniform local PUCT revisit bound under changing values | `thm:v35local` | open |  |
| 51 | App. E | Theorem: Pathwise terminal coverage under recursive local PUCT | `thm:v35dag` | open |  |
| 52 | App. E | Lemma: Anytime coverage and a usable width bound | `lem:v35width` | open |  |
| 53 | App. E | Theorem: High-probability on-policy PUCT certification horizon | `thm:v35horizon` | open |  |
| 54 | App. E | Corollary: Polynomial accuracy dependence at fixed depth | `cor:v35poly` | open |  |
| 55 | App. E | Proposition: Positive-variance root PUCT: almost-sure square-root counts | `prop:v35rootrates` | open |  |
| 56 | App. E | Counterexample: Zero prior at one internal edge prevents terminal coverage | `ce:v35prior` | open |  |
| 57 | App. K | Theorem: Exact coupling and charged maintenance | `thm:adaptive-oracle-coupling` | open |  |
| 58 | App. K | Proposition: Trajectory Coupling Across Circuit Representations | `prop:representation-coupling` | open |  |
| 59 | App. K | Proposition: Unified Full-Cost Representation Comparison | `prop:representation-cost` | open |  |
| 60 | App. K | Theorem: Every-layout limit of flat dyadic compilation | `thm:coded-main` | open |  |
| 61 | App. K | Theorem: Every-Layout Dyadic Cover Lower Bound | `thm:coded-covers` | open |  |
| 62 | App. K | Proposition: Equivalence Under Unrestricted Circuit Retention | `prop:unrestricted-compiler` | open |  |

## What the open results need

- **Assembling the CD-Joint theorem:** a formal model of Algorithm 1 that discharges the per-step hypotheses of `cd_joint_cost` from `cd_width` and `contrast_l1`, and identifies `‖Lᵀg‖` with `√(gᵀV⁻¹g)` for `L Lᵀ = V⁻¹`.
- **Appendix B, remaining:** the certified restart bound (`thm:active-restart`), which needs a probability model of independent episodes and a geometric-series bound on the expected stopping time; and formal models of Algorithms 1 and 2 to assemble the two modular theorems.
- **Appendix C (confidence sequences):** time-uniform Hoeffding, empirical-Bernstein and self-normalized bounds. Mathlib has sub-Gaussian and martingale foundations but not these sequences, so they must be built.
- **Appendix D (information limits):** change of measure for stopped processes, KL projections, tracking arguments, and the unknown-variance theory. This is the largest block (23 results) and the furthest from existing Mathlib.
- **Appendix E (UCT / PUCT trajectories):** 19 results on deterministic and noisy search dynamics; needs a formal model of the search procedures.
- **Appendix K (representation costs):** 6 combinatorial statements about circuits and dyadic covers.
