# Lean 4 formalization

Machine-checked proofs, against [Mathlib](https://github.com/leanprover-community/mathlib4), of results from **Certify the Decision, Not the Outcome: Bayesian Experimental Design on Search Graphs** ([manuscript](../manuscript/Joint_cert_manuscript.pdf)).

**Status: of the 62 numbered results, 32 are proved, 30 are partly proved, and 0 are open.** The goal is all 62. Everything in this directory compiles with no `sorry` and no added axioms (the theorems depend only on `propext`, `Classical.choice` and `Quot.sound`).

How to read the status column:

- **proved**: the result is proved as stated, or in modular form where the only hypotheses are other numbered results of the paper, the definition of the procedure being analysed, or conditions the manuscript leaves implicit. The row says which.
- **partial**: named parts are proved and the row lists what is assumed or still open. The recurring gaps are a small set of probabilistic facts that Mathlib does not have (the change of measure for a stopped adaptive process, the self-normalized martingale bound, chi-square tails, exponential supermartingales for bounded differences) and running-time claims that need a formal cost model.
- **open**: not yet formalized.

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
| `Basic.lean` | Decision model: global optimum, root value, regret, challenger advantage; outside-inside reduction for one environment |
| `JointSet.lean` | Joint-set reduction for an arbitrary set of environments |
| `Rectangular.lean` | Exact rectangular certificate, comparison with marginal bounds, anytime-valid commitment |
| `Minimax.lean` | Minimax identity over a Euclidean ball and the simplex, with weak and strong duality |
| `Ellipsoid.lean` | Exact joint ellipsoidal certificate; feasible mixtures as upper bounds |
| `Sparse.lean` | Optimal inside mixtures with at most rank(L)+1 nonzero entries |
| `FeatureHull.lean` | Feature-hull dominance, exact and approximate |
| `Acquisition.lean` | Variance reduction of a fixed contrast; the rank-one downdate is Gaussian conditioning |
| `ActiveWidth.lean` | Width charged to the selected terminal for exact-regret and optimistic-separation sampling |
| `Potential.lean` | Coercive design matrices: the V⁻¹ quadratic form, Cauchy-Schwarz and triangle inequalities, matrix determinant lemma |
| `CDJoint.lean` | Finite-sample cost of safeguarded CD-Joint |
| `ActiveBounds.lean` | Confidence-width inversion, Safeguarded-LCB width, counting argument and explicit sample bound |
| `Restart.lean` | Certified restart bound: confidence schedule, episode budgets, numeric constants, expected stopping time |
| `Coverage.lean` | Ville's inequality; Hoeffding coverage and nesting of terminal boxes; empirical-Bernstein and Gaussian mixture confidence sequences; misspecification-aware radius; posterior-risk bound |
| `BernoulliInfo.lean` | Bernoulli KL facts, scalar information projection, one-witness reduction, tied-star lower bound, gap and discovery propositions |
| `StoppedProcess.lean` | Adaptive Bernoulli sampler with a stopping rule: law of the stopped history, Wald identity, change of measure, sampler forms of the lower bounds |
| `Assembly.lean` | End-to-end statements that discharge hypotheses with facts proved elsewhere: exact-regret sampling, recursive-PUCT certification, action-local coverage, restart bound, ellipsoid/`V⁻¹` identification |
| `GaussianInfo.lean` | Known-variance Gaussian information: screened projection and its dual, distance certificate, budget inversion, tracking and finite-confidence discovery/confirmation cores |
| `UnknownVariance.lean` | Nuisance-profiled KL game: stability, batch comparison, action-local wealth, intersection-union coverage, solver-call counts, converse reduction |
| `PassiveRetirement.lean` | Safe permanent retirement, trajectory coupling, UCT count bound, common-core instance |
| `RootPUCT.lean` | Fixed-prior root-PUCT: count bounds, nested radii, certification-horizon scale, post-cut revisits |
| `RecursivePUCT.lean` | Recursive local PUCT: revisit bound, terminal coverage through a DAG, certification horizon, almost-sure root rates, zero-prior counterexample |
| `Representation.lean` | Max-circuits and dyadic covers: coupling across representations, incidence bound, every-layout parity-grid lower bound, cost accounting |

## How statements are modelled

- A root action is its support `S : Finset Z`, nonempty, over a finite nonempty terminal type `Z`. An environment is a function `f : Z → ℝ`.
- Worst-case regret over a set `C` of environments is stated two ways: as a certificate (`∀ f ∈ C, regret S f ≤ ε ↔ …`) and as a value (`sSup`), the latter where the supremum exists.
- The ellipsoid is `m + L(B₂(β))` for a linear map `L` between finite-dimensional real inner product spaces; `Lᵀ` is `LinearMap.adjoint L`. No rank condition is assumed.
- The manuscript proves the minimax identity by Sion's theorem. Here it is proved from the Hahn-Banach separation theorem in Mathlib.
- Algorithms are not modelled as programs. A run is a sequence of selections satisfying the rule the paper states (for example "the selected index maximises the PUCT score"), so the theorems hold for every tie-breaking rule. Stopping monitors enter through their specification.
- Probabilistic statements are over an arbitrary probability space carrying the reward tapes, and are stated as bounds on the failure probability.
- Asymptotic statements (`Θ`, `O`, `Õ`) are proved as explicit two-sided inequalities with named constants.

## Hypotheses the manuscript leaves implicit

Found while formalizing; none makes a stated result false.

- `thm:active-restart` uses `ρ_z ≤ 1` and `M ≥ |Z|`.
- `cor:v2countscales`: the shrinking-gap lower bound is derived from a count bound that needs `t ≥ 2K`.
- Safe permanent retirement preserves the stopping bit only for `ε ≥ 0`.
- `thm:active-star-lb` needs the return probability to be positive under interior alternatives.
- `prop:ast-gap-tradeoff` needs `N ≥ 1`.
- The Safeguarded-LCB width argument needs the lower-confidence candidate to maximise the lower endpoint over the support.
- The UCT index is written with `log N_t(v)` in its definition but used with `log(1+t)` (and coefficient 2 in one place) in the proofs of the funnel and common-core theorems.

## Result-by-result status

Rows follow the order of the LaTeX source.

| # | Where | Result | Label | Status | Lean |
|---|---|---|---|---|---|
| 1 | Main text | Theorem: Exact joint ellipsoidal certificate and sparse witnesses | `thm:bay-main-dual` | proved | `Ellipsoid.lean`: `ellipsoid_certificate_iff`, `robustRegret_ellipsoid`, `adv_le_ellObj`; `Sparse.lean`: `ellipsoid_sparse_witness`; minimax identity in `Minimax.lean`. The sharpness example for rank+1 is not formalized. |
| 2 | Main text | Theorem: Finite-sample cost of safeguarded CD-Joint | `thm:t4-finite-sample` | proved | `CDJoint.lean`: `cd_joint_cost` (the cost bound `eq:t4-bound`), `cd_step`, `cd_width` (`eq:cd-width-lemma`), `contrast_l1`; linear algebra in `Potential.lean`. `Assembly.lean`: `exists_ellipsoid_map` identifies `‖Lᵀg‖` with `√(gᵀV⁻¹g)` and the ellipsoid with `{θ : (θ-m)ᵀV(θ-m) ≤ β²}`; `confidence_ellipsoid_certificate_iff` and `cd_width_of_uncertified` connect the exact certificate to the width lemma. Proved as separate lemmas whose hypotheses are the conditions Algorithm 1 guarantees at each uncertified step; not assembled into one statement about a formal model of the algorithm. Assumed: coverage of the self-normalized radius (`thm:t3-misspec`). |
| 3 | App. A | Lemma: Joint-set reduction | `lem:bay-reduction` | proved | `JointSet.lean`: `robust_regret_le_iff`, `robustRegret_eq` |
| 4 | App. A | Theorem: Exact rectangular shared-support certificate | `thm:shared-regret` | proved | `Rectangular.lean`: `rect_isGreatest`, `robustRegret_box`, `robustRegret_box_full`, `rectCert_le_iff`, `rectCert_le_marginal` |
| 5 | App. A | Corollary: Anytime-valid root commitment | `cor:shared-regret-pac` | proved | `Rectangular.lean`: `anytime_valid_commitment`, `anytime_valid_commitment_box` |
| 6 | App. A | Theorem: Feature-hull dominance | `thm:t2-hull` | proved | `FeatureHull.lean`: `feature_hull_dominance`, `regret_le_of_hull_dist` |
| 7 | App. B | Theorem: Finite-sample support-sensitive acquisition | `thm:active-er` | proved | `Assembly.lean`: `active_er_end_to_end` (exact-regret sampling, end to end: outside an event of probability at most `δ` the returned action is `ε`-optimal and the number of queries is at most the explicit sum; the only probabilistic input is the reward-tape model), `active_sample_bound_tape`, `active_tape_end_to_end` (same for an arbitrary threshold), `run_width_le`, `tape_coverage`, `erStep_width`. `ActiveBounds.lean`: `stopping_time_le_sum_budget`, `active_sg_width`; `ActiveWidth.lean`: `active_width`, `active_os_width`. The Safeguarded-LCB and optimistic-separation bounds are the instances of `active_tape_end_to_end` with the thresholds of `active_sg_width` and `active_os_width`; they are not written out as separate end-to-end statements. |
| 8 | App. B | Lemma: Width charged to each selected terminal | `lem:active-width` | proved | `ActiveWidth.lean`: `active_width` |
| 9 | App. B | Lemma: Explicit confidence-width inversion | `lem:active-inversion` | proved | `ActiveBounds.lean`: `width_inversion`, `width_inversion_nat`. Proved without the monotonicity-by-derivative step: the width is shown to be below `r` at every count above the threshold. |
| 10 | App. B | Lemma: Width charged by optimistic-separation sampling | `lem:active-os-width` | proved | `ActiveWidth.lean`: `active_os_width` |
| 11 | App. B | Theorem: Certified restart bound | `thm:active-restart` | partial | `Assembly.lean`: `certified_restart_end_to_end` (expected queries below `1600 H L`, almost-sure termination, error probability at most `δ`), `restart_reach_step`, `restart_covered_episode_within_cap`. `Restart.lean`: `certified_restart_bound`, `restart_numeric`, `restart_constants`, `restart_tail`, `restart_lintegral_le`. Assumed: independence of the episodes, as independent σ-algebras carrying each episode's failure event, and that queried widths meet the optimistic-separation threshold on coverage. Open: an explicit product measure realising the independence. Uses `ρ_z ≤ 1` and `|Z| ≤ M`, implicit in the manuscript. |
| 12 | App. C | Lemma: Full-domain confidence sequence | `lem:bay-cs` | partial | `Coverage.lean`: `mixGap_bounds` (`0 ≤ A_t ≤ (γ/2)‖θ̂‖²`), `det_le_trace_div_pow` (AM-GM), `mixThreshold_le` (bound on `H_t`), `mixture_exponent_identity`, `bay_cs_coverage` via `ville_ineq` (Ville's inequality, proved here). Assumed: the Gaussian mixture of likelihood ratios is a nonnegative supermartingale with the stated closed form. Open: the adaptive Gaussian model and the Gaussian integration that give it. |
| 13 | App. C | Lemma: Anytime validity and nesting of terminal boxes | `lem:nested-interval-valid` | partial | `Coverage.lean`: Hoeffding schedule fully proved from Mathlib's Hoeffding inequality (`hoeffding_count_failure`, `hoeffding_schedule_failure`, `hoeffding_box_coverage`), nesting fully proved (`box_nested`, `runLo_mono`, `runHi_anti`). Empirical-Bernstein variant: `eb_coverage`, `eb_interval_of_lt`, assuming the two test processes are supermartingales. Open: the exponential inequality for bounded martingale differences that makes them so. |
| 14 | App. C | Proposition: Valid misspecification-aware ellipsoid and safe intersection | `thm:t3-misspec` | partial | `Coverage.lean`: `misspec_radius`, `bias_qinv_le`, `ridge_error_decomp`, `bias_budget_cap`, `misspec_regret_isGreatest` and `misspec_certificate_isGreatest` (the `+2ξ` correction is exact), `safe_intersection`. Assumed: the time-uniform self-normalized bound on the noise term (Abbasi-Yadkori et al.), which is not in Mathlib. Also proved here: the unnumbered Bayesian guarantee `eq:bay-posterior-risk` (`posterior_risk_bound`). |
| 15 | App. D | Theorem: One inside witness and Bernoulli information limit | `thm:ast-main` | partial | `BernoulliInfo.lean`: `one_witness_reduction` (`eq:ast-star`, with suprema rather than attained maxima), `infoRate_concave`, `charRate_mem_Icc`, `charRate_pos_iff`, `pairF_le_of_alt`. `StoppedProcess.lean`: `transport_lower_bound_sampler` (fixed-answer lower bound `kl(1-δ, δ) ≤ E τ · C_a` for a sampler). Open: the asymptotic lower bound with several correct answers, the allocation oracle, the mixture-martingale certificate, and the tracking argument for the matching upper bound. |
| 16 | App. D | Theorem: Correlated Gaussian information limit | `thm:bay-main-optimal` | partial | `GaussianInfo.lean`: regularity of the information function (`rootInfo_lipschitz`, `rootInfo_design_lipschitz`, `info_concave_design`, `info_le_anchor`, `floor_rate_loss`), `tracking_discrepancy`, `upper_rate_of_bounds`, `change_of_measure_bound`, `lower_bound_event`, `lower_rate_of_bounds`, `certified_branch_safe`. Assumed: coverage of the confidence sequence (`lem:bay-cs`), the density identity on the stopped history, and the per-slack bounds. Open: a model of adaptive Gaussian experiments, joint continuity of the information, the oracle contract, concentration of the estimator, and the stopped likelihood-ratio identity. Not assembled into one statement. |
| 17 | App. D | Lemma: Stopped Bernoulli change of measure | `lem:active-com` | proved | `StoppedProcess.lean`: `wald_identity`, `stopped_transport_finite`, `stopped_transport`; binary data processing in `BernoulliInfo.lean` (`bkl_le_integral_llr`). The sampler is a deterministic function of the observed history; its law is built from Bernoulli likelihoods of stopped histories and shown equal to the law induced by a product reward table (`prob_eq_table`). Needs only finite expected stopping time under `μ`. Not modelled: internal randomization of the sampler; unbounded-horizon probabilities and expectations are defined as monotone limits over the horizon. |
| 18 | App. D | Theorem: Scalar information projection for a fixed root answer | `thm:active-kl-projection` | proved | `BernoulliInfo.lean`: `info_projection`, `scalarObj_convexOn`, `scalarObj_strictConvexOn`, `scalarObj_existsUnique_isMinOn`. For `0 ≤ ε < 1`, proper nonempty support and interior means. |
| 19 | App. D | Theorem: Non-containment tied-star lower bound | `thm:active-star-lb` | proved | `StoppedProcess.lean`: `tied_star_lower_bound_sampler`, whose only hypotheses on the algorithm are `(ε,δ)`-correctness at interior parameters and finite expected stopping time. `BernoulliInfo.lean`: `tied_star_lower_bound`, `star_bound_quadratic`, `star_first_term_smaller`. Deterministic samplers; finite expected stopping time only. |
| 20 | App. D | Proposition: A support-margin versus information tradeoff | `prop:ast-gap-tradeoff` | proved | `BernoulliInfo.lean`: `gap_tradeoff_structure`, `gap_tradeoff_A`, `gap_tradeoff_B`. Needs `N ≥ 1`, implicit in the manuscript. |
| 21 | App. D | Proposition: A discovery cost absent from the characteristic time | `prop:ast-discovery` | partial | `BernoulliInfo.lean`: `discovery_cost`, `discovery_pathwise`, `discovery_rate`, `discovery_instances`. Assumed: the coupled probability space of the null and alternative runs (first-request indices, agreement of answers before the first request, correctness of each run). Open: constructing that coupling from a sampler. |
| 22 | App. D | Lemma: Screened projection | `lem:bay-projection` | proved | `GaussianInfo.lean`: `strictComp_nonempty_iff`, `closure_strictComp`, `closure_strictAlt`, `screened_projection`, `exists_min_polyhedron`, `hullScreen_eq_empty_iff`, `screened_projection_dual` (strong duality by Hahn-Banach, no rank condition), `projection_ratio`. |
| 23 | App. D | Lemma: Distance and certification | `lem:bay-distance-certificate` | proved | `GaussianInfo.lean`: `distance_certificate`, `distance_certificate_ellipsoid`, `distance_certificate_rootInfo`, `certified_of_threshold`. |
| 24 | App. D | Proposition: Finite-confidence discovery, frozen confirmation, and safeguard | `prop:bay-finite` | partial | Summary of `thm:v10g-discovery`, `prop:v10g-safety-fallback`, `thm:v10g-expectation` and `cor:v10g-target`; see those rows. Safety is `certified_branch_safe` with `two_branch_safe`; the bound is `finite_confidence_expectation` with `target_bound`. |
| 25 | App. D | Lemma: Elementary logarithmic budget inversion | `lem:bay-fc-inversion` | proved | `GaussianInfo.lean`: `log_budget_inversion`. |
| 26 | App. D | Theorem: Explicit discovery and a frozen near-optimal plan | `thm:v10g-discovery` | partial | `GaussianInfo.lean`: `stage_union_bound`, `pilot_radius`, `pilot_gate_succeeds`, `pilot_budget_sufficient`, `exists_pilot_stage`, `frozen_plan_rate`. Assumed: the chi-square tail per stage, the oracle contract, and the root modulus of the optimal rate. Not assembled into one statement about the pilot loop. |
| 27 | App. D | Proposition: Conditional safety and a finite-mean reference design | `prop:v10g-safety-fallback` | partial | `GaussianInfo.lean`: `certified_branch_safe`, `frozen_recycle`, `safeguard_mean_bound`, `fallback_stops`, `chernoff_half`, `expected_count_le_of_exp_tail`. Assumed: simultaneous ellipsoid coverage and the exponential tail of the safeguard count. Open: the chi-square moment generating function and the conditioning on pilot histories. |
| 28 | App. D | Theorem: Correlated finite-confidence discovery and confirmation | `thm:v10g-expectation` | partial | `GaussianInfo.lean`: `finite_confidence_expectation` (from five hypotheses on the good event, safeguard domination and independence), `setLIntegral_of_indep`, `confirm_crossing`, `confirm_stops`, `calendar_main`, `two_branch_safe`. Open: assembling these for a formal model of the interleaved procedure. |
| 29 | App. D | Corollary: Finite-confidence correlated confirmation bound | `cor:v10g-target` | partial | `GaussianInfo.lean`: `discovery_budget_split`, `leading_multiplier_le`, `target_bound`. Assumed: the expectation bound of `thm:v10g-expectation`. Open: the order of the remainder term. |
| 30 | App. D | Theorem: Action-local optional evaluation and intersection-union root coverage | `thm:v34-action-local` | partial | `Assembly.lean`: `action_local_coverage` (intersection-union coverage with Ville's inequality proved, no union over components). `UnknownVariance.lean`: `halfCash_integral_le_one`, `localWealth_supermartingale`. Assumed: on the selection event the conditional expectation of the next e-factor is at most one. Open: deriving that from the concrete Gaussian batch density. |
| 31 | App. D | Theorem: Sparse four-power nuisance-KL tracking with unknown variances | `thm:v34-adaptive` | partial | `UnknownVariance.lean`: `actGame_domination`, `score_error_of_contract`, `retained_design_value`, `sticky_stabilization`, `log_factor_rate`, `wealth_rate`, `lintegral_stopping_le`, `overshoot_bound`, `limsup_coefficient`. Open: the tail bound `eq:v34-tail-stop`, its summability, the schedule asymptotics, and the assembly into the sharp rate. |
| 32 | App. D | Theorem: Matching unknown-variance converse with a unique correct action | `thm:v34-converse-main` | partial | Same statement as `thm:v34-converse`; see that row. |
| 33 | App. D | Proposition: Global solver-call reduction under sparse refreshes and action-local evidence | `prop:v34-work` | proved | `UnknownVariance.lean`: `designCalls_eq` (an equality), `card_fourPower_refreshes`, `nullSolves_le`, `expected_designCalls_le`, `expected_nullSolves_le`. The expectation bounds assume the expected-stopping bound supplied by `thm:v34-adaptive`. |
| 34 | App. D | Lemma: Uniform stability of the nuisance-KL information game | `lem:v34-transport` | proved | `UnknownVariance.lean`: `actGame_transport`, `actGameStar_transport`, `transport_nuisDist`. |
| 35 | App. D | Lemma: A uniform batch log-likelihood comparison | `lem:v34-batch-comparison` | partial | `UnknownVariance.lean`: `batch_comparison`, `profBracket_sub_le`, `profBracket_eq_loglik`, for the profiled statistic. Open: identifying that statistic with `R⁻¹ log(q(Y)/U(Y))` as one statement. |
| 36 | App. D | Lemma: Explicit intrinsic-tape Gaussian concentration | `lem:v34-concentration` | partial | `UnknownVariance.lean`: `chi2_threshold_upper`, `chi2_threshold_lower`, `concentration_fixed`, `concentration_prefix`. Assumed: the Gaussian mean tail and the two chi-square Chernoff tails. Open: those tails (Mathlib has no chi-square distribution) and summability. |
| 37 | App. D | Theorem: Unknown-variance nuisance-KL lower bound for one correct answer | `thm:v34-converse` | partial | `UnknownVariance.lean`: `converse_reduction`, `converse_reduction_star`, `gaussKL_isLeast`, `tendsto_klBin_div_log`, `liminf_coefficient`. Assumed: the transportation inequality (stopped change of measure plus data processing). Open: that inequality, and identifying the closed-form `gaussKL` with the KL divergence of Gaussian laws. |
| 38 | App. E | Proposition: Safe permanent retirement | `prop:uct-coupling` | partial | `PassiveRetirement.lean`: `protected_pruning`, `RetireRun.invariant`, `RetireRun.lowLeader_iff`, `RetireRun.stops_iff`, `coupled_trajectories`. Preservation of the stopping bit needs `ε ≥ 0`, implicit in the manuscript. Open: the work bounds `eq:ram-work-bounds` (no cost model). |
| 39 | App. E | Theorem: Selective vs. eager maintenance separations on UCT and Root-PUCT funnels | `thm:onpolicy-uct` | partial | `PassiveRetirement.lean`: `uct_count_le`, `funnel_check_forces_radius`. Open: the fairness step, the funnel and ladder graph families, and the `O(m)` versus `Ω(m log m)` work claims (need a recursive UCT model and a cost model). |
| 40 | App. E | Theorem: Wide Common-Core Support Compilation Cost | `thm:ta-core` | partial | `PassiveRetirement.lean`: `card_coreZ`, `core_flat_support_size`, `core_unique_eps_optimal`, `core_lose_count_le`. Open: the DAG itself, the stopping-time bound and the work bounds. |
| 41 | App. E | Lemma: Uniform finite-horizon count bounds | `lem:v2counts` | proved | `RootPUCT.lean`: `RootPUCTTrace.count_le`, `count_lower_exact`, `count_lower`. Holds for every tie-breaking rule. |
| 42 | App. E | Corollary: Fixed gaps versus a shrinking gap | `cor:v2countscales` | proved | `RootPUCT.lean`: `RootPUCTTrace.count_optimal_linear`, `count_shrinking_gap`, in explicit form. The shrinking-gap bound needs `t ≥ 2K`, which the manuscript does not state. |
| 43 | App. E | Lemma: Nesting and actual endpoint changes | `lem:v2strict` | proved | `RootPUCT.lean`: `rootPuctRadius_strictAntiOn`, `rootPuctLo_mono`, `rootPuctHi_anti`, `rootPuctHi_strict`. |
| 44 | App. E | Theorem: A sharp certification-horizon scale | `thm:v2horizon` | proved | `RootPUCT.lean`: `v2horizon`, as explicit two-sided bounds with one constant valid for all `g ∈ (0, 1/8]`, rather than asymptotic notation. |
| 45 | App. E | Proposition: Uniformly early retirement and changing revisits | `prop:v2postcut` | proved | `RootPUCT.lean`: `v2postcut`, `cut3_uniform`, `cut3_strict_change`. |
| 46 | App. E | Theorem: Root-PUCT work separation from uninformative initialization | `thm:v2separation` | partial | `RootPUCT.lean`: `v2separation_horizon` (proved), `v2separation_work` (assuming the per-operation accounting inequalities for the two monitors). Open: a cost model for the monitors and the identification of the `m`-leaf root process with the three-terminal process. |
| 47 | App. E | Corollary: One explicit polynomial instance | `cor:v2quarter` | partial | `RootPUCT.lean`: `v2quarter_horizon`, `v2quarter_work`; same open parts as `thm:v2separation`. |
| 48 | App. E | Proposition: The family does not lower-bound all numerical oracles | `prop:v2escape` | partial | `PassiveRetirement.lean`: `MaxCirc.eval_of_onlyTerm`, `MaxCirc.interval_of_onlyTerm`. Open: the `O(m + τ)` operation count. |
| 49 | App. E | Theorem: Support-sensitive certification under recursive PUCT | `thm:puct-noisy-main` | proved | `Assembly.lean`: `puct_noisy_main_tape`, whose only probabilistic input is the reward-tape model (bounded tapes with the stated means, independent within each tape). `RecursivePUCT.lean`: `puct_noisy_main`, `puct_certification_core`, `exists_horizon`, `full_support_certified`. Assumed: the specification of the stopping monitor. Stated as failure probability at most `δ/2`. |
| 50 | App. E | Theorem: Uniform local PUCT revisit bound under changing values | `thm:v35local` | proved | `RecursivePUCT.lean`: `local_puct_revisit`, `local_puct_core`. |
| 51 | App. E | Theorem: Pathwise terminal coverage under recursive local PUCT | `thm:v35dag` | proved | `RecursivePUCT.lean`: `puct_terminal_coverage`, `terminal_sampled_unboundedly`. |
| 52 | App. E | Lemma: Anytime coverage and a usable width bound | `lem:v35width` | proved | `RecursivePUCT.lean`: `hoeffding_tape_coverage` (from Mathlib's Hoeffding inequality), `running_box_covers`, `running_box_width_bt`. |
| 53 | App. E | Theorem: High-probability on-policy PUCT certification horizon | `thm:v35horizon` | proved | `RecursivePUCT.lean`: `puct_horizon_full`, `puct_horizon`. Assumed: the specification of the stopping monitor. Stated as failure probability at most `δ/2`. |
| 54 | App. E | Corollary: Polynomial accuracy dependence at fixed depth | `cor:v35poly` | partial | `RecursivePUCT.lean`: `poly_horizon`, `horizon_condition_of_poly` (polynomial degree `2/(r−s)` for every `s > 0`). Open: the form with an explicit logarithmic factor and the oracle-substitution clause. |
| 55 | App. E | Proposition: Positive-variance root PUCT: almost-sure square-root counts | `prop:v35rootrates` | proved | `RecursivePUCT.lean`: `root_puct_sqrt_rates_ae` (almost surely, via the strong law), `root_puct_upper`, `pullCount_unbounded`; the matching lower rate is `local_puct_revisit`. |
| 56 | App. E | Counterexample: Zero prior at one internal edge prevents terminal coverage | `ce:v35prior` | proved | `RecursivePUCT.lean`: `zero_prior_never_selected`, `zero_prior_run_exists`. The Bernoulli terminals are abstracted to a nonnegative value on the other edge. |
| 57 | App. K | Theorem: Exact coupling and charged maintenance | `thm:adaptive-oracle-coupling` | partial | `Representation.lean`: `exact_coupling`, `dualCover_incidence_bound` (`B ≤ 2h(2R_run + K)` for an existing cover under every layout). Open: the compile-work, update-work and space claims (no cost model for the segment-tree and heap algorithm). |
| 58 | App. K | Proposition: Trajectory Coupling Across Circuit Representations | `prop:representation-coupling` | proved | `Representation.lean`: `MaxCircuit.eval_eq_sup`, `eval_unary`, `eval_gate_congr`, `eval_dyadicCircuit`, `representation_coupling`, `MaxCircuit.retire_preserves`, `retirement_coupling`. One retirement step is proved; the induction over successive retirements is a hypothesis of `retirement_coupling`. |
| 59 | App. K | Proposition: Unified Full-Cost Representation Comparison | `prop:representation-cost` | partial | `Representation.lean`: `deliveries_le_Splus`, `Sminus_le_deliveries`, `work_upper`, `work_lower`, `representation_advantage`. Assumed: the per-operation charges of the indexed-heap engine. Open: a formal engine satisfying them. |
| 60 | App. K | Theorem: Every-layout limit of flat dyadic compilation | `thm:coded-main` | partial | `Representation.lean`: the every-layout `Ω(r³)` half via `parityGrid_cover_lower`. Open: the `O(r² log² r)` upper half (needs a TA-UCT process and a cost model). |
| 61 | App. K | Theorem: Every-Layout Dyadic Cover Lower Bound | `thm:coded-covers` | partial | `Representation.lean`: `parity_separation`, `total_runs_lower`, `runs_le_card_of_cover`, `parityGrid_runs_lower`, `parityGrid_cover_lower` (`r³ ≤ 2 Σ|C_p|` for every layout and every dyadic cover; slightly stronger than the manuscript). Open: the stopping-work step. |
| 62 | App. K | Proposition: Equivalence Under Unrestricted Circuit Retention | `prop:unrestricted-compiler` | partial | `Representation.lean`: `retained_circuit_coupling` (semantic equivalence). Open: the `O(|V|+|E|)` copy cost. |

## What remains

- **Change of measure for stopped adaptive processes.** Needed by `lem:active-com`, `thm:ast-main`, `thm:v34-converse` and the Gaussian lower bounds. Requires a model of an adaptive sampler with a stopping time and a Wald-type identity for its log-likelihood ratio.
- **Martingale concentration not in Mathlib.** The self-normalized bound (`thm:t3-misspec`), the exponential supermartingale for bounded differences (empirical-Bernstein part of `lem:nested-interval-valid`), the Gaussian mixture martingale (`lem:bay-cs`), and chi-square tails (`lem:v34-concentration`). Ville's inequality is now proved in `Coverage.lean`.
- **Tracking arguments.** The matching upper bounds in `thm:ast-main` and `thm:v34-adaptive`.
- **Cost models.** Every running-time, work and memory claim (Appendix K, the work-separation theorems of Appendix E) needs a formal model of the monitors and data structures; only their accounting consequences are proved.
- **Assembly.** Formal models of Algorithms 1 and 2 to turn the modular theorems of the main text and Appendix B into single statements, and wiring already-proved facts (Hoeffding coverage, Ville) into the theorems that still take them as hypotheses.
