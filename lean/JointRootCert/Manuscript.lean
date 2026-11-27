/-
Joint Root Certification: reviewer-facing index of all 62 numbered results of the manuscript.
-/
import JointRootCert

/-!
# Index of the manuscript's numbered results

One section per numbered result of `manuscript/joint_cert_manuscript.tex` (62 results), in the
order of the LaTeX source, which is also the order of the "Result-by-result status" table in
`lean/README.md`. Numbers (Theorem 2.1, Lemma A.1, ...) are those of the compiled manuscript.

Each section contains

* a main theorem named after the LaTeX label (`thm:t4-finite-sample` becomes
  `thm_t4_finite_sample`), whose doc comment gives the manuscript statement in words (notation
  paraphrased) and the modelling notes of the README row;
* for some results, companion theorems (suffixed names) for the other clauses of the statement or
  for an instance showing that the hypotheses can be met.

Every theorem here restates, in full, the statement of the final Lean theorem cited for that
result in the README, and is proved by applying that theorem to the hypotheses. Lean therefore
checks that each statement printed in this file is the cited theorem's statement (up to
definitional unfolding); nothing new is proved here. The statements were produced by printing the
elaborated types of the cited theorems and checking that they elaborate back to the same
propositions; a few printed with explicit numeral types (`(2 : ℝ)`) or with
the filtration argument of `Measurable`/`MeasurableSet` written explicitly, where the default printing does not elaborate.

Definitions used in the statements live in the cited files; the modelling choices are listed in
`lean/README.md` ("How statements are modelled", "Hypotheses the manuscript left implicit",
"Limits of the formalization").

To list the axioms of every theorem in this file, run `scripts/check_axioms.sh` from `lean/`; it
fails if any theorem depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`.
-/

universe u u_1 u_2 u_3 u_4 u_5 u_6

-- The statements are printed from elaborated types, which keep the names of bound variables
-- that the statement does not use.
set_option linter.unusedVariables false

namespace JointRootCert.Manuscript

/-! ### `thm:bay-main-dual`: Theorem 2.1 (Exact joint ellipsoidal certificate and sparse witnesses) -/

/-- **Theorem 2.1** `thm:bay-main-dual`: Exact joint ellipsoidal certificate and sparse witnesses.

Manuscript: For any proper support S(a), its worst-case regret over the ellipsoid Θ_t is R_t(a) =
[max_{z ∉ S(a)} D_t(z, S(a))]_+, where D_t(z, S) = min_{p ∈ Δ(S)} [g_{z,p}ᵀ m_t + β_t ‖L_tᵀ
g_{z,p}‖₂]. There exists an optimal inside mixture with at most rank(L_t) + 1 nonzero entries. Any
feasible mixture yields a certifying upper bound on D_t, also for singular covariance.

Lean: `ellipsoid_certificate_iff` (`JointRootCert/Ellipsoid.lean`). The ellipsoid is `m +
L(B₂(β))` for a linear map `L` between finite-dimensional inner product spaces, with no rank
condition. The main statement is the certificate form; the value form and the sparse witness are
the companions. The minimax identity is proved by Hahn-Banach separation rather than Sion's
theorem. The sharpness example for rank + 1 is not formalized. -/
theorem thm_bay_main_dual
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : Type u_3}
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {S : Finset Z}
    {β : ℝ}
    {ε : ℝ}
    (hS : S.Nonempty)
    (hβ : 0 ≤ β)
    (φ : Z → E)
    (m : E)
    (L : F →ₗ[ℝ] E) :
      (∀ θ ∈ ellipsoid m L β, regret S hS (env φ θ) ≤ ε) ↔ 0 ≤ ε ∧ ∀ z ∉ S, ∃ p ∈ simplex ↥S, ellObj φ S m L β z p ≤ ε :=
  @ellipsoid_certificate_iff Z _ _ _ E _ _ _ F _ _ _ S β ε hS hβ φ m L

/-- Companion to Theorem 2.1 `thm:bay-main-dual`: the worst-case regret as a value (`sSup`). Lean:
`robustRegret_ellipsoid` (`JointRootCert/Ellipsoid.lean`). -/
theorem thm_bay_main_dual_value
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : Type u_3}
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {S : Finset Z}
    {β : ℝ}
    (hS : S.Nonempty)
    (hSc : Sᶜ.Nonempty)
    (hβ : 0 ≤ β)
    (φ : Z → E)
    (m : E)
    (L : F →ₗ[ℝ] E) :
      robustRegret S hS (env φ '' ellipsoid m L β) = max 0 (Sᶜ.sup' hSc (ellD φ S m L β)) :=
  @robustRegret_ellipsoid Z _ _ _ E _ _ _ F _ _ _ S β hS hSc hβ φ m L

/-- Companion to Theorem 2.1 `thm:bay-main-dual`: an optimal inside mixture with at most rank(L) + 1
nonzero entries. Lean: `ellipsoid_sparse_witness` (`JointRootCert/Sparse.lean`). -/
theorem thm_bay_main_dual_sparse
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : Type u_3}
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {S : Finset Z}
    (hS : Finset.Nonempty S)
    {β : ℝ}
    (hβ : (0 : ℝ) ≤ β)
    (φ : Z → E)
    (m : E)
    (L : F →ₗ[ℝ] E)
    (z : Z) :
      ∃ p ∈ simplex ↥S,
        IsLeast (ellObj φ S m L β z '' simplex ↥S) (ellObj φ S m L β z p) ∧
          Finset.card {y : ↥S | p y ≠ (0 : ℝ)} ≤ Module.finrank ℝ ↥(LinearMap.range L) + (1 : ℕ) :=
  @ellipsoid_sparse_witness Z _ _ _ E _ _ _ F _ _ _ S hS β hβ φ m L z

/-! ### `thm:t4-finite-sample`: Theorem 2.2 (Finite-sample cost of safeguarded CD-Joint) -/

/-- **Theorem 2.2** `thm:t4-finite-sample`: Finite-sample cost of safeguarded CD-Joint.

Manuscript: Assume the fixed-feature, unit-noise model, a positive, nondecreasing self-normalized
radius β_t, anytime-valid at level 0 < δ < 1, with liminf_{t→∞} β_t² log t / t = 0, a query
dictionary containing all terminal features, and 0 < c_x ≤ c_max. Let L_φ = max_x ‖φ_x‖₂ and ε >
0. On simultaneous confidence coverage, exact CD-Joint returns an ε-optimal root action and its
cumulative query cost satisfies Σ_{t=1}^{τ} c_{x_t} ≤ 16 c_max (1 + L_φ²/λ) β_{τ-1}² / ε² ·
log(det V_τ / λ^d).

Lean: `LiteralF1.t4_finite_sample` (`JointRootCert/LiteralF1.lean`). A run of Algorithm 1 is an
infinite sequence with the first certified time `cdStop`; no stopping time is presupposed. The
liminf is taken in `EReal`. The main theorem holds for any radius with the stated properties; the
companion discharges every hypothesis jointly for i.i.d. standard Gaussian noise on `ℕ → ℝ`, with
a causal policy making the algorithm's choices in its order with fixed tie-breaking (so the main
theorem is not vacuous). -/
theorem thm_t4_finite_sample
    {n : Type u_1}
    [Fintype n]
    [DecidableEq n]
    {X : Type u_2}
    [Fintype X]
    [DecidableEq X]
    {Z : Type u_3}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_4}
    {Ω : Type u_5}
    {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω}
    [Nonempty n]
    [MeasureTheory.IsProbabilityMeasure μ]
    {lam : ℝ}
    {δ : ℝ}
    (hlam : 0 < lam)
    (φ : X → n → ℝ)
    (cost : X → ℝ)
    {cmax : ℝ}
    {Lsq : ℝ}
    {ε : ℝ}
    (hcost : ∀ (x : X), 0 < cost x ∧ cost x ≤ cmax)
    (hφ : ∀ (x : X), φ x ⬝ᵥ φ x ≤ Lsq)
    (hε : 0 < ε)
    (ι : Z → X)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (θs : n → ℝ)
    (x : ℕ → Ω → X)
    (m : ℕ → Ω → n → ℝ)
    (β : ℕ → Ω → ℝ)
    (hβpos : ∀ (t : ℕ) (ω : Ω), 0 < β t ω)
    (hβmono : ∀ (ω : Ω), Monotone fun t => β t ω)
    (hcov : (μ : Set Ω → ENNReal) {ω | ∃ t, β t ω ^ 2 < (θs - m t ω) ⬝ᵥ (design lam φ (fun s => x s ω) t).mulVec (θs - m t ω)} ≤
  ENNReal.ofReal δ)
    (hliminf : ∀ (ω : Ω), Filter.liminf (fun t => (↑(β t ω ^ 2 * Real.log (↑t : ℝ) / (↑t : ℝ)) : EReal)) Filter.atTop = 0)
    (hrun : ∀ (ω : Ω), LiteralABC2.CDRun lam φ cost ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω) :
      (∀ (ω : Ω),
          LiteralABC2.CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)
              (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω) ∧
            ∑ t ∈ Finset.range (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω),
                cost (x t ω) ≤
              16 * cmax * (1 + Lsq / lam) *
                    β ((LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω) - 1) ω ^ 2 /
                  ε ^ 2 *
                Real.log
                  ((design lam φ (fun s => x s ω)
                        (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω)).det /
                    lam ^ Fintype.card n)) ∧
        (∀ (ω : Ω),
            (∀ (t : ℕ), (θs - m t ω) ⬝ᵥ (design lam φ (fun s => x s ω) t).mulVec (θs - m t ω) ≤ β t ω ^ 2) →
              ∀ (r : A),
                cdDualCert
                    (design lam φ (fun s => x s ω)
                      (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω))
                    (fun z => φ (ι z))
                    (m (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω) ω)
                    (β (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω) ω) ε (supp r) →
                  (regret (supp r) (hne r) fun z => φ (ι z) ⬝ᵥ θs) ≤ ε) ∧
          (μ : Set Ω → ENNReal)
              {ω |
                ¬∀ (r : A),
                    cdDualCert
                        (design lam φ (fun s => x s ω)
                          (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω))
                        (fun z => φ (ι z))
                        (m (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω) ω)
                        (β (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) fun t => β t ω) ω) ε
                        (supp r) →
                      (regret (supp r) (hne r) fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤
            ENNReal.ofReal δ :=
  @LiteralF1.t4_finite_sample n _ _ X _ _ Z _ _ _ A Ω m0 μ _ _ lam δ hlam φ cost cmax Lsq ε hcost hφ hε ι supp hne θs x m β hβpos hβmono hcov hliminf hrun

/-- Companion to Theorem 2.2 `thm:t4-finite-sample`: all hypotheses discharged for Gaussian noise and
the sequential fixed-tie-breaking policy. Lean: `LiteralG3.t4_finite_sample_gaussian_seq`
(`JointRootCert/LiteralG3.lean`). -/
theorem thm_t4_finite_sample_gaussian
    {n : Type u_1}
    [Fintype n]
    [DecidableEq n]
    {X : Type u_2}
    [Fintype X]
    [DecidableEq X]
    {Z : Type u_3}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_4}
    [Nonempty A]
    [Nonempty n]
    {lam : ℝ}
    {δ : ℝ}
    {B : ℝ}
    (hlam : 0 < lam)
    (hδ0 : 0 < δ)
    (hδ1 : δ < 1)
    (hB : 0 ≤ B)
    (φ : X → n → ℝ)
    (cost : X → ℝ)
    {cmax : ℝ}
    {Lsq : ℝ}
    {ε : ℝ}
    (hcost : ∀ (x : X), 0 < cost x ∧ cost x ≤ cmax)
    (hφ : ∀ (x : X), φ x ⬝ᵥ φ x ≤ Lsq)
    (hε : 0 < ε)
    (ι : Z → X)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    (θs : n → ℝ)
    (hθ : θs ⬝ᵥ θs ≤ B ^ 2) :
      have x := LiteralG3.gQ3 lam 1 δ B ε φ cost ι supp θs;
      (∀ (s : ℕ) (x0 : X), @MeasurableSet (ℕ → ℝ) (LiteralG1.nFilt s) {ω | x s ω = x0}) ∧
        (∀ (t : ℕ) (ω : ℕ → ℝ), 0 < LiteralG1.gRad 1 lam δ B φ x t ω) ∧
          (∀ (ω : ℕ → ℝ), Monotone fun t => LiteralG1.gRad 1 lam δ B φ x t ω) ∧
            (LiteralG1.noiseP (ProbabilityTheory.gaussianReal 0 1) : Set (ℕ → ℝ) → ENNReal)
                  {ω |
                    ∃ t,
                      LiteralG1.gRad 1 lam δ B φ x t ω ^ 2 <
                        (θs - LiteralG1.gEst lam φ θs x t ω) ⬝ᵥ
                          (design lam φ (fun s => x s ω) t).mulVec (θs - LiteralG1.gEst lam φ θs x t ω)} ≤
                ENNReal.ofReal δ ∧
              (∀ (ω : ℕ → ℝ),
                  Filter.liminf (fun t => (↑(LiteralG1.gRad 1 lam δ B φ x t ω ^ 2 * Real.log (↑t : ℝ) / (↑t : ℝ)) : EReal))
                      Filter.atTop =
                    0) ∧
                (∀ (ω : ℕ → ℝ),
                    LiteralABC2.CDRun lam φ cost ι supp ε (fun s => x s ω) (fun t => LiteralG1.gEst lam φ θs x t ω) fun t =>
                      LiteralG1.gRad 1 lam δ B φ x t ω) ∧
                  (∀ (ω : ℕ → ℝ),
                      LiteralABC2.CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => LiteralG1.gEst lam φ θs x t ω)
                          (fun t => LiteralG1.gRad 1 lam δ B φ x t ω)
                          (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => LiteralG1.gEst lam φ θs x t ω)
                            fun t => LiteralG1.gRad 1 lam δ B φ x t ω) ∧
                        ∑
                            t ∈
                              Finset.range
                                (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => LiteralG1.gEst lam φ θs x t ω)
                                  fun t => LiteralG1.gRad 1 lam δ B φ x t ω),
                            cost (x t ω) ≤
                          16 * cmax * (1 + Lsq / lam) *
                                LiteralG1.gRad 1 lam δ B φ x
                                    ((LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω)
                                        (fun t => LiteralG1.gEst lam φ θs x t ω) fun t => LiteralG1.gRad 1 lam δ B φ x t ω) -
                                      1)
                                    ω ^
                                  2 /
                              ε ^ 2 *
                            Real.log
                              ((design lam φ (fun s => x s ω)
                                    (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω)
                                      (fun t => LiteralG1.gEst lam φ θs x t ω) fun t =>
                                      LiteralG1.gRad 1 lam δ B φ x t ω)).det /
                                lam ^ Fintype.card n)) ∧
                    (∀ (ω : ℕ → ℝ),
                        (∀ (t : ℕ),
                            (θs - LiteralG1.gEst lam φ θs x t ω) ⬝ᵥ
                                (design lam φ (fun s => x s ω) t).mulVec (θs - LiteralG1.gEst lam φ θs x t ω) ≤
                              LiteralG1.gRad 1 lam δ B φ x t ω ^ 2) →
                          ∀ (r : A),
                            cdDualCert
                                (design lam φ (fun s => x s ω)
                                  (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => LiteralG1.gEst lam φ θs x t ω)
                                    fun t => LiteralG1.gRad 1 lam δ B φ x t ω))
                                (fun z => φ (ι z))
                                (LiteralG1.gEst lam φ θs x
                                  (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => LiteralG1.gEst lam φ θs x t ω)
                                    fun t => LiteralG1.gRad 1 lam δ B φ x t ω)
                                  ω)
                                (LiteralG1.gRad 1 lam δ B φ x
                                  (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω) (fun t => LiteralG1.gEst lam φ θs x t ω)
                                    fun t => LiteralG1.gRad 1 lam δ B φ x t ω)
                                  ω)
                                ε (supp r) →
                              (regret (supp r) (hne r) fun z => φ (ι z) ⬝ᵥ θs) ≤ ε) ∧
                      (LiteralG1.noiseP (ProbabilityTheory.gaussianReal 0 1) : Set (ℕ → ℝ) → ENNReal)
                          {ω |
                            ¬∀ (r : A),
                                cdDualCert
                                    (design lam φ (fun s => x s ω)
                                      (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω)
                                        (fun t => LiteralG1.gEst lam φ θs x t ω) fun t => LiteralG1.gRad 1 lam δ B φ x t ω))
                                    (fun z => φ (ι z))
                                    (LiteralG1.gEst lam φ θs x
                                      (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω)
                                        (fun t => LiteralG1.gEst lam φ θs x t ω) fun t => LiteralG1.gRad 1 lam δ B φ x t ω)
                                      ω)
                                    (LiteralG1.gRad 1 lam δ B φ x
                                      (LiteralABC2.cdStop lam φ ι supp ε (fun s => x s ω)
                                        (fun t => LiteralG1.gEst lam φ θs x t ω) fun t => LiteralG1.gRad 1 lam δ B φ x t ω)
                                      ω)
                                    ε (supp r) →
                                  (regret (supp r) (hne r) fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤
                        ENNReal.ofReal δ :=
  @LiteralG3.t4_finite_sample_gaussian_seq n _ _ X _ _ Z _ _ _ A _ _ lam δ B hlam hδ0 hδ1 hB φ cost cmax Lsq ε hcost hφ hε ι supp hne hcov θs hθ

/-! ### `lem:bay-reduction`: Lemma A.1 (Joint-set reduction) -/

/-- **Lemma A.1** `lem:bay-reduction`: Joint-set reduction.

Manuscript: For every nonempty compact C, R_C(a) = max{0, max_{z ∉ S(a)} D_C(z, S(a))} with D_C(z,
S) = max_{θ ∈ C} min_{y ∈ S} (φ_z − φ_y)ᵀ θ. The value is zero when the exterior is empty.

Lean: `LiteralABC.bay_reduction_compact` (`JointRootCert/LiteralABC.lean`). Maxima are attained,
as stated. -/
theorem lem_bay_reduction
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {S : Finset Z}
    {hS : S.Nonempty}
    (C : Set (Z → ℝ))
    (hC : C.Nonempty)
    (hCc : IsCompact C)
    (hSc : Sᶜ.Nonempty) :
      (∀ (z : Z), IsGreatest ((fun f => adv S hS f z) '' C) (robustAdv S hS C z)) ∧
        IsGreatest (regret S hS '' C) (max 0 (Sᶜ.sup' hSc (robustAdv S hS C))) :=
  @LiteralABC.bay_reduction_compact Z _ _ _ S hS C hC hCc hSc

/-! ### `thm:shared-regret`: Theorem A.2 (Exact rectangular shared-support certificate) -/

/-- **Theorem A.2** `thm:shared-regret`: Exact rectangular shared-support certificate.

Manuscript: For every nonempty confidence box and proper root support, the robust regret equals
the outside-support expression of eq:exact-robust-regret. For full support it is zero.

Lean: `rect_isGreatest` (`JointRootCert/Rectangular.lean`). The main theorem states that the
outside-support expression is the greatest regret over the box (`IsGreatest`); companions: the
full-support case and the comparison with the marginal bound. -/
theorem thm_shared_regret
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {S : Finset Z}
    {hS : S.Nonempty}
    {l : Z → ℝ}
    {u : Z → ℝ}
    (hlu : l ≤ u)
    (hSc : Sᶜ.Nonempty) :
      IsGreatest (regret S hS '' Set.Icc l u) (rectCert S hS hSc l u) :=
  @rect_isGreatest Z _ _ _ S hS l u hlu hSc

/-- Companion to Theorem A.2 `thm:shared-regret`: for full support the robust regret is zero. Lean:
`robustRegret_box_full` (`JointRootCert/Rectangular.lean`). -/
theorem thm_shared_regret_full
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {S : Finset Z}
    {hS : S.Nonempty}
    {l : Z → ℝ}
    {u : Z → ℝ}
    (hlu : l ≤ u)
    (hSc : Sᶜ = ∅) :
      robustRegret S hS (Set.Icc l u) = 0 :=
  @robustRegret_box_full Z _ _ _ S hS l u hlu hSc

/-- Companion to Theorem A.2 `thm:shared-regret`: the rectangular certificate is at most the marginal
bound. Lean: `rectCert_le_marginal` (`JointRootCert/Rectangular.lean`). -/
theorem thm_shared_regret_marginal
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {S : Finset Z}
    {hS : S.Nonempty}
    {l : Z → ℝ}
    {u : Z → ℝ}
    {A : Type u_2}
    (supp : A → Finset Z)
    (a : A)
    (hsupp : supp a = S)
    (hcover : ∀ z ∉ S, ∃ b, b ≠ a ∧ z ∈ supp b)
    (hSc : Sᶜ.Nonempty)
    {M : ℝ}
    (hM : ∀ (b : A), b ≠ a → ∀ z ∈ supp b, u z ≤ M) :
      rectCert S hS hSc l u ≤ max 0 (M - S.sup' hS l) :=
  @rectCert_le_marginal Z _ _ _ S hS l u A supp a hsupp hcover hSc M hM

/-! ### `cor:shared-regret-pac`: Corollary A.3 (Anytime-valid root commitment) -/

/-- **Corollary A.3** `cor:shared-regret-pac`: Anytime-valid root commitment.

Manuscript: Under the simultaneous coverage condition eq:terminal-box, returning any action with
robust regret at most ε incurs error probability at most δ for any predictable adaptive
terminal-sampling policy.

Lean: `LiteralABC.anytime_valid_commitment_stopping` (`JointRootCert/LiteralABC.lean`). Stated at
a stopping time that may be infinite (the procedure may never stop). The companion is the version
for terminal boxes. -/
theorem cor_shared_regret_pac
    {Z : Type u_1}
    [Fintype Z]
    [Nonempty Z]
    {A : Type u_2}
    {Ω : Type u_3}
    [MeasurableSpace Ω]
    {ε : ℝ}
    (P : MeasureTheory.Measure Ω)
    (μ : Z → ℝ)
    (δ : ENNReal)
    (C : ℕ → Ω → Set (Z → ℝ))
    (supp : A → Finset Z)
    (hsupp : ∀ (a : A), (supp a).Nonempty)
    (out : Ω → Option (ℕ × A))
    (hcover : (P : Set Ω → ENNReal) {ω | ∃ t, μ ∉ C t ω} ≤ δ)
    (hcert : ∀ (ω : Ω) (t : ℕ) (a : A), out ω = some (t, a) → ∀ f ∈ C t ω, regret (supp a) (hsupp a) f ≤ ε) :
      (P : Set Ω → ENNReal) {ω | ∃ t a, out ω = some (t, a) ∧ ε < regret (supp a) (hsupp a) μ} ≤ δ :=
  @LiteralABC.anytime_valid_commitment_stopping Z _ _ A Ω _ ε P μ δ C supp hsupp out hcover hcert

/-- Companion to Corollary A.3 `cor:shared-regret-pac`: the version for terminal confidence boxes.
Lean: `LiteralABC.anytime_valid_commitment_box_stopping` (`JointRootCert/LiteralABC.lean`). -/
theorem cor_shared_regret_pac_box
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_2}
    {Ω : Type u_3}
    [MeasurableSpace Ω]
    {ε : ℝ}
    (P : MeasureTheory.Measure Ω)
    (μ : Z → ℝ)
    (δ : ENNReal)
    (l : ℕ → Ω → Z → ℝ)
    (u : ℕ → Ω → Z → ℝ)
    (supp : A → Finset Z)
    (hsupp : ∀ (a : A), (supp a).Nonempty)
    (out : Ω → Option (ℕ × A))
    (hcover : (P : Set Ω → ENNReal) {ω | ∃ t, μ ∉ Set.Icc (l t ω) (u t ω)} ≤ δ)
    (hcert : ∀ (ω : Ω) (t : ℕ) (a : A), out ω = some (t, a) → robustRegret (supp a) (hsupp a) (Set.Icc (l t ω) (u t ω)) ≤ ε) :
      (P : Set Ω → ENNReal) {ω | ∃ t a, out ω = some (t, a) ∧ ε < regret (supp a) (hsupp a) μ} ≤ δ :=
  @LiteralABC.anytime_valid_commitment_box_stopping Z _ _ _ A Ω _ ε P μ δ l u supp hsupp out hcover hcert

/-! ### `thm:t2-hull`: Theorem A.4 (Feature-hull dominance) -/

/-- **Theorem A.4** `thm:t2-hull`: Feature-hull dominance.

Manuscript: Let P_a = conv{φ_y : y ∈ S(a)} and P_Z = conv{φ_z : z ∈ Z}. Then V(a; θ) = V*(θ) for
all θ if and only if P_Z ⊆ P_a. For a feature norm ‖·‖ and parameter dual norm ‖·‖_*, ‖θ‖_* ≤ B
implies regret at most B max_{z ∉ S(a)} inf_{p ∈ P_a} ‖φ_z − p‖ (zero for an empty complement).

Lean: `LiteralABC.regret_le_hullGap` (`JointRootCert/LiteralABC.lean`). The main theorem is the
literal hull-gap bound; the companion is the dominance equivalence. -/
theorem thm_t2_hull
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {S : Finset Z}
    (hS : S.Nonempty)
    (φ : Z → E)
    {B : ℝ}
    {θ : StrongDual ℝ E}
    (hθ : ‖θ‖ ≤ B) :
      regret S hS (dualEnv φ θ) ≤ B * LiteralABC.hullGap φ S :=
  @LiteralABC.regret_le_hullGap Z _ _ _ E _ _ S hS φ B θ hθ

/-- Companion to Theorem A.4 `thm:t2-hull`: V(a; θ) = V*(θ) for all θ iff P_Z ⊆ P_a. Lean:
`feature_hull_dominance` (`JointRootCert/FeatureHull.lean`). -/
theorem thm_t2_hull_dominance
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {S : Finset Z}
    (hS : S.Nonempty)
    (φ : Z → E) :
      (∀ (θ : StrongDual ℝ E), val S hS (dualEnv φ θ) = gmax (dualEnv φ θ)) ↔
        (convexHull ℝ : Set E → Set E) (Set.range φ) ⊆ (convexHull ℝ : Set E → Set E) (φ '' (↑S : Set Z)) :=
  @feature_hull_dominance Z _ _ _ E _ _ S hS φ

/-! ### `thm:active-er`: Theorem B.2 (Finite-sample support-sensitive acquisition) -/

/-- **Theorem B.2** `thm:active-er`: Finite-sample support-sensitive acquisition.

Manuscript: On simultaneous coverage, for the specified rules, τ_ER ≤ Σ_z n_{M,δ}(max{ε, Δ_z/2}),
τ_SG ≤ Σ_z n_{M,δ}(max{ε/2, Δ_z/3}), τ_OS ≤ Σ_z n_{M,δ}(max{Γ + ε, Δ_z}/2). ER/SG require 0 < ε <
1; OS permits ε = 0 when Γ > 0. These are observation bounds, not end-to-end runtime guarantees.

Lean: `LiteralABC.active_er_literal` (`JointRootCert/LiteralABC.lean`). `invCount` is the minimal
count n_{M,δ}. Each rule is an infinite run with the first certified time. Supports must cover
`Z`, and `M ≥ max{2, |Z|}`. Main theorem: exact-regret sampling; companions: Safeguarded-LCB and
optimistic separation. -/
theorem thm_active_er
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_2}
    {Ω : Type u_3}
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    (hmeas : ∀ (z : Z) (i : ℕ), AEMeasurable (X z i) P)
    (hbdd : ∀ (z : Z) (i : ℕ), ∀ᵐ (ω : Ω) ∂P, X z i ω ∈ Set.Icc 0 1)
    {m : Z → ℝ}
    (hmean : ∀ (z : Z) (i : ℕ), ∫ (ω : Ω), X z i ω ∂P = m z)
    {M : ℝ}
    {δ : ℝ}
    (hM : 2 ≤ M)
    (hcard : (↑(Fintype.card Z) : ℝ) ≤ M)
    (hδ0 : 0 < δ)
    (hδ1 : δ < 1)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    {ε : ℝ}
    (hε0 : 0 < ε)
    (sel : Ω → ℕ → Z)
    (hrun : ∀ (ω : Ω), LiteralABC.ActiveRun supp hne M δ ε (LiteralABC.ERRule supp hne ε) (fun z i => X z i ω) (sel ω)) :
      (P : Set Ω → ENNReal)
          {ω |
            ¬((∃ t,
                  LiteralABC.Certified supp hne (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
                    (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε) ∧
                LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω) ≤
                    ∑ z, LiteralABC.invCount M δ (max ε ((gmax m - m z) / 2)) ∧
                  ∀ (a : A),
                    LiteralABC.exactCert (supp a) (hne a)
                          (tapeLo M δ (fun z i => X z i ω) (sel ω)
                            (LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω)))
                          (tapeHi M δ (fun z i => X z i ω) (sel ω)
                            (LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω))) ≤
                        ε →
                      regret (supp a) (hne a) m ≤ ε)} ≤
        ENNReal.ofReal δ :=
  @LiteralABC.active_er_literal Z _ _ _ A Ω _ P _ X hindep hmeas hbdd m hmean M δ hM hcard hδ0 hδ1 supp hne hcov ε hε0 sel hrun

/-- Companion to Theorem B.2 `thm:active-er`: the Safeguarded-LCB bound. Lean:
`LiteralABC.active_sg_literal` (`JointRootCert/LiteralABC.lean`). -/
theorem thm_active_er_sg
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_2}
    {Ω : Type u_3}
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    (hmeas : ∀ (z : Z) (i : ℕ), AEMeasurable (X z i) P)
    (hbdd : ∀ (z : Z) (i : ℕ), ∀ᵐ (ω : Ω) ∂P, X z i ω ∈ Set.Icc 0 1)
    {m : Z → ℝ}
    (hmean : ∀ (z : Z) (i : ℕ), ∫ (ω : Ω), X z i ω ∂P = m z)
    {M : ℝ}
    {δ : ℝ}
    (hM : 2 ≤ M)
    (hcard : (↑(Fintype.card Z) : ℝ) ≤ M)
    (hδ0 : 0 < δ)
    (hδ1 : δ < 1)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    {ε : ℝ}
    (hε0 : 0 < ε)
    (sel : Ω → ℕ → Z)
    (hrun : ∀ (ω : Ω), LiteralABC.ActiveRun supp hne M δ ε (LiteralABC.SGRule supp hne ε) (fun z i => X z i ω) (sel ω)) :
      (P : Set Ω → ENNReal)
          {ω |
            ¬((∃ t,
                  LiteralABC.Certified supp hne (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
                    (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε) ∧
                LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω) ≤
                    ∑ z, LiteralABC.invCount M δ (max (ε / 2) ((gmax m - m z) / 3)) ∧
                  ∀ (a : A),
                    LiteralABC.exactCert (supp a) (hne a)
                          (tapeLo M δ (fun z i => X z i ω) (sel ω)
                            (LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω)))
                          (tapeHi M δ (fun z i => X z i ω) (sel ω)
                            (LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω))) ≤
                        ε →
                      regret (supp a) (hne a) m ≤ ε)} ≤
        ENNReal.ofReal δ :=
  @LiteralABC.active_sg_literal Z _ _ _ A Ω _ P _ X hindep hmeas hbdd m hmean M δ hM hcard hδ0 hδ1 supp hne hcov ε hε0 sel hrun

/-- Companion to Theorem B.2 `thm:active-er`: the optimistic-separation bound. Lean:
`LiteralABC.active_os_literal` (`JointRootCert/LiteralABC.lean`). -/
theorem thm_active_er_os
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_2}
    {Ω : Type u_3}
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    (hmeas : ∀ (z : Z) (i : ℕ), AEMeasurable (X z i) P)
    (hbdd : ∀ (z : Z) (i : ℕ), ∀ᵐ (ω : Ω) ∂P, X z i ω ∈ Set.Icc 0 1)
    {m : Z → ℝ}
    (hmean : ∀ (z : Z) (i : ℕ), ∫ (ω : Ω), X z i ω ∂P = m z)
    {M : ℝ}
    {δ : ℝ}
    (hM : 2 ≤ M)
    (hcard : (↑(Fintype.card Z) : ℝ) ≤ M)
    (hδ0 : 0 < δ)
    (hδ1 : δ < 1)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    {ε : ℝ}
    {Γ : ℝ}
    (hε0 : 0 ≤ ε)
    (hΓ : ∀ (hpr : ∀ (a : A), (supp a)ᶜ.Nonempty),
  IsGreatest (Set.range fun a => val (supp a) (hne a) m - (supp a)ᶜ.sup' (hpr a) m) Γ)
    (hpos : 0 < Γ + ε)
    (sel : Ω → ℕ → Z)
    (hrun : ∀ (ω : Ω), LiteralABC.ActiveRun supp hne M δ ε (LiteralABC.OSRule supp hne ε) (fun z i => X z i ω) (sel ω)) :
      (P : Set Ω → ENNReal)
          {ω |
            ¬((∃ t,
                  LiteralABC.Certified supp hne (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
                    (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε) ∧
                LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω) ≤
                    ∑ z, LiteralABC.invCount M δ (max (Γ + ε) (gmax m - m z) / 2) ∧
                  ∀ (a : A),
                    LiteralABC.exactCert (supp a) (hne a)
                          (tapeLo M δ (fun z i => X z i ω) (sel ω)
                            (LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω)))
                          (tapeHi M δ (fun z i => X z i ω) (sel ω)
                            (LiteralABC.stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω))) ≤
                        ε →
                      regret (supp a) (hne a) m ≤ ε)} ≤
        ENNReal.ofReal δ :=
  @LiteralABC.active_os_literal Z _ _ _ A Ω _ P _ X hindep hmeas hbdd m hmean M δ hM hcard hδ0 hδ1 supp hne hcov ε Γ hε0 hΓ hpos sel hrun

/-! ### `lem:active-width`: Lemma B.3 (Width charged to each selected terminal) -/

/-- **Lemma B.3** `lem:active-width`: Width charged to each selected terminal.

Manuscript: At each nonfailed continuing step of Exact-Regret-DAG-LUCB, the selected terminal z
has w_t(z) > ε. On the simultaneous coverage event, it also satisfies w_t(z) ≥ Δ_z/2.

Lean: `active_width` (`JointRootCert/ActiveWidth.lean`). -/
theorem lem_active_width
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_2}
    {l : Z → ℝ}
    {u : Z → ℝ}
    {ε : ℝ}
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hpr : ∀ (a : A), (supp a)ᶜ.Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    (hlu : l ≤ u)
    (hε : 0 ≤ ε)
    (a : A)
    (hmin : ∀ (c : A), rectCert (supp a) (hne a) (hpr a) l u ≤ rectCert (supp c) (hne c) (hpr c) l u)
    (hcont : ε < rectCert (supp a) (hne a) (hpr a) l u)
    {p : Z}
    {q : Z}
    (hp : p ∈ supp a)
    (hpmax : ∀ y ∈ supp a, u y ≤ u p)
    (hq : q ∉ supp a)
    (hqmax : ∀ z ∉ supp a, u z ≤ u q) :
      ε < max (u p - l p) (u q - l q) ∧
        ∀ μ ∈ Set.Icc l u,
          (u q - l q ≤ u p - l p → (gmax μ - μ p) / 2 ≤ u p - l p) ∧ (u p - l p ≤ u q - l q → (gmax μ - μ q) / 2 ≤ u q - l q) :=
  @active_width Z _ _ _ A l u ε supp hne hpr hcov hlu hε a hmin hcont p q hp hpmax hq hqmax

/-! ### `lem:active-inversion`: Lemma B.4 (Explicit confidence-width inversion) -/

/-- **Lemma B.4** `lem:active-inversion`: Explicit confidence-width inversion.

Manuscript: For M ≥ 2, 0 < δ < 1 and 0 < r ≤ 1, the inversion threshold of eq:active-inversion
satisfies n_{M,δ}(r) ≤ ⌈(32/r²) log(32M/(δ r²))⌉.

Lean: `LiteralABC.active_inversion_literal` (`JointRootCert/LiteralABC.lean`). Proved without the
monotonicity-by-derivative step. -/
theorem lem_active_inversion
    {M : ℝ}
    {δ : ℝ}
    {r : ℝ}
    (hM : 2 ≤ M)
    (hδ0 : 0 < δ)
    (hδ1 : δ < 1)
    (hr0 : 0 < r)
    (hr1 : r ≤ 1) :
      LiteralABC.invCount M δ r ≤ ⌈32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2))⌉₊ :=
  @LiteralABC.active_inversion_literal M δ r hM hδ0 hδ1 hr0 hr1

/-! ### `lem:active-os-width`: Lemma B.5 (Width charged by optimistic-separation sampling) -/

/-- **Lemma B.5** `lem:active-os-width`: Width charged by optimistic-separation sampling.

Manuscript: On the coverage event, if optimistic-separation sampling continues and selects
terminal z, then w_t(z) > (Γ + ε)/2 and w_t(z) ≥ Δ_z/2. Every nonfailed continuing step also
selects width strictly greater than ε/2 without assuming coverage.

Lean: `active_os_width` (`JointRootCert/ActiveWidth.lean`). -/
theorem lem_active_os_width
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_2}
    {l : Z → ℝ}
    {u : Z → ℝ}
    {ε : ℝ}
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hpr : ∀ (a : A), (supp a)ᶜ.Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    (hlu : l ≤ u)
    (hε : 0 ≤ ε)
    (b : A)
    (hmax : ∀ (c : A), osIndex (supp c) (hne c) (hpr c) l u ≤ osIndex (supp b) (hne b) (hpr b) l u)
    (hcont : ε < rectCert (supp b) (hne b) (hpr b) l u)
    {p : Z}
    {q : Z}
    (hp : p ∈ supp b)
    (hpmax : ∀ y ∈ supp b, u y ≤ u p)
    (hq : q ∉ supp b)
    (hqmax : ∀ z ∉ supp b, u z ≤ u q) :
      ε / 2 < max (u p - l p) (u q - l q) ∧
        ∀ μ ∈ Set.Icc l u,
          (∀ (a : A), (val (supp a) (hne a) μ - (supp a)ᶜ.sup' (hpr a) μ + ε) / 2 < max (u p - l p) (u q - l q)) ∧
            (u q - l q ≤ u p - l p → (gmax μ - μ p) / 2 ≤ u p - l p) ∧
              (u p - l p ≤ u q - l q → (gmax μ - μ q) / 2 ≤ u q - l q) :=
  @active_os_width Z _ _ _ A l u ε supp hne hpr hcov hlu hε b hmax hcont p q hp hpmax hq hqmax

/-! ### `thm:active-restart`: Theorem B.6 (Certified restart bound) -/

/-- **Theorem B.6** `thm:active-restart`: Certified restart bound.

Manuscript: Let 0 < δ ≤ 1/4, 0 ≤ ε ≤ 1, Γ + ε > 0, ρ_z = d_z/2 (so ρ_z ≤ 1 and |Z| = M), H_ρ = Σ_z
ρ_z⁻², ρ_min = min_z ρ_z and L = log(128M/(δ ρ_min²)). The restarted procedure is almost surely
terminating and (ε, δ)-correct, with E_μ[τ_rest] ≤ 1600 H_ρ L. This counts observations.

Lean: `certified_restart_product` (`JointRootCert/Completions2.lean`). On an explicit product
space of independent episode tapes (`restartMeasure`); each episode is a function of its own tape,
capped at 2^j observations. The companion exhibits a concrete, measurable optimistic-separation
episode on the Hoeffding box satisfying every hypothesis. -/
theorem thm_active_restart
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {A : Type u_2}
    (law : Z → MeasureTheory.Measure ℝ)
    [∀ (z : Z), MeasureTheory.IsProbabilityMeasure (law z)]
    {m : Z → ℝ}
    (hsupp : ∀ (z : Z), ∀ᵐ (x : ℝ) ∂law z, x ∈ Set.Icc 0 1)
    (hmean : ∀ (z : Z), ∫ (x : ℝ), x ∂law z = m z)
    {M : ℝ}
    {δ : ℝ}
    (hM : 2 ≤ M)
    (hcard : (↑(Fintype.card Z) : ℝ) ≤ M)
    (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hpr : ∀ (a : A), (supp a)ᶜ.Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    {ε : ℝ}
    {Γ : ℝ}
    (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1)
    (hΓ : IsGreatest (Set.range fun a => val (supp a) (hne a) m - (supp a)ᶜ.sup' (hpr a) m) Γ)
    (hpos : 0 < Γ + ε)
    (selE : ℕ → (Z × ℕ → ℝ) → ℕ → Z)
    (σE : ℕ → (Z × ℕ → ℝ) → ℕ)
    (obsE : ℕ → (Z × ℕ → ℝ) → ℕ)
    (recE : ℕ → (Z × ℕ → ℝ) → A)
    (failE : ℕ → Set (Z × ℕ → ℝ))
    (hfailm : ∀ (j : ℕ), MeasurableSet (failE j))
    (hobs : ∀ (j : ℕ) (x : Z × ℕ → ℝ), obsE j x ≤ 2 ^ j)
    (hrule : ∀ (j : ℕ),
  1 ≤ j →
    ∀ (x : Z × ℕ → ℝ),
      tapeCovered M (δ / ((↑j : ℝ) * ((↑j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) m →
        ∀ t < σE j x,
          OSStep supp hne hpr (tapeLo M (δ / ((↑j : ℝ) * ((↑j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) t)
            (tapeHi M (δ / ((↑j : ℝ) * ((↑j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) t) ε (selE j x t))
    (hret : ∀ (j : ℕ),
  1 ≤ j →
    ∀ (x : Z × ℕ → ℝ),
      tapeCovered M (δ / ((↑j : ℝ) * ((↑j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) m → σE j x ≤ 2 ^ j → x ∉ failE j)
    (hsucc : ∀ (j : ℕ),
  1 ≤ j →
    ∀ x ∉ failE j,
      rectCert (supp (recE j x)) (hne (recE j x)) (hpr (recE j x))
          (tapeLo M (δ / ((↑j : ℝ) * ((↑j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) (σE j x))
          (tapeHi M (δ / ((↑j : ℝ) * ((↑j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) (σE j x)) ≤
        ε) :
      ∫⁻ (ω : ℕ → Z × ℕ → ℝ), restartTime failE obsE ω ∂restartMeasure law <
          ENNReal.ofReal
            ((1600 * ∑ z, 1 / (max (Γ + ε) (gmax m - m z) / 2) ^ 2) *
              Real.log
                (128 * M / (δ * (Finset.univ.inf' Finset.univ_nonempty fun z => max (Γ + ε) (gmax m - m z) / 2) ^ 2))) ∧
        (∀ᵐ (ω : ℕ → Z × ℕ → ℝ) ∂restartMeasure law, restartTime failE obsE ω < ⊤) ∧
          (restartMeasure law : Set (ℕ → Z × ℕ → ℝ) → ENNReal) (⋂ j, ⋂ i ∈ Finset.Ico 1 j, {ω | ω i ∈ failE i}) = 0 ∧
            (restartMeasure law : Set (ℕ → Z × ℕ → ℝ) → ENNReal)
                {ω |
                  ε <
                    regret (supp (recE (restartOut failE ω) (ω (restartOut failE ω))))
                      (hne (recE (restartOut failE ω) (ω (restartOut failE ω)))) m} ≤
              ENNReal.ofReal δ :=
  @certified_restart_product Z _ _ _ A law _ m hsupp hmean M δ hM hcard hδ0 hδ supp hne hpr hcov ε Γ hε0 hε1 hΓ hpos selE σE obsE recE failE hfailm hobs hrule hret hsucc

/-- Companion to Theorem B.6 `thm:active-restart`: a concrete episode satisfying every hypothesis of
the main theorem. Lean: `LiteralF6.active_restart_instance` (`JointRootCert/LiteralF6.lean`). -/
theorem thm_active_restart_instance
    {Z : Type u_1}
    [Fintype Z]
    [LinearOrder Z]
    [Nonempty Z]
    {A : Type u_2}
    [Fintype A]
    [LinearOrder A]
    [Nonempty A]
    (law : Z → MeasureTheory.Measure ℝ)
    [∀ (z : Z), MeasureTheory.IsProbabilityMeasure (law z)]
    {m : Z → ℝ}
    (hsupp : ∀ (z : Z), ∀ᵐ (x : ℝ) ∂law z, x ∈ Set.Icc 0 1)
    (hmean : ∀ (z : Z), ∫ (x : ℝ), x ∂law z = m z)
    {M : ℝ}
    {δ : ℝ}
    (hM : 2 ≤ M)
    (hcard : (↑(Fintype.card Z) : ℝ) ≤ M)
    (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hpr : ∀ (a : A), (supp a)ᶜ.Nonempty)
    (hcov : ∀ (z : Z), ∃ a, z ∈ supp a)
    {ε : ℝ}
    {Γ : ℝ}
    (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1)
    (hΓ : IsGreatest (Set.range fun a => val (supp a) (hne a) m - (supp a)ᶜ.sup' (hpr a) m) Γ)
    (hpos : 0 < Γ + ε) :
      ∫⁻ (ω : ℕ → Z × ℕ → ℝ),
            restartTime (LiteralF6.epFail supp hne hpr M δ ε) (LiteralF6.epObs supp hne hpr M δ ε) ω ∂restartMeasure law <
          ENNReal.ofReal
            ((1600 * ∑ z, 1 / (max (Γ + ε) (gmax m - m z) / 2) ^ 2) *
              Real.log
                (128 * M / (δ * (Finset.univ.inf' Finset.univ_nonempty fun z => max (Γ + ε) (gmax m - m z) / 2) ^ 2))) ∧
        (∀ᵐ (ω : ℕ → Z × ℕ → ℝ) ∂restartMeasure law,
            restartTime (LiteralF6.epFail supp hne hpr M δ ε) (LiteralF6.epObs supp hne hpr M δ ε) ω < ⊤) ∧
          (restartMeasure law : Set (ℕ → Z × ℕ → ℝ) → ENNReal)
                (⋂ j, ⋂ i ∈ Finset.Ico 1 j, {ω | ω i ∈ LiteralF6.epFail supp hne hpr M δ ε i}) =
              0 ∧
            (restartMeasure law : Set (ℕ → Z × ℕ → ℝ) → ENNReal)
                {ω |
                  ε <
                    regret
                      (supp
                        (LiteralF6.epRec supp hne hpr M δ ε (restartOut (LiteralF6.epFail supp hne hpr M δ ε) ω)
                          (ω (restartOut (LiteralF6.epFail supp hne hpr M δ ε) ω))))
                      (hne
                        (LiteralF6.epRec supp hne hpr M δ ε (restartOut (LiteralF6.epFail supp hne hpr M δ ε) ω)
                          (ω (restartOut (LiteralF6.epFail supp hne hpr M δ ε) ω))))
                      m} ≤
              ENNReal.ofReal δ :=
  @LiteralF6.active_restart_instance Z _ _ _ A _ _ _ law _ m hsupp hmean M δ hM hcard hδ0 hδ supp hne hpr hcov ε Γ hε0 hε1 hΓ hpos

/-! ### `lem:bay-cs`: Lemma C.1 (Full-domain confidence sequence) -/

/-- **Lemma C.1** `lem:bay-cs`: Full-domain confidence sequence.

Manuscript: For every fixed θ ∈ ℝ^d, P_θ(θ ∈ C_t(δ) for all invertible G_t) ≥ 1 − δ. Moreover, if
ℓ = max_x ‖u_x‖₂, then 0 ≤ A_t ≤ (γ/2)‖θ̂_t‖₂² and H_t(δ) ≤ log(1/δ) + (d/2) log(1 + tℓ²/(dγ)) +
(γ/2)‖θ̂_t‖₂².

Lean: `LiteralABC2.bay_cs_literal` (`JointRootCert/LiteralABC2.lean`). Conditional
standard-Gaussian innovations given the past. -/
theorem lem_bay_cs
    {n : Type u_1}
    [Fintype n]
    [DecidableEq n]
    {Ω : Type u_2}
    {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ m0)
    {δ : ℝ}
    {γ : ℝ}
    (hδ : 0 < δ)
    (hγ : 0 < γ)
    {u : ℕ → Ω → n → ℝ}
    {ν : ℕ → Ω → ℝ}
    (θ : n → ℝ)
    (hu : ∀ (s : ℕ), @Measurable _ _ (ℱ s) _ (u s))
    (hν : ∀ (s : ℕ), @Measurable _ _ (ℱ (s + 1)) _ (ν s))
    (hgauss : ∀ (s : ℕ), LiteralABC2.CondStdGaussian μ ((↑ℱ : ℕ → MeasurableSpace Ω) s) (ν s)) :
      (μ : Set Ω → ENNReal)
          {ω |
            ∃ t,
              IsUnit (gram (fun s => u s ω) t) ∧
                mixThreshold δ γ (gram (fun s => u s ω) t) (bayB u ν θ t ω) <
                  1 / 2 *
                    (θ - (gram (fun s => u s ω) t)⁻¹.mulVec (bayB u ν θ t ω)) ⬝ᵥ
                      (gram (fun s => u s ω) t).mulVec (θ - (gram (fun s => u s ω) t)⁻¹.mulVec (bayB u ν θ t ω))} ≤
        ENNReal.ofReal δ :=
  @LiteralABC2.bay_cs_literal n _ _ Ω m0 μ _ ℱ δ γ hδ hγ u ν θ hu hν hgauss

/-! ### `lem:nested-interval-valid`: Lemma C.2 (Anytime validity and nesting of terminal boxes) -/

/-- **Lemma C.2** `lem:nested-interval-valid`: Anytime validity and nesting of terminal boxes.

Manuscript: Under either the stated Hoeffding schedule or the predictable Empirical Bernstein
confidence sequence, the simultaneous coverage event {∀ t ≥ 0, μ ∈ B_t} holds with probability at
least 1 − δ. Moreover, on every nonfailed history the endpoints satisfy l_{t+1}(z) ≥ l_t(z) and
u_{t+1}(z) ≤ u_t(z) for all z.

Lean: `LiteralABC3.eb_box_coverage_ae` (`JointRootCert/LiteralABC3.lean`). Main theorem:
empirical-Bernstein coverage of running-intersection boxes at path-dependent counts (`M ≥ |Z|`,
needs `δ < 2M`). Companions: empirical-Bernstein nesting, Hoeffding coverage, Hoeffding nesting. -/
theorem lem_nested_interval_valid
    {Ω : Type u_1}
    {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω}
    {Z : Type u_2}
    [Fintype Z]
    [Nonempty Z]
    [MeasureTheory.IsProbabilityMeasure μ]
    {δ : ℝ}
    {M : ℝ}
    (hδ : 0 < δ)
    (hM : (↑(Fintype.card Z) : ℝ) ≤ M)
    (hδM : δ < 2 * M)
    (X : Z → ℕ → Ω → ℝ)
    (m : Z → ℝ)
    (hmeas : ∀ (z : Z) (i : ℕ), AEMeasurable (X z i) μ)
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) μ)
    (hbdd : ∀ (z : Z) (i : ℕ), ∀ᵐ (ω : Ω) ∂μ, X z i ω ∈ Set.Icc 0 1)
    (hmean : ∀ (z : Z) (i : ℕ), ∫ (ω : Ω), X z i ω ∂μ = m z)
    (N : ℕ → Ω → Z → ℕ) :
      (μ : Set Ω → ENNReal)
          {ω |
            ∃ t z,
              m z ∉
                Set.Icc (runLo (LiteralABC.ebLo (Real.log (2 * M / δ)) (X z) ω) (N t ω z))
                  (runHi (LiteralABC.ebHi (Real.log (2 * M / δ)) (X z) ω) (N t ω z))} ≤
        ENNReal.ofReal δ :=
  @LiteralABC3.eb_box_coverage_ae Ω m0 μ Z _ _ _ δ M hδ hM hδM X m hmeas hindep hbdd hmean N

/-- Companion to Lemma C.2 `lem:nested-interval-valid`: nesting of the empirical-Bernstein boxes.
Lean: `LiteralABC.eb_box_nested` (`JointRootCert/LiteralABC.lean`). -/
theorem lem_nested_interval_valid_nested
    {Ω : Type u_1}
    {Z : Type u_2}
    (L : ℝ)
    (X : Z → ℕ → Ω → ℝ)
    (ω : Ω)
    (N : ℕ → Z → ℕ)
    (hN : ∀ (t : ℕ) (z : Z), N t z ≤ N (t + 1) z)
    (t : ℕ)
    (z : Z) :
      runLo (LiteralABC.ebLo L (X z) ω) (N t z) ≤ runLo (LiteralABC.ebLo L (X z) ω) (N (t + 1) z) ∧
        runHi (LiteralABC.ebHi L (X z) ω) (N (t + 1) z) ≤ runHi (LiteralABC.ebHi L (X z) ω) (N t z) :=
  @LiteralABC.eb_box_nested Ω Z L X ω N hN t z

/-- Companion to Lemma C.2 `lem:nested-interval-valid`: coverage under the Hoeffding schedule. Lean:
`hoeffding_box_coverage` (`JointRootCert/Coverage.lean`). -/
theorem lem_nested_interval_valid_hoeffding
    {Ω : Type u_1}
    {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω}
    {Z : Type u_2}
    [Fintype Z]
    [MeasureTheory.IsProbabilityMeasure μ]
    {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) μ)
    (hmeas : ∀ (z : Z) (i : ℕ), AEMeasurable (X z i) μ)
    (hbdd : ∀ (z : Z) (i : ℕ), ∀ᵐ (ω : Ω) ∂μ, X z i ω ∈ Set.Icc 0 1)
    {m : Z → ℝ}
    (hmean : ∀ (z : Z) (i : ℕ), ∫ (ω : Ω), X z i ω ∂μ = m z)
    {M : ℝ}
    {δ : ℝ}
    (hM : 1 ≤ M)
    (hcard : (↑(Fintype.card Z) : ℝ) ≤ M)
    (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1)
    (N : ℕ → Ω → Z → ℕ) :
      (μ : Set Ω → ENNReal)
          {ω |
            ∃ t z,
              m z ∉
                Set.Icc (runLo (hoeffLo M δ fun i => X z i ω) (N t ω z)) (runHi (hoeffHi M δ fun i => X z i ω) (N t ω z))} ≤
        ENNReal.ofReal δ :=
  @hoeffding_box_coverage Ω m0 μ Z _ _ X hindep hmeas hbdd m hmean M δ hM hcard hδ0 hδ1 N

/-- Companion to Lemma C.2 `lem:nested-interval-valid`: nesting of the Hoeffding boxes. Lean:
`box_nested` (`JointRootCert/Coverage.lean`). -/
theorem lem_nested_interval_valid_hoeffding_nested
    {Z : Type u_1}
    (lo : Z → ℕ → ℝ)
    (hi : Z → ℕ → ℝ)
    (N : ℕ → Z → ℕ)
    (hN : ∀ (t : ℕ) (z : Z), N t z ≤ N (t + 1) z)
    (t : ℕ)
    (z : Z) :
      runLo (lo z) (N t z) ≤ runLo (lo z) (N (t + 1) z) ∧ runHi (hi z) (N (t + 1) z) ≤ runHi (hi z) (N t z) :=
  @box_nested Z lo hi N hN t z

/-! ### `thm:t3-misspec`: Proposition C.3 (Valid misspecification-aware ellipsoid and safe intersection) -/

/-- **Proposition C.3** `thm:t3-misspec`: Valid misspecification-aware ellipsoid and safe intersection.

Manuscript: Suppose Y_s = m_0 + φ_{x_s}ᵀ θ* + b_{x_s} + η_s, ‖θ*‖ ≤ B_θ, ‖b‖_∞ ≤ ξ, and η_s is
conditionally σ-sub-Gaussian. Use predictable inclusion indicators α_s ∈ {0,1}, with at most
N_max(ξ) = ⌈σ²/ξ²⌉ included queries per terminal if ξ > 0. Set T_eff = Σ_s α_s and V_t = λI + Σ_s
α_s φ_{x_s} φ_{x_s}ᵀ. The RLS estimator based on included queries admits the time-uniform radius
β_t = √λ B_θ + σ √(2 log(1/δ) + log(det V_t/λ^d)) + ξ √T_eff. Intersecting this model-based
plausible value set with a separately valid bounded terminal confidence box, using a δ/2 error
split, preserves overall δ validity.

Lean: `LiteralABC2.t3_misspec_radius` (`JointRootCert/LiteralABC2.lean`). The regression is
centred at the known intercept `m₀`. Main theorem: the radius; companions: the per-terminal cap,
the safe intersection with any terminal box valid at δ/2, and exactness of the `+2ξ` correction of
the certificate. -/
theorem thm_t3_misspec
    {n : Type u_1}
    [Fintype n]
    [DecidableEq n]
    {Ω : Type u_2}
    {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω}
    {X : Type u_3}
    [Fintype X]
    [MeasureTheory.IsProbabilityMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ m0)
    {σ : ℝ}
    {lam : ℝ}
    {δ : ℝ}
    {ξ : ℝ}
    {B : ℝ}
    (hσ : 0 < σ)
    (hlam : 0 < lam)
    (hδ : 0 < δ)
    (hB : 0 ≤ B)
    (hξ : 0 ≤ ξ)
    (φ : X → n → ℝ)
    (b : X → ℝ)
    (mu0 : ℝ)
    (θs : n → ℝ)
    (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hb : ∀ (z : X), |b z| ≤ ξ)
    (x : ℕ → Ω → X)
    (hx : ∀ (s : ℕ) (x0 : X), @MeasurableSet _ (ℱ s) {ω | x s ω = x0})
    {α : ℕ → Ω → ℝ}
    (hα01 : ∀ (s : ℕ) (ω : Ω), α s ω = 0 ∨ α s ω = 1)
    (hα : ∀ (s : ℕ), @Measurable _ _ (ℱ s) _ (α s))
    {η : ℕ → Ω → ℝ}
    (hη : ∀ (s : ℕ), @Measurable _ _ (ℱ (s + 1)) _ (η s))
    (hsub : ∀ (s : ℕ), CondSubG μ ((↑ℱ : ℕ → MeasurableSpace Ω) s) (η s) σ)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ (s : ℕ) (ω : Ω), Y s ω = mu0 + φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω) :
      (μ : Set Ω → ENNReal)
          {ω |
            ∃ t,
              LiteralABC2.misRadius σ lam δ B ξ (LiteralABC2.inclDesign lam α (fun s ω => φ (x s ω)) t ω)
                  (LiteralABC2.effCount α t ω) <
                √((LiteralABC2.inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs) ⬝ᵥ
                    (LiteralABC2.inclDesign lam α (fun s ω => φ (x s ω)) t ω).mulVec
                      (LiteralABC2.inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs))} ≤
        ENNReal.ofReal δ :=
  @LiteralABC2.t3_misspec_radius n _ _ Ω m0 μ X _ _ ℱ σ lam δ ξ B hσ hlam hδ hB hξ φ b mu0 θs hθ hb x hx α hα01 hα η hη hsub Y hY

/-- Companion to Proposition C.3 `thm:t3-misspec`: the radius under the per-terminal inclusion cap.
Lean: `LiteralABC2.t3_misspec_radius_capped` (`JointRootCert/LiteralABC2.lean`). -/
theorem thm_t3_misspec_capped
    {n : Type u_1}
    [Fintype n]
    [DecidableEq n]
    {Ω : Type u_2}
    {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω}
    {X : Type u_3}
    [Fintype X]
    [DecidableEq X]
    [MeasureTheory.IsProbabilityMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ m0)
    {σ : ℝ}
    {lam : ℝ}
    {δ : ℝ}
    {ξ : ℝ}
    {B : ℝ}
    (hσ : 0 < σ)
    (hlam : 0 < lam)
    (hδ : 0 < δ)
    (hB : 0 ≤ B)
    (hξ : 0 < ξ)
    (φ : X → n → ℝ)
    (b : X → ℝ)
    (mu0 : ℝ)
    (θs : n → ℝ)
    (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hb : ∀ (z : X), |b z| ≤ ξ)
    (x : ℕ → Ω → X)
    (hx : ∀ (s : ℕ) (x0 : X), @MeasurableSet _ (ℱ s) {ω | x s ω = x0})
    {α : ℕ → Ω → ℝ}
    (hα01 : ∀ (s : ℕ) (ω : Ω), α s ω = 0 ∨ α s ω = 1)
    (hα : ∀ (s : ℕ), @Measurable _ _ (ℱ s) _ (α s))
    (hcap : ∀ (ω : Ω) (t : ℕ) (z : X), (∑ s ∈ Finset.range t, if x s ω = z then α s ω else 0) ≤ (↑⌈σ ^ 2 / ξ ^ 2⌉₊ : ℝ))
    {η : ℕ → Ω → ℝ}
    (hη : ∀ (s : ℕ), @Measurable _ _ (ℱ (s + 1)) _ (η s))
    (hsub : ∀ (s : ℕ), CondSubG μ ((↑ℱ : ℕ → MeasurableSpace Ω) s) (η s) σ)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ (s : ℕ) (ω : Ω), Y s ω = mu0 + φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω) :
      (μ : Set Ω → ENNReal)
          {ω |
            ∃ t,
              √lam * B +
                    σ *
                      √(2 * Real.log (1 / δ) +
                          Real.log ((LiteralABC2.inclDesign lam α (fun s ω => φ (x s ω)) t ω).det / lam ^ Fintype.card n)) +
                  √((↑(Fintype.card X) : ℝ) * (σ ^ 2 + ξ ^ 2)) <
                √((LiteralABC2.inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs) ⬝ᵥ
                    (LiteralABC2.inclDesign lam α (fun s ω => φ (x s ω)) t ω).mulVec
                      (LiteralABC2.inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs))} ≤
        ENNReal.ofReal δ :=
  @LiteralABC2.t3_misspec_radius_capped n _ _ Ω m0 μ X _ _ _ ℱ σ lam δ ξ B hσ hlam hδ hB hξ φ b mu0 θs hθ hb x hx α hα01 hα hcap η hη hsub Y hY

/-- Companion to Proposition C.3 `thm:t3-misspec`: safe intersection with a terminal box valid at δ/2.
Lean: `LiteralABC3.t3_safe_intersection_box` (`JointRootCert/LiteralABC3.lean`). -/
theorem thm_t3_misspec_intersection
    {n : Type u_1}
    [Fintype n]
    [DecidableEq n]
    {Ω : Type u_2}
    {X : Type u_3}
    [Fintype X]
    {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ m0)
    {σ : ℝ}
    {lam : ℝ}
    {δ : ℝ}
    {ξ : ℝ}
    {B : ℝ}
    (hσ : 0 < σ)
    (hlam : 0 < lam)
    (hδ0 : 0 < δ)
    (hB : 0 ≤ B)
    (hξ : 0 ≤ ξ)
    (φ : X → n → ℝ)
    (b : X → ℝ)
    (mu0 : ℝ)
    (θs : n → ℝ)
    (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hb : ∀ (z : X), |b z| ≤ ξ)
    (x : ℕ → Ω → X)
    (hx : ∀ (s : ℕ) (x0 : X), @MeasurableSet _ (ℱ s) {ω | x s ω = x0})
    {α : ℕ → Ω → ℝ}
    (hα01 : ∀ (s : ℕ) (ω : Ω), α s ω = 0 ∨ α s ω = 1)
    (hα : ∀ (s : ℕ), @Measurable _ _ (ℱ s) _ (α s))
    {η : ℕ → Ω → ℝ}
    (hη : ∀ (s : ℕ), @Measurable _ _ (ℱ (s + 1)) _ (η s))
    (hsub : ∀ (s : ℕ), CondSubG μ ((↑ℱ : ℕ → MeasurableSpace Ω) s) (η s) σ)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ (s : ℕ) (ω : Ω), Y s ω = mu0 + φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω)
    (lo : ℕ → Ω → X → ℝ)
    (hi : ℕ → Ω → X → ℝ)
    (hbox : (μ : Set Ω → ENNReal) {ω | ∃ t, (fun z => mu0 + φ z ⬝ᵥ θs + b z) ∉ Set.Icc (lo t ω) (hi t ω)} ≤ ENNReal.ofReal (δ / 2)) :
      (μ : Set Ω → ENNReal)
          {ω |
            ∃ t,
              (fun z => mu0 + φ z ⬝ᵥ θs + b z) ∉
                LiteralABC2.plausibleValues mu0 ξ φ
                    (LiteralABC2.inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω)
                    (LiteralABC2.inclDesign lam α (fun s ω => φ (x s ω)) t ω)
                    (LiteralABC2.misRadius σ lam (δ / 2) B ξ (LiteralABC2.inclDesign lam α (fun s ω => φ (x s ω)) t ω)
                      (LiteralABC2.effCount α t ω)) ∩
                  Set.Icc (lo t ω) (hi t ω)} ≤
        ENNReal.ofReal δ :=
  @LiteralABC3.t3_safe_intersection_box n _ _ Ω X _ m0 μ _ ℱ σ lam δ ξ B hσ hlam hδ0 hB hξ φ b mu0 θs hθ hb x hx α hα01 hα η hη hsub Y hY lo hi hbox

/-- Companion to Proposition C.3 `thm:t3-misspec`: the misspecification-corrected certificate is
exact. Lean: `misspec_certificate_isGreatest` (`JointRootCert/Coverage.lean`). -/
theorem thm_t3_misspec_certificate
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {S : Finset Z}
    {hS : S.Nonempty}
    {ξ : ℝ}
    (hSc : Sᶜ.Nonempty)
    (hξ : 0 ≤ ξ)
    (C : Set (Z → ℝ))
    {D : ℝ}
    (hD : ∀ f ∈ C, ∀ z ∉ S, f z - val S hS f ≤ D)
    (hatt : ∃ f ∈ C, ∃ z ∉ S, f z - val S hS f = D) :
      IsGreatest {r | ∃ f ∈ C, ∃ b, (∀ (x : Z), |b x| ≤ ξ) ∧ r = regret S hS (f + b)} (max 0 (D + 2 * ξ)) :=
  @misspec_certificate_isGreatest Z _ _ _ S hS ξ hSc hξ C D hD hatt

/-! ### `thm:ast-main`: Theorem D.1 (One inside witness and Bernoulli information limit) -/

/-- **Theorem D.1** `thm:ast-main`: One inside witness and Bernoulli information limit.

Manuscript: For proper supports and j ∈ argmax_{y ∈ S(a)} μ_y, with d↓(p,c) = kl(p,c) if p > c and
zero otherwise, C_a^ε = max_{s, t_z ≥ 0, s + Σ t_z = 1} min_{z ∈ B_a} inf_{ε<q<1} {s d↓(μ_j, q −
ε) + t_z kl(μ_z, q)}. For fixed rational ε ∈ [0,1) with C_*^ε > 0, every uniformly correct
procedure obeys liminf_{δ↓0} E τ_δ / log(1/δ) ≥ (C_*^ε)⁻¹, and a likelihood-certified tracker
attains equality, including with multiple correct answers.

Lean: `Rand.ast_main_full` (`JointRootCert/Randomised.lean`). Randomised procedures (one seed
drawn independently of the observations) for the lower bound; the attaining procedure is explicit
and parameter-free. The oracle's rational arithmetic and numerical enclosures are not formalized
(any oracle meeting the contract works). Main theorem: 0 < ε < 1; companion: ε = 0. -/
theorem thm_ast_main
    {Z : Type u_2}
    [Fintype Z]
    [DecidableEq Z]
    {A : Type u_3}
    [Fintype A]
    [Nonempty A]
    [Nonempty Z]
    (SupA : A → Finset Z)
    (hS : ∀ (a : A), Finset.Nonempty (SupA a))
    (hSc : ∀ (a : A), Finset.Nonempty (SupA a)ᶜ)
    (hcov : ∀ (z : Z), ∃ (a : A), z ∈ SupA a)
    {ε : ℝ}
    (hε0 : (0 : ℝ) < ε)
    (hε1 : ε < (1 : ℝ)) :
      (∀ (Sd' : Type u) [inst : MeasurableSpace Sd'] (ν : ℝ → MeasureTheory.Measure Sd')
          [∀ (δ : ℝ), MeasureTheory.IsProbabilityMeasure (ν δ)] (R : ℝ → Rand.RSampler Z Sd') (dec : ℝ → Sd' → List Bool → A),
          (∀ (δ : ℝ) (l : List Bool) (a : A), MeasurableSet {s : Sd' | dec δ s l = a}) →
            (∀ (δ : ℝ),
                (0 : ℝ) < δ →
                  δ < (1 : ℝ) →
                    ∀ (lam : Z → ℝ),
                      (∀ (z : Z), (0 : ℝ) < lam z ∧ lam z < (1 : ℝ)) →
                        (1 : ℝ) - δ ≤
                          Rand.rprobInf (ν δ) (R δ) lam fun (s : Sd') => {l : List Bool | lam ∉ Alt (SupA (dec δ s l)) ε}) →
              ∀ (μ : Z → ℝ),
                (∀ (z : Z), (0 : ℝ) < μ z ∧ μ z < (1 : ℝ)) →
                  (∀ c₀ < (1 : ℝ) / Stopped.charStar SupA ε μ,
                      ∀ᶠ (δ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
                        ∃ (n : ℕ), c₀ * Real.log ((1 : ℝ) / δ) ≤ Rand.rexpTime (ν δ) (R δ) μ n) ∧
                    ((∀ (δ : ℝ), ∃ (B : ℝ), ∀ (n : ℕ), Rand.rexpTime (ν δ) (R δ) μ n ≤ B) →
                      (↑((1 : ℝ) / Stopped.charStar SupA ε μ) : EReal) ≤
                        Filter.liminf (fun (δ : ℝ) => (↑(Rand.rexpTimeInf (ν δ) (R δ) μ / Real.log ((1 : ℝ) / δ)) : EReal))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))))) ∧
        ∃ (S : ℝ → Stopped.Sampler Z) (dec : ℝ → List Bool → A),
          (∀ (δ : ℝ),
              (0 : ℝ) < δ →
                ∀ (lam : Z → ℝ),
                  (∀ (i : Z), (0 : ℝ) < lam i ∧ lam i < (1 : ℝ)) →
                    (Rand.rprobInf (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) lam fun (x : Unit) =>
                          {l : List Bool | lam ∈ Alt (SupA (dec δ l)) ε}) ≤
                        δ ∧
                      (1 : ℝ) - δ ≤
                        Rand.rprobInf (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) lam fun (x : Unit) =>
                          {l : List Bool | lam ∉ Alt (SupA (dec δ l)) ε}) ∧
            ∀ (μ : Z → ℝ),
              (∀ (i : Z), (0 : ℝ) < μ i ∧ μ i < (1 : ℝ)) →
                (∀ (δ : ℝ),
                    ∃ (Bd : ℝ),
                      ∀ (n : ℕ), Rand.rexpTime (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) μ n ≤ Bd) ∧
                  Filter.Tendsto
                    (fun (δ : ℝ) =>
                      Rand.rexpTimeInf (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) μ /
                        Real.log ((1 : ℝ) / δ))
                    (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds ((1 : ℝ) / Stopped.charStar SupA ε μ)) :=
  @Rand.ast_main_full Z _ _ A _ _ _ SupA hS hSc hcov ε hε0 hε1

/-- Companion to Theorem D.1 `thm:ast-main`: the case ε = 0. Lean: `Rand.ast_main_exact_full`
(`JointRootCert/Randomised.lean`). -/
theorem thm_ast_main_exact
    {Z : Type u_2}
    [Fintype Z]
    [DecidableEq Z]
    {A : Type u_3}
    [Fintype A]
    [Nonempty A]
    [Nonempty Z]
    (SupA : A → Finset Z)
    (hS : ∀ (a : A), Finset.Nonempty (SupA a))
    (hSc : ∀ (a : A), Finset.Nonempty (SupA a)ᶜ)
    (hcov : ∀ (z : Z), ∃ (a : A), z ∈ SupA a) :
      (∀ (Sd' : Type u) [inst : MeasurableSpace Sd'] (ν : ℝ → MeasureTheory.Measure Sd')
          [∀ (δ : ℝ), MeasureTheory.IsProbabilityMeasure (ν δ)] (R : ℝ → Rand.RSampler Z Sd') (dec : ℝ → Sd' → List Bool → A),
          (∀ (δ : ℝ) (l : List Bool) (a : A), MeasurableSet {s : Sd' | dec δ s l = a}) →
            (∀ (δ : ℝ),
                (0 : ℝ) < δ →
                  δ < (1 : ℝ) →
                    ∀ lam ∈ Stopped.exactDomain SupA,
                      (∀ (z : Z), (0 : ℝ) < lam z ∧ lam z < (1 : ℝ)) →
                        (1 : ℝ) - δ ≤
                          Rand.rprobInf (ν δ) (R δ) lam fun (s : Sd') =>
                            {l : List Bool | lam ∉ Alt (SupA (dec δ s l)) (0 : ℝ)}) →
              ∀ μ ∈ Stopped.exactDomain SupA,
                (∀ (z : Z), (0 : ℝ) < μ z ∧ μ z < (1 : ℝ)) →
                  (∀ c₀ < (1 : ℝ) / Stopped.charStar SupA (0 : ℝ) μ,
                      ∀ᶠ (δ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
                        ∃ (n : ℕ), c₀ * Real.log ((1 : ℝ) / δ) ≤ Rand.rexpTime (ν δ) (R δ) μ n) ∧
                    ((∀ (δ : ℝ), ∃ (B : ℝ), ∀ (n : ℕ), Rand.rexpTime (ν δ) (R δ) μ n ≤ B) →
                      (↑((1 : ℝ) / Stopped.charStar SupA (0 : ℝ) μ) : EReal) ≤
                        Filter.liminf (fun (δ : ℝ) => (↑(Rand.rexpTimeInf (ν δ) (R δ) μ / Real.log ((1 : ℝ) / δ)) : EReal))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))))) ∧
        ∃ (S : ℝ → Stopped.Sampler Z) (dec : ℝ → List Bool → A),
          (∀ (δ : ℝ),
              (0 : ℝ) < δ →
                ∀ (lam : Z → ℝ),
                  (∀ (i : Z), (0 : ℝ) < lam i ∧ lam i < (1 : ℝ)) →
                    (Rand.rprobInf (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) lam fun (x : Unit) =>
                        {l : List Bool | lam ∈ Alt (SupA (dec δ l)) (0 : ℝ)}) ≤
                      δ) ∧
            (∀ (δ : ℝ),
                (0 : ℝ) < δ →
                  ∀ lam ∈ Stopped.exactDomain SupA,
                    (∀ (i : Z), (0 : ℝ) < lam i ∧ lam i < (1 : ℝ)) →
                      (1 : ℝ) - δ ≤
                        Rand.rprobInf (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) lam fun (x : Unit) =>
                          {l : List Bool | lam ∉ Alt (SupA (dec δ l)) (0 : ℝ)}) ∧
              ∀ μ ∈ Stopped.exactDomain SupA,
                (∀ (i : Z), (0 : ℝ) < μ i ∧ μ i < (1 : ℝ)) →
                  (∀ (δ : ℝ),
                      ∃ (Bd : ℝ),
                        ∀ (n : ℕ), Rand.rexpTime (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) μ n ≤ Bd) ∧
                    Filter.Tendsto
                      (fun (δ : ℝ) =>
                        Rand.rexpTimeInf (MeasureTheory.Measure.dirac ()) (Rand.RSampler.const (S δ)) μ /
                          Real.log ((1 : ℝ) / δ))
                      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds ((1 : ℝ) / Stopped.charStar SupA (0 : ℝ) μ)) :=
  @Rand.ast_main_exact_full Z _ _ A _ _ _ SupA hS hSc hcov

/-! ### `thm:bay-main-optimal`: Theorem D.2 (Correlated Gaussian information limit) -/

/-- **Theorem D.2** `thm:bay-main-optimal`: Correlated Gaussian information limit.

Manuscript: For a finite correctly specified fixed-feature Gaussian experiment model with a
spanning query dictionary and 0 < I_*(θ) < ∞, every uniformly correct procedure has liminf_{δ↓0}
E_θ τ_δ / log(1/δ) ≥ I_*(θ)⁻¹, with equality attained by an explicitly constructed
likelihood-certified information tracker, including for multiple correct root actions.

Lean: `LiteralF2.bay_main_optimal_full` (`JointRootCert/LiteralF2.lean`). Randomised lower bound
for the paper's I_*(θ), together with the explicitly constructed finite-grid tracker. Grid values
are exact infima rather than computed enclosures. -/
theorem thm_bay_main_optimal
    {X : Type u_1}
    {ι : Type u_2}
    {𝒜 : Type u_3}
    {Z : Type u_4}
    [Fintype X]
    [DecidableEq X]
    [Nonempty X]
    [MeasurableSpace X]
    [MeasurableSingletonClass X]
    [Fintype ι]
    [DecidableEq ι]
    [Nonempty ι]
    [Fintype 𝒜]
    [Nonempty 𝒜]
    [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒜]
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    (u : X → ι → ℝ)
    {v : X → ℝ}
    (hv : ∀ (x : X), (0 : ℝ) < v x)
    {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X)
    {κ : ℝ}
    (hκ : (0 : ℝ) < κ)
    (hspan : ∀ (e : ι → ℝ), κ * e ⬝ᵥ e ≤ ∑ x : X, w0 x * (u x ⬝ᵥ e) ^ (2 : ℕ))
    (φ : Z → EuclideanSpace ℝ ι)
    (supp : 𝒜 → Finset Z)
    (hne : ∀ (a : 𝒜), Finset.Nonempty (supp a))
    (ε : ℝ)
    (hQne : ∀ (a : 𝒜), Set.Nonempty (strictAlt φ (supp a) (hne a) ε)) :
      (∀ (θ : ι → ℝ),
          (0 : ℝ) < LiteralD1b.IstarE u (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) θ →
            ∀ (Sd : Type) [inst : MeasurableSpace Sd] (ν : ℝ → MeasureTheory.Measure Sd)
              [∀ (δ : ℝ), MeasureTheory.IsProbabilityMeasure (ν δ)] (R : ℝ → RandG.RGSampler X Sd)
              (D : ℝ → RandG.RGDecision 𝒜 Sd),
              (∀ (δ : ℝ),
                  (0 : ℝ) < δ →
                    δ < (1 : ℝ) →
                      ∀ (a : 𝒜),
                        ∀ lam ∈ strictAlt φ (supp a) (hne a) ε,
                          ∀ (n : ℕ),
                            RandG.rprobAns (ν δ) (R δ) (D δ) a (fun (x : X) => √(v x) * u x ⬝ᵥ WithLp.ofLp lam) v n ≤ δ) →
                ∀ c < (1 : ℝ) / LiteralD1b.IstarE u (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) θ,
                  ∀ᶠ (δ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
                    ENNReal.ofReal (c * Real.log ((1 : ℝ) / δ)) ≤
                      RandG.rexpTau (ν δ) (R δ) (fun (x : X) => √(v x) * u x ⬝ᵥ θ) v) ∧
        ∃ (ℓ : ℝ) (A0 : ℝ) (hT :
          GaussTrack.Tracker.Meas
            (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ κ A0)),
          GaussTrack.Tracker.Valid
              (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ κ A0) ℓ κ A0 ∧
            (∀ (δ : ℝ),
                (0 : ℝ) < δ →
                  δ < (1 : ℝ) →
                    ∀ (a : 𝒜),
                      ∀ lam ∈ strictAlt φ (supp a) (hne a) ε,
                        ∀ (n : ℕ),
                          (GaussStopped.law
                                  (GaussTrack.Tracker.sampler
                                    (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ)
                                      ℓ κ A0)
                                    hT δ)
                                  (fun (x : X) => √(v x) * u x ⬝ᵥ WithLp.ofLp lam) v n :
                                Set (Fin n → ℝ) → ENNReal)
                              (GaussStopped.ansSet
                                (GaussTrack.Tracker.sampler
                                  (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ
                                    κ A0)
                                  hT δ)
                                (GaussTrack.Tracker.decision
                                  (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ
                                    κ A0)
                                  hT δ)
                                a n) ≤
                            ENNReal.ofReal δ) ∧
              (∀ (δ : ℝ),
                  (0 : ℝ) < δ →
                    δ < (1 : ℝ) →
                      ∀ (lam : EuclideanSpace ℝ ι) (n : ℕ),
                        (GaussStopped.law
                                (GaussTrack.Tracker.sampler
                                  (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ
                                    κ A0)
                                  hT δ)
                                (fun (x : X) => √(v x) * u x ⬝ᵥ WithLp.ofLp lam) v n :
                              Set (Fin n → ℝ) → ENNReal)
                            (⋃ a ∈ {a : 𝒜 | lam ∈ strictAlt φ (supp a) (hne a) ε},
                              GaussStopped.ansSet
                                (GaussTrack.Tracker.sampler
                                  (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ
                                    κ A0)
                                  hT δ)
                                (GaussTrack.Tracker.decision
                                  (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ
                                    κ A0)
                                  hT δ)
                                a n) ≤
                          ENNReal.ofReal δ) ∧
                ∀ (θ : ι → ℝ),
                  (0 : ℝ) < LiteralD1b.IstarE u (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) θ →
                    (∀ (δ : ℝ),
                        (0 : ℝ) < δ →
                          δ < (1 : ℝ) →
                            GaussStopped.expTau
                                (GaussTrack.Tracker.sampler
                                  (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ
                                    κ A0)
                                  hT δ)
                                (fun (x : X) => √(v x) * u x ⬝ᵥ θ) v ≠
                              ⊤) ∧
                      Filter.Tendsto
                        (fun (δ : ℝ) =>
                          ENNReal.toReal
                              (GaussStopped.expTau
                                (GaussTrack.Tracker.sampler
                                  (LiteralD1b.finGridTracker u v (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) w0 (1 : ℝ) ℓ
                                    κ A0)
                                  hT δ)
                                (fun (x : X) => √(v x) * u x ⬝ᵥ θ) v) /
                            Real.log ((1 : ℝ) / δ))
                        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
                        (nhds ((1 : ℝ) / LiteralD1b.IstarE u (fun (a : 𝒜) => strictAlt φ (supp a) (hne a) ε) θ)) :=
  @LiteralF2.bay_main_optimal_full X ι 𝒜 Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u v hv w0 hw0 κ hκ hspan φ supp hne ε hQne

/-! ### `lem:active-com`: Lemma D.3 (Stopped Bernoulli change of measure) -/

/-- **Lemma D.3** `lem:active-com`: Stopped Bernoulli change of measure.

Manuscript: If an adaptive sampler stops almost surely under two interior Bernoulli mean vectors
μ, λ and has finite expected time under μ, then for any event E measurable at stopping, Σ_z
E_μ[N_z(τ)] kl(μ_z, λ_z) ≥ kl(P_μ(E), P_λ(E)).

Lean: `Rand.rstopped_transport` (`JointRootCert/Randomised.lean`). Randomised procedures with one
seed independent of the observations; unbounded-horizon probabilities and expectations are
monotone limits over the horizon. -/
theorem lem_active_com
    {Sd : Type u_1}
    [MeasurableSpace Sd]
    {Z : Type u_2}
    [Fintype Z]
    [DecidableEq Z]
    (ν : MeasureTheory.Measure Sd)
    [MeasureTheory.IsProbabilityMeasure ν]
    (R : Rand.RSampler Z Sd)
    {μ : Z → ℝ}
    {lam : Z → ℝ}
    (hμ : ∀ (z : Z), 0 < μ z ∧ μ z < 1)
    (hlam : ∀ (z : Z), 0 < lam z ∧ lam z < 1)
    {B : ℝ}
    (hB : ∀ (n : ℕ), Rand.rexpTime ν R μ n ≤ B)
    {E : Sd → Set (List Bool)}
    (hE : Rand.SeedEvent E) :
      bkl (Rand.rprobInf ν R μ E) (Rand.rprobInf ν R lam E) ≤ ∑ z, Rand.rexpCountInf ν R μ z * bkl (μ z) (lam z) :=
  @Rand.rstopped_transport Sd _ Z _ _ ν _ R μ lam hμ hlam B hB E hE

/-! ### `thm:active-kl-projection`: Theorem D.4 (Scalar information projection for a fixed root answer) -/

/-- **Theorem D.4** `thm:active-kl-projection`: Scalar information projection for a fixed root answer.

Manuscript: For any nonnegative sampling-weight vector v, inf_{λ ∈ Alt_ε(a)} Σ_z v_z kl(μ_z, λ_z)
= min_{z ∉ S(a)} inf_{ε<θ<1} [v_z kl(μ_z, θ) + Σ_{y ∈ S(a)} v_y d↓(μ_y, θ − ε)]. Each scalar
objective is convex; if its outside weight and the sum of its inside weights are strictly
positive, it has a unique interior minimizer. A terminal shared by many root supports contributes
only once to information cost.

Lean: `info_projection` (`JointRootCert/BernoulliInfo.lean`). For 0 ≤ ε < 1, proper nonempty
support and interior means. Convexity and uniqueness are `scalarObj_convexOn`,
`scalarObj_existsUnique_isMinOn` in `BernoulliInfo.lean`. -/
theorem thm_active_kl_projection
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {S : Finset Z}
    (hS : S.Nonempty)
    (hSc : Sᶜ.Nonempty)
    {ε : ℝ}
    (hε0 : 0 ≤ ε)
    (hε1 : ε < 1)
    {v : Z → ℝ}
    {μ : Z → ℝ}
    (hv : ∀ (i : Z), 0 ≤ v i)
    (hμ : ∀ (i : Z), 0 < μ i ∧ μ i < 1) :
      infoRate S ε v μ = Sᶜ.inf' hSc fun z => sInf (scalarObj S ε v μ z '' Set.Ioo ε 1) :=
  @info_projection Z _ _ _ S hS hSc ε hε0 hε1 v μ hv hμ

/-! ### `thm:active-star-lb`: Theorem D.5 (Non-containment tied-star lower bound) -/

/-- **Theorem D.5** `thm:active-star-lb`: Non-containment tied-star lower bound.

Manuscript: On the Bernoulli star family S_A = {p, q}, S_{B_i} = {p, r_i} (i = 1..N) with μ_p =
μ_q = 1/2 and μ_{r_i} = 1/2 − g (0 < ε ≤ g ≤ 1/4, 0 < δ ≤ 1/4), every (ε, δ)-correct, almost
surely halting algorithm satisfies E_μ[τ] ≥ kl(1/2, δ) min{N / kl(1/2 − g, 1/2 + ε), 1 / kl(1/2,
1/2 + ε)}. (ε, δ)-correct means correct with probability at least 1 − δ at every interior
Bernoulli parameter.

Lean: `Rand.tied_star_lower_bound_rand` (`JointRootCert/Randomised.lean`). Randomised procedures. -/
theorem thm_active_star_lb
    {Sd : Type u_1}
    [MeasurableSpace Sd]
    {N : ℕ}
    {g : ℝ}
    {ε : ℝ}
    {δ : ℝ}
    (hε : 0 < ε)
    (hεg : ε ≤ g)
    (hg : g ≤ 1 / 4)
    (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4)
    (ν : MeasureTheory.Measure Sd)
    [MeasureTheory.IsProbabilityMeasure ν]
    (R : Rand.RSampler (Fan N) Sd)
    (dec : Sd → List Bool → Option (Fin N))
    (hdec : ∀ (l : List Bool) (a : Option (Fin N)), MeasurableSet {s | dec s l = a})
    (hcorr : ∀ (lam : Fan N → ℝ),
  (∀ (i : Fan N), 0 < lam i ∧ lam i < 1) →
    1 - δ ≤
      Rand.rprobInf ν R lam fun s =>
        {l | regret (Stopped.starSupp N (dec s l)) (Stopped.starSupp_nonempty N (dec s l)) lam ≤ ε})
    {B : ℝ}
    (hB : ∀ (n : ℕ), Rand.rexpTime ν R (starMu N g) n ≤ B) :
      bkl (1 / 2) δ * min ((↑N : ℝ) / bkl (1 / 2 - g) (1 / 2 + ε)) (1 / bkl (1 / 2) (1 / 2 + ε)) ≤
        Rand.rexpTimeInf ν R (starMu N g) :=
  @Rand.tied_star_lower_bound_rand Sd _ N g ε δ hε hεg hg hδ0 hδ ν _ R dec hdec hcorr B hB

/-! ### `prop:ast-gap-tradeoff`: Proposition D.6 (A support-margin versus information tradeoff) -/

/-- **Proposition D.6** `prop:ast-gap-tradeoff`: A support-margin versus information tradeoff.

Manuscript: Let 0 < h < g ≤ 1/4 and N ≥ 1, terminals p, s, r_1..r_N, supports S_A = {p, s}, S_B =
{p, r_1, ..., r_N}, means μ_p = 1/2, μ_s = 1/2 − h, μ_{r_i} = 1/2 − g. Both actions are optimal
and neither support contains the other. Action A has the larger exterior margin, but C_A^0(μ) ≤
4g²/N and C_B^0(μ) ≥ h²/2.

Lean: `gap_tradeoff_structure` (`JointRootCert/BernoulliInfo.lean`). Main theorem: the structural
facts; companions: the two information bounds. -/
theorem prop_ast_gap_tradeoff
    {N : ℕ}
    (hN : 0 < N)
    {g : ℝ}
    {h : ℝ}
    (hh : 0 < h)
    (hhg : h < g)
    (hA : (pairSupp N)ᶜ.Nonempty)
    (hB : (fanSupp N)ᶜ.Nonempty) :
      regret (pairSupp N) (pairSupp_nonempty N) (gapMu N g h) = 0 ∧
        regret (fanSupp N) (fanSupp_nonempty N) (gapMu N g h) = 0 ∧
          ¬pairSupp N ⊆ fanSupp N ∧
            ¬fanSupp N ⊆ pairSupp N ∧
              val (pairSupp N) (pairSupp_nonempty N) (gapMu N g h) - (pairSupp N)ᶜ.sup' hA (gapMu N g h) = g ∧
                val (fanSupp N) (fanSupp_nonempty N) (gapMu N g h) - (fanSupp N)ᶜ.sup' hB (gapMu N g h) = h :=
  @gap_tradeoff_structure N hN g h hh hhg hA hB

/-- Companion to Proposition D.6 `prop:ast-gap-tradeoff`: C_A^0(μ) ≤ 4g²/N. Lean: `gap_tradeoff_A`
(`JointRootCert/BernoulliInfo.lean`). -/
theorem prop_ast_gap_tradeoff_A
    {N : ℕ}
    (hN : 0 < N)
    {g : ℝ}
    {h : ℝ}
    (hh : 0 < h)
    (hhg : h < g)
    (hg : g ≤ 1 / 4) :
      charRate (pairSupp N) 0 (gapMu N g h) ≤ 4 * g ^ 2 / (↑N : ℝ) :=
  @gap_tradeoff_A N hN g h hh hhg hg

/-- Companion to Proposition D.6 `prop:ast-gap-tradeoff`: C_B^0(μ) ≥ h²/2. Lean: `gap_tradeoff_B`
(`JointRootCert/BernoulliInfo.lean`). -/
theorem prop_ast_gap_tradeoff_B
    {N : ℕ}
    {g : ℝ}
    {h : ℝ}
    (hh : 0 < h)
    (hhg : h < g)
    (hg : g ≤ 1 / 4) :
      h ^ 2 / 2 ≤ charRate (fanSupp N) 0 (gapMu N g h) :=
  @gap_tradeoff_B N g h hh hhg hg

/-! ### `prop:ast-discovery`: Proposition D.7 (A discovery cost absent from the characteristic time) -/

/-- **Proposition D.7** `prop:ast-discovery`: A discovery cost absent from the characteristic time.

Manuscript: For every N ≥ 1 there is a two-action overlapping support family with M = N + 2
terminals and N + 1 interior Bernoulli instances such that every procedure that is δ-correct and
almost surely terminating on these instances satisfies, for some instance μ^j, E_{μ^j} τ ≥ (N +
1)(1 − 2δ)/2 and C_*^0(μ^j) ≥ g²/2, for a fixed g ∈ (0, 1/8] independent of N.

Lean: `Rand.discovery_cost_rand` (`JointRootCert/Randomised.lean`). Randomised procedures; no
coupling is assumed. -/
theorem prop_ast_discovery
    {Sd : Type u_1}
    [MeasurableSpace Sd]
    {N : ℕ}
    (hN : 0 < N)
    {g : ℝ}
    (hg : 0 < g)
    (hg8 : g ≤ 1 / 8)
    {δ : ℝ}
    (ν : MeasureTheory.Measure Sd)
    [MeasureTheory.IsProbabilityMeasure ν]
    (R : Rand.RSampler (Fan N) Sd)
    (dec : Sd → List Bool → Bool)
    (hdec : ∀ (l : List Bool) (a : Bool), MeasurableSet {s | dec s l = a})
    (hcorr0 : 1 - δ ≤ Rand.rprobInf ν R (discMu N g none) fun s => {l | dec s l = false})
    (hcorr : ∀ (j : Fin N), 1 - δ ≤ Rand.rprobInf ν R (discMu N g (some j)) fun s => {l | dec s l = true})
    {Bd : Fin N → ℝ}
    (hBd : ∀ (j : Fin N) (n : ℕ), Rand.rexpTime ν R (discMu N g (some j)) n ≤ Bd j) :
      ∃ j,
        ((↑N : ℝ) + 1) / 2 * (1 - 2 * δ) ≤ Rand.rexpTimeInf ν R (discMu N g (some j)) ∧
          g ^ 2 / 2 ≤ charRate (fanSupp N) 0 (discMu N g (some j)) ∧
            g ^ 2 / 2 ≤ Stopped.charStar (Rand.discSupp N) 0 (discMu N g (some j)) :=
  @Rand.discovery_cost_rand Sd _ N hN g hg hg8 δ ν _ R dec hdec hcorr0 hcorr Bd hBd

/-! ### `lem:bay-projection`: Lemma D.8 (Screened projection) -/

/-- **Lemma D.8** `lem:bay-projection`: Screened projection.

Manuscript: I_a(θ, w) = min_{z ∈ E_a} min_{λ ∈ P_{a,z}} (1/2)‖λ − θ‖²_{M(w)}. All component minima
exist, including for singular M(w). An empty E_a means I_a = +∞. For z ∈ E_a, with D the matrix of
rows (φ_z − φ_y)ᵀ and b = ε1 − Dθ, the component distance equals the dual maximum over α ≥ 0 with
Dᵀα ∈ range M(w) of αᵀb − (1/2)(Dᵀα)ᵀ M(w)† Dᵀα; if M(w) ≻ 0 it is also (1/2) max_{p ∈ Δ(S(a))} (ε
− g_{z,p}ᵀθ)_+² / (g_{z,p}ᵀ M(w)⁻¹ g_{z,p}).

Lean: `screened_projection` (`JointRootCert/GaussianInfo.lean`). Strong duality by Hahn-Banach, no
rank condition. The ratio form is `projection_ratio`. -/
theorem lem_bay_projection
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : Type u_3}
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    {S : Finset Z}
    {φ : Z → E}
    {ε : ℝ}
    (hS : S.Nonempty)
    (hε : 0 ≤ ε)
    (A : E →ₗ[ℝ] F)
    (θ : E)
    (c : ℝ) :
      (∀ lam ∈ strictAlt φ S hS ε, c ≤ ‖(A : E → F) (lam - θ)‖) ↔
        ∀ z ∈ hullScreen φ S, ∀ lam ∈ closedComp φ S ε z, c ≤ ‖(A : E → F) (lam - θ)‖ :=
  @screened_projection Z _ _ _ E _ _ _ F _ _ S φ ε hS hε A θ c

/-- Companion to Lemma D.8 `lem:bay-projection`: the dual formula for the component distance. Lean:
`screened_projection_dual` (`JointRootCert/GaussianInfo.lean`). -/
theorem lem_bay_projection_dual
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : Type u_3}
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {S : Finset Z}
    {φ : Z → E}
    {ε : ℝ}
    {z : Z}
    (hε : (0 : ℝ) ≤ ε)
    (A : E →ₗ[ℝ] F)
    (θ : E)
    (hz : φ z ∉ (convexHull ℝ : Set E → Set E) (φ '' (↑S : Set Z))) :
      ∃ lam ∈ closedComp φ S ε z,
        (∀ mu ∈ closedComp φ S ε z, ‖(A : E → F) (lam - θ)‖ ≤ ‖(A : E → F) (mu - θ)‖) ∧
          (∀ (α : ↥S → ℝ) (ν : E),
              (∀ (y : ↥S), (0 : ℝ) ≤ α y) →
                ∑ y : ↥S, α y • (φ z - φ (↑y : Z)) =
                    ((LinearMap.adjoint : (E →ₗ[ℝ] F) → F →ₗ[ℝ] E) A : F → E) ((A : E → F) ν) →
                  ∑ y : ↥S, α y * (ε - inner ℝ (φ z - φ (↑y : Z)) θ) - ‖(A : E → F) ν‖ ^ (2 : ℕ) / (2 : ℝ) ≤
                    ‖(A : E → F) (lam - θ)‖ ^ (2 : ℕ) / (2 : ℝ)) ∧
            ∃ (α : ↥S → ℝ) (ν : E),
              (∀ (y : ↥S), (0 : ℝ) ≤ α y) ∧
                ∑ y : ↥S, α y • (φ z - φ (↑y : Z)) =
                    ((LinearMap.adjoint : (E →ₗ[ℝ] F) → F →ₗ[ℝ] E) A : F → E) ((A : E → F) ν) ∧
                  ∑ y : ↥S, α y * (ε - inner ℝ (φ z - φ (↑y : Z)) θ) - ‖(A : E → F) ν‖ ^ (2 : ℕ) / (2 : ℝ) =
                    ‖(A : E → F) (lam - θ)‖ ^ (2 : ℕ) / (2 : ℝ) :=
  @screened_projection_dual Z _ _ _ E _ _ _ F _ _ _ S φ ε z hε A θ hz

/-! ### `lem:bay-distance-certificate`: Lemma D.9 (Distance and certification) -/

/-- **Lemma D.9** `lem:bay-distance-certificate`: Distance and certification.

Manuscript: Let M ≻ 0, suppose r_θ(a) ≤ ε, and let C = {λ : ‖λ − θ‖_M ≤ β}. Then R_C(a) ≤ ε if and
only if β² ≤ 2 inf_{λ : r_λ(a) > ε} (1/2)‖λ − θ‖²_M.

Lean: `distance_certificate` (`JointRootCert/GaussianInfo.lean`). -/
theorem lem_bay_distance_certificate
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : Type u_3}
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    {S : Finset Z}
    {φ : Z → E}
    {ε : ℝ}
    (hS : S.Nonempty)
    (A : E →ₗ[ℝ] F)
    (hA : Function.Injective (⇑A : E → F))
    {θ : E}
    {β : ℝ}
    (hθ : regret S hS (env φ θ) ≤ ε) :
      (∀ (lam : E), ‖(A : E → F) (lam - θ)‖ ≤ β → regret S hS (env φ lam) ≤ ε) ↔
        ∀ lam ∈ strictAlt φ S hS ε, β ≤ ‖(A : E → F) (lam - θ)‖ :=
  @distance_certificate Z _ _ _ E _ _ _ F _ _ S φ ε hS A hA θ β hθ

/-! ### `prop:bay-finite`: Proposition D.10 (Finite-confidence discovery, frozen confirmation, and safeguard) -/

/-- **Proposition D.10** `prop:bay-finite`: Finite-confidence discovery, frozen confirmation, and safeguard.

Manuscript: For the known-noise Gaussian experiment model and any fixed instance with I_*(θ) > 0,
the explicit spanning-pilot, frozen-design, fresh-confirmation and independent-safeguard procedure
is uniformly (ε, δ)-safe. For prescribed s ∈ (0,1], E_θ τ ≤ D(θ, G, ε, s) + (1 + s) I_*(θ)⁻¹
log(1/δ) + R_s(θ, δ), where D is finite and independent of δ, and R_s = O(1 + log log(1/δ)) as δ ↓
0.

Lean: `LiteralD1c.grid_bay_finite` (`JointRootCert/LiteralD1c.lean`). One explicit procedure
`gridProc` with the finite-grid oracle on a constructed product space of Gaussian tapes. -/
theorem prop_bay_finite
    {X : Type u_1}
    [Fintype X]
    [DecidableEq X]
    [Nonempty X]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E]
    [BorelSpace E]
    {𝒜 : Type u_3}
    [Fintype 𝒜]
    [DecidableEq 𝒜]
    [Nonempty 𝒜]
    {Z : Type u_4}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    (φ : Z → E)
    (supp : 𝒜 → Finset Z)
    (hne : ∀ (a : 𝒜), (supp a).Nonempty)
    (ε : ℝ)
    {A0 : ℝ}
    (hA : ∀ (a : 𝒜), ∃ lam ∈ strictAlt φ (supp a) (hne a) ε, ‖lam‖ ≤ A0)
    (u : X → E)
    {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X)
    {ℓ : ℝ}
    {k0 : ℝ}
    {s : ℝ}
    (hℓ : 0 < ℓ)
    (hu : ∀ (x : X), ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0)
    (hM0 : ∀ (v : E), k0 * ‖v‖ ^ 2 ≤ ‖(designMap u w0 : E → EuclideanSpace ℝ X) v‖ ^ 2)
    (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
      (∀ (δ J : ℝ) (e : ℕ → ℝ),
          0 < δ →
            δ ≤ 1 →
              1 ≤ J →
                (∀ (j : ℕ), ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j / √2 ≤ e j) →
                  (∀ (j : ℕ), e j ≤ √2 * ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j) →
                    (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e δ).Spec
                        (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 (1 / (8 * J ^ 2)) δ ∧
                      ∀ (θ : E),
                        (LiteralD1.tapeP X : Set (Fin 3 → X × ℕ → ℝ) → ENNReal)
                            {ω |
                              (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e δ).tauΩ θ
                                    ω <
                                  ⊤ ∧
                                ∃ a,
                                  (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e
                                            δ).retΩ
                                        θ ω =
                                      some a ∧
                                    ε < regret (supp a) (hne a) (env φ θ)} ≤
                          ENNReal.ofReal δ) ∧
        ∀ (θ : E),
          0 < LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
            ∃ K,
              ∀ (δ J : ℝ) (e : ℕ → ℝ),
                0 < δ →
                  δ ≤ 1 / 4 →
                    1 + Real.log (1 / δ) ≤ J →
                      J < 3 + Real.log (1 / δ) →
                        (∀ (j : ℕ), ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j / √2 ≤ e j) →
                          (∀ (j : ℕ), e j ≤ √2 * ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j) →
                            ∫⁻ (ω : Fin 3 → X × ℕ → ℝ),
                                  (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e
                                        δ).tauΩ
                                    θ ω ∂LiteralD1.tapeP X ≤
                                ENNReal.ofReal
                                  (LiteralD1.Dconst ℓ k0 s (LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                                        (↑(Module.finrank ℝ E) : ℝ) (↑(Fintype.card X) : ℝ) +
                                      (1 + s) * (1 / LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) *
                                        Real.log (1 / δ) +
                                    LiteralD1.Rrem ℓ k0 s (LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                                      (LiteralD1.C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)
                                      (↑(Module.finrank ℝ E) : ℝ) (↑(Fintype.card X) : ℝ) δ J) ∧
                              LiteralD1.Rrem ℓ k0 s (LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                                  (LiteralD1.C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0) (↑(Module.finrank ℝ E) : ℝ)
                                  (↑(Fintype.card X) : ℝ) δ J ≤
                                K * (1 + Real.log (Real.log (1 / δ))) :=
  @LiteralD1c.grid_bay_finite X _ _ _ E _ _ _ _ _ 𝒜 _ _ _ Z _ _ _ φ supp hne ε A0 hA u w0 hw0 ℓ k0 s hℓ hu hk0 hM0 hs0 hs1

/-! ### `lem:bay-fc-inversion`: Lemma D.11 (Elementary logarithmic budget inversion) -/

/-- **Lemma D.11** `lem:bay-fc-inversion`: Elementary logarithmic budget inversion.

Manuscript: For a ≥ 0, b ≥ 1, put x = a + 2b log(a + b + 1). Then x ≥ a + b log(x + 1) and x > b;
moreover the first inequality persists for every real n ≥ x.

Lean: `log_budget_inversion` (`JointRootCert/GaussianInfo.lean`). -/
theorem lem_bay_fc_inversion
    {a : ℝ}
    {b : ℝ}
    (ha : 0 ≤ a)
    (hb : 1 ≤ b) :
      a + b * Real.log (logBudget a b + 1) ≤ logBudget a b ∧
        b < logBudget a b ∧ ∀ (n : ℝ), logBudget a b ≤ n → a + b * Real.log (n + 1) ≤ n :=
  @log_budget_inversion a b ha hb

/-! ### `thm:v10g-discovery`: Theorem D.12 (Explicit discovery and a frozen near-optimal plan) -/

/-- **Theorem D.12** `thm:v10g-discovery`: Explicit discovery and a frozen near-optimal plan.

Manuscript: On an event of probability at least 1 − α, every pilot estimate obeys ‖v_j − θ‖₂ ≤
ρ_j. On that event commitment occurs, and the retained record satisfies (√l − e_j)² ≥ c_* C with
c_* = (1 − k)³/(1 + 2k)², and I_a(θ, w) ≥ (√l − e_j)². An explicit upper bound on its pilot
observations is D̄ = 2x_D + q + 2 with the budget of eq:v10g-discovery-budget. The algorithm does
not receive C, A or D̄.

Lean: `LiteralD1c.grid_v10g_discovery` (`JointRootCert/LiteralD1c.lean`). Finite-grid oracle, with
C = I_*. -/
theorem thm_v10g_discovery
    {X : Type u_1}
    [Fintype X]
    [DecidableEq X]
    [Nonempty X]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {𝒜 : Type u_3}
    [Fintype 𝒜]
    [DecidableEq 𝒜]
    [Nonempty 𝒜]
    (u : X → E)
    (Q : 𝒜 → Set E)
    {A0 : ℝ}
    (hA : ∀ (a : 𝒜), ∃ lam ∈ Q a, ‖lam‖ ≤ A0)
    {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X)
    {ℓ : ℝ}
    {k0 : ℝ}
    {k : ℝ}
    (hℓ : 0 < ℓ)
    (hu : ∀ (x : X), ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0)
    (hM0 : ∀ (v : E), k0 * ‖v‖ ^ 2 ≤ ‖(designMap u w0 : E → EuclideanSpace ℝ X) v‖ ^ 2)
    (hk : 0 < k)
    (hk1 : k < 1)
    (α : ℝ)
    (e : ℕ → ℝ) :
      0 < α →
        α ≤ 1 →
          (∀ (j : ℕ), ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 α j / √2 ≤ e j) →
            (∀ (j : ℕ), e j ≤ √2 * ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 α j) →
              OracleContract u Q w0 k e (LiteralD1c.gridOa u Q w0 k ℓ k0 A0 e) (LiteralD1c.gridOw u Q w0 k ℓ k0 A0 e)
                  (LiteralD1c.gridOl u Q w0 k ℓ k0 A0 e) (LiteralD1c.gridOu u Q w0 k ℓ k0 A0 e) ∧
                ∀ (θ : E),
                  0 < LiteralD1.IstarG u Q θ →
                    (LiteralD1.tapeP X : Set (Fin 3 → X × ℕ → ℝ) → ENNReal)
                          {ω |
                            ¬∀ (j : ℕ),
                                ‖pilotV u w0 (obsTape u θ (LiteralD1.tapeξ 0) ω) j - θ‖ ≤
                                  pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 α j} ≤
                        ENNReal.ofReal α ∧
                      ∀ (ω : Fin 3 → X × ℕ → ℝ),
                        (∀ (j : ℕ),
                            ‖pilotV u w0 (obsTape u θ (LiteralD1.tapeξ 0) ω) j - θ‖ ≤
                              pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 α j) →
                          ∃ j,
                            commitAt e k (LiteralD1c.gridOl u Q w0 k ℓ k0 A0 e)
                                (pilotV u w0 (obsTape u θ (LiteralD1.tapeξ 0) ω)) j ∧
                              cstar k * LiteralD1.IstarG u Q θ ≤
                                  (√(LiteralD1c.gridOl u Q w0 k ℓ k0 A0 e j
                                          (pilotV u w0 (obsTape u θ (LiteralD1.tapeξ 0) ω) j)) -
                                      e j) ^
                                    2 ∧
                                (√(LiteralD1c.gridOl u Q w0 k ℓ k0 A0 e j
                                            (pilotV u w0 (obsTape u θ (LiteralD1.tapeξ 0) ω) j)) -
                                        e j) ^
                                      2 ≤
                                    gInfo u
                                      (Q
                                        (LiteralD1c.gridOa u Q w0 k ℓ k0 A0 e j
                                          (pilotV u w0 (obsTape u θ (LiteralD1.tapeξ 0) ω) j)))
                                      θ
                                      (LiteralD1c.gridOw u Q w0 k ℓ k0 A0 e j
                                        (pilotV u w0 (obsTape u θ (LiteralD1.tapeξ 0) ω) j)) ∧
                                  ∑ x, (↑(roundCount w0 (2 ^ j) x) : ℝ) ≤
                                    Dbar (pilotA ℓ k0 k (LiteralD1.IstarG u Q θ)) (↑(Module.finrank ℝ E) : ℝ) α
                                      (↑(Fintype.card X) : ℝ) :=
  @LiteralD1c.grid_v10g_discovery X _ _ _ E _ _ _ 𝒜 _ _ _ u Q A0 hA w0 hw0 ℓ k0 k hℓ hu hk0 hM0 hk hk1 α e

/-! ### `prop:v10g-safety-fallback`: Proposition D.13 (Conditional safety and a finite-mean reference design) -/

/-- **Proposition D.13** `prop:v10g-safety-fallback`: Conditional safety and a finite-mean reference design.

Manuscript: The fresh confirmation branch is uniformly (ε, δ/2)-safe, conditional on every finite
pilot history, including histories outside the pilot good event. The reference safeguard is also
uniformly (ε, δ/2)-safe. With the budget H_δ of eq:v10g-fallback-budget, E_θ F_δ ≤ H_δ < ∞.

Lean: `LiteralF2.safety_fallback_full` (`JointRootCert/LiteralF2.lean`). With the manuscript's
general enclosures; needs measurability of the lower enclosure in the tape. "Conditional on every
pilot history" is stated for every fixed frozen record on the independent fresh tape. -/
theorem prop_v10g_safety_fallback
    {X : Type}
    [Fintype X]
    {E : Type}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E]
    [BorelSpace E]
    {𝒜 : Type}
    [Fintype 𝒜]
    [Nonempty 𝒜]
    {Z : Type}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    (φ : Z → E)
    (supp : 𝒜 → Finset Z)
    (hne : ∀ (a : 𝒜), (supp a).Nonempty)
    (ε : ℝ)
    (hQ : ∀ (a : 𝒜), (strictAlt φ (supp a) (hne a) ε).Nonempty)
    (u : X → E)
    {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X)
    {ℓ : ℝ}
    {k0 : ℝ}
    {k : ℝ}
    {δ : ℝ}
    (hℓ : 0 < ℓ)
    (hu : ∀ (x : X), ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0)
    (hM0 : ∀ (v : E), k0 * ‖v‖ ^ 2 ≤ ‖(designMap u w0 : E → EuclideanSpace ℝ X) v‖ ^ 2)
    (hk : 0 < k)
    (hk1 : k ≤ 1)
    (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1)
    {Bbar : ℕ → ℝ}
    (hBlo : ∀ (n : ℕ), boundary (↑(Module.finrank ℝ E) : ℝ) (↑n : ℝ) (δ / 2) ≤ Bbar n)
    (hBhi : ∀ (n : ℕ), Bbar n ≤ boundary (↑(Module.finrank ℝ E) : ℝ) (↑n : ℝ) (δ / 2) + 1)
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ}
    (hJlo : ∀ (n : ℕ) (Y : X → ℕ → ℝ) (a : 𝒜),
  (gInfo u (strictAlt φ (supp a) (hne a) ε) (olsCount u (roundCount w0 (↑n : ℝ)) Y) fun x =>
        (↑(roundCount w0 (↑n : ℝ) x) : ℝ)) -
      1 ≤
    Jlow n Y a)
    (hJhi : ∀ (n : ℕ) (Y : X → ℕ → ℝ) (a : 𝒜),
  Jlow n Y a ≤
    gInfo u (strictAlt φ (supp a) (hne a) ε) (olsCount u (roundCount w0 (↑n : ℝ)) Y) fun x =>
      (↑(roundCount w0 (↑n : ℝ) x) : ℝ))
    (hJm : ∀ (n : ℕ) (a : 𝒜), Measurable fun Y => Jlow n Y a) :
      (∀ (θ : E) (a : 𝒜),
          ∀ p ∈ simplex X,
            ∀ (v : E),
              ∀ l ≤ gInfo u (strictAlt φ (supp a) (hne a) ε) v (floorDesign k w0 p),
                ∀ (Zlow : (X → ℕ → ℝ) → ℕ → ℝ),
                  (∀ (Y : X → ℕ → ℝ) (n : ℕ), max 0 (confirmZ u (floorDesign k w0 p) v l Y n - 1) ≤ Zlow Y n) →
                    (∀ (Y : X → ℕ → ℝ) (n : ℕ), Zlow Y n ≤ confirmZ u (floorDesign k w0 p) v l Y n) →
                      (LiteralD1.tapeP X : Set (Fin 3 → X × ℕ → ℝ) → ENNReal)
                          {ω |
                            ∃ n,
                              1 ≤ n ∧
                                Bbar n ≤ Zlow (obsTape u θ (LiteralD1.tapeξ 1) ω) n ∧ ε < regret (supp a) (hne a) (env φ θ)} ≤
                        ENNReal.ofReal (δ / 2)) ∧
        (∀ (θ : E),
            (LiteralD1.tapeP X : Set (Fin 3 → X × ℕ → ℝ) → ENNReal)
                {ω |
                  ∃ n,
                    1 ≤ n ∧
                      ∃ a, Bbar n ≤ Jlow n (obsTape u θ (LiteralD1.tapeξ 2) ω) a ∧ ε < regret (supp a) (hne a) (env φ θ)} ≤
              ENNReal.ofReal (δ / 2)) ∧
          ∀ (θ : E),
            0 < LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
              ∫⁻ (ω : Fin 3 → X × ℕ → ℝ),
                  roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ (LiteralD1.tapeξ 2) ω))) ∂LiteralD1.tapeP X ≤
                ENNReal.ofReal
                  (Hdelta (↑(Fintype.card X) : ℝ) (↑(Module.finrank ℝ E) : ℝ) δ
                    (LiteralD1.C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)) :=
  @LiteralF2.safety_fallback_full X _ E _ _ _ _ _ 𝒜 _ _ Z _ _ _ φ supp hne ε hQ u w0 hw0 ℓ k0 k δ hℓ hu hk0 hM0 hk hk1 hδ0 hδ1 Bbar hBlo hBhi Jlow hJlo hJhi hJm

/-! ### `thm:v10g-expectation`: Theorem D.14 (Correlated finite-confidence discovery and confirmation) -/

/-- **Theorem D.14** `thm:v10g-expectation`: Correlated finite-confidence discovery and confirmation.

Manuscript: The specified procedure is uniformly (ε, δ)-safe on ℝ^d. On every fixed instance with
C > 0 it has finite mean, and E_θ τ ≤ min{B_δ, H_δ/k + 1} with B_δ = (D̄ + x_C + q + 1)/(1 − k) +
1 + 2α(H_δ/k + 1). No unique best action, unique maximizing design or gap between competing
information rates is assumed.

Lean: `LiteralD1c.grid_v10g_expectation` (`JointRootCert/LiteralD1c.lean`). Finite-grid oracle. -/
theorem thm_v10g_expectation
    {X : Type u_1}
    [Fintype X]
    [DecidableEq X]
    [Nonempty X]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E]
    [BorelSpace E]
    {𝒜 : Type u_3}
    [Fintype 𝒜]
    [DecidableEq 𝒜]
    [Nonempty 𝒜]
    {Z : Type u_4}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    (φ : Z → E)
    (supp : 𝒜 → Finset Z)
    (hne : ∀ (a : 𝒜), (supp a).Nonempty)
    (ε : ℝ)
    {A0 : ℝ}
    (hA : ∀ (a : 𝒜), ∃ lam ∈ strictAlt φ (supp a) (hne a) ε, ‖lam‖ ≤ A0)
    (u : X → E)
    {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X)
    {ℓ : ℝ}
    {k0 : ℝ}
    {k : ℝ}
    (hℓ : 0 < ℓ)
    (hu : ∀ (x : X), ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0)
    (hM0 : ∀ (v : E), k0 * ‖v‖ ^ 2 ≤ ‖(designMap u w0 : E → EuclideanSpace ℝ X) v‖ ^ 2)
    (hk : 0 < k)
    (hk1 : k < 1)
    (δ : ℝ)
    (α : ℝ)
    (e : ℕ → ℝ) :
      0 < δ →
        δ ≤ 1 →
          0 < α →
            α ≤ 1 →
              (∀ (j : ℕ), ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 α j / √2 ≤ e j) →
                (∀ (j : ℕ), e j ≤ √2 * ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 α j) →
                  (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).Spec
                      (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 α δ ∧
                    (∀ (θ : E),
                        (LiteralD1.tapeP X : Set (Fin 3 → X × ℕ → ℝ) → ENNReal)
                            {ω |
                              (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).tauΩ θ ω <
                                  ⊤ ∧
                                ∃ a,
                                  (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).retΩ θ
                                        ω =
                                      some a ∧
                                    ε < regret (supp a) (hne a) (env φ θ)} ≤
                          ENNReal.ofReal δ) ∧
                      ∀ (θ : E),
                        0 < LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
                          ∫⁻ (ω : Fin 3 → X × ℕ → ℝ),
                              (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).tauΩ θ
                                ω ∂LiteralD1.tapeP X ≤
                            ENNReal.ofReal
                              (min
                                (Bdelta
                                  (Dbar (pilotA ℓ k0 k (LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ))
                                    (↑(Module.finrank ℝ E) : ℝ) α (↑(Fintype.card X) : ℝ))
                                  (logBudget
                                    (aC (↑(Module.finrank ℝ E) : ℝ) k
                                      (cstar k * LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) δ α)
                                    (bC k (cstar k * LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)))
                                  (↑(Fintype.card X) : ℝ) k α
                                  (Hdelta (↑(Fintype.card X) : ℝ) (↑(Module.finrank ℝ E) : ℝ) δ
                                    (LiteralD1.C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)))
                                (Hdelta (↑(Fintype.card X) : ℝ) (↑(Module.finrank ℝ E) : ℝ) δ
                                      (LiteralD1.C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0) /
                                    k +
                                  1)) :=
  @LiteralD1c.grid_v10g_expectation X _ _ _ E _ _ _ _ _ 𝒜 _ _ _ Z _ _ _ φ supp hne ε A0 hA u w0 hw0 ℓ k0 k hℓ hu hk0 hM0 hk hk1 δ α e

/-! ### `cor:v10g-target`: Corollary D.15 (Finite-confidence correlated confirmation bound) -/

/-- **Corollary D.15** `cor:v10g-target`: Finite-confidence correlated confirmation bound.

Manuscript: For the implementable choices and 0 < δ ≤ 1/4, E_θ τ ≤ (D_0 + q)/(1 − k) + (1 + s)
T_*^ε(θ) log(1/δ) + R_10, with the explicit remainder R_10 of eq:v10g-remainder. For each fixed
instance, ε and s > 0, R_10 = O(1 + log log(1/δ)) as δ ↓ 0. The constant D is independent of δ.

Lean: `LiteralD1c.grid_bay_finite` (`JointRootCert/LiteralD1c.lean`). The same Lean theorem as
Proposition D.10 (`grid_bay_finite`), whose bound carries the remainder R_10 of eq:v10g-remainder. -/
theorem cor_v10g_target
    {X : Type u_1}
    [Fintype X]
    [DecidableEq X]
    [Nonempty X]
    {E : Type u_2}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E]
    [BorelSpace E]
    {𝒜 : Type u_3}
    [Fintype 𝒜]
    [DecidableEq 𝒜]
    [Nonempty 𝒜]
    {Z : Type u_4}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    (φ : Z → E)
    (supp : 𝒜 → Finset Z)
    (hne : ∀ (a : 𝒜), (supp a).Nonempty)
    (ε : ℝ)
    {A0 : ℝ}
    (hA : ∀ (a : 𝒜), ∃ lam ∈ strictAlt φ (supp a) (hne a) ε, ‖lam‖ ≤ A0)
    (u : X → E)
    {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X)
    {ℓ : ℝ}
    {k0 : ℝ}
    {s : ℝ}
    (hℓ : 0 < ℓ)
    (hu : ∀ (x : X), ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0)
    (hM0 : ∀ (v : E), k0 * ‖v‖ ^ 2 ≤ ‖(designMap u w0 : E → EuclideanSpace ℝ X) v‖ ^ 2)
    (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
      (∀ (δ J : ℝ) (e : ℕ → ℝ),
          0 < δ →
            δ ≤ 1 →
              1 ≤ J →
                (∀ (j : ℕ), ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j / √2 ≤ e j) →
                  (∀ (j : ℕ), e j ≤ √2 * ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j) →
                    (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e δ).Spec
                        (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 (1 / (8 * J ^ 2)) δ ∧
                      ∀ (θ : E),
                        (LiteralD1.tapeP X : Set (Fin 3 → X × ℕ → ℝ) → ENNReal)
                            {ω |
                              (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e δ).tauΩ θ
                                    ω <
                                  ⊤ ∧
                                ∃ a,
                                  (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e
                                            δ).retΩ
                                        θ ω =
                                      some a ∧
                                    ε < regret (supp a) (hne a) (env φ θ)} ≤
                          ENNReal.ofReal δ) ∧
        ∀ (θ : E),
          0 < LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
            ∃ K,
              ∀ (δ J : ℝ) (e : ℕ → ℝ),
                0 < δ →
                  δ ≤ 1 / 4 →
                    1 + Real.log (1 / δ) ≤ J →
                      J < 3 + Real.log (1 / δ) →
                        (∀ (j : ℕ), ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j / √2 ≤ e j) →
                          (∀ (j : ℕ), e j ≤ √2 * ℓ * pilotRho (↑(Module.finrank ℝ E) : ℝ) k0 (1 / (8 * J ^ 2)) j) →
                            ∫⁻ (ω : Fin 3 → X × ℕ → ℝ),
                                  (LiteralD1c.gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e
                                        δ).tauΩ
                                    θ ω ∂LiteralD1.tapeP X ≤
                                ENNReal.ofReal
                                  (LiteralD1.Dconst ℓ k0 s (LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                                        (↑(Module.finrank ℝ E) : ℝ) (↑(Fintype.card X) : ℝ) +
                                      (1 + s) * (1 / LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) *
                                        Real.log (1 / δ) +
                                    LiteralD1.Rrem ℓ k0 s (LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                                      (LiteralD1.C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)
                                      (↑(Module.finrank ℝ E) : ℝ) (↑(Fintype.card X) : ℝ) δ J) ∧
                              LiteralD1.Rrem ℓ k0 s (LiteralD1.IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                                  (LiteralD1.C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0) (↑(Module.finrank ℝ E) : ℝ)
                                  (↑(Fintype.card X) : ℝ) δ J ≤
                                K * (1 + Real.log (Real.log (1 / δ))) :=
  @LiteralD1c.grid_bay_finite X _ _ _ E _ _ _ _ _ 𝒜 _ _ _ Z _ _ _ φ supp hne ε A0 hA u w0 hw0 ℓ k0 s hℓ hu hk0 hM0 hs0 hs1

/-! ### `thm:v34-action-local`: Theorem D.16 (Action-local optional evaluation and intersection-union root coverage) -/

/-- **Theorem D.16** `thm:v34-action-local`: Action-local optional evaluation and intersection-union root coverage.

Manuscript: Under every component null H_{a,z} and all positive unknown query variances, the
action-local wealth E^loc_{a,z}(j) is a nonnegative supermartingale starting at one. Stopping at
the first completed batch where the selected action satisfies min_{z ∈ J_{A_j}} E^loc_{A_j,z}(j) ≥
K/δ is (ε, δ)-safe under arbitrary predictable action and allocation policies, allocating error
δ/K per root action without a Bonferroni split over |J_a|.

Lean: `LiteralD2a.v34_action_local` (`JointRootCert/LiteralD2a.lean`). Arbitrary predictable
policies on intrinsic tapes (deterministic functions of the tapes), extended-real envelope. -/
theorem thm_v34_action_local
    {X : Type u_1}
    {A : Type u_2}
    {Z : Type u_3}
    {U : Type u_4}
    [Fintype X]
    [Fintype A]
    [DecidableEq A]
    {Ω : Type u_5}
    [MeasurableSpace Ω]
    (π : LiteralD2a.Policy X A Z)
    (hp : LiteralD2a.Policy.Predictable π)
    (J : A → Finset Z)
    (H : A → Z → Set U)
    (pred : X → U → ℝ)
    (hs : LiteralD2a.Policy.Sound π J H pred)
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ (x : X) (n : ℕ), Measurable (Y x n))
    (hind : ProbabilityTheory.iIndepFun (fun (p : X × ℕ) => Y (Prod.fst p) (Prod.snd p)) P)
    (θ : U)
    {v : X → ℝ}
    (hv : ∀ (x : X), (0 : ℝ) < v x)
    (hlaw : ∀ (x : X) (n : ℕ), ProbabilityTheory.HasLaw (Y x n) (ProbabilityTheory.gaussianReal (pred x θ) (Real.toNNReal (v x))) P) :
      (∀ (a : A),
          ∀ z ∈ J a,
            θ ∈ H a z →
              MeasureTheory.Supermartingale (fun (j : ℕ) (ω : Ω) => LiteralD2a.Policy.wealth π (tapeOf Y ω) a z j)
                  (LiteralD2a.Policy.obsFiltration hp hYm) P ∧
                (∀ (j : ℕ) (ω : Ω), (0 : ℝ) ≤ LiteralD2a.Policy.wealth π (tapeOf Y ω) a z j) ∧
                  ∀ (ω : Ω), LiteralD2a.Policy.wealth π (tapeOf Y ω) a z (0 : ℕ) = (1 : ℝ)) ∧
        ∀ (δ : ℝ),
          (0 : ℝ) < δ →
            (P : Set Ω → ENNReal)
                {ω : Ω |
                  LiteralD2a.Policy.Stops π J (tapeOf Y ω) δ ∧
                    ∃ z ∈ J (LiteralD2a.Policy.returned π J (tapeOf Y ω) δ),
                      θ ∈ H (LiteralD2a.Policy.returned π J (tapeOf Y ω) δ) z} ≤
              ENNReal.ofReal δ :=
  @LiteralD2a.v34_action_local X A Z U _ _ _ Ω _ π hp J H pred hs P _ Y hYm hind θ v hv hlaw

/-! ### `thm:v34-adaptive`: Theorem D.17 (Sparse four-power nuisance-KL tracking with unknown variances) -/

/-- **Theorem D.17** `thm:v34-adaptive`: Sparse four-power nuisance-KL tracking with unknown variances.

Manuscript: Assume fixed spanning query features, independent Gaussian observations with arbitrary
fixed σ_x² > 0, a finite root-action family, and 0 < C_* < ∞; use the plug-in predictor, the
certified design oracle with sticky selection, refreshes at batch indices 4^k with precision
(k+1)⁻¹ and hysteresis (k+1)^{-1/2}, the denominator-free allocation, action-local testing, the
two-nat numerical enclosure contract, and Borel measurable oracles. Then the procedure is (ε,
δ)-correct, and for every rational s ∈ (0,1] there is a finite constant D_s, independent of δ,
with E[τ_δ] ≤ D_s + (1 + s) C_*⁻¹ log(1/δ) and limsup_{δ↓0} E[τ_δ]/log(1/δ) ≤ 1/C_*.

Lean: `LiteralD2c.v34_adaptive_literal` (`JointRootCert/LiteralD2c.lean`). D_s and the tail are
literally eq:v34-discovery-constant and eq:v34-explicit-tail. Correctness is a bound on the bad
event over all batches. -/
theorem thm_v34_adaptive
    {Ω : Type u_1}
    [MeasurableSpace Ω]
    {X : Type u_2}
    {A : Type u_3}
    {Z : Type u_4}
    {U : Type u_5}
    [Fintype X]
    [Nonempty X]
    [DecidableEq X]
    [Fintype A]
    [Nonempty A]
    [DecidableEq A]
    (T : Tracker X A Z U)
    (hc : Tracker.Contract T)
    (hm : Tracker.Meas T)
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ (x : X) (n : ℕ), Measurable (Y x n))
    (hind : ProbabilityTheory.iIndepFun (fun (p : X × ℕ) => Y (Prod.fst p) (Prod.snd p)) P)
    (θ : U)
    {v : X → ℝ}
    (hv0 : ∀ (x : X), (0 : ℝ) < v x)
    (hlaw : ∀ (x : X) (n : ℕ),
  ProbabilityTheory.HasLaw (Y x n) (ProbabilityTheory.gaussianReal (Tracker.pred T x θ) (Real.toNNReal (v x))) P)
    (hC : (0 : ℝ) < LiteralD2c.Instance.Cstar (Tracker.inst T (fun (x : X) => Tracker.pred T x θ) v)) :
      (∀ (δ : ℝ),
          (0 : ℝ) < δ →
            (P : Set Ω → ENNReal)
                  {ω : Ω |
                    LiteralD2c.Stops T (tapeOf Y ω) δ ∧
                      ∃ z ∈ Tracker.J T (LiteralD2c.returned T (tapeOf Y ω) δ),
                        θ ∈ Tracker.H T (LiteralD2c.returned T (tapeOf Y ω) δ) z} ≤
                ENNReal.ofReal δ ∧
              (P : Set Ω → ENNReal) {ω : Ω | ¬LiteralD2c.Stops T (tapeOf Y ω) δ} = (0 : ENNReal)) ∧
        (∀ (s : ℝ),
            (0 : ℝ) < s →
              s ≤ (1 : ℝ) →
                ∀ (δ : ℝ),
                  (0 : ℝ) < δ →
                    δ < (1 : ℝ) →
                      ∫⁻ (ω : Ω), LiteralD2c.tau T (tapeOf Y ω) δ ∂P ≤
                        ENNReal.ofReal
                          (LiteralD2c.Instance.Ds (Tracker.inst T (fun (x : X) => Tracker.pred T x θ) v) s +
                            ((1 : ℝ) + s) / LiteralD2c.Instance.Cstar (Tracker.inst T (fun (x : X) => Tracker.pred T x θ) v) *
                              Real.log ((1 : ℝ) / δ))) ∧
          ∀ (c : ℝ),
            (1 : ℝ) / LiteralD2c.Instance.Cstar (Tracker.inst T (fun (x : X) => Tracker.pred T x θ) v) < c →
              ∀ᶠ (δ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
                ENNReal.toReal (∫⁻ (ω : Ω), LiteralD2c.tau T (tapeOf Y ω) δ ∂P) ≤ c * Real.log ((1 : ℝ) / δ) :=
  @LiteralD2c.v34_adaptive_literal Ω _ X A Z U _ _ _ _ _ _ T hc hm P _ Y hYm hind θ v hv0 hlaw hC

/-! ### `thm:v34-converse-main`: Theorem D.18 (Matching unknown-variance converse with a unique correct action) -/

/-- **Theorem D.18** `thm:v34-converse-main`: Matching unknown-variance converse with a unique correct action.

Manuscript: When the ε-correct root action is unique, every uniformly (ε, δ)-correct algorithm in
the unknown-variance Gaussian experiment model satisfies, for 0 < δ < 1/2, E τ_δ ≥ kl(1 − δ,
δ)/C_* and liminf_{δ↓0} E τ_δ / log(1/δ) ≥ C_*⁻¹.

Lean: `RandG.Regret.rv34_converse_main_regret` (`JointRootCert/Randomised2.lean`). Randomised
procedures, polyhedral instance, correctness stated in terms of regret. -/
theorem thm_v34_converse_main
    {X : Type u_1}
    {A : Type u_2}
    {Z : Type u_3}
    {E : Type u_4}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace X]
    [MeasurableSingletonClass X]
    [Fintype X]
    [MeasurableSpace A]
    [MeasurableSingletonClass A]
    {Sd : Type u_5}
    [MeasurableSpace Sd]
    [Fintype A]
    [Nonempty X]
    (G : LiteralD2d.Problem X A Z E)
    (hJ : ∀ (a : A), (G.J a).Nonempty)
    (astar : A)
    (θ : E)
    {v : X → ℝ}
    (hv : ∀ (x : X), 0 < v x)
    (huniq : ∀ (a : A), a ≠ astar → G.ε < G.reg a θ)
    (hCpos : 0 <
  Finset.univ.sup' (Exists.intro astar (Finset.mem_univ astar)) fun a =>
    actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)
    (ν : ℝ → MeasureTheory.Measure Sd)
    [∀ (δ : ℝ), MeasureTheory.IsProbabilityMeasure (ν δ)]
    (R : ℝ → RandG.RGSampler X Sd)
    (D : ℝ → RandG.RGDecision A Sd)
    (hcorr : ∀ (δ : ℝ), 0 < δ → δ < 1 / 2 → RandG.Regret.RCorrect G (ν δ) (R δ) (D δ) δ) :
      (∀ (δ : ℝ),
          0 < δ →
            δ < 1 / 2 →
              ENNReal.ofReal
                  (klBin (1 - δ) δ /
                    Finset.univ.sup' (Exists.intro astar (Finset.mem_univ astar)) fun a =>
                      actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v) ≤
                RandG.rexpTau (ν δ) (R δ) (fun x => G.pred x θ) v) ∧
        ∀
          c <
            1 /
              Finset.univ.sup' (Exists.intro astar (Finset.mem_univ astar)) fun a =>
                actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v,
          ∀ᶠ (δ : ℝ) in nhdsWithin 0 (Set.Ioi 0),
            ENNReal.ofReal (c * Real.log (1 / δ)) ≤ RandG.rexpTau (ν δ) (R δ) (fun x => G.pred x θ) v :=
  @RandG.Regret.rv34_converse_main_regret X A Z E _ _ _ _ _ _ _ _ _ _ _ Sd _ _ _ G hJ astar θ v hv huniq hCpos ν _ R D hcorr

/-! ### `prop:v34-work`: Proposition D.19 (Global solver-call reduction under sparse refreshes and action-local evidence) -/

/-- **Proposition D.19** `prop:v34-work`: Global solver-call reduction under sparse refreshes and action-local evidence.

Manuscript: Let J_max = max_a |J_a| and L_δ = 1 + log(1 + log(1/δ)). Through batch j, the
procedure performs at most K(1 + ⌊log₄ j⌋) globally certified design-game calls and J_max j
component-null likelihood solves. At stopping, E[W_design(τ_δ)] = O(K[1 + log(1 + L_δ)]) and
E[W_null(τ_δ)] = O(J_max[1 + L_δ²]).

Lean: `LiteralF7.v34_work_full` (`JointRootCert/LiteralF7.lean`). The tracker as a costed program
whose counters are incremented only by executed calls. -/
theorem prop_v34_work
    {X : Type u_1}
    {A : Type u_2}
    {Z : Type u_3}
    {U : Type u_4}
    [Fintype A]
    [DecidableEq A]
    [DecidableEq Z]
    {Ω : Type u_5}
    [MeasurableSpace Ω]
    [Fintype X]
    [Nonempty X]
    [DecidableEq X]
    [Nonempty A]
    (T : Tracker X A Z U)
    (hc : Tracker.Contract T)
    (hm : Tracker.Meas T)
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ (x : X) (n : ℕ), Measurable (Y x n))
    (hind : ProbabilityTheory.iIndepFun (fun (p : X × ℕ) => Y (Prod.fst p) (Prod.snd p)) P)
    {μ : X → ℝ}
    {v : X → ℝ}
    (hv0 : ∀ (x : X), (0 : ℝ) < v x)
    (hlaw : ∀ (x : X) (n : ℕ), ProbabilityTheory.HasLaw (Y x n) (ProbabilityTheory.gaussianReal (μ x) (Real.toNNReal (v x))) P)
    (hC : (0 : ℝ) < LiteralD2c.Instance.Cstar (Tracker.inst T μ v))
    {Jmax : ℕ}
    (hJmax : ∀ (a : A), Finset.card (Tracker.J T a) ≤ Jmax) :
      (∀ (y : X → ℕ → ℝ) (j : ℕ),
          (1 : ℕ) ≤ j → LiteralF7.CState.dc (LiteralF7.crun T y j) = Fintype.card A * ((1 : ℕ) + Nat.log (4 : ℕ) j)) ∧
        (∀ (y : X → ℕ → ℝ) (j : ℕ), LiteralF7.CState.nc (LiteralF7.crun T y j) ≤ Jmax * j) ∧
          ∀ (δ : ℝ),
            (0 : ℝ) < δ →
              δ < (1 : ℝ) →
                ∫⁻ (ω : Ω), LiteralF7.cStopIdx T (tapeOf Y ω) δ ∂P ≤
                    ENNReal.ofReal (LiteralD2e.cWork (Tracker.inst T μ v) * ((1 : ℝ) + LiteralD2b.Ldelta δ ^ (2 : ℕ))) ∧
                  ∫⁻ (ω : Ω), LiteralF7.cDesignStop T (tapeOf Y ω) δ ∂P ≤
                      ENNReal.ofReal
                        (LiteralD2e.cWork (Tracker.inst T μ v) *
                          ((↑(Fintype.card A) : ℝ) * ((1 : ℝ) + Real.log ((1 : ℝ) + LiteralD2b.Ldelta δ)))) ∧
                    ∫⁻ (ω : Ω), LiteralF7.cNullStop T (tapeOf Y ω) δ ∂P ≤
                      ENNReal.ofReal
                        (LiteralD2e.cWork (Tracker.inst T μ v) * ((↑Jmax : ℝ) * ((1 : ℝ) + LiteralD2b.Ldelta δ ^ (2 : ℕ)))) :=
  @LiteralF7.v34_work_full X A Z U _ _ _ Ω _ _ _ _ _ T hc hm P _ Y hYm hind μ v hv0 hlaw hC Jmax hJmax

/-! ### `lem:v34-transport`: Lemma D.20 (Uniform stability of the nuisance-KL information game) -/

/-- **Lemma D.20** `lem:v34-transport`: Uniform stability of the nuisance-KL information game.

Manuscript: Let v_x, ṽ_x > 0 and m_x, m̃_x ∈ ℝ. For every action a and design w, |C_a(w; m, v) −
C_a(w; m̃, ṽ)| ≤ d(m, v; m̃, ṽ) and |C_a*(m, v) − C_a*(m̃, ṽ)| ≤ d(m, v; m̃, ṽ), where d = max_x
{|m_x − m̃_x| / (2√min(v_x, ṽ_x)) + (1/2)|log(v_x/ṽ_x)|}.

Lean: `actGame_transport` (`JointRootCert/UnknownVariance.lean`). Main theorem: the design-level
bound; companion: the bound for the optimised game. -/
theorem lem_v34_transport
    {X : Type u_1}
    [Fintype X]
    {U : Type u_2}
    {Z : Type u_3}
    [Nonempty X]
    (J : Finset Z)
    (hJ : J.Nonempty)
    (H : Z → Set U)
    (pred : X → U → ℝ)
    {w : X → ℝ}
    {m : X → ℝ}
    {v : X → ℝ}
    {m' : X → ℝ}
    {v' : X → ℝ}
    {d : ℝ}
    (hw : w ∈ simplex X)
    (hv : ∀ (x : X), 0 < v x)
    (hv' : ∀ (x : X), 0 < v' x)
    (hd : ∀ (x : X), |m x - m' x| / (2 * √(min (v x) (v' x))) + 1 / 2 * |Real.log (v x / v' x)| ≤ d) :
      |actGame J hJ H pred w m v - actGame J hJ H pred w m' v'| ≤ d :=
  @actGame_transport X _ U Z _ J hJ H pred w m v m' v' d hw hv hv' hd

/-- Companion to Lemma D.20 `lem:v34-transport`: the bound for C_a*. Lean: `actGameStar_transport`
(`JointRootCert/UnknownVariance.lean`). -/
theorem lem_v34_transport_star
    {X : Type u_1}
    [Fintype X]
    {U : Type u_2}
    {Z : Type u_3}
    [Nonempty X]
    [DecidableEq X]
    (J : Finset Z)
    (hJ : J.Nonempty)
    (H : Z → Set U)
    (pred : X → U → ℝ)
    {m : X → ℝ}
    {v : X → ℝ}
    {m' : X → ℝ}
    {v' : X → ℝ}
    {d : ℝ}
    (hv : ∀ (x : X), 0 < v x)
    (hv' : ∀ (x : X), 0 < v' x)
    (hd : ∀ (x : X), |m x - m' x| / (2 * √(min (v x) (v' x))) + 1 / 2 * |Real.log (v x / v' x)| ≤ d) :
      |actGameStar J hJ H pred m v - actGameStar J hJ H pred m' v'| ≤ d :=
  @actGameStar_transport X _ U Z _ _ J hJ H pred m v m' v' d hv hv' hd

/-! ### `lem:v34-batch-comparison`: Lemma D.21 (A uniform batch log-likelihood comparison) -/

/-- **Lemma D.21** `lem:v34-batch-comparison`: A uniform batch log-likelihood comparison.

Manuscript: Let v_min = min_x v_x > 0 and L_0 = 40(1 + v_min⁻¹ + v_min^{-1/2}). For one batch,
suppose the within-batch means, centred variances and predictable estimates are each within ρ ≤
min{1, v_min/8} of the true values. Then for every action and unscreened component with nonempty
null set, |R_i⁻¹ log(q_i(Y_i)/U_{a,z,i}(Y_i)) − C_{a,z}(w̃_i; μ, v)| ≤ L_0 ρ.

Lean: `batch_comparison_loglik` (`JointRootCert/UnknownVarianceBatch.lean`). Needs the null set to
be nonempty, now stated in the manuscript. -/
theorem lem_v34_batch_comparison
    {X : Type u_1}
    [Fintype X]
    {U : Type u_2}
    {H : Set U}
    {pred : X → U → ℝ}
    {r : X → ℕ}
    {y : X → ℕ → ℝ}
    {muh : X → ℝ}
    {vh : X → ℝ}
    [Nonempty X]
    (hH : H.Nonempty)
    {μ : X → ℝ}
    {v : X → ℝ}
    {vmin : ℝ}
    {ρ : ℝ}
    (hvmin : 0 < vmin)
    (hv : ∀ (x : X), vmin ≤ v x)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hρv : ρ ≤ vmin / 8)
    (h1 : ∀ (x : X), |batchMean r y x - μ x| ≤ ρ)
    (h2 : ∀ (x : X), |batchVar r y x - v x| ≤ ρ)
    (h3 : ∀ (x : X), |muh x - μ x| ≤ ρ)
    (h4 : ∀ (x : X), |vh x - v x| ≤ ρ) :
      |(∑ x, (↑(r x) : ℝ))⁻¹ * Real.log (batchDens r muh vh y / nullEnv H pred r y) -
            compGame H pred (fun x => (↑(r x) : ℝ) / ∑ x, (↑(r x) : ℝ)) μ v| ≤
        L0 vmin * ρ :=
  @batch_comparison_loglik X _ U H pred r y muh vh _ hH μ v vmin ρ hvmin hv hρ0 hρ1 hρv h1 h2 h3 h4

/-! ### `lem:v34-concentration`: Lemma D.22 (Explicit intrinsic-tape Gaussian concentration) -/

/-- **Lemma D.22** `lem:v34-concentration`: Explicit intrinsic-tape Gaussian concentration.

Manuscript: For 0 < r ≤ v_x/8 put n_0 = max{3, ⌈4v_x/r⌉} and Q_x(n, r) = 1 for n < n_0, min{1,
2e^{−nr²/(2v_x)} + 2e^{−(n−1)r²/(64v_x²)}} otherwise. For a fixed prefix of n i.i.d. observations,
the probability that its mean or centred variance differs from (μ_x, v_x) by more than r is at
most Q_x(n, r). For a data-dependent prefix count n ≥ n_0, the probability that any such prefix
violates the condition is at most Σ_{n ≥ n_0} Q_x(n, r).

Lean: `gaussian_concentration_prefix` (`JointRootCert/Completions4.lean`). For i.i.d. Gaussian
observations, with no tail hypothesis. -/
theorem lem_v34_concentration
    {Ω : Type u_1}
    {m0 : MeasurableSpace Ω}
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {v : ℝ}
    {r : ℝ}
    {μ : ℝ}
    (hv : 0 < v)
    (hr0 : 0 < r)
    (hrv : r ≤ v / 8)
    {Y : ℕ → Ω → ℝ}
    (hind : ProbabilityTheory.iIndepFun Y P)
    (hY : ∀ (i : ℕ), ProbabilityTheory.HasLaw (Y i) (ProbabilityTheory.gaussianReal μ v.toNNReal) P)
    (N : ℕ) :
      (Summable fun n => Qtail v n r) ∧
        (P : Set Ω → ENNReal)
              {ω |
                ∃ n,
                  N ≤ n ∧
                    (r < |(∑ i ∈ Finset.range n, Y i ω) / (↑n : ℝ) - μ| ∨
                      r < |(∑ i ∈ Finset.range n, (Y i ω - (∑ j ∈ Finset.range n, Y j ω) / (↑n : ℝ)) ^ 2) / (↑n : ℝ) - v|)} ≤
            ENNReal.ofReal (∑' (n : ℕ), if N ≤ n then Qtail v n r else 0) ∧
          ∀ (κ : Ω → ℕ),
            (∀ (ω : Ω), N ≤ κ ω) →
              (P : Set Ω → ENNReal)
                  {ω |
                    r < |(∑ i ∈ Finset.range (κ ω), Y i ω) / (↑(κ ω) : ℝ) - μ| ∨
                      r <
                        |(∑ i ∈ Finset.range (κ ω), (Y i ω - (∑ j ∈ Finset.range (κ ω), Y j ω) / (↑(κ ω) : ℝ)) ^ 2) /
                              (↑(κ ω) : ℝ) -
                            v|} ≤
                ENNReal.ofReal (∑' (n : ℕ), if N ≤ n then Qtail v n r else 0) :=
  @gaussian_concentration_prefix Ω m0 P _ v r μ hv hr0 hrv Y hind hY N

/-! ### `thm:v34-converse`: Theorem D.23 (Unknown-variance nuisance-KL lower bound for one correct answer) -/

/-- **Theorem D.23** `thm:v34-converse`: Unknown-variance nuisance-KL lower bound for one correct answer.

Manuscript: Suppose the Gaussian experiment model has a unique ε-correct root action and 0 < C_* <
∞. For every family of procedures uniformly (ε, δ)-correct over the fixed-feature Gaussian model
with arbitrary positive unknown query variances, E τ_δ ≥ kl(1 − δ, δ)/C_* and liminf_{δ↓0} E τ_δ /
log(1/δ) ≥ C_*⁻¹.

Lean: `RandG.Regret.rv34_converse_regret` (`JointRootCert/Randomised2.lean`). Randomised
procedures; correctness stated in terms of regret. -/
theorem thm_v34_converse
    {X : Type u_1}
    {A : Type u_2}
    {Z : Type u_3}
    {E : Type u_4}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace X]
    [MeasurableSingletonClass X]
    [Fintype X]
    [MeasurableSpace A]
    [MeasurableSingletonClass A]
    {Sd : Type u_5}
    [MeasurableSpace Sd]
    [Fintype A]
    [Nonempty X]
    (G : LiteralD2d.Problem X A Z E)
    (hJ : ∀ (a : A), (G.J a).Nonempty)
    (astar : A)
    (θ : E)
    {v : X → ℝ}
    (hv : ∀ (x : X), 0 < v x)
    (huniq : ∀ (a : A), a ≠ astar → G.ε < G.reg a θ)
    (hCpos : 0 <
  Finset.univ.sup' (Exists.intro astar (Finset.mem_univ astar)) fun a =>
    actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)
    (ν : MeasureTheory.Measure Sd)
    [MeasureTheory.IsProbabilityMeasure ν]
    (R : RandG.RGSampler X Sd)
    (D : RandG.RGDecision A Sd)
    {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ < 1 / 2)
    (hcorr : RandG.Regret.RCorrect G ν R D δ) :
      ENNReal.ofReal
          (klBin (1 - δ) δ /
            Finset.univ.sup' (Exists.intro astar (Finset.mem_univ astar)) fun a =>
              actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v) ≤
        RandG.rexpTau ν R (fun x => G.pred x θ) v :=
  @RandG.Regret.rv34_converse_regret X A Z E _ _ _ _ _ _ _ _ _ _ _ Sd _ _ _ G hJ astar θ v hv huniq hCpos ν _ R D δ hδ0 hδ hcorr

/-! ### `prop:uct-coupling`: Proposition E.1 (Safe permanent retirement) -/

/-- **Proposition E.1** `prop:uct-coupling`: Safe permanent retirement.

Manuscript: Under nested nonempty confidence boxes, (i) an internal incidence (v, j) can be
permanently removed from a protected MAX evaluation once u_t(j) < max_{k ∈ E_live(v) ∖ {j}}
l_t(k); and (ii) a marginal leader-and-stop monitor can retire root action b once U_t(b) < max_{a
≠ b, a active} L_t(a). The first rule preserves protected numerical intervals. The second
preserves the lower-bound leader and, for ε ≥ 0, the marginal stopping bit, but not necessarily
the numerical marginal gap. Neither rule changes the original graph used by a passive traversal
policy.

Lean: `LiteralE7a.ram_work_bounds_display` (`JointRootCert/LiteralE7a.lean`). The main theorem is
the README's literal statement: for a retirement run, the selective and eager engines give the
same outputs at every time, with the work display eq:ram-work-bounds of the proof (linear
initialisation, O(log(2+D)) per delivery; `W` read as monitor work). The companions state rules
(i) and (ii) themselves. -/
theorem prop_uct_coupling
    {α : Type u_1}
    [LinearOrder α]
    [OrderBot α]
    (R : LiteralE4.Traj α) :
      (∀ (t : ℕ), LiteralE7a.outSD R t = LiteralE7a.outED R t) ∧
        R.T + R.S0 ≤ LiteralE7a.WeagerD R ∧
          LiteralE7a.WeagerD R ≤ LiteralE7a.initWB R + R.samp + 6 * R.T + 2 * (R.Q * R.K) + (Nat.clog 2 R.D + 5) * R.S0 ∧
            R.T + R.S ≤ LiteralE7a.WliveD R ∧
              LiteralE7a.WliveD R ≤
                  LiteralE7a.initWB R + R.samp + 6 * R.T + 8 * (R.Q * R.K) + 2 * ((Nat.clog 2 R.D + 6) * R.S) +
                      2 * ((2 * Nat.clog 2 R.D + 4) * R.Rret) +
                    4 * (R.G0.N + DagRetire.live R.G0) ∧
                LiteralE7a.initWB R ≤ 4 * (R.G0.N + 2 * DagRetire.live R.G0) ∧
                  (R.T ≤ R.samp ∧ R.samp ≤ R.T * ((R.G0.L + 1) * (R.D + 1))) ∧ R.S ≤ R.S0 ∧ R.Rret ≤ DagRetire.live R.G0 :=
  @LiteralE7a.ram_work_bounds_display α _ _ R

/-- Companion to Proposition E.1 `prop:uct-coupling`: rule (i): removing a dominated incidence leaves
the protected MAX unchanged on every sub-box. Lean: `protected_pruning`
(`JointRootCert/PassiveRetirement.lean`). -/
theorem prop_uct_coupling_pruning
    {X : Type u_1}
    {E : Type u_2}
    [DecidableEq E]
    (B : Set X)
    (F : E → X → ℝ)
    (l : E → ℝ)
    (u : E → ℝ)
    (hl : ∀ x ∈ B, ∀ (e : E), l e ≤ F e x)
    (hu : ∀ x ∈ B, ∀ (e : E), F e x ≤ u e)
    (live : Finset E)
    {j : E}
    {k : E}
    (hk : k ∈ live.erase j)
    (hdom : u j < l k) :
      ∃ (hne : (live.erase j).Nonempty),
        ∀ B' ⊆ B,
          ∀ x ∈ B',
            (live.sup' (Exists.intro k (Finset.mem_of_mem_erase hk)) fun e => F e x) = (live.erase j).sup' hne fun e => F e x :=
  @protected_pruning X E _ B F l u hl hu live j k hk hdom

/-- Companion to Proposition E.1 `prop:uct-coupling`: rule (ii): retirement preserves the lower-bound
leader. Lean: `RetireRun.lowLeader_iff` (`JointRootCert/PassiveRetirement.lean`). -/
theorem prop_uct_coupling_leader
    {A : Type u_1}
    [Fintype A]
    {L : ℕ → A → ℝ}
    {U : ℕ → A → ℝ}
    {act : ℕ → Finset A}
    [LinearOrder A]
    [Nonempty A]
    (h : RetireRun L U act)
    (t : ℕ)
    (a : A) :
      LowLeader Finset.univ (L t) a ↔ LowLeader (act t) (L t) a :=
  @RetireRun.lowLeader_iff A _ L U act _ _ h t a

/-- Companion to Proposition E.1 `prop:uct-coupling`: rule (ii): for ε ≥ 0, retirement preserves the
marginal stopping bit. Lean: `RetireRun.stops_iff` (`JointRootCert/PassiveRetirement.lean`). -/
theorem prop_uct_coupling_stop
    {A : Type u_1}
    [Fintype A]
    {L : ℕ → A → ℝ}
    {U : ℕ → A → ℝ}
    {act : ℕ → Finset A}
    [LinearOrder A]
    [Nonempty A]
    (h : RetireRun L U act)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (t : ℕ)
    (a : A) :
      MarginalStops Finset.univ (L t) (U t) ε a ↔ MarginalStops (act t) (L t) (U t) ε a :=
  @RetireRun.stops_iff A _ L U act _ _ h ε hε t a

/-- Companion to Proposition E.1 `prop:uct-coupling`: rule (ii) need not preserve the numerical
marginal gap (explicit example). Lean: `LiteralE4.gap_not_preserved`
(`JointRootCert/LiteralE4a.lean`). -/
theorem prop_uct_coupling_gap :
      RetireRun (fun x => LiteralE4.exL) (fun x => LiteralE4.exU) LiteralE4.exAct ∧
        LowLeader Finset.univ LiteralE4.exL 0 ∧
          LowLeader (LiteralE4.exAct 1) LiteralE4.exL 0 ∧
            (∀ (ε : ℝ),
                0 ≤ ε →
                  MarginalStops Finset.univ LiteralE4.exL LiteralE4.exU ε 0 ∧
                    MarginalStops (LiteralE4.exAct 1) LiteralE4.exL LiteralE4.exU ε 0) ∧
              ∃ (h1 : (Finset.univ.erase 0).Nonempty) (h2 : ((LiteralE4.exAct 1).erase 0).Nonempty),
                LiteralE4.margGap Finset.univ LiteralE4.exL LiteralE4.exU 0 h1 = -5 ∧
                  LiteralE4.margGap (LiteralE4.exAct 1) LiteralE4.exL LiteralE4.exU 0 h2 = -9 :=
  @LiteralE4.gap_not_preserved

/-- Companion to Proposition E.1 `prop:uct-coupling`: monitors that agree on the trajectory induce the
same trajectory (the passive policy is unchanged). Lean: `coupled_trajectories`
(`JointRootCert/PassiveRetirement.lean`). -/
theorem prop_uct_coupling_trajectories
    {H : Type u_1}
    {O : Type u_2}
    (step : H → O → H)
    (mon₁ : H → O)
    (mon₂ : H → O)
    (h0 : H)
    (hagree : ∀ (t : ℕ), mon₁ (runTraj step mon₁ h0 t) = mon₂ (runTraj step mon₁ h0 t))
    (t : ℕ) :
      runTraj step mon₁ h0 t = runTraj step mon₂ h0 t :=
  @coupled_trajectories H O step mon₁ mon₂ h0 hagree t

/-! ### `thm:onpolicy-uct`: Theorem E.2 (Selective vs. eager maintenance separations on UCT and Root-PUCT funnels) -/

/-- **Theorem E.2** `thm:onpolicy-uct`: Selective vs. eager maintenance separations on UCT and Root-PUCT funnels.

Manuscript: On the bounded out-degree two-exit funnel DAGs of size Θ(m) under local UCT (g_m =
m^{−1/16}/4), decision-selective maintenance performs O(m) total work whereas full-incidence eager
propagation incurs Ω(m log m) on the identical sample path. Under fixed-prior Root-PUCT (g_m =
m^{−α}, 0 < α < 1/2), both monitors stop after Θ(m^{2α} log² m) rollouts, with selective work Θ(m)
versus Θ(m^{1+α} log m) for eager propagation.

Lean: `LiteralE2.onpolicy_uct_funnel_full` (`JointRootCert/LiteralE2.lean`). Main theorem: the
local-UCT half, with UCT at every internal vertex and the index eq:uct-index under both readings
of N_t(v); the two-exit funnel is `monFunnelCirc`. Companion: the Root-PUCT half. Asymptotic
orders are explicit two-sided inequalities. -/
theorem thm_onpolicy_uct
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ1 : δ < (1 : ℝ)) :
      ∃ (m0 : ℕ) (c : ℝ) (C : ℝ),
        (0 : ℝ) < c ∧
          ∀ (m : ℕ),
            m0 ≤ m →
              ∀ (g : ℝ),
                g = (1 / 4 : ℝ) * (↑m : ℝ) ^ (-(1 / 16 : ℝ)) →
                  ∀ (sel : ℕ → Fin (3 : ℕ)) (sub : ℕ → Fin (2 : ℕ)) (arm : Fin (2 : ℕ) → List Bool → ℕ → Fin (2 : ℕ)),
                    LiteralE2.FullFunnelSearch m g sel sub arm →
                      LiteralE2.FunnelConclusion δ c C m g (LiteralE2.fullRule m sel sub arm) sel sub :=
  @LiteralE2.onpolicy_uct_funnel_full δ hδ0 hδ1

/-- Companion to Theorem E.2 `thm:onpolicy-uct`: the Root-PUCT half. Lean:
`LiteralE5.v2separation_literal` (`JointRootCert/LiteralE5.lean`). -/
theorem thm_onpolicy_uct_rootpuct
    {δ : ℝ}
    {α : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2)
    (hα0 : 0 < α)
    (hα : α < 1 / 2) :
      ∃ m0 T cτ Cτ cH CH C1 cF CF,
        0 < cτ ∧
          0 < cH ∧
            0 < C1 ∧
              0 < cF ∧
                ∀ (m : ℕ),
                  m0 ≤ m →
                    ∀ (g : ℝ),
                      g = (↑m : ℝ) ^ (-α) →
                        ∀ (rule : ℕ → ℕ → Bool) (pick : LiteralE5.Hist → Fin 3),
                          LiteralE5.IsPuctPick pick →
                            ∃ tc τ,
                              tc ≤ T ∧
                                LiteralE5.SeparationBounds m δ g rule pick tc τ cτ Cτ cH CH C1 cF CF
                                  ((↑m : ℝ) ^ (2 * α) * Real.log (↑m : ℝ) ^ 2) ((↑m : ℝ) ^ α * Real.log (↑m : ℝ))
                                  ((↑m : ℝ) ^ (1 + α) * Real.log (↑m : ℝ)) :=
  @LiteralE5.v2separation_literal δ α hδ0 hδ hα0 hα

/-! ### `thm:ta-core`: Theorem E.3 (Wide Common-Core Support Compilation Cost) -/

/-- **Theorem E.3** `thm:ta-core`: Wide Common-Core Support Compilation Cost.

Manuscript: There exist explicit DAGs with r + 1 root actions, Θ(r²) edges and a unique ε-optimal
root action at ε = 1/5 on which TA-UCT with either Selective or Eager graph maintenance certifies
the optimal action in O(r² log² r) total scalar work, whereas materializing explicit flat
root-to-terminal supports at startup requires Ω(r³) operations. A dyadic cover compiler that
exploits contiguous terminal ordering achieves the same O(r² log² r) bound on this layout.

Lean: `LiteralF5.ta_core_full` (`JointRootCert/LiteralF5.lean`). An explicit local-UCT search at
every vertex, both readings of N_t(v), c_uct = 2. -/
theorem thm_ta_core
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ1 : δ < (1 : ℝ)) :
      ∃ (A : ℝ) (B : ℝ) (C : ℝ),
        (0 : ℝ) < A ∧
          (0 : ℝ) < B ∧
            (0 : ℝ) < C ∧
              ∀ (r : ℕ) [inst : NeZero r],
                (2 : ℕ) ≤ r →
                  ∀ (lit : Bool) (sel : ℕ → Fin (r + (1 : ℕ))) (act : Fin r → ℕ → Fin (2 : ℕ))
                    (arm : List Bool → ℕ → Fin (2 : ℕ)),
                    LiteralF5.FullCoreSearch r lit sel act arm →
                      ∀ (rule : ℕ → ℕ → Bool) (zt : ℕ → CoreZ r),
                        rule = LiteralF5.fullCoreRule r sel act arm →
                          zt = LiteralF5.fullCoreTerm r sel act arm →
                            (∀ (k : ℕ) (a : Fin (r + (1 : ℕ))),
                                LiteralE.cvLo
                                      (LiteralE.cvRun r (coreBox r (coreRadius r δ) zt) (fun (k : ℕ) => zt (r + (1 : ℕ) + k))
                                        k)
                                      a =
                                    coreL r (coreBox r (coreRadius r δ) zt) k a ∧
                                  LiteralE.cvHi
                                      (LiteralE.cvRun r (coreBox r (coreRadius r δ) zt) (fun (k : ℕ) => zt (r + (1 : ℕ) + k))
                                        k)
                                      a =
                                    coreU r (coreBox r (coreRadius r δ) zt) k a) ∧
                              (∀ (s : Bool) (k : ℕ) (a : Fin (r + (1 : ℕ))),
                                  LiteralE.cvStops
                                      (LiteralE.cvRun r (coreBox r (coreRadius r δ) zt) (fun (k : ℕ) => zt (r + (1 : ℕ) + k))
                                        k)
                                      a ↔
                                    coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
                                      (coreBox r (coreRadius r δ) zt k) a) ∧
                                ∃ (τ : ℕ),
                                  LiteralE.cvStops
                                      (LiteralE.cvRun r (coreBox r (coreRadius r δ) zt) (fun (k : ℕ) => zt (r + (1 : ℕ) + k))
                                        τ)
                                      (Fin.last r) ∧
                                    (∀ (s : Bool),
                                        coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
                                          (coreBox r (coreRadius r δ) zt τ) (Fin.last r)) ∧
                                      (∀ k < τ,
                                          ∀ (a : Fin (r + (1 : ℕ))),
                                            ¬LiteralE.cvStops
                                                (LiteralE.cvRun r (coreBox r (coreRadius r δ) zt)
                                                  (fun (k : ℕ) => zt (r + (1 : ℕ) + k)) k)
                                                a) ∧
                                        (∀ (s : Bool),
                                            ∀ k < τ,
                                              ∀ (a : Fin (r + (1 : ℕ))),
                                                ¬coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
                                                    (coreBox r (coreRadius r δ) zt k) a) ∧
                                          (∀ (k : ℕ) (a : Fin (r + (1 : ℕ))),
                                              LiteralE.cvStops
                                                  (LiteralE.cvRun r (coreBox r (coreRadius r δ) zt)
                                                    (fun (k : ℕ) => zt (r + (1 : ℕ) + k)) k)
                                                  a →
                                                a = Fin.last r) ∧
                                            (↑(r + (1 : ℕ) + τ) : ℝ) ≤ A * (↑r : ℝ) * Real.log (↑r : ℝ) ∧
                                              (∀ (s : Bool),
                                                  (↑(coreTotalWork s r (coreRadius r δ) rule sel zt τ) : ℝ) ≤
                                                    B * (↑r : ℝ) ^ (2 : ℕ) * Real.log (↑r : ℝ)) ∧
                                                (↑(LiteralE.cvTotalWork r (coreRadius r δ) rule sel zt τ) : ℝ) ≤
                                                    C * (↑r : ℝ) ^ (2 : ℕ) * Real.log (↑r : ℝ) ^ (2 : ℕ) ∧
                                                  r ^ (3 : ℕ) ≤
                                                      Prod.snd (LiteralE.flatAll (coreAct r) (List.finRange (r + (1 : ℕ)))) ∧
                                                    ∀ (out : Fin (r + (1 : ℕ)) → List (CoreZ r)),
                                                      (∀ (a : Fin (r + (1 : ℕ))), coreSupp r a ⊆ List.toFinset (out a)) →
                                                        r ^ (3 : ℕ) ≤ ∑ a : Fin (r + (1 : ℕ)), List.length (out a) :=
  @LiteralF5.ta_core_full δ hδ0 hδ1

/-! ### `lem:v2counts`: Lemma E.4 (Uniform finite-horizon count bounds) -/

/-- **Lemma E.4** `lem:v2counts`: Uniform finite-horizon count bounds.

Manuscript: For every suboptimal arm and every t ≥ K, n_i(t) ≤ max{1, λ_i √t / Δ_i}. For every arm
and every integer t ≥ 2K, n_i(t) + 1 > λ_i √⌊t/2⌋ / (Δ_i + 4Λ/√t) ≥ λ_i t / (√3 (Δ_i √t + 4Λ)).
These bounds hold for every tie-breaking choice.

Lean: `RootPUCTTrace.count_le` (`JointRootCert/RootPUCT.lean`). Main theorem: the upper bound;
companion: the lower bounds. -/
theorem lem_v2counts
    {ι : Type u_1}
    [Fintype ι]
    [DecidableEq ι]
    {μ : ι → ℝ}
    {lam : ι → ℝ}
    {n : ℕ → ι → ℕ}
    {sel : ℕ → ι}
    (h : RootPUCTTrace μ lam n sel)
    (hlam : ∀ (i : ι), 0 < lam i)
    {i : ι}
    {star : ι}
    (hgap : μ i < μ star)
    {t : ℕ}
    (ht : Fintype.card ι ≤ t) :
      (↑(n t i) : ℝ) ≤ max 1 (lam i * √(↑t : ℝ) / (μ star - μ i)) :=
  @RootPUCTTrace.count_le ι _ _ μ lam n sel h hlam i star hgap t ht

/-- Companion to Lemma E.4 `lem:v2counts`: the lower bounds. Lean: `RootPUCTTrace.count_lower`
(`JointRootCert/RootPUCT.lean`). -/
theorem lem_v2counts_lower
    {ι : Type u_1}
    [Fintype ι]
    [DecidableEq ι]
    {μ : ι → ℝ}
    {lam : ι → ℝ}
    {n : ℕ → ι → ℕ}
    {sel : ℕ → ι}
    (h : RootPUCTTrace μ lam n sel)
    (hlam : ∀ (i : ι), 0 < lam i)
    {star : ι}
    (hstar : ∀ (j : ι), μ j ≤ μ star)
    (i : ι)
    {t : ℕ}
    (ht : 2 * Fintype.card ι ≤ t) :
      lam i * (↑t : ℝ) / (√3 * ((μ star - μ i) * √(↑t : ℝ) + 4 * ∑ j, lam j)) < (↑(n t i) : ℝ) + 1 :=
  @RootPUCTTrace.count_lower ι _ _ μ lam n sel h hlam star hstar i t ht

/-! ### `cor:v2countscales`: Corollary E.5 (Fixed gaps versus a shrinking gap) -/

/-- **Corollary E.5** `cor:v2countscales`: Fixed gaps versus a shrinking gap.

Manuscript: With fixed positive λ_i and fixed K, an optimal arm has count Ω(t). Every arm of fixed
positive gap has count Θ(√t). For an arm of gap g > 0, whenever t ≥ 2K and g√t ≥ 4Λ, λ_i √t / (2√3
g) − 1 < n_i(t) ≤ max{1, λ_i √t / g}.

Lean: `RootPUCTTrace.count_shrinking_gap` (`JointRootCert/RootPUCT.lean`). The hypothesis t ≥ 2K
was added to the manuscript after the printed statement was shown false
(`LiteralE7.v2shrinking_counterexample`). Main theorem: eq:v2shrinking; companion: the optimal arm
is Ω(t). -/
theorem cor_v2countscales
    {ι : Type u_1}
    [Fintype ι]
    [DecidableEq ι]
    {μ : ι → ℝ}
    {lam : ι → ℝ}
    {n : ℕ → ι → ℕ}
    {sel : ℕ → ι}
    (h : RootPUCTTrace μ lam n sel)
    (hlam : ∀ (i : ι), 0 < lam i)
    {star : ι}
    (hstar : ∀ (j : ι), μ j ≤ μ star)
    {i : ι}
    {g : ℝ}
    (hg : 0 < g)
    (hgi : μ star - μ i = g)
    {t : ℕ}
    (ht : 2 * Fintype.card ι ≤ t)
    (hgt : 4 * ∑ j, lam j ≤ g * √(↑t : ℝ)) :
      lam i * √(↑t : ℝ) / (2 * √3 * g) - 1 < (↑(n t i) : ℝ) ∧ (↑(n t i) : ℝ) ≤ max 1 (lam i * √(↑t : ℝ) / g) :=
  @RootPUCTTrace.count_shrinking_gap ι _ _ μ lam n sel h hlam star hstar i g hg hgi t ht hgt

/-- Companion to Corollary E.5 `cor:v2countscales`: the optimal arm has count Ω(t). Lean:
`RootPUCTTrace.count_optimal_linear` (`JointRootCert/RootPUCT.lean`). -/
theorem cor_v2countscales_optimal
    {ι : Type u_1}
    [Fintype ι]
    [DecidableEq ι]
    {μ : ι → ℝ}
    {lam : ι → ℝ}
    {n : ℕ → ι → ℕ}
    {sel : ℕ → ι}
    (h : RootPUCTTrace μ lam n sel)
    (hlam : ∀ (i : ι), 0 < lam i)
    {star : ι}
    (hstar : ∀ (j : ι), μ j ≤ μ star)
    {i : ι}
    (hi : μ i = μ star)
    {t : ℕ}
    (ht : 2 * Fintype.card ι ≤ t) :
      lam i * (↑t : ℝ) / (4 * √3 * ∑ j, lam j) < (↑(n t i) : ℝ) + 1 :=
  @RootPUCTTrace.count_optimal_linear ι _ _ μ lam n sel h hlam star hstar i hi t ht

/-! ### `lem:v2strict`: Lemma E.7 (Nesting and actual endpoint changes) -/

/-- **Lemma E.7** `lem:v2strict`: Nesting and actual endpoint changes.

Manuscript: The function β_δ(n) strictly decreases for real n ≥ 1. The clipped intervals on these
deterministic tapes are consequently already nested, so the running-intersection operation changes
none of them. Whenever U_C < 1, every subsequent observation of C strictly decreases its upper
endpoint.

Lean: `LiteralE6.v2strict_literal` (`JointRootCert/LiteralE6.lean`). -/
theorem lem_v2strict
    {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2)
    (g : ℝ) :
      StrictAntiOn (rootPuctRadius δ) (Set.Ici 1) ∧
        (∀ (a : Fin 3) (j k : ℕ),
            1 ≤ j →
              j ≤ k →
                0 ≤ rootPuctLo δ (mu3 g a) j ∧
                  rootPuctLo δ (mu3 g a) j ≤ rootPuctLo δ (mu3 g a) k ∧
                    rootPuctHi δ (mu3 g a) k ≤ rootPuctHi δ (mu3 g a) j ∧ rootPuctHi δ (mu3 g a) j ≤ 1) ∧
          (∀ (a : Fin 3), LiteralE6.v2RunLo δ (mu3 g a) 0 = 0 ∧ LiteralE6.v2RunHi δ (mu3 g a) 0 = 1) ∧
            (∀ (a : Fin 3) (n : ℕ),
                1 ≤ n →
                  LiteralE6.v2RunLo δ (mu3 g a) n = rootPuctLo δ (mu3 g a) n ∧
                    LiteralE6.v2RunHi δ (mu3 g a) n = rootPuctHi δ (mu3 g a) n) ∧
              ∀ (j k : ℕ), 1 ≤ j → j < k → rootPuctHi δ (mu3 g 2) j < 1 → rootPuctHi δ (mu3 g 2) k < rootPuctHi δ (mu3 g 2) j :=
  @LiteralE6.v2strict_literal δ hδ0 hδ g

/-! ### `thm:v2horizon`: Theorem E.8 (A sharp certification-horizon scale) -/

/-- **Theorem E.8** `thm:v2horizon`: A sharp certification-horizon scale.

Manuscript: For every fixed δ ∈ (0, 1/2], the three-terminal procedure succeeds finitely for every
g ∈ (0, 1/8], and as g ↓ 0, τ_g = Θ_δ(g⁻² log²(1/g)) and n_C(τ_g) = Θ_δ(g⁻¹ log(1/g)). Its
successful recommendation is A.

Lean: `v2horizon` (`JointRootCert/RootPUCT.lean`). Explicit two-sided bounds with one constant
valid for all g ∈ (0, 1/8]. -/
theorem thm_v2horizon
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ : δ ≤ (1 / 2 : ℝ)) :
      ∃ (C : ℝ),
        (0 : ℝ) < C ∧
          ∀ (g : ℝ),
            (0 : ℝ) < g →
              g ≤ (1 / 8 : ℝ) →
                ∀ (n : ℕ → Fin (3 : ℕ) → ℕ) (sel : ℕ → Fin (3 : ℕ)),
                  RootPUCTTrace (mu3 g) (fun (x : Fin (3 : ℕ)) => (1 : ℝ)) n sel →
                    ∃ (τ : ℕ),
                      (3 : ℕ) ≤ τ ∧
                        Stop3 δ g (n τ) (0 : Fin (3 : ℕ)) ∧
                          (∀ (s : ℕ) (a : Fin (3 : ℕ)), (3 : ℕ) ≤ s → s < τ → ¬Stop3 δ g (n s) a) ∧
                            (∀ (a : Fin (3 : ℕ)), Stop3 δ g (n τ) a → a = (0 : Fin (3 : ℕ))) ∧
                              (16 / 81 : ℝ) * Real.log ((1 : ℝ) / g) ^ (2 : ℕ) / g ^ (2 : ℕ) ≤ (↑τ : ℝ) ∧
                                (↑τ : ℝ) ≤ C * Real.log ((1 : ℝ) / g) ^ (2 : ℕ) / g ^ (2 : ℕ) ∧
                                  Real.log ((1 : ℝ) / g) / ((18 : ℝ) * g) < (↑(n τ (2 : Fin (3 : ℕ))) : ℝ) + (1 : ℝ) ∧
                                    (↑(n τ (2 : Fin (3 : ℕ))) : ℝ) ≤ (2 : ℝ) * √C * Real.log ((1 : ℝ) / g) / g :=
  @v2horizon δ hδ0 hδ

/-! ### `prop:v2postcut`: Proposition E.9 (Uniformly early retirement and changing revisits) -/

/-- **Proposition E.9** `prop:v2postcut`: Uniformly early retirement and changing revisits.

Manuscript: Let t_cut be the first time U_C(t) < max{L_A(t), L_B(t)}. There is a finite T_δ,
independent of g ∈ (0, 1/8], with t_cut ≤ T_δ. For sufficiently small g, t_cut < τ_g, and the
number H_g = n_C(τ_g) − n_C(t_cut) of observations of C after t_cut and through τ_g is Θ_δ(g⁻¹
log(1/g)). Every one of these observations strictly changes U_C.

Lean: `v2postcut` (`JointRootCert/RootPUCT.lean`). -/
theorem prop_v2postcut
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ : δ ≤ (1 / 2 : ℝ)) :
      ∃ (T : ℕ) (g0 : ℝ) (C : ℝ),
        (0 : ℝ) < g0 ∧
          (0 : ℝ) < C ∧
            ∀ (g : ℝ),
              (0 : ℝ) < g →
                g ≤ (1 / 8 : ℝ) →
                  ∀ (n : ℕ → Fin (3 : ℕ) → ℕ) (sel : ℕ → Fin (3 : ℕ)),
                    RootPUCTTrace (mu3 g) (fun (x : Fin (3 : ℕ)) => (1 : ℝ)) n sel →
                      ∃ (tc : ℕ) (τ : ℕ),
                        (3 : ℕ) ≤ tc ∧
                          tc ≤ T ∧
                            Cut3 δ g (n tc) ∧
                              (∀ (s : ℕ), (3 : ℕ) ≤ s → s < tc → ¬Cut3 δ g (n s)) ∧
                                (3 : ℕ) ≤ τ ∧
                                  Stop3 δ g (n τ) (0 : Fin (3 : ℕ)) ∧
                                    (∀ (s : ℕ) (a : Fin (3 : ℕ)), (3 : ℕ) ≤ s → s < τ → ¬Stop3 δ g (n s) a) ∧
                                      (g ≤ g0 → tc < τ) ∧
                                        (16 / 81 : ℝ) * Real.log ((1 : ℝ) / g) ^ (2 : ℕ) / g ^ (2 : ℕ) ≤ (↑τ : ℝ) ∧
                                          (↑τ : ℝ) ≤ C * Real.log ((1 : ℝ) / g) ^ (2 : ℕ) / g ^ (2 : ℕ) ∧
                                            Real.log ((1 : ℝ) / g) / ((18 : ℝ) * g) - (1 : ℝ) - (↑T : ℝ) <
                                                (↑(n τ (2 : Fin (3 : ℕ))) : ℝ) - (↑(n tc (2 : Fin (3 : ℕ))) : ℝ) ∧
                                              (↑(n τ (2 : Fin (3 : ℕ))) : ℝ) - (↑(n tc (2 : Fin (3 : ℕ))) : ℝ) ≤
                                                  (2 : ℝ) * √C * Real.log ((1 : ℝ) / g) / g ∧
                                                ∀ (s : ℕ),
                                                  tc ≤ s →
                                                    sel s = (2 : Fin (3 : ℕ)) →
                                                      U3 δ g (n (s + (1 : ℕ))) (2 : Fin (3 : ℕ)) <
                                                        U3 δ g (n s) (2 : Fin (3 : ℕ)) :=
  @v2postcut δ hδ0 hδ

/-! ### `thm:v2separation`: Theorem E.10 (Root-PUCT work separation from uninformative initialization) -/

/-- **Theorem E.10** `thm:v2separation`: Root-PUCT work separation from uninformative initialization.

Manuscript: Fix δ ∈ (0, 1/2] and α ∈ (0, 1/2). For all sufficiently large m, set g_m = m^{−α} and
ε_m = g_m/2. The two specified monitors and the root-PUCT controller, starting with [0,1] at all
three terminals, have identical sampled paths, observations, leaders and stopping times, and
recommend A. Moreover τ_m = Θ(m^{2α} log² m), H_m = Θ(m^α log m), W_selective = Θ(m) and W_full =
Θ(m^{1+α} log m), in the unit-cost endpoint-operation model.

Lean: `LiteralF5.v2separation_full` (`JointRootCert/LiteralF5.lean`). Work is computed by the
implemented monitors; build, release and query costs are charged per element. -/
theorem thm_v2separation
    {δ : ℝ}
    {α : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2)
    (hα0 : 0 < α)
    (hα : α < 1 / 2) :
      ∃ m0 T cτ Cτ cH CH C1 cF CF,
        0 < cτ ∧
          0 < cH ∧
            0 < C1 ∧
              0 < cF ∧
                ∀ (m : ℕ),
                  m0 ≤ m →
                    ∀ (g : ℝ),
                      g = (↑m : ℝ) ^ (-α) →
                        ∀ (rule : ℕ → ℕ → Bool) (pick : LiteralE5.Hist → Fin 3),
                          LiteralE5.IsPuctPick pick →
                            ∃ tc τ,
                              tc ≤ T ∧
                                LiteralE5.SeparationBounds m δ g rule pick tc τ cτ Cτ cH CH C1 cF CF
                                    ((↑m : ℝ) ^ (2 * α) * Real.log (↑m : ℝ) ^ 2) ((↑m : ℝ) ^ α * Real.log (↑m : ℝ))
                                    ((↑m : ℝ) ^ (1 + α) * Real.log (↑m : ℝ)) ∧
                                  (∀ (t : ℕ),
                                      LiteralE5.ctlMon true m δ (g / 2) (LiteralE5.closedLoop m g rule pick true δ t) =
                                        LiteralE5.ctlMon false m δ (g / 2) (LiteralE5.closedLoop m g rule pick false δ t)) ∧
                                    ∀ (t : ℕ),
                                      (LiteralE5.ctlMon true m δ (g / 2)
                                              (LiteralE5.closedLoop m g rule pick true δ t)).out.leaders =
                                        (LiteralE5.ctlMon false m δ (g / 2)
                                              (LiteralE5.closedLoop m g rule pick false δ t)).out.leaders :=
  @LiteralF5.v2separation_full δ α hδ0 hδ hα0 hα

/-! ### `cor:v2quarter`: Corollary E.11 (One explicit polynomial instance) -/

/-- **Corollary E.11** `cor:v2quarter`: One explicit polynomial instance.

Manuscript: For g_m = m^{−1/4} and fixed δ, τ_m = Θ(m^{1/2} log² m), W_selective = Θ(m), W_full =
Θ(m^{5/4} log m). The work ratio is Θ(m^{1/4} log m) although the observation trajectories and
successful decisions coincide exactly.

Lean: `LiteralF5.v2quarter_full` (`JointRootCert/LiteralF5.lean`). -/
theorem cor_v2quarter
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ : δ ≤ (1 / 2 : ℝ)) :
      ∃ (m0 : ℕ) (T : ℕ) (cτ : ℝ) (Cτ : ℝ) (cH : ℝ) (CH : ℝ) (C1 : ℝ) (cF : ℝ) (CF : ℝ) (cR : ℝ) (CR : ℝ),
        (0 : ℝ) < cτ ∧
          (0 : ℝ) < cH ∧
            (0 : ℝ) < C1 ∧
              (0 : ℝ) < cF ∧
                (0 : ℝ) < cR ∧
                  ∀ (m : ℕ),
                    m0 ≤ m →
                      ∀ (g : ℝ),
                        g = (↑m : ℝ) ^ (-(1 / 4 : ℝ)) →
                          ∀ (rule : ℕ → ℕ → Bool) (pick : LiteralE5.Hist → Fin (3 : ℕ)),
                            LiteralE5.IsPuctPick pick →
                              ∃ (tc : ℕ) (τ : ℕ),
                                tc ≤ T ∧
                                  LiteralE5.SeparationBounds m δ g rule pick tc τ cτ Cτ cH CH C1 cF CF
                                      ((↑m : ℝ) ^ (1 / 2 : ℝ) * Real.log (↑m : ℝ) ^ (2 : ℕ))
                                      ((↑m : ℝ) ^ (1 / 4 : ℝ) * Real.log (↑m : ℝ))
                                      ((↑m : ℝ) ^ (5 / 4 : ℝ) * Real.log (↑m : ℝ)) ∧
                                    cR * ((↑m : ℝ) ^ (1 / 4 : ℝ) * Real.log (↑m : ℝ)) ≤
                                        (↑(LiteralE5.histWork false m δ (g / (2 : ℝ)) rule
                                                (LiteralE5.freeH m g rule pick τ)) :
                                            ℝ) /
                                          (↑(LiteralE5.histWork true m δ (g / (2 : ℝ)) rule
                                                (LiteralE5.freeH m g rule pick τ)) :
                                            ℝ) ∧
                                      (↑(LiteralE5.histWork false m δ (g / (2 : ℝ)) rule (LiteralE5.freeH m g rule pick τ)) :
                                              ℝ) /
                                            (↑(LiteralE5.histWork true m δ (g / (2 : ℝ)) rule
                                                  (LiteralE5.freeH m g rule pick τ)) :
                                              ℝ) ≤
                                          CR * ((↑m : ℝ) ^ (1 / 4 : ℝ) * Real.log (↑m : ℝ)) ∧
                                        (∀ (t : ℕ),
                                            LiteralE5.ctlMon true m δ (g / (2 : ℝ))
                                                (LiteralE5.closedLoop m g rule pick true δ t) =
                                              LiteralE5.ctlMon false m δ (g / (2 : ℝ))
                                                (LiteralE5.closedLoop m g rule pick false δ t)) ∧
                                          ∀ (t : ℕ),
                                            MonOut.leaders
                                                (LiteralE5.Iface.out
                                                  (LiteralE5.ctlMon true m δ (g / (2 : ℝ))
                                                    (LiteralE5.closedLoop m g rule pick true δ t))) =
                                              MonOut.leaders
                                                (LiteralE5.Iface.out
                                                  (LiteralE5.ctlMon false m δ (g / (2 : ℝ))
                                                    (LiteralE5.closedLoop m g rule pick false δ t))) :=
  @LiteralF5.v2quarter_full δ hδ0 hδ

/-! ### `prop:v2escape`: Proposition E.12 (The family does not lower-bound all numerical oracles) -/

/-- **Proposition E.12** `prop:v2escape`: The family does not lower-bound all numerical oracles.

Manuscript: The same graph admits an implementation that preserves even the complete root-action
interval vector with O(m + τ_m) monitor work, before charging sampling-path traversal. Therefore
the full-monitor lower bound of Theorem E.10 cannot be promoted to a lower bound for every
exact-interval implementation.

Lean: `LiteralF3.v2escape_literal` (`JointRootCert/LiteralF3.lean`). The alias monitor as an
executed costed program, with honest cost floors for the comparison. -/
theorem prop_v2escape
    {δ : ℝ}
    {α : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2)
    (hα0 : 0 < α)
    (hα : α < 1 / 2) :
      ∃ m0 C cF,
        0 < C ∧
          0 < cF ∧
            ∀ (m : ℕ),
              m0 ≤ m →
                ∀ (g : ℝ),
                  g = (↑m : ℝ) ^ (-α) →
                    ∀ (rule : ℕ → ℕ → Bool) (pick : LiteralE5.Hist → Fin 3),
                      LiteralE5.IsPuctPick pick →
                        ∃ τ,
                          LiteralF3.StopsAt m g rule pick δ τ ∧
                            cF * ((↑m : ℝ) ^ (1 + α) * Real.log (↑m : ℝ)) ≤
                                (↑(LiteralE5.histWork false m δ (g / 2) rule (LiteralE5.freeH m g rule pick τ)) : ℝ) ∧
                              LiteralF3.ExactOn (LiteralF3.aliasImpl (monRootCirc m)) (monRootCirc m) LiteralF3.box01
                                  (LiteralF3.runUpd m g rule pick δ) τ ∧
                                (∀ k ≤ τ,
                                    ∀ (a : Fin 3),
                                      ((LiteralF3.aliasImpl (monRootCirc m)).query
                                              (LiteralF3.implState (LiteralF3.aliasImpl (monRootCirc m)) LiteralF3.box01
                                                (LiteralF3.runUpd m g rule pick δ) k)).1
                                          a =
                                        some
                                          ((monRun false (monRootCirc m)
                                                  (LiteralE5.histSeq δ (LiteralE5.freeH m g rule pick τ)) k).lo
                                              (LiteralE5.histSeq δ (LiteralE5.freeH m g rule pick τ) k) a,
                                            (monRun false (monRootCirc m)
                                                  (LiteralE5.histSeq δ (LiteralE5.freeH m g rule pick τ)) k).hi
                                              (LiteralE5.histSeq δ (LiteralE5.freeH m g rule pick τ) k) a)) ∧
                                  LiteralF3.implWork (LiteralF3.aliasImpl (monRootCirc m)) LiteralF3.box01
                                        (LiteralF3.runUpd m g rule pick δ) τ =
                                      3 * m + 4 * τ + 4 ∧
                                    (↑(LiteralF3.implHistWork m g rule pick (LiteralF3.aliasImpl (monRootCirc m)) δ τ) : ℝ) ≤
                                      C * (↑m : ℝ) :=
  @LiteralF3.v2escape_literal δ α hδ0 hδ hα0 hα

/-! ### `thm:puct-noisy-main`: Theorem E.14 (Support-sensitive certification under recursive PUCT) -/

/-- **Theorem E.14** `thm:puct-noisy-main`: Support-sensitive certification under recursive PUCT.

Manuscript: For a fixed finite all-MAX DAG of depth H, stationary bounded terminal observations,
full terminal rollouts and fixed strictly positive PUCT priors, there are explicit constants c_* >
0 and t_* < ∞ such that every terminal receives at least c_* t^{2^{−H}} observations for t ≥ t_*,
on every sample path. With Γ = max_{a : V(a) = μ_*} (μ_* − max_{z ∉ S(a)} μ_z): a root support
equal to Z is certifiable without observations; otherwise, whenever ε + Γ > 0, the exact-regret
monitor with nested Hoeffding intervals certifies an ε-optimal action by any t ≥ t_* satisfying
eq:puct-noisy-condition, with probability at least 1 − δ.

Lean: `LiteralE6.puct_noisy_main_literal` (`JointRootCert/LiteralE6.lean`). Supports come from the
graph; the stopping monitor enters through its specification; stated as failure probability at
most δ/2. -/
theorem thm_puct_noisy_main
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {V : Type u_2}
    {E : Type u_3}
    [Fintype E]
    {Ω : Type u_4}
    [MeasurableSpace Ω]
    {src : E → V}
    {tgt : E → V}
    {root : V}
    {lam : E → ℝ}
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (vis : Ω → ℕ → V → Prop)
    (ch : Ω → ℕ → V → E)
    (Q : Ω → E → ℕ → ℝ)
    (hrun : ∀ (ω : Ω), PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω))
    (term : Z → V)
    (rk : V → ℕ)
    (hrk : ∀ (e : E), rk (tgt e) < rk (src e))
    (hsink : ∀ (v : V), outEdges src v = ∅ → ∃ (z : Z), term z = v)
    (path : Z → List E)
    (hpath : ∀ (z : Z), IsPath src tgt (path z) root (term z))
    (H : ℕ)
    (hH : ∀ (z : Z), List.length (path z) ≤ H)
    (μ : Z → ℝ)
    (hμ : ∀ (z : Z), μ z ∈ Set.Icc (0 : ℝ) (1 : ℝ))
    (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ (z : Z) (k : ℕ), AEMeasurable (X z k) P)
    (hbdd : ∀ (z : Z) (k : ℕ), ∀ᵐ (ω : Ω) ∂P, X z k ω ∈ Set.Icc (0 : ℝ) (1 : ℝ))
    (hmean : ∀ (z : Z) (k : ℕ), ∫ (ω : Ω), X z k ω ∂P = μ z)
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ1 : δ ≤ (1 : ℝ))
    (ε : ℝ)
    (hε : (0 : ℝ) ≤ ε)
    (τ : Ω → ℕ)
    (rec : Ω → LiteralE6.RootAct src root)
    (hmon : ∀ (ω : Ω) (s : ℕ),
  (∃ (a : LiteralE6.RootAct src root),
      (exactCert (LiteralE6.rootSupp src tgt root term a) (LiteralE6.rootSupp_nonempty term rk hrk hsink a)
          (fun (z : Z) =>
            runLower (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
              (visitCount (vis ω) (term z) s))
          fun (z : Z) =>
          runUpper (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
            (visitCount (vis ω) (term z) s)) ≤
        ε) →
    τ ω ≤ s ∧
      (exactCert (LiteralE6.rootSupp src tgt root term (rec ω)) (LiteralE6.rootSupp_nonempty term rk hrk hsink (rec ω))
          (fun (z : Z) =>
            runLower (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
              (visitCount (vis ω) (term z) (τ ω)))
          fun (z : Z) =>
          runUpper (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
            (visitCount (vis ω) (term z) (τ ω))) ≤
        ε) :
      ((0 : ℝ) < puctCstar lam path ∧
          ∀ (ω : Ω) (t : ℕ),
            puctTstar src lam path ≤ t →
              ∀ (z : Z), puctCstar lam path * (↑t : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ H) ≤ (↑(visitCount (vis ω) (term z) t) : ℝ)) ∧
        ((∃ (a : LiteralE6.RootAct src root), LiteralE6.rootSupp src tgt root term a = Finset.univ) →
            ∀ (ω : Ω),
              τ ω = (0 : ℕ) ∧
                (exactCert (LiteralE6.rootSupp src tgt root term (rec ω))
                      (LiteralE6.rootSupp_nonempty term rk hrk hsink (rec ω)) (fun (x : Z) => (0 : ℝ)) fun (x : Z) =>
                      (1 : ℝ)) ≤
                    ε ∧
                  regret (LiteralE6.rootSupp src tgt root term (rec ω))
                      (LiteralE6.rootSupp_nonempty term rk hrk hsink (rec ω)) μ ≤
                    ε) ∧
          ∀ (hpr : ∀ (a : LiteralE6.RootAct src root), Finset.Nonempty (LiteralE6.rootSupp src tgt root term a)ᶜ) (Γ : ℝ),
            IsGreatest
                ((fun (a : LiteralE6.RootAct src root) => outsideMargin (LiteralE6.rootSupp src tgt root term a) (hpr a) μ) ''
                  {a : LiteralE6.RootAct src root |
                    val (LiteralE6.rootSupp src tgt root term a) (LiteralE6.rootSupp_nonempty term rk hrk hsink a) μ =
                      gmax μ})
                Γ →
              (0 : ℝ) < ε + Γ →
                ∀ (t : ℕ),
                  puctTstar src lam path ≤ t →
                    (8 : ℝ) / (ε + Γ) ^ (2 : ℕ) *
                          Real.log ((4 : ℝ) * (↑(Fintype.card Z) : ℝ) * ((↑t : ℝ) + (1 : ℝ)) ^ (2 : ℕ) / δ) ≤
                        puctCstar lam path * (↑t : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ H) →
                      (P : Set Ω → ENNReal)
                          {ω : Ω |
                            ¬(τ ω ≤ t ∧
                                regret (LiteralE6.rootSupp src tgt root term (rec ω))
                                    (LiteralE6.rootSupp_nonempty term rk hrk hsink (rec ω)) μ ≤
                                  ε)} ≤
                        ENNReal.ofReal (δ / (2 : ℝ)) :=
  @LiteralE6.puct_noisy_main_literal Z _ _ _ V E _ Ω _ src tgt root lam P _ vis ch Q hrun term rk hrk hsink path hpath H hH μ hμ X hmeas hbdd hmean hindep δ hδ0 hδ1 ε hε τ rec hmon

/-! ### `thm:v35local`: Theorem E.15 (Uniform local PUCT revisit bound under changing values) -/

/-- **Theorem E.15** `thm:v35local`: Uniform local PUCT revisit bound under changing values.

Manuscript: Let k ≥ 1 actions have weights λ_i > 0 and selection rule i_n ∈ argmax_i (Q_i(n) + λ_i
√n / (1 + N_i(n))) with Q_i(n) ∈ [0,1] and Σ_i N_i(n) = n. With α_i = λ_i/(8√2) and T_0 = ⌈max{16,
128/λ_*², 16Λ²}⌉, for every realized bounded-value sequence, every t ≥ T_0 and every action i,
N_i(t) ≥ α_i √t.

Lean: `local_puct_revisit` (`JointRootCert/RecursivePUCT.lean`). -/
theorem thm_v35local
    {ι : Type u_1}
    [Fintype ι]
    (lam : ι → ℝ)
    (hlam : ∀ (j : ι), 0 < lam j)
    (sel : ℕ → ι)
    (Q : ι → ℕ → ℝ)
    (hQ : ∀ (n : ℕ) (j : ι), 0 ≤ Q j n ∧ Q j n ≤ 1)
    (hrule : ∀ (n : ℕ) (j : ι),
  Q j n + lam j * √(↑n : ℝ) / (1 + (↑(pullCount sel j n) : ℝ)) ≤
    Q (sel n) n + lam (sel n) * √(↑n : ℝ) / (1 + (↑(pullCount sel (sel n) n) : ℝ)))
    (t : ℕ)
    (ht : puctThreshold Finset.univ lam ≤ t)
    (i : ι) :
      lam i / (8 * √2) * √(↑t : ℝ) ≤ (↑(pullCount sel i t) : ℝ) :=
  @local_puct_revisit ι _ lam hlam sel Q hQ hrule t ht i

/-! ### `thm:v35dag`: Theorem E.17 (Pathwise terminal coverage under recursive local PUCT) -/

/-- **Theorem E.17** `thm:v35dag`: Pathwise terminal coverage under recursive local PUCT.

Manuscript: Under the fixed-DAG PUCT contract, for every outcome sequence and every integer t ≥
t_*, the number n_z(t) of samples of every terminal z satisfies n_z(t) ≥ C_{z,d_z} t^{2^{−d_z}} ≥
c_* t^{2^{−H}}. In particular every terminal is sampled infinitely often on every infinite
continuation of the run.

Lean: `puct_terminal_coverage` (`JointRootCert/RecursivePUCT.lean`). -/
theorem thm_v35dag
    {V : Type u_1}
    {E : Type u_2}
    [Fintype E]
    {src : E → V}
    {tgt : E → V}
    {root : V}
    {lam : E → ℝ}
    {vis : ℕ → V → Prop}
    {ch : ℕ → V → E}
    {Q : E → ℕ → ℝ}
    {Zt : Type u_3}
    [Fintype Zt]
    [Nonempty Zt]
    (h : PUCTRun src tgt root lam vis ch Q)
    (term : Zt → V)
    (P : Zt → List E)
    (hP : ∀ (z : Zt), IsPath src tgt (P z) root (term z))
    (H : ℕ)
    (hH : ∀ (z : Zt), List.length (P z) ≤ H)
    (t : ℕ)
    (ht : puctTstar src lam P ≤ t)
    (z : Zt) :
      pathConst lam (P z) (1 : ℝ) * (↑t : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ List.length (P z)) ≤ (↑(visitCount vis (term z) t) : ℝ) ∧
        puctCstar lam P * (↑t : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ H) ≤
          pathConst lam (P z) (1 : ℝ) * (↑t : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ List.length (P z)) :=
  @puct_terminal_coverage V E _ src tgt root lam vis ch Q Zt _ _ h term P hP H hH t ht z

/-! ### `lem:v35width`: Lemma E.19 (Anytime coverage and a usable width bound) -/

/-- **Lemma E.19** `lem:v35width`: Anytime coverage and a usable width bound.

Manuscript: With probability at least 1 − δ/2, simultaneously for every terminal z and every count
n ≥ 1, μ_z ∈ I_{z,n}; on this event the failure flag never fires. If at time t every terminal has
n_z(t) ≥ m > 0, then every running interval obeys μ_z − 2b_t ≤ l_z(t) ≤ μ_z ≤ u_z(t) ≤ μ_z + 2b_t
with b_t = √(log(4M(t+1)²/δ)/(2m)).

Lean: `hoeffding_tape_coverage` (`JointRootCert/RecursivePUCT.lean`). Main theorem: coverage (from
Mathlib's Hoeffding inequality); companion: the width bound. -/
theorem lem_v35width
    {Ω : Type u_1}
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    {Z : Type u_2}
    [Fintype Z]
    [Nonempty Z]
    (X : Z → ℕ → Ω → ℝ)
    (μ : Z → ℝ)
    (hmeas : ∀ (z : Z) (k : ℕ), AEMeasurable (X z k) P)
    (hbdd : ∀ (z : Z) (k : ℕ), ∀ᵐ (ω : Ω) ∂P, X z k ω ∈ Set.Icc 0 1)
    (hmean : ∀ (z : Z) (k : ℕ), ∫ (ω : Ω), X z k ω ∂P = μ z)
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
      (P : Set Ω → ENNReal)
          {ω | ∃ z k, 1 ≤ k ∧ puctRadius (↑(Fintype.card Z) : ℝ) δ k < |(↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω - μ z|} ≤
        ENNReal.ofReal (δ / 2) :=
  @hoeffding_tape_coverage Ω _ P _ Z _ _ X μ hmeas hbdd hmean hindep δ hδ0 hδ1

/-- Companion to Lemma E.19 `lem:v35width`: the width bound on the running box. Lean:
`running_box_width_bt` (`JointRootCert/RecursivePUCT.lean`). -/
theorem lem_v35width_bound
    {c : ℕ → ℝ}
    {μ : ℝ}
    {M : ℝ}
    {δ : ℝ}
    {m : ℝ}
    (hμ : μ ∈ Set.Icc 0 1)
    (hM : 1 ≤ M)
    (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1)
    (hm : 0 < m)
    (hcov : ∀ (k : ℕ), 1 ≤ k → |c k - μ| ≤ puctRadius M δ k)
    {n : ℕ}
    {t : ℕ}
    (hmn : m ≤ (↑n : ℝ))
    (hnt : n ≤ t) :
      μ - 2 * puctB M δ m t ≤ runLower c (puctRadius M δ) n ∧
        runLower c (puctRadius M δ) n ≤ μ ∧
          μ ≤ runUpper c (puctRadius M δ) n ∧ runUpper c (puctRadius M δ) n ≤ μ + 2 * puctB M δ m t :=
  @running_box_width_bt c μ M δ m hμ hM hδ0 hδ1 hm hcov n t hmn hnt

/-! ### `thm:v35horizon`: Theorem E.20 (High-probability on-policy PUCT certification horizon) -/

/-- **Theorem E.20** `thm:v35horizon`: High-probability on-policy PUCT certification horizon.

Manuscript: Fix ε > 0. Let τ be the first successful query of the exact minimum robust-regret
oracle along the recursively selected PUCT trajectory. For any integer t with t ≥ t_* and c_*
t^{2^{−H}} ≥ (8/ε²) log(4M(t+1)²/δ), P(τ ≤ t, Reg(â_τ) ≤ ε) ≥ 1 − δ/2. A finite such t always
exists.

Lean: `puct_horizon_full` (`JointRootCert/RecursivePUCT.lean`). The stopping monitor enters
through its specification. -/
theorem thm_v35horizon
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {V : Type u_2}
    {E : Type u_3}
    [Fintype E]
    {Ω : Type u_4}
    [MeasurableSpace Ω]
    {A : Type u_5}
    {src : E → V}
    {tgt : E → V}
    {root : V}
    {lam : E → ℝ}
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (vis : Ω → ℕ → V → Prop)
    (ch : Ω → ℕ → V → E)
    (Q : Ω → E → ℕ → ℝ)
    (hrun : ∀ (ω : Ω), PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω))
    (term : Z → V)
    (path : Z → List E)
    (hpath : ∀ (z : Z), IsPath src tgt (path z) root (term z))
    (H : ℕ)
    (hH : ∀ (z : Z), List.length (path z) ≤ H)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), Finset.Nonempty (supp a))
    (hreach : ∀ (z : Z), ∃ (a : A), z ∈ supp a)
    (μ : Z → ℝ)
    (hμ : ∀ (z : Z), μ z ∈ Set.Icc (0 : ℝ) (1 : ℝ))
    (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ (z : Z) (k : ℕ), AEMeasurable (X z k) P)
    (hbdd : ∀ (z : Z) (k : ℕ), ∀ᵐ (ω : Ω) ∂P, X z k ω ∈ Set.Icc (0 : ℝ) (1 : ℝ))
    (hmean : ∀ (z : Z) (k : ℕ), ∫ (ω : Ω), X z k ω ∂P = μ z)
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ1 : δ ≤ (1 : ℝ))
    (ε : ℝ)
    (τ : Ω → ℕ)
    (rec : Ω → A)
    (hmon : ∀ (ω : Ω) (s : ℕ),
  (∃ (a : A),
      (exactCert (supp a) (hne a)
          (fun (z : Z) =>
            runLower (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
              (visitCount (vis ω) (term z) s))
          fun (z : Z) =>
          runUpper (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
            (visitCount (vis ω) (term z) s)) ≤
        ε) →
    τ ω ≤ s ∧
      (exactCert (supp (rec ω)) (hne (rec ω))
          (fun (z : Z) =>
            runLower (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
              (visitCount (vis ω) (term z) (τ ω)))
          fun (z : Z) =>
          runUpper (fun (k : ℕ) => (↑k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X z i ω) (puctRadius (↑(Fintype.card Z) : ℝ) δ)
            (visitCount (vis ω) (term z) (τ ω))) ≤
        ε)
    (t : ℕ)
    (ht : puctTstar src lam path ≤ t)
    (hε : (0 : ℝ) < ε)
    (hcond : (8 : ℝ) / ε ^ (2 : ℕ) * Real.log ((4 : ℝ) * (↑(Fintype.card Z) : ℝ) * ((↑t : ℝ) + (1 : ℝ)) ^ (2 : ℕ) / δ) ≤
  puctCstar lam path * (↑t : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ H)) :
      (P : Set Ω → ENNReal) {ω : Ω | ¬(τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤ ENNReal.ofReal (δ / (2 : ℝ)) :=
  @puct_horizon_full Z _ _ _ V E _ Ω _ A src tgt root lam P _ vis ch Q hrun term path hpath H hH supp hne hreach μ hμ X hmeas hbdd hmean hindep δ hδ0 hδ1 ε τ rec hmon t ht hε hcond

/-! ### `cor:v35poly`: Corollary E.21 (Polynomial accuracy dependence at fixed depth) -/

/-- **Corollary E.21** `cor:v35poly`: Polynomial accuracy dependence at fixed depth.

Manuscript: For a fixed finite graph, fixed positive priors and fixed δ, the sufficient
continuation horizon is polynomial in ε⁻¹ for 0 < ε ≤ 1/e (with a logarithmic factor), with crude
exponent 2^{H+1} up to logarithms. If a different exact implementation of the minimum
robust-regret oracle is used, Theorem K.1 transfers the same certified PUCT sampling and stopping
sequence, provided the controller sees identical replies.

Lean: `LiteralE3.puct_controller_horizon` (`JointRootCert/LiteralE3.lean`). Main theorem: the
horizon for a controller; companion: the oracle-substitution clause. -/
theorem cor_v35poly
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {V : Type u_2}
    {E : Type u_3}
    [Fintype E]
    {Ω : Type u_4}
    [MeasurableSpace Ω]
    {A : Type u_5}
    [Nonempty A]
    {G : LiteralE3.Search V E Z}
    {term : Z → V}
    (hG : G.Valid term)
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (tie : Ω → Finset E → E)
    (path : Z → List E)
    (hpath : ∀ (z : Z), IsPath G.src G.tgt (path z) G.root (term z))
    (H : ℕ)
    (hH : ∀ (z : Z), (path z).length ≤ H)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hreach : ∀ (z : Z), ∃ a, z ∈ supp a)
    (μ : Z → ℝ)
    (hμ : ∀ (z : Z), μ z ∈ Set.Icc 0 1)
    (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ (z : Z) (k : ℕ), AEMeasurable (X z k) P)
    (hbdd : ∀ (z : Z) (k : ℕ), ∀ᵐ (ω : Ω) ∂P, X z k ω ∈ Set.Icc 0 1)
    (hmean : ∀ (z : Z) (k : ℕ), ∫ (ω : Ω), X z k ω ∂P = μ z)
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1)
    (ε : ℝ)
    (t : ℕ)
    (ht : puctTstar G.src G.lam path ≤ t)
    (hε : 0 < ε)
    (hε1 : ε ≤ Real.exp (-1))
    (hpoly : polyD (puctCstar G.lam path) (↑(Fintype.card Z) : ℝ) δ H ^ 2 ^ H * (1 / ε) ^ 2 ^ (H + 1) * Real.log (1 / ε) ^ 2 ^ H ≤
  (↑t : ℝ)) :
      (P : Set Ω → ENNReal)
          {ω |
            ¬((G.tau ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω) fun z k =>
                    X z k ω) ≤
                  t ∧
                regret
                    (supp
                      (G.rcm ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω)
                        fun z k => X z k ω))
                    (hne
                      (G.rcm ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω)
                        fun z k => X z k ω))
                    μ ≤
                  ε)} ≤
        ENNReal.ofReal (δ / 2) :=
  @LiteralE3.puct_controller_horizon Z _ _ _ V E _ Ω _ A _ G term hG P _ tie path hpath H hH supp hne hreach μ hμ X hmeas hbdd hmean hindep δ hδ0 hδ1 ε t ht hε hε1 hpoly

/-- Companion to Corollary E.21 `cor:v35poly`: oracle substitution. Lean:
`LiteralE3.v35poly_oracle_substitution` (`JointRootCert/LiteralE3.lean`). -/
theorem cor_v35poly_substitution
    {Z : Type u_1}
    [Fintype Z]
    [DecidableEq Z]
    [Nonempty Z]
    {V : Type u_2}
    {E : Type u_3}
    [Fintype E]
    {Ω : Type u_4}
    [MeasurableSpace Ω]
    {A : Type u_5}
    [Nonempty A]
    {G : LiteralE3.Search V E Z}
    {term : Z → V}
    (hG : G.Valid term)
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (tie : Ω → Finset E → E)
    (path : Z → List E)
    (hpath : ∀ (z : Z), IsPath G.src G.tgt (path z) G.root (term z))
    (H : ℕ)
    (hH : ∀ (z : Z), (path z).length ≤ H)
    (supp : A → Finset Z)
    (hne : ∀ (a : A), (supp a).Nonempty)
    (hreach : ∀ (z : Z), ∃ a, z ∈ supp a)
    (μ : Z → ℝ)
    (hμ : ∀ (z : Z), μ z ∈ Set.Icc 0 1)
    (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ (z : Z) (k : ℕ), AEMeasurable (X z k) P)
    (hbdd : ∀ (z : Z) (k : ℕ), ∀ᵐ (ω : Ω) ∂P, X z k ω ∈ Set.Icc 0 1)
    (hmean : ∀ (z : Z) (k : ℕ), ∫ (ω : Ω), X z k ω ∂P = μ z)
    (hindep : ∀ (z : Z), ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1)
    (ε : ℝ)
    (t : ℕ)
    (ht : puctTstar G.src G.lam path ≤ t)
    (hε : 0 < ε)
    (hε1 : ε ≤ Real.exp (-1))
    (hpoly : polyD (puctCstar G.lam path) (↑(Fintype.card Z) : ℝ) δ H ^ 2 ^ H * (1 / ε) ^ 2 ^ (H + 1) * Real.log (1 / ε) ^ 2 ^ H ≤
  (↑t : ℝ))
    {σ' : Type u_6}
    (J : Representation.OracleImpl σ' (Z × ℝ) (A → ℝ))
    (hJ : ∀ (ω : Ω) (n : ℕ),
  J.answer (G.hist (tie ω) (fun z k => X z k ω) n) =
    (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer
      (G.hist (tie ω) (fun z k => X z k ω) n)) :
      (∀ (ω : Ω) (n : ℕ),
          LiteralE3.ctrlRun J.answer (G.controller ε A) (tie ω) (fun z k => X z k ω) n =
              LiteralE3.ctrlRun (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer
                (G.controller ε A) (tie ω) (fun z k => X z k ω) n ∧
            J.answer (LiteralE3.ctrlRun J.answer (G.controller ε A) (tie ω) (fun z k => X z k ω) n) =
              (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer
                (LiteralE3.ctrlRun (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer
                  (G.controller ε A) (tie ω) (fun z k => X z k ω) n)) ∧
        (∀ (ω : Ω),
            ((G.tau ε J.answer (tie ω) fun z k => X z k ω) =
                G.tau ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω) fun z k =>
                  X z k ω) ∧
              (G.rcm ε J.answer (tie ω) fun z k => X z k ω) =
                G.rcm ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω) fun z k =>
                  X z k ω) ∧
          (P : Set Ω → ENNReal)
                {ω |
                  ¬((G.tau ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω) fun z k =>
                          X z k ω) ≤
                        t ∧
                      regret
                          (supp
                            (G.rcm ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω)
                              fun z k => X z k ω))
                          (hne
                            (G.rcm ε (LiteralE3.refMonitor supp hne (puctRadius (↑(Fintype.card Z) : ℝ) δ)).answer (tie ω)
                              fun z k => X z k ω))
                          μ ≤
                        ε)} ≤
              ENNReal.ofReal (δ / 2) ∧
            (P : Set Ω → ENNReal)
                {ω |
                  ¬((G.tau ε J.answer (tie ω) fun z k => X z k ω) ≤ t ∧
                      regret (supp (G.rcm ε J.answer (tie ω) fun z k => X z k ω))
                          (hne (G.rcm ε J.answer (tie ω) fun z k => X z k ω)) μ ≤
                        ε)} ≤
              ENNReal.ofReal (δ / 2) :=
  @LiteralE3.v35poly_oracle_substitution Z _ _ _ V E _ Ω _ A _ G term hG P _ tie path hpath H hH supp hne hreach μ hμ X hmeas hbdd hmean hindep δ hδ0 hδ1 ε t ht hε hε1 hpoly σ' J hJ

/-! ### `prop:v35rootrates`: Proposition E.22 (Positive-variance root PUCT: almost-sure square-root counts) -/

/-- **Proposition E.22** `prop:v35rootrates`: Positive-variance root PUCT: almost-sure square-root counts.

Manuscript: Let K root actions have independent bounded i.i.d. reward tapes with means μ_i, Q_i(n)
the empirical mean, and the fixed-positive-prior PUCT rule. Then every action is sampled
infinitely often on every outcome sequence. On a probability-one event, each action with positive
gap satisfies N_i(t) = Θ(√t); if the best mean is unique, its action receives t − O(√t) samples
almost surely.

Lean: `LiteralE6.v35rootrates_literal` (`JointRootCert/LiteralE6.lean`). -/
theorem prop_v35rootrates
    {ι : Type u_1}
    [Fintype ι]
    {Ω : Type u_2}
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (lam : ι → ℝ)
    (hlam : ∀ (j : ι), 0 < lam j)
    (X : ι → ℕ → Ω → ℝ)
    (hbdd : ∀ (i : ι) (k : ℕ) (ω : Ω), X i k ω ∈ Set.Icc 0 1)
    (hindep : ∀ (i : ι), Pairwise (Function.onFun (fun f g => ProbabilityTheory.IndepFun f g P) (X i)))
    (hident : ∀ (i : ι) (k : ℕ), ProbabilityTheory.IdentDistrib (X i k) (X i 0) P P)
    (sel : Ω → ℕ → ι)
    (Q : Ω → ι → ℕ → ℝ)
    (hQ0 : ∀ (ω : Ω) (n : ℕ) (j : ι), pullCount (sel ω) j n = 0 → 0 ≤ Q ω j n ∧ Q ω j n ≤ 1)
    (hQmean : ∀ (ω : Ω) (n : ℕ) (j : ι),
  1 ≤ pullCount (sel ω) j n →
    Q ω j n = (↑(pullCount (sel ω) j n) : ℝ)⁻¹ * ∑ k ∈ Finset.range (pullCount (sel ω) j n), X j k ω)
    (hrule : ∀ (ω : Ω) (n : ℕ) (j : ι),
  Q ω j n + lam j * √(↑n : ℝ) / (1 + (↑(pullCount (sel ω) j n) : ℝ)) ≤
    Q ω (sel ω n) n + lam (sel ω n) * √(↑n : ℝ) / (1 + (↑(pullCount (sel ω) (sel ω n) n) : ℝ))) :
      (∀ (ω : Ω) (i : ι) (B : ℝ), ∃ t0, ∀ (t : ℕ), t0 ≤ t → B ≤ (↑(pullCount (sel ω) i t) : ℝ)) ∧
        ∀ᵐ (ω : Ω) ∂P,
          (∀ (i : ι),
              (∃ j, ∫ (ω' : Ω), X i 0 ω' ∂P < ∫ (ω' : Ω), X j 0 ω' ∂P) →
                0 < lam i / (8 * √2) ∧
                  ∃ C,
                    ∀ (t : ℕ),
                      puctThreshold Finset.univ lam ≤ t →
                        lam i / (8 * √2) * √(↑t : ℝ) ≤ (↑(pullCount (sel ω) i t) : ℝ) ∧
                          (↑(pullCount (sel ω) i t) : ℝ) ≤ C * √(↑t : ℝ)) ∧
            ∀ (j : ι),
              (∀ (i : ι), i ≠ j → ∫ (ω' : Ω), X i 0 ω' ∂P < ∫ (ω' : Ω), X j 0 ω' ∂P) →
                ∃ C,
                  ∀ (t : ℕ),
                    1 ≤ t →
                      (↑t : ℝ) - C * √(↑t : ℝ) ≤ (↑(pullCount (sel ω) j t) : ℝ) ∧ (↑(pullCount (sel ω) j t) : ℝ) ≤ (↑t : ℝ) :=
  @LiteralE6.v35rootrates_literal ι _ Ω _ P _ lam hlam X hbdd hindep hident sel Q hQ0 hQmean hrule

/-! ### `ce:v35prior`: Counterexample E.23 (Zero prior at one internal edge prevents terminal coverage) -/

/-- **Counterexample E.23** `ce:v35prior`: Zero prior at one internal edge prevents terminal coverage.

Manuscript: For a two-edge internal node with weights λ_1 > 0 and λ_2 = 0, unvisited values
initialized to zero and first-edge tie breaking, with Bernoulli terminals (the first of mean 1/2),
the second terminal is never sampled, even though both reward laws have positive variance.

Lean: `LiteralE6.zero_prior_bernoulli` (`JointRootCert/LiteralE6.lean`). Bernoulli terminals with
positive variance. -/
theorem ce_v35prior
    (lam0 : ℝ)
    (hlam0 : (0 : ℝ) < lam0)
    (p : Fin (2 : ℕ) → ℝ)
    (hp : ∀ (z : Fin (2 : ℕ)), (0 : ℝ) < p z ∧ p z < (1 : ℝ)) :
      ∃ (Ω : Type) (x : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω) (B : Fin (2 : ℕ) × ℕ → Ω → ℝ),
        MeasureTheory.IsProbabilityMeasure P ∧
          (∀ (i : Fin (2 : ℕ) × ℕ), Measurable (B i)) ∧
            (∀ (i : Fin (2 : ℕ) × ℕ) (ω : Ω), B i ω = (0 : ℝ) ∨ B i ω = (1 : ℝ)) ∧
              (∀ (i : Fin (2 : ℕ) × ℕ), (P : Set Ω → ENNReal) {ω : Ω | B i ω = (1 : ℝ)} = ENNReal.ofReal (p (Prod.fst i))) ∧
                ProbabilityTheory.iIndepFun B P ∧
                  ∃ (vis : Ω → ℕ → Fin (3 : ℕ) → Prop) (ch : Ω → ℕ → Fin (3 : ℕ) → Fin (2 : ℕ)) (Q : Ω → Fin (2 : ℕ) → ℕ → ℝ),
                    ∀ (ω : Ω),
                      LiteralE6.TapeRun LiteralE6.ceSrc LiteralE6.ceTgt (0 : Fin (3 : ℕ)) ![lam0, (0 : ℝ)]
                          (fun (v : Fin (3 : ℕ)) (k : ℕ) =>
                            if v = (1 : Fin (3 : ℕ)) then B ((0 : Fin (2 : ℕ)), k) ω
                            else if v = (2 : Fin (3 : ℕ)) then B ((1 : Fin (2 : ℕ)), k) ω else (0 : ℝ))
                          (1 : ℕ) (vis ω) (ch ω) (Q ω) ∧
                        LiteralE6.FirstEdgeTies LiteralE6.ceSrc ![lam0, (0 : ℝ)] (vis ω) (ch ω) (Q ω) ∧
                          (∀ (s : ℕ), ¬vis ω s (LiteralE6.ceTgt (1 : Fin (2 : ℕ)))) ∧
                            ∀ (t : ℕ), visitCount (vis ω) (LiteralE6.ceTgt (1 : Fin (2 : ℕ))) t = (0 : ℕ) :=
  @LiteralE6.zero_prior_bernoulli lam0 hlam0 p hp

/-! ### `thm:adaptive-oracle-coupling`: Theorem K.1 (Exact coupling and charged maintenance) -/

/-- **Theorem K.1** `thm:adaptive-oracle-coupling`: Exact coupling and charged maintenance.

Manuscript: Implementations exposing the same deterministic certificate-and-witness oracle induce
identical observations, recommendations and stopping times under common tapes. With h = 1 + ⌈log₂
M⌉, R_run = Σ_a r_a and charged run-merging work P_G, dual covers use B ≤ 2h(2R_run + K)
incidences, compile in O(P_G + (R_run + K)h + B) work, update in O(h) tree work plus
changed-subscription heap work, and occupy O(|V| + |E| + M + B + K) space.

Lean: `LiteralK7.charged_dual_cover_literal` (`JointRootCert/LiteralK7.lean`). One shared tree,
linear initialisation, a global min-heap on the regret, space in a cell-accounting model; pairwise
run merging (same order as a heap merge); a query costs one unit. -/
theorem thm_adaptive_oracle_coupling
    {α : Type u_1}
    [LinearOrder α]
    [OrderBot α]
    (G : CostEngines.Dag)
    (hG : CostEngines.Dag.WF G)
    (pos : ℕ → ℕ)
    (M : ℕ)
    (hM1 : (1 : ℕ) ≤ M)
    (supp : ℕ → Finset ℕ)
    (order : List ℕ)
    (hsorted : List.Pairwise (fun (a b : ℕ) => CostEngines.Dag.level G a ≤ CostEngines.Dag.level G b) order)
    (hclosed : ∀ g ∈ order, ∀ c ∈ CostEngines.Dag.children G g, c ∈ order)
    (hleaf : ∀ g ∈ order, CostEngines.Dag.children G g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order,
  CostEngines.Dag.children G g ≠ [] → supp g = Finset.biUnion (List.toFinset (CostEngines.Dag.children G g)) supp)
    (as : List ℕ)
    (has : ∀ a ∈ as, a ∈ order)
    (hnd : List.Nodup as)
    (φ : α → ℝ)
    (fl : ℕ → α)
    (fu : ℕ → α)
    (hfl : ∀ (p : ℕ), (2 : ℕ) ^ Nat.clog (2 : ℕ) M ≤ p → fl p = ⊥)
    (hfu : ∀ (p : ℕ), (2 : ℕ) ^ Nat.clog (2 : ℕ) M ≤ p → fu p = ⊥)
    (ops : List (Option (ℕ × α × α)))
    (hops : ∀ (q : ℕ × α × α), some q ∈ ops → Prod.fst q < (2 : ℕ) ^ Nat.clog (2 : ℕ) M) :
      have n := Nat.clog (2 : ℕ) M;
      have cP := DualCoverFinal.covPlus G pos M order as;
      have cM := DualCoverFinal.covMinus G pos M order as;
      have B :=
        List.sum (List.map (fun (a : ℕ) => List.length (cP a)) as) +
          List.sum (List.map (fun (a : ℕ) => List.length (cM a)) as);
      have Rrun := List.sum (List.map (fun (a : ℕ) => Representation.runs (supp a)) as);
      have s0 := LiteralK7.iInit n fl fu cP cM (LiteralK7.minKey φ) as;
      have run :=
        LiteralK7.iRun n (DualCoverFinal.subsOf as cP) (DualCoverFinal.subsOf as cM) (LiteralK7.minKey φ) ops (Prod.fst s0);
      (∀ a ∈ as,
          Representation.IsDyadicCover (List.toFinset (List.map CostModel.blk (cP a))) (supp a) ∧
            Representation.IsDyadicCover (List.toFinset (List.map CostModel.blk (cM a))) (Finset.range M \ supp a)) ∧
        B ≤ (2 : ℕ) * ((1 : ℕ) + n) * ((2 : ℕ) * Rrun + List.length as) ∧
          Prod.snd (Prod.fst run) =
              LiteralK7.specRun (List.toFinset as) (LiteralK7.minKey φ) supp (fun (a : ℕ) => Finset.range M \ supp a) ops fl
                fu ∧
            Prod.snd (RunMerge.runPhase G pos order fun (x : ℕ) => []) +
                      Prod.snd
                        (CostModel.compileAll n M
                          (List.map (Prod.fst (RunMerge.runPhase G pos order fun (x : ℕ) => [])) as)) +
                    Prod.snd s0 +
                  Prod.snd run ≤
                List.sum (List.map (RunMerge.gateCost G supp) order) +
                                (4 : ℕ) * ((1 : ℕ) + n) * ((2 : ℕ) * Rrun + List.length as) +
                              B +
                            ((2 : ℕ) ^ (n + (1 : ℕ)) - (1 : ℕ)) +
                          List.sum (List.map (fun (a : ℕ) => (8 : ℕ) * List.length (cP a) + (1 : ℕ)) as) +
                        List.sum (List.map (fun (a : ℕ) => (8 : ℕ) * List.length (cM a) + (1 : ℕ)) as) +
                      (10 : ℕ) * List.length as +
                    LiteralK7.runSum n (DualCoverFinal.subsOf as cP) (DualCoverFinal.subsOf as cM)
                      (fun (a : ℕ) => List.length (cP a)) (fun (a : ℕ) => List.length (cM a)) (List.length as) ops
                      (LiteralK7.prj1 (LiteralK7.IState.tree (Prod.fst s0)))
                      (LiteralK7.prj2 (LiteralK7.IState.tree (Prod.fst s0))) +
                  LiteralK7.numQ ops ∧
              List.sum (List.map (RunMerge.gateCost G supp) order) ≤
                  (3 : ℕ) * List.sum (List.map (LiteralK7.pgTerm G supp) order) ∧
                LiteralK7.TreeFits n (LiteralK7.IState.tree (Prod.fst (Prod.fst run))) ∧
                  DualCoverFinal.graphCells G +
                      LiteralK7.iFootprint n cP cM (DualCoverFinal.subsOf as cP) (DualCoverFinal.subsOf as cM) as
                        (Prod.fst (Prod.fst run)) ≤
                    CostEngines.Dag.N G +
                            (2 : ℕ) * ∑ p ∈ Finset.range (CostEngines.Dag.N G), List.length (CostEngines.Dag.children G p) +
                          (8 : ℕ) * M +
                        (5 : ℕ) * B +
                      (4 : ℕ) * List.length as :=
  @LiteralK7.charged_dual_cover_literal α _ _ G hG pos M hM1 supp order hsorted hclosed hleaf hgate as has hnd φ fl fu hfl hfu ops hops

/-! ### `prop:representation-coupling`: Proposition K.2 (Trajectory Coupling Across Circuit Representations) -/

/-- **Proposition K.2** `prop:representation-coupling`: Trajectory Coupling Across Circuit Representations.

Manuscript: Bypassing unary gates, interning gates with identical child sets, or replacing root
supports by a shared dyadic-block max-circuit preserves all root confidence intervals, optimistic
leaders and certified stopping times. Applying the strict dominance retirement rule u(c) < l(v)
inside any such circuit preserves exact rollout trajectory coupling with unmonitored TA-UCT.

Lean: `LiteralK1.retirement_coupling_literal` (`JointRootCert/LiteralK1.lean`). Main theorem: the
retirement clause on DAGs with sharing and reference-counted release; companion: the semantic
coupling of the representations. -/
theorem prop_representation_coupling
    {Z : Type u_1}
    {X : Type u_2}
    [DecidableEq Z]
    {α : Type u_3}
    [LinearOrder α]
    [OrderBot α]
    {G0 : CostEngines.Dag}
    {K : ℕ}
    {rt : ℕ → ℕ}
    {cand : DagRetire.RState α → DagRetire.RState α → List (ℕ × ℕ)}
    {q : ℕ → Bool}
    {leaf : Z → ℕ}
    {ci : List (Z × X) → α × α}
    {I0 : Z → α × α}
    {lo0 : CostEngines.EState α}
    {hi0 : CostEngines.EState α}
    {Ω : Type u_4}
    (hG : G0.WF)
    (h0 : DagRetire.RInv G0 { G := G0, lo := lo0, hi := hi0 })
    (hleaf : ∀ (z : Z), leaf z < G0.N ∧ G0.children (leaf z) = [])
    (hinj : Function.Injective leaf)
    (hI0 : ∀ (z : Z), lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (hK : 0 < K)
    (φ : α → ℝ)
    (hφ : StrictMono φ)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (ctrl : Representation.Controller Z X (Bool × Option ℕ × Bool) Ω)
    (rew : ℕ → Z → X)
    (ω : Ω) :
      (∀ (n : ℕ),
          Representation.history (LiteralK1.selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n =
            Representation.history (LiteralK1.eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
        (∀ (n : ℕ),
            Representation.replyAt (LiteralK1.selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n =
              Representation.replyAt (LiteralK1.eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
          Representation.stopTime (LiteralK1.selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω =
            Representation.stopTime (LiteralK1.eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω :=
  @LiteralK1.retirement_coupling_literal Z X _ α _ _ G0 K rt cand q leaf ci I0 lo0 hi0 Ω hG h0 hleaf hinj hI0 hK φ hφ ε hε ctrl rew ω

/-- Companion to Proposition K.2 `prop:representation-coupling`: coupling of root values across the
representations. Lean: `Representation.representation_coupling`
(`JointRootCert/Representation.lean`). -/
theorem prop_representation_coupling_circuits
    {Z : Type u_1}
    {X : Type u_2}
    {Ω : Type u_3}
    {A : Type u_4}
    {β : Type u_5}
    [SemilatticeSup β]
    [OrderBot β]
    [DecidableEq Z]
    (box : List (Z × X) → (Z → β) × (Z → β))
    (R : A → Representation.MaxCircuit Z)
    (R' : A → Representation.MaxCircuit Z)
    (h : ∀ (a : A), (R' a).supp = (R a).supp)
    (ctrl : Representation.Controller Z X (A → β × β) Ω)
    (rew : ℕ → Z → X)
    (ω : Ω) :
      (∀ (n : ℕ),
          Representation.history (Representation.circuitOracle box R') ctrl rew ω n =
            Representation.history (Representation.circuitOracle box R) ctrl rew ω n) ∧
        (∀ (n : ℕ),
            Representation.replyAt (Representation.circuitOracle box R') ctrl rew ω n =
              Representation.replyAt (Representation.circuitOracle box R) ctrl rew ω n) ∧
          Representation.stopTime (Representation.circuitOracle box R') ctrl rew ω =
            Representation.stopTime (Representation.circuitOracle box R) ctrl rew ω :=
  @Representation.representation_coupling Z X Ω A β _ _ _ box R R' h ctrl rew ω

/-! ### `prop:representation-cost`: Proposition K.3 (Unified Full-Cost Representation Comparison) -/

/-- **Proposition K.3** `prop:representation-cost`: Unified Full-Cost Representation Comparison.

Manuscript: Under the shared indexed-heap update and strict dominance retirement engine, the total
scalar work of representation R satisfies W_R = O(H + P_R + n_R + e_R + (S_R⁺ + e_R) log D_R).
Conversely, any compiled representation C executing the incidence-delivery contract incurs at
least Ω(P_C + S_C⁻) scalar operations. Consequently, direct graph maintenance G achieves an
asymptotic total-work advantage over C whenever H + P_G + n_G + e_G + (S_G⁺ + e_G) log D_G = o(P_C
+ S_C⁻) (condition R).

Lean: `LiteralG4.representation_cost_Lin` (`JointRootCert/LiteralG4.lean`). Main theorem: the RAM
model with a linked incidence structure (`WL ≤ 303·XD` for distinct root gates); companion: every
cell read, write and comparison charged by op-count functions, with the upfront passes P_G
computed. Inputs: H, the run data, the stop rule as an oracle, the input circuit, the level-sorted
initial order, empty initial heaps. -/
theorem prop_representation_cost
    {α : Type u_1}
    [LinearOrder α]
    [OrderBot α]
    {β : Type u_2}
    {Cell : Type u_3}
    {ι : Type u_4}
    [DecidableEq β]
    [DecidableEq Cell]
    {l : Filter ι}
    (G : ι → LiteralK3.SelRun α)
    (μ : ι → LiteralG4.Mem)
    (φ : ι → α → ℝ)
    (ε : ι → ℝ)
    (hcl : ∀ (i : ι) (p c : ℕ), c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ (i : ι), ∀ k < (G i).K, (G i).rt k < (G i).G0.N)
    (hinj : ∀ (i : ι), ∀ k < (G i).K, ∀ j < (G i).K, (G i).rt k = (G i).rt j → k = j)
    (C : ι → LiteralK4.DeliveryImpl β Cell) :
      (∀ (i : ι), LiteralG4.WL (G i) (μ i) (φ i) (ε i) ≤ 303 * LiteralK10.XD (G i)) ∧
        ((fun i => (↑(LiteralG4.WL (G i) (μ i) (φ i) (ε i)) : ℝ)) =O[l] fun i => (↑(LiteralK10.XD (G i)) : ℝ)) ∧
          (∀ (i : ι), (C i).P + (C i).Sminus ≤ (C i).W) ∧
            (((fun i => (↑(LiteralK10.XD (G i)) : ℝ)) =o[l] fun i => (↑((C i).P + (C i).Sminus) : ℝ)) →
              (fun i => (↑(LiteralG4.WL (G i) (μ i) (φ i) (ε i)) : ℝ)) =o[l] fun i => (↑(C i).W : ℝ)) :=
  @LiteralG4.representation_cost_Lin α _ _ β Cell ι _ _ l G μ φ ε hcl hlt hinj C

/-- Companion to Proposition K.3 `prop:representation-cost`: strict per-operation counts with computed
upfront passes. Lean: `LiteralG5.representation_cost_strict` (`JointRootCert/LiteralG5.lean`). -/
theorem prop_representation_cost_strict
    {α : Type u_1}
    [LinearOrder α]
    [OrderBot α]
    {β : Type u_2}
    {Cell : Type u_3}
    {ι : Type u_4}
    [DecidableEq β]
    [DecidableEq Cell]
    {l : Filter ι}
    (G : ι → LiteralK3.SelRun α)
    (μ : ι → LiteralG4.Mem)
    (φ : ι → α → ℝ)
    (ε : ι → ℝ)
    (hcl : ∀ (i : ι) (p c : ℕ), c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ (i : ι), ∀ k < (G i).K, (G i).rt k < (G i).G0.N)
    (hinj : ∀ (i : ι), ∀ k < (G i).K, ∀ j < (G i).K, (G i).rt k = (G i).rt j → k = j)
    (C : ι → LiteralK4.DeliveryImpl β Cell) :
      (∀ (i : ι), LiteralG5.WLS (G i) (μ i) (φ i) (ε i) ≤ 6969 * LiteralG5.XGS (G i) (μ i)) ∧
        (∀ (i : ι), LiteralG5.PGS (G i) (μ i) ≤ 621 * ((G i).G0.N + DagRetire.live (G i).G0)) ∧
          ((fun i => (↑(LiteralG5.WLS (G i) (μ i) (φ i) (ε i)) : ℝ)) =O[l] fun i => (↑(LiteralG5.XGS (G i) (μ i)) : ℝ)) ∧
            ((fun i => (↑(LiteralG5.XGS (G i) (μ i)) : ℝ)) =O[l] fun i => (↑(LiteralG5.XD0 (G i)) : ℝ)) ∧
              ((fun i => (↑(LiteralG5.XD0 (G i)) : ℝ)) =O[l] fun i => (↑(LiteralG5.XGS (G i) (μ i)) : ℝ)) ∧
                (∀ (i : ι), (C i).P + (C i).Sminus ≤ (C i).W) ∧
                  (((fun i => (↑(LiteralG5.XGS (G i) (μ i)) : ℝ)) =o[l] fun i => (↑((C i).P + (C i).Sminus) : ℝ)) →
                    (fun i => (↑(LiteralG5.WLS (G i) (μ i) (φ i) (ε i)) : ℝ)) =o[l] fun i => (↑(C i).W : ℝ)) :=
  @LiteralG5.representation_cost_strict α _ _ β Cell ι _ _ l G μ φ ε hcl hlt hinj C

/-! ### `thm:coded-main`: Theorem K.4 (Every-layout limit of flat dyadic compilation) -/

/-- **Theorem K.4** `thm:coded-main`: Every-layout limit of flat dyadic compilation.

Manuscript: For every power of two r ≥ 4, there exist all-MAX parity-grid DAGs of size Θ(r²) with
Θ(r) root actions on which direct graph maintenance certifies an ε-optimal action in O(r² log² r)
total work with probability at least 1 − δ, whereas every single-ordering dyadic root-support
compiler explicitly materializing root-to-block incidences incurs Ω(r³) initialization work prior
to the first rollout.

Lean: `LiteralK6.coded_main_computed` (`JointRootCert/LiteralK6.lean`). Main theorem: computed
costs on the implemented heap for the eager and selective engines; companion: the Ω(r³) half as
compiler work. -/
theorem thm_coded_main
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ1 : δ < (1 : ℝ)) :
      ∃ (A : ℝ) (B : ℝ),
        (0 : ℝ) < A ∧
          (0 : ℝ) < B ∧
            ∀ (k : ℕ),
              (2 : ℕ) ≤ k →
                ((2 : ℕ) ^ k * (2 : ℕ) ^ k ≤ CostEngines.Dag.N (ParityGrid.pgDag k) ∧
                    CostEngines.Dag.N (ParityGrid.pgDag k) ≤ (7 : ℕ) * ((2 : ℕ) ^ k * (2 : ℕ) ^ k) ∧
                      (2 : ℕ) * ((2 : ℕ) ^ k * (2 : ℕ) ^ k) ≤ ParityGrid.pgE k ∧
                        ParityGrid.pgE k ≤ (11 : ℕ) * ((2 : ℕ) ^ k * (2 : ℕ) ^ k)) ∧
                  Function.Injective (ParityGrid.pgSupp k) ∧
                    (∀ (a : Fin (ParityGrid.pgD k + (1 : ℕ))) (hne : Finset.Nonempty (ParityGrid.pgSupp k a)),
                        regret (ParityGrid.pgSupp k a) hne (ParityGrid.pgMean k) ≤ (1 / 5 : ℝ) ↔
                          a = Fin.last (ParityGrid.pgD k)) ∧
                      (∀ (Op : Type) (π : Representation.GridTerminal k ≃ Fin ((2 : ℕ) ^ k * (2 : ℕ) ^ k + (1 : ℕ)))
                          (tr : List (LiteralK5.Instr (Finset (Representation.GridTerminal k)) Op)),
                          (∀ (a : Fin (ParityGrid.pgD k + (1 : ℕ))),
                              LiteralK5.IsListCover (LiteralK5.emitted tr (ParityGrid.pgSupp k a))
                                (Representation.layoutPos π (ParityGrid.pgSupp k a))) →
                            ((2 : ℕ) ^ k) ^ (3 : ℕ) ≤ (2 : ℕ) * LiteralK5.work tr) ∧
                        ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
                          [MeasureTheory.IsProbabilityMeasure P] (X : Representation.GridTerminal k → ℕ → Ω → ℝ),
                          (∀ (z : Representation.GridTerminal k), ProbabilityTheory.iIndepFun (X z) P) →
                            (∀ (z : Representation.GridTerminal k) (i : ℕ), AEMeasurable (X z i) P) →
                              (∀ (i : ℕ), ∀ᵐ (ω : Ω) ∂P, X none i ω ∈ Set.Icc 0.98 (1 : ℝ)) →
                                (∀ (g : Representation.Mask k × Representation.Mask k) (i : ℕ),
                                    ∀ᵐ (ω : Ω) ∂P, X (some g) i ω ∈ Set.Icc 1e-2 3e-2) →
                                  (∀ (z : Representation.GridTerminal k) (i : ℕ),
                                      ∫ (ω : Ω), X z i ω ∂P = ParityGrid.pgMean k z) →
                                    ∀ (sel : Ω → ℕ → Fin (ParityGrid.pgD k + (1 : ℕ)))
                                      (zt : Ω → ℕ → Representation.GridTerminal k) (idx : Ω → ℕ → ℕ → ℝ)
                                      (rawL rawU : HeapImpl.HEState NNReal),
                                      LiteralK6.RawOK k ⊥ rawL →
                                        LiteralK6.RawOK k (1 : NNReal) rawU →
                                          (∀ (ω : Ω),
                                              ParityGrid.ParitySearch
                                                (fun (z : Representation.GridTerminal k) (i : ℕ) => X z i ω) (sel ω) (zt ω)) →
                                            (P : Set Ω → ENNReal)
                                                {ω : Ω |
                                                  ¬(tapeCovered (ParityGrid.pgM k) δ
                                                        (fun (z : Representation.GridTerminal k) (i : ℕ) => X z i ω) (zt ω)
                                                        (ParityGrid.pgMean k) ∧
                                                      LiteralK6.PGCertifiedComputed δ A B
                                                        (fun (z : Representation.GridTerminal k) (i : ℕ) => X z i ω) (sel ω)
                                                        (zt ω) (idx ω) rawL rawU)} ≤
                                              ENNReal.ofReal δ :=
  @LiteralK6.coded_main_computed δ hδ0 hδ1

/-- Companion to Theorem K.4 `thm:coded-main`: the Ω(r³) compiler-work lower bound. Lean:
`LiteralK5.compiler_work_lower` (`JointRootCert/LiteralK5.lean`). -/
theorem thm_coded_main_lower
    {k : ℕ}
    (hk : 1 ≤ k)
    {Op : Type u_1}
    (π : Representation.GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (tr : List (LiteralK5.Instr (Finset (Representation.GridTerminal k)) Op))
    (hC : ∀ (a : Fin (ParityGrid.pgD k + 1)),
  LiteralK5.IsListCover (LiteralK5.emitted tr (ParityGrid.pgSupp k a))
    (Representation.layoutPos π (ParityGrid.pgSupp k a))) :
      (2 ^ k) ^ 3 ≤ 2 * LiteralK5.work tr :=
  @LiteralK5.compiler_work_lower k hk Op π tr hC

/-! ### `thm:coded-covers`: Theorem K.5 (Every-Layout Dyadic Cover Lower Bound) -/

/-- **Theorem K.5** `thm:coded-covers`: Every-Layout Dyadic Cover Lower Bound.

Manuscript: For every r = 2^k ≥ 4 and δ ∈ (0, 1/2), there exist explicit all-max DAGs of size
Θ(r²) with Θ(r) distinct root supports, a unique ε-optimal root action at ε = 1/5 and independent
continuous bounded rewards such that TA-UCT with c = 2 stops within O(r² log² r) total scalar work
under either Graph Eager or Graph Selective and certifies the optimal action with probability at
least 1 − δ. Every cold compiler that materializes root dyadic block covers in a single terminal
ordering incurs Ω(r³) operations prior to certification, regardless of the ordering.

Lean: `LiteralK2.coded_covers_selective` (`JointRootCert/LiteralK2.lean`). The confidence alarm is
not modelled. Companion: `r³ ≤ 2 Σ|C_p|` for every layout and cover. -/
theorem thm_coded_covers
    {δ : ℝ}
    (hδ0 : (0 : ℝ) < δ)
    (hδ1 : δ < (1 : ℝ)) :
      ∃ (A : ℝ) (B : ℝ),
        (0 : ℝ) < A ∧
          (0 : ℝ) < B ∧
            ∀ (k : ℕ),
              (2 : ℕ) ≤ k →
                ((2 : ℕ) ^ k * (2 : ℕ) ^ k ≤ CostEngines.Dag.N (ParityGrid.pgDag k) ∧
                    CostEngines.Dag.N (ParityGrid.pgDag k) ≤ (7 : ℕ) * ((2 : ℕ) ^ k * (2 : ℕ) ^ k) ∧
                      (2 : ℕ) * ((2 : ℕ) ^ k * (2 : ℕ) ^ k) ≤ ParityGrid.pgE k ∧
                        ParityGrid.pgE k ≤ (11 : ℕ) * ((2 : ℕ) ^ k * (2 : ℕ) ^ k)) ∧
                  Function.Injective (ParityGrid.pgSupp k) ∧
                    (∀ (a : Fin (ParityGrid.pgD k + (1 : ℕ))) (hne : Finset.Nonempty (ParityGrid.pgSupp k a)),
                        regret (ParityGrid.pgSupp k a) hne (ParityGrid.pgMean k) ≤ (1 / 5 : ℝ) ↔
                          a = Fin.last (ParityGrid.pgD k)) ∧
                      (∀ (π : Representation.GridTerminal k ≃ Fin ((2 : ℕ) ^ k * (2 : ℕ) ^ k + (1 : ℕ)))
                          (C : Representation.ParityIndex k → Finset (Finset ℕ)),
                          (∀ p ∈ Representation.parityActions k,
                              Representation.IsDyadicCover (C p) (Representation.layoutPos π (Representation.paritySupp p))) →
                            (2 : ℕ) ^ k * (2 : ℕ) ^ k * (2 : ℕ) ^ k ≤
                              (2 : ℕ) * ∑ p ∈ Representation.parityActions k, Finset.card (C p)) ∧
                        ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
                          [MeasureTheory.IsProbabilityMeasure P] (X : Representation.GridTerminal k → ℕ → Ω → ℝ),
                          (∀ (z : Representation.GridTerminal k), ProbabilityTheory.iIndepFun (X z) P) →
                            (∀ (z : Representation.GridTerminal k) (i : ℕ), AEMeasurable (X z i) P) →
                              (∀ (i : ℕ), ∀ᵐ (ω : Ω) ∂P, X none i ω ∈ Set.Icc 0.98 (1 : ℝ)) →
                                (∀ (g : Representation.Mask k × Representation.Mask k) (i : ℕ),
                                    ∀ᵐ (ω : Ω) ∂P, X (some g) i ω ∈ Set.Icc 1e-2 3e-2) →
                                  (∀ (z : Representation.GridTerminal k) (i : ℕ),
                                      ∫ (ω : Ω), X z i ω ∂P = ParityGrid.pgMean k z) →
                                    ∀ (sel : Ω → ℕ → Fin (ParityGrid.pgD k + (1 : ℕ)))
                                      (zt : Ω → ℕ → Representation.GridTerminal k),
                                      (∀ (ω : Ω),
                                          ParityGrid.ParitySearch (fun (z : Representation.GridTerminal k) (i : ℕ) => X z i ω)
                                            (sel ω) (zt ω)) →
                                        (P : Set Ω → ENNReal)
                                            {ω : Ω |
                                              ¬(tapeCovered (ParityGrid.pgM k) δ
                                                    (fun (z : Representation.GridTerminal k) (i : ℕ) => X z i ω) (zt ω)
                                                    (ParityGrid.pgMean k) ∧
                                                  LiteralK2.PGCertifiedBoth δ A B
                                                    (fun (z : Representation.GridTerminal k) (i : ℕ) => X z i ω) (sel ω)
                                                    (zt ω))} ≤
                                          ENNReal.ofReal δ :=
  @LiteralK2.coded_covers_selective δ hδ0 hδ1

/-- Companion to Theorem K.5 `thm:coded-covers`: the every-layout cover lower bound. Lean:
`Representation.parityGrid_cover_lower` (`JointRootCert/Representation.lean`). -/
theorem thm_coded_covers_lower
    {k : ℕ}
    (hk : 1 ≤ k)
    (π : Representation.GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (C : Representation.ParityIndex k → Finset (Finset ℕ))
    (hC : ∀ p ∈ Representation.parityActions k,
  Representation.IsDyadicCover (C p) (Representation.layoutPos π (Representation.paritySupp p))) :
      2 ^ k * 2 ^ k * 2 ^ k ≤ 2 * ∑ p ∈ Representation.parityActions k, (C p).card :=
  @Representation.parityGrid_cover_lower k hk π C hC

/-! ### `prop:unrestricted-compiler`: Proposition K.6 (Equivalence Under Unrestricted Circuit Retention) -/

/-- **Proposition K.6** `prop:unrestricted-compiler`: Equivalence Under Unrestricted Circuit Retention.

Manuscript: A compiler permitted to retain the original hierarchical monitor circuit G and execute
the shared indexed-heap update engine reproduces Graph Selective with at most O(|V| + |E|)
additional setup work.

Lean: `LiteralK8.retained_compiler_literal` (`JointRootCert/LiteralK8.lean`). Stated for the Graph
Selective engine itself, in the step-counting model. -/
theorem prop_unrestricted_compiler
    {α : Type u_1}
    [LinearOrder α]
    [OrderBot α]
    {A : CostEngines.ADag}
    {L : ℕ}
    (hA : LiteralK8.WFA A L)
    (order : List ℕ)
    (vl : ℕ → α)
    (vu : ℕ → α)
    (candV : EngineFinal.Policy α)
    (u : ℕ → ℕ × α × α)
    (q : ℕ → Bool)
    (φ : α → ℝ)
    (ε : ℝ) :
      Prod.fst (CostEngines.copyDag A) = A ∧
        CostEngines.Dag.WF (CostEngines.ADag.toDag A L) ∧
          LiteralK8.rootOf (Prod.fst (CostEngines.copyDag A)) = LiteralK8.rootOf A ∧
            (∀ (T : ℕ),
                Prod.fst (LiteralK8.retainedCompile A L order vl vu candV u q T) =
                  Prod.fst (LiteralK8.graphSelective A L order vl vu candV u q T)) ∧
              (∀ (T : ℕ),
                  RetireFinal.qOut φ ε (List.length (CostEngines.ADag.roots A))
                      (fun (i : ℕ) =>
                        HeapImpl.HEState.val
                          (EngineFinal.HRState.lo
                            (RetireFinal.HQS.r (Prod.fst (LiteralK8.retainedCompile A L order vl vu candV u q T))))
                          (LiteralK8.rootOf A i))
                      (fun (i : ℕ) =>
                        HeapImpl.HEState.val
                          (EngineFinal.HRState.hi
                            (RetireFinal.HQS.r (Prod.fst (LiteralK8.retainedCompile A L order vl vu candV u q T))))
                          (LiteralK8.rootOf A i))
                      (RetireFinal.HQS.act (Prod.fst (LiteralK8.retainedCompile A L order vl vu candV u q T))) =
                    RetireFinal.qOut φ ε (List.length (CostEngines.ADag.roots A))
                      (fun (i : ℕ) =>
                        HeapImpl.HEState.val
                          (EngineFinal.HRState.lo
                            (RetireFinal.HQS.r (Prod.fst (LiteralK8.graphSelective A L order vl vu candV u q T))))
                          (LiteralK8.rootOf A i))
                      (fun (i : ℕ) =>
                        HeapImpl.HEState.val
                          (EngineFinal.HRState.hi
                            (RetireFinal.HQS.r (Prod.fst (LiteralK8.graphSelective A L order vl vu candV u q T))))
                          (LiteralK8.rootOf A i))
                      (RetireFinal.HQS.act (Prod.fst (LiteralK8.graphSelective A L order vl vu candV u q T)))) ∧
                (∀ (T : ℕ),
                    RetireFinal.qRetireH (List.length (CostEngines.ADag.roots A)) (LiteralK8.rootOf A)
                        (Prod.fst (LiteralK8.retainedCompile A L order vl vu candV u q T)) =
                      RetireFinal.qRetireH (List.length (CostEngines.ADag.roots A)) (LiteralK8.rootOf A)
                        (Prod.fst (LiteralK8.graphSelective A L order vl vu candV u q T))) ∧
                  (∀ (t : ℕ),
                      RetireFinal.costH (List.length (CostEngines.ADag.roots (Prod.fst (CostEngines.copyDag A))))
                          (LiteralK8.rootOf (Prod.fst (CostEngines.copyDag A))) candV u q
                          { r := Prod.fst (LiteralK8.coldInit (Prod.fst (CostEngines.copyDag A)) L order vl vu),
                            act := fun (x : ℕ) => true }
                          t =
                        RetireFinal.costH (List.length (CostEngines.ADag.roots A)) (LiteralK8.rootOf A) candV u q
                          { r := Prod.fst (LiteralK8.coldInit A L order vl vu), act := fun (x : ℕ) => true } t) ∧
                    (∀ (T : ℕ),
                        Prod.snd (LiteralK8.retainedCompile A L order vl vu candV u q T) =
                          Prod.snd (LiteralK8.graphSelective A L order vl vu candV u q T) +
                            Prod.snd (CostEngines.copyDag A)) ∧
                      Prod.snd (CostEngines.copyDag A) ≤ (4 : ℕ) * (CostEngines.ADag.V A + CostEngines.ADag.E A) :=
  @LiteralK8.retained_compiler_literal α _ _ A L hA order vl vu candV u q φ ε

end JointRootCert.Manuscript
