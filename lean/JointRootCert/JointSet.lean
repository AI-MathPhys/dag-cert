/-
Joint-set reduction (Lemma `lem:bay-reduction`, Appendix A.1) and the first
equality of `eq:robust-definition`.

For an arbitrary set `C` of plausible environments (terminal-value vectors), the
worst-case regret of a commitment under one *common* environment is governed only
by excluded terminals.
-/
import JointRootCert.Basic

namespace JointRootCert

open Finset

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {S : Finset Z} {hS : S.Nonempty} {ε : ℝ}

/-- **Joint-set reduction, certificate form.**  A commitment is `ε`-acceptable in every
environment of `C` iff `ε ≥ 0` and no excluded terminal has advantage above `ε` in any
environment of `C`. -/
theorem robust_regret_le_iff (C : Set (Z → ℝ)) (hC : C.Nonempty) :
    (∀ f ∈ C, regret S hS f ≤ ε) ↔
      0 ≤ ε ∧ ∀ z, z ∉ S → ∀ f ∈ C, adv S hS f z ≤ ε := by
  constructor
  · intro h
    obtain ⟨f₀, hf₀⟩ := hC
    refine ⟨(regret_nonneg S hS f₀).trans (h f₀ hf₀), fun z hz f hf => ?_⟩
    rw [adv_eq]
    exact (regret_le_iff.mp (h f hf)).2 z hz
  · rintro ⟨h0, h⟩ f hf
    rw [regret_le_iff]
    refine ⟨h0, fun z hz => ?_⟩
    rw [← adv_eq]
    exact h z hz f hf

/-- Worst-case common-environment regret `R_C(a) = sup_{f ∈ C} r_f(a)`. -/
noncomputable def robustRegret (S : Finset Z) (hS : S.Nonempty) (C : Set (Z → ℝ)) : ℝ :=
  sSup (regret S hS '' C)

/-- Worst-case advantage `D_C(z, S) = sup_{f ∈ C} min_{y ∈ S} (f z - f y)`. -/
noncomputable def robustAdv (S : Finset Z) (hS : S.Nonempty) (C : Set (Z → ℝ)) (z : Z) : ℝ :=
  sSup ((fun f => adv S hS f z) '' C)

lemma adv_le_regret (S : Finset Z) (hS : S.Nonempty) (f : Z → ℝ) (z : Z) :
    adv S hS f z ≤ regret S hS f := by
  rw [adv_eq]
  have := le_gmax f z
  unfold regret
  linarith

lemma bddAbove_adv_image {C : Set (Z → ℝ)} (hB : BddAbove (regret S hS '' C)) (z : Z) :
    BddAbove ((fun f => adv S hS f z) '' C) := by
  obtain ⟨M, hM⟩ := hB
  refine ⟨M, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact (adv_le_regret S hS f z).trans (hM ⟨f, hf, rfl⟩)

/-- **Joint-set reduction (Lemma `lem:bay-reduction`).**  For a nonempty set of
environments on which the regret is bounded (in particular any compact set) and a
proper support,
`R_C(a) = max {0, max_{z ∉ S(a)} D_C(z, S(a))}`. -/
theorem robustRegret_eq (C : Set (Z → ℝ)) (hC : C.Nonempty)
    (hB : BddAbove (regret S hS '' C)) (hSc : Sᶜ.Nonempty) :
    robustRegret S hS C = max 0 (Sᶜ.sup' hSc (robustAdv S hS C)) := by
  refine eq_of_forall_ge_iff (fun ε => ?_)
  have h1 : robustRegret S hS C ≤ ε ↔ ∀ f ∈ C, regret S hS f ≤ ε := by
    unfold robustRegret
    rw [csSup_le_iff hB (hC.image _)]
    constructor
    · intro h f hf
      exact h _ ⟨f, hf, rfl⟩
    · rintro h _ ⟨f, hf, rfl⟩
      exact h f hf
  have h2 : ∀ z, robustAdv S hS C z ≤ ε ↔ ∀ f ∈ C, adv S hS f z ≤ ε := by
    intro z
    unfold robustAdv
    rw [csSup_le_iff (bddAbove_adv_image hB z) (hC.image _)]
    constructor
    · intro h f hf
      exact h _ ⟨f, hf, rfl⟩
    · rintro h _ ⟨f, hf, rfl⟩
      exact h f hf
  rw [h1, robust_regret_le_iff C hC, max_le_iff, sup'_le_iff]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun z hz => (h2 z).mpr (h z (mem_compl.mp hz))⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun z hz => (h2 z).mp (h z (mem_compl.mpr hz))⟩

/-- Full support: the robust regret vanishes for every set of environments. -/
theorem robustRegret_eq_zero_of_compl_empty (C : Set (Z → ℝ)) (hC : C.Nonempty)
    (hSc : Sᶜ = ∅) : robustRegret S hS C = 0 := by
  have : regret S hS '' C = {0} := by
    ext r
    constructor
    · rintro ⟨f, -, rfl⟩
      exact regret_eq_zero_of_compl_empty hSc
    · rintro rfl
      obtain ⟨f, hf⟩ := hC
      exact ⟨f, hf, regret_eq_zero_of_compl_empty hSc⟩
  simp [robustRegret, this]

end JointRootCert
