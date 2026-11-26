/-
Joint Root Certification: the decision model.

Manuscript: Section 2.1 (`eq:true-value`) and Appendix A.1.

A root action is identified with its support `S ⊆ Z`, the finite set of terminal
outcomes that remain reachable after committing to it.  All decisions along the
graph maximise the same terminal reward, so the value of the commitment is the
maximum of the terminal values over `S`.
-/
import Mathlib

namespace JointRootCert

open Finset

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- Global optimum `μ_* = max_{z ∈ Z} f z`. -/
noncomputable def gmax (f : Z → ℝ) : ℝ := univ.sup' univ_nonempty f

/-- Root value `V(a) = max_{z ∈ S(a)} f z` of a commitment with nonempty support `S`. -/
noncomputable def val (S : Finset Z) (hS : S.Nonempty) (f : Z → ℝ) : ℝ := S.sup' hS f

/-- Regret `r_f(a) = μ_* - V(a)` of a commitment (`eq:true-value`). -/
noncomputable def regret (S : Finset Z) (hS : S.Nonempty) (f : Z → ℝ) : ℝ :=
  gmax f - val S hS f

/-- Advantage of a challenger `z` over the best retained terminal,
`min_{y ∈ S} (f z - f y)`. -/
noncomputable def adv (S : Finset Z) (hS : S.Nonempty) (f : Z → ℝ) (z : Z) : ℝ :=
  S.inf' hS (fun y => f z - f y)

variable {S : Finset Z} {hS : S.Nonempty} {f : Z → ℝ} {ε : ℝ}

lemma le_gmax (f : Z → ℝ) (z : Z) : f z ≤ gmax f := le_sup' f (mem_univ z)

lemma le_val (hS : S.Nonempty) (f : Z → ℝ) {y : Z} (hy : y ∈ S) : f y ≤ val S hS f :=
  le_sup' f hy

lemma val_le_gmax (S : Finset Z) (hS : S.Nonempty) (f : Z → ℝ) : val S hS f ≤ gmax f :=
  sup'_le _ _ (fun z _ => le_gmax f z)

lemma regret_nonneg (S : Finset Z) (hS : S.Nonempty) (f : Z → ℝ) : 0 ≤ regret S hS f :=
  sub_nonneg.mpr (val_le_gmax S hS f)

/-- The advantage is the challenger value minus the root value. -/
lemma adv_eq (S : Finset Z) (hS : S.Nonempty) (f : Z → ℝ) (z : Z) :
    adv S hS f z = f z - val S hS f := by
  apply le_antisymm
  · obtain ⟨y, hy, hval⟩ := exists_mem_eq_sup' hS f
    have h : adv S hS f z ≤ f z - f y := inf'_le (fun y => f z - f y) hy
    simpa [val, hval] using h
  · refine le_inf' _ _ (fun y hy => ?_)
    have := le_val hS f hy
    linarith

/-- **Outside--inside reduction for one environment.**  A commitment has regret at most
`ε` exactly when `ε ≥ 0` and no *excluded* terminal beats the root value by more than `ε`.
Retained terminals never count against the commitment. -/
lemma regret_le_iff :
    regret S hS f ≤ ε ↔ 0 ≤ ε ∧ ∀ z, z ∉ S → f z - val S hS f ≤ ε := by
  constructor
  · intro h
    refine ⟨(regret_nonneg S hS f).trans h, fun z _ => ?_⟩
    have := le_gmax f z
    unfold regret at h
    linarith
  · rintro ⟨h0, h⟩
    obtain ⟨z, -, hz⟩ := exists_mem_eq_sup' (univ_nonempty (α := Z)) f
    have hg : gmax f = f z := hz
    unfold regret
    by_cases hzS : z ∈ S
    · have := le_val hS f hzS
      linarith
    · have := h z hzS
      linarith

/-- A commitment that retains every terminal has zero regret in every environment:
no observation is needed. -/
lemma regret_univ (f : Z → ℝ) : regret univ univ_nonempty f = 0 := by
  simp [regret, gmax, val]

/-- Full support, stated for an arbitrary proof of nonemptiness. -/
lemma regret_eq_zero_of_compl_empty (hSc : Sᶜ = ∅) : regret S hS f = 0 := by
  apply le_antisymm _ (regret_nonneg S hS f)
  rw [regret_le_iff]
  refine ⟨le_rfl, fun z hz => ?_⟩
  have : z ∈ Sᶜ := mem_compl.mpr hz
  simp [hSc] at this

/-- Point regret of a proper support: `[max_{z ∉ S} f z - max_{y ∈ S} f y]_+`. -/
lemma regret_eq (hSc : Sᶜ.Nonempty) :
    regret S hS f = max 0 (Sᶜ.sup' hSc f - val S hS f) := by
  apply le_antisymm
  · rw [regret_le_iff]
    refine ⟨le_max_left _ _, fun z hz => ?_⟩
    have : f z ≤ Sᶜ.sup' hSc f := le_sup' f (mem_compl.mpr hz)
    exact le_max_of_le_right (by linarith)
  · refine max_le (regret_nonneg S hS f) ?_
    have : Sᶜ.sup' hSc f ≤ gmax f := sup'_le _ _ (fun z _ => le_gmax f z)
    unfold regret
    linarith

end JointRootCert
