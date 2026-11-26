/-
Feature-hull dominance (Theorem `thm:t2-hull`, Appendix A.4).

Features live in a real normed space `E` and parameters are continuous linear
functionals `θ` on `E`, so that `f_θ(z) = θ (φ z)`.  For `E = ℝ^d` this is the pairing
`φ_zᵀ θ` of the manuscript, and the operator norm of `θ` is the dual norm `‖θ‖_*`.
-/
import JointRootCert.Rectangular

namespace JointRootCert

open Finset

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Finset Z} {hS : S.Nonempty} {φ : Z → E}

/-- The environment of a linear parameter. -/
def dualEnv (φ : Z → E) (θ : StrongDual ℝ E) : Z → ℝ := fun z => θ (φ z)

/-- A linear functional on the hull of the inside features is at most the root value. -/
lemma le_val_of_mem_hull (hS : S.Nonempty) (θ : StrongDual ℝ E) {w : E}
    (hw : w ∈ convexHull ℝ (φ '' (S : Set Z))) : θ w ≤ val S hS (dualEnv φ θ) := by
  have hconv : Convex ℝ {x : E | θ x ≤ val S hS (dualEnv φ θ)} :=
    convex_halfSpace_le θ.isLinear _
  refine convexHull_min ?_ hconv hw
  rintro _ ⟨y, hy, rfl⟩
  exact le_val hS (dualEnv φ θ) hy

/-- **Feature-hull dominance, exact part.**  A commitment is optimal for *every* linear
parameter iff the hull of all features is contained in the hull of the retained
features, `P_Z ⊆ P_a`.  No observation can then change the decision. -/
theorem feature_hull_dominance (hS : S.Nonempty) (φ : Z → E) :
    (∀ θ : StrongDual ℝ E, val S hS (dualEnv φ θ) = gmax (dualEnv φ θ)) ↔
      convexHull ℝ (Set.range φ) ⊆ convexHull ℝ (φ '' (S : Set Z)) := by
  constructor
  · intro h
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro _ ⟨z, rfl⟩
    by_contra hz
    have hfin : (φ '' (S : Set Z)).Finite := (S.finite_toSet).image φ
    obtain ⟨θ, s, hlt, hs⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (φ '' (S : Set Z))) (hfin.isCompact_convexHull (𝕜 := ℝ)).isClosed hz
    obtain ⟨y, hy, hval⟩ := exists_mem_eq_sup' hS (dualEnv φ θ)
    have h1 : val S hS (dualEnv φ θ) < s := by
      have : val S hS (dualEnv φ θ) = θ (φ y) := hval
      rw [this]
      exact hlt _ (subset_convexHull ℝ _ ⟨y, hy, rfl⟩)
    have h2 : θ (φ z) ≤ gmax (dualEnv φ θ) := le_gmax (dualEnv φ θ) z
    have := h θ
    linarith
  · intro h θ
    apply le_antisymm (val_le_gmax S hS _)
    refine sup'_le _ _ (fun z _ => ?_)
    exact le_val_of_mem_hull hS θ (h (subset_convexHull ℝ _ ⟨z, rfl⟩))

/-- **Feature-hull dominance, approximate part.**  If every excluded feature is within
distance `η` of the hull of the retained features, then every parameter with dual norm
`‖θ‖_* ≤ B` gives regret at most `B η`. -/
theorem regret_le_of_hull_dist (hS : S.Nonempty) (φ : Z → E) {η B : ℝ} (hη : 0 ≤ η)
    (hdist : ∀ z, z ∉ S → ∃ w ∈ convexHull ℝ (φ '' (S : Set Z)), ‖φ z - w‖ ≤ η)
    {θ : StrongDual ℝ E} (hθ : ‖θ‖ ≤ B) :
    regret S hS (dualEnv φ θ) ≤ B * η := by
  have hB : 0 ≤ B := (norm_nonneg θ).trans hθ
  rw [regret_le_iff]
  refine ⟨mul_nonneg hB hη, fun z hz => ?_⟩
  obtain ⟨w, hw, hwd⟩ := hdist z hz
  have h1 : θ w ≤ val S hS (dualEnv φ θ) := le_val_of_mem_hull hS θ hw
  have h2 : θ (φ z) - θ w ≤ ‖θ‖ * ‖φ z - w‖ := by
    rw [← map_sub]
    exact (le_abs_self _).trans (θ.le_opNorm _)
  have h3 : ‖θ‖ * ‖φ z - w‖ ≤ B * η := mul_le_mul hθ hwd (norm_nonneg _) hB
  have : dualEnv φ θ z = θ (φ z) := rfl
  linarith

end JointRootCert
