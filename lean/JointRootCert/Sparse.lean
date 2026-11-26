/-
Sparse witnesses (second claim of Theorem `thm:bay-main-dual`, Appendix A.3).

At a primal--dual optimal pair, positive weights sit only on retained terminals that are
tied at the optimum.  On that active set the linear part of the objective is an affine
function of the uncertainty-space contrast, so Carathéodory's theorem replaces the
mixture by one supported on an affinely independent family, of size at most
`rank(L) + 1`, without changing the objective.
-/
import JointRootCert.Ellipsoid

namespace JointRootCert

open Finset
open scoped RealInnerProductSpace

section Abstract

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Pushing weights on an index family `κ` forward along `y : κ → ι`. -/
lemma sum_push_smul {κ M : Type*} [Fintype κ] [DecidableEq ι] [AddCommMonoid M] [Module ℝ M]
    (y : κ → ι) (w : κ → ℝ) (g : ι → M) :
    ∑ i, (∑ k, if y k = i then w k else 0) • g i = ∑ k, w k • g (y k) := by
  simp_rw [sum_smul, ite_smul, zero_smul]
  rw [sum_comm]
  simp

variable [FiniteDimensional ℝ F]

/-- **Sparse optimal mixtures.**  If all uncertainty-space vectors `c y` lie in a subspace
`W`, some minimiser of the dual objective has at most `dim W + 1` nonzero weights. -/
theorem sparse_optimal [Nonempty ι] [DecidableEq ι] (b : ι → ℝ) (c : ι → F) {β : ℝ}
    (hβ : 0 ≤ β) (W : Submodule ℝ F) (hW : ∀ y, c y ∈ W) :
    ∃ p ∈ simplex ι, (∀ q ∈ simplex ι, dualObj b c β p ≤ dualObj b c β q) ∧
      (univ.filter (fun y => p y ≠ 0)).card ≤ Module.finrank ℝ W + 1 := by
  obtain ⟨p, hp, u, hu, hmin, hall⟩ := strong_duality b c hβ
  set D := dualObj b c β p with hD
  set w := ∑ y, p y • c y with hw
  -- the mixed payoff equals the optimum, so positive weights are on tied terminals
  have hsum_le : ∑ y, p y * (b y + ⟪c y, u⟫) ≤ D := sum_mul_payoff_le b c hu p
  have hsum_ge : D ≤ ∑ y, p y * (b y + ⟪c y, u⟫) := by
    have : ∑ y, p y * D ≤ ∑ y, p y * (b y + ⟪c y, u⟫) :=
      sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hall y) (hp.1 y))
    rwa [← sum_mul, hp.2, one_mul] at this
  have hsum : ∑ y, p y * (b y + ⟪c y, u⟫) = D := le_antisymm hsum_le hsum_ge
  have hzero : ∑ y, p y * (b y + ⟪c y, u⟫ - D) = 0 := by
    simp only [mul_sub, sum_sub_distrib]
    rw [hsum, ← sum_mul, hp.2, one_mul, sub_self]
  have htied : ∀ y, 0 < p y → b y + ⟪c y, u⟫ = D := by
    intro y hy
    have h0 := (sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hp.1 y) (sub_nonneg.mpr (hall y)))).mp hzero y (mem_univ y)
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hy.ne'
    · linarith
  have hDw : D = ∑ y, p y * b y + ⟪w, u⟫ := by
    rw [← hsum, sum_mul_payoff]
  -- the uncertainty-space contrast lies in the hull of the active vectors
  let A : Set ι := {y | 0 < p y}
  have hmem : w ∈ convexHull ℝ (c '' A) := by
    have h1 : ∑ y ∈ univ.filter (fun y => 0 < p y), p y • c y = w := by
      rw [hw]
      refine sum_filter_of_ne (fun y _ hne => ?_)
      have : p y ≠ 0 := fun h => hne (by rw [h, zero_smul])
      exact lt_of_le_of_ne (hp.1 y) (Ne.symm this)
    have h2 : ∑ y ∈ univ.filter (fun y => 0 < p y), p y = 1 := by
      rw [← hp.2]
      refine sum_filter_of_ne (fun y _ hne => lt_of_le_of_ne (hp.1 y) (Ne.symm hne))
    rw [← h1]
    refine (convex_convexHull ℝ (c '' A)).sum_mem (fun y _ => hp.1 y) h2 (fun y hy => ?_)
    exact subset_convexHull ℝ _ ⟨y, (mem_filter.mp hy).2, rfl⟩
  obtain ⟨κ, _, z, wt, hrange, haff, hpos, hone, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hmem
  have hch : ∀ k, ∃ y, 0 < p y ∧ c y = z k := fun k => hrange ⟨k, rfl⟩
  choose y hyA hyz using hch
  let p' : ι → ℝ := fun i => ∑ k, if y k = i then wt k else 0
  have hp'0 : ∀ i, 0 ≤ p' i := fun i =>
    sum_nonneg (fun k _ => by split_ifs <;> [exact (hpos k).le; exact le_rfl])
  have hp'1 : ∑ i, p' i = 1 := by
    have := sum_push_smul y wt (fun _ : ι => (1 : ℝ))
    simpa [smul_eq_mul, hone] using this
  have hp'c : ∑ i, p' i • c i = w := by
    rw [sum_push_smul y wt c, ← hcomb]
    exact sum_congr rfl (fun k _ => by rw [hyz k])
  have hp'b : ∑ i, p' i * b i = ∑ y, p y * b y := by
    have h1 : ∑ i, p' i * b i = ∑ k, wt k * b (y k) := by
      simpa [smul_eq_mul] using sum_push_smul y wt b
    have h2 : ∑ k, wt k * b (y k) = D - ⟪w, u⟫ := by
      have hb : ∀ k, b (y k) = D - ⟪z k, u⟫ := by
        intro k
        have := htied (y k) (hyA k)
        rw [hyz k] at this
        linarith
      simp only [hb, mul_sub, sum_sub_distrib]
      rw [← sum_mul, hone, one_mul, ← hcomb, sum_inner]
      simp only [real_inner_smul_left]
    rw [h1, h2, hDw]
    ring
  have hobj : dualObj b c β p' = D := by
    rw [hD]
    unfold dualObj
    rw [hp'b, hp'c]
  refine ⟨p', ⟨hp'0, hp'1⟩, fun q hq => by rw [hobj]; exact hmin q hq, ?_⟩
  -- support of the new mixture is the image of the affinely independent family
  have hsub : univ.filter (fun i => p' i ≠ 0) ⊆ univ.image y := by
    intro i hi
    rw [mem_filter] at hi
    by_contra hni
    apply hi.2
    refine sum_eq_zero (fun k _ => ?_)
    have hne : y k ≠ i := by
      rintro rfl
      exact hni (mem_image_of_mem y (mem_univ k))
    simp [hne]
  have hcard : Fintype.card κ ≤ Module.finrank ℝ W + 1 := by
    refine haff.card_le_finrank_succ.trans (Nat.succ_le_succ ?_)
    refine Submodule.finrank_mono ?_
    rw [vectorSpan_def]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨k', rfl⟩, rfl⟩
    rw [← hyz k, ← hyz k']
    exact W.sub_mem (hW _) (hW _)
  calc (univ.filter (fun i => p' i ≠ 0)).card ≤ (univ.image y).card := card_le_card hsub
    _ ≤ (univ : Finset κ).card := card_image_le
    _ = Fintype.card κ := card_univ
    _ ≤ Module.finrank ℝ W + 1 := hcard

end Abstract

section Ellipsoid

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The range of the adjoint has the dimension of the range: `rank(Lᵀ) = rank(L)`. -/
lemma finrank_range_adjoint (L : F →ₗ[ℝ] E) :
    Module.finrank ℝ (LinearMap.range (LinearMap.adjoint L)) =
      Module.finrank ℝ (LinearMap.range L) := by
  rw [← LinearMap.orthogonal_ker]
  have h1 := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker L)
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  omega

/-- **Sparse witnesses (Theorem `thm:bay-main-dual`).**  For every challenger there is an
optimal inside mixture with at most `rank(L) + 1` nonzero entries. -/
theorem ellipsoid_sparse_witness {S : Finset Z} (hS : S.Nonempty) {β : ℝ} (hβ : 0 ≤ β)
    (φ : Z → E) (m : E) (L : F →ₗ[ℝ] E) (z : Z) :
    ∃ p ∈ simplex S, IsLeast (ellObj φ S m L β z '' simplex S) (ellObj φ S m L β z p) ∧
      (univ.filter (fun y => p y ≠ 0)).card ≤ Module.finrank ℝ (LinearMap.range L) + 1 := by
  have : Nonempty S := hS.to_subtype
  obtain ⟨p, hp, hmin, hcard⟩ := sparse_optimal (fun y : S => ⟪φ z - φ y, m⟫)
    (fun y : S => LinearMap.adjoint L (φ z - φ y)) hβ
    (LinearMap.range (LinearMap.adjoint L)) (fun y => LinearMap.mem_range_self _ _)
  refine ⟨p, hp, ⟨⟨p, hp, rfl⟩, ?_⟩, by rwa [finrank_range_adjoint] at hcard⟩
  rintro _ ⟨q, hq, rfl⟩
  have := hmin q hq
  rwa [dualObj_eq_ellObj φ S m L β z hp, dualObj_eq_ellObj φ S m L β z hq] at this

end Ellipsoid

end JointRootCert
