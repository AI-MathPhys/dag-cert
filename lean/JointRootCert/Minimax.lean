/-
The finite-dimensional minimax identity behind the ellipsoidal certificate
(proof of Theorem `thm:bay-main-dual`, Appendix A.3):

  max_{‖u‖ ≤ β} min_y (b_y + ⟨c_y, u⟩)
      = min_{p ∈ Δ} [ ∑_y p_y b_y + β ‖∑_y p_y c_y‖ ].

The manuscript invokes Sion's minimax theorem.  Here the identity is proved directly
from the Hahn--Banach separation theorem available in Mathlib: a compact convex set of
attainable advantage vectors is separated from the closed convex orthant of vectors that
are everywhere at least the dual optimum.
-/
import JointRootCert.Rectangular

namespace JointRootCert

open Finset
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The probability simplex `Δ(ι)`. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {p | (∀ y, 0 ≤ p y) ∧ ∑ y, p y = 1}

lemma isCompact_simplex (ι : Type*) [Fintype ι] : IsCompact (simplex ι) := by
  have hcl : IsClosed (simplex ι) := by
    have : simplex ι = (⋂ y, {p : ι → ℝ | 0 ≤ p y}) ∩ {p | ∑ y, p y = 1} := by
      ext p; simp [simplex]
    rw [this]
    exact (isClosed_iInter (fun y => isClosed_le continuous_const (continuous_apply y))).inter
      (isClosed_eq (by fun_prop) continuous_const)
  refine (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset
    hcl ?_
  intro p hp y _
  refine ⟨hp.1 y, ?_⟩
  rw [← hp.2]
  exact single_le_sum (fun i _ => hp.1 i) (mem_univ y)

lemma single_mem_simplex [DecidableEq ι] (i : ι) : Pi.single i (1 : ℝ) ∈ simplex ι := by
  refine ⟨fun y => ?_, by simp⟩
  by_cases h : y = i <;> simp [Pi.single_apply, h]

/-- The dual objective `∑_y p_y b_y + β ‖∑_y p_y c_y‖`. -/
noncomputable def dualObj (b : ι → ℝ) (c : ι → F) (β : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ y, p y * b y + β * ‖∑ y, p y • c y‖

lemma continuous_dualObj (b : ι → ℝ) (c : ι → F) (β : ℝ) : Continuous (dualObj b c β) := by
  unfold dualObj
  fun_prop

/-- The mixture value of the primal payoffs. -/
lemma sum_mul_payoff (b : ι → ℝ) (c : ι → F) (p : ι → ℝ) (u : F) :
    ∑ y, p y * (b y + ⟪c y, u⟫) = ∑ y, p y * b y + ⟪∑ y, p y • c y, u⟫ := by
  rw [sum_inner, ← sum_add_distrib]
  refine sum_congr rfl (fun y _ => ?_)
  rw [real_inner_smul_left]
  ring

/-- Every mixture bounds the mixed payoff of every point of the ball. -/
lemma sum_mul_payoff_le (b : ι → ℝ) (c : ι → F) {β : ℝ} {u : F} (hu : ‖u‖ ≤ β)
    (p : ι → ℝ) : ∑ y, p y * (b y + ⟪c y, u⟫) ≤ dualObj b c β p := by
  rw [sum_mul_payoff, dualObj]
  have h1 : ⟪∑ y, p y • c y, u⟫ ≤ ‖∑ y, p y • c y‖ * ‖u‖ := real_inner_le_norm _ _
  have h2 : ‖∑ y, p y • c y‖ * ‖u‖ ≤ β * ‖∑ y, p y • c y‖ := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)
  linarith

/-- **Weak duality: a feasible mixture is a certifying upper bound.**  For every `u` in
the ball and every mixture `p`, some retained terminal has payoff at most the dual
objective at `p`.  No optimality of `p` is needed, and the covariance may be singular. -/
theorem weak_duality (b : ι → ℝ) (c : ι → F) {β : ℝ} {u : F} (hu : ‖u‖ ≤ β)
    {p : ι → ℝ} (hp : p ∈ simplex ι) : ∃ y, b y + ⟪c y, u⟫ ≤ dualObj b c β p := by
  by_contra hcon
  push Not at hcon
  have hle := sum_mul_payoff_le b c hu p
  have hpos : ∃ y, 0 < p y := by
    by_contra h
    push Not at h
    have : ∑ y, p y ≤ 0 := sum_nonpos (fun y _ => h y)
    linarith [hp.2]
  obtain ⟨y₀, hy₀⟩ := hpos
  have hlt : ∑ y, p y * dualObj b c β p < ∑ y, p y * (b y + ⟪c y, u⟫) := by
    refine sum_lt_sum (fun y _ => mul_le_mul_of_nonneg_left (hcon y).le (hp.1 y))
      ⟨y₀, mem_univ _, mul_lt_mul_of_pos_left (hcon y₀) hy₀⟩
  rw [← sum_mul, hp.2, one_mul] at hlt
  linarith

variable [FiniteDimensional ℝ F]

/-- A point of the ball of radius `β` aligned with `w`: its inner product with `w` is
`β ‖w‖`. -/
lemma exists_aligned (w : F) {β : ℝ} (hβ : 0 ≤ β) : ∃ u : F, ‖u‖ ≤ β ∧ ⟪w, u⟫ = β * ‖w‖ := by
  by_cases hw : w = 0
  · exact ⟨0, by simpa using hβ, by simp [hw]⟩
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    refine ⟨(β / ‖w‖) • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hβ hn.le),
        div_mul_cancel₀ _ hn.ne']
    · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp

/-- **Strong duality.**  The dual objective has a minimiser `p` over the simplex, and
there is a point `u` of the ball at which *every* payoff is at least the dual optimum.
Together with weak duality this is the minimax identity, with both optima attained. -/
theorem strong_duality [Nonempty ι] (b : ι → ℝ) (c : ι → F) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ p ∈ simplex ι, ∃ u : F, ‖u‖ ≤ β ∧
      (∀ q ∈ simplex ι, dualObj b c β p ≤ dualObj b c β q) ∧
      ∀ y, dualObj b c β p ≤ b y + ⟪c y, u⟫ := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hne : (simplex ι).Nonempty := ⟨_, single_mem_simplex i₀⟩
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_simplex ι).exists_isMinOn hne (continuous_dualObj b c β).continuousOn
  have hmin' : ∀ q ∈ simplex ι, dualObj b c β p ≤ dualObj b c β q := fun q hq => hmin hq
  refine ⟨p, hp, ?_⟩
  set v := dualObj b c β p with hv
  by_contra hno
  have hno' : ∀ u : F, ‖u‖ ≤ β → ∃ y, b y + ⟪c y, u⟫ < v := by
    intro u hu
    by_contra h
    push Not at h
    exact hno ⟨u, hu, hmin', h⟩
  -- attainable payoff vectors and the orthant above the dual optimum
  let pay : F → ι → ℝ := fun u y => b y + ⟪c y, u⟫
  let K : Set (ι → ℝ) := pay '' Metric.closedBall 0 β
  let T : Set (ι → ℝ) := {a | ∀ y, v ≤ a y}
  have hKc : IsCompact K :=
    (isCompact_closedBall (0 : F) β).image (by fun_prop)
  have hKconv : Convex ℝ K := by
    rintro _ ⟨u₁, h₁, rfl⟩ _ ⟨u₂, h₂, rfl⟩ s t hs ht hst
    refine ⟨s • u₁ + t • u₂, convex_closedBall (0 : F) β h₁ h₂ hs ht hst, ?_⟩
    funext y
    simp only [pay, Pi.add_apply, Pi.smul_apply, smul_eq_mul, inner_add_right,
      real_inner_smul_right]
    linear_combination (-(b y)) * hst
  have hTcl : IsClosed T := by
    have : T = ⋂ y, {a : ι → ℝ | v ≤ a y} := by
      ext a; simp [T]
    rw [this]
    exact isClosed_iInter (fun y => isClosed_le continuous_const (continuous_apply y))
  have hTconv : Convex ℝ T := by
    intro a ha a' ha' s t hs ht hst y
    have h1 := ha y
    have h2 := ha' y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ hT
    obtain ⟨y, hy⟩ := hno' u (by simpa using hu)
    exact absurd (hT y) (not_le.mpr hy)
  obtain ⟨f, s', t', hKs, hst', hTt⟩ :=
    geometric_hahn_banach_compact_closed hKc hKconv hTcl hTconv hdisj
  -- coordinates of the separating functional
  let e : ι → ι → ℝ := fun y j => if y = j then 1 else 0
  let q : ι → ℝ := fun y => f (e y)
  have hf : ∀ a : ι → ℝ, f a = ∑ y, a y * q y := by
    intro a
    have := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) a
    simpa [q, e, smul_eq_mul] using this
  have hconst : (fun _ : ι => v) ∈ T := fun _ => le_rfl
  have hq : ∀ y, 0 ≤ q y := by
    intro y
    by_contra hneg
    push Not at hneg
    set κ := f (fun _ : ι => v) with hκ
    set n := max 0 ((κ - t') / (-q y)) with hn
    have hn0 : 0 ≤ n := le_max_left _ _
    have hmem : (fun _ : ι => v) + n • e y ∈ T := by
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
      split_ifs <;> nlinarith
    have hval : f ((fun _ : ι => v) + n • e y) = κ + n * q y := by
      rw [map_add, map_smul, smul_eq_mul]
    have hbig : κ - t' ≤ n * (-q y) := by
      have : (κ - t') / (-q y) ≤ n := le_max_right _ _
      exact (div_le_iff₀ (by linarith)).mp this
    have := hTt _ hmem
    rw [hval] at this
    linarith
  set Q := ∑ y, q y with hQ
  have hQ0 : 0 ≤ Q := sum_nonneg (fun y _ => hq y)
  set w := ∑ y, q y • c y with hw
  -- homogeneity: the unnormalised dual objective is at least `v * Q`
  have hstar : v * Q ≤ ∑ y, q y * b y + β * ‖w‖ := by
    rcases hQ0.eq_or_lt with hzero | hpos
    · have hall : ∀ y, q y = 0 := by
        intro y
        have := (sum_eq_zero_iff_of_nonneg (fun y _ => hq y)).mp hzero.symm y (mem_univ y)
        exact this
      simp [hw, hall, ← hzero]
    · have hp' : (fun y => q y / Q) ∈ simplex ι := by
        refine ⟨fun y => div_nonneg (hq y) hQ0, ?_⟩
        rw [← sum_div, div_self hpos.ne']
      have h := hmin' _ hp'
      have hobj : dualObj b c β (fun y => q y / Q) = (∑ y, q y * b y + β * ‖w‖) / Q := by
        unfold dualObj
        have h1 : ∑ y, q y / Q * b y = (∑ y, q y * b y) / Q := by
          rw [sum_div]
          exact sum_congr rfl (fun y _ => by ring)
        have h2 : ∑ y, (q y / Q) • c y = (1 / Q) • w := by
          rw [hw, smul_sum]
          refine sum_congr rfl (fun y _ => ?_)
          rw [smul_smul]
          congr 1
          ring
        rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
      rw [hobj, le_div_iff₀ hpos] at h
      exact h
  obtain ⟨u, hu, hu'⟩ := exists_aligned w hβ
  have hK : pay u ∈ K := ⟨u, by simpa using hu, rfl⟩
  have h1 := hKs _ hK
  have h2 := hTt _ hconst
  rw [hf] at h1 h2
  have h3 : ∑ y, pay u y * q y = ∑ y, q y * b y + β * ‖w‖ := by
    have := sum_mul_payoff b c q u
    rw [← hw, hu'] at this
    rw [← this]
    exact sum_congr rfl (fun y _ => by simp only [pay]; ring)
  have h4 : ∑ y, (fun _ : ι => v) y * q y = v * Q := by
    rw [hQ, mul_sum]
  rw [h3] at h1
  rw [h4] at h2
  linarith

/-- **Minimax identity.**  The best worst-case payoff over the ball equals the least dual
objective over the simplex, and both are attained. -/
theorem minimax_ball [Nonempty ι] (b : ι → ℝ) (c : ι → F) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ D : ℝ,
      IsGreatest ((fun u : F => univ.inf' univ_nonempty (fun y => b y + ⟪c y, u⟫)) ''
        Metric.closedBall 0 β) D ∧
      IsLeast (dualObj b c β '' simplex ι) D := by
  obtain ⟨p, hp, u, hu, hmin, hall⟩ := strong_duality b c hβ
  refine ⟨dualObj b c β p, ⟨⟨u, by simpa using hu, ?_⟩, ?_⟩, ⟨p, hp, rfl⟩, ?_⟩
  · apply le_antisymm
    · obtain ⟨y, hy⟩ := weak_duality b c hu hp
      exact (inf'_le _ (mem_univ y)).trans hy
    · exact le_inf' _ _ (fun y _ => hall y)
  · rintro _ ⟨u', hu', rfl⟩
    obtain ⟨y, hy⟩ := weak_duality b c (u := u') (by simpa using hu') hp
    exact (inf'_le _ (mem_univ y)).trans hy
  · rintro _ ⟨q, hq, rfl⟩
    exact hmin q hq

end JointRootCert
