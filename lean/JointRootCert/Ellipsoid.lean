/-
Exact joint ellipsoidal certificate (Theorem `thm:bay-main-dual`, Section 2.2 and
Appendix A.3).

Terminal values are linear in fixed features, `f_θ(z) = ⟨φ z, θ⟩`, and the parameter
ranges over the ellipsoid `Θ = m + L (B₂(β))`.  The worst-case advantage of an excluded
challenger `z` over a support `S` is

  D(z, S) = min_{p ∈ Δ(S)} [ ⟨g_{z,p}, m⟩ + β ‖Lᵀ g_{z,p}‖ ],   g_{z,p} = φ z - ∑_{y ∈ S} p_y φ y,

and the worst-case regret is `[max_{z ∉ S} D(z, S)]_+`.  No rank condition on `L` is used.
-/
import JointRootCert.Minimax

namespace JointRootCert

open Finset
open scoped RealInnerProductSpace

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The environment induced by a parameter: `f_θ(z) = ⟨φ z, θ⟩`. -/
def env (φ : Z → E) (θ : E) : Z → ℝ := fun z => ⟪φ z, θ⟫

/-- The parameter ellipsoid `Θ = m + L (B₂(β))`. -/
def ellipsoid (m : E) (L : F →ₗ[ℝ] E) (β : ℝ) : Set E :=
  (fun u => m + L u) '' Metric.closedBall 0 β

/-- The contrast `g_{z,p} = φ z - ∑_{y ∈ S} p_y φ y` of a challenger against an inside
mixture. -/
def contrast (φ : Z → E) (S : Finset Z) (z : Z) (p : S → ℝ) : E :=
  φ z - ∑ y, p y • φ y

/-- The dual objective `⟨g_{z,p}, m⟩ + β ‖Lᵀ g_{z,p}‖`: estimated advantage plus the
uncertainty of that same contrast. -/
noncomputable def ellObj (φ : Z → E) (S : Finset Z) (m : E) (L : F →ₗ[ℝ] E) (β : ℝ)
    (z : Z) (p : S → ℝ) : ℝ :=
  ⟪contrast φ S z p, m⟫ + β * ‖LinearMap.adjoint L (contrast φ S z p)‖

variable {S : Finset Z} {hS : S.Nonempty} {φ : Z → E} {m : E} {L : F →ₗ[ℝ] E} {β ε : ℝ}

/-- Outside--inside difference at a point of the ellipsoid. -/
lemma payoff_eq (φ : Z → E) (m : E) (L : F →ₗ[ℝ] E) (z y : Z) (u : F) :
    env φ (m + L u) z - env φ (m + L u) y =
      ⟪φ z - φ y, m⟫ + ⟪LinearMap.adjoint L (φ z - φ y), u⟫ := by
  simp only [env]
  rw [LinearMap.adjoint_inner_left, ← inner_sub_left, inner_add_right]

/-- On the simplex, the abstract dual objective is the contrast objective. -/
lemma dualObj_eq_ellObj (φ : Z → E) (S : Finset Z) (m : E) (L : F →ₗ[ℝ] E) (β : ℝ) (z : Z)
    {p : S → ℝ} (hp : p ∈ simplex S) :
    dualObj (fun y : S => ⟪φ z - φ y, m⟫) (fun y : S => LinearMap.adjoint L (φ z - φ y)) β p =
      ellObj φ S m L β z p := by
  have h1 : ∑ y : S, p y * ⟪φ z - φ y, m⟫ = ⟪contrast φ S z p, m⟫ := by
    simp only [contrast, inner_sub_left, sum_inner, real_inner_smul_left, mul_sub, sum_sub_distrib]
    rw [← sum_mul, hp.2, one_mul]
  have h2 : ∑ y : S, p y • LinearMap.adjoint L (φ z - φ y) =
      LinearMap.adjoint L (contrast φ S z p) := by
    simp only [contrast, map_sub, map_sum, map_smul, smul_sub, sum_sub_distrib]
    rw [← sum_smul, hp.2, one_smul]
  rw [dualObj, ellObj, h1, h2]

/-- **Any feasible mixture is a certifying upper bound** (last claim of
Theorem `thm:bay-main-dual`): for every parameter in the ellipsoid and every inside
mixture `p`, the challenger's advantage is at most the contrast objective at `p`.
Optimality of `p` is not required, and `L` may be singular. -/
theorem adv_le_ellObj (hS : S.Nonempty) (z : Z) {θ : E} (hθ : θ ∈ ellipsoid m L β)
    {p : S → ℝ} (hp : p ∈ simplex S) :
    adv S hS (env φ θ) z ≤ ellObj φ S m L β z p := by
  obtain ⟨u, hu, rfl⟩ := hθ
  have hu' : ‖u‖ ≤ β := by simpa using hu
  obtain ⟨y, hy⟩ := weak_duality (fun y : S => ⟪φ z - φ y, m⟫)
    (fun y : S => LinearMap.adjoint L (φ z - φ y)) hu' hp
  rw [dualObj_eq_ellObj φ S m L β z hp] at hy
  refine le_trans ?_ hy
  have h : adv S hS (env φ (m + L u)) z ≤ env φ (m + L u) z - env φ (m + L u) y :=
    inf'_le (fun y => env φ (m + L u) z - env φ (m + L u) y) y.2
  rw [payoff_eq] at h
  exact h

/-- **Exact ellipsoidal advantage.**  For `β ≥ 0` the worst-case advantage of a
challenger over the ellipsoid equals the least contrast objective over inside mixtures;
the maximum over parameters and the minimum over mixtures are both attained. -/
theorem ellipsoid_adv_exact (hS : S.Nonempty) (hβ : 0 ≤ β) (φ : Z → E) (m : E)
    (L : F →ₗ[ℝ] E) (z : Z) :
    ∃ D : ℝ,
      IsGreatest ((fun θ => adv S hS (env φ θ) z) '' ellipsoid m L β) D ∧
      IsLeast (ellObj φ S m L β z '' simplex S) D := by
  have : Nonempty S := hS.to_subtype
  obtain ⟨p, hp, u, hu, hmin, hall⟩ := strong_duality (fun y : S => ⟪φ z - φ y, m⟫)
    (fun y : S => LinearMap.adjoint L (φ z - φ y)) hβ
  have hθ : m + L u ∈ ellipsoid m L β := ⟨u, by simpa using hu, rfl⟩
  refine ⟨ellObj φ S m L β z p, ⟨⟨m + L u, hθ, ?_⟩, ?_⟩, ⟨p, hp, rfl⟩, ?_⟩
  · apply le_antisymm (adv_le_ellObj hS z hθ hp)
    refine le_inf' _ _ (fun y hy => ?_)
    rw [payoff_eq, ← dualObj_eq_ellObj φ S m L β z hp]
    exact hall ⟨y, hy⟩
  · rintro _ ⟨θ, hθ', rfl⟩
    exact adv_le_ellObj hS z hθ' hp
  · rintro _ ⟨q, hq, rfl⟩
    have := hmin q hq
    rwa [dualObj_eq_ellObj φ S m L β z hp, dualObj_eq_ellObj φ S m L β z hq] at this

/-- **Exact joint ellipsoidal certificate (Theorem `thm:bay-main-dual`), certificate
form.**  A commitment is `ε`-acceptable throughout the ellipsoid iff `ε ≥ 0` and every
excluded challenger admits an inside mixture whose contrast objective is at most `ε`.
Equivalently `R(a) = [max_{z ∉ S(a)} D(z, S(a))]_+ ≤ ε` with
`D(z, S) = min_{p ∈ Δ(S)} [⟨g_{z,p}, m⟩ + β ‖Lᵀ g_{z,p}‖]`. -/
theorem ellipsoid_certificate_iff (hS : S.Nonempty) (hβ : 0 ≤ β) (φ : Z → E) (m : E)
    (L : F →ₗ[ℝ] E) :
    (∀ θ ∈ ellipsoid m L β, regret S hS (env φ θ) ≤ ε) ↔
      0 ≤ ε ∧ ∀ z, z ∉ S → ∃ p ∈ simplex S, ellObj φ S m L β z p ≤ ε := by
  have hne : (env φ '' ellipsoid m L β).Nonempty :=
    ⟨_, ⟨m + L 0, ⟨0, by simpa using hβ, rfl⟩, rfl⟩⟩
  have key := robust_regret_le_iff (S := S) (hS := hS) (ε := ε) (env φ '' ellipsoid m L β) hne
  constructor
  · intro h
    obtain ⟨h0, hadv⟩ := key.mp (by rintro _ ⟨θ, hθ, rfl⟩; exact h θ hθ)
    refine ⟨h0, fun z hz => ?_⟩
    obtain ⟨D, ⟨⟨θ, hθ, hθD⟩, -⟩, ⟨⟨p, hp, hpD⟩, -⟩⟩ := ellipsoid_adv_exact hS hβ φ m L z
    refine ⟨p, hp, ?_⟩
    rw [hpD, ← hθD]
    exact hadv z hz _ ⟨θ, hθ, rfl⟩
  · rintro ⟨h0, h⟩ θ hθ
    refine key.mpr ⟨h0, ?_⟩ _ ⟨θ, hθ, rfl⟩
    rintro z hz _ ⟨θ', hθ', rfl⟩
    obtain ⟨p, hp, hle⟩ := h z hz
    exact (adv_le_ellObj hS z hθ' hp).trans hle

/-- The dual value `D(z, S) = min_{p ∈ Δ(S)} [⟨g_{z,p}, m⟩ + β ‖Lᵀ g_{z,p}‖]`. -/
noncomputable def ellD (φ : Z → E) (S : Finset Z) (m : E) (L : F →ₗ[ℝ] E) (β : ℝ) (z : Z) : ℝ :=
  sInf (ellObj φ S m L β z '' simplex S)

/-- The robust advantage over the ellipsoid is the dual value. -/
theorem robustAdv_ellipsoid (hS : S.Nonempty) (hβ : 0 ≤ β) (φ : Z → E) (m : E)
    (L : F →ₗ[ℝ] E) (z : Z) :
    robustAdv S hS (env φ '' ellipsoid m L β) z = ellD φ S m L β z := by
  obtain ⟨D, hG, hL⟩ := ellipsoid_adv_exact hS hβ φ m L z
  have h1 : (fun f => adv S hS f z) '' (env φ '' ellipsoid m L β) =
      (fun θ => adv S hS (env φ θ) z) '' ellipsoid m L β := by
    rw [Set.image_image]
  rw [robustAdv, h1, hG.csSup_eq, ellD, hL.csInf_eq]

/-- **Exact joint ellipsoidal certificate (Theorem `thm:bay-main-dual`), value form:**
`R(a) = [max_{z ∉ S(a)} D(z, S(a))]_+` for every proper support. -/
theorem robustRegret_ellipsoid (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hβ : 0 ≤ β)
    (φ : Z → E) (m : E) (L : F →ₗ[ℝ] E) :
    robustRegret S hS (env φ '' ellipsoid m L β) =
      max 0 (Sᶜ.sup' hSc (ellD φ S m L β)) := by
  have hne : (env φ '' ellipsoid m L β).Nonempty :=
    ⟨_, ⟨m + L 0, ⟨0, by simpa using hβ, rfl⟩, rfl⟩⟩
  have hB : BddAbove (regret S hS '' (env φ '' ellipsoid m L β)) := by
    refine ⟨max 0 (Sᶜ.sup' hSc (ellD φ S m L β)), ?_⟩
    rintro _ ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    rw [regret_le_iff]
    refine ⟨le_max_left _ _, fun z hz => ?_⟩
    rw [← adv_eq]
    obtain ⟨D, hG, hL⟩ := ellipsoid_adv_exact hS hβ φ m L z
    have h1 : adv S hS (env φ θ) z ≤ D := hG.2 ⟨θ, hθ, rfl⟩
    have h2 : ellD φ S m L β z = D := hL.csInf_eq
    have h3 : ellD φ S m L β z ≤ Sᶜ.sup' hSc (ellD φ S m L β) :=
      le_sup' _ (mem_compl.mpr hz)
    exact le_max_of_le_right (by linarith)
  rw [robustRegret_eq _ hne hB hSc]
  congr 1
  exact sup'_congr hSc rfl (fun z _ => robustAdv_ellipsoid hS hβ φ m L z)

end JointRootCert
