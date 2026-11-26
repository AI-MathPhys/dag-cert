/-
Known-variance Gaussian information limits and finite-confidence discovery and
confirmation (Appendix D, `app:known-gauss-info` and `app:bay-finite`).

Manuscript results covered, in whole or in part (see each doc comment and the summary at
the end of the file):

* `lem:bay-projection`            Lemma "Screened projection"
* `lem:bay-distance-certificate`  Lemma "Distance and certification"
* `thm:bay-main-optimal`          Theorem "Correlated Gaussian information limit"
                                  (deterministic and analytic cores only)
* `lem:bay-fc-inversion`          Lemma "Elementary logarithmic budget inversion"
* `thm:v10g-discovery`            Theorem "Explicit discovery and a frozen near-optimal plan"
* `prop:v10g-safety-fallback`     Proposition "Conditional safety and a finite-mean
                                  reference design"
* `thm:v10g-expectation`          Theorem "Correlated finite-confidence discovery and
                                  confirmation"
* `cor:v10g-target`               Corollary "Finite-confidence correlated confirmation bound"
* `prop:bay-finite`               Proposition "Finite-confidence discovery, frozen
                                  confirmation, and safeguard" (the main-text summary of the
                                  three preceding results)

Modelling.  Parameters live in a finite-dimensional real inner product space `E`.  The
design seminorm `‖v‖_{M(w)}`, `M(w) = ∑_x w_x u_x u_xᵀ`, is `‖A v‖` for a linear map `A`
(`designMap u w` is the concrete one, `norm_designMap_sq`); `M(w) ≻ 0` is injectivity of
`A`.  The root information `√(2 I_a(θ, w))` is `rootInfo A Q θ`, the distance from `A θ`
to `A '' Q`.  Probabilistic inputs (Gaussian tails, coverage of confidence sequences,
independence) are hypotheses of the measure-theoretic statements and are named there.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset
open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

section Geometry

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Strict invalidating alternatives of a root action: parameters whose regret exceeds
`ε` (the constraint set of `eq:bay-main-information`). -/
def strictAlt (φ : Z → E) (S : Finset Z) (hS : S.Nonempty) (ε : ℝ) : Set E :=
  {lam | ε < regret S hS (env φ lam)}

/-- The open component of an exterior terminal `z`: it beats every inside terminal by
more than `ε`. -/
def strictComp (φ : Z → E) (S : Finset Z) (ε : ℝ) (z : Z) : Set E :=
  {lam | ∀ y ∈ S, ε < ⟪φ z - φ y, lam⟫}

/-- The closed polyhedron `P_{a,z} = {λ : (φ_z - φ_y)ᵀ λ ≥ ε ∀ y ∈ S(a)}`. -/
def closedComp (φ : Z → E) (S : Finset Z) (ε : ℝ) (z : Z) : Set E :=
  {lam | ∀ y ∈ S, ε ≤ ⟪φ z - φ y, lam⟫}

/-- The hull screen `E_a`: exterior terminals whose feature is outside the hull of the
inside features. -/
def hullScreen (φ : Z → E) (S : Finset Z) : Set Z :=
  {z | z ∉ S ∧ φ z ∉ convexHull ℝ (φ '' (S : Set Z))}

variable {S : Finset Z} {φ : Z → E} {ε : ℝ} {z : Z}

lemma inner_sub_eq_env (φ : Z → E) (z y : Z) (lam : E) :
    ⟪φ z - φ y, lam⟫ = env φ lam z - env φ lam y := by
  simp [env, inner_sub_left]

/-- An action is incorrect exactly when some exterior terminal exceeds every inside
terminal by more than `ε`. -/
lemma mem_strictAlt_iff (hS : S.Nonempty) (hε : 0 ≤ ε) (lam : E) :
    lam ∈ strictAlt φ S hS ε ↔ ∃ z, z ∉ S ∧ lam ∈ strictComp φ S ε z := by
  simp only [strictAlt, Set.mem_ofPred_eq, strictComp]
  rw [← not_le, regret_le_iff]
  constructor
  · intro h
    by_contra hcon
    apply h
    refine ⟨hε, fun z hz => ?_⟩
    by_contra hlt
    apply hcon
    refine ⟨z, hz, fun y hy => ?_⟩
    push Not at hlt
    have h1 := le_val hS (env φ lam) hy
    rw [inner_sub_eq_env]
    linarith
  · rintro ⟨z, hz, hall⟩ ⟨-, h⟩
    obtain ⟨y, hy, hval⟩ := exists_mem_eq_sup' hS (env φ lam)
    have h1 := hall y hy
    have h3 : val S hS (env φ lam) = env φ lam y := hval
    have := h z hz
    rw [inner_sub_eq_env] at h1
    linarith

/-- **Hull screen** (`lem:bay-projection`, first step of the proof).  For `ε ≥ 0` the
strict inequalities of an exterior terminal `z` have a solution iff `φ_z` lies outside
the convex hull of the inside features. -/
theorem strictComp_nonempty_iff (hε : 0 ≤ ε) (z : Z) :
    (strictComp φ S ε z).Nonempty ↔ φ z ∉ convexHull ℝ (φ '' (S : Set Z)) := by
  constructor
  · rintro ⟨lam, hlam⟩ hz
    have hlin : IsLinearMap ℝ (fun x : E => ⟪x, lam⟫) :=
      ⟨fun x y => inner_add_left _ _ _, fun c x => by simp [real_inner_smul_left]⟩
    have hconv : Convex ℝ {x : E | ⟪x, lam⟫ < ⟪φ z, lam⟫ - ε} := convex_halfSpace_lt hlin _
    have hsub : φ '' (S : Set Z) ⊆ {x : E | ⟪x, lam⟫ < ⟪φ z, lam⟫ - ε} := by
      rintro _ ⟨y, hy, rfl⟩
      have := hlam y hy
      simp only [Set.mem_ofPred_eq]
      rw [inner_sub_left] at this
      linarith
    have hmem := convexHull_min hsub hconv hz
    simp only [Set.mem_ofPred_eq] at hmem
    linarith
  · intro hz
    have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
    have hfin : (φ '' (S : Set Z)).Finite := (S.finite_toSet).image φ
    obtain ⟨f, s, hlt, hs⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (φ '' (S : Set Z))) (hfin.isCompact_convexHull (𝕜 := ℝ)).isClosed hz
    set lam0 : E := (InnerProductSpace.toDual ℝ E).symm f with hlam0
    have hf : ∀ x, ⟪lam0, x⟫ = f x := fun x => InnerProductSpace.toDual_symm_apply
    have hgap : 0 < f (φ z) - s := sub_pos.mpr hs
    refine ⟨((ε + 1) / (f (φ z) - s)) • lam0, fun y hy => ?_⟩
    have h1 : f (φ y) < s := hlt _ (subset_convexHull ℝ _ ⟨y, hy, rfl⟩)
    have h0 : ⟪φ z - φ y, lam0⟫ = f (φ z) - f (φ y) := by
      rw [real_inner_comm, hf, map_sub]
    rw [real_inner_smul_right, h0]
    have h2 : f (φ z) - s ≤ f (φ z) - f (φ y) := by linarith
    calc ε < ε + 1 := by linarith
      _ = (ε + 1) / (f (φ z) - s) * (f (φ z) - s) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma isClosed_closedComp : IsClosed (closedComp φ S ε z) := by
  have : closedComp φ S ε z = ⋂ y ∈ S, {lam : E | ε ≤ ⟪φ z - φ y, lam⟫} := by
    ext lam; simp [closedComp]
  rw [this]
  exact isClosed_biInter (fun y _ => isClosed_le continuous_const (by fun_prop))

lemma strictComp_subset_closedComp : strictComp φ S ε z ⊆ closedComp φ S ε z :=
  fun _ hl y hy => (hl y hy).le

/-- **Closure of a strict component** (`lem:bay-projection`, second step).  If the strict
component is nonempty, its closure is exactly the closed polyhedron `P_{a,z}`. -/
theorem closure_strictComp (h : (strictComp φ S ε z).Nonempty) :
    closure (strictComp φ S ε z) = closedComp φ S ε z := by
  apply Set.Subset.antisymm
  · exact closure_minimal strictComp_subset_closedComp isClosed_closedComp
  · intro lam hlam
    obtain ⟨mu, hmu⟩ := h
    rw [Metric.mem_closure_iff]
    intro η hη
    set t := min 1 (η / (2 * (‖mu - lam‖ + 1))) with ht
    have hpos : 0 < ‖mu - lam‖ + 1 := by positivity
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    refine ⟨lam + t • (mu - lam), fun y hy => ?_, ?_⟩
    · have h1 := hlam y hy
      have h2 := hmu y hy
      rw [inner_add_right, real_inner_smul_right, inner_sub_right]
      nlinarith [mul_pos ht0 (sub_pos.mpr h2), mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h1)]
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht0.le]
      have h3 : t ≤ η / (2 * (‖mu - lam‖ + 1)) := min_le_right _ _
      calc t * ‖mu - lam‖ ≤ η / (2 * (‖mu - lam‖ + 1)) * ‖mu - lam‖ := by gcongr
        _ < η := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (mu - lam)]

/-- The strict alternative set is the union of the hull-screened strict components. -/
theorem strictAlt_eq_iUnion (hS : S.Nonempty) (hε : 0 ≤ ε) :
    strictAlt φ S hS ε = ⋃ z ∈ hullScreen φ S, strictComp φ S ε z := by
  ext lam
  rw [mem_strictAlt_iff hS hε]
  simp only [Set.mem_iUnion, exists_prop, hullScreen, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, hl⟩
    exact ⟨z, ⟨hz, (strictComp_nonempty_iff hε z).mp ⟨lam, hl⟩⟩, hl⟩
  · rintro ⟨z, ⟨hz, -⟩, hl⟩
    exact ⟨z, hz, hl⟩

/-- **Screened alternative set** `Q_a = ⋃_{z ∈ E_a} P_{a,z}`: the closure of the strict
alternatives is the union of the closed components over the hull screen. -/
theorem closure_strictAlt (hS : S.Nonempty) (hε : 0 ≤ ε) :
    closure (strictAlt φ S hS ε) = ⋃ z ∈ hullScreen φ S, closedComp φ S ε z := by
  rw [strictAlt_eq_iUnion hS hε, (Set.toFinite (hullScreen φ S)).closure_biUnion]
  refine Set.iUnion₂_congr (fun z hz => ?_)
  exact closure_strictComp ((strictComp_nonempty_iff hε z).mpr hz.2)

/-- **Screened projection, infimum form** (`lem:bay-projection`, first display).  A number
is a lower bound for the design distance from `θ` to the strict alternatives iff it is a
lower bound on every closed component `P_{a,z}`, `z ∈ E_a`.  Here `‖A v‖` is the design
seminorm `‖v‖_{M(w)}` (`A` may be singular), so the two infima coincide; with `E_a = ∅`
both sides are vacuous (`I_a = +∞`). -/
theorem screened_projection (hS : S.Nonempty) (hε : 0 ≤ ε) (A : E →ₗ[ℝ] F) (θ : E) (c : ℝ) :
    (∀ lam ∈ strictAlt φ S hS ε, c ≤ ‖A (lam - θ)‖) ↔
      ∀ z ∈ hullScreen φ S, ∀ lam ∈ closedComp φ S ε z, c ≤ ‖A (lam - θ)‖ := by
  have hcont : Continuous (fun lam : E => ‖A (lam - θ)‖) :=
    (A.continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)).norm
  have hcl : IsClosed {lam : E | c ≤ ‖A (lam - θ)‖} := isClosed_le continuous_const hcont
  constructor
  · intro h z hz lam hlam
    have hsub : closure (strictAlt φ S hS ε) ⊆ {lam : E | c ≤ ‖A (lam - θ)‖} :=
      closure_minimal (fun l hl => h l hl) hcl
    apply hsub
    rw [closure_strictAlt hS hε]
    exact Set.mem_biUnion hz hlam
  · intro h lam hlam
    have : lam ∈ closure (strictAlt φ S hS ε) := subset_closure hlam
    rw [closure_strictAlt hS hε] at this
    simp only [Set.mem_iUnion, exists_prop] at this
    obtain ⟨z, hz, hl⟩ := this
    exact h z hz lam hl

/-- **Universal actions** (`lem:bay-projection`): `E_a` is empty iff the action is optimal
for every parameter. -/
theorem hullScreen_eq_empty_iff (hS : S.Nonempty) :
    hullScreen φ S = ∅ ↔ ∀ θ : E, regret S hS (env φ θ) = 0 := by
  constructor
  · intro h θ
    apply le_antisymm _ (regret_nonneg S hS _)
    by_contra hcon
    push Not at hcon
    have hmem : θ ∈ strictAlt φ S hS 0 := hcon
    rw [strictAlt_eq_iUnion hS le_rfl, h] at hmem
    simp at hmem
  · intro h
    by_contra hne
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨lam, hlam⟩ := (strictComp_nonempty_iff (ε := 0) le_rfl z).mpr hz.2
    have : lam ∈ strictAlt φ S hS 0 := (mem_strictAlt_iff hS le_rfl lam).mpr ⟨z, hz.1, hlam⟩
    have h0 := h lam
    simp only [strictAlt, Set.mem_ofPred_eq] at this
    linarith

lemma continuous_regret_env (hS : S.Nonempty) (φ : Z → E) :
    Continuous (fun lam : E => regret S hS (env φ lam)) := by
  unfold regret gmax val env
  refine Continuous.sub ?_ ?_
  · exact Continuous.finset_sup'_apply univ_nonempty (fun z _ => by fun_prop)
  · exact Continuous.finset_sup'_apply hS (fun z _ => by fun_prop)

/-- Every strict alternative set is open. -/
lemma isOpen_strictAlt (hS : S.Nonempty) (φ : Z → E) (ε : ℝ) : IsOpen (strictAlt φ S hS ε) :=
  isOpen_lt continuous_const (continuous_regret_env hS φ)

/-- **Distance and certification** (`lem:bay-distance-certificate`).  Let the design be
positive definite (`A` injective, `‖A v‖ = ‖v‖_M`) and let `a` be acceptable at the
center.  Then `a` is `ε`-acceptable throughout the ellipsoid `{λ : ‖λ - θ‖_M ≤ β}` iff
`β` is a lower bound for the `M`-distance from `θ` to the strict alternatives, that is
`β² ≤ 2 inf_{λ : r_λ(a) > ε} ½ ‖λ - θ‖²_M`.  The infimum may be attained by the radius:
it is not attained inside the open alternative set. -/
theorem distance_certificate (hS : S.Nonempty) (A : E →ₗ[ℝ] F) (hA : Function.Injective A)
    {θ : E} {β : ℝ} (hθ : regret S hS (env φ θ) ≤ ε) :
    (∀ lam, ‖A (lam - θ)‖ ≤ β → regret S hS (env φ lam) ≤ ε) ↔
      ∀ lam ∈ strictAlt φ S hS ε, β ≤ ‖A (lam - θ)‖ := by
  constructor
  · intro h lam hlam
    by_contra hcon
    push Not at hcon
    have := h lam hcon.le
    simp only [strictAlt, Set.mem_ofPred_eq] at hlam
    linarith
  · intro h lam hle
    by_contra hcon
    push Not at hcon
    have hne : lam - θ ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0] at hcon
      linarith
    have hd : 0 < ‖A (lam - θ)‖ := by
      rw [norm_pos_iff]
      intro h0
      exact hne (hA (by rw [h0, map_zero]))
    -- move the alternative slightly toward the center
    have hpath : Continuous (fun t : ℝ => regret S hS (env φ (θ + t • (lam - θ)))) :=
      (continuous_regret_env hS φ).comp (by fun_prop)
    have hopen : IsOpen {t : ℝ | ε < regret S hS (env φ (θ + t • (lam - θ)))} :=
      isOpen_lt continuous_const hpath
    have h1 : (1 : ℝ) ∈ {t : ℝ | ε < regret S hS (env φ (θ + t • (lam - θ)))} := by
      simpa using hcon
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 1 h1
    set t : ℝ := 1 - min (r / 2) (1 / 2) with ht
    have hm0 : 0 < min (r / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
    have hm1 : min (r / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hm2 : min (r / 2) (1 / 2) ≤ r / 2 := min_le_left _ _
    have htmem : t ∈ Metric.ball (1 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, ht]
      rw [abs_lt]
      constructor <;> linarith
    have hstrict : θ + t • (lam - θ) ∈ strictAlt φ S hS ε := hball htmem
    have hb := h _ hstrict
    rw [add_sub_cancel_left, map_smul, norm_smul, Real.norm_of_nonneg (by linarith)] at hb
    nlinarith

/-- `lem:bay-distance-certificate` with the ellipsoid written as `θ + M^{-1/2} B₂(β)`,
the form used by the exact ellipsoidal certificate (`ellipsoid`). -/
theorem distance_certificate_ellipsoid [FiniteDimensional ℝ F] (hS : S.Nonempty)
    (A : E ≃ₗ[ℝ] F) {θ : E} {β : ℝ} (hθ : regret S hS (env φ θ) ≤ ε) :
    (∀ lam ∈ ellipsoid θ (A.symm : F →ₗ[ℝ] E) β, regret S hS (env φ lam) ≤ ε) ↔
      ∀ lam ∈ strictAlt φ S hS ε, β ≤ ‖A (lam - θ)‖ := by
  refine Iff.trans ?_ (distance_certificate hS (A : E →ₗ[ℝ] F) A.injective hθ)
  constructor
  · intro h lam hle
    refine h lam ⟨A (lam - θ), by simpa using hle, ?_⟩
    simp
  · rintro h _ ⟨u, hu, rfl⟩
    refine h _ ?_
    simpa using hu

end Geometry

/-! ### Attained component minima, including singular designs -/

section Attainment

universe u

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A convex quadratic `‖A v - c‖` attains its minimum on every nonempty polyhedron
`{v : b i ≤ ℓ i v, i ∈ s}`, with no rank condition on `A`.  Proved by induction on the
number of constraints: either the minimizer of the relaxed problem is feasible, or the
minimum is attained on the hyperplane of the dropped constraint. -/
theorem exists_min_polyhedron {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
      (A : V →ₗ[ℝ] F) (c : F) (ℓ : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ),
      (∃ v, ∀ i ∈ s, b i ≤ ℓ i v) →
      ∃ v, (∀ i ∈ s, b i ≤ ℓ i v) ∧
        ∀ w, (∀ i ∈ s, b i ≤ ℓ i w) → ‖A v - c‖ ≤ ‖A w - c‖ := by
  induction s using Finset.induction_on with
  | empty =>
    intro V _ _ _ A c ℓ b _
    have hcomp : IsComplete ((LinearMap.range A : Submodule ℝ F) : Set F) :=
      (LinearMap.range A).isComplete_of_finiteDimensional
    obtain ⟨y, hy, hmin⟩ :=
      Submodule.exists_norm_eq_iInf_of_complete_subspace (LinearMap.range A) hcomp c
    obtain ⟨v, rfl⟩ := hy
    refine ⟨v, by simp, fun w _ => ?_⟩
    rw [norm_sub_rev, hmin, norm_sub_rev (A w)]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
      (⟨A w, LinearMap.mem_range_self A w⟩ : ((LinearMap.range A : Submodule ℝ F) : Set F))
  | insert j s hj ih =>
    intro V _ _ _ A c ℓ b hfeas
    obtain ⟨v1, hv1⟩ := hfeas
    have hv1s : ∀ i ∈ s, b i ≤ ℓ i v1 := fun i hi => hv1 i (mem_insert_of_mem hi)
    have hv1j : b j ≤ ℓ j v1 := hv1 j (mem_insert_self j s)
    obtain ⟨v', hv'f, hv'min⟩ := ih V A c ℓ b ⟨v1, hv1s⟩
    by_cases hj' : b j ≤ ℓ j v'
    · refine ⟨v', ?_, fun w hw => hv'min w (fun i hi => hw i (mem_insert_of_mem hi))⟩
      intro i hi
      rcases mem_insert.mp hi with h | hi
      · rw [h]; exact hj'
      · exact hv'f i hi
    · push Not at hj'
      -- every feasible point can be moved onto the hyperplane without increasing the objective
      have cross : ∀ p, (∀ i ∈ s, b i ≤ ℓ i p) → b j ≤ ℓ j p →
          ∃ q, ℓ j q = b j ∧ (∀ i ∈ s, b i ≤ ℓ i q) ∧ ‖A q - c‖ ≤ ‖A p - c‖ := by
        intro p hps hpj
        have hden : 0 < ℓ j p - ℓ j v' := by linarith
        set t := (ℓ j p - b j) / (ℓ j p - ℓ j v') with ht
        have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
        refine ⟨p + t • (v' - p), ?_, fun i hi => ?_, ?_⟩
        · simp only [map_add, map_smul, map_sub, smul_eq_mul]
          rw [ht]; field_simp; ring
        · simp only [map_add, map_smul, map_sub, smul_eq_mul]
          nlinarith [hps i hi, hv'f i hi, mul_nonneg ht0 (sub_nonneg.mpr (hv'f i hi)),
            mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hps i hi))]
        · have h1 : A (p + t • (v' - p)) - c = (1 - t) • (A p - c) + t • (A v' - c) := by
            simp only [map_add, map_smul, map_sub, smul_sub, sub_smul, one_smul]
            abel
          rw [h1]
          calc ‖(1 - t) • (A p - c) + t • (A v' - c)‖
              ≤ (1 - t) * ‖A p - c‖ + t * ‖A v' - c‖ := by
                refine (norm_add_le _ _).trans ?_
                rw [norm_smul, norm_smul, Real.norm_of_nonneg ht0,
                  Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
            _ ≤ (1 - t) * ‖A p - c‖ + t * ‖A p - c‖ := by
                gcongr; exact hv'min p hps
            _ = ‖A p - c‖ := by ring
      obtain ⟨v0, hv0j, hv0s, -⟩ := cross v1 hv1s hv1j
      let W : Submodule ℝ V := LinearMap.ker (ℓ j)
      obtain ⟨w', hw'f, hw'min⟩ := ih W (A.comp W.subtype) (c - A v0)
        (fun i => (ℓ i).comp W.subtype) (fun i => b i - ℓ i v0)
        ⟨0, fun i hi => by simpa using hv0s i hi⟩
      refine ⟨v0 + (w' : V), ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with h | hi
        · have h0 : ℓ j (w' : V) = 0 := w'.2
          rw [h, map_add, h0, hv0j]; simp
        · have := hw'f i hi
          simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
          rw [map_add]; linarith
      · intro p hp
        obtain ⟨q, hqj, hqs, hqn⟩ :=
          cross p (fun i hi => hp i (mem_insert_of_mem hi)) (hp j (mem_insert_self j s))
        have hmem : q - v0 ∈ W := by
          simp [W, LinearMap.mem_ker, map_sub, hqj, hv0j]
        have := hw'min ⟨q - v0, hmem⟩ (fun i hi => by
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_sub]
          linarith [hqs i hi])
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_sub] at this
        calc ‖A (v0 + w') - c‖ = ‖A (w' : V) - (c - A v0)‖ := by
              rw [map_add]; congr 1; abel
          _ ≤ ‖A q - A v0 - (c - A v0)‖ := this
          _ = ‖A q - c‖ := by congr 1; abel
          _ ≤ ‖A p - c‖ := hqn

end Attainment

section Projection

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {S : Finset Z} {φ : Z → E} {ε : ℝ} {z : Z}

/-- **Component minima exist, including for singular `M(w)`** (`lem:bay-projection`).
The design distance `‖λ - θ‖_{M(w)} = ‖A (λ - θ)‖` attains its minimum on every nonempty
closed component `P_{a,z}`; `A` is an arbitrary linear map. -/
theorem exists_min_closedComp (A : E →ₗ[ℝ] F) (θ : E) (h : (closedComp φ S ε z).Nonempty) :
    ∃ lam ∈ closedComp φ S ε z, ∀ mu ∈ closedComp φ S ε z,
      ‖A (lam - θ)‖ ≤ ‖A (mu - θ)‖ := by
  obtain ⟨v, hv, hmin⟩ := exists_min_polyhedron S E A (A θ)
    (fun y => innerₗ E (φ z - φ y)) (fun _ => ε) (by
      obtain ⟨lam, hlam⟩ := h
      exact ⟨lam, fun y hy => hlam y hy⟩)
  refine ⟨v, fun y hy => hv y hy, fun mu hmu => ?_⟩
  have := hmin mu (fun y hy => hmu y hy)
  simpa [map_sub] using this

/-- **The information infimum is an attained minimum over the screened closed
components** (`lem:bay-projection`): if `E_a` is nonempty there is a point of
`Q_a = ⋃_{z ∈ E_a} P_{a,z}` whose design distance to `θ` is a lower bound for the distance
to every point of `Q_a`, hence to every strict alternative. -/
theorem exists_min_screened (hS : S.Nonempty) (hε : 0 ≤ ε) (A : E →ₗ[ℝ] F) (θ : E)
    (hne : (hullScreen φ S).Nonempty) :
    ∃ z ∈ hullScreen φ S, ∃ lam ∈ closedComp φ S ε z,
      (∀ z' ∈ hullScreen φ S, ∀ mu ∈ closedComp φ S ε z', ‖A (lam - θ)‖ ≤ ‖A (mu - θ)‖) ∧
      ∀ mu ∈ strictAlt φ S hS ε, ‖A (lam - θ)‖ ≤ ‖A (mu - θ)‖ := by
  classical
  have hex : ∀ z : Z, ∃ lam, z ∈ hullScreen φ S → lam ∈ closedComp φ S ε z ∧
      ∀ mu ∈ closedComp φ S ε z, ‖A (lam - θ)‖ ≤ ‖A (mu - θ)‖ := by
    intro z
    by_cases hz : z ∈ hullScreen φ S
    · obtain ⟨lam, h1, h2⟩ := exists_min_closedComp (φ := φ) (S := S) (ε := ε) (z := z) A θ
        (((strictComp_nonempty_iff hε z).mpr hz.2).mono strictComp_subset_closedComp)
      exact ⟨lam, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose m hm using hex
  have hfne : ((hullScreen φ S).toFinset).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, by simpa using hz⟩
  obtain ⟨z, hz, hzmin⟩ := Finset.exists_min_image _ (fun z => ‖A (m z - θ)‖) hfne
  have hz' : z ∈ hullScreen φ S := by simpa using hz
  have hall : ∀ z' ∈ hullScreen φ S, ∀ mu ∈ closedComp φ S ε z',
      ‖A (m z - θ)‖ ≤ ‖A (mu - θ)‖ := fun z' hz'' mu hmu =>
    (hzmin z' (by simpa using hz'')).trans ((hm z' hz'').2 mu hmu)
  exact ⟨z, hz', m z, (hm z hz').1, hall,
    (screened_projection hS hε A θ _).mpr hall⟩

/-! ### The positive-definite ratio formula `eq:bay-projection-ratio` -/

variable [FiniteDimensional ℝ F]

/-- The ratio `(ε - g_{z,p}ᵀ θ)_+ / ‖g_{z,p}‖_{M⁻¹}` of `eq:bay-projection-ratio`, for a
whitening equivalence `A` with `‖A v‖ = ‖v‖_M`; then `‖(A⁻¹)ᵀ g‖ = ‖g‖_{M⁻¹}`
(`adjoint_symm_norm_sq`). -/
noncomputable def projRatio (A : E ≃ₗ[ℝ] F) (φ : Z → E) (S : Finset Z) (ε : ℝ) (θ : E) (z : Z)
    (p : S → ℝ) : ℝ :=
  max (ε - ⟪contrast φ S z p, θ⟫) 0 /
    ‖LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) (contrast φ S z p)‖

/-- `‖(A⁻¹)ᵀ g‖² = gᵀ M⁻¹ g`: if `h` solves `M h = g`, where `M = AᵀA` is given through
its bilinear form `⟨M h, v⟩ = ⟨A h, A v⟩`, then `‖(A⁻¹)ᵀ g‖² = ⟨g, h⟩`. -/
lemma adjoint_symm_norm_sq (A : E ≃ₗ[ℝ] F) (g h : E) (hM : ∀ v, ⟪g, v⟫ = ⟪A h, A v⟫) :
    ‖LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) g‖ ^ 2 = ⟪g, h⟫ := by
  have h1 : LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) g = A h := by
    apply ext_inner_right ℝ
    intro y
    rw [LinearMap.adjoint_inner_left, hM]
    simp
  rw [h1, ← real_inner_self_eq_norm_sq, ← hM]

lemma adjoint_symm_ne_zero (A : E ≃ₗ[ℝ] F) {g : E} (hg : g ≠ 0) :
    LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) g ≠ 0 := by
  intro h0
  apply hg
  have h1 : ⟪g, g⟫ = ⟪LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) g, A g⟫ := by
    rw [LinearMap.adjoint_inner_left]; simp
  rw [h0, inner_zero_left] at h1
  exact inner_self_eq_zero.mp h1

lemma contrast_ne_zero {p : S → ℝ} (hp : p ∈ simplex S)
    (hz : φ z ∉ convexHull ℝ (φ '' (S : Set Z))) : contrast φ S z p ≠ 0 := by
  intro h0
  apply hz
  have h1 : φ z = ∑ y : S, p y • φ y := sub_eq_zero.mp h0
  rw [h1]
  refine (convex_convexHull ℝ _).sum_mem (fun y _ => hp.1 y) hp.2 (fun y _ => ?_)
  exact subset_convexHull ℝ _ ⟨y, y.2, rfl⟩

/-- **Ball--polyhedron duality.**  For a positive-definite design, the closed component
`P_{a,z}` meets the ellipsoid `{λ : ‖λ - θ‖_M ≤ β}` iff every inside mixture satisfies
`ε - g_{z,p}ᵀ θ ≤ β ‖g_{z,p}‖_{M⁻¹}`.  This is the exact ellipsoidal certificate
(`ellipsoid_adv_exact`) read as a statement about the information projection: the same
mixture `p` appears in robust regret and in the information needed to invalidate an
answer (`eq:t5-proj-dual`). -/
theorem closedComp_dist_le_iff (hS : S.Nonempty) (A : E ≃ₗ[ℝ] F) (θ : E) (z : Z) {β : ℝ}
    (hβ : 0 ≤ β) :
    (∃ lam ∈ closedComp φ S ε z, ‖A (lam - θ)‖ ≤ β) ↔
      ∀ p ∈ simplex S, ε - ⟪contrast φ S z p, θ⟫ ≤
        β * ‖LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) (contrast φ S z p)‖ := by
  obtain ⟨D, hG, hL⟩ := ellipsoid_adv_exact hS hβ φ θ (A.symm : F →ₗ[ℝ] E) z
  constructor
  · rintro ⟨lam, hlam, hle⟩ p hp
    have hmem : lam ∈ ellipsoid θ (A.symm : F →ₗ[ℝ] E) β :=
      ⟨A (lam - θ), by simpa using hle, by simp⟩
    have h1 : ε ≤ adv S hS (env φ lam) z := by
      refine le_inf' _ _ (fun y hy => ?_)
      rw [← inner_sub_eq_env]
      exact hlam y hy
    have h2 := adv_le_ellObj (φ := φ) hS z hmem hp
    unfold ellObj at h2
    linarith
  · intro h
    obtain ⟨⟨p, hp, hpD⟩, -⟩ := hL
    obtain ⟨⟨lam, hlam, hlD⟩, -⟩ := hG
    have h1 := h p hp
    have h2 : ε ≤ D := by
      rw [← hpD]; unfold ellObj; linarith
    refine ⟨lam, fun y hy => ?_, ?_⟩
    · have h3 : adv S hS (env φ lam) z ≤ env φ lam z - env φ lam y :=
        inf'_le (fun y => env φ lam z - env φ lam y) hy
      rw [inner_sub_eq_env]
      simp only at hlD
      linarith
    · obtain ⟨u, hu, rfl⟩ := hlam
      simpa using hu

/-- **Screened projection, positive-definite ratio form** (`eq:bay-projection-ratio`,
equivalently `eq:t5-proj-dual`).  For `z ∈ E_a` and a positive-definite design, the
component distance is attained at some `λ ∈ P_{a,z}`, the ratio
`(ε - g_{z,p}ᵀ θ)_+ / ‖g_{z,p}‖_{M⁻¹}` attains its maximum over inside mixtures at some
`p`, and the two values agree.  Squaring and halving gives
`K_{a,z} = ½ max_p (ε - g_{z,p}ᵀ θ)_+² / (g_{z,p}ᵀ M⁻¹ g_{z,p})`; the denominators are
positive because `z ∈ E_a`. -/
theorem projection_ratio (hS : S.Nonempty) (hε : 0 ≤ ε) (A : E ≃ₗ[ℝ] F) (θ : E)
    (hz : φ z ∉ convexHull ℝ (φ '' (S : Set Z))) :
    (∀ q ∈ simplex S, 0 < ‖LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) (contrast φ S z q)‖) ∧
    ∃ lam ∈ closedComp φ S ε z, ∃ p ∈ simplex S,
      (∀ mu ∈ closedComp φ S ε z, ‖A (lam - θ)‖ ≤ ‖A (mu - θ)‖) ∧
      (∀ q ∈ simplex S, projRatio A φ S ε θ z q ≤ projRatio A φ S ε θ z p) ∧
      ‖A (lam - θ)‖ = projRatio A φ S ε θ z p := by
  classical
  have hden : ∀ q ∈ simplex S,
      0 < ‖LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) (contrast φ S z q)‖ := fun q hq =>
    norm_pos_iff.mpr (adjoint_symm_ne_zero A (contrast_ne_zero hq hz))
  refine ⟨hden, ?_⟩
  obtain ⟨lam, hlam, hmin⟩ := exists_min_closedComp (φ := φ) (S := S) (ε := ε) (z := z)
    (A : E →ₗ[ℝ] F) θ (((strictComp_nonempty_iff hε z).mpr hz).mono strictComp_subset_closedComp)
  have hmin' : ∀ mu ∈ closedComp φ S ε z, ‖A (lam - θ)‖ ≤ ‖A (mu - θ)‖ := hmin
  have hub : ∀ q ∈ simplex S, projRatio A φ S ε θ z q ≤ ‖A (lam - θ)‖ := by
    intro q hq
    have h1 := (closedComp_dist_le_iff hS A θ z (norm_nonneg _)).mp ⟨lam, hlam, le_rfl⟩ q hq
    unfold projRatio
    rw [div_le_iff₀ (hden q hq)]
    exact max_le h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- the ratio is continuous on the simplex
  have hc : Continuous (fun q : S → ℝ => contrast φ S z q) := by
    unfold contrast; fun_prop
  have hnum : Continuous (fun q : S → ℝ => max (ε - ⟪contrast φ S z q, θ⟫) 0) :=
    (continuous_const.sub (hc.inner continuous_const)).max continuous_const
  have hdenc : Continuous (fun q : S → ℝ =>
      ‖LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) (contrast φ S z q)‖) :=
    ((LinearMap.continuous_of_finiteDimensional _).comp hc).norm
  have hcont : ContinuousOn (projRatio A φ S ε θ z) (simplex S) :=
    hnum.continuousOn.div hdenc.continuousOn (fun q hq => (hden q hq).ne')
  obtain ⟨y0, hy0⟩ := hS
  have hne : (simplex S).Nonempty := ⟨_, single_mem_simplex (⟨y0, hy0⟩ : S)⟩
  obtain ⟨p, hp, hpmax⟩ := (isCompact_simplex S).exists_isMaxOn hne hcont
  have hpmax' : ∀ q ∈ simplex S, projRatio A φ S ε θ z q ≤ projRatio A φ S ε θ z p :=
    fun q hq => hpmax hq
  refine ⟨lam, hlam, p, hp, hmin', hpmax', le_antisymm ?_ (hub p hp)⟩
  have hr0 : 0 ≤ projRatio A φ S ε θ z p :=
    div_nonneg (le_max_right _ _) (norm_nonneg _)
  obtain ⟨mu, hmu, hmule⟩ := (closedComp_dist_le_iff (φ := φ) (ε := ε) ⟨y0, hy0⟩ A θ z hr0).mpr
    (fun q hq => by
      have h1 := hpmax' q hq
      have h2 : ε - ⟪contrast φ S z q, θ⟫ ≤ projRatio A φ S ε θ z q *
          ‖LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) (contrast φ S z q)‖ := by
        unfold projRatio
        rw [div_mul_cancel₀ _ (hden q hq).ne']
        exact le_max_left _ _
      exact h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
  exact (hmin' mu hmu).trans hmule

end Projection

/-! ### The quadratic dual of a component distance, singular designs included -/

section QuadDual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {ι : Type*} [Fintype ι]

lemma convex_strict_aux {a c x1 x2 r1 r2 : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (h1 : x1 < r1) (h2 : x2 < r2) : a * x1 + c * x2 < a * r1 + c * r2 := by
  rcases ha.eq_or_lt with h | h
  · have hc1 : c = 1 := by linarith
    rw [← h, hc1]; linarith
  · have := mul_lt_mul_of_pos_left h1 h
    have := mul_le_mul_of_nonneg_left h2.le hc
    linarith

/-- **Weak duality** for `min {½ ‖A v‖² : ⟨d y, v⟩ ≥ b y}`.  A multiplier `α ≥ 0` with
`∑ α_y d_y = AᵀA ν` (that is `Dᵀα ∈ range M`, `M = AᵀA`) gives the lower bound
`αᵀ b - ½ νᵀ M ν`. -/
theorem quad_dual_weak (A : E →ₗ[ℝ] F) (d : ι → E) (b : ι → ℝ) {α : ι → ℝ}
    (hα : ∀ y, 0 ≤ α y) {ν : E} (hν : ∑ y, α y • d y = LinearMap.adjoint A (A ν))
    {v : E} (hv : ∀ y, b y ≤ ⟪d y, v⟫) :
    ∑ y, α y * b y - ‖A ν‖ ^ 2 / 2 ≤ ‖A v‖ ^ 2 / 2 := by
  have h1 : ∑ y, α y * b y ≤ ∑ y, α y * ⟪d y, v⟫ :=
    sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hv y) (hα y))
  have h2 : ∑ y, α y * ⟪d y, v⟫ = ⟪A ν, A v⟫ := by
    rw [← LinearMap.adjoint_inner_left, ← hν, sum_inner]
    simp [real_inner_smul_left]
  have h3 := real_inner_le_norm (A ν) (A v)
  nlinarith [sq_nonneg (‖A ν‖ - ‖A v‖)]

/-- **Strong duality with attainment** for `min {½ ‖A v‖² : ⟨d y, v⟩ ≥ b y}` under
Slater's condition, with no rank condition on `A`.  If `v0` is a minimizer there is a
multiplier `α ≥ 0` and `ν` with `∑ α_y d_y = AᵀA ν` whose dual value reaches the minimum.
Proved by separating the open convex epigraph set from the optimal value
(Hahn--Banach); boundedness below of the Lagrangian puts `Dᵀα` in the range of `AᵀA`. -/
theorem quad_dual_strong (A : E →ₗ[ℝ] F) (d : ι → E) (b : ι → ℝ)
    (hslater : ∃ v, ∀ y, b y < ⟪d y, v⟫) {v0 : E}
    (hmin : ∀ v, (∀ y, b y ≤ ⟪d y, v⟫) → ‖A v0‖ ≤ ‖A v‖) :
    ∃ α : ι → ℝ, (∀ y, 0 ≤ α y) ∧ ∃ ν : E, ∑ y, α y • d y = LinearMap.adjoint A (A ν) ∧
      ‖A v0‖ ^ 2 / 2 ≤ ∑ y, α y * b y - ‖A ν‖ ^ 2 / 2 := by
  classical
  set mstar := ‖A v0‖ ^ 2 / 2 with hm
  let U : Set (ℝ × (ι → ℝ)) :=
    {x | ∃ v : E, ‖A v‖ ^ 2 / 2 < x.1 ∧ ∀ y, b y - ⟪d y, v⟫ < x.2 y}
  have hUopen : IsOpen U := by
    have : U = ⋃ v : E, ({x : ℝ × (ι → ℝ) | ‖A v‖ ^ 2 / 2 < x.1} ∩
        ⋂ y, {x : ℝ × (ι → ℝ) | b y - ⟪d y, v⟫ < x.2 y}) := by
      ext x; simp [U]
    rw [this]
    exact isOpen_iUnion (fun v => IsOpen.inter (isOpen_lt continuous_const continuous_fst)
      (isOpen_iInter_of_finite (fun y => isOpen_lt continuous_const (by fun_prop))))
  have hUconv : Convex ℝ U := by
    rintro ⟨r1, s1⟩ ⟨v1, h1, h1'⟩ ⟨r2, s2⟩ ⟨v2, h2, h2'⟩ a c ha hc hac
    simp only at h1 h2 h1' h2'
    refine ⟨a • v1 + c • v2, ?_, fun y => ?_⟩
    · have hn : ‖a • A v1 + c • A v2‖ ≤ a * ‖A v1‖ + c * ‖A v2‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc]
      have h3 : (a * ‖A v1‖ + c * ‖A v2‖) ^ 2 ≤ a * ‖A v1‖ ^ 2 + c * ‖A v2‖ ^ 2 := by
        have hc' : c = 1 - a := by linarith
        subst hc'
        nlinarith [mul_nonneg (mul_nonneg ha hc) (sq_nonneg (‖A v1‖ - ‖A v2‖))]
      have hsq : ‖a • A v1 + c • A v2‖ ^ 2 ≤ a * ‖A v1‖ ^ 2 + c * ‖A v2‖ ^ 2 :=
        (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans h3
      have h4 := convex_strict_aux ha hc hac h1 h2
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, map_add, map_smul]
      linarith
    · have h4 := convex_strict_aux ha hc hac (h1' y) (h2' y)
      have h5 : a * b y + c * b y = b y := by rw [← add_mul, hac, one_mul]
      simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        inner_add_right, real_inner_smul_right]
      linarith
  have hnot : ((mstar, 0) : ℝ × (ι → ℝ)) ∉ U := by
    rintro ⟨v, hv1, hv2⟩
    have h1 := hmin v (fun y => by have := hv2 y; simp at this; linarith)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    simp only at hv1
    linarith
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hUconv hUopen hnot
  set c0 : ℝ := f ((1 : ℝ), (0 : ι → ℝ)) with hc0def
  set α : ι → ℝ := fun y => f ((0 : ℝ), Pi.single y (1 : ℝ)) with hαdef
  have hdec : ∀ (r : ℝ) (s : ι → ℝ), f (r, s) = r * c0 + ∑ y, s y * α y := by
    intro r s
    have hrs : ((r, s) : ℝ × (ι → ℝ)) =
        r • ((1 : ℝ), (0 : ι → ℝ)) + ∑ y, s y • ((0 : ℝ), Pi.single y (1 : ℝ)) := by
      refine Prod.ext ?_ (funext fun y' => ?_)
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hrs, map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul]
    rfl
  -- monotonicity of `U`
  have hmono : ∀ r s r' s', ((r, s) : ℝ × (ι → ℝ)) ∈ U → r ≤ r' → (∀ y, s y ≤ s' y) →
      ((r', s') : ℝ × (ι → ℝ)) ∈ U := by
    rintro r s r' s' ⟨v, h1, h2⟩ hr hs
    exact ⟨v, lt_of_lt_of_le h1 hr, fun y => lt_of_lt_of_le (h2 y) (hs y)⟩
  set s0 : ι → ℝ := fun y => |b y| + 1 with hs0
  have hp0 : (((1 : ℝ), s0) : ℝ × (ι → ℝ)) ∈ U :=
    ⟨0, by simp, fun y => by simp [hs0]; linarith [le_abs_self (b y)]⟩
  have hK : 0 < f (mstar, 0) - f ((1 : ℝ), s0) := sub_pos.mpr (hf _ hp0)
  have hα : ∀ y, α y ≤ 0 := by
    intro y
    by_contra hcon
    push Not at hcon
    set T := (f (mstar, 0) - f ((1 : ℝ), s0)) / α y with hT
    have hT0 : 0 ≤ T := div_nonneg hK.le hcon.le
    have hmem : (((1 : ℝ), s0 + T • Pi.single y (1 : ℝ)) : ℝ × (ι → ℝ)) ∈ U :=
      hmono _ _ _ _ hp0 le_rfl (fun y' => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have : 0 ≤ T * (Pi.single y (1 : ℝ) : ι → ℝ) y' := by
          refine mul_nonneg hT0 ?_
          by_cases h : y' = y <;> simp [h]
        linarith)
    have heq : (((1 : ℝ), s0 + T • Pi.single y (1 : ℝ)) : ℝ × (ι → ℝ)) =
        ((1 : ℝ), s0) + T • ((0 : ℝ), Pi.single y (1 : ℝ)) := by
      refine Prod.ext (by simp) (by simp)
    have h1 := hf _ hmem
    rw [heq, map_add, map_smul, smul_eq_mul] at h1
    have h2 : T * α y = f (mstar, 0) - f ((1 : ℝ), s0) := by
      rw [hT]; field_simp
    have h3 : f ((0 : ℝ), Pi.single y (1 : ℝ)) = α y := rfl
    rw [h3, h2] at h1
    linarith
  have hc0 : c0 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    set T := (f (mstar, 0) - f ((1 : ℝ), s0)) / c0 with hT
    have hT0 : 0 ≤ T := div_nonneg hK.le hcon.le
    have hmem : (((1 : ℝ) + T, s0) : ℝ × (ι → ℝ)) ∈ U :=
      hmono _ _ _ _ hp0 (by linarith) (fun y' => le_rfl)
    have heq : (((1 : ℝ) + T, s0) : ℝ × (ι → ℝ)) =
        ((1 : ℝ), s0) + T • ((1 : ℝ), (0 : ι → ℝ)) := by
      refine Prod.ext (by simp) (by simp)
    have h1 := hf _ hmem
    rw [heq, map_add, map_smul, smul_eq_mul] at h1
    have h2 : T * c0 = f (mstar, 0) - f ((1 : ℝ), s0) := by
      rw [hT]; field_simp
    rw [← hc0def, h2] at h1
    linarith
  have hc0' : c0 < 0 := by
    refine lt_of_le_of_ne hc0 (fun h0 => ?_)
    obtain ⟨vs, hvs⟩ := hslater
    have hmem : ((‖A vs‖ ^ 2 / 2 + 1, 0) : ℝ × (ι → ℝ)) ∈ U :=
      ⟨vs, by simp, fun y => by have := hvs y; simp; linarith⟩
    have h1 := hf _ hmem
    rw [hdec, hdec, h0] at h1
    simp at h1
  -- the Lagrangian is bounded below by the optimal value
  have hlag0 : ∀ v : E, mstar ≤ ‖A v‖ ^ 2 / 2 + (∑ y, (b y - ⟪d y, v⟫) * α y) / c0 := by
    intro v
    set P := ∑ y, (b y - ⟪d y, v⟫) * α y with hP
    set Q := ∑ y, α y with hQ
    have hQ0 : 0 ≤ Q / c0 := div_nonneg_of_nonpos (sum_nonpos (fun y _ => hα y)) hc0
    have hstep : ∀ η : ℝ, 0 < η → mstar ≤ ‖A v‖ ^ 2 / 2 + P / c0 + η * (1 + Q / c0) := by
      intro η hη
      have hmem : ((‖A v‖ ^ 2 / 2 + η, fun y => b y - ⟪d y, v⟫ + η) : ℝ × (ι → ℝ)) ∈ U :=
        ⟨v, by simp; linarith, fun y => by simp; linarith⟩
      have h1 := hf _ hmem
      rw [hdec, hdec] at h1
      have h2 : ∑ y, (b y - ⟪d y, v⟫ + η) * α y = P + η * Q := by
        rw [hP, hQ, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl (fun y _ => by ring)
      rw [h2] at h1
      simp only [Pi.zero_apply, zero_mul, sum_const_zero, add_zero] at h1
      by_contra hcon
      push Not at hcon
      have h3 := mul_lt_mul_of_neg_right hcon hc0'
      have h4 : (‖A v‖ ^ 2 / 2 + P / c0 + η * (1 + Q / c0)) * c0 =
          (‖A v‖ ^ 2 / 2 + η) * c0 + (P + η * Q) := by
        have hne : c0 ≠ 0 := hc0'.ne
        field_simp
        ring
      linarith
    apply le_of_forall_pos_le_add
    intro e he
    have hσ : 0 < 1 + Q / c0 := by linarith
    have := hstep (e / (1 + Q / c0)) (div_pos he hσ)
    rwa [div_mul_cancel₀ _ hσ.ne'] at this
  set α' : ι → ℝ := fun y => α y / c0 with hα'def
  have hα' : ∀ y, 0 ≤ α' y := fun y => div_nonneg_of_nonpos (hα y) hc0
  set g : E := ∑ y, α' y • d y with hg
  have hlag : ∀ v : E, mstar ≤ ‖A v‖ ^ 2 / 2 + ∑ y, α' y * b y - ⟪g, v⟫ := by
    intro v
    have h1 := hlag0 v
    have h2 : (∑ y, (b y - ⟪d y, v⟫) * α y) / c0 = ∑ y, α' y * b y - ⟪g, v⟫ := by
      rw [hg, sum_inner, ← sum_sub_distrib, sum_div]
      refine sum_congr rfl (fun y _ => ?_)
      rw [real_inner_smul_left, hα'def]
      ring
    linarith
  set T : E →ₗ[ℝ] E := (LinearMap.adjoint A).comp A with hT
  have hgmem : g ∈ (LinearMap.range T)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    have hTk : ⟪T k, k⟫ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hk (T k) (LinearMap.mem_range_self T k)
    have hAk : A k = 0 := by
      have h0 : ⟪A k, A k⟫ = 0 := by
        rw [← LinearMap.adjoint_inner_left]; exact hTk
      exact inner_self_eq_zero.mp h0
    rw [real_inner_comm]
    by_contra hne
    have hL := hlag (((∑ y, α' y * b y - mstar + 1) / ⟪g, k⟫) • k)
    rw [map_smul, hAk, smul_zero, norm_zero, real_inner_smul_right,
      div_mul_cancel₀ _ hne] at hL
    norm_num at hL
    linarith
  rw [Submodule.orthogonal_orthogonal] at hgmem
  obtain ⟨ν, hν⟩ := hgmem
  refine ⟨α', hα', ν, hν.symm, ?_⟩
  have h1 := hlag ν
  have h2 : ⟪g, ν⟫ = ‖A ν‖ ^ 2 := by
    rw [← hν, hT, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq]
  linarith

end QuadDual

section ProjectionDual

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {S : Finset Z} {φ : Z → E} {ε : ℝ} {z : Z}

/-- **Screened projection, dual form** (`lem:bay-projection`, the display for
`K_{a,z}`), for an arbitrary and possibly singular design.  With `D` the matrix of rows
`(φ_z - φ_y)ᵀ`, `b = ε 1 - D θ` and `M = AᵀA`, the condition `Dᵀα ∈ range M` is written
`∑ α_y (φ_z - φ_y) = AᵀA ν`, and then `(Dᵀα)ᵀ M† Dᵀα = νᵀ M ν = ‖A ν‖²`.  For `z ∈ E_a`
the component distance is attained, every dual-feasible `(α, ν)` gives a lower bound,
and some dual-feasible pair attains it:
`K_{a,z} = max_{α ≥ 0, Dᵀα ∈ range M} [αᵀb - ½ (Dᵀα)ᵀ M† Dᵀα]`. -/
theorem screened_projection_dual (hε : 0 ≤ ε) (A : E →ₗ[ℝ] F) (θ : E)
    (hz : φ z ∉ convexHull ℝ (φ '' (S : Set Z))) :
    ∃ lam ∈ closedComp φ S ε z,
      (∀ mu ∈ closedComp φ S ε z, ‖A (lam - θ)‖ ≤ ‖A (mu - θ)‖) ∧
      (∀ (α : S → ℝ) (ν : E), (∀ y, 0 ≤ α y) →
          ∑ y : S, α y • (φ z - φ y) = LinearMap.adjoint A (A ν) →
          ∑ y : S, α y * (ε - ⟪φ z - φ y, θ⟫) - ‖A ν‖ ^ 2 / 2 ≤ ‖A (lam - θ)‖ ^ 2 / 2) ∧
      ∃ (α : S → ℝ) (ν : E), (∀ y, 0 ≤ α y) ∧
          ∑ y : S, α y • (φ z - φ y) = LinearMap.adjoint A (A ν) ∧
          ∑ y : S, α y * (ε - ⟪φ z - φ y, θ⟫) - ‖A ν‖ ^ 2 / 2 = ‖A (lam - θ)‖ ^ 2 / 2 := by
  obtain ⟨sl, hsl⟩ := (strictComp_nonempty_iff hε z).mpr hz
  obtain ⟨lam, hlam, hmin⟩ := exists_min_closedComp (φ := φ) (S := S) (ε := ε) (z := z) A θ
    ⟨sl, strictComp_subset_closedComp hsl⟩
  have hfeas : ∀ mu : E, mu ∈ closedComp φ S ε z ↔
      ∀ y : S, ε - ⟪φ z - φ y, θ⟫ ≤ ⟪φ z - φ y, mu - θ⟫ := by
    intro mu
    constructor
    · intro h y
      have := h y y.2
      rw [inner_sub_right]; linarith
    · intro h y hy
      have := h ⟨y, hy⟩
      rw [inner_sub_right] at this
      simp only at this
      linarith
  have hweak : ∀ (α : S → ℝ) (ν : E), (∀ y, 0 ≤ α y) →
      ∑ y : S, α y • (φ z - φ y) = LinearMap.adjoint A (A ν) →
      ∑ y : S, α y * (ε - ⟪φ z - φ y, θ⟫) - ‖A ν‖ ^ 2 / 2 ≤ ‖A (lam - θ)‖ ^ 2 / 2 :=
    fun α ν hα hν => quad_dual_weak A (fun y : S => φ z - φ y)
      (fun y : S => ε - ⟪φ z - φ y, θ⟫) hα hν ((hfeas lam).mp hlam)
  refine ⟨lam, hlam, hmin, hweak, ?_⟩
  obtain ⟨α, hα, ν, hν, hle⟩ := quad_dual_strong A (fun y : S => φ z - φ y)
    (fun y : S => ε - ⟪φ z - φ y, θ⟫) (v0 := lam - θ)
    ⟨sl - θ, fun y => by
      have := hsl y y.2
      rw [inner_sub_right]; linarith⟩
    (fun v hv => by
      have h1 : v + θ ∈ closedComp φ S ε z := (hfeas _).mpr (by simpa using hv)
      simpa using hmin _ h1)
  exact ⟨α, ν, hα, hν, le_antisymm (hweak α ν hα hν) hle⟩

end ProjectionDual

/-! ### The design map `M(w) = ∑_x w_x u_x u_xᵀ` -/

section Design

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The whitening map of a design: `v ↦ (√(w_x) ⟨u_x, v⟩)_x`, so that
`‖designMap u w v‖² = ∑_x w_x ⟨u_x, v⟩² = vᵀ M(w) v` (`norm_designMap_sq`). -/
noncomputable def designMap (u : X → E) (w : X → ℝ) : E →ₗ[ℝ] EuclideanSpace ℝ X :=
  (WithLp.linearEquiv 2 ℝ (X → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.pi (fun x => Real.sqrt (w x) • innerₗ E (u x))

lemma designMap_apply (u : X → E) (w : X → ℝ) (v : E) (x : X) :
    designMap u w v x = Real.sqrt (w x) * ⟪u x, v⟫ := rfl

/-- `‖v‖²_{M(w)} = ∑_x w_x ⟨u_x, v⟩²`. -/
lemma norm_designMap_sq (u : X → E) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (v : E) :
    ‖designMap u w v‖ ^ 2 = ∑ x, w x * ⟪u x, v⟫ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine sum_congr rfl (fun x _ => ?_)
  rw [designMap_apply, mul_pow, Real.sq_sqrt (hw x)]

/-- The bilinear form of `M(w)`: `⟨A h, A v⟩ = ⟨M(w) h, v⟩` with
`M(w) h = ∑_x w_x ⟨u_x, h⟩ u_x`. -/
lemma inner_designMap (u : X → E) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (h v : E) :
    ⟪designMap u w h, designMap u w v⟫ = ⟪∑ x, (w x * ⟪u x, h⟫) • u x, v⟫ := by
  rw [PiLp.inner_apply, sum_inner]
  refine sum_congr rfl (fun x _ => ?_)
  rw [designMap_apply, designMap_apply, real_inner_smul_left]
  have := Real.mul_self_sqrt (hw x)
  simp only [inner]
  calc Real.sqrt (w x) * ⟪u x, v⟫ * (Real.sqrt (w x) * ⟪u x, h⟫)
      = (Real.sqrt (w x) * Real.sqrt (w x)) * ⟪u x, h⟫ * ⟪u x, v⟫ := by ring
    _ = w x * ⟪u x, h⟫ * ⟪u x, v⟫ := by rw [this]

/-- `M(w) ⪯ ℓ² I` on the simplex when `‖u_x‖ ≤ ℓ`. -/
lemma norm_designMap_le (u : X → E) {w : X → ℝ} (hw : w ∈ simplex X) {ℓ : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ ℓ) (v : E) : ‖designMap u w v‖ ≤ ℓ * ‖v‖ := by
  have hℓ : 0 ≤ ℓ := by
    by_contra hneg
    push Not at hneg
    have hall : ∀ x, w x ≤ 0 := fun x => by
      have := (norm_nonneg (u x)).trans (hu x)
      linarith
    have := sum_nonpos (fun x (_ : x ∈ univ) => hall x)
    linarith [hw.2]
  have hsq : ‖designMap u w v‖ ^ 2 ≤ (ℓ * ‖v‖) ^ 2 := by
    rw [norm_designMap_sq u hw.1]
    calc ∑ x, w x * ⟪u x, v⟫ ^ 2 ≤ ∑ x, w x * (ℓ * ‖v‖) ^ 2 := by
          refine sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left ?_ (hw.1 x))
          have h1 := abs_real_inner_le_norm (u x) v
          have h2 : ‖u x‖ * ‖v‖ ≤ ℓ * ‖v‖ := mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
          exact sq_le_sq' (by linarith [neg_abs_le ⟪u x, v⟫]) (by linarith [le_abs_self ⟪u x, v⟫])
      _ = (ℓ * ‖v‖) ^ 2 := by rw [← sum_mul, hw.2, one_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hℓ (norm_nonneg _)) two_ne_zero).mp hsq

/-- `M` is linear in the design: `‖v‖²_{M(t w₁ + (1-t) w₂)} = t ‖v‖²_{M(w₁)} + (1-t) ‖v‖²_{M(w₂)}`. -/
lemma norm_designMap_sq_mix (u : X → E) {w₁ w₂ : X → ℝ} (h₁ : ∀ x, 0 ≤ w₁ x)
    (h₂ : ∀ x, 0 ≤ w₂ x) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (v : E) :
    ‖designMap u (fun x => t * w₁ x + (1 - t) * w₂ x) v‖ ^ 2 =
      t * ‖designMap u w₁ v‖ ^ 2 + (1 - t) * ‖designMap u w₂ v‖ ^ 2 := by
  rw [norm_designMap_sq u h₁, norm_designMap_sq u h₂, norm_designMap_sq u
    (fun x => add_nonneg (mul_nonneg ht0 (h₁ x)) (mul_nonneg (sub_nonneg.mpr ht1) (h₂ x))),
    mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun x _ => by ring)

/-- **Reference-design domination** (`app:bay-finite`, "the inherited geometry gives
`C₀ ≥ k₀ C / ℓ²`"): if `M(w⁰) ⪰ k₀ I` and `‖u_x‖ ≤ ℓ` then `M(w⁰) ⪰ (k₀ / ℓ²) M(w)` for
every design `w`. -/
lemma reference_design_dominates (u : X → E) {w0 w : X → ℝ} (hw : w ∈ simplex X) {ℓ k0 : ℝ}
    (hℓ : 0 < ℓ) (hk0 : 0 ≤ k0) (hu : ∀ x, ‖u x‖ ≤ ℓ)
    (h0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (v : E) :
    k0 / ℓ ^ 2 * ‖designMap u w v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2 := by
  have h1 := norm_designMap_le u hw hu v
  have h2 : ‖designMap u w v‖ ^ 2 ≤ (ℓ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc k0 / ℓ ^ 2 * ‖designMap u w v‖ ^ 2 ≤ k0 / ℓ ^ 2 * (ℓ * ‖v‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = k0 * ‖v‖ ^ 2 := by field_simp
    _ ≤ _ := h0 v

end Design

/-! ### Root information and its regularity -/

section RootInfo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Root information `√(2 I(θ))`, `I(θ) = inf_{λ ∈ Q} ½ ‖λ - θ‖²_M`, as the distance from
`A θ` to `A '' Q` (`rootInfo_isGLB` identifies it with the infimum).  For empty `Q` the
value is `0`, not `+∞`; statements below assume `Q` nonempty where this matters. -/
noncomputable def rootInfo (A : E →ₗ[ℝ] F) (Q : Set E) (θ : E) : ℝ :=
  Metric.infDist (A θ) (A '' Q)

variable {A : E →ₗ[ℝ] F} {Q : Set E} {θ θ' : E}

lemma dist_map_eq (A : E →ₗ[ℝ] F) (θ lam : E) : dist (A θ) (A lam) = ‖A (lam - θ)‖ := by
  rw [dist_comm, dist_eq_norm, map_sub]

lemma rootInfo_nonneg : 0 ≤ rootInfo A Q θ := Metric.infDist_nonneg

lemma rootInfo_le {lam : E} (h : lam ∈ Q) : rootInfo A Q θ ≤ ‖A (lam - θ)‖ := by
  rw [← dist_map_eq]
  exact Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem A h)

lemma le_rootInfo_iff (hQ : Q.Nonempty) {c : ℝ} :
    c ≤ rootInfo A Q θ ↔ ∀ lam ∈ Q, c ≤ ‖A (lam - θ)‖ := by
  unfold rootInfo
  rw [Metric.le_infDist (hQ.image A)]
  constructor
  · intro h lam hl
    have := h (Set.mem_image_of_mem A hl)
    rwa [dist_map_eq] at this
  · rintro h _ ⟨lam, hl, rfl⟩
    rw [dist_map_eq]
    exact h lam hl

/-- `½ rootInfo² = inf_{λ ∈ Q} ½ ‖λ - θ‖²_M`. -/
theorem rootInfo_isGLB (hQ : Q.Nonempty) :
    IsGLB ((fun lam => ‖A (lam - θ)‖ ^ 2 / 2) '' Q) (rootInfo A Q θ ^ 2 / 2) := by
  constructor
  · rintro _ ⟨lam, hl, rfl⟩
    have := pow_le_pow_left₀ rootInfo_nonneg (rootInfo_le (A := A) (θ := θ) hl) 2
    simp only
    linarith
  · intro c hc
    by_cases hc0 : c ≤ 0
    · have := sq_nonneg (rootInfo A Q θ)
      linarith
    · push Not at hc0
      have h1 : Real.sqrt (2 * c) ≤ rootInfo A Q θ := by
        rw [le_rootInfo_iff hQ]
        intro lam hl
        have h2 : c ≤ ‖A (lam - θ)‖ ^ 2 / 2 := hc ⟨lam, hl, rfl⟩
        rw [Real.sqrt_le_iff]
        exact ⟨norm_nonneg _, by linarith⟩
      have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [Real.sq_sqrt (by linarith)] at h3
      linarith

/-- **Square-root distance modulus** (`eq:bay-root-lipschitz`, seminorm form):
`|√(2 I(θ)) - √(2 I(θ'))| ≤ ‖θ - θ'‖_M`. -/
theorem rootInfo_lipschitz (A : E →ₗ[ℝ] F) (Q : Set E) (θ θ' : E) :
    |rootInfo A Q θ - rootInfo A Q θ'| ≤ ‖A (θ - θ')‖ := by
  have h1 : rootInfo A Q θ ≤ rootInfo A Q θ' + dist (A θ) (A θ') :=
    Metric.infDist_le_infDist_add_dist
  have h2 : rootInfo A Q θ' ≤ rootInfo A Q θ + dist (A θ') (A θ) :=
    Metric.infDist_le_infDist_add_dist
  rw [dist_map_eq] at h2
  rw [dist_comm, dist_map_eq] at h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **Design domination**: `G ⪰ c² M` implies `√(2 I_G) ≥ c √(2 I_M)`.  Used for
`G_n ⪰ n M(w)` and for `M(w_n) ⪰ c_n M(w)` in the continuity argument. -/
theorem rootInfo_mono_design {G : E →ₗ[ℝ] F} (hQ : Q.Nonempty) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ v, c * ‖A v‖ ≤ ‖G v‖) : c * rootInfo A Q θ ≤ rootInfo G Q θ := by
  rw [le_rootInfo_iff hQ]
  intro lam hl
  exact (mul_le_mul_of_nonneg_left (rootInfo_le hl) hc).trans (hdom _)

/-- Replacing the alternatives by their closure does not change the information
(the information infimum over strict alternatives is the minimum over `Q_a`). -/
theorem rootInfo_closure [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] F) (Q : Set E) (θ : E) :
    rootInfo A (closure Q) θ = rootInfo A Q θ := by
  rcases Q.eq_empty_or_nonempty with rfl | hQ
  · simp
  · unfold rootInfo
    apply le_antisymm
    · exact Metric.infDist_le_infDist_of_subset (Set.image_mono subset_closure) (hQ.image A)
    · rw [← Metric.infDist_closure (s := A '' Q)]
      exact Metric.infDist_le_infDist_of_subset
        (image_closure_subset_closure_image A.continuous_of_finiteDimensional)
        ((hQ.mono subset_closure).image A)

end RootInfo

section RootInfoDesign

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `eq:bay-root-lipschitz`: `|√(2 I_a(θ, w)) - √(2 I_a(θ', w))| ≤ ℓ ‖θ - θ'‖₂` for every
design `w` in the simplex, `ℓ = max_x ‖u_x‖`. -/
theorem rootInfo_design_lipschitz (u : X → E) {w : X → ℝ} (hw : w ∈ simplex X) {ℓ : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ ℓ) (Q : Set E) (θ θ' : E) :
    |rootInfo (designMap u w) Q θ - rootInfo (designMap u w) Q θ'| ≤ ℓ * ‖θ - θ'‖ :=
  (rootInfo_lipschitz _ Q θ θ').trans (norm_designMap_le u hw hu _)

/-- **Concavity of the information in the design** ("the infimum of linear functions in
`w`"): `I(θ, t w₁ + (1-t) w₂) ≥ t I(θ, w₁) + (1-t) I(θ, w₂)`, with `I = ½ rootInfo²`. -/
theorem info_concave_design (u : X → E) {w₁ w₂ : X → ℝ} (h₁ : ∀ x, 0 ≤ w₁ x)
    (h₂ : ∀ x, 0 ≤ w₂ x) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {Q : Set E} (hQ : Q.Nonempty)
    (θ : E) :
    t * (rootInfo (designMap u w₁) Q θ ^ 2 / 2) + (1 - t) * (rootInfo (designMap u w₂) Q θ ^ 2 / 2)
      ≤ rootInfo (designMap u (fun x => t * w₁ x + (1 - t) * w₂ x)) Q θ ^ 2 / 2 := by
  refine (rootInfo_isGLB hQ).2 ?_
  rintro _ ⟨lam, hl, rfl⟩
  simp only
  rw [norm_designMap_sq_mix u h₁ h₂ ht0 ht1]
  have e1 := pow_le_pow_left₀ rootInfo_nonneg
    (rootInfo_le (A := designMap u w₁) (θ := θ) hl) 2
  have e2 := pow_le_pow_left₀ rootInfo_nonneg
    (rootInfo_le (A := designMap u w₂) (θ := θ) hl) 2
  nlinarith [mul_le_mul_of_nonneg_left e1 ht0,
    mul_le_mul_of_nonneg_left e2 (sub_nonneg.mpr ht1)]

end RootInfoDesign

/-! ### Certification from the stopping statistic, and the frozen record -/

section Certify

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {S : Finset Z} {φ : Z → E} {ε : ℝ}

/-- `lem:bay-distance-certificate` in terms of the root information: with alternatives
present, `R_C(a) ≤ ε` iff `β ≤ √(2 I_a(θ))`, i.e. `β² ≤ 2 I_a(θ)` for `β ≥ 0`. -/
theorem distance_certificate_rootInfo (hS : S.Nonempty) (A : E →ₗ[ℝ] F)
    (hA : Function.Injective A) {θ : E} {β : ℝ} (hθ : regret S hS (env φ θ) ≤ ε)
    (hne : (strictAlt φ S hS ε).Nonempty) :
    (∀ lam, ‖A (lam - θ)‖ ≤ β → regret S hS (env φ lam) ≤ ε) ↔
      β ≤ rootInfo A (strictAlt φ S hS ε) θ := by
  rw [distance_certificate hS A hA hθ, le_rootInfo_iff hne]

/-- **Likelihood stopping certifies the action** (the paragraph after `lem:bay-cs`, and
the "radius--information implication" in the proof of `prop:v10g-safety-fallback`).  If
the statistic `J = inf_{λ : r_λ(a) > ε} ½ ‖λ - θ̂‖²_G` is at least a positive threshold `H`
and the true parameter lies in the confidence ellipsoid `½ ‖θ - θ̂‖²_G ≤ H`, then `a` is
`ε`-acceptable at the true parameter.  The Gram matrix is positive definite (`G`
injective).  Coverage is a hypothesis; `lem:bay-cs` supplies it. -/
theorem certified_of_threshold (hS : S.Nonempty) (G : E →ₗ[ℝ] F) (hG : Function.Injective G)
    {θhat θ : E} {H : ℝ} (hH : 0 < H)
    (hstop : ∀ lam ∈ strictAlt φ S hS ε, H ≤ ‖G (lam - θhat)‖ ^ 2 / 2)
    (hcov : ‖G (θ - θhat)‖ ^ 2 / 2 ≤ H) : regret S hS (env φ θ) ≤ ε := by
  have hcenter : regret S hS (env φ θhat) ≤ ε := by
    by_contra hcon
    push Not at hcon
    have := hstop θhat hcon
    simp at this
    linarith
  refine (distance_certificate hS G hG (β := Real.sqrt (2 * H)) hcenter).mpr ?_ θ ?_
  · intro lam hl
    rw [Real.sqrt_le_iff]
    exact ⟨norm_nonneg _, by linarith [hstop lam hl]⟩
  · apply Real.le_sqrt_of_sq_le
    linarith

/-- **The frozen pilot certificate** (`eq:v10g-recycle`).  If the pilot record satisfies
`l ≤ I_a(v, w)` and the fresh Gram matrix dominates `n M(w)`, then
`Z_n = n [√l - ‖θ̂_n - v‖_{M(w)} / √2]_+² ≤ ½ ‖u - θ̂_n‖²_{G_n}` for every `u ∈ Q_a`. -/
theorem frozen_recycle (A G : E →ₗ[ℝ] F) (Q : Set E) {n l : ℝ} (hn : 0 ≤ n)
    (hdom : ∀ v, Real.sqrt n * ‖A v‖ ≤ ‖G v‖) {v θhat : E}
    (hl : ∀ u ∈ Q, l ≤ ‖A (u - v)‖ ^ 2 / 2) :
    ∀ u ∈ Q, n * (max (Real.sqrt l - ‖A (θhat - v)‖ / Real.sqrt 2) 0) ^ 2 ≤
      ‖G (u - θhat)‖ ^ 2 / 2 := by
  intro u hu
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hkey : Real.sqrt n * (Real.sqrt 2 * max (Real.sqrt l - ‖A (θhat - v)‖ / Real.sqrt 2) 0)
      ≤ ‖G (u - θhat)‖ := by
    rcases le_total (Real.sqrt l - ‖A (θhat - v)‖ / Real.sqrt 2) 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h]
      have h3 : Real.sqrt l ≤ ‖A (u - v)‖ / Real.sqrt 2 := by
        rw [le_div_iff₀ h2, ← Real.sqrt_mul' _ (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_le_iff]
        exact ⟨norm_nonneg _, by linarith [hl u hu]⟩
      have h4 : ‖A (u - v)‖ ≤ ‖A (u - θhat)‖ + ‖A (θhat - v)‖ := by
        have : u - v = (u - θhat) + (θhat - v) := by abel
        rw [this, map_add]
        exact norm_add_le _ _
      have h5 : Real.sqrt 2 * (Real.sqrt l - ‖A (θhat - v)‖ / Real.sqrt 2) ≤ ‖A (u - θhat)‖ := by
        have h6 : Real.sqrt 2 * (‖A (u - v)‖ / Real.sqrt 2) = ‖A (u - v)‖ := by field_simp
        have h7 : Real.sqrt 2 * (‖A (θhat - v)‖ / Real.sqrt 2) = ‖A (θhat - v)‖ := by field_simp
        have h8 := mul_le_mul_of_nonneg_left h3 h2.le
        rw [mul_sub, h7]
        linarith
      exact (mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)).trans (hdom _)
  have hsq := pow_le_pow_left₀ (by positivity) hkey 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hn, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
  linarith

/-- **Reference-design information growth** (proof of `prop:v10g-safety-fallback`,
"the distance inequality gives `J_n(a₀) ≥ (√(n C₀) - √Q_n)_+²`").  Here
`C₀ = ½ rootInfo_A(θ)²`, `Q_n = ½ ‖θ̂ - θ‖²_G`, `J_n = ½ rootInfo_G(θ̂)²` and `G ⪰ n M`. -/
theorem reference_info_lower (A G : E →ₗ[ℝ] F) {Q : Set E} (hQ : Q.Nonempty) {n : ℝ}
    (hn : 0 ≤ n) (hdom : ∀ v, Real.sqrt n * ‖A v‖ ≤ ‖G v‖) (θ θhat : E) :
    (max (Real.sqrt (n * (rootInfo A Q θ ^ 2 / 2)) - Real.sqrt (‖G (θhat - θ)‖ ^ 2 / 2)) 0) ^ 2
      ≤ rootInfo G Q θhat ^ 2 / 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have e1 : Real.sqrt (n * (rootInfo A Q θ ^ 2 / 2)) = Real.sqrt n * rootInfo A Q θ / Real.sqrt 2 := by
    rw [Real.sqrt_mul hn, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq rootInfo_nonneg]
    ring
  have e2 : Real.sqrt (‖G (θhat - θ)‖ ^ 2 / 2) = ‖G (θhat - θ)‖ / Real.sqrt 2 := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have h3 : Real.sqrt n * rootInfo A Q θ ≤ rootInfo G Q θ :=
    rootInfo_mono_design hQ (Real.sqrt_nonneg _) hdom
  have h4 := (abs_sub_le_iff.mp (rootInfo_lipschitz G Q θ θhat)).1
  have h4' : ‖G (θ - θhat)‖ = ‖G (θhat - θ)‖ := by rw [← neg_sub, map_neg, norm_neg]
  rw [h4'] at h4
  have h5 : Real.sqrt n * rootInfo A Q θ / Real.sqrt 2 - ‖G (θhat - θ)‖ / Real.sqrt 2 ≤
      rootInfo G Q θhat / Real.sqrt 2 := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) h2.le
  have h6 : max (Real.sqrt (n * (rootInfo A Q θ ^ 2 / 2)) - Real.sqrt (‖G (θhat - θ)‖ ^ 2 / 2)) 0
      ≤ rootInfo G Q θhat / Real.sqrt 2 := by
    rw [e1, e2]
    exact max_le h5 (div_nonneg rootInfo_nonneg h2.le)
  have h7 := pow_le_pow_left₀ (le_max_right _ _) h6 2
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h7
  exact h7

end Certify

/-! ### `lem:bay-fc-inversion` and the explicit budgets of `app:bay-finite` -/

section Budgets

open Real

/-- The budget `x = a + 2 b log(a + b + 1)` of `lem:bay-fc-inversion`. -/
noncomputable def logBudget (a b : ℝ) : ℝ := a + 2 * b * Real.log (a + b + 1)

/-- **Elementary logarithmic budget inversion** (`lem:bay-fc-inversion`).  For `a ≥ 0`,
`b ≥ 1` and `x = a + 2 b log(a + b + 1)`: `x ≥ a + b log(x + 1)`, `x > b`, and
`n ≥ a + b log(n + 1)` for every real `n ≥ x`. -/
theorem log_budget_inversion {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) :
    a + b * Real.log (logBudget a b + 1) ≤ logBudget a b ∧ b < logBudget a b ∧
      ∀ n : ℝ, logBudget a b ≤ n → a + b * Real.log (n + 1) ≤ n := by
  set A := a + b + 1 with hA
  have hA2 : 2 ≤ A := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogA : Real.log 2 ≤ Real.log A := Real.log_le_log (by norm_num) hA2
  have h2log : 2 * Real.log A ≤ A := by
    have h1 : Real.log (A / 2) ≤ A / 2 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : Real.log A = Real.log (A / 2) + Real.log 2 := by
      rw [← Real.log_mul (by linarith) (by norm_num)]
      congr 1; ring
    linarith [Real.log_two_lt_d9]
  set x := logBudget a b with hx
  have hxdef : x = a + 2 * b * Real.log A := rfl
  have hxb : b < x := by
    rw [hxdef]
    nlinarith
  have hx1 : x + 1 ≤ A ^ 2 := by
    rw [hxdef]
    nlinarith
  have hfirst : a + b * Real.log (x + 1) ≤ x := by
    have h1 : Real.log (x + 1) ≤ Real.log (A ^ 2) := Real.log_le_log (by linarith) hx1
    have h2 : Real.log (A ^ 2) = 2 * Real.log A := by
      rw [Real.log_pow]; norm_num
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ b)
    linarith [hxdef]
  refine ⟨hfirst, hxb, fun n hn => ?_⟩
  have hx0 : 0 < x + 1 := by linarith
  have hn0 : 0 < n + 1 := by linarith
  have h1 : Real.log ((n + 1) / (x + 1)) ≤ (n + 1) / (x + 1) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hn0 hx0)
  rw [Real.log_div hn0.ne' hx0.ne'] at h1
  have h2 : b * ((n + 1) / (x + 1) - 1) ≤ n - x := by
    have h3 : (n + 1) / (x + 1) - 1 = (n - x) / (x + 1) := by field_simp; ring
    rw [h3, ← mul_div_assoc, div_le_iff₀ hx0]
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ b)
  linarith

/-- `ψ_d(u) = d/2 + √(d u) + u`, the chi-square boundary of `app:bay-finite`. -/
noncomputable def psiD (d u : ℝ) : ℝ := d / 2 + Real.sqrt (d * u) + u

/-- `b_d(k) = d/2 + d/(4k)`. -/
noncomputable def bD (d k : ℝ) : ℝ := d / 2 + d / (4 * k)

lemma psiD_nonneg {d u : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u) : 0 ≤ psiD d u := by
  unfold psiD; positivity

/-- First bound of `eq:v10g-psi`: `ψ_d(u) ≤ d + 2u`. -/
theorem psiD_le_two {d u : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u) : psiD d u ≤ d + 2 * u := by
  have h : Real.sqrt (d * u) ≤ (d + u) / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [sq_nonneg (d - u)]⟩
  unfold psiD; linarith

/-- Second bound of `eq:v10g-psi`: `ψ_d(u) ≤ (1 + k) u + b_d(k)`. -/
theorem psiD_le_young {d u k : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u) (hk : 0 < k) :
    psiD d u ≤ (1 + k) * u + bD d k := by
  have hc : 4 * (k * u) * (d / (4 * k)) = d * u := by field_simp
  have hc0 : 0 ≤ d / (4 * k) := by positivity
  have h : Real.sqrt (d * u) ≤ k * u + d / (4 * k) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [sq_nonneg (k * u - d / (4 * k))]⟩
  unfold psiD bD; linarith

/-- The fresh-design boundary `B(n, β) = ψ_d(log(n (n + 1) / β))`. -/
noncomputable def boundary (d n β : ℝ) : ℝ := psiD d (Real.log (n * (n + 1) / β))

lemma log_boundary_arg {n β : ℝ} (hn : 1 ≤ n) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    0 ≤ Real.log (n * (n + 1) / β) ∧
      Real.log (n * (n + 1) / β) ≤ Real.log (1 / β) + 2 * Real.log (n + 1) := by
  have hnn : 1 ≤ n * (n + 1) := by nlinarith
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ hβ0]; linarith
  · have h1 : Real.log (n * (n + 1) / β) = Real.log (1 / β) + Real.log (n * (n + 1)) := by
      rw [Real.log_div (by positivity) hβ0.ne', Real.log_div one_ne_zero hβ0.ne', Real.log_one]
      ring
    have h2 : Real.log (n * (n + 1)) ≤ Real.log ((n + 1) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    have h3 : Real.log ((n + 1) ^ 2) = 2 * Real.log (n + 1) := by
      rw [Real.log_pow]; norm_num
    linarith

/-! #### `thm:v10g-discovery`: deterministic core -/

/-- `c_* = (1 - k)³ / (1 + 2k)²`. -/
noncomputable def cstar (k : ℝ) : ℝ := (1 - k) ^ 3 / (1 + 2 * k) ^ 2

/-- `A = 4 ℓ² (1 + 2k)² / (k₀ k² (1 - k) C)` of `eq:v10g-discovery-budget`. -/
noncomputable def pilotA (ℓ k0 k C : ℝ) : ℝ :=
  4 * ℓ ^ 2 * (1 + 2 * k) ^ 2 / (k0 * k ^ 2 * (1 - k) * C)

/-- `a_D = A (d + 2 log(1/α))`. -/
noncomputable def aD (A d α : ℝ) : ℝ := A * (d + 2 * Real.log (1 / α))

/-- `b_D = max {1, 4A}`. -/
noncomputable def bDm (A : ℝ) : ℝ := max 1 (4 * A)

/-- `D̄ = 2 x_D + q + 2`, `x_D = a_D + 2 b_D log(a_D + b_D + 1)`. -/
noncomputable def Dbar (A d α q : ℝ) : ℝ := 2 * logBudget (aD A d α) (bDm A) + q + 2

/-- The oracle contract `eq:v10g-oracle` and the root modulus give
`√(C_k(θ)) - 2e ≤ √l`: here `hgap` is `C_k(v) ≤ u ≤ l + e²` and `hmod` is
`√(C_k(θ)) ≤ √(C_k(v)) + e`. -/
lemma oracle_root_lower {l e Ckv Ckθ : ℝ} (hl : 0 ≤ l) (he : 0 ≤ e) (hgap : Ckv ≤ l + e ^ 2)
    (hmod : Real.sqrt Ckθ ≤ Real.sqrt Ckv + e) : Real.sqrt Ckθ - 2 * e ≤ Real.sqrt l := by
  have h1 : Real.sqrt Ckv ≤ Real.sqrt l + e := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hl, Real.sqrt_nonneg l, mul_nonneg he (Real.sqrt_nonneg l)]
  linarith

/-- **The planning gate succeeds once the pilot radius is small**
(proof of `thm:v10g-discovery`): if `√(C_k(θ)) - 2e ≤ √l` and
`e ≤ k √(C_k(θ)) / (1 + 2k)` then the gate `e² ≤ k² l` of `eq:v10g-gate` holds. -/
theorem pilot_gate_succeeds {k e l Ck : ℝ} (hk : 0 < k) (he : 0 ≤ e) (hl : 0 ≤ l)
    (horacle : Real.sqrt Ck - 2 * e ≤ Real.sqrt l)
    (hsmall : e ≤ k * Real.sqrt Ck / (1 + 2 * k)) : e ^ 2 ≤ k ^ 2 * l := by
  have hpos : 0 < 1 + 2 * k := by linarith
  rw [le_div_iff₀ hpos] at hsmall
  have h1 : e ≤ k * Real.sqrt l := by nlinarith
  have h2 := pow_le_pow_left₀ he h1 2
  rw [mul_pow, Real.sq_sqrt hl] at h2
  exact h2

/-- **The frozen record is near-optimal** (`eq:v10g-plan-rate`).  At a committing stage
(`hgate`), with `√(C_k(θ)) - 2e ≤ √l` from the oracle contract and root modulus
(`oracle_root_lower`), `C_k(θ) ≥ (1 - k) C` from the exploration floor, and
`√l - e ≤ √(I_a(θ, w))` from `l ≤ I_a(v, w)` and the parameter modulus:
`(√l - e)² ≥ c_* C` and `I_a(θ, w) ≥ (√l - e)²`. -/
theorem frozen_plan_rate {k e l Ck C Iθ : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (he : 0 ≤ e)
    (hl : 0 ≤ l) (hC : 0 ≤ C) (hIθ : 0 ≤ Iθ)
    (hgate : e ^ 2 ≤ k ^ 2 * l) (horacle : Real.sqrt Ck - 2 * e ≤ Real.sqrt l)
    (hfloor : (1 - k) * C ≤ Ck) (hmod : Real.sqrt l - e ≤ Real.sqrt Iθ) :
    cstar k * C ≤ (Real.sqrt l - e) ^ 2 ∧ (Real.sqrt l - e) ^ 2 ≤ Iθ := by
  have hsl := Real.sqrt_nonneg l
  have hek : e ≤ k * Real.sqrt l := by
    have h1 : e ^ 2 ≤ (k * Real.sqrt l) ^ 2 := by rw [mul_pow, Real.sq_sqrt hl]; exact hgate
    exact (pow_le_pow_iff_left₀ he (by positivity) two_ne_zero).mp h1
  have hCk0 : 0 ≤ Ck := (mul_nonneg (by linarith) hC).trans hfloor
  have h0 : 0 ≤ Real.sqrt l - e := by nlinarith
  have h1 : Real.sqrt Ck ≤ (1 + 2 * k) * Real.sqrt l := by nlinarith
  have h2 : Ck ≤ (1 + 2 * k) ^ 2 * l := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg Ck) h1 2
    rwa [Real.sq_sqrt hCk0, mul_pow, Real.sq_sqrt hl] at this
  have h3 : (1 - k) ^ 2 * l ≤ (Real.sqrt l - e) ^ 2 := by
    have h4 : (1 - k) * Real.sqrt l ≤ Real.sqrt l - e := by linarith
    have := pow_le_pow_left₀ (mul_nonneg (by linarith) hsl) h4 2
    rwa [mul_pow, Real.sq_sqrt hl] at this
  constructor
  · unfold cstar
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h5 : (1 - k) ^ 3 * C ≤ (1 - k) ^ 2 * Ck := by
      have := mul_le_mul_of_nonneg_left hfloor (sq_nonneg (1 - k))
      nlinarith
    have h6 : (1 - k) ^ 2 * Ck ≤ (1 - k) ^ 2 * ((1 + 2 * k) ^ 2 * l) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have h7 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (1 + 2 * k))
    nlinarith
  · have := pow_le_pow_left₀ h0 hmod 2
    rwa [Real.sq_sqrt hIθ] at this

/-- **The explicit pilot budget forces a small radius** (proof of `thm:v10g-discovery`).
At stage `j` with `n = 2^j`, if `n ≥ a_D + b_D log(n + 1)` then every admissible
`e_j ≤ √2 ℓ ρ_j` (so `e_j² ≤ 4 ℓ² ψ_d(u_j) / (k₀ 2^j)`, `u_j = log((j+1)(j+2)/α)`)
satisfies `e_j ≤ k √(C_k(θ)) / (1 + 2k)`. -/
theorem pilot_budget_sufficient {ℓ k0 k C Ck d α e : ℝ} {j : ℕ} (hℓ : 0 < ℓ) (hk0 : 0 < k0)
    (hk : 0 < k) (hk1 : k < 1) (hC : 0 < C) (hd : 0 ≤ d) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (he0 : 0 ≤ e)
    (he : e ^ 2 ≤ 4 * ℓ ^ 2 * psiD d (Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2) / α)) /
      (k0 * 2 ^ j))
    (hfloor : (1 - k) * C ≤ Ck)
    (hbud : aD (pilotA ℓ k0 k C) d α + bDm (pilotA ℓ k0 k C) * Real.log (2 ^ j + 1) ≤ 2 ^ j) :
    e ≤ k * Real.sqrt Ck / (1 + 2 * k) := by
  set A := pilotA ℓ k0 k C with hAdef
  have hden : 0 < k0 * k ^ 2 * (1 - k) * C := by
    have : 0 < 1 - k := by linarith
    positivity
  have hA : 0 < A := by rw [hAdef]; unfold pilotA; positivity
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hj : (j : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast (Nat.lt_two_pow_self : j < 2 ^ j)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hprod : ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ ((2 : ℝ) ^ j + 1) ^ 2 := by nlinarith
  have hprod1 : 1 ≤ ((j : ℝ) + 1) * ((j : ℝ) + 2) := by nlinarith
  set L := Real.log (2 ^ j + 1) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  set u := Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2) / α) with hu
  have hu0 : 0 ≤ u := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hα0]; linarith
  have hu1 : u ≤ Real.log (1 / α) + 2 * L := by
    have h1 : u = Real.log (1 / α) + Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      rw [hu, Real.log_div (by positivity) hα0.ne', Real.log_div one_ne_zero hα0.ne',
        Real.log_one]
      ring
    have h2 : Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤ Real.log (((2 : ℝ) ^ j + 1) ^ 2) :=
      Real.log_le_log (by linarith) hprod
    have h3 : Real.log (((2 : ℝ) ^ j + 1) ^ 2) = 2 * L := by
      rw [Real.log_pow, hL]; push_cast; ring
    linarith
  have hψ := psiD_le_two hd hu0
  have hψ0 := psiD_nonneg hd hu0
  have hAψ : A * psiD d u ≤ 2 ^ j := by
    have h1 : A * psiD d u ≤ A * (d + 2 * (Real.log (1 / α) + 2 * L)) :=
      mul_le_mul_of_nonneg_left (by linarith) hA.le
    have h2 : 4 * A ≤ bDm A := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_right h2 hL0
    unfold aD at hbud
    nlinarith
  have hAψ' : 4 * ℓ ^ 2 * (1 + 2 * k) ^ 2 * psiD d u ≤ 2 ^ j * (k0 * k ^ 2 * (1 - k) * C) := by
    have h1 := hAψ
    rw [hAdef] at h1
    unfold pilotA at h1
    rwa [div_mul_eq_mul_div, div_le_iff₀ hden] at h1
  have hCk0 : 0 ≤ Ck := (mul_nonneg (by linarith) hC.le).trans hfloor
  have hrhs0 : 0 ≤ k * Real.sqrt Ck / (1 + 2 * k) := by positivity
  refine (pow_le_pow_iff_left₀ he0 hrhs0 two_ne_zero).mp ?_
  rw [div_pow, mul_pow, Real.sq_sqrt hCk0]
  refine he.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : k ^ 2 * ((1 - k) * C) ≤ k ^ 2 * Ck := mul_le_mul_of_nonneg_left hfloor (sq_nonneg k)
  have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ k0 * 2 ^ j)
  nlinarith

/-- **A committing dyadic stage exists within the budget** (proof of
`thm:v10g-discovery`): there is a stage `j` with `2^j ≥ a + b log(2^j + 1)` and
`2^j < 2 x + 2`, `x = a + 2 b log(a + b + 1)`.  With cumulative pilot counts at most
`2^j + q` this is the observation budget `D̄ = 2 x_D + q + 2`. -/
theorem exists_pilot_stage {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) :
    ∃ j : ℕ, a + b * Real.log (2 ^ j + 1) ≤ 2 ^ j ∧ (2 : ℝ) ^ j < 2 * logBudget a b + 2 := by
  obtain ⟨-, hxb, hpers⟩ := log_budget_inversion ha hb
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := logBudget a b) (y := (2 : ℝ))
    (by linarith) (by norm_num)
  refine ⟨n + 1, hpers _ hn2.le, ?_⟩
  rw [pow_succ]
  linarith

/-! #### `prop:v10g-safety-fallback`: deterministic core -/

/-- `a_F` of `eq:v10g-fallback-budget`. -/
noncomputable def aF (d δ C0 : ℝ) : ℝ :=
  (4 * (d + 2 + 2 * Real.log (2 / δ)) + 8 * d * Real.log 2) / C0

/-- `b_F = max {1, 16 / C₀}`. -/
noncomputable def bF (C0 : ℝ) : ℝ := max 1 (16 / C0)

/-- `H_δ = q + x_F + 2 + 16 / C₀`. -/
noncomputable def Hdelta (q d δ C0 : ℝ) : ℝ :=
  q + logBudget (aF d δ C0) (bF C0) + 2 + 16 / C0

lemma aF_nonneg {d δ C0 : ℝ} (hd : 0 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hC0 : 0 < C0) :
    0 ≤ aF d δ C0 := by
  have h1 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold aF; positivity

/-- **Both sufficient conditions hold beyond `x_F`** (proof of
`prop:v10g-safety-fallback`): for every real `n ≥ x_F`,
`n C₀ ≥ 4 (B(n, δ/2) + 2)` and `n C₀ ≥ 8 d log 2`. -/
theorem fallback_budget_sufficient {d δ C0 n : ℝ} (hd : 0 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hC0 : 0 < C0) (hn : logBudget (aF d δ C0) (bF C0) ≤ n) :
    4 * (boundary d n (δ / 2) + 2) ≤ n * C0 ∧ 8 * d * Real.log 2 ≤ n * C0 := by
  have haF := aF_nonneg hd hδ0 hδ1 hC0
  have hbF : 1 ≤ bF C0 := le_max_left _ _
  obtain ⟨-, hxb, hpers⟩ := log_budget_inversion haF hbF
  have hn1 : 1 ≤ n := by linarith
  have hbud := hpers n hn
  have hL0 : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
  obtain ⟨hu0, hu1⟩ := log_boundary_arg (β := δ / 2) hn1 (by linarith) (by linarith)
  have hψ := psiD_le_two hd hu0
  have h12 : (1 : ℝ) / (δ / 2) = 2 / δ := by field_simp
  rw [h12] at hu1
  have h1 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hid : C0 * aF d δ C0 = 4 * (d + 2 + 2 * Real.log (2 / δ)) + 8 * d * Real.log 2 := by
    unfold aF; field_simp
  have h16 : 16 ≤ C0 * bF C0 := by
    have : 16 / C0 ≤ bF C0 := le_max_right _ _
    rw [div_le_iff₀ hC0] at this
    linarith
  have h3 := mul_le_mul_of_nonneg_left hbud hC0.le
  have h4 := mul_le_mul_of_nonneg_right h16 hL0
  have h5 : 0 ≤ d * Real.log 2 := mul_nonneg hd h2
  have h6 : 0 ≤ C0 * bF C0 * Real.log (n + 1) := by positivity
  unfold boundary
  constructor <;> nlinarith

/-- **The safeguard stops unless the noise is large** (proof of
`prop:v10g-safety-fallback`): if `n C₀ ≥ 4 (B + 2)` and `Q_n ≤ n C₀ / 4` then
`(√(n C₀) - √Q_n)_+² ≥ B + 2`. -/
theorem fallback_stops {n C0 B Qn : ℝ} (hQ : 0 ≤ Qn) (hB : 4 * (B + 2) ≤ n * C0)
    (hQn : Qn ≤ n * C0 / 4) :
    B + 2 ≤ (max (Real.sqrt (n * C0) - Real.sqrt Qn) 0) ^ 2 := by
  have hnC : 0 ≤ n * C0 := by linarith
  have h1 : Real.sqrt Qn ≤ Real.sqrt (n * C0) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, Real.sq_sqrt hnC]; linarith
  have h2 : Real.sqrt (n * C0) / 2 ≤ max (Real.sqrt (n * C0) - Real.sqrt Qn) 0 :=
    le_max_of_le_left (by linarith)
  have h3 := pow_le_pow_left₀ (by positivity) h2 2
  rw [div_pow, Real.sq_sqrt hnC] at h3
  linarith

/-- `2^{d/2} e^{-n C₀ / 8} ≤ e^{-n C₀ / 16}` whenever `n C₀ ≥ 8 d log 2`. -/
theorem mgf_tail_simplify {d x : ℝ} (hx : 8 * d * Real.log 2 ≤ x) :
    (2 : ℝ) ^ (d / 2) * Real.exp (-x / 8) ≤ Real.exp (-x / 16) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- `(1 - e^{-c})⁻¹ ≤ 1 + 1/c` for `c > 0`. -/
theorem geom_tail_le {c : ℝ} (hc : 0 < c) : (1 - Real.exp (-c))⁻¹ ≤ 1 + 1 / c := by
  have h1 : c + 1 ≤ Real.exp c := Real.add_one_le_exp c
  have he : Real.exp (-c) = (Real.exp c)⁻¹ := Real.exp_neg c
  have hpos : 0 < Real.exp c := Real.exp_pos c
  have h2 : 0 < 1 - Real.exp (-c) := by
    rw [he, sub_pos, inv_lt_one₀ hpos]; linarith
  rw [inv_le_iff_one_le_mul₀ h2, he]
  have h3 : (Real.exp c)⁻¹ * (c + 1) ≤ 1 := by
    rw [inv_mul_le_iff₀ hpos]; linarith
  have h4 : (1 + 1 / c) * (1 - (Real.exp c)⁻¹) = 1 + (1 - (Real.exp c)⁻¹ * (c + 1)) / c := by
    field_simp; ring
  rw [h4]
  have : 0 ≤ (1 - (Real.exp c)⁻¹ * (c + 1)) / c := div_nonneg (by linarith) hc.le
  linarith

/-! #### `thm:v10g-expectation`: deterministic core -/

/-- `r_C` of `eq:v10g-confirm-budget`. -/
noncomputable def rC (d k c0 α : ℝ) : ℝ :=
  ((1 + k) * ((1 + k) * Real.log 2 + bD d k + 2) +
    (1 + 1 / k) * ((1 + k) * Real.log (1 / α) + bD d k)) / c0

/-- `a_C = (1 + k)² log(1/δ) / c₀ + r_C`. -/
noncomputable def aC (d k c0 δ α : ℝ) : ℝ := (1 + k) ^ 2 * Real.log (1 / δ) / c0 + rC d k c0 α

/-- `b_C = max {1, 2 (1 + k) ((1 + k) + (1 + 1/k)) / c₀}`. -/
noncomputable def bC (k c0 : ℝ) : ℝ := max 1 (2 * (1 + k) * ((1 + k) + (1 + 1 / k)) / c0)

/-- **Confirmation statistic on the good event** (proof of `thm:v10g-expectation`, first
display).  With `d_M = ‖θ̂_n - v‖_{M(w)}`, `g = ‖θ̂_n - θ‖_{G_n}`, `Q_n = g² / 2`, the triangle
inequality and `G_n ⪰ n M(w)` give `d_M ≤ g / √n + √2 e`; hence
`Z_n = n [√l - d_M / √2]_+² ≥ [√n (√l - e) - √Q_n]_+²`. -/
theorem confirm_stat_lower {n l e dM g : ℝ} (hn : 0 < n) (hg : 0 ≤ g)
    (htri : dM ≤ g / Real.sqrt n + Real.sqrt 2 * e) :
    (max (Real.sqrt n * (Real.sqrt l - e) - Real.sqrt (g ^ 2 / 2)) 0) ^ 2 ≤
      n * (max (Real.sqrt l - dM / Real.sqrt 2) 0) ^ 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have e2 : Real.sqrt (g ^ 2 / 2) = g / Real.sqrt 2 := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hg]
  have h3 : dM / Real.sqrt 2 ≤ g / (Real.sqrt n * Real.sqrt 2) + e := by
    rw [div_le_iff₀ h2]
    have : (g / (Real.sqrt n * Real.sqrt 2) + e) * Real.sqrt 2 = g / Real.sqrt n + Real.sqrt 2 * e := by
      field_simp
    linarith
  have h4 : Real.sqrt n * (Real.sqrt l - e) - Real.sqrt (g ^ 2 / 2) ≤
      Real.sqrt n * (Real.sqrt l - dM / Real.sqrt 2) := by
    rw [e2]
    have h5 : Real.sqrt n * (g / (Real.sqrt n * Real.sqrt 2)) = g / Real.sqrt 2 := by
      field_simp
    have h6 := mul_le_mul_of_nonneg_left h3 hsn.le
    nlinarith
  have h7 : max (Real.sqrt n * (Real.sqrt l - e) - Real.sqrt (g ^ 2 / 2)) 0 ≤
      Real.sqrt n * max (Real.sqrt l - dM / Real.sqrt 2) 0 := by
    refine max_le (h4.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hsn.le)) ?_
    exact mul_nonneg hsn.le (le_max_right _ _)
  have h8 := pow_le_pow_left₀ (le_max_right _ _) h7 2
  rwa [mul_pow, Real.sq_sqrt hn.le] at h8

/-- **The crossing condition** `eq:v10g-crossing` follows from the confirmation budget
(Young's inequality with parameter `k`, the second bound of `eq:v10g-psi`, and
`n (n + 1) ≤ (n + 1)²`): if `n ≥ a_C + b_C log(n + 1)` then
`√(n c₀) ≥ √(B(n, δ/2) + 2) + √(B(n, α))`. -/
theorem confirm_crossing {d k c0 δ α n : ℝ} (hd : 0 ≤ d) (hk : 0 < k) (hc0 : 0 < c0)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 1 ≤ n)
    (hbud : aC d k c0 δ α + bC k c0 * Real.log (n + 1) ≤ n) :
    Real.sqrt (boundary d n (δ / 2) + 2) + Real.sqrt (boundary d n α) ≤ Real.sqrt (n * c0) := by
  set L := Real.log (n + 1) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  obtain ⟨hu0, hu1⟩ := log_boundary_arg (β := δ / 2) hn (by linarith) (by linarith)
  obtain ⟨hv0, hv1⟩ := log_boundary_arg (β := α) hn hα0 hα1
  have h12 : Real.log (1 / (δ / 2)) = Real.log (1 / δ) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1; field_simp
  rw [h12] at hu1
  set X := boundary d n (δ / 2) + 2 with hX
  set Y := boundary d n α with hY
  have hX0 : 0 ≤ X := by
    have := psiD_nonneg hd hu0
    rw [hX]; unfold boundary; linarith
  have hY0 : 0 ≤ Y := psiD_nonneg hd hv0
  have hXle : X ≤ (1 + k) * (Real.log (1 / δ) + Real.log 2 + 2 * L) + bD d k + 2 := by
    have h1 := psiD_le_young hd hu0 hk
    have h2 := mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℝ) ≤ 1 + k)
    rw [hX]; unfold boundary; linarith
  have hYle : Y ≤ (1 + k) * (Real.log (1 / α) + 2 * L) + bD d k := by
    have h1 := psiD_le_young hd hv0 hk
    have h2 := mul_le_mul_of_nonneg_left hv1 (by linarith : (0 : ℝ) ≤ 1 + k)
    rw [hY]; unfold boundary; linarith
  have hk1 : 0 < 1 + 1 / k := by positivity
  -- Young
  have hyoung : (Real.sqrt X + Real.sqrt Y) ^ 2 ≤ (1 + k) * X + (1 + 1 / k) * Y := by
    have hp := Real.sq_sqrt hX0
    have hq := Real.sq_sqrt hY0
    have hcross : 2 * Real.sqrt X * Real.sqrt Y ≤ k * Real.sqrt X ^ 2 + Real.sqrt Y ^ 2 / k := by
      rw [← sub_nonneg]
      have : k * Real.sqrt X ^ 2 + Real.sqrt Y ^ 2 / k - 2 * Real.sqrt X * Real.sqrt Y =
          (k * Real.sqrt X - Real.sqrt Y) ^ 2 / k := by field_simp; ring
      rw [this]; positivity
    have h1 : (1 + 1 / k) * Y = Y + Y / k := by ring
    have hexp : (Real.sqrt X + Real.sqrt Y) ^ 2 =
        Real.sqrt X ^ 2 + 2 * Real.sqrt X * Real.sqrt Y + Real.sqrt Y ^ 2 := by ring
    rw [hp, hq] at hcross
    rw [hexp, hp, hq, h1]
    linarith
  have hid : c0 * aC d k c0 δ α = (1 + k) ^ 2 * Real.log (1 / δ) +
      ((1 + k) * ((1 + k) * Real.log 2 + bD d k + 2) +
        (1 + 1 / k) * ((1 + k) * Real.log (1 / α) + bD d k)) := by
    unfold aC rC
    rw [mul_add, mul_div_cancel₀ _ hc0.ne', mul_div_cancel₀ _ hc0.ne']
  have hbC : 2 * (1 + k) * ((1 + k) + (1 + 1 / k)) ≤ c0 * bC k c0 := by
    have : 2 * (1 + k) * ((1 + k) + (1 + 1 / k)) / c0 ≤ bC k c0 := le_max_right _ _
    rw [div_le_iff₀ hc0] at this
    linarith
  have hsum : (1 + k) * X + (1 + 1 / k) * Y ≤ n * c0 := by
    have h1 := mul_le_mul_of_nonneg_left hXle (by linarith : (0 : ℝ) ≤ 1 + k)
    have h2 := mul_le_mul_of_nonneg_left hYle hk1.le
    have h3 := mul_le_mul_of_nonneg_left hbud hc0.le
    have h4 := mul_le_mul_of_nonneg_right hbC hL0
    have h5 : (1 + k) * ((1 + k) * (Real.log (1 / δ) + Real.log 2 + 2 * L) + bD d k + 2) +
        (1 + 1 / k) * ((1 + k) * (Real.log (1 / α) + 2 * L) + bD d k) =
        c0 * aC d k c0 δ α + 2 * (1 + k) * ((1 + k) + (1 + 1 / k)) * L := by
      rw [hid]; ring
    nlinarith
  apply Real.le_sqrt_of_sq_le
  linarith

/-- **Confirmation stops at a crossing count** (proof of `thm:v10g-expectation`): on the
good event `Z_n ≥ [√(n c₀) - √(B(n, α))]_+²`; with the crossing condition this gives
`Z_n ≥ B(n, δ/2) + 2`, so the outward-rounded test `Z_n - 1 ≥ B(n, δ/2) + 1` fires. -/
theorem confirm_stops {nc0 Bδ Bα Zn : ℝ}
    (hcross : Real.sqrt (Bδ + 2) + Real.sqrt Bα ≤ Real.sqrt nc0) (hB : 0 ≤ Bδ + 2)
    (hZ : (max (Real.sqrt nc0 - Real.sqrt Bα) 0) ^ 2 ≤ Zn) : Bδ + 2 ≤ Zn := by
  have h1 : Real.sqrt (Bδ + 2) ≤ max (Real.sqrt nc0 - Real.sqrt Bα) 0 :=
    le_max_of_le_left (by linarith)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt hB] at h2
  linarith

/-- On the good event (`Q_n ≤ B(n, α)`) and with the plan rate `c₀ ≤ (√l - e)²` of
`eq:v10g-plan-rate`: `[√n (√l - e) - √Q_n]_+² ≥ [√(n c₀) - √(B(n, α))]_+²`. -/
theorem confirm_stat_mono {n c0 sl Qn Bα : ℝ} (hn : 0 ≤ n) (hsl : 0 ≤ sl) (hc : c0 ≤ sl ^ 2)
    (hQ : Qn ≤ Bα) :
    (max (Real.sqrt (n * c0) - Real.sqrt Bα) 0) ^ 2 ≤
      (max (Real.sqrt n * sl - Real.sqrt Qn) 0) ^ 2 := by
  have h1 : Real.sqrt c0 ≤ sl := by
    rw [Real.sqrt_le_iff]; exact ⟨hsl, hc⟩
  have h2 : Real.sqrt (n * c0) ≤ Real.sqrt n * sl := by
    rw [Real.sqrt_mul hn]
    exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
  have h3 : Real.sqrt Qn ≤ Real.sqrt Bα := Real.sqrt_le_sqrt hQ
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 (by linarith)) 2

/-- **Constant-share calendar, main branch**: the main procedure has received `m`
observations by a global time `t ≤ m / (1 - k) + 1` (the safeguard receives `⌊k t⌋` of the
first `t` observations). -/
theorem calendar_main {k : ℝ} (hk1 : k < 1) (m : ℕ) :
    ∃ t : ℕ, (t : ℝ) ≤ m / (1 - k) + 1 ∧ (m : ℝ) ≤ t - ⌊k * t⌋ := by
  have hpos : 0 < 1 - k := by linarith
  refine ⟨⌈(m : ℝ) / (1 - k)⌉₊, (Nat.ceil_lt_add_one (by positivity)).le, ?_⟩
  have h1 : (m : ℝ) / (1 - k) ≤ ⌈(m : ℝ) / (1 - k)⌉₊ := Nat.le_ceil _
  rw [div_le_iff₀ hpos] at h1
  have h2 := Int.floor_le (k * (⌈(m : ℝ) / (1 - k)⌉₊ : ℝ))
  linarith

/-- **Constant-share calendar, safeguard**: the safeguard has received `F` observations
by a global time `t ≤ F / k + 1`. -/
theorem calendar_safeguard {k : ℝ} (hk0 : 0 < k) (F : ℕ) :
    ∃ t : ℕ, (t : ℝ) ≤ F / k + 1 ∧ (F : ℤ) ≤ ⌊k * t⌋ := by
  refine ⟨⌈(F : ℝ) / k⌉₊, (Nat.ceil_lt_add_one (by positivity)).le, ?_⟩
  have h1 : (F : ℝ) / k ≤ ⌈(F : ℝ) / k⌉₊ := Nat.le_ceil _
  rw [div_le_iff₀ hk0] at h1
  rw [Int.le_floor]
  push_cast
  linarith

/-- The calendar gives the safeguard at most one observation per global step. -/
theorem calendar_increment {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (t : ℕ) :
    ⌊k * (t : ℝ)⌋ ≤ ⌊k * ((t : ℝ) + 1)⌋ ∧ ⌊k * ((t : ℝ) + 1)⌋ ≤ ⌊k * (t : ℝ)⌋ + 1 := by
  constructor
  · exact Int.floor_le_floor (by nlinarith)
  · rw [← Int.floor_add_one]
    exact Int.floor_le_floor (by nlinarith)

/-! #### `cor:v10g-target`: the explicit algebra -/

/-- `D₀ = 2 a₀ + 4 b_D log(a₀ + b_D + 1) + q + 2`, `a₀ = A (d + 2 log 8)`. -/
noncomputable def D0 (A d q : ℝ) : ℝ :=
  2 * (A * (d + 2 * Real.log 8)) +
    4 * bDm A * Real.log (A * (d + 2 * Real.log 8) + bDm A + 1) + q + 2

/-- `D_extra(J) = 8 A log J + 4 b_D log(1 + 4 A log J / (a₀ + b_D + 1))`. -/
noncomputable def Dextra (A d J : ℝ) : ℝ :=
  8 * A * Real.log J +
    4 * bDm A * Real.log (1 + 4 * A * Real.log J / (A * (d + 2 * Real.log 8) + bDm A + 1))

/-- `eq:v10g-D-split`: with `α = 1 / (8 J²)`, `D̄ = D₀ + D_extra(J)` exactly. -/
theorem discovery_budget_split {A d J q : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d) (hJ : 1 ≤ J) :
    Dbar A d (1 / (8 * J ^ 2)) q = D0 A d q + Dextra A d J := by
  have hJ0 : 0 < J := by linarith
  have hlJ : 0 ≤ Real.log J := Real.log_nonneg hJ
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hb : 1 ≤ bDm A := le_max_left _ _
  have h1 : Real.log (1 / (1 / (8 * J ^ 2))) = Real.log 8 + 2 * Real.log J := by
    rw [one_div_one_div, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  set a0 := A * (d + 2 * Real.log 8) with ha0
  have ha0n : 0 ≤ a0 := by positivity
  have hpos : 0 < a0 + bDm A + 1 := by linarith
  have haD : aD A d (1 / (8 * J ^ 2)) = a0 + 4 * A * Real.log J := by
    unfold aD; rw [h1, ha0]; ring
  have hlog : Real.log (a0 + 4 * A * Real.log J + bDm A + 1) =
      Real.log (a0 + bDm A + 1) + Real.log (1 + 4 * A * Real.log J / (a0 + bDm A + 1)) := by
    rw [← Real.log_mul hpos.ne' (by positivity)]
    congr 1
    field_simp
    ring
  unfold Dbar logBudget D0 Dextra
  rw [haD, hlog]
  ring

/-- The leading multiplier of `cor:v10g-target`:
`(1 + k)² (1 + 2k)² / (1 - k)⁴ ≤ 1 + s` for `k = s / 16`, `0 < s ≤ 1`. -/
theorem leading_multiplier_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (1 + s / 16) ^ 2 * (1 + 2 * (s / 16)) ^ 2 / (1 - s / 16) ^ 4 ≤ 1 + s := by
  set k := s / 16 with hk
  have hk0 : 0 < k := by positivity
  have hk1 : k ≤ 1 / 16 := by rw [hk]; linarith
  have hs : s = 16 * k := by rw [hk]; ring
  have hpos : 0 < (1 - k) ^ 4 := by
    have : 0 < 1 - k := by linarith
    positivity
  rw [div_le_iff₀ hpos, hs]
  have hid : (1 + 16 * k) * (1 - k) ^ 4 - (1 + k) ^ 2 * (1 + 2 * k) ^ 2 =
      k * (6 - 71 * k + 80 * k ^ 2 - 67 * k ^ 3 + 16 * k ^ 4) := by ring
  have h3 : k ^ 3 ≤ (1 / 16) ^ 3 := pow_le_pow_left₀ hk0.le hk1 3
  have hinner : 0 ≤ 6 - 71 * k + 80 * k ^ 2 - 67 * k ^ 3 + 16 * k ^ 4 := by
    have := sq_nonneg k
    have := pow_nonneg hk0.le 4
    norm_num at h3
    linarith
  have := mul_nonneg hk0.le hinner
  linarith

/-- `𝓑_δ` of `eq:v10g-finite`. -/
noncomputable def Bdelta (Dbar xC q k α H : ℝ) : ℝ :=
  (Dbar + xC + q + 1) / (1 - k) + 1 + 2 * α * (H / k + 1)

/-- The remainder `R₁₀` of `eq:v10g-remainder`. -/
noncomputable def R10 (Dx rC LC k J H : ℝ) : ℝ :=
  (Dx + rC + LC + 1) / (1 - k) + 1 + H / (4 * k * J ^ 2) + 1 / (4 * J ^ 2)

/-- **Finite-confidence correlated confirmation bound, explicit algebra**
(`cor:v10g-target`).  With `k = s/16`, `α = 1/(8 J²)`, `c₀ = c_* C`,
`x_C = a_C + 2 b_C log(a_C + b_C + 1)` and `D̄ = D₀ + D_extra(J)`
(`discovery_budget_split`), the bound `𝓑_δ` of `thm:v10g-expectation` is at most
`(D₀ + q)/(1 - k) + (1 + s) C⁻¹ log(1/δ) + R₁₀`, i.e. `eq:v10g-target` with
`T_*^ε = 1/C`.  The hypothesis that `𝔼_θ τ ≤ 𝓑_δ` is `thm:v10g-expectation`. -/
theorem target_bound {s C δ J q H A d : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hC : 0 < C)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hJ : 1 ≤ J) (hA : 0 ≤ A) (hd : 0 ≤ d) :
    Bdelta (Dbar A d (1 / (8 * J ^ 2)) q)
        (logBudget (aC d (s / 16) (cstar (s / 16) * C) δ (1 / (8 * J ^ 2)))
          (bC (s / 16) (cstar (s / 16) * C)))
        q (s / 16) (1 / (8 * J ^ 2)) H ≤
      (D0 A d q + q) / (1 - s / 16) + (1 + s) * (1 / C) * Real.log (1 / δ) +
        R10 (Dextra A d J) (rC d (s / 16) (cstar (s / 16) * C) (1 / (8 * J ^ 2)))
          (2 * bC (s / 16) (cstar (s / 16) * C) *
            Real.log (aC d (s / 16) (cstar (s / 16) * C) δ (1 / (8 * J ^ 2)) +
              bC (s / 16) (cstar (s / 16) * C) + 1))
          (s / 16) J H := by
  rw [discovery_budget_split hA hd hJ]
  set k := s / 16 with hk
  have hk0 : 0 < k := by positivity
  have hk1 : k ≤ 1 / 16 := by rw [hk]; linarith
  have h1k : 0 < 1 - k := by linarith
  set c0 := cstar k * C with hc0
  have hcs : 0 < cstar k := by unfold cstar; positivity
  have hc0pos : 0 < c0 := mul_pos hcs hC
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hJ0 : 0 < J := by linarith
  -- the leading term
  have hlead : (1 + k) ^ 2 * Real.log (1 / δ) / c0 / (1 - k) ≤
      (1 + s) * (1 / C) * Real.log (1 / δ) := by
    have hm := leading_multiplier_le hs0 hs1
    rw [← hk] at hm
    have h2 : (1 + k) ^ 2 * Real.log (1 / δ) / c0 / (1 - k) =
        ((1 + k) ^ 2 * (1 + 2 * k) ^ 2 / (1 - k) ^ 4) * (1 / C) * Real.log (1 / δ) := by
      rw [hc0]; unfold cstar; field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) hlog
  set LC := 2 * bC k c0 * Real.log (aC d k c0 δ (1 / (8 * J ^ 2)) + bC k c0 + 1) with hLC
  have hx : logBudget (aC d k c0 δ (1 / (8 * J ^ 2))) (bC k c0) =
      (1 + k) ^ 2 * Real.log (1 / δ) / c0 + rC d k c0 (1 / (8 * J ^ 2)) + LC := by
    unfold logBudget aC; rw [hLC]; unfold aC; ring
  rw [hx]
  unfold Bdelta R10
  have hsplit : (D0 A d q + Dextra A d J +
        ((1 + k) ^ 2 * Real.log (1 / δ) / c0 + rC d k c0 (1 / (8 * J ^ 2)) + LC) + q + 1) /
        (1 - k) =
      (D0 A d q + q) / (1 - k) + (1 + k) ^ 2 * Real.log (1 / δ) / c0 / (1 - k) +
        (Dextra A d J + rC d k c0 (1 / (8 * J ^ 2)) + LC + 1) / (1 - k) := by
    field_simp; ring
  have hα : 2 * (1 / (8 * J ^ 2)) * (H / k + 1) = H / (4 * k * J ^ 2) + 1 / (4 * J ^ 2) := by
    field_simp; ring
  rw [hsplit, hα]
  linarith

end Budgets

/-! ### Rounded designs -/

section Rounding

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rounded counts `⌈n w_x⌉` total between `n` and `n + |X|`. -/
theorem sum_ceil_counts {w : X → ℝ} (hw : w ∈ simplex X) {n : ℝ} (hn : 0 ≤ n) :
    n ≤ ∑ x, (⌈n * w x⌉₊ : ℝ) ∧ ∑ x, (⌈n * w x⌉₊ : ℝ) ≤ n + Fintype.card X := by
  have hsum : ∑ x, n * w x = n := by rw [← mul_sum, hw.2, mul_one]
  constructor
  · calc n = ∑ x, n * w x := hsum.symm
      _ ≤ _ := sum_le_sum (fun x _ => Nat.le_ceil _)
  · calc ∑ x, (⌈n * w x⌉₊ : ℝ) ≤ ∑ x, (n * w x + 1) :=
          sum_le_sum (fun x _ => (Nat.ceil_lt_add_one (mul_nonneg hn (hw.1 x))).le)
      _ = n + Fintype.card X := by
          rw [sum_add_distrib, hsum]; simp

/-- **Gram domination by a rounded design**: counts `c_x ≥ n w_x` give `G ⪰ n M(w)`, in
the form `√n ‖v‖_{M(w)} ≤ ‖v‖_G` used by `frozen_recycle` and `reference_info_lower`. -/
theorem gram_dominates (u : X → E) {w c : X → ℝ} (hw : ∀ x, 0 ≤ w x) {n : ℝ} (hn : 0 ≤ n)
    (hc : ∀ x, n * w x ≤ c x) (v : E) :
    Real.sqrt n * ‖designMap u w v‖ ≤ ‖designMap u c v‖ := by
  have hc0 : ∀ x, 0 ≤ c x := fun x => (mul_nonneg hn (hw x)).trans (hc x)
  have hsq : (Real.sqrt n * ‖designMap u w v‖) ^ 2 ≤ ‖designMap u c v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn, norm_designMap_sq u hw, norm_designMap_sq u hc0, mul_sum]
    refine sum_le_sum (fun x _ => ?_)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc x) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- **Pilot radius** (`eq:v10g-pilot-radius`): on the chi-square event
`½ ‖v_j - θ‖²_{G_j} ≤ ψ` with `G_j ⪰ k₀ 2^j I`, the Euclidean error is at most
`ρ_j = √(2 ψ / (k₀ 2^j))`. -/
theorem pilot_radius {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (G : E →ₗ[ℝ] F) {k0 N ψ : ℝ} (hk0 : 0 < k0) (hN : 0 < N)
    (hG : ∀ x, k0 * N * ‖x‖ ^ 2 ≤ ‖G x‖ ^ 2) {x : E} (hx : ‖G x‖ ^ 2 / 2 ≤ ψ) :
    ‖x‖ ≤ Real.sqrt (2 * ψ / (k0 * N)) := by
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ (by positivity)]
  have := hG x
  linarith

end Rounding

/-! ### Probabilistic wrappers

In this section the probability space is abstract.  Gaussian facts enter only through the
displayed hypotheses. -/

section Probability

open MeasureTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sum_stage_weights (α : ℝ) (N : ℕ) :
    ∑ j ∈ range N, α / (((j : ℝ) + 1) * ((j : ℝ) + 2)) = α * (1 - 1 / ((N : ℝ) + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    have h3 : ((N : ℝ) + 1 + 1) = (N : ℝ) + 2 := by ring
    rw [h3]
    field_simp
    ring

/-- **Simultaneous coverage from per-stage tails** (proofs of `thm:v10g-discovery` and
`prop:v10g-safety-fallback`).  If the stage-`j` failure event has probability at most
`e^{-u_j}` with `u_j = log((j+1)(j+2)/α)` (the Gaussian chi-square inequality
`ℙ{½ χ²_d > ψ_d(u)} ≤ e^{-u}` at each fixed stage, taken as hypothesis), then some stage
fails with probability at most `α`: the risks `α/((j+1)(j+2))` sum to `α`.  With
`n = j + 1` this is also the union bound over `n ≥ 1` with risks `β/(n(n+1))`. -/
theorem stage_union_bound (P : Measure Ω) (Bad : ℕ → Set Ω) {α : ℝ} (hα : 0 < α)
    (h : ∀ j : ℕ, P (Bad j) ≤
      ENNReal.ofReal (Real.exp (-Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2) / α)))) :
    P (⋃ j, Bad j) ≤ ENNReal.ofReal α := by
  have hw : ∀ j : ℕ, Real.exp (-Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2) / α)) =
      α / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    intro j
    have hpos : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) / α := by positivity
    rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  refine (measure_iUnion_le Bad).trans ?_
  refine ENNReal.tsum_le_of_sum_range_le (fun N => ?_)
  calc ∑ j ∈ range N, P (Bad j)
      ≤ ∑ j ∈ range N, ENNReal.ofReal (α / (((j : ℝ) + 1) * ((j : ℝ) + 2))) :=
        sum_le_sum (fun j _ => by rw [← hw j]; exact h j)
    _ = ENNReal.ofReal (∑ j ∈ range N, α / (((j : ℝ) + 1) * ((j : ℝ) + 2))) :=
        (ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)).symm
    _ ≤ ENNReal.ofReal α := by
        apply ENNReal.ofReal_le_ofReal
        rw [sum_stage_weights]
        have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
        nlinarith

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Safety of a likelihood-certified branch** (`prop:v10g-safety-fallback`, first two
sentences; also the safety half of `thm:bay-main-optimal`).  Let `G n ω` be the (positive
definite) Gram map, `θhat n ω` the estimate and `H n ω` the threshold at count `n`, and
suppose the confidence ellipsoids cover the true parameter simultaneously except with
probability `β` (hypothesis `hcover`: for the fresh fixed design this is the chi-square
union bound `stage_union_bound`; for the tracker it is `lem:bay-cs`).  If the procedure
only stops, at a path-dependent count `τ ω` with a path-dependent action `ahat ω`, when
the threshold is positive and the statistic of that action is at least the threshold,
then the returned action is not `ε`-acceptable with probability at most `β`.  No
property of the allocation, of the pilot, or of the stopping rule is used. -/
theorem certified_branch_safe {𝒜 : Type*} (P : Measure Ω) (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (θ : E)
    (G : ℕ → Ω → E →ₗ[ℝ] F) (hG : ∀ n ω, Function.Injective (G n ω))
    (θhat : ℕ → Ω → E) (H : ℕ → Ω → ℝ) (Stop : Set Ω) (τ : Ω → ℕ) (ahat : Ω → 𝒜)
    {β : ℝ≥0∞}
    (hcover : P {ω | ∃ n, H n ω < ‖G n ω (θ - θhat n ω)‖ ^ 2 / 2} ≤ β)
    (hstop : ∀ ω ∈ Stop, 0 < H (τ ω) ω ∧
      ∀ lam ∈ strictAlt φ (supp (ahat ω)) (hne _) ε,
        H (τ ω) ω ≤ ‖G (τ ω) ω (lam - θhat (τ ω) ω)‖ ^ 2 / 2) :
    P {ω | ω ∈ Stop ∧ ε < regret (supp (ahat ω)) (hne _) (env φ θ)} ≤ β := by
  refine (measure_mono ?_).trans hcover
  rintro ω ⟨hω, hbad⟩
  by_contra hcov
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hcov
  obtain ⟨hH, hst⟩ := hstop ω hω
  have := certified_of_threshold (hne (ahat ω)) (G (τ ω) ω) (hG _ _) hH hst (hcov (τ ω))
  linarith

/-- The two branch errors add: `δ/2 + δ/2 = δ` (`thm:v10g-expectation`, safety). -/
theorem two_branch_safe (P : Measure Ω) {A B : Set Ω} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : P A ≤ ENNReal.ofReal (δ / 2)) (hB : P B ≤ ENNReal.ofReal (δ / 2)) :
    P (A ∪ B) ≤ ENNReal.ofReal δ := by
  refine (measure_union_le A B).trans ((add_le_add hA hB).trans ?_)
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  linarith

/-- Chernoff step of `prop:v10g-safety-fallback`: if `𝔼 e^{Q/2} ≤ 2^{d/2}` (true for
`Q ∼ ½ χ²_d`; hypothesis) then `ℙ(Q > x) ≤ 2^{d/2} e^{-x/2}`. -/
theorem chernoff_half (P : Measure Ω) {Q : Ω → ℝ} (hQ : Measurable Q) {d : ℝ}
    (hmgf : ∫⁻ ω, ENNReal.ofReal (Real.exp (Q ω / 2)) ∂P ≤ ENNReal.ofReal ((2 : ℝ) ^ (d / 2)))
    (x : ℝ) :
    P {ω | x < Q ω} ≤ ENNReal.ofReal ((2 : ℝ) ^ (d / 2) * Real.exp (-x / 2)) := by
  have hmeas : Measurable (fun ω => ENNReal.ofReal (Real.exp (Q ω / 2))) := by fun_prop
  have h1 := mul_meas_ge_le_lintegral (μ := P) hmeas (ENNReal.ofReal (Real.exp (x / 2)))
  have hsub : {ω | x < Q ω} ⊆
      {ω | ENNReal.ofReal (Real.exp (x / 2)) ≤ ENNReal.ofReal (Real.exp (Q ω / 2))} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  have hpos : 0 < Real.exp (x / 2) := Real.exp_pos _
  have h2 : (2 : ℝ) ^ (d / 2) * Real.exp (-x / 2) = (2 : ℝ) ^ (d / 2) / Real.exp (x / 2) := by
    have h3 : Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h3]; exact (div_eq_mul_inv _ _).symm
  rw [h2, ENNReal.ofReal_div_of_pos hpos]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos)) (Or.inl ENNReal.ofReal_ne_top)]
  calc P {ω | x < Q ω} * ENNReal.ofReal (Real.exp (x / 2))
      ≤ P {ω | ENNReal.ofReal (Real.exp (x / 2)) ≤ ENNReal.ofReal (Real.exp (Q ω / 2))} *
          ENNReal.ofReal (Real.exp (x / 2)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (x / 2)) *
          P {ω | ENNReal.ofReal (Real.exp (x / 2)) ≤ ENNReal.ofReal (Real.exp (Q ω / 2))} :=
        mul_comm _ _
    _ ≤ _ := h1.trans hmgf

/-- Tail-sum formula for a count: `𝔼 τ = ∑_n ℙ(τ > n)`. -/
theorem lintegral_nat_eq_tsum (P : Measure Ω) {τ : Ω → ℕ} (hτ : Measurable τ) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P = ∑' n : ℕ, P {ω | n < τ ω} := by
  have hpt : ∀ ω, (τ ω : ℝ≥0∞) = ∑' n : ℕ, ({ω | n < τ ω} : Set Ω).indicator (fun _ => 1) ω := by
    intro ω
    rw [tsum_eq_sum (s := range (τ ω))]
    · rw [sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
      · simp
      · intro n hn
        have : n < τ ω := mem_range.mp hn
        simp [this]
    · intro n hn
      have : ¬ n < τ ω := fun h => hn (mem_range.mpr h)
      simp [this]
  have hms : ∀ n : ℕ, MeasurableSet {ω | n < τ ω} := fun n =>
    measurableSet_lt measurable_const hτ
  simp_rw [hpt]
  rw [lintegral_tsum (fun n => (measurable_const.indicator (hms n)).aemeasurable)]
  refine tsum_congr (fun n => ?_)
  rw [lintegral_indicator (hms n)]
  simp

/-- **Expected count from an exponential tail** (proof of `prop:v10g-safety-fallback`,
last display): if `ℙ(τ > n) ≤ e^{-c n}` for all `n ≥ n₀` then
`𝔼 τ ≤ n₀ + (1 - e^{-c})⁻¹ ≤ n₀ + 1 + 1/c`. -/
theorem expected_count_le_of_exp_tail (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → ℕ}
    (hτ : Measurable τ) {c : ℝ} (hc : 0 < c) (n0 : ℕ)
    (htail : ∀ n : ℕ, n0 ≤ n → P {ω | n < τ ω} ≤ ENNReal.ofReal (Real.exp (-(c * n)))) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P ≤ n0 + ENNReal.ofReal (1 + 1 / c) := by
  have hle : ∀ ω, (τ ω : ℝ≥0∞) ≤ n0 + ((τ ω - n0 : ℕ) : ℝ≥0∞) := by
    intro ω
    have : τ ω ≤ n0 + (τ ω - n0) := by omega
    exact_mod_cast this
  have hτ' : Measurable (fun ω => τ ω - n0) := hτ.sub measurable_const
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  calc ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P ≤ ∫⁻ ω, ((n0 : ℝ≥0∞) + ((τ ω - n0 : ℕ) : ℝ≥0∞)) ∂P :=
        lintegral_mono hle
    _ = n0 + ∫⁻ ω, ((τ ω - n0 : ℕ) : ℝ≥0∞) ∂P := by
        rw [lintegral_add_left measurable_const]; simp
    _ = n0 + ∑' n : ℕ, P {ω | n < τ ω - n0} := by rw [lintegral_nat_eq_tsum P hτ']
    _ ≤ n0 + ∑' n : ℕ, ENNReal.ofReal (Real.exp (-c) ^ n) := by
        gcongr with n
        have hset : {ω | n < τ ω - n0} = {ω | n0 + n < τ ω} := by
          ext ω; simp only [Set.mem_ofPred_eq]; omega
        rw [hset]
        refine (htail (n0 + n) (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ c * n0 := by positivity
        push_cast
        nlinarith
    _ = n0 + ENNReal.ofReal ((1 - Real.exp (-c))⁻¹) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hr0 n)
          (summable_geometric_of_lt_one hr0 hr1), tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ n0 + ENNReal.ofReal (1 + 1 / c) := by
        gcongr
        exact geom_tail_le hc

/-- **Finite mean of the reference safeguard** (`prop:v10g-safety-fallback`,
`𝔼_θ F_δ ≤ H_δ`).  `N` is the nominal count at which the safeguard stops and `Fδ ≤ q + N`
its observation count (the rounded counts total at most `n + q`).  Hypothesis `htail`:
for every integer `n ≥ x_F`, `ℙ(N > n) ≤ 2^{d/2} e^{-n C₀ / 8}`.  This is what the
paper derives from `fallback_budget_sufficient`, `reference_info_lower`,
`fallback_stops` (not stopped by `n` forces `Q_n > n C₀ / 4`) and `chernoff_half` with
`Q_n ∼ ½ χ²_d`; the Gaussian law of `Q_n` is the unformalized input. -/
theorem safeguard_mean_bound (P : Measure Ω) [IsProbabilityMeasure P] {N Fδ : Ω → ℕ}
    (hN : Measurable N) {q : ℕ} (hF : ∀ ω, Fδ ω ≤ q + N ω) {d δ C0 : ℝ} (hd : 0 ≤ d)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hC0 : 0 < C0)
    (htail : ∀ n : ℕ, logBudget (aF d δ C0) (bF C0) ≤ n →
      P {ω | n < N ω} ≤ ENNReal.ofReal ((2 : ℝ) ^ (d / 2) * Real.exp (-(n * C0) / 8))) :
    ∫⁻ ω, (Fδ ω : ℝ≥0∞) ∂P ≤ ENNReal.ofReal (Hdelta q d δ C0) := by
  set xF := logBudget (aF d δ C0) (bF C0) with hxF
  have haF := aF_nonneg hd hδ0 hδ1 hC0
  have hxF0 : 0 ≤ xF := by
    have hb1 : (1 : ℝ) ≤ bF C0 := le_max_left _ _
    obtain ⟨-, hxb, -⟩ := log_budget_inversion haF hb1
    linarith
  have hmean := expected_count_le_of_exp_tail P hN (c := C0 / 16) (by positivity) ⌈xF⌉₊
    (fun n hn => by
      have hxn : xF ≤ n := (Nat.le_ceil xF).trans (by exact_mod_cast hn)
      refine (htail n hxn).trans (ENNReal.ofReal_le_ofReal ?_)
      have h8 := (fallback_budget_sufficient hd hδ0 hδ1 hC0 hxn).2
      have := mgf_tail_simplify (d := d) (x := n * C0) h8
      have e : -(n * C0) / 16 = -(C0 / 16 * n) := by ring
      rw [e] at this
      exact this)
  calc ∫⁻ ω, (Fδ ω : ℝ≥0∞) ∂P ≤ ∫⁻ ω, ((q : ℝ≥0∞) + (N ω : ℝ≥0∞)) ∂P :=
        lintegral_mono (fun ω => by exact_mod_cast hF ω)
    _ = q + ∫⁻ ω, (N ω : ℝ≥0∞) ∂P := by
        rw [lintegral_add_left measurable_const]; simp
    _ ≤ q + (⌈xF⌉₊ + ENNReal.ofReal (1 + 1 / (C0 / 16))) := by gcongr
    _ = ENNReal.ofReal (q + (⌈xF⌉₊ + (1 + 1 / (C0 / 16)))) := by
        conv_rhs =>
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Hdelta q d δ C0) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (⌈xF⌉₊ : ℝ) ≤ xF + 1 := (Nat.ceil_lt_add_one hxF0).le
        have h2 : 1 / (C0 / 16) = 16 / C0 := by field_simp
        unfold Hdelta
        rw [h2, ← hxF]
        linarith

/-- **The expectation wrapper** (proof of `thm:v10g-expectation`).  `τ` is the global
stopping time, `g = F_δ / k + 1` the pathwise safeguard bound, `𝒢` the main good event.
If `τ ≤ c` on `𝒢`, `τ ≤ g` everywhere, and `𝒢ᶜ` is independent of `g` in the form
`𝔼[g ; 𝒢ᶜ] = ℙ(𝒢ᶜ) 𝔼 g` (see `setLIntegral_of_indep` for a sufficient condition), then
`𝔼 τ ≤ c + ℙ(𝒢ᶜ) 𝔼 g` and `𝔼 τ ≤ 𝔼 g`. -/
theorem expectation_wrapper (P : Measure Ω) [IsProbabilityMeasure P] {τ g : Ω → ℝ≥0∞}
    {𝒢 : Set Ω} (h𝒢 : MeasurableSet 𝒢) {c : ℝ≥0∞}
    (hmain : ∀ ω ∈ 𝒢, τ ω ≤ c) (hsafe : ∀ ω, τ ω ≤ g ω)
    (hind : ∫⁻ ω in 𝒢ᶜ, g ω ∂P = P 𝒢ᶜ * ∫⁻ ω, g ω ∂P) :
    ∫⁻ ω, τ ω ∂P ≤ c + P 𝒢ᶜ * ∫⁻ ω, g ω ∂P ∧ ∫⁻ ω, τ ω ∂P ≤ ∫⁻ ω, g ω ∂P := by
  refine ⟨?_, lintegral_mono hsafe⟩
  have hpt : ∀ ω, τ ω ≤ 𝒢.indicator (fun _ => c) ω + 𝒢ᶜ.indicator g ω := by
    intro ω
    by_cases hω : ω ∈ 𝒢
    · simp [hω, hmain ω hω]
    · simp [hω, hsafe ω]
  calc ∫⁻ ω, τ ω ∂P ≤ ∫⁻ ω, (𝒢.indicator (fun _ => c) ω + 𝒢ᶜ.indicator g ω) ∂P :=
        lintegral_mono hpt
    _ = ∫⁻ ω, 𝒢.indicator (fun _ => c) ω ∂P + ∫⁻ ω, 𝒢ᶜ.indicator g ω ∂P :=
        lintegral_add_left (measurable_const.indicator h𝒢) _
    _ = c * P 𝒢 + P 𝒢ᶜ * ∫⁻ ω, g ω ∂P := by
        rw [lintegral_indicator_const h𝒢, lintegral_indicator h𝒢.compl, hind]
    _ ≤ c + P 𝒢ᶜ * ∫⁻ ω, g ω ∂P := by
        gcongr
        calc c * P 𝒢 ≤ c * 1 := by gcongr; exact prob_le_one
          _ = c := mul_one c

/-- Independence in the form used by `expectation_wrapper`: if `g` is measurable for a
σ-algebra `Mf` (the safeguard tape) independent of the event `T`, then
`𝔼[g ; T] = ℙ(T) 𝔼 g`. -/
theorem setLIntegral_of_indep {Ω' : Type*} {Mf mΩ : MeasurableSpace Ω'} (P : Measure Ω')
    (hMf : Mf ≤ mΩ) {T : Set Ω'} (hT : MeasurableSet T) {g : Ω' → ℝ≥0∞}
    (hind : ProbabilityTheory.IndepSets {s | MeasurableSet[Mf] s} {T} P)
    (hg : Measurable[Mf] g) :
    ∫⁻ ω in T, g ω ∂P = P T * ∫⁻ ω, g ω ∂P := by
  have h := ProbabilityTheory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
    hMf 1 hT hind hg
  rw [lintegral_indicator_const hT, one_mul] at h
  rw [mul_comm, ← h, ← lintegral_indicator hT]
  refine lintegral_congr (fun ω => ?_)
  by_cases hω : ω ∈ T <;> simp [hω]

/-- **Correlated finite-confidence discovery and confirmation, expectation bound**
(`eq:v10g-finite`): `𝔼_θ τ ≤ min {𝓑_δ, H_δ / k + 1}`.

Hypotheses and what supplies them in the paper:
* `hmain`: on the good event `𝒢` the global time is at most
  `(D̄ + x_C + q + 1)/(1 - k) + 1` (`exists_pilot_stage`, `pilot_budget_sufficient`,
  `pilot_gate_succeeds`, `frozen_plan_rate`, `confirm_stat_lower`, `confirm_crossing`,
  `confirm_stops`, `calendar_main`);
* `hsafe`: on every path the procedure stops no later than the safeguard, whose global
  count is at most `F_δ / k + 1` (`calendar_safeguard`);
* `hprob`: `ℙ(𝒢ᶜ) ≤ 2α` (`stage_union_bound` twice, given the chi-square tail);
* `hind`: `𝒢ᶜ` is independent of the safeguard tape;
* `hF`: `𝔼 F_δ / k + 1 ≤ H_δ / k + 1` (`safeguard_mean_bound`). -/
theorem finite_confidence_expectation (P : Measure Ω) [IsProbabilityMeasure P]
    {τ g : Ω → ℝ≥0∞} {𝒢 : Set Ω} (h𝒢 : MeasurableSet 𝒢) {Db xC q k α H : ℝ}
    (hk0 : 0 < k) (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hc : 0 ≤ (Db + xC + q + 1) / (1 - k) + 1)
    (hmain : ∀ ω ∈ 𝒢, τ ω ≤ ENNReal.ofReal ((Db + xC + q + 1) / (1 - k) + 1))
    (hsafe : ∀ ω, τ ω ≤ g ω)
    (hprob : P 𝒢ᶜ ≤ ENNReal.ofReal (2 * α))
    (hind : ∫⁻ ω in 𝒢ᶜ, g ω ∂P = P 𝒢ᶜ * ∫⁻ ω, g ω ∂P)
    (hF : ∫⁻ ω, g ω ∂P ≤ ENNReal.ofReal (H / k + 1)) :
    ∫⁻ ω, τ ω ∂P ≤ ENNReal.ofReal (min (Bdelta Db xC q k α H) (H / k + 1)) := by
  obtain ⟨h1, h2⟩ := expectation_wrapper P h𝒢 hmain hsafe hind
  have hHk : 0 ≤ H / k + 1 := by positivity
  have hB : ∫⁻ ω, τ ω ∂P ≤ ENNReal.ofReal (Bdelta Db xC q k α H) := by
    refine h1.trans ?_
    unfold Bdelta
    rw [ENNReal.ofReal_add hc (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
  rcases le_total (Bdelta Db xC q k α H) (H / k + 1) with h | h
  · rw [min_eq_left h]; exact hB
  · rw [min_eq_right h]; exact h2.trans hF

end Probability

/-! ### `thm:bay-main-optimal`: deterministic and analytic cores

The theorem itself (a sharp limit for the expected stopping time of an adaptive
procedure) is not stated here as one formal statement: that needs a formal model of
sequential Gaussian experiments, stopped likelihood ratios and the tracker.  What follows
are the deterministic and analytic steps of its proof, each with the facts it takes from
the probabilistic model as hypotheses. -/

section OracleBounds

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Explicit oracle bound `I_a ≤ C_R = ℓ² (R + A)² / 2` on the parameter ball of radius
`R`, in root form: `√(2 I_a(θ, w)) ≤ ℓ (R + A)` when `Q` has an anchor of norm at most `A`. -/
theorem rootInfo_le_anchor (u : X → E) {w : X → ℝ} (hw : w ∈ simplex X) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hu : ∀ x, ‖u x‖ ≤ ℓ) {Q : Set E} {lam0 : E} (h0 : lam0 ∈ Q) {R A0 : ℝ}
    (hA : ‖lam0‖ ≤ A0) {θ : E} (hθ : ‖θ‖ ≤ R) :
    rootInfo (designMap u w) Q θ ≤ ℓ * (R + A0) := by
  refine (rootInfo_le h0).trans ((norm_designMap_le u hw hu _).trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ hℓ
  have := norm_sub_le lam0 θ
  linarith

/-- `I_a ≤ C_R`. -/
theorem info_le_anchor (u : X → E) {w : X → ℝ} (hw : w ∈ simplex X) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hu : ∀ x, ‖u x‖ ≤ ℓ) {Q : Set E} {lam0 : E} (h0 : lam0 ∈ Q) {R A0 : ℝ}
    (hA : ‖lam0‖ ≤ A0) {θ : E} (hθ : ‖θ‖ ≤ R) :
    rootInfo (designMap u w) Q θ ^ 2 / 2 ≤ ℓ ^ 2 * (R + A0) ^ 2 / 2 := by
  have h := pow_le_pow_left₀ rootInfo_nonneg (rootInfo_le_anchor u hw hℓ hu h0 hA hθ) 2
  rw [mul_pow] at h
  linarith

/-- Local Lipschitz bound `|I_a(θ, w) - I_a(θ', w)| ≤ L_R ‖θ - θ'‖₂`, `L_R = ℓ² (R + A)`,
on the parameter ball of radius `R`. -/
theorem info_lipschitz_ball (u : X → E) {w : X → ℝ} (hw : w ∈ simplex X) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hu : ∀ x, ‖u x‖ ≤ ℓ) {Q : Set E} {lam0 : E} (h0 : lam0 ∈ Q) {R A0 : ℝ}
    (hA : ‖lam0‖ ≤ A0) {θ θ' : E} (hθ : ‖θ‖ ≤ R) (hθ' : ‖θ'‖ ≤ R) :
    |rootInfo (designMap u w) Q θ ^ 2 / 2 - rootInfo (designMap u w) Q θ' ^ 2 / 2| ≤
      ℓ ^ 2 * (R + A0) * ‖θ - θ'‖ := by
  set r := rootInfo (designMap u w) Q θ with hr
  set r' := rootInfo (designMap u w) Q θ' with hr'
  have h1 : r ≤ ℓ * (R + A0) := rootInfo_le_anchor u hw hℓ hu h0 hA hθ
  have h2 : r' ≤ ℓ * (R + A0) := rootInfo_le_anchor u hw hℓ hu h0 hA hθ'
  have h3 : |r - r'| ≤ ℓ * ‖θ - θ'‖ := rootInfo_design_lipschitz u hw hu Q θ θ'
  have hr0 : 0 ≤ r := rootInfo_nonneg
  have hr0' : 0 ≤ r' := rootInfo_nonneg
  have h4 : r ^ 2 / 2 - r' ^ 2 / 2 = (r - r') * ((r + r') / 2) := by ring
  rw [h4, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (r + r') / 2)]
  have h5 : (r + r') / 2 ≤ ℓ * (R + A0) := by linarith
  calc |r - r'| * ((r + r') / 2) ≤ ℓ * ‖θ - θ'‖ * (ℓ * (R + A0)) :=
        mul_le_mul h3 h5 (by positivity) (by positivity)
    _ = ℓ ^ 2 * (R + A0) * ‖θ - θ'‖ := by ring

/-- The exploration floor `W_η = (1 - η) Δ + η w⁰` loses at most `η C_R` of the rate, by
concavity: `I(θ, (1 - η) w + η w⁰) ≥ I(θ, w) - η C` whenever `I(θ, w) ≤ C`. -/
theorem floor_rate_loss (u : X → E) {w w0 : X → ℝ} (hw : ∀ x, 0 ≤ w x) (hw0 : ∀ x, 0 ≤ w0 x)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {Q : Set E} (hQ : Q.Nonempty) (θ : E) {C : ℝ}
    (hC : rootInfo (designMap u w) Q θ ^ 2 / 2 ≤ C) :
    rootInfo (designMap u w) Q θ ^ 2 / 2 - η * C ≤
      rootInfo (designMap u (fun x => (1 - η) * w x + η * w0 x)) Q θ ^ 2 / 2 := by
  have hfun : (fun x => (1 - η) * w x + η * w0 x) =
      fun x => (1 - η) * w x + (1 - (1 - η)) * w0 x := by
    funext x; ring
  have h := info_concave_design u hw hw0 (t := 1 - η) (by linarith) (by linarith) hQ θ
  rw [← hfun] at h
  have h0 : 0 ≤ rootInfo (designMap u w0) Q θ ^ 2 / 2 := by positivity
  nlinarith [mul_nonneg hη0 h0, mul_le_mul_of_nonneg_left hC hη0]

end OracleBounds

section Tracking

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Number of queries of experiment `x` among the first `t` rounds. -/
def pulls (sel : ℕ → X) (x : X) (t : ℕ) : ℕ := ((range t).filter (fun s => sel s = x)).card

/-- Cumulative target `W_x(t) = ∑_{s < t} v_s(x)`. -/
def cumTarget (v : ℕ → X → ℝ) (x : X) (t : ℕ) : ℝ := ∑ s ∈ range t, v s x

lemma pulls_succ (sel : ℕ → X) (x : X) (t : ℕ) :
    pulls sel x (t + 1) = pulls sel x t + (if sel t = x then 1 else 0) := by
  unfold pulls
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · simp

lemma sum_pulls (sel : ℕ → X) (t : ℕ) : ∑ x, (pulls sel x t : ℝ) = t := by
  have h := card_eq_sum_card_fiberwise (f := sel) (s := range t) (t := univ)
    (fun _ _ => mem_univ _)
  rw [card_range] at h
  unfold pulls
  exact_mod_cast h.symm

/-- **Tracking discrepancy** (proof of `thm:bay-main-optimal`, "Tracking, estimation, and
stabilization").  If at every round the queried experiment maximizes the deficit
`W_x(t) - N_x(t-1)` of the cumulative target designs, then
`-(m - 1) ≤ N_x(t) - W_x(t) ≤ 1` for all `t` and `x`, `m = |X|`. -/
theorem tracking_discrepancy [Nonempty X] (v : ℕ → X → ℝ) (hv : ∀ s, v s ∈ simplex X)
    (sel : ℕ → X)
    (hsel : ∀ t x, cumTarget v x (t + 1) - pulls sel x t ≤
      cumTarget v (sel t) (t + 1) - pulls sel (sel t) t) :
    ∀ t x, -((Fintype.card X : ℝ) - 1) ≤ (pulls sel x t : ℝ) - cumTarget v x t ∧
      (pulls sel x t : ℝ) - cumTarget v x t ≤ 1 := by
  have hsumN := sum_pulls sel
  have hsumW : ∀ t : ℕ, ∑ x, cumTarget v x t = t := by
    intro t
    unfold cumTarget
    rw [sum_comm]
    simp [(hv _).2]
  have hW : ∀ x t, cumTarget v x (t + 1) = cumTarget v x t + v t x :=
    fun x t => sum_range_succ _ _
  have hupper : ∀ t x, (pulls sel x t : ℝ) - cumTarget v x t ≤ 1 := by
    intro t
    induction t with
    | zero => intro x; simp [pulls, cumTarget]
    | succ t ih =>
      intro x
      have hdef : 0 ≤ cumTarget v (sel t) (t + 1) - pulls sel (sel t) t := by
        by_contra hneg
        push Not at hneg
        have hlt : ∑ y, (cumTarget v y (t + 1) - (pulls sel y t : ℝ)) < ∑ _y : X, (0 : ℝ) :=
          sum_lt_sum_of_nonempty univ_nonempty (fun y _ => lt_of_le_of_lt (hsel t y) hneg)
        rw [sum_sub_distrib, hsumW, hsumN, sum_const_zero] at hlt
        push_cast at hlt
        linarith
      rw [pulls_succ, hW]
      by_cases h : sel t = x
      · rw [h] at hdef
        rw [hW] at hdef
        simp only [h, ↓reduceIte]
        push_cast
        linarith
      · simp only [h, ↓reduceIte]
        push_cast
        have h1 := ih x
        have h2 := (hv t).1 x
        linarith
  intro t x
  refine ⟨?_, hupper t x⟩
  have h0 : ∑ y, ((pulls sel y t : ℝ) - cumTarget v y t) = 0 := by
    rw [sum_sub_distrib, hsumN, hsumW]; ring
  rw [← add_sum_erase univ _ (mem_univ x)] at h0
  have h1 : ∑ y ∈ univ.erase x, ((pulls sel y t : ℝ) - cumTarget v y t) ≤
      ∑ _y ∈ univ.erase x, (1 : ℝ) := sum_le_sum (fun y _ => hupper t y)
  rw [sum_const, card_erase_of_mem (mem_univ x), card_univ, nsmul_eq_mul, mul_one] at h1
  have hcard : 1 ≤ Fintype.card X := Fintype.card_pos
  rw [Nat.cast_sub hcard] at h1
  push_cast at h1
  linarith

end Tracking

section Selector

/-- **Answer selection stabilizes** (proof of `thm:bay-main-optimal`).  With score errors
at most `err` and slack `ζ ≥ 2 err`, every true maximizer passes the eligibility test
`ŝ(a) ≥ max_b ŝ(b) - ζ`; and an action whose true score is more than `ζ + 2 err` below a
competitor fails it. -/
theorem selector_stable {𝒜 : Type*} (s shat : 𝒜 → ℝ) {err ζ : ℝ}
    (herr : ∀ a, |shat a - s a| ≤ err) (hζ : 2 * err ≤ ζ) :
    (∀ a, (∀ b, s b ≤ s a) → ∀ b, shat b - ζ ≤ shat a) ∧
      (∀ a b, s a + ζ + 2 * err < s b → shat a < shat b - ζ) := by
  constructor
  · intro a ha b
    have h1 := abs_le.mp (herr a)
    have h2 := abs_le.mp (herr b)
    have := ha b
    linarith
  · intro a b hab
    have h1 := abs_le.mp (herr a)
    have h2 := abs_le.mp (herr b)
    linarith

end Selector

section Asymptotics

open MeasureTheory ENNReal

/-- **Linear information beats a logarithmic threshold** ("Expected upper bound").  For
rate slack `0 < s < I/2` and threshold `log(1/δ) + c₁ log(1 + t) + c₂`, all sufficiently
small `δ` satisfy: every `t ≥ log(1/δ) / (I - 2s)` has
`(I - s) t ≥ log(1/δ) + c₁ log(1 + t) + c₂`.  Hence a procedure with `J_t ≥ (I - s) t`
and `H_t ≤ log(1/δ) + c₁ log(1 + t) + c₂` for `t ≥ T_s` has stopped by
`max {T_s, ⌈log(1/δ) / (I - 2s)⌉}`. -/
theorem linear_beats_log {I s c1 c2 : ℝ} (hs : 0 < s) (hI : 2 * s < I) (hc2 : 0 ≤ c2) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ, 0 < δ → δ < δ0 → ∀ t : ℝ, Real.log (1 / δ) / (I - 2 * s) ≤ t →
      Real.log (1 / δ) + c1 * Real.log (1 + t) + c2 ≤ (I - s) * t := by
  have hIs : 0 < I - 2 * s := by linarith
  set a := c2 / s with ha
  set b := max 1 (c1 / s) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb1 : 1 ≤ b := le_max_left _ _
  obtain ⟨-, hxb, hpers⟩ := log_budget_inversion ha0 hb1
  set x := logBudget a b with hx
  refine ⟨Real.exp (-((I - 2 * s) * x)), Real.exp_pos _, fun δ hδ hlt t ht => ?_⟩
  have h1 := Real.log_lt_log hδ hlt
  rw [Real.log_exp] at h1
  have hL : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  have h2 : x < Real.log (1 / δ) / (I - 2 * s) := by
    rw [lt_div_iff₀ hIs, hL]; linarith
  have hxt : x ≤ t := by linarith
  have h3 := hpers t hxt
  have h4 : Real.log (1 / δ) ≤ (I - 2 * s) * t := by
    rw [div_le_iff₀ hIs] at ht; linarith
  have ht0 : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have h5 : c1 / s ≤ b := le_max_right _ _
  rw [div_le_iff₀ hs] at h5
  have h6 : a * s = c2 := by rw [ha]; field_simp
  have h7 := mul_le_mul_of_nonneg_left h3 hs.le
  have h8 := mul_le_mul_of_nonneg_right h5 ht0
  have h9 : Real.log (1 + t) = Real.log (t + 1) := by rw [add_comm]
  rw [h9]
  nlinarith

/-- **Upper constant** ("dividing the expectation by `log(1/δ)` and then sending
`s ↓ 0`").  If for every small slack `s` the expected stopping time `f δ` is eventually at
most `K_s + log(1/δ) / (I - 2s)`, then `limsup_{δ ↓ 0} f(δ) / log(1/δ) ≤ 1/I`, stated as:
for every `η > 0` the ratio is eventually at most `1/I + η`. -/
theorem upper_rate_of_bounds {f : ℝ → ℝ} {I : ℝ} (hI : 0 < I)
    (h : ∀ s, 0 < s → 2 * s < I → ∃ K δ0 : ℝ, 0 < δ0 ∧ ∀ δ, 0 < δ → δ < δ0 →
      f δ ≤ K + Real.log (1 / δ) / (I - 2 * s)) :
    ∀ η > 0, ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 → f δ / Real.log (1 / δ) ≤ 1 / I + η := by
  intro η hη
  set s := min (I / 4) (η * I ^ 2 / 8) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  have hs1 : s ≤ I / 4 := min_le_left _ _
  have hs2 : s ≤ η * I ^ 2 / 8 := min_le_right _ _
  obtain ⟨K, δ1, hδ1, hK⟩ := h s hs0 (by linarith)
  have hIs : 0 < I - 2 * s := by linarith
  have hrate : 1 / (I - 2 * s) ≤ 1 / I + η / 2 := by
    rw [div_le_iff₀ hIs]
    have h1 : (1 / I + η / 2) * (I - 2 * s) = 1 + (η / 2 * (I - 2 * s) - 2 * s / I) := by
      field_simp; ring
    rw [h1]
    have h2 : 2 * s / I ≤ η * I / 4 := by rw [div_le_iff₀ hI]; nlinarith
    nlinarith
  refine ⟨min δ1 (Real.exp (-(2 * |K| / η + 1))), lt_min hδ1 (Real.exp_pos _),
    fun δ hδ hlt => ?_⟩
  have hL : 2 * |K| / η + 1 < Real.log (1 / δ) := by
    have h1 : δ < Real.exp (-(2 * |K| / η + 1)) := lt_of_lt_of_le hlt (min_le_right _ _)
    have h2 := Real.log_lt_log hδ h1
    rw [Real.log_exp] at h2
    rw [one_div, Real.log_inv]; linarith
  have hK0 : 0 ≤ 2 * |K| / η := by positivity
  have hLpos : 0 < Real.log (1 / δ) := by linarith
  have hf := hK δ hδ (lt_of_lt_of_le hlt (min_le_left _ _))
  rw [div_le_iff₀ hLpos]
  have hKL : K ≤ η / 2 * Real.log (1 / δ) := by
    have h1 : η / 2 * (2 * |K| / η + 1) = |K| + η / 2 := by field_simp
    have h3 := mul_lt_mul_of_pos_left hL (by positivity : 0 < η / 2)
    linarith [le_abs_self K]
  have h4 : Real.log (1 / δ) / (I - 2 * s) ≤ (1 / I + η / 2) * Real.log (1 / δ) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hrate hLpos.le
  have h5 : (1 / I + η) * Real.log (1 / δ) =
      η / 2 * Real.log (1 / δ) + (1 / I + η / 2) * Real.log (1 / δ) := by ring
  linarith

/-- **Lower constant** ("letting `α ↓ 0` matches the upper bound").  If for every
`a, γ ∈ (0, 1)` the expected stopping time is eventually at least
`(1 - γ) (1 - a) log(1/δ) / I` (from `ℙ_θ(τ_δ ≤ T_δ) → 0` at
`T_δ = ⌊(1 - a) log(1/δ) / I⌋` and `mean_ge_of_late_stop`), then
`liminf_{δ ↓ 0} f(δ) / log(1/δ) ≥ 1/I`: for every `η > 0` the ratio is eventually at least
`1/I - η`. -/
theorem lower_rate_of_bounds {f : ℝ → ℝ} {I : ℝ} (hI : 0 < I)
    (h : ∀ a γ : ℝ, 0 < a → a < 1 → 0 < γ → γ < 1 → ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 →
      (1 - γ) * ((1 - a) * Real.log (1 / δ) / I) ≤ f δ) :
    ∀ η > 0, ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 → 1 / I - η ≤ f δ / Real.log (1 / δ) := by
  intro η hη
  set a := min (1 / 2) (η * I / 2) with ha
  have ha0 : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 / 2 := min_le_left _ _
  have ha2 : a ≤ η * I / 2 := min_le_right _ _
  obtain ⟨δ1, hδ1, hb⟩ := h a a ha0 (by linarith) ha0 (by linarith)
  refine ⟨min δ1 1, lt_min hδ1 one_pos, fun δ hδ hlt => ?_⟩
  have hδlt1 : δ < 1 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hLpos : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hf := hb δ hδ (lt_of_lt_of_le hlt (min_le_left _ _))
  rw [le_div_iff₀ hLpos]
  have h1 : (1 / I - η) * Real.log (1 / δ) ≤ (1 - a) * ((1 - a) * Real.log (1 / δ) / I) := by
    have h2 : (1 - a) * ((1 - a) * Real.log (1 / δ) / I) =
        ((1 - a) ^ 2 / I) * Real.log (1 / δ) := by ring
    rw [h2]
    refine mul_le_mul_of_nonneg_right ?_ hLpos.le
    rw [le_div_iff₀ hI]
    have h3 : (1 / I - η) * I = 1 - η * I := by field_simp
    rw [h3]
    nlinarith [sq_nonneg a]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `𝔼 τ ≥ (T + 1) ℙ(τ > T)`. -/
theorem mean_ge_of_late_stop (P : Measure Ω) {τ : Ω → ℕ} (hτ : Measurable τ) (T : ℕ) :
    ((T : ℝ≥0∞) + 1) * P {ω | T < τ ω} ≤ ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P := by
  have hm : Measurable (fun ω => (τ ω : ℝ≥0∞)) := measurable_from_nat.comp hτ
  have h := mul_meas_ge_le_lintegral (μ := P) hm ((T : ℝ≥0∞) + 1)
  have hset : {ω | T < τ ω} = {ω | (T : ℝ≥0∞) + 1 ≤ (τ ω : ℝ≥0∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hlt; exact_mod_cast Nat.succ_le_of_lt hlt
    · intro hle
      have : T + 1 ≤ τ ω := by exact_mod_cast hle
      omega
  rw [hset]
  exact h

/-- **Change of measure on a stopping event** ("Multiple-answer lower bound").  If the
law under `θ` has density `e^{L}` with respect to the law under an alternative `λ` (on the
σ-algebra of the stopped transcript; this likelihood-ratio identity for the adaptive
Gaussian experiment is the hypothesis `hdens`), then an event on which `L ≤ c` satisfies
`ℙ_θ(E) ≤ e^{c} ℙ_λ(E)`. -/
theorem change_of_measure_bound (Pθ Pl : Measure Ω) {L : Ω → ℝ}
    (hdens : Pθ = Pl.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω))))
    {Ev : Set Ω} (hE : MeasurableSet Ev) {c : ℝ} (hc : ∀ ω ∈ Ev, L ω ≤ c) :
    Pθ Ev ≤ ENNReal.ofReal (Real.exp c) * Pl Ev := by
  rw [hdens, withDensity_apply _ hE, ← setLIntegral_const]
  exact setLIntegral_mono' hE
    (fun ω hω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hc ω hω)))

/-- `exp[(1 - a/2) log(1/δ)] · δ = δ^{a/2}`. -/
lemma exp_log_inv_mul {a δ : ℝ} (hδ : 0 < δ) :
    Real.exp ((1 - a / 2) * Real.log (1 / δ)) * δ = δ ^ (a / 2) := by
  rw [Real.rpow_def_of_pos hδ, one_div, Real.log_inv]
  nth_rewrite 2 [← Real.exp_log hδ]
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The lower-bound event has vanishing probability.**  With the change of measure and
uniform correctness under the invalidating alternative (`ℙ_λ(E) ≤ δ`, since on `E` the
procedure returns an action that is wrong under `λ`), an event on which
`L ≤ (1 - a/2) log(1/δ)` has `ℙ_θ(E) ≤ δ^{a/2}`. -/
theorem lower_bound_event (Pθ Pl : Measure Ω) {L : Ω → ℝ}
    (hdens : Pθ = Pl.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω))))
    {Ev : Set Ω} (hE : MeasurableSet Ev) {a δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ ω ∈ Ev, L ω ≤ (1 - a / 2) * Real.log (1 / δ))
    (hcorrect : Pl Ev ≤ ENNReal.ofReal δ) :
    Pθ Ev ≤ ENNReal.ofReal (δ ^ (a / 2)) := by
  refine (change_of_measure_bound Pθ Pl hdens hE hc).trans ?_
  rw [← exp_log_inv_mul hδ, ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr

end Asymptotics

/-!
## Status summary

* `lem:bay-projection`: `strictComp_nonempty_iff`, `closure_strictComp`,
  `closure_strictAlt`, `screened_projection`, `exists_min_closedComp`,
  `exists_min_screened`, `hullScreen_eq_empty_iff`, `screened_projection_dual`,
  `projection_ratio` (with `adjoint_symm_norm_sq`, `closedComp_dist_le_iff`).
* `lem:bay-distance-certificate`: `distance_certificate`,
  `distance_certificate_ellipsoid`, `distance_certificate_rootInfo`.
* `lem:bay-fc-inversion`: `log_budget_inversion`.
* `thm:v10g-discovery`: `stage_union_bound`, `pilot_radius`, `oracle_root_lower`,
  `pilot_gate_succeeds`, `frozen_plan_rate`, `pilot_budget_sufficient`,
  `exists_pilot_stage`, `sum_ceil_counts`, `gram_dominates`.
* `prop:v10g-safety-fallback`: `certified_of_threshold`, `certified_branch_safe`,
  `frozen_recycle`, `reference_info_lower`, `fallback_budget_sufficient`,
  `fallback_stops`, `chernoff_half`, `mgf_tail_simplify`, `expected_count_le_of_exp_tail`,
  `safeguard_mean_bound`.
* `thm:v10g-expectation`: `two_branch_safe`, `confirm_stat_lower`, `confirm_stat_mono`,
  `confirm_crossing`, `confirm_stops`, `calendar_main`, `calendar_safeguard`, `expectation_wrapper`,
  `setLIntegral_of_indep`, `finite_confidence_expectation`.
* `cor:v10g-target`: `discovery_budget_split`, `leading_multiplier_le`, `target_bound`.
* `thm:bay-main-optimal`: `rootInfo_lipschitz`, `rootInfo_design_lipschitz`,
  `info_concave_design`, `rootInfo_mono_design`, `rootInfo_closure`, `info_le_anchor`,
  `info_lipschitz_ball`, `floor_rate_loss`, `tracking_discrepancy`, `selector_stable`,
  `linear_beats_log`, `upper_rate_of_bounds`, `lower_rate_of_bounds`,
  `mean_ge_of_late_stop`, `change_of_measure_bound`, `lower_bound_event`.
-/

end JointRootCert
