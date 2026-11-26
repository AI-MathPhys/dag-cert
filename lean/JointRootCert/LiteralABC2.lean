/-
Literal forms of main-text and Appendix A--C statements, part 2.

* `thm:t3-misspec` (Valid misspecification-aware ellipsoid and safe intersection): the
  time-uniform radius with predictable inclusion indicators `α_s ∈ {0,1}`,
  `V_t = λ I + ∑_s α_s φ_{x_s} φ_{x_s}ᵀ`, the RLS estimator on included queries and
  `T_eff = ∑_s α_s` (`t3_misspec_radius`), the per-terminal cap `N_max(ξ) = ⌈σ²/ξ²⌉`
  (`t3_misspec_radius_capped`), and the safe intersection as one statement
  (`t3_safe_intersection`).
* `lem:bay-cs` (Full-domain confidence sequence): coverage for all `t` with `G_t`
  invertible, with conditionally `N(0,1)` innovations (`bay_cs_literal`,
  `bay_cs_literal_kernel`), invertibility versus `Coercive` (`gram_isUnit_iff_coercive`).
* `thm:t4-finite-sample` (Finite-sample cost of safeguarded CD-Joint): an infinite run of
  Algorithm `alg:cd-joint` with its first certified time (`cd_joint_infinite_run`),
  termination with the radius `eq:ay-radius` (`cd_joint_terminates`), and the end-to-end
  statement (`cd_joint_literal`).
-/
import JointRootCert.Completions

namespace JointRootCert

namespace LiteralABC2

open Finset MeasureTheory Matrix
open scoped ENNReal

/-! ### `thm:t3-misspec`: predictable inclusion indicators -/

section Misspec

variable {n : Type*} [Fintype n] [DecidableEq n] {Ω : Type*}

/-- `V_t = λ I + ∑_{s<t} α_s φ_s φ_sᵀ`, the design matrix of the included queries. -/
noncomputable def inclDesign (lam : ℝ) (α : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    Matrix n n ℝ :=
  lam • (1 : Matrix n n ℝ) + ∑ s ∈ range t, α s ω • vecMulVec (φ s ω) (φ s ω)

/-- The RLS estimator based on included queries, `θ̂_t = V_t⁻¹ ∑_{s<t} α_s y_s φ_s`, for
centred observations `y_s = Y_s - m₀`. -/
noncomputable def inclRLS (lam : ℝ) (α : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (y : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : n → ℝ :=
  (inclDesign lam α φ t ω)⁻¹ *ᵥ ∑ s ∈ range t, (α s ω * y s ω) • φ s ω

/-- `T_eff = ∑_{s<t} α_s`, the number of included queries. -/
noncomputable def effCount (α : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := ∑ s ∈ range t, α s ω

/-- The radius `β_t^{(ξ)} = √λ B_θ + σ √(2 log (1/δ) + log (det V_t / λ^d)) + ξ √T_eff` of
`eq:t3-misspec-radius`. -/
noncomputable def misRadius (σ lam δ B ξ : ℝ) (V : Matrix n n ℝ) (Teff : ℝ) : ℝ :=
  Real.sqrt lam * B +
    σ * Real.sqrt (2 * Real.log (1 / δ) + Real.log (V.det / lam ^ Fintype.card n)) +
    ξ * Real.sqrt Teff

omit [Fintype n] in
lemma inclDesign_eq (lam : ℝ) {α : ℕ → Ω → ℝ} (hα : ∀ s ω, α s ω = 0 ∨ α s ω = 1)
    (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    inclDesign lam α φ t ω = ridgeDesign lam (fun s : Fin t => α s ω • φ s ω) := by
  unfold inclDesign ridgeDesign
  rw [Fin.sum_univ_eq_sum_range (fun s => vecMulVec (α s ω • φ s ω) (α s ω • φ s ω)) t]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rcases hα s ω with h | h <;> simp [h]

omit [DecidableEq n] in
lemma incl_sum_eq {α : ℕ → Ω → ℝ} (hα : ∀ s ω, α s ω = 0 ∨ α s ω = 1) (φ : ℕ → Ω → n → ℝ)
    (θs : n → ℝ) (bias η : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑ s ∈ range t, (α s ω * (φ s ω ⬝ᵥ θs + bias s ω + η s ω)) • φ s ω =
      ∑ s : Fin t, ((α s ω • φ s ω) ⬝ᵥ θs + α s ω * bias s ω + η s ω) • (α s ω • φ s ω) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun s => ((α s ω • φ s ω) ⬝ᵥ θs + α s ω * bias s ω + η s ω) • (α s ω • φ s ω)) t]
  refine sum_congr rfl fun s _ => ?_
  rcases hα s ω with h | h <;> simp [h]

/-- **Deterministic radius with inclusion indicators.**  `ψ_s = α_s φ_s` are the included
features, `αv s ∈ {0,1}`.  If the innovation sum obeys the self-normalized bound `β_sn`,
the ridge error is at most `√λ B + β_sn + ξ √(∑_s α_s)`: the bias term counts included
queries only. -/
theorem incl_radius_det {ι : Type*} [Fintype ι] {lam ξ B βsn : ℝ} (hlam : 0 < lam)
    (hB : 0 ≤ B) (hξ : 0 ≤ ξ) (ψ : ι → n → ℝ) (αv : ι → ℝ) (hα : ∀ s, αv s = 0 ∨ αv s = 1)
    (bias η : ι → ℝ) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) (hbias : ∀ s, |bias s| ≤ ξ)
    (hsn : Real.sqrt (qinv (ridgeDesign lam ψ) (∑ s, η s • ψ s)) ≤ βsn) :
    Real.sqrt
        (((ridgeDesign lam ψ)⁻¹ *ᵥ (∑ s, (ψ s ⬝ᵥ θs + αv s * bias s + η s) • ψ s) - θs) ⬝ᵥ
          ridgeDesign lam ψ *ᵥ
            ((ridgeDesign lam ψ)⁻¹ *ᵥ (∑ s, (ψ s ⬝ᵥ θs + αv s * bias s + η s) • ψ s) - θs)) ≤
      Real.sqrt lam * B + βsn + ξ * Real.sqrt (∑ s, αv s) := by
  have hV : Coercive (ridgeDesign lam ψ) lam := ridgeDesign_coercive lam ψ
  rw [hV.quad_eq_qinv hlam, ridge_error_decomp hlam ψ (fun s => αv s * bias s) η θs]
  have h1 := hV.sqrt_qinv_smul_le hlam hB θs hθ
  have h2 : Real.sqrt (qinv (ridgeDesign lam ψ) (∑ s, (αv s * bias s) • ψ s)) ≤
      ξ * Real.sqrt (∑ s, αv s) := by
    have hle : qinv (ridgeDesign lam ψ) (∑ s, (αv s * bias s) • ψ s) ≤ ξ ^ 2 * ∑ s, αv s := by
      refine (bias_qinv_le hV hlam ψ (fun s => αv s * bias s)
        (ridgeDesign_dom hlam.le ψ)).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun s _ => ?_
      have hb : bias s ^ 2 ≤ ξ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbias s) 2
      rcases hα s with h | h
      · simp [h]
      · simpa [h] using hb
    calc Real.sqrt (qinv (ridgeDesign lam ψ) (∑ s, (αv s * bias s) • ψ s))
        ≤ Real.sqrt (ξ ^ 2 * ∑ s, αv s) := Real.sqrt_le_sqrt hle
      _ = ξ * Real.sqrt (∑ s, αv s) := by
          rw [Real.sqrt_mul (sq_nonneg ξ), Real.sqrt_sq hξ]
  have h3 := hV.sqrt_qinv_sub_le hlam
    (∑ s, η s • ψ s + ∑ s, (αv s * bias s) • ψ s) (lam • θs)
  have h4 := hV.sqrt_qinv_add_le hlam (∑ s, η s • ψ s) (∑ s, (αv s * bias s) • ψ s)
  linarith

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Proposition `thm:t3-misspec`, the radius, for predictable feature and bias
sequences.**  Centred observations `y_s = φ_s · θ* + b_s + η_s` with predictable features
`φ_s`, predictable inclusion indicators `α_s ∈ {0,1}`, `|b_s| ≤ ξ`, `‖θ*‖ ≤ B` and
conditionally `σ`-sub-Gaussian `η_s`.  With probability at least `1 - δ`, for all `t`,
`‖θ̂_t - θ*‖_{V_t} ≤ √λ B + σ √(2 log (1/δ) + log (det V_t / λ^d)) + ξ √T_eff`, where
`V_t`, `θ̂_t` and `T_eff` are built from the included queries only. -/
theorem misspec_radius_incl_whp [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ ξ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ : 0 < δ) (hB : 0 ≤ B) (hξ : 0 ≤ ξ)
    {η : ℕ → Ω → ℝ} {φ : ℕ → Ω → n → ℝ} {α : ℕ → Ω → ℝ} (bias : ℕ → Ω → ℝ) (θs : n → ℝ)
    (hθ : θs ⬝ᵥ θs ≤ B ^ 2) (hbias : ∀ s ω, |bias s ω| ≤ ξ)
    (hα01 : ∀ s ω, α s ω = 0 ∨ α s ω = 1) (hα : ∀ s, Measurable[ℱ s] (α s))
    (hφ : ∀ s, Measurable[ℱ s] (φ s)) (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    μ {ω | ∃ t : ℕ, misRadius σ lam δ B ξ (inclDesign lam α φ t ω) (effCount α t ω) <
        Real.sqrt
          ((inclRLS lam α φ (fun s ω => φ s ω ⬝ᵥ θs + bias s ω + η s ω) t ω - θs) ⬝ᵥ
            inclDesign lam α φ t ω *ᵥ
              (inclRLS lam α φ (fun s ω => φ s ω ⬝ᵥ θs + bias s ω + η s ω) t ω - θs))} ≤
      ENNReal.ofReal δ := by
  have hψ : ∀ s, Measurable[ℱ s] (fun ω => α s ω • φ s ω) := fun s => (hα s).smul (hφ s)
  refine (measure_mono ?_).trans (self_normalized_ridge ℱ hσ hlam hδ hψ hη hsub)
  rintro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  by_contra hcon
  have h := incl_radius_det hlam hB hξ (fun s : Fin t => α s ω • φ s ω)
    (fun s : Fin t => α s ω) (fun s => hα01 s ω) (fun s : Fin t => bias s ω)
    (fun s : Fin t => η s ω) θs hθ (fun s => hbias s ω) (not_lt.mp hcon)
  unfold misRadius inclRLS effCount at ht
  beta_reduce at ht
  rw [inclDesign_eq lam hα01, incl_sum_eq hα01,
    ← Fin.sum_univ_eq_sum_range (fun s => α s ω) t] at ht
  exact absurd ht (not_lt.mpr h)

variable {X : Type*} [Fintype X]

/-- **Proposition `thm:t3-misspec`, the radius, as stated.**

`Y_s = m₀ + φ_{x_s}ᵀ θ* + b_{x_s} + η_s` with `‖θ*‖ ≤ B_θ`, `‖b‖_∞ ≤ ξ`, queries `x_s`
chosen from the past (`hx`), `η_s` conditionally `σ`-sub-Gaussian given the past, and
predictable inclusion indicators `α_s ∈ {0,1}` (`hα01`, `hα`).  With
`V_t = λ I + ∑_{s<t} α_s φ_{x_s} φ_{x_s}ᵀ` (`inclDesign`), the RLS estimator on included
queries `θ̂_t = V_t⁻¹ ∑_{s<t} α_s (Y_s - m₀) φ_{x_s}` (`inclRLS`) and
`T_eff = ∑_{s<t} α_s` (`effCount`): with probability at least `1 - δ`, for all `t`,
`‖θ̂_t - θ*‖_{V_t} ≤ β_t^{(ξ)}` (`misRadius`, `eq:t3-misspec-radius`). -/
theorem t3_misspec_radius [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ ξ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ : 0 < δ) (hB : 0 ≤ B) (hξ : 0 ≤ ξ)
    (φ : X → n → ℝ) (b : X → ℝ) (mu0 : ℝ) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hb : ∀ z, |b z| ≤ ξ) (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    {α : ℕ → Ω → ℝ} (hα01 : ∀ s ω, α s ω = 0 ∨ α s ω = 1) (hα : ∀ s, Measurable[ℱ s] (α s))
    {η : ℕ → Ω → ℝ} (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ s ω, Y s ω = mu0 + φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω) :
    μ {ω | ∃ t : ℕ,
        misRadius σ lam δ B ξ (inclDesign lam α (fun s ω => φ (x s ω)) t ω) (effCount α t ω) <
        Real.sqrt
          ((inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs) ⬝ᵥ
            inclDesign lam α (fun s ω => φ (x s ω)) t ω *ᵥ
              (inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs))} ≤
      ENNReal.ofReal δ := by
  have hφm : ∀ s, Measurable[ℱ s] (fun ω => φ (x s ω)) := by
    intro s
    have hxm : @Measurable Ω X (ℱ s) ⊤ (x s) :=
      @measurable_to_countable' X Ω ⊤ _ (ℱ s) (x s) (fun x0 => hx s x0)
    exact (measurable_from_top (f := φ) : @Measurable X (n → ℝ) ⊤ _ φ).comp hxm
  have hy : (fun s ω => Y s ω - mu0) =
      fun s ω => φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω := by
    funext s ω
    rw [hY]
    ring
  rw [hy]
  exact misspec_radius_incl_whp ℱ hσ hlam hδ hB hξ (fun s ω => b (x s ω)) θs hθ
    (fun s ω => hb (x s ω)) hα01 hα hφm hη hsub

omit [Fintype n] [DecidableEq n] in
/-- With at most `Nmax` included queries per terminal, `T_eff ≤ |X| · Nmax`. -/
lemma effCount_le_of_cap [DecidableEq X] (α : ℕ → Ω → ℝ) (x : ℕ → Ω → X) (t : ℕ) (ω : Ω)
    (Nmax : ℝ) (hcap : ∀ z, ∑ s ∈ range t, (if x s ω = z then α s ω else 0) ≤ Nmax) :
    effCount α t ω ≤ Fintype.card X * Nmax := by
  have h1 : effCount α t ω = ∑ z : X, ∑ s ∈ range t, (if x s ω = z then α s ω else 0) := by
    unfold effCount
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    simp
  rw [h1]
  calc ∑ z : X, ∑ s ∈ range t, (if x s ω = z then α s ω else 0)
      ≤ ∑ _z : X, Nmax := sum_le_sum fun z _ => hcap z
    _ = Fintype.card X * Nmax := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- The budget cap bounds the bias term: if `T ≤ M ⌈σ²/ξ²⌉` then `ξ √T ≤ √(M (σ² + ξ²))`
(real-valued `T`; cf. `bias_budget_cap`). -/
lemma bias_cap_real {σ ξ : ℝ} (hξ : 0 < ξ) {T : ℝ} (M : ℕ)
    (hT : T ≤ M * (⌈σ ^ 2 / ξ ^ 2⌉₊ : ℝ)) :
    ξ * Real.sqrt T ≤ Real.sqrt (M * (σ ^ 2 + ξ ^ 2)) := by
  have hceil : (⌈σ ^ 2 / ξ ^ 2⌉₊ : ℝ) ≤ σ ^ 2 / ξ ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hT' : T ≤ M * (σ ^ 2 / ξ ^ 2 + 1) :=
    hT.trans (mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg M))
  have hle : ξ ^ 2 * T ≤ M * (σ ^ 2 + ξ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hT' (sq_nonneg ξ)
    have he : ξ ^ 2 * ((M : ℝ) * (σ ^ 2 / ξ ^ 2 + 1)) = M * (σ ^ 2 + ξ ^ 2) := by
      field_simp
    linarith
  calc ξ * Real.sqrt T = Real.sqrt (ξ ^ 2 * T) := by
        rw [Real.sqrt_mul (sq_nonneg ξ), Real.sqrt_sq hξ.le]
    _ ≤ Real.sqrt (M * (σ ^ 2 + ξ ^ 2)) := Real.sqrt_le_sqrt hle

/-- **Proposition `thm:t3-misspec` with the per-terminal cap.**  Model of
`t3_misspec_radius` with `ξ > 0` and at most `N_max(ξ) = ⌈σ²/ξ²⌉` included queries per
terminal (`hcap`).  Then `ξ √T_eff ≤ √(|X| (σ² + ξ²))` at all times, so with probability
at least `1 - δ`, for all `t`,
`‖θ̂_t - θ*‖_{V_t} ≤ √λ B + σ √(2 log (1/δ) + log (det V_t / λ^d)) + √(|X| (σ² + ξ²))`:
the bias inflation does not grow with the number of queries. -/
theorem t3_misspec_radius_capped [DecidableEq X] [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    {σ lam δ ξ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ : 0 < δ) (hB : 0 ≤ B) (hξ : 0 < ξ)
    (φ : X → n → ℝ) (b : X → ℝ) (mu0 : ℝ) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hb : ∀ z, |b z| ≤ ξ) (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    {α : ℕ → Ω → ℝ} (hα01 : ∀ s ω, α s ω = 0 ∨ α s ω = 1) (hα : ∀ s, Measurable[ℱ s] (α s))
    (hcap : ∀ ω t z, ∑ s ∈ range t, (if x s ω = z then α s ω else 0) ≤
      (⌈σ ^ 2 / ξ ^ 2⌉₊ : ℝ))
    {η : ℕ → Ω → ℝ} (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ s ω, Y s ω = mu0 + φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω) :
    μ {ω | ∃ t : ℕ,
        Real.sqrt lam * B +
          σ * Real.sqrt (2 * Real.log (1 / δ) +
            Real.log ((inclDesign lam α (fun s ω => φ (x s ω)) t ω).det /
              lam ^ Fintype.card n)) +
          Real.sqrt (Fintype.card X * (σ ^ 2 + ξ ^ 2)) <
        Real.sqrt
          ((inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs) ⬝ᵥ
            inclDesign lam α (fun s ω => φ (x s ω)) t ω *ᵥ
              (inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω - θs))} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (t3_misspec_radius ℱ hσ hlam hδ hB hξ.le φ b mu0 θs hθ hb x
    hx hα01 hα hη hsub Y hY)
  rintro ω ⟨t, ht⟩
  refine ⟨t, lt_of_le_of_lt ?_ ht⟩
  have hbias := bias_cap_real (σ := σ) hξ (Fintype.card X)
    (effCount_le_of_cap α x t ω _ (hcap ω t))
  unfold misRadius
  linarith

/-- The model-based plausible value set: terminal value vectors
`z ↦ m₀ + φ_zᵀ θ + b'_z` with `θ` in the ellipsoid of radius `r` around `θ̂` in the
`V`-norm and `‖b'‖_∞ ≤ ξ`. -/
def plausibleValues (mu0 ξ : ℝ) (φ : X → n → ℝ) (θhat : n → ℝ) (V : Matrix n n ℝ) (r : ℝ) :
    Set (X → ℝ) :=
  {f | ∃ θ : n → ℝ, ∃ b' : X → ℝ, (∀ z, |b' z| ≤ ξ) ∧
    Real.sqrt ((θhat - θ) ⬝ᵥ V *ᵥ (θhat - θ)) ≤ r ∧ f = fun z => mu0 + φ z ⬝ᵥ θ + b' z}

/-- **Proposition `thm:t3-misspec`, safe intersection, as one statement.**

Model of `t3_misspec_radius`.  In addition every terminal `z` has a tape `W z i` of
independent `[0,1]`-valued observations with mean the true value
`m₀ + φ_zᵀ θ* + b_z`, and `N t ω z` are arbitrary path-dependent counts.  The model-based
plausible value set at level `δ/2` (radius `β_t^{(ξ)}` computed with `δ/2`) intersected
with the running-intersection Hoeffding box at level `δ/2` contains the true value vector
at all times with probability at least `1 - δ`. -/
theorem t3_safe_intersection [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ ξ B M : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : 0 ≤ B) (hξ : 0 ≤ ξ)
    (φ : X → n → ℝ) (b : X → ℝ) (mu0 : ℝ) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hb : ∀ z, |b z| ≤ ξ) (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    {α : ℕ → Ω → ℝ} (hα01 : ∀ s ω, α s ω = 0 ∨ α s ω = 1) (hα : ∀ s, Measurable[ℱ s] (α s))
    {η : ℕ → Ω → ℝ} (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ s ω, Y s ω = mu0 + φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω)
    {W : X → ℕ → Ω → ℝ} (hindep : ∀ z, ProbabilityTheory.iIndepFun (W z) μ)
    (hmeas : ∀ z i, AEMeasurable (W z i) μ)
    (hbdd : ∀ z i, ∀ᵐ ω ∂μ, W z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z i, ∫ ω, W z i ω ∂μ = mu0 + φ z ⬝ᵥ θs + b z)
    (hM : 1 ≤ M) (hcard : (Fintype.card X : ℝ) ≤ M) (N : ℕ → Ω → X → ℕ) :
    μ {ω | ∃ t, (fun z => mu0 + φ z ⬝ᵥ θs + b z) ∉
        plausibleValues mu0 ξ φ
            (inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω)
            (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
            (misRadius σ lam (δ / 2) B ξ (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
              (effCount α t ω)) ∩
          Set.Icc (fun z => runLo (hoeffLo M (δ / 2) (fun i => W z i ω)) (N t ω z))
            (fun z => runHi (hoeffHi M (δ / 2) (fun i => W z i ω)) (N t ω z))} ≤
      ENNReal.ofReal δ := by
  refine safe_intersection μ hδ0.le
    (fun t ω => plausibleValues mu0 ξ φ
      (inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω)
      (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
      (misRadius σ lam (δ / 2) B ξ (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
        (effCount α t ω)))
    (fun t ω => Set.Icc (fun z => runLo (hoeffLo M (δ / 2) (fun i => W z i ω)) (N t ω z))
      (fun z => runHi (hoeffHi M (δ / 2) (fun i => W z i ω)) (N t ω z)))
    (fun z => mu0 + φ z ⬝ᵥ θs + b z) ?_ ?_
  · refine (measure_mono ?_).trans (t3_misspec_radius ℱ hσ hlam (half_pos hδ0) hB hξ φ b mu0
      θs hθ hb x hx hα01 hα hη hsub Y hY)
    rintro ω ⟨t, hnot⟩
    refine ⟨t, ?_⟩
    by_contra hcon
    exact hnot ⟨θs, b, hb, not_lt.mp hcon, rfl⟩
  · refine (measure_mono ?_).trans (hoeffding_box_coverage hindep hmeas hbdd hmean hM hcard
      (half_pos hδ0) (by linarith) N)
    rintro ω ⟨t, hnot⟩
    by_contra hgood
    apply hnot
    have hz : ∀ z, mu0 + φ z ⬝ᵥ θs + b z ∈
        Set.Icc (runLo (hoeffLo M (δ / 2) (fun i => W z i ω)) (N t ω z))
          (runHi (hoeffHi M (δ / 2) (fun i => W z i ω)) (N t ω z)) := by
      intro z
      by_contra h
      exact hgood ⟨t, z, h⟩
    exact ⟨fun z => (hz z).1, fun z => (hz z).2⟩

end Misspec

/-! ### `lem:bay-cs`: invertible Gram matrices and conditionally Gaussian innovations -/

section BayCS

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `|xᵀ M x| ≤ (∑_{ij} |M_ij|) ‖x‖²`, upper half. -/
lemma quad_le_sum_abs_mul (Mx : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ Mx *ᵥ x ≤ (∑ i, ∑ j, |Mx i j|) * (x ⬝ᵥ x) := by
  have hs : ∀ i, x i ^ 2 ≤ x ⬝ᵥ x := fun i => by
    have h := single_le_sum (f := fun k => x k * x k) (fun k _ => mul_self_nonneg (x k))
      (mem_univ i)
    simpa [dotProduct, sq] using h
  have hexp : x ⬝ᵥ Mx *ᵥ x = ∑ i, ∑ j, x i * (Mx i j * x j) := by
    simp only [dotProduct, mulVec, mul_sum]
  rw [hexp, sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [sum_mul]
  refine sum_le_sum fun j _ => ?_
  have h1 : x i * (Mx i j * x j) ≤ |Mx i j| * (|x i| * |x j|) := by
    calc x i * (Mx i j * x j) ≤ |x i * (Mx i j * x j)| := le_abs_self _
      _ = |Mx i j| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
  have h2 : |x i| * |x j| ≤ x ⬝ᵥ x := by
    have hi := hs i
    have hj := hs j
    nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))

/-- A symmetric positive semidefinite matrix that is invertible is coercive: its quadratic
form dominates a positive multiple of `‖x‖²`. -/
theorem coercive_of_psd_isUnit {G : Matrix n n ℝ} (hsymm : Gᵀ = G)
    (hpsd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ G *ᵥ x) (hunit : IsUnit G.det) :
    ∃ lam, 0 < lam ∧ Coercive G lam := by
  set c : ℝ := ∑ i, ∑ j, |G⁻¹ i j| with hc
  have hc0 : 0 ≤ c := sum_nonneg fun i _ => sum_nonneg fun j _ => abs_nonneg _
  refine ⟨1 / (c + 1), by positivity, hsymm, fun x => ?_⟩
  have hq := hpsd x
  have hs := dotProduct_self_nonneg' x
  have hA : x ⬝ᵥ G⁻¹ *ᵥ x ≤ c * (x ⬝ᵥ x) := quad_le_sum_abs_mul G⁻¹ x
  have hGG : G *ᵥ (G⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, one_mulVec]
  have hB : (x ⬝ᵥ x) ^ 2 ≤ (x ⬝ᵥ G *ᵥ x) * (x ⬝ᵥ G⁻¹ *ᵥ x) := by
    have h := cauchy_schwarz_matrix hsymm hpsd x (G⁻¹ *ᵥ x)
    rw [hGG, dotProduct_comm (G⁻¹ *ᵥ x) x] at h
    exact h
  have h1 : (x ⬝ᵥ x) ^ 2 ≤ (x ⬝ᵥ G *ᵥ x) * (c * (x ⬝ᵥ x)) :=
    hB.trans (mul_le_mul_of_nonneg_left hA hq)
  have h2 : x ⬝ᵥ x ≤ (c + 1) * (x ⬝ᵥ G *ᵥ x) := by
    rcases hs.eq_or_lt with h0 | hpos
    · rw [← h0]
      positivity
    · have h3 : (x ⬝ᵥ x) * (x ⬝ᵥ x) ≤ ((x ⬝ᵥ G *ᵥ x) * c) * (x ⬝ᵥ x) := by nlinarith
      have h4 := le_of_mul_le_mul_right h3 hpos
      nlinarith
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  exact h2

/-- **Invertibility of a Gram matrix is the `Coercive` condition.**  `G_t = ∑_{s<t} u_s u_sᵀ`
is invertible iff it is coercive with some positive constant (i.e. positive definite). -/
theorem gram_isUnit_iff_coercive (u : ℕ → n → ℝ) (t : ℕ) :
    IsUnit (gram u t) ↔ ∃ lam, 0 < lam ∧ Coercive (gram u t) lam := by
  rw [Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    refine coercive_of_psd_isUnit (gram_symm u t) (fun x => ?_) h
    rw [gram_quadratic]
    exact sum_nonneg fun s _ => sq_nonneg _
  · rintro ⟨lam, hlam, hG⟩
    exact hG.isUnit_det hlam

/-- **The bounds of Lemma `lem:bay-cs` at invertible `G_t`**: `0 ≤ A_t ≤ (γ/2) ‖θ̂_t‖²`
and `H_t(δ) ≤ log (1/δ) + (d/2) log (1 + t ℓ² / (d γ)) + (γ/2) ‖θ̂_t‖²`, for
`ℓ ≥ max_x ‖u_x‖₂`. -/
theorem bay_cs_bounds [Nonempty n] (u : ℕ → n → ℝ) (t : ℕ) {ℓ γ δ : ℝ}
    (hu : ∀ s, u s ⬝ᵥ u s ≤ ℓ ^ 2) (hinv : IsUnit (gram u t)) (hγ : 0 < γ) (b : n → ℝ) :
    0 ≤ mixGap γ (gram u t) b ∧
      mixGap γ (gram u t) b ≤ γ / 2 * (((gram u t)⁻¹ *ᵥ b) ⬝ᵥ ((gram u t)⁻¹ *ᵥ b)) ∧
      mixThreshold δ γ (gram u t) b ≤
        Real.log (1 / δ) +
          (Fintype.card n : ℝ) / 2 * Real.log (1 + t * ℓ ^ 2 / (Fintype.card n * γ)) +
          γ / 2 * (((gram u t)⁻¹ *ᵥ b) ⬝ᵥ ((gram u t)⁻¹ *ᵥ b)) := by
  obtain ⟨lam, hlam, hG⟩ := (gram_isUnit_iff_coercive u t).mp hinv
  exact ⟨(mixGap_bounds hG hlam hγ b).1, (mixGap_bounds hG hlam hγ b).2,
    mixThreshold_le u t hu hG hlam hγ b⟩

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The conditional law of `X` given `m` is `N(0,1)`**, in elementary form: for every
`A ∈ m` and Borel `B`, `P(A ∩ {X ∈ B}) = P(A) · N(0,1)(B)`. -/
def CondStdGaussian (μ : Measure Ω) (m : MeasurableSpace Ω) (X : Ω → ℝ) : Prop :=
  ∀ A, MeasurableSet[m] A → ∀ B : Set ℝ, MeasurableSet B →
    μ (A ∩ X ⁻¹' B) = μ A * ProbabilityTheory.gaussianReal 0 1 B

/-- Conditionally `N(0,1)` innovations are conditionally `1`-sub-Gaussian. -/
theorem CondStdGaussian.condSubG [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) (h : CondStdGaussian μ m X) :
    CondSubG μ m X 1 := by
  have hlawB : ∀ B : Set ℝ, MeasurableSet B →
      μ (X ⁻¹' B) = ProbabilityTheory.gaussianReal 0 1 B := by
    intro B hB
    have := h Set.univ MeasurableSet.univ B hB
    simpa using this
  have hlaw : @Measure.map Ω ℝ m0 _ X μ = ProbabilityTheory.gaussianReal 0 1 := by
    ext B hB
    rw [Measure.map_apply hX hB, hlawB B hB]
  have hind : ProbabilityTheory.Indep
      (MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)) m μ := by
    rw [ProbabilityTheory.Indep_iff]
    rintro t1 t2 ⟨B, hB, rfl⟩ ht2
    rw [Set.inter_comm, h t2 ht2 B hB, hlawB B hB, mul_comm]
  have hsub := CondSubG.of_indep_gaussian hX hlaw hm hind
  simpa using hsub

/-- **Regular-conditional-law form.**  If for almost every `ω` the law of `X` under the
conditional expectation kernel given `m` is `N(0,1)`, then `X` is conditionally `N(0,1)`
given `m` in the sense of `CondStdGaussian`. -/
theorem condStdGaussian_of_condExpKernel [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (h : ∀ᵐ ω ∂μ, @Measure.map Ω ℝ m0 _ X
        (ProbabilityTheory.condExpKernel (mΩ := m0) μ m ω) =
      ProbabilityTheory.gaussianReal 0 1) :
    CondStdGaussian μ m X := by
  intro A hA B hB
  have hs : MeasurableSet[m0] (X ⁻¹' B) := hX hB
  have hA0 : MeasurableSet[m0] A := hm A hA
  have hint : Integrable ((X ⁻¹' B).indicator fun _ : Ω => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hs
  have h1 := ProbabilityTheory.condExpKernel_ae_eq_condExp (mΩ := m0) (m := m) (μ := μ) hm hs
  have h2 : ∫ ω in A, (μ[(X ⁻¹' B).indicator (fun _ : Ω => (1 : ℝ)) | m]) ω ∂μ =
      ∫ ω in A, (X ⁻¹' B).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ :=
    setIntegral_condExp hm hint hA
  have h3 : ∫ ω in A, (X ⁻¹' B).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
      μ.real (A ∩ X ⁻¹' B) := by
    rw [integral_indicator hs, Measure.restrict_restrict hs, setIntegral_const, smul_eq_mul,
      mul_one, Set.inter_comm]
  have h4 : ∫ ω in A, (μ[(X ⁻¹' B).indicator (fun _ : Ω => (1 : ℝ)) | m]) ω ∂μ =
      ∫ _ω in A, (ProbabilityTheory.gaussianReal 0 1).real B ∂μ := by
    refine setIntegral_congr_ae hA0 ?_
    filter_upwards [h1, h] with ω hω1 hω2 _
    rw [← hω1, measureReal_def, measureReal_def, ← hω2, Measure.map_apply hX hB]
  rw [setIntegral_const, smul_eq_mul] at h4
  have hreal : μ.real (A ∩ X ⁻¹' B) = μ.real A * (ProbabilityTheory.gaussianReal 0 1).real B := by
    rw [← h3, ← h2, h4]
  have hfin : μ A * ProbabilityTheory.gaussianReal 0 1 B ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top μ A) (measure_ne_top _ B)
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) hfin, ENNReal.toReal_mul]
  exact hreal

/-- **Full-domain confidence sequence (Lemma `lem:bay-cs`), as stated.**

Observations `Y_s = u_sᵀ θ + ν_s` with predictable `u_s` (`hu`) and conditional
innovations `ν_s ∼ N(0,1)` given the past (`hgauss`); `G_t = ∑_{s<t} u_s u_sᵀ`,
`b_t = ∑_{s<t} Y_s u_s`, `θ̂_t = G_t⁻¹ b_t` and
`C_t(δ) = {v : ½ ‖v - θ̂_t‖²_{G_t} ≤ H_t(δ)}`.  For every fixed `θ`,
`P_θ(θ ∈ C_t(δ) for all t with G_t invertible) ≥ 1 - δ`: the event that `θ ∉ C_t(δ)` at
some `t` with `G_t` invertible has probability at most `δ`. -/
theorem bay_cs_literal [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) {u : ℕ → Ω → n → ℝ} {ν : ℕ → Ω → ℝ} (θ : n → ℝ)
    (hu : ∀ s, Measurable[ℱ s] (u s)) (hν : ∀ s, Measurable[ℱ (s + 1)] (ν s))
    (hgauss : ∀ s, CondStdGaussian μ (ℱ s) (ν s)) :
    μ {ω | ∃ t, IsUnit (gram (fun s => u s ω) t) ∧
        mixThreshold δ γ (gram (fun s => u s ω) t) (bayB u ν θ t ω) <
          1 / 2 * ((θ - (gram (fun s => u s ω) t)⁻¹ *ᵥ bayB u ν θ t ω) ⬝ᵥ
            gram (fun s => u s ω) t *ᵥ
              (θ - (gram (fun s => u s ω) t)⁻¹ *ᵥ bayB u ν θ t ω))} ≤
      ENNReal.ofReal δ := by
  have hsub : ∀ s, CondSubG μ (ℱ s) (ν s) 1 := fun s =>
    (hgauss s).condSubG ((hν s).mono (ℱ.le _) le_rfl) (ℱ.le s)
  refine (measure_mono ?_).trans (bay_cs_coverage_subgaussian ℱ hδ hγ θ hu hν hsub)
  rintro ω ⟨t, hinv, hlt⟩
  exact ⟨t, (gram_isUnit_iff_coercive _ t).mp hinv, hlt⟩

/-- Lemma `lem:bay-cs` with the Gaussian hypothesis in regular-conditional-law form: for
each `s` and almost every `ω`, the law of `ν_s` under the conditional kernel given `ℱ_s`
is `N(0,1)`. -/
theorem bay_cs_literal_kernel [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) {u : ℕ → Ω → n → ℝ} {ν : ℕ → Ω → ℝ} (θ : n → ℝ)
    (hu : ∀ s, Measurable[ℱ s] (u s)) (hν : ∀ s, Measurable[ℱ (s + 1)] (ν s))
    (hgauss : ∀ s, ∀ᵐ ω ∂μ, (ProbabilityTheory.condExpKernel μ (ℱ s) ω).map (ν s) =
      ProbabilityTheory.gaussianReal 0 1) :
    μ {ω | ∃ t, IsUnit (gram (fun s => u s ω) t) ∧
        mixThreshold δ γ (gram (fun s => u s ω) t) (bayB u ν θ t ω) <
          1 / 2 * ((θ - (gram (fun s => u s ω) t)⁻¹ *ᵥ bayB u ν θ t ω) ⬝ᵥ
            gram (fun s => u s ω) t *ᵥ
              (θ - (gram (fun s => u s ω) t)⁻¹ *ᵥ bayB u ν θ t ω))} ≤
      ENNReal.ofReal δ :=
  bay_cs_literal ℱ hδ hγ θ hu hν fun s =>
    condStdGaussian_of_condExpKernel ((hν s).mono (ℱ.le _) le_rfl) (ℱ.le s) (hgauss s)

end BayCS

/-! ### `thm:t4-finite-sample`: an infinite run of Algorithm `alg:cd-joint` -/

section CDInfinite

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- The stopping test of Algorithm `alg:cd-joint` at time `t`: `min_a R_t(a) ≤ ε`, i.e.
some action passes `cdDualCert`. -/
def CDCertified (lam : ℝ) (φ : X → n → ℝ) (ι : Z → X) (supp : A → Finset Z) (ε : ℝ)
    (x : ℕ → X) (m : ℕ → n → ℝ) (β : ℕ → ℝ) (t : ℕ) : Prop :=
  ∃ a, cdDualCert (design lam φ x t) (fun z => φ (ι z)) (m t) (β t) ε (supp a)

/-- The stopping time `τ`: the first time at which the stopping test passes (`0` if it
never does). -/
noncomputable def cdStop (lam : ℝ) (φ : X → n → ℝ) (ι : Z → X) (supp : A → Finset Z) (ε : ℝ)
    (x : ℕ → X) (m : ℕ → n → ℝ) (β : ℕ → ℝ) : ℕ :=
  sInf {t | CDCertified lam φ ι supp ε x m β t}

/-- **An infinite run of Algorithm `alg:cd-joint`**: at every time at which the stopping
test fails, the query `x t` follows the rule `CDStep`.  Nothing is required at other
times. -/
def CDRun (lam : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X) (supp : A → Finset Z) (ε : ℝ)
    (x : ℕ → X) (m : ℕ → n → ℝ) (β : ℕ → ℝ) : Prop :=
  ∀ t, ¬ CDCertified lam φ ι supp ε x m β t →
    CDStep (design lam φ x t) (m t) (β t) ε φ cost ι supp (x t)

/-- **Theorem `thm:t4-finite-sample` for an infinite run and its first certified time.**

Fixed-feature model as in `cd_joint_run`; `m t`, `β t` are the estimate and the radius,
with `β` positive and nondecreasing.  For an infinite run of Algorithm `alg:cd-joint`:

* for every `T` such that no step before `T` is certified, the cumulative cost of the first
  `T` queries satisfies `eq:t4-bound` with `T` in place of `τ`;
* if the stopping test ever passes, then at the stopping time `τ = cdStop` the test passes,
  the cumulative cost satisfies `eq:t4-bound`, and every action that passes the test at `τ`
  (in particular the returned minimiser) is `ε`-optimal for every parameter in the
  confidence ellipsoid at time `τ` (the coverage event). -/
theorem cd_joint_infinite_run {lam : ℝ} (hlam : 0 < lam) (φ : X → n → ℝ) (cost : X → ℝ)
    {cmax Lsq ε : ℝ} (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax)
    (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε) (ι : Z → X) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (x : ℕ → X) (m : ℕ → n → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ t, 0 < β t) (hβmono : Monotone β)
    (hrun : CDRun lam φ cost ι supp ε x m β) :
    (∀ T, (∀ t < T, ¬ CDCertified lam φ ι supp ε x m β t) →
      ∑ t ∈ range T, cost (x t) ≤
        16 * cmax * (1 + Lsq / lam) * β (T - 1) ^ 2 / ε ^ 2 *
          Real.log ((design lam φ x T).det / lam ^ Fintype.card n)) ∧
    ((∃ t, CDCertified lam φ ι supp ε x m β t) →
      CDCertified lam φ ι supp ε x m β (cdStop lam φ ι supp ε x m β) ∧
      ∑ t ∈ range (cdStop lam φ ι supp ε x m β), cost (x t) ≤
        16 * cmax * (1 + Lsq / lam) * β (cdStop lam φ ι supp ε x m β - 1) ^ 2 / ε ^ 2 *
          Real.log ((design lam φ x (cdStop lam φ ι supp ε x m β)).det /
            lam ^ Fintype.card n) ∧
      ∀ (r : A) (θs : n → ℝ),
        cdDualCert (design lam φ x (cdStop lam φ ι supp ε x m β)) (fun z => φ (ι z))
          (m (cdStop lam φ ι supp ε x m β)) (β (cdStop lam φ ι supp ε x m β)) ε (supp r) →
        (θs - m (cdStop lam φ ι supp ε x m β)) ⬝ᵥ
            design lam φ x (cdStop lam φ ι supp ε x m β) *ᵥ
              (θs - m (cdStop lam φ ι supp ε x m β)) ≤
          β (cdStop lam φ ι supp ε x m β) ^ 2 →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε) := by
  have hprefix : ∀ T, (∀ t < T, ¬ CDCertified lam φ ι supp ε x m β t) →
      ∑ t ∈ range T, cost (x t) ≤
        16 * cmax * (1 + Lsq / lam) * β (T - 1) ^ 2 / ε ^ 2 *
          Real.log ((design lam φ x T).det / lam ^ Fintype.card n) := by
    intro T hT
    exact (cd_joint_run hlam φ cost hcost hφ hε ι supp hne T x m β (fun t _ => hβpos t)
      (fun s t hst _ => hβmono hst)
      (fun t ht => ⟨fun a ha => hT t ht ⟨a, ha⟩, hrun t (hT t ht)⟩)).1
  refine ⟨hprefix, fun hex => ⟨Nat.sInf_mem
    (show Set.Nonempty {t | CDCertified lam φ ι supp ε x m β t} from hex), ?_, ?_⟩⟩
  · exact hprefix _ (fun t ht hc => absurd (Nat.sInf_le (show t ∈ {t | CDCertified lam φ ι supp ε x m β t} from hc))
      (not_le.mpr ht))
  · intro r θs hcert hcov
    exact (cdDualCert_iff (design_coercive lam φ x _) hlam (hne r) (hβpos _).le _ _).mp hcert
      θs hcov

end CDInfinite

/-! ### `thm:t4-finite-sample`: termination and the end-to-end statement -/

section CDTermination

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

omit [Fintype n] [Fintype X] [DecidableEq X] in
lemma design_eq_gram (lam : ℝ) (φ : X → n → ℝ) (x : ℕ → X) :
    ∀ t, design lam φ x t = lam • (1 : Matrix n n ℝ) + gram (fun s => φ (x s)) t
  | 0 => by simp [design, gram]
  | t + 1 => by
    show design lam φ x t + vecMulVec (φ (x t)) (φ (x t)) = _
    rw [design_eq_gram lam φ x t]
    unfold gram
    rw [sum_range_succ, add_assoc]

omit [Fintype X] [DecidableEq X] in
/-- `log (det V_t / λ^d) ≤ d log (1 + t L² / (d λ))` (determinant--trace inequality). -/
lemma log_design_det_le [Nonempty n] {lam Lsq : ℝ} (hlam : 0 < lam) (hLsq : 0 ≤ Lsq)
    (φ : X → n → ℝ) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (x : ℕ → X) (t : ℕ) :
    Real.log ((design lam φ x t).det / lam ^ Fintype.card n) ≤
      Fintype.card n * Real.log (1 + t * Lsq / (Fintype.card n * lam)) := by
  have hdet : (design lam φ x t).det / lam ^ Fintype.card n =
      (1 + lam⁻¹ • gram (fun s => φ (x s)) t).det := by
    have e : lam • (1 : Matrix n n ℝ) + gram (fun s => φ (x s)) t =
        lam • (1 + lam⁻¹ • gram (fun s => φ (x s)) t) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
    rw [design_eq_gram, e, det_smul]
    exact mul_div_cancel_left₀ _ (pow_pos hlam _).ne'
  rw [hdet]
  have hpsd : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ gram (fun s => φ (x s)) t *ᵥ v := fun v => by
    rw [gram_quadratic]
    exact sum_nonneg fun s _ => sq_nonneg _
  have htr := gram_trace_le (fun s => φ (x s)) t (ℓ := Real.sqrt Lsq)
    (fun s => by rw [Real.sq_sqrt hLsq]; exact hφ _)
  rw [Real.sq_sqrt hLsq] at htr
  exact logdet_le_of_trace_le (gram_symm _ t) hpsd hlam htr

/-- A count `T` with `c_min T ≤ K (a + b ℓ) ℓ` and `ℓ ≤ d log (1 + c T)` is bounded by an
explicit constant: a linear function cannot stay below a squared logarithm. -/
lemma real_termination {cmin K a b c d T ℓ : ℝ} (hcmin : 0 < cmin) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hT : 0 ≤ T) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ d * Real.log (1 + c * T)) (hcost : cmin * T ≤ K * (a + b * ℓ) * ℓ) :
    T ≤ (K * (a + 4 * b * d) * (4 * d)) ^ 2 * c / cmin ^ 2 +
      K * (a + 4 * b * d) * (4 * d) / cmin := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = K * (a + 4 * b * d) * (4 * d) := ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 + c * T := ⟨_, rfl⟩
  rw [← hy] at hℓ
  have hy1 : 1 ≤ y := by
    have := mul_nonneg hc hT
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (Real.sqrt y) := ⟨_, rfl⟩
  have hsy : s ^ 2 = Real.sqrt y := by rw [hs]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have hsqrt1 : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy1
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hsqrt1
  have hlog : Real.log y ≤ 4 * s := by
    have h4 : y = s ^ 4 := by
      have e : s ^ 4 = (s ^ 2) ^ 2 := by ring
      rw [e, hsy, hyy]
    rw [h4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    push_cast
    linarith
  have hℓ' : ℓ ≤ 4 * d * s := by
    calc ℓ ≤ d * Real.log y := hℓ
      _ ≤ d * (4 * s) := mul_le_mul_of_nonneg_left hlog hd
      _ = 4 * d * s := by ring
  have h1 : (a + b * ℓ) * ℓ ≤ (a + 4 * b * d) * (4 * d) * s ^ 2 := by
    have hA : a + b * ℓ ≤ (a + 4 * b * d) * s := by
      have h5 : b * ℓ ≤ b * (4 * d * s) := mul_le_mul_of_nonneg_left hℓ' hb
      have h6 : a ≤ a * s := le_mul_of_one_le_right ha hs1
      nlinarith
    calc (a + b * ℓ) * ℓ ≤ ((a + 4 * b * d) * s) * (4 * d * s) :=
          mul_le_mul hA hℓ' hℓ0 (by positivity)
      _ = (a + 4 * b * d) * (4 * d) * s ^ 2 := by ring
  have h2 : cmin * T ≤ R * Real.sqrt y := by
    calc cmin * T ≤ K * ((a + b * ℓ) * ℓ) := by rw [← mul_assoc]; exact hcost
      _ ≤ K * ((a + 4 * b * d) * (4 * d) * s ^ 2) := mul_le_mul_of_nonneg_left h1 hK
      _ = R * Real.sqrt y := by rw [hsy, hR]; ring
  have h3 : (cmin * T) ^ 2 ≤ R ^ 2 * (1 + c * T) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ cmin * T) h2 2
    rw [mul_pow R, hyy, hy] at h
    exact h
  by_contra hcon
  have hcon' := not_le.mp hcon
  have hT1 : R / cmin < T :=
    lt_of_le_of_lt (le_add_of_nonneg_left (by positivity)) hcon'
  have hT1' : R < cmin * T := by rwa [div_lt_iff₀ hcmin, mul_comm] at hT1
  have hT2 : R ^ 2 * c + R * cmin < cmin ^ 2 * T := by
    have h := mul_lt_mul_of_pos_left hcon' (pow_pos hcmin 2)
    have e : cmin ^ 2 * (R ^ 2 * c / cmin ^ 2 + R / cmin) = R ^ 2 * c + R * cmin := by
      field_simp
    linarith
  have hTpos : 0 < T := lt_of_le_of_lt (by positivity) hT1
  nlinarith [mul_lt_mul_of_pos_right hT2 hTpos, mul_le_mul_of_nonneg_left hT1'.le hR0]

/-- **Termination of safeguarded CD-Joint with the radius `eq:ay-radius`.**  There is a
number `N`, depending only on the parameters of the model, such that every infinite run of
Algorithm `alg:cd-joint` with radius `β_t = √λ B + σ √(2 log (1/δ) + log (det V_t / λ^d))`
(and any estimate sequence) passes the stopping test at some time `t ≤ N`.  This follows
from the cost bound `eq:t4-bound`: its right-hand side grows like `log² T` while the
left-hand side is at least `c_min T`. -/
theorem cd_joint_terminates [Nonempty n] {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B) (φ : X → n → ℝ) (cost : X → ℝ)
    {cmax Lsq ε : ℝ} (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax)
    (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε) (ι : Z → X) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) :
    ∃ N : ℕ, ∀ (x : ℕ → X) (m : ℕ → n → ℝ),
      CDRun lam φ cost ι supp ε x m (fun t => ayRadius σ lam δ B (design lam φ x t)) →
      ∃ t, t ≤ N ∧
        CDCertified lam φ ι supp ε x m (fun t => ayRadius σ lam δ B (design lam φ x t)) t := by
  obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image (univ : Finset X) cost
    ⟨ι (Classical.arbitrary Z), mem_univ _⟩
  have hcmin : 0 < cost x0 := (hcost x0).1
  have hcmax : 0 < cmax := hcmin.trans_le (hcost x0).2
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ x0)).trans (hφ x0)
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 16 * cmax * (1 + Lsq / lam) / ε ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * lam * B ^ 2 + 4 * σ ^ 2 * Real.log (1 / δ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Lsq / (Fintype.card n * lam) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈(K * (a + 4 * b * (Fintype.card n : ℝ)) *
      (4 * (Fintype.card n : ℝ))) ^ 2 * c / cost x0 ^ 2 +
      K * (a + 4 * b * (Fintype.card n : ℝ)) * (4 * (Fintype.card n : ℝ)) / cost x0⌉₊ :=
    ⟨_, rfl⟩
  refine ⟨N, fun x m hrun => ?_⟩
  by_contra hcon
  have hunc : ∀ t, t ≤ N → ¬ CDCertified lam φ ι supp ε x m
      (fun t => ayRadius σ lam δ B (design lam φ x t)) t := fun t ht hcert => hcon ⟨t, ht, hcert⟩
  have hβpos : ∀ t, 0 < ayRadius σ lam δ B (design lam φ x t) := fun t =>
    ayRadius_design_pos hσ hlam hδ0 hδ1 hB φ x t
  have hβmono : Monotone fun t => ayRadius σ lam δ B (design lam φ x t) := fun s t hst =>
    ayRadius_design_mono hσ hlam φ x hst
  have hpre := (cd_joint_infinite_run hlam φ cost hcost hφ hε ι supp hne x m
    (fun t => ayRadius σ lam δ B (design lam φ x t)) hβpos hβmono hrun).1 (N + 1)
    (fun t ht => hunc t (by omega))
  have hN1 : N + 1 - 1 = N := by omega
  rw [hN1] at hpre
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((design lam φ x (N + 1)).det / lam ^ Fintype.card n) :=
    ⟨_, rfl⟩
  rw [← hℓ] at hpre
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓ]
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (pow_pos hlam _), one_mul, ← design_det_zero lam φ x]
    exact design_det_mono hlam φ x (Nat.zero_le _)
  have hℓle : ℓ ≤ (Fintype.card n : ℝ) * Real.log (1 + c * ((N + 1 : ℕ) : ℝ)) := by
    have h := log_design_det_le hlam hLsq φ hφ x (N + 1)
    have e : 1 + c * ((N + 1 : ℕ) : ℝ) =
        1 + ((N + 1 : ℕ) : ℝ) * Lsq / (Fintype.card n * lam) := by
      rw [hc]
      ring
    rw [hℓ, e]
    exact h
  have hβN : ayRadius σ lam δ B (design lam φ x N) ^ 2 ≤ a + b * ℓ := by
    have h1 : ayRadius σ lam δ B (design lam φ x N) ≤
        ayRadius σ lam δ B (design lam φ x (N + 1)) := hβmono (Nat.le_succ N)
    have h2 : ayRadius σ lam δ B (design lam φ x (N + 1)) =
        Real.sqrt lam * B + σ * Real.sqrt (2 * Real.log (1 / δ) + ℓ) := by
      rw [hℓ]
      rfl
    have hu : 0 ≤ 2 * Real.log (1 / δ) + ℓ := by linarith
    have h3 : ayRadius σ lam δ B (design lam φ x (N + 1)) ^ 2 ≤
        2 * (Real.sqrt lam * B) ^ 2 +
          2 * (σ * Real.sqrt (2 * Real.log (1 / δ) + ℓ)) ^ 2 := by
      rw [h2]
      nlinarith [sq_nonneg (Real.sqrt lam * B - σ * Real.sqrt (2 * Real.log (1 / δ) + ℓ))]
    have h4 : (Real.sqrt lam * B) ^ 2 = lam * B ^ 2 := by rw [mul_pow, Real.sq_sqrt hlam.le]
    have h5 : (σ * Real.sqrt (2 * Real.log (1 / δ) + ℓ)) ^ 2 =
        σ ^ 2 * (2 * Real.log (1 / δ) + ℓ) := by rw [mul_pow, Real.sq_sqrt hu]
    have h6 : ayRadius σ lam δ B (design lam φ x N) ^ 2 ≤
        ayRadius σ lam δ B (design lam φ x (N + 1)) ^ 2 :=
      pow_le_pow_left₀ (hβpos N).le h1 2
    rw [h4, h5] at h3
    rw [ha, hb]
    linarith
  have hsum : cost x0 * ((N + 1 : ℕ) : ℝ) ≤ ∑ t ∈ range (N + 1), cost (x t) := by
    have h := Finset.card_nsmul_le_sum (range (N + 1)) (fun t => cost (x t)) (cost x0)
      (fun t _ => hx0 (x t) (mem_univ _))
    rw [card_range, nsmul_eq_mul] at h
    linarith [mul_comm (cost x0) ((N + 1 : ℕ) : ℝ)]
  have hcostb : cost x0 * ((N + 1 : ℕ) : ℝ) ≤ K * (a + b * ℓ) * ℓ := by
    refine hsum.trans (hpre.trans ?_)
    have e : 16 * cmax * (1 + Lsq / lam) * ayRadius σ lam δ B (design lam φ x N) ^ 2 / ε ^ 2 * ℓ =
        K * ayRadius σ lam δ B (design lam φ x N) ^ 2 * ℓ := by
      rw [hK]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβN hK0) hℓ0
  have hfin := real_termination hcmin hK0 ha0 hb0 hc0 hd.le (Nat.cast_nonneg _) hℓ0 hℓle hcostb
  have hle : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    refine hfin.trans ?_
    rw [hN]
    exact Nat.le_ceil _
  have : N + 1 ≤ N := by exact_mod_cast hle
  omega

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Finite-sample cost of safeguarded CD-Joint (Theorem `thm:t4-finite-sample`), for an
infinite run with its first certified time.**

Model of `cd_joint_finite_sample`: fixed features with `‖φ x‖² ≤ Lsq`, costs
`0 < cost x ≤ cmax`, terminals in the dictionary, `‖θ*‖ ≤ B`, predictable queries,
observations `Y_s = φ_{x_s}ᵀ θ* + η_s` with conditionally `σ`-sub-Gaussian noise, the
ridge estimate and the radius `eq:ay-radius`.  On every sample path the queries form an
infinite run of Algorithm `alg:cd-joint` (`CDRun`).  Then with probability at least
`1 - δ`: the stopping test passes at the stopping time `τ = cdStop` (so the procedure
returns), the cumulative cost up to `τ` satisfies `eq:t4-bound`, and every action that
passes the test at `τ` is `ε`-optimal.  (Termination and the cost bound hold on every
path, `cd_joint_terminates` and `cd_joint_infinite_run`; only `ε`-optimality uses
coverage.) -/
theorem cd_joint_literal [Nonempty n] [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) {η : ℕ → Ω → ℝ} (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ)
    (hrun : ∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω)
      (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
      (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))) :
    μ {ω | ¬ (CDCertified lam φ ι supp ε (fun s => x s ω)
          (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
          (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))
          (cdStop lam φ ι supp ε (fun s => x s ω)
            (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
            (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))) ∧
        ∑ t ∈ range (cdStop lam φ ι supp ε (fun s => x s ω)
            (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
            (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))), cost (x t ω) ≤
          16 * cmax * (1 + Lsq / lam) *
            ayRadius σ lam δ B (design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
                (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)) - 1)) ^ 2 /
              ε ^ 2 *
            Real.log ((design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
                (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)))).det /
              lam ^ Fintype.card n) ∧
        ∀ r : A,
          cdDualCert (design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
                (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))))
            (fun z => φ (ι z))
            (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
                (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))))
            (ayRadius σ lam δ B (design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
                (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)))))
            ε (supp r) →
          regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε)} ≤
      ENNReal.ofReal δ := by
  have hφm : ∀ s, Measurable[ℱ s] (fun ω => φ (x s ω)) := by
    intro s
    have hxm : @Measurable Ω X (ℱ s) ⊤ (x s) :=
      @measurable_to_countable' X Ω ⊤ _ (ℱ s) (x s) (fun x0 => hx s x0)
    exact (measurable_from_top (f := φ) : @Measurable X (n → ℝ) ⊤ _ φ).comp hxm
  obtain ⟨N, hN⟩ := cd_joint_terminates (δ := δ) (B := B) hσ hlam hδ0 hδ1 hB φ cost hcost hφ
    hε ι supp hne
  refine (measure_mono ?_).trans (ay_radius_whp ℱ hσ hlam hδ0 hB (η := η)
    (φ := fun s ω => φ (x s ω)) θs hθ hφm hη hsub)
  intro ω hω
  by_contra hgood
  apply hω
  have e1 : ∀ t, ridgeDesign lam (fun s : Fin t => φ (x s ω)) =
      design lam φ (fun s => x s ω) t := fun t =>
    (ridgeDesign_fin_eq lam (fun s ω => φ (x s ω)) t ω).trans
      (design_eq_snDesign lam φ x ω t).symm
  have e2 : ∀ t, ∑ s : Fin t, (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω) =
      ∑ s ∈ range t, (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω) := fun t =>
    Fin.sum_univ_eq_sum_range (fun s => (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω)) t
  have hcov : ∀ t, Real.sqrt
      ((ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t - θs) ⬝ᵥ
        design lam φ (fun s => x s ω) t *ᵥ
          (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t - θs)) ≤
      ayRadius σ lam δ B (design lam φ (fun s => x s ω) t) := by
    intro t
    by_contra h
    apply hgood
    refine ⟨t, ?_⟩
    rw [e1, e2]
    exact not_le.mp h
  obtain ⟨t, -, hcert⟩ := hN (fun s => x s ω)
    (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω)) (hrun ω)
  obtain ⟨hstop, hcostb, hcorr⟩ := (cd_joint_infinite_run hlam φ cost hcost hφ hε ι supp hne
    (fun s => x s ω) (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
    (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))
    (fun t => ayRadius_design_pos hσ hlam hδ0 hδ1 hB φ (fun s => x s ω) t)
    (fun s t hst => ayRadius_design_mono hσ hlam φ (fun s => x s ω) hst) (hrun ω)).2 ⟨t, hcert⟩
  refine ⟨hstop, hcostb, fun r hr => hcorr r θs hr ?_⟩
  have h := (Real.sqrt_le_iff.mp (hcov (cdStop lam φ ι supp ε (fun s => x s ω)
    (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
    (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))))).2
  have hneg : ∀ v : n → ℝ, θs - v = -(v - θs) := fun v => by rw [neg_sub]
  rw [hneg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  exact h

end CDTermination

end LiteralABC2

end JointRootCert
