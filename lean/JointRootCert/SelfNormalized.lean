/-
Self-normalized bound for vector-valued martingales and the Gaussian mixture
confidence sequence (Abbasi-Yadkori, Pal and Szepesvari 2011, Theorem 1).

Results covered (they were hypotheses of earlier files):

* the self-normalized radius `eq:ay-radius` used by Theorem `thm:t4-finite-sample`
  and by Proposition `thm:t3-misspec` (`self_normalized_bound`,
  `self_normalized_ridge`, `misspec_radius_whp`, `ay_radius_whp`);
* the mixture supermartingale of Lemma `lem:bay-cs` (`snMix_supermartingale`,
  `snMix_bay_form`, `bay_cs_coverage_subgaussian`).

Contents.

* `CondSubG`: the conditional `σ`-sub-Gaussian assumption in integrated form, with
  bridges from conditional expectations (`CondSubG.of_condExp`), from Mathlib's
  `HasCondSubgaussianMGF`, and from independent Gaussian noise
  (`CondSubG.of_indep_gaussian`).
* `CondSubG.setLIntegral_le_of_measurable`: the conditional moment bound with a random,
  conditionally known coefficient.
* `expMart_supermartingale`: the fixed-`λ` exponential process is a supermartingale.
* `gauss_mix_lintegral`, `scalar_mixture_closed_form`: one-dimensional Gaussian mixing
  integrals in closed form.
* `snMix_supermartingale`: the closed-form mixture
  `(det V_0 / det V_t)^{1/2} exp ((‖S_t‖²_{V_t⁻¹} - ‖S_0‖²_{V_0⁻¹}) / (2 σ²))`
  is a nonnegative supermartingale in any finite dimension.
* `self_normalized_bound`: the time-uniform bound, by Ville's inequality.

Method.  The supermartingale property of the closed-form mixture is proved one step at
a time: by the rank-one update of `‖S‖²_{V⁻¹}` and the matrix determinant lemma, the
one-step ratio of the mixture is a one-dimensional Gaussian mixture of the exponential
factors `exp (c η - c² σ² / 2)` with conditionally known coefficients `c`, so only
one-dimensional Gaussian integrals are needed.  The identity between the closed form
and the `d`-dimensional integral `∫ M_t^λ dN(0, V_0⁻¹)(λ)` is proved only for `d = 1`
(`scalar_mixture_closed_form`); it is not needed for the bounds.
-/
import JointRootCert.Coverage

namespace JointRootCert

open Finset MeasureTheory Matrix Filter
open scoped ENNReal Topology

/-! ### Conditional sub-Gaussian noise -/

/-- The normalized exponential factor `exp (c x - c² σ² / 2)`. -/
noncomputable def expFac (σ c x : ℝ) : ℝ := Real.exp (c * x - c ^ 2 * σ ^ 2 / 2)

lemma expFac_pos (σ c x : ℝ) : 0 < expFac σ c x := Real.exp_pos _

section Helpers

variable {α : Type*} {mα : MeasurableSpace α}

lemma measurable_dyadic {C : α → ℝ} (hC : Measurable C) (k : ℕ) :
    Measurable fun ω => (⌊C ω * 2 ^ k⌋ : ℝ) / 2 ^ k :=
  ((measurable_of_countable (fun j : ℤ => (j : ℝ))).comp (hC.mul_const _).floor).div_const _

lemma measurable_expFac (σ : ℝ) {C X : α → ℝ} (hC : Measurable C) (hX : Measurable X) :
    Measurable fun ω => expFac σ (C ω) (X ω) := by
  unfold expFac
  exact Real.measurable_exp.comp ((hC.mul hX).sub (((hC.pow_const 2).mul_const _).div_const _))

lemma measurable_ofReal_expFac (σ : ℝ) {C X : α → ℝ} (hC : Measurable C) (hX : Measurable X) :
    Measurable fun ω => ENNReal.ofReal (expFac σ (C ω) (X ω)) :=
  ENNReal.measurable_ofReal.comp (measurable_expFac σ hC hX)

lemma measurable_indicator_ofReal {f : α → ℝ} (hf : Measurable f) {A : Set α}
    (hA : MeasurableSet A) : Measurable (A.indicator fun ω => ENNReal.ofReal (f ω)) :=
  (ENNReal.measurable_ofReal.comp hf).indicator hA

lemma stronglyMeasurable_of_measurable_real {f : α → ℝ} (hf : Measurable f) :
    StronglyMeasurable f := hf.stronglyMeasurable

lemma measurable_dotProduct {n : Type*} [Fintype n] {x y : α → n → ℝ} (hx : Measurable x)
    (hy : Measurable y) : Measurable fun ω => x ω ⬝ᵥ y ω := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hx).mul ((measurable_pi_apply i).comp hy)

lemma measurable_unit_pi {f : α → ℝ} (hf : Measurable f) :
    Measurable fun (ω : α) (_ : Unit) => f ω :=
  measurable_pi_iff.mpr fun _ => hf

lemma measurable_div_const_real {f : α → ℝ} (hf : Measurable f) (c : ℝ) :
    Measurable fun ω => f ω / c := hf.div_const c

lemma measurable_exp_sum_aux {t : ℕ} {η x : ℕ → α → ℝ} (hη : ∀ s < t, Measurable (η s))
    (hx : ∀ s < t, Measurable (x s)) (σ : ℝ) :
    Measurable fun ω => Real.exp (∑ s ∈ range t, (η s ω * x s ω / σ - x s ω ^ 2 / 2)) := by
  refine Real.measurable_exp.comp (Finset.measurable_sum _ fun s hs => ?_)
  have hs' := mem_range.mp hs
  exact (((hη s hs').mul (hx s hs')).div_const _).sub (((hx s hs').pow_const 2).div_const _)

end Helpers

section CondSubG

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- `X` is conditionally `σ`-sub-Gaussian given the sub-σ-algebra `m`, in integrated form:
`E[exp (c X) 1_A] ≤ exp (c² σ² / 2) P(A)` for every real `c` and every `A ∈ m`.
For integrable `exp (c X)` this is `E[exp (c X) | m] ≤ exp (c² σ² / 2)` a.e.
(`CondSubG.of_condExp`). -/
def CondSubG (μ : Measure Ω) (m : MeasurableSpace Ω) (X : Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ c : ℝ, ∀ A : Set Ω, MeasurableSet[m] A →
    ∫⁻ ω in A, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)) * μ A

/-- The conditional-expectation form of the sub-Gaussian assumption implies `CondSubG`. -/
theorem CondSubG.of_condExp [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {X : Ω → ℝ} {σ : ℝ} (hint : ∀ c : ℝ, Integrable (fun ω => Real.exp (c * X ω)) μ)
    (hce : ∀ c : ℝ, ∀ᵐ ω ∂μ,
      (μ[fun ω => Real.exp (c * X ω) | m]) ω ≤ Real.exp (c ^ 2 * σ ^ 2 / 2)) :
    CondSubG μ m X σ := by
  intro c A hA
  have hA0 : MeasurableSet[m0] A := hm A hA
  have h1 : ∫⁻ ω in A, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ =
      ENNReal.ofReal (∫ ω in A, Real.exp (c * X ω) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hint c).integrableOn
      (ae_of_all _ fun ω => (Real.exp_pos _).le)).symm
  have h2 := setIntegral_condExp hm (hint c) hA
  have h3 : ∫ ω in A, (μ[fun ω => Real.exp (c * X ω) | m]) ω ∂μ ≤
      ∫ _ω in A, Real.exp (c ^ 2 * σ ^ 2 / 2) ∂μ :=
    setIntegral_mono_on_ae integrable_condExp.integrableOn (integrable_const _).integrableOn
      hA0 ((hce c).mono fun ω h _ => h)
  rw [setIntegral_const, smul_eq_mul] at h3
  rw [h1, ← h2]
  calc ENNReal.ofReal (∫ ω in A, (μ[fun ω => Real.exp (c * X ω) | m]) ω ∂μ)
      ≤ ENNReal.ofReal (μ.real A * Real.exp (c ^ 2 * σ ^ 2 / 2)) := ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)) * μ A := by
        rw [mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ A)]

/-- Mathlib's conditional sub-Gaussian moment generating function bound with variance
proxy `c` implies `CondSubG` with `σ = √c`. -/
theorem CondSubG.of_hasCondSubgaussianMGF [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {X : Ω → ℝ} {c : NNReal}
    (h : ProbabilityTheory.HasCondSubgaussianMGF m hm X c μ) :
    CondSubG μ m X (Real.sqrt c) := by
  refine CondSubG.of_condExp hm (fun t => h.integrable_exp_mul t) (fun t => ?_)
  filter_upwards [h.ae_condExp_le t] with ω hω
  rw [Real.sq_sqrt c.coe_nonneg]
  refine hω.trans (le_of_eq ?_)
  congr 1
  ring

/-- Deterministic coefficient: `E[exp (c X - c² σ² / 2) 1_A] ≤ P(A)`. -/
lemma CondSubG.setLIntegral_le {m : MeasurableSpace Ω} {X : Ω → ℝ} {σ : ℝ}
    (h : CondSubG μ m X σ) (c : ℝ) {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, ENNReal.ofReal (expFac σ c (X ω)) ∂μ ≤ μ A := by
  have hE : ∀ ω, ENNReal.ofReal (expFac σ c (X ω)) =
      ENNReal.ofReal (Real.exp (c * X ω)) *
        ENNReal.ofReal (Real.exp (-(c ^ 2 * σ ^ 2 / 2))) := fun ω => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, expFac, sub_eq_add_neg]
  simp_rw [hE]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc (∫⁻ ω in A, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ) *
        ENNReal.ofReal (Real.exp (-(c ^ 2 * σ ^ 2 / 2)))
      ≤ ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)) * μ A *
        ENNReal.ofReal (Real.exp (-(c ^ 2 * σ ^ 2 / 2))) := by
        gcongr
        exact h c A hA
    _ = μ A := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- **Random coefficient.**  If `X` is conditionally `σ`-sub-Gaussian given `m` and `C`
is `m`-measurable, then `E[exp (C X - C² σ² / 2) 1_A] ≤ P(A)` for `A ∈ m`.  Proved by
discretizing `C` on dyadic grids and Fatou's lemma. -/
theorem CondSubG.setLIntegral_le_of_measurable {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {X : Ω → ℝ} {σ : ℝ} (h : CondSubG μ m X σ) (hX : Measurable[m0] X) {C : Ω → ℝ}
    (hC : Measurable[m] C) {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, ENNReal.ofReal (expFac σ (C ω) (X ω)) ∂μ ≤ μ A := by
  have hC0 : Measurable[m0] C := hC.mono hm le_rfl
  set Ck : ℕ → Ω → ℝ := fun k ω => (⌊C ω * 2 ^ k⌋ : ℝ) / 2 ^ k with hCk
  set F : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (expFac σ (Ck k ω) (X ω)) with hF
  have hCkm : ∀ k, Measurable[m0] (Ck k) := fun k => measurable_dyadic hC0 k
  have hFm : ∀ k, Measurable[m0] (F k) := fun k => measurable_ofReal_expFac σ (hCkm k) hX
  -- each discretization satisfies the bound
  have hk : ∀ k, ∫⁻ ω in A, F k ω ∂μ ≤ μ A := by
    intro k
    set B : ℤ → Set Ω := fun j => A ∩ (fun ω => ⌊C ω * 2 ^ k⌋) ⁻¹' {j} with hB
    have hBm : ∀ j, MeasurableSet[m] (B j) := fun j =>
      hA.inter ((hC.mul_const _).floor (measurableSet_singleton j))
    have hdisj : Pairwise (Function.onFun Disjoint B) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨_, h1⟩ ⟨_, h2⟩
      have h1' : ⌊C ω * 2 ^ k⌋ = i := h1
      have h2' : ⌊C ω * 2 ^ k⌋ = j := h2
      exact hij (h1'.symm.trans h2')
    have hU : ⋃ j, B j = A := by
      ext ω
      simp [hB]
    have hAμ : ∑' j, μ (B j) = μ A := by
      rw [← measure_iUnion hdisj (fun j => hm _ (hBm j)), hU]
    calc ∫⁻ ω in A, F k ω ∂μ = ∫⁻ ω in ⋃ j, B j, F k ω ∂μ := by rw [hU]
      _ = ∑' j, ∫⁻ ω in B j, F k ω ∂μ := lintegral_iUnion (fun j => hm _ (hBm j)) hdisj _
      _ ≤ ∑' j, μ (B j) := by
          refine tsum_le_tsum fun j => ?_
          have hcongr : ∫⁻ ω in B j, F k ω ∂μ =
              ∫⁻ ω in B j, ENNReal.ofReal (expFac σ ((j : ℝ) / 2 ^ k) (X ω)) ∂μ := by
            refine setLIntegral_congr_fun (hm _ (hBm j)) fun ω hω => ?_
            have hj : ⌊C ω * 2 ^ k⌋ = j := hω.2
            simp only [hF, hCk, hj]
          rw [hcongr]
          exact h.setLIntegral_le _ (hBm j)
      _ = μ A := hAμ
  -- the discretizations converge
  have hCklim : ∀ ω, Tendsto (fun k => Ck k ω) atTop (𝓝 (C ω)) := by
    intro ω
    have hlow : Tendsto (fun k : ℕ => C ω - (1 / 2 : ℝ) ^ k) atTop (𝓝 (C ω - 0)) :=
      tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    rw [sub_zero] at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun k => ?_) (fun k => ?_)
    · have h2 : (0 : ℝ) < 2 ^ k := by positivity
      have h1 := Int.lt_floor_add_one (C ω * 2 ^ k)
      show C ω - (1 / 2 : ℝ) ^ k ≤ (⌊C ω * 2 ^ k⌋ : ℝ) / 2 ^ k
      rw [le_div_iff₀ h2, sub_mul, one_div, inv_pow, inv_mul_cancel₀ h2.ne']
      linarith
    · have h2 : (0 : ℝ) < 2 ^ k := by positivity
      show (⌊C ω * 2 ^ k⌋ : ℝ) / 2 ^ k ≤ C ω
      rw [div_le_iff₀ h2]
      exact Int.floor_le _
  have hlim : ∀ ω, Tendsto (fun k => F k ω) atTop
      (𝓝 (ENNReal.ofReal (expFac σ (C ω) (X ω)))) := by
    intro ω
    have hcont : Continuous fun c : ℝ => ENNReal.ofReal (expFac σ c (X ω)) := by
      refine ENNReal.continuous_ofReal.comp ?_
      unfold expFac
      fun_prop
    exact (hcont.tendsto (C ω)).comp (hCklim ω)
  calc ∫⁻ ω in A, ENNReal.ofReal (expFac σ (C ω) (X ω)) ∂μ
      = ∫⁻ ω in A, liminf (fun k => F k ω) atTop ∂μ :=
        lintegral_congr fun ω => (hlim ω).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ ω in A, F k ω ∂μ) atTop := lintegral_liminf_le hFm
    _ ≤ liminf (fun _ : ℕ => μ A) atTop := liminf_le_liminf (Eventually.of_forall hk)
    _ = μ A := liminf_const _

/-- A function whose integral over every `m`-measurable set is at most the measure of the
set can be integrated against any nonnegative `m`-measurable weight. -/
lemma lintegral_mul_le_of_setLIntegral_le {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {f : Ω → ℝ≥0∞} (hf : Measurable[m0] f)
    (h : ∀ A, MeasurableSet[m] A → ∫⁻ ω in A, f ω ∂μ ≤ μ A) {G : Ω → ℝ≥0∞}
    (hG : Measurable[m] G) : ∫⁻ ω, G ω * f ω ∂μ ≤ ∫⁻ ω, G ω ∂μ := by
  have hle : (μ.withDensity f).trim hm ≤ μ.trim hm := by
    rw [Measure.le_iff]
    intro s hs
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs,
      withDensity_apply _ (hm s hs)]
    exact h s hs
  calc ∫⁻ ω, G ω * f ω ∂μ = ∫⁻ ω, G ω ∂(μ.withDensity f) := by
        rw [lintegral_withDensity_eq_lintegral_mul μ hf (hG.mono hm le_rfl)]
        simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ ω, G ω ∂((μ.withDensity f).trim hm) := (lintegral_trim hm hG).symm
    _ ≤ ∫⁻ ω, G ω ∂(μ.trim hm) := lintegral_mono' hle le_rfl
    _ = ∫⁻ ω, G ω ∂μ := lintegral_trim hm hG

/-- Weighted form of `CondSubG.setLIntegral_le_of_measurable`. -/
theorem CondSubG.lintegral_mul_expFac_le {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {X : Ω → ℝ} {σ : ℝ} (h : CondSubG μ m X σ) (hX : Measurable[m0] X) {C : Ω → ℝ}
    (hC : Measurable[m] C) {G : Ω → ℝ≥0∞} (hG : Measurable[m] G) :
    ∫⁻ ω, G ω * ENNReal.ofReal (expFac σ (C ω) (X ω)) ∂μ ≤ ∫⁻ ω, G ω ∂μ := by
  exact lintegral_mul_le_of_setLIntegral_le hm
    (measurable_ofReal_expFac σ (hC.mono hm le_rfl) hX)
    (fun A hA => h.setLIntegral_le_of_measurable hm hX hC hA) hG

/-- Noise that is independent of `m` and has a `σ`-sub-Gaussian moment generating function
is conditionally `σ`-sub-Gaussian given `m`. -/
theorem CondSubG.of_indep {m : MeasurableSpace Ω} (hm : m ≤ m0) {X : Ω → ℝ} {σ : ℝ}
    (hX : Measurable[m0] X)
    (hind : ProbabilityTheory.Indep
      (MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)) m μ)
    (hmgf : ∀ c : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2))) :
    CondSubG μ m X σ := by
  intro c A hA
  have hA0 : MeasurableSet[m0] A := hm A hA
  have hle : MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ) ≤ m0 := hX.comap_le
  have hIS : ProbabilityTheory.IndepSets
      {s | MeasurableSet[MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)] s} {A} μ :=
    ProbabilityTheory.indepSets_of_indepSets_of_le_right
      ((ProbabilityTheory.Indep_iff_IndepSets _ _ μ).mp hind) (Set.singleton_subset_iff.mpr hA)
  have hreal : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (c * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hf : Measurable[MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)]
      fun ω => ENNReal.ofReal (Real.exp (c * X ω)) := hreal.comp (comap_measurable X)
  have h := ProbabilityTheory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
    hle 1 hA0 hIS hf
  rw [lintegral_indicator_const hA0, one_mul] at h
  calc ∫⁻ ω in A, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (c * X ω)) * A.indicator (fun _ => 1) ω ∂μ := by
        rw [← lintegral_indicator hA0]
        refine lintegral_congr fun ω => ?_
        by_cases hω : ω ∈ A <;> simp [hω]
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ) * μ A := h
    _ ≤ ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)) * μ A := mul_le_mul' (hmgf c) le_rfl

/-- The moment generating function of a centred Gaussian variable, as a lower integral. -/
lemma lintegral_exp_of_map_gaussian {X : Ω → ℝ} {v : NNReal} (hX : Measurable X)
    (hlaw : μ.map X = ProbabilityTheory.gaussianReal 0 v) (c : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ =
      ENNReal.ofReal (Real.exp (c ^ 2 * Real.sqrt v ^ 2 / 2)) := by
  have hreal : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (c * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (c * X ω)) ∂μ =
      ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂(ProbabilityTheory.gaussianReal 0 v) := by
    rw [← hlaw, lintegral_map hreal hX]
  have hint := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v) c
  have h2 : ∫ x, Real.exp (c * x) ∂(ProbabilityTheory.gaussianReal 0 v) =
      Real.exp (0 * c + v * c ^ 2 / 2) :=
    ProbabilityTheory.mgf_gaussianReal (X := id) (μ := 0) (v := v)
      (p := ProbabilityTheory.gaussianReal 0 v) ⟨aemeasurable_id, Measure.map_id⟩ c
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le),
    h2, Real.sq_sqrt v.coe_nonneg]
  congr 2
  ring

/-- Gaussian noise `N(0, v)` independent of `m` is conditionally `√v`-sub-Gaussian given
`m`. -/
theorem CondSubG.of_indep_gaussian {X : Ω → ℝ} {v : NNReal} (hX : Measurable X)
    (hlaw : μ.map X = ProbabilityTheory.gaussianReal 0 v) {m : MeasurableSpace Ω}
    (hm : m ≤ m0)
    (hind : ProbabilityTheory.Indep
      (MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)) m μ) :
    CondSubG μ m X (Real.sqrt v) :=
  CondSubG.of_indep hm hX hind (fun c => le_of_eq (lintegral_exp_of_map_gaussian hX hlaw c))

end CondSubG

/-! ### One-dimensional Gaussian mixing -/

section Gauss

/-- `∫ exp (-b z² + B z + D) dz = √(π / b) exp (B² / (4 b) + D)` for `b > 0`. -/
lemma integral_exp_quadratic {b : ℝ} (hb : 0 < b) (B D : ℝ) :
    Integrable (fun z : ℝ => Real.exp (-b * z ^ 2 + B * z + D)) ∧
      ∫ z : ℝ, Real.exp (-b * z ^ 2 + B * z + D) =
        Real.sqrt (Real.pi / b) * Real.exp (B ^ 2 / (4 * b) + D) := by
  have hfun : (fun z : ℝ => Real.exp (-b * z ^ 2 + B * z + D)) =
      fun z : ℝ => Real.exp (-b * (z - B / (2 * b)) ^ 2) * Real.exp (B ^ 2 / (4 * b) + D) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hint : Integrable (fun z : ℝ => Real.exp (-b * (z - B / (2 * b)) ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).comp_sub_right (B / (2 * b))
  have hI : Integrable (fun z : ℝ =>
      Real.exp (-b * (z - B / (2 * b)) ^ 2) * Real.exp (B ^ 2 / (4 * b) + D)) :=
    hint.mul_const _
  have hsub := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun z : ℝ => Real.exp (-b * z ^ 2)) (B / (2 * b))
  have hv : ∫ z : ℝ, Real.exp (-b * (z - B / (2 * b)) ^ 2) * Real.exp (B ^ 2 / (4 * b) + D) =
      Real.sqrt (Real.pi / b) * Real.exp (B ^ 2 / (4 * b) + D) := by
    rw [integral_mul_const, hsub, integral_gaussian]
  exact ⟨(congrArg (fun f : ℝ → ℝ => Integrable f) hfun).mpr hI,
    (congrArg (fun f : ℝ → ℝ => ∫ z : ℝ, f z) hfun).trans hv⟩

/-- The standard Gaussian density. -/
noncomputable def stdGauss (z : ℝ) : ℝ := Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi)

lemma stdGauss_nonneg (z : ℝ) : 0 ≤ stdGauss z := by
  unfold stdGauss
  positivity

lemma measurable_stdGauss : Measurable stdGauss := by
  have h : Continuous fun z : ℝ => Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
    fun_prop
  exact h.measurable

/-- The coefficient `c(z) = (a / σ + √w z) / σ` of the one-step mixture. -/
noncomputable def mixCoef (σ a w z : ℝ) : ℝ := (a / σ + Real.sqrt w * z) / σ

lemma measurable_mixCoef {α : Type*} {mα : MeasurableSpace α} (σ : ℝ) {a w z : α → ℝ}
    (ha : Measurable a) (hw : Measurable w) (hz : Measurable z) :
    Measurable fun p => mixCoef σ (a p) (w p) (z p) := by
  unfold mixCoef
  exact ((ha.div_const σ).add ((Real.continuous_sqrt.measurable.comp hw).mul hz)).div_const σ

/-- The one-step factor of the mixture supermartingale:
`(1 + w)^{-1/2} exp ((w x² + 2 a x - a²) / (2 σ² (1 + w)))`. -/
noncomputable def mixStep (σ a w x : ℝ) : ℝ :=
  (Real.sqrt (1 + w))⁻¹ * Real.exp ((w * x ^ 2 + 2 * a * x - a ^ 2) / (2 * σ ^ 2 * (1 + w)))

lemma mixStep_nonneg (σ a w x : ℝ) : 0 ≤ mixStep σ a w x := by
  unfold mixStep
  positivity

/-- **Gaussian mixing integral in closed form.**  Mixing the exponential factors
`exp (c x - c² σ² / 2)` over `c = (a / σ + √w z) / σ`, `z ∼ N(0, 1)`, gives `mixStep`. -/
theorem gauss_mix_real {σ : ℝ} (hσ : 0 < σ) {w : ℝ} (hw : 0 ≤ w) (a x : ℝ) :
    Integrable (fun z : ℝ => expFac σ (mixCoef σ a w z) x * stdGauss z) ∧
      ∫ z : ℝ, expFac σ (mixCoef σ a w z) x * stdGauss z = mixStep σ a w x := by
  have hs : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw
  have hσ0 : σ ≠ 0 := hσ.ne'
  have h1w : (1 + w) ≠ 0 := by positivity
  have hb : 0 < (1 + w) / 2 := by positivity
  obtain ⟨hI, hval⟩ := integral_exp_quadratic hb (Real.sqrt w * (x / σ - a / σ))
    (a / σ * (x / σ) - (a / σ) ^ 2 / 2)
  have hfun : (fun z : ℝ => expFac σ (mixCoef σ a w z) x * stdGauss z) =
      fun z : ℝ => Real.exp (-((1 + w) / 2) * z ^ 2 + Real.sqrt w * (x / σ - a / σ) * z +
        (a / σ * (x / σ) - (a / σ) ^ 2 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ := by
    funext z
    unfold expFac mixCoef stdGauss
    rw [div_eq_mul_inv (Real.exp _), ← mul_assoc, ← Real.exp_add]
    congr 2
    have h1 : ((a / σ + Real.sqrt w * z) / σ) ^ 2 * σ ^ 2 / 2 =
        (a / σ + Real.sqrt w * z) ^ 2 / 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hσ0)]
    rw [h1]
    linear_combination (-(z ^ 2 / 2)) * hs
  have hexp : (Real.sqrt w * (x / σ - a / σ)) ^ 2 / (4 * ((1 + w) / 2)) +
      (a / σ * (x / σ) - (a / σ) ^ 2 / 2) =
      (w * x ^ 2 + 2 * a * x - a ^ 2) / (2 * σ ^ 2 * (1 + w)) := by
    rw [mul_pow, hs]
    field_simp
    ring
  have hsq : Real.sqrt (Real.pi / ((1 + w) / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ =
      (Real.sqrt (1 + w))⁻¹ := by
    have h2 : Real.pi / ((1 + w) / 2) = (2 * Real.pi) * (1 + w)⁻¹ := by
      field_simp
    have h3 : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    rw [h2, Real.sqrt_mul (by positivity), Real.sqrt_inv, mul_right_comm, mul_inv_cancel₀ h3,
      one_mul]
  have hI' : Integrable (fun z : ℝ =>
      Real.exp (-((1 + w) / 2) * z ^ 2 + Real.sqrt w * (x / σ - a / σ) * z +
        (a / σ * (x / σ) - (a / σ) ^ 2 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹) :=
    hI.mul_const _
  have hv : ∫ z : ℝ, Real.exp (-((1 + w) / 2) * z ^ 2 + Real.sqrt w * (x / σ - a / σ) * z +
        (a / σ * (x / σ) - (a / σ) ^ 2 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ =
      mixStep σ a w x := by
    rw [integral_mul_const, hval, hexp, mul_right_comm, hsq]
    rfl
  exact ⟨(congrArg (fun f : ℝ → ℝ => Integrable f) hfun).mpr hI',
    (congrArg (fun f : ℝ → ℝ => ∫ z : ℝ, f z) hfun).trans hv⟩

theorem gauss_mix_lintegral {σ : ℝ} (hσ : 0 < σ) {w : ℝ} (hw : 0 ≤ w) (a x : ℝ) :
    ∫⁻ z : ℝ, ENNReal.ofReal (expFac σ (mixCoef σ a w z) x) * ENNReal.ofReal (stdGauss z) =
      ENNReal.ofReal (mixStep σ a w x) := by
  obtain ⟨hI, hval⟩ := gauss_mix_real hσ hw a x
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun z => mul_nonneg (expFac_pos _ _ _).le (stdGauss_nonneg z))]
  exact lintegral_congr fun z => (ENNReal.ofReal_mul (expFac_pos _ _ _).le).symm

lemma lintegral_stdGauss : ∫⁻ z : ℝ, ENNReal.ofReal (stdGauss z) = 1 := by
  have h := gauss_mix_lintegral one_pos (le_refl (0 : ℝ)) 0 0
  simpa [expFac, mixCoef, mixStep] using h

end Gauss

/-! ### The one-step mixture inequality -/

section MixStep

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Tonelli: the weighted integral of the one-step factor is the Gaussian mixture of the
weighted integrals of the exponential factors. -/
lemma lintegral_mul_mixStep_eq [SFinite μ] {σ : ℝ} (hσ : 0 < σ) {X a w : Ω → ℝ}
    (hX : Measurable X) (ha : Measurable a) (hw : Measurable w) (hw0 : ∀ ω, 0 ≤ w ω)
    {G : Ω → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, G ω * ENNReal.ofReal (mixStep σ (a ω) (w ω) (X ω)) ∂μ =
      ∫⁻ z : ℝ, ENNReal.ofReal (stdGauss z) *
        ∫⁻ ω, G ω * ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) ∂μ := by
  have hEg : ∀ ω, Measurable fun z : ℝ =>
      ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) * ENNReal.ofReal (stdGauss z) :=
    fun ω => (measurable_ofReal_expFac σ
      (measurable_mixCoef σ measurable_const measurable_const measurable_id)
      measurable_const).mul (ENNReal.measurable_ofReal.comp measurable_stdGauss)
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (z : ℝ) =>
      G ω * (ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) *
        ENNReal.ofReal (stdGauss z))) :=
    (hG.comp measurable_fst).mul ((measurable_ofReal_expFac σ
      (measurable_mixCoef σ (ha.comp measurable_fst) (hw.comp measurable_fst) measurable_snd)
      (hX.comp measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp (measurable_stdGauss.comp measurable_snd)))
  calc ∫⁻ ω, G ω * ENNReal.ofReal (mixStep σ (a ω) (w ω) (X ω)) ∂μ
      = ∫⁻ ω, (∫⁻ z : ℝ, G ω * (ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) *
          ENNReal.ofReal (stdGauss z))) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [lintegral_const_mul _ (hEg ω), gauss_mix_lintegral hσ (hw0 ω)]
    _ = ∫⁻ z : ℝ, (∫⁻ ω, G ω * (ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) *
          ENNReal.ofReal (stdGauss z)) ∂μ) := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ z : ℝ, ENNReal.ofReal (stdGauss z) *
          ∫⁻ ω, G ω * ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) ∂μ := by
        refine lintegral_congr fun z => ?_
        have hmz : Measurable fun ω =>
            G ω * ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) :=
          hG.mul (measurable_ofReal_expFac σ (measurable_mixCoef σ ha hw measurable_const) hX)
        rw [← lintegral_const_mul _ hmz]
        refine lintegral_congr fun ω => ?_
        ring

/-- **One-step mixture inequality.**  If `X` is conditionally `σ`-sub-Gaussian given `m`
and `a`, `w ≥ 0`, `G ≥ 0` are `m`-measurable, then
`E[G · mixStep σ a w X] ≤ E[G]`. -/
theorem CondSubG.lintegral_mul_mixStep_le [SFinite μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {X : Ω → ℝ} {σ : ℝ} (hσ : 0 < σ) (h : CondSubG μ m X σ) (hX : Measurable[m0] X)
    {a w : Ω → ℝ} (ha : Measurable[m] a) (hw : Measurable[m] w) (hw0 : ∀ ω, 0 ≤ w ω)
    {G : Ω → ℝ≥0∞} (hG : Measurable[m] G) :
    ∫⁻ ω, G ω * ENNReal.ofReal (mixStep σ (a ω) (w ω) (X ω)) ∂μ ≤ ∫⁻ ω, G ω ∂μ := by
  rw [lintegral_mul_mixStep_eq hσ hX (ha.mono hm le_rfl) (hw.mono hm le_rfl) hw0
    (hG.mono hm le_rfl)]
  calc ∫⁻ z : ℝ, ENNReal.ofReal (stdGauss z) *
        ∫⁻ ω, G ω * ENNReal.ofReal (expFac σ (mixCoef σ (a ω) (w ω) z) (X ω)) ∂μ
      ≤ ∫⁻ z : ℝ, ENNReal.ofReal (stdGauss z) * ∫⁻ ω, G ω ∂μ := by
        refine lintegral_mono fun z => ?_
        exact mul_le_mul' le_rfl
          (h.lintegral_mul_expFac_le hm hX (measurable_mixCoef σ ha hw measurable_const) hG)
    _ = ∫⁻ ω, G ω ∂μ := by
        have hg : Measurable[borel ℝ] fun z : ℝ => ENNReal.ofReal (stdGauss z) :=
          ENNReal.measurable_ofReal.comp measurable_stdGauss
        rw [lintegral_mul_const _ hg, lintegral_stdGauss, one_mul]

/-- A nonnegative adapted process with `f (t + 1) = f t · K t`, whose factors satisfy
`E[G · K t] ≤ E[G]` for every nonnegative `ℱ t`-measurable weight `G`, is a
supermartingale. -/
theorem supermartingale_of_lintegral_mul_step [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0}
    {f K : ℕ → Ω → ℝ} (hnn : ∀ t ω, 0 ≤ f t ω) (hmeas : ∀ t, Measurable[ℱ t] (f t))
    (h0 : Integrable (f 0) μ) (hrec : ∀ t ω, f (t + 1) ω = f t ω * K t ω)
    (hstep : ∀ t (G : Ω → ℝ≥0∞), Measurable[ℱ t] G →
      ∫⁻ ω, G ω * ENNReal.ofReal (K t ω) ∂μ ≤ ∫⁻ ω, G ω ∂μ) :
    Supermartingale f ℱ μ := by
  have hset : ∀ t A, MeasurableSet[ℱ t] A →
      ∫⁻ ω in A, ENNReal.ofReal (f (t + 1) ω) ∂μ ≤ ∫⁻ ω in A, ENNReal.ofReal (f t ω) ∂μ := by
    intro t A hA
    have hA0 : MeasurableSet A := ℱ.le t A hA
    have h := hstep t _ (measurable_indicator_ofReal (hmeas t) hA)
    rw [lintegral_indicator hA0] at h
    refine le_trans (le_of_eq ?_) h
    rw [← lintegral_indicator hA0]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hrec, ENNReal.ofReal_mul (hnn t ω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  have hfin : ∀ t, ∫⁻ ω, ENNReal.ofReal (f t ω) ∂μ < ∞ := by
    intro t
    induction t with
    | zero => exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (hnn 0))).mp h0.2
    | succ t ih =>
      have h := hset t Set.univ MeasurableSet.univ
      rw [Measure.restrict_univ] at h
      exact h.trans_lt ih
  have hint : ∀ t, Integrable (f t) μ := fun t =>
    ⟨((hmeas t).mono (ℱ.le t) le_rfl).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (hnn t))).mpr (hfin t)⟩
  refine supermartingale_of_setIntegral_succ_le
    (fun t => stronglyMeasurable_of_measurable_real (hmeas t)) hint fun t A hA => ?_
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn (t + 1)))
      (hint (t + 1)).aestronglyMeasurable.restrict,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn t))
      (hint t).aestronglyMeasurable.restrict]
  exact ENNReal.toReal_mono
    (ne_of_lt ((setLIntegral_le_lintegral _ _).trans_lt (hfin t))) (hset t A hA)

/-! ### (a) The fixed-`λ` exponential supermartingale -/

variable {n : Type*} [Fintype n]

/-- `M_t^λ = exp (∑_{s<t} (η_s ⟨λ, φ_s⟩ / σ - ½ ⟨λ, φ_s⟩²))`. -/
noncomputable def expMart (σ : ℝ) (v : n → ℝ) (η : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  Real.exp (∑ s ∈ range t, (η s ω * (v ⬝ᵥ φ s ω) / σ - (v ⬝ᵥ φ s ω) ^ 2 / 2))

/-- **The fixed-`λ` exponential process is a nonnegative supermartingale.**  `φ s` is
`ℱ s`-measurable (predictable features), `η s` is `ℱ (s + 1)`-measurable and conditionally
`σ`-sub-Gaussian given `ℱ s`. -/
theorem expMart_supermartingale [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {σ : ℝ}
    (hσ : 0 < σ) (v : n → ℝ) {η : ℕ → Ω → ℝ} {φ : ℕ → Ω → n → ℝ}
    (hφ : ∀ s, Measurable[ℱ s] (φ s)) (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    Supermartingale (expMart σ v η φ) ℱ μ := by
  refine supermartingale_of_lintegral_mul_step
    (K := fun t ω => expFac σ (v ⬝ᵥ φ t ω / σ) (η t ω)) (fun t ω => (Real.exp_pos _).le)
    (fun t => ?_) ?_ (fun t ω => ?_) (fun t G hG => ?_)
  · exact measurable_exp_sum_aux
      (fun s hs => (hη s).mono (ℱ.mono (Nat.succ_le_of_lt hs)) le_rfl)
      (fun s hs => measurable_dotProduct measurable_const
        ((hφ s).mono (ℱ.mono (Nat.le_of_lt hs)) le_rfl)) σ
  · have h1 : expMart σ v η φ 0 = fun _ => 1 := by
      funext ω
      simp [expMart]
    rw [h1]
    exact integrable_const _
  · have h1 : η t ω * (v ⬝ᵥ φ t ω) / σ - (v ⬝ᵥ φ t ω) ^ 2 / 2 =
        v ⬝ᵥ φ t ω / σ * η t ω - (v ⬝ᵥ φ t ω / σ) ^ 2 * σ ^ 2 / 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hσ.ne')]
      ring
    unfold expMart expFac
    rw [sum_range_succ, Real.exp_add, h1]
  · exact (hsub t).lintegral_mul_expFac_le (ℱ.le t) ((hη t).mono (ℱ.le _) le_rfl)
      (measurable_div_const_real (measurable_dotProduct measurable_const (hφ t)) σ) hG

end MixStep

/-! ### Rank-one updates of the `V⁻¹` quadratic form -/

section LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma Coercive.det_pos {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam) :
    0 < V.det := by
  have h1 := (hV.isUnit_det hlam).ne_zero
  have hH : V.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hV.symm
  have h2 := (PosSemidef.of_dotProduct_mulVec_nonneg hH
    (fun x => by simpa using hV.psd hlam x)).det_nonneg
  exact lt_of_le_of_ne h2 (Ne.symm h1)

/-- **Rank-one update of the self-normalized quadratic form** (Sherman--Morrison):
with `w = ‖φ‖²_{V⁻¹}` and `a = φᵀ V⁻¹ S`,
`‖S + x φ‖²_{(V + φ φᵀ)⁻¹} = ‖S‖²_{V⁻¹} + (w x² + 2 a x - a²) / (1 + w)`. -/
theorem Coercive.qinv_rank_one_update {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam)
    (hlam : 0 < lam) (φ S : n → ℝ) (x : ℝ) :
    qinv (V + vecMulVec φ φ) (S + x • φ) = qinv V S +
      (qinv V φ * x ^ 2 + 2 * (φ ⬝ᵥ V⁻¹ *ᵥ S) * x - (φ ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) /
        (1 + qinv V φ) := by
  have hw0 : 0 ≤ qinv V φ := hV.qinv_nonneg hlam φ
  obtain ⟨w, hw⟩ : ∃ w, qinv V φ = w := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, φ ⬝ᵥ V⁻¹ *ᵥ S = a := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, qinv V S = q := ⟨_, rfl⟩
  have hw' : φ ⬝ᵥ V⁻¹ *ᵥ φ = w := hw
  have hq' : S ⬝ᵥ V⁻¹ *ᵥ S = q := hq
  have ha' : S ⬝ᵥ V⁻¹ *ᵥ φ = a := (dotProduct_mulVec_symm hV.inv_symm φ S).trans ha
  rw [hw] at hw0 ⊢
  rw [ha, hq]
  have h1w : (1 + w) ≠ 0 := by positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (a + x * w) / (1 + w) := ⟨_, rfl⟩
  have hκ' : a + x * w - κ * w = κ := by
    rw [hκ]
    field_simp
    ring
  have hy : (V + vecMulVec φ φ) *ᵥ (V⁻¹ *ᵥ (S + x • φ) - κ • (V⁻¹ *ᵥ φ)) = S + x • φ := by
    have e1 : φ ⬝ᵥ (V⁻¹ *ᵥ (S + x • φ) - κ • (V⁻¹ *ᵥ φ)) = κ := by
      rw [dotProduct_sub, dotProduct_smul, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, ha, hw', smul_eq_mul, smul_eq_mul]
      exact hκ'
    rw [add_mulVec, vecMulVec_self_mulVec, e1, mulVec_sub, mulVec_smul,
      hV.mul_inv_mulVec hlam, hV.mul_inv_mulVec hlam]
    abel
  have hinv : (V + vecMulVec φ φ)⁻¹ *ᵥ (S + x • φ) =
      V⁻¹ *ᵥ (S + x • φ) - κ • (V⁻¹ *ᵥ φ) := by
    conv_lhs => rw [← hy]
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((hV.rank_one φ).isUnit_det hlam), one_mulVec]
  unfold qinv
  rw [hinv]
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, dotProduct_sub, smul_eq_mul, hq', ha', ha, hw']
  rw [hκ]
  field_simp
  ring

lemma measurable_det_matrix : Measurable (fun M : Matrix n n ℝ => M.det) :=
  (continuous_id.matrix_det).measurable

lemma measurable_inv_matrix : Measurable (fun M : Matrix n n ℝ => M⁻¹) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun M : Matrix n n ℝ => M⁻¹ i j) = fun M => (M.det)⁻¹ * M.adjugate i j := by
    funext M
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  change Measurable fun M : Matrix n n ℝ => M⁻¹ i j
  rw [h]
  exact (measurable_det_matrix.inv).mul ((continuous_id.matrix_adjugate).measurable.eval_matrix)

end LinAlg

/-! ### The mixture supermartingale and the self-normalized bound -/

section SelfNormalized

variable {n : Type*} [Fintype n] [DecidableEq n] {Ω : Type*}

/-- `V_t = V_0 + ∑_{s<t} φ_s φ_sᵀ`. -/
noncomputable def snDesign (V0 : Matrix n n ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    Matrix n n ℝ :=
  V0 + ∑ s ∈ range t, vecMulVec (φ s ω) (φ s ω)

/-- `S_t = S_0 + ∑_{s<t} η_s φ_s`. -/
noncomputable def snSum (S0 : n → ℝ) (η : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    n → ℝ :=
  S0 + ∑ s ∈ range t, η s ω • φ s ω

/-- The closed-form Gaussian mixture
`(det V_0 / det V_t)^{1/2} exp ((‖S_t‖²_{V_t⁻¹} - ‖S_0‖²_{V_0⁻¹}) / (2 σ²))`. -/
noncomputable def snMix (σ : ℝ) (V0 : Matrix n n ℝ) (S0 : n → ℝ) (η : ℕ → Ω → ℝ)
    (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (V0.det / (snDesign V0 φ t ω).det) *
    Real.exp ((qinv (snDesign V0 φ t ω) (snSum S0 η φ t ω) - qinv V0 S0) / (2 * σ ^ 2))

omit [Fintype n] [DecidableEq n] in
lemma snDesign_succ (V0 : Matrix n n ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    snDesign V0 φ (t + 1) ω = snDesign V0 φ t ω + vecMulVec (φ t ω) (φ t ω) := by
  unfold snDesign
  rw [sum_range_succ, add_assoc]

omit [Fintype n] [DecidableEq n] in
lemma snSum_succ (S0 : n → ℝ) (η : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    snSum S0 η φ (t + 1) ω = snSum S0 η φ t ω + η t ω • φ t ω := by
  unfold snSum
  rw [sum_range_succ, add_assoc]

lemma snDesign_coercive {V0 : Matrix n n ℝ} {lam : ℝ} (hV0 : Coercive V0 lam)
    (φ : ℕ → Ω → n → ℝ) (ω : Ω) : ∀ t, Coercive (snDesign V0 φ t ω) lam
  | 0 => by simpa [snDesign] using hV0
  | t + 1 => by
    rw [snDesign_succ]
    exact (snDesign_coercive hV0 φ ω t).rank_one _

lemma snMix_nonneg (σ : ℝ) (V0 : Matrix n n ℝ) (S0 : n → ℝ) (η : ℕ → Ω → ℝ)
    (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) : 0 ≤ snMix σ V0 S0 η φ t ω :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

lemma snMix_zero {V0 : Matrix n n ℝ} {lam : ℝ} (hV0 : Coercive V0 lam) (hlam : 0 < lam)
    (σ : ℝ) (S0 : n → ℝ) (η : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (ω : Ω) :
    snMix σ V0 S0 η φ 0 ω = 1 := by
  have h := (hV0.det_pos hlam).ne'
  simp [snMix, snDesign, snSum, h]

/-- One step of the mixture: `M_{t+1} = M_t · mixStep σ a_t w_t η_t` with
`a_t = φ_tᵀ V_t⁻¹ S_t` and `w_t = ‖φ_t‖²_{V_t⁻¹}`. -/
lemma snMix_succ {σ lam : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) {V0 : Matrix n n ℝ}
    (hV0 : Coercive V0 lam) (S0 : n → ℝ) (η : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    snMix σ V0 S0 η φ (t + 1) ω = snMix σ V0 S0 η φ t ω *
      mixStep σ (φ t ω ⬝ᵥ (snDesign V0 φ t ω)⁻¹ *ᵥ snSum S0 η φ t ω)
        (qinv (snDesign V0 φ t ω) (φ t ω)) (η t ω) := by
  have hV := snDesign_coercive hV0 φ ω t
  have hw0 := hV.qinv_nonneg hlam (φ t ω)
  have hd := hV.det_pos hlam
  have hd0 := hV0.det_pos hlam
  unfold snMix mixStep
  rw [snDesign_succ, snSum_succ, hV.det_rank_one hlam, hV.qinv_rank_one_update hlam]
  generalize qinv (snDesign V0 φ t ω) (φ t ω) = w at hw0 ⊢
  generalize φ t ω ⬝ᵥ (snDesign V0 φ t ω)⁻¹ *ᵥ snSum S0 η φ t ω = a
  generalize qinv (snDesign V0 φ t ω) (snSum S0 η φ t ω) = q
  generalize (snDesign V0 φ t ω).det = d at hd ⊢
  generalize V0.det = d0 at hd0 ⊢
  generalize qinv V0 S0 = q0
  generalize η t ω = x
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hd' : d ≠ 0 := hd.ne'
  have h1w : (1 + w) ≠ 0 := by positivity
  have h1 : Real.sqrt (d0 / (d * (1 + w))) = Real.sqrt (d0 / d) * (Real.sqrt (1 + w))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have h2 : (q + (w * x ^ 2 + 2 * a * x - a ^ 2) / (1 + w) - q0) / (2 * σ ^ 2) =
      (q - q0) / (2 * σ ^ 2) + (w * x ^ 2 + 2 * a * x - a ^ 2) / (2 * σ ^ 2 * (1 + w)) := by
    field_simp
    ring
  rw [h1, h2, Real.exp_add]
  ring

section Measurability

variable {mΩ : MeasurableSpace Ω}

omit [Fintype n] [DecidableEq n] in
lemma measurable_snDesign (V0 : Matrix n n ℝ) {φ : ℕ → Ω → n → ℝ} {t : ℕ}
    (hφ : ∀ s < t, Measurable (φ s)) : Measurable (snDesign V0 φ t) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [snDesign, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply]
  exact measurable_const.add (Finset.measurable_sum _ fun s hs =>
    ((measurable_pi_apply i).comp (hφ s (mem_range.mp hs))).mul
      ((measurable_pi_apply j).comp (hφ s (mem_range.mp hs))))

omit [Fintype n] [DecidableEq n] in
lemma measurable_snSum (S0 : n → ℝ) {η : ℕ → Ω → ℝ} {φ : ℕ → Ω → n → ℝ} {t : ℕ}
    (hη : ∀ s < t, Measurable (η s)) (hφ : ∀ s < t, Measurable (φ s)) :
    Measurable (snSum S0 η φ t) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [snSum, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact measurable_const.add (Finset.measurable_sum _ fun s hs =>
    (hη s (mem_range.mp hs)).mul ((measurable_pi_apply i).comp (hφ s (mem_range.mp hs))))

omit [DecidableEq n] in
lemma measurable_qform {x y : Ω → n → ℝ} {P : Ω → Matrix n n ℝ} (hx : Measurable x)
    (hP : Measurable P) (hy : Measurable y) : Measurable fun ω => x ω ⬝ᵥ P ω *ᵥ y ω := by
  refine measurable_dotProduct hx (measurable_pi_iff.mpr fun i => ?_)
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    hP.eval_matrix.mul ((measurable_pi_apply j).comp hy)

lemma measurable_snMix (σ : ℝ) (V0 : Matrix n n ℝ) (S0 : n → ℝ) {η : ℕ → Ω → ℝ}
    {φ : ℕ → Ω → n → ℝ} {t : ℕ} (hη : ∀ s < t, Measurable (η s))
    (hφ : ∀ s < t, Measurable (φ s)) : Measurable (snMix σ V0 S0 η φ t) := by
  have hV := measurable_snDesign V0 hφ
  have hS := measurable_snSum S0 hη hφ
  have hq : Measurable fun ω => qinv (snDesign V0 φ t ω) (snSum S0 η φ t ω) :=
    measurable_qform hS (measurable_inv_matrix.comp hV) hS
  have hd : Measurable fun ω => (snDesign V0 φ t ω).det := measurable_det_matrix.comp hV
  exact (Real.continuous_sqrt.measurable.comp (measurable_const.div hd)).mul
    (Real.measurable_exp.comp ((hq.sub measurable_const).div_const _))

end Measurability

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The Gaussian mixture is a nonnegative supermartingale, in any finite dimension.**

`φ s` is `ℱ s`-measurable (predictable features), `η s` is `ℱ (s + 1)`-measurable and
conditionally `σ`-sub-Gaussian given `ℱ s`, `V_0` is a fixed symmetric positive definite
matrix (`Coercive V0 lam`, `lam > 0`) and `S_0` a fixed vector.  Then
`(det V_0 / det V_t)^{1/2} exp ((‖S_t‖²_{V_t⁻¹} - ‖S_0‖²_{V_0⁻¹}) / (2 σ²))` is a
supermartingale with initial value `1`. -/
theorem snMix_supermartingale [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {σ lam : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lam) {V0 : Matrix n n ℝ} (hV0 : Coercive V0 lam) (S0 : n → ℝ)
    {η : ℕ → Ω → ℝ} {φ : ℕ → Ω → n → ℝ} (hφ : ∀ s, Measurable[ℱ s] (φ s))
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    Supermartingale (snMix σ V0 S0 η φ) ℱ μ := by
  have hφt : ∀ t, ∀ s < t, Measurable[ℱ t] (φ s) := fun t s hs =>
    (hφ s).mono (ℱ.mono hs.le) le_rfl
  have hηt : ∀ t, ∀ s < t, Measurable[ℱ t] (η s) := fun t s hs =>
    (hη s).mono (ℱ.mono (Nat.succ_le_of_lt hs)) le_rfl
  refine supermartingale_of_lintegral_mul_step
    (K := fun t ω => mixStep σ (φ t ω ⬝ᵥ (snDesign V0 φ t ω)⁻¹ *ᵥ snSum S0 η φ t ω)
      (qinv (snDesign V0 φ t ω) (φ t ω)) (η t ω))
    (fun t ω => snMix_nonneg σ V0 S0 η φ t ω)
    (fun t => measurable_snMix σ V0 S0 (hηt t) (hφt t)) ?_
    (fun t ω => snMix_succ hσ hlam hV0 S0 η φ t ω) (fun t G hG => ?_)
  · have h1 : snMix σ V0 S0 η φ 0 = fun _ => 1 := funext fun ω => snMix_zero hV0 hlam σ S0 η φ ω
    rw [h1]
    exact integrable_const _
  · exact (hsub t).lintegral_mul_mixStep_le (ℱ.le t) hσ ((hη t).mono (ℱ.le _) le_rfl)
      (measurable_qform (hφ t) (measurable_inv_matrix.comp (measurable_snDesign V0 (hφt t)))
        (measurable_snSum S0 (hηt t) (hφt t)))
      (measurable_qform (hφ t) (measurable_inv_matrix.comp (measurable_snDesign V0 (hφt t)))
        (hφ t))
      (fun ω => (snDesign_coercive hV0 φ ω t).qinv_nonneg hlam _) hG

/-- **Self-normalized bound for vector-valued martingales** (Abbasi-Yadkori, Pal and
Szepesvari 2011, Theorem 1), time-uniform form.  With probability at least `1 - δ`, for
all `t`,
`‖S_t‖²_{V_t⁻¹} - ‖S_0‖²_{V_0⁻¹} < σ² (2 log (1 / δ) + log (det V_t / det V_0))`. -/
theorem self_normalized_bound [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {σ lam δ : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lam) (hδ : 0 < δ) {V0 : Matrix n n ℝ} (hV0 : Coercive V0 lam)
    (S0 : n → ℝ) {η : ℕ → Ω → ℝ} {φ : ℕ → Ω → n → ℝ} (hφ : ∀ s, Measurable[ℱ s] (φ s))
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    μ {ω | ∃ t, σ ^ 2 * (2 * Real.log (1 / δ) +
          Real.log ((snDesign V0 φ t ω).det / V0.det)) ≤
        qinv (snDesign V0 φ t ω) (snSum S0 η φ t ω) - qinv V0 S0} ≤ ENNReal.ofReal δ := by
  have hM := snMix_supermartingale ℱ hσ hlam hV0 S0 hφ hη hsub
  have h0 : ∫ ω, snMix σ V0 S0 η φ 0 ω ∂μ ≤ 1 := by
    have h1 : snMix σ V0 S0 η φ 0 = fun _ => 1 := funext fun ω => snMix_zero hV0 hlam σ S0 η φ ω
    rw [h1]
    simp
  have hville := ville_test hM (fun t ω => snMix_nonneg σ V0 S0 η φ t ω) h0 (c := 1 / δ)
    (by positivity)
  rw [one_div_one_div] at hville
  refine (measure_mono ?_).trans hville
  rintro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hd := (snDesign_coercive hV0 φ ω t).det_pos hlam
  have hd0 := hV0.det_pos hlam
  have hr : 0 < V0.det / (snDesign V0 φ t ω).det := div_pos hd0 hd
  have hlog : Real.log (V0.det / (snDesign V0 φ t ω).det) =
      -Real.log ((snDesign V0 φ t ω).det / V0.det) := by
    rw [← Real.log_inv, inv_div]
  have hsqrt : Real.sqrt (V0.det / (snDesign V0 φ t ω).det) =
      Real.exp (Real.log (V0.det / (snDesign V0 φ t ω).det) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
    congr 1
    ring
  have hσ2 : 0 < 2 * σ ^ 2 := by positivity
  have hkey : Real.log (1 / δ) + Real.log ((snDesign V0 φ t ω).det / V0.det) / 2 ≤
      (qinv (snDesign V0 φ t ω) (snSum S0 η φ t ω) - qinv V0 S0) / (2 * σ ^ 2) := by
    rw [le_div_iff₀ hσ2]
    have e : (Real.log (1 / δ) + Real.log ((snDesign V0 φ t ω).det / V0.det) / 2) *
        (2 * σ ^ 2) = σ ^ 2 * (2 * Real.log (1 / δ) +
          Real.log ((snDesign V0 φ t ω).det / V0.det)) := by ring
    rw [e]
    exact ht
  show 1 / δ ≤ snMix σ V0 S0 η φ t ω
  unfold snMix
  rw [hsqrt, ← Real.exp_add, hlog]
  calc 1 / δ = Real.exp (Real.log (1 / δ)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end SelfNormalized

/-! ### The ridge radius `eq:ay-radius` and Proposition `thm:t3-misspec` -/

section Ridge

variable {n : Type*} [Fintype n] [DecidableEq n] {Ω : Type*}

omit [Fintype n] in
lemma ridgeDesign_fin_eq (lam : ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    ridgeDesign lam (fun s : Fin t => φ s ω) = snDesign (lam • (1 : Matrix n n ℝ)) φ t ω := by
  unfold ridgeDesign snDesign
  rw [Fin.sum_univ_eq_sum_range (fun s => vecMulVec (φ s ω) (φ s ω)) t]

omit [Fintype n] [DecidableEq n] in
lemma sum_fin_eq_snSum (η : ℕ → Ω → ℝ) (φ : ℕ → Ω → n → ℝ) (t : ℕ) (ω : Ω) :
    ∑ s : Fin t, η s ω • φ s ω = snSum 0 η φ t ω := by
  unfold snSum
  rw [zero_add, Fin.sum_univ_eq_sum_range (fun s => η s ω • φ s ω) t]

omit [Fintype n] in
/-- The design matrices of `CDJoint.lean` along a random query sequence are the matrices
`snDesign`. -/
lemma design_eq_snDesign {X : Type*} (lam : ℝ) (φ : X → n → ℝ) (x : ℕ → Ω → X) (ω : Ω) :
    ∀ t, design lam φ (fun s => x s ω) t =
      snDesign (lam • (1 : Matrix n n ℝ)) (fun s ω => φ (x s ω)) t ω
  | 0 => by simp [design, snDesign]
  | t + 1 => by
    rw [snDesign_succ, ← design_eq_snDesign lam φ x ω t]
    rfl

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Self-normalized bound, ridge form** (the term `σ √(2 log (1/δ) + log (det V_t / λ^d))`
of `eq:ay-radius` and `eq:t3-misspec-radius`).  With `V_t = λ I + ∑_{s<t} φ_s φ_sᵀ`,
with probability at least `1 - δ`, for all `t`,
`‖∑_{s<t} η_s φ_s‖_{V_t⁻¹} ≤ σ √(2 log (1 / δ) + log (det V_t / λ^d))`.
This is the hypothesis `hsn` of `misspec_radius`, with `ι = Fin t`. -/
theorem self_normalized_ridge [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {σ lam δ : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lam) (hδ : 0 < δ) {η : ℕ → Ω → ℝ} {φ : ℕ → Ω → n → ℝ}
    (hφ : ∀ s, Measurable[ℱ s] (φ s)) (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    μ {ω | ∃ t : ℕ, σ * Real.sqrt (2 * Real.log (1 / δ) +
          Real.log ((ridgeDesign lam (fun s : Fin t => φ s ω)).det / lam ^ Fintype.card n)) <
        Real.sqrt (qinv (ridgeDesign lam (fun s : Fin t => φ s ω))
          (∑ s : Fin t, η s ω • φ s ω))} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (self_normalized_bound ℱ hσ hlam hδ
    (coercive_smul_one (n := n) (lam := lam)) 0 hφ hη hsub)
  rintro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ridgeDesign_fin_eq, sum_fin_eq_snSum] at ht
  have hdet0 : (lam • (1 : Matrix n n ℝ)).det = lam ^ Fintype.card n := by
    rw [det_smul, det_one, mul_one]
  have hq0 : qinv (lam • (1 : Matrix n n ℝ)) 0 = 0 := by simp [qinv]
  show σ ^ 2 * (2 * Real.log (1 / δ) +
      Real.log ((snDesign (lam • (1 : Matrix n n ℝ)) φ t ω).det /
        (lam • (1 : Matrix n n ℝ)).det)) ≤
    qinv (snDesign (lam • (1 : Matrix n n ℝ)) φ t ω) (snSum 0 η φ t ω) -
      qinv (lam • (1 : Matrix n n ℝ)) 0
  rw [hq0, sub_zero, hdet0]
  generalize 2 * Real.log (1 / δ) +
    Real.log ((snDesign (lam • (1 : Matrix n n ℝ)) φ t ω).det / lam ^ Fintype.card n) = X
    at ht ⊢
  generalize qinv (snDesign (lam • (1 : Matrix n n ℝ)) φ t ω) (snSum 0 η φ t ω) = q at ht ⊢
  by_contra hcon
  have h1 := Real.sqrt_le_sqrt (not_le.mp hcon).le
  rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le] at h1
  linarith

/-- **Proposition `thm:t3-misspec`, time-uniform radius with its probability.**
Observations `Y_s - m₀ = φ_s · θ* + b_s + η_s` with predictable features `φ_s` (inclusion
indicators are absorbed into `φ_s`), `|b_s| ≤ ξ`, `‖θ*‖ ≤ B` and conditionally
`σ`-sub-Gaussian `η_s`.  With probability at least `1 - δ`, for all `t`, the ridge
estimator `θ̂_t = V_t⁻¹ ∑_{s<t} (Y_s - m₀) φ_s` satisfies
`‖θ̂_t - θ*‖_{V_t} ≤ √λ B + σ √(2 log (1/δ) + log (det V_t / λ^d)) + ξ √t`.
This combines `misspec_radius` with `self_normalized_ridge`; no hypothesis stands for the
self-normalized bound. -/
theorem misspec_radius_whp [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {σ lam δ ξ B : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lam) (hδ : 0 < δ) (hB : 0 ≤ B) (hξ : 0 ≤ ξ) {η : ℕ → Ω → ℝ}
    {φ : ℕ → Ω → n → ℝ} (bias : ℕ → Ω → ℝ) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hbias : ∀ s ω, |bias s ω| ≤ ξ) (hφ : ∀ s, Measurable[ℱ s] (φ s))
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    μ {ω | ∃ t : ℕ, Real.sqrt lam * B + σ * Real.sqrt (2 * Real.log (1 / δ) +
          Real.log ((ridgeDesign lam (fun s : Fin t => φ s ω)).det / lam ^ Fintype.card n)) +
          ξ * Real.sqrt t <
        Real.sqrt (((ridgeDesign lam (fun s : Fin t => φ s ω))⁻¹ *ᵥ
            (∑ s : Fin t, (φ s ω ⬝ᵥ θs + bias s ω + η s ω) • φ s ω) - θs) ⬝ᵥ
          ridgeDesign lam (fun s : Fin t => φ s ω) *ᵥ
            ((ridgeDesign lam (fun s : Fin t => φ s ω))⁻¹ *ᵥ
              (∑ s : Fin t, (φ s ω ⬝ᵥ θs + bias s ω + η s ω) • φ s ω) - θs))} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (self_normalized_ridge ℱ hσ hlam hδ hφ hη hsub)
  rintro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  by_contra hcon
  have h := misspec_radius hlam hB hξ (fun s : Fin t => φ s ω) (fun s : Fin t => bias s ω)
    (fun s : Fin t => η s ω) θs hθ (fun s => hbias s ω) (not_lt.mp hcon)
  rw [Fintype.card_fin] at h
  exact absurd ht (not_lt.mpr h)

/-- **The self-normalized ridge radius `eq:ay-radius` is anytime valid** (the radius
assumed by Theorem `thm:t4-finite-sample`).  In the well-specified model
`Y_s - m₀ = φ_s · θ* + η_s` with `‖θ*‖ ≤ B`, with probability at least `1 - δ`, for all
`t`, `‖θ̂_t - θ*‖_{V_t} ≤ √λ B + σ √(2 log (1/δ) + log (det V_t / λ^d))`. -/
theorem ay_radius_whp [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {σ lam δ B : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lam) (hδ : 0 < δ) (hB : 0 ≤ B) {η : ℕ → Ω → ℝ}
    {φ : ℕ → Ω → n → ℝ} (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hφ : ∀ s, Measurable[ℱ s] (φ s))
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    μ {ω | ∃ t : ℕ, Real.sqrt lam * B + σ * Real.sqrt (2 * Real.log (1 / δ) +
          Real.log ((ridgeDesign lam (fun s : Fin t => φ s ω)).det / lam ^ Fintype.card n)) <
        Real.sqrt (((ridgeDesign lam (fun s : Fin t => φ s ω))⁻¹ *ᵥ
            (∑ s : Fin t, (φ s ω ⬝ᵥ θs + η s ω) • φ s ω) - θs) ⬝ᵥ
          ridgeDesign lam (fun s : Fin t => φ s ω) *ᵥ
            ((ridgeDesign lam (fun s : Fin t => φ s ω))⁻¹ *ᵥ
              (∑ s : Fin t, (φ s ω ⬝ᵥ θs + η s ω) • φ s ω) - θs))} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (misspec_radius_whp ℱ hσ hlam hδ hB (le_refl (0 : ℝ))
    (fun _ _ => 0) θs hθ (fun _ _ => by simp) hφ hη hsub)
  rintro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  simpa only [add_zero, zero_mul] using ht

end Ridge

/-! ### The mixture supermartingale of Lemma `lem:bay-cs` -/

section BayCS

variable {n : Type*} [Fintype n] [DecidableEq n] {Ω : Type*}

/-- `b_t = ∑_{s<t} Y_s u_s` with observations `Y_s = u_s · θ + ν_s`. -/
noncomputable def bayB (u : ℕ → Ω → n → ℝ) (ν : ℕ → Ω → ℝ) (θ : n → ℝ) (t : ℕ) (ω : Ω) :
    n → ℝ :=
  ∑ s ∈ range t, (u s ω ⬝ᵥ θ + ν s ω) • u s ω

/-- **Closed form of the mixture martingale of Lemma `lem:bay-cs`.**  With
`G_t = ∑_{s<t} u_s u_sᵀ`, `b_t = ∑_{s<t} Y_s u_s`, `Y_s = u_s · θ + ν_s`, the mixture
`snMix` with unit noise scale, `V_0 = γ I` and `S_0 = -γ θ` equals
`exp (-½ log det (I + G_t / γ) + ½ b_tᵀ (G_t + γ I)⁻¹ b_t - θᵀ b_t + ½ θᵀ G_t θ)`,
for every `t` (whether or not `G_t` is invertible). -/
theorem snMix_bay_form {γ : ℝ} (hγ : 0 < γ) (u : ℕ → Ω → n → ℝ) (ν : ℕ → Ω → ℝ) (θ : n → ℝ)
    (t : ℕ) (ω : Ω) :
    snMix 1 (γ • (1 : Matrix n n ℝ)) (-(γ • θ)) ν u t ω =
      Real.exp (-(1 / 2) * Real.log (1 + γ⁻¹ • gram (fun s => u s ω) t).det +
        1 / 2 * qinv (gram (fun s => u s ω) t + γ • (1 : Matrix n n ℝ)) (bayB u ν θ t ω) -
        θ ⬝ᵥ bayB u ν θ t ω + 1 / 2 * (θ ⬝ᵥ gram (fun s => u s ω) t *ᵥ θ)) := by
  obtain ⟨G, hG⟩ : ∃ G, gram (fun s => u s ω) t = G := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, bayB u ν θ t ω = b := ⟨_, rfl⟩
  rw [hG, hb]
  have hVG : snDesign (γ • (1 : Matrix n n ℝ)) u t ω = G + γ • (1 : Matrix n n ℝ) := by
    rw [← hG]
    unfold snDesign gram
    exact add_comm _ _
  have hV : Coercive (G + γ • (1 : Matrix n n ℝ)) γ := by
    rw [← hVG]
    exact snDesign_coercive coercive_smul_one u ω t
  have hGθ : G *ᵥ θ = ∑ s ∈ range t, (u s ω ⬝ᵥ θ) • u s ω := by
    rw [← hG]
    unfold gram
    rw [sum_mulVec]
    exact sum_congr rfl fun s _ => vecMulVec_self_mulVec _ _
  have hS : snSum (-(γ • θ)) ν u t ω = b - (G + γ • (1 : Matrix n n ℝ)) *ᵥ θ := by
    rw [← hb, add_mulVec, smul_mulVec, one_mulVec, hGθ]
    unfold snSum bayB
    simp only [add_smul, sum_add_distrib]
    abel
  have hunit := hV.isUnit_det hγ
  have hq : qinv (G + γ • (1 : Matrix n n ℝ)) (b - (G + γ • (1 : Matrix n n ℝ)) *ᵥ θ) =
      qinv (G + γ • (1 : Matrix n n ℝ)) b - 2 * (θ ⬝ᵥ b) +
        θ ⬝ᵥ (G + γ • (1 : Matrix n n ℝ)) *ᵥ θ := by
    have e1 : (G + γ • (1 : Matrix n n ℝ))⁻¹ *ᵥ ((G + γ • (1 : Matrix n n ℝ)) *ᵥ θ) = θ := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, one_mulVec]
    have e2 : ((G + γ • (1 : Matrix n n ℝ)) *ᵥ θ) ⬝ᵥ (G + γ • (1 : Matrix n n ℝ))⁻¹ *ᵥ b =
        θ ⬝ᵥ b := by
      rw [dotProduct_mulVec_symm hV.inv_symm b, e1, dotProduct_comm]
    unfold qinv
    rw [mulVec_sub, e1, sub_dotProduct, dotProduct_sub, dotProduct_sub, e2,
      dotProduct_comm b θ, dotProduct_comm ((G + γ • (1 : Matrix n n ℝ)) *ᵥ θ) θ]
    ring
  have hθV : θ ⬝ᵥ (G + γ • (1 : Matrix n n ℝ)) *ᵥ θ = θ ⬝ᵥ G *ᵥ θ + γ * (θ ⬝ᵥ θ) := by
    rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hq0 : qinv (γ • (1 : Matrix n n ℝ)) (-(γ • θ)) = γ * (θ ⬝ᵥ θ) := by
    have e0 : (γ • (1 : Matrix n n ℝ)) *ᵥ (-θ) = -(γ • θ) := by
      rw [smul_mulVec, one_mulVec, smul_neg]
    have e1 : (γ • (1 : Matrix n n ℝ))⁻¹ *ᵥ (-(γ • θ)) = -θ := by
      rw [← e0, mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((coercive_smul_one (n := n)).isUnit_det hγ), one_mulVec]
    unfold qinv
    rw [e1, neg_dotProduct_neg, smul_dotProduct, smul_eq_mul]
  have hdet0 : (γ • (1 : Matrix n n ℝ)).det = γ ^ Fintype.card n := by
    rw [det_smul, det_one, mul_one]
  have hdet : (1 + γ⁻¹ • G).det =
      (G + γ • (1 : Matrix n n ℝ)).det / (γ • (1 : Matrix n n ℝ)).det := by
    have e : 1 + γ⁻¹ • G = γ⁻¹ • (G + γ • (1 : Matrix n n ℝ)) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul, add_comm]
    rw [e, det_smul, hdet0, inv_pow, div_eq_inv_mul]
  have hx : 0 < (1 + γ⁻¹ • G).det := by
    rw [hdet, hdet0]
    exact div_pos (hV.det_pos hγ) (by positivity)
  have hratio : (γ • (1 : Matrix n n ℝ)).det / (G + γ • (1 : Matrix n n ℝ)).det =
      ((1 + γ⁻¹ • G).det)⁻¹ := by
    rw [hdet, inv_div]
  unfold snMix
  rw [hVG, hS, hq, hq0, hθV, hratio, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (inv_pos.mpr hx),
    Real.log_inv, ← Real.exp_add]
  congr 1
  ring

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Full-domain confidence sequence (Lemma `lem:bay-cs`), coverage, with the mixture
supermartingale proved.**  Observations `Y_s = u_s · θ + ν_s` with predictable `u_s` and
innovations `ν_s` that are conditionally `1`-sub-Gaussian given `ℱ s` (in particular
conditionally `N(0, 1)`); `G_t = ∑_{s<t} u_s u_sᵀ`, `b_t = ∑_{s<t} Y_s u_s`.  The fixed
parameter `θ` leaves `C_t(δ)` at some time with invertible `G_t` with probability at most
`δ`.  The hypotheses `hM`, `hnn`, `h0`, `hform` of `bay_cs_coverage` are discharged by
`snMix_supermartingale` and `snMix_bay_form`. -/
theorem bay_cs_coverage_subgaussian [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) {u : ℕ → Ω → n → ℝ} {ν : ℕ → Ω → ℝ} (θ : n → ℝ)
    (hu : ∀ s, Measurable[ℱ s] (u s)) (hν : ∀ s, Measurable[ℱ (s + 1)] (ν s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (ν s) 1) :
    μ {ω | ∃ t, (∃ lam, 0 < lam ∧ Coercive (gram (fun s => u s ω) t) lam) ∧
        mixThreshold δ γ (gram (fun s => u s ω) t) (bayB u ν θ t ω) <
          1 / 2 * ((θ - (gram (fun s => u s ω) t)⁻¹ *ᵥ bayB u ν θ t ω) ⬝ᵥ
            gram (fun s => u s ω) t *ᵥ
              (θ - (gram (fun s => u s ω) t)⁻¹ *ᵥ bayB u ν θ t ω))} ≤
      ENNReal.ofReal δ := by
  have h0 : ∫ ω, snMix 1 (γ • (1 : Matrix n n ℝ)) (-(γ • θ)) ν u 0 ω ∂μ ≤ 1 := by
    have h1 : snMix 1 (γ • (1 : Matrix n n ℝ)) (-(γ • θ)) ν u 0 = fun _ => 1 :=
      funext fun ω => snMix_zero coercive_smul_one hγ 1 _ ν u ω
    rw [h1]
    simp
  exact bay_cs_coverage hδ (fun t ω => gram (fun s => u s ω) t) (bayB u ν θ) θ
    (snMix 1 (γ • (1 : Matrix n n ℝ)) (-(γ • θ)) ν u)
    (snMix_supermartingale ℱ one_pos hγ coercive_smul_one _ hu hν hsub)
    (fun t ω => snMix_nonneg _ _ _ _ _ t ω) h0
    (fun t ω _ => snMix_bay_form hγ u ν θ t ω)

end BayCS

/-! ### (b) The one-dimensional case -/

section Scalar

/-- **Gaussian mixing integral in closed form, scalar features.**  For scalar features
the fixed-`λ` process is `M_t^λ = exp (∑_{s<t} (η_s λ φ_s / σ - ½ (λ φ_s)²))`, and its
mixture over `λ ∼ N(0, 1 / v₀)` is
`(v₀ / V_t)^{1/2} exp (S_t² / (2 σ² V_t))` with `V_t = v₀ + ∑ φ_s²`, `S_t = ∑ η_s φ_s`. -/
theorem scalar_mixture_closed_form {σ v0 : ℝ} (hσ : 0 < σ) (hv0 : 0 < v0) (η φ : ℕ → ℝ)
    (t : ℕ) :
    ∫ l : ℝ, Real.exp (∑ s ∈ range t, (η s * (l * φ s) / σ - (l * φ s) ^ 2 / 2)) *
        (Real.sqrt (v0 / (2 * Real.pi)) * Real.exp (-(v0 * l ^ 2) / 2)) =
      Real.sqrt (v0 / (v0 + ∑ s ∈ range t, φ s ^ 2)) *
        Real.exp ((∑ s ∈ range t, η s * φ s) ^ 2 /
          (2 * σ ^ 2 * (v0 + ∑ s ∈ range t, φ s ^ 2))) := by
  have hsum : ∀ l : ℝ, ∑ s ∈ range t, (η s * (l * φ s) / σ - (l * φ s) ^ 2 / 2) =
      l * (∑ s ∈ range t, η s * φ s) / σ - l ^ 2 * (∑ s ∈ range t, φ s ^ 2) / 2 := by
    intro l
    rw [sum_sub_distrib, mul_sum, mul_sum, sum_div, sum_div]
    congr 1 <;> exact sum_congr rfl fun s _ => by ring
  have hP0 : 0 ≤ ∑ s ∈ range t, φ s ^ 2 := sum_nonneg fun s _ => sq_nonneg _
  generalize ∑ s ∈ range t, η s * φ s = S at hsum ⊢
  generalize ∑ s ∈ range t, φ s ^ 2 = P at hsum hP0 ⊢
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hvP : v0 + P ≠ 0 := by positivity
  have hb : 0 < (v0 + P) / 2 := by positivity
  obtain ⟨-, hval⟩ := integral_exp_quadratic hb (S / σ) 0
  have hfun : (fun l : ℝ =>
      Real.exp (∑ s ∈ range t, (η s * (l * φ s) / σ - (l * φ s) ^ 2 / 2)) *
        (Real.sqrt (v0 / (2 * Real.pi)) * Real.exp (-(v0 * l ^ 2) / 2))) =
      fun l : ℝ => Real.exp (-((v0 + P) / 2) * l ^ 2 + S / σ * l + 0) *
        Real.sqrt (v0 / (2 * Real.pi)) := by
    funext l
    rw [hsum, mul_left_comm, ← Real.exp_add, mul_comm]
    congr 2
    ring
  refine (congrArg (fun f : ℝ → ℝ => ∫ l : ℝ, f l) hfun).trans ?_
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have e1 : Real.pi / ((v0 + P) / 2) * (v0 / (2 * Real.pi)) = v0 / (v0 + P) := by
    field_simp
  have e2 : (S / σ) ^ 2 / (4 * ((v0 + P) / 2)) + 0 = S ^ 2 / (2 * σ ^ 2 * (v0 + P)) := by
    field_simp
    ring
  show ∫ l : ℝ, Real.exp (-((v0 + P) / 2) * l ^ 2 + S / σ * l + 0) *
      Real.sqrt (v0 / (2 * Real.pi)) = _
  rw [integral_mul_const, hval, mul_right_comm, ← Real.sqrt_mul (by positivity), e1, e2]

variable {Ω : Type*}

/-- Scalar features as vectors indexed by `Unit`. -/
def liftUnit (φ : ℕ → Ω → ℝ) : ℕ → Ω → Unit → ℝ := fun s ω _ => φ s ω

lemma qinv_unit {V : Matrix Unit Unit ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    (S : Unit → ℝ) : qinv V S = S () ^ 2 / V () () := by
  have hpos : 0 < V () () := by
    have h := hV.det_pos hlam
    rw [Matrix.det_unique] at h
    exact h
  have e : ∀ y : Unit → ℝ, (V *ᵥ y) () = V () () * y () := fun y => by
    show ∑ j, V () j * y j = _
    rw [Fintype.sum_unique]
  have e2 : ∀ x y : Unit → ℝ, x ⬝ᵥ y = x () * y () := fun x y => by
    show ∑ j, x j * y j = _
    rw [Fintype.sum_unique]
  have h := congrFun (hV.mul_inv_mulVec hlam S) ()
  rw [e] at h
  have hq : qinv V S = S () * (V⁻¹ *ᵥ S) () := e2 _ _
  rw [hq, eq_div_iff hpos.ne']
  calc S () * (V⁻¹ *ᵥ S) () * V () () = S () * (V () () * (V⁻¹ *ᵥ S) ()) := by ring
    _ = S () ^ 2 := by rw [h]; ring

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Time-uniform self-normalized bound, scalar features.**  With
`V_t = v₀ + ∑_{s<t} φ_s²` and `S_t = ∑_{s<t} η_s φ_s`, with probability at least `1 - δ`,
for all `t`, `S_t² / V_t < σ² (2 log (1 / δ) + log (V_t / v₀))`. -/
theorem self_normalized_scalar [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {σ v0 δ : ℝ}
    (hσ : 0 < σ) (hv0 : 0 < v0) (hδ : 0 < δ) {η φ : ℕ → Ω → ℝ}
    (hφ : ∀ s, Measurable[ℱ s] (φ s)) (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    μ {ω | ∃ t, σ ^ 2 * (2 * Real.log (1 / δ) +
          Real.log ((v0 + ∑ s ∈ range t, φ s ω ^ 2) / v0)) ≤
        (∑ s ∈ range t, η s ω * φ s ω) ^ 2 / (v0 + ∑ s ∈ range t, φ s ω ^ 2)} ≤
      ENNReal.ofReal δ := by
  have hφ' : ∀ s, Measurable[ℱ s] (liftUnit φ s) := fun s => measurable_unit_pi (hφ s)
  refine (measure_mono ?_).trans (self_normalized_bound ℱ hσ hv0 hδ
    (coercive_smul_one (n := Unit) (lam := v0)) 0 hφ' hη hsub)
  rintro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hV := snDesign_coercive (coercive_smul_one (n := Unit) (lam := v0)) (liftUnit φ) ω t
  have hentry : snDesign (v0 • (1 : Matrix Unit Unit ℝ)) (liftUnit φ) t ω () () =
      v0 + ∑ s ∈ range t, φ s ω ^ 2 := by
    simp only [snDesign, liftUnit, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    congr 1
    exact sum_congr rfl fun s _ => (sq _).symm
  have hdet : (snDesign (v0 • (1 : Matrix Unit Unit ℝ)) (liftUnit φ) t ω).det =
      v0 + ∑ s ∈ range t, φ s ω ^ 2 := by
    rw [Matrix.det_unique]
    exact hentry
  have hdet0 : (v0 • (1 : Matrix Unit Unit ℝ)).det = v0 := by
    rw [det_smul, det_one, mul_one]
    simp
  have hSe : snSum (0 : Unit → ℝ) η (liftUnit φ) t ω () = ∑ s ∈ range t, η s ω * φ s ω := by
    simp [snSum, liftUnit]
  have hq0 : qinv (v0 • (1 : Matrix Unit Unit ℝ)) 0 = 0 := by simp [qinv]
  show σ ^ 2 * (2 * Real.log (1 / δ) +
      Real.log ((snDesign (v0 • (1 : Matrix Unit Unit ℝ)) (liftUnit φ) t ω).det /
        (v0 • (1 : Matrix Unit Unit ℝ)).det)) ≤
    qinv (snDesign (v0 • (1 : Matrix Unit Unit ℝ)) (liftUnit φ) t ω)
      (snSum 0 η (liftUnit φ) t ω) - qinv (v0 • (1 : Matrix Unit Unit ℝ)) 0
  rw [hq0, sub_zero, qinv_unit hV hv0, hSe, hentry, hdet, hdet0]
  exact ht

end Scalar

end JointRootCert
