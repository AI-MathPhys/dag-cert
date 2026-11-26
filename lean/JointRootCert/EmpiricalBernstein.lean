/-
Predictable empirical-Bernstein test supermartingales (Appendix C,
"Predictable empirical-Bernstein confidence sequences", `app:variance-cs`; the
empirical-Bernstein half of Lemma `lem:nested-interval-valid`, "Anytime validity and
nesting of terminal boxes").

Results covered:

* the deterministic exponential inequality of Fan, Grama and Liu,
  `exp (λ ξ - ψ_E(λ) ξ²) ≤ 1 + λ ξ` for `ξ ≥ -1`, `λ ∈ [0,1)` (`fan_log_ineq`,
  `fan_exp_ineq`);
* the one-step bounds for both signs (`eb_step_le`, `eb_condExp_le_one`);
* the supermartingale property of `M_n^±` for arbitrary predictable `μ̂ ∈ [0,1]`,
  `λ ∈ [0,1)` (`ebProc_supermartingale`);
* the manuscript's predictable plug-in estimators `μ̂`, `σ̂²`, `λ` and their ranges and
  predictability (`ebMu`, `ebVar`, `ebLam`, ...);
* coverage of the empirical-Bernstein intervals with no supermartingale hypothesis
  (`eb_coverage_predictable`, and `eb_coverage_iid` for independent observations).
-/
import JointRootCert.Coverage

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### The deterministic inequality -/

/-- `ψ_E(λ) = -log (1 - λ) - λ`. -/
noncomputable def psiE (l : ℝ) : ℝ := -Real.log (1 - l) - l

lemma psiE_nonneg {l : ℝ} (h1 : l < 1) : 0 ≤ psiE l := by
  have := Real.log_le_sub_one_of_pos (x := 1 - l) (by linarith)
  unfold psiE
  linarith

lemma measurable_psiE : Measurable psiE := by
  unfold psiE
  exact ((Real.measurable_log.comp (measurable_const.sub measurable_id)).neg).sub measurable_id

/-- **Fan--Grama--Liu inequality, logarithmic form.**  For `ξ ≥ -1` and `λ ∈ [0,1)`,
`λ ξ - ψ_E(λ) ξ² ≤ log (1 + λ ξ)`. -/
theorem fan_log_ineq {ξ l : ℝ} (hξ : -1 ≤ ξ) (h0 : 0 ≤ l) (h1 : l < 1) :
    l * ξ - psiE l * ξ ^ 2 ≤ Real.log (1 + l * ξ) := by
  set g : ℝ → ℝ := fun t => Real.log (1 + t * ξ) - t * ξ + ξ ^ 2 * (-Real.log (1 - t) - t)
    with hg
  have hpos : ∀ t ∈ Set.Ico (0 : ℝ) 1, 0 < 1 + t * ξ ∧ 0 < 1 - t := by
    intro t ht
    refine ⟨?_, by linarith [ht.2]⟩
    nlinarith [ht.1, ht.2, mul_nonneg ht.1 (by linarith : (0 : ℝ) ≤ ξ + 1)]
  have hder : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivAt g (ξ / (1 + t * ξ) - ξ + ξ ^ 2 * (-(-1 / (1 - t)) - 1)) t := by
    intro t ht
    obtain ⟨hp1, hp2⟩ := hpos t ht
    have e1 : HasDerivAt (fun t : ℝ => 1 + t * ξ) ξ t := by
      simpa using ((hasDerivAt_id t).mul_const ξ).const_add 1
    have e2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have e3 : HasDerivAt (fun t : ℝ => t * ξ) ξ t := by
      simpa using (hasDerivAt_id t).mul_const ξ
    exact ((e1.log hp1.ne').sub e3).add
      ((((e2.log hp2.ne').neg).sub (hasDerivAt_id t)).const_mul (ξ ^ 2))
  have hmono : MonotoneOn g (Set.Ico (0 : ℝ) 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).hasDerivWithinAt) ?_
    intro t ht
    have ht' := interior_subset ht
    obtain ⟨hp1, hp2⟩ := hpos t ht'
    have heq : ξ / (1 + t * ξ) - ξ + ξ ^ 2 * (-(-1 / (1 - t)) - 1) =
        t ^ 2 * ξ ^ 2 * (1 + ξ) * ((1 - t)⁻¹ * (1 + t * ξ)⁻¹) := by
      have e1 : (1 + t * ξ)⁻¹ * (1 + t * ξ) = 1 := inv_mul_cancel₀ hp1.ne'
      have e2 : (1 - t)⁻¹ * (1 - t) = 1 := inv_mul_cancel₀ hp2.ne'
      linear_combination (ξ - ξ ^ 2 * t * (1 - t)⁻¹) * e1 +
        (ξ ^ 2 + ξ ^ 2 * t * (1 + t * ξ)⁻¹) * e2
    rw [heq]
    have : 0 ≤ 1 + ξ := by linarith
    positivity
  have h := hmono (Set.left_mem_Ico.mpr one_pos) ⟨h0, h1⟩ h0
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0] at h
  simp only [hg, psiE] at h ⊢
  linarith

/-- **Fan--Grama--Liu inequality.**  For `ξ ≥ -1` and `λ ∈ [0,1)`,
`exp (λ ξ - ψ_E(λ) ξ²) ≤ 1 + λ ξ`. -/
theorem fan_exp_ineq {ξ l : ℝ} (hξ : -1 ≤ ξ) (h0 : 0 ≤ l) (h1 : l < 1) :
    Real.exp (l * ξ - psiE l * ξ ^ 2) ≤ 1 + l * ξ := by
  have hpos : 0 < 1 + l * ξ := by
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ ξ + 1)]
  calc Real.exp (l * ξ - psiE l * ξ ^ 2) ≤ Real.exp (Real.log (1 + l * ξ)) :=
        Real.exp_le_exp.mpr (fan_log_ineq hξ h0 h1)
    _ = 1 + l * ξ := Real.exp_log hpos

/-! ### One step -/

/-- One multiplicative increment of `M^±`:
`exp (s λ (x - m) - (x - μ̂)² ψ_E(λ))`, with `s = 1` for `M^+` and `s = -1` for `M^-`. -/
noncomputable def ebFac (s m x mh l : ℝ) : ℝ :=
  Real.exp (s * (l * (x - m)) - (x - mh) ^ 2 * psiE l)

lemma ebFac_pos (s m x mh l : ℝ) : 0 < ebFac s m x mh l := Real.exp_pos _

lemma ebFac_le {s m x mh l : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hm : m ∈ Set.Icc (0 : ℝ) 1)
    (h0 : 0 ≤ l) (h1 : l < 1) (hs : s = 1 ∨ s = -1) : ebFac s m x mh l ≤ Real.exp 1 := by
  apply Real.exp_le_exp.mpr
  have hψ := mul_nonneg (sq_nonneg (x - mh)) (psiE_nonneg h1)
  have habs : s * (l * (x - m)) ≤ 1 := by
    rcases hs with rfl | rfl
    · nlinarith [hx.1, hx.2, hm.1, hm.2]
    · nlinarith [hx.1, hx.2, hm.1, hm.2]
  linarith

/-- **Deterministic one-step bound.**  For `x, μ̂ ∈ [0,1]`, `λ ∈ [0,1)` and either sign `s`,
`exp (s λ (x - m) - (x - μ̂)² ψ_E(λ)) ≤ (1 + s λ (x - μ̂)) exp (s λ (μ̂ - m))`. -/
theorem eb_step_le {s m x mh l : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hmh : mh ∈ Set.Icc (0 : ℝ) 1) (h0 : 0 ≤ l) (h1 : l < 1) (hs : s = 1 ∨ s = -1) :
    ebFac s m x mh l ≤ (1 + l * (s * (x - mh))) * Real.exp (s * l * (mh - m)) := by
  have hξ : -1 ≤ s * (x - mh) := by
    rcases hs with rfl | rfl <;> linarith [hx.1, hx.2, hmh.1, hmh.2]
  have hsq : (s * (x - mh)) ^ 2 = (x - mh) ^ 2 := by
    rcases hs with rfl | rfl <;> ring
  have h := fan_exp_ineq hξ h0 h1
  rw [hsq] at h
  have hsplit : ebFac s m x mh l =
      Real.exp (l * (s * (x - mh)) - psiE l * (x - mh) ^ 2) * Real.exp (s * l * (mh - m)) := by
    unfold ebFac
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- `(1 - y) e^y ≤ 1`. -/
lemma one_sub_mul_exp_le_one (y : ℝ) : (1 - y) * Real.exp y ≤ 1 := by
  have h := Real.add_one_le_exp (-y)
  calc (1 - y) * Real.exp y ≤ Real.exp (-y) * Real.exp y :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

section Process

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **One-step conditional-expectation bound.**  `X` is `[0,1]`-valued with conditional
mean `m` given the σ-algebra `𝒢`; `μ̂ ∈ [0,1]` and `λ ∈ [0,1)` are `𝒢`-measurable.  Then
`E[exp (s λ (X - m) - (X - μ̂)² ψ_E(λ)) | 𝒢] ≤ 1` for either sign `s`. -/
theorem eb_condExp_le_one [IsFiniteMeasure μ] {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ m0)
    {X muh lam : Ω → ℝ} {m s : ℝ} (hXm : Measurable[m0] X) (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (hm : m ∈ Set.Icc (0 : ℝ) 1) (hmean : μ[X | 𝒢] =ᵐ[μ] fun _ => m)
    (hmuhm : Measurable[𝒢] muh) (hmuh : ∀ ω, muh ω ∈ Set.Icc (0 : ℝ) 1)
    (hlamm : Measurable[𝒢] lam) (hlam : ∀ ω, lam ω ∈ Set.Ico (0 : ℝ) 1)
    (hs : s = 1 ∨ s = -1) :
    μ[fun ω => ebFac s m (X ω) (muh ω) (lam ω) | 𝒢] ≤ᵐ[μ] fun _ => 1 := by
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hsle : s ≤ 1 ∧ -1 ≤ s := by rcases hs with rfl | rfl <;> constructor <;> norm_num
  -- the exponential weight `E = exp (s λ (μ̂ - m))`, and the affine majorant `A + B X`
  set E : Ω → ℝ := fun ω => Real.exp (s * lam ω * (muh ω - m)) with hE
  set A : Ω → ℝ := fun ω => (1 - lam ω * (s * muh ω)) * E ω with hA
  set B : Ω → ℝ := fun ω => lam ω * s * E ω with hB
  have hEm : Measurable[𝒢] E :=
    (((hlamm.const_mul s).mul (hmuhm.sub_const m))).exp
  have hAm : Measurable[𝒢] A :=
    ((hlamm.mul (hmuhm.const_mul s)).const_sub 1).mul hEm
  have hBm : Measurable[𝒢] B := (hlamm.mul_const s).mul hEm
  have hEb : ∀ ω, 0 < E ω ∧ E ω ≤ Real.exp 1 := by
    intro ω
    refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
    have h1 := (hlam ω).1
    have h2 := (hlam ω).2
    have h3 := hmuh ω
    rcases hs with rfl | rfl
    · nlinarith [h3.1, h3.2, hm.1, hm.2]
    · nlinarith [h3.1, h3.2, hm.1, hm.2]
  have hBb : ∀ ω, |B ω| ≤ Real.exp 1 := by
    intro ω
    have h1 := (hlam ω).1
    have h2 := (hlam ω).2
    obtain ⟨h3, h4⟩ := hEb ω
    simp only [hB]
    rw [abs_mul, abs_mul, hs1, mul_one, abs_of_nonneg h1, abs_of_pos h3]
    nlinarith
  have hXint : Integrable X μ :=
    Integrable.of_mem_Icc 0 1 hXm.aemeasurable (Filter.Eventually.of_forall hX)
  have hAint : Integrable A μ := by
    refine Integrable.of_mem_Icc 0 (2 * Real.exp 1) (hAm.mono h𝒢 le_rfl).aemeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := (hlam ω).1
    have h2 := (hlam ω).2
    have h3 := hmuh ω
    obtain ⟨h4, h5⟩ := hEb ω
    have h6 : 0 ≤ 1 - lam ω * (s * muh ω) ∧ 1 - lam ω * (s * muh ω) ≤ 2 := by
      rcases hs with rfl | rfl
      · constructor <;> nlinarith [h3.1, h3.2]
      · constructor <;> nlinarith [h3.1, h3.2]
    simp only [hA]
    exact ⟨mul_nonneg h6.1 h4.le, by nlinarith⟩
  have hBX : μ[B * X | 𝒢] =ᵐ[μ] B * μ[X | 𝒢] :=
    condExp_stronglyMeasurable_mul_of_bound h𝒢 hBm.stronglyMeasurable hXint (Real.exp 1)
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hBb ω)
  have hBXint : Integrable (B * X) μ := by
    refine Integrable.of_mem_Icc (-Real.exp 1) (Real.exp 1)
      ((hBm.mono h𝒢 le_rfl).mul hXm).aemeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hX ω
    have h2 := abs_le.mp (hBb ω)
    have h3 : |B ω * X ω| ≤ Real.exp 1 := by
      rw [abs_mul, abs_of_nonneg h1.1]
      calc |B ω| * X ω ≤ |B ω| * 1 := mul_le_mul_of_nonneg_left h1.2 (abs_nonneg _)
        _ ≤ Real.exp 1 := by rw [mul_one]; exact hBb ω
    exact abs_le.mp h3
  have hFm : Measurable[m0] fun ω => ebFac s m (X ω) (muh ω) (lam ω) := by
    unfold ebFac
    exact ((((hlamm.mono h𝒢 le_rfl).mul (hXm.sub_const m)).const_mul s).sub
      (((hXm.sub (hmuhm.mono h𝒢 le_rfl)).pow_const 2).mul
        (measurable_psiE.comp (hlamm.mono h𝒢 le_rfl)))).exp
  have hFint : Integrable (fun ω => ebFac s m (X ω) (muh ω) (lam ω)) μ :=
    Integrable.of_mem_Icc 0 (Real.exp 1) hFm.aemeasurable
      (Filter.Eventually.of_forall fun ω =>
        ⟨(ebFac_pos _ _ _ _ _).le, ebFac_le (hX ω) hm (hlam ω).1 (hlam ω).2 hs⟩)
  have hle : (fun ω => ebFac s m (X ω) (muh ω) (lam ω)) ≤ᵐ[μ] A + B * X :=
    Filter.Eventually.of_forall fun ω => by
      have h := eb_step_le (m := m) (hX ω) (hmuh ω) (hlam ω).1 (hlam ω).2 hs
      refine h.trans (le_of_eq ?_)
      simp only [Pi.add_apply, Pi.mul_apply, hA, hB, hE]
      ring
  have hmono := condExp_mono (m := 𝒢) hFint (hAint.add hBXint) hle
  have hadd := condExp_add hAint hBXint 𝒢
  have hAc : μ[A | 𝒢] = A :=
    condExp_of_stronglyMeasurable h𝒢 hAm.stronglyMeasurable hAint
  filter_upwards [hmono, hadd, hBX, hmean] with ω h1 h2 h3 h4
  rw [h2] at h1
  simp only [Pi.add_apply, Pi.mul_apply] at h1 h3
  rw [h3, h4, hAc] at h1
  refine h1.trans ?_
  have h5 := one_sub_mul_exp_le_one (s * lam ω * (muh ω - m))
  have h6 : A ω + B ω * m =
      (1 - s * lam ω * (muh ω - m)) * Real.exp (s * lam ω * (muh ω - m)) := by
    simp only [hA, hB, hE]
    ring
  rw [h6]
  exact h5

/-- The test process
`M_n^s = exp (s ∑_{i<n} λ_i (X_i - m) - ∑_{i<n} (X_i - μ̂_i)² ψ_E(λ_i))`
(`s = 1` gives `M^+`, `s = -1` gives `M^-`).  Observations are indexed from `0`, so `μ̂_i`
and `λ_i` are the quantities computed before observation `X_i`. -/
noncomputable def ebProc (s m : ℝ) (X muh lam : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (s * ∑ i ∈ range n, lam i ω * (X i ω - m) -
    ∑ i ∈ range n, (X i ω - muh i ω) ^ 2 * psiE (lam i ω))

lemma ebProc_zero (s m : ℝ) (X muh lam : ℕ → Ω → ℝ) (ω : Ω) : ebProc s m X muh lam 0 ω = 1 := by
  simp [ebProc]

lemma ebProc_succ (s m : ℝ) (X muh lam : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ebProc s m X muh lam (n + 1) ω =
      ebProc s m X muh lam n ω * ebFac s m (X n ω) (muh n ω) (lam n ω) := by
  unfold ebProc ebFac
  rw [← Real.exp_add, sum_range_succ, sum_range_succ]
  congr 1
  ring

/-- **The empirical-Bernstein test processes are supermartingales.**
`X_i` is `ℱ (i+1)`-measurable, `[0,1]`-valued, with conditional mean `m` given `ℱ i`;
`μ̂_i ∈ [0,1]` and `λ_i ∈ [0,1)` are `ℱ i`-measurable (predictable).  Then, for either sign,
`M_n^s` is a supermartingale, and `M_0^s = 1` (`ebProc_zero`). -/
theorem ebProc_supermartingale [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0}
    {X muh lam : ℕ → Ω → ℝ} {m s : ℝ}
    (hXm : ∀ i, Measurable[ℱ (i + 1)] (X i)) (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hm : m ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ i, μ[X i | ℱ i] =ᵐ[μ] fun _ => m)
    (hmuhm : ∀ i, Measurable[ℱ i] (muh i)) (hmuh : ∀ i ω, muh i ω ∈ Set.Icc (0 : ℝ) 1)
    (hlamm : ∀ i, Measurable[ℱ i] (lam i)) (hlam : ∀ i ω, lam i ω ∈ Set.Ico (0 : ℝ) 1)
    (hs : s = 1 ∨ s = -1) :
    Supermartingale (ebProc s m X muh lam) ℱ μ := by
  have hXn : ∀ i n, i < n → Measurable[ℱ n] (X i) := fun i n hin =>
    (hXm i).mono (ℱ.mono hin) le_rfl
  have hadp : ∀ n, Measurable[ℱ n] (ebProc s m X muh lam n) := by
    intro n
    have h1 : Measurable[ℱ n] fun ω => ∑ i ∈ range n, lam i ω * (X i ω - m) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hin := mem_range.mp hi
      exact ((hlamm i).mono (ℱ.mono hin.le) le_rfl).mul ((hXn i n hin).sub_const m)
    have h2 : Measurable[ℱ n] fun ω =>
        ∑ i ∈ range n, (X i ω - muh i ω) ^ 2 * psiE (lam i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hin := mem_range.mp hi
      exact (((hXn i n hin).sub ((hmuhm i).mono (ℱ.mono hin.le) le_rfl)).pow_const 2).mul
        (measurable_psiE.comp ((hlamm i).mono (ℱ.mono hin.le) le_rfl))
    exact ((h1.const_mul s).sub h2).exp
  have hbd : ∀ n ω, ebProc s m X muh lam n ω ≤ Real.exp 1 ^ n := by
    intro n ω
    induction n with
    | zero => simp [ebProc_zero]
    | succ n ih =>
      rw [ebProc_succ, pow_succ]
      exact mul_le_mul ih (ebFac_le (hX n ω) hm (hlam n ω).1 (hlam n ω).2 hs)
        (ebFac_pos _ _ _ _ _).le (by positivity)
  have hpos : ∀ n ω, 0 < ebProc s m X muh lam n ω := fun n ω => Real.exp_pos _
  have hint : ∀ n, Integrable (ebProc s m X muh lam n) μ := fun n =>
    Integrable.of_mem_Icc 0 (Real.exp 1 ^ n) ((hadp n).mono (ℱ.le n) le_rfl).aemeasurable
      (Filter.Eventually.of_forall fun ω => ⟨(hpos n ω).le, hbd n ω⟩)
  refine supermartingale_nat (fun n => (hadp n).stronglyMeasurable) hint fun n => ?_
  set F : Ω → ℝ := fun ω => ebFac s m (X n ω) (muh n ω) (lam n ω) with hF
  have hsucc : ebProc s m X muh lam (n + 1) = ebProc s m X muh lam n * F := by
    funext ω
    exact ebProc_succ s m X muh lam n ω
  have hFle := eb_condExp_le_one (μ := μ) (ℱ.le n) ((hXm n).mono (ℱ.le (n + 1)) le_rfl)
    (hX n) hm (hmean n) (hmuhm n) (hmuh n) (hlamm n) (hlam n) hs
  have hFint : Integrable F μ := by
    refine Integrable.of_mem_Icc 0 (Real.exp 1) ?_ (Filter.Eventually.of_forall fun ω =>
      ⟨(ebFac_pos _ _ _ _ _).le, ebFac_le (hX n ω) hm (hlam n ω).1 (hlam n ω).2 hs⟩)
    have h1 := (hXm n).mono (ℱ.le (n + 1)) le_rfl
    have h2 := (hmuhm n).mono (ℱ.le n) le_rfl
    have h3 := (hlamm n).mono (ℱ.le n) le_rfl
    simp only [hF, ebFac]
    exact ((((h3.mul (h1.sub_const m)).const_mul s).sub
      (((h1.sub h2).pow_const 2).mul (measurable_psiE.comp h3))).exp).aemeasurable
  have hpull : μ[ebProc s m X muh lam n * F | ℱ n] =ᵐ[μ] ebProc s m X muh lam n * μ[F | ℱ n] :=
    condExp_stronglyMeasurable_mul_of_bound (ℱ.le n) (hadp n).stronglyMeasurable hFint
      (Real.exp 1 ^ n) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hpos n ω)]
        exact hbd n ω)
  rw [hsucc]
  filter_upwards [hpull, hFle] with ω h1 h2
  rw [h1, Pi.mul_apply]
  calc ebProc s m X muh lam n ω * (μ[F | ℱ n]) ω ≤ ebProc s m X muh lam n ω * 1 :=
        mul_le_mul_of_nonneg_left h2 (hpos n ω).le
    _ = ebProc s m X muh lam n ω := mul_one _

/-! ### The manuscript's predictable plug-in estimators -/

/-- `μ̂_{i}` computed before observation `X_i` (0-indexed):
`(1/2 + ∑_{s<i} X_s) / (i + 1)`. -/
noncomputable def ebMu (X : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (1 / 2 + ∑ s ∈ range i, X s ω) / (i + 1)

/-- `σ̂²_{i}` computed before observation `X_i` (0-indexed):
`(1/4 + ∑_{s<i} (X_s - μ̂_s)²) / (i + 1)`. -/
noncomputable def ebVar (X : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (1 / 4 + ∑ s ∈ range i, (X s ω - ebMu X s ω) ^ 2) / (i + 1)

/-- `λ_{i}` used for observation `X_i` (0-indexed), with `L = log (2 M / δ)`:
`min (3/4) √(2 L / (σ̂²_i (i + 1) log (i + 2)))`. -/
noncomputable def ebLam (L : ℝ) (X : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  min (3 / 4) (Real.sqrt (2 * L / (ebVar X i ω * (i + 1) * Real.log (i + 2))))

lemma ebMu_zero (X : ℕ → Ω → ℝ) (ω : Ω) : ebMu X 0 ω = 1 / 2 := by simp [ebMu]

lemma ebMu_mem {X : ℕ → Ω → ℝ} (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) (ω : Ω) :
    ebMu X i ω ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ ∑ s ∈ range i, X s ω := sum_nonneg fun s _ => (hX s ω).1
  have h1 : ∑ s ∈ range i, X s ω ≤ i := by
    calc ∑ s ∈ range i, X s ω ≤ ∑ _s ∈ range i, (1 : ℝ) := sum_le_sum fun s _ => (hX s ω).2
      _ = i := by simp
  have hi : (0 : ℝ) < i + 1 := by positivity
  unfold ebMu
  constructor
  · positivity
  · rw [div_le_one hi]
    linarith

lemma ebVar_pos (X : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : 0 < ebVar X i ω := by
  have h0 : 0 ≤ ∑ s ∈ range i, (X s ω - ebMu X s ω) ^ 2 := sum_nonneg fun s _ => sq_nonneg _
  unfold ebVar
  positivity

/-- `λ_i ∈ (0, 3/4]` when `log (2 M / δ) > 0`. -/
lemma ebLam_mem {L : ℝ} (hL : 0 < L) (X : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) :
    0 < ebLam L X i ω ∧ ebLam L X i ω ≤ 3 / 4 := by
  have hv := ebVar_pos X i ω
  have hlog : 0 < Real.log ((i : ℝ) + 2) := Real.log_pos (by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith)
  have hi : (0 : ℝ) < i + 1 := by positivity
  unfold ebLam
  refine ⟨lt_min (by norm_num) (Real.sqrt_pos.mpr ?_), min_le_left _ _⟩
  positivity

variable {ℱ : Filtration ℕ m0}

lemma measurable_ebMu {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable[ℱ (i + 1)] (X i)) (i : ℕ) :
    Measurable[ℱ i] (ebMu X i) := by
  unfold ebMu
  refine Measurable.div_const (Measurable.const_add ?_ _) _
  refine Finset.measurable_sum _ fun s hs => ?_
  exact (hXm s).mono (ℱ.mono (mem_range.mp hs)) le_rfl

lemma measurable_ebVar {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable[ℱ (i + 1)] (X i)) (i : ℕ) :
    Measurable[ℱ i] (ebVar X i) := by
  unfold ebVar
  refine Measurable.div_const (Measurable.const_add ?_ _) _
  refine Finset.measurable_sum _ fun s hs => ?_
  have hsi := mem_range.mp hs
  exact (((hXm s).mono (ℱ.mono hsi) le_rfl).sub
    ((measurable_ebMu hXm s).mono (ℱ.mono hsi.le) le_rfl)).pow_const 2

lemma measurable_ebLam (L : ℝ) {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable[ℱ (i + 1)] (X i))
    (i : ℕ) : Measurable[ℱ i] (ebLam L X i) := by
  unfold ebLam
  exact measurable_const.min
    ((((measurable_ebVar hXm i).mul_const _).mul_const _).const_div _).sqrt

/-- **The manuscript's empirical-Bernstein test processes are supermartingales**
(`app:variance-cs`): `M_n^±(m)` built with the plug-in `μ̂`, `σ̂²` and
`λ_i = min (3/4) √(2 L / (σ̂²_{i-1} i log (i+1)))`, `L > 0`. -/
theorem ebProc_plugin_supermartingale [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {m s L : ℝ}
    (hL : 0 < L) (hXm : ∀ i, Measurable[ℱ (i + 1)] (X i))
    (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (hm : m ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, μ[X i | ℱ i] =ᵐ[μ] fun _ => m) (hs : s = 1 ∨ s = -1) :
    Supermartingale (ebProc s m X (ebMu X) (ebLam L X)) ℱ μ :=
  ebProc_supermartingale hXm hX hm hmean (measurable_ebMu hXm) (ebMu_mem hX)
    (measurable_ebLam L hXm)
    (fun i ω => ⟨(ebLam_mem hL X i ω).1.le, by linarith [(ebLam_mem hL X i ω).2]⟩) hs

end Process

/-! ### Coverage of the empirical-Bernstein intervals -/

section CoverageEB

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- **Anytime validity of the empirical-Bernstein terminal intervals (Lemma
`lem:nested-interval-valid`, empirical-Bernstein variant), with no supermartingale
hypothesis.**

For each terminal `z`, the observations `X z i` (`i = 0, 1, …`) are `[0,1]`-valued,
`X z i` is `ℱ z (i+1)`-measurable and has conditional mean `m z` given `ℱ z i`.  With
`L = log (2 |Z| / δ) > 0`, `λ_{z,i} = ebLam L (X z) i`, `μ̂_{z,i} = ebMu (X z) i`,
`Λ_{z,n} = ∑_{i<n} λ_{z,i}` and
`W_{z,n} = L + ∑_{i<n} (X_{z,i} - μ̂_{z,i})² ψ_E(λ_{z,i})`, the probability that some
`m z` leaves some interval
`[max 0 ((∑ λ X - W) / Λ), min 1 ((∑ λ X + W) / Λ)]`, `n ≥ 1`, is at most `δ`. -/
theorem eb_coverage_predictable [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ)
    (hδM : δ < 2 * Fintype.card Z) (ℱ : Z → Filtration ℕ m0) (X : Z → ℕ → Ω → ℝ)
    (m : Z → ℝ) (hXm : ∀ z i, Measurable[ℱ z (i + 1)] (X z i))
    (hX : ∀ z i ω, X z i ω ∈ Set.Icc (0 : ℝ) 1) (hm01 : ∀ z, m z ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z i, μ[X z i | ℱ z i] =ᵐ[μ] fun _ => m z) :
    μ {ω | ∃ z, ∃ n, 1 ≤ n ∧ m z ∉ Set.Icc
        (max 0 ((∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω * X z i ω -
            (Real.log (2 * Fintype.card Z / δ) +
              ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 *
                psiE (ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))) /
          ∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))
        (min 1 ((∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω * X z i ω +
            (Real.log (2 * Fintype.card Z / δ) +
              ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 *
                psiE (ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))) /
          ∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))} ≤
      ENNReal.ofReal δ := by
  set L : ℝ := Real.log (2 * Fintype.card Z / δ) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [one_lt_div hδ]; exact hδM)
  have hkey : ∀ (s : ℝ) (z : Z) (n : ℕ) (ω : Ω),
      s * (∑ i ∈ range n, ebLam L (X z) i ω * X z i ω -
          m z * ∑ i ∈ range n, ebLam L (X z) i ω) -
        ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 * psiE (ebLam L (X z) i ω) =
      s * ∑ i ∈ range n, ebLam L (X z) i ω * (X z i ω - m z) -
        ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 * psiE (ebLam L (X z) i ω) := by
    intro s z n ω
    congr 2
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hLam : ∀ z n ω, 1 ≤ n → 0 < ∑ i ∈ range n, ebLam L (X z) i ω := fun z n ω hn =>
    sum_pos (fun i _ => (ebLam_mem hL (X z) i ω).1) (nonempty_range_iff.mpr (by omega))
  have hplus : ∀ z, Supermartingale (fun n ω => Real.exp
      (∑ i ∈ range n, ebLam L (X z) i ω * X z i ω - m z * ∑ i ∈ range n, ebLam L (X z) i ω -
        ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 * psiE (ebLam L (X z) i ω)))
      (ℱ z) μ := by
    intro z
    have h := ebProc_plugin_supermartingale (μ := μ) (s := 1) hL (hXm z) (hX z) (hm01 z)
      (hmean z) (Or.inl rfl)
    convert h using 1
    funext n ω
    unfold ebProc
    rw [← hkey 1 z n ω, one_mul]
  have hminus : ∀ z, Supermartingale (fun n ω => Real.exp
      (-(∑ i ∈ range n, ebLam L (X z) i ω * X z i ω - m z * ∑ i ∈ range n, ebLam L (X z) i ω) -
        ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 * psiE (ebLam L (X z) i ω)))
      (ℱ z) μ := by
    intro z
    have h := ebProc_plugin_supermartingale (μ := μ) (s := -1) hL (hXm z) (hX z) (hm01 z)
      (hmean z) (Or.inr rfl)
    convert h using 1
    funext n ω
    unfold ebProc
    rw [← hkey (-1) z n ω, neg_one_mul]
  exact eb_coverage hδ ℱ
    (fun z n ω => ∑ i ∈ range n, ebLam L (X z) i ω * X z i ω)
    (fun z n ω => ∑ i ∈ range n, ebLam L (X z) i ω)
    (fun z n ω => ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 * psiE (ebLam L (X z) i ω))
    m hm01 hLam hplus hminus (fun z => by simp) (fun z => by simp)

/-- The filtration `ℱ n = σ(X_0, …, X_{n-1})` generated by the observations strictly
before time `n`. -/
def pastFiltration (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) : Filtration ℕ m0 where
  seq n := ⨆ k ∈ Set.Iio n, MeasurableSpace.comap (X k) inferInstance
  mono' := fun _ _ hab => biSup_mono fun _ hk => lt_of_lt_of_le hk hab
  le' := fun _ => iSup₂_le fun k _ => (hX k).comap_le

lemma measurable_pastFiltration (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (i : ℕ) :
    Measurable[pastFiltration X hX (i + 1)] (X i) := by
  have hle : MeasurableSpace.comap (X i) inferInstance ≤ pastFiltration X hX (i + 1) :=
    le_biSup (fun k => MeasurableSpace.comap (X k) inferInstance)
      (show i ∈ Set.Iio (i + 1) from Nat.lt_succ_self i)
  exact (comap_measurable (X i)).mono hle le_rfl

/-- For independent observations, the conditional mean of `X_i` given
`σ(X_0, …, X_{i-1})` is its mean. -/
lemma condExp_pastFiltration [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ) (i : ℕ) :
    μ[X i | pastFiltration X hX i] =ᵐ[μ] fun _ => ∫ ω, X i ω ∂μ := by
  have hind : Indep (⨆ k ∈ ({i} : Set ℕ), MeasurableSpace.comap (X k) inferInstance)
      (⨆ k ∈ Set.Iio i, MeasurableSpace.comap (X k) inferInstance) μ :=
    indep_iSup_of_disjoint (fun k => (hX k).comap_le) hindep (by simp)
  rw [_root_.iSup_singleton] at hind
  exact condExp_indep_eq (hX i).comap_le ((pastFiltration X hX).le i)
    (comap_measurable (X i)).stronglyMeasurable hind

/-- **Empirical-Bernstein coverage for independent bounded observations** (the
reward-tape model of `hoeffding_box_coverage`): for each terminal `z` the observations
`X z i` are independent, `[0,1]`-valued, with mean `m z`.  Same conclusion as
`eb_coverage_predictable`. -/
theorem eb_coverage_iid [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ)
    (hδM : δ < 2 * Fintype.card Z) (X : Z → ℕ → Ω → ℝ) (m : Z → ℝ)
    (hXm : ∀ z i, Measurable (X z i)) (hindep : ∀ z, iIndepFun (X z) μ)
    (hX : ∀ z i ω, X z i ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ z i, ∫ ω, X z i ω ∂μ = m z) :
    μ {ω | ∃ z, ∃ n, 1 ≤ n ∧ m z ∉ Set.Icc
        (max 0 ((∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω * X z i ω -
            (Real.log (2 * Fintype.card Z / δ) +
              ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 *
                psiE (ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))) /
          ∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))
        (min 1 ((∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω * X z i ω +
            (Real.log (2 * Fintype.card Z / δ) +
              ∑ i ∈ range n, (X z i ω - ebMu (X z) i ω) ^ 2 *
                psiE (ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))) /
          ∑ i ∈ range n, ebLam (Real.log (2 * Fintype.card Z / δ)) (X z) i ω))} ≤
      ENNReal.ofReal δ := by
  have hm01 : ∀ z, m z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    have hint : Integrable (X z 0) μ :=
      Integrable.of_mem_Icc 0 1 (hXm z 0).aemeasurable (Filter.Eventually.of_forall (hX z 0))
    rw [← hmean z 0]
    constructor
    · exact integral_nonneg fun ω => (hX z 0 ω).1
    · have := integral_mono hint (integrable_const (1 : ℝ)) fun ω => (hX z 0 ω).2
      simpa using this
  exact eb_coverage_predictable hδ hδM (fun z => pastFiltration (X z) (hXm z)) X m
    (fun z i => measurable_pastFiltration (X z) (hXm z) i) hX hm01
    (fun z i => by
      have h := condExp_pastFiltration (μ := μ) (hXm z) (hindep z) i
      rw [hmean z i] at h
      exact h)

end CoverageEB

end JointRootCert
