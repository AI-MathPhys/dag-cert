/-
Gaussian and chi-square tails for Lemma `lem:v34-concentration` ("Explicit intrinsic-tape
Gaussian concentration").

Results covered:

* the Gaussian sample-mean tail `P(|Ȳ - μ| ≥ r) ≤ 2 exp (-n r² / (2 v))`
  (`gaussian_mean_tail`);
* the moment generating function of the square of a standard Gaussian,
  `E exp (t g²) = (1 - 2 t)^{-1/2}` for `t < 1/2` (`integral_exp_mul_sq_gaussianReal`,
  `mgf_sq_stdGaussian`), and of a sum of independent squares (`mgf_sum_sq_stdGaussian`);
* the Laurent--Massart chi-square tails by Chernoff's method (`chiSq_upper_tail`,
  `chiSq_lower_tail`);
* the Cochran / Helmert decomposition of the centered sum of squares of iid standard
  Gaussians (`cochran_helmert`), and the resulting law `∑ (Y_i - Ȳ)² / v ~ χ²_{n-1}`
  (`chiSqMeasure`, `hasLaw_sum_sq_chiSq`, `hasLaw_sample_variance_chiSq`);
* the first claim of Lemma `lem:v34-concentration` with no distributional hypothesis
  (`gaussian_concentration_fixed`), by applying `concentration_fixed`.
-/
import JointRootCert.UnknownVariance

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ### Analytic inequalities for the chi-square cumulant generating function -/

/-- `(1 - 2t)^{-1/2} ≤ exp (t + t² / (1 - 2t))` for `0 ≤ t < 1/2`. -/
lemma inv_sqrt_le_exp_upper {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 2) :
    (Real.sqrt (1 - 2 * t))⁻¹ ≤ Real.exp (t + t ^ 2 / (1 - 2 * t)) := by
  set y := 1 - 2 * t with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hy1 : y ≤ 1 := by rw [hy]; linarith
  have hz : 0 ≤ -Real.log y := neg_nonneg.mpr (Real.log_nonpos hy0.le hy1)
  have hsinh := Real.self_le_sinh_iff.mpr hz
  rw [Real.sinh_eq, neg_neg, Real.exp_neg, Real.exp_log hy0] at hsinh
  have hrhs : (y⁻¹ - y) / 2 = 2 * (t + t ^ 2 / y) := by
    have hgen : ∀ z : ℝ, 0 < z →
        (z⁻¹ - z) / 2 = 2 * ((1 - z) / 2 + ((1 - z) / 2) ^ 2 / z) := by
      intro z hz
      have e : z⁻¹ * z = 1 := inv_mul_cancel₀ hz.ne'
      linear_combination (1 - z / 2) * e
    have ht' : (1 - y) / 2 = t := by rw [hy]; ring
    have h := hgen y hy0
    rwa [ht'] at h
  have heq : (Real.sqrt y)⁻¹ = Real.exp (-(Real.log y / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt hy0.le, Real.exp_log (Real.sqrt_pos.mpr hy0)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  rw [hrhs] at hsinh
  linarith

/-- `(1 + 2t)^{-1/2} ≤ exp (-t + t²)` for `t ≥ 0`. -/
lemma inv_sqrt_le_exp_lower {t : ℝ} (ht0 : 0 ≤ t) :
    (Real.sqrt (1 + 2 * t))⁻¹ ≤ Real.exp (-t + t ^ 2) := by
  have hy0 : 0 < 1 + 2 * t := by linarith
  have hlog := Real.le_log_one_add_of_nonneg (x := 2 * t) (by linarith)
  have h1 : 2 * t - 2 * t ^ 2 ≤ 2 * (2 * t) / (2 * t + 2) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [pow_nonneg ht0 3]
  have heq : (Real.sqrt (1 + 2 * t))⁻¹ = Real.exp (-(Real.log (1 + 2 * t) / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt hy0.le, Real.exp_log (Real.sqrt_pos.mpr hy0)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  linarith

/-! ### The moment generating function of a squared standard Gaussian -/

/-- `∫ exp (t x²) dN(0,1)(x) = (1 - 2t)^{-1/2}` for `t < 1/2`. -/
theorem integral_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, Real.exp (t * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hb : 0 < 1 / 2 - t := by linarith
  have h : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h2 : Real.pi / (1 / 2 - t) = 2 * Real.pi / (1 - 2 * t) := by
    field_simp
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [h2, Real.sqrt_div (by positivity)]
  field_simp

section MGF

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **MGF of the square of a standard Gaussian**: `E exp (t g²) = (1 - 2t)^{-1/2}`,
`t < 1/2`. -/
theorem mgf_sq_stdGaussian {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) P) {t : ℝ}
    (ht : t < 1 / 2) : mgf (fun ω => g ω ^ 2) P t = (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [← integral_exp_mul_sq_gaussianReal ht]
  exact hg.integral_comp (f := fun x => Real.exp (t * x ^ 2))
    (by fun_prop : Measurable fun x : ℝ => Real.exp (t * x ^ 2)).aestronglyMeasurable

lemma inv_sqrt_pos {t : ℝ} (ht : t < 1 / 2) : 0 < (Real.sqrt (1 - 2 * t))⁻¹ :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

/-- **MGF of a sum of independent squared standard Gaussians**:
`E exp (t ∑_{i ∈ s} g_i²) = (1 - 2t)^{-|s|/2}`, `t < 1/2`. -/
theorem mgf_sum_sq_stdGaussian {ι : Type*} {g : ι → Ω → ℝ} (hind : iIndepFun g P)
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (s : Finset ι) {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun ω => ∑ i ∈ s, g i ω ^ 2) P t = (Real.sqrt (1 - 2 * t))⁻¹ ^ s.card := by
  have hindsq : iIndepFun (fun i ω => g i ω ^ 2) P :=
    hind.comp (fun _ x => x ^ 2) (fun _ => measurable_id.pow_const 2)
  have hfun : (fun ω => ∑ i ∈ s, g i ω ^ 2) = ∑ i ∈ s, fun ω => g i ω ^ 2 := by
    funext ω
    simp
  rw [hfun, hindsq.mgf_sum₀ (fun i => (hg i).aemeasurable.pow_const 2) s]
  rw [prod_congr rfl fun i _ => mgf_sq_stdGaussian (hg i) ht, prod_const]

lemma integrable_exp_mul_sum_sq {ι : Type*} {g : ι → Ω → ℝ} (hind : iIndepFun g P)
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (s : Finset ι) {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ s, g i ω ^ 2)) P := by
  refine Integrable.of_integral_ne_zero ?_
  have h := mgf_sum_sq_stdGaussian hind hg s ht
  unfold mgf at h
  rw [h]
  exact (pow_pos (inv_sqrt_pos ht) _).ne'

/-! ### Laurent--Massart tails -/

/-- **Laurent--Massart upper tail.**  For `Q = ∑_{i ∈ s} g_i²` with `g_i` independent
standard Gaussians (a `χ²_k` variable, `k = |s|`) and `u ≥ 0`,
`P(Q ≥ k + 2 √(k u) + 2 u) ≤ exp (-u)`. -/
theorem chiSq_upper_tail [IsProbabilityMeasure P] {ι : Type*} {g : ι → Ω → ℝ}
    (hind : iIndepFun g P) (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (s : Finset ι)
    {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | s.card + 2 * Real.sqrt (s.card * u) + 2 * u ≤ ∑ i ∈ s, g i ω ^ 2} ≤
      Real.exp (-u) := by
  rcases hu.eq_or_lt with rfl | hupos
  · simp
  rcases Nat.eq_zero_or_pos s.card with hk | hk
  · have hs : s = ∅ := card_eq_zero.mp hk
    have hempty : {ω | (s.card : ℝ) + 2 * Real.sqrt (s.card * u) + 2 * u ≤
        ∑ i ∈ s, g i ω ^ 2} = ∅ := by
      ext ω
      simp only [hs, card_empty, Nat.cast_zero, zero_mul, Real.sqrt_zero, mul_zero, zero_add,
        sum_empty, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      linarith
    rw [hempty]
    simpa using (Real.exp_pos (-u)).le
  set k : ℝ := (s.card : ℝ) with hkdef
  have hkpos : 0 < k := by rw [hkdef]; exact_mod_cast hk
  set a := Real.sqrt k with ha
  set b := Real.sqrt u with hb
  have hapos : 0 < a := Real.sqrt_pos.mpr hkpos
  have hbpos : 0 < b := Real.sqrt_pos.mpr hupos
  have ha2 : a ^ 2 = k := Real.sq_sqrt hkpos.le
  have hb2 : b ^ 2 = u := Real.sq_sqrt hupos.le
  have hab : Real.sqrt (k * u) = a * b := Real.sqrt_mul hkpos.le u
  set t := b / (a + 2 * b) with htdef
  have hd : 0 < a + 2 * b := by linarith
  have ht0 : 0 ≤ t := by positivity
  have ht : t < 1 / 2 := by
    rw [htdef, div_lt_iff₀ hd]
    linarith
  have e1 : t * (a + 2 * b) = b := div_mul_cancel₀ b hd.ne'
  have h12 : 0 < 1 - 2 * t := by linarith
  have e2 : t ^ 2 / (1 - 2 * t) * a = t * b := by
    have h3 : t ^ 2 / (1 - 2 * t) * (1 - 2 * t) = t ^ 2 := div_mul_cancel₀ _ h12.ne'
    have h4 : (1 - 2 * t) * (a + 2 * b) = a := by linear_combination -2 * e1
    calc t ^ 2 / (1 - 2 * t) * a = t ^ 2 / (1 - 2 * t) * ((1 - 2 * t) * (a + 2 * b)) := by
          rw [h4]
      _ = t ^ 2 * (a + 2 * b) := by rw [← mul_assoc, h3]
      _ = t * b := by rw [pow_two, mul_assoc, e1]
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i ∈ s, g i ω ^ 2)
    (k + 2 * Real.sqrt (k * u) + 2 * u) ht0 (integrable_exp_mul_sum_sq hind hg s ht)
  rw [mgf_sum_sq_stdGaussian hind hg s ht] at hch
  refine hch.trans ?_
  calc Real.exp (-t * (k + 2 * Real.sqrt (k * u) + 2 * u)) * (Real.sqrt (1 - 2 * t))⁻¹ ^ s.card
      ≤ Real.exp (-t * (k + 2 * Real.sqrt (k * u) + 2 * u)) *
          Real.exp (t + t ^ 2 / (1 - 2 * t)) ^ s.card :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_sqrt_pos ht).le (inv_sqrt_le_exp_upper ht0 ht) _)
          (Real.exp_pos _).le
    _ = Real.exp (-u) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        rw [← hkdef, hab, ← ha2, ← hb2]
        linear_combination a * e2 - b * e1

/-- **Laurent--Massart lower tail.**  For `Q = ∑_{i ∈ s} g_i²` with `g_i` independent
standard Gaussians, `k = |s| ≥ 1` and `u ≥ 0`, `P(Q ≤ k - 2 √(k u)) ≤ exp (-u)`.
(For `k = 0` and `u > 0` the event is `{0 ≤ 0}`, so `k ≥ 1` is needed for the non-strict
event.) -/
theorem chiSq_lower_tail [IsProbabilityMeasure P] {ι : Type*} {g : ι → Ω → ℝ}
    (hind : iIndepFun g P) (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (s : Finset ι)
    (hs : s.Nonempty) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | ∑ i ∈ s, g i ω ^ 2 ≤ s.card - 2 * Real.sqrt (s.card * u)} ≤ Real.exp (-u) := by
  set k : ℝ := (s.card : ℝ) with hkdef
  have hkpos : 0 < k := by rw [hkdef]; exact_mod_cast hs.card_pos
  set a := Real.sqrt k with ha
  set b := Real.sqrt u with hb
  have hapos : 0 < a := Real.sqrt_pos.mpr hkpos
  have hbpos : 0 ≤ b := Real.sqrt_nonneg u
  have ha2 : a ^ 2 = k := Real.sq_sqrt hkpos.le
  have hb2 : b ^ 2 = u := Real.sq_sqrt hu
  have hab : Real.sqrt (k * u) = a * b := Real.sqrt_mul hkpos.le u
  set t := b / a with htdef
  have ht0 : 0 ≤ t := by positivity
  have e1 : t * a = b := div_mul_cancel₀ b hapos.ne'
  have hneg : -t < 1 / 2 := by linarith
  have hch := measure_le_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i ∈ s, g i ω ^ 2)
    (k - 2 * Real.sqrt (k * u)) (neg_nonpos.mpr ht0) (integrable_exp_mul_sum_sq hind hg s hneg)
  rw [mgf_sum_sq_stdGaussian hind hg s hneg] at hch
  refine hch.trans ?_
  have h1 : (1 : ℝ) - 2 * -t = 1 + 2 * t := by ring
  rw [h1]
  calc Real.exp (- -t * (k - 2 * Real.sqrt (k * u))) * (Real.sqrt (1 + 2 * t))⁻¹ ^ s.card
      ≤ Real.exp (- -t * (k - 2 * Real.sqrt (k * u))) * Real.exp (-t + t ^ 2) ^ s.card :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))).le
            (inv_sqrt_le_exp_lower ht0) _)
          (Real.exp_pos _).le
    _ = Real.exp (-u) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        rw [← hkdef, hab, ← ha2, ← hb2]
        linear_combination (t * a - b) * e1

/-! ### Gaussian sample mean -/

/-- A centered Gaussian `N(0, v)` variable has sub-Gaussian MGF with parameter `v`. -/
lemma hasSubgaussianMGF_of_gaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : HasSubgaussianMGF X v P := by
  have hm : ∀ t, mgf X P t = Real.exp (v * t ^ 2 / 2) := by
    intro t
    rw [mgf_gaussianReal hX t]
    congr 1
    ring
  refine ⟨fun t => Integrable.of_integral_ne_zero ?_, fun t => (hm t).le⟩
  have h := hm t
  unfold mgf at h
  rw [h]
  exact (Real.exp_pos _).ne'

/-- **Gaussian sample-mean tail.**  For `n ≥ 1` independent `N(μ, v)` observations, `v > 0`,
`P(|Ȳ_n - μ| ≥ r) ≤ 2 exp (-n r² / (2 v))`. -/
theorem gaussian_mean_tail [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (hind : iIndepFun Y P) (hY : ∀ i, HasLaw (Y i) (gaussianReal μ v) P) {n : ℕ}
    (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    P.real {ω | r ≤ |(∑ i ∈ range n, Y i ω) / n - μ|} ≤
      2 * Real.exp (-(n * r ^ 2 / (2 * v))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have hsub : ∀ i, HasSubgaussianMGF (fun ω => Y i ω - μ) v P := by
    intro i
    have h := gaussianReal_sub_const (hY i) μ
    rw [sub_self] at h
    exact hasSubgaussianMGF_of_gaussian h
  have hsubN : ∀ i, HasSubgaussianMGF (fun ω => -(Y i ω - μ)) v P := fun i => (hsub i).neg
  have hindY : iIndepFun (fun i ω => Y i ω - μ) P :=
    hind.comp (fun _ x => x - μ) (fun _ => measurable_id.sub_const μ)
  have hindN : iIndepFun (fun i ω => -(Y i ω - μ)) P :=
    hind.comp (fun _ x => -(x - μ)) (fun _ => (measurable_id.sub_const μ).neg)
  have hε : (0 : ℝ) ≤ n * r := by positivity
  have hup := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindY (n := n)
    (fun i _ => hsub i) hε
  have hdown := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindN (n := n)
    (fun i _ => hsubN i) hε
  have hexp : Real.exp (-(n * r) ^ 2 / (2 * n * v)) = Real.exp (-(n * r ^ 2 / (2 * v))) := by
    congr 1
    field_simp
  rw [hexp] at hup hdown
  have hsubset : {ω | r ≤ |(∑ i ∈ range n, Y i ω) / n - μ|} ⊆
      {ω | n * r ≤ ∑ i ∈ range n, (Y i ω - μ)} ∪
        {ω | n * r ≤ ∑ i ∈ range n, -(Y i ω - μ)} := by
    intro ω hω
    have hω' : r ≤ |(∑ i ∈ range n, Y i ω) / n - μ| := hω
    have hsum : ∑ i ∈ range n, (Y i ω - μ) = (∑ i ∈ range n, Y i ω) - n * μ := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    have hsum' : ∑ i ∈ range n, -(Y i ω - μ) = -((∑ i ∈ range n, Y i ω) - n * μ) := by
      rw [sum_neg_distrib, hsum]
    have hdiv : (∑ i ∈ range n, Y i ω) / n - μ = ((∑ i ∈ range n, Y i ω) - n * μ) / n := by
      field_simp
    rw [hdiv, abs_div, abs_of_pos hnpos, le_div_iff₀ hnpos] at hω'
    rcases le_abs.mp hω' with h | h
    · left
      show (n : ℝ) * r ≤ ∑ i ∈ range n, (Y i ω - μ)
      rw [hsum]
      linarith
    · right
      show (n : ℝ) * r ≤ ∑ i ∈ range n, -(Y i ω - μ)
      rw [hsum']
      linarith
  calc P.real {ω | r ≤ |(∑ i ∈ range n, Y i ω) / n - μ|}
      ≤ P.real ({ω | n * r ≤ ∑ i ∈ range n, (Y i ω - μ)} ∪
          {ω | n * r ≤ ∑ i ∈ range n, -(Y i ω - μ)}) := measureReal_mono hsubset
    _ ≤ P.real {ω | n * r ≤ ∑ i ∈ range n, (Y i ω - μ)} +
          P.real {ω | n * r ≤ ∑ i ∈ range n, -(Y i ω - μ)} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(n * r ^ 2 / (2 * v))) := by linarith

/-! ### Cochran / Helmert decomposition -/

/-- `∑ (z_i - z̄)² = ∑ z_i² - (∑ z_i / √n)²`. -/
lemma sum_sq_centered {n : ℕ} (hn : 1 ≤ n) (z : Fin n → ℝ) :
    ∑ i, (z i - (∑ j, z j) / n) ^ 2 = ∑ i, z i ^ 2 - ((∑ j, z j) / Real.sqrt n) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∑ i, (z i - (∑ j, z j) / n) ^ 2 =
      ∑ i, (z i ^ 2 - 2 * ((∑ j, z j) / n) * z i + ((∑ j, z j) / n) ^ 2) :=
    sum_congr rfl fun i _ => by ring
  rw [h1, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, div_pow _ (Real.sqrt n), Real.sq_sqrt hnpos.le]
  field_simp
  ring

/-- **Cochran / Helmert.**  Let `Z_1, …, Z_n` be independent standard Gaussians, `n ≥ 1`.
There are independent standard Gaussians `W_1, …, W_n` (the coordinates of `Z` in an
orthonormal basis whose first vector is `(1, …, 1) / √n`) and an index `i₀` such that
`W_{i₀} = √n Z̄` and `∑_i (Z_i - Z̄)² = ∑_{i ≠ i₀} W_i²`.  Thus the centered sum of squares is
a sum of `n - 1` independent squared standard Gaussians (a `χ²_{n-1}` variable), jointly
independent of the sample mean. -/
theorem cochran_helmert [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n) {Z : Fin n → Ω → ℝ}
    (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) :
    ∃ (W : Fin n → Ω → ℝ) (i0 : Fin n), iIndepFun W P ∧
      (∀ i, HasLaw (W i) (gaussianReal 0 1) P) ∧
      (∀ ω, W i0 ω = (∑ i, Z i ω) / Real.sqrt n) ∧
      ∀ ω, ∑ i, (Z i ω - (∑ j, Z j ω) / n) ^ 2 = ∑ i ∈ univ.erase i0, W i ω ^ 2 := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  let i0 : Fin n := ⟨0, hn⟩
  let e : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (Real.sqrt n)⁻¹)
  have he : inner ℝ e e = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow,
      Real.sq_sqrt hnpos.le]
    exact mul_inv_cancel₀ hnpos.ne'
  have horth : Orthonormal ℝ (({i0} : Set (Fin n)).domRestrict
      (fun _ : Fin n => e)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim i j
    have hite : (if i = j then (1 : ℝ) else 0) = 1 := by simp [hij]
    rw [hite]
    exact he
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n))
  have hb0 : b i0 = e := hb i0 rfl
  let V : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 (fun i => Z i ω)
  let W : Fin n → Ω → ℝ := fun i ω => b.repr (V ω) i
  have hpi : HasLaw (fun ω i => Z i ω) (Measure.pi fun _ : Fin n => gaussianReal 0 1) P :=
    hind.hasLaw_pi hZ
  have hto : HasLaw (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    ⟨(WithLp.measurable_toLp 2 _).aemeasurable, map_pi_eq_stdGaussian⟩
  have hrepr : HasLaw (b.repr : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨b.repr.continuous.measurable.aemeasurable, stdGaussian_map b.repr⟩
  have hof : HasLaw (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    refine ⟨(WithLp.measurable_ofLp 2 _).aemeasurable, ?_⟩
    rw [← map_pi_eq_stdGaussian,
      Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _)]
    exact Measure.map_id
  have hWvec : HasLaw (fun ω i => W i ω) (Measure.pi fun _ : Fin n => gaussianReal 0 1) P :=
    hof.comp (hrepr.comp (hto.comp hpi))
  have hWi : ∀ i, HasLaw (W i) (gaussianReal 0 1) P := fun i =>
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).hasLaw.comp hWvec
  have hWind : iIndepFun W P := (iIndepFun_iff_hasLaw_pi_pi hWi).mpr hWvec
  have hW0 : ∀ ω, W i0 ω = (∑ i, Z i ω) / Real.sqrt n := by
    intro ω
    show b.repr (V ω) i0 = _
    rw [b.repr_apply_apply, hb0]
    simp only [e, V, EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, div_eq_mul_inv, sum_mul]
  have hsq : ∀ ω, ∑ i, W i ω ^ 2 = ∑ i, Z i ω ^ 2 := by
    intro ω
    have h1 := b.sum_sq_norm_inner_right (V ω)
    rw [EuclideanSpace.real_norm_sq_eq] at h1
    simpa [W, b.repr_apply_apply, V] using h1
  refine ⟨W, i0, hWind, hWi, hW0, fun ω => ?_⟩
  rw [sum_sq_centered hn, ← hsq ω, ← hW0 ω, ← sum_erase_add _ _ (mem_univ i0)]
  ring

/-! ### The chi-square law of the sample variance -/

/-- The chi-square distribution with `k` degrees of freedom: the law of `∑_{i<k} x_i²` under
the product of `k` standard Gaussians.  (Mathlib has no chi-square distribution.) -/
noncomputable def chiSqMeasure (k : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, x i ^ 2)

/-- A sum of `|s|` independent squared standard Gaussians has law `χ²_{|s|}`. -/
theorem hasLaw_sum_sq_chiSq {ι : Type*} {g : ι → Ω → ℝ} (hind : iIndepFun g P)
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s, g i ω ^ 2) (chiSqMeasure s.card) P := by
  let e : Fin s.card ≃ s := s.equivFin.symm
  have hinj : Function.Injective (fun j : Fin s.card => (e j : ι)) :=
    Subtype.val_injective.comp e.injective
  have hpi : HasLaw (fun ω (j : Fin s.card) => g (e j) ω)
      (Measure.pi fun _ : Fin s.card => gaussianReal 0 1) P :=
    (hind.precomp hinj).hasLaw_pi (fun j => hg (e j))
  have hsum : HasLaw (fun x : Fin s.card → ℝ => ∑ i, x i ^ 2) (chiSqMeasure s.card)
      (Measure.pi fun _ : Fin s.card => gaussianReal 0 1) :=
    ⟨(by fun_prop : Measurable fun x : Fin s.card → ℝ => ∑ i, x i ^ 2).aemeasurable, rfl⟩
  have h := hsum.comp hpi
  have hfun : (fun ω => ∑ i ∈ s, g i ω ^ 2) =
      (fun x : Fin s.card → ℝ => ∑ i, x i ^ 2) ∘ fun ω (j : Fin s.card) => g (e j) ω := by
    funext ω
    simp only [Function.comp]
    rw [← Finset.sum_coe_sort s (fun i => g i ω ^ 2)]
    exact (Equiv.sum_comp e (fun i : s => g i ω ^ 2)).symm
  rw [hfun]
  exact h

/-- **Cochran's theorem for the sample variance.**  For `n ≥ 1` independent `N(μ, v)`
observations, `v > 0`, the statistic `∑_i (Y_i - Ȳ)² / v = (n - 1) S² / v = n v̌ / v` has
law `χ²_{n-1}`. -/
theorem hasLaw_sample_variance_chiSq [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n) {v μ : ℝ}
    (hv : 0 < v) {Y : Fin n → Ω → ℝ} (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal μ v.toNNReal) P) :
    HasLaw (fun ω => (∑ i, (Y i ω - (∑ j, Y j ω) / n) ^ 2) / v) (chiSqMeasure (n - 1)) P := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hvnn : (v.toNNReal : ℝ) = v := Real.coe_toNNReal v hv.le
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  let Z : Fin n → Ω → ℝ := fun i ω => (Y i ω - μ) / Real.sqrt v
  have hZind : iIndepFun Z P :=
    hind.comp (fun _ x => (x - μ) / Real.sqrt v)
      (fun _ => (measurable_id.sub_const μ).div_const _)
  have hZlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P := by
    intro i
    have h := gaussianReal_div_const (gaussianReal_sub_const (hY i) μ) (Real.sqrt v)
    have h1 : (μ - μ) / Real.sqrt v = 0 := by simp
    have h2 : v.toNNReal / NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) = 1 := by
      apply NNReal.eq
      push_cast
      rw [hvnn]
      show v / (Real.sqrt v ^ 2) = 1
      rw [Real.sq_sqrt hv.le, div_self hv.ne']
    rw [h1, h2] at h
    exact h
  obtain ⟨W, i0, hWind, hWlaw, -, hWsq⟩ := cochran_helmert hn hZind hZlaw
  have h := hasLaw_sum_sq_chiSq hWind hWlaw (univ.erase i0)
  rw [card_erase_of_mem (mem_univ i0), card_univ, Fintype.card_fin] at h
  have hfun : (fun ω => (∑ i, (Y i ω - (∑ j, Y j ω) / n) ^ 2) / v) =
      fun ω => ∑ i ∈ univ.erase i0, W i ω ^ 2 := by
    funext ω
    rw [← hWsq ω]
    have hZbar : (∑ j : Fin n, Z j ω) / n = ((∑ j, Y j ω) / n - μ) / Real.sqrt v := by
      simp only [Z]
      rw [← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hterm : ∀ i : Fin n, (Z i ω - (∑ j : Fin n, Z j ω) / n) ^ 2 =
        (Y i ω - (∑ j, Y j ω) / n) ^ 2 / v := by
      intro i
      rw [hZbar]
      simp only [Z]
      rw [← sub_div, div_pow, Real.sq_sqrt hv.le]
      congr 1
      ring
    rw [sum_congr rfl fun i _ => hterm i, ← sum_div]
  rw [hfun]
  exact h

/-! ### Lemma `lem:v34-concentration`, first claim -/

/-- **Explicit Gaussian concentration, fixed sample size (Lemma `lem:v34-concentration`,
first claim), with no distributional hypothesis.**  `Y_0, Y_1, …` are independent
`N(μ, v)` observations, `v > 0`.  For `0 < r ≤ v / 8` and every `n`, the probability that
the mean or the centered variance (denominator `n`) of the first `n` observations differs
from `(μ, v)` by more than `r` is at most `Q(n, r)`. -/
theorem gaussian_concentration_fixed [IsProbabilityMeasure P] {v r μ : ℝ} (hv : 0 < v)
    (hr0 : 0 < r) (hrv : r ≤ v / 8) (n : ℕ) {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal μ v.toNNReal) P) :
    P {ω | r < |(∑ i ∈ range n, Y i ω) / n - μ| ∨
        r < |(∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n - v|} ≤
      ENNReal.ofReal (Qtail v n r) := by
  by_cases hn : n < n0 v r
  · unfold Qtail
    simp only [hn, ↓reduceIte]
    simpa using prob_le_one
  have hn3 : 3 ≤ n := (le_max_left _ _).trans (not_lt.mp hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hvnn : (v.toNNReal : ℝ) = v := Real.coe_toNNReal v hv.le
  have hvne : v.toNNReal ≠ 0 := by
    intro h
    rw [h] at hvnn
    simp at hvnn
    linarith
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  -- standardized observations
  let Z : Fin n → Ω → ℝ := fun i ω => (Y i ω - μ) / Real.sqrt v
  have hZind : iIndepFun Z P :=
    (hind.precomp Fin.val_injective).comp (fun _ x => (x - μ) / Real.sqrt v)
      (fun _ => (measurable_id.sub_const μ).div_const _)
  have hZlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P := by
    intro i
    have h := gaussianReal_div_const (gaussianReal_sub_const (hY i) μ) (Real.sqrt v)
    have h1 : (μ - μ) / Real.sqrt v = 0 := by simp
    have h2 : v.toNNReal / NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) = 1 := by
      apply NNReal.eq
      push_cast
      rw [hvnn]
      show v / (Real.sqrt v ^ 2) = 1
      rw [Real.sq_sqrt hv.le, div_self hv.ne']
    rw [h1, h2] at h
    exact h
  obtain ⟨W, i0, hWind, hWlaw, -, hWsq⟩ := cochran_helmert (by omega : 1 ≤ n) hZind hZlaw
  have hcard : (((univ : Finset (Fin n)).erase i0).card : ℝ) = (n : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ i0), card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have key : ∀ ω, n * ((∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n) / v =
      ∑ i ∈ univ.erase i0, W i ω ^ 2 := by
    intro ω
    rw [← hWsq ω]
    have hZbar : (∑ j : Fin n, Z j ω) / n =
        ((∑ j ∈ range n, Y j ω) / n - μ) / Real.sqrt v := by
      simp only [Z]
      rw [← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        sum_range (fun j => Y j ω)]
      field_simp
    have hterm : ∀ i : Fin n, (Z i ω - (∑ j : Fin n, Z j ω) / n) ^ 2 =
        (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2 / v := by
      intro i
      rw [hZbar]
      simp only [Z]
      rw [← sub_div, div_pow, Real.sq_sqrt hv.le]
      congr 1
      ring
    rw [sum_congr rfl fun i _ => hterm i, ← sum_div,
      sum_range (fun i => (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2)]
    field_simp
  have hu : 0 ≤ ((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have : 0 ≤ (n : ℝ) - 1 := by linarith
    positivity
  have hne : ((univ : Finset (Fin n)).erase i0).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ i0), card_univ, Fintype.card_fin]
    omega
  have hU := chiSq_upper_tail hWind hWlaw (univ.erase i0) hu
  have hL := chiSq_lower_tail hWind hWlaw (univ.erase i0) hne hu
  rw [hcard] at hU hL
  refine concentration_fixed P hv hr0 hrv n
    (fun ω => (∑ i ∈ range n, Y i ω) / n)
    (fun ω => (∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n) ?_ ?_ ?_
  · have h := gaussian_mean_tail hvne hind hY (n := n) (by omega) hr0.le
    rw [hvnn] at h
    have hsub : {ω | r < |(∑ i ∈ range n, Y i ω) / n - μ|} ⊆
        {ω | r ≤ |(∑ i ∈ range n, Y i ω) / n - μ|} := fun ω hω => by
      have h1 : r < |(∑ i ∈ range n, Y i ω) / n - μ| := hω
      exact h1.le
    exact (measure_mono hsub).trans
      ((ofReal_measureReal (μ := P)).symm.le.trans (ENNReal.ofReal_le_ofReal h))
  · refine (measure_mono fun ω hω => ?_).trans
      ((ofReal_measureReal (μ := P)).symm.le.trans (ENNReal.ofReal_le_ofReal hU))
    have h1 : _ < n * ((∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n) / v := hω
    rw [key ω] at h1
    exact h1.le
  · refine (measure_mono fun ω hω => ?_).trans
      ((ofReal_measureReal (μ := P)).symm.le.trans (ENNReal.ofReal_le_ofReal hL))
    have h1 : n * ((∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n) / v < _ := hω
    rw [key ω] at h1
    exact h1.le

end MGF

end JointRootCert
