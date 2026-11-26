/-
Unknown-variance Gaussian tracking: the concrete Gaussian batch model
(manuscript subsection "Unknown-variance Gaussian tracking: construction and proofs",
`app:v34-theory`).

Results covered:

* Lemma `lem:v34-batch-comparison` (A uniform batch log-likelihood comparison):
  `batchDens` (the Gaussian batch density `p_{u,s}`, and the plug-in predictor `q` of
  `eq:v34-predictor-density`), `nullEnv` (the null envelope `U_{a,z}`),
  `batchDens_eq_exp`, `nullEnv_eq_exp`, `batch_loglik_identification`
  (`R⁻¹ log (q(Y) / U(Y)) = profStat`), and `batch_comparison_loglik` (the lemma as stated).
* Theorem `thm:v34-action-local` (Action-local optional evaluation and intersection-union
  root coverage): `lintegral_batch_ratio_eq_one` (the one-step identity for a fresh Gaussian
  batch of predictable size), `lintegral_freeze` (conditioning on the past of a function of
  the past and of an independent fresh batch), `gaussian_localWealth_supermartingale` (the
  supermartingale property, derived), `action_local_coverage_gaussian` (coverage with
  hypotheses on the batch model only).
* Theorem `thm:v34-adaptive`, second term of `eq:v34-explicit-tail`:
  `fresh_batch_concentration` (a fresh batch of predictable size at least `b` is bad with
  probability at most `Q(b, r)`), `Qtail_anti`.

What each theorem assumes is stated in its doc comment.
-/
import JointRootCert.Assembly
import JointRootCert.ChiSquare

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! ### The Gaussian batch density, the plug-in predictor and the null envelope -/

section BatchDensity

variable {X : Type*} [Fintype X] {U : Type*}

/-- The Gaussian batch density.  A batch with planned sizes `r` reads, for every query type
`x`, the entries `y x 0, …, y x (r x - 1)`; under query means `t` and query variances `s` its
density is `∏ₓ ∏_{ℓ < rₓ} N(yₓℓ; tₓ, sₓ)`.  With `t = pred · u` this is the manuscript's
`p_{u,s}`, and with the predictable estimates `(μ̂, v̂)` it is the plug-in predictor `q_j` of
`eq:v34-predictor-density`. -/
def batchDens (r : X → ℕ) (t s : X → ℝ) (y : X → ℕ → ℝ) : ℝ :=
  ∏ x, ∏ ℓ ∈ range (r x), gaussianPDFReal (t x) (s x).toNNReal (y x ℓ)

/-- Within-batch empirical mean `Ȳₓ`. -/
def batchMean (r : X → ℕ) (y : X → ℕ → ℝ) (x : X) : ℝ :=
  (∑ ℓ ∈ range (r x), y x ℓ) / r x

/-- Within-batch centered variance `v̌ₓ` (denominator `rₓ`). -/
def batchVar (r : X → ℕ) (y : X → ℕ → ℝ) (x : X) : ℝ :=
  (∑ ℓ ∈ range (r x), (y x ℓ - batchMean r y x) ^ 2) / r x

/-- The component-null likelihood supremum
`U_{a,z}(y) = sup_{u ∈ H, sₓ > 0} p_{u,s}(y)` (as a real supremum; it is finite when every
within-batch centered variance is positive, see `batchDens_le_nullEnv`). -/
def nullEnv (H : Set U) (pred : X → U → ℝ) (r : X → ℕ) (y : X → ℕ → ℝ) : ℝ :=
  ⨆ p : {p : U × (X → ℝ) // p.1 ∈ H ∧ ∀ x, 0 < p.2 x},
    batchDens r (fun x => pred x p.1.1) p.1.2 y

lemma batchDens_nonneg (r : X → ℕ) (t s : X → ℝ) (y : X → ℕ → ℝ) : 0 ≤ batchDens r t s y :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

lemma toNNReal_ne_zero_of_pos {s : ℝ} (hs : 0 < s) : s.toNNReal ≠ 0 := by
  simpa using hs

lemma batchDens_pos (r : X → ℕ) (t : X → ℝ) {s : X → ℝ} (hs : ∀ x, 0 < s x)
    (y : X → ℕ → ℝ) : 0 < batchDens r t s y :=
  prod_pos fun x _ => prod_pos fun _ _ =>
    gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero_of_pos (hs x))

/-- The Gaussian density as an exponential. -/
lemma gaussianPDFReal_eq_exp (t : ℝ) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    gaussianPDFReal t s.toNNReal y =
      Real.exp (-(1 / 2) * Real.log (2 * Real.pi * s) - (y - t) ^ 2 / (2 * s)) := by
  have hpos : (0 : ℝ) < 2 * Real.pi * s := by positivity
  have e : -(1 / 2) * Real.log (2 * Real.pi * s) - (y - t) ^ 2 / (2 * s) =
      Real.log (√(2 * Real.pi * s))⁻¹ + -(y - t) ^ 2 / (2 * s) := by
    rw [Real.log_inv, Real.log_sqrt hpos.le]
    ring
  rw [gaussianPDFReal, Real.coe_toNNReal s hs.le, e, Real.exp_add,
    Real.exp_log (by positivity)]

omit [Fintype X] in
/-- Sum-of-squares decomposition of one query type of a batch. -/
lemma batch_sum_sq (r : X → ℕ) (y : X → ℕ → ℝ) (x : X) (t : ℝ) :
    ∑ ℓ ∈ range (r x), (y x ℓ - t) ^ 2 =
      (r x : ℝ) * (batchVar r y x + (batchMean r y x - t) ^ 2) := by
  rcases Nat.eq_zero_or_pos (r x) with h0 | hpos
  · simp [h0]
  · have h := sum_sq_decomp (range (r x)) (nonempty_range_iff.mpr hpos.ne') (fun ℓ => y x ℓ) t
    rw [card_range] at h
    exact h

/-- **Log-density of a Gaussian batch** in terms of the within-batch mean and centered
variance: `log p_{t,s}(y) = ∑ₓ rₓ [-½ log (2π sₓ) - (v̌ₓ + (Ȳₓ - tₓ)²) / (2 sₓ)]`. -/
lemma batchDens_eq_exp (r : X → ℕ) (t : X → ℝ) {s : X → ℝ} (hs : ∀ x, 0 < s x)
    (y : X → ℕ → ℝ) :
    batchDens r t s y =
      Real.exp (∑ x, (r x : ℝ) * (-(1 / 2) * Real.log (2 * Real.pi * s x) -
        (batchVar r y x + (batchMean r y x - t x) ^ 2) / (2 * s x))) := by
  unfold batchDens
  rw [Real.exp_sum]
  refine prod_congr rfl fun x _ => ?_
  rw [prod_congr rfl fun ℓ _ => gaussianPDFReal_eq_exp (t x) (hs x) (y x ℓ), ← Real.exp_sum]
  congr 1
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div, batch_sum_sq]
  ring

section Identification

variable (H : Set U) (pred : X → U → ℝ) (r : X → ℕ) (y : X → ℕ → ℝ) (muh vh : X → ℝ)

/-- The unnormalized profiled statistic `∑ₓ rₓ · ½ profBracket`. -/
def profSum (u : U) : ℝ :=
  ∑ x, (r x : ℝ) * (1 / 2 * profBracket (batchMean r y x) (batchVar r y x) (muh x) (vh x)
    (pred x u))

/-- The log of the plug-in predictor density. -/
def logQ : ℝ :=
  ∑ x, (r x : ℝ) * (-(1 / 2) * Real.log (2 * Real.pi * vh x) -
    (batchVar r y x + (batchMean r y x - muh x) ^ 2) / (2 * vh x))

/-- The variance-profiled null log-likelihood at `u`. -/
def logProf (u : U) : ℝ :=
  ∑ x, (r x : ℝ) * (-(1 / 2) * (Real.log (2 * Real.pi) + 1) -
    1 / 2 * Real.log (batchVar r y x + (batchMean r y x - pred x u) ^ 2))

variable {H pred r y muh vh}

private lemma profSum_eq (hvchk : ∀ x, 0 < batchVar r y x) (hvh : ∀ x, 0 < vh x) (u : U) :
    profSum pred r y muh vh u = logQ r y muh vh - logProf pred r y u := by
  unfold profSum logQ logProf
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← profBracket_eq_loglik (hvchk x) (hvh x) (t := pred x u), mul_sub]

/-- Every null density is at most the profiled likelihood at the same `u`. -/
private lemma batchDens_le_prof (hvchk : ∀ x, 0 < batchVar r y x) (u : U) {s : X → ℝ}
    (hs : ∀ x, 0 < s x) :
    batchDens r (fun x => pred x u) s y ≤ Real.exp (logProf pred r y u) := by
  rw [batchDens_eq_exp r _ hs]
  refine Real.exp_le_exp.mpr (sum_le_sum fun x _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact gaussian_profile_le (by have := hvchk x; positivity) (hs x)

/-- The profiled likelihood is attained at `sₓ = v̌ₓ + (Ȳₓ - hₓᵀu)²`. -/
private lemma batchDens_prof_eq (hvchk : ∀ x, 0 < batchVar r y x) (u : U) :
    batchDens r (fun x => pred x u)
        (fun x => batchVar r y x + (batchMean r y x - pred x u) ^ 2) y =
      Real.exp (logProf pred r y u) := by
  rw [batchDens_eq_exp r _ (fun x => by have := hvchk x; positivity)]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [gaussian_profile_eq (by have := hvchk x; positivity)]

private lemma logProf_le (hvchk : ∀ x, 0 < batchVar r y x) (u : U) :
    logProf pred r y u ≤ ∑ x, (r x : ℝ) * (-(1 / 2) * (Real.log (2 * Real.pi) + 1) -
      1 / 2 * Real.log (batchVar r y x)) := by
  refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have := Real.log_le_log (hvchk x)
    (by nlinarith [sq_nonneg (batchMean r y x - pred x u)] :
      batchVar r y x ≤ batchVar r y x + (batchMean r y x - pred x u) ^ 2)
  linarith

/-- The null densities are bounded above when every within-batch centered variance is
positive. -/
lemma nullEnv_bddAbove (H : Set U) (pred : X → U → ℝ) (hvchk : ∀ x, 0 < batchVar r y x) :
    BddAbove (Set.range fun p : {p : U × (X → ℝ) // p.1 ∈ H ∧ ∀ x, 0 < p.2 x} =>
      batchDens r (fun x => pred x p.1.1) p.1.2 y) := by
  refine ⟨Real.exp (∑ x, (r x : ℝ) * (-(1 / 2) * (Real.log (2 * Real.pi) + 1) -
      1 / 2 * Real.log (batchVar r y x))), ?_⟩
  rintro _ ⟨p, rfl⟩
  exact (batchDens_le_prof hvchk p.1.1 p.2.2).trans
    (Real.exp_le_exp.mpr (logProf_le hvchk p.1.1))

/-- Every null density is at most the envelope: `p_{u,s}(y) ≤ U(y)` for `u ∈ H`, `s > 0`. -/
lemma batchDens_le_nullEnv (hvchk : ∀ x, 0 < batchVar r y x) {u : U} (hu : u ∈ H)
    {s : X → ℝ} (hs : ∀ x, 0 < s x) :
    batchDens r (fun x => pred x u) s y ≤ nullEnv H pred r y :=
  le_ciSup (nullEnv_bddAbove H pred hvchk)
    (⟨(u, s), hu, hs⟩ : {p : U × (X → ℝ) // p.1 ∈ H ∧ ∀ x, 0 < p.2 x})

lemma nullEnv_pos (hH : H.Nonempty) (hvchk : ∀ x, 0 < batchVar r y x) :
    0 < nullEnv H pred r y := by
  obtain ⟨u, hu⟩ := hH
  exact (batchDens_pos r _ (fun _ => one_pos) y).trans_le
    (batchDens_le_nullEnv hvchk hu (s := fun _ => 1) (fun _ => one_pos))

private lemma profSum_bddBelow (hvchk : ∀ x, 0 < batchVar r y x) (hvh : ∀ x, 0 < vh x) :
    BddBelow (Set.range fun u : H => profSum pred r y muh vh (u : U)) := by
  refine ⟨logQ r y muh vh - ∑ x, (r x : ℝ) * (-(1 / 2) * (Real.log (2 * Real.pi) + 1) -
      1 / 2 * Real.log (batchVar r y x)), ?_⟩
  rintro _ ⟨u, rfl⟩
  show _ ≤ profSum pred r y muh vh (u : U)
  rw [profSum_eq hvchk hvh]
  have := logProf_le (pred := pred) hvchk (u : U)
  linarith

/-- **Maximum-likelihood profiling of the null envelope.**
`U(y) = q(y) · exp (-inf_{u ∈ H} ∑ₓ rₓ ½ profBracket)`: the supremum over the null variance
vector is taken coordinatewise inside the product over query types, and the remaining
supremum over `u ∈ H` of the profiled likelihood is the exponential of an infimum.  Equivalent
to the manuscript's display for `log U_{a,z,i}(Y_i)`. -/
theorem nullEnv_eq_exp (hH : H.Nonempty) (hvchk : ∀ x, 0 < batchVar r y x)
    (hvh : ∀ x, 0 < vh x) :
    nullEnv H pred r y =
      Real.exp (logQ r y muh vh - ⨅ u : H, profSum pred r y muh vh (u : U)) := by
  have hne : Nonempty {p : U × (X → ℝ) // p.1 ∈ H ∧ ∀ x, 0 < p.2 x} := by
    obtain ⟨u, hu⟩ := hH
    exact ⟨⟨(u, fun _ => 1), hu, fun _ => one_pos⟩⟩
  have hneH : Nonempty H := hH.to_subtype
  have hbdd := profSum_bddBelow (H := H) (pred := pred) (muh := muh) hvchk hvh
  have hUpos : 0 < nullEnv H pred r y := nullEnv_pos hH hvchk
  apply le_antisymm
  · refine ciSup_le fun p => ?_
    refine (batchDens_le_prof hvchk p.1.1 p.2.2).trans (Real.exp_le_exp.mpr ?_)
    have h1 : (⨅ u : H, profSum pred r y muh vh (u : U)) ≤ profSum pred r y muh vh p.1.1 :=
      ciInf_le hbdd (⟨p.1.1, p.2.1⟩ : H)
    rw [profSum_eq hvchk hvh] at h1
    linarith
  · have hI : logQ r y muh vh - Real.log (nullEnv H pred r y) ≤
        ⨅ u : H, profSum pred r y muh vh (u : U) := by
      refine le_ciInf fun u => ?_
      have h1 : Real.exp (logProf pred r y (u : U)) ≤ nullEnv H pred r y := by
        rw [← batchDens_prof_eq hvchk]
        exact batchDens_le_nullEnv hvchk u.2 (fun x => by have := hvchk x; positivity)
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp] at h2
      rw [profSum_eq hvchk hvh]
      linarith
    calc Real.exp (logQ r y muh vh - ⨅ u : H, profSum pred r y muh vh (u : U))
        ≤ Real.exp (Real.log (nullEnv H pred r y)) := Real.exp_le_exp.mpr (by linarith)
      _ = nullEnv H pred r y := Real.exp_log hUpos

/-- **Identification of the profiled statistic with the batch log-likelihood ratio
(Lemma `lem:v34-batch-comparison`, first step of the proof).**  For a batch with sizes `r`,
total size `R = ∑ₓ rₓ`, plug-in predictor `q = batchDens r μ̂ v̂` and null envelope
`U = nullEnv H pred r`, if `H` is nonempty, every within-batch centered variance is positive
(which forces `rₓ ≥ 2`) and `v̂ₓ > 0`, then
`R⁻¹ log (q(y) / U(y)) = profStat H pred (r / R) Ȳ v̌ μ̂ v̂`. -/
theorem batch_loglik_identification (hH : H.Nonempty) (hvchk : ∀ x, 0 < batchVar r y x)
    (hvh : ∀ x, 0 < vh x) :
    (∑ x, (r x : ℝ))⁻¹ * Real.log (batchDens r muh vh y / nullEnv H pred r y) =
      profStat H pred (fun x => (r x : ℝ) / ∑ x, (r x : ℝ)) (batchMean r y) (batchVar r y)
        muh vh := by
  have hq : batchDens r muh vh y = Real.exp (logQ r y muh vh) := batchDens_eq_exp r _ hvh y
  rw [nullEnv_eq_exp (muh := muh) hH hvchk hvh, hq, ← Real.exp_sub, Real.log_exp, sub_sub_cancel]
  unfold profStat
  rw [Real.mul_iInf_of_nonneg (inv_nonneg.mpr (sum_nonneg fun x _ => Nat.cast_nonneg _))]
  congr 1
  funext u
  unfold profSum
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- **A uniform batch log-likelihood comparison (Lemma `lem:v34-batch-comparison`), as
stated.**  `μ, v` are the true query means and variances, `v_min ≤ vₓ`, and
`ρ ≤ min {1, v_min / 8}`.  If for every query type the within-batch mean and centered variance
and the predictable estimates `μ̂ₓ, v̂ₓ` are within `ρ` of the corresponding true mean or
variance, then for the component null `H` (nonempty)
`|R⁻¹ log (q(Y) / U(Y)) - C_{a,z}(w̃; μ, v)| ≤ L₀ ρ` with `w̃ₓ = rₓ / R`.
There is no hypothesis beyond those of the manuscript: positivity of `v̌` and `v̂` follows from
the `ρ`-closeness. -/
theorem batch_comparison_loglik [Nonempty X] (hH : H.Nonempty) {μ v : X → ℝ} {vmin ρ : ℝ}
    (hvmin : 0 < vmin) (hv : ∀ x, vmin ≤ v x) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρv : ρ ≤ vmin / 8)
    (h1 : ∀ x, |batchMean r y x - μ x| ≤ ρ) (h2 : ∀ x, |batchVar r y x - v x| ≤ ρ)
    (h3 : ∀ x, |muh x - μ x| ≤ ρ) (h4 : ∀ x, |vh x - v x| ≤ ρ) :
    |(∑ x, (r x : ℝ))⁻¹ * Real.log (batchDens r muh vh y / nullEnv H pred r y) -
        compGame H pred (fun x => (r x : ℝ) / ∑ x, (r x : ℝ)) μ v| ≤ L0 vmin * ρ := by
  have hvchk : ∀ x, 0 < batchVar r y x := fun x => by
    have := (abs_le.mp (h2 x)).1
    have := hv x
    linarith
  have hvh : ∀ x, 0 < vh x := fun x => by
    have := (abs_le.mp (h4 x)).1
    have := hv x
    linarith
  have hr : ∀ x, 0 < r x := fun x => by
    rcases Nat.eq_zero_or_pos (r x) with h0 | hpos
    · have := hvchk x
      simp [batchVar, h0] at this
    · exact hpos
  have hR : 0 < ∑ x, (r x : ℝ) :=
    sum_pos (fun x _ => by exact_mod_cast hr x) univ_nonempty
  have hw : (fun x => (r x : ℝ) / ∑ x, (r x : ℝ)) ∈ simplex X :=
    ⟨fun x => div_nonneg (Nat.cast_nonneg _) hR.le, by rw [← sum_div, div_self hR.ne']⟩
  rw [batch_loglik_identification hH hvchk hvh]
  exact batch_comparison H pred hw hvmin hv hρ0 hρ1 hρv h1 h2 h3 h4

end Identification

end BatchDensity

/-! ### Conditioning on the past of a function of the past and a fresh batch -/

section Freeze

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {T : Type*} [MeasurableSpace T]

/-- **Freezing lemma.**  If `ξ` is independent of the sub-σ-algebra `m` and `G` is jointly
measurable with respect to `m ⊗ borel`, then
`E[G(ω, ξ ω)] = E[∫ G(ω, y) d(law ξ)(y)]`: the fresh variable is integrated out with the
past frozen. -/
theorem lintegral_freeze (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm : m ≤ m0) {ξ : Ω → T} (hξ : Measurable ξ)
    (hind : Indep m (MeasurableSpace.comap ξ inferInstance) μ)
    {G : Ω × T → ℝ≥0∞} (hG : Measurable[m.prod inferInstance] G) :
    ∫⁻ ω, G (ω, ξ ω) ∂μ = ∫⁻ ω, ∫⁻ y, G (ω, y) ∂(μ.map ξ) ∂μ := by
  have hid : @Measurable Ω Ω m0 m id := measurable_id'' hm
  have hindf : @IndepFun Ω Ω T m0 m _ id ξ μ := by
    refine (IndepFun_iff_Indep (mβ := m) id ξ μ).mpr ?_
    rw [MeasurableSpace.comap_id]
    exact hind
  have hpair : @Measurable Ω (Ω × T) m0 (m.prod inferInstance) (fun ω => (id ω, ξ ω)) :=
    hid.prodMk hξ
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (mβ := m) (f := id) (g := ξ) (μ := μ)
    (@Measurable.aemeasurable Ω Ω m0 m id μ hid) hξ.aemeasurable).mp hindf
  have h1 : ∫⁻ ω, G (ω, ξ ω) ∂μ =
      ∫⁻ p, G p ∂(@Measure.map Ω (Ω × T) m0 (m.prod inferInstance) (fun ω => (id ω, ξ ω)) μ) :=
    (@lintegral_map Ω (Ω × T) m0 (m.prod inferInstance) μ G _ hG hpair).symm
  rw [h1, hmap, @lintegral_prod Ω T m _ _ _ _ G hG.aemeasurable, ← trim_eq_map hm,
    lintegral_trim hm (@Measurable.lintegral_prod_right' Ω T m _ _ _ G hG)]

/-- Freezing inequality: if every section of `Φ` integrates to at most one against the law of
the fresh variable `ξ`, then multiplying by `Φ (ω, ξ ω)` does not increase the integral of an
`m`-measurable weight. -/
theorem lintegral_mul_freeze_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm : m ≤ m0) {ξ : Ω → T} (hξ : Measurable ξ)
    (hind : Indep m (MeasurableSpace.comap ξ inferInstance) μ)
    {Φ : Ω × T → ℝ≥0∞} (hΦ : Measurable[m.prod inferInstance] Φ)
    (hone : ∀ ω, ∫⁻ y, Φ (ω, y) ∂(μ.map ξ) ≤ 1) {g : Ω → ℝ≥0∞} (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * Φ (ω, ξ ω) ∂μ ≤ ∫⁻ ω, g ω ∂μ := by
  have hG : Measurable[m.prod inferInstance] (fun p : Ω × T => g p.1 * Φ p) :=
    Measurable.mul (m := m.prod inferInstance) (hg.comp (@measurable_fst Ω T m _)) hΦ
  have h := lintegral_freeze μ hm hξ hind hG
  refine (le_of_eq h).trans (lintegral_mono fun ω => ?_)
  have hsec : Measurable fun y => Φ (ω, y) := hΦ.comp (@measurable_prodMk_left Ω T m _ ω)
  show ∫⁻ y, g ω * Φ (ω, y) ∂(μ.map ξ) ≤ g ω
  rw [lintegral_const_mul _ hsec]
  calc g ω * ∫⁻ y, Φ (ω, y) ∂(μ.map ξ) ≤ g ω * 1 := by gcongr; exact hone ω
    _ = g ω := mul_one _

end Freeze

/-! ### Concentration of a fresh batch of predictable size -/

section FreshBatch

variable {Ω : Type*} {m m0 : MeasurableSpace Ω}

/-- The statistics of the first `n` entries of a tape `t` are `r`-bad: the mean or the
centered variance (denominator `n`) is more than `r` away from `(μ, v)`. -/
def tapeBad (μ v r : ℝ) (n : ℕ) (t : ℕ → ℝ) : Prop :=
  r < |(∑ i ∈ range n, t i) / n - μ| ∨
    r < |(∑ i ∈ range n, (t i - (∑ j ∈ range n, t j) / n) ^ 2) / n - v|

lemma measurableSet_tapeBad (μ v r : ℝ) (n : ℕ) : MeasurableSet {t | tapeBad μ v r n t} := by
  have h1 : Measurable fun t : ℕ → ℝ => |(∑ i ∈ range n, t i) / n - μ| := by fun_prop
  have h2 : Measurable fun t : ℕ → ℝ =>
      |(∑ i ∈ range n, (t i - (∑ j ∈ range n, t j) / n) ^ 2) / n - v| := by fun_prop
  exact (measurableSet_lt measurable_const h1).union (measurableSet_lt measurable_const h2)

/-- The explicit tail `Q(n, r)` is nonincreasing in `n` beyond the onset `n₀`. -/
lemma Qtail_anti {v r : ℝ} (hv : 0 < v) {b k : ℕ} (hb0 : n0 v r ≤ b) (hbk : b ≤ k) :
    Qtail v k r ≤ Qtail v b r := by
  have hb3 : 3 ≤ b := (le_max_left _ _).trans hb0
  have hkb : (b : ℝ) ≤ k := by exact_mod_cast hbk
  unfold Qtail
  simp only [not_lt.mpr hb0, not_lt.mpr (hb0.trans hbk), ↓reduceIte]
  refine min_le_min le_rfl (add_le_add ?_ ?_)
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (by norm_num)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkb (sq_nonneg r))
      (by positivity)
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (by norm_num)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)) (by positivity)

/-- **Concentration of a fresh batch of predictable size (the second term of
`eq:v34-explicit-tail`).**  `T` is a tape of independent `N(μ, v)` observations, independent of
the past `m`; the batch reads its first `n ω` entries, where the size `n` is `m`-measurable
(predictable) and at least `b ≥ n₀(v, r)`.  Then the probability that the batch mean or the
batch centered variance is more than `r` away from `(μ, v)` is at most `Q(b, r)`.  The size
is frozen by `lintegral_freeze`; there is no conditioning on an adaptively selected sample
size. -/
theorem fresh_batch_concentration (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    {T : Ω → ℕ → ℝ} (hT : Measurable T)
    (hfresh : Indep m (MeasurableSpace.comap T inferInstance) P) {μ v r : ℝ} (hv : 0 < v)
    (hr0 : 0 < r) (hrv : r ≤ v / 8) (hind : iIndepFun (fun ℓ ω => T ω ℓ) P)
    (hlaw : ∀ ℓ, HasLaw (fun ω => T ω ℓ) (gaussianReal μ v.toNNReal) P)
    {n : Ω → ℕ} (hn : Measurable[m] n) {b : ℕ} (hb : ∀ ω, b ≤ n ω) (hb0 : n0 v r ≤ b) :
    P {ω | tapeBad μ v r (n ω) (T ω)} ≤ ENNReal.ofReal (Qtail v b r) := by
  classical
  set g : ℕ × (ℕ → ℝ) → ℝ≥0∞ := fun q => {t | tapeBad μ v r q.1 t}.indicator 1 q.2 with hg
  have hgm : Measurable g :=
    measurable_from_prod_countable_right fun k =>
      measurable_one.indicator (measurableSet_tapeBad μ v r k)
  set G : Ω × (ℕ → ℝ) → ℝ≥0∞ := fun p => g (n p.1, p.2) with hG
  have hGm : Measurable[m.prod inferInstance] G :=
    hgm.comp (Measurable.prodMk (m := m.prod inferInstance)
      (hn.comp (@measurable_fst Ω (ℕ → ℝ) m _)) (@measurable_snd Ω (ℕ → ℝ) m _))
  have hn0 : Measurable n := hn.mono hm le_rfl
  have hcomp : Measurable fun ω => G (ω, T ω) := hgm.comp (hn0.prodMk hT)
  have hval : ∀ ω, G (ω, T ω) = {ω | tapeBad μ v r (n ω) (T ω)}.indicator 1 ω := by
    intro ω
    simp only [hG, hg, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  have hE : MeasurableSet {ω | tapeBad μ v r (n ω) (T ω)} := by
    have : {ω | tapeBad μ v r (n ω) (T ω)} = (fun ω => G (ω, T ω)) ⁻¹' {1} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hval,
        Set.indicator, Pi.one_apply]
      by_cases h : tapeBad μ v r (n ω) (T ω) <;> simp [h]
    rw [this]
    exact hcomp (measurableSet_singleton 1)
  have hinner : ∀ ω, ∫⁻ y, G (ω, y) ∂(P.map T) ≤ ENNReal.ofReal (Qtail v b r) := by
    intro ω
    have h1 : ∫⁻ y, G (ω, y) ∂(P.map T) = P.map T {t | tapeBad μ v r (n ω) t} := by
      simp only [hG, hg]
      exact lintegral_indicator_one (measurableSet_tapeBad μ v r (n ω))
    rw [h1, Measure.map_apply hT (measurableSet_tapeBad μ v r (n ω))]
    have h2 := gaussian_concentration_fixed hv hr0 hrv (n ω) hind hlaw
    exact h2.trans (ENNReal.ofReal_le_ofReal (Qtail_anti hv hb0 (hb ω)))
  calc P {ω | tapeBad μ v r (n ω) (T ω)}
      = ∫⁻ ω, G (ω, T ω) ∂P := by
        rw [← lintegral_indicator_one hE]
        exact lintegral_congr fun ω => (hval ω).symm
    _ = ∫⁻ ω, ∫⁻ y, G (ω, y) ∂(P.map T) ∂P := lintegral_freeze P hm hT hfresh hGm
    _ ≤ ∫⁻ _ω, ENNReal.ofReal (Qtail v b r) ∂P := lintegral_mono hinner
    _ = ENNReal.ofReal (Qtail v b r) := by simp

end FreshBatch

/-! ### The one-step likelihood-ratio integral for a fresh Gaussian batch -/

section OneStep

variable {X : Type*} [Fintype X] {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_batchDens (r : X → ℕ) (t s : X → ℝ) : Measurable (batchDens r t s) := by
  unfold batchDens
  refine Finset.measurable_prod _ fun x _ => Finset.measurable_prod _ fun ℓ _ => ?_
  exact (measurable_gaussianPDFReal _ _).comp
    ((measurable_pi_apply ℓ).comp (measurable_pi_apply x))

/-- **One-step likelihood-ratio integral for a fresh Gaussian batch.**  `Y` is a tape of
independent observations, `Y · x ℓ ~ N(mₓ, vₓ)`; a batch with (deterministic) sizes `r` reads
the first `rₓ` entries of each type.  For every Gaussian batch density `q = batchDens r t s`
(`sₓ > 0`), `E[q(Y) / p(Y)] = 1`, where `p = batchDens r m v` is the true batch density.  This
is `∫ q(y) dy = 1` in the proof of Theorem `thm:v34-action-local`. -/
theorem lintegral_batch_ratio_eq_one (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → X → ℕ → ℝ} {m v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hind : iIndepFun (fun (p : X × ℕ) ω => Y ω p.1 p.2) P)
    (hlaw : ∀ x ℓ, HasLaw (fun ω => Y ω x ℓ) (gaussianReal (m x) (v x).toNNReal) P)
    (r : X → ℕ) (t : X → ℝ) {s : X → ℝ} (hs : ∀ x, 0 < s x) :
    ∫⁻ ω, ENNReal.ofReal (batchDens r t s (Y ω) / batchDens r m v (Y ω)) ∂P = 1 := by
  classical
  let I := Σ x, Fin (r x)
  let f : I → ℝ → ℝ := fun i a =>
    gaussianPDFReal (t i.1) (s i.1).toNNReal a / gaussianPDFReal (m i.1) (v i.1).toNNReal a
  have hinj : Function.Injective (fun i : I => ((i.1, (i.2 : ℕ)) : X × ℕ)) := by
    rintro ⟨x, a⟩ ⟨x', a'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have : a = a' := Fin.ext h2
    rw [this]
  have hW : HasLaw (fun ω (i : I) => Y ω i.1 i.2)
      (Measure.pi fun i : I => gaussianReal (m i.1) (v i.1).toNNReal) P :=
    iIndepFun.hasLaw_pi (fun i => hlaw i.1 i.2) (hind.precomp hinj)
  have hratio : ∀ y : X → ℕ → ℝ,
      batchDens r t s y / batchDens r m v y = ∏ i : I, f i (y i.1 i.2) := by
    intro y
    unfold batchDens
    rw [← Finset.prod_div_distrib, Fintype.prod_sigma]
    refine prod_congr rfl fun x _ => ?_
    rw [← Finset.prod_div_distrib]
    exact (Fin.prod_univ_eq_prod_range (fun ℓ => gaussianPDFReal (t x) (s x).toNNReal (y x ℓ) /
      gaussianPDFReal (m x) (v x).toNNReal (y x ℓ)) (r x)).symm
  have h1d : ∀ i : I, ∫ a, f i a ∂(gaussianReal (m i.1) (v i.1).toNNReal) = 1 := by
    intro i
    rw [integral_gaussianReal_eq_integral_smul (toNNReal_ne_zero_of_pos (hv i.1)),
      ← integral_gaussianPDFReal_eq_one (t i.1) (toNNReal_ne_zero_of_pos (hs i.1))]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    have hp := gaussianPDFReal_pos (m i.1) (v i.1).toNNReal a (toNNReal_ne_zero_of_pos (hv i.1))
    simp only [f, smul_eq_mul]
    field_simp
  have hint : ∫ w : I → ℝ, ∏ i, f i (w i)
      ∂(Measure.pi fun i : I => gaussianReal (m i.1) (v i.1).toNNReal) = 1 := by
    rw [integral_fintype_prod_eq_prod]
    simp [h1d]
  have hintble : Integrable (fun w : I → ℝ => ∏ i, f i (w i))
      (Measure.pi fun i : I => gaussianReal (m i.1) (v i.1).toNNReal) :=
    Integrable.of_integral_ne_zero (by rw [hint]; exact one_ne_zero)
  have hmeas : Measurable (fun w : I → ℝ => ENNReal.ofReal (∏ i, f i (w i))) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
    exact ((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)).comp
      (measurable_pi_apply i)
  have hnn : ∀ w : I → ℝ, 0 ≤ ∏ i, f i (w i) := fun w => prod_nonneg fun i _ =>
    div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
  calc ∫⁻ ω, ENNReal.ofReal (batchDens r t s (Y ω) / batchDens r m v (Y ω)) ∂P
      = ∫⁻ ω, (fun w : I → ℝ => ENNReal.ofReal (∏ i, f i (w i))) (fun i => Y ω i.1 i.2) ∂P := by
        simp only [hratio]
    _ = ∫⁻ w, ENNReal.ofReal (∏ i, f i (w i))
          ∂(Measure.pi fun i : I => gaussianReal (m i.1) (v i.1).toNNReal) :=
        hW.lintegral_comp hmeas.aemeasurable
    _ = ENNReal.ofReal (∫ w : I → ℝ, ∏ i, f i (w i)
          ∂(Measure.pi fun i : I => gaussianReal (m i.1) (v i.1).toNNReal)) :=
        (ofReal_integral_eq_lintegral_ofReal hintble (ae_of_all _ hnn)).symm
    _ = 1 := by rw [hint]; simp

end OneStep

/-! ### Action-local wealth in the Gaussian batch model (Theorem `thm:v34-action-local`) -/

section Helpers

lemma measurable_halfCash {α : Type*} {mα : MeasurableSpace α} {q U : α → ℝ}
    (hq : Measurable q) (hU : Measurable U) :
    Measurable fun p => halfCash (q p) (U p) := by
  unfold halfCash
  exact measurable_const.mul (measurable_const.add (hq.div hU))

lemma integrable_of_lintegral_ofReal_le_one {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (h0 : ∀ ω, 0 ≤ f ω)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ 1) : Integrable f μ :=
  ⟨hf, (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).mpr (h.trans_lt ENNReal.one_lt_top)⟩

end Helpers

section GaussianBatchModel

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {X : Type*} [Fintype X] {A : Type*}
  [DecidableEq A]

/-- **Action-local wealth is a nonnegative supermartingale in the Gaussian batch model
(Theorem `thm:v34-action-local`, first claim), with no conditional-expectation hypothesis.**

Model.  `ℱ i` is the information after batch `i`.  Batch `i + 1` is read from a fresh tape
`Y (i + 1) : Ω → X → ℕ → ℝ` of independent observations, `Y (i + 1) · x ℓ ~ N(meanₓ, vₓ)` with
`vₓ > 0`, independent of `ℱ i` and `ℱ (i + 1)`-measurable; the batch consists of the first
`r (i + 1) ω x` entries of each query type.  The selection event `{A_{i+1} = a}` is
`ℱ i`-measurable.  `qlo (i + 1)` and `Uhi (i + 1)` are the certified bounds for the fixed
action-component pair: jointly measurable functions of the past (`ℱ i`) and of the batch, with
`0 ≤ qlo ≤ q` for the plug-in Gaussian predictor `q = batchDens r μ̂ v̂` (`v̂ > 0`; the planned
sizes and the estimates may depend on the past in an arbitrary way) and `p ≤ Uhi` for the
true batch density `p = batchDens r mean v`.  Under a component null this last bound follows
from `Uhi ≥ sup_{u ∈ H, s > 0} p_{u,s}`; see `action_local_coverage_gaussian`.  The enclosures
are only required on the selection event.

Conclusion: the action-local wealth with factors `½ (1 + qlo(Y) / Uhi(Y))` is a
supermartingale.  Integrability of the factors and of the wealth is derived.  Nonnegativity
is `localWealth_nonneg` and the initial value `localWealth_zero`. -/
theorem gaussian_localWealth_supermartingale (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → X → ℕ → ℝ) {mean v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hYmeas : ∀ i, Measurable[ℱ (i + 1)] (Y (i + 1)))
    (hYfresh : ∀ i, Indep (ℱ i) (MeasurableSpace.comap (Y (i + 1)) inferInstance) μ)
    (hYind : ∀ i, iIndepFun (fun (p : X × ℕ) ω => Y (i + 1) ω p.1 p.2) μ)
    (hYlaw : ∀ i x ℓ,
      HasLaw (fun ω => Y (i + 1) ω x ℓ) (gaussianReal (mean x) (v x).toNNReal) μ)
    (sel : ℕ → Ω → A) (a : A) (hsel : ∀ i, MeasurableSet[ℱ i] {ω | sel (i + 1) ω = a})
    (r : ℕ → Ω → X → ℕ) (muh vh : ℕ → Ω → X → ℝ)
    (hvh : ∀ i ω x, sel (i + 1) ω = a → 0 < vh (i + 1) ω x)
    (qlo Uhi : ℕ → Ω → (X → ℕ → ℝ) → ℝ)
    (hqmeas : ∀ i, Measurable[(ℱ i).prod inferInstance]
      (fun p : Ω × (X → ℕ → ℝ) => qlo (i + 1) p.1 p.2))
    (hUmeas : ∀ i, Measurable[(ℱ i).prod inferInstance]
      (fun p : Ω × (X → ℕ → ℝ) => Uhi (i + 1) p.1 p.2))
    (hq0 : ∀ i ω y, sel (i + 1) ω = a → 0 ≤ qlo (i + 1) ω y)
    (hq : ∀ i ω y, sel (i + 1) ω = a →
      qlo (i + 1) ω y ≤ batchDens (r (i + 1) ω) (muh (i + 1) ω) (vh (i + 1) ω) y)
    (hU : ∀ i ω y, sel (i + 1) ω = a →
      batchDens (r (i + 1) ω) mean v y ≤ Uhi (i + 1) ω y) :
    Supermartingale (fun j ω => localWealth
      (fun i => halfCash (qlo i ω (Y i ω)) (Uhi i ω (Y i ω))) (fun i => sel i ω) a j) ℱ μ := by
  classical
  -- the factor as a function of the past and of the fresh tape
  set Φ : ℕ → Ω × (X → ℕ → ℝ) → ℝ := fun i p =>
    if sel (i + 1) p.1 = a then halfCash (qlo (i + 1) p.1 p.2) (Uhi (i + 1) p.1 p.2)
    else 1 with hΦdef
  have hΦmeas : ∀ i, Measurable[(ℱ i).prod inferInstance] (Φ i) := fun i =>
    Measurable.ite ((@measurable_fst Ω (X → ℕ → ℝ) (ℱ i) _) (hsel i))
      (measurable_halfCash (mα := (ℱ i).prod inferInstance) (hqmeas i) (hUmeas i))
      measurable_const
  have hΦ0 : ∀ i p, 0 ≤ Φ i p := by
    intro i p
    simp only [hΦdef]
    split_ifs with h
    · have h1 := hq0 i p.1 p.2 h
      have h2 := (batchDens_nonneg _ _ _ _).trans (hU i p.1 p.2 h)
      have := halfCash_ge_half h1 h2
      linarith
    · exact zero_le_one
  have hYm0 : ∀ i, Measurable (Y (i + 1)) := fun i => (hYmeas i).mono (ℱ.le _) le_rfl
  -- every section of the factor integrates to at most one against the law of the tape
  have hone : ∀ i ω, ∫⁻ y, ENNReal.ofReal (Φ i (ω, y)) ∂(μ.map (Y (i + 1))) ≤ 1 := by
    intro i ω
    have : IsProbabilityMeasure (μ.map (Y (i + 1))) :=
      (Measure.isProbabilityMeasure_map_iff (hYm0 i).aemeasurable).mpr inferInstance
    by_cases h : sel (i + 1) ω = a
    · have hvh' : ∀ x, 0 < vh (i + 1) ω x := fun x => hvh i ω x h
      have hbound : ∀ y, ENNReal.ofReal (Φ i (ω, y)) ≤
          ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) *
            ENNReal.ofReal (batchDens (r (i + 1) ω) (muh (i + 1) ω) (vh (i + 1) ω) y /
              batchDens (r (i + 1) ω) mean v y) := by
        intro y
        have hp : 0 < batchDens (r (i + 1) ω) mean v y := batchDens_pos _ _ hv y
        have hle : qlo (i + 1) ω y / Uhi (i + 1) ω y ≤
            batchDens (r (i + 1) ω) (muh (i + 1) ω) (vh (i + 1) ω) y /
              batchDens (r (i + 1) ω) mean v y :=
          div_le_div₀ (batchDens_nonneg _ _ _ _) (hq i ω y h) hp (hU i ω y h)
        have hr0 : 0 ≤ batchDens (r (i + 1) ω) (muh (i + 1) ω) (vh (i + 1) ω) y /
            batchDens (r (i + 1) ω) mean v y := div_nonneg (batchDens_nonneg _ _ _ _) hp.le
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num)
          (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hΦ : Φ i (ω, y) = halfCash (qlo (i + 1) ω y) (Uhi (i + 1) ω y) := by
          simp only [hΦdef]
          simp only [h, ↓reduceIte]
        rw [hΦ]
        unfold halfCash
        linarith
      have hm1 : Measurable fun y : X → ℕ → ℝ => ENNReal.ofReal
          (batchDens (r (i + 1) ω) (muh (i + 1) ω) (vh (i + 1) ω) y /
            batchDens (r (i + 1) ω) mean v y) :=
        ENNReal.measurable_ofReal.comp
          ((measurable_batchDens _ _ _).div (measurable_batchDens _ _ _))
      refine (lintegral_mono hbound).trans (le_of_eq ?_)
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ hm1, lintegral_const,
        lintegral_map hm1 (hYm0 i),
        lintegral_batch_ratio_eq_one μ hv (hYind i) (hYlaw i) (r (i + 1) ω) (muh (i + 1) ω) hvh',
        measure_univ, mul_one]
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    · have hΦ : ∀ y, Φ i (ω, y) = 1 := by
        intro y
        simp only [hΦdef]
        simp only [h, ↓reduceIte]
      simp [hΦ]
  -- the factors used by `localWealth_supermartingale`
  set Fn : ℕ → Ω → ℝ := fun i ω =>
    Nat.casesOn i 1 (fun k => Φ k (ω, Y (k + 1) ω)) with hFndef
  have hFn0 : ∀ ω, Fn 0 ω = 1 := fun ω => rfl
  have hFnS : ∀ k ω, Fn (k + 1) ω = Φ k (ω, Y (k + 1) ω) := fun k ω => rfl
  have hF0 : ∀ i ω, 0 ≤ Fn i ω := by
    intro i ω
    cases i with
    | zero => rw [hFn0]; exact zero_le_one
    | succ k => rw [hFnS]; exact hΦ0 k _
  have hFmeas : ∀ i, Measurable[ℱ i] (Fn i) := by
    intro i
    cases i with
    | zero =>
      have : Fn 0 = fun _ => 1 := funext hFn0
      rw [this]; exact measurable_const
    | succ k =>
      have hpair : @Measurable Ω (Ω × (X → ℕ → ℝ)) (ℱ (k + 1)) ((ℱ k).prod inferInstance)
          (fun ω => (id ω, Y (k + 1) ω)) :=
        (measurable_id'' (ℱ.mono (Nat.le_succ k))).prodMk (hYmeas k)
      exact (hΦmeas k).comp hpair
  have hFad : ∀ i, StronglyMeasurable[ℱ i] (Fn i) := fun i => (hFmeas i).stronglyMeasurable
  -- freezing
  have hfrz : ∀ i (g : Ω → ℝ≥0∞), Measurable[ℱ i] g →
      ∫⁻ ω, g ω * ENNReal.ofReal (Fn (i + 1) ω) ∂μ ≤ ∫⁻ ω, g ω ∂μ := by
    intro i g hg
    exact lintegral_mul_freeze_le μ (ℱ.le i) (hYm0 i) (hYfresh i)
      (Φ := fun p => ENNReal.ofReal (Φ i p))
      (ENNReal.measurable_ofReal.comp (hΦmeas i)) (hone i) hg
  have hFm0 : ∀ i, Measurable (Fn i) := fun i => (hFmeas i).mono (ℱ.le i) le_rfl
  have hFint : ∀ i, Integrable (Fn i) μ := by
    intro i
    refine integrable_of_lintegral_ofReal_le_one (hFm0 i).aestronglyMeasurable (hF0 i) ?_
    cases i with
    | zero => simp [hFn0]
    | succ k =>
      have := hfrz k (fun _ => 1) measurable_const
      simpa using this
  -- the wealth
  set W : ℕ → Ω → ℝ := fun j ω => localWealth (fun i => Fn i ω) (fun i => sel i ω) a j with hW
  have hWsucc : ∀ j ω, W (j + 1) ω = W j ω * Fn (j + 1) ω := by
    intro j ω
    simp only [hW]
    rw [localWealth_succ]
    congr 1
    split_ifs with h
    · rfl
    · rw [hFnS]
      simp only [hΦdef]
      simp only [h, ↓reduceIte]
  have hW0 : ∀ j ω, 0 ≤ W j ω := fun j ω => localWealth_nonneg (fun i => hF0 i ω) j
  have hWmeas : ∀ j, Measurable[ℱ j] (W j) := by
    intro j
    induction j with
    | zero =>
      have : W 0 = fun _ => 1 := by funext ω; simp [hW]
      rw [this]; exact measurable_const
    | succ j ih =>
      have : W (j + 1) = fun ω => W j ω * Fn (j + 1) ω := funext (hWsucc j)
      rw [this]
      exact (ih.mono (ℱ.mono (Nat.le_succ j)) le_rfl).mul (hFmeas (j + 1))
  have hWle : ∀ j, ∫⁻ ω, ENNReal.ofReal (W j ω) ∂μ ≤ 1 := by
    intro j
    induction j with
    | zero => simp [hW]
    | succ j ih =>
      have h1 : ∀ ω, ENNReal.ofReal (W (j + 1) ω) =
          ENNReal.ofReal (W j ω) * ENNReal.ofReal (Fn (j + 1) ω) := fun ω => by
        rw [hWsucc, ENNReal.ofReal_mul (hW0 j ω)]
      simp only [h1]
      exact (hfrz j _ (ENNReal.measurable_ofReal.comp (hWmeas j))).trans ih
  have hWint : ∀ j, Integrable (W j) μ := fun j =>
    integrable_of_lintegral_ofReal_le_one
      ((hWmeas j).mono (ℱ.le j) le_rfl).aestronglyMeasurable (hW0 j) (hWle j)
  -- conditional expectation of the next factor is at most one
  have hcond : ∀ i, ∀ᵐ ω ∂μ, sel (i + 1) ω = a → (μ[Fn (i + 1)|ℱ i]) ω ≤ 1 := by
    intro i
    set c := μ[Fn (i + 1)|ℱ i] with hc
    have hcsm : StronglyMeasurable[ℱ i] c := stronglyMeasurable_condExp
    set B : Set Ω := c ⁻¹' Set.Ioi 1 with hBdef
    have hB : MeasurableSet[ℱ i] B := hcsm.measurable measurableSet_Ioi
    have hB0 : MeasurableSet B := ℱ.le i _ hB
    have hcint : Integrable c μ := integrable_condExp
    have h1 : ∫ ω in B, c ω ∂μ = ∫ ω in B, Fn (i + 1) ω ∂μ :=
      setIntegral_condExp (ℱ.le i) (hFint (i + 1)) hB
    have h2 : ∫ ω in B, Fn (i + 1) ω ∂μ ≤ μ.real B := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hF0 (i + 1)))
        (hFm0 (i + 1)).aestronglyMeasurable]
      refine ENNReal.toReal_mono (measure_ne_top μ B) ?_
      have h3 := hfrz i (B.indicator fun _ => 1) (measurable_const.indicator hB)
      rw [lintegral_indicator hB0, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, one_mul] at h3
      refine le_trans (le_of_eq ?_) h3
      rw [← lintegral_indicator hB0]
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ B
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    have h3 : ∫ ω in B, (c ω - 1) ∂μ ≤ 0 := by
      rw [integral_sub hcint.integrableOn (integrableOn_const (measure_ne_top μ B)),
        setIntegral_const, smul_eq_mul, mul_one]
      linarith
    have h4 : 0 ≤ᵐ[μ.restrict B] fun ω => c ω - 1 :=
      ae_restrict_of_forall_mem hB0 fun ω hω => (sub_pos.mpr hω).le
    have h5 : ∫ ω in B, (c ω - 1) ∂μ = 0 :=
      le_antisymm h3 (integral_nonneg_of_ae h4)
    have h6 := (setIntegral_eq_zero_iff_of_nonneg_ae h4
      (hcint.integrableOn.sub (integrableOn_const (measure_ne_top μ B)))).mp h5
    have h7 := (ae_restrict_iff' hB0).mp h6
    filter_upwards [h7] with ω hω _
    by_contra hlt
    have hmem : ω ∈ B := not_le.mp hlt
    have := hω hmem
    simp only [Pi.zero_apply] at this
    have h8 : 1 < c ω := hmem
    linarith
  have hsm := localWealth_supermartingale μ ℱ Fn sel a hF0 hFad hsel hFint hWint hcond
  have hEq : (fun j ω => localWealth
      (fun i => halfCash (qlo i ω (Y i ω)) (Uhi i ω (Y i ω))) (fun i => sel i ω) a j) = W := by
    funext j ω
    simp only [hW]
    unfold localWealth
    refine prod_congr rfl fun i hi => ?_
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := (Finset.mem_Icc.mp hi).1; omega⟩
    split_ifs with h
    · show halfCash (qlo (k + 1) ω (Y (k + 1) ω)) (Uhi (k + 1) ω (Y (k + 1) ω)) = Fn (k + 1) ω
      rw [hFnS]
      simp only [hΦdef]
      simp only [h, ↓reduceIte]
    · rfl
  rw [hEq]
  exact hsm

/-- **Action-local optional evaluation and intersection-union root coverage
(Theorem `thm:v34-action-local`), for the Gaussian batch model.**

Model (as in `gaussian_localWealth_supermartingale`): the true parameter is `θ`, the query
means are `pred x θ` (`pred x u` stands for `hₓᵀ u`), the query variances `vₓ > 0` are
arbitrary; batch `i + 1` is read from a fresh tape of independent `N(pred x θ, vₓ)`
observations, independent of the past `ℱ i`.  The selected action `sel (i + 1)`, the batch
sizes `r (i + 1)` and the predictor estimates `(μ̂, v̂)` (with `v̂ > 0`) depend on the past in
an arbitrary way; the selection events are `ℱ i`-measurable.  For an incorrect action
`a ∈ bad`, `zstar a ∈ J a` is a component whose closed null `H a (zstar a)` contains `θ`.
Certified bounds, required on the selection event only: `0 ≤ qlo ≤ q` (plug-in Gaussian
predictor `q = batchDens r μ̂ v̂`), and `Uhi a z ≥ p_{u,s}` for every `u ∈ H a z` and every
positive variance vector `s` (that is, `Uhi ≥ U_{a,z}` in `[0, ∞]`); both jointly measurable
in the past and the batch.  No accuracy of the predictor, of the enclosures or of the
selection is assumed.

Conclusion: the probability that at some batch the selected action is incorrect and passes
the minimum-over-components test `∀ z ∈ J_{A_j}, E^loc_{A_j,z}(j) ≥ K / δ`, `K = |A|`, is at
most `δ`.  The error is `δ / K` per root action, with no union over components. -/
theorem action_local_coverage_gaussian [Fintype A] {U Z : Type*} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (pred : X → U → ℝ) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x) (Y : ℕ → Ω → X → ℕ → ℝ)
    (hYmeas : ∀ i, Measurable[ℱ (i + 1)] (Y (i + 1)))
    (hYfresh : ∀ i, Indep (ℱ i) (MeasurableSpace.comap (Y (i + 1)) inferInstance) μ)
    (hYind : ∀ i, iIndepFun (fun (p : X × ℕ) ω => Y (i + 1) ω p.1 p.2) μ)
    (hYlaw : ∀ i x ℓ,
      HasLaw (fun ω => Y (i + 1) ω x ℓ) (gaussianReal (pred x θ) (v x).toNNReal) μ)
    (J : A → Finset Z) (H : A → Z → Set U) (bad : Finset A) (zstar : A → Z)
    (hz : ∀ a ∈ bad, zstar a ∈ J a) (hθ : ∀ a ∈ bad, θ ∈ H a (zstar a))
    (sel : ℕ → Ω → A) (hsel : ∀ a ∈ bad, ∀ i, MeasurableSet[ℱ i] {ω | sel (i + 1) ω = a})
    (r : ℕ → Ω → X → ℕ) (muh vh : ℕ → Ω → X → ℝ) (hvh : ∀ i ω x, 0 < vh (i + 1) ω x)
    (qlo : ℕ → Ω → (X → ℕ → ℝ) → ℝ) (Uhi : A → Z → ℕ → Ω → (X → ℕ → ℝ) → ℝ)
    (hqmeas : ∀ i, Measurable[(ℱ i).prod inferInstance]
      (fun p : Ω × (X → ℕ → ℝ) => qlo (i + 1) p.1 p.2))
    (hUmeas : ∀ a ∈ bad, ∀ i, Measurable[(ℱ i).prod inferInstance]
      (fun p : Ω × (X → ℕ → ℝ) => Uhi a (zstar a) (i + 1) p.1 p.2))
    (hq0 : ∀ i ω y, 0 ≤ qlo (i + 1) ω y)
    (hq : ∀ i ω y,
      qlo (i + 1) ω y ≤ batchDens (r (i + 1) ω) (muh (i + 1) ω) (vh (i + 1) ω) y)
    (hU : ∀ a ∈ bad, ∀ i ω y, sel (i + 1) ω = a → ∀ u ∈ H a (zstar a), ∀ s : X → ℝ,
      (∀ x, 0 < s x) →
        batchDens (r (i + 1) ω) (fun x => pred x u) s y ≤ Uhi a (zstar a) (i + 1) ω y)
    {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ j, sel j ω ∈ bad ∧ ∀ z ∈ J (sel j ω), (Fintype.card A : ℝ) / δ ≤
        localWealth (fun i => halfCash (qlo i ω (Y i ω)) (Uhi (sel j ω) z i ω (Y i ω)))
          (fun i => sel i ω) (sel j ω) j} ≤ ENNReal.ofReal δ := by
  refine intersection_union_coverage μ J
    (fun a z j ω => localWealth (fun i => halfCash (qlo i ω (Y i ω)) (Uhi a z i ω (Y i ω)))
      (fun i => sel i ω) a j) sel bad zstar hz hδ.le (fun a ha => ?_)
  have hK : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  have hsm := gaussian_localWealth_supermartingale μ ℱ Y hv hYmeas hYfresh hYind hYlaw sel a
    (hsel a ha) r muh vh (fun i ω x _ => hvh i ω x) qlo (Uhi a (zstar a)) hqmeas
    (hUmeas a ha) (fun i ω y _ => hq0 i ω y) (fun i ω y _ => hq i ω y)
    (fun i ω y h => hU a ha i ω y h θ (hθ a ha) v hv)
  have hnn : ∀ j ω, 0 ≤ localWealth
      (fun i => halfCash (qlo i ω (Y i ω)) (Uhi a (zstar a) i ω (Y i ω)))
      (fun i => sel i ω) a j := by
    intro j ω
    unfold localWealth
    refine prod_nonneg fun i hi => ?_
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := (Finset.mem_Icc.mp hi).1; omega⟩
    split_ifs with h
    · have h1 := hq0 k ω (Y (k + 1) ω)
      have h2 := (batchDens_nonneg _ _ _ _).trans
        (hU a ha k ω (Y (k + 1) ω) h θ (hθ a ha) v hv)
      have := halfCash_ge_half h1 h2
      linarith
    · exact zero_le_one
  have hvl := ville_ineq hsm hnn (c := (Fintype.card A : ℝ) / δ) (by positivity)
  refine hvl.trans (le_of_eq ?_)
  congr 1
  simp only [localWealth_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [one_div_div]

end GaussianBatchModel

end

end JointRootCert
