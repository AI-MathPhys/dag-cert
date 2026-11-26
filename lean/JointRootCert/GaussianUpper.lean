/-
# Known-variance Gaussian information limit: pieces of the upper bound

Manuscript result: `thm:bay-main-optimal` (Correlated Gaussian information limit), upper
half, paragraphs "Regularity of the information game" and "Expected upper bound".

Proved here:

* `rootInfo_joint_continuous`: joint continuity of `(θ, w) ↦ √(2 I_a(θ, w))` on
  `E × Δ(X)`, including singular designs;
* `upper_half_of_pathwise`: the step "dividing the expectation by `log(1/δ)` and then
  sending `s ↓ 0`", from the pathwise bound
  `τ_δ ≤ max {T_s, ⌈log(1/δ) / (I_* - 2s)⌉}` with `T_s` integrable.

Not proved here: the tracking rule as a formal adaptive procedure, the concentration of
its estimator, and the stabilization of the selected action, which together supply the
integrable times `T_s`.
-/
import JointRootCert.GaussianInfo

namespace JointRootCert

open Finset MeasureTheory
open scoped ENNReal RealInnerProductSpace

section JointContinuity

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Raising each design weight by at most `δ` raises `‖v‖²_{M(w)}` by at most
`δ |X| (ℓ ‖v‖)²`. -/
lemma norm_designMap_sq_perturb (u : X → E) {w w' : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hw' : ∀ x, 0 ≤ w' x) {δ ℓ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ x, w' x - w x ≤ δ)
    (hu : ∀ x, ‖u x‖ ≤ ℓ) (v : E) :
    ‖designMap u w' v‖ ^ 2 ≤ ‖designMap u w v‖ ^ 2 + δ * Fintype.card X * (ℓ * ‖v‖) ^ 2 := by
  rw [norm_designMap_sq u hw, norm_designMap_sq u hw']
  have hsq : ∀ x, ⟪u x, v⟫ ^ 2 ≤ (ℓ * ‖v‖) ^ 2 := fun x => by
    have h1 := abs_real_inner_le_norm (u x) v
    have h2 : ‖u x‖ * ‖v‖ ≤ ℓ * ‖v‖ := mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
    exact sq_le_sq' (by linarith [neg_abs_le ⟪u x, v⟫]) (by linarith [le_abs_self ⟪u x, v⟫])
  calc ∑ x, w' x * ⟪u x, v⟫ ^ 2 ≤ ∑ x, (w x * ⟪u x, v⟫ ^ 2 + δ * (ℓ * ‖v‖) ^ 2) := by
        refine sum_le_sum (fun x _ => ?_)
        have h1 : (w' x - w x) * ⟪u x, v⟫ ^ 2 ≤ δ * ⟪u x, v⟫ ^ 2 :=
          mul_le_mul_of_nonneg_right (hδ x) (sq_nonneg _)
        have h2 : δ * ⟪u x, v⟫ ^ 2 ≤ δ * (ℓ * ‖v‖) ^ 2 := mul_le_mul_of_nonneg_left (hsq x) hδ0
        linarith
    _ = ∑ x, w x * ⟪u x, v⟫ ^ 2 + δ * Fintype.card X * (ℓ * ‖v‖) ^ 2 := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
        ring

/-- If every positive weight of `w` is at least `w_min` and `w'` is below `w` by at most
`δ` in each coordinate, then `M(w') ⪰ (1 - δ / w_min) M(w)` (the manuscript's
`M(w_n) ⪰ c_n M(w)`). -/
lemma norm_designMap_sq_lower (u : X → E) {w w' : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hw' : ∀ x, 0 ≤ w' x) {δ wmin : ℝ} (hwmin : 0 < wmin) (hmin : ∀ x, w x = 0 ∨ wmin ≤ w x)
    (hδ0 : 0 ≤ δ) (hδ : ∀ x, w x - w' x ≤ δ) (v : E) :
    (1 - δ / wmin) * ‖designMap u w v‖ ^ 2 ≤ ‖designMap u w' v‖ ^ 2 := by
  rw [norm_designMap_sq u hw, norm_designMap_sq u hw', mul_sum]
  refine sum_le_sum (fun x _ => ?_)
  have hx : (1 - δ / wmin) * w x ≤ w' x := by
    rcases hmin x with h0 | hpos
    · rw [h0, mul_zero]
      exact hw' x
    · have h1 : δ ≤ δ / wmin * w x := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hwmin]
        exact mul_le_mul_of_nonneg_left hpos hδ0
      have := hδ x
      linarith
  calc (1 - δ / wmin) * (w x * ⟪u x, v⟫ ^ 2) = ((1 - δ / wmin) * w x) * ⟪u x, v⟫ ^ 2 := by ring
    _ ≤ w' x * ⟪u x, v⟫ ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)

lemma exists_min_pos_weight (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ∃ wmin : ℝ, 0 < wmin ∧ ∀ x, w x = 0 ∨ wmin ≤ w x := by
  classical
  by_cases h : (univ.filter (fun x => 0 < w x)).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image _ w h
    refine ⟨w x0, (mem_filter.mp hx0).2, fun x => ?_⟩
    rcases (hw x).eq_or_lt with h0 | hpos
    · left; exact h0.symm
    · right; exact hmin x (mem_filter.mpr ⟨mem_univ x, hpos⟩)
  · refine ⟨1, one_pos, fun x => Or.inl ?_⟩
    by_contra hne
    exact h ⟨x, mem_filter.mpr ⟨mem_univ x, lt_of_le_of_ne (hw x) (Ne.symm hne)⟩⟩

/-- **Joint continuity of the information** (`thm:bay-main-optimal`, "Regularity of the
information game": `I_a(θ, w)` is jointly continuous, including on singular designs).
Stated for the root `√(2 I_a(θ, w)) = rootInfo (designMap u w) Q θ` at an arbitrary point
`(θ, w)` of `E × Δ(X)`: for every `ε > 0` there is `δ > 0` such that
`|√(2 I_a(θ', w')) - √(2 I_a(θ, w))| < ε` whenever `w' ∈ Δ(X)`, `‖θ' - θ‖ ≤ δ` and
`|w'_x - w_x| ≤ δ` for all `x`.  As in the manuscript, the lower bound uses
`M(w') ⪰ c M(w)` with `c → 1` and the seminorm modulus, and the upper bound evaluates one
near-minimizer for `(θ, w)`; no positive-definiteness is assumed. -/
theorem rootInfo_joint_continuous (u : X → E) {ℓ : ℝ} (hu : ∀ x, ‖u x‖ ≤ ℓ) {Q : Set E}
    (hQ : Q.Nonempty) (θ : E) {w : X → ℝ} (hw : w ∈ simplex X) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ' : E, ∀ w' ∈ simplex X, ‖θ' - θ‖ ≤ δ → (∀ x, |w' x - w x| ≤ δ) →
      |rootInfo (designMap u w') Q θ' - rootInfo (designMap u w) Q θ| < ε := by
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hw.2
    simp at this
  obtain ⟨x0⟩ := hX
  have hℓ0 : 0 ≤ ℓ := (norm_nonneg (u x0)).trans (hu x0)
  obtain ⟨r, hrdef⟩ : ∃ r, r = rootInfo (designMap u w) Q θ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hrdef]; exact rootInfo_nonneg
  obtain ⟨wmin, hwmin, hmin⟩ := exists_min_pos_weight w hw.1
  obtain ⟨lam, hlam, hlamlt⟩ : ∃ lam ∈ Q, ‖designMap u w (lam - θ)‖ < r + ε / 4 := by
    have h0 : Metric.infDist (designMap u w θ) (designMap u w '' Q) < r + ε / 4 := by
      rw [hrdef]
      unfold rootInfo
      linarith
    obtain ⟨_, ⟨lam, hl, rfl⟩, hd⟩ := (Metric.infDist_lt_iff (hQ.image (designMap u w))).mp h0
    exact ⟨lam, hl, by rwa [dist_map_eq] at hd⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = (Fintype.card X : ℝ) * (ℓ * ‖lam - θ‖) ^ 2 := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  obtain ⟨δ1, hδ1def⟩ : ∃ δ1, δ1 = (ε / 4) ^ 2 / (b + 1) := ⟨_, rfl⟩
  have hδ1 : 0 < δ1 := by rw [hδ1def]; positivity
  have hδ1b : δ1 * (b + 1) = (ε / 4) ^ 2 := by
    rw [hδ1def]
    exact div_mul_cancel₀ _ (by positivity)
  have hden2 : 0 < ℓ + (r + ℓ) / wmin + 1 := by positivity
  obtain ⟨δ2, hδ2def⟩ : ∃ δ2, δ2 = (ε / 2) / (ℓ + (r + ℓ) / wmin + 1) := ⟨_, rfl⟩
  have hδ2 : 0 < δ2 := by rw [hδ2def]; positivity
  have hδ2b : δ2 * (ℓ + (r + ℓ) / wmin + 1) = ε / 2 := by
    rw [hδ2def]
    exact div_mul_cancel₀ _ hden2.ne'
  refine ⟨min (min 1 wmin) (min δ1 δ2), lt_min (lt_min one_pos hwmin) (lt_min hδ1 hδ2), ?_⟩
  intro θ' w' hw' hθ' hww
  have hδpos : 0 < min (min 1 wmin) (min δ1 δ2) :=
    lt_min (lt_min one_pos hwmin) (lt_min hδ1 hδ2)
  have hδ_1 : min (min 1 wmin) (min δ1 δ2) ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ_w : min (min 1 wmin) (min δ1 δ2) ≤ wmin := (min_le_left _ _).trans (min_le_right _ _)
  have hδ_1' : min (min 1 wmin) (min δ1 δ2) ≤ δ1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_2 : min (min 1 wmin) (min δ1 δ2) ≤ δ2 := (min_le_right _ _).trans (min_le_right _ _)
  generalize min (min 1 wmin) (min δ1 δ2) = δ at hθ' hww hδpos hδ_1 hδ_w hδ_1' hδ_2
  have hθn : ‖θ - θ'‖ ≤ δ := by rwa [norm_sub_rev]
  have hθdist : ‖designMap u w' (θ - θ')‖ ≤ ℓ * δ :=
    (norm_designMap_le u hw' hu _).trans (mul_le_mul_of_nonneg_left hθn hℓ0)
  have hdw0 : 0 ≤ δ / wmin := by positivity
  have hrl0 : 0 ≤ (r + ℓ) / wmin := by positivity
  have hℓδ : ℓ * δ + δ / wmin * (r + ℓ) < ε / 2 := by
    have h1 : δ * (ℓ + (r + ℓ) / wmin) ≤ δ2 * (ℓ + (r + ℓ) / wmin) :=
      mul_le_mul_of_nonneg_right hδ_2 (by positivity)
    have h3 : δ / wmin * (r + ℓ) = δ * ((r + ℓ) / wmin) := by ring
    rw [h3]
    linarith
  rw [← hrdef, abs_lt]
  constructor
  · -- lower bound
    have hc0 : 0 ≤ 1 - δ / wmin := by
      rw [sub_nonneg, div_le_one hwmin]
      exact hδ_w
    have hdom : ∀ v, Real.sqrt (1 - δ / wmin) * ‖designMap u w v‖ ≤ ‖designMap u w' v‖ := by
      intro v
      have h := norm_designMap_sq_lower u hw.1 hw'.1 hwmin hmin hδpos.le
        (fun x => by have := (abs_le.mp (hww x)).1; linarith) v
      have h' := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_mul hc0, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h'
    have h1 := rootInfo_mono_design (A := designMap u w) (G := designMap u w') (θ := θ') hQ
      (Real.sqrt_nonneg _) hdom
    have h2 : 1 - δ / wmin ≤ Real.sqrt (1 - δ / wmin) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have h3 := abs_sub_le_iff.mp (rootInfo_design_lipschitz u hw hu Q θ θ')
    have hR'0 : 0 ≤ rootInfo (designMap u w) Q θ' := rootInfo_nonneg
    have hmul := mul_le_mul_of_nonneg_left hθn hℓ0
    have hR'lo : r - ℓ * δ ≤ rootInfo (designMap u w) Q θ' := by
      rw [hrdef]
      linarith [h3.1]
    have hR'hi : rootInfo (designMap u w) Q θ' ≤ r + ℓ := by
      have := mul_le_mul_of_nonneg_left hδ_1 hℓ0
      rw [hrdef]
      linarith [h3.2]
    have h4 : (1 - δ / wmin) * rootInfo (designMap u w) Q θ' ≤
        rootInfo (designMap u w') Q θ' := (mul_le_mul_of_nonneg_right h2 hR'0).trans h1
    have h5 : δ / wmin * rootInfo (designMap u w) Q θ' ≤ δ / wmin * (r + ℓ) :=
      mul_le_mul_of_nonneg_left hR'hi hdw0
    linarith
  · -- upper bound
    have h1 : rootInfo (designMap u w') Q θ' ≤ ‖designMap u w' (lam - θ')‖ := rootInfo_le hlam
    have h2 : ‖designMap u w' (lam - θ')‖ ≤
        ‖designMap u w' (lam - θ)‖ + ‖designMap u w' (θ - θ')‖ := by
      have : lam - θ' = (lam - θ) + (θ - θ') := by abel
      rw [this, map_add]
      exact norm_add_le _ _
    have h3 : ‖designMap u w' (lam - θ)‖ ≤ ‖designMap u w (lam - θ)‖ + ε / 4 := by
      have hp := norm_designMap_sq_perturb u hw.1 hw'.1 hδpos.le
        (fun x => (abs_le.mp (hww x)).2) hu (lam - θ)
      have hδb : δ * Fintype.card X * (ℓ * ‖lam - θ‖) ^ 2 ≤ (ε / 4) ^ 2 := by
        have e1 : δ * b ≤ δ1 * b := mul_le_mul_of_nonneg_right hδ_1' hb0
        have e3 : δ * Fintype.card X * (ℓ * ‖lam - θ‖) ^ 2 = δ * b := by rw [hbdef]; ring
        rw [e3]
        linarith
      have hn0 := norm_nonneg (designMap u w (lam - θ))
      have hsq : ‖designMap u w' (lam - θ)‖ ^ 2 ≤ (‖designMap u w (lam - θ)‖ + ε / 4) ^ 2 := by
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
    have hpos : 0 ≤ δ / wmin * (r + ℓ) := by positivity
    linarith

end JointContinuity

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Expected upper bound** (`thm:bay-main-optimal`, "Expected upper bound": "dividing
the expectation by `log(1/δ)` and then sending `s ↓ 0` proves the upper constant").
Suppose that for every rate slack `0 < s < I_*/2` there are a time `T_s` with finite
expectation, independent of `δ`, and `δ_s > 0` such that for all `δ < δ_s`, on every path,
`τ_δ ≤ max {T_s, ⌈log(1/δ) / (I_* - 2s)⌉}`.  Then
`limsup_{δ ↓ 0} 𝔼 τ_δ / log(1/δ) ≤ 1 / I_*`, stated as: for every `η > 0` the ratio is
eventually at most `1/I_* + η`.  The hypothesis is what the tracking, estimation and
stabilization argument supplies; it is not derived here. -/
theorem upper_half_of_pathwise (P : Measure Ω) [IsProbabilityMeasure P] {I : ℝ} (hI : 0 < I)
    (τ : ℝ → Ω → ℝ≥0∞)
    (h : ∀ s, 0 < s → 2 * s < I → ∃ (T : Ω → ℝ≥0∞) (δ0 : ℝ), 0 < δ0 ∧ ∫⁻ ω, T ω ∂P ≠ ⊤ ∧
      ∀ δ, 0 < δ → δ < δ0 → ∀ ω,
        τ δ ω ≤ max (T ω) ((⌈Real.log (1 / δ) / (I - 2 * s)⌉₊ : ℕ) : ℝ≥0∞)) :
    ∀ η > 0, ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 →
      (∫⁻ ω, τ δ ω ∂P).toReal / Real.log (1 / δ) ≤ 1 / I + η := by
  refine upper_rate_of_bounds hI (f := fun δ => (∫⁻ ω, τ δ ω ∂P).toReal) (fun s hs0 hs => ?_)
  obtain ⟨T, δ0, hδ0, hT, hb⟩ := h s hs0 hs
  have hIs : 0 < I - 2 * s := by linarith
  refine ⟨(∫⁻ ω, T ω ∂P).toReal + 1, min δ0 1, lt_min hδ0 one_pos, fun δ hδ hlt => ?_⟩
  have hδ1 : δ < 1 := hlt.trans_le (min_le_right _ _)
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hx : 0 ≤ Real.log (1 / δ) / (I - 2 * s) := by positivity
  have hle : ∫⁻ ω, τ δ ω ∂P ≤
      ∫⁻ ω, T ω ∂P + ((⌈Real.log (1 / δ) / (I - 2 * s)⌉₊ : ℕ) : ℝ≥0∞) := by
    calc ∫⁻ ω, τ δ ω ∂P
        ≤ ∫⁻ ω, (T ω + ((⌈Real.log (1 / δ) / (I - 2 * s)⌉₊ : ℕ) : ℝ≥0∞)) ∂P :=
          lintegral_mono (fun ω => (hb δ hδ (hlt.trans_le (min_le_left _ _)) ω).trans
            (max_le (le_add_of_nonneg_right bot_le) (le_add_of_nonneg_left bot_le)))
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have hfin : ∫⁻ ω, T ω ∂P + ((⌈Real.log (1 / δ) / (I - 2 * s)⌉₊ : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hT, ENNReal.natCast_ne_top _⟩
  have h1 := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add hT (ENNReal.natCast_ne_top _), ENNReal.toReal_natCast] at h1
  have h2 : (⌈Real.log (1 / δ) / (I - 2 * s)⌉₊ : ℝ) ≤ Real.log (1 / δ) / (I - 2 * s) + 1 :=
    (Nat.ceil_lt_add_one hx).le
  show (∫⁻ ω, τ δ ω ∂P).toReal ≤ _
  linarith

end Expectation

end JointRootCert
