/-
Finite-sample cost of safeguarded CD-Joint (Theorem `thm:t4-finite-sample`, Section 2.3
and Appendix B.1).

Unit-noise, fixed-feature model.  Queries `x ∈ X` have features `φ x` and costs `cost x`;
the design matrix is `V_0 = λ I`, `V_{t+1} = V_t + φ_{x_{t+1}} φ_{x_{t+1}}ᵀ`.  Indexing: at
step `t` the procedure holds `V_t`, forms the contrast `g t`, and queries `x t`.

The argument has three parts, all proved here.

* `cd_width`: at an uncertified step the safeguarded contrast is still uncertain,
  `‖g_t‖²_{V_t⁻¹} > ε² / (4 β_t²)` (`eq:cd-width-lemma`).
* `cd_step`: maximising the normalised covariance score with a contrast that is a
  combination of dictionary features with `ℓ¹` weight at most `2` forces
  `‖φ‖²/(1+‖φ‖²) ≥ cost · ‖g‖² / (4 c_max (1 + L²/λ))` in the `V⁻¹` geometry.
* `cd_joint_cost`: summing the resulting increments of `log det V_t` gives
  `∑ cost ≤ 16 c_max (1 + L²/λ) β² / ε² · log (det V_τ / λ^d)`.
-/
import JointRootCert.Potential

namespace JointRootCert

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X]

/-- The acquisition score of `eq:safeguard`:
`(gᵀ V⁻¹ φ_x)² / (c_x (1 + ‖φ_x‖²_{V⁻¹}))`. -/
noncomputable def cdScore (V : Matrix n n ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (g : n → ℝ)
    (x : X) : ℝ :=
  (g ⬝ᵥ V⁻¹ *ᵥ φ x) ^ 2 / (cost x * (1 + qinv V (φ x)))

/-- Cancelling the contrast width from the score comparison. -/
lemma real_step {Q P c C K : ℝ} (hQ : 0 ≤ Q) (hP : 0 ≤ P) (hc : 0 < c) (hC : 0 < C)
    (hK : 0 < K) (h : Q ^ 2 / (4 * C * K) ≤ Q * P / (c * (1 + P))) :
    c * Q / (4 * C * K) ≤ P / (1 + P) := by
  have h1P : 0 < 1 + P := by linarith
  have hD : 0 < 4 * C * K := by positivity
  have hcP : 0 < c * (1 + P) := mul_pos hc h1P
  rcases hQ.eq_or_lt with rfl | hQpos
  · rw [mul_zero, zero_div]
    exact div_nonneg hP h1P.le
  · rw [div_le_div_iff₀ hD hcP] at h
    rw [div_le_div_iff₀ hD h1P]
    have h2 : Q * (c * Q * (1 + P)) ≤ Q * (P * (4 * C * K)) := by nlinarith
    exact le_of_mul_le_mul_left h2 hQpos

/-- **One step of the potential argument.**  If the contrast is a combination of
dictionary features with `ℓ¹` weight at most `2` and the query maximises the score, the
normalised predictive variance of the query is at least a fixed multiple of
`cost · ‖g‖²_{V⁻¹}`. -/
theorem cd_step {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq)
    (g : n → ℝ) (a : X → ℝ) (hg : g = ∑ x, a x • φ x) (ha : ∑ x, |a x| ≤ 2)
    (xs : X) (hsel : ∀ y, cdScore V φ cost g y ≤ cdScore V φ cost g xs) :
    cost xs * qinv V g / (4 * cmax * (1 + Lsq / lam)) ≤
      qinv V (φ xs) / (1 + qinv V (φ xs)) := by
  have hQ : 0 ≤ qinv V g := hV.qinv_nonneg hlam g
  have hP : 0 ≤ qinv V (φ xs) := hV.qinv_nonneg hlam _
  have hcmax : 0 < cmax := (hcost xs).1.trans_le (hcost xs).2
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ xs)).trans (hφ xs)
  have hK : 0 < 1 + Lsq / lam := by positivity
  -- the contrast width is a weighted sum of covariances with dictionary features
  have hWg : V⁻¹ *ᵥ g = ∑ x, a x • (V⁻¹ *ᵥ φ x) := by
    conv_lhs => rw [hg]
    rw [mulVec_sum]
    exact sum_congr rfl (fun x _ => mulVec_smul _ _ _)
  have hQsum : qinv V g = ∑ x, a x * (g ⬝ᵥ V⁻¹ *ᵥ φ x) := by
    unfold qinv
    rw [hWg, dotProduct_sum]
    exact sum_congr rfl (fun x _ => by rw [dotProduct_smul, smul_eq_mul])
  -- some dictionary feature has covariance at least half the width
  have hne : (univ : Finset X).Nonempty := ⟨xs, mem_univ _⟩
  obtain ⟨xt, -, hxt⟩ := exists_mem_eq_sup' hne (fun x => |g ⬝ᵥ V⁻¹ *ᵥ φ x|)
  have hmax : ∀ x, |g ⬝ᵥ V⁻¹ *ᵥ φ x| ≤ |g ⬝ᵥ V⁻¹ *ᵥ φ xt| := fun x =>
    hxt ▸ le_sup' (fun x => |g ⬝ᵥ V⁻¹ *ᵥ φ x|) (mem_univ x)
  have hQle : qinv V g ≤ 2 * |g ⬝ᵥ V⁻¹ *ᵥ φ xt| := by
    rw [hQsum]
    calc ∑ x, a x * (g ⬝ᵥ V⁻¹ *ᵥ φ x)
        ≤ ∑ x, |a x| * |g ⬝ᵥ V⁻¹ *ᵥ φ xt| := sum_le_sum (fun x _ => by
          calc a x * (g ⬝ᵥ V⁻¹ *ᵥ φ x) ≤ |a x * (g ⬝ᵥ V⁻¹ *ᵥ φ x)| := le_abs_self _
            _ = |a x| * |g ⬝ᵥ V⁻¹ *ᵥ φ x| := abs_mul _ _
            _ ≤ |a x| * |g ⬝ᵥ V⁻¹ *ᵥ φ xt| :=
                mul_le_mul_of_nonneg_left (hmax x) (abs_nonneg _))
      _ = (∑ x, |a x|) * |g ⬝ᵥ V⁻¹ *ᵥ φ xt| := by rw [sum_mul]
      _ ≤ 2 * |g ⬝ᵥ V⁻¹ *ᵥ φ xt| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hB : qinv V g ^ 2 ≤ 4 * (g ⬝ᵥ V⁻¹ *ᵥ φ xt) ^ 2 := by
    have := pow_le_pow_left₀ hQ hQle 2
    rw [mul_pow, sq_abs] at this
    linarith
  -- its score is large, hence so is the score of the selected query
  have hPt : 0 ≤ qinv V (φ xt) := hV.qinv_nonneg hlam _
  have hden : cost xt * (1 + qinv V (φ xt)) ≤ cmax * (1 + Lsq / lam) := by
    have h1 : qinv V (φ xt) ≤ Lsq / lam :=
      (hV.qinv_le hlam _).trans (div_le_div_of_nonneg_right (hφ xt) hlam.le)
    exact mul_le_mul (hcost xt).2 (by linarith) (by linarith) hcmax.le
  have hdenpos : 0 < cost xt * (1 + qinv V (φ xt)) := mul_pos (hcost xt).1 (by linarith)
  have hlow : qinv V g ^ 2 / (4 * cmax * (1 + Lsq / lam)) ≤ cdScore V φ cost g xt := by
    unfold cdScore
    rw [div_le_div_iff₀ (by positivity) hdenpos]
    calc qinv V g ^ 2 * (cost xt * (1 + qinv V (φ xt)))
        ≤ qinv V g ^ 2 * (cmax * (1 + Lsq / lam)) :=
          mul_le_mul_of_nonneg_left hden (sq_nonneg _)
      _ ≤ (4 * (g ⬝ᵥ V⁻¹ *ᵥ φ xt) ^ 2) * (cmax * (1 + Lsq / lam)) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
      _ = (g ⬝ᵥ V⁻¹ *ᵥ φ xt) ^ 2 * (4 * cmax * (1 + Lsq / lam)) := by ring
  have hup : cdScore V φ cost g xs ≤
      qinv V g * qinv V (φ xs) / (cost xs * (1 + qinv V (φ xs))) := by
    unfold cdScore
    exact div_le_div_of_nonneg_right (hV.cauchy_schwarz_inv hlam g (φ xs))
      (mul_pos (hcost xs).1 (by linarith)).le
  exact real_step hQ hP (hcost xs).1 hcmax hK ((hlow.trans (hsel xt)).trans hup)

/-- The design matrices `V_0 = λ I`, `V_{t+1} = V_t + φ_{x_t} φ_{x_t}ᵀ`. -/
noncomputable def design (lam : ℝ) (φ : X → n → ℝ) (x : ℕ → X) : ℕ → Matrix n n ℝ
  | 0 => lam • 1
  | t + 1 => design lam φ x t + vecMulVec (φ (x t)) (φ (x t))

lemma design_coercive (lam : ℝ) (φ : X → n → ℝ) (x : ℕ → X) :
    ∀ t, Coercive (design lam φ x t) lam
  | 0 => coercive_smul_one
  | t + 1 => (design_coercive lam φ x t).rank_one _

lemma design_det_succ {lam : ℝ} (hlam : 0 < lam) (φ : X → n → ℝ) (x : ℕ → X) (t : ℕ) :
    (design lam φ x (t + 1)).det =
      (design lam φ x t).det * (1 + qinv (design lam φ x t) (φ (x t))) :=
  (design_coercive lam φ x t).det_rank_one hlam _

lemma design_det_zero (lam : ℝ) (φ : X → n → ℝ) (x : ℕ → X) :
    (design lam φ x 0).det = lam ^ Fintype.card n := by
  simp [design]

lemma design_det_pos {lam : ℝ} (hlam : 0 < lam) (φ : X → n → ℝ) (x : ℕ → X) :
    ∀ t, 0 < (design lam φ x t).det
  | 0 => by rw [design_det_zero]; positivity
  | t + 1 => by
    rw [design_det_succ hlam]
    exact mul_pos (design_det_pos hlam φ x t)
      (by linarith [(design_coercive lam φ x t).qinv_nonneg hlam (φ (x t))])

/-- **Finite-sample cost of safeguarded CD-Joint (Theorem `thm:t4-finite-sample`).**

Over `τ` uncertified steps, suppose that at each step `t < τ`

* the radius satisfies `0 < β t ≤ B` (for a nondecreasing radius take `B = β (τ - 1)`),
* the safeguarded contrast is still uncertain, `ε² / (4 β_t²) ≤ ‖g_t‖²_{V_t⁻¹}`
  (supplied by `cd_width`),
* the contrast is a combination of dictionary features with `ℓ¹` weight at most `2`
  (supplied by `contrast_l1`), and
* the query `x t` maximises the score of `eq:safeguard`.

Then the cumulative query cost is at most
`16 c_max (1 + L²/λ) B² / ε² · log (det V_τ / λ^d)` (`eq:t4-bound`). -/
theorem cd_joint_cost {lam : ℝ} (hlam : 0 < lam) (φ : X → n → ℝ) (cost : X → ℝ)
    {cmax Lsq ε B : ℝ} (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hcmax : 0 < cmax)
    (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hLsq : 0 ≤ Lsq) (hε : 0 < ε) (hB : 0 < B)
    (τ : ℕ) (x : ℕ → X) (g : ℕ → n → ℝ) (β : ℕ → ℝ)
    (hβ : ∀ t < τ, 0 < β t ∧ β t ≤ B)
    (hwidth : ∀ t < τ, ε ^ 2 / (4 * β t ^ 2) ≤ qinv (design lam φ x t) (g t))
    (hdict : ∀ t < τ, ∃ a : X → ℝ, g t = ∑ y, a y • φ y ∧ ∑ y, |a y| ≤ 2)
    (hsel : ∀ t < τ, ∀ y, cdScore (design lam φ x t) φ cost (g t) y ≤
      cdScore (design lam φ x t) φ cost (g t) (x t)) :
    ∑ t ∈ range τ, cost (x t) ≤
      16 * cmax * (1 + Lsq / lam) * B ^ 2 / ε ^ 2 *
        Real.log ((design lam φ x τ).det / lam ^ Fintype.card n) := by
  have hK : 0 < 1 + Lsq / lam := by positivity
  set κ := ε ^ 2 / (16 * cmax * (1 + Lsq / lam) * B ^ 2) with hκ
  have hκpos : 0 < κ := by positivity
  -- each uncertified step raises the log-determinant by at least `cost · κ`
  have hstep : ∀ t ∈ range τ, cost (x t) * κ ≤
      Real.log (design lam φ x (t + 1)).det - Real.log (design lam φ x t).det := by
    intro t ht
    have ht' : t < τ := mem_range.mp ht
    obtain ⟨a, hga, ha⟩ := hdict t ht'
    have hVt := design_coercive lam φ x t
    have hP : 0 ≤ qinv (design lam φ x t) (φ (x t)) := hVt.qinv_nonneg hlam _
    have h1 := cd_step hVt hlam φ cost hcost hφ (g t) a hga ha (x t) (hsel t ht')
    have h2 : qinv (design lam φ x t) (φ (x t)) / (1 + qinv (design lam φ x t) (φ (x t))) ≤
        Real.log (1 + qinv (design lam φ x t) (φ (x t))) := by
      have h := Real.one_sub_inv_le_log_of_pos
        (show 0 < 1 + qinv (design lam φ x t) (φ (x t)) by linarith)
      have he : qinv (design lam φ x t) (φ (x t)) / (1 + qinv (design lam φ x t) (φ (x t))) =
          1 - (1 + qinv (design lam φ x t) (φ (x t)))⁻¹ := by
        field_simp
        ring
      rw [he]
      exact h
    have h3 : Real.log (design lam φ x (t + 1)).det - Real.log (design lam φ x t).det =
        Real.log (1 + qinv (design lam φ x t) (φ (x t))) := by
      rw [design_det_succ hlam, Real.log_mul (design_det_pos hlam φ x t).ne' (by linarith)]
      ring
    have hβt := hβ t ht'
    have h4 : κ ≤ qinv (design lam φ x t) (g t) / (4 * cmax * (1 + Lsq / lam)) := by
      have h5 : ε ^ 2 / (4 * B ^ 2) ≤ ε ^ 2 / (4 * β t ^ 2) := by
        have hb : β t ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hβt.1.le hβt.2 2
        have hbpos : 0 < 4 * β t ^ 2 := by have := hβt.1; positivity
        exact div_le_div_of_nonneg_left (by positivity) hbpos (by linarith)
      have h6 : κ = ε ^ 2 / (4 * B ^ 2) / (4 * cmax * (1 + Lsq / lam)) := by
        rw [hκ, div_div]
        congr 1
        ring
      rw [h6]
      exact div_le_div_of_nonneg_right (h5.trans (hwidth t ht')) (by positivity)
    have h7 : cost (x t) * κ ≤
        cost (x t) * qinv (design lam φ x t) (g t) / (4 * cmax * (1 + Lsq / lam)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h4 (hcost (x t)).1.le
    rw [h3]
    exact (h7.trans h1).trans h2
  -- telescoping
  have hsum : (∑ t ∈ range τ, cost (x t)) * κ ≤
      Real.log (design lam φ x τ).det - Real.log (design lam φ x 0).det := by
    rw [sum_mul, ← sum_range_sub (fun t => Real.log (design lam φ x t).det) τ]
    exact sum_le_sum hstep
  have hlog : Real.log (design lam φ x τ).det - Real.log (design lam φ x 0).det =
      Real.log ((design lam φ x τ).det / lam ^ Fintype.card n) := by
    rw [design_det_zero, Real.log_div (design_det_pos hlam φ x τ).ne' (by positivity)]
  rw [hlog] at hsum
  have hfin : ∑ t ∈ range τ, cost (x t) ≤
      Real.log ((design lam φ x τ).det / lam ^ Fintype.card n) / κ :=
    (le_div_iff₀ hκpos).mpr hsum
  refine hfin.trans (le_of_eq ?_)
  rw [hκ]
  field_simp

/-- **Width of the safeguarded contrast (`eq:cd-width-lemma`).**

`hD` says the contrast objective at the mixture in use exceeds `ε`: for the dual contrast
it is the optimal value `D_t(z_t, S(b_t))`, for the direct contrast the one-vertex
mixture is feasible, and `D_t > ε` because no action is certified.  `hcase` is the
safeguard: either the estimated advantage is at most `ε / 2` (dual contrast kept), or the
contrast is `φ_z - φ_y` for a globally optimistic terminal `y`.  In both cases
`‖g‖²_{V⁻¹} > ε² / (4 β²)`. -/
theorem cd_width {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    {ε β : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (θ g : n → ℝ)
    (hD : ε < g ⬝ᵥ θ + β * Real.sqrt (qinv V g))
    (hcase : g ⬝ᵥ θ ≤ ε / 2 ∨ ∃ fz fy : n → ℝ, g = fz - fy ∧
      fz ⬝ᵥ θ + β * Real.sqrt (qinv V fz) ≤ fy ⬝ᵥ θ + β * Real.sqrt (qinv V fy)) :
    ε ^ 2 / (4 * β ^ 2) < qinv V g := by
  have hq : 0 ≤ qinv V g := hV.qinv_nonneg hlam g
  have hN : 0 ≤ Real.sqrt (qinv V g) := Real.sqrt_nonneg _
  have hkey : ε < 2 * (β * Real.sqrt (qinv V g)) := by
    rcases hcase with h | ⟨fz, fy, rfl, hopt⟩
    · linarith
    · have htri : Real.sqrt (qinv V fy) ≤
          Real.sqrt (qinv V fz) + Real.sqrt (qinv V (fz - fy)) := by
        have := hV.sqrt_qinv_sub_le hlam fz (fz - fy)
        rwa [sub_sub_cancel] at this
      have h1 : (fz - fy) ⬝ᵥ θ = fz ⬝ᵥ θ - fy ⬝ᵥ θ := sub_dotProduct _ _ _
      have h2 : β * Real.sqrt (qinv V fy) ≤
          β * (Real.sqrt (qinv V fz) + Real.sqrt (qinv V (fz - fy))) :=
        mul_le_mul_of_nonneg_left htri hβ.le
      rw [h1] at hD
      linarith
  rw [div_lt_iff₀ (by positivity)]
  have hsq : Real.sqrt (qinv V g) ^ 2 = qinv V g := Real.sq_sqrt hq
  have hpos : 0 ≤ β * Real.sqrt (qinv V g) := mul_nonneg hβ.le hN
  have : ε ^ 2 < (2 * (β * Real.sqrt (qinv V g))) ^ 2 := pow_lt_pow_left₀ hkey hε (by norm_num)
  calc ε ^ 2 < (2 * (β * Real.sqrt (qinv V g))) ^ 2 := this
    _ = Real.sqrt (qinv V g) ^ 2 * (4 * β ^ 2) := by ring
    _ = qinv V g * (4 * β ^ 2) := by rw [hsq]

/-- **Dictionary representation of a contrast.**  With all terminal features in the query
dictionary, the contrast of a challenger against any inside mixture is a combination of
dictionary features with `ℓ¹` weight at most `2`.  A one-vertex mixture gives the direct
contrast `φ_z - φ_y`. -/
lemma contrast_l1 [DecidableEq X] (φ : X → n → ℝ) (z : X) (p : X → ℝ)
    (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) :
    ∃ a : X → ℝ, φ z - ∑ y, p y • φ y = ∑ y, a y • φ y ∧ ∑ y, |a y| ≤ 2 := by
  refine ⟨fun y => (if y = z then 1 else 0) - p y, ?_, ?_⟩
  · simp [sub_smul, sum_sub_distrib]
  · calc ∑ y, |(if y = z then (1 : ℝ) else 0) - p y|
        ≤ ∑ y, ((if y = z then (1 : ℝ) else 0) + p y) := sum_le_sum (fun y _ => by
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg (hp0 y)]
          split_ifs <;> simp)
      _ = 2 := by
          rw [sum_add_distrib, hp1]
          simp
          norm_num

end JointRootCert
