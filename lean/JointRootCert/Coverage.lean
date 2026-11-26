/-
Statistical validity and model misspecification (Appendix C,
"Statistical Validity and Model Misspecification").

Results covered:

* the Bayesian posterior-risk guarantee `eq:bay-posterior-risk` (`posterior_risk_bound`);
* Lemma `lem:bay-cs` (Full-domain confidence sequence): `mixGap_bounds`,
  `logdet_le_of_trace_le`, `mixThreshold_le`, `mixture_exponent_identity`,
  `bay_cs_coverage`;
* Lemma `lem:nested-interval-valid` (Anytime validity and nesting of terminal boxes):
  `hoeffding_two_sided`, `hoeffding_count_failure`, `hoeffding_schedule_failure`,
  `hoeffding_box_coverage`, `eb_interval_of_lt`, `eb_coverage`, `runLo_mono`,
  `runHi_anti`, `mem_run_Icc`, `box_nested`;
* Proposition `thm:t3-misspec` (Valid misspecification-aware ellipsoid and safe
  intersection): `bias_qinv_le`, `misspec_radius`, `bias_budget_cap`,
  `misspec_regret_isGreatest`, `misspec_certificate_isGreatest`, `safe_intersection`.

Ville's maximal inequality for nonnegative supermartingales, which Mathlib does not
provide, is proved here as `ville_ineq`.

What is assumed rather than proved is stated in the doc comment of each theorem: the
supermartingale property of the Gaussian mixture likelihood ratio and of the
empirical-Bernstein test processes, and the self-normalized bound for the sub-Gaussian
innovation sum.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset MeasureTheory Matrix
open scoped ENNReal

/-! ### Ville's maximal inequality -/

section Ville

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ}

/-- **Ville's inequality.**  A nonnegative supermartingale ever reaches the level `c > 0`
with probability at most `E[f 0] / c`. -/
theorem ville_ineq [IsFiniteMeasure μ] (hf : Supermartingale f ℱ μ) (hnn : ∀ n ω, 0 ≤ f n ω)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c ≤ f n ω} ≤ ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c) := by
  -- `D k`: the level has not been reached before time `k`; `A k`: first reached at `k`
  set D : ℕ → Set Ω := fun k => {ω | ∀ j < k, f j ω < c} with hD
  set A : ℕ → Set Ω := fun k => {ω | c ≤ f k ω} ∩ D k with hA
  have hsm : ∀ j k, j ≤ k → StronglyMeasurable[ℱ k] (f j) := fun j k hjk =>
    (hf.stronglyMeasurable j).mono (ℱ.mono hjk)
  have hDm : ∀ k, MeasurableSet[ℱ k] (D k) := by
    intro k
    have : D k = ⋂ j, ⋂ (_ : j < k), {ω | f j ω < c} := by
      ext ω
      simp [hD]
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj =>
      (hsm j k hj.le).measurableSet_lt stronglyMeasurable_const
  have hAm : ∀ k, MeasurableSet[ℱ k] (A k) := fun k =>
    (stronglyMeasurable_const.measurableSet_le (hsm k k le_rfl)).inter (hDm k)
  have hDsucc : ∀ k, D (k + 1) = {ω | f k ω < c} ∩ D k := by
    intro k
    ext ω
    simp only [hD, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨h k (Nat.lt_succ_self k), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact h2 j h
      · exact h1
  have hDm' : ∀ k, MeasurableSet[ℱ k] (D (k + 1)) := fun k => by
    rw [hDsucc]
    exact ((hsm k k le_rfl).measurableSet_lt stronglyMeasurable_const).inter (hDm k)
  have hsplit : ∀ k, A k ∪ D (k + 1) = D k := by
    intro k
    rw [hDsucc]
    ext ω
    simp only [hA, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.2
    · intro h
      rcases le_or_gt c (f k ω) with h1 | h1
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
  have hdisj : ∀ k, Disjoint (A k) (D (k + 1)) := by
    intro k
    rw [hDsucc, Set.disjoint_left]
    rintro ω ⟨h1, _⟩ ⟨h2, _⟩
    have h1' : c ≤ f k ω := h1
    have h2' : f k ω < c := h2
    exact not_le.mpr h2' h1'
  have hstep : ∀ k, c * μ.real (A k) + ∫ ω in D (k + 1), f (k + 1) ω ∂μ ≤
      ∫ ω in D k, f k ω ∂μ := by
    intro k
    have h1 : c * μ.real (A k) ≤ ∫ ω in A k, f k ω ∂μ :=
      setIntegral_ge_of_const_le_real (ℱ.le k _ (hAm k)) (measure_ne_top _ _)
        (fun ω hω => hω.1) (hf.integrable k).integrableOn
    have h2 : ∫ ω in D (k + 1), f (k + 1) ω ∂μ ≤ ∫ ω in D (k + 1), f k ω ∂μ :=
      hf.setIntegral_le (Nat.le_succ k) (hDm' k)
    have h3 : ∫ ω in D k, f k ω ∂μ =
        ∫ ω in A k, f k ω ∂μ + ∫ ω in D (k + 1), f k ω ∂μ := by
      rw [← hsplit k]
      exact setIntegral_union (hdisj k) (ℱ.le k _ (hDm' k)) (hf.integrable k).integrableOn
        (hf.integrable k).integrableOn
    linarith
  have hinv : ∀ n, ∑ k ∈ range n, c * μ.real (A k) + ∫ ω in D n, f n ω ∂μ ≤
      ∫ ω, f 0 ω ∂μ := by
    intro n
    induction n with
    | zero =>
      have : D 0 = Set.univ := by
        ext ω
        simp [hD]
      simp [this]
    | succ n ih =>
      rw [sum_range_succ]
      linarith [hstep n]
  have hpart : ∀ n, ∑ k ∈ range n, μ.real (A k) ≤ (∫ ω, f 0 ω ∂μ) / c := by
    intro n
    have h0 : 0 ≤ ∫ ω in D n, f n ω ∂μ := integral_nonneg (fun ω => hnn n ω)
    have h1 := hinv n
    rw [← mul_sum] at h1
    rw [le_div_iff₀ hc]
    linarith
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    wlog h : i < j generalizing i j
    · exact (this (Ne.symm hij) (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hij))).symm
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, _⟩ ⟨_, h2⟩
    have h1' : c ≤ f i ω := h1
    have h2' : ∀ j' < j, f j' ω < c := h2
    exact not_le.mpr (h2' i h) h1'
  have hUnion : {ω | ∃ n, c ≤ f n ω} = ⋃ k, A k := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      classical
      exact ⟨Nat.find h, Nat.find_spec h, fun j hj => not_le.mp (Nat.find_min h hj)⟩
    · rintro ⟨k, hk, _⟩
      exact ⟨k, hk⟩
  rw [hUnion, measure_iUnion hAdisj (fun k => ℱ.le k _ (hAm k))]
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  have hsum : ∑ k ∈ range n, μ (A k) = ENNReal.ofReal (∑ k ∈ range n, μ.real (A k)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => measureReal_nonneg)]
    exact sum_congr rfl fun k _ => (ENNReal.ofReal_toReal (measure_ne_top μ (A k))).symm
  rw [hsum]
  exact ENNReal.ofReal_le_ofReal (hpart n)

/-- Ville's inequality at threshold `1 / δ` for a test supermartingale (`E[f 0] ≤ 1`). -/
theorem ville_test [IsFiniteMeasure μ] (hf : Supermartingale f ℱ μ) (hnn : ∀ n ω, 0 ≤ f n ω)
    (h0 : ∫ ω, f 0 ω ∂μ ≤ 1) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c ≤ f n ω} ≤ ENNReal.ofReal (1 / c) :=
  (ville_ineq hf hnn hc).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h0 hc.le))

end Ville

/-! ### Bayesian posterior-risk validity (`eq:bay-posterior-risk`) -/

section Posterior

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Bayesian posterior-risk guarantee (`eq:bay-posterior-risk`).**

`S t = {τ = t}` is the event of stopping at time `t` (measurable with respect to the
information `ℱ t`), and `Bad t = {r_θ(A_t) > ε}` is the event that the action held at time
`t` is not `ε`-optimal (an event of the joint prior-predictive space).  The exact posterior
risk is the conditional probability `q_t = μ[1_{Bad t} | ℱ t]`.  If the rule stops only
when `q_t ≤ δ`, then
`P(τ < ∞, r_θ(A_τ) > ε) ≤ δ P(τ < ∞)`. -/
theorem posterior_risk_bound [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) (S Bad : ℕ → Set Ω)
    (hS : ∀ t, MeasurableSet[ℱ t] (S t)) (hSdisj : Pairwise (Function.onFun Disjoint S))
    (hBad : ∀ t, MeasurableSet (Bad t)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrisk : ∀ t, ∀ᵐ ω ∂μ, ω ∈ S t →
      (μ[(Bad t).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω ≤ δ) :
    μ (⋃ t, S t ∩ Bad t) ≤ ENNReal.ofReal δ * μ (⋃ t, S t) := by
  have hSm : ∀ t, MeasurableSet (S t) := fun t => ℱ.le t _ (hS t)
  have hr : ∀ s : Set Ω, ENNReal.ofReal (μ.real s) = μ s := fun s =>
    ENNReal.ofReal_toReal (measure_ne_top μ s)
  have hone : ∀ t, μ.real (S t ∩ Bad t) ≤ δ * μ.real (S t) := by
    intro t
    have hint : Integrable ((Bad t).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const 1).indicator (hBad t)
    have h1 : ∫ ω in S t, (Bad t).indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real (S t ∩ Bad t) := by
      rw [integral_indicator_const _ (hBad t), smul_eq_mul, mul_one,
        measureReal_restrict_apply (hBad t), Set.inter_comm]
    have h2 := setIntegral_condExp (ℱ.le t) hint (hS t)
    have h3 : ∫ ω in S t, (μ[(Bad t).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω ∂μ ≤
        ∫ _ω in S t, δ ∂μ :=
      setIntegral_mono_on_ae integrable_condExp.integrableOn (integrable_const δ).integrableOn
        (hSm t) (hrisk t)
    rw [setIntegral_const, smul_eq_mul] at h3
    linarith [mul_comm (μ.real (S t)) δ]
  have hE : ∀ t, μ (S t ∩ Bad t) ≤ ENNReal.ofReal δ * μ (S t) := by
    intro t
    have := ENNReal.ofReal_le_ofReal (hone t)
    rwa [ENNReal.ofReal_mul hδ, hr, hr] at this
  calc μ (⋃ t, S t ∩ Bad t) ≤ ∑' t, μ (S t ∩ Bad t) := measure_iUnion_le _
    _ ≤ ∑' t, ENNReal.ofReal δ * μ (S t) := tsum_le_tsum hE
    _ = ENNReal.ofReal δ * ∑' t, μ (S t) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal δ * μ (⋃ t, S t) := by rw [measure_iUnion hSdisj hSm]

end Posterior

/-! ### Full-domain Gaussian confidence sequence (Lemma `lem:bay-cs`) -/

section GaussianCS

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `A_t = ½ bᵀ [G⁻¹ - (G + γ I)⁻¹] b` of `eq:bay-gaussian-cs`. -/
noncomputable def mixGap (γ : ℝ) (G : Matrix n n ℝ) (b : n → ℝ) : ℝ :=
  1 / 2 * (qinv G b - qinv (G + γ • (1 : Matrix n n ℝ)) b)

/-- `H_t(δ) = log (1 / δ) + ½ log det (I + G / γ) + A_t` of `eq:bay-gaussian-cs`. -/
noncomputable def mixThreshold (δ γ : ℝ) (G : Matrix n n ℝ) (b : n → ℝ) : ℝ :=
  Real.log (1 / δ) + 1 / 2 * Real.log (1 + γ⁻¹ • G).det + mixGap γ G b

/-- Core of the bounds on `A_t`: with `G x = b` and `(G + γ I) y = b`,
`0 ≤ ½ (b·x - b·y) ≤ (γ / 2) ‖x‖²`. -/
theorem mixGap_core {G : Matrix n n ℝ} (hsymm : Gᵀ = G) (hpsd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ G *ᵥ x)
    {γ : ℝ} (hγ : 0 < γ) {b x y : n → ℝ} (hx : G *ᵥ x = b)
    (hy : (G + γ • (1 : Matrix n n ℝ)) *ᵥ y = b) :
    0 ≤ 1 / 2 * (b ⬝ᵥ x - b ⬝ᵥ y) ∧ 1 / 2 * (b ⬝ᵥ x - b ⬝ᵥ y) ≤ γ / 2 * (x ⬝ᵥ x) := by
  set d := x - y with hd
  have hGd : G *ᵥ d = γ • y := by
    have h1 : G *ᵥ y + γ • y = b := by
      rw [← hy, add_mulVec, smul_mulVec, one_mulVec]
    rw [hd, mulVec_sub, hx, ← h1]
    abel
  have e1 : b ⬝ᵥ d = γ * (x ⬝ᵥ y) := by
    rw [← hx, dotProduct_comm, dotProduct_mulVec_symm hsymm x d, hGd, dotProduct_smul,
      smul_eq_mul]
  have e2 : d ⬝ᵥ G *ᵥ d = γ * (d ⬝ᵥ y) := by
    rw [hGd, dotProduct_smul, smul_eq_mul]
  have hq := hpsd d
  have hxy : x ⬝ᵥ y = y ⬝ᵥ y + d ⬝ᵥ y := by
    rw [hd, sub_dotProduct]
    ring
  have hxx : x ⬝ᵥ x = y ⬝ᵥ y + 2 * (d ⬝ᵥ y) + d ⬝ᵥ d := by
    simp only [hd, sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm y x]
    ring
  have hbd : b ⬝ᵥ x - b ⬝ᵥ y = b ⬝ᵥ d := by rw [hd, dotProduct_sub]
  have hyy := mul_nonneg hγ.le (dotProduct_self_nonneg' y)
  have hdd := mul_nonneg hγ.le (dotProduct_self_nonneg' d)
  rw [hbd, e1, hxy, hxx]
  constructor
  · nlinarith
  · nlinarith

lemma Coercive.add_smul_one {G : Matrix n n ℝ} {lam : ℝ} (hG : Coercive G lam) (γ : ℝ) :
    Coercive (G + γ • (1 : Matrix n n ℝ)) (lam + γ) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [transpose_add, hG.symm, transpose_smul, transpose_one]
  · rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have := hG.coer x
    linarith

lemma Coercive.psd {G : Matrix n n ℝ} {lam : ℝ} (hG : Coercive G lam) (hlam : 0 < lam)
    (x : n → ℝ) : 0 ≤ x ⬝ᵥ G *ᵥ x :=
  (mul_nonneg hlam.le (dotProduct_self_nonneg' x)).trans (hG.coer x)

/-- **Bounds on `A_t` (Lemma `lem:bay-cs`).**  For a symmetric positive definite `G`
(`Coercive G lam` with `lam > 0`) and `θ̂ = G⁻¹ b`,
`0 ≤ A_t ≤ (γ / 2) ‖θ̂‖₂²`. -/
theorem mixGap_bounds {G : Matrix n n ℝ} {lam γ : ℝ} (hG : Coercive G lam) (hlam : 0 < lam)
    (hγ : 0 < γ) (b : n → ℝ) :
    0 ≤ mixGap γ G b ∧ mixGap γ G b ≤ γ / 2 * ((G⁻¹ *ᵥ b) ⬝ᵥ (G⁻¹ *ᵥ b)) :=
  mixGap_core hG.symm (hG.psd hlam) hγ (hG.mul_inv_mulVec hlam b)
    ((hG.add_smul_one γ).mul_inv_mulVec (by linarith) b)

/-- **Arithmetic--geometric mean bound for determinants.**  A symmetric positive
semidefinite real matrix satisfies `det N ≤ (tr N / d)^d`. -/
theorem det_le_trace_div_pow [Nonempty n] {N : Matrix n n ℝ} (hsymm : Nᵀ = N)
    (hpsd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ N *ᵥ x) :
    N.det ≤ (N.trace / Fintype.card n) ^ Fintype.card n := by
  have hH : N.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  have hP : N.PosSemidef :=
    PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => by simpa using hpsd x)
  have hdet : N.det = ∏ i, hH.eigenvalues i := by simpa using hH.det_eq_prod_eigenvalues
  have htr : N.trace = ∑ i, hH.eigenvalues i := by simpa using hH.trace_eq_sum_eigenvalues
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hP.eigenvalues_nonneg
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : n, 1 / (Fintype.card n : ℝ) = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted univ (fun _ : n => 1 / (Fintype.card n : ℝ))
    hH.eigenvalues (fun _ _ => by positivity) hw (fun i _ => hnn i)
  calc N.det = ∏ i, (hH.eigenvalues i ^ (1 / (Fintype.card n : ℝ))) ^ Fintype.card n := by
        rw [hdet]
        refine prod_congr rfl fun i _ => ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hnn i), one_div, inv_mul_cancel₀ hd.ne',
          Real.rpow_one]
    _ = (∏ i, hH.eigenvalues i ^ (1 / (Fintype.card n : ℝ))) ^ Fintype.card n :=
        prod_pow _ _ _
    _ ≤ (∑ i, 1 / (Fintype.card n : ℝ) * hH.eigenvalues i) ^ Fintype.card n :=
        pow_le_pow_left₀ (prod_nonneg fun i _ => Real.rpow_nonneg (hnn i) _) hamgm _
    _ = (N.trace / Fintype.card n) ^ Fintype.card n := by
        rw [htr, ← mul_sum]
        congr 1
        ring

/-- **Determinant bound (Lemma `lem:bay-cs`).**  If `G` is symmetric positive semidefinite
with `tr G ≤ T`, then `log det (I + G / γ) ≤ d log (1 + T / (d γ))`. -/
theorem logdet_le_of_trace_le [Nonempty n] {G : Matrix n n ℝ} (hsymm : Gᵀ = G)
    (hpsd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ G *ᵥ x) {γ T : ℝ} (hγ : 0 < γ) (htr : G.trace ≤ T) :
    Real.log (1 + γ⁻¹ • G).det ≤
      Fintype.card n * Real.log (1 + T / (Fintype.card n * γ)) := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hT : 0 ≤ T := by
    refine le_trans ?_ htr
    have hH : G.IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
      exact hsymm
    exact (PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => by simpa using hpsd x)).trace_nonneg
  have hN : Coercive (1 + γ⁻¹ • G) 1 := by
    refine ⟨?_, fun x => ?_⟩
    · rw [transpose_add, transpose_one, transpose_smul, hsymm]
    · rw [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
        one_mul]
      have := mul_nonneg (inv_pos.mpr hγ).le (hpsd x)
      linarith
  have hpsdN := hN.psd one_pos
  have hdetpos : 0 < (1 + γ⁻¹ • G).det := by
    have h1 := (hN.isUnit_det one_pos).ne_zero
    have hH : (1 + γ⁻¹ • G).IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
      exact hN.symm
    have h2 := (PosSemidef.of_dotProduct_mulVec_nonneg hH
      (fun x => by simpa using hpsdN x)).det_nonneg
    exact lt_of_le_of_ne h2 (Ne.symm h1)
  have htrN : (1 + γ⁻¹ • G).trace / Fintype.card n ≤ 1 + T / (Fintype.card n * γ) := by
    rw [trace_add, trace_one, trace_smul, smul_eq_mul, add_div, div_self hd.ne']
    have : γ⁻¹ * G.trace / Fintype.card n ≤ T / (Fintype.card n * γ) := by
      rw [div_le_div_iff₀ hd (by positivity)]
      have h := mul_le_mul_of_nonneg_left htr hd.le
      field_simp
      nlinarith
    linarith
  have hbase : 0 ≤ (1 + γ⁻¹ • G).trace / Fintype.card n :=
    div_nonneg (by
      have hH : (1 + γ⁻¹ • G).IsHermitian := by
        rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
        exact hN.symm
      exact (PosSemidef.of_dotProduct_mulVec_nonneg hH
        (fun x => by simpa using hpsdN x)).trace_nonneg) hd.le
  calc Real.log (1 + γ⁻¹ • G).det
      ≤ Real.log ((1 + T / (Fintype.card n * γ)) ^ Fintype.card n) :=
        Real.log_le_log hdetpos
          ((det_le_trace_div_pow hN.symm hpsdN).trans (pow_le_pow_left₀ hbase htrN _))
    _ = Fintype.card n * Real.log (1 + T / (Fintype.card n * γ)) := Real.log_pow _ _

/-- The Gram matrix `G_t = ∑_{s < t} u_s u_sᵀ`. -/
noncomputable def gram (u : ℕ → n → ℝ) (t : ℕ) : Matrix n n ℝ :=
  ∑ s ∈ range t, vecMulVec (u s) (u s)

omit [Fintype n] [DecidableEq n] in
lemma gram_symm (u : ℕ → n → ℝ) (t : ℕ) : (gram u t)ᵀ = gram u t := by
  unfold gram
  rw [transpose_sum]
  refine sum_congr rfl fun s _ => ?_
  ext i j
  simp [vecMulVec_apply, mul_comm]

lemma gram_quadratic (u : ℕ → n → ℝ) (t : ℕ) (x : n → ℝ) :
    x ⬝ᵥ gram u t *ᵥ x = ∑ s ∈ range t, (u s ⬝ᵥ x) ^ 2 := by
  unfold gram
  rw [sum_mulVec, dotProduct_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [vecMulVec_self_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm x (u s)]
  ring

omit [DecidableEq n] in
lemma gram_trace_le (u : ℕ → n → ℝ) (t : ℕ) {ℓ : ℝ} (hu : ∀ s, u s ⬝ᵥ u s ≤ ℓ ^ 2) :
    (gram u t).trace ≤ t * ℓ ^ 2 := by
  unfold gram
  rw [trace_sum]
  calc ∑ s ∈ range t, (vecMulVec (u s) (u s)).trace ≤ ∑ _s ∈ range t, ℓ ^ 2 :=
        sum_le_sum fun s _ => by rw [trace_vecMulVec]; exact hu s
    _ = t * ℓ ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]

/-- **Bound on the threshold `H_t(δ)` (Lemma `lem:bay-cs`).**  For
`G_t = ∑_{s < t} u_s u_sᵀ` invertible (positive definite), `‖u_s‖₂ ≤ ℓ` and
`θ̂_t = G_t⁻¹ b_t`,
`H_t(δ) ≤ log (1 / δ) + (d / 2) log (1 + t ℓ² / (d γ)) + (γ / 2) ‖θ̂_t‖₂²`. -/
theorem mixThreshold_le [Nonempty n] (u : ℕ → n → ℝ) (t : ℕ) {ℓ lam γ δ : ℝ}
    (hu : ∀ s, u s ⬝ᵥ u s ≤ ℓ ^ 2) (hG : Coercive (gram u t) lam) (hlam : 0 < lam)
    (hγ : 0 < γ) (b : n → ℝ) :
    mixThreshold δ γ (gram u t) b ≤
      Real.log (1 / δ) +
        (Fintype.card n : ℝ) / 2 * Real.log (1 + t * ℓ ^ 2 / (Fintype.card n * γ)) +
        γ / 2 * (((gram u t)⁻¹ *ᵥ b) ⬝ᵥ ((gram u t)⁻¹ *ᵥ b)) := by
  have h1 := (mixGap_bounds hG hlam hγ b).2
  have h2 := logdet_le_of_trace_le (gram_symm u t) (hG.psd hlam) hγ (gram_trace_le u t hu)
  unfold mixThreshold
  linarith

/-- **The two forms of the mixture-martingale exponent (proof of Lemma `lem:bay-cs`).**
With `G θ̂ = b` and `(G + γ I) y = b`,
`½ bᵀ(G + γ I)⁻¹ b - θᵀ b + ½ θᵀ G θ = ½ ‖θ - θ̂‖²_G - A_t`. -/
theorem mixture_exponent_identity {G : Matrix n n ℝ} (hsymm : Gᵀ = G) {b x y θ : n → ℝ}
    (hx : G *ᵥ x = b) :
    1 / 2 * (b ⬝ᵥ y) - θ ⬝ᵥ b + 1 / 2 * (θ ⬝ᵥ G *ᵥ θ) =
      1 / 2 * ((θ - x) ⬝ᵥ G *ᵥ (θ - x)) - 1 / 2 * (b ⬝ᵥ x - b ⬝ᵥ y) := by
  have h1 : (θ - x) ⬝ᵥ G *ᵥ (θ - x) = θ ⬝ᵥ G *ᵥ θ - 2 * (θ ⬝ᵥ b) + b ⬝ᵥ x := by
    simp only [mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [dotProduct_mulVec_symm hsymm θ x, hx, dotProduct_comm x b]
    ring
  rw [h1]
  ring

end GaussianCS

section GaussianCoverage

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Full-domain confidence sequence (Lemma `lem:bay-cs`), coverage.**

`C_t(δ) = {v : ½ ‖v - θ̂_t‖²_{G_t} ≤ H_t(δ)}` with `θ̂_t = G_t⁻¹ b_t`.  The fixed parameter
`θ` leaves `C_t(δ)` at some time with invertible `G_t` with probability at most `δ`.

Proved here: Ville's inequality (`ville_ineq`), the identity between the two forms of the
mixture exponent, and the resulting inclusion of events.  Assumed (hypotheses `hM`, `h0`,
`hform`): the Gaussian mixture of adaptive likelihood ratios is a nonnegative
supermartingale `Mt` under `P_θ` with `E Mt 0 ≤ 1`, and at invertible `G_t` it has the
closed form `log Mt = -½ log det (I + G_t / γ) + ½ b_tᵀ (G_t + γ I)⁻¹ b_t - θᵀ b_t +
½ θᵀ G_t θ` given by Gaussian integration.  Invertibility of the symmetric matrix `G_t` is
expressed as `Coercive (G t ω) lam` for some `lam > 0`. -/
theorem bay_cs_coverage [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {δ γ : ℝ}
    (hδ : 0 < δ) (G : ℕ → Ω → Matrix n n ℝ) (b : ℕ → Ω → n → ℝ) (θ : n → ℝ)
    (Mt : ℕ → Ω → ℝ) (hM : Supermartingale Mt ℱ μ) (hnn : ∀ t ω, 0 ≤ Mt t ω)
    (h0 : ∫ ω, Mt 0 ω ∂μ ≤ 1)
    (hform : ∀ t ω, (∃ lam, 0 < lam ∧ Coercive (G t ω) lam) →
      Mt t ω = Real.exp (-(1 / 2) * Real.log (1 + γ⁻¹ • G t ω).det +
        1 / 2 * qinv (G t ω + γ • (1 : Matrix n n ℝ)) (b t ω) - θ ⬝ᵥ b t ω +
        1 / 2 * (θ ⬝ᵥ G t ω *ᵥ θ))) :
    μ {ω | ∃ t, (∃ lam, 0 < lam ∧ Coercive (G t ω) lam) ∧
        mixThreshold δ γ (G t ω) (b t ω) <
          1 / 2 * ((θ - (G t ω)⁻¹ *ᵥ b t ω) ⬝ᵥ G t ω *ᵥ (θ - (G t ω)⁻¹ *ᵥ b t ω))} ≤
      ENNReal.ofReal δ := by
  have hville := ville_test hM hnn h0 (c := 1 / δ) (by positivity)
  rw [one_div_one_div] at hville
  refine (measure_mono ?_).trans hville
  rintro ω ⟨t, hpd, hlt⟩
  refine ⟨t, ?_⟩
  obtain ⟨lam, hlam, hG⟩ := hpd
  have hx := hG.mul_inv_mulVec hlam (b t ω)
  have hid := mixture_exponent_identity (G := G t ω) hG.symm (θ := θ)
    (y := (G t ω + γ • (1 : Matrix n n ℝ))⁻¹ *ᵥ b t ω) hx
  have hgap : mixGap γ (G t ω) (b t ω) =
      1 / 2 * (b t ω ⬝ᵥ (G t ω)⁻¹ *ᵥ b t ω -
        b t ω ⬝ᵥ (G t ω + γ • (1 : Matrix n n ℝ))⁻¹ *ᵥ b t ω) := rfl
  have hq : qinv (G t ω + γ • (1 : Matrix n n ℝ)) (b t ω) =
      b t ω ⬝ᵥ (G t ω + γ • (1 : Matrix n n ℝ))⁻¹ *ᵥ b t ω := rfl
  rw [hform t ω ⟨lam, hlam, hG⟩]
  unfold mixThreshold at hlt
  have hexp : Real.log (1 / δ) ≤ -(1 / 2) * Real.log (1 + γ⁻¹ • G t ω).det +
        1 / 2 * qinv (G t ω + γ • (1 : Matrix n n ℝ)) (b t ω) - θ ⬝ᵥ b t ω +
        1 / 2 * (θ ⬝ᵥ G t ω *ᵥ θ) := by
    rw [hq]
    rw [hgap] at hlt
    linarith
  calc 1 / δ = Real.exp (Real.log (1 / δ)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexp

end GaussianCoverage

/-! ### Bounded observations and nested confidence boxes
(Lemma `lem:nested-interval-valid`) -/

section Nested

/-- Lower endpoint of the running intersection of the intervals `[lo k, hi k]`, `k ≤ n`. -/
noncomputable def runLo (lo : ℕ → ℝ) : ℕ → ℝ
  | 0 => lo 0
  | k + 1 => max (runLo lo k) (lo (k + 1))

/-- Upper endpoint of the running intersection of the intervals `[lo k, hi k]`, `k ≤ n`. -/
noncomputable def runHi (hi : ℕ → ℝ) : ℕ → ℝ
  | 0 => hi 0
  | k + 1 => min (runHi hi k) (hi (k + 1))

/-- Running lower endpoints are nondecreasing. -/
lemma runLo_mono (lo : ℕ → ℝ) : Monotone (runLo lo) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

/-- Running upper endpoints are nonincreasing. -/
lemma runHi_anti (hi : ℕ → ℝ) : Antitone (runHi hi) :=
  antitone_nat_of_succ_le fun _ => min_le_left _ _

/-- A point lying in every interval `[lo k, hi k]`, `k ≤ n`, lies in the running
intersection. -/
lemma mem_run_Icc {lo hi : ℕ → ℝ} {m : ℝ} {n : ℕ} (h : ∀ k ≤ n, m ∈ Set.Icc (lo k) (hi k)) :
    m ∈ Set.Icc (runLo lo n) (runHi hi n) := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    have h1 := ih fun k hk => h k (Nat.le_succ_of_le hk)
    have h2 := h (n + 1) le_rfl
    exact ⟨max_le h1.1 h2.1, le_min h1.2 h2.2⟩

/-- The running intersection is contained in each of the intervals it intersects. -/
lemma run_Icc_subset {lo hi : ℕ → ℝ} {n k : ℕ} (hk : k ≤ n) :
    Set.Icc (runLo lo n) (runHi hi n) ⊆ Set.Icc (lo k) (hi k) := by
  intro m hm
  have hlo : lo k ≤ runLo lo k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  have hhi : runHi hi k ≤ hi k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact min_le_right _ _
  exact ⟨hlo.trans ((runLo_mono lo hk).trans hm.1), (hm.2.trans (runHi_anti hi hk)).trans hhi⟩

/-- **Nesting of terminal boxes (Lemma `lem:nested-interval-valid`).**  With intrinsic
counts `N t z` that never decrease, the endpoints `l_t(z)`, `u_t(z)` of the running
intersections satisfy `l_{t+1}(z) ≥ l_t(z)` and `u_{t+1}(z) ≤ u_t(z)`.  No coverage or
non-emptiness assumption is needed. -/
theorem box_nested {Z : Type*} (lo hi : Z → ℕ → ℝ) (N : ℕ → Z → ℕ)
    (hN : ∀ t z, N t z ≤ N (t + 1) z) (t : ℕ) (z : Z) :
    runLo (lo z) (N t z) ≤ runLo (lo z) (N (t + 1) z) ∧
      runHi (hi z) (N (t + 1) z) ≤ runHi (hi z) (N t z) :=
  ⟨runLo_mono _ (hN t z), runHi_anti _ (hN t z)⟩

end Nested

section Hoeffding

open ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Two-sided Hoeffding inequality** for the mean of `n ≥ 1` independent `[0,1]`-valued
observations with common mean `m`. -/
theorem hoeffding_two_sided [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {m : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : 0 ≤ β) :
    μ.real {ω | β ≤ |(∑ i ∈ range n, X i ω) / n - m|} ≤ 2 * Real.exp (-2 * n * β ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set c : NNReal := (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 with hcdef
  have hc : (c : ℝ) = 1 / 4 := by
    simp [hcdef]
    norm_num
  have hsub : ∀ i, HasSubgaussianMGF (fun ω => X i ω - m) c μ := by
    intro i
    have := hasSubgaussianMGF_of_mem_Icc (hmeas i) (hbdd i)
    rwa [hmean i] at this
  have hsubN : ∀ i, HasSubgaussianMGF (fun ω => -(X i ω - m)) c μ := fun i => (hsub i).neg
  have hindY : iIndepFun (fun i ω => X i ω - m) μ :=
    hindep.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m)
  have hindN : iIndepFun (fun i ω => -(X i ω - m)) μ :=
    hindep.comp (fun _ x => -(x - m)) (fun _ => (measurable_id.sub_const m).neg)
  have hε : (0 : ℝ) ≤ n * β := by positivity
  have hup := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindY (n := n) (fun i _ => hsub i) hε
  have hdown := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindN (n := n) (fun i _ => hsubN i) hε
  have hexp : Real.exp (-(n * β) ^ 2 / (2 * n * c)) = Real.exp (-2 * n * β ^ 2) := by
    rw [hc]
    congr 1
    field_simp
    ring
  rw [hexp] at hup hdown
  have hsubset : {ω | β ≤ |(∑ i ∈ range n, X i ω) / n - m|} ⊆
      {ω | n * β ≤ ∑ i ∈ range n, (X i ω - m)} ∪
        {ω | n * β ≤ ∑ i ∈ range n, -(X i ω - m)} := by
    intro ω hω
    have hω' : β ≤ |(∑ i ∈ range n, X i ω) / n - m| := hω
    have hsum : ∑ i ∈ range n, (X i ω - m) = (∑ i ∈ range n, X i ω) - n * m := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    have hsum' : ∑ i ∈ range n, -(X i ω - m) = -((∑ i ∈ range n, X i ω) - n * m) := by
      rw [sum_neg_distrib, hsum]
    have hdiv : (∑ i ∈ range n, X i ω) / n - m = ((∑ i ∈ range n, X i ω) - n * m) / n := by
      field_simp
    rw [hdiv, abs_div, abs_of_pos hnpos, le_div_iff₀ hnpos] at hω'
    rcases le_abs.mp hω' with h | h
    · left
      show (n : ℝ) * β ≤ ∑ i ∈ range n, (X i ω - m)
      rw [hsum]
      linarith
    · right
      show (n : ℝ) * β ≤ ∑ i ∈ range n, -(X i ω - m)
      rw [hsum']
      linarith
  calc μ.real {ω | β ≤ |(∑ i ∈ range n, X i ω) / n - m|}
      ≤ μ.real ({ω | n * β ≤ ∑ i ∈ range n, (X i ω - m)} ∪
          {ω | n * β ≤ ∑ i ∈ range n, -(X i ω - m)}) := measureReal_mono hsubset
    _ ≤ μ.real {ω | n * β ≤ ∑ i ∈ range n, (X i ω - m)} +
          μ.real {ω | n * β ≤ ∑ i ∈ range n, -(X i ω - m)} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * n * β ^ 2) := by linarith

/-- With the radius `β(n) = √(log (4 M n² / δ) / (2 n))` (half of `hoeffdingWidth`), the
interval built from `n ≥ 1` observations misses the mean with probability at most
`δ / (2 M n²)`. -/
theorem hoeffding_count_failure [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1) {m : ℝ}
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) {M δ : ℝ} (hM : 1 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    μ.real {ω | hoeffdingWidth M δ n / 2 ≤ |(∑ i ∈ range n, X i ω) / n - m|} ≤
      δ / (2 * M * (n : ℝ) ^ 2) := by
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hMpos : 0 < M := by linarith
  set y := 4 * M * (n : ℝ) ^ 2 / δ with hy
  have hypos : 0 < y := by positivity
  have hy1 : 1 ≤ y := by
    rw [hy, one_le_div hδ0]
    nlinarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hβ : hoeffdingWidth M δ n / 2 = Real.sqrt (Real.log y / (2 * n)) := by
    unfold hoeffdingWidth
    ring
  have h := hoeffding_two_sided hindep hmeas hbdd hmean hn
    (β := hoeffdingWidth M δ n / 2) (by rw [hβ]; exact Real.sqrt_nonneg _)
  refine h.trans (le_of_eq ?_)
  rw [hβ, Real.sq_sqrt (by positivity)]
  have harg : -2 * (n : ℝ) * (Real.log y / (2 * n)) = -Real.log y := by
    field_simp
  rw [harg, Real.exp_neg, Real.exp_log hypos, hy]
  field_simp
  ring

/-- `∑_{k ≥ 0} c / (k + 1)² = c π² / 6`. -/
lemma hasSum_inv_succ_sq (c : ℝ) :
    HasSum (fun k : ℕ => c / ((k : ℝ) + 1) ^ 2) (c * (Real.pi ^ 2 / 6)) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have h0 : ∑ i ∈ range 1, (1 : ℝ) / ((i : ℕ) : ℝ) ^ 2 = 0 := by simp
  rw [h0, sub_zero] at h
  have h' := h.mul_left c
  convert h' using 1
  funext k
  push_cast
  rw [mul_one_div]

/-- `π² / 12 < 1`, so the union bound `δ π² / 12` is below `δ`. -/
lemma mul_pi_sq_div_twelve_lt {δ : ℝ} (hδ : 0 < δ) : δ * (Real.pi ^ 2 / 12) < δ := by
  have h1 := Real.pi_lt_d2
  have h2 := Real.pi_pos
  have h3 : Real.pi ^ 2 < 12 := by nlinarith
  nlinarith

/-- Lower endpoint of the Hoeffding interval `I_{z,k}` (`I_{z,0} = [0,1]`). -/
noncomputable def hoeffLo (M δ : ℝ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (∑ i ∈ range k, x i) / k - hoeffdingWidth M δ k / 2

/-- Upper endpoint of the Hoeffding interval `I_{z,k}` (`I_{z,0} = [0,1]`). -/
noncomputable def hoeffHi (M δ : ℝ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else (∑ i ∈ range k, x i) / k + hoeffdingWidth M δ k / 2

variable {Z : Type*} [Fintype Z]

/-- **Union bound over terminals and intrinsic counts (Hoeffding schedule).**
`X z i` is the `i`-th observation of terminal `z` (reward-tape model: for each terminal
the observations are independent, `[0,1]`-valued, with mean `m z`).  The probability that
some interval `I_{z,n}`, `n ≥ 1`, misses its mean is at most
`∑_z ∑_{n ≥ 1} δ / (2 M n²) ≤ δ π² / 12`. -/
theorem hoeffding_schedule_failure [IsProbabilityMeasure μ] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, iIndepFun (X z) μ) (hmeas : ∀ z i, AEMeasurable (X z i) μ)
    (hbdd : ∀ z i, ∀ᵐ ω ∂μ, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂μ = m z) {M δ : ℝ} (hM : 1 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | ∃ z, ∃ k : ℕ, hoeffdingWidth M δ ((k + 1 : ℕ) : ℝ) / 2 ≤
        |(∑ i ∈ range (k + 1), X z i ω) / ((k + 1 : ℕ) : ℝ) - m z|} ≤
      ENNReal.ofReal (δ * (Real.pi ^ 2 / 12)) := by
  have hMpos : 0 < M := by linarith
  set E : Z → ℕ → Set Ω := fun z k => {ω | hoeffdingWidth M δ ((k + 1 : ℕ) : ℝ) / 2 ≤
    |(∑ i ∈ range (k + 1), X z i ω) / ((k + 1 : ℕ) : ℝ) - m z|} with hE
  have hset : {ω | ∃ z, ∃ k : ℕ, hoeffdingWidth M δ ((k + 1 : ℕ) : ℝ) / 2 ≤
      |(∑ i ∈ range (k + 1), X z i ω) / ((k + 1 : ℕ) : ℝ) - m z|} = ⋃ z, ⋃ k, E z k := by
    ext ω
    simp only [hE, Set.mem_ofPred_eq, Set.mem_iUnion]
  have hEk : ∀ z k, μ (E z k) ≤ ENNReal.ofReal (δ / (2 * M) / ((k : ℝ) + 1) ^ 2) := by
    intro z k
    have h := hoeffding_count_failure (hindep z) (hmeas z) (hbdd z) (hmean z) hM hδ0 hδ1
      (n := k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    have h2 : μ (E z k) = ENNReal.ofReal (μ.real (E z k)) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    rw [h2]
    apply ENNReal.ofReal_le_ofReal
    refine h.trans (le_of_eq ?_)
    push_cast
    field_simp
  have hz : ∀ z, μ (⋃ k, E z k) ≤ ENNReal.ofReal (δ / (2 * M) * (Real.pi ^ 2 / 6)) := by
    intro z
    calc μ (⋃ k, E z k) ≤ ∑' k, μ (E z k) := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (δ / (2 * M) / ((k : ℝ) + 1) ^ 2) := tsum_le_tsum (hEk z)
      _ = ENNReal.ofReal (∑' k : ℕ, δ / (2 * M) / ((k : ℝ) + 1) ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (hasSum_inv_succ_sq _).summable).symm
      _ = ENNReal.ofReal (δ / (2 * M) * (Real.pi ^ 2 / 6)) := by
          rw [(hasSum_inv_succ_sq _).tsum_eq]
  rw [hset]
  calc μ (⋃ z, ⋃ k, E z k) ≤ ∑ z, μ (⋃ k, E z k) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _z : Z, ENNReal.ofReal (δ / (2 * M) * (Real.pi ^ 2 / 6)) :=
        sum_le_sum fun z _ => hz z
    _ = ENNReal.ofReal ((Fintype.card Z : ℝ) * (δ / (2 * M) * (Real.pi ^ 2 / 6))) := by
        rw [sum_const, card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (Fintype.card Z : ℝ)) (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (δ * (Real.pi ^ 2 / 12)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (Fintype.card Z : ℝ) * (δ / (2 * M)) ≤ δ / 2 := by
          rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have h2 : 0 ≤ Real.pi ^ 2 / 6 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]

/-- **Anytime validity of the Hoeffding terminal boxes (Lemma
`lem:nested-interval-valid`, Hoeffding schedule).**  `B_t = ∏_z [l_t(z), u_t(z)]` where
`[l_t(z), u_t(z)]` is the running intersection of `I_{z,0} = [0,1]` and the Hoeffding
intervals `I_{z,k}`, `1 ≤ k ≤ N_t(z)`.  For arbitrary intrinsic counts `N t ω z`
(any adaptive sampling policy), `P(∃ t, μ ∉ B_t) ≤ δ π² / 12 < δ`. -/
theorem hoeffding_box_coverage [IsProbabilityMeasure μ] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, iIndepFun (X z) μ) (hmeas : ∀ z i, AEMeasurable (X z i) μ)
    (hbdd : ∀ z i, ∀ᵐ ω ∂μ, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂μ = m z) {M δ : ℝ} (hM : 1 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ → Ω → Z → ℕ) :
    μ {ω | ∃ t z, m z ∉ Set.Icc (runLo (hoeffLo M δ (fun i => X z i ω)) (N t ω z))
        (runHi (hoeffHi M δ (fun i => X z i ω)) (N t ω z))} ≤ ENNReal.ofReal δ := by
  have hm01 : ∀ z, m z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    have hint : Integrable (X z 0) μ := Integrable.of_mem_Icc 0 1 (hmeas z 0) (hbdd z 0)
    rw [← hmean z 0]
    constructor
    · exact integral_nonneg_of_ae ((hbdd z 0).mono fun ω h => h.1)
    · have := integral_mono_ae hint (integrable_const (1 : ℝ))
        ((hbdd z 0).mono fun ω h => h.2)
      simpa using this
  refine (measure_mono ?_).trans
    ((hoeffding_schedule_failure hindep hmeas hbdd hmean hM hcard hδ0 hδ1).trans
      (ENNReal.ofReal_le_ofReal (mul_pi_sq_div_twelve_lt hδ0).le))
  rintro ω ⟨t, z, hnot⟩
  by_contra hgood
  apply hnot
  apply mem_run_Icc
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [hoeffLo, hoeffHi] using hm01 z
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hlt : |(∑ i ∈ range (j + 1), X z i ω) / ((j + 1 : ℕ) : ℝ) - m z| <
        hoeffdingWidth M δ ((j + 1 : ℕ) : ℝ) / 2 := by
      by_contra h
      exact hgood ⟨z, j, not_lt.mp h⟩
    rw [abs_lt] at hlt
    have hne : j + 1 ≠ 0 := Nat.succ_ne_zero j
    simp only [hoeffLo, hoeffHi, hne, ↓reduceIte, Set.mem_Icc]
    constructor <;> linarith [hlt.1, hlt.2]

end Hoeffding

/-! ### Predictable empirical-Bernstein confidence sequences -/

section EmpiricalBernstein

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **From the test processes to the interval `I^{EB}`.**  Write
`SX = ∑ λ_i X_i`, `Λ = ∑ λ_i`, `V = ∑ (X_i - μ̂_{i-1})² ψ_E(λ_i)`, so that
`M^± = exp (± (SX - m Λ) - V)`.  If both processes are below the threshold `c`, then `m`
lies between `(SX ∓ (log c + V)) / Λ`. -/
theorem eb_interval_of_lt {SX Lam V m c : ℝ} (hLam : 0 < Lam)
    (hp : Real.exp (SX - m * Lam - V) < c) (hm : Real.exp (-(SX - m * Lam) - V) < c) :
    (SX - (Real.log c + V)) / Lam ≤ m ∧ m ≤ (SX + (Real.log c + V)) / Lam := by
  have hc : 0 < c := lt_trans (Real.exp_pos _) hp
  have h1 := (Real.lt_log_iff_exp_lt hc).mpr hp
  have h2 := (Real.lt_log_iff_exp_lt hc).mpr hm
  constructor
  · rw [div_le_iff₀ hLam]
    linarith
  · rw [le_div_iff₀ hLam]
    linarith

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- **Anytime validity of the empirical-Bernstein terminal intervals (Lemma
`lem:nested-interval-valid`, empirical-Bernstein variant).**

For each terminal `z`, `SX z n = ∑_{i ≤ n} λ_{z,i} X_{z,i}`, `Lam z n = ∑_{i ≤ n} λ_{z,i}`
and `V z n = ∑_{i ≤ n} (X_{z,i} - μ̂_{z,i-1})² ψ_E(λ_{z,i})`, so that
`M^±_{z,n}(μ_z) = exp (± (SX - μ_z Lam) - V)` and
`W_{z,n} = log (2 M / δ) + V z n` with `M = |Z|`.

Proved here: Ville's maximal inequality at threshold `2 M / δ`, the union bound over the
`2 M` processes, and the passage from the two test processes to the clipped interval
`I^{EB}_{z,n}`.  Assumed (hypotheses `hplus`, `hminus`, `hp0`, `hm0`): `M^±_z` are
supermartingales with initial expectation at most one, which the paper takes from the
exponential inequality for bounded martingale differences. -/
theorem eb_coverage [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ)
    (ℱ : Z → Filtration ℕ m0) (SX Lam V : Z → ℕ → Ω → ℝ) (m : Z → ℝ)
    (hm01 : ∀ z, m z ∈ Set.Icc (0 : ℝ) 1) (hLam : ∀ z n ω, 1 ≤ n → 0 < Lam z n ω)
    (hplus : ∀ z, Supermartingale
      (fun n ω => Real.exp (SX z n ω - m z * Lam z n ω - V z n ω)) (ℱ z) μ)
    (hminus : ∀ z, Supermartingale
      (fun n ω => Real.exp (-(SX z n ω - m z * Lam z n ω) - V z n ω)) (ℱ z) μ)
    (hp0 : ∀ z, ∫ ω, Real.exp (SX z 0 ω - m z * Lam z 0 ω - V z 0 ω) ∂μ ≤ 1)
    (hm0 : ∀ z, ∫ ω, Real.exp (-(SX z 0 ω - m z * Lam z 0 ω) - V z 0 ω) ∂μ ≤ 1) :
    μ {ω | ∃ z, ∃ n, 1 ≤ n ∧ m z ∉ Set.Icc
        (max 0 ((SX z n ω - (Real.log (2 * Fintype.card Z / δ) + V z n ω)) / Lam z n ω))
        (min 1 ((SX z n ω + (Real.log (2 * Fintype.card Z / δ) + V z n ω)) / Lam z n ω))} ≤
      ENNReal.ofReal δ := by
  have hd : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  set c : ℝ := 2 * Fintype.card Z / δ with hc
  have hcpos : 0 < c := by positivity
  set P : Z → Set Ω := fun z =>
    {ω | ∃ n, c ≤ Real.exp (SX z n ω - m z * Lam z n ω - V z n ω)} with hP
  set Q : Z → Set Ω := fun z =>
    {ω | ∃ n, c ≤ Real.exp (-(SX z n ω - m z * Lam z n ω) - V z n ω)} with hQ
  have hPz : ∀ z, μ (P z) ≤ ENNReal.ofReal (1 / c) := fun z =>
    ville_test (hplus z) (fun _ _ => (Real.exp_pos _).le) (hp0 z) hcpos
  have hQz : ∀ z, μ (Q z) ≤ ENNReal.ofReal (1 / c) := fun z =>
    ville_test (hminus z) (fun _ _ => (Real.exp_pos _).le) (hm0 z) hcpos
  have hsub : {ω | ∃ z, ∃ n, 1 ≤ n ∧ m z ∉ Set.Icc
        (max 0 ((SX z n ω - (Real.log c + V z n ω)) / Lam z n ω))
        (min 1 ((SX z n ω + (Real.log c + V z n ω)) / Lam z n ω))} ⊆ ⋃ z, (P z ∪ Q z) := by
    rintro ω ⟨z, n, hn, hnot⟩
    rw [Set.mem_iUnion]
    refine ⟨z, ?_⟩
    by_contra hout
    apply hnot
    have h1 : Real.exp (SX z n ω - m z * Lam z n ω - V z n ω) < c := by
      by_contra h
      exact hout (Or.inl ⟨n, not_lt.mp h⟩)
    have h2 : Real.exp (-(SX z n ω - m z * Lam z n ω) - V z n ω) < c := by
      by_contra h
      exact hout (Or.inr ⟨n, not_lt.mp h⟩)
    have h := eb_interval_of_lt (hLam z n ω hn) h1 h2
    exact ⟨max_le (hm01 z).1 h.1, le_min (hm01 z).2 h.2⟩
  calc μ _ ≤ μ (⋃ z, (P z ∪ Q z)) := measure_mono hsub
    _ ≤ ∑ z, μ (P z ∪ Q z) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _z : Z, (ENNReal.ofReal (1 / c) + ENNReal.ofReal (1 / c)) :=
        sum_le_sum fun z _ => (measure_union_le _ _).trans (add_le_add (hPz z) (hQz z))
    _ = ENNReal.ofReal ((Fintype.card Z : ℝ) * (1 / c + 1 / c)) := by
        rw [sum_const, card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (Fintype.card Z : ℝ)) (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal δ := by
        congr 1
        rw [hc]
        field_simp
        ring

end EmpiricalBernstein

/-! ### Bounded-residual robustness and safe intersections
(Proposition `thm:t3-misspec`) -/

section Misspec

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]

/-- **`‖A v‖_{V⁻¹} ≤ ‖v‖₂` when `A Aᵀ ⪯ V`.**  Here `A = [φ_s]_s`, so
`A v = ∑_s v_s φ_s`, and `A Aᵀ ⪯ V` reads `∑_s (φ_s · x)² ≤ xᵀ V x`. -/
theorem bias_qinv_le {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    (φ : ι → n → ℝ) (v : ι → ℝ)
    (hdom : ∀ x : n → ℝ, ∑ s, (φ s ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ V *ᵥ x) :
    qinv V (∑ s, v s • φ s) ≤ ∑ s, v s ^ 2 := by
  set g := ∑ s, v s • φ s with hg
  set y := V⁻¹ *ᵥ g with hy
  have hq : qinv V g = ∑ s, v s * (φ s ⬝ᵥ y) := by
    have : qinv V g = g ⬝ᵥ y := rfl
    rw [this, hg, sum_dotProduct]
    refine sum_congr rfl fun s _ => ?_
    rw [smul_dotProduct, smul_eq_mul]
  have hq2 : qinv V g = y ⬝ᵥ V *ᵥ y := hV.qinv_eq hlam g
  have hcs := sum_mul_sq_le_sq_mul_sq univ v (fun s => φ s ⬝ᵥ y)
  have h0 := hV.qinv_nonneg hlam g
  have hd := hdom y
  have hS : 0 ≤ ∑ s, v s ^ 2 := sum_nonneg fun s _ => sq_nonneg _
  rw [← hq] at hcs
  have hsq : qinv V g ^ 2 ≤ (∑ s, v s ^ 2) * qinv V g := by
    refine hcs.trans (mul_le_mul_of_nonneg_left ?_ hS)
    rw [hq2]
    exact hd
  by_contra hlt
  have hlt' := not_le.mp hlt
  have hpos : 0 < qinv V g := lt_of_le_of_lt hS hlt'
  nlinarith [mul_lt_mul_of_pos_right hlt' hpos]

/-- The ridge design matrix `V = λ I + ∑_s φ_s φ_sᵀ` over the included queries. -/
noncomputable def ridgeDesign (lam : ℝ) (φ : ι → n → ℝ) : Matrix n n ℝ :=
  lam • (1 : Matrix n n ℝ) + ∑ s, vecMulVec (φ s) (φ s)

lemma ridgeDesign_mulVec (lam : ℝ) (φ : ι → n → ℝ) (x : n → ℝ) :
    ridgeDesign lam φ *ᵥ x = lam • x + ∑ s, (φ s ⬝ᵥ x) • φ s := by
  unfold ridgeDesign
  rw [add_mulVec, smul_mulVec, one_mulVec, sum_mulVec]
  congr 1
  exact sum_congr rfl fun s _ => vecMulVec_self_mulVec (φ s) x

lemma ridgeDesign_quadratic (lam : ℝ) (φ : ι → n → ℝ) (x : n → ℝ) :
    x ⬝ᵥ ridgeDesign lam φ *ᵥ x = lam * (x ⬝ᵥ x) + ∑ s, (φ s ⬝ᵥ x) ^ 2 := by
  rw [ridgeDesign_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_sum]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm x (φ s)]
  ring

lemma ridgeDesign_coercive (lam : ℝ) (φ : ι → n → ℝ) : Coercive (ridgeDesign lam φ) lam := by
  refine ⟨?_, fun x => ?_⟩
  · unfold ridgeDesign
    rw [transpose_add, transpose_smul, transpose_one, transpose_sum]
    congr 1
    refine sum_congr rfl fun s _ => ?_
    ext i j
    simp [vecMulVec_apply, mul_comm]
  · rw [ridgeDesign_quadratic]
    have : 0 ≤ ∑ s, (φ s ⬝ᵥ x) ^ 2 := sum_nonneg fun s _ => sq_nonneg _
    linarith

/-- `A Aᵀ ⪯ V_t` for the ridge design matrix. -/
lemma ridgeDesign_dom {lam : ℝ} (hlam : 0 ≤ lam) (φ : ι → n → ℝ) (x : n → ℝ) :
    ∑ s, (φ s ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ ridgeDesign lam φ *ᵥ x := by
  rw [ridgeDesign_quadratic]
  have := mul_nonneg hlam (dotProduct_self_nonneg' x)
  linarith

lemma qinv_neg (V : Matrix n n ℝ) (x : n → ℝ) : qinv V (-x) = qinv V x := by
  unfold qinv
  rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

lemma Coercive.sqrt_qinv_add_le {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam)
    (hlam : 0 < lam) (x y : n → ℝ) :
    Real.sqrt (qinv V (x + y)) ≤ Real.sqrt (qinv V x) + Real.sqrt (qinv V y) := by
  have h := hV.sqrt_qinv_sub_le hlam x (-y)
  rwa [sub_neg_eq_add, qinv_neg] at h

/-- `wᵀ V w = ‖V w‖²_{V⁻¹}`. -/
lemma Coercive.quad_eq_qinv {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    (w : n → ℝ) : w ⬝ᵥ V *ᵥ w = qinv V (V *ᵥ w) := by
  rw [hV.qinv_eq hlam, mulVec_mulVec, Matrix.nonsing_inv_mul _ (hV.isUnit_det hlam),
    one_mulVec]

/-- Ridge term: `‖λ θ‖_{V⁻¹} ≤ √λ B` when `‖θ‖ ≤ B`. -/
lemma Coercive.sqrt_qinv_smul_le {V : Matrix n n ℝ} {lam B : ℝ} (hV : Coercive V lam)
    (hlam : 0 < lam) (hB : 0 ≤ B) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) :
    Real.sqrt (qinv V (lam • θs)) ≤ Real.sqrt lam * B := by
  have hq : qinv V (lam • θs) = lam ^ 2 * qinv V θs := by
    unfold qinv
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hle : qinv V (lam • θs) ≤ lam * B ^ 2 := by
    rw [hq]
    have h := hV.qinv_le hlam θs
    have h' : lam ^ 2 * qinv V θs ≤ lam ^ 2 * (θs ⬝ᵥ θs / lam) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h'' : lam ^ 2 * (θs ⬝ᵥ θs / lam) = lam * (θs ⬝ᵥ θs) := by
      field_simp
    have h3 : lam * (θs ⬝ᵥ θs) ≤ lam * B ^ 2 := mul_le_mul_of_nonneg_left hθ hlam.le
    linarith
  calc Real.sqrt (qinv V (lam • θs)) ≤ Real.sqrt (lam * B ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt lam * B := by rw [Real.sqrt_mul hlam.le, Real.sqrt_sq hB]

/-- Bias term: `‖∑_s b_s φ_s‖_{V⁻¹} ≤ ξ √T_eff` when `|b_s| ≤ ξ`. -/
lemma sqrt_qinv_bias_le {lam ξ : ℝ} (hlam : 0 < lam) (hξ : 0 ≤ ξ) (φ : ι → n → ℝ)
    (bias : ι → ℝ) (hbias : ∀ s, |bias s| ≤ ξ) :
    Real.sqrt (qinv (ridgeDesign lam φ) (∑ s, bias s • φ s)) ≤
      ξ * Real.sqrt (Fintype.card ι) := by
  have hle : qinv (ridgeDesign lam φ) (∑ s, bias s • φ s) ≤ ξ ^ 2 * (Fintype.card ι : ℝ) := by
    refine (bias_qinv_le (ridgeDesign_coercive lam φ) hlam φ bias
      (ridgeDesign_dom hlam.le φ)).trans ?_
    calc ∑ s, bias s ^ 2 ≤ ∑ _s : ι, ξ ^ 2 :=
          sum_le_sum fun s _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hbias s) 2
      _ = ξ ^ 2 * (Fintype.card ι : ℝ) := by
          rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  calc Real.sqrt (qinv (ridgeDesign lam φ) (∑ s, bias s • φ s))
      ≤ Real.sqrt (ξ ^ 2 * (Fintype.card ι : ℝ)) := Real.sqrt_le_sqrt hle
    _ = ξ * Real.sqrt (Fintype.card ι) := by
        rw [Real.sqrt_mul (sq_nonneg ξ), Real.sqrt_sq hξ]

/-- Error decomposition of the ridge estimator:
`V (θ̂ - θ*) = ∑_s η_s φ_s + ∑_s b_s φ_s - λ θ*`. -/
lemma ridge_error_decomp {lam : ℝ} (hlam : 0 < lam) (φ : ι → n → ℝ) (bias η : ι → ℝ)
    (θs : n → ℝ) :
    ridgeDesign lam φ *ᵥ
        ((ridgeDesign lam φ)⁻¹ *ᵥ (∑ s, (φ s ⬝ᵥ θs + bias s + η s) • φ s) - θs) =
      ∑ s, η s • φ s + ∑ s, bias s • φ s - lam • θs := by
  have hsplit : ∑ s, (φ s ⬝ᵥ θs + bias s + η s) • φ s =
      ∑ s, (φ s ⬝ᵥ θs) • φ s + ∑ s, bias s • φ s + ∑ s, η s • φ s := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun s _ => by rw [add_smul, add_smul]
  rw [mulVec_sub, (ridgeDesign_coercive lam φ).mul_inv_mulVec hlam, hsplit, ridgeDesign_mulVec]
  abel

/-- **Misspecification-aware radius (Proposition `thm:t3-misspec`, deterministic part).**

`ι` indexes the included queries (`α_s = 1`), so `T_eff = |ι|` and
`V = λ I + ∑_s φ_s φ_sᵀ`.  The centred observations are
`Y_s - m₀ = φ_s · θ* + b_s + η_s` with `|b_s| ≤ ξ` and `‖θ*‖ ≤ B`, and
`θ̂ = V⁻¹ ∑_s (Y_s - m₀) φ_s` is the ridge estimator.  If the innovation sum satisfies the
self-normalized bound `‖∑_s η_s φ_s‖_{V⁻¹} ≤ β_sn`, then
`‖θ̂ - θ*‖_V ≤ √λ B + β_sn + ξ √T_eff`.

With `β_sn = σ √(2 log (1 / δ) + log (det V / λ^d))` this is the radius
`eq:t3-misspec-radius`.  The hypothesis `hsn` stands for the time-uniform self-normalized
martingale bound for conditionally `σ`-sub-Gaussian noise, which is not proved here. -/
theorem misspec_radius {lam ξ B βsn : ℝ} (hlam : 0 < lam) (hB : 0 ≤ B) (hξ : 0 ≤ ξ)
    (φ : ι → n → ℝ) (bias η : ι → ℝ) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hbias : ∀ s, |bias s| ≤ ξ)
    (hsn : Real.sqrt (qinv (ridgeDesign lam φ) (∑ s, η s • φ s)) ≤ βsn) :
    Real.sqrt
        (((ridgeDesign lam φ)⁻¹ *ᵥ (∑ s, (φ s ⬝ᵥ θs + bias s + η s) • φ s) - θs) ⬝ᵥ
          ridgeDesign lam φ *ᵥ
            ((ridgeDesign lam φ)⁻¹ *ᵥ (∑ s, (φ s ⬝ᵥ θs + bias s + η s) • φ s) - θs)) ≤
      Real.sqrt lam * B + βsn + ξ * Real.sqrt (Fintype.card ι) := by
  have hV : Coercive (ridgeDesign lam φ) lam := ridgeDesign_coercive lam φ
  rw [hV.quad_eq_qinv hlam, ridge_error_decomp hlam φ bias η θs]
  have h1 := hV.sqrt_qinv_smul_le hlam hB θs hθ
  have h2 := sqrt_qinv_bias_le hlam hξ φ bias hbias
  have h3 := hV.sqrt_qinv_sub_le hlam (∑ s, η s • φ s + ∑ s, bias s • φ s) (lam • θs)
  have h4 := hV.sqrt_qinv_add_le hlam (∑ s, η s • φ s) (∑ s, bias s • φ s)
  linarith

/-- **The budget cap bounds the bias term.**  If at most `⌈σ² / ξ²⌉` queries are included
per terminal, so `T_eff ≤ M ⌈σ² / ξ²⌉`, then `ξ √T_eff ≤ √(M (σ² + ξ²))`. -/
theorem bias_budget_cap {σ ξ : ℝ} (hξ : 0 < ξ) (T M : ℕ) (hT : T ≤ M * ⌈σ ^ 2 / ξ ^ 2⌉₊) :
    ξ * Real.sqrt T ≤ Real.sqrt (M * (σ ^ 2 + ξ ^ 2)) := by
  have hceil : (⌈σ ^ 2 / ξ ^ 2⌉₊ : ℝ) ≤ σ ^ 2 / ξ ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hT' : (T : ℝ) ≤ M * (σ ^ 2 / ξ ^ 2 + 1) := by
    have h : (T : ℝ) ≤ (M : ℝ) * (⌈σ ^ 2 / ξ ^ 2⌉₊ : ℝ) := by exact_mod_cast hT
    exact h.trans (mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg M))
  have hle : ξ ^ 2 * (T : ℝ) ≤ M * (σ ^ 2 + ξ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hT' (sq_nonneg ξ)
    have he : ξ ^ 2 * ((M : ℝ) * (σ ^ 2 / ξ ^ 2 + 1)) = M * (σ ^ 2 + ξ ^ 2) := by
      field_simp
    linarith
  calc ξ * Real.sqrt T = Real.sqrt (ξ ^ 2 * (T : ℝ)) := by
        rw [Real.sqrt_mul (sq_nonneg ξ), Real.sqrt_sq hξ.le]
    _ ≤ Real.sqrt (M * (σ ^ 2 + ξ ^ 2)) := Real.sqrt_le_sqrt hle

end Misspec

section Residual

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {S : Finset Z} {hS : S.Nonempty} {ξ : ℝ}

/-- The worst bounded residual for a support `S`: `-ξ` inside, `+ξ` outside. -/
def worstResidual (S : Finset Z) (ξ : ℝ) : Z → ℝ := fun x => if x ∈ S then -ξ else ξ

omit [Fintype Z] [Nonempty Z] in
lemma worstResidual_abs (S : Finset Z) (hξ : 0 ≤ ξ) (x : Z) : |worstResidual S ξ x| ≤ ξ := by
  unfold worstResidual
  split_ifs
  · rw [abs_neg, abs_of_nonneg hξ]
  · rw [abs_of_nonneg hξ]

/-- A residual bounded by `ξ` raises the regret certificate by at most `2 ξ`. -/
theorem misspec_regret_le (hSc : Sᶜ.Nonempty) (f b : Z → ℝ) (hb : ∀ x, |b x| ≤ ξ) :
    regret S hS (f + b) ≤ max 0 (Sᶜ.sup' hSc f - val S hS f + 2 * ξ) := by
  rw [regret_eq hSc]
  refine max_le_max le_rfl ?_
  have h1 : Sᶜ.sup' hSc (f + b) ≤ Sᶜ.sup' hSc f + ξ := by
    refine sup'_le _ _ fun z hz => ?_
    have := le_sup' f hz
    have := (abs_le.mp (hb z)).2
    simp only [Pi.add_apply]
    linarith
  have h2 : val S hS f ≤ val S hS (f + b) + ξ := by
    refine sup'_le _ _ fun y hy => ?_
    have h := le_val hS (f + b) hy
    have := (abs_le.mp (hb y)).1
    simp only [Pi.add_apply] at h
    linarith
  linarith

/-- The worst residual attains the `+2 ξ` correction. -/
theorem misspec_regret_worst (hSc : Sᶜ.Nonempty) (f : Z → ℝ) :
    regret S hS (f + worstResidual S ξ) = max 0 (Sᶜ.sup' hSc f - val S hS f + 2 * ξ) := by
  rw [regret_eq hSc]
  have h1 : Sᶜ.sup' hSc (f + worstResidual S ξ) = Sᶜ.sup' hSc f + ξ := by
    apply le_antisymm
    · refine sup'_le _ _ fun z hz => ?_
      have hw : worstResidual S ξ z = ξ := by simp [worstResidual, mem_compl.mp hz]
      have := le_sup' f hz
      rw [Pi.add_apply, hw]
      linarith
    · obtain ⟨z, hz, hzeq⟩ := exists_mem_eq_sup' hSc f
      have hw : worstResidual S ξ z = ξ := by simp [worstResidual, mem_compl.mp hz]
      have := le_sup' (f + worstResidual S ξ) hz
      rw [Pi.add_apply, hw] at this
      linarith
  have h2 : val S hS (f + worstResidual S ξ) = val S hS f - ξ := by
    unfold val
    apply le_antisymm
    · refine sup'_le _ _ fun y hy => ?_
      have hw : worstResidual S ξ y = -ξ := by simp [worstResidual, hy]
      have := le_sup' f hy
      rw [Pi.add_apply, hw]
      linarith
    · obtain ⟨y, hy, hyeq⟩ := exists_mem_eq_sup' hS f
      have hw : worstResidual S ξ y = -ξ := by simp [worstResidual, hy]
      have := le_sup' (f + worstResidual S ξ) hy
      rw [Pi.add_apply, hw] at this
      linarith
  rw [h1, h2]
  congr 1
  ring

/-- **The `+2 ξ` regret correction for one environment (Proposition `thm:t3-misspec`).**
Maximising the regret of a proper support over residuals `‖b‖_∞ ≤ ξ` adds exactly `2 ξ`
to the inside--outside contrast before the positive part. -/
theorem misspec_regret_isGreatest (hSc : Sᶜ.Nonempty) (hξ : 0 ≤ ξ) (f : Z → ℝ) :
    IsGreatest {r | ∃ b : Z → ℝ, (∀ x, |b x| ≤ ξ) ∧ r = regret S hS (f + b)}
      (max 0 (Sᶜ.sup' hSc f - val S hS f + 2 * ξ)) := by
  refine ⟨⟨worstResidual S ξ, worstResidual_abs S hξ, (misspec_regret_worst hSc f).symm⟩, ?_⟩
  rintro r ⟨b, hb, rfl⟩
  exact misspec_regret_le hSc f b hb

/-- **The corrected certificate `R^{(ξ)}(a) = [max_{z ∉ S} D(z, S) + 2 ξ]_+` of
`eq:ay-radius`.**  `C` is the plausible set of model value vectors and `D` is the largest
inside--outside contrast `f z - max_{y ∈ S} f y` over `f ∈ C` and `z ∉ S` (attained).
Then the largest regret over `f ∈ C` and residuals `‖b‖_∞ ≤ ξ` is `[D + 2 ξ]_+`. -/
theorem misspec_certificate_isGreatest (hSc : Sᶜ.Nonempty) (hξ : 0 ≤ ξ) (C : Set (Z → ℝ))
    {D : ℝ} (hD : ∀ f ∈ C, ∀ z, z ∉ S → f z - val S hS f ≤ D)
    (hatt : ∃ f ∈ C, ∃ z, z ∉ S ∧ f z - val S hS f = D) :
    IsGreatest {r | ∃ f ∈ C, ∃ b : Z → ℝ, (∀ x, |b x| ≤ ξ) ∧ r = regret S hS (f + b)}
      (max 0 (D + 2 * ξ)) := by
  constructor
  · obtain ⟨f, hf, z, hz, hzeq⟩ := hatt
    refine ⟨f, hf, worstResidual S ξ, worstResidual_abs S hξ, ?_⟩
    rw [misspec_regret_worst hSc f]
    apply le_antisymm
    · refine max_le_max le_rfl ?_
      have := le_sup' f (mem_compl.mpr hz)
      linarith
    · refine max_le_max le_rfl ?_
      have : Sᶜ.sup' hSc f ≤ D + val S hS f := by
        refine sup'_le _ _ fun w hw => ?_
        have := hD f hf w (mem_compl.mp hw)
        linarith
      linarith
  · rintro r ⟨f, hf, b, hb, rfl⟩
    refine (misspec_regret_le hSc f b hb).trans (max_le_max le_rfl ?_)
    have : Sᶜ.sup' hSc f ≤ D + val S hS f := by
      refine sup'_le _ _ fun w hw => ?_
      have := hD f hf w (mem_compl.mp hw)
      linarith
    linarith

end Residual

section SafeIntersection

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Safe intersection (Proposition `thm:t3-misspec`).**  If the model-based plausible
set `C₁` and a separately valid confidence set `C₂` each fail to cover the truth at some
time with probability at most `δ / 2`, their intersection fails with probability at most
`δ`. -/
theorem safe_intersection {Θ : Type*} (P : Measure Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (C₁ C₂ : ℕ → Ω → Set Θ) (θ : Θ)
    (h₁ : P {ω | ∃ t, θ ∉ C₁ t ω} ≤ ENNReal.ofReal (δ / 2))
    (h₂ : P {ω | ∃ t, θ ∉ C₂ t ω} ≤ ENNReal.ofReal (δ / 2)) :
    P {ω | ∃ t, θ ∉ C₁ t ω ∩ C₂ t ω} ≤ ENNReal.ofReal δ := by
  have hsub : {ω | ∃ t, θ ∉ C₁ t ω ∩ C₂ t ω} ⊆
      {ω | ∃ t, θ ∉ C₁ t ω} ∪ {ω | ∃ t, θ ∉ C₂ t ω} := by
    rintro ω ⟨t, ht⟩
    by_cases h : θ ∈ C₁ t ω
    · exact Or.inr ⟨t, fun h2 => ht ⟨h, h2⟩⟩
    · exact Or.inl ⟨t, h⟩
  calc P {ω | ∃ t, θ ∉ C₁ t ω ∩ C₂ t ω}
      ≤ P ({ω | ∃ t, θ ∉ C₁ t ω} ∪ {ω | ∃ t, θ ∉ C₂ t ω}) := measure_mono hsub
    _ ≤ P {ω | ∃ t, θ ∉ C₁ t ω} + P {ω | ∃ t, θ ∉ C₂ t ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add h₁ h₂
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end SafeIntersection

end JointRootCert
