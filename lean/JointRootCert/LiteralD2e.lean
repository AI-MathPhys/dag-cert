/-
Proposition `prop:v34-work` (Global solver-call reduction under sparse refreshes and
action-local evidence), with an instance constant.

`LiteralD2b.v34_work` proves the three expectation bounds with a constant `c` that is chosen
after the tracker and the probability space (it is built from the existential onset and tail of
`tracker_tail`).  Here the constant is a named function of the instance only:
`cStop I` and `cWork I`, for `I = T.inst μ v` (the root-action data `J, H, pred` and the true
means and variances; see `LiteralD2c.Instance`).  They are built from the instance onset
`I.j1 (C_*/4)` and the instance tail sum `I.tailSum (C_*/4)` of `LiteralD2c`, through
`LiteralD2c.tail_stop` at `η = C_*/4`, `lintegral_stopping_le` and `clock_inversion`.

* `expected_stopIdx_le_inst`: `E T_δ ≤ cStop I · (1 + L_δ²)` for all `δ ∈ (0, 1)`.
* `v34_work_inst`: the proposition, with `c = cWork I`.
* `v34_work_uniform`: the same in the form `∃ c, ∀ T, ∀ probability spaces, ∀ δ, …`, for a
  fixed instance `I`.

Model (as in `LiteralD2c.v34_finite_confidence`): the tracker meets the oracle contracts
(`Tracker.Contract`) with Borel allocation oracles (`Tracker.Meas`); the tapes `Y x n` are
measurable, jointly independent, `Y x n ~ N(μₓ, vₓ)` with `vₓ > 0`; and `C_* > 0`.
Expectations are lower Lebesgue integrals of `[0, ∞]`-valued functions.
-/
import JointRootCert.LiteralD2b
import JointRootCert.LiteralD2c

namespace JointRootCert

namespace LiteralD2e

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ### The instance constants -/

section Constants

variable {X A Z U : Type*} [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]

/-- `κ = C_* - 2 η` at `η = C_* / 4`. -/
def kappa (I : LiteralD2c.Instance X A Z U) : ℝ := I.Cstar - 2 * (I.Cstar / 4)

/-- `A_c = 1 + (1 + log K) / κ`. -/
def logFactor (I : LiteralD2c.Instance X A Z U) : ℝ :=
  1 + (1 + Real.log (Fintype.card A : ℝ)) / kappa I

/-- The constant of `E T_δ ≤ c (1 + L_δ²)`:
`1 + j₁(C_*/4) + ∑_{j ≥ j₁} R_{j+1} min {1, p_j} + 4 (1 + log A_c)²`. -/
def cStop (I : LiteralD2c.Instance X A Z U) : ℝ :=
  1 + (I.j1 (I.Cstar / 4) : ℝ) + (I.tailSum (I.Cstar / 4)).toReal +
    4 * (1 + Real.log (logFactor I)) ^ 2

/-- The constant of `prop:v34-work`: `max {cStop, 1 + (3 + log cStop) / log 4}`. -/
def cWork (I : LiteralD2c.Instance X A Z U) : ℝ :=
  max (cStop I) (1 + (3 + Real.log (cStop I)) / Real.log 4)

omit [Nonempty X] in
lemma kappa_pos (I : LiteralD2c.Instance X A Z U) (hC : 0 < I.Cstar) : 0 < kappa I := by
  unfold kappa; linarith

omit [Nonempty X] in
lemma one_le_logFactor (I : LiteralD2c.Instance X A Z U) (hC : 0 < I.Cstar) :
    1 ≤ logFactor I := by
  have hK : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have := Real.log_nonneg hK
  have := kappa_pos I hC
  have : 0 ≤ (1 + Real.log (Fintype.card A : ℝ)) / kappa I := by positivity
  unfold logFactor; linarith

lemma one_le_cStop (I : LiteralD2c.Instance X A Z U) (hC : 0 < I.Cstar) : 1 ≤ cStop I := by
  have := Real.log_nonneg (one_le_logFactor I hC)
  have : (0 : ℝ) ≤ I.j1 (I.Cstar / 4) := Nat.cast_nonneg _
  have : 0 ≤ (I.tailSum (I.Cstar / 4)).toReal := ENNReal.toReal_nonneg
  have : 0 ≤ 4 * (1 + Real.log (logFactor I)) ^ 2 := by positivity
  unfold cStop; linarith

lemma cStop_le_cWork (I : LiteralD2c.Instance X A Z U) : cStop I ≤ cWork I := le_max_left _ _

lemma one_le_cWork (I : LiteralD2c.Instance X A Z U) (hC : 0 < I.Cstar) : 1 ≤ cWork I :=
  (one_le_cStop I hC).trans (cStop_le_cWork I)

end Constants

/-! ### The expectation bounds -/

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Nonempty X]
  [DecidableEq X] [Fintype A] [Nonempty A] [DecidableEq A]

/-- **`E T_δ ≤ c (1 + L_δ²)` with the instance constant `c = cStop (T.inst μ v)`.**  For a
tracker meeting the oracle contracts with Borel allocation oracles, on measurable, jointly
independent tapes `Y x n ~ N(μₓ, vₓ)`, `vₓ > 0`, with `C_* > 0`, and every `δ ∈ (0, 1)`.
`T_δ = LiteralD2b.stopIdx` is the batch index at stopping, `L_δ = 1 + log (1 + log (1 / δ))`. -/
theorem expected_stopIdx_le_inst (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas)
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {μ v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (μ x) (v x).toNNReal) P)
    (hC : 0 < (T.inst μ v).Cstar) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∫⁻ ω, LiteralD2b.stopIdx T (tapeOf Y ω) δ ∂P ≤
      ENNReal.ofReal (cStop (T.inst μ v) * (1 + LiteralD2b.Ldelta δ ^ 2)) := by
  classical
  set I := T.inst μ v with hI
  set m := Fintype.card X with hm'
  set η : ℝ := I.Cstar / 4 with hη
  have hη0 : 0 < η := by positivity
  have hηC : η ≤ 8 * I.Cstar := by rw [hη]; linarith
  have hK : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hfin := I.tail_summability_instance hv0 hη0
  set κ : ℝ := kappa I with hκ
  have hκpos : 0 < κ := kappa_pos I hC
  set j1 := I.j1 η with hj1def
  set Sig : ℝ := (I.tailSum η).toReal with hSig
  have hSig0 : 0 ≤ Sig := ENNReal.toReal_nonneg
  set Ac : ℝ := logFactor I with hAc
  have hAc1 : 1 ≤ Ac := one_le_logFactor I hC
  have hlogAc : 0 ≤ Real.log Ac := Real.log_nonneg hAc1
  have hcdef : cStop I = 1 + j1 + Sig + 4 * (1 + Real.log Ac) ^ 2 := rfl
  set x := Real.log (1 / δ) with hx
  have hx0 : 0 < x := LiteralD2b.log_inv_pos hδ0 hδ1
  set B := Real.log ((Fintype.card A : ℝ) / δ) with hB
  have hBeq : B = Real.log (Fintype.card A : ℝ) + x := by
    rw [hB, hx, Real.log_div (by linarith) hδ0.ne', one_div, Real.log_inv]
    ring
  have hB0 : 0 ≤ B := by
    have := Real.log_nonneg hK
    rw [hBeq]; linarith
  obtain ⟨j', -, hj'N, hj'le⟩ := LiteralD2b.clock_inversion m (t := B / κ) (by positivity)
  set jstar := max j1 j' with hjstar
  set S : ℕ → Set Ω := fun j => toMeasurable P {ω | T.running (tapeOf Y ω) δ j} with hS
  have hp : ∀ j, jstar ≤ j → P (S j) ≤ I.pTail η j := by
    intro j hj
    rw [hS]
    simp only
    rw [measure_toMeasurable]
    refine (LiteralD2c.tail_stop T hc hm P hYm hind hv0 hlaw hC hη0 hηC hδ0
      ((le_max_left _ _).trans hj) ?_).trans (min_le_right _ _)
    have h1 : (cumN m j' : ℝ) ≤ cumN m j := by
      exact_mod_cast cumN_mono m ((le_max_right _ _).trans hj)
    have h2 : B ≤ κ * cumN m j' := by
      have := (div_le_iff₀ hκpos).mp hj'N
      linarith
    have h3 : B ≤ κ * cumN m j := h2.trans (mul_le_mul_of_nonneg_left h1 hκpos.le)
    exact h3
  have hmain := lintegral_stopping_le P S (fun j => measurableSet_toMeasurable _ _)
    (fun _ => 1) (I.pTail η) jstar hp
  have hlhs : ∫⁻ ω, LiteralD2b.stopIdx T (tapeOf Y ω) δ ∂P ≤
      ∫⁻ ω, ∑' j, (1 : ℝ≥0∞) * (S j).indicator 1 ω ∂P := by
    refine lintegral_mono fun ω => ?_
    rw [LiteralD2b.stopIdx_eq_tsum]
    refine tsum_le_tsum fun j => ?_
    by_cases hr : T.running (tapeOf Y ω) δ j
    · have hmem : ω ∈ S j := subset_toMeasurable P _ hr
      rw [ite_eq_left hr, Set.indicator_of_mem hmem]
      simp
    · rw [ite_eq_right hr]
      exact zero_le
  have hrhs : (∑ j ∈ Finset.range jstar, (1 : ℝ≥0∞)) +
      (∑' j, if jstar ≤ j then (1 : ℝ≥0∞) * min 1 (I.pTail η j) else 0) ≤
      ENNReal.ofReal ((jstar : ℝ) + Sig) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) hSig0, ENNReal.ofReal_natCast, hSig,
      ENNReal.ofReal_toReal hfin]
    refine add_le_add (by simp) ?_
    unfold LiteralD2c.Instance.tailSum
    refine tsum_le_tsum fun j => ?_
    by_cases hj : jstar ≤ j
    · have hj1 : j1 ≤ j := (le_max_left _ _).trans hj
      rw [ite_eq_left hj, ite_eq_left hj1]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have : 1 ≤ batchR m (j + 1) := le_trans (by omega) (le_batchR m (j + 1))
      exact_mod_cast this
    · rw [ite_eq_right hj]
      exact zero_le
  refine hlhs.trans (hmain.trans (hrhs.trans (ENNReal.ofReal_le_ofReal ?_)))
  -- real arithmetic
  have hL1 : 1 ≤ LiteralD2b.Ldelta δ := LiteralD2b.Ldelta_ge_one hδ0 hδ1
  have hlog1x : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hLeq : LiteralD2b.Ldelta δ = 1 + Real.log (1 + x) := rfl
  have hlogK := Real.log_nonneg hK
  have hfrac : 1 + B / κ ≤ Ac * (1 + x) := by
    have h1 : B / κ ≤ (1 + Real.log (Fintype.card A : ℝ)) / κ * (1 + x) := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hκpos.le
      rw [hBeq]
      nlinarith
    have hAc' : Ac = 1 + (1 + Real.log (Fintype.card A : ℝ)) / κ := rfl
    rw [hAc']
    nlinarith
  have hBκ : 0 ≤ B / κ := by positivity
  have hlogle : Real.log (1 + B / κ) ≤ Real.log Ac + Real.log (1 + x) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hfrac
  have hlog0 : 0 ≤ Real.log (1 + B / κ) := Real.log_nonneg (by linarith)
  have hone : 1 + Real.log (1 + B / κ) ≤ (1 + Real.log Ac) * LiteralD2b.Ldelta δ := by
    rw [hLeq]
    nlinarith [mul_nonneg hlogAc hlog1x]
  have hsq : (1 + Real.log (1 + B / κ)) ^ 2 ≤ ((1 + Real.log Ac) * LiteralD2b.Ldelta δ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hone 2
  have hjs : (jstar : ℝ) ≤ j1 + j' := by
    have : jstar ≤ j1 + j' := by rw [hjstar]; omega
    exact_mod_cast this
  have hj1r : (0 : ℝ) ≤ j1 := Nat.cast_nonneg _
  have hL2 : 0 ≤ LiteralD2b.Ldelta δ ^ 2 := sq_nonneg _
  have hterm : (j' : ℝ) ≤ 4 * (1 + Real.log Ac) ^ 2 * LiteralD2b.Ldelta δ ^ 2 := by
    calc (j' : ℝ) ≤ 4 * (1 + Real.log (1 + B / κ)) ^ 2 := hj'le
      _ ≤ 4 * ((1 + Real.log Ac) * LiteralD2b.Ldelta δ) ^ 2 := by linarith
      _ = 4 * (1 + Real.log Ac) ^ 2 * LiteralD2b.Ldelta δ ^ 2 := by ring
  have hexp : cStop I * (1 + LiteralD2b.Ldelta δ ^ 2) = (1 + j1 + Sig) +
      (1 + j1 + Sig) * LiteralD2b.Ldelta δ ^ 2 + 4 * (1 + Real.log Ac) ^ 2 +
      4 * (1 + Real.log Ac) ^ 2 * LiteralD2b.Ldelta δ ^ 2 := by
    rw [hcdef]; ring
  have h5 : 0 ≤ (1 + (j1 : ℝ) + Sig) * LiteralD2b.Ldelta δ ^ 2 := by positivity
  have h6 : 0 ≤ 4 * (1 + Real.log Ac) ^ 2 := by positivity
  rw [hexp]
  linarith

/-- **Proposition `prop:v34-work` for the tracker, with the instance constant
`c = cWork (T.inst μ v)`.**  `K = |A|` root actions, `J_max` a bound on the number of
unscreened components of an action, `L_δ = 1 + log (1 + log (1 / δ))`.

1. Through batch `j ≥ 1`: `W_design(j) = K (1 + ⌊log₄ j⌋)` and, on every tape,
   `W_null(j) ≤ J_max j`.
2. Model of `LiteralD2c.v34_finite_confidence` (oracle contracts, Borel allocation oracles,
   measurable jointly independent Gaussian tapes with positive variances, `C_* > 0`): for all
   `δ ∈ (0, 1)`, with `T_δ = LiteralD2b.stopIdx`,
   `E T_δ ≤ c (1 + L_δ²)`, `E W_design(T_δ) ≤ c K (1 + log (1 + L_δ))`,
   `E W_null(T_δ) ≤ c J_max (1 + L_δ²)`.

`c` is a function of the instance `(J, H, pred, μ, v)` (and the schedule) only: it does not
depend on `δ`, `J_max`, the oracles of the tracker, or the probability space. -/
theorem v34_work_inst (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas)
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {μ v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (μ x) (v x).toNNReal) P)
    (hC : 0 < (T.inst μ v).Cstar) {Jmax : ℕ} (hJmax : ∀ a, (T.J a).card ≤ Jmax) :
    (∀ j, 1 ≤ j → LiteralD2b.designWork (Fintype.card A) j =
      Fintype.card A * (1 + Nat.log 4 j)) ∧
    (∀ (y : X → ℕ → ℝ) (j : ℕ), LiteralD2b.nullWork T y j ≤ Jmax * j) ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, LiteralD2b.stopIdx T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal (cWork (T.inst μ v) * (1 + LiteralD2b.Ldelta δ ^ 2)) ∧
      ∫⁻ ω, LiteralD2b.designWorkStop (Fintype.card A) T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal (cWork (T.inst μ v) *
          (Fintype.card A * (1 + Real.log (1 + LiteralD2b.Ldelta δ)))) ∧
      ∫⁻ ω, LiteralD2b.nullWorkStop T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal (cWork (T.inst μ v) * (Jmax * (1 + LiteralD2b.Ldelta δ ^ 2))) := by
  classical
  set I := T.inst μ v with hI
  have hK1 : 1 ≤ Fintype.card A := Fintype.card_pos
  have hJ1 : 1 ≤ Jmax := by
    have := Finset.card_pos.mpr (T.hJ (Classical.arbitrary A))
    exact this.trans_le (hJmax _)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set c1 := cStop I with hc1def
  have hc11 : 1 ≤ c1 := one_le_cStop I hC
  have hlogc1 : 0 ≤ Real.log c1 := Real.log_nonneg hc11
  set c2 : ℝ := 1 + (3 + Real.log c1) / Real.log 4 with hc2
  have hcw : cWork I = max c1 c2 := rfl
  refine ⟨fun j hj => LiteralD2b.designWork_eq _ hj,
    fun y j => LiteralD2b.nullWork_le T y hJmax j, fun δ hδ0 hδ1 => ?_⟩
  rw [hcw]
  have hL1 : 1 ≤ LiteralD2b.Ldelta δ := LiteralD2b.Ldelta_ge_one hδ0 hδ1
  have hE := expected_stopIdx_le_inst T hc hm P hYm hind hv0 hlaw hC hδ0 hδ1
  rw [← hI, ← hc1def] at hE
  set c0 : ℝ := c1 * (1 + LiteralD2b.Ldelta δ ^ 2) with hc0
  have hc0ge : 1 ≤ c0 := by
    rw [hc0]
    nlinarith [sq_nonneg (LiteralD2b.Ldelta δ)]
  have hc0pos : 0 < c0 := by linarith
  refine ⟨hE.trans (ENNReal.ofReal_le_ofReal ?_), ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- design calls
    have hb : 0 ≤ (Fintype.card A : ℝ) / (c0 * Real.log 4) := by positivity
    have ha : 0 ≤ (Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4) := by
      have : 0 ≤ Real.log c0 := Real.log_nonneg hc0ge
      positivity
    calc ∫⁻ ω, LiteralD2b.designWorkStop (Fintype.card A) T (tapeOf Y ω) δ ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4)) +
            ENNReal.ofReal ((Fintype.card A : ℝ) / (c0 * Real.log 4)) *
              LiteralD2b.stopIdx T (tapeOf Y ω) δ) ∂P :=
          lintegral_mono fun ω => LiteralD2b.designWorkStop_le T _ δ hK1 hc0ge
      _ = ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4)) +
            ENNReal.ofReal ((Fintype.card A : ℝ) / (c0 * Real.log 4)) *
              ∫⁻ ω, LiteralD2b.stopIdx T (tapeOf Y ω) δ ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4)) +
            ENNReal.ofReal ((Fintype.card A : ℝ) / (c0 * Real.log 4)) * ENNReal.ofReal c0 := by
          gcongr
      _ = ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4) +
            (Fintype.card A : ℝ) / (c0 * Real.log 4) * c0) := by
          rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add ha (by positivity)]
      _ ≤ ENNReal.ofReal (max c1 c2 *
            (Fintype.card A * (1 + Real.log (1 + LiteralD2b.Ldelta δ)))) := by
          apply ENNReal.ofReal_le_ofReal
          have hlogL : 0 ≤ Real.log (1 + LiteralD2b.Ldelta δ) := Real.log_nonneg (by linarith)
          have hlogc0 : Real.log c0 ≤ Real.log c1 + 2 * Real.log (1 + LiteralD2b.Ldelta δ) := by
            rw [hc0, Real.log_mul (by linarith) (by positivity)]
            have h1 : Real.log (1 + LiteralD2b.Ldelta δ ^ 2) ≤
                Real.log ((1 + LiteralD2b.Ldelta δ) ^ 2) :=
              Real.log_le_log (by positivity) (by nlinarith)
            rw [Real.log_pow] at h1
            push_cast at h1
            linarith
          have e1 : (Fintype.card A : ℝ) / (c0 * Real.log 4) * c0 =
              (Fintype.card A : ℝ) / Real.log 4 := by
            field_simp
          rw [e1]
          have h2 : (Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4) +
              (Fintype.card A : ℝ) / Real.log 4 =
              (Fintype.card A : ℝ) * (1 + (1 + Real.log c0) / Real.log 4) := by
            field_simp
            ring
          rw [h2]
          have h3 : 1 + (1 + Real.log c0) / Real.log 4 ≤
              c2 * (1 + Real.log (1 + LiteralD2b.Ldelta δ)) := by
            have h4 : (1 + Real.log c0) / Real.log 4 ≤
                (1 + Real.log c1 + 2 * Real.log (1 + LiteralD2b.Ldelta δ)) / Real.log 4 :=
              div_le_div_of_nonneg_right (by linarith) hlog4.le
            have h5 : c2 * (1 + Real.log (1 + LiteralD2b.Ldelta δ)) =
                1 + (3 + Real.log c1) / Real.log 4 + Real.log (1 + LiteralD2b.Ldelta δ) +
                  (3 + Real.log c1) * Real.log (1 + LiteralD2b.Ldelta δ) / Real.log 4 := by
              rw [hc2]; ring
            have h6 : (1 + Real.log c1 + 2 * Real.log (1 + LiteralD2b.Ldelta δ)) / Real.log 4 ≤
                (3 + Real.log c1) / Real.log 4 +
                  (3 + Real.log c1) * Real.log (1 + LiteralD2b.Ldelta δ) / Real.log 4 := by
              rw [← add_div]
              refine div_le_div_of_nonneg_right ?_ hlog4.le
              nlinarith [mul_nonneg hlogc1 hlogL]
            linarith
          have h7 : c2 * (1 + Real.log (1 + LiteralD2b.Ldelta δ)) ≤
              max c1 c2 * (1 + Real.log (1 + LiteralD2b.Ldelta δ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
          have hK0 : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
          calc (Fintype.card A : ℝ) * (1 + (1 + Real.log c0) / Real.log 4)
              ≤ (Fintype.card A : ℝ) * (max c1 c2 * (1 + Real.log (1 + LiteralD2b.Ldelta δ))) :=
                mul_le_mul_of_nonneg_left (h3.trans h7) hK0
            _ = max c1 c2 * (Fintype.card A * (1 + Real.log (1 + LiteralD2b.Ldelta δ))) := by
                ring
  · -- null solves
    calc ∫⁻ ω, LiteralD2b.nullWorkStop T (tapeOf Y ω) δ ∂P
        ≤ ∫⁻ ω, (Jmax : ℝ≥0∞) * LiteralD2b.stopIdx T (tapeOf Y ω) δ ∂P :=
          lintegral_mono fun ω => LiteralD2b.nullWorkStop_le T _ δ hJmax hJ1
      _ = (Jmax : ℝ≥0∞) * ∫⁻ ω, LiteralD2b.stopIdx T (tapeOf Y ω) δ ∂P :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
      _ ≤ (Jmax : ℝ≥0∞) * ENNReal.ofReal (c1 * (1 + LiteralD2b.Ldelta δ ^ 2)) := by gcongr
      _ = ENNReal.ofReal (Jmax * (c1 * (1 + LiteralD2b.Ldelta δ ^ 2))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (max c1 c2 * (Jmax * (1 + LiteralD2b.Ldelta δ ^ 2))) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : c1 * (Jmax * (1 + LiteralD2b.Ldelta δ ^ 2)) ≤
              max c1 c2 * (Jmax * (1 + LiteralD2b.Ldelta δ ^ 2)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          linarith [mul_left_comm (Jmax : ℝ) c1 (1 + LiteralD2b.Ldelta δ ^ 2)]

end Expect

/-! ### The uniform form -/

universe uΩ

variable {X A Z U : Type*} [Fintype X] [Nonempty X] [DecidableEq X] [Fintype A] [Nonempty A]
  [DecidableEq A]

/-- **Proposition `prop:v34-work`, uniform form.**  Fix the instance `I` (root-action data
`J, H, pred`, true means `I.mean`, true variances `I.var > 0`, `C_* > 0`).  There is one
constant `c ≥ 1` (namely `cWork I`) such that for every tracker `T` with that instance that
meets the oracle contracts with Borel allocation oracles, every `J_max` bounding `|J_a|`,
every probability space carrying measurable, jointly independent tapes
`Y x n ~ N(I.mean x, I.var x)`, and every `δ ∈ (0, 1)`:
`E T_δ ≤ c (1 + L_δ²)`, `E W_design(T_δ) ≤ c K (1 + log (1 + L_δ))` and
`E W_null(T_δ) ≤ c J_max (1 + L_δ²)`. -/
theorem v34_work_uniform (I : LiteralD2c.Instance X A Z U) (hv0 : ∀ x, 0 < I.var x)
    (hC : 0 < I.Cstar) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ T : Tracker X A Z U, T.inst I.mean I.var = I → T.Contract → T.Meas →
      ∀ {Jmax : ℕ}, (∀ a, (T.J a).card ≤ Jmax) →
      ∀ (Ω : Type uΩ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y : X → ℕ → Ω → ℝ), (∀ x n, Measurable (Y x n)) →
        iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P →
        (∀ x n, HasLaw (Y x n) (gaussianReal (I.mean x) (I.var x).toNNReal) P) →
        ∀ δ : ℝ, 0 < δ → δ < 1 →
          ∫⁻ ω, LiteralD2b.stopIdx T (tapeOf Y ω) δ ∂P ≤
            ENNReal.ofReal (c * (1 + LiteralD2b.Ldelta δ ^ 2)) ∧
          ∫⁻ ω, LiteralD2b.designWorkStop (Fintype.card A) T (tapeOf Y ω) δ ∂P ≤
            ENNReal.ofReal (c * (Fintype.card A * (1 + Real.log (1 + LiteralD2b.Ldelta δ)))) ∧
          ∫⁻ ω, LiteralD2b.nullWorkStop T (tapeOf Y ω) δ ∂P ≤
            ENNReal.ofReal (c * (Jmax * (1 + LiteralD2b.Ldelta δ ^ 2))) := by
  refine ⟨cWork I, one_le_cWork I hC, fun T hTI hc hm Jmax hJmax Ω _ P _ Y hYm hind hlaw δ hδ0
    hδ1 => ?_⟩
  have h := (v34_work_inst T hc hm P hYm hind (μ := I.mean) (v := I.var) hv0 hlaw
    (by rw [hTI]; exact hC) hJmax).2.2 δ hδ0 hδ1
  rw [hTI] at h
  exact h

end

end LiteralD2e

end JointRootCert
