/-
Proposition `prop:v34-work` (Global solver-call reduction under sparse refreshes and
action-local evidence), for the formal tracker `Tracker` of `UnknownVarianceTracker.lean`.

* Stopping batch index.  `Stops T y δ`: the test of the `δ`-procedure passes at some completed
  batch; `stopIdx T y δ` is the first such batch (`T_δ`, with value `∞` if there is none), and
  `stopIdx_eq_tsum` is the survival identity `T_δ = ∑_j 1{τ_δ > N_j}`.
* Work counts.  `refreshCount j` counts the batches `i ≤ j` at which `Tracker.step` takes its
  refresh branch; at every other batch the state update does not involve the design oracle
  (`step_of_not_refresh`).  A refresh evaluates the design game once per root action, so
  `designWork K j = K · refreshCount j`.  `nullWork T y j = ∑_{i ≤ j} |J (A_i)|` counts the
  component-null solves: at batch `i` the wealth update and the test only involve the
  components of the selected action (`wealth_of_ne_sel`).  Deterministic counts:
  `designWork_eq` (`= K (1 + ⌊log₄ j⌋)`), `nullWork_le` (`≤ J_max j`).
* Clock inversion.  `clock_inversion`, `firstClock_le`:
  `min {j : N_j ≥ t} ≤ 4 (1 + log (1 + t))²`.
* `expected_stopIdx_le`: `E T_δ ≤ c (1 + L_δ²)` with `L_δ = 1 + log (1 + log (1 / δ))` and `c`
  independent of `δ`, from `tracker_tail` and the clock inversion.
* `v34_work`: the proposition for the tracker, with the two expectation bounds
  `E W_design(T_δ) ≤ c K (1 + log (1 + L_δ))` and `E W_null(T_δ) ≤ c J_max (1 + L_δ²)`.

Expectations are lower Lebesgue integrals of `[0, ∞]`-valued functions (the work at stopping is
`∞` on the event that the procedure never stops); no measurability of the oracles is assumed.
-/
import JointRootCert.UnknownVarianceCorrect

namespace JointRootCert

namespace LiteralD2b

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-- `L_δ = 1 + log (1 + log (1 / δ))`. -/
def Ldelta (δ : ℝ) : ℝ := 1 + Real.log (1 + Real.log (1 / δ))

lemma log_inv_pos {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : 0 < Real.log (1 / δ) := by
  apply Real.log_pos
  rw [lt_div_iff₀ h0]
  linarith

lemma Ldelta_ge_one {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : 1 ≤ Ldelta δ := by
  have := log_inv_pos h0 h1
  have : 0 ≤ Real.log (1 + Real.log (1 / δ)) := Real.log_nonneg (by linarith)
  unfold Ldelta
  linarith

/-! ### Clock inversion -/

/-- **Clock inversion.**  For the denominator-free schedule with `m` query types and every
`t ≥ 0` there is a batch index `j ≤ 4 (1 + log (1 + t))²` with `N_j ≥ t`. -/
theorem clock_inversion (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ j : ℕ, 1 ≤ j ∧ t ≤ cumN m j ∧ (j : ℝ) ≤ 4 * (1 + Real.log (1 + t)) ^ 2 := by
  set x := Real.log (1 + t) with hx
  have hx0 : 0 ≤ x := Real.log_nonneg (by linarith)
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hl2pos : 0 < Real.log 2 := by linarith
  set n := ⌈x / Real.log 2⌉₊ with hn
  set k := n + 1 with hk
  have hnge : x / Real.log 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hnlt : (n : ℝ) < x / Real.log 2 + 1 := Nat.ceil_lt_add_one (div_nonneg hx0 hl2pos.le)
  have hsq : Nat.sqrt (k * k + 1) = k := Nat.sqrt_add_eq k (by omega)
  have hj1 : 1 ≤ k * k := Nat.mul_pos (by omega) (by omega)
  have hN := cumN_ge_pow m hj1
  rw [hsq] at hN
  have hpow : 1 + t ≤ (2 : ℝ) ^ n := by
    have h1 : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have h2 : x ≤ n * Real.log 2 := (div_le_iff₀ hl2pos).mp hnge
    calc 1 + t = Real.exp x := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (n * Real.log 2) := Real.exp_le_exp.mpr h2
      _ = (2 : ℝ) ^ n := h1.symm
  refine ⟨k * k, hj1, ?_, ?_⟩
  · have h1 : (2 : ℝ) ^ n ≤ ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by
      have : 2 ^ n ≤ k * 2 ^ (k - 1) := by
        rw [hk, Nat.add_sub_cancel]
        exact Nat.le_mul_of_pos_left _ (by omega)
      exact_mod_cast this
    have h2 : ((k * 2 ^ (k - 1) : ℕ) : ℝ) ≤ cumN m (k * k) := by exact_mod_cast hN
    linarith
  · have hk2 : (k : ℝ) ≤ 2 * (1 + x) := by
      have h1 : (k : ℝ) = n + 1 := by rw [hk]; push_cast; ring
      have h2 : x / Real.log 2 ≤ 2 * x := by
        rw [div_le_iff₀ hl2pos]
        nlinarith
      linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    push_cast
    nlinarith

lemma exists_clock (m : ℕ) (t : ℝ) : ∃ j : ℕ, t ≤ cumN m j := by
  rcases le_total 0 t with h | h
  · obtain ⟨j, -, hj, -⟩ := clock_inversion m h
    exact ⟨j, hj⟩
  · exact ⟨0, h.trans (Nat.cast_nonneg _)⟩

open Classical in
/-- `min {j : N_j ≥ t}`. -/
def firstClock (m : ℕ) (t : ℝ) : ℕ := Nat.find (exists_clock m t)

lemma firstClock_spec (m : ℕ) (t : ℝ) : t ≤ cumN m (firstClock m t) := by
  classical
  exact Nat.find_spec (exists_clock m t)

/-- **`min {j : N_j ≥ t} = O((1 + log (1 + t))²)`**, with constant `4`. -/
theorem firstClock_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (firstClock m t : ℝ) ≤ 4 * (1 + Real.log (1 + t)) ^ 2 := by
  classical
  obtain ⟨j, -, hj, hle⟩ := clock_inversion m ht
  have h : firstClock m t ≤ j := Nat.find_min' (exists_clock m t) hj
  exact le_trans (by exact_mod_cast h) hle

/-! ### Stopping batch index and work counts of the tracker -/

section Counts

variable {X A Z U : Type*}

/-- The number of batches `i ≤ j` at which `Tracker.step` takes its refresh branch. -/
def refreshCount (j : ℕ) : ℕ := ((Icc 1 j).filter fun i => 4 ^ Nat.log 4 i = i).card

/-- `W_design(j)`: globally certified design-game calls through batch `j`, one per root action
(`K` of them) at each refresh. -/
def designWork (K j : ℕ) : ℕ := K * refreshCount j

/-- `W_null(j)`: component-null likelihood solves through batch `j`, one per component of the
action selected at each batch. -/
def nullWork (T : Tracker X A Z U) (y : X → ℕ → ℝ) (j : ℕ) : ℕ :=
  ∑ i ∈ Icc 1 j, (T.J (T.sel y i)).card

/-- At a batch that is not a refresh the state update does not involve the design oracle or
its displayed scores: the incumbent and its design are kept and only the allocation is made. -/
lemma step_of_not_refresh (T : Tracker X A Z U) (y : X → ℕ → ℝ) {j : ℕ} (s : TState X A)
    (h : 4 ^ Nat.log 4 (j + 1) ≠ j + 1) :
    T.step y j s = ⟨fun x => s.cnt x + T.alloc (j + 1) s.w x, s.inc, s.w⟩ := by
  unfold Tracker.step
  simp only [h, ↓reduceIte]

/-- The wealth of an action that is not selected at batch `j + 1` is not updated: no
component-null solve is made for it. -/
lemma wealth_of_ne_sel [DecidableEq A] (T : Tracker X A Z U) (y : X → ℕ → ℝ) (a : A) (z : Z)
    (j : ℕ) (h : T.sel y (j + 1) ≠ a) : T.wealth y a z (j + 1) = T.wealth y a z j :=
  localWealth_skip _ _ _ _ h

theorem refreshCount_eq {j : ℕ} (hj : 1 ≤ j) : refreshCount j = Nat.log 4 j + 1 := by
  classical
  rw [← card_fourPower_refreshes hj]
  unfold refreshCount
  congr 1
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Nat.log 4 i, h2.symm⟩
  · rintro ⟨h1, k, rfl⟩
    exact ⟨h1, by rw [Nat.log_pow (by norm_num)]⟩

/-- **`W_design(j) ≤ K (1 + ⌊log₄ j⌋)`**, with equality. -/
theorem designWork_eq (K : ℕ) {j : ℕ} (hj : 1 ≤ j) : designWork K j = K * (1 + Nat.log 4 j) := by
  rw [designWork, refreshCount_eq hj, add_comm]

/-- **`W_null(j) ≤ J_max j`.** -/
theorem nullWork_le (T : Tracker X A Z U) (y : X → ℕ → ℝ) {Jmax : ℕ}
    (hJ : ∀ a, (T.J a).card ≤ Jmax) (j : ℕ) : nullWork T y j ≤ Jmax * j :=
  nullSolves_le T.J (T.sel y) hJ j

variable [Fintype A] [DecidableEq A]

/-- The `δ`-procedure stops: the test passes at some completed batch. -/
def Stops (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : Prop := ∃ j, 1 ≤ j ∧ T.test y δ j

open Classical in
/-- The batch index at stopping `T_δ` (so that `τ_δ = N_{T_δ}`): the first completed batch at
which the test passes, `∞` if there is none. -/
def stopIdx (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  if h : Stops T y δ then ((Nat.find h : ℕ) : ℝ≥0∞) else ⊤

open Classical in
/-- `W_design(T_δ)`: design-game calls made up to stopping (`∞` if the procedure never stops). -/
def designWorkStop (K : ℕ) (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  if h : Stops T y δ then ((designWork K (Nat.find h) : ℕ) : ℝ≥0∞) else ⊤

open Classical in
/-- `W_null(T_δ)`: component-null solves made up to stopping (`∞` if the procedure never
stops). -/
def nullWorkStop (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  if h : Stops T y δ then ((nullWork T y (Nat.find h) : ℕ) : ℝ≥0∞) else ⊤

variable (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ)

open Classical in
lemma running_iff (h : Stops T y δ) (j : ℕ) : T.running y δ j ↔ j < Nat.find h := by
  constructor
  · intro hr
    by_contra hcon
    have hs := Nat.find_spec h
    exact hr _ (Finset.mem_Icc.mpr ⟨hs.1, not_lt.mp hcon⟩) hs.2
  · intro hlt i hi htest
    have hi' := Finset.mem_Icc.mp hi
    have : Nat.find h ≤ i := Nat.find_min' h ⟨hi'.1, htest⟩
    omega

lemma running_of_not_stops (h : ¬ Stops T y δ) (j : ℕ) : T.running y δ j :=
  fun i hi htest => h ⟨i, (Finset.mem_Icc.mp hi).1, htest⟩

open Classical in
/-- **Survival identity for the batch index**: `T_δ = ∑_{j ≥ 0} 1{τ_δ > N_j}`. -/
theorem stopIdx_eq_tsum :
    stopIdx T y δ = ∑' j, (if T.running y δ j then (1 : ℝ≥0∞) else 0) := by
  by_cases h : Stops T y δ
  · have e : stopIdx T y δ = ((Nat.find h : ℕ) : ℝ≥0∞) := by
      unfold stopIdx
      exact dite_eq_left h
    rw [e]
    have h1 := survival_identity (fun _ => (1 : ℝ≥0∞)) (Nat.find h)
    simp only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
    rw [← h1]
    refine tsum_congr fun j => ?_
    by_cases hj : j < Nat.find h
    · rw [ite_eq_left ((running_iff T y δ h j).mpr hj), ite_eq_left hj]
    · rw [ite_eq_right (fun hr => hj ((running_iff T y δ h j).mp hr)), ite_eq_right hj]
  · have e : stopIdx T y δ = ⊤ := by
      unfold stopIdx
      exact dite_eq_right h
    rw [e]
    have h1 : ∀ j, (if T.running y δ j then (1 : ℝ≥0∞) else 0) = 1 := fun j =>
      ite_eq_left (running_of_not_stops T y δ h j)
    simp only [h1]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm

open Classical in
/-- `W_null(T_δ) ≤ J_max T_δ`. -/
lemma nullWorkStop_le {Jmax : ℕ} (hJ : ∀ a, (T.J a).card ≤ Jmax) (hJ1 : 1 ≤ Jmax) :
    nullWorkStop T y δ ≤ (Jmax : ℝ≥0∞) * stopIdx T y δ := by
  by_cases h : Stops T y δ
  · have e1 : nullWorkStop T y δ = ((nullWork T y (Nat.find h) : ℕ) : ℝ≥0∞) := by
      unfold nullWorkStop
      exact dite_eq_left h
    have e2 : stopIdx T y δ = ((Nat.find h : ℕ) : ℝ≥0∞) := by
      unfold stopIdx
      exact dite_eq_left h
    rw [e1, e2]
    exact_mod_cast nullWork_le T y hJ (Nat.find h)
  · have e2 : stopIdx T y δ = ⊤ := by
      unfold stopIdx
      exact dite_eq_right h
    rw [e2, ENNReal.mul_top (by exact_mod_cast (by omega : Jmax ≠ 0))]
    exact le_top

open Classical in
/-- `W_design(T_δ) ≤ K (1 + log c₀ / log 4) + K / (c₀ log 4) · T_δ` for every `c₀ ≥ 1`
(the tangent-line form of Jensen's inequality for the logarithm). -/
lemma designWorkStop_le {K : ℕ} (hK : 1 ≤ K) {c0 : ℝ} (hc0 : 1 ≤ c0) :
    designWorkStop K T y δ ≤ ENNReal.ofReal (K * (1 + Real.log c0 / Real.log 4)) +
      ENNReal.ofReal (K / (c0 * Real.log 4)) * stopIdx T y δ := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc0pos : 0 < c0 := by linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hb : 0 < (K : ℝ) / (c0 * Real.log 4) := by positivity
  by_cases h : Stops T y δ
  · have e1 : designWorkStop K T y δ = ((designWork K (Nat.find h) : ℕ) : ℝ≥0∞) := by
      unfold designWorkStop
      exact dite_eq_left h
    have e2 : stopIdx T y δ = ((Nat.find h : ℕ) : ℝ≥0∞) := by
      unfold stopIdx
      exact dite_eq_left h
    set n := Nat.find h with hn
    have hn1 : 1 ≤ n := (Nat.find_spec h).1
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have ha : 0 ≤ (K : ℝ) * (1 + Real.log c0 / Real.log 4) := by
      have : 0 ≤ Real.log c0 := Real.log_nonneg hc0
      positivity
    have hreal : ((designWork K n : ℕ) : ℝ) ≤
        K * (1 + Real.log c0 / Real.log 4) + K / (c0 * Real.log 4) * n := by
      rw [designWork_eq K hn1]
      push_cast
      have h1 := Real.natLog_le_logb n 4
      have e : Real.logb ((4 : ℕ) : ℝ) (n : ℝ) = Real.log n / Real.log 4 := by
        simp [Real.logb]
      rw [e] at h1
      have h2 := Real.log_le_sub_one_of_pos (div_pos hnr hc0pos)
      rw [Real.log_div hnr.ne' hc0pos.ne'] at h2
      have h3 : Real.log n / Real.log 4 ≤ (Real.log c0 + n / c0) / Real.log 4 :=
        div_le_div_of_nonneg_right (by linarith) hlog4.le
      have h4 : (K : ℝ) * (1 + (Nat.log 4 n : ℝ)) ≤
          K * (1 + (Real.log c0 + n / c0) / Real.log 4) :=
        mul_le_mul_of_nonneg_left (by linarith) hKr.le
      have e2 : (K : ℝ) * (1 + (Real.log c0 + n / c0) / Real.log 4) =
          K * (1 + Real.log c0 / Real.log 4) + K / (c0 * Real.log 4) * n := by
        field_simp
        ring
      linarith
    rw [e1, e2, ← ENNReal.ofReal_natCast (designWork K n), ← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_mul hb.le, ← ENNReal.ofReal_add ha (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have e2 : stopIdx T y δ = ⊤ := by
      unfold stopIdx
      exact dite_eq_right h
    rw [e2, ENNReal.mul_top (by simpa using hb), add_top]
    exact le_top

end Counts

/-! ### Expected stopping batch index -/

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Nonempty X]
  [DecidableEq X] [Fintype A] [DecidableEq A]

/-- **`E T_δ ≤ c (1 + L_δ²)` with `c` independent of `δ`.**  Model and hypotheses as in
`tracker_tail` / `v34_adaptive_rate`: the tracker satisfies the oracle contracts, the intrinsic
tapes are independent `N(μₓ, vₓ)` with `vₓ > 0`, and `C = C_* > 0` is attained.  The proof is
the manuscript's: `E T_δ ≤ j_* + ∑_{j ≥ j_*} min {1, p_j}` from `eq:v34-tail-stop`
(`tracker_tail`, with `η = C_* / 4`), and `j_* ≤ j₁ + min {j : (C_*/2) N_j ≥ log (K / δ)}`
is bounded by the clock inversion. -/
theorem expected_stopIdx_le (T : Tracker X A Z U) (hc : T.Contract) (P : Measure Ω)
    [IsProbabilityMeasure P] {μ v : X → ℝ} (hv0 : ∀ x, 0 < v x) {Y : X → ℕ → Ω → ℝ}
    (hind : ∀ x, iIndepFun (Y x) P)
    (hY : ∀ x i, HasLaw (Y x i) (gaussianReal (μ x) (v x).toNNReal) P) {C : ℝ} (hC : 0 < C)
    (hCmax : ∀ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v ≤ C)
    (hCatt : ∃ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v = C) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, stopIdx T (fun x n => Y x n ω) δ ∂P ≤ ENNReal.ofReal (c * (1 + Ldelta δ ^ 2)) := by
  classical
  set m := Fintype.card X with hm
  have hA : Nonempty A := ⟨hCatt.choose⟩
  have hK : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  obtain ⟨j1, p, hfin, htl⟩ := tracker_tail T hc P hv0 hind hY hC hCmax hCatt
    (η := C / 4) (by positivity) (by linarith)
  set κ : ℝ := C - 2 * (C / 4) with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  set Sig : ℝ := (∑' j, if j1 ≤ j then ENNReal.ofReal (batchR m (j + 1)) * min 1 (p j)
    else 0).toReal with hSig
  have hSig0 : 0 ≤ Sig := ENNReal.toReal_nonneg
  have hlogK : 0 ≤ Real.log (Fintype.card A : ℝ) := Real.log_nonneg hK
  set Ac : ℝ := 1 + (1 + Real.log (Fintype.card A : ℝ)) / κ with hAc
  have hAc1 : 1 ≤ Ac := by
    have : 0 ≤ (1 + Real.log (Fintype.card A : ℝ)) / κ := by positivity
    rw [hAc]; linarith
  have hlogAc : 0 ≤ Real.log Ac := Real.log_nonneg hAc1
  set c : ℝ := 1 + j1 + Sig + 4 * (1 + Real.log Ac) ^ 2 with hcdef
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) ≤ j1 := Nat.cast_nonneg _
    have : 0 ≤ 4 * (1 + Real.log Ac) ^ 2 := by positivity
    rw [hcdef]; linarith
  refine ⟨c, hc1, fun δ hδ0 hδ1 => ?_⟩
  set x := Real.log (1 / δ) with hx
  have hx0 : 0 < x := log_inv_pos hδ0 hδ1
  set B := Real.log ((Fintype.card A : ℝ) / δ) with hB
  have hBeq : B = Real.log (Fintype.card A : ℝ) + x := by
    rw [hB, hx, Real.log_div (by linarith) hδ0.ne', one_div, Real.log_inv]
    ring
  have hB0 : 0 ≤ B := by rw [hBeq]; linarith
  obtain ⟨j', -, hj'N, hj'le⟩ := clock_inversion m (t := B / κ) (by positivity)
  set jstar := max j1 j' with hjstar
  set S : ℕ → Set Ω := fun j => toMeasurable P {ω | T.running (fun x n => Y x n ω) δ j} with hS
  have hp : ∀ j, jstar ≤ j → P (S j) ≤ p j := by
    intro j hj
    rw [hS]
    simp only
    rw [measure_toMeasurable]
    refine htl δ hδ0 j ((le_max_left _ _).trans hj) ?_
    have h1 : (cumN m j' : ℝ) ≤ cumN m j := by
      exact_mod_cast cumN_mono m ((le_max_right _ _).trans hj)
    have h2 : B ≤ κ * cumN m j' := by
      have := (div_le_iff₀ hκpos).mp hj'N
      linarith
    calc B ≤ κ * cumN m j' := h2
      _ ≤ κ * cumN m j := mul_le_mul_of_nonneg_left h1 hκpos.le
  have hmain := lintegral_stopping_le P S (fun j => measurableSet_toMeasurable _ _)
    (fun _ => 1) p jstar hp
  have hlhs : ∫⁻ ω, stopIdx T (fun x n => Y x n ω) δ ∂P ≤
      ∫⁻ ω, ∑' j, (1 : ℝ≥0∞) * (S j).indicator 1 ω ∂P := by
    refine lintegral_mono fun ω => ?_
    rw [stopIdx_eq_tsum]
    refine tsum_le_tsum fun j => ?_
    by_cases hr : T.running (fun x n => Y x n ω) δ j
    · have hmem : ω ∈ S j := subset_toMeasurable P _ hr
      rw [ite_eq_left hr, Set.indicator_of_mem hmem]
      simp
    · rw [ite_eq_right hr]
      exact zero_le
  have hrhs : (∑ j ∈ Finset.range jstar, (1 : ℝ≥0∞)) +
      (∑' j, if jstar ≤ j then (1 : ℝ≥0∞) * min 1 (p j) else 0) ≤
      ENNReal.ofReal ((jstar : ℝ) + Sig) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) hSig0, ENNReal.ofReal_natCast, hSig,
      ENNReal.ofReal_toReal hfin]
    refine add_le_add (by simp) (tsum_le_tsum fun j => ?_)
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
  have hL1 : 1 ≤ Ldelta δ := Ldelta_ge_one hδ0 hδ1
  have hlog1x : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hLeq : Ldelta δ = 1 + Real.log (1 + x) := rfl
  have hfrac : 1 + B / κ ≤ Ac * (1 + x) := by
    have h1 : B / κ ≤ (1 + Real.log (Fintype.card A : ℝ)) / κ * (1 + x) := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hκpos.le
      rw [hBeq]
      nlinarith
    rw [hAc]
    nlinarith
  have hBκ : 0 ≤ B / κ := by positivity
  have hlogle : Real.log (1 + B / κ) ≤ Real.log Ac + Real.log (1 + x) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hfrac
  have hlog0 : 0 ≤ Real.log (1 + B / κ) := Real.log_nonneg (by linarith)
  have hone : 1 + Real.log (1 + B / κ) ≤ (1 + Real.log Ac) * Ldelta δ := by
    rw [hLeq]
    nlinarith [mul_nonneg hlogAc hlog1x]
  have hsq : (1 + Real.log (1 + B / κ)) ^ 2 ≤ ((1 + Real.log Ac) * Ldelta δ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hone 2
  have hjs : (jstar : ℝ) ≤ j1 + j' := by
    have : jstar ≤ j1 + j' := by rw [hjstar]; omega
    exact_mod_cast this
  have hj1r : (0 : ℝ) ≤ j1 := Nat.cast_nonneg _
  have hL2 : 0 ≤ Ldelta δ ^ 2 := sq_nonneg _
  have hterm : (j' : ℝ) ≤ 4 * (1 + Real.log Ac) ^ 2 * Ldelta δ ^ 2 := by
    calc (j' : ℝ) ≤ 4 * (1 + Real.log (1 + B / κ)) ^ 2 := hj'le
      _ ≤ 4 * ((1 + Real.log Ac) * Ldelta δ) ^ 2 := by linarith
      _ = 4 * (1 + Real.log Ac) ^ 2 * Ldelta δ ^ 2 := by ring
  have hexp : c * (1 + Ldelta δ ^ 2) = (1 + j1 + Sig) + (1 + j1 + Sig) * Ldelta δ ^ 2 +
      4 * (1 + Real.log Ac) ^ 2 + 4 * (1 + Real.log Ac) ^ 2 * Ldelta δ ^ 2 := by
    rw [hcdef]; ring
  have h5 : 0 ≤ (1 + (j1 : ℝ) + Sig) * Ldelta δ ^ 2 := by positivity
  have h6 : 0 ≤ 4 * (1 + Real.log Ac) ^ 2 := by positivity
  rw [hexp]
  linarith

/-- **Proposition `prop:v34-work` for the tracker.**  `K = |A|` root actions, `J_max` a bound
on the number of unscreened components of an action, `L_δ = 1 + log (1 + log (1 / δ))`.

1. Through batch `j ≥ 1` the tracker makes `W_design(j) = K (1 + ⌊log₄ j⌋)` design-game calls
   and, on every tape, `W_null(j) ≤ J_max j` component-null solves.
2. Under the model of `thm:v34-adaptive` (oracle contracts, independent Gaussian tapes with
   positive variances, `C_* > 0` attained) there is a constant `c`, independent of `δ`, such
   that for all `δ ∈ (0, 1)`:
   `E T_δ ≤ c (1 + L_δ²)`,
   `E W_design(T_δ) ≤ c K (1 + log (1 + L_δ))`, and
   `E W_null(T_δ) ≤ c J_max (1 + L_δ²)`,
   where `T_δ` is the batch index at stopping (`stopIdx`).

Expectations are lower integrals of `[0, ∞]`-valued functions. -/
theorem v34_work (T : Tracker X A Z U) (hc : T.Contract) (P : Measure Ω)
    [IsProbabilityMeasure P] {μ v : X → ℝ} (hv0 : ∀ x, 0 < v x) {Y : X → ℕ → Ω → ℝ}
    (hind : ∀ x, iIndepFun (Y x) P)
    (hY : ∀ x i, HasLaw (Y x i) (gaussianReal (μ x) (v x).toNNReal) P) {C : ℝ} (hC : 0 < C)
    (hCmax : ∀ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v ≤ C)
    (hCatt : ∃ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v = C)
    {Jmax : ℕ} (hJmax : ∀ a, (T.J a).card ≤ Jmax) :
    (∀ j, 1 ≤ j → designWork (Fintype.card A) j = Fintype.card A * (1 + Nat.log 4 j)) ∧
    (∀ (y : X → ℕ → ℝ) (j : ℕ), nullWork T y j ≤ Jmax * j) ∧
    ∃ c : ℝ, 1 ≤ c ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, stopIdx T (fun x n => Y x n ω) δ ∂P ≤ ENNReal.ofReal (c * (1 + Ldelta δ ^ 2)) ∧
      ∫⁻ ω, designWorkStop (Fintype.card A) T (fun x n => Y x n ω) δ ∂P ≤
        ENNReal.ofReal (c * (Fintype.card A * (1 + Real.log (1 + Ldelta δ)))) ∧
      ∫⁻ ω, nullWorkStop T (fun x n => Y x n ω) δ ∂P ≤
        ENNReal.ofReal (c * (Jmax * (1 + Ldelta δ ^ 2))) := by
  classical
  have hA : Nonempty A := ⟨hCatt.choose⟩
  have hK1 : 1 ≤ Fintype.card A := Fintype.card_pos
  have hKr : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast hK1
  have hJ1 : 1 ≤ Jmax := by
    have := Finset.card_pos.mpr (T.hJ hA.some)
    exact this.trans_le (hJmax _)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨c1, hc11, hET⟩ := expected_stopIdx_le T hc P hv0 hind hY hC hCmax hCatt
  have hlogc1 : 0 ≤ Real.log c1 := Real.log_nonneg hc11
  set c2 : ℝ := 1 + (3 + Real.log c1) / Real.log 4 with hc2
  have hc2ge : 1 ≤ c2 := by
    have : 0 ≤ (3 + Real.log c1) / Real.log 4 := by positivity
    rw [hc2]; linarith
  refine ⟨fun j hj => designWork_eq _ hj, fun y j => nullWork_le T y hJmax j,
    max c1 c2, le_max_of_le_left hc11, fun δ hδ0 hδ1 => ?_⟩
  have hL1 : 1 ≤ Ldelta δ := Ldelta_ge_one hδ0 hδ1
  have hE := hET δ hδ0 hδ1
  set c0 : ℝ := c1 * (1 + Ldelta δ ^ 2) with hc0
  have hc0ge : 1 ≤ c0 := by
    rw [hc0]
    nlinarith [sq_nonneg (Ldelta δ)]
  have hc0pos : 0 < c0 := by linarith
  refine ⟨hE.trans (ENNReal.ofReal_le_ofReal ?_), ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- design calls
    have hb : 0 ≤ (Fintype.card A : ℝ) / (c0 * Real.log 4) := by positivity
    have ha : 0 ≤ (Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4) := by
      have : 0 ≤ Real.log c0 := Real.log_nonneg hc0ge
      positivity
    calc ∫⁻ ω, designWorkStop (Fintype.card A) T (fun x n => Y x n ω) δ ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4)) +
            ENNReal.ofReal ((Fintype.card A : ℝ) / (c0 * Real.log 4)) *
              stopIdx T (fun x n => Y x n ω) δ) ∂P :=
          lintegral_mono fun ω => designWorkStop_le T _ δ hK1 hc0ge
      _ = ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4)) +
            ENNReal.ofReal ((Fintype.card A : ℝ) / (c0 * Real.log 4)) *
              ∫⁻ ω, stopIdx T (fun x n => Y x n ω) δ ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4)) +
            ENNReal.ofReal ((Fintype.card A : ℝ) / (c0 * Real.log 4)) * ENNReal.ofReal c0 := by
          gcongr
      _ = ENNReal.ofReal ((Fintype.card A : ℝ) * (1 + Real.log c0 / Real.log 4) +
            (Fintype.card A : ℝ) / (c0 * Real.log 4) * c0) := by
          rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add ha (by positivity)]
      _ ≤ ENNReal.ofReal (max c1 c2 *
            (Fintype.card A * (1 + Real.log (1 + Ldelta δ)))) := by
          apply ENNReal.ofReal_le_ofReal
          have hlogL : 0 ≤ Real.log (1 + Ldelta δ) := Real.log_nonneg (by linarith)
          have hlogc0 : Real.log c0 ≤ Real.log c1 + 2 * Real.log (1 + Ldelta δ) := by
            rw [hc0, Real.log_mul (by linarith) (by positivity)]
            have h1 : Real.log (1 + Ldelta δ ^ 2) ≤ Real.log ((1 + Ldelta δ) ^ 2) :=
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
              c2 * (1 + Real.log (1 + Ldelta δ)) := by
            have h4 : (1 + Real.log c0) / Real.log 4 ≤
                (1 + Real.log c1 + 2 * Real.log (1 + Ldelta δ)) / Real.log 4 :=
              div_le_div_of_nonneg_right (by linarith) hlog4.le
            have h5 : c2 * (1 + Real.log (1 + Ldelta δ)) =
                1 + (3 + Real.log c1) / Real.log 4 + Real.log (1 + Ldelta δ) +
                  (3 + Real.log c1) * Real.log (1 + Ldelta δ) / Real.log 4 := by
              rw [hc2]; ring
            have h6 : (1 + Real.log c1 + 2 * Real.log (1 + Ldelta δ)) / Real.log 4 ≤
                (3 + Real.log c1) / Real.log 4 +
                  (3 + Real.log c1) * Real.log (1 + Ldelta δ) / Real.log 4 := by
              rw [← add_div]
              refine div_le_div_of_nonneg_right ?_ hlog4.le
              nlinarith [mul_nonneg hlogc1 hlogL]
            linarith
          have h7 : c2 * (1 + Real.log (1 + Ldelta δ)) ≤
              max c1 c2 * (1 + Real.log (1 + Ldelta δ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
          have hK0 : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
          calc (Fintype.card A : ℝ) * (1 + (1 + Real.log c0) / Real.log 4)
              ≤ (Fintype.card A : ℝ) * (max c1 c2 * (1 + Real.log (1 + Ldelta δ))) :=
                mul_le_mul_of_nonneg_left (h3.trans h7) hK0
            _ = max c1 c2 * (Fintype.card A * (1 + Real.log (1 + Ldelta δ))) := by ring
  · -- null solves
    calc ∫⁻ ω, nullWorkStop T (fun x n => Y x n ω) δ ∂P
        ≤ ∫⁻ ω, (Jmax : ℝ≥0∞) * stopIdx T (fun x n => Y x n ω) δ ∂P :=
          lintegral_mono fun ω => nullWorkStop_le T _ δ hJmax hJ1
      _ = (Jmax : ℝ≥0∞) * ∫⁻ ω, stopIdx T (fun x n => Y x n ω) δ ∂P :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
      _ ≤ (Jmax : ℝ≥0∞) * ENNReal.ofReal (c1 * (1 + Ldelta δ ^ 2)) := by gcongr
      _ = ENNReal.ofReal (Jmax * (c1 * (1 + Ldelta δ ^ 2))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (max c1 c2 * (Jmax * (1 + Ldelta δ ^ 2))) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : c1 * (Jmax * (1 + Ldelta δ ^ 2)) ≤ max c1 c2 * (Jmax * (1 + Ldelta δ ^ 2)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          linarith [mul_left_comm (Jmax : ℝ) c1 (1 + Ldelta δ ^ 2)]

end Expect

end

end LiteralD2b

end JointRootCert
