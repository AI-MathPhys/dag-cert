/-
Unknown-variance Gaussian tracking: the sharp-rate proof
(manuscript, proof of Theorem `thm:v34-adaptive` in `app:v34-theory`).

Results covered, in the order of the manuscript's proof (see the doc comment of each theorem
for what is proved and what is assumed):

* the denominator-free batch schedule `M_j, b_j, R_j, N_j, 𝔟_j, H_j`: `clockM`, `baseB`,
  `batchR`, `cumN`, `cumB`, `refH`, with `tendsto_baseline_fraction` (`m b_j / R_j → 0`),
  `tendsto_batchR_atTop`, `tendsto_index_div_cumN` (`j / N_j → 0`),
  `tendsto_batchR_div_cumN` (`R_{j+1} / N_j → 0`), `refH_bounds` (`j/16 < H_j ≤ j/4`),
  `tendsto_cumN_refH_div` (`N_{H_j - 1} / N_j → 0`), `exists_schedule_onset` (existence of
  the deterministic onset `j₁`);
* the refresh step: `coord_dist_le_L0`, `nuisDist_le_L0` (`d ≤ L₀ ρ`),
  `truncVar_eq_self` (eventual inactivity of the variance truncation),
  `refresh_score_error`, `refresh_design_value`;
* the batch-evidence step: `baseline_domination`, `batch_log_factor_ge`,
  `good_window_stops` (the deterministic half of `eq:v34-tail-stop`);
* the tail step: `prefix_concentration_tail` (union over intrinsic tape prefixes with the
  explicit Gaussian tail), `tail_union_bound`;
* finite confidence and the leading coefficient: `exists_first_crossing`,
  `expected_stopping_le`, `sharp_rate_of_tail`, `sharp_rate_schedule`
  (`eq:v34-finite-envelope`, `eq:v34-discovery-constant`, `eq:v34-sharp-rate`).

Not proved here: the summability `eq:v34-tail-summability` of the explicit tail, the clock
inversion `min {j : N_j ≥ t} = O((1 + log (1 + t))²)`, and the pathwise inclusion of the
event `{τ_δ > N_j}` in the union of bad concentration events for a formal model of the
tracker (its batch-evidence half is `good_window_stops`, its stabilization half is
`sticky_stabilization` with `refresh_score_error`).
-/
import JointRootCert.Assembly
import JointRootCert.ChiSquare

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ### The denominator-free batch schedule -/

section Schedule

/-- The clock `M_j = max {j, 2^⌊√j⌋}`. -/
def clockM (j : ℕ) : ℕ := max j (2 ^ Nat.sqrt j)

/-- The uniform baseline `b_j = 2 + ⌈√M_j⌉`. -/
def baseB (j : ℕ) : ℕ := 2 + ⌈Real.sqrt (clockM j)⌉₊

/-- The batch size `R_j = M_j + m b_j` for `m` query types. -/
def batchR (m j : ℕ) : ℕ := clockM j + m * baseB j

/-- The cumulative sample size `N_j = ∑_{i ≤ j} R_i`. -/
def cumN (m j : ℕ) : ℕ := ∑ i ∈ Icc 1 j, batchR m i

/-- The last four-power refresh index before the recent window,
`H_j = 4^⌊log₄ ⌊j/4⌋⌋`. -/
def refH (j : ℕ) : ℕ := 4 ^ Nat.log 4 (j / 4)

lemma le_clockM (j : ℕ) : j ≤ clockM j := le_max_left _ _

lemma pow_sqrt_le_clockM (j : ℕ) : 2 ^ Nat.sqrt j ≤ clockM j := le_max_right _ _

lemma one_le_clockM (j : ℕ) : 1 ≤ clockM j :=
  (Nat.one_le_two_pow).trans (pow_sqrt_le_clockM j)

lemma clockM_le (j : ℕ) : clockM j ≤ j + 2 ^ Nat.sqrt j :=
  max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

lemma clockM_mono : Monotone clockM := fun _ _ hab =>
  max_le_max hab (Nat.pow_le_pow_right (by norm_num) (Nat.sqrt_le_sqrt hab))

lemma baseB_mono : Monotone baseB := fun a b hab => by
  unfold baseB
  have : Real.sqrt (clockM a) ≤ Real.sqrt (clockM b) :=
    Real.sqrt_le_sqrt (by exact_mod_cast clockM_mono hab)
  have := Nat.ceil_le_ceil this
  omega

lemma batchR_mono (m : ℕ) : Monotone (batchR m) := fun _ _ hab =>
  Nat.add_le_add (clockM_mono hab) (Nat.mul_le_mul_left m (baseB_mono hab))

lemma clockM_le_batchR (m j : ℕ) : clockM j ≤ batchR m j := Nat.le_add_right _ _

lemma le_batchR (m j : ℕ) : j ≤ batchR m j := (le_clockM j).trans (clockM_le_batchR m j)

lemma baseB_le (j : ℕ) : baseB j ≤ 3 * clockM j := by
  unfold baseB
  have h1 := one_le_clockM j
  have h2 : ⌈Real.sqrt (clockM j)⌉₊ ≤ clockM j := by
    rw [Nat.ceil_le]
    have hM : (1 : ℝ) ≤ clockM j := by exact_mod_cast h1
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  omega

lemma batchR_le (m j : ℕ) : batchR m j ≤ (1 + 3 * m) * clockM j := by
  unfold batchR
  have := Nat.mul_le_mul_left m (baseB_le j)
  nlinarith

lemma cumN_succ (m j : ℕ) : cumN m (j + 1) = cumN m j + batchR m (j + 1) := by
  unfold cumN
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma cumN_mono (m : ℕ) : Monotone (cumN m) := fun _ _ hab =>
  Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hab)

/-- `N_j ≥ j (j + 1) / 2`. -/
lemma two_mul_cumN_ge (m j : ℕ) : j * (j + 1) ≤ 2 * cumN m j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [cumN_succ]
    have := le_batchR m (j + 1)
    nlinarith

lemma batchR_le_cumN (m : ℕ) {j : ℕ} (hj : 1 ≤ j) : batchR m j ≤ cumN m j := by
  unfold cumN
  exact Finset.single_le_sum (f := fun i => batchR m i) (fun i _ => Nat.zero_le _)
    (Finset.mem_Icc.mpr ⟨hj, le_rfl⟩)

/-- `N_j ≤ j R_j`. -/
lemma cumN_le (m j : ℕ) : cumN m j ≤ j * batchR m j := by
  unfold cumN
  calc ∑ i ∈ Icc 1 j, batchR m i ≤ ∑ _i ∈ Icc 1 j, batchR m j :=
        Finset.sum_le_sum fun i hi => batchR_mono m (Finset.mem_Icc.mp hi).2
    _ = j * batchR m j := by simp

/-- `N_j ≥ k 2^{k-1}` with `k = ⌊√(j+1)⌋`: at least `k` of the batches `i ≤ j` have
`⌊√i⌋ ≥ k - 1`. -/
lemma cumN_ge_pow (m : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    Nat.sqrt (j + 1) * 2 ^ (Nat.sqrt (j + 1) - 1) ≤ cumN m j := by
  set k := Nat.sqrt (j + 1) with hk
  have hk1 : 1 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hkk : k * k ≤ j + 1 := Nat.sqrt_le _
  have hkj : k ≤ j := by
    have : Nat.sqrt (j + 1) < j + 1 := Nat.sqrt_lt_self (by omega)
    omega
  set lo := max 1 ((k - 1) * (k - 1)) with hlo
  have hlo_le : lo + k ≤ j + 1 := by
    rcases le_total 1 ((k - 1) * (k - 1)) with h | h
    · rw [hlo, max_eq_right h]
      have key : ∀ n : ℕ, 1 ≤ n → (n - 1) * (n - 1) + n ≤ n * n := by
        intro n hn
        obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        nlinarith
      exact (key k hk1).trans hkk
    · rw [hlo, max_eq_left h]
      omega
  have hsub : Icc lo j ⊆ Icc 1 j := Finset.Icc_subset_Icc_left (le_max_left _ _)
  have hterm : ∀ i ∈ Icc lo j, 2 ^ (k - 1) ≤ batchR m i := by
    intro i hi
    have hi1 : (k - 1) * (k - 1) ≤ i := (le_max_right _ _).trans (Finset.mem_Icc.mp hi).1
    have : k - 1 ≤ Nat.sqrt i := Nat.le_sqrt.mpr hi1
    exact (Nat.pow_le_pow_right (by norm_num) this).trans
      ((pow_sqrt_le_clockM i).trans (clockM_le_batchR m i))
  have hcard : k ≤ (Icc lo j).card := by
    rw [Nat.card_Icc]
    omega
  calc k * 2 ^ (k - 1) ≤ (Icc lo j).card * 2 ^ (k - 1) := Nat.mul_le_mul_right _ hcard
    _ = ∑ _i ∈ Icc lo j, 2 ^ (k - 1) := by simp
    _ ≤ ∑ i ∈ Icc lo j, batchR m i := Finset.sum_le_sum hterm
    _ ≤ cumN m j := Finset.sum_le_sum_of_subset hsub

lemma tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun _ hj => Nat.le_sqrt.mpr hj⟩

/-- `R_j → ∞`. -/
theorem tendsto_batchR_atTop (m : ℕ) : Tendsto (fun j => (batchR m j : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun j => by exact_mod_cast le_batchR m j) tendsto_natCast_atTop_atTop

/-- `N_j → ∞`. -/
theorem tendsto_cumN_atTop (m : ℕ) : Tendsto (fun j => (cumN m j : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_batchR_atTop m)
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact_mod_cast batchR_le_cumN m hj

/-- **The baseline fraction vanishes: `m b_j / R_j → 0`
(`eq:v34-domination-repaired`).** -/
theorem tendsto_baseline_fraction (m : ℕ) :
    Tendsto (fun j => ((m : ℝ) * baseB j) / batchR m j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j : ℕ => (4 * (m : ℝ)) / Real.sqrt j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hM1 : (1 : ℝ) ≤ clockM j := by exact_mod_cast one_le_clockM j
  have hMj : (j : ℝ) ≤ clockM j := by exact_mod_cast le_clockM j
  set sM := Real.sqrt (clockM j) with hsM
  have hsM1 : 1 ≤ sM := by
    rw [hsM]
    exact Real.le_sqrt_of_sq_le (by rw [one_pow]; exact hM1)
  have hsMsq : sM * sM = clockM j := Real.mul_self_sqrt (by linarith)
  have hb : (baseB j : ℝ) ≤ 4 * sM := by
    have h1 : (⌈sM⌉₊ : ℝ) < sM + 1 := Nat.ceil_lt_add_one (by linarith)
    have : (baseB j : ℝ) = 2 + (⌈sM⌉₊ : ℝ) := by
      simp only [baseB, hsM]
      push_cast
      ring
    rw [this]
    linarith
  have hR : (clockM j : ℝ) ≤ batchR m j := by exact_mod_cast clockM_le_batchR m j
  have hsj : Real.sqrt j ≤ sM := Real.sqrt_le_sqrt hMj
  have hsj0 : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
  calc ((m : ℝ) * baseB j) / batchR m j ≤ ((m : ℝ) * (4 * sM)) / (sM * sM) := by
        rw [hsMsq]
        exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
          (by linarith) hR
    _ = (4 * (m : ℝ)) / sM := by
        field_simp
    _ ≤ (4 * (m : ℝ)) / Real.sqrt j := div_le_div_of_nonneg_left (by positivity) hsj0 hsj

/-- **`j / N_j → 0`.** -/
theorem tendsto_index_div_cumN (m : ℕ) :
    Tendsto (fun j : ℕ => (j : ℝ) / cumN m j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j : ℕ => (2 : ℝ) / j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have h := two_mul_cumN_ge m j
  have h' : (j : ℝ) * (j + 1) ≤ 2 * cumN m j := by exact_mod_cast h
  have hN : (0 : ℝ) < cumN m j := by nlinarith
  rw [div_le_div_iff₀ hN hj0]
  nlinarith

/-- **`R_{j+1} / N_j → 0`.** -/
theorem tendsto_batchR_div_cumN (m : ℕ) :
    Tendsto (fun j : ℕ => (batchR m (j + 1) : ℝ) / cumN m j) atTop (𝓝 0) := by
  have hsq : Tendsto (fun j : ℕ => ((Nat.sqrt (j + 1) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_natSqrt_atTop.comp (tendsto_add_atTop_nat 1))
  have hlim : Tendsto (fun j : ℕ => (1 + 3 * (m : ℝ)) * (4 / j + 2 / (Nat.sqrt (j + 1) : ℕ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => (4 : ℝ) / j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun j : ℕ => (2 : ℝ) / (Nat.sqrt (j + 1) : ℕ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsq
    simpa using (h1.add h2).const_mul (1 + 3 * (m : ℝ))
  refine squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with j hj
  set k := Nat.sqrt (j + 1) with hk
  have hk1 : 1 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hN1 : (j : ℝ) * (j + 1) ≤ 2 * cumN m j := by exact_mod_cast two_mul_cumN_ge m j
  have hN2 : (k : ℝ) * 2 ^ (k - 1) ≤ cumN m j := by exact_mod_cast cumN_ge_pow m hj
  have hN : (0 : ℝ) < cumN m j := by nlinarith
  have hpow : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    obtain ⟨c, hc⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    rw [hc, Nat.add_sub_cancel, pow_succ]
    ring
  have hR : (batchR m (j + 1) : ℝ) ≤ (1 + 3 * (m : ℝ)) * ((j + 1 : ℝ) + 2 ^ k) := by
    have h1 := (batchR_le m (j + 1)).trans (Nat.mul_le_mul_left _ (clockM_le (j + 1)))
    have h2 : (batchR m (j + 1) : ℝ) ≤ ((1 + 3 * m : ℕ) : ℝ) * ((j + 1 + 2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast h1
    simpa using h2
  have ha : ((j : ℝ) + 1) / cumN m j ≤ 4 / j := by
    rw [div_le_div_iff₀ hN hj0]
    nlinarith
  have hb : (2 : ℝ) ^ k / cumN m j ≤ 2 / k := by
    rw [div_le_div_iff₀ hN hk0, hpow]
    have hp : (0 : ℝ) < 2 ^ (k - 1) := by positivity
    nlinarith
  calc (batchR m (j + 1) : ℝ) / cumN m j
      ≤ (1 + 3 * (m : ℝ)) * ((j + 1 : ℝ) + 2 ^ k) / cumN m j :=
        div_le_div_of_nonneg_right hR hN.le
    _ = (1 + 3 * (m : ℝ)) * (((j : ℝ) + 1) / cumN m j + 2 ^ k / cumN m j) := by ring
    _ ≤ (1 + 3 * (m : ℝ)) * (4 / j + 2 / k) :=
        mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)

/-- **`j / 16 < H_j ≤ j / 4` for `j ≥ 16`.** -/
theorem refH_bounds {j : ℕ} (hj : 16 ≤ j) : j < 16 * refH j ∧ 4 * refH j ≤ j := by
  unfold refH
  have hn : j / 4 ≠ 0 := by omega
  have h1 := Nat.pow_log_le_self 4 hn
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) (j / 4)
  rw [Nat.pow_succ] at h2
  omega

lemma refH_pos (j : ℕ) : 1 ≤ refH j := Nat.one_le_pow _ _ (by norm_num)

/-- `H_j` is a four-power refresh index. -/
lemma refH_fourPower (j : ℕ) : ∃ k : ℕ, refH j = 4 ^ k := ⟨_, rfl⟩


/-- `⌊√⌊j/4⌋⌋ ≤ ⌊√j⌋ / 2`. -/
lemma sqrt_div_four_le (j : ℕ) : Nat.sqrt (j / 4) ≤ Nat.sqrt j / 2 := by
  have h := Nat.sqrt_le (j / 4)
  have h2 : 2 * Nat.sqrt (j / 4) ≤ Nat.sqrt j :=
    Nat.le_sqrt.mpr (by nlinarith [Nat.div_mul_le_self j 4])
  omega

/-- **`N_{H_j - 1} / N_j → 0`.** -/
theorem tendsto_cumN_refH_div (m : ℕ) :
    Tendsto (fun j : ℕ => (cumN m (refH j - 1) : ℝ) / cumN m j) atTop (𝓝 0) := by
  have hf4 : Tendsto (fun n : ℕ => (n : ℝ) ^ 4 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num)
  have hf2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hk1 : Tendsto (fun j : ℕ => Nat.sqrt j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_succ _) tendsto_natSqrt_atTop
  have hhalf : Tendsto (fun k : ℕ => k / 2 + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun k hk => by omega⟩
  have hk2 : Tendsto (fun j : ℕ => Nat.sqrt j / 2 + 1) atTop atTop :=
    hhalf.comp tendsto_natSqrt_atTop
  have hlim : Tendsto (fun j : ℕ => (1 + 3 * (m : ℝ)) *
      (2 * (((Nat.sqrt j + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (Nat.sqrt j + 1)) +
        8 * (((Nat.sqrt j / 2 + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (Nat.sqrt j / 2 + 1)))) atTop (𝓝 0) := by
    have a := (hf4.comp hk1).const_mul 2
    have b := (hf2.comp hk2).const_mul 8
    simpa using (a.add b).const_mul (1 + 3 * (m : ℝ))
  refine squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 16] with j hj
  set k := Nat.sqrt j with hk
  set n := j / 4 with hn
  set h := k / 2 with hh
  have hH : refH j - 1 ≤ n := by
    have := (refH_bounds hj).2
    omega
  have h1 : cumN m (refH j - 1) ≤ n * ((1 + 3 * m) * (n + 2 ^ h)) :=
    ((cumN_mono m hH).trans (cumN_le m n)).trans (Nat.mul_le_mul_left _
      ((batchR_le m n).trans (Nat.mul_le_mul_left _ ((clockM_le n).trans
        (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (sqrt_div_four_le j)) _)))))
  have h2 : 2 ^ k ≤ cumN m j :=
    (pow_sqrt_le_clockM j).trans ((clockM_le_batchR m j).trans (batchR_le_cumN m (by omega)))
  have h3 : j < (k + 1) * (k + 1) := Nat.lt_succ_sqrt j
  have h4 : 2 ^ h * 2 ^ h ≤ 2 ^ k := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkh : k + 1 ≤ 2 * (h + 1) := by omega
  -- real-valued versions
  set a : ℝ := (k : ℝ) + 1 with ha
  set Pk : ℝ := (2 : ℝ) ^ k with hPk
  set Q : ℝ := (2 : ℝ) ^ h with hQ
  have ha0 : 0 < a := by positivity
  have hP0 : 0 < Pk := by positivity
  have hQ0 : 0 < Q := by positivity
  have hnj : (n : ℝ) ≤ a ^ 2 := by
    have h5 : n ≤ (k + 1) * (k + 1) := (Nat.div_le_self j 4).trans h3.le
    have h6 : (n : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) := by exact_mod_cast h5
    rw [ha]
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnum : (cumN m (refH j - 1) : ℝ) ≤ (1 + 3 * (m : ℝ)) * (a ^ 4 + a ^ 2 * Q) := by
    have h5 : (cumN m (refH j - 1) : ℝ) ≤ (n : ℝ) * ((1 + 3 * (m : ℝ)) * ((n : ℝ) + Q)) := by
      have : (cumN m (refH j - 1) : ℝ) ≤ ((n * ((1 + 3 * m) * (n + 2 ^ h)) : ℕ) : ℝ) := by
        exact_mod_cast h1
      simpa [hQ] using this
    have h6 : (n : ℝ) * ((n : ℝ) + Q) ≤ a ^ 2 * (a ^ 2 + Q) :=
      mul_le_mul hnj (by linarith) (by positivity) (by positivity)
    have hm0 : (0 : ℝ) ≤ 1 + 3 * (m : ℝ) := by positivity
    calc (cumN m (refH j - 1) : ℝ) ≤ (1 + 3 * (m : ℝ)) * ((n : ℝ) * ((n : ℝ) + Q)) := by
          linarith
      _ ≤ (1 + 3 * (m : ℝ)) * (a ^ 2 * (a ^ 2 + Q)) := mul_le_mul_of_nonneg_left h6 hm0
      _ = (1 + 3 * (m : ℝ)) * (a ^ 4 + a ^ 2 * Q) := by ring
  have hden : Pk ≤ cumN m j := by
    have : ((2 ^ k : ℕ) : ℝ) ≤ cumN m j := by exact_mod_cast h2
    simpa [hPk] using this
  have hQP : Q * Q ≤ Pk := by
    have : ((2 ^ h * 2 ^ h : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h4
    simpa [hQ, hPk] using this
  have hah : a ≤ 2 * ((h : ℝ) + 1) := by
    have : ((k + 1 : ℕ) : ℝ) ≤ ((2 * (h + 1) : ℕ) : ℝ) := by exact_mod_cast hkh
    simpa [ha] using this
  have hN0 : (0 : ℝ) < cumN m j := lt_of_lt_of_le hP0 hden
  have hterm1 : a ^ 4 / Pk = 2 * (((k + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (k + 1)) := by
    push_cast
    rw [pow_succ (2 : ℝ) k, ← hPk]
    field_simp
    rw [ha]
  have hterm2 : a ^ 2 * Q / Pk ≤ 8 * (((h + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (h + 1)) := by
    push_cast
    rw [pow_succ (2 : ℝ) h, ← hQ]
    have e : 8 * (((h : ℝ) + 1) ^ 2 / (Q * 2)) = (2 * ((h : ℝ) + 1)) ^ 2 / Q := by
      field_simp
      ring
    rw [e]
    have h7 : a ^ 2 * Q / Pk ≤ a ^ 2 * Q / (Q * Q) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hQP
    have h8 : a ^ 2 * Q / (Q * Q) = a ^ 2 / Q := by
      field_simp
    rw [h8] at h7
    refine h7.trans (div_le_div_of_nonneg_right ?_ hQ0.le)
    exact pow_le_pow_left₀ ha0.le hah 2
  calc (cumN m (refH j - 1) : ℝ) / cumN m j
      ≤ (1 + 3 * (m : ℝ)) * (a ^ 4 + a ^ 2 * Q) / Pk :=
        div_le_div₀ (by positivity) hnum hP0 hden
    _ = (1 + 3 * (m : ℝ)) * (a ^ 4 / Pk + a ^ 2 * Q / Pk) := by ring
    _ ≤ (1 + 3 * (m : ℝ)) * (2 * (((k + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (k + 1)) +
          8 * (((h + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (h + 1))) := by
        rw [← hterm1]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm2) (by positivity)


/-- The cumulative baseline `𝔟_j = ∑_{i ≤ j} b_i`: every query type has at least `𝔟_j`
observations by the end of batch `j`. -/
def cumB (j : ℕ) : ℕ := ∑ i ∈ Icc 1 j, baseB i

lemma two_le_baseB (j : ℕ) : 2 ≤ baseB j := Nat.le_add_right _ _

lemma le_cumB (j : ℕ) : j ≤ cumB j := by
  unfold cumB
  calc j = ∑ _i ∈ Icc 1 j, 1 := by simp
    _ ≤ ∑ i ∈ Icc 1 j, baseB i := Finset.sum_le_sum fun i _ => by
        have := two_le_baseB i
        omega

/-- `b_i² ≥ M_i ≥ i`. -/
lemma le_baseB_sq (j : ℕ) : j ≤ baseB j * baseB j := by
  have hM0 : (0 : ℝ) ≤ clockM j := Nat.cast_nonneg _
  have h1 : Real.sqrt (clockM j) ≤ (baseB j : ℝ) := by
    have := Nat.le_ceil (Real.sqrt (clockM j))
    have e : (baseB j : ℝ) = 2 + (⌈Real.sqrt (clockM j)⌉₊ : ℝ) := by
      simp only [baseB]
      push_cast
      ring
    rw [e]
    linarith
  have h2 : (clockM j : ℝ) ≤ (baseB j : ℝ) * baseB j := by
    calc (clockM j : ℝ) = Real.sqrt (clockM j) * Real.sqrt (clockM j) :=
          (Real.mul_self_sqrt hM0).symm
      _ ≤ (baseB j : ℝ) * baseB j :=
          mul_le_mul h1 h1 (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have h3 : clockM j ≤ baseB j * baseB j := by exact_mod_cast h2
  exact (le_clockM j).trans h3

lemma le_baseB_of_sq_le {L i : ℕ} (h : L * L ≤ i) : L ≤ baseB i := by
  by_contra hlt
  have hlt' : baseB i < L := not_le.mp hlt
  have := le_baseB_sq i
  nlinarith

/-- **Existence of the deterministic onset `j₁`.**  For every `η, C > 0` and every threshold
`L` (standing for `4^{k₀}`, `max_x n₀(x, ρ)` and `2 + 2 max {max_x v_x, v_min⁻¹}`), there is
`j₁ ≥ 16` such that for all `j ≥ j₁`: `H_j ≥ L`, `𝔟_{H_j - 1} ≥ L`,
`N_{H_j - 1} / N_j ≤ η / (4 C)`, `j log 2 / N_j ≤ η / 4`, and for every `i ≥ H_j`:
`i ≥ L`, `b_i ≥ L`, `m b_i / R_i ≤ η / (8 C)`, `R_i ≥ 4 (2 + log 2) / η`.  These are the
explicit deterministic inequalities listed in the proof of Theorem `thm:v34-adaptive`. -/
theorem exists_schedule_onset (m : ℕ) {C η : ℝ} (hC : 0 < C) (hη : 0 < η) (L : ℕ) :
    ∃ j1 : ℕ, 16 ≤ j1 ∧ ∀ j, j1 ≤ j →
      L ≤ refH j ∧ L ≤ cumB (refH j - 1) ∧
      (cumN m (refH j - 1) : ℝ) ≤ η / (4 * C) * cumN m j ∧
      (j : ℝ) * Real.log 2 ≤ η / 4 * cumN m j ∧
      ∀ i, refH j ≤ i → L ≤ i ∧ L ≤ baseB i ∧
        (m : ℝ) * baseB i ≤ η / (8 * C) * batchR m i ∧
        4 * (2 + Real.log 2) / η ≤ batchR m i := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have E1 := (tendsto_cumN_refH_div m).eventually
    (gt_mem_nhds (show (0 : ℝ) < η / (4 * C) by positivity))
  have E2 := (tendsto_index_div_cumN m).eventually
    (gt_mem_nhds (show (0 : ℝ) < η / (4 * Real.log 2) by positivity))
  have E3 := (tendsto_baseline_fraction m).eventually
    (gt_mem_nhds (show (0 : ℝ) < η / (8 * C) by positivity))
  have E4 := (tendsto_batchR_atTop m).eventually_ge_atTop (4 * (2 + Real.log 2) / η)
  obtain ⟨ja, hja⟩ := eventually_atTop.mp (E1.and E2)
  obtain ⟨ia, hia⟩ := eventually_atTop.mp (E3.and E4)
  refine ⟨max (max ja 16) (16 * (ia + L * L + L + 2)), (le_max_right _ _).trans (le_max_left _ _),
    fun j hj => ?_⟩
  have hj16 : 16 ≤ j := ((le_max_right _ _).trans (le_max_left _ _)).trans hj
  have hjja : ja ≤ j := ((le_max_left _ _).trans (le_max_left _ _)).trans hj
  have hjbig : 16 * (ia + L * L + L + 2) ≤ j := (le_max_right _ _).trans hj
  have hH := (refH_bounds hj16).1
  have hHbig : ia + L * L + L + 2 ≤ refH j := by omega
  have hNpos : (0 : ℝ) < cumN m j := by
    have h := two_mul_cumN_ge m j
    have h' : (j : ℝ) * (j + 1) ≤ 2 * cumN m j := by exact_mod_cast h
    have : (16 : ℝ) ≤ j := by exact_mod_cast hj16
    nlinarith
  obtain ⟨e1, e2⟩ := hja j hjja
  refine ⟨by omega, (by omega : L ≤ refH j - 1).trans (le_cumB _), ?_, ?_, fun i hi => ?_⟩
  · have := (div_lt_iff₀ hNpos).mp e1
    linarith
  · have h := (div_lt_iff₀ hNpos).mp e2
    have e : η / (4 * Real.log 2) * cumN m j * Real.log 2 = η / 4 * cumN m j := by
      field_simp
    have := mul_le_mul_of_nonneg_right h.le hlog2.le
    linarith
  · obtain ⟨e3, e4⟩ := hia i (by omega)
    have hLL : L * L ≤ i := by omega
    have hRpos : (0 : ℝ) < batchR m i := by
      have : (0 : ℝ) < 4 * (2 + Real.log 2) / η := by positivity
      linarith
    refine ⟨by omega, le_baseB_of_sq_le hLL, ?_, e4⟩
    have := (div_lt_iff₀ hRpos).mp e3
    linarith

end Schedule

/-! ### The refresh step: `d ≤ L₀ ρ`, truncation, displayed scores -/

/-- **One coordinate of `d(μ̂, v̂; μ, v) ≤ L₀ ρ`.**  If the estimates are within
`ρ ≤ v_min / 8` of a true mean and a true variance `v ≥ v_min`, the coordinate term of the
perturbation size of Lemma `lem:v34-transport` is at most `L₀ ρ`. -/
theorem coord_dist_le_L0 {vmin v m mh vh ρ : ℝ} (hvmin : 0 < vmin) (hv : vmin ≤ v)
    (hρ0 : 0 ≤ ρ) (hρv : ρ ≤ vmin / 8) (hm : |mh - m| ≤ ρ) (hvh : |vh - v| ≤ ρ) :
    |mh - m| / (2 * Real.sqrt (min vh v)) + 1 / 2 * |Real.log (vh / v)| ≤ L0 vmin * ρ := by
  have hv0 : 0 < v := hvmin.trans_le hv
  obtain ⟨hlo, -⟩ := abs_le.mp hvh
  have hvh0 : vmin / 2 ≤ vh := by linarith
  have hmin : vmin / 2 ≤ min vh v := le_min hvh0 (by linarith)
  have hsv : 0 < Real.sqrt vmin := Real.sqrt_pos.mpr hvmin
  have hsq : Real.sqrt vmin / 2 ≤ Real.sqrt (min vh v) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hvmin.le]
    linarith
  have h1 : |mh - m| / (2 * Real.sqrt (min vh v)) ≤ ρ * (Real.sqrt vmin)⁻¹ := by
    have : |mh - m| / (2 * Real.sqrt (min vh v)) ≤ ρ / (2 * (Real.sqrt vmin / 2)) :=
      div_le_div₀ hρ0 hm (by positivity) (by linarith)
    refine this.trans (le_of_eq ?_)
    field_simp
  have h2 : |Real.log (vh / v)| ≤ ρ / (vmin / 2) := by
    rw [Real.log_div (by linarith) hv0.ne']
    exact (abs_log_sub_log_le (by positivity) hvh0 (by linarith)).trans
      (div_le_div_of_nonneg_right hvh (by positivity))
  have h2' : 1 / 2 * |Real.log (vh / v)| ≤ ρ * vmin⁻¹ := by
    have e : ρ / (vmin / 2) = 2 * (ρ * vmin⁻¹) := by field_simp
    rw [e] at h2
    linarith
  have p1 : 0 ≤ ρ * (Real.sqrt vmin)⁻¹ := by positivity
  have p2 : 0 ≤ ρ * vmin⁻¹ := by positivity
  have hR : L0 vmin * ρ = 40 * ρ + 40 * (ρ * vmin⁻¹) + 40 * (ρ * (Real.sqrt vmin)⁻¹) := by
    unfold L0; ring
  rw [hR]
  linarith

/-- **`d(μ̂, v̂; μ, v) ≤ L₀ ρ`** when all prefix means and variances are within
`ρ ≤ v_min / 8` of the truth (the step used at a good refresh in the proof of
Theorem `thm:v34-adaptive`). -/
theorem nuisDist_le_L0 {X : Type*} [Fintype X] [Nonempty X] {μh vh μ v : X → ℝ} {vmin ρ : ℝ}
    (hvmin : 0 < vmin) (hv : ∀ x, vmin ≤ v x) (hρ0 : 0 ≤ ρ) (hρv : ρ ≤ vmin / 8)
    (hm : ∀ x, |μh x - μ x| ≤ ρ) (hvh : ∀ x, |vh x - v x| ≤ ρ) :
    nuisDist μh vh μ v ≤ L0 vmin * ρ :=
  Finset.sup'_le _ _ fun x _ => coord_dist_le_L0 hvmin (hv x) hρ0 hρv (hm x) (hvh x)

/-- The truncated historical variance estimate `min {j, max {j⁻¹, s²}}` of
`eq:v34-predictor-estimates`. -/
def truncVar (j s2 : ℝ) : ℝ := min j (max j⁻¹ s2)

/-- **Eventual inactivity of the variance truncation.**  If the centered variance is within
`ρ ≤ v_min / 8` of a true variance `v ∈ [v_min, v_max]` and
`j ≥ 2 + 2 max {v_max, v_min⁻¹}`, the truncation does nothing. -/
theorem truncVar_eq_self {vmin vmax v s2 ρ j : ℝ} (hvmin : 0 < vmin) (hv : vmin ≤ v)
    (hvmax : v ≤ vmax) (hρv : ρ ≤ vmin / 8) (hs : |s2 - v| ≤ ρ)
    (hj : 2 + 2 * max vmax vmin⁻¹ ≤ j) : truncVar j s2 = s2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hs
  have h1 : vmax ≤ max vmax vmin⁻¹ := le_max_left _ _
  have h2 : vmin⁻¹ ≤ max vmax vmin⁻¹ := le_max_right _ _
  have hj0 : 0 < j := by
    have : 0 < vmin⁻¹ := inv_pos.mpr hvmin
    linarith
  have hupper : s2 ≤ j := by linarith
  have hlower : j⁻¹ ≤ s2 := by
    have hjv : 2 * vmin⁻¹ ≤ j := by linarith
    have h3 : j⁻¹ ≤ vmin / 2 := by
      rw [inv_le_comm₀ hj0 (by positivity)]
      refine le_trans (le_of_eq ?_) hjv
      field_simp
    linarith
  unfold truncVar
  rw [max_eq_right hlower, min_eq_right hupper]

section Refresh

variable {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X] {U Z : Type*}

/-- **Displayed-score accuracy at a good refresh.**  If all prefix means and variances are
within `ρ ≤ v_min / 8` of the truth (the truncation being inactive), the design contract
`eq:v34-design-contract` gives `|Ĉ_a - C_a^*| ≤ L₀ ρ + e`. -/
theorem refresh_score_error (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {μh vh μ v : X → ℝ} {vmin ρ Chat e : ℝ} (hvmin : 0 < vmin)
    (hv : ∀ x, vmin ≤ v x) (hρ0 : 0 ≤ ρ) (hρv : ρ ≤ vmin / 8)
    (hm : ∀ x, |μh x - μ x| ≤ ρ) (hvh : ∀ x, |vh x - v x| ≤ ρ)
    (h1 : Chat ≤ actGameStar J hJ H pred μh vh)
    (h2 : actGameStar J hJ H pred μh vh ≤ Chat + e) :
    |Chat - actGameStar J hJ H pred μ v| ≤ L0 vmin * ρ + e := by
  have hv0 : ∀ x, 0 < v x := fun x => hvmin.trans_le (hv x)
  have hvh0 : ∀ x, 0 < vh x := fun x => by
    have := (abs_le.mp (hvh x)).1
    have := hv x
    linarith
  exact score_error_of_contract J hJ H pred hvh0 hv0
    (fun x => coord_dist_le_L0 hvmin (hv x) hρ0 hρv (hm x) (hvh x)) h1 h2

/-- **Value of the retained design at a good refresh:**
`C_a(w; μ, v) ≥ C_a^* - 2 L₀ ρ - e`. -/
theorem refresh_design_value (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {w μh vh μ v : X → ℝ} {vmin ρ Chat e : ℝ} (hw : w ∈ simplex X)
    (hvmin : 0 < vmin) (hv : ∀ x, vmin ≤ v x) (hρ0 : 0 ≤ ρ) (hρv : ρ ≤ vmin / 8)
    (hm : ∀ x, |μh x - μ x| ≤ ρ) (hvh : ∀ x, |vh x - v x| ≤ ρ)
    (h1 : Chat ≤ actGame J hJ H pred w μh vh)
    (h2 : actGameStar J hJ H pred μh vh ≤ Chat + e) :
    actGameStar J hJ H pred μ v - 2 * (L0 vmin * ρ) - e ≤ actGame J hJ H pred w μ v := by
  have hv0 : ∀ x, 0 < v x := fun x => hvmin.trans_le (hv x)
  have hvh0 : ∀ x, 0 < vh x := fun x => by
    have := (abs_le.mp (hvh x)).1
    have := hv x
    linarith
  exact retained_design_value J hJ H pred hw hvh0 hv0
    (fun x => coord_dist_le_L0 hvmin (hv x) hρ0 hρv (hm x) (hvh x)) h1 h2

end Refresh

/-! ### The batch-evidence step -/

section Evidence

variable {X : Type*} [Fintype X] {U Z : Type*}

/-- **Baseline domination with a small baseline fraction.**  If the deployed frequencies
dominate `c w` with `c = M_j / R_j ≥ 1 - η / (8 C)` (that is, `m b_j / R_j ≤ η / (8 C)`) and
the nominal design has `C_a(w; μ, v) ≥ C - η / 8`, then `C_a(w̃; μ, v) ≥ C - η / 4`. -/
theorem baseline_domination (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {w wt μ v : X → ℝ} {c C η : ℝ} (hC : 0 < C)
    (hηC : η ≤ 8 * C) (hc1 : 1 - η / (8 * C) ≤ c) (hw : ∀ x, 0 ≤ w x)
    (hdom : ∀ x, c * w x ≤ wt x) (hv : ∀ x, 0 < v x)
    (hval : C - η / 8 ≤ actGame J hJ H pred w μ v) :
    C - η / 4 ≤ actGame J hJ H pred wt μ v := by
  have hc0 : 0 ≤ 1 - η / (8 * C) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hηC
  have hc : 0 ≤ c := hc0.trans hc1
  refine le_trans ?_ (actGame_domination J hJ H pred hc hw hdom hv)
  have hg0 : 0 ≤ actGame J hJ H pred w μ v := actGame_nonneg hw hv
  have h1 : (1 - η / (8 * C)) * actGame J hJ H pred w μ v ≤
      c * actGame J hJ H pred w μ v := mul_le_mul_of_nonneg_right hc1 hg0
  have h2 : (1 - η / (8 * C)) * (C - η / 8) ≤
      (1 - η / (8 * C)) * actGame J hJ H pred w μ v := mul_le_mul_of_nonneg_left hval hc0
  have e : (1 - η / (8 * C)) * (C - η / 8) = C - η / 4 + η ^ 2 / (64 * C) := by
    field_simp
    ring
  have h3 : 0 ≤ η ^ 2 / (64 * C) := by positivity
  linarith

/-- **Evidence of one good batch.**  For a component null `H` with
`C_{a,z}(w̃; μ, v) ≥ C - η / 4`, batch and predictor statistics within
`ρ ≤ min {1, v_min / 8}` of the truth with `L₀ ρ ≤ η / 16`, the two-nat numerical contract
`eq:v34-numeric-contract`, and `R ≥ 4 (2 + log 2) / η`, the half-cash factor satisfies
`log F ≥ R (C - η)`.  The hypothesis `hident` is the identification
`R⁻¹ log (q / U) = profStat` (Lemma `lem:v34-batch-comparison`; proved for the Gaussian batch
density in `UnknownVarianceBatch.lean`, `batch_loglik_identification`). -/
theorem batch_log_factor_ge (H : Set U) (pred : X → U → ℝ)
    {w μ v ybar vchk muh vh : X → ℝ} {vmin ρ C η R q qlo Uenv Uhi : ℝ} (hw : w ∈ simplex X)
    (hvmin : 0 < vmin) (hv : ∀ x, vmin ≤ v x) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρv : ρ ≤ vmin / 8) (hρη : L0 vmin * ρ ≤ η / 16) (hη : 0 < η)
    (h1 : ∀ x, |ybar x - μ x| ≤ ρ) (h2 : ∀ x, |vchk x - v x| ≤ ρ)
    (h3 : ∀ x, |muh x - μ x| ≤ ρ) (h4 : ∀ x, |vh x - v x| ≤ ρ)
    (hgame : C - η / 4 ≤ compGame H pred w μ v)
    (hident : R⁻¹ * Real.log (q / Uenv) = profStat H pred w ybar vchk muh vh)
    (hqlo : 0 < qlo) (hq : qlo ≤ q) (hU : 0 < Uenv) (hUhi : Uenv ≤ Uhi)
    (hcontract : Real.log (q / qlo) + Real.log (Uhi / Uenv) ≤ 2)
    (hR : 4 * (2 + Real.log 2) / η ≤ R) :
    R * (C - η) ≤ Real.log (halfCash qlo Uhi) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hcmp := abs_le.mp (batch_comparison H pred hw hvmin hv hρ0 hρ1 hρv h1 h2 h3 h4)
  rw [← hident] at hcmp
  have hratio : R * (C - η / 4 - L0 vmin * ρ) ≤ Real.log (q / Uenv) := by
    have h5 : C - η / 4 - L0 vmin * ρ ≤ R⁻¹ * Real.log (q / Uenv) := by linarith [hcmp.1]
    have h6 := mul_le_mul_of_nonneg_left h5 hR0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hR0.ne', one_mul] at h6
  exact log_factor_rate hη (log_halfCash_ge hqlo hq hU hUhi hcontract) hratio hρη hR

/-- **Batch evidence on a recent window forces stopping (deterministic half of
`eq:v34-tail-stop`).**  Fix one path.  `sel i` is the action selected at batch `i`, `a` the
stabilized optimal action, `J` its component set with nulls `H z`.  For every batch `i` in the
window `H₀ ≤ i ≤ j`:

* `a` is selected (stabilization);
* the nominal design `w i` has `C_a(w_i; μ, v) ≥ C - η / 8` (`refresh_design_value`), the
  deployed frequencies `wt i` dominate `c_i w_i` with `c_i = M_i / R_i ≥ 1 - η / (8 C)`;
* the batch statistics and predictor estimates are within `ρ` of the truth, where
  `ρ ≤ min {1, v_min / 8}` and `L₀ ρ ≤ η / 16`;
* the numerical contract holds and `R⁻¹ log (q / U) = profStat` (`hident`, see
  `batch_log_factor_ge`);
* `R_i ≥ 4 (2 + log 2) / η`.

On all batches the certified bounds are nonnegative (so every evaluated factor is at least
`½`).  The schedule satisfies `∑_{H₀ ≤ i ≤ j} R_i = N_j - N_{H₀ - 1}`,
`N_{H₀-1} ≤ η / (4 C) N_j`, `j log 2 ≤ (η / 4) N_j`, and `(C - 2 η) N_j ≥ log (K / δ)`.
Then every component wealth of `a` is at least `K / δ` at batch `j`: the stopping test of
Theorem `thm:v34-action-local` has fired by batch `j`. -/
theorem good_window_stops {A : Type*} [DecidableEq A] (J : Finset Z) (hJ : J.Nonempty)
    (H : Z → Set U) (pred : X → U → ℝ) {μ v : X → ℝ} {vmin ρ C η K δ : ℝ}
    (sel : ℕ → A) (a : A) (j H0 : ℕ) (R cdom : ℕ → ℝ) (w wt ybar vchk muh vh : ℕ → X → ℝ)
    (q qlo : ℕ → ℝ) (Uenv Uhi : Z → ℕ → ℝ) {Nj NH : ℝ}
    (hvmin : 0 < vmin) (hv : ∀ x, vmin ≤ v x) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρv : ρ ≤ vmin / 8) (hρη : L0 vmin * ρ ≤ η / 16) (hC : 0 < C) (hη : 0 < η)
    (hηC : η ≤ 8 * C) (hK : 0 < K) (hδ : 0 < δ)
    (hqlo0 : ∀ i ∈ Icc 1 j, 0 ≤ qlo i) (hUhi0 : ∀ z ∈ J, ∀ i ∈ Icc 1 j, 0 ≤ Uhi z i)
    (hsel : ∀ i ∈ Icc 1 j, H0 ≤ i → sel i = a)
    (hwt : ∀ i ∈ Icc 1 j, H0 ≤ i → wt i ∈ simplex X)
    (hw0 : ∀ i ∈ Icc 1 j, H0 ≤ i → ∀ x, 0 ≤ w i x)
    (hcdom : ∀ i ∈ Icc 1 j, H0 ≤ i → 1 - η / (8 * C) ≤ cdom i)
    (hdom : ∀ i ∈ Icc 1 j, H0 ≤ i → ∀ x, cdom i * w i x ≤ wt i x)
    (hval : ∀ i ∈ Icc 1 j, H0 ≤ i → C - η / 8 ≤ actGame J hJ H pred (w i) μ v)
    (h1 : ∀ i ∈ Icc 1 j, H0 ≤ i → ∀ x, |ybar i x - μ x| ≤ ρ)
    (h2 : ∀ i ∈ Icc 1 j, H0 ≤ i → ∀ x, |vchk i x - v x| ≤ ρ)
    (h3 : ∀ i ∈ Icc 1 j, H0 ≤ i → ∀ x, |muh i x - μ x| ≤ ρ)
    (h4 : ∀ i ∈ Icc 1 j, H0 ≤ i → ∀ x, |vh i x - v x| ≤ ρ)
    (hident : ∀ z ∈ J, ∀ i ∈ Icc 1 j, H0 ≤ i → (R i)⁻¹ * Real.log (q i / Uenv z i) =
      profStat (H z) pred (wt i) (ybar i) (vchk i) (muh i) (vh i))
    (hqlo : ∀ i ∈ Icc 1 j, H0 ≤ i → 0 < qlo i ∧ qlo i ≤ q i)
    (hU : ∀ z ∈ J, ∀ i ∈ Icc 1 j, H0 ≤ i → 0 < Uenv z i ∧ Uenv z i ≤ Uhi z i)
    (hcontract : ∀ z ∈ J, ∀ i ∈ Icc 1 j, H0 ≤ i →
      Real.log (q i / qlo i) + Real.log (Uhi z i / Uenv z i) ≤ 2)
    (hR : ∀ i ∈ Icc 1 j, H0 ≤ i → 4 * (2 + Real.log 2) / η ≤ R i)
    (hsum : ∑ i ∈ (Icc 1 j).filter (fun i => H0 ≤ i), R i = Nj - NH)
    (hNH0 : 0 ≤ NH) (hNH : NH ≤ η / (4 * C) * Nj) (hjlog : j * Real.log 2 ≤ η / 4 * Nj)
    (hstop : Real.log (K / δ) ≤ (C - 2 * η) * Nj) :
    ∀ z ∈ J, K / δ ≤ localWealth (fun i => halfCash (qlo i) (Uhi z i)) sel a j := by
  intro z hz
  have hv0 : ∀ x, 0 < v x := fun x => hvmin.trans_le (hv x)
  have hhalf : ∀ i ∈ Icc 1 j, sel i = a → 1 / 2 ≤ halfCash (qlo i) (Uhi z i) := fun i hi _ =>
    halfCash_ge_half (hqlo0 i hi) (hUhi0 z hz i hi)
  have hwin : ∀ i ∈ Icc 1 j, H0 ≤ i →
      sel i = a ∧ (C - η) * R i ≤ Real.log (halfCash (qlo i) (Uhi z i)) := by
    intro i hi hHi
    refine ⟨hsel i hi hHi, ?_⟩
    have hgame : C - η / 4 ≤ compGame (H z) pred (wt i) μ v :=
      (baseline_domination J hJ H pred hC hηC (hcdom i hi hHi) (hw0 i hi hHi)
        (hdom i hi hHi) hv0 (hval i hi hHi)).trans (Finset.inf'_le _ hz)
    have := batch_log_factor_ge (H z) pred (hwt i hi hHi) hvmin hv hρ0 hρ1 hρv hρη hη
      (h1 i hi hHi) (h2 i hi hHi) (h3 i hi hHi) (h4 i hi hHi) hgame (hident z hz i hi hHi)
      (hqlo i hi hHi).1 (hqlo i hi hHi).2 (hU z hz i hi hHi).1 (hU z hz i hi hHi).2
      (hcontract z hz i hi hHi) (hR i hi hHi)
    linarith
  have hlog := log_localWealth_ge (fun i => halfCash (qlo i) (Uhi z i)) sel a j H0 R (C - η)
    hhalf hwin
  rw [hsum] at hlog
  have hrate := wealth_rate (C := C) (η := η) (Nj := Nj) (NH := NH) hC hη.le hNH0 hNH hjlog
  have hpos : 0 < localWealth (fun i => halfCash (qlo i) (Uhi z i)) sel a j :=
    localWealth_pos fun i hi hs => lt_of_lt_of_le (by norm_num) (hhalf i hi hs)
  exact stop_of_log_ge hpos hK hδ (by linarith)

end Evidence

/-! ### The tail step: union over intrinsic tape prefixes and fresh batches -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that the length-`n` prefix of the tape `Y` has its mean or its centered
variance (denominator `n`) more than `r` away from `(μ, v)`. -/
def prefixBad (Y : ℕ → Ω → ℝ) (μ v r : ℝ) (n : ℕ) : Set Ω :=
  {ω | r < |(∑ i ∈ range n, Y i ω) / n - μ| ∨
    r < |(∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n - v|}

/-- **Union over intrinsic tape prefixes with the explicit Gaussian tail.**  For an intrinsic
tape of independent `N(μ, v)` observations and `0 < r ≤ v / 8`, the probability that some
prefix of length `n ≥ N` (in particular one of data-dependent length) is `r`-bad is at most
`∑_{n ≥ N} Q(n, r)`.  No tail hypothesis: the fixed-count bound is
`gaussian_concentration_fixed`. -/
theorem prefix_concentration_tail (P : Measure Ω) [IsProbabilityMeasure P] {v r μ : ℝ}
    (hv : 0 < v) (hr0 : 0 < r) (hrv : r ≤ v / 8) {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal μ v.toNNReal) P) (N : ℕ) :
    P {ω | ∃ n, N ≤ n ∧ ω ∈ prefixBad Y μ v r n} ≤
      ∑' n, if N ≤ n then ENNReal.ofReal (Qtail v n r) else 0 :=
  concentration_prefix P (prefixBad Y μ v r) (fun n => Qtail v n r) N
    fun n _ => gaussian_concentration_fixed hv hr0 hrv n hind hY

/-- The explicit tail `p_j` of `eq:v34-explicit-tail`, as a function of `H = H_j`:
`∑ₓ [∑_{n ≥ 𝔟_{H-1}} Qₓ(n, ρ) + ∑_{i ≥ H} Qₓ(b_i, ρ)
  + ∑_{k : 4^k ≥ H} ∑_{n ≥ 𝔟_{4^k - 1}} Qₓ(n, ρ_k)]`. -/
def explicitTail {X : Type*} [Fintype X] (v : X → ℝ) (ρ : ℝ) (ρk : ℕ → ℝ) (bcum b : ℕ → ℕ)
    (H : ℕ) : ℝ≥0∞ :=
  ∑ x, ((∑' n, if bcum (H - 1) ≤ n then ENNReal.ofReal (Qtail (v x) n ρ) else 0) +
    (∑' i, if H ≤ i then ENNReal.ofReal (Qtail (v x) (b i) ρ) else 0) +
    ∑' k, if H ≤ 4 ^ k then
      (∑' n, if bcum (4 ^ k - 1) ≤ n then ENNReal.ofReal (Qtail (v x) n (ρk k)) else 0)
      else 0)

/-- **Union bound behind `eq:v34-tail-stop`.**  `Y x` is the intrinsic tape of query type
`x` (independent `N(μₓ, vₓ)` observations).  Suppose the event `S` (the procedure has not
stopped by batch `j`) is contained in the union over query types of: a bad prefix of length
at least `𝔟_{H-1}` at radius `ρ`; a bad fresh batch `i ≥ H`; a bad prefix of length at least
`𝔟_{4^k - 1}` at the refresh radius `ρ_k` for some refresh `4^k ≥ H`.  Then
`P(S) ≤ p_j`, the explicit tail.

Proved here: the three prefix/refresh terms, from the Gaussian law of the tapes alone.
Assumed: the inclusion `hincl` (the pathwise argument; its batch-evidence half is
`good_window_stops`) and `hbatch`, the bound `P(batch i of type x is bad) ≤ Qₓ(b_i, ρ)` for a
fresh batch of predictable size at least `b_i`. -/
theorem tail_union_bound {X : Type*} [Fintype X] (P : Measure Ω) [IsProbabilityMeasure P]
    {μ v : X → ℝ} (hv : ∀ x, 0 < v x) {ρ : ℝ} {ρk : ℕ → ℝ} (hρ0 : 0 < ρ)
    (hρv : ∀ x, ρ ≤ v x / 8) (hρk0 : ∀ k, 0 < ρk k) (hρkv : ∀ k x, ρk k ≤ v x / 8)
    {Y : X → ℕ → Ω → ℝ} (hind : ∀ x, iIndepFun (Y x) P)
    (hY : ∀ x i, HasLaw (Y x i) (gaussianReal (μ x) (v x).toNNReal) P)
    (bcum b : ℕ → ℕ) (H : ℕ) (batchBad : X → ℕ → Set Ω)
    (hbatch : ∀ x i, H ≤ i → P (batchBad x i) ≤ ENNReal.ofReal (Qtail (v x) (b i) ρ))
    (S : Set Ω)
    (hincl : S ⊆ ⋃ x, ({ω | ∃ n, bcum (H - 1) ≤ n ∧ ω ∈ prefixBad (Y x) (μ x) (v x) ρ n} ∪
      {ω | ∃ i, H ≤ i ∧ ω ∈ batchBad x i} ∪
      {ω | ∃ k, H ≤ 4 ^ k ∧ ∃ n, bcum (4 ^ k - 1) ≤ n ∧
        ω ∈ prefixBad (Y x) (μ x) (v x) (ρk k) n})) :
    P S ≤ explicitTail v ρ ρk bcum b H := by
  refine (measure_mono hincl).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  unfold explicitTail
  refine Finset.sum_le_sum fun x _ => ?_
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ?_ ?_)) ?_)
  · exact prefix_concentration_tail P (hv x) hρ0 (hρv x) (hind x) (hY x) _
  · exact concentration_prefix P (batchBad x) (fun i => Qtail (v x) (b i) ρ) H
      fun i hi => hbatch x i hi
  · have hsub : {ω | ∃ k, H ≤ 4 ^ k ∧ ∃ n, bcum (4 ^ k - 1) ≤ n ∧
          ω ∈ prefixBad (Y x) (μ x) (v x) (ρk k) n} ⊆
        ⋃ k, if H ≤ 4 ^ k then
          {ω | ∃ n, bcum (4 ^ k - 1) ≤ n ∧ ω ∈ prefixBad (Y x) (μ x) (v x) (ρk k) n} else ∅ := by
      rintro ω ⟨k, hk, hω⟩
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      simp only [hk, ↓reduceIte]
      exact hω
    refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
    refine tsum_le_tsum fun k => ?_
    split_ifs with hk
    · exact prefix_concentration_tail P (hv x) (hρk0 k) (hρkv k x) (hind x) (hY x) _
    · simp

end Tail

/-! ### Finite confidence and the leading coefficient -/

section FiniteConfidence

lemma sum_range_succ_eq_sum_Icc (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, f (j + 1) = ∑ i ∈ Icc 1 n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- The first batch index `j⋆ ≥ j₁` with `c N_j ≥ B` exists when `N_j → ∞`
(`j⋆(B_δ)` in the manuscript). -/
theorem exists_first_crossing {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {c : ℝ} (hc : 0 < c)
    (B : ℝ) (j1 : ℕ) :
    ∃ jstar, j1 ≤ jstar ∧ B ≤ c * N jstar ∧ ∀ j, j1 ≤ j → j < jstar → c * N j < B := by
  classical
  have hex : ∃ j, j1 ≤ j ∧ B ≤ c * N j := by
    obtain ⟨j, hj1, hj2⟩ := ((eventually_ge_atTop j1).and
      (hN.eventually_ge_atTop (B / c))).exists
    exact ⟨j, hj1, by have := (div_le_iff₀ hc).mp hj2; linarith⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj hlt => ?_⟩
  by_contra hcon
  exact Nat.find_min hex hlt ⟨hj, not_lt.mp hcon⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Finite-confidence expected stopping bound (`eq:v34-finite-envelope` and the overshoot
step).**  `S j` is the event that the procedure has not stopped by the end of batch `j`, `R j`
the size of batch `j`, `N_j = ∑_{i ≤ j} R_i`, and the stopping time (in observations) is
`τ = ∑_j R_{j+1} 1_{S j}`.  With `η = C s / (16 (1 + s))` and `B = log (K / δ) ≥ 0`, assume

* `htail`: `P(S j) ≤ p_j` for every `j ≥ j₁` with `(C - 2 η) N_j ≥ B` (`eq:v34-tail-stop`);
* `hsum`: `∑_{j ≥ j₁} R_{j+1} min {1, p_j} ≤ Σ` (`eq:v34-tail-summability`);
* `hstep`: `R_j ≤ (s / 4) N_{j-1}` beyond `j_s ≥ j₁ + 1`, and `N_j → ∞`.

Then `E τ ≤ N_{j_s} + Σ + (1 + s) / C · B`. -/
theorem expected_stopping_le (P : Measure Ω) [IsProbabilityMeasure P] (S : ℕ → Set Ω)
    (hS : ∀ j, MeasurableSet (S j)) (R : ℕ → ℝ) (hR0 : ∀ j, 0 ≤ R j) (p : ℕ → ℝ≥0∞)
    {C η s B Sig : ℝ} {j1 js : ℕ} (hC : 0 < C) (hs0 : 0 < s)
    (hη : η = C * s / (16 * (1 + s))) (hB : 0 ≤ B) (hSig : 0 ≤ Sig)
    (hNtop : Tendsto (fun j => ∑ i ∈ Icc 1 j, R i) atTop atTop) (hjs : j1 + 1 ≤ js)
    (hstep : ∀ j, js < j → R j ≤ s / 4 * ∑ i ∈ Icc 1 (j - 1), R i)
    (htail : ∀ j, j1 ≤ j → B ≤ (C - 2 * η) * ∑ i ∈ Icc 1 j, R i → P (S j) ≤ p j)
    (hsum : (∑' j, if j1 ≤ j then ENNReal.ofReal (R (j + 1)) * min 1 (p j) else 0) ≤
      ENNReal.ofReal Sig) :
    ∫⁻ ω, ∑' j, ENNReal.ofReal (R (j + 1)) * (S j).indicator 1 ω ∂P ≤
      ENNReal.ofReal (∑ i ∈ Icc 1 js, R i + Sig + (1 + s) / C * B) := by
  set N : ℕ → ℝ := fun j => ∑ i ∈ Icc 1 j, R i with hNdef
  have hN0 : ∀ j, 0 ≤ N j := fun j => sum_nonneg fun i _ => hR0 i
  have hmono : Monotone N := by
    intro a b hab
    exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hab) fun i _ _ => hR0 i
  have hc : 0 < C - 2 * η := by
    have h1 : 2 * η = C * (s / (8 * (1 + s))) := by rw [hη]; field_simp; ring
    have h2 : s / (8 * (1 + s)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have := mul_lt_mul_of_pos_left h2 hC
    linarith
  obtain ⟨jstar, hj1, hcross, hmin⟩ := exists_first_crossing hNtop hc B j1
  have htail' : ∀ j, jstar ≤ j → P (S j) ≤ p j := fun j hj =>
    htail j (hj1.trans hj)
      (hcross.trans (mul_le_mul_of_nonneg_left (hmono hj) hc.le))
  have h1 := lintegral_stopping_le P S hS (fun j => ENNReal.ofReal (R j)) p jstar htail'
  have hfirst : ∑ j ∈ range jstar, ENNReal.ofReal (R (j + 1)) = ENNReal.ofReal (N jstar) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hR0 (j + 1), sum_range_succ_eq_sum_Icc]
  have hsecond : (∑' j, if jstar ≤ j then ENNReal.ofReal (R (j + 1)) * min 1 (p j) else 0) ≤
      ENNReal.ofReal Sig := by
    refine le_trans (tsum_le_tsum fun j => ?_) hsum
    by_cases hj : jstar ≤ j
    · simp only [hj, hj1.trans hj, ↓reduceIte, le_refl]
    · simp only [hj, ↓reduceIte, zero_le]
  have hover : N jstar ≤ N js + (1 + s) / C * B := by
    refine overshoot_bound hC hs0 hη hB hN0 hmono hjs (fun j hj => ?_) hmin
    have hj1' : 1 ≤ j := by omega
    have e : N j - N (j - 1) = R j := by
      simp only [hNdef]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp
    rw [e]
    exact hstep j hj
  refine h1.trans ?_
  rw [hfirst]
  refine (add_le_add le_rfl hsecond).trans ?_
  rw [← ENNReal.ofReal_add (hN0 jstar) hSig]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Sharp rate from the stopping tail (`eq:v34-sharp-rate`).**  For each confidence
`δ ∈ (0, 1)`, `S δ j` is the event that the `δ`-procedure has not stopped by the end of batch
`j`; the batch sizes `R j ≥ 0` do not depend on `δ` (the allocation is continued
counterfactually), `N_j = ∑_{i ≤ j} R_i → ∞` and `R_j / N_{j-1} → 0` (`hstepLim`); `K ≥ 1` is
the number of root actions and `C = C_* > 0`.  Assume that for every rational `s ∈ (0, 1]`,
with `η = C s / (16 (1 + s))`, there are an onset `j₁` and a tail sequence `p` (both may depend
on `s`, not on `δ`) such that

* `∑_{j ≥ j₁} R_{j+1} min {1, p_j} < ∞` (`eq:v34-tail-summability`), and
* `P(S δ j) ≤ p_j` whenever `j ≥ j₁` and `(C - 2 η) N_j ≥ log (K / δ)` (`eq:v34-tail-stop`).

Then for every rational `s ∈ (0, 1]` there is a constant `D_s ≥ 0`, independent of `δ`, with
`E τ_δ ≤ D_s + (1 + s) / C · log (1 / δ)` for all `δ ∈ (0, 1)`; and
`limsup_{δ ↓ 0} E τ_δ / log (1 / δ) ≤ 1 / C`, in the form: for every `c > 1 / C`, eventually
`E τ_δ ≤ c log (1 / δ)`.  Here `E τ_δ = E ∑_j R_{j+1} 1_{S δ j}` (survival identity).  The
constant is `D_s = N_{j_s} + ∑_{j ≥ j₁} R_{j+1} min {1, p_j} + (1 + s) / C · log K`, as in
`eq:v34-discovery-constant`. -/
theorem sharp_rate_of_tail (P : Measure Ω) [IsProbabilityMeasure P] (S : ℝ → ℕ → Set Ω)
    (hS : ∀ δ j, MeasurableSet (S δ j)) (R : ℕ → ℝ) (hR0 : ∀ j, 0 ≤ R j) {C K : ℝ}
    (hC : 0 < C) (hK : 1 ≤ K)
    (hNtop : Tendsto (fun j => ∑ i ∈ Icc 1 j, R i) atTop atTop)
    (hstepLim : ∀ ε : ℝ, 0 < ε → ∃ j0 : ℕ, ∀ j, j0 < j → R j ≤ ε * ∑ i ∈ Icc 1 (j - 1), R i)
    (htail : ∀ s : ℚ, 0 < s → s ≤ 1 → ∃ (j1 : ℕ) (p : ℕ → ℝ≥0∞),
      (∑' j, if j1 ≤ j then ENNReal.ofReal (R (j + 1)) * min 1 (p j) else 0) ≠ ∞ ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ j, j1 ≤ j →
        Real.log (K / δ) ≤ (C - 2 * (C * (s : ℝ) / (16 * (1 + (s : ℝ))))) *
          ∑ i ∈ Icc 1 j, R i → P (S δ j) ≤ p j) :
    (∀ s : ℚ, 0 < s → s ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, ∑' j, ENNReal.ofReal (R (j + 1)) * (S δ j).indicator 1 ω ∂P ≤
        ENNReal.ofReal (D + (1 + (s : ℝ)) / C * Real.log (1 / δ))) ∧
    ∀ c : ℝ, 1 / C < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, ∑' j, ENNReal.ofReal (R (j + 1)) * (S δ j).indicator 1 ω ∂P).toReal ≤
        c * Real.log (1 / δ) := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hfirst : ∀ s : ℚ, 0 < s → s ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, ∑' j, ENNReal.ofReal (R (j + 1)) * (S δ j).indicator 1 ω ∂P ≤
        ENNReal.ofReal (D + (1 + (s : ℝ)) / C * Real.log (1 / δ)) := by
    intro s hs0 hs1
    have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
    obtain ⟨j1, p, hfin, htl⟩ := htail s hs0 hs1
    obtain ⟨j0, hj0⟩ := hstepLim ((s : ℝ) / 4) (by positivity)
    set js := max j0 (j1 + 1) with hjs
    set Sig := (∑' j, if j1 ≤ j then ENNReal.ofReal (R (j + 1)) * min 1 (p j) else 0).toReal
      with hSig
    have hSig0 : 0 ≤ Sig := ENNReal.toReal_nonneg
    have hNjs : 0 ≤ ∑ i ∈ Icc 1 js, R i := sum_nonneg fun i _ => hR0 i
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
    have hcoef : 0 ≤ (1 + (s : ℝ)) / C := by positivity
    refine ⟨∑ i ∈ Icc 1 js, R i + Sig + (1 + (s : ℝ)) / C * Real.log K, by positivity,
      fun δ hδ0 hδ1 => ?_⟩
    have hBeq : Real.log (K / δ) = Real.log K + Real.log (1 / δ) := by
      rw [one_div, Real.log_inv, Real.log_div hK0.ne' hδ0.ne']
      ring
    have hB : 0 ≤ Real.log (K / δ) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hδ0]
      linarith
    have h := expected_stopping_le P (S δ) (hS δ) R hR0 p (C := C) (s := (s : ℝ))
      (B := Real.log (K / δ)) (Sig := Sig) (j1 := j1) (js := js) hC hs0' rfl hB hSig0 hNtop
      (le_max_right _ _) (fun j hj => hj0 j (lt_of_le_of_lt (le_max_left _ _) hj))
      (fun j hj hcr => htl δ hδ0 hδ1 j hj hcr) (by rw [hSig, ENNReal.ofReal_toReal hfin])
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hBeq]
    ring
  refine ⟨hfirst, fun c hc => ?_⟩
  classical
  choose! D hD0 hD using hfirst
  set Eτ : ℝ → ℝ := fun δ =>
    (∫⁻ ω, ∑' j, ENNReal.ofReal (R (j + 1)) * (S δ j).indicator 1 ω ∂P).toReal with hEτ
  refine limsup_coefficient (Eτ := Eτ) hC D (fun s hs0 hs1 δ hδ0 hδ1 => ?_) hc
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    linarith
  have hnn : 0 ≤ D s + (1 + (s : ℝ)) / C * Real.log (1 / δ) := by
    have := hD0 s hs0 hs1
    have : 0 ≤ (1 + (s : ℝ)) / C * Real.log (1 / δ) := by positivity
    linarith
  exact ENNReal.toReal_le_of_le_ofReal hnn (hD s hs0 hs1 δ hδ0 hδ1)

end FiniteConfidence

/-! ### The sharp rate on the manuscript's schedule -/

section ScheduleRate

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Sharp rate on the denominator-free schedule (`eq:v34-sharp-rate`).**
`sharp_rate_of_tail` for the batch sizes `R_j = M_j + m b_j`: the schedule hypotheses
(`N_j → ∞`, `R_j / N_{j-1} → 0`) are proved (`tendsto_cumN_atTop`,
`tendsto_batchR_div_cumN`).  What remains assumed, for every rational `s ∈ (0, 1]` with
`η = C s / (16 (1 + s))`: an onset `j₁` and a tail sequence `p` with
`∑_{j ≥ j₁} R_{j+1} min {1, p_j} < ∞` (`eq:v34-tail-summability`) and
`P(τ_δ > N_j) ≤ p_j` whenever `j ≥ j₁` and `(C - 2 η) N_j ≥ log (K / δ)`
(`eq:v34-tail-stop`). -/
theorem sharp_rate_schedule (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ)
    (S : ℝ → ℕ → Set Ω) (hS : ∀ δ j, MeasurableSet (S δ j)) {C K : ℝ} (hC : 0 < C)
    (hK : 1 ≤ K)
    (htail : ∀ s : ℚ, 0 < s → s ≤ 1 → ∃ (j1 : ℕ) (p : ℕ → ℝ≥0∞),
      (∑' j, if j1 ≤ j then ENNReal.ofReal (batchR m (j + 1)) * min 1 (p j) else 0) ≠ ∞ ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ j, j1 ≤ j →
        Real.log (K / δ) ≤ (C - 2 * (C * (s : ℝ) / (16 * (1 + (s : ℝ))))) * cumN m j →
          P (S δ j) ≤ p j) :
    (∀ s : ℚ, 0 < s → s ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, ∑' j, ENNReal.ofReal (batchR m (j + 1)) * (S δ j).indicator 1 ω ∂P ≤
        ENNReal.ofReal (D + (1 + (s : ℝ)) / C * Real.log (1 / δ))) ∧
    ∀ c : ℝ, 1 / C < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, ∑' j, ENNReal.ofReal (batchR m (j + 1)) * (S δ j).indicator 1 ω ∂P).toReal ≤
        c * Real.log (1 / δ) := by
  have hcum : ∀ j, ∑ i ∈ Icc 1 j, (batchR m i : ℝ) = cumN m j := fun j => by
    simp [cumN]
  refine sharp_rate_of_tail P S hS (fun j => (batchR m j : ℝ)) (fun j => Nat.cast_nonneg _)
    hC hK ?_ ?_ ?_
  · simp only [hcum]
    exact tendsto_cumN_atTop m
  · intro ε hε
    obtain ⟨j0, hj0⟩ := eventually_atTop.mp
      ((tendsto_batchR_div_cumN m).eventually (gt_mem_nhds hε))
    refine ⟨max j0 1, fun j hj => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi0 : j0 ≤ i := by
      have := le_max_left j0 1
      omega
    have hi1 : 1 ≤ i := by
      have := le_max_right j0 1
      omega
    have hNpos : (0 : ℝ) < cumN m i := by
      have h := two_mul_cumN_ge m i
      have h' : (i : ℝ) * (i + 1) ≤ 2 * cumN m i := by exact_mod_cast h
      have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
      nlinarith
    have := (div_lt_iff₀ hNpos).mp (hj0 i hi0)
    simp only [Nat.add_sub_cancel, hcum]
    linarith
  · intro s hs0 hs1
    obtain ⟨j1, p, hfin, htl⟩ := htail s hs0 hs1
    exact ⟨j1, p, hfin, fun δ hδ0 hδ1 j hj hcr => htl δ hδ0 hδ1 j hj (by rwa [hcum] at hcr)⟩

end ScheduleRate

end

end JointRootCert
