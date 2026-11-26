/-
Certified restart bound (Theorem `thm:active-restart`, "Certified restart bound",
end of Appendix B).

The wrapper runs the optimistic-separation policy in fresh episodes `j ≥ 1` with confidence
`δ_j = δ / (j (j + 1))` and a cap of `2 ^ j` observations.

* `hasSum_restart_conf`, `restart_correct`: `∑_j δ_j = δ` and the union bound for
  correctness.
* `restart_episode_budget`, `restart_episode_samples`: a covered episode `j` needs at most
  `T_j ≤ H_ρ [1 + 32 (log (32 M / (δ ρ_min²)) + 2 log (j + 1))]` observations.
* `restart_numeric`, `restart_constants`: the numeric claims about
  `j_* = ⌈log₂ (256 H_ρ L)⌉` used in the proof.
* `restart_good_episode_within_cap`: a covered episode `j ≥ j_*` stops within its cap.
* `restart_lintegral_le`, `restart_ae_terminates`, `certified_restart_bound`: the
  geometric-tail computation `E τ ≤ (7/3) 2^{j_*} < 1600 H_ρ L` and almost-sure stopping.

The probabilistic structure of the wrapper (fresh independent episodes) is not modelled;
it enters through the hypotheses `hfail` / `hF`, as documented at each theorem.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset MeasureTheory
open scoped ENNReal

/-! ### The confidence schedule `δ_j = δ / (j (j + 1))` -/

/-- `∑_{j ≥ 1} δ / (j (j + 1)) = δ` (episode `j = i + 1`). -/
theorem hasSum_restart_conf (δ : ℝ) :
    HasSum (fun i : ℕ => δ / (((i : ℝ) + 1) * ((i : ℝ) + 2))) δ := by
  have h1 : HasSum (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
    have hpart : ∀ n : ℕ, ∑ i ∈ range n, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
        1 - 1 / ((n : ℝ) + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ, ih]
        push_cast
        field_simp
        ring
    simp_rw [hpart]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    simpa using this
  have h := h1.mul_left δ
  rw [mul_one] at h
  have hfun : (fun i : ℕ => δ * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) =
      fun i : ℕ => δ / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
    funext i
    rw [mul_one_div]
  rwa [hfun] at h

/-- **Correctness of the restarted procedure.**  If an incorrect output forces
non-coverage in some episode, and episode `i + 1` fails to cover with probability at most
`δ / ((i + 1) (i + 2))`, the error probability is at most `δ`.

`F i` stands for the non-coverage event of episode `i + 1`; the hypothesis `hF` is the
coverage guarantee of the fresh confidence boxes of that episode. -/
theorem restart_correct {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (Err : Set Ω) (F : ℕ → Set Ω) (hsub : Err ⊆ ⋃ i, F i)
    (hF : ∀ i : ℕ, P (F i) ≤ ENNReal.ofReal (δ / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) :
    P Err ≤ ENNReal.ofReal δ := by
  calc P Err ≤ P (⋃ i, F i) := measure_mono hsub
    _ ≤ ∑' i, P (F i) := measure_iUnion_le F
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (δ / (((i : ℝ) + 1) * ((i : ℝ) + 2))) :=
        tsum_le_tsum hF
    _ = ENNReal.ofReal (∑' i : ℕ, δ / (((i : ℝ) + 1) * ((i : ℝ) + 2))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          (hasSum_restart_conf δ).summable).symm
    _ = ENNReal.ofReal δ := by rw [(hasSum_restart_conf δ).tsum_eq]

/-! ### Observations needed by a covered episode -/

/-- The bound `H [1 + 32 (L₀ + 2 log (j + 1))]` on the observations of a covered
episode `j`, with `L₀ = log (32 M / (δ ρ_min²))`. -/
noncomputable def restartBudget (H L0 : ℝ) (j : ℕ) : ℝ :=
  H * (1 + 32 * (L0 + 2 * Real.log ((j : ℝ) + 1)))

/-- The episode index `j_* = ⌈log₂ (256 H L)⌉`. -/
noncomputable def restartEpisode (H L : ℝ) : ℕ := ⌈Real.logb 2 (256 * H * L)⌉₊

section Episode

variable {Z : Type*} [Fintype Z]

/-- The explicit budget of `active_sample_bound` at confidence `δ_j = δ / (j (j + 1))` is at
most `H_ρ [1 + 32 (log (32 M / (δ ρ_min²)) + 2 log (j + 1))]`. -/
theorem restart_episode_budget {M δ ρmin : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ρ : Z → ℝ) (hρmin : 0 < ρmin) (hρ : ∀ z, ρmin ≤ ρ z ∧ ρ z ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    (∑ z, (⌈32 / ρ z ^ 2 *
        Real.log (32 * M / (δ / ((j : ℝ) * ((j : ℝ) + 1)) * ρ z ^ 2))⌉₊ : ℝ)) ≤
      restartBudget (∑ z, 1 / ρ z ^ 2) (Real.log (32 * M / (δ * ρmin ^ 2))) j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < j := by linarith
  set c := δ / ((j : ℝ) * ((j : ℝ) + 1)) with hc
  have hcpos : 0 < c := by positivity
  have hcle : c ≤ δ := by
    rw [hc]
    apply div_le_self hδ0.le
    nlinarith
  have hcge : δ / ((j : ℝ) + 1) ^ 2 ≤ c := by
    rw [hc]
    apply div_le_div_of_nonneg_left hδ0.le (by positivity)
    nlinarith
  set a := 32 * M / (δ * ρmin ^ 2) with ha
  have hapos : 0 < a := by positivity
  set C := 1 + 32 * (Real.log a + 2 * Real.log ((j : ℝ) + 1)) with hC
  have hterm : ∀ z, (⌈32 / ρ z ^ 2 * Real.log (32 * M / (c * ρ z ^ 2))⌉₊ : ℝ) ≤
      1 / ρ z ^ 2 * C := by
    intro z
    obtain ⟨hz1, hz2⟩ := hρ z
    have hzpos : 0 < ρ z := lt_of_lt_of_le hρmin hz1
    have hz2' : ρ z ^ 2 ≤ 1 := by nlinarith
    have hmin2 : ρmin ^ 2 ≤ ρ z ^ 2 := by nlinarith
    set y := 32 * M / (c * ρ z ^ 2) with hy
    have hy1 : 1 ≤ y := by
      rw [hy, one_le_div (by positivity)]
      have : c * ρ z ^ 2 ≤ 1 * 1 := mul_le_mul (hcle.trans hδ1) hz2' (by positivity) (by norm_num)
      linarith
    have hyle : y ≤ a * ((j : ℝ) + 1) ^ 2 := by
      have h1 : y ≤ 32 * M / (δ / ((j : ℝ) + 1) ^ 2 * ρmin ^ 2) := by
        rw [hy]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul hcge hmin2 (by positivity) hcpos.le
      have h2 : 32 * M / (δ / ((j : ℝ) + 1) ^ 2 * ρmin ^ 2) = a * ((j : ℝ) + 1) ^ 2 := by
        rw [ha]
        field_simp
      linarith
    have hlogy : Real.log y ≤ Real.log a + 2 * Real.log ((j : ℝ) + 1) := by
      calc Real.log y ≤ Real.log (a * ((j : ℝ) + 1) ^ 2) :=
            Real.log_le_log (by linarith) hyle
        _ = Real.log a + 2 * Real.log ((j : ℝ) + 1) := by
            rw [Real.log_mul hapos.ne' (by positivity), Real.log_pow]
            push_cast
            ring
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hinv : 1 ≤ 1 / ρ z ^ 2 := by
      rw [one_le_div (by positivity)]
      exact hz2'
    have hx0 : 0 ≤ 32 / ρ z ^ 2 * Real.log y := by positivity
    have hceil := (Nat.ceil_lt_add_one hx0).le
    have hmul : 32 / ρ z ^ 2 * Real.log y ≤
        32 / ρ z ^ 2 * (Real.log a + 2 * Real.log ((j : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hlogy (by positivity)
    have hexp : 1 / ρ z ^ 2 * C = 1 / ρ z ^ 2 +
        32 / ρ z ^ 2 * (Real.log a + 2 * Real.log ((j : ℝ) + 1)) := by
      rw [hC]
      ring
    linarith
  unfold restartBudget
  rw [sum_mul]
  exact sum_le_sum (fun z _ => hterm z)

/-- **Observations of a covered episode.**  In episode `j ≥ 1` (confidence
`δ / (j (j + 1))`), a run in which every queried terminal is at least as wide as its
threshold `ρ z` (the conclusion of `active_os_width` on the coverage event) makes at most
`H_ρ [1 + 32 (log (32 M / (δ ρ_min²)) + 2 log (j + 1))]` queries. -/
theorem restart_episode_samples [DecidableEq Z] {M δ ρmin : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) (ρ : Z → ℝ) (hρmin : 0 < ρmin) (hρ : ∀ z, ρmin ≤ ρ z ∧ ρ z ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) (τ : ℕ) (sel : ℕ → Z) (wsel : ℕ → ℝ)
    (hnest : ∀ t < τ, wsel t ≤
      nestedWidth M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (priorCount sel t))
    (hcharged : ∀ t < τ, ρ (sel t) ≤ wsel t) :
    (τ : ℝ) ≤ restartBudget (∑ z, 1 / ρ z ^ 2) (Real.log (32 * M / (δ * ρmin ^ 2))) j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hc0 : 0 < δ / ((j : ℝ) * ((j : ℝ) + 1)) := by positivity
  have hc1 : δ / ((j : ℝ) * ((j : ℝ) + 1)) < 1 := by
    have : δ / ((j : ℝ) * ((j : ℝ) + 1)) ≤ δ := by
      apply div_le_self hδ0.le
      nlinarith
    linarith
  have h := active_sample_bound hM hc0 hc1 τ sel wsel ρ
    (fun z => ⟨lt_of_lt_of_le hρmin (hρ z).1, (hρ z).2⟩) hnest hcharged
  have h' : (τ : ℝ) ≤ ∑ z, (⌈32 / ρ z ^ 2 *
      Real.log (32 * M / (δ / ((j : ℝ) * ((j : ℝ) + 1)) * ρ z ^ 2))⌉₊ : ℝ) := by
    exact_mod_cast h
  exact h'.trans (restart_episode_budget hM hδ0 (by linarith) ρ hρmin hρ hj)

end Episode

/-! ### Numeric claims about `j_*` -/

/-- **The numeric claims in the proof of Theorem `thm:active-restart`.**  With
`j_* = ⌈log₂ (256 H L)⌉`, `H ≥ 1`, `L ≥ log 1024` and `512 H ≤ e^L`:

* `256 H L ≤ 2^{j_*} < 512 H L`;
* `j_* ≤ 3 L` and `log (j_* + 1) ≤ L`;
* `T_{j_*} < 256 H L`;
* `T_j ≤ 2^j` for every `j ≥ j_*` (the bound less than doubles between episodes).

Here `T_j = restartBudget H (L - log 4) j`, and `L - log 4 = log (32 M / (δ ρ_min²))` when
`L = log (128 M / (δ ρ_min²))`; see `restart_constants` for the three hypotheses. -/
theorem restart_numeric {H L : ℝ} (hH : 1 ≤ H) (hL : Real.log 1024 ≤ L)
    (hHL : 512 * H ≤ Real.exp L) :
    256 * H * L ≤ 2 ^ restartEpisode H L ∧
    (2 : ℝ) ^ restartEpisode H L < 512 * H * L ∧
    (restartEpisode H L : ℝ) ≤ 3 * L ∧
    Real.log ((restartEpisode H L : ℝ) + 1) ≤ L ∧
    restartBudget H (L - Real.log 4) (restartEpisode H L) < 256 * H * L ∧
    ∀ j, restartEpisode H L ≤ j → restartBudget H (L - Real.log 4) j ≤ 2 ^ j := by
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hL6 : 6.9 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hHpos : 0 < H := by linarith
  set x := 256 * H * L with hx
  have hx1 : 1 ≤ x := by
    rw [hx]
    nlinarith
  have hxpos : 0 < x := by linarith
  have hlogb0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  set js := restartEpisode H L with hjs
  have hceil1 : Real.logb 2 x ≤ js := Nat.le_ceil _
  have hceil2 : (js : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlogb0
  have hpow1 : x ≤ 2 ^ js := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hceil1
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hxpos, Real.rpow_natCast] at this
  have hpow2 : (2 : ℝ) ^ js < 2 * x := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hceil2
    rwa [Real.rpow_natCast, Real.rpow_add (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hxpos, Real.rpow_one, mul_comm] at this
  have hlogL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
  have h2x : Real.log (2 * x) ≤ L + Real.log L := by
    have h : 2 * x ≤ Real.exp L * L := by
      rw [hx]
      nlinarith
    calc Real.log (2 * x) ≤ Real.log (Real.exp L * L) := Real.log_le_log (by positivity) h
      _ = L + Real.log L := by
          rw [Real.log_mul (Real.exp_pos _).ne' hLpos.ne', Real.log_exp]
  have hjs3 : (js : ℝ) ≤ 3 * L := by
    have h : Real.logb 2 x + 1 = Real.log (2 * x) / Real.log 2 := by
      rw [Real.logb, Real.log_mul (by norm_num) hxpos.ne']
      field_simp
      ring
    have h' : Real.log (2 * x) / Real.log 2 ≤ 3 * L := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hlogjs : Real.log ((js : ℝ) + 1) ≤ L := by
    have h1 : (js : ℝ) + 1 ≤ Real.exp L := by
      have := Real.quadratic_le_exp_of_nonneg hLpos.le
      nlinarith
    calc Real.log ((js : ℝ) + 1) ≤ Real.log (Real.exp L) :=
          Real.log_le_log (by positivity) h1
      _ = L := Real.log_exp L
  have hB : restartBudget H (L - Real.log 4) js < x := by
    unfold restartBudget
    have h : 1 + 32 * (L - Real.log 4 + 2 * Real.log ((js : ℝ) + 1)) < 256 * L := by
      linarith
    calc H * (1 + 32 * (L - Real.log 4 + 2 * Real.log ((js : ℝ) + 1)))
        < H * (256 * L) := mul_lt_mul_of_pos_left h hHpos
      _ = x := by rw [hx]; ring
  have hgrow : ∀ j : ℕ, restartBudget H (L - Real.log 4) (j + 1) ≤
      2 * restartBudget H (L - Real.log 4) j := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    have hlg : Real.log (((j + 1 : ℕ) : ℝ) + 1) ≤ Real.log 2 + Real.log ((j : ℝ) + 1) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    have h0 : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by linarith)
    unfold restartBudget
    have h : 1 + 32 * (L - Real.log 4 + 2 * Real.log (((j + 1 : ℕ) : ℝ) + 1)) ≤
        2 * (1 + 32 * (L - Real.log 4 + 2 * Real.log ((j : ℝ) + 1))) := by
      linarith
    calc H * (1 + 32 * (L - Real.log 4 + 2 * Real.log (((j + 1 : ℕ) : ℝ) + 1)))
        ≤ H * (2 * (1 + 32 * (L - Real.log 4 + 2 * Real.log ((j : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left h hHpos.le
      _ = 2 * (H * (1 + 32 * (L - Real.log 4 + 2 * Real.log ((j : ℝ) + 1)))) := by ring
  refine ⟨hpow1, by linarith, hjs3, hlogjs, hB, fun j hj => ?_⟩
  induction j, hj using Nat.le_induction with
  | base => linarith
  | succ j _ ih =>
    calc restartBudget H (L - Real.log 4) (j + 1)
        ≤ 2 * restartBudget H (L - Real.log 4) j := hgrow j
      _ ≤ 2 * 2 ^ j := by linarith
      _ = 2 ^ (j + 1) := by ring

/-- The hypotheses of `restart_numeric` hold for `H_ρ = ∑_z ρ_z⁻²` and
`L = log (128 M / (δ ρ_min²))` when `M ≥ max {2, |Z|}`, `0 < δ ≤ 1/4` and
`0 < ρ_min ≤ ρ_z ≤ 1`; moreover `log (32 M / (δ ρ_min²)) = L - log 4`. -/
theorem restart_constants {Z : Type*} [Fintype Z] [Nonempty Z] {M δ ρmin : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) (ρ : Z → ℝ)
    (hρmin : 0 < ρmin) (hρ : ∀ z, ρmin ≤ ρ z ∧ ρ z ≤ 1) :
    1 ≤ ∑ z, 1 / ρ z ^ 2 ∧
    Real.log 1024 ≤ Real.log (128 * M / (δ * ρmin ^ 2)) ∧
    512 * ∑ z, 1 / ρ z ^ 2 ≤ Real.exp (Real.log (128 * M / (δ * ρmin ^ 2))) ∧
    Real.log (32 * M / (δ * ρmin ^ 2)) =
      Real.log (128 * M / (δ * ρmin ^ 2)) - Real.log 4 := by
  obtain ⟨z0⟩ := ‹Nonempty Z›
  have hmin1 : ρmin ≤ 1 := (hρ z0).1.trans (hρ z0).2
  have hmin2 : ρmin ^ 2 ≤ 1 := by nlinarith
  have hmin2pos : 0 < ρmin ^ 2 := by positivity
  have hapos : 0 < 128 * M / (δ * ρmin ^ 2) := by positivity
  have hterm1 : ∀ z, 1 ≤ 1 / ρ z ^ 2 := by
    intro z
    have hz := hρ z
    have hzpos : 0 < ρ z := lt_of_lt_of_le hρmin hz.1
    rw [one_le_div (by positivity)]
    nlinarith
  have hterm2 : ∀ z, 1 / ρ z ^ 2 ≤ 1 / ρmin ^ 2 := by
    intro z
    have hz := hρ z
    apply div_le_div_of_nonneg_left (by norm_num) hmin2pos
    nlinarith
  have hH1 : 1 ≤ ∑ z, 1 / ρ z ^ 2 :=
    (hterm1 z0).trans
      (single_le_sum (f := fun z => 1 / ρ z ^ 2) (fun z _ => by positivity) (mem_univ z0))
  have hHle : ∑ z, 1 / ρ z ^ 2 ≤ M / ρmin ^ 2 := by
    calc ∑ z, 1 / ρ z ^ 2 ≤ ∑ _z : Z, 1 / ρmin ^ 2 := sum_le_sum (fun z _ => hterm2 z)
      _ = (Fintype.card Z : ℝ) * (1 / ρmin ^ 2) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ M * (1 / ρmin ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = M / ρmin ^ 2 := by ring
  refine ⟨hH1, ?_, ?_, ?_⟩
  · apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    have : δ * ρmin ^ 2 ≤ 1 / 4 * 1 := mul_le_mul hδ hmin2 (by positivity) (by norm_num)
    nlinarith
  · rw [Real.exp_log hapos]
    have h1 : 512 * (M / ρmin ^ 2) ≤ 128 * M / (δ * ρmin ^ 2) := by
      have hMpos : 0 < M := by linarith
      rw [← mul_div_assoc, div_le_div_iff₀ hmin2pos (by positivity)]
      nlinarith [mul_nonneg (mul_pos hMpos hmin2pos).le (by linarith : (0 : ℝ) ≤ 1 - 4 * δ)]
    linarith
  · rw [← Real.log_div hapos.ne' (by norm_num)]
    congr 1
    field_simp
    norm_num

/-- **A covered episode `j ≥ j_*` stops within its cap `2^j`.**  Combines
`restart_episode_samples`, `restart_constants` and `restart_numeric`. -/
theorem restart_good_episode_within_cap {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {M δ ρmin : ℝ} (hM : 2 ≤ M) (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (ρ : Z → ℝ) (hρmin : 0 < ρmin) (hρ : ∀ z, ρmin ≤ ρ z ∧ ρ z ≤ 1)
    {j : ℕ} (hj : 1 ≤ j)
    (hjs : restartEpisode (∑ z, 1 / ρ z ^ 2) (Real.log (128 * M / (δ * ρmin ^ 2))) ≤ j)
    (τ : ℕ) (sel : ℕ → Z) (wsel : ℕ → ℝ)
    (hnest : ∀ t < τ, wsel t ≤
      nestedWidth M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (priorCount sel t))
    (hcharged : ∀ t < τ, ρ (sel t) ≤ wsel t) :
    τ ≤ 2 ^ j := by
  obtain ⟨h1, h2, h3, h4⟩ := restart_constants hM hcard hδ0 hδ ρ hρmin hρ
  have hnum := (restart_numeric h1 h2 h3).2.2.2.2.2 j hjs
  have hs := restart_episode_samples hM hδ0 hδ ρ hρmin hρ hj τ sel wsel hnest hcharged
  rw [h4] at hs
  have : (τ : ℝ) ≤ 2 ^ j := hs.trans hnum
  exact_mod_cast this

/-! ### Expected number of observations -/

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Reaching episode `j_* + k` has probability at most `(δ / 2)^k`. -/
theorem restart_tail (P : Measure Ω) [IsProbabilityMeasure P] {δ : ℝ} (jstar : ℕ)
    (R : ℕ → Set Ω)
    (hfail : ∀ j, jstar ≤ j → P (R (j + 1)) ≤ ENNReal.ofReal (δ / 2) * P (R j)) (k : ℕ) :
    P (R (jstar + k)) ≤ ENNReal.ofReal (δ / 2) ^ k := by
  induction k with
  | zero => simpa using prob_le_one
  | succ k ih =>
    calc P (R (jstar + (k + 1))) ≤ ENNReal.ofReal (δ / 2) * P (R (jstar + k)) :=
          hfail _ (Nat.le_add_right _ _)
      _ ≤ ENNReal.ofReal (δ / 2) * ENNReal.ofReal (δ / 2) ^ k := by gcongr
      _ = ENNReal.ofReal (δ / 2) ^ (k + 1) := by rw [pow_succ']

/-- **Geometric-tail bound on the expected number of observations.**

`R j` is the event that episode `j` is reached, and `τ` is the total number of
observations, which is at most the sum of the caps `2^j` of the reached episodes.
`hfail` says that a reached episode `j ≥ j_*` fails to terminate with conditional
probability at most `δ / 2`; in the paper this follows from the independence of fresh
episodes, their coverage `1 - δ_j ≥ 1 - δ / 2`, and `restart_good_episode_within_cap`.
Then `E τ ≤ ∑_{j < j_*} 2^j + ∑_k 2^{j_* + k} (δ / 2)^k ≤ (7/3) 2^{j_*}`. -/
theorem restart_lintegral_le (P : Measure Ω) [IsProbabilityMeasure P] {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 4) (jstar : ℕ) (R : ℕ → Set Ω) (hR : ∀ j, MeasurableSet (R j))
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ∑' j : ℕ, (R j).indicator (fun _ => (2 : ℝ≥0∞) ^ j) ω)
    (hfail : ∀ j, jstar ≤ j → P (R (j + 1)) ≤ ENNReal.ofReal (δ / 2) * P (R j)) :
    ∫⁻ ω, τ ω ∂P ≤ ENNReal.ofReal (7 / 3 * 2 ^ jstar) := by
  have htail := restart_tail P jstar R hfail
  have htwo : ∀ n : ℕ, (2 : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
    intro n
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  -- real majorant of the summands
  set c : ℕ → ℝ := fun j => if j < jstar then (2 : ℝ) ^ j else (2 : ℝ) ^ jstar * δ ^ (j - jstar)
    with hc
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j
    simp only [hc]
    split_ifs <;> positivity
  have hterm : ∀ j : ℕ, (2 : ℝ≥0∞) ^ j * P (R j) ≤ ENNReal.ofReal (c j) := by
    intro j
    by_cases hj : j < jstar
    · have : c j = (2 : ℝ) ^ j := by simp [hc, hj]
      rw [this, ← htwo]
      calc (2 : ℝ≥0∞) ^ j * P (R j) ≤ 2 ^ j * 1 := mul_le_mul' le_rfl prob_le_one
        _ = 2 ^ j := mul_one _
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hj)
      have : c (jstar + k) = (2 : ℝ) ^ jstar * δ ^ k := by
        simp [hc]
      rw [this]
      calc (2 : ℝ≥0∞) ^ (jstar + k) * P (R (jstar + k))
          ≤ (2 : ℝ≥0∞) ^ (jstar + k) * ENNReal.ofReal (δ / 2) ^ k :=
            mul_le_mul' le_rfl (htail k)
        _ = ENNReal.ofReal ((2 : ℝ) ^ jstar * δ ^ k) := by
            have e1 : ENNReal.ofReal (δ / 2) ^ k = ENNReal.ofReal ((δ / 2) ^ k) :=
              (ENNReal.ofReal_pow (by positivity) k).symm
            have h2k : (0 : ℝ) ≤ 2 ^ (jstar + k) := by positivity
            rw [htwo, e1, ← ENNReal.ofReal_mul h2k]
            congr 1
            have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
            rw [div_pow, pow_add]
            field_simp
  have hshift : ∀ k : ℕ, c (k + jstar) = (2 : ℝ) ^ jstar * δ ^ k := by
    intro k
    have : ¬ (k + jstar < jstar) := by omega
    simp [hc]
  have hsumm_tail : Summable (fun k : ℕ => c (k + jstar)) := by
    simp_rw [hshift]
    exact (summable_geometric_of_lt_one hδ0 (by linarith)).mul_left _
  have hsumm : Summable c := (summable_nat_add_iff jstar).mp hsumm_tail
  have hhead : ∀ n : ℕ, n ≤ jstar → ∑ j ∈ range n, c j ≤ (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hlt : n < jstar := hn
      have hcn : c n = (2 : ℝ) ^ n := by simp [hc, hlt]
      rw [sum_range_succ, hcn, pow_succ]
      linarith [ih hlt.le]
  have htsum : ∑' j, c j ≤ 7 / 3 * 2 ^ jstar := by
    rw [← hsumm.sum_add_tsum_nat_add jstar]
    simp_rw [hshift]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 (by linarith)]
    have hinv : (1 - δ)⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hp : (0 : ℝ) < 2 ^ jstar := by positivity
    have h1 := hhead jstar le_rfl
    have h2 : (2 : ℝ) ^ jstar * (1 - δ)⁻¹ ≤ 2 ^ jstar * (4 / 3) :=
      mul_le_mul_of_nonneg_left hinv hp.le
    linarith
  calc ∫⁻ ω, τ ω ∂P
      ≤ ∫⁻ ω, ∑' j : ℕ, (R j).indicator (fun _ => (2 : ℝ≥0∞) ^ j) ω ∂P := lintegral_mono hτ
    _ = ∑' j : ℕ, ∫⁻ ω, (R j).indicator (fun _ => (2 : ℝ≥0∞) ^ j) ω ∂P :=
        lintegral_tsum (fun j => (measurable_const.indicator (hR j)).aemeasurable)
    _ = ∑' j : ℕ, (2 : ℝ≥0∞) ^ j * P (R j) := by
        congr 1
        funext j
        exact lintegral_indicator_const (hR j) _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (c j) := tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j, c j) := (ENNReal.ofReal_tsum_of_nonneg hc0 hsumm).symm
    _ ≤ ENNReal.ofReal (7 / 3 * 2 ^ jstar) := ENNReal.ofReal_le_ofReal htsum

/-- **Almost-sure termination.**  Under the same conditional-failure hypothesis, the
event that every episode is reached has probability zero. -/
theorem restart_ae_terminates (P : Measure Ω) [IsProbabilityMeasure P] {δ : ℝ}
    (hδ : δ ≤ 1 / 4) (jstar : ℕ) (R : ℕ → Set Ω)
    (hfail : ∀ j, jstar ≤ j → P (R (j + 1)) ≤ ENNReal.ofReal (δ / 2) * P (R j)) :
    P (⋂ j, R j) = 0 := by
  have htail := restart_tail P jstar R hfail
  have hlt : ENNReal.ofReal (δ / 2) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)
  have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  have hle : ∀ k : ℕ, P (⋂ j, R j) ≤ ENNReal.ofReal (δ / 2) ^ k := fun k =>
    (measure_mono (Set.iInter_subset _ (jstar + k))).trans (htail k)
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' hlim hle)

/-- **Certified restart bound (Theorem `thm:active-restart`), expected observations.**

With `H_ρ = ∑_z ρ_z⁻²`, `L = log (128 M / (δ ρ_min²))` and
`j_* = ⌈log₂ (256 H_ρ L)⌉`, the restarted procedure satisfies
`E τ_rest < 1600 H_ρ L` and stops almost surely.

Proved here: all numeric steps and the geometric-tail computation.  Hypotheses standing
in for the unformalized episode model: `R j` is the event that episode `j` is reached;
`hτ` says the observation count is at most the sum of the caps of the reached episodes;
`hfail` says that a reached episode `j ≥ j_*` is followed by another one with conditional
probability at most `δ / 2` (fresh-episode coverage at level `δ_j ≤ δ / 2` together with
`restart_good_episode_within_cap`).  `ρ_min` may be any positive lower bound on the `ρ_z`,
in particular their minimum; `ρ_z ≤ 1` is the standing normalisation of
`active_sample_bound`. -/
theorem certified_restart_bound {Z : Type*} [Fintype Z] [Nonempty Z] {M δ ρmin : ℝ}
    (hM : 2 ≤ M) (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (ρ : Z → ℝ) (hρmin : 0 < ρmin) (hρ : ∀ z, ρmin ≤ ρ z ∧ ρ z ≤ 1)
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Set Ω) (hR : ∀ j, MeasurableSet (R j))
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ∑' j : ℕ, (R j).indicator (fun _ => (2 : ℝ≥0∞) ^ j) ω)
    (hfail : ∀ j,
      restartEpisode (∑ z, 1 / ρ z ^ 2) (Real.log (128 * M / (δ * ρmin ^ 2))) ≤ j →
      P (R (j + 1)) ≤ ENNReal.ofReal (δ / 2) * P (R j)) :
    ∫⁻ ω, τ ω ∂P <
        ENNReal.ofReal (1600 * (∑ z, 1 / ρ z ^ 2) * Real.log (128 * M / (δ * ρmin ^ 2))) ∧
      P (⋂ j, R j) = 0 ∧ ∀ᵐ ω ∂P, τ ω < ∞ := by
  obtain ⟨h1, h2, h3, -⟩ := restart_constants hM hcard hδ0 hδ ρ hρmin hρ
  obtain ⟨-, hlt, -⟩ := restart_numeric h1 h2 h3
  have hle := restart_lintegral_le P hδ0.le hδ _ R hR τ hτ hfail
  have hmain : ∫⁻ ω, τ ω ∂P <
      ENNReal.ofReal (1600 * (∑ z, 1 / ρ z ^ 2) * Real.log (128 * M / (δ * ρmin ^ 2))) := by
    refine lt_of_le_of_lt hle ?_
    have hp : (0 : ℝ) < 2 ^ restartEpisode (∑ z, 1 / ρ z ^ 2)
        (Real.log (128 * M / (δ * ρmin ^ 2))) := by positivity
    rw [ENNReal.ofReal_lt_ofReal_iff (by nlinarith)]
    nlinarith
  refine ⟨hmain, restart_ae_terminates P hδ _ R hfail, ?_⟩
  -- `τ` is dominated by a measurable function with the same integral bound
  have hdom : ∀ᵐ ω ∂P, (∑' j : ℕ, (R j).indicator (fun _ => (2 : ℝ≥0∞) ^ j) ω) < ∞ := by
    refine ae_lt_top' (AEMeasurable.tsum
      (fun j => (measurable_const.indicator (hR j)).aemeasurable)) ?_
    have := restart_lintegral_le P hδ0.le hδ _ R hR
      (fun ω => ∑' j : ℕ, (R j).indicator (fun _ => (2 : ℝ≥0∞) ^ j) ω) (fun _ => le_rfl) hfail
    exact (lt_of_le_of_lt this ENNReal.ofReal_lt_top).ne
  filter_upwards [hdom] with ω hω using lt_of_le_of_lt (hτ ω) hω

end Expectation

end JointRootCert
