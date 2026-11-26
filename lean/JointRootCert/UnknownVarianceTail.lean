/-
Unknown-variance Gaussian tracking: summability of the explicit tail
(manuscript, proof of Theorem `thm:v34-adaptive`, display `eq:v34-tail-summability`).

Results covered:

* `Qtail_le_exp`, `prefix_tail_le`: explicit geometric bounds for the Gaussian tail
  `Q_x(n, r)` of `eq:v34-concentration-tail` and for its sum over `n ≥ N`, with the dependence
  on the radius `r` explicit;
* `prefix_term_le`, `batch_term_le`, `refresh_term_le`: each of the three terms of the
  explicit tail `p_j` of `eq:v34-explicit-tail`, as a function of `H = H_j`, is eventually at
  most `B / (H³ 16^⌊√H⌋)`;
* `explicitTailW`, `explicitTailW_le`: the same bound for the explicit tail with a weight
  `W_i ≤ c b_i⁸` on the batch term (`W = 1` is `explicitTail`, `explicitTailW_one`);
* `segW`, `segW_le`: the weight `(N_{i-1} + 1)(R_i + 1)` used in
  `UnknownVarianceTracker.lean`;
* `batchR_succ_le_refH`: `R_{j+1} ≤ 24 (1 + 3 m) H_j 16^⌊√H_j⌋`;
* `tail_summability`: `∑_{j ≥ j₁} R_{j+1} min {1, p_j} < ∞` (`eq:v34-tail-summability`), for
  any refresh radii with `c / (k + 1) ≤ ρ_k ≤ 1`; `tail_summabilityW` is the weighted form;
* `refreshRadius`, `tail_summability_refreshRadius`: the same for the manuscript's
  `ρ_k = min {1, v_min / 8, h_k / (64 L₀)}`, `h_k = (k + 1)^{-1/2}` (`eq:v34-refresh-radius`).

The growth facts the manuscript quotes (`b_{H_j} ≥ c 2^{√j / 9}`, superpolynomial growth of
`𝔟_{4^k - 1} ρ_k²`) are used in the forms `M_i ≤ b_i²` (`clockM_le_baseB_sq`), hence
`i ≤ b_i²` and `2^⌊√i⌋ ≤ b_i²`, and `(k + 1)⁴ ≤ b_{4^k - 1}` for `k ≥ 7`
(`succ_pow_four_le_baseB`).
-/
import JointRootCert.UnknownVarianceRate
import JointRootCert.Completions4

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ### Geometric bounds for the Gaussian tail -/

/-- The exponential rate constant of `Q(n, r)`: `min {1 / (2 v), 1 / (64 v²)}`. -/
def tailGamma (v : ℝ) : ℝ := min (1 / (2 * v)) (1 / (64 * v ^ 2))

lemma tailGamma_pos {v : ℝ} (hv : 0 < v) : 0 < tailGamma v :=
  lt_min (by positivity) (by positivity)

/-- Beyond the onset `n₀(v, r)`, `Q(n, r) ≤ 4 e^a e^{-n a}` with `a = γ(v) r²`. -/
lemma Qtail_le_exp {v r : ℝ} (hv : 0 < v) {n : ℕ} (hn : n0 v r ≤ n) :
    Qtail v n r ≤ 4 * Real.exp (tailGamma v * r ^ 2) *
      Real.exp (-(n * (tailGamma v * r ^ 2))) := by
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hg1 : tailGamma v ≤ 1 / (2 * v) := min_le_left _ _
  have hg2 : tailGamma v ≤ 1 / (64 * v ^ 2) := min_le_right _ _
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg _
  set a := tailGamma v * r ^ 2 with ha
  have ha0 : 0 ≤ a := mul_nonneg (tailGamma_pos hv).le hr2
  unfold Qtail
  simp only [not_lt.mpr hn, ↓reduceIte]
  refine (min_le_right _ _).trans ?_
  have h1 : Real.exp (-(n * r ^ 2 / (2 * v))) ≤ Real.exp (a - n * a) := by
    apply Real.exp_le_exp.mpr
    have h : a * n ≤ 1 / (2 * v) * r ^ 2 * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg1 hr2) (by linarith)
    have e : (n : ℝ) * r ^ 2 / (2 * v) = 1 / (2 * v) * r ^ 2 * n := by ring
    rw [e]
    linarith
  have h2 : Real.exp (-(((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2))) ≤ Real.exp (a - n * a) := by
    apply Real.exp_le_exp.mpr
    have h : a * ((n : ℝ) - 1) ≤ 1 / (64 * v ^ 2) * r ^ 2 * ((n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg2 hr2) (by linarith)
    have e : ((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2) = 1 / (64 * v ^ 2) * r ^ 2 * ((n : ℝ) - 1) := by
      ring
    rw [e]
    linarith
  have e3 : 4 * Real.exp a * Real.exp (-(n * a)) = 4 * Real.exp (a - n * a) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
  rw [e3]
  linarith

lemma tsum_le_ofReal_tsum {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g)
    (h : ∀ n, f n ≤ ENNReal.ofReal (g n)) : ∑' n, f n ≤ ENNReal.ofReal (∑' n, g n) := by
  rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg]
  exact tsum_le_tsum h

lemma inv_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) : (1 - Real.exp (-x))⁻¹ ≤ 1 + 1 / x := by
  have h1 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp x])
  have h2 : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    have : 1 - 1 / (1 + x) = x / (1 + x) := by field_simp; ring
    linarith
  have h3 : 0 < x / (1 + x) := by positivity
  calc (1 - Real.exp (-x))⁻¹ ≤ (x / (1 + x))⁻¹ := inv_anti₀ h3 h2
    _ = 1 + 1 / x := by field_simp; ring

/-- **Sum of the Gaussian tail over all counts `n ≥ N`,** for `N ≥ n₀(v, r)`:
`∑_{n ≥ N} Q(n, r) ≤ 4 e^a (1 + 2 / a) e^{-N a / 2}` with `a = γ(v) r²`. -/
theorem prefix_tail_le {v r : ℝ} (hv : 0 < v) (hr : 0 < r) {N : ℕ} (hN : n0 v r ≤ N) :
    (∑' n, if N ≤ n then ENNReal.ofReal (Qtail v n r) else 0) ≤
      ENNReal.ofReal (4 * Real.exp (tailGamma v * r ^ 2) * (1 + 2 / (tailGamma v * r ^ 2)) *
        Real.exp (-(N * (tailGamma v * r ^ 2) / 2))) := by
  set a := tailGamma v * r ^ 2 with ha
  have ha0 : 0 < a := mul_pos (tailGamma_pos hv) (by positivity)
  set q := Real.exp (-(a / 2)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    linarith
  set c := 4 * Real.exp a * Real.exp (-(N * a / 2)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hgs : Summable (fun n : ℕ => c * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left c
  refine (tsum_le_ofReal_tsum (g := fun n => c * q ^ n) (fun n => by positivity) hgs
    (fun n => ?_)).trans ?_
  · split_ifs with hn
    · refine ENNReal.ofReal_le_ofReal ((Qtail_le_exp hv (hN.trans hn)).trans ?_)
      have hqn : q ^ n = Real.exp (-(n * a / 2)) := by
        rw [hq, ← Real.exp_nat_mul]
        congr 1
        ring
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hexp : Real.exp (-(n * a)) ≤ Real.exp (-(N * a / 2)) * Real.exp (-(n * a / 2)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right hNn ha0.le
        linarith
      calc 4 * Real.exp a * Real.exp (-(n * a))
          ≤ 4 * Real.exp a * (Real.exp (-(N * a / 2)) * Real.exp (-(n * a / 2))) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = c * q ^ n := by rw [hqn, hc]; ring
    · exact bot_le
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    have h := inv_one_sub_exp_neg_le (x := a / 2) (by positivity)
    have e : 1 + 1 / (a / 2) = 1 + 2 / a := by field_simp
    rw [e] at h
    calc c * (1 - q)⁻¹ ≤ c * (1 + 2 / a) := mul_le_mul_of_nonneg_left h hc0
      _ = 4 * Real.exp a * (1 + 2 / a) * Real.exp (-(N * a / 2)) := by rw [hc]; ring

/-- `t^p e^{-c t} ≤ p! / c^p` for `t ≥ 0`. -/
lemma pow_mul_exp_neg_le (p : ℕ) {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    t ^ p * Real.exp (-(c * t)) ≤ p.factorial / c ^ p := by
  have h := Real.pow_div_factorial_le_exp (x := c * t) (by positivity) p
  have hf : (0 : ℝ) < p.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  calc t ^ p * c ^ p = (c * t) ^ p := by rw [mul_pow]; ring
    _ ≤ Real.exp (c * t) * p.factorial := h
    _ = p.factorial * Real.exp (c * t) := by ring

/-! ### Growth of the schedule -/

/-- `M_j ≤ b_j²`. -/
lemma clockM_le_baseB_sq (j : ℕ) : clockM j ≤ baseB j * baseB j := by
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
  exact_mod_cast h2

/-- The comparison weight `G(H) = H³ 16^⌊√H⌋`. -/
def tailG (H : ℕ) : ℝ := (H : ℝ) ^ 3 * 16 ^ Nat.sqrt H

lemma tailG_pos {H : ℕ} (hH : 1 ≤ H) : 0 < tailG H := by
  have : (0 : ℝ) < H := by exact_mod_cast hH
  unfold tailG
  positivity

lemma tailG_nonneg (H : ℕ) : 0 ≤ tailG H := by
  unfold tailG
  positivity

lemma tailG_mono {H H' : ℕ} (h : H ≤ H') : tailG H ≤ tailG H' := by
  unfold tailG
  have h1 : (H : ℝ) ≤ H' := by exact_mod_cast h
  have h2 : (16 : ℝ) ^ Nat.sqrt H ≤ 16 ^ Nat.sqrt H' :=
    pow_le_pow_right₀ (by norm_num) (Nat.sqrt_le_sqrt h)
  exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3) h2 (by positivity) (by positivity)

/-- `G(i) ≤ b_i¹⁴`. -/
lemma tailG_le_baseB (i : ℕ) : tailG i ≤ (baseB i : ℝ) ^ 14 := by
  have h1 : (i : ℝ) ≤ (baseB i : ℝ) ^ 2 := by
    have := le_baseB_sq i
    rw [sq]
    exact_mod_cast this
  have h2 : (2 : ℝ) ^ Nat.sqrt i ≤ (baseB i : ℝ) ^ 2 := by
    have := (pow_sqrt_le_clockM i).trans (clockM_le_baseB_sq i)
    rw [sq]
    exact_mod_cast this
  have e : (16 : ℝ) ^ Nat.sqrt i = ((2 : ℝ) ^ Nat.sqrt i) ^ 4 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  unfold tailG
  rw [e]
  calc (i : ℝ) ^ 3 * ((2 : ℝ) ^ Nat.sqrt i) ^ 4
      ≤ ((baseB i : ℝ) ^ 2) ^ 3 * ((baseB i : ℝ) ^ 2) ^ 4 :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3)
          (pow_le_pow_left₀ (by positivity) h2 4) (by positivity) (by positivity)
    _ = (baseB i : ℝ) ^ 14 := by ring

/-- `G(H) ≤ 128 G(H - 1)` for `H ≥ 2`. -/
lemma tailG_le_pred {H : ℕ} (hH : 2 ≤ H) : tailG H ≤ 128 * tailG (H - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, H = n + 1 := ⟨H - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hn : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * n := by push_cast; linarith
  have h2 : (16 : ℝ) ^ Nat.sqrt (n + 1) ≤ 16 ^ (Nat.sqrt n + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sqrt_succ_le_succ_sqrt n)
  unfold tailG
  calc ((n + 1 : ℕ) : ℝ) ^ 3 * 16 ^ Nat.sqrt (n + 1)
      ≤ (2 * (n : ℝ)) ^ 3 * 16 ^ (Nat.sqrt n + 1) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3) h2 (by positivity) (by positivity)
    _ = 128 * ((n : ℝ) ^ 3 * 16 ^ Nat.sqrt n) := by ring

lemma baseB_le_cumB {n : ℕ} (hn : 1 ≤ n) : baseB n ≤ cumB n := by
  unfold cumB
  exact Finset.single_le_sum (f := fun i => baseB i) (fun i _ => Nat.zero_le _)
    (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)

/-- `G(H) ≤ 128 𝔟_{H-1}¹⁴` for `H ≥ 2`. -/
lemma tailG_le_cumB {H : ℕ} (hH : 2 ≤ H) : tailG H ≤ 128 * (cumB (H - 1) : ℝ) ^ 14 := by
  have h1 : (baseB (H - 1) : ℝ) ≤ cumB (H - 1) := by
    exact_mod_cast baseB_le_cumB (by omega : 1 ≤ H - 1)
  calc tailG H ≤ 128 * tailG (H - 1) := tailG_le_pred hH
    _ ≤ 128 * (baseB (H - 1) : ℝ) ^ 14 := by
        have := tailG_le_baseB (H - 1)
        linarith
    _ ≤ 128 * (cumB (H - 1) : ℝ) ^ 14 := by
        have := pow_le_pow_left₀ (Nat.cast_nonneg (baseB (H - 1))) h1 14
        linarith

lemma eight_mul_le_two_pow (n : ℕ) : 8 * (n + 7) ≤ 2 ^ (n + 6) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h8 : 8 ≤ 2 ^ (n + 6) := by
      calc 8 ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (n + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 ^ (n + 1 + 6) = 2 * 2 ^ (n + 6) := by
      rw [show n + 1 + 6 = (n + 6) + 1 by ring, pow_succ]
      ring
    rw [e]
    omega

/-- `(k + 1)⁴ ≤ b_{4^k - 1}` for `k ≥ 7`. -/
lemma succ_pow_four_le_baseB {k : ℕ} (hk : 7 ≤ k) : (k + 1) ^ 4 ≤ baseB (4 ^ k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 7 := ⟨k - 7, by omega⟩
  set b := baseB (4 ^ (n + 7) - 1) with hb
  have h4 : (4 : ℕ) ^ (n + 6) = 2 ^ (n + 6) * 2 ^ (n + 6) := by
    rw [← mul_pow]; norm_num
  have hsq : 2 ^ (n + 6) ≤ Nat.sqrt (4 ^ (n + 7) - 1) := by
    rw [Nat.le_sqrt, ← h4]
    have e : (4 : ℕ) ^ (n + 7) = 4 * 4 ^ (n + 6) := by
      rw [show n + 7 = (n + 6) + 1 by ring, pow_succ]
      ring
    have : 1 ≤ 4 ^ (n + 6) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have h1 : 2 ^ (2 ^ (n + 6)) ≤ b * b :=
    (Nat.pow_le_pow_right (by norm_num) hsq).trans
      ((pow_sqrt_le_clockM _).trans (clockM_le_baseB_sq _))
  have h2 : (n + 7 + 1) ^ 8 ≤ 2 ^ (2 ^ (n + 6)) := by
    have hlt : n + 7 + 1 ≤ 2 ^ (n + 7) := Nat.lt_two_pow_self
    calc (n + 7 + 1) ^ 8 ≤ (2 ^ (n + 7)) ^ 8 := Nat.pow_le_pow_left hlt 8
      _ = 2 ^ (8 * (n + 7)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (2 ^ (n + 6)) := Nat.pow_le_pow_right (by norm_num) (eight_mul_le_two_pow n)
  have h3 : ((n + 7 + 1) ^ 4) * ((n + 7 + 1) ^ 4) ≤ b * b := by
    calc ((n + 7 + 1) ^ 4) * ((n + 7 + 1) ^ 4) = (n + 7 + 1) ^ 8 := by ring
      _ ≤ b * b := h2.trans h1
  exact Nat.mul_self_le_mul_self_iff.mp h3

/-! ### The three terms of the explicit tail -/

/-- **First term of `eq:v34-explicit-tail`** (future prefix estimates at the batch radius):
eventually in `H`, `∑_{n ≥ 𝔟_{H-1}} Q(n, ρ) ≤ B / G(H)`. -/
theorem prefix_term_le {v ρ : ℝ} (hv : 0 < v) (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ H0 : ℕ, ∀ H, H0 ≤ H →
      (∑' n, if cumB (H - 1) ≤ n then ENNReal.ofReal (Qtail v n ρ) else 0) ≤
        ENNReal.ofReal (B / tailG H) := by
  set a := tailGamma v * ρ ^ 2 with ha
  have ha0 : 0 < a := mul_pos (tailGamma_pos hv) (by positivity)
  set C1 := 4 * Real.exp a * (1 + 2 / a) with hC1
  have hC10 : 0 ≤ C1 := by positivity
  set C2 : ℝ := (Nat.factorial 14 : ℝ) / (a / 2) ^ 14 with hC2
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨C1 * (128 * C2), by positivity, n0 v ρ + 2, fun H hH => ?_⟩
  have hH2 : 2 ≤ H := by omega
  have hN : n0 v ρ ≤ cumB (H - 1) := (by omega : n0 v ρ ≤ H - 1).trans (le_cumB _)
  refine (prefix_tail_le hv hρ hN).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← ha, ← hC1, le_div_iff₀ (tailG_pos (by omega))]
  set N : ℝ := (cumB (H - 1) : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hpe := pow_mul_exp_neg_le 14 (c := a / 2) (by positivity) hN0
  have hG := tailG_le_cumB hH2
  have hE0 : 0 ≤ Real.exp (-(N * a / 2)) := (Real.exp_pos _).le
  have e : Real.exp (-(N * a / 2)) = Real.exp (-(a / 2 * N)) := by
    congr 1
    ring
  calc C1 * Real.exp (-(N * a / 2)) * tailG H
      ≤ C1 * Real.exp (-(N * a / 2)) * (128 * N ^ 14) :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg hC10 hE0)
    _ = C1 * (128 * (N ^ 14 * Real.exp (-(a / 2 * N)))) := by rw [e]; ring
    _ ≤ C1 * (128 * C2) := by
        refine mul_le_mul_of_nonneg_left ?_ hC10
        linarith

/-- **Second term of `eq:v34-explicit-tail`** (future fresh batches), with a weight `W_i`
of at most polynomial growth in `b_i` (`W_i ≤ c b_i⁸`): eventually in `H`,
`∑_{i ≥ H} W_i Q(b_i, ρ) ≤ B / G(H)`.  The manuscript's term is `W = 1`. -/
theorem batch_term_le {v ρ : ℝ} (hv : 0 < v) (hρ : 0 < ρ) {W : ℕ → ℝ} {cW : ℝ}
    (hcW : 0 ≤ cW) (hW : ∀ i, W i ≤ cW * (baseB i : ℝ) ^ 8) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ H0 : ℕ, ∀ H, H0 ≤ H →
      (∑' i, if H ≤ i then ENNReal.ofReal (W i * Qtail v (baseB i) ρ) else 0) ≤
        ENNReal.ofReal (B / tailG H) := by
  set a := tailGamma v * ρ ^ 2 with ha
  have ha0 : 0 < a := mul_pos (tailGamma_pos hv) (by positivity)
  set B1 : ℝ := cW * (4 * Real.exp a * ((Nat.factorial 26 : ℝ) / a ^ 26)) with hB1
  have hB10 : 0 ≤ B1 := by positivity
  have hS : Summable (fun i : ℕ => 1 / (i : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  set S2 : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ 2 with hS2
  have hS20 : 0 ≤ S2 := tsum_nonneg fun i => by positivity
  refine ⟨B1 * S2, by positivity, max 1 (n0 v ρ * n0 v ρ), fun H hH => ?_⟩
  have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
  have hHn : n0 v ρ * n0 v ρ ≤ H := (le_max_right _ _).trans hH
  have hG0 := tailG_pos hH1
  have hgs : Summable (fun i : ℕ => B1 / tailG H * (1 / (i : ℝ) ^ 2)) := hS.mul_left _
  refine (tsum_le_ofReal_tsum (g := fun i : ℕ => B1 / tailG H * (1 / (i : ℝ) ^ 2))
    (fun i => by positivity) hgs (fun i => ?_)).trans ?_
  · split_ifs with hi
    · have hi1 : 1 ≤ i := hH1.trans hi
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
      have hb : n0 v ρ ≤ baseB i := le_baseB_of_sq_le (hHn.trans hi)
      have hWQ : W i * Qtail v (baseB i) ρ ≤ cW * (baseB i : ℝ) ^ 8 *
          (4 * Real.exp (tailGamma v * ρ ^ 2) *
            Real.exp (-((baseB i : ℝ) * (tailGamma v * ρ ^ 2)))) :=
        mul_le_mul (hW i) (Qtail_le_exp hv hb) (Qtail_nonneg _ _ _) (by positivity)
      refine ENNReal.ofReal_le_ofReal (hWQ.trans ?_)
      rw [← ha]
      set b : ℝ := (baseB i : ℝ) with hbdef
      have hb0 : 0 ≤ b := Nat.cast_nonneg _
      have hpe := pow_mul_exp_neg_le 26 (c := a) ha0 hb0
      have h1 : (i : ℝ) ≤ b ^ 2 := by
        have : ((i : ℕ) : ℝ) ≤ (baseB i : ℝ) * baseB i := by exact_mod_cast le_baseB_sq i
        rw [sq]
        exact this
      have hGi : tailG H ≤ b ^ 14 := (tailG_mono hi).trans (tailG_le_baseB i)
      have hprod : (i : ℝ) ^ 2 * tailG H ≤ b ^ 18 := by
        calc (i : ℝ) ^ 2 * tailG H ≤ (b ^ 2) ^ 2 * b ^ 14 :=
              mul_le_mul (pow_le_pow_left₀ hi0.le h1 2) hGi (tailG_nonneg _) (by positivity)
          _ = b ^ 18 := by ring
      have e : B1 / tailG H * (1 / (i : ℝ) ^ 2) = B1 / ((i : ℝ) ^ 2 * tailG H) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have hE0 : 0 ≤ Real.exp (-(b * a)) := (Real.exp_pos _).le
      have e2 : Real.exp (-(b * a)) = Real.exp (-(a * b)) := by
        congr 1
        ring
      calc cW * b ^ 8 * (4 * Real.exp a * Real.exp (-(b * a))) * ((i : ℝ) ^ 2 * tailG H)
          ≤ cW * b ^ 8 * (4 * Real.exp a * Real.exp (-(b * a))) * b ^ 18 :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = cW * (4 * Real.exp a * (b ^ 26 * Real.exp (-(a * b)))) := by rw [e2]; ring
        _ ≤ B1 := by
            rw [hB1]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpe (by positivity)) hcW
    · exact bot_le
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [tsum_mul_left, ← hS2]
    ring

/-- **Third term of `eq:v34-explicit-tail`** (later refreshes at their shrinking radii):
for refresh radii with `c₁ / (k + 1) ≤ ρ_k ≤ 1`, eventually in `H`,
`∑_{k : 4^k ≥ H} ∑_{n ≥ 𝔟_{4^k - 1}} Q(n, ρ_k) ≤ B / G(H)`. -/
theorem refresh_term_le {v c1 : ℝ} (hv : 0 < v) (hc1 : 0 < c1) {ρk : ℕ → ℝ}
    (hρk1 : ∀ k, ρk k ≤ 1) (hρkc : ∀ k : ℕ, c1 / ((k : ℝ) + 1) ≤ ρk k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ H0 : ℕ, ∀ H, H0 ≤ H →
      (∑' k, if H ≤ 4 ^ k then
        (∑' n, if cumB (4 ^ k - 1) ≤ n then ENNReal.ofReal (Qtail v n (ρk k)) else 0)
        else 0) ≤ ENNReal.ofReal (B / tailG H) := by
  have hγ := tailGamma_pos hv
  set γ := tailGamma v with hγdef
  set d := γ * c1 ^ 2 with hd
  have hd0 : 0 < d := by positivity
  set B2 : ℝ := 4 * Real.exp γ * (1 + 2 / d) * (256 * ((Nat.factorial 33 : ℝ) / (d / 2) ^ 33))
    with hB2
  have hB20 : 0 ≤ B2 := by positivity
  set k1 : ℕ := max 7 ⌈4 * v / c1⌉₊ with hk1
  have hq0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hq1 : (1 / 4 : ℝ) < 1 := by norm_num
  refine ⟨B2 * (1 - 1 / 4)⁻¹, by positivity, 4 ^ k1, fun H hH => ?_⟩
  have hH1 : 1 ≤ H := (Nat.one_le_pow _ _ (by norm_num)).trans hH
  have hG0 := tailG_pos hH1
  have hgs : Summable (fun k : ℕ => B2 / tailG H * (1 / 4 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine (tsum_le_ofReal_tsum (g := fun k : ℕ => B2 / tailG H * (1 / 4 : ℝ) ^ k)
    (fun k => by positivity) hgs (fun k => ?_)).trans ?_
  · split_ifs with hk
    · -- `k ≥ k₁`
      have hkk : k1 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 4)).mp (hH.trans hk)
      have hk7 : 7 ≤ k := (le_max_left _ _).trans hkk
      have hkc : 4 * v / c1 ≤ k := by
        have h1 : ⌈4 * v / c1⌉₊ ≤ k := (le_max_right _ _).trans hkk
        exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hρ0 : 0 < ρk k := lt_of_lt_of_le (by positivity) (hρkc k)
      -- the base count
      have hbk := succ_pow_four_le_baseB hk7
      have h4k : 2 ≤ 4 ^ k := by
        calc 2 ≤ 4 ^ 1 := by norm_num
          _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hbN : baseB (4 ^ k - 1) ≤ cumB (4 ^ k - 1) := baseB_le_cumB (by omega)
      have hbN' : (baseB (4 ^ k - 1) : ℝ) ≤ (cumB (4 ^ k - 1) : ℝ) := by exact_mod_cast hbN
      have hkb : ((k : ℝ) + 1) ^ 4 ≤ (baseB (4 ^ k - 1) : ℝ) := by exact_mod_cast hbk
      have h4b' : (4 : ℝ) ^ k ≤ (baseB (4 ^ k - 1) : ℝ) * (baseB (4 ^ k - 1) : ℝ) + 1 := by
        have h1 := le_baseB_sq (4 ^ k - 1)
        have h2 : 4 ^ k ≤ baseB (4 ^ k - 1) * baseB (4 ^ k - 1) + 1 := by omega
        exact_mod_cast h2
      set b : ℝ := (baseB (4 ^ k - 1) : ℝ) with hbdef
      set N : ℝ := (cumB (4 ^ k - 1) : ℝ) with hNdef
      have hb1 : (1 : ℝ) ≤ b := by
        have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
        linarith
      -- onset
      have hn0 : n0 v (ρk k) ≤ cumB (4 ^ k - 1) := by
        refine le_trans ?_ hbN
        refine le_trans ?_ hbk
        unfold n0
        refine max_le ?_ ?_
        · calc 3 ≤ (7 + 1) ^ 4 := by norm_num
            _ ≤ (k + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        · rw [Nat.ceil_le]
          push_cast
          have h1 : 4 * v / ρk k ≤ 4 * v / (c1 / ((k : ℝ) + 1)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (hρkc k)
          have h2 : 4 * v / (c1 / ((k : ℝ) + 1)) = 4 * v / c1 * ((k : ℝ) + 1) := by
            field_simp
          have h3 : 4 * v / c1 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hk0.le
          have h4 : ((k : ℝ) + 1) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 4 := by
            have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
            have hx2 : (1 : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) := by nlinarith
            calc ((k : ℝ) + 1) * ((k : ℝ) + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 1) * 1 := by ring
              _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) * (((k : ℝ) + 1) * ((k : ℝ) + 1)) :=
                  mul_le_mul_of_nonneg_left hx2 (by positivity)
              _ = ((k : ℝ) + 1) ^ 4 := by ring
          linarith
      refine (prefix_tail_le hv hρ0 hn0).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hγdef, ← hNdef]
      set ak := γ * ρk k ^ 2 with hak
      have hak0 : 0 < ak := by positivity
      have hakγ : ak ≤ γ := by
        have : ρk k ^ 2 ≤ 1 := pow_le_one₀ hρ0.le (hρk1 k)
        calc ak ≤ γ * 1 := mul_le_mul_of_nonneg_left this hγ.le
          _ = γ := mul_one _
      set t := Real.sqrt b with ht
      have ht2 : t * t = b := Real.mul_self_sqrt (by linarith)
      have ht1 : 1 ≤ t := by
        rw [ht]
        exact Real.le_sqrt_of_sq_le (by rw [one_pow]; exact hb1)
      have hkt : ((k : ℝ) + 1) ^ 2 ≤ t := by
        rw [ht]
        apply Real.le_sqrt_of_sq_le
        calc (((k : ℝ) + 1) ^ 2) ^ 2 = ((k : ℝ) + 1) ^ 4 := by ring
          _ ≤ b := hkb
      have hakd : d / t ≤ ak := by
        have h1 : c1 ^ 2 / ((k : ℝ) + 1) ^ 2 ≤ ρk k ^ 2 := by
          rw [← div_pow]
          exact pow_le_pow_left₀ (by positivity) (hρkc k) 2
        have h2 : c1 ^ 2 / t ≤ c1 ^ 2 / ((k : ℝ) + 1) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hkt
        calc d / t = γ * (c1 ^ 2 / t) := by rw [hd]; ring
          _ ≤ γ * ρk k ^ 2 := mul_le_mul_of_nonneg_left (h2.trans h1) hγ.le
      have ht0 : 0 < t := by linarith
      -- the three factors
      have hf1 : Real.exp ak ≤ Real.exp γ := Real.exp_le_exp.mpr hakγ
      have hf2 : 1 + 2 / ak ≤ (1 + 2 / d) * t := by
        have h1 : 2 / ak ≤ 2 / (d / t) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hakd
        have h2 : 2 / (d / t) = 2 / d * t := by field_simp
        nlinarith
      have hf3 : Real.exp (-(N * ak / 2)) ≤ Real.exp (-(d / 2 * t)) := by
        apply Real.exp_le_exp.mpr
        have h1 : b * (d / t) ≤ N * ak :=
          mul_le_mul hbN' hakd (by positivity) (by linarith)
        have h2 : b * (d / t) = d * t := by
          rw [← ht2]
          field_simp
        linarith
      have hprod : (4 : ℝ) ^ k * tailG H ≤ 256 * t ^ 32 := by
        have hG1 : tailG H ≤ 128 * b ^ 14 := by
          calc tailG H ≤ tailG (4 ^ k) := tailG_mono hk
            _ ≤ 128 * tailG (4 ^ k - 1) := tailG_le_pred h4k
            _ ≤ 128 * b ^ 14 := by
                have := tailG_le_baseB (4 ^ k - 1)
                linarith
        have h4b : (4 : ℝ) ^ k ≤ 2 * b ^ 2 := by
          nlinarith
        calc (4 : ℝ) ^ k * tailG H ≤ (2 * b ^ 2) * (128 * b ^ 14) :=
              mul_le_mul h4b hG1 (tailG_nonneg _) (by positivity)
          _ = 256 * (t * t) ^ 16 := by rw [ht2]; ring
          _ = 256 * t ^ 32 := by ring
      have hpe := pow_mul_exp_neg_le 33 (c := d / 2) (by positivity) ht0.le
      have e : B2 / tailG H * (1 / 4 : ℝ) ^ k = B2 / ((4 : ℝ) ^ k * tailG H) := by
        rw [one_div, inv_pow]
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have hE0 : 0 < Real.exp (-(d / 2 * t)) := Real.exp_pos _
      calc 4 * Real.exp ak * (1 + 2 / ak) * Real.exp (-(N * ak / 2)) * ((4 : ℝ) ^ k * tailG H)
          ≤ 4 * Real.exp γ * ((1 + 2 / d) * t) * Real.exp (-(d / 2 * t)) * (256 * t ^ 32) := by
            have hpos1 : 0 ≤ 1 + 2 / ak := by positivity
            have hpos2 : 0 ≤ (4 : ℝ) ^ k * tailG H := mul_nonneg (by positivity) (tailG_nonneg _)
            refine mul_le_mul (mul_le_mul (mul_le_mul
              (mul_le_mul_of_nonneg_left hf1 (by norm_num)) hf2 hpos1 (by positivity)) hf3
              (Real.exp_pos _).le (by positivity)) hprod hpos2 (by positivity)
        _ = 4 * Real.exp γ * (1 + 2 / d) * (256 * (t ^ 33 * Real.exp (-(d / 2 * t)))) := by ring
        _ ≤ B2 := by
            rw [hB2]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith
    · exact bot_le
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    ring

/-- The explicit tail of `eq:v34-explicit-tail` on the manuscript's schedule, with a weight
`W_i` on the batch term:
`∑ₓ [∑_{n ≥ 𝔟_{H-1}} Qₓ(n, ρ) + ∑_{i ≥ H} W_i Qₓ(b_i, ρ)
  + ∑_{k : 4^k ≥ H} ∑_{n ≥ 𝔟_{4^k - 1}} Qₓ(n, ρ_k)]`.  For `W = 1` it is `explicitTail`
(`explicitTailW_one`). -/
def explicitTailW {X : Type*} [Fintype X] (W : ℕ → ℝ) (v : X → ℝ) (ρ : ℝ) (ρk : ℕ → ℝ)
    (H : ℕ) : ℝ≥0∞ :=
  ∑ x, ((∑' n, if cumB (H - 1) ≤ n then ENNReal.ofReal (Qtail (v x) n ρ) else 0) +
    (∑' i, if H ≤ i then ENNReal.ofReal (W i * Qtail (v x) (baseB i) ρ) else 0) +
    ∑' k, if H ≤ 4 ^ k then
      (∑' n, if cumB (4 ^ k - 1) ≤ n then ENNReal.ofReal (Qtail (v x) n (ρk k)) else 0)
      else 0)

lemma explicitTailW_one {X : Type*} [Fintype X] (v : X → ℝ) (ρ : ℝ) (ρk : ℕ → ℝ) (H : ℕ) :
    explicitTailW (fun _ => 1) v ρ ρk H = explicitTail v ρ ρk cumB baseB H := by
  simp only [explicitTailW, explicitTail, one_mul]

/-- **The (weighted) explicit tail is eventually at most `B / (H³ 16^⌊√H⌋)`.** -/
theorem explicitTailW_le {X : Type*} [Fintype X] {v : X → ℝ} (hv : ∀ x, 0 < v x) {ρ c1 : ℝ}
    (hρ : 0 < ρ) (hc1 : 0 < c1) {ρk : ℕ → ℝ} (hρk1 : ∀ k, ρk k ≤ 1)
    (hρkc : ∀ k : ℕ, c1 / ((k : ℝ) + 1) ≤ ρk k) {W : ℕ → ℝ} {cW : ℝ}
    (hcW : 0 ≤ cW) (hW : ∀ i, W i ≤ cW * (baseB i : ℝ) ^ 8) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ H0 : ℕ, ∀ H, H0 ≤ H →
      explicitTailW W v ρ ρk H ≤ ENNReal.ofReal (B / tailG H) := by
  classical
  choose Ba hBa0 Ha hBa using fun x => prefix_term_le (hv x) hρ
  choose Bb hBb0 Hb hBb using fun x => batch_term_le (hv x) hρ hcW hW
  choose Bc hBc0 Hc hBc using fun x => refresh_term_le (hv x) hc1 hρk1 hρkc
  refine ⟨∑ x, (Ba x + Bb x + Bc x),
    Finset.sum_nonneg fun x _ => add_nonneg (add_nonneg (hBa0 x) (hBb0 x)) (hBc0 x),
    1 + ∑ x, (Ha x + Hb x + Hc x), fun H hH => ?_⟩
  have hHx : ∀ x, Ha x + Hb x + Hc x ≤ H := fun x => by
    have := Finset.single_le_sum (f := fun x => Ha x + Hb x + Hc x)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ x)
    omega
  have hG0 := tailG_pos (by omega : 1 ≤ H)
  unfold explicitTailW
  rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg
    (fun x _ => div_nonneg (add_nonneg (add_nonneg (hBa0 x) (hBb0 x)) (hBc0 x)) hG0.le)]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [add_div, add_div, ENNReal.ofReal_add (add_nonneg (div_nonneg (hBa0 x) hG0.le)
    (div_nonneg (hBb0 x) hG0.le)) (div_nonneg (hBc0 x) hG0.le),
    ENNReal.ofReal_add (div_nonneg (hBa0 x) hG0.le) (div_nonneg (hBb0 x) hG0.le)]
  have := hHx x
  exact add_le_add (add_le_add (hBa x H (by omega)) (hBb x H (by omega))) (hBc x H (by omega))

/-! ### Summability of the weighted tail -/

/-- `R_{j+1} ≤ 24 (1 + 3 m) H_j 16^⌊√H_j⌋` for `j ≥ 16`. -/
lemma batchR_succ_le_refH (m : ℕ) {j : ℕ} (hj : 16 ≤ j) :
    (batchR m (j + 1) : ℝ) ≤
      24 * (1 + 3 * (m : ℝ)) * ((refH j : ℝ) * 16 ^ Nat.sqrt (refH j)) := by
  set H := refH j with hH
  set s := Nat.sqrt H with hs
  have hjH : j + 1 ≤ 16 * H := (refH_bounds hj).1
  have hH1 : 1 ≤ H := refH_pos j
  have hsq : Nat.sqrt (j + 1) ≤ 4 * s + 3 := by
    have h1 : Nat.sqrt (16 * H) < 4 * s + 4 := by
      rw [Nat.sqrt_lt]
      have := Nat.lt_succ_sqrt H
      rw [← hs] at this
      have e : (4 * s + 4) * (4 * s + 4) = 16 * (Nat.succ s * Nat.succ s) := by
        simp only [Nat.succ_eq_add_one]
        ring
      rw [e]
      omega
    have := Nat.sqrt_le_sqrt hjH
    omega
  have hpow : 2 ^ Nat.sqrt (j + 1) ≤ 8 * 16 ^ s := by
    calc 2 ^ Nat.sqrt (j + 1) ≤ 2 ^ (4 * s + 3) := Nat.pow_le_pow_right (by norm_num) hsq
      _ = 8 * 16 ^ s := by
          rw [pow_add, pow_mul]
          norm_num
          ring
  have h16 : 1 ≤ 16 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hclock : clockM (j + 1) ≤ 24 * (H * 16 ^ s) := by
    have h1 := clockM_le (j + 1)
    have h2 : H ≤ H * 16 ^ s := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : 16 ^ s ≤ H * 16 ^ s := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h := (batchR_le m (j + 1)).trans (Nat.mul_le_mul_left _ hclock)
  have h' : (batchR m (j + 1) : ℝ) ≤ (((1 + 3 * m) * (24 * (H * 16 ^ s)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- **Summability of the weighted explicit tail (`eq:v34-tail-summability`).**  For query
variances `v x > 0`, a batch radius `ρ > 0` and refresh radii with `c₁ / (k + 1) ≤ ρ_k ≤ 1`,
and with `p_j` the explicit tail of `eq:v34-explicit-tail` evaluated at `H = H_j` on the
manuscript's schedule (`𝔟 = cumB`, `b = baseB`),
`∑_{j ≥ j₁} R_{j+1} min {1, p_j} < ∞` for every onset `j₁`. -/
theorem tail_summabilityW {X : Type*} [Fintype X] (m : ℕ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    {ρ c1 : ℝ} (hρ : 0 < ρ) (hc1 : 0 < c1) {ρk : ℕ → ℝ} (hρk1 : ∀ k, ρk k ≤ 1)
    (hρkc : ∀ k : ℕ, c1 / ((k : ℝ) + 1) ≤ ρk k) {W : ℕ → ℝ} {cW : ℝ}
    (hcW : 0 ≤ cW) (hW : ∀ i, W i ≤ cW * (baseB i : ℝ) ^ 8) (j1 : ℕ) :
    (∑' j, if j1 ≤ j then ENNReal.ofReal (batchR m (j + 1)) *
      min 1 (explicitTailW W v ρ ρk (refH j)) else 0) ≠ ∞ := by
  obtain ⟨B, hB0, H0, hB⟩ := explicitTailW_le hv hρ hc1 hρk1 hρkc hcW hW
  set J0 : ℕ := max 16 (16 * H0) with hJ0
  set D : ℝ := 24 * (1 + 3 * (m : ℝ)) * B * 256 with hD
  have hD0 : 0 ≤ D := by positivity
  set u : ℕ → ℝ := fun j =>
    (if j < J0 then (batchR m (j + 1) : ℝ) else 0) + D * (1 / (j : ℝ) ^ 2) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => by
    simp only [hu]
    have : (0 : ℝ) ≤ if j < J0 then (batchR m (j + 1) : ℝ) else 0 := by
      split_ifs
      · exact Nat.cast_nonneg _
      · exact le_rfl
    positivity
  have hus : Summable u := by
    refine Summable.add (summable_of_ne_finset_zero (s := Finset.range J0) fun j hj => ?_)
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left D)
    simp only [show ¬ j < J0 by simpa using hj, ↓reduceIte]
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (tsum_le_ofReal_tsum (g := u) hu0 hus fun j => ?_)
  have hR0 : (0 : ℝ) ≤ batchR m (j + 1) := Nat.cast_nonneg _
  have hD2 : 0 ≤ D * (1 / (j : ℝ) ^ 2) := by positivity
  split_ifs with hj1
  · by_cases hj : j < J0
    · calc ENNReal.ofReal (batchR m (j + 1)) * min 1 (explicitTailW W v ρ ρk (refH j))
          ≤ ENNReal.ofReal (batchR m (j + 1)) * 1 := by gcongr; exact min_le_left _ _
        _ = ENNReal.ofReal (batchR m (j + 1)) := mul_one _
        _ ≤ ENNReal.ofReal (u j) := by
            refine ENNReal.ofReal_le_ofReal ?_
            simp only [hu, hj, ↓reduceIte]
            linarith
    · have hjJ : J0 ≤ j := not_lt.mp hj
      have hj16 : 16 ≤ j := (le_max_left _ _).trans hjJ
      have hjH0 : 16 * H0 ≤ j := (le_max_right _ _).trans hjJ
      have hb := refH_bounds hj16
      have hHH : H0 ≤ refH j := by omega
      have hH1 : 1 ≤ refH j := refH_pos j
      have hG0 := tailG_pos hH1
      have hH0' : (0 : ℝ) < refH j := by exact_mod_cast hH1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hjle : (j : ℝ) ≤ 16 * refH j := by exact_mod_cast hb.1.le
      calc ENNReal.ofReal (batchR m (j + 1)) * min 1 (explicitTailW W v ρ ρk (refH j))
          ≤ ENNReal.ofReal (batchR m (j + 1)) * ENNReal.ofReal (B / tailG (refH j)) := by
            gcongr
            exact (min_le_right _ _).trans (hB _ hHH)
        _ = ENNReal.ofReal (batchR m (j + 1) * (B / tailG (refH j))) :=
            (ENNReal.ofReal_mul hR0).symm
        _ ≤ ENNReal.ofReal (u j) := by
            refine ENNReal.ofReal_le_ofReal ?_
            simp only [hu, hj, ↓reduceIte, zero_add]
            have h1 := batchR_succ_le_refH m hj16
            have h2 : (batchR m (j + 1) : ℝ) * (B / tailG (refH j)) ≤
                24 * (1 + 3 * (m : ℝ)) * ((refH j : ℝ) * 16 ^ Nat.sqrt (refH j)) *
                  (B / tailG (refH j)) :=
              mul_le_mul_of_nonneg_right h1 (div_nonneg hB0 hG0.le)
            have h3 : 24 * (1 + 3 * (m : ℝ)) * ((refH j : ℝ) * 16 ^ Nat.sqrt (refH j)) *
                (B / tailG (refH j)) = 24 * (1 + 3 * (m : ℝ)) * B / (refH j : ℝ) ^ 2 := by
              unfold tailG
              field_simp
            have h4 : 24 * (1 + 3 * (m : ℝ)) * B / (refH j : ℝ) ^ 2 ≤ D * (1 / (j : ℝ) ^ 2) := by
              have e : D * (1 / (j : ℝ) ^ 2) = 24 * (1 + 3 * (m : ℝ)) * B * (256 / (j : ℝ) ^ 2) := by
                rw [hD]
                ring
              rw [e, div_eq_mul_one_div]
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith
            linarith
  · exact bot_le

lemma one_le_baseB_pow (i : ℕ) : (1 : ℝ) ≤ 1 * (baseB i : ℝ) ^ 8 := by
  have : (2 : ℝ) ≤ baseB i := by exact_mod_cast two_le_baseB i
  rw [one_mul]
  exact one_le_pow₀ (by linarith)

/-- **Summability of the weighted explicit tail (`eq:v34-tail-summability`),** for the tail
`p_j` exactly as displayed in `eq:v34-explicit-tail` (`explicitTail` on the manuscript's
schedule). -/
theorem tail_summability {X : Type*} [Fintype X] (m : ℕ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    {ρ c1 : ℝ} (hρ : 0 < ρ) (hc1 : 0 < c1) {ρk : ℕ → ℝ} (hρk1 : ∀ k, ρk k ≤ 1)
    (hρkc : ∀ k : ℕ, c1 / ((k : ℝ) + 1) ≤ ρk k) (j1 : ℕ) :
    (∑' j, if j1 ≤ j then ENNReal.ofReal (batchR m (j + 1)) *
      min 1 (explicitTail v ρ ρk cumB baseB (refH j)) else 0) ≠ ∞ := by
  have h := tail_summabilityW m hv hρ hc1 hρk1 hρkc (W := fun _ => 1) (cW := 1)
    zero_le_one one_le_baseB_pow j1
  simpa only [explicitTailW_one] using h

/-- The number of tape segments a batch of type `x` at index `i` can occupy: start at most
`N_{i-1}`, length at most `R_i`. -/
def segW (m i : ℕ) : ℝ := ((cumN m (i - 1) + 1) * (batchR m i + 1) : ℕ)

lemma segW_nonneg (m i : ℕ) : 0 ≤ segW m i := Nat.cast_nonneg _

/-- `W_i ≤ (2 + 3 m)² b_i⁸`. -/
lemma segW_le (m i : ℕ) : segW m i ≤ (2 + 3 * (m : ℝ)) ^ 2 * (baseB i : ℝ) ^ 8 := by
  have hb2 := two_le_baseB i
  have hi : i ≤ baseB i * baseB i := le_baseB_sq i
  have hM : clockM i ≤ baseB i * baseB i := clockM_le_baseB_sq i
  have hR : batchR m i ≤ (1 + 3 * m) * (baseB i * baseB i) :=
    (batchR_le m i).trans (Nat.mul_le_mul_left _ hM)
  have hN : cumN m (i - 1) ≤ (baseB i * baseB i) * ((1 + 3 * m) * (baseB i * baseB i)) :=
    ((cumN_mono m (Nat.sub_le i 1)).trans (cumN_le m i)).trans (Nat.mul_le_mul hi hR)
  set b := baseB i with hb
  have hb4 : 1 ≤ b * b * (b * b) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 : cumN m (i - 1) + 1 ≤ (2 + 3 * m) * (b * b * (b * b)) := by nlinarith
  have h2 : batchR m i + 1 ≤ (2 + 3 * m) * (b * b * (b * b)) := by nlinarith
  have h3 := Nat.mul_le_mul h1 h2
  have h4 : segW m i ≤
      (((2 + 3 * m) * (b * b * (b * b)) * ((2 + 3 * m) * (b * b * (b * b))) : ℕ) : ℝ) := by
    unfold segW
    exact_mod_cast h3
  push_cast at h4
  refine h4.trans (le_of_eq ?_)
  ring

/-! ### The manuscript's refresh radius -/

/-- The refresh radius `ρ_k = min {1, v_min / 8, h_k / (64 L₀)}` with `h_k = (k + 1)^{-1/2}`
(`eq:v34-refresh-radius`). -/
def refreshRadius (vmin : ℝ) (k : ℕ) : ℝ :=
  min 1 (min (vmin / 8) (1 / Real.sqrt ((k : ℝ) + 1) / (64 * L0 vmin)))

lemma refreshRadius_pos {vmin : ℝ} (hvmin : 0 < vmin) (k : ℕ) : 0 < refreshRadius vmin k := by
  have := L0_pos hvmin
  unfold refreshRadius
  have hs : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

lemma refreshRadius_le_one (vmin : ℝ) (k : ℕ) : refreshRadius vmin k ≤ 1 := min_le_left _ _

lemma refreshRadius_le_vmin (vmin : ℝ) (k : ℕ) : refreshRadius vmin k ≤ vmin / 8 :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma refreshRadius_le_hyst (vmin : ℝ) (k : ℕ) :
    refreshRadius vmin k ≤ 1 / Real.sqrt ((k : ℝ) + 1) / (64 * L0 vmin) :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- `ρ_k ≥ min {1, v_min / 8, 1 / (64 L₀)} / (k + 1)`. -/
lemma refreshRadius_ge {vmin : ℝ} (hvmin : 0 < vmin) (k : ℕ) :
    min 1 (min (vmin / 8) (1 / (64 * L0 vmin))) / ((k : ℝ) + 1) ≤ refreshRadius vmin k := by
  have hL := L0_pos hvmin
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  set c := min 1 (min (vmin / 8) (1 / (64 * L0 vmin))) with hc
  have hc0 : 0 < c := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hck : c / ((k : ℝ) + 1) ≤ c := div_le_self hc0.le hk1
  have hs : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    rw [Real.sqrt_le_left hk0.le]
    nlinarith
  have hs0 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr hk0
  unfold refreshRadius
  refine le_min (hck.trans (min_le_left _ _)) (le_min
    (hck.trans ((min_le_right _ _).trans (min_le_left _ _))) ?_)
  have h1 : c ≤ 1 / (64 * L0 vmin) := (min_le_right _ _).trans (min_le_right _ _)
  calc c / ((k : ℝ) + 1) ≤ 1 / (64 * L0 vmin) / ((k : ℝ) + 1) :=
        div_le_div_of_nonneg_right h1 hk0.le
    _ ≤ 1 / (64 * L0 vmin) / Real.sqrt ((k : ℝ) + 1) :=
        div_le_div_of_nonneg_left (by positivity) hs0 hs
    _ = 1 / Real.sqrt ((k : ℝ) + 1) / (64 * L0 vmin) := by
        field_simp

/-- **Weighted form of `eq:v34-tail-summability` for the manuscript's radii.**  With the refresh radius
`ρ_k = min {1, v_min / 8, h_k / (64 L₀)}` and any batch radius `ρ > 0` (the manuscript takes
`ρ = min {1, v_min / 8, η / (16 L₀)}`), the explicit tail with a polynomially bounded weight
on the batch term is summable from every onset. -/
theorem tail_summabilityW_refreshRadius {X : Type*} [Fintype X] (m : ℕ) {v : X → ℝ}
    (hv : ∀ x, 0 < v x) {ρ vmin : ℝ} (hρ : 0 < ρ) (hvmin : 0 < vmin) {W : ℕ → ℝ} {cW : ℝ}
    (hcW : 0 ≤ cW) (hW : ∀ i, W i ≤ cW * (baseB i : ℝ) ^ 8) (j1 : ℕ) :
    (∑' j, if j1 ≤ j then ENNReal.ofReal (batchR m (j + 1)) *
      min 1 (explicitTailW W v ρ (refreshRadius vmin) (refH j)) else 0) ≠ ∞ := by
  have hL := L0_pos hvmin
  exact tail_summabilityW m hv hρ
    (lt_min one_pos (lt_min (by positivity) (by positivity)) :
      0 < min 1 (min (vmin / 8) (1 / (64 * L0 vmin))))
    (refreshRadius_le_one vmin) (refreshRadius_ge hvmin) hcW hW j1

/-- **`eq:v34-tail-summability` for the manuscript's radii and the tail `p_j` as displayed.** -/
theorem tail_summability_refreshRadius {X : Type*} [Fintype X] (m : ℕ) {v : X → ℝ}
    (hv : ∀ x, 0 < v x) {ρ vmin : ℝ} (hρ : 0 < ρ) (hvmin : 0 < vmin) (j1 : ℕ) :
    (∑' j, if j1 ≤ j then ENNReal.ofReal (batchR m (j + 1)) *
      min 1 (explicitTail v ρ (refreshRadius vmin) cumB baseB (refH j)) else 0) ≠ ∞ := by
  have hL := L0_pos hvmin
  exact tail_summability m hv hρ
    (lt_min one_pos (lt_min (by positivity) (by positivity)) :
      0 < min 1 (min (vmin / 8) (1 / (64 * L0 vmin))))
    (refreshRadius_le_one vmin) (refreshRadius_ge hvmin) j1

end

end JointRootCert
