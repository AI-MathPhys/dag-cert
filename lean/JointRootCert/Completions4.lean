/-
Completions, part 4: Lemma `lem:v34-concentration` (Explicit intrinsic-tape Gaussian
concentration), second claim.

* `Qtail_nonneg`, `Qtail_summable`: the explicit tail `Q_x(n, r)` is summable over the
  counts `n`.
* `gaussian_concentration_prefix`: for i.i.d. Gaussian observations, the probability that
  some prefix of length `n ≥ N` (in particular a data-dependent one) has mean or centered
  variance off by more than `r` is at most the finite sum `∑_{n ≥ N} Q_x(n, r)`.
-/
import JointRootCert.ChiSquare

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

lemma Qtail_nonneg (v : ℝ) (n : ℕ) (r : ℝ) : 0 ≤ Qtail v n r := by
  unfold Qtail
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)

/-- **The tail `Q_x(n, r)` is summable over the counts** (`v > 0`, `r > 0`): beyond the
onset `n₀` it is dominated by two geometric sequences. -/
theorem Qtail_summable {v r : ℝ} (hv : 0 < v) (hr : 0 < r) :
    Summable (fun n : ℕ => Qtail v n r) := by
  have ha : -(r ^ 2 / (2 * v)) < 0 := by
    have : 0 < r ^ 2 / (2 * v) := by positivity
    linarith
  have hb : -(r ^ 2 / (64 * v ^ 2)) < 0 := by
    have : 0 < r ^ 2 / (64 * v ^ 2) := by positivity
    linarith
  have h1 := (Real.summable_exp_nat_mul_iff.mpr (neg_one_lt_zero)).mul_left
    (Real.exp (n0 v r))
  have h2 := (Real.summable_exp_nat_mul_iff.mpr ha).mul_left 2
  have h3 := (Real.summable_exp_nat_mul_iff.mpr hb).mul_left
    (2 * Real.exp (r ^ 2 / (64 * v ^ 2)))
  refine Summable.of_nonneg_of_le (fun n => Qtail_nonneg v n r) (fun n => ?_)
    ((h1.add h2).add h3)
  have e1 : 0 ≤ Real.exp (n0 v r) * Real.exp ((n : ℝ) * -1) := by positivity
  have e2 : 0 ≤ 2 * Real.exp ((n : ℝ) * -(r ^ 2 / (2 * v))) := by positivity
  have e3 : 0 ≤ 2 * Real.exp (r ^ 2 / (64 * v ^ 2)) *
      Real.exp ((n : ℝ) * -(r ^ 2 / (64 * v ^ 2))) := by positivity
  unfold Qtail
  split_ifs with hn
  · have hle : (1 : ℝ) ≤ Real.exp (n0 v r) * Real.exp ((n : ℝ) * -1) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : (n : ℝ) ≤ (n0 v r : ℝ) := by exact_mod_cast hn.le
      linarith
    linarith
  · refine (min_le_right _ _).trans ?_
    have e4 : -(n * r ^ 2 / (2 * v)) = (n : ℝ) * -(r ^ 2 / (2 * v)) := by ring
    have e5 : Real.exp (-(((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2))) =
        Real.exp (r ^ 2 / (64 * v ^ 2)) * Real.exp ((n : ℝ) * -(r ^ 2 / (64 * v ^ 2))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e4, e5]
    linarith

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Explicit intrinsic-tape Gaussian concentration (Lemma `lem:v34-concentration`), both
claims, with no distributional hypothesis.**  `Y_0, Y_1, …` are independent `N(μ, v)`
observations, `v > 0`, and `0 < r ≤ v / 8`.  Then

* `Q(n, r)` is summable over `n`;
* for every `N`, the probability that for some `n ≥ N` the mean or the centered variance
  (denominator `n`) of the first `n` observations differs from `(μ, v)` by more than `r` is
  at most `∑_{n ≥ N} Q(n, r)`;
* the same bound holds for the prefix selected by any count `κ ≥ N`, whatever its
  dependence on the data (no measurability of `κ` is needed).

The manuscript states this with `N = n₀`. -/
theorem gaussian_concentration_prefix [IsProbabilityMeasure P] {v r μ : ℝ} (hv : 0 < v)
    (hr0 : 0 < r) (hrv : r ≤ v / 8) {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal μ v.toNNReal) P) (N : ℕ) :
    Summable (fun n : ℕ => Qtail v n r) ∧
    P {ω | ∃ n, N ≤ n ∧ (r < |(∑ i ∈ range n, Y i ω) / n - μ| ∨
        r < |(∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n - v|)} ≤
      ENNReal.ofReal (∑' n : ℕ, if N ≤ n then Qtail v n r else 0) ∧
    ∀ κ : Ω → ℕ, (∀ ω, N ≤ κ ω) →
      P {ω | r < |(∑ i ∈ range (κ ω), Y i ω) / (κ ω) - μ| ∨
        r < |(∑ i ∈ range (κ ω), (Y i ω - (∑ j ∈ range (κ ω), Y j ω) / (κ ω)) ^ 2) / (κ ω) - v|} ≤
      ENNReal.ofReal (∑' n : ℕ, if N ≤ n then Qtail v n r else 0) := by
  have hsum := Qtail_summable (v := v) (r := r) hv hr0
  have hnn : ∀ n : ℕ, 0 ≤ (if N ≤ n then Qtail v n r else 0) := fun n => by
    split_ifs
    · exact Qtail_nonneg v n r
    · exact le_rfl
  have hsumN : Summable (fun n : ℕ => if N ≤ n then Qtail v n r else 0) :=
    Summable.of_nonneg_of_le hnn (fun n => by
      split_ifs
      · exact le_rfl
      · exact Qtail_nonneg v n r) hsum
  have hmain : P {ω | ∃ n, N ≤ n ∧ (r < |(∑ i ∈ range n, Y i ω) / n - μ| ∨
        r < |(∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n - v|)} ≤
      ENNReal.ofReal (∑' n : ℕ, if N ≤ n then Qtail v n r else 0) := by
    have h := concentration_prefix P
      (fun n => {ω | r < |(∑ i ∈ range n, Y i ω) / n - μ| ∨
        r < |(∑ i ∈ range n, (Y i ω - (∑ j ∈ range n, Y j ω) / n) ^ 2) / n - v|})
      (fun n => Qtail v n r) N
      (fun n _ => gaussian_concentration_fixed hv hr0 hrv n hind hY)
    refine h.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsumN]
    refine tsum_congr (fun n => ?_)
    split_ifs
    · rfl
    · simp
  refine ⟨hsum, hmain, fun κ hκ => (measure_mono ?_).trans hmain⟩
  intro ω hω
  exact ⟨κ ω, hκ ω, hω⟩

end JointRootCert
