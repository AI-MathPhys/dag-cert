/-
Fixed-prior root-PUCT count and certification-horizon results
(Appendix "Certification Along Passive Graph-Search Trajectories",
subsection `app:root-puct-proofs`).

* Lemma `lem:v2counts` (Uniform finite-horizon count bounds):
  `RootPUCTTrace.count_le`, `RootPUCTTrace.count_lower_exact`, `RootPUCTTrace.count_lower`.
* Corollary `cor:v2countscales` (Fixed gaps versus a shrinking gap):
  `RootPUCTTrace.count_optimal_linear`, `RootPUCTTrace.count_shrinking_gap`.
* Lemma `lem:v2strict` (Nesting and actual endpoint changes):
  `rootPuctRadius_strictAntiOn`, `rootPuctLo_mono`, `rootPuctHi_anti`, `rootPuctHi_strict`, ...
* Theorem `thm:v2horizon` (A sharp certification-horizon scale):
  `stop3_leader_eq`, `stop3_radii`, `stop3_time_lower`, `stop3_exists_upper`,
  `v2horizon`.
* Proposition `prop:v2postcut` (Uniformly early retirement and changing revisits):
  `cut3_uniform`, `cut3_strict_change`, `v2postcut`.
* Theorem `thm:v2separation` (Root-PUCT work separation) and Corollary `cor:v2quarter`:
  the horizon substitution `g = m^{-α}` (`v2separation_horizon`) and the arithmetic that
  turns the operation-count accounting into the stated orders (`v2separation_work`,
  `v2quarter_work`).  The RAM cost model of the two monitors is not formalized; its
  accounting inequalities are hypotheses there.

The allocation rule is the one of `eq:v2puct`: after one observation of each of the `K`
arms, at every time `t ≥ K` (the number of observations already made) an arm maximizing
`μ i + λ i * √t / (1 + n i t)` is observed.  A trace is any pair (counts, selections)
consistent with this rule, so every statement holds for every tie-breaking choice.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset

/-! ### The allocation rule -/

section Counts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The root-PUCT index `I_i(t) = μ_i + λ_i √t / (1 + n_i(t))` (`eq:v2puct`). -/
noncomputable def rootPuctIndex (μ lam : ι → ℝ) (c : ι → ℕ) (t : ℕ) (i : ι) : ℝ :=
  μ i + lam i * Real.sqrt t / (1 + c i)

/-- A trace of the fixed-prior root-PUCT rule on deterministic-return arms: `n t i` is
the count of arm `i` when `t` observations have been made (meaningful for `t ≥ K`),
`sel t` is the arm observed next.  Any maximizer of the index may be selected. -/
structure RootPUCTTrace (μ lam : ι → ℝ) (n : ℕ → ι → ℕ) (sel : ℕ → ι) : Prop where
  init : ∀ i, n (Fintype.card ι) i = 1
  step : ∀ t, Fintype.card ι ≤ t → ∀ i, n (t + 1) i = n t i + if sel t = i then 1 else 0
  greedy : ∀ t, Fintype.card ι ≤ t →
    ∀ j, rootPuctIndex μ lam (n t) t j ≤ rootPuctIndex μ lam (n t) t (sel t)

/-- Count vectors of a trace built from a selection rule `next`. -/
def rootPuctState (next : ℕ → (ι → ℕ) → ι) (K : ℕ) : ℕ → ι → ℕ
  | 0 => fun _ => 1
  | k + 1 => fun i =>
      rootPuctState next K k i + if next (K + k) (rootPuctState next K k) = i then 1 else 0

/-- Traces exist: the model is not vacuous. -/
theorem exists_rootPUCTTrace [Nonempty ι] (μ lam : ι → ℝ) : ∃ n sel, RootPUCTTrace μ lam n sel := by
  classical
  have hex : ∀ (t : ℕ) (c : ι → ℕ), ∃ i, ∀ j, rootPuctIndex μ lam c t j ≤ rootPuctIndex μ lam c t i :=
    fun t c => Finite.exists_max (rootPuctIndex μ lam c t)
  choose next hnext using hex
  refine ⟨fun t => rootPuctState next (Fintype.card ι) (t - Fintype.card ι),
    fun t => next t (rootPuctState next (Fintype.card ι) (t - Fintype.card ι)), ?_, ?_, ?_⟩
  · intro i
    simp [rootPuctState]
  · intro t ht i
    have h1 : t + 1 - Fintype.card ι = (t - Fintype.card ι) + 1 := by omega
    have h2 : Fintype.card ι + (t - Fintype.card ι) = t := by omega
    simp only [h1, rootPuctState, h2]
  · intro t _ j
    exact hnext t _ j

variable {μ lam : ι → ℝ} {n : ℕ → ι → ℕ} {sel : ℕ → ι}

/-- The counts add up to the number of observations. -/
theorem RootPUCTTrace.sum_counts (h : RootPUCTTrace μ lam n sel) {t : ℕ}
    (ht : Fintype.card ι ≤ t) : ∑ i, n t i = t := by
  induction t, ht using Nat.le_induction with
  | base => simp [h.init, Finset.card_univ]
  | succ t ht ih =>
    simp only [h.step t ht, Finset.sum_add_distrib, ih]
    simp

theorem RootPUCTTrace.mono (h : RootPUCTTrace μ lam n sel) (i : ι) {s t : ℕ}
    (hs : Fintype.card ι ≤ s) (hst : s ≤ t) : n s i ≤ n t i := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih =>
    rw [h.step t (hs.trans hst)]
    exact ih.trans (Nat.le_add_right _ _)

theorem RootPUCTTrace.one_le (h : RootPUCTTrace μ lam n sel) (i : ι) {t : ℕ}
    (ht : Fintype.card ι ≤ t) : 1 ≤ n t i := by
  have := h.mono i le_rfl ht
  rwa [h.init] at this

theorem RootPUCTTrace.count_le_time (h : RootPUCTTrace μ lam n sel) (i : ι) {t : ℕ}
    (ht : Fintype.card ι ≤ t) : n t i ≤ t := by
  have := h.sum_counts ht
  calc n t i ≤ ∑ j, n t j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    _ = t := this

/-- **Lemma `lem:v2counts`, upper bound (`eq:v2uppercounts`).**  An arm whose reward is
below that of some other arm `star` has `n_i(t) ≤ max {1, λ_i √t / Δ_i}` for all `t ≥ K`,
with `Δ_i = μ star - μ i`. -/
theorem RootPUCTTrace.count_le (h : RootPUCTTrace μ lam n sel) (hlam : ∀ i, 0 < lam i) {i star : ι}
    (hgap : μ i < μ star) {t : ℕ} (ht : Fintype.card ι ≤ t) :
    (n t i : ℝ) ≤ max 1 (lam i * Real.sqrt t / (μ star - μ i)) := by
  have hΔ : 0 < μ star - μ i := sub_pos.mpr hgap
  induction t, ht using Nat.le_induction with
  | base => rw [h.init]; simp
  | succ t ht ih =>
    have hsq : Real.sqrt (t : ℝ) ≤ Real.sqrt ((t : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hmono : lam i * Real.sqrt (t : ℝ) / (μ star - μ i)
        ≤ lam i * Real.sqrt ((t : ℝ) + 1) / (μ star - μ i) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (hlam i).le) hΔ.le
    rw [h.step t ht]
    by_cases hsel : sel t = i
    · have hg := h.greedy t ht star
      rw [hsel] at hg
      unfold rootPuctIndex at hg
      have hpos : 0 ≤ lam star * Real.sqrt t / (1 + (n t star : ℝ)) :=
        div_nonneg (mul_nonneg (hlam star).le (Real.sqrt_nonneg _)) (by positivity)
      have hden : (0 : ℝ) < 1 + n t i := by positivity
      have h1 : μ star - μ i ≤ lam i * Real.sqrt t / (1 + (n t i : ℝ)) := by linarith
      rw [le_div_iff₀ hden] at h1
      have h2 : 1 + (n t i : ℝ) ≤ lam i * Real.sqrt t / (μ star - μ i) := by
        rw [le_div_iff₀ hΔ]
        linarith
      simp only [hsel, ite_true]
      push_cast
      exact le_max_of_le_right (by linarith)
    · simp only [hsel, ite_false, add_zero]
      push_cast
      exact ih.trans (max_le_max le_rfl hmono)

/-- **Lemma `lem:v2counts`, lower bound (`eq:v2lowerexact`).**  For every arm and every
`t ≥ 2K`, `n_i(t) + 1 > λ_i √⌊t/2⌋ / (Δ_i + 4Λ/√t)`. -/
theorem RootPUCTTrace.count_lower_exact (h : RootPUCTTrace μ lam n sel) (hlam : ∀ i, 0 < lam i)
    {star : ι} (hstar : ∀ j, μ j ≤ μ star) (i : ι) {t : ℕ} (ht : 2 * Fintype.card ι ≤ t) :
    lam i * Real.sqrt ((t / 2 : ℕ) : ℝ) / ((μ star - μ i) + 4 * (∑ j, lam j) / Real.sqrt t)
      < (n t i : ℝ) + 1 := by
  classical
  have hK : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = t / 2 := ⟨_, rfl⟩
  rw [← hs0]
  have hKs0 : Fintype.card ι ≤ s0 := by omega
  have hs0t : s0 ≤ t := by omega
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = ∑ j, lam j := ⟨_, rfl⟩
  rw [← hΛ]
  have hΛpos : 0 < Λ := by
    rw [hΛ]
    exact Finset.sum_pos (fun j _ => hlam j) ⟨i, mem_univ i⟩
  obtain ⟨η, hη⟩ : ∃ η, η = 4 * Λ / Real.sqrt t := ⟨_, rfl⟩
  rw [← hη]
  have hηpos : 0 < η := by rw [hη]; positivity
  have hΔ : 0 ≤ μ star - μ i := sub_nonneg.mpr (hstar i)
  by_contra hcon
  rw [not_lt, le_div_iff₀ (by linarith)] at hcon
  -- every index of arm `i` in the window is at least `μ_* + η`
  have hA : ∀ s, s0 ≤ s → s < t → μ star + η ≤ rootPuctIndex μ lam (n s) s i := by
    intro s hs hst
    have hmono : (n s i : ℝ) ≤ n t i := by exact_mod_cast h.mono i (hKs0.trans hs) hst.le
    have hsq : Real.sqrt (s0 : ℝ) ≤ Real.sqrt s := Real.sqrt_le_sqrt (by exact_mod_cast hs)
    have hden : (0 : ℝ) < 1 + n s i := by positivity
    have h3 : (μ star - μ i) + η ≤ lam i * Real.sqrt s / (1 + (n s i : ℝ)) := by
      rw [le_div_iff₀ hden]
      have h1 : ((μ star - μ i) + η) * (1 + (n s i : ℝ))
          ≤ ((n t i : ℝ) + 1) * ((μ star - μ i) + η) := by
        nlinarith [mul_le_mul_of_nonneg_left hmono (by linarith : 0 ≤ (μ star - μ i) + η)]
      have h2 : lam i * Real.sqrt (s0 : ℝ) ≤ lam i * Real.sqrt s :=
        mul_le_mul_of_nonneg_left hsq (hlam i).le
      linarith
    unfold rootPuctIndex
    linarith
  -- hence each arm gains at most `λ_j t / (4Λ)` in the window
  have hB : ∀ j u, s0 ≤ u → u ≤ t → (n u j : ℝ) - n s0 j ≤ lam j * t / (4 * Λ) := by
    intro j u hu
    induction u, hu using Nat.le_induction with
    | base =>
      intro _
      rw [sub_self]
      exact div_nonneg (mul_nonneg (hlam j).le htpos.le) (by positivity)
    | succ u hu ih =>
      intro hut
      have ih' := ih (by omega)
      rw [h.step u (hKs0.trans hu)]
      by_cases hsel : sel u = j
      · have hg := (hA u hu (by omega)).trans (h.greedy u (hKs0.trans hu) i)
        rw [hsel] at hg
        unfold rootPuctIndex at hg
        have hden : (0 : ℝ) < 1 + n u j := by positivity
        have h1 : η ≤ lam j * Real.sqrt u / (1 + (n u j : ℝ)) := by
          have := hstar j
          linarith
        rw [le_div_iff₀ hden] at h1
        have hsq : Real.sqrt (u : ℝ) ≤ Real.sqrt t :=
          Real.sqrt_le_sqrt (by exact_mod_cast (by omega : u ≤ t))
        have h2 : η * (1 + (n u j : ℝ)) ≤ lam j * Real.sqrt t :=
          h1.trans (mul_le_mul_of_nonneg_left hsq (hlam j).le)
        have hηs : η * Real.sqrt t = 4 * Λ := by rw [hη, div_mul_cancel₀ _ hsqt.ne']
        have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htpos.le
        have h3 : 4 * Λ * (1 + (n u j : ℝ)) ≤ lam j * t := by
          calc 4 * Λ * (1 + (n u j : ℝ)) = (η * (1 + (n u j : ℝ))) * Real.sqrt t := by
                rw [← hηs]; ring
            _ ≤ (lam j * Real.sqrt t) * Real.sqrt t := mul_le_mul_of_nonneg_right h2 hsqt.le
            _ = lam j * t := by rw [mul_assoc, hss]
        have h4 : 1 + (n u j : ℝ) ≤ lam j * t / (4 * Λ) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        simp only [hsel, ite_true]
        push_cast
        have : (0 : ℝ) ≤ n s0 j := Nat.cast_nonneg _
        linarith
      · simp only [hsel, ite_false, add_zero]
        exact ih'
  have hsum : ∑ j, ((n t j : ℝ) - n s0 j) ≤ ∑ j, lam j * t / (4 * Λ) :=
    Finset.sum_le_sum (fun j _ => hB j t hs0t le_rfl)
  have hl : ∑ j, ((n t j : ℝ) - n s0 j) = (t : ℝ) - s0 := by
    rw [Finset.sum_sub_distrib]
    have e1 := h.sum_counts (hKs0.trans hs0t)
    have e2 := h.sum_counts hKs0
    rw [← Nat.cast_sum, ← Nat.cast_sum, e1, e2]
  have hr : ∑ j, lam j * t / (4 * Λ) = (t : ℝ) / 4 := by
    rw [← Finset.sum_div, ← Finset.sum_mul, ← hΛ]
    have := hΛpos.ne'
    field_simp
  have hs0half : (s0 : ℝ) ≤ t / 2 := by
    rw [hs0]
    exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := t) (n := 2))
  rw [hl, hr] at hsum
  linarith

/-- **Lemma `lem:v2counts`, lower bound (`eq:v2lowercounts`).**  For every arm and every
`t ≥ 2K`, `n_i(t) + 1 > λ_i t / (√3 (Δ_i √t + 4Λ))`. -/
theorem RootPUCTTrace.count_lower (h : RootPUCTTrace μ lam n sel) (hlam : ∀ i, 0 < lam i)
    {star : ι} (hstar : ∀ j, μ j ≤ μ star) (i : ι) {t : ℕ} (ht : 2 * Fintype.card ι ≤ t) :
    lam i * t / (Real.sqrt 3 * ((μ star - μ i) * Real.sqrt t + 4 * ∑ j, lam j))
      < (n t i : ℝ) + 1 := by
  refine lt_of_le_of_lt ?_ (h.count_lower_exact hlam hstar i ht)
  have hK : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hΛpos : 0 < ∑ j, lam j := Finset.sum_pos (fun j _ => hlam j) ⟨i, mem_univ i⟩
  have hΔ : 0 ≤ μ star - μ i := sub_nonneg.mpr (hstar i)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hD : 0 < (μ star - μ i) * Real.sqrt t + 4 * ∑ j, lam j := by positivity
  have e : (μ star - μ i) + 4 * (∑ j, lam j) / Real.sqrt t
      = ((μ star - μ i) * Real.sqrt t + 4 * ∑ j, lam j) / Real.sqrt t := by
    field_simp
  have hts : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt htpos.le
  have hsr : Real.sqrt t ≤ Real.sqrt 3 * Real.sqrt ((t / 2 : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have : t ≤ 3 * (t / 2) := by omega
    exact_mod_cast this
  rw [e, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hD]
  have hnn : 0 ≤ lam i * Real.sqrt t *
      ((μ star - μ i) * Real.sqrt t + 4 * ∑ j, lam j) :=
    mul_nonneg (mul_nonneg (hlam i).le hs.le) hD.le
  have := mul_le_mul_of_nonneg_left hsr hnn
  calc lam i * (t : ℝ) * ((μ star - μ i) * Real.sqrt t + 4 * ∑ j, lam j)
      = lam i * (Real.sqrt t * Real.sqrt t)
          * ((μ star - μ i) * Real.sqrt t + 4 * ∑ j, lam j) := by rw [hts]
    _ = lam i * Real.sqrt t * ((μ star - μ i) * Real.sqrt t + 4 * ∑ j, lam j)
          * Real.sqrt t := by ring
    _ ≤ _ := this
    _ = _ := by ring

/-- **Corollary `cor:v2countscales`, optimal arm.**  An optimal arm has count
`n_i(t) + 1 > λ_i t / (4 √3 Λ)`, i.e. `Ω(t)`. -/
theorem RootPUCTTrace.count_optimal_linear (h : RootPUCTTrace μ lam n sel) (hlam : ∀ i, 0 < lam i)
    {star : ι} (hstar : ∀ j, μ j ≤ μ star) {i : ι} (hi : μ i = μ star) {t : ℕ}
    (ht : 2 * Fintype.card ι ≤ t) :
    lam i * t / (4 * Real.sqrt 3 * ∑ j, lam j) < (n t i : ℝ) + 1 := by
  have := h.count_lower hlam hstar i ht
  rw [hi, sub_self, zero_mul, zero_add] at this
  rwa [show 4 * Real.sqrt 3 * ∑ j, lam j = Real.sqrt 3 * (4 * ∑ j, lam j) by ring]

/-- **Corollary `cor:v2countscales`, `eq:v2shrinking`.**  For an arm of gap `g > 0`,
uniformly in `g`: whenever `g √t ≥ 4Λ` (and `t ≥ 2K`, which the lower bound of
`lem:v2counts` requires),
`λ_i √t / (2 √3 g) - 1 < n_i(t) ≤ max {1, λ_i √t / g}`.
With `g` fixed this is the `Θ(√t)` statement for fixed positive gaps. -/
theorem RootPUCTTrace.count_shrinking_gap (h : RootPUCTTrace μ lam n sel) (hlam : ∀ i, 0 < lam i)
    {star : ι} (hstar : ∀ j, μ j ≤ μ star) {i : ι} {g : ℝ} (hg : 0 < g)
    (hgi : μ star - μ i = g) {t : ℕ} (ht : 2 * Fintype.card ι ≤ t)
    (hgt : 4 * ∑ j, lam j ≤ g * Real.sqrt t) :
    lam i * Real.sqrt t / (2 * Real.sqrt 3 * g) - 1 < (n t i : ℝ) ∧
      (n t i : ℝ) ≤ max 1 (lam i * Real.sqrt t / g) := by
  have hK : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  constructor
  · have hl := h.count_lower hlam hstar i ht
    rw [hgi] at hl
    have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have hΛpos : 0 < ∑ j, lam j := Finset.sum_pos (fun j _ => hlam j) ⟨i, mem_univ i⟩
    have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hts : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt htpos.le
    have hle : lam i * Real.sqrt t / (2 * Real.sqrt 3 * g)
        ≤ lam i * t / (Real.sqrt 3 * (g * Real.sqrt t + 4 * ∑ j, lam j)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hnn : 0 ≤ lam i * Real.sqrt t * Real.sqrt 3 :=
        mul_nonneg (mul_nonneg (hlam i).le hs.le) h3.le
      have h1 : g * Real.sqrt t + 4 * ∑ j, lam j ≤ 2 * (g * Real.sqrt t) := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hnn
      calc lam i * Real.sqrt t * (Real.sqrt 3 * (g * Real.sqrt t + 4 * ∑ j, lam j))
          = lam i * Real.sqrt t * Real.sqrt 3 * (g * Real.sqrt t + 4 * ∑ j, lam j) := by ring
        _ ≤ lam i * Real.sqrt t * Real.sqrt 3 * (2 * (g * Real.sqrt t)) := h2
        _ = lam i * (Real.sqrt t * Real.sqrt t) * (2 * Real.sqrt 3 * g) := by ring
        _ = lam i * t * (2 * Real.sqrt 3 * g) := by rw [hts]
    linarith
  · have hgap : μ i < μ star := by linarith
    have := h.count_le hlam hgap (t := t) (by omega)
    rwa [hgi] at this

end Counts

/-! ### The confidence radius (`eq:v2radius`, Lemma `lem:v2strict`) -/

/-- `β_δ(n) = √(log (12 n² / δ) / (2 n))`, the radius with three terminals. -/
noncomputable def rootPuctRadius (δ x : ℝ) : ℝ := Real.sqrt (Real.log (12 * x ^ 2 / δ) / (2 * x))

lemma rootPuctRadius_nonneg (δ x : ℝ) : 0 ≤ rootPuctRadius δ x := Real.sqrt_nonneg _

lemma rootPuctRadius_eq_half_width (δ x : ℝ) : rootPuctRadius δ x = hoeffdingWidth 3 δ x / 2 := by
  unfold rootPuctRadius hoeffdingWidth
  rw [show (4 : ℝ) * 3 = 12 by norm_num]
  ring

private lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

private lemma two_lt_log_of_ge {X : ℝ} (hX : 8 ≤ X) : 2 < Real.log X := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  exact exp_two_lt_eight.trans_le hX

/-- **Lemma `lem:v2strict`, first assertion.**  `β_δ` strictly decreases on `[1, ∞)` for
`δ ∈ (0, 1/2]`. -/
theorem rootPuctRadius_strictAntiOn {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    StrictAntiOn (rootPuctRadius δ) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hc : 2 < Real.log (12 / δ) :=
    two_lt_log_of_ge (by rw [le_div_iff₀ hδ0]; linarith)
  have ex : ∀ z : ℝ, 0 < z →
      Real.log (12 * z ^ 2 / δ) = Real.log (12 / δ) + 2 * Real.log z := by
    intro z hz
    rw [show 12 * z ^ 2 / δ = 12 / δ * z ^ 2 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hr : Real.log (y / x) < y / x - 1 :=
    Real.log_lt_sub_one_of_pos (by positivity) (by
      intro h
      rw [div_eq_one_iff_eq hx0.ne'] at h
      exact hxy.ne' h)
  rw [Real.log_div hy0.ne' hx0.ne'] at hr
  have h1 : x * Real.log y < x * Real.log x + y - x := by
    have h2 := mul_lt_mul_of_pos_left hr hx0
    have h3 : x * (y / x - 1) = y - x := by field_simp
    rw [h3] at h2
    linarith
  show rootPuctRadius δ y < rootPuctRadius δ x
  unfold rootPuctRadius
  apply Real.sqrt_lt_sqrt
  · rw [ex y hy0]
    exact div_nonneg (by linarith) (by positivity)
  · rw [ex x hx0, ex y hy0, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hc),
      mul_nonneg (sub_pos.mpr hxy).le hlx]

lemma rootPuctRadius_anti {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) {j k : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ k) : rootPuctRadius δ k ≤ rootPuctRadius δ j :=
  (rootPuctRadius_strictAntiOn hδ0 hδ).antitoneOn
    (Set.mem_Ici.mpr (by exact_mod_cast hj))
    (Set.mem_Ici.mpr (by exact_mod_cast hj.trans hjk)) (by exact_mod_cast hjk)

/-- Clipped lower endpoint `L = max {0, μ - β_δ(k)}` after `k` observations. -/
noncomputable def rootPuctLo (δ μ : ℝ) (k : ℕ) : ℝ := max 0 (μ - rootPuctRadius δ k)

/-- Clipped upper endpoint `U = min {1, μ + β_δ(k)}` after `k` observations. -/
noncomputable def rootPuctHi (δ μ : ℝ) (k : ℕ) : ℝ := min 1 (μ + rootPuctRadius δ k)

section Endpoints

variable {δ μ : ℝ} {j k : ℕ}

lemma rootPuctLo_nonneg : 0 ≤ rootPuctLo δ μ k := le_max_left _ _

lemma rootPuctHi_le_one : rootPuctHi δ μ k ≤ 1 := min_le_left _ _

lemma rootPuctLo_le_mean (hμ : 0 ≤ μ) : rootPuctLo δ μ k ≤ μ :=
  max_le hμ (by linarith [rootPuctRadius_nonneg δ k])

lemma mean_le_puctHi (hμ : μ ≤ 1) : μ ≤ rootPuctHi δ μ k :=
  le_min hμ (by linarith [rootPuctRadius_nonneg δ k])

/-- **Lemma `lem:v2strict`, nesting.**  The clipped intervals lie in the initial interval
`[0,1]` (`rootPuctLo_nonneg`, `rootPuctHi_le_one`), contain the constant empirical mean
(`rootPuctLo_le_mean`, `mean_le_puctHi`) and are nested: lower endpoints do not decrease. -/
theorem rootPuctLo_mono (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hj : 1 ≤ j) (hjk : j ≤ k) :
    rootPuctLo δ μ j ≤ rootPuctLo δ μ k :=
  max_le_max le_rfl (by linarith [rootPuctRadius_anti hδ0 hδ hj hjk])

/-- Upper endpoints do not increase. -/
theorem rootPuctHi_anti (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hj : 1 ≤ j) (hjk : j ≤ k) :
    rootPuctHi δ μ k ≤ rootPuctHi δ μ j :=
  min_le_min le_rfl (by linarith [rootPuctRadius_anti hδ0 hδ hj hjk])

/-- **Lemma `lem:v2strict`, last assertion.**  Once the upper endpoint is below `1`,
every further observation strictly decreases it. -/
theorem rootPuctHi_strict (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hj : 1 ≤ j) (hjk : j < k)
    (h1 : rootPuctHi δ μ j < 1) : rootPuctHi δ μ k < rootPuctHi δ μ j := by
  have hlt : rootPuctRadius δ k < rootPuctRadius δ j :=
    (rootPuctRadius_strictAntiOn hδ0 hδ) (Set.mem_Ici.mpr (by exact_mod_cast hj))
      (Set.mem_Ici.mpr (by exact_mod_cast hj.trans hjk.le)) (by exact_mod_cast hjk)
  unfold rootPuctHi at h1 ⊢
  rcases le_total 1 (μ + rootPuctRadius δ j) with h | h
  · rw [min_eq_left h] at h1
    exact absurd h1 (lt_irrefl _)
  · rw [min_eq_right h]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

end Endpoints

/-- Radius inversion: `β_δ(x) ≤ ρ` once `x ≥ (8/ρ²) log (24 / (δ ρ²))`
(from `width_inversion` with `M = 3`). -/
theorem rootPuctRadius_le_of_count {δ ρ x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1 / 2) (hx : 8 / ρ ^ 2 * Real.log (24 / (δ * ρ ^ 2)) ≤ x) :
    rootPuctRadius δ x ≤ ρ := by
  have e1 : 32 / (2 * ρ) ^ 2 = 8 / ρ ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have e2 : 32 * 3 / (δ * (2 * ρ) ^ 2) = 24 / (δ * ρ ^ 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have := width_inversion (M := 3) (r := 2 * ρ) (by norm_num) hδ0 hδ1 (by linarith)
    (by linarith) (x := x) (by rw [e1, e2]; exact hx)
  rw [rootPuctRadius_eq_half_width]
  linarith

private lemma one_le_log_inv {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8) : 1 ≤ Real.log (1 / g) := by
  have h8 : 8 ≤ 1 / g := by
    rw [le_div_iff₀ hg]
    linarith
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  linarith

/-- `β_δ(x) ≤ g/2` once `x ≥ 32 (log (96/δ) + 2) · log (1/g) / g²`. -/
theorem rootPuctRadius_le_half_gap {δ g x : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g)
    (hg8 : g ≤ 1 / 8)
    (hx : 32 * (Real.log (96 / δ) + 2) * (Real.log (1 / g) / g ^ 2) ≤ x) :
    rootPuctRadius δ x ≤ g / 2 := by
  have hL := one_le_log_inv hg hg8
  have hD : 0 ≤ Real.log (96 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0]
    linarith)
  apply rootPuctRadius_le_of_count hδ0 (by linarith) (by linarith) (by linarith)
  have e1 : 8 / (g / 2) ^ 2 = 32 / g ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have e2 : 24 / (δ * (g / 2) ^ 2) = 96 / δ * (1 / g) ^ 2 := by
    field_simp
    ring
  have e3 : Real.log (96 / δ * (1 / g) ^ 2) = Real.log (96 / δ) + 2 * Real.log (1 / g) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e1, e2, e3]
  refine le_trans ?_ hx
  have hg2 : 0 < g ^ 2 := by positivity
  rw [div_mul_eq_mul_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hg2]
  nlinarith [mul_nonneg hD (sub_nonneg.mpr hL)]

/-- `β_δ(x) ≤ 1/8` once `x ≥ 512 log (1536/δ)`. -/
theorem rootPuctRadius_le_eighth {δ x : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hx : 512 * Real.log (1536 / δ) ≤ x) : rootPuctRadius δ x ≤ 1 / 8 := by
  apply rootPuctRadius_le_of_count hδ0 (by linarith) (by norm_num) (by norm_num)
  have e1 : (8 : ℝ) / (1 / 8) ^ 2 = 512 := by norm_num
  have e2 : 24 / (δ * (1 / 8 : ℝ) ^ 2) = 1536 / δ := by
    rw [div_eq_div_iff (by positivity) hδ0.ne']
    ring
  rw [e1, e2]
  exact hx

/-! ### The three-terminal instance (`eq:v2means`) -/

/-- Rewards of the root actions `A = 0`, `B = 1`, `C = 2`:
`μ_A = 3/4`, `μ_B = 3/4 - g`, `μ_C = 1/4`. -/
noncomputable def mu3 (g : ℝ) : Fin 3 → ℝ := ![3 / 4, 3 / 4 - g, 1 / 4]

@[simp] lemma mu3_zero (g : ℝ) : mu3 g 0 = 3 / 4 := rfl
@[simp] lemma mu3_one (g : ℝ) : mu3 g 1 = 3 / 4 - g := rfl
@[simp] lemma mu3_two (g : ℝ) : mu3 g 2 = 1 / 4 := rfl

private lemma fin3_cases (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ a, P a := by
  intro a
  fin_cases a
  exacts [h0, h1, h2]

lemma mu3_le {g : ℝ} (hg : 0 ≤ g) : ∀ a, mu3 g a ≤ 3 / 4 :=
  fin3_cases (fun a => mu3 g a ≤ 3 / 4)
    (by show mu3 g 0 ≤ 3 / 4; rw [mu3_zero])
    (by show mu3 g 1 ≤ 3 / 4; rw [mu3_one]; linarith)
    (by show mu3 g 2 ≤ 3 / 4; rw [mu3_two]; norm_num)

lemma mu3_nonneg {g : ℝ} (hg : g ≤ 1 / 8) : ∀ a, 0 ≤ mu3 g a :=
  fin3_cases (fun a => 0 ≤ mu3 g a)
    (by show 0 ≤ mu3 g 0; rw [mu3_zero]; norm_num)
    (by show 0 ≤ mu3 g 1; rw [mu3_one]; linarith)
    (by show 0 ≤ mu3 g 2; rw [mu3_two]; norm_num)

lemma mu3_le_of_ne {g : ℝ} (hg : g ≤ 1 / 8) : ∀ a, a ≠ 0 → mu3 g a ≤ 3 / 4 - g :=
  fin3_cases (fun a => a ≠ 0 → mu3 g a ≤ 3 / 4 - g)
    (fun h => absurd rfl h)
    (fun _ => by show mu3 g 1 ≤ 3 / 4 - g; rw [mu3_one])
    (fun _ => by show mu3 g 2 ≤ 3 / 4 - g; rw [mu3_two]; linarith)

/-- Canonical lower-bound leader: a maximizer of `L` of lowest index. -/
def RootPuctLeader (L : Fin 3 → ℝ) (a : Fin 3) : Prop :=
  (∀ b, L b ≤ L a) ∧ ∀ b, L b = L a → a ≤ b

/-- The standard stopping bit with leader `a`: `max_{b ≠ a} U b - L a ≤ ε`. -/
def RootPuctStops (L U : Fin 3 → ℝ) (ε : ℝ) (a : Fin 3) : Prop :=
  RootPuctLeader L a ∧ ∀ b, b ≠ a → U b - L a ≤ ε

/-- Lower endpoints of the three root actions at counts `c`. -/
noncomputable def L3 (δ g : ℝ) (c : Fin 3 → ℕ) (a : Fin 3) : ℝ := rootPuctLo δ (mu3 g a) (c a)

/-- Upper endpoints of the three root actions at counts `c`. -/
noncomputable def U3 (δ g : ℝ) (c : Fin 3 → ℕ) (a : Fin 3) : ℝ := rootPuctHi δ (mu3 g a) (c a)

/-- The check with `ε = g/2` succeeds at counts `c` with canonical leader `a`. -/
def Stop3 (δ g : ℝ) (c : Fin 3 → ℕ) (a : Fin 3) : Prop :=
  RootPuctStops (L3 δ g c) (U3 δ g c) (g / 2) a

section ThreeArm

variable {δ g : ℝ} {n : ℕ → Fin 3 → ℕ} {sel : ℕ → Fin 3} {c : Fin 3 → ℕ}

/-- **Theorem `thm:v2horizon`, recommendation.**  Any successful check recommends `A`. -/
theorem stop3_leader_eq (hg : 0 < g) (hg8 : g ≤ 1 / 8) {a : Fin 3} (hs : Stop3 δ g c a) :
    a = 0 := by
  by_contra ha
  have h := hs.2 0 (fun h => ha h.symm)
  have hU : (3 / 4 : ℝ) ≤ U3 δ g c 0 :=
    mean_le_puctHi (μ := mu3 g 0) (by rw [mu3_zero]; norm_num)
  have hL : L3 δ g c a ≤ 3 / 4 - g :=
    (rootPuctLo_le_mean (mu3_nonneg hg8 a)).trans (mu3_le_of_ne hg8 a ha)
  linarith

/-- **`eq:v2necessary`.**  At a successful check `β_δ(n_A) + β_δ(n_B) ≤ 3g/2`. -/
theorem stop3_radii (hg : 0 < g) (hg8 : g ≤ 1 / 8) (hs : Stop3 δ g c 0) :
    rootPuctRadius δ (c 0) + rootPuctRadius δ (c 1) ≤ 3 * g / 2 := by
  have h : min 1 (3 / 4 - g + rootPuctRadius δ (c 1)) - max 0 (3 / 4 - rootPuctRadius δ (c 0))
      ≤ g / 2 := hs.2 1 (by decide)
  have hA := rootPuctRadius_nonneg δ (c 0)
  have hB := rootPuctRadius_nonneg δ (c 1)
  have hl : max 0 (3 / 4 - rootPuctRadius δ (c 0)) ≤ 3 / 4 := max_le (by norm_num) (by linarith)
  rcases le_total 1 (3 / 4 - g + rootPuctRadius δ (c 1)) with h1 | h1
  · rw [min_eq_left h1] at h
    linarith
  · rw [min_eq_right h1] at h
    rcases le_total (3 / 4 - rootPuctRadius δ (c 0)) 0 with h2 | h2
    · rw [max_eq_left h2] at h
      linarith
    · rw [max_eq_right h2] at h
      linarith

/-- **`eq:v2nblow` and its consequence.**  A count `k ≥ 1` with `β_δ(k) ≤ 3g/2` satisfies
`k g² > 4/9` and `k ≥ (4/9) g⁻² log (1/g)`, for every `g > 0`. -/
theorem count_of_radius_le (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g)
    {k : ℕ} (hk : 1 ≤ k) (hβ : rootPuctRadius δ k ≤ 3 * g / 2) :
    4 / 9 < k * g ^ 2 ∧ 4 / 9 * Real.log (1 / g) / g ^ 2 ≤ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hg2 : 0 < g ^ 2 := by positivity
  have hX24 : 24 * (k : ℝ) ^ 2 ≤ 12 * (k : ℝ) ^ 2 / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (by linarith : (0 : ℝ) ≤ 12 - 24 * δ)]
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hlog2 : 2 < Real.log (12 * (k : ℝ) ^ 2 / δ) := two_lt_log_of_ge (by linarith)
  unfold rootPuctRadius at hβ
  rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)] at hβ
  have h49 : 4 / 9 < k * g ^ 2 := by nlinarith
  refine ⟨h49, ?_⟩
  have hkk : 4 / 9 ≤ (k : ℝ) * (k * g ^ 2) := by nlinarith
  have hXg : 1 / g ^ 2 ≤ 12 * (k : ℝ) ^ 2 / δ := by
    refine le_trans ?_ hX24
    rw [div_le_iff₀ hg2]
    nlinarith
  have hlogg : 2 * Real.log (1 / g) ≤ Real.log (12 * (k : ℝ) ^ 2 / δ) := by
    have e : 2 * Real.log (1 / g) = Real.log (1 / g ^ 2) := by
      rw [← one_div_pow, Real.log_pow]
      push_cast
      ring
    rw [e]
    exact Real.log_le_log (by positivity) hXg
  rw [div_le_iff₀ hg2]
  nlinarith

private lemma sqrt_three_le_two : Real.sqrt 3 ≤ 2 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

private lemma card_fin3_le {t : ℕ} (ht : 3 ≤ t) : Fintype.card (Fin 3) ≤ t := by
  rw [Fintype.card_fin]
  exact ht

private lemma sum_one_fin3 : (∑ _j : Fin 3, (1 : ℝ)) = 3 := by simp

/-- Count of the optimal arm `A`: `n_A(t) + 1 > t/24` for `t ≥ 6`. -/
theorem trace3_nA (hg : 0 ≤ g) (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel) {t : ℕ}
    (ht : 6 ≤ t) : (t : ℝ) / 24 < n t 0 + 1 := by
  have := h.count_optimal_linear (fun _ => one_pos) (star := 0)
    (fun j => by rw [mu3_zero]; exact mu3_le hg j) (i := 0) rfl (t := t)
    (by rw [Fintype.card_fin]; omega)
  rw [sum_one_fin3, one_mul] at this
  refine lt_of_le_of_lt ?_ this
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left sqrt_three_le_two (Nat.cast_nonneg (α := ℝ) t)]

/-- Count of the near-optimal arm `B`: `n_B(t) > √t/(4g) - 1` once `g √t ≥ 12`. -/
theorem trace3_nB (hg : 0 < g) (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel) {t : ℕ}
    (ht : 6 ≤ t) (hgt : 12 ≤ g * Real.sqrt t) : Real.sqrt t / (4 * g) - 1 < n t 1 := by
  have := (h.count_shrinking_gap (fun _ => one_pos) (star := 0)
    (fun j => by rw [mu3_zero]; exact mu3_le hg.le j) (i := 1) (g := g) hg
    (by rw [mu3_zero, mu3_one]; ring) (t := t) (by rw [Fintype.card_fin]; omega)
    (by rw [sum_one_fin3]; linarith)).1
  rw [one_mul] at this
  refine lt_of_le_of_lt (sub_le_sub_right ?_ _) this
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg (t : ℝ)) hg.le)
    (sub_nonneg.mpr sqrt_three_le_two)]

/-- Count of the fixed-gap arm `C`: `n_C(t) + 1 > t/(√t + 24)` for `t ≥ 6`. -/
theorem trace3_nC (hg : 0 ≤ g) (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel) {t : ℕ}
    (ht : 6 ≤ t) : (t : ℝ) / (Real.sqrt t + 24) < n t 2 + 1 := by
  have := h.count_lower (fun _ => one_pos) (star := 0)
    (fun j => by rw [mu3_zero]; exact mu3_le hg j) 2 (t := t)
    (by rw [Fintype.card_fin]; omega)
  rw [sum_one_fin3, one_mul, mu3_zero, mu3_two] at this
  refine lt_of_le_of_lt ?_ this
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sqrt_nonneg (t : ℝ)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) t)
    (by linarith : 0 ≤ 1 / 2 * Real.sqrt t + 12)) (sub_nonneg.mpr sqrt_three_le_two)]

/-- `n_C(t) + 1 > √t/2` once `√t ≥ 24`. -/
theorem trace3_nC' (hg : 0 ≤ g) (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel) {t : ℕ}
    (ht : 6 ≤ t) (hst : 24 ≤ Real.sqrt t) : Real.sqrt t / 2 < n t 2 + 1 := by
  refine lt_of_le_of_lt ?_ (trace3_nC hg h ht)
  have hts : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg t)
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-- Upper count bounds `n_B(t) ≤ max {1, √t/g}` and `n_C(t) ≤ max {1, 2√t}`. -/
theorem trace3_upper (hg : 0 < g) (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel) {t : ℕ}
    (ht : 3 ≤ t) :
    (n t 1 : ℝ) ≤ max 1 (Real.sqrt t / g) ∧ (n t 2 : ℝ) ≤ max 1 (2 * Real.sqrt t) := by
  constructor
  · have := h.count_le (fun _ => one_pos) (i := 1) (star := 0)
      (by rw [mu3_zero, mu3_one]; linarith) (card_fin3_le ht)
    rwa [one_mul, mu3_zero, mu3_one, show (3 / 4 : ℝ) - (3 / 4 - g) = g by ring] at this
  · have := h.count_le (fun _ => one_pos) (i := 2) (star := 0)
      (by rw [mu3_zero, mu3_two]; norm_num) (card_fin3_le ht)
    rw [one_mul, mu3_zero, mu3_two] at this
    refine this.trans (max_le_max le_rfl (le_of_eq ?_))
    ring

/-- A sufficient condition for a successful check with leader `A`. -/
theorem stop3_of_radii (hg : 0 < g) (hg8 : g ≤ 1 / 8) (hA : rootPuctRadius δ (c 0) ≤ g / 2)
    (hB : rootPuctRadius δ (c 1) ≤ g / 2) (hC : rootPuctRadius δ (c 2) ≤ 1 / 8) :
    Stop3 δ g c 0 := by
  have hLA : 3 / 4 - g / 2 ≤ L3 δ g c 0 := by
    show 3 / 4 - g / 2 ≤ max 0 (3 / 4 - rootPuctRadius δ (c 0))
    exact le_max_of_le_right (by linarith)
  have hLB : L3 δ g c 1 ≤ 3 / 4 - g := by
    show max 0 (3 / 4 - g - rootPuctRadius δ (c 1)) ≤ 3 / 4 - g
    exact max_le (by linarith) (by linarith [rootPuctRadius_nonneg δ (c 1)])
  have hLC : L3 δ g c 2 ≤ 1 / 4 := by
    show max 0 (1 / 4 - rootPuctRadius δ (c 2)) ≤ 1 / 4
    exact max_le (by norm_num) (by linarith [rootPuctRadius_nonneg δ (c 2)])
  have hUB : U3 δ g c 1 ≤ 3 / 4 - g / 2 := by
    show min 1 (3 / 4 - g + rootPuctRadius δ (c 1)) ≤ 3 / 4 - g / 2
    exact (min_le_right _ _).trans (by linarith)
  have hUC : U3 δ g c 2 ≤ 3 / 8 := by
    show min 1 (1 / 4 + rootPuctRadius δ (c 2)) ≤ 3 / 8
    exact (min_le_right _ _).trans (by linarith)
  refine ⟨⟨?_, fun b _ => Fin.zero_le b⟩, ?_⟩
  · exact fin3_cases (fun b => L3 δ g c b ≤ L3 δ g c 0) le_rfl
      (by show L3 δ g c 1 ≤ L3 δ g c 0; linarith)
      (by show L3 δ g c 2 ≤ L3 δ g c 0; linarith)
  · exact fin3_cases (fun b => b ≠ 0 → U3 δ g c b - L3 δ g c 0 ≤ g / 2)
      (fun h => absurd rfl h)
      (fun _ => by show U3 δ g c 1 - L3 δ g c 0 ≤ g / 2; linarith)
      (fun _ => by show U3 δ g c 2 - L3 δ g c 0 ≤ g / 2; linarith)

/-- **Theorem `thm:v2horizon`, lower bound.**  Every successful check time `t` satisfies
`t ≥ (16/81) g⁻² log² (1/g)`, for every `g ∈ (0, 1/8]`. -/
theorem stop3_time_lower (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel) {t : ℕ} (ht : 3 ≤ t)
    (hs : Stop3 δ g (n t) 0) : 16 / 81 * Real.log (1 / g) ^ 2 / g ^ 2 ≤ t := by
  have hk := h.one_le 1 (card_fin3_le ht)
  have hβ : rootPuctRadius δ (n t 1) ≤ 3 * g / 2 := by
    have := stop3_radii hg hg8 hs
    linarith [rootPuctRadius_nonneg δ (n t 0)]
  obtain ⟨h49, hkL⟩ := count_of_radius_le hδ0 hδ hg hk hβ
  have hg2 : 0 < g ^ 2 := by positivity
  have hg2' : g ^ 2 ≤ 1 / 64 := by nlinarith
  have hk1 : (1 : ℝ) < n t 1 := by
    by_contra hle
    rw [not_lt] at hle
    nlinarith [mul_le_mul_of_nonneg_right hle hg2.le]
  have hcnt := (trace3_upper hg h ht).1
  have hk2 : (n t 1 : ℝ) ≤ Real.sqrt t / g := by
    rcases le_max_iff.mp hcnt with h1 | h1
    · linarith
    · exact h1
  rw [le_div_iff₀ hg] at hk2
  rw [div_le_iff₀ hg2] at hkL
  have hL : 0 ≤ Real.log (1 / g) := Real.log_nonneg (by
    rw [le_div_iff₀ hg]
    linarith)
  have h1 : 4 / 9 * Real.log (1 / g) ≤ Real.sqrt t * g := by nlinarith
  have h2 : (4 / 9 * Real.log (1 / g)) ^ 2 ≤ (Real.sqrt t * g) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg t)] at h2
  rw [div_le_iff₀ hg2]
  nlinarith

/-- **Theorem `thm:v2horizon`, upper bound.**  There is `C_δ` such that for every
`g ∈ (0, 1/8]` and every trace the check succeeds, with leader `A`, at some time
`t ≤ C_δ g⁻² log² (1/g)`.  (The bound is uniform over the whole range of `g`.) -/
theorem stop3_exists_upper (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ, 0 < g → g ≤ 1 / 8 → ∀ (n : ℕ → Fin 3 → ℕ) (sel : ℕ → Fin 3),
      RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel →
      ∃ t : ℕ, 6 ≤ t ∧ (t : ℝ) ≤ C * Real.log (1 / g) ^ 2 / g ^ 2 ∧ Stop3 δ g (n t) 0 := by
  obtain ⟨E, hE⟩ : ∃ E, E = 32 * (Real.log (96 / δ) + 2) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = 512 * Real.log (1536 / δ) := ⟨_, rfl⟩
  have hD : 0 ≤ Real.log (96 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0]
    linarith)
  have hE64 : 64 ≤ E := by rw [hE]; linarith
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      rw [le_div_iff₀ hδ0]
      linarith))
  obtain ⟨R, hR⟩ : ∃ R, R = max (4 * (E + 1)) (F + 1) := ⟨_, rfl⟩
  have hR1 : 4 * (E + 1) ≤ R := by rw [hR]; exact le_max_left _ _
  have hR2 : F + 1 ≤ R := by rw [hR]; exact le_max_right _ _
  have hR0 : 0 < R := by linarith
  refine ⟨R ^ 2 + 1, by positivity, ?_⟩
  intro g hg hg8 n sel h
  have hL := one_le_log_inv hg hg8
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (1 / g) := ⟨_, rfl⟩
  rw [← hLdef] at hL ⊢
  have hg2 : 0 < g ^ 2 := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y, Y = L / g := ⟨_, rfl⟩
  have hY8 : 8 ≤ Y := by
    rw [hY, le_div_iff₀ hg]
    nlinarith
  obtain ⟨w, hw⟩ : ∃ w, w = L / g ^ 2 := ⟨_, rfl⟩
  have hwY : w ≤ Y ^ 2 := by
    rw [hw, hY, div_pow, div_le_div_iff_of_pos_right hg2]
    nlinarith
  have hw1 : 1 ≤ w := by
    rw [hw, le_div_iff₀ hg2]
    nlinarith
  have hYw : Y / g = w := by
    rw [hY, hw]
    field_simp
  have hY2 : 1 ≤ Y ^ 2 := by nlinarith
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = ⌈R ^ 2 * Y ^ 2⌉₊ := ⟨_, rfl⟩
  have ht_lo : R ^ 2 * Y ^ 2 ≤ t := by rw [htdef]; exact Nat.le_ceil _
  have ht_hi : (t : ℝ) < R ^ 2 * Y ^ 2 + 1 := by
    rw [htdef]
    exact Nat.ceil_lt_add_one (by positivity)
  have hRY : 0 ≤ R * Y := by positivity
  have hsqrt : R * Y ≤ Real.sqrt t := by
    rw [Real.le_sqrt hRY (Nat.cast_nonneg t)]
    linarith [mul_pow R Y 2]
  have hR260 : 260 ≤ R := by linarith
  have hRsq : 24 * (E + 1) ≤ R ^ 2 := by
    have := mul_le_mul hR1 (by linarith : (6 : ℝ) ≤ R) (by norm_num) hR0.le
    rw [sq]
    linarith
  have hRY8 : R * 8 ≤ R * Y := mul_le_mul_of_nonneg_left hY8 hR0.le
  have hRL : R * 1 ≤ R * L := mul_le_mul_of_nonneg_left hL hR0.le
  have hRY2 : R ^ 2 * 1 ≤ R ^ 2 * Y ^ 2 := mul_le_mul_of_nonneg_left hY2 (by positivity)
  have ht6 : 6 ≤ t := by
    have : (6 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  refine ⟨t, ht6, ?_, ?_⟩
  · have e : (R ^ 2 + 1) * L ^ 2 / g ^ 2 = (R ^ 2 + 1) * Y ^ 2 := by
      rw [hY, div_pow]
      ring
    rw [e]
    linarith
  · -- counts
    have hnA := trace3_nA hg.le h ht6
    have hgt : 12 ≤ g * Real.sqrt t := by
      have h1 : g * (R * Y) ≤ g * Real.sqrt t := mul_le_mul_of_nonneg_left hsqrt hg.le
      have h2 : g * (R * Y) = R * L := by
        rw [hY]
        field_simp
      linarith
    have hnB := trace3_nB hg h ht6 hgt
    have hst : 24 ≤ Real.sqrt t := by linarith
    have hnC := trace3_nC' hg.le h ht6 hst
    have hBw : R * w / 4 ≤ Real.sqrt t / (4 * g) := by
      have h1 : R * Y / (4 * g) ≤ Real.sqrt t / (4 * g) :=
        div_le_div_of_nonneg_right hsqrt (by positivity)
      have h2 : R * Y / (4 * g) = R * w / 4 := by
        rw [← hYw]
        field_simp
      linarith
    have hcA : E * w ≤ n t 0 := by
      have h1 : E * w ≤ E * Y ^ 2 := mul_le_mul_of_nonneg_left hwY (by linarith)
      have h2 : 24 * (E + 1) * Y ^ 2 ≤ R ^ 2 * Y ^ 2 :=
        mul_le_mul_of_nonneg_right hRsq (by positivity)
      linarith
    have hcB : E * w ≤ n t 1 := by
      have h1 : 4 * (E + 1) * w ≤ R * w := mul_le_mul_of_nonneg_right hR1 (by linarith)
      linarith
    have hcC : F ≤ n t 2 := by linarith
    rw [hE, hw, hLdef] at hcA hcB
    rw [hF] at hcC
    exact stop3_of_radii hg hg8 (rootPuctRadius_le_half_gap hδ0 hδ hg hg8 hcA)
      (rootPuctRadius_le_half_gap hδ0 hδ hg hg8 hcB) (rootPuctRadius_le_eighth hδ0 hδ hcC)

/-- **Theorem `thm:v2horizon` (A sharp certification-horizon scale).**  For fixed
`δ ∈ (0, 1/2]` there is a constant `C_δ` such that for every `g ∈ (0, 1/8]` and every
trace of the three-terminal procedure the first successful check time `τ` exists, its
recommendation is `A`, and, with `L = log (1/g)`,

* `(16/81) g⁻² L² ≤ τ ≤ C_δ g⁻² L²`,
* `L / (18 g) - 1 < n_C(τ) ≤ 2 √C_δ · L / g`.

These explicit two-sided bounds hold on the whole range of `g`, hence give the
`Θ_δ` statements `eq:v2horizonscale` as `g ↓ 0`. -/
theorem v2horizon (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ, 0 < g → g ≤ 1 / 8 → ∀ (n : ℕ → Fin 3 → ℕ) (sel : ℕ → Fin 3),
      RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel →
      ∃ τ : ℕ, 3 ≤ τ ∧ Stop3 δ g (n τ) 0 ∧
        (∀ s a, 3 ≤ s → s < τ → ¬ Stop3 δ g (n s) a) ∧
        (∀ a, Stop3 δ g (n τ) a → a = 0) ∧
        16 / 81 * Real.log (1 / g) ^ 2 / g ^ 2 ≤ τ ∧
        (τ : ℝ) ≤ C * Real.log (1 / g) ^ 2 / g ^ 2 ∧
        Real.log (1 / g) / (18 * g) < n τ 2 + 1 ∧
        (n τ 2 : ℝ) ≤ 2 * Real.sqrt C * Real.log (1 / g) / g := by
  classical
  obtain ⟨C, hC, hup⟩ := stop3_exists_upper hδ0 hδ
  refine ⟨C, hC, ?_⟩
  intro g hg hg8 n sel h
  obtain ⟨t, ht6, htC, hst⟩ := hup g hg hg8 n sel h
  have hex : ∃ s, 3 ≤ s ∧ ∃ a, Stop3 δ g (n s) a := ⟨t, by omega, 0, hst⟩
  obtain ⟨hτ3, a, ha⟩ := Nat.find_spec hex
  have ha0 : a = 0 := stop3_leader_eq hg hg8 ha
  rw [ha0] at ha
  have hmin : ∀ s a, 3 ≤ s → s < Nat.find hex → ¬ Stop3 δ g (n s) a :=
    fun s a hs hlt hstop => Nat.find_min hex hlt ⟨hs, a, hstop⟩
  have hτt : Nat.find hex ≤ t := Nat.find_min' hex ⟨by omega, 0, hst⟩
  have hlow := stop3_time_lower hδ0 hδ hg hg8 h hτ3 ha
  have hL := one_le_log_inv hg hg8
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (1 / g) := ⟨_, rfl⟩
  rw [← hLdef] at hL hlow htC ⊢
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = Nat.find hex := ⟨_, rfl⟩
  rw [← hτdef] at hτ3 ha hmin hτt hlow
  have hg2 : 0 < g ^ 2 := by positivity
  have hτC : (τ : ℝ) ≤ C * L ^ 2 / g ^ 2 := le_trans (by exact_mod_cast hτt) htC
  -- `q = (4/9) L / g ≤ √τ`
  have hq : 4 / 9 * (L / g) ≤ Real.sqrt τ := by
    rw [Real.le_sqrt (by positivity) (Nat.cast_nonneg τ)]
    refine le_trans (le_of_eq ?_) hlow
    rw [mul_pow, div_pow]
    ring
  have hLg : 8 ≤ L / g := by
    rw [le_div_iff₀ hg]
    nlinarith
  have hs32 : 32 / 9 ≤ Real.sqrt τ := by linarith
  have hss : Real.sqrt τ * Real.sqrt τ = (τ : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg τ)
  have hτ6 : 6 ≤ τ := by
    have : (6 : ℝ) ≤ τ := by nlinarith
    exact_mod_cast this
  refine ⟨τ, hτ3, ha, hmin, fun a ha' => stop3_leader_eq hg hg8 ha', hlow, hτC, ?_, ?_⟩
  · have hnC := trace3_nC hg.le h hτ6
    have h1 : Real.sqrt τ / 8 ≤ (τ : ℝ) / (Real.sqrt τ + 24) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have h2 : L / (18 * g) ≤ Real.sqrt τ / 8 := by
      have e : L / (18 * g) = 4 / 9 * (L / g) / 8 := by
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_right hq (by norm_num)
    linarith
  · have hup2 := (trace3_upper hg h hτ3).2
    have h1 : (n τ 2 : ℝ) ≤ 2 * Real.sqrt τ := by
      rcases le_max_iff.mp hup2 with h1 | h1
      · linarith
      · exact h1
    have hLg0 : 0 ≤ L / g := by linarith
    have h2 : Real.sqrt τ ≤ Real.sqrt C * (L / g) := by
      have e : C * L ^ 2 / g ^ 2 = C * (L / g) ^ 2 := by
        rw [div_pow]
        ring
      rw [e] at hτC
      calc Real.sqrt τ ≤ Real.sqrt (C * (L / g) ^ 2) := Real.sqrt_le_sqrt hτC
        _ = Real.sqrt C * (L / g) := by rw [Real.sqrt_mul hC.le, Real.sqrt_sq hLg0]
    calc (n τ 2 : ℝ) ≤ 2 * Real.sqrt τ := h1
      _ ≤ 2 * (Real.sqrt C * (L / g)) := by linarith
      _ = 2 * Real.sqrt C * L / g := by ring

/-! ### Proposition `prop:v2postcut` -/

/-- The retirement condition for `C`: `U_C < max {L_A, L_B}`. -/
def Cut3 (δ g : ℝ) (c : Fin 3 → ℕ) : Prop := U3 δ g c 2 < max (L3 δ g c 0) (L3 δ g c 1)

/-- **Proposition `prop:v2postcut`, uniform cut time.**  There is `T_δ`, independent of
`g ∈ (0, 1/8]` and of the trace, at which the retirement condition for `C` holds; hence
the first such time is at most `T_δ`. -/
theorem cut3_uniform (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ T : ℕ, 6 ≤ T ∧ ∀ g : ℝ, 0 < g → g ≤ 1 / 8 → ∀ (n : ℕ → Fin 3 → ℕ) (sel : ℕ → Fin 3),
      RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel → Cut3 δ g (n T) := by
  obtain ⟨F, hF⟩ : ∃ F, F = 512 * Real.log (1536 / δ) := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      rw [le_div_iff₀ hδ0]
      linarith))
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = ⌈(2 * F + 50) ^ 2⌉₊ := ⟨_, rfl⟩
  have hT_lo : (2 * F + 50) ^ 2 ≤ T := by rw [hT]; exact Nat.le_ceil _
  have hsqrt : 2 * F + 50 ≤ Real.sqrt T := by
    rw [Real.le_sqrt (by linarith) (Nat.cast_nonneg T)]
    exact hT_lo
  have hT6 : 6 ≤ T := by
    have : (6 : ℝ) ≤ T := by nlinarith
    exact_mod_cast this
  refine ⟨T, hT6, ?_⟩
  intro g hg hg8 n sel h
  have hnA := trace3_nA hg.le h hT6
  have hnC := trace3_nC' hg.le h hT6 (by linarith)
  have hcA : F ≤ n T 0 := by nlinarith
  have hcC : F ≤ n T 2 := by linarith
  rw [hF] at hcA hcC
  have hA := rootPuctRadius_le_eighth hδ0 hδ hcA
  have hC := rootPuctRadius_le_eighth hδ0 hδ hcC
  have hLA : 5 / 8 ≤ L3 δ g (n T) 0 := by
    show 5 / 8 ≤ max 0 (3 / 4 - rootPuctRadius δ (n T 0))
    exact le_max_of_le_right (by linarith)
  have hUC : U3 δ g (n T) 2 ≤ 3 / 8 := by
    show min 1 (1 / 4 + rootPuctRadius δ (n T 2)) ≤ 3 / 8
    exact (min_le_right _ _).trans (by linarith)
  exact lt_max_of_lt_left (by linarith)

/-- **Proposition `prop:v2postcut`, changing revisits.**  After a time `tc` at which the
retirement condition holds, every observation of `C` strictly decreases `U_C`. -/
theorem cut3_strict_change (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel) {tc s : ℕ} (htc : 3 ≤ tc)
    (hcut : Cut3 δ g (n tc)) (hs : tc ≤ s) (hsel : sel s = 2) :
    U3 δ g (n (s + 1)) 2 < U3 δ g (n s) 2 := by
  have hKtc := card_fin3_le htc
  have hLA : L3 δ g (n tc) 0 ≤ 3 / 4 :=
    (rootPuctLo_le_mean (mu3_nonneg hg8 0)).trans (mu3_le hg.le 0)
  have hLB : L3 δ g (n tc) 1 ≤ 3 / 4 :=
    (rootPuctLo_le_mean (mu3_nonneg hg8 1)).trans (mu3_le hg.le 1)
  have hU : U3 δ g (n tc) 2 < 1 := by
    have : max (L3 δ g (n tc) 0) (L3 δ g (n tc) 1) ≤ 3 / 4 := max_le hLA hLB
    unfold Cut3 at hcut
    linarith
  have hUs : U3 δ g (n s) 2 < 1 :=
    lt_of_le_of_lt (rootPuctHi_anti hδ0 hδ (h.one_le 2 hKtc) (h.mono 2 hKtc hs)) hU
  have hstep : n (s + 1) 2 = n s 2 + 1 := by
    rw [h.step s (hKtc.trans hs), hsel]
    simp
  show rootPuctHi δ (mu3 g 2) (n (s + 1) 2) < rootPuctHi δ (mu3 g 2) (n s 2)
  rw [hstep]
  exact rootPuctHi_strict hδ0 hδ (h.one_le 2 (hKtc.trans hs)) (Nat.lt_succ_self _) hUs

/-- **Proposition `prop:v2postcut` (Uniformly early retirement and changing revisits).**
For fixed `δ ∈ (0, 1/2]` there are `T_δ`, `g₀ > 0` and `C > 0` such that for every
`g ∈ (0, 1/8]` and every trace: the first cut time `t_cut` exists and is at most `T_δ`;
the first successful check time `τ` exists and obeys the bounds of `v2horizon`;
`t_cut < τ` whenever `g ≤ g₀`; the number `H = n_C(τ) - n_C(t_cut)` satisfies
`L/(18 g) - 1 - T_δ < H ≤ 2 √C · L/g` with `L = log (1/g)`; and every observation of `C` from `t_cut` on strictly decreases `U_C`. -/
theorem v2postcut (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ (T : ℕ) (g0 C : ℝ), 0 < g0 ∧ 0 < C ∧
      ∀ g : ℝ, 0 < g → g ≤ 1 / 8 → ∀ (n : ℕ → Fin 3 → ℕ) (sel : ℕ → Fin 3),
      RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel →
      ∃ tc τ : ℕ, 3 ≤ tc ∧ tc ≤ T ∧ Cut3 δ g (n tc) ∧
        (∀ s, 3 ≤ s → s < tc → ¬ Cut3 δ g (n s)) ∧
        3 ≤ τ ∧ Stop3 δ g (n τ) 0 ∧ (∀ s a, 3 ≤ s → s < τ → ¬ Stop3 δ g (n s) a) ∧
        (g ≤ g0 → tc < τ) ∧
        16 / 81 * Real.log (1 / g) ^ 2 / g ^ 2 ≤ τ ∧
        (τ : ℝ) ≤ C * Real.log (1 / g) ^ 2 / g ^ 2 ∧
        Real.log (1 / g) / (18 * g) - 1 - T < (n τ 2 : ℝ) - n tc 2 ∧
        (n τ 2 : ℝ) - n tc 2 ≤ 2 * Real.sqrt C * Real.log (1 / g) / g ∧
        (∀ s, tc ≤ s → sel s = 2 → U3 δ g (n (s + 1)) 2 < U3 δ g (n s) 2) := by
  classical
  obtain ⟨C, hC, hhor⟩ := v2horizon hδ0 hδ
  obtain ⟨T, hT6, hcutT⟩ := cut3_uniform hδ0 hδ
  have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  refine ⟨T, 1 / (3 * ((T : ℝ) + 1)), C, by positivity, hC, ?_⟩
  intro g hg hg8 n sel h
  obtain ⟨τ, hτ3, hstop, hmin, -, hlow, hτC, hnClo, hnChi⟩ := hhor g hg hg8 n sel h
  have hex : ∃ s, 3 ≤ s ∧ Cut3 δ g (n s) := ⟨T, by omega, hcutT g hg hg8 n sel h⟩
  obtain ⟨htc3, hcut⟩ := Nat.find_spec hex
  have htcT : Nat.find hex ≤ T := Nat.find_min' hex ⟨by omega, hcutT g hg hg8 n sel h⟩
  have hcmin : ∀ s, 3 ≤ s → s < Nat.find hex → ¬ Cut3 δ g (n s) :=
    fun s hs hlt hc => Nat.find_min hex hlt ⟨hs, hc⟩
  obtain ⟨tc, htcdef⟩ : ∃ tc, tc = Nat.find hex := ⟨_, rfl⟩
  rw [← htcdef] at htc3 hcut htcT hcmin
  have hL := one_le_log_inv hg hg8
  have hntc : (n tc 2 : ℝ) ≤ T := by
    have := (h.count_le_time 2 (card_fin3_le htc3)).trans htcT
    exact_mod_cast this
  have hntc0 : (0 : ℝ) ≤ n tc 2 := Nat.cast_nonneg _
  refine ⟨tc, τ, htc3, htcT, hcut, hcmin, hτ3, hstop, hmin, ?_, hlow, hτC, ?_, ?_, ?_⟩
  · intro hg0
    have hga : g * (3 * ((T : ℝ) + 1)) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hg0
    have hg2 : 0 < g ^ 2 := by positivity
    rw [div_le_iff₀ hg2] at hlow
    have hL2 : 1 ≤ Real.log (1 / g) ^ 2 := by nlinarith
    have h1 : (g * (3 * ((T : ℝ) + 1))) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) hga
    have h2 : (τ : ℝ) * (g * (3 * ((T : ℝ) + 1))) ^ 2 ≤ τ :=
      mul_le_of_le_one_right (Nat.cast_nonneg τ) h1
    have h3 : 16 / 81 * (3 * ((T : ℝ) + 1)) ^ 2 ≤ τ := by
      have h4 : 16 / 81 * Real.log (1 / g) ^ 2 * (3 * ((T : ℝ) + 1)) ^ 2
          ≤ τ * g ^ 2 * (3 * ((T : ℝ) + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_right hlow (by positivity)
      have h5 : 16 / 81 * (3 * ((T : ℝ) + 1)) ^ 2
          ≤ 16 / 81 * Real.log (1 / g) ^ 2 * (3 * ((T : ℝ) + 1)) ^ 2 := by
        have : (0 : ℝ) ≤ 16 / 81 * (3 * ((T : ℝ) + 1)) ^ 2 := by positivity
        nlinarith
      have h6 : (τ : ℝ) * g ^ 2 * (3 * ((T : ℝ) + 1)) ^ 2
          = τ * (g * (3 * ((T : ℝ) + 1))) ^ 2 := by ring
      linarith
    have h7 : (T : ℝ) < τ := by nlinarith
    have : T < τ := by exact_mod_cast h7
    omega
  · linarith
  · linarith
  · intro s hs hsel
    exact cut3_strict_change hδ0 hδ hg hg8 h htc3 hcut hs hsel

end ThreeArm

/-! ### Theorem `thm:v2separation` and Corollary `cor:v2quarter` -/

section Separation

variable {δ : ℝ}

/-- **Theorem `thm:v2separation`, `eq:v2taum` and `eq:v2hm`.**  Substituting
`g = m^{-α}` (any `α > 0`, any real `m` with `m^α ≥ 8`) in `thm:v2horizon` and
`prop:v2postcut`: the first successful check time `τ` and the number
`H = n_C(τ) - n_C(t_cut)` of post-cut observations of `C` satisfy

* `(16/81) α² m^{2α} log² m ≤ τ ≤ C α² m^{2α} log² m`,
* `α m^α log m / 18 - 1 - T_δ < H ≤ 2 √C α m^α log m`,

the cut precedes certification once `m^α ≥ 1/g₀`, the recommendation is `A`, and every
post-cut observation of `C` strictly changes `U_C`.  The root observation process on the
graph of `sec:v2separation` is the three-terminal process, because every path below `C`
reaches the single terminal `z`; that identification, and the identity of the two
monitors' leader-and-stop outputs, are not part of this statement. -/
theorem v2separation_horizon (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ (T : ℕ) (g0 C : ℝ), 0 < g0 ∧ 0 < C ∧ ∀ α : ℝ, 0 < α → ∀ m : ℝ, 0 < m → 8 ≤ m ^ α →
      ∀ (n : ℕ → Fin 3 → ℕ) (sel : ℕ → Fin 3),
      RootPUCTTrace (mu3 (m ^ (-α))) (fun _ => (1 : ℝ)) n sel →
      ∃ tc τ : ℕ, 3 ≤ tc ∧ tc ≤ T ∧ Cut3 δ (m ^ (-α)) (n tc) ∧
        (∀ s, 3 ≤ s → s < tc → ¬ Cut3 δ (m ^ (-α)) (n s)) ∧
        3 ≤ τ ∧ Stop3 δ (m ^ (-α)) (n τ) 0 ∧
        (∀ s a, 3 ≤ s → s < τ → ¬ Stop3 δ (m ^ (-α)) (n s) a) ∧
        (1 / g0 ≤ m ^ α → tc < τ) ∧
        16 / 81 * α ^ 2 * m ^ (2 * α) * Real.log m ^ 2 ≤ τ ∧
        (τ : ℝ) ≤ C * α ^ 2 * m ^ (2 * α) * Real.log m ^ 2 ∧
        α * m ^ α * Real.log m / 18 - 1 - T < (n τ 2 : ℝ) - n tc 2 ∧
        (n τ 2 : ℝ) - n tc 2 ≤ 2 * Real.sqrt C * α * m ^ α * Real.log m ∧
        (∀ s, tc ≤ s → sel s = 2 →
          U3 δ (m ^ (-α)) (n (s + 1)) 2 < U3 δ (m ^ (-α)) (n s) 2) := by
  obtain ⟨T, g0, C, hg0, hC, H⟩ := v2postcut hδ0 hδ
  refine ⟨T, g0, C, hg0, hC, ?_⟩
  intro α hα m hm hm8 n sel h
  have h2α : m ^ (2 * α) = (m ^ α) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hm.le, Real.rpow_two]
  have hga : m ^ (-α) = (m ^ α)⁻¹ := Real.rpow_neg hm.le α
  have hlog : Real.log (m ^ α) = α * Real.log m := Real.log_rpow hm α
  obtain ⟨a, ha⟩ : ∃ a, a = m ^ α := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = m ^ (-α) := ⟨_, rfl⟩
  rw [← ha] at hm8 h2α hga hlog ⊢
  rw [← hg] at h hga ⊢
  have ha0 : 0 < a := by linarith
  have hgpos : 0 < g := by rw [hga]; positivity
  have hg8 : g ≤ 1 / 8 := by
    rw [hga, one_div]
    exact inv_anti₀ (by norm_num) hm8
  have hL : Real.log (1 / g) = α * Real.log m := by
    rw [hga, one_div, inv_inv, hlog]
  obtain ⟨tc, τ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    H g hgpos hg8 n sel h
  rw [hL] at h9 h10 h11 h12
  refine ⟨tc, τ, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, ?_, ?_, ?_, h13⟩
  · intro hle
    apply h8
    rw [hga]
    rw [one_div] at hle
    exact inv_le_of_inv_le₀ hg0 hle
  · refine le_trans (le_of_eq ?_) h9
    rw [h2α, hga]
    field_simp
  · refine le_trans h10 (le_of_eq ?_)
    rw [h2α, hga]
    field_simp
  · refine lt_of_eq_of_lt ?_ h11
    rw [hga]
    field_simp
  · refine le_trans h12 (le_of_eq ?_)
    rw [hga]
    field_simp

/-- **Theorem `thm:v2separation`, `eq:v2wselective` and `eq:v2wfull`: the arithmetic.**
Let `0 < α < 1/2`, `r = (1 - 2α)/2` and `m ≥ 3`.  Assume the horizon bounds
`τ ≤ Cτ m^{2α} log² m`, `n_C(τ) ≤ Cn m^α log m`, `H ≥ cH m^α log m`
(supplied by `v2separation_horizon`) and the operation-count accounting of the proof:

* `W_selective ≤ c₁ (m + τ + n_C(τ) log (2m))` (`eq:v2fullaccounting`),
* `m H ≤ W_full ≤ c₂ (m + τ + m n_C(τ) + n_C(τ) log (2m))`.

Then `W_selective ≤ c₁ (1 + (Cτ + 2 Cn)/r²) m` and
`cH m^{1+α} log m ≤ W_full ≤ c₂ (1 + (Cτ + 2 Cn)/r² + Cn) m^{1+α} log m`.
The accounting inequalities are hypotheses: the RAM cost model of the two monitors is
not formalized.  (The matching bound `W_selective = Ω(m)` is the initialization cost,
itself an accounting hypothesis.) -/
theorem v2separation_work {α m τ nC H Wsel Wfull Cτ Cn cH c1 c2 : ℝ} (hα0 : 0 < α)
    (hα : α < 1 / 2) (hm : 3 ≤ m) (hCτ : 0 ≤ Cτ) (hCn : 0 ≤ Cn)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hn0 : 0 ≤ nC)
    (hτ : τ ≤ Cτ * m ^ (2 * α) * Real.log m ^ 2) (hnC : nC ≤ Cn * m ^ α * Real.log m)
    (hH : cH * m ^ α * Real.log m ≤ H)
    (hsel : Wsel ≤ c1 * (m + τ + nC * Real.log (2 * m)))
    (hfull_lo : m * H ≤ Wfull)
    (hfull_up : Wfull ≤ c2 * (m + τ + m * nC + nC * Real.log (2 * m))) :
    Wsel ≤ c1 * (1 + (Cτ + 2 * Cn) / ((1 - 2 * α) / 2) ^ 2) * m ∧
      cH * m ^ (1 + α) * Real.log m ≤ Wfull ∧
      Wfull ≤ c2 * (1 + (Cτ + 2 * Cn) / ((1 - 2 * α) / 2) ^ 2 + Cn)
        * m ^ (1 + α) * Real.log m := by
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  obtain ⟨r, hr⟩ : ∃ r, r = (1 - 2 * α) / 2 := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := by rw [hr]; linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log m := ⟨_, rfl⟩
  rw [← hℓ] at hτ hnC hH ⊢
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le hm0]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = m ^ α := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = m ^ (2 * α) := ⟨_, rfl⟩
  have hX : m ^ (1 + α) = m * a := by
    rw [ha, Real.rpow_add hm0, Real.rpow_one]
  rw [hX]
  rw [← ha] at hnC hH
  rw [← hb] at hτ
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Real.one_le_rpow hm1 hα0.le
  have hab : a ≤ b := by
    rw [ha, hb]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hb0 : 0 < b := by linarith
  -- `log m ≤ m^r / r`, hence `b ℓ² ≤ m / r²`
  have hlogr : ℓ ≤ m ^ r / r := by
    rw [hℓ]
    exact Real.log_le_rpow_div hm0.le hr0
  have hmr0 : 0 < m ^ r := Real.rpow_pos_of_pos hm0 r
  have hbr : b * (m ^ r) ^ 2 = m := by
    rw [hb, ← Real.rpow_two, ← Real.rpow_mul hm0.le, ← Real.rpow_add hm0]
    have : 2 * α + r * 2 = 1 := by rw [hr]; ring
    rw [this, Real.rpow_one]
  obtain ⟨K, hK⟩ : ∃ K, K = 1 / r ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hbℓ : b * ℓ ^ 2 ≤ K * m := by
    have h1 : ℓ ^ 2 ≤ (m ^ r / r) ^ 2 := pow_le_pow_left₀ (by linarith) hlogr 2
    have h2 : b * ℓ ^ 2 ≤ b * (m ^ r / r) ^ 2 := mul_le_mul_of_nonneg_left h1 hb0.le
    have h3 : b * (m ^ r / r) ^ 2 = K * m := by
      calc b * (m ^ r / r) ^ 2 = (b * (m ^ r) ^ 2) * (1 / r ^ 2) := by
            rw [div_pow]
            ring
        _ = K * m := by
            rw [hbr, hK]
            ring
    linarith
  have haℓ : a * ℓ ^ 2 ≤ K * m :=
    le_trans (mul_le_mul_of_nonneg_right hab (by positivity)) hbℓ
  -- `log (2m) ≤ 2 log m`
  have hlog2 : Real.log (2 * m) ≤ 2 * ℓ := by
    have : Real.log (2 * m) ≤ Real.log (m ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at this
    rw [hℓ]
    exact_mod_cast this
  have hτK : τ ≤ Cτ * (K * m) := by
    have := mul_le_mul_of_nonneg_left hbℓ hCτ
    calc τ ≤ Cτ * b * ℓ ^ 2 := hτ
      _ = Cτ * (b * ℓ ^ 2) := by ring
      _ ≤ Cτ * (K * m) := this
  have hnlog : nC * Real.log (2 * m) ≤ 2 * Cn * (K * m) := by
    have h1 : nC * Real.log (2 * m) ≤ nC * (2 * ℓ) := mul_le_mul_of_nonneg_left hlog2 hn0
    have h2 : nC * (2 * ℓ) ≤ Cn * a * ℓ * (2 * ℓ) :=
      mul_le_mul_of_nonneg_right hnC (by linarith)
    have h3 : Cn * a * ℓ * (2 * ℓ) = 2 * Cn * (a * ℓ ^ 2) := by ring
    have h4 : 2 * Cn * (a * ℓ ^ 2) ≤ 2 * Cn * (K * m) :=
      mul_le_mul_of_nonneg_left haℓ (by linarith)
    linarith
  have hKr : (Cτ + 2 * Cn) / r ^ 2 = (Cτ + 2 * Cn) * K := by
    rw [hK]
    ring
  rw [hKr]
  have haℓ1 : 1 ≤ a * ℓ := by nlinarith
  have hmaℓ : m ≤ m * a * ℓ := by
    have := mul_le_mul_of_nonneg_left haℓ1 hm0.le
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc Wsel ≤ c1 * (m + τ + nC * Real.log (2 * m)) := hsel
      _ ≤ c1 * (m + Cτ * (K * m) + 2 * Cn * (K * m)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc1
      _ = c1 * (1 + (Cτ + 2 * Cn) * K) * m := by ring
  · have := mul_le_mul_of_nonneg_left hH hm0.le
    calc cH * (m * a) * ℓ = m * (cH * a * ℓ) := by ring
      _ ≤ m * H := this
      _ ≤ Wfull := hfull_lo
  · have hKm : (Cτ + 2 * Cn) * K * m ≤ (Cτ + 2 * Cn) * K * (m * a * ℓ) :=
      mul_le_mul_of_nonneg_left hmaℓ (by positivity)
    have hmn : m * nC ≤ Cn * (m * a * ℓ) := by
      have := mul_le_mul_of_nonneg_left hnC hm0.le
      linarith
    calc Wfull ≤ c2 * (m + τ + m * nC + nC * Real.log (2 * m)) := hfull_up
      _ ≤ c2 * ((1 + (Cτ + 2 * Cn) * K + Cn) * (m * a * ℓ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc2
      _ = c2 * (1 + (Cτ + 2 * Cn) * K + Cn) * (m * a) * ℓ := by ring

/-- **Corollary `cor:v2quarter`, horizon.**  With `g_m = m^{-1/4}`:
`(1/81) m^{1/2} log² m ≤ τ ≤ (C/16) m^{1/2} log² m`. -/
theorem v2quarter_horizon (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 < m → 8 ≤ m ^ (1 / 4 : ℝ) →
      ∀ (n : ℕ → Fin 3 → ℕ) (sel : ℕ → Fin 3),
      RootPUCTTrace (mu3 (m ^ (-(1 / 4 : ℝ)))) (fun _ => (1 : ℝ)) n sel →
      ∃ τ : ℕ, 3 ≤ τ ∧ Stop3 δ (m ^ (-(1 / 4 : ℝ))) (n τ) 0 ∧
        (∀ s a, 3 ≤ s → s < τ → ¬ Stop3 δ (m ^ (-(1 / 4 : ℝ))) (n s) a) ∧
        1 / 81 * m ^ (1 / 2 : ℝ) * Real.log m ^ 2 ≤ τ ∧
        (τ : ℝ) ≤ C / 16 * m ^ (1 / 2 : ℝ) * Real.log m ^ 2 := by
  obtain ⟨T, g0, C, -, hC, H⟩ := v2separation_horizon hδ0 hδ
  refine ⟨C, hC, ?_⟩
  intro m hm hm8 n sel h
  obtain ⟨tc, τ, -, -, -, -, h5, h6, h7, -, h9, h10, -⟩ :=
    H (1 / 4) (by norm_num) m hm hm8 n sel h
  have e : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [e] at h9 h10
  refine ⟨τ, h5, h6, h7, le_trans (le_of_eq ?_) h9, le_trans h10 (le_of_eq ?_)⟩
  · ring
  · ring

/-- **Corollary `cor:v2quarter`, work.**  The case `α = 1/4` of `v2separation_work`:
`W_selective ≤ c₁ (1 + 16 (Cτ + 2 Cn)) m` and
`cH m^{5/4} log m ≤ W_full ≤ c₂ (1 + 16 (Cτ + 2 Cn) + Cn) m^{5/4} log m`,
under the same accounting hypotheses. -/
theorem v2quarter_work {m τ nC H Wsel Wfull Cτ Cn cH c1 c2 : ℝ} (hm : 3 ≤ m)
    (hCτ : 0 ≤ Cτ) (hCn : 0 ≤ Cn) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hn0 : 0 ≤ nC) (hτ : τ ≤ Cτ * m ^ (1 / 2 : ℝ) * Real.log m ^ 2)
    (hnC : nC ≤ Cn * m ^ (1 / 4 : ℝ) * Real.log m)
    (hH : cH * m ^ (1 / 4 : ℝ) * Real.log m ≤ H)
    (hsel : Wsel ≤ c1 * (m + τ + nC * Real.log (2 * m)))
    (hfull_lo : m * H ≤ Wfull)
    (hfull_up : Wfull ≤ c2 * (m + τ + m * nC + nC * Real.log (2 * m))) :
    Wsel ≤ c1 * (1 + 16 * (Cτ + 2 * Cn)) * m ∧
      cH * m ^ (5 / 4 : ℝ) * Real.log m ≤ Wfull ∧
      Wfull ≤ c2 * (1 + 16 * (Cτ + 2 * Cn) + Cn) * m ^ (5 / 4 : ℝ) * Real.log m := by
  have e1 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
  have e3 : (Cτ + 2 * Cn) / ((1 - 2 * (1 / 4 : ℝ)) / 2) ^ 2 = 16 * (Cτ + 2 * Cn) := by
    norm_num
    ring
  have := v2separation_work (α := 1 / 4) (by norm_num) (by norm_num) hm hCτ hCn hc1 hc2
    hn0 (by rw [e1]; exact hτ) hnC hH hsel hfull_lo hfull_up
  rw [e2, e3] at this
  exact this

end Separation

end JointRootCert
