/-
Finite-sample bounds for active shared-support sampling (Lemma `lem:active-inversion`
and Theorem `thm:active-er`, Appendix B.2--B.3).

* `width_inversion`: once a terminal has at least `(32 / r²) log (32 M / (δ r²))`
  observations, its time-uniform Hoeffding width `2 β(n)` is below `r`.
* `active_sg_width`: the width charged by the Safeguarded-LCB rule.
* `stopping_time_le_sum_budget`: the counting argument.  If every queried terminal is
  still wider than its threshold `ρ z`, and `budget z` observations push the width below
  `ρ z`, the number of queries is at most `∑_z budget z`.
* `active_sample_bound`: the explicit bound obtained by combining the two.
-/
import JointRootCert.CDJoint

namespace JointRootCert

open Finset

/-! ### Explicit confidence-width inversion -/

/-- The time-uniform Hoeffding width `2 β(n)`, with
`β(n) = √(log (4 M n² / δ) / (2 n))`, as a function of a real count. -/
noncomputable def hoeffdingWidth (M δ x : ℝ) : ℝ :=
  2 * Real.sqrt (Real.log (4 * M * x ^ 2 / δ) / (2 * x))

/-- **Explicit confidence-width inversion (Lemma `lem:active-inversion`).**  For `M ≥ 2`,
`0 < δ < 1` and `0 < r ≤ 1`, every count `x ≥ (32 / r²) log (32 M / (δ r²))` has width
`2 β(x) < r`.  In particular the least such integer count `n_{M,δ}(r)` is at most
`⌈(32 / r²) log (32 M / (δ r²))⌉`, and the width stays below `r` afterwards. -/
theorem width_inversion {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r ≤ 1) {x : ℝ} (hx : 32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2)) ≤ x) :
    hoeffdingWidth M δ x < r := by
  set y := 32 * M / (δ * r ^ 2) with hy
  set L := Real.log y with hL
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2le : r ^ 2 ≤ 1 := by nlinarith
  have hMpos : 0 < M := by linarith
  have hypos : 0 < y := by positivity
  -- `y ≥ 64`, hence `L ≥ 1`
  have hy64 : 64 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hδ1.le hr2le hr2.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hypos]
    have := Real.exp_one_lt_d9
    linarith
  set x0 := 32 / r ^ 2 * L with hx0
  have hx0pos : 0 < x0 := by positivity
  have hxpos : 0 < x := lt_of_lt_of_le hx0pos hx
  -- the width at the threshold count: `log (4 M x0² / δ) ≤ 4 L`
  have hbase : Real.log (4 * M * x0 ^ 2 / δ) ≤ 4 * L := by
    have hfac : 4 * M * x0 ^ 2 / δ = 2 * y ^ 2 * L ^ 2 * (2 * δ / M) := by
      rw [hx0, hy]
      field_simp
      ring
    have hle : 4 * M * x0 ^ 2 / δ ≤ 2 * y ^ 2 * L ^ 2 := by
      rw [hfac]
      have h1 : 2 * δ / M ≤ 1 := by
        rw [div_le_one hMpos]
        linarith
      exact mul_le_of_le_one_right (by positivity) h1
    have hlog : Real.log (2 * y ^ 2 * L ^ 2) = Real.log 2 + 2 * L + 2 * Real.log L := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hLL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : Real.log 2 ≤ 2 := by
      have := Real.log_two_lt_d9
      linarith
    calc Real.log (4 * M * x0 ^ 2 / δ) ≤ Real.log (2 * y ^ 2 * L ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log 2 + 2 * L + 2 * Real.log L := hlog
      _ ≤ 4 * L := by linarith
  -- growth beyond the threshold: `log (x / x0) ≤ x / x0 - 1`
  have ht1 : 1 ≤ x / x0 := (one_le_div hx0pos).mpr hx
  have hsplit : Real.log (4 * M * x ^ 2 / δ) =
      Real.log (4 * M * x0 ^ 2 / δ) + 2 * Real.log (x / x0) := by
    have hrw : 4 * M * x ^ 2 / δ = 4 * M * x0 ^ 2 / δ * (x / x0) ^ 2 := by
      field_simp
    rw [hrw, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogt : Real.log (x / x0) ≤ x / x0 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hrx : r ^ 2 * x = 32 * L * (x / x0) := by
    rw [hx0]
    field_simp
  have hmain : 2 * Real.log (4 * M * x ^ 2 / δ) < r ^ 2 * x := by
    rw [hsplit, hrx]
    have h3 : 0 ≤ L * (x / x0 - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  -- conclude through the square root
  unfold hoeffdingWidth
  have hsq : Real.sqrt (Real.log (4 * M * x ^ 2 / δ) / (2 * x)) < r / 2 := by
    rw [Real.sqrt_lt' (by positivity)]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Integer form: with `n ≥ ⌈(32 / r²) log (32 M / (δ r²))⌉` observations the width is
below `r`. -/
theorem width_inversion_nat {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) {n : ℕ}
    (hn : ⌈32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2))⌉₊ ≤ n) :
    hoeffdingWidth M δ n < r :=
  width_inversion hM hδ0 hδ1 hr0 hr1 ((Nat.le_ceil _).trans (by exact_mod_cast hn))

/-! ### The counting argument -/

section Counting

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- Number of earlier queries of the terminal queried at step `t`. -/
def priorCount (sel : ℕ → Z) (t : ℕ) : ℕ := ((range t).filter (fun s => sel s = sel t)).card

/-- **Budget counting.**  If at every step the queried terminal has been queried fewer
than `budget` times before, the number of steps is at most the total budget. -/
theorem steps_le_sum_budget (τ : ℕ) (sel : ℕ → Z) (budget : Z → ℕ)
    (h : ∀ t < τ, priorCount sel t < budget (sel t)) : τ ≤ ∑ z, budget z := by
  have hfib : ∀ z, ((range τ).filter (fun s => sel s = z)).card ≤ budget z := by
    intro z
    rcases ((range τ).filter (fun s => sel s = z)).eq_empty_or_nonempty with he | hne
    · simp [he]
    · -- look at the last query of `z`
      set t := ((range τ).filter (fun s => sel s = z)).max' hne with ht
      have htmem := max'_mem _ hne
      rw [← ht, mem_filter, mem_range] at htmem
      have hsub : (range τ).filter (fun s => sel s = z) ⊆
          insert t ((range t).filter (fun s => sel s = sel t)) := by
        intro s hs
        have hsle : s ≤ t := le_max' _ s hs
        rw [mem_filter, mem_range] at hs
        rcases hsle.eq_or_lt with rfl | hlt
        · exact mem_insert_self _ _
        · refine mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr hlt, ?_⟩)
          rw [hs.2, htmem.2]
      have hcard := (card_le_card hsub).trans (card_insert_le _ _)
      have := h t htmem.1
      unfold priorCount at this
      have hb : budget (sel t) = budget z := by rw [htmem.2]
      omega
  calc τ = (range τ).card := (card_range τ).symm
    _ = ∑ z, ((range τ).filter (fun s => sel s = z)).card :=
        card_eq_sum_card_fiberwise (fun s _ => mem_univ (sel s))
    _ ≤ ∑ z, budget z := sum_le_sum (fun z _ => hfib z)

/-- **From widths to stopping times (proof of Theorem `thm:active-er`).**

`wsel t` is the confidence width of the terminal queried at step `t` and `W n` bounds the
width of a nested interval built from `n` observations.  If each queried terminal is at
least as wide as its threshold `ρ z` (the width lemmas), and `budget z` observations push
the width strictly below `ρ z` (the inversion), then the procedure makes at most
`∑_z budget z` queries. -/
theorem stopping_time_le_sum_budget (τ : ℕ) (sel : ℕ → Z) (wsel : ℕ → ℝ) (W : ℕ → ℝ)
    (ρ : Z → ℝ) (budget : Z → ℕ)
    (hnest : ∀ t < τ, wsel t ≤ W (priorCount sel t))
    (hcharged : ∀ t < τ, ρ (sel t) ≤ wsel t)
    (hinv : ∀ z n, budget z ≤ n → W n < ρ z) : τ ≤ ∑ z, budget z := by
  refine steps_le_sum_budget τ sel budget (fun t ht => ?_)
  by_contra hge
  have h1 := hinv (sel t) (priorCount sel t) (not_lt.mp hge)
  have h2 := hnest t ht
  have h3 := hcharged t ht
  linarith

/-- **Explicit sample bound.**  With time-uniform Hoeffding intervals and thresholds
`0 < ρ z ≤ 1`, the number of queries is at most
`∑_z ⌈(32 / ρ_z²) log (32 M / (δ ρ_z²))⌉`.

The three bounds of Theorem `thm:active-er` are the instances
`ρ_z = max {ε, Δ_z / 2}` (exact-regret sampling, `active_width`),
`ρ_z = max {ε / 2, Δ_z / 3}` (Safeguarded-LCB, `active_sg_width`) and
`ρ_z = max {Γ + ε, Δ_z} / 2` (optimistic separation, `active_os_width`). -/
theorem active_sample_bound {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (τ : ℕ) (sel : ℕ → Z) (wsel : ℕ → ℝ) (ρ : Z → ℝ) (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ 1)
    (hnest : ∀ t < τ, wsel t ≤ hoeffdingWidth M δ (priorCount sel t))
    (hcharged : ∀ t < τ, ρ (sel t) ≤ wsel t) :
    τ ≤ ∑ z, ⌈32 / ρ z ^ 2 * Real.log (32 * M / (δ * ρ z ^ 2))⌉₊ :=
  stopping_time_le_sum_budget τ sel wsel (fun n => hoeffdingWidth M δ n) ρ _ hnest hcharged
    (fun z _ hn => width_inversion_nat hM hδ0 hδ1 (hρ z).1 (hρ z).2 hn)

end Counting

/-! ### Safeguarded-LCB -/

section Safeguard

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}
variable {l u : Z → ℝ} {ε : ℝ}

/-- **Width charged by Safeguarded-LCB (proof of Proposition `prop:active-hybrid`).**

`a` minimises the exact certificate and the procedure continues; `p`, `q` are the
optimistic inside and outside witnesses and `y` is the lower-confidence inside candidate
(a maximiser of the lower endpoint over `S(a)`), admitted by the gate
`w(y) ≥ max {R(a) / 2, u(p) - u(y)}` of `eq:safeguard-gate`.  The wider of `y` and `q` is
queried.  Then

* its width exceeds `ε / 2`, without coverage;
* on coverage it is at least a third of its own gap. -/
theorem active_sg_width (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) (hlu : l ≤ u) (hε : 0 ≤ ε)
    (a : A)
    (hmin : ∀ c, rectCert (supp a) (hne a) (hpr a) l u ≤ rectCert (supp c) (hne c) (hpr c) l u)
    (hcont : ε < rectCert (supp a) (hne a) (hpr a) l u)
    {p q y : Z} (_hp : p ∈ supp a) (hpmax : ∀ x ∈ supp a, u x ≤ u p)
    (hq : q ∉ supp a) (hqmax : ∀ z, z ∉ supp a → u z ≤ u q)
    (hy : y ∈ supp a) (hymax : ∀ x ∈ supp a, l x ≤ l y)
    (hgate1 : rectCert (supp a) (hne a) (hpr a) l u / 2 ≤ u y - l y)
    (hgate2 : u p - u y ≤ u y - l y) :
    ε / 2 < max (u y - l y) (u q - l q) ∧
      ∀ μ ∈ Set.Icc l u,
        (u q - l q ≤ u y - l y → (gmax μ - μ y) / 3 ≤ u y - l y) ∧
        (u y - l y ≤ u q - l q → (gmax μ - μ q) / 3 ≤ u q - l q) := by
  have hUq : (supp a)ᶜ.sup' (hpr a) u = u q :=
    le_antisymm (sup'_le _ _ (fun z hz => hqmax z (mem_compl.mp hz)))
      (le_sup' u (mem_compl.mpr hq))
  have hLy : (supp a).sup' (hne a) l = l y :=
    le_antisymm (sup'_le _ _ (fun x hx => hymax x hx)) (le_sup' l hy)
  have hRa : rectCert (supp a) (hne a) (hpr a) l u = max 0 (u q - l y) := by
    unfold rectCert
    rw [hUq, hLy]
  have hgap : ε < u q - l y := by
    by_contra h
    have : max 0 (u q - l y) ≤ ε := max_le hε (not_lt.mp h)
    rw [hRa] at hcont
    linarith
  have hRa' : rectCert (supp a) (hne a) (hpr a) l u = u q - l y := by
    rw [hRa]
    exact max_eq_right (by linarith)
  refine ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _), fun μ hμ => ?_⟩
  have h1 := hμ.1 y
  have h2 := hμ.1 q
  have h3 := le_gmax μ y
  have h4 := le_gmax μ q
  rcases le_total (u q) (u p) with hpq | hpq
  · have hg : ∀ x, u x ≤ u p := fun x => by
      by_cases hx : x ∈ supp a
      · exact hpmax x hx
      · exact (hqmax x hx).trans hpq
    have hstar : gmax μ ≤ u p := sup'_le _ _ (fun x _ => (hμ.2 x).trans (hg x))
    constructor
    · intro _
      linarith
    · intro _
      linarith
  · have hg : ∀ x, u x ≤ u q := fun x => by
      by_cases hx : x ∈ supp a
      · exact (hpmax x hx).trans hpq
      · exact hqmax x hx
    have hstar : gmax μ ≤ u q := sup'_le _ _ (fun x _ => (hμ.2 x).trans (hg x))
    obtain ⟨c, hc⟩ := hcov q
    have hw : rectCert (supp a) (hne a) (hpr a) l u ≤ u q - l q :=
      (hmin c).trans (rectCert_le_width (hne c) (hpr c) hlu hc hg)
    rw [hRa'] at hw
    constructor
    · intro _
      linarith
    · intro _
      linarith

end Safeguard

end JointRootCert
