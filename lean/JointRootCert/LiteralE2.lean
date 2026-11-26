/-
Theorem `thm:onpolicy-uct` / `thm:selective-separation` (Selective vs. eager maintenance
separations on UCT and Root-PUCT funnels), local-UCT half, for the UCT index literally as
`eq:uct-index` displays it.

The manuscript's index is `I_t(v,j) = mean_t(j) + c_uct √(log N_t(v) / N_t(v,j))`, "untried
outgoing edges are visited first", and `N_t(v)` is not defined.  `FunnelUCT.lean` proves the
theorem for the reading `N_t(v) = 1 + (number of earlier visits of v)` (`uctIndex`,
`log (1 + t)`).  This file proves the same statement for the other reading,
`N_t(v) = number of earlier visits of v` (`litIndex`, `log t`), with `c_uct = 1`, and
states both readings together.

* `litIndex`, `LitUCTRun`: the literal index and a run of local UCT with it (every arm
  tried once during the first `|ι|` visits, afterwards any maximiser of the index).
  `litUCTRun_iff` (a literal run is a `UCTRun` for shifted means), `exists_litRun`,
  `LitUCTRun.count_le`, `LitUCTRun.window_lower`, `LitUCTRun.fairness`.
* `LitFunnelSearch`: the recursive funnel model of `FunnelUCT.lean` with the literal index
  at the root and at the split; `exists_litFunnelSearch`.
* `FunFacts`: the six count facts about the search process through which the proof of the
  theorem uses UCT.  Both `FunnelSearch` (`FunnelSearch.facts`) and `LitFunnelSearch`
  (`LitFunnelSearch.facts`) satisfy them; the theorem is proved once from `FunFacts`
  (`onpolicy_of_facts`), with the same constants `funK0`, `funJ`, `funT0` as in
  `FunnelUCT.lean`.
* `onpolicy_uct_funnel_literal`, `onpolicy_uct_funnel_both_readings`: the assembled
  statements, with the conclusion of `onpolicy_uct_funnel` verbatim (`FunnelConclusion`).
* Local UCT at every internal vertex: `FullFunnelSearch` (root, split and every binary
  vertex of the two fans are literal UCT nodes on their own visit clocks, with the
  empirical means of the rewards of the terminals actually reached), its reduction
  `FullFunnelSearch.lit`, the induced path rule `fullRule`, the theorem
  `onpolicy_uct_funnel_full`, and existence `exists_fullFunnelSearch`.

Graph family.  The manuscript says only "bounded-degree two-exit funnel DAGs of size
`Θ(m)`".  The graph used here is `monFunnelCirc m` of `MonitorWork.lean`: the root has the
three actions `b = 0` (a terminal of reward `4/5`), `a' = 1` (a terminal of reward
`4/5 - g`) and `C = 2`; the top vertex of `C` is a binary split over the two fans
`monFunnelFan m 2` and `monFunnelFan m 3`; the fan `monFanZ z ⌈log₂ m⌉ m` is a balanced
binary tree with `m` unary bottom vertices, each of which has the exit terminal `z` as its
only child (rewards `3/20` and `1/5`).  `MaxCirc` is the tree unfolding: each exit is one
terminal of the DAG with `m` parents.  `funnel_graph`: the unfolding has `6 m + 1` vertices,
each fan has exactly `m` bottom-layer parents, height at most `⌈log₂ m⌉ + 1`, and only its
exit as terminal.  Out-degrees are at most `3` (root) and `2` (elsewhere) by construction;
the in-degree of the two exit terminals is `m`, so "bounded-degree" holds for out-degree
only.  The eager wave is charged for all `m` bottom-layer parents of the changed exit
(the manuscript says "at least `m/2`").
-/
import JointRootCert.FunnelUCT

namespace JointRootCert

namespace LiteralE2

open Finset

noncomputable section

/-! ### Local UCT with the literal index -/

section UCT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The UCT index of `eq:uct-index` with `N_t(v)` read as the number `t` of earlier visits
of the node: `Q + c √(log t / N)`. -/
def litIndex (c q : ℝ) (t n : ℕ) : ℝ := q + c * Real.sqrt (Real.log t / n)

/-- A run of local UCT with the literal index at a node with arms `ι`: the first `|ι|`
visits try every arm once (in any order), and afterwards a maximiser of `litIndex` is
selected (any maximiser).  `Q t i` is the empirical mean of arm `i` before visit `t`. -/
structure LitUCTRun (c : ℝ) (Q : ℕ → ι → ℝ) (sel : ℕ → ι) : Prop where
  forced : ∀ i, uctCount sel (Fintype.card ι) i = 1
  greedy : ∀ t, Fintype.card ι ≤ t → ∀ j,
    litIndex c (Q t j) t (uctCount sel t j) ≤ litIndex c (Q t (sel t)) t (uctCount sel t (sel t))

/-- Difference between the literal exploration bonus and the `log (1 + t)` bonus. -/
def litShift (c : ℝ) (sel : ℕ → ι) (t : ℕ) (i : ι) : ℝ :=
  c * Real.sqrt (Real.log (t : ℝ) / (uctCount sel t i : ℝ))
    - c * Real.sqrt (Real.log (1 + (t : ℝ)) / (uctCount sel t i : ℝ))

variable {c : ℝ} {Q : ℕ → ι → ℝ} {sel : ℕ → ι}

omit [Fintype ι] in
theorem litIndex_eq (c : ℝ) (Q : ℕ → ι → ℝ) (sel : ℕ → ι) (t : ℕ) (i : ι) :
    litIndex c (Q t i) t (uctCount sel t i)
      = uctIndex c (Q t i + litShift c sel t i) t (uctCount sel t i) := by
  unfold litIndex uctIndex litShift
  ring

/-- A literal-index run is exactly a `UCTRun` (index with `log (1 + t)`) whose means are
shifted by `litShift`. -/
theorem litUCTRun_iff :
    LitUCTRun c Q sel ↔ UCTRun c (fun t i => Q t i + litShift c sel t i) sel := by
  constructor
  · intro h
    refine ⟨h.forced, fun t ht j => ?_⟩
    have := h.greedy t ht j
    rw [litIndex_eq, litIndex_eq] at this
    exact this
  · intro h
    refine ⟨h.forced, fun t ht j => ?_⟩
    have := h.greedy t ht j
    rw [litIndex_eq, litIndex_eq]
    exact this

/-- Literal-index runs exist for every history-dependent empirical-mean functional. -/
theorem exists_litRun [Nonempty ι] (c : ℝ) (Qf : (ℕ → ι) → ℕ → ι → ℝ)
    (hQ : ∀ (sel sel' : ℕ → ι) (t : ℕ), (∀ s, s < t → sel s = sel' s) → Qf sel t = Qf sel' t) :
    ∃ sel, LitUCTRun c (Qf sel) sel := by
  obtain ⟨sel, h⟩ := exists_uctRun c (fun sel t i => Qf sel t i + litShift c sel t i) (by
    intro sel sel' t hss
    funext i
    have hc : uctCount sel t i = uctCount sel' t i := by
      unfold uctCount
      congr 1
      exact Finset.filter_congr (fun s hs => by rw [hss s (mem_range.mp hs)])
    show Qf sel t i + litShift c sel t i = Qf sel' t i + litShift c sel' t i
    rw [hQ sel sel' t hss]
    unfold litShift
    rw [hc])
  exact ⟨sel, litUCTRun_iff.mpr h⟩

theorem log_nat_le (t : ℕ) : Real.log (t : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    simp
  · exact Real.log_le_log (Nat.cast_pos.mpr h) (by linarith)

theorem LitUCTRun.one_le (h : LitUCTRun c Q sel) (i : ι) {t : ℕ} (ht : Fintype.card ι ≤ t) :
    1 ≤ uctCount sel t i := by
  have := uctCount_mono sel i ht
  rwa [h.forced] at this

/-- **Count bound, literal index.**  Same statement as `UCTRun.count_le`: if the mean of
arm `i` never exceeds `u0` and some arm always has mean at least `b > u0`, then for
`t ≥ |ι|`, `N_i(t) ≤ max {1, 1 + c² log (1 + t) / (b - u0)²}`. -/
theorem LitUCTRun.count_le (h : LitUCTRun c Q sel) (hc : 0 ≤ c) {i star : ι} {u0 b : ℝ}
    (hΔ : u0 < b) (hi : ∀ t, Q t i ≤ u0) (hstar : ∀ t, b ≤ Q t star) {t : ℕ}
    (ht : Fintype.card ι ≤ t) :
    (uctCount sel t i : ℝ) ≤ max 1 (1 + c ^ 2 * Real.log (1 + t) / (b - u0) ^ 2) := by
  have := uct_count_le (c := c) hΔ (fun t => uctCount sel t i) (fun t => sel t = i)
    (Fintype.card ι)
    (fun t _ => ⟨fun hp => by rw [uctCount_succ, ite_eq_left hp],
      fun hp => by rw [uctCount_succ, ite_eq_right hp, add_zero]⟩)
    (fun t ht hp => by
      have hg := h.greedy t ht star
      rw [hp] at hg
      unfold litIndex at hg
      have h1 : 0 ≤ c * Real.sqrt (Real.log (t : ℝ) / (uctCount sel t star : ℝ)) :=
        mul_nonneg hc (Real.sqrt_nonneg _)
      have h4 : c * Real.sqrt (Real.log (t : ℝ) / (uctCount sel t i : ℝ))
          ≤ c * Real.sqrt (Real.log (1 + (t : ℝ)) / (uctCount sel t i : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right (log_nat_le t) (Nat.cast_nonneg _))) hc
      have h2 := hstar t
      have h3 := hi t
      linarith) t ht
  rw [h.forced] at this
  simpa using this

/-- **Window lower bound, literal index.**  At a node with `K = |ι|` arms whose means are at
most `B`, let the arm `e0` have mean at least `B - γ`, let `η > 0`, and let the window
`[s0, t]` with `max {1, K} ≤ s0 ≤ t` satisfy `K (c² log t / η² + 1) < t - s0`.  Then
`c² log s0 < (γ + η)² N_{e0}(t)`. -/
theorem LitUCTRun.window_lower (h : LitUCTRun c Q sel) (hc : 0 < c) {B γ η : ℝ} (hη : 0 < η)
    (hγ : 0 ≤ γ) (hQ1 : ∀ t i, Q t i ≤ B) {e0 : ι} (hQ0 : ∀ t, B - γ ≤ Q t e0) {s0 t : ℕ}
    (hs1 : 1 ≤ s0) (hKs0 : Fintype.card ι ≤ s0) (hs0t : s0 ≤ t)
    (hwin : (Fintype.card ι : ℝ) * (c ^ 2 * Real.log t / η ^ 2 + 1) < (t : ℝ) - s0) :
    c ^ 2 * Real.log s0 < (γ + η) ^ 2 * uctCount sel t e0 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hγη : 0 < γ + η := by linarith
  have hη2 : 0 < η ^ 2 := by positivity
  have hs1R : (1 : ℝ) ≤ s0 := by exact_mod_cast hs1
  -- the index of `e0` is at least `B + η` throughout the window
  have hA : ∀ s, s0 ≤ s → s < t → B + η ≤ litIndex c (Q s e0) s (uctCount sel s e0) := by
    intro s hs hst
    have hns : (0 : ℝ) < uctCount sel s e0 := by
      exact_mod_cast h.one_le e0 (hKs0.trans hs)
    have hmono : (uctCount sel s e0 : ℝ) ≤ uctCount sel t e0 := by
      exact_mod_cast uctCount_mono sel e0 hst.le
    have hlog : Real.log (s0 : ℝ) ≤ Real.log (s : ℝ) :=
      Real.log_le_log (by linarith) (by exact_mod_cast hs)
    have h4 : (γ + η) ^ 2 ≤ c ^ 2 * (Real.log (s : ℝ) / uctCount sel s e0) := by
      rw [← mul_div_assoc, le_div_iff₀ hns]
      have h5 : (γ + η) ^ 2 * (uctCount sel s e0 : ℝ) ≤ (γ + η) ^ 2 * uctCount sel t e0 :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
      have h6 := mul_le_mul_of_nonneg_left hlog (sq_nonneg c)
      linarith
    have hsq : γ + η ≤ c * Real.sqrt (Real.log (s : ℝ) / uctCount sel s e0) := by
      have h5 : Real.sqrt ((γ + η) ^ 2)
          ≤ Real.sqrt (c ^ 2 * (Real.log (s : ℝ) / uctCount sel s e0)) :=
        Real.sqrt_le_sqrt h4
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, Real.sqrt_sq hγη.le] at h5
      exact h5
    unfold litIndex
    linarith [hQ0 s]
  have hlt0 : 0 ≤ Real.log (t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hs1.trans hs0t)
  -- hence every arm gains at most `c² log t / η² + 1` selections in the window
  have hB : ∀ j u, s0 ≤ u → u ≤ t →
      (uctCount sel u j : ℝ) - uctCount sel s0 j ≤ c ^ 2 * Real.log t / η ^ 2 + 1 := by
    intro j u hu
    have hnn : 0 ≤ c ^ 2 * Real.log (t : ℝ) / η ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg c) hlt0) hη2.le
    induction u, hu using Nat.le_induction with
    | base =>
      intro _
      rw [sub_self]
      linarith
    | succ u hu ih =>
      intro hut
      have ih' := ih (by omega)
      rw [uctCount_succ]
      by_cases hsel : sel u = j
      · have hg := (hA u hu (by omega)).trans (h.greedy u (hKs0.trans hu) e0)
        rw [hsel] at hg
        unfold litIndex at hg
        have hnu : (0 : ℝ) < uctCount sel u j := by
          exact_mod_cast h.one_le j (hKs0.trans hu)
        have h1 : η ≤ c * Real.sqrt (Real.log (u : ℝ) / uctCount sel u j) := by
          linarith [hQ1 u j]
        have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hs1.trans hu
        have hlogu : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg hu1
        have h2 : η ^ 2 ≤ (c * Real.sqrt (Real.log (u : ℝ) / uctCount sel u j)) ^ 2 :=
          pow_le_pow_left₀ hη.le h1 2
        rw [mul_pow, Real.sq_sqrt (div_nonneg hlogu hnu.le), ← mul_div_assoc,
          le_div_iff₀ hnu] at h2
        have hlogut : Real.log (u : ℝ) ≤ Real.log (t : ℝ) :=
          Real.log_le_log (by linarith) (by exact_mod_cast (by omega : u ≤ t))
        have h3 : (uctCount sel u j : ℝ) ≤ c ^ 2 * Real.log t / η ^ 2 := by
          rw [le_div_iff₀ hη2]
          have := mul_le_mul_of_nonneg_left hlogut (sq_nonneg c)
          linarith
        rw [ite_eq_left hsel]
        push_cast
        have : (0 : ℝ) ≤ uctCount sel s0 j := Nat.cast_nonneg _
        linarith
      · rw [ite_eq_right hsel, add_zero]
        exact ih'
  have hsum : ∑ j, ((uctCount sel t j : ℝ) - uctCount sel s0 j)
      ≤ ∑ _j : ι, (c ^ 2 * Real.log t / η ^ 2 + 1) :=
    Finset.sum_le_sum (fun j _ => hB j t hs0t le_rfl)
  have hl : ∑ j, ((uctCount sel t j : ℝ) - uctCount sel s0 j) = (t : ℝ) - s0 := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, uctCount_sum, uctCount_sum]
  rw [hl, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith

/-- **Logarithmic fairness, literal index** (Step 1 of the proof).  With means in `[0, 1]`
and a window `[s0, t]`, `max {1, K} ≤ s0 ≤ t`, `K (c² log t + 1) < t - s0`: every arm has
`c² log s0 < 4 N_e(t)`. -/
theorem LitUCTRun.fairness (h : LitUCTRun c Q sel) (hc : 0 < c) (hQ0 : ∀ t i, 0 ≤ Q t i)
    (hQ1 : ∀ t i, Q t i ≤ 1) {s0 t : ℕ} (hs1 : 1 ≤ s0) (hKs0 : Fintype.card ι ≤ s0)
    (hs0t : s0 ≤ t)
    (hwin : (Fintype.card ι : ℝ) * (c ^ 2 * Real.log t + 1) < (t : ℝ) - s0)
    (e0 : ι) : c ^ 2 * Real.log s0 < 4 * uctCount sel t e0 := by
  have := h.window_lower hc (B := 1) (γ := 1) (η := 1) one_pos zero_le_one hQ1 (e0 := e0)
    (fun t => by rw [sub_self]; exact hQ0 t e0) hs1 hKs0 hs0t
    (by rw [one_pow, div_one]; exact hwin)
  norm_num at this
  linarith

omit [Fintype ι] in
/-- An empirical mean of history-determined returns depends only on the earlier
selections. -/
theorem mean_local (F : (ℕ → ι) → ℕ → ℝ)
    (hF : ∀ (sel sel' : ℕ → ι) (s : ℕ), (∀ u, u ≤ s → sel u = sel' u) → F sel s = F sel' s)
    (sel sel' : ℕ → ι) (t : ℕ) (hss : ∀ s, s < t → sel s = sel' s) :
    (fun a => (∑ s ∈ (range t).filter (fun s => sel s = a), F sel s) / (uctCount sel t a : ℝ))
      = fun a => (∑ s ∈ (range t).filter (fun s => sel' s = a), F sel' s)
          / (uctCount sel' t a : ℝ) := by
  funext a
  have hf : (range t).filter (fun s => sel s = a) = (range t).filter (fun s => sel' s = a) :=
    Finset.filter_congr (fun s hs => by rw [hss s (mem_range.mp hs)])
  have hc : uctCount sel t a = uctCount sel' t a := by
    unfold uctCount
    rw [hf]
  show (∑ s ∈ (range t).filter (fun s => sel s = a), F sel s) / (uctCount sel t a : ℝ)
    = (∑ s ∈ (range t).filter (fun s => sel' s = a), F sel' s) / (uctCount sel' t a : ℝ)
  rw [hc, hf]
  congr 1
  exact Finset.sum_congr rfl (fun s hs => hF sel sel' s (fun u hu =>
    hss u (lt_of_le_of_lt hu (mem_range.mp (Finset.mem_filter.mp hs).1))))

end UCT

/-! ### The recursive funnel model with the literal index -/

/-- **Recursive local UCT on the two-exit funnel with the literal index** (`c = 1`).  As
`FunnelSearch`, with `litIndex` in place of `uctIndex` at the root and at the split. -/
structure LitFunnelSearch (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) : Prop where
  root : LitUCTRun 1 (fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a),
    funMu g (funTerm sel sub s)) / uctCount sel t a) sel
  split : LitUCTRun 1 (fun j e => (∑ i ∈ (range j).filter (fun i => sub i = e),
    funMu g (funExit (sub i))) / uctCount sub j e) sub

/-- Literal-index recursive funnel searches exist for every `g`. -/
theorem exists_litFunnelSearch (g : ℝ) : ∃ sel sub, LitFunnelSearch g sel sub := by
  obtain ⟨sub, hsub⟩ := exists_litRun (ι := Fin 2) 1
    (fun sub j e => (∑ i ∈ (range j).filter (fun i => sub i = e), funMu g (funExit (sub i)))
      / uctCount sub j e)
    (fun s s' t hss => mean_local (fun sub i => funMu g (funExit (sub i)))
      (fun s s' i h => by
        show funMu g (funExit (s i)) = funMu g (funExit (s' i))
        rw [h i le_rfl]) s s' t hss)
  obtain ⟨sel, hsel⟩ := exists_litRun (ι := Fin 3) 1
    (fun sel t a => (∑ s ∈ (range t).filter (fun s => sel s = a), funMu g (funTerm sel sub s))
      / uctCount sel t a)
    (fun s s' t hss => mean_local (fun sel s => funMu g (funTerm sel sub s))
      (fun sel sel' s h => by
        have hcnt : uctCount sel s 2 = uctCount sel' s 2 := by
          unfold uctCount
          congr 1
          exact Finset.filter_congr (fun u hu => by rw [h u (mem_range.mp hu).le])
        show funMu g (funTerm sel sub s) = funMu g (funTerm sel' sub s)
        unfold funTerm
        rw [h s le_rfl, hcnt]) s s' t hss)
  exact ⟨sel, sub, hsel, hsub⟩

private theorem fin3 (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ a, P a := by
  intro a
  fin_cases a
  exacts [h0, h1, h2]

variable {δ g : ℝ} {sel : ℕ → Fin 3} {sub : ℕ → Fin 2}

theorem funQ_zero (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) :
    funQ g sel sub t 0 = 4 / 5 := by simp [funQ, funMu]

theorem funQ_one (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) :
    funQ g sel sub t 1 = 4 / 5 - g := by simp [funQ, funMu]

theorem funQ_two (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) :
    0 ≤ funQ g sel sub t 2 ∧ funQ g sel sub t 2 ≤ 1 / 5 := by
  have e : funQ g sel sub t 2
      = (∑ s ∈ (range t).filter (fun s => sel s = 2), funMu g (funTerm sel sub s))
        / uctCount sel t 2 := by
    unfold funQ
    rw [ite_eq_left rfl]
  rw [e]
  exact fuMean_bounds sel _ 2 t (fun s hs => by
    rw [funTerm, ite_eq_left hs]
    exact ⟨by linarith [(funMu_exit g (sub (uctCount sel s 2))).1],
      (funMu_exit g (sub (uctCount sel s 2))).2⟩) (by norm_num)

theorem funQ_bounds (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (t : ℕ) : ∀ i : Fin 3, 0 ≤ funQ g sel sub t i ∧ funQ g sel sub t i ≤ 4 / 5 := by
  refine fin3 _ ?_ ?_ ?_
  · rw [funQ_zero]
    norm_num
  · rw [funQ_one]
    constructor <;> linarith
  · exact ⟨(funQ_two g sel sub t).1, by linarith [(funQ_two g sel sub t).2]⟩

/-- The root of a literal funnel search is a literal UCT node for the value table `funQ`. -/
theorem LitFunnelSearch.rootQ (h : LitFunnelSearch g sel sub) :
    LitUCTRun 1 (funQ g sel sub) sel :=
  ⟨h.root.forced, fun t ht j => by
    have := h.root.greedy t ht j
    rw [funQ_eq g sel sub (h.root.one_le j ht),
      funQ_eq g sel sub (h.root.one_le (sel t) ht)] at this
    exact this⟩

/-! ### The count facts through which the proof uses UCT -/

/-- The facts about the search process used by the proof of `thm:onpolicy-uct`:

* every root action has been tried after three rollouts;
* `N_C(t) ≤ 1 + log (1 + t) / (3/5)²` and `N_{a'}(t) ≤ 1 + log (1 + t) / g²` (Steps 2-3);
* fairness at the root (`t ≥ 400`) and at the split (`j ≥ 196`):
  `log ⌊t/2⌋ < 4 N(t)` (Step 1);
* the near-rival lower bound of Step 3 on the window `[⌈t/2⌉, t]`. -/
structure FunFacts (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) : Prop where
  one_le : ∀ t, 3 ≤ t → ∀ a, 1 ≤ uctCount sel t a
  cntC : ∀ t : ℕ, 3 ≤ t → (uctCount sel t 2 : ℝ) ≤ 1 + Real.log (1 + (t : ℝ)) / (3 / 5) ^ 2
  cntA : ∀ t : ℕ, 3 ≤ t → (uctCount sel t 1 : ℝ) ≤ 1 + Real.log (1 + (t : ℝ)) / g ^ 2
  fairRoot : ∀ t : ℕ, 400 ≤ t → ∀ a, Real.log ((t / 2 : ℕ) : ℝ) < 4 * (uctCount sel t a : ℝ)
  fairSplit : ∀ j : ℕ, 196 ≤ j → ∀ e, Real.log ((j / 2 : ℕ) : ℝ) < 4 * (uctCount sub j e : ℝ)
  rival : ∀ t : ℕ, 6 ≤ t →
    3 * (Real.log (1 + (t : ℝ)) / g ^ 2 + 1) < (t : ℝ) - (((t + 1) / 2 : ℕ) : ℝ) →
    Real.log (((t + 1) / 2 : ℕ) : ℝ) < 4 * g ^ 2 * (uctCount sel t 1 : ℝ)

private theorem log1_nonneg (t : ℕ) : 0 ≤ Real.log (1 + (t : ℝ)) :=
  Real.log_nonneg (by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith)

/-- A literal-index funnel search satisfies the count facts. -/
theorem LitFunnelSearch.facts (h : LitFunnelSearch g sel sub) (hg0 : 0 < g) (hg : g ≤ 4 / 5) :
    FunFacts g sel sub := by
  have hR := h.rootQ
  have hQb := funQ_bounds hg0.le hg sel sub
  have e3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  refine ⟨fun t ht a => h.root.one_le a (by rw [Fintype.card_fin]; exact ht), ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have := hR.count_le (by norm_num) (i := 2) (star := 0) (u0 := 1 / 5) (b := 4 / 5)
      (by norm_num) (fun t => (funQ_two g sel sub t).2)
      (fun t => le_of_eq (funQ_zero g sel sub t).symm) (t := t)
      (by rw [Fintype.card_fin]; exact ht)
    have hl := div_nonneg (log1_nonneg t) (by norm_num : (0 : ℝ) ≤ (3 / 5) ^ 2)
    refine this.trans (max_le (by linarith) (le_of_eq ?_))
    norm_num
  · intro t ht
    have := hR.count_le (by norm_num) (i := 1) (star := 0) (u0 := 4 / 5 - g) (b := 4 / 5)
      (by linarith) (fun t => le_of_eq (funQ_one g sel sub t))
      (fun t => le_of_eq (funQ_zero g sel sub t).symm) (t := t)
      (by rw [Fintype.card_fin]; exact ht)
    have hl := div_nonneg (log1_nonneg t) (sq_nonneg g)
    refine this.trans (max_le (by linarith) (le_of_eq ?_))
    rw [one_pow, one_mul, show (4 / 5 : ℝ) - (4 / 5 - g) = g by ring]
  · intro t ht a
    have hw := fu_window (K := 3) (by norm_num) (t := t) (by
      norm_num
      exact_mod_cast ht)
    have := hR.fairness one_pos (fun t i => (hQb t i).1)
      (fun t i => ((hQb t i).2).trans (by norm_num)) (s0 := t / 2) (t := t) (by omega)
      (by rw [Fintype.card_fin]; omega) (Nat.div_le_self t 2)
      (by
        rw [Fintype.card_fin, one_pow, one_mul, e3]
        have := log_nat_le t
        linarith) a
    rwa [one_pow, one_mul] at this
  · intro j hj e
    have hw := fu_window (K := 2) (by norm_num) (t := j) (by
      norm_num
      exact_mod_cast hj)
    have hsb : ∀ (j : ℕ) (e : Fin 2),
        0 ≤ (∑ i ∈ (range j).filter (fun i => sub i = e), funMu g (funExit (sub i)))
            / uctCount sub j e ∧
          (∑ i ∈ (range j).filter (fun i => sub i = e), funMu g (funExit (sub i)))
            / uctCount sub j e ≤ 1 :=
      fun j e => fuMean_bounds sub _ e j (fun i _ => ⟨by linarith [(funMu_exit g (sub i)).1],
        by linarith [(funMu_exit g (sub i)).2]⟩) zero_le_one
    have := h.split.fairness one_pos (fun j e => (hsb j e).1) (fun j e => (hsb j e).2)
      (s0 := j / 2) (t := j) (by omega) (by rw [Fintype.card_fin]; omega) (Nat.div_le_self j 2)
      (by
        rw [Fintype.card_fin, one_pow, one_mul, e2]
        have := log_nat_le j
        linarith) e
    rwa [one_pow, one_mul] at this
  · intro t ht hw
    have hdiv : Real.log (t : ℝ) / g ^ 2 ≤ Real.log (1 + (t : ℝ)) / g ^ 2 :=
      div_le_div_of_nonneg_right (log_nat_le t) (sq_nonneg g)
    have := hR.window_lower one_pos (B := 4 / 5) (γ := g) (η := g) hg0 hg0.le
      (fun t i => (hQb t i).2) (e0 := 1) (fun t => le_of_eq (funQ_one g sel sub t).symm)
      (s0 := (t + 1) / 2) (t := t) (by omega) (by rw [Fintype.card_fin]; omega) (by omega)
      (by
        rw [Fintype.card_fin, one_pow, one_mul, e3]
        linarith)
    rw [one_pow, one_mul] at this
    linarith [show (g + g) ^ 2 * (uctCount sel t 1 : ℝ) = 4 * g ^ 2 * uctCount sel t 1 by ring]

/-- A `FunnelSearch` of `FunnelUCT.lean` (index with `log (1 + t)`) satisfies the count
facts. -/
theorem facts_of_funnelSearch (h : FunnelSearch g sel sub) (hg0 : 0 < g) (hg : g ≤ 4 / 5) :
    FunFacts g sel sub := by
  refine ⟨fun t ht a => h.root.one_le a (by rw [Fintype.card_fin]; exact ht), ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨c1, -, -, -⟩ := funnel_counts h.funnelRoot hg0 hg ht
    have hl := div_nonneg (log1_nonneg t) (by norm_num : (0 : ℝ) ≤ (3 / 5) ^ 2)
    exact c1.trans (max_le (by linarith) le_rfl)
  · intro t ht
    obtain ⟨-, c2, -, -⟩ := funnel_counts h.funnelRoot hg0 hg ht
    have hl := div_nonneg (log1_nonneg t) (sq_nonneg g)
    exact c2.trans (max_le (by linarith) le_rfl)
  · intro t ht a
    exact lt_of_le_of_lt (log_nat_le (t / 2)) (h.root_fair hg0.le hg ht a)
  · intro j hj e
    exact lt_of_le_of_lt (log_nat_le (j / 2)) (h.split_fair hj e)
  · intro t ht hw
    obtain ⟨-, -, -, c4⟩ := funnel_counts h.funnelRoot hg0 hg (by omega : 3 ≤ t)
    have h1 : ((t / 2 : ℕ) : ℝ) ≤ (((t + 1) / 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : t / 2 ≤ (t + 1) / 2)
    have h2 := c4 ht (by linarith)
    have h3 : Real.log (((t + 1) / 2 : ℕ) : ℝ) ≤ Real.log (1 + ((t / 2 : ℕ) : ℝ)) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by
        exact_mod_cast (by omega : (t + 1) / 2 ≤ 1 + t / 2))
    linarith

/-! ### Steps 1-2 from the count facts -/

theorem lit_log_ge {c : ℝ} {t : ℕ} (h : 2 * ⌈Real.exp c⌉₊ ≤ t) :
    c ≤ Real.log ((t / 2 : ℕ) : ℝ) := by
  have h1 : ⌈Real.exp c⌉₊ ≤ t / 2 := by omega
  have h2 : Real.exp c ≤ ((t / 2 : ℕ) : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos c) h2)]
  exact h2

/-- **Step 2: counts at the constant cutoff** `funT0 δ` (the same cutoff as in
`FunnelUCT.lean`). -/
theorem FunFacts.counts_const (h : FunFacts g sel sub) {t : ℕ} (ht : funT0 δ ≤ t) :
    funK0 δ ≤ funCnt sel sub t 0 ∧ funK0 δ ≤ funCnt sel sub t 2 ∧
      funK0 δ ≤ funCnt sel sub t 3 := by
  have ht400 : 400 ≤ t := le_trans (funT0_ge δ) ht
  have hT2 : 2 * ⌈Real.exp (4 * (funJ δ : ℝ))⌉₊ ≤ funT0 δ := le_max_right _ _
  have hJ2 : 2 * ⌈Real.exp (4 * (funK0 δ : ℝ))⌉₊ ≤ funJ δ := le_max_right _ _
  have hJ196 : 196 ≤ funJ δ := le_max_left _ _
  have hlog : 4 * (funJ δ : ℝ) ≤ Real.log ((t / 2 : ℕ) : ℝ) :=
    lit_log_ge (le_trans hT2 ht)
  have hroot : ∀ a, funJ δ < uctCount sel t a := by
    intro a
    have h1 := h.fairRoot t ht400 a
    have h2 : (funJ δ : ℝ) < uctCount sel t a := by linarith
    exact_mod_cast h2
  have hKJ : funK0 δ ≤ funJ δ := by
    have h1 : (funK0 δ : ℝ) ≤ Real.exp (4 * (funK0 δ : ℝ)) := by
      have h3 := Real.add_one_le_exp (4 * (funK0 δ : ℝ))
      have h4 : (0 : ℝ) ≤ funK0 δ := Nat.cast_nonneg _
      linarith
    have h2 : funK0 δ ≤ ⌈Real.exp (4 * (funK0 δ : ℝ))⌉₊ := by
      exact_mod_cast le_trans h1 (Nat.le_ceil _)
    omega
  have hexit : ∀ e : Fin 2, funK0 δ ≤ funCnt sel sub t (funExit e) := by
    intro e
    rw [funCnt_exit]
    have hj := hroot 2
    have hf := h.fairSplit (uctCount sel t 2) (by omega) e
    have hl : 4 * (funK0 δ : ℝ) ≤ Real.log ((uctCount sel t 2 / 2 : ℕ) : ℝ) :=
      lit_log_ge (le_trans hJ2 hj.le)
    have h2 : (funK0 δ : ℝ) < uctCount sub (uctCount sel t 2) e := by linarith
    exact_mod_cast h2.le
  refine ⟨?_, hexit 0, hexit 1⟩
  rw [funCnt_zero]
  exact hKJ.trans (hroot 0).le

/-- **Step 2: intervals at the constant cutoff.** -/
theorem FunFacts.box_const (h : FunFacts g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {t : ℕ} (ht : funT0 δ ≤ t) :
    11 / 20 ≤ (funTab δ g sel sub t 0).1 ∧ (funTab δ g sel sub t 2).2 ≤ 9 / 20 ∧
      (funTab δ g sel sub t 3).2 ≤ 9 / 20 := by
  obtain ⟨c0, c2, c3⟩ := h.counts_const (δ := δ) ht
  have hK := funK0_pos δ
  have r0 := funRad_le_quarter hδ0 hδ1 c0
  have r2 := funRad_le_quarter hδ0 hδ1 c2
  have r3 := funRad_le_quarter hδ0 hδ1 c3
  rw [funTab_of_pos sel sub (hK.trans c0), funTab_of_pos sel sub (hK.trans c2),
    funTab_of_pos sel sub (hK.trans c3), funMu_zero, funMu_two, funMu_three]
  refine ⟨le_max_of_le_right (by linarith), (min_le_right _ _).trans (by linarith),
    (min_le_right _ _).trans (by linarith)⟩

/-- **Step 2: constant-time retirement of the dominated funnel.** -/
theorem FunFacts.retired (m : ℕ) (h : FunFacts g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg0 : 0 < g) (hg : g ≤ 1 / 4) :
    ∀ k, funT0 δ - 3 < k →
      (2 : Fin 3) ∉ (monRun true (monFunnelCirc m) (funBox δ g sel sub) k).act := by
  have hT := funT0_ge δ
  have hstep : (2 : Fin 3) ∉
      (monRun true (monFunnelCirc m) (funBox δ g sel sub) (funT0 δ - 3 + 1)).act := by
    rw [mem_monRun_act_succ]
    rintro ⟨-, hno⟩
    apply hno
    refine ⟨0, funnel_b_active m hg0 hg sel sub _, by decide, ?_⟩
    obtain ⟨b0, b2, b3⟩ := h.box_const (δ := δ) hδ0 hδ1 (t := 3 + (funT0 δ - 3)) (by omega)
    rw [funU_two, funL_zero]
    have hmax : max (funBox δ g sel sub (funT0 δ - 3) 2).2 (funBox δ g sel sub (funT0 δ - 3) 3).2
        ≤ 9 / 20 := max_le b2 b3
    have hb0 : 11 / 20 ≤ (funBox δ g sel sub (funT0 δ - 3) 0).1 := b0
    linarith
  intro k hk
  induction k, (show funT0 δ - 3 + 1 ≤ k from hk) using Nat.le_induction with
  | base => exact hstep
  | succ k _ ih => exact fun hmem => ih (by omega) (monRun_act_anti _ _ k hmem)

/-- **Step 3: `τ = Ω(m^{1/8})`.** -/
theorem FunFacts.horizon (h : FunFacts g sel sub) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) (hgdef : g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ))) (hg0 : 0 < g)
    (hg : g ≤ 1 / 4) {k : ℕ} (hs : funStops m δ g sel sub k 0) :
    64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < ((3 + k : ℕ) : ℝ) := by
  have hnb1 : 1 ≤ uctCount sel (3 + k) 0 := h.one_le (3 + k) (by omega) 0
  have hnbτ : uctCount sel (3 + k) 0 ≤ 3 + k := uctCount_le_time sel (3 + k) 0
  have hU : 4 / 5 - g ≤ (funBox δ g sel sub k 1).2 := by
    have := funTab_hi_ge (δ := δ) hg0.le (by linarith) sel sub (3 + k) 1
    rw [funMu_one] at this
    exact this
  have hstop := hs.2 1 (mem_univ _) (by decide)
  rw [funU_one, funL_zero] at hstop
  have hL : (funBox δ g sel sub k 0).1
      = max 0 (4 / 5 - hoeffdingWidth 4 δ (uctCount sel (3 + k) 0 : ℕ) / 2) := by
    show (funTab δ g sel sub (3 + k) 0).1 = _
    rw [funTab_of_pos sel sub (by rw [funCnt_zero]; exact hnb1), funMu_zero, funCnt_zero]
    rfl
  rw [hL] at hstop
  have hU' : 4 / 5 - 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) ≤ (funBox δ g sel sub k 1).2 := by
    rw [← hgdef]
    exact hU
  have hstop' : (funBox δ g sel sub k 1).2
      - max 0 (4 / 5 - hoeffdingWidth 4 δ (uctCount sel (3 + k) 0 : ℕ) / 2)
        ≤ 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) / 2 := by
    rw [← hgdef]
    exact hstop
  exact funnel_horizon_lower_m (M := 4) (by norm_num) hδ0 hδ1 (by exact_mod_cast hm) hnb1 hnbτ
    hU' hstop'

/-- **Step 3: certification has occurred by `T = m`.** -/
theorem facts_stops_at_m (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ a0 : ℝ, 2 ≤ a0 ∧ ∀ (m : ℕ) (a : ℝ), a0 ≤ a → (m : ℝ) = a ^ 16 → funT0 δ ≤ m →
      ∀ (sel : ℕ → Fin 3) (sub : ℕ → Fin 2), FunFacts (1 / (4 * a)) sel sub →
        funStops m δ (1 / (4 * a)) sel sub (m - 3) 0 := by
  refine ⟨max 2 (max (Real.log (2048 / δ)) (Real.exp ((Real.log (65536 / δ) + 1) / 2))),
    le_max_left _ _, ?_⟩
  intro m a ha0 hm hT sel sub h
  have ha : 2 ≤ a := le_trans (le_max_left _ _) ha0
  have hD1 : Real.log (2048 / δ) ≤ a :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha0
  have hD2 : Real.exp ((Real.log (65536 / δ) + 1) / 2) ≤ a :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha0
  have hapos : 0 < a := by linarith
  have hane : a ≠ 0 := hapos.ne'
  have hδne : δ ≠ 0 := hδ0.ne'
  have hD : Real.log (65536 / δ) + 1 ≤ 2 * Real.log a := by
    have := (Real.le_log_iff_exp_le hapos).mpr hD2
    linarith
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = 1 / (4 * a) := ⟨_, rfl⟩
  rw [← hgdef] at h ⊢
  have hg0 : 0 < g := by
    rw [hgdef]
    positivity
  have hg8 : g ≤ 1 / 8 := by
    rw [hgdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hg2 : g ^ 2 = 1 / (16 * a ^ 2) := by
    rw [hgdef]
    field_simp
    ring
  obtain ⟨s1, -, -, s4, -⟩ := fu_scale ha hm
  have hT400 := funT0_ge δ
  have hm3 : 3 ≤ m := by omega
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have e : 3 + (m - 3) = m := by omega
  have c1 := h.cntC m hm3
  have c2 := h.cntA m hm3
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = a ^ 3 := ⟨_, rfl⟩
  have ha2 : 4 ≤ a ^ 2 := by nlinarith
  have hP8 : 8 ≤ P := by
    rw [hP]
    nlinarith
  have hPa : 4 * a ≤ P := by
    rw [hP]
    nlinarith
  rw [← hP] at s4
  have hlogg : Real.log (1 + (m : ℝ)) / g ^ 2 ≤ 256 * P := by
    have e1 : Real.log (1 + (m : ℝ)) / g ^ 2 = 16 * a ^ 2 * Real.log (1 + (m : ℝ)) := by
      rw [hg2]
      field_simp
    rw [e1]
    calc 16 * a ^ 2 * Real.log (1 + (m : ℝ)) ≤ 16 * a ^ 2 * (16 * a) :=
          mul_le_mul_of_nonneg_left s1 (by positivity)
      _ = 256 * P := by rw [hP]; ring
  have hNa : (uctCount sel m 1 : ℝ) ≤ 1 + 256 * P := by linarith
  have hNC : (uctCount sel m 2 : ℝ) ≤ 1 + 45 * a := by
    have h9 : Real.log (1 + (m : ℝ)) / (3 / 5) ^ 2 ≤ 45 * a := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  have hsum : (uctCount sel m 0 : ℝ) + uctCount sel m 1 + uctCount sel m 2 = m := by
    have := uctCount_sum sel m
    rw [Fin.sum_univ_three] at this
    exact_mod_cast this
  have hNb : 7900 * P ≤ (uctCount sel m 0 : ℝ) := by linarith
  -- the direct action
  have hbrad : funRad δ (funCnt sel sub (3 + (m - 3)) 0) ≤ g / 2 := by
    rw [e, funCnt_zero]
    have hlog2 : Real.log (32 * 4 / (δ * g ^ 2)) ≤ 3 * a := by
      rw [hg2, show 32 * 4 / (δ * (1 / (16 * a ^ 2))) = 2048 / δ * a ^ 2 by
        field_simp
        ring, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have := Real.log_le_sub_one_of_pos hapos
      push_cast
      linarith
    have hx : 32 / g ^ 2 * Real.log (32 * 4 / (δ * g ^ 2)) ≤ (uctCount sel m 0 : ℝ) := by
      have e2 : 32 / g ^ 2 = 512 * a ^ 2 := by
        rw [hg2]
        field_simp
        ring
      rw [e2]
      calc 512 * a ^ 2 * Real.log (32 * 4 / (δ * g ^ 2)) ≤ 512 * a ^ 2 * (3 * a) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = 1536 * P := by rw [hP]; ring
        _ ≤ _ := by linarith
    have := width_inversion (M := 4) (by norm_num) hδ0 hδ1 hg0 (by linarith) hx
    unfold funRad
    linarith
  -- the near rival, on the window `[⌈m/2⌉, m]`
  have hhalf : (((m + 1) / 2 : ℕ) : ℝ) ≤ ((m : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := m + 1) (n := 2)
    push_cast at this
    linarith
  have hs0lo : (m : ℝ) / 2 ≤ (((m + 1) / 2 : ℕ) : ℝ) := by
    have h1 : m ≤ 2 * ((m + 1) / 2) := by omega
    have h2 : (m : ℝ) ≤ 2 * (((m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hs0hi : (((m + 1) / 2 : ℕ) : ℝ) ≤ m := by
    exact_mod_cast (by omega : (m + 1) / 2 ≤ m)
  have hs0pos : (0 : ℝ) < (((m + 1) / 2 : ℕ) : ℝ) := by linarith
  have hwin : 3 * (Real.log (1 + (m : ℝ)) / g ^ 2 + 1)
      < (m : ℝ) - (((m + 1) / 2 : ℕ) : ℝ) := by linarith
  have hriv := h.rival m (by omega) hwin
  have hLlo : 16 * Real.log a - Real.log 2 ≤ Real.log (((m + 1) / 2 : ℕ) : ℝ) := by
    have h3 : Real.log (a ^ 16 / 2) ≤ Real.log (((m + 1) / 2 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by rw [← hm]; exact hs0lo)
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h3
    push_cast at h3
    exact h3
  have hLhi : Real.log (((m + 1) / 2 : ℕ) : ℝ) ≤ 16 * a :=
    (Real.log_le_log hs0pos (by linarith)).trans s1
  have hN1 : 4 * a ^ 2 * Real.log (((m + 1) / 2 : ℕ) : ℝ) < (uctCount sel m 1 : ℝ) := by
    rw [hg2] at hriv
    have e3 : 4 * (1 / (16 * a ^ 2)) * (uctCount sel m 1 : ℝ)
        = (uctCount sel m 1 : ℝ) / (4 * a ^ 2) := by
      field_simp
      ring
    rw [e3, lt_div_iff₀ (by positivity)] at hriv
    linarith
  have harad : funRad δ (funCnt sel sub (3 + (m - 3)) 1) ≤ g := by
    rw [e, funCnt_one, hgdef]
    exact fu_rival_radius hδ0 hδ1.le ha hLlo hLhi hD hN1
  -- the exits
  obtain ⟨-, b2, b3⟩ := h.box_const (δ := δ) hδ0 hδ1 hT
  have hb1 : 1 ≤ funCnt sel sub (3 + (m - 3)) 0 := by
    rw [e, funCnt_zero]
    exact h.one_le m hm3 0
  have ha1 : 1 ≤ funCnt sel sub (3 + (m - 3)) 1 := by
    rw [e, funCnt_one]
    exact h.one_le m hm3 1
  exact funStops_of_radii hg0 (by linarith) hb1 hbrad ha1 harad (by rw [e]; exact b2)
    (by rw [e]; exact b3)

/-! ### Step 4 from the count facts -/

/-- A rollout through the funnel at a time `t ≥ t₀` strictly changes the interval of the
exit it reaches. -/
theorem FunFacts.tab_change (h : FunFacts g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {t : ℕ} (ht : funT0 δ ≤ t) (h2 : sel t = 2) :
    funTab δ g sel sub (t + 1) 2 ≠ funTab δ g sel sub t 2 ∨
      funTab δ g sel sub (t + 1) 3 ≠ funTab δ g sel sub t 3 := by
  obtain ⟨-, c2, c3⟩ := h.counts_const (δ := δ) ht
  have hterm : funTerm sel sub t = funExit (sub (uctCount sel t 2)) := by
    unfold funTerm
    rw [ite_eq_left h2]
  by_cases he : sub (uctCount sel t 2) = 0
  · have hz : funTerm sel sub t = 2 := by
      rw [hterm, he]
      rfl
    refine Or.inl (funTab_change_at hδ0 hδ1 sel sub (by rw [funMu_two]; norm_num) c2 ?_)
    unfold funCnt
    rw [uctCount_succ, ite_eq_left hz]
  · have hz : funTerm sel sub t = 3 := by
      rw [hterm]
      unfold funExit
      rw [ite_eq_right he]
    refine Or.inr (funTab_change_at hδ0 hδ1 sel sub (by rw [funMu_three]) c3 ?_)
    unfold funCnt
    rw [uctCount_succ, ite_eq_left hz]

open Classical in
/-- **Step 4: number of exit-changing updates.** -/
theorem FunFacts.changes_ge (h : FunFacts g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ K, funT0 δ - 3 ≤ K →
      uctCount sel (3 + K) 2 ≤ ((range K).filter (fun k =>
          funBox δ g sel sub (k + 1) 2 ≠ funBox δ g sel sub k 2 ∨
            funBox δ g sel sub (k + 1) 3 ≠ funBox δ g sel sub k 3)).card
        + uctCount sel (funT0 δ) 2 := by
  have hT := funT0_ge δ
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    have e : 3 + (funT0 δ - 3) = funT0 δ := by omega
    rw [e]
    exact Nat.le_add_left _ _
  | succ K hK ih =>
    have e : 3 + (K + 1) = 3 + K + 1 := rfl
    rw [e, uctCount_succ, Finset.range_add_one, Finset.filter_insert]
    by_cases h2 : sel (3 + K) = 2
    · have hch : funBox δ g sel sub (K + 1) 2 ≠ funBox δ g sel sub K 2 ∨
          funBox δ g sel sub (K + 1) 3 ≠ funBox δ g sel sub K 3 :=
        h.tab_change hδ0 hδ1 (t := 3 + K) (by omega) h2
      rw [ite_eq_left h2, ite_eq_left hch, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [ite_eq_right h2, add_zero]
      refine ih.trans (Nat.add_le_add_right ?_ _)
      split_ifs
      · exact Finset.card_le_card (Finset.subset_insert _ _)
      · exact le_rfl

/-- **Step 4, selective side.** -/
theorem FunFacts.selective_work (h : FunFacts g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg0 : 0 < g) (hg4 : g ≤ 1 / 4) {a : ℝ} (ha8 : 8 ≤ a) {m : ℕ} (ha16 : (m : ℝ) = a ^ 16)
    (rule : ℕ → ℕ → Bool) {τ : ℕ} (hτ3 : 3 ≤ τ) (hτm : τ ≤ m) :
    (funWork true m δ g rule sel sub τ : ℝ) ≤ (12 * ((funT0 δ - 3 : ℕ) : ℝ) + 42) * m := by
  have hapos : 0 < a := by linarith
  obtain ⟨s1, -, -, -, s5⟩ := fu_scale (by linarith : (2 : ℝ) ≤ a) ha16
  have hmR : (1 : ℝ) ≤ m := by
    rw [ha16]
    exact one_le_pow₀ (by linarith)
  have hm1 : 1 ≤ m := by exact_mod_cast hmR
  have hτR : (τ : ℝ) ≤ m := by exact_mod_cast hτm
  have hret := h.retired (δ := δ) m hδ0 hδ1 hg0 hg4
  have hfw := (funnel_work hm1 (funBox δ g sel sub) (g / 2) (τ - 3)).2 (funT0 δ - 3) hret
  have hsamp := funRollout_sum_le m rule sel sub τ
  have hNC : (uctCount sel τ 2 : ℝ) ≤ 46 * a := by
    have c1 := h.cntC τ hτ3
    have hlog : Real.log (1 + (τ : ℝ)) ≤ 16 * a :=
      (Real.log_le_log (by positivity) (by linarith)).trans s1
    have h9 : Real.log (1 + (τ : ℝ)) / (3 / 5) ^ 2 ≤ 45 * a := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  have hclog : ((Nat.clog 2 m : ℕ) : ℝ) + 2 ≤ 49 * a := by
    have h1 := monClog_le_log hm1
    have h2 : Real.log (2 * (m : ℝ)) = Real.log 2 + 16 * Real.log a := by
      rw [ha16, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have hl := Real.log_le_sub_one_of_pos hapos
    have hl2 := Real.log_two_lt_d9
    rw [h2] at h1
    linarith
  have hprod : 2 * (((Nat.clog 2 m : ℕ) : ℝ) + 2) * (uctCount sel τ 2 : ℝ) ≤ m := by
    have h1 : (((Nat.clog 2 m : ℕ) : ℝ) + 2) * (uctCount sel τ 2 : ℝ) ≤ 49 * a * (46 * a) :=
      mul_le_mul hclog hNC (Nat.cast_nonneg _) (by linarith)
    linarith [sq_nonneg a]
  have hK3 : ((τ - 3 : ℕ) : ℝ) ≤ τ := by exact_mod_cast Nat.sub_le τ 3
  have hW : (funWork true m δ g rule sel sub τ : ℝ)
      ≤ (5 * (τ : ℝ) + 2 * (((Nat.clog 2 m : ℕ) : ℝ) + 2) * (uctCount sel τ 2 : ℝ))
        + ((12 * ((funT0 δ - 3 : ℕ) : ℝ) + 12) * m + 16 * ((τ - 3 : ℕ) : ℝ) + 8) := by
    unfold funWork
    have := Nat.add_le_add hsamp hfw
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ ((funT0 δ - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Step 4, eager side.** -/
theorem FunFacts.eager_work (h : FunFacts g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {a : ℝ} (ha8 : 8 ≤ a) {m : ℕ} (ha16 : (m : ℝ) = a ^ 16)
    (rule : ℕ → ℕ → Bool) {τ : ℕ} (hτa : 64 / 9 * a ^ 2 < (τ : ℝ))
    (hloga : 4 * (funT0 δ : ℝ) ≤ Real.log a) :
    1 / 64 * (m : ℝ) * Real.log m ≤ funWork false m δ g rule sel sub τ := by
  have hapos : 0 < a := by linarith
  have hmR : (1 : ℝ) ≤ m := by
    rw [ha16]
    exact one_le_pow₀ (by linarith)
  have hm1 : 1 ≤ m := by exact_mod_cast hmR
  have hT400 := funT0_ge δ
  have hT0R : (0 : ℝ) ≤ funT0 δ := Nat.cast_nonneg _
  have hT0a : (funT0 δ : ℝ) ≤ a := by
    have h1 := Real.log_le_sub_one_of_pos hapos
    linarith
  have haa : a * 8 ≤ a * a := mul_le_mul_of_nonneg_left ha8 hapos.le
  have ha64 : 64 ≤ a ^ 2 := by nlinarith
  have hT0τ : funT0 δ < τ := by
    have : (funT0 δ : ℝ) < τ := by linarith [sq a]
    exact_mod_cast this
  have hfair := h.fairRoot τ (hT400.trans hT0τ.le) 2
  have hc : (τ : ℝ) ≤ 2 * ((τ / 2 : ℕ) : ℝ) + 1 := by
    have : τ ≤ 2 * (τ / 2) + 1 := by omega
    exact_mod_cast this
  have hLτ : 2 * Real.log a ≤ Real.log ((τ / 2 : ℕ) : ℝ) := by
    have h1 : Real.log (a ^ 2) ≤ Real.log ((τ / 2 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  have hNT0 : (uctCount sel (funT0 δ) 2 : ℝ) ≤ funT0 δ := by
    exact_mod_cast uctCount_le_time sel (funT0 δ) 2
  have hlogm : Real.log m = 16 * Real.log a := by
    rw [ha16, Real.log_pow]
    push_cast
    ring
  have hdiff : Real.log a / 4 ≤ (uctCount sel τ 2 : ℝ) - uctCount sel (funT0 δ) 2 := by
    linarith
  have hch := h.changes_ge hδ0 hδ1 (τ - 3) (by omega)
  have e : 3 + (τ - 3) = τ := by omega
  rw [e] at hch
  have hmonoC : uctCount sel (funT0 δ) 2 ≤ uctCount sel τ 2 :=
    uctCount_mono sel 2 hT0τ.le
  have hfw := (funnel_work hm1 (funBox δ g sel sub) (g / 2) (τ - 3)).1
  have hnat : m * (uctCount sel τ 2 - uctCount sel (funT0 δ) 2)
      ≤ monWork false (monFunnelCirc m) (funBox δ g sel sub) (g / 2) (τ - 3) :=
    (Nat.mul_le_mul_left m (Nat.sub_le_iff_le_add.mpr hch)).trans hfw
  have hreal : (m : ℝ) * ((uctCount sel τ 2 : ℝ) - uctCount sel (funT0 δ) 2)
      ≤ (funWork false m δ g rule sel sub τ : ℝ) := by
    have h1 : ((m * (uctCount sel τ 2 - uctCount sel (funT0 δ) 2) : ℕ) : ℝ)
        ≤ (funWork false m δ g rule sel sub τ : ℝ) := by
      unfold funWork
      exact_mod_cast hnat.trans (Nat.le_add_left _ _)
    rw [Nat.cast_mul, Nat.cast_sub hmonoC] at h1
    exact h1
  have hfin : (m : ℝ) * (Real.log a / 4)
      ≤ (m : ℝ) * ((uctCount sel τ 2 : ℝ) - uctCount sel (funT0 δ) 2) :=
    mul_le_mul_of_nonneg_left hdiff (by linarith)
  rw [hlogm]
  linarith

/-! ### The assembled statements -/

/-- The conclusion of `onpolicy_uct_funnel`, verbatim, for the constants `c`, `C`, the width
`m`, the gap `g` (with `ε = g/2`), the path rule `rule` and the selections `sel`, `sub`:

* the selective and the eager monitor expose the same output at every step;
* the selective monitor has retired the funnel action at every step after `funT0 δ - 3`;
* the common first stopping count `τ` exists, the stopping set there is `{b}`, and
  `(64/9) m^{1/8} < τ ≤ m`;
* `W_selective ≤ C m` and `W_eager ≥ c m log m`. -/
def FunnelConclusion (δ c C : ℝ) (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3)
    (sub : ℕ → Fin 2) : Prop :=
  (∀ k, (monQuery (g / 2) (funBox δ g sel sub k)
        (monRun true (monFunnelCirc m) (funBox δ g sel sub) k)).1
      = (monQuery (g / 2) (funBox δ g sel sub k)
        (monRun false (monFunnelCirc m) (funBox δ g sel sub) k)).1) ∧
  (∀ k, funT0 δ - 3 < k →
    (2 : Fin 3) ∉ (monRun true (monFunnelCirc m) (funBox δ g sel sub) k).act) ∧
  ∃ τ : ℕ, 3 ≤ τ ∧
    (∀ k, k < τ - 3 → (monQuery (g / 2) (funBox δ g sel sub k)
      (monRun false (monFunnelCirc m) (funBox δ g sel sub) k)).1.stops = ∅) ∧
    (monQuery (g / 2) (funBox δ g sel sub (τ - 3))
      (monRun false (monFunnelCirc m) (funBox δ g sel sub) (τ - 3))).1.stops = {0} ∧
    64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < τ ∧ τ ≤ m ∧
    (funWork true m δ g rule sel sub τ : ℝ) ≤ C * m ∧
    c * m * Real.log m ≤ funWork false m δ g rule sel sub τ

/-- **The theorem from the count facts.**  For `δ ∈ (0, 1)` there are `m₀`, `c > 0`, `C`
depending only on `δ` such that for `m ≥ m₀`, `g = (1/4) m^{-1/16}`, every path rule and
every pair of selection sequences satisfying `FunFacts`, the conclusion of
`onpolicy_uct_funnel` holds. -/
theorem onpolicy_of_facts (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (m0 : ℕ) (c C : ℝ), 0 < c ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g : ℝ, g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2),
        (0 < g → g ≤ 1 / 4 → FunFacts g sel sub) →
        FunnelConclusion δ c C m g rule sel sub := by
  classical
  obtain ⟨a0, ha02, Hstop⟩ := facts_stops_at_m hδ0 hδ1
  obtain ⟨T0, hT0def⟩ : ∃ T0 : ℕ, T0 = funT0 δ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = max a0 (max 8 (Real.exp (4 * (T0 : ℝ)))) := ⟨_, rfl⟩
  have hAa0 : a0 ≤ A := by rw [hA]; exact le_max_left _ _
  have hA8 : 8 ≤ A := by rw [hA]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAe : Real.exp (4 * (T0 : ℝ)) ≤ A := by
    rw [hA]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨⌈A ^ 16⌉₊, 1 / 64, 12 * ((T0 - 3 : ℕ) : ℝ) + 42, by norm_num, ?_⟩
  intro m hm g hgdef rule sel sub hfacts
  -- the scale `a = m^{1/16}`
  have hAm : A ^ 16 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hAm
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (m : ℝ) ^ (1 / 16 : ℝ) := ⟨_, rfl⟩
  have hAa : A ≤ a := by
    have h1 := Real.rpow_le_rpow (by positivity) hAm (by norm_num : (0 : ℝ) ≤ 1 / 16)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at h1
    norm_num at h1
    rw [ha]
    exact h1
  have ha16 : (m : ℝ) = a ^ 16 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
    norm_num
  have ha8 : 8 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hg' : g = 1 / (4 * a) := by
    rw [hgdef, Real.rpow_neg hmpos.le, ← ha]
    field_simp
  have hm8 : (m : ℝ) ^ (1 / 8 : ℝ) = a ^ 2 := by
    rw [ha, ← Real.rpow_two, ← Real.rpow_mul hmpos.le]
    norm_num
  have hg0 : 0 < g := by
    rw [hg']
    positivity
  have hg4 : g ≤ 1 / 4 := by
    rw [hg', div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h : FunFacts g sel sub := hfacts hg0 hg4
  have hT0R : (0 : ℝ) ≤ T0 := Nat.cast_nonneg _
  have hT0a : (T0 : ℝ) ≤ a := by
    have h1 := Real.add_one_le_exp (4 * (T0 : ℝ))
    linarith
  have hloga : 4 * (T0 : ℝ) ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le hapos]
    linarith
  have haa : a * 8 ≤ a * a := mul_le_mul_of_nonneg_left ha8 hapos.le
  have hm16 : a * a ≤ (m : ℝ) := by
    rw [ha16]
    have h2 : (1 : ℝ) ≤ a ^ 14 := one_le_pow₀ (by linarith)
    have h3 : a ^ 16 = a ^ 14 * (a * a) := by ring
    rw [h3]
    exact le_mul_of_one_le_left (by positivity) h2
  have ham : a ≤ (m : ℝ) := by linarith
  have hT0m : T0 ≤ m := by exact_mod_cast hT0a.trans ham
  have hT400 : 400 ≤ T0 := by
    rw [hT0def]
    exact funT0_ge δ
  have hm1 : 1 ≤ m := by omega
  -- the stopping time
  have hstopm : funStops m δ g sel sub (m - 3) 0 := by
    have h' : FunFacts (1 / (4 * a)) sel sub := by
      rw [← hg']
      exact h
    rw [hg']
    exact Hstop m a (hAa0.trans hAa) ha16 (by rw [← hT0def]; exact hT0m) sel sub h'
  have hex : ∃ k, ∃ b, funStops m δ g sel sub k b := ⟨m - 3, 0, hstopm⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Nat.find hex := ⟨_, rfl⟩
  have hκm : κ ≤ m - 3 := by
    rw [hκ]
    exact Nat.find_min' hex ⟨0, hstopm⟩
  obtain ⟨b, hb⟩ := Nat.find_spec hex
  rw [← hκ] at hb
  have hb0 : b = 0 := funStops_leader hg0 hg4 hb
  rw [hb0] at hb
  have hmin : ∀ k, k < κ → ∀ b', ¬ funStops m δ g sel sub k b' := by
    intro k hk b' hs
    rw [hκ] at hk
    exact Nat.find_min hex hk ⟨b', hs⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = 3 + κ := ⟨_, rfl⟩
  have hτκ : τ - 3 = κ := by omega
  have hτ3 : 3 ≤ τ := by omega
  have hτm : τ ≤ m := by omega
  rw [← hτκ] at hb hmin
  have hτlow : 64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < (τ : ℝ) := by
    have := h.horizon hδ0 hδ1.le hm1 hgdef hg0 hg4 hb
    have e : 3 + (τ - 3) = τ := by omega
    rw [e] at this
    exact this
  obtain ⟨hL, hU, hne⟩ := funnel_nested (δ := δ) m hδ0 hδ1.le hg0.le (by linarith) sel sub
  have hout := fun k => monRun_outputs (circ := monFunnelCirc m) (x := funBox δ g sel sub)
    hL hU hne (ε := g / 2) (by linarith) k
  have hret := h.retired (δ := δ) m hδ0 hδ1 hg0 hg4
  have hτa : 64 / 9 * a ^ 2 < (τ : ℝ) := by
    rw [hm8] at hτlow
    exact hτlow
  unfold FunnelConclusion
  refine ⟨fun k => (hout k).1, hret, τ, hτ3, ?_, ?_, hτlow, hτm, ?_, ?_⟩
  · intro k hk
    rw [(hout k).2]
    exact Set.eq_empty_iff_forall_notMem.mpr (fun b' hb' => hmin k hk b' hb')
  · rw [(hout (τ - 3)).2]
    exact Set.eq_singleton_iff_unique_mem.mpr
      ⟨hb, fun b' hb' => funStops_leader hg0 hg4 hb'⟩
  · rw [hT0def]
    exact h.selective_work hδ0 hδ1 hg0 hg4 ha8 ha16 rule hτ3 hτm
  · exact h.eager_work hδ0 hδ1 ha8 ha16 rule hτa (by rw [← hT0def]; exact hloga)

/-- **Theorem `thm:onpolicy-uct` / `thm:selective-separation`, local-UCT half, for the index
literally as in `eq:uct-index` with `N_t(v)` = number of earlier visits of `v`.**  Fix
`δ ∈ (0, 1)`.  There are a size `m₀` and constants `c > 0`, `C` depending only on `δ` such
that for every `m ≥ m₀`, with `g = (1/4) m^{-1/16}` and `ε = g/2`, for every recursive
literal-index UCT search (`c_uct = 1`) on the two-exit funnel of width `m` (every
tie-breaking at the root and at the split, every path rule inside the fans):

* the selective and the eager monitor expose the same output at every step;
* the selective monitor has retired the funnel action at every step after `funT0 δ - 3`;
* the common first stopping count `τ` exists, the stopping set there is `{b}`, and
  `(64/9) m^{1/8} < τ ≤ m`;
* `W_selective ≤ C m`;
* `W_eager ≥ c m log m`.

The conclusion is that of `onpolicy_uct_funnel` verbatim.  No value fact, count bound or
accounting inequality is assumed. -/
theorem onpolicy_uct_funnel_literal (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (m0 : ℕ) (c C : ℝ), 0 < c ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g : ℝ, g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2), LitFunnelSearch g sel sub →
        (∀ k, (monQuery (g / 2) (funBox δ g sel sub k)
              (monRun true (monFunnelCirc m) (funBox δ g sel sub) k)).1
            = (monQuery (g / 2) (funBox δ g sel sub k)
              (monRun false (monFunnelCirc m) (funBox δ g sel sub) k)).1) ∧
        (∀ k, funT0 δ - 3 < k →
          (2 : Fin 3) ∉ (monRun true (monFunnelCirc m) (funBox δ g sel sub) k).act) ∧
        ∃ τ : ℕ, 3 ≤ τ ∧
          (∀ k, k < τ - 3 → (monQuery (g / 2) (funBox δ g sel sub k)
            (monRun false (monFunnelCirc m) (funBox δ g sel sub) k)).1.stops = ∅) ∧
          (monQuery (g / 2) (funBox δ g sel sub (τ - 3))
            (monRun false (monFunnelCirc m) (funBox δ g sel sub) (τ - 3))).1.stops = {0} ∧
          64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < τ ∧ τ ≤ m ∧
          (funWork true m δ g rule sel sub τ : ℝ) ≤ C * m ∧
          c * m * Real.log m ≤ funWork false m δ g rule sel sub τ := by
  obtain ⟨m0, c, C, hc, H⟩ := onpolicy_of_facts hδ0 hδ1
  exact ⟨m0, c, C, hc, fun m hm g hg rule sel sub h =>
    H m hm g hg rule sel sub (fun hg0 hg4 => h.facts hg0 (by linarith))⟩

/-- **Both readings of `N_t(v)` in `eq:uct-index`.**  With one choice of `m₀`, `c`, `C`
(depending only on `δ`), the conclusion of `onpolicy_uct_funnel` holds for every recursive
UCT search with `c_uct = 1` on the two-exit funnel whose exploration bonus is
`√(log (1 + t) / N)` (`FunnelSearch`) or `√(log t / N)` (`LitFunnelSearch`), `t` being the
number of earlier visits of the node. -/
theorem onpolicy_uct_funnel_both_readings (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (m0 : ℕ) (c C : ℝ), 0 < c ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g : ℝ, g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2),
        (FunnelSearch g sel sub ∨ LitFunnelSearch g sel sub) →
        FunnelConclusion δ c C m g rule sel sub := by
  obtain ⟨m0, c, C, hc, H⟩ := onpolicy_of_facts hδ0 hδ1
  refine ⟨m0, c, C, hc, fun m hm g hg rule sel sub h => H m hm g hg rule sel sub ?_⟩
  intro hg0 hg4
  rcases h with h | h
  · exact facts_of_funnelSearch h hg0 (by linarith)
  · exact h.facts hg0 (by linarith)

/-! ### Local UCT at every internal vertex -/

section Fans

variable {Z : Type*}

/-- Terminal reached from a vertex of a circuit at the vertex's visit number `n`, when the
binary vertex with address `v` takes arm `arm v j` at its `j`-th visit.  Addresses: the
child of a unary vertex `v` is `v ++ [true]`, the two children of a binary vertex `v` are
`v ++ [true]` and `v ++ [false]`.  The visit number of a child is the number of earlier
visits of the parent that took the edge to it. -/
def fanLeaf (arm : List Bool → ℕ → Fin 2) : MaxCirc Z → List Bool → ℕ → Z
  | .term z, _, _ => z
  | .unary c, v, n => fanLeaf arm c (v ++ [true]) n
  | .bin c d, v, n =>
      if arm v n = 0 then fanLeaf arm c (v ++ [true]) (uctCount (arm v) n 0)
      else fanLeaf arm d (v ++ [false]) (uctCount (arm v) n 1)

/-- The decision taken `k` edges below a vertex on the path of its `n`-th visit (`true` =
first child). -/
def fanDec (arm : List Bool → ℕ → Fin 2) : MaxCirc Z → List Bool → ℕ → ℕ → Bool
  | .term _, _, _, _ => true
  | .unary _, _, _, 0 => true
  | .unary c, v, n, k + 1 => fanDec arm c (v ++ [true]) n k
  | .bin _ _, v, n, 0 => decide (arm v n = 0)
  | .bin c d, v, n, k + 1 =>
      if arm v n = 0 then fanDec arm c (v ++ [true]) (uctCount (arm v) n 0) k
      else fanDec arm d (v ++ [false]) (uctCount (arm v) n 1) k

/-- Every binary vertex of the circuit is a literal local UCT node (`c = 1`) on its own
visit clock; the empirical mean of an arm is the average of the rewards `r` of the terminals
reached by the earlier visits that took the arm. -/
def FanUCT (r : Z → ℝ) (arm : List Bool → ℕ → Fin 2) : MaxCirc Z → List Bool → Prop
  | .term _, _ => True
  | .unary c, v => FanUCT r arm c (v ++ [true])
  | .bin c d, v =>
      LitUCTRun 1 (fun j b => (∑ i ∈ (range j).filter (fun i => arm v i = b),
          r (fanLeaf arm (.bin c d) v i)) / uctCount (arm v) j b) (arm v) ∧
        FanUCT r arm c (v ++ [true]) ∧ FanUCT r arm d (v ++ [false])

theorem fanLeaf_onlyTerm {z : Z} (arm : List Bool → ℕ → Fin 2) :
    ∀ c : MaxCirc Z, MaxCirc.OnlyTerm z c → ∀ v n, fanLeaf arm c v n = z
  | .term _, h, _, _ => h
  | .unary c, h, v, n => fanLeaf_onlyTerm arm c h (v ++ [true]) n
  | .bin c d, h, v, n => by
      have h' : MaxCirc.OnlyTerm z c ∧ MaxCirc.OnlyTerm z d := h
      simp only [fanLeaf]
      split_ifs
      · exact fanLeaf_onlyTerm arm c h'.1 _ _
      · exact fanLeaf_onlyTerm arm d h'.2 _ _

/-- A path rule that follows the decisions `fanDec` reaches the terminal `fanLeaf`: the two
descriptions of the path of a visit agree, on every circuit. -/
theorem fanDec_walk (arm : List Bool → ℕ → Fin 2) (r : ℕ → Bool) :
    ∀ (c : MaxCirc Z) (v : List Bool) (n d0 : ℕ),
      (∀ k, r (d0 + k) = fanDec arm c v n k) → (c.monWalk r d0).1 = fanLeaf arm c v n
  | .term _, _, _, _, _ => rfl
  | .unary c, v, n, d0, h => by
      have ih := fanDec_walk arm r c (v ++ [true]) n (d0 + 1) (fun k => by
        have h1 := h (k + 1)
        simp only [fanDec] at h1
        rw [show d0 + 1 + k = d0 + (k + 1) by omega]
        exact h1)
      simp only [MaxCirc.monWalk, fanLeaf]
      exact ih
  | .bin c e, v, n, d0, h => by
      have h0 : r d0 = decide (arm v n = 0) := by
        have h1 := h 0
        simp only [fanDec, Nat.add_zero] at h1
        exact h1
      by_cases ha : arm v n = 0
      · have hr : r d0 = true := by rw [h0]; exact decide_eq_true ha
        have ih := fanDec_walk arm r c (v ++ [true]) (uctCount (arm v) n 0) (d0 + 1) (fun k => by
          have h1 := h (k + 1)
          simp only [fanDec, ite_eq_left ha] at h1
          rw [show d0 + 1 + k = d0 + (k + 1) by omega]
          exact h1)
        simp only [MaxCirc.monWalk, hr, Bool.cond_true, fanLeaf, ite_eq_left ha]
        exact ih
      · have hr : r d0 = false := by rw [h0]; exact decide_eq_false ha
        have ih := fanDec_walk arm r e (v ++ [false]) (uctCount (arm v) n 1) (d0 + 1) (fun k => by
          have h1 := h (k + 1)
          simp only [fanDec, ite_eq_right ha] at h1
          rw [show d0 + 1 + k = d0 + (k + 1) by omega]
          exact h1)
        simp only [MaxCirc.monWalk, hr, Bool.cond_false, fanLeaf, ite_eq_right ha]
        exact ih

/-- On a circuit whose only terminal is `z`, arms that are literal UCT runs for the
constant return `r z` at every address make every binary vertex a literal UCT node. -/
theorem fanUCT_of_onlyTerm (r : Z → ℝ) {z : Z} (arm : List Bool → ℕ → Fin 2)
    (harm : ∀ v, LitUCTRun 1 (fun j b => (∑ _i ∈ (range j).filter (fun i => arm v i = b), r z)
      / uctCount (arm v) j b) (arm v)) :
    ∀ (c : MaxCirc Z) (v : List Bool), MaxCirc.OnlyTerm z c → FanUCT r arm c v
  | .term _, _, _ => trivial
  | .unary c, v, h => fanUCT_of_onlyTerm r arm harm c (v ++ [true]) h
  | .bin c d, v, h => by
      have h' : MaxCirc.OnlyTerm z c ∧ MaxCirc.OnlyTerm z d := h
      refine ⟨?_, fanUCT_of_onlyTerm r arm harm c _ h'.1, fanUCT_of_onlyTerm r arm harm d _ h'.2⟩
      have := harm v
      simp only [fanLeaf_onlyTerm arm (.bin c d) h]
      exact this

/-- Number of unary vertices (bottom-layer parents in a fan). -/
def fanParents : MaxCirc Z → ℕ
  | .term _ => 0
  | .unary c => fanParents c + 1
  | .bin c d => fanParents c + fanParents d

theorem monFanZ_parents (z : Z) : ∀ d m, 1 ≤ m → m ≤ 2 ^ d → fanParents (monFanZ z d m) = m
  | 0, m, h1, h2 => by
      have : m = 1 := by
        rw [pow_zero] at h2
        omega
      subst this
      rfl
  | d + 1, m, h1, h2 => by
      unfold monFanZ
      split_ifs with hm
      · have : m = 1 := by omega
        subst this
        rfl
      · rw [pow_succ] at h2
        have a := monFanZ_parents z d ((m + 1) / 2) (by omega) (by omega)
        have b := monFanZ_parents z d (m / 2) (by omega) (by omega)
        show fanParents (monFanZ z d ((m + 1) / 2)) + fanParents (monFanZ z d (m / 2)) = m
        omega

end Fans

/-- **The graph family.**  For `m ≥ 1` the tree unfolding of the two-exit funnel
`monFunnelCirc m` has `6 m + 1` vertices (terminal occurrences included), and the fan above
each exit has exactly `m` bottom-layer parents, height at most `⌈log₂ m⌉ + 1`, and the exit
as its only terminal. -/
theorem funnel_graph {m : ℕ} (hm : 1 ≤ m) :
    (∑ a, (monFunnelCirc m a).monSize = 6 * m + 1) ∧
      ∀ e : Fin 2, fanParents (monFunnelFan m (funExit e)) = m ∧
        (monFunnelFan m (funExit e)).monHeight ≤ Nat.clog 2 m + 1 ∧
        MaxCirc.OnlyTerm (funExit e) (monFunnelFan m (funExit e)) :=
  ⟨monFunnelCirc_size hm, fun e =>
    ⟨monFanZ_parents _ _ m hm (Nat.le_pow_clog (by norm_num) m), monFanZ_height _ _ _,
      monFanZ_onlyTerm _ _ _⟩⟩

/-- Terminal reached by the `i`-th visit of the split: the split takes arm `sub i`, and the
root of that fan is at its visit number `N_{sub i}(i)`. -/
def splitLeaf (m : ℕ) (sub : ℕ → Fin 2) (arm : Fin 2 → List Bool → ℕ → Fin 2) (i : ℕ) : Fin 4 :=
  fanLeaf (arm (sub i)) (monFunnelFan m (funExit (sub i))) [] (uctCount sub i (sub i))

/-- Terminal reached by rollout `s` of the full search. -/
def fullTerm (m : ℕ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (arm : Fin 2 → List Bool → ℕ → Fin 2)
    (s : ℕ) : Fin 4 :=
  if sel s = 2 then splitLeaf m sub arm (uctCount sel s 2) else Fin.castSucc (sel s)

/-- **Local literal UCT at every internal vertex of the two-exit funnel of width `m`**
(`c = 1`).  `sel` are the root's selections, `sub` the split's, and `arm e v` those of the
vertex with address `v` in the fan above exit `e`, each indexed by the vertex's own visit
number.  The root, the split and every binary fan vertex maximise the literal index with
the empirical means of the rewards of the terminals reached through each edge.  (A unary
vertex has a single outgoing edge.) -/
structure FullFunnelSearch (m : ℕ) (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (arm : Fin 2 → List Bool → ℕ → Fin 2) : Prop where
  root : LitUCTRun 1 (fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a),
    funMu g (fullTerm m sel sub arm s)) / uctCount sel t a) sel
  split : LitUCTRun 1 (fun j e => (∑ i ∈ (range j).filter (fun i => sub i = e),
    funMu g (splitLeaf m sub arm i)) / uctCount sub j e) sub
  fans : ∀ e : Fin 2, FanUCT (funMu g) (arm e) (monFunnelFan m (funExit e)) []

theorem splitLeaf_eq (m : ℕ) (sub : ℕ → Fin 2) (arm : Fin 2 → List Bool → ℕ → Fin 2) (i : ℕ) :
    splitLeaf m sub arm i = funExit (sub i) :=
  fanLeaf_onlyTerm _ _ (monFanZ_onlyTerm _ _ _) _ _

theorem fullTerm_eq (m : ℕ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (arm : Fin 2 → List Bool → ℕ → Fin 2) (s : ℕ) :
    fullTerm m sel sub arm s = funTerm sel sub s := by
  unfold fullTerm funTerm
  rw [splitLeaf_eq]

variable {arm : Fin 2 → List Bool → ℕ → Fin 2} {m : ℕ}

/-- **Reduction.**  A search with local UCT at every internal vertex is a `LitFunnelSearch`:
the choices inside the fans do not change the terminal reached. -/
theorem FullFunnelSearch.lit (h : FullFunnelSearch m g sel sub arm) :
    LitFunnelSearch g sel sub := by
  refine ⟨?_, ?_⟩
  · have := h.root
    simp only [fullTerm_eq] at this
    exact this
  · have := h.split
    simp only [splitLeaf_eq] at this
    exact this

/-- The path rule induced by a full search: at rollout `s`, depth `0` is the split's
decision at its current visit number, and depth `k + 1` is the decision of the fan vertex
`k` edges below the root of the chosen fan, at that vertex's current visit number. -/
def fullRule (m : ℕ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (arm : Fin 2 → List Bool → ℕ → Fin 2)
    (s : ℕ) : ℕ → Bool
  | 0 => decide (sub (uctCount sel s 2) = 0)
  | k + 1 => fanDec (arm (sub (uctCount sel s 2)))
      (monFunnelFan m (funExit (sub (uctCount sel s 2)))) []
      (uctCount sub (uctCount sel s 2) (sub (uctCount sel s 2))) k

/-- The walk through the funnel DAG under the induced rule reaches the terminal of the
rollout. -/
theorem fullRule_walk (m : ℕ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (arm : Fin 2 → List Bool → ℕ → Fin 2) (s : ℕ) :
    ((monFunnelCirc m (sel s)).monWalk (fullRule m sel sub arm s) 0).1
      = fullTerm m sel sub arm s := by
  rw [fullTerm_eq]
  exact funTerm_walk m sel sub s _ rfl

/-- Inside the chosen fan, the walk under the induced rule is the path of the local UCT
decisions: it reaches `splitLeaf`. -/
theorem fullRule_fan (m : ℕ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (arm : Fin 2 → List Bool → ℕ → Fin 2) (s : ℕ) :
    ((monFunnelFan m (funExit (sub (uctCount sel s 2)))).monWalk (fullRule m sel sub arm s) 1).1
      = splitLeaf m sub arm (uctCount sel s 2) :=
  fanDec_walk _ _ _ _ _ 1 (fun k => by
    rw [show 1 + k = k + 1 by omega]
    rfl)

/-- Searches with local literal UCT at every internal vertex exist, for every width `m` and
gap `g`. -/
theorem exists_fullFunnelSearch (m : ℕ) (g : ℝ) :
    ∃ sel sub arm, FullFunnelSearch m g sel sub arm := by
  obtain ⟨sel, sub, h⟩ := exists_litFunnelSearch g
  have hrun : ∀ μ : ℝ, ∃ s : ℕ → Fin 2, LitUCTRun 1
      (fun j b => (∑ _i ∈ (range j).filter (fun i => s i = b), μ) / uctCount s j b) s :=
    fun μ => exists_litRun (ι := Fin 2) 1
      (fun s j b => (∑ _i ∈ (range j).filter (fun i => s i = b), μ) / uctCount s j b)
      (fun s s' t hss => mean_local (fun _ _ => μ) (fun _ _ _ _ => rfl) s s' t hss)
  choose run hrunspec using hrun
  refine ⟨sel, sub, fun e _ => run (funMu g (funExit e)), ?_, ?_, ?_⟩
  · have := h.root
    simp only [fullTerm_eq]
    exact this
  · have := h.split
    simp only [splitLeaf_eq]
    exact this
  · intro e
    exact fanUCT_of_onlyTerm (funMu g) _ (fun _ => hrunspec (funMu g (funExit e))) _ _
      (monFanZ_onlyTerm _ _ _)

/-- **`thm:onpolicy-uct`, local-UCT half, with literal local UCT at every internal vertex.**
For every search in which the root, the split and every binary vertex of both fans are
literal UCT nodes (`FullFunnelSearch`), the conclusion of `onpolicy_uct_funnel` holds with
the sampler following the induced path rule `fullRule`. -/
theorem onpolicy_uct_funnel_full (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (m0 : ℕ) (c C : ℝ), 0 < c ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g : ℝ, g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) →
      ∀ (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (arm : Fin 2 → List Bool → ℕ → Fin 2),
        FullFunnelSearch m g sel sub arm →
        FunnelConclusion δ c C m g (fullRule m sel sub arm) sel sub := by
  obtain ⟨m0, c, C, hc, H⟩ := onpolicy_of_facts hδ0 hδ1
  exact ⟨m0, c, C, hc, fun m hm g hg sel sub arm h =>
    H m hm g hg _ sel sub (fun hg0 hg4 => h.lit.facts hg0 (by linarith))⟩

end

end LiteralE2

end JointRootCert
