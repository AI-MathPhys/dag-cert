/-
Literal form of Proposition `prop:v2escape` (The family does not lower-bound all numerical
oracles).

`MonitorWork.lean` (`v2escape`) proves that the alias table gives the exact root-action
interval vector on the `m`-leaf graph, but its work `monAliasWork` is a formula: only the
preprocessing cost is computed by a program (`monAlias`).  This file closes the two gaps.

1. The alias monitor as executed costed programs, in the cost model of `CostModel.lean`
   (a program returns `(result, cost)`, the cost computed by the same recursion):
   `aliasBuild` (run `monAlias` on every root circuit, store the aliases and the terminal
   table), `aliasUpdate` (write one terminal interval, 1 unit), `aliasQuery` (read every
   action's interval through its alias, 1 unit per action).  A generic interface
   `IntervalImpl` (build / update / query, each returning its cost), its run `implState`
   along a sequence of terminal updates, its work `implWork` (build, every update, a query
   after the build and after every update) and its exactness `ExactOn`.
   `alias_escape`: on the `m`-leaf graph, along every update sequence, the alias outputs are
   the exact root-action interval vectors and equal the full monitor's complete interval
   vectors at every step, and the computed work for `K` updates is `3m + 4K + 4`.
2. The consequence.  `runUpd`: the terminal updates of the closed-loop run of
   `thm:v2separation` (`histTab` of the history changes at the observed terminal only,
   `updSeq_run`).  `PromotedLB δ α`: the full-monitor lower bound `W ≥ c·m^{1+α} log m` of
   `v2separation_literal`, claimed for every exact-interval implementation (total work:
   graph reading and disposal, all rollouts, and the implementation's monitor work, the
   same charges as `histWork`).  `v2escape_literal`: on that family the alias
   implementation is exact, agrees with the full monitor's interval vectors, and its total
   work is at most `(2 C₁ + 7) m`, while the full monitor's is at least `c_F m^{1+α} log m`.
   `not_promotedLB`, `not_promotedMonLB`: the promoted lower bound fails (for the total work
   and for the monitor work alone).
-/
import JointRootCert.LiteralE5

namespace JointRootCert

namespace LiteralF3

open Finset LiteralE5

noncomputable section

/-! ### The alias monitor as costed programs -/

section Alias

variable {A Z : Type*} [DecidableEq Z]

/-- State of the alias monitor: one alias (optional terminal) per root action, and the
terminal interval table. -/
structure AliasSt (A Z : Type*) where
  als : A → Option Z
  tab : Z → ℝ × ℝ

/-- Build: run the preprocessing `monAlias` on every root circuit (its returned cost is
charged) and store the aliases next to the initial terminal table. -/
def aliasBuild [Fintype A] (circ : A → MaxCirc Z) (x : Z → ℝ × ℝ) : AliasSt A Z × ℕ :=
  (⟨fun a => (monAlias (circ a)).1, x⟩, ∑ a, (monAlias (circ a)).2)

/-- Update: write the new interval of terminal `z` into the table; one write. -/
def aliasUpdate (z : Z) (v : ℝ × ℝ) (σ : AliasSt A Z) : AliasSt A Z × ℕ :=
  (⟨σ.als, Function.update σ.tab z v⟩, 1)

/-- Read the interval of action `a` through its alias; one read. -/
def aliasRead (σ : AliasSt A Z) (a : A) : Option (ℝ × ℝ) × ℕ :=
  ((σ.als a).map σ.tab, 1)

/-- Query: the complete root-action interval vector, one alias read per action. -/
def aliasQuery [Fintype A] (σ : AliasSt A Z) : (A → Option (ℝ × ℝ)) × ℕ :=
  (fun a => (aliasRead σ a).1, ∑ a, (aliasRead σ a).2)

end Alias

/-! ### Interval implementations and their runs -/

section Impl

variable {A Z : Type} [DecidableEq Z]

/-- An implementation that maintains root-action intervals: costed build, terminal update
and complete-vector query programs on a state type of its own. -/
structure IntervalImpl (A Z : Type) where
  St : Type
  build : (Z → ℝ × ℝ) → St × ℕ
  update : Z → ℝ × ℝ → St → St × ℕ
  query : St → (A → Option (ℝ × ℝ)) × ℕ

/-- The terminal tables along a sequence of terminal updates `u k = (z, new interval)`. -/
def updSeq (x0 : Z → ℝ × ℝ) (u : ℕ → Z × (ℝ × ℝ)) : ℕ → Z → ℝ × ℝ
  | 0 => x0
  | k + 1 => Function.update (updSeq x0 u k) (u k).1 (u k).2

/-- The implementation's state after the build and `k` updates. -/
def implState (I : IntervalImpl A Z) (x0 : Z → ℝ × ℝ) (u : ℕ → Z × (ℝ × ℝ)) : ℕ → I.St
  | 0 => (I.build x0).1
  | k + 1 => (I.update (u k).1 (u k).2 (implState I x0 u k)).1

/-- Monitor work for `K` updates: the build, every update, and a complete query after the
build and after every update; all costs are those returned by the programs. -/
def implWork (I : IntervalImpl A Z) (x0 : Z → ℝ × ℝ) (u : ℕ → Z × (ℝ × ℝ)) (K : ℕ) : ℕ :=
  (I.build x0).2 + ∑ k ∈ range K, (I.update (u k).1 (u k).2 (implState I x0 u k)).2
    + ∑ k ∈ range (K + 1), (I.query (implState I x0 u k)).2

/-- Exact-interval implementation along the first `K` updates: after the build and after
every update, the query returns the exact root-action interval vector of the current
table. -/
def ExactOn (I : IntervalImpl A Z) (circ : A → MaxCirc Z) (x0 : Z → ℝ × ℝ)
    (u : ℕ → Z × (ℝ × ℝ)) (K : ℕ) : Prop :=
  ∀ k ≤ K, (I.query (implState I x0 u k)).1 = fun a => some ((circ a).ival (updSeq x0 u k))

/-- The alias monitor as an interval implementation. -/
def aliasImpl [Fintype A] (circ : A → MaxCirc Z) : IntervalImpl A Z :=
  ⟨AliasSt A Z, aliasBuild circ, aliasUpdate, aliasQuery⟩

theorem aliasImpl_state [Fintype A] (circ : A → MaxCirc Z) (x0 : Z → ℝ × ℝ)
    (u : ℕ → Z × (ℝ × ℝ)) : ∀ k,
    (implState (aliasImpl circ) x0 u k : AliasSt A Z)
      = ⟨fun a => (monAlias (circ a)).1, updSeq x0 u k⟩
  | 0 => rfl
  | k + 1 => by
      show (aliasUpdate (u k).1 (u k).2 (implState (aliasImpl circ) x0 u k : AliasSt A Z)).1 = _
      rw [aliasImpl_state circ x0 u k]
      rfl

/-- The alias query output after `k` updates is the alias vector of the current table. -/
theorem aliasImpl_out [Fintype A] (circ : A → MaxCirc Z) (x0 : Z → ℝ × ℝ)
    (u : ℕ → Z × (ℝ × ℝ)) (k : ℕ) :
    ((aliasImpl circ).query (implState (aliasImpl circ) x0 u k)).1
      = monAliasVec circ (updSeq x0 u k) := by
  show (aliasQuery (implState (aliasImpl circ) x0 u k : AliasSt A Z)).1 = _
  rw [aliasImpl_state]
  rfl

/-- The computed work of the alias monitor for `K` updates. -/
theorem aliasImpl_work [Fintype A] (circ : A → MaxCirc Z) (x0 : Z → ℝ × ℝ)
    (u : ℕ → Z × (ℝ × ℝ)) (K : ℕ) :
    implWork (aliasImpl circ) x0 u K
      = ∑ a, (circ a).monSize + K + Fintype.card A * (K + 1) := by
  unfold implWork
  have hb : ((aliasImpl circ).build x0).2 = ∑ a, (circ a).monSize := by
    show ∑ a, (monAlias (circ a)).2 = _
    simp only [monAlias_cost]
  have hu : ∀ k, ((aliasImpl circ).update (u k).1 (u k).2
      (implState (aliasImpl circ) x0 u k)).2 = 1 := fun _ => rfl
  have hq : ∀ k, ((aliasImpl circ).query (implState (aliasImpl circ) x0 u k)).2
      = Fintype.card A := by
    intro k
    show ∑ a, (aliasRead (implState (aliasImpl circ) x0 u k : AliasSt A Z) a).2 = _
    simp [aliasRead]
  simp only [hb, hu, hq, sum_const, card_range, smul_eq_mul, mul_one]
  ring

/-- **Gap 1 (`prop:v2escape`, executed alias monitor).**  On the `m`-leaf graph, along
every initial table `x0` and every sequence `u` of terminal updates:

* after the build and after every update, the alias query returns the exact root-action
  interval vector (`ExactOn`, for every `K`);
* it equals the complete interval vector `(lo, hi)` stored by the full monitor (`monRun
  false`, all actions active) along the same tables, at every step;
* the work computed by the build, update and query programs for `K` updates, with a query
  after the build and after every update, is `3m + 4K + 4`. -/
theorem alias_escape {m : ℕ} (hm : 1 ≤ m) (x0 : Fin 3 → ℝ × ℝ)
    (u : ℕ → Fin 3 × (ℝ × ℝ)) :
    (∀ K, ExactOn (aliasImpl (monRootCirc m)) (monRootCirc m) x0 u K) ∧
    (∀ k (a : Fin 3),
      ((aliasImpl (monRootCirc m)).query (implState (aliasImpl (monRootCirc m)) x0 u k)).1 a
        = some ((monRun false (monRootCirc m) (updSeq x0 u) k).lo (updSeq x0 u k) a,
            (monRun false (monRootCirc m) (updSeq x0 u) k).hi (updSeq x0 u k) a)) ∧
    ∀ K, implWork (aliasImpl (monRootCirc m)) x0 u K = 3 * m + 4 * K + 4 := by
  obtain ⟨h1, -, h3, -⟩ := v2escape hm
  refine ⟨fun K k _ => ?_, fun k a => ?_, fun K => ?_⟩
  · rw [aliasImpl_out]
    funext a
    exact h1 _ a
  · rw [aliasImpl_out]
    exact h3 (updSeq x0 u) k a
  · rw [aliasImpl_work, monRootCirc_size hm, Fintype.card_fin]
    ring

end Impl

/-! ### The terminal updates of the closed-loop run -/

/-- One observation changes the terminal table only at the observed terminal. -/
theorem histTab_cons (δ : ℝ) (e : Entry) (h : Hist) :
    histTab δ (e :: h) = Function.update (histTab δ h) e.2.1 (histTab δ (e :: h) e.2.1) := by
  funext z
  by_cases hz : z = e.2.1
  · subst hz
    simp
  · rw [Function.update_of_ne hz]
    have hne : ¬ e.2.1 = z := fun h' => hz h'.symm
    have hc : cntZ (e :: h) z = cntZ h z := by
      show cntZ h z + (if e.2.1 = z then 1 else 0) = _
      simp only [hne, ite_false, add_zero]
    have hs : sumZ (e :: h) z = sumZ h z := by
      show sumZ h z + (if e.2.1 = z then e.2.2 else 0) = _
      simp only [hne, ite_false, add_zero]
    unfold histTab
    rw [hc, hs]

section Run

variable (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3)

local notation "FH" => freeH m g rule pick

local notation "NE" => nextEntry m g rule pick

/-- The uninformative box `[0,1]` at every terminal. -/
def box01 : Fin 3 → ℝ × ℝ := fun _ => (0, 1)

/-- The `k`-th terminal update of the run: the terminal observed at step `k` and its new
interval. -/
def runUpd (δ : ℝ) (k : ℕ) : Fin 3 × (ℝ × ℝ) :=
  ((NE (FH k)).2.1, histTab δ (FH (k + 1)) (NE (FH k)).2.1)

/-- The tables produced by the run's terminal updates from the box are the run's terminal
tables. -/
theorem updSeq_run (δ : ℝ) : ∀ k, updSeq box01 (runUpd m g rule pick δ) k = histTab δ (FH k)
  | 0 => by
      funext z
      show ((0 : ℝ), (1 : ℝ)) = histTab δ [] z
      simp [histTab, cntZ]
  | k + 1 => by
      show Function.update (updSeq box01 (runUpd m g rule pick δ) k)
        (NE (FH k)).2.1 (histTab δ (FH (k + 1)) (NE (FH k)).2.1) = histTab δ (NE (FH k) :: FH k)
      rw [updSeq_run δ k, histTab_cons δ (NE (FH k)) (FH k)]
      rfl

/-- The table sequence the full monitor processes in the loop is the run's table sequence. -/
theorem histSeq_eq_histTab (δ : ℝ) {k t : ℕ} (hk : k ≤ t) :
    histSeq δ (FH t) k = histTab δ (FH k) := by
  rw [histSeq_free m g rule pick δ hk, histTab_free m g rule pick δ k]
  rfl

/-- The controller with the full monitor is running up to `τ` observations on the continued
trace and halts after `τ` observations. -/
def StopsAt (δ : ℝ) (τ : ℕ) : Prop :=
  (∀ t ≤ τ, closedLoop m g rule pick false δ t = ⟨FH t, .running⟩) ∧
    ∃ a, closedLoop m g rule pick false δ (τ + 1) = ⟨FH τ, .stopped a⟩

/-- Total work of an interval implementation on the run stopped after `τ` observations,
with the charges of `histWork`: reading, initializing and disposing of the graph, every
rollout (forced ones included), and the implementation's monitor work along the run's `τ`
terminal updates. -/
def implHistWork (I : IntervalImpl (Fin 3) (Fin 3)) (δ : ℝ) (τ : ℕ) : ℕ :=
  2 * ∑ a, (monRootCirc m a).monSize + rollCost m rule (FH τ)
    + implWork I box01 (runUpd m g rule pick δ) τ

theorem rollCost_ge (τ : ℕ) : 5 * τ ≤ rollCost m rule (FH τ) := by
  rw [rollCost_free m g rule pick τ]
  have h : ∑ _u ∈ range τ, 5 ≤ ∑ u ∈ range τ, monRollout m rule u (freeSel m g rule pick u) :=
    sum_le_sum (fun u _ => by unfold monRollout; omega)
  simpa [mul_comm] using h

end Run

/-! ### The promoted lower bound and its failure -/

/-- **The promoted lower bound.**  The full-monitor bound `W_full ≥ c·m^{1+α} log m` of
`thm:v2separation`, claimed for every exact-interval implementation: for all large `m`,
`g = m^{-α}`, every path rule and tie-breaking, the stopping count `τ` of the closed loop,
and every implementation that is exact along the run's `τ` terminal updates from the box,
its total work (`implHistWork`) is at least `c·m^{1+α} log m`. -/
def PromotedLB (δ α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-α) →
    ∀ (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3), IsPuctPick pick →
    ∀ τ : ℕ, StopsAt m g rule pick δ τ →
    ∀ I : IntervalImpl (Fin 3) (Fin 3),
      ExactOn I (monRootCirc m) box01 (runUpd m g rule pick δ) τ →
      c * ((m : ℝ) ^ (1 + α) * Real.log m) ≤ implHistWork m g rule pick I δ τ

/-- The same, for the monitor work alone (`implWork`). -/
def PromotedMonLB (δ α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-α) →
    ∀ (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3), IsPuctPick pick →
    ∀ τ : ℕ, StopsAt m g rule pick δ τ →
    ∀ I : IntervalImpl (Fin 3) (Fin 3),
      ExactOn I (monRootCirc m) box01 (runUpd m g rule pick δ) τ →
      c * ((m : ℝ) ^ (1 + α) * Real.log m) ≤ implWork I box01 (runUpd m g rule pick δ) τ

/-- **Proposition `prop:v2escape`, literal form, on the family of `thm:v2separation`.**
Fix `δ ∈ (0, 1/2]`, `α ∈ (0, 1/2)`.  There are `m₀` and constants `C, c_F > 0` such that for
every `m ≥ m₀`, `g = m^{-α}`, path rule and tie-breaking, the closed loop with the full
monitor stops after some `τ` observations (`StopsAt`) and:

* the full monitor's total work is at least `c_F m^{1+α} log m` (`v2separation_literal`);
* the alias implementation is exact along the run's `τ` terminal updates from the box;
* at every step `k ≤ τ` its output equals the complete interval vector of the full monitor
  in the loop (`monRun false` along `histSeq`);
* its monitor work is `3m + 4τ + 4`, and its total work (same charges as `histWork`) is at
  most `C m`. -/
theorem v2escape_literal {δ α : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α < 1 / 2) :
    ∃ (m0 : ℕ) (C cF : ℝ), 0 < C ∧ 0 < cF ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-α) →
      ∀ (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3), IsPuctPick pick →
      ∃ τ : ℕ, StopsAt m g rule pick δ τ ∧
        cF * ((m : ℝ) ^ (1 + α) * Real.log m)
          ≤ histWork false m δ (g / 2) rule (freeH m g rule pick τ) ∧
        ExactOn (aliasImpl (monRootCirc m)) (monRootCirc m) box01 (runUpd m g rule pick δ) τ ∧
        (∀ k ≤ τ, ∀ a : Fin 3,
          ((aliasImpl (monRootCirc m)).query
            (implState (aliasImpl (monRootCirc m)) box01 (runUpd m g rule pick δ) k)).1 a
          = some ((monRun false (monRootCirc m) (histSeq δ (freeH m g rule pick τ)) k).lo
                (histSeq δ (freeH m g rule pick τ) k) a,
              (monRun false (monRootCirc m) (histSeq δ (freeH m g rule pick τ)) k).hi
                (histSeq δ (freeH m g rule pick τ) k) a)) ∧
        implWork (aliasImpl (monRootCirc m)) box01 (runUpd m g rule pick δ) τ
          = 3 * m + 4 * τ + 4 ∧
        (implHistWork m g rule pick (aliasImpl (monRootCirc m)) δ τ : ℝ) ≤ C * m := by
  obtain ⟨m0, T, cτ, Cτ, cH, CH, C1, cF, CF, -, -, hC1, hcF, H⟩ :=
    v2separation_literal hδ0 hδ hα0 hα
  refine ⟨max m0 1, 2 * C1 + 7, cF, by linarith, hcF, ?_⟩
  intro m hm g hg rule pick hpick
  have hm0 : m0 ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨tc, τ, -, SB⟩ := H m hm0 g hg rule pick hpick
  obtain ⟨hex, -, hwork⟩ := alias_escape hm1 box01 (runUpd m g rule pick δ)
  obtain ⟨-, -, h3, -⟩ := v2escape (m := m) hm1
  refine ⟨τ, ⟨fun t ht => SB.run.running false t ht,
    ⟨0, SB.run.halted false (τ + 1) (by omega)⟩⟩, SB.full_lower, hex τ, ?_, hwork τ, ?_⟩
  · intro k hk a
    rw [aliasImpl_out, updSeq_run, ← histSeq_eq_histTab m g rule pick δ hk]
    exact h3 (histSeq δ (freeH m g rule pick τ)) k a
  · have hR := rollCost_ge m g rule pick τ
    have hsz := monRootCirc_size hm1
    have hW : implHistWork m g rule pick (aliasImpl (monRootCirc m)) δ τ
        ≤ 2 * histWork true m δ (g / 2) rule (freeH m g rule pick τ) + 3 * m + 4 := by
      unfold implHistWork histWork
      rw [hwork τ]
      omega
    have hWR : (implHistWork m g rule pick (aliasImpl (monRootCirc m)) δ τ : ℝ)
        ≤ 2 * (histWork true m δ (g / 2) rule (freeH m g rule pick τ) : ℝ) + 3 * m + 4 := by
      exact_mod_cast hW
    have hsel := SB.sel_upper
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    nlinarith

/-- For every `K` and `n₀` there is `m ≥ n₀` with `K·m < m^{1+α} log m`. -/
theorem exists_large {α : ℝ} (hα0 : 0 < α) (K : ℝ) (n0 : ℕ) :
    ∃ m : ℕ, n0 ≤ m ∧ K * m < (m : ℝ) ^ (1 + α) * Real.log m := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = max 1 (K + 1) := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := hX ▸ le_max_left _ _
  have hXK : K + 1 ≤ X := hX ▸ le_max_right _ _
  refine ⟨max (max n0 3) ⌈X ^ (1 / α)⌉₊, le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  set m := max (max n0 3) ⌈X ^ (1 / α)⌉₊
  have hm3 : (3 : ℝ) ≤ m := by
    have : 3 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by linarith
  have hXm : X ^ (1 / α) ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
  have hXa : X ≤ (m : ℝ) ^ α := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hXm hα0.le
    rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hα0.ne', Real.rpow_one] at h1
    exact h1
  have hℓ1 : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hmpos]
    have := Real.exp_one_lt_d9
    linarith
  have hsplit : (m : ℝ) ^ (1 + α) = m * (m : ℝ) ^ α := by
    rw [Real.rpow_add hmpos, Real.rpow_one]
  rw [hsplit]
  have hpa : 0 < (m : ℝ) ^ α := by linarith
  have h2 : (m : ℝ) * (m : ℝ) ^ α ≤ (m : ℝ) * (m : ℝ) ^ α * Real.log m := by
    nlinarith [mul_pos hmpos hpa]
  nlinarith

/-- **`prop:v2escape`, second sentence.**  The full-monitor lower bound of
`thm:v2separation` cannot be promoted to a lower bound on the total work of every
exact-interval implementation: `PromotedLB δ α` is false for every `δ ∈ (0, 1/2]`,
`α ∈ (0, 1/2)`.  Witness: the alias implementation, whose total work is `O(m)`
(`v2escape_literal`). -/
theorem not_promotedLB {δ α : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α < 1 / 2) : ¬ PromotedLB δ α := by
  rintro ⟨c, hc, m1, HP⟩
  obtain ⟨m0, C, cF, hC, -, H⟩ := v2escape_literal hδ0 hδ hα0 hα
  obtain ⟨m, hm, hlt⟩ := exists_large hα0 (C / c) (max m0 m1)
  obtain ⟨pick, hpick⟩ := exists_isPuctPick
  let rule : ℕ → ℕ → Bool := fun _ _ => false
  obtain ⟨τ, hstop, -, hex, -, -, hW⟩ :=
    H m (le_trans (le_max_left _ _) hm) _ rfl rule pick hpick
  have hlb := HP m (le_trans (le_max_right _ _) hm) _ rfl rule pick hpick τ hstop _ hex
  have h1 : C * m < c * ((m : ℝ) ^ (1 + α) * Real.log m) := by
    have := mul_lt_mul_of_pos_left hlt hc
    rw [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at this
    exact this
  linarith

/-- The same for the monitor work alone. -/
theorem not_promotedMonLB {δ α : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α < 1 / 2) : ¬ PromotedMonLB δ α := by
  rintro ⟨c, hc, m1, HP⟩
  refine not_promotedLB hδ0 hδ hα0 hα ⟨c, hc, m1, ?_⟩
  intro m hm g hg rule pick hpick τ hstop I hex
  have h := HP m hm g hg rule pick hpick τ hstop I hex
  have hle : (implWork I box01 (runUpd m g rule pick δ) τ : ℝ)
      ≤ implHistWork m g rule pick I δ τ := by
    unfold implHistWork
    push_cast
    have : (0 : ℝ) ≤ 2 * ∑ a, ((monRootCirc m a).monSize : ℝ)
      + (rollCost m rule (freeH m g rule pick τ) : ℝ) := by positivity
    linarith
  linarith

end

end LiteralF3

end JointRootCert
