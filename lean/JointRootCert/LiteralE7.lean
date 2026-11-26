/-
Appendix E, second-round gaps (part 1).

* `thm:ta-core` (Wide Common-Core Support Compilation Cost) under the literal index of
  `eq:uct-index`.  `LiteralE1.ta_core_literal` assumes `CoreSearch` (root index
  `Q + 2 √(log (1 + t) / N)`, as in the manuscript's proof).  Here the root may instead use
  `Q + 2 √(log t / N)` with `t = N_t(root)` the number of previous visits of the root
  (`LitCoreSearch`, built on `LiteralE2.LitUCTRun`).  `ta_core_both_readings` states every
  clause of `ta_core_literal` for a search satisfying `CoreSearch ∨ LitCoreSearch`.
  The proof goes through the three facts about a search that the argument uses
  (`CoreFacts`: the terminal reached is the walk of the selected action, every action is
  tried once in the first `r + 1` rollouts, a losing action has
  `N(t) ≤ 1 + 4 log (1 + t)`); both readings satisfy them (`CoreSearch.facts`,
  `LitCoreSearch.facts`); the chain `core_stops_by`, `ta_core`, `ta_core_coupled`,
  `ta_core_literal` is re-proved from `CoreFacts` with the same constants.
  `exists_litCoreSearch`: literal searches exist for every path rule.

* `cor:v2countscales` (Fixed gaps versus a shrinking gap), `eq:v2shrinking`.  The manuscript
  states the two-sided bound "whenever `g √t ≥ 4Λ`" (for `t ≥ K`, the times at which the
  rule runs).  `RootPUCT.lean` proves it with the extra hypothesis `t ≥ 2K`.
  - `count_shrinking_gap_small`: the bound holds for `K ≤ t < 2K` whenever
    `K λ_i ≤ 8 √3 Λ` (for instance all `λ_j` equal, or `K ≤ 13`).
    `count_shrinking_gap_ext` combines both ranges.
  - `v2shrinking_counterexample`: the statement as written is FALSE in general.  With
    `K = 36` arms, `λ_0 = 1`, `λ_j = 1/350` (`j ≠ 0`, so `Λ = 11/10`), `μ_0 = 0`,
    `μ_j = 11/15` (`j ≠ 0`), the arm `0` has gap `g = 11/15`, `g √36 = 4Λ`, and at
    `t = K = 36` every trace has `n_0(36) = 1`, while the lower bound of `eq:v2shrinking`
    requires `n_0(36) > 45/(11√3) - 1 > 1.36`.  All rewards lie in `[0, 1]`.
-/
import JointRootCert.LiteralE1
import JointRootCert.LiteralE2
import JointRootCert.RootPUCT

namespace JointRootCert
namespace LiteralE7

open Finset
open LiteralE

noncomputable section

/-! ## 1. `thm:ta-core` under the literal index -/

section TaCore

variable (r : ℕ) [NeZero r]

/-- **UCT search on the common-core DAG with the literal index** of `eq:uct-index`: as
`CoreSearch`, but the root selects a maximiser of `Q + 2 √(log t / N)`, where `t` is the
number of previous visits of the root (`LiteralE2.litIndex`). -/
structure LitCoreSearch (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r) :
    Prop where
  reach : ∀ s, zt s = ((coreAct r (sel s)).uctWalk (rule s) 0).1
  uct : LiteralE2.LitUCTRun 2 (fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a),
    coreReward r (zt s)) / uctCount sel t a) sel

/-- The facts about a search on the common-core DAG used by the proof of `thm:ta-core`. -/
structure CoreFacts (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r) :
    Prop where
  reach : ∀ s, zt s = ((coreAct r (sel s)).uctWalk (rule s) 0).1
  forced : ∀ i, uctCount sel (r + 1) i = 1
  lose : ∀ t, r + 1 ≤ t → ∀ i : Fin r,
    (uctCount sel t (Fin.castSucc i) : ℝ) ≤ 1 + 4 * Real.log (1 + t)

variable {r} {rule : ℕ → ℕ → Bool} {sel : ℕ → Fin (r + 1)} {zt : ℕ → CoreZ r}

theorem reward_of_reach (hr : ∀ s, zt s = ((coreAct r (sel s)).uctWalk (rule s) 0).1) (s : ℕ) :
    coreReward r (zt s) = coreMu r (sel s) := by
  rw [hr]
  exact MaxCirc.uctWalk_mem (P := fun z => coreReward r z = coreMu r (sel s)) _ _ 0
    (coreAct_reward r (sel s))

theorem Q_of_reach (hr : ∀ s, zt s = ((coreAct r (sel s)).uctWalk (rule s) 0).1) {t : ℕ}
    {a : Fin (r + 1)} (hpos : 1 ≤ uctCount sel t a) :
    (∑ s ∈ (range t).filter (fun s => sel s = a), coreReward r (zt s)) / uctCount sel t a
      = coreMu r a := by
  have hs : ∑ s ∈ (range t).filter (fun s => sel s = a), coreReward r (zt s)
      = uctCount sel t a * coreMu r a := by
    rw [Finset.sum_congr rfl (fun s hs => by
      rw [reward_of_reach hr s, (Finset.mem_filter.mp hs).2] :
      ∀ s ∈ (range t).filter (fun s => sel s = a), coreReward r (zt s) = coreMu r a)]
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  have hne : (uctCount sel t a : ℝ) ≠ 0 := by exact_mod_cast (by omega : uctCount sel t a ≠ 0)
  rw [hs, mul_div_cancel_left₀ _ hne]

/-- The root of a literal search is a literal UCT node with the deterministic means. -/
theorem LitCoreSearch.run (h : LitCoreSearch r rule sel zt) :
    LiteralE2.LitUCTRun 2 (fun _ a => coreMu r a) sel where
  forced := h.uct.forced
  greedy := by
    intro t ht j
    have := h.uct.greedy t ht j
    rw [Q_of_reach h.reach (h.uct.one_le j ht), Q_of_reach h.reach (h.uct.one_le (sel t) ht)]
      at this
    exact this

theorem CoreSearch.facts (h : CoreSearch r rule sel zt) : CoreFacts r rule sel zt := by
  refine ⟨h.reach, fun i => by simpa using h.uct.forced i, ?_⟩
  intro t ht i
  have hcard : Fintype.card (Fin (r + 1)) ≤ t := by rw [Fintype.card_fin]; exact ht
  have hlog : 0 ≤ Real.log (1 + (t : ℝ)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith)
  have hlast : coreMu r (Fin.last r) = 1 := by simp [coreMu]
  have hmu : coreMu r (Fin.castSucc i) = 0 := by simp [coreMu]
  have := h.run.count_le (by norm_num) (i := Fin.castSucc i) (star := Fin.last r) (u0 := 0)
    (b := 1) (by norm_num) (fun _ => le_of_eq hmu) (fun _ => le_of_eq hlast.symm) hcard
  refine this.trans (max_le (by linarith) (le_of_eq ?_))
  norm_num

theorem LitCoreSearch.facts (h : LitCoreSearch r rule sel zt) : CoreFacts r rule sel zt := by
  refine ⟨h.reach, fun i => by simpa using h.uct.forced i, ?_⟩
  intro t ht i
  have hcard : Fintype.card (Fin (r + 1)) ≤ t := by rw [Fintype.card_fin]; exact ht
  have hlog : 0 ≤ Real.log (1 + (t : ℝ)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith)
  have hlast : coreMu r (Fin.last r) = 1 := by simp [coreMu]
  have hmu : coreMu r (Fin.castSucc i) = 0 := by simp [coreMu]
  have := h.run.count_le (by norm_num) (i := Fin.castSucc i) (star := Fin.last r) (u0 := 0)
    (b := 1) (by norm_num) (fun _ => le_of_eq hmu) (fun _ => le_of_eq hlast.symm) hcard
  refine this.trans (max_le (by linarith) (le_of_eq ?_))
  norm_num

/-- Literal searches on the common-core DAG exist for every path rule. -/
theorem exists_litCoreSearch (r : ℕ) [NeZero r] (rule : ℕ → ℕ → Bool) :
    ∃ sel zt, LitCoreSearch r rule sel zt := by
  let ztOf : (ℕ → Fin (r + 1)) → ℕ → CoreZ r :=
    fun sel s => ((coreAct r (sel s)).uctWalk (rule s) 0).1
  obtain ⟨sel, hsel⟩ := LiteralE2.exists_litRun (ι := Fin (r + 1)) 2
    (fun sel t a => (∑ s ∈ (range t).filter (fun s => sel s = a), coreReward r (ztOf sel s))
      / uctCount sel t a)
    (by
      intro sel sel' t hss
      funext a
      have hf : (range t).filter (fun s => sel s = a) = (range t).filter (fun s => sel' s = a) :=
        Finset.filter_congr (fun s hs => by rw [hss s (mem_range.mp hs)])
      have hc : uctCount sel t a = uctCount sel' t a := by
        unfold uctCount
        rw [hf]
      show (∑ s ∈ (range t).filter (fun s => sel s = a), coreReward r (ztOf sel s))
          / (uctCount sel t a : ℝ)
        = (∑ s ∈ (range t).filter (fun s => sel' s = a), coreReward r (ztOf sel' s))
          / (uctCount sel' t a : ℝ)
      rw [hc, hf]
      congr 1
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hs' : s < t := mem_range.mp (Finset.mem_filter.mp hs).1
      show coreReward r (((coreAct r (sel s)).uctWalk (rule s) 0).1)
        = coreReward r (((coreAct r (sel' s)).uctWalk (rule s) 0).1)
      rw [hss s hs'])
  exact ⟨sel, ztOf sel, fun _ => rfl, hsel⟩

theorem CoreFacts.one_le (h : CoreFacts r rule sel zt) (i : Fin (r + 1)) {t : ℕ}
    (ht : r + 1 ≤ t) : 1 ≤ uctCount sel t i := by
  have := uctCount_mono sel i ht
  rwa [h.forced] at this

/-- `N_win(t) ≥ t - r (1 + 4 log (1 + t))`, from the facts. -/
theorem CoreFacts.win_count_ge (h : CoreFacts r rule sel zt) {t : ℕ} (ht : r + 1 ≤ t) :
    (t : ℝ) - r * (1 + 4 * Real.log (1 + t)) ≤ uctCount sel t (Fin.last r) := by
  have hsum := uctCount_sum sel t
  rw [Fin.sum_univ_castSucc] at hsum
  have hsumR : (∑ i : Fin r, (uctCount sel t (Fin.castSucc i) : ℝ))
      + uctCount sel t (Fin.last r) = t := by
    exact_mod_cast hsum
  have hle : ∑ i : Fin r, (uctCount sel t (Fin.castSucc i) : ℝ)
      ≤ ∑ _i : Fin r, (1 + 4 * Real.log (1 + t)) := Finset.sum_le_sum (fun i _ => h.lose t ht i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  linarith

theorem CoreFacts.win_count (h : CoreFacts r rule sel zt) (t : ℕ) :
    uctCount zt t (coreWinZ r) = uctCount sel t (Fin.last r) := by
  unfold uctCount
  congr 1
  refine Finset.filter_congr (fun s _ => ?_)
  constructor
  · intro hz
    have hre := reward_of_reach h.reach s
    rw [hz] at hre
    by_contra hne
    have hlt : ((sel s : Fin (r + 1)) : ℕ) < r := by
      have h1 : ((sel s : Fin (r + 1)) : ℕ) ≤ r := Fin.is_le _
      have h2 : ((sel s : Fin (r + 1)) : ℕ) ≠ r := fun e => hne (Fin.ext (by rw [e, Fin.val_last]))
      omega
    have h1 : coreReward r (coreWinZ r) = 1 := rfl
    rw [h1] at hre
    simp [coreMu, hlt] at hre
  · intro hs
    have hact : coreAct r (Fin.last r) = .term (coreWinZ r) := by
      unfold coreAct
      rw [dite_eq_right (by simp)]
    rw [h.reach, hs, hact]
    rfl

/-- `UCTWork.core_stops_by` from the facts. -/
theorem CoreFacts.stops_by (h : CoreFacts r rule sel zt) {β : ℕ → ℝ} (hβ0 : ∀ n, 0 ≤ β n)
    {k0 : ℕ} (hβ : ∀ n, k0 ≤ n → β n ≤ 1 / 5) (s : Bool) {T : ℕ} (hT : r + 1 ≤ T)
    (hTk : (k0 : ℝ) + r * (1 + 4 * Real.log (1 + T)) ≤ T) :
    coreStops (coreRun s (coreHub r) (coreBox r β zt) (T - (r + 1)))
      (coreBox r β zt (T - (r + 1))) (Fin.last r) := by
  have hinv := coreRun_inv s (coreBox_table hβ0 zt) (coreHub_zero r) (T - (r + 1))
  apply hinv.stop_of_lower
  have e : r + 1 + (T - (r + 1)) = T := by omega
  have hcnt := h.win_count_ge hT
  have hk : k0 ≤ uctCount sel T (Fin.last r) := by
    have : (k0 : ℝ) ≤ uctCount sel T (Fin.last r) := by linarith
    exact_mod_cast this
  have hpos : 1 ≤ uctCount sel T (Fin.last r) := h.one_le _ hT
  unfold coreBox coreTab
  rw [e, h.win_count, ite_eq_right (by omega)]
  show 4 / 5 ≤ max 0 (coreReward r (coreWinZ r) - β _)
  have h1 : coreReward r (coreWinZ r) = 1 := rfl
  rw [h1]
  exact le_max_of_le_right (by linarith [hβ _ hk])

/-- `UCTWork.ta_core` from the facts (same constants). -/
theorem ta_core_facts {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r),
      CoreFacts r rule sel zt → ∀ s : Bool,
      ∃ τ : ℕ,
        coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
          (coreBox r (coreRadius r δ) zt τ) (Fin.last r) ∧
        (∀ k, k < τ → ∀ a, ¬ coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
          (coreBox r (coreRadius r δ) zt k) a) ∧
        (∀ k a, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
          (coreBox r (coreRadius r δ) zt k) a → a = Fin.last r) ∧
        ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
        (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ) ≤ B * (r : ℝ) ^ 2 * Real.log r ∧
        r ^ 3 ≤ ∑ i : Fin r, (coreLoseSupp r i).card := by
  classical
  obtain ⟨A, hA, hhor⟩ := core_horizon_exists hδ0 hδ1
  refine ⟨A, 27 * A + 42, hA, by linarith, ?_⟩
  intro r _ hr rule sel zt h s
  obtain ⟨T, hT1, hT2, hT3⟩ := hhor r hr
  have hβ0 := coreRadius_nonneg r δ
  have htab := coreBox_table hβ0 zt
  have hstopT := h.stops_by hβ0 (fun n hn => coreRadius_le hδ0 hδ1 (by omega) hn) s hT1 hT3
  have hlead : ∀ k a, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
      (coreBox r (coreRadius r δ) zt k) a → a = Fin.last r :=
    fun k a hs => (coreRun_inv s htab (coreHub_zero r) k).stop_leader (htab.win k) hs
  have hex : ∃ k, ∃ a, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
      (coreBox r (coreRadius r δ) zt k) a := ⟨_, _, hstopT⟩
  obtain ⟨a, ha⟩ := Nat.find_spec hex
  have hτT : Nat.find hex ≤ T - (r + 1) := Nat.find_min' hex ⟨_, hstopT⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = Nat.find hex := ⟨_, rfl⟩
  rw [← hτ] at ha hτT
  have hτR : ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r := by
    have : r + 1 + τ ≤ T := by omega
    exact le_trans (by exact_mod_cast this) hT2
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hℓ69 : (0.69 : ℝ) ≤ Real.log r := by
    have h1 : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hrR
    have h2 := Real.log_two_gt_d9
    linarith
  refine ⟨τ, ?_, ?_, hlead, hτR, ?_, (core_flat_support_size r).2⟩
  · rw [hlead τ a ha] at ha
    exact ha
  · intro k hk a' hs
    rw [hτ] at hk
    exact Nat.find_min hex hk ⟨a', hs⟩
  · have hW := coreTotalWork_le s hβ0 rule sel zt τ
    have hWR : (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ)
        ≤ 13 * (r : ℝ) ^ 2 + 24 * r + 11 + τ * (19 * r + 16) := by
      exact_mod_cast hW
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log r := ⟨_, rfl⟩
    rw [← hℓ] at hτR hℓ69 ⊢
    have hτle : (τ : ℝ) ≤ A * r * ℓ := by
      have : (τ : ℝ) ≤ ((r + 1 + τ : ℕ) : ℝ) := by
        push_cast
        linarith
      linarith
    have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
    have h1 : (τ : ℝ) * (19 * r + 16) ≤ A * r * ℓ * (27 * r) := by
      have ha : (19 : ℝ) * r + 16 ≤ 27 * r := by linarith
      calc (τ : ℝ) * (19 * r + 16) ≤ τ * (27 * r) := mul_le_mul_of_nonneg_left ha hτ0
        _ ≤ A * r * ℓ * (27 * r) := mul_le_mul_of_nonneg_right hτle (by linarith)
    have hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have h2 : 13 * (r : ℝ) ^ 2 + 24 * r + 11 ≤ 42 * ((r : ℝ) ^ 2 * ℓ) := by
      have hb : (24 : ℝ) * r + 11 ≤ 15 * (r : ℝ) ^ 2 := by nlinarith
      have hc : 28 * (r : ℝ) ^ 2 ≤ 42 * ((r : ℝ) ^ 2 * ℓ) := by nlinarith
      linarith
    have e : (27 * A + 42) * (r : ℝ) ^ 2 * ℓ = A * r * ℓ * (27 * r) + 42 * ((r : ℝ) ^ 2 * ℓ) := by
      ring
    linarith

/-- `CoreCovers.ta_core_coupled` from the facts (same constants). -/
theorem ta_core_coupled_facts {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r),
      CoreFacts r rule sel zt →
        (∀ k a, coreStops (coreRun true (coreHub r) (coreBox r (coreRadius r δ) zt) k)
            (coreBox r (coreRadius r δ) zt k) a ↔
          coreStops (coreRun false (coreHub r) (coreBox r (coreRadius r δ) zt) k)
            (coreBox r (coreRadius r δ) zt k) a) ∧
        (∀ (s : Bool) k a, a ∈ (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k).act →
          (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k).lo
              (coreBox r (coreRadius r δ) zt k) a = coreL r (coreBox r (coreRadius r δ) zt) k a ∧
            (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k).hi
              (coreBox r (coreRadius r δ) zt k) a
                = coreU r (coreBox r (coreRadius r δ) zt) k a) ∧
        ∃ τ : ℕ,
          (∀ s : Bool, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
            (coreBox r (coreRadius r δ) zt τ) (Fin.last r)) ∧
          (∀ (s : Bool) k, k < τ → ∀ a,
            ¬ coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
          (∀ (s : Bool) k a, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
            (coreBox r (coreRadius r δ) zt k) a → a = Fin.last r) ∧
          ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
          (∀ s : Bool, (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ B * (r : ℝ) ^ 2 * Real.log r) ∧
          r ^ 3 ≤ ∑ i : Fin r, (coreLoseSupp r i).card := by
  obtain ⟨A, B, hA, hB, H⟩ := ta_core_facts hδ0 hδ1
  refine ⟨A, B, hA, hB, ?_⟩
  intro r _ hr rule sel zt h
  obtain ⟨hmono, hne⟩ := coreBox_nested (coreRadius_nonneg r δ)
    (fun j k hj hjk => coreRadius_anti hδ0 hδ1.le (by omega) hj hjk) zt
  have hiff := core_stops_iff (coreBox r (coreRadius r δ) zt) hmono hne
  obtain ⟨τ, f1, f2, f3, f4, f5, f6⟩ := H r hr rule sel zt h false
  obtain ⟨τ', t1, t2, t3, -, t5, -⟩ := H r hr rule sel zt h true
  have hττ : τ' = τ := by
    rcases Nat.lt_trichotomy τ' τ with hlt | heq | hgt
    · exact absurd ((hiff τ' _).mp t1) (f2 τ' hlt _)
    · exact heq
    · exact absurd ((hiff τ _).mpr f1) (t2 τ hgt _)
  subst hττ
  refine ⟨hiff, fun s k a ha => coreRun_lo_hi s _ k ha, τ', ?_, ?_, ?_, f4, ?_, f6⟩
  · intro s
    cases s
    · exact f1
    · exact t1
  · intro s
    cases s
    · exact f2
    · exact t2
  · intro s
    cases s
    · exact f3
    · exact t3
  · intro s
    cases s
    · exact f5
    · exact t5

/-- **Theorem `thm:ta-core` under both readings of the root index.**  Every clause of
`LiteralE1.ta_core_literal`, with the same constants, for every search on the common-core
DAG whose root uses either `Q + 2 √(log (1 + t) / N)` (`CoreSearch`) or the literal index
`Q + 2 √(log t / N)` of `eq:uct-index` with `t = N_t(root)` the number of previous root
visits (`LitCoreSearch`); any path rule below the root, any tie-breaking. -/
theorem ta_core_both_readings {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r),
      (CoreSearch r rule sel zt ∨ LitCoreSearch r rule sel zt) →
        (∀ k a,
          cvLo (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a
              = coreL r (coreBox r (coreRadius r δ) zt) k a ∧
            cvHi (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a
              = coreU r (coreBox r (coreRadius r δ) zt) k a) ∧
        (∀ (s : Bool) k a,
          cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a ↔
            coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
        ∃ τ : ℕ,
          cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) τ)
            (Fin.last r) ∧
          (∀ s : Bool, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
            (coreBox r (coreRadius r δ) zt τ) (Fin.last r)) ∧
          (∀ k, k < τ → ∀ a, ¬ cvStops
            (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a) ∧
          (∀ (s : Bool) k, k < τ → ∀ a,
            ¬ coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
          (∀ k a, cvStops
            (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a →
              a = Fin.last r) ∧
          ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
          (∀ s : Bool, (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ B * (r : ℝ) ^ 2 * Real.log r) ∧
          (cvTotalWork r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ C * (r : ℝ) ^ 2 * Real.log r ^ 2 ∧
          r ^ 3 ≤ (flatAll (coreAct r) (List.finRange (r + 1))).2 ∧
          ∀ out : Fin (r + 1) → List (CoreZ r), (∀ a, coreSupp r a ⊆ (out a).toFinset) →
            r ^ 3 ≤ ∑ a : Fin (r + 1), (out a).length := by
  obtain ⟨A, B, hA, hB, H⟩ := ta_core_coupled_facts hδ0 hδ1
  refine ⟨A, B, 500 * A + 20000, hA, hB, by linarith, ?_⟩
  intro r _ hr rule sel zt hboth
  have h : CoreFacts r rule sel zt := by
    rcases hboth with h | h
    · exact CoreSearch.facts h
    · exact h.facts
  obtain ⟨hiff, -, τ, f1, f2, f3, f4, f5, -⟩ := H r hr rule sel zt h
  have hone := coreBox_one (r := r) (coreRadius r δ) zt
  have hcv := cv_stops_iff (r := r) hone
  have hcvs : ∀ (s : Bool) k a,
      cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a ↔
        coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
          (coreBox r (coreRadius r δ) zt k) a := by
    intro s k a
    cases s
    · exact hcv k a
    · exact (hcv k a).trans (hiff k a).symm
  refine ⟨fun k a => cv_exact (cvRun_inv hone k) a, hcvs, τ, (hcvs false τ _).mpr (f1 false), f1,
    fun k hk a hs => f2 false k hk a ((hcvs false k a).mp hs), f2,
    fun k a hs => f3 false k a ((hcvs false k a).mp hs), f4, f5, ?_, (coreFlat_cost_ge r).2,
    flat_cells_ge r⟩
  have hmon := cvMonWork_le (r := r) hone τ
  have hsize := coreHub_size r
  have hroll : ∑ u ∈ range (r + 1 + τ), coreRollout r rule u (sel u)
      ≤ (r + 1 + τ) * (5 * r + 5) := by
    have hh := coreHub_height_le r
    have : ∑ u ∈ range (r + 1 + τ), coreRollout r rule u (sel u)
        ≤ ∑ _u ∈ range (r + 1 + τ), (5 * r + 5) := by
      refine Finset.sum_le_sum (fun u _ => ?_)
      have h1 := (MaxCirc.uctWalk_snd_le (rule u) (coreAct r (sel u)) 0).trans
        (coreAct_height r (sel u))
      have h2 := coreClog_le r
      unfold coreRollout
      omega
    rwa [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  have hW : cvTotalWork r (coreRadius r δ) rule sel zt τ
      ≤ 2 * (2 * r ^ 2 + 3 * r) + (r + 1 + τ) * (5 * r + 5)
        + (30 * (1 + coreN r) * (r + 1)
          + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (16 * (coreN r + 1) ^ 2)
            + (r + 1) * (coreN r + 2))
          + τ * (4 * (r + 1) + 18 * ((r + 1) * (coreN r + 1)))
          + 4 * (r + 1)
          + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (4 * coreN r + 3) + (r + 1))) := by
    unfold cvTotalWork
    omega
  have hWR : (cvTotalWork r (coreRadius r δ) rule sel zt τ : ℝ)
      ≤ 2 * (2 * (r : ℝ) ^ 2 + 3 * r) + ((r + 1 + τ : ℕ) : ℝ) * (5 * r + 5)
        + (30 * (1 + (coreN r : ℝ)) * (r + 1)
          + 2 * (4 * ((r : ℝ) ^ 2 + r + 1) + (r + 1) * (16 * ((coreN r : ℝ) + 1) ^ 2)
            + (r + 1) * ((coreN r : ℝ) + 2))
          + (τ : ℝ) * (4 * (r + 1) + 18 * ((r + 1) * ((coreN r : ℝ) + 1)))
          + 4 * (r + 1)
          + 2 * (4 * ((r : ℝ) ^ 2 + r + 1) + (r + 1) * (4 * (coreN r : ℝ) + 3) + (r + 1))) := by
    exact_mod_cast hW
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hℓ69 : (0.69 : ℝ) ≤ Real.log r := by
    have h1 : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hrR
    have h2 := Real.log_two_gt_d9
    linarith
  have hτT : (τ : ℝ) ≤ ((r + 1 + τ : ℕ) : ℝ) := by push_cast; linarith
  exact hWR.trans (core_work_arith hA hrR hℓ69 (Nat.cast_nonneg _) (coreN_le_log hr)
    (Nat.cast_nonneg τ) hτT f4)

end TaCore

/-! ## 2. `cor:v2countscales`, `eq:v2shrinking` for `K ≤ t < 2K` -/

section Shrinking

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ lam : ι → ℝ} {n : ℕ → ι → ℕ}
  {sel : ℕ → ι}

/-- **`eq:v2shrinking` below `2K`, lower bound.**  For `K ≤ t < 2K` with `g √t ≥ 4Λ`, the
lower bound `λ_i √t / (2 √3 g) - 1 < n_i(t)` holds whenever `K λ_i ≤ 8 √3 Λ`. -/
theorem count_shrinking_gap_small (h : RootPUCTTrace μ lam n sel) (hlam : ∀ i, 0 < lam i)
    {i : ι} {g : ℝ} (hg : 0 < g) {t : ℕ} (htK : Fintype.card ι ≤ t)
    (ht2 : t < 2 * Fintype.card ι) (hgt : 4 * ∑ j, lam j ≤ g * Real.sqrt t)
    (hK : (Fintype.card ι : ℝ) * lam i ≤ 8 * Real.sqrt 3 * ∑ j, lam j) :
    lam i * Real.sqrt t / (2 * Real.sqrt 3 * g) - 1 < (n t i : ℝ) := by
  have hK0 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hn1 : (1 : ℝ) ≤ n t i := by exact_mod_cast h.one_le i htK
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hΛ : 0 < ∑ j, lam j := Finset.sum_pos (fun j _ => hlam j) ⟨i, mem_univ i⟩
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hts : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt htpos.le
  have ht2R : (t : ℝ) < 2 * Fintype.card ι := by exact_mod_cast ht2
  -- `λ_i √t / g ≤ λ_i t / (4Λ) < λ_i K / (2Λ) ≤ 4 √3`
  have hkey : lam i * Real.sqrt t < 4 * Real.sqrt 3 * g := by
    have h1 : lam i * Real.sqrt t * (4 * ∑ j, lam j) ≤ lam i * Real.sqrt t * (g * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hgt (mul_nonneg (hlam i).le hs.le)
    have h2 : lam i * Real.sqrt t * (g * Real.sqrt t) = g * (lam i * t) := by
      calc lam i * Real.sqrt t * (g * Real.sqrt t) = g * (lam i * (Real.sqrt t * Real.sqrt t)) := by
            ring
        _ = g * (lam i * t) := by rw [hts]
    have h4 : lam i * t < lam i * (2 * Fintype.card ι) := mul_lt_mul_of_pos_left ht2R (hlam i)
    have h5 : g * (lam i * t) < g * (2 * (Fintype.card ι * lam i)) := by nlinarith
    have h6 : g * (2 * (Fintype.card ι * lam i)) ≤ g * (2 * (8 * Real.sqrt 3 * ∑ j, lam j)) :=
      mul_le_mul_of_nonneg_left (by linarith) hg.le
    have h7 : lam i * Real.sqrt t * (4 * ∑ j, lam j)
        < (4 * Real.sqrt 3 * g) * (4 * ∑ j, lam j) := by nlinarith
    exact lt_of_mul_lt_mul_right h7 (by positivity)
  have hdiv : lam i * Real.sqrt t / (2 * Real.sqrt 3 * g) < 2 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  linarith

/-- **`eq:v2shrinking` for all `t ≥ K`** under `t ≥ 2K` or `K λ_i ≤ 8 √3 Λ`. -/
theorem count_shrinking_gap_ext (h : RootPUCTTrace μ lam n sel) (hlam : ∀ i, 0 < lam i)
    {star : ι} (hstar : ∀ j, μ j ≤ μ star) {i : ι} {g : ℝ} (hg : 0 < g)
    (hgi : μ star - μ i = g) {t : ℕ} (htK : Fintype.card ι ≤ t)
    (hcase : 2 * Fintype.card ι ≤ t ∨ (Fintype.card ι : ℝ) * lam i ≤ 8 * Real.sqrt 3 * ∑ j, lam j)
    (hgt : 4 * ∑ j, lam j ≤ g * Real.sqrt t) :
    lam i * Real.sqrt t / (2 * Real.sqrt 3 * g) - 1 < (n t i : ℝ) ∧
      (n t i : ℝ) ≤ max 1 (lam i * Real.sqrt t / g) := by
  by_cases h2 : 2 * Fintype.card ι ≤ t
  · exact h.count_shrinking_gap hlam hstar hg hgi h2 hgt
  · have hK := hcase.resolve_left h2
    refine ⟨count_shrinking_gap_small h hlam hg htK (by omega) hgt hK, ?_⟩
    have hgap : μ i < μ star := by linarith
    have := h.count_le hlam hgap (t := t) htK
    rwa [hgi] at this

/-- Means of the counterexample. -/
def cxMu (j : Fin 36) : ℝ := if j = 0 then 0 else 11 / 15

/-- Prior weights of the counterexample. -/
def cxLam (j : Fin 36) : ℝ := if j = 0 then 1 else 1 / 350

lemma cxLam_sum : ∑ j, cxLam j = 11 / 10 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin 36))]
  have : ∀ j ∈ (univ : Finset (Fin 36)).erase 0, cxLam j = 1 / 350 := by
    intro j hj
    unfold cxLam
    rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  simp [cxLam]
  norm_num

/-- **`eq:v2shrinking` is false as written below `2K`.**  For `K = 36` arms with
`λ_0 = 1`, `λ_j = 1/350` (`j ≠ 0`), `μ_0 = 0`, `μ_j = 11/15` (`j ≠ 0`), all rewards in
`[0, 1]`: arm `0` has gap `g = 11/15`, at `t = K = 36` one has `g √t = 4Λ`, and for EVERY
trace of the fixed-prior root-PUCT rule the lower bound of `eq:v2shrinking` fails at
`t = 36`.  Traces exist (`exists_rootPUCTTrace`). -/
theorem v2shrinking_counterexample :
    (∀ j, 0 ≤ cxMu j ∧ cxMu j ≤ 1) ∧ (∀ j, 0 < cxLam j) ∧ (∀ j, cxMu j ≤ cxMu 1) ∧
    cxMu 1 - cxMu 0 = 11 / 15 ∧ Fintype.card (Fin 36) = 36 ∧
    4 * ∑ j, cxLam j ≤ 11 / 15 * Real.sqrt (36 : ℕ) ∧
    (∃ n sel, RootPUCTTrace cxMu cxLam n sel) ∧
    ∀ n sel, RootPUCTTrace cxMu cxLam n sel →
      ¬ (cxLam 0 * Real.sqrt (36 : ℕ) / (2 * Real.sqrt 3 * (11 / 15)) - 1 < (n 36 0 : ℝ)) := by
  have hs36 : Real.sqrt ((36 : ℕ) : ℝ) = 6 := by
    rw [show ((36 : ℕ) : ℝ) = 6 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, Fintype.card_fin 36, ?_, exists_rootPUCTTrace _ _, ?_⟩
  · intro j
    unfold cxMu
    split_ifs <;> norm_num
  · intro j
    unfold cxLam
    split_ifs <;> norm_num
  · intro j
    have h1 : cxMu 1 = 11 / 15 := by simp [cxMu]
    rw [h1]
    unfold cxMu
    split_ifs <;> norm_num
  · have h1 : cxMu 1 = 11 / 15 := by simp [cxMu]
    have h0 : cxMu 0 = 0 := by simp [cxMu]
    rw [h1, h0]
    norm_num
  · rw [cxLam_sum, hs36]
    norm_num
  · intro n sel h hlt
    have hn : n 36 0 = 1 := by
      have := h.init 0
      rwa [Fintype.card_fin] at this
    rw [hn, hs36] at hlt
    have hl0 : cxLam 0 = 1 := by simp [cxLam]
    rw [hl0] at hlt
    have h3 : Real.sqrt 3 < 1.7321 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have : (2 : ℝ) ≤ 1 * 6 / (2 * Real.sqrt 3 * (11 / 15)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    push_cast at hlt
    linarith

end Shrinking

end

end LiteralE7
end JointRootCert
