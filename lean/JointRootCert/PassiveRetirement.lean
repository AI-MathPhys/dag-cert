/-
Trajectory coupling, safe retirement and the explicit graph families of the appendix
"Certification Along Passive Graph-Search Trajectories" (`app:ta-proofs`).

* Proposition `prop:uct-coupling` / `prop:ta-coupled` / `thm:protected-pruning` /
  `thm:decision-retirement` / `thm:tombstones` (Safe permanent retirement):
  `protected_pruning` (part (i)), `RetireRun.invariant`, `RetireRun.lowLeader_iff`,
  `RetireRun.stops_iff` (part (ii)), and `coupled_trajectories` (the induction behind the
  exact coupling of `prop:ta-coupled`).
* Theorem `thm:selective-separation` (Selective vs. eager maintenance separations):
  only the deterministic count inequality of Steps 2--3 (`uct_count_le`) and the
  radius consequence of a successful check (`funnel_check_forces_radius`).  The
  Root-PUCT half of the statement is in `RootPUCT.lean`.
* Theorem `thm:ta-core` (Wide common-core support compilation cost): the explicit
  terminal family, its supports and regrets, and the `Ω(r³)` flat-support size
  (`card_coreZ`, `card_coreLoseSupp`, `core_flat_support_size`, `core_regret_win`,
  `core_regret_lose`, `core_lose_count_le`).
* Proposition `prop:v2escape` (The family does not lower-bound all numerical oracles):
  `MaxCirc.eval_of_onlyTerm`, `MaxCirc.interval_of_onlyTerm`.

RAM operation counts (`eq:ram-work-bounds`, the `O(·)`/`Ω(·)` work claims) are not
formalized here.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset

/-! ### Safe permanent retirement, part (i): protected MAX evaluation -/

/-- **`thm:protected-pruning` (i).**  Let `F e x` be the value of the child `e` of a MAX
vertex in the environment `x`, and let `[l e, u e]` enclose `F e` on the confidence set
`B`.  If a live child `k ≠ j` has `u j < l k`, then deleting the incidence `j` leaves a
nonempty live set and does not change the MAX value on `B`, nor on any nested subset
`B' ⊆ B` (all later confidence sets).  Hence the interval endpoints of the vertex, and of
all its ancestors, are unchanged. -/
theorem protected_pruning {X E : Type*} [DecidableEq E] (B : Set X) (F : E → X → ℝ)
    (l u : E → ℝ) (hl : ∀ x ∈ B, ∀ e, l e ≤ F e x) (hu : ∀ x ∈ B, ∀ e, F e x ≤ u e)
    (live : Finset E) {j k : E} (hk : k ∈ live.erase j) (hdom : u j < l k) :
    ∃ hne : (live.erase j).Nonempty, ∀ B' ⊆ B, ∀ x ∈ B',
      live.sup' ⟨k, mem_of_mem_erase hk⟩ (fun e => F e x)
        = (live.erase j).sup' hne (fun e => F e x) := by
  refine ⟨⟨k, hk⟩, fun B' hB' x hx => ?_⟩
  have hxB := hB' hx
  apply le_antisymm
  · refine sup'_le _ _ (fun e he => ?_)
    by_cases hej : e = j
    · have h1 : F e x ≤ F k x := by
        rw [hej]
        have := hu x hxB j
        have := hl x hxB k
        linarith
      exact h1.trans (le_sup' (fun e => F e x) hk)
    · exact le_sup' (fun e => F e x) (mem_erase.mpr ⟨hej, he⟩)
  · exact sup'_mono (fun e => F e x) (erase_subset j live) ⟨k, hk⟩

/-! ### Safe permanent retirement, part (ii): leader-and-stop monitors -/

section Retirement

variable {A : Type*} [Fintype A]

/-- A run of a marginal monitor with retirement: nested nonempty action intervals
`[L t a, U t a]`, all actions active initially, and an action `b` leaves the active set
at time `t` only if some other currently active action `a` has `U t b < L t a`. -/
structure RetireRun (L U : ℕ → A → ℝ) (act : ℕ → Finset A) : Prop where
  nestedL : ∀ a s t, s ≤ t → L s a ≤ L t a
  nestedU : ∀ a s t, s ≤ t → U t a ≤ U s a
  nonempty : ∀ t a, L t a ≤ U t a
  init : act 0 = univ
  anti : ∀ t, act (t + 1) ⊆ act t
  retire : ∀ t b, b ∉ act (t + 1) → b ∈ act t → ∃ a ∈ act t, a ≠ b ∧ U t b < L t a

variable {L U : ℕ → A → ℝ} {act : ℕ → Finset A}

/-- **`thm:decision-retirement`, the chaining argument.**  At every time the active set
is nonempty, and every retired action has its upper bound strictly below the lower bound
of some still-active action. -/
theorem RetireRun.invariant [Nonempty A] (h : RetireRun L U act) :
    ∀ t, (act t).Nonempty ∧ ∀ b, b ∉ act t → ∃ a ∈ act t, U t b < L t a := by
  intro t
  induction t with
  | zero =>
    rw [h.init]
    exact ⟨univ_nonempty, fun b hb => absurd (mem_univ b) hb⟩
  | succ t ih =>
    obtain ⟨hne, hinv⟩ := ih
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (act t) (L t) hne
    have hm' : m ∈ act (t + 1) := by
      by_contra hmn
      obtain ⟨a, ha, -, hlt⟩ := h.retire t m hmn hm
      have := hmax a ha
      have := h.nonempty t m
      linarith
    refine ⟨⟨m, hm'⟩, fun b hb => ?_⟩
    have hex : ∃ a ∈ act t, U t b < L t a := by
      by_cases hbt : b ∈ act t
      · obtain ⟨a, ha, -, hlt⟩ := h.retire t b hb hbt
        exact ⟨a, ha, hlt⟩
      · exact hinv b hbt
    obtain ⟨a, ha, hlt⟩ := hex
    refine ⟨m, hm', ?_⟩
    have h1 := h.nestedU b t (t + 1) (Nat.le_succ t)
    have h2 := hmax a ha
    have h3 := h.nestedL m t (t + 1) (Nat.le_succ t)
    linarith

variable [LinearOrder A]

/-- Canonical lower-bound leader among the actions in `s`: a maximizer of `L` of lowest
index. -/
def LowLeader (s : Finset A) (L : A → ℝ) (a : A) : Prop :=
  a ∈ s ∧ (∀ b ∈ s, L b ≤ L a) ∧ ∀ b ∈ s, L b = L a → a ≤ b

/-- The marginal stopping bit over the actions in `s`, with leader `a`:
`max_{b ∈ s, b ≠ a} U b - L a ≤ ε` (`eq:cert-gap`). -/
def MarginalStops (s : Finset A) (L U : A → ℝ) (ε : ℝ) (a : A) : Prop :=
  LowLeader s L a ∧ ∀ b ∈ s, b ≠ a → U b - L a ≤ ε

/-- **`thm:decision-retirement`: the leader is preserved.**  The canonical lower-bound
leader over all actions is the canonical leader over the active actions. -/
theorem RetireRun.lowLeader_iff [Nonempty A] (h : RetireRun L U act) (t : ℕ) (a : A) :
    LowLeader univ (L t) a ↔ LowLeader (act t) (L t) a := by
  obtain ⟨-, hinv⟩ := h.invariant t
  constructor
  · rintro ⟨-, hmax, hlow⟩
    have ha : a ∈ act t := by
      by_contra hn
      obtain ⟨a', -, hlt⟩ := hinv a hn
      have := hmax a' (mem_univ _)
      have := h.nonempty t a
      linarith
    exact ⟨ha, fun b _ => hmax b (mem_univ b), fun b _ => hlow b (mem_univ b)⟩
  · rintro ⟨-, hmax, hlow⟩
    have hlt : ∀ b, b ∉ act t → L t b < L t a := by
      intro b hb
      obtain ⟨a', ha', hlt⟩ := hinv b hb
      have := hmax a' ha'
      have := h.nonempty t b
      linarith
    refine ⟨mem_univ a, fun b _ => ?_, fun b _ hb => ?_⟩
    · by_cases hbt : b ∈ act t
      · exact hmax b hbt
      · exact (hlt b hbt).le
    · by_cases hbt : b ∈ act t
      · exact hlow b hbt hb
      · exact absurd hb (hlt b hbt).ne

/-- **`thm:decision-retirement`: the stopping bit is preserved.**  For `ε ≥ 0`, the
marginal leader-and-stop outcome computed from all actions equals the one computed from
the active actions only.  (The numerical gap `max_{b ≠ a} U b - L a` itself may differ:
a retired action can attain the maximum over all rivals.) -/
theorem RetireRun.stops_iff [Nonempty A] (h : RetireRun L U act) {ε : ℝ} (hε : 0 ≤ ε)
    (t : ℕ) (a : A) :
    MarginalStops univ (L t) (U t) ε a ↔ MarginalStops (act t) (L t) (U t) ε a := by
  constructor
  · rintro ⟨hl, hs⟩
    exact ⟨(h.lowLeader_iff t a).mp hl, fun b _ hb => hs b (mem_univ b) hb⟩
  · rintro ⟨hl, hs⟩
    refine ⟨(h.lowLeader_iff t a).mpr hl, fun b _ hb => ?_⟩
    by_cases hbt : b ∈ act t
    · exact hs b hbt hb
    · obtain ⟨a', ha', hlt⟩ := (h.invariant t).2 b hbt
      have := hl.2.1 a' ha'
      linarith

end Retirement

/-! ### Exact coupling of a passive controller with two monitors -/

section Coupling

variable {H O : Type*}

/-- The history of a deterministic closed loop: `step h o` is the next history when the
controller, at history `h` (which contains its randomness and the reward tape consumed so
far), reads the monitor output `o`. -/
def runTraj (step : H → O → H) (mon : H → O) (h0 : H) : ℕ → H
  | 0 => h0
  | t + 1 => step (runTraj step mon h0 t) (mon (runTraj step mon h0 t))

/-- **Exact coupling (`prop:ta-coupled`, inductive step).**  If two monitors expose the
same interface output on every history reached with the first one, the controller's
histories (sampled paths, observations, queries) coincide at all times.  Combined with
`RetireRun.stops_iff`, a full monitor and a decision-selective monitor that expose only
the leader and the stopping bit induce the same trajectory. -/
theorem coupled_trajectories (step : H → O → H) (mon₁ mon₂ : H → O) (h0 : H)
    (hagree : ∀ t, mon₁ (runTraj step mon₁ h0 t) = mon₂ (runTraj step mon₁ h0 t)) :
    ∀ t, runTraj step mon₁ h0 t = runTraj step mon₂ h0 t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [runTraj]
    rw [← ih, hagree t]

end Coupling

/-! ### Local UCT count bound (Steps 2--3 of the proof of `thm:selective-separation`) -/

/-- **UCT count bound.**  Let `n t` be the count of an edge whose empirical return never
exceeds `u0`, competing with an edge whose index is at least `b > u0`.  If the edge can be
selected at time `t` only when `u0 + c √(log (1+t) / n t) ≥ b`, then for all `t ≥ t0`
`n t ≤ max {n t0, 1 + c² log (1+t) / (b - u0)²}`. -/
theorem uct_count_le {c b u0 : ℝ} (hΔ : u0 < b) (n : ℕ → ℕ) (pick : ℕ → Prop) (t0 : ℕ)
    (hstep : ∀ t, t0 ≤ t → (pick t → n (t + 1) = n t + 1) ∧ (¬ pick t → n (t + 1) = n t))
    (hsel : ∀ t, t0 ≤ t → pick t → b ≤ u0 + c * Real.sqrt (Real.log (1 + t) / n t)) :
    ∀ t, t0 ≤ t →
      (n t : ℝ) ≤ max (n t0 : ℝ) (1 + c ^ 2 * Real.log (1 + t) / (b - u0) ^ 2) := by
  intro t ht
  have hΔ' : 0 < b - u0 := sub_pos.mpr hΔ
  induction t, ht using Nat.le_induction with
  | base => exact le_max_left _ _
  | succ t ht ih =>
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hlogmono : Real.log (1 + (t : ℝ)) ≤ Real.log (1 + ((t : ℝ) + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hmono : 1 + c ^ 2 * Real.log (1 + (t : ℝ)) / (b - u0) ^ 2
        ≤ 1 + c ^ 2 * Real.log (1 + ((t : ℝ) + 1)) / (b - u0) ^ 2 := by
      have := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogmono (sq_nonneg c)) (sq_nonneg (b - u0))
      linarith
    by_cases hp : pick t
    · rw [(hstep t ht).1 hp]
      have h1 := hsel t ht hp
      have hx : 0 ≤ Real.log (1 + (t : ℝ)) := Real.log_nonneg (by linarith)
      have hn : (0 : ℝ) < n t := by
        rcases Nat.eq_zero_or_pos (n t) with h0 | h0
        · rw [h0] at h1
          simp at h1
          linarith
        · exact_mod_cast h0
      have hy : 0 ≤ Real.log (1 + (t : ℝ)) / n t := div_nonneg hx hn.le
      have h2 : (b - u0) ^ 2 ≤ (c * Real.sqrt (Real.log (1 + (t : ℝ)) / n t)) ^ 2 :=
        pow_le_pow_left₀ hΔ'.le (by linarith) 2
      rw [mul_pow, Real.sq_sqrt hy] at h2
      have h3 : (n t : ℝ) ≤ c ^ 2 * Real.log (1 + (t : ℝ)) / (b - u0) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have e : c ^ 2 * (Real.log (1 + (t : ℝ)) / n t) * n t
            = c ^ 2 * Real.log (1 + (t : ℝ)) := by
          field_simp
        have := mul_le_mul_of_nonneg_right h2 hn.le
        linarith
      push_cast
      exact le_max_of_le_right (by linarith)
    · rw [(hstep t ht).2 hp]
      push_cast
      exact ih.trans (max_le_max le_rfl hmono)

/-- **Step 3 of the proof of `thm:selective-separation`, first display.**  If the rival's
upper bound is at least `b - g` and the check `U(a') - l(b) ≤ g/2` succeeds, the winning
lower bound satisfies `l(b) ≥ b - 3g/2`. -/
theorem funnel_check_forces_radius {b g Ua lb : ℝ} (hU : b - g ≤ Ua)
    (hstop : Ua - lb ≤ g / 2) : b - 3 * g / 2 ≤ lb := by
  linarith

/-! ### The wide common-core family (`thm:ta-core`) -/

section CommonCore

/-- Terminals of the wide common-core family: `r²` core leaves, one private leaf for
each of the `r` losing root actions, and the terminal of the winning direct action. -/
abbrev CoreZ (r : ℕ) := Fin (r ^ 2) ⊕ Fin r ⊕ Unit

/-- Rewards: `1` at the winning terminal, `0` elsewhere. -/
def coreReward (r : ℕ) : CoreZ r → ℝ
  | Sum.inr (Sum.inr _) => 1
  | _ => 0

/-- Support of the losing root action `i`: all core leaves and its private leaf. -/
def coreLoseSupp (r : ℕ) (i : Fin r) : Finset (CoreZ r) :=
  insert (Sum.inr (Sum.inl i)) (univ.map ⟨Sum.inl, Sum.inl_injective⟩)

/-- Support of the winning root action. -/
def coreWinSupp (r : ℕ) : Finset (CoreZ r) := {Sum.inr (Sum.inr ())}

lemma coreLoseSupp_nonempty (r : ℕ) (i : Fin r) : (coreLoseSupp r i).Nonempty :=
  ⟨_, mem_insert_self _ _⟩

lemma coreWinSupp_nonempty (r : ℕ) : (coreWinSupp r).Nonempty := singleton_nonempty _

/-- There are `L = r² + r + 1` terminals. -/
theorem card_coreZ (r : ℕ) : Fintype.card (CoreZ r) = r ^ 2 + r + 1 := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

/-- Each losing support has `r² + 1` terminals. -/
theorem card_coreLoseSupp (r : ℕ) (i : Fin r) : (coreLoseSupp r i).card = r ^ 2 + 1 := by
  unfold coreLoseSupp
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_map, Finset.card_univ,
    Fintype.card_fin]

/-- **`thm:ta-core`, flat-support size.**  Materializing the flat supports of the `r`
losing root actions writes `r (r² + 1) ≥ r³` entries. -/
theorem core_flat_support_size (r : ℕ) :
    ∑ i : Fin r, (coreLoseSupp r i).card = r * (r ^ 2 + 1) ∧
      r ^ 3 ≤ ∑ i : Fin r, (coreLoseSupp r i).card := by
  have h : ∑ i : Fin r, (coreLoseSupp r i).card = r * (r ^ 2 + 1) := by
    simp [card_coreLoseSupp]
  refine ⟨h, ?_⟩
  rw [h]
  nlinarith

lemma gmax_coreReward (r : ℕ) : gmax (coreReward r) = 1 := by
  apply le_antisymm
  · refine sup'_le _ _ (fun z _ => ?_)
    rcases z with c | p | u
    · show (0 : ℝ) ≤ 1
      norm_num
    · show (0 : ℝ) ≤ 1
      norm_num
    · show (1 : ℝ) ≤ 1
      exact le_rfl
  · exact le_gmax (coreReward r) (Sum.inr (Sum.inr ()))

/-- The winning action has regret `0`. -/
theorem core_regret_win (r : ℕ) :
    regret (coreWinSupp r) (coreWinSupp_nonempty r) (coreReward r) = 0 := by
  have hv : val (coreWinSupp r) (coreWinSupp_nonempty r) (coreReward r) = 1 := by
    apply le_antisymm
    · rw [← gmax_coreReward r]
      exact val_le_gmax _ _ _
    · exact le_val (coreWinSupp_nonempty r) (coreReward r)
        (y := Sum.inr (Sum.inr ())) (mem_singleton_self _)
  rw [regret, hv, gmax_coreReward]
  ring

/-- Every losing action has regret `1`. -/
theorem core_regret_lose (r : ℕ) (i : Fin r) :
    regret (coreLoseSupp r i) (coreLoseSupp_nonempty r i) (coreReward r) = 1 := by
  have hv : val (coreLoseSupp r i) (coreLoseSupp_nonempty r i) (coreReward r) = 0 := by
    apply le_antisymm
    · refine sup'_le _ _ (fun z hz => ?_)
      unfold coreLoseSupp at hz
      rw [mem_insert, mem_map] at hz
      rcases hz with rfl | ⟨c, -, rfl⟩
      · exact le_rfl
      · exact le_rfl
    · exact le_val (coreLoseSupp_nonempty r i) (coreReward r)
        (y := Sum.inr (Sum.inl i)) (mem_insert_self _ _)
  rw [regret, hv, gmax_coreReward]
  ring

/-- **`thm:ta-core`, unique `ε`-optimal action at `ε = 1/5`.**  The winning action is
`1/5`-optimal and no losing action is. -/
theorem core_unique_eps_optimal (r : ℕ) :
    regret (coreWinSupp r) (coreWinSupp_nonempty r) (coreReward r) ≤ 1 / 5 ∧
      ∀ i : Fin r,
        ¬ regret (coreLoseSupp r i) (coreLoseSupp_nonempty r i) (coreReward r) ≤ 1 / 5 := by
  refine ⟨by rw [core_regret_win]; norm_num, fun i => ?_⟩
  rw [core_regret_lose]
  norm_num

/-- **`thm:ta-core`, count of a losing action.**  A losing action returns `0`; once the
winning action (return `1`) has been tried it can be selected only if
`2 √(log (1+t) / N_a(t)) ≥ 1`, hence `N_a(t) ≤ max {N_a(t0), 1 + 4 log (1+t)}`. -/
theorem core_lose_count_le (n : ℕ → ℕ) (pick : ℕ → Prop) (t0 : ℕ)
    (hstep : ∀ t, t0 ≤ t → (pick t → n (t + 1) = n t + 1) ∧ (¬ pick t → n (t + 1) = n t))
    (hsel : ∀ t, t0 ≤ t → pick t → (1 : ℝ) ≤ 2 * Real.sqrt (Real.log (1 + t) / n t)) :
    ∀ t, t0 ≤ t → (n t : ℝ) ≤ max (n t0 : ℝ) (1 + 4 * Real.log (1 + t)) := by
  intro t ht
  have := uct_count_le (c := 2) (b := 1) (u0 := 0) (by norm_num) n pick t0 hstep
    (fun t ht hp => by rw [zero_add]; exact hsel t ht hp) t ht
  refine this.trans (max_le_max le_rfl (le_of_eq ?_))
  norm_num

end CommonCore

/-! ### `prop:v2escape`: an all-MAX circuit over a single terminal -/

/-- All-MAX circuits with unary and binary internal vertices (the tree unfolding of the
subgraph below `C` in `sec:v2separation`; unfolding a DAG does not change its value
function). -/
inductive MaxCirc (Z : Type*) where
  | term : Z → MaxCirc Z
  | unary : MaxCirc Z → MaxCirc Z
  | bin : MaxCirc Z → MaxCirc Z → MaxCirc Z

namespace MaxCirc

variable {Z : Type*}

/-- The MAX value function of the circuit in the environment `x`. -/
def eval (x : Z → ℝ) : MaxCirc Z → ℝ
  | term z => x z
  | unary c => eval x c
  | bin c d => max (eval x c) (eval x d)

/-- Every terminal reachable in the circuit is `z`. -/
def OnlyTerm (z : Z) : MaxCirc Z → Prop
  | term w => w = z
  | unary c => OnlyTerm z c
  | bin c d => OnlyTerm z c ∧ OnlyTerm z d

/-- **`prop:v2escape`, core identity.**  An all-MAX circuit whose only terminal is `z`
computes `F_C(x) = x_z` identically. -/
theorem eval_of_onlyTerm {z : Z} (x : Z → ℝ) :
    ∀ c : MaxCirc Z, OnlyTerm z c → eval x c = x z
  | term w, h => by
    have h' : w = z := h
    simp [eval, h']
  | unary c, h => eval_of_onlyTerm x c h
  | bin c d, h => by
    have h' : OnlyTerm z c ∧ OnlyTerm z d := h
    simp [eval, eval_of_onlyTerm x c h'.1, eval_of_onlyTerm x d h'.2]

/-- **`prop:v2escape`.**  Consequently the exact root-action interval of `C` on any box
`[l, u]` is the terminal interval `[l z, u z]`: an alias to the terminal interval of `z`
preserves the complete root-action interval vector with `O(1)` work per update and per
query after the `O(m)` identification of `z` (the operation counts themselves are not
formalized). -/
theorem interval_of_onlyTerm {z : Z} {c : MaxCirc Z} (h : OnlyTerm z c) {l u : Z → ℝ}
    (hlu : l ≤ u) :
    IsLeast ((fun x => eval x c) '' Set.Icc l u) (l z) ∧
      IsGreatest ((fun x => eval x c) '' Set.Icc l u) (u z) := by
  refine ⟨⟨⟨l, ⟨le_rfl, hlu⟩, eval_of_onlyTerm l c h⟩, ?_⟩,
    ⟨⟨u, ⟨hlu, le_rfl⟩, eval_of_onlyTerm u c h⟩, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    show l z ≤ eval x c
    rw [eval_of_onlyTerm x c h]
    exact hx.1 z
  · rintro _ ⟨x, hx, rfl⟩
    show eval x c ≤ u z
    rw [eval_of_onlyTerm x c h]
    exact hx.2 z

end MaxCirc

end JointRootCert
