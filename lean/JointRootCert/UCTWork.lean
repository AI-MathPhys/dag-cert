/-
Local UCT allocation and the common-core family of the appendix
"Certification Along Passive Graph-Search Trajectories".

* Theorem `thm:ta-core` (Wide Common-Core Support Compilation Cost): the common-core DAG
  (`coreHub`, `coreAct`), the UCT search process on it (`CoreSearch`), its identification
  with a deterministic-return root bandit (`CoreSearch.reward_eq`, `CoreSearch.Q_eq`), the
  stopping-time bound `τ = O(r log r)` (`core_win_count_ge`, `core_stops_by`,
  `core_horizon_exists`), an eager and a selective monitor on the shared-hub DAG with
  computed work (`coreRun`, `coreWork`, `coreWork_le`), and the assembled statement
  `ta_core`.
* Theorem `thm:onpolicy-uct` (Selective vs. eager maintenance separations on UCT and
  Root-PUCT funnels), local-UCT half: the explicit logarithmic fairness of Step 1
  (`UCTRun.fairness`, `UCTRun.window_lower`), the count bounds of Steps 2-3 (`UCTRun.count_le`,
  `funnel_counts`) and the lower bound on the certification horizon
  (`funnel_horizon_lower`).

The UCT index is the one used in the proofs of these theorems, `Q + c √(log (1 + t) / N)`
with `t` the number of earlier visits of the node; the manuscript's displayed definition
`eq:uct-index` has `log N_t(v)` in place of `log (1 + t)`.

Cost model (self-contained copy of the tree part of `MonitorWork.lean`).  A monitor graph
stores an interval at every internal vertex; a propagation wave delivers every changed
child interval to its parent and charges `⌈log₂ d⌉ + 1` per delivery for out-degree
`d ∈ {1, 2}`; root queries and retirement checks are charged per active action; building,
releasing and disposing are charged per vertex.  All works are natural numbers returned by
the functions that perform the operations.
-/
import JointRootCert.PassiveRetirement

namespace JointRootCert

open Finset

noncomputable section

/-! ### Local UCT allocation at one node -/

section UCT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of selections of arm `i` among the first `t` visits of the node. -/
def uctCount (sel : ℕ → ι) (t : ℕ) (i : ι) : ℕ := ((range t).filter (fun s => sel s = i)).card

/-- The UCT index `Q + c √(log (1 + t) / N)`. -/
def uctIndex (c q : ℝ) (t n : ℕ) : ℝ := q + c * Real.sqrt (Real.log (1 + t) / n)

/-- A run of local UCT at a node with arms `ι`: `Q t i` is the empirical mean of arm `i`
before the `t`-th visit (arbitrary, it may change over time), the first `|ι|` visits try
every arm once, and afterwards a maximizer of the index is selected.  Any maximizer is
admissible. -/
structure UCTRun (c : ℝ) (Q : ℕ → ι → ℝ) (sel : ℕ → ι) : Prop where
  forced : ∀ i, uctCount sel (Fintype.card ι) i = 1
  greedy : ∀ t, Fintype.card ι ≤ t → ∀ j,
    uctIndex c (Q t j) t (uctCount sel t j) ≤ uctIndex c (Q t (sel t)) t (uctCount sel t (sel t))

omit [Fintype ι] in
theorem uctCount_succ (sel : ℕ → ι) (t : ℕ) (i : ι) :
    uctCount sel (t + 1) i = uctCount sel t i + if sel t = i then 1 else 0 := by
  unfold uctCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem uctCount_sum (sel : ℕ → ι) : ∀ t, ∑ i, uctCount sel t i = t
  | 0 => by simp [uctCount]
  | t + 1 => by
      simp only [uctCount_succ, Finset.sum_add_distrib, uctCount_sum sel t]
      simp

omit [Fintype ι] in
theorem uctCount_mono (sel : ℕ → ι) (i : ι) {s t : ℕ} (hst : s ≤ t) :
    uctCount sel s i ≤ uctCount sel t i :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hst))

theorem uctCount_le_time (sel : ℕ → ι) (t : ℕ) (i : ι) : uctCount sel t i ≤ t := by
  have := uctCount_sum sel t
  calc uctCount sel t i ≤ ∑ j, uctCount sel t j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    _ = t := this

variable {c : ℝ} {Q : ℕ → ι → ℝ} {sel : ℕ → ι}

theorem UCTRun.one_le (h : UCTRun c Q sel) (i : ι) {t : ℕ} (ht : Fintype.card ι ≤ t) :
    1 ≤ uctCount sel t i := by
  have := uctCount_mono sel i ht
  rwa [h.forced] at this

/-- **Steps 2-3 of the proof of `thm:selective-separation`: UCT count bound.**  If the
empirical mean of arm `i` never exceeds `u0` and some arm `star` always has empirical mean
at least `b > u0`, then for all `t ≥ |ι|`,
`N_i(t) ≤ max {1, 1 + c² log (1 + t) / (b - u0)²}`. -/
theorem UCTRun.count_le (h : UCTRun c Q sel) (hc : 0 ≤ c) {i star : ι} {u0 b : ℝ}
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
      unfold uctIndex at hg
      have h1 : 0 ≤ c * Real.sqrt (Real.log (1 + (t : ℝ)) / (uctCount sel t star : ℝ)) :=
        mul_nonneg hc (Real.sqrt_nonneg _)
      have h2 := hstar t
      have h3 := hi t
      linarith) t ht
  rw [h.forced] at this
  simpa using this

/-- **Window lower bound for local UCT** (the argument of Step 1 and of the near-rival
estimate in Step 3 of the proof of `thm:selective-separation`).  At a node with `K = |ι|`
arms whose empirical means are at most `B`, let the arm `e0` have empirical mean at least
`B - γ`, let `η > 0`, and let `t ≥ 2K` satisfy
`K (c² log (1 + t) / η² + 1) < t - ⌊t/2⌋` (true for all large `t`).  Then
`c² log (1 + ⌊t/2⌋) < (γ + η)² N_{e0}(t)`. -/
theorem UCTRun.window_lower (h : UCTRun c Q sel) (hc : 0 < c) {B γ η : ℝ} (hη : 0 < η)
    (hγ : 0 ≤ γ) (hQ1 : ∀ t i, Q t i ≤ B) {e0 : ι} (hQ0 : ∀ t, B - γ ≤ Q t e0) {t : ℕ}
    (ht : 2 * Fintype.card ι ≤ t)
    (hwin : (Fintype.card ι : ℝ) * (c ^ 2 * Real.log (1 + t) / η ^ 2 + 1)
      < (t : ℝ) - (t / 2 : ℕ)) :
    c ^ 2 * Real.log (1 + (t / 2 : ℕ)) < (γ + η) ^ 2 * uctCount sel t e0 := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = t / 2 := ⟨_, rfl⟩
  rw [← hs0] at hcon hwin
  have hKs0 : Fintype.card ι ≤ s0 := by omega
  have hs0t : s0 ≤ t := by omega
  have hγη : 0 < γ + η := by linarith
  have hη2 : 0 < η ^ 2 := by positivity
  -- the index of `e0` is at least `B + η` throughout the window
  have hA : ∀ s, s0 ≤ s → s < t → B + η ≤ uctIndex c (Q s e0) s (uctCount sel s e0) := by
    intro s hs hst
    have hns : (0 : ℝ) < uctCount sel s e0 := by
      exact_mod_cast h.one_le e0 (hKs0.trans hs)
    have hmono : (uctCount sel s e0 : ℝ) ≤ uctCount sel t e0 := by
      exact_mod_cast uctCount_mono sel e0 hst.le
    have hlog : Real.log (1 + (s0 : ℝ)) ≤ Real.log (1 + (s : ℝ)) :=
      Real.log_le_log (by positivity) (by
        have : (s0 : ℝ) ≤ s := by exact_mod_cast hs
        linarith)
    have h4 : (γ + η) ^ 2 ≤ c ^ 2 * (Real.log (1 + (s : ℝ)) / uctCount sel s e0) := by
      rw [← mul_div_assoc, le_div_iff₀ hns]
      have h5 : (γ + η) ^ 2 * (uctCount sel s e0 : ℝ) ≤ (γ + η) ^ 2 * uctCount sel t e0 :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
      have h6 := mul_le_mul_of_nonneg_left hlog (sq_nonneg c)
      linarith
    have hsq : γ + η ≤ c * Real.sqrt (Real.log (1 + (s : ℝ)) / uctCount sel s e0) := by
      have h5 : Real.sqrt ((γ + η) ^ 2)
          ≤ Real.sqrt (c ^ 2 * (Real.log (1 + (s : ℝ)) / uctCount sel s e0)) :=
        Real.sqrt_le_sqrt h4
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, Real.sqrt_sq hγη.le] at h5
      exact h5
    unfold uctIndex
    linarith [hQ0 s]
  -- hence every arm gains at most `c² log (1 + t) / η² + 1` selections in the window
  have hB : ∀ j u, s0 ≤ u → u ≤ t →
      (uctCount sel u j : ℝ) - uctCount sel s0 j ≤ c ^ 2 * Real.log (1 + t) / η ^ 2 + 1 := by
    intro j u hu
    have hlt0 : 0 ≤ Real.log (1 + (t : ℝ)) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith)
    have hnn : 0 ≤ c ^ 2 * Real.log (1 + (t : ℝ)) / η ^ 2 :=
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
        unfold uctIndex at hg
        have hnu : (0 : ℝ) < uctCount sel u j := by
          exact_mod_cast h.one_le j (hKs0.trans hu)
        have h1 : η ≤ c * Real.sqrt (Real.log (1 + (u : ℝ)) / uctCount sel u j) := by
          linarith [hQ1 u j]
        have hlogu : 0 ≤ Real.log (1 + (u : ℝ)) := Real.log_nonneg (by
          have : (0 : ℝ) ≤ u := Nat.cast_nonneg u
          linarith)
        have h2 : η ^ 2 ≤ (c * Real.sqrt (Real.log (1 + (u : ℝ)) / uctCount sel u j)) ^ 2 :=
          pow_le_pow_left₀ hη.le h1 2
        rw [mul_pow, Real.sq_sqrt (div_nonneg hlogu hnu.le), ← mul_div_assoc,
          le_div_iff₀ hnu] at h2
        have hlogut : Real.log (1 + (u : ℝ)) ≤ Real.log (1 + (t : ℝ)) :=
          Real.log_le_log (by positivity) (by
            have : (u : ℝ) ≤ t := by exact_mod_cast (by omega : u ≤ t)
            linarith)
        have h3 : (uctCount sel u j : ℝ) ≤ c ^ 2 * Real.log (1 + t) / η ^ 2 := by
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
      ≤ ∑ _j : ι, (c ^ 2 * Real.log (1 + t) / η ^ 2 + 1) :=
    Finset.sum_le_sum (fun j _ => hB j t hs0t le_rfl)
  have hl : ∑ j, ((uctCount sel t j : ℝ) - uctCount sel s0 j) = (t : ℝ) - s0 := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, uctCount_sum, uctCount_sum]
  rw [hl, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith

/-- **Step 1 of the proof of `thm:selective-separation`: logarithmic fairness of local UCT,
in explicit form.**  At a node with `K = |ι|` arms whose empirical means lie in `[0, 1]`,
let `t ≥ 2K` satisfy `K (c² log (1 + t) + 1) < t - ⌊t/2⌋` (true for all large `t`).  Then
every arm has been selected more than `(c²/4) log (1 + ⌊t/2⌋)` times:
`c² log (1 + ⌊t/2⌋) < 4 N_e(t)`. -/
theorem UCTRun.fairness (h : UCTRun c Q sel) (hc : 0 < c) (hQ0 : ∀ t i, 0 ≤ Q t i)
    (hQ1 : ∀ t i, Q t i ≤ 1) {t : ℕ} (ht : 2 * Fintype.card ι ≤ t)
    (hwin : (Fintype.card ι : ℝ) * (c ^ 2 * Real.log (1 + t) + 1) < (t : ℝ) - (t / 2 : ℕ))
    (e0 : ι) : c ^ 2 * Real.log (1 + (t / 2 : ℕ)) < 4 * uctCount sel t e0 := by
  have := h.window_lower hc (B := 1) (γ := 1) (η := 1) one_pos zero_le_one hQ1 (e0 := e0)
    (fun t => by rw [sub_self]; exact hQ0 t e0) ht (by rw [one_pow, div_one]; exact hwin)
  norm_num at this
  linarith

end UCT

/-! ### Circuits and monitor vertices (tree part of the cost model) -/

namespace MaxCirc

variable {Z : Type*}

/-- Number of vertices of the tree unfolding. -/
def uctSize : MaxCirc Z → ℕ
  | term _ => 1
  | unary c => uctSize c + 1
  | bin c d => uctSize c + uctSize d + 1

/-- Longest path to a terminal. -/
def uctHeight : MaxCirc Z → ℕ
  | term _ => 0
  | unary c => uctHeight c + 1
  | bin c d => max (uctHeight c) (uctHeight d) + 1

/-- A rollout below a vertex: at depth `d` a binary vertex takes its first child if
`rule d` and its second child otherwise.  Returns the terminal reached and the number of
edges traversed. -/
def uctWalk (rule : ℕ → Bool) : ℕ → MaxCirc Z → Z × ℕ
  | _, term z => (z, 0)
  | d, unary c => ((uctWalk rule (d + 1) c).1, (uctWalk rule (d + 1) c).2 + 1)
  | d, bin c e =>
      bif rule d then ((uctWalk rule (d + 1) c).1, (uctWalk rule (d + 1) c).2 + 1)
      else ((uctWalk rule (d + 1) e).1, (uctWalk rule (d + 1) e).2 + 1)

/-- Every terminal below the vertex satisfies `P`. -/
def AllTerm (P : Z → Prop) : MaxCirc Z → Prop
  | term z => P z
  | unary c => AllTerm P c
  | bin c d => AllTerm P c ∧ AllTerm P d

/-- Number of terminal occurrences below the vertex that are flagged by `p`. -/
def uctOcc (p : Z → Bool) : MaxCirc Z → ℕ
  | term z => if p z then 1 else 0
  | unary c => uctOcc p c
  | bin c d => uctOcc p c + uctOcc p d

theorem uctWalk_snd_le (rule : ℕ → Bool) :
    ∀ (c : MaxCirc Z) (d : ℕ), (uctWalk rule d c).2 ≤ c.uctHeight
  | term _, _ => le_rfl
  | unary c, d => by
      have := uctWalk_snd_le rule c (d + 1)
      simp only [uctWalk, uctHeight]
      omega
  | bin c e, d => by
      have h1 := uctWalk_snd_le rule c (d + 1)
      have h2 := uctWalk_snd_le rule e (d + 1)
      cases hr : rule d <;>
        simp only [uctWalk, uctHeight, hr, Bool.cond_true, Bool.cond_false] <;> omega

theorem uctWalk_mem {P : Z → Prop} (rule : ℕ → Bool) :
    ∀ (c : MaxCirc Z) (d : ℕ), AllTerm P c → P (uctWalk rule d c).1
  | term _, _, h => h
  | unary c, d, h => uctWalk_mem rule c (d + 1) h
  | bin c e, d, h => by
      have h' : AllTerm P c ∧ AllTerm P e := h
      cases hr : rule d
      · simp only [uctWalk, hr, Bool.cond_false]
        exact uctWalk_mem rule e (d + 1) h'.2
      · simp only [uctWalk, hr, Bool.cond_true]
        exact uctWalk_mem rule c (d + 1) h'.1

theorem AllTerm.mono {P P' : Z → Prop} (hPP : ∀ z, P z → P' z) :
    ∀ c : MaxCirc Z, AllTerm P c → AllTerm P' c
  | term z, h => hPP z h
  | unary c, h => AllTerm.mono hPP c h
  | bin c d, h => by
      have h' : AllTerm P c ∧ AllTerm P d := h
      exact ⟨AllTerm.mono hPP c h'.1, AllTerm.mono hPP d h'.2⟩

theorem uctOcc_mono {p q : Z → Bool} (hpq : ∀ z, p z = true → q z = true) :
    ∀ c : MaxCirc Z, uctOcc p c ≤ uctOcc q c
  | term z => by
      simp only [uctOcc]
      by_cases hp : p z = true
      · rw [ite_eq_left hp, ite_eq_left (hpq z hp)]
      · rw [ite_eq_right hp]
        exact Nat.zero_le _
  | unary c => uctOcc_mono hpq c
  | bin c d => Nat.add_le_add (uctOcc_mono hpq c) (uctOcc_mono hpq d)

end MaxCirc

/-- Interval of a MAX vertex from the intervals of two children. -/
def uctJoin (p q : ℝ × ℝ) : ℝ × ℝ := (max p.1 q.1, max p.2 q.2)

/-- A monitor graph: an all-MAX circuit whose internal vertices store an interval. -/
inductive UctNode (Z : Type*) where
  | term : Z → UctNode Z
  | unary : ℝ × ℝ → UctNode Z → UctNode Z
  | bin : ℝ × ℝ → UctNode Z → UctNode Z → UctNode Z

namespace UctNode

variable {Z : Type*}

/-- The underlying circuit. -/
def shape : UctNode Z → MaxCirc Z
  | term z => .term z
  | unary _ c => .unary (shape c)
  | bin _ c d => .bin (shape c) (shape d)

/-- The interval stored at the vertex (read from the terminal table at a terminal). -/
def val (x : Z → ℝ × ℝ) : UctNode Z → ℝ × ℝ
  | term z => x z
  | unary v _ => v
  | bin v _ _ => v

/-- Every stored interval satisfies `P`. -/
def AllVal (P : ℝ × ℝ → Prop) : UctNode Z → Prop
  | term _ => True
  | unary v c => P v ∧ AllVal P c
  | bin v c d => P v ∧ AllVal P c ∧ AllVal P d

theorem val_of_allVal {P : ℝ × ℝ → Prop} {Q : Z → Prop} {x : Z → ℝ × ℝ}
    (hx : ∀ z, Q z → P (x z)) :
    ∀ n : UctNode Z, MaxCirc.AllTerm Q n.shape → n.AllVal P → P (n.val x)
  | term z, h, _ => hx z h
  | unary _ _, _, h => h.1
  | bin _ _ _, _, h => h.1

end UctNode

section Wave

variable {Z : Type*}

/-- Build the monitor graph of a circuit from the terminal table. -/
def uctBuild (x : Z → ℝ × ℝ) : MaxCirc Z → UctNode Z
  | .term z => .term z
  | .unary c => .unary ((uctBuild x c).val x) (uctBuild x c)
  | .bin c d =>
      .bin (uctJoin ((uctBuild x c).val x) ((uctBuild x d).val x)) (uctBuild x c) (uctBuild x d)

theorem uctBuild_shape (x : Z → ℝ × ℝ) : ∀ c : MaxCirc Z, (uctBuild x c).shape = c
  | .term _ => rfl
  | .unary c => congrArg MaxCirc.unary (uctBuild_shape x c)
  | .bin c d => by
      show MaxCirc.bin (uctBuild x c).shape (uctBuild x d).shape = MaxCirc.bin c d
      rw [uctBuild_shape x c, uctBuild_shape x d]

open Classical in
/-- A propagation wave in reverse topological order.  `x` is the new terminal table and
`chg z` says whether the interval of terminal `z` changed.  A vertex receives a delivery
from each child whose interval changed and is then recomputed; a delivery costs `1` at a
unary parent and `2` at a binary parent.  Returns the new graph, whether the interval of
its top vertex changed, and the work. -/
def uctWave (x : Z → ℝ × ℝ) (chg : Z → Bool) : UctNode Z → UctNode Z × Bool × ℕ
  | .term z => (.term z, chg z, 0)
  | .unary v c =>
      if (uctWave x chg c).2.1 then
        (.unary ((uctWave x chg c).1.val x) (uctWave x chg c).1,
          decide ((uctWave x chg c).1.val x ≠ v), (uctWave x chg c).2.2 + 1)
      else (.unary v (uctWave x chg c).1, false, (uctWave x chg c).2.2)
  | .bin v c d =>
      if (uctWave x chg c).2.1 = true ∨ (uctWave x chg d).2.1 = true then
        (.bin (uctJoin ((uctWave x chg c).1.val x) ((uctWave x chg d).1.val x))
            (uctWave x chg c).1 (uctWave x chg d).1,
          decide (uctJoin ((uctWave x chg c).1.val x) ((uctWave x chg d).1.val x) ≠ v),
          (uctWave x chg c).2.2 + (uctWave x chg d).2.2
            + (if (uctWave x chg c).2.1 then 2 else 0) + (if (uctWave x chg d).2.1 then 2 else 0))
      else (.bin v (uctWave x chg c).1 (uctWave x chg d).1, false,
        (uctWave x chg c).2.2 + (uctWave x chg d).2.2)

theorem uctWave_shape (x : Z → ℝ × ℝ) (chg : Z → Bool) :
    ∀ n : UctNode Z, (uctWave x chg n).1.shape = n.shape
  | .term _ => rfl
  | .unary v c => by
      have ih := uctWave_shape x chg c
      by_cases hf : (uctWave x chg c).2.1 = true
      · rw [uctWave, ite_eq_left hf]
        exact congrArg MaxCirc.unary ih
      · rw [uctWave, ite_eq_right hf]
        exact congrArg MaxCirc.unary ih
  | .bin v c d => by
      have ic := uctWave_shape x chg c
      have id := uctWave_shape x chg d
      by_cases hf : (uctWave x chg c).2.1 = true ∨ (uctWave x chg d).2.1 = true
      · rw [uctWave, ite_eq_left hf]
        show MaxCirc.bin _ _ = MaxCirc.bin _ _
        rw [ic, id]
      · rw [uctWave, ite_eq_right hf]
        show MaxCirc.bin _ _ = MaxCirc.bin _ _
        rw [ic, id]

/-- **Work of a wave.**  The work is at most twice the number of flagged terminal
occurrences times the height, and the top interval can change only if some flagged
terminal occurs below. -/
theorem uctWave_cost_le (x : Z → ℝ × ℝ) (chg : Z → Bool) :
    ∀ n : UctNode Z,
      (uctWave x chg n).2.2 ≤ 2 * (n.shape.uctOcc chg * n.shape.uctHeight) ∧
        ((uctWave x chg n).2.1 = true → 1 ≤ n.shape.uctOcc chg)
  | .term z => by
      refine ⟨Nat.zero_le _, fun h => ?_⟩
      have h' : chg z = true := h
      show 1 ≤ if chg z = true then 1 else 0
      rw [ite_eq_left h']
  | .unary v c => by
      obtain ⟨ih1, ih2⟩ := uctWave_cost_le x chg c
      have e : 2 * (c.shape.uctOcc chg * (c.shape.uctHeight + 1))
          = 2 * (c.shape.uctOcc chg * c.shape.uctHeight) + 2 * c.shape.uctOcc chg := by ring
      by_cases hf : (uctWave x chg c).2.1 = true
      · have h1 := ih2 hf
        rw [uctWave, ite_eq_left hf]
        refine ⟨?_, fun _ => h1⟩
        show (uctWave x chg c).2.2 + 1 ≤ 2 * (c.shape.uctOcc chg * (c.shape.uctHeight + 1))
        omega
      · rw [uctWave, ite_eq_right hf]
        refine ⟨?_, fun h => absurd h (by simp)⟩
        show (uctWave x chg c).2.2 ≤ 2 * (c.shape.uctOcc chg * (c.shape.uctHeight + 1))
        omega
  | .bin v c d => by
      obtain ⟨ic1, ic2⟩ := uctWave_cost_le x chg c
      obtain ⟨id1, id2⟩ := uctWave_cost_le x chg d
      have e : 2 * ((c.shape.uctOcc chg + d.shape.uctOcc chg)
            * (max c.shape.uctHeight d.shape.uctHeight + 1))
          = 2 * (c.shape.uctOcc chg * max c.shape.uctHeight d.shape.uctHeight)
            + 2 * (d.shape.uctOcc chg * max c.shape.uctHeight d.shape.uctHeight)
            + 2 * c.shape.uctOcc chg + 2 * d.shape.uctOcc chg := by ring
      have t1 : c.shape.uctOcc chg * c.shape.uctHeight
          ≤ c.shape.uctOcc chg * max c.shape.uctHeight d.shape.uctHeight :=
        Nat.mul_le_mul_left _ (le_max_left _ _)
      have t2 : d.shape.uctOcc chg * d.shape.uctHeight
          ≤ d.shape.uctOcc chg * max c.shape.uctHeight d.shape.uctHeight :=
        Nat.mul_le_mul_left _ (le_max_right _ _)
      by_cases hf : (uctWave x chg c).2.1 = true ∨ (uctWave x chg d).2.1 = true
      · rw [uctWave, ite_eq_left hf]
        refine ⟨?_, fun _ => ?_⟩
        · show (uctWave x chg c).2.2 + (uctWave x chg d).2.2
              + (if (uctWave x chg c).2.1 = true then 2 else 0)
              + (if (uctWave x chg d).2.1 = true then 2 else 0)
            ≤ 2 * ((c.shape.uctOcc chg + d.shape.uctOcc chg)
              * (max c.shape.uctHeight d.shape.uctHeight + 1))
          have u1 : (if (uctWave x chg c).2.1 = true then 2 else 0) ≤ 2 * c.shape.uctOcc chg := by
            split_ifs with h
            · have := ic2 h
              omega
            · exact Nat.zero_le _
          have u2 : (if (uctWave x chg d).2.1 = true then 2 else 0) ≤ 2 * d.shape.uctOcc chg := by
            split_ifs with h
            · have := id2 h
              omega
            · exact Nat.zero_le _
          omega
        · show 1 ≤ c.shape.uctOcc chg + d.shape.uctOcc chg
          rcases hf with h | h
          · have := ic2 h
            omega
          · have := id2 h
            omega
      · rw [uctWave, ite_eq_right hf]
        refine ⟨?_, fun h => absurd h (by simp)⟩
        show (uctWave x chg c).2.2 + (uctWave x chg d).2.2
          ≤ 2 * ((c.shape.uctOcc chg + d.shape.uctOcc chg)
            * (max c.shape.uctHeight d.shape.uctHeight + 1))
        omega

/-- A wave preserves any property of the stored intervals that holds for the table entries
of the terminals below and is closed under `uctJoin`. -/
theorem uctWave_allVal {P : ℝ × ℝ → Prop} {Q : Z → Prop} {x : Z → ℝ × ℝ} (chg : Z → Bool)
    (hx : ∀ z, Q z → P (x z)) (hJ : ∀ p q, P p → P q → P (uctJoin p q)) :
    ∀ n : UctNode Z, MaxCirc.AllTerm Q n.shape → n.AllVal P → (uctWave x chg n).1.AllVal P
  | .term _, _, _ => trivial
  | .unary v c, hq, h => by
      have hq' : MaxCirc.AllTerm Q c.shape := hq
      obtain ⟨hv, hc⟩ : P v ∧ c.AllVal P := h
      have ih := uctWave_allVal chg hx hJ c hq' hc
      have hval := UctNode.val_of_allVal hx (uctWave x chg c).1
        (by rw [uctWave_shape]; exact hq') ih
      by_cases hf : (uctWave x chg c).2.1 = true
      · rw [uctWave, ite_eq_left hf]
        exact ⟨hval, ih⟩
      · rw [uctWave, ite_eq_right hf]
        exact ⟨hv, ih⟩
  | .bin v c d, hq, h => by
      have hq' : MaxCirc.AllTerm Q c.shape ∧ MaxCirc.AllTerm Q d.shape := hq
      obtain ⟨hv, hc, hd⟩ : P v ∧ c.AllVal P ∧ d.AllVal P := h
      have ic := uctWave_allVal chg hx hJ c hq'.1 hc
      have id := uctWave_allVal chg hx hJ d hq'.2 hd
      have hvc := UctNode.val_of_allVal hx (uctWave x chg c).1
        (by rw [uctWave_shape]; exact hq'.1) ic
      have hvd := UctNode.val_of_allVal hx (uctWave x chg d).1
        (by rw [uctWave_shape]; exact hq'.2) id
      by_cases hf : (uctWave x chg c).2.1 = true ∨ (uctWave x chg d).2.1 = true
      · rw [uctWave, ite_eq_left hf]
        exact ⟨hJ _ _ hvc hvd, ic, id⟩
      · rw [uctWave, ite_eq_right hf]
        exact ⟨hv, ic, id⟩

theorem uctBuild_allVal {P : ℝ × ℝ → Prop} {Q : Z → Prop} {x : Z → ℝ × ℝ}
    (hx : ∀ z, Q z → P (x z)) (hJ : ∀ p q, P p → P q → P (uctJoin p q)) :
    ∀ c : MaxCirc Z, MaxCirc.AllTerm Q c → (uctBuild x c).AllVal P
  | .term _, _ => trivial
  | .unary c, hq => by
      have hq' : MaxCirc.AllTerm Q c := hq
      have ih := uctBuild_allVal hx hJ c hq'
      exact ⟨UctNode.val_of_allVal hx _ (by rw [uctBuild_shape]; exact hq') ih, ih⟩
  | .bin c d, hq => by
      have hq' : MaxCirc.AllTerm Q c ∧ MaxCirc.AllTerm Q d := hq
      have ic := uctBuild_allVal hx hJ c hq'.1
      have id := uctBuild_allVal hx hJ d hq'.2
      exact ⟨hJ _ _ (UctNode.val_of_allVal hx _ (by rw [uctBuild_shape]; exact hq'.1) ic)
        (UctNode.val_of_allVal hx _ (by rw [uctBuild_shape]; exact hq'.2) id), ic, id⟩

end Wave

/-! ### The wide common-core family (`thm:ta-core`): the DAG -/

section Balanced

variable {Z : Type*}

/-- Balanced binary tree over the leaves `leaf lo, …, leaf (lo + len - 1)`; `d` bounds the
recursion depth. -/
def uctBal (leaf : ℕ → Z) : ℕ → ℕ → ℕ → MaxCirc Z
  | 0, lo, _ => .term (leaf lo)
  | d + 1, lo, len =>
      if len ≤ 1 then .term (leaf lo)
      else .bin (uctBal leaf d lo ((len + 1) / 2)) (uctBal leaf d (lo + (len + 1) / 2) (len / 2))

theorem uctBal_height (leaf : ℕ → Z) : ∀ d lo len, (uctBal leaf d lo len).uctHeight ≤ d
  | 0, _, _ => le_rfl
  | d + 1, lo, len => by
      unfold uctBal
      split_ifs
      · exact Nat.zero_le _
      · have h1 := uctBal_height leaf d lo ((len + 1) / 2)
        have h2 := uctBal_height leaf d (lo + (len + 1) / 2) (len / 2)
        show max _ _ + 1 ≤ d + 1
        omega

theorem uctBal_size (leaf : ℕ → Z) : ∀ d lo len, 1 ≤ len → len ≤ 2 ^ d →
    (uctBal leaf d lo len).uctSize + 1 = 2 * len
  | 0, lo, len, h1, h2 => by
      have : len = 1 := by
        rw [pow_zero] at h2
        omega
      subst this
      rfl
  | d + 1, lo, len, h1, h2 => by
      unfold uctBal
      split_ifs with hm
      · have : len = 1 := by omega
        subst this
        rfl
      · rw [pow_succ] at h2
        have a := uctBal_size leaf d lo ((len + 1) / 2) (by omega) (by omega)
        have b := uctBal_size leaf d (lo + (len + 1) / 2) (len / 2) (by omega) (by omega)
        show (uctBal leaf d lo ((len + 1) / 2)).uctSize
          + (uctBal leaf d (lo + (len + 1) / 2) (len / 2)).uctSize + 1 + 1 = 2 * len
        omega

theorem uctBal_allTerm {P : Z → Prop} (leaf : ℕ → Z) (hP : ∀ j, P (leaf j)) :
    ∀ d lo len, MaxCirc.AllTerm P (uctBal leaf d lo len)
  | 0, lo, _ => hP lo
  | d + 1, lo, len => by
      unfold uctBal
      split_ifs
      · exact hP lo
      · exact ⟨uctBal_allTerm leaf hP d _ _, uctBal_allTerm leaf hP d _ _⟩

theorem uctBal_occ (leaf : ℕ → Z) (p : Z → Bool) : ∀ d lo len, 1 ≤ len →
    (uctBal leaf d lo len).uctOcc p ≤ ∑ j ∈ Ico lo (lo + len), if p (leaf j) then 1 else 0
  | 0, lo, len, h1 =>
      Finset.single_le_sum (f := fun j => if p (leaf j) then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  | d + 1, lo, len, h1 => by
      unfold uctBal
      split_ifs with hm
      · exact Finset.single_le_sum (f := fun j => if p (leaf j) then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
      · have a := uctBal_occ leaf p d lo ((len + 1) / 2) (by omega)
        have b := uctBal_occ leaf p d (lo + (len + 1) / 2) (len / 2) (by omega)
        have e : lo + (len + 1) / 2 + len / 2 = lo + len := by omega
        rw [e] at b
        have hcons := Finset.sum_Ico_consecutive (fun j => if p (leaf j) then 1 else 0)
          (show lo ≤ lo + (len + 1) / 2 by omega) (show lo + (len + 1) / 2 ≤ lo + len by omega)
        show (uctBal leaf d lo ((len + 1) / 2)).uctOcc p
          + (uctBal leaf d (lo + (len + 1) / 2) (len / 2)).uctOcc p ≤ _
        omega

end Balanced

section CoreGraph

variable (r : ℕ) [NeZero r]

/-- The `j`-th core leaf. -/
def coreLeaf (j : ℕ) : CoreZ r := Sum.inl (Fin.ofNat (r ^ 2) j)

/-- The shared hub: a balanced binary tree over the `r²` core leaves. -/
def coreHub : MaxCirc (CoreZ r) := uctBal (coreLeaf r) (Nat.clog 2 (r ^ 2)) 0 (r ^ 2)

/-- The private leaf of the losing action `i`. -/
def corePriv (r : ℕ) (i : Fin r) : CoreZ r := Sum.inr (Sum.inl i)

/-- The terminal of the winning direct action. -/
def coreWinZ (r : ℕ) : CoreZ r := Sum.inr (Sum.inr ())

/-- The subgraph below a root action.  Actions `0, …, r - 1` are the losing actions: a
binary vertex over the shared hub and the private leaf.  Action `r` is the winning direct
action.  The hub is one shared vertex of the DAG; it appears here once per losing action
only because `MaxCirc` is the tree unfolding used by the sampler. -/
def coreAct (a : Fin (r + 1)) : MaxCirc (CoreZ r) :=
  if h : (a : ℕ) < r then .bin (coreHub r) (.term (corePriv r ⟨a, h⟩)) else .term (coreWinZ r)

/-- Deterministic return of a root action: `0` for the losing actions, `1` for the winner. -/
def coreMu (r : ℕ) (a : Fin (r + 1)) : ℝ := if (a : ℕ) < r then 0 else 1

theorem coreHub_height : (coreHub r).uctHeight ≤ Nat.clog 2 (r ^ 2) := uctBal_height _ _ _ _

/-- The hub has `2 r² - 1` vertices: the DAG has `Θ(r²)` vertices and edges. -/
theorem coreHub_size : (coreHub r).uctSize + 1 = 2 * r ^ 2 :=
  uctBal_size _ _ _ _ (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.le_pow_clog (by norm_num) _)

theorem coreHub_zero : MaxCirc.AllTerm (fun z => coreReward r z = 0) (coreHub r) :=
  uctBal_allTerm (P := fun z => coreReward r z = 0) (coreLeaf r) (fun _ => rfl) _ _ _

/-- Every core leaf occurs once in the hub. -/
theorem coreHub_occ (z : CoreZ r) : (coreHub r).uctOcc (fun w => decide (w = z)) ≤ 1 := by
  have hpos : 1 ≤ r ^ 2 := Nat.pos_of_ne_zero (NeZero.ne _)
  refine le_trans (uctBal_occ (coreLeaf r) _ _ 0 (r ^ 2) hpos) ?_
  rw [zero_add]
  rcases z with i | p
  · calc ∑ j ∈ Ico 0 (r ^ 2), (if decide (coreLeaf r j = Sum.inl i) = true then 1 else 0)
        ≤ ∑ j ∈ Ico 0 (r ^ 2), (if j = (i : ℕ) then 1 else 0) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hjlt : j < r ^ 2 := (Finset.mem_Ico.mp hj).2
          by_cases hji : j = (i : ℕ)
          · rw [ite_eq_left hji]
            split_ifs <;> omega
          · have : coreLeaf r j ≠ Sum.inl i := by
              intro e
              have e' : Fin.ofNat (r ^ 2) j = i := Sum.inl_injective e
              have e'' := congrArg Fin.val e'
              rw [Fin.val_ofNat, Nat.mod_eq_of_lt hjlt] at e''
              exact hji e''
            simp [this]
      _ ≤ 1 := by
          rw [Finset.sum_ite_eq' (Ico 0 (r ^ 2)) (i : ℕ) (fun _ => 1)]
          split_ifs <;> omega
  · refine le_trans (le_of_eq (Finset.sum_eq_zero (fun j _ => ?_))) (Nat.zero_le 1)
    have : coreLeaf r j ≠ Sum.inr p := by
      intro e
      exact Sum.inl_ne_inr e
    simp [this]

theorem coreAct_reward (a : Fin (r + 1)) :
    MaxCirc.AllTerm (fun z => coreReward r z = coreMu r a) (coreAct r a) := by
  unfold coreAct coreMu
  split_ifs with h
  · exact ⟨coreHub_zero r, rfl⟩
  · rfl

theorem coreAct_height (a : Fin (r + 1)) : (coreAct r a).uctHeight ≤ Nat.clog 2 (r ^ 2) + 1 := by
  unfold coreAct
  split_ifs with h
  · have := coreHub_height r
    show max (coreHub r).uctHeight 0 + 1 ≤ _
    omega
  · exact Nat.zero_le _

/-! #### The search process -/

/-- A run of UCT search (`c = 2`) on the common-core DAG.  `sel s` is the root action of
rollout `s`, `rule s` the path rule below the root at rollout `s` (arbitrary; in particular
recursive UCT in the hub with any tie-breaking), `zt s` the terminal reached, whose
point-mass reward `coreReward` is observed.  The root is a UCT node whose empirical means
are the averages of the observed rewards. -/
structure CoreSearch (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r) :
    Prop where
  reach : ∀ s, zt s = ((coreAct r (sel s)).uctWalk (rule s) 0).1
  uct : UCTRun 2 (fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a), coreReward r (zt s))
    / uctCount sel t a) sel

variable {r} {rule : ℕ → ℕ → Bool} {sel : ℕ → Fin (r + 1)} {zt : ℕ → CoreZ r}

/-- Every rollout through a losing action returns `0`, every rollout through the winning
action returns `1`. -/
theorem CoreSearch.reward_eq (h : CoreSearch r rule sel zt) (s : ℕ) :
    coreReward r (zt s) = coreMu r (sel s) := by
  rw [h.reach]
  exact MaxCirc.uctWalk_mem (P := fun z => coreReward r z = coreMu r (sel s)) _ _ 0
    (coreAct_reward r (sel s))

theorem CoreSearch.Q_eq (h : CoreSearch r rule sel zt) {t : ℕ} {a : Fin (r + 1)}
    (hpos : 1 ≤ uctCount sel t a) :
    (∑ s ∈ (range t).filter (fun s => sel s = a), coreReward r (zt s)) / uctCount sel t a
      = coreMu r a := by
  have hs : ∑ s ∈ (range t).filter (fun s => sel s = a), coreReward r (zt s)
      = uctCount sel t a * coreMu r a := by
    rw [Finset.sum_congr rfl (fun s hs => by
      rw [h.reward_eq s, (Finset.mem_filter.mp hs).2] :
      ∀ s ∈ (range t).filter (fun s => sel s = a), coreReward r (zt s) = coreMu r a)]
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  have hne : (uctCount sel t a : ℝ) ≠ 0 := by exact_mod_cast (by omega : uctCount sel t a ≠ 0)
  rw [hs, mul_div_cancel_left₀ _ hne]

/-- **Identification of the root process.**  The root of the common-core search is a UCT
node with the deterministic means `coreMu`. -/
theorem CoreSearch.run (h : CoreSearch r rule sel zt) :
    UCTRun 2 (fun _ a => coreMu r a) sel where
  forced := h.uct.forced
  greedy := by
    intro t ht j
    have := h.uct.greedy t ht j
    rw [h.Q_eq (h.uct.one_le j ht), h.Q_eq (h.uct.one_le (sel t) ht)] at this
    exact this

omit [NeZero r] in
/-- **`thm:ta-core`, count of the winning action.**  The `r` losing actions together
receive at most `r (1 + 4 log (1 + t))` rollouts, so
`N_win(t) ≥ t - r (1 + 4 log (1 + t))`. -/
theorem core_win_count_ge (h : UCTRun 2 (fun _ a => coreMu r a) sel) {t : ℕ} (ht : r + 1 ≤ t) :
    (t : ℝ) - r * (1 + 4 * Real.log (1 + t)) ≤ uctCount sel t (Fin.last r) := by
  have hcard : Fintype.card (Fin (r + 1)) ≤ t := by rw [Fintype.card_fin]; exact ht
  have hlog : 0 ≤ Real.log (1 + (t : ℝ)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith)
  have hlast : coreMu r (Fin.last r) = 1 := by simp [coreMu]
  have hlose : ∀ i : Fin r, (uctCount sel t (Fin.castSucc i) : ℝ) ≤ 1 + 4 * Real.log (1 + t) := by
    intro i
    have hmu : coreMu r (Fin.castSucc i) = 0 := by simp [coreMu]
    have := h.count_le (by norm_num) (i := Fin.castSucc i) (star := Fin.last r) (u0 := 0)
      (b := 1) (by norm_num) (fun _ => le_of_eq hmu) (fun _ => le_of_eq hlast.symm) hcard
    refine this.trans (max_le (by linarith) (le_of_eq ?_))
    norm_num
  have hsum := uctCount_sum sel t
  rw [Fin.sum_univ_castSucc] at hsum
  have hsumR : (∑ i : Fin r, (uctCount sel t (Fin.castSucc i) : ℝ))
      + uctCount sel t (Fin.last r) = t := by
    exact_mod_cast hsum
  have hle : ∑ i : Fin r, (uctCount sel t (Fin.castSucc i) : ℝ)
      ≤ ∑ _i : Fin r, (1 + 4 * Real.log (1 + t)) := Finset.sum_le_sum (fun i _ => hlose i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  linarith

end CoreGraph

/-! ### Monitors on the shared-hub DAG -/

section CoreMonitor

variable {r : ℕ}

/-- Monitor state on the common-core DAG: the active root actions, the monitor graph of the
shared hub (`none` once released), and the interval stored at the top vertex of each losing
action.  The winning action is a terminal vertex and is read from the terminal table. -/
structure CoreMon (r : ℕ) where
  act : Finset (Fin (r + 1))
  hub : Option (UctNode (CoreZ r))
  top : Fin r → ℝ × ℝ

/-- Stored lower endpoint of a root action. -/
def CoreMon.lo (σ : CoreMon r) (x : CoreZ r → ℝ × ℝ) (a : Fin (r + 1)) : ℝ :=
  if h : (a : ℕ) < r then (σ.top ⟨a, h⟩).1 else (x (coreWinZ r)).1

/-- Stored upper endpoint of a root action. -/
def CoreMon.hi (σ : CoreMon r) (x : CoreZ r → ℝ × ℝ) (a : Fin (r + 1)) : ℝ :=
  if h : (a : ℕ) < r then (σ.top ⟨a, h⟩).2 else (x (coreWinZ r)).2

/-- The stopping test of a root query at `ε = 1/5`: `a` is the canonical lower-bound
leader among the active actions and every active rival has `U - L(a) ≤ 1/5`. -/
def coreStops (σ : CoreMon r) (x : CoreZ r → ℝ × ℝ) (a : Fin (r + 1)) : Prop :=
  MarginalStops σ.act (σ.lo x) (σ.hi x) (1 / 5) a

/-- Work of a root query: two scans of the active actions. -/
def coreQueryCost (σ : CoreMon r) : ℕ := 2 * σ.act.card

/-- Number of vertices of a possibly released monitor graph. -/
def uctOptSize {Z : Type*} (o : Option (UctNode Z)) : ℕ := o.elim 0 (fun n => n.shape.uctSize)

open Classical in
/-- Actions that survive the retirement rule of `thm:decision-retirement`. -/
def coreKeep (x : CoreZ r → ℝ × ℝ) (σ : CoreMon r) : Finset (Fin (r + 1)) :=
  σ.act.filter (fun b => ¬ ∃ a ∈ σ.act, a ≠ b ∧ σ.hi x b < σ.lo x a)

open Classical in
/-- Retirement step.  The selective monitor (`s = true`) retires dominated actions (three
steps per active action for the checks, three per retired action to release its top vertex
and two incidences) and releases the hub once no losing action is active (one step per
vertex).  The eager monitor does nothing. -/
def coreRetire (s : Bool) (x : CoreZ r → ℝ × ℝ) (σ : CoreMon r) : CoreMon r × ℕ :=
  bif s then
    (⟨coreKeep x σ, if ∃ i : Fin r, Fin.castSucc i ∈ coreKeep x σ then σ.hub else none, σ.top⟩,
      3 * σ.act.card + 3 * (σ.act \ coreKeep x σ).card
        + if ∃ i : Fin r, Fin.castSucc i ∈ coreKeep x σ then 0 else uctOptSize σ.hub)
  else (σ, 0)

/-- The hub after a wave. -/
def coreHubNew (x' : CoreZ r → ℝ × ℝ) (chg : CoreZ r → Bool) (σ : CoreMon r) :
    Option (UctNode (CoreZ r)) := σ.hub.map (fun n => (uctWave x' chg n).1)

/-- Whether the interval of the hub's top vertex changed in the wave. -/
def coreHubFlag (x' : CoreZ r → ℝ × ℝ) (chg : CoreZ r → Bool) (σ : CoreMon r) : Bool :=
  σ.hub.elim false (fun n => (uctWave x' chg n).2.1)

/-- Work of the wave inside the hub. -/
def coreHubCost (x' : CoreZ r → ℝ × ℝ) (chg : CoreZ r → Bool) (σ : CoreMon r) : ℕ :=
  σ.hub.elim 0 (fun n => (uctWave x' chg n).2.2)

/-- Interval of the hub's top vertex. -/
def coreHubVal (x' : CoreZ r → ℝ × ℝ) (o : Option (UctNode (CoreZ r))) : ℝ × ℝ :=
  o.elim (0, 1) (fun n => n.val x')

open Classical in
/-- Propagation wave on the DAG: first inside the shared hub (once), then one delivery to
the top vertex of every active losing action if the hub's interval changed, and one from
its private leaf if that changed; each such delivery costs `2` (binary parent). -/
def coreWave (x' : CoreZ r → ℝ × ℝ) (chg : CoreZ r → Bool) (σ : CoreMon r) : CoreMon r × ℕ :=
  (⟨σ.act, coreHubNew x' chg σ,
      fun i => if Fin.castSucc i ∈ σ.act ∧
          (coreHubFlag x' chg σ = true ∨ chg (corePriv r i) = true) then
        uctJoin (coreHubVal x' (coreHubNew x' chg σ)) (x' (corePriv r i)) else σ.top i⟩,
    coreHubCost x' chg σ + ∑ i : Fin r, if Fin.castSucc i ∈ σ.act then
      (if coreHubFlag x' chg σ = true then 2 else 0) + (if chg (corePriv r i) = true then 2 else 0)
      else 0)

open Classical in
/-- Which terminal intervals change between step `k` and step `k + 1`. -/
def coreChg (x : ℕ → CoreZ r → ℝ × ℝ) (k : ℕ) (z : CoreZ r) : Bool :=
  decide (x (k + 1) z ≠ x k z)

/-- The monitor state before the query at step `k`. -/
def coreRun (s : Bool) (hub : MaxCirc (CoreZ r)) (x : ℕ → CoreZ r → ℝ × ℝ) : ℕ → CoreMon r
  | 0 => ⟨univ, some (uctBuild (x 0) hub),
      fun i => uctJoin ((uctBuild (x 0) hub).val (x 0)) (x 0 (corePriv r i))⟩
  | k + 1 => (coreWave (x (k + 1)) (coreChg x k) (coreRetire s (x k) (coreRun s hub x k)).1).1

/-- Monitor work of step `k`: query, retirement, terminal-table update, wave. -/
def coreStepCost (s : Bool) (hub : MaxCirc (CoreZ r)) (x : ℕ → CoreZ r → ℝ × ℝ) (k : ℕ) : ℕ :=
  coreQueryCost (coreRun s hub x k) + (coreRetire s (x k) (coreRun s hub x k)).2 + 1
    + (coreWave (x (k + 1)) (coreChg x k) (coreRetire s (x k) (coreRun s hub x k)).1).2

/-- Total monitor work for `K` terminal updates: build (hub, `r` top vertices with two
incidences each, the winner), the `K` steps, the final query, and the disposal of what is
still held. -/
def coreWork (s : Bool) (hub : MaxCirc (CoreZ r)) (x : ℕ → CoreZ r → ℝ × ℝ) (K : ℕ) : ℕ :=
  (hub.uctSize + 3 * r + 1) + ∑ k ∈ range K, coreStepCost s hub x k
    + coreQueryCost (coreRun s hub x K)
    + (uctOptSize (coreRun s hub x K).hub + 3 * (coreRun s hub x K).act.card)

/-- The property of an interval of a zero-reward vertex: lower endpoint `0`, upper endpoint
at most `1`. -/
def coreP (p : ℝ × ℝ) : Prop := p.1 = 0 ∧ p.2 ≤ 1

theorem coreP_join {p q : ℝ × ℝ} (hp : coreP p) (hq : coreP q) : coreP (uctJoin p q) := by
  refine ⟨?_, max_le hp.2 hq.2⟩
  show max p.1 q.1 = 0
  rw [hp.1, hq.1, max_self]

/-- What the monitors need from the sequence of terminal tables: zero-reward terminals have
lower endpoint `0` and upper endpoint at most `1`, the winning terminal has upper endpoint
`1`, and each update changes at most one terminal. -/
structure CoreTable (x : ℕ → CoreZ r → ℝ × ℝ) : Prop where
  zero : ∀ k z, coreReward r z = 0 → coreP (x k z)
  win : ∀ k, (x k (coreWinZ r)).2 = 1
  one : ∀ k, ∃ z0, ∀ z, x (k + 1) z ≠ x k z → z = z0

/-- Invariant of both monitors. -/
def CoreInv (hub : MaxCirc (CoreZ r)) (σ : CoreMon r) : Prop :=
  (∀ n, σ.hub = some n → n.shape = hub ∧ n.AllVal coreP) ∧ (∀ i, coreP (σ.top i)) ∧
    Fin.last r ∈ σ.act

variable {hub : MaxCirc (CoreZ r)} {σ : CoreMon r} {x' : CoreZ r → ℝ × ℝ}

theorem CoreMon.lo_last (σ : CoreMon r) (x : CoreZ r → ℝ × ℝ) :
    σ.lo x (Fin.last r) = (x (coreWinZ r)).1 := by
  unfold CoreMon.lo
  rw [dite_eq_right (by simp)]

theorem CoreMon.hi_last (σ : CoreMon r) (x : CoreZ r → ℝ × ℝ) :
    σ.hi x (Fin.last r) = (x (coreWinZ r)).2 := by
  unfold CoreMon.hi
  rw [dite_eq_right (by simp)]

private theorem lt_of_ne_last {a : Fin (r + 1)} (ha : a ≠ Fin.last r) : (a : ℕ) < r := by
  have h1 : (a : ℕ) ≤ r := Fin.is_le a
  have h2 : (a : ℕ) ≠ r := fun e => ha (Fin.ext (by rw [e, Fin.val_last]))
  omega

theorem CoreInv.lo_loser (h : CoreInv hub σ) (x : CoreZ r → ℝ × ℝ) {a : Fin (r + 1)}
    (ha : a ≠ Fin.last r) : σ.lo x a = 0 := by
  unfold CoreMon.lo
  rw [dite_eq_left (lt_of_ne_last ha)]
  exact (h.2.1 _).1

theorem CoreInv.hi_loser (h : CoreInv hub σ) (x : CoreZ r → ℝ × ℝ) {a : Fin (r + 1)}
    (ha : a ≠ Fin.last r) : σ.hi x a ≤ 1 := by
  unfold CoreMon.hi
  rw [dite_eq_left (lt_of_ne_last ha)]
  exact (h.2.1 _).2

/-- **Any successful stopping test recommends the winning action.** -/
theorem CoreInv.stop_leader (h : CoreInv hub σ) {x : CoreZ r → ℝ × ℝ}
    (hwin : (x (coreWinZ r)).2 = 1) {a : Fin (r + 1)} (hs : coreStops σ x a) :
    a = Fin.last r := by
  by_contra ha
  have h1 := hs.2 (Fin.last r) h.2.2 (Ne.symm ha)
  rw [σ.hi_last, hwin, h.lo_loser x ha] at h1
  linarith

/-- **The stopping test passes once the winning terminal's lower endpoint is `≥ 4/5`.** -/
theorem CoreInv.stop_of_lower (h : CoreInv hub σ) {x : CoreZ r → ℝ × ℝ}
    (h45 : 4 / 5 ≤ (x (coreWinZ r)).1) : coreStops σ x (Fin.last r) := by
  refine ⟨⟨h.2.2, fun b _ => ?_, fun b _ hbe => ?_⟩, fun b _ hne => ?_⟩
  · by_cases hb : b = Fin.last r
    · rw [hb]
    · rw [h.lo_loser x hb, σ.lo_last]
      linarith
  · by_cases hb : b = Fin.last r
    · rw [hb]
    · rw [h.lo_loser x hb, σ.lo_last] at hbe
      linarith
  · have := h.hi_loser x hne
    rw [σ.lo_last]
    linarith

theorem coreRetire_inv (s : Bool) {x : CoreZ r → ℝ × ℝ} (hwin : (x (coreWinZ r)).2 = 1)
    (h : CoreInv hub σ) : CoreInv hub (coreRetire s x σ).1 := by
  classical
  cases s
  · exact h
  · refine ⟨fun n hn => ?_, h.2.1, ?_⟩
    · have hn' : (if ∃ i : Fin r, Fin.castSucc i ∈ coreKeep x σ then σ.hub else none) = some n :=
        hn
      split_ifs at hn'
      exact h.1 n hn'
    · show Fin.last r ∈ coreKeep x σ
      unfold coreKeep
      rw [mem_filter]
      refine ⟨h.2.2, ?_⟩
      rintro ⟨a, -, hane, hlt⟩
      rw [σ.hi_last, hwin, h.lo_loser x hane] at hlt
      linarith

theorem coreHubVal_P {Q : CoreZ r → Prop} (hx : ∀ z, Q z → coreP (x' z))
    (o : Option (UctNode (CoreZ r)))
    (ho : ∀ n, o = some n → MaxCirc.AllTerm Q n.shape ∧ n.AllVal coreP) :
    coreP (coreHubVal x' o) := by
  cases o with
  | none => exact ⟨rfl, le_rfl⟩
  | some n => exact UctNode.val_of_allVal hx n (ho n rfl).1 (ho n rfl).2

theorem coreWave_inv (chg : CoreZ r → Bool)
    (hzero : ∀ z, coreReward r z = 0 → coreP (x' z))
    (hhub : MaxCirc.AllTerm (fun z => coreReward r z = 0) hub) (h : CoreInv hub σ) :
    CoreInv hub (coreWave x' chg σ).1 := by
  have hnew : ∀ n, coreHubNew x' chg σ = some n → n.shape = hub ∧ n.AllVal coreP := by
    intro n hn
    unfold coreHubNew at hn
    cases ho : σ.hub with
    | none => rw [ho] at hn; exact absurd hn (by simp)
    | some n0 =>
      rw [ho] at hn
      have e : (uctWave x' chg n0).1 = n := Option.some_inj.mp hn
      obtain ⟨hs, hv⟩ := h.1 n0 ho
      rw [← e]
      exact ⟨(uctWave_shape x' chg n0).trans hs,
        uctWave_allVal chg hzero (fun _ _ => coreP_join) n0 (by rw [hs]; exact hhub) hv⟩
  refine ⟨hnew, fun i => ?_, h.2.2⟩
  show coreP (if Fin.castSucc i ∈ σ.act ∧
      (coreHubFlag x' chg σ = true ∨ chg (corePriv r i) = true) then
    uctJoin (coreHubVal x' (coreHubNew x' chg σ)) (x' (corePriv r i)) else σ.top i)
  split_ifs
  · exact coreP_join (coreHubVal_P hzero _ (fun n hn => by
      obtain ⟨hs, hv⟩ := hnew n hn
      exact ⟨by rw [hs]; exact hhub, hv⟩)) (hzero _ rfl)
  · exact h.2.1 i

theorem coreRun_inv (s : Bool) {x : ℕ → CoreZ r → ℝ × ℝ} (hx : CoreTable x)
    (hhub : MaxCirc.AllTerm (fun z => coreReward r z = 0) hub) :
    ∀ k, CoreInv hub (coreRun s hub x k)
  | 0 => by
      have hv := uctBuild_allVal (P := coreP) (hx.zero 0) (fun _ _ => coreP_join) hub hhub
      refine ⟨fun n hn => ?_, fun i => ?_, mem_univ _⟩
      · have e : uctBuild (x 0) hub = n := Option.some_inj.mp hn
        rw [← e]
        exact ⟨uctBuild_shape _ _, hv⟩
      · exact coreP_join (UctNode.val_of_allVal (hx.zero 0) _
          (by rw [uctBuild_shape]; exact hhub) hv) (hx.zero 0 _ rfl)
  | k + 1 => coreWave_inv _ (hx.zero (k + 1)) hhub
      (coreRetire_inv s (hx.win k) (coreRun_inv s hx hhub k))

/-! #### Work of the two monitors -/

theorem coreRetire_cost_le (s : Bool) (x : CoreZ r → ℝ × ℝ) (σ : CoreMon r) :
    (coreRetire s x σ).2 + uctOptSize (coreRetire s x σ).1.hub
      ≤ 6 * (r + 1) + uctOptSize σ.hub := by
  classical
  cases s
  · show 0 + uctOptSize σ.hub ≤ _
    omega
  · have h1 : σ.act.card ≤ r + 1 := by
      have := Finset.card_le_univ σ.act
      rwa [Fintype.card_fin] at this
    have h2 : (σ.act \ coreKeep x σ).card ≤ r + 1 :=
      (Finset.card_le_card Finset.sdiff_subset).trans h1
    show 3 * σ.act.card + 3 * (σ.act \ coreKeep x σ).card
        + (if ∃ i : Fin r, Fin.castSucc i ∈ coreKeep x σ then 0 else uctOptSize σ.hub)
        + uctOptSize (if ∃ i : Fin r, Fin.castSucc i ∈ coreKeep x σ then σ.hub else none)
      ≤ 6 * (r + 1) + uctOptSize σ.hub
    split_ifs
    · omega
    · show _ + _ + uctOptSize σ.hub + 0 ≤ _
      omega

theorem coreWave_optSize (x' : CoreZ r → ℝ × ℝ) (chg : CoreZ r → Bool) (σ : CoreMon r) :
    uctOptSize (coreWave x' chg σ).1.hub = uctOptSize σ.hub := by
  show uctOptSize (σ.hub.map (fun n => (uctWave x' chg n).1)) = uctOptSize σ.hub
  cases σ.hub with
  | none => rfl
  | some n =>
    show ((uctWave x' chg n).1).shape.uctSize = n.shape.uctSize
    rw [uctWave_shape]

/-- **Work of one wave on the DAG**: at most `2 · height` inside the hub (one changed leaf,
one path) plus `2 r + 2` for the deliveries to the top vertices. -/
theorem coreWave_cost_le {chg : CoreZ r → Bool} (h : CoreInv hub σ)
    (hone : ∃ z0, ∀ z, chg z = true → z = z0)
    (hocc : ∀ z, hub.uctOcc (fun w => decide (w = z)) ≤ 1) :
    (coreWave x' chg σ).2 ≤ 2 * hub.uctHeight + 2 * r + 2 := by
  classical
  obtain ⟨z0, hz0⟩ := hone
  have hhubcost : coreHubCost x' chg σ ≤ 2 * hub.uctHeight := by
    unfold coreHubCost
    cases ho : σ.hub with
    | none => exact Nat.zero_le _
    | some n =>
      obtain ⟨hs, -⟩ := h.1 n ho
      have h1 := (uctWave_cost_le x' chg n).1
      rw [hs] at h1
      have h2 : hub.uctOcc chg ≤ 1 :=
        (MaxCirc.uctOcc_mono (q := fun w => decide (w = z0))
          (fun z hz => decide_eq_true (hz0 z hz)) hub).trans (hocc z0)
      have h3 : hub.uctOcc chg * hub.uctHeight ≤ 1 * hub.uctHeight :=
        Nat.mul_le_mul_right _ h2
      show (uctWave x' chg n).2.2 ≤ 2 * hub.uctHeight
      omega
  have hpriv : ∑ i : Fin r, (if chg (corePriv r i) = true then 2 else 0) ≤ 2 := by
    by_cases hex : ∃ i0 : Fin r, corePriv r i0 = z0
    · obtain ⟨i0, hi0⟩ := hex
      calc ∑ i : Fin r, (if chg (corePriv r i) = true then 2 else 0)
          ≤ ∑ i : Fin r, (if i = i0 then 2 else 0) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            by_cases hc : chg (corePriv r i) = true
            · have e : corePriv r i = corePriv r i0 := (hz0 _ hc).trans hi0.symm
              have e' : i = i0 := Sum.inl_injective (Sum.inr_injective e)
              rw [ite_eq_left hc, ite_eq_left e']
            · rw [ite_eq_right hc]
              exact Nat.zero_le _
        _ = 2 := by simp
    · refine le_trans (le_of_eq (Finset.sum_eq_zero (fun i _ => ?_))) (Nat.zero_le 2)
      have : ¬ chg (corePriv r i) = true := fun hc => hex ⟨i, hz0 _ hc⟩
      rw [ite_eq_right this]
  have htop : ∑ i : Fin r, (if Fin.castSucc i ∈ σ.act then
        (if coreHubFlag x' chg σ = true then 2 else 0)
          + (if chg (corePriv r i) = true then 2 else 0) else 0)
      ≤ ∑ i : Fin r, (2 + (if chg (corePriv r i) = true then 2 else 0)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    split_ifs <;> omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at htop
  show coreHubCost x' chg σ + _ ≤ _
  omega

/-- **Work of both monitors on the common-core DAG.**  For `K` terminal updates,
`W ≤ 2 |hub| + 8 r + 6 + K (2 · height(hub) + 10 r + 11)`. -/
theorem coreWork_le (s : Bool) {x : ℕ → CoreZ r → ℝ × ℝ} (hx : CoreTable x)
    (hhub : MaxCirc.AllTerm (fun z => coreReward r z = 0) hub)
    (hocc : ∀ z, hub.uctOcc (fun w => decide (w = z)) ≤ 1) (K : ℕ) :
    coreWork s hub x K ≤ 2 * hub.uctSize + 8 * r + 6 + K * (2 * hub.uctHeight + 10 * r + 11) := by
  classical
  have hcard : ∀ k, (coreRun s hub x k).act.card ≤ r + 1 := fun k => by
    have := Finset.card_le_univ (coreRun s hub x k).act
    rwa [Fintype.card_fin] at this
  have hstep : ∀ k, coreStepCost s hub x k + uctOptSize (coreRun s hub x (k + 1)).hub
      ≤ (2 * hub.uctHeight + 10 * r + 11) + uctOptSize (coreRun s hub x k).hub := by
    intro k
    have hinv := coreRun_inv s hx hhub k
    have h1 := coreRetire_cost_le s (x k) (coreRun s hub x k)
    have h2 := coreWave_cost_le (x' := x (k + 1)) (chg := coreChg x k)
      (coreRetire_inv s (hx.win k) hinv)
      (by
        obtain ⟨z0, hz0⟩ := hx.one k
        exact ⟨z0, fun z hz => hz0 z (of_decide_eq_true hz)⟩) hocc
    have h3 := coreWave_optSize (x (k + 1)) (coreChg x k)
      (coreRetire s (x k) (coreRun s hub x k)).1
    have h4 := hcard k
    have e : (coreRun s hub x (k + 1)).hub
        = (coreWave (x (k + 1)) (coreChg x k) (coreRetire s (x k) (coreRun s hub x k)).1).1.hub :=
      rfl
    rw [e, h3]
    unfold coreStepCost coreQueryCost
    omega
  have hsum : ∀ K, ∑ k ∈ range K, coreStepCost s hub x k + uctOptSize (coreRun s hub x K).hub
      ≤ K * (2 * hub.uctHeight + 10 * r + 11) + hub.uctSize := by
    intro K
    induction K with
    | zero =>
      show 0 + (uctBuild (x 0) hub).shape.uctSize ≤ _
      rw [uctBuild_shape]
      omega
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have := hstep K
      have e : (K + 1) * (2 * hub.uctHeight + 10 * r + 11)
          = K * (2 * hub.uctHeight + 10 * r + 11) + (2 * hub.uctHeight + 10 * r + 11) := by ring
      omega
  have h1 := hsum K
  have h2 := hcard K
  unfold coreWork coreQueryCost
  omega

end CoreMonitor

/-! ### Existence of UCT runs -/

section Exists

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- UCT runs exist for every history-dependent empirical-mean functional `Qf` (the mean
before visit `t` may depend on the selections before `t`): the models of this file are not
vacuous. -/
theorem exists_uctRun [Nonempty ι] (c : ℝ) (Qf : (ℕ → ι) → ℕ → ι → ℝ)
    (hQ : ∀ (sel sel' : ℕ → ι) (t : ℕ), (∀ s, s < t → sel s = sel' s) → Qf sel t = Qf sel' t) :
    ∃ sel, UCTRun c (Qf sel) sel := by
  classical
  obtain ⟨d⟩ : Nonempty ι := inferInstance
  let e := Fintype.equivFin ι
  let selOf : List ι → ℕ → ι := fun l s => l.getD s d
  have hex : ∀ l : List ι, ∃ i, ∀ j,
      uctIndex c (Qf (selOf l) l.length j) l.length (uctCount (selOf l) l.length j)
        ≤ uctIndex c (Qf (selOf l) l.length i) l.length (uctCount (selOf l) l.length i) :=
    fun l => Finite.exists_max _
  choose am ham using hex
  let F : List ι → ι := fun l =>
    if h : l.length < Fintype.card ι then e.symm ⟨l.length, h⟩ else am l
  let hist : ℕ → List ι := fun t => Nat.rec [] (fun _ l => l ++ [F l]) t
  have hist_succ : ∀ t, hist (t + 1) = hist t ++ [F (hist t)] := fun _ => rfl
  have hlen : ∀ t, (hist t).length = t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hist_succ, List.length_append, ih]; rfl
  have hget : ∀ t s, s < t → (hist t).getD s d = F (hist s) := by
    intro t
    induction t with
    | zero => intro s hs; exact absurd hs (Nat.not_lt_zero s)
    | succ t ih =>
      intro s hs
      rw [hist_succ]
      rcases Nat.lt_or_ge s t with h1 | h1
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h1)]
        exact ih s h1
      · have hst : s = t := by omega
        rw [List.getD_append_right _ _ _ _ (by rw [hlen]; exact h1), hlen, hst]
        simp
  refine ⟨fun t => F (hist t), ?_, ?_⟩
  · intro i
    have hsel : ∀ s (hs : s < Fintype.card ι), F (hist s) = e.symm ⟨s, hs⟩ := by
      intro s hs
      show (if h : (hist s).length < Fintype.card ι then e.symm ⟨(hist s).length, h⟩
        else am (hist s)) = _
      rw [dite_eq_left (by rw [hlen]; exact hs)]
      congr 2
      exact hlen s
    have hset : (range (Fintype.card ι)).filter (fun s => F (hist s) = i) = {((e i : Fin _) : ℕ)} := by
      ext s
      rw [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hs, hi⟩
        rw [hsel s hs] at hi
        have : (⟨s, hs⟩ : Fin (Fintype.card ι)) = e i := by
          rw [← hi, Equiv.apply_symm_apply]
        exact congrArg Fin.val this
      · intro hs
        have hlt : s < Fintype.card ι := by rw [hs]; exact (e i).isLt
        refine ⟨hlt, ?_⟩
        rw [hsel s hlt]
        have : (⟨s, hlt⟩ : Fin (Fintype.card ι)) = e i := Fin.ext hs
        rw [this, Equiv.symm_apply_apply]
    show ((range (Fintype.card ι)).filter (fun s => F (hist s) = i)).card = 1
    rw [hset, card_singleton]
  · intro t ht j
    have hagree : ∀ s, s < t → selOf (hist t) s = F (hist s) := fun s hs => hget t s hs
    have hcnt : ∀ a, uctCount (selOf (hist t)) t a = uctCount (fun t => F (hist t)) t a := by
      intro a
      unfold uctCount
      congr 1
      refine Finset.filter_congr (fun s hs => ?_)
      rw [hagree s (mem_range.mp hs)]
    have hQe : Qf (selOf (hist t)) t = Qf (fun t => F (hist t)) t := hQ _ _ t hagree
    have hF : F (hist t) = am (hist t) := by
      show (if h : (hist t).length < Fintype.card ι then e.symm ⟨(hist t).length, h⟩
        else am (hist t)) = _
      rw [dite_eq_right (by rw [hlen]; omega)]
    have := ham (hist t) j
    rw [hlen, hcnt, hcnt, hQe] at this
    show uctIndex c (Qf (fun t => F (hist t)) t j) t (uctCount (fun t => F (hist t)) t j)
      ≤ uctIndex c (Qf (fun t => F (hist t)) t (F (hist t))) t
        (uctCount (fun t => F (hist t)) t (F (hist t)))
    rw [hF]
    exact this

end Exists

/-! ### Terminal table, stopping time and total work on the common-core family -/

section CoreFinal

variable {r : ℕ} [NeZero r]

/-- Searches on the common-core DAG exist for every path rule. -/
theorem exists_coreSearch (r : ℕ) [NeZero r] (rule : ℕ → ℕ → Bool) :
    ∃ sel zt, CoreSearch r rule sel zt := by
  let ztOf : (ℕ → Fin (r + 1)) → ℕ → CoreZ r :=
    fun sel s => ((coreAct r (sel s)).uctWalk (rule s) 0).1
  obtain ⟨sel, hsel⟩ := exists_uctRun (ι := Fin (r + 1)) 2
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

/-- The terminal observation table after `t` rollouts: `[0, 1]` for an unsampled terminal,
otherwise the clipped interval of radius `β(count)` around the (deterministic) empirical
mean. -/
def coreTab (r : ℕ) (β : ℕ → ℝ) (zt : ℕ → CoreZ r) (t : ℕ) (z : CoreZ r) : ℝ × ℝ :=
  if uctCount zt t z = 0 then (0, 1)
  else (max 0 (coreReward r z - β (uctCount zt t z)), min 1 (coreReward r z + β (uctCount zt t z)))

/-- The table seen by the monitors at their step `k`, after the `r + 1` forced rollouts and
`k` further ones. -/
def coreBox (r : ℕ) (β : ℕ → ℝ) (zt : ℕ → CoreZ r) (k : ℕ) : CoreZ r → ℝ × ℝ :=
  coreTab r β zt (r + 1 + k)

omit [NeZero r] in
theorem coreBox_table {β : ℕ → ℝ} (hβ : ∀ n, 0 ≤ β n) (zt : ℕ → CoreZ r) :
    CoreTable (coreBox r β zt) where
  zero := by
    intro k z hz
    unfold coreBox coreTab
    split_ifs
    · exact ⟨rfl, le_rfl⟩
    · refine ⟨?_, min_le_left _ _⟩
      show max 0 (coreReward r z - β _) = 0
      rw [hz]
      exact max_eq_left (by linarith [hβ (uctCount zt (r + 1 + k) z)])
  win := by
    intro k
    unfold coreBox coreTab
    split_ifs
    · rfl
    · show min 1 (coreReward r (coreWinZ r) + β _) = 1
      have h1 : coreReward r (coreWinZ r) = 1 := rfl
      rw [h1]
      exact min_eq_left (by linarith [hβ (uctCount zt (r + 1 + k) (coreWinZ r))])
  one := by
    intro k
    refine ⟨zt (r + 1 + k), fun z hne => ?_⟩
    by_contra hz
    apply hne
    have hc : uctCount zt (r + 1 + (k + 1)) z = uctCount zt (r + 1 + k) z := by
      show uctCount zt (r + 1 + k + 1) z = _
      rw [uctCount_succ, ite_eq_right (fun e => hz e.symm), add_zero]
    unfold coreBox coreTab
    rw [hc]

variable {rule : ℕ → ℕ → Bool} {sel : ℕ → Fin (r + 1)} {zt : ℕ → CoreZ r}

/-- The winning terminal is observed exactly when the winning action is selected. -/
theorem CoreSearch.win_count (h : CoreSearch r rule sel zt) (t : ℕ) :
    uctCount zt t (coreWinZ r) = uctCount sel t (Fin.last r) := by
  unfold uctCount
  congr 1
  refine Finset.filter_congr (fun s _ => ?_)
  constructor
  · intro hz
    have hre := h.reward_eq s
    rw [hz] at hre
    by_contra hne
    have hlt := lt_of_ne_last hne
    have h1 : coreReward r (coreWinZ r) = 1 := rfl
    rw [h1] at hre
    simp [coreMu, hlt] at hre
  · intro hs
    have hact : coreAct r (Fin.last r) = .term (coreWinZ r) := by
      unfold coreAct
      rw [dite_eq_right (by simp)]
    rw [h.reach, hs, hact]
    rfl

/-- **`thm:ta-core`, stopping.**  If the radius is at most `1/5` from count `k0` on and
`T ≥ k0 + r (1 + 4 log (1 + T))`, then after `T` rollouts the stopping test of either
monitor passes and recommends the winning action. -/
theorem core_stops_by (h : CoreSearch r rule sel zt) {β : ℕ → ℝ} (hβ0 : ∀ n, 0 ≤ β n) {k0 : ℕ}
    (hβ : ∀ n, k0 ≤ n → β n ≤ 1 / 5) (s : Bool) {T : ℕ} (hT : r + 1 ≤ T)
    (hTk : (k0 : ℝ) + r * (1 + 4 * Real.log (1 + T)) ≤ T) :
    coreStops (coreRun s (coreHub r) (coreBox r β zt) (T - (r + 1)))
      (coreBox r β zt (T - (r + 1))) (Fin.last r) := by
  have hinv := coreRun_inv s (coreBox_table hβ0 zt) (coreHub_zero r) (T - (r + 1))
  apply hinv.stop_of_lower
  have e : r + 1 + (T - (r + 1)) = T := by omega
  have hcnt := core_win_count_ge h.run hT
  have hk : k0 ≤ uctCount sel T (Fin.last r) := by
    have : (k0 : ℝ) ≤ uctCount sel T (Fin.last r) := by linarith
    exact_mod_cast this
  have hpos : 1 ≤ uctCount sel T (Fin.last r) :=
    h.uct.one_le _ (by rw [Fintype.card_fin]; exact hT)
  unfold coreBox coreTab
  rw [e, h.win_count, ite_eq_right (by omega)]
  show 4 / 5 ≤ max 0 (coreReward r (coreWinZ r) - β _)
  have h1 : coreReward r (coreWinZ r) = 1 := rfl
  rw [h1]
  exact le_max_of_le_right (by linarith [hβ _ hk])

/-- The Hoeffding radius `β(n) = √(log (4 M n² / δ) / (2n))` with `M = r² + r + 1`, the
number of terminals of the common-core DAG (`card_coreZ`). -/
def coreRadius (r : ℕ) (δ : ℝ) (n : ℕ) : ℝ := hoeffdingWidth ((r ^ 2 + r + 1 : ℕ) : ℝ) δ n / 2

/-- A count from which the radius is at most `1/5`: `k₀ = ⌈200 log (200 M / δ)⌉`. -/
def coreK0 (r : ℕ) (δ : ℝ) : ℕ := ⌈200 * Real.log (200 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / δ)⌉₊

theorem coreRadius_nonneg (r : ℕ) (δ : ℝ) (n : ℕ) : 0 ≤ coreRadius r δ n := by
  unfold coreRadius hoeffdingWidth
  have := Real.sqrt_nonneg (Real.log (4 * ((r ^ 2 + r + 1 : ℕ) : ℝ) * (n : ℝ) ^ 2 / δ) / (2 * n))
  linarith

theorem coreRadius_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {r : ℕ} (hr : 1 ≤ r) {n : ℕ}
    (hn : coreK0 r δ ≤ n) : coreRadius r δ n ≤ 1 / 5 := by
  have hM : (2 : ℝ) ≤ ((r ^ 2 + r + 1 : ℕ) : ℝ) := by
    have : 2 ≤ r ^ 2 + r + 1 := by nlinarith
    exact_mod_cast this
  have e1 : (32 : ℝ) / (2 / 5) ^ 2 = 200 := by norm_num
  have e2 : 32 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / (δ * (2 / 5) ^ 2)
      = 200 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / δ := by
    field_simp
    ring
  have hx : 32 / (2 / 5 : ℝ) ^ 2 * Real.log (32 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / (δ * (2 / 5) ^ 2))
      ≤ (n : ℝ) := by
    rw [e1, e2]
    have hn' : ((coreK0 r δ : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr hn
    exact le_trans (Nat.le_ceil _) hn'
  have := width_inversion hM hδ0 hδ1 (by norm_num : (0 : ℝ) < 2 / 5) (by norm_num) hx
  unfold coreRadius
  linarith

/-- **`thm:ta-core`, `τ = O(r log r)`.**  There is a constant `A` depending only on `δ`
such that for every `r ≥ 2` some `T ≤ A r log r` satisfies the hypothesis of
`core_stops_by` for the Hoeffding radius. -/
theorem core_horizon_exists {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℕ, 2 ≤ r → ∃ T : ℕ, r + 1 ≤ T ∧ (T : ℝ) ≤ A * r * Real.log r ∧
      (coreK0 r δ : ℝ) + r * (1 + 4 * Real.log (1 + T)) ≤ T := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 200 * Real.log (600 / δ) + 1 := ⟨_, rfl⟩
  have hlog600 : 0 ≤ Real.log (600 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0]
    linarith)
  have hD0 : 1 ≤ D := by rw [hD]; linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * D + 400 := ⟨_, rfl⟩
  have hA400 : 402 ≤ A := by rw [hA]; linarith
  refine ⟨A + 1, by linarith, ?_⟩
  intro r hr
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log r := ⟨_, rfl⟩
  rw [← hℓ]
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hℓ69 : (0.69 : ℝ) ≤ ℓ := by
    have : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hrR
    rw [hℓ]
    linarith
  have hℓr : ℓ ≤ r := by
    have := Real.log_le_sub_one_of_pos hr0
    rw [hℓ]
    linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = r * ℓ := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hp]; nlinarith
  have hAp0 : 0 ≤ A * p := by nlinarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = ⌈A * p⌉₊ := ⟨_, rfl⟩
  have hT1 : A * p ≤ T := by rw [hTdef]; exact Nat.le_ceil _
  have hT2 : (T : ℝ) < A * p + 1 := by rw [hTdef]; exact Nat.ceil_lt_add_one hAp0
  -- the count threshold
  have hMle : ((r ^ 2 + r + 1 : ℕ) : ℝ) ≤ 3 * (r : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hMpos : (0 : ℝ) < ((r ^ 2 + r + 1 : ℕ) : ℝ) := by positivity
  have hk0 : (coreK0 r δ : ℝ) ≤ D + 400 * ℓ := by
    have harg : 1 ≤ 200 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / δ := by
      rw [le_div_iff₀ hδ0]
      have : (1 : ℝ) ≤ ((r ^ 2 + r + 1 : ℕ) : ℝ) := by
        have : 1 ≤ r ^ 2 + r + 1 := by omega
        exact_mod_cast this
      linarith
    have hnn : 0 ≤ 200 * Real.log (200 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / δ) :=
      mul_nonneg (by norm_num) (Real.log_nonneg harg)
    have h1 : (coreK0 r δ : ℝ) < 200 * Real.log (200 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / δ) + 1 :=
      Nat.ceil_lt_add_one hnn
    have h2 : Real.log (200 * ((r ^ 2 + r + 1 : ℕ) : ℝ) / δ)
        ≤ Real.log (600 / δ * (r : ℝ) ^ 2) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ0]
      linarith
    have h3 : Real.log (600 / δ * (r : ℝ) ^ 2) = Real.log (600 / δ) + 2 * ℓ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hℓ]
      push_cast
      ring
    rw [hD]
    linarith
  -- the logarithm of the horizon
  have hlogT : Real.log (1 + (T : ℝ)) ≤ A / 16 + 3 + 2 * ℓ := by
    have hpr : p ≤ (r : ℝ) ^ 2 := by rw [hp]; nlinarith
    have h1 : 1 + (T : ℝ) ≤ 2 * A * (r : ℝ) ^ 2 := by nlinarith
    have h2 : Real.log (1 + (T : ℝ)) ≤ Real.log (2 * A * (r : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (2 * A * (r : ℝ) ^ 2) = Real.log (A / 16) + Real.log 32 + 2 * ℓ := by
      rw [show 2 * A * (r : ℝ) ^ 2 = A / 16 * 32 * (r : ℝ) ^ 2 by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by norm_num),
        Real.log_pow, hℓ]
      push_cast
      ring
    have h4 : Real.log (A / 16) ≤ A / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h5 : Real.log 32 ≤ 4 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      push_cast
      linarith
    linarith
  have hmul : (r : ℝ) * (1 + 4 * Real.log (1 + (T : ℝ)))
      ≤ r * (1 + 4 * (A / 16 + 3 + 2 * ℓ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hr0.le
  have q1 : D ≤ D * p := le_mul_of_one_le_right (by linarith) hp1
  have q2 : 2 * ℓ ≤ p := by rw [hp]; nlinarith
  have q3 : 13 * (r : ℝ) ≤ 19 * p := by rw [hp]; nlinarith
  have q4 : 5 * (A * r) ≤ 8 * (A * p) := by
    rw [hp]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ A) hr0.le)
      (by linarith : (0 : ℝ) ≤ 8 * ℓ - 5)]
  have q5 : 0 ≤ (6 / 10 * A - D - 227) * p :=
    mul_nonneg (by rw [hA]; linarith) (by linarith)
  have hfinal : (coreK0 r δ : ℝ) + r * (1 + 4 * Real.log (1 + (T : ℝ))) ≤ A * p := by
    have e : (r : ℝ) * (1 + 4 * (A / 16 + 3 + 2 * ℓ)) = 13 * r + A * r / 4 + 8 * p := by
      rw [hp]
      ring
    nlinarith
  refine ⟨T, ?_, ?_, by linarith⟩
  · have : ((r + 1 : ℕ) : ℝ) ≤ T := by
      push_cast
      nlinarith
    exact_mod_cast this
  · have : (A + 1) * r * ℓ = A * p + p := by rw [hp]; ring
    linarith

/-- Work of one rollout through root action `a`: `r + 1` root index evaluations, one step
down and one step back up per traversed edge, and the root and terminal table updates. -/
def coreRollout (r : ℕ) [NeZero r] (rule : ℕ → ℕ → Bool) (u : ℕ) (a : Fin (r + 1)) : ℕ :=
  (r + 1) + 2 * ((coreAct r a).uctWalk (rule u) 0).2 + 2

/-- Total work of a run of `r + 1 + K` rollouts with the selective (`s = true`) or the
eager (`s = false`) monitor: reading and disposing of the graph, all rollouts, and the
monitor work. -/
def coreTotalWork (s : Bool) (r : ℕ) [NeZero r] (β : ℕ → ℝ) (rule : ℕ → ℕ → Bool)
    (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r) (K : ℕ) : ℕ :=
  2 * ((coreHub r).uctSize + 3 * r + 1) + ∑ u ∈ range (r + 1 + K), coreRollout r rule u (sel u)
    + coreWork s (coreHub r) (coreBox r β zt) K

theorem coreClog_le (r : ℕ) : Nat.clog 2 (r ^ 2) ≤ 2 * r := by
  refine Nat.clog_le_of_le_pow ?_
  have h1 : r ≤ 2 ^ r := Nat.lt_two_pow_self.le
  calc r ^ 2 ≤ (2 ^ r) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ (2 * r) := by rw [← pow_mul, mul_comm]

theorem coreHub_height_le (r : ℕ) [NeZero r] : (coreHub r).uctHeight ≤ 2 * r :=
  (coreHub_height r).trans (coreClog_le r)

/-- **Total work on the common-core DAG, in natural numbers**:
`W ≤ 13 r² + 24 r + 11 + K (19 r + 16)` for `r + 1 + K` rollouts, with either monitor. -/
theorem coreTotalWork_le (s : Bool) {β : ℕ → ℝ} (hβ : ∀ n, 0 ≤ β n) (rule : ℕ → ℕ → Bool)
    (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r) (K : ℕ) :
    coreTotalWork s r β rule sel zt K ≤ 13 * r ^ 2 + 24 * r + 11 + K * (19 * r + 16) := by
  have hsize := coreHub_size r
  have hh := coreHub_height_le r
  have hroll : ∀ u a, coreRollout r rule u a ≤ 5 * r + 5 := by
    intro u a
    have h1 := (MaxCirc.uctWalk_snd_le (rule u) (coreAct r a) 0).trans (coreAct_height r a)
    have h2 := coreClog_le r
    unfold coreRollout
    omega
  have hsum : ∑ u ∈ range (r + 1 + K), coreRollout r rule u (sel u)
      ≤ (r + 1 + K) * (5 * r + 5) := by
    have : ∑ u ∈ range (r + 1 + K), coreRollout r rule u (sel u)
        ≤ ∑ _u ∈ range (r + 1 + K), (5 * r + 5) :=
      Finset.sum_le_sum (fun u _ => hroll u (sel u))
    rwa [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  have hw := coreWork_le s (coreBox_table hβ zt) (coreHub_zero r) (coreHub_occ r) K
  have hK : K * (2 * (coreHub r).uctHeight + 10 * r + 11) ≤ K * (14 * r + 11) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold coreTotalWork
  have e1 : (r + 1 + K) * (5 * r + 5) = 5 * r ^ 2 + 10 * r + 5 + K * (5 * r + 5) := by ring
  have e2 : K * (19 * r + 16) = K * (14 * r + 11) + K * (5 * r + 5) := by ring
  omega

/-- **Theorem `thm:ta-core` (Wide Common-Core Support Compilation Cost).**  Fix
`δ ∈ (0, 1)`.  There are constants `A, B` such that for every `r ≥ 2`, every UCT search
(`c = 2`, any tie-breaking, any path rule below the root) on the common-core DAG with
`r + 1` root actions and the Hoeffding boxes for its `r² + r + 1` terminals, and for the
selective as well as the eager monitor:

* the first rollout count `r + 1 + τ` at which the stopping test at `ε = 1/5` passes
  exists, is at most `A r log r`, and the recommendation at any successful test is the
  winning action;
* the total work (graph, rollouts, monitor) up to that point is at most `B r² log r`, in
  particular `O(r² log² r)`;
* materializing the flat supports of the losing actions writes at least `r³` entries.

The dyadic-cover clause of the theorem is not covered. -/
theorem ta_core {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r),
      CoreSearch r rule sel zt → ∀ s : Bool,
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
  have hstopT := core_stops_by h hβ0 (fun n hn => coreRadius_le hδ0 hδ1 (by omega) hn) s hT1 hT3
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

end CoreFinal

/-! ### The dominated funnel under local UCT (`thm:onpolicy-uct`): root process -/

section Funnel

/-- The root of the dominated-funnel search under local UCT with `c = 1`
(`thm:selective-separation`): the optimal direct action `b = 0` returns `4/5`, the
near-optimal rival `a' = 1` returns `4/5 - g`, and the funnel `C = 2` has an empirical mean
in `[0, 1/5]` at all times (its exits return `0.15` and `0.20`; the mean depends on the
recursive choices below `C`, which are left arbitrary). -/
structure FunnelRoot (g : ℝ) (Q : ℕ → Fin 3 → ℝ) (sel : ℕ → Fin 3) : Prop where
  uct : UCTRun 1 Q sel
  qb : ∀ t, Q t 0 = 4 / 5
  qa : ∀ t, Q t 1 = 4 / 5 - g
  qC0 : ∀ t, 0 ≤ Q t 2
  qC1 : ∀ t, Q t 2 ≤ 1 / 5

variable {g : ℝ} {Q : ℕ → Fin 3 → ℝ} {sel : ℕ → Fin 3}

private theorem funnel_Q_bounds (h : FunnelRoot g Q sel) (hg0 : 0 < g) (hg : g ≤ 4 / 5) :
    (∀ t i, 0 ≤ Q t i) ∧ (∀ t i, Q t i ≤ 4 / 5) := by
  constructor
  · intro t i
    fin_cases i
    · show 0 ≤ Q t 0
      rw [h.qb]; norm_num
    · show 0 ≤ Q t 1
      rw [h.qa]; linarith
    · exact h.qC0 t
  · intro t i
    fin_cases i
    · show Q t 0 ≤ 4 / 5
      rw [h.qb]
    · show Q t 1 ≤ 4 / 5
      rw [h.qa]; linarith
    · show Q t 2 ≤ 4 / 5
      linarith [h.qC1 t]

/-- **Steps 1-3 of the proof of `thm:selective-separation`: root counts on the funnel.**
For all `t ≥ 3`:

* `N_C(t) ≤ max {1, 1 + log (1 + t) / (3/5)²}` (Step 2), uniformly in `g` and in the size
  of the funnel;
* `N_{a'}(t) ≤ max {1, 1 + log (1 + t) / g²}` (Step 3);
* if `t ≥ 6` and `3 (log (1 + t) + 1) < t - ⌊t/2⌋`, then `log (1 + ⌊t/2⌋) < 4 N_C(t)`
  (Step 1: `N_C = Θ(log t)`);
* if `t ≥ 6` and `3 (log (1 + t) / g² + 1) < t - ⌊t/2⌋`, then
  `log (1 + ⌊t/2⌋) < 4 g² N_{a'}(t)` (the near-rival estimate of Step 3). -/
theorem funnel_counts (h : FunnelRoot g Q sel) (hg0 : 0 < g) (hg : g ≤ 4 / 5) {t : ℕ}
    (ht : 3 ≤ t) :
    (uctCount sel t 2 : ℝ) ≤ max 1 (1 + Real.log (1 + t) / (3 / 5) ^ 2) ∧
    (uctCount sel t 1 : ℝ) ≤ max 1 (1 + Real.log (1 + t) / g ^ 2) ∧
    (6 ≤ t → 3 * (Real.log (1 + t) + 1) < (t : ℝ) - (t / 2 : ℕ) →
      Real.log (1 + (t / 2 : ℕ)) < 4 * uctCount sel t 2) ∧
    (6 ≤ t → 3 * (Real.log (1 + t) / g ^ 2 + 1) < (t : ℝ) - (t / 2 : ℕ) →
      Real.log (1 + (t / 2 : ℕ)) < 4 * g ^ 2 * uctCount sel t 1) := by
  have hcard : Fintype.card (Fin 3) ≤ t := by rw [Fintype.card_fin]; exact ht
  obtain ⟨hQ0, hQ45⟩ := funnel_Q_bounds h hg0 hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h.uct.count_le (by norm_num) (i := 2) (star := 0) (u0 := 1 / 5) (b := 4 / 5)
      (by norm_num) h.qC1 (fun t => le_of_eq (h.qb t).symm) hcard
    refine this.trans (le_of_eq ?_)
    norm_num
  · have := h.uct.count_le (by norm_num) (i := 1) (star := 0) (u0 := 4 / 5 - g) (b := 4 / 5)
      (by linarith) (fun t => le_of_eq (h.qa t)) (fun t => le_of_eq (h.qb t).symm) hcard
    refine this.trans (le_of_eq ?_)
    rw [one_pow, one_mul, show (4 / 5 : ℝ) - (4 / 5 - g) = g by ring]
  · intro ht6 hwin
    have := h.uct.fairness one_pos hQ0 (fun t i => (hQ45 t i).trans (by norm_num))
      (t := t) (by rw [Fintype.card_fin]; omega)
      (by rw [Fintype.card_fin, one_pow, one_mul]; exact_mod_cast hwin) 2
    rwa [one_pow, one_mul] at this
  · intro ht6 hwin
    have := h.uct.window_lower one_pos (B := 4 / 5) (γ := g) (η := g) hg0 hg0.le hQ45
      (e0 := 1) (fun t => le_of_eq (h.qa t).symm) (t := t)
      (by rw [Fintype.card_fin]; omega)
      (by rw [Fintype.card_fin, one_pow, one_mul]; exact_mod_cast hwin)
    rw [one_pow, one_mul] at this
    linarith [show (g + g) ^ 2 * (uctCount sel t 1 : ℝ) = 4 * g ^ 2 * uctCount sel t 1 by ring]

private theorem uct_exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

/-- A count `k ≥ 1` at which the Hoeffding radius for `M ≥ 2` terminals is at most `3g/2`
satisfies `k g² > 4/9`. -/
theorem radius_count_lower {M δ g : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {k : ℕ}
    (hk : 1 ≤ k) (hβ : hoeffdingWidth M δ k / 2 ≤ 3 * g / 2) : 4 / 9 < k * g ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hg0 : 0 ≤ g := by
    unfold hoeffdingWidth at hβ
    have := Real.sqrt_nonneg (Real.log (4 * M * (k : ℝ) ^ 2 / δ) / (2 * k))
    linarith
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hX8 : 8 ≤ 4 * M * (k : ℝ) ^ 2 / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hlog2 : 2 < Real.log (4 * M * (k : ℝ) ^ 2 / δ) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact uct_exp_two_lt_eight.trans_le hX8
  unfold hoeffdingWidth at hβ
  have hβ' : Real.sqrt (Real.log (4 * M * (k : ℝ) ^ 2 / δ) / (2 * k)) ≤ 3 * g / 2 := by
    linarith
  rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)] at hβ'
  nlinarith

/-- **Step 3 of the proof of `thm:selective-separation`: `τ = Ω(g⁻²)`.**  Suppose that at
a rollout count `τ` the check `U(a') - l(b) ≤ g/2` succeeds, where the rival's upper bound
contains its mean, `U(a') ≥ 4/5 - g`, and `l(b) = max {0, 4/5 - β(n_b)}` is the clipped
Hoeffding lower endpoint of the winning terminal at its count `1 ≤ n_b ≤ τ` (any number
`M ≥ 2` of canonical terminals, `δ ≤ 1`, `g ≤ 1/2`).  Then `τ g² > 4/9`. -/
theorem funnel_horizon_lower {M δ g : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hg0 : 0 < g) (hg : g ≤ 1 / 2) {τ nb : ℕ} (hnb : 1 ≤ nb) (hnbτ : nb ≤ τ) {Ua : ℝ}
    (hU : 4 / 5 - g ≤ Ua)
    (hstop : Ua - max 0 (4 / 5 - hoeffdingWidth M δ nb / 2) ≤ g / 2) :
    4 / 9 < (τ : ℝ) * g ^ 2 := by
  have hl := funnel_check_forces_radius hU hstop
  have hβ : hoeffdingWidth M δ nb / 2 ≤ 3 * g / 2 := by
    rcases le_total (4 / 5 - hoeffdingWidth M δ nb / 2) 0 with h0 | h0
    · rw [max_eq_left h0] at hl
      linarith
    · rw [max_eq_right h0] at hl
      linarith
  have h1 := radius_count_lower hM hδ0 hδ1 hnb hβ
  have h2 : (nb : ℝ) ≤ τ := by exact_mod_cast hnbτ
  nlinarith [sq_nonneg g]

/-- **`thm:onpolicy-uct`, `τ = Ω(m^{1/8})`.**  With `g_m = (1/4) m^{-1/16}` the conclusion
of `funnel_horizon_lower` reads `τ > (64/9) m^{1/8}`. -/
theorem funnel_horizon_lower_m {M δ m : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 1 ≤ m) {τ nb : ℕ} (hnb : 1 ≤ nb) (hnbτ : nb ≤ τ) {Ua : ℝ}
    (hU : 4 / 5 - 1 / 4 * m ^ (-(1 / 16 : ℝ)) ≤ Ua)
    (hstop : Ua - max 0 (4 / 5 - hoeffdingWidth M δ nb / 2) ≤ 1 / 4 * m ^ (-(1 / 16 : ℝ)) / 2) :
    64 / 9 * m ^ (1 / 8 : ℝ) < τ := by
  have hm0 : 0 < m := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = m ^ (1 / 16 : ℝ) := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by rw [ha]; exact Real.one_le_rpow hm (by norm_num)
  have hinv : m ^ (-(1 / 16 : ℝ)) = a⁻¹ := by rw [ha, Real.rpow_neg hm0.le]
  have h8 : m ^ (1 / 8 : ℝ) = a ^ 2 := by
    rw [ha, ← Real.rpow_two, ← Real.rpow_mul hm0.le]
    norm_num
  rw [hinv] at hU hstop
  have hinv0 : 0 < a⁻¹ := by positivity
  have hinv1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  have := funnel_horizon_lower hM hδ0 hδ1 (g := 1 / 4 * a⁻¹) (by positivity) (by linarith)
    hnb hnbτ hU hstop
  rw [h8]
  have e : (τ : ℝ) * (1 / 4 * a⁻¹) ^ 2 = τ / (16 * a ^ 2) := by
    field_simp
    ring
  rw [e, lt_div_iff₀ (by positivity)] at this
  linarith

end Funnel

end

end JointRootCert
