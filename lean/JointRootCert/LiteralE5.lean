/-
Literal form of Theorem `thm:v2separation` (Root-PUCT work separation from uninformative
initialization) and Corollary `cor:v2quarter` (One explicit polynomial instance).

`MonitorWork.lean` proves the two results for monitors that are built after the three forced
observations, along a fixed open-loop trace.  This file closes the remaining literal gaps.

1. First cut time.  `ClosedLoopRun.cut`: the count `tc` of the theorem satisfies
   `U_C < max {L_A, L_B}` on the monitor's terminal table exactly at the counts `s ≥ tc`
   (so it is the first cut time and the cut persists), and `tc ≤ T` with `T` depending on
   `δ` only (`v2separation_literal`).
2. Initial box and forced observations.  The terminal table of a history (`histTab`) is
   `[0,1]` at every terminal that has not been observed; the monitors are built on that box
   before any observation (`monRun` along `histSeq`) and process the three forced
   observations as ordinary updates; the work `histWork` charges the three forced rollouts
   and the monitor steps they cause.  `boxRun_eq`, `boxWork_eq`, `histWork_free`: from count
   `3` on the monitor states are those of `MonitorWork.lean`, and the extra monitor work is
   exactly `48` (selective) resp. `21` (full) operations.
3. Controller loop.  `Ctl`, `ctlStep`, `ctlMon`, `closedLoop`: the controller reads the
   monitor's failure flag, canonical leader and stopping set after every observation and
   either halts or performs the next root-PUCT selection, rollout and observation.
   `ClosedLoopRun.coupled` (via `coupled_trajectories`): the closed loops with the selective
   and with the full monitor are equal at all times; `ClosedLoopRun.running`,
   `ClosedLoopRun.halted`: both halt after exactly `τ` observations with recommendation `A`.
4. `v2quarter_literal`: the case `α = 1/4` with the two-sided work ratio.
5. Final statements: `v2separation_literal`, `v2quarter_literal`.

Tie-breaking is a parameter `pick : Hist → Fin 3` that returns a maximiser of the root-PUCT
index on every history of length at least three (`IsPuctPick`); it may depend on the whole
history.  The three forced observations are taken in the order `A, B, C`.
-/
import JointRootCert.MonitorWork

namespace JointRootCert

namespace LiteralE5

open Finset

noncomputable section

/-! ### Generic facts about the implemented monitors -/

section Generic

variable {A Z : Type*}

/-- A wave with no changed terminal changes nothing and costs nothing. -/
theorem monWave_noop (x : Z → ℝ × ℝ) {chg : Z → Bool} (hchg : ∀ z, chg z = false) :
    ∀ n : MonNode Z, monWave x chg n = (n, false, 0)
  | .term z => by
      show (MonNode.term z, chg z, 0) = _
      rw [hchg]
  | .unary v c => by
      rw [monWave]
      simp [monWave_noop x hchg c]
  | .bin v c d => by
      rw [monWave]
      simp [monWave_noop x hchg c, monWave_noop x hchg d]

theorem monWaveAll_noop [Fintype A] (x : Z → ℝ × ℝ) {chg : Z → Bool}
    (hchg : ∀ z, chg z = false) (σ : MonState A Z) : monWaveAll x chg σ = (σ, 0) := by
  have h1 : ∀ n : MonNode Z, (monWave x chg n).1 = n := fun n => by
    rw [monWave_noop x hchg n]
  have h2 : ∀ n : MonNode Z, (monWave x chg n).2.2 = 0 := fun n => by
    rw [monWave_noop x hchg n]
  obtain ⟨act, nodes⟩ := σ
  have hn : (fun a => (nodes a).map (fun n => (monWave x chg n).1)) = nodes := by
    funext a
    cases nodes a with
    | none => rfl
    | some n => exact congrArg some (h1 n)
  have hc : ∑ a, (nodes a).elim 0 (fun n => (monWave x chg n).2.2) = 0 := by
    refine Finset.sum_eq_zero (fun a _ => ?_)
    cases nodes a with
    | none => rfl
    | some n => exact h2 n
  show ((⟨act, fun a => (nodes a).map (fun n => (monWave x chg n).1)⟩ : MonState A Z),
      ∑ a, (nodes a).elim 0 (fun n => (monWave x chg n).2.2)) = _
  rw [hn, hc]

theorem monRetire_noop [Fintype A] [DecidableEq A] (s : Bool) (x : Z → ℝ × ℝ)
    (σ : MonState A Z) (hkeep : monKeep x σ = univ) (hact : σ.act = univ) :
    monRetire s x σ = (σ, if s then 3 * Fintype.card A else 0) := by
  obtain ⟨act, nodes⟩ := σ
  have hact' : act = univ := hact
  subst hact'
  cases s
  · rfl
  · show ((⟨monKeep x ⟨univ, nodes⟩,
          fun a => if a ∈ monKeep x ⟨univ, nodes⟩ then nodes a else none⟩ : MonState A Z),
        3 * (univ : Finset A).card
          + ∑ a ∈ univ \ monKeep x ⟨univ, nodes⟩, monOptSize (nodes a)) = _
    rw [hkeep]
    simp

section Run

variable [Fintype A] [LinearOrder A]

/-- The monitor state right after the build on the table `x`. -/
def buildState (circ : A → MaxCirc Z) (x : Z → ℝ × ℝ) : MonState A Z :=
  ⟨univ, fun a => some (monBuild x (circ a))⟩

open Classical in
/-- One transition of the implemented monitor (`monRun`): retirement on the current table
`xk`, then the wave for the new table `xk1`. -/
def nextState (s : Bool) (xk xk1 : Z → ℝ × ℝ) (σ : MonState A Z) : MonState A Z :=
  (monWaveAll xk1 (fun z => decide (xk1 z ≠ xk z)) (monRetire s xk σ).1).1

open Classical in
/-- The work of that transition (`monStepCost`). -/
def stepCostOf (s : Bool) (ε : ℝ) (xk xk1 : Z → ℝ × ℝ) (σ : MonState A Z) : ℕ :=
  (monQuery ε xk σ).2 + (monRetire s xk σ).2
    + (monWaveAll xk1 (fun z => decide (xk1 z ≠ xk z)) (monRetire s xk σ).1).2 + 1

theorem monRun_succ (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (k : ℕ) :
    monRun s circ x (k + 1) = nextState s (x k) (x (k + 1)) (monRun s circ x k) := rfl

theorem monStepCost_eq (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) (k : ℕ) :
    monStepCost s circ x ε k = stepCostOf s ε (x k) (x (k + 1)) (monRun s circ x k) := rfl

open Classical in
/-- A step on an unchanged table at which no action is dominated leaves the state alone and
costs one query, one retirement scan (selective monitor only) and one table step. -/
theorem quiet_step (s : Bool) (circ : A → MaxCirc Z) (ε : ℝ) {x : Z → ℝ × ℝ}
    {σ : MonState A Z} (hinv : MonInv circ x σ) (hact : σ.act = univ)
    (hnd : ∀ a b : A, ¬ ((circ b).ival x).2 < ((circ a).ival x).1) :
    nextState s x x σ = σ ∧
      stepCostOf s ε x x σ
        = 2 * Fintype.card A + (if s then 3 * Fintype.card A else 0) + 1 := by
  have hkeep : monKeep x σ = univ := by
    ext b
    constructor
    · intro _
      exact mem_univ b
    · intro _
      exact (hinv.mem_monKeep b).mpr
        ⟨by rw [hact]; exact mem_univ b, fun ⟨a, _, _, hlt⟩ => hnd a b hlt⟩
  have hret := monRetire_noop s x σ hkeep hact
  have hwave : monWaveAll x (fun z => decide (x z ≠ x z)) σ = (σ, 0) :=
    monWaveAll_noop x (fun z => by simp) σ
  constructor
  · have e : nextState s x x σ
        = (monWaveAll x (fun z => decide (x z ≠ x z)) (monRetire s x σ).1).1 := rfl
    rw [e, hret]
    exact congrArg Prod.fst hwave
  · have hq : (monQuery ε x σ).2 = 2 * Fintype.card A := by
      show 2 * σ.act.card = _
      rw [hact, Finset.card_univ]
    have hw : (monWaveAll x (fun z => decide (x z ≠ x z)) σ).2 = 0 := congrArg Prod.snd hwave
    have e : stepCostOf s ε x x σ = (monQuery ε x σ).2 + (monRetire s x σ).2
        + (monWaveAll x (fun z => decide (x z ≠ x z)) (monRetire s x σ).1).2 + 1 := rfl
    rw [e, hret, hq]
    simp only [hw, add_zero]

/-- While the table does not change and no action is dominated, the monitor stays in its
build state, and every step costs `2|A| + 1` (full) or `5|A| + 1` (selective). -/
theorem monRun_quiet (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) {j : ℕ}
    (hx : ∀ k, k < j → x (k + 1) = x k)
    (hnd : ∀ k, k < j → ∀ a b : A, ¬ ((circ b).ival (x k)).2 < ((circ a).ival (x k)).1) :
    (∀ k, k ≤ j → monRun s circ x k = buildState circ (x k)) ∧
      ∀ k, k < j → monStepCost s circ x ε k
        = 2 * Fintype.card A + (if s then 3 * Fintype.card A else 0) + 1 := by
  have hstate : ∀ k, k ≤ j → monRun s circ x k = buildState circ (x k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rfl
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hinv := monRun_inv s circ x k
      have hact : (monRun s circ x k).act = univ := congrArg MonState.act ihk
      rw [monRun_succ, hx k (by omega),
        (quiet_step s circ ε hinv hact (hnd k (by omega))).1]
      exact ihk
  refine ⟨hstate, fun k hk => ?_⟩
  have hinv := monRun_inv s circ x k
  have hact : (monRun s circ x k).act = univ := congrArg MonState.act (hstate k hk.le)
  rw [monStepCost_eq, hx k hk]
  exact (quiet_step s circ ε hinv hact (hnd k hk)).2

/-- If the monitor is in its build state at step `j`, its later states are those of the
monitor built at step `j`. -/
theorem monRun_shift (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) {j : ℕ}
    (hj : monRun s circ x j = buildState circ (x j)) :
    ∀ k, monRun s circ x (j + k) = monRun s circ (fun i => x (j + i)) k
  | 0 => hj
  | k + 1 => congrArg (nextState s (x (j + k)) (x (j + k + 1))) (monRun_shift s circ x hj k)

/-- The monitor state at step `k` depends on the tables up to step `k` only. -/
theorem monRun_congr (s : Bool) (circ : A → MaxCirc Z) {x x' : ℕ → Z → ℝ × ℝ} :
    ∀ k, (∀ i, i ≤ k → x i = x' i) → monRun s circ x k = monRun s circ x' k
  | 0, h => congrArg (buildState circ) (h 0 le_rfl)
  | k + 1, h => by
      rw [monRun_succ, monRun_succ,
        monRun_congr s circ k (fun i hi => h i (Nat.le_succ_of_le hi)),
        h k (Nat.le_succ k), h (k + 1) le_rfl]

theorem monWork_congr (s : Bool) (circ : A → MaxCirc Z) {x x' : ℕ → Z → ℝ × ℝ} (ε : ℝ)
    (K : ℕ) (h : ∀ i, i ≤ K → x i = x' i) :
    monWork s circ x ε K = monWork s circ x' ε K := by
  have hs : ∑ k ∈ range K, monStepCost s circ x ε k
      = ∑ k ∈ range K, monStepCost s circ x' ε k := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < K := mem_range.mp hk
    rw [monStepCost_eq, monStepCost_eq, monRun_congr s circ k (fun i hi => h i (by omega)),
      h k (by omega), h (k + 1) (by omega)]
  unfold monWork
  rw [hs, monRun_congr s circ K h, h K le_rfl]

/-- Work of a run whose first `j` steps end in the build state: the work of those steps
plus the work of the run built at step `j`. -/
theorem monWork_shift (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) {j : ℕ}
    (hj : monRun s circ x j = buildState circ (x j)) (K : ℕ) :
    monWork s circ x ε (j + K)
      = ∑ k ∈ range j, monStepCost s circ x ε k
        + monWork s circ (fun i => x (j + i)) ε K := by
  have hstep : ∀ k, monStepCost s circ x ε (j + k)
      = monStepCost s circ (fun i => x (j + i)) ε k :=
    fun k => congrArg (stepCostOf s ε (x (j + k)) (x (j + k + 1))) (monRun_shift s circ x hj k)
  have hK := monRun_shift s circ x hj K
  unfold monWork
  rw [Finset.sum_range_add, hK]
  simp only [hstep]
  ring

end Run

end Generic

/-! ### The `[0,1]` box and the forced observations -/

private theorem c3 {t : ℕ} (ht : 3 ≤ t) : Fintype.card (Fin 3) ≤ t := by
  rw [Fintype.card_fin]
  exact ht

private theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

/-- The radius after one observation exceeds `1`: one observation leaves `[0,1]` unchanged. -/
theorem radius_one_gt {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    1 < rootPuctRadius δ ((1 : ℕ) : ℝ) := by
  have h8 : (8 : ℝ) ≤ 12 / δ := by
    rw [le_div_iff₀ hδ0]
    linarith
  have hlog : 2 < Real.log (12 / δ) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact exp_two_lt_eight.trans_le h8
  have e : Real.log (12 * (((1 : ℕ) : ℝ)) ^ 2 / δ) / (2 * ((1 : ℕ) : ℝ))
      = Real.log (12 / δ) / 2 := by
    norm_num
  unfold rootPuctRadius
  rw [Real.lt_sqrt (by norm_num), e]
  linarith

/-- The terminal table of the three-terminal process from a count vector: the initial
interval `[0,1]` before the first observation of a terminal, the clipped interval
`eq:v2radius` afterwards. -/
def boxTab (δ g : ℝ) (c : Fin 3 → ℕ) (z : Fin 3) : ℝ × ℝ :=
  if c z = 0 then (0, 1) else (L3 δ g c z, U3 δ g c z)

/-- The table after `k` observations, `k ≥ 0`. -/
def boxSeq (δ g : ℝ) (N : ℕ → Fin 3 → ℕ) (k : ℕ) : Fin 3 → ℝ × ℝ := boxTab δ g (N k)

/-- The retirement condition for `C` on a terminal table: `U_C < max {L_A, L_B}`. -/
def CutTab (x : Fin 3 → ℝ × ℝ) : Prop := (x 2).2 < max (x 0).1 (x 1).1

section Box

variable {δ g : ℝ} {N : ℕ → Fin 3 → ℕ}

theorem boxTab_of_pos {c : Fin 3 → ℕ} {z : Fin 3} (hz : 1 ≤ c z) :
    boxTab δ g c z = (L3 δ g c z, U3 δ g c z) :=
  ite_eq_right (by omega)

/-- With at most one observation the interval is still `[0,1]`. -/
theorem boxTab_of_le_one (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    {c : Fin 3 → ℕ} {z : Fin 3} (hz : c z ≤ 1) : boxTab δ g c z = (0, 1) := by
  unfold boxTab
  split_ifs with h0
  · rfl
  · have h1 : c z = 1 := by omega
    have hr := radius_one_gt hδ0 hδ
    have hμ0 := mu3_nonneg hg8 z
    have hμ1 := mu3_le hg.le z
    unfold L3 U3 rootPuctLo rootPuctHi
    rw [h1, max_eq_left (by linarith), min_eq_left (by linarith)]

theorem box_no_dom (m : ℕ) {x : Fin 3 → ℝ × ℝ} (hx : ∀ z, x z = (0, 1)) (a b : Fin 3) :
    ¬ ((monRootCirc m b).ival x).2 < ((monRootCirc m a).ival x).1 := by
  rw [MaxCirc.ival_of_onlyTerm _ (monRootCirc_onlyTerm m b),
    MaxCirc.ival_of_onlyTerm _ (monRootCirc_onlyTerm m a), hx b, hx a]
  norm_num

theorem boxSeq_low (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hlow : ∀ k, k ≤ 3 → ∀ a, N k a ≤ 1) {k : ℕ} (hk : k ≤ 3) (z : Fin 3) :
    boxSeq δ g N k z = (0, 1) :=
  boxTab_of_le_one hδ0 hδ hg hg8 (hlow k hk z)

/-- From count `3` on the table is the one used in `MonitorWork.lean`. -/
theorem boxSeq_shift (hhigh : ∀ k, 3 ≤ k → ∀ a, 1 ≤ N k a) :
    (fun i => boxSeq δ g N (3 + i)) = monBox δ g N := by
  funext i z
  exact boxTab_of_pos (hhigh (3 + i) (by omega) z)

/-- **The forced observations are ordinary quiet updates.**  Started on the `[0,1]` box,
both monitors are in their build state after each of the three forced observations, and
each of the three steps costs `7` (full) resp. `16` (selective) operations: a root query, a
retirement scan (selective only), a terminal-table step, and an empty wave. -/
theorem box_quiet (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hlow : ∀ k, k ≤ 3 → ∀ a, N k a ≤ 1) (m : ℕ) (s : Bool) (ε : ℝ) :
    (∀ k, k ≤ 3 → monRun s (monRootCirc m) (boxSeq δ g N) k
        = buildState (monRootCirc m) (boxSeq δ g N k)) ∧
      ∀ k, k < 3 → monStepCost s (monRootCirc m) (boxSeq δ g N) ε k
        = 2 * 3 + (if s then 3 * 3 else 0) + 1 := by
  have hx : ∀ k, k < 3 → boxSeq δ g N (k + 1) = boxSeq δ g N k := by
    intro k hk
    funext z
    rw [boxSeq_low hδ0 hδ hg hg8 hlow (by omega) z, boxSeq_low hδ0 hδ hg hg8 hlow (by omega) z]
  have hnd : ∀ k, k < 3 → ∀ a b : Fin 3,
      ¬ ((monRootCirc m b).ival (boxSeq δ g N k)).2
        < ((monRootCirc m a).ival (boxSeq δ g N k)).1 :=
    fun k hk a b => box_no_dom m (fun z => boxSeq_low hδ0 hδ hg hg8 hlow (by omega) z) a b
  have h := monRun_quiet s (monRootCirc m) (boxSeq δ g N) ε hx hnd
  rw [Fintype.card_fin] at h
  exact h

/-- **Gap 2, states.**  The monitors started on the `[0,1]` box before any observation are,
after `3 + k` observations, in exactly the state of the monitors of `MonitorWork.lean`
(built after the forced observations) at their step `k`. -/
theorem boxRun_eq (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hlow : ∀ k, k ≤ 3 → ∀ a, N k a ≤ 1) (hhigh : ∀ k, 3 ≤ k → ∀ a, 1 ≤ N k a)
    (m : ℕ) (s : Bool) (k : ℕ) :
    monRun s (monRootCirc m) (boxSeq δ g N) (3 + k)
      = monRun s (monRootCirc m) (monBox δ g N) k := by
  have h := monRun_shift s (monRootCirc m) (boxSeq δ g N)
    ((box_quiet hδ0 hδ hg hg8 hlow m s 0).1 3 le_rfl) k
  rw [boxSeq_shift hhigh] at h
  exact h

/-- **Gap 2, work.**  The monitor work from the `[0,1]` box exceeds the monitor work of
`MonitorWork.lean` by exactly `48` (selective) resp. `21` (full) operations. -/
theorem boxWork_eq (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hlow : ∀ k, k ≤ 3 → ∀ a, N k a ≤ 1) (hhigh : ∀ k, 3 ≤ k → ∀ a, 1 ≤ N k a)
    (m : ℕ) (s : Bool) (ε : ℝ) (K : ℕ) :
    monWork s (monRootCirc m) (boxSeq δ g N) ε (3 + K)
      = monWork s (monRootCirc m) (monBox δ g N) ε K + (if s then 48 else 21) := by
  obtain ⟨hst, hc⟩ := box_quiet hδ0 hδ hg hg8 hlow m s ε
  have h := monWork_shift s (monRootCirc m) (boxSeq δ g N) ε (hst 3 le_rfl) K
  rw [boxSeq_shift hhigh] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num)]
  cases s <;> simp <;> omega

/-- Outputs of the two monitors started on the `[0,1]` box: they agree after every
observation count `t ≥ 0`; the stopping set is empty for `t < 3` and is the three-terminal
check `Stop3` for `t ≥ 3`. -/
theorem box_outputs {sel : ℕ → Fin 3} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g)
    (hg8 : g ≤ 1 / 8) (hlow : ∀ k, k ≤ 3 → ∀ a, N k a ≤ 1)
    (htr : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) N sel) (m : ℕ) :
    (∀ t, (monQuery (g / 2) (boxSeq δ g N t) (monRun true (monRootCirc m) (boxSeq δ g N) t)).1
        = (monQuery (g / 2) (boxSeq δ g N t)
            (monRun false (monRootCirc m) (boxSeq δ g N) t)).1) ∧
    (∀ (s : Bool) (t : ℕ), t < 3 →
      (monQuery (g / 2) (boxSeq δ g N t)
        (monRun s (monRootCirc m) (boxSeq δ g N) t)).1.stops = ∅) ∧
    (∀ (s : Bool) (t : ℕ), 3 ≤ t →
      (monQuery (g / 2) (boxSeq δ g N t)
        (monRun s (monRootCirc m) (boxSeq δ g N) t)).1.stops = {a | Stop3 δ g (N t) a}) := by
  have hhigh : ∀ k, 3 ≤ k → ∀ a, 1 ≤ N k a := fun k hk a => htr.one_le a (c3 hk)
  have hq := fun s => (box_quiet hδ0 hδ hg hg8 hlow m s 0).1
  have hshift : ∀ (s : Bool) (k : ℕ),
      (monQuery (g / 2) (boxSeq δ g N (3 + k))
          (monRun s (monRootCirc m) (boxSeq δ g N) (3 + k))).1
        = (monQuery (g / 2) (monBox δ g N k) (monRun s (monRootCirc m) (monBox δ g N) k)).1 := by
    intro s k
    rw [boxRun_eq hδ0 hδ hg hg8 hlow hhigh m s k,
      show boxSeq δ g N (3 + k) = monBox δ g N k from congrFun (boxSeq_shift hhigh) k]
  refine ⟨fun t => ?_, fun s t ht => ?_, fun s t ht => ?_⟩
  · by_cases h3 : t ≤ 3
    · rw [hq true t h3, hq false t h3]
    · obtain ⟨k, rfl⟩ : ∃ k, t = 3 + k := ⟨t - 3, by omega⟩
      rw [hshift true k, hshift false k]
      exact (v2_outputs hδ0 hδ hg hg8 htr m k).1
  · have hst := hq s t (by omega)
    have hinv := monRun_inv s (monRootCirc m) (boxSeq δ g N) t
    have hact : (monRun s (monRootCirc m) (boxSeq δ g N) t).act = univ :=
      congrArg MonState.act hst
    rw [hinv.query_out (g / 2)]
    ext b
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hb
    have hb' : MarginalStops (monRun s (monRootCirc m) (boxSeq δ g N) t).act
        (fun a => ((monRootCirc m a).ival (boxSeq δ g N t)).1)
        (fun a => ((monRootCirc m a).ival (boxSeq δ g N t)).2) (g / 2) b := hb
    obtain ⟨c, hc⟩ : ∃ c : Fin 3, c ≠ b := by
      by_cases h : b = 0
      · exact ⟨1, by rw [h]; decide⟩
      · exact ⟨0, fun e => h e.symm⟩
    have h1 : ((monRootCirc m c).ival (boxSeq δ g N t)).2
        - ((monRootCirc m b).ival (boxSeq δ g N t)).1 ≤ g / 2 :=
      hb'.2 c (by rw [hact]; exact mem_univ c) hc
    rw [MaxCirc.ival_of_onlyTerm _ (monRootCirc_onlyTerm m c),
      MaxCirc.ival_of_onlyTerm _ (monRootCirc_onlyTerm m b),
      boxSeq_low hδ0 hδ hg hg8 hlow (by omega) c,
      boxSeq_low hδ0 hδ hg hg8 hlow (by omega) b] at h1
    have h2 : (1 : ℝ) - 0 ≤ g / 2 := h1
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, t = 3 + k := ⟨t - 3, by omega⟩
    rw [hshift s k]
    cases s
    · exact (v2_outputs hδ0 hδ hg hg8 htr m k).2.1
    · rw [(v2_outputs hδ0 hδ hg hg8 htr m k).1]
      exact (v2_outputs hδ0 hδ hg hg8 htr m k).2.1

/-- Once the retirement condition for `C` holds it holds at every later count. -/
theorem cut3_persist {sel : ℕ → Fin 3} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (htr : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) N sel) {tc s : ℕ} (htc : 3 ≤ tc)
    (hcut : Cut3 δ g (N tc)) (hs : tc ≤ s) : Cut3 δ g (N s) := by
  have hU : U3 δ g (N s) 2 ≤ U3 δ g (N tc) 2 :=
    rootPuctHi_anti hδ0 hδ (htr.one_le 2 (c3 htc)) (htr.mono 2 (c3 htc) hs)
  have hL0 : L3 δ g (N tc) 0 ≤ L3 δ g (N s) 0 :=
    rootPuctLo_mono hδ0 hδ (htr.one_le 0 (c3 htc)) (htr.mono 0 (c3 htc) hs)
  have hL1 : L3 δ g (N tc) 1 ≤ L3 δ g (N s) 1 :=
    rootPuctLo_mono hδ0 hδ (htr.one_le 1 (c3 htc)) (htr.mono 1 (c3 htc) hs)
  exact lt_of_le_of_lt hU (lt_of_lt_of_le hcut (max_le_max hL0 hL1))

end Box

/-! ### Histories, the controller, the monitors as functions of the history -/

/-- One completed rollout: the root action selected, the terminal reached, the reward
observed. -/
abbrev Entry := Fin 3 × Fin 3 × ℝ

/-- The controller's history of selections and observations, most recent first. -/
abbrev Hist := List Entry

/-- Number of rollouts through root action `a`. -/
def cntA : Hist → Fin 3 → ℕ
  | [], _ => 0
  | e :: h, a => cntA h a + if e.1 = a then 1 else 0

/-- Sum of the rewards observed through root action `a`. -/
def sumA : Hist → Fin 3 → ℝ
  | [], _ => 0
  | e :: h, a => sumA h a + if e.1 = a then e.2.2 else 0

/-- Number of observations of terminal `z`. -/
def cntZ : Hist → Fin 3 → ℕ
  | [], _ => 0
  | e :: h, z => cntZ h z + if e.2.1 = z then 1 else 0

/-- Sum of the rewards observed at terminal `z`. -/
def sumZ : Hist → Fin 3 → ℝ
  | [], _ => 0
  | e :: h, z => sumZ h z + if e.2.1 = z then e.2.2 else 0

/-- The common terminal observation table after a history: `[0,1]` at a terminal that has
not been observed, otherwise the clipped interval `eq:v2radius` around the empirical mean. -/
def histTab (δ : ℝ) (h : Hist) (z : Fin 3) : ℝ × ℝ :=
  if cntZ h z = 0 then (0, 1)
  else (rootPuctLo δ (sumZ h z / cntZ h z) (cntZ h z),
    rootPuctHi δ (sumZ h z / cntZ h z) (cntZ h z))

/-- The table after the first `k` observations of the history. -/
def histSeq (δ : ℝ) (h : Hist) (k : ℕ) : Fin 3 → ℝ × ℝ := histTab δ (h.drop (h.length - k))

/-- The root-PUCT index `eq:v2puct` with `λ = 1`, from the controller's own statistics. -/
def puctIdx (h : Hist) (j : Fin 3) : ℝ :=
  sumA h j / cntA h j + Real.sqrt (h.length : ℝ) / (1 + cntA h j)

/-- A tie-breaking: a deterministic selection function that returns a maximiser of the
root-PUCT index on every history with at least three observations. -/
def IsPuctPick (pick : Hist → Fin 3) : Prop :=
  ∀ h : Hist, 3 ≤ h.length → ∀ j, puctIdx h j ≤ puctIdx h (pick h)

theorem exists_isPuctPick : ∃ pick : Hist → Fin 3, IsPuctPick pick := by
  have hex : ∀ h : Hist, ∃ i, ∀ j, puctIdx h j ≤ puctIdx h i :=
    fun h => Finite.exists_max (puctIdx h)
  choose pick hpick using hex
  exact ⟨pick, fun h _ j => hpick h j⟩

/-- The next root action: the forced observations `A, B, C`, then the tie-breaking. -/
def nextAction (pick : Hist → Fin 3) (h : Hist) : Fin 3 :=
  if hl : h.length < 3 then ⟨h.length, hl⟩ else pick h

/-- The next rollout on the `m`-leaf graph: select the root action, walk below it with the
path rule of the current time, observe the point-mass reward of the terminal reached. -/
def nextEntry (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3) (h : Hist) : Entry :=
  (nextAction pick h, ((monRootCirc m (nextAction pick h)).monWalk (rule h.length) 0).1,
    mu3 g ((monRootCirc m (nextAction pick h)).monWalk (rule h.length) 0).1)

/-- Controller status. -/
inductive Status
  | running
  | stopped (a : Fin 3)
  | failed

/-- Controller state: the history and whether it has halted (and with which
recommendation). -/
structure Ctl where
  hist : Hist
  status : Status

/-- What the controller reads from a monitor: the shared failure flag, and the canonical
lower-bound leader and stopping set. -/
structure Iface where
  fail : Prop
  out : MonOut (Fin 3)

open Classical in
/-- The recommendation read off the stopping set (its lowest element). -/
def firstStop (S : Set (Fin 3)) : Option (Fin 3) :=
  if (0 : Fin 3) ∈ S then some 0 else if (1 : Fin 3) ∈ S then some 1
  else if (2 : Fin 3) ∈ S then some 2 else none

theorem firstStop_empty : firstStop ∅ = none := by simp [firstStop]

theorem firstStop_zero : firstStop {0} = some 0 := by simp [firstStop]

open Classical in
/-- Controller step on history `h`, given the monitor output `o`. -/
def ctlStepAux (next : Hist → Entry) (h : Hist) (o : Iface) : Status → Ctl
  | .running =>
      if o.fail then ⟨h, .failed⟩
      else (firstStop o.out.stops).elim ⟨next h :: h, .running⟩ (fun a => ⟨h, .stopped a⟩)
  | st => ⟨h, st⟩

/-- **The controller step.**  A halted controller stays put.  A running controller halts
with failure if the failure flag is up, halts with the recommendation if the stopping set
is nonempty, and otherwise performs the next selection, rollout and observation. -/
def ctlStep (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3) (c : Ctl)
    (o : Iface) : Ctl :=
  ctlStepAux (nextEntry m g rule pick) c.hist o c.status

/-- **The monitor in the loop.**  The selective (`s = true`) or full (`s = false`) monitor,
as a function of the controller state: it was built on the `[0,1]` box and has processed
the observations of the history one by one (`monRun` along `histSeq`); it exposes the
failure flag of the common terminal table and the output of its root query. -/
def ctlMon (s : Bool) (m : ℕ) (δ ε : ℝ) (c : Ctl) : Iface :=
  ⟨∃ z, (histTab δ c.hist z).2 < (histTab δ c.hist z).1,
    (monQuery ε (histSeq δ c.hist c.hist.length)
      (monRun s (monRootCirc m) (histSeq δ c.hist) c.hist.length)).1⟩

/-- Rollout work of a history: `monRollout` for every rollout, forced ones included. -/
def rollCost (m : ℕ) (rule : ℕ → ℕ → Bool) : Hist → ℕ
  | [] => 0
  | e :: h => rollCost m rule h + monRollout m rule h.length e.1

/-- **Total work of a run that ends with history `h`**: reading and initializing the graph
and its final disposal, every rollout (forced ones included), and the monitor work from the
`[0,1]` box: build, and for every observation of the history a terminal-table step, a wave,
a retirement scan (selective) and a root query, then the final query and disposal. -/
def histWork (s : Bool) (m : ℕ) (δ ε : ℝ) (rule : ℕ → ℕ → Bool) (h : Hist) : ℕ :=
  2 * ∑ a, (monRootCirc m a).monSize + rollCost m rule h
    + monWork s (monRootCirc m) (histSeq δ h) ε h.length

section Loop

variable (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3)

/-- The continued trace: the history after `t` observations if the controller never halts. -/
def freeH : ℕ → Hist
  | 0 => []
  | t + 1 => nextEntry m g rule pick (freeH t) :: freeH t

/-- Root counts of the continued trace. -/
def freeN (t : ℕ) (a : Fin 3) : ℕ := cntA (freeH m g rule pick t) a

/-- Root reward sums of the continued trace. -/
def freeS (t : ℕ) (a : Fin 3) : ℝ := sumA (freeH m g rule pick t) a

/-- Selections of the continued trace. -/
def freeSel (t : ℕ) : Fin 3 := nextAction pick (freeH m g rule pick t)

/-- **The closed loop** of the controller with the selective (`s = true`) or full
(`s = false`) monitor, from the empty history. -/
def closedLoop (s : Bool) (δ : ℝ) : ℕ → Ctl :=
  runTraj (ctlStep m g rule pick) (ctlMon s m δ (g / 2)) ⟨[], .running⟩

local notation "FH" => freeH m g rule pick

local notation "NE" => nextEntry m g rule pick

theorem freeH_length : ∀ t, (FH t).length = t
  | 0 => rfl
  | t + 1 => by
      show (FH t).length + 1 = t + 1
      rw [freeH_length t]

theorem nextEntry_term (h : Hist) : (NE h).2.1 = (NE h).1 := monRootCirc_walk m _ _

theorem nextEntry_reward (h : Hist) : (NE h).2.2 = mu3 g (NE h).1 :=
  congrArg (mu3 g) (monRootCirc_walk m _ _)

theorem cntZ_free : ∀ t, cntZ (FH t) = cntA (FH t)
  | 0 => by
      funext a
      rfl
  | t + 1 => by
      funext a
      show cntZ (FH t) a + (if (NE (FH t)).2.1 = a then 1 else 0)
        = cntA (FH t) a + (if (NE (FH t)).1 = a then 1 else 0)
      rw [cntZ_free t, nextEntry_term]

theorem sumZ_free : ∀ t, sumZ (FH t) = sumA (FH t)
  | 0 => by
      funext a
      rfl
  | t + 1 => by
      funext a
      show sumZ (FH t) a + (if (NE (FH t)).2.1 = a then (NE (FH t)).2.2 else 0)
        = sumA (FH t) a + (if (NE (FH t)).1 = a then (NE (FH t)).2.2 else 0)
      rw [sumZ_free t, nextEntry_term]

/-- Every observation through root action `a` returns `mu3 g a`. -/
theorem sumA_free : ∀ t a, sumA (FH t) a = (cntA (FH t) a : ℝ) * mu3 g a
  | 0, a => by
      show (0 : ℝ) = ((0 : ℕ) : ℝ) * mu3 g a
      simp
  | t + 1, a => by
      show sumA (FH t) a + (if (NE (FH t)).1 = a then (NE (FH t)).2.2 else 0)
        = ((cntA (FH t) a + (if (NE (FH t)).1 = a then 1 else 0) : ℕ) : ℝ) * mu3 g a
      rw [sumA_free t a, nextEntry_reward]
      split_ifs with h
      · rw [h]
        push_cast
        ring
      · simp only [add_zero]

theorem freeSel_forced {t : ℕ} (ht : t < 3) : freeSel m g rule pick t = ⟨t, ht⟩ := by
  have hl : (FH t).length < 3 := by
    rw [freeH_length]
    exact ht
  show nextAction pick (FH t) = _
  unfold nextAction
  rw [dite_eq_left hl]
  exact Fin.ext (freeH_length m g rule pick t)

theorem freeSel_zero : freeSel m g rule pick 0 = 0 :=
  freeSel_forced m g rule pick (by norm_num)

theorem freeSel_one : freeSel m g rule pick 1 = 1 :=
  freeSel_forced m g rule pick (by norm_num)

theorem freeSel_two : freeSel m g rule pick 2 = 2 :=
  freeSel_forced m g rule pick (by norm_num)

theorem freeSel_pick {t : ℕ} (ht : 3 ≤ t) : freeSel m g rule pick t = pick (FH t) := by
  have hl : ¬ (FH t).length < 3 := by
    rw [freeH_length]
    omega
  show nextAction pick (FH t) = _
  unfold nextAction
  rw [dite_eq_right hl]

theorem freeN_succ (t : ℕ) (a : Fin 3) :
    freeN m g rule pick (t + 1) a
      = freeN m g rule pick t a + if freeSel m g rule pick t = a then 1 else 0 := rfl

/-- After the three forced observations every root action has count one. -/
theorem freeN_three (a : Fin 3) : freeN m g rule pick 3 a = 1 := by
  have key : ∀ a : Fin 3, (0 + (if (0 : Fin 3) = a then 1 else 0)
      + (if (1 : Fin 3) = a then 1 else 0) + (if (2 : Fin 3) = a then 1 else 0) : ℕ) = 1 := by
    decide
  have h3 : freeN m g rule pick 3 a
      = 0 + (if freeSel m g rule pick 0 = a then 1 else 0)
        + (if freeSel m g rule pick 1 = a then 1 else 0)
        + (if freeSel m g rule pick 2 = a then 1 else 0) := rfl
  rw [h3, freeSel_zero, freeSel_one, freeSel_two]
  exact key a

theorem freeN_mono (a : Fin 3) {s t : ℕ} (hst : s ≤ t) :
    freeN m g rule pick s a ≤ freeN m g rule pick t a := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih =>
    rw [freeN_succ]
    exact ih.trans (Nat.le_add_right _ _)

theorem freeN_le_one {k : ℕ} (hk : k ≤ 3) (a : Fin 3) : freeN m g rule pick k a ≤ 1 :=
  (freeN_mono m g rule pick a hk).trans (freeN_three m g rule pick a).le

/-- **The continued trace is a run of the root-PUCT controller on the `m`-leaf graph** in
the sense of `MonGraphRun`, for every tie-breaking and every path rule. -/
theorem free_graphRun (hpick : IsPuctPick pick) :
    MonGraphRun m g rule (freeN m g rule pick) (freeS m g rule pick) (freeSel m g rule pick) where
  initN := freeN_three m g rule pick
  initS := fun a => by
    rw [monRootCirc_walk]
    show sumA (FH 3) a = _
    rw [sumA_free, show cntA (FH 3) a = 1 from freeN_three m g rule pick a]
    simp
  stepN := fun t _ a => rfl
  stepS := fun t _ a => by
    show sumA (FH t) a + (if (NE (FH t)).1 = a then (NE (FH t)).2.2 else 0)
      = sumA (FH t) a + if nextAction pick (FH t) = a
          then mu3 g ((monRootCirc m a).monWalk (rule t) 0).1 else 0
    rw [nextEntry_reward, monRootCirc_walk]
    show sumA (FH t) a
        + (if nextAction pick (FH t) = a then mu3 g (nextAction pick (FH t)) else 0) = _
    split_ifs with h
    · rw [h]
    · rfl
  greedy := fun t ht j => by
    have h := hpick (FH t) (by rw [freeH_length]; exact ht) j
    unfold puctIdx at h
    rw [freeH_length] at h
    rw [freeSel_pick m g rule pick ht]
    exact h

/-- The terminal table of the continued trace is the box table of its counts. -/
theorem histTab_free (δ : ℝ) (t : ℕ) :
    histTab δ (FH t) = boxTab δ g (freeN m g rule pick t) := by
  funext z
  have hc : cntZ (FH t) z = freeN m g rule pick t z := congrFun (cntZ_free m g rule pick t) z
  have hs : sumZ (FH t) z = sumA (FH t) z := congrFun (sumZ_free m g rule pick t) z
  unfold histTab boxTab
  rw [hc, hs]
  by_cases h0 : freeN m g rule pick t z = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · have hq : sumA (FH t) z / (freeN m g rule pick t z : ℝ) = mu3 g z := by
      rw [sumA_free]
      exact mul_div_cancel_left₀ _ (by exact_mod_cast h0)
    rw [ite_eq_right h0, ite_eq_right h0, hq]
    rfl

theorem freeH_drop (j : ℕ) : ∀ d, (FH (j + d)).drop d = FH j
  | 0 => rfl
  | d + 1 => by
      show (NE (FH (j + d)) :: FH (j + d)).drop (d + 1) = FH j
      exact freeH_drop j d

theorem histSeq_free (δ : ℝ) {k t : ℕ} (hk : k ≤ t) :
    histSeq δ (FH t) k = boxSeq δ g (freeN m g rule pick) k := by
  have h := freeH_drop m g rule pick k (t - k)
  rw [show k + (t - k) = t by omega] at h
  unfold histSeq
  rw [freeH_length, h, histTab_free]
  rfl

/-- The monitor in the loop, on a history of the continued trace, is the monitor run along
the box tables of the trace. -/
theorem ctlMon_free_out (s : Bool) (δ ε : ℝ) (t : ℕ) (st : Status) :
    (ctlMon s m δ ε ⟨FH t, st⟩).out
      = (monQuery ε (boxSeq δ g (freeN m g rule pick) t)
          (monRun s (monRootCirc m) (boxSeq δ g (freeN m g rule pick)) t)).1 := by
  show (monQuery ε (histSeq δ (FH t) (FH t).length)
    (monRun s (monRootCirc m) (histSeq δ (FH t)) (FH t).length)).1 = _
  rw [freeH_length,
    monRun_congr s (monRootCirc m) t (fun i hi => histSeq_free m g rule pick δ hi),
    histSeq_free m g rule pick δ le_rfl]

/-- The shared failure flag is never raised on the continued trace. -/
theorem ctlMon_free_not_fail (hg : 0 < g) (hg8 : g ≤ 1 / 8) (s : Bool) (δ ε : ℝ) (t : ℕ)
    (st : Status) : ¬ (ctlMon s m δ ε ⟨FH t, st⟩).fail := by
  rintro ⟨z, hz⟩
  have hz' : (histTab δ (FH t) z).2 < (histTab δ (FH t) z).1 := hz
  rw [histTab_free] at hz'
  unfold boxTab at hz'
  split_ifs at hz' with h0
  · norm_num at hz'
  · have h1 : L3 δ g (freeN m g rule pick t) z ≤ mu3 g z :=
      rootPuctLo_le_mean (mu3_nonneg hg8 z)
    have h2 : mu3 g z ≤ U3 δ g (freeN m g rule pick t) z :=
      mean_le_puctHi ((mu3_le hg.le z).trans (by norm_num))
    have h3 : U3 δ g (freeN m g rule pick t) z < L3 δ g (freeN m g rule pick t) z := hz'
    linarith

/-! #### Steps of the controller -/

open Classical in
theorem ctlStep_running (h : Hist) (o : Iface) :
    ctlStep m g rule pick ⟨h, .running⟩ o
      = if o.fail then ⟨h, .failed⟩
        else (firstStop o.out.stops).elim ⟨NE h :: h, .running⟩ (fun a => ⟨h, .stopped a⟩) :=
  rfl

theorem ctlStep_continue {h : Hist} {o : Iface} (hf : ¬ o.fail) (hs : o.out.stops = ∅) :
    ctlStep m g rule pick ⟨h, .running⟩ o = ⟨NE h :: h, .running⟩ := by
  rw [ctlStep_running, ite_eq_right hf, hs, firstStop_empty]
  rfl

theorem ctlStep_stop {h : Hist} {o : Iface} (hf : ¬ o.fail) (hs : o.out.stops = {0}) :
    ctlStep m g rule pick ⟨h, .running⟩ o = ⟨h, .stopped 0⟩ := by
  rw [ctlStep_running, ite_eq_right hf, hs, firstStop_zero]
  rfl

theorem ctlStep_cases (h : Hist) (st : Status) (o : Iface) :
    (∃ st', ctlStep m g rule pick ⟨h, st⟩ o = ⟨h, st'⟩) ∨
      ctlStep m g rule pick ⟨h, st⟩ o = ⟨NE h :: h, .running⟩ := by
  classical
  cases st with
  | running =>
    rw [ctlStep_running]
    by_cases hf : o.fail
    · rw [ite_eq_left hf]
      exact Or.inl ⟨_, rfl⟩
    · rw [ite_eq_right hf]
      cases firstStop o.out.stops with
      | none => exact Or.inr rfl
      | some a => exact Or.inl ⟨_, rfl⟩
  | stopped a => exact Or.inl ⟨_, rfl⟩
  | failed => exact Or.inl ⟨_, rfl⟩

theorem closedLoop_succ (s : Bool) (δ : ℝ) (t : ℕ) :
    closedLoop m g rule pick s δ (t + 1)
      = ctlStep m g rule pick (closedLoop m g rule pick s δ t)
          (ctlMon s m δ (g / 2) (closedLoop m g rule pick s δ t)) := rfl

/-- Every state reached by a closed loop carries a history of the continued trace. -/
theorem closedLoop_reach (s : Bool) (δ : ℝ) :
    ∀ t, ∃ j st, closedLoop m g rule pick s δ t = ⟨FH j, st⟩
  | 0 => ⟨0, .running, rfl⟩
  | t + 1 => by
      obtain ⟨j, st, hj⟩ := closedLoop_reach s δ t
      rw [closedLoop_succ, hj]
      rcases ctlStep_cases m g rule pick (FH j) st (ctlMon s m δ (g / 2) ⟨FH j, st⟩)
        with ⟨st', h⟩ | h
      · exact ⟨j, st', h⟩
      · exact ⟨j + 1, .running, h⟩

/-- The closed loop, from the monitor's outputs along the continued trace: if the failure
flag is never raised, the stopping set is empty before count `τ` and is `{A}` at `τ`, then
the loop makes exactly `τ` observations and halts with recommendation `A`. -/
theorem closedLoop_spec (s : Bool) (δ : ℝ) {τ : ℕ}
    (hfail : ∀ t st, ¬ (ctlMon s m δ (g / 2) ⟨FH t, st⟩).fail)
    (hno : ∀ t, t < τ → (ctlMon s m δ (g / 2) ⟨FH t, .running⟩).out.stops = ∅)
    (hstop : (ctlMon s m δ (g / 2) ⟨FH τ, .running⟩).out.stops = {0}) :
    (∀ t, t ≤ τ → closedLoop m g rule pick s δ t = ⟨FH t, .running⟩) ∧
      ∀ t, τ < t → closedLoop m g rule pick s δ t = ⟨FH τ, .stopped 0⟩ := by
  have h1 : ∀ t, t ≤ τ → closedLoop m g rule pick s δ t = ⟨FH t, .running⟩ := by
    intro t
    induction t with
    | zero =>
      intro _
      rfl
    | succ t ih =>
      intro ht
      rw [closedLoop_succ, ih (by omega)]
      exact ctlStep_continue m g rule pick (hfail t _) (hno t (by omega))
  have h2 : ∀ d, closedLoop m g rule pick s δ (τ + 1 + d) = ⟨FH τ, .stopped 0⟩ := by
    intro d
    induction d with
    | zero =>
      show closedLoop m g rule pick s δ (τ + 1) = _
      rw [closedLoop_succ, h1 τ le_rfl]
      exact ctlStep_stop m g rule pick (hfail τ _) hstop
    | succ d ih =>
      show closedLoop m g rule pick s δ (τ + 1 + d + 1) = _
      rw [closedLoop_succ, ih]
      rfl
  refine ⟨h1, fun t ht => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, t = τ + 1 + d := ⟨t - (τ + 1), by omega⟩
  exact h2 d

/-! #### Work of the continued trace -/

theorem rollCost_free : ∀ t, rollCost m rule (FH t)
    = ∑ u ∈ range t, monRollout m rule u (freeSel m g rule pick u)
  | 0 => by
      rw [Finset.sum_range_zero]
      rfl
  | t + 1 => by
      show rollCost m rule (FH t) + monRollout m rule (FH t).length (NE (FH t)).1 = _
      rw [rollCost_free t, freeH_length, Finset.sum_range_succ]
      rfl

theorem free_forced_rollouts :
    ∑ u ∈ range 3, monRollout m rule u (freeSel m g rule pick u)
      = ∑ a : Fin 3, monRollout m rule a a := by
  rw [Fin.sum_univ_three]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [freeSel_zero, freeSel_one, freeSel_two]
  rfl

/-- **Gap 2, total work.**  The work of the run from the `[0,1]` box, with the forced
observations charged, is the work `v2Work` of `MonitorWork.lean` plus `48` (selective)
resp. `21` (full): the forced rollouts are already in `v2Work`, and the three forced
observations cause three quiet monitor steps (`box_quiet`). -/
theorem histWork_free {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hpick : IsPuctPick pick) (s : Bool) {τ : ℕ} (hτ : 3 ≤ τ) :
    histWork s m δ (g / 2) rule (FH τ)
      = v2Work s m δ g rule (freeN m g rule pick) (freeSel m g rule pick) τ
        + (if s then 48 else 21) := by
  have htr := (free_graphRun m g rule pick hpick).trace
  have hlow : ∀ k, k ≤ 3 → ∀ a, freeN m g rule pick k a ≤ 1 :=
    fun k hk a => freeN_le_one m g rule pick hk a
  have hhigh : ∀ k, 3 ≤ k → ∀ a, 1 ≤ freeN m g rule pick k a :=
    fun k hk a => htr.one_le a (c3 hk)
  have hroll : rollCost m rule (FH τ)
      = ∑ a : Fin 3, monRollout m rule a a
        + ∑ t ∈ Ico 3 τ, monRollout m rule t (freeSel m g rule pick t) := by
    rw [rollCost_free, ← Finset.sum_range_add_sum_Ico _ hτ, free_forced_rollouts]
  have hmon : monWork s (monRootCirc m) (histSeq δ (FH τ)) (g / 2) (FH τ).length
      = monWork s (monRootCirc m) (monBox δ g (freeN m g rule pick)) (g / 2) (τ - 3)
        + (if s then 48 else 21) := by
    rw [freeH_length, monWork_congr s (monRootCirc m) (g / 2) τ
      (fun i hi => histSeq_free m g rule pick δ hi)]
    have h := boxWork_eq hδ0 hδ hg hg8 hlow hhigh m s (g / 2) (τ - 3)
    rw [show 3 + (τ - 3) = τ by omega] at h
    exact h
  unfold histWork v2Work
  rw [hroll, hmon]
  ring

end Loop

/-! ### The closed-loop statement for one run -/

/-- The run-level conclusions of `thm:v2separation` for the closed loops on the `m`-leaf
graph with gap `g`, path rule `rule` and tie-breaking `pick`; `tc` is the first cut time
and `τ` the stopping time (both observation counts). -/
structure ClosedLoopRun (m : ℕ) (δ g : ℝ) (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3)
    (tc τ : ℕ) : Prop where
  /-- Exact coupling: the closed loops with the selective and with the full monitor are in
  the same state (history of selections, terminals reached and observations; status) at
  every time. -/
  coupled : ∀ t, closedLoop m g rule pick true δ t = closedLoop m g rule pick false δ t
  /-- `tc` is the first cut time, and the cut persists: on the terminal table of the
  continued trace, `U_C < max {L_A, L_B}` holds exactly at the counts `s ≥ tc`. -/
  cut : ∀ s, CutTab (histTab δ (freeH m g rule pick s)) ↔ tc ≤ s
  /-- The cut comes after the forced observations. -/
  cut_gt : 3 < tc
  /-- Up to `τ` observations both loops are running, on the continued trace. -/
  running : ∀ (s : Bool) (t : ℕ), t ≤ τ →
    closedLoop m g rule pick s δ t = ⟨freeH m g rule pick t, .running⟩
  /-- Both loops halt after exactly `τ` observations and recommend `A`. -/
  halted : ∀ (s : Bool) (t : ℕ), τ < t →
    closedLoop m g rule pick s δ t = ⟨freeH m g rule pick τ, .stopped 0⟩
  /-- Every observation of `C` from the cut on strictly decreases the upper endpoint of
  the terminal `z`. -/
  strict : ∀ s, tc ≤ s → (nextEntry m g rule pick (freeH m g rule pick s)).1 = 2 →
    (histTab δ (freeH m g rule pick (s + 1)) 2).2 < (histTab δ (freeH m g rule pick s) 2).2
  /-- Charging of the forced observations: the work from the `[0,1]` box is the work of
  `MonitorWork.lean` plus a constant. -/
  work : ∀ s : Bool, histWork s m δ (g / 2) rule (freeH m g rule pick τ)
    = v2Work s m δ g rule (freeN m g rule pick) (freeSel m g rule pick) τ
      + if s then 48 else 21

/-- **Closed loop, coupling and first cut time**, for every `δ ∈ (0, 1/2]`, `g ∈ (0, 1/8]`,
`m`, path rule and tie-breaking: if `tc ≥ 3` is the first count from `3` on at which `Cut3`
holds on the continued trace and `τ ≥ 3` is the first count at which `Stop3` holds, then all
of `ClosedLoopRun` holds. -/
theorem closedLoopRun_of_first_times (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool)
    (pick : Hist → Fin 3) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    (hpick : IsPuctPick pick) {tc τ : ℕ} (htc : 3 ≤ tc)
    (hcut : Cut3 δ g (freeN m g rule pick tc))
    (hcmin : ∀ s, 3 ≤ s → s < tc → ¬ Cut3 δ g (freeN m g rule pick s))
    (hτ : 3 ≤ τ) (hstop : Stop3 δ g (freeN m g rule pick τ) 0)
    (hsmin : ∀ s a, 3 ≤ s → s < τ → ¬ Stop3 δ g (freeN m g rule pick s) a) :
    ClosedLoopRun m δ g rule pick tc τ := by
  have htr := (free_graphRun m g rule pick hpick).trace
  have hlow : ∀ k, k ≤ 3 → ∀ a, freeN m g rule pick k a ≤ 1 :=
    fun k hk a => freeN_le_one m g rule pick hk a
  have hhigh : ∀ k, 3 ≤ k → ∀ a, 1 ≤ freeN m g rule pick k a :=
    fun k hk a => htr.one_le a (c3 hk)
  obtain ⟨hagree, hlowstop, hhighstop⟩ := box_outputs hδ0 hδ hg hg8 hlow htr m
  have hspec := fun s : Bool => closedLoop_spec m g rule pick s δ (τ := τ)
    (fun t st => ctlMon_free_not_fail m g rule pick hg hg8 s δ (g / 2) t st)
    (fun t ht => by
      rw [ctlMon_free_out]
      by_cases h3 : t < 3
      · exact hlowstop s t h3
      · rw [hhighstop s t (by omega)]
        ext b
        simp only [Set.mem_empty_iff_false, iff_false]
        exact hsmin t b (by omega) ht)
    (by
      rw [ctlMon_free_out, hhighstop s τ hτ]
      ext b
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hb
        exact stop3_leader_eq hg hg8 hb
      · rintro rfl
        exact hstop)
  have htc3 : tc ≠ 3 := by
    rintro rfl
    have hb3 : ∀ z, (L3 δ g (freeN m g rule pick 3) z, U3 δ g (freeN m g rule pick 3) z)
        = ((0 : ℝ), (1 : ℝ)) := fun z => by
      rw [← boxTab_of_pos (hhigh 3 le_rfl z)]
      exact boxTab_of_le_one hδ0 hδ hg hg8 (hlow 3 le_rfl z)
    have hU : U3 δ g (freeN m g rule pick 3) 2 = 1 := congrArg Prod.snd (hb3 2)
    have hL0 : L3 δ g (freeN m g rule pick 3) 0 = 0 := congrArg Prod.fst (hb3 0)
    have hL1 : L3 δ g (freeN m g rule pick 3) 1 = 0 := congrArg Prod.fst (hb3 1)
    unfold Cut3 at hcut
    rw [hU, hL0, hL1] at hcut
    norm_num at hcut
  refine ⟨?_, ?_, by omega, fun s => (hspec s).1, fun s => (hspec s).2, ?_, ?_⟩
  · intro t
    refine coupled_trajectories (ctlStep m g rule pick) (ctlMon true m δ (g / 2))
      (ctlMon false m δ (g / 2)) ⟨[], .running⟩ (fun u => ?_) t
    obtain ⟨j, st, hj⟩ := closedLoop_reach m g rule pick true δ u
    have hj' : runTraj (ctlStep m g rule pick) (ctlMon true m δ (g / 2)) ⟨[], .running⟩ u
        = ⟨freeH m g rule pick j, st⟩ := hj
    rw [hj']
    have ho : (ctlMon true m δ (g / 2) ⟨freeH m g rule pick j, st⟩).out
        = (ctlMon false m δ (g / 2) ⟨freeH m g rule pick j, st⟩).out := by
      rw [ctlMon_free_out, ctlMon_free_out]
      exact hagree j
    exact congrArg (Iface.mk (∃ z, (histTab δ (freeH m g rule pick j) z).2
      < (histTab δ (freeH m g rule pick j) z).1)) ho
  · intro s
    rw [histTab_free]
    by_cases hs : s ≤ 3
    · have hb : ∀ z, boxTab δ g (freeN m g rule pick s) z = (0, 1) :=
        fun z => boxTab_of_le_one hδ0 hδ hg hg8 (hlow s hs z)
      have hnc : ¬ CutTab (boxTab δ g (freeN m g rule pick s)) := by
        unfold CutTab
        rw [hb 2, hb 0, hb 1]
        norm_num
      constructor
      · intro h
        exact absurd h hnc
      · intro h
        omega
    · have hs3 : 3 ≤ s := by omega
      have hiff : CutTab (boxTab δ g (freeN m g rule pick s))
          ↔ Cut3 δ g (freeN m g rule pick s) := by
        unfold CutTab Cut3
        simp only [boxTab_of_pos (hhigh s hs3 2), boxTab_of_pos (hhigh s hs3 0),
          boxTab_of_pos (hhigh s hs3 1)]
      rw [hiff]
      constructor
      · intro hc
        by_contra hlt
        exact hcmin s hs3 (by omega) hc
      · intro hle
        exact cut3_persist hδ0 hδ htr htc hcut hle
  · intro s hs hsel
    have hs3 : 3 ≤ s := by omega
    have e : ∀ u, 3 ≤ u → (histTab δ (freeH m g rule pick u) 2).2
        = U3 δ g (freeN m g rule pick u) 2 := by
      intro u hu
      simp only [histTab_free, boxTab_of_pos (hhigh u hu 2)]
    rw [e s hs3, e (s + 1) (by omega)]
    exact cut3_strict_change hδ0 hδ hg hg8 htr htc hcut hs hsel
  · intro s
    exact histWork_free m g rule pick hδ0 hδ hg hg8 hpick s hτ

/-! ### The open-loop bounds with the first cut time -/

/-- `v2separation_monitors` with the first cut time made explicit and the extra constants
of the `[0,1]` start added to the works: for every run (`MonGraphRun`) on the `m`-leaf
graph with `g = m^{-α}`, `m ≥ m₀`, the first count `tc ≥ 3` with `Cut3` and the first count
`τ` with `Stop3` satisfy `tc ≤ T`, `tc < τ` and the four two-sided bounds. -/
theorem v2separation_firstcut {δ α : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α < 1 / 2) :
    ∃ (m0 T : ℕ) (cτ Cτ cH CH C1 cF CF : ℝ), 0 < cτ ∧ 0 < cH ∧ 0 < C1 ∧ 0 < cF ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-α) →
      ∀ (rule : ℕ → ℕ → Bool) (N : ℕ → Fin 3 → ℕ) (S : ℕ → Fin 3 → ℝ) (sel : ℕ → Fin 3),
      MonGraphRun m g rule N S sel →
        0 < g ∧ g ≤ 1 / 8 ∧
        ∃ tc τ : ℕ, 3 ≤ tc ∧ tc ≤ T ∧ tc < τ ∧ Cut3 δ g (N tc) ∧
          (∀ s, 3 ≤ s → s < tc → ¬ Cut3 δ g (N s)) ∧
          Stop3 δ g (N τ) 0 ∧ (∀ s a, 3 ≤ s → s < τ → ¬ Stop3 δ g (N s) a) ∧
          cτ * ((m : ℝ) ^ (2 * α) * Real.log m ^ 2) ≤ τ ∧
          (τ : ℝ) ≤ Cτ * ((m : ℝ) ^ (2 * α) * Real.log m ^ 2) ∧
          cH * ((m : ℝ) ^ α * Real.log m) ≤ (N τ 2 : ℝ) - N tc 2 ∧
          (N τ 2 : ℝ) - N tc 2 ≤ CH * ((m : ℝ) ^ α * Real.log m) ∧
          (m : ℝ) ≤ (v2Work true m δ g rule N sel τ : ℝ) + 48 ∧
          (v2Work true m δ g rule N sel τ : ℝ) + 48 ≤ C1 * m ∧
          cF * ((m : ℝ) ^ (1 + α) * Real.log m) ≤ (v2Work false m δ g rule N sel τ : ℝ) + 21 ∧
          (v2Work false m δ g rule N sel τ : ℝ) + 21
            ≤ CF * ((m : ℝ) ^ (1 + α) * Real.log m) := by
  obtain ⟨T, g0, C, hg0, hC, H⟩ := v2separation_horizon hδ0 hδ
  obtain ⟨m1, cτ', Cτ', cH', CH', C1, C2, -, hcH', HM⟩ :=
    v2separation_monitors hδ0 hδ hα0 hα
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = max 8 (max (1 / g0) (36 * (1 + (T : ℝ)) / α)) := ⟨_, rfl⟩
  have hX8 : 8 ≤ X := by
    rw [hX]
    exact le_max_left _ _
  have hXg : 1 / g0 ≤ X := by
    rw [hX]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hXT : 36 * (1 + (T : ℝ)) / α ≤ X := by
    rw [hX]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hC1 : 0 < max C1 1 + 48 := by
    have := le_max_right C1 1
    linarith
  refine ⟨max m1 (max 3 ⌈X ^ (1 / α)⌉₊), T, 16 / 81 * α ^ 2, C * α ^ 2, α / 36,
    2 * Real.sqrt C * α, max C1 1 + 48, cH', C2 + 21, by positivity, by positivity, hC1,
    hcH', ?_⟩
  intro m hm g hgdef rule N S sel hrun
  subst hgdef
  have htr := hrun.trace
  have hm1' : m1 ≤ m := le_trans (le_max_left _ _) hm
  have hm3 : 3 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hmpos : (0 : ℝ) < m := by linarith
  have hXm : X ^ (1 / α) ≤ m := by
    have : ⌈X ^ (1 / α)⌉₊ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have hXa : X ≤ (m : ℝ) ^ α := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hXm hα0.le
    rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hα0.ne', Real.rpow_one] at h1
    exact h1
  have hℓ1 : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hmpos]
    have := Real.exp_one_lt_d9
    linarith
  have hgpos : 0 < (m : ℝ) ^ (-α) := Real.rpow_pos_of_pos hmpos _
  have hg8 : (m : ℝ) ^ (-α) ≤ 1 / 8 := by
    rw [Real.rpow_neg hmpos.le, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  obtain ⟨tc, τ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ :=
    H α hα0 m hmpos (by linarith) N sel htr
  have htcτ : tc < τ := h8 (by linarith)
  obtain ⟨-, tc0, τ0, htc0, htc0τ0, hno0, hstop0, -, -, -, -, hWs_lo, hWs_hi, hWf_lo, hWf_hi⟩ :=
    HM m hm1' _ rfl rule N S sel hrun
  have hout := fun k => v2_outputs hδ0 hδ hgpos hg8 htr m k
  -- the stopping count of `v2separation_monitors` is the first `Stop3` count
  have hττ : τ0 = τ := by
    have hS0 : Stop3 δ ((m : ℝ) ^ (-α)) (N τ0) 0 := by
      have hmem0 : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) := Set.mem_singleton _
      rw [← hstop0, (hout (τ0 - 3)).2.1] at hmem0
      have e : 3 + (τ0 - 3) = τ0 := by omega
      rw [e] at hmem0
      exact hmem0
    have hle : τ ≤ τ0 := by
      by_contra hlt
      exact h7 τ0 0 (by omega) (by omega) hS0
    have hge : τ0 ≤ τ := by
      by_contra hlt
      have hemp := hno0 (τ - 3) (by omega)
      have e : 3 + (τ - 3) = τ := by omega
      have hmem : (0 : Fin 3) ∈ {a | Stop3 δ ((m : ℝ) ^ (-α)) (N (3 + (τ - 3))) a} := by
        rw [e]
        exact h6
      rw [← (hout (τ - 3)).2.1, hemp] at hmem
      exact (Set.mem_empty_iff_false _).mp hmem
    omega
  rw [hττ] at hWs_lo hWs_hi hWf_lo hWf_hi
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (m : ℝ) ^ α := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log m := ⟨_, rfl⟩
  rw [← ha, ← hℓ] at h11 h12
  rw [← ha] at hXa
  have hℓ1' : 1 ≤ ℓ := by
    rw [hℓ]
    exact hℓ1
  have ha8 : 8 ≤ a := by linarith
  have hαa : 36 * (1 + (T : ℝ)) ≤ α * a := by
    have := hXT.trans hXa
    rw [div_le_iff₀ hα0] at this
    linarith
  have hP : α * a ≤ α * a * ℓ := by
    nlinarith [mul_nonneg (mul_nonneg hα0.le (by linarith : (0 : ℝ) ≤ a))
      (by linarith : (0 : ℝ) ≤ ℓ - 1)]
  have hHlo : α / 36 * (a * ℓ) ≤ (N τ 2 : ℝ) - N tc 2 := by linarith
  have hHhi : (N τ 2 : ℝ) - N tc 2 ≤ 2 * Real.sqrt C * α * (a * ℓ) := by linarith
  rw [ha, hℓ] at hHlo hHhi
  have hY : 1 ≤ (m : ℝ) ^ (1 + α) * Real.log m := by
    have h1' : (1 : ℝ) ≤ (m : ℝ) ^ (1 + α) := Real.one_le_rpow (by linarith) (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr h1') (sub_nonneg.mpr hℓ1)]
  refine ⟨hgpos, hg8, tc, τ, h1, h2, htcτ, h3, h4, h6, h7, le_trans (le_of_eq (by ring)) h9,
    le_trans h10 (le_of_eq (by ring)), hHlo, hHhi, by linarith, ?_, ?_, ?_⟩
  · have hmx : C1 ≤ max C1 1 := le_max_left _ _
    have hmul : C1 * (m : ℝ) ≤ max C1 1 * m := mul_le_mul_of_nonneg_right hmx hmpos.le
    have e : (max C1 1 + 48) * (m : ℝ) = max C1 1 * m + 48 * m := by ring
    rw [e]
    linarith
  · have e : cH' * ((m : ℝ) ^ (1 + α) * Real.log m)
        = cH' * (m : ℝ) ^ (1 + α) * Real.log m := by ring
    rw [e]
    linarith
  · have e : (C2 + 21) * ((m : ℝ) ^ (1 + α) * Real.log m)
        = C2 * (m : ℝ) ^ (1 + α) * Real.log m + 21 * ((m : ℝ) ^ (1 + α) * Real.log m) := by
      ring
    rw [e]
    linarith

/-! ### The final statements -/

/-- All conclusions of `thm:v2separation` for one closed-loop run, with the orders of
`τ`, `H` and `W_full` supplied as the real numbers `Oτ`, `OH`, `OF`. -/
structure SeparationBounds (m : ℕ) (δ g : ℝ) (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3)
    (tc τ : ℕ) (cτ Cτ cH CH C1 cF CF Oτ OH OF : ℝ) : Prop where
  /-- Coupling of the two closed loops, first cut time, common stopping time `τ` and
  recommendation `A`, strict post-cut changes, charging of the forced observations. -/
  run : ClosedLoopRun m δ g rule pick tc τ
  /-- The cut precedes certification. -/
  cut_lt_stop : tc < τ
  /-- `eq:v2taum`, lower bound. -/
  tau_lower : cτ * Oτ ≤ τ
  /-- `eq:v2taum`, upper bound. -/
  tau_upper : (τ : ℝ) ≤ Cτ * Oτ
  /-- `eq:v2hm`, lower bound: `H` is the number of observations of `C` strictly after the
  first cut time and through `τ`. -/
  H_lower : cH * OH
    ≤ (cntA (freeH m g rule pick τ) 2 : ℝ) - cntA (freeH m g rule pick tc) 2
  /-- `eq:v2hm`, upper bound. -/
  H_upper : (cntA (freeH m g rule pick τ) 2 : ℝ) - cntA (freeH m g rule pick tc) 2
    ≤ CH * OH
  /-- `eq:v2wselective`, lower bound. -/
  sel_lower : (m : ℝ) ≤ histWork true m δ (g / 2) rule (freeH m g rule pick τ)
  /-- `eq:v2wselective`, upper bound. -/
  sel_upper : (histWork true m δ (g / 2) rule (freeH m g rule pick τ) : ℝ) ≤ C1 * m
  /-- `eq:v2wfull`, lower bound. -/
  full_lower : cF * OF ≤ histWork false m δ (g / 2) rule (freeH m g rule pick τ)
  /-- `eq:v2wfull`, upper bound. -/
  full_upper : (histWork false m δ (g / 2) rule (freeH m g rule pick τ) : ℝ) ≤ CF * OF

/-- **Theorem `thm:v2separation` (Root-PUCT work separation from uninformative
initialization), literal form.**  Fix `δ ∈ (0, 1/2]` and `α ∈ (0, 1/2)`.  There are a size
`m₀`, a count `T` and constants, all depending on `δ, α` only, such that for every
`m ≥ m₀`, with `g = m^{-α}` and `ε = g/2`, for every path rule and every tie-breaking, the
root-PUCT controller run in closed loop with the selective and with the full monitor on the
`m`-leaf graph, from `[0,1]` at all three terminals, satisfies `SeparationBounds` with first
cut time `tc ≤ T`, stopping time `τ`, and orders `m^{2α} log² m`, `m^α log m`,
`m^{1+α} log m`. -/
theorem v2separation_literal {δ α : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α < 1 / 2) :
    ∃ (m0 T : ℕ) (cτ Cτ cH CH C1 cF CF : ℝ), 0 < cτ ∧ 0 < cH ∧ 0 < C1 ∧ 0 < cF ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-α) →
      ∀ (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3), IsPuctPick pick →
      ∃ tc τ : ℕ, tc ≤ T ∧
        SeparationBounds m δ g rule pick tc τ cτ Cτ cH CH C1 cF CF
          ((m : ℝ) ^ (2 * α) * Real.log m ^ 2) ((m : ℝ) ^ α * Real.log m)
          ((m : ℝ) ^ (1 + α) * Real.log m) := by
  obtain ⟨m0, T, cτ, Cτ, cH, CH, C1, cF, CF, p1, p2, p3, p4, H⟩ :=
    v2separation_firstcut hδ0 hδ hα0 hα
  refine ⟨m0, T, cτ, Cτ, cH, CH, C1, cF, CF, p1, p2, p3, p4, ?_⟩
  intro m hm g hg rule pick hpick
  obtain ⟨hgpos, hg8, tc, τ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15⟩ := H m hm g hg rule _ _ _ (free_graphRun m g rule pick hpick)
  have hτ3 : 3 ≤ τ := by omega
  have hrunF := closedLoopRun_of_first_times m g rule pick hδ0 hδ hgpos hg8 hpick a1 a4 a5
    hτ3 a6 a7
  have e1 : (histWork true m δ (g / 2) rule (freeH m g rule pick τ) : ℝ)
      = (v2Work true m δ g rule (freeN m g rule pick) (freeSel m g rule pick) τ : ℝ) + 48 := by
    rw [hrunF.work true]
    simp
  have e2 : (histWork false m δ (g / 2) rule (freeH m g rule pick τ) : ℝ)
      = (v2Work false m δ g rule (freeN m g rule pick) (freeSel m g rule pick) τ : ℝ) + 21 := by
    rw [hrunF.work false]
    simp
  refine ⟨tc, τ, a2, ⟨hrunF, a3, a8, a9, a10, a11, ?_, ?_, ?_, ?_⟩⟩
  · rw [e1]
    exact a12
  · rw [e1]
    exact a13
  · rw [e2]
    exact a14
  · rw [e2]
    exact a15

/-- **Corollary `cor:v2quarter` (One explicit polynomial instance), literal form.**  The
case `α = 1/4` of `v2separation_literal`: `τ = Θ(m^{1/2} log² m)`, `W_selective = Θ(m)`,
`W_full = Θ(m^{5/4} log m)`, and the work ratio `W_full / W_selective` is
`Θ(m^{1/4} log m)`, while the two closed loops coincide exactly (`SeparationBounds.run`). -/
theorem v2quarter_literal {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ (m0 T : ℕ) (cτ Cτ cH CH C1 cF CF cR CR : ℝ),
      0 < cτ ∧ 0 < cH ∧ 0 < C1 ∧ 0 < cF ∧ 0 < cR ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-(1 / 4 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3), IsPuctPick pick →
      ∃ tc τ : ℕ, tc ≤ T ∧
        SeparationBounds m δ g rule pick tc τ cτ Cτ cH CH C1 cF CF
          ((m : ℝ) ^ (1 / 2 : ℝ) * Real.log m ^ 2) ((m : ℝ) ^ (1 / 4 : ℝ) * Real.log m)
          ((m : ℝ) ^ (5 / 4 : ℝ) * Real.log m) ∧
        cR * ((m : ℝ) ^ (1 / 4 : ℝ) * Real.log m)
          ≤ (histWork false m δ (g / 2) rule (freeH m g rule pick τ) : ℝ)
            / histWork true m δ (g / 2) rule (freeH m g rule pick τ) ∧
        (histWork false m δ (g / 2) rule (freeH m g rule pick τ) : ℝ)
            / histWork true m δ (g / 2) rule (freeH m g rule pick τ)
          ≤ CR * ((m : ℝ) ^ (1 / 4 : ℝ) * Real.log m) := by
  obtain ⟨m0, T, cτ, Cτ, cH, CH, C1, cF, CF, p1, p2, p3, p4, H⟩ :=
    v2separation_literal hδ0 hδ (α := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨max m0 3, T, cτ, Cτ, cH, CH, C1, cF, CF, cF / C1, CF, p1, p2, p3, p4,
    div_pos p4 p3, ?_⟩
  intro m hm g hg rule pick hpick
  obtain ⟨tc, τ, htcT, hB⟩ := H m (le_trans (le_max_left _ _) hm) g hg rule pick hpick
  have e1 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
  rw [e1, e2] at hB
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hℓ1 : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hmpos]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (m : ℝ) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 < y := by
    rw [hy]
    exact Real.rpow_pos_of_pos hmpos _
  have h54 : (m : ℝ) ^ (5 / 4 : ℝ) = m * y := by
    rw [hy, ← e2, Real.rpow_add hmpos, Real.rpow_one]
  have hsl := hB.sel_lower
  have hsu := hB.sel_upper
  have hfl := hB.full_lower
  have hfu := hB.full_upper
  rw [h54] at hfl hfu
  refine ⟨tc, τ, htcT, hB, ?_, ?_⟩
  all_goals rw [← hy]
  all_goals
    obtain ⟨Ws, hWs⟩ : ∃ Ws : ℝ,
      Ws = (histWork true m δ (g / 2) rule (freeH m g rule pick τ) : ℝ) := ⟨_, rfl⟩
    obtain ⟨Wf, hWf⟩ : ∃ Wf : ℝ,
      Wf = (histWork false m δ (g / 2) rule (freeH m g rule pick τ) : ℝ) := ⟨_, rfl⟩
    rw [← hWs] at hsl hsu
    rw [← hWf] at hfl hfu
    rw [← hWs, ← hWf]
    have hWs0 : 0 < Ws := by linarith
    have hyℓ : 0 ≤ y * Real.log m := mul_nonneg hy0.le (by linarith)
  · rw [le_div_iff₀ hWs0]
    have hK : 0 ≤ cF / C1 * (y * Real.log m) := mul_nonneg (div_pos p4 p3).le hyℓ
    have hc : cF / C1 * C1 = cF := div_mul_cancel₀ cF p3.ne'
    calc cF / C1 * (y * Real.log m) * Ws
        ≤ cF / C1 * (y * Real.log m) * (C1 * m) := mul_le_mul_of_nonneg_left hsu hK
      _ = cF / C1 * C1 * (m * y * Real.log m) := by ring
      _ = cF * (m * y * Real.log m) := by rw [hc]
      _ ≤ Wf := hfl
  · rw [div_le_iff₀ hWs0]
    have hpos : 0 < (m : ℝ) * y * Real.log m := mul_pos (mul_pos hmpos hy0) (by linarith)
    have hCF : 0 ≤ CF := by
      by_contra hneg
      have h1 := mul_neg_of_neg_of_pos (not_le.mp hneg) hpos
      have h2 := mul_pos p4 hpos
      linarith
    calc Wf ≤ CF * (m * y * Real.log m) := hfu
      _ = CF * (y * Real.log m) * m := by ring
      _ ≤ CF * (y * Real.log m) * Ws := mul_le_mul_of_nonneg_left hsl (mul_nonneg hCF hyℓ)

end

end LiteralE5

end JointRootCert
