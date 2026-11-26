/-
Corollary `cor:v35poly` (Polynomial accuracy dependence at fixed depth), the
oracle-substitution clause composed with the horizon clause, using
`thm:v35horizon` and the first sentence of `thm:adaptive-oracle-coupling`.

* `Search`, `Search.controller`: recursive PUCT on a finite DAG (rank function), with a
  backup rule and a tie-breaking rule, as a `Representation.Controller` whose history is the
  list of (terminal, reward) observations.  The tie-breaking rule is the controller tape.
* `refMonitor`: the exact-regret stopping monitor (running Hoeffding boxes and the exact
  rectangular certificate of every root action) as a `Representation.OracleImpl`.
* `Search.puctRun`, `Search.ref_answer`: the trajectory of this controller is a `PUCTRun`,
  and the monitor's replies are the exact certificates assumed by `puct_poly_horizon_full`.
* `puct_controller_horizon`: `puct_poly_horizon_full` for this concrete search and monitor,
  with no hypothesis on the monitor.
* `dcMonitor`, `dcMonitor_answer`: the dual-cover index (segment trees and implemented heaps
  of `DualCoverFinal`) as a second `OracleImpl`, with the same replies on every history.
* `v35poly_oracle_substitution`, `v35poly_dual_cover`: the composed statement.
-/
import JointRootCert.Completions3
import JointRootCert.DualCoverFinal

namespace JointRootCert
namespace LiteralE3

open Finset MeasureTheory
open JointRootCert.Representation
open scoped Classical

noncomputable section

/-! ## Counting along a sequence of growing lists -/

/-- If `L (s+1) = L s ++ [r s]` and `L 0 = []`, counting in the list `L s` is counting over
the steps `i < s`. -/
lemma countP_seq {α : Type*} (L : ℕ → List α) (r : ℕ → α) (h0 : L 0 = [])
    (hs : ∀ s, L (s + 1) = L s ++ [r s]) (p : α → Prop) [DecidablePred p] (s : ℕ) :
    (L s).countP (fun a => decide (p a)) = stepCount (fun i => p (r i)) s := by
  induction s with
  | zero => rw [h0]; simp [stepCount]
  | succ s ih =>
    rw [hs, List.countP_append, ih]
    by_cases hp : p (r s)
    · rw [stepCount_succ_of_pos (p := fun i => p (r i)) hp]; simp [hp]
    · rw [stepCount_succ_of_neg (p := fun i => p (r i)) hp]; simp [hp]

/-- First index at which `p` holds (`0` if never). -/
def firstTime (p : ℕ → Prop) : ℕ := if h : ∃ n, p n then Nat.find h else 0

lemma firstTime_spec {p : ℕ → Prop} (h : ∃ n, p n) :
    p (firstTime p) ∧ ∀ n, p n → firstTime p ≤ n := by
  unfold firstTime
  rw [dite_eq_left h]
  exact ⟨Nat.find_spec h, fun n hn => Nat.find_min' h hn⟩

/-! ## Runs that read each terminal's reward tape in order -/

section TapeRun

variable {Z : Type*}

/-- Number of observations of terminal `z` in a history. -/
def cntZ (z : Z) (h : List (Z × ℝ)) : ℕ := h.countP (fun p => decide (p.1 = z))

lemma cntZ_append_self (h : List (Z × ℝ)) (z : Z) (x : ℝ) :
    cntZ z (h ++ [(z, x)]) = cntZ z h + 1 := by
  simp [cntZ, List.countP_append]

lemma cntZ_append_ne (h : List (Z × ℝ)) {z z' : Z} (x : ℝ) (hne : z' ≠ z) :
    cntZ z (h ++ [(z', x)]) = cntZ z h := by
  simp [cntZ, List.countP_append, hne]

/-- The history after `n` rollouts when the next terminal is `nxt h` and the reward revealed
for terminal `z` is the next unread entry `x z (n_z)` of its tape. -/
def tapeRun (nxt : List (Z × ℝ) → Z) (x : Z → ℕ → ℝ) : ℕ → List (Z × ℝ)
  | 0 => []
  | n + 1 =>
    tapeRun nxt x n ++
      [(nxt (tapeRun nxt x n), x (nxt (tapeRun nxt x n))
        (cntZ (nxt (tapeRun nxt x n)) (tapeRun nxt x n)))]

/-- The rollout-indexed reward table of `Representation.history` induced by per-terminal tapes
along a sequence of histories: at rollout `n`, terminal `z` reveals its next unread entry. -/
def tapeTable (x : Z → ℕ → ℝ) (hist : ℕ → List (Z × ℝ)) : ℕ → Z → ℝ :=
  fun n z => x z (cntZ z (hist n))

variable {R Ωc : Type*}

/-- The run of a `Representation.Controller` against an oracle `o` on per-terminal tapes. -/
def ctrlRun (o : List (Z × ℝ) → R) (ctrl : Controller Z ℝ R Ωc) (w : Ωc) (x : Z → ℕ → ℝ) :
    ℕ → List (Z × ℝ) :=
  tapeRun (fun h => ctrl.next h (o h) w) x

/-- First rollout count at which the controller's stopping bit is set (`0` if never). -/
def stopIdx (o : List (Z × ℝ) → R) (ctrl : Controller Z ℝ R Ωc) (w : Ωc) (x : Z → ℕ → ℝ) : ℕ :=
  firstTime (fun n => ctrl.stop (ctrlRun o ctrl w x n) (o (ctrlRun o ctrl w x n)) = true)

/-- The oracle reply at the stopping index. -/
def finalReply (o : List (Z × ℝ) → R) (ctrl : Controller Z ℝ R Ωc) (w : Ωc)
    (x : Z → ℕ → ℝ) : R :=
  o (ctrlRun o ctrl w x (stopIdx o ctrl w x))

/-- `ctrlRun` is the trajectory `Representation.history` for the reward table that reveals
tape entries in order. -/
theorem history_tapeTable (o : List (Z × ℝ) → R) (ctrl : Controller Z ℝ R Ωc) (w : Ωc)
    (x : Z → ℕ → ℝ) (n : ℕ) :
    history o ctrl (tapeTable x (ctrlRun o ctrl w x)) w n = ctrlRun o ctrl w x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [history, ih]
    rfl

/-- ... and it is the only sequence of histories with this property. -/
theorem history_tapeTable_unique (o : List (Z × ℝ) → R) (ctrl : Controller Z ℝ R Ωc) (w : Ωc)
    (x : Z → ℕ → ℝ) (hist : ℕ → List (Z × ℝ))
    (hfix : ∀ n, hist n = history o ctrl (tapeTable x hist) w n) :
    ∀ n, hist n = ctrlRun o ctrl w x n := by
  intro n
  induction n with
  | zero => rw [hfix 0]; rfl
  | succ n ih =>
    have h1 := hfix (n + 1)
    rw [history, ← hfix n] at h1
    rw [h1]
    simp only [tapeTable]
    rw [ih]
    rfl

/-- If the run stops, `Representation.stopTime` is `stopIdx`. -/
theorem stopTime_eq_stopIdx (o : List (Z × ℝ) → R) (ctrl : Controller Z ℝ R Ωc) (w : Ωc)
    (x : Z → ℕ → ℝ)
    (hex : ∃ n, ctrl.stop (ctrlRun o ctrl w x n) (o (ctrlRun o ctrl w x n)) = true) :
    stopTime o ctrl (tapeTable x (ctrlRun o ctrl w x)) w = (stopIdx o ctrl w x : ℕ∞) := by
  have hst : ∀ n, stoppedAt o ctrl (tapeTable x (ctrlRun o ctrl w x)) w n ↔
      ctrl.stop (ctrlRun o ctrl w x n) (o (ctrlRun o ctrl w x n)) = true := by
    intro n
    unfold stoppedAt replyAt
    rw [history_tapeTable]
  obtain ⟨hs, hmin⟩ := firstTime_spec hex
  unfold stopTime
  apply le_antisymm
  · exact sInf_le ⟨stopIdx o ctrl w x, (hst _).mpr hs, rfl⟩
  · refine le_sInf ?_
    rintro _ ⟨m, hm, rfl⟩
    have : stopIdx o ctrl w x ≤ m := hmin m ((hst m).mp hm)
    show ((stopIdx o ctrl w x : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞)
    exact_mod_cast this

/-- **Coupling on tapes.**  If a second oracle agrees with the first on every history reached
by the first run, then histories, replies, stopping index and final reply coincide. -/
theorem tape_coupling (o o' : List (Z × ℝ) → R) (ctrl : Controller Z ℝ R Ωc) (w : Ωc)
    (x : Z → ℕ → ℝ) (h : ∀ n, o' (ctrlRun o ctrl w x n) = o (ctrlRun o ctrl w x n)) :
    (∀ n, ctrlRun o' ctrl w x n = ctrlRun o ctrl w x n) ∧
    (∀ n, o' (ctrlRun o' ctrl w x n) = o (ctrlRun o ctrl w x n)) ∧
    stopIdx o' ctrl w x = stopIdx o ctrl w x ∧
    finalReply o' ctrl w x = finalReply o ctrl w x := by
  have hrun : ∀ n, ctrlRun o' ctrl w x n = ctrlRun o ctrl w x n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have h' := h n
      unfold ctrlRun at ih h' ⊢
      simp only [tapeRun]
      rw [ih, h']
  have hrep : ∀ n, o' (ctrlRun o' ctrl w x n) = o (ctrlRun o ctrl w x n) := fun n => by
    rw [hrun n, h n]
  have hidx : stopIdx o' ctrl w x = stopIdx o ctrl w x := by
    unfold stopIdx
    congr 1
    funext n
    rw [hrun n, h n]
  refine ⟨hrun, hrep, hidx, ?_⟩
  unfold finalReply
  rw [hidx, hrep]

end TapeRun

/-! ## The exact-regret monitor on running Hoeffding boxes -/

section Monitor

lemma runLower_succ (c β : ℕ → ℝ) (n : ℕ) :
    runLower c β (n + 1) = max (runLower c β n) (c (n + 1) - β (n + 1)) := by
  unfold runLower
  apply le_antisymm
  · refine sup'_le _ _ (fun k hk => ?_)
    by_cases hkn : k = n + 1
    · subst hkn
      rw [ite_eq_right (Nat.succ_ne_zero n)]
      exact le_max_right _ _
    · refine le_trans ?_ (le_max_left _ _)
      exact le_sup' (fun k => if k = 0 then 0 else c k - β k)
        (mem_range.mpr (by have := mem_range.mp hk; omega))
  · refine max_le (sup'_le _ _ (fun k hk =>
      le_sup' (fun k => if k = 0 then 0 else c k - β k)
        (mem_range.mpr (by have := mem_range.mp hk; omega)))) ?_
    refine le_trans (le_of_eq ?_) (le_sup' (fun k => if k = 0 then 0 else c k - β k)
      (mem_range.mpr (Nat.lt_succ_self (n + 1))))
    simp

lemma runUpper_succ (c β : ℕ → ℝ) (n : ℕ) :
    runUpper c β (n + 1) = min (runUpper c β n) (c (n + 1) + β (n + 1)) := by
  unfold runUpper
  apply le_antisymm
  · refine le_min (le_inf' _ _ (fun k hk =>
      inf'_le (fun k => if k = 0 then 1 else c k + β k)
        (mem_range.mpr (by have := mem_range.mp hk; omega)))) ?_
    refine le_trans (inf'_le (fun k => if k = 0 then 1 else c k + β k)
      (mem_range.mpr (Nat.lt_succ_self (n + 1)))) (le_of_eq ?_)
    simp
  · refine le_inf' _ _ (fun k hk => ?_)
    by_cases hkn : k = n + 1
    · subst hkn
      rw [ite_eq_right (Nat.succ_ne_zero n)]
      exact min_le_right _ _
    · refine le_trans (min_le_left _ _) ?_
      exact inf'_le (fun k => if k = 0 then 1 else c k + β k)
        (mem_range.mpr (by have := mem_range.mp hk; omega))

/-- Per-terminal statistics kept by the monitor: number of samples, their sum, and the
endpoints of the running intersection of the clipped confidence intervals. -/
structure Stat where
  n : ℕ
  sum : ℝ
  lo : ℝ
  hi : ℝ

/-- Before any sample the interval is `[0, 1]`. -/
def Stat.init : Stat := ⟨0, 0, 0, 1⟩

/-- A new sample `x`: update the count and the sum, and intersect with the new interval
`mean ± β (count)`. -/
def Stat.upd (β : ℕ → ℝ) (s : Stat) (x : ℝ) : Stat :=
  ⟨s.n + 1, s.sum + x,
    max s.lo (((s.n + 1 : ℕ) : ℝ)⁻¹ * (s.sum + x) - β (s.n + 1)),
    min s.hi (((s.n + 1 : ℕ) : ℝ)⁻¹ * (s.sum + x) + β (s.n + 1))⟩

/-- The statistics after reading the first `k` entries of a tape. -/
def statOf (β : ℕ → ℝ) (xz : ℕ → ℝ) (k : ℕ) : Stat :=
  ⟨k, ∑ i ∈ range k, xz i,
    runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, xz i) β k,
    runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, xz i) β k⟩

lemma statOf_zero (β : ℕ → ℝ) (xz : ℕ → ℝ) : statOf β xz 0 = Stat.init := by
  simp [statOf, Stat.init, runLower, runUpper]

lemma statOf_succ (β : ℕ → ℝ) (xz : ℕ → ℝ) (k : ℕ) :
    (statOf β xz k).upd β (xz k) = statOf β xz (k + 1) := by
  unfold statOf Stat.upd
  simp only [Stat.mk.injEq]
  refine ⟨trivial, (sum_range_succ _ _).symm, ?_, ?_⟩
  · rw [runLower_succ, sum_range_succ]
  · rw [runUpper_succ, sum_range_succ]

variable {Z : Type*} [DecidableEq Z]

/-- The monitor's update on one observation `(z, x)`. -/
def boxStep (β : ℕ → ℝ) (s : Z → Stat) (p : Z × ℝ) : Z → Stat :=
  Function.update s p.1 ((s p.1).upd β p.2)

/-- The monitor's statistics after a history. -/
def boxOf (β : ℕ → ℝ) (h : List (Z × ℝ)) : Z → Stat :=
  h.foldl (boxStep β) (fun _ => Stat.init)

/-- Along a run that reads tapes in order, the monitor's statistics for `z` are those of the
first `n_z` entries of the tape of `z`. -/
lemma boxOf_tapeRun (β : ℕ → ℝ) (nxt : List (Z × ℝ) → Z) (x : Z → ℕ → ℝ) (n : ℕ) (z : Z) :
    boxOf β (tapeRun nxt x n) z = statOf β (x z) (cntZ z (tapeRun nxt x n)) := by
  induction n with
  | zero =>
    show Stat.init = statOf β (x z) (cntZ z [])
    rw [show cntZ z ([] : List (Z × ℝ)) = 0 from rfl, statOf_zero]
  | succ n ih =>
    have e : tapeRun nxt x (n + 1) = tapeRun nxt x n ++
        [(nxt (tapeRun nxt x n), x (nxt (tapeRun nxt x n))
          (cntZ (nxt (tapeRun nxt x n)) (tapeRun nxt x n)))] := rfl
    have hb : boxOf β (tapeRun nxt x (n + 1)) = boxStep β (boxOf β (tapeRun nxt x n))
        (nxt (tapeRun nxt x n), x (nxt (tapeRun nxt x n))
          (cntZ (nxt (tapeRun nxt x n)) (tapeRun nxt x n))) := by
      rw [e]
      unfold boxOf
      rw [List.foldl_append]
      rfl
    rw [hb, e]
    unfold boxStep
    by_cases hz : z = nxt (tapeRun nxt x n)
    · subst hz
      rw [Function.update_self, cntZ_append_self]
      have ih' : boxOf β (tapeRun nxt x n) (nxt (tapeRun nxt x n)) =
          statOf β (x (nxt (tapeRun nxt x n)))
            (cntZ (nxt (tapeRun nxt x n)) (tapeRun nxt x n)) := ih
      rw [ih']
      exact statOf_succ β _ _
    · rw [Function.update_of_ne hz, cntZ_append_ne _ _ (Ne.symm hz)]
      exact ih

variable [Fintype Z] [Nonempty Z] {A : Type*}

/-- **The exact-regret monitor as an oracle implementation.**  State: the per-terminal
statistics.  Reply: for every root action the exact minimum-regret certificate of its support
over the current box (`exactCert`, i.e. `rectCert` for a proper support and `0` for a full
one). -/
def refMonitor (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (β : ℕ → ℝ) :
    OracleImpl (Z → Stat) (Z × ℝ) (A → ℝ) where
  init := fun _ => Stat.init
  step := boxStep β
  reply := fun s a => exactCert (supp a) (hne a) (fun z => (s z).lo) (fun z => (s z).hi)

omit [Nonempty Z] in
lemma refMonitor_answer (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (β : ℕ → ℝ)
    (h : List (Z × ℝ)) :
    (refMonitor supp hne β).answer h = fun a => exactCert (supp a) (hne a)
      (fun z => (boxOf β h z).lo) (fun z => (boxOf β h z).hi) := rfl

/-- The recommendation read off a reply: an action whose certificate is at most `ε` (chosen
by `Classical.epsilon`; any fixed selection rule would do). -/
def recOf [Nonempty A] (ε : ℝ) (r : A → ℝ) : A := Classical.epsilon (fun a => r a ≤ ε)

end Monitor

/-! ## Recursive PUCT as a deterministic function of the observation history -/

section Walk

variable {V E : Type*} [Fintype E] (src tgt : E → V) (c : V → E)

/-- The vertices visited from `v` when following the choices `c`, with fuel `k`. -/
def walk : ℕ → V → List V
  | 0, v => [v]
  | k + 1, v => if (outEdges src v).Nonempty then v :: walk k (tgt (c v)) else [v]

/-- The last vertex of `walk`. -/
def endV : ℕ → V → V
  | 0, v => v
  | k + 1, v => if (outEdges src v).Nonempty then endV k (tgt (c v)) else v

lemma walk_head (k : ℕ) (v : V) : v ∈ walk src tgt c k v := by
  cases k with
  | zero => simp [walk]
  | succ k =>
    simp only [walk]
    split_ifs <;> simp

variable {src tgt c} {rk : V → ℕ}

lemma no_out_of_rk_zero (hrk : ∀ e, rk (tgt e) < rk (src e)) {u : V} (h : rk u = 0) :
    ¬ (outEdges src u).Nonempty := by
  rintro ⟨e, he⟩
  have h1 := mem_outEdges.mp he
  have h2 := hrk e
  rw [h1] at h2
  omega

lemma walk_step (hrk : ∀ e, rk (tgt e) < rk (src e))
    (hc : ∀ v, (outEdges src v).Nonempty → src (c v) = v) :
    ∀ k u, rk u ≤ k → ∀ v, v ∈ walk src tgt c k u → (outEdges src v).Nonempty →
      tgt (c v) ∈ walk src tgt c k u := by
  intro k
  induction k with
  | zero =>
    intro u hu v hv hne
    simp only [walk, List.mem_singleton] at hv
    subst hv
    exact absurd hne (no_out_of_rk_zero hrk (by omega))
  | succ k ih =>
    intro u hu v hv hne
    simp only [walk] at hv ⊢
    by_cases hu' : (outEdges src u).Nonempty
    · rw [ite_eq_left hu'] at hv ⊢
      have hlt : rk (tgt (c u)) ≤ k := by
        have := hrk (c u)
        rw [hc u hu'] at this
        omega
      rcases List.mem_cons.mp hv with h1 | h1
      · subst h1
        exact List.mem_cons_of_mem _ (walk_head src tgt c k _)
      · exact List.mem_cons_of_mem _ (ih _ hlt v h1 hne)
    · rw [ite_eq_right hu', List.mem_singleton] at hv
      subst hv
      exact absurd hne hu'

lemma endV_sink (hrk : ∀ e, rk (tgt e) < rk (src e))
    (hc : ∀ v, (outEdges src v).Nonempty → src (c v) = v) :
    ∀ k u, rk u ≤ k → ¬ (outEdges src (endV src tgt c k u)).Nonempty := by
  intro k
  induction k with
  | zero =>
    intro u hu
    show ¬ (outEdges src u).Nonempty
    exact no_out_of_rk_zero hrk (by omega)
  | succ k ih =>
    intro u hu
    simp only [endV]
    by_cases hu' : (outEdges src u).Nonempty
    · rw [ite_eq_left hu']
      have hlt : rk (tgt (c u)) ≤ k := by
        have := hrk (c u)
        rw [hc u hu'] at this
        omega
      exact ih _ hlt
    · rw [ite_eq_right hu']
      exact hu'

lemma endV_mem : ∀ k u, endV src tgt c k u ∈ walk src tgt c k u := by
  intro k
  induction k with
  | zero => intro u; simp [walk, endV]
  | succ k ih =>
    intro u
    simp only [walk, endV]
    by_cases hu' : (outEdges src u).Nonempty
    · rw [ite_eq_left hu', ite_eq_left hu']
      exact List.mem_cons_of_mem _ (ih _)
    · rw [ite_eq_right hu', ite_eq_right hu']
      simp

lemma endV_eq_of_mem (hrk : ∀ e, rk (tgt e) < rk (src e))
    (hc : ∀ v, (outEdges src v).Nonempty → src (c v) = v) :
    ∀ k u, rk u ≤ k → ∀ v, v ∈ walk src tgt c k u → ¬ (outEdges src v).Nonempty →
      endV src tgt c k u = v := by
  intro k
  induction k with
  | zero =>
    intro u hu v hv hne
    simp only [walk, List.mem_singleton] at hv
    subst hv
    rfl
  | succ k ih =>
    intro u hu v hv hne
    simp only [walk] at hv
    simp only [endV]
    by_cases hu' : (outEdges src u).Nonempty
    · rw [ite_eq_left hu'] at hv ⊢
      have hlt : rk (tgt (c u)) ≤ k := by
        have := hrk (c u)
        rw [hc u hu'] at this
        omega
      rcases List.mem_cons.mp hv with h1 | h1
      · subst h1
        exact absurd hu' hne
      · exact ih _ hlt v h1 hne
    · rw [ite_eq_right hu', List.mem_singleton] at hv
      rw [ite_eq_right hu']
      exact hv.symm

end Walk

section Pick

variable {E : Type*}

/-- Tie-broken maximiser of `f` over `A`.  `tie` is the tie-breaking rule: it is shown the set
of maximisers and its choice is followed whenever it lies in that set; otherwise a fixed
maximiser is taken. -/
def pickMax (tie : Finset E → E) (A : Finset E) (f : E → ℝ) : E :=
  if tie (A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e)) ∈ A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e)
  then tie (A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e))
  else if h : (A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e)).Nonempty then h.choose
  else tie (A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e))

lemma pickMax_mem (tie : Finset E → E) {A : Finset E} (f : E → ℝ) (hA : A.Nonempty) :
    pickMax tie A f ∈ A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e) := by
  have hB : (A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e)).Nonempty := by
    obtain ⟨e, he, hmax⟩ := A.exists_max_image f hA
    exact ⟨e, mem_filter.mpr ⟨he, hmax⟩⟩
  unfold pickMax
  split_ifs with h1
  · exact h1
  · exact hB.choose_spec

lemma pickMax_spec (tie : Finset E → E) {A : Finset E} (f : E → ℝ) (hA : A.Nonempty) :
    pickMax tie A f ∈ A ∧ ∀ e' ∈ A, f e' ≤ f (pickMax tie A f) :=
  mem_filter.mp (pickMax_mem tie f hA)

/-- Clip to `[0, 1]`. -/
def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- Mean of the clipped entries (`0` for the empty list). -/
def clipMean (l : List ℝ) : ℝ := if l = [] then 0 else (l.map clip01).sum / l.length

lemma clipMean_mem (l : List ℝ) : 0 ≤ clipMean l ∧ clipMean l ≤ 1 := by
  unfold clipMean
  split_ifs with h
  · exact ⟨le_rfl, zero_le_one⟩
  · have hpos : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.mpr h
    have h0 : 0 ≤ (l.map clip01).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact le_max_left _ _)
    have h1 : (l.map clip01).sum ≤ l.length := by
      have := List.sum_le_length_nsmul (l.map clip01) 1 (by
        intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        exact max_le zero_le_one (min_le_left _ _))
      simpa using this
    exact ⟨div_nonneg h0 hpos.le, (div_le_one hpos).mpr h1⟩

end Pick

/-- **Data of a recursive PUCT search.**  A graph (`src`, `tgt`, `root`), edge weights `lam`,
a rank function `rk` witnessing acyclicity, the terminal `leaf v` read at a sink `v`, and the
backup rule `bk`: the value `Q_e` as a function of the past simulations (each recorded as its
selection function and its reward). -/
structure Search (V E Z : Type*) where
  src : E → V
  tgt : E → V
  root : V
  lam : E → ℝ
  rk : V → ℕ
  leaf : V → Z
  bk : List ((V → E) × ℝ) → E → ℝ

namespace Search

variable {V E Z : Type*} [Fintype E] (G : Search V E Z)

/-- `v` is on the root path selected by the choices `c`. -/
def onPath (c : V → E) (v : V) : Prop := v ∈ walk G.src G.tgt c (G.rk G.root) G.root

/-- Visit count of `v` in the past simulations `L`. -/
def nV (L : List ((V → E) × ℝ)) (v : V) : ℕ := L.countP (fun r => decide (G.onPath r.1 v))

/-- Number of past simulations that visit `v` and leave through `e`. -/
def nE (L : List ((V → E) × ℝ)) (v : V) (e : E) : ℕ :=
  L.countP (fun r => decide (G.onPath r.1 v ∧ r.1 v = e))

/-- **The PUCT selection at every vertex**, given the past simulations `L` and the
tie-breaking rule `w`: a maximiser of `Q_e + λ_e √(n_v) / (1 + N_{v,e})` over the outgoing
edges of `v`. -/
def sel (w : Finset E → E) (L : List ((V → E) × ℝ)) : V → E :=
  fun v => pickMax w (outEdges G.src v)
    (fun e => G.bk L e + G.lam e * √(G.nV L v : ℝ) / (1 + (G.nE L v e : ℝ)))

/-- The simulation records replayed from the observation history. -/
def simsOf (w : Finset E → E) (h : List (Z × ℝ)) : List ((V → E) × ℝ) :=
  h.foldl (fun L p => L ++ [(G.sel w L, p.2)]) []

/-- The terminal reached by the next simulation. -/
def next (w : Finset E → E) (h : List (Z × ℝ)) : Z :=
  G.leaf (endV G.src G.tgt (G.sel w (G.simsOf w h)) (G.rk G.root) G.root)

/-- **Recursive PUCT with the stopping rule as a `Representation.Controller`.**  The
controller tape is the tie-breaking rule.  The reply of the monitor is the vector of exact
certificates; the stopping bit is set when some certificate is at most `ε`.  The sampling
rule does not read the reply. -/
def controller (ε : ℝ) (A : Type*) : Controller Z ℝ (A → ℝ) (Finset E → E) where
  next := fun h _ w => G.next w h
  stop := fun _ r => decide (∃ a, r a ≤ ε)

/-- The observation history after `n` simulations on the tapes `x`. -/
def hist (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) : List (Z × ℝ) := tapeRun (G.next w) x n

/-- The simulation records after `n` simulations. -/
def sims (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) : List ((V → E) × ℝ) :=
  G.simsOf w (G.hist w x n)

/-- The selection function of simulation `n`. -/
def ch (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) : V → E := G.sel w (G.sims w x n)

/-- Simulation `n` visits `v`. -/
def vis (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) (v : V) : Prop := G.onPath (G.ch w x n) v

/-- The backed-up value of `e` before simulation `n`. -/
def Q (w : Finset E → E) (x : Z → ℕ → ℝ) (e : E) (n : ℕ) : ℝ := G.bk (G.sims w x n) e

/-- Stopping index of the search run against the oracle `o`. -/
def tau {A : Type*} (ε : ℝ) (o : List (Z × ℝ) → A → ℝ) (w : Finset E → E)
    (x : Z → ℕ → ℝ) : ℕ :=
  stopIdx o (G.controller ε A) w x

/-- Recommendation at the stopping index. -/
def rcm {A : Type*} [Nonempty A] (ε : ℝ) (o : List (Z × ℝ) → A → ℝ) (w : Finset E → E)
    (x : Z → ℕ → ℝ) : A :=
  recOf ε (finalReply o (G.controller ε A) w x)

/-- The sampling sequence of the controller does not depend on the oracle. -/
lemma ctrlRun_eq {A : Type*} (ε : ℝ) (o : List (Z × ℝ) → A → ℝ) (w : Finset E → E)
    (x : Z → ℕ → ℝ) : ctrlRun o (G.controller ε A) w x = G.hist w x := rfl

/-- Conditions on the search data: positive weights, the rank decreases along edges, backed-up
values in `[0, 1]`, and the terminals are exactly the sinks (`term z` is a sink, every sink
`v` is `term (leaf v)`, and `leaf (term z) = z`). -/
structure Valid (term : Z → V) : Prop where
  lam_pos : ∀ e, 0 < G.lam e
  rk_lt : ∀ e, G.rk (G.tgt e) < G.rk (G.src e)
  bk_mem : ∀ L e, 0 ≤ G.bk L e ∧ G.bk L e ≤ 1
  sink : ∀ z, ¬ (outEdges G.src (term z)).Nonempty
  term_leaf : ∀ v, ¬ (outEdges G.src v).Nonempty → term (G.leaf v) = v
  leaf_term : ∀ z, G.leaf (term z) = z

lemma sel_src (w : Finset E → E) (L : List ((V → E) × ℝ)) :
    ∀ v, (outEdges G.src v).Nonempty → G.src (G.sel w L v) = v :=
  fun _ hv => mem_outEdges.mp (pickMax_spec w _ hv).1

lemma sims_succ (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) :
    G.sims w x (n + 1) = G.sims w x n ++
      [(G.ch w x n, x (G.next w (G.hist w x n)) (cntZ (G.next w (G.hist w x n))
        (G.hist w x n)))] := by
  have e : G.hist w x (n + 1) = G.hist w x n ++
      [(G.next w (G.hist w x n), x (G.next w (G.hist w x n))
        (cntZ (G.next w (G.hist w x n)) (G.hist w x n)))] := rfl
  unfold sims
  rw [e]
  unfold simsOf
  rw [List.foldl_append]
  rfl

lemma nV_eq (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) (v : V) :
    G.nV (G.sims w x n) v = visitCount (G.vis w x) v n :=
  countP_seq (fun n => G.sims w x n)
    (fun n => (G.ch w x n, x (G.next w (G.hist w x n)) (cntZ (G.next w (G.hist w x n))
      (G.hist w x n)))) rfl (G.sims_succ w x) (fun r => G.onPath r.1 v) n

lemma nE_eq (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) (v : V) (e : E) :
    G.nE (G.sims w x n) v e = edgeCount (G.vis w x) (G.ch w x) v e n :=
  countP_seq (fun n => G.sims w x n)
    (fun n => (G.ch w x n, x (G.next w (G.hist w x n)) (cntZ (G.next w (G.hist w x n))
      (G.hist w x n)))) rfl (G.sims_succ w x) (fun r => G.onPath r.1 v ∧ r.1 v = e) n

variable {G} {term : Z → V}

/-- **The trajectory of the controller is a recursive-PUCT run** in the sense of `PUCTRun`,
for every tie-breaking rule and every reward tape. -/
theorem puctRun (hG : G.Valid term) (w : Finset E → E) (x : Z → ℕ → ℝ) :
    PUCTRun G.src G.tgt G.root G.lam (G.vis w x) (G.ch w x) (G.Q w x) := by
  refine ⟨hG.lam_pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    show G.root ∈ walk G.src G.tgt (G.ch w x s) (G.rk G.root) G.root
    exact walk_head _ _ _ _ _
  · intro s v _ hne
    exact G.sel_src w (G.sims w x s) v hne
  · intro s v hv hne
    show G.tgt (G.ch w x s v) ∈ walk G.src G.tgt (G.ch w x s) (G.rk G.root) G.root
    have hc : ∀ v, (outEdges G.src v).Nonempty → G.src (G.ch w x s v) = v :=
      G.sel_src w (G.sims w x s)
    exact walk_step hG.rk_lt hc (G.rk G.root) G.root le_rfl v hv hne
  · intro s e
    exact hG.bk_mem _ e
  · intro s v _ e he
    have hA : (outEdges G.src v).Nonempty := ⟨e, mem_outEdges.mpr he⟩
    rw [← G.nV_eq w x s v, ← G.nE_eq w x s v e, ← G.nE_eq w x s v (G.ch w x s v)]
    have key : ∀ e' ∈ outEdges G.src v,
        G.bk (G.sims w x s) e' + G.lam e' * √(G.nV (G.sims w x s) v : ℝ) /
          (1 + (G.nE (G.sims w x s) v e' : ℝ)) ≤
        G.bk (G.sims w x s) (G.sel w (G.sims w x s) v) +
          G.lam (G.sel w (G.sims w x s) v) * √(G.nV (G.sims w x s) v : ℝ) /
          (1 + (G.nE (G.sims w x s) v (G.sel w (G.sims w x s) v) : ℝ)) :=
      (pickMax_spec w
        (fun e => G.bk (G.sims w x s) e + G.lam e * √(G.nV (G.sims w x s) v : ℝ) /
          (1 + (G.nE (G.sims w x s) v e : ℝ))) hA).2
    exact key e (mem_outEdges.mpr he)

lemma onPath_term_iff (hG : G.Valid term) {c : V → E}
    (hc : ∀ v, (outEdges G.src v).Nonempty → G.src (c v) = v) (z : Z) :
    G.onPath c (term z) ↔ G.leaf (endV G.src G.tgt c (G.rk G.root) G.root) = z := by
  constructor
  · intro h
    rw [endV_eq_of_mem hG.rk_lt hc _ _ le_rfl (term z) h (hG.sink z)]
    exact hG.leaf_term z
  · intro h
    have hs := endV_sink hG.rk_lt hc (G.rk G.root) G.root le_rfl
    have ht := hG.term_leaf _ hs
    rw [h] at ht
    unfold onPath
    rw [ht]
    exact endV_mem _ _

/-- The visit count of the terminal vertex of `z` is the number of observations of `z`. -/
lemma term_count (hG : G.Valid term) (w : Finset E → E) (x : Z → ℕ → ℝ) (n : ℕ) (z : Z) :
    visitCount (G.vis w x) (term z) n = cntZ z (G.hist w x n) := by
  have e1 : cntZ z (G.hist w x n) = stepCount (fun i => G.next w (G.hist w x i) = z) n :=
    countP_seq (fun n => G.hist w x n)
      (fun i => (G.next w (G.hist w x i), x (G.next w (G.hist w x i))
        (cntZ (G.next w (G.hist w x i)) (G.hist w x i)))) rfl (fun _ => rfl)
      (fun p : Z × ℝ => p.1 = z) n
  rw [e1]
  unfold visitCount
  congr 1
  funext i
  exact propext (onPath_term_iff hG (G.sel_src w _) z)

/-- **The monitor's reply along the run** is the exact certificate on the running Hoeffding
boxes `runLower`/`runUpper` at the terminal visit counts: the monitor specification that
`puct_horizon_full` takes as a hypothesis. -/
theorem ref_answer [DecidableEq Z] [Fintype Z] [Nonempty Z] {A : Type*} (hG : G.Valid term)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (β : ℕ → ℝ) (w : Finset E → E)
    (x : Z → ℕ → ℝ) (n : ℕ) :
    (refMonitor supp hne β).answer (G.hist w x n) = fun a => exactCert (supp a) (hne a)
      (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, x z i) β
        (visitCount (G.vis w x) (term z) n))
      (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, x z i) β
        (visitCount (G.vis w x) (term z) n)) := by
  rw [refMonitor_answer]
  funext a
  congr 1
  · funext z
    rw [term_count hG]
    exact congrArg Stat.lo (boxOf_tapeRun β (G.next w) x n z)
  · funext z
    rw [term_count hG]
    exact congrArg Stat.hi (boxOf_tapeRun β (G.next w) x n z)

end Search

/-! ## The horizon theorem for the concrete search and monitor -/

section Horizon

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {V E : Type*} [Fintype E]
  {Ω : Type*} [MeasurableSpace Ω] {A : Type*} [Nonempty A]

/-- **`thm:v35horizon` / `cor:v35poly`, first clause, for the concrete controller and
monitor.**  `G` is a valid search, `tie ω` the tie-breaking rule on the sample point `ω`
(arbitrary), `X z` the reward tape of terminal `z` (`[0,1]`-valued, mean `μ z`, independent
within the tape).  The search is `G.controller`, the monitor is `refMonitor` with the radius
`β_M(n, δ)`.  No hypothesis is made on the monitor or on the run: for every
`t ≥ max {t_*, D^(2^H) (1/ε)^(2^(H+1)) log(1/ε)^(2^H)}` the run stops by `t` with an
`ε`-optimal recommendation outside an event of probability at most `δ / 2`. -/
theorem puct_controller_horizon {G : Search V E Z} {term : Z → V} (hG : G.Valid term)
    (P : Measure Ω) [IsProbabilityMeasure P] (tie : Ω → Finset E → E)
    (path : Z → List E) (hpath : ∀ z, IsPath G.src G.tgt (path z) G.root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hreach : ∀ z, ∃ a, z ∈ supp a)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ)
    (t : ℕ) (ht : puctTstar G.src G.lam path ≤ t) (hε : 0 < ε) (hε1 : ε ≤ Real.exp (-1))
    (hpoly : polyD (puctCstar G.lam path) (Fintype.card Z) δ H ^ 2 ^ H *
        (1 / ε) ^ 2 ^ (H + 1) * Real.log (1 / ε) ^ 2 ^ H ≤ (t : ℝ)) :
    P {ω | ¬ (G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω) ≤ t ∧
        regret (supp (G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (tie ω) (fun z k => X z k ω))) (hne _) μ ≤ ε)} ≤ ENNReal.ofReal (δ / 2) := by
  refine puct_poly_horizon_full P (fun ω => G.vis (tie ω) (fun z k => X z k ω))
    (fun ω => G.ch (tie ω) (fun z k => X z k ω)) (fun ω => G.Q (tie ω) (fun z k => X z k ω))
    (fun ω => Search.puctRun hG _ _) term path hpath H hH supp hne hreach μ hμ X hmeas hbdd
    hmean hindep hδ0 hδ1 ε
    (fun ω => G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
      (fun z k => X z k ω))
    (fun ω => G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
      (fun z k => X z k ω)) ?_ t ht hε hε1 hpoly
  intro ω s hs
  obtain ⟨a, ha⟩ := hs
  have hcert := fun m a => congrFun (Search.ref_answer hG supp hne
    (puctRadius (Fintype.card Z) δ) (tie ω) (fun z k => X z k ω) m) a
  have hex : ∃ m, (G.controller ε A).stop
      (ctrlRun (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (G.controller ε A)
        (tie ω) (fun z k => X z k ω) m)
      ((refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
        (ctrlRun (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (G.controller ε A) (tie ω) (fun z k => X z k ω) m)) = true := by
    refine ⟨s, ?_⟩
    show decide (∃ a, (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
      (G.hist (tie ω) (fun z k => X z k ω) s) a ≤ ε) = true
    exact decide_eq_true ⟨a, (hcert s a).le.trans ha⟩
  obtain ⟨hsp, hmin⟩ := firstTime_spec hex
  have hsp' : ∃ a, (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
      (G.hist (tie ω) (fun z k => X z k ω)
        (G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω))) a ≤ ε := of_decide_eq_true hsp
  refine ⟨hmin s ?_, ?_⟩
  · show decide (∃ a, (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
      (G.hist (tie ω) (fun z k => X z k ω) s) a ≤ ε) = true
    exact decide_eq_true ⟨a, (hcert s a).le.trans ha⟩
  · have hrec := Classical.epsilon_spec hsp'
    exact (hcert _ _).ge.trans hrec

/-- **Corollary `cor:v35poly`, both clauses in one statement.**  Setting of
`puct_controller_horizon`: the recursive-PUCT controller `G.controller` on reward tapes `X`,
with the exact-regret monitor `I = refMonitor`.  Let `J` be any other implementation, with
any internal state, whose replies agree with those of `I` on the histories reached by the
run.  Then on every sample point the run with `J` has the same observation histories and
replies at every time, the same stopping index and the same recommendation; and for every
`t ≥ max {t_*, D^(2^H) (1/ε)^(2^(H+1)) log(1/ε)^(2^H)}`, with either implementation, the
search stops by `t` with an `ε`-optimal recommendation outside an event of probability at
most `δ / 2`. -/
theorem v35poly_oracle_substitution {G : Search V E Z} {term : Z → V} (hG : G.Valid term)
    (P : Measure Ω) [IsProbabilityMeasure P] (tie : Ω → Finset E → E)
    (path : Z → List E) (hpath : ∀ z, IsPath G.src G.tgt (path z) G.root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hreach : ∀ z, ∃ a, z ∈ supp a)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ)
    (t : ℕ) (ht : puctTstar G.src G.lam path ≤ t) (hε : 0 < ε) (hε1 : ε ≤ Real.exp (-1))
    (hpoly : polyD (puctCstar G.lam path) (Fintype.card Z) δ H ^ 2 ^ H *
        (1 / ε) ^ 2 ^ (H + 1) * Real.log (1 / ε) ^ 2 ^ H ≤ (t : ℝ))
    {σ' : Type*} (J : OracleImpl σ' (Z × ℝ) (A → ℝ))
    (hJ : ∀ ω n, J.answer (G.hist (tie ω) (fun z k => X z k ω) n) =
      (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
        (G.hist (tie ω) (fun z k => X z k ω) n)) :
    (∀ ω n,
      ctrlRun J.answer (G.controller ε A) (tie ω) (fun z k => X z k ω) n =
        ctrlRun (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (G.controller ε A) (tie ω) (fun z k => X z k ω) n ∧
      J.answer (ctrlRun J.answer (G.controller ε A) (tie ω) (fun z k => X z k ω) n) =
        (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (ctrlRun (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
            (G.controller ε A) (tie ω) (fun z k => X z k ω) n)) ∧
    (∀ ω,
      G.tau ε J.answer (tie ω) (fun z k => X z k ω) =
        G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω) ∧
      G.rcm ε J.answer (tie ω) (fun z k => X z k ω) =
        G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω)) ∧
    P {ω | ¬ (G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω) ≤ t ∧
        regret (supp (G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (tie ω) (fun z k => X z k ω))) (hne _) μ ≤ ε)} ≤ ENNReal.ofReal (δ / 2) ∧
    P {ω | ¬ (G.tau ε J.answer (tie ω) (fun z k => X z k ω) ≤ t ∧
        regret (supp (G.rcm ε J.answer (tie ω) (fun z k => X z k ω))) (hne _) μ ≤ ε)} ≤
      ENNReal.ofReal (δ / 2) := by
  have hc := fun ω => tape_coupling
    (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer J.answer (G.controller ε A)
    (tie ω) (fun z k => X z k ω) (hJ ω)
  have hI := puct_controller_horizon hG P tie path hpath H hH supp hne hreach μ hμ X hmeas
    hbdd hmean hindep hδ0 hδ1 ε t ht hε hε1 hpoly
  have hτ : ∀ ω, G.tau ε J.answer (tie ω) (fun z k => X z k ω) =
      G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
        (fun z k => X z k ω) := fun ω => (hc ω).2.2.1
  have hr : ∀ ω, G.rcm ε J.answer (tie ω) (fun z k => X z k ω) =
      G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
        (fun z k => X z k ω) := fun ω => congrArg (recOf ε) (hc ω).2.2.2
  refine ⟨fun ω n => ⟨(hc ω).1 n, (hc ω).2.1 n⟩, fun ω => ⟨hτ ω, hr ω⟩, hI, ?_⟩
  have hset : {ω | ¬ (G.tau ε J.answer (tie ω) (fun z k => X z k ω) ≤ t ∧
        regret (supp (G.rcm ε J.answer (tie ω) (fun z k => X z k ω))) (hne _) μ ≤ ε)} =
      {ω | ¬ (G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω) ≤ t ∧
        regret (supp (G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (tie ω) (fun z k => X z k ω))) (hne _) μ ≤ ε)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [hτ ω, hr ω]
  rw [hset]
  exact hI

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] [Nonempty A] in
/-- The same coupling in the vocabulary of `Representation`: for the reward table that reveals
tape entries in order along the run, `Representation.history`, `replyAt` and `stopTime` of
the two implementations coincide, and `history` is the tape run. -/
theorem representation_coupling_on_tapes {G : Search V E Z} (ε : ℝ)
    {σ σ' : Type*} (I : OracleImpl σ (Z × ℝ) (A → ℝ)) (J : OracleImpl σ' (Z × ℝ) (A → ℝ))
    (hIJ : ∀ h, J.answer h = I.answer h) (w : Finset E → E) (x : Z → ℕ → ℝ) :
    (∀ n, history I.answer (G.controller ε A) (tapeTable x (G.hist w x)) w n = G.hist w x n) ∧
    (∀ n, history J.answer (G.controller ε A) (tapeTable x (G.hist w x)) w n = G.hist w x n) ∧
    (∀ n, replyAt J.answer (G.controller ε A) (tapeTable x (G.hist w x)) w n =
      replyAt I.answer (G.controller ε A) (tapeTable x (G.hist w x)) w n) ∧
    stopTime J.answer (G.controller ε A) (tapeTable x (G.hist w x)) w =
      stopTime I.answer (G.controller ε A) (tapeTable x (G.hist w x)) w := by
  obtain ⟨h1, h2, h3⟩ := exact_coupling I J hIJ (G.controller ε A) (tapeTable x (G.hist w x)) w
  have hI : ∀ n, history I.answer (G.controller ε A) (tapeTable x (G.hist w x)) w n =
      G.hist w x n := fun n => history_tapeTable I.answer (G.controller ε A) w x n
  exact ⟨hI, fun n => (h1 n).trans (hI n), h2, h3⟩

end Horizon

/-! ## A second exact implementation: the dual-cover index -/

section DualCover

open HeapImpl (HState findMax dcUpdateH)
open CostModel (blk)
open DualCoverFinal (dcInit dcRunH leafRun subsOf dual_cover_index)

variable {Z : Type*} {A : Type*} [DecidableEq A] [Inhabited A] {M : ℕ}

/-- Leaf values of the segment tree under the layout `π`: position `π z` holds `g z`, all
other positions are blank. -/
def leafVal (π : Z ≃ Fin M) (g : Z → ℝ) : ℕ → WithBot ℝ :=
  fun p => if h : p < M then ((g (π.symm ⟨p, h⟩) : ℝ) : WithBot ℝ) else ⊥

omit [DecidableEq A] [Inhabited A] in
lemma leafVal_pos (π : Z ≃ Fin M) (g : Z → ℝ) (z : Z) :
    leafVal π g (π z : ℕ) = ((g z : ℝ) : WithBot ℝ) := by
  unfold leafVal
  rw [dite_eq_left (π z).2]
  simp

omit [DecidableEq A] [Inhabited A] in
lemma leafVal_blank (π : Z ≃ Fin M) (g : Z → ℝ) {n : ℕ} (hM : M ≤ 2 ^ n) :
    ∀ p, 2 ^ n ≤ p → leafVal π g p = ⊥ := by
  intro p hp
  unfold leafVal
  rw [dite_eq_right (by omega)]

omit [DecidableEq A] [Inhabited A] in
lemma leafVal_update [DecidableEq Z] (π : Z ≃ Fin M) (g : Z → ℝ) (z : Z) (y : ℝ) :
    leafVal π (Function.update g z y) =
      Function.update (leafVal π g) (π z : ℕ) ((y : ℝ) : WithBot ℝ) := by
  funext p
  by_cases hpz : p = (π z : ℕ)
  · subst hpz
    rw [Function.update_self, leafVal_pos, Function.update_self]
  · rw [Function.update_of_ne hpz]
    unfold leafVal
    by_cases hp : p < M
    · rw [dite_eq_left hp, dite_eq_left hp, Function.update_of_ne]
      intro h
      apply hpz
      rw [← h]
      simp
    · rw [dite_eq_right hp, dite_eq_right hp]

omit [Inhabited A] in
lemma dcRunH_append_fst {α : Type*} [LinearOrder α] [OrderBot α] (n : ℕ)
    (subs : ℕ × ℕ → List A) (u : ℕ × α) : ∀ (us : List (ℕ × α)) (s : HState A α),
    (dcRunH n subs (us ++ [u]) s).1 = (dcUpdateH n subs u.1 u.2 (dcRunH n subs us s).1).1
  | [], _ => rfl
  | _ :: us, _ => dcRunH_append_fst n subs u us _

omit [DecidableEq A] [Inhabited A] in
lemma leafRun_append {α : Type*} (u : ℕ × α) : ∀ (us : List (ℕ × α)) (f : ℕ → α),
    leafRun f (us ++ [u]) = Function.update (leafRun f us) u.1 u.2
  | [], _ => rfl
  | _ :: us, _ => leafRun_append u us _

variable [DecidableEq Z] (π : Z ≃ Fin M) (n : ℕ) (as : List A)

/-- The implemented index state `s` (one endpoint, covers `covL`, initial leaf value `c`) is
the result of a run of updates from the initialised index, and the leaf values of that run
are the endpoints `g (st z)` of the monitor statistics `st`. -/
def IdxInv (c : ℝ) (covL : A → List (ℕ × ℕ)) (g : Stat → ℝ) (st : Z → Stat)
    (s : HState A (WithBot ℝ)) : Prop :=
  ∃ us : List (ℕ × WithBot ℝ), (∀ u ∈ us, u.1 < 2 ^ n) ∧
    s = (dcRunH n (subsOf as covL) us (dcInit n (leafVal π (fun _ => c)) covL as).1).1 ∧
    leafRun (leafVal π (fun _ => c)) us = leafVal π (fun z => g (st z))

variable {π n as}

lemma idxInv_step (β : ℕ → ℝ) (hM : M ≤ 2 ^ n) (c : ℝ) (covL : A → List (ℕ × ℕ))
    (g : Stat → ℝ) {st : Z → Stat} {s : HState A (WithBot ℝ)}
    (h : IdxInv π n as c covL g st s) (p : Z × ℝ) :
    IdxInv π n as c covL g (boxStep β st p)
      (dcUpdateH n (subsOf as covL) (π p.1 : ℕ)
        ((g (boxStep β st p p.1) : ℝ) : WithBot ℝ) s).1 := by
  obtain ⟨us, hus, hs, hl⟩ := h
  refine ⟨us ++ [((π p.1 : ℕ), ((g (boxStep β st p p.1) : ℝ) : WithBot ℝ))], ?_, ?_, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with h1 | h1
    · exact hus u h1
    · rw [List.mem_singleton] at h1
      subst h1
      exact lt_of_lt_of_le (π p.1).2 hM
  · rw [dcRunH_append_fst, ← hs]
  · rw [leafRun_append, hl]
    show Function.update (leafVal π (fun z => g (st z))) (π p.1 : ℕ)
      ((g (boxStep β st p p.1) : ℝ) : WithBot ℝ) = _
    rw [← leafVal_update]
    congr 1
    funext z
    by_cases hz : z = p.1
    · subst hz
      rw [Function.update_self]
    · rw [Function.update_of_ne hz]
      unfold boxStep
      rw [Function.update_of_ne hz]

omit [DecidableEq Z] in
/-- **Query of the index.**  If the blocks of `covL a` cover exactly the positions of
`S a`, the root of the heap of `a` is the maximum of the endpoints over `S a`. -/
lemma idx_query (hM : M ≤ 2 ^ n) (hnd : as.Nodup) (hall : ∀ a, a ∈ as) {c : ℝ}
    {covL : A → List (ℕ × ℕ)} (hcn : ∀ a, (covL a).Nodup)
    (hnodes : ∀ a, ∀ d ∈ covL a, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1)) (S : A → Finset Z)
    (hcov : ∀ a, (covL a).toFinset.biUnion blk = (S a).image (fun z => (π z : ℕ)))
    {g : Stat → ℝ} {st : Z → Stat} {s : HState A (WithBot ℝ)}
    (h : IdxInv π n as c covL g st s) (a : A) :
    findMax (s.hp a) = (S a).sup (fun z => ((g (st z) : ℝ) : WithBot ℝ)) := by
  obtain ⟨us, hus, hs, hl⟩ := h
  have hq := (dual_cover_index n (leafVal π (fun _ => c)) (leafVal_blank π _ hM) covL as hnd
    hcn (fun a ha => absurd (hall a) ha) hnodes us hus).1 a
  rw [hs, hq, hl, hcov, Finset.sup_image]
  refine Finset.sup_congr rfl (fun z _ => ?_)
  exact leafVal_pos π _ z

omit [DecidableEq A] [Inhabited A] [DecidableEq Z] in
lemma sup_coe_unbot {S : Finset Z} (hS : S.Nonempty) (F : Z → ℝ) :
    (S.sup (fun z => ((F z : ℝ) : WithBot ℝ))).unbotD 0 = S.sup' hS F := by
  have h : S.sup (fun z => ((F z : ℝ) : WithBot ℝ)) = ((S.sup' hS F : ℝ) : WithBot ℝ) :=
    (Finset.coe_sup' hS F).symm
  rw [h, WithBot.unbotD_coe]

variable (π n as) (covS covC : A → List (ℕ × ℕ)) (β : ℕ → ℝ)

/-- One step of the dual-cover monitor on an observation `(z, x)`: update the statistics of
`z`, then write the new lower endpoint into the index over the support covers and the new
upper endpoint into the index over the complement covers (`HeapImpl.dcUpdateH`: leaf-to-root
recomputation in the segment tree, key updates in the subscribed heaps). -/
def dcStep (s : (Z → Stat) × HState A (WithBot ℝ) × HState A (WithBot ℝ)) (p : Z × ℝ) :
    (Z → Stat) × HState A (WithBot ℝ) × HState A (WithBot ℝ) :=
  (boxStep β s.1 p,
   (dcUpdateH n (subsOf as covS) (π p.1 : ℕ)
      (((boxStep β s.1 p p.1).lo : ℝ) : WithBot ℝ) s.2.1).1,
   (dcUpdateH n (subsOf as covC) (π p.1 : ℕ)
      (((boxStep β s.1 p p.1).hi : ℝ) : WithBot ℝ) s.2.2).1)

/-- Initial state: all intervals `[0, 1]`, both indexes initialised by
`DualCoverFinal.dcInit`. -/
def dcStart : (Z → Stat) × HState A (WithBot ℝ) × HState A (WithBot ℝ) :=
  (fun _ => Stat.init, (dcInit n (leafVal π (fun _ => (0 : ℝ))) covS as).1,
    (dcInit n (leafVal π (fun _ => (1 : ℝ))) covC as).1)

/-- **The dual-cover monitor as an oracle implementation.**  The reply for a root action `a`
reads the roots of two heaps: the maximum lower endpoint over the support of `a` and the
maximum upper endpoint over its complement, and returns `[U - L]_+` (or `0` for a full
support). -/
def dcMonitor [Fintype Z] (supp : A → Finset Z) :
    OracleImpl ((Z → Stat) × HState A (WithBot ℝ) × HState A (WithBot ℝ)) (Z × ℝ) (A → ℝ) where
  init := dcStart π n as covS covC
  step := dcStep π n as covS covC β
  reply := fun s a =>
    if (supp a)ᶜ.Nonempty then
      max 0 ((findMax (s.2.2.hp a)).unbotD 0 - (findMax (s.2.1.hp a)).unbotD 0)
    else 0

variable {π n as covS covC}

lemma dcMonitor_inv (hM : M ≤ 2 ^ n) (h : List (Z × ℝ)) :
    (h.foldl (dcStep π n as covS covC β) (dcStart π n as covS covC)).1 = boxOf β h ∧
    IdxInv π n as 0 covS Stat.lo (boxOf β h)
      (h.foldl (dcStep π n as covS covC β) (dcStart π n as covS covC)).2.1 ∧
    IdxInv π n as 1 covC Stat.hi (boxOf β h)
      (h.foldl (dcStep π n as covS covC β) (dcStart π n as covS covC)).2.2 := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl, ⟨[], by simp, rfl, rfl⟩, ⟨[], by simp, rfl, rfl⟩⟩
  | append_singleton h p ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hb : boxOf β (h ++ [p]) = boxStep β (boxOf β h) p := by
      unfold boxOf
      rw [List.foldl_append]
      rfl
    rw [List.foldl_append, hb]
    generalize List.foldl (dcStep π n as covS covC β) (dcStart π n as covS covC) h = s
      at h1 h2 h3 ⊢
    obtain ⟨st, L, U⟩ := s
    dsimp only at h1 h2 h3
    subst h1
    exact ⟨rfl, idxInv_step β hM 0 covS Stat.lo h2 p, idxInv_step β hM 1 covC Stat.hi h3 p⟩

/-- **The dual-cover monitor is exact.**  `as` lists the root actions without repetition;
`covS a` / `covC a` are lists of segment-tree nodes without repetition whose blocks cover
exactly the positions of the support of `a` / of its complement.  Then on EVERY history the
dual-cover monitor returns the same reply as the exact-regret monitor `refMonitor`. -/
theorem dcMonitor_answer [Fintype Z] [Nonempty Z] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hM : M ≤ 2 ^ n) (hnd : as.Nodup) (hall : ∀ a, a ∈ as)
    (hcnS : ∀ a, (covS a).Nodup)
    (hnodesS : ∀ a, ∀ d ∈ covS a, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1))
    (hcovS : ∀ a, (covS a).toFinset.biUnion blk = (supp a).image (fun z => (π z : ℕ)))
    (hcnC : ∀ a, (covC a).Nodup)
    (hnodesC : ∀ a, ∀ d ∈ covC a, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1))
    (hcovC : ∀ a, (covC a).toFinset.biUnion blk = (supp a)ᶜ.image (fun z => (π z : ℕ)))
    (h : List (Z × ℝ)) :
    (dcMonitor π n as covS covC β supp).answer h = (refMonitor supp hne β).answer h := by
  obtain ⟨_, h2, h3⟩ := dcMonitor_inv (π := π) (as := as) (covS := covS) (covC := covC) β hM h
  rw [refMonitor_answer]
  funext a
  have qL := idx_query hM hnd hall hcnS hnodesS supp hcovS h2 a
  have qU := idx_query hM hnd hall hcnC hnodesC (fun a => (supp a)ᶜ) hcovC h3 a
  show (if (supp a)ᶜ.Nonempty then
      max 0 ((findMax ((h.foldl (dcStep π n as covS covC β)
          (dcStart π n as covS covC)).2.2.hp a)).unbotD 0 -
        (findMax ((h.foldl (dcStep π n as covS covC β)
          (dcStart π n as covS covC)).2.1.hp a)).unbotD 0)
    else 0) = _
  unfold exactCert
  by_cases hc : (supp a)ᶜ.Nonempty
  · rw [ite_eq_left hc, dite_eq_left hc, qL, qU, sup_coe_unbot hc, sup_coe_unbot (hne a)]
    rfl
  · rw [ite_eq_right hc, dite_eq_right hc]

omit [DecidableEq A] [Inhabited A] [DecidableEq Z] in
/-- The cover hypotheses of `dcMonitor_answer` are satisfiable: the cover of a set by its
leaf blocks.  (Dyadic covers with few blocks are produced by
`Representation.exists_dyadicCover` and `CostModel.dualCompile`; exactness does not depend on
which cover is used.) -/
lemma leaf_cover_spec (π : Z ≃ Fin M) {n : ℕ} (hM : M ≤ 2 ^ n) (S : Finset Z) :
    ((S.image (fun z => ((0 : ℕ), (π z : ℕ)))).toList).Nodup ∧
    (∀ d ∈ (S.image (fun z => ((0 : ℕ), (π z : ℕ)))).toList, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1)) ∧
    ((S.image (fun z => ((0 : ℕ), (π z : ℕ)))).toList).toFinset.biUnion blk =
      S.image (fun z => (π z : ℕ)) := by
  refine ⟨Finset.nodup_toList _, ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_toList, mem_image] at hd
    obtain ⟨z, _, rfl⟩ := hd
    exact ⟨Nat.zero_le _, lt_of_lt_of_le (π z).2 hM⟩
  · rw [Finset.toList_toFinset]
    ext p
    simp only [mem_biUnion, mem_image]
    constructor
    · rintro ⟨d, ⟨z, hz, rfl⟩, hp⟩
      have hb : blk ((0 : ℕ), (π z : ℕ)) = {(π z : ℕ)} := CostModel.dyadicBlock_zero _
      rw [hb, mem_singleton] at hp
      exact ⟨z, hz, hp.symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨((0 : ℕ), (π z : ℕ)), ⟨z, hz, rfl⟩, ?_⟩
      have hb : blk ((0 : ℕ), (π z : ℕ)) = {(π z : ℕ)} := CostModel.dyadicBlock_zero _
      rw [hb]
      exact mem_singleton_self _

end DualCover

/-! ## The composed statement with the dual-cover monitor -/

section DualCoverComposed

open CostModel (blk)

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {V E : Type*} [Fintype E]
  {Ω : Type*} [MeasurableSpace Ω] {A : Type*} [DecidableEq A] [Inhabited A]

/-- **Corollary `cor:v35poly` with the dual-cover monitor substituted for the exact-regret
monitor.**  Setting of `v35poly_oracle_substitution`; `π` is a layout of the terminals in
`M ≤ 2^n` positions, `as` lists the root actions, and `covS`, `covC` are covers of the
supports and of their complements by segment-tree nodes.  Running the recursive-PUCT
controller with `dcMonitor` (segment trees and implemented heaps) instead of `refMonitor`
gives, on every sample point, the same observation histories and replies at every time, the
same stopping index and the same recommendation; and with either monitor the search stops by
every `t ≥ max {t_*, D^(2^H) (1/ε)^(2^(H+1)) log(1/ε)^(2^H)}` with an `ε`-optimal
recommendation outside an event of probability at most `δ / 2`. -/
theorem v35poly_dual_cover {G : Search V E Z} {term : Z → V} (hG : G.Valid term)
    (P : Measure Ω) [IsProbabilityMeasure P] (tie : Ω → Finset E → E)
    (path : Z → List E) (hpath : ∀ z, IsPath G.src G.tgt (path z) G.root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hreach : ∀ z, ∃ a, z ∈ supp a)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ)
    (t : ℕ) (ht : puctTstar G.src G.lam path ≤ t) (hε : 0 < ε) (hε1 : ε ≤ Real.exp (-1))
    (hpoly : polyD (puctCstar G.lam path) (Fintype.card Z) δ H ^ 2 ^ H *
        (1 / ε) ^ 2 ^ (H + 1) * Real.log (1 / ε) ^ 2 ^ H ≤ (t : ℝ))
    {M n : ℕ} (π : Z ≃ Fin M) (hM : M ≤ 2 ^ n) (as : List A) (hnd : as.Nodup)
    (hall : ∀ a, a ∈ as) (covS covC : A → List (ℕ × ℕ))
    (hcnS : ∀ a, (covS a).Nodup)
    (hnodesS : ∀ a, ∀ d ∈ covS a, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1))
    (hcovS : ∀ a, (covS a).toFinset.biUnion blk = (supp a).image (fun z => (π z : ℕ)))
    (hcnC : ∀ a, (covC a).Nodup)
    (hnodesC : ∀ a, ∀ d ∈ covC a, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1))
    (hcovC : ∀ a, (covC a).toFinset.biUnion blk = (supp a)ᶜ.image (fun z => (π z : ℕ))) :
    (∀ ω n',
      ctrlRun (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp).answer
          (G.controller ε A) (tie ω) (fun z k => X z k ω) n' =
        ctrlRun (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (G.controller ε A) (tie ω) (fun z k => X z k ω) n' ∧
      (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp).answer
          (ctrlRun (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp).answer
            (G.controller ε A) (tie ω) (fun z k => X z k ω) n') =
        (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (ctrlRun (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
            (G.controller ε A) (tie ω) (fun z k => X z k ω) n')) ∧
    (∀ ω,
      G.tau ε (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp).answer (tie ω)
          (fun z k => X z k ω) =
        G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω) ∧
      G.rcm ε (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp).answer (tie ω)
          (fun z k => X z k ω) =
        G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω)) ∧
    P {ω | ¬ (G.tau ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer (tie ω)
          (fun z k => X z k ω) ≤ t ∧
        regret (supp (G.rcm ε (refMonitor supp hne (puctRadius (Fintype.card Z) δ)).answer
          (tie ω) (fun z k => X z k ω))) (hne _) μ ≤ ε)} ≤ ENNReal.ofReal (δ / 2) ∧
    P {ω | ¬ (G.tau ε (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp).answer
          (tie ω) (fun z k => X z k ω) ≤ t ∧
        regret (supp (G.rcm ε
          (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp).answer
          (tie ω) (fun z k => X z k ω))) (hne _) μ ≤ ε)} ≤ ENNReal.ofReal (δ / 2) :=
  v35poly_oracle_substitution hG P tie path hpath H hH supp hne hreach μ hμ X hmeas hbdd hmean
    hindep hδ0 hδ1 ε t ht hε hε1 hpoly
    (dcMonitor π n as covS covC (puctRadius (Fintype.card Z) δ) supp)
    (fun _ _ => dcMonitor_answer (puctRadius (Fintype.card Z) δ) supp hne hM hnd hall hcnS
      hnodesS hcovS hcnC hnodesC hcovC _)

end DualCoverComposed

/-! ## Non-vacuity -/

section NonVacuity

variable {V E Z : Type*} [Fintype E]

/-- The backup rule of recursive PUCT: `Q_e` is the mean of the (clipped) rewards of the past
simulations that traversed `e`, and `0` before the first traversal. -/
def meanBackup (src tgt : E → V) (root : V) (rk : V → ℕ) (L : List ((V → E) × ℝ)) (e : E) : ℝ :=
  clipMean ((L.filter (fun r => decide (src e ∈ walk src tgt r.1 (rk root) root ∧
    r.1 (src e) = e))).map Prod.snd)

/-- Every graph with positive weights, a rank function and terminals at the sinks gives a
valid search with the mean backup rule. -/
theorem valid_meanBackup (src tgt : E → V) (root : V) (lam : E → ℝ) (rk : V → ℕ)
    (leaf : V → Z) (term : Z → V) (hlam : ∀ e, 0 < lam e)
    (hrk : ∀ e, rk (tgt e) < rk (src e)) (hsink : ∀ z, ¬ (outEdges src (term z)).Nonempty)
    (hterm : ∀ v, ¬ (outEdges src v).Nonempty → term (leaf v) = v)
    (hleaf : ∀ z, leaf (term z) = z) :
    (Search.mk src tgt root lam rk leaf (meanBackup src tgt root rk)).Valid term :=
  ⟨hlam, hrk, fun _ _ => clipMean_mem _, hsink, hterm, hleaf⟩

/-- A concrete valid search: the one-level tree whose root has one edge to each terminal. -/
theorem exists_valid_search (Z : Type*) [Fintype Z] [Nonempty Z] :
    ∃ (G : Search (Option Z) Z Z) (path : Z → List Z),
      G.Valid some ∧ (∀ z, IsPath G.src G.tgt (path z) G.root (some z)) ∧
      ∀ z, (path z).length ≤ 1 := by
  refine ⟨Search.mk (fun _ => none) some none (fun _ => 1) (fun v => v.elim 1 (fun _ => 0))
    (fun v => v.getD (Classical.arbitrary Z))
    (meanBackup (fun _ => none) some none (fun v => v.elim 1 (fun _ => 0))),
    fun z => [z], ?_, ?_, ?_⟩
  · refine valid_meanBackup _ _ _ _ _ _ _ (fun _ => one_pos) (fun _ => Nat.zero_lt_one) ?_ ?_
      (fun _ => rfl)
    · rintro z ⟨e, he⟩
      have h : (none : Option Z) = some z := mem_outEdges.mp he
      cases h
    · intro v hv
      cases v with
      | none => exact (hv ⟨Classical.arbitrary Z, mem_outEdges.mpr rfl⟩).elim
      | some z => rfl
  · intro z
    exact ⟨rfl, rfl⟩
  · intro z
    exact le_rfl

end NonVacuity

end

end LiteralE3
end JointRootCert
