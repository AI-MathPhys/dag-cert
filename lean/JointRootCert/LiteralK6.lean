/-
Joint Root Certification: `thm:coded-main` / `thm:coded-covers`, upper half, with COMPUTED
costs.

IMPORTS `JointRootCert.LiteralK2` (a new file; build it first).

Manuscript result covered:

* `thm:coded-main` (Every-layout limit of flat dyadic compilation) and `thm:coded-covers`,
  the sentence "direct graph maintenance certifies an `ε`-optimal action in
  `O(r² log² r)` total work with probability at least `1 - δ`" (Step 3 of the proof), for
  Graph Eager and for Graph Selective.

`ParityGrid.coded_main` measures the work `pgWork`, in which the heap is a charged
primitive and initialisation, allocator and query costs are stipulated numbers.  Here every
one of these is the cost component of a costed program `(result, cost)`:

* **initialisation** (`initEndC`, once per endpoint): a pass writing the initial value of
  every vertex and resetting its heap (`rawInit`, 2 units per vertex), a scan selecting the
  internal gates (`filterC`, 1 unit per vertex), and `EngineFinal.initPassH`, which builds
  every heap by insertions executed by `HeapImpl`;
* **waves**: `HeapImpl.waveH` (every heap operation executed by the implemented heap), one
  per endpoint per rollout (`runStateH`, `waveCostH`);
* **root query**: a costed leader scan and a costed stop scan (`leadScanC`, `stopScanC`,
  `qOutC`), proved to return the result of `RetireFinal.qOut` (`qOutC_spec`);
* **UCT selection at the root**: a costed argmax scan of the UCT index over the `d + 1`
  root actions (`argmaxC`, `rootSelC`); its result is an index maximiser
  (`rootSelC_spec`), a selection that follows it satisfies the greedy clause of
  `UCTWork.UCTRun` (`greedy_of_rootSelC`), and conversely the selection of any
  `ParitySearch` has the index value of the scan's result (`rootSelC_consistent`);
* **selections below the root**: costed list scans (`pickC`) of the child lists of the
  action gate and of the coordinate gate on the path, for an arbitrary index function
  `idx` (the selections below the root are unconstrained in `ParitySearch`);
* **Graph Selective**: `RetireFinal.runH` / `costH` (waves, retirements and release
  cascades on implemented heaps).

Charged by definition (not computed):

* `9` units per rollout for the at most three steps down and back up, the root statistics
  and the terminal-table update (as in `ParityGrid.pgRolloutCost`);
* one unit per array write / per scanned index inside the costed programs above (the unit
  of the cost model);
* inside `RetireFinal.costH` (Graph Selective only): `K` units for each of the three root
  scans of a query (stop scan, leader scan, root-retirement scan), one unit per retirement
  test, per list unlink and per examined gate of a release cascade, as documented in
  `RetireFinal.lean` and `EngineFinal.lean`;
* memory cells outside the vertex range `[0, N)` are assumed to hold the default value
  (`RawOK`); the contents of the cells inside the range are arbitrary before `rawInit`.

Main statements: `init_sim`, `qEagC_spec`, `qSelC_spec`, `pgWorkC_le`, `selWorkC_le`,
`parity_certified_computed` (pathwise) and `coded_main_computed` (probabilistic; it also
carries the lower half as compiler work, `LiteralK5.compiler_work_lower`).

IMPORTS `JointRootCert.LiteralK5` as well.
-/
import JointRootCert.LiteralK2
import JointRootCert.LiteralK5

namespace JointRootCert
namespace LiteralK6

open Finset MeasureTheory CostEngines DagRetire EngineFinal RetireFinal ParityGrid LiteralK2
  _root_.JointRootCert.Representation
open HeapImpl (Heap HEState SimE Rep waveH findMax)

noncomputable section

/-! ## Costed root scans -/

section Scans

variable {α : Type*} [LinearOrder α]

/-- **Costed leader scan**: `RetireFinal.leadScan`, one unit per root index. -/
def leadScanC (L : ℕ → α) (act : ℕ → Bool) : ℕ → Option ℕ × ℕ
  | 0 => (none, 0)
  | n + 1 => ((leadScanC L act n).1.elim (if act n = true then some n else none)
      (fun a => if act n = true ∧ L a < L n then some n else some a),
      (leadScanC L act n).2 + 1)

lemma leadScanC_spec (L : ℕ → α) (act : ℕ → Bool) :
    ∀ n, leadScanC L act n = (leadScan L act n, n)
  | 0 => rfl
  | n + 1 => by
    show ((leadScanC L act n).1.elim _ _, (leadScanC L act n).2 + 1) = _
    rw [leadScanC_spec L act n]
    rfl

/-- **Costed stop scan**: `RetireFinal.stopScan`, one unit per root index. -/
def stopScanC (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ) (act : ℕ → Bool) :
    ℕ → Bool × ℕ
  | 0 => (true, 0)
  | n + 1 => ((stopScanC φ ε U la a act n).1
      && (!(act n) || decide (n = a) || decide (φ (U n) - φ la ≤ ε)),
      (stopScanC φ ε U la a act n).2 + 1)

omit [LinearOrder α] in
lemma stopScanC_spec (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ) (act : ℕ → Bool) :
    ∀ n, stopScanC φ ε U la a act n = (stopScan φ ε U la a act n, n)
  | 0 => rfl
  | n + 1 => by
    show ((stopScanC φ ε U la a act n).1 && _, (stopScanC φ ε U la a act n).2 + 1) = _
    rw [stopScanC_spec φ ε U la a act n]
    rfl

/-- **Costed leader-and-stop query**: the leader scan, then (if there is a leader) the stop
scan. -/
def qOutC (φ : α → ℝ) (ε : ℝ) (K : ℕ) (L U : ℕ → α) (act : ℕ → Bool) :
    (Option ℕ × Bool) × ℕ :=
  (((leadScanC L act K).1,
    (leadScanC L act K).1.elim false (fun a => (stopScanC φ ε U (L a) a act K).1)),
   (leadScanC L act K).2
    + (leadScanC L act K).1.elim 0 (fun a => (stopScanC φ ε U (L a) a act K).2))

/-- The costed query returns the output of `RetireFinal.qOut` and costs at most `2K`. -/
lemma qOutC_spec (φ : α → ℝ) (ε : ℝ) (K : ℕ) (L U : ℕ → α) (act : ℕ → Bool) :
    (qOutC φ ε K L U act).1 = qOut φ ε K L U act ∧ (qOutC φ ε K L U act).2 ≤ 2 * K := by
  unfold qOutC qOut
  rw [leadScanC_spec]
  cases leadScan L act K with
  | none =>
    refine ⟨rfl, ?_⟩
    show K + 0 ≤ 2 * K
    omega
  | some a =>
    refine ⟨?_, ?_⟩
    · show (some a, (stopScanC φ ε U (L a) a act K).1) = (some a, stopScan φ ε U (L a) a act K)
      rw [stopScanC_spec]
    · show K + (stopScanC φ ε U (L a) a act K).2 ≤ 2 * K
      rw [stopScanC_spec]
      show K + K ≤ 2 * K
      omega

end Scans

/-! ## Costed selection scans of the allocator -/

section Select

/-- **Costed argmax scan** over the indices `0, …, n`: evaluate the index of each, keep the
best, one unit each.  Returns the selected index and the cost. -/
def argmaxC (f : ℕ → ℝ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => (if f (argmaxC f n).1 < f (n + 1) then n + 1 else (argmaxC f n).1,
      (argmaxC f n).2 + 1)

lemma argmaxC_spec (f : ℕ → ℝ) : ∀ n,
    (argmaxC f n).1 ≤ n ∧ (∀ i, i ≤ n → f i ≤ f (argmaxC f n).1) ∧ (argmaxC f n).2 = n + 1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨le_rfl, fun i hi => ?_, rfl⟩
    have : i = 0 := by omega
    rw [this]
    exact le_rfl
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e1 : (argmaxC f (n + 1)).1
        = if f (argmaxC f n).1 < f (n + 1) then n + 1 else (argmaxC f n).1 := rfl
    have e2 : (argmaxC f (n + 1)).2 = (argmaxC f n).2 + 1 := rfl
    rw [e1, e2, h3]
    by_cases hc : f (argmaxC f n).1 < f (n + 1)
    · rw [ite_eq_left hc]
      refine ⟨le_rfl, fun i hi => ?_, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with h | h
      · exact (h2 i (Nat.lt_succ_iff.1 h)).trans hc.le
      · rw [h]
    · rw [ite_eq_right hc]
      refine ⟨Nat.le_succ_of_le h1, fun i hi => ?_, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with h | h
      · exact h2 i (Nat.lt_succ_iff.1 h)
      · rw [h]
        exact not_lt.1 hc

/-- **Costed scan of a child list** with an arbitrary index `f`: keep a child of largest
index, one unit per child. -/
def pickC (f : ℕ → ℝ) : List ℕ → Option ℕ × ℕ
  | [] => (none, 0)
  | c :: cs => ((pickC f cs).1.elim (some c) (fun b => if f b < f c then some c else some b),
      (pickC f cs).2 + 1)

lemma pickC_cost (f : ℕ → ℝ) : ∀ l : List ℕ, (pickC f l).2 = l.length
  | [] => rfl
  | c :: cs => by
    show (pickC f cs).2 + 1 = _
    rw [pickC_cost f cs, List.length_cons]

/-- The scan of a nonempty child list returns one of its children with the largest index. -/
lemma pickC_spec (f : ℕ → ℝ) : ∀ l : List ℕ, l ≠ [] →
    ∃ b ∈ l, (pickC f l).1 = some b ∧ ∀ c ∈ l, f c ≤ f b := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons c cs ih =>
    intro _
    by_cases hcs : cs = []
    · subst hcs
      refine ⟨c, List.mem_cons_self, rfl, fun c' hc' => ?_⟩
      rw [List.mem_singleton.1 hc']
    · obtain ⟨b, hb, hbe, hmax⟩ := ih hcs
      have e : (pickC f (c :: cs)).1 = if f b < f c then some c else some b := by
        show (pickC f cs).1.elim _ _ = _
        rw [hbe]
        rfl
      by_cases hlt : f b < f c
      · rw [ite_eq_left hlt] at e
        refine ⟨c, List.mem_cons_self, e, fun c' hc' => ?_⟩
        rcases List.mem_cons.1 hc' with h | h
        · rw [h]
        · exact (hmax c' h).trans hlt.le
      · rw [ite_eq_right hlt] at e
        refine ⟨b, List.mem_cons_of_mem _ hb, e, fun c' hc' => ?_⟩
        rcases List.mem_cons.1 hc' with h | h
        · rw [h]
          exact not_lt.1 hlt
        · exact hmax c' h

variable {k : ℕ}

/-- The UCT index (`c = 2`) of root action `i` before rollout `t`, as evaluated by the root
scan (`0` for indices that are not root actions). -/
def rootIdx (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (t : ℕ) (i : ℕ) : ℝ :=
  if h : i < pgD k + 1 then uctIndex 2 (pgQ x sel zt t ⟨i, h⟩) t (uctCount sel t ⟨i, h⟩) else 0

lemma rootIdx_fin (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (t : ℕ) (a : Fin (pgD k + 1)) :
    rootIdx x sel zt t a = uctIndex 2 (pgQ x sel zt t a) t (uctCount sel t a) := by
  unfold rootIdx
  rw [dite_eq_left a.isLt]

/-- **Costed UCT selection at the root** before rollout `t`: the argmax scan of the UCT
index over the `d + 1` root actions. -/
def rootSelC (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (t : ℕ) : ℕ × ℕ :=
  argmaxC (rootIdx x sel zt t) (pgD k)

/-- The root scan returns a root action of largest UCT index, at cost `d + 1`. -/
theorem rootSelC_spec (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (t : ℕ) :
    (rootSelC x sel zt t).1 < pgD k + 1 ∧
    (∀ j : Fin (pgD k + 1), rootIdx x sel zt t j ≤ rootIdx x sel zt t (rootSelC x sel zt t).1) ∧
    (rootSelC x sel zt t).2 = pgD k + 1 := by
  obtain ⟨h1, h2, h3⟩ := argmaxC_spec (rootIdx x sel zt t) (pgD k)
  exact ⟨Nat.lt_succ_of_le h1, fun j => h2 j (Nat.lt_succ_iff.1 j.isLt), h3⟩

/-- A selection that follows the root scan satisfies the greedy clause of `UCTRun`. -/
theorem greedy_of_rootSelC (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (t : ℕ) (h : ((sel t : Fin (pgD k + 1)) : ℕ) = (rootSelC x sel zt t).1)
    (j : Fin (pgD k + 1)) :
    uctIndex 2 (pgQ x sel zt t j) t (uctCount sel t j)
      ≤ uctIndex 2 (pgQ x sel zt t (sel t)) t (uctCount sel t (sel t)) := by
  have h2 := (rootSelC_spec x sel zt t).2.1 j
  rw [← h, rootIdx_fin, rootIdx_fin] at h2
  exact h2

/-- Conversely, in every `ParitySearch` the action selected at a rollout `t ≥ d + 1` has
the UCT index of the scan's result (the two can differ only by tie-breaking). -/
theorem rootSelC_consistent {x : GridTerminal k → ℕ → ℝ} {sel : ℕ → Fin (pgD k + 1)}
    {zt : ℕ → GridTerminal k} (h : ParitySearch x sel zt) (t : ℕ) (ht : pgD k + 1 ≤ t) :
    rootIdx x sel zt t (sel t) = rootIdx x sel zt t (rootSelC x sel zt t).1 := by
  obtain ⟨h1, h2, _⟩ := rootSelC_spec x sel zt t
  refine le_antisymm (h2 (sel t)) ?_
  have hg := h.uct.greedy t (by rw [Fintype.card_fin]; exact ht) ⟨(rootSelC x sel zt t).1, h1⟩
  rw [← rootIdx_fin, ← rootIdx_fin] at hg
  exact hg

/-- **Computed allocator work of rollout `s`**: the root scan; for a parity action also the
scans of the child lists of the action gate and of the coordinate gate on the path (index
`idx s`, arbitrary); plus `9` units charged for the steps down and up, the root statistics
and the terminal table. -/
def rolloutC (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (idx : ℕ → ℕ → ℝ) (s : ℕ) : ℕ :=
  (rootSelC x sel zt s).2
    + Fin.lastCases (motive := fun _ => ℕ) 0
        (fun i => (pickC (idx s) ((pgDag k).children (gid (vA i)))).2
          + (pickC (idx s) ((pgDag k).children
              (gid (vC ((pgIdx k i).1, pgCoord (pgIdx k i).1 (zt s)))))).2) (sel s) + 9

lemma rolloutC_le (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (idx : ℕ → ℕ → ℝ) (s : ℕ) :
    rolloutC x sel zt idx s ≤ 7 * 2 ^ k + 6 := by
  have hd := pgD_le (k := k)
  have h0 := (rootSelC_spec x sel zt s).2.2
  unfold rolloutC
  rw [h0]
  rcases Fin.eq_castSucc_or_eq_last (sel s) with ⟨i, hi⟩ | hl
  · rw [hi, Fin.lastCases_castSucc, pickC_cost, pickC_cost, children_length, children_length]
    have h2 := cV_act_card_le i
    have h3 := cV_coord_card (k := k) ((pgIdx k i).1, pgCoord (pgIdx k i).1 (zt s))
    omega
  · rw [hl, Fin.lastCases_last]
    omega

end Select

/-! ## Costed initialisation -/

section Init

/-- **Raw initialisation pass**: for every listed vertex write the initial value `y` and
reset its heap to the empty heap, 2 units per vertex. -/
def rawInit (y : NNReal) : List ℕ → HEState NNReal → HEState NNReal × ℕ
  | [], s => (s, 0)
  | g :: gs, s =>
    ((rawInit y gs ⟨Function.update s.val g y, Function.update s.hp g Heap.empty⟩).1,
     (rawInit y gs ⟨Function.update s.val g y, Function.update s.hp g Heap.empty⟩).2 + 2)

lemma rawInit_spec (y : NNReal) : ∀ (gs : List ℕ) (s : HEState NNReal),
    (∀ g, (rawInit y gs s).1.val g = if g ∈ gs then y else s.val g) ∧
    (∀ g, (rawInit y gs s).1.hp g = if g ∈ gs then Heap.empty else s.hp g) ∧
    (rawInit y gs s).2 = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro s; exact ⟨fun g => by simp [rawInit], fun g => by simp [rawInit], rfl⟩
  | cons g gs ih =>
    intro s
    obtain ⟨h1, h2, h3⟩ := ih ⟨Function.update s.val g y, Function.update s.hp g Heap.empty⟩
    refine ⟨fun g' => ?_, fun g' => ?_, ?_⟩
    · show (rawInit y gs _).1.val g' = _
      rw [h1 g']
      by_cases hm : g' ∈ gs
      · simp [hm]
      · by_cases e : g' = g
        · subst e
          simp [hm]
        · simp [hm, e]
    · show (rawInit y gs _).1.hp g' = _
      rw [h2 g']
      by_cases hm : g' ∈ gs
      · simp [hm]
      · by_cases e : g' = g
        · subst e
          simp [hm]
        · simp [hm, e]
    · show (rawInit y gs _).2 + 2 = _
      rw [h3, List.length_cons]
      ring

/-- **Costed filter scan**: one unit per element. -/
def filterC (p : ℕ → Bool) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | g :: gs => (if p g = true then g :: (filterC p gs).1 else (filterC p gs).1,
      (filterC p gs).2 + 1)

lemma filterC_spec (p : ℕ → Bool) : ∀ l : List ℕ, filterC p l = (l.filter p, l.length)
  | [] => rfl
  | g :: gs => by
    have ih := filterC_spec p gs
    show (if p g = true then g :: (filterC p gs).1 else (filterC p gs).1,
      (filterC p gs).2 + 1) = _
    rw [ih]
    by_cases h : p g = true <;> simp [h]

lemma nonemptyB_iff (l : List ℕ) : (!l.isEmpty) = true ↔ l ≠ [] := by
  cases l <;> simp

lemma sum_filter_range_le (f : ℕ → ℕ) (p : ℕ → Bool) :
    ∀ N, (((List.range N).filter p).map f).sum ≤ ∑ g ∈ range N, f g
  | 0 => by simp
  | N + 1 => by
    have ih := sum_filter_range_le f p N
    have h1 : (([N].filter p).map f).sum ≤ f N := by
      by_cases h : p N = true <;> simp [h]
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      Finset.sum_range_succ]
    omega

/-- On a constant state, initialising an internal gate changes nothing. -/
lemma initGate_const (G : Dag) (g : ℕ) (y : NNReal) (hg : G.children g ≠ []) :
    (initGate G g (⟨fun _ => y, fun _ _ => y⟩ : EState NNReal)).1
      = ⟨fun _ => y, fun _ _ => y⟩ := by
  have hk : (insKeys (G.children g).length g (fun _ => y) (G.children g)
      (fun _ _ => y)).1 = fun _ _ => y := by
    funext p c
    rw [(insKeys_spec (G.children g).length g (fun _ => y) (G.children g) (fun _ _ => y)).1 p c]
    split_ifs <;> rfl
  show (⟨fun g' => if g' = g then
          heapMax (G.children g)
            ((insKeys (G.children g).length g (fun _ => y) (G.children g)
              (fun _ _ => y)).1 g)
        else y,
      (insKeys (G.children g).length g (fun _ => y) (G.children g) (fun _ _ => y)).1⟩ :
      EState NNReal) = _
  rw [hk]
  have hv : (fun g' => if g' = g then heapMax (G.children g) (fun _ => y) else y)
      = fun _ => y := by
    funext g'
    split_ifs
    · exact heapMax_const _ y hg
    · rfl
  rw [hv]

lemma initPass_const (G : Dag) (y : NNReal) : ∀ order : List ℕ,
    (∀ g ∈ order, G.children g ≠ []) →
    (initPass G order (⟨fun _ => y, fun _ _ => y⟩ : EState NNReal)).1
      = ⟨fun _ => y, fun _ _ => y⟩ := by
  intro order
  induction order with
  | nil => intro _; rfl
  | cons g rest ih =>
    intro h
    show (initPass G rest (initGate G g _).1).1 = _
    rw [initGate_const G g y (h g List.mem_cons_self)]
    exact ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

lemma initPass_cost (G : Dag) : ∀ (order : List ℕ) (s : EState NNReal),
    (initPass G order s).2 = (order.map (initCost G)).sum := by
  intro order
  induction order with
  | nil => intro s; rfl
  | cons g rest ih =>
    intro s
    show (initGate G g s).2 + (initPass G rest (initGate G g s).1).2 = _
    rw [(initGate_spec G g s).2.2.2.2, ih, List.map_cons, List.sum_cons]

/-- **Costed initialisation of one endpoint** from raw memory: `rawInit` over the `N`
vertices, the scan selecting the internal gates, and the heap-building pass
`EngineFinal.initPassH` over them. -/
def initEndC (G : Dag) (y : NNReal) (raw : HEState NNReal) : HEState NNReal × ℕ :=
  ((initPassH G (filterC (fun g => !(G.children g).isEmpty) (List.range G.N)).1
      (rawInit y (List.range G.N) raw).1).1,
   (rawInit y (List.range G.N) raw).2
    + (filterC (fun g => !(G.children g).isEmpty) (List.range G.N)).2
    + (initPassH G (filterC (fun g => !(G.children g).isEmpty) (List.range G.N)).1
        (rawInit y (List.range G.N) raw).1).2)

/-- **Correctness and cost of the initialisation.**  If the child lists are free of
repetitions, internal gates have indices below `N`, and the memory cells outside `[0, N)`
hold the default (`y`, empty heap), the initialised implemented state represents the
constant engine state `y`, at computed cost at most
`3N + 2 (N + (⌈log₂ D⌉ + 1) |E|)`. -/
theorem initEndC_spec (G : Dag) (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D)
    (hnd : ∀ g, (G.children g).Nodup) (hlt : ∀ g, G.children g ≠ [] → g < G.N) (y : NNReal)
    (raw : HEState NNReal) (hraw : ∀ g, G.N ≤ g → raw.val g = y ∧ raw.hp g = Heap.empty) :
    SimE G (initEndC G y raw).1 (⟨fun _ => y, fun _ _ => y⟩ : EState NNReal) ∧
    (initEndC G y raw).2 ≤ 3 * G.N + 2 * (G.N + (Nat.clog 2 D + 1) * live G) := by
  obtain ⟨r1, r2, r3⟩ := rawInit_spec y (List.range G.N) raw
  have hval : (rawInit y (List.range G.N) raw).1.val = fun _ => y := by
    funext g
    rw [r1 g]
    by_cases hg : g < G.N
    · rw [ite_eq_left (List.mem_range.2 hg)]
    · rw [ite_eq_right (fun h => hg (List.mem_range.1 h))]
      exact (hraw g (not_lt.1 hg)).1
  have hemp : ∀ p, (rawInit y (List.range G.N) raw).1.hp p = Heap.empty := by
    intro g
    rw [r2 g]
    by_cases hg : g < G.N
    · rw [ite_eq_left (List.mem_range.2 hg)]
    · rw [ite_eq_right (fun h => hg (List.mem_range.1 h))]
      exact (hraw g (not_lt.1 hg)).2
  have hf := filterC_spec (fun g => !(G.children g).isEmpty) (List.range G.N)
  have hall : ∀ g, G.children g ≠ [] →
      g ∈ (List.range G.N).filter (fun g => !(G.children g).isEmpty) := fun g hg =>
    List.mem_filter.2 ⟨List.mem_range.2 (hlt g hg), (nonemptyB_iff _).2 hg⟩
  have hint : ∀ g ∈ (List.range G.N).filter (fun g => !(G.children g).isEmpty),
      G.children g ≠ [] := fun g hg => (nonemptyB_iff _).1 (List.mem_filter.1 hg).2
  obtain ⟨s1, s2⟩ := initPassH_sim (G := G)
    ((List.range G.N).filter (fun g => !(G.children g).isEmpty))
    (rawInit y (List.range G.N) raw).1 (⟨fun _ => y, fun _ _ => y⟩ : EState NNReal)
    hnd hall hval hemp
  rw [initPass_const G y _ hint] at s1
  rw [initPass_cost] at s2
  have c1 := initCost_sum_le G D hD ((List.range G.N).filter (fun g => !(G.children g).isEmpty))
  have c2 : ((List.range G.N).filter (fun g => !(G.children g).isEmpty)).length ≤ G.N :=
    (List.length_filter_le _ _).trans (le_of_eq List.length_range)
  have c3 : (((List.range G.N).filter (fun g => !(G.children g).isEmpty)).map
      (fun g => (G.children g).length)).sum ≤ live G := sum_filter_range_le _ _ _
  have c4 := Nat.mul_le_mul_left (Nat.clog 2 D + 1) c3
  have e1 : (initEndC G y raw).1
      = (initPassH G ((List.range G.N).filter (fun g => !(G.children g).isEmpty))
          (rawInit y (List.range G.N) raw).1).1 := by
    unfold initEndC
    rw [hf]
  have e2 : (initEndC G y raw).2
      = (rawInit y (List.range G.N) raw).2 + (List.range G.N).length
        + (initPassH G ((List.range G.N).filter (fun g => !(G.children g).isEmpty))
          (rawInit y (List.range G.N) raw).1).2 := by
    unfold initEndC
    rw [hf]
  refine ⟨e1 ▸ s1, ?_⟩
  rw [e2, r3, List.length_range]
  omega

end Init

/-! ## The eager engine on implemented heaps -/

section EagerH

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Interval wave on implemented heaps: one `HeapImpl.waveH` per endpoint. -/
def ivWaveH (G : Dag) (x : ℕ) (yl yu : α) (s : HEState α × HEState α) :
    (HEState α × HEState α) × ℕ :=
  (((waveH G x yl s.1).1, (waveH G x yu s.2).1), (waveH G x yl s.1).2 + (waveH G x yu s.2).2)

/-- State of the eager engine on implemented heaps after `t` rollouts. -/
def runStateH (G : Dag) (u : ℕ → ℕ × α × α) (s0 : HEState α × HEState α) :
    ℕ → HEState α × HEState α
  | 0 => s0
  | t + 1 => (ivWaveH G (u (t + 1)).1 (u (t + 1)).2.1 (u (t + 1)).2.2 (runStateH G u s0 t)).1

/-- Computed cost of the interval wave of rollout `t + 1` on implemented heaps. -/
def waveCostH (G : Dag) (u : ℕ → ℕ × α × α) (s0 : HEState α × HEState α) (t : ℕ) : ℕ :=
  (ivWaveH G (u (t + 1)).1 (u (t + 1)).2.1 (u (t + 1)).2.2 (runStateH G u s0 t)).2

/-- The implemented eager engine simulates `CostEngines.runState`. -/
theorem runStateH_sim (G : Dag) (u : ℕ → ℕ × α × α) {hs0 : HEState α × HEState α}
    {s0 : EState α × EState α} (h1 : SimE G hs0.1 s0.1) (h2 : SimE G hs0.2 s0.2) : ∀ t,
    SimE G (runStateH G u hs0 t).1 (runState G u s0 t).1 ∧
    SimE G (runStateH G u hs0 t).2 (runState G u s0 t).2 := by
  intro t
  induction t with
  | zero => exact ⟨h1, h2⟩
  | succ t ih =>
    exact ⟨(HeapImpl.waveH_sim G (u (t + 1)).1 (u (t + 1)).2.1 _ _ ih.1).1,
      (HeapImpl.waveH_sim G (u (t + 1)).1 (u (t + 1)).2.2 _ _ ih.2).1⟩

/-- Each implemented interval wave costs at most twice the charged wave. -/
theorem waveCostH_le (G : Dag) (u : ℕ → ℕ × α × α) {hs0 : HEState α × HEState α}
    {s0 : EState α × EState α} (h1 : SimE G hs0.1 s0.1) (h2 : SimE G hs0.2 s0.2) (t : ℕ) :
    waveCostH G u hs0 t ≤ 2 * waveCost G u s0 (t + 1) := by
  obtain ⟨a, b⟩ := runStateH_sim G u h1 h2 t
  have c1 := (HeapImpl.waveH_sim G (u (t + 1)).1 (u (t + 1)).2.1 _ _ a).2
  have c2 := (HeapImpl.waveH_sim G (u (t + 1)).1 (u (t + 1)).2.2 _ _ b).2
  show (waveH G (u (t + 1)).1 (u (t + 1)).2.1 (runStateH G u hs0 t).1).2 +
      (waveH G (u (t + 1)).1 (u (t + 1)).2.2 (runStateH G u hs0 t).2).2 ≤
    2 * ((wave G (u (t + 1)).1 (u (t + 1)).2.1 (runState G u s0 t).1).2 +
      (wave G (u (t + 1)).1 (u (t + 1)).2.2 (runState G u s0 t).2).2)
  exact le_trans (Nat.add_le_add c1 c2) (le_of_eq (Nat.mul_add 2 _ _).symm)

end EagerH

/-! ## Arithmetic -/

section Arith

lemma arith_eag {I R W Q r k T Y : ℕ} (hI : I ≤ 70 * (r * r) + (k + 3) * (44 * (r * r)))
    (hR : R ≤ T * (7 * r + 6)) (hW : W ≤ T * (2 * (2 * (6 + Y))))
    (hQ : Q ≤ (T + 1) * (8 * r)) :
    I + R + W + Q
      ≤ 70 * (r * r) + 8 * r + (k + 3) * (44 * (r * r)) + T * (15 * r + 30 + 4 * Y) := by
  have e : T * (15 * r + 30 + 4 * Y)
      = T * (7 * r + 6) + T * (2 * (2 * (6 + Y))) + T * (8 * r) := by ring
  have e2 : (T + 1) * (8 * r) = T * (8 * r) + 8 * r := by ring
  rw [e]
  rw [e2] at hQ
  omega

lemma arith_sel {I R C S Q r k T Z : ℕ} (hI : I ≤ 70 * (r * r) + (k + 3) * (44 * (r * r)))
    (hR : R ≤ T * (7 * r + 6)) (hC : C ≤ 2 * S)
    (hS : S ≤ 36 * (r * r) + (2 * k + 8) * (11 * (r * r)) + T * (16 * r + 12 + Z))
    (hQ : Q ≤ 8 * r) :
    I + R + C + Q
      ≤ 142 * (r * r) + 8 * r + (k + 3) * (44 * (r * r)) + (2 * k + 8) * (22 * (r * r))
        + T * (39 * r + 30 + 2 * Z) := by
  have e : T * (39 * r + 30 + 2 * Z) = T * (7 * r + 6) + 2 * (T * (16 * r + 12 + Z)) := by ring
  have e2 : (2 * k + 8) * (22 * (r * r)) = 2 * ((2 * k + 8) * (11 * (r * r))) := by ring
  rw [e, e2]
  omega

end Arith

/-! ## The two monitors with computed costs on the parity grid -/

section Monitors

variable {k : ℕ}

lemma pg_children_nodup (g : ℕ) : ((pgDag k).children g).Nodup := by
  by_cases hg : g < pgN k
  · rw [← gid_gof g hg, children_gid]
    exact (Finset.nodup_toList _).map gid_injective
  · rw [children_of_not_lt hg]
    exact List.nodup_nil

lemma pg_internal_lt (g : ℕ) (h : (pgDag k).children g ≠ []) : g < (pgDag k).N := by
  by_contra hn
  exact h (children_of_not_lt hn)

/-- Raw memory of one endpoint: arbitrary inside the vertex range, default (`y`, empty heap)
outside it. -/
def RawOK (k : ℕ) (y : NNReal) (raw : HEState NNReal) : Prop :=
  ∀ g, (pgDag k).N ≤ g → raw.val g = y ∧ raw.hp g = Heap.empty

/-- Implemented initial state of the lower endpoints. -/
def hl0 (k : ℕ) (rawL : HEState NNReal) : HEState NNReal := (initEndC (pgDag k) ⊥ rawL).1

/-- Implemented initial state of the upper endpoints. -/
def hu0 (k : ℕ) (rawU : HEState NNReal) : HEState NNReal := (initEndC (pgDag k) 1 rawU).1

/-- Computed initialisation work (both endpoints). -/
def initC (k : ℕ) (rawL rawU : HEState NNReal) : ℕ :=
  (initEndC (pgDag k) ⊥ rawL).2 + (initEndC (pgDag k) 1 rawU).2

/-- **Initialisation on the parity grid.**  The costed initialisation produces implemented
states representing the initial engine state `pgInit` of `coded_main`, at computed cost at
most `70 r² + 44 (k + 3) r²`. -/
theorem init_sim {rawL rawU : HEState NNReal} (hL : RawOK k ⊥ rawL) (hU : RawOK k 1 rawU) :
    SimE (pgDag k) (hl0 k rawL) (pgInit k).1 ∧ SimE (pgDag k) (hu0 k rawU) (pgInit k).2 ∧
    initC k rawL rawU ≤ 70 * (2 ^ k * 2 ^ k) + (k + 3) * (44 * (2 ^ k * 2 ^ k)) := by
  obtain ⟨a1, a2⟩ := initEndC_spec (pgDag k) (4 * 2 ^ k) pgDag_degree pg_children_nodup
    pg_internal_lt ⊥ rawL hL
  obtain ⟨b1, b2⟩ := initEndC_spec (pgDag k) (4 * 2 ^ k) pgDag_degree pg_children_nodup
    pg_internal_lt 1 rawU hU
  refine ⟨a1, b1, ?_⟩
  have hcl : Nat.clog 2 (4 * 2 ^ k) ≤ k + 2 :=
    Nat.clog_le_of_le_pow (by rw [pow_succ, pow_succ]; omega)
  have hlive : live (pgDag k) = pgE k := rfl
  obtain ⟨-, hN, -, hE⟩ := pgDag_size (k := k)
  rw [hlive] at a2 b2
  have A := Nat.mul_le_mul (show Nat.clog 2 (4 * 2 ^ k) + 1 ≤ k + 3 by omega) hE
  have e : (k + 3) * (44 * (2 ^ k * 2 ^ k)) = 4 * ((k + 3) * (11 * (2 ^ k * 2 ^ k))) := by ring
  rw [e]
  unfold initC
  omega

variable {x : GridTerminal k → ℕ → ℝ} {zt : ℕ → GridTerminal k} {δ : ℝ}

/-! ### Graph Eager with computed costs -/

/-- State of the implemented eager engine after `t` rollouts. -/
def hsE (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k)
    (rawL rawU : HEState NNReal) (t : ℕ) : HEState NNReal × HEState NNReal :=
  runStateH (pgDag k) (pgUpd δ x zt) (hl0 k rawL, hu0 k rawU) t

/-- **Costed root query of the implemented eager engine** after `t` rollouts: output and
cost. -/
def qEagC (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k)
    (rawL rawU : HEState NNReal) (t : ℕ) : (Option ℕ × Bool) × ℕ :=
  qOutC cR (1 / 5) (pgD k + 1) (fun i => (hsE δ x zt rawL rawU t).1.val (pgRt k i))
    (fun i => (hsE δ x zt rawL rawU t).2.val (pgRt k i)) (fun _ => true)

/-- The costed query on the implemented eager engine returns the output `qEag` of the
eager monitor of `coded_main` (so it stops exactly when `pgStops` holds, by
`LiteralK2.qEag_iff`), at cost at most `2 (d + 1)`. -/
theorem qEagC_spec {rawL rawU : HEState NNReal} (hL : RawOK k ⊥ rawL) (hU : RawOK k 1 rawU)
    (t : ℕ) :
    (qEagC δ x zt rawL rawU t).1 = qEag δ x zt t ∧
    (qEagC δ x zt rawL rawU t).2 ≤ 2 * (pgD k + 1) := by
  obtain ⟨sl, su, _⟩ := init_sim hL hU
  obtain ⟨a, b⟩ := runStateH_sim (pgDag k) (pgUpd δ x zt)
    (hs0 := (hl0 k rawL, hu0 k rawU)) (s0 := pgInit k) sl su t
  obtain ⟨q1, q2⟩ := qOutC_spec cR (1 / 5) (pgD k + 1)
    (fun i => (hsE δ x zt rawL rawU t).1.val (pgRt k i))
    (fun i => (hsE δ x zt rawL rawU t).2.val (pgRt k i)) (fun _ => true)
  refine ⟨?_, q2⟩
  have e1 : (hsE δ x zt rawL rawU t).1.val = (pgState δ x zt t).1.val := a.val
  have e2 : (hsE δ x zt rawL rawU t).2.val = (pgState δ x zt t).2.val := b.val
  unfold qEagC qEag
  rw [q1, e1, e2]

/-- **Computed total work of `T` rollouts under Graph Eager**: initialisation, allocator
scans of every rollout, the implemented interval wave of every rollout, and a costed root
query at each of the times `0, …, T`. -/
def pgWorkC (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (idx : ℕ → ℕ → ℝ) (rawL rawU : HEState NNReal) (T : ℕ) : ℕ :=
  initC k rawL rawU + ∑ s ∈ range T, rolloutC x sel zt idx s
    + ∑ t ∈ range T, waveCostH (pgDag k) (pgUpd δ x zt) (hl0 k rawL, hu0 k rawU) t
    + ∑ t ∈ range (T + 1), (qEagC δ x zt rawL rawU t).2

/-- **Computed work under Graph Eager, in natural numbers.** -/
theorem pgWorkC_le {rawL rawU : HEState NNReal} (hL : RawOK k ⊥ rawL) (hU : RawOK k 1 rawU)
    (sel : ℕ → Fin (pgD k + 1)) (idx : ℕ → ℕ → ℝ) (T : ℕ) :
    pgWorkC δ x sel zt idx rawL rawU T
      ≤ 70 * (2 ^ k * 2 ^ k) + 8 * 2 ^ k + (k + 3) * (44 * (2 ^ k * 2 ^ k))
        + T * (15 * 2 ^ k + 30 + 4 * ((k + 5) * (4 * 2 ^ k + 2))) := by
  obtain ⟨sl, su, h0⟩ := init_sim hL hU
  have h1 : ∑ s ∈ range T, rolloutC x sel zt idx s ≤ T * (7 * 2 ^ k + 6) := by
    have := Finset.sum_le_card_nsmul (range T) (fun s => rolloutC x sel zt idx s)
      (7 * 2 ^ k + 6) (fun s _ => rolloutC_le x sel zt idx s)
    rwa [card_range, smul_eq_mul] at this
  have h2 : ∑ t ∈ range T, waveCostH (pgDag k) (pgUpd δ x zt) (hl0 k rawL, hu0 k rawU) t
      ≤ T * (2 * (2 * (6 + (k + 5) * (4 * 2 ^ k + 2)))) := by
    have := Finset.sum_le_card_nsmul (range T)
      (fun t => waveCostH (pgDag k) (pgUpd δ x zt) (hl0 k rawL, hu0 k rawU) t)
      (2 * (2 * (6 + (k + 5) * (4 * 2 ^ k + 2))))
      (fun t _ => (waveCostH_le (pgDag k) (pgUpd δ x zt)
          (hs0 := (hl0 k rawL, hu0 k rawU)) (s0 := pgInit k) sl su t).trans
        (Nat.mul_le_mul_left 2 (pgWave_le δ x zt (t + 1) (Nat.le_add_left 1 t))))
    rwa [card_range, smul_eq_mul] at this
  have hq : ∀ t, (qEagC δ x zt rawL rawU t).2 ≤ 8 * 2 ^ k := fun t =>
    (qEagC_spec hL hU t).2.trans (by have := pgD_le (k := k); omega)
  have h3 : ∑ t ∈ range (T + 1), (qEagC δ x zt rawL rawU t).2 ≤ (T + 1) * (8 * 2 ^ k) := by
    have := Finset.sum_le_card_nsmul (range (T + 1))
      (fun t => (qEagC δ x zt rawL rawU t).2) (8 * 2 ^ k) (fun t _ => hq t)
    rwa [card_range, smul_eq_mul] at this
  unfold pgWorkC
  exact arith_eag h0 h1 h2 h3

/-! ### Graph Selective with computed costs -/

/-- State of the implemented Graph-Selective engine after `t` rollouts
(`RetireFinal.runH`: delivery retirement policy, query with root retirement after every
rollout), started from the costed initialisation. -/
def hsS (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k)
    (rawL rawU : HEState NNReal) (t : ℕ) : HQS NNReal :=
  runH (pgD k + 1) (pgRt k) delivV (pgUpd δ x zt) (fun _ => true)
    ⟨⟨pgDag k, hl0 k rawL, hu0 k rawU⟩, fun _ => true⟩ t

/-- **Costed root query of the implemented Graph-Selective engine** after `t` rollouts. -/
def qSelC (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k)
    (rawL rawU : HEState NNReal) (t : ℕ) : (Option ℕ × Bool) × ℕ :=
  qOutC cR (1 / 5) (pgD k + 1) (fun i => (hsS δ x zt rawL rawU t).r.lo.val (pgRt k i))
    (fun i => (hsS δ x zt rawL rawU t).r.hi.val (pgRt k i)) (hsS δ x zt rawL rawU t).act

/-- Computed engine cost of the implemented Graph-Selective engine for the query at time
`t` and rollout `t + 1` (`RetireFinal.costH`). -/
def selCostH (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k)
    (rawL rawU : HEState NNReal) (t : ℕ) : ℕ :=
  costH (pgD k + 1) (pgRt k) delivV (pgUpd δ x zt) (fun _ => true)
    ⟨⟨pgDag k, hl0 k rawL, hu0 k rawU⟩, fun _ => true⟩ t

/-- On the coverage event, the costed query on the implemented Graph-Selective engine
returns the output `qEag` of the eager monitor, at cost at most `2 (d + 1)`. -/
theorem qSelC_spec (hx : PGTape x) {m : GridTerminal k → ℝ}
    (hcov : tapeCovered (pgM k) δ x zt m) {rawL rawU : HEState NNReal}
    (hL : RawOK k ⊥ rawL) (hU : RawOK k 1 rawU) (t : ℕ) :
    (qSelC δ x zt rawL rawU t).1 = qEag δ x zt t ∧
    (qSelC δ x zt rawL rawU t).2 ≤ 2 * (pgD k + 1) := by
  obtain ⟨sl, su, _⟩ := init_sim hL hU
  obtain ⟨q1, q2⟩ := qOutC_spec cR (1 / 5) (pgD k + 1)
    (fun i => (hsS δ x zt rawL rawU t).r.lo.val (pgRt k i))
    (fun i => (hsS δ x zt rawL rawU t).r.hi.val (pgRt k i)) (hsS δ x zt rawL rawU t).act
  refine ⟨q1.trans ?_, q2⟩
  exact (ram_work_bounds_impl (K := pgD k + 1) (rt := pgRt k) pgDag_wf (4 * 2 ^ k)
    pgDag_degree (pg_h0 k) (pg_nested hx hcov) (by omega) cR cR_strictMono (1 / 5)
    (by norm_num) (fun _ => true) 0 0 ⟨pgDag k, hl0 k rawL, hu0 k rawU⟩ ⟨rfl, sl, su⟩).1 t

/-- Each step of the implemented Graph-Selective engine costs at most twice the charged
step `LiteralK2.selCost`. -/
theorem selCostH_le {rawL rawU : HEState NNReal} (hL : RawOK k ⊥ rawL) (hU : RawOK k 1 rawU)
    (t : ℕ) : selCostH δ x zt rawL rawU t ≤ 2 * selCost δ x zt t := by
  obtain ⟨sl, su, _⟩ := init_sim hL hU
  exact (runH_sim (K := pgD k + 1) (rt := pgRt k) delivV (pgUpd δ x zt) (fun _ => true)
    (hs0 := ⟨⟨pgDag k, hl0 k rawL, hu0 k rawU⟩, fun _ => true⟩)
    (s0 := ⟨⟨pgDag k, (pgInit k).1, (pgInit k).2⟩, fun _ => true⟩) ⟨⟨rfl, sl, su⟩, rfl⟩ t).2

/-- **Computed total work of `T` rollouts under Graph Selective**: initialisation,
allocator scans of every rollout, the computed engine cost (queries at times `0, …, T - 1`
and rollouts `1, …, T`), and the costed final query at time `T`. -/
def selWorkC (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (idx : ℕ → ℕ → ℝ) (rawL rawU : HEState NNReal) (T : ℕ) : ℕ :=
  initC k rawL rawU + ∑ s ∈ range T, rolloutC x sel zt idx s
    + ∑ t ∈ range T, selCostH δ x zt rawL rawU t + (qSelC δ x zt rawL rawU T).2

/-- **Computed work under Graph Selective, in natural numbers.** -/
theorem selWorkC_le (hx : PGTape x) {m : GridTerminal k → ℝ}
    (hcov : tapeCovered (pgM k) δ x zt m) {rawL rawU : HEState NNReal}
    (hL : RawOK k ⊥ rawL) (hU : RawOK k 1 rawU)
    (sel : ℕ → Fin (pgD k + 1)) (idx : ℕ → ℕ → ℝ) (T : ℕ) :
    selWorkC δ x sel zt idx rawL rawU T
      ≤ 142 * (2 ^ k * 2 ^ k) + 8 * 2 ^ k + (k + 3) * (44 * (2 ^ k * 2 ^ k))
        + (2 * k + 8) * (22 * (2 ^ k * 2 ^ k))
        + T * (39 * 2 ^ k + 30 + 2 * ((k + 7) * (8 * 2 ^ k + 4))) := by
  obtain ⟨_, _, h0⟩ := init_sim hL hU
  have h1 : ∑ s ∈ range T, rolloutC x sel zt idx s ≤ T * (7 * 2 ^ k + 6) := by
    have := Finset.sum_le_card_nsmul (range T) (fun s => rolloutC x sel zt idx s)
      (7 * 2 ^ k + 6) (fun s _ => rolloutC_le x sel zt idx s)
    rwa [card_range, smul_eq_mul] at this
  have h2 : ∑ t ∈ range T, selCostH δ x zt rawL rawU t
      ≤ 2 * ∑ t ∈ range T, selCost δ x zt t := by
    rw [mul_sum]
    exact sum_le_sum (fun t _ => selCostH_le hL hU t)
  have h3 := selCost_sum_le hx hcov T
  have h4 : (qSelC δ x zt rawL rawU T).2 ≤ 8 * 2 ^ k :=
    (qSelC_spec hx hcov hL hU T).2.trans (by have := pgD_le (k := k); omega)
  unfold selWorkC
  exact arith_sel h0 h1 h2 h3 h4

end Monitors

/-! ## Assembly with computed costs -/

section Final

/-- Real arithmetic for the selective bound. -/
lemma sel_real {r ℓ k τ A : ℝ} (hr4 : 4 ≤ r) (hℓ1 : 1 ≤ ℓ) (hk0 : 0 ≤ k) (hk2 : k ≤ 2 * ℓ)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ A * r * ℓ) :
    142 * (r * r) + 8 * r + (k + 3) * (44 * (r * r)) + (2 * k + 8) * (22 * (r * r))
      + τ * (39 * r + 30 + 2 * ((k + 7) * (8 * r + 4))) ≤ (209 * A + 628) * r ^ 2 * ℓ ^ 2 := by
  have hrℓ : r ≤ r * ℓ := le_mul_of_one_le_right (by linarith) hℓ1
  have hk7 : k + 7 ≤ 9 * ℓ := by linarith
  have h84 : 8 * r + 4 ≤ 9 * r := by linarith
  have hp : (k + 7) * (8 * r + 4) ≤ 9 * ℓ * (9 * r) :=
    mul_le_mul hk7 h84 (by linarith) (by linarith)
  have e81 : 9 * ℓ * (9 * r) = 81 * (r * ℓ) := by ring
  have hP : 39 * r + 30 + 2 * ((k + 7) * (8 * r + 4)) ≤ 209 * (r * ℓ) := by
    rw [e81] at hp
    linarith
  have hP0 : 0 ≤ 39 * r + 30 + 2 * ((k + 7) * (8 * r + 4)) := by
    have : 0 ≤ (k + 7) * (8 * r + 4) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hA0 : 0 ≤ A * r * ℓ := hτ0.trans hτ
  have h1 : τ * (39 * r + 30 + 2 * ((k + 7) * (8 * r + 4))) ≤ A * r * ℓ * (209 * (r * ℓ)) :=
    mul_le_mul hτ hP hP0 hA0
  have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
  have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hrr : r * r = r ^ 2 := by ring
  have hc : r ^ 2 ≤ r ^ 2 * ℓ ^ 2 := le_mul_of_one_le_right hr2 hℓ2
  have hc' : r ^ 2 * ℓ ≤ r ^ 2 * ℓ ^ 2 := mul_le_mul_of_nonneg_left hℓℓ hr2
  have c1 : 142 * (r * r) + 8 * r ≤ 144 * (r ^ 2 * ℓ ^ 2) := by
    have hb : 8 * r ≤ 2 * r ^ 2 := by nlinarith
    rw [hrr]
    linarith
  have c2 : (k + 3) * (44 * (r * r)) ≤ 220 * (r ^ 2 * ℓ ^ 2) := by
    have h : (k + 3) * (44 * (r * r)) ≤ 5 * ℓ * (44 * (r * r)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : 5 * ℓ * (44 * (r * r)) = 220 * (r ^ 2 * ℓ) := by ring
    linarith
  have c3 : (2 * k + 8) * (22 * (r * r)) ≤ 264 * (r ^ 2 * ℓ ^ 2) := by
    have h : (2 * k + 8) * (22 * (r * r)) ≤ 12 * ℓ * (22 * (r * r)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : 12 * ℓ * (22 * (r * r)) = 264 * (r ^ 2 * ℓ) := by ring
    linarith
  have e : (209 * A + 628) * r ^ 2 * ℓ ^ 2
      = A * r * ℓ * (209 * (r * ℓ)) + 628 * (r ^ 2 * ℓ ^ 2) := by ring
  linarith

/-- Real arithmetic for the eager bound (reduced to the selective one). -/
lemma eag_real {r ℓ k τ A : ℝ} (hr4 : 4 ≤ r) (hℓ1 : 1 ≤ ℓ) (hk0 : 0 ≤ k) (hk2 : k ≤ 2 * ℓ)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ A * r * ℓ) :
    70 * (r * r) + 8 * r + (k + 3) * (44 * (r * r))
      + τ * (15 * r + 30 + 4 * ((k + 5) * (4 * r + 2))) ≤ (209 * A + 628) * r ^ 2 * ℓ ^ 2 := by
  have hs := sel_real hr4 hℓ1 hk0 hk2 hτ0 hτ
  have e : 2 * ((k + 7) * (8 * r + 4)) - 4 * ((k + 5) * (4 * r + 2)) = 4 * (8 * r + 4) := by
    ring
  have hle : 15 * r + 30 + 4 * ((k + 5) * (4 * r + 2))
      ≤ 39 * r + 30 + 2 * ((k + 7) * (8 * r + 4)) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hle hτ0
  have h2 : 0 ≤ (2 * k + 8) * (22 * (r * r)) := mul_nonneg (by linarith) (by positivity)
  have h3 : 0 ≤ r * r := by positivity
  linarith

variable {k : ℕ}

/-- The pathwise conclusion with computed costs, for a search `(sel, zt)` on the tapes `x`,
selection scans below the root with index `idx`, and raw memories `rawL`, `rawU`.  There is
a rollout count `τ` such that the eager root query first stops at `τ` and recommends `w*`
(index `d`), every successful query recommends `w*`, the costed queries of BOTH implemented
engines return the eager output `qEag` at every time (so both first stop at `τ` with `w*`),
`τ ≤ A r log r`, and the computed total work of each engine up to `τ` is at most
`B r² log² r`. -/
def PGCertifiedComputed (δ A B : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (idx : ℕ → ℕ → ℝ) (rawL rawU : HEState NNReal) : Prop :=
  ∃ τ : ℕ, pgStops δ x zt τ (Fin.last _) ∧
    (∀ t, t < τ → ∀ a, ¬ pgStops δ x zt t a) ∧
    (∀ t a, pgStops δ x zt t a → a = Fin.last _) ∧
    (∀ t (a : Fin (pgD k + 1)), qEag δ x zt t = (some (a : ℕ), true) ↔ pgStops δ x zt t a) ∧
    (∀ t, (qEagC δ x zt rawL rawU t).1 = qEag δ x zt t) ∧
    (∀ t, (qSelC δ x zt rawL rawU t).1 = qEag δ x zt t) ∧
    (qEagC δ x zt rawL rawU τ).1 = (some (pgD k), true) ∧
    (qSelC δ x zt rawL rawU τ).1 = (some (pgD k), true) ∧
    (∀ t, t < τ → (qEagC δ x zt rawL rawU t).1.2 = false ∧
      (qSelC δ x zt rawL rawU t).1.2 = false) ∧
    (τ : ℝ) ≤ A * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) ∧
    (pgWorkC δ x sel zt idx rawL rawU τ : ℝ)
      ≤ B * ((2 : ℝ) ^ k) ^ 2 * Real.log ((2 : ℝ) ^ k) ^ 2 ∧
    (selWorkC δ x sel zt idx rawL rawU τ : ℝ)
      ≤ B * ((2 : ℝ) ^ k) ^ 2 * Real.log ((2 : ℝ) ^ k) ^ 2

/-- **Step 3 of `thm:coded-main` / `thm:coded-covers`, pathwise, with computed costs, for
both engines on implemented heaps.**  Fix `δ ∈ (0, 1)`.  There are constants `A, B` such
that for every `k ≥ 2`, every reward tape with the stated ranges, every UCT search on the
parity-grid DAG, every index used by the selection scans below the root, every pair of raw
memories that hold the default value outside the vertex range, and every run on the coverage
event, `PGCertifiedComputed` holds. -/
theorem parity_certified_computed {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1)) (zt : ℕ → GridTerminal k)
        (idx : ℕ → ℕ → ℝ) (rawL rawU : HEState NNReal),
      RawOK k ⊥ rawL → RawOK k 1 rawU →
      PGTape x → ParitySearch x sel zt → tapeCovered (pgM k) δ x zt (pgMean k) →
      PGCertifiedComputed δ A B x sel zt idx rawL rawU := by
  obtain ⟨A, B, hA, hB, hpath⟩ := parity_certified_both hδ0 hδ1
  refine ⟨A, 209 * A + 628, hA, by linarith, ?_⟩
  intro k hk x sel zt idx rawL rawU hL hU hx h hcov
  obtain ⟨τ, c1, c2, c3, c4, c5, c6, c7, _, c9, _, _⟩ := hpath k hk x sel zt hx h hcov
  have hE : ∀ t, (qEagC δ x zt rawL rawU t).1 = qEag δ x zt t := fun t =>
    (qEagC_spec hL hU t).1
  have hS : ∀ t, (qSelC δ x zt rawL rawU t).1 = qEag δ x zt t := fun t =>
    (qSelC_spec hx hcov hL hU t).1
  have hτq : qEag δ x zt τ = (some (pgD k), true) := by rw [← c4 τ]; exact c6
  have hbef : ∀ t, t < τ → (qEag δ x zt t).2 = false := fun t ht => by
    rw [← c4 t]; exact c7 t ht
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ k := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log r := ⟨_, rfl⟩
  have hr4 : (4 : ℝ) ≤ r := by
    rw [hr]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hl2 := Real.log_two_gt_d9
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓk : ℓ = k * Real.log 2 := by rw [hℓ, hr, Real.log_pow]
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓk]
    nlinarith
  have hk2 : (k : ℝ) ≤ 2 * ℓ := by
    rw [hℓk]
    nlinarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
  rw [← hr, ← hℓ] at c9
  refine ⟨τ, c1, c2, c3, c5, hE, hS, by rw [hE]; exact hτq, by rw [hS]; exact hτq,
    fun t ht => ⟨by rw [hE]; exact hbef t ht, by rw [hS]; exact hbef t ht⟩, ?_, ?_, ?_⟩
  · rw [← hr, ← hℓ]
    exact c9
  · rw [← hr, ← hℓ]
    have hW := pgWorkC_le (δ := δ) (x := x) (zt := zt) hL hU sel idx τ
    have hWR : (pgWorkC δ x sel zt idx rawL rawU τ : ℝ) ≤ 70 * (r * r) + 8 * r
        + ((k : ℝ) + 3) * (44 * (r * r))
        + τ * (15 * r + 30 + 4 * (((k : ℝ) + 5) * (4 * r + 2))) := by
      rw [hr]
      exact_mod_cast hW
    exact hWR.trans (eag_real hr4 hℓ1 hk0 hk2 hτ0 c9)
  · rw [← hr, ← hℓ]
    have hW := selWorkC_le hx hcov hL hU sel idx τ
    have hWR : (selWorkC δ x sel zt idx rawL rawU τ : ℝ) ≤ 142 * (r * r) + 8 * r
        + ((k : ℝ) + 3) * (44 * (r * r)) + (2 * (k : ℝ) + 8) * (22 * (r * r))
        + τ * (39 * r + 30 + 2 * (((k : ℝ) + 7) * (8 * r + 4))) := by
      rw [hr]
      exact_mod_cast hW
    exact hWR.trans (sel_real hr4 hℓ1 hk0 hk2 hτ0 c9)

/-- **Theorem `thm:coded-main` (and `thm:coded-covers`) with compiler work in the lower half
and computed costs in the upper half.**  Fix `δ ∈ (0, 1)`.  There are constants `A, B`
(depending only on `δ`) such that for every `k ≥ 2`, with `r = 2^k`:

1. `pgDag k` has `r² ≤ |V| ≤ 7r²` vertices and `2r² ≤ |E| ≤ 11r²` edges, its root supports
   are pairwise distinct, and `w*` is the unique `1/5`-optimal root action;
2. (lower half, every layout, compiler work; `LiteralK5.compiler_work_lower`) every trace of
   unit-cost instructions whose emitted list for each root support is a possibly overlapping
   dyadic cover of the positions of that support under some terminal ordering has work at
   least `r³ / 2`;
3. (upper half) for every probability space carrying reward tapes that are independent
   within each tape, have the stated ranges almost surely and the stated means, every UCT
   search run on them, every (possibly random) index `idx` for the selection scans below the
   root, and raw memories `rawL`, `rawU` with default contents outside the vertex range:
   outside an event of probability at most `δ`, the means lie in the Hoeffding box at every
   time and `PGCertifiedComputed` holds.

The confidence alarm is not modelled: nothing is claimed off the coverage event. -/
theorem coded_main_computed {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ k : ℕ, 2 ≤ k →
      (2 ^ k * 2 ^ k ≤ (pgDag k).N ∧ (pgDag k).N ≤ 7 * (2 ^ k * 2 ^ k) ∧
        2 * (2 ^ k * 2 ^ k) ≤ pgE k ∧ pgE k ≤ 11 * (2 ^ k * 2 ^ k)) ∧
      Function.Injective (pgSupp k) ∧
      (∀ (a : Fin (pgD k + 1)) (hne : (pgSupp k a).Nonempty),
        regret (pgSupp k a) hne (pgMean k) ≤ 1 / 5 ↔ a = Fin.last _) ∧
      (∀ (Op : Type) (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
        (tr : List (LiteralK5.Instr (Finset (GridTerminal k)) Op)),
        (∀ a : Fin (pgD k + 1), LiteralK5.IsListCover (LiteralK5.emitted tr (pgSupp k a))
          (layoutPos π (pgSupp k a))) →
        (2 ^ k) ^ 3 ≤ 2 * LiteralK5.work tr) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : GridTerminal k → ℕ → Ω → ℝ),
        (∀ z, ProbabilityTheory.iIndepFun (X z) P) → (∀ z i, AEMeasurable (X z i) P) →
        (∀ i, ∀ᵐ ω ∂P, X none i ω ∈ Set.Icc (0.98 : ℝ) 1) →
        (∀ g i, ∀ᵐ ω ∂P, X (some g) i ω ∈ Set.Icc (0.01 : ℝ) 0.03) →
        (∀ z i, ∫ ω, X z i ω ∂P = pgMean k z) →
        ∀ (sel : Ω → ℕ → Fin (pgD k + 1)) (zt : Ω → ℕ → GridTerminal k)
          (idx : Ω → ℕ → ℕ → ℝ) (rawL rawU : HEState NNReal),
        RawOK k ⊥ rawL → RawOK k 1 rawU →
        (∀ ω, ParitySearch (fun z i => X z i ω) (sel ω) (zt ω)) →
        P {ω | ¬ (tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k) ∧
            PGCertifiedComputed δ A B (fun z i => X z i ω) (sel ω) (zt ω) (idx ω) rawL rawU)}
          ≤ ENNReal.ofReal δ) := by
  obtain ⟨A, B, hA, hB, hpath⟩ := parity_certified_computed hδ0 hδ1
  refine ⟨A, B, hA, hB, ?_⟩
  intro k hk
  refine ⟨pgDag_size, pgSupp_injective, pg_unique_optimal, ?_, ?_⟩
  · intro Op π tr hC
    exact LiteralK5.compiler_work_lower (by omega) π tr hC
  · intro Ω _ P _ X hindep hmeas hwin hgrid hmean sel zt idx rawL rawU hL hU hsearch
    have hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1 := by
      intro z i
      rcases z with _ | g
      · filter_upwards [hwin i] with ω hω
        exact ⟨by have := hω.1; linarith, hω.2⟩
      · filter_upwards [hgrid g i] with ω hω
        exact ⟨by have := hω.1; linarith, by have := hω.2; linarith⟩
    have hcard : (Fintype.card (GridTerminal k) : ℝ) ≤ pgM k := by
      have hm : Fintype.card (Mask k) = 2 ^ k := by
        rw [← card_univ, card_univ_mask]
      have : Fintype.card (GridTerminal k) = 2 ^ k * 2 ^ k + 1 := by
        rw [Fintype.card_option, Fintype.card_prod, hm]
      unfold pgM
      rw [this]
    have hM1 : (1 : ℝ) ≤ pgM k := by
      have := pgM_ge (k := k)
      linarith
    have hcov := tape_coverage P hindep hmeas hbdd hmean hM1 hcard hδ0 hδ1.le zt
    have hae : ∀ᵐ ω ∂P, PGTape (fun z i => X z i ω) := by
      have h1 : ∀ᵐ ω ∂P, ∀ i, X none i ω ∈ Set.Icc (0.98 : ℝ) 1 := ae_all_iff.2 hwin
      have h2 : ∀ᵐ ω ∂P, ∀ g i, X (some g) i ω ∈ Set.Icc (0.01 : ℝ) 0.03 :=
        ae_all_iff.2 (fun g => ae_all_iff.2 (hgrid g))
      filter_upwards [h1, h2] with ω a b
      exact ⟨a, b⟩
    have hnull : P {ω | ¬ PGTape (fun z i => X z i ω)} = 0 := ae_iff.1 hae
    have hsub : {ω | ¬ (tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k) ∧
          PGCertifiedComputed δ A B (fun z i => X z i ω) (sel ω) (zt ω) (idx ω) rawL rawU)}
        ⊆ {ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          ∪ {ω | ¬ PGTape (fun z i => X z i ω)} := by
      intro ω hω
      by_cases hx : PGTape (fun z i => X z i ω)
      · left
        intro hc
        exact hω ⟨hc, hpath k hk _ _ _ _ _ _ hL hU hx (hsearch ω) hc⟩
      · right
        exact hx
    calc P {ω | ¬ (tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k) ∧
            PGCertifiedComputed δ A B (fun z i => X z i ω) (sel ω) (zt ω) (idx ω) rawL rawU)}
        ≤ P ({ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          ∪ {ω | ¬ PGTape (fun z i => X z i ω)}) := measure_mono hsub
      _ ≤ P {ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          + P {ω | ¬ PGTape (fun z i => X z i ω)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ := by
          rw [hnull, add_zero]
          exact hcov

end Final

end

end LiteralK6
end JointRootCert
