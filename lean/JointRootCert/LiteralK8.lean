/-
Joint Root Certification: `prop:unrestricted-compiler` (Equivalence Under Unrestricted
Circuit Retention), stated for the Graph Selective engine itself.

Manuscript result covered:

* `prop:unrestricted-compiler`.  "A compiler permitted to retain the original hierarchical
  monitor circuit `G` and execute the shared indexed-heap update engine reproduces Graph
  Selective with at most `O(|V| + |E|)` additional setup work."

## Contents

1. `WFA A L`: an explicit well-formedness predicate on a circuit stored as arrays
   (`CostEngines.ADag`), and `toDag_wf`: it implies `(A.toDag L).WF`.  `parents_sum_eq`
   derives "the parent array has `|E|` entries" from the predicate, so that the hypotheses of
   `CostEngines.copyDag_cost_le` are consequences of `WFA` (`copy_cost_le`).

2. `graphSelective`: Graph Selective on an array circuit as a costed program: cold
   initialisation of both endpoints on implemented heaps (`EngineFinal.initPassH`), then the
   engine `RetireFinal.runH` with computed per-step cost `RetireFinal.costH`; the root-action
   gates are read from the array `A.roots` in order (`rootOf`).  `retainedCompile`: copy the
   arrays (`CostEngines.copyDag`, computed cost) and run `graphSelective` on the copy.
   `retained_compiler_literal`: the copy is equal to the input, the engine state of the
   compiler equals that of Graph Selective at every time, hence so do the replies, the
   retirements and the per-step costs; total work = Graph Selective's work + copy cost, and
   copy cost `≤ 4 (|V| + |E|)`.
   `retained_compiler_sound` adds the semantic content of "Graph Selective" (via
   `RetireFinal.ram_work_bounds_impl`): the compiler's leader-and-stop reply equals that of
   the eager engine on the original circuit, with an explicit bound on its total work.

3. `gsImpl`, `compilerImpl`: the two programs as oracle implementations driven by
   observations (running-intersection terminal boxes as in `LiteralK1.lean`);
   `gs_fold` identifies the oracle implementation with `runH`;
   `retained_compiler_coupling`: identical histories, replies and stopping times for every
   controller.

4. `coldInit_cost_ge`, `copy_absorbed`: the cold initialisation costs at least
   `2 (n_int + |E|)` computed units, so
   `copy ≤ 4 (|V| + |E|) ≤ 2 · (cold initialisation cost) + 4 · (number of leaves)`.

Charges that are by definition: `copyList`/`copyAdj` charge one unit per array cell copied
(one per vertex record, one per incidence, one per level entry, one per root entry).  The
costs of initialisation and of the engine are those computed by `initPassH`, `relStepH`,
`qRetireH` (see `EngineFinal.lean`, `RetireFinal.lean`).
-/
import JointRootCert.RetireFinal

namespace JointRootCert
namespace LiteralK8

open Finset CostEngines DagRetire EngineFinal RetireFinal
open HeapImpl (Heap HEState SimE)
open _root_.JointRootCert.Representation (Controller history replyAt stopTime OracleImpl exact_coupling)

/-! ## 1. Well-formedness of an array circuit -/

section Arrays

/-- **Well-formedness of a circuit stored as arrays**, for level bound `L`.  Out-of-range
entries are read as the empty list / level `0` (as `ADag.toDag` does), so every condition
below is a condition on the finitely many array cells. -/
structure WFA (A : ADag) (L : ℕ) : Prop where
  /-- one parent list per vertex -/
  parents_len : A.parents.length = A.V
  /-- one level per vertex -/
  level_len : A.level.length = A.V
  /-- at most `|V|` root-action outputs -/
  roots_len : A.roots.length ≤ A.V
  /-- every child index is a vertex -/
  child_lt : ∀ p c, c ∈ A.children.getD p [] → c < A.V
  /-- every parent index is a vertex -/
  parent_lt : ∀ c p, p ∈ A.parents.getD c [] → p < A.V
  /-- the parent array is the reverse of the child array -/
  rev : ∀ c p, p ∈ A.parents.getD c [] ↔ c ∈ A.children.getD p []
  /-- parent lists have no repetition -/
  parents_nodup : ∀ c, (A.parents.getD c []).Nodup
  /-- child lists have no repetition -/
  children_nodup : ∀ p, (A.children.getD p []).Nodup
  /-- levels strictly decrease from parent to child -/
  level_lt : ∀ p c, c ∈ A.children.getD p [] → A.level.getD c 0 < A.level.getD p 0
  /-- levels are at most `L` -/
  level_le : ∀ g, g < A.V → A.level.getD g 0 ≤ L

/-- **The array conditions imply well-formedness of the engine's view of the circuit.** -/
theorem toDag_wf {A : ADag} {L : ℕ} (h : WFA A L) : (A.toDag L).WF where
  parents_iff := h.rev
  parents_nodup := h.parents_nodup
  parent_lt := h.parent_lt
  level_lt := h.level_lt
  level_le := fun g => by
    show A.level.getD g 0 ≤ L
    by_cases hg : g < A.V
    · exact h.level_le g hg
    · rw [List.getD_eq_default _ _ (by rw [h.level_len]; omega)]
      exact Nat.zero_le _

lemma sum_map_eq_sum_range {β : Type*} (l : List β) (d : β) (f : β → ℕ) :
    (l.map f).sum = ∑ i ∈ range l.length, f (l.getD i d) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

lemma length_eq_card_filter (V : ℕ) (l : List ℕ) (hn : l.Nodup) (hlt : ∀ x ∈ l, x < V) :
    l.length = ((range V).filter (fun x => x ∈ l)).card := by
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext x
  simp only [List.mem_toFinset, mem_filter, mem_range]
  exact ⟨fun hx => ⟨hlt x hx, hx⟩, fun hx => hx.2⟩

/-- `|E|` as a sum over vertices. -/
lemma E_eq_sum (A : ADag) : A.E = ∑ p ∈ range A.V, (A.children.getD p []).length :=
  sum_map_eq_sum_range A.children [] List.length

/-- **The parent array has `|E|` entries**: derived from the array conditions (reverse
incidence without repetition), not assumed. -/
theorem parents_sum_eq {A : ADag} {L : ℕ} (h : WFA A L) :
    (A.parents.map List.length).sum = A.E := by
  rw [E_eq_sum, sum_map_eq_sum_range A.parents [] List.length, h.parents_len]
  have e1 : ∀ c ∈ range A.V, (A.parents.getD c []).length
      = ∑ p ∈ range A.V, if p ∈ A.parents.getD c [] then 1 else 0 := by
    intro c _
    rw [length_eq_card_filter A.V _ (h.parents_nodup c) (h.parent_lt c), Finset.card_filter]
  have e2 : ∀ p ∈ range A.V, (A.children.getD p []).length
      = ∑ c ∈ range A.V, if c ∈ A.children.getD p [] then 1 else 0 := by
    intro p _
    rw [length_eq_card_filter A.V _ (h.children_nodup p) (h.child_lt p), Finset.card_filter]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun c _ => ?_))
  simp only [h.rev c p]

/-- **Copy cost**: for a well-formed array circuit the computed cost of `copyDag` is at
most `4 (|V| + |E|)`. -/
theorem copy_cost_le {A : ADag} {L : ℕ} (h : WFA A L) : (copyDag A).2 ≤ 4 * (A.V + A.E) :=
  copyDag_cost_le A h.parents_len (parents_sum_eq h) h.level_len h.roots_len

/-- The gate of root action `i`, read from the ordered root array. -/
def rootOf (A : ADag) (i : ℕ) : ℕ := A.roots.getD i 0

end Arrays

/-! ## 2. Graph Selective and the retained-circuit compiler as costed programs -/

section Programs

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **Cold initialisation** of the Graph Selective engine on an array circuit, on implemented
heaps: both endpoints are initialised by `initPassH` from the terminal values `vl`, `vu`
(read at the leaves) and empty heaps; the cost is the computed cost of the two passes. -/
def coldInit (A : ADag) (L : ℕ) (order : List ℕ) (vl vu : ℕ → α) : HRState α × ℕ :=
  (⟨A.toDag L, (initPassH (A.toDag L) order ⟨vl, fun _ => Heap.empty⟩).1,
      (initPassH (A.toDag L) order ⟨vu, fun _ => Heap.empty⟩).1⟩,
   (initPassH (A.toDag L) order ⟨vl, fun _ => Heap.empty⟩).2
    + (initPassH (A.toDag L) order ⟨vu, fun _ => Heap.empty⟩).2)

/-- **Graph Selective on an array circuit**, as a costed program: cold initialisation, then
`T` rollouts of the engine with retirement on implemented heaps (`runH`; candidate policy
`candV`, terminal updates `u`, query schedule `q`).  The `A.roots.length` root actions are
the gates listed in `A.roots`, in that order.  Result: the engine state after `T` rollouts
and the total computed work. -/
def graphSelective (A : ADag) (L : ℕ) (order : List ℕ) (vl vu : ℕ → α) (candV : Policy α)
    (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (T : ℕ) : HQS α × ℕ :=
  (runH A.roots.length (rootOf A) candV u q ⟨(coldInit A L order vl vu).1, fun _ => true⟩ T,
   (coldInit A L order vl vu).2
    + ∑ t ∈ range T, costH A.roots.length (rootOf A) candV u q
        ⟨(coldInit A L order vl vu).1, fun _ => true⟩ t)

/-- **The retained-circuit compiler**: copy the arrays of the input circuit (`copyDag`,
computed cost), then run Graph Selective on the copy. -/
def retainedCompile (A : ADag) (L : ℕ) (order : List ℕ) (vl vu : ℕ → α) (candV : Policy α)
    (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (T : ℕ) : HQS α × ℕ :=
  ((graphSelective (copyDag A).1 L order vl vu candV u q T).1,
   (copyDag A).2 + (graphSelective (copyDag A).1 L order vl vu candV u q T).2)

/-- **`prop:unrestricted-compiler`.**  Let `A` be a well-formed array circuit (`WFA A L`).
For every list `order` handed to the initialisation, all initial terminal values `vl`,
`vu`, every candidate policy, update sequence and query schedule:

* the copy made by the compiler is equal to `A` as an array circuit; in particular it has
  the same gate indices (canonical terminal identities) and the same ordered root array
  (root-action ordering), and `A.toDag L` is a well-formed circuit;
* at every time `T` the compiler's engine state (live circuit, stored values, heaps,
  activity flags of the root actions) equals that of Graph Selective run on `A`; hence the
  leader-and-stop reply `qOut`, the outcome of every root retirement `qRetireH` and the
  computed cost `costH` of every step are equal;
* the compiler's total work equals Graph Selective's total work plus the copy cost, and
  the copy cost is at most `4 (|V| + |E|)`. -/
theorem retained_compiler_literal {A : ADag} {L : ℕ} (hA : WFA A L) (order : List ℕ)
    (vl vu : ℕ → α) (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (φ : α → ℝ) (ε : ℝ) :
    (copyDag A).1 = A ∧ (A.toDag L).WF ∧
    rootOf (copyDag A).1 = rootOf A ∧
    (∀ T, (retainedCompile A L order vl vu candV u q T).1
        = (graphSelective A L order vl vu candV u q T).1) ∧
    (∀ T, qOut φ ε A.roots.length
        (fun i => (retainedCompile A L order vl vu candV u q T).1.r.lo.val (rootOf A i))
        (fun i => (retainedCompile A L order vl vu candV u q T).1.r.hi.val (rootOf A i))
        (retainedCompile A L order vl vu candV u q T).1.act
      = qOut φ ε A.roots.length
        (fun i => (graphSelective A L order vl vu candV u q T).1.r.lo.val (rootOf A i))
        (fun i => (graphSelective A L order vl vu candV u q T).1.r.hi.val (rootOf A i))
        (graphSelective A L order vl vu candV u q T).1.act) ∧
    (∀ T, qRetireH A.roots.length (rootOf A) (retainedCompile A L order vl vu candV u q T).1
        = qRetireH A.roots.length (rootOf A) (graphSelective A L order vl vu candV u q T).1) ∧
    (∀ t, costH (copyDag A).1.roots.length (rootOf (copyDag A).1) candV u q
          ⟨(coldInit (copyDag A).1 L order vl vu).1, fun _ => true⟩ t
        = costH A.roots.length (rootOf A) candV u q
          ⟨(coldInit A L order vl vu).1, fun _ => true⟩ t) ∧
    (∀ T, (retainedCompile A L order vl vu candV u q T).2
        = (graphSelective A L order vl vu candV u q T).2 + (copyDag A).2) ∧
    (copyDag A).2 ≤ 4 * (A.V + A.E) := by
  have hc : (copyDag A).1 = A := (copyDag_spec A).1
  have hs : ∀ T, (retainedCompile A L order vl vu candV u q T).1
      = (graphSelective A L order vl vu candV u q T).1 := by
    intro T
    unfold retainedCompile
    rw [hc]
  refine ⟨hc, toDag_wf hA, by rw [hc], hs, fun T => by rw [hs T], fun T => by rw [hs T],
    fun t => by rw [hc], fun T => ?_, copy_cost_le hA⟩
  unfold retainedCompile
  rw [hc]
  exact Nat.add_comm _ _

/-- **The compiler reproduces Graph Selective, with the meaning of Graph Selective made
explicit.**  Let `A` be a well-formed array circuit with at least one root action and
degrees at most `D`, `order` a list of its internal gates by nondecreasing level, the
initial terminal intervals nonempty, and the terminal updates `u` nested (`NestedRun`: each
update shrinks the interval of a terminal; this is what the running-intersection boxes
produce).  With the delivery policy `delivV`:

* at every time the compiler's leader-and-stop reply equals that of the full-incidence
  (eager) engine on the original circuit;
* the compiler's total computed work is at most the copy cost `4 (|V| + |E|)`, plus the
  cold initialisation bound `4 Σ_g (1 + deg g (⌈log₂ deg g⌉ + 1))`, plus the bound of
  `eq:ram-work-bounds` for the run (`RetireFinal.ram_work_bounds_impl`). -/
theorem retained_compiler_sound {A : ADag} {L : ℕ} (hA : WFA A L) (D : ℕ)
    (hD : ∀ p, ((A.toDag L).children p).length ≤ D) (order : List ℕ)
    (hall : ∀ g, (A.toDag L).children g ≠ [] → g ∈ order)
    (hint : ∀ g ∈ order, (A.toDag L).children g ≠ [])
    (hsorted : order.Pairwise (fun a b => (A.toDag L).level a ≤ (A.toDag L).level b))
    (vl vu : ℕ → α) (hleaf : ∀ g, (A.toDag L).children g = [] → vl g ≤ vu g)
    (u : ℕ → ℕ × α × α)
    (hn : NestedRun (A.toDag L) noCand u
      ⟨A.toDag L, (initPass (A.toDag L) order ⟨vl, fun _ _ => ⊥⟩).1,
        (initPass (A.toDag L) order ⟨vu, fun _ _ => ⊥⟩).1⟩)
    (hK : 0 < A.roots.length) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (q : ℕ → Bool) (T : ℕ) :
    (∀ t, qOut φ ε A.roots.length
        (fun i => (retainedCompile A L order vl vu delivV u q t).1.r.lo.val (rootOf A i))
        (fun i => (retainedCompile A L order vl vu delivV u q t).1.r.hi.val (rootOf A i))
        (retainedCompile A L order vl vu delivV u q t).1.act
      = qOut φ ε A.roots.length
        (fun i => (runState (A.toDag L) u
          ((initPass (A.toDag L) order ⟨vl, fun _ _ => ⊥⟩).1,
            (initPass (A.toDag L) order ⟨vu, fun _ _ => ⊥⟩).1) t).1.val (rootOf A i))
        (fun i => (runState (A.toDag L) u
          ((initPass (A.toDag L) order ⟨vl, fun _ _ => ⊥⟩).1,
            (initPass (A.toDag L) order ⟨vu, fun _ _ => ⊥⟩).1) t).2.val (rootOf A i))
        (fun _ => true)) ∧
    (retainedCompile A L order vl vu delivV u q T).2
      ≤ 4 * (A.V + A.E) + 4 * (order.map (initCost (A.toDag L))).sum
        + 2 * (2 * T * (L + 3)
          + ((range T).filter (fun t => q t = true)).card * (4 * A.roots.length)
          + (Nat.clog 2 D + 5) * ∑ t ∈ range T, volF A.roots.length (rootOf A) delivCand u q
              ⟨⟨A.toDag L, (initPass (A.toDag L) order ⟨vl, fun _ _ => ⊥⟩).1,
                (initPass (A.toDag L) order ⟨vu, fun _ _ => ⊥⟩).1⟩, fun _ => true⟩ t
          + (2 * Nat.clog 2 D + 4) * ∑ t ∈ range T, retF A.roots.length (rootOf A) delivCand u q
              ⟨⟨A.toDag L, (initPass (A.toDag L) order ⟨vl, fun _ _ => ⊥⟩).1,
                (initPass (A.toDag L) order ⟨vu, fun _ _ => ⊥⟩).1⟩, fun _ => true⟩ t
          + 2 * (A.V + live (A.toDag L))) := by
  have hG := toDag_wf hA
  have hc : (copyDag A).1 = A := (copyDag_spec A).1
  obtain ⟨i1, i2⟩ := init_engine hG order (⟨vl, fun _ _ => ⊥⟩ : EState α)
    ⟨vu, fun _ _ => ⊥⟩ hall hint hsorted hleaf
  obtain ⟨l1, l2⟩ := initPassH_sim (G := A.toDag L) order
    (⟨vl, fun _ => Heap.empty⟩ : HEState α) ⟨vl, fun _ _ => ⊥⟩ hA.children_nodup hall rfl
    (fun _ => rfl)
  obtain ⟨u1, u2⟩ := initPassH_sim (G := A.toDag L) order
    (⟨vu, fun _ => Heap.empty⟩ : HEState α) ⟨vu, fun _ _ => ⊥⟩ hA.children_nodup hall rfl
    (fun _ => rfl)
  have hsim : SimR (coldInit A L order vl vu).1
      ⟨A.toDag L, (initPass (A.toDag L) order ⟨vl, fun _ _ => ⊥⟩).1,
        (initPass (A.toDag L) order ⟨vu, fun _ _ => ⊥⟩).1⟩ := ⟨rfl, l1, u1⟩
  obtain ⟨b1, b2⟩ := ram_work_bounds_impl (K := A.roots.length) (rt := rootOf A) hG D hD i1 hn
    hK φ hφ ε hε q T 0 (coldInit A L order vl vu).1 hsim
  rw [Nat.zero_add, Nat.zero_add] at b2
  have hcopy := copy_cost_le hA
  refine ⟨fun t => ?_, ?_⟩
  · unfold retainedCompile
    rw [hc]
    exact b1 t
  · unfold retainedCompile
    rw [hc]
    have hinit : (coldInit A L order vl vu).2 ≤ 4 * (order.map (initCost (A.toDag L))).sum := by
      show (initPassH (A.toDag L) order ⟨vl, fun _ => Heap.empty⟩).2
        + (initPassH (A.toDag L) order ⟨vu, fun _ => Heap.empty⟩).2 ≤ _
      omega
    show (copyDag A).2 + ((coldInit A L order vl vu).2
      + ∑ t ∈ range T, costH A.roots.length (rootOf A) delivV u q
          ⟨(coldInit A L order vl vu).1, fun _ => true⟩ t) ≤ _
    have hN : (A.toDag L).N = A.V := rfl
    have hL : (A.toDag L).L = L := rfl
    rw [hN, hL] at b2
    omega

end Programs

/-! ## 4. The copy is absorbed into the cold initialisation -/

section Absorb

variable {α : Type*} [LinearOrder α] [OrderBot α]

omit [OrderBot α] in
lemma insertAll_cost_ge {ι : Type*} [DecidableEq ι] :
    ∀ (es : List (ι × α)) (H : Heap ι α), es.length ≤ (HeapImpl.insertAll H es).2 := by
  intro es
  induction es with
  | nil => intro H; exact Nat.zero_le _
  | cons e es ih =>
    intro H
    show es.length + 1 ≤ (HeapImpl.insert H e.1 e.2).2
      + (HeapImpl.insertAll (HeapImpl.insert H e.1 e.2).1 es).2
    have h1 : 1 ≤ (HeapImpl.insert H e.1 e.2).2 := Nat.le_add_left 1 _
    have h2 := ih (HeapImpl.insert H e.1 e.2).1
    omega

/-- The implemented initialisation pass costs at least one unit per listed gate and one
unit per incidence of a listed gate (computed cost, not a charge). -/
lemma initPassH_cost_ge (G : Dag) : ∀ (order : List ℕ) (s : HEState α),
    (order.map (fun g => 1 + (G.children g).length)).sum ≤ (initPassH G order s).2 := by
  intro order
  induction order with
  | nil => intro s; exact Nat.zero_le _
  | cons g rest ih =>
    intro s
    show (1 + (G.children g).length) + (rest.map (fun g => 1 + (G.children g).length)).sum
      ≤ (initGateH G g s).2 + (initPassH G rest (initGateH G g s).1).2
    have h1 : (G.children g).length + 1 ≤ (initGateH G g s).2 := by
      show (G.children g).length + 1 ≤ (HeapImpl.insertAll (Heap.empty : Heap ℕ α)
        ((G.children g).map (fun c => (c, s.val c)))).2 + 1
      have := insertAll_cost_ge ((G.children g).map (fun c => (c, s.val c)))
        (Heap.empty : Heap ℕ α)
      rw [List.length_map] at this
      omega
    have h2 := ih (initGateH G g s).1
    omega

lemma sum_one_add (f : ℕ → ℕ) (l : List ℕ) :
    (l.map (fun g => 1 + f g)).sum = l.length + (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- For a list of the internal gates without repetition, the incidences of the listed gates
are all `|E|` incidences, and there are at most `|V|` listed gates. -/
lemma order_facts {A : ADag} {L : ℕ} (order : List ℕ) (hnd : order.Nodup)
    (hall : ∀ g, (A.toDag L).children g ≠ [] → g ∈ order) :
    A.E ≤ (order.map (fun g => ((A.toDag L).children g).length)).sum ∧
    ((∀ g ∈ order, (A.toDag L).children g ≠ []) →
      (order.map (fun g => ((A.toDag L).children g).length)).sum = A.E ∧
      order.length ≤ A.V) := by
  rw [← List.sum_toFinset _ hnd, E_eq_sum]
  have hsub : ∀ g ∈ range A.V, g ∉ order.toFinset → (A.children.getD g []).length = 0 := by
    intro g _ hg
    by_contra hne
    exact hg (List.mem_toFinset.2 (hall g (fun h0 => hne (by
      have : A.children.getD g [] = [] := h0
      rw [this]; rfl))))
  refine ⟨?_, fun hint => ?_⟩
  · rw [← Finset.sum_filter_add_sum_filter_not (range A.V) (fun g => g ∈ order.toFinset),
      Finset.sum_eq_zero (s := (range A.V).filter (fun g => ¬ g ∈ order.toFinset))
        (fun g hg => hsub g (mem_filter.1 hg).1 (mem_filter.1 hg).2), Nat.add_zero]
    exact Finset.sum_le_sum_of_subset (fun g hg => (mem_filter.1 hg).2)
  · have hss : order.toFinset ⊆ range A.V := by
      intro g hg
      rw [mem_range]
      by_contra hlt
      apply hint g (List.mem_toFinset.1 hg)
      show A.children.getD g [] = []
      exact List.getD_eq_default _ _ (by unfold ADag.V at hlt; omega)
    refine ⟨Finset.sum_subset hss hsub, ?_⟩
    have := Finset.card_le_card hss
    rwa [List.toFinset_card_of_nodup hnd, card_range] at this

/-- **Cold initialisation lower bound**: if `order` lists every internal gate, without
repetition, the computed cost of the cold initialisation of both endpoints is at least
`2 (|order| + |E|)`, i.e. at least `2 (n_int + |E|)` when `order` lists exactly the
internal gates. -/
theorem coldInit_cost_ge {A : ADag} {L : ℕ} (order : List ℕ) (hnd : order.Nodup)
    (hall : ∀ g, (A.toDag L).children g ≠ [] → g ∈ order) (vl vu : ℕ → α) :
    2 * (order.length + A.E) ≤ (coldInit A L order vl vu).2 := by
  have h1 := initPassH_cost_ge (A.toDag L) order (⟨vl, fun _ => Heap.empty⟩ : HEState α)
  have h2 := initPassH_cost_ge (A.toDag L) order (⟨vu, fun _ => Heap.empty⟩ : HEState α)
  rw [sum_one_add] at h1 h2
  have h3 := (order_facts (A := A) (L := L) order hnd hall).1
  show _ ≤ (initPassH (A.toDag L) order ⟨vl, fun _ => Heap.empty⟩).2
    + (initPassH (A.toDag L) order ⟨vu, fun _ => Heap.empty⟩).2
  omega

/-- **"Absorbed into the cold initialisation bound", precisely.**  For a well-formed array
circuit and `order` listing exactly its `n_int` internal gates without repetition:

* copy cost `≤ 4 (|V| + |E|)`;
* `2 (n_int + |E|) ≤` computed cost of the cold initialisation;
* hence copy cost `≤ 2 · (cold initialisation cost) + 4 (|V| − n_int)`, where
  `|V| − n_int` is the number of leaves (which the initialisation pass does not touch). -/
theorem copy_absorbed {A : ADag} {L : ℕ} (hA : WFA A L) (order : List ℕ) (hnd : order.Nodup)
    (hall : ∀ g, (A.toDag L).children g ≠ [] → g ∈ order)
    (hint : ∀ g ∈ order, (A.toDag L).children g ≠ []) (vl vu : ℕ → α) :
    (copyDag A).2 ≤ 4 * (A.V + A.E) ∧
    2 * (order.length + A.E) ≤ (coldInit A L order vl vu).2 ∧
    order.length ≤ A.V ∧
    (copyDag A).2 ≤ 2 * (coldInit A L order vl vu).2 + 4 * (A.V - order.length) := by
  have h1 := copy_cost_le hA
  have h2 := coldInit_cost_ge (A := A) (L := L) order hnd hall vl vu
  have h3 := ((order_facts (A := A) (L := L) order hnd hall).2 hint).2
  exact ⟨h1, h2, h3, by omega⟩

end Absorb

/-! ## 3. The two programs as oracle implementations; coupling for every controller -/

section Oracle

variable {Z X : Type*} [DecidableEq Z] {α : Type*} [LinearOrder α] [OrderBot α]

/-- The terminal box: endpoints, the sticky confidence-alarm flag and the history. -/
structure BoxState (Z X α : Type*) where
  lo : Z → α
  hi : Z → α
  alarm : Bool
  hist : List (Z × X)

omit [OrderBot α] in
/-- **Running intersection** (`eq:terminal-box`): the raw interval `ci` of the terminal just
sampled is intersected with its current interval; an empty intersection leaves the box
unchanged and raises the alarm. -/
def boxStep (ci : List (Z × X) → α × α) (b : BoxState Z X α) (o : Z × X) : BoxState Z X α :=
  if max (b.lo o.1) (ci (b.hist ++ [o])).1 ≤ min (b.hi o.1) (ci (b.hist ++ [o])).2 then
    ⟨Function.update b.lo o.1 (max (b.lo o.1) (ci (b.hist ++ [o])).1),
     Function.update b.hi o.1 (min (b.hi o.1) (ci (b.hist ++ [o])).2), b.alarm, b.hist ++ [o]⟩
  else ⟨b.lo, b.hi, true, b.hist ++ [o]⟩

omit [OrderBot α] in
lemma boxStep_hist (ci : List (Z × X) → α × α) (b : BoxState Z X α) (o : Z × X) :
    (boxStep ci b o).hist = b.hist ++ [o] := by
  unfold boxStep
  split_ifs <;> rfl

/-- The box after the first `t` observations of a stream. -/
def boxAt (ci : List (Z × X) → α × α) (b0 : BoxState Z X α) (obs : ℕ → Z × X) :
    ℕ → BoxState Z X α
  | 0 => b0
  | t + 1 => boxStep ci (boxAt ci b0 obs t) (obs t)

omit [OrderBot α] in
lemma boxAt_hist_length (ci : List (Z × X) → α × α) (b0 : BoxState Z X α) (hb : b0.hist = [])
    (obs : ℕ → Z × X) : ∀ t, (boxAt ci b0 obs t).hist.length = t := by
  intro t
  induction t with
  | zero => simp [boxAt, hb]
  | succ t ih =>
    show (boxStep ci (boxAt ci b0 obs t) (obs t)).hist.length = t + 1
    rw [boxStep_hist, List.length_append, ih]
    rfl

/-- Terminal updates fed to the engine along a stream of observations: rollout `t + 1`
writes the new box endpoints of the terminal it sampled. -/
def uS (leaf : Z → ℕ) (ci : List (Z × X) → α × α) (b0 : BoxState Z X α) (obs : ℕ → Z × X) :
    ℕ → ℕ × α × α
  | 0 => (0, ⊥, ⊥)
  | t + 1 => (leaf (obs t).1, (boxAt ci b0 obs (t + 1)).lo (obs t).1,
      (boxAt ci b0 obs (t + 1)).hi (obs t).1)

/-- One observation processed by the Graph Selective engine on implemented heaps: box
update; root retirement with release if a query is scheduled; waves, retirement pass and
release cascade (`relStepH`). -/
def selStepH (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (q : ℕ → Bool) (leaf : Z → ℕ)
    (ci : List (Z × X) → α × α) (s : BoxState Z X α × HQS α) (o : Z × X) :
    BoxState Z X α × HQS α :=
  (boxStep ci s.1 o,
   (relStepH K rt candV (leaf o.1, (boxStep ci s.1 o).lo o.1, (boxStep ci s.1 o).hi o.1)
      (if q s.1.hist.length = true then (qRetireH K rt s.2).1 else s.2)).1)

/-- **Graph Selective on an array circuit as an oracle implementation.**  Terminal `z` is
the leaf `leaf z`; the initial box is read from the initial terminal values; the engine
starts from the cold initialisation; the reply is the alarm flag, the leader among the
active root actions (root array order) and the stopping bit. -/
noncomputable def gsImpl (A : ADag) (L : ℕ) (order : List ℕ) (vl vu : ℕ → α)
    (candV : Policy α) (q : ℕ → Bool) (leaf : Z → ℕ) (ci : List (Z × X) → α × α)
    (φ : α → ℝ) (ε : ℝ) :
    OracleImpl (BoxState Z X α × HQS α) (Z × X) (Bool × Option ℕ × Bool) where
  init := (⟨fun z => vl (leaf z), fun z => vu (leaf z), false, []⟩,
    ⟨(coldInit A L order vl vu).1, fun _ => true⟩)
  step := selStepH A.roots.length (rootOf A) candV q leaf ci
  reply := fun s => (s.1.alarm,
    qOut φ ε A.roots.length (fun i => s.2.r.lo.val (rootOf A i))
      (fun i => s.2.r.hi.val (rootOf A i)) s.2.act)

/-- **The retained-circuit compiler as an oracle implementation**: the same engine, started
from (and reading the root order of) the copied circuit. -/
noncomputable def compilerImpl (A : ADag) (L : ℕ) (order : List ℕ) (vl vu : ℕ → α)
    (candV : Policy α) (q : ℕ → Bool) (leaf : Z → ℕ) (ci : List (Z × X) → α × α)
    (φ : α → ℝ) (ε : ℝ) :
    OracleImpl (BoxState Z X α × HQS α) (Z × X) (Bool × Option ℕ × Bool) :=
  gsImpl (copyDag A).1 L order vl vu candV q leaf ci φ ε

/-- The oracle implementation is the engine of part 2: after the first `n` observations
of a stream its engine state is `runH` on the induced terminal updates, i.e. the state
computed by `graphSelective`. -/
theorem gs_fold (A : ADag) (L : ℕ) (order : List ℕ) (vl vu : ℕ → α) (candV : Policy α)
    (q : ℕ → Bool) (leaf : Z → ℕ) (ci : List (Z × X) → α × α) (φ : α → ℝ) (ε : ℝ)
    (obs : ℕ → Z × X) : ∀ n,
    (((List.range n).map obs).foldl (gsImpl A L order vl vu candV q leaf ci φ ε).step
        (gsImpl A L order vl vu candV q leaf ci φ ε).init).2
      = (graphSelective A L order vl vu candV
          (uS leaf ci ⟨fun z => vl (leaf z), fun z => vu (leaf z), false, []⟩ obs) q n).1 := by
  have key : ∀ n, ((List.range n).map obs).foldl
        (selStepH A.roots.length (rootOf A) candV q leaf ci)
        (⟨fun z => vl (leaf z), fun z => vu (leaf z), false, []⟩,
          ⟨(coldInit A L order vl vu).1, fun _ => true⟩)
      = (boxAt ci ⟨fun z => vl (leaf z), fun z => vu (leaf z), false, []⟩ obs n,
        runH A.roots.length (rootOf A) candV
          (uS leaf ci ⟨fun z => vl (leaf z), fun z => vu (leaf z), false, []⟩ obs) q
          ⟨(coldInit A L order vl vu).1, fun _ => true⟩ n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.foldl_append, ih]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, selStepH]
      rw [boxAt_hist_length ci _ rfl obs n]
      rfl
  intro n
  exact congrArg Prod.snd (key n)

/-- **`prop:unrestricted-compiler`, coupling form.**  For every array circuit, the
retained-circuit compiler and Graph Selective expose the same oracle on every history
(because the copy is equal to the original circuit, with the same gate indices and root
order), hence induce identical histories (rollout trajectories and rewards), replies
(alarm, leader, stopping bit) and stopping times for every controller, reward tape and
controller tape. -/
theorem retained_compiler_coupling {Ω : Type*} (A : ADag) (L : ℕ) (order : List ℕ)
    (vl vu : ℕ → α) (candV : Policy α) (q : ℕ → Bool) (leaf : Z → ℕ)
    (ci : List (Z × X) → α × α) (φ : α → ℝ) (ε : ℝ)
    (ctrl : Controller Z X (Bool × Option ℕ × Bool) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ h, (compilerImpl A L order vl vu candV q leaf ci φ ε).answer h
        = (gsImpl A L order vl vu candV q leaf ci φ ε).answer h) ∧
    (∀ n, history (compilerImpl A L order vl vu candV q leaf ci φ ε).answer ctrl rew ω n
        = history (gsImpl A L order vl vu candV q leaf ci φ ε).answer ctrl rew ω n) ∧
    (∀ n, replyAt (compilerImpl A L order vl vu candV q leaf ci φ ε).answer ctrl rew ω n
        = replyAt (gsImpl A L order vl vu candV q leaf ci φ ε).answer ctrl rew ω n) ∧
    stopTime (compilerImpl A L order vl vu candV q leaf ci φ ε).answer ctrl rew ω
      = stopTime (gsImpl A L order vl vu candV q leaf ci φ ε).answer ctrl rew ω := by
  have hans : ∀ h, (compilerImpl A L order vl vu candV q leaf ci φ ε).answer h
      = (gsImpl A L order vl vu candV q leaf ci φ ε).answer h := by
    intro h
    unfold compilerImpl
    rw [(copyDag_spec A).1]
  exact ⟨hans, exact_coupling _ _ hans ctrl rew ω⟩

end Oracle

end LiteralK8
end JointRootCert
