/-
Joint Root Certification: the DAG interval engine with online incidence retirement.

Manuscript results covered:

* `prop:representation-cost` (Unified Full-Cost Representation Comparison): the engine of
  `CostEngines.lean` extended by online strict-dominance retirement of incidences, so that
  the live incidence set `F_t` shrinks; exactness of the stored intervals with respect to
  the ORIGINAL circuit; the work bound `eq:prop-rep-upper` with `S⁺` taken over the changing
  live sets; a costed initialisation pass; and the lower bound `Ω(P + S⁻)` for every
  implementation satisfying a delivery contract that is stated below.
* `prop:uct-coupling` (Safe permanent retirement), the work bounds `eq:ram-work-bounds`,
  for general DAGs of out-degree at most `D` with retirement of internal incidences
  (rule (i)).

## Cost model

As in `CostModel.lean` / `CostEngines.lean`: a costed program returns `(result, cost)`, the
cost being computed by the recursion that computes the result.  New charges:

* a retirement test of one incidence `(p, c)` (membership flag and one comparison
  `u(c) < l(p)`): 1 unit;
* a retirement: two indexed-heap deletions in the heaps of `p` (one per endpoint),
  `⌈log₂ deg p⌉ + 1` units each, and two list unlinks (child list of `p`, parent list of
  `c`), 1 unit each.  The lists are Lean lists; the unit charge per unlink models doubly
  linked lists with handles and is a modelling convention;
* initialisation: 1 unit per internal gate (reading the heap root) and one heap insertion
  `⌈log₂ deg p⌉ + 1` per incidence and endpoint;
* a root query: one unit per root action and endpoint scanned.

Indexed heaps are charged as in `CostEngines.lean` (`⌈log₂ m⌉ + 1` per operation).  The
file `HeapImpl.lean` implements the heap with `⌈log₂ m⌉ + 2` computed steps per operation
and shows that `CostEngines.wave` run on implemented heaps costs at most twice its charge;
the two files do not import each other, so the theorems here are stated in the charged
model.

Which incidences are tested is decided by a retirement policy `cand` (any function of the
states before and after the wave); all theorems hold for every policy, and each test is
charged.  The delivery policy `delivCand` tests exactly the incidences along which the wave
delivered (changed child, parent live before the wave).  Its candidate list is defined
from the set of changed gates (which by `CostEngines.wave_spec` is the set of gates that
delivered), not emitted by `wave` itself; the unit charged per test covers recording it.

As in `CostEngines.lean`, a wave costs a scheduling term `L + 3` per endpoint that the
manuscript's bounds do not display (they have `T` where the bounds here have `T (2L + 6)`).
-/
import JointRootCert.CostEngines

namespace JointRootCert
namespace DagRetire

open Finset CostEngines

/-! ## Heap maxima and exact valuations -/

section Sem

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma heapMax_cons (c : ℕ) (cs : List ℕ) (k : ℕ → α) :
    heapMax (c :: cs) k = k c ⊔ heapMax cs k := rfl

lemma le_heapMax {cs : List ℕ} {c : ℕ} (k : ℕ → α) (h : c ∈ cs) : k c ≤ heapMax cs k := by
  induction cs with
  | nil => simp at h
  | cons a cs ih =>
    rw [heapMax_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_sup_left
    · exact (ih h).trans le_sup_right

lemma heapMax_le {cs : List ℕ} {k : ℕ → α} {b : α} (h : ∀ c ∈ cs, k c ≤ b) :
    heapMax cs k ≤ b := by
  induction cs with
  | nil => exact bot_le
  | cons a cs ih =>
    rw [heapMax_cons]
    exact sup_le (h a List.mem_cons_self) (ih (fun c hc => h c (List.mem_cons_of_mem _ hc)))

lemma heapMax_mono {cs : List ℕ} {k k' : ℕ → α} (h : ∀ c ∈ cs, k c ≤ k' c) :
    heapMax cs k ≤ heapMax cs k' :=
  heapMax_le (fun c hc => (h c hc).trans (le_heapMax k' hc))

/-- Dropping entries that are below the maximum of the remaining ones does not change the
maximum. -/
lemma heapMax_eq_of_sub {cs cs' : List ℕ} {k : ℕ → α} (h1 : ∀ c ∈ cs', c ∈ cs)
    (h2 : ∀ c ∈ cs, c ∈ cs' ∨ k c ≤ heapMax cs' k) : heapMax cs k = heapMax cs' k :=
  le_antisymm (heapMax_le (fun c hc => (h2 c hc).elim (le_heapMax k) id))
    (heapMax_le (fun c hc => le_heapMax k (h1 c hc)))

/-- Removing a key strictly below the heap maximum does not change the maximum. -/
lemma heapMax_erase {cs : List ℕ} {c : ℕ} {k : ℕ → α} (h : k c < heapMax cs k) :
    heapMax (cs.filter (· ≠ c)) k = heapMax cs k := by
  symm
  apply heapMax_eq_of_sub
  · intro c' hc'
    exact (List.mem_filter.1 hc').1
  · intro c' hc'
    by_cases e : c' = c
    · right
      subst e
      by_contra hlt
      have hlt' := lt_of_not_ge hlt
      have : heapMax cs k ≤ k c' := heapMax_le (fun d hd => by
        by_cases e : d = c'
        · rw [e]
        · exact (le_heapMax k (List.mem_filter.2 ⟨hd, by simpa using e⟩)).trans hlt'.le)
      exact absurd h (not_lt.2 this)
    · left
      exact List.mem_filter.2 ⟨hc', by simpa using e⟩

/-- A valuation of the gates is exact for the circuit `G` if every internal gate holds the
maximum of its children.  (Leaf values are the inputs.) -/
def Exact (G : Dag) (v : ℕ → α) : Prop :=
  ∀ g, G.children g ≠ [] → v g = heapMax (G.children g) v

lemma inv_exact {G : Dag} {s : EState α} (h : Inv G s) : Exact G s.val :=
  fun g hg => (h.gate g hg).trans (heapMax_congr (fun c hc => h.keys g c hc))

/-- Exact valuations are monotone in the leaf values. -/
theorem exact_mono {G : Dag} (hG : G.WF) {v v' : ℕ → α} (h : Exact G v) (h' : Exact G v')
    (hl : ∀ g, G.children g = [] → v g ≤ v' g) : ∀ g, v g ≤ v' g := by
  have key : ∀ n, ∀ g, G.level g < n → v g ≤ v' g := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg
      by_cases hc : G.children g = []
      · exact hl g hc
      · rw [h g hc, h' g hc]
        exact heapMax_mono (fun c hcm => ih c (by have := hG.level_lt g c hcm; omega))
  exact fun g => key (G.level g + 1) g (Nat.lt_succ_self _)

/-- **Uniqueness of the exact evaluation**: two exact valuations with the same leaf values
agree at every gate. -/
theorem exact_unique {G : Dag} (hG : G.WF) {v v' : ℕ → α} (h : Exact G v) (h' : Exact G v')
    (hl : ∀ g, G.children g = [] → v g = v' g) : ∀ g, v g = v' g :=
  fun g => le_antisymm (exact_mono hG h h' (fun g hg => (hl g hg).le) g)
    (exact_mono hG h' h (fun g hg => (hl g hg).ge) g)

end Sem

/-! ## Removing an incidence -/

/-- The circuit with the incidence `(p, c)` unlinked from the child list of `p` and from
the parent list of `c`. -/
def retireDag (G : Dag) (p c : ℕ) : Dag where
  N := G.N
  children := fun g => if g = p then (G.children g).filter (· ≠ c) else G.children g
  parents := fun g => if g = c then (G.parents g).filter (· ≠ p) else G.parents g
  level := G.level
  L := G.L

lemma mem_retire_children {G : Dag} {p c p' c' : ℕ} :
    c' ∈ (retireDag G p c).children p' ↔ c' ∈ G.children p' ∧ ¬ (p' = p ∧ c' = c) := by
  show c' ∈ (if p' = p then (G.children p').filter (· ≠ c) else G.children p') ↔ _
  by_cases h : p' = p
  · simp [h, List.mem_filter]
  · simp [h]

lemma mem_retire_parents {G : Dag} {p c p' c' : ℕ} :
    p' ∈ (retireDag G p c).parents c' ↔ p' ∈ G.parents c' ∧ ¬ (p' = p ∧ c' = c) := by
  show p' ∈ (if c' = c then (G.parents c').filter (· ≠ p) else G.parents c') ↔ _
  by_cases h : c' = c
  · simp [h, List.mem_filter]
  · simp [h]

lemma retire_children_sublist (G : Dag) (p c g : ℕ) :
    ((retireDag G p c).children g).Sublist (G.children g) := by
  show (if g = p then (G.children g).filter (· ≠ c) else G.children g).Sublist _
  split_ifs
  · exact List.filter_sublist
  · exact List.Sublist.refl _

lemma retire_parents_sublist (G : Dag) (p c g : ℕ) :
    ((retireDag G p c).parents g).Sublist (G.parents g) := by
  show (if g = c then (G.parents g).filter (· ≠ p) else G.parents g).Sublist _
  split_ifs
  · exact List.filter_sublist
  · exact List.Sublist.refl _

lemma retireDag_wf {G : Dag} (hG : G.WF) (p c : ℕ) : (retireDag G p c).WF where
  parents_iff := by
    intro c' p'
    rw [mem_retire_parents, mem_retire_children, hG.parents_iff]
  parents_nodup := fun c' => (hG.parents_nodup c').sublist (retire_parents_sublist G p c c')
  parent_lt := fun c' p' h => hG.parent_lt c' p' (mem_retire_parents.1 h).1
  level_lt := fun p' c' h => hG.level_lt p' c' (mem_retire_children.1 h).1
  level_le := hG.level_le

/-- Number of live incidences. -/
def live (G : Dag) : ℕ := ∑ p ∈ range G.N, (G.children p).length

lemma length_filter_ne_lt (cs : List ℕ) (c : ℕ) (h : c ∈ cs) :
    (cs.filter (· ≠ c)).length + 1 ≤ cs.length := by
  induction cs with
  | nil => simp at h
  | cons a cs ih =>
    by_cases e : a = c
    · have : ((a :: cs).filter (· ≠ c)) = cs.filter (· ≠ c) := by
        simp [e]
      rw [this, List.length_cons]
      exact Nat.succ_le_succ (List.length_filter_le _ _)
    · have hc : c ∈ cs := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm e
        · exact h
      have : ((a :: cs).filter (· ≠ c)) = a :: cs.filter (· ≠ c) := by
        simp [e]
      rw [this, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (ih hc)

/-- Unlinking a live incidence removes at least one live incidence. -/
lemma live_retire {G : Dag} (hG : G.WF) {p c : ℕ} (h : c ∈ G.children p) :
    live (retireDag G p c) + 1 ≤ live G := by
  have hp : p ∈ range G.N := mem_range.2 (hG.parent_lt c p ((hG.parents_iff c p).2 h))
  unfold live
  show ∑ g ∈ range G.N, ((retireDag G p c).children g).length + 1 ≤ _
  rw [← add_sum_erase _ _ hp, ← add_sum_erase _ (fun g => (G.children g).length) hp]
  have h1 : ∑ g ∈ (range G.N).erase p, ((retireDag G p c).children g).length
      = ∑ g ∈ (range G.N).erase p, (G.children g).length := by
    apply sum_congr rfl
    intro g hg
    have hne : g ≠ p := (mem_erase.1 hg).1
    show (if g = p then (G.children g).filter (· ≠ c) else G.children g).length = _
    rw [ite_eq_right hne]
  have h2 : ((retireDag G p c).children p).length + 1 ≤ (G.children p).length := by
    show (if p = p then (G.children p).filter (· ≠ c) else G.children p).length + 1 ≤ _
    rw [ite_eq_left rfl]
    exact length_filter_ne_lt _ _ h
  rw [h1]
  omega

/-! ## The engine state and the retirement step -/

section Retire

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- State of the interval engine with retirement: the current circuit (live incidences)
and the engine states of the lower and of the upper endpoint. -/
structure RState (α : Type*) where
  G : Dag
  lo : EState α
  hi : EState α

/-- Invariant of the engine relative to the original circuit `G0`. -/
structure RInv (G0 : Dag) (s : RState α) : Prop where
  wf : s.G.WF
  nEq : s.G.N = G0.N
  levelEq : s.G.level = G0.level
  lEq : s.G.L = G0.L
  csub : ∀ p, (s.G.children p).Sublist (G0.children p)
  psub : ∀ c, (s.G.parents c).Sublist (G0.parents c)
  invLo : Inv s.G s.lo
  invHi : Inv s.G s.hi
  cons : ∀ g, s.lo.val g ≤ s.hi.val g
  dom : ∀ p c, c ∈ G0.children p → c ∉ s.G.children p → s.hi.val c < s.lo.val p
  leaf : ∀ g, s.G.children g = [] → G0.children g = []

/-- **Exactness with respect to the original circuit** (`prop:representation-coupling`,
retirement part; `thm:protected-pruning`, rule (i)).  Under the invariant, the stored lower
and upper values are exact valuations of the ORIGINAL circuit `G0`, although only the live
incidences are maintained: every retired incidence `(p, c)` has `u(c) < l(p)` and so
determines neither endpoint of `p`. -/
theorem RInv.exact {G0 : Dag} {s : RState α} (h : RInv G0 s) :
    Exact G0 s.lo.val ∧ Exact G0 s.hi.val := by
  have hlo := inv_exact h.invLo
  have hhi := inv_exact h.invHi
  constructor
  · intro g hg
    have hg' : s.G.children g ≠ [] := fun e => hg (h.leaf g e)
    rw [hlo g hg']
    symm
    apply heapMax_eq_of_sub (fun c hc => (h.csub g).subset hc)
    intro c hc
    by_cases hm : c ∈ s.G.children g
    · exact Or.inl hm
    · right
      rw [← hlo g hg']
      exact (h.cons c).trans (h.dom g c hc hm).le
  · intro g hg
    have hg' : s.G.children g ≠ [] := fun e => hg (h.leaf g e)
    rw [hhi g hg']
    symm
    apply heapMax_eq_of_sub (fun c hc => (h.csub g).subset hc)
    intro c hc
    by_cases hm : c ∈ s.G.children g
    · exact Or.inl hm
    · right
      rw [← hhi g hg']
      exact (h.dom g c hc hm).le.trans (h.cons g)

lemma RInv.leaf_iff {G0 : Dag} {s : RState α} (h : RInv G0 s) (g : ℕ) :
    s.G.children g = [] ↔ G0.children g = [] :=
  ⟨h.leaf g, fun e => List.eq_nil_of_subset_nil (e ▸ (h.csub g).subset)⟩

/-- The initial state: all incidences live. -/
theorem RInv.init {G0 : Dag} (hG : G0.WF) {lo hi : EState α} (hlo : Inv G0 lo)
    (hhi : Inv G0 hi) (hleaf : ∀ g, G0.children g = [] → lo.val g ≤ hi.val g) :
    RInv G0 ⟨G0, lo, hi⟩ where
  wf := hG
  nEq := rfl
  levelEq := rfl
  lEq := rfl
  csub := fun _ => List.Sublist.refl _
  psub := fun _ => List.Sublist.refl _
  invLo := hlo
  invHi := hhi
  cons := exact_mono hG (inv_exact hlo) (inv_exact hhi) hleaf
  dom := fun _ _ h h' => absurd h h'
  leaf := fun _ h => h

/-- **Retirement test and retirement of one incidence** `e = (p, c)`.  The test (1 unit):
is the incidence live and is `u(c) < l(p)`?  If so, unlink it: two heap deletions in the
heaps of `p` (`⌈log₂ deg p⌉ + 1` each) and two list unlinks (1 unit each). -/
def retireOne (e : ℕ × ℕ) (s : RState α) : RState α × ℕ :=
  if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then
    (⟨retireDag s.G e.1 e.2, s.lo, s.hi⟩, 2 * Nat.clog 2 (s.G.children e.1).length + 5)
  else (s, 1)

/-- Process a list of candidate incidences. -/
def retireList : List (ℕ × ℕ) → RState α → RState α × ℕ
  | [], s => (s, 0)
  | e :: es, s =>
    ((retireList es (retireOne e s).1).1,
     (retireOne e s).2 + (retireList es (retireOne e s).1).2)

theorem retireOne_inv {G0 : Dag} {s : RState α} (h : RInv G0 s) (e : ℕ × ℕ) :
    RInv G0 (retireOne e s).1 := by
  unfold retireOne
  by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
  · rw [ite_eq_left hc]
    obtain ⟨hm, hlt⟩ := hc
    have hne : s.G.children e.1 ≠ [] := List.ne_nil_of_mem hm
    have hlo_lt : s.lo.key e.1 e.2 < heapMax (s.G.children e.1) (s.lo.key e.1) := by
      rw [← h.invLo.gate e.1 hne, h.invLo.keys e.1 e.2 hm]
      exact (h.cons e.2).trans_lt hlt
    have hhi_lt : s.hi.key e.1 e.2 < heapMax (s.G.children e.1) (s.hi.key e.1) := by
      rw [← h.invHi.gate e.1 hne, h.invHi.keys e.1 e.2 hm]
      exact hlt.trans_le (h.cons e.1)
    have hfl : heapMax ((s.G.children e.1).filter (· ≠ e.2)) (s.lo.key e.1) = s.lo.val e.1 := by
      rw [heapMax_erase hlo_lt, ← h.invLo.gate e.1 hne]
    have hfh : heapMax ((s.G.children e.1).filter (· ≠ e.2)) (s.hi.key e.1) = s.hi.val e.1 := by
      rw [heapMax_erase hhi_lt, ← h.invHi.gate e.1 hne]
    have hch : ∀ g, (retireDag s.G e.1 e.2).children g
        = if g = e.1 then (s.G.children g).filter (· ≠ e.2) else s.G.children g := fun _ => rfl
    refine ⟨retireDag_wf h.wf _ _, h.nEq, h.levelEq, h.lEq,
      fun p => (retire_children_sublist _ _ _ p).trans (h.csub p),
      fun c => (retire_parents_sublist _ _ _ c).trans (h.psub c), ⟨?_, ?_⟩, ⟨?_, ?_⟩, h.cons,
      ?_, ?_⟩
    · intro g hg
      show s.lo.val g = heapMax ((retireDag s.G e.1 e.2).children g) (s.lo.key g)
      rw [hch] at hg ⊢
      by_cases hge : g = e.1
      · subst hge
        rw [ite_eq_left rfl]
        exact hfl.symm
      · rw [ite_eq_right hge] at hg ⊢
        exact h.invLo.gate g hg
    · intro p c hcm
      exact h.invLo.keys p c (mem_retire_children.1 hcm).1
    · intro g hg
      show s.hi.val g = heapMax ((retireDag s.G e.1 e.2).children g) (s.hi.key g)
      rw [hch] at hg ⊢
      by_cases hge : g = e.1
      · subst hge
        rw [ite_eq_left rfl]
        exact hfh.symm
      · rw [ite_eq_right hge] at hg ⊢
        exact h.invHi.gate g hg
    · intro p c hcm
      exact h.invHi.keys p c (mem_retire_children.1 hcm).1
    · intro p c hc0 hnc
      show s.hi.val c < s.lo.val p
      by_cases hold : c ∈ s.G.children p
      · have : p = e.1 ∧ c = e.2 := by
          by_contra hcon
          exact hnc (mem_retire_children.2 ⟨hold, hcon⟩)
        rw [this.1, this.2]
        exact hlt
      · exact h.dom p c hc0 hold
    · intro g hg
      show G0.children g = []
      rw [hch] at hg
      by_cases hge : g = e.1
      · subst hge
        rw [ite_eq_left rfl] at hg
        exfalso
        rw [hg] at hfl
        have : s.lo.val e.1 = ⊥ := hfl.symm
        rw [this] at hlt
        exact not_lt_bot hlt
      · rw [ite_eq_right hge] at hg
        exact h.leaf g hg
  · rw [ite_eq_right hc]
    exact h

omit [OrderBot α] in
lemma retireOne_endpoints (e : ℕ × ℕ) (s : RState α) :
    (retireOne e s).1.lo = s.lo ∧ (retireOne e s).1.hi = s.hi ∧
    (retireOne e s).1.G.N = s.G.N ∧
    (∀ g, ((retireOne e s).1.G.parents g).Sublist (s.G.parents g)) ∧
    1 ≤ (retireOne e s).2 := by
  unfold retireOne
  split_ifs
  · exact ⟨rfl, rfl, rfl, fun g => retire_parents_sublist _ _ _ g, by omega⟩
  · exact ⟨rfl, rfl, rfl, fun g => List.Sublist.refl _, le_rfl⟩

omit [OrderBot α] in
/-- Cost of one test: at most `1` plus `2 ⌈log₂ D⌉ + 4` per incidence actually removed. -/
lemma retireOne_cost {s : RState α} (hG : s.G.WF) (D : ℕ)
    (hD : ∀ p, (s.G.children p).length ≤ D) (e : ℕ × ℕ) :
    (retireOne e s).2 + (2 * Nat.clog 2 D + 4) * live (retireOne e s).1.G
      ≤ 1 + (2 * Nat.clog 2 D + 4) * live s.G := by
  unfold retireOne
  by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
  · rw [ite_eq_left hc]
    have h1 := live_retire hG hc.1
    have h2 : Nat.clog 2 (s.G.children e.1).length ≤ Nat.clog 2 D :=
      Nat.clog_mono_right 2 (hD e.1)
    show 2 * Nat.clog 2 (s.G.children e.1).length + 5
        + (2 * Nat.clog 2 D + 4) * live (retireDag s.G e.1 e.2) ≤ _
    have h3 := Nat.mul_le_mul_left (2 * Nat.clog 2 D + 4) h1
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega
  · rw [ite_eq_right hc]

theorem retireList_inv {G0 : Dag} : ∀ (L : List (ℕ × ℕ)) (s : RState α), RInv G0 s →
    RInv G0 (retireList L s).1 := by
  intro L
  induction L with
  | nil => intro s h; exact h
  | cons e es ih => intro s h; exact ih _ (retireOne_inv h e)

omit [OrderBot α] in
lemma retireList_endpoints : ∀ (L : List (ℕ × ℕ)) (s : RState α),
    (retireList L s).1.lo = s.lo ∧ (retireList L s).1.hi = s.hi ∧
    (retireList L s).1.G.N = s.G.N ∧
    (∀ g, ((retireList L s).1.G.parents g).Sublist (s.G.parents g)) ∧
    L.length ≤ (retireList L s).2 := by
  intro L
  induction L with
  | nil => intro s; exact ⟨rfl, rfl, rfl, fun g => List.Sublist.refl _, le_rfl⟩
  | cons e es ih =>
    intro s
    obtain ⟨a1, a2, a3, a4, a5⟩ := retireOne_endpoints e s
    obtain ⟨b1, b2, b3, b4, b5⟩ := ih (retireOne e s).1
    refine ⟨b1.trans a1, b2.trans a2, b3.trans a3, fun g => (b4 g).trans (a4 g), ?_⟩
    show es.length + 1 ≤ (retireOne e s).2 + (retireList es (retireOne e s).1).2
    omega

/-- **Cost of a retirement pass**: one unit per test plus `2 ⌈log₂ D⌉ + 4` per incidence
removed (potential argument: every incidence is removed at most once). -/
theorem retireList_cost {G0 : Dag} (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D) :
    ∀ (L : List (ℕ × ℕ)) (s : RState α), RInv G0 s →
      (retireList L s).2 + (2 * Nat.clog 2 D + 4) * live (retireList L s).1.G
        ≤ L.length + (2 * Nat.clog 2 D + 4) * live s.G := by
  intro L
  induction L with
  | nil => intro s _; simp [retireList]
  | cons e es ih =>
    intro s h
    have h1 := retireOne_cost h.wf D (fun p => ((h.csub p).length_le).trans (hD p)) e
    have h2 := ih _ (retireOne_inv h e)
    show (retireOne e s).2 + (retireList es (retireOne e s).1).2
        + (2 * Nat.clog 2 D + 4) * live (retireList es (retireOne e s).1).1.G ≤ _
    rw [List.length_cons]
    omega

/-! ## One rollout: wave, then retirement -/

/-- The backup waves of one terminal update `u = (x, l, u)` on the live circuit. -/
def waveStep (u : ℕ × α × α) (s : RState α) : RState α × ℕ :=
  (⟨s.G, (wave s.G u.1 u.2.1 s.lo).1, (wave s.G u.1 u.2.2 s.hi).1⟩,
   (wave s.G u.1 u.2.1 s.lo).2 + (wave s.G u.1 u.2.2 s.hi).2)

/-- A nested terminal update preserves the invariant: the lower endpoint of the terminal
does not decrease, the upper one does not increase, and the interval is nonempty. -/
theorem waveStep_inv {G0 : Dag} {s : RState α} (h : RInv G0 s) (u : ℕ × α × α)
    (hx : u.1 < G0.N) (h1 : s.lo.val u.1 ≤ u.2.1) (h2 : u.2.1 ≤ u.2.2)
    (h3 : u.2.2 ≤ s.hi.val u.1) : RInv G0 (waveStep u s).1 := by
  obtain ⟨l1, l2, l3, _⟩ := wave_spec h.wf u.1 u.2.1 s.lo (h.nEq ▸ hx) h.invLo
  obtain ⟨u1, u2, u3, _⟩ := wave_spec h.wf u.1 u.2.2 s.hi (h.nEq ▸ hx) h.invHi
  have hcons : ∀ g, (wave s.G u.1 u.2.1 s.lo).1.val g ≤ (wave s.G u.1 u.2.2 s.hi).1.val g := by
    apply exact_mono h.wf (inv_exact l1) (inv_exact u1)
    intro g hg
    by_cases hgx : g = u.1
    · subst hgx
      rw [l2 hg, u2 hg]
      exact h2
    · rw [l3 g hg hgx, u3 g hg hgx]
      exact h.cons g
  have hlo : ∀ g, s.lo.val g ≤ (wave s.G u.1 u.2.1 s.lo).1.val g := by
    apply exact_mono h.wf (inv_exact h.invLo) (inv_exact l1)
    intro g hg
    by_cases hgx : g = u.1
    · subst hgx
      rw [l2 hg]
      exact h1
    · rw [l3 g hg hgx]
  have hhi : ∀ g, (wave s.G u.1 u.2.2 s.hi).1.val g ≤ s.hi.val g := by
    apply exact_mono h.wf (inv_exact u1) (inv_exact h.invHi)
    intro g hg
    by_cases hgx : g = u.1
    · subst hgx
      rw [u2 hg]
      exact h3
    · rw [u3 g hg hgx]
  exact ⟨h.wf, h.nEq, h.levelEq, h.lEq, h.csub, h.psub, l1, u1, hcons,
    fun p c hc hnc => ((hhi c).trans_lt (h.dom p c hc hnc)).trans_le (hlo p), h.leaf⟩

/-- **One rollout of the engine with retirement**: the waves of the terminal update, then
a retirement pass over the candidates chosen by the policy `cand` from the states before
and after the waves. -/
def rstep (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ × α × α) (s : RState α) :
    RState α × ℕ :=
  ((retireList (cand s (waveStep u s).1) (waveStep u s).1).1,
   (waveStep u s).2 + (retireList (cand s (waveStep u s).1) (waveStep u s).1).2)

/-- The delivery policy: test every incidence along which the waves delivered, that is
every `(p, g)` with `g` a gate one of whose endpoints changed and `p` a parent of `g` live
before the wave. -/
def delivCand (s s1 : RState α) : List (ℕ × ℕ) :=
  ((List.range s.G.N).filter
      (fun g => s1.lo.val g ≠ s.lo.val g ∨ s1.hi.val g ≠ s.hi.val g)).flatMap
    (fun g => (s.G.parents g).map (fun p => (p, g)))

lemma sum_filter_or_le (f : ℕ → ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] :
    ∀ l : List ℕ, ((l.filter (fun g => p g ∨ q g)).map f).sum
      ≤ ((l.filter (fun g => p g)).map f).sum + ((l.filter (fun g => q g)).map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih
    simp only [Bool.decide_or] at ih'
    by_cases hp : p a <;> by_cases hq : q a <;>
      simp [hp, hq] <;> omega

lemma sum_range_filter (f : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (((List.range N).filter (fun g => p g)).map f).sum = ∑ g ∈ (range N).filter p, f g := by
  rw [← List.sum_toFinset f ((List.nodup_range).filter _)]
  apply sum_congr _ (fun _ _ => rfl)
  ext g
  simp

omit [OrderBot α] in
/-- The delivery policy tests at most as many incidences as the waves delivered along. -/
lemma delivCand_length (s s1 : RState α) :
    (delivCand s s1).length ≤ vol s.G s.lo s1.lo + vol s.G s.hi s1.hi := by
  unfold delivCand vol
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [← sum_range_filter (fun g => (s.G.parents g).length)
      (fun g => s1.lo.val g ≠ s.lo.val g) s.G.N,
    ← sum_range_filter (fun g => (s.G.parents g).length)
      (fun g => s1.hi.val g ≠ s.hi.val g) s.G.N]
  exact sum_filter_or_le (fun g => (s.G.parents g).length) _ _ _

/-- **Correctness and cost of one rollout.**  From a state satisfying the invariant, after
a nested terminal update:

* the invariant holds again (so the stored intervals are exact for the original circuit);
* the lower and upper states are those produced by the waves on the pre-update live
  circuit; the updated terminal holds the new endpoints and other terminals are unchanged;
* the cost is at least the number of deliveries on the pre-update live set plus the number
  of tests, and, together with `2 ⌈log₂ D⌉ + 4` per live incidence remaining, at most
  `2 (L + 3) + (⌈log₂ D⌉ + 3) · (deliveries) + (tests)` plus the same potential before. -/
theorem rstep_spec {G0 : Dag} (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (cand : RState α → RState α → List (ℕ × ℕ)) {s : RState α} (h : RInv G0 s)
    (u : ℕ × α × α) (hx : u.1 < G0.N) (h1 : s.lo.val u.1 ≤ u.2.1) (h2 : u.2.1 ≤ u.2.2)
    (h3 : u.2.2 ≤ s.hi.val u.1) :
    RInv G0 (rstep cand u s).1 ∧
    (rstep cand u s).1.lo = (wave s.G u.1 u.2.1 s.lo).1 ∧
    (rstep cand u s).1.hi = (wave s.G u.1 u.2.2 s.hi).1 ∧
    (G0.children u.1 = [] →
      (rstep cand u s).1.lo.val u.1 = u.2.1 ∧ (rstep cand u s).1.hi.val u.1 = u.2.2) ∧
    (∀ g, G0.children g = [] → g ≠ u.1 →
      (rstep cand u s).1.lo.val g = s.lo.val g ∧ (rstep cand u s).1.hi.val g = s.hi.val g) ∧
    (rstep cand u s).1.G.N = G0.N ∧
    (∀ g, ((rstep cand u s).1.G.parents g).Sublist (s.G.parents g)) ∧
    vol s.G s.lo (rstep cand u s).1.lo + vol s.G s.hi (rstep cand u s).1.hi
        + (cand s (waveStep u s).1).length ≤ (rstep cand u s).2 ∧
    (rstep cand u s).2 + (2 * Nat.clog 2 D + 4) * live (rstep cand u s).1.G
      ≤ 2 * (G0.L + 3)
        + (Nat.clog 2 D + 3)
          * (vol s.G s.lo (rstep cand u s).1.lo + vol s.G s.hi (rstep cand u s).1.hi)
        + (cand s (waveStep u s).1).length + (2 * Nat.clog 2 D + 4) * live s.G := by
  have hw := waveStep_inv h u hx h1 h2 h3
  obtain ⟨l1, l2, l3, l4⟩ := wave_spec h.wf u.1 u.2.1 s.lo (h.nEq ▸ hx) h.invLo
  obtain ⟨u1, u2, u3, u4⟩ := wave_spec h.wf u.1 u.2.2 s.hi (h.nEq ▸ hx) h.invHi
  obtain ⟨e1, e2, e3, e4, e5⟩ :=
    retireList_endpoints (cand s (waveStep u s).1) (waveStep u s).1
  have hc := retireList_cost D hD (cand s (waveStep u s).1) (waveStep u s).1 hw
  have hDs : ∀ p, (s.G.children p).length ≤ D := fun p => ((h.csub p).length_le).trans (hD p)
  have bl := chgSum_bounds D hDs s.lo (wave s.G u.1 u.2.1 s.lo).1
  have bh := chgSum_bounds D hDs s.hi (wave s.G u.1 u.2.2 s.hi).1
  have elo : (rstep cand u s).1.lo = (wave s.G u.1 u.2.1 s.lo).1 := e1
  have ehi : (rstep cand u s).1.hi = (wave s.G u.1 u.2.2 s.hi).1 := e2
  have hcost : (rstep cand u s).2
      = (wave s.G u.1 u.2.1 s.lo).2 + (wave s.G u.1 u.2.2 s.hi).2
        + (retireList (cand s (waveStep u s).1) (waveStep u s).1).2 := rfl
  have hlive : live (waveStep u s).1.G = live s.G := rfl
  have hL : s.G.L = G0.L := h.lEq
  refine ⟨retireList_inv _ _ hw, elo, ehi, ?_, ?_, e3.trans h.nEq, e4, ?_, ?_⟩
  · intro hl
    have hl' := (h.leaf_iff u.1).2 hl
    rw [elo, ehi]
    exact ⟨l2 hl', u2 hl'⟩
  · intro g hl hg
    have hl' := (h.leaf_iff g).2 hl
    rw [elo, ehi]
    exact ⟨l3 g hl' hg, u3 g hl' hg⟩
  · rw [elo, ehi, hcost, l4, u4]
    omega
  · rw [elo, ehi, hcost, l4, u4, hL]
    have : (retireList (cand s (waveStep u s).1) (waveStep u s).1).1 = (rstep cand u s).1 := rfl
    rw [this, hlive] at hc
    nlinarith [bl.2, bh.2]

end Retire

/-! ## Runs: exactness and total work over the changing live sets -/

section Run

variable {α : Type*} [LinearOrder α] [OrderBot α]

omit [OrderBot α] in
lemma retireList_children : ∀ (L : List (ℕ × ℕ)) (s : RState α) (g : ℕ),
    ((retireList L s).1.G.children g).Sublist (s.G.children g) := by
  intro L
  induction L with
  | nil => intro s g; exact List.Sublist.refl _
  | cons e es ih =>
    intro s g
    refine (ih (retireOne e s).1 g).trans ?_
    unfold retireOne
    split_ifs
    · exact retire_children_sublist _ _ _ g
    · exact List.Sublist.refl _

omit [OrderBot α] in
lemma vol_le_of_sub {G G' : Dag} (hN : G'.N = G.N)
    (hp : ∀ g, (G'.parents g).Sublist (G.parents g)) (a b : EState α) :
    vol G' a b ≤ vol G a b := by
  unfold vol
  rw [hN]
  exact sum_le_sum (fun g _ => (hp g).length_le)

omit [OrderBot α] in
lemma vol_congr (G : Dag) {a a' b b' : EState α} (ha : ∀ g, a.val g = a'.val g)
    (hb : ∀ g, b.val g = b'.val g) : vol G a b = vol G a' b' := by
  unfold vol
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr
  intro g _
  rw [ha g, hb g]

lemma rstep_endpoints (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ × α × α)
    (s : RState α) :
    (rstep cand u s).1.lo = (wave s.G u.1 u.2.1 s.lo).1 ∧
    (rstep cand u s).1.hi = (wave s.G u.1 u.2.2 s.hi).1 ∧
    (rstep cand u s).1.G.N = s.G.N ∧
    (∀ g, ((rstep cand u s).1.G.parents g).Sublist (s.G.parents g)) ∧
    (∀ g, ((rstep cand u s).1.G.children g).Sublist (s.G.children g)) := by
  obtain ⟨e1, e2, e3, e4, _⟩ :=
    retireList_endpoints (cand s (waveStep u s).1) (waveStep u s).1
  exact ⟨e1, e2, e3, e4, fun g => retireList_children _ _ g⟩

lemma rstep_live_le (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ × α × α)
    (s : RState α) : live (rstep cand u s).1.G ≤ live s.G := by
  obtain ⟨_, _, e3, _, e5⟩ := rstep_endpoints cand u s
  unfold live
  rw [e3]
  exact sum_le_sum (fun g _ => (e5 g).length_le)

/-- State after `t` rollouts; rollout `t + 1` applies the terminal update `u (t + 1)`. -/
def rrun (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α) (s0 : RState α) :
    ℕ → RState α
  | 0 => s0
  | t + 1 => (rstep cand (u (t + 1)) (rrun cand u s0 t)).1

/-- Cost of rollout `t + 1` (waves and retirement pass). -/
def stepCost (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α)
    (s0 : RState α) (t : ℕ) : ℕ :=
  (rstep cand (u (t + 1)) (rrun cand u s0 t)).2

/-- Pre-update delivery volume of rollout `t + 1`: `Σ_v b_{t+1}(v) d⁻_{F_t}(v)`, where
`b_{t+1}(v)` counts the endpoints of `v` changed by the rollout and `F_t` is the live
incidence set before it. -/
def stepPlus (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α)
    (s0 : RState α) (t : ℕ) : ℕ :=
  vol (rrun cand u s0 t).G (rrun cand u s0 t).lo (rrun cand u s0 (t + 1)).lo
    + vol (rrun cand u s0 t).G (rrun cand u s0 t).hi (rrun cand u s0 (t + 1)).hi

/-- Post-update delivery volume of rollout `t + 1`: `Σ_v b_{t+1}(v) d⁻_{F_{t+1}}(v)`. -/
def stepMinus (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α)
    (s0 : RState α) (t : ℕ) : ℕ :=
  vol (rrun cand u s0 (t + 1)).G (rrun cand u s0 t).lo (rrun cand u s0 (t + 1)).lo
    + vol (rrun cand u s0 (t + 1)).G (rrun cand u s0 t).hi (rrun cand u s0 (t + 1)).hi

/-- Number of retirement tests of rollout `t + 1`. -/
def stepTests (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α)
    (s0 : RState α) (t : ℕ) : ℕ :=
  (cand (rrun cand u s0 t) (waveStep (u (t + 1)) (rrun cand u s0 t)).1).length

/-- The terminal updates are nested along the run: each update addresses a gate, does not
decrease the stored lower endpoint, does not increase the stored upper endpoint, and keeps
the interval nonempty (cumulative intersections of confidence intervals,
`eq:terminal-box`). -/
def NestedRun (G0 : Dag) (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α)
    (s0 : RState α) : Prop :=
  ∀ t, (u (t + 1)).1 < G0.N ∧
    (rrun cand u s0 t).lo.val (u (t + 1)).1 ≤ (u (t + 1)).2.1 ∧
    (u (t + 1)).2.1 ≤ (u (t + 1)).2.2 ∧
    (u (t + 1)).2.2 ≤ (rrun cand u s0 t).hi.val (u (t + 1)).1

variable {G0 : Dag} {cand : RState α → RState α → List (ℕ × ℕ)} {u : ℕ → ℕ × α × α}
  {s0 : RState α}

theorem rrun_inv (h0 : RInv G0 s0) (hn : NestedRun G0 cand u s0) :
    ∀ t, RInv G0 (rrun cand u s0 t) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    obtain ⟨a, b, c, d⟩ := hn t
    exact retireList_inv _ _ (waveStep_inv ih _ a b c d)

/-- **Exactness along the run** (`prop:representation-coupling` with retirement).  At every
time the stored lower and upper values are exact valuations of the original circuit `G0`;
a rollout sets the endpoints of its terminal and leaves the other terminals unchanged.  By
`exact_unique` the stored intervals are therefore the ones any exact evaluation of `G0`
computes from the same terminal intervals. -/
theorem rrun_exact (h0 : RInv G0 s0) (hn : NestedRun G0 cand u s0) (t : ℕ) :
    Exact G0 (rrun cand u s0 t).lo.val ∧ Exact G0 (rrun cand u s0 t).hi.val ∧
    (G0.children (u (t + 1)).1 = [] →
      (rrun cand u s0 (t + 1)).lo.val (u (t + 1)).1 = (u (t + 1)).2.1 ∧
      (rrun cand u s0 (t + 1)).hi.val (u (t + 1)).1 = (u (t + 1)).2.2) ∧
    (∀ g, G0.children g = [] → g ≠ (u (t + 1)).1 →
      (rrun cand u s0 (t + 1)).lo.val g = (rrun cand u s0 t).lo.val g ∧
      (rrun cand u s0 (t + 1)).hi.val g = (rrun cand u s0 t).hi.val g) := by
  have hI := rrun_inv h0 hn t
  obtain ⟨a, _, _, _⟩ := hn t
  obtain ⟨e1, e2, _⟩ := rstep_endpoints cand (u (t + 1)) (rrun cand u s0 t)
  obtain ⟨_, l2, l3, _⟩ := wave_spec hI.wf (u (t + 1)).1 (u (t + 1)).2.1
    (rrun cand u s0 t).lo (hI.nEq ▸ a) hI.invLo
  obtain ⟨_, u2, u3, _⟩ := wave_spec hI.wf (u (t + 1)).1 (u (t + 1)).2.2
    (rrun cand u s0 t).hi (hI.nEq ▸ a) hI.invHi
  have elo : (rrun cand u s0 (t + 1)).lo
      = (wave (rrun cand u s0 t).G (u (t + 1)).1 (u (t + 1)).2.1 (rrun cand u s0 t).lo).1 := e1
  have ehi : (rrun cand u s0 (t + 1)).hi
      = (wave (rrun cand u s0 t).G (u (t + 1)).1 (u (t + 1)).2.2 (rrun cand u s0 t).hi).1 := e2
  refine ⟨hI.exact.1, hI.exact.2, fun hl => ?_, fun g hl hg => ?_⟩
  · have hl' := (hI.leaf_iff _).2 hl
    rw [elo, ehi]
    exact ⟨l2 hl', u2 hl'⟩
  · have hl' := (hI.leaf_iff g).2 hl
    rw [elo, ehi]
    exact ⟨l3 g hl' hg, u3 g hl' hg⟩

/-- **Work of a run, any retirement policy.**  With all gate degrees of the original
circuit at most `D`, for `τ` rollouts:

* total cost `≥ S⁺ + (number of tests)`;
* total cost `+ (2⌈log₂ D⌉ + 4) · |F_τ| ≤ 2τ(L + 3) + (⌈log₂ D⌉ + 3) S⁺ + (tests)
  + (2⌈log₂ D⌉ + 4) · |F_0|`, i.e. every incidence pays for its retirement at most once;
* `S⁻ ≤ S⁺` and `|F_τ| ≤ |F_0|`,

where `S⁺ = Σ_t Σ_v b_t(v) d⁻_{F_{t-1}}(v)` and `S⁻ = Σ_t Σ_v b_t(v) d⁻_{F_t}(v)` are the
delivery volumes of `eq:s-plus-minus` over the changing live sets. -/
theorem run_work (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D) (h0 : RInv G0 s0)
    (hn : NestedRun G0 cand u s0) (τ : ℕ) :
    (∑ t ∈ range τ, (stepPlus cand u s0 t + stepTests cand u s0 t)
      ≤ ∑ t ∈ range τ, stepCost cand u s0 t) ∧
    (∑ t ∈ range τ, stepCost cand u s0 t
        + (2 * Nat.clog 2 D + 4) * live (rrun cand u s0 τ).G
      ≤ 2 * τ * (G0.L + 3) + (Nat.clog 2 D + 3) * ∑ t ∈ range τ, stepPlus cand u s0 t
        + ∑ t ∈ range τ, stepTests cand u s0 t + (2 * Nat.clog 2 D + 4) * live s0.G) ∧
    (∑ t ∈ range τ, stepMinus cand u s0 t ≤ ∑ t ∈ range τ, stepPlus cand u s0 t) ∧
    live (rrun cand u s0 τ).G ≤ live s0.G := by
  have hstep : ∀ t, (stepPlus cand u s0 t + stepTests cand u s0 t ≤ stepCost cand u s0 t) ∧
      (stepCost cand u s0 t + (2 * Nat.clog 2 D + 4) * live (rrun cand u s0 (t + 1)).G
        ≤ 2 * (G0.L + 3) + (Nat.clog 2 D + 3) * stepPlus cand u s0 t
          + stepTests cand u s0 t + (2 * Nat.clog 2 D + 4) * live (rrun cand u s0 t).G) ∧
      stepMinus cand u s0 t ≤ stepPlus cand u s0 t ∧
      live (rrun cand u s0 (t + 1)).G ≤ live (rrun cand u s0 t).G := by
    intro t
    obtain ⟨a, b, c, d⟩ := hn t
    obtain ⟨_, _, _, _, _, _, _, r8, r9⟩ :=
      rstep_spec D hD cand (rrun_inv h0 hn t) (u (t + 1)) a b c d
    obtain ⟨_, _, e3, e4, _⟩ := rstep_endpoints cand (u (t + 1)) (rrun cand u s0 t)
    exact ⟨r8, r9, Nat.add_le_add (vol_le_of_sub e3 e4 _ _) (vol_le_of_sub e3 e4 _ _),
      rstep_live_le _ _ _⟩
  refine ⟨sum_le_sum (fun t _ => (hstep t).1), ?_, sum_le_sum (fun t _ => (hstep t).2.2.1), ?_⟩
  · induction τ with
    | zero => simp [rrun]
    | succ τ ih =>
      rw [sum_range_succ, sum_range_succ, sum_range_succ]
      have := (hstep τ).2.1
      nlinarith
  · induction τ with
    | zero => exact le_rfl
    | succ τ ih => exact ((hstep τ).2.2.2).trans ih

lemma deliv_tests_le (u : ℕ → ℕ × α × α) (s0 : RState α) (t : ℕ) :
    stepTests delivCand u s0 t ≤ stepPlus delivCand u s0 t := by
  have h := delivCand_length (rrun delivCand u s0 t)
    (waveStep (u (t + 1)) (rrun delivCand u s0 t)).1
  obtain ⟨e1, e2, _⟩ := rstep_endpoints delivCand (u (t + 1)) (rrun delivCand u s0 t)
  have elo : (rrun delivCand u s0 (t + 1)).lo
      = (waveStep (u (t + 1)) (rrun delivCand u s0 t)).1.lo := e1
  have ehi : (rrun delivCand u s0 (t + 1)).hi
      = (waveStep (u (t + 1)) (rrun delivCand u s0 t)).1.hi := e2
  unfold stepTests stepPlus
  rw [elo, ehi]
  exact h

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, with online retirement.**
Let `W = P + Σ_{t ≤ τ} (cost of rollout t)` be the total work of the engine with the
delivery retirement policy (upfront work `P`).  With `e = |F_0|` the initial number of live
incidences, `R = |F_0| - |F_τ|` the number of incidences retired, and
`H = 2τ(L + 3)` the level scheduling of the waves:

* `W ≤ P + H + (⌈log₂ D⌉ + 4) S⁺ + (2⌈log₂ D⌉ + 4) R`;
* `W ≤ 4 (H + P + (S⁺ + e)(⌈log₂ D⌉ + 1))`, which is `eq:prop-rep-upper`;
* `P + S⁻ ≤ P + S⁺ ≤ W` (the lower bound for this engine).

`S⁺`, `S⁻` are taken over the changing live sets `F_t`. -/
theorem representation_cost_retire (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 s0) (hn : NestedRun G0 delivCand u s0) (τ P : ℕ) :
    (P + ∑ t ∈ range τ, stepCost delivCand u s0 t
      ≤ P + 2 * τ * (G0.L + 3)
        + (Nat.clog 2 D + 4) * ∑ t ∈ range τ, stepPlus delivCand u s0 t
        + (2 * Nat.clog 2 D + 4) * (live s0.G - live (rrun delivCand u s0 τ).G)) ∧
    (P + ∑ t ∈ range τ, stepCost delivCand u s0 t
      ≤ 4 * (2 * τ * (G0.L + 3) + P
        + (∑ t ∈ range τ, stepPlus delivCand u s0 t + live s0.G) * (Nat.clog 2 D + 1))) ∧
    (P + ∑ t ∈ range τ, stepMinus delivCand u s0 t
      ≤ P + ∑ t ∈ range τ, stepPlus delivCand u s0 t) ∧
    (P + ∑ t ∈ range τ, stepPlus delivCand u s0 t
      ≤ P + ∑ t ∈ range τ, stepCost delivCand u s0 t) := by
  obtain ⟨w1, w2, w3, w4⟩ := run_work D hD h0 hn τ
  have ht : ∑ t ∈ range τ, stepTests delivCand u s0 t
      ≤ ∑ t ∈ range τ, stepPlus delivCand u s0 t :=
    sum_le_sum (fun t _ => deliv_tests_le u s0 t)
  have hsub : (2 * Nat.clog 2 D + 4) * (live s0.G - live (rrun delivCand u s0 τ).G)
      + (2 * Nat.clog 2 D + 4) * live (rrun delivCand u s0 τ).G
      = (2 * Nat.clog 2 D + 4) * live s0.G := by
    rw [← Nat.mul_add, Nat.sub_add_cancel w4]
  have h1 : P + ∑ t ∈ range τ, stepCost delivCand u s0 t
      ≤ P + 2 * τ * (G0.L + 3)
        + (Nat.clog 2 D + 4) * ∑ t ∈ range τ, stepPlus delivCand u s0 t
        + (2 * Nat.clog 2 D + 4) * (live s0.G - live (rrun delivCand u s0 τ).G) := by
    nlinarith
  refine ⟨h1, ?_, Nat.add_le_add_left w3 P, ?_⟩
  · have h2 : (2 * Nat.clog 2 D + 4) * (live s0.G - live (rrun delivCand u s0 τ).G)
        ≤ (2 * Nat.clog 2 D + 4) * live s0.G := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith [Nat.zero_le (Nat.clog 2 D * ∑ t ∈ range τ, stepPlus delivCand u s0 t),
      Nat.zero_le (Nat.clog 2 D * live s0.G),
      Nat.zero_le (∑ t ∈ range τ, stepPlus delivCand u s0 t), Nat.zero_le (live s0.G),
      Nat.zero_le (τ * (G0.L + 3)), Nat.zero_le P]
  · have : ∑ t ∈ range τ, stepPlus delivCand u s0 t
        ≤ ∑ t ∈ range τ, (stepPlus delivCand u s0 t + stepTests delivCand u s0 t) :=
      sum_le_sum (fun t _ => Nat.le_add_right _ _)
    omega

end Run

/-! ## Coupling with the eager (full-incidence) engine and `eq:ram-work-bounds` -/

section Eager

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Root query: scan the root actions, one unit per action. -/
def scanMax (v : ℕ → α) : List ℕ → α × ℕ
  | [] => (⊥, 0)
  | a :: as => (v a ⊔ (scanMax v as).1, (scanMax v as).2 + 1)

lemma scanMax_spec (v : ℕ → α) (l : List ℕ) : scanMax v l = (heapMax l v, l.length) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [scanMax, ih, List.length_cons]; rfl

/-- **Root query**: the largest lower and the largest upper endpoint over the root actions
(two scans of the `K` root gates). -/
def rootQuery (roots : List ℕ) (lo hi : EState α) : (α × α) × ℕ :=
  (((scanMax lo.val roots).1, (scanMax hi.val roots).1),
   (scanMax lo.val roots).2 + (scanMax hi.val roots).2)

lemma rootQuery_spec (roots : List ℕ) (lo hi : EState α) :
    rootQuery roots lo hi = ((heapMax roots lo.val, heapMax roots hi.val), 2 * roots.length) := by
  unfold rootQuery
  rw [scanMax_spec, scanMax_spec]
  simp only [Prod.mk.injEq, true_and]
  omega

variable {G0 : Dag} {cand : RState α → RState α → List (ℕ × ℕ)} {u : ℕ → ℕ × α × α}
  {lo0 hi0 : EState α}

/-- **Graph-Eager and Graph-Selective store the same intervals** (`prop:uct-coupling`,
numerical coupling).  Along nested updates, the engine with retirement (any policy) and the
full-incidence engine `CostEngines.runState` on the original circuit hold the same lower
and upper value at every gate at every time; the eager engine keeps its invariant. -/
theorem live_eq_eager (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 cand u ⟨G0, lo0, hi0⟩) : ∀ t,
    Inv G0 (runState G0 u (lo0, hi0) t).1 ∧ Inv G0 (runState G0 u (lo0, hi0) t).2 ∧
    (∀ g, (rrun cand u ⟨G0, lo0, hi0⟩ t).lo.val g = (runState G0 u (lo0, hi0) t).1.val g) ∧
    (∀ g, (rrun cand u ⟨G0, lo0, hi0⟩ t).hi.val g = (runState G0 u (lo0, hi0) t).2.val g) := by
  intro t
  induction t with
  | zero => exact ⟨h0.invLo, h0.invHi, fun _ => rfl, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    obtain ⟨a, _, _, _⟩ := hn t
    obtain ⟨l1, l2, l3, _⟩ := wave_spec hG (u (t + 1)).1 (u (t + 1)).2.1
      (runState G0 u (lo0, hi0) t).1 a i1
    obtain ⟨u1, u2, u3, _⟩ := wave_spec hG (u (t + 1)).1 (u (t + 1)).2.2
      (runState G0 u (lo0, hi0) t).2 a i2
    obtain ⟨_, _, x3, x4⟩ := rrun_exact h0 hn t
    obtain ⟨y1, y2⟩ := (rrun_inv h0 hn (t + 1)).exact
    refine ⟨l1, u1, ?_, ?_⟩
    · apply exact_unique hG y1 (inv_exact l1)
      intro g hg
      by_cases hgx : g = (u (t + 1)).1
      · rw [hgx] at hg ⊢
        exact ((x3 hg).1).trans (l2 hg).symm
      · exact ((x4 g hg hgx).1).trans ((i3 g).trans (l3 g hg hgx).symm)
    · apply exact_unique hG y2 (inv_exact u1)
      intro g hg
      by_cases hgx : g = (u (t + 1)).1
      · rw [hgx] at hg ⊢
        exact ((x3 hg).2).trans (u2 hg).symm
      · exact ((x4 g hg hgx).2).trans ((i4 g).trans (u3 g hg hgx).symm)

/-- Full-incidence delivery volume of rollout `t + 1` (`S₀`, one rollout). -/
def eagerPlus (G0 : Dag) (u : ℕ → ℕ × α × α) (lo0 hi0 : EState α) (t : ℕ) : ℕ :=
  vol G0 (runState G0 u (lo0, hi0) t).1 (runState G0 u (lo0, hi0) (t + 1)).1
    + vol G0 (runState G0 u (lo0, hi0) t).2 (runState G0 u (lo0, hi0) (t + 1)).2

/-- Cost of the eager waves of rollout `t + 1`. -/
def eagerCost (G0 : Dag) (u : ℕ → ℕ × α × α) (lo0 hi0 : EState α) (t : ℕ) : ℕ :=
  (ivWave G0 (u (t + 1)).1 (u (t + 1)).2.1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t)).2

/-- Live deliveries are at most full-incidence deliveries: `S ≤ S₀`, rollout by rollout. -/
theorem stepPlus_le_eager (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 cand u ⟨G0, lo0, hi0⟩) (t : ℕ) :
    stepPlus cand u ⟨G0, lo0, hi0⟩ t ≤ eagerPlus G0 u lo0 hi0 t := by
  have hI := rrun_inv h0 hn t
  obtain ⟨_, _, a3, a4⟩ := live_eq_eager hG h0 hn t
  obtain ⟨_, _, b3, b4⟩ := live_eq_eager hG h0 hn (t + 1)
  unfold stepPlus eagerPlus
  exact Nat.add_le_add
    ((vol_le_of_sub hI.nEq hI.psub _ _).trans (vol_congr G0 a3 b3).le)
    ((vol_le_of_sub hI.nEq hI.psub _ _).trans (vol_congr G0 a4 b4).le)

/-- **`eq:ram-work-bounds` for general DAGs with retirement of internal incidences.**
Fixed coupled trajectory with `T` rollouts and `Q` root queries over `K = |roots|` root
actions, all gate degrees at most `D`, initialisation work `P` (see `initPass_spec`),
`S₀ = Σ eagerPlus` the full-incidence changed-endpoint deliveries, `S = Σ stepPlus` the
live deliveries of the engine with the delivery retirement policy, and
`R = |F_0| - |F_T|` the incidences retired.  Then:

* both engines hold the same intervals at every gate, so every root query returns the same
  answer in both, at cost `2K`;
* `P + S₀ ≤ W_eager ≤ P + 2T(L + 3) + 2QK + (⌈log₂ D⌉ + 3) S₀`;
* `W_live ≤ P + 2T(L + 3) + 2QK + (⌈log₂ D⌉ + 4) S + (2⌈log₂ D⌉ + 4) R`;
* `S ≤ S₀`.

`W_eager` and `W_live` are the sums of the computed costs of the waves, retirement passes
and queries.  The term `2T(L + 3)` is the level scheduling of the waves, where the
manuscript has `T`. -/
theorem ram_work_bounds_dag (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 delivCand u ⟨G0, lo0, hi0⟩)
    (roots : List ℕ) (T Q P : ℕ) :
    (∀ t, rootQuery roots (rrun delivCand u ⟨G0, lo0, hi0⟩ t).lo
        (rrun delivCand u ⟨G0, lo0, hi0⟩ t).hi
      = rootQuery roots (runState G0 u (lo0, hi0) t).1 (runState G0 u (lo0, hi0) t).2) ∧
    (∀ lo hi : EState α, (rootQuery roots lo hi).2 = 2 * roots.length) ∧
    (P + ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t
      ≤ P + ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t + Q * (2 * roots.length)) ∧
    (P + ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t + Q * (2 * roots.length)
      ≤ P + 2 * T * (G0.L + 3) + Q * (2 * roots.length)
        + (Nat.clog 2 D + 3) * ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t) ∧
    (P + ∑ t ∈ range T, stepCost delivCand u ⟨G0, lo0, hi0⟩ t + Q * (2 * roots.length)
      ≤ P + 2 * T * (G0.L + 3) + Q * (2 * roots.length)
        + (Nat.clog 2 D + 4) * ∑ t ∈ range T, stepPlus delivCand u ⟨G0, lo0, hi0⟩ t
        + (2 * Nat.clog 2 D + 4)
          * (live G0 - live (rrun delivCand u ⟨G0, lo0, hi0⟩ T).G)) ∧
    (∑ t ∈ range T, stepPlus delivCand u ⟨G0, lo0, hi0⟩ t
      ≤ ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t) := by
  have hstep : ∀ t, eagerPlus G0 u lo0 hi0 t ≤ eagerCost G0 u lo0 hi0 t ∧
      eagerCost G0 u lo0 hi0 t
        ≤ 2 * (G0.L + 3) + (Nat.clog 2 D + 3) * eagerPlus G0 u lo0 hi0 t := by
    intro t
    obtain ⟨i1, i2, _, _⟩ := live_eq_eager hG h0 hn t
    obtain ⟨a, _, _, _⟩ := hn t
    obtain ⟨_, _, _, l4⟩ := wave_spec hG (u (t + 1)).1 (u (t + 1)).2.1
      (runState G0 u (lo0, hi0) t).1 a i1
    obtain ⟨_, _, _, u4⟩ := wave_spec hG (u (t + 1)).1 (u (t + 1)).2.2
      (runState G0 u (lo0, hi0) t).2 a i2
    have bl := chgSum_bounds D hD (runState G0 u (lo0, hi0) t).1
      (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
    have bh := chgSum_bounds D hD (runState G0 u (lo0, hi0) t).2
      (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1
    have hc : eagerCost G0 u lo0 hi0 t
        = (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).2
          + (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).2 := rfl
    have hp : eagerPlus G0 u lo0 hi0 t
        = vol G0 (runState G0 u (lo0, hi0) t).1
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
          + vol G0 (runState G0 u (lo0, hi0) t).2
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1 := rfl
    rw [hc, hp, l4, u4]
    constructor
    · omega
    · nlinarith [bl.2, bh.2]
  have hsumL : ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t ≤ ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t :=
    sum_le_sum (fun t _ => (hstep t).1)
  have hsumU : ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t
      ≤ 2 * T * (G0.L + 3) + (Nat.clog 2 D + 3) * ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t := by
    calc ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t
        ≤ ∑ t ∈ range T, (2 * (G0.L + 3) + (Nat.clog 2 D + 3) * eagerPlus G0 u lo0 hi0 t) :=
          sum_le_sum (fun t _ => (hstep t).2)
      _ = 2 * T * (G0.L + 3) + (Nat.clog 2 D + 3) * ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t := by
          rw [sum_add_distrib, sum_const, card_range, ← mul_sum, smul_eq_mul]
          ring
  obtain ⟨r1, _, _, _⟩ := representation_cost_retire D hD h0 hn T P
  refine ⟨?_, fun lo hi => by rw [rootQuery_spec], ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨_, _, e3, e4⟩ := live_eq_eager hG h0 hn t
    rw [rootQuery_spec, rootQuery_spec]
    have f1 : (rrun delivCand u ⟨G0, lo0, hi0⟩ t).lo.val = (runState G0 u (lo0, hi0) t).1.val :=
      funext e3
    have f2 : (rrun delivCand u ⟨G0, lo0, hi0⟩ t).hi.val = (runState G0 u (lo0, hi0) t).2.val :=
      funext e4
    rw [f1, f2]
  · omega
  · omega
  · have : live (⟨G0, lo0, hi0⟩ : RState α).G = live G0 := rfl
    rw [this] at r1
    omega
  · exact sum_le_sum (fun t _ => stepPlus_le_eager hG h0 hn t)

end Eager

/-! ## A costed initialisation pass -/

section Init

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Insert the keys of the children `cs` of gate `g` into the heap of `g` (a heap of `m`
keys): one heap insertion, `⌈log₂ m⌉ + 1` units, per child. -/
def insKeys (m g : ℕ) (v : ℕ → α) : List ℕ → (ℕ → ℕ → α) → (ℕ → ℕ → α) × ℕ
  | [], key => (key, 0)
  | c :: cs, key =>
    ((insKeys m g v cs (fun p c' => if p = g ∧ c' = c then v c else key p c')).1,
     (insKeys m g v cs (fun p c' => if p = g ∧ c' = c then v c else key p c')).2
       + (Nat.clog 2 m + 1))

omit [LinearOrder α] [OrderBot α] in
lemma insKeys_spec (m g : ℕ) (v : ℕ → α) : ∀ (cs : List ℕ) (key : ℕ → ℕ → α),
    (∀ p c', (insKeys m g v cs key).1 p c' = if p = g ∧ c' ∈ cs then v c' else key p c') ∧
    (insKeys m g v cs key).2 = cs.length * (Nat.clog 2 m + 1) := by
  intro cs
  induction cs with
  | nil => intro key; exact ⟨fun p c' => by simp [insKeys], by simp [insKeys]⟩
  | cons c cs ih =>
    intro key
    obtain ⟨h1, h2⟩ := ih (fun p c' => if p = g ∧ c' = c then v c else key p c')
    refine ⟨fun p c' => ?_, ?_⟩
    · show (insKeys m g v cs _).1 p c' = _
      rw [h1 p c']
      by_cases hp : p = g
      · by_cases hm : c' ∈ cs
        · simp [hp, hm]
        · rcases eq_or_ne c' c with rfl | hne
          · simp [hp, hm]
          · simp [hp, hm, hne]
      · simp [hp]
    · show (insKeys m g v cs _).2 + (Nat.clog 2 m + 1) = _
      rw [h2, List.length_cons]
      ring

/-- Initialise one internal gate: insert the keys of its children (the children's stored
values) into its heap, then read the heap root into the gate (1 unit). -/
def initGate (G : Dag) (g : ℕ) (s : EState α) : EState α × ℕ :=
  (⟨fun g' => if g' = g then
        heapMax (G.children g)
          ((insKeys (G.children g).length g s.val (G.children g) s.key).1 g)
      else s.val g',
    (insKeys (G.children g).length g s.val (G.children g) s.key).1⟩,
   (insKeys (G.children g).length g s.val (G.children g) s.key).2 + 1)

/-- **Initialisation pass**: initialise the internal gates in the given order. -/
def initPass (G : Dag) : List ℕ → EState α → EState α × ℕ
  | [], s => (s, 0)
  | g :: rest, s =>
    ((initPass G rest (initGate G g s).1).1,
     (initGate G g s).2 + (initPass G rest (initGate G g s).1).2)

/-- Per-gate cost of initialisation. -/
def initCost (G : Dag) (g : ℕ) : ℕ :=
  1 + (G.children g).length * (Nat.clog 2 (G.children g).length + 1)

lemma initGate_spec (G : Dag) (g : ℕ) (s : EState α) :
    (∀ g', g' ≠ g → (initGate G g s).1.val g' = s.val g') ∧
    (∀ p c, p ≠ g → (initGate G g s).1.key p c = s.key p c) ∧
    (∀ c ∈ G.children g, (initGate G g s).1.key g c = s.val c) ∧
    (initGate G g s).1.val g = heapMax (G.children g) ((initGate G g s).1.key g) ∧
    (initGate G g s).2 = initCost G g := by
  obtain ⟨h1, h2⟩ := insKeys_spec (G.children g).length g s.val (G.children g) s.key
  refine ⟨fun g' hg' => ?_, fun p c hp => ?_, fun c hc => ?_, ?_, ?_⟩
  · show (if g' = g then _ else s.val g') = s.val g'
    rw [ite_eq_right hg']
  · show (insKeys _ g s.val (G.children g) s.key).1 p c = _
    rw [h1 p c, ite_eq_right (fun h => hp h.1)]
  · show (insKeys _ g s.val (G.children g) s.key).1 g c = _
    rw [h1 g c, ite_eq_left ⟨rfl, hc⟩]
  · show (if g = g then _ else s.val g) = _
    rw [ite_eq_left rfl]
    rfl
  · show (insKeys _ g s.val (G.children g) s.key).2 + 1 = _
    rw [h2]
    unfold initCost
    ring

/-- Loop invariant of the initialisation pass with `rest` still to process. -/
structure IPre (G : Dag) (rest : List ℕ) (s : EState α) : Prop where
  done : ∀ h, G.children h ≠ [] → h ∉ rest →
    s.val h = heapMax (G.children h) (s.key h) ∧ ∀ c ∈ G.children h, s.key h c = s.val c
  before : ∀ h, G.children h ≠ [] → h ∉ rest → ∀ g ∈ rest, G.level h ≤ G.level g
  sorted : rest.Pairwise (fun a b => G.level a ≤ G.level b)

lemma IPre.step {G : Dag} (hG : G.WF) {g : ℕ} {rest : List ℕ} {s : EState α}
    (h : IPre G (g :: rest) s) : IPre G rest (initGate G g s).1 := by
  obtain ⟨s1, s2, s3, s4, _⟩ := initGate_spec G g s
  have hsort := List.pairwise_cons.1 h.sorted
  refine ⟨?_, ?_, hsort.2⟩
  · intro h' hint hnot
    by_cases e : h' = g
    · subst e
      refine ⟨s4, fun c hc => ?_⟩
      have hne : c ≠ h' := fun e => by
        have := hG.level_lt h' c hc
        rw [e] at this
        exact lt_irrefl _ this
      rw [s3 c hc, s1 c hne]
    · have hnot' : h' ∉ g :: rest := fun hm => by
        rcases List.mem_cons.1 hm with hm | hm
        · exact e hm
        · exact hnot hm
      obtain ⟨d1, d2⟩ := h.done h' hint hnot'
      have hlev := h.before h' hint hnot' g List.mem_cons_self
      have hcne : ∀ c ∈ G.children h', c ≠ g := fun c hc e' => by
        have := hG.level_lt h' c hc
        rw [e'] at this
        omega
      refine ⟨?_, fun c hc => ?_⟩
      · rw [s1 h' e, d1]
        exact heapMax_congr (fun c _ => (s2 h' c e).symm)
      · rw [s2 h' c e, d2 c hc, s1 c (hcne c hc)]
  · intro h' hint hnot g' hg'
    by_cases e : h' = g
    · subst e
      exact hsort.1 g' hg'
    · have hnot' : h' ∉ g :: rest := fun hm => by
        rcases List.mem_cons.1 hm with hm | hm
        · exact e hm
        · exact hnot hm
      exact h.before h' hint hnot' g' (List.mem_cons_of_mem _ hg')

lemma initPass_loop {G : Dag} (hG : G.WF) : ∀ (rest : List ℕ) (s : EState α), IPre G rest s →
    IPre G [] (initPass G rest s).1 ∧
    (∀ g, g ∉ rest → (initPass G rest s).1.val g = s.val g) ∧
    (initPass G rest s).2 = (rest.map (initCost G)).sum := by
  intro rest
  induction rest with
  | nil => intro s h; exact ⟨h, fun _ _ => rfl, rfl⟩
  | cons g rest ih =>
    intro s h
    obtain ⟨h1, h2, h3⟩ := ih _ (h.step hG)
    obtain ⟨s1, _, _, _, s5⟩ := initGate_spec G g s
    refine ⟨h1, fun g' hg' => ?_, ?_⟩
    · have hne : g' ≠ g := fun e => hg' (e ▸ List.mem_cons_self)
      have hnr : g' ∉ rest := fun hm => hg' (List.mem_cons_of_mem _ hm)
      show (initPass G rest (initGate G g s).1).1.val g' = _
      rw [h2 g' hnr, s1 g' hne]
    · show (initGate G g s).2 + (initPass G rest (initGate G g s).1).2 = _
      rw [h3, s5, List.map_cons, List.sum_cons]

/-- **Correctness and exact cost of the initialisation pass** (one endpoint).  Let `order`
list the internal gates by nondecreasing level.  Starting from any state whose leaf values
are the terminal values, the pass produces a state satisfying the engine invariant with
the same leaf values, at cost exactly `Σ_{g ∈ order} (1 + deg g (⌈log₂ deg g⌉ + 1))`:
one heap insertion per incidence and one read per internal gate. -/
theorem initPass_spec {G : Dag} (hG : G.WF) (order : List ℕ) (s : EState α)
    (hall : ∀ g, G.children g ≠ [] → g ∈ order) (hint : ∀ g ∈ order, G.children g ≠ [])
    (hsorted : order.Pairwise (fun a b => G.level a ≤ G.level b)) :
    Inv G (initPass G order s).1 ∧
    (∀ g, G.children g = [] → (initPass G order s).1.val g = s.val g) ∧
    (initPass G order s).2 = (order.map (initCost G)).sum := by
  have hpre : IPre G order s :=
    ⟨fun h hh hn => absurd (hall h hh) hn, fun h hh hn => absurd (hall h hh) hn, hsorted⟩
  obtain ⟨h1, h2, h3⟩ := initPass_loop hG order s hpre
  refine ⟨⟨fun g hg => (h1.done g hg List.not_mem_nil).1,
    fun p c hc => (h1.done p (List.ne_nil_of_mem hc) List.not_mem_nil).2 c hc⟩, ?_, h3⟩
  intro g hg
  exact h2 g (fun hm => hint g hm hg)

/-- The initialisation cost is at most `n_int + (⌈log₂ D⌉ + 1) · e`, with `n_int` the number
of internal gates and `e` the number of incidences. -/
lemma initCost_sum_le (G : Dag) (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D)
    (order : List ℕ) :
    (order.map (initCost G)).sum
      ≤ order.length + (Nat.clog 2 D + 1) * (order.map (fun g => (G.children g).length)).sum := by
  induction order with
  | nil => simp
  | cons g rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : (G.children g).length * (Nat.clog 2 (G.children g).length + 1)
        ≤ (Nat.clog 2 D + 1) * (G.children g).length := by
      rw [mul_comm]
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.clog_mono_right 2 (hD g)) 1)
    have e : initCost G g
        = 1 + (G.children g).length * (Nat.clog 2 (G.children g).length + 1) := rfl
    have hk := Nat.mul_add (Nat.clog 2 D + 1) (G.children g).length
      (rest.map (fun g => (G.children g).length)).sum
    rw [e]
    omega

/-- **Initialised engine.**  Initialising both endpoints from terminal intervals with
`l ≤ u` gives a state satisfying the invariant of the engine with retirement (all
incidences live), at cost `2 Σ_{g ∈ order} initCost g`. -/
theorem init_engine {G : Dag} (hG : G.WF) (order : List ℕ) (sl su : EState α)
    (hall : ∀ g, G.children g ≠ [] → g ∈ order) (hint : ∀ g ∈ order, G.children g ≠ [])
    (hsorted : order.Pairwise (fun a b => G.level a ≤ G.level b))
    (hleaf : ∀ g, G.children g = [] → sl.val g ≤ su.val g) :
    RInv G ⟨G, (initPass G order sl).1, (initPass G order su).1⟩ ∧
    (initPass G order sl).2 + (initPass G order su).2 = 2 * (order.map (initCost G)).sum := by
  obtain ⟨a1, a2, a3⟩ := initPass_spec hG order sl hall hint hsorted
  obtain ⟨b1, b2, b3⟩ := initPass_spec hG order su hall hint hsorted
  refine ⟨RInv.init hG a1 b1 (fun g hg => ?_), by rw [a3, b3]; ring⟩
  rw [a2 g hg, b2 g hg]
  exact hleaf g hg

end Init

/-! ## The lower bound `Ω(P + S⁻)` for every implementation under a delivery contract -/

section Contract

variable {α : Type*} [DecidableEq α] {C : Type*} [DecidableEq C]

/-- A scalar operation writes at most one memory cell: `some (c, x)` writes `x` to cell
`c`, `none` writes no cell.  A program trace is a list of operations. -/
def applyOps : List (Option (C × α)) → (C → α) → (C → α)
  | [], m => m
  | none :: ops, m => applyOps ops m
  | some w :: ops, m => applyOps ops (Function.update m w.1 w.2)

/-- A trace of `k` operations changes at most `k` cells. -/
lemma changed_le_length (S : Finset C) : ∀ (ops : List (Option (C × α))) (m : C → α),
    (S.filter (fun c => applyOps ops m c ≠ m c)).card ≤ ops.length := by
  intro ops
  induction ops with
  | nil => intro m; simp [applyOps]
  | cons o ops ih =>
    intro m
    cases o with
    | none => exact (ih m).trans (Nat.le_succ _)
    | some w =>
      have hsub : S.filter (fun c => applyOps (some w :: ops) m c ≠ m c)
          ⊆ insert w.1 (S.filter (fun c =>
              applyOps ops (Function.update m w.1 w.2) c ≠ Function.update m w.1 w.2 c)) := by
        intro c hc
        rw [mem_filter] at hc
        rw [mem_insert]
        by_cases e : c = w.1
        · exact Or.inl e
        · right
          rw [mem_filter, Function.update_of_ne e]
          exact hc
      calc _ ≤ (insert w.1 (S.filter (fun c =>
              applyOps ops (Function.update m w.1 w.2) c ≠ Function.update m w.1 w.2 c))).card :=
            card_le_card hsub
        _ ≤ _ + 1 := card_insert_le _ _
        _ ≤ ops.length + 1 := Nat.succ_le_succ (ih _)

/-- **`prop:representation-cost`, lower bound `Ω(P_C + S_C^-)` for every implementation
satisfying the incidence-delivery contract.**

The contract.  An implementation keeps, for every incidence `e = (p, c)` and endpoint
`b ∈ {lower, upper}`, a memory cell `(b, e)` (the key of `c` in the indexed heap of `p`).
Its execution of wave `t` is a trace `ops t` of scalar operations, each writing at most one
cell (`applyOps`); `m t` is the memory after wave `t`.  `F t` is the set of incidences live
after wave `t` (only retirement: `F t ⊆ F (t - 1)`), and `lo t`, `hi t` are the exact gate
endpoints after wave `t`.  The contract requires that at the conclusion of every wave the
key cell of every live incidence holds the exact endpoint of its child
(`hcontract`): "every changed endpoint of `v` must be delivered to every parent incidence
that remains live in `F_t`".

Conclusion: the number of operations of wave `t` is at least
`Σ_{e ∈ F_t} b_t(child e) = Σ_v b_t(v) d⁻_{F_t}(v)`, where `b_t(v) ∈ {0, 1, 2}` counts the
changed endpoints of `v` (`Representation.deliveryVolume_eq_sum`).  Hence a total work
consisting of `P` upfront operations and the wave traces is at least `P + S⁻`.  Nothing is
assumed about how the implementation schedules, shares or retires. -/
theorem contract_lower (τ : ℕ) (F : ℕ → Finset (ℕ × ℕ)) (lo hi : ℕ → ℕ → α)
    (m : ℕ → Bool × (ℕ × ℕ) → α) (ops : ℕ → List (Option ((Bool × (ℕ × ℕ)) × α))) (P : ℕ)
    (hF : ∀ t ∈ Icc 1 τ, F t ⊆ F (t - 1))
    (hrun : ∀ t ∈ Icc 1 τ, m t = applyOps (ops t) (m (t - 1)))
    (hcontract : ∀ t ≤ τ, ∀ e ∈ F t, m t (false, e) = lo t e.2 ∧ m t (true, e) = hi t e.2) :
    P + ∑ t ∈ Icc 1 τ, ∑ e ∈ F t,
        ((if lo t e.2 ≠ lo (t - 1) e.2 then 1 else 0)
          + (if hi t e.2 ≠ hi (t - 1) e.2 then 1 else 0))
      ≤ P + ∑ t ∈ Icc 1 τ, (ops t).length := by
  apply Nat.add_le_add_left
  apply sum_le_sum
  intro t ht
  have ht1 : 1 ≤ t ∧ t ≤ τ := mem_Icc.1 ht
  have hlen := changed_le_length ((univ : Finset Bool) ×ˢ F t) (ops t) (m (t - 1))
  rw [← hrun t ht] at hlen
  refine le_trans ?_ hlen
  rw [card_filter, sum_product, Fintype.sum_bool, ← sum_add_distrib]
  apply sum_le_sum
  intro e he
  have c1 := hcontract t ht1.2 e he
  have c0 := hcontract (t - 1) (by omega) e (hF t ht he)
  rw [add_comm]
  apply Nat.add_le_add
  · by_cases hch : hi t e.2 ≠ hi (t - 1) e.2
    · have : m t (true, e) ≠ m (t - 1) (true, e) := by rw [c1.2, c0.2]; exact hch
      simp [hch, this]
    · simp [hch]
  · by_cases hch : lo t e.2 ≠ lo (t - 1) e.2
    · have : m t (false, e) ≠ m (t - 1) (false, e) := by rw [c1.1, c0.1]; exact hch
      simp [hch, this]
    · simp [hch]

end Contract

end DagRetire
end JointRootCert
