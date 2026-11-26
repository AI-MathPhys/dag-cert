/-
Joint Root Certification: costed engines for max-circuit maintenance.

Manuscript: Part III, section "Efficient Algorithms and Certified Numerical Methods",
subsection `app:representation`.  Results covered:

* `prop:representation-cost` (Unified Full-Cost Representation Comparison): an
  indexed-heap max-circuit engine on a DAG with explicit vertex and incidence lists, the
  exact operation count of each backup wave, and the resulting instances of
  `Representation.work_upper` and `Representation.work_lower`.
* `prop:unrestricted-compiler` (Equivalence Under Unrestricted Circuit Retention): the
  `O(|V| + |E|)` copy cost of a retained circuit.
* `thm:coded-main` / `thm:coded-covers`, Step 3: the per-wave work of the engine on DAGs of
  parity-grid shape and the resulting `O(r² log² r)` work bound given the stopping-time
  bound (see the last section for what is assumed).

## Cost model and its correspondence with the unit-cost RAM

As in `CostModel.lean`: a costed program returns `(result, cost)`, the cost is computed by
the recursion that computes the result, and the cost of a composite program is the sum of
the costs of its parts.  One unit stands for a bounded number of unit-cost RAM operations.
The charges of the engine are:

* scanning one level bucket of the wave agenda: 1 unit per level;
* popping one gate from a bucket (read the root of its indexed heap, compare with the
  stored value): 1 unit;
* one reverse-incidence delivery from a changed gate `g` to a parent `p`: one indexed-heap
  key update in the heap of `p`, charged `⌈log₂ deg(p)⌉ + 1` units, plus 1 unit for pushing
  `p` on the bucket of its level;
* copying one vertex record or one incidence: 1 unit.

Indexed heaps are a PRIMITIVE of the model: the heap of gate `p` is represented by the keys
it stores (`key p c` for each child `c`), and its maximum (`heapMax`) is read in one unit.
The sift procedure is not implemented; `⌈log₂ m⌉ + 1` per key update is the modelling
assumption.  The heap contents are part of the state: a gate value is always read from the
gate's own heap, never recomputed from the children, so an omitted delivery would make the
engine incorrect.

Scheduling.  For each gate value to change at most once per wave, a gate must be
recomputed only after all its changed children have delivered.  The engine therefore
processes the agenda by topological level, using one bucket per level.  This costs
`L + 3` units per wave on top of the deliveries, where `L` is the largest level.  In
`prop:representation-cost` this term belongs to the shared work `H` (a rollout traverses a
root-to-terminal path, so `H` already contains a term proportional to the depth per
rollout); it is stated explicitly in the theorems below.

Not modelled: online retirement of dominated incidences (the engine keeps all incidences
live, so `F_t` is constant and `S⁺ = S⁻`), and a dedicated heap-construction pass (the
initial state is assumed to satisfy the invariant and its construction cost is the
parameter `P`; the all-`⊥` state satisfies it by `Inv.bot`, and initial terminal values can
be installed from there by waves).  The TA-UCT allocator and the reward model of
`thm:coded-covers` are not modelled: Step 3 is proved from a root-level selection rule, a
stopping hypothesis and a per-rollout cost bound (see `parity_total_work`).
-/
import JointRootCert.Representation
import JointRootCert.PassiveRetirement

namespace JointRootCert
namespace CostEngines

open Finset _root_.JointRootCert.Representation

/-! ## DAG circuits with explicit incidence lists -/

/-- A max-circuit DAG with gates `0, …, N-1`: child lists, reverse-incidence (parent)
lists, and a topological level for each gate (at most `L`). -/
structure Dag where
  N : ℕ
  children : ℕ → List ℕ
  parents : ℕ → List ℕ
  level : ℕ → ℕ
  L : ℕ

/-- Well-formedness: the parent lists are the reverse of the child lists, without
repetition; parents are gates; levels increase strictly from child to parent and are at
most `L`. -/
structure Dag.WF (G : Dag) : Prop where
  parents_iff : ∀ c p, p ∈ G.parents c ↔ c ∈ G.children p
  parents_nodup : ∀ c, (G.parents c).Nodup
  parent_lt : ∀ c p, p ∈ G.parents c → p < G.N
  level_lt : ∀ p c, c ∈ G.children p → G.level c < G.level p
  level_le : ∀ g, G.level g ≤ G.L

section Engine

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Engine state for one endpoint: the stored value of every gate and the keys of every
gate's indexed heap (`key p c` is the key of child `c` in the heap of `p`). -/
structure EState (α : Type*) where
  val : ℕ → α
  key : ℕ → ℕ → α

/-- Maximum of the indexed heap of a gate with child list `cs` and keys `k`. -/
def heapMax (cs : List ℕ) (k : ℕ → α) : α := (cs.map k).foldr (· ⊔ ·) ⊥

lemma heapMax_congr {cs : List ℕ} {k k' : ℕ → α}
    (h : ∀ c ∈ cs, k c = k' c) : heapMax cs k = heapMax cs k' := by
  unfold heapMax
  rw [List.map_congr_left h]

/-- Invariant of the engine: every non-leaf gate stores the maximum of its heap, and every
heap key equals the stored value of the corresponding child.  Hence the stored values are
the exact evaluation of the circuit on the leaf values. -/
structure Inv (G : Dag) (s : EState α) : Prop where
  gate : ∀ g, G.children g ≠ [] → s.val g = heapMax (G.children g) (s.key g)
  keys : ∀ p c, c ∈ G.children p → s.key p c = s.val c

/-- The value a gate should store: for the updated leaf `x` the new terminal value `y`,
for any other leaf its stored value, for an internal gate the maximum of its heap. -/
def target (G : Dag) (x : ℕ) (y : α) (s : EState α) (g : ℕ) : α :=
  if G.children g = [] then (if g = x then y else s.val g) else heapMax (G.children g) (s.key g)

/-- **Deliveries from a changed gate.**  For each parent `p` of `g`: update the key of `g`
in the heap of `p` (`⌈log₂ deg p⌉ + 1` units) and push `p` on the bucket of its level
(1 unit). -/
def push (G : Dag) (g : ℕ) (y : α) :
    List ℕ → (ℕ → ℕ → α) → (ℕ → List ℕ) → (ℕ → ℕ → α) × (ℕ → List ℕ) × ℕ
  | [], key, bk => (key, bk, 0)
  | p :: ps, key, bk =>
    ((push G g y ps (fun p' c' => if p' = p ∧ c' = g then y else key p' c')
        (fun l => if l = G.level p then p :: bk l else bk l)).1,
     (push G g y ps (fun p' c' => if p' = p ∧ c' = g then y else key p' c')
        (fun l => if l = G.level p then p :: bk l else bk l)).2.1,
     (push G g y ps (fun p' c' => if p' = p ∧ c' = g then y else key p' c')
        (fun l => if l = G.level p then p :: bk l else bk l)).2.2
       + (Nat.clog 2 (G.children p).length + 2))

omit [LinearOrder α] [OrderBot α] in
lemma push_key (G : Dag) (g : ℕ) (y : α) :
    ∀ (ps : List ℕ) (key : ℕ → ℕ → α) (bk : ℕ → List ℕ) (p' c' : ℕ),
      (push G g y ps key bk).1 p' c' = if p' ∈ ps ∧ c' = g then y else key p' c' := by
  intro ps
  induction ps with
  | nil => intro key bk p' c'; simp [push]
  | cons p ps ih =>
    intro key bk p' c'
    simp only [push, ih, List.mem_cons]
    by_cases h1 : p' ∈ ps ∧ c' = g
    · rw [ite_eq_left h1, ite_eq_left ⟨Or.inr h1.1, h1.2⟩]
    · by_cases h2 : p' = p ∧ c' = g
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left ⟨Or.inl h2.1, h2.2⟩]
      · have h3 : ¬ ((p' = p ∨ p' ∈ ps) ∧ c' = g) := by tauto
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

omit [LinearOrder α] [OrderBot α] in
lemma push_cost (G : Dag) (g : ℕ) (y : α) :
    ∀ (ps : List ℕ) (key : ℕ → ℕ → α) (bk : ℕ → List ℕ),
      (push G g y ps key bk).2.2
        = (ps.map (fun p => Nat.clog 2 (G.children p).length + 2)).sum := by
  intro ps
  induction ps with
  | nil => intro key bk; rfl
  | cons p ps ih =>
    intro key bk
    simp only [push, ih, List.map_cons, List.sum_cons]
    omega

omit [LinearOrder α] [OrderBot α] in
lemma push_mem (G : Dag) (g : ℕ) (y : α) :
    ∀ (ps : List ℕ) (key : ℕ → ℕ → α) (bk : ℕ → List ℕ) (h l : ℕ),
      h ∈ (push G g y ps key bk).2.1 l ↔ h ∈ bk l ∨ (h ∈ ps ∧ G.level h = l) := by
  intro ps
  induction ps with
  | nil => intro key bk h l; simp [push]
  | cons p ps ih =>
    intro key bk h l
    simp only [push, ih, List.mem_cons]
    by_cases hl : l = G.level p
    · subst hl
      rw [ite_eq_left rfl, List.mem_cons]
      constructor
      · rintro ((rfl | h1) | h1)
        · exact Or.inr ⟨Or.inl rfl, rfl⟩
        · exact Or.inl h1
        · exact Or.inr ⟨Or.inr h1.1, h1.2⟩
      · rintro (h1 | ⟨rfl | h1, h2⟩)
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨h1, h2⟩
    · rw [ite_eq_right hl]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr ⟨Or.inr h1.1, h1.2⟩
      · rintro (h1 | ⟨rfl | h1, h2⟩)
        · exact Or.inl h1
        · exact absurd h2.symm hl
        · exact Or.inr ⟨h1, h2⟩

omit [LinearOrder α] [OrderBot α] in
lemma push_len (G : Dag) (g : ℕ) (y : α) (I : Finset ℕ) :
    ∀ (ps : List ℕ) (key : ℕ → ℕ → α) (bk : ℕ → List ℕ), (∀ p ∈ ps, G.level p ∈ I) →
      ∑ l ∈ I, ((push G g y ps key bk).2.1 l).length
        = ∑ l ∈ I, (bk l).length + ps.length := by
  intro ps
  induction ps with
  | nil => intro key bk _; simp [push]
  | cons p ps ih =>
    intro key bk hI
    have hp : G.level p ∈ I := hI p (List.mem_cons.2 (Or.inl rfl))
    simp only [push]
    rw [ih _ _ (fun q hq => hI q (List.mem_cons_of_mem _ hq))]
    have hlen : ∀ l, (if l = G.level p then p :: bk l else bk l).length
        = (bk l).length + (if l = G.level p then 1 else 0) := by
      intro l
      split_ifs <;> simp
    simp only [hlen, sum_add_distrib, sum_ite_eq', hp, ite_true, List.length_cons]
    omega

/-- Stored values after gate `g` takes its target value. -/
def stepVal (G : Dag) (x : ℕ) (y : α) (s : EState α) (g : ℕ) : ℕ → α :=
  fun g' => if g' = g then target G x y s g else s.val g'

/-- **Processing one bucket.**  Pop each gate of the list (1 unit): read the maximum of its
heap; if it differs from the stored value, store it and deliver it to all parents. -/
def procList (G : Dag) (x : ℕ) (y : α) :
    List ℕ → EState α → (ℕ → List ℕ) → EState α × (ℕ → List ℕ) × ℕ
  | [], s, bk => (s, bk, 0)
  | g :: rest, s, bk =>
    if target G x y s g = s.val g then
      ((procList G x y rest s bk).1, (procList G x y rest s bk).2.1,
        (procList G x y rest s bk).2.2 + 1)
    else
      ((procList G x y rest
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
          (push G g (target G x y s g) (G.parents g) s.key bk).2.1).1,
       (procList G x y rest
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
          (push G g (target G x y s g) (G.parents g) s.key bk).2.1).2.1,
       (procList G x y rest
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
          (push G g (target G x y s g) (G.parents g) s.key bk).2.1).2.2
        + 1 + (push G g (target G x y s g) (G.parents g) s.key bk).2.2)

/-- **Level sweep.**  `waveLevels G x y ℓ` processes the buckets of levels `0, …, ℓ-1` in
increasing order; scanning a level costs 1 unit. -/
def waveLevels (G : Dag) (x : ℕ) (y : α) :
    ℕ → EState α → (ℕ → List ℕ) → EState α × (ℕ → List ℕ) × ℕ
  | 0, s, bk => (s, bk, 0)
  | l + 1, s, bk =>
    ((procList G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
        (waveLevels G x y l s bk).2.1).1,
     (procList G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
        (waveLevels G x y l s bk).2.1).2.1,
     (waveLevels G x y l s bk).2.2 + 1
      + (procList G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
          (waveLevels G x y l s bk).2.1).2.2)

/-- **One backup wave**: terminal `x` receives the value `y`.  Push `x` on the bucket of its
level (1 unit), then sweep all levels. -/
def wave (G : Dag) (x : ℕ) (y : α) (s : EState α) : EState α × ℕ :=
  ((waveLevels G x y (G.L + 1) s (fun l => if l = G.level x then [x] else [])).1,
   (waveLevels G x y (G.L + 1) s (fun l => if l = G.level x then [x] else [])).2.2 + 1)

/-- Cost charged to a changed gate `g`: for each parent `p`, one heap update
(`⌈log₂ deg p⌉ + 1`), one bucket push and one later pop. -/
def dcost (G : Dag) (g : ℕ) : ℕ :=
  ((G.parents g).map (fun p => Nat.clog 2 (G.children p).length + 3)).sum

/-- Total delivery cost of the gates whose stored value differs between `s0` and `s`. -/
def chgSum (G : Dag) (s0 s : EState α) : ℕ :=
  ∑ g ∈ (range G.N).filter (fun g => s.val g ≠ s0.val g), dcost G g

/-- Pending agenda entries at levels `a, …, L`. -/
def pendSum (G : Dag) (a : ℕ) (bk : ℕ → List ℕ) : ℕ :=
  ∑ l ∈ Ico a (G.L + 1), (bk l).length

/-- Loop invariant while processing level `ℓ` with `rest` still to pop. -/
structure PInv (G : Dag) (x : ℕ) (y : α) (s0 : EState α) (ℓ : ℕ) (rest : List ℕ)
    (s : EState α) (bk : ℕ → List ℕ) : Prop where
  keys : ∀ p c, c ∈ G.children p → s.key p c = s.val c
  pend : ∀ g, s.val g = target G x y s g ∨ (G.level g = ℓ ∧ g ∈ rest) ∨
    (ℓ < G.level g ∧ g ∈ bk (G.level g))
  chg : ∀ g, s.val g ≠ s0.val g → G.level g ≤ ℓ ∧ s.val g = target G x y s g ∧ g < G.N
  leaf : ∀ g, G.children g = [] → g ≠ x → s.val g = s0.val g
  bkt : ∀ l, ∀ g ∈ bk l, G.level g = l ∧ g < G.N
  rst : ∀ g ∈ rest, G.level g = ℓ ∧ g < G.N

variable {G : Dag} {x : ℕ} {y : α} {s0 s : EState α} {ℓ g : ℕ} {rest : List ℕ}
  {bk : ℕ → List ℕ}

lemma PInv.step_same (h : PInv G x y s0 ℓ (g :: rest) s bk)
    (heq : target G x y s g = s.val g) : PInv G x y s0 ℓ rest s bk where
  keys := h.keys
  pend := by
    intro g'
    rcases h.pend g' with h1 | ⟨h1, h2⟩ | h1
    · exact Or.inl h1
    · rcases List.mem_cons.1 h2 with rfl | h2
      · exact Or.inl heq.symm
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr h1)
  chg := h.chg
  leaf := h.leaf
  bkt := h.bkt
  rst := fun g' hg' => h.rst g' (List.mem_cons_of_mem _ hg')

lemma target_step_of_not_parent (s : EState α) (bk : ℕ → List ℕ) (g h : ℕ) (hne : h ≠ g)
    (hnp : h ∉ G.parents g) :
    target G x y
      ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩ h
      = target G x y s h := by
  unfold target
  by_cases hl : G.children h = []
  · rw [ite_eq_left hl, ite_eq_left hl]
    by_cases hx : h = x
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx]
      show stepVal G x y s g h = s.val h
      unfold stepVal
      exact ite_eq_right hne
  · rw [ite_eq_right hl, ite_eq_right hl]
    apply heapMax_congr
    intro c _
    show (push G g (target G x y s g) (G.parents g) s.key bk).1 h c = s.key h c
    rw [push_key]
    exact ite_eq_right (fun h' => hnp h'.1)

lemma target_step_self (s : EState α) (bk : ℕ → List ℕ) (g : ℕ) (hgg : g ∉ G.parents g) :
    target G x y
      ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩ g
      = target G x y s g := by
  by_cases hl : G.children g = []
  · by_cases hx : g = x
    · unfold target
      rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left hx, ite_eq_left hx]
    · have e : target G x y
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩ g
          = stepVal G x y s g g := by
        unfold target
        rw [ite_eq_left hl, ite_eq_right hx]
      rw [e]
      unfold stepVal
      exact ite_eq_left rfl
  · unfold target
    rw [ite_eq_right hl, ite_eq_right hl]
    apply heapMax_congr
    intro c _
    show (push G g _ (G.parents g) s.key bk).1 g c = s.key g c
    rw [push_key]
    exact ite_eq_right (fun h' => hgg h'.1)

lemma PInv.step_change (hG : G.WF) (h : PInv G x y s0 ℓ (g :: rest) s bk)
    (hne : target G x y s g ≠ s.val g) :
    PInv G x y s0 ℓ rest
      ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
      (push G g (target G x y s g) (G.parents g) s.key bk).2.1 := by
  have hgl : G.level g = ℓ ∧ g < G.N := h.rst g (List.mem_cons.2 (Or.inl rfl))
  have hgg : g ∉ G.parents g := fun hp => by
    have := hG.level_lt g g ((hG.parents_iff g g).1 hp)
    omega
  have hval : ∀ h', h' ≠ g → stepVal G x y s g h' = s.val h' := fun h' hh => by
    unfold stepVal
    exact ite_eq_right hh
  have hvalg : stepVal G x y s g g = target G x y s g := by
    unfold stepVal
    exact ite_eq_left rfl
  have hlev : ∀ h', h' ∈ G.parents g → ℓ < G.level h' := fun h' hp => by
    have := hG.level_lt h' g ((hG.parents_iff g h').1 hp)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p c hc
    show (push G g (target G x y s g) (G.parents g) s.key bk).1 p c = stepVal G x y s g c
    rw [push_key]
    by_cases hcg : c = g
    · subst hcg
      rw [ite_eq_left ⟨(hG.parents_iff c p).2 hc, rfl⟩, hvalg]
    · rw [ite_eq_right (fun h' => hcg h'.2), hval c hcg]
      exact h.keys p c hc
  · intro h'
    by_cases hh : h' = g
    · subst hh
      left
      show stepVal G x y s h' h' = _
      rw [hvalg, target_step_self s bk h' hgg]
    by_cases hp : h' ∈ G.parents g
    · exact Or.inr (Or.inr ⟨hlev h' hp, (push_mem G g _ _ _ _ h' _).2 (Or.inr ⟨hp, rfl⟩)⟩)
    rcases h.pend h' with h1 | ⟨h1, h2⟩ | h1
    · left
      show stepVal G x y s g h' = _
      rw [hval h' hh, target_step_of_not_parent s bk g h' hh hp]
      exact h1
    · rcases List.mem_cons.1 h2 with h2 | h2
      · exact absurd h2 hh
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1.1, (push_mem G g _ _ _ _ h' _).2 (Or.inl h1.2)⟩)
  · intro h' hch
    by_cases hh : h' = g
    · subst hh
      refine ⟨hgl.1.le, ?_, hgl.2⟩
      show stepVal G x y s h' h' = _
      rw [hvalg, target_step_self s bk h' hgg]
    · change stepVal G x y s g h' ≠ s0.val h' at hch
      rw [hval h' hh] at hch
      obtain ⟨h1, h2, h3⟩ := h.chg h' hch
      have hnp : h' ∉ G.parents g := fun hp => by
        have := hlev h' hp
        omega
      refine ⟨h1, ?_, h3⟩
      show stepVal G x y s g h' = _
      rw [hval h' hh, target_step_of_not_parent s bk g h' hh hnp]
      exact h2
  · intro h' hl hx
    by_cases hh : h' = g
    · subst hh
      exfalso
      apply hne
      unfold target
      rw [ite_eq_left hl, ite_eq_right hx]
    · show stepVal G x y s g h' = s0.val h'
      rw [hval h' hh]
      exact h.leaf h' hl hx
  · intro l h' hm
    rcases (push_mem G g _ _ _ _ h' l).1 hm with h1 | ⟨h1, h2⟩
    · exact h.bkt l h' h1
    · exact ⟨h2, hG.parent_lt g h' h1⟩
  · exact fun g' hg' => h.rst g' (List.mem_cons_of_mem _ hg')

omit [OrderBot α] in
lemma chgSum_step (hgN : g < G.N) (hs0 : s.val g = s0.val g) (v : ℕ → α) (k : ℕ → ℕ → α)
    (hv : ∀ h', h' ≠ g → v h' = s.val h') (hvg : v g ≠ s.val g) :
    chgSum G s0 ⟨v, k⟩ = chgSum G s0 s + dcost G g := by
  have hfil : (range G.N).filter (fun h' => v h' ≠ s0.val h')
      = insert g ((range G.N).filter (fun h' => s.val h' ≠ s0.val h')) := by
    ext h'
    simp only [mem_filter, mem_range, mem_insert]
    by_cases hh : h' = g
    · subst hh
      constructor
      · exact fun _ => Or.inl rfl
      · exact fun _ => ⟨hgN, by rw [← hs0]; exact hvg⟩
    · rw [hv h' hh]
      constructor
      · exact fun h1 => Or.inr h1
      · rintro (h1 | h1)
        · exact absurd h1 hh
        · exact h1
  have hnot : g ∉ (range G.N).filter (fun h' => s.val h' ≠ s0.val h') := by
    intro hm
    exact (mem_filter.1 hm).2 hs0
  change ∑ g' ∈ (range G.N).filter (fun h' => v h' ≠ s0.val h'), dcost G g' = _
  rw [hfil, sum_insert hnot, add_comm]
  rfl

lemma dcost_eq (G : Dag) (g : ℕ) :
    dcost G g = ((G.parents g).map (fun p => Nat.clog 2 (G.children p).length + 2)).sum
      + (G.parents g).length := by
  unfold dcost
  induction G.parents g with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

lemma procList_same (rest : List ℕ) (heq : target G x y s g = s.val g) :
    procList G x y (g :: rest) s bk
      = ((procList G x y rest s bk).1, (procList G x y rest s bk).2.1,
          (procList G x y rest s bk).2.2 + 1) := by
  rw [procList]
  exact ite_eq_left heq

lemma procList_change (rest : List ℕ) (hne : target G x y s g ≠ s.val g) :
    procList G x y (g :: rest) s bk
      = ((procList G x y rest
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
          (push G g (target G x y s g) (G.parents g) s.key bk).2.1).1,
       (procList G x y rest
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
          (push G g (target G x y s g) (G.parents g) s.key bk).2.1).2.1,
       (procList G x y rest
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
          (push G g (target G x y s g) (G.parents g) s.key bk).2.1).2.2
        + 1 + (push G g (target G x y s g) (G.parents g) s.key bk).2.2) := by
  rw [procList]
  exact ite_eq_right hne

/-- **One bucket: invariant and exact operation count.**  Processing the remaining list
`rest` of level `ℓ` preserves the invariant, and its cost, plus the agenda entries it
creates at higher levels, equals the number of pops plus the delivery cost of the gates
that changed. -/
theorem procList_spec (hG : G.WF) (s0 : EState α) (ℓ : ℕ) :
    ∀ (rest : List ℕ) (s : EState α) (bk : ℕ → List ℕ), PInv G x y s0 ℓ rest s bk →
      PInv G x y s0 ℓ [] (procList G x y rest s bk).1 (procList G x y rest s bk).2.1 ∧
      (procList G x y rest s bk).2.2 + pendSum G (ℓ + 1) (procList G x y rest s bk).2.1
          + chgSum G s0 s
        = rest.length + pendSum G (ℓ + 1) bk + chgSum G s0 (procList G x y rest s bk).1 := by
  intro rest
  induction rest with
  | nil =>
    intro s bk h
    refine ⟨h, ?_⟩
    simp [procList]
  | cons g rest ih =>
    intro s bk h
    by_cases heq : target G x y s g = s.val g
    · rw [procList_same rest heq]
      obtain ⟨h1, h2⟩ := ih s bk (h.step_same heq)
      refine ⟨h1, ?_⟩
      simp only [List.length_cons]
      omega
    · rw [procList_change rest heq]
      obtain ⟨h1, h2⟩ := ih _ _ (h.step_change hG heq)
      have hgl : G.level g = ℓ ∧ g < G.N := h.rst g (List.mem_cons.2 (Or.inl rfl))
      have hs0 : s.val g = s0.val g := by
        by_contra hc
        exact heq (h.chg g hc).2.1.symm
      have e1 := chgSum_step (G := G) (s0 := s0) (s := s) hgl.2 hs0 (stepVal G x y s g)
        (push G g (target G x y s g) (G.parents g) s.key bk).1
        (fun h' hh => by unfold stepVal; exact ite_eq_right hh)
        (by unfold stepVal; rw [ite_eq_left rfl]; exact heq)
      have e2 : pendSum G (ℓ + 1) (push G g (target G x y s g) (G.parents g) s.key bk).2.1
          = pendSum G (ℓ + 1) bk + (G.parents g).length := by
        unfold pendSum
        apply push_len
        intro p hp
        have := hG.level_lt p g ((hG.parents_iff g p).1 hp)
        have := hG.level_le p
        rw [mem_Ico]
        omega
      have e3 := push_cost G g (target G x y s g) (G.parents g) s.key bk
      have e4 := dcost_eq G g
      refine ⟨h1, ?_⟩
      simp only [List.length_cons]
      omega

lemma PInv.next (h : PInv G x y s0 ℓ [] s bk) : PInv G x y s0 (ℓ + 1) (bk (ℓ + 1)) s bk where
  keys := h.keys
  pend := by
    intro g'
    rcases h.pend g' with h1 | ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1
    · simp at h2
    · by_cases hl : G.level g' = ℓ + 1
      · exact Or.inr (Or.inl ⟨hl, hl ▸ h2⟩)
      · exact Or.inr (Or.inr ⟨by omega, h2⟩)
  chg := fun g' hg' => ⟨(h.chg g' hg').1.trans (Nat.le_succ _), (h.chg g' hg').2⟩
  leaf := h.leaf
  bkt := h.bkt
  rst := fun g' hg' => h.bkt (ℓ + 1) g' hg'

/-- **Level sweep: invariant and exact operation count.** -/
theorem waveLevels_spec (hG : G.WF) (s0 : EState α) (bk0 : ℕ → List ℕ)
    (h0 : PInv G x y s0 0 (bk0 0) s0 bk0) : ∀ ℓ, ℓ ≤ G.L + 1 →
      PInv G x y s0 ℓ ((waveLevels G x y ℓ s0 bk0).2.1 ℓ) (waveLevels G x y ℓ s0 bk0).1
        (waveLevels G x y ℓ s0 bk0).2.1 ∧
      (waveLevels G x y ℓ s0 bk0).2.2 + pendSum G ℓ (waveLevels G x y ℓ s0 bk0).2.1
        = ℓ + pendSum G 0 bk0 + chgSum G s0 (waveLevels G x y ℓ s0 bk0).1 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _
    refine ⟨h0, ?_⟩
    simp [waveLevels, chgSum]
  | succ ℓ ih =>
    intro hℓ
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := procList_spec hG s0 ℓ _ _ _ h1
    have hsplit : pendSum G ℓ (waveLevels G x y ℓ s0 bk0).2.1
        = ((waveLevels G x y ℓ s0 bk0).2.1 ℓ).length
          + pendSum G (ℓ + 1) (waveLevels G x y ℓ s0 bk0).2.1 := by
      unfold pendSum
      exact Finset.sum_eq_sum_Ico_succ_bot (by omega) _
    refine ⟨?_, ?_⟩
    · simp only [waveLevels]
      exact h3.next
    · simp only [waveLevels]
      omega

/-- Number of reverse-incidence deliveries of a wave: one per changed gate and parent. -/
def vol (G : Dag) (s0 s : EState α) : ℕ :=
  ∑ g ∈ (range G.N).filter (fun g => s.val g ≠ s0.val g), (G.parents g).length

/-- **Correctness and exact cost of a backup wave** (`prop:representation-cost`, one
endpoint).  From a state satisfying the engine invariant, after `wave G x y`:

* the invariant holds again (the stored values are the exact evaluation), leaf `x` stores
  `y`, and all other leaves are unchanged;
* the cost is exactly `L + 3` plus, for every gate `g` whose value changed under exact
  evaluation and every parent `p` of `g`, `⌈log₂ deg p⌉ + 3` units.

In particular each changed gate delivers along each of its parent incidences exactly once
and unchanged gates deliver nothing. -/
theorem wave_spec (hG : G.WF) (x : ℕ) (y : α) (s0 : EState α) (hx : x < G.N)
    (h0 : Inv G s0) :
    Inv G (wave G x y s0).1 ∧
    (G.children x = [] → (wave G x y s0).1.val x = y) ∧
    (∀ g, G.children g = [] → g ≠ x → (wave G x y s0).1.val g = s0.val g) ∧
    (wave G x y s0).2 = G.L + 3 + chgSum G s0 (wave G x y s0).1 := by
  set bk0 : ℕ → List ℕ := fun l => if l = G.level x then [x] else [] with hbk0
  have hbkt : ∀ l, ∀ g ∈ bk0 l, G.level g = l ∧ g < G.N := by
    intro l g hg
    by_cases hl : l = G.level x
    · have hg' : g ∈ [x] := by
        simpa [hbk0, hl] using hg
      rw [List.mem_singleton] at hg'
      subst hg'
      exact ⟨hl.symm, hx⟩
    · simp [hbk0, hl] at hg
  have hxb : x ∈ bk0 (G.level x) := by simp [hbk0]
  have hP : PInv G x y s0 0 (bk0 0) s0 bk0 := by
    refine ⟨h0.keys, ?_, ?_, fun _ _ _ => rfl, hbkt, fun g hg => hbkt 0 g hg⟩
    · intro g
      by_cases hl : G.children g = []
      · by_cases hgx : g = x
        · subst hgx
          by_cases hlev : G.level g = 0
          · exact Or.inr (Or.inl ⟨hlev, hlev ▸ hxb⟩)
          · exact Or.inr (Or.inr ⟨by omega, hxb⟩)
        · left
          unfold target
          rw [ite_eq_left hl, ite_eq_right hgx]
      · left
        unfold target
        rw [ite_eq_right hl]
        exact h0.gate g hl
    · intro g hg
      exact absurd rfl hg
  obtain ⟨h1, h2⟩ := waveLevels_spec hG s0 bk0 hP (G.L + 1) le_rfl
  have hcons : ∀ g, (waveLevels G x y (G.L + 1) s0 bk0).1.val g
      = target G x y (waveLevels G x y (G.L + 1) s0 bk0).1 g := by
    intro g
    have := hG.level_le g
    rcases h1.pend g with h | ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · omega
    · omega
  have hpend0 : pendSum G 0 bk0 = 1 := by
    unfold pendSum
    have hlen : ∀ l, (bk0 l).length = if l = G.level x then 1 else 0 := by
      intro l
      simp only [hbk0]
      split_ifs <;> simp
    have hmem : G.level x ∈ Ico 0 (G.L + 1) := by
      have := hG.level_le x
      rw [mem_Ico]
      omega
    simp only [hlen, sum_ite_eq', hmem, ite_true]
  have hpendL : pendSum G (G.L + 1) (waveLevels G x y (G.L + 1) s0 bk0).2.1 = 0 := by
    unfold pendSum
    simp
  refine ⟨⟨?_, h1.keys⟩, ?_, h1.leaf, ?_⟩
  · intro g hg
    have := hcons g
    unfold target at this
    rw [ite_eq_right hg] at this
    exact this
  · intro hl
    have := hcons x
    unfold target at this
    rw [ite_eq_left hl, ite_eq_left rfl] at this
    exact this
  · show (waveLevels G x y (G.L + 1) s0 bk0).2.2 + 1
      = G.L + 3 + chgSum G s0 (waveLevels G x y (G.L + 1) s0 bk0).1
    omega

omit [LinearOrder α] [OrderBot α] in
lemma dcost_le (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D) (g : ℕ) :
    dcost G g ≤ (G.parents g).length * (Nat.clog 2 D + 3) := by
  unfold dcost
  calc ((G.parents g).map (fun p => Nat.clog 2 (G.children p).length + 3)).sum
      ≤ ((G.parents g).map (fun _ => Nat.clog 2 D + 3)).sum := by
        apply List.sum_le_sum
        intro p _
        exact Nat.add_le_add_right (Nat.clog_mono_right 2 (hD p)) 3
    _ = (G.parents g).length * (Nat.clog 2 D + 3) := by simp

omit [LinearOrder α] [OrderBot α] in
lemma length_le_dcost (g : ℕ) : (G.parents g).length ≤ dcost G g := by
  rw [dcost_eq]
  omega

omit [OrderBot α] in
/-- With heap sizes (gate degrees) at most `D`, the delivery cost of a wave is between the
number of deliveries and `⌈log₂ D⌉ + 3` times that number. -/
lemma chgSum_bounds (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D) (s0 s : EState α) :
    vol G s0 s ≤ chgSum G s0 s ∧ chgSum G s0 s ≤ (Nat.clog 2 D + 3) * vol G s0 s := by
  unfold vol chgSum
  constructor
  · exact sum_le_sum (fun g _ => length_le_dcost g)
  · rw [mul_sum]
    apply sum_le_sum
    intro g _
    rw [mul_comm]
    exact dcost_le D hD g

end Engine

/-! ## The engine in the accounting of `prop:representation-cost` -/

section Accounting

variable {α : Type*} [LinearOrder α] [OrderBot α] {G : Dag}

/-- The incidence set of the circuit as pairs `(parent, child)` of gates. -/
def incF (G : Dag) : Finset (Fin G.N × Fin G.N) :=
  univ.filter (fun e => (e.2 : ℕ) ∈ G.children e.1)

/-- The active incoming parent degree of a gate is the length of its parent list. -/
lemma inDeg_incF (hG : G.WF) (v : Fin G.N) : inDeg (incF G) v = (G.parents v).length := by
  unfold inDeg incF
  rw [filter_filter]
  have himg : ((univ.filter (fun e : Fin G.N × Fin G.N =>
      (e.2 : ℕ) ∈ G.children e.1 ∧ e.2 = v)).image (fun e => (e.1 : ℕ)))
      = (G.parents v).toFinset := by
    ext p
    simp only [mem_image, mem_filter, mem_univ, true_and, List.mem_toFinset]
    constructor
    · rintro ⟨e, ⟨h1, h2⟩, rfl⟩
      rw [← h2]
      exact (hG.parents_iff _ _).2 h1
    · intro hp
      exact ⟨(⟨p, hG.parent_lt _ _ hp⟩, v), ⟨(hG.parents_iff _ _).1 hp, rfl⟩, rfl⟩
  rw [← List.toFinset_card_of_nodup (hG.parents_nodup v), ← himg, card_image_of_injOn]
  intro e he e' he' h
  rw [mem_coe, mem_filter] at he he'
  exact Prod.ext (Fin.ext h) (he.2.2.trans he'.2.2.symm)

omit [OrderBot α] in
/-- The number of deliveries of a wave is the delivery volume `Σ_v b(v) d⁻(v)` with
`b(v) = 1` if the value of `v` changed and `0` otherwise. -/
lemma vol_eq_deliveryVolume (hG : G.WF) (s0 s : EState α) :
    vol G s0 s
      = deliveryVolume (incF G) (fun v : Fin G.N => if s.val v ≠ s0.val v then 1 else 0) := by
  unfold deliveryVolume
  simp only [inDeg_incF hG]
  rw [Fin.sum_univ_eq_sum_range
    (fun g => (if s.val g ≠ s0.val g then 1 else 0) * (G.parents g).length) G.N]
  unfold vol
  rw [sum_filter]
  apply sum_congr rfl
  intro g _
  split_ifs <;> simp

/-- **Interval wave**: terminal `x` receives the lower endpoint `yl` and the upper endpoint
`yu`; one wave per endpoint (both endpoints of a max-gate are maxima over its children). -/
def ivWave (G : Dag) (x : ℕ) (yl yu : α) (s : EState α × EState α) :
    (EState α × EState α) × ℕ :=
  (((wave G x yl s.1).1, (wave G x yu s.2).1), (wave G x yl s.1).2 + (wave G x yu s.2).2)

/-- State of the engine after `t` waves of the update sequence `u` (`u t = (x, l, u)` is
the terminal update of rollout `t ≥ 1`). -/
def runState (G : Dag) (u : ℕ → ℕ × α × α) (s0 : EState α × EState α) :
    ℕ → EState α × EState α
  | 0 => s0
  | t + 1 => (ivWave G (u (t + 1)).1 (u (t + 1)).2.1 (u (t + 1)).2.2 (runState G u s0 t)).1

/-- Cost of the backup wave of rollout `t ≥ 1`. -/
def waveCost (G : Dag) (u : ℕ → ℕ × α × α) (s0 : EState α × EState α) (t : ℕ) : ℕ :=
  (ivWave G (u t).1 (u t).2.1 (u t).2.2 (runState G u s0 (t - 1))).2

/-- The endpoints of gate `v` that change in wave `t`: `0` for the lower endpoint, `1` for
the upper one.  Its cardinality is `b_t(v) ∈ {0, 1, 2}`. -/
def chSet (G : Dag) (u : ℕ → ℕ × α × α) (s0 : EState α × EState α) (t : ℕ) (v : Fin G.N) :
    Finset (Fin 2) :=
  (if (runState G u s0 t).1.val v ≠ (runState G u s0 (t - 1)).1.val v then {0} else ∅) ∪
  (if (runState G u s0 t).2.val v ≠ (runState G u s0 (t - 1)).2.val v then {1} else ∅)

lemma card_chSet (u : ℕ → ℕ × α × α) (s0 : EState α × EState α) (t : ℕ) (v : Fin G.N) :
    (chSet G u s0 t v).card
      = (if (runState G u s0 t).1.val v ≠ (runState G u s0 (t - 1)).1.val v then 1 else 0)
        + (if (runState G u s0 t).2.val v ≠ (runState G u s0 (t - 1)).2.val v
            then 1 else 0) := by
  unfold chSet
  split_ifs <;> rfl

lemma deliveryVolume_add {V : Type*} [Fintype V] [DecidableEq V] (F : Finset (V × V))
    (a b : V → ℕ) :
    deliveryVolume F (fun v => a v + b v) = deliveryVolume F a + deliveryVolume F b := by
  unfold deliveryVolume
  simp only [add_mul, sum_add_distrib]

lemma runState_inv (hG : G.WF) (u : ℕ → ℕ × α × α) (hu : ∀ t, (u t).1 < G.N)
    (s0 : EState α × EState α) (h0 : Inv G s0.1 ∧ Inv G s0.2) :
    ∀ t, Inv G (runState G u s0 t).1 ∧ Inv G (runState G u s0 t).2 := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    exact ⟨(wave_spec hG _ _ _ (hu _) ih.1).1, (wave_spec hG _ _ _ (hu _) ih.2).1⟩

/-- **Per-wave work of the interval engine.**  For every rollout `t ≥ 1`, with all gate
degrees at most `D`, the cost of the wave is at least the number of deliveries
`|deliverySet F (ch t)| = Σ_v b_t(v) d⁻(v)` and at most
`2 (L + 3) + (⌈log₂ D⌉ + 3)` times that number. -/
theorem waveCost_bounds (hG : G.WF) (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D)
    (u : ℕ → ℕ × α × α) (hu : ∀ t, (u t).1 < G.N)
    (s0 : EState α × EState α) (h0 : Inv G s0.1 ∧ Inv G s0.2) (t : ℕ) (ht : 1 ≤ t) :
    (deliverySet (incF G) (chSet G u s0 t)).card ≤ waveCost G u s0 t ∧
    waveCost G u s0 t
      ≤ 2 * (G.L + 3) + (Nat.clog 2 D + 3) * (deliverySet (incF G) (chSet G u s0 t)).card := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hinv := runState_inv hG u hu s0 h0 t
  have hl := (wave_spec hG (u (t + 1)).1 (u (t + 1)).2.1 _ (hu _) hinv.1).2.2.2
  have hh := (wave_spec hG (u (t + 1)).1 (u (t + 1)).2.2 _ (hu _) hinv.2).2.2.2
  have hbl := chgSum_bounds D hD (runState G u s0 t).1
    (wave G (u (t + 1)).1 (u (t + 1)).2.1 (runState G u s0 t).1).1
  have hbh := chgSum_bounds D hD (runState G u s0 t).2
    (wave G (u (t + 1)).1 (u (t + 1)).2.2 (runState G u s0 t).2).1
  have hcard : (deliverySet (incF G) (chSet G u s0 (t + 1))).card
      = vol G (runState G u s0 t).1
          (wave G (u (t + 1)).1 (u (t + 1)).2.1 (runState G u s0 t).1).1
        + vol G (runState G u s0 t).2
          (wave G (u (t + 1)).1 (u (t + 1)).2.2 (runState G u s0 t).2).1 := by
    rw [card_deliverySet]
    simp only [card_chSet]
    rw [deliveryVolume_add, vol_eq_deliveryVolume hG, vol_eq_deliveryVolume hG]
    rfl
  have hcost : waveCost G u s0 (t + 1)
      = (wave G (u (t + 1)).1 (u (t + 1)).2.1 (runState G u s0 t).1).2
        + (wave G (u (t + 1)).1 (u (t + 1)).2.2 (runState G u s0 t).2).2 := rfl
  rw [hcard, hcost, hl, hh]
  constructor
  · omega
  · nlinarith [hbl.2, hbh.2]

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper` for the engine.**  Let
`W = P + Σ_{t ≤ τ} waveCost t` be the total work of the interval engine on the circuit `G`
(upfront work `P`, then `τ` backup waves).  With `H = 2 τ (L + 3)` (the level scheduling
of the waves), any `n`, `e`, and `log D := ⌈log₂ D⌉ + 1`:

`W ≤ 3 (H + P + n + e + (S⁺ + e) log D)`,

where `S⁺` is the delivery volume of `eq:s-plus-minus` for the constant incidence set of
`G` and `b_t(v)` the number of endpoints of `v` changed by wave `t` under exact evaluation.
This is `Representation.work_upper` with its accounting hypotheses discharged. -/
theorem engine_work_upper (hG : G.WF) (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D)
    (u : ℕ → ℕ × α × α) (hu : ∀ t, (u t).1 < G.N)
    (s0 : EState α × EState α) (h0 : Inv G s0.1 ∧ Inv G s0.2) (τ P n e : ℕ) :
    P + ∑ t ∈ Icc 1 τ, waveCost G u s0 t
      ≤ 3 * (2 * τ * (G.L + 3) + P + n + e
          + (Splus τ (fun _ => incF G) (fun t v => (chSet G u s0 t v).card) + e)
            * (Nat.clog 2 D + 1)) := by
  apply work_upper τ (fun _ => incF G) (chSet G u s0)
    (fun t => deliverySet (incF G) (chSet G u s0 t)) (fun t _ => subset_rfl)
    (P + ∑ t ∈ Icc 1 τ, waveCost G u s0 t) (2 * τ * (G.L + 3)) P n e (Nat.clog 2 D + 1) 3
    (by norm_num)
  have hsum : ∑ t ∈ Icc 1 τ, waveCost G u s0 t
      ≤ ∑ t ∈ Icc 1 τ, (2 * (G.L + 3)
          + (Nat.clog 2 D + 3) * (deliverySet (incF G) (chSet G u s0 t)).card) :=
    sum_le_sum (fun t ht =>
      (waveCost_bounds hG D hD u hu s0 h0 t (mem_Icc.1 ht).1).2)
  rw [sum_add_distrib, sum_const, Nat.card_Icc, ← mul_sum] at hsum
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hsum
  nlinarith [Nat.zero_le (∑ t ∈ Icc 1 τ, (deliverySet (incF G) (chSet G u s0 t)).card),
    Nat.zero_le (Nat.clog 2 D), Nat.zero_le e, Nat.zero_le n]

/-- **`prop:representation-cost`, lower bound `Ω(P + S⁻)` for the engine.**  The total work
of the interval engine is at least `P + S⁻`: every changed endpoint is delivered along
every live incidence.  This is `Representation.work_lower` with its hypotheses discharged
(for this engine; it is not a lower bound over all possible implementations). -/
theorem engine_work_lower (hG : G.WF) (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D)
    (u : ℕ → ℕ × α × α) (hu : ∀ t, (u t).1 < G.N)
    (s0 : EState α × EState α) (h0 : Inv G s0.1 ∧ Inv G s0.2) (τ P : ℕ) :
    P + Sminus τ (fun _ => incF G) (fun t v => (chSet G u s0 t v).card)
      ≤ P + ∑ t ∈ Icc 1 τ, waveCost G u s0 t := by
  apply work_lower τ (fun _ => incF G) (chSet G u s0)
    (fun t => deliverySet (incF G) (chSet G u s0 t)) (fun t _ => subset_rfl)
  exact Nat.add_le_add_left (sum_le_sum (fun t ht =>
    (waveCost_bounds hG D hD u hu s0 h0 t (mem_Icc.1 ht).1).1)) P

end Accounting

/-! ## Copying a retained circuit (`prop:unrestricted-compiler`) -/

section Copy

/-- Copy a list of gate indices; one unit per entry. -/
def copyList : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | c :: cs => (c :: (copyList cs).1, (copyList cs).2 + 1)

lemma copyList_spec (l : List ℕ) : copyList l = (l, l.length) := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp only [copyList, ih, List.length_cons]

/-- Copy an adjacency array: one unit per vertex record and one per incidence. -/
def copyAdj : List (List ℕ) → List (List ℕ) × ℕ
  | [] => ([], 0)
  | v :: vs => ((copyList v).1 :: (copyAdj vs).1, 1 + (copyList v).2 + (copyAdj vs).2)

lemma copyAdj_spec (adj : List (List ℕ)) :
    copyAdj adj = (adj, adj.length + (adj.map List.length).sum) := by
  induction adj with
  | nil => rfl
  | cons v vs ih =>
    simp only [copyAdj, copyList_spec, ih, List.length_cons, List.map_cons, List.sum_cons]
    rw [Prod.mk.injEq]
    exact ⟨rfl, by omega⟩

/-- A retained monitor circuit as arrays: child lists and parent (reverse-incidence) lists
indexed by gate, the level of each gate, and the ordered list of root-action output gates.
Gate indices are the canonical terminal and gate identities. -/
structure ADag where
  children : List (List ℕ)
  parents : List (List ℕ)
  level : List ℕ
  roots : List ℕ

/-- Number of vertices `|V|`. -/
def ADag.V (G : ADag) : ℕ := G.children.length

/-- Number of incidences `|E|`. -/
def ADag.E (G : ADag) : ℕ := (G.children.map List.length).sum

/-- The engine's view of a retained circuit. -/
def ADag.toDag (G : ADag) (L : ℕ) : Dag :=
  ⟨G.children.length, fun i => G.children.getD i [], fun i => G.parents.getD i [],
    fun i => G.level.getD i 0, L⟩

/-- **Copy of a retained circuit**: copy the four arrays. -/
def copyDag (G : ADag) : ADag × ℕ :=
  (⟨(copyAdj G.children).1, (copyAdj G.parents).1, (copyList G.level).1,
      (copyList G.roots).1⟩,
   (copyAdj G.children).2 + (copyAdj G.parents).2 + (copyList G.level).2
    + (copyList G.roots).2)

/-- The copy is identical to the input (terminal identities and root-action order are
preserved) and its cost is the number of array cells copied. -/
theorem copyDag_spec (G : ADag) :
    (copyDag G).1 = G ∧
    (copyDag G).2 = G.children.length + (G.children.map List.length).sum
      + (G.parents.length + (G.parents.map List.length).sum) + G.level.length
      + G.roots.length := by
  refine ⟨?_, ?_⟩ <;> simp only [copyDag, copyAdj_spec, copyList_spec]

/-- **`prop:unrestricted-compiler`, copy cost.**  For a retained circuit whose parent array
is the reverse of its child array (same number of vertices and incidences), with one level
per vertex and at most `|V|` root outputs, the copy costs at most `4 (|V| + |E|)` units. -/
theorem copyDag_cost_le (G : ADag) (hp : G.parents.length = G.V)
    (hpe : (G.parents.map List.length).sum = G.E) (hl : G.level.length = G.V)
    (hr : G.roots.length ≤ G.V) : (copyDag G).2 ≤ 4 * (G.V + G.E) := by
  rw [(copyDag_spec G).2, hp, hpe, hl]
  unfold ADag.V ADag.E at *
  omega

/-- **`prop:unrestricted-compiler`.**  A compiler that copies the retained circuit and then
runs any costed monitor `run` on the copy (in particular the engine above, i.e. Graph
Selective maintenance on the original circuit) produces the same result as `run` on the
original circuit, with at most `4 (|V| + |E|)` additional setup work. -/
theorem retained_compiler {β : Type*} (run : ADag → β × ℕ) (G : ADag)
    (hp : G.parents.length = G.V) (hpe : (G.parents.map List.length).sum = G.E)
    (hl : G.level.length = G.V) (hr : G.roots.length ≤ G.V) :
    (run (copyDag G).1).1 = (run G).1 ∧
    (copyDag G).2 + (run (copyDag G).1).2 ≤ (run G).2 + 4 * (G.V + G.E) := by
  have h := copyDag_cost_le G hp hpe hl hr
  rw [(copyDag_spec G).1]
  exact ⟨rfl, by omega⟩

end Copy

/-! ## Step 3 of `thm:coded-covers`: work of direct graph maintenance -/

section ParityWork

variable {α : Type*} [LinearOrder α] [OrderBot α] {G : Dag}

lemma sum_toFinset_le (l : List ℕ) (f : ℕ → ℕ) : ∑ g ∈ l.toFinset, f g ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases ha : a ∈ l.toFinset
    · rw [insert_eq_of_mem ha]
      omega
    · rw [sum_insert ha]
      omega

lemma flatMap_length_le (l : List ℕ) (f : ℕ → List ℕ) (m : ℕ)
    (h : ∀ g ∈ l, (f g).length ≤ m) : (l.flatMap f).length ≤ l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (List.mem_cons.2 (Or.inl rfl))
    have h2 := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-- **Only ancestors of the updated terminal change.**  If `U` contains `x` and is closed
under taking parents, the wave leaves every gate outside `U` unchanged. -/
theorem wave_unchanged_outside (hG : G.WF) (x : ℕ) (y : α) (s0 : EState α) (hx : x < G.N)
    (h0 : Inv G s0) (U : Set ℕ) (hxU : x ∈ U) (hU : ∀ g ∈ U, ∀ p ∈ G.parents g, p ∈ U) :
    ∀ g, g ∉ U → (wave G x y s0).1.val g = s0.val g := by
  obtain ⟨hI, -, hleaf, -⟩ := wave_spec hG x y s0 hx h0
  have key : ∀ n g, G.level g < n → g ∉ U → (wave G x y s0).1.val g = s0.val g := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg hgU
      by_cases hl : G.children g = []
      · exact hleaf g hl (fun e => hgU (e ▸ hxU))
      · rw [hI.gate g hl, h0.gate g hl]
        apply heapMax_congr
        intro c hc
        rw [hI.keys g c hc, h0.keys g c hc]
        have := hG.level_lt g c hc
        exact ih c (by omega) (fun hcU => hgU (hU c hcU g ((hG.parents_iff c g).2 hc)))
  exact fun g hg => key (G.level g + 1) g (Nat.lt_succ_self _) hg

/-- The number of deliveries of a wave is at most the number of parent incidences of any
parent-closed set of gates containing the updated terminal. -/
theorem vol_le_of_closed (hG : G.WF) (x : ℕ) (y : α) (s0 : EState α) (hx : x < G.N)
    (h0 : Inv G s0) (T : Finset ℕ) (hxT : x ∈ T)
    (hT : ∀ g ∈ T, ∀ p ∈ G.parents g, p ∈ T) :
    vol G s0 (wave G x y s0).1 ≤ ∑ g ∈ T, (G.parents g).length := by
  unfold vol
  apply sum_le_sum_of_subset
  intro g hg
  by_contra hgT
  exact (mem_filter.1 hg).2
    (wave_unchanged_outside hG x y s0 hx h0 (↑T) (mem_coe.2 hxT)
      (fun g hg p hp => mem_coe.2 (hT g (mem_coe.1 hg) p hp)) g (fun h => hgT (mem_coe.1 h)))

/-- **Work of one wave on a circuit of parity-grid shape.**  Suppose the updated terminal
`x` has at most `m0` parents (coordinate gates), each of these has at most `m1` parents
(parity actions), each of those has at most `m2` parents (the root), and the gates above
have none.  With gate degrees at most `D`, the wave costs at most
`L + 3 + (⌈log₂ D⌉ + 3) (m0 + m0 m1 + m0 m1 m2)` units.  For the parity grid of
`thm:coded-covers` (`m0 = 2`, `m1 ≤ 2r`, `m2 = 1`, `D ≤ 4r`) this is `O(r log r)`. -/
theorem wave_cost_three_layers (hG : G.WF) (x : ℕ) (y : α) (s0 : EState α) (hx : x < G.N)
    (h0 : Inv G s0) (D m0 m1 m2 : ℕ) (hD : ∀ p, (G.children p).length ≤ D)
    (hm0 : (G.parents x).length ≤ m0)
    (hm1 : ∀ g ∈ G.parents x, (G.parents g).length ≤ m1)
    (hm2 : ∀ g ∈ (G.parents x).flatMap G.parents, (G.parents g).length ≤ m2)
    (hm3 : ∀ g ∈ ((G.parents x).flatMap G.parents).flatMap G.parents, G.parents g = []) :
    (wave G x y s0).2
      ≤ G.L + 3 + (Nat.clog 2 D + 3) * (m0 + m0 * m1 + m0 * m1 * m2) := by
  have hclosed : ∀ g ∈ ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents).toFinset,
      ∀ p ∈ G.parents g, p ∈ ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents).toFinset := by
    intro g hg p hp
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hg ⊢
    rcases hg with ((rfl | hg) | hg) | hg
    · exact Or.inl (Or.inl (Or.inr hp))
    · exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨g, hg, hp⟩))
    · exact Or.inr (List.mem_flatMap.2 ⟨g, hg, hp⟩)
    · rw [hm3 g hg] at hp
      simp at hp
  have hxT : x ∈ ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents).toFinset := by simp
  have hvol := vol_le_of_closed hG x y s0 hx h0 _ hxT hclosed
  have hlist := sum_toFinset_le ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents)
      (fun g => (G.parents g).length)
  have e1 : ((G.parents x).map (fun g => (G.parents g).length)).sum
      = ((G.parents x).flatMap G.parents).length := by
    rw [List.length_flatMap]
  have e2 : (((G.parents x).flatMap G.parents).map (fun g => (G.parents g).length)).sum
      = (((G.parents x).flatMap G.parents).flatMap G.parents).length := by
    rw [List.length_flatMap]
  have e3 : ((((G.parents x).flatMap G.parents).flatMap G.parents).map
      (fun g => (G.parents g).length)).sum = 0 := by
    have := flatMap_length_le (((G.parents x).flatMap G.parents).flatMap G.parents)
      G.parents 0 (fun g hg => by rw [hm3 g hg]; simp)
    rw [List.length_flatMap] at this
    omega
  have b2 := flatMap_length_le (G.parents x) G.parents m1 hm1
  have b3 := flatMap_length_le ((G.parents x).flatMap G.parents) G.parents m2 hm2
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, e1, e2, e3] at hlist
  have b2' : ((G.parents x).flatMap G.parents).length ≤ m0 * m1 :=
    b2.trans (Nat.mul_le_mul_right _ hm0)
  have b3' : (((G.parents x).flatMap G.parents).flatMap G.parents).length ≤ m0 * m1 * m2 :=
    b3.trans (Nat.mul_le_mul_right _ b2')
  have hV : vol G s0 (wave G x y s0).1 ≤ m0 + m0 * m1 + m0 * m1 * m2 := by
    omega
  have hc := (wave_spec hG x y s0 hx h0).2.2.2
  have hb := (chgSum_bounds D hD s0 (wave G x y s0).1).2
  rw [hc]
  have := Nat.mul_le_mul_left (Nat.clog 2 D + 3) hV
  omega

/-- **Root-level count bound** (Step 3 of the proof of `thm:coded-covers`).  There are `d`
losing root actions with counts `n a t` and the winning action `w*` with count `nw t`;
every rollout goes to exactly one root action.  If from time `t0` on a losing action is
selected only when its index reaches the winner's lower value,
`0.03 + 2 √(log(1+t) / N_a(t)) ≥ 0.98`, and each losing action has count at most `1` at
`t0`, then `N_{w*}(t) ≥ t - d (1 + 5 log(1+t))`. -/
theorem winner_count_lower {d : ℕ} (n : Fin d → ℕ → ℕ) (nw : ℕ → ℕ)
    (pick : Fin d → ℕ → Prop) (t0 : ℕ)
    (htot : ∀ t, nw t + ∑ a, n a t = t)
    (hstep : ∀ a t, t0 ≤ t →
      (pick a t → n a (t + 1) = n a t + 1) ∧ (¬ pick a t → n a (t + 1) = n a t))
    (hsel : ∀ a t, t0 ≤ t → pick a t →
      (0.98 : ℝ) ≤ 0.03 + 2 * Real.sqrt (Real.log (1 + t) / n a t))
    (h0 : ∀ a, n a t0 ≤ 1) :
    ∀ t, t0 ≤ t → (t : ℝ) - d * (1 + 5 * Real.log (1 + t)) ≤ nw t := by
  intro t ht
  have hlog : 0 ≤ Real.log (1 + (t : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)
  have hbound : ∀ a, (n a t : ℝ) ≤ 1 + 5 * Real.log (1 + t) := by
    intro a
    have h := uct_count_le (c := 2) (b := 0.98) (u0 := 0.03) (by norm_num) (n a) (pick a) t0
      (hstep a) (hsel a) t ht
    have h1 : (n a t0 : ℝ) ≤ 1 := by exact_mod_cast h0 a
    have h2 : (2 : ℝ) ^ 2 * Real.log (1 + t) / (0.98 - 0.03) ^ 2
        ≤ 5 * Real.log (1 + t) := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [hlog]
    exact h.trans (max_le (by linarith) (by linarith))
  have hsum : ∑ a, (n a t : ℝ) ≤ d * (1 + 5 * Real.log (1 + t)) := by
    calc ∑ a, (n a t : ℝ) ≤ ∑ _a : Fin d, (1 + 5 * Real.log (1 + (t : ℝ))) :=
          sum_le_sum (fun a _ => hbound a)
      _ = d * (1 + 5 * Real.log (1 + t)) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : (nw t : ℝ) + ∑ a, (n a t : ℝ) = t := by exact_mod_cast htot t
  linarith

/-- Logarithm estimate for the horizon `T ≈ 1024 r log r`. -/
lemma log_horizon_le {r T : ℝ} (hr : 4 ≤ r) (hT : T ≤ 1024 * r * Real.log r + 1)
    (hT0 : 0 ≤ T) : Real.log (1 + T) ≤ 8 + 2 * Real.log r ∧ 1 ≤ Real.log r := by
  have hL1 : 1 ≤ Real.log r := by
    have h4 : 1 ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact h4.trans (Real.log_le_log (by norm_num) hr)
  have hr0 : 0 < r := by linarith
  have hL0 : 0 < Real.log r := by linarith
  have hprod : 4 ≤ r * Real.log r := by nlinarith
  have h1 : 1 + T ≤ 2048 * r * Real.log r := by nlinarith
  have h2 : Real.log (1 + T) ≤ Real.log (2048 * r * Real.log r) :=
    Real.log_le_log (by linarith) h1
  have h3 : Real.log (2048 * r * Real.log r)
      = Real.log 2048 + Real.log r + Real.log (Real.log r) := by
    rw [Real.log_mul (mul_pos (by norm_num) hr0).ne' hL0.ne',
      Real.log_mul (by norm_num) hr0.ne']
  have h4 : Real.log 2048 ≤ 8 := by
    have e : (2048 : ℝ) = 2 ^ 11 := by norm_num
    rw [e, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have h5 : Real.log (Real.log r) ≤ Real.log r := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  exact ⟨by linarith, hL1⟩

/-- **Stopping horizon and total work on the parity grid** (Step 3 of the proof of
`thm:coded-covers`, deterministic part).  Let `r = 2^k ≥ 4` and let the root-level process
satisfy the hypotheses of `winner_count_lower` with `d ≤ 4r` losing actions.  Assume:

* `hstop`: the run has stopped by any time at which `w*` has `n0` observations (this stands
  for: on the simultaneous coverage event the confidence radius at `n0` samples is below
  `0.18`, which certifies `w*`), with `n0 ≤ 512 r log r`;
* `hcost`: every rollout before stopping costs at most `croll` units (allocator work plus
  the backup wave; `wave_cost_three_layers` bounds the wave by `O(r log r)`).

Then `τ ≤ 1024 r k` and the total work is at most `P + 1024 r k · croll`.  With
`croll = O(r k)` and `P = O(r² k)` this is `O(r² log² r)`. -/
theorem parity_total_work {k d : ℕ} (hk : 2 ≤ k) (hd : d ≤ 4 * 2 ^ k)
    (n : Fin d → ℕ → ℕ) (nw : ℕ → ℕ) (pick : Fin d → ℕ → Prop) (t0 : ℕ)
    (htot : ∀ t, nw t + ∑ a, n a t = t)
    (hstep : ∀ a t, t0 ≤ t →
      (pick a t → n a (t + 1) = n a t + 1) ∧ (¬ pick a t → n a (t + 1) = n a t))
    (hsel : ∀ a t, t0 ≤ t → pick a t →
      (0.98 : ℝ) ≤ 0.03 + 2 * Real.sqrt (Real.log (1 + t) / n a t))
    (h0 : ∀ a, n a t0 ≤ 1)
    (ht0 : t0 ≤ ⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊)
    (n0 : ℝ) (hn0 : n0 ≤ 512 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k))
    (τ : ℕ) (hstop : ∀ t, t0 ≤ t → n0 ≤ (nw t : ℝ) → τ ≤ t)
    (cost : ℕ → ℕ) (croll P : ℕ) (hcost : ∀ t ∈ Icc 1 τ, cost t ≤ croll) :
    τ ≤ 1024 * 2 ^ k * k ∧ P + ∑ t ∈ Icc 1 τ, cost t ≤ P + 1024 * 2 ^ k * k * croll := by
  have hr4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    linarith
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ k := by linarith
  have hL1 : 1 ≤ Real.log ((2 : ℝ) ^ k) := by
    have h4 : 1 ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact h4.trans (Real.log_le_log (by norm_num) hr4)
  have hnn : 0 ≤ 1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) := by positivity
  have hts1 : 1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)
      ≤ (⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊ : ℝ) := Nat.le_ceil _
  have hts2 : (⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊ : ℝ)
      ≤ 1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) + 1 := (Nat.ceil_lt_add_one hnn).le
  have hlog := (log_horizon_le hr4 hts2 (Nat.cast_nonneg _)).1
  have hw := winner_count_lower n nw pick t0 htot hstep hsel h0 _ ht0
  have hd' : (d : ℝ) ≤ 4 * (2 : ℝ) ^ k := by exact_mod_cast hd
  have hlog0 : 0 ≤ Real.log
      (1 + (⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊ : ℝ)) :=
    Real.log_nonneg (by
      have : (0 : ℝ) ≤ (⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊ : ℝ) :=
        Nat.cast_nonneg _
      linarith)
  have hA : (d : ℝ) * (1 + 5 * Real.log
        (1 + (⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊ : ℝ)))
      ≤ 4 * (2 : ℝ) ^ k * (41 + 10 * Real.log ((2 : ℝ) ^ k)) :=
    mul_le_mul hd' (by linarith) (by linarith) (by linarith)
  have hrL : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) := by nlinarith
  have hstopped : τ ≤ ⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊ :=
    hstop _ ht0 (by nlinarith)
  have hk1 : Real.log ((2 : ℝ) ^ k) ≤ k := by
    rw [Real.log_pow]
    have := Real.log_two_lt_d9
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have htsle : ⌈1024 * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)⌉₊ ≤ 1024 * 2 ^ k * k := by
    rw [Nat.ceil_le]
    push_cast
    have : (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ k * k :=
      mul_le_mul_of_nonneg_left hk1 hr0.le
    nlinarith
  have hτ : τ ≤ 1024 * 2 ^ k * k := hstopped.trans htsle
  refine ⟨hτ, Nat.add_le_add_left ?_ P⟩
  calc ∑ t ∈ Icc 1 τ, cost t ≤ (Icc 1 τ).card • croll := sum_le_card_nsmul _ _ _ hcost
    _ = τ * croll := by simp
    _ ≤ 1024 * 2 ^ k * k * croll := Nat.mul_le_mul_right _ hτ

end ParityWork

/-! ## Exact evaluation, the empty state, and interval waves on parity-grid shapes -/

section Exact

variable {α : Type*} [LinearOrder α] [OrderBot α] {G : Dag}

/-- **The invariant determines the stored values.**  Two states satisfying the engine
invariant with the same leaf values store the same value at every gate: the stored values
are the exact evaluation of the circuit, so "the endpoints of `v` that change under exact
evaluation" is the set of gates whose stored value changes. -/
theorem Inv.val_unique (hG : G.WF) {s s' : EState α} (h : Inv G s) (h' : Inv G s')
    (hleaf : ∀ g, G.children g = [] → s.val g = s'.val g) : ∀ g, s.val g = s'.val g := by
  have key : ∀ n g, G.level g < n → s.val g = s'.val g := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg
      by_cases hl : G.children g = []
      · exact hleaf g hl
      · rw [h.gate g hl, h'.gate g hl]
        apply heapMax_congr
        intro c hc
        rw [h.keys g c hc, h'.keys g c hc]
        have := hG.level_lt g c hc
        exact ih c (by omega)
  exact fun g => key (G.level g + 1) g (Nat.lt_succ_self _)

lemma heapMax_bot (cs : List ℕ) : heapMax cs (fun _ => (⊥ : α)) = ⊥ := by
  unfold heapMax
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.foldr_cons, ih, bot_sup_eq]

/-- The state with every value and key equal to `⊥` satisfies the invariant.  Starting from
it, the initial terminal values can be installed by waves, whose cost is then computed by
the engine itself. -/
theorem Inv.bot (G : Dag) : Inv G (⟨fun _ => ⊥, fun _ _ => ⊥⟩ : EState α) where
  gate := fun g _ => (heapMax_bot (G.children g)).symm
  keys := fun _ _ _ => rfl

/-- Work of one interval wave on a circuit of parity-grid shape: twice the bound of
`wave_cost_three_layers`. -/
theorem ivWave_cost_three_layers (hG : G.WF) (x : ℕ) (yl yu : α) (s : EState α × EState α)
    (hx : x < G.N) (h0 : Inv G s.1 ∧ Inv G s.2) (D m0 m1 m2 : ℕ)
    (hD : ∀ p, (G.children p).length ≤ D) (hm0 : (G.parents x).length ≤ m0)
    (hm1 : ∀ g ∈ G.parents x, (G.parents g).length ≤ m1)
    (hm2 : ∀ g ∈ (G.parents x).flatMap G.parents, (G.parents g).length ≤ m2)
    (hm3 : ∀ g ∈ ((G.parents x).flatMap G.parents).flatMap G.parents, G.parents g = []) :
    (ivWave G x yl yu s).2
      ≤ 2 * (G.L + 3 + (Nat.clog 2 D + 3) * (m0 + m0 * m1 + m0 * m1 * m2)) := by
  have h1 := wave_cost_three_layers hG x yl s.1 hx h0.1 D m0 m1 m2 hD hm0 hm1 hm2 hm3
  have h2 := wave_cost_three_layers hG x yu s.2 hx h0.2 D m0 m1 m2 hD hm0 hm1 hm2 hm3
  show (wave G x yl s.1).2 + (wave G x yu s.2).2 ≤ _
  omega

end Exact

end CostEngines
end JointRootCert
