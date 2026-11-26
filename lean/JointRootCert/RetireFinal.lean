/-
Joint Root Certification: release of orphaned gates, root-action retirement and the
leader-and-stop query inside the DAG engine.

Manuscript result covered:

* `prop:uct-coupling` (Safe permanent retirement; also labelled `prop:ta-coupled`,
  `thm:protected-pruning`, `thm:decision-retirement`), with the work bounds
  `eq:ram-work-bounds`.

IMPORTS `JointRootCert.EngineFinal` (a new file; build it first).

## The engine

The Graph-Selective engine of this file extends `DagRetire.rstep` by

* **release of orphaned gates** (`releaseLoop`): after a retirement pass, every child of a
  tested incidence is examined; a gate that still has children, has no live parent left
  (reference count `|parents| = 0`) and is not the gate of an active root action is
  released: all its child incidences are unlinked and its children are examined in turn;
* **root-action retirement** (`qRetire`, the rule of `thm:decision-retirement`): at a root
  query, with `a` the lowest-index lower-bound leader among the active actions, every other
  active action `b` with `u(b) < l(a)` becomes inactive; its gate loses its protection and
  is examined for release;
* **the leader-and-stop query** (`qOut`): the lowest-index lower-bound leader among the
  active actions and the marginal stopping bit `max_{b ≠ a active} u(b) - l(a) ≤ ε`.

A released gate is no longer maintained: its stored interval is stale.  The invariant
`CInv` states that every gate that is not released (in particular the gate of every active
root action) stores the interval of the eager full-incidence engine.

## Cost model

As in `DagRetire.lean`.  New charges, one unit each: examining a gate for release;
unlinking one child incidence of a released gate (this disposes the heap entry as well; no
sift is needed since the whole heap is discarded); one index of a root scan (leader scan,
stop scan, retirement scan).  The scans are structural recursions over the `K` root
indices and their cost `K` is charged by definition.

Order values are compared through a strictly monotone map `φ : α → ℝ`, so that the stopping
bit `u(b) - l(a) ≤ ε` of `PassiveRetirement.MarginalStops` is defined.
-/
import JointRootCert.EngineFinal

namespace JointRootCert
namespace RetireFinal

open Finset CostEngines DagRetire EngineFinal
open HeapImpl (Heap HEState SimE Rep waveH findMax)

/-! ## Releasing a gate -/

/-- The circuit with every child incidence of gate `g` unlinked: the child list of `g` is
emptied and `g` is removed from the parent list of each of its children. -/
def releaseDag (G : Dag) (g : ℕ) : Dag where
  N := G.N
  children := fun p => if p = g then [] else G.children p
  parents := fun c => if c ∈ G.children g then (G.parents c).filter (· ≠ g) else G.parents c
  level := G.level
  L := G.L

lemma mem_release_children {G : Dag} {g p c : ℕ} :
    c ∈ (releaseDag G g).children p ↔ c ∈ G.children p ∧ p ≠ g := by
  show c ∈ (if p = g then [] else G.children p) ↔ _
  by_cases h : p = g
  · simp [h]
  · simp [h]

lemma mem_release_parents {G : Dag} (hG : G.WF) {g p c : ℕ} :
    p ∈ (releaseDag G g).parents c ↔ p ∈ G.parents c ∧ p ≠ g := by
  show p ∈ (if c ∈ G.children g then (G.parents c).filter (· ≠ g) else G.parents c) ↔ _
  by_cases h : c ∈ G.children g
  · simp [h, List.mem_filter]
  · rw [ite_eq_right h]
    constructor
    · intro hp
      refine ⟨hp, fun e => h ?_⟩
      rw [e] at hp
      exact (hG.parents_iff c g).1 hp
    · exact fun hp => hp.1

lemma release_children_sublist (G : Dag) (g p : ℕ) :
    ((releaseDag G g).children p).Sublist (G.children p) := by
  show (if p = g then [] else G.children p).Sublist _
  split_ifs
  · exact List.nil_sublist _
  · exact List.Sublist.refl _

lemma release_parents_sublist (G : Dag) (g c : ℕ) :
    ((releaseDag G g).parents c).Sublist (G.parents c) := by
  show (if c ∈ G.children g then (G.parents c).filter (· ≠ g) else G.parents c).Sublist _
  split_ifs
  · exact List.filter_sublist
  · exact List.Sublist.refl _

lemma releaseDag_wf {G : Dag} (hG : G.WF) (g : ℕ) : (releaseDag G g).WF where
  parents_iff := by
    intro c p
    rw [mem_release_parents hG, mem_release_children, hG.parents_iff]
  parents_nodup := fun c => (hG.parents_nodup c).sublist (release_parents_sublist G g c)
  parent_lt := fun c p h => hG.parent_lt c p ((release_parents_sublist G g c).subset h)
  level_lt := fun p c h => hG.level_lt p c ((release_children_sublist G g p).subset h)
  level_le := hG.level_le

/-- Allocated cells of the live circuit: one per live incidence and one per gate that
still has children. -/
def cells (G : Dag) : ℕ :=
  ∑ p ∈ range G.N, ((G.children p).length + if G.children p = [] then 0 else 1)

lemma cells_le_of_sub {G G' : Dag} (hN : G'.N = G.N)
    (h : ∀ p, (G'.children p).Sublist (G.children p)) : cells G' ≤ cells G := by
  unfold cells
  rw [hN]
  apply sum_le_sum
  intro p _
  have h1 := (h p).length_le
  by_cases e : G.children p = []
  · have e' : G'.children p = [] := List.sublist_nil.1 (e ▸ h p)
    rw [ite_eq_left e, ite_eq_left e']
    omega
  · rw [ite_eq_right e]
    split_ifs <;> omega

lemma live_le_of_sub {G G' : Dag} (hN : G'.N = G.N)
    (h : ∀ p, (G'.children p).Sublist (G.children p)) : live G' ≤ live G := by
  unfold live
  rw [hN]
  exact sum_le_sum (fun p _ => (h p).length_le)

/-- The cells of a circuit are at most its gates plus its incidences. -/
lemma cells_le (G : Dag) : cells G ≤ G.N + live G := by
  unfold cells live
  rw [sum_add_distrib]
  have : ∑ p ∈ range G.N, (if G.children p = [] then 0 else 1) ≤ ∑ _p ∈ range G.N, 1 :=
    sum_le_sum (fun p _ => by split_ifs <;> omega)
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at this
  omega

/-- Releasing a gate with children frees exactly its child incidences and its own cell. -/
lemma cells_release {G : Dag} {g : ℕ} (hg : g < G.N) (hc : G.children g ≠ []) :
    cells (releaseDag G g) + (G.children g).length + 1 = cells G := by
  have hp : g ∈ range G.N := mem_range.2 hg
  unfold cells
  show ∑ p ∈ range G.N, (((releaseDag G g).children p).length
    + if (releaseDag G g).children p = [] then 0 else 1) + _ + 1 = _
  rw [← add_sum_erase _ _ hp, ← add_sum_erase _ (fun p => (G.children p).length
    + if G.children p = [] then 0 else 1) hp]
  have h1 : ∑ p ∈ (range G.N).erase g, (((releaseDag G g).children p).length
      + if (releaseDag G g).children p = [] then 0 else 1)
      = ∑ p ∈ (range G.N).erase g, ((G.children p).length
        + if G.children p = [] then 0 else 1) := by
    apply sum_congr rfl
    intro p hp'
    have hne : p ≠ g := (mem_erase.1 hp').1
    have : (releaseDag G g).children p = G.children p := by
      show (if p = g then [] else G.children p) = _
      rw [ite_eq_right hne]
    rw [this]
  have h2 : (releaseDag G g).children g = [] := by
    show (if g = g then [] else G.children g) = []
    rw [ite_eq_left rfl]
  rw [h1, h2, ite_eq_right hc]
  simp only [List.length_nil, ite_true]
  omega

/-- **The release cascade** (reference counting).  Examine the gates on the stack (1 unit
each); a gate that has children, has no live parent and is not protected is released:
its child incidences are unlinked (1 unit each) and its children are pushed. -/
def releaseLoop (prot : ℕ → Bool) : ℕ → List ℕ → Dag → Dag × ℕ
  | 0, _, G => (G, 0)
  | _ + 1, [], G => (G, 0)
  | f + 1, g :: st, G =>
    if G.children g ≠ [] ∧ G.parents g = [] ∧ prot g = false then
      ((releaseLoop prot f (G.children g ++ st) (releaseDag G g)).1,
       (releaseLoop prot f (G.children g ++ st) (releaseDag G g)).2 + 1 + (G.children g).length)
    else ((releaseLoop prot f st G).1, (releaseLoop prot f st G).2 + 1)

/-- Fuel that suffices for the cascade to empty its stack. -/
def relFuel (G : Dag) (st : List ℕ) : ℕ := 2 * cells G + st.length + 1

/-- Properties of the release cascade that hold for every fuel: the result is a
well-formed sub-circuit with the same gates, and the cost plus twice the remaining cells
is at most the initial stack plus twice the initial cells (every cell is disposed of at
most once). -/
theorem releaseLoop_spec (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (G : Dag), G.WF →
    (releaseLoop prot f st G).1.WF ∧ (releaseLoop prot f st G).1.N = G.N ∧
    (releaseLoop prot f st G).1.level = G.level ∧ (releaseLoop prot f st G).1.L = G.L ∧
    (∀ p, ((releaseLoop prot f st G).1.children p).Sublist (G.children p)) ∧
    (∀ c, ((releaseLoop prot f st G).1.parents c).Sublist (G.parents c)) ∧
    (releaseLoop prot f st G).2 + 2 * cells (releaseLoop prot f st G).1
      ≤ st.length + 2 * cells G := by
  intro f
  induction f with
  | zero =>
    intro st G hG
    exact ⟨hG, rfl, rfl, rfl, fun _ => List.Sublist.refl _, fun _ => List.Sublist.refl _,
      by show 0 + 2 * cells G ≤ _; omega⟩
  | succ f ih =>
    intro st G hG
    cases st with
    | nil =>
      exact ⟨hG, rfl, rfl, rfl, fun _ => List.Sublist.refl _, fun _ => List.Sublist.refl _,
        by show 0 + 2 * cells G ≤ 0 + 2 * cells G; omega⟩
    | cons g st =>
      rw [releaseLoop]
      by_cases hc : G.children g ≠ [] ∧ G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc]
        obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih (G.children g ++ st) (releaseDag G g)
          (releaseDag_wf hG g)
        obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc.1
        have hgN : g < G.N := hG.parent_lt c g ((hG.parents_iff c g).2 hcm)
        have hcell := cells_release hgN hc.1
        refine ⟨a1, a2, a3, a4, fun p => (a5 p).trans (release_children_sublist G g p),
          fun c => (a6 c).trans (release_parents_sublist G g c), ?_⟩
        rw [List.length_append] at a7
        show (releaseLoop prot f (G.children g ++ st) (releaseDag G g)).2 + 1
            + (G.children g).length
            + 2 * cells (releaseLoop prot f (G.children g ++ st) (releaseDag G g)).1
          ≤ (st.length + 1) + 2 * cells G
        omega
      · rw [ite_eq_right hc]
        obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih st G hG
        refine ⟨a1, a2, a3, a4, a5, a6, ?_⟩
        show (releaseLoop prot f st G).2 + 1 + 2 * cells (releaseLoop prot f st G).1
          ≤ (st.length + 1) + 2 * cells G
        omega

/-! ## The coupled invariant -/

section Inv

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- A gate is released (dead): internal in the original circuit, without live children. -/
def Dead (G0 G : Dag) (g : ℕ) : Prop := G0.children g ≠ [] ∧ G.children g = []

/-- The reference valuation: exact lower and upper valuations of the original circuit,
with nonempty intervals. -/
structure RefOK (G0 : Dag) (elo ehi : ℕ → α) : Prop where
  lo : Exact G0 elo
  hi : Exact G0 ehi
  cons : ∀ g, elo g ≤ ehi g

/-- **Invariant of the engine with retirement, release and root retirement**, relative to
the original circuit `G0`, the root gates `rt i` (`i < K`), the activity flags `act` and
the reference valuation `(elo, ehi)`:

* the live circuit is a well-formed sub-circuit and the engine invariant holds on it;
* `agree`: every gate that is not released stores the reference interval;
* `dom`: every unlinked incidence `(p, c)` of a non-released gate `p` is strictly
  dominated in the reference valuation;
* `live_child`: a released gate has no live parent;
* `prot`: the gate of every active root action is not released. -/
structure CInv (G0 : Dag) (K : ℕ) (rt : ℕ → ℕ) (s : RState α) (act : ℕ → Bool)
    (elo ehi : ℕ → α) : Prop where
  wf : s.G.WF
  nEq : s.G.N = G0.N
  levelEq : s.G.level = G0.level
  lEq : s.G.L = G0.L
  csub : ∀ p, (s.G.children p).Sublist (G0.children p)
  psub : ∀ c, (s.G.parents c).Sublist (G0.parents c)
  invLo : Inv s.G s.lo
  invHi : Inv s.G s.hi
  agree : ∀ g, ¬ Dead G0 s.G g → s.lo.val g = elo g ∧ s.hi.val g = ehi g
  dom : ∀ p c, c ∈ G0.children p → c ∉ s.G.children p → ¬ Dead G0 s.G p → ehi c < elo p
  live_child : ∀ p c, c ∈ s.G.children p → ¬ Dead G0 s.G c
  prot : ∀ i, i < K → act i = true → ¬ Dead G0 s.G (rt i)

variable {G0 : Dag} {K : ℕ} {rt : ℕ → ℕ} {s : RState α} {act : ℕ → Bool} {elo ehi : ℕ → α}

lemma not_dead_of_child {G0 G : Dag} {p c : ℕ} (hc : c ∈ G.children p) : ¬ Dead G0 G p :=
  fun hd => List.ne_nil_of_mem hc hd.2

/-- The initial state: all incidences live, no gate released. -/
theorem CInv.init (hG : G0.WF) {lo hi : EState α} (hlo : Inv G0 lo) (hhi : Inv G0 hi)
    (K : ℕ) (rt : ℕ → ℕ) (act : ℕ → Bool) :
    CInv G0 K rt ⟨G0, lo, hi⟩ act lo.val hi.val where
  wf := hG
  nEq := rfl
  levelEq := rfl
  lEq := rfl
  csub := fun _ => List.Sublist.refl _
  psub := fun _ => List.Sublist.refl _
  invLo := hlo
  invHi := hhi
  agree := fun _ _ => ⟨rfl, rfl⟩
  dom := fun _ _ h h' _ => absurd h h'
  live_child := fun _ _ _ hd => hd.1 hd.2
  prot := fun _ _ _ hd => hd.1 hd.2

/-- Deactivating root actions preserves the invariant. -/
theorem CInv.deact (h : CInv G0 K rt s act elo ehi) {act' : ℕ → Bool}
    (hle : ∀ i, act' i = true → act i = true) : CInv G0 K rt s act' elo ehi :=
  { h with prot := fun i hi ha => h.prot i hi (hle i ha) }

/-- **A retirement test preserves the invariant** (`thm:protected-pruning`, rule (i)). -/
theorem CInv.retireOne (h : CInv G0 K rt s act elo ehi) (ref : RefOK G0 elo ehi)
    (e : ℕ × ℕ) : CInv G0 K rt (retireOne e s).1 act elo ehi := by
  unfold DagRetire.retireOne
  by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
  · rw [ite_eq_left hc]
    obtain ⟨hm, hlt⟩ := hc
    have hne : s.G.children e.1 ≠ [] := List.ne_nil_of_mem hm
    have hndp : ¬ Dead G0 s.G e.1 := not_dead_of_child hm
    have hndc : ¬ Dead G0 s.G e.2 := h.live_child e.1 e.2 hm
    have consc : s.lo.val e.2 ≤ s.hi.val e.2 := by
      rw [(h.agree e.2 hndc).1, (h.agree e.2 hndc).2]; exact ref.cons e.2
    have consp : s.lo.val e.1 ≤ s.hi.val e.1 := by
      rw [(h.agree e.1 hndp).1, (h.agree e.1 hndp).2]; exact ref.cons e.1
    have hlo_lt : s.lo.key e.1 e.2 < heapMax (s.G.children e.1) (s.lo.key e.1) := by
      rw [← h.invLo.gate e.1 hne, h.invLo.keys e.1 e.2 hm]
      exact consc.trans_lt hlt
    have hhi_lt : s.hi.key e.1 e.2 < heapMax (s.G.children e.1) (s.hi.key e.1) := by
      rw [← h.invHi.gate e.1 hne, h.invHi.keys e.1 e.2 hm]
      exact hlt.trans_le consp
    have hfl : heapMax ((s.G.children e.1).filter (· ≠ e.2)) (s.lo.key e.1) = s.lo.val e.1 := by
      rw [heapMax_erase hlo_lt, ← h.invLo.gate e.1 hne]
    have hfh : heapMax ((s.G.children e.1).filter (· ≠ e.2)) (s.hi.key e.1) = s.hi.val e.1 := by
      rw [heapMax_erase hhi_lt, ← h.invHi.gate e.1 hne]
    have hch : ∀ g, (retireDag s.G e.1 e.2).children g
        = if g = e.1 then (s.G.children g).filter (· ≠ e.2) else s.G.children g := fun _ => rfl
    have hfne : (s.G.children e.1).filter (· ≠ e.2) ≠ [] := by
      intro hnil
      rw [hnil] at hfl
      have : s.lo.val e.1 = ⊥ := hfl.symm
      rw [this] at hlt
      exact not_lt_bot hlt
    have hdead : ∀ g, Dead G0 (retireDag s.G e.1 e.2) g ↔ Dead G0 s.G g := by
      intro g
      unfold Dead
      rw [hch]
      by_cases hge : g = e.1
      · rw [ite_eq_left hge, hge]
        exact ⟨fun hd => absurd hd.2 hfne, fun hd => absurd hd.2 hne⟩
      · rw [ite_eq_right hge]
    refine ⟨retireDag_wf h.wf _ _, h.nEq, h.levelEq, h.lEq,
      fun p => (retire_children_sublist _ _ _ p).trans (h.csub p),
      fun c => (retire_parents_sublist _ _ _ c).trans (h.psub c), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ?_, ?_, ?_, ?_⟩
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
    · intro g hg
      exact h.agree g (fun hd => hg ((hdead g).2 hd))
    · intro p c hc0 hnc hnd
      have hnd' : ¬ Dead G0 s.G p := fun hd => hnd ((hdead p).2 hd)
      by_cases hold : c ∈ s.G.children p
      · have : p = e.1 ∧ c = e.2 := by
          by_contra hcon
          exact hnc (mem_retire_children.2 ⟨hold, hcon⟩)
        rw [this.1, this.2, ← (h.agree e.2 hndc).2, ← (h.agree e.1 hndp).1]
        exact hlt
      · exact h.dom p c hc0 hold hnd'
    · intro p c hcm hd
      exact h.live_child p c (mem_retire_children.1 hcm).1 ((hdead c).1 hd)
    · intro i hi ha hd
      exact h.prot i hi ha ((hdead _).1 hd)
  · rw [ite_eq_right hc]
    exact h

theorem CInv.retireList (ref : RefOK G0 elo ehi) : ∀ (L : List (ℕ × ℕ)) (s : RState α),
    CInv G0 K rt s act elo ehi → CInv G0 K rt (retireList L s).1 act elo ehi := by
  intro L
  induction L with
  | nil => intro s h; exact h
  | cons e es ih => intro s h; exact ih _ (h.retireOne ref e)

/-- **Releasing an orphaned unprotected gate preserves the invariant**: the gate becomes
dead and nothing that is still maintained reads it. -/
theorem CInv.release (h : CInv G0 K rt s act elo ehi) (g : ℕ) (hc : s.G.children g ≠ [])
    (hp : s.G.parents g = []) (hprot : ∀ i, i < K → act i = true → rt i ≠ g) :
    CInv G0 K rt ⟨releaseDag s.G g, s.lo, s.hi⟩ act elo ehi := by
  have hch : ∀ p, (releaseDag s.G g).children p = if p = g then [] else s.G.children p :=
    fun _ => rfl
  have hdead : ∀ g', Dead G0 (releaseDag s.G g) g' → g' ≠ g → Dead G0 s.G g' := by
    intro g' hd hne
    refine ⟨hd.1, ?_⟩
    have := hd.2
    rw [hch, ite_eq_right hne] at this
    exact this
  have hdead' : ∀ g', Dead G0 s.G g' → Dead G0 (releaseDag s.G g) g' := by
    intro g' hd
    refine ⟨hd.1, ?_⟩
    rw [hch]
    split_ifs
    · rfl
    · exact hd.2
  have hg0 : G0.children g ≠ [] := by
    intro e
    exact hc (List.sublist_nil.1 (e ▸ h.csub g))
  have hgdead : Dead G0 (releaseDag s.G g) g := ⟨hg0, by rw [hch, ite_eq_left rfl]⟩
  refine ⟨releaseDag_wf h.wf g, h.nEq, h.levelEq, h.lEq,
    fun p => (release_children_sublist _ _ p).trans (h.csub p),
    fun c => (release_parents_sublist _ _ c).trans (h.psub c), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    show s.lo.val g' = heapMax ((releaseDag s.G g).children g') (s.lo.key g')
    rw [hch] at hg' ⊢
    by_cases e : g' = g
    · rw [ite_eq_left e] at hg'
      exact absurd rfl hg'
    · rw [ite_eq_right e] at hg' ⊢
      exact h.invLo.gate g' hg'
  · intro p c hcm
    exact h.invLo.keys p c (mem_release_children.1 hcm).1
  · intro g' hg'
    show s.hi.val g' = heapMax ((releaseDag s.G g).children g') (s.hi.key g')
    rw [hch] at hg' ⊢
    by_cases e : g' = g
    · rw [ite_eq_left e] at hg'
      exact absurd rfl hg'
    · rw [ite_eq_right e] at hg' ⊢
      exact h.invHi.gate g' hg'
  · intro p c hcm
    exact h.invHi.keys p c (mem_release_children.1 hcm).1
  · intro g' hg'
    exact h.agree g' (fun hd => hg' (hdead' g' hd))
  · intro p c hc0 hnc hnd
    have hpg : p ≠ g := fun e => hnd (e ▸ hgdead)
    have hnc' : c ∉ s.G.children p := fun hm => hnc (mem_release_children.2 ⟨hm, hpg⟩)
    exact h.dom p c hc0 hnc' (fun hd => hnd (hdead' p hd))
  · intro p c hcm hd
    obtain ⟨hcm', hpg⟩ := mem_release_children.1 hcm
    have hcg : c ≠ g := by
      intro e
      rw [e] at hcm'
      have := (h.wf.parents_iff g p).2 hcm'
      rw [hp] at this
      simp at this
    exact h.live_child p c hcm' (hdead c hd hcg)
  · intro i hi ha hd
    exact h.prot i hi ha (hdead _ hd (hprot i hi ha))

/-- Protection flags of the gates: a gate is protected iff it is the gate of an active
root action. -/
def protOf (K : ℕ) (rt : ℕ → ℕ) (act : ℕ → Bool) (g : ℕ) : Bool :=
  (List.range K).any (fun i => act i && decide (rt i = g))

lemma protOf_false {K : ℕ} {rt : ℕ → ℕ} {act : ℕ → Bool} {g : ℕ}
    (h : protOf K rt act g = false) : ∀ i, i < K → act i = true → rt i ≠ g := by
  intro i hi ha e
  have : protOf K rt act g = true := by
    unfold protOf
    rw [List.any_eq_true]
    exact ⟨i, List.mem_range.2 hi, by simp [ha, e]⟩
  rw [h] at this
  exact Bool.false_ne_true this

/-- **The release cascade preserves the invariant**, for every fuel and stack. -/
theorem CInv.releaseLoop : ∀ (f : ℕ) (st : List ℕ) (s : RState α),
    CInv G0 K rt s act elo ehi →
    CInv G0 K rt ⟨(releaseLoop (protOf K rt act) f st s.G).1, s.lo, s.hi⟩ act elo ehi := by
  intro f
  induction f with
  | zero => intro st s h; exact h
  | succ f ih =>
    intro st s h
    cases st with
    | nil => exact h
    | cons g st =>
      rw [RetireFinal.releaseLoop]
      by_cases hc : s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ protOf K rt act g = false
      · rw [ite_eq_left hc]
        exact ih (s.G.children g ++ st) ⟨releaseDag s.G g, s.lo, s.hi⟩
          (h.release g hc.1 hc.2.1 (protOf_false hc.2.2))
      · rw [ite_eq_right hc]
        exact ih st s h

/-- Level induction on the non-released gates: two valuations that satisfy the max
equations on the live circuit and agree at its leaves agree at every non-released gate. -/
lemma agree_of_live_exact {G : Dag} (hG : G.WF) {v e : ℕ → α} (nd : ℕ → Prop)
    (hv : ∀ g, G.children g ≠ [] → v g = heapMax (G.children g) v)
    (he : ∀ g, nd g → G.children g ≠ [] → e g = heapMax (G.children g) e)
    (hleaf : ∀ g, nd g → G.children g = [] → v g = e g)
    (hch : ∀ p c, c ∈ G.children p → nd c) : ∀ g, nd g → v g = e g := by
  have key : ∀ n, ∀ g, G.level g < n → nd g → v g = e g := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg hnd
      by_cases hc : G.children g = []
      · exact hleaf g hnd hc
      · rw [hv g hc, he g hnd hc]
        exact heapMax_congr (fun c hcm =>
          ih c (by have := hG.level_lt g c hcm; omega) (hch g c hcm))
  exact fun g => key (G.level g + 1) g (Nat.lt_succ_self _)

/-- **A backup wave on the live circuit preserves the invariant**, with the reference
moved to the valuation after the terminal update.  The update addresses a terminal of the
original circuit; the new reference has the updated terminal value, the other terminal
values unchanged, lower values not smaller and upper values not larger (nested boxes). -/
theorem CInv.wave (h : CInv G0 K rt s act elo ehi) {elo' ehi' : ℕ → α}
    (ref' : RefOK G0 elo' ehi') (u : ℕ × α × α) (hx : u.1 < G0.N)
    (hlo' : ∀ g, G0.children g = [] → elo' g = if g = u.1 then u.2.1 else elo g)
    (hhi' : ∀ g, G0.children g = [] → ehi' g = if g = u.1 then u.2.2 else ehi g)
    (hmono : ∀ g, elo g ≤ elo' g) (hanti : ∀ g, ehi' g ≤ ehi g) :
    CInv G0 K rt (waveStep u s).1 act elo' ehi' := by
  obtain ⟨l1, l2, l3, _⟩ := wave_spec h.wf u.1 u.2.1 s.lo (h.nEq ▸ hx) h.invLo
  obtain ⟨u1, u2, u3, _⟩ := wave_spec h.wf u.1 u.2.2 s.hi (h.nEq ▸ hx) h.invHi
  have hleafG : ∀ g, G0.children g = [] → s.G.children g = [] :=
    fun g e => List.sublist_nil.1 (e ▸ h.csub g)
  have hold : ∀ g, ¬ Dead G0 s.G g → s.G.children g ≠ [] →
      elo g = heapMax (s.G.children g) elo := by
    intro g hnd hc
    rw [← (h.agree g hnd).1, h.invLo.gate g hc]
    exact heapMax_congr (fun c hcm =>
      (h.invLo.keys g c hcm).trans (h.agree c (h.live_child g c hcm)).1)
  have hE1 : ∀ g, ¬ Dead G0 s.G g → s.G.children g ≠ [] →
      elo' g = heapMax (s.G.children g) elo' := by
    intro g hnd hc
    have hg0 : G0.children g ≠ [] := fun e => hc (hleafG g e)
    rw [ref'.lo g hg0]
    apply heapMax_eq_of_sub (fun c hcm => (h.csub g).subset hcm)
    intro c hc0
    by_cases hm : c ∈ s.G.children g
    · exact Or.inl hm
    · right
      calc elo' c ≤ ehi' c := ref'.cons c
        _ ≤ ehi c := hanti c
        _ ≤ elo g := (h.dom g c hc0 hm hnd).le
        _ = heapMax (s.G.children g) elo := hold g hnd hc
        _ ≤ heapMax (s.G.children g) elo' := heapMax_mono (fun c _ => hmono c)
  have hE2 : ∀ g, ¬ Dead G0 s.G g → s.G.children g ≠ [] →
      ehi' g = heapMax (s.G.children g) ehi' := by
    intro g hnd hc
    have hg0 : G0.children g ≠ [] := fun e => hc (hleafG g e)
    rw [ref'.hi g hg0]
    apply heapMax_eq_of_sub (fun c hcm => (h.csub g).subset hcm)
    intro c hc0
    by_cases hm : c ∈ s.G.children g
    · exact Or.inl hm
    · right
      calc ehi' c ≤ ehi c := hanti c
        _ ≤ elo g := (h.dom g c hc0 hm hnd).le
        _ ≤ elo' g := hmono g
        _ = heapMax (s.G.children g) elo' := hE1 g hnd hc
        _ ≤ heapMax (s.G.children g) ehi' := heapMax_mono (fun c _ => ref'.cons c)
  have hagL : ∀ g, ¬ Dead G0 s.G g → (CostEngines.wave s.G u.1 u.2.1 s.lo).1.val g = elo' g := by
    apply agree_of_live_exact h.wf (fun g => ¬ Dead G0 s.G g)
      (fun g hc => (l1.gate g hc).trans (heapMax_congr (fun c hcm => l1.keys g c hcm))) hE1
      ?_ (fun p c hcm => h.live_child p c hcm)
    intro g hnd hc
    have hg0 : G0.children g = [] := by
      by_contra hne
      exact hnd ⟨hne, hc⟩
    by_cases e : g = u.1
    · rw [e] at hc hg0 ⊢
      rw [l2 hc, hlo' u.1 hg0, ite_eq_left rfl]
    · rw [l3 g hc e, (h.agree g hnd).1, hlo' g hg0, ite_eq_right e]
  have hagH : ∀ g, ¬ Dead G0 s.G g → (CostEngines.wave s.G u.1 u.2.2 s.hi).1.val g = ehi' g := by
    apply agree_of_live_exact h.wf (fun g => ¬ Dead G0 s.G g)
      (fun g hc => (u1.gate g hc).trans (heapMax_congr (fun c hcm => u1.keys g c hcm))) hE2
      ?_ (fun p c hcm => h.live_child p c hcm)
    intro g hnd hc
    have hg0 : G0.children g = [] := by
      by_contra hne
      exact hnd ⟨hne, hc⟩
    by_cases e : g = u.1
    · rw [e] at hc hg0 ⊢
      rw [u2 hc, hhi' u.1 hg0, ite_eq_left rfl]
    · rw [u3 g hc e, (h.agree g hnd).2, hhi' g hg0, ite_eq_right e]
  exact ⟨h.wf, h.nEq, h.levelEq, h.lEq, h.csub, h.psub, l1, u1,
    fun g hnd => ⟨hagL g hnd, hagH g hnd⟩,
    fun p c hc0 hnc hnd => lt_of_le_of_lt (hanti c)
      (lt_of_lt_of_le (h.dom p c hc0 hnc hnd) (hmono p)),
    h.live_child, h.prot⟩

end Inv

/-! ## Root scans: leader, stopping bit, root retirement -/

section Scans

variable {α : Type*} [LinearOrder α]

/-- **Leader scan** over the root indices `0, …, n-1`: the lowest-index maximiser of `L`
among the active indices (`none` if no index is active). -/
def leadScan (L : ℕ → α) (act : ℕ → Bool) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => (leadScan L act n).elim (if act n = true then some n else none)
      (fun a => if act n = true ∧ L a < L n then some n else some a)

theorem leadScan_spec (L : ℕ → α) (act : ℕ → Bool) : ∀ n,
    (leadScan L act n = none → ∀ i, i < n → act i = false) ∧
    (∀ a, leadScan L act n = some a → a < n ∧ act a = true ∧
      ∀ i, i < n → act i = true → L i ≤ L a ∧ (L i = L a → a ≤ i)) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun a h => by simp [leadScan] at h⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases hl : leadScan L act n with
    | none =>
      have hs : leadScan L act (n + 1) = if act n = true then some n else none := by
        show (leadScan L act n).elim _ _ = _
        rw [hl]; rfl
      rw [hs]
      have hall := ih1 hl
      by_cases ha : act n = true
      · rw [ite_eq_left ha]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        have ha' : a = n := (Option.some.inj h).symm
        rw [ha']
        refine ⟨Nat.lt_succ_self _, ha, fun i hi hai => ?_⟩
        have : i = n := by
          by_contra hne
          have := hall i (by omega)
          rw [this] at hai
          exact Bool.false_ne_true hai
        rw [this]
        exact ⟨le_rfl, fun _ => le_rfl⟩
      · rw [ite_eq_right ha]
        refine ⟨fun _ i hi => ?_, fun a h => by simp at h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact hall i h
        · rw [h]; simpa using ha
    | some a0 =>
      obtain ⟨b1, b2, b3⟩ := ih2 a0 hl
      have hs : leadScan L act (n + 1)
          = if act n = true ∧ L a0 < L n then some n else some a0 := by
        show (leadScan L act n).elim _ _ = _
        rw [hl]; rfl
      rw [hs]
      by_cases hc : act n = true ∧ L a0 < L n
      · rw [ite_eq_left hc]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        have ha' : a = n := (Option.some.inj h).symm
        rw [ha']
        refine ⟨Nat.lt_succ_self _, hc.1, fun i hi hai => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
        · have hle := (b3 i h' hai).1
          exact ⟨hle.trans hc.2.le, fun e => absurd (e ▸ hle) (not_le.2 hc.2)⟩
        · rw [h']
          exact ⟨le_rfl, fun _ => le_rfl⟩
      · rw [ite_eq_right hc]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        have ha' : a = a0 := (Option.some.inj h).symm
        rw [ha']
        refine ⟨by omega, b2, fun i hi hai => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
        · exact b3 i h' hai
        · rw [h']
          have hnl : ¬ L a0 < L n := fun hlt => hc ⟨h' ▸ hai, hlt⟩
          exact ⟨not_lt.1 hnl, fun _ => by omega⟩

/-- **Stop scan** over the root indices `0, …, n-1`: every active index other than the
leader `a` has `φ(U i) - φ(la) ≤ ε`. -/
noncomputable def stopScan (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ)
    (act : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => stopScan φ ε U la a act n
      && (!(act n) || decide (n = a) || decide (φ (U n) - φ la ≤ ε))

omit [LinearOrder α] in
theorem stopScan_spec (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ) (act : ℕ → Bool) :
    ∀ n, stopScan φ ε U la a act n = true
      ↔ ∀ i, i < n → act i = true → i ≠ a → φ (U i) - φ la ≤ ε := by
  intro n
  induction n with
  | zero => simp [stopScan]
  | succ n ih =>
    rw [stopScan, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi hai hia
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h hai hia
      · rw [h] at hai hia ⊢
        simpa [hai, hia] using h2
    · intro h
      refine ⟨fun i hi => h i (by omega), ?_⟩
      by_cases ha : act n = true
      · by_cases hna : n = a
        · simp [hna]
        · simp [ha, hna, h n (Nat.lt_succ_self n) ha hna]
      · simp [ha]

/-- **The leader-and-stop query**: the lowest-index lower-bound leader among the active
root actions and the marginal stopping bit (`false` if no action is active). -/
noncomputable def qOut (φ : α → ℝ) (ε : ℝ) (K : ℕ) (L U : ℕ → α) (act : ℕ → Bool) :
    Option ℕ × Bool :=
  (leadScan L act K, (leadScan L act K).elim false (fun a => stopScan φ ε U (L a) a act K))

/-- Flags after the retirement scan with leader `a`: every other active index `i < K` with
`U i < la` is deactivated. -/
def deact (K a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) : ℕ → Bool :=
  fun i => act i && !(decide (i < K) && decide (i ≠ a) && decide (U i < la))

/-- The gates of the root actions deactivated by the retirement scan. -/
def retiredRoots (K : ℕ) (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) :
    List ℕ :=
  ((List.range K).filter (fun i => act i = true ∧ i ≠ a ∧ U i < la)).map rt

lemma deact_le (K a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) (i : ℕ)
    (h : deact K a U la act i = true) : act i = true := by
  unfold deact at h
  rw [Bool.and_eq_true] at h
  exact h.1

lemma deact_false_iff (K a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) (i : ℕ)
    (hi : act i = true) :
    deact K a U la act i = false ↔ i < K ∧ i ≠ a ∧ U i < la := by
  unfold deact
  simp [hi, and_assoc]

lemma retiredRoots_length (K : ℕ) (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α)
    (act : ℕ → Bool) : (retiredRoots K rt a U la act).length ≤ K := by
  unfold retiredRoots
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

end Scans

/-! ## The Graph-Selective engine: rollouts with release, queries with root retirement -/

section Run

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- State of the Graph-Selective engine: the engine state of `DagRetire` and the activity
flags of the root actions. -/
structure QS (α : Type*) where
  r : RState α
  act : ℕ → Bool

/-- **Root retirement at a query** (`thm:decision-retirement`).  Leader scan (`K` units);
retirement scan (`K` units): every active action other than the leader `a` whose stored
upper value is strictly below the stored lower value of `a` is deactivated; then the
release cascade from the gates of the deactivated actions. -/
def qRetire (K : ℕ) (rt : ℕ → ℕ) (s : QS α) : QS α × ℕ :=
  (leadScan (fun i => s.r.lo.val (rt i)) s.act K).elim (s, K)
    (fun a =>
      (⟨⟨(releaseLoop
            (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r.G).1,
          s.r.lo, s.r.hi⟩,
        deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act⟩,
       K + K + (releaseLoop
            (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r.G).2))

/-- **One rollout of the Graph-Selective engine**: the waves and the retirement pass of
`DagRetire.rstep`, then the release cascade from the children of the tested incidences. -/
def relStep (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ))
    (u : ℕ × α × α) (s : QS α) : QS α × ℕ :=
  (⟨⟨(releaseLoop (protOf K rt s.act)
        (relFuel (rstep cand u s.r).1.G ((cand s.r (waveStep u s.r).1).map Prod.snd))
        ((cand s.r (waveStep u s.r).1).map Prod.snd) (rstep cand u s.r).1.G).1,
      (rstep cand u s.r).1.lo, (rstep cand u s.r).1.hi⟩, s.act⟩,
   (rstep cand u s.r).2 + (releaseLoop (protOf K rt s.act)
        (relFuel (rstep cand u s.r).1.G ((cand s.r (waveStep u s.r).1).map Prod.snd))
        ((cand s.r (waveStep u s.r).1).map Prod.snd) (rstep cand u s.r).1.G).2)

variable {G0 : Dag} {K : ℕ} {rt : ℕ → ℕ} {elo ehi : ℕ → α}

theorem qRetire_inv {s : QS α} (h : CInv G0 K rt s.r s.act elo ehi) :
    CInv G0 K rt (qRetire K rt s).1.r (qRetire K rt s).1.act elo ehi := by
  unfold qRetire
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => exact h
  | some a =>
    exact (h.deact (fun i hi => deact_le _ _ _ _ _ i hi)).releaseLoop _ _ s.r

omit [OrderBot α] in
lemma qRetire_act_le (s : QS α) (i : ℕ) (h : (qRetire K rt s).1.act i = true) :
    s.act i = true := by
  unfold qRetire at h
  cases hl : leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => rw [hl] at h; exact h
  | some a =>
    rw [hl] at h
    have h' : deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act i = true := h
    exact deact_le _ _ _ _ _ i h'

omit [OrderBot α] in
lemma qRetire_act_false (s : QS α) (i : ℕ) (hi : s.act i = true)
    (h : (qRetire K rt s).1.act i = false) :
    ∃ a, leadScan (fun i => s.r.lo.val (rt i)) s.act K = some a ∧ i < K ∧ i ≠ a ∧
      s.r.hi.val (rt i) < s.r.lo.val (rt a) := by
  unfold qRetire at h
  cases hl : leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none =>
    rw [hl] at h
    have h' : s.act i = false := h
    rw [hi] at h'
    exact absurd h' (by simp)
  | some a =>
    rw [hl] at h
    have h' : deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act i = false := h
    exact ⟨a, rfl, (deact_false_iff K a _ _ s.act i hi).1 h'⟩

theorem relStep_inv {s : QS α} (cand : RState α → RState α → List (ℕ × ℕ))
    (h : CInv G0 K rt s.r s.act elo ehi) {elo' ehi' : ℕ → α}
    (ref' : RefOK G0 elo' ehi') (u : ℕ × α × α) (hx : u.1 < G0.N)
    (hlo' : ∀ g, G0.children g = [] → elo' g = if g = u.1 then u.2.1 else elo g)
    (hhi' : ∀ g, G0.children g = [] → ehi' g = if g = u.1 then u.2.2 else ehi g)
    (hmono : ∀ g, elo g ≤ elo' g) (hanti : ∀ g, ehi' g ≤ ehi g) :
    CInv G0 K rt (relStep K rt cand u s).1.r (relStep K rt cand u s).1.act elo' ehi' := by
  have hw := h.wave ref' u hx hlo' hhi' hmono hanti
  have hr : CInv G0 K rt (rstep cand u s.r).1 s.act elo' ehi' :=
    CInv.retireList ref' _ _ hw
  exact hr.releaseLoop _ _ _

/-- The engine without retirement, used as the reference (it holds the same values as the
eager engine `CostEngines.runState`, by `DagRetire.live_eq_eager`). -/
def noCand : RState α → RState α → List (ℕ × ℕ) := fun _ _ => []

variable (K rt)

/-- State of the Graph-Selective engine after `t` rollouts.  If `q t` holds, a root query
with root retirement is made on the state after rollout `t`, before rollout `t + 1`. -/
def runF (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : QS α) : ℕ → QS α
  | 0 => s0
  | t + 1 => (relStep K rt cand (u (t + 1))
      (if q t = true then (qRetire K rt (runF cand u q s0 t)).1 else runF cand u q s0 t)).1

/-- The state on which rollout `t + 1` acts (after the query of time `t`, if any). -/
def preF (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : QS α) (t : ℕ) : QS α :=
  if q t = true then (qRetire K rt (runF K rt cand u q s0 t)).1 else runF K rt cand u q s0 t

/-- Cost of the query of time `t` (if any: stop scan `K`, plus `qRetire`) and of rollout
`t + 1`. -/
def costF (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : QS α) (t : ℕ) : ℕ :=
  (if q t = true then K + (qRetire K rt (runF K rt cand u q s0 t)).2 else 0)
    + (relStep K rt cand (u (t + 1)) (preF K rt cand u q s0 t)).2

/-- Live deliveries of rollout `t + 1`. -/
def volF (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : QS α) (t : ℕ) : ℕ :=
  vol (preF K rt cand u q s0 t).r.G (preF K rt cand u q s0 t).r.lo
      (runF K rt cand u q s0 (t + 1)).r.lo
    + vol (preF K rt cand u q s0 t).r.G (preF K rt cand u q s0 t).r.hi
      (runF K rt cand u q s0 (t + 1)).r.hi

/-- Incidences retired (strict dominance, with heap deletions) by rollout `t + 1`. -/
def retF (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : QS α) (t : ℕ) : ℕ :=
  live (preF K rt cand u q s0 t).r.G
    - live (rstep cand (u (t + 1)) (preF K rt cand u q s0 t).r).1.G

variable {K rt}
variable {cand : RState α → RState α → List (ℕ × ℕ)} {u : ℕ → ℕ × α × α} {q : ℕ → Bool}
  {lo0 hi0 : EState α} {act0 : ℕ → Bool}

/-- Facts about the reference run: exact valuations with nonempty intervals at every time,
terminal values follow the updates, lower values increase and upper values decrease. -/
lemma ref_facts (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (t : ℕ) :
    RefOK G0 (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val ∧
    (u (t + 1)).1 < G0.N ∧
    (∀ g, G0.children g = [] → (rrun noCand u ⟨G0, lo0, hi0⟩ (t + 1)).lo.val g
      = if g = (u (t + 1)).1 then (u (t + 1)).2.1
        else (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val g) ∧
    (∀ g, G0.children g = [] → (rrun noCand u ⟨G0, lo0, hi0⟩ (t + 1)).hi.val g
      = if g = (u (t + 1)).1 then (u (t + 1)).2.2
        else (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val g) ∧
    (∀ g, (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val g
      ≤ (rrun noCand u ⟨G0, lo0, hi0⟩ (t + 1)).lo.val g) ∧
    (∀ g, (rrun noCand u ⟨G0, lo0, hi0⟩ (t + 1)).hi.val g
      ≤ (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val g) := by
  have hI := rrun_inv h0 hn
  obtain ⟨a, b, c, d⟩ := hn t
  obtain ⟨_, _, x3, x4⟩ := rrun_exact h0 hn t
  have hl : ∀ g, G0.children g = [] → (rrun noCand u ⟨G0, lo0, hi0⟩ (t + 1)).lo.val g
      = if g = (u (t + 1)).1 then (u (t + 1)).2.1
        else (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val g := by
    intro g hg
    by_cases e : g = (u (t + 1)).1
    · rw [ite_eq_left e, e]
      exact (x3 (e ▸ hg)).1
    · rw [ite_eq_right e]
      exact (x4 g hg e).1
  have hh : ∀ g, G0.children g = [] → (rrun noCand u ⟨G0, lo0, hi0⟩ (t + 1)).hi.val g
      = if g = (u (t + 1)).1 then (u (t + 1)).2.2
        else (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val g := by
    intro g hg
    by_cases e : g = (u (t + 1)).1
    · rw [ite_eq_left e, e]
      exact (x3 (e ▸ hg)).2
    · rw [ite_eq_right e]
      exact (x4 g hg e).2
  refine ⟨⟨(hI t).exact.1, (hI t).exact.2, (hI t).cons⟩, a, hl, hh, ?_, ?_⟩
  · apply exact_mono hG (hI t).exact.1 (hI (t + 1)).exact.1
    intro g hg
    rw [hl g hg]
    by_cases e : g = (u (t + 1)).1
    · rw [ite_eq_left e, e]; exact b
    · rw [ite_eq_right e]
  · apply exact_mono hG (hI (t + 1)).exact.2 (hI t).exact.2
    intro g hg
    rw [hh g hg]
    by_cases e : g = (u (t + 1)).1
    · rw [ite_eq_left e, e]; exact d
    · rw [ite_eq_right e]

/-- **The invariant along the run** (`prop:uct-coupling`, numerical coupling with release
and root retirement).  At every time, every non-released gate of the Graph-Selective
engine, in particular the gate of every active root action, stores the interval of the
engine without retirement. -/
theorem runF_inv (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) : ∀ t,
    CInv G0 K rt (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r
      (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).act
      (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val := by
  intro t
  induction t with
  | zero => exact CInv.init hG h0.invLo h0.invHi K rt act0
  | succ t ih =>
    obtain ⟨_, f2, f3, f4, f5, f6⟩ := ref_facts hG h0 hn t
    obtain ⟨f1', _⟩ := ref_facts hG h0 hn (t + 1)
    have hpre : CInv G0 K rt (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r
        (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).act
        (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val := by
      unfold preF
      split_ifs
      · exact qRetire_inv ih
      · exact ih
    exact relStep_inv cand hpre f1' (u (t + 1)) f2 f3 f4 f5 f6

lemma preF_inv (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (t : ℕ) :
    CInv G0 K rt (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r
      (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).act
      (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val := by
  have ih := runF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0) hG h0 hn t
  unfold preF
  split_ifs
  · exact qRetire_inv ih
  · exact ih

end Run

/-! ## Coupling of the leader-and-stop outputs -/

section Coupling

variable {α : Type*} [LinearOrder α] [OrderBot α]
variable {G0 : Dag} {K : ℕ} {rt : ℕ → ℕ}
  {cand : RState α → RState α → List (ℕ × ℕ)} {u : ℕ → ℕ × α × α} {q : ℕ → Bool}
  {lo0 hi0 : EState α}

lemma ref_mono (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) : ∀ s t, s ≤ t → ∀ g,
    (rrun noCand u ⟨G0, lo0, hi0⟩ s).lo.val g ≤ (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val g ∧
    (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val g ≤ (rrun noCand u ⟨G0, lo0, hi0⟩ s).hi.val g := by
  intro s t hst
  induction t, hst using Nat.le_induction with
  | base => exact fun g => ⟨le_rfl, le_rfl⟩
  | succ t _ ih =>
    obtain ⟨_, _, _, _, f5, f6⟩ := ref_facts hG h0 hn t
    exact fun g => ⟨(ih g).1.trans (f5 g), (f6 g).trans (ih g).2⟩

/-- Reference lower value of root action `a` at time `t`, as a real number. -/
def refL (φ : α → ℝ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (G0 : Dag) (lo0 hi0 : EState α)
    (K : ℕ) (t : ℕ) (a : Fin K) : ℝ := φ ((rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt a))

/-- Reference upper value of root action `a` at time `t`, as a real number. -/
def refU (φ : α → ℝ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (G0 : Dag) (lo0 hi0 : EState α)
    (K : ℕ) (t : ℕ) (a : Fin K) : ℝ := φ ((rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val (rt a))

/-- The active root actions of the Graph-Selective engine at time `t`. -/
def actSet (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ))
    (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : QS α) (t : ℕ) : Finset (Fin K) :=
  univ.filter (fun a : Fin K => (runF K rt cand u q s0 t).act a = true)

/-- **The root actions of the DAG engine form a `RetireRun`** (`thm:decision-retirement`):
the reference root intervals are nested and nonempty, all actions are active initially, and
an action leaves the active set only at a query at which its upper value is strictly below
the lower value of another active action (the leader). -/
theorem retireRun_of_runF (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (φ : α → ℝ) (hφ : StrictMono φ) :
    RetireRun (refL φ rt u G0 lo0 hi0 K) (refU φ rt u G0 lo0 hi0 K)
      (actSet K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩) where
  nestedL := fun a s t hst => hφ.monotone ((ref_mono hG h0 hn s t hst (rt a)).1)
  nestedU := fun a s t hst => hφ.monotone ((ref_mono hG h0 hn s t hst (rt a)).2)
  nonempty := fun t a => hφ.monotone ((rrun_inv h0 hn t).cons (rt a))
  init := by
    ext a
    simp [actSet, runF]
  anti := by
    intro t a ha
    unfold actSet at ha ⊢
    rw [mem_filter] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have h1 : (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act a = true := ha.2
    unfold preF at h1
    split_ifs at h1
    · exact qRetire_act_le _ _ h1
    · exact h1
  retire := by
    intro t b hb1 hb
    unfold actSet at hb1 hb
    have hbt : (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act b = true :=
      (mem_filter.1 hb).2
    have hbf : (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act b = false := by
      by_contra hne
      refine hb1 (mem_filter.2 ⟨mem_univ _, ?_⟩)
      show (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act b = true
      simpa using hne
    unfold preF at hbf
    by_cases hq : q t = true
    · rw [ite_eq_left hq] at hbf
      obtain ⟨a, ha, _, hba, hlt⟩ := qRetire_act_false _ _ hbt hbf
      obtain ⟨haK, haa, _⟩ := (leadScan_spec _ _ K).2 a ha
      have hinv := runF_inv (K := K) (rt := rt) (cand := cand) (q := q)
        (act0 := fun _ => true) hG h0 hn t
      have ea := hinv.agree (rt a) (hinv.prot a haK haa)
      have eb := hinv.agree (rt b) (hinv.prot b b.isLt hbt)
      refine ⟨⟨a, haK⟩, mem_filter.2 ⟨mem_univ _, haa⟩, fun e => hba (by rw [← e]), ?_⟩
      show φ _ < φ _
      apply hφ
      rw [← eb.2, ← ea.1]
      exact hlt
    · rw [ite_eq_right hq, hbt] at hbf
      exact absurd hbf (by simp)

/-- **Graph-Eager and Graph-Selective return the same leader and the same stopping bit at
every step** (`prop:uct-coupling`, decision coupling).  The query of the Graph-Selective
engine reads the stored values of the ACTIVE root actions only; the reference query reads
the exact values of ALL root actions.  For `ε ≥ 0` and `K ≥ 1` root actions, the two
outputs coincide at every time, although retired actions may have been released and their
stored intervals are stale. -/
theorem query_coupling (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (hK : 0 < K) (φ : α → ℝ)
    (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε) (t : ℕ) :
    qOut φ ε K
        (fun i => (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.lo.val (rt i))
        (fun i => (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.hi.val (rt i))
        (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act
      = qOut φ ε K (fun i => (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt i))
        (fun i => (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val (rt i)) (fun _ => true) := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have RR := retireRun_of_runF (K := K) (rt := rt) (cand := cand) (q := q) hG h0 hn φ hφ
  have hinv := runF_inv (K := K) (rt := rt) (cand := cand) (q := q)
    (act0 := fun _ => true) hG h0 hn t
  generalize hS : runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t = S at hinv ⊢
  have hact : ∀ b : Fin K, b ∈ actSet K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
      ↔ S.act b = true := by
    intro b
    unfold actSet
    rw [mem_filter, hS]
    simp
  have hag : ∀ i, i < K → S.act i = true →
      S.r.lo.val (rt i) = (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt i) ∧
      S.r.hi.val (rt i) = (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val (rt i) :=
    fun i hi ha => hinv.agree (rt i) (hinv.prot i hi ha)
  cases hs : leadScan (fun i => S.r.lo.val (rt i)) S.act K with
  | none =>
    exfalso
    obtain ⟨b, hb⟩ := (RR.invariant t).1
    have h1 := (leadScan_spec _ _ K).1 hs b b.isLt
    rw [(hact b).1 hb] at h1
    exact absurd h1 (by simp)
  | some a =>
    obtain ⟨haK, haa, hspec⟩ := (leadScan_spec _ _ K).2 a hs
    have hLL : LowLeader (actSet K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t)
        (refL φ rt u G0 lo0 hi0 K t) ⟨a, haK⟩ := by
      unfold LowLeader
      refine ⟨(hact ⟨a, haK⟩).2 haa, fun b hb => ?_, fun b hb hbe => ?_⟩
      · have hb' := (hact b).1 hb
        show φ _ ≤ φ _
        rw [← (hag b b.isLt hb').1, ← (hag a haK haa).1]
        exact hφ.monotone (hspec b b.isLt hb').1
      · have hb' := (hact b).1 hb
        have he : S.r.lo.val (rt b) = S.r.lo.val (rt a) := by
          rw [(hag b b.isLt hb').1, (hag a haK haa).1]
          exact hφ.injective hbe
        exact Fin.le_def.2 ((hspec b b.isLt hb').2 he)
    have hLLu := (RR.lowLeader_iff t ⟨a, haK⟩).2 hLL
    cases he : leadScan (fun i => (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt i))
        (fun _ => true) K with
    | none =>
      exfalso
      have h1 := (leadScan_spec _ _ K).1 he 0 hK
      simp at h1
    | some a' =>
      obtain ⟨ha'K, _, hspec'⟩ := (leadScan_spec _ _ K).2 a' he
      have haa' : a' = a := by
        have h1 := hspec' a haK rfl
        have h2 : φ ((rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt a'))
            ≤ φ ((rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt a)) :=
          hLLu.2.1 ⟨a', ha'K⟩ (mem_univ _)
        have h3 := hφ.le_iff_le.1 h2
        have heq := le_antisymm h1.1 h3
        have h4 : a' ≤ a := h1.2 heq
        have h5 : (⟨a, haK⟩ : Fin K) ≤ ⟨a', ha'K⟩ :=
          hLLu.2.2 ⟨a', ha'K⟩ (mem_univ _) (by show φ _ = φ _; rw [heq])
        have h5' : a ≤ a' := Fin.le_def.1 h5
        omega
      have hbits : stopScan φ ε (fun i => S.r.hi.val (rt i)) (S.r.lo.val (rt a)) a S.act K
          = stopScan φ ε (fun i => (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val (rt i))
              ((rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt a)) a (fun _ => true) K := by
        rw [Bool.eq_iff_iff, stopScan_spec, stopScan_spec]
        constructor
        · intro hst i hi _ hia
          have MSa : MarginalStops (actSet K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t)
              (refL φ rt u G0 lo0 hi0 K t) (refU φ rt u G0 lo0 hi0 K t) ε ⟨a, haK⟩ := by
            refine ⟨hLL, fun b hb hba => ?_⟩
            have hb' := (hact b).1 hb
            have h1 := hst b b.isLt hb' (fun e => hba (Fin.ext e))
            show φ _ - φ _ ≤ ε
            rw [← (hag b b.isLt hb').2, ← (hag a haK haa).1]
            exact h1
          exact ((RR.stops_iff hε t ⟨a, haK⟩).2 MSa).2 ⟨i, hi⟩ (mem_univ _)
            (fun e => hia (congrArg Fin.val e))
        · intro hst i hi hai hia
          have MSu : MarginalStops univ (refL φ rt u G0 lo0 hi0 K t)
              (refU φ rt u G0 lo0 hi0 K t) ε ⟨a, haK⟩ :=
            ⟨hLLu, fun b _ hba => hst b b.isLt rfl (fun e => hba (Fin.ext e))⟩
          have h1 := ((RR.stops_iff hε t ⟨a, haK⟩).1 MSu).2 ⟨i, hi⟩
            ((hact ⟨i, hi⟩).2 hai) (fun e => hia (congrArg Fin.val e))
          show φ (S.r.hi.val (rt i)) - φ (S.r.lo.val (rt a)) ≤ ε
          rw [(hag i hi hai).2, (hag a haK haa).1]
          exact h1
      unfold qOut
      rw [hs, he, haa']
      show (some a, stopScan φ ε _ _ a S.act K) = (some a, stopScan φ ε _ _ a _ K)
      rw [hbits]

end Coupling

/-! ## Work of the Graph-Selective engine -/

section Cost

variable {α : Type*} [LinearOrder α] [OrderBot α]

omit [OrderBot α] in
lemma retireOne_G (e : ℕ × ℕ) (s : RState α) (hG : s.G.WF) :
    (retireOne e s).1.G.WF ∧ (retireOne e s).1.G.N = s.G.N ∧
    ∀ p, ((retireOne e s).1.G.children p).Sublist (s.G.children p) := by
  unfold retireOne
  split_ifs
  · exact ⟨retireDag_wf hG _ _, rfl, fun p => retire_children_sublist _ _ _ p⟩
  · exact ⟨hG, rfl, fun p => List.Sublist.refl _⟩

omit [OrderBot α] in
lemma retireList_G : ∀ (L : List (ℕ × ℕ)) (s : RState α), s.G.WF →
    (retireList L s).1.G.WF ∧ (retireList L s).1.G.N = s.G.N ∧
    ∀ p, ((retireList L s).1.G.children p).Sublist (s.G.children p) := by
  intro L
  induction L with
  | nil => intro s hG; exact ⟨hG, rfl, fun p => List.Sublist.refl _⟩
  | cons e es ih =>
    intro s hG
    obtain ⟨a1, a2, a3⟩ := retireOne_G e s hG
    obtain ⟨b1, b2, b3⟩ := ih (retireOne e s).1 a1
    exact ⟨b1, b2.trans a2, fun p => (b3 p).trans (a3 p)⟩

omit [OrderBot α] in
/-- Cost of a retirement pass on any well-formed live circuit of degree at most `D`: one
unit per test plus `2⌈log₂ D⌉ + 4` per incidence removed. -/
lemma retireList_cost' (D : ℕ) : ∀ (L : List (ℕ × ℕ)) (s : RState α), s.G.WF →
    (∀ p, (s.G.children p).length ≤ D) →
    (retireList L s).2 + (2 * Nat.clog 2 D + 4) * live (retireList L s).1.G
      ≤ L.length + (2 * Nat.clog 2 D + 4) * live s.G := by
  intro L
  induction L with
  | nil => intro s _ _; simp [retireList]
  | cons e es ih =>
    intro s hG hD
    have h1 := retireOne_cost hG D hD e
    obtain ⟨w, _, sub⟩ := retireOne_G e s hG
    have h2 := ih (retireOne e s).1 w (fun p => ((sub p).length_le).trans (hD p))
    show (retireOne e s).2 + (retireList es (retireOne e s).1).2
        + (2 * Nat.clog 2 D + 4) * live (retireList es (retireOne e s).1).1.G ≤ _
    rw [List.length_cons]
    omega

variable {G0 : Dag} {K : ℕ} {rt : ℕ → ℕ} {elo ehi : ℕ → α}

/-- **Cost of one rollout** of the Graph-Selective engine, with the cells still allocated
as potential: level scheduling, `⌈log₂ D⌉ + 3` per live delivery, two units per retirement
test (the test and the later release examination), `2⌈log₂ D⌉ + 4` per incidence retired,
and two units per cell disposed of by the release cascade. -/
theorem relStep_cost (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D) {s : QS α}
    (cand : RState α → RState α → List (ℕ × ℕ)) (h : CInv G0 K rt s.r s.act elo ehi)
    (u : ℕ × α × α) (hx : u.1 < G0.N) :
    (relStep K rt cand u s).2 + 2 * cells (relStep K rt cand u s).1.r.G
      ≤ 2 * (G0.L + 3)
        + (Nat.clog 2 D + 3) * (vol s.r.G s.r.lo (relStep K rt cand u s).1.r.lo
            + vol s.r.G s.r.hi (relStep K rt cand u s).1.r.hi)
        + 2 * (cand s.r (waveStep u s.r).1).length
        + (2 * Nat.clog 2 D + 4) * (live s.r.G - live (rstep cand u s.r).1.G)
        + 2 * cells s.r.G := by
  obtain ⟨_, _, _, l4⟩ := wave_spec h.wf u.1 u.2.1 s.r.lo (h.nEq ▸ hx) h.invLo
  obtain ⟨_, _, _, u4⟩ := wave_spec h.wf u.1 u.2.2 s.r.hi (h.nEq ▸ hx) h.invHi
  have hDs : ∀ p, (s.r.G.children p).length ≤ D :=
    fun p => ((h.csub p).length_le).trans (hD p)
  have bl := (chgSum_bounds D hDs s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1).2
  have bh := (chgSum_bounds D hDs s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1).2
  obtain ⟨e1, e2, e3, _, e5⟩ := rstep_endpoints cand u s.r
  have hwfw : (waveStep u s.r).1.G.WF := h.wf
  obtain ⟨g1, _, _⟩ := retireList_G (cand s.r (waveStep u s.r).1) (waveStep u s.r).1 hwfw
  have rc : (retireList (cand s.r (waveStep u s.r).1) (waveStep u s.r).1).2
      + (2 * Nat.clog 2 D + 4) * live (rstep cand u s.r).1.G
      ≤ (cand s.r (waveStep u s.r).1).length + (2 * Nat.clog 2 D + 4) * live s.r.G :=
    retireList_cost' D (cand s.r (waveStep u s.r).1) (waveStep u s.r).1 hwfw hDs
  have hle := rstep_live_le cand u s.r
  have hsub : (2 * Nat.clog 2 D + 4) * (live s.r.G - live (rstep cand u s.r).1.G)
      + (2 * Nat.clog 2 D + 4) * live (rstep cand u s.r).1.G
      = (2 * Nat.clog 2 D + 4) * live s.r.G := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hle]
  obtain ⟨_, _, _, _, _, _, r7⟩ := releaseLoop_spec (protOf K rt s.act)
    (relFuel (rstep cand u s.r).1.G ((cand s.r (waveStep u s.r).1).map Prod.snd))
    ((cand s.r (waveStep u s.r).1).map Prod.snd) (rstep cand u s.r).1.G g1
  rw [List.length_map] at r7
  have hcells : cells (rstep cand u s.r).1.G ≤ cells s.r.G := cells_le_of_sub e3 e5
  have hcost : (relStep K rt cand u s).2
      = (wave s.r.G u.1 u.2.1 s.r.lo).2 + (wave s.r.G u.1 u.2.2 s.r.hi).2
        + (retireList (cand s.r (waveStep u s.r).1) (waveStep u s.r).1).2
        + (releaseLoop (protOf K rt s.act)
            (relFuel (rstep cand u s.r).1.G ((cand s.r (waveStep u s.r).1).map Prod.snd))
            ((cand s.r (waveStep u s.r).1).map Prod.snd) (rstep cand u s.r).1.G).2 := rfl
  have elo' : (relStep K rt cand u s).1.r.lo = (wave s.r.G u.1 u.2.1 s.r.lo).1 := e1
  have ehi' : (relStep K rt cand u s).1.r.hi = (wave s.r.G u.1 u.2.2 s.r.hi).1 := e2
  have hGout : (relStep K rt cand u s).1.r.G = (releaseLoop (protOf K rt s.act)
      (relFuel (rstep cand u s.r).1.G ((cand s.r (waveStep u s.r).1).map Prod.snd))
      ((cand s.r (waveStep u s.r).1).map Prod.snd) (rstep cand u s.r).1.G).1 := rfl
  rw [hcost, elo', ehi', hGout]
  have hy := Nat.mul_add (Nat.clog 2 D + 3) (vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1)
    (vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1)
  have hL : s.r.G.L = G0.L := h.lEq
  omega

omit [OrderBot α] in
lemma qRetire_cost {s : QS α} (hG : s.r.G.WF) :
    (qRetire K rt s).1.r.G.WF ∧ (qRetire K rt s).1.r.G.N = s.r.G.N ∧
    (∀ p, ((qRetire K rt s).1.r.G.children p).Sublist (s.r.G.children p)) ∧
    (qRetire K rt s).2 + 2 * cells (qRetire K rt s).1.r.G ≤ 3 * K + 2 * cells s.r.G := by
  unfold qRetire
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none =>
    exact ⟨hG, rfl, fun _ => List.Sublist.refl _, by show K + 2 * cells s.r.G ≤ _; omega⟩
  | some a =>
    obtain ⟨a1, a2, _, _, a5, _, a7⟩ := releaseLoop_spec
      (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
      (relFuel s.r.G
        (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
      (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act) s.r.G hG
    have hl := retiredRoots_length K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act
    refine ⟨a1, a2, a5, ?_⟩
    show K + K + (releaseLoop _ _ _ s.r.G).2 + 2 * cells (releaseLoop _ _ _ s.r.G).1
      ≤ 3 * K + 2 * cells s.r.G
    omega

variable {cand : RState α → RState α → List (ℕ × ℕ)} {u : ℕ → ℕ × α × α} {q : ℕ → Bool}
  {lo0 hi0 : EState α} {act0 : ℕ → Bool}

/-- Number of retirement tests of rollout `t + 1`. -/
def testsF (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ))
    (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : QS α) (t : ℕ) : ℕ :=
  (cand (preF K rt cand u q s0 t).r
    (waveStep (u (t + 1)) (preF K rt cand u q s0 t).r).1).length

/-- Per-step cost bound with the cells as potential. -/
theorem costF_step (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (t : ℕ) :
    costF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * cells (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.G
      ≤ (if q t = true then 4 * K else 0) + 2 * (G0.L + 3)
        + (Nat.clog 2 D + 3) * volF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * testsF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + (2 * Nat.clog 2 D + 4) * retF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * cells (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G := by
  have hpre := preF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0) hG h0 hn t
  have hrun := runF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0) hG h0 hn t
  have rs : (relStep K rt cand (u (t + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2
      + 2 * cells (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.G
      ≤ 2 * (G0.L + 3)
        + (Nat.clog 2 D + 3) * volF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * testsF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + (2 * Nat.clog 2 D + 4) * retF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * cells (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G :=
    relStep_cost D hD cand hpre (u (t + 1)) (hn t).1
  have hq : (if q t = true then K + (qRetire K rt
        (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2 else 0)
      + 2 * cells (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G
      ≤ (if q t = true then 4 * K else 0)
        + 2 * cells (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G := by
    unfold preF
    by_cases hqt : q t = true
    · rw [ite_eq_left hqt, ite_eq_left hqt, ite_eq_left hqt]
      have := (qRetire_cost (K := K) (rt := rt) hrun.wf).2.2.2
      omega
    · rw [ite_eq_right hqt, ite_eq_right hqt, ite_eq_right hqt]
  unfold costF
  omega

/-- **Total work of the Graph-Selective engine** over `T` rollouts with queries at the
times `t < T` with `q t`: -/
theorem live_work (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (T : ℕ) :
    ∑ t ∈ range T, costF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * cells (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r.G
      ≤ ((range T).filter (fun t => q t = true)).card * (4 * K) + 2 * T * (G0.L + 3)
        + (Nat.clog 2 D + 3) * ∑ t ∈ range T, volF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * ∑ t ∈ range T, testsF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + (2 * Nat.clog 2 D + 4)
          * ∑ t ∈ range T, retF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * cells G0 := by
  have hQ : ((range T).filter (fun t => q t = true)).card * (4 * K)
      = ∑ t ∈ range T, (if q t = true then 4 * K else 0) := by
    rw [← sum_filter, sum_const, smul_eq_mul]
  rw [hQ]
  clear hQ
  induction T with
  | zero =>
    show _ + 2 * cells G0 ≤ _
    simp
  | succ T ih =>
    have hstep := costF_step (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0)
      hG D hD h0 hn T
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
    have e1 := Nat.mul_add (Nat.clog 2 D + 3)
      (∑ t ∈ range T, volF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)
      (volF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T)
    have e2 := Nat.mul_add (2 * Nat.clog 2 D + 4)
      (∑ t ∈ range T, retF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)
      (retF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T)
    have e3 : 2 * (T + 1) * (G0.L + 3) = 2 * T * (G0.L + 3) + 2 * (G0.L + 3) := by ring
    rw [e3]
    omega

/-- Every incidence is retired at most once: the retirements of a run number at most the
incidences of the circuit. -/
theorem retF_sum_le (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (T : ℕ) :
    ∑ t ∈ range T, retF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + live (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r.G ≤ live G0 := by
  induction T with
  | zero => show _ + live G0 ≤ _; simp
  | succ T ih =>
    have hpre := preF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0)
      hG h0 hn T
    have hrun := runF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0)
      hG h0 hn T
    have h1 : live (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r.G
        ≤ live (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r.G := by
      unfold preF
      split_ifs
      · obtain ⟨_, b2, b3, _⟩ := qRetire_cost (K := K) (rt := rt) hrun.wf
        exact live_le_of_sub b2 b3
      · exact le_rfl
    have h2 := rstep_live_le cand (u (T + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r
    have hwfw : (waveStep (u (T + 1))
        (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r).1.G.WF := hpre.wf
    obtain ⟨g1, _, _⟩ := retireList_G (cand (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r
      (waveStep (u (T + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r).1) _ hwfw
    obtain ⟨_, r2, _, _, r5, _, _⟩ := releaseLoop_spec
      (protOf K rt (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).act)
      (relFuel (rstep cand (u (T + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r).1.G
        ((cand (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r
          (waveStep (u (T + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r).1).map
          Prod.snd))
      ((cand (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r
        (waveStep (u (T + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r).1).map Prod.snd)
      (rstep cand (u (T + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r).1.G g1
    have h3 : live (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (T + 1)).r.G
        ≤ live (rstep cand (u (T + 1))
            (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ T).r).1.G := live_le_of_sub r2 r5
    rw [sum_range_succ]
    unfold retF at ih ⊢
    omega

end Cost

/-! ## `prop:uct-coupling` and `eq:ram-work-bounds` -/

section Final

variable {α : Type*} [LinearOrder α] [OrderBot α]
variable {G0 : Dag} {K : ℕ} {rt : ℕ → ℕ} {u : ℕ → ℕ × α × α} {q : ℕ → Bool}
  {lo0 hi0 : EState α} {act0 : ℕ → Bool}

omit [OrderBot α] in
lemma vol_le_ref {G : Dag} (hN : G.N = G0.N)
    (psub : ∀ c, (G.parents c).Sublist (G0.parents c)) (a b a0 b0 : EState α)
    (hnd : ∀ g, G.parents g ≠ [] → a.val g = a0.val g ∧ b.val g = b0.val g) :
    vol G a b ≤ vol G0 a0 b0 := by
  rw [vol_eq_sum, vol_eq_sum, hN]
  apply sum_le_sum
  intro g _
  by_cases hp : G.parents g = []
  · rw [hp]; simp
  · obtain ⟨h1, h2⟩ := hnd g hp
    rw [h1, h2]
    exact Nat.mul_le_mul_left _ (psub g).length_le

/-- Live deliveries are at most full-incidence deliveries: `S ≤ S₀`, rollout by rollout,
also with release and root retirement. -/
theorem volF_le_eager {cand : RState α → RState α → List (ℕ × ℕ)} (hG : G0.WF)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (t : ℕ) :
    volF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t ≤ eagerPlus G0 u lo0 hi0 t := by
  have hpre := preF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0) hG h0 hn t
  obtain ⟨_, f2, f3, f4, f5, f6⟩ := ref_facts hG h0 hn t
  obtain ⟨f1', _⟩ := ref_facts hG h0 hn (t + 1)
  have hw := hpre.wave f1' (u (t + 1)) f2 f3 f4 f5 f6
  obtain ⟨e1, e2, _⟩ := rstep_endpoints cand (u (t + 1))
    (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r
  have elo : (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.lo
      = (waveStep (u (t + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r).1.lo := e1
  have ehi : (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.hi
      = (waveStep (u (t + 1)) (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r).1.hi := e2
  obtain ⟨_, _, a3, a4⟩ := live_eq_eager (cand := noCand) hG h0 hn t
  obtain ⟨_, _, b3, b4⟩ := live_eq_eager (cand := noCand) hG h0 hn (t + 1)
  have hnd : ∀ g, (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G.parents g ≠ [] →
      ¬ Dead G0 (preF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G g := by
    intro g hg
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hg
    exact hpre.live_child p g ((hpre.wf.parents_iff g p).1 hp)
  unfold volF eagerPlus
  rw [elo, ehi]
  apply Nat.add_le_add
  · exact vol_le_ref hpre.nEq hpre.psub _ _ _ _ (fun g hg =>
      ⟨((hpre.agree g (hnd g hg)).1).trans (a3 g), ((hw.agree g (hnd g hg)).1).trans (b3 g)⟩)
  · exact vol_le_ref hpre.nEq hpre.psub _ _ _ _ (fun g hg =>
      ⟨((hpre.agree g (hnd g hg)).2).trans (a4 g), ((hw.agree g (hnd g hg)).2).trans (b4 g)⟩)

/-- The delivery policy tests at most as many incidences as the waves delivered along. -/
lemma tests_le_vol (s0 : QS α) (t : ℕ) :
    testsF K rt delivCand u q s0 t ≤ volF K rt delivCand u q s0 t := by
  have h := delivCand_length (preF K rt delivCand u q s0 t).r
    (waveStep (u (t + 1)) (preF K rt delivCand u q s0 t).r).1
  obtain ⟨e1, e2, _⟩ := rstep_endpoints delivCand (u (t + 1)) (preF K rt delivCand u q s0 t).r
  have elo : (runF K rt delivCand u q s0 (t + 1)).r.lo
      = (waveStep (u (t + 1)) (preF K rt delivCand u q s0 t).r).1.lo := e1
  have ehi : (runF K rt delivCand u q s0 (t + 1)).r.hi
      = (waveStep (u (t + 1)) (preF K rt delivCand u q s0 t).r).1.hi := e2
  unfold testsF volF
  rw [elo, ehi]
  exact h

/-- Work of the eager waves: `S₀ ≤ Σ cost ≤ 2T(L + 3) + (⌈log₂ D⌉ + 3) S₀`. -/
theorem eager_work (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (T : ℕ) :
    (∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t ≤ ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t) ∧
    (∑ t ∈ range T, eagerCost G0 u lo0 hi0 t
      ≤ 2 * T * (G0.L + 3) + (Nat.clog 2 D + 3) * ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t) := by
  have hstep : ∀ t, eagerPlus G0 u lo0 hi0 t ≤ eagerCost G0 u lo0 hi0 t ∧
      eagerCost G0 u lo0 hi0 t
        ≤ 2 * (G0.L + 3) + (Nat.clog 2 D + 3) * eagerPlus G0 u lo0 hi0 t := by
    intro t
    obtain ⟨i1, i2, _, _⟩ := live_eq_eager (cand := noCand) hG h0 hn t
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
  refine ⟨sum_le_sum (fun t _ => (hstep t).1), ?_⟩
  calc ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t
      ≤ ∑ t ∈ range T, (2 * (G0.L + 3) + (Nat.clog 2 D + 3) * eagerPlus G0 u lo0 hi0 t) :=
        sum_le_sum (fun t _ => (hstep t).2)
    _ = 2 * T * (G0.L + 3) + (Nat.clog 2 D + 3) * ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t := by
        rw [sum_add_distrib, sum_const, card_range, ← mul_sum, smul_eq_mul]
        ring

/-- **`prop:uct-coupling` with `eq:ram-work-bounds`, for general DAGs, with retirement of
internal incidences, release of orphaned gates, root-action retirement and the
leader-and-stop query.**

Fixed coupled trajectory: terminal updates `u` (nested, as in `DagRetire.NestedRun` for the
engine without retirement), `T` rollouts, root queries at the times `t < T` with `q t`
(`Q` of them), `K ≥ 1` root actions with gates `rt i`, all gate degrees at most `D`,
initialisation work `P`.  Graph-Selective is `runF` with the delivery retirement policy;
Graph-Eager is `CostEngines.runState` on the original circuit with a query that scans all
`K` actions (leader scan and stop scan, `2K` units).  With `S₀ = Σ eagerPlus`,
`S = Σ volF` (live deliveries) and `R = Σ retF` (incidences retired):

1. at every time both engines return the same leader and the same stopping bit;
2. the gate of every active root action stores the eager interval;
3. `P + S₀ ≤ W_eager ≤ P + 2T(L + 3) + 2QK + (⌈log₂ D⌉ + 3) S₀`;
4. `W_live ≤ P + 2T(L + 3) + 4QK + (⌈log₂ D⌉ + 5) S + (2⌈log₂ D⌉ + 4) R + 2(|V| + |E|)`;
5. `S ≤ S₀` and `R ≤ |E|`.

`W_live` sums the computed costs of the waves, retirement passes, release cascades and
queries; `2(|V| + |E|)` bounds all disposal by release.  The term `2T(L + 3)` is the level
scheduling of the waves, where the manuscript has `T`. -/
theorem ram_work_bounds_final (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩)
    (hK : 0 < K) (rt : ℕ → ℕ) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (q : ℕ → Bool) (T P : ℕ) :
    (∀ t, qOut φ ε K
        (fun i => (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.lo.val (rt i))
        (fun i => (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.hi.val (rt i))
        (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act
      = qOut φ ε K (fun i => (runState G0 u (lo0, hi0) t).1.val (rt i))
        (fun i => (runState G0 u (lo0, hi0) t).2.val (rt i)) (fun _ => true)) ∧
    (∀ t i, i < K → (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act i = true →
      (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.lo.val (rt i)
        = (runState G0 u (lo0, hi0) t).1.val (rt i) ∧
      (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.hi.val (rt i)
        = (runState G0 u (lo0, hi0) t).2.val (rt i)) ∧
    (P + ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t
      ≤ P + ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t
        + ((range T).filter (fun t => q t = true)).card * (2 * K)) ∧
    (P + ∑ t ∈ range T, eagerCost G0 u lo0 hi0 t
        + ((range T).filter (fun t => q t = true)).card * (2 * K)
      ≤ P + 2 * T * (G0.L + 3) + ((range T).filter (fun t => q t = true)).card * (2 * K)
        + (Nat.clog 2 D + 3) * ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t) ∧
    (P + ∑ t ∈ range T, costF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
      ≤ P + 2 * T * (G0.L + 3) + ((range T).filter (fun t => q t = true)).card * (4 * K)
        + (Nat.clog 2 D + 5)
          * ∑ t ∈ range T, volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
        + (2 * Nat.clog 2 D + 4)
          * ∑ t ∈ range T, retF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
        + 2 * (G0.N + live G0)) ∧
    (∑ t ∈ range T, volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
      ≤ ∑ t ∈ range T, eagerPlus G0 u lo0 hi0 t) ∧
    (∑ t ∈ range T, retF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t ≤ live G0) := by
  obtain ⟨w1, w2⟩ := eager_work hG D hD h0 hn T
  have hlw := live_work (K := K) (rt := rt) (cand := delivCand) (q := q)
    (act0 := fun _ => true) hG D hD h0 hn T
  have hret := retF_sum_le (K := K) (rt := rt) (cand := delivCand) (q := q)
    (act0 := fun _ => true) hG h0 hn T
  have htests : ∑ t ∈ range T, testsF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
      ≤ ∑ t ∈ range T, volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t :=
    sum_le_sum (fun t _ => tests_le_vol _ t)
  have hcells := cells_le G0
  refine ⟨fun t => ?_, fun t i hi ha => ?_, by omega, by omega, ?_,
    sum_le_sum (fun t _ => volF_le_eager hG h0 hn t), by omega⟩
  · obtain ⟨_, _, a3, a4⟩ := live_eq_eager (cand := noCand) hG h0 hn t
    have e1 : (fun i => (runState G0 u (lo0, hi0) t).1.val (rt i))
        = fun i => (rrun noCand u ⟨G0, lo0, hi0⟩ t).lo.val (rt i) :=
      funext (fun i => (a3 (rt i)).symm)
    have e2 : (fun i => (runState G0 u (lo0, hi0) t).2.val (rt i))
        = fun i => (rrun noCand u ⟨G0, lo0, hi0⟩ t).hi.val (rt i) :=
      funext (fun i => (a4 (rt i)).symm)
    rw [e1, e2]
    exact query_coupling hG h0 hn hK φ hφ ε hε t
  · obtain ⟨_, _, a3, a4⟩ := live_eq_eager (cand := noCand) hG h0 hn t
    have hinv := runF_inv (K := K) (rt := rt) (cand := delivCand) (q := q)
      (act0 := fun _ => true) hG h0 hn t
    have hag := hinv.agree (rt i) (hinv.prot i hi ha)
    exact ⟨hag.1.trans (a3 _), hag.2.trans (a4 _)⟩
  · have e5 : (Nat.clog 2 D + 5)
          * ∑ t ∈ range T, volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
        = (Nat.clog 2 D + 3)
            * ∑ t ∈ range T, volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
          + 2 * ∑ t ∈ range T, volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t := by
      ring
    omega

end Final

/-! ## The Graph-Selective engine on implemented heaps -/

section Impl

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The release cascade on implemented heaps: as `releaseLoop`, and the two heaps of a
released gate are discarded (replaced by the empty heap; the entries are charged as the
unlinks, one unit each). -/
def releaseLoopH (prot : ℕ → Bool) : ℕ → List ℕ → HRState α → HRState α × ℕ
  | 0, _, s => (s, 0)
  | _ + 1, [], s => (s, 0)
  | f + 1, g :: st, s =>
    if s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false then
      ((releaseLoopH prot f (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩).1,
       (releaseLoopH prot f (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩).2 + 1 + (s.G.children g).length)
    else ((releaseLoopH prot f st s).1, (releaseLoopH prot f st s).2 + 1)

lemma simE_release {G : Dag} {hs : HEState α} {s : EState α} (h : SimE G hs s) (g : ℕ) :
    SimE (releaseDag G g) ⟨hs.val, Function.update hs.hp g Heap.empty⟩ s := by
  refine ⟨h.val, fun p => ?_⟩
  show Rep (Function.update hs.hp g Heap.empty p)
    (if p = g then [] else G.children p).toFinset (s.key p)
    (if p = g then [] else G.children p).length
  by_cases hp : p = g
  · rw [hp, Function.update_self, ite_eq_left rfl]
    exact ⟨Heap.empty_inv, le_rfl, fun _ => rfl⟩
  · rw [Function.update_of_ne hp, ite_eq_right hp]
    exact h.hp p

theorem releaseLoopH_sim (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (hs : HRState α)
    (s : RState α), SimR hs s →
    SimR (releaseLoopH prot f st hs).1 ⟨(releaseLoop prot f st s.G).1, s.lo, s.hi⟩ ∧
    (releaseLoopH prot f st hs).2 = (releaseLoop prot f st s.G).2 := by
  intro f
  induction f with
  | zero => intro st hs s h; exact ⟨h, rfl⟩
  | succ f ih =>
    intro st hs s h
    cases st with
    | nil => exact ⟨h, rfl⟩
    | cons g st =>
      obtain ⟨hG, hlo, hhi⟩ := h
      obtain ⟨G, lo, hi⟩ := hs
      simp only at hG hlo hhi
      subst hG
      rw [releaseLoopH, RetireFinal.releaseLoop]
      by_cases hc : s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc, ite_eq_left hc]
        have hsim : SimR (⟨releaseDag s.G g, ⟨lo.val, Function.update lo.hp g Heap.empty⟩,
            ⟨hi.val, Function.update hi.hp g Heap.empty⟩⟩ : HRState α)
            ⟨releaseDag s.G g, s.lo, s.hi⟩ :=
          ⟨rfl, simE_release hlo g, simE_release hhi g⟩
        obtain ⟨i1, i2⟩ := ih (s.G.children g ++ st) _ _ hsim
        exact ⟨i1, by show _ + 1 + _ = _ + 1 + _; rw [i2]⟩
      · rw [ite_eq_right hc, ite_eq_right hc]
        obtain ⟨i1, i2⟩ := ih st ⟨s.G, lo, hi⟩ s ⟨rfl, hlo, hhi⟩
        exact ⟨i1, by show _ + 1 = _ + 1; rw [i2]⟩

/-- State of the Graph-Selective engine on implemented heaps. -/
structure HQS (α : Type*) where
  r : HRState α
  act : ℕ → Bool

/-- The implemented state represents the abstract state. -/
structure SimQ (hs : HQS α) (s : QS α) : Prop where
  r : SimR hs.r s.r
  act : hs.act = s.act

/-- One rollout on implemented heaps: `EngineFinal.rstepH`, then the release cascade. -/
def relStepH (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ × α × α) (s : HQS α) :
    HQS α × ℕ :=
  (⟨(releaseLoopH (protOf K rt s.act)
        (relFuel (rstepH candV u s.r).1.G
          ((candV s.r.G s.r.lo.val s.r.hi.val (waveStepH u s.r).1.lo.val
            (waveStepH u s.r).1.hi.val).map Prod.snd))
        ((candV s.r.G s.r.lo.val s.r.hi.val (waveStepH u s.r).1.lo.val
          (waveStepH u s.r).1.hi.val).map Prod.snd) (rstepH candV u s.r).1).1, s.act⟩,
   (rstepH candV u s.r).2 + (releaseLoopH (protOf K rt s.act)
        (relFuel (rstepH candV u s.r).1.G
          ((candV s.r.G s.r.lo.val s.r.hi.val (waveStepH u s.r).1.lo.val
            (waveStepH u s.r).1.hi.val).map Prod.snd))
        ((candV s.r.G s.r.lo.val s.r.hi.val (waveStepH u s.r).1.lo.val
          (waveStepH u s.r).1.hi.val).map Prod.snd) (rstepH candV u s.r).1).2)

theorem relStepH_sim (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ × α × α) {hs : HQS α}
    {s : QS α} (h : SimQ hs s) :
    SimQ (relStepH K rt candV u hs).1 (relStep K rt (liftCand candV) u s).1 ∧
    (relStepH K rt candV u hs).2 ≤ 2 * (relStep K rt (liftCand candV) u s).2 := by
  obtain ⟨hr, hact⟩ := h
  obtain ⟨w1, _⟩ := waveStepH_sim hr u
  obtain ⟨r1, r2⟩ := rstepH_sim candV hr u
  have hc : candV hs.r.G hs.r.lo.val hs.r.hi.val (waveStepH u hs.r).1.lo.val
      (waveStepH u hs.r).1.hi.val = liftCand candV s.r (waveStep u s.r).1 := by
    unfold liftCand
    rw [hr.G, hr.lo.val, hr.hi.val, w1.lo.val, w1.hi.val]
  have hG1 : (rstepH candV u hs.r).1.G = (rstep (liftCand candV) u s.r).1.G := r1.G
  obtain ⟨l1, l2⟩ := releaseLoopH_sim (protOf K rt s.act)
    (relFuel (rstep (liftCand candV) u s.r).1.G
      ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd))
    ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd) _ _ r1
  unfold relStepH
  rw [hc, hG1, hact]
  refine ⟨⟨l1, rfl⟩, ?_⟩
  show (rstepH candV u hs.r).2 + (releaseLoopH _ _ _ (rstepH candV u hs.r).1).2
    ≤ 2 * ((rstep (liftCand candV) u s.r).2
      + (releaseLoop _ _ _ (rstep (liftCand candV) u s.r).1.G).2)
  rw [l2]
  omega

/-- Root retirement at a query, on implemented heaps. -/
def qRetireH (K : ℕ) (rt : ℕ → ℕ) (s : HQS α) : HQS α × ℕ :=
  (leadScan (fun i => s.r.lo.val (rt i)) s.act K).elim (s, K)
    (fun a =>
      (⟨(releaseLoopH
            (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r).1,
        deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act⟩,
       K + K + (releaseLoopH
            (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r).2))

theorem qRetireH_sim (K : ℕ) (rt : ℕ → ℕ) {hs : HQS α} {s : QS α} (h : SimQ hs s) :
    SimQ (qRetireH K rt hs).1 (qRetire K rt s).1 ∧
    (qRetireH K rt hs).2 = (qRetire K rt s).2 := by
  obtain ⟨hr, hact⟩ := h
  have hl : hs.r.lo.val = s.r.lo.val := hr.lo.val
  have hh : hs.r.hi.val = s.r.hi.val := hr.hi.val
  unfold qRetireH qRetire
  rw [hl, hh, hact, hr.G]
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => exact ⟨⟨hr, hact⟩, rfl⟩
  | some a =>
    obtain ⟨l1, l2⟩ := releaseLoopH_sim
      (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
      (relFuel s.r.G
        (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
      (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act) hs.r s.r hr
    exact ⟨⟨l1, rfl⟩, by show K + K + _ = K + K + _; rw [l2]⟩

variable (K : ℕ) (rt : ℕ → ℕ)

/-- State of the implemented Graph-Selective engine after `t` rollouts. -/
def runH (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : HQS α) : ℕ → HQS α
  | 0 => s0
  | t + 1 => (relStepH K rt candV (u (t + 1))
      (if q t = true then (qRetireH K rt (runH candV u q s0 t)).1 else runH candV u q s0 t)).1

/-- Computed cost of the query of time `t` (if any) and of rollout `t + 1` on implemented
heaps. -/
def costH (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : HQS α) (t : ℕ) : ℕ :=
  (if q t = true then K + (qRetireH K rt (runH K rt candV u q s0 t)).2 else 0)
    + (relStepH K rt candV (u (t + 1))
        (if q t = true then (qRetireH K rt (runH K rt candV u q s0 t)).1
          else runH K rt candV u q s0 t)).2

variable {K rt}

/-- **Simulation.**  The implemented Graph-Selective engine simulates `runF` at every
time (same live circuit, same stored values, same activity flags, heaps storing the keys
of the live children), and every step costs at most twice the charged cost. -/
theorem runH_sim (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) {hs0 : HQS α}
    {s0 : QS α} (h : SimQ hs0 s0) : ∀ t,
    SimQ (runH K rt candV u q hs0 t) (runF K rt (liftCand candV) u q s0 t) ∧
    costH K rt candV u q hs0 t ≤ 2 * costF K rt (liftCand candV) u q s0 t := by
  have hs : ∀ t, SimQ (runH K rt candV u q hs0 t) (runF K rt (liftCand candV) u q s0 t) := by
    intro t
    induction t with
    | zero => exact h
    | succ t ih =>
      show SimQ (relStepH K rt candV (u (t + 1)) _).1 (relStep K rt (liftCand candV) (u (t + 1)) _).1
      by_cases hq : q t = true
      · rw [ite_eq_left hq, ite_eq_left hq]
        exact (relStepH_sim K rt candV (u (t + 1)) (qRetireH_sim K rt ih).1).1
      · rw [ite_eq_right hq, ite_eq_right hq]
        exact (relStepH_sim K rt candV (u (t + 1)) ih).1
  intro t
  refine ⟨hs t, ?_⟩
  unfold costH costF preF
  by_cases hq : q t = true
  · rw [ite_eq_left hq, ite_eq_left hq, ite_eq_left hq, ite_eq_left hq]
    obtain ⟨a1, a2⟩ := qRetireH_sim K rt (hs t)
    have := (relStepH_sim K rt candV (u (t + 1)) a1).2
    omega
  · rw [ite_eq_right hq, ite_eq_right hq, ite_eq_right hq, ite_eq_right hq]
    have := (relStepH_sim K rt candV (u (t + 1)) (hs t)).2
    omega

/-- **`prop:uct-coupling` / `eq:ram-work-bounds` for the engine on implemented heaps.**
Under the hypotheses of `ram_work_bounds_final`, for the Graph-Selective engine in which
all heap operations are executed by `HeapImpl` (`runH`, started from any implemented state
representing the initial state):

* its leader-and-stop output equals that of the eager engine at every time;
* its computed work satisfies
  `W ≤ P + 2 (2T(L + 3) + 4QK + (⌈log₂ D⌉ + 5) S + (2⌈log₂ D⌉ + 4) R + 2(|V| + |E|))`. -/
theorem ram_work_bounds_impl {G0 : Dag} {u : ℕ → ℕ × α × α} {lo0 hi0 : EState α}
    (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (q : ℕ → Bool) (T P : ℕ) (hr0 : HRState α) (hsim : SimR hr0 ⟨G0, lo0, hi0⟩) :
    (∀ t, qOut φ ε K
        (fun i => (runH K rt delivV u q ⟨hr0, fun _ => true⟩ t).r.lo.val (rt i))
        (fun i => (runH K rt delivV u q ⟨hr0, fun _ => true⟩ t).r.hi.val (rt i))
        (runH K rt delivV u q ⟨hr0, fun _ => true⟩ t).act
      = qOut φ ε K (fun i => (runState G0 u (lo0, hi0) t).1.val (rt i))
        (fun i => (runState G0 u (lo0, hi0) t).2.val (rt i)) (fun _ => true)) ∧
    (P + ∑ t ∈ range T, costH K rt delivV u q ⟨hr0, fun _ => true⟩ t
      ≤ P + 2 * (2 * T * (G0.L + 3) + ((range T).filter (fun t => q t = true)).card * (4 * K)
        + (Nat.clog 2 D + 5)
          * ∑ t ∈ range T, volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
        + (2 * Nat.clog 2 D + 4)
          * ∑ t ∈ range T, retF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
        + 2 * (G0.N + live G0))) := by
  have hS := runH_sim (K := K) (rt := rt) delivV u q
    (hs0 := ⟨hr0, fun _ => true⟩) (s0 := ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩) ⟨hsim, rfl⟩
  obtain ⟨b1, _, _, _, b5, _, _⟩ := ram_work_bounds_final hG D hD h0 hn hK rt φ hφ ε hε q T 0
  refine ⟨fun t => ?_, ?_⟩
  · obtain ⟨⟨sr, sa⟩, _⟩ := hS t
    have e1 : (runH K rt delivV u q ⟨hr0, fun _ => true⟩ t).r.lo.val
        = (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.lo.val := sr.lo.val
    have e2 : (runH K rt delivV u q ⟨hr0, fun _ => true⟩ t).r.hi.val
        = (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).r.hi.val := sr.hi.val
    have e3 : (runH K rt delivV u q ⟨hr0, fun _ => true⟩ t).act
        = (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t).act := sa
    rw [e1, e2, e3]
    exact b1 t
  · have hsum : ∑ t ∈ range T, costH K rt delivV u q ⟨hr0, fun _ => true⟩ t
        ≤ 2 * ∑ t ∈ range T, costF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t := by
      rw [mul_sum]
      exact sum_le_sum (fun t _ => (hS t).2)
    omega

end Impl

end RetireFinal
end JointRootCert
