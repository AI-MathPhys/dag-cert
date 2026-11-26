/-
Joint Root Certification: the retirement engine on implemented heaps, as an instance of the
lower-bound contract.

Manuscript result covered:

* `prop:representation-cost` (Unified Full-Cost Representation Comparison), as one
  statement `representation_cost_final` / `representation_cost_condition_R`: the upper bound
  `eq:prop-rep-upper`, the lower bound `Ω(P + S⁻)`, and condition (R).

## What is new here

* `rstepH`, `rrunH`: the engine of `DagRetire.lean` (backup waves, then a retirement pass)
  in which EVERY heap operation is executed by the implemented indexed heap of
  `HeapImpl.lean`: key updates of the waves (`HeapImpl.waveH`), the two heap deletions of a
  retirement (`HeapImpl.delete`), and the insertions of the initialisation pass
  (`initPassH`, by `HeapImpl.insertAll` into empty heaps).
* `rrunH_sim`: the implemented engine simulates `DagRetire.rrun` step by step, and every
  step costs at most twice the charged cost.  `initPassH_sim`: the same for initialisation.
* `stepOps`: the execution of one rollout as a trace of single-cell writes to the key cells
  `(endpoint, (parent, child))`; `rrunH_trace` shows that the trace transforms the key
  memory of the implemented engine (`memH`, read off its heaps) from one rollout to the
  next, that all writes are among the engine's operations (`stepOps_length_le`), and that
  the delivery contract of `DagRetire.contract_lower` holds.  Hence `contract_lower` applies
  to the implemented engine (`engineH_contract_lower`).

## Cost model

As in `HeapImpl.lean` and `DagRetire.lean`.  Heap operations cost what the implemented
sift procedures compute.  Still charged by convention, one unit each: the retirement test,
the two list unlinks of a retirement, reading a heap root, a bucket push or pop, scanning a
level.  A trace operation writes one key cell `(b, (p, c))`: the key stored under handle
`c` in the heap of gate `p` for endpoint `b`.  A heap key update is one such write (and at
least one unit of computed cost); a heap deletion is one such write (the cell is cleared to
`⊥`).  Position-map and array-slot moves inside a heap are not key cells and are not
traced; they only add to the computed cost.
-/
import JointRootCert.DagRetire
import JointRootCert.HeapImpl

namespace JointRootCert
namespace EngineFinal

open Finset CostEngines DagRetire
open HeapImpl (Heap HEState SimE Rep waveH findMax)

/-! ## Heap facts used below -/

section HeapFacts

variable {ι α : Type*} [DecidableEq ι] [LinearOrder α]

/-- A heap storing exactly the handles of `S` has at most `|S|` entries. -/
lemma heap_size_le_card {H : Heap ι α} (hI : H.Inv) (S : Finset ι) (k : ι → α)
    (hS : ∀ h, H.lookup h = if h ∈ S then some (k h) else none) : H.n ≤ S.card := by
  have hmem : ∀ i ∈ range H.n, H.hd i ∈ S := by
    intro i hi
    by_contra hn
    have h1 := hS (H.hd i)
    rw [ite_eq_right hn] at h1
    unfold Heap.lookup at h1
    rw [hI.posOK.fwd i (mem_range.1 hi)] at h1
    simp at h1
  have hinj : Set.InjOn H.hd (range H.n : Finset ℕ) := by
    intro a ha b hb hab
    exact hI.posOK.hd_inj (mem_range.1 (mem_coe.1 ha)) (mem_range.1 (mem_coe.1 hb)) hab
  have := Finset.card_le_card_of_injOn H.hd hmem hinj
  rwa [card_range] at this

/-- Deleting the handle `c` from the heap of a gate with child list `cs` gives the heap of
the child list `cs.filter (· ≠ c)`, at computed cost at most `⌈log₂ |cs|⌉ + 2`. -/
lemma rep_delete {H : Heap ℕ α} {cs : List ℕ} {k : ℕ → α}
    (h : Rep H cs.toFinset k cs.length) {c : ℕ} (hc : c ∈ cs) :
    Rep (HeapImpl.delete H c).1 (cs.filter (· ≠ c)).toFinset k (cs.filter (· ≠ c)).length ∧
    (HeapImpl.delete H c).2 ≤ Nat.clog 2 cs.length + 2 ∧ 1 ≤ (HeapImpl.delete H c).2 := by
  have hlk : H.lookup c ≠ none := by
    rw [h.look c, ite_eq_left (List.mem_toFinset.2 hc)]
    simp
  obtain ⟨d1, _, d3⟩ := HeapImpl.delete_spec h.inv c hlk
  have hlook : ∀ h', (HeapImpl.delete H c).1.lookup h'
      = if h' ∈ (cs.filter (· ≠ c)).toFinset then some (k h') else none := by
    intro h'
    rw [d3 h', h.look h']
    by_cases e : h' = c
    · subst e
      simp
    · by_cases hm : h' ∈ cs
      · simp [e, hm]
      · simp [e, hm]
  refine ⟨⟨d1, ?_, hlook⟩, ?_, ?_⟩
  · exact (heap_size_le_card d1 _ k hlook).trans (List.toFinset_card_le _)
  · exact (HeapImpl.delete_cost H c).trans
      (Nat.add_le_add_right (Nat.clog_mono_right 2 h.size) 2)
  · unfold HeapImpl.delete
    cases H.pos c with
    | none => simp
    | some i =>
      simp only [Option.elim_some, HeapImpl.deleteAt]
      split_ifs
      · exact le_rfl
      · exact Nat.le_add_left _ _
      · exact Nat.le_add_left _ _

/-- A key update costs at least one unit. -/
lemma one_le_updateKey (H : Heap ι α) (h : ι) (x : α) : 1 ≤ (HeapImpl.updateKey H h x).2 := by
  unfold HeapImpl.updateKey
  cases H.pos h with
  | none => simp
  | some i =>
    simp only [Option.elim_some, HeapImpl.updateAt]
    split_ifs
    · exact Nat.le_add_left _ _
    · exact Nat.le_add_left _ _

end HeapFacts

/-! ## The retirement engine on implemented heaps -/

section EngineH

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- State of the interval engine with retirement, with implemented heaps: the live circuit
and, for each endpoint, the stored gate values and one indexed heap per gate. -/
structure HRState (α : Type*) where
  G : Dag
  lo : HEState α
  hi : HEState α

/-- The implemented state represents the abstract state of `DagRetire`. -/
structure SimR (hs : HRState α) (s : RState α) : Prop where
  G : hs.G = s.G
  lo : SimE s.G hs.lo s.lo
  hi : SimE s.G hs.hi s.hi

/-- **Retirement test and retirement of one incidence on implemented heaps**: the test
(1 unit), two heap deletions executed by `HeapImpl.delete` (computed cost), and two list
unlinks (1 unit each). -/
def retireOneH (e : ℕ × ℕ) (s : HRState α) : HRState α × ℕ :=
  if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then
    (⟨retireDag s.G e.1 e.2,
      ⟨s.lo.val, Function.update s.lo.hp e.1 (HeapImpl.delete (s.lo.hp e.1) e.2).1⟩,
      ⟨s.hi.val, Function.update s.hi.hp e.1 (HeapImpl.delete (s.hi.hp e.1) e.2).1⟩⟩,
     (HeapImpl.delete (s.lo.hp e.1) e.2).2 + (HeapImpl.delete (s.hi.hp e.1) e.2).2 + 3)
  else (s, 1)

omit [OrderBot α] in
lemma simE_retire {G : Dag} {hs : HEState α} {s : EState α} (h : SimE G hs s) {p c : ℕ}
    (hc : c ∈ G.children p) :
    SimE (retireDag G p c) ⟨hs.val, Function.update hs.hp p (HeapImpl.delete (hs.hp p) c).1⟩ s := by
  refine ⟨h.val, fun q => ?_⟩
  show Rep (Function.update hs.hp p (HeapImpl.delete (hs.hp p) c).1 q)
    (if q = p then (G.children q).filter (· ≠ c) else G.children q).toFinset (s.key q)
    (if q = p then (G.children q).filter (· ≠ c) else G.children q).length
  by_cases hq : q = p
  · subst hq
    rw [Function.update_self, ite_eq_left rfl]
    exact (rep_delete (h.hp q) hc).1
  · rw [Function.update_of_ne hq, ite_eq_right hq]
    exact h.hp q

omit [OrderBot α] in
/-- One retirement test on implemented heaps simulates `DagRetire.retireOne` at no more
than twice its charged cost, and costs at least as much as the number of key cells it
clears (two when it retires). -/
theorem retireOneH_sim {hs : HRState α} {s : RState α} (h : SimR hs s) (e : ℕ × ℕ) :
    SimR (retireOneH e hs).1 (retireOne e s).1 ∧
    (retireOneH e hs).2 ≤ 2 * (retireOne e s).2 ∧
    (if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then 2 else 0)
      ≤ (retireOneH e hs).2 := by
  obtain ⟨hG, hlo, hhi⟩ := h
  obtain ⟨G, lo, hi⟩ := hs
  simp only at hG hlo hhi
  subst hG
  have hvl : lo.val = s.lo.val := hlo.val
  have hvh : hi.val = s.hi.val := hhi.val
  unfold retireOneH retireOne
  simp only [hvl, hvh]
  by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
  · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc]
    obtain ⟨_, l2, l3⟩ := rep_delete (hlo.hp e.1) hc.1
    obtain ⟨_, u2, u3⟩ := rep_delete (hhi.hp e.1) hc.1
    refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
    · have := simE_retire hlo hc.1
      rw [hvl] at this
      exact this
    · have := simE_retire hhi hc.1
      rw [hvh] at this
      exact this
    · show _ + _ + 3 ≤ 2 * (2 * Nat.clog 2 (s.G.children e.1).length + 5)
      omega
    · show 2 ≤ _ + _ + 3
      omega
  · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
    exact ⟨⟨rfl, hlo, hhi⟩, by show 1 ≤ 2 * 1; omega, Nat.zero_le _⟩

/-- Process a list of candidate incidences on implemented heaps. -/
def retireListH : List (ℕ × ℕ) → HRState α → HRState α × ℕ
  | [], s => (s, 0)
  | e :: es, s =>
    ((retireListH es (retireOneH e s).1).1,
     (retireOneH e s).2 + (retireListH es (retireOneH e s).1).2)

omit [OrderBot α] in
theorem retireListH_sim : ∀ (L : List (ℕ × ℕ)) {hs : HRState α} {s : RState α}, SimR hs s →
    SimR (retireListH L hs).1 (retireList L s).1 ∧
    (retireListH L hs).2 ≤ 2 * (retireList L s).2 := by
  intro L
  induction L with
  | nil => intro hs s h; exact ⟨h, le_rfl⟩
  | cons e es ih =>
    intro hs s h
    obtain ⟨a1, a2, _⟩ := retireOneH_sim h e
    obtain ⟨b1, b2⟩ := ih a1
    refine ⟨b1, ?_⟩
    show (retireOneH e hs).2 + (retireListH es (retireOneH e hs).1).2
      ≤ 2 * ((retireOne e s).2 + (retireList es (retireOne e s).1).2)
    omega

/-- The backup waves of one terminal update on implemented heaps (`HeapImpl.waveH`). -/
def waveStepH (u : ℕ × α × α) (s : HRState α) : HRState α × ℕ :=
  (⟨s.G, (waveH s.G u.1 u.2.1 s.lo).1, (waveH s.G u.1 u.2.2 s.hi).1⟩,
   (waveH s.G u.1 u.2.1 s.lo).2 + (waveH s.G u.1 u.2.2 s.hi).2)

theorem waveStepH_sim {hs : HRState α} {s : RState α} (h : SimR hs s) (u : ℕ × α × α) :
    SimR (waveStepH u hs).1 (waveStep u s).1 ∧ (waveStepH u hs).2 ≤ 2 * (waveStep u s).2 := by
  obtain ⟨hG, hlo, hhi⟩ := h
  obtain ⟨G, lo, hi⟩ := hs
  simp only at hG hlo hhi
  subst hG
  obtain ⟨l1, l2⟩ := HeapImpl.waveH_sim s.G u.1 u.2.1 lo s.lo hlo
  obtain ⟨u1, u2⟩ := HeapImpl.waveH_sim s.G u.1 u.2.2 hi s.hi hhi
  refine ⟨⟨rfl, l1, u1⟩, ?_⟩
  show (waveH s.G u.1 u.2.1 lo).2 + (waveH s.G u.1 u.2.2 hi).2
    ≤ 2 * ((wave s.G u.1 u.2.1 s.lo).2 + (wave s.G u.1 u.2.2 s.hi).2)
  omega

/-- A retirement policy that reads the live circuit and the stored values before and after
the waves: `candV G lo hi lo' hi'`. -/
abbrev Policy (α : Type*) := Dag → (ℕ → α) → (ℕ → α) → (ℕ → α) → (ℕ → α) → List (ℕ × ℕ)

/-- The policy of `DagRetire.rstep` induced by a value-reading policy. -/
def liftCand (candV : Policy α) (s s1 : RState α) : List (ℕ × ℕ) :=
  candV s.G s.lo.val s.hi.val s1.lo.val s1.hi.val

/-- The delivery policy as a value-reading policy. -/
def delivV : Policy α := fun G l h l1 h1 =>
  ((List.range G.N).filter (fun g => l1 g ≠ l g ∨ h1 g ≠ h g)).flatMap
    (fun g => (G.parents g).map (fun p => (p, g)))

omit [OrderBot α] in
lemma liftCand_delivV : liftCand (delivV : Policy α) = delivCand := rfl

/-- **One rollout of the engine on implemented heaps**: waves, then the retirement pass
over the candidates of the policy. -/
def rstepH (candV : Policy α) (u : ℕ × α × α) (s : HRState α) : HRState α × ℕ :=
  ((retireListH
      (candV s.G s.lo.val s.hi.val (waveStepH u s).1.lo.val (waveStepH u s).1.hi.val)
      (waveStepH u s).1).1,
   (waveStepH u s).2
    + (retireListH
        (candV s.G s.lo.val s.hi.val (waveStepH u s).1.lo.val (waveStepH u s).1.hi.val)
        (waveStepH u s).1).2)

theorem rstepH_sim (candV : Policy α) {hs : HRState α} {s : RState α} (h : SimR hs s)
    (u : ℕ × α × α) :
    SimR (rstepH candV u hs).1 (rstep (liftCand candV) u s).1 ∧
    (rstepH candV u hs).2 ≤ 2 * (rstep (liftCand candV) u s).2 := by
  obtain ⟨w1, w2⟩ := waveStepH_sim h u
  have hc : candV hs.G hs.lo.val hs.hi.val (waveStepH u hs).1.lo.val (waveStepH u hs).1.hi.val
      = liftCand candV s (waveStep u s).1 := by
    unfold liftCand
    rw [h.G, h.lo.val, h.hi.val, w1.lo.val, w1.hi.val]
  obtain ⟨r1, r2⟩ := retireListH_sim (liftCand candV s (waveStep u s).1) w1
  unfold rstepH
  rw [hc]
  refine ⟨r1, ?_⟩
  show (waveStepH u hs).2 + (retireListH _ (waveStepH u hs).1).2
    ≤ 2 * ((waveStep u s).2 + (retireList _ (waveStep u s).1).2)
  omega

/-- State of the implemented engine after `t` rollouts. -/
def rrunH (candV : Policy α) (u : ℕ → ℕ × α × α) (s0 : HRState α) : ℕ → HRState α
  | 0 => s0
  | t + 1 => (rstepH candV (u (t + 1)) (rrunH candV u s0 t)).1

/-- Computed cost of rollout `t + 1` of the implemented engine. -/
def stepCostH (candV : Policy α) (u : ℕ → ℕ × α × α) (s0 : HRState α) (t : ℕ) : ℕ :=
  (rstepH candV (u (t + 1)) (rrunH candV u s0 t)).2

/-- **Simulation theorem.**  The engine on implemented heaps simulates the engine of
`DagRetire.lean` at every time: same live circuit, same stored values, and every gate's
heap stores exactly the keys of its live children.  Every rollout costs at most twice the
charged cost. -/
theorem rrunH_sim (candV : Policy α) (u : ℕ → ℕ × α × α) {hs0 : HRState α} {s0 : RState α}
    (h : SimR hs0 s0) : ∀ t,
    SimR (rrunH candV u hs0 t) (rrun (liftCand candV) u s0 t) ∧
    stepCostH candV u hs0 t ≤ 2 * stepCost (liftCand candV) u s0 t := by
  have hs : ∀ t, SimR (rrunH candV u hs0 t) (rrun (liftCand candV) u s0 t) := by
    intro t
    induction t with
    | zero => exact h
    | succ t ih => exact (rstepH_sim candV ih (u (t + 1))).1
  exact fun t => ⟨hs t, (rstepH_sim candV (hs t) (u (t + 1))).2⟩

end EngineH

/-! ## Initialisation on implemented heaps -/

section InitH

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Initialise one internal gate on implemented heaps: build its heap by inserting the
stored values of its children into the empty heap (`HeapImpl.insertAll`, computed cost),
then read the heap root into the gate (1 unit). -/
def initGateH (G : Dag) (g : ℕ) (s : HEState α) : HEState α × ℕ :=
  (⟨fun g' => if g' = g then
        findMax (HeapImpl.insertAll (Heap.empty : Heap ℕ α)
          ((G.children g).map (fun c => (c, s.val c)))).1
      else s.val g',
    Function.update s.hp g (HeapImpl.insertAll (Heap.empty : Heap ℕ α)
      ((G.children g).map (fun c => (c, s.val c)))).1⟩,
   (HeapImpl.insertAll (Heap.empty : Heap ℕ α)
      ((G.children g).map (fun c => (c, s.val c)))).2 + 1)

/-- **Initialisation pass on implemented heaps.** -/
def initPassH (G : Dag) : List ℕ → HEState α → HEState α × ℕ
  | [], s => (s, 0)
  | g :: rest, s =>
    ((initPassH G rest (initGateH G g s).1).1,
     (initGateH G g s).2 + (initPassH G rest (initGateH G g s).1).2)

/-- Simulation during the pass: values agree, and the heap of every gate not waiting in
`rest` represents the abstract keys. -/
structure PSim (G : Dag) (rest : List ℕ) (hs : HEState α) (s : EState α) : Prop where
  val : hs.val = s.val
  hp : ∀ p, p ∉ rest → Rep (hs.hp p) (G.children p).toFinset (s.key p) (G.children p).length

lemma initGateH_sim {G : Dag} {g : ℕ} {rest : List ℕ} {hs : HEState α} {s : EState α}
    (hnd : (G.children g).Nodup) (h : PSim G (g :: rest) hs s) :
    PSim G rest (initGateH G g hs).1 (initGate G g s).1 ∧
    (initGateH G g hs).2 ≤ 2 * (initGate G g s).2 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := initGate_spec G g s
  obtain ⟨rb, rc⟩ := HeapImpl.rep_build (G.children g) hnd hs.val
  have hv := h.val
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · funext g'
    show (if g' = g then findMax _ else hs.val g') = (initGate G g s).1.val g'
    by_cases e : g' = g
    · rw [ite_eq_left e, e, rb.findMax, s4, HeapImpl.heapMax_eq_sup]
      apply Finset.sup_congr rfl
      intro c hc
      rw [s3 c (List.mem_toFinset.1 hc), hv]
    · rw [ite_eq_right e, s1 g' e, hv]
  · intro p hp
    show Rep (Function.update hs.hp g _ p) _ _ _
    by_cases e : p = g
    · rw [e, Function.update_self]
      refine rb.congr (fun c hc => ?_)
      rw [s3 c (List.mem_toFinset.1 hc), hv]
    · rw [Function.update_of_ne e]
      have hp' : p ∉ g :: rest := fun hm => by
        rcases List.mem_cons.1 hm with hm | hm
        · exact e hm
        · exact hp hm
      exact (h.hp p hp').congr (fun c _ => (s2 p c e).symm)
  · rw [s5]
    show _ + 1 ≤ 2 * initCost G g
    unfold initCost
    have h1 : (G.children g).length * (Nat.clog 2 (G.children g).length + 2)
        ≤ (G.children g).length * (2 * (Nat.clog 2 (G.children g).length + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (G.children g).length * (2 * (Nat.clog 2 (G.children g).length + 1))
        = 2 * ((G.children g).length * (Nat.clog 2 (G.children g).length + 1)) := by ring
    omega

lemma initPassH_loop {G : Dag} : ∀ (rest : List ℕ) (hs : HEState α) (s : EState α),
    (∀ g ∈ rest, (G.children g).Nodup) → PSim G rest hs s →
    SimE G (initPassH G rest hs).1 (initPass G rest s).1 ∧
    (initPassH G rest hs).2 ≤ 2 * (initPass G rest s).2 := by
  intro rest
  induction rest with
  | nil => intro hs s _ h; exact ⟨⟨h.val, fun p => h.hp p List.not_mem_nil⟩, le_rfl⟩
  | cons g rest ih =>
    intro hs s hnd h
    obtain ⟨a1, a2⟩ := initGateH_sim (hnd g List.mem_cons_self) h
    obtain ⟨b1, b2⟩ := ih _ _ (fun g' hg' => hnd g' (List.mem_cons_of_mem _ hg')) a1
    refine ⟨b1, ?_⟩
    show (initGateH G g hs).2 + (initPassH G rest (initGateH G g hs).1).2
      ≤ 2 * ((initGate G g s).2 + (initPass G rest (initGate G g s).1).2)
    omega

/-- **The initialisation pass on implemented heaps.**  Starting from empty heaps, with the
child lists free of repetitions and every internal gate listed in `order`, `initPassH`
simulates `DagRetire.initPass` (so `initPass_spec` applies) at computed cost at most twice
the charged cost. -/
theorem initPassH_sim {G : Dag} (order : List ℕ) (hs : HEState α) (s : EState α)
    (hnd : ∀ g, (G.children g).Nodup) (hall : ∀ g, G.children g ≠ [] → g ∈ order)
    (hval : hs.val = s.val) (hemp : ∀ p, hs.hp p = Heap.empty) :
    SimE G (initPassH G order hs).1 (initPass G order s).1 ∧
    (initPassH G order hs).2 ≤ 2 * (initPass G order s).2 := by
  apply initPassH_loop order hs s (fun g _ => hnd g)
  refine ⟨hval, fun p hp => ?_⟩
  have hc : G.children p = [] := by
    by_contra hne
    exact hp (hall p hne)
  rw [hemp p, hc]
  exact ⟨Heap.empty_inv, le_rfl, fun _ => rfl⟩

end InitH

/-! ## The execution as a trace of single-cell writes -/

section Trace

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- A key write `(p, c, y)`: the key of child `c` in the heap of gate `p` becomes `y`. -/
def wr (key : ℕ → ℕ → α) (o : ℕ × ℕ × α) : ℕ → ℕ → α :=
  fun p' c' => if p' = o.1 ∧ c' = o.2.1 then o.2.2 else key p' c'

/-- Apply a list of key writes. -/
def applyK : List (ℕ × ℕ × α) → (ℕ → ℕ → α) → ℕ → ℕ → α
  | [], key => key
  | o :: os, key => applyK os (wr key o)

omit [LinearOrder α] [OrderBot α] in
lemma applyK_append (a b : List (ℕ × ℕ × α)) (key : ℕ → ℕ → α) :
    applyK (a ++ b) key = applyK b (applyK a key) := by
  induction a generalizing key with
  | nil => rfl
  | cons o a ih => exact ih _

/-- Key writes of the deliveries from a changed gate `g`: one per parent. -/
def pushT (g : ℕ) (y : α) (ps : List ℕ) : List (ℕ × ℕ × α) := ps.map (fun p => (p, g, y))

omit [LinearOrder α] [OrderBot α] in
lemma push_trace (G : Dag) (g : ℕ) (y : α) : ∀ (ps : List ℕ) (key : ℕ → ℕ → α)
    (bk : ℕ → List ℕ), (push G g y ps key bk).1 = applyK (pushT g y ps) key := by
  intro ps
  induction ps with
  | nil => intro key bk; rfl
  | cons p ps ih =>
    intro key bk
    exact ih _ _

/-- Key writes of processing one bucket (the recursion of `CostEngines.procList`). -/
def procListT (G : Dag) (x : ℕ) (y : α) :
    List ℕ → EState α → (ℕ → List ℕ) → List (ℕ × ℕ × α)
  | [], _, _ => []
  | g :: rest, s, bk =>
    if target G x y s g = s.val g then procListT G x y rest s bk
    else
      pushT g (target G x y s g) (G.parents g) ++
        procListT G x y rest
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
          (push G g (target G x y s g) (G.parents g) s.key bk).2.1

lemma procList_trace (G : Dag) (x : ℕ) (y : α) : ∀ (rest : List ℕ) (s : EState α)
    (bk : ℕ → List ℕ),
    (procList G x y rest s bk).1.key = applyK (procListT G x y rest s bk) s.key := by
  intro rest
  induction rest with
  | nil => intro s bk; rfl
  | cons g rest ih =>
    intro s bk
    by_cases heq : target G x y s g = s.val g
    · rw [procList_same rest heq, procListT, ite_eq_left heq]
      exact ih s bk
    · rw [procList_change rest heq, procListT, ite_eq_right heq, applyK_append,
        ← push_trace G g (target G x y s g) (G.parents g) s.key bk]
      exact ih _ _

/-- Key writes of the level sweep (the recursion of `CostEngines.waveLevels`). -/
def waveLevelsT (G : Dag) (x : ℕ) (y : α) :
    ℕ → EState α → (ℕ → List ℕ) → List (ℕ × ℕ × α)
  | 0, _, _ => []
  | l + 1, s, bk =>
    waveLevelsT G x y l s bk ++
      procListT G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
        (waveLevels G x y l s bk).2.1

lemma waveLevels_trace (G : Dag) (x : ℕ) (y : α) (s : EState α) (bk : ℕ → List ℕ) : ∀ l,
    (waveLevels G x y l s bk).1.key = applyK (waveLevelsT G x y l s bk) s.key := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    show (procList G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
        (waveLevels G x y l s bk).2.1).1.key
      = applyK (waveLevelsT G x y l s bk ++ procListT G x y ((waveLevels G x y l s bk).2.1 l)
          (waveLevels G x y l s bk).1 (waveLevels G x y l s bk).2.1) s.key
    rw [applyK_append, procList_trace, ih]

/-- **Key-write trace of one backup wave.** -/
def waveT (G : Dag) (x : ℕ) (y : α) (s : EState α) : List (ℕ × ℕ × α) :=
  waveLevelsT G x y (G.L + 1) s (fun l => if l = G.level x then [x] else [])

/-- The keys after a wave are the keys before it with the trace applied. -/
lemma wave_trace (G : Dag) (x : ℕ) (y : α) (s : EState α) :
    (wave G x y s).1.key = applyK (waveT G x y s) s.key :=
  waveLevels_trace G x y s _ (G.L + 1)

/-- All writes of a trace address live incidences of `G`. -/
def OpsLive (G : Dag) (T : List (ℕ × ℕ × α)) : Prop := ∀ o ∈ T, o.2.1 ∈ G.children o.1

lemma procListT_live {G : Dag} (hG : G.WF) (x : ℕ) (y : α) : ∀ (rest : List ℕ)
    (s : EState α) (bk : ℕ → List ℕ), OpsLive G (procListT G x y rest s bk) := by
  intro rest
  induction rest with
  | nil => intro s bk o ho; simp [procListT] at ho
  | cons g rest ih =>
    intro s bk
    by_cases heq : target G x y s g = s.val g
    · rw [procListT, ite_eq_left heq]
      exact ih s bk
    · rw [procListT, ite_eq_right heq]
      intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        exact (hG.parents_iff g p).1 hp
      · exact ih _ _ o ho

lemma waveLevelsT_live {G : Dag} (hG : G.WF) (x : ℕ) (y : α) (s : EState α)
    (bk : ℕ → List ℕ) : ∀ l, OpsLive G (waveLevelsT G x y l s bk) := by
  intro l
  induction l with
  | zero => intro o ho; simp [waveLevelsT] at ho
  | succ l ih =>
    intro o ho
    rw [waveLevelsT] at ho
    rcases List.mem_append.1 ho with ho | ho
    · exact ih o ho
    · exact procListT_live hG x y _ _ _ o ho

lemma waveT_live {G : Dag} (hG : G.WF) (x : ℕ) (y : α) (s : EState α) :
    OpsLive G (waveT G x y s) := waveLevelsT_live hG x y s _ _

/-! ### Every traced write is an operation of the implemented engine -/

omit [OrderBot α] in
lemma pushH_len (G : Dag) (g : ℕ) (y : α) : ∀ (ps : List ℕ) (hp : ℕ → Heap ℕ α)
    (bk : ℕ → List ℕ), ps.length ≤ (HeapImpl.pushH G g y ps hp bk).2.2 := by
  intro ps
  induction ps with
  | nil => intro hp bk; exact Nat.zero_le _
  | cons p ps ih =>
    intro hp bk
    simp only [HeapImpl.pushH, List.length_cons]
    exact Nat.add_le_add (ih _ _) (Nat.le_add_left _ _)

lemma procListH_len (G : Dag) (x : ℕ) (y : α) : ∀ (rest : List ℕ) (hs : HEState α)
    (s : EState α) (bk : ℕ → List ℕ), SimE G hs s →
    (procListT G x y rest s bk).length ≤ (HeapImpl.procListH G x y rest hs bk).2.2 := by
  intro rest
  induction rest with
  | nil => intro hs s bk _; exact Nat.zero_le _
  | cons g rest ih =>
    intro hs s bk h
    have ht := HeapImpl.targetH_eq h x y g
    by_cases heq : target G x y s g = s.val g
    · have heq' : HeapImpl.targetH G x y hs g = hs.val g := by rw [ht, h.val]; exact heq
      rw [procListT, ite_eq_left heq, HeapImpl.procListH, ite_eq_left heq']
      exact (ih hs s bk h).trans (Nat.le_succ _)
    · have heq' : ¬ HeapImpl.targetH G x y hs g = hs.val g := by rw [ht, h.val]; exact heq
      rw [procListT, ite_eq_right heq, HeapImpl.procListH, ite_eq_right heq']
      obtain ⟨p1, p2, _⟩ := HeapImpl.pushH_spec G g (target G x y s g) (G.parents g) hs.hp
        s.key bk h.hp
      rw [ht, p2]
      have hsim : SimE G
          ⟨fun g' => if g' = g then target G x y s g else hs.val g',
            (HeapImpl.pushH G g (target G x y s g) (G.parents g) hs.hp bk).1⟩
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩ :=
        ⟨by show (fun g' => if g' = g then target G x y s g else hs.val g') = stepVal G x y s g
            rw [h.val]; rfl, p1⟩
      have h1 := ih _ _ (push G g (target G x y s g) (G.parents g) s.key bk).2.1 hsim
      have h2 := pushH_len G g (target G x y s g) (G.parents g) hs.hp bk
      rw [List.length_append]
      have h3 : (pushT g (target G x y s g) (G.parents g)).length = (G.parents g).length := by
        simp [pushT]
      rw [h3]
      show _ ≤ _ + 1 + _
      omega

lemma waveLevelsH_len (G : Dag) (x : ℕ) (y : α) (hs : HEState α) (s : EState α)
    (bk : ℕ → List ℕ) (h : SimE G hs s) : ∀ l,
    (waveLevelsT G x y l s bk).length ≤ (HeapImpl.waveLevelsH G x y l hs bk).2.2 := by
  intro l
  induction l with
  | zero => exact Nat.zero_le _
  | succ l ih =>
    obtain ⟨h1, h2, _⟩ := HeapImpl.waveLevelsH_spec G x y hs s bk h l
    simp only [waveLevelsT, HeapImpl.waveLevelsH]
    rw [h2, List.length_append]
    have q := procListH_len G x y ((waveLevels G x y l s bk).2.1 l) _ _
      (waveLevels G x y l s bk).2.1 h1
    omega

/-- The number of key writes of a wave is at most the computed cost of the wave on
implemented heaps. -/
lemma waveT_length_le (G : Dag) (x : ℕ) (y : α) (hs : HEState α) (s : EState α)
    (h : SimE G hs s) : (waveT G x y s).length ≤ (waveH G x y hs).2 :=
  (waveLevelsH_len G x y hs s _ h (G.L + 1)).trans (Nat.le_succ _)

/-! ### Key memory -/

/-- Key memory determined by a live circuit and key tables: the cell `(b, (p, c))` holds
the key of child `c` in the heap of `p` for endpoint `b` (`false` lower, `true` upper) if
the incidence is live, and is blank (`⊥`) otherwise. -/
def memG (G : Dag) (klo khi : ℕ → ℕ → α) : Bool × (ℕ × ℕ) → α :=
  fun c => if c.2.2 ∈ G.children c.2.1 then
    (if c.1 then khi c.2.1 c.2.2 else klo c.2.1 c.2.2) else ⊥

/-- Key memory of an abstract engine state. -/
def memL (s : RState α) : Bool × (ℕ × ℕ) → α := memG s.G s.lo.key s.hi.key

/-- **Key memory of the implemented engine**, read off its heaps: the key stored under
handle `c` in the heap of gate `p`, blank if the handle is absent. -/
def memH (hs : HRState α) : Bool × (ℕ × ℕ) → α :=
  fun c => (((if c.1 then hs.hi else hs.lo).hp c.2.1).lookup c.2.2).getD ⊥

lemma memH_eq {hs : HRState α} {s : RState α} (h : SimR hs s) : memH hs = memL s := by
  funext c
  obtain ⟨b, p, c⟩ := c
  cases b
  · show (((hs.lo).hp p).lookup c).getD ⊥
      = if c ∈ s.G.children p then s.lo.key p c else ⊥
    rw [(h.lo.hp p).look c]
    by_cases hm : c ∈ s.G.children p
    · simp [hm]
    · simp [hm]
  · show (((hs.hi).hp p).lookup c).getD ⊥
      = if c ∈ s.G.children p then s.hi.key p c else ⊥
    rw [(h.hi.hp p).look c]
    by_cases hm : c ∈ s.G.children p
    · simp [hm]
    · simp [hm]

/-- A key write as a contract operation on the cell of endpoint `b`. -/
def tagOp (b : Bool) (o : ℕ × ℕ × α) : Option ((Bool × (ℕ × ℕ)) × α) :=
  some ((b, (o.1, o.2.1)), o.2.2)

omit [LinearOrder α] [OrderBot α] in
lemma applyOps_append {C : Type*} [DecidableEq C] (a b : List (Option (C × α)))
    (m : C → α) : applyOps (a ++ b) m = applyOps b (applyOps a m) := by
  induction a generalizing m with
  | nil => rfl
  | cons o a ih =>
    cases o with
    | none => exact ih m
    | some w => exact ih _

lemma memG_wr_lo {G : Dag} (klo khi : ℕ → ℕ → α) (o : ℕ × ℕ × α)
    (hc : o.2.1 ∈ G.children o.1) :
    Function.update (memG G klo khi) (false, (o.1, o.2.1)) o.2.2 = memG G (wr klo o) khi := by
  funext c
  obtain ⟨b, p, c⟩ := c
  by_cases e : (b, p, c) = (false, o.1, o.2.1)
  · rw [e, Function.update_self]
    simp [memG, wr, hc]
  · rw [Function.update_of_ne e]
    cases b
    · have hne : ¬ (p = o.1 ∧ c = o.2.1) := fun h => e (by rw [h.1, h.2])
      simp [memG, wr, hne]
    · simp [memG]

lemma memG_wr_hi {G : Dag} (klo khi : ℕ → ℕ → α) (o : ℕ × ℕ × α)
    (hc : o.2.1 ∈ G.children o.1) :
    Function.update (memG G klo khi) (true, (o.1, o.2.1)) o.2.2 = memG G klo (wr khi o) := by
  funext c
  obtain ⟨b, p, c⟩ := c
  by_cases e : (b, p, c) = (true, o.1, o.2.1)
  · rw [e, Function.update_self]
    simp [memG, wr, hc]
  · rw [Function.update_of_ne e]
    cases b
    · simp [memG]
    · have hne : ¬ (p = o.1 ∧ c = o.2.1) := fun h => e (by rw [h.1, h.2])
      simp [memG, wr, hne]

lemma applyOps_tag_lo {G : Dag} (khi : ℕ → ℕ → α) : ∀ (T : List (ℕ × ℕ × α))
    (klo : ℕ → ℕ → α), OpsLive G T →
    applyOps (T.map (tagOp false)) (memG G klo khi) = memG G (applyK T klo) khi := by
  intro T
  induction T with
  | nil => intro klo _; rfl
  | cons o T ih =>
    intro klo hT
    show applyOps (T.map (tagOp false))
      (Function.update (memG G klo khi) (false, (o.1, o.2.1)) o.2.2) = _
    rw [memG_wr_lo klo khi o (hT o List.mem_cons_self)]
    exact ih _ (fun o' ho' => hT o' (List.mem_cons_of_mem _ ho'))

lemma applyOps_tag_hi {G : Dag} (klo : ℕ → ℕ → α) : ∀ (T : List (ℕ × ℕ × α))
    (khi : ℕ → ℕ → α), OpsLive G T →
    applyOps (T.map (tagOp true)) (memG G klo khi) = memG G klo (applyK T khi) := by
  intro T
  induction T with
  | nil => intro khi _; rfl
  | cons o T ih =>
    intro khi hT
    show applyOps (T.map (tagOp true))
      (Function.update (memG G klo khi) (true, (o.1, o.2.1)) o.2.2) = _
    rw [memG_wr_hi klo khi o (hT o List.mem_cons_self)]
    exact ih _ (fun o' ho' => hT o' (List.mem_cons_of_mem _ ho'))

/-- Key writes of a retirement pass: a retirement clears the two key cells of the
incidence. -/
def retireOps : List (ℕ × ℕ) → RState α → List (Option ((Bool × (ℕ × ℕ)) × α))
  | [], _ => []
  | e :: es, s =>
    (if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then
        [some ((false, e), ⊥), some ((true, e), ⊥)] else [])
      ++ retireOps es (retireOne e s).1

lemma retireOne_mem (e : ℕ × ℕ) (s : RState α) :
    applyOps (if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then
        [some ((false, e), (⊥ : α)), some ((true, e), ⊥)] else []) (memL s)
      = memL (retireOne e s).1 := by
  unfold retireOne
  by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
  · rw [ite_eq_left hc, ite_eq_left hc]
    show Function.update (Function.update (memL s) (false, e) ⊥) (true, e) ⊥
      = memG (retireDag s.G e.1 e.2) s.lo.key s.hi.key
    funext c
    obtain ⟨b, p, c⟩ := c
    have hm := @mem_retire_children s.G e.1 e.2 p c
    by_cases hpc : p = e.1 ∧ c = e.2
    · have hnot : c ∉ (retireDag s.G e.1 e.2).children p := fun h => (hm.1 h).2 hpc
      have he : (p, c) = e := by rw [hpc.1, hpc.2]
      show _ = if c ∈ (retireDag s.G e.1 e.2).children p then _ else ⊥
      rw [ite_eq_right hnot, he]
      cases b
      · rw [Function.update_of_ne (by simp), Function.update_self]
      · rw [Function.update_self]
    · have hne : ∀ b' : Bool, (b, p, c) ≠ (b', e) := by
        intro b' h
        apply hpc
        have h2 : (p, c) = e := (Prod.mk.inj h).2
        rw [← h2]
        exact ⟨rfl, rfl⟩
      rw [Function.update_of_ne (hne true), Function.update_of_ne (hne false)]
      show (if c ∈ s.G.children p then _ else ⊥)
        = if c ∈ (retireDag s.G e.1 e.2).children p then _ else ⊥
      by_cases hmem : c ∈ s.G.children p
      · rw [ite_eq_left hmem, ite_eq_left (hm.2 ⟨hmem, hpc⟩)]
      · rw [ite_eq_right hmem, ite_eq_right (fun h => hmem (hm.1 h).1)]
  · rw [ite_eq_right hc, ite_eq_right hc]
    rfl

lemma retireOps_spec : ∀ (L : List (ℕ × ℕ)) (s : RState α),
    applyOps (retireOps L s) (memL s) = memL (retireList L s).1 := by
  intro L
  induction L with
  | nil => intro s; rfl
  | cons e es ih =>
    intro s
    show applyOps (_ ++ retireOps es (retireOne e s).1) (memL s)
      = memL (retireList es (retireOne e s).1).1
    rw [applyOps_append, retireOne_mem, ih]

lemma retireOps_length_le : ∀ (L : List (ℕ × ℕ)) {hs : HRState α}
    {s : RState α}, SimR hs s → (retireOps L s).length ≤ (retireListH L hs).2 := by
  intro L
  induction L with
  | nil => intro hs s _; exact Nat.zero_le _
  | cons e es ih =>
    intro hs s h
    obtain ⟨a1, _, a3⟩ := retireOneH_sim h e
    have b := ih a1
    show (_ ++ retireOps es (retireOne e s).1).length
      ≤ (retireOneH e hs).2 + (retireListH es (retireOneH e hs).1).2
    rw [List.length_append]
    refine Nat.add_le_add ?_ b
    refine le_trans (le_of_eq ?_) a3
    split_ifs <;> rfl

/-- **Trace of one rollout**: the key writes of the lower wave, of the upper wave, and of
the retirement pass. -/
def stepOps (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ × α × α) (s : RState α) :
    List (Option ((Bool × (ℕ × ℕ)) × α)) :=
  (waveT s.G u.1 u.2.1 s.lo).map (tagOp false) ++ (waveT s.G u.1 u.2.2 s.hi).map (tagOp true)
    ++ retireOps (cand s (waveStep u s).1) (waveStep u s).1

/-- The trace of a rollout transforms the key memory before it into the key memory after
it. -/
theorem stepOps_spec (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ × α × α)
    (s : RState α) (hG : s.G.WF) :
    applyOps (stepOps cand u s) (memL s) = memL (rstep cand u s).1 := by
  unfold stepOps
  rw [applyOps_append, applyOps_append]
  show applyOps _ (applyOps _ (applyOps _ (memG s.G s.lo.key s.hi.key))) = _
  rw [applyOps_tag_lo _ _ _ (waveT_live hG _ _ _), applyOps_tag_hi _ _ _ (waveT_live hG _ _ _),
    ← wave_trace, ← wave_trace]
  exact retireOps_spec _ _

/-- Every write of the trace is an operation of the implemented engine: the trace of a
rollout is no longer than the rollout's computed cost. -/
theorem stepOps_length_le (candV : Policy α) (u : ℕ × α × α) {hs : HRState α} {s : RState α}
    (h : SimR hs s) : (stepOps (liftCand candV) u s).length ≤ (rstepH candV u hs).2 := by
  obtain ⟨w1, _⟩ := waveStepH_sim h u
  have hc : candV hs.G hs.lo.val hs.hi.val (waveStepH u hs).1.lo.val (waveStepH u hs).1.hi.val
      = liftCand candV s (waveStep u s).1 := by
    unfold liftCand
    rw [h.G, h.lo.val, h.hi.val, w1.lo.val, w1.hi.val]
  have r := retireOps_length_le (liftCand candV s (waveStep u s).1) w1
  have l1 := waveT_length_le s.G u.1 u.2.1 hs.lo s.lo h.lo
  have l2 := waveT_length_le s.G u.1 u.2.2 hs.hi s.hi h.hi
  unfold stepOps rstepH
  rw [hc, List.length_append, List.length_append, List.length_map, List.length_map]
  have hw : (waveStepH u hs).2 = (waveH s.G u.1 u.2.1 hs.lo).2 + (waveH s.G u.1 u.2.2 hs.hi).2 := by
    unfold waveStepH
    rw [h.G]
  show _ ≤ (waveStepH u hs).2 + _
  omega

end Trace

/-! ## The implemented engine as an instance of the lower-bound contract -/

section Contract

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The live incidences `(p, c)` of a circuit, as a finite set. -/
def liveInc (G : Dag) : Finset (ℕ × ℕ) :=
  (range G.N ×ˢ range G.N).filter (fun e => e.2 ∈ G.children e.1)

lemma sum_liveInc {G : Dag} (hG : G.WF) (f : ℕ → ℕ) :
    ∑ e ∈ liveInc G, f e.2 = ∑ g ∈ range G.N, f g * (G.parents g).length := by
  unfold liveInc
  rw [sum_filter, sum_product_right]
  apply sum_congr rfl
  intro c _
  have hcard : ((range G.N).filter (fun p => c ∈ G.children p)).card
      = (G.parents c).length := by
    rw [← List.toFinset_card_of_nodup (hG.parents_nodup c)]
    congr 1
    ext p
    simp only [mem_filter, mem_range, List.mem_toFinset]
    exact ⟨fun h => (hG.parents_iff c p).2 h.2,
      fun h => ⟨hG.parent_lt c p h, (hG.parents_iff c p).1 h⟩⟩
  show ∑ p ∈ range G.N, (if c ∈ G.children p then f c else 0) = _
  rw [← sum_filter, sum_const, hcard, smul_eq_mul, mul_comm]

omit [OrderBot α] in
lemma vol_eq_sum (G : Dag) (a b : EState α) :
    vol G a b
      = ∑ g ∈ range G.N, (if b.val g ≠ a.val g then 1 else 0) * (G.parents g).length := by
  unfold vol
  rw [sum_filter]
  apply sum_congr rfl
  intro g _
  split_ifs <;> simp

omit [OrderBot α] in
/-- The changed endpoints summed over the live incidences are the delivery volume
`Σ_v b(v) d⁻_F(v)`. -/
lemma liveInc_delivery {G : Dag} (hG : G.WF) (a b a' b' : EState α) :
    ∑ e ∈ liveInc G, ((if b.val e.2 ≠ a.val e.2 then 1 else 0)
        + (if b'.val e.2 ≠ a'.val e.2 then 1 else 0))
      = vol G a b + vol G a' b' := by
  refine (sum_liveInc hG (fun g => (if b.val g ≠ a.val g then 1 else 0)
    + (if b'.val g ≠ a'.val g then 1 else 0))).trans ?_
  rw [vol_eq_sum, vol_eq_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro g _
  ring

lemma sum_Icc_pred (h : ℕ → ℕ) : ∀ τ, ∑ t ∈ Icc 1 τ, h (t - 1) = ∑ t ∈ range τ, h t
  | 0 => by simp
  | τ + 1 => by
    rw [sum_Icc_succ_top (by omega), sum_Icc_pred h τ, sum_range_succ]
    simp

variable {G0 : Dag} {hs0 : HRState α} {s0 : RState α}

/-- **The implemented engine satisfies the contract of `DagRetire.contract_lower`.**
Along a run of the engine on implemented heaps, with `F t` the live incidences after
rollout `t` and `memH` the key memory read off the heaps:

* `F (t + 1) ⊆ F t` (only retirement);
* the key memory after rollout `t + 1` is the key memory after rollout `t` with the trace
  `stepOps` of single-cell writes applied;
* at every time the key cell of every live incidence holds the stored (exact) endpoint of
  its child;
* the trace of a rollout is no longer than the computed cost of the rollout. -/
theorem rrunH_trace (candV : Policy α) (u : ℕ → ℕ × α × α) (hsim : SimR hs0 s0)
    (h0 : RInv G0 s0) (hn : NestedRun G0 (liftCand candV) u s0) :
    (∀ t, liveInc (rrunH candV u hs0 (t + 1)).G ⊆ liveInc (rrunH candV u hs0 t).G) ∧
    (∀ t, memH (rrunH candV u hs0 (t + 1))
      = applyOps (stepOps (liftCand candV) (u (t + 1)) (rrun (liftCand candV) u s0 t))
          (memH (rrunH candV u hs0 t))) ∧
    (∀ t, ∀ e ∈ liveInc (rrunH candV u hs0 t).G,
      memH (rrunH candV u hs0 t) (false, e) = (rrunH candV u hs0 t).lo.val e.2 ∧
      memH (rrunH candV u hs0 t) (true, e) = (rrunH candV u hs0 t).hi.val e.2) ∧
    (∀ t, (stepOps (liftCand candV) (u (t + 1)) (rrun (liftCand candV) u s0 t)).length
      ≤ stepCostH candV u hs0 t) := by
  have hS := fun t => (rrunH_sim candV u hsim t).1
  have hI := rrun_inv h0 hn
  refine ⟨fun t e he => ?_, fun t => ?_, fun t e he => ?_, fun t => ?_⟩
  · obtain ⟨_, _, e3, _, e5⟩ :=
      rstep_endpoints (liftCand candV) (u (t + 1)) (rrun (liftCand candV) u s0 t)
    have e3' : (rrun (liftCand candV) u s0 (t + 1)).G.N = (rrun (liftCand candV) u s0 t).G.N :=
      e3
    have e5' : ∀ g, ((rrun (liftCand candV) u s0 (t + 1)).G.children g).Sublist
        ((rrun (liftCand candV) u s0 t).G.children g) := e5
    rw [(hS (t + 1)).G] at he
    rw [(hS t).G]
    unfold liveInc at he ⊢
    simp only [mem_filter, mem_product, mem_range] at he ⊢
    rw [e3'] at he
    exact ⟨he.1, (e5' e.1).subset he.2⟩
  · rw [memH_eq (hS (t + 1)), memH_eq (hS t)]
    exact (stepOps_spec _ _ _ (hI t).wf).symm
  · rw [(hS t).G] at he
    have hm : e.2 ∈ (rrun (liftCand candV) u s0 t).G.children e.1 := (mem_filter.1 he).2
    rw [memH_eq (hS t), (hS t).lo.val, (hS t).hi.val]
    constructor
    · show (if e.2 ∈ (rrun (liftCand candV) u s0 t).G.children e.1 then
        (rrun (liftCand candV) u s0 t).lo.key e.1 e.2 else ⊥) = _
      rw [ite_eq_left hm, (hI t).invLo.keys e.1 e.2 hm]
    · show (if e.2 ∈ (rrun (liftCand candV) u s0 t).G.children e.1 then
        (rrun (liftCand candV) u s0 t).hi.key e.1 e.2 else ⊥) = _
      rw [ite_eq_left hm, (hI t).invHi.keys e.1 e.2 hm]
  · exact stepOps_length_le candV (u (t + 1)) (hS t)

/-- **`contract_lower` applied to the implemented engine**: `P + S⁻ ≤ P + Σ_t (computed
cost of rollout t)`, with `S⁻` the post-update delivery volume of `eq:s-plus-minus` over
the changing live sets.  The bound is obtained from `DagRetire.contract_lower` through
`rrunH_trace`, not from the engine's cost formula. -/
theorem engineH_contract_lower (candV : Policy α) (u : ℕ → ℕ × α × α) (hsim : SimR hs0 s0)
    (h0 : RInv G0 s0) (hn : NestedRun G0 (liftCand candV) u s0) (τ P : ℕ) :
    P + ∑ t ∈ range τ, stepMinus (liftCand candV) u s0 t
      ≤ P + ∑ t ∈ range τ, stepCostH candV u hs0 t := by
  obtain ⟨c1, c2, c3, c4⟩ := rrunH_trace candV u hsim h0 hn
  have hS := fun t => (rrunH_sim candV u hsim t).1
  have hI := rrun_inv h0 hn
  have key := contract_lower τ (fun t => liveInc (rrunH candV u hs0 t).G)
    (fun t => (rrunH candV u hs0 t).lo.val) (fun t => (rrunH candV u hs0 t).hi.val)
    (fun t => memH (rrunH candV u hs0 t))
    (fun t => stepOps (liftCand candV) (u t) (rrun (liftCand candV) u s0 (t - 1))) P
    (by
      intro t ht
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
      exact c1 t')
    (by
      intro t ht
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
      exact c2 t')
    (fun t _ e he => c3 t e he)
  have hA : ∀ t ∈ Icc 1 τ, stepMinus (liftCand candV) u s0 (t - 1)
      = ∑ e ∈ liveInc (rrunH candV u hs0 t).G,
          ((if (rrunH candV u hs0 t).lo.val e.2 ≠ (rrunH candV u hs0 (t - 1)).lo.val e.2
              then 1 else 0)
            + (if (rrunH candV u hs0 t).hi.val e.2 ≠ (rrunH candV u hs0 (t - 1)).hi.val e.2
              then 1 else 0)) := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
    rw [Nat.add_sub_cancel, (hS (t' + 1)).G, (hS (t' + 1)).lo.val, (hS (t' + 1)).hi.val,
      (hS t').lo.val, (hS t').hi.val]
    exact (liveInc_delivery (hI (t' + 1)).wf _ _ _ _).symm
  have hB : ∀ t ∈ Icc 1 τ,
      (stepOps (liftCand candV) (u t) (rrun (liftCand candV) u s0 (t - 1))).length
        ≤ stepCostH candV u hs0 (t - 1) := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
    exact c4 t'
  calc P + ∑ t ∈ range τ, stepMinus (liftCand candV) u s0 t
      = P + ∑ t ∈ Icc 1 τ, stepMinus (liftCand candV) u s0 (t - 1) := by
        rw [sum_Icc_pred]
    _ = P + ∑ t ∈ Icc 1 τ, ∑ e ∈ liveInc (rrunH candV u hs0 t).G,
          ((if (rrunH candV u hs0 t).lo.val e.2 ≠ (rrunH candV u hs0 (t - 1)).lo.val e.2
              then 1 else 0)
            + (if (rrunH candV u hs0 t).hi.val e.2 ≠ (rrunH candV u hs0 (t - 1)).hi.val e.2
              then 1 else 0)) := by
        rw [sum_congr rfl hA]
    _ ≤ P + ∑ t ∈ Icc 1 τ,
          (stepOps (liftCand candV) (u t) (rrun (liftCand candV) u s0 (t - 1))).length := key
    _ ≤ P + ∑ t ∈ Icc 1 τ, stepCostH candV u hs0 (t - 1) :=
        Nat.add_le_add_left (sum_le_sum hB) P
    _ = P + ∑ t ∈ range τ, stepCostH candV u hs0 t := by rw [sum_Icc_pred]

end Contract

/-! ## `prop:representation-cost` -/

section Final

open Asymptotics

/-- **An instance of the engine**: a circuit `G0` of maximum degree `D`, its internal gates
`order` listed by nondecreasing level, initial terminal intervals (`hl.val`, `hu.val` at
the leaves) with empty heaps, a sequence of nested terminal updates `u`, a number of
rollouts `τ`, and upfront work `P` (compilation; any number).  The run is: initialisation
of both endpoints by `initPassH`, then `τ` rollouts of `rstepH` with the delivery retirement
policy. -/
structure EngineRun (α : Type*) [LinearOrder α] [OrderBot α] where
  G0 : Dag
  D : ℕ
  order : List ℕ
  hl : HEState α
  hu : HEState α
  u : ℕ → ℕ × α × α
  τ : ℕ
  P : ℕ
  wf : G0.WF
  deg : ∀ p, (G0.children p).length ≤ D
  nodup : ∀ g, (G0.children g).Nodup
  order_all : ∀ g, G0.children g ≠ [] → g ∈ order
  order_int : ∀ g ∈ order, G0.children g ≠ []
  order_sorted : order.Pairwise (fun a b => G0.level a ≤ G0.level b)
  order_nodup : order.Nodup
  empty_lo : ∀ p, hl.hp p = Heap.empty
  empty_hi : ∀ p, hu.hp p = Heap.empty
  leaf : ∀ g, G0.children g = [] → hl.val g ≤ hu.val g
  nested : ∀ t, (u (t + 1)).1 < G0.N ∧
    (rrunH delivV u ⟨G0, (initPassH G0 order hl).1, (initPassH G0 order hu).1⟩ t).lo.val
        (u (t + 1)).1 ≤ (u (t + 1)).2.1 ∧
    (u (t + 1)).2.1 ≤ (u (t + 1)).2.2 ∧
    (u (t + 1)).2.2 ≤
      (rrunH delivV u ⟨G0, (initPassH G0 order hl).1, (initPassH G0 order hu).1⟩ t).hi.val
        (u (t + 1)).1

namespace EngineRun

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : EngineRun α)

/-- The initialised state of the implemented engine. -/
def hs0 : HRState α := ⟨R.G0, (initPassH R.G0 R.order R.hl).1, (initPassH R.G0 R.order R.hu).1⟩

/-- The corresponding initialised state of the engine of `DagRetire.lean`. -/
def s0 : RState α :=
  ⟨R.G0, (initPass R.G0 R.order ⟨R.hl.val, fun _ _ => ⊥⟩).1,
    (initPass R.G0 R.order ⟨R.hu.val, fun _ _ => ⊥⟩).1⟩

/-- **Total computed work** `W_R`: upfront work, the two initialisation passes, and the
`τ` rollouts, all heap operations executed by the implemented heap. -/
def W : ℕ :=
  R.P + ((initPassH R.G0 R.order R.hl).2 + (initPassH R.G0 R.order R.hu).2)
    + ∑ t ∈ range R.τ, stepCostH delivV R.u R.hs0 t

/-- `S⁺` of `eq:s-plus-minus` over the changing live sets. -/
def Splus : ℕ := ∑ t ∈ range R.τ, stepPlus delivCand R.u R.s0 t

/-- `S⁻` of `eq:s-plus-minus` over the changing live sets. -/
def Sminus : ℕ := ∑ t ∈ range R.τ, stepMinus delivCand R.u R.s0 t

/-- The upper expression of `eq:prop-rep-upper`:
`H + P + n + e + (S⁺ + e)(⌈log₂ D⌉ + 1)`, with `H = 2τ(L + 3)` the level scheduling of the
waves, `n` the number of internal gates and `e` the number of incidences. -/
def X : ℕ :=
  2 * R.τ * (R.G0.L + 3) + R.P + R.order.length + live R.G0
    + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)

/-- The lower expression `P + S⁻`. -/
def Y : ℕ := R.P + R.Sminus

lemma init_sim : SimR R.hs0 R.s0 ∧ RInv R.G0 R.s0 ∧
    (initPassH R.G0 R.order R.hl).2 + (initPassH R.G0 R.order R.hu).2
      ≤ 4 * (R.order.map (initCost R.G0)).sum := by
  obtain ⟨i1, i2⟩ := init_engine R.wf R.order (⟨R.hl.val, fun _ _ => ⊥⟩ : EState α)
    ⟨R.hu.val, fun _ _ => ⊥⟩ R.order_all R.order_int R.order_sorted R.leaf
  obtain ⟨l1, l2⟩ := initPassH_sim (G := R.G0) R.order R.hl ⟨R.hl.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_lo
  obtain ⟨u1, u2⟩ := initPassH_sim (G := R.G0) R.order R.hu ⟨R.hu.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_hi
  exact ⟨⟨rfl, l1, u1⟩, i1, by omega⟩

lemma sim (t : ℕ) : SimR (rrunH delivV R.u R.hs0 t) (rrun delivCand R.u R.s0 t) :=
  (rrunH_sim delivV R.u R.init_sim.1 t).1

lemma nestedRun : NestedRun R.G0 delivCand R.u R.s0 := by
  intro t
  obtain ⟨a, b, c, d⟩ := R.nested t
  have hS := R.sim t
  have hl : (rrunH delivV R.u R.hs0 t).lo.val = (rrun delivCand R.u R.s0 t).lo.val := hS.lo.val
  have hh : (rrunH delivV R.u R.hs0 t).hi.val = (rrun delivCand R.u R.s0 t).hi.val := hS.hi.val
  refine ⟨a, ?_, c, ?_⟩
  · rw [← hl]; exact b
  · rw [← hh]; exact d

lemma order_deg_le : (R.order.map (fun g => (R.G0.children g).length)).sum ≤ live R.G0 := by
  rw [← List.sum_toFinset _ R.order_nodup]
  unfold live
  apply sum_le_sum_of_subset
  intro g hg
  rw [List.mem_toFinset] at hg
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (R.order_int g hg)
  exact mem_range.2 (R.wf.parent_lt c g ((R.wf.parents_iff c g).2 hc))

/-- **`prop:representation-cost` for one instance of the implemented engine.**

* Simulation and exactness: at every time the implemented engine has the same live circuit
  and stored values as the engine of `DagRetire.lean`, and the stored lower and upper
  values are exact valuations of the ORIGINAL circuit.
* Lower bound `P + S⁻ ≤ W`, obtained from the contract (`engineH_contract_lower`).
* Upper bound `W ≤ 12 (H + P + n + e + (S⁺ + e)(⌈log₂ D⌉ + 1))` (`eq:prop-rep-upper`).
* `S⁻ ≤ S⁺`, so the two bounds are tight up to the logarithmic factor when no incidence
  is retired. -/
theorem bounds :
    (∀ t, SimR (rrunH delivV R.u R.hs0 t) (rrun delivCand R.u R.s0 t)) ∧
    (∀ t, Exact R.G0 (rrunH delivV R.u R.hs0 t).lo.val ∧
      Exact R.G0 (rrunH delivV R.u R.hs0 t).hi.val) ∧
    R.Y ≤ R.W ∧ R.W ≤ 12 * R.X ∧ R.Sminus ≤ R.Splus := by
  obtain ⟨i1, i2, i3⟩ := R.init_sim
  have hn := R.nestedRun
  refine ⟨R.sim, fun t => ?_, ?_, ?_, ?_⟩
  · obtain ⟨e1, e2, _⟩ := rrun_exact i2 hn t
    have hS := R.sim t
    have hl : (rrunH delivV R.u R.hs0 t).lo.val = (rrun delivCand R.u R.s0 t).lo.val :=
      hS.lo.val
    have hh : (rrunH delivV R.u R.hs0 t).hi.val = (rrun delivCand R.u R.s0 t).hi.val :=
      hS.hi.val
    rw [hl, hh]
    exact ⟨e1, e2⟩
  · have := engineH_contract_lower delivV R.u i1 i2 hn R.τ R.P
    unfold Y W Sminus
    have h2 : ∑ t ∈ range R.τ, stepMinus (liftCand delivV) R.u R.s0 t
        = ∑ t ∈ range R.τ, stepMinus delivCand R.u R.s0 t := rfl
    omega
  · obtain ⟨_, r2, _, _⟩ := representation_cost_retire R.D R.deg i2 hn R.τ 0
    have hH : ∑ t ∈ range R.τ, stepCostH delivV R.u R.hs0 t
        ≤ 2 * ∑ t ∈ range R.τ, stepCost delivCand R.u R.s0 t := by
      rw [mul_sum]
      exact sum_le_sum (fun t _ => (rrunH_sim delivV R.u i1 t).2)
    have hinit := initCost_sum_le R.G0 R.D R.deg R.order
    have hdeg := R.order_deg_le
    have hlive : live R.s0.G = live R.G0 := rfl
    rw [hlive] at r2
    have hSp : ∑ t ∈ range R.τ, stepPlus delivCand R.u R.s0 t = R.Splus := rfl
    rw [hSp] at r2
    have h1 : (Nat.clog 2 R.D + 1) * (R.order.map (fun g => (R.G0.children g).length)).sum
        ≤ (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_right _ (hdeg.trans (Nat.le_add_left _ _))
    have key : ∀ (T A B n e P ci ch cs i : ℕ), 0 + cs ≤ 4 * (T + 0 + A) → ch ≤ 2 * cs →
        ci ≤ 4 * i → i ≤ n + B → B ≤ A → P + ci + ch ≤ 12 * (T + P + n + e + A) := by
      intros
      omega
    unfold W X
    exact key _ _ _ _ _ _ _ _ _ _ r2 hH i3 hinit h1
  · obtain ⟨_, _, r3, _⟩ := representation_cost_retire R.D R.deg i2 hn R.τ 0
    unfold Sminus Splus
    omega

end EngineRun

/-- **`prop:representation-cost`** (Unified Full-Cost Representation Comparison), as one
statement.  Let `RG i` be a family of instances of the retirement engine on implemented
heaps (direct graph maintenance), and let `WC i` be the work of any compiled
representation with lower expression `YC i = P_C + S_C⁻`.

1. Upper bound `eq:prop-rep-upper`: `W_G ≤ 12 (H + P_G + n_G + e_G + (S_G⁺ + e_G)(⌈log₂ D_G⌉ + 1))`
   for every instance.
2. Lower bound for the engine itself: `P_G + S_G⁻ ≤ W_G` for every instance, through the
   incidence-delivery contract.
3. Condition (R): if the compiled work satisfies its lower bound `YC = O(WC)` (which
   `DagRetire.contract_lower` gives for every implementation of the contract, and item 2
   for the engine) and `X_G = o(YC)`, then `W_G = o(WC)`. -/
theorem representation_cost_final {α ι : Type*} [LinearOrder α] [OrderBot α] {l : Filter ι}
    (RG : ι → EngineRun α) (WC YC : ι → ℝ) (hC : YC =O[l] WC) :
    (∀ i, (RG i).W ≤ 12 * (RG i).X) ∧
    (∀ i, (RG i).Y ≤ (RG i).W) ∧
    ((fun i => ((RG i).X : ℝ)) =o[l] YC → (fun i => ((RG i).W : ℝ)) =o[l] WC) := by
  refine ⟨fun i => (RG i).bounds.2.2.2.1, fun i => (RG i).bounds.2.2.1, fun hR => ?_⟩
  have hG : (fun i => ((RG i).W : ℝ)) =O[l] (fun i => ((RG i).X : ℝ)) := by
    apply IsBigO.of_bound 12
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (RG i).bounds.2.2.2.1
  exact Representation.representation_advantage hG hR hC

/-- **Condition (R) between two engine families**: the compiled representation `C` is
itself run by the engine on implemented heaps (on the compiled circuit).  If
`H + P_G + n_G + e_G + (S_G⁺ + e_G) log D_G = o(P_C + S_C⁻)` then `W_G = o(W_C)`. -/
theorem representation_cost_condition_R {α β ι : Type*} [LinearOrder α] [OrderBot α]
    [LinearOrder β] [OrderBot β] {l : Filter ι} (RG : ι → EngineRun α) (RC : ι → EngineRun β)
    (hR : (fun i => ((RG i).X : ℝ)) =o[l] (fun i => ((RC i).Y : ℝ))) :
    (fun i => ((RG i).W : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
  have hC : (fun i => ((RC i).Y : ℝ)) =O[l] (fun i => ((RC i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (RC i).bounds.2.2.1
  exact (representation_cost_final RG _ _ hC).2.2 hR

end Final

end EngineFinal
end JointRootCert
