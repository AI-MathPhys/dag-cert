/-
Joint Root Certification: `prop:representation-cost`, the upper bound `eq:prop-rep-upper`,
for the engine WITH release of orphaned gates, with `F_t` the root-reachable live
incidences, and with every part of the work computed.

Manuscript result covered:

* `prop:representation-cost` (Unified Full-Cost Representation Comparison), first sentence:
  `W_R = O(H + P_R + n_R + e_R + (S_R^+ + e_R) log D_R)` (`eq:prop-rep-upper`), with the
  definitions of `eq:s-plus-minus`.

## What is proved

The engine is the Graph-Selective engine of `RetireFinal.lean` on implemented heaps
(`RetireFinal.runH`): backup waves, strict-dominance retirement tests along the deliveries,
heap deletions, the reference-counted release cascade, and root queries with root-action
retirement.

1. **Completeness of the release cascade** (`releaseLoop_rooted`): with the fuel
   `RetireFinal.relFuel` the cascade empties its stack, and the invariant `Rooted` (every
   gate that still has live children has a live parent or is the gate of an active root
   action) is maintained by every rollout and every query (`runF_rooted`).  Hence every
   live incidence of the engine is reachable from the gate of an active root action
   through live incidences (`reach_of_rooted`), and the set `rrInc` of root-reachable live
   incidences EQUALS the live incidence set of the engine (`rrInc_eq_liveInc`).
2. **`S^+`** (`SelRun.Splus`) is defined as in `eq:s-plus-minus`:
   `Σ_{t<τ} Σ_{v<N} b_{t+1}(v) · d⁻_{F_t}(v)` with `F_t = rrInc` of the state immediately
   before the backup wave of rollout `t + 1`, `d⁻_F(v)` (`dIn`) the number of incidences
   of `F` with child `v`, and `b_{t+1}(v) ∈ {0, 1, 2}` (`SelRun.b`, `bChg`) the number of
   endpoints of `v` that change under EXACT evaluation of the original circuit.  The
   deliveries of the engine in rollout `t + 1` are exactly `Σ_v b_{t+1}(v) d⁻_{F_t}(v)`
   (`SelRun.volF_eq`).
3. **`W`** (`SelRun.W`) is `P + H` plus computed costs only: the two initialisation passes
   on implemented heaps, every rollout (waves, retirement tests, heap deletions, release
   cascade), every root query (leader scan, retirement scan, stop scan, release cascade),
   including the query at the stopping time, and the final disposal pass `disposeAll`
   (unlink every remaining live incidence, free every gate; one unit each).
4. `representation_cost_upper`:
   * unconditionally `W ≤ 12 (τ(L+3) + Q·K + H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))`,
     where `τ(L+3)` is the level scheduling of the waves and `Q·K` the root scans;
   * the manuscript's bound `W ≤ 13 (H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))` under the
     hypotheses that the shared work `h t` of every rollout is at least the circuit depth
     `L + 3`, and that the shared work at a time with a root query is at least `K`
     (the manuscript's `H` contains the root-action scans by definition).

## Differences from the manuscript (see the doc comment of the main theorem)

The manuscript's proof says that a terminal update changes each gate endpoint at most once
per wave.  This holds only if gates are processed in topological order; the implemented
wave processes level buckets `0..L` and pays `L + 3` per endpoint and rollout for it,
which `eq:prop-rep-upper` does not show.
-/
import JointRootCert.RetireFinal

namespace JointRootCert
namespace LiteralK3

open Finset CostEngines DagRetire EngineFinal RetireFinal
open HeapImpl (Heap HEState SimE)

/-! ## Completeness of the release cascade -/

section Complete

/-- **The reference-count invariant**: every gate that still has live children has a live
parent, or is protected, or is on the stack `st` of gates still to be examined. -/
def Rooted (prot : ℕ → Bool) (G : Dag) (st : List ℕ) : Prop :=
  ∀ g, G.children g ≠ [] → G.parents g ≠ [] ∨ prot g = true ∨ g ∈ st

lemma Rooted.mono {prot : ℕ → Bool} {G : Dag} {st st' : List ℕ} (h : Rooted prot G st)
    (hs : ∀ g ∈ st, g ∈ st') : Rooted prot G st' :=
  fun g hg => (h g hg).imp_right (fun h' => h'.imp_right (hs g))

/-- Releasing the gate on top of the stack: its children are pushed. -/
lemma rooted_release {prot : ℕ → Bool} {G : Dag} {g : ℕ} {st : List ℕ}
    (h : Rooted prot G (g :: st)) : Rooted prot (releaseDag G g) (G.children g ++ st) := by
  intro x hx
  have hch : (releaseDag G g).children x = if x = g then [] else G.children x := rfl
  have hxg : x ≠ g := by
    intro e
    rw [hch, ite_eq_left e] at hx
    exact hx rfl
  rw [hch, ite_eq_right hxg] at hx
  by_cases hm : x ∈ G.children g
  · exact Or.inr (Or.inr (List.mem_append_left _ hm))
  · rcases h x hx with h1 | h1 | h1
    · left
      have hpa : (releaseDag G g).parents x = G.parents x := by
        show (if x ∈ G.children g then (G.parents x).filter (· ≠ g) else G.parents x) = _
        rw [ite_eq_right hm]
      rw [hpa]
      exact h1
    · exact Or.inr (Or.inl h1)
    · right
      right
      rcases List.mem_cons.1 h1 with e | e
      · exact absurd e hxg
      · exact List.mem_append_right _ e

/-- **Completeness of the release cascade.**  With fuel at least
`2 · cells + |stack| + 1` (in particular with `RetireFinal.relFuel`), the cascade examines
its whole stack, and the result satisfies the reference-count invariant with an EMPTY
stack: no gate with live children is left without a live parent or protection. -/
theorem releaseLoop_rooted (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (G : Dag), G.WF →
    2 * cells G + st.length + 1 ≤ f → Rooted prot G st →
    Rooted prot (releaseLoop prot f st G).1 [] := by
  intro f
  induction f with
  | zero => intro st G _ hf _; omega
  | succ f ih =>
    intro st G hG hf h
    cases st with
    | nil => exact h
    | cons g st =>
      rw [releaseLoop]
      rw [List.length_cons] at hf
      by_cases hc : G.children g ≠ [] ∧ G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc]
        obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc.1
        have hgN : g < G.N := hG.parent_lt c g ((hG.parents_iff c g).2 hcm)
        have hcell := cells_release hgN hc.1
        refine ih _ _ (releaseDag_wf hG g) ?_ (rooted_release h)
        rw [List.length_append]
        omega
      · rw [ite_eq_right hc]
        refine ih st G hG (by omega) ?_
        intro x hx
        rcases h x hx with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · rcases List.mem_cons.1 h1 with e | e
          · rw [e] at hx ⊢
            by_cases hp : G.parents g = []
            · right
              left
              cases hb : prot g with
              | true => rfl
              | false => exact absurd ⟨hx, hp, hb⟩ hc
            · exact Or.inl hp
          · exact Or.inr (Or.inr e)

variable {α : Type*} [LinearOrder α] [OrderBot α]

omit [OrderBot α] in
/-- A retirement test of `(p, c)`: the only gate that may lose its last parent is `c`. -/
lemma rooted_retireOne {prot : ℕ → Bool} (e : ℕ × ℕ) (s : RState α) {st : List ℕ}
    (h : Rooted prot s.G st) : Rooted prot (retireOne e s).1.G (e.2 :: st) := by
  unfold retireOne
  split_ifs with hc
  · show Rooted prot (retireDag s.G e.1 e.2) (e.2 :: st)
    intro x hx
    have hx' : s.G.children x ≠ [] := by
      intro e'
      have hsub := retire_children_sublist s.G e.1 e.2 x
      rw [e'] at hsub
      exact hx (List.sublist_nil.1 hsub)
    by_cases hxe : x = e.2
    · exact Or.inr (Or.inr (hxe ▸ List.mem_cons_self))
    · rcases h x hx' with h1 | h1 | h1
      · left
        have hpa : (retireDag s.G e.1 e.2).parents x = s.G.parents x := by
          show (if x = e.2 then (s.G.parents x).filter (· ≠ e.1) else s.G.parents x) = _
          rw [ite_eq_right hxe]
        rw [hpa]
        exact h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h1))
  · exact h.mono (fun g hg => List.mem_cons_of_mem _ hg)

omit [OrderBot α] in
lemma rooted_retireList {prot : ℕ → Bool} : ∀ (L : List (ℕ × ℕ)) (s : RState α)
    (st : List ℕ), Rooted prot s.G st →
    Rooted prot (retireList L s).1.G (L.map Prod.snd ++ st) := by
  intro L
  induction L with
  | nil => intro s st h; exact h
  | cons e es ih =>
    intro s st h
    have h1 := ih (retireOne e s).1 (e.2 :: st) (rooted_retireOne e s h)
    show Rooted prot (retireList es (retireOne e s).1).1.G _
    refine h1.mono ?_
    intro g hg
    simp only [List.map_cons, List.mem_append, List.mem_cons, List.cons_append] at hg ⊢
    tauto

lemma protOf_true {K : ℕ} {rt : ℕ → ℕ} {act : ℕ → Bool} {g : ℕ}
    (h : protOf K rt act g = true) : ∃ i, i < K ∧ act i = true ∧ rt i = g := by
  unfold protOf at h
  rw [List.any_eq_true] at h
  obtain ⟨i, hi, hb⟩ := h
  rw [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨i, List.mem_range.1 hi, hb.1, hb.2⟩

lemma protOf_intro {K : ℕ} {rt : ℕ → ℕ} {act : ℕ → Bool} {g i : ℕ} (hi : i < K)
    (ha : act i = true) (hrt : rt i = g) : protOf K rt act g = true := by
  unfold protOf
  rw [List.any_eq_true]
  exact ⟨i, List.mem_range.2 hi, by simp [ha, hrt]⟩

/-- **One rollout preserves the reference-count invariant**: after the retirement pass the
gates that may have lost their last parent are the children of the tested incidences,
which is the stack the cascade starts from. -/
theorem rooted_relStep (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ))
    (u : ℕ × α × α) (s : QS α) (hG : s.r.G.WF) (h : Rooted (protOf K rt s.act) s.r.G []) :
    (relStep K rt cand u s).1.r.G.WF ∧
    Rooted (protOf K rt (relStep K rt cand u s).1.act) (relStep K rt cand u s).1.r.G [] := by
  have hwfw : (waveStep u s.r).1.G.WF := hG
  obtain ⟨g1, _, _⟩ := retireList_G (cand s.r (waveStep u s.r).1) (waveStep u s.r).1 hwfw
  have hr : Rooted (protOf K rt s.act) (rstep cand u s.r).1.G
      ((cand s.r (waveStep u s.r).1).map Prod.snd) := by
    have h1 := rooted_retireList (prot := protOf K rt s.act) (cand s.r (waveStep u s.r).1)
      (waveStep u s.r).1 [] h
    rw [List.append_nil] at h1
    exact h1
  exact ⟨(releaseLoop_spec _ _ _ _ g1).1,
    releaseLoop_rooted _ _ _ _ g1 (le_of_eq rfl) hr⟩

omit [OrderBot α] in
/-- **A root query with root-action retirement preserves the reference-count invariant**:
the gates that lose their protection are the gates of the retired actions, which is the
stack the cascade starts from. -/
theorem rooted_qRetire (K : ℕ) (rt : ℕ → ℕ) (s : QS α) (hG : s.r.G.WF)
    (h : Rooted (protOf K rt s.act) s.r.G []) :
    Rooted (protOf K rt (qRetire K rt s).1.act) (qRetire K rt s).1.r.G [] := by
  unfold qRetire
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => exact h
  | some a =>
    refine releaseLoop_rooted
      (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)) _
      (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act) s.r.G hG
      (le_of_eq rfl) ?_
    intro x hx
    rcases h x hx with h1 | h1 | h1
    · exact Or.inl h1
    · obtain ⟨i, hi, ha, hrt⟩ := protOf_true h1
      cases hd : deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act i with
      | true => exact Or.inr (Or.inl (protOf_intro hi hd hrt))
      | false =>
        right
        right
        have h2 := (deact_false_iff K a _ _ s.act i ha).1 hd
        unfold retiredRoots
        rw [List.mem_map]
        exact ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, decide_eq_true ⟨ha, h2.2⟩⟩, hrt⟩
    · simp at h1

/-- **The reference-count invariant along the run**, for the states after each rollout
(`runF`) and for the states on which the next rollout acts (`preF`, after the query). -/
theorem runF_rooted (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ))
    (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : QS α) (hG : s0.r.G.WF)
    (h0 : Rooted (protOf K rt s0.act) s0.r.G []) : ∀ t,
    ((runF K rt cand u q s0 t).r.G.WF ∧
      Rooted (protOf K rt (runF K rt cand u q s0 t).act) (runF K rt cand u q s0 t).r.G []) ∧
    ((preF K rt cand u q s0 t).r.G.WF ∧
      Rooted (protOf K rt (preF K rt cand u q s0 t).act) (preF K rt cand u q s0 t).r.G []) := by
  have hpre : ∀ t, ((runF K rt cand u q s0 t).r.G.WF ∧
      Rooted (protOf K rt (runF K rt cand u q s0 t).act) (runF K rt cand u q s0 t).r.G []) →
      ((preF K rt cand u q s0 t).r.G.WF ∧
      Rooted (protOf K rt (preF K rt cand u q s0 t).act) (preF K rt cand u q s0 t).r.G []) := by
    intro t ht
    unfold preF
    by_cases hq : q t = true
    · rw [ite_eq_left hq]
      exact ⟨(qRetire_cost (K := K) (rt := rt) ht.1).1, rooted_qRetire K rt _ ht.1 ht.2⟩
    · rw [ite_eq_right hq]
      exact ht
  have hrun : ∀ t, ((runF K rt cand u q s0 t).r.G.WF ∧
      Rooted (protOf K rt (runF K rt cand u q s0 t).act) (runF K rt cand u q s0 t).r.G []) := by
    intro t
    induction t with
    | zero => exact ⟨hG, h0⟩
    | succ t ih =>
      have hp := hpre t ih
      exact rooted_relStep K rt cand (u (t + 1)) (preF K rt cand u q s0 t) hp.1 hp.2
  exact fun t => ⟨hrun t, hpre t (hrun t)⟩

/-- **Root-reachability in the live circuit**: a gate is reachable if it is the gate of an
active root action, or a live child of a reachable gate. -/
inductive Reach (G : Dag) (K : ℕ) (rt : ℕ → ℕ) (act : ℕ → Bool) : ℕ → Prop
  | root (i : ℕ) (hi : i < K) (ha : act i = true) : Reach G K rt act (rt i)
  | step (p c : ℕ) (hp : Reach G K rt act p) (hc : c ∈ G.children p) : Reach G K rt act c

/-- Under the reference-count invariant with an empty stack, every gate with live children
is root-reachable (induction on the level, downwards from `L`). -/
theorem reach_of_rooted {G : Dag} (hG : G.WF) {K : ℕ} {rt : ℕ → ℕ} {act : ℕ → Bool}
    (h : Rooted (protOf K rt act) G []) :
    ∀ g, G.children g ≠ [] → Reach G K rt act g := by
  have key : ∀ n g, G.L - G.level g < n → G.children g ≠ [] → Reach G K rt act g := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg hc
      rcases h g hc with h1 | h1 | h1
      · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h1
        have hcp := (hG.parents_iff g p).1 hp
        have h2 := hG.level_lt p g hcp
        have h3 := hG.level_le p
        exact Reach.step p g (ih p (by omega) (List.ne_nil_of_mem hcp)) hcp
      · obtain ⟨i, hi, ha, hrt⟩ := protOf_true h1
        exact hrt ▸ Reach.root i hi ha
      · simp at h1
  exact fun g => key (G.L - G.level g + 1) g (Nat.lt_succ_self _)

open Classical in
/-- **The root-reachable live incidences** of a live circuit `G` with active root actions
`act`: the live incidences `(p, c)` whose parent `p` is root-reachable. -/
noncomputable def rrInc (G : Dag) (K : ℕ) (rt : ℕ → ℕ) (act : ℕ → Bool) : Finset (ℕ × ℕ) :=
  (liveInc G).filter (fun e => Reach G K rt act e.1)

open Classical in
/-- Under the reference-count invariant the live incidences are exactly the root-reachable
live incidences. -/
theorem rrInc_eq_liveInc {G : Dag} (hG : G.WF) {K : ℕ} {rt : ℕ → ℕ} {act : ℕ → Bool}
    (h : Rooted (protOf K rt act) G []) : rrInc G K rt act = liveInc G := by
  unfold rrInc
  exact filter_true_of_mem
    (fun e he => reach_of_rooted hG h e.1 (List.ne_nil_of_mem (mem_filter.1 he).2))

end Complete

/-! ## Delivery volumes as in `eq:s-plus-minus` -/

section Volume

variable {α : Type*} [DecidableEq α]

/-- `d⁻_F(v)`: the number of incidences `(p, v)` in `F` (the active incoming parent degree
of gate `v` in the incidence set `F`). -/
def dIn (F : Finset (ℕ × ℕ)) (v : ℕ) : ℕ := (F.filter (fun e => e.2 = v)).card

/-- `b(v) ∈ {0, 1, 2}`: the number of interval endpoints of gate `v` that differ between
the valuations `(lo0, hi0)` and `(lo1, hi1)`. -/
def bChg (lo0 hi0 lo1 hi1 : ℕ → α) (v : ℕ) : ℕ :=
  (if lo1 v ≠ lo0 v then 1 else 0) + (if hi1 v ≠ hi0 v then 1 else 0)

lemma bChg_le_two (lo0 hi0 lo1 hi1 : ℕ → α) (v : ℕ) : bChg lo0 hi0 lo1 hi1 v ≤ 2 := by
  unfold bChg
  split_ifs <;> omega

/-- One wave's delivery volume `Σ_{v < N} b(v) · d⁻_F(v)`. -/
def delivVol (N : ℕ) (F : Finset (ℕ × ℕ)) (b : ℕ → ℕ) : ℕ := ∑ v ∈ range N, b v * dIn F v

/-- In the live incidence set of a circuit, `d⁻(v)` is the length of the parent list. -/
lemma dIn_liveInc {G : Dag} (hG : G.WF) {v : ℕ} (hv : v < G.N) :
    dIn (liveInc G) v = (G.parents v).length := by
  unfold dIn
  rw [card_filter]
  refine (sum_liveInc hG (fun g => if g = v then 1 else 0)).trans ?_
  rw [sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => absurd (mem_range.2 hv) h)]
  simp

end Volume

/-! ## Final disposal -/

section Dispose

/-- **Final disposal pass**: for every gate of the list, unlink each of its remaining
child incidences (one unit each; the heap entries go with them) and free the gate (one
unit). -/
def disposeAll : List ℕ → Dag → Dag × ℕ
  | [], G => (G, 0)
  | g :: gs, G =>
    ((disposeAll gs (releaseDag G g)).1,
     (disposeAll gs (releaseDag G g)).2 + 1 + (G.children g).length)

lemma live_release {G : Dag} {g : ℕ} (hg : g < G.N) :
    live (releaseDag G g) + (G.children g).length = live G := by
  have hp : g ∈ range G.N := mem_range.2 hg
  unfold live
  show ∑ p ∈ range G.N, ((releaseDag G g).children p).length + _ = _
  rw [← add_sum_erase _ (fun p => ((releaseDag G g).children p).length) hp,
    ← add_sum_erase _ (fun p => (G.children p).length) hp]
  have h1 : ∑ p ∈ (range G.N).erase g, ((releaseDag G g).children p).length
      = ∑ p ∈ (range G.N).erase g, (G.children p).length := by
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
  rw [h1, h2]
  simp only [List.length_nil]
  omega

/-- The disposal pass costs one unit per gate of the list plus one unit per incidence it
unlinks. -/
lemma disposeAll_cost : ∀ (gs : List ℕ) (G : Dag), (∀ g ∈ gs, g < G.N) →
    (disposeAll gs G).2 + live (disposeAll gs G).1 = gs.length + live G := by
  intro gs
  induction gs with
  | nil => intro G _; simp [disposeAll]
  | cons g gs ih =>
    intro G hgs
    have h1 := ih (releaseDag G g) (fun x hx => hgs x (List.mem_cons_of_mem _ hx))
    have h2 := live_release (hgs g List.mem_cons_self)
    show (disposeAll gs (releaseDag G g)).2 + 1 + (G.children g).length
      + live (disposeAll gs (releaseDag G g)).1 = (gs.length + 1) + live G
    omega

lemma disposeAll_children : ∀ (gs : List ℕ) (G : Dag) (p : ℕ),
    (disposeAll gs G).1.children p = if p ∈ gs then [] else G.children p := by
  intro gs
  induction gs with
  | nil => intro G p; simp [disposeAll]
  | cons g gs ih =>
    intro G p
    have h1 : (disposeAll (g :: gs) G).1 = (disposeAll gs (releaseDag G g)).1 := rfl
    have h2 : (releaseDag G g).children p = if p = g then [] else G.children p := rfl
    rw [h1, ih, h2]
    by_cases a : p ∈ gs <;> by_cases b : p = g <;> simp [a, b]

/-- After the disposal pass over all gates no incidence is left. -/
lemma disposeAll_empty {G : Dag} (hG : G.WF) (p : ℕ) :
    (disposeAll (List.range G.N) G).1.children p = [] := by
  rw [disposeAll_children]
  by_cases hp : p ∈ List.range G.N
  · rw [ite_eq_left hp]
  · rw [ite_eq_right hp]
    by_contra hne
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    exact hp (List.mem_range.2 (hG.parent_lt c p ((hG.parents_iff c p).2 hc)))

lemma live_le_cells (G : Dag) : live G ≤ cells G := by
  unfold live cells
  exact sum_le_sum (fun p _ => Nat.le_add_right _ _)

end Dispose

/-! ## The root scans as costed programs

`RetireFinal.qRetire` charges `K` for the leader scan and `K` for the retirement scan, and
`RetireFinal.costF` / `costH` charge `K` for the stop scan.  The three scans are written
here as costed programs (one unit per root index, the cost produced by the same recursion
as the result); their results are the values used by `qRetire` / `qOut` and their computed
costs are the charges `K`. -/

section ScanCost

variable {α : Type*} [LinearOrder α]

/-- Costed leader scan. -/
def leadScanC (L : ℕ → α) (act : ℕ → Bool) : ℕ → Option ℕ × ℕ
  | 0 => (none, 0)
  | n + 1 =>
    ((leadScanC L act n).1.elim (if act n = true then some n else none)
        (fun a => if act n = true ∧ L a < L n then some n else some a),
     (leadScanC L act n).2 + 1)

lemma leadScanC_spec (L : ℕ → α) (act : ℕ → Bool) :
    ∀ n, leadScanC L act n = (leadScan L act n, n)
  | 0 => rfl
  | n + 1 => by
    rw [leadScanC, leadScanC_spec L act n]
    rfl

/-- Costed retirement scan: the gates of the root actions to deactivate. -/
def retScanC (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) : ℕ → List ℕ × ℕ
  | 0 => ([], 0)
  | n + 1 =>
    ((retScanC rt a U la act n).1
        ++ (if act n = true ∧ n ≠ a ∧ U n < la then [rt n] else []),
     (retScanC rt a U la act n).2 + 1)

lemma retScanC_spec (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) :
    ∀ n, retScanC rt a U la act n = (retiredRoots n rt a U la act, n)
  | 0 => by simp [retScanC, retiredRoots]
  | n + 1 => by
    rw [retScanC, retScanC_spec rt a U la act n]
    unfold retiredRoots
    rw [List.range_succ, List.filter_append, List.map_append]
    by_cases h : act n = true ∧ n ≠ a ∧ U n < la <;> simp [h]

/-- Costed stop scan. -/
noncomputable def stopScanC (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ)
    (act : ℕ → Bool) : ℕ → Bool × ℕ
  | 0 => (true, 0)
  | n + 1 =>
    ((stopScanC φ ε U la a act n).1
        && (!(act n) || decide (n = a) || decide (φ (U n) - φ la ≤ ε)),
     (stopScanC φ ε U la a act n).2 + 1)

omit [LinearOrder α] in
lemma stopScanC_spec (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ) (act : ℕ → Bool) :
    ∀ n, stopScanC φ ε U la a act n = (stopScan φ ε U la a act n, n)
  | 0 => rfl
  | n + 1 => by
    rw [stopScanC, stopScanC_spec φ ε U la a act n]
    rfl

end ScanCost

/-! ## The run, `W`, `S^+`, and `eq:prop-rep-upper` -/

section Final

open Asymptotics

/-- **An instance of the Graph-Selective engine with release** (data of one run).

* `G0`: the monitor circuit, of maximum gate degree at most `D`; `order` lists its internal
  gates by nondecreasing level (the order of the initialisation pass).
* `hl`, `hu`: the initial terminal intervals (values at the leaves) with empty heaps.
* `K`, `rt`: the root actions `i < K` and their gates `rt i`.
* `u`: the terminal updates (`u (t + 1) = (x, l, u)` is the update of rollout `t + 1`);
  `q t`: whether a root query (with root-action retirement) is made after rollout `t`;
  `τ`: the stopping time (number of rollouts).
* `P`: upfront compiler work (a given number, as in the manuscript).
* `h t`: the shared work at time `t ≤ τ` (rollout selection, reward sampling and terminal
  interval intersection of rollout `t + 1`, and the root-action scan of the query at time
  `t`); a given function, as the manuscript's `H`.

Structural conditions on the input: well-formedness, child lists without repetition,
`leaf` (initial terminal intervals nonempty), `rooted` (every internal gate without a
parent is the gate of a root action), and `nested` (the terminal updates are cumulative
intersections: nested and nonempty with respect to the exact evaluation of `G0`,
`eq:terminal-box`). -/
structure SelRun (α : Type*) [LinearOrder α] [OrderBot α] where
  G0 : Dag
  D : ℕ
  order : List ℕ
  hl : HEState α
  hu : HEState α
  K : ℕ
  rt : ℕ → ℕ
  u : ℕ → ℕ × α × α
  q : ℕ → Bool
  τ : ℕ
  P : ℕ
  h : ℕ → ℕ
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
  rooted : ∀ g, G0.children g ≠ [] → G0.parents g ≠ [] ∨ ∃ i, i < K ∧ rt i = g
  nested : NestedRun G0 noCand u
    ⟨G0, (initPass G0 order ⟨hl.val, fun _ _ => ⊥⟩).1,
      (initPass G0 order ⟨hu.val, fun _ _ => ⊥⟩).1⟩

namespace SelRun

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α)

/-- Initialised lower-endpoint state (abstract engine). -/
def lo0 : EState α := (initPass R.G0 R.order ⟨R.hl.val, fun _ _ => ⊥⟩).1

/-- Initialised upper-endpoint state (abstract engine). -/
def hi0 : EState α := (initPass R.G0 R.order ⟨R.hu.val, fun _ _ => ⊥⟩).1

/-- Initial state of the abstract Graph-Selective engine: all root actions active. -/
def s0 : QS α := ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩

/-- Initial state of the engine on implemented heaps, produced by `initPassH`. -/
def hq0 : HQS α :=
  ⟨⟨R.G0, (initPassH R.G0 R.order R.hl).1, (initPassH R.G0 R.order R.hu).1⟩, fun _ => true⟩

/-- Abstract state after `t` rollouts. -/
def run (t : ℕ) : QS α := runF R.K R.rt delivCand R.u R.q R.s0 t

/-- Abstract state immediately before the backup wave of rollout `t + 1` (after the query
of time `t`, if any). -/
def pre (t : ℕ) : QS α := preF R.K R.rt delivCand R.u R.q R.s0 t

/-- State of the engine on implemented heaps after `t` rollouts. -/
def hrun (t : ℕ) : HQS α := runH R.K R.rt delivV R.u R.q R.hq0 t

/-- State of the engine on implemented heaps immediately before the backup wave of rollout
`t + 1`. -/
def hpre (t : ℕ) : HQS α :=
  if R.q t = true then (qRetireH R.K R.rt (R.hrun t)).1 else R.hrun t

/-- Exact lower endpoints of all gates of the ORIGINAL circuit after `t` rollouts (the
engine without retirement on the full circuit; `Exact G0` by `representation_cost_upper`). -/
def refLo (t : ℕ) : ℕ → α := (rrun noCand R.u ⟨R.G0, R.lo0, R.hi0⟩ t).lo.val

/-- Exact upper endpoints of all gates of the original circuit after `t` rollouts. -/
def refHi (t : ℕ) : ℕ → α := (rrun noCand R.u ⟨R.G0, R.lo0, R.hi0⟩ t).hi.val

/-- `b_{t+1}(v) ∈ {0, 1, 2}`: the number of interval endpoints of gate `v` that change
under exact evaluation of the terminal update of rollout `t + 1`. -/
def b (t v : ℕ) : ℕ := bChg (R.refLo t) (R.refHi t) (R.refLo (t + 1)) (R.refHi (t + 1)) v

/-- `F_t`: the root-reachable live incidences immediately before the backup wave of
rollout `t + 1`. -/
noncomputable def F (t : ℕ) : Finset (ℕ × ℕ) := rrInc (R.pre t).r.G R.K R.rt (R.pre t).act

/-- **`S^+` of `eq:s-plus-minus`**: `Σ_{t<τ} Σ_{v<N} b_{t+1}(v) · d⁻_{F_t}(v)`. -/
noncomputable def Splus : ℕ := ∑ t ∈ range R.τ, delivVol R.G0.N (R.F t) (R.b t)

/-- `H`: the shared work through `τ`. -/
def H : ℕ := ∑ t ∈ range (R.τ + 1), R.h t

/-- Number of root indices covered by one scan at each query time `t ≤ τ` (`Q · K`). -/
def scans : ℕ := ∑ t ∈ range (R.τ + 1), if R.q t = true then R.K else 0

/-- Computed cost of the two initialisation passes on implemented heaps. -/
def Winit : ℕ := (initPassH R.G0 R.order R.hl).2 + (initPassH R.G0 R.order R.hu).2

/-- Computed cost of the `τ` rollouts and of the queries at the times `t < τ`. -/
def Wroll : ℕ := ∑ t ∈ range R.τ, costH R.K R.rt delivV R.u R.q R.hq0 t

/-- Computed cost of the query at the stopping time `τ` (if `q τ`): stop scan, leader scan,
retirement scan and release cascade. -/
def Wlast : ℕ := if R.q R.τ = true then R.K + (qRetireH R.K R.rt (R.hrun R.τ)).2 else 0

/-- Computed cost of the final disposal pass over all gates. -/
def Wdisp : ℕ := (disposeAll (List.range R.G0.N) (R.hpre R.τ).r.G).2

/-- **Total scalar work `W_R`**: the two given quantities `P` (upfront compiler passes) and
`H` (shared work), plus the computed costs of initialisation, of all rollouts and queries,
and of final disposal. -/
def W : ℕ := R.P + R.H + R.Winit + R.Wroll + R.Wlast + R.Wdisp

/-- The right side of `eq:prop-rep-upper`: `H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1)`, with
`n` the number of gates and `e` the number of incidences of the circuit. -/
noncomputable def X : ℕ :=
  R.H + R.P + R.G0.N + live R.G0 + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)

/-- The right side with the two terms the manuscript does not show: level scheduling
`τ(L + 3)` and root scans `Q · K`. -/
noncomputable def X1 : ℕ := R.τ * (R.G0.L + 3) + R.scans + R.X

lemma init_facts :
    SimR ⟨R.G0, (initPassH R.G0 R.order R.hl).1, (initPassH R.G0 R.order R.hu).1⟩
      ⟨R.G0, R.lo0, R.hi0⟩ ∧ RInv R.G0 ⟨R.G0, R.lo0, R.hi0⟩ ∧
    R.Winit ≤ 4 * (R.order.map (initCost R.G0)).sum := by
  obtain ⟨i1, i2⟩ := init_engine R.wf R.order (⟨R.hl.val, fun _ _ => ⊥⟩ : EState α)
    ⟨R.hu.val, fun _ _ => ⊥⟩ R.order_all R.order_int R.order_sorted R.leaf
  obtain ⟨l1, l2⟩ := initPassH_sim (G := R.G0) R.order R.hl ⟨R.hl.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_lo
  obtain ⟨u1, u2⟩ := initPassH_sim (G := R.G0) R.order R.hu ⟨R.hu.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_hi
  refine ⟨⟨rfl, l1, u1⟩, i1, ?_⟩
  unfold Winit
  omega

lemma hn : NestedRun R.G0 noCand R.u ⟨R.G0, R.lo0, R.hi0⟩ := R.nested

lemma rooted0 : Rooted (protOf R.K R.rt R.s0.act) R.s0.r.G [] := by
  intro g hg
  rcases R.rooted g hg with h1 | ⟨i, hi, hrt⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl (protOf_intro hi rfl hrt))

lemma rooted_all (t : ℕ) :
    ((R.run t).r.G.WF ∧ Rooted (protOf R.K R.rt (R.run t).act) (R.run t).r.G []) ∧
    ((R.pre t).r.G.WF ∧ Rooted (protOf R.K R.rt (R.pre t).act) (R.pre t).r.G []) :=
  runF_rooted R.K R.rt delivCand R.u R.q R.s0 R.wf R.rooted0 t

lemma sim_run (t : ℕ) : SimQ (R.hrun t) (R.run t) ∧
    costH R.K R.rt delivV R.u R.q R.hq0 t ≤ 2 * costF R.K R.rt delivCand R.u R.q R.s0 t :=
  runH_sim (K := R.K) (rt := R.rt) delivV R.u R.q (hs0 := R.hq0) (s0 := R.s0)
    ⟨R.init_facts.1, rfl⟩ t

lemma sim_pre (t : ℕ) : SimQ (R.hpre t) (R.pre t) := by
  unfold hpre pre preF
  by_cases hq : R.q t = true
  · rw [ite_eq_left hq, ite_eq_left hq]
    exact (qRetireH_sim R.K R.rt (R.sim_run t).1).1
  · rw [ite_eq_right hq, ite_eq_right hq]
    exact (R.sim_run t).1

lemma pre_inv (t : ℕ) :
    CInv R.G0 R.K R.rt (R.pre t).r (R.pre t).act (R.refLo t) (R.refHi t) :=
  preF_inv (K := R.K) (rt := R.rt) (cand := delivCand) (q := R.q) (act0 := fun _ => true)
    R.wf R.init_facts.2.1 R.hn t

/-- **`F_t` is the live incidence set of the engine**: every live incidence is
root-reachable (and conversely by definition). -/
lemma F_eq (t : ℕ) : R.F t = liveInc (R.pre t).r.G :=
  rrInc_eq_liveInc (R.rooted_all t).2.1 (R.rooted_all t).2.2

/-- **The deliveries of rollout `t + 1` are `Σ_v b_{t+1}(v) d⁻_{F_t}(v)`**: the engine's
delivery count `RetireFinal.volF` (one delivery per changed endpoint of a gate and live
parent incidence of that gate) equals the summand of `S^+` in `eq:s-plus-minus`, with `b`
computed by exact evaluation of the original circuit and `F_t` the root-reachable live
incidences. -/
lemma volF_eq (t : ℕ) :
    volF R.K R.rt delivCand R.u R.q R.s0 t = delivVol R.G0.N (R.F t) (R.b t) := by
  have i2 := R.init_facts.2.1
  have hn := R.hn
  have hpre := R.pre_inv t
  obtain ⟨_, f2, f3, f4, f5, f6⟩ := ref_facts R.wf i2 hn t
  obtain ⟨f1', _⟩ := ref_facts R.wf i2 hn (t + 1)
  have hw := hpre.wave f1' (R.u (t + 1)) f2 f3 f4 f5 f6
  obtain ⟨e1, e2, _⟩ := rstep_endpoints delivCand (R.u (t + 1)) (R.pre t).r
  have elo : (runF R.K R.rt delivCand R.u R.q R.s0 (t + 1)).r.lo
      = (waveStep (R.u (t + 1)) (R.pre t).r).1.lo := e1
  have ehi : (runF R.K R.rt delivCand R.u R.q R.s0 (t + 1)).r.hi
      = (waveStep (R.u (t + 1)) (R.pre t).r).1.hi := e2
  have hnd : ∀ g, (R.pre t).r.G.parents g ≠ [] → ¬ Dead R.G0 (R.pre t).r.G g := by
    intro g hg
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hg
    exact hpre.live_child p g ((hpre.wf.parents_iff g p).1 hp)
  show vol (R.pre t).r.G (R.pre t).r.lo (runF R.K R.rt delivCand R.u R.q R.s0 (t + 1)).r.lo
    + vol (R.pre t).r.G (R.pre t).r.hi (runF R.K R.rt delivCand R.u R.q R.s0 (t + 1)).r.hi = _
  rw [elo, ehi, vol_eq_sum, vol_eq_sum, hpre.nEq, ← sum_add_distrib]
  unfold delivVol
  apply sum_congr rfl
  intro g hg
  have hgN : g < (R.pre t).r.G.N := by rw [hpre.nEq]; exact mem_range.1 hg
  rw [R.F_eq t, dIn_liveInc hpre.wf hgN]
  by_cases hp : (R.pre t).r.G.parents g = []
  · rw [hp]
    simp
  · have nd := hnd g hp
    rw [(hpre.agree g nd).1, (hpre.agree g nd).2, (hw.agree g nd).1, (hw.agree g nd).2]
    exact (Nat.add_mul _ _ _).symm

lemma order_deg_le : (R.order.map (fun g => (R.G0.children g).length)).sum ≤ live R.G0 := by
  rw [← List.sum_toFinset _ R.order_nodup]
  unfold live
  apply sum_le_sum_of_subset
  intro g hg
  rw [List.mem_toFinset] at hg
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (R.order_int g hg)
  exact mem_range.2 (R.wf.parent_lt c g ((R.wf.parents_iff c g).2 hc))

lemma order_length_le : R.order.length ≤ R.G0.N := by
  rw [← List.toFinset_card_of_nodup R.order_nodup]
  have hsub : R.order.toFinset ⊆ range R.G0.N := by
    intro g hg
    rw [List.mem_toFinset] at hg
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (R.order_int g hg)
    exact mem_range.2 (R.wf.parent_lt c g ((R.wf.parents_iff c g).2 hc))
  exact (card_le_card hsub).trans (by simp)

/-- The explicit work bound, before grouping into the form of `eq:prop-rep-upper`. -/
lemma work_le :
    R.W ≤ R.P + R.H + 9 * R.G0.N + 4 * live R.G0 + 8 * R.scans + 4 * (R.τ * (R.G0.L + 3))
      + 2 * ((Nat.clog 2 R.D + 5) * R.Splus) + (8 * Nat.clog 2 R.D + 12) * live R.G0 := by
  obtain ⟨_, i2, i3⟩ := R.init_facts
  have hn := R.hn
  have hlw : ∑ t ∈ range R.τ, costF R.K R.rt delivCand R.u R.q R.s0 t
        + 2 * cells (R.run R.τ).r.G
      ≤ ((range R.τ).filter (fun t => R.q t = true)).card * (4 * R.K)
        + 2 * R.τ * (R.G0.L + 3)
        + (Nat.clog 2 R.D + 3) * ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t
        + 2 * ∑ t ∈ range R.τ, testsF R.K R.rt delivCand R.u R.q R.s0 t
        + (2 * Nat.clog 2 R.D + 4) * ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t
        + 2 * cells R.G0 :=
    live_work (K := R.K) (rt := R.rt) (cand := delivCand) (q := R.q)
      (act0 := fun _ => true) R.wf R.D R.deg i2 hn R.τ
  have hret : ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t
      + live (R.run R.τ).r.G ≤ live R.G0 :=
    retF_sum_le (K := R.K) (rt := R.rt) (cand := delivCand) (q := R.q)
      (act0 := fun _ => true) R.wf i2 hn R.τ
  have htests : ∑ t ∈ range R.τ, testsF R.K R.rt delivCand R.u R.q R.s0 t
      ≤ ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t :=
    sum_le_sum (fun t _ => tests_le_vol _ t)
  have hvol : ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus :=
    sum_congr rfl (fun t _ => R.volF_eq t)
  have hcells := cells_le R.G0
  have hroll : R.Wroll ≤ 2 * ∑ t ∈ range R.τ, costF R.K R.rt delivCand R.u R.q R.s0 t := by
    unfold Wroll
    rw [mul_sum]
    exact sum_le_sum (fun t _ => (R.sim_run t).2)
  have hlast : R.Wlast + 2 * cells (R.pre R.τ).r.G
      ≤ 4 * (if R.q R.τ = true then R.K else 0) + 2 * cells (R.run R.τ).r.G := by
    unfold Wlast pre preF
    by_cases hq : R.q R.τ = true
    · rw [ite_eq_left hq, ite_eq_left hq, ite_eq_left hq]
      have h1 := (qRetireH_sim R.K R.rt (R.sim_run R.τ).1).2
      have h2 := (qRetire_cost (K := R.K) (rt := R.rt) (R.rooted_all R.τ).1.1).2.2.2
      rw [h1]
      have h3 : (qRetire R.K R.rt (R.run R.τ)).2
          + 2 * cells (qRetire R.K R.rt (R.run R.τ)).1.r.G
          ≤ 3 * R.K + 2 * cells (R.run R.τ).r.G := h2
      show R.K + (qRetire R.K R.rt (R.run R.τ)).2
          + 2 * cells (qRetire R.K R.rt (R.run R.τ)).1.r.G
        ≤ 4 * R.K + 2 * cells (R.run R.τ).r.G
      omega
    · rw [ite_eq_right hq, ite_eq_right hq, ite_eq_right hq]
      show 0 + 2 * cells (R.run R.τ).r.G ≤ 4 * 0 + 2 * cells (R.run R.τ).r.G
      omega
  have hdisp : R.Wdisp ≤ R.G0.N + cells (R.pre R.τ).r.G := by
    have hG : (R.hpre R.τ).r.G = (R.pre R.τ).r.G := (R.sim_pre R.τ).r.G
    have hN : (R.pre R.τ).r.G.N = R.G0.N := (R.pre_inv R.τ).nEq
    have h1 := disposeAll_cost (List.range R.G0.N) (R.pre R.τ).r.G
      (fun g hg => by rw [hN]; exact List.mem_range.1 hg)
    have h2 := live_le_cells (R.pre R.τ).r.G
    unfold Wdisp
    rw [hG]
    rw [List.length_range] at h1
    omega
  have hinit := initCost_sum_le R.G0 R.D R.deg R.order
  have hdeg := Nat.mul_le_mul_left (Nat.clog 2 R.D + 1) R.order_deg_le
  have hlen := R.order_length_le
  have hretm := Nat.mul_le_mul_left (2 * Nat.clog 2 R.D + 4)
    (show ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t ≤ live R.G0 by omega)
  have hsc : R.scans = ((range R.τ).filter (fun t => R.q t = true)).card * R.K
      + (if R.q R.τ = true then R.K else 0) := by
    unfold scans
    rw [sum_range_succ, ← sum_filter, sum_const, smul_eq_mul]
  rw [hvol] at hlw
  unfold W
  rw [hsc]
  generalize (if R.q R.τ = true then R.K else 0) = a at *
  generalize ((range R.τ).filter (fun t => R.q t = true)).card = cq at *
  generalize ∑ t ∈ range R.τ, costF R.K R.rt delivCand R.u R.q R.s0 t = A at *
  generalize ∑ t ∈ range R.τ, testsF R.K R.rt delivCand R.u R.q R.s0 t = T at *
  generalize ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t = Rt at *
  generalize Nat.clog 2 R.D = c at *
  have n1 := Nat.zero_le (c * R.Splus)
  have n2 := Nat.zero_le (c * live R.G0)
  have n3 := Nat.zero_le (cq * R.K)
  have n4 := Nat.zero_le (R.τ * R.G0.L)
  nlinarith [n1, n2, n3, n4]

end SelRun

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, for the engine with
release of orphaned gates.**

Hypotheses.  Only the fields of `R : SelRun α` (the data of one run and the structural
input conditions listed there).  Nothing is assumed about costs.

Conclusions.

1. `F_t` (the root-reachable live incidences immediately before the backup wave of rollout
   `t + 1`) is exactly the live incidence set of the engine on implemented heaps at that
   moment: the engine holds no incidence that is not root-reachable.
2. The reference valuations used to define `b` are exact valuations of the original
   circuit.
3. `b_{t+1}(v) ≤ 2`.
4. The deliveries made by the engine through `τ` are exactly `S^+` of `eq:s-plus-minus`.
5. After the final disposal pass no incidence is left.
6. Unconditional bound:
   `W ≤ 12 (τ(L + 3) + Q·K + H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))`.
7. The manuscript's bound `W ≤ 13 (H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))` under two
   hypotheses on the shared work: (a) `L + 3 ≤ h t` for every `t < τ` (the shared work of
   a rollout is at least the circuit depth; true when a rollout descends one level of a
   layered graph per selection); (b) `K ≤ h t` at every query time `t ≤ τ` (the
   manuscript's `H` contains the root-action scans by definition).

`W = P + H + (computed)`, where the computed part is: `initPassH` for both endpoints;
`RetireFinal.costH` for every rollout and query (waves on implemented heaps, retirement
tests, heap deletions, release cascade, leader scan, retirement scan, stop scan); the query
at the stopping time; `disposeAll`.

Remaining differences from the manuscript statement:

* The manuscript's proof step "a single terminal update changes each gate endpoint at most
  once per wave" needs a topological processing order.  The wave here scans the level
  buckets `0..L` (`L + 3` units per endpoint and rollout); this is the term `τ(L + 3)` of
  item 6, which the manuscript's bound does not contain.  Item 7 absorbs it into `H` under
  hypothesis (a).
* The root scans of the engine (`4K` per query) are in `W`; the manuscript puts root-action
  scans into `H`.  Item 7 uses hypothesis (b) for this.
* `log D` is `⌈log₂ D⌉ + 1`; `n` is the number of gate indices `N`; `e = live G0`.
* Root-reachability is from the gates of the ACTIVE root actions (root actions retired at
  a query are no longer roots).  If the manuscript means all root actions, its `F_t` is a
  superset of the one here and its `S^+` is at least `SelRun.Splus`, so the bounds hold a
  fortiori.
* The root scans are charged `K` each inside `RetireFinal.qRetire` / `costF` / `costH`;
  `leadScanC_spec`, `retScanC_spec`, `stopScanC_spec` show that `K` is the computed cost of
  each scan written as a costed program.  Bucket operations and list unlinks are unit
  charges as in `DagRetire.lean` and `HeapImpl.lean`. -/
theorem representation_cost_upper {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α) :
    (∀ t, R.F t = liveInc (R.hpre t).r.G) ∧
    (∀ t, Exact R.G0 (R.refLo t) ∧ Exact R.G0 (R.refHi t)) ∧
    (∀ t v, R.b t v ≤ 2) ∧
    (∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus) ∧
    (∀ p, (disposeAll (List.range R.G0.N) (R.hpre R.τ).r.G).1.children p = []) ∧
    R.W ≤ 12 * R.X1 ∧
    ((∀ t, t < R.τ → R.G0.L + 3 ≤ R.h t) → (∀ t, t ≤ R.τ → R.q t = true → R.K ≤ R.h t) →
      R.W ≤ 13 * R.X) := by
  have hw := R.work_le
  refine ⟨fun t => ?_, fun t => ?_, fun t v => bChg_le_two _ _ _ _ v,
    sum_congr rfl (fun t _ => R.volF_eq t), fun p => ?_, ?_, fun ha hb => ?_⟩
  · rw [R.F_eq t, (R.sim_pre t).r.G]
  · obtain ⟨e1, e2, _⟩ := rrun_exact R.init_facts.2.1 R.hn t
    exact ⟨e1, e2⟩
  · have hG : (R.hpre R.τ).r.G = (R.pre R.τ).r.G := (R.sim_pre R.τ).r.G
    have hN : (R.pre R.τ).r.G.N = R.G0.N := (R.pre_inv R.τ).nEq
    rw [hG, ← hN]
    exact disposeAll_empty (R.rooted_all R.τ).2.1 p
  · unfold SelRun.X1 SelRun.X
    generalize Nat.clog 2 R.D = c at *
    have n1 := Nat.zero_le (c * R.Splus)
    have n2 := Nat.zero_le (c * live R.G0)
    nlinarith [n1, n2]
  · have h1 : R.τ * (R.G0.L + 3) ≤ R.H := by
      unfold SelRun.H
      calc R.τ * (R.G0.L + 3) = ∑ _t ∈ range R.τ, (R.G0.L + 3) := by
            rw [sum_const, card_range, smul_eq_mul]
        _ ≤ ∑ t ∈ range R.τ, R.h t := sum_le_sum (fun t ht => ha t (mem_range.1 ht))
        _ ≤ ∑ t ∈ range (R.τ + 1), R.h t := by
            rw [sum_range_succ]
            exact Nat.le_add_right _ _
    have h2 : R.scans ≤ R.H := by
      unfold SelRun.scans SelRun.H
      apply sum_le_sum
      intro t ht
      by_cases hq : R.q t = true
      · rw [ite_eq_left hq]
        exact hb t (by have := mem_range.1 ht; omega) hq
      · rw [ite_eq_right hq]
        exact Nat.zero_le _
    unfold SelRun.X
    generalize Nat.clog 2 R.D = c at *
    have n1 := Nat.zero_le (c * R.Splus)
    have n2 := Nat.zero_le (c * live R.G0)
    nlinarith [n1, n2]

/-- **`eq:prop-rep-upper` in `O` form**: for a family of runs satisfying the two
shared-work hypotheses, `W = O(H + P + n + e + (S^+ + e) log D)` along any filter. -/
theorem representation_cost_upper_isBigO {α ι : Type*} [LinearOrder α] [OrderBot α]
    {l : Filter ι} (R : ι → SelRun α)
    (ha : ∀ i t, t < (R i).τ → (R i).G0.L + 3 ≤ (R i).h t)
    (hb : ∀ i t, t ≤ (R i).τ → (R i).q t = true → (R i).K ≤ (R i).h t) :
    (fun i => ((R i).W : ℝ)) =O[l] (fun i => ((R i).X : ℝ)) := by
  apply IsBigO.of_bound 13
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (representation_cost_upper (R i)).2.2.2.2.2.2 (ha i) (hb i)

end Final

end LiteralK3
end JointRootCert
