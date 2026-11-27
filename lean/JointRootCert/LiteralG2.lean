/-
Joint Root Certification: `prop:representation-cost` (Unified Full-Cost Representation
Comparison), upper bound `eq:prop-rep-upper`, for an engine with no cost-model conventions
beyond the given inputs `P` and `H`.

Manuscript result covered: `prop:representation-cost` (all three sentences), restated from
`LiteralF4` for a modified executed program.

## The three conventions of `LiteralF4` and how they are removed

1. **Fuel.**  `LiteralF4` runs the wave loop `loopDR` with fuel `N + 2` and the release
   cascade with fuel `relFuel`; neither fuel is work.  Here:
   * `doneD` / `doneR` say that a loop reaches its empty-stack exit before the fuel runs out;
     `loopDR_done`, `waveDR_done`, `releaseLoopG_done` prove this for every invocation of the
     engine (`relStepG_eq`, `stepG`), and `loopDR_fuel`, `waveDRf_fuel`, `releaseLoopG_fuel`
     show that then the result (state and cost) is the same for every larger fuel, i.e. it
     is the result of the unbounded loop;
   * `itersD_le`, `itersW_le`, `itersR_le`: the number of executed iterations (including
     the final empty-stack test) is at most the computed cost.  In `RetireFinal.releaseLoopH`
     the final empty-stack test was free; `releaseLoopG` charges it one unit, and `qRetireG`,
     `tailG` use `releaseLoopG`.
2. **Membership test.**  `EngineFinal.retireOneH` tests `c ∈ children p` at one unit.  The
   executed engine here does not test membership at all: `retireOneG` tests only the value
   condition `hi c < lo p` (one unit).  This is correct because the candidate list is built
   from the live parent lists, is duplicate-free, and a retirement removes only its own
   incidence, so every candidate is live when it is tested (`retireListG_eq`: on such a
   list `retireListG = retireListH`).
3. **Pre-wave values.**  `LiteralF4.mergeChg` decides "the lower value of `g` did not change"
   by comparing with the pre-wave value.  Here the merge `mergeM` reads no value at all: it
   marks the gates of the lower record in a Boolean table indexed by gate (`setMarks`,
   one write per record), keeps the upper-record gates whose mark is unset
   (`filterUnmarked`, one read each) and clears the marks again (`clearMarks`, one write per
   record).  The table is part of the engine state (`GS.marks`); it is allocated once by
   `initMarks` (one write per gate, from arbitrary initial contents `m0`) and is all-false
   on `[0, N)` between rollouts (`simG_all`).  `mergeM_spec`: a lookup agrees with list
   membership; `relStepG_eq`: the merged list equals `LiteralF4.mergedR`.

With these, `WR + Σ|lower records| + N ≤ WG ≤ WR + Σ|lower records| + N + 2τ + 1`
(`WG_bounds`), hence `WG ≤ 23 · XD` (`WG_le`).

## Two further conventions, removed in sections 8 to 12

4. **Heap fuel.**  `HeapImpl.siftUp` / `siftDown` run with fuel `⌈log₂ n⌉`.  `doneUp` /
   `doneDn` say a sift stops by its own test before the fuel runs out; `siftUp_done`
   (`j + 1 < 2^(d+1)`) and `siftDown_done` (`n ≤ (j+1) 2^d`) prove it, and `siftUp_fuel` /
   `siftDown_fuel` show that more fuel gives the same result.  `updateAt_done`,
   `insert_done`, `deleteAt_done`, `heapLoop_done` instantiate this at every call site
   (`pos_lt`: a position read from a valid position map is in range).
5. **Protection test.**  The cascade's test `prot g` was `protOf K rt act g`, a scan over
   the `K` root actions, inside one unit.  The engine `runSP` keeps a count table
   (`GP.cnt`: the number of active root actions per gate), built by `initCnt` (one write per
   gate `< N` from arbitrary contents `c0`, then one increment per root action) and
   decremented at every query by one write per retired root (`qRetireP`, `decAll`); the
   cascade reads `pidx cnt g = decide (0 < cnt g)`, one read inside the unit already charged
   per popped gate.  `protOf_cnt`, `cnt_deact`, `simP_all`: the lookup equals `protOf` below
   `N` at every time; `releaseLoopG_congr`: the cascade only reads gates `< N`.
   `WP_bounds`: `WG + N + K ≤ WP ≤ WG + N + K + Q·K`, hence `WP ≤ 24 · XD + K` (`WP_le`) and
   `WP ≤ 25 · XD` when some query occurs by time `τ` (`WP_le_query`).  The extra `K` is the
   construction of the table from the `K` root actions: `XD` contains `K` only through the
   query scans `Q · K`, so with no query it is not bounded by `XD`.
-/
import JointRootCert.LiteralF4

namespace JointRootCert
namespace LiteralG2

open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)
open Asymptotics
open scoped List

/-! ## 1. The wave loop: fuel and iterations -/

section WaveFuel

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The stack loop reaches its empty-stack exit before the fuel runs out. -/
def doneD (G : Dag) : ℕ → HEState α → List ℕ → Prop
  | 0, _, _ => False
  | _ + 1, _, [] => True
  | f + 1, s, g :: st => doneD G f (dlv g (s.val g) (G.parents g) s st).1
      (dlv g (s.val g) (G.parents g) s st).2.1

/-- Number of iterations executed by the stack loop (pops and the final empty test). -/
def itersD (G : Dag) : ℕ → HEState α → List ℕ → ℕ
  | 0, _, _ => 0
  | _ + 1, _, [] => 1
  | f + 1, s, g :: st => 1 + itersD G f (dlv g (s.val g) (G.parents g) s st).1
      (dlv g (s.val g) (G.parents g) s st).2.1

/-- Every executed iteration of the stack loop is charged. -/
lemma itersD_le (G : Dag) : ∀ (f : ℕ) (s : HEState α) (st : List ℕ),
    itersD G f s st ≤ (loopDR G f s st).2.1 := by
  intro f
  induction f with
  | zero => intro s st; exact Nat.zero_le _
  | succ f ih =>
    intro s st
    cases st with
    | nil => exact le_rfl
    | cons g st =>
      have := ih (dlv g (s.val g) (G.parents g) s st).1 (dlv g (s.val g) (G.parents g) s st).2.1
      rw [itersD, loopDR]
      dsimp only
      omega

/-- With a terminating fuel, any larger fuel gives the same result. -/
lemma loopDR_fuel (G : Dag) : ∀ (f : ℕ) (s : HEState α) (st : List ℕ), doneD G f s st →
    ∀ j, loopDR G (f + j) s st = loopDR G f s st := by
  intro f
  induction f with
  | zero => intro s st h; exact (h : False).elim
  | succ f ih =>
    intro s st h j
    rw [Nat.add_right_comm]
    cases st with
    | nil => rfl
    | cons g st =>
      rw [loopDR, loopDR, ih (dlv g (s.val g) (G.parents g) s st).1
        (dlv g (s.val g) (G.parents g) s st).2.1 h j]

variable {G : Dag} {o f : ℕ → α}

/-- **The stack loop does not run out of fuel** under the invariant of `LiteralF4.loopDR_rec`. -/
theorem loopDR_done (hG : G.WF) (hD : Dir o f) (ho : Exact G o) (hf : Exact G f) :
    ∀ (fuel : ℕ) (s : HEState α) (k : ℕ → ℕ → α) (st : List ℕ),
    DI G o f 0 [] s k st → st.length + (Uset G o f s).card < fuel → doneD G fuel s st := by
  intro fuel
  induction fuel with
  | zero => intro s k st _ hm; omega
  | succ fuel ih =>
    intro s k st h hm
    cases st with
    | nil => exact trivial
    | cons g rest =>
      obtain ⟨hg, _, _⟩ := h.stk g List.mem_cons_self
      obtain ⟨hgr, hrnd⟩ := List.nodup_cons.1 h.nd
      have hD' : DI G o f g (G.parents g) s k rest := by
        refine ⟨h.rep, h.gate, fun p c hc => ?_, h.val,
          fun q hq => h.stk q (List.mem_cons_of_mem _ hq), hrnd, h.leaf⟩
        rw [h.key p c hc]
        have hpc : p ∈ G.parents c := (hG.parents_iff c p).2 hc
        by_cases e : c = g
        · subst e
          simp [hpc]
        · simp [e]
      obtain ⟨k1, d1, _, _, d4, _, _, _, _⟩ := dlv_spec hG hD ho hf g (s.val g)
        (G.parents g) s k rest hD' rfl hg hgr (fun p hp => (hG.parents_iff g p).1 hp)
        (hG.parents_nodup g)
      have hm' : (dlv g (s.val g) (G.parents g) s rest).2.1.length
          + (Uset G o f (dlv g (s.val g) (G.parents g) s rest).1).card < fuel := by
        rw [d4]
        simp only [List.length_cons] at hm
        omega
      exact ih _ k1 _ d1.reg hm'

/-- The wave either stops at its first test or its stack loop terminates within its fuel. -/
def waveDone (G : Dag) (x : ℕ) (y : α) (s : HEState α) : Prop :=
  targetH G x y s x = s.val x ∨
    doneD G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]

/-- The recording wave with an explicit fuel `F` (`waveDR` is `F = N + 2`). -/
def waveDRf (G : Dag) (F x : ℕ) (y : α) (s : HEState α) : HEState α × ℕ × List ℕ :=
  if targetH G x y s x = s.val x then (s, 1, [])
  else ((loopDR G F ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).1,
    1 + (loopDR G F ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).2.1,
    (loopDR G F ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).2.2)

lemma waveDRf_eq (G : Dag) (x : ℕ) (y : α) (s : HEState α) :
    waveDRf G (G.N + 2) x y s = waveDR G x y s := rfl

/-- **A terminating wave gives the same result with any larger fuel.** -/
theorem waveDRf_fuel (G : Dag) (x : ℕ) (y : α) (s : HEState α) (h : waveDone G x y s)
    (j : ℕ) : waveDRf G (G.N + 2 + j) x y s = waveDR G x y s := by
  unfold waveDRf waveDR
  by_cases hc : targetH G x y s x = s.val x
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc, loopDR_fuel G _ _ _ (h.resolve_left hc) j]

/-- Iterations executed by the wave: its first test, then the stack loop. -/
def itersW (G : Dag) (x : ℕ) (y : α) (s : HEState α) : ℕ :=
  if targetH G x y s x = s.val x then 1
  else 1 + itersD G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]

lemma itersW_le (G : Dag) (x : ℕ) (y : α) (s : HEState α) :
    itersW G x y s ≤ (waveDR G x y s).2.1 := by
  unfold itersW waveDR
  by_cases hc : targetH G x y s x = s.val x
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    have := itersD_le G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]
    dsimp only
    omega

/-- **Every wave of the engine terminates within its fuel** (hypotheses of
`LiteralF4.waveDR_rec`). -/
theorem waveDR_done (hG : G.WF) (x : ℕ) (y : α) (hs : HEState α) (s0 : EState α)
    (hx : x < G.N) (h : SimE G hs s0) (h0 : Inv G s0) : waveDone G x y hs := by
  obtain ⟨w1, w2, w3, _⟩ := wave_spec hG x y s0 hx h0
  have ho := inv_exact h0
  have hf := inv_exact w1
  have hD := dir_of_wave hG x y s0 hx h0
  have ht := HeapImpl.targetH_eq h x y x
  have hv := h.val
  by_cases hc : targetH G x y hs x = hs.val x
  · exact Or.inl hc
  · right
    have hxl : G.children x = [] := by
      by_contra hxl
      apply hc
      rw [ht, hv]
      unfold target
      rw [ite_eq_right hxl]
      exact (h0.gate x hxl).symm
    have hty : targetH G x y hs x = y := by
      rw [ht]
      unfold target
      rw [ite_eq_left hxl, ite_eq_left rfl]
    have hfx : (wave G x y s0).1.val x = y := w2 hxl
    have hfo : (wave G x y s0).1.val x ≠ s0.val x := by
      rw [hfx, ← hty, ← hv]
      exact hc
    set s1 : HEState α := ⟨Function.update hs.val x (targetH G x y hs x), hs.hp⟩ with hs1
    have hs1x : s1.val x = (wave G x y s0).1.val x := by
      rw [hs1]
      show Function.update hs.val x (targetH G x y hs x) x = _
      rw [Function.update_self, hty, hfx]
    have hs1o : ∀ q, q ≠ x → s1.val q = s0.val q := by
      intro q e
      rw [hs1]
      show Function.update hs.val x (targetH G x y hs x) q = _
      rw [Function.update_of_ne e, hv]
    have hDI : DI G s0.val (wave G x y s0).1.val 0 [] s1 s0.key [x] := by
      refine ⟨h.hp, fun p hp => ?_, fun p c hcp => ?_, fun q => ?_, fun q hq => ?_,
        List.nodup_singleton x, fun q hq => ?_⟩
      · have e : p ≠ x := fun e => hp (e ▸ hxl)
        rw [hs1o p e]
        exact h0.gate p hp
      · rw [h0.keys p c hcp]
        by_cases e : c = x
        · subst e
          simp
        · simp only [List.mem_singleton, e, false_or, List.not_mem_nil, and_false, ite_false]
          exact (hs1o c e).symm
      · by_cases e : q = x
        · subst e; exact Or.inr hs1x
        · exact Or.inl (hs1o q e)
      · rw [List.mem_singleton] at hq
        subst hq
        exact ⟨hs1x, hfo, hx⟩
      · by_cases e : q = x
        · subst e; exact hs1x
        · rw [hs1o q e]; exact (w3 q hq e).symm
    have hUle : (Uset G s0.val (wave G x y s0).1.val s1).card ≤ G.N := by
      have := card_filter_le (range G.N)
        (fun q => s1.val q = s0.val q ∧ (wave G x y s0).1.val q ≠ s0.val q)
      rw [card_range] at this
      exact this
    exact loopDR_done hG hD ho hf (G.N + 2) s1 s0.key [x] hDI
      (by simp only [List.length_singleton]; omega)

end WaveFuel

/-! ## 2. The release cascade: fuel, iterations and the final test -/

section ReleaseFuel

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **The release cascade of the engine**: `RetireFinal.releaseLoopH`, with the final
empty-stack test charged one unit. -/
def releaseLoopG (prot : ℕ → Bool) : ℕ → List ℕ → HRState α → HRState α × ℕ
  | 0, _, s => (s, 0)
  | _ + 1, [], s => (s, 1)
  | f + 1, g :: st, s =>
    if s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false then
      ((releaseLoopG prot f (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩).1,
       (releaseLoopG prot f (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩).2 + 1 + (s.G.children g).length)
    else ((releaseLoopG prot f st s).1, (releaseLoopG prot f st s).2 + 1)

/-- The cascade reaches its empty-stack exit before the fuel runs out. -/
def doneR (prot : ℕ → Bool) : ℕ → List ℕ → HRState α → Prop
  | 0, _, _ => False
  | _ + 1, [], _ => True
  | f + 1, g :: st, s =>
    if s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false then
      doneR prot f (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩
    else doneR prot f st s

/-- Number of iterations executed by the cascade (pops and the final empty test). -/
def itersR (prot : ℕ → Bool) : ℕ → List ℕ → HRState α → ℕ
  | 0, _, _ => 0
  | _ + 1, [], _ => 1
  | f + 1, g :: st, s =>
    if s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false then
      1 + itersR prot f (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩
    else 1 + itersR prot f st s

/-- `releaseLoopG` computes the state of `releaseLoopH`; its cost is that of `releaseLoopH`
plus at most one, and exactly one more when the cascade terminates within its fuel. -/
theorem releaseLoopG_rel (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (s : HRState α),
    (releaseLoopG prot f st s).1 = (releaseLoopH prot f st s).1 ∧
    (releaseLoopH prot f st s).2 ≤ (releaseLoopG prot f st s).2 ∧
    (releaseLoopG prot f st s).2 ≤ (releaseLoopH prot f st s).2 + 1 ∧
    (doneR prot f st s → (releaseLoopG prot f st s).2 = (releaseLoopH prot f st s).2 + 1) := by
  intro f
  induction f with
  | zero => intro st s; exact ⟨rfl, le_rfl, Nat.zero_le _, fun h => (h : False).elim⟩
  | succ f ih =>
    intro st s
    cases st with
    | nil => exact ⟨rfl, Nat.zero_le _, le_rfl, fun _ => rfl⟩
    | cons g st =>
      rw [releaseLoopG, releaseLoopH, doneR]
      by_cases hc : s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc]
        obtain ⟨i1, i2, i3, i4⟩ := ih (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩
        refine ⟨i1, ?_, ?_, fun h => ?_⟩
        · dsimp only; omega
        · dsimp only; omega
        · have := i4 h; dsimp only at this ⊢; omega
      · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
        obtain ⟨i1, i2, i3, i4⟩ := ih st s
        refine ⟨i1, ?_, ?_, fun h => ?_⟩
        · dsimp only; omega
        · dsimp only; omega
        · have := i4 h; dsimp only at this ⊢; omega

lemma releaseLoopG_fst (prot : ℕ → Bool) (f : ℕ) (st : List ℕ) (s : HRState α) :
    (releaseLoopG prot f st s).1 = (releaseLoopH prot f st s).1 :=
  (releaseLoopG_rel prot f st s).1

/-- **The cascade does not run out of fuel**: on a well-formed circuit, fuel above
`2 · cells + |stack|` (in particular `relFuel`) suffices. -/
theorem releaseLoopG_done (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (s : HRState α),
    s.G.WF → 2 * cells s.G + st.length < f → doneR prot f st s := by
  intro f
  induction f with
  | zero => intro st s _ hf; omega
  | succ f ih =>
    intro st s hG hf
    cases st with
    | nil => exact trivial
    | cons g st =>
      rw [List.length_cons] at hf
      rw [doneR]
      by_cases hc : s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc]
        obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc.1
        have hgN : g < s.G.N := hG.parent_lt c g ((hG.parents_iff c g).2 hcm)
        have hcell := cells_release hgN hc.1
        refine ih _ _ (releaseDag_wf hG g) ?_
        show 2 * cells (releaseDag s.G g) + (s.G.children g ++ st).length < f
        rw [List.length_append]
        omega
      · rw [ite_eq_right hc]
        exact ih st s hG (by omega)

lemma relFuel_done (prot : ℕ → Bool) (st : List ℕ) (s : HRState α) (hG : s.G.WF) :
    doneR prot (relFuel s.G st) st s :=
  releaseLoopG_done prot _ st s hG (LiteralE4.relFuel_enough s.G st)

/-- **A terminating cascade gives the same result with any larger fuel.** -/
theorem releaseLoopG_fuel (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (s : HRState α),
    doneR prot f st s → ∀ j, releaseLoopG prot (f + j) st s = releaseLoopG prot f st s := by
  intro f
  induction f with
  | zero => intro st s h; exact (h : False).elim
  | succ f ih =>
    intro st s h j
    rw [Nat.add_right_comm]
    cases st with
    | nil => rfl
    | cons g st =>
      rw [doneR] at h
      rw [releaseLoopG, releaseLoopG]
      by_cases hc : s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc] at h
        rw [ite_eq_left hc, ite_eq_left hc, ih _ _ h j]
      · rw [ite_eq_right hc] at h
        rw [ite_eq_right hc, ite_eq_right hc, ih _ _ h j]

/-- Every executed iteration of the cascade is charged. -/
lemma itersR_le (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (s : HRState α),
    itersR prot f st s ≤ (releaseLoopG prot f st s).2 := by
  intro f
  induction f with
  | zero => intro st s; exact Nat.zero_le _
  | succ f ih =>
    intro st s
    cases st with
    | nil => exact le_rfl
    | cons g st =>
      rw [itersR, releaseLoopG]
      by_cases hc : s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc, ite_eq_left hc]
        have := ih (s.G.children g ++ st)
          ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
            ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩
        dsimp only
        omega
      · rw [ite_eq_right hc, ite_eq_right hc]
        have := ih st s
        dsimp only
        omega

end ReleaseFuel

/-! ## 3. The retirement pass without a membership test -/

section RetireG

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **Retirement of one candidate without a membership test**: the value test
`hi c < lo p` (1 unit); if it holds, two heap deletions (computed cost) and two unlinks
(1 unit each), as in `EngineFinal.retireOneH`. -/
def retireOneG (e : ℕ × ℕ) (s : HRState α) : HRState α × ℕ :=
  if s.hi.val e.2 < s.lo.val e.1 then
    (⟨retireDag s.G e.1 e.2,
      ⟨s.lo.val, Function.update s.lo.hp e.1 (HeapImpl.delete (s.lo.hp e.1) e.2).1⟩,
      ⟨s.hi.val, Function.update s.hi.hp e.1 (HeapImpl.delete (s.hi.hp e.1) e.2).1⟩⟩,
     (HeapImpl.delete (s.lo.hp e.1) e.2).2 + (HeapImpl.delete (s.hi.hp e.1) e.2).2 + 3)
  else (s, 1)

/-- The retirement pass of the engine over a candidate list. -/
def retireListG : List (ℕ × ℕ) → HRState α → HRState α × ℕ
  | [], s => (s, 0)
  | e :: es, s =>
    ((retireListG es (retireOneG e s).1).1,
     (retireOneG e s).2 + (retireListG es (retireOneG e s).1).2)

omit [OrderBot α] in
lemma retireOneG_eq (e : ℕ × ℕ) (s : HRState α) (h : e.2 ∈ s.G.children e.1) :
    retireOneG e s = retireOneH e s := by
  unfold retireOneG retireOneH
  by_cases hc : s.hi.val e.2 < s.lo.val e.1
  · rw [ite_eq_left hc, ite_eq_left ⟨h, hc⟩]
  · rw [ite_eq_right hc, ite_eq_right (fun h' => hc h'.2)]

omit [OrderBot α] in
/-- **The membership test is not needed**: on a duplicate-free list of live incidences the
pass without the test equals `EngineFinal.retireListH` (state and cost). -/
theorem retireListG_eq : ∀ (L : List (ℕ × ℕ)) (s : HRState α), L.Nodup →
    (∀ e ∈ L, e.2 ∈ s.G.children e.1) → retireListG L s = retireListH L s := by
  intro L
  induction L with
  | nil => intro s _ _; rfl
  | cons e es ih =>
    intro s hn hl
    obtain ⟨he, hes⟩ := List.nodup_cons.1 hn
    have h1 := retireOneG_eq e s (hl e List.mem_cons_self)
    have hl' : ∀ e' ∈ es, e'.2 ∈ (retireOneH e s).1.G.children e'.1 := by
      intro e' he'
      have hm := hl e' (List.mem_cons_of_mem _ he')
      have hne : e' ≠ e := fun h => he (h ▸ he')
      unfold retireOneH
      by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
      · rw [ite_eq_left hc]
        show e'.2 ∈ (retireDag s.G e.1 e.2).children e'.1
        rw [mem_retire_children]
        exact ⟨hm, fun h => hne (Prod.ext h.1 h.2)⟩
      · rw [ite_eq_right hc]; exact hm
    show ((retireListG es (retireOneG e s).1).1,
        (retireOneG e s).2 + (retireListG es (retireOneG e s).1).2)
      = ((retireListH es (retireOneH e s).1).1,
        (retireOneH e s).2 + (retireListH es (retireOneH e s).1).2)
    rw [h1, ih _ hes hl']

omit [OrderBot α] in
lemma retireListH_wf : ∀ (L : List (ℕ × ℕ)) (s : HRState α), s.G.WF →
    (retireListH L s).1.G.WF := by
  intro L
  induction L with
  | nil => intro s h; exact h
  | cons e es ih =>
    intro s h
    have h1 : (retireOneH e s).1.G.WF := by
      unfold retireOneH
      split_ifs
      · exact retireDag_wf h _ _
      · exact h
    exact ih _ h1

end RetireG

/-! ## 4. The mark table -/

section Marks

/-- Set the marks of the gates of `l` (1 unit per write). -/
def setMarks : List ℕ → (ℕ → Bool) → (ℕ → Bool) × ℕ
  | [], m => (m, 0)
  | g :: l, m => ((setMarks l (Function.update m g true)).1,
      (setMarks l (Function.update m g true)).2 + 1)

/-- Clear the marks of the gates of `l` (1 unit per write). -/
def clearMarks : List ℕ → (ℕ → Bool) → (ℕ → Bool) × ℕ
  | [], m => (m, 0)
  | g :: l, m => ((clearMarks l (Function.update m g false)).1,
      (clearMarks l (Function.update m g false)).2 + 1)

/-- Keep the gates of `l` whose mark is unset (1 unit per lookup). -/
def filterUnmarked (m : ℕ → Bool) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | g :: l => (if m g then (filterUnmarked m l).1 else g :: (filterUnmarked m l).1,
      (filterUnmarked m l).2 + 1)

/-- **The merge with a mark table**: the lower record, then the upper-record gates not in
the lower record; the marks are set and cleared again.  Returns the merged list, the table
afterwards, and the cost `2 |rl| + |rh|`. -/
def mergeM (mk : ℕ → Bool) (rl rh : List ℕ) : List ℕ × (ℕ → Bool) × ℕ :=
  (rl ++ (filterUnmarked (setMarks rl mk).1 rh).1,
   (clearMarks rl (setMarks rl mk).1).1,
   (setMarks rl mk).2 + (filterUnmarked (setMarks rl mk).1 rh).2
     + (clearMarks rl (setMarks rl mk).1).2)

/-- Allocation of the mark table: one write per gate `< N`, from arbitrary contents. -/
def initMarks (N : ℕ) (m0 : ℕ → Bool) : (ℕ → Bool) × ℕ := clearMarks (List.range N) m0

lemma setMarks_spec : ∀ (l : List ℕ) (m : ℕ → Bool),
    (∀ g, (setMarks l m).1 g = (decide (g ∈ l) || m g)) ∧ (setMarks l m).2 = l.length := by
  intro l
  induction l with
  | nil => intro m; exact ⟨fun g => by simp [setMarks], rfl⟩
  | cons a l ih =>
    intro m
    obtain ⟨h1, h2⟩ := ih (Function.update m a true)
    refine ⟨fun g => ?_, ?_⟩
    · show (setMarks l (Function.update m a true)).1 g = _
      rw [h1 g]
      by_cases e : g = a
      · subst e; simp
      · simp [e, Function.update_of_ne e]
    · show (setMarks l (Function.update m a true)).2 + 1 = _
      rw [h2, List.length_cons]

lemma clearMarks_spec : ∀ (l : List ℕ) (m : ℕ → Bool),
    (∀ g, (clearMarks l m).1 g = (!decide (g ∈ l) && m g)) ∧ (clearMarks l m).2 = l.length := by
  intro l
  induction l with
  | nil => intro m; exact ⟨fun g => by simp [clearMarks], rfl⟩
  | cons a l ih =>
    intro m
    obtain ⟨h1, h2⟩ := ih (Function.update m a false)
    refine ⟨fun g => ?_, ?_⟩
    · show (clearMarks l (Function.update m a false)).1 g = _
      rw [h1 g]
      by_cases e : g = a
      · subst e; simp
      · simp [e, Function.update_of_ne e]
    · show (clearMarks l (Function.update m a false)).2 + 1 = _
      rw [h2, List.length_cons]

lemma filterUnmarked_spec (m : ℕ → Bool) : ∀ l : List ℕ,
    (filterUnmarked m l).1 = l.filter (fun g => !m g) ∧ (filterUnmarked m l).2 = l.length := by
  intro l
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons g l ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show (if m g then (filterUnmarked m l).1 else g :: (filterUnmarked m l).1) = _
      rw [h1]
      cases hm : m g <;> simp [List.filter_cons, hm]
    · show (filterUnmarked m l).2 + 1 = _
      rw [h2, List.length_cons]

/-- **Lookups in the mark table agree with list membership**: if the table is unset on the
upper record, the merged list is the lower record followed by the upper-record gates not
in the lower record; the table is unset afterwards wherever it was unset before; the cost
is `2 |rl| + |rh|`. -/
theorem mergeM_spec (mk : ℕ → Bool) (rl rh : List ℕ) (hmk : ∀ g ∈ rh, mk g = false) :
    (mergeM mk rl rh).1 = rl ++ rh.filter (fun g => !decide (g ∈ rl)) ∧
    (∀ g, mk g = false → (mergeM mk rl rh).2.1 g = false) ∧
    (mergeM mk rl rh).2.2 = 2 * rl.length + rh.length := by
  obtain ⟨s1, s2⟩ := setMarks_spec rl mk
  obtain ⟨c1, c2⟩ := clearMarks_spec rl (setMarks rl mk).1
  obtain ⟨f1, f2⟩ := filterUnmarked_spec (setMarks rl mk).1 rh
  refine ⟨?_, fun g hg => ?_, ?_⟩
  · show rl ++ (filterUnmarked (setMarks rl mk).1 rh).1 = _
    rw [f1]
    congr 1
    apply List.filter_congr
    intro g hg
    rw [s1 g, hmk g hg, Bool.or_false]
  · show (clearMarks rl (setMarks rl mk).1).1 g = false
    rw [c1 g, s1 g, hg, Bool.or_false]
    cases decide (g ∈ rl) <;> rfl
  · show (setMarks rl mk).2 + (filterUnmarked (setMarks rl mk).1 rh).2
      + (clearMarks rl (setMarks rl mk).1).2 = _
    rw [s2, f2, c2]
    omega

lemma initMarks_spec (N : ℕ) (m0 : ℕ → Bool) :
    (∀ g, g < N → (initMarks N m0).1 g = false) ∧ (initMarks N m0).2 = N := by
  obtain ⟨c1, c2⟩ := clearMarks_spec (List.range N) m0
  refine ⟨fun g hg => ?_, ?_⟩
  · show (clearMarks (List.range N) m0).1 g = false
    rw [c1 g]
    simp [hg]
  · show (clearMarks (List.range N) m0).2 = N
    rw [c2, List.length_range]

end Marks

/-! ## 5. The executed engine -/

section EngineG

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- State of the executed engine: the implemented state of `LiteralF4` and the mark
table. -/
structure GS (α : Type*) where
  q : HQS α
  marks : ℕ → Bool

/-- The merge of the two recorded lists of a rollout, with the mark table. -/
def mergeG (u : ℕ × α × α) (s : GS α) : List ℕ × (ℕ → Bool) × ℕ :=
  mergeM s.marks (recLo u s.q.r).2.2 (recHi u s.q.r).2.2

/-- The candidate list of a rollout: the parent incidences of the merged gates. -/
def candG (u : ℕ × α × α) (s : GS α) : List (ℕ × ℕ) := (buildCand s.q.r.G (mergeG u s).1).1

/-- The part of a rollout after the waves: the retirement pass without membership test,
then the release cascade `releaseLoopG` from the children of the candidates. -/
def tailG (K : ℕ) (rt : ℕ → ℕ) (cand : List (ℕ × ℕ)) (s : HQS α) (w : HRState α) :
    HQS α × ℕ :=
  (⟨(releaseLoopG (protOf K rt s.act) (relFuel (retireListG cand w).1.G (cand.map Prod.snd))
      (cand.map Prod.snd) (retireListG cand w).1).1, s.act⟩,
   (retireListG cand w).2
    + (releaseLoopG (protOf K rt s.act) (relFuel (retireListG cand w).1.G (cand.map Prod.snd))
      (cand.map Prod.snd) (retireListG cand w).1).2)

/-- **One rollout of the executed engine**: the two recording waves `waveDR`, the merge
with the mark table, the candidate construction, the retirement pass without membership
test and the release cascade. -/
def relStepG (K : ℕ) (rt : ℕ → ℕ) (u : ℕ × α × α) (s : GS α) : GS α × ℕ :=
  (⟨(tailG K rt (candG u s) s.q (wR u s.q.r)).1, (mergeG u s).2.1⟩,
   (recLo u s.q.r).2.1 + (recHi u s.q.r).2.1 + (mergeG u s).2.2
     + (buildCand s.q.r.G (mergeG u s).1).2 + (tailG K rt (candG u s) s.q (wR u s.q.r)).2)

/-- Root retirement at a query: `RetireFinal.qRetireH` with the cascade `releaseLoopG`. -/
def qRetireG (K : ℕ) (rt : ℕ → ℕ) (s : HQS α) : HQS α × ℕ :=
  (leadScan (fun i => s.r.lo.val (rt i)) s.act K).elim (s, K)
    (fun a =>
      (⟨(releaseLoopG
            (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r).1,
        deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act⟩,
       K + K + (releaseLoopG
            (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r).2))

/-- State of the executed engine after `t` rollouts. -/
def runSG (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : GS α) : ℕ → GS α
  | 0 => s0
  | t + 1 => (relStepG K rt (u (t + 1))
      (if q t = true then ⟨(qRetireG K rt (runSG K rt u q s0 t).q).1, (runSG K rt u q s0 t).marks⟩
        else runSG K rt u q s0 t)).1

/-- Computed cost of the query of time `t` (if any) and of rollout `t + 1`. -/
def costSG (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : GS α) (t : ℕ) : ℕ :=
  (if q t = true then K + (qRetireG K rt (runSG K rt u q s0 t).q).2 else 0)
    + (relStepG K rt (u (t + 1))
        (if q t = true then ⟨(qRetireG K rt (runSG K rt u q s0 t).q).1, (runSG K rt u q s0 t).marks⟩
          else runSG K rt u q s0 t)).2

lemma qRetireG_rel (K : ℕ) (rt : ℕ → ℕ) (s : HQS α) :
    (qRetireG K rt s).1 = (qRetireH K rt s).1 ∧ (qRetireH K rt s).2 ≤ (qRetireG K rt s).2 ∧
    (qRetireG K rt s).2 ≤ (qRetireH K rt s).2 + 1 := by
  unfold qRetireG qRetireH
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => exact ⟨rfl, le_rfl, Nat.le_succ _⟩
  | some a =>
    obtain ⟨i1, i2, i3, _⟩ := releaseLoopG_rel
      (protOf K rt (deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
      (relFuel s.r.G
        (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
      (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act) s.r
    dsimp only [Option.elim]
    refine ⟨by rw [i1], by omega, by omega⟩

/-- The tail of the executed engine against `LiteralE4.tailStep` with the same list. -/
theorem tailG_rel (K : ℕ) (rt : ℕ → ℕ) (L : List (ℕ × ℕ)) (s : HQS α) (w : HRState α)
    (hn : L.Nodup) (hl : ∀ e ∈ L, e.2 ∈ w.G.children e.1) :
    (tailG K rt L s w).1 = (LiteralE4.tailStep K rt (fun _ _ _ _ _ => L) s w).1 ∧
    (LiteralE4.tailStep K rt (fun _ _ _ _ _ => L) s w).2 ≤ (tailG K rt L s w).2 ∧
    (tailG K rt L s w).2 ≤ (LiteralE4.tailStep K rt (fun _ _ _ _ _ => L) s w).2 + 1 ∧
    (w.G.WF → doneR (protOf K rt s.act) (relFuel (retireListG L w).1.G (L.map Prod.snd))
      (L.map Prod.snd) (retireListG L w).1) := by
  have e := retireListG_eq L w hn hl
  obtain ⟨i1, i2, i3, _⟩ := releaseLoopG_rel (protOf K rt s.act)
    (relFuel (retireListH L w).1.G (L.map Prod.snd)) (L.map Prod.snd) (retireListH L w).1
  unfold tailG LiteralE4.tailStep
  rw [e]
  refine ⟨by rw [i1], by dsimp only; omega, by dsimp only; omega, fun hw => ?_⟩
  exact relFuel_done _ _ _ (retireListH_wf L w hw)

variable {K : ℕ} {rt : ℕ → ℕ}

/-- **One rollout of the executed engine against `LiteralF4.relStepR`.**  Hypotheses as in
`LiteralF4.relStepR_spec`, and the mark table unset below `N`.

1. the merged list (computed with the mark table) is `LiteralF4.mergedR`, and the
   candidate list is `LiteralF4.candR`;
2. the candidate list is duplicate-free and every candidate is a live incidence, so the
   retirement pass without membership test equals `retireListH`;
3. the engine state after the rollout is that of `relStepR`, and the mark table is still
   unset wherever it was;
4. the computed cost is that of `relStepR` plus the length of the lower record (the
   clearing pass), plus at most one (the final test of the cascade);
5. both waves and the cascade terminate within their fuel. -/
theorem relStepG_eq {gs : GS α} {s : QS α} (h : SimQ gs.q s) {G0 : Dag} {elo ehi : ℕ → α}
    (hinv : CInv G0 K rt s.r s.act elo ehi) (hroot : Rooted (protOf K rt s.act) s.r.G [])
    (D : ℕ) (hD : ∀ p, (s.r.G.children p).length ≤ D) (u : ℕ × α × α) (hx : u.1 < G0.N)
    (hmk : ∀ g, g < gs.q.r.G.N → gs.marks g = false) :
    (mergeG u gs).1 = mergedR u gs.q.r ∧ candG u gs = candR u gs.q.r ∧
    (candR u gs.q.r).Nodup ∧
    (∀ e ∈ candR u gs.q.r, e.2 ∈ (wR u gs.q.r).G.children e.1) ∧
    retireListG (candR u gs.q.r) (wR u gs.q.r) = retireListH (candR u gs.q.r) (wR u gs.q.r) ∧
    (relStepG K rt u gs).1.q = (relStepR K rt u gs.q).1 ∧
    (∀ g, gs.marks g = false → (relStepG K rt u gs).1.marks g = false) ∧
    (relStepR K rt u gs.q).2 + (recLo u gs.q.r).2.2.length ≤ (relStepG K rt u gs).2 ∧
    (relStepG K rt u gs).2 ≤ (relStepR K rt u gs.q).2 + (recLo u gs.q.r).2.2.length + 1 ∧
    waveDone gs.q.r.G u.1 u.2.1 gs.q.r.lo ∧ waveDone gs.q.r.G u.1 u.2.2 gs.q.r.hi ∧
    doneR (protOf K rt gs.q.act)
      (relFuel (retireListG (candG u gs) (wR u gs.q.r)).1.G ((candG u gs).map Prod.snd))
      ((candG u gs).map Prod.snd) (retireListG (candG u gs) (wR u gs.q.r)).1 := by
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -, -⟩ := relStepR_spec h hinv hroot D hD u hx
  have hGeq : gs.q.r.G = s.r.G := h.r.G
  have hwf : gs.q.r.G.WF := hGeq ▸ hinv.wf
  have hxs : u.1 < s.r.G.N := by rw [hinv.nEq]; exact hx
  have hmkh : ∀ g ∈ (recHi u gs.q.r).2.2, gs.marks g = false :=
    fun g hg => hmk g ((a2.2 g).1 hg).1
  obtain ⟨m1, m2, m3⟩ := mergeM_spec gs.marks (recLo u gs.q.r).2.2 (recHi u gs.q.r).2.2 hmkh
  have eM : (mergeG u gs).1 = mergedR u gs.q.r := by
    show (mergeM gs.marks (recLo u gs.q.r).2.2 (recHi u gs.q.r).2.2).1
      = (recLo u gs.q.r).2.2 ++ (recHi u gs.q.r).2.2.filter
          (fun g => decide ((recLo u gs.q.r).1.val g = gs.q.r.lo.val g))
    rw [m1]
    congr 1
    apply List.filter_congr
    intro g hg
    have hgN : g < gs.q.r.G.N := ((a2.2 g).1 hg).1
    by_cases e : (recLo u gs.q.r).1.val g = gs.q.r.lo.val g
    · have hn : g ∉ (recLo u gs.q.r).2.2 := fun hm => ((a1.2 g).1 hm).2 e
      simp [e, hn]
    · have hm : g ∈ (recLo u gs.q.r).2.2 := (a1.2 g).2 ⟨hgN, e⟩
      simp [e, hm]
  have eC : candG u gs = candR u gs.q.r := by
    show (buildCand gs.q.r.G (mergeG u gs).1).1 = (buildCand gs.q.r.G (mergedR u gs.q.r)).1
    rw [eM]
  have nC : (candR u gs.q.r).Nodup := by
    show ((mergedR u gs.q.r).flatMap
      (fun g => (gs.q.r.G.parents g).map (fun p => (p, g)))).Nodup
    rw [List.nodup_flatMap]
    refine ⟨fun g _ => (hwf.parents_nodup g).map (fun a b hab => (Prod.ext_iff.1 hab).1), ?_⟩
    refine List.Pairwise.imp (fun {a b} hab => ?_) a3
    intro x hx1 hx2
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx1
    obtain ⟨p', _, e⟩ := List.mem_map.1 hx2
    exact hab (Prod.ext_iff.1 e).2.symm
  have lC : ∀ e ∈ candR u gs.q.r, e.2 ∈ (wR u gs.q.r).G.children e.1 := by
    intro e he
    have he' : e ∈ (mergedR u gs.q.r).flatMap
        (fun g => (gs.q.r.G.parents g).map (fun p => (p, g))) := he
    obtain ⟨g, _, hm⟩ := List.mem_flatMap.1 he'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    exact (hwf.parents_iff g p).1 hp
  have eRet := retireListG_eq _ _ nC lC
  obtain ⟨t1, t2, t3, t4⟩ := tailG_rel K rt (candR u gs.q.r) gs.q (wR u gs.q.r) nC lC
  have eS : (relStepG K rt u gs).2 = (recLo u gs.q.r).2.1 + (recHi u gs.q.r).2.1
      + (mergeG u gs).2.2 + (buildCand gs.q.r.G (mergeG u gs).1).2
      + (tailG K rt (candG u gs) gs.q (wR u gs.q.r)).2 := rfl
  have eR : (relStepR K rt u gs.q).2 = (recLo u gs.q.r).2.1 + (recHi u gs.q.r).2.1
      + ((recLo u gs.q.r).2.2.length + (recHi u gs.q.r).2.2.length)
      + (buildCand gs.q.r.G (mergedR u gs.q.r)).2
      + (LiteralE4.tailStep K rt (fun _ _ _ _ _ => candR u gs.q.r) gs.q (wR u gs.q.r)).2 := rfl
  have m3' : (mergeG u gs).2.2 = 2 * (recLo u gs.q.r).2.2.length
      + (recHi u gs.q.r).2.2.length := m3
  rw [eC, eM, m3'] at eS
  refine ⟨eM, eC, nC, lC, eRet, ?_, fun g hg => m2 g hg, ?_, ?_, ?_, ?_, ?_⟩
  · show (tailG K rt (candG u gs) gs.q (wR u gs.q.r)).1 = _
    rw [eC]
    exact t1
  · rw [eS, eR]; omega
  · rw [eS, eR]; omega
  · rw [hGeq]
    exact waveDR_done hinv.wf u.1 u.2.1 gs.q.r.lo s.r.lo hxs h.r.lo hinv.invLo
  · rw [hGeq]
    exact waveDR_done hinv.wf u.1 u.2.2 gs.q.r.hi s.r.hi hxs h.r.hi hinv.invHi
  · rw [eC]
    exact t4 hwf

end EngineG

/-! ## 6. The executed engine on the run `R` -/

section Run

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α) (m0 : ℕ → Bool)

/-- Initial state: the initial implemented state of `LiteralK10` and the mark table
allocated from arbitrary contents `m0`. -/
def gs0 : GS α := ⟨hq0B R, (initMarks R.G0.N m0).1⟩

/-- State of the executed engine after `t` rollouts. -/
def hrunG (t : ℕ) : GS α := runSG R.K R.rt R.u R.q (gs0 R m0) t

/-- State of the executed engine immediately before the waves of rollout `t + 1`. -/
def hpreG (t : ℕ) : GS α :=
  if R.q t = true then ⟨(qRetireG R.K R.rt (hrunG R m0 t).q).1, (hrunG R m0 t).marks⟩
  else hrunG R m0 t

lemma hpreG_q (t : ℕ) (ih : (hrunG R m0 t).q = hrunR R t) :
    (hpreG R m0 t).q = hpreR R t ∧ (hpreG R m0 t).marks = (hrunG R m0 t).marks := by
  unfold hpreG hpreR
  by_cases hq : R.q t = true
  · rw [ite_eq_left hq, ite_eq_left hq]
    refine ⟨?_, rfl⟩
    show (qRetireG R.K R.rt (hrunG R m0 t).q).1 = _
    rw [(qRetireG_rel R.K R.rt _).1, ih]
  · rw [ite_eq_right hq, ite_eq_right hq]
    exact ⟨ih, rfl⟩

/-- **The executed engine computes the states of `LiteralF4`'s engine**, and its mark
table is unset on `[0, N)` before every rollout. -/
theorem simG_all : ∀ t, (hrunG R m0 t).q = hrunR R t ∧
    ∀ g, g < R.G0.N → (hrunG R m0 t).marks g = false := by
  intro t
  induction t with
  | zero => exact ⟨rfl, (initMarks_spec R.G0.N m0).1⟩
  | succ t ih =>
    obtain ⟨p1, p2⟩ := hpreG_q R m0 t ih.1
    have hP : SimQ (hpreG R m0 t).q (R.pre t) := by rw [p1]; exact (simR_all R t).2
    have hN : (hpreG R m0 t).q.r.G.N = R.G0.N := by
      rw [hP.r.G]; exact (R.pre_inv t).nEq
    have hmk : ∀ g, g < (hpreG R m0 t).q.r.G.N → (hpreG R m0 t).marks g = false := by
      intro g hg
      rw [p2]
      exact ih.2 g (hN ▸ hg)
    obtain ⟨-, -, -, -, -, e6, e7, -⟩ := relStepG_eq hP (R.pre_inv t) (R.rooted_all t).2.2
      R.D (deg_pre R t) (R.u (t + 1)) (R.hn t).1 hmk
    refine ⟨?_, fun g hg => ?_⟩
    · show (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).1.q = _
      rw [e6, p1]
      rfl
    · show (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).1.marks g = false
      exact e7 g (hmk g (hN ▸ hg))

/-- **Rollout `t + 1` of the executed engine on the run.** -/
theorem stepG (t : ℕ) :
    (hpreG R m0 t).q = hpreR R t ∧
    (mergeG (R.u (t + 1)) (hpreG R m0 t)).1 = mergedRt R t ∧
    candG (R.u (t + 1)) (hpreG R m0 t) = candRt R t ∧
    (candRt R t).Nodup ∧
    (∀ e ∈ candRt R t, e.2 ∈ (hpreR R t).r.G.children e.1) ∧
    retireListG (candRt R t) (wR1 R t) = retireListH (candRt R t) (wR1 R t) ∧
    waveDone (hpreR R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (hpreR R t).r.lo ∧
    waveDone (hpreR R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (hpreR R t).r.hi ∧
    doneR (protOf R.K R.rt (hpreR R t).act)
      (relFuel (retireListG (candRt R t) (wR1 R t)).1.G ((candRt R t).map Prod.snd))
      ((candRt R t).map Prod.snd) (retireListG (candRt R t) (wR1 R t)).1 ∧
    costSR R.K R.rt R.u R.q (hq0B R) t + (recLoR R t).length
      ≤ costSG R.K R.rt R.u R.q (gs0 R m0) t ∧
    costSG R.K R.rt R.u R.q (gs0 R m0) t
      ≤ costSR R.K R.rt R.u R.q (hq0B R) t + (recLoR R t).length + 2 := by
  obtain ⟨i1, i2⟩ := simG_all R m0 t
  obtain ⟨p1, p2⟩ := hpreG_q R m0 t i1
  have hP : SimQ (hpreG R m0 t).q (R.pre t) := by rw [p1]; exact (simR_all R t).2
  have hN : (hpreG R m0 t).q.r.G.N = R.G0.N := by
    rw [hP.r.G]; exact (R.pre_inv t).nEq
  have hmk : ∀ g, g < (hpreG R m0 t).q.r.G.N → (hpreG R m0 t).marks g = false := by
    intro g hg
    rw [p2]
    exact i2 g (hN ▸ hg)
  obtain ⟨e1, e2, e3, e4, e5, _, _, e8, e9, e10, e11, e12⟩ := relStepG_eq hP (R.pre_inv t)
    (R.rooted_all t).2.2 R.D (deg_pre R t) (R.u (t + 1)) (R.hn t).1 hmk
  rw [p1] at e1 e3 e4 e5 e8 e9 e10 e11
  rw [p1] at e2
  have hq := qRetireG_rel R.K R.rt (hrunG R m0 t).q
  rw [i1] at hq
  have hcG : costSG R.K R.rt R.u R.q (gs0 R m0) t
      = (if R.q t = true then R.K + (qRetireG R.K R.rt (hrunG R m0 t).q).2 else 0)
        + (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).2 := rfl
  have hcR : costSR R.K R.rt R.u R.q (hq0B R) t
      = (if R.q t = true then R.K + (qRetireH R.K R.rt (hrunR R t)).2 else 0)
        + (relStepR R.K R.rt (R.u (t + 1)) (hpreR R t)).2 := rfl
  rw [i1] at hcG
  rw [p1] at e12
  refine ⟨p1, e1, e2, e3, e4, e5, e10, e11, ?_, ?_, ?_⟩
  · rw [e2] at e12
    exact e12
  · rw [hcG, hcR]
    have e8' : (relStepR R.K R.rt (R.u (t + 1)) (hpreR R t)).2 + (recLoR R t).length
        ≤ (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).2 := e8
    by_cases hqt : R.q t = true
    · rw [ite_eq_left hqt, ite_eq_left hqt]; omega
    · rw [ite_eq_right hqt, ite_eq_right hqt]; omega
  · rw [hcG, hcR]
    have e9' : (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).2
        ≤ (relStepR R.K R.rt (R.u (t + 1)) (hpreR R t)).2 + (recLoR R t).length + 1 := e9
    by_cases hqt : R.q t = true
    · rw [ite_eq_left hqt, ite_eq_left hqt]; omega
    · rw [ite_eq_right hqt, ite_eq_right hqt]; omega

/-- Computed cost of the `τ` rollouts and the queries at times `t < τ`. -/
def WrollG : ℕ := ∑ t ∈ range R.τ, costSG R.K R.rt R.u R.q (gs0 R m0) t

/-- Computed cost of the query at the stopping time `τ`. -/
def WlastG : ℕ := if R.q R.τ = true then R.K + (qRetireG R.K R.rt (hrunG R m0 R.τ).q).2 else 0

/-- Computed cost of the final disposal pass. -/
def WdispG : ℕ := (disposeAll (List.range R.G0.N) (hpreG R m0 R.τ).q.r.G).2

/-- Computed cost of allocating the mark table. -/
def WmarkG : ℕ := (initMarks R.G0.N m0).2

/-- **Total scalar work of the executed engine**: the given `P` and `R.H`, plus the
computed costs of initialisation (heaps and mark table), of all rollouts and queries, and
of final disposal. -/
def WG : ℕ := R.P + R.H + WinitB R + WmarkG R m0 + WrollG R m0 + WlastG R m0 + WdispG R m0

/-- **`WG` against `LiteralF4.WR`**: it adds the allocation of the mark table, the clearing
pass of every rollout, and at most one final cascade test per rollout and query. -/
theorem WG_bounds :
    WR R + ∑ t ∈ range R.τ, (recLoR R t).length + R.G0.N ≤ WG R m0 ∧
    WG R m0 ≤ WR R + ∑ t ∈ range R.τ, (recLoR R t).length + R.G0.N + 2 * R.τ + 1 := by
  have hroll1 : WrollR R + ∑ t ∈ range R.τ, (recLoR R t).length ≤ WrollG R m0 := by
    unfold WrollR WrollG
    rw [← sum_add_distrib]
    exact sum_le_sum (fun t _ => (stepG R m0 t).2.2.2.2.2.2.2.2.2.1)
  have hroll2 : WrollG R m0 ≤ WrollR R + ∑ t ∈ range R.τ, (recLoR R t).length + 2 * R.τ := by
    unfold WrollR WrollG
    have : ∑ t ∈ range R.τ, costSG R.K R.rt R.u R.q (gs0 R m0) t
        ≤ ∑ t ∈ range R.τ, (costSR R.K R.rt R.u R.q (hq0B R) t + (recLoR R t).length + 2) :=
      sum_le_sum (fun t _ => (stepG R m0 t).2.2.2.2.2.2.2.2.2.2)
    rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, smul_eq_mul] at this
    omega
  have hq := qRetireG_rel R.K R.rt (hrunG R m0 R.τ).q
  rw [(simG_all R m0 R.τ).1] at hq
  have hlast1 : WlastR R ≤ WlastG R m0 := by
    unfold WlastR WlastG
    rw [(simG_all R m0 R.τ).1]
    split_ifs <;> omega
  have hlast2 : WlastG R m0 ≤ WlastR R + 1 := by
    unfold WlastR WlastG
    rw [(simG_all R m0 R.τ).1]
    split_ifs <;> omega
  have hdisp : WdispG R m0 = WdispR R := by
    unfold WdispG WdispR
    rw [(hpreG_q R m0 R.τ (simG_all R m0 R.τ).1).1]
  have hmark : WmarkG R m0 = R.G0.N := (initMarks_spec R.G0.N m0).2
  unfold WG WR
  omega

/-- **The work bound of the executed engine**: `WG ≤ 23 · XD`. -/
theorem WG_le : WG R m0 ≤ 23 * XD R := by
  obtain ⟨_, h2⟩ := WG_bounds R m0
  have hW := WR_le R
  have hc := WcandR_le R
  have hrec : 2 * ∑ t ∈ range R.τ, (recLoR R t).length ≤ WcandR R := by
    unfold WcandR
    rw [mul_sum]
    apply sum_le_sum
    intro t _
    unfold extraR
    omega
  have hN : 1 ≤ R.G0.N := by have := (R.hn 0).1; omega
  have hS : R.Splus ≤ (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1) := by nlinarith
  have hX : R.τ + R.G0.N + R.Splus ≤ XD R := by
    unfold XD Hsh
    omega
  omega

end Run

/-! ## 7. `prop:representation-cost` for the executed engine -/

section Final

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, for the executed engine
with no fuel, membership or pre-wave-value conventions.**  Same hypotheses as
`LiteralF4.representation_cost_upper_R` (the fields of `R : LiteralK3.SelRun α`), and any
initial contents `m0` of the mark table.  Conclusions:

1. the executed engine computes the states of `LiteralF4`'s engine (hence represents the
   abstract run `RetireFinal.runF`), and its mark table is unset on `[0, N)` before every
   rollout;
2. `F_t` is the live incidence set of the executed engine before rollout `t + 1`;
3. the reference valuations are exact and `b_{t+1}(v) ≤ 2`;
4. the deliveries through `τ` are exactly `S^+`, and the computed rollout work is at least
   `S^+`;
5. after the final disposal pass no incidence is left;
6. in every rollout `t + 1`: the merged list computed with the mark table is duplicate-free
   and a permutation of `chgR R t`; the candidate list is a permutation of the `delivV`
   list, duplicate-free, and consists of live incidences, so the retirement pass without
   membership test equals `retireListH`; both waves and the release cascade terminate
   within their fuel; every cascade started from an engine state (in particular at a
   query) terminates within `relFuel`;
7. `WG ≤ 23 (H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))`, with `H = Hsh R`;
8. the same with `H` written as `R.H + τ + Q·K`;
9. if every rollout has given shared work at least one and every query time given shared
   work at least `K`, then `WG ≤ 69 · R.X`. -/
theorem representation_cost_upper_G {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α)
    (m0 : ℕ → Bool) :
    (∀ t, (hrunG R m0 t).q = hrunR R t ∧ SimQ (hrunG R m0 t).q (R.run t) ∧
      SimQ (hpreG R m0 t).q (R.pre t) ∧ ∀ g, g < R.G0.N → (hrunG R m0 t).marks g = false) ∧
    (∀ t, R.F t = liveInc (hpreG R m0 t).q.r.G) ∧
    (∀ t, Exact R.G0 (R.refLo t) ∧ Exact R.G0 (R.refHi t)) ∧ (∀ t v, R.b t v ≤ 2) ∧
    (∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus) ∧
    R.Splus ≤ WrollG R m0 ∧
    (∀ p, (disposeAll (List.range R.G0.N) (hpreG R m0 R.τ).q.r.G).1.children p = []) ∧
    (∀ t,
      (mergeG (R.u (t + 1)) (hpreG R m0 t)).1.Nodup ∧
      (mergeG (R.u (t + 1)) (hpreG R m0 t)).1.Perm (chgR R t) ∧
      (candG (R.u (t + 1)) (hpreG R m0 t)).Perm (delivV (hpreR R t).r.G (hpreR R t).r.lo.val
        (hpreR R t).r.hi.val (wR1 R t).lo.val (wR1 R t).hi.val) ∧
      (candG (R.u (t + 1)) (hpreG R m0 t)).Nodup ∧
      (∀ e ∈ candG (R.u (t + 1)) (hpreG R m0 t), e.2 ∈ (hpreG R m0 t).q.r.G.children e.1) ∧
      retireListG (candRt R t) (wR1 R t) = retireListH (candRt R t) (wR1 R t) ∧
      waveDone (hpreR R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (hpreR R t).r.lo ∧
      waveDone (hpreR R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (hpreR R t).r.hi ∧
      doneR (protOf R.K R.rt (hpreR R t).act)
        (relFuel (retireListG (candRt R t) (wR1 R t)).1.G ((candRt R t).map Prod.snd))
        ((candRt R t).map Prod.snd) (retireListG (candRt R t) (wR1 R t)).1 ∧
      ∀ (prot : ℕ → Bool) (st : List ℕ),
        doneR prot (relFuel (hrunG R m0 t).q.r.G st) st (hrunG R m0 t).q.r) ∧
    WG R m0 ≤ 23 * XD R ∧
    WG R m0 ≤ 23 * (R.H + R.τ + R.scans + R.P + R.G0.N + live R.G0
      + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)) ∧
    ((∀ t, t < R.τ → 1 ≤ R.h t) → (∀ t, t ≤ R.τ → R.q t = true → R.K ≤ R.h t) →
      WG R m0 ≤ 69 * R.X) := by
  have hF4 := representation_cost_upper_R R
  have hW := WG_le R m0
  have hpq : ∀ t, (hpreG R m0 t).q = hpreR R t :=
    fun t => (hpreG_q R m0 t (simG_all R m0 t).1).1
  refine ⟨fun t => ⟨(simG_all R m0 t).1, ?_, ?_, (simG_all R m0 t).2⟩, fun t => ?_,
    hF4.2.2.1, hF4.2.2.2.1, hF4.2.2.2.2.1, ?_, fun p => ?_, fun t => ?_, hW, ?_,
    fun ha hb => ?_⟩
  · rw [(simG_all R m0 t).1]; exact (simR_all R t).1
  · rw [hpq t]; exact (simR_all R t).2
  · rw [hpq t]; exact hF4.2.1 t
  · have h1 := hF4.2.2.2.2.2.1
    have h2 := (WG_bounds R m0).1
    have h3 : WrollR R + ∑ t ∈ range R.τ, (recLoR R t).length ≤ WrollG R m0 := by
      unfold WrollR WrollG
      rw [← sum_add_distrib]
      exact sum_le_sum (fun t _ => (stepG R m0 t).2.2.2.2.2.2.2.2.2.1)
    omega
  · rw [hpq R.τ]; exact hF4.2.2.2.2.2.2.1 p
  · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, _, _⟩ := stepG R m0 t
    obtain ⟨_, _, b3, b4, b5, _⟩ := hF4.2.2.2.2.2.2.2.1 t
    have hwf : (hrunG R m0 t).q.r.G.WF := by
      rw [(simG_all R m0 t).1, (simR_all R t).1.r.G]
      exact (R.rooted_all t).1.1
    refine ⟨?_, ?_, ?_, ?_, ?_, s6, s7, s8, s9, fun prot st => relFuel_done prot st _ hwf⟩
    · rw [s2]; exact b3
    · rw [s2]; exact b4
    · rw [s3]; exact b5
    · rw [s3]; exact s4
    · rw [s3, s1]; exact s5
  · unfold XD Hsh at hW
    exact hW
  · have h1 : R.τ ≤ R.H := by
      unfold SelRun.H
      calc R.τ = ∑ _t ∈ range R.τ, 1 := by rw [sum_const, card_range, smul_eq_mul, mul_one]
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
    unfold XD Hsh at hW
    unfold SelRun.X
    generalize (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1) = Y at *
    omega

/-- **`eq:prop-rep-upper` in `O` form** for the executed engine. -/
theorem representation_cost_upper_isBigO_G {α ι : Type*} [LinearOrder α] [OrderBot α]
    {l : Filter ι} (R : ι → SelRun α) (m0 : ι → ℕ → Bool) :
    (fun i => (WG (R i) (m0 i) : ℝ)) =O[l] (fun i => (XD (R i) : ℝ)) := by
  apply IsBigO.of_bound 23
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast WG_le (R i) (m0 i)

/-- **`prop:representation-cost` as one theorem** for the executed engine (total work
`W_G = WG (G i) (m0 i)`); `C i` is any family of implementations of the incidence-delivery
contract.

1. `W_G ≤ 23 X_G` for every `i`, hence `W_G = O(X_G)`;
2. `P_C + S_C^- ≤ W_C` for every `i`;
3. condition (R), `X_G = o(P_C + S_C^-)`, implies `W_G = o(W_C)`. -/
theorem representation_cost {α β Cell ι : Type*} [LinearOrder α] [OrderBot α]
    [DecidableEq β] [DecidableEq Cell] {l : Filter ι}
    (G : ι → SelRun α) (m0 : ι → ℕ → Bool) (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WG (G i) (m0 i) ≤ 23 * XD (G i)) ∧
    (fun i => (WG (G i) (m0 i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WG (G i) (m0 i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  have hG := representation_cost_upper_isBigO_G (l := l) G m0
  exact ⟨fun i => WG_le (G i) (m0 i), hG, fun i => (C i).lower,
    fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)** for the executed engine: against the retirement engine itself
as the compiled representation (`LiteralK4.engineImpl`). -/
theorem condition_R_engine_G {α β ι : Type*} [LinearOrder α] [OrderBot α] [LinearOrder β]
    [OrderBot β] {l : Filter ι} (G : ι → SelRun α) (m0 : ι → ℕ → Bool) (RC : ι → EngineRun β)
    (hR : (fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WG (G i) (m0 i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
  have hR' : (fun i => (XD (G i) : ℝ)) =o[l]
      (fun i => (((LiteralK4.engineImpl (RC i)).P
        + (LiteralK4.engineImpl (RC i)).Sminus : ℕ) : ℝ)) := by
    have e : (fun i => (((LiteralK4.engineImpl (RC i)).P
          + (LiteralK4.engineImpl (RC i)).Sminus : ℕ) : ℝ))
        = (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ)) := by
      funext i
      rw [LiteralK4.engineImpl_Sminus]
      rfl
    rw [e]
    exact hR
  have h1 := (LiteralG2.representation_cost (l := l) G m0
    (fun i => LiteralK4.engineImpl (RC i))).2.2.2 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast LiteralK4.engineImpl_W_le (RC i)

end Final

/-! ## 8. Heap sifts: the fuel `⌈log₂ n⌉` suffices -/

section HeapFuel

open HeapImpl (siftUp siftDown bigChild par par_eq_iff bigChild_spec fuel_up fuel_dn)

variable {ι β : Type*} [DecidableEq ι] [LinearOrder β]

/-- Sift-up stops by its own test before the fuel runs out. -/
def doneUp : ℕ → Heap ι β → ℕ → Prop
  | 0, H, j => ¬ (0 < j ∧ H.ky (par j) < H.ky j)
  | d + 1, H, j =>
    if 0 < j ∧ H.ky (par j) < H.ky j then doneUp d (H.swap j (par j)) (par j) else True

/-- Sift-down stops by its own test before the fuel runs out. -/
def doneDn : ℕ → Heap ι β → ℕ → Prop
  | 0, H, j => ¬ (2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j))
  | d + 1, H, j =>
    if 2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j) then
      doneDn d (H.swap j (bigChild H j)) (bigChild H j)
    else True

/-- **Sift-up terminates within fuel `d`** when `j + 1 < 2^(d+1)`. -/
theorem siftUp_done : ∀ (d : ℕ) (H : Heap ι β) (j : ℕ), j + 1 < 2 ^ (d + 1) →
    doneUp d H j := by
  intro d
  induction d with
  | zero =>
    intro H j hd
    have : j = 0 := by simp at hd; omega
    exact fun hc => absurd hc.1 (by omega)
  | succ d ih =>
    intro H j hd
    rw [doneUp]
    split_ifs with hc
    · have hfuel : par j + 1 < 2 ^ (d + 1) := by
        have : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
        unfold par; omega
      exact ih _ _ hfuel

/-- **Sift-down terminates within fuel `d`** when `n ≤ (j + 1) 2^d`. -/
theorem siftDown_done : ∀ (d : ℕ) (H : Heap ι β) (j : ℕ), H.n ≤ (j + 1) * 2 ^ d →
    doneDn d H j := by
  intro d
  induction d with
  | zero =>
    intro H j hd
    simp at hd
    exact fun hc => absurd hc.1 (by omega)
  | succ d ih =>
    intro H j hd
    rw [doneDn]
    split_ifs with hc
    · obtain ⟨hm0, _, hpm, _⟩ := bigChild_spec H j hc.1
      have hfuel : H.n ≤ (bigChild H j + 1) * 2 ^ d := by
        have h1 : 2 * (j + 1) ≤ bigChild H j + 1 := by
          have := (par_eq_iff hm0).1 hpm; omega
        calc H.n ≤ (j + 1) * 2 ^ (d + 1) := hd
          _ = 2 * (j + 1) * 2 ^ d := by ring
          _ ≤ (bigChild H j + 1) * 2 ^ d := Nat.mul_le_mul_right _ h1
      exact ih _ _ hfuel

/-- **More fuel gives the same sift-up** (state and cost). -/
theorem siftUp_fuel : ∀ (d : ℕ) (H : Heap ι β) (j : ℕ), doneUp d H j →
    ∀ k, siftUp (d + k) H j = siftUp d H j := by
  intro d
  induction d with
  | zero =>
    intro H j h k
    have h' : ¬ (0 < j ∧ H.ky (par j) < H.ky j) := h
    cases k with
    | zero => rfl
    | succ k =>
      rw [Nat.zero_add]
      show siftUp (k + 1) H j = (H, 1)
      rw [siftUp, ite_eq_right h']
  | succ d ih =>
    intro H j h k
    rw [doneUp] at h
    rw [Nat.add_right_comm, siftUp, siftUp]
    by_cases hc : 0 < j ∧ H.ky (par j) < H.ky j
    · rw [ite_eq_left hc] at h
      rw [ite_eq_left hc, ite_eq_left hc, ih _ _ h k]
    · rw [ite_eq_right hc, ite_eq_right hc]

/-- **More fuel gives the same sift-down** (state and cost). -/
theorem siftDown_fuel : ∀ (d : ℕ) (H : Heap ι β) (j : ℕ), doneDn d H j →
    ∀ k, siftDown (d + k) H j = siftDown d H j := by
  intro d
  induction d with
  | zero =>
    intro H j h k
    have h' : ¬ (2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j)) := h
    cases k with
    | zero => rfl
    | succ k =>
      rw [Nat.zero_add]
      show siftDown (k + 1) H j = (H, 1)
      rw [siftDown, ite_eq_right h']
  | succ d ih =>
    intro H j h k
    rw [doneDn] at h
    rw [Nat.add_right_comm, siftDown, siftDown]
    by_cases hc : 2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j)
    · rw [ite_eq_left hc] at h
      rw [ite_eq_left hc, ite_eq_left hc, ih _ _ h k]
    · rw [ite_eq_right hc, ite_eq_right hc]

/-- The sifts of `HeapImpl.updateAt` at a valid position terminate within their fuel. -/
theorem updateAt_done (H : Heap ι β) (i : ℕ) (x : β) (hi : i < H.n) :
    doneUp (Nat.clog 2 H.n) (H.setKey i x) i ∧ doneDn (Nat.clog 2 H.n) (H.setKey i x) i :=
  ⟨siftUp_done _ _ _ (fuel_up hi), siftDown_done _ _ _ (fuel_dn (n := H.n) i)⟩

/-- The sift of `HeapImpl.insert` terminates within its fuel. -/
theorem insert_done (H : Heap ι β) (h : ι) (x : β) :
    doneUp (Nat.clog 2 (H.n + 1)) (H.append h x) H.n :=
  siftUp_done _ _ _ (fuel_up (Nat.lt_succ_self H.n))

/-- The sifts of `HeapImpl.deleteAt` at a valid position terminate within their fuel. -/
theorem deleteAt_done (H : Heap ι β) (h : ι) (i : ℕ) (hi : i < H.n) :
    doneUp (Nat.clog 2 H.n) (H.moveLast h i) i ∧ doneDn (Nat.clog 2 H.n) (H.moveLast h i) i :=
  ⟨siftUp_done _ _ _ (fuel_up hi),
    siftDown_done _ _ _ (show H.n - 1 ≤ _ from (Nat.sub_le _ _).trans (fuel_dn (n := H.n) i))⟩

/-- `updateKey` and `delete` on a heap with a valid position map call `updateAt` /
`deleteAt` at a valid position, so their sifts terminate within their fuel. -/
theorem pos_lt (H : Heap ι β) (hP : H.PosOK) (h : ι) (i : ℕ) (hpos : H.pos h = some i) :
    i < H.n := (hP.bwd h i hpos).1

/-- The sift of each step of `LiteralE7a.heapLoop` (bottom-up heapify) terminates within
its fuel. -/
theorem heapLoop_done (H : Heap ι β) (j : ℕ) : doneDn (Nat.clog 2 H.n) H j :=
  siftDown_done _ _ _ (fuel_dn (n := H.n) j)

end HeapFuel

/-! ## 9. The protection index -/

section Protect

/-- Number of active root actions whose gate is `g`. -/
def cntL (K : ℕ) (rt : ℕ → ℕ) (act : ℕ → Bool) (g : ℕ) : ℕ :=
  ((List.range K).filter (fun i => act i && decide (rt i = g))).length

/-- **The protection lookup**: one read of the count table. -/
def pidx (c : ℕ → ℕ) (g : ℕ) : Bool := decide (0 < c g)

/-- The lookup in a correct count table is `protOf`. -/
lemma protOf_cnt (K : ℕ) (rt : ℕ → ℕ) (act : ℕ → Bool) (g : ℕ) :
    protOf K rt act g = pidx (cntL K rt act) g := by
  unfold protOf pidx cntL
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, List.length_pos_iff_exists_mem]
  simp only [List.mem_filter]

/-- Increment the counts at the gates of `l` (1 unit per write). -/
def incAll : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) × ℕ
  | [], c => (c, 0)
  | g :: l, c => ((incAll l (Function.update c g (c g + 1))).1,
      (incAll l (Function.update c g (c g + 1))).2 + 1)

/-- Decrement the counts at the gates of `l` (1 unit per write). -/
def decAll : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) × ℕ
  | [], c => (c, 0)
  | g :: l, c => ((decAll l (Function.update c g (c g - 1))).1,
      (decAll l (Function.update c g (c g - 1))).2 + 1)

/-- Set the counts at the gates of `l` to zero (1 unit per write). -/
def zeroAll : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) × ℕ
  | [], c => (c, 0)
  | g :: l, c => ((zeroAll l (Function.update c g 0)).1,
      (zeroAll l (Function.update c g 0)).2 + 1)

lemma incAll_spec : ∀ (l : List ℕ) (c : ℕ → ℕ),
    (∀ g, (incAll l c).1 g = c g + l.count g) ∧ (incAll l c).2 = l.length := by
  intro l
  induction l with
  | nil => intro c; exact ⟨fun g => rfl, rfl⟩
  | cons a l ih =>
    intro c
    obtain ⟨h1, h2⟩ := ih (Function.update c a (c a + 1))
    refine ⟨fun g => ?_, ?_⟩
    · show (incAll l (Function.update c a (c a + 1))).1 g = _
      rw [h1 g, List.count_cons]
      by_cases e : g = a
      · subst e; simp; omega
      · simp [e, Function.update_of_ne e, Ne.symm e]
    · show (incAll l (Function.update c a (c a + 1))).2 + 1 = _
      rw [h2, List.length_cons]

lemma decAll_spec : ∀ (l : List ℕ) (c : ℕ → ℕ),
    (∀ g, (decAll l c).1 g = c g - l.count g) ∧ (decAll l c).2 = l.length := by
  intro l
  induction l with
  | nil => intro c; exact ⟨fun g => rfl, rfl⟩
  | cons a l ih =>
    intro c
    obtain ⟨h1, h2⟩ := ih (Function.update c a (c a - 1))
    refine ⟨fun g => ?_, ?_⟩
    · show (decAll l (Function.update c a (c a - 1))).1 g = _
      rw [h1 g, List.count_cons]
      by_cases e : g = a
      · subst e; simp; omega
      · simp [e, Function.update_of_ne e, Ne.symm e]
    · show (decAll l (Function.update c a (c a - 1))).2 + 1 = _
      rw [h2, List.length_cons]

lemma zeroAll_spec : ∀ (l : List ℕ) (c : ℕ → ℕ),
    (∀ g, g ∈ l → (zeroAll l c).1 g = 0) ∧ (zeroAll l c).2 = l.length := by
  intro l
  induction l with
  | nil => intro c; exact ⟨fun g hg => absurd hg List.not_mem_nil, rfl⟩
  | cons a l ih =>
    intro c
    refine ⟨fun g hg => ?_, ?_⟩
    · show (zeroAll l (Function.update c a 0)).1 g = 0
      have hval : ∀ (l : List ℕ) (c : ℕ → ℕ) (g : ℕ), g ∉ l → (zeroAll l c).1 g = c g := by
        intro l
        induction l with
        | nil => intro c g _; rfl
        | cons b l ih2 =>
          intro c g hg
          show (zeroAll l (Function.update c b 0)).1 g = _
          rw [ih2 _ g (fun h => hg (List.mem_cons_of_mem _ h))]
          exact Function.update_of_ne (fun e => hg (by rw [e]; exact List.mem_cons_self)) _ _
      by_cases hm : g ∈ l
      · exact (ih _).1 g hm
      · rw [hval l _ g hm]
        have : g = a := by
          rcases List.mem_cons.1 hg with e | e
          · exact e
          · exact absurd e hm
        subst this
        exact Function.update_self _ _ _
    · show (zeroAll l (Function.update c a 0)).2 + 1 = _
      rw [(ih _).2, List.length_cons]

lemma count_map_filter (rt : ℕ → ℕ) (g : ℕ) (P : ℕ → Bool) : ∀ l : List ℕ,
    ((l.filter P).map rt).count g = (l.filter (fun i => P i && decide (rt i = g))).length := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hp : P x = true
    · by_cases hr : rt x = g
      · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (by simp [hp, hr]),
          List.map_cons, List.count_cons, List.length_cons, ih]
        simp [hr]
      · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by simp [hr]),
          List.map_cons, List.count_cons, ih]
        simp [hr]
    · rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg (by simp [hp]), ih]

lemma length_filter_split (p q r : ℕ → Bool) : ∀ l : List ℕ,
    (∀ x ∈ l, p x = (q x || r x)) → (∀ x ∈ l, ¬ (q x = true ∧ r x = true)) →
    (l.filter p).length = (l.filter q).length + (l.filter r).length := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons x l ih =>
    intro h1 h2
    have e := ih (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
      (fun y hy => h2 y (List.mem_cons_of_mem _ hy))
    have hx := h1 x List.mem_cons_self
    have hd := h2 x List.mem_cons_self
    cases hq : q x <;> cases hr : r x
    · have hp : p x = false := by rw [hx, hq, hr]; rfl
      rw [List.filter_cons_of_neg (by rw [hp]; decide), List.filter_cons_of_neg (by rw [hq]; decide),
        List.filter_cons_of_neg (by rw [hr]; decide), e]
    · have hp : p x = true := by rw [hx, hq, hr]; rfl
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hq]; decide),
        List.filter_cons_of_pos hr, List.length_cons, List.length_cons, e]
      omega
    · have hp : p x = true := by rw [hx, hq, hr]; rfl
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq,
        List.filter_cons_of_neg (by rw [hr]; decide), List.length_cons, List.length_cons, e]
      omega
    · exact absurd ⟨hq, hr⟩ hd

/-- **Deactivation and the count table**: the count after deactivation plus the number of
retired roots at `g` is the count before. -/
lemma cnt_deact {α : Type*} [LinearOrder α] (K a : ℕ) (rt : ℕ → ℕ) (U : ℕ → α) (la : α)
    (act : ℕ → Bool) (g : ℕ) :
    cntL K rt (deact K a U la act) g + (retiredRoots K rt a U la act).count g
      = cntL K rt act g := by
  unfold cntL retiredRoots
  rw [count_map_filter]
  symm
  apply length_filter_split
  · intro i hi
    have hiK := List.mem_range.1 hi
    cases hact : act i <;> cases h1 : decide (i = a) <;> cases h2 : decide (U i < la) <;>
      simp [deact, hiK, hact, h1, h2]
  · intro i hi h
    have hiK := List.mem_range.1 hi
    obtain ⟨hq, hr⟩ := h
    cases hact : act i <;> by_cases h1 : i = a <;> by_cases h2 : U i < la <;>
      simp_all [deact]

lemma retiredRoots_length {α : Type*} [LinearOrder α] (K a : ℕ) (rt : ℕ → ℕ) (U : ℕ → α)
    (la : α) (act : ℕ → Bool) : (retiredRoots K rt a U la act).length ≤ K := by
  unfold retiredRoots
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

end Protect

/-! ## 10. The engine with the protection index -/

section EngineP

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma releaseLoopG_N (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (s : HRState α),
    (releaseLoopG prot f st s).1.G.N = s.G.N := by
  intro f
  induction f with
  | zero => intro st s; rfl
  | succ f ih =>
    intro st s
    cases st with
    | nil => rfl
    | cons g st =>
      rw [releaseLoopG]
      split_ifs
      · exact ih _ _
      · exact ih _ _

/-- **The cascade only reads the protection of gates `< N`**: two protection functions
that agree there give the same cascade (state and cost). -/
theorem releaseLoopG_congr (p1 p2 : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (s : HRState α),
    s.G.WF → (∀ g, g < s.G.N → p1 g = p2 g) →
    releaseLoopG p1 f st s = releaseLoopG p2 f st s := by
  intro f
  induction f with
  | zero => intro st s _ _; rfl
  | succ f ih =>
    intro st s hG hp
    cases st with
    | nil => rfl
    | cons g st =>
      have hiff : (s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ p1 g = false) ↔
          (s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ p2 g = false) := by
        constructor
        · rintro ⟨h1, h2, h3⟩
          obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ h1
          have hgN : g < s.G.N := hG.parent_lt c g ((hG.parents_iff c g).2 hcm)
          exact ⟨h1, h2, by rw [← hp g hgN]; exact h3⟩
        · rintro ⟨h1, h2, h3⟩
          obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ h1
          have hgN : g < s.G.N := hG.parent_lt c g ((hG.parents_iff c g).2 hcm)
          exact ⟨h1, h2, by rw [hp g hgN]; exact h3⟩
      rw [releaseLoopG, releaseLoopG]
      by_cases hc : s.G.children g ≠ [] ∧ s.G.parents g = [] ∧ p2 g = false
      · rw [ite_eq_left (hiff.2 hc), ite_eq_left hc,
          ih (s.G.children g ++ st)
            ⟨releaseDag s.G g, ⟨s.lo.val, Function.update s.lo.hp g Heap.empty⟩,
              ⟨s.hi.val, Function.update s.hi.hp g Heap.empty⟩⟩
            (releaseDag_wf hG g) (fun g' hg' => hp g' hg')]
      · rw [ite_eq_right (fun h => hc (hiff.1 h)), ite_eq_right hc, ih st s hG hp]

omit [OrderBot α] in
lemma retireListG_G : ∀ (L : List (ℕ × ℕ)) (s : HRState α), s.G.WF →
    (retireListG L s).1.G.WF ∧ (retireListG L s).1.G.N = s.G.N := by
  intro L
  induction L with
  | nil => intro s h; exact ⟨h, rfl⟩
  | cons e es ih =>
    intro s h
    have h1 : (retireOneG e s).1.G.WF ∧ (retireOneG e s).1.G.N = s.G.N := by
      unfold retireOneG
      split_ifs
      · exact ⟨retireDag_wf h _ _, rfl⟩
      · exact ⟨h, rfl⟩
    obtain ⟨a1, a2⟩ := ih _ h1.1
    exact ⟨a1, a2.trans h1.2⟩

/-- The tail with the protection function `pr`. -/
def tailP (pr : ℕ → Bool) (cand : List (ℕ × ℕ)) (s : HQS α) (w : HRState α) : HQS α × ℕ :=
  (⟨(releaseLoopG pr (relFuel (retireListG cand w).1.G (cand.map Prod.snd))
      (cand.map Prod.snd) (retireListG cand w).1).1, s.act⟩,
   (retireListG cand w).2
    + (releaseLoopG pr (relFuel (retireListG cand w).1.G (cand.map Prod.snd))
      (cand.map Prod.snd) (retireListG cand w).1).2)

/-- **One rollout with the protection index**: as `relStepG`, the cascade reading the
protection function `pr` (in the engine, `pidx` of the count table: one read). -/
def relStepP (pr : ℕ → Bool) (u : ℕ × α × α) (s : GS α) : GS α × ℕ :=
  (⟨(tailP pr (candG u s) s.q (wR u s.q.r)).1, (mergeG u s).2.1⟩,
   (recLo u s.q.r).2.1 + (recHi u s.q.r).2.1 + (mergeG u s).2.2
     + (buildCand s.q.r.G (mergeG u s).1).2 + (tailP pr (candG u s) s.q (wR u s.q.r)).2)

/-- **Root retirement with the count table**: as `qRetireG`; after the scan, the counts of
the gates of the retired roots are decremented (one write per retired root), and the
cascade reads the protection from the updated table. -/
def qRetireP (K : ℕ) (rt : ℕ → ℕ) (c : ℕ → ℕ) (s : HQS α) : HQS α × (ℕ → ℕ) × ℕ :=
  (leadScan (fun i => s.r.lo.val (rt i)) s.act K).elim (s, c, K)
    (fun a =>
      (⟨(releaseLoopG
            (pidx (decAll (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
              s.act) c).1)
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r).1,
        deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act⟩,
       (decAll (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
          c).1,
       K + K + (decAll (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
          s.act) c).2
         + (releaseLoopG
            (pidx (decAll (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
              s.act) c).1)
            (relFuel s.r.G
              (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act))
            (retiredRoots K rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act)
            s.r).2))

variable {K : ℕ} {rt : ℕ → ℕ}

theorem tailP_eq (pr : ℕ → Bool) (cand : List (ℕ × ℕ)) (s : HQS α) (w : HRState α)
    (hw : w.G.WF) (hp : ∀ g, g < w.G.N → pr g = protOf K rt s.act g) :
    tailP pr cand s w = tailG K rt cand s w := by
  obtain ⟨h1, h2⟩ := retireListG_G cand w hw
  unfold tailP tailG
  rw [releaseLoopG_congr pr (protOf K rt s.act) _ _ _ h1 (fun g hg => hp g (h2 ▸ hg))]

/-- With a protection function that agrees with `protOf` below `N`, the rollout is
`relStepG` (state and cost). -/
theorem relStepP_eq (pr : ℕ → Bool) (u : ℕ × α × α) (gs : GS α) (hw : gs.q.r.G.WF)
    (hp : ∀ g, g < gs.q.r.G.N → pr g = protOf K rt gs.q.act g) :
    relStepP pr u gs = relStepG K rt u gs := by
  unfold relStepP relStepG
  rw [tailP_eq (K := K) (rt := rt) pr (candG u gs) gs.q (wR u gs.q.r) hw hp]

lemma qRetireG_N (s : HQS α) : (qRetireG K rt s).1.r.G.N = s.r.G.N := by
  unfold qRetireG
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => rfl
  | some a =>
    dsimp only [Option.elim]
    exact releaseLoopG_N _ _ _ _

/-- **Root retirement with the count table against `qRetireG`**: same state; the count
table is correct for the new activity flags below `N`; the cost exceeds that of `qRetireG`
by the number of retired roots, at most `K`. -/
theorem qRetireP_eq (c : ℕ → ℕ) (s : HQS α) (hw : s.r.G.WF)
    (hc : ∀ g, g < s.r.G.N → c g = cntL K rt s.act g) :
    (qRetireP K rt c s).1 = (qRetireG K rt s).1 ∧
    (∀ g, g < s.r.G.N → (qRetireP K rt c s).2.1 g = cntL K rt (qRetireG K rt s).1.act g) ∧
    (qRetireG K rt s).2 ≤ (qRetireP K rt c s).2.2 ∧
    (qRetireP K rt c s).2.2 ≤ (qRetireG K rt s).2 + K := by
  unfold qRetireP qRetireG
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none =>
    dsimp only [Option.elim]
    exact ⟨rfl, hc, le_rfl, Nat.le_add_right _ _⟩
  | some a =>
    dsimp only [Option.elim]
    set U : ℕ → α := fun i => s.r.hi.val (rt i) with hU
    set la : α := s.r.lo.val (rt a) with hla
    obtain ⟨d1, d2⟩ := decAll_spec (retiredRoots K rt a U la s.act) c
    have hnew : ∀ g, g < s.r.G.N →
        (decAll (retiredRoots K rt a U la s.act) c).1 g = cntL K rt (deact K a U la s.act) g := by
      intro g hg
      rw [d1 g, hc g hg, ← cnt_deact K a rt U la s.act g]
      omega
    have hagree : ∀ g, g < s.r.G.N →
        pidx (decAll (retiredRoots K rt a U la s.act) c).1 g
          = protOf K rt (deact K a U la s.act) g := by
      intro g hg
      rw [protOf_cnt]
      unfold pidx
      rw [hnew g hg]
    have hrel := releaseLoopG_congr _ _
      (relFuel s.r.G (retiredRoots K rt a U la s.act)) (retiredRoots K rt a U la s.act) s.r hw
      hagree
    have hlen := retiredRoots_length K a rt U la s.act
    rw [hrel]
    refine ⟨rfl, hnew, ?_, ?_⟩
    · omega
    · rw [d2]; omega

end EngineP
/-! ## 11. The run with the protection index -/

section RunP

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- State of the engine with the protection index: the state of the engine of `relStepG`
and the count table (number of active root actions per gate). -/
structure GP (α : Type*) where
  s : GS α
  cnt : ℕ → ℕ

/-- A query on the engine with the protection index. -/
def qStepP (K : ℕ) (rt : ℕ → ℕ) (x : GP α) : GP α :=
  ⟨⟨(qRetireP K rt x.cnt x.s.q).1, x.s.marks⟩, (qRetireP K rt x.cnt x.s.q).2.1⟩

/-- State of the engine with the protection index after `t` rollouts: every cascade reads
the protection of a gate from the count table (`pidx`). -/
def runSP (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (x0 : GP α) : ℕ → GP α
  | 0 => x0
  | t + 1 =>
    ⟨(relStepP (pidx (if q t = true then qStepP K rt (runSP K rt u q x0 t)
          else runSP K rt u q x0 t).cnt) (u (t + 1))
        (if q t = true then qStepP K rt (runSP K rt u q x0 t) else runSP K rt u q x0 t).s).1,
     (if q t = true then qStepP K rt (runSP K rt u q x0 t) else runSP K rt u q x0 t).cnt⟩

/-- Computed cost of the query of time `t` (if any) and of rollout `t + 1`. -/
def costSP (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (x0 : GP α) (t : ℕ) : ℕ :=
  (if q t = true then K + (qRetireP K rt (runSP K rt u q x0 t).cnt (runSP K rt u q x0 t).s.q).2.2
    else 0)
    + (relStepP (pidx (if q t = true then qStepP K rt (runSP K rt u q x0 t)
          else runSP K rt u q x0 t).cnt) (u (t + 1))
        (if q t = true then qStepP K rt (runSP K rt u q x0 t) else runSP K rt u q x0 t).s).2

variable (R : SelRun α) (m0 : ℕ → Bool) (c0 : ℕ → ℕ)

/-- **Construction of the count table** from arbitrary contents `c0`: zero the entries of
the gates `< N` (one write each), then one increment per root action. -/
def initCnt : (ℕ → ℕ) × ℕ :=
  ((incAll ((List.range R.K).map R.rt) (zeroAll (List.range R.G0.N) c0).1).1,
   (zeroAll (List.range R.G0.N) c0).2
     + (incAll ((List.range R.K).map R.rt) (zeroAll (List.range R.G0.N) c0).1).2)

lemma initCnt_spec :
    (∀ g, g < R.G0.N → (initCnt R c0).1 g = cntL R.K R.rt (fun _ => true) g) ∧
    (initCnt R c0).2 = R.G0.N + R.K := by
  obtain ⟨z1, z2⟩ := zeroAll_spec (List.range R.G0.N) c0
  obtain ⟨i1, i2⟩ := incAll_spec ((List.range R.K).map R.rt) (zeroAll (List.range R.G0.N) c0).1
  refine ⟨fun g hg => ?_, ?_⟩
  · show (incAll ((List.range R.K).map R.rt) (zeroAll (List.range R.G0.N) c0).1).1 g = _
    rw [i1 g, z1 g (List.mem_range.2 hg), Nat.zero_add]
    have := count_map_filter R.rt g (fun _ => true) (List.range R.K)
    rw [List.filter_true] at this
    exact this
  · show (zeroAll (List.range R.G0.N) c0).2
        + (incAll ((List.range R.K).map R.rt) (zeroAll (List.range R.G0.N) c0).1).2 = _
    rw [z2, i2, List.length_map, List.length_range, List.length_range]

/-- Initial state. -/
def p0 : GP α := ⟨gs0 R m0, (initCnt R c0).1⟩

/-- State after `t` rollouts. -/
def hrunP (t : ℕ) : GP α := runSP R.K R.rt R.u R.q (p0 R m0 c0) t

/-- State before the waves of rollout `t + 1`. -/
def hpreP (t : ℕ) : GP α :=
  if R.q t = true then qStepP R.K R.rt (hrunP R m0 c0 t) else hrunP R m0 c0 t

lemma hpreG_N (t : ℕ) : (hpreG R m0 t).q.r.G.N = R.G0.N := by
  rw [(hpreG_q R m0 t (simG_all R m0 t).1).1, (simR_all R t).2.r.G]
  exact (R.pre_inv t).nEq

lemma hrunG_N (t : ℕ) : (hrunG R m0 t).q.r.G.N = R.G0.N := by
  have hN := hpreG_N R m0 t
  unfold hpreG at hN
  by_cases hq : R.q t = true
  · rw [ite_eq_left hq] at hN
    exact (qRetireG_N (K := R.K) (rt := R.rt) (hrunG R m0 t).q).symm.trans hN
  · rw [ite_eq_right hq] at hN
    exact hN

lemma hrunG_wf (t : ℕ) : (hrunG R m0 t).q.r.G.WF := by
  rw [(simG_all R m0 t).1, (simR_all R t).1.r.G]
  exact (R.rooted_all t).1.1

lemma hpreG_wf (t : ℕ) : (hpreG R m0 t).q.r.G.WF := by
  rw [(hpreG_q R m0 t (simG_all R m0 t).1).1, (simR_all R t).2.r.G]
  exact (R.rooted_all t).2.1

lemma hpreP_eq (t : ℕ) (ih : (hrunP R m0 c0 t).s = hrunG R m0 t ∧
    ∀ g, g < R.G0.N → (hrunP R m0 c0 t).cnt g = cntL R.K R.rt (hrunG R m0 t).q.act g) :
    (hpreP R m0 c0 t).s = hpreG R m0 t ∧
    ∀ g, g < R.G0.N → (hpreP R m0 c0 t).cnt g = cntL R.K R.rt (hpreG R m0 t).q.act g := by
  unfold hpreP hpreG
  by_cases hq : R.q t = true
  · rw [ite_eq_left hq, ite_eq_left hq]
    obtain ⟨e1, e2, _, _⟩ := qRetireP_eq (K := R.K) (rt := R.rt) (hrunP R m0 c0 t).cnt
      (hrunP R m0 c0 t).s.q (by rw [ih.1]; exact hrunG_wf R m0 t)
      (by intro g hg; rw [ih.1] at hg ⊢; exact ih.2 g (hrunG_N R m0 t ▸ hg))
    refine ⟨?_, fun g hg => ?_⟩
    · show (⟨(qRetireP R.K R.rt (hrunP R m0 c0 t).cnt (hrunP R m0 c0 t).s.q).1,
          (hrunP R m0 c0 t).s.marks⟩ : GS α)
        = ⟨(qRetireG R.K R.rt (hrunG R m0 t).q).1, (hrunG R m0 t).marks⟩
      rw [e1, ih.1]
    · show (qRetireP R.K R.rt (hrunP R m0 c0 t).cnt (hrunP R m0 c0 t).s.q).2.1 g
        = cntL R.K R.rt (qRetireG R.K R.rt (hrunG R m0 t).q).1.act g
      rw [e2 g (by rw [ih.1, hrunG_N]; exact hg), ih.1]
  · rw [ite_eq_right hq, ite_eq_right hq]
    exact ih

/-- **The engine with the protection index computes the states of the engine of
`relStepG`**, and its count table is correct below `N` at every time. -/
theorem simP_all : ∀ t, (hrunP R m0 c0 t).s = hrunG R m0 t ∧
    ∀ g, g < R.G0.N → (hrunP R m0 c0 t).cnt g = cntL R.K R.rt (hrunG R m0 t).q.act g := by
  intro t
  induction t with
  | zero => exact ⟨rfl, fun g hg => (initCnt_spec R c0).1 g hg⟩
  | succ t ih =>
    obtain ⟨p1, p2⟩ := hpreP_eq R m0 c0 t ih
    refine ⟨?_, fun g hg => ?_⟩
    · show (relStepP (pidx (hpreP R m0 c0 t).cnt) (R.u (t + 1)) (hpreP R m0 c0 t).s).1
        = (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).1
      rw [p1, relStepP_eq (K := R.K) (rt := R.rt) _ _ _ (hpreG_wf R m0 t)]
      intro g hg
      rw [protOf_cnt]
      unfold pidx
      rw [p2 g (hpreG_N R m0 t ▸ hg)]
    · show (hpreP R m0 c0 t).cnt g
        = cntL R.K R.rt (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).1.q.act g
      exact p2 g hg

/-- **Rollout `t + 1` of the engine with the protection index**: the lookup is `protOf`
below `N`; the cost exceeds that of `costSG` by at most `K` at a query (the decrements). -/
theorem stepP (t : ℕ) :
    (hpreP R m0 c0 t).s = hpreG R m0 t ∧
    (∀ g, g < R.G0.N →
      pidx (hpreP R m0 c0 t).cnt g = protOf R.K R.rt (hpreP R m0 c0 t).s.q.act g) ∧
    costSG R.K R.rt R.u R.q (gs0 R m0) t ≤ costSP R.K R.rt R.u R.q (p0 R m0 c0) t ∧
    costSP R.K R.rt R.u R.q (p0 R m0 c0) t
      ≤ costSG R.K R.rt R.u R.q (gs0 R m0) t + (if R.q t = true then R.K else 0) := by
  have ih := simP_all R m0 c0 t
  obtain ⟨p1, p2⟩ := hpreP_eq R m0 c0 t ih
  have hlook : ∀ g, g < R.G0.N →
      pidx (hpreP R m0 c0 t).cnt g = protOf R.K R.rt (hpreP R m0 c0 t).s.q.act g := by
    intro g hg
    rw [p1, protOf_cnt]
    unfold pidx
    rw [p2 g hg]
  have hrol : (relStepP (pidx (hpreP R m0 c0 t).cnt) (R.u (t + 1)) (hpreP R m0 c0 t).s).2
      = (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).2 := by
    rw [relStepP_eq (K := R.K) (rt := R.rt) _ _ _ (by rw [p1]; exact hpreG_wf R m0 t)
      (fun g hg => hlook g (by rw [p1, hpreG_N] at hg; exact hg)), p1]
  obtain ⟨_, _, e3, e4⟩ := qRetireP_eq (K := R.K) (rt := R.rt) (hrunP R m0 c0 t).cnt
    (hrunP R m0 c0 t).s.q (by rw [ih.1]; exact hrunG_wf R m0 t)
    (by intro g hg; rw [ih.1] at hg ⊢; exact ih.2 g (hrunG_N R m0 t ▸ hg))
  rw [ih.1] at e3 e4
  have hcP : costSP R.K R.rt R.u R.q (p0 R m0 c0) t
      = (if R.q t = true then R.K + (qRetireP R.K R.rt (hrunP R m0 c0 t).cnt
          (hrunP R m0 c0 t).s.q).2.2 else 0)
        + (relStepP (pidx (hpreP R m0 c0 t).cnt) (R.u (t + 1)) (hpreP R m0 c0 t).s).2 := rfl
  have hcG : costSG R.K R.rt R.u R.q (gs0 R m0) t
      = (if R.q t = true then R.K + (qRetireG R.K R.rt (hrunG R m0 t).q).2 else 0)
        + (relStepG R.K R.rt (R.u (t + 1)) (hpreG R m0 t)).2 := rfl
  rw [ih.1] at hcP
  refine ⟨p1, hlook, ?_, ?_⟩
  · rw [hcP, hcG, hrol]
    by_cases hq : R.q t = true
    · rw [ite_eq_left hq, ite_eq_left hq]; omega
    · rw [ite_eq_right hq, ite_eq_right hq]
  · rw [hcP, hcG, hrol]
    by_cases hq : R.q t = true
    · rw [ite_eq_left hq, ite_eq_left hq, ite_eq_left hq]; omega
    · rw [ite_eq_right hq, ite_eq_right hq, ite_eq_right hq]
      omega

/-- Computed cost of the rollouts and queries at times `t < τ`. -/
def WrollP : ℕ := ∑ t ∈ range R.τ, costSP R.K R.rt R.u R.q (p0 R m0 c0) t

/-- Computed cost of the query at the stopping time. -/
def WlastP : ℕ := if R.q R.τ = true then
    R.K + (qRetireP R.K R.rt (hrunP R m0 c0 R.τ).cnt (hrunP R m0 c0 R.τ).s.q).2.2 else 0

/-- Computed cost of the final disposal pass. -/
def WdispP : ℕ := (disposeAll (List.range R.G0.N) (hpreP R m0 c0 R.τ).s.q.r.G).2

/-- Computed cost of building the count table. -/
def WcntP : ℕ := (initCnt R c0).2

/-- **Total scalar work of the engine with the protection index**: the given `P` and
`R.H`, plus the computed costs of initialisation (heaps, mark table, count table), of all
rollouts and queries (including the count decrements), and of final disposal. -/
def WP : ℕ := R.P + R.H + WinitB R + WmarkG R m0 + WcntP R c0 + WrollP R m0 c0
  + WlastP R m0 c0 + WdispP R m0 c0

theorem WP_bounds :
    WG R m0 + R.G0.N + R.K ≤ WP R m0 c0 ∧ WP R m0 c0 ≤ WG R m0 + R.G0.N + R.K + R.scans := by
  have r1 : WrollG R m0 ≤ WrollP R m0 c0 :=
    sum_le_sum (fun t _ => (stepP R m0 c0 t).2.2.1)
  have r2 : WrollP R m0 c0 ≤ WrollG R m0
      + ∑ t ∈ range R.τ, (if R.q t = true then R.K else 0) := by
    unfold WrollP WrollG
    rw [← sum_add_distrib]
    exact sum_le_sum (fun t _ => (stepP R m0 c0 t).2.2.2)
  have ih := simP_all R m0 c0 R.τ
  obtain ⟨_, _, e3, e4⟩ := qRetireP_eq (K := R.K) (rt := R.rt) (hrunP R m0 c0 R.τ).cnt
    (hrunP R m0 c0 R.τ).s.q (by rw [ih.1]; exact hrunG_wf R m0 R.τ)
    (by intro g hg; rw [ih.1] at hg ⊢; exact ih.2 g (hrunG_N R m0 R.τ ▸ hg))
  rw [ih.1] at e3 e4
  have l1 : WlastG R m0 ≤ WlastP R m0 c0 := by
    unfold WlastG WlastP
    rw [ih.1]
    split_ifs <;> omega
  have l2 : WlastP R m0 c0 ≤ WlastG R m0 + (if R.q R.τ = true then R.K else 0) := by
    unfold WlastG WlastP
    rw [ih.1]
    split_ifs <;> omega
  have hd : WdispP R m0 c0 = WdispG R m0 := by
    unfold WdispP WdispG
    rw [(hpreP_eq R m0 c0 R.τ ih).1]
  have hc : WcntP R c0 = R.G0.N + R.K := (initCnt_spec R c0).2
  have hsc : R.scans = ∑ t ∈ range R.τ, (if R.q t = true then R.K else 0)
      + (if R.q R.τ = true then R.K else 0) := by
    unfold SelRun.scans
    rw [sum_range_succ]
  unfold WP WG
  omega

/-- **The work bound with the protection index**: `WP ≤ 24 · XD + K`.  The term `K` is
the construction of the count table from the `K` root actions; `XD` contains `K` only
through the scans `Q · K` of the queries, so with no query `K` is not bounded by `XD`. -/
theorem WP_le : WP R m0 c0 ≤ 24 * XD R + R.K := by
  have h1 := (WP_bounds R m0 c0).2
  have h2 := WG_le R m0
  have h3 : R.G0.N + R.scans ≤ XD R := by unfold XD Hsh; omega
  omega

/-- **If some query occurs by time `τ`**, `K ≤ Q · K` and `WP ≤ 25 · XD`. -/
theorem WP_le_query (hq : ∃ t, t ≤ R.τ ∧ R.q t = true) : WP R m0 c0 ≤ 25 * XD R := by
  obtain ⟨t, ht, hqt⟩ := hq
  have hK : R.K ≤ R.scans := by
    unfold SelRun.scans
    have := Finset.single_le_sum (f := fun t => if R.q t = true then R.K else 0)
      (fun _ _ => Nat.zero_le _) (mem_range.2 (show t < R.τ + 1 by omega))
    simp only [hqt, ite_true] at this
    exact this
  have h1 := (WP_bounds R m0 c0).2
  have h2 := WG_le R m0
  have h3 : R.G0.N + R.scans ≤ XD R := by unfold XD Hsh; omega
  omega

end RunP

/-! ## 12. `prop:representation-cost` with the protection index -/

section FinalP

/-- **`prop:representation-cost`, upper bound, for the engine with the protection index.**

1. at every time the engine computes the states of the engine of `relStepG` (so every
   conclusion of `representation_cost_upper_G` holds for its states), and the protection
   lookup `pidx` of its count table equals `protOf` below `N`, before and after queries;
2. per rollout its cost is that of `costSG`, plus at most `K` at a query;
3. `WG + N + K ≤ WP ≤ WG + N + K + Q·K`;
4. `S^+ ≤ WrollP`;
5. `WP ≤ 24 · XD + K`, and `WP ≤ 25 · XD` if some query occurs by time `τ`. -/
theorem representation_cost_upper_P {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α)
    (m0 : ℕ → Bool) (c0 : ℕ → ℕ) :
    (∀ t, (hrunP R m0 c0 t).s = hrunG R m0 t ∧ (hrunP R m0 c0 t).s.q = hrunR R t ∧
      (∀ g, g < R.G0.N →
        pidx (hrunP R m0 c0 t).cnt g = protOf R.K R.rt (hrunP R m0 c0 t).s.q.act g) ∧
      (hpreP R m0 c0 t).s = hpreG R m0 t ∧
      (∀ g, g < R.G0.N →
        pidx (hpreP R m0 c0 t).cnt g = protOf R.K R.rt (hpreP R m0 c0 t).s.q.act g)) ∧
    (∀ t, costSG R.K R.rt R.u R.q (gs0 R m0) t ≤ costSP R.K R.rt R.u R.q (p0 R m0 c0) t ∧
      costSP R.K R.rt R.u R.q (p0 R m0 c0) t
        ≤ costSG R.K R.rt R.u R.q (gs0 R m0) t + (if R.q t = true then R.K else 0)) ∧
    WG R m0 + R.G0.N + R.K ≤ WP R m0 c0 ∧ WP R m0 c0 ≤ WG R m0 + R.G0.N + R.K + R.scans ∧
    R.Splus ≤ WrollP R m0 c0 ∧
    WP R m0 c0 ≤ 24 * XD R + R.K ∧
    ((∃ t, t ≤ R.τ ∧ R.q t = true) → WP R m0 c0 ≤ 25 * XD R) := by
  refine ⟨fun t => ?_, fun t => (stepP R m0 c0 t).2.2, (WP_bounds R m0 c0).1,
    (WP_bounds R m0 c0).2, ?_, WP_le R m0 c0, WP_le_query R m0 c0⟩
  · obtain ⟨a1, a2⟩ := simP_all R m0 c0 t
    obtain ⟨b1, b2, _, _⟩ := stepP R m0 c0 t
    refine ⟨a1, by rw [a1]; exact (simG_all R m0 t).1, fun g hg => ?_, b1, b2⟩
    rw [protOf_cnt]
    unfold pidx
    rw [a2 g hg, a1]
  · have h1 := (representation_cost_upper_G R m0).2.2.2.2.2.1
    have h2 : WrollG R m0 ≤ WrollP R m0 c0 := sum_le_sum (fun t _ => (stepP R m0 c0 t).2.2.1)
    omega

/-- **`prop:representation-cost` as one theorem** for the engine with the protection
index, on families in which every run has a query by its stopping time. -/
theorem representation_cost_P {α β Cell ι : Type*} [LinearOrder α] [OrderBot α]
    [DecidableEq β] [DecidableEq Cell] {l : Filter ι}
    (G : ι → SelRun α) (m0 : ι → ℕ → Bool) (c0 : ι → ℕ → ℕ)
    (hq : ∀ i, ∃ t, t ≤ (G i).τ ∧ (G i).q t = true) (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WP (G i) (m0 i) (c0 i) ≤ 25 * XD (G i)) ∧
    (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  have hW : ∀ i, WP (G i) (m0 i) (c0 i) ≤ 25 * XD (G i) :=
    fun i => WP_le_query (G i) (m0 i) (c0 i) (hq i)
  have hG : (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) := by
    apply IsBigO.of_bound 25
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hW i
  exact ⟨hW, hG, fun i => (C i).lower, fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)** for the engine with the protection index. -/
theorem condition_R_engine_P {α β ι : Type*} [LinearOrder α] [OrderBot α] [LinearOrder β]
    [OrderBot β] {l : Filter ι} (G : ι → SelRun α) (m0 : ι → ℕ → Bool) (c0 : ι → ℕ → ℕ)
    (hq : ∀ i, ∃ t, t ≤ (G i).τ ∧ (G i).q t = true) (RC : ι → EngineRun β)
    (hR : (fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
  have hR' : (fun i => (XD (G i) : ℝ)) =o[l]
      (fun i => (((LiteralK4.engineImpl (RC i)).P
        + (LiteralK4.engineImpl (RC i)).Sminus : ℕ) : ℝ)) := by
    have e : (fun i => (((LiteralK4.engineImpl (RC i)).P
          + (LiteralK4.engineImpl (RC i)).Sminus : ℕ) : ℝ))
        = (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ)) := by
      funext i
      rw [LiteralK4.engineImpl_Sminus]
      rfl
    rw [e]
    exact hR
  have h1 := (representation_cost_P (l := l) G m0 c0 hq
    (fun i => LiteralK4.engineImpl (RC i))).2.2.2 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast LiteralK4.engineImpl_W_le (RC i)

end FinalP

/-! ## 13. `K ≤ N` when root actions are distinct gates

`LiteralK3.SelRun` does not constrain `rt` (no injectivity, no `rt i < N`), so `K` is not
bounded by `XD` from its fields.  If the root actions are distinct gates of the initial
circuit, `K ≤ N` and the `+K` term is absorbed. -/

section KleN

theorem K_le_N {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) : R.K ≤ R.G0.N := by
  have := Finset.card_le_card_of_injOn R.rt (s := range R.K) (t := range R.G0.N)
    (by intro i hi; simp only [coe_range, Set.mem_Iio] at hi ⊢; exact hlt i hi)
    (by intro i hi j hj h; simp only [coe_range, Set.mem_Iio] at hi hj; exact hinj i hi j hj h)
  simpa using this

/-- **`WP ≤ 25 · XD` without a query hypothesis**, when the root actions are distinct gates
`< N`. -/
theorem WP_le_inj {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α) (m0 : ℕ → Bool)
    (c0 : ℕ → ℕ) (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    WP R m0 c0 ≤ 25 * XD R := by
  have h1 := WP_le R m0 c0
  have h2 := K_le_N R hlt hinj
  have h3 : R.G0.N ≤ XD R := by unfold XD Hsh; omega
  omega

/-- **`prop:representation-cost` as one theorem** for the engine with the protection
index, when in every run the root actions are distinct gates `< N` (`𝒜 ⊆ V`). -/
theorem representation_cost_Pinj {α β Cell ι : Type*} [LinearOrder α] [OrderBot α]
    [DecidableEq β] [DecidableEq Cell] {l : Filter ι}
    (G : ι → SelRun α) (m0 : ι → ℕ → Bool) (c0 : ι → ℕ → ℕ)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j)
    (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WP (G i) (m0 i) (c0 i) ≤ 25 * XD (G i)) ∧
    (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  have hW : ∀ i, WP (G i) (m0 i) (c0 i) ≤ 25 * XD (G i) :=
    fun i => WP_le_inj (G i) (m0 i) (c0 i) (hlt i) (hinj i)
  have hG : (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) := by
    apply IsBigO.of_bound 25
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hW i
  exact ⟨hW, hG, fun i => (C i).lower, fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)** for the engine with the protection index, root actions being
distinct gates `< N` in every run. -/
theorem condition_R_engine_Pinj {α β ι : Type*} [LinearOrder α] [OrderBot α] [LinearOrder β]
    [OrderBot β] {l : Filter ι} (G : ι → SelRun α) (m0 : ι → ℕ → Bool) (c0 : ι → ℕ → ℕ)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j)
    (RC : ι → EngineRun β)
    (hR : (fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WP (G i) (m0 i) (c0 i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
  have hR' : (fun i => (XD (G i) : ℝ)) =o[l]
      (fun i => (((LiteralK4.engineImpl (RC i)).P
        + (LiteralK4.engineImpl (RC i)).Sminus : ℕ) : ℝ)) := by
    have e : (fun i => (((LiteralK4.engineImpl (RC i)).P
          + (LiteralK4.engineImpl (RC i)).Sminus : ℕ) : ℝ))
        = (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ)) := by
      funext i
      rw [LiteralK4.engineImpl_Sminus]
      rfl
    rw [e]
    exact hR
  have h1 := (representation_cost_Pinj (l := l) G m0 c0 hlt hinj
    (fun i => LiteralK4.engineImpl (RC i))).2.2.2 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast LiteralK4.engineImpl_W_le (RC i)

end KleN

end LiteralG2
end JointRootCert
