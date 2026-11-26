/-
Joint Root Certification: `prop:representation-cost` (Unified Full-Cost Representation
Comparison), upper bound `eq:prop-rep-upper`, for an engine that builds its retirement
candidate list from the gates recorded by its own waves.

Manuscript result covered: `prop:representation-cost` (all three sentences), restated from
`LiteralK11` for a different executed program.

## The gap closed

In `LiteralK10`/`LiteralK11` the executed engine `LiteralE7a.runSD` obtains its retirement
candidates from `EngineFinal.delivV`, a filter over all `N` gates; `LiteralK11.WDc` charges
only `|chgList| + |candList|` for it.  Here the executed program is changed instead:

* `waveDR` (= `waveD` plus a record list): the stack loop `loopDR` appends each popped gate
  to an output list, one unit per record (`waveDR_eq`: same state as `waveD`, cost
  `waveD` cost + length of the record).  `waveDR_rec`: the record is duplicate-free and
  its members are exactly the gates `q < N` whose stored value the wave changed.
* `mergeChg`: the lower record, then the upper-record gates whose stored lower value did
  not change (one comparison each); cost `|rl| + |rh|`.
* `buildCand`: the parent incidences of the merged gates; cost `|merged| + |cand|`.
* `relStepR`: these, then `LiteralE4.tailStep` (retirement tests, heap deletions, release
  cascade) reading the computed list `candR`.  `runSR` / `costSR`: the run with queries,
  as `runSD` / `costSD`.

Every cost in `WR` is computed by these functions; no step is charged by formula.

The merged list is a permutation of the changed-gate list `chgR` (increasing order), not
equal to it, so the candidate list is a permutation of the `delivV` list.  The abstract
semantics is shown to be insensitive to that:

* `retireList_perm`: the retirement pass over a permutation ends in the same state and
  retires the same number of incidences (tests on distinct incidences commute,
  `retireOne_comm`); its charged cost may differ (heap sizes at the time of a deletion), by
  at most `2 ⌈log₂ D⌉` per retired incidence (`retireList_lower` / `retireList_upper`);
* `releaseLoop_perm`: the release cascade over a permutation of a stack that contains every
  orphan ends in the same circuit at the same cost (via `LiteralE4.releaseLoop_exact` and
  the exact cost identity `releaseLoop_cost_eq`);
* `relStep_perm`: hence the abstract rollout with the permuted list has the same result
  state, and charged cost at most `+ 2 ⌈log₂ D⌉ · (retired incidences)`.

So the executed engine represents the same abstract run `RetireFinal.runF` (`simR_all`),
and per rollout `costSR + 4(L+3) ≤ 12 + 6 V + 2 costF + 4 ⌈log₂ D⌉ · retF` (`stepR`), giving
`WR ≤ 18 · XD` (`WR_le`).
-/
import JointRootCert.LiteralK11

namespace JointRootCert
namespace LiteralF4

open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)
open Asymptotics
open scoped List

/-! ## 1. The recording wave -/

section Record

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **The stack loop with recording**: as `LiteralE7a.loopD`, and each popped gate is
appended to the output list (1 unit per record). -/
def loopDR (G : Dag) : ℕ → HEState α → List ℕ → HEState α × ℕ × List ℕ
  | 0, s, _ => (s, 0, [])
  | _ + 1, s, [] => (s, 1, [])
  | f + 1, s, g :: st =>
    ((loopDR G f (dlv g (s.val g) (G.parents g) s st).1
        (dlv g (s.val g) (G.parents g) s st).2.1).1,
     2 + (dlv g (s.val g) (G.parents g) s st).2.2
       + (loopDR G f (dlv g (s.val g) (G.parents g) s st).1
          (dlv g (s.val g) (G.parents g) s st).2.1).2.1,
     g :: (loopDR G f (dlv g (s.val g) (G.parents g) s st).1
          (dlv g (s.val g) (G.parents g) s st).2.1).2.2)

/-- **The wave with recording**: as `LiteralE7a.waveD`; it also returns the list of the
gates popped from its stack (the gates whose stored value it changed). -/
def waveDR (G : Dag) (x : ℕ) (y : α) (s : HEState α) : HEState α × ℕ × List ℕ :=
  if targetH G x y s x = s.val x then (s, 1, [])
  else ((loopDR G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).1,
    1 + (loopDR G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).2.1,
    (loopDR G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).2.2)

lemma loopDR_eq (G : Dag) : ∀ (fuel : ℕ) (s : HEState α) (st : List ℕ),
    (loopDR G fuel s st).1 = (loopD G fuel s st).1 ∧
    (loopDR G fuel s st).2.1 = (loopD G fuel s st).2 + (loopDR G fuel s st).2.2.length := by
  intro fuel
  induction fuel with
  | zero => intro s st; exact ⟨rfl, rfl⟩
  | succ f ih =>
    intro s st
    cases st with
    | nil => exact ⟨rfl, rfl⟩
    | cons g st =>
      obtain ⟨h1, h2⟩ := ih (dlv g (s.val g) (G.parents g) s st).1
        (dlv g (s.val g) (G.parents g) s st).2.1
      refine ⟨by rw [loopDR, loopD]; exact h1, ?_⟩
      rw [loopDR, loopD]
      dsimp only
      rw [h2, List.length_cons]
      omega

/-- `waveDR` executes `waveD` (same state) and charges one more unit per recorded gate. -/
lemma waveDR_eq (G : Dag) (x : ℕ) (y : α) (s : HEState α) :
    (waveDR G x y s).1 = (waveD G x y s).1 ∧
    (waveDR G x y s).2.1 = (waveD G x y s).2 + (waveDR G x y s).2.2.length := by
  unfold waveDR waveD
  by_cases hc : targetH G x y s x = s.val x
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hc, ite_eq_right hc]
    obtain ⟨h1, h2⟩ := loopDR_eq G (G.N + 2)
      ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]
    refine ⟨h1, ?_⟩
    dsimp only
    rw [h2]
    omega

variable {G : Dag} {o f : ℕ → α}

/-- **The recorded gates of the loop** are exactly the changed gates that have not
delivered yet (`Rset`), each once. -/
theorem loopDR_rec (hG : G.WF) (hD : Dir o f) (ho : Exact G o) (hf : Exact G f) :
    ∀ (fuel : ℕ) (s : HEState α) (k : ℕ → ℕ → α) (st : List ℕ),
    DI G o f 0 [] s k st → st.length + (Uset G o f s).card < fuel →
    (loopDR G fuel s st).2.2.Nodup ∧
    ∀ q, q ∈ (loopDR G fuel s st).2.2 ↔ q ∈ Rset G o f s st := by
  intro fuel
  induction fuel with
  | zero => intro s k st _ hm; omega
  | succ fuel ih =>
    intro s k st h hm
    cases st with
    | nil =>
      have hkey : ∀ p c, c ∈ G.children p → k p c = s.val c := by
        intro p c hc
        rw [h.key p c hc]
        simp
      have hex : Exact G s.val := fun p hp =>
        (h.gate p hp).trans (heapMax_congr (fun c hc => hkey p c hc))
      have hall : ∀ q, s.val q = f q := exact_unique hG hex hf (fun q hq => h.leaf q hq)
      refine ⟨List.nodup_nil, fun q => ?_⟩
      show q ∈ ([] : List ℕ) ↔ _
      simp only [Rset, mem_filter, mem_range, List.not_mem_nil, or_false, false_iff, not_and]
      intro _ hne hso
      exact hne ((hall q).symm.trans hso)
    | cons g rest =>
      obtain ⟨hg, hgo, hgN⟩ := h.stk g List.mem_cons_self
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
      obtain ⟨k1, d1, _, _, d4, d5, _, _, _⟩ := dlv_spec hG hD ho hf g (s.val g)
        (G.parents g) s k rest hD' rfl hg hgr (fun p hp => (hG.parents_iff g p).1 hp)
        (hG.parents_nodup g)
      have hm' : (dlv g (s.val g) (G.parents g) s rest).2.1.length
          + (Uset G o f (dlv g (s.val g) (G.parents g) s rest).1).card < fuel := by
        rw [d4]
        simp only [List.length_cons] at hm
        omega
      obtain ⟨i1, i2⟩ := ih _ k1 _ d1.reg hm'
      rw [d5] at i2
      have hRins : ∀ q, q ∈ Rset G o f s (g :: rest) ↔ q = g ∨ q ∈ Rset G o f s rest := by
        intro q
        simp only [Rset, mem_filter, mem_range, List.mem_cons]
        by_cases e : q = g
        · subst e
          simp [hgN, hgo]
        · simp [e]
      have hgR : g ∉ Rset G o f s rest := by
        simp only [Rset, mem_filter, mem_range, not_and, not_or]
        intro _ _
        exact ⟨fun e => hgo (hg ▸ e), hgr⟩
      rw [loopDR]
      dsimp only
      refine ⟨List.nodup_cons.2 ⟨fun hm => hgR ((i2 g).1 hm), i1⟩, fun q => ?_⟩
      rw [List.mem_cons, hRins q, i2 q]

/-- **The recorded gates of the wave** are exactly the gates whose stored value the wave
changed, each once. -/
theorem waveDR_rec (hG : G.WF) (x : ℕ) (y : α) (hs : HEState α) (s0 : EState α)
    (hx : x < G.N) (h : SimE G hs s0) (h0 : Inv G s0) :
    (waveDR G x y hs).2.2.Nodup ∧
    ∀ q, q ∈ (waveDR G x y hs).2.2 ↔ q < G.N ∧ (waveD G x y hs).1.val q ≠ hs.val q := by
  obtain ⟨w1, w2, w3, _⟩ := wave_spec hG x y s0 hx h0
  have ho := inv_exact h0
  have hf := inv_exact w1
  have hD := dir_of_wave hG x y s0 hx h0
  have ht := HeapImpl.targetH_eq h x y x
  have hv := h.val
  have hWv : (waveD G x y hs).1.val = (wave G x y s0).1.val :=
    (waveD_spec hG x y hs s0 hx h h0).1.val
  by_cases hc : targetH G x y hs x = hs.val x
  · unfold waveDR
    rw [ite_eq_left hc]
    refine ⟨List.nodup_nil, fun q => ?_⟩
    unfold waveD
    rw [ite_eq_left hc]
    simp
  · have hxl : G.children x = [] := by
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
    obtain ⟨r1, r2⟩ := loopDR_rec hG hD ho hf (G.N + 2) s1 s0.key [x] hDI
      (by simp only [List.length_singleton]; omega)
    have hR : ∀ q, q ∈ Rset G s0.val (wave G x y s0).1.val s1 [x]
        ↔ q < G.N ∧ (wave G x y s0).1.val q ≠ s0.val q := by
      intro q
      simp only [Rset, mem_filter, mem_range, List.mem_singleton]
      by_cases e : q = x
      · subst e
        simp [hfo]
      · simp [e, hs1o q e]
    unfold waveDR
    rw [ite_eq_right hc, ← hs1]
    refine ⟨r1, fun q => ?_⟩
    rw [r2 q, hR q, hWv, hv]

end Record

/-! ## 2. The retirement pass does not depend on the order of its candidates -/

section RetirePerm

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma dag_ext {G1 G2 : Dag} (h1 : G1.N = G2.N) (h2 : G1.children = G2.children)
    (h3 : G1.parents = G2.parents) (h4 : G1.level = G2.level) (h5 : G1.L = G2.L) :
    G1 = G2 := by
  cases G1
  cases G2
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

lemma retireDag_comm (G : Dag) (a b c d : ℕ) :
    retireDag (retireDag G a b) c d = retireDag (retireDag G c d) a b := by
  refine dag_ext rfl ?_ ?_ rfl rfl
  · funext g
    show (if g = c then (if g = a then (G.children g).filter (· ≠ b) else G.children g).filter
        (· ≠ d) else (if g = a then (G.children g).filter (· ≠ b) else G.children g))
      = (if g = a then (if g = c then (G.children g).filter (· ≠ d) else G.children g).filter
        (· ≠ b) else (if g = c then (G.children g).filter (· ≠ d) else G.children g))
    split_ifs <;> first
      | rfl
      | rw [List.filter_filter, List.filter_filter]; congr 1; funext x; exact Bool.and_comm _ _
  · funext g
    show (if g = d then (if g = b then (G.parents g).filter (· ≠ a) else G.parents g).filter
        (· ≠ c) else (if g = b then (G.parents g).filter (· ≠ a) else G.parents g))
      = (if g = b then (if g = d then (G.parents g).filter (· ≠ c) else G.parents g).filter
        (· ≠ a) else (if g = d then (G.parents g).filter (· ≠ c) else G.parents g))
    split_ifs <;> first
      | rfl
      | rw [List.filter_filter, List.filter_filter]; congr 1; funext x; exact Bool.and_comm _ _

omit [OrderBot α] in
/-- The retirement test of `x` is not affected by the retirement of another incidence. -/
lemma fires_retireOne {x y : ℕ × ℕ} (hxy : x ≠ y) (s : RState α) :
    (x.2 ∈ (retireOne y s).1.G.children x.1 ∧ (retireOne y s).1.hi.val x.2
        < (retireOne y s).1.lo.val x.1) ↔
      (x.2 ∈ s.G.children x.1 ∧ s.hi.val x.2 < s.lo.val x.1) := by
  unfold retireOne
  by_cases hc : y.2 ∈ s.G.children y.1 ∧ s.hi.val y.2 < s.lo.val y.1
  · rw [ite_eq_left hc]
    show (x.2 ∈ (retireDag s.G y.1 y.2).children x.1 ∧ _) ↔ _
    rw [mem_retire_children]
    have : ¬ (x.1 = y.1 ∧ x.2 = y.2) := fun h => hxy (Prod.ext h.1 h.2)
    simp [this]
  · rw [ite_eq_right hc]

omit [OrderBot α] in
lemma retireOne_comm {x y : ℕ × ℕ} (hxy : x ≠ y) (s : RState α) :
    (retireOne x (retireOne y s).1).1 = (retireOne y (retireOne x s).1).1 := by
  have fx := fires_retireOne hxy s
  have fy := fires_retireOne (Ne.symm hxy) s
  by_cases hx : x.2 ∈ s.G.children x.1 ∧ s.hi.val x.2 < s.lo.val x.1 <;>
  by_cases hy : y.2 ∈ s.G.children y.1 ∧ s.hi.val y.2 < s.lo.val y.1
  · have hx' := fx.2 hx
    have hy' := fy.2 hy
    unfold retireOne at hx' hy' ⊢
    rw [ite_eq_left hy, ite_eq_left hx] at *
    rw [ite_eq_left hx', ite_eq_left hy']
    show (⟨retireDag (retireDag s.G y.1 y.2) x.1 x.2, s.lo, s.hi⟩ : RState α)
      = ⟨retireDag (retireDag s.G x.1 x.2) y.1 y.2, s.lo, s.hi⟩
    rw [retireDag_comm]
  · have hy' : ¬ _ := fun h => hy (fy.1 h)
    unfold retireOne at hy' ⊢
    rw [ite_eq_right hy, ite_eq_left hx] at *
    rw [ite_eq_right hy']
  · have hx' : ¬ _ := fun h => hx (fx.1 h)
    unfold retireOne at hx' ⊢
    rw [ite_eq_right hx, ite_eq_left hy] at *
    rw [ite_eq_right hx']
  · simp [retireOne, hx, hy]

/-- Number of incidences actually retired by the pass. -/
def nev : List (ℕ × ℕ) → RState α → ℕ
  | [], _ => 0
  | e :: es, s =>
    (if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then 1 else 0)
      + nev es (retireOne e s).1

omit [OrderBot α] in
/-- **The retirement pass over a permutation of the candidates** ends in the same state and
retires the same number of incidences. -/
theorem retireList_perm {L L' : List (ℕ × ℕ)} (hp : L ~ L') : ∀ s : RState α,
    (retireList L s).1 = (retireList L' s).1 ∧ nev L s = nev L' s := by
  induction hp with
  | nil => intro s; exact ⟨rfl, rfl⟩
  | cons x _ ih =>
    intro s
    obtain ⟨h1, h2⟩ := ih (retireOne x s).1
    refine ⟨?_, ?_⟩
    · exact h1
    · show _ + nev _ (retireOne x s).1 = _ + nev _ (retireOne x s).1
      rw [h2]
  | swap x y l =>
    intro s
    by_cases hxy : x = y
    · subst hxy; exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · show (retireList l (retireOne x (retireOne y s).1).1).1
        = (retireList l (retireOne y (retireOne x s).1).1).1
      rw [retireOne_comm hxy]
    · show (if y.2 ∈ s.G.children y.1 ∧ s.hi.val y.2 < s.lo.val y.1 then 1 else 0)
          + ((if x.2 ∈ (retireOne y s).1.G.children x.1 ∧ (retireOne y s).1.hi.val x.2
                < (retireOne y s).1.lo.val x.1 then 1 else 0)
            + nev l (retireOne x (retireOne y s).1).1)
        = (if x.2 ∈ s.G.children x.1 ∧ s.hi.val x.2 < s.lo.val x.1 then 1 else 0)
          + ((if y.2 ∈ (retireOne x s).1.G.children y.1 ∧ (retireOne x s).1.hi.val y.2
                < (retireOne x s).1.lo.val y.1 then 1 else 0)
            + nev l (retireOne y (retireOne x s).1).1)
      rw [if_congr (fires_retireOne hxy s) rfl rfl,
        if_congr (fires_retireOne (Ne.symm hxy) s) rfl rfl, retireOne_comm hxy]
      omega
  | trans _ _ ih1 ih2 =>
    intro s
    exact ⟨(ih1 s).1.trans (ih2 s).1, (ih1 s).2.trans (ih2 s).2⟩

omit [OrderBot α] in
/-- Every test costs at least one unit, every retirement at least five. -/
lemma retireList_lower : ∀ (L : List (ℕ × ℕ)) (s : RState α),
    L.length + 4 * nev L s ≤ (retireList L s).2 := by
  intro L
  induction L with
  | nil => intro s; simp [retireList, nev]
  | cons e es ih =>
    intro s
    have h := ih (retireOne e s).1
    show es.length + 1 + 4 * (_ + nev es (retireOne e s).1)
      ≤ (retireOne e s).2 + (retireList es (retireOne e s).1).2
    unfold retireOne
    by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
    · rw [ite_eq_left hc, ite_eq_left hc]
      unfold retireOne at h
      rw [ite_eq_left hc] at h
      dsimp only at h ⊢
      omega
    · rw [ite_eq_right hc, ite_eq_right hc]
      unfold retireOne at h
      rw [ite_eq_right hc] at h
      dsimp only at h ⊢
      omega

omit [OrderBot α] in
/-- Every test costs at most one unit plus, if it retires, `2 ⌈log₂ D⌉ + 4`. -/
lemma retireList_upper (D : ℕ) : ∀ (L : List (ℕ × ℕ)) (s : RState α), s.G.WF →
    (∀ p, (s.G.children p).length ≤ D) →
    (retireList L s).2 ≤ L.length + (2 * Nat.clog 2 D + 4) * nev L s := by
  intro L
  induction L with
  | nil => intro s _ _; simp [retireList, nev]
  | cons e es ih =>
    intro s hG hD
    obtain ⟨w, _, sub⟩ := retireOne_G e s hG
    have h := ih (retireOne e s).1 w (fun p => ((sub p).length_le).trans (hD p))
    show (retireOne e s).2 + (retireList es (retireOne e s).1).2
      ≤ es.length + 1 + (2 * Nat.clog 2 D + 4) * (_ + nev es (retireOne e s).1)
    rw [mul_add]
    have hc1 : (retireOne e s).2
        ≤ 1 + (2 * Nat.clog 2 D + 4)
          * (if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then 1 else 0) := by
      unfold retireOne
      by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
      · rw [ite_eq_left hc, ite_eq_left hc]
        have := Nat.clog_mono_right 2 (hD e.1)
        show 2 * Nat.clog 2 (s.G.children e.1).length + 5 ≤ _
        omega
      · rw [ite_eq_right hc, ite_eq_right hc]
        show 1 ≤ _
        omega
    omega

omit [OrderBot α] in
/-- Every retirement removes at least one live incidence. -/
lemma nev_le_live : ∀ (L : List (ℕ × ℕ)) (s : RState α), s.G.WF →
    nev L s + live (retireList L s).1.G ≤ live s.G := by
  intro L
  induction L with
  | nil => intro s _; simp [retireList, nev]
  | cons e es ih =>
    intro s hG
    obtain ⟨w, _, _⟩ := retireOne_G e s hG
    have h := ih (retireOne e s).1 w
    show (_ + nev es (retireOne e s).1) + live (retireList es (retireOne e s).1).1.G ≤ _
    have hc1 : (if e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1 then 1 else 0)
        + live (retireOne e s).1.G ≤ live s.G := by
      unfold retireOne
      by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
      · rw [ite_eq_left hc, ite_eq_left hc]
        have := live_retire hG hc.1
        show 1 + live (retireDag s.G e.1 e.2) ≤ _
        omega
      · rw [ite_eq_right hc, ite_eq_right hc]
        show 0 + live s.G ≤ live s.G
        omega
    omega

end RetirePerm

/-! ## 3. The release cascade does not depend on the order of its stack -/

section ReleasePerm

open LiteralE4 (Orphan Anch releaseLoop_exact relFuel_enough)

/-- With enough fuel the cascade empties its stack: its cost is the stack length plus twice
the live incidences it removes. -/
theorem releaseLoop_cost_eq (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (G : Dag), G.WF →
    2 * cells G + st.length < f →
    (releaseLoop prot f st G).2 + 2 * live (releaseLoop prot f st G).1 = st.length + 2 * live G := by
  intro f
  induction f with
  | zero => intro st G _ hf; omega
  | succ f ih =>
    intro st G hG hf
    cases st with
    | nil => show 0 + 2 * live G = 0 + 2 * live G; rfl
    | cons g st =>
      rw [List.length_cons] at hf
      rw [releaseLoop]
      by_cases hc : G.children g ≠ [] ∧ G.parents g = [] ∧ prot g = false
      · rw [ite_eq_left hc]
        obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc.1
        have hgN : g < G.N := hG.parent_lt c g ((hG.parents_iff c g).2 hcm)
        have hcell := cells_release hgN hc.1
        have hl := LiteralK3.live_release (G := G) hgN
        have h := ih (G.children g ++ st) (releaseDag G g) (releaseDag_wf hG g)
          (by rw [List.length_append]; omega)
        rw [List.length_append] at h
        dsimp only
        rw [List.length_cons]
        omega
      · rw [ite_eq_right hc]
        have h := ih st G hG (by omega)
        dsimp only
        rw [List.length_cons]
        omega

lemma sublist_eq_filter {l L : List ℕ} (h : l <+ L) (hL : L.Nodup) :
    l = L.filter (fun x => decide (x ∈ l)) := by
  induction h with
  | slnil => rfl
  | @cons l₁ l₂ a h ih =>
    have ha : a ∉ l₁ := fun hm => (List.nodup_cons.1 hL).1 (h.subset hm)
    rw [List.filter_cons_of_neg (by simpa using ha)]
    exact ih (List.nodup_cons.1 hL).2
  | @cons_cons l₁ l₂ a h ih =>
    have ha : a ∉ l₂ := (List.nodup_cons.1 hL).1
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    conv_lhs => rw [ih (List.nodup_cons.1 hL).2]
    apply List.filter_congr
    intro x hx
    have : x ≠ a := fun e => ha (e ▸ hx)
    simp [this]

lemma sublist_ext {l1 l2 L : List ℕ} (h1 : l1 <+ L) (h2 : l2 <+ L) (hL : L.Nodup)
    (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 := by
  rw [sublist_eq_filter h1 hL, sublist_eq_filter h2 hL]
  apply List.filter_congr
  intro x _
  simp [h x]

/-- **The release cascade over a permutation of its stack** ends in the same circuit at
the same cost, provided the stack contains every orphan (as it does in the engine). -/
theorem releaseLoop_perm (prot : ℕ → Bool) (G : Dag) (hG : G.WF) {st st' : List ℕ}
    (hp : st ~ st') (hst : ∀ g, Orphan prot G g → g ∈ st) :
    releaseLoop prot (relFuel G st') st' G = releaseLoop prot (relFuel G st) st G := by
  have hst' : ∀ g, Orphan prot G g → g ∈ st' := fun g ho => hp.mem_iff.1 (hst g ho)
  obtain ⟨a1, a2, _⟩ := releaseLoop_exact prot _ st G hG (relFuel_enough _ _) hst
  obtain ⟨b1, b2, _⟩ := releaseLoop_exact prot _ st' G hG (relFuel_enough _ _) hst'
  obtain ⟨c1, c2, c3, c4, _, c6, _⟩ := releaseLoop_spec prot (relFuel G st) st G hG
  obtain ⟨d1, d2, d3, d4, _, d6, _⟩ := releaseLoop_spec prot (relFuel G st') st' G hG
  have hch : (releaseLoop prot (relFuel G st') st' G).1.children
      = (releaseLoop prot (relFuel G st) st G).1.children := by
    funext g
    by_cases ha : Anch prot G g
    · rw [a1 g ha, b1 g ha]
    · rw [a2 g ha, b2 g ha]
  have hD : (releaseLoop prot (relFuel G st') st' G).1 = (releaseLoop prot (relFuel G st) st G).1 := by
    refine dag_ext (d2.trans c2.symm) hch ?_ (d3.trans c3.symm) (d4.trans c4.symm)
    funext c
    refine sublist_ext (d6 c) (c6 c) (hG.parents_nodup c) (fun p => ?_)
    rw [d1.parents_iff, c1.parents_iff, hch]
  have e1 := releaseLoop_cost_eq prot (relFuel G st) st G hG (relFuel_enough _ _)
  have e2 := releaseLoop_cost_eq prot (relFuel G st') st' G hG (relFuel_enough _ _)
  rw [hD, ← hp.length_eq] at e2
  refine Prod.ext hD ?_
  omega

end ReleasePerm

/-! ## 4. One rollout with permuted candidates -/

section StepPerm

variable {α : Type*} [LinearOrder α] [OrderBot α]

open LiteralE4 (Orphan)

/-- **A rollout of the abstract engine with a permuted candidate list** ends in the same
state; its charged cost exceeds the original one by at most `2 ⌈log₂ D⌉` per retired
incidence. -/
theorem relStep_perm (K : ℕ) (rt : ℕ → ℕ) (cand cand' : RState α → RState α → List (ℕ × ℕ))
    (u : ℕ × α × α) (s : QS α) (hwf : s.r.G.WF) (hroot : Rooted (protOf K rt s.act) s.r.G [])
    (D : ℕ) (hD : ∀ p, (s.r.G.children p).length ≤ D)
    (hp : cand' s.r (waveStep u s.r).1 ~ cand s.r (waveStep u s.r).1) :
    (relStep K rt cand' u s).1 = (relStep K rt cand u s).1 ∧
    (relStep K rt cand' u s).2 ≤ (relStep K rt cand u s).2
      + 2 * Nat.clog 2 D * (live s.r.G - live (rstep cand u s.r).1.G) := by
  have hwfw : (waveStep u s.r).1.G.WF := hwf
  obtain ⟨hr, hn⟩ := retireList_perm hp (waveStep u s.r).1
  have hrs : (rstep cand' u s.r).1 = (rstep cand u s.r).1 := hr
  obtain ⟨g1, _, _⟩ := retireList_G (cand s.r (waveStep u s.r).1) (waveStep u s.r).1 hwfw
  have hroot1 := rooted_retireList (prot := protOf K rt s.act) (cand s.r (waveStep u s.r).1)
    (waveStep u s.r).1 [] hroot
  rw [List.append_nil] at hroot1
  have horph : ∀ g, Orphan (protOf K rt s.act) (rstep cand u s.r).1.G g →
      g ∈ (cand s.r (waveStep u s.r).1).map Prod.snd := by
    intro g ho
    obtain ⟨o1, o2, o3⟩ := ho
    rcases hroot1 g o1 with h | h | h
    · exact absurd o2 h
    · rw [o3] at h; exact absurd h Bool.false_ne_true
    · exact h
  have hrel := releaseLoop_perm (protOf K rt s.act) (rstep cand u s.r).1.G g1
    (hp.map Prod.snd).symm horph
  have hcost : (retireList (cand' s.r (waveStep u s.r).1) (waveStep u s.r).1).2
      ≤ (retireList (cand s.r (waveStep u s.r).1) (waveStep u s.r).1).2
        + 2 * Nat.clog 2 D * (live s.r.G - live (rstep cand u s.r).1.G) := by
    have u1 := retireList_upper D (cand' s.r (waveStep u s.r).1) (waveStep u s.r).1 hwfw hD
    have l1 := retireList_lower (cand s.r (waveStep u s.r).1) (waveStep u s.r).1
    have n1 := nev_le_live (cand s.r (waveStep u s.r).1) (waveStep u s.r).1 hwfw
    have hlen := hp.length_eq
    rw [← hn] at l1 n1
    have n2 : nev (cand' s.r (waveStep u s.r).1) (waveStep u s.r).1
        ≤ live s.r.G - live (rstep cand u s.r).1.G := by
      show _ ≤ live s.r.G - live (retireList (cand s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G
      have : live (waveStep u s.r).1.G = live s.r.G := rfl
      omega
    have m := Nat.mul_le_mul_left (2 * Nat.clog 2 D) n2
    have e : (2 * Nat.clog 2 D + 4) * nev (cand' s.r (waveStep u s.r).1) (waveStep u s.r).1
        = 2 * Nat.clog 2 D * nev (cand' s.r (waveStep u s.r).1) (waveStep u s.r).1
          + 4 * nev (cand' s.r (waveStep u s.r).1) (waveStep u s.r).1 := by ring
    omega
  refine ⟨?_, ?_⟩
  · unfold relStep
    rw [hrs, ← hrel]
  · unfold relStep
    rw [hrs, ← hrel]
    show (waveStep u s.r).2 + (retireList (cand' s.r (waveStep u s.r).1) (waveStep u s.r).1).2 + _
      ≤ (waveStep u s.r).2 + (retireList (cand s.r (waveStep u s.r).1) (waveStep u s.r).1).2 + _ + _
    omega

end StepPerm

/-! ## 5. The engine whose candidate list is built from the recorded gates -/

section EngineR

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **Merging the two recorded lists.**  The gates recorded by the lower wave, followed by
the gates recorded by the upper wave whose lower value did not change (one comparison of
the stored lower value with the pre-wave one each).  Cost: one unit per element of each
recorded list. -/
def mergeChg (lo1 lo0 : ℕ → α) (rl rh : List ℕ) : List ℕ × ℕ :=
  (rl ++ rh.filter (fun g => decide (lo1 g = lo0 g)), rl.length + rh.length)

/-- **Building the candidate list** from a list of gates: for each gate `g` its parent
incidences `(p, g)`.  Cost: one unit per gate and one per emitted incidence. -/
def buildCand (G : Dag) (m : List ℕ) : List (ℕ × ℕ) × ℕ :=
  (m.flatMap (fun g => (G.parents g).map (fun p => (p, g))),
   m.length + (m.flatMap (fun g => (G.parents g).map (fun p => (p, g)))).length)

/-- The recording lower wave of the rollout. -/
def recLo (u : ℕ × α × α) (s : HRState α) : HEState α × ℕ × List ℕ := waveDR s.G u.1 u.2.1 s.lo

/-- The recording upper wave of the rollout. -/
def recHi (u : ℕ × α × α) (s : HRState α) : HEState α × ℕ × List ℕ := waveDR s.G u.1 u.2.2 s.hi

/-- Implemented state after the two recording waves. -/
def wR (u : ℕ × α × α) (s : HRState α) : HRState α := ⟨s.G, (recLo u s).1, (recHi u s).1⟩

/-- The merged list of changed gates. -/
def mergedR (u : ℕ × α × α) (s : HRState α) : List ℕ :=
  (mergeChg (recLo u s).1.val s.lo.val (recLo u s).2.2 (recHi u s).2.2).1

/-- The candidate list read by the retirement pass and the release cascade. -/
def candR (u : ℕ × α × α) (s : HRState α) : List (ℕ × ℕ) := (buildCand s.G (mergedR u s)).1

/-- Computed cost of the two recording waves, the merge and the candidate construction. -/
def prepR (u : ℕ × α × α) (s : HRState α) : ℕ :=
  (recLo u s).2.1 + (recHi u s).2.1
    + (mergeChg (recLo u s).1.val s.lo.val (recLo u s).2.2 (recHi u s).2.2).2
    + (buildCand s.G (mergedR u s)).2

/-- **One rollout of the executed engine**: the two recording waves, the merge, the
candidate construction, then the retirement pass and the release cascade of
`LiteralE4.tailStep` reading the list `candR`. -/
def relStepR (K : ℕ) (rt : ℕ → ℕ) (u : ℕ × α × α) (s : HQS α) : HQS α × ℕ :=
  ((LiteralE4.tailStep K rt (fun _ _ _ _ _ => candR u s.r) s (wR u s.r)).1,
   prepR u s.r + (LiteralE4.tailStep K rt (fun _ _ _ _ _ => candR u s.r) s (wR u s.r)).2)

/-- State of the executed engine after `t` rollouts (queries with root retirement as in
`LiteralE7a.runSD`). -/
def runSR (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : HQS α) : ℕ → HQS α
  | 0 => s0
  | t + 1 => (relStepR K rt (u (t + 1))
      (if q t = true then (qRetireH K rt (runSR K rt u q s0 t)).1 else runSR K rt u q s0 t)).1

/-- Computed cost of the query of time `t` (if any) and of rollout `t + 1`. -/
def costSR (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : HQS α) (t : ℕ) : ℕ :=
  (if q t = true then K + (qRetireH K rt (runSR K rt u q s0 t)).2 else 0)
    + (relStepR K rt (u (t + 1))
        (if q t = true then (qRetireH K rt (runSR K rt u q s0 t)).1
          else runSR K rt u q s0 t)).2

lemma length_eq_card {l : List ℕ} (hn : l.Nodup) (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ q, q ∈ l ↔ q < N ∧ P q) : l.length = ((range N).filter P).card := by
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext q
  simp [h q]

variable {K : ℕ} {rt : ℕ → ℕ}

/-- **One rollout of the executed engine.**  From an implemented state representing a state
`s` that satisfies the coupled invariant and the reference-count invariant, with child lists
of length at most `D`:

1. each wave records each gate whose stored value it changed, exactly once;
2. the merged list is duplicate-free and a permutation of the list `chg` of changed gates
   (`List.range N` filtered by "a stored endpoint changed");
3. the candidate list is a permutation of the list `delivV` of `LiteralK11` (the parent
   incidences of `chg`, in the order of `chg`);
4. the waves end in the state of `waveStepD`;
5. the rollout represents the abstract rollout `RetireFinal.relStep` with the policy
   `delivCand`;
6. its computed cost (waves with recording, merge, candidate construction, tests, heap
   deletions, release) satisfies
   `cost + 4(L+3) ≤ 12 + 6 V + 2 · (charged cost of relStep) + 4 ⌈log₂ D⌉ · (retired)`,
   with `V` the live deliveries and `retired` the incidences removed by the pass;
7. it is at least `V`;
8. the cost of recording, merging and building is `2(|rl| + |rh|) + |merged| + |cand|`
   on top of the `waveD` costs, and that extra is at most `6 + 4 V`. -/
theorem relStepR_spec {hs : HQS α} {s : QS α} (h : SimQ hs s) {G0 : Dag} {elo ehi : ℕ → α}
    (hinv : CInv G0 K rt s.r s.act elo ehi) (hroot : Rooted (protOf K rt s.act) s.r.G [])
    (D : ℕ) (hD : ∀ p, (s.r.G.children p).length ≤ D) (u : ℕ × α × α) (hx : u.1 < G0.N) :
    ((recLo u hs.r).2.2.Nodup ∧
      ∀ q, q ∈ (recLo u hs.r).2.2 ↔ q < hs.r.G.N ∧ (wR u hs.r).lo.val q ≠ hs.r.lo.val q) ∧
    ((recHi u hs.r).2.2.Nodup ∧
      ∀ q, q ∈ (recHi u hs.r).2.2 ↔ q < hs.r.G.N ∧ (wR u hs.r).hi.val q ≠ hs.r.hi.val q) ∧
    (mergedR u hs.r).Nodup ∧
    (mergedR u hs.r).Perm ((List.range hs.r.G.N).filter (fun g =>
      (wR u hs.r).lo.val g ≠ hs.r.lo.val g ∨ (wR u hs.r).hi.val g ≠ hs.r.hi.val g)) ∧
    (candR u hs.r).Perm
      (delivV hs.r.G hs.r.lo.val hs.r.hi.val (wR u hs.r).lo.val (wR u hs.r).hi.val) ∧
    wR u hs.r = (waveStepD u hs.r).1 ∧
    SimQ (relStepR K rt u hs).1 (relStep K rt delivCand u s).1 ∧
    (relStepR K rt u hs).2 + 4 * (G0.L + 3)
      ≤ 12 + 6 * (vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1
            + vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1)
        + 2 * (relStep K rt delivCand u s).2
        + 4 * Nat.clog 2 D * (live s.r.G - live (rstep delivCand u s.r).1.G) ∧
    vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1
        + vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1 ≤ (relStepR K rt u hs).2 ∧
    prepR u hs.r = (waveStepD u hs.r).2
      + 2 * ((recLo u hs.r).2.2.length + (recHi u hs.r).2.2.length)
      + (mergedR u hs.r).length + (candR u hs.r).length ∧
    2 * ((recLo u hs.r).2.2.length + (recHi u hs.r).2.2.length)
        + (mergedR u hs.r).length + (candR u hs.r).length
      ≤ 6 + 4 * (vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1
            + vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1) := by
  obtain ⟨⟨G', hlo, hhi⟩, hact⟩ := hs
  obtain ⟨⟨hG', slo, shi⟩, hact'⟩ := h
  simp only at hG' slo shi hact'
  subst hG'
  have hxs : u.1 < s.r.G.N := by rw [hinv.nEq]; exact hx
  -- the waves
  obtain ⟨l1, l2, l3⟩ := waveD_spec hinv.wf u.1 u.2.1 hlo s.r.lo hxs slo hinv.invLo
  obtain ⟨u1, u2, u3⟩ := waveD_spec hinv.wf u.1 u.2.2 hhi s.r.hi hxs shi hinv.invHi
  obtain ⟨wl1, -, wl3, lw⟩ := wave_spec hinv.wf u.1 u.2.1 s.r.lo hxs hinv.invLo
  obtain ⟨wu1, -, wu3, uw⟩ := wave_spec hinv.wf u.1 u.2.2 s.r.hi hxs hinv.invHi
  rw [hinv.lEq] at lw uw
  obtain ⟨el1, el2⟩ := waveDR_eq s.r.G u.1 u.2.1 hlo
  obtain ⟨eu1, eu2⟩ := waveDR_eq s.r.G u.1 u.2.2 hhi
  obtain ⟨rl1, rl2⟩ := waveDR_rec hinv.wf u.1 u.2.1 hlo s.r.lo hxs slo hinv.invLo
  obtain ⟨ru1, ru2⟩ := waveDR_rec hinv.wf u.1 u.2.2 hhi s.r.hi hxs shi hinv.invHi
  set hr : HRState α := ⟨s.r.G, hlo, hhi⟩ with hhr
  set wlo := (wave s.r.G u.1 u.2.1 s.r.lo).1 with hwlo
  set whi := (wave s.r.G u.1 u.2.2 s.r.hi).1 with hwhi
  set rl := (recLo u hr).2.2 with hrl
  set rh := (recHi u hr).2.2 with hrh
  have eWl : (wR u hr).lo = (waveD s.r.G u.1 u.2.1 hlo).1 := el1
  have eWh : (wR u hr).hi = (waveD s.r.G u.1 u.2.2 hhi).1 := eu1
  have vWl : (wR u hr).lo.val = wlo.val := by rw [eWl]; exact l1.val
  have vWh : (wR u hr).hi.val = whi.val := by rw [eWh]; exact u1.val
  have eW : wR u hr = (waveStepD u hr).1 := by
    show (⟨s.r.G, (waveDR s.r.G u.1 u.2.1 hlo).1, (waveDR s.r.G u.1 u.2.2 hhi).1⟩ : HRState α)
      = ⟨s.r.G, (waveD s.r.G u.1 u.2.1 hlo).1, (waveD s.r.G u.1 u.2.2 hhi).1⟩
    rw [el1, eu1]
  -- recorded lists, in abstract terms
  have mRl : ∀ q, q ∈ rl ↔ q < s.r.G.N ∧ wlo.val q ≠ s.r.lo.val q := by
    intro q
    rw [hrl]
    show q ∈ (waveDR s.r.G u.1 u.2.1 hlo).2.2 ↔ _
    rw [rl2 q, l1.val, slo.val]
  have mRh : ∀ q, q ∈ rh ↔ q < s.r.G.N ∧ whi.val q ≠ s.r.hi.val q := by
    intro q
    rw [hrh]
    show q ∈ (waveDR s.r.G u.1 u.2.2 hhi).2.2 ↔ _
    rw [ru2 q, u1.val, shi.val]
  have nRl : rl.Nodup := rl1
  have nRh : rh.Nodup := ru1
  -- the merged list
  have eM : mergedR u hr = rl ++ rh.filter (fun g => decide (wlo.val g = s.r.lo.val g)) := by
    show rl ++ rh.filter (fun g => decide ((waveDR s.r.G u.1 u.2.1 hlo).1.val g = hlo.val g)) = _
    rw [el1, l1.val, slo.val]
  have nM : (mergedR u hr).Nodup := by
    rw [eM]
    refine List.Nodup.append nRl (nRh.filter _) ?_
    intro a ha hb
    rw [List.mem_filter, decide_eq_true_eq] at hb
    exact ((mRl a).1 ha).2 hb.2
  set chg := (List.range s.r.G.N).filter (fun g => wlo.val g ≠ s.r.lo.val g ∨ whi.val g ≠ s.r.hi.val g)
    with hchg
  have nC : chg.Nodup := List.nodup_range.filter _
  have pM : (mergedR u hr).Perm chg := by
    rw [List.perm_ext_iff_of_nodup nM nC]
    intro a
    rw [eM, hchg, List.mem_append, List.mem_filter, List.mem_filter, decide_eq_true_eq,
      List.mem_range, mRl a, mRh a]
    simp only [decide_eq_true_eq]
    by_cases e : wlo.val a = s.r.lo.val a <;> simp [e]
  have pC : (candR u hr).Perm (delivCand s.r (waveStep u s.r).1) :=
    pM.flatMap_right (fun g => (s.r.G.parents g).map (fun p => (p, g)))
  have eD : delivV hr.G hr.lo.val hr.hi.val (wR u hr).lo.val (wR u hr).hi.val
      = delivCand s.r (waveStep u s.r).1 := by
    show delivV s.r.G hlo.val hhi.val (wR u hr).lo.val (wR u hr).hi.val = _
    rw [vWl, vWh, slo.val, shi.val]
    rfl
  -- the tail
  have hw : SimR (wR u hr) (waveStep u s.r).1 := by
    refine ⟨rfl, ?_, ?_⟩
    · show SimE s.r.G (waveDR s.r.G u.1 u.2.1 hlo).1 (wave s.r.G u.1 u.2.1 s.r.lo).1
      rw [el1]; exact l1
    · show SimE s.r.G (waveDR s.r.G u.1 u.2.2 hhi).1 (wave s.r.G u.1 u.2.2 s.r.hi).1
      rw [eu1]; exact u1
  have hsq : SimQ (⟨hr, hact⟩ : HQS α) s := ⟨⟨rfl, slo, shi⟩, hact'⟩
  obtain ⟨t1, t2⟩ := tailStep_gen (K := K) (rt := rt) (fun _ _ _ _ _ => candR u hr) hsq u hw
  obtain ⟨p1, p2⟩ := relStep_perm K rt delivCand
    (liftCand (fun _ _ _ _ _ => candR u hr)) u s hinv.wf hroot D hD pC
  -- lengths
  have lenRl : rl.length ≤ 1 + vol s.r.G s.r.lo wlo := by
    rw [length_eq_card nRl s.r.G.N _ mRl]
    exact LiteralK11.card_changed_le hinv.wf (inv_exact hinv.invLo) (inv_exact wl1) hxs wl3
  have lenRh : rh.length ≤ 1 + vol s.r.G s.r.hi whi := by
    rw [length_eq_card nRh s.r.G.N _ mRh]
    exact LiteralK11.card_changed_le hinv.wf (inv_exact hinv.invHi) (inv_exact wu1) hxs wu3
  have lenM : (mergedR u hr).length ≤ rl.length + rh.length := by
    rw [pM.length_eq, length_eq_card nRl s.r.G.N _ mRl, length_eq_card nRh s.r.G.N _ mRh]
    exact LiteralK11.length_filter_or_le _ _ _
  have lenC : (candR u hr).length ≤ vol s.r.G s.r.lo wlo + vol s.r.G s.r.hi whi := by
    rw [pC.length_eq]
    exact delivCand_length s.r (waveStep u s.r).1
  have ePrep : prepR u hr = (waveStepD u hr).2 + 2 * (rl.length + rh.length)
      + (mergedR u hr).length + (candR u hr).length := by
    show (waveDR s.r.G u.1 u.2.1 hlo).2.1 + (waveDR s.r.G u.1 u.2.2 hhi).2.1
        + (rl.length + rh.length) + ((mergedR u hr).length + (candR u hr).length)
      = (waveD s.r.G u.1 u.2.1 hlo).2 + (waveD s.r.G u.1 u.2.2 hhi).2 + _ + _ + _
    have el2' : (waveDR s.r.G u.1 u.2.1 hlo).2.1 = (waveD s.r.G u.1 u.2.1 hlo).2 + rl.length := el2
    have eu2' : (waveDR s.r.G u.1 u.2.2 hhi).2.1 = (waveD s.r.G u.1 u.2.2 hhi).2 + rh.length := eu2
    rw [el2', eu2']
    omega
  have eA' : (relStep K rt (liftCand (fun _ _ _ _ _ => candR u hr)) u s).2
      = (wave s.r.G u.1 u.2.1 s.r.lo).2 + (wave s.r.G u.1 u.2.2 s.r.hi).2
        + (retireList (candR u hr) (waveStep u s.r).1).2
        + (releaseLoop (protOf K rt s.act)
            (relFuel (retireList (candR u hr) (waveStep u s.r).1).1.G
              ((candR u hr).map Prod.snd))
            ((candR u hr).map Prod.snd)
            (retireList (candR u hr) (waveStep u s.r).1).1.G).2 := rfl
  have eS : (relStepR K rt u ⟨hr, hact⟩).2 = prepR u hr
      + (LiteralE4.tailStep K rt (fun _ _ _ _ _ => candR u hr) ⟨hr, hact⟩ (wR u hr)).2 := rfl
  have t2' : (LiteralE4.tailStep K rt (fun _ _ _ _ _ => candR u hr) ⟨hr, hact⟩ (wR u hr)).2
      ≤ 2 * ((retireList (candR u hr) (waveStep u s.r).1).2
        + (releaseLoop (protOf K rt s.act)
            (relFuel (retireList (candR u hr) (waveStep u s.r).1).1.G
              ((candR u hr).map Prod.snd))
            ((candR u hr).map Prod.snd)
            (retireList (candR u hr) (waveStep u s.r).1).1.G).2) := t2
  have eWD : (waveStepD u hr).2 = (waveD s.r.G u.1 u.2.1 hlo).2 + (waveD s.r.G u.1 u.2.2 hhi).2 :=
    rfl
  refine ⟨⟨rl1, fun q => ?_⟩, ⟨ru1, fun q => ?_⟩, nM, ?_, ?_, eW, ?_, ?_, ?_, ePrep, ?_⟩
  · show q ∈ (waveDR s.r.G u.1 u.2.1 hlo).2.2 ↔ q < s.r.G.N ∧ (wR u hr).lo.val q ≠ hlo.val q
    rw [rl2 q, eWl]
  · show q ∈ (waveDR s.r.G u.1 u.2.2 hhi).2.2 ↔ q < s.r.G.N ∧ (wR u hr).hi.val q ≠ hhi.val q
    rw [ru2 q, eWh]
  · show (mergedR u hr).Perm ((List.range s.r.G.N).filter (fun g =>
      (wR u hr).lo.val g ≠ hlo.val g ∨ (wR u hr).hi.val g ≠ hhi.val g))
    rw [vWl, vWh, slo.val, shi.val]
    exact pM
  · show (candR u hr).Perm (delivV hr.G hr.lo.val hr.hi.val (wR u hr).lo.val (wR u hr).hi.val)
    rw [eD]
    exact pC
  · rw [← p1]
    exact t1
  · rw [eS, ePrep, eWD]
    rw [eA'] at p2
    have e4 : 4 * Nat.clog 2 D * (live s.r.G - live (rstep delivCand u s.r).1.G)
        = 2 * (2 * Nat.clog 2 D * (live s.r.G - live (rstep delivCand u s.r).1.G)) := by ring
    rw [e4]
    omega
  · rw [eS, ePrep, eWD]
    omega
  · show 2 * (rl.length + rh.length) + (mergedR u hr).length + (candR u hr).length
      ≤ 6 + 4 * (vol s.r.G s.r.lo wlo + vol s.r.G s.r.hi whi)
    omega

end EngineR

/-! ## 6. The executed engine on the run `R` -/

section Run

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α)

/-- State of the executed engine after `t` rollouts (same initial state `hq0B` as
`LiteralK10`). -/
def hrunR (t : ℕ) : HQS α := runSR R.K R.rt R.u R.q (hq0B R) t

/-- State of the executed engine immediately before the waves of rollout `t + 1`. -/
def hpreR (t : ℕ) : HQS α :=
  if R.q t = true then (qRetireH R.K R.rt (hrunR R t)).1 else hrunR R t

/-- The list recorded by the lower wave of rollout `t + 1`. -/
def recLoR (t : ℕ) : List ℕ := (recLo (R.u (t + 1)) (hpreR R t).r).2.2

/-- The list recorded by the upper wave of rollout `t + 1`. -/
def recHiR (t : ℕ) : List ℕ := (recHi (R.u (t + 1)) (hpreR R t).r).2.2

/-- Implemented state after the two waves of rollout `t + 1`. -/
def wR1 (t : ℕ) : HRState α := wR (R.u (t + 1)) (hpreR R t).r

/-- The gates whose stored value changed in one of the two waves of rollout `t + 1`, in
increasing order (a specification object: the engine does not compute it). -/
def chgR (t : ℕ) : List ℕ :=
  (List.range (hpreR R t).r.G.N).filter (fun g =>
    (wR1 R t).lo.val g ≠ (hpreR R t).r.lo.val g ∨ (wR1 R t).hi.val g ≠ (hpreR R t).r.hi.val g)

/-- The merged list of rollout `t + 1` (computed by the engine). -/
def mergedRt (t : ℕ) : List ℕ := mergedR (R.u (t + 1)) (hpreR R t).r

/-- The candidate list of rollout `t + 1` (computed by the engine, read by its retirement
pass and release cascade). -/
def candRt (t : ℕ) : List (ℕ × ℕ) := candR (R.u (t + 1)) (hpreR R t).r

/-- Cost of recording, merging and building the candidate list in rollout `t + 1`; it is
part of the computed cost `costSR` (`prepR`). -/
def extraR (t : ℕ) : ℕ :=
  2 * ((recLoR R t).length + (recHiR R t).length) + (mergedRt R t).length + (candRt R t).length

lemma deg_pre (t : ℕ) : ∀ p, ((R.pre t).r.G.children p).length ≤ R.D :=
  fun p => ((R.pre_inv t).csub p).length_le.trans (R.deg p)

lemma simR_all : ∀ t, SimQ (hrunR R t) (R.run t) ∧ SimQ (hpreR R t) (R.pre t) := by
  have hpre : ∀ t, SimQ (hrunR R t) (R.run t) → SimQ (hpreR R t) (R.pre t) := by
    intro t ih
    unfold hpreR SelRun.pre preF
    by_cases hq : R.q t = true
    · rw [ite_eq_left hq, ite_eq_left hq]
      exact (qRetireH_sim R.K R.rt ih).1
    · rw [ite_eq_right hq, ite_eq_right hq]
      exact ih
  have hrun : ∀ t, SimQ (hrunR R t) (R.run t) := by
    intro t
    induction t with
    | zero => exact ⟨(initB_facts R).1, rfl⟩
    | succ t ih =>
      exact (relStepR_spec (hpre t ih) (R.pre_inv t) (R.rooted_all t).2.2 R.D (deg_pre R t)
        (R.u (t + 1)) (R.hn t).1).2.2.2.2.2.2.1
  exact fun t => ⟨hrun t, hpre t (hrun t)⟩

/-- **Rollout `t + 1` of the executed engine on the run.** -/
theorem stepR (t : ℕ) :
    ((recLoR R t).Nodup ∧ ∀ q, q ∈ recLoR R t ↔
      q < (hpreR R t).r.G.N ∧ (wR1 R t).lo.val q ≠ (hpreR R t).r.lo.val q) ∧
    ((recHiR R t).Nodup ∧ ∀ q, q ∈ recHiR R t ↔
      q < (hpreR R t).r.G.N ∧ (wR1 R t).hi.val q ≠ (hpreR R t).r.hi.val q) ∧
    (mergedRt R t).Nodup ∧ (mergedRt R t).Perm (chgR R t) ∧
    (candRt R t).Perm (delivV (hpreR R t).r.G (hpreR R t).r.lo.val (hpreR R t).r.hi.val
      (wR1 R t).lo.val (wR1 R t).hi.val) ∧
    wR1 R t = (waveStepD (R.u (t + 1)) (hpreR R t).r).1 ∧
    prepR (R.u (t + 1)) (hpreR R t).r = (waveStepD (R.u (t + 1)) (hpreR R t).r).2 + extraR R t ∧
    extraR R t ≤ 6 + 4 * volF R.K R.rt delivCand R.u R.q R.s0 t ∧
    costSR R.K R.rt R.u R.q (hq0B R) t + 4 * (R.G0.L + 3)
      ≤ 12 + 6 * volF R.K R.rt delivCand R.u R.q R.s0 t
        + 2 * costF R.K R.rt delivCand R.u R.q R.s0 t
        + 4 * Nat.clog 2 R.D * retF R.K R.rt delivCand R.u R.q R.s0 t ∧
    volF R.K R.rt delivCand R.u R.q R.s0 t ≤ costSR R.K R.rt R.u R.q (hq0B R) t := by
  obtain ⟨hS, hP⟩ := simR_all R t
  obtain ⟨a1, a2, a3, a4, a5, a6, _, a8, a9, a10, a11⟩ := relStepR_spec hP (R.pre_inv t)
    (R.rooted_all t).2.2 R.D (deg_pre R t) (R.u (t + 1)) (R.hn t).1
  obtain ⟨e1, e2, _⟩ := rstep_endpoints delivCand (R.u (t + 1)) (R.pre t).r
  have hvF : volF R.K R.rt delivCand R.u R.q R.s0 t
      = vol (R.pre t).r.G (R.pre t).r.lo
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1
        + vol (R.pre t).r.G (R.pre t).r.hi
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1 := by
    show vol (R.pre t).r.G (R.pre t).r.lo (relStep R.K R.rt delivCand (R.u (t + 1)) (R.pre t)).1.r.lo
      + vol (R.pre t).r.G (R.pre t).r.hi (relStep R.K R.rt delivCand (R.u (t + 1)) (R.pre t)).1.r.hi
      = _
    have f1 : (relStep R.K R.rt delivCand (R.u (t + 1)) (R.pre t)).1.r.lo
        = (rstep delivCand (R.u (t + 1)) (R.pre t).r).1.lo := rfl
    have f2 : (relStep R.K R.rt delivCand (R.u (t + 1)) (R.pre t)).1.r.hi
        = (rstep delivCand (R.u (t + 1)) (R.pre t).r).1.hi := rfl
    rw [f1, f2, e1, e2]
  have hq2 : (if R.q t = true then R.K + (qRetireH R.K R.rt (hrunR R t)).2 else 0)
      = (if R.q t = true then R.K + (qRetire R.K R.rt (R.run t)).2 else 0) := by
    rw [(qRetireH_sim R.K R.rt hS).2]
  have hcS : costSR R.K R.rt R.u R.q (hq0B R) t
      = (if R.q t = true then R.K + (qRetire R.K R.rt (R.run t)).2 else 0)
        + (relStepR R.K R.rt (R.u (t + 1)) (hpreR R t)).2 := by
    show (if R.q t = true then R.K + (qRetireH R.K R.rt (hrunR R t)).2 else 0) + _ = _
    rw [hq2]
    rfl
  have hcF : costF R.K R.rt delivCand R.u R.q R.s0 t
      = (if R.q t = true then R.K + (qRetire R.K R.rt (R.run t)).2 else 0)
        + (relStep R.K R.rt delivCand (R.u (t + 1)) (R.pre t)).2 := rfl
  have hrF : retF R.K R.rt delivCand R.u R.q R.s0 t
      = live (R.pre t).r.G - live (rstep delivCand (R.u (t + 1)) (R.pre t).r).1.G := rfl
  refine ⟨a1, a2, a3, a4, a5, a6, ?_, ?_, ?_, ?_⟩
  · rw [a10]; unfold extraR recLoR recHiR mergedRt candRt; omega
  · rw [hvF]; exact a11
  · rw [hcS, hcF, hvF, hrF]
    have key : ∀ (X cs kv A B : ℕ), cs + 4 * (R.G0.L + 3) ≤ 12 + 6 * kv + 2 * A + B →
        X + cs + 4 * (R.G0.L + 3) ≤ 12 + 6 * kv + 2 * (X + A) + B := by
      intros
      omega
    exact key _ _ _ _ _ a8
  · rw [hcS, hvF]
    exact a9.trans (Nat.le_add_left _ _)

/-- Computed cost of the `τ` rollouts and the queries at times `t < τ`. -/
def WrollR : ℕ := ∑ t ∈ range R.τ, costSR R.K R.rt R.u R.q (hq0B R) t

/-- Computed cost of the query at the stopping time `τ`. -/
def WlastR : ℕ := if R.q R.τ = true then R.K + (qRetireH R.K R.rt (hrunR R R.τ)).2 else 0

/-- Computed cost of the final disposal pass. -/
def WdispR : ℕ := (disposeAll (List.range R.G0.N) (hpreR R R.τ).r.G).2

/-- **Total scalar work of the executed engine**: the given `P` and `R.H`, plus the
computed costs of initialisation, of all rollouts (recording waves, merge, candidate
construction, tests, heap deletions, release) and queries, and of final disposal. -/
def WR : ℕ := R.P + R.H + WinitB R + WrollR R + WlastR R + WdispR R

/-- The part of `WrollR` spent on recording, merging and building candidate lists. -/
def WcandR : ℕ := ∑ t ∈ range R.τ, extraR R t

theorem WcandR_le : WcandR R ≤ 6 * R.τ + 4 * R.Splus := by
  have hvol : ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus :=
    sum_congr rfl (fun t _ => R.volF_eq t)
  calc WcandR R ≤ ∑ t ∈ range R.τ, (6 + 4 * volF R.K R.rt delivCand R.u R.q R.s0 t) :=
        sum_le_sum (fun t _ => (stepR R t).2.2.2.2.2.2.2.1)
    _ = 6 * R.τ + 4 * R.Splus := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum, hvol]
        ring

/-- **The work bound of the executed engine.** -/
theorem WR_le : WR R ≤ 18 * XD R := by
  obtain ⟨_, i2, _⟩ := R.init_facts
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
  have hroll : WrollR R + R.τ * (4 * (R.G0.L + 3))
      ≤ 12 * R.τ + 6 * ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t
        + 2 * ∑ t ∈ range R.τ, costF R.K R.rt delivCand R.u R.q R.s0 t
        + 4 * Nat.clog 2 R.D * ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t := by
    calc WrollR R + R.τ * (4 * (R.G0.L + 3))
        = ∑ t ∈ range R.τ, (costSR R.K R.rt R.u R.q (hq0B R) t + 4 * (R.G0.L + 3)) := by
          unfold WrollR
          rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
      _ ≤ ∑ t ∈ range R.τ, (12 + 6 * volF R.K R.rt delivCand R.u R.q R.s0 t
          + 2 * costF R.K R.rt delivCand R.u R.q R.s0 t
          + 4 * Nat.clog 2 R.D * retF R.K R.rt delivCand R.u R.q R.s0 t) :=
          sum_le_sum (fun t _ => (stepR R t).2.2.2.2.2.2.2.2.1)
      _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, card_range,
            ← mul_sum, ← mul_sum, ← mul_sum, smul_eq_mul]
          ring
  have hlast : WlastR R + 2 * cells (R.pre R.τ).r.G
      ≤ 4 * (if R.q R.τ = true then R.K else 0) + 2 * cells (R.run R.τ).r.G := by
    unfold WlastR SelRun.pre preF
    by_cases hq : R.q R.τ = true
    · rw [ite_eq_left hq, ite_eq_left hq, ite_eq_left hq]
      have h1 := (qRetireH_sim R.K R.rt (simR_all R R.τ).1).2
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
  have hdisp : WdispR R ≤ R.G0.N + cells (R.pre R.τ).r.G := by
    have hG : (hpreR R R.τ).r.G = (R.pre R.τ).r.G := (simR_all R R.τ).2.r.G
    have hN : (R.pre R.τ).r.G.N = R.G0.N := (R.pre_inv R.τ).nEq
    have h1 := disposeAll_cost (List.range R.G0.N) (R.pre R.τ).r.G
      (fun g hg => by rw [hN]; exact List.mem_range.1 hg)
    have h2 := live_le_cells (R.pre R.τ).r.G
    unfold WdispR
    rw [hG]
    rw [List.length_range] at h1
    omega
  have hinit := (initB_facts R).2
  have hretm := Nat.mul_le_mul_left (2 * Nat.clog 2 R.D + 4)
    (show ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t ≤ live R.G0 by omega)
  have hretc := Nat.mul_le_mul_left (4 * Nat.clog 2 R.D)
    (show ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t ≤ live R.G0 by omega)
  have hsc : R.scans = ((range R.τ).filter (fun t => R.q t = true)).card * R.K
      + (if R.q R.τ = true then R.K else 0) := by
    unfold SelRun.scans
    rw [sum_range_succ, ← sum_filter, sum_const, smul_eq_mul]
  have hTL1 : 2 * R.τ * (R.G0.L + 3) = 2 * (R.τ * (R.G0.L + 3)) := by ring
  have hTL2 : R.τ * (4 * (R.G0.L + 3)) = 4 * (R.τ * (R.G0.L + 3)) := by ring
  rw [hTL1] at hlw
  rw [hTL2] at hroll
  rw [hvol] at hlw hroll
  unfold WR XD Hsh
  rw [hsc]
  generalize R.τ * (R.G0.L + 3) = TL at *
  generalize (if R.q R.τ = true then R.K else 0) = a at *
  generalize ((range R.τ).filter (fun t => R.q t = true)).card = cq at *
  generalize ∑ t ∈ range R.τ, costF R.K R.rt delivCand R.u R.q R.s0 t = A at *
  generalize ∑ t ∈ range R.τ, testsF R.K R.rt delivCand R.u R.q R.s0 t = T at *
  generalize ∑ t ∈ range R.τ, retF R.K R.rt delivCand R.u R.q R.s0 t = Rt at *
  generalize Nat.clog 2 R.D = c at *
  have n1 := Nat.zero_le (c * R.Splus)
  have n2 := Nat.zero_le (c * live R.G0)
  have n3 := Nat.zero_le (cq * R.K)
  nlinarith [n1, n2, n3]

end Run

/-! ## 7. `prop:representation-cost` for the executed engine -/

section Final

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, for the engine whose
retirement candidates are built from the gates recorded by its waves.**

Same hypotheses as `LiteralK11.representation_cost_upper_D` (only the fields of
`R : LiteralK3.SelRun α`).  Conclusions:

1. the executed engine represents the abstract run `RetireFinal.runF` at every time;
2. `F_t` is the live incidence set of the executed engine before the waves of rollout
   `t + 1`;
3. the reference valuations are exact and `b_{t+1}(v) ≤ 2`;
4. the deliveries through `τ` are exactly `S^+`, and the computed rollout work is at least
   `S^+`;
5. after the final disposal pass no incidence is left;
6. in every rollout `t + 1`: each wave's recorded list is duplicate-free and consists
   exactly of the gates whose stored value that wave changed; the merged list is
   duplicate-free and a permutation of `chgR R t` (the changed gates in increasing order);
   the candidate list the engine reads is a permutation of the `delivV` list of the same
   states; the waves execute `waveD`; the computed preparation cost is the `waveD` cost
   plus `extraR R t` (recording, merging, building), and `extraR R t ≤ 6 + 4 · volF t`;
7. the total recording/merging/building cost is at most `6τ + 4 S^+`;
8. `WR ≤ 18 (H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))`, with `H = Hsh R`;
9. the same with `H` written as `R.H + τ + Q·K`;
10. if every rollout has given shared work at least one and every query time given shared
    work at least `K`, then `WR ≤ 54 · R.X`. -/
theorem representation_cost_upper_R {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α) :
    (∀ t, SimQ (hrunR R t) (R.run t) ∧ SimQ (hpreR R t) (R.pre t)) ∧
    (∀ t, R.F t = liveInc (hpreR R t).r.G) ∧
    (∀ t, Exact R.G0 (R.refLo t) ∧ Exact R.G0 (R.refHi t)) ∧ (∀ t v, R.b t v ≤ 2) ∧
    (∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus) ∧
    R.Splus ≤ WrollR R ∧
    (∀ p, (disposeAll (List.range R.G0.N) (hpreR R R.τ).r.G).1.children p = []) ∧
    (∀ t,
      ((recLoR R t).Nodup ∧ ∀ q, q ∈ recLoR R t ↔
        q < (hpreR R t).r.G.N ∧ (wR1 R t).lo.val q ≠ (hpreR R t).r.lo.val q) ∧
      ((recHiR R t).Nodup ∧ ∀ q, q ∈ recHiR R t ↔
        q < (hpreR R t).r.G.N ∧ (wR1 R t).hi.val q ≠ (hpreR R t).r.hi.val q) ∧
      (mergedRt R t).Nodup ∧ (mergedRt R t).Perm (chgR R t) ∧
      (candRt R t).Perm (delivV (hpreR R t).r.G (hpreR R t).r.lo.val (hpreR R t).r.hi.val
        (wR1 R t).lo.val (wR1 R t).hi.val) ∧
      wR1 R t = (waveStepD (R.u (t + 1)) (hpreR R t).r).1 ∧
      prepR (R.u (t + 1)) (hpreR R t).r
        = (waveStepD (R.u (t + 1)) (hpreR R t).r).2 + extraR R t ∧
      extraR R t ≤ 6 + 4 * volF R.K R.rt delivCand R.u R.q R.s0 t) ∧
    WcandR R ≤ 6 * R.τ + 4 * R.Splus ∧
    WR R ≤ 18 * XD R ∧
    WR R ≤ 18 * (R.H + R.τ + R.scans + R.P + R.G0.N + live R.G0
      + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)) ∧
    ((∀ t, t < R.τ → 1 ≤ R.h t) → (∀ t, t ≤ R.τ → R.q t = true → R.K ≤ R.h t) →
      WR R ≤ 54 * R.X) := by
  have hK3 := representation_cost_upper R
  have hW := WR_le R
  have hvol : ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus :=
    hK3.2.2.2.1
  refine ⟨simR_all R, fun t => ?_, hK3.2.1, hK3.2.2.1, hvol, ?_, fun p => ?_,
    fun t => ?_, WcandR_le R, hW, ?_, fun ha hb => ?_⟩
  · rw [R.F_eq t, (simR_all R t).2.r.G]
  · rw [← hvol]
    exact sum_le_sum (fun t _ => (stepR R t).2.2.2.2.2.2.2.2.2)
  · have hG : (hpreR R R.τ).r.G = (R.pre R.τ).r.G := (simR_all R R.τ).2.r.G
    have hN : (R.pre R.τ).r.G.N = R.G0.N := (R.pre_inv R.τ).nEq
    rw [hG, ← hN]
    exact disposeAll_empty (R.rooted_all R.τ).2.1 p
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, _, _⟩ := stepR R t
    exact ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
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
theorem representation_cost_upper_isBigO_R {α ι : Type*} [LinearOrder α] [OrderBot α]
    {l : Filter ι} (R : ι → SelRun α) :
    (fun i => (WR (R i) : ℝ)) =O[l] (fun i => (XD (R i) : ℝ)) := by
  apply IsBigO.of_bound 18
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast WR_le (R i)

/-- **`prop:representation-cost` as one theorem** for the executed engine (total work
`W_G = WR (G i)`, every cost computed by the program, candidate list built from the
recorded gates); `C i` is any family of implementations of the incidence-delivery contract.

1. `W_G ≤ 18 X_G` for every `i`, hence `W_G = O(X_G)`;
2. `P_C + S_C^- ≤ W_C` for every `i`;
3. condition (R), `X_G = o(P_C + S_C^-)`, implies `W_G = o(W_C)`. -/
theorem representation_cost {α β Cell ι : Type*} [LinearOrder α] [OrderBot α]
    [DecidableEq β] [DecidableEq Cell] {l : Filter ι}
    (G : ι → SelRun α) (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WR (G i) ≤ 18 * XD (G i)) ∧
    (fun i => (WR (G i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WR (G i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  have hG := representation_cost_upper_isBigO_R (l := l) G
  exact ⟨fun i => WR_le (G i), hG, fun i => (C i).lower,
    fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)** for the executed engine: against the retirement engine itself
as the compiled representation (`LiteralK4.engineImpl`). -/
theorem condition_R_engine_R {α β ι : Type*} [LinearOrder α] [OrderBot α] [LinearOrder β]
    [OrderBot β] {l : Filter ι} (G : ι → SelRun α) (RC : ι → EngineRun β)
    (hR : (fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WR (G i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
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
  have h1 := (LiteralF4.representation_cost (l := l) G
    (fun i => LiteralK4.engineImpl (RC i))).2.2.2 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast LiteralK4.engineImpl_W_le (RC i)

end Final

end LiteralF4
end JointRootCert
