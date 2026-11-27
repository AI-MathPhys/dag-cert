/-
Joint Root Certification: `prop:representation-cost` (Unified Full-Cost Representation
Comparison), upper bound `eq:prop-rep-upper`, for an engine whose incidence lists are
doubly linked lists in arrays, with every remaining convention of `LiteralG2` replaced by an
executed, charged step.

Manuscript result covered: `prop:representation-cost` (all three sentences), restated from
`LiteralG2` for a modified executed program (the linked engine).

## Cost model

The RAM cost model: one unit per array cell read or write and per arithmetic comparison.
The new executed parts below (unlinks, traversals, list construction, scans, exit tests)
charge each access individually; the parts taken over from `LiteralG2` keep its per-step
charges (each a constant number of such operations).  Arrays are total functions `ℕ → ·`
with arbitrary initial contents (`Mem`); nothing assumes zero-initialised memory.

## The four conventions of `LiteralG2` and how they are removed

1. **Unlinks at O(1).**  `LiteralG2` unlinks with `List.filter` and charges 1 per unlink.
   Here the incidences are records `1, …, M` (`Lin`): record `e` stores `src e`, `dst e`
   and, for the child list of `src e` and the parent list of `dst e`, its next and previous
   records (`DL`: heads `hd`, pointers `nx`, `pv`; `0` is null).  `DL.unlink` executes at
   most 6 array accesses (`DRep.unlink`: the owner's list loses the record, all other lists
   are unchanged).  A retirement (`retireOneL`) unlinks the record from both lists; a release
   (`relGate`) follows the next pointers of the child list (`relTrav`), unlinking each record
   from the parent list of its child, and writes a null head.  `AbsR` is the abstraction
   (simulation) relation: with ghost lists, mapping `dst` over the child lists and `src` over
   the parent lists gives the child and parent lists of the engine's circuit; `readback`:
   following the pointers reads them back exactly.  `AbsR.retire` / `AbsR.release`: the
   linked operations represent `retireDag` / `releaseDag`.  The circuit field of the engine
   state is kept as a ghost equal to the readback at every time (`simL_all`,
   `representation_cost_upper_Lin` 2); the waves read parent lists from it, which is reading
   the linked list (already charged per parent by `dlv`).  The structure is built by
   `buildLin` (phases A, B, D) from arbitrary contents, in `15 · live + 10 N + 3` executed
   units (`buildLin_spec`); this needs the children of `G0` to be gates (`< N`), a hypothesis
   (`hcl`) of the final theorems (`Dag.WF` states it only for parents).
2. **Empty-list exits.**  `dlvX`, `loopDX`, `waveDX`, `setMarksX`, `clearMarksX`,
   `filterUnmarkedX`, `mergeMX`, `incAllX`, `decAllX`, `zeroAllX`, `retireListL`, `disposeL`,
   `candTrav`, `dstAll`, `heapLoopX`, `initPassBX` charge 1 for every exit test; each computes
   the same state as its `LiteralG2` / `LiteralE7a` counterpart (`*_eq`).
3. **Query scans.**  `leadScanX` (6 per index), `stopScanX` (6 per index) and `retScanX`
   (7 per index) are executed loops over the `K` roots with an exit test; their outputs are
   `leadScan`, `stopScan`, `deact` / `retiredRoots` and their costs are exactly `6K + 1`,
   `6K + 1`, `7K + 1` (`leadScanX_spec`, `stopScanX_spec`, `retScanX_spec`); the query output
   is `RetireFinal.qOut` (`qOutL_eq`).
4. **Heap fuel.**  `stepOK` mirrors every heap call of a rollout (both waves: every
   `updateKey`; the retirement pass: every `delete`) and asserts that each of their sifts
   stops by its own test within the fuel `⌈log₂ n⌉`; `hlOK` does the same for every heapify
   of the initialisation.  `sifts_done`: they hold for every rollout of the run (all heaps
   of the engine are valid heaps, from `SimQ`, and remain so inside every pass).  Queries,
   cascades and the disposal execute no sift.

## Result

`WP ≤ WL ≤ 11 · WP + 10 τ + 15 · live + 12 N + 13` (`WL_bounds`), hence
`WL ≤ 292 · XD + 11 K` (`WL_le`) and `WL ≤ 303 · XD` when some query occurs by time `τ`
(`WL_le_query`) or the root actions are distinct gates `< N` (`WL_le_inj`).  All terms are
in `XD`: `τ, N, live ≤ XD` and `1 ≤ N`.  The term `11 K` comes, as in `LiteralG2`, from the
construction of the count table from the `K` root actions; `XD` contains `K` only through
the query scans `Q · K`.

Kept from `LiteralG2` (not conventions of the list above): the fuels of the wave loop
(`N + 2`) and of the cascade (`relFuel`), for which `LiteralG2` proves that the loops reach
their exit tests (`waveDone`, `doneR`; `loopDX` and `releaseLoopL` take the same branches as
`loopDR` and `releaseLoopG`); the traversal fuel `M + 1`, proved not to bind here
(`relTrav_eq`, `travE_eq`).
-/

import JointRootCert.LiteralG2

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace JointRootCert
namespace LiteralG4


/-! ## 1. Doubly linked lists in arrays -/

section DLists

/-- One family of doubly linked lists over records `1, 2, …` (`0` is the null pointer), all
stored in three arrays: the head record of the list of each gate, and the next and previous
record of each record. -/
structure DL where
  hd : ℕ → ℕ
  nx : ℕ → ℕ
  pv : ℕ → ℕ

/-- `Seg nx pv p l n`: the records of `l`, in this order, are doubly linked, the record
before the first is `p` and the record after the last is `n`. -/
def Seg (nx pv : ℕ → ℕ) : ℕ → List ℕ → ℕ → Prop
  | _, [], _ => True
  | p, x :: xs, n => pv x = p ∧ nx x = xs.headD n ∧ Seg nx pv x xs n

lemma headD_append (a b : List ℕ) (n : ℕ) : (a ++ b).headD n = a.headD (b.headD n) := by
  cases a <;> rfl

lemma seg_append (nx pv : ℕ → ℕ) : ∀ (a b : List ℕ) (p n : ℕ),
    Seg nx pv p (a ++ b) n ↔ Seg nx pv p a (b.headD n) ∧ Seg nx pv (a.getLastD p) b n := by
  intro a
  induction a with
  | nil => intro b p n; simp [Seg]
  | cons x a ih =>
    intro b p n
    show (pv x = p ∧ nx x = (a ++ b).headD n ∧ Seg nx pv x (a ++ b) n) ↔
      (pv x = p ∧ nx x = a.headD (b.headD n) ∧ Seg nx pv x a (b.headD n)) ∧
        Seg nx pv ((x :: a).getLastD p) b n
    rw [headD_append, ih, List.getLastD_cons]
    tauto

lemma seg_congr {nx pv nx' pv' : ℕ → ℕ} : ∀ (l : List ℕ) (p n : ℕ),
    (∀ x ∈ l, nx' x = nx x ∧ pv' x = pv x) → Seg nx pv p l n → Seg nx' pv' p l n := by
  intro l
  induction l with
  | nil => intro _ _ _ _; trivial
  | cons x l ih =>
    intro p n h hs
    obtain ⟨h1, h2, h3⟩ := hs
    obtain ⟨e1, e2⟩ := h x List.mem_cons_self
    exact ⟨e2.trans h1, e1.trans h2, ih x n (fun y hy => h y (List.mem_cons_of_mem _ hy)) h3⟩

lemma seg_single (nx pv : ℕ → ℕ) (p x n : ℕ) : Seg nx pv p [x] n ↔ pv x = p ∧ nx x = n := by
  simp [Seg]

lemma getLastD_pos : ∀ (a : List ℕ), (∀ x ∈ a, 0 < x) → a ≠ [] → 0 < a.getLastD 0 := by
  intro a ha hne
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
  exact ha _ (List.getLast_mem hne)

lemma headD_pos (b : List ℕ) (hb : ∀ x ∈ b, 0 < x) (hne : b ≠ []) : 0 < b.headD 0 := by
  cases b with
  | nil => exact absurd rfl hne
  | cons y b => exact hb y List.mem_cons_self

/-- **Unlink of a record** `e` from the list of gate `o` (`o` its owner): read the previous
and the next record (2), test the previous for null (1) and write either the head of `o` or
the next pointer of the previous record (1), test the next for null (1) and, if it is not
null, write its previous pointer (1).  At most 6 array accesses. -/
def DL.unlink (D : DL) (o e : ℕ) : DL × ℕ :=
  (⟨if D.pv e = 0 then Function.update D.hd o (D.nx e) else D.hd,
    if D.pv e = 0 then D.nx else Function.update D.nx (D.pv e) (D.nx e),
    if D.nx e = 0 then D.pv else Function.update D.pv (D.nx e) (D.pv e)⟩,
   if D.nx e = 0 then 5 else 6)

/-- Ghost lists of a list family: `l g` is the list of records of gate `g`; `own e` is the
owner gate of record `e`. -/
structure DRep (D : DL) (l : ℕ → List ℕ) (own : ℕ → ℕ) (N : ℕ) : Prop where
  hd : ∀ g, g < N → D.hd g = (l g).headD 0
  seg : ∀ g, Seg D.nx D.pv 0 (l g) 0
  nd : ∀ g, (l g).Nodup
  own : ∀ g e, e ∈ l g → own e = g
  pos : ∀ g e, e ∈ l g → 0 < e
  emp : ∀ g, N ≤ g → l g = []

lemma DRep.not_mem {D : DL} {l : ℕ → List ℕ} {own : ℕ → ℕ} {N : ℕ} (h : DRep D l own N) {g e : ℕ}
    (hg : g ≠ own e) : e ∉ l g := fun he => hg (h.own g e he).symm

/-- **Correctness of the unlink**: the list of the owner loses `e`, every other list is
unchanged, and the cost is 5 or 6. -/
theorem DRep.unlink {D : DL} {l : ℕ → List ℕ} {own : ℕ → ℕ} {N : ℕ} (h : DRep D l own N) {e : ℕ}
    (he : e ∈ l (own e)) :
    DRep (D.unlink (own e) e).1 (Function.update l (own e) ((l (own e)).erase e)) own N ∧
    5 ≤ (D.unlink (own e) e).2 ∧ (D.unlink (own e) e).2 ≤ 6 := by
  set o := own e with ho
  obtain ⟨a, b, hab⟩ := List.append_of_mem he
  have hnd := h.nd o
  rw [hab] at hnd
  have hea : e ∉ a := fun hm => (List.nodup_append.1 hnd).2.2 e hm e List.mem_cons_self rfl
  have heb : e ∉ b := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  have hpos : ∀ x ∈ l o, 0 < x := h.pos o
  rw [hab] at hpos
  have hposa : ∀ x ∈ a, 0 < x := fun x hx => hpos x (List.mem_append_left _ hx)
  have hposb : ∀ x ∈ b, 0 < x := fun x hx => hpos x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
  have hseg := h.seg o
  rw [hab, seg_append] at hseg
  obtain ⟨sa, se⟩ := hseg
  obtain ⟨hpve, hnxe, sb⟩ := se
  have herase : (l o).erase e = a ++ b := by
    rw [hab, List.erase_append_right _ hea, List.erase_cons_head]
  have hcost : 5 ≤ (D.unlink o e).2 ∧ (D.unlink o e).2 ≤ 6 := by
    unfold DL.unlink; split_ifs <;> simp
  refine ⟨?_, hcost⟩
  -- membership facts for other gates
  have hother : ∀ g, g ≠ o → ∀ x ∈ l o, x ∉ l g := by
    intro g hg x hx hxg
    exact hg ((h.own g x hxg).symm.trans (h.own o x hx))
  have hmem_lo : ∀ x, x ∈ a ∨ x ∈ b → x ∈ l o := by
    intro x hx
    rw [hab]
    rcases hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
  -- the new arrays
  set D' := (D.unlink o e).1 with hD'
  have hnd' : (a ++ b).Nodup := by
    rw [← herase]; exact (h.nd o).erase e
  -- case split on `a` and `b`
  rcases List.eq_nil_or_concat' a with ha | ⟨a', q, ha⟩
  · -- `e` is the first record
    have hpv0 : D.pv e = 0 := by rw [hpve, ha]; rfl
    subst ha
    rcases List.eq_nil_or_concat' b with hb | ⟨b', y', hb'⟩
    · subst hb
      have hnx0 : D.nx e = 0 := by rw [hnxe]; rfl
      have e1 : D'.hd = Function.update D.hd o 0 := by
        rw [hD']; unfold DL.unlink; simp [hpv0, hnx0]
      have e2 : D'.nx = D.nx := by rw [hD']; unfold DL.unlink; simp [hpv0]
      have e3 : D'.pv = D.pv := by rw [hD']; unfold DL.unlink; simp [hnx0]
      refine ⟨fun g hgN => ?_, fun g => ?_, fun g => ?_, fun g x hx => ?_, fun g x hx => ?_,
        fun g hgN => ?_⟩
      · rw [e1]
        by_cases hg : g = o
        · subst hg; simp [herase]
        · rw [Function.update_of_ne hg, Function.update_of_ne hg]; exact h.hd g hgN
      · rw [e2, e3]
        by_cases hg : g = o
        · subst hg; rw [Function.update_self, herase]; trivial
        · rw [Function.update_of_ne hg]; exact h.seg g
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self]; exact (h.nd _).erase e
        · rw [Function.update_of_ne hg]; exact h.nd g
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.own _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.own g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.pos _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.pos g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self, h.emp _ hgN]; rfl
        · rw [Function.update_of_ne hg]; exact h.emp g hgN
    · -- `b` is nonempty: its first record `y`
      obtain ⟨y, b'', hb⟩ : ∃ y b'', b = y :: b'' := by
        cases b with
        | nil => exact absurd hb' (by simp)
        | cons y b'' => exact ⟨y, b'', rfl⟩
      clear hb'
      subst hb
      have hy : 0 < y := hposb y List.mem_cons_self
      have hnxy : D.nx e = y := by rw [hnxe]; rfl
      have hnx0 : D.nx e ≠ 0 := by rw [hnxy]; omega
      have e1 : D'.hd = Function.update D.hd o y := by
        rw [hD']; unfold DL.unlink; simp [hpv0, hnxy]
      have e2 : D'.nx = D.nx := by rw [hD']; unfold DL.unlink; simp [hpv0]
      have e3 : D'.pv = Function.update D.pv y 0 := by
        rw [hD']; unfold DL.unlink; dsimp only; rw [if_neg hnx0, hnxy, hpv0]
      have hyb : y ∉ b'' := (List.nodup_cons.1 hnd').1
      refine ⟨fun g hgN => ?_, fun g => ?_, fun g => ?_, fun g x hx => ?_, fun g x hx => ?_,
        fun g hgN => ?_⟩
      · rw [e1]
        by_cases hg : g = o
        · subst hg; simp [herase]
        · rw [Function.update_of_ne hg, Function.update_of_ne hg]; exact h.hd g hgN
      · rw [e2, e3]
        by_cases hg : g = o
        · subst hg
          rw [Function.update_self, herase]
          obtain ⟨s1, s2, s3⟩ := sb
          refine ⟨Function.update_self _ _ _, s2, ?_⟩
          refine seg_congr b'' y 0 (fun x hx => ⟨rfl, ?_⟩) s3
          exact Function.update_of_ne (fun ex => by subst ex; exact hyb hx) _ _
        · rw [Function.update_of_ne hg]
          refine seg_congr (l g) 0 0 (fun x hx => ⟨rfl, ?_⟩) (h.seg g)
          refine Function.update_of_ne (fun ex => ?_) _ _
          subst ex
          exact hother g hg x (hmem_lo x (Or.inr List.mem_cons_self)) hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self]; exact (h.nd _).erase e
        · rw [Function.update_of_ne hg]; exact h.nd g
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.own _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.own g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.pos _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.pos g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self, h.emp _ hgN]; rfl
        · rw [Function.update_of_ne hg]; exact h.emp g hgN
  · -- `a = a' ++ [q]`: `q` is the previous record
    subst ha
    have hq : 0 < q := hposa q (List.mem_append_right _ List.mem_cons_self)
    have hpvq : D.pv e = q := by rw [hpve]; simp
    have hpv0 : D.pv e ≠ 0 := by rw [hpvq]; omega
    rw [seg_append, seg_single] at sa
    obtain ⟨sa', hpq, hnq⟩ := sa
    have hqa' : q ∉ a' := fun hm =>
      (List.nodup_append.1 (List.nodup_append.1 hnd').1).2.2 q hm q (List.mem_singleton_self q) rfl
    rcases List.eq_nil_or_concat' b with hb | ⟨b', y', hb'⟩
    · subst hb
      have hnx0 : D.nx e = 0 := by rw [hnxe]; rfl
      have e1 : D'.hd = D.hd := by rw [hD']; unfold DL.unlink; simp [hpv0]
      have e2 : D'.nx = Function.update D.nx q 0 := by
        rw [hD']; unfold DL.unlink; dsimp only; rw [if_neg hpv0, hpvq, hnx0]
      have e3 : D'.pv = D.pv := by rw [hD']; unfold DL.unlink; simp [hnx0]
      refine ⟨fun g hgN => ?_, fun g => ?_, fun g => ?_, fun g x hx => ?_, fun g x hx => ?_,
        fun g hgN => ?_⟩
      · rw [e1]
        by_cases hg : g = o
        · subst hg
          rw [Function.update_self, herase, h.hd _ hgN, hab]
          cases a' <;> rfl
        · rw [Function.update_of_ne hg]; exact h.hd g hgN
      · rw [e2, e3]
        by_cases hg : g = o
        · subst hg
          rw [Function.update_self, herase, List.append_nil, seg_append, seg_single]
          refine ⟨?_, hpq, Function.update_self _ _ _⟩
          refine seg_congr a' 0 q (fun x hx => ⟨?_, rfl⟩) sa'
          exact Function.update_of_ne (fun ex => by subst ex; exact hqa' hx) _ _
        · rw [Function.update_of_ne hg]
          refine seg_congr (l g) 0 0 (fun x hx => ⟨?_, rfl⟩) (h.seg g)
          refine Function.update_of_ne (fun ex => ?_) _ _
          subst ex
          exact hother g hg x (hmem_lo x (Or.inl (List.mem_append_right _ List.mem_cons_self))) hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self]; exact (h.nd _).erase e
        · rw [Function.update_of_ne hg]; exact h.nd g
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.own _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.own g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.pos _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.pos g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self, h.emp _ hgN]; rfl
        · rw [Function.update_of_ne hg]; exact h.emp g hgN
    · obtain ⟨y, b'', hb⟩ : ∃ y b'', b = y :: b'' := by
        cases b with
        | nil => exact absurd hb' (by simp)
        | cons y b'' => exact ⟨y, b'', rfl⟩
      clear hb'
      subst hb
      have hy : 0 < y := hposb y List.mem_cons_self
      have hnxy : D.nx e = y := by rw [hnxe]; rfl
      have hnx0 : D.nx e ≠ 0 := by rw [hnxy]; omega
      have e1 : D'.hd = D.hd := by rw [hD']; unfold DL.unlink; simp [hpv0]
      have e2 : D'.nx = Function.update D.nx q y := by
        rw [hD']; unfold DL.unlink; dsimp only; rw [if_neg hpv0, hpvq, hnxy]
      have e3 : D'.pv = Function.update D.pv y q := by
        rw [hD']; unfold DL.unlink; dsimp only; rw [if_neg hnx0, hnxy, hpvq]
      have hyb : y ∉ b'' := (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).1
      have hqy : q ≠ y := by
        intro e'
        exact (List.nodup_append.1 hnd').2.2 q (List.mem_append_right _ List.mem_cons_self)
          y List.mem_cons_self e'
      have hya' : y ∉ a' := fun hm =>
        (List.nodup_append.1 hnd').2.2 y (List.mem_append_left _ hm) y List.mem_cons_self rfl
      have hqb : q ∉ b'' := fun hm =>
        (List.nodup_append.1 hnd').2.2 q (List.mem_append_right _ List.mem_cons_self) q
          (List.mem_cons_of_mem _ hm) rfl
      refine ⟨fun g hgN => ?_, fun g => ?_, fun g => ?_, fun g x hx => ?_, fun g x hx => ?_,
        fun g hgN => ?_⟩
      · rw [e1]
        by_cases hg : g = o
        · subst hg
          rw [Function.update_self, herase, h.hd _ hgN, hab]
          cases a' <;> rfl
        · rw [Function.update_of_ne hg]; exact h.hd g hgN
      · rw [e2, e3]
        by_cases hg : g = o
        · subst hg
          rw [Function.update_self, herase, seg_append, seg_append, seg_single]
          obtain ⟨s1, s2, s3⟩ := sb
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · refine seg_congr a' 0 q (fun x hx => ⟨?_, ?_⟩) sa'
            · exact Function.update_of_ne (fun ex => by subst ex; exact hqa' hx) _ _
            · exact Function.update_of_ne (fun ex => by subst ex; exact hya' hx) _ _
          · rw [Function.update_of_ne hqy]; exact hpq
          · rw [Function.update_self]; rfl
          · rw [show (a' ++ [q]).getLastD 0 = q by simp]
            refine ⟨Function.update_self _ _ _, ?_, ?_⟩
            · rw [Function.update_of_ne hqy.symm]; exact s2
            · refine seg_congr b'' y 0 (fun x hx => ⟨?_, ?_⟩) s3
              · exact Function.update_of_ne (fun ex => by subst ex; exact hqb hx) _ _
              · exact Function.update_of_ne (fun ex => by subst ex; exact hyb hx) _ _
        · rw [Function.update_of_ne hg]
          refine seg_congr (l g) 0 0 (fun x hx => ⟨?_, ?_⟩) (h.seg g)
          · refine Function.update_of_ne (fun ex => ?_) _ _
            subst ex
            exact hother g hg x (hmem_lo x (Or.inl (List.mem_append_right _ List.mem_cons_self))) hx
          · refine Function.update_of_ne (fun ex => ?_) _ _
            subst ex
            exact hother g hg x (hmem_lo x (Or.inr List.mem_cons_self)) hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self]; exact (h.nd _).erase e
        · rw [Function.update_of_ne hg]; exact h.nd g
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.own _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.own g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self] at hx; exact h.pos _ x (List.mem_of_mem_erase hx)
        · rw [Function.update_of_ne hg] at hx; exact h.pos g x hx
      · by_cases hg : g = o
        · subst hg; rw [Function.update_self, h.emp _ hgN]; rfl
        · rw [Function.update_of_ne hg]; exact h.emp g hgN

end DLists


open Finset CostEngines DagRetire RetireFinal

/-! ## 2. Traversals, sequences of unlinks, construction of one list -/

section Trav

/-- **Unlink of every record of a list**, in order (list form): for each record `e`, unlink
it from the list of its owner `own e` (5 or 6 accesses), push `own e` on the stack (1), plus
the traversal step (3: null test, read the owner, read the next pointer); 1 for the final
null test. -/
def travU (own : ℕ → ℕ) : List ℕ → DL → List ℕ → DL × List ℕ × ℕ
  | [], P, st => (P, st, 1)
  | e :: es, P, st =>
    ((travU own es (P.unlink (own e) e).1 st).1,
     own e :: (travU own es (P.unlink (own e) e).1 st).2.1,
     (P.unlink (own e) e).2 + 4 + (travU own es (P.unlink (own e) e).1 st).2.2)

/-- **The same, executed by following the next pointers `nx`** from the record `e`
(fuel `f`; `releaseTrav_eq` shows the fuel never binds). -/
def relTrav (nx own : ℕ → ℕ) : ℕ → ℕ → DL → List ℕ → DL × List ℕ × ℕ
  | 0, _, P, st => (P, st, 0)
  | f + 1, e, P, st =>
    if e = 0 then (P, st, 1)
    else ((relTrav nx own f (nx e) (P.unlink (own e) e).1 st).1,
      own e :: (relTrav nx own f (nx e) (P.unlink (own e) e).1 st).2.1,
      (P.unlink (own e) e).2 + 4 + (relTrav nx own f (nx e) (P.unlink (own e) e).1 st).2.2)

/-- **Readback of a list** by following the next pointers from `e`: the records visited, and
the cost (3 per record: null test, emit, read next; 1 for the final null test). -/
def travE (nx : ℕ → ℕ) : ℕ → ℕ → List ℕ × ℕ
  | 0, _ => ([], 0)
  | f + 1, e =>
    if e = 0 then ([], 1) else (e :: (travE nx f (nx e)).1, (travE nx f (nx e)).2 + 3)

theorem relTrav_eq (nx pv own : ℕ → ℕ) : ∀ (l : List ℕ) (f p : ℕ) (P : DL) (st : List ℕ),
    Seg nx pv p l 0 → (∀ x ∈ l, 0 < x) → l.length < f →
    relTrav nx own f (l.headD 0) P st = travU own l P st := by
  intro l
  induction l with
  | nil =>
    intro f p P st _ _ hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rfl
  | cons x xs ih =>
    intro f p P st hs hpos hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨_, h2, h3⟩ := hs
    have hx : x ≠ 0 := (hpos x List.mem_cons_self).ne'
    have e1 := ih f x (P.unlink (own x) x).1 st h3 (fun y hy => hpos y (List.mem_cons_of_mem _ hy))
      (by simp at hf; omega)
    show relTrav nx own (f + 1) x P st = _
    rw [relTrav, if_neg hx, h2, e1]
    rfl

theorem travE_eq (nx pv : ℕ → ℕ) : ∀ (l : List ℕ) (f p : ℕ),
    Seg nx pv p l 0 → (∀ x ∈ l, 0 < x) → l.length < f →
    travE nx f (l.headD 0) = (l, 3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro f p _ _ hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rfl
  | cons x xs ih =>
    intro f p hs hpos hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨_, h2, h3⟩ := hs
    have hx : x ≠ 0 := (hpos x List.mem_cons_self).ne'
    have e1 := ih f x h3 (fun y hy => hpos y (List.mem_cons_of_mem _ hy)) (by simp at hf; omega)
    show travE nx (f + 1) x = _
    rw [travE, if_neg hx, h2, e1]
    simp only [List.length_cons]
    congr 1

/-- **Correctness of the unlink sequence**: every list loses the records of `es`; the stack
receives the owners of `es` in order; the cost is between `9 |es| + 1` and `10 |es| + 1`. -/
theorem travU_spec (own : ℕ → ℕ) (N : ℕ) : ∀ (es : List ℕ) (D : DL) (l : ℕ → List ℕ) (st : List ℕ),
    DRep D l own N → es.Nodup → (∀ e ∈ es, e ∈ l (own e)) →
    DRep (travU own es D st).1 (fun g => (l g).filter (fun x => decide (x ∉ es))) own N ∧
    (travU own es D st).2.1 = es.map own ++ st ∧
    9 * es.length + 1 ≤ (travU own es D st).2.2 ∧
    (travU own es D st).2.2 ≤ 10 * es.length + 1 := by
  intro es
  induction es with
  | nil =>
    intro D l st h _ _
    refine ⟨?_, rfl, le_rfl, le_rfl⟩
    have : (fun g => (l g).filter (fun x => decide (x ∉ ([] : List ℕ)))) = l := by
      funext g; simp
    rw [this]; exact h
  | cons e es ih =>
    intro D l st h hnd hl
    obtain ⟨hne, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨u1, u2, u3⟩ := h.unlink (hl e List.mem_cons_self)
    set l1 := Function.update l (own e) ((l (own e)).erase e) with hl1
    have hl' : ∀ x ∈ es, x ∈ l1 (own x) := by
      intro x hx
      have hxe : x ≠ e := fun h' => hne (h' ▸ hx)
      rw [hl1]
      by_cases ho : own x = own e
      · rw [ho, Function.update_self]
        exact (List.mem_erase_of_ne hxe).2 (ho ▸ hl x (List.mem_cons_of_mem _ hx))
      · rw [Function.update_of_ne ho]
        exact hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨i1, i2, i3, i4⟩ := ih (D.unlink (own e) e).1 l1 st u1 hnd' hl'
    have hfun : (fun g => (l1 g).filter (fun x => decide (x ∉ es)))
        = (fun g => (l g).filter (fun x => decide (x ∉ e :: es))) := by
      funext g
      rw [hl1]
      by_cases hg : g = own e
      · subst hg
        rw [Function.update_self, (h.nd (own e)).erase_eq_filter, List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases h1 : x = e <;> by_cases h2 : x ∈ es <;> simp [h1, h2]
      · rw [Function.update_of_ne hg]
        apply List.filter_congr
        intro x hx
        have : x ≠ e := fun h' => h.not_mem hg (h' ▸ hx)
        simp [this]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show DRep (travU own es (D.unlink (own e) e).1 st).1 _ own N
      rw [← hfun]; exact i1
    · show own e :: (travU own es (D.unlink (own e) e).1 st).2.1 = _
      rw [i2]; rfl
    · show _ ≤ (D.unlink (own e) e).2 + 4 + (travU own es (D.unlink (own e) e).1 st).2.2
      simp only [List.length_cons]; omega
    · show (D.unlink (own e) e).2 + 4 + (travU own es (D.unlink (own e) e).1 st).2.2 ≤ _
      simp only [List.length_cons]; omega

/-- **Construction of one list** from the records `es` in order (recursively: build the rest,
then link `e` in front: 3 writes and 1 null test; 1 for the empty list).  Returns the arrays,
the head record and the cost. -/
def bldL : List ℕ → DL → DL × ℕ × ℕ
  | [], D => (D, 0, 1)
  | e :: es, D =>
    (⟨(bldL es D).1.hd, Function.update (bldL es D).1.nx e (bldL es D).2.1,
      if (bldL es D).2.1 = 0 then Function.update (bldL es D).1.pv e 0
      else Function.update (Function.update (bldL es D).1.pv e 0) (bldL es D).2.1 e⟩,
     e, (bldL es D).2.2 + 4)

theorem bldL_spec : ∀ (es : List ℕ) (D : DL), es.Nodup → (∀ x ∈ es, 0 < x) →
    Seg (bldL es D).1.nx (bldL es D).1.pv 0 es 0 ∧ (bldL es D).2.1 = es.headD 0 ∧
    (bldL es D).1.hd = D.hd ∧
    (∀ x, x ∉ es → (bldL es D).1.nx x = D.nx x ∧ (bldL es D).1.pv x = D.pv x) ∧
    (bldL es D).2.2 = 4 * es.length + 1 := by
  intro es
  induction es with
  | nil => intro D _ _; exact ⟨trivial, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, rfl⟩
  | cons e es ih =>
    intro D hnd hpos
    obtain ⟨hne, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨s1, s2, s3, s4, s5⟩ := ih D hnd' (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
    set B := bldL es D with hB
    have hpv : ∀ x, x ≠ e → x ≠ B.2.1 →
        (if B.2.1 = 0 then Function.update B.1.pv e 0
          else Function.update (Function.update B.1.pv e 0) B.2.1 e) x = B.1.pv x := by
      intro x h1 h2
      split_ifs
      · exact Function.update_of_ne h1 _ _
      · rw [Function.update_of_ne h2, Function.update_of_ne h1]
    have hpv2 : ∀ x, x ≠ e → x ∉ es →
        (if B.2.1 = 0 then Function.update B.1.pv e 0
          else Function.update (Function.update B.1.pv e 0) B.2.1 e) x = B.1.pv x := by
      intro x h1 h2
      split_ifs with h0
      · exact Function.update_of_ne h1 _ _
      · have hx2 : x ≠ B.2.1 := by
          intro h'
          rw [s2] at h' h0
          cases es with
          | nil => exact h0 rfl
          | cons y es' => exact h2 (by rw [h']; exact List.mem_cons_self)
        rw [Function.update_of_ne hx2, Function.update_of_ne h1]
    have hpve : (if B.2.1 = 0 then Function.update B.1.pv e 0
          else Function.update (Function.update B.1.pv e 0) B.2.1 e) e = 0 := by
      split_ifs with h0
      · exact Function.update_self _ _ _
      · have : e ≠ B.2.1 := by
          intro h'
          rw [s2] at h'
          cases es with
          | nil => exact h0 (s2.trans rfl)
          | cons y es' => exact hne (h' ▸ List.mem_cons_self)
        rw [Function.update_of_ne this, Function.update_self]
    refine ⟨⟨hpve, by
      show Function.update B.1.nx e B.2.1 e = _
      rw [Function.update_self, s2], ?_⟩, rfl, s3, fun x hx => ?_, ?_⟩
    · -- the rest of the list, with `e` in front
      cases es with
      | nil => trivial
      | cons y es' =>
        obtain ⟨t1, t2, t3⟩ := s1
        have hy0 : B.2.1 = y := s2
        have hyne : y ≠ 0 := (hpos y (List.mem_cons_of_mem _ List.mem_cons_self)).ne'
        have hye : y ≠ e := fun h' => hne (h' ▸ List.mem_cons_self)
        have hyes : y ∉ es' := (List.nodup_cons.1 hnd').1
        refine ⟨?_, ?_, ?_⟩
        · show (if B.2.1 = 0 then Function.update B.1.pv e 0
            else Function.update (Function.update B.1.pv e 0) B.2.1 e) y = e
          rw [hy0, if_neg hyne, Function.update_self]
        · show Function.update B.1.nx e B.2.1 y = _
          rw [Function.update_of_ne hye]; exact t2
        · refine seg_congr es' y 0 (fun x hx => ⟨?_, ?_⟩) t3
          · exact Function.update_of_ne (fun h' => hne (by rw [← h']; exact List.mem_cons_of_mem _ hx)) _ _
          · exact hpv x (fun h' => hne (by rw [← h']; exact List.mem_cons_of_mem _ hx))
              (fun h' => hyes (by rw [hy0] at h'; rw [← h']; exact hx))
    · have hxe : x ≠ e := fun h' => hx (by rw [h']; exact List.mem_cons_self)
      have hxes : x ∉ es := fun h' => hx (List.mem_cons_of_mem _ h')
      refine ⟨(Function.update_of_ne hxe _ _).trans (s4 x hxes).1, ?_⟩
      exact (hpv2 x hxe hxes).trans (s4 x hxes).2
    · show B.2.2 + 4 = _
      rw [s5, List.length_cons]; ring

/-- A duplicate-free list of records in `[1, M]` has at most `M` records. -/
lemma length_le_of_bound (l : List ℕ) (M : ℕ) (hnd : l.Nodup) (hb : ∀ x ∈ l, 0 < x ∧ x ≤ M) :
    l.length ≤ M := by
  rw [← List.toFinset_card_of_nodup hnd]
  have hs : l.toFinset ⊆ Finset.Icc 1 M := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_Icc]
    exact ⟨hb x hx |>.1, hb x hx |>.2⟩
  have := Finset.card_le_card hs
  rw [Nat.card_Icc] at this
  omega

end Trav


open Finset CostEngines DagRetire RetireFinal

/-! ## 3. The incidence structure and its abstraction -/

section Incidence

/-- **The incidence structure**: incidence records `1, …, M`; record `e` stores its parent
`src e` and its child `dst e`.  Every record is in the child list of its parent (family `C`)
and in the parent list of its child (family `P`), each doubly linked; the prev/next fields
of a record are its positions in the two lists. -/
structure Lin where
  N : ℕ
  M : ℕ
  src : ℕ → ℕ
  dst : ℕ → ℕ
  C : DL
  P : DL

/-- **Abstraction**: with ghost lists `lc g` (records of the child list of `g`) and `lp g`
(records of the parent list of `g`), the linked lists represent the child and parent lists of
the circuit `G`: mapping `dst` over `lc g` gives `G.children g`, mapping `src` over `lp g`
gives `G.parents g`, and a record is in the child list of its parent iff it is in the parent
list of its child. -/
structure AbsR (L : Lin) (G : Dag) (lc lp : ℕ → List ℕ) : Prop where
  c : DRep L.C lc L.src L.N
  p : DRep L.P lp L.dst L.N
  ch : ∀ g, (lc g).map L.dst = G.children g
  pa : ∀ g, (lp g).map L.src = G.parents g
  sync : ∀ e, e ∈ lc (L.src e) ↔ e ∈ lp (L.dst e)
  bdc : ∀ g e, e ∈ lc g → e ≤ L.M
  bdp : ∀ g e, e ∈ lp g → e ≤ L.M
  cnd : ∀ g, (G.children g).Nodup

/-- The linked structure represents `G` for some ghost lists. -/
def Abs (L : Lin) (G : Dag) : Prop := ∃ lc lp, AbsR L G lc lp

variable {L : Lin} {G : Dag} {lc lp : ℕ → List ℕ}

/-- **Readback**: following the next pointers from the heads reads back exactly the child
and parent lists of `G` (fuel `M + 1` never binds); the cost of a readback is
`3 · length + 1`. -/
theorem AbsR.readback (h : AbsR L G lc lp) {g : ℕ} (hg : g < L.N) :
    (travE L.C.nx (L.M + 1) (L.C.hd g)).1.map L.dst = G.children g ∧
    (travE L.P.nx (L.M + 1) (L.P.hd g)).1.map L.src = G.parents g ∧
    (travE L.C.nx (L.M + 1) (L.C.hd g)).1 = lc g ∧
    (travE L.P.nx (L.M + 1) (L.P.hd g)).1 = lp g := by
  have hc : (lc g).length < L.M + 1 :=
    Nat.lt_succ_of_le (length_le_of_bound _ _ (h.c.nd g) (fun x hx => ⟨h.c.pos g x hx, h.bdc g x hx⟩))
  have hp : (lp g).length < L.M + 1 :=
    Nat.lt_succ_of_le (length_le_of_bound _ _ (h.p.nd g) (fun x hx => ⟨h.p.pos g x hx, h.bdp g x hx⟩))
  have e1 := travE_eq L.C.nx L.C.pv (lc g) (L.M + 1) 0 (h.c.seg g) (h.c.pos g) hc
  have e2 := travE_eq L.P.nx L.P.pv (lp g) (L.M + 1) 0 (h.p.seg g) (h.p.pos g) hp
  rw [h.c.hd g hg, h.p.hd g hg, e1, e2]
  exact ⟨h.ch g, h.pa g, rfl, rfl⟩

lemma headD_eq_zero (l : List ℕ) (hp : ∀ x ∈ l, 0 < x) : l.headD 0 = 0 ↔ l = [] := by
  cases l with
  | nil => simp
  | cons x l => simp only [List.headD_cons, reduceCtorEq, iff_false]; exact (hp x List.mem_cons_self).ne'

/-- **The O(1) tests read the heads**: a gate has children iff the head of its child list is
not null, and has no parent iff the head of its parent list is null. -/
theorem AbsR.tests (h : AbsR L G lc lp) {g : ℕ} (hg : g < L.N) :
    (L.C.hd g ≠ 0 ↔ G.children g ≠ []) ∧ (L.P.hd g = 0 ↔ G.parents g = []) := by
  rw [h.c.hd g hg, h.p.hd g hg, ← h.ch g, ← h.pa g]
  simp only [ne_eq, headD_eq_zero _ (h.c.pos g), headD_eq_zero _ (h.p.pos g), List.map_eq_nil_iff,
    and_self, iff_self]

lemma map_erase_of_inj {l : List ℕ} (f : ℕ → ℕ) (hnd : l.Nodup) (hm : (l.map f).Nodup) (e : ℕ)
    (he : e ∈ l) : (l.erase e).map f = (l.map f).filter (fun x => decide (x ≠ f e)) := by
  rw [hnd.erase_eq_filter, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x hx
  have hinj := List.inj_on_of_nodup_map hm
  by_cases h1 : x = e
  · subst h1; simp
  · have h2 : f x ≠ f e := fun h3 => h1 (hinj hx he h3)
    simp [h1, h2]

/-- **Retirement of a live record** `e`: unlinking it from both lists represents
`retireDag G (src e) (dst e)`. -/
theorem AbsR.retire (h : AbsR L G lc lp) (hG : G.WF) {e : ℕ} (he : e ∈ lc (L.src e)) :
    AbsR ⟨L.N, L.M, L.src, L.dst, (L.C.unlink (L.src e) e).1, (L.P.unlink (L.dst e) e).1⟩
      (retireDag G (L.src e) (L.dst e))
      (Function.update lc (L.src e) ((lc (L.src e)).erase e))
      (Function.update lp (L.dst e) ((lp (L.dst e)).erase e)) := by
  have hep : e ∈ lp (L.dst e) := (h.sync e).1 he
  obtain ⟨c1, -, -⟩ := h.c.unlink he
  obtain ⟨p1, -, -⟩ := h.p.unlink hep
  refine ⟨c1, p1, fun g => ?_, fun g => ?_, fun e' => ?_, fun g x hx => ?_, fun g x hx => ?_,
    fun g => ?_⟩
  · show _ = if g = L.src e then (G.children g).filter (· ≠ L.dst e) else G.children g
    by_cases hg : g = L.src e
    · subst hg
      rw [Function.update_self, if_pos rfl, ← h.ch]
      refine map_erase_of_inj L.dst (h.c.nd _) ?_ e he
      rw [h.ch]; exact h.cnd _
    · rw [Function.update_of_ne hg, if_neg hg, h.ch]
  · show _ = if g = L.dst e then (G.parents g).filter (· ≠ L.src e) else G.parents g
    by_cases hg : g = L.dst e
    · subst hg
      rw [Function.update_self, if_pos rfl, ← h.pa]
      refine map_erase_of_inj L.src (h.p.nd _) ?_ e hep
      rw [h.pa]; exact hG.parents_nodup _
    · rw [Function.update_of_ne hg, if_neg hg, h.pa]
  · by_cases hee : e' = e
    · subst hee
      rw [Function.update_self, Function.update_self]
      exact ⟨fun h1 => absurd h1 ((h.c.nd _).not_mem_erase), fun h1 => absurd h1 ((h.p.nd _).not_mem_erase)⟩
    · have l1 : e' ∈ Function.update lc (L.src e) ((lc (L.src e)).erase e) (L.src e') ↔
          e' ∈ lc (L.src e') := by
        by_cases hs : L.src e' = L.src e
        · rw [hs, Function.update_self, List.mem_erase_of_ne hee]
        · rw [Function.update_of_ne hs]
      have l2 : e' ∈ Function.update lp (L.dst e) ((lp (L.dst e)).erase e) (L.dst e') ↔
          e' ∈ lp (L.dst e') := by
        by_cases hs : L.dst e' = L.dst e
        · rw [hs, Function.update_self, List.mem_erase_of_ne hee]
        · rw [Function.update_of_ne hs]
      rw [l1, l2]; exact h.sync e'
  · by_cases hg : g = L.src e
    · subst hg; rw [Function.update_self] at hx; exact h.bdc _ x (List.mem_of_mem_erase hx)
    · rw [Function.update_of_ne hg] at hx; exact h.bdc g x hx
  · by_cases hg : g = L.dst e
    · subst hg; rw [Function.update_self] at hx; exact h.bdp _ x (List.mem_of_mem_erase hx)
    · rw [Function.update_of_ne hg] at hx; exact h.bdp g x hx
  · show (if g = L.src e then (G.children g).filter (· ≠ L.dst e) else G.children g).Nodup
    split_ifs
    · exact (h.cnd g).filter _
    · exact h.cnd g

/-- **Release of a gate** `g`: unlinking every record of its child list from the parent
list of its child, and emptying its child list (one write of the head), represents
`releaseDag G g`; the stack receives the children of `g`. -/
theorem AbsR.release (h : AbsR L G lc lp) (hG : G.WF) (g : ℕ) (st : List ℕ) :
    AbsR ⟨L.N, L.M, L.src, L.dst, ⟨Function.update L.C.hd g 0, L.C.nx, L.C.pv⟩,
        (travU L.dst (lc g) L.P st).1⟩ (releaseDag G g)
      (Function.update lc g []) (fun c => (lp c).filter (fun x => decide (x ∉ lc g))) ∧
    (travU L.dst (lc g) L.P st).2.1 = G.children g ++ st ∧
    9 * (G.children g).length + 1 ≤ (travU L.dst (lc g) L.P st).2.2 ∧
    (travU L.dst (lc g) L.P st).2.2 ≤ 10 * (G.children g).length + 1 := by
  have hlive : ∀ e ∈ lc g, e ∈ lp (L.dst e) := by
    intro e he
    have hs : L.src e = g := h.c.own g e he
    exact (h.sync e).1 (hs ▸ he)
  obtain ⟨t1, t2, t3, t4⟩ := travU_spec L.dst L.N (lc g) L.P lp st h.p (h.c.nd g) hlive
  have hlen : (lc g).length = (G.children g).length := by rw [← h.ch g, List.length_map]
  have hmemg : ∀ c x, x ∈ lp c → (x ∈ lc g ↔ L.src x = g) := by
    intro c x hx
    constructor
    · exact h.c.own g x
    · intro hs
      have hd : L.dst x = c := h.p.own c x hx
      have := (h.sync x).2 (hd ▸ hx)
      rw [hs] at this; exact this
  refine ⟨⟨⟨fun g' hg' => ?_, fun g' => ?_, fun g' => ?_, fun g' x hx => ?_, fun g' x hx => ?_,
      fun g' hg' => ?_⟩,
    t1, fun g' => ?_, fun c => ?_, fun e => ?_, fun g' x hx => ?_, fun g' x hx => ?_,
    fun g' => ?_⟩, by rw [t2, h.ch], by rw [← hlen]; exact t3, by rw [← hlen]; exact t4⟩
  · show Function.update L.C.hd g 0 g' = _
    by_cases hg : g' = g
    · subst hg; rw [Function.update_self, Function.update_self]; rfl
    · rw [Function.update_of_ne hg, Function.update_of_ne hg]; exact h.c.hd g' hg'
  · by_cases hg : g' = g
    · subst hg; rw [Function.update_self]; trivial
    · rw [Function.update_of_ne hg]; exact h.c.seg g'
  · by_cases hg : g' = g
    · subst hg; rw [Function.update_self]; exact List.nodup_nil
    · rw [Function.update_of_ne hg]; exact h.c.nd g'
  · by_cases hg : g' = g
    · subst hg; rw [Function.update_self] at hx; exact absurd hx List.not_mem_nil
    · rw [Function.update_of_ne hg] at hx; exact h.c.own g' x hx
  · by_cases hg : g' = g
    · subst hg; rw [Function.update_self] at hx; exact absurd hx List.not_mem_nil
    · rw [Function.update_of_ne hg] at hx; exact h.c.pos g' x hx
  · by_cases hg : g' = g
    · subst hg; rw [Function.update_self]
    · rw [Function.update_of_ne hg]; exact h.c.emp g' hg'
  · show _ = if g' = g then [] else G.children g'
    by_cases hg : g' = g
    · subst hg; rw [Function.update_self, if_pos rfl]; rfl
    · rw [Function.update_of_ne hg, if_neg hg, h.ch]
  · show _ = if c ∈ G.children g then (G.parents c).filter (· ≠ g) else G.parents c
    have e1 : (lp c).filter (fun x => decide (x ∉ lc g))
        = (lp c).filter (fun x => decide (L.src x ≠ g)) := by
      apply List.filter_congr
      intro x hx
      simp only [hmemg c x hx]
    rw [e1]
    rw [show ((lp c).filter (fun x => decide (L.src x ≠ g))).map L.src
        = ((lp c).map L.src).filter (fun p => decide (p ≠ g)) by
      rw [List.filter_map]; rfl, h.pa]
    split_ifs with hc
    · rfl
    · apply List.filter_eq_self.2
      intro p hp
      simp only [ne_eq, decide_eq_true_eq]
      rintro rfl
      exact hc ((hG.parents_iff c p).1 hp)
  · by_cases hs : L.src e = g
    · rw [hs, Function.update_self]
      simp only [List.not_mem_nil, false_iff, List.mem_filter, decide_eq_true_eq, not_and,
        not_not]
      intro hx
      exact (hmemg _ e hx).2 hs
    · rw [Function.update_of_ne hs, List.mem_filter, h.sync e]
      constructor
      · intro hx
        refine ⟨hx, ?_⟩
        simp only [decide_eq_true_eq]
        intro hm
        exact hs ((hmemg _ e hx).1 hm)
      · exact fun hx => hx.1
  · by_cases hg : g' = g
    · subst hg; rw [Function.update_self] at hx; exact absurd hx List.not_mem_nil
    · rw [Function.update_of_ne hg] at hx; exact h.bdc g' x hx
  · exact h.bdp g' x (List.mem_of_mem_filter hx)
  · show (if g' = g then [] else G.children g').Nodup
    split_ifs
    · exact List.nodup_nil
    · exact h.cnd g'

end Incidence


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)

/-! ## 4. Exit tests of the inner loops -/

section Exits

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- `LiteralE7a.dlv` with its empty-list exit test charged one unit. -/
def dlvX (g : ℕ) (y : α) : List ℕ → HEState α → List ℕ → HEState α × List ℕ × ℕ
  | [], s, st => (s, st, 1)
  | p :: ps, s, st =>
    ((dlvX g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).1,
     (dlvX g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).2.1,
     (dlvOne g y p s st).2.2 + (dlvX g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).2.2)

lemma dlvX_eq (g : ℕ) (y : α) : ∀ (ps : List ℕ) (s : HEState α) (st : List ℕ),
    dlvX g y ps s st = ((dlv g y ps s st).1, (dlv g y ps s st).2.1, (dlv g y ps s st).2.2 + 1) := by
  intro ps
  induction ps with
  | nil => intro s st; rfl
  | cons p ps ih =>
    intro s st
    rw [dlvX, ih]
    show _ = ((dlv g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).1,
      (dlv g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).2.1,
      (dlvOne g y p s st).2.2 + (dlv g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).2.2 + 1)
    simp only [Prod.mk.injEq, true_and]
    omega

/-- `LiteralF4.loopDR` with the deliveries `dlvX` (exit test of each delivery loop
charged). -/
def loopDX (G : Dag) : ℕ → HEState α → List ℕ → HEState α × ℕ × List ℕ
  | 0, s, _ => (s, 0, [])
  | _ + 1, s, [] => (s, 1, [])
  | f + 1, s, g :: st =>
    ((loopDX G f (dlvX g (s.val g) (G.parents g) s st).1
        (dlvX g (s.val g) (G.parents g) s st).2.1).1,
     2 + (dlvX g (s.val g) (G.parents g) s st).2.2
       + (loopDX G f (dlvX g (s.val g) (G.parents g) s st).1
          (dlvX g (s.val g) (G.parents g) s st).2.1).2.1,
     g :: (loopDX G f (dlvX g (s.val g) (G.parents g) s st).1
          (dlvX g (s.val g) (G.parents g) s st).2.1).2.2)

lemma loopDX_eq (G : Dag) : ∀ (f : ℕ) (s : HEState α) (st : List ℕ),
    (loopDX G f s st).1 = (loopDR G f s st).1 ∧ (loopDX G f s st).2.2 = (loopDR G f s st).2.2 ∧
    (loopDR G f s st).2.1 ≤ (loopDX G f s st).2.1 ∧
    (loopDX G f s st).2.1 ≤ 2 * (loopDR G f s st).2.1 := by
  intro f
  induction f with
  | zero => intro s st; exact ⟨rfl, rfl, le_rfl, Nat.zero_le _⟩
  | succ f ih =>
    intro s st
    cases st with
    | nil => exact ⟨rfl, rfl, le_rfl, by show 1 ≤ 2 * 1; omega⟩
    | cons g st =>
      rw [loopDX, loopDR, dlvX_eq]
      obtain ⟨i1, i2, i3, i4⟩ := ih (dlv g (s.val g) (G.parents g) s st).1
        (dlv g (s.val g) (G.parents g) s st).2.1
      dsimp only
      refine ⟨i1, by rw [i2], by omega, by omega⟩

/-- `LiteralF4.waveDR` with the stack loop `loopDX`. -/
def waveDX (G : Dag) (x : ℕ) (y : α) (s : HEState α) : HEState α × ℕ × List ℕ :=
  if targetH G x y s x = s.val x then (s, 1, [])
  else ((loopDX G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).1,
    1 + (loopDX G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).2.1,
    (loopDX G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).2.2)

lemma waveDX_eq (G : Dag) (x : ℕ) (y : α) (s : HEState α) :
    (waveDX G x y s).1 = (waveDR G x y s).1 ∧ (waveDX G x y s).2.2 = (waveDR G x y s).2.2 ∧
    (waveDR G x y s).2.1 ≤ (waveDX G x y s).2.1 ∧
    (waveDX G x y s).2.1 ≤ 2 * (waveDR G x y s).2.1 := by
  unfold waveDX waveDR
  by_cases hc : targetH G x y s x = s.val x
  · rw [if_pos hc, if_pos hc]; exact ⟨rfl, rfl, le_rfl, by omega⟩
  · rw [if_neg hc, if_neg hc]
    obtain ⟨i1, i2, i3, i4⟩ := loopDX_eq G (G.N + 2)
      ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]
    exact ⟨i1, i2, by dsimp only; omega, by dsimp only; omega⟩

/-- Mark writes with the exit test charged. -/
def setMarksX : List ℕ → (ℕ → Bool) → (ℕ → Bool) × ℕ
  | [], m => (m, 1)
  | g :: l, m => ((setMarksX l (Function.update m g true)).1,
      (setMarksX l (Function.update m g true)).2 + 1)

def clearMarksX : List ℕ → (ℕ → Bool) → (ℕ → Bool) × ℕ
  | [], m => (m, 1)
  | g :: l, m => ((clearMarksX l (Function.update m g false)).1,
      (clearMarksX l (Function.update m g false)).2 + 1)

def filterUnmarkedX (m : ℕ → Bool) : List ℕ → List ℕ × ℕ
  | [] => ([], 1)
  | g :: l => (if m g then (filterUnmarkedX m l).1 else g :: (filterUnmarkedX m l).1,
      (filterUnmarkedX m l).2 + 1)

lemma setMarksX_eq : ∀ (l : List ℕ) (m : ℕ → Bool),
    setMarksX l m = ((setMarks l m).1, (setMarks l m).2 + 1) := by
  intro l; induction l with
  | nil => intro m; rfl
  | cons g l ih => intro m; rw [setMarksX, ih]; rfl

lemma clearMarksX_eq : ∀ (l : List ℕ) (m : ℕ → Bool),
    clearMarksX l m = ((clearMarks l m).1, (clearMarks l m).2 + 1) := by
  intro l; induction l with
  | nil => intro m; rfl
  | cons g l ih => intro m; rw [clearMarksX, ih]; rfl

lemma filterUnmarkedX_eq (m : ℕ → Bool) : ∀ (l : List ℕ),
    filterUnmarkedX m l = ((filterUnmarked m l).1, (filterUnmarked m l).2 + 1) := by
  intro l; induction l with
  | nil => rfl
  | cons g l ih => rw [filterUnmarkedX, ih]; rfl

/-- `LiteralG2.mergeM` with the three exit tests charged. -/
def mergeMX (mk : ℕ → Bool) (rl rh : List ℕ) : List ℕ × (ℕ → Bool) × ℕ :=
  (rl ++ (filterUnmarkedX (setMarksX rl mk).1 rh).1,
   (clearMarksX rl (setMarksX rl mk).1).1,
   (setMarksX rl mk).2 + (filterUnmarkedX (setMarksX rl mk).1 rh).2
     + (clearMarksX rl (setMarksX rl mk).1).2)

lemma mergeMX_eq (mk : ℕ → Bool) (rl rh : List ℕ) :
    (mergeMX mk rl rh).1 = (mergeM mk rl rh).1 ∧ (mergeMX mk rl rh).2.1 = (mergeM mk rl rh).2.1 ∧
    (mergeMX mk rl rh).2.2 = (mergeM mk rl rh).2.2 + 3 := by
  unfold mergeMX mergeM
  rw [setMarksX_eq, filterUnmarkedX_eq, clearMarksX_eq]
  exact ⟨rfl, rfl, by dsimp only; omega⟩

def incAllX : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) × ℕ
  | [], c => (c, 1)
  | g :: l, c => ((incAllX l (Function.update c g (c g + 1))).1,
      (incAllX l (Function.update c g (c g + 1))).2 + 1)

def decAllX : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) × ℕ
  | [], c => (c, 1)
  | g :: l, c => ((decAllX l (Function.update c g (c g - 1))).1,
      (decAllX l (Function.update c g (c g - 1))).2 + 1)

def zeroAllX : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) × ℕ
  | [], c => (c, 1)
  | g :: l, c => ((zeroAllX l (Function.update c g 0)).1,
      (zeroAllX l (Function.update c g 0)).2 + 1)

lemma incAllX_eq : ∀ (l : List ℕ) (c : ℕ → ℕ), incAllX l c = ((incAll l c).1, (incAll l c).2 + 1) := by
  intro l; induction l with
  | nil => intro c; rfl
  | cons g l ih => intro c; rw [incAllX, ih]; rfl

lemma decAllX_eq : ∀ (l : List ℕ) (c : ℕ → ℕ), decAllX l c = ((decAll l c).1, (decAll l c).2 + 1) := by
  intro l; induction l with
  | nil => intro c; rfl
  | cons g l ih => intro c; rw [decAllX, ih]; rfl

lemma zeroAllX_eq : ∀ (l : List ℕ) (c : ℕ → ℕ), zeroAllX l c = ((zeroAll l c).1, (zeroAll l c).2 + 1) := by
  intro l; induction l with
  | nil => intro c; rfl
  | cons g l ih => intro c; rw [zeroAllX, ih]; rfl

end Exits

/-! ## 5. The root scans as executed loops -/

section ScansX

variable {α : Type*} [LinearOrder α]

/-- **Executed leader scan** over the root indices `0, …, n-1`: per index, read the flag,
read the root gate and its value, read the leader's gate and value, compare (6 units); 1 for
the exit test. -/
def leadScanX (L : ℕ → α) (act : ℕ → Bool) : ℕ → Option ℕ × ℕ
  | 0 => (none, 1)
  | n + 1 =>
    ((leadScanX L act n).1.elim (if act n = true then some n else none)
        (fun a => if act n = true ∧ L a < L n then some n else some a),
     (leadScanX L act n).2 + 6)

lemma leadScanX_spec (L : ℕ → α) (act : ℕ → Bool) :
    ∀ n, leadScanX L act n = (leadScan L act n, 6 * n + 1)
  | 0 => rfl
  | n + 1 => by
    rw [leadScanX, leadScanX_spec L act n]
    simp only [Prod.mk.injEq]
    exact ⟨rfl, by ring⟩

/-- **Executed stop scan**: per index, read the flag, compare with the leader, read the gate
and its value, evaluate and compare the gap (6 units); 1 for the exit test. -/
noncomputable def stopScanX (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ)
    (act : ℕ → Bool) : ℕ → Bool × ℕ
  | 0 => (true, 1)
  | n + 1 =>
    ((stopScanX φ ε U la a act n).1
        && (!(act n) || decide (n = a) || decide (φ (U n) - φ la ≤ ε)),
     (stopScanX φ ε U la a act n).2 + 6)

omit [LinearOrder α] in
lemma stopScanX_spec (φ : α → ℝ) (ε : ℝ) (U : ℕ → α) (la : α) (a : ℕ) (act : ℕ → Bool) :
    ∀ n, stopScanX φ ε U la a act n = (stopScan φ ε U la a act n, 6 * n + 1)
  | 0 => rfl
  | n + 1 => by
    rw [stopScanX, stopScanX_spec φ ε U la a act n]
    simp only [Prod.mk.injEq]
    exact ⟨rfl, by ring⟩

/-- **Executed retirement scan**: per index, read the flag, compare with the leader, read the
gate and its upper value, compare with the leader's lower value, and if retired clear the
flag and append the gate to the output (7 units); 1 for the exit test.  Returns the new
flags, the retired gates and the cost. -/
def retScanX (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) :
    ℕ → (ℕ → Bool) × List ℕ × ℕ
  | 0 => (act, [], 1)
  | n + 1 =>
    if (retScanX rt a U la act n).1 n = true ∧ n ≠ a ∧ U n < la then
      (Function.update (retScanX rt a U la act n).1 n false,
       (retScanX rt a U la act n).2.1 ++ [rt n], (retScanX rt a U la act n).2.2 + 7)
    else ((retScanX rt a U la act n).1, (retScanX rt a U la act n).2.1,
      (retScanX rt a U la act n).2.2 + 7)

lemma retScanX_spec (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) :
    ∀ n, (∀ i, (retScanX rt a U la act n).1 i
        = (act i && !(decide (i < n) && decide (i ≠ a) && decide (U i < la)))) ∧
      (retScanX rt a U la act n).2.1 = retiredRoots n rt a U la act ∧
      (retScanX rt a U la act n).2.2 = 7 * n + 1 := by
  intro n
  induction n with
  | zero => exact ⟨fun i => by simp [retScanX], by simp [retScanX, retiredRoots], rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hn : (retScanX rt a U la act n).1 n = act n := by rw [h1 n]; simp
    have hr : retiredRoots (n + 1) rt a U la act = retiredRoots n rt a U la act
        ++ (if act n = true ∧ n ≠ a ∧ U n < la then [rt n] else []) := by
      unfold retiredRoots
      rw [List.range_succ, List.filter_append, List.map_append]
      by_cases h : act n = true ∧ n ≠ a ∧ U n < la <;> simp [h]
    rw [retScanX]
    by_cases hc : (retScanX rt a U la act n).1 n = true ∧ n ≠ a ∧ U n < la
    · rw [if_pos hc]
      have hc' : act n = true ∧ n ≠ a ∧ U n < la := by rw [← hn]; exact hc
      refine ⟨fun i => ?_, by rw [hr, if_pos hc', h2], by dsimp only; rw [h3]; ring⟩
      dsimp only
      by_cases hi : i = n
      · subst hi
        rw [Function.update_self]
        simp [hc'.1, hc'.2.1, hc'.2.2]
      · rw [Function.update_of_ne hi, h1 i]
        have : (i < n + 1) ↔ (i < n) := by omega
        simp [this]
    · rw [if_neg hc]
      have hc' : ¬ (act n = true ∧ n ≠ a ∧ U n < la) := by rw [← hn]; exact hc
      refine ⟨fun i => ?_, by rw [hr, if_neg hc', h2, List.append_nil], by dsimp only; rw [h3]; ring⟩
      dsimp only
      rw [h1 i]
      by_cases hi : i = n
      · subst hi
        have : ¬ (act i = true ∧ i ≠ a ∧ U i < la) := hc'
        by_cases ha : act i = true
        · by_cases hia : i = a
          · simp [hia]
          · have : ¬ U i < la := fun h => this ⟨ha, hia, h⟩
            simp [ha, hia, this]
        · simp [ha]
      · have : (i < n + 1) ↔ (i < n) := by omega
        simp [this]

lemma retScanX_deact (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) (K : ℕ) :
    (retScanX rt a U la act K).1 = deact K a U la act := by
  funext i
  rw [(retScanX_spec rt a U la act K).1 i]
  rfl

end ScansX


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)

/-! ## 6. Retirement, release and candidate construction on the linked structure -/

section LinkedOps

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The fixed fields of the incidence structure (number of records, `src`, `dst`). -/
def Stat (L L' : Lin) : Prop := L'.N = L.N ∧ L'.M = L.M ∧ L'.src = L.src ∧ L'.dst = L.dst

lemma Stat.refl (L : Lin) : Stat L L := ⟨rfl, rfl, rfl, rfl⟩

lemma Stat.trans {L1 L2 L3 : Lin} (h1 : Stat L1 L2) (h2 : Stat L2 L3) : Stat L1 L3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- **Retirement of one candidate record** `e`: read its parent and child (2), compare
`hi c < lo p` (1); if it holds, the two heap deletions (computed cost) and the two unlinks
(executed, 5 or 6 accesses each). -/
def retireOneL (e : ℕ) (x : HRState α × Lin) : (HRState α × Lin) × ℕ :=
  if x.1.hi.val (x.2.dst e) < x.1.lo.val (x.2.src e) then
    ((⟨retireDag x.1.G (x.2.src e) (x.2.dst e),
        ⟨x.1.lo.val, Function.update x.1.lo.hp (x.2.src e)
          (HeapImpl.delete (x.1.lo.hp (x.2.src e)) (x.2.dst e)).1⟩,
        ⟨x.1.hi.val, Function.update x.1.hi.hp (x.2.src e)
          (HeapImpl.delete (x.1.hi.hp (x.2.src e)) (x.2.dst e)).1⟩⟩,
      ⟨x.2.N, x.2.M, x.2.src, x.2.dst, (x.2.C.unlink (x.2.src e) e).1, (x.2.P.unlink (x.2.dst e) e).1⟩),
     3 + (HeapImpl.delete (x.1.lo.hp (x.2.src e)) (x.2.dst e)).2
       + (HeapImpl.delete (x.1.hi.hp (x.2.src e)) (x.2.dst e)).2
       + (x.2.C.unlink (x.2.src e) e).2 + (x.2.P.unlink (x.2.dst e) e).2)
  else (x, 3)

/-- The retirement pass over a list of candidate records; 1 for the exit test. -/
def retireListL : List ℕ → HRState α × Lin → (HRState α × Lin) × ℕ
  | [], x => (x, 1)
  | e :: es, x =>
    ((retireListL es (retireOneL e x).1).1, (retireOneL e x).2 + (retireListL es (retireOneL e x).1).2)

/-- The pair of a record. -/
def pr (L : Lin) (e : ℕ) : ℕ × ℕ := (L.src e, L.dst e)

omit [OrderBot α] in
lemma retireOneL_stat (e : ℕ) (x : HRState α × Lin) : Stat x.2 (retireOneL e x).1.2 := by
  unfold retireOneL; split_ifs
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact Stat.refl _

/-- **The retirement pass on the linked structure**: on duplicate-free live candidate
records it computes the state of `LiteralG2.retireListG` on their pairs, keeps the
abstraction, and costs between `retireListG + 1` and `6 · retireListG + 1`. -/
theorem retireListL_spec : ∀ (ids : List ℕ) (x : HRState α × Lin) (lc lp : ℕ → List ℕ),
    AbsR x.2 x.1.G lc lp → x.1.G.WF → ids.Nodup → (∀ e ∈ ids, e ∈ lc (x.2.src e)) →
    (retireListL ids x).1.1 = (retireListG (ids.map (pr x.2)) x.1).1 ∧
    Abs (retireListL ids x).1.2 (retireListL ids x).1.1.G ∧ Stat x.2 (retireListL ids x).1.2 ∧
    (retireListG (ids.map (pr x.2)) x.1).2 + 1 ≤ (retireListL ids x).2 ∧
    (retireListL ids x).2 ≤ 6 * (retireListG (ids.map (pr x.2)) x.1).2 + 1 := by
  intro ids
  induction ids with
  | nil => intro x lc lp h _ _ _; exact ⟨rfl, ⟨lc, lp, h⟩, Stat.refl _, le_rfl, by simp [retireListL, retireListG]⟩
  | cons e es ih =>
    intro x lc lp h hG hnd hl
    obtain ⟨hne, hnd'⟩ := List.nodup_cons.1 hnd
    have he := hl e List.mem_cons_self
    -- the step on `e`
    have step : ∃ lc' lp', AbsR (retireOneL e x).1.2 (retireOneL e x).1.1.G lc' lp' ∧
        (retireOneL e x).1.1.G.WF ∧ (∀ e' ∈ es, e' ∈ lc' ((retireOneL e x).1.2.src e')) ∧
        (retireOneL e x).1.1 = (retireOneG (pr x.2 e) x.1).1 ∧
        (retireOneG (pr x.2 e) x.1).2 ≤ (retireOneL e x).2 ∧
        (retireOneL e x).2 ≤ 6 * (retireOneG (pr x.2 e) x.1).2 := by
      unfold retireOneL retireOneG pr
      by_cases hc : x.1.hi.val (x.2.dst e) < x.1.lo.val (x.2.src e)
      · rw [if_pos hc, if_pos hc]
        obtain ⟨-, u1, u2⟩ := h.c.unlink he
        obtain ⟨-, v1, v2⟩ := h.p.unlink ((h.sync e).1 he)
        refine ⟨_, _, h.retire hG he, retireDag_wf hG _ _, fun e' he' => ?_, rfl, ?_, ?_⟩
        · have hee : e' ≠ e := fun h' => hne (h' ▸ he')
          show e' ∈ Function.update lc (x.2.src e) ((lc (x.2.src e)).erase e) (x.2.src e')
          by_cases hs : x.2.src e' = x.2.src e
          · rw [hs, Function.update_self]
            exact (List.mem_erase_of_ne hee).2 (hs ▸ hl e' (List.mem_cons_of_mem _ he'))
          · rw [Function.update_of_ne hs]; exact hl e' (List.mem_cons_of_mem _ he')
        · dsimp only; omega
        · dsimp only; omega
      · rw [if_neg hc, if_neg hc]
        exact ⟨lc, lp, h, hG, fun e' he' => hl e' (List.mem_cons_of_mem _ he'), rfl, by omega,
          by omega⟩
    obtain ⟨lc', lp', h', hG', hl', e1, c1, c2⟩ := step
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih (retireOneL e x).1 lc' lp' h' hG' hnd' hl'
    have hst := retireOneL_stat e x
    have hmap : es.map (pr (retireOneL e x).1.2) = es.map (pr x.2) := by
      unfold pr; rw [hst.2.2.1, hst.2.2.2]
    rw [hmap, e1] at i1 i4 i5
    refine ⟨?_, i2, hst.trans i3, ?_, ?_⟩
    · show (retireListL es (retireOneL e x).1).1.1 = (retireListG (pr x.2 e :: es.map (pr x.2)) x.1).1
      rw [i1]; rfl
    · show _ ≤ (retireOneL e x).2 + (retireListL es (retireOneL e x).1).2
      have : (retireListG (pr x.2 e :: es.map (pr x.2)) x.1).2 = (retireOneG (pr x.2 e) x.1).2
          + (retireListG (es.map (pr x.2)) (retireOneG (pr x.2 e) x.1).1).2 := rfl
      rw [List.map_cons, this]; omega
    · show (retireOneL e x).2 + (retireListL es (retireOneL e x).1).2 ≤ _
      have : (retireListG (pr x.2 e :: es.map (pr x.2)) x.1).2 = (retireOneG (pr x.2 e) x.1).2
          + (retireListG (es.map (pr x.2)) (retireOneG (pr x.2 e) x.1).1).2 := rfl
      rw [List.map_cons, this]; omega

/-- **Release of one gate** `g` on the linked structure: traverse its child list by the next
pointers, unlinking each record from the parent list of its child and pushing the child
(`relTrav`); write the null head of its child list (1) and empty its two heaps (2), plus the
3 units of the test.  Returns the state, the new stack and the cost. -/
def relGate (g : ℕ) (st : List ℕ) (x : HRState α × Lin) : (HRState α × Lin) × List ℕ × ℕ :=
  ((⟨releaseDag x.1.G g, ⟨x.1.lo.val, Function.update x.1.lo.hp g Heap.empty⟩,
      ⟨x.1.hi.val, Function.update x.1.hi.hp g Heap.empty⟩⟩,
    ⟨x.2.N, x.2.M, x.2.src, x.2.dst, ⟨Function.update x.2.C.hd g 0, x.2.C.nx, x.2.C.pv⟩,
      (relTrav x.2.C.nx x.2.dst (x.2.M + 1) (x.2.C.hd g) x.2.P st).1⟩),
   (relTrav x.2.C.nx x.2.dst (x.2.M + 1) (x.2.C.hd g) x.2.P st).2.1,
   (relTrav x.2.C.nx x.2.dst (x.2.M + 1) (x.2.C.hd g) x.2.P st).2.2 + 6)

theorem relGate_spec (g : ℕ) (st : List ℕ) (x : HRState α × Lin) {lc lp : ℕ → List ℕ}
    (h : AbsR x.2 x.1.G lc lp) (hG : x.1.G.WF) (hg : g < x.2.N) :
    Abs (relGate g st x).1.2 (relGate g st x).1.1.G ∧ Stat x.2 (relGate g st x).1.2 ∧
    (relGate g st x).1.1.G.WF ∧
    (relGate g st x).2.1 = x.1.G.children g ++ st ∧
    9 * (x.1.G.children g).length + 7 ≤ (relGate g st x).2.2 ∧
    (relGate g st x).2.2 ≤ 10 * (x.1.G.children g).length + 7 := by
  have hlen : (lc g).length < x.2.M + 1 :=
    Nat.lt_succ_of_le (length_le_of_bound _ _ (h.c.nd g) (fun y hy => ⟨h.c.pos g y hy, h.bdc g y hy⟩))
  have et : relTrav x.2.C.nx x.2.dst (x.2.M + 1) (x.2.C.hd g) x.2.P st
      = travU x.2.dst (lc g) x.2.P st := by
    rw [h.c.hd g hg]; exact relTrav_eq _ _ _ _ _ _ _ _ (h.c.seg g) (h.c.pos g) hlen
  obtain ⟨r1, r2, r3, r4⟩ := h.release hG g st
  unfold relGate
  rw [et]
  exact ⟨⟨_, _, r1⟩, ⟨rfl, rfl, rfl, rfl⟩, releaseDag_wf hG g, r2, by dsimp only; omega,
    by dsimp only; omega⟩

/-- **The release cascade on the linked structure**: the test compares the gate with `N`,
reads the head of its child list, the head of its parent list and its protection (4 units); a released gate is handled
by `relGate`; 1 for the final empty-stack test. -/
def releaseLoopL (prot : ℕ → Bool) : ℕ → List ℕ → HRState α × Lin → (HRState α × Lin) × ℕ
  | 0, _, x => (x, 0)
  | _ + 1, [], x => (x, 1)
  | f + 1, g :: st, x =>
    if g < x.2.N ∧ x.2.C.hd g ≠ 0 ∧ x.2.P.hd g = 0 ∧ prot g = false then
      ((releaseLoopL prot f (relGate g st x).2.1 (relGate g st x).1).1,
       (releaseLoopL prot f (relGate g st x).2.1 (relGate g st x).1).2 + 4 + (relGate g st x).2.2)
    else ((releaseLoopL prot f st x).1, (releaseLoopL prot f st x).2 + 4)

/-- **The cascade on the linked structure computes `LiteralG2.releaseLoopG`** (same fuel,
same protection function), keeps the abstraction, and costs between `releaseLoopG` and
`11 · releaseLoopG`. -/
theorem releaseLoopL_spec (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (x : HRState α × Lin),
    Abs x.2 x.1.G → x.1.G.WF →
    (releaseLoopL prot f st x).1.1 = (releaseLoopG prot f st x.1).1 ∧
    Abs (releaseLoopL prot f st x).1.2 (releaseLoopL prot f st x).1.1.G ∧
    Stat x.2 (releaseLoopL prot f st x).1.2 ∧
    (releaseLoopG prot f st x.1).2 ≤ (releaseLoopL prot f st x).2 ∧
    (releaseLoopL prot f st x).2 ≤ 11 * (releaseLoopG prot f st x.1).2 := by
  intro f
  induction f with
  | zero => intro st x h _; exact ⟨rfl, h, Stat.refl _, le_rfl, by simp [releaseLoopL]⟩
  | succ f ih =>
    intro st x h hG
    cases st with
    | nil => exact ⟨rfl, h, Stat.refl _, le_rfl, by simp [releaseLoopL, releaseLoopG]⟩
    | cons g st =>
      obtain ⟨lc, lp, hr⟩ := h
      have hiff : (g < x.2.N ∧ x.2.C.hd g ≠ 0 ∧ x.2.P.hd g = 0 ∧ prot g = false) ↔
          (x.1.G.children g ≠ [] ∧ x.1.G.parents g = [] ∧ prot g = false) := by
        by_cases hgN : g < x.2.N
        · obtain ⟨t1, t2⟩ := hr.tests hgN
          rw [t1, t2]; exact ⟨fun h => h.2, fun h => ⟨hgN, h⟩⟩
        · refine ⟨fun h => absurd h.1 hgN, fun h => ?_⟩
          exfalso
          obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ h.1
          have hlc : c ∈ (lc g).map x.2.dst := by rw [hr.ch g]; exact hcm
          rw [hr.c.emp g (by omega)] at hlc
          exact List.not_mem_nil hlc
      rw [releaseLoopL, releaseLoopG]
      by_cases hc : g < x.2.N ∧ x.2.C.hd g ≠ 0 ∧ x.2.P.hd g = 0 ∧ prot g = false
      · rw [if_pos hc, if_pos (hiff.1 hc)]
        obtain ⟨g1, g2, g3, g4, g5, g6⟩ := relGate_spec g st x hr hG hc.1
        obtain ⟨i1, i2, i3, i4, i5⟩ := ih (relGate g st x).2.1 (relGate g st x).1 g1 g3
        rw [g4] at i1 i4 i5
        have hx1 : (relGate g st x).1.1 = ⟨releaseDag x.1.G g,
            ⟨x.1.lo.val, Function.update x.1.lo.hp g Heap.empty⟩,
            ⟨x.1.hi.val, Function.update x.1.hi.hp g Heap.empty⟩⟩ := rfl
        rw [hx1] at i1 i4 i5
        rw [g4] at i2 i3 ⊢
        refine ⟨i1, i2, g2.trans i3, by dsimp only; omega, by dsimp only; omega⟩
      · rw [if_neg hc, if_neg (fun h' => hc (hiff.2 h'))]
        obtain ⟨i1, i2, i3, i4, i5⟩ := ih st x ⟨lc, lp, hr⟩ hG
        exact ⟨i1, i2, i3, by dsimp only; omega, by dsimp only; omega⟩

/-- **Final disposal on the linked structure**: release every gate of the list (`relGate`);
1 for the exit test. -/
def disposeL : List ℕ → HRState α × Lin → (HRState α × Lin) × ℕ
  | [], x => (x, 1)
  | g :: gs, x => ((disposeL gs (relGate g [] x).1).1, (relGate g [] x).2.2 + (disposeL gs (relGate g [] x).1).2)

theorem disposeL_spec : ∀ (gs : List ℕ) (x : HRState α × Lin), Abs x.2 x.1.G → x.1.G.WF →
    (∀ g ∈ gs, g < x.2.N) →
    (disposeL gs x).1.1.G = (disposeAll gs x.1.G).1 ∧
    (disposeAll gs x.1.G).2 ≤ (disposeL gs x).2 ∧
    (disposeL gs x).2 ≤ 10 * (disposeAll gs x.1.G).2 + 1 := by
  intro gs
  induction gs with
  | nil => intro x _ _ _; exact ⟨rfl, Nat.zero_le _, le_rfl⟩
  | cons g gs ih =>
    intro x h hG hgs
    obtain ⟨lc, lp, hr⟩ := h
    obtain ⟨g1, g2, g3, -, g5, g6⟩ := relGate_spec g [] x hr hG (hgs g List.mem_cons_self)
    obtain ⟨i1, i2, i3⟩ := ih (relGate g [] x).1 g1 g3
      (fun g' hg' => g2.1 ▸ hgs g' (List.mem_cons_of_mem _ hg'))
    have hx1 : (relGate g [] x).1.1.G = releaseDag x.1.G g := rfl
    rw [hx1] at i1 i2 i3
    refine ⟨i1, ?_, ?_⟩
    · show (disposeAll gs (releaseDag x.1.G g)).2 + 1 + (x.1.G.children g).length ≤
        (relGate g [] x).2.2 + (disposeL gs (relGate g [] x).1).2
      omega
    · show (relGate g [] x).2.2 + (disposeL gs (relGate g [] x).1).2 ≤
        10 * ((disposeAll gs (releaseDag x.1.G g)).2 + 1 + (x.1.G.children g).length) + 1
      omega

/-- **Candidate construction on the linked structure**: for each merged gate (1 unit),
compare it with `N` and traverse its parent list by the next pointers emitting the records (`travE`, 3 per record and
1 for the null test); 1 for the exit test. -/
def pTrav (L : Lin) (g : ℕ) : List ℕ × ℕ :=
  if g < L.N then travE L.P.nx (L.M + 1) (L.P.hd g) else ([], 1)

def candTrav (L : Lin) : List ℕ → List ℕ × ℕ
  | [] => ([], 1)
  | g :: gs => ((pTrav L g).1 ++ (candTrav L gs).1, 1 + (pTrav L g).2 + (candTrav L gs).2)

theorem candTrav_spec {L : Lin} {G : Dag} {lc lp : ℕ → List ℕ} (h : AbsR L G lc lp) :
    ∀ m : List ℕ, (candTrav L m).1 = m.flatMap lp ∧
      (candTrav L m).1.map (pr L) = (buildCand G m).1 ∧
      (∀ e ∈ (candTrav L m).1, e ∈ lc (L.src e)) ∧
      (buildCand G m).2 ≤ (candTrav L m).2 ∧ (candTrav L m).2 ≤ 3 * (buildCand G m).2 + 1 := by
  intro m
  induction m with
  | nil => exact ⟨rfl, rfl, fun e he => absurd he List.not_mem_nil, Nat.zero_le _, le_rfl⟩
  | cons g gs ih =>
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    have et : pTrav L g = (lp g, 3 * (lp g).length + 1) := by
      unfold pTrav
      by_cases hgN : g < L.N
      · rw [if_pos hgN, h.p.hd g hgN]
        have hlen : (lp g).length < L.M + 1 :=
          Nat.lt_succ_of_le (length_le_of_bound _ _ (h.p.nd g)
            (fun y hy => ⟨h.p.pos g y hy, h.bdp g y hy⟩))
        exact travE_eq _ _ _ _ _ (h.p.seg g) (h.p.pos g) hlen
      · rw [if_neg hgN, h.p.emp g (by omega)]; rfl
    have hpg : (lp g).map (pr L) = (G.parents g).map (fun p => (p, g)) := by
      rw [← h.pa g, List.map_map]
      apply List.map_congr_left
      intro e he
      simp only [pr, Function.comp, h.p.own g e he]
    have hb : (buildCand G (g :: gs)).1 = (G.parents g).map (fun p => (p, g)) ++ (buildCand G gs).1 := by
      simp [buildCand, List.flatMap_cons]
    have hb2 : (buildCand G (g :: gs)).2 = (gs.length + 1) + ((G.parents g).length
        + (buildCand G gs).1.length) := by
      show (g :: gs).length + (buildCand G (g :: gs)).1.length = _
      rw [hb, List.length_append, List.length_map, List.length_cons]
    have hb3 : (buildCand G gs).2 = gs.length + (buildCand G gs).1.length := rfl
    have hlp : (lp g).length = (G.parents g).length := by rw [← h.pa g, List.length_map]
    have hc1 : (candTrav L (g :: gs)).1 = lp g ++ (candTrav L gs).1 := by
      show (pTrav L g).1 ++ (candTrav L gs).1 = _; rw [et]
    have hc2 : (candTrav L (g :: gs)).2 = 1 + (3 * (lp g).length + 1) + (candTrav L gs).2 := by
      show 1 + (pTrav L g).2 + (candTrav L gs).2 = _; rw [et]
    have hcl : (candTrav L gs).1.length = (buildCand G gs).1.length := by
      rw [← i2, List.length_map]
    refine ⟨by rw [hc1, i1, List.flatMap_cons], by rw [hc1, List.map_append, hpg, i2, hb], ?_, ?_, ?_⟩
    · intro e he
      rw [hc1] at he
      rcases List.mem_append.1 he with he | he
      · have hd : L.dst e = g := h.p.own g e he
        exact (h.sync e).2 (hd ▸ he)
      · exact i3 e he
    · rw [hb2, hc2, hlp]; omega
    · rw [hb2, hc2, hlp]
      have : (candTrav L gs).2 ≤ 3 * (gs.length + (buildCand G gs).1.length) + 1 := hb3 ▸ i5
      omega

/-- The stack of the cascade: the child of each candidate record (read `dst`, push: 1 unit
per record; 1 for the exit test). -/
def dstAll (L : Lin) : List ℕ → List ℕ × ℕ
  | [] => ([], 1)
  | e :: es => (L.dst e :: (dstAll L es).1, (dstAll L es).2 + 1)

lemma dstAll_spec (L : Lin) : ∀ ids : List ℕ,
    (dstAll L ids).1 = (ids.map (pr L)).map Prod.snd ∧ (dstAll L ids).2 = ids.length + 1 := by
  intro ids
  induction ids with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
    refine ⟨?_, ?_⟩
    · show L.dst e :: (dstAll L es).1 = _; rw [ih.1]; rfl
    · show (dstAll L es).2 + 1 = _; rw [ih.2, List.length_cons]

end LinkedOps


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)

/-! ## 7. One rollout and one query of the linked engine -/

section Steps

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **One rollout of the linked engine**: the two recording waves (`waveDX`), the merge
(`mergeMX`), the candidate records read from the linked parent lists (`candTrav`), the
retirement pass (`retireListL`), the stack of the cascade (`dstAll`) and the cascade
(`releaseLoopL`, fuel as in `LiteralG2`, proved not to bind there). -/
def relStepL (prot : ℕ → Bool) (u : ℕ × α × α) (s : GS α) (L : Lin) : (GS α × Lin) × ℕ :=
  let wl := waveDX s.q.r.G u.1 u.2.1 s.q.r.lo
  let wh := waveDX s.q.r.G u.1 u.2.2 s.q.r.hi
  let mg := mergeMX s.marks wl.2.2 wh.2.2
  let ct := candTrav L mg.1
  let rl := retireListL ct.1 (⟨s.q.r.G, wl.1, wh.1⟩, L)
  let sk := dstAll L ct.1
  let cs := releaseLoopL prot (relFuel rl.1.1.G sk.1) sk.1 rl.1
  ((⟨⟨cs.1.1, s.q.act⟩, mg.2.1⟩, cs.1.2), wl.2.1 + wh.2.1 + mg.2.2 + ct.2 + rl.2 + sk.2 + cs.2)

/-- **One rollout of the linked engine against `LiteralG2.relStepP`** (same protection
function): same engine state, the abstraction is kept, and the cost is between that of
`relStepP` and `11 · relStepP + 6`.  Hypotheses: the linked structure represents the circuit,
which is well formed, and the candidate list of `LiteralG2` is duplicate-free (`stepG`). -/
theorem relStepL_eq (prot : ℕ → Bool) (u : ℕ × α × α) (s : GS α) (L : Lin)
    {lc lp : ℕ → List ℕ} (h : AbsR L s.q.r.G lc lp) (hG : s.q.r.G.WF) (hnd : (candG u s).Nodup) :
    (relStepL prot u s L).1.1 = (relStepP prot u s).1 ∧
    Abs (relStepL prot u s L).1.2 (relStepP prot u s).1.q.r.G ∧ Stat L (relStepL prot u s L).1.2 ∧
    (relStepP prot u s).2 ≤ (relStepL prot u s L).2 ∧
    (relStepL prot u s L).2 ≤ 11 * (relStepP prot u s).2 + 6 := by
  obtain ⟨wl1, wl2, wl3, wl4⟩ := waveDX_eq s.q.r.G u.1 u.2.1 s.q.r.lo
  obtain ⟨wh1, wh2, wh3, wh4⟩ := waveDX_eq s.q.r.G u.1 u.2.2 s.q.r.hi
  obtain ⟨mg1, mg2, mg3⟩ := mergeMX_eq s.marks (waveDX s.q.r.G u.1 u.2.1 s.q.r.lo).2.2
    (waveDX s.q.r.G u.1 u.2.2 s.q.r.hi).2.2
  have hm : (mergeMX s.marks (waveDX s.q.r.G u.1 u.2.1 s.q.r.lo).2.2
      (waveDX s.q.r.G u.1 u.2.2 s.q.r.hi).2.2).1 = (mergeG u s).1 := by
    rw [mg1, wl2, wh2]; rfl
  have hm2 : (mergeMX s.marks (waveDX s.q.r.G u.1 u.2.1 s.q.r.lo).2.2
      (waveDX s.q.r.G u.1 u.2.2 s.q.r.hi).2.2).2.1 = (mergeG u s).2.1 := by
    rw [mg2, wl2, wh2]; rfl
  have hm3 : (mergeMX s.marks (waveDX s.q.r.G u.1 u.2.1 s.q.r.lo).2.2
      (waveDX s.q.r.G u.1 u.2.2 s.q.r.hi).2.2).2.2 = (mergeG u s).2.2 + 3 := by
    rw [mg3, wl2, wh2]; rfl
  have hw : (⟨s.q.r.G, (waveDX s.q.r.G u.1 u.2.1 s.q.r.lo).1,
      (waveDX s.q.r.G u.1 u.2.2 s.q.r.hi).1⟩ : HRState α) = wR u s.q.r := by
    rw [wl1, wh1]; rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := candTrav_spec h (mergeG u s).1
  set ids := (candTrav L (mergeG u s).1).1 with hids
  have hcand : ids.map (pr L) = candG u s := c2
  have hnd' : ids.Nodup := by rw [← hcand] at hnd; exact hnd.of_map _
  have hw' : (wR u s.q.r).G = s.q.r.G := rfl
  obtain ⟨r1, r2, r3, r4, r5⟩ := retireListL_spec ids (wR u s.q.r, L) lc lp (by exact h) hG hnd' c3
  simp only at r1 r2 r3 r4 r5
  rw [hcand] at r1 r4 r5
  obtain ⟨d1, d2⟩ := dstAll_spec L ids
  rw [hcand] at d1
  obtain ⟨gw1, -⟩ := retireListG_G (candG u s) (wR u s.q.r) hG
  obtain ⟨l1, l2, l3, l4, l5⟩ := releaseLoopL_spec prot
    (relFuel (retireListG (candG u s) (wR u s.q.r)).1.G ((candG u s).map Prod.snd))
    ((candG u s).map Prod.snd) (retireListL ids (wR u s.q.r, L)).1 (by rw [r1] at r2; rw [r1]; exact r2)
    (by rw [r1]; exact gw1)
  rw [r1] at l1 l4 l5
  have hbc : (buildCand s.q.r.G (mergeG u s).1).1.length ≤ (buildCand s.q.r.G (mergeG u s).1).2 := by
    have : (buildCand s.q.r.G (mergeG u s).1).2
        = (mergeG u s).1.length + (buildCand s.q.r.G (mergeG u s).1).1.length := rfl
    omega
  have hidsl : ids.length = (buildCand s.q.r.G (mergeG u s).1).1.length := by
    rw [← c2, List.length_map]
  unfold relStepL relStepP tailP
  dsimp only
  rw [hm, hm2, hm3, hw]
  rw [← hids, r1, d1]
  rw [l1] at l2
  have e1 : (recLo u s.q.r).2.1 = (waveDR s.q.r.G u.1 u.2.1 s.q.r.lo).2.1 := rfl
  have e2 : (recHi u s.q.r).2.1 = (waveDR s.q.r.G u.1 u.2.2 s.q.r.hi).2.1 := rfl
  refine ⟨by rw [l1], l2, r3.trans l3, ?_, ?_⟩
  · rw [d2, e1, e2]; omega
  · rw [d2, e1, e2]; omega

/-- **One query of the linked engine**: the executed leader scan (`leadScanX`); if there is
a leader, the executed stop scan (`stopScanX`), the executed retirement scan (`retScanX`),
the decrements of the count table (`decAllX`) and the cascade `releaseLoopL` reading the
updated table; with no leader, 1 unit for that test.  Returns the new state and count
table, the linked structure, and the cost. -/
noncomputable def qRetireL (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (c : ℕ → ℕ) (s : HQS α)
    (L : Lin) : ((HQS α × (ℕ → ℕ)) × Lin) × ℕ :=
  (leadScanX (fun i => s.r.lo.val (rt i)) s.act K).1.elim
    (((s, c), L), (leadScanX (fun i => s.r.lo.val (rt i)) s.act K).2 + 1)
    (fun a =>
      let U := fun i => s.r.hi.val (rt i)
      let la := s.r.lo.val (rt a)
      let ss := stopScanX φ ε U la a s.act K
      let rs := retScanX rt a U la s.act K
      let dc := decAllX rs.2.1 c
      let cs := releaseLoopL (pidx dc.1) (relFuel s.r.G rs.2.1) rs.2.1 (s.r, L)
      (((⟨cs.1.1, rs.1⟩, dc.1), cs.1.2),
        (leadScanX (fun i => s.r.lo.val (rt i)) s.act K).2 + ss.2 + rs.2.2 + dc.2 + cs.2))

/-- The output of a query of the linked engine: the leader of the executed leader scan and
the bit of the executed stop scan (`false` with no leader). -/
noncomputable def qOutL (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (s : HQS α) : Option ℕ × Bool :=
  ((leadScanX (fun i => s.r.lo.val (rt i)) s.act K).1,
   (leadScanX (fun i => s.r.lo.val (rt i)) s.act K).1.elim false
     (fun a => (stopScanX φ ε (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) a s.act K).1))

/-- **The executed scans compute the query of the manuscript**: `qOutL` is
`RetireFinal.qOut` (lowest-index lower-bound leader among active roots, marginal stop bit). -/
theorem qOutL_eq (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (s : HQS α) :
    qOutL φ ε K rt s = qOut φ ε K (fun i => s.r.lo.val (rt i)) (fun i => s.r.hi.val (rt i)) s.act := by
  unfold qOutL qOut
  rw [leadScanX_spec]
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => rfl
  | some a => simp only [Option.elim_some]; rw [stopScanX_spec]

/-- **One query of the linked engine against `LiteralG2.qRetireP`**: same state and count
table, the abstraction is kept, and the cost is between `K + qRetireP` (the charge of
`LiteralG2.costSP`, including the stop scan) and `11 · (K + qRetireP) + 4`; the executed
scans cost exactly `6K + 1`, `6K + 1` and `7K + 1`. -/
theorem qRetireL_eq (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (c : ℕ → ℕ) (s : HQS α) (L : Lin)
    (h : Abs L s.r.G) (hG : s.r.G.WF) :
    (qRetireL φ ε K rt c s L).1.1.1 = (qRetireP K rt c s).1 ∧
    (qRetireL φ ε K rt c s L).1.1.2 = (qRetireP K rt c s).2.1 ∧
    Abs (qRetireL φ ε K rt c s L).1.2 (qRetireP K rt c s).1.r.G ∧
    Stat L (qRetireL φ ε K rt c s L).1.2 ∧
    K + (qRetireP K rt c s).2.2 ≤ (qRetireL φ ε K rt c s L).2 ∧
    (qRetireL φ ε K rt c s L).2 ≤ 11 * (K + (qRetireP K rt c s).2.2) + 4 := by
  unfold qRetireL qRetireP
  rw [leadScanX_spec]
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none =>
    dsimp only [Option.elim]
    exact ⟨rfl, rfl, h, Stat.refl _, by omega, by omega⟩
  | some a =>
    dsimp only [Option.elim]
    set U : ℕ → α := fun i => s.r.hi.val (rt i)
    set la : α := s.r.lo.val (rt a)
    obtain ⟨-, rs2, rs3⟩ := retScanX_spec rt a U la s.act K
    have rs1 := retScanX_deact rt a U la s.act K
    rw [rs1, rs2, rs3, stopScanX_spec, decAllX_eq]
    obtain ⟨l1, l2, l3, l4, l5⟩ := releaseLoopL_spec
      (pidx (decAll (retiredRoots K rt a U la s.act) c).1)
      (relFuel s.r.G (retiredRoots K rt a U la s.act)) (retiredRoots K rt a U la s.act) (s.r, L) h hG
    simp only at l1 l2 l3 l4 l5
    rw [l1]
    rw [l1] at l2
    refine ⟨rfl, rfl, l2, l3, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only
      have := (decAll_spec (retiredRoots K rt a U la s.act) c).2
      omega

end Steps


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)

/-! ## 8. The linked engine on a run -/

section RunL

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- State of the linked engine: the state of `LiteralG2`'s engine with the protection index
(heaps, values, activity flags, mark table, count table; its circuit field is the ghost
abstraction of the linked lists) and the incidence structure. -/
structure LS (α : Type*) where
  x : GP α
  L : Lin

/-- A query of the linked engine. -/
noncomputable def qStepL (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (y : LS α) : LS α :=
  ⟨⟨⟨(qRetireL φ ε K rt y.x.cnt y.x.s.q y.L).1.1.1, y.x.s.marks⟩,
    (qRetireL φ ε K rt y.x.cnt y.x.s.q y.L).1.1.2⟩, (qRetireL φ ε K rt y.x.cnt y.x.s.q y.L).1.2⟩

/-- The state before the waves of rollout `t + 1`: after the query of time `t`, if any. -/
noncomputable def preL (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (q : ℕ → Bool) (y : LS α)
    (t : ℕ) : LS α :=
  if q t = true then qStepL φ ε K rt y else y

/-- State of the linked engine after `t` rollouts. -/
noncomputable def runSL (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α)
    (q : ℕ → Bool) (y0 : LS α) : ℕ → LS α
  | 0 => y0
  | t + 1 =>
    ⟨⟨(relStepL (pidx (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.cnt) (u (t + 1))
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.s
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).L).1.1,
      (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.cnt⟩,
     (relStepL (pidx (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.cnt) (u (t + 1))
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.s
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).L).1.2⟩

/-- Executed cost of the query of time `t` (if any) and of rollout `t + 1`. -/
noncomputable def costSL (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α)
    (q : ℕ → Bool) (y0 : LS α) (t : ℕ) : ℕ :=
  (if q t = true then (qRetireL φ ε K rt (runSL φ ε K rt u q y0 t).x.cnt
      (runSL φ ε K rt u q y0 t).x.s.q (runSL φ ε K rt u q y0 t).L).2 else 0)
    + (relStepL (pidx (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.cnt) (u (t + 1))
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.s
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).L).2

variable (R : SelRun α) (m0 : ℕ → Bool) (c0 : ℕ → ℕ) (φ : α → ℝ) (ε : ℝ) (L0 : Lin)

/-- Initial state: the initial state of `LiteralG2` (`p0`; its mark and count tables are
the results of the executed passes `clearMarksX`, `zeroAllX`, `incAllX`, `initX_eq`) and an
initial incidence structure `L0`. -/
def y0 : LS α := ⟨p0 R m0 c0, L0⟩

noncomputable def hrunL (t : ℕ) : LS α := runSL φ ε R.K R.rt R.u R.q (y0 R m0 c0 L0) t

noncomputable def hpreL (t : ℕ) : LS α := preL φ ε R.K R.rt R.q (hrunL R m0 c0 φ ε L0 t) t

/-- The executed initialisation passes of the mark and count tables compute the tables of
`p0`; their costs are `N + 1` and `(N + 1) + (K + 1)`. -/
lemma initX_eq :
    (clearMarksX (List.range R.G0.N) m0).1 = (initMarks R.G0.N m0).1 ∧
    (clearMarksX (List.range R.G0.N) m0).2 = R.G0.N + 1 ∧
    (incAllX ((List.range R.K).map R.rt) (zeroAllX (List.range R.G0.N) c0).1).1 = (initCnt R c0).1 ∧
    (zeroAllX (List.range R.G0.N) c0).2
      + (incAllX ((List.range R.K).map R.rt) (zeroAllX (List.range R.G0.N) c0).1).2
      = R.G0.N + 1 + (R.K + 1) := by
  refine ⟨by rw [clearMarksX_eq]; rfl, ?_, by rw [zeroAllX_eq, incAllX_eq]; rfl, ?_⟩
  · rw [clearMarksX_eq]
    have := (initMarks_spec R.G0.N m0).2
    unfold initMarks at this
    omega
  · rw [zeroAllX_eq, incAllX_eq]
    have := (initCnt_spec R c0).2
    unfold initCnt at this
    simp only at this ⊢
    omega

variable {R m0 c0 φ ε L0}

lemma hpreL_eq (t : ℕ) (ih : (hrunL R m0 c0 φ ε L0 t).x = hrunP R m0 c0 t ∧
    Abs (hrunL R m0 c0 φ ε L0 t).L (hrunP R m0 c0 t).s.q.r.G) :
    (hpreL R m0 c0 φ ε L0 t).x = hpreP R m0 c0 t ∧
    Abs (hpreL R m0 c0 φ ε L0 t).L (hpreP R m0 c0 t).s.q.r.G ∧
    Stat (hrunL R m0 c0 φ ε L0 t).L (hpreL R m0 c0 φ ε L0 t).L := by
  have hwf : (hrunP R m0 c0 t).s.q.r.G.WF := by
    rw [(simP_all R m0 c0 t).1]; exact hrunG_wf R m0 t
  unfold hpreL preL hpreP
  by_cases hq : R.q t = true
  · rw [if_pos hq, if_pos hq]
    obtain ⟨q1, q2, q3, q4, -, -⟩ := qRetireL_eq φ ε R.K R.rt (hrunL R m0 c0 φ ε L0 t).x.cnt
      (hrunL R m0 c0 φ ε L0 t).x.s.q (hrunL R m0 c0 φ ε L0 t).L (by rw [ih.1]; exact ih.2)
      (by rw [ih.1]; exact hwf)
    refine ⟨?_, ?_, q4⟩
    · show (⟨⟨(qRetireL φ ε R.K R.rt _ _ _).1.1.1, _⟩, (qRetireL φ ε R.K R.rt _ _ _).1.1.2⟩ : GP α) = _
      rw [q1, q2, ih.1]; rfl
    · show Abs (qRetireL φ ε R.K R.rt _ _ _).1.2 (qRetireP R.K R.rt (hrunP R m0 c0 t).cnt
        (hrunP R m0 c0 t).s.q).1.r.G
      rw [← ih.1]; exact q3
  · rw [if_neg hq, if_neg hq]
    exact ⟨ih.1, ih.2, Stat.refl _⟩

/-- **The linked engine computes the states of `LiteralG2`'s engine with the protection
index, and its incidence structure represents the circuit at every time.** -/
theorem simL_all (hL : Abs L0 R.G0) : ∀ t,
    (hrunL R m0 c0 φ ε L0 t).x = hrunP R m0 c0 t ∧
    Abs (hrunL R m0 c0 φ ε L0 t).L (hrunP R m0 c0 t).s.q.r.G ∧
    Stat L0 (hrunL R m0 c0 φ ε L0 t).L := by
  intro t
  induction t with
  | zero => exact ⟨rfl, hL, Stat.refl _⟩
  | succ t ih =>
    obtain ⟨p1, p2, p3⟩ := hpreL_eq t ⟨ih.1, ih.2.1⟩
    obtain ⟨lc, lp, hr⟩ := p2
    have hs : (hpreP R m0 c0 t).s = hpreG R m0 t := (stepP R m0 c0 t).1
    have hwf : (hpreP R m0 c0 t).s.q.r.G.WF := by rw [hs]; exact hpreG_wf R m0 t
    have hnd : (candG (R.u (t + 1)) (hpreP R m0 c0 t).s).Nodup := by
      obtain ⟨-, -, s3, s4, -⟩ := stepG R m0 t
      rw [hs, s3]; exact s4
    rw [← p1] at hr hwf hnd
    obtain ⟨e1, e2, e3, -, -⟩ := relStepL_eq (pidx (hpreL R m0 c0 φ ε L0 t).x.cnt) (R.u (t + 1))
      (hpreL R m0 c0 φ ε L0 t).x.s (hpreL R m0 c0 φ ε L0 t).L hr hwf hnd
    refine ⟨?_, ?_, ih.2.2.trans (p3.trans e3)⟩
    · show (⟨(relStepL (pidx (hpreL R m0 c0 φ ε L0 t).x.cnt) (R.u (t + 1))
          (hpreL R m0 c0 φ ε L0 t).x.s (hpreL R m0 c0 φ ε L0 t).L).1.1,
          (hpreL R m0 c0 φ ε L0 t).x.cnt⟩ : GP α) = _
      rw [e1, p1]; rfl
    · show Abs (relStepL (pidx (hpreL R m0 c0 φ ε L0 t).x.cnt) (R.u (t + 1))
          (hpreL R m0 c0 φ ε L0 t).x.s (hpreL R m0 c0 φ ε L0 t).L).1.2 _
      have : (hrunP R m0 c0 (t + 1)).s = (relStepP (pidx (hpreP R m0 c0 t).cnt) (R.u (t + 1))
          (hpreP R m0 c0 t).s).1 := rfl
      rw [this, ← p1]; exact e2

/-- **Cost of each query and rollout of the linked engine against `LiteralG2.costSP`.** -/
theorem stepL_cost (hL : Abs L0 R.G0) (t : ℕ) :
    costSP R.K R.rt R.u R.q (p0 R m0 c0) t ≤ costSL φ ε R.K R.rt R.u R.q (y0 R m0 c0 L0) t ∧
    costSL φ ε R.K R.rt R.u R.q (y0 R m0 c0 L0) t
      ≤ 11 * costSP R.K R.rt R.u R.q (p0 R m0 c0) t + 10 := by
  obtain ⟨i1, i2, -⟩ := simL_all (m0 := m0) (c0 := c0) (φ := φ) (ε := ε) hL t
  obtain ⟨p1, p2, -⟩ := hpreL_eq t ⟨i1, i2⟩
  obtain ⟨lc, lp, hr⟩ := p2
  have hs : (hpreP R m0 c0 t).s = hpreG R m0 t := (stepP R m0 c0 t).1
  have hwf : (hpreP R m0 c0 t).s.q.r.G.WF := by rw [hs]; exact hpreG_wf R m0 t
  have hnd : (candG (R.u (t + 1)) (hpreP R m0 c0 t).s).Nodup := by
    obtain ⟨-, -, s3, s4, -⟩ := stepG R m0 t
    rw [hs, s3]; exact s4
  rw [← p1] at hr hwf hnd
  obtain ⟨-, -, -, r4, r5⟩ := relStepL_eq (pidx (hpreL R m0 c0 φ ε L0 t).x.cnt) (R.u (t + 1))
    (hpreL R m0 c0 φ ε L0 t).x.s (hpreL R m0 c0 φ ε L0 t).L hr hwf hnd
  have hwf0 : (hrunP R m0 c0 t).s.q.r.G.WF := by
    rw [(simP_all R m0 c0 t).1]; exact hrunG_wf R m0 t
  obtain ⟨-, -, -, -, q5, q6⟩ := qRetireL_eq φ ε R.K R.rt (hrunL R m0 c0 φ ε L0 t).x.cnt
    (hrunL R m0 c0 φ ε L0 t).x.s.q (hrunL R m0 c0 φ ε L0 t).L (by rw [i1]; exact i2)
    (by rw [i1]; exact hwf0)
  rw [i1] at q5 q6
  have hcL : costSL φ ε R.K R.rt R.u R.q (y0 R m0 c0 L0) t
      = (if R.q t = true then (qRetireL φ ε R.K R.rt (hrunL R m0 c0 φ ε L0 t).x.cnt
          (hrunL R m0 c0 φ ε L0 t).x.s.q (hrunL R m0 c0 φ ε L0 t).L).2 else 0)
        + (relStepL (pidx (hpreL R m0 c0 φ ε L0 t).x.cnt) (R.u (t + 1))
          (hpreL R m0 c0 φ ε L0 t).x.s (hpreL R m0 c0 φ ε L0 t).L).2 := rfl
  have hcP : costSP R.K R.rt R.u R.q (p0 R m0 c0) t
      = (if R.q t = true then R.K + (qRetireP R.K R.rt (hrunP R m0 c0 t).cnt
          (hrunP R m0 c0 t).s.q).2.2 else 0)
        + (relStepP (pidx (hpreP R m0 c0 t).cnt) (R.u (t + 1)) (hpreP R m0 c0 t).s).2 := rfl
  rw [← p1] at hcP
  rw [hcL, hcP]
  by_cases hq : R.q t = true
  · rw [if_pos hq, if_pos hq]
    rw [i1]
    constructor <;> omega
  · rw [if_neg hq, if_neg hq]
    constructor <;> omega

variable (R m0 c0 φ ε L0)

/-- Executed cost of the `τ` rollouts and the queries at times `t < τ`. -/
noncomputable def WrollL : ℕ := ∑ t ∈ range R.τ, costSL φ ε R.K R.rt R.u R.q (y0 R m0 c0 L0) t

/-- Executed cost of the query at the stopping time. -/
noncomputable def WlastL : ℕ := if R.q R.τ = true then
    (qRetireL φ ε R.K R.rt (hrunL R m0 c0 φ ε L0 R.τ).x.cnt (hrunL R m0 c0 φ ε L0 R.τ).x.s.q
      (hrunL R m0 c0 φ ε L0 R.τ).L).2 else 0

/-- Executed cost of the final disposal on the linked structure. -/
noncomputable def WdispL : ℕ :=
  (disposeL (List.range R.G0.N) ((hpreL R m0 c0 φ ε L0 R.τ).x.s.q.r, (hpreL R m0 c0 φ ε L0 R.τ).L)).2

/-- Executed cost of the allocation of the mark table. -/
def WmarkL : ℕ := (clearMarksX (List.range R.G0.N) m0).2

/-- Executed cost of the construction of the count table. -/
def WcntL : ℕ := (zeroAllX (List.range R.G0.N) c0).2
  + (incAllX ((List.range R.K).map R.rt) (zeroAllX (List.range R.G0.N) c0).1).2

variable {R m0 c0 φ ε L0}

theorem W_parts (hL : Abs L0 R.G0) (hN : L0.N = R.G0.N) :
    WrollP R m0 c0 ≤ WrollL R m0 c0 φ ε L0 ∧
    WrollL R m0 c0 φ ε L0 ≤ 11 * WrollP R m0 c0 + 10 * R.τ ∧
    WlastP R m0 c0 ≤ WlastL R m0 c0 φ ε L0 ∧ WlastL R m0 c0 φ ε L0 ≤ 11 * WlastP R m0 c0 + 4 ∧
    WdispP R m0 c0 ≤ WdispL R m0 c0 φ ε L0 ∧ WdispL R m0 c0 φ ε L0 ≤ 10 * WdispP R m0 c0 + 1 ∧
    (disposeL (List.range R.G0.N) ((hpreL R m0 c0 φ ε L0 R.τ).x.s.q.r,
      (hpreL R m0 c0 φ ε L0 R.τ).L)).1.1.G
      = (disposeAll (List.range R.G0.N) (hpreP R m0 c0 R.τ).s.q.r.G).1 ∧
    WmarkL R m0 = WmarkG R m0 + 1 ∧ WcntL R c0 = WcntP R c0 + 2 := by
  have r1 : WrollP R m0 c0 ≤ WrollL R m0 c0 φ ε L0 :=
    sum_le_sum (fun t _ => (stepL_cost hL t).1)
  have r2 : WrollL R m0 c0 φ ε L0 ≤ 11 * WrollP R m0 c0 + 10 * R.τ := by
    unfold WrollL WrollP
    rw [mul_sum]
    have := sum_le_sum (s := range R.τ) (fun t _ => (stepL_cost (m0 := m0) (c0 := c0) (φ := φ)
      (ε := ε) hL t).2)
    rw [sum_add_distrib, sum_const, card_range, smul_eq_mul] at this
    omega
  obtain ⟨i1, i2, i3⟩ := simL_all (m0 := m0) (c0 := c0) (φ := φ) (ε := ε) hL R.τ
  have hwf0 : (hrunP R m0 c0 R.τ).s.q.r.G.WF := by
    rw [(simP_all R m0 c0 R.τ).1]; exact hrunG_wf R m0 R.τ
  obtain ⟨-, -, -, -, q5, q6⟩ := qRetireL_eq φ ε R.K R.rt (hrunL R m0 c0 φ ε L0 R.τ).x.cnt
    (hrunL R m0 c0 φ ε L0 R.τ).x.s.q (hrunL R m0 c0 φ ε L0 R.τ).L (by rw [i1]; exact i2)
    (by rw [i1]; exact hwf0)
  rw [i1] at q5 q6
  have l1 : WlastP R m0 c0 ≤ WlastL R m0 c0 φ ε L0 := by
    unfold WlastP WlastL; rw [i1]; split_ifs <;> omega
  have l2 : WlastL R m0 c0 φ ε L0 ≤ 11 * WlastP R m0 c0 + 4 := by
    unfold WlastP WlastL; rw [i1]; split_ifs <;> omega
  obtain ⟨p1, p2, p3⟩ := hpreL_eq R.τ ⟨i1, i2⟩
  have hs : (hpreP R m0 c0 R.τ).s = hpreG R m0 R.τ := (stepP R m0 c0 R.τ).1
  have hwf : (hpreP R m0 c0 R.τ).s.q.r.G.WF := by rw [hs]; exact hpreG_wf R m0 R.τ
  have hNL : (hpreL R m0 c0 φ ε L0 R.τ).L.N = R.G0.N := by rw [p3.1, i3.1, hN]
  rw [← p1] at p2 hwf
  obtain ⟨d1, d2, d3⟩ := disposeL_spec (List.range R.G0.N)
    ((hpreL R m0 c0 φ ε L0 R.τ).x.s.q.r, (hpreL R m0 c0 φ ε L0 R.τ).L) p2 hwf
    (fun g hg => by rw [hNL]; exact List.mem_range.1 hg)
  simp only at d1 d2 d3
  obtain ⟨-, m2, -, c2⟩ := initX_eq R m0 c0
  refine ⟨r1, r2, l1, l2, ?_, ?_, ?_, ?_, ?_⟩
  · unfold WdispP WdispL; rw [← p1]; exact d2
  · unfold WdispP WdispL; rw [← p1]; exact d3
  · rw [← p1]; exact d1
  · unfold WmarkL WmarkG; rw [m2, (initMarks_spec R.G0.N m0).2]
  · unfold WcntL WcntP; rw [c2, (initCnt_spec R c0).2]; ring

end RunL


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2

/-! ## 9. Construction of the incidence structure -/

section Build

/-- Offset of gate `p`: number of incidences of the gates `< p`. -/
def off (G : Dag) (p : ℕ) : ℕ := ∑ q ∈ range p, (G.children q).length

lemma off_succ (G : Dag) (p : ℕ) : off G (p + 1) = off G p + (G.children p).length := by
  unfold off; rw [sum_range_succ]

lemma off_mono (G : Dag) {p q : ℕ} (h : p ≤ q) : off G p ≤ off G q := by
  unfold off
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) (fun _ _ _ => Nat.zero_le _)

lemma off_N (G : Dag) : off G G.N = live G := rfl

/-- Record of the incidence `(p, c)`: `off p + (position of c in the child list of p) + 1`. -/
def ix (G : Dag) (p c : ℕ) : ℕ := off G p + (G.children p).idxOf c + 1

/-- Records, children and parents during the construction. -/
structure RB where
  src : ℕ → ℕ
  dst : ℕ → ℕ
  inc : ℕ → List ℕ

/-- **Phase A**: empty the incoming-record list of every gate of the list (1 write each; 1
for the exit test). -/
def clrInc : List ℕ → (ℕ → List ℕ) → (ℕ → List ℕ) × ℕ
  | [], I => (I, 1)
  | c :: cs, I => ((clrInc cs (Function.update I c [])).1, (clrInc cs (Function.update I c [])).2 + 1)

lemma clrInc_spec : ∀ (l : List ℕ) (I : ℕ → List ℕ),
    (∀ c, c ∈ l → (clrInc l I).1 c = []) ∧ (∀ c, c ∉ l → (clrInc l I).1 c = I c) ∧
    (clrInc l I).2 = l.length + 1 := by
  intro l
  induction l with
  | nil => intro I; exact ⟨fun c hc => absurd hc List.not_mem_nil, fun _ _ => rfl, rfl⟩
  | cons a l ih =>
    intro I
    obtain ⟨h1, h2, h3⟩ := ih (Function.update I a [])
    refine ⟨fun c hc => ?_, fun c hc => ?_, ?_⟩
    · show (clrInc l (Function.update I a [])).1 c = []
      by_cases hl : c ∈ l
      · exact h1 c hl
      · rw [h2 c hl]
        have : c = a := by
          rcases List.mem_cons.1 hc with h | h
          · exact h
          · exact absurd h hl
        rw [this, Function.update_self]
    · show (clrInc l (Function.update I a [])).1 c = I c
      have hca : c ≠ a := fun h => hc (h ▸ List.mem_cons_self)
      rw [h2 c (fun h => hc (List.mem_cons_of_mem _ h)), Function.update_of_ne hca]
    · show (clrInc l (Function.update I a [])).2 + 1 = _
      rw [h3, List.length_cons]

/-- **Phase B1**: create the records `k + 1, …` of the children `l` of gate `p`: write
`src`, `dst` and prepend the record to the incoming list of the child (4 units each; 1 for
the exit test). -/
def recs (p : ℕ) : List ℕ → ℕ → RB → RB × ℕ
  | [], _, B => (B, 1)
  | c :: cs, k, B =>
    ((recs p cs (k + 1) ⟨Function.update B.src (k + 1) p, Function.update B.dst (k + 1) c,
        Function.update B.inc c ((k + 1) :: B.inc c)⟩).1,
     (recs p cs (k + 1) ⟨Function.update B.src (k + 1) p, Function.update B.dst (k + 1) c,
        Function.update B.inc c ((k + 1) :: B.inc c)⟩).2 + 4)

lemma recs_spec (p : ℕ) : ∀ (l : List ℕ) (k : ℕ) (B : RB),
    (∀ j (hj : j < l.length), (recs p l k B).1.src (k + 1 + j) = p ∧
      (recs p l k B).1.dst (k + 1 + j) = l[j]) ∧
    (∀ e, (e < k + 1 ∨ k + l.length < e) →
      (recs p l k B).1.src e = B.src e ∧ (recs p l k B).1.dst e = B.dst e) ∧
    (∀ c e, e ∈ (recs p l k B).1.inc c ↔
      e ∈ B.inc c ∨ ∃ j, ∃ hj : j < l.length, l[j] = c ∧ e = k + 1 + j) ∧
    (∀ S : Finset ℕ, (∀ c ∈ l, c ∈ S) →
      ∑ c ∈ S, ((recs p l k B).1.inc c).length = ∑ c ∈ S, (B.inc c).length + l.length) ∧
    (recs p l k B).2 = 4 * l.length + 1 := by
  intro l
  induction l with
  | nil =>
    intro k B
    refine ⟨fun j hj => absurd hj (by simp), fun _ _ => ⟨rfl, rfl⟩, fun c e => ?_, fun S _ => rfl, rfl⟩
    show e ∈ B.inc c ↔ _
    simp
  | cons a l ih =>
    intro k B
    set B1 : RB := ⟨Function.update B.src (k + 1) p, Function.update B.dst (k + 1) a,
      Function.update B.inc a ((k + 1) :: B.inc a)⟩ with hB1
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih (k + 1) B1
    refine ⟨fun j hj => ?_, fun e he => ?_, fun c e => ?_, fun S hS => ?_, ?_⟩
    · show (recs p l (k + 1) B1).1.src (k + 1 + j) = p ∧ (recs p l (k + 1) B1).1.dst (k + 1 + j) = _
      cases j with
      | zero =>
        have := i2 (k + 1) (Or.inl (by omega))
        rw [this.1, this.2]
        exact ⟨Function.update_self _ _ _, Function.update_self _ _ _⟩
      | succ j =>
        have := i1 j (by simp at hj; omega)
        rw [show k + 1 + (j + 1) = k + 1 + 1 + j by ring]
        exact ⟨this.1, this.2⟩
    · show (recs p l (k + 1) B1).1.src e = B.src e ∧ (recs p l (k + 1) B1).1.dst e = B.dst e
      have he' : e < k + 1 + 1 ∨ k + 1 + l.length < e := by
        simp only [List.length_cons] at he; omega
      rw [(i2 e he').1, (i2 e he').2]
      have hne : e ≠ k + 1 := by simp only [List.length_cons] at he; omega
      exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩
    · show e ∈ (recs p l (k + 1) B1).1.inc c ↔ _
      rw [i3 c e]
      have hb : e ∈ B1.inc c ↔ e ∈ B.inc c ∨ (a = c ∧ e = k + 1) := by
        show e ∈ Function.update B.inc a ((k + 1) :: B.inc a) c ↔ _
        by_cases hc : c = a
        · subst hc; rw [Function.update_self]; simp [or_comm]
        · rw [Function.update_of_ne hc]; simp [Ne.symm hc]
      rw [hb]
      constructor
      · rintro ((h | ⟨h1, h2⟩) | ⟨j, hj, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨0, by simp, h1, by rw [h2]⟩
        · exact Or.inr ⟨j + 1, by simp; omega, h1, by rw [h2]; ring⟩
      · rintro (h | ⟨j, hj, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · cases j with
          | zero => exact Or.inl (Or.inr ⟨h1, by rw [h2]⟩)
          | succ j => exact Or.inr ⟨j, by simp at hj; omega, h1, by rw [h2]; ring⟩
    · show ∑ c ∈ S, ((recs p l (k + 1) B1).1.inc c).length = _
      rw [i4 S (fun c hc => hS c (List.mem_cons_of_mem _ hc))]
      have haS : a ∈ S := hS a List.mem_cons_self
      have : ∑ c ∈ S, (B1.inc c).length = ∑ c ∈ S, (B.inc c).length + 1 := by
        show ∑ c ∈ S, (Function.update B.inc a ((k + 1) :: B.inc a) c).length = _
        rw [← add_sum_erase _ _ haS, ← add_sum_erase _ (fun c => (B.inc c).length) haS,
          Function.update_self]
        have : ∑ c ∈ S.erase a, (Function.update B.inc a ((k + 1) :: B.inc a) c).length
            = ∑ c ∈ S.erase a, (B.inc c).length := by
          apply sum_congr rfl
          intro c hc
          rw [Function.update_of_ne (mem_erase.1 hc).1]
        rw [this, List.length_cons]; ring
      rw [this, List.length_cons]; ring
    · show (recs p l (k + 1) B1).2 + 4 = _
      rw [i5, List.length_cons]; ring

/-- **Phase B**: for each gate `p` of the list (1 unit), create the records of its children
(`recs`) and build its child list from them (`bldL` on the records `k+1, …, k+|children p|`,
then write its head: 1 unit). -/
def phB (G : Dag) : List ℕ → ℕ → RB × DL → (RB × DL) × ℕ
  | [], _, X => (X, 1)
  | p :: ps, k, X =>
    ((phB G ps (k + (G.children p).length)
        ((recs p (G.children p) k X.1).1,
         ⟨Function.update (bldL (List.range' (k + 1) (G.children p).length) X.2).1.hd p
            (bldL (List.range' (k + 1) (G.children p).length) X.2).2.1,
          (bldL (List.range' (k + 1) (G.children p).length) X.2).1.nx,
          (bldL (List.range' (k + 1) (G.children p).length) X.2).1.pv⟩)).1,
     1 + (recs p (G.children p) k X.1).2 + (bldL (List.range' (k + 1) (G.children p).length) X.2).2.2
       + 1 + (phB G ps (k + (G.children p).length)
        ((recs p (G.children p) k X.1).1,
         ⟨Function.update (bldL (List.range' (k + 1) (G.children p).length) X.2).1.hd p
            (bldL (List.range' (k + 1) (G.children p).length) X.2).2.1,
          (bldL (List.range' (k + 1) (G.children p).length) X.2).1.nx,
          (bldL (List.range' (k + 1) (G.children p).length) X.2).1.pv⟩)).2)

/-- The child list of `p` after phase B. -/
def lcB (G : Dag) (p : ℕ) : List ℕ := List.range' (off G p + 1) (G.children p).length

lemma mem_lcB {G : Dag} {p e : ℕ} : e ∈ lcB G p ↔ off G p < e ∧ e ≤ off G (p + 1) := by
  unfold lcB; rw [List.mem_range'_1, off_succ]; omega

lemma lcB_disj (G : Dag) {p q e : ℕ} (hp : e ∈ lcB G p) (hq : e ∈ lcB G q) : p = q := by
  rw [mem_lcB] at hp hq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := off_mono G (show p + 1 ≤ q by omega); omega
  · have := off_mono G (show q + 1 ≤ p by omega); omega

theorem phB_spec (G : Dag) : ∀ (n a : ℕ) (X : RB × DL),
    (∀ p, a ≤ p → p < a + n → ∀ j (hj : j < (G.children p).length),
      (phB G (List.range' a n) (off G a) X).1.1.src (off G p + 1 + j) = p ∧
      (phB G (List.range' a n) (off G a) X).1.1.dst (off G p + 1 + j) = (G.children p)[j]) ∧
    (∀ e, (e ≤ off G a ∨ off G (a + n) < e) →
      (phB G (List.range' a n) (off G a) X).1.1.src e = X.1.src e ∧
      (phB G (List.range' a n) (off G a) X).1.1.dst e = X.1.dst e) ∧
    (∀ c e, e ∈ (phB G (List.range' a n) (off G a) X).1.1.inc c ↔
      e ∈ X.1.inc c ∨ ∃ p, a ≤ p ∧ p < a + n ∧ ∃ j, ∃ hj : j < (G.children p).length,
        (G.children p)[j] = c ∧ e = off G p + 1 + j) ∧
    (∀ S : Finset ℕ, (∀ p, a ≤ p → p < a + n → ∀ c ∈ G.children p, c ∈ S) →
      ∑ c ∈ S, ((phB G (List.range' a n) (off G a) X).1.1.inc c).length
        = ∑ c ∈ S, (X.1.inc c).length + (off G (a + n) - off G a)) ∧
    (∀ p, a ≤ p → p < a + n →
      Seg (phB G (List.range' a n) (off G a) X).1.2.nx (phB G (List.range' a n) (off G a) X).1.2.pv
        0 (lcB G p) 0 ∧
      (phB G (List.range' a n) (off G a) X).1.2.hd p = (lcB G p).headD 0) ∧
    (∀ e, (e ≤ off G a ∨ off G (a + n) < e) →
      (phB G (List.range' a n) (off G a) X).1.2.nx e = X.2.nx e ∧
      (phB G (List.range' a n) (off G a) X).1.2.pv e = X.2.pv e) ∧
    (∀ p, (p < a ∨ a + n ≤ p) → (phB G (List.range' a n) (off G a) X).1.2.hd p = X.2.hd p) ∧
    (phB G (List.range' a n) (off G a) X).2 = 8 * (off G (a + n) - off G a) + 4 * n + 1 := by
  intro n
  induction n with
  | zero =>
    intro a X
    refine ⟨fun p h1 h2 => absurd h2 (by omega), fun _ _ => ⟨rfl, rfl⟩, fun c e => ?_,
      fun S _ => by simp; rfl, fun p h1 h2 => absurd h2 (by omega), fun _ _ => ⟨rfl, rfl⟩,
      fun _ _ => rfl, by simp [phB]⟩
    show e ∈ X.1.inc c ↔ _
    constructor
    · exact Or.inl
    · rintro (h | ⟨p, h1, h2, _⟩)
      · exact h
      · omega
  | succ n ih =>
    intro a X
    have hr : List.range' a (n + 1) = a :: List.range' (a + 1) n := List.range'_succ
    have hoff : off G a + (G.children a).length = off G (a + 1) := (off_succ G a).symm
    set d := (G.children a).length with hd
    obtain ⟨r1, r2, r3, r4, r5⟩ := recs_spec a (G.children a) (off G a) X.1
    obtain ⟨b1, b2, b3, b4, b5⟩ := bldL_spec (List.range' (off G a + 1) d) X.2
      (List.nodup_range' ..) (fun x hx => by rw [List.mem_range'_1] at hx; omega)
    set X1 : RB × DL := ((recs a (G.children a) (off G a) X.1).1,
         ⟨Function.update (bldL (List.range' (off G a + 1) d) X.2).1.hd a
            (bldL (List.range' (off G a + 1) d) X.2).2.1,
          (bldL (List.range' (off G a + 1) d) X.2).1.nx,
          (bldL (List.range' (off G a + 1) d) X.2).1.pv⟩) with hX1
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih (a + 1) X1
    have hmono : ∀ p, a + 1 ≤ p → off G (a + 1) ≤ off G p := fun p h => off_mono G h
    have hmono2 : off G (a + 1) ≤ off G (a + 1 + n) := off_mono G (by omega)
    have heq : phB G (List.range' a (n + 1)) (off G a) X
        = ((phB G (List.range' (a + 1) n) (off G (a + 1)) X1).1,
           1 + (recs a (G.children a) (off G a) X.1).2
             + (bldL (List.range' (off G a + 1) d) X.2).2.2 + 1
             + (phB G (List.range' (a + 1) n) (off G (a + 1)) X1).2) := by
      rw [hr]; show phB G (a :: _) _ _ = _; rw [phB, hoff]
    rw [heq]
    dsimp only
    have han : a + 1 + n = a + (n + 1) := by ring
    rw [han] at i1 i2 i3 i4 i5 i6 i7 i8 hmono2
    refine ⟨fun p h1 h2 j hj => ?_, fun e he => ?_, fun c e => ?_, fun S hS => ?_,
      fun p h1 h2 => ?_, fun e he => ?_, fun p hp => ?_, ?_⟩
    · by_cases hpa : p = a
      · subst hpa
        have hlt : off G p + 1 + j ≤ off G (p + 1) := by omega
        have := i2 (off G p + 1 + j) (Or.inl hlt)
        rw [this.1, this.2]
        exact r1 j hj
      · exact i1 p (by omega) h2 j hj
    · have he' : e ≤ off G (a + 1) ∨ off G (a + (n + 1)) < e := by
        rcases he with h | h
        · left; omega
        · right; exact h
      rw [(i2 e he').1, (i2 e he').2]
      have he'' : e < off G a + 1 ∨ off G a + d < e := by
        rcases he with h | h
        · left; omega
        · right; omega
      exact r2 e he''
    · rw [i3 c e]
      show (e ∈ (recs a (G.children a) (off G a) X.1).1.inc c ∨ _) ↔ _
      rw [r3 c e]
      constructor
      · rintro ((h | ⟨j, hj, h1, h2⟩) | ⟨p, h1, h2, j, hj, h3, h4⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, le_rfl, by omega, j, hj, h1, h2⟩
        · exact Or.inr ⟨p, by omega, h2, j, hj, h3, h4⟩
      · rintro (h | ⟨p, h1, h2, j, hj, h3, h4⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hpa : p = a
          · subst hpa; exact Or.inl (Or.inr ⟨j, hj, h3, h4⟩)
          · exact Or.inr ⟨p, by omega, h2, j, hj, h3, h4⟩
    · rw [i4 S (fun p h1 h2 c hc => hS p (by omega) h2 c hc)]
      show ∑ c ∈ S, ((recs a (G.children a) (off G a) X.1).1.inc c).length + _ = _
      rw [r4 S (fun c hc => hS a le_rfl (by omega) c hc)]
      omega
    · by_cases hpa : p = a
      · subst hpa
        rw [(i7 p (Or.inl (by omega)))]
        refine ⟨?_, ?_⟩
        · refine seg_congr (nx := X1.2.nx) (pv := X1.2.pv) (lcB G p) 0 0 (fun x hx => ?_) ?_
          · rw [mem_lcB] at hx
            exact i6 x (Or.inl (by omega))
          · exact b1
        · show Function.update _ p _ p = _
          rw [Function.update_self, b2]; rfl
      · exact i5 p (by omega) h2
    · have he' : e ≤ off G (a + 1) ∨ off G (a + (n + 1)) < e := by
        rcases he with h | h
        · left; omega
        · right; exact h
      rw [(i6 e he').1, (i6 e he').2]
      have hx : e ∉ List.range' (off G a + 1) d := by
        rw [List.mem_range'_1]; rcases he with h | h <;> omega
      exact b4 e hx
    · rw [i7 p (by omega)]
      show Function.update _ a _ p = _
      have hpa : p ≠ a := by omega
      rw [Function.update_of_ne hpa, b3]
    · rw [i8, r5, b5, List.length_range']
      have := off_mono G (show a ≤ a + 1 by omega)
      omega

end Build


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2

section Build2

/-- Scatter the records of a list into a table indexed by their parent gate (read `src`,
write: 2 units each; 1 for the exit test). -/
def scatter (src : ℕ → ℕ) : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) × ℕ
  | [], T => (T, 1)
  | e :: es, T => ((scatter src es (Function.update T (src e) e)).1,
      (scatter src es (Function.update T (src e) e)).2 + 2)

lemma scatter_frame (src : ℕ → ℕ) : ∀ (l : List ℕ) (T : ℕ → ℕ) (x : ℕ), (∀ e ∈ l, src e ≠ x) →
    (scatter src l T).1 x = T x := by
  intro l
  induction l with
  | nil => intro T x _; rfl
  | cons e l ih =>
    intro T x h
    show (scatter src l (Function.update T (src e) e)).1 x = T x
    rw [ih _ x (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    exact Function.update_of_ne (fun h' => h e List.mem_cons_self h'.symm) _ _

lemma scatter_spec (src : ℕ → ℕ) : ∀ (l : List ℕ) (T : ℕ → ℕ),
    (∀ e ∈ l, ∀ e' ∈ l, src e = src e' → e = e') →
    (∀ e ∈ l, (scatter src l T).1 (src e) = e) ∧ (scatter src l T).2 = 2 * l.length + 1 := by
  intro l
  induction l with
  | nil => intro T _; exact ⟨fun e he => absurd he List.not_mem_nil, rfl⟩
  | cons e l ih =>
    intro T hinj
    obtain ⟨i1, i2⟩ := ih (Function.update T (src e) e)
      (fun a ha b hb h => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) h)
    refine ⟨fun e' he' => ?_, by show _ + 2 = _; rw [i2, List.length_cons]; ring⟩
    show (scatter src l (Function.update T (src e) e)).1 (src e') = e'
    rcases List.mem_cons.1 he' with h | h
    · subst h
      by_cases hx : ∃ e'' ∈ l, src e'' = src e'
      · obtain ⟨e'', h1, h2⟩ := hx
        have := hinj e'' (List.mem_cons_of_mem _ h1) e' List.mem_cons_self h2
        subst this
        exact i1 e'' h1
      · push Not at hx
        rw [scatter_frame src l _ _ hx, Function.update_self]
    · exact i1 e' h

/-- Read the table at each gate of a list (1 unit each; 1 for the exit test). -/
def mapT (T : ℕ → ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 1)
  | p :: ps => (T p :: (mapT T ps).1, (mapT T ps).2 + 1)

lemma mapT_eq (T : ℕ → ℕ) : ∀ l : List ℕ, mapT T l = (l.map T, l.length + 1) := by
  intro l
  induction l with
  | nil => rfl
  | cons p l ih => rw [mapT, ih]; rfl

/-- **Phase D**: for each gate `c` of the list (1 unit), scatter its incoming records by
parent, read the records of its parents in the order of its parent list, build its parent
list (`bldL`) and write its head (1 unit). -/
def phD (G : Dag) (B : RB) : List ℕ → (ℕ → ℕ) × DL → ((ℕ → ℕ) × DL) × ℕ
  | [], X => (X, 1)
  | c :: cs, X =>
    ((phD G B cs ((scatter B.src (B.inc c) X.1).1,
        ⟨Function.update (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.hd c
            (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).2.1,
          (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.nx,
          (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.pv⟩)).1,
     1 + (scatter B.src (B.inc c) X.1).2 + (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).2
       + (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).2.2 + 1
       + (phD G B cs ((scatter B.src (B.inc c) X.1).1,
        ⟨Function.update (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.hd c
            (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).2.1,
          (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.nx,
          (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.pv⟩)).2)

/-- The parent list of `c`: the records of its parents, in the order of `G.parents c`. -/
def lpB (G : Dag) (c : ℕ) : List ℕ := (G.parents c).map (fun p => ix G p c)

theorem phD_spec (G : Dag) (B : RB) : ∀ (cs : List ℕ) (X : (ℕ → ℕ) × DL), cs.Nodup →
    (∀ c ∈ cs, ∀ e ∈ B.inc c, ∀ e' ∈ B.inc c, B.src e = B.src e' → e = e') →
    (∀ c ∈ cs, ∀ p ∈ G.parents c, ix G p c ∈ B.inc c ∧ B.src (ix G p c) = p) →
    (∀ c ∈ cs, (lpB G c).Nodup ∧ ∀ e ∈ lpB G c, 0 < e) →
    (∀ c ∈ cs, ∀ c', c' ≠ c → ∀ e ∈ lpB G c, e ∉ lpB G c') →
    (∀ c ∈ cs, Seg (phD G B cs X).1.2.nx (phD G B cs X).1.2.pv 0 (lpB G c) 0 ∧
      (phD G B cs X).1.2.hd c = (lpB G c).headD 0) ∧
    (∀ e, (∀ c ∈ cs, e ∉ lpB G c) →
      (phD G B cs X).1.2.nx e = X.2.nx e ∧ (phD G B cs X).1.2.pv e = X.2.pv e) ∧
    (∀ c, c ∉ cs → (phD G B cs X).1.2.hd c = X.2.hd c) ∧
    (phD G B cs X).2 = ∑ c ∈ cs.toFinset, (2 * (B.inc c).length + 5 * (G.parents c).length + 5) + 1 := by
  intro cs
  induction cs with
  | nil =>
    intro X _ _ _ _ _
    exact ⟨fun c hc => absurd hc List.not_mem_nil, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  | cons c cs ih =>
    intro X hnd hinj hix hlp hdis
    obtain ⟨hc, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨sc1, sc2⟩ := scatter_spec B.src (B.inc c) X.1 (hinj c List.mem_cons_self)
    set T1 := (scatter B.src (B.inc c) X.1).1 with hT1
    have hids : (mapT T1 (G.parents c)).1 = lpB G c := by
      rw [mapT_eq]
      unfold lpB
      apply List.map_congr_left
      intro p hp
      obtain ⟨h1, h2⟩ := hix c List.mem_cons_self p hp
      have := sc1 _ h1
      rw [h2] at this
      exact this
    obtain ⟨hnd1, hpos1⟩ := hlp c List.mem_cons_self
    obtain ⟨b1, b2, b3, b4, b5⟩ := bldL_spec (lpB G c) X.2 hnd1 hpos1
    set X1 : (ℕ → ℕ) × DL := (T1, ⟨Function.update (bldL (lpB G c) X.2).1.hd c
        (bldL (lpB G c) X.2).2.1, (bldL (lpB G c) X.2).1.nx, (bldL (lpB G c) X.2).1.pv⟩) with hX1
    obtain ⟨i1, i2, i3, i4⟩ := ih X1 hnd' (fun c' h => hinj c' (List.mem_cons_of_mem _ h))
      (fun c' h => hix c' (List.mem_cons_of_mem _ h)) (fun c' h => hlp c' (List.mem_cons_of_mem _ h))
      (fun c' h => hdis c' (List.mem_cons_of_mem _ h))
    have heq : phD G B (c :: cs) X = ((phD G B cs X1).1,
        1 + (scatter B.src (B.inc c) X.1).2 + (mapT T1 (G.parents c)).2
          + (bldL (lpB G c) X.2).2.2 + 1 + (phD G B cs X1).2) := by
      rw [phD, hids]
    rw [heq]
    dsimp only
    refine ⟨fun c' hc' => ?_, fun e he => ?_, fun c' hc' => ?_, ?_⟩
    · rcases List.mem_cons.1 hc' with h | h
      · subst h
        refine ⟨?_, ?_⟩
        · refine seg_congr (nx := X1.2.nx) (pv := X1.2.pv) (lpB G c') 0 0 (fun x hx => ?_) b1
          refine i2 x (fun c'' hc'' => ?_)
          have hne : c'' ≠ c' := fun h => hc (h ▸ hc'')
          exact hdis c' List.mem_cons_self c'' hne x hx
        · rw [i3 c' hc]
          show Function.update _ c' _ c' = _
          rw [Function.update_self, b2]
      · exact i1 c' h
    · rw [(i2 e (fun c' hc' => he c' (List.mem_cons_of_mem _ hc'))).1,
        (i2 e (fun c' hc' => he c' (List.mem_cons_of_mem _ hc'))).2]
      exact b4 e (he c List.mem_cons_self)
    · rw [i3 c' (fun h => hc' (List.mem_cons_of_mem _ h))]
      show Function.update _ c _ c' = _
      rw [Function.update_of_ne (fun h => hc' (by rw [h]; exact List.mem_cons_self)), b3]
    · rw [i4, sc2, mapT_eq, b5, List.toFinset_cons, sum_insert (fun h => hc (List.mem_toFinset.1 h))]
      have : (lpB G c).length = (G.parents c).length := by unfold lpB; rw [List.length_map]
      rw [this]
      ring

/-- `Σ_{c < N} |parents c| = live G` when every child is a gate and child lists have no
repetition. -/
lemma sum_parents (G : Dag) (hG : G.WF) (hnd : ∀ g, (G.children g).Nodup)
    (hcl : ∀ p c, c ∈ G.children p → c < G.N) :
    ∑ c ∈ range G.N, (G.parents c).length = live G := by
  have h1 : ∀ c ∈ range G.N, (G.parents c).length
      = ∑ p ∈ range G.N, if c ∈ G.children p then 1 else 0 := by
    intro c _
    rw [← card_filter]
    rw [← List.toFinset_card_of_nodup (hG.parents_nodup c)]
    congr 1
    ext p
    simp only [mem_filter, mem_range, List.mem_toFinset]
    exact ⟨fun h => ⟨hG.parent_lt c p h, (hG.parents_iff c p).1 h⟩,
      fun h => (hG.parents_iff c p).2 h.2⟩
  rw [sum_congr rfl h1, sum_comm]
  unfold live
  apply sum_congr rfl
  intro p _
  rw [← card_filter, ← List.toFinset_card_of_nodup (hnd p)]
  congr 1
  ext c
  simp only [mem_filter, mem_range, List.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨hcl p c h, h⟩⟩

/-- **Construction of the incidence structure** from arbitrary initial contents of all its
arrays (`B0`, `C0`, `P0`, the scratch table `T0`): phase A (`clrInc`), phase B (`phB`: records
and child lists), phase D (`phD`: parent lists). -/
def buildLin (G : Dag) (B0 : RB) (C0 P0 : DL) (T0 : ℕ → ℕ) : Lin × ℕ :=
  (⟨G.N, live G,
    (phB G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)).1.1.src,
    (phB G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)).1.1.dst,
    (phB G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)).1.2,
    (phD G (phB G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)).1.1
      (List.range G.N) (T0, P0)).1.2⟩,
   (clrInc (List.range G.N) B0.inc).2
    + (phB G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)).2
    + (phD G (phB G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)).1.1
      (List.range G.N) (T0, P0)).2)

/-- The ghost child lists of the constructed structure. -/
def lcF (G : Dag) (p : ℕ) : List ℕ := if p < G.N then lcB G p else []

/-- The ghost parent lists of the constructed structure. -/
def lpF (G : Dag) (c : ℕ) : List ℕ := if c < G.N then lpB G c else []

end Build2


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2

section Build3

lemma ix_eq (G : Dag) (p c : ℕ) : ix G p c = off G p + 1 + (G.children p).idxOf c := by
  unfold ix; ring

lemma ix_mem (G : Dag) {p c : ℕ} (h : c ∈ G.children p) : ix G p c ∈ lcB G p := by
  rw [mem_lcB, ix_eq, off_succ]
  have := List.idxOf_lt_length_of_mem h
  omega

/-- **Correctness and cost of the construction**: if the circuit is well formed, its child
lists have no repetition and its children are gates (`< N`), the constructed structure
represents `G` (ghost lists `lcF`, `lpF`), has `N` gates and `live G` records, and its
construction costs `15 · live G + 10 · N + 3`, from arbitrary initial array contents. -/
theorem buildLin_spec (G : Dag) (hG : G.WF) (hnd : ∀ g, (G.children g).Nodup)
    (hcl : ∀ p c, c ∈ G.children p → c < G.N) (B0 : RB) (C0 P0 : DL) (T0 : ℕ → ℕ) :
    AbsR (buildLin G B0 C0 P0 T0).1 G (lcF G) (lpF G) ∧ (buildLin G B0 C0 P0 T0).1.N = G.N ∧
    (buildLin G B0 C0 P0 T0).1.M = live G ∧
    (buildLin G B0 C0 P0 T0).2 = 15 * live G + 10 * G.N + 3 := by
  obtain ⟨a1, -, a3⟩ := clrInc_spec (List.range G.N) B0.inc
  set A := clrInc (List.range G.N) B0.inc with hA
  set X : RB × DL := (⟨B0.src, B0.dst, A.1⟩, C0) with hX
  have hr : List.range G.N = List.range' 0 G.N := List.range_eq_range'
  have h0 : off G 0 = 0 := by unfold off; simp
  have hB : phB G (List.range G.N) 0 X = phB G (List.range' 0 G.N) (off G 0) X := by rw [hr, h0]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := phB_spec G G.N 0 X
  rw [← hB, Nat.zero_add, h0] at *
  set Bp := phB G (List.range G.N) 0 X with hBp
  -- translated facts
  have sx : ∀ p, p < G.N → ∀ c ∈ G.children p, Bp.1.1.src (ix G p c) = p ∧ Bp.1.1.dst (ix G p c) = c := by
    intro p hp c hc
    have hj := List.idxOf_lt_length_of_mem hc
    obtain ⟨e1, e2⟩ := f1 p (Nat.zero_le _) hp _ hj
    rw [ix_eq]
    exact ⟨e1, by rw [e2, List.getElem_idxOf]⟩
  have sl : ∀ p, p < G.N → ∀ e ∈ lcB G p, Bp.1.1.src e = p ∧
      ∃ j, ∃ hj : j < (G.children p).length, e = off G p + 1 + j ∧ Bp.1.1.dst e = (G.children p)[j] := by
    intro p hp e he
    have he' : e ∈ List.range' (off G p + 1) (G.children p).length := he
    rw [List.mem_range'_1] at he'
    obtain ⟨e1, e2⟩ := f1 p (Nat.zero_le _) hp (e - off G p - 1) (by omega)
    have hee : off G p + 1 + (e - off G p - 1) = e := by omega
    rw [hee] at e1 e2
    exact ⟨e1, e - off G p - 1, by omega, hee.symm, e2⟩
  have smem : ∀ c, c < G.N → ∀ e, e ∈ Bp.1.1.inc c ↔ ∃ p, p < G.N ∧ ∃ j, ∃ hj : j < (G.children p).length,
      (G.children p)[j] = c ∧ e = off G p + 1 + j := by
    intro c hc e
    rw [f3 c e]
    have : X.1.inc c = [] := a1 c (List.mem_range.2 hc)
    rw [this]
    constructor
    · rintro (h | ⟨p, -, h2, h3⟩)
      · exact absurd h List.not_mem_nil
      · exact ⟨p, h2, h3⟩
    · rintro ⟨p, h2, h3⟩
      exact Or.inr ⟨p, Nat.zero_le _, h2, h3⟩
  have hparN : ∀ c p, p ∈ G.parents c → p < G.N ∧ c < G.N ∧ c ∈ G.children p := by
    intro c p hp
    have hc := (hG.parents_iff c p).1 hp
    exact ⟨hG.parent_lt c p hp, hcl p c hc, hc⟩
  have hchN : ∀ p c, c ∈ G.children p → p < G.N := fun p c h => hG.parent_lt c p ((hG.parents_iff c p).2 h)
  -- phase D
  obtain ⟨d1, d2, d3, d4⟩ := phD_spec G Bp.1.1 (List.range G.N) (T0, P0) (List.nodup_range)
    (by
      intro c hc e he e' he' hs
      have hcN := List.mem_range.1 hc
      obtain ⟨p, hp, j, hj, hj1, rfl⟩ := (smem c hcN e).1 he
      obtain ⟨p', hp', j', hj', hj1', rfl⟩ := (smem c hcN e').1 he'
      have s1 := (f1 p (Nat.zero_le _) hp j hj).1
      have s2 := (f1 p' (Nat.zero_le _) hp' j' hj').1
      rw [s1, s2] at hs
      subst hs
      have : j = j' := ((hnd p).getElem_inj_iff).1 (hj1.trans hj1'.symm)
      subst this; rfl)
    (by
      intro c _ p hp
      obtain ⟨hpN, hcN, hcp⟩ := hparN c p hp
      refine ⟨(smem c hcN _).2 ⟨p, hpN, _, List.idxOf_lt_length_of_mem hcp,
        List.getElem_idxOf _, ix_eq G p c⟩, (sx p hpN c hcp).1⟩)
    (by
      intro c _
      refine ⟨(hG.parents_nodup c).map_on (fun p hp p' hp' h => ?_), fun e he => ?_⟩
      · exact lcB_disj G (ix_mem G (hparN c p hp).2.2) (h ▸ ix_mem G (hparN c p' hp').2.2)
      · obtain ⟨p, _, rfl⟩ := List.mem_map.1 he
        unfold ix; omega)
    (by
      intro c _ c' hne e he he'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      obtain ⟨p', hp', h⟩ := List.mem_map.1 he'
      obtain ⟨hpN, _, hcp⟩ := hparN c p hp
      obtain ⟨hpN', _, hcp'⟩ := hparN c' p' hp'
      have e1 := (sx p hpN c hcp).2
      have e2 := (sx p' hpN' c' hcp').2
      rw [h] at e2
      exact hne (e2.symm.trans e1))
  set Dp := phD G Bp.1.1 (List.range G.N) (T0, P0) with hDp
  have hL : (buildLin G B0 C0 P0 T0).1 = ⟨G.N, live G, Bp.1.1.src, Bp.1.1.dst, Bp.1.2, Dp.1.2⟩ := rfl
  have hcost : (buildLin G B0 C0 P0 T0).2 = A.2 + Bp.2 + Dp.2 := rfl
  refine ⟨?_, by rw [hL], by rw [hL], ?_⟩
  · rw [hL]
    refine ⟨⟨fun g hg => ?_, fun g => ?_, fun g => ?_, fun g e he => ?_, fun g e he => ?_,
      fun g hg => ?_⟩, ⟨fun g hg => ?_, fun g => ?_, fun g => ?_, fun g e he => ?_,
      fun g e he => ?_, fun g hg => ?_⟩, fun g => ?_, fun g => ?_, fun e => ?_, fun g e he => ?_,
      fun g e he => ?_, hnd⟩
    -- child lists
    · show Bp.1.2.hd g = (lcF G g).headD 0
      unfold lcF; rw [if_pos hg]; exact (f5 g (Nat.zero_le _) hg).2
    · show Seg Bp.1.2.nx Bp.1.2.pv 0 (lcF G g) 0
      unfold lcF; split_ifs with hg
      · exact (f5 g (Nat.zero_le _) hg).1
      · trivial
    · unfold lcF; split_ifs
      · exact List.nodup_range' ..
      · exact List.nodup_nil
    · show Bp.1.1.src e = g
      unfold lcF at he; split_ifs at he with hg
      · exact (sl g hg e he).1
      · exact absurd he List.not_mem_nil
    · unfold lcF at he; split_ifs at he with hg
      · have := (mem_lcB.1 he).1; omega
      · exact absurd he List.not_mem_nil
    · unfold lcF; rw [if_neg (by have : G.N ≤ g := hg; omega)]
    -- parent lists
    · show Dp.1.2.hd g = (lpF G g).headD 0
      unfold lpF; rw [if_pos hg]; exact (d1 g (List.mem_range.2 hg)).2
    · show Seg Dp.1.2.nx Dp.1.2.pv 0 (lpF G g) 0
      unfold lpF; split_ifs with hg
      · exact (d1 g (List.mem_range.2 hg)).1
      · trivial
    · unfold lpF; split_ifs
      · exact (hG.parents_nodup g).map_on (fun p hp p' hp' h =>
          lcB_disj G (ix_mem G (hparN g p hp).2.2) (h ▸ ix_mem G (hparN g p' hp').2.2))
      · exact List.nodup_nil
    · show Bp.1.1.dst e = g
      unfold lpF at he; split_ifs at he with hg
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
        exact (sx p (hparN g p hp).1 g (hparN g p hp).2.2).2
      · exact absurd he List.not_mem_nil
    · unfold lpF at he; split_ifs at he
      · obtain ⟨p, _, rfl⟩ := List.mem_map.1 he; unfold ix; omega
      · exact absurd he List.not_mem_nil
    · unfold lpF; rw [if_neg (by have : G.N ≤ g := hg; omega)]
    -- children
    · show (lcF G g).map Bp.1.1.dst = G.children g
      unfold lcF; split_ifs with hg
      · apply List.ext_getElem (by unfold lcB; simp)
        intro i h1 h2
        rw [List.getElem_map]
        have hm : (lcB G g)[i]'(by simpa using h1) ∈ lcB G g := List.getElem_mem _
        obtain ⟨-, j, hj, hj1, hj2⟩ := sl g hg _ hm
        rw [hj2]
        have : (lcB G g)[i]'(by simpa using h1) = off G g + 1 + i := by
          unfold lcB; rw [List.getElem_range']; ring
        have hji : j = i := by omega
        subst hji; rfl
      · symm
        apply List.eq_nil_iff_forall_not_mem.2
        intro c hc
        exact hg (hchN g c hc)
    -- parents
    · show (lpF G g).map Bp.1.1.src = G.parents g
      unfold lpF; split_ifs with hg
      · unfold lpB; rw [List.map_map]
        conv_rhs => rw [← List.map_id (G.parents g)]
        apply List.map_congr_left
        intro p hp
        exact (sx p (hparN g p hp).1 g (hparN g p hp).2.2).1
      · symm
        apply List.eq_nil_iff_forall_not_mem.2
        intro p hp
        exact hg (hparN g p hp).2.1
    -- sync
    · show e ∈ lcF G (Bp.1.1.src e) ↔ e ∈ lpF G (Bp.1.1.dst e)
      constructor
      · intro he
        unfold lcF at he; split_ifs at he with hg
        · obtain ⟨-, j, hj, hj1, hj2⟩ := sl _ hg e he
          set g := Bp.1.1.src e
          have hcm : (G.children g)[j] ∈ G.children g := List.getElem_mem _
          have hcN : (G.children g)[j] < G.N := hcl g _ hcm
          unfold lpF; rw [hj2, if_pos hcN]
          refine List.mem_map.2 ⟨g, (hG.parents_iff _ g).2 hcm, ?_⟩
          rw [ix_eq, (hnd g).idxOf_getElem, hj1]
        · exact absurd he List.not_mem_nil
      · intro he
        unfold lpF at he; split_ifs at he with hg
        · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 he
          obtain ⟨hpN, _, hcp⟩ := hparN _ p hp
          have hs : Bp.1.1.src e = p := by rw [← hpe]; exact (sx p hpN _ hcp).1
          unfold lcF; rw [hs, if_pos hpN, ← hpe]
          exact ix_mem G hcp
        · exact absurd he List.not_mem_nil
    -- bounds
    · unfold lcF at he; split_ifs at he with hg
      · have := (mem_lcB.1 he).2
        have := off_mono G (show g + 1 ≤ G.N by omega)
        rw [off_N] at this; show _ ≤ live G; omega
      · exact absurd he List.not_mem_nil
    · unfold lpF at he; split_ifs at he with hg
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
        have := (mem_lcB.1 (ix_mem G (hparN g p hp).2.2)).2
        have := off_mono G (show p + 1 ≤ G.N by have := (hparN g p hp).1; omega)
        rw [off_N] at this; show _ ≤ live G; omega
      · exact absurd he List.not_mem_nil
  · rw [hcost, a3, f8, d4, List.toFinset_range, List.length_range, off_N, sum_add_distrib,
      sum_add_distrib, ← mul_sum, ← mul_sum, sum_parents G hG hnd hcl, sum_const, card_range,
      smul_eq_mul]
    have hinc := f4 (range G.N) (fun p _ hp c hc => mem_range.2 (hcl p c hc))
    have h0' : ∑ c ∈ range G.N, (X.1.inc c).length = 0 := by
      apply sum_eq_zero
      intro c hc
      show (A.1 c).length = 0
      rw [a1 c (List.mem_range.2 (mem_range.1 hc))]; rfl
    rw [h0', off_N] at hinc
    rw [hinc]
    omega

end Build3


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)

/-! ## 10. Every sift of the run terminates within its fuel -/

section HeapRun

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The sifts executed by `updateKey H h x` (at the position of `h`, if present) stop by
their own test within the fuel `⌈log₂ n⌉`. -/
def ukOK (H : Heap ℕ α) (h : ℕ) (x : α) : Prop :=
  ∀ i, H.pos h = some i →
    doneUp (Nat.clog 2 H.n) (H.setKey i x) i ∧ doneDn (Nat.clog 2 H.n) (H.setKey i x) i

/-- The sifts executed by `delete H h` stop by their own test within the fuel. -/
def delOK (H : Heap ℕ α) (h : ℕ) : Prop :=
  ∀ i, H.pos h = some i →
    doneUp (Nat.clog 2 H.n) (H.moveLast h i) i ∧ doneDn (Nat.clog 2 H.n) (H.moveLast h i) i

lemma ukOK_of (H : Heap ℕ α) (hP : H.PosOK) (h : ℕ) (x : α) : ukOK H h x :=
  fun i hi => updateAt_done H i x (pos_lt H hP h i hi)

lemma delOK_of (H : Heap ℕ α) (hP : H.PosOK) (h : ℕ) : delOK H h :=
  fun i hi => deleteAt_done H h i (pos_lt H hP h i hi)

/-- Every heap of an endpoint state is a valid heap. -/
def AllInv (s : HEState α) : Prop := ∀ p, (s.hp p).Inv

lemma delete_inv (H : Heap ℕ α) (hI : H.Inv) (h : ℕ) : (HeapImpl.delete H h).1.Inv := by
  by_cases hp : H.pos h = none
  · unfold HeapImpl.delete; rw [hp]; exact hI
  · have : H.lookup h ≠ none := by unfold Heap.lookup; simpa using hp
    exact (HeapImpl.delete_spec hI h this).1

/-- Mirror of `dlvX`: every `updateKey` it executes runs its sifts within their fuel. -/
def dlvOK (g : ℕ) (y : α) : List ℕ → HEState α → List ℕ → Prop
  | [], _, _ => True
  | p :: ps, s, st => ukOK (s.hp p) g y ∧ dlvOK g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1

/-- Mirror of `loopDX`. -/
def loopOK (G : Dag) : ℕ → HEState α → List ℕ → Prop
  | 0, _, _ => True
  | _ + 1, _, [] => True
  | f + 1, s, g :: st => dlvOK g (s.val g) (G.parents g) s st ∧
      loopOK G f (dlvX g (s.val g) (G.parents g) s st).1 (dlvX g (s.val g) (G.parents g) s st).2.1

/-- Mirror of `waveDX`. -/
def waveOK (G : Dag) (x : ℕ) (y : α) (s : HEState α) : Prop :=
  targetH G x y s x ≠ s.val x →
    loopOK G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]

lemma dlvOne_inv (g : ℕ) (y : α) (p : ℕ) (s : HEState α) (st : List ℕ) (h : AllInv s) :
    AllInv (dlvOne g y p s st).1 := by
  intro q
  unfold dlvOne
  split_ifs
  · show (Function.update s.hp p (updateKey (s.hp p) g y).1 q).Inv
    by_cases hq : q = p
    · subst hq; rw [Function.update_self]; exact (HeapImpl.updateKey_spec (h q) g y).1
    · rw [Function.update_of_ne hq]; exact h q
  · show (Function.update s.hp p (updateKey (s.hp p) g y).1 q).Inv
    by_cases hq : q = p
    · subst hq; rw [Function.update_self]; exact (HeapImpl.updateKey_spec (h q) g y).1
    · rw [Function.update_of_ne hq]; exact h q

lemma dlv_ok (g : ℕ) (y : α) : ∀ (ps : List ℕ) (s : HEState α) (st : List ℕ), AllInv s →
    dlvOK g y ps s st ∧ AllInv (dlvX g y ps s st).1 := by
  intro ps
  induction ps with
  | nil => intro s st h; exact ⟨trivial, h⟩
  | cons p ps ih =>
    intro s st h
    obtain ⟨i1, i2⟩ := ih (dlvOne g y p s st).1 (dlvOne g y p s st).2.1 (dlvOne_inv g y p s st h)
    exact ⟨⟨ukOK_of _ (h p).posOK g y, i1⟩, i2⟩

lemma loop_ok (G : Dag) : ∀ (f : ℕ) (s : HEState α) (st : List ℕ), AllInv s →
    loopOK G f s st ∧ AllInv (loopDX G f s st).1 := by
  intro f
  induction f with
  | zero => intro s st h; exact ⟨trivial, h⟩
  | succ f ih =>
    intro s st h
    cases st with
    | nil => exact ⟨trivial, h⟩
    | cons g st =>
      obtain ⟨d1, d2⟩ := dlv_ok g (s.val g) (G.parents g) s st h
      obtain ⟨i1, i2⟩ := ih _ (dlvX g (s.val g) (G.parents g) s st).2.1 d2
      exact ⟨⟨d1, i1⟩, i2⟩

lemma wave_ok (G : Dag) (x : ℕ) (y : α) (s : HEState α) (h : AllInv s) :
    waveOK G x y s ∧ AllInv (waveDX G x y s).1 := by
  have h' : AllInv (⟨Function.update s.val x (targetH G x y s x), s.hp⟩ : HEState α) := h
  refine ⟨fun _ => (loop_ok G _ _ _ h').1, ?_⟩
  unfold waveDX
  split_ifs
  · exact h
  · exact (loop_ok G _ _ _ h').2

/-- Mirror of `retireListL`: both heap deletions of every retired candidate run their sifts
within their fuel. -/
def retOK : List ℕ → HRState α × Lin → Prop
  | [], _ => True
  | e :: es, x =>
    (x.1.hi.val (x.2.dst e) < x.1.lo.val (x.2.src e) →
      delOK (x.1.lo.hp (x.2.src e)) (x.2.dst e) ∧ delOK (x.1.hi.hp (x.2.src e)) (x.2.dst e)) ∧
    retOK es (retireOneL e x).1

lemma retire_ok : ∀ (ids : List ℕ) (x : HRState α × Lin), AllInv x.1.lo → AllInv x.1.hi →
    retOK ids x := by
  intro ids
  induction ids with
  | nil => intro _ _ _; trivial
  | cons e es ih =>
    intro x hl hh
    refine ⟨fun _ => ⟨delOK_of _ (hl _).posOK _, delOK_of _ (hh _).posOK _⟩, ih _ ?_ ?_⟩
    · unfold retireOneL; split_ifs
      · intro q
        show (Function.update x.1.lo.hp (x.2.src e) _ q).Inv
        by_cases hq : q = x.2.src e
        · subst hq; rw [Function.update_self]; exact delete_inv _ (hl _) _
        · rw [Function.update_of_ne hq]; exact hl q
      · exact hl
    · unfold retireOneL; split_ifs
      · intro q
        show (Function.update x.1.hi.hp (x.2.src e) _ q).Inv
        by_cases hq : q = x.2.src e
        · subst hq; rw [Function.update_self]; exact delete_inv _ (hh _) _
        · rw [Function.update_of_ne hq]; exact hh q
      · exact hh

/-- **Mirror of one rollout of the linked engine**: every sift executed by its two waves
and by its retirement pass terminates within its fuel (the cascade and the merge execute
no sift). -/
def stepOK (u : ℕ × α × α) (s : GS α) (L : Lin) : Prop :=
  waveOK s.q.r.G u.1 u.2.1 s.q.r.lo ∧ waveOK s.q.r.G u.1 u.2.2 s.q.r.hi ∧
  retOK (candTrav L (mergeMX s.marks (waveDX s.q.r.G u.1 u.2.1 s.q.r.lo).2.2
      (waveDX s.q.r.G u.1 u.2.2 s.q.r.hi).2.2).1).1
    (⟨s.q.r.G, (waveDX s.q.r.G u.1 u.2.1 s.q.r.lo).1, (waveDX s.q.r.G u.1 u.2.2 s.q.r.hi).1⟩, L)

lemma step_ok (u : ℕ × α × α) (s : GS α) (L : Lin) (hl : AllInv s.q.r.lo) (hh : AllInv s.q.r.hi) :
    stepOK u s L := by
  obtain ⟨w1, w2⟩ := wave_ok s.q.r.G u.1 u.2.1 s.q.r.lo hl
  obtain ⟨v1, v2⟩ := wave_ok s.q.r.G u.1 u.2.2 s.q.r.hi hh
  exact ⟨w1, v1, retire_ok _ _ w2 v2⟩

/-- Mirror of `LiteralE7a.heapLoop` (the bottom-up heapify of the initialisation). -/
def hlOK {ι β : Type*} [DecidableEq ι] [LinearOrder β] : ℕ → Heap ι β → Prop
  | 0, _ => True
  | j + 1, H => doneDn (Nat.clog 2 H.n) H j ∧ hlOK j (HeapImpl.siftDown (Nat.clog 2 H.n) H j).1

lemma hl_ok {ι β : Type*} [DecidableEq ι] [LinearOrder β] : ∀ (j : ℕ) (H : Heap ι β), hlOK j H := by
  intro j
  induction j with
  | zero => intro _; trivial
  | succ j ih => intro H; exact ⟨heapLoop_done H j, ih _⟩

end HeapRun

section HeapRunR

variable {α : Type*} [LinearOrder α] [OrderBot α]
variable {R : SelRun α} {m0 : ℕ → Bool} {c0 : ℕ → ℕ} {φ : α → ℝ} {ε : ℝ} {L0 : Lin}

/-- **Every sift executed in the run terminates within its fuel `⌈log₂ n⌉`**: in every
rollout `t + 1` of the linked engine (before every stopping time, indeed for every `t`), all
sifts of its two waves and of its retirement pass; and every sift of every bottom-up
heapify (`HeapB.heapify`, called by the initialisation pass for each gate). -/
theorem sifts_done (hL : Abs L0 R.G0) :
    (∀ t, stepOK (R.u (t + 1)) (hpreL R m0 c0 φ ε L0 t).x.s (hpreL R m0 c0 φ ε L0 t).L) ∧
    (∀ (cs : List ℕ) (k : ℕ → α), hlOK cs.length (HeapB.ofKeys cs k)) := by
  refine ⟨fun t => ?_, fun cs k => hl_ok _ _⟩
  obtain ⟨i1, i2, -⟩ := simL_all (m0 := m0) (c0 := c0) (φ := φ) (ε := ε) hL t
  obtain ⟨p1, -, -⟩ := hpreL_eq t ⟨i1, i2⟩
  have hs : (hpreL R m0 c0 φ ε L0 t).x.s.q = hpreR R t := by
    rw [p1, (stepP R m0 c0 t).1]; exact (hpreG_q R m0 t (simG_all R m0 t).1).1
  have hsim := (simR_all R t).2
  rw [← hs] at hsim
  exact step_ok _ _ _ (fun p => (hsim.r.lo.hp p).inv) (fun p => (hsim.r.hi.hp p).inv)

end HeapRunR


open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)
open Asymptotics

/-! ## 11. Total work and `prop:representation-cost` for the linked engine -/

section InitX

variable {ι β : Type*} [DecidableEq ι] [LinearOrder β]

/-- `LiteralE7a.HeapB.heapLoop` with its exit test charged one unit. -/
def heapLoopX : ℕ → Heap ι β → Heap ι β × ℕ
  | 0, H => (H, 1)
  | j + 1, H => ((heapLoopX j (HeapImpl.siftDown (Nat.clog 2 H.n) H j).1).1,
      (HeapImpl.siftDown (Nat.clog 2 H.n) H j).2
        + (heapLoopX j (HeapImpl.siftDown (Nat.clog 2 H.n) H j).1).2)

lemma heapLoopX_eq : ∀ (j : ℕ) (H : Heap ι β),
    heapLoopX j H = ((HeapB.heapLoop j H).1, (HeapB.heapLoop j H).2 + 1) := by
  intro j
  induction j with
  | zero => intro H; rfl
  | succ j ih =>
    intro H
    rw [heapLoopX, ih]
    show _ = ((HeapB.heapLoop j (HeapImpl.siftDown (Nat.clog 2 H.n) H j).1).1,
      (HeapImpl.siftDown (Nat.clog 2 H.n) H j).2
        + (HeapB.heapLoop j (HeapImpl.siftDown (Nat.clog 2 H.n) H j).1).2 + 1)
    simp only [Prod.mk.injEq, true_and]; omega

variable [Inhabited ι]

/-- `LiteralE7a.HeapB.heapify` with the exit test of its loop charged. -/
def heapifyX (cs : List ι) (k : ι → β) : Heap ι β × ℕ :=
  ((heapLoopX cs.length (HeapB.ofKeys cs k)).1,
    cs.length + 1 + (heapLoopX cs.length (HeapB.ofKeys cs k)).2)

lemma heapifyX_eq (cs : List ι) (k : ι → β) :
    heapifyX cs k = ((HeapB.heapify cs k).1, (HeapB.heapify cs k).2 + 1) := by
  unfold heapifyX HeapB.heapify; rw [heapLoopX_eq]; simp only [Prod.mk.injEq, true_and]; omega

end InitX

section InitPassX

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- `LiteralE7a.initGateB` with `heapifyX`. -/
def initGateBX (G : Dag) (g : ℕ) (s : HEState α) : HEState α × ℕ :=
  (⟨fun g' => if g' = g then findMax (heapifyX (G.children g) s.val).1 else s.val g',
    Function.update s.hp g (heapifyX (G.children g) s.val).1⟩,
   (heapifyX (G.children g) s.val).2 + 1)

/-- `LiteralE7a.initPassB` with `initGateBX` and its exit test charged. -/
def initPassBX (G : Dag) : List ℕ → HEState α → HEState α × ℕ
  | [], s => (s, 1)
  | g :: rest, s =>
    ((initPassBX G rest (initGateBX G g s).1).1,
     (initGateBX G g s).2 + (initPassBX G rest (initGateBX G g s).1).2)

lemma initPassBX_eq (G : Dag) : ∀ (l : List ℕ) (s : HEState α),
    initPassBX G l s = ((initPassB G l s).1, (initPassB G l s).2 + l.length + 1) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons g l ih =>
    intro s
    have hg : initGateBX G g s = ((initGateB G g s).1, (initGateB G g s).2 + 1) := by
      unfold initGateBX initGateB; rw [heapifyX_eq]
    rw [initPassBX, hg, ih]
    show _ = ((initPassB G l (initGateB G g s).1).1,
      (initGateB G g s).2 + (initPassB G l (initGateB G g s).1).2 + (l.length + 1) + 1)
    simp only [Prod.mk.injEq, true_and]; omega

end InitPassX

section Final

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Initial contents of all arrays of the linked engine (arbitrary): mark table, count
table, and the arrays of the incidence structure and its construction. -/
structure Mem where
  m0 : ℕ → Bool
  c0 : ℕ → ℕ
  B0 : RB
  C0 : DL
  P0 : DL
  T0 : ℕ → ℕ

variable (R : SelRun α) (μ : Mem) (φ : α → ℝ) (ε : ℝ)

/-- The incidence structure built from the initial circuit. -/
def L0 : Lin := (buildLin R.G0 μ.B0 μ.C0 μ.P0 μ.T0).1

/-- State of the linked engine after `t` rollouts. -/
noncomputable def runL (t : ℕ) : LS α := hrunL R μ.m0 μ.c0 φ ε (L0 R μ) t

/-- State of the linked engine before the waves of rollout `t + 1`. -/
noncomputable def preLt (t : ℕ) : LS α := hpreL R μ.m0 μ.c0 φ ε (L0 R μ) t

/-- Executed cost of the two initialisation passes (`initPassBX`); they compute the
initial heaps and values of `LiteralK10.hq0B` (`initPassBX_eq`). -/
def WinitL : ℕ := (initPassBX R.G0 R.order R.hl).2 + (initPassBX R.G0 R.order R.hu).2

/-- **Total work of the linked engine**: the given `P` and `R.H`, the executed initialisation
of the heaps (`WinitL`), the executed constructions of the mark table, the count table
and the incidence structure, the executed cost of all rollouts and queries, and the executed
final disposal. -/
noncomputable def WL : ℕ :=
  R.P + R.H + WinitL R + WmarkL R μ.m0 + WcntL R μ.c0 + (buildLin R.G0 μ.B0 μ.C0 μ.P0 μ.T0).2
    + WrollL R μ.m0 μ.c0 φ ε (L0 R μ) + WlastL R μ.m0 μ.c0 φ ε (L0 R μ)
    + WdispL R μ.m0 μ.c0 φ ε (L0 R μ)

variable {R}

theorem L0_spec (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N) :
    AbsR (L0 R μ) R.G0 (lcF R.G0) (lpF R.G0) ∧ (L0 R μ).N = R.G0.N ∧ (L0 R μ).M = live R.G0 ∧
    (buildLin R.G0 μ.B0 μ.C0 μ.P0 μ.T0).2 = 15 * live R.G0 + 10 * R.G0.N + 3 :=
  buildLin_spec R.G0 R.wf R.nodup hcl μ.B0 μ.C0 μ.P0 μ.T0

/-- **`WL` against `LiteralG2.WP`**: `WP ≤ WL ≤ 11 · WP + 10 τ + 15 · live + 12 N + 13`. -/
theorem WL_bounds (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N) :
    WP R μ.m0 μ.c0 ≤ WL R μ φ ε ∧
    WL R μ φ ε ≤ 11 * WP R μ.m0 μ.c0 + 10 * R.τ + 15 * live R.G0 + 12 * R.G0.N + 13 := by
  obtain ⟨l1, l2, -, l4⟩ := L0_spec μ hcl
  obtain ⟨w1, w2, w3, w4, w5, w6, -, w8, w9⟩ := W_parts (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε)
    ⟨_, _, l1⟩ l2
  have hi : WinitL R = WinitB R + 2 * R.order.length + 2 := by
    unfold WinitL WinitB; rw [initPassBX_eq, initPassBX_eq]; ring
  have ho := R.order_length_le
  unfold WL WP
  rw [w8, w9, l4, hi]
  constructor <;> omega

/-- `WL ≤ 292 · XD + 11 · K` (no further hypothesis). -/
theorem WL_le (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N) :
    WL R μ φ ε ≤ 292 * XD R + 11 * R.K := by
  have h1 := (WL_bounds μ φ ε hcl).2
  have h2 := WP_le R μ.m0 μ.c0
  have hN : 1 ≤ R.G0.N := by have := (R.hn 0).1; omega
  have hX : R.τ + R.G0.N + live R.G0 ≤ XD R := by unfold XD Hsh; omega
  omega

/-- **`WL ≤ 303 · XD`** if some query occurs by time `τ`. -/
theorem WL_le_query (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hq : ∃ t, t ≤ R.τ ∧ R.q t = true) : WL R μ φ ε ≤ 303 * XD R := by
  have h1 := (WL_bounds μ φ ε hcl).2
  have h2 := WP_le_query R μ.m0 μ.c0 hq
  have hN : 1 ≤ R.G0.N := by have := (R.hn 0).1; omega
  have hX : R.τ + R.G0.N + live R.G0 ≤ XD R := by unfold XD Hsh; omega
  omega

/-- **`WL ≤ 303 · XD`** when the root actions are distinct gates `< N`. -/
theorem WL_le_inj (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    WL R μ φ ε ≤ 303 * XD R := by
  have h1 := (WL_bounds μ φ ε hcl).2
  have h2 := WP_le_inj R μ.m0 μ.c0 hlt hinj
  have hN : 1 ≤ R.G0.N := by have := (R.hn 0).1; omega
  have hX : R.τ + R.G0.N + live R.G0 ≤ XD R := by unfold XD Hsh; omega
  omega

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, for the linked engine.**
Hypotheses: the fields of `R : LiteralK3.SelRun α`, the children of `G0` are gates
(`c ∈ children p → c < N`, as in the description of `CostEngines.Dag`; `Dag.WF` states it
only for parents), any stop rule `φ, ε`, any initial array contents `μ`.  Conclusions:

0. the initial heaps, values, mark table and count table are those computed by the executed
   initialisation passes (`initPassBX`, `clearMarksX`, `zeroAllX`, `incAllX`);
1. at every time the linked engine's state is that of `LiteralG2.runSP` (hence of
   `LiteralG2.runSG`, `LiteralF4.runSR`, and represents the abstract run `R.run t`; before
   the waves, `R.pre t`, whose root-reachable live incidences `F_t` are the live incidences
   of the engine's circuit);
2. **simulation of the incidence structure**: at every time, before and after queries,
   following the next pointers from the heads reads back exactly the child and parent lists
   of the engine's circuit for every gate `< N`;
3. the query outputs (executed leader and stop scans) are `RetireFinal.qOut`;
4. every sift executed in every rollout, and in every heapify, terminates within its fuel;
5. the construction of the incidence structure represents `G0` and costs
   `15 · live + 10 N + 3`; after the final disposal no incidence is left;
6. `S^+ ≤ WrollL` and `WP ≤ WL ≤ 11 · WP + 10 τ + 15 · live + 12 N + 13`;
7. `WL ≤ 292 · XD + 11 K`, and `WL ≤ 303 · XD` if some query occurs by time `τ` or if the
   root actions are distinct gates `< N`. -/
theorem representation_cost_upper_Lin (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N) :
    ((hq0B R).r.lo = (initPassBX R.G0 R.order R.hl).1 ∧
      (hq0B R).r.hi = (initPassBX R.G0 R.order R.hu).1 ∧
      (gs0 R μ.m0).marks = (clearMarksX (List.range R.G0.N) μ.m0).1 ∧
      (initCnt R μ.c0).1
        = (incAllX ((List.range R.K).map R.rt) (zeroAllX (List.range R.G0.N) μ.c0).1).1) ∧
    (∀ t, (runL R μ φ ε t).x = hrunP R μ.m0 μ.c0 t ∧ (preLt R μ φ ε t).x = hpreP R μ.m0 μ.c0 t ∧
      (runL R μ φ ε t).x.s = hrunG R μ.m0 t ∧ (runL R μ φ ε t).x.s.q = hrunR R t ∧
      SimQ (runL R μ φ ε t).x.s.q (R.run t) ∧ SimQ (preLt R μ φ ε t).x.s.q (R.pre t) ∧
      R.F t = liveInc (preLt R μ φ ε t).x.s.q.r.G) ∧
    (∀ t g, g < R.G0.N →
      (travE (runL R μ φ ε t).L.C.nx ((runL R μ φ ε t).L.M + 1) ((runL R μ φ ε t).L.C.hd g)).1.map
          (runL R μ φ ε t).L.dst = (runL R μ φ ε t).x.s.q.r.G.children g ∧
      (travE (runL R μ φ ε t).L.P.nx ((runL R μ φ ε t).L.M + 1) ((runL R μ φ ε t).L.P.hd g)).1.map
          (runL R μ φ ε t).L.src = (runL R μ φ ε t).x.s.q.r.G.parents g ∧
      (travE (preLt R μ φ ε t).L.C.nx ((preLt R μ φ ε t).L.M + 1) ((preLt R μ φ ε t).L.C.hd g)).1.map
          (preLt R μ φ ε t).L.dst = (preLt R μ φ ε t).x.s.q.r.G.children g ∧
      (travE (preLt R μ φ ε t).L.P.nx ((preLt R μ φ ε t).L.M + 1) ((preLt R μ φ ε t).L.P.hd g)).1.map
          (preLt R μ φ ε t).L.src = (preLt R μ φ ε t).x.s.q.r.G.parents g) ∧
    (∀ t, qOutL φ ε R.K R.rt (runL R μ φ ε t).x.s.q
      = qOut φ ε R.K (fun i => (runL R μ φ ε t).x.s.q.r.lo.val (R.rt i))
          (fun i => (runL R μ φ ε t).x.s.q.r.hi.val (R.rt i)) (runL R μ φ ε t).x.s.q.act) ∧
    (∀ t, stepOK (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L) ∧
    (∀ (cs : List ℕ) (k : ℕ → α), hlOK cs.length (HeapB.ofKeys cs k)) ∧
    AbsR (L0 R μ) R.G0 (lcF R.G0) (lpF R.G0) ∧
    (buildLin R.G0 μ.B0 μ.C0 μ.P0 μ.T0).2 = 15 * live R.G0 + 10 * R.G0.N + 3 ∧
    (∀ p, (disposeL (List.range R.G0.N) ((preLt R μ φ ε R.τ).x.s.q.r,
      (preLt R μ φ ε R.τ).L)).1.1.G.children p = []) ∧
    R.Splus ≤ WrollL R μ.m0 μ.c0 φ ε (L0 R μ) ∧
    WP R μ.m0 μ.c0 ≤ WL R μ φ ε ∧
    WL R μ φ ε ≤ 11 * WP R μ.m0 μ.c0 + 10 * R.τ + 15 * live R.G0 + 12 * R.G0.N + 13 ∧
    WL R μ φ ε ≤ 292 * XD R + 11 * R.K ∧
    ((∃ t, t ≤ R.τ ∧ R.q t = true) → WL R μ φ ε ≤ 303 * XD R) ∧
    ((∀ i, i < R.K → R.rt i < R.G0.N) →
      (∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) → WL R μ φ ε ≤ 303 * XD R) := by
  obtain ⟨l1, l2, -, l4⟩ := L0_spec μ hcl
  have hL : Abs (L0 R μ) R.G0 := ⟨_, _, l1⟩
  have hG := representation_cost_upper_G R μ.m0
  have hP := representation_cost_upper_P R μ.m0 μ.c0
  have hpre : ∀ t, (preLt R μ φ ε t).x = hpreP R μ.m0 μ.c0 t ∧
      Abs (preLt R μ φ ε t).L (hpreP R μ.m0 μ.c0 t).s.q.r.G ∧ (preLt R μ φ ε t).L.N = R.G0.N := by
    intro t
    obtain ⟨i1, i2, i3⟩ := simL_all (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL t
    obtain ⟨p1, p2, p3⟩ := hpreL_eq t ⟨i1, i2⟩
    exact ⟨p1, p2, by rw [show (preLt R μ φ ε t).L.N = _ from p3.1, i3.1, l2]⟩
  obtain ⟨-, -, -, -, -, -, d7, -, -⟩ := W_parts (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL l2
  obtain ⟨x1, -, x3, -⟩ := initX_eq R μ.m0 μ.c0
  refine ⟨⟨by rw [initPassBX_eq]; rfl, by rw [initPassBX_eq]; rfl, x1.symm, x3.symm⟩,
    fun t => ?_, fun t g hg => ?_, fun t => qOutL_eq _ _ _ _ _, (sifts_done (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL).1,
    (sifts_done (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL).2, l1, l4, fun p => ?_, ?_, (WL_bounds μ φ ε hcl).1, (WL_bounds μ φ ε hcl).2,
    WL_le μ φ ε hcl, WL_le_query μ φ ε hcl, WL_le_inj μ φ ε hcl⟩
  · obtain ⟨i1, -, -⟩ := simL_all (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL t
    have p1 := (hpre t).1
    obtain ⟨a1, -, -, b1, -⟩ := hP.1 t
    obtain ⟨g1, g2, g3, -⟩ := hG.1 t
    refine ⟨i1, p1, by rw [show (runL R μ φ ε t).x = _ from i1, a1], ?_, ?_, ?_, ?_⟩
    · show (runL R μ φ ε t).x.s.q = _; rw [show (runL R μ φ ε t).x = _ from i1, a1, g1]
    · show SimQ (runL R μ φ ε t).x.s.q _; rw [show (runL R μ φ ε t).x = _ from i1, a1]; exact g2
    · rw [p1, b1]; exact g3
    · rw [p1, b1]; exact hG.2.1 t
  · obtain ⟨i1, ⟨lc, lp, hr⟩, i3⟩ := simL_all (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL t
    obtain ⟨-, ⟨lc', lp', hr'⟩, -⟩ := hpre t
    have hgN : g < (runL R μ φ ε t).L.N := by
      rw [show (runL R μ φ ε t).L.N = _ from i3.1, l2]; exact hg
    have hgN' : g < (preLt R μ φ ε t).L.N := by rw [(hpre t).2.2]; exact hg
    obtain ⟨r1, r2, -, -⟩ := hr.readback hgN
    obtain ⟨s1, s2, -, -⟩ := hr'.readback hgN'
    have e1 : (runL R μ φ ε t).x.s.q.r.G = (hrunP R μ.m0 μ.c0 t).s.q.r.G := by
      rw [show (runL R μ φ ε t).x = _ from i1]
    have e2 : (preLt R μ φ ε t).x.s.q.r.G = (hpreP R μ.m0 μ.c0 t).s.q.r.G := by
      rw [(hpre t).1]
    rw [e1, e2]
    exact ⟨r1, r2, s1, s2⟩
  · show (disposeL _ ((hpreL R μ.m0 μ.c0 φ ε (L0 R μ) R.τ).x.s.q.r,
      (hpreL R μ.m0 μ.c0 φ ε (L0 R μ) R.τ).L)).1.1.G.children p = []
    rw [d7]
    have := hG.2.2.2.2.2.2.1 p
    rw [← (stepP R μ.m0 μ.c0 R.τ).1] at this
    exact this
  · have h1 := hP.2.2.2.2.1
    have h2 := (W_parts (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL l2).1
    unfold WrollL at h2 ⊢
    exact h1.trans h2

/-- **`eq:prop-rep-upper` in `O` form** for the linked engine, root actions being distinct
gates `< N` and children gates in every run. -/
theorem representation_cost_upper_isBigO_Lin {ι : Type*} {l : Filter ι} (G : ι → SelRun α)
    (μ : ι → Mem) (φ : ι → α → ℝ) (ε : ι → ℝ)
    (hcl : ∀ i p c, c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j) :
    (fun i => (WL (G i) (μ i) (φ i) (ε i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) := by
  apply IsBigO.of_bound 303
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast WL_le_inj (μ i) (φ i) (ε i) (hcl i) (hlt i) (hinj i)

/-- **`prop:representation-cost` as one theorem** for the linked engine (total work
`W_G = WL`), when in every run the children are gates and the root actions are distinct
gates `< N`: `W_G ≤ 303 X_G`, hence `W_G = O(X_G)`; `P_C + S_C^- ≤ W_C`; condition (R),
`X_G = o(P_C + S_C^-)`, implies `W_G = o(W_C)`. -/
theorem representation_cost_Lin {β Cell ι : Type*} [DecidableEq β] [DecidableEq Cell]
    {l : Filter ι} (G : ι → SelRun α) (μ : ι → Mem) (φ : ι → α → ℝ) (ε : ι → ℝ)
    (hcl : ∀ i p c, c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j)
    (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WL (G i) (μ i) (φ i) (ε i) ≤ 303 * XD (G i)) ∧
    (fun i => (WL (G i) (μ i) (φ i) (ε i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WL (G i) (μ i) (φ i) (ε i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  have hG := representation_cost_upper_isBigO_Lin (l := l) G μ φ ε hcl hlt hinj
  exact ⟨fun i => WL_le_inj (μ i) (φ i) (ε i) (hcl i) (hlt i) (hinj i), hG, fun i => (C i).lower,
    fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)** for the linked engine: against the retirement engine itself as
the compiled representation (`LiteralK4.engineImpl`). -/
theorem condition_R_engine_Lin {β ι : Type*} [LinearOrder β] [OrderBot β] {l : Filter ι}
    (G : ι → SelRun α) (μ : ι → Mem) (φ : ι → α → ℝ) (ε : ι → ℝ)
    (hcl : ∀ i p c, c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j)
    (RC : ι → EngineRun β)
    (hR : (fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WL (G i) (μ i) (φ i) (ε i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
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
  have h1 := (representation_cost_Lin (l := l) G μ φ ε hcl hlt hinj
    (fun i => LiteralK4.engineImpl (RC i))).2.2.2 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast LiteralK4.engineImpl_W_le (RC i)

end Final


end LiteralG4
end JointRootCert
