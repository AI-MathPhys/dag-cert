/-
Joint Root Certification: linear-time construction of the implemented indexed heap.

Manuscript result supported:

* `thm:adaptive-oracle-coupling` / `thm:charged-dual-cover`, the `B + M + K` terms of
  `eq:dual-cover-work`: the heaps of the dual-cover index are initialised in time linear in
  their sizes.  `HeapImpl.insertAll` builds a heap by successive insertions in
  `m (⌈log₂ m⌉ + 2)` steps; this file implements the bottom-up construction (load the
  entries into the arrays, then sift down every position from the last to the first) on the
  representation `HeapImpl.Heap` and proves that it returns a valid heap storing exactly the
  given entries in at most `6 m` steps (`build_spec`).

## Cost model

As in `HeapImpl.lean`: a program returns `(result, cost)`, the cost computed by the same
recursion.  Charges: one unit per loaded entry (`loadAll`: the writes of handle, key and
position), and the computed cost of every `HeapImpl.siftDown` (one unit per visited
position).  The sift-down from position `i` runs with fuel `⌈log₂ n⌉ - ⌊log₂ (i + 1)⌋`, the
number of tree levels below the level of `i`.
-/
import JointRootCert.HeapImpl

namespace JointRootCert
namespace LiteralK7a

open Finset
open HeapImpl

/-! ## Partial heap order -/

section Order

variable {α : Type*} [LinearOrder α]

/-- Heap order between every position and its parent, for parents at positions `≥ t`:
the subtrees rooted at positions `≥ t` are heaps. -/
def OrdFrom (t n : ℕ) (k : ℕ → α) : Prop :=
  ∀ i, 0 < i → i < n → t ≤ par i → k i ≤ k (par i)

/-- `OrdFrom t` except possibly between `j` and its children; the children of `j` are below
the parent of `j` when that parent is at a position `≥ t`. -/
def OrdDnP (t n : ℕ) (k : ℕ → α) (j : ℕ) : Prop :=
  (∀ i, 0 < i → i < n → t ≤ par i → par i ≠ j → k i ≤ k (par i)) ∧
  (∀ i, 0 < i → i < n → par i = j → 0 < j → t ≤ par j → k i ≤ k (par j))

lemma ordFrom_zero {n : ℕ} {k : ℕ → α} (h : OrdFrom 0 n k) : Ord n k :=
  fun i hi hin => h i hi hin (Nat.zero_le _)

lemma ordFrom_top {n : ℕ} (k : ℕ → α) : OrdFrom n n k := by
  intro i hi hin ht
  have := par_lt hi
  omega

lemma ordFrom_start {n : ℕ} {k : ℕ → α} {j : ℕ} (h : OrdFrom (j + 1) n k) :
    OrdDnP j n k j := by
  constructor
  · intro i hi hin ht hne
    exact h i hi hin (by omega)
  · intro i _ _ _ hj ht
    have := par_lt hj
    omega

lemma ordDnP_done {t n : ℕ} {k : ℕ → α} {j : ℕ} (h : OrdDnP t n k j)
    (hj : ∀ i, 0 < i → i < n → par i = j → k i ≤ k j) : OrdFrom t n k := by
  intro i hi hin ht
  by_cases hp : par i = j
  · rw [hp]; exact hj i hi hin hp
  · exact h.1 i hi hin ht hp

lemma ordDnP_swap {t n : ℕ} {k : ℕ → α} {j m : ℕ} (h : OrdDnP t n k j) (htj : t ≤ j)
    (hm : 0 < m) (hmn : m < n) (hpm : par m = j) (hlt : k j < k m)
    (hbig : ∀ i, 0 < i → i < n → par i = j → k i ≤ k m) : OrdDnP t n (swapK k j m) m := by
  have hjm : j < m := hpm ▸ par_lt hm
  have e1 : swapK k j m j = k m := by simp [swapK]
  have e2 : swapK k j m m = k j := by
    unfold swapK; rw [ite_eq_right (by omega), ite_eq_left rfl]
  have e3 : ∀ i, i ≠ j → i ≠ m → swapK k j m i = k i := by
    intro i h1 h2; unfold swapK; rw [ite_eq_right h1, ite_eq_right h2]
  constructor
  · intro i hi hin ht hne
    by_cases him : i = m
    · rw [him, e2, hpm, e1]; exact hlt.le
    · by_cases hij : i = j
      · have hj0 : 0 < j := hij ▸ hi
        have hpj := par_lt hj0
        rw [hij, e1, e3 _ (by omega) (by omega)]
        exact h.2 m hm hmn hpm hj0 (by rw [← hij]; exact ht)
      · rw [e3 i hij him]
        by_cases hp : par i = j
        · rw [hp, e1]; exact hbig i hi hin hp
        · rw [e3 _ hp hne]
          exact h.1 i hi hin ht hp
  · intro i hi hin hp _ _
    have hij : i ≠ j := by have := par_lt hi; omega
    have him : i ≠ m := by have := par_lt hi; omega
    rw [e3 i hij him, hpm, e1]
    have := h.1 i hi hin (by omega) (by omega)
    rwa [hp] at this

end Order

/-! ## Sift-down inside a partially ordered array -/

section Build

variable {ι α : Type*} [DecidableEq ι] [LinearOrder α]

/-- **Sift-down in a partial heap.**  If the subtrees rooted at positions `≥ t` are heaps
except at `j ≥ t`, sifting down from `j` with enough fuel makes all of them heaps; the
position map stays consistent and the stored handle-to-key map and the size are unchanged. -/
theorem siftDown_partial : ∀ (d : ℕ) (H : Heap ι α) (j t : ℕ), H.PosOK →
    OrdDnP t H.n H.ky j → t ≤ j → j < H.n → H.n ≤ (j + 1) * 2 ^ d →
    (siftDown d H j).1.PosOK ∧ OrdFrom t H.n (siftDown d H j).1.ky ∧
      (siftDown d H j).1.n = H.n ∧ ∀ h, (siftDown d H j).1.lookup h = H.lookup h := by
  intro d
  induction d with
  | zero =>
    intro H j t hP hO _ hj hd
    refine ⟨hP, ordDnP_done hO ?_, rfl, fun _ => rfl⟩
    intro i hi hin hp
    exfalso
    have := (par_eq_iff hi).1 hp
    simp at hd
    omega
  | succ d ih =>
    intro H j t hP hO htj hj hd
    rw [siftDown]
    by_cases hc : 2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j)
    · rw [ite_eq_left hc]
      obtain ⟨hm0, hmn, hpm, hbig⟩ := bigChild_spec H j hc.1
      have hjm : j < bigChild H j := by
        have := par_lt hm0
        rw [hpm] at this
        exact this
      have hP' := Heap.swap_posOK hP hj hmn (by omega)
      have hfuel : H.n ≤ (bigChild H j + 1) * 2 ^ d := by
        have h1 : 2 * (j + 1) ≤ bigChild H j + 1 := by
          have := (par_eq_iff hm0).1 hpm; omega
        calc H.n ≤ (j + 1) * 2 ^ (d + 1) := hd
          _ = 2 * (j + 1) * 2 ^ d := by ring
          _ ≤ (bigChild H j + 1) * 2 ^ d := Nat.mul_le_mul_right _ h1
      obtain ⟨h1, h2, h3, h4⟩ := ih (H.swap j (bigChild H j)) (bigChild H j) t hP'
        (ordDnP_swap hO htj hm0 hmn hpm hc.2 hbig) (by omega) hmn hfuel
      refine ⟨h1, h2, h3, fun h => ?_⟩
      rw [h4 h]
      exact Heap.swap_lookup hP hj hmn (by omega) h
    · rw [ite_eq_right hc]
      refine ⟨hP, ordDnP_done hO ?_, rfl, fun _ => rfl⟩
      intro i hi hin hp
      have hl : 2 * j + 1 < H.n := by
        have := (par_eq_iff hi).1 hp; omega
      obtain ⟨_, _, _, hbig⟩ := bigChild_spec H j hl
      refine (hbig i hi hin hp).trans ?_
      by_contra hlt
      exact hc ⟨hl, lt_of_not_ge hlt⟩

/-! ## Loading the arrays -/

omit [LinearOrder α] in
lemma append_posOK {H : Heap ι α} (hP : H.PosOK) (h : ι) (x : α) (hh : H.pos h = none) :
    (H.append h x).PosOK := by
  constructor
  · intro i hi
    show Function.update H.pos h (some H.n) (Function.update H.hd H.n h i) = some i
    by_cases hin : i = H.n
    · rw [hin, Function.update_self, Function.update_self]
    · have hi' : i < H.n := by
        have : i < H.n + 1 := hi
        omega
      have hne : H.hd i ≠ h := fun e => by
        have := hP.fwd i hi'
        rw [e, hh] at this
        simp at this
      rw [Function.update_of_ne hin, Function.update_of_ne hne]
      exact hP.fwd i hi'
  · intro h' i hpi
    change Function.update H.pos h (some H.n) h' = some i at hpi
    show i < H.n + 1 ∧ Function.update H.hd H.n h i = h'
    by_cases he : h' = h
    · rw [he, Function.update_self] at hpi
      have : H.n = i := Option.some.inj hpi
      rw [← this, Function.update_self]
      exact ⟨by omega, he.symm⟩
    · rw [Function.update_of_ne he] at hpi
      obtain ⟨h3, h4⟩ := hP.bwd h' i hpi
      rw [Function.update_of_ne (by omega)]
      exact ⟨by omega, h4⟩

omit [LinearOrder α] in
lemma append_lookup {H : Heap ι α} (hP : H.PosOK) (h : ι) (x : α) (h' : ι) :
    (H.append h x).lookup h' = if h' = h then some x else H.lookup h' := by
  show Option.map (Function.update H.ky H.n x) (Function.update H.pos h (some H.n) h') = _
  by_cases he : h' = h
  · rw [ite_eq_left he, he, Function.update_self]
    simp
  · rw [ite_eq_right he, Function.update_of_ne he]
    unfold Heap.lookup
    cases hp' : H.pos h' with
    | none => rfl
    | some i' =>
      have := (hP.bwd h' i' hp').1
      simp [Function.update_of_ne (show i' ≠ H.n by omega)]

/-- **Load** a list of entries at the end of the arrays, without restoring the heap order:
one unit per entry. -/
def loadAll (H : Heap ι α) : List (ι × α) → Heap ι α × ℕ
  | [] => (H, 0)
  | e :: es => ((loadAll (H.append e.1 e.2) es).1, (loadAll (H.append e.1 e.2) es).2 + 1)

omit [LinearOrder α] in
theorem loadAll_spec : ∀ (es : List (ι × α)) (H : Heap ι α), H.PosOK →
    (es.map Prod.fst).Nodup → (∀ e ∈ es, H.pos e.1 = none) →
    (loadAll H es).1.PosOK ∧ (loadAll H es).1.n = H.n + es.length ∧
    (∀ e ∈ es, (loadAll H es).1.lookup e.1 = some e.2) ∧
    (∀ h, h ∉ es.map Prod.fst → (loadAll H es).1.lookup h = H.lookup h) ∧
    (loadAll H es).2 = es.length := by
  intro es
  induction es with
  | nil => intro H hP _ _; exact ⟨hP, rfl, fun e he => by simp at he, fun _ _ => rfl, rfl⟩
  | cons e es ih =>
    intro H hP hnd habs
    rw [List.map_cons, List.nodup_cons] at hnd
    have hP1 := append_posOK hP e.1 e.2 (habs e List.mem_cons_self)
    have habs' : ∀ e' ∈ es, (H.append e.1 e.2).pos e'.1 = none := by
      intro e' he'
      have hne : e'.1 ≠ e.1 := fun eq => hnd.1 (eq ▸ List.mem_map_of_mem he')
      show Function.update H.pos e.1 (some H.n) e'.1 = none
      rw [Function.update_of_ne hne]
      exact habs e' (List.mem_cons_of_mem _ he')
    obtain ⟨g1, g2, g3, g4, g5⟩ := ih (H.append e.1 e.2) hP1 hnd.2 habs'
    refine ⟨g1, ?_, ?_, ?_, ?_⟩
    · show (loadAll (H.append e.1 e.2) es).1.n = _
      rw [g2, List.length_cons]
      show H.n + 1 + es.length = _
      omega
    · intro e' he'
      show (loadAll (H.append e.1 e.2) es).1.lookup e'.1 = _
      rcases List.mem_cons.1 he' with rfl | he'
      · rw [g4 _ hnd.1, append_lookup hP, ite_eq_left rfl]
      · exact g3 e' he'
    · intro h hm
      show (loadAll (H.append e.1 e.2) es).1.lookup h = _
      rw [List.map_cons, List.mem_cons, not_or] at hm
      rw [g4 h hm.2, append_lookup hP, ite_eq_right hm.1]
    · show (loadAll (H.append e.1 e.2) es).2 + 1 = _
      rw [g5, List.length_cons]

/-! ## Bottom-up heap construction -/

/-- Fuel of the sift-down from position `i` in an array of `n` entries. -/
def fuelAt (n i : ℕ) : ℕ := Nat.clog 2 n - Nat.log 2 (i + 1)

lemma fuelAt_ok {n i : ℕ} (hi : i < n) : n ≤ (i + 1) * 2 ^ fuelAt n i := by
  have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  have h2 : 2 ^ Nat.log 2 (i + 1) ≤ i + 1 := Nat.pow_log_le_self 2 (by omega)
  have h3 : Nat.log 2 (i + 1) ≤ Nat.clog 2 n := by
    by_contra hlt
    have h4 : 2 ^ (Nat.clog 2 n + 1) ≤ 2 ^ Nat.log 2 (i + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (Nat.clog 2 n + 1) = 2 * 2 ^ Nat.clog 2 n := by ring
    omega
  unfold fuelAt
  calc n ≤ 2 ^ Nat.clog 2 n := h1
    _ = 2 ^ Nat.log 2 (i + 1) * 2 ^ (Nat.clog 2 n - Nat.log 2 (i + 1)) := by
        rw [← pow_add, Nat.add_sub_cancel' h3]
    _ ≤ (i + 1) * 2 ^ (Nat.clog 2 n - Nat.log 2 (i + 1)) := Nat.mul_le_mul_right _ h2

/-- **Bottom-up loop**: sift down the positions `i - 1, i - 2, …, 0` in turn. -/
def heapLoop : ℕ → Heap ι α → Heap ι α × ℕ
  | 0, H => (H, 0)
  | i + 1, H =>
    ((heapLoop i (siftDown (fuelAt H.n i) H i).1).1,
     (siftDown (fuelAt H.n i) H i).2 + (heapLoop i (siftDown (fuelAt H.n i) H i).1).2)

theorem heapLoop_spec : ∀ (i : ℕ) (H : Heap ι α), H.PosOK → i ≤ H.n → OrdFrom i H.n H.ky →
    (heapLoop i H).1.Inv ∧ (heapLoop i H).1.n = H.n ∧
    (∀ h, (heapLoop i H).1.lookup h = H.lookup h) ∧
    (heapLoop i H).2 ≤ ∑ j ∈ range i, (fuelAt H.n j + 1) := by
  intro i
  induction i with
  | zero =>
    intro H hP _ hO
    exact ⟨⟨hP, ordFrom_zero hO⟩, rfl, fun _ => rfl, by simp [heapLoop]⟩
  | succ i ih =>
    intro H hP hi hO
    obtain ⟨s1, s2, s3, s4⟩ := siftDown_partial (fuelAt H.n i) H i i hP (ordFrom_start hO)
      le_rfl (by omega) (fuelAt_ok (by omega))
    obtain ⟨g1, g2, g3, g4⟩ := ih (siftDown (fuelAt H.n i) H i).1 s1 (by rw [s3]; omega)
      (by rw [s3]; exact s2)
    have hc := siftDown_cost (fuelAt H.n i) H i
    refine ⟨g1, g2.trans s3, fun h => (g3 h).trans (s4 h), ?_⟩
    show (siftDown (fuelAt H.n i) H i).2 + (heapLoop i (siftDown (fuelAt H.n i) H i).1).2 ≤ _
    rw [s3] at g4
    rw [sum_range_succ]
    omega

/-- The fuel of all positions sums to less than `4 n` (sum of the heights of a binary
tree). -/
theorem fuel_sum_le (n : ℕ) : ∑ j ∈ range n, fuelAt n j ≤ 4 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : ∀ j ∈ range n, fuelAt n j
      ≤ ∑ k ∈ range (Nat.clog 2 n), (if j + 1 < 2 ^ (k + 1) then 1 else 0) := by
    intro j _
    rw [← card_filter]
    have hsub : Ico (Nat.log 2 (j + 1)) (Nat.clog 2 n)
        ⊆ (range (Nat.clog 2 n)).filter (fun k => j + 1 < 2 ^ (k + 1)) := by
      intro k hk
      rw [mem_Ico] at hk
      rw [mem_filter, mem_range]
      refine ⟨hk.2, ?_⟩
      calc j + 1 < 2 ^ (Nat.log 2 (j + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    exact this
  have h2 : ∀ k ∈ range (Nat.clog 2 n),
      ∑ j ∈ range n, (if j + 1 < 2 ^ (k + 1) then 1 else 0) ≤ 2 ^ (k + 1) := by
    intro k _
    rw [← card_filter]
    have hsub : (range n).filter (fun j => j + 1 < 2 ^ (k + 1)) ⊆ range (2 ^ (k + 1)) := by
      intro j hj
      rw [mem_filter] at hj
      rw [mem_range]
      omega
    have := card_le_card hsub
    rwa [card_range] at this
  have h3 : ∀ L : ℕ, ∑ k ∈ range L, 2 ^ (k + 1) + 2 = 2 ^ (L + 1) := by
    intro L
    induction L with
    | zero => rfl
    | succ L ih =>
      rw [sum_range_succ]
      have : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
      omega
  have h4 := CostModel.segTree_nodes_lt n hn
  calc ∑ j ∈ range n, fuelAt n j
      ≤ ∑ j ∈ range n, ∑ k ∈ range (Nat.clog 2 n), (if j + 1 < 2 ^ (k + 1) then 1 else 0) :=
        sum_le_sum h1
    _ = ∑ k ∈ range (Nat.clog 2 n), ∑ j ∈ range n, (if j + 1 < 2 ^ (k + 1) then 1 else 0) :=
        sum_comm
    _ ≤ ∑ k ∈ range (Nat.clog 2 n), 2 ^ (k + 1) := sum_le_sum h2
    _ ≤ 4 * n := by
        have := h3 (Nat.clog 2 n)
        omega

/-- **Heapify**: restore the heap order of an arbitrary array of entries, bottom-up. -/
def heapify (H : Heap ι α) : Heap ι α × ℕ := heapLoop H.n H

/-- **Correctness and linear cost of heapify.**  On arrays with a consistent position map,
`heapify` returns a valid heap with the same size and the same stored handle-to-key map, in
at most `5 n` steps. -/
theorem heapify_spec (H : Heap ι α) (hP : H.PosOK) :
    (heapify H).1.Inv ∧ (heapify H).1.n = H.n ∧
    (∀ h, (heapify H).1.lookup h = H.lookup h) ∧ (heapify H).2 ≤ 5 * H.n := by
  obtain ⟨g1, g2, g3, g4⟩ := heapLoop_spec H.n H hP le_rfl (ordFrom_top _)
  refine ⟨g1, g2, g3, g4.trans ?_⟩
  rw [sum_add_distrib]
  have := fuel_sum_le H.n
  simp only [sum_const, card_range, smul_eq_mul, mul_one]
  omega

/-- **Linear heap construction**: load the entries into the empty heap, then heapify. -/
def build [Inhabited ι] [OrderBot α] (es : List (ι × α)) : Heap ι α × ℕ :=
  ((heapify (loadAll (Heap.empty : Heap ι α) es).1).1,
   (loadAll (Heap.empty : Heap ι α) es).2 + (heapify (loadAll (Heap.empty : Heap ι α) es).1).2)

/-- **Building a heap for a key table in linear time.**  For a duplicate-free list `es` of
`m` handles and keys `k`, `build` returns a valid heap of `m` entries storing exactly the
keys `k h`, `h ∈ es` (`HeapImpl.Rep`), at computed cost at most `6 m`. -/
theorem build_spec [Inhabited ι] [OrderBot α] (es : List ι) (hnd : es.Nodup) (k : ι → α) :
    Rep (build (es.map (fun h => (h, k h)))).1 es.toFinset k es.length ∧
    (build (es.map (fun h => (h, k h)))).1.n = es.length ∧
    (build (es.map (fun h => (h, k h)))).2 ≤ 6 * es.length := by
  have hmap : (es.map (fun h => (h, k h))).map Prod.fst = es := by
    rw [List.map_map]
    exact List.map_id _
  obtain ⟨l1, l2, l3, l4, l5⟩ := loadAll_spec (es.map (fun h => (h, k h)))
    (Heap.empty : Heap ι α) Heap.empty_inv.posOK (by rw [hmap]; exact hnd) (fun _ _ => rfl)
  have hn0 : (Heap.empty : Heap ι α).n = 0 := rfl
  rw [List.length_map, hn0, Nat.zero_add] at l2
  rw [List.length_map] at l5
  obtain ⟨g1, g2, g3, g4⟩ := heapify_spec _ l1
  rw [l2] at g2 g4
  refine ⟨⟨g1, g2.le, fun h => ?_⟩, g2, ?_⟩
  · show (heapify _).1.lookup h = _
    rw [g3 h]
    by_cases hm : h ∈ es.toFinset
    · rw [ite_eq_left hm]
      exact l3 (h, k h) (List.mem_map_of_mem (List.mem_toFinset.1 hm))
    · rw [ite_eq_right hm, l4 h (by rw [hmap]; exact fun hh => hm (List.mem_toFinset.2 hh))]
      rfl
  · show (loadAll _ _).2 + (heapify _).2 ≤ _
    rw [l5]
    omega

end Build

end LiteralK7a
end JointRootCert
