/-
Joint Root Certification: an implemented indexed binary max-heap.

Manuscript: Part III, subsection `app:representation`.  Results supported:

* `thm:adaptive-oracle-coupling` / `thm:charged-dual-cover` (Exact coupling and charged
  maintenance) and `prop:representation-cost` (Unified Full-Cost Representation
  Comparison): both use "indexed max-heaps" with `O(log m)` key updates.  In
  `CostModel.lean` and `CostEngines.lean` such a heap is a primitive charged
  `⌈log₂ m⌉ + 1` per key update.  This file implements the heap and proves the charge.

## The data structure

An array-based binary max-heap with handles (`Heap ι α`): `n` stored entries at array
positions `0, …, n-1`, the handle `hd i : ι` and key `ky i : α` of position `i`, and the
position map `pos : ι → Option ℕ` (the index of a handle, if present).  The parent of
position `i > 0` is `(i - 1) / 2`.  Arrays are modelled as functions, as in `CostModel.lean`.

Operations, each returning the new heap together with a step count computed by the same
recursion: `siftUp`, `siftDown` (one unit per visited position: at most two key
comparisons, one swap, two position-map writes), `findMax` (a read of position `0`),
`updateKey`, `insert`, `delete` (one unit for the handle lookup and the comparison that
chooses the sift direction, plus the sift).

## What is proved

* `findMax_spec`, `findMax_eq_sup`: the root key is the maximum of the stored keys.
* `updateKey_spec`, `insert_spec`, `delete_spec`: the heap invariant is preserved and the
  stored handle-to-key map changes exactly as specified.
* `updateKey_cost`, `insert_cost`, `delete_cost`: at most `⌈log₂ n⌉ + 2 ≤ 2 (⌈log₂ n⌉ + 1)`
  units, `n` the number of stored entries (after the insertion for `insert`).
* `build_spec`: a heap built by successive insertions.
* Plug-in for the charged dual cover (`CostModel.dcUpdate`): `dcUpdateH` runs the same
  update on implemented heaps; `dcUpdateH_spec` shows that it simulates `dcUpdate` (so
  `dcUpdate_inv` applies), that `findMax` of each action heap is the root summary, and
  that its computed cost is at most `2 h` plus `⌈log₂ b_a⌉ + 2` per changed subscription
  plus `⌈log₂ K⌉ + 2` per affected action, hence at most twice the charge of
  `dcUpdate_cost`.
* Plug-in for the level-bucket engine (`CostEngines.wave`): `waveH` runs the wave with one
  implemented heap per gate; `waveH_spec` shows that it simulates `wave` (so `wave_spec`
  applies) with computed cost at most twice the cost of `wave`.
-/
import JointRootCert.CostModel
import JointRootCert.CostEngines

namespace JointRootCert
namespace HeapImpl

open Finset

/-! ## Heap order on key arrays -/

/-- Parent position. -/
def par (i : ℕ) : ℕ := (i - 1) / 2

section Order

variable {α : Type*} [LinearOrder α]

/-- Heap order on positions `0, …, n-1`. -/
def Ord (n : ℕ) (k : ℕ → α) : Prop := ∀ i, 0 < i → i < n → k i ≤ k (par i)

/-- Heap order except possibly between `j` and its parent; the children of `j` are below
the parent of `j`. -/
def OrdUp (n : ℕ) (k : ℕ → α) (j : ℕ) : Prop :=
  (∀ i, 0 < i → i < n → i ≠ j → k i ≤ k (par i)) ∧
  (∀ i, 0 < i → i < n → par i = j → 0 < j → k i ≤ k (par j))

/-- Heap order except possibly between `j` and its children; the children of `j` are below
the parent of `j`. -/
def OrdDn (n : ℕ) (k : ℕ → α) (j : ℕ) : Prop :=
  (∀ i, 0 < i → i < n → par i ≠ j → k i ≤ k (par i)) ∧
  (∀ i, 0 < i → i < n → par i = j → 0 < j → k i ≤ k (par j))

/-- Exchange of two array cells. -/
def swapK {β : Type*} (k : ℕ → β) (a b : ℕ) : ℕ → β :=
  fun i => if i = a then k b else if i = b then k a else k i

lemma par_lt {i : ℕ} (h : 0 < i) : par i < i := by unfold par; omega

lemma par_eq_iff {i j : ℕ} (h : 0 < i) : par i = j ↔ i = 2 * j + 1 ∨ i = 2 * j + 2 := by
  unfold par; omega

lemma ordUp_done {n : ℕ} {k : ℕ → α} {j : ℕ} (h : OrdUp n k j)
    (hj : j = 0 ∨ k j ≤ k (par j)) : Ord n k := by
  intro i hi hin
  by_cases hij : i = j
  · subst hij
    rcases hj with hj | hj
    · omega
    · exact hj
  · exact h.1 i hi hin hij

lemma ordUp_swap {n : ℕ} {k : ℕ → α} {j : ℕ} (h : OrdUp n k j) (hj : 0 < j)
    (hlt : k (par j) < k j) : OrdUp n (swapK k j (par j)) (par j) := by
  have hpj := par_lt hj
  have e1 : swapK k j (par j) j = k (par j) := by simp [swapK]
  have e2 : swapK k j (par j) (par j) = k j := by
    unfold swapK; rw [ite_eq_right (by omega), ite_eq_left rfl]
  have e3 : ∀ i, i ≠ j → i ≠ par j → swapK k j (par j) i = k i := by
    intro i h1 h2; unfold swapK; rw [ite_eq_right h1, ite_eq_right h2]
  constructor
  · intro i hi hin hne
    by_cases hij : i = j
    · subst hij
      rw [e1, e2]; exact hlt.le
    · rw [e3 i hij hne]
      by_cases hp : par i = j
      · rw [hp, e1]
        exact h.2 i hi hin hp hj
      · by_cases hp2 : par i = par j
        · rw [hp2, e2]
          exact (hp2 ▸ h.1 i hi hin hij).trans hlt.le
        · rw [e3 _ hp hp2]
          exact h.1 i hi hin hij
  · intro i hi hin hp hpj0
    have hppne : par (par j) ≠ j := by have := par_lt hpj0; omega
    have hppne2 : par (par j) ≠ par j := by have := par_lt hpj0; omega
    rw [e3 _ hppne hppne2]
    have hpjn : par j < n := by
      have := par_lt hi; omega
    have hpp : k (par j) ≤ k (par (par j)) := h.1 (par j) hpj0 hpjn (by omega)
    by_cases hij : i = j
    · subst hij
      rw [e1]; exact hpp
    · have hne : i ≠ par j := by have := par_lt hi; omega
      rw [e3 i hij hne]
      exact ((hp ▸ h.1 i hi hin hij)).trans hpp

lemma ordDn_done {n : ℕ} {k : ℕ → α} {j : ℕ} (h : OrdDn n k j)
    (hj : ∀ i, 0 < i → i < n → par i = j → k i ≤ k j) : Ord n k := by
  intro i hi hin
  by_cases hp : par i = j
  · rw [hp]; exact hj i hi hin hp
  · exact h.1 i hi hin hp

lemma ordDn_swap {n : ℕ} {k : ℕ → α} {j m : ℕ} (h : OrdDn n k j) (hm : 0 < m) (hmn : m < n)
    (hpm : par m = j) (hlt : k j < k m)
    (hbig : ∀ i, 0 < i → i < n → par i = j → k i ≤ k m) : OrdDn n (swapK k j m) m := by
  have hjm : j < m := hpm ▸ par_lt hm
  have e1 : swapK k j m j = k m := by simp [swapK]
  have e2 : swapK k j m m = k j := by
    unfold swapK; rw [ite_eq_right (by omega), ite_eq_left rfl]
  have e3 : ∀ i, i ≠ j → i ≠ m → swapK k j m i = k i := by
    intro i h1 h2; unfold swapK; rw [ite_eq_right h1, ite_eq_right h2]
  constructor
  · intro i hi hin hne
    by_cases him : i = m
    · subst him
      rw [e2, hpm, e1]; exact hlt.le
    · by_cases hij : i = j
      · subst hij
        have hpi := par_lt hi
        rw [e1, e3 _ (by omega) (by omega)]
        have := h.2 m hm hmn hpm hi
        exact this
      · rw [e3 i hij him]
        by_cases hp : par i = j
        · rw [hp, e1]; exact hbig i hi hin hp
        · rw [e3 _ hp hne]
          exact h.1 i hi hin hp
  · intro i hi hin hp _
    have hij : i ≠ j := by have := par_lt hi; omega
    have him : i ≠ m := by have := par_lt hi; omega
    rw [e3 i hij him, hpm, e1]
    have := h.1 i hi hin (by omega)
    rwa [hp] at this

lemma ord_root_max {n : ℕ} {k : ℕ → α} (h : Ord n k) : ∀ i, i < n → k i ≤ k 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hin
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact le_rfl
    · have hp := par_lt hi
      exact (h i hi hin).trans (ih (par i) hp (by omega))

/-- Replacing the key at `i` by a larger one (possibly after shrinking the array) leaves a
heap that is ordered except between `i` and its parent. -/
lemma ordUp_replace {n n' : ℕ} {k : ℕ → α} (h : Ord n k) (hn : n' ≤ n) (i : ℕ) (x : α)
    (hx : k i ≤ x) : OrdUp n' (Function.update k i x) i := by
  constructor
  · intro i' hi' hin' hne
    rw [Function.update_of_ne hne]
    by_cases hp : par i' = i
    · rw [hp, Function.update_self]
      exact (hp ▸ h i' hi' (by omega)).trans hx
    · rw [Function.update_of_ne hp]
      exact h i' hi' (by omega)
  · intro i' hi' hin' hp hi
    have hne : i' ≠ i := by have := par_lt hi'; omega
    have hne2 : par i ≠ i := by have := par_lt hi; omega
    rw [Function.update_of_ne hne, Function.update_of_ne hne2]
    have h1 := h i' hi' (by omega)
    rw [hp] at h1
    have hin : i < n := by have := par_lt hi'; omega
    exact h1.trans (h i hi hin)

/-- Replacing the key at `i` by a smaller one leaves a heap that is ordered except between
`i` and its children. -/
lemma ordDn_replace {n n' : ℕ} {k : ℕ → α} (h : Ord n k) (hn : n' ≤ n) (i : ℕ) (x : α)
    (hx : x ≤ k i) : OrdDn n' (Function.update k i x) i := by
  constructor
  · intro i' hi' hin' hp
    rw [Function.update_of_ne hp]
    by_cases hne : i' = i
    · subst hne
      rw [Function.update_self]
      exact hx.trans (h i' hi' (by omega))
    · rw [Function.update_of_ne hne]
      exact h i' hi' (by omega)
  · intro i' hi' hin' hp hi
    have hne : i' ≠ i := by have := par_lt hi'; omega
    have hne2 : par i ≠ i := by have := par_lt hi; omega
    rw [Function.update_of_ne hne, Function.update_of_ne hne2]
    have h1 := h i' hi' (by omega)
    rw [hp] at h1
    have hin : i < n := by have := par_lt hi'; omega
    exact h1.trans (h i hi hin)

end Order

/-! ## The indexed heap -/

/-- Array-based indexed binary heap: `n` entries, handle and key of each position, and the
position of each handle. -/
structure Heap (ι α : Type*) where
  n : ℕ
  hd : ℕ → ι
  ky : ℕ → α
  pos : ι → Option ℕ

section HeapOps

variable {ι α : Type*} [DecidableEq ι] [LinearOrder α]

/-- The key stored under a handle, if the handle is present. -/
def Heap.lookup (H : Heap ι α) (h : ι) : Option α := (H.pos h).map H.ky

/-- The position map and the handle array are mutually inverse on `0, …, n-1`. -/
structure Heap.PosOK (H : Heap ι α) : Prop where
  fwd : ∀ i, i < H.n → H.pos (H.hd i) = some i
  bwd : ∀ h i, H.pos h = some i → i < H.n ∧ H.hd i = h

/-- Heap invariant. -/
structure Heap.Inv (H : Heap ι α) : Prop where
  posOK : H.PosOK
  ord : Ord H.n H.ky

/-- Exchange the entries at positions `a` and `b` (two position-map writes). -/
def Heap.swap (H : Heap ι α) (a b : ℕ) : Heap ι α where
  n := H.n
  hd := swapK H.hd a b
  ky := swapK H.ky a b
  pos := fun h => if h = H.hd a then some b else if h = H.hd b then some a else H.pos h

omit [DecidableEq ι] [LinearOrder α] in
lemma Heap.PosOK.hd_inj {H : Heap ι α} (hP : H.PosOK) {a b : ℕ} (ha : a < H.n) (hb : b < H.n)
    (h : H.hd a = H.hd b) : a = b := by
  have h1 := hP.fwd a ha
  have h2 := hP.fwd b hb
  rw [h, h2] at h1
  exact (Option.some.inj h1).symm

omit [LinearOrder α] in
lemma Heap.swap_posOK {H : Heap ι α} (hP : H.PosOK) {a b : ℕ} (ha : a < H.n) (hb : b < H.n)
    (hab : a ≠ b) : (H.swap a b).PosOK := by
  have hne : H.hd a ≠ H.hd b := fun h => hab (hP.hd_inj ha hb h)
  constructor
  · intro i hi
    show (if swapK H.hd a b i = H.hd a then some b
      else if swapK H.hd a b i = H.hd b then some a else H.pos (swapK H.hd a b i)) = some i
    unfold swapK
    by_cases h1 : i = a
    · subst h1
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
    · rw [ite_eq_right h1]
      by_cases h2 : i = b
      · subst h2
        rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h1 (hP.hd_inj hi ha h)),
          ite_eq_right (fun h => h2 (hP.hd_inj hi hb h))]
        exact hP.fwd i hi
  · intro h i hpi
    change (if h = H.hd a then some b else if h = H.hd b then some a else H.pos h) = some i
      at hpi
    show i < H.n ∧ swapK H.hd a b i = h
    unfold swapK
    by_cases h1 : h = H.hd a
    · rw [ite_eq_left h1] at hpi
      have : b = i := Option.some.inj hpi
      subst this
      rw [ite_eq_right (Ne.symm hab), ite_eq_left rfl]
      exact ⟨hb, h1.symm⟩
    · rw [ite_eq_right h1] at hpi
      by_cases h2 : h = H.hd b
      · rw [ite_eq_left h2] at hpi
        have : a = i := Option.some.inj hpi
        subst this
        rw [ite_eq_left rfl]
        exact ⟨ha, h2.symm⟩
      · rw [ite_eq_right h2] at hpi
        obtain ⟨h3, h4⟩ := hP.bwd h i hpi
        have hia : i ≠ a := fun e => h1 (e ▸ h4.symm)
        have hib : i ≠ b := fun e => h2 (e ▸ h4.symm)
        rw [ite_eq_right hia, ite_eq_right hib]
        exact ⟨h3, h4⟩

omit [LinearOrder α] in
lemma Heap.swap_lookup {H : Heap ι α} (hP : H.PosOK) {a b : ℕ} (ha : a < H.n) (hb : b < H.n)
    (hab : a ≠ b) (h : ι) : (H.swap a b).lookup h = H.lookup h := by
  have hne : H.hd a ≠ H.hd b := fun h => hab (hP.hd_inj ha hb h)
  show Option.map (swapK H.ky a b)
    (if h = H.hd a then some b else if h = H.hd b then some a else H.pos h)
    = Option.map H.ky (H.pos h)
  by_cases h1 : h = H.hd a
  · rw [ite_eq_left h1, h1, hP.fwd a ha]
    simp [swapK, Ne.symm hab]
  · rw [ite_eq_right h1]
    by_cases h2 : h = H.hd b
    · rw [ite_eq_left h2, h2, hP.fwd b hb]
      simp [swapK]
    · rw [ite_eq_right h2]
      cases hp : H.pos h with
      | none => rfl
      | some i =>
        obtain ⟨_, h4⟩ := hP.bwd h i hp
        have hia : i ≠ a := fun e => h1 (e ▸ h4.symm)
        have hib : i ≠ b := fun e => h2 (e ▸ h4.symm)
        simp [swapK, hia, hib]

/-- **Sift up** from position `j` with fuel `d`: one unit per visited position. -/
def siftUp : ℕ → Heap ι α → ℕ → Heap ι α × ℕ
  | 0, H, _ => (H, 1)
  | d + 1, H, j =>
    if 0 < j ∧ H.ky (par j) < H.ky j then
      ((siftUp d (H.swap j (par j)) (par j)).1, (siftUp d (H.swap j (par j)) (par j)).2 + 1)
    else (H, 1)

lemma siftUp_cost : ∀ (d : ℕ) (H : Heap ι α) (j : ℕ), (siftUp d H j).2 ≤ d + 1 := by
  intro d
  induction d with
  | zero => intro H j; simp [siftUp]
  | succ d ih =>
    intro H j
    rw [siftUp]
    split_ifs
    · have := ih (H.swap j (par j)) (par j)
      show _ + 1 ≤ _
      omega
    · show 1 ≤ _
      omega

theorem siftUp_spec : ∀ (d : ℕ) (H : Heap ι α) (j : ℕ), H.PosOK → OrdUp H.n H.ky j →
    j < H.n → j + 1 < 2 ^ (d + 1) →
    (siftUp d H j).1.Inv ∧ (siftUp d H j).1.n = H.n ∧
      ∀ h, (siftUp d H j).1.lookup h = H.lookup h := by
  intro d
  induction d with
  | zero =>
    intro H j hP hO hj hd
    have : j = 0 := by simp at hd; omega
    exact ⟨⟨hP, ordUp_done hO (Or.inl this)⟩, rfl, fun _ => rfl⟩
  | succ d ih =>
    intro H j hP hO hj hd
    rw [siftUp]
    by_cases hc : 0 < j ∧ H.ky (par j) < H.ky j
    · rw [ite_eq_left hc]
      have hpj := par_lt hc.1
      have hP' := Heap.swap_posOK hP hj (by omega : par j < H.n) (by omega)
      have hfuel : par j + 1 < 2 ^ (d + 1) := by
        have : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
        unfold par; omega
      obtain ⟨h1, h2, h3⟩ := ih (H.swap j (par j)) (par j) hP'
        (ordUp_swap hO hc.1 hc.2) (by show par j < H.n; omega) hfuel
      refine ⟨h1, h2, fun h => ?_⟩
      rw [h3 h]
      exact Heap.swap_lookup hP hj (by omega) (by omega) h
    · rw [ite_eq_right hc]
      refine ⟨⟨hP, ordUp_done hO ?_⟩, rfl, fun _ => rfl⟩
      by_cases hj0 : j = 0
      · exact Or.inl hj0
      · right
        by_contra hlt
        exact hc ⟨by omega, lt_of_not_ge hlt⟩

/-- The child of `j` with the larger key (the left child if there is no right child). -/
def bigChild (H : Heap ι α) (j : ℕ) : ℕ :=
  if 2 * j + 2 < H.n ∧ H.ky (2 * j + 1) < H.ky (2 * j + 2) then 2 * j + 2 else 2 * j + 1

omit [DecidableEq ι] in
lemma bigChild_spec (H : Heap ι α) (j : ℕ) (hl : 2 * j + 1 < H.n) :
    0 < bigChild H j ∧ bigChild H j < H.n ∧ par (bigChild H j) = j ∧
      ∀ i, 0 < i → i < H.n → par i = j → H.ky i ≤ H.ky (bigChild H j) := by
  unfold bigChild
  by_cases hc : 2 * j + 2 < H.n ∧ H.ky (2 * j + 1) < H.ky (2 * j + 2)
  · rw [ite_eq_left hc]
    refine ⟨by omega, hc.1, by unfold par; omega, ?_⟩
    intro i hi _ hp
    rcases (par_eq_iff hi).1 hp with rfl | rfl
    · exact hc.2.le
    · exact le_rfl
  · rw [ite_eq_right hc]
    refine ⟨by omega, hl, by unfold par; omega, ?_⟩
    intro i hi hin hp
    rcases (par_eq_iff hi).1 hp with rfl | rfl
    · exact le_rfl
    · by_contra hlt
      exact hc ⟨hin, lt_of_not_ge hlt⟩

/-- **Sift down** from position `j` with fuel `d`: one unit per visited position. -/
def siftDown : ℕ → Heap ι α → ℕ → Heap ι α × ℕ
  | 0, H, _ => (H, 1)
  | d + 1, H, j =>
    if 2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j) then
      ((siftDown d (H.swap j (bigChild H j)) (bigChild H j)).1,
       (siftDown d (H.swap j (bigChild H j)) (bigChild H j)).2 + 1)
    else (H, 1)

lemma siftDown_cost : ∀ (d : ℕ) (H : Heap ι α) (j : ℕ), (siftDown d H j).2 ≤ d + 1 := by
  intro d
  induction d with
  | zero => intro H j; simp [siftDown]
  | succ d ih =>
    intro H j
    rw [siftDown]
    split_ifs
    · have := ih (H.swap j (bigChild H j)) (bigChild H j)
      show _ + 1 ≤ _
      omega
    · show 1 ≤ _
      omega

theorem siftDown_spec : ∀ (d : ℕ) (H : Heap ι α) (j : ℕ), H.PosOK → OrdDn H.n H.ky j →
    j < H.n → H.n ≤ (j + 1) * 2 ^ d →
    (siftDown d H j).1.Inv ∧ (siftDown d H j).1.n = H.n ∧
      ∀ h, (siftDown d H j).1.lookup h = H.lookup h := by
  intro d
  induction d with
  | zero =>
    intro H j hP hO hj hd
    refine ⟨⟨hP, ordDn_done hO ?_⟩, rfl, fun _ => rfl⟩
    intro i hi hin hp
    exfalso
    have hin' : i < H.n := hin
    have := (par_eq_iff hi).1 hp
    simp at hd
    omega
  | succ d ih =>
    intro H j hP hO hj hd
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
      obtain ⟨h1, h2, h3⟩ := ih (H.swap j (bigChild H j)) (bigChild H j) hP'
        (ordDn_swap hO hm0 hmn hpm hc.2 hbig) hmn hfuel
      refine ⟨h1, h2, fun h => ?_⟩
      rw [h3 h]
      exact Heap.swap_lookup hP hj hmn (by omega) h
    · rw [ite_eq_right hc]
      refine ⟨⟨hP, ordDn_done hO ?_⟩, rfl, fun _ => rfl⟩
      intro i hi hin hp
      have hin' : i < H.n := hin
      have hl : 2 * j + 1 < H.n := by
        have := (par_eq_iff hi).1 hp; omega
      obtain ⟨_, _, _, hbig⟩ := bigChild_spec H j hl
      refine (hbig i hi hin hp).trans ?_
      by_contra hlt
      exact hc ⟨hl, lt_of_not_ge hlt⟩

lemma fuel_up {n j : ℕ} (hj : j < n) : j + 1 < 2 ^ (Nat.clog 2 n + 1) := by
  have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  have h2 : 2 ^ (Nat.clog 2 n + 1) = 2 * 2 ^ Nat.clog 2 n := by ring
  have h3 : 0 < 2 ^ Nat.clog 2 n := by positivity
  omega

lemma fuel_dn {n : ℕ} (j : ℕ) : n ≤ (j + 1) * 2 ^ Nat.clog 2 n := by
  have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  calc n ≤ 1 * 2 ^ Nat.clog 2 n := by omega
    _ ≤ (j + 1) * 2 ^ Nat.clog 2 n := Nat.mul_le_mul_right _ (by omega)

/-! ### find-max -/

/-- **find-max**: a read of the root (`⊥` for the empty heap). -/
def findMax [OrderBot α] (H : Heap ι α) : α := if H.n = 0 then ⊥ else H.ky 0

omit [DecidableEq ι] in
/-- **Correctness of find-max**: the root key is an upper bound of all stored keys and, if
the heap is nonempty, is the key of some stored handle. -/
theorem findMax_spec [OrderBot α] {H : Heap ι α} (hI : H.Inv) :
    (∀ h x, H.lookup h = some x → x ≤ findMax H) ∧
    (0 < H.n → ∃ h, H.lookup h = some (findMax H)) := by
  constructor
  · intro h x hx
    unfold Heap.lookup at hx
    cases hp : H.pos h with
    | none => rw [hp] at hx; simp at hx
    | some i =>
      rw [hp] at hx
      obtain ⟨hin, _⟩ := hI.posOK.bwd h i hp
      have : H.ky i = x := by simpa using hx
      unfold findMax
      rw [ite_eq_right (by omega), ← this]
      exact ord_root_max hI.ord i hin
  · intro hn
    refine ⟨H.hd 0, ?_⟩
    unfold Heap.lookup findMax
    rw [hI.posOK.fwd 0 hn, ite_eq_right (by omega)]
    rfl

/-- If the heap stores the keys `k h` for the handles `h ∈ S`, find-max returns
`max_{h ∈ S} k h`. -/
theorem findMax_eq_sup [OrderBot α] {H : Heap ι α} (hI : H.Inv) (S : Finset ι) (k : ι → α)
    (hS : ∀ h, H.lookup h = if h ∈ S then some (k h) else none) : findMax H = S.sup k := by
  obtain ⟨h1, h2⟩ := findMax_spec hI
  apply le_antisymm
  · by_cases hn : H.n = 0
    · unfold findMax; rw [ite_eq_left hn]; exact bot_le
    · obtain ⟨h, hh⟩ := h2 (by omega)
      rw [hS h] at hh
      by_cases hm : h ∈ S
      · rw [ite_eq_left hm] at hh
        rw [← Option.some.inj hh]
        exact Finset.le_sup hm
      · rw [ite_eq_right hm] at hh; simp at hh
  · apply Finset.sup_le
    intro h hm
    exact h1 h (k h) (by rw [hS h, ite_eq_left hm])

/-! ### update-key -/

/-- Overwrite the key at position `i`. -/
def Heap.setKey (H : Heap ι α) (i : ℕ) (x : α) : Heap ι α :=
  { H with ky := Function.update H.ky i x }

/-- Key update at a known position: compare with the old key (1 unit), then sift. -/
def updateAt (H : Heap ι α) (i : ℕ) (x : α) : Heap ι α × ℕ :=
  if H.ky i ≤ x then
    ((siftUp (Nat.clog 2 H.n) (H.setKey i x) i).1,
     (siftUp (Nat.clog 2 H.n) (H.setKey i x) i).2 + 1)
  else
    ((siftDown (Nat.clog 2 H.n) (H.setKey i x) i).1,
     (siftDown (Nat.clog 2 H.n) (H.setKey i x) i).2 + 1)

/-- **update-key**: set the key of handle `h` to `x` (no effect if `h` is absent). -/
def updateKey (H : Heap ι α) (h : ι) (x : α) : Heap ι α × ℕ :=
  (H.pos h).elim (H, 1) (fun i => updateAt H i x)

/-- **Cost of update-key**: at most `⌈log₂ n⌉ + 2` units. -/
theorem updateKey_cost (H : Heap ι α) (h : ι) (x : α) :
    (updateKey H h x).2 ≤ Nat.clog 2 H.n + 2 := by
  unfold updateKey
  cases H.pos h with
  | none => simp
  | some i =>
    simp only [Option.elim_some, updateAt]
    split_ifs
    · have := siftUp_cost (Nat.clog 2 H.n) (H.setKey i x) i
      show _ + 1 ≤ _
      omega
    · have := siftDown_cost (Nat.clog 2 H.n) (H.setKey i x) i
      show _ + 1 ≤ _
      omega

/-- **Correctness of update-key**: the invariant and the size are preserved; the key of `h`
becomes `x` if `h` is present and no other key changes. -/
theorem updateKey_spec {H : Heap ι α} (hI : H.Inv) (h : ι) (x : α) :
    (updateKey H h x).1.Inv ∧ (updateKey H h x).1.n = H.n ∧
      ∀ h', (updateKey H h x).1.lookup h'
        = if h' = h ∧ H.lookup h ≠ none then some x else H.lookup h' := by
  unfold updateKey
  cases hp : H.pos h with
  | none =>
    refine ⟨hI, rfl, fun h' => ?_⟩
    have : H.lookup h = none := by unfold Heap.lookup; rw [hp]; rfl
    simp [this]
  | some i =>
    obtain ⟨hin, hhd⟩ := hI.posOK.bwd h i hp
    have hlk : H.lookup h ≠ none := by unfold Heap.lookup; rw [hp]; simp
    have hP1 : (H.setKey i x).PosOK := ⟨hI.posOK.fwd, hI.posOK.bwd⟩
    have hl1 : ∀ h', (H.setKey i x).lookup h' = if h' = h then some x else H.lookup h' := by
      intro h'
      show Option.map (Function.update H.ky i x) (H.pos h') = _
      by_cases hh : h' = h
      · rw [ite_eq_left hh, hh, hp]
        simp
      · rw [ite_eq_right hh]
        unfold Heap.lookup
        cases hp' : H.pos h' with
        | none => rfl
        | some i' =>
          have hne : i' ≠ i := fun e => hh (by
            have := (hI.posOK.bwd h' i' hp').2
            rw [e, hhd] at this; exact this.symm)
          simp [Function.update_of_ne hne]
    simp only [Option.elim_some, updateAt]
    by_cases hc : H.ky i ≤ x
    · rw [ite_eq_left hc]
      obtain ⟨h1, h2, h3⟩ := siftUp_spec (Nat.clog 2 H.n) (H.setKey i x) i hP1
        (ordUp_replace hI.ord le_rfl i x hc) hin (fuel_up hin)
      refine ⟨h1, h2, fun h' => ?_⟩
      show (siftUp (Nat.clog 2 H.n) (H.setKey i x) i).1.lookup h' = _
      rw [h3 h', hl1 h']
      by_cases hh : h' = h
      · rw [ite_eq_left hh, ite_eq_left ⟨hh, hlk⟩]
      · rw [ite_eq_right hh, ite_eq_right (fun e => hh e.1)]
    · rw [ite_eq_right hc]
      obtain ⟨h1, h2, h3⟩ := siftDown_spec (Nat.clog 2 H.n) (H.setKey i x) i hP1
        (ordDn_replace hI.ord le_rfl i x (le_of_not_ge hc)) hin (fuel_dn i)
      refine ⟨h1, h2, fun h' => ?_⟩
      show (siftDown (Nat.clog 2 H.n) (H.setKey i x) i).1.lookup h' = _
      rw [h3 h', hl1 h']
      by_cases hh : h' = h
      · rw [ite_eq_left hh, ite_eq_left ⟨hh, hlk⟩]
      · rw [ite_eq_right hh, ite_eq_right (fun e => hh e.1)]

/-! ### insert -/

/-- Append an entry at position `n`. -/
def Heap.append (H : Heap ι α) (h : ι) (x : α) : Heap ι α where
  n := H.n + 1
  hd := Function.update H.hd H.n h
  ky := Function.update H.ky H.n x
  pos := Function.update H.pos h (some H.n)

/-- **insert**: append the entry (1 unit) and sift up. -/
def insert (H : Heap ι α) (h : ι) (x : α) : Heap ι α × ℕ :=
  ((siftUp (Nat.clog 2 (H.n + 1)) (H.append h x) H.n).1,
   (siftUp (Nat.clog 2 (H.n + 1)) (H.append h x) H.n).2 + 1)

/-- **Cost of insert**: at most `⌈log₂ (n + 1)⌉ + 2` units, `n + 1` the new size. -/
theorem insert_cost (H : Heap ι α) (h : ι) (x : α) :
    (insert H h x).2 ≤ Nat.clog 2 (H.n + 1) + 2 := by
  have := siftUp_cost (Nat.clog 2 (H.n + 1)) (H.append h x) H.n
  show _ + 1 ≤ _
  omega

/-- **Correctness of insert** of an absent handle. -/
theorem insert_spec {H : Heap ι α} (hI : H.Inv) (h : ι) (x : α) (hh : H.pos h = none) :
    (insert H h x).1.Inv ∧ (insert H h x).1.n = H.n + 1 ∧
      ∀ h', (insert H h x).1.lookup h' = if h' = h then some x else H.lookup h' := by
  have hP1 : (H.append h x).PosOK := by
    constructor
    · intro i hi
      show Function.update H.pos h (some H.n) (Function.update H.hd H.n h i) = some i
      by_cases hin : i = H.n
      · rw [hin, Function.update_self, Function.update_self]
      · have hi' : i < H.n := by
          have : i < H.n + 1 := hi
          omega
        have hne : H.hd i ≠ h := fun e => by
          have := hI.posOK.fwd i hi'
          rw [e, hh] at this
          simp at this
        rw [Function.update_of_ne hin, Function.update_of_ne hne]
        exact hI.posOK.fwd i hi'
    · intro h' i hpi
      change Function.update H.pos h (some H.n) h' = some i at hpi
      show i < H.n + 1 ∧ Function.update H.hd H.n h i = h'
      by_cases he : h' = h
      · rw [he, Function.update_self] at hpi
        have : H.n = i := Option.some.inj hpi
        rw [← this, Function.update_self]
        exact ⟨by omega, he.symm⟩
      · rw [Function.update_of_ne he] at hpi
        obtain ⟨h3, h4⟩ := hI.posOK.bwd h' i hpi
        rw [Function.update_of_ne (by omega)]
        exact ⟨by omega, h4⟩
  have hO1 : OrdUp (H.append h x).n (H.append h x).ky H.n := by
    constructor
    · intro i hi hin hne
      have hi' : i < H.n := by
        have : i < H.n + 1 := hin
        omega
      have hp := par_lt hi
      show Function.update H.ky H.n x i ≤ Function.update H.ky H.n x (par i)
      rw [Function.update_of_ne hne, Function.update_of_ne (by omega)]
      exact hI.ord i hi hi'
    · intro i hi hin hp _
      exfalso
      have := (par_eq_iff hi).1 hp
      have : i < H.n + 1 := hin
      omega
  have hl1 : ∀ h', (H.append h x).lookup h' = if h' = h then some x else H.lookup h' := by
    intro h'
    show Option.map (Function.update H.ky H.n x) (Function.update H.pos h (some H.n) h') = _
    by_cases he : h' = h
    · rw [ite_eq_left he, he, Function.update_self]
      simp
    · rw [ite_eq_right he, Function.update_of_ne he]
      unfold Heap.lookup
      cases hp' : H.pos h' with
      | none => rfl
      | some i' =>
        have := (hI.posOK.bwd h' i' hp').1
        simp [Function.update_of_ne (show i' ≠ H.n by omega)]
  obtain ⟨h1, h2, h3⟩ := siftUp_spec (Nat.clog 2 (H.n + 1)) (H.append h x) H.n hP1 hO1
    (by show H.n < H.n + 1; omega) (fuel_up (by omega))
  exact ⟨h1, h2, fun h' => by
    show (siftUp (Nat.clog 2 (H.n + 1)) (H.append h x) H.n).1.lookup h' = _
    rw [h3 h', hl1 h']⟩

/-! ### delete -/

/-- Drop the last entry, whose handle is `h`. -/
def Heap.dropLast (H : Heap ι α) (h : ι) : Heap ι α :=
  { H with n := H.n - 1, pos := Function.update H.pos h none }

/-- Move the last entry to position `i` (whose handle `h` is removed) and shrink. -/
def Heap.moveLast (H : Heap ι α) (h : ι) (i : ℕ) : Heap ι α where
  n := H.n - 1
  hd := Function.update H.hd i (H.hd (H.n - 1))
  ky := Function.update H.ky i (H.ky (H.n - 1))
  pos := fun h' => if h' = h then none else if h' = H.hd (H.n - 1) then some i else H.pos h'

/-- Deletion at a known position. -/
def deleteAt (H : Heap ι α) (h : ι) (i : ℕ) : Heap ι α × ℕ :=
  if i = H.n - 1 then (H.dropLast h, 1)
  else if H.ky i ≤ H.ky (H.n - 1) then
    ((siftUp (Nat.clog 2 H.n) (H.moveLast h i) i).1,
     (siftUp (Nat.clog 2 H.n) (H.moveLast h i) i).2 + 1)
  else
    ((siftDown (Nat.clog 2 H.n) (H.moveLast h i) i).1,
     (siftDown (Nat.clog 2 H.n) (H.moveLast h i) i).2 + 1)

/-- **delete**: remove handle `h` (no effect if absent): move the last entry into its
position (1 unit) and sift. -/
def delete (H : Heap ι α) (h : ι) : Heap ι α × ℕ :=
  (H.pos h).elim (H, 1) (fun i => deleteAt H h i)

/-- **Cost of delete**: at most `⌈log₂ n⌉ + 2` units, `n` the size before deletion. -/
theorem delete_cost (H : Heap ι α) (h : ι) : (delete H h).2 ≤ Nat.clog 2 H.n + 2 := by
  unfold delete
  cases H.pos h with
  | none => simp
  | some i =>
    simp only [Option.elim_some, deleteAt]
    split_ifs
    · show 1 ≤ _
      omega
    · have := siftUp_cost (Nat.clog 2 H.n) (H.moveLast h i) i
      show _ + 1 ≤ _
      omega
    · have := siftDown_cost (Nat.clog 2 H.n) (H.moveLast h i) i
      show _ + 1 ≤ _
      omega

/-- **Correctness of delete** of a present handle. -/
theorem delete_spec {H : Heap ι α} (hI : H.Inv) (h : ι) (hh : H.lookup h ≠ none) :
    (delete H h).1.Inv ∧ (delete H h).1.n = H.n - 1 ∧
      ∀ h', (delete H h).1.lookup h' = if h' = h then none else H.lookup h' := by
  unfold delete
  cases hp : H.pos h with
  | none => exact absurd (by unfold Heap.lookup; rw [hp]; rfl) hh
  | some i =>
    obtain ⟨hin, hhd⟩ := hI.posOK.bwd h i hp
    simp only [Option.elim_some, deleteAt]
    by_cases hlast : i = H.n - 1
    · rw [ite_eq_left hlast]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, rfl, ?_⟩
      · intro i' hi'
        have hi'' : i' < H.n - 1 := hi'
        show Function.update H.pos h none (H.hd i') = some i'
        have hne : H.hd i' ≠ h := fun e => by
          have := hI.posOK.hd_inj (by omega : i' < H.n) hin (e.trans hhd.symm)
          omega
        rw [Function.update_of_ne hne]
        exact hI.posOK.fwd i' (by omega)
      · intro h' i' hpi
        change Function.update H.pos h none h' = some i' at hpi
        show i' < H.n - 1 ∧ H.hd i' = h'
        by_cases he : h' = h
        · rw [he, Function.update_self] at hpi
          simp at hpi
        · rw [Function.update_of_ne he] at hpi
          obtain ⟨h3, h4⟩ := hI.posOK.bwd h' i' hpi
          refine ⟨?_, h4⟩
          have : i' ≠ i := fun e => he (by rw [← h4, e, hhd])
          omega
      · intro i' hi' hin'
        have : i' < H.n - 1 := hin'
        exact hI.ord i' hi' (by omega)
      · intro h'
        show Option.map H.ky (Function.update H.pos h none h') = _
        by_cases he : h' = h
        · rw [ite_eq_left he, he, Function.update_self]
          rfl
        · rw [ite_eq_right he, Function.update_of_ne he]
          rfl
    · rw [ite_eq_right hlast]
      have hil : i < H.n - 1 := by omega
      have hln : H.n - 1 < H.n := by omega
      have hlne : H.hd (H.n - 1) ≠ h := fun e => by
        have := hI.posOK.hd_inj hln hin (e.trans hhd.symm)
        omega
      have hP1 : (H.moveLast h i).PosOK := by
        constructor
        · intro i' hi'
          have hi'' : i' < H.n - 1 := hi'
          show (if Function.update H.hd i (H.hd (H.n - 1)) i' = h then none
            else if Function.update H.hd i (H.hd (H.n - 1)) i' = H.hd (H.n - 1) then some i
            else H.pos (Function.update H.hd i (H.hd (H.n - 1)) i')) = some i'
          by_cases he : i' = i
          · rw [he, Function.update_self, ite_eq_right hlne, ite_eq_left rfl]
          · rw [Function.update_of_ne he]
            have h1 : H.hd i' ≠ h := fun e => he
              (hI.posOK.hd_inj (by omega) hin (e.trans hhd.symm))
            have h2 : H.hd i' ≠ H.hd (H.n - 1) := fun e => by
              have := hI.posOK.hd_inj (by omega : i' < H.n) hln e
              omega
            rw [ite_eq_right h1, ite_eq_right h2]
            exact hI.posOK.fwd i' (by omega)
        · intro h' i' hpi
          change (if h' = h then none else if h' = H.hd (H.n - 1) then some i
            else H.pos h') = some i' at hpi
          show i' < H.n - 1 ∧ Function.update H.hd i (H.hd (H.n - 1)) i' = h'
          by_cases he : h' = h
          · rw [ite_eq_left he] at hpi
            simp at hpi
          · rw [ite_eq_right he] at hpi
            by_cases he2 : h' = H.hd (H.n - 1)
            · rw [ite_eq_left he2] at hpi
              have : i = i' := Option.some.inj hpi
              rw [← this, Function.update_self]
              exact ⟨hil, he2.symm⟩
            · rw [ite_eq_right he2] at hpi
              obtain ⟨h3, h4⟩ := hI.posOK.bwd h' i' hpi
              have hne1 : i' ≠ i := fun e => he (by rw [← h4, e, hhd])
              have hne2 : i' ≠ H.n - 1 := fun e => he2 (by rw [← h4, e])
              rw [Function.update_of_ne hne1]
              exact ⟨by omega, h4⟩
      have hl1 : ∀ h', (H.moveLast h i).lookup h' = if h' = h then none else H.lookup h' := by
        intro h'
        show Option.map (Function.update H.ky i (H.ky (H.n - 1)))
          (if h' = h then none else if h' = H.hd (H.n - 1) then some i else H.pos h') = _
        by_cases he : h' = h
        · rw [ite_eq_left he, ite_eq_left he]
          rfl
        · rw [ite_eq_right he, ite_eq_right he]
          unfold Heap.lookup
          by_cases he2 : h' = H.hd (H.n - 1)
          · rw [ite_eq_left he2, he2, hI.posOK.fwd _ hln]
            simp
          · rw [ite_eq_right he2]
            cases hp' : H.pos h' with
            | none => rfl
            | some i' =>
              have h4 := (hI.posOK.bwd h' i' hp').2
              have hne1 : i' ≠ i := fun e => he (by rw [← h4, e, hhd])
              simp [Function.update_of_ne hne1]
      by_cases hc : H.ky i ≤ H.ky (H.n - 1)
      · rw [ite_eq_left hc]
        obtain ⟨h1, h2, h3⟩ := siftUp_spec (Nat.clog 2 H.n) (H.moveLast h i) i hP1
          (ordUp_replace hI.ord (Nat.sub_le _ _) i _ hc) hil (fuel_up hin)
        refine ⟨h1, h2, fun h' => ?_⟩
        show (siftUp (Nat.clog 2 H.n) (H.moveLast h i) i).1.lookup h' = _
        rw [h3 h', hl1 h']
      · rw [ite_eq_right hc]
        have hfd : (H.moveLast h i).n ≤ (i + 1) * 2 ^ Nat.clog 2 H.n :=
          (Nat.sub_le _ _).trans (fuel_dn i)
        obtain ⟨h1, h2, h3⟩ := siftDown_spec (Nat.clog 2 H.n) (H.moveLast h i) i hP1
          (ordDn_replace hI.ord (Nat.sub_le _ _) i _ (le_of_not_ge hc)) hil hfd
        refine ⟨h1, h2, fun h' => ?_⟩
        show (siftDown (Nat.clog 2 H.n) (H.moveLast h i) i).1.lookup h' = _
        rw [h3 h', hl1 h']

/-! ### The empty heap and heap construction -/

/-- The empty heap. -/
def Heap.empty [Inhabited ι] [OrderBot α] : Heap ι α :=
  ⟨0, fun _ => default, fun _ => ⊥, fun _ => none⟩

omit [DecidableEq ι] in
lemma Heap.empty_inv [Inhabited ι] [OrderBot α] : (Heap.empty : Heap ι α).Inv :=
  ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun h i hp => by simp [Heap.empty] at hp⟩,
    fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩

/-- Insert a list of entries one by one; the cost is the sum of the insertion costs. -/
def insertAll (H : Heap ι α) : List (ι × α) → Heap ι α × ℕ
  | [] => (H, 0)
  | e :: es =>
    ((insertAll (insert H e.1 e.2).1 es).1,
     (insert H e.1 e.2).2 + (insertAll (insert H e.1 e.2).1 es).2)

/-- **Heap construction by insertions.**  Inserting entries with distinct absent handles
gives a heap storing the old entries and the new ones, of size `n + |es|`, at cost at most
`|es| (⌈log₂ (n + |es|)⌉ + 2)`. -/
theorem insertAll_spec : ∀ (es : List (ι × α)) (H : Heap ι α), H.Inv →
    (es.map Prod.fst).Nodup → (∀ e ∈ es, H.pos e.1 = none) →
    (insertAll H es).1.Inv ∧ (insertAll H es).1.n = H.n + es.length ∧
    (∀ e ∈ es, (insertAll H es).1.lookup e.1 = some e.2) ∧
    (∀ h, h ∉ es.map Prod.fst → (insertAll H es).1.lookup h = H.lookup h) ∧
    (insertAll H es).2 ≤ es.length * (Nat.clog 2 (H.n + es.length) + 2) := by
  intro es
  induction es with
  | nil => intro H hI _ _; simp [insertAll, hI]
  | cons e es ih =>
    intro H hI hnd habs
    obtain ⟨h1, h2, h3⟩ := insert_spec hI e.1 e.2 (habs e (List.mem_cons_self))
    rw [List.map_cons, List.nodup_cons] at hnd
    have habs' : ∀ e' ∈ es, (insert H e.1 e.2).1.pos e'.1 = none := by
      intro e' he'
      have hne : e'.1 ≠ e.1 := fun eq => hnd.1 (eq ▸ List.mem_map_of_mem he')
      have hl := h3 e'.1
      rw [ite_eq_right hne] at hl
      have hold : H.lookup e'.1 = none := by
        unfold Heap.lookup
        rw [habs e' (List.mem_cons_of_mem _ he')]; rfl
      rw [hold] at hl
      unfold Heap.lookup at hl
      cases hp : (insert H e.1 e.2).1.pos e'.1 with
      | none => rfl
      | some i => rw [hp] at hl; simp at hl
    obtain ⟨g1, g2, g3a, g3, g4⟩ := ih (insert H e.1 e.2).1 h1 hnd.2 habs'
    refine ⟨g1, ?_, ?_, ?_, ?_⟩
    · show (insertAll (insert H e.1 e.2).1 es).1.n = _
      rw [g2, h2, List.length_cons]; omega
    · intro e' he'
      show (insertAll (insert H e.1 e.2).1 es).1.lookup e'.1 = _
      rcases List.mem_cons.1 he' with rfl | he'
      · rw [g3 _ hnd.1, h3, ite_eq_left rfl]
      · exact g3a e' he'
    · intro h hm
      show (insertAll (insert H e.1 e.2).1 es).1.lookup h = _
      rw [List.map_cons, List.mem_cons, not_or] at hm
      rw [g3 h hm.2, h3 h, ite_eq_right hm.1]
    · show (insert H e.1 e.2).2 + (insertAll (insert H e.1 e.2).1 es).2 ≤ _
      have hc := insert_cost H e.1 e.2
      rw [h2] at g4
      have hm1 : Nat.clog 2 (H.n + 1) ≤ Nat.clog 2 (H.n + (es.length + 1)) :=
        Nat.clog_mono_right 2 (by omega)
      have he : H.n + 1 + es.length = H.n + (es.length + 1) := by omega
      rw [he] at g4
      rw [List.length_cons]
      calc (insert H e.1 e.2).2 + (insertAll (insert H e.1 e.2).1 es).2
          ≤ (Nat.clog 2 (H.n + (es.length + 1)) + 2)
            + es.length * (Nat.clog 2 (H.n + (es.length + 1)) + 2) := by omega
        _ = (es.length + 1) * (Nat.clog 2 (H.n + (es.length + 1)) + 2) := by ring

end HeapOps

/-! ## Heaps as representations of key tables -/

section Rep

variable {ι α : Type*} [DecidableEq ι] [LinearOrder α] [OrderBot α]

/-- The heap `H` is a valid heap of at most `b` entries storing exactly the keys `k h` for
the handles `h ∈ S`. -/
structure Rep (H : Heap ι α) (S : Finset ι) (k : ι → α) (b : ℕ) : Prop where
  inv : H.Inv
  size : H.n ≤ b
  look : ∀ h, H.lookup h = if h ∈ S then some (k h) else none

lemma Rep.findMax {H : Heap ι α} {S : Finset ι} {k : ι → α} {b : ℕ} (h : Rep H S k b) :
    findMax H = S.sup k := findMax_eq_sup h.inv S k h.look

omit [OrderBot α] in
lemma Rep.congr {H : Heap ι α} {S : Finset ι} {k k' : ι → α} {b : ℕ} (h : Rep H S k b)
    (hk : ∀ i ∈ S, k i = k' i) : Rep H S k' b :=
  ⟨h.inv, h.size, fun i => by
    rw [h.look i]
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi, ite_eq_left hi, hk i hi]
    · rw [ite_eq_right hi, ite_eq_right hi]⟩

omit [OrderBot α] in
/-- A key update on the heap is a point update of the key table. -/
lemma Rep.update {H : Heap ι α} {S : Finset ι} {k : ι → α} {b : ℕ} (h : Rep H S k b)
    (i : ι) (x : α) :
    Rep (updateKey H i x).1 S (fun i' => if i' = i then x else k i') b := by
  obtain ⟨h1, h2, h3⟩ := updateKey_spec h.inv i x
  refine ⟨h1, h2 ▸ h.size, fun i' => ?_⟩
  rw [h3 i', h.look i', h.look i]
  by_cases hi : i ∈ S
  · by_cases he : i' = i
    · subst he
      simp [hi]
    · simp [he]
  · by_cases he : i' = i
    · subst he
      simp [hi]
    · simp [he]

omit [OrderBot α] in
lemma Rep.updateKey_cost {H : Heap ι α} {S : Finset ι} {k : ι → α} {b : ℕ} (h : Rep H S k b)
    (i : ι) (x : α) : (updateKey H i x).2 ≤ Nat.clog 2 b + 2 :=
  (HeapImpl.updateKey_cost H i x).trans
    (Nat.add_le_add_right (Nat.clog_mono_right 2 h.size) 2)

/-- **Building a heap for a key table**: inserting the handles of a duplicate-free list
into the empty heap gives a representation of the table, at cost at most
`m (⌈log₂ m⌉ + 2)` for `m` handles. -/
theorem rep_build [Inhabited ι] (es : List ι) (hnd : es.Nodup) (k : ι → α) :
    Rep (insertAll (Heap.empty : Heap ι α) (es.map (fun h => (h, k h)))).1 es.toFinset k
        es.length ∧
    (insertAll (Heap.empty : Heap ι α) (es.map (fun h => (h, k h)))).2
      ≤ es.length * (Nat.clog 2 es.length + 2) := by
  have hmap : (es.map (fun h => (h, k h))).map Prod.fst = es := by
    rw [List.map_map]
    exact List.map_id _
  obtain ⟨h1, h2, h3, h4, h5⟩ := insertAll_spec (es.map (fun h => (h, k h)))
    (Heap.empty : Heap ι α) Heap.empty_inv (by rw [hmap]; exact hnd) (fun _ _ => rfl)
  have hn0 : (Heap.empty : Heap ι α).n = 0 := rfl
  rw [List.length_map, hn0, Nat.zero_add] at h2 h5
  refine ⟨⟨h1, h2.le, fun h => ?_⟩, h5⟩
  by_cases hm : h ∈ es.toFinset
  · rw [ite_eq_left hm]
    exact h3 (h, k h) (List.mem_map_of_mem (List.mem_toFinset.1 hm))
  · rw [ite_eq_right hm, h4 h (by rw [hmap]; exact fun hh => hm (List.mem_toFinset.2 hh))]
    rfl

end Rep

/-! ## Plug-in: the charged dual cover on implemented heaps -/

section DualCover

open CostModel

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]

/-- State of the dual-cover index with implemented heaps: the segment-tree array, one
indexed heap per root action (handles are blocks), and the global heap (handles are root
actions). -/
structure HState (A α : Type*) where
  tree : ℕ → ℕ → α
  hp : A → Heap (ℕ × ℕ) α
  gh : Heap A α

/-- Subscription deliveries on implemented heaps: one `updateKey` per changed
subscription. -/
def deliverH (tree' : ℕ → ℕ → α) :
    List ((ℕ × ℕ) × A) → (A → Heap (ℕ × ℕ) α) → (A → Heap (ℕ × ℕ) α) × ℕ
  | [], hp => (hp, 0)
  | e :: rest, hp =>
    ((deliverH tree' rest
        (Function.update hp e.2 (updateKey (hp e.2) e.1 (tree' e.1.1 e.1.2)).1)).1,
     (deliverH tree' rest
        (Function.update hp e.2 (updateKey (hp e.2) e.1 (tree' e.1.1 e.1.2)).1)).2
       + (updateKey (hp e.2) e.1 (tree' e.1.1 e.1.2)).2)

omit [OrderBot α] in
theorem deliverH_spec (tree' : ℕ → ℕ → α) (cov : A → Finset (ℕ × ℕ)) (bsz : A → ℕ) :
    ∀ (L : List ((ℕ × ℕ) × A)) (hp : A → Heap (ℕ × ℕ) α) (key : A → ℕ × ℕ → α),
      (∀ a, Rep (hp a) (cov a) (key a) (bsz a)) →
      (∀ a, Rep ((deliverH tree' L hp).1 a) (cov a) ((deliver tree' bsz L key).1 a) (bsz a)) ∧
      (deliverH tree' L hp).2 ≤ (L.map (fun e => Nat.clog 2 (bsz e.2) + 2)).sum := by
  intro L
  induction L with
  | nil => intro hp key h; exact ⟨h, le_rfl⟩
  | cons e rest ih =>
    intro hp key h
    have hstep : ∀ a, Rep
        (Function.update hp e.2 (updateKey (hp e.2) e.1 (tree' e.1.1 e.1.2)).1 a) (cov a)
        ((fun a' d' => if a' = e.2 ∧ d' = e.1 then tree' e.1.1 e.1.2 else key a' d') a)
        (bsz a) := by
      intro a
      by_cases ha : a = e.2
      · subst ha
        rw [Function.update_self]
        exact ((h e.2).update e.1 (tree' e.1.1 e.1.2)).congr (fun d _ => by simp)
      · rw [Function.update_of_ne ha]
        exact (h a).congr (fun d _ => by simp [ha])
    obtain ⟨h1, h2⟩ := ih _ _ hstep
    refine ⟨h1, ?_⟩
    have hc := (h e.2).updateKey_cost e.1 (tree' e.1.1 e.1.2)
    simp only [deliverH, List.map_cons, List.sum_cons]
    omega

/-- Root refresh on implemented heaps: read the maximum of the action heap and update the
key of the action in the global heap. -/
def refreshH (hp : A → Heap (ℕ × ℕ) α) : List A → Heap A α → Heap A α × ℕ
  | [], gh => (gh, 0)
  | a :: rest, gh =>
    ((refreshH hp rest (updateKey gh a (findMax (hp a))).1).1,
     (refreshH hp rest (updateKey gh a (findMax (hp a))).1).2
       + (updateKey gh a (findMax (hp a))).2)

theorem refreshH_spec (cov : A → Finset (ℕ × ℕ)) (bsz : A → ℕ) (acts : Finset A) (K : ℕ)
    (hp : A → Heap (ℕ × ℕ) α) (key : A → ℕ × ℕ → α)
    (hrep : ∀ a, Rep (hp a) (cov a) (key a) (bsz a)) :
    ∀ (L : List A) (gh : Heap A α) (root : A → α), Rep gh acts root K →
      Rep (refreshH hp L gh).1 acts (refresh cov key K L root).1 K ∧
      (refreshH hp L gh).2 ≤ L.length * (Nat.clog 2 K + 2) := by
  intro L
  induction L with
  | nil => intro gh root h; exact ⟨h, by simp [refreshH]⟩
  | cons a rest ih =>
    intro gh root h
    have hstep : Rep (updateKey gh a (findMax (hp a))).1 acts
        (fun a' => if a' = a then (cov a).sup (key a) else root a') K := by
      rw [(hrep a).findMax]
      exact h.update a _
    obtain ⟨h1, h2⟩ := ih _ _ hstep
    refine ⟨h1, ?_⟩
    have hc := h.updateKey_cost a (findMax (hp a))
    simp only [refreshH, List.length_cons]
    have : (rest.length + 1) * (Nat.clog 2 K + 2)
        = rest.length * (Nat.clog 2 K + 2) + (Nat.clog 2 K + 2) := by ring
    omega

/-- **One update of the charged dual-cover index on implemented heaps**: the program
`CostModel.dcUpdate` with every heap operation executed by `updateKey` / `findMax`. -/
def dcUpdateH (n : ℕ) (subs : ℕ × ℕ → List A) (p : ℕ) (x : α) (s : HState A α) :
    HState A α × ℕ :=
  (⟨(pathUpdate p x s.tree n).1,
    (deliverH (pathUpdate p x s.tree n).1 (changedSubs n subs p x s.tree) s.hp).1,
    (refreshH (deliverH (pathUpdate p x s.tree n).1 (changedSubs n subs p x s.tree) s.hp).1
      (affected n subs p x s.tree) s.gh).1⟩,
   (pathUpdate p x s.tree n).2
    + (changedNodes p s.tree (pathUpdate p x s.tree n).1 n).2
    + (deliverH (pathUpdate p x s.tree n).1 (changedSubs n subs p x s.tree) s.hp).2
    + (refreshH (deliverH (pathUpdate p x s.tree n).1 (changedSubs n subs p x s.tree) s.hp).1
        (affected n subs p x s.tree) s.gh).2)

/-- The implemented state `hs` represents the abstract state `s` of `CostModel`: same
tree, each action heap stores the keys of the action's blocks, the global heap stores the
root summaries of the actions in `acts`. -/
structure Sim (cov : A → Finset (ℕ × ℕ)) (bsz : A → ℕ) (acts : Finset A) (K : ℕ)
    (hs : HState A α) (s : DCState A α) : Prop where
  tree : hs.tree = s.tree
  hp : ∀ a, Rep (hs.hp a) (cov a) (s.key a) (bsz a)
  gh : Rep hs.gh acts s.root K

/-- **The dual-cover update with implemented heaps** (`thm:charged-dual-cover`,
`eq:dual-cover-work`, one update and one endpoint).  `dcUpdateH` simulates
`CostModel.dcUpdate` (hence `dcUpdate_inv` applies to it), and its computed cost is at most

`2 h + Σ_{(d, a) ∈ 𝒩_t} (⌈log₂ b_a⌉ + 2) + |𝒜_t| (⌈log₂ K⌉ + 2)`,

which is at most twice the charge `dcUpdate_cost` of the primitive-heap model.  Here `b_a`
bounds the size of the heap of action `a` and `K` the size of the global heap. -/
theorem dcUpdateH_spec (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (bsz : A → ℕ) (acts : Finset A) (K p : ℕ) (x : α) (hs : HState A α) (s : DCState A α)
    (h : Sim cov bsz acts K hs s) :
    Sim cov bsz acts K (dcUpdateH n subs p x hs).1 (dcUpdate n cov subs bsz K p x s).1 ∧
    (dcUpdateH n subs p x hs).2
      ≤ 2 * (n + 1)
        + ((changedSubs n subs p x s.tree).map (fun e => Nat.clog 2 (bsz e.2) + 2)).sum
        + (affected n subs p x s.tree).length * (Nat.clog 2 K + 2) ∧
    (dcUpdateH n subs p x hs).2 ≤ 2 * (dcUpdate n cov subs bsz K p x s).2 := by
  obtain ⟨hs_tree, hs_hp, hs_gh⟩ := hs
  obtain ⟨ht, hhp, hgh⟩ := h
  simp only at ht hhp hgh
  subst ht
  obtain ⟨d1, d2⟩ := deliverH_spec (pathUpdate p x s.tree n).1 cov bsz
    (changedSubs n subs p x s.tree) hs_hp s.key hhp
  obtain ⟨r1, r2⟩ := refreshH_spec cov bsz acts K _ _ d1 (affected n subs p x s.tree)
    hs_gh s.root hgh
  have hcost : (dcUpdateH n subs p x ⟨s.tree, hs_hp, hs_gh⟩).2
      ≤ 2 * (n + 1)
        + ((changedSubs n subs p x s.tree).map (fun e => Nat.clog 2 (bsz e.2) + 2)).sum
        + (affected n subs p x s.tree).length * (Nat.clog 2 K + 2) := by
    simp only [dcUpdateH, pathUpdate_cost, changedNodes_cost]
    omega
  refine ⟨⟨rfl, d1, r1⟩, hcost, hcost.trans ?_⟩
  rw [dcUpdate_cost]
  have e1 : ((changedSubs n subs p x s.tree).map (fun e => Nat.clog 2 (bsz e.2) + 2)).sum
      ≤ 2 * ((changedSubs n subs p x s.tree).map (fun e => Nat.clog 2 (bsz e.2) + 1)).sum := by
    induction (changedSubs n subs p x s.tree) with
    | nil => simp
    | cons e l ih => simp only [List.map_cons, List.sum_cons]; omega
  have e2 : (affected n subs p x s.tree).length * (Nat.clog 2 K + 2)
      ≤ 2 * ((affected n subs p x s.tree).length * (Nat.clog 2 K + 1)) := by
    rw [← mul_assoc, mul_comm 2, mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Queries** (`eq:dual-cover-work`, the `Q` term).  Under the simulation and the index
invariant, the root of the heap of action `a` is the maximum of the terminal values over
the positions covered by the blocks of `a`, and the root of the global heap is the maximum
of these over the actions; each is one read (`findMax`), so `Q` queries cost `Q` units. -/
theorem query_spec (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (bsz : A → ℕ) (acts : Finset A)
    (K : ℕ) (f : ℕ → α) (hs : HState A α) (s : DCState A α) (h : Sim cov bsz acts K hs s)
    (hinv : DCInv n cov f s) (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n) :
    (∀ a, findMax (hs.hp a) = ((cov a).biUnion blk).sup f) ∧
    findMax hs.gh = acts.sup (fun a => ((cov a).biUnion blk).sup f) := by
  have h1 : ∀ a, findMax (hs.hp a) = ((cov a).biUnion blk).sup f := by
    intro a
    rw [(h.hp a).findMax, ← hinv.root a]
    exact hinv.root_eq hlev a
  refine ⟨h1, ?_⟩
  rw [h.gh.findMax]
  exact Finset.sup_congr rfl (fun a _ => hinv.root_eq hlev a)

end DualCover

/-! ## Plug-in: the level-bucket engine on implemented heaps -/

section Engine

open CostEngines

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma heapMax_eq_sup (cs : List ℕ) (k : ℕ → α) : heapMax cs k = cs.toFinset.sup k := by
  induction cs with
  | nil => simp [heapMax]
  | cons c cs ih =>
    rw [List.toFinset_cons, Finset.sup_insert, ← ih]
    rfl

/-- Engine state with implemented heaps: the stored value of every gate and the indexed
heap of every gate (handles are the children). -/
structure HEState (α : Type*) where
  val : ℕ → α
  hp : ℕ → Heap ℕ α

/-- The implemented state represents the abstract engine state. -/
structure SimE (G : Dag) (hs : HEState α) (s : EState α) : Prop where
  val : hs.val = s.val
  hp : ∀ p, Rep (hs.hp p) (G.children p).toFinset (s.key p) (G.children p).length

/-- Target value read from the implemented heap. -/
def targetH (G : Dag) (x : ℕ) (y : α) (s : HEState α) (g : ℕ) : α :=
  if G.children g = [] then (if g = x then y else s.val g) else findMax (s.hp g)

lemma targetH_eq {G : Dag} {hs : HEState α} {s : EState α} (h : SimE G hs s) (x : ℕ) (y : α)
    (g : ℕ) : targetH G x y hs g = target G x y s g := by
  unfold targetH target
  rw [h.val, (h.hp g).findMax, heapMax_eq_sup]

/-- Deliveries from a changed gate on implemented heaps: one `updateKey` in the heap of
each parent, and one bucket push (1 unit). -/
def pushH (G : Dag) (g : ℕ) (y : α) :
    List ℕ → (ℕ → Heap ℕ α) → (ℕ → List ℕ) → (ℕ → Heap ℕ α) × (ℕ → List ℕ) × ℕ
  | [], hp, bk => (hp, bk, 0)
  | p :: ps, hp, bk =>
    ((pushH G g y ps (Function.update hp p (updateKey (hp p) g y).1)
        (fun l => if l = G.level p then p :: bk l else bk l)).1,
     (pushH G g y ps (Function.update hp p (updateKey (hp p) g y).1)
        (fun l => if l = G.level p then p :: bk l else bk l)).2.1,
     (pushH G g y ps (Function.update hp p (updateKey (hp p) g y).1)
        (fun l => if l = G.level p then p :: bk l else bk l)).2.2
       + ((updateKey (hp p) g y).2 + 1))

omit [OrderBot α] in
theorem pushH_spec (G : Dag) (g : ℕ) (y : α) :
    ∀ (ps : List ℕ) (hp : ℕ → Heap ℕ α) (key : ℕ → ℕ → α) (bk : ℕ → List ℕ),
      (∀ p, Rep (hp p) (G.children p).toFinset (key p) (G.children p).length) →
      (∀ p, Rep ((pushH G g y ps hp bk).1 p) (G.children p).toFinset
        ((push G g y ps key bk).1 p) (G.children p).length) ∧
      (pushH G g y ps hp bk).2.1 = (push G g y ps key bk).2.1 ∧
      (pushH G g y ps hp bk).2.2 ≤ 2 * (push G g y ps key bk).2.2 := by
  intro ps
  induction ps with
  | nil => intro hp key bk h; exact ⟨h, rfl, le_rfl⟩
  | cons p ps ih =>
    intro hp key bk h
    have hstep : ∀ p', Rep (Function.update hp p (updateKey (hp p) g y).1 p')
        (G.children p').toFinset
        ((fun p' c' => if p' = p ∧ c' = g then y else key p' c') p')
        (G.children p').length := by
      intro p'
      by_cases hp' : p' = p
      · subst hp'
        rw [Function.update_self]
        exact ((h p').update g y).congr (fun c _ => by simp)
      · rw [Function.update_of_ne hp']
        exact (h p').congr (fun c _ => by simp [hp'])
    obtain ⟨h1, h2, h3⟩ := ih _ _ (fun l => if l = G.level p then p :: bk l else bk l) hstep
    refine ⟨h1, h2, ?_⟩
    have hc := (h p).updateKey_cost g y
    simp only [pushH, push]
    omega

/-- Processing one bucket on implemented heaps (as `CostEngines.procList`). -/
def procListH (G : Dag) (x : ℕ) (y : α) :
    List ℕ → HEState α → (ℕ → List ℕ) → HEState α × (ℕ → List ℕ) × ℕ
  | [], s, bk => (s, bk, 0)
  | g :: rest, s, bk =>
    if targetH G x y s g = s.val g then
      ((procListH G x y rest s bk).1, (procListH G x y rest s bk).2.1,
        (procListH G x y rest s bk).2.2 + 1)
    else
      ((procListH G x y rest
          ⟨fun g' => if g' = g then targetH G x y s g else s.val g',
            (pushH G g (targetH G x y s g) (G.parents g) s.hp bk).1⟩
          (pushH G g (targetH G x y s g) (G.parents g) s.hp bk).2.1).1,
       (procListH G x y rest
          ⟨fun g' => if g' = g then targetH G x y s g else s.val g',
            (pushH G g (targetH G x y s g) (G.parents g) s.hp bk).1⟩
          (pushH G g (targetH G x y s g) (G.parents g) s.hp bk).2.1).2.1,
       (procListH G x y rest
          ⟨fun g' => if g' = g then targetH G x y s g else s.val g',
            (pushH G g (targetH G x y s g) (G.parents g) s.hp bk).1⟩
          (pushH G g (targetH G x y s g) (G.parents g) s.hp bk).2.1).2.2
        + 1 + (pushH G g (targetH G x y s g) (G.parents g) s.hp bk).2.2)

theorem procListH_spec (G : Dag) (x : ℕ) (y : α) :
    ∀ (rest : List ℕ) (hs : HEState α) (s : EState α) (bk : ℕ → List ℕ), SimE G hs s →
      SimE G (procListH G x y rest hs bk).1 (procList G x y rest s bk).1 ∧
      (procListH G x y rest hs bk).2.1 = (procList G x y rest s bk).2.1 ∧
      (procListH G x y rest hs bk).2.2 ≤ 2 * (procList G x y rest s bk).2.2 := by
  intro rest
  induction rest with
  | nil => intro hs s bk h; exact ⟨h, rfl, le_rfl⟩
  | cons g rest ih =>
    intro hs s bk h
    have ht := targetH_eq h x y g
    by_cases heq : target G x y s g = s.val g
    · have heq' : targetH G x y hs g = hs.val g := by rw [ht, h.val]; exact heq
      rw [procList_same rest heq, procListH, ite_eq_left heq']
      obtain ⟨h1, h2, h3⟩ := ih hs s bk h
      exact ⟨h1, h2, by show _ + 1 ≤ 2 * (_ + 1); omega⟩
    · have heq' : ¬ targetH G x y hs g = hs.val g := by rw [ht, h.val]; exact heq
      rw [procList_change rest heq, procListH, ite_eq_right heq']
      obtain ⟨p1, p2, p3⟩ := pushH_spec G g (target G x y s g) (G.parents g) hs.hp s.key bk
        h.hp
      rw [ht, p2]
      have hsim : SimE G
          ⟨fun g' => if g' = g then target G x y s g else hs.val g',
            (pushH G g (target G x y s g) (G.parents g) hs.hp bk).1⟩
          ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩ :=
        ⟨by show (fun g' => if g' = g then target G x y s g else hs.val g') = stepVal G x y s g
            rw [h.val]; rfl, p1⟩
      obtain ⟨h1, h2, h3⟩ := ih _ _ (push G g (target G x y s g) (G.parents g) s.key bk).2.1
        hsim
      refine ⟨h1, h2, ?_⟩
      show _ + 1 + _ ≤ 2 * (_ + 1 + _)
      omega

/-- Level sweep on implemented heaps (as `CostEngines.waveLevels`). -/
def waveLevelsH (G : Dag) (x : ℕ) (y : α) :
    ℕ → HEState α → (ℕ → List ℕ) → HEState α × (ℕ → List ℕ) × ℕ
  | 0, s, bk => (s, bk, 0)
  | l + 1, s, bk =>
    ((procListH G x y ((waveLevelsH G x y l s bk).2.1 l) (waveLevelsH G x y l s bk).1
        (waveLevelsH G x y l s bk).2.1).1,
     (procListH G x y ((waveLevelsH G x y l s bk).2.1 l) (waveLevelsH G x y l s bk).1
        (waveLevelsH G x y l s bk).2.1).2.1,
     (waveLevelsH G x y l s bk).2.2 + 1
      + (procListH G x y ((waveLevelsH G x y l s bk).2.1 l) (waveLevelsH G x y l s bk).1
          (waveLevelsH G x y l s bk).2.1).2.2)

theorem waveLevelsH_spec (G : Dag) (x : ℕ) (y : α) (hs : HEState α) (s : EState α)
    (bk : ℕ → List ℕ) (h : SimE G hs s) : ∀ l,
      SimE G (waveLevelsH G x y l hs bk).1 (waveLevels G x y l s bk).1 ∧
      (waveLevelsH G x y l hs bk).2.1 = (waveLevels G x y l s bk).2.1 ∧
      (waveLevelsH G x y l hs bk).2.2 ≤ 2 * (waveLevels G x y l s bk).2.2 := by
  intro l
  induction l with
  | zero => exact ⟨h, rfl, le_rfl⟩
  | succ l ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [waveLevelsH, waveLevels]
    rw [h2]
    obtain ⟨q1, q2, q3⟩ := procListH_spec G x y ((waveLevels G x y l s bk).2.1 l) _ _
      (waveLevels G x y l s bk).2.1 h1
    exact ⟨q1, q2, by omega⟩

/-- **One backup wave on implemented heaps** (as `CostEngines.wave`). -/
def waveH (G : Dag) (x : ℕ) (y : α) (s : HEState α) : HEState α × ℕ :=
  ((waveLevelsH G x y (G.L + 1) s (fun l => if l = G.level x then [x] else [])).1,
   (waveLevelsH G x y (G.L + 1) s (fun l => if l = G.level x then [x] else [])).2.2 + 1)

/-- **The backup wave with implemented heaps.**  `waveH` simulates `CostEngines.wave`, and
its computed cost is at most twice the cost of `wave` in the primitive-heap model. -/
theorem waveH_sim (G : Dag) (x : ℕ) (y : α) (hs : HEState α) (s : EState α)
    (h : SimE G hs s) :
    SimE G (waveH G x y hs).1 (wave G x y s).1 ∧ (waveH G x y hs).2 ≤ 2 * (wave G x y s).2 := by
  obtain ⟨h1, _, h3⟩ := waveLevelsH_spec G x y hs s
    (fun l => if l = G.level x then [x] else []) h (G.L + 1)
  exact ⟨h1, by show _ + 1 ≤ 2 * (_ + 1); omega⟩

/-- **`wave_spec` with implemented heaps** (`prop:representation-cost`, one endpoint).
Starting from an implemented state representing an abstract state that satisfies the
engine invariant, after `waveH`: the represented state satisfies the invariant again (the
stored values are the exact evaluation, and `findMax` of the heap of every internal gate is
its stored value), the updated leaf stores `y`, other leaves are unchanged, and the
computed cost is at most `2 (L + 3 + Σ_{g changed} Σ_{p ∈ parents g} (⌈log₂ deg p⌉ + 3))`. -/
theorem waveH_spec {G : Dag} (hG : G.WF) (x : ℕ) (y : α) (hs : HEState α) (s0 : EState α)
    (hx : x < G.N) (h : SimE G hs s0) (h0 : Inv G s0) :
    SimE G (waveH G x y hs).1 (wave G x y s0).1 ∧ Inv G (wave G x y s0).1 ∧
    (∀ g, G.children g ≠ [] → findMax ((waveH G x y hs).1.hp g) = (waveH G x y hs).1.val g) ∧
    (G.children x = [] → (waveH G x y hs).1.val x = y) ∧
    (∀ g, G.children g = [] → g ≠ x → (waveH G x y hs).1.val g = hs.val g) ∧
    (waveH G x y hs).2 ≤ 2 * (G.L + 3 + chgSum G s0 (wave G x y s0).1) := by
  obtain ⟨h1, h2⟩ := waveH_sim G x y hs s0 h
  obtain ⟨w1, w2, w3, w4⟩ := wave_spec hG x y s0 hx h0
  refine ⟨h1, w1, ?_, ?_, ?_, w4 ▸ h2⟩
  · intro g hg
    rw [(h1.hp g).findMax, ← heapMax_eq_sup, h1.val]
    exact (w1.gate g hg).symm
  · intro hl
    rw [h1.val]; exact w2 hl
  · intro g hl hgx
    rw [h1.val, h.val]; exact w3 g hl hgx

end Engine

end HeapImpl
end JointRootCert
