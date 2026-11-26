/-
Joint Root Certification: the charged dual-cover index, initialisation, space and total
work.

Manuscript result covered:

* `thm:adaptive-oracle-coupling` / `thm:charged-dual-cover` (Exact coupling and charged
  maintenance): a costed initialisation of the segment tree and of the per-action and
  global heaps on the implemented heap of `HeapImpl.lean` (the `M + K` terms of
  `eq:dual-cover-work`); a space bound proved for the memory footprint of the program
  states; and one assembled statement of `eq:dual-cover-work` for a `T`-update, `Q`-query
  run, with the compile phase of `RunMerge.charged_dual_cover_compile`.

## Cost model

As in `CostModel.lean` and `HeapImpl.lean`.  New charges, one unit each: writing one
segment-tree node during the build (two reads, one `max`, one write); per root action,
allocating its heap (1 unit) and registering one reverse subscription per block of its
cover; a query (one read of a heap root).  Heap insertions cost what `HeapImpl.insert`
computes.

## Memory model

Arrays are functions, as in `CostModel.lean`; blank memory holds `⊥`.  The footprint of a
state counts: the non-blank cells of the tree array (`treeCells`), the slots of every heap
(`Heap.n`; a slot is a constant number of machine cells: key, handle, position), the nodes
of the cover lists and of the reverse-subscription lists, and the records of the retained
graph.  It is a function of the state and of the static tables, not a formula in the
parameters.
-/
import JointRootCert.HeapImpl
import JointRootCert.RunMerge

namespace JointRootCert
namespace DualCoverFinal

open Finset CostModel CostEngines RunMerge _root_.JointRootCert.Representation
open HeapImpl (Heap Rep findMax HState Sim dcUpdateH)

/-! ## The compiled cover lists: no repeated block, all blocks are tree nodes -/

lemma blk_nonempty (d : ℕ × ℕ) : (blk d).Nonempty := by
  refine ⟨d.2 * 2 ^ d.1, ?_⟩
  have hpos : 0 < 2 ^ d.1 := by positivity
  have e : (d.2 + 1) * 2 ^ d.1 = d.2 * 2 ^ d.1 + 2 ^ d.1 := by ring
  simp only [blk, dyadicBlock, mem_Ico]
  omega

lemma blk_sub_of_cover {l : List (ℕ × ℕ)} {T : Finset ℕ}
    (h : IsDyadicCover (l.map blk).toFinset T) {d : ℕ × ℕ} (hd : d ∈ l) : blk d ⊆ T :=
  h.subset (List.mem_toFinset.2 (List.mem_map_of_mem hd))

/-- The blocks of a dyadic cover of a subset of `[0, 2^n)` are nodes of the tree. -/
lemma cover_nodes {n : ℕ} {l : List (ℕ × ℕ)} {T : Finset ℕ}
    (h : IsDyadicCover (l.map blk).toFinset T) (hT : T ⊆ range (2 ^ n)) :
    ∀ d ∈ l, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1) :=
  fun _ hd => dyadicBlock_node ((blk_sub_of_cover h hd).trans hT)

lemma segQuery_nodup (a b : ℕ) : ∀ k j, (segQuery a b k j).1.Nodup := by
  intro k
  induction k with
  | zero =>
    intro j
    simp only [segQuery]
    split_ifs <;> simp
  | succ k ih =>
    intro j
    by_cases hd : b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a
    · rw [segQuery_of_disjoint a b (k + 1) j hd]
      simp
    by_cases hc : a ≤ j * 2 ^ (k + 1) ∧ (j + 1) * 2 ^ (k + 1) ≤ b
    · rw [segQuery_of_contained a b (k + 1) j hc.1 hc.2]
      simp
    rw [segQuery_split a b k j hd hc]
    show ((segQuery a b k (2 * j)).1 ++ (segQuery a b k (2 * j + 1)).1).Nodup
    rw [List.nodup_append]
    refine ⟨ih _, ih _, ?_⟩
    intro d hd1 d' hd2 e
    obtain ⟨x, hx⟩ := blk_nonempty d
    have h1 := blk_sub_of_cover (segQuery_cover a b k (2 * j)) hd1 hx
    have h2 := blk_sub_of_cover (segQuery_cover a b k (2 * j + 1)) (e ▸ hd2) hx
    simp only [mem_inter, dyadicBlock, mem_Ico] at h1 h2
    omega

lemma coverRuns_nodup (n M : ℕ) (hM : M ≤ 2 ^ n) : ∀ (rl : List (ℕ × ℕ)) (lo : ℕ),
    IvlsFrom M lo rl → (coverRuns n rl).1.Nodup := by
  intro rl
  induction rl with
  | nil => intro lo _; simp [coverRuns]
  | cons p rest ih =>
    intro lo h
    simp only [IvlsFrom] at h
    show ((segQuery p.1 p.2 n 0).1 ++ (coverRuns n rest).1).Nodup
    rw [List.nodup_append]
    refine ⟨segQuery_nodup _ _ _ _, ih p.2 h.2.2.2, ?_⟩
    intro d hd1 d' hd2 e
    obtain ⟨x, hx⟩ := blk_nonempty d
    have h1 := blk_sub_of_cover (segQuery_cover p.1 p.2 n 0) hd1 hx
    have h2 := blk_sub_of_cover (coverRuns_cover n M hM rest p.2 h.2.2.2) (e ▸ hd2) hx
    have h3 := (runSet_bounds h.2.2.2 x h2).1
    simp only [mem_inter, mem_Ico] at h1
    omega

/-- **The output of the dual-cover compiler for one action**: neither block list repeats a
block, and every block is a node `(k, j)` of the segment tree with `2^n` leaves
(`k ≤ n`, `j < 2^(n-k)`). -/
theorem dualCompile_lists (n M : ℕ) (hM : M ≤ 2 ^ n) (rl : List (ℕ × ℕ))
    (hrl : RunsFrom M 0 rl) :
    (dualCompile n M rl).1.1.Nodup ∧ (dualCompile n M rl).1.2.Nodup ∧
    (∀ d ∈ (dualCompile n M rl).1.1, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1)) ∧
    (∀ d ∈ (dualCompile n M rl).1.2, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1)) := by
  obtain ⟨c1, c2⟩ := dualCompile_cover n M hM rl hrl
  have hsub1 : runSet rl ⊆ range (2 ^ n) := by
    intro x hx
    have := (runSet_bounds hrl.ivls x hx).2
    exact mem_range.2 (by omega)
  have hsub2 : range M \ runSet rl ⊆ range (2 ^ n) := by
    intro x hx
    have := mem_range.1 (mem_sdiff.1 hx).1
    exact mem_range.2 (by omega)
  exact ⟨coverRuns_nodup n M hM rl 0 hrl.ivls,
    coverRuns_nodup n M hM _ 0 (gaps_ivls M rl 0 hrl.ivls),
    cover_nodes c1 hsub1, cover_nodes c2 hsub2⟩

/-! ## Costed initialisation of the segment tree -/

section Tree

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Write the cells `0, …, m-1` of level `k` with the values `g j`: one unit per cell. -/
def fillLevel (v : ℕ → ℕ → α) (k : ℕ) (g : ℕ → α) : ℕ → (ℕ → ℕ → α) × ℕ
  | 0 => (v, 0)
  | m + 1 => (setNode (fillLevel v k g m).1 k m (g m), (fillLevel v k g m).2 + 1)

omit [LinearOrder α] [OrderBot α] in
lemma fillLevel_spec (v : ℕ → ℕ → α) (k : ℕ) (g : ℕ → α) : ∀ m,
    (∀ k' j', (fillLevel v k g m).1 k' j' = if k' = k ∧ j' < m then g j' else v k' j') ∧
    (fillLevel v k g m).2 = m := by
  intro m
  induction m with
  | zero => exact ⟨fun k' j' => by simp [fillLevel], rfl⟩
  | succ m ih =>
    refine ⟨fun k' j' => ?_, by show (fillLevel v k g m).2 + 1 = m + 1; rw [ih.2]⟩
    show setNode (fillLevel v k g m).1 k m (g m) k' j' = _
    by_cases h : k' = k ∧ j' = m
    · rw [h.1, h.2, setNode_same, ite_eq_left ⟨rfl, Nat.lt_succ_self m⟩]
    · rw [setNode_of_ne _ _ _ _ h, ih.1]
      by_cases h2 : k' = k ∧ j' < m
      · rw [ite_eq_left h2, ite_eq_left ⟨h2.1, by omega⟩]
      · rw [ite_eq_right h2, ite_eq_right (fun h3 => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 h3.2 with h4 | h4
          · exact h2 ⟨h3.1, h4⟩
          · exact h ⟨h3.1, h4⟩)]

/-- **Segment-tree build**, bottom up: level `0` holds the `2^n` leaf values, a node of
level `k + 1` the maximum of its two children.  One unit per node written. -/
def treeBuild (n : ℕ) (f : ℕ → α) (v0 : ℕ → ℕ → α) : ℕ → (ℕ → ℕ → α) × ℕ
  | 0 => fillLevel v0 0 f (2 ^ n)
  | k + 1 =>
    ((fillLevel (treeBuild n f v0 k).1 (k + 1)
        (fun j => (treeBuild n f v0 k).1 k (2 * j) ⊔ (treeBuild n f v0 k).1 k (2 * j + 1))
        (2 ^ (n - (k + 1)))).1,
     (treeBuild n f v0 k).2 + (fillLevel (treeBuild n f v0 k).1 (k + 1)
        (fun j => (treeBuild n f v0 k).1 k (2 * j) ⊔ (treeBuild n f v0 k).1 k (2 * j + 1))
        (2 ^ (n - (k + 1)))).2)

/-- A block lying beyond the `2^n` leaves has blank maximum. -/
lemma block_sup_bot {n : ℕ} {f : ℕ → α} (hf : ∀ p, 2 ^ n ≤ p → f p = ⊥) {k j : ℕ}
    (hk : k ≤ n) (hj : 2 ^ (n - k) ≤ j) : (dyadicBlock k j).sup f = ⊥ := by
  rw [Finset.sup_eq_bot_iff]
  intro p hp
  apply hf
  simp only [dyadicBlock, mem_Ico] at hp
  have e : 2 ^ n = 2 ^ (n - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  calc 2 ^ n = 2 ^ (n - k) * 2 ^ k := e
    _ ≤ j * 2 ^ k := Nat.mul_le_mul_right _ hj
    _ ≤ p := hp.1

/-- **Correctness and exact cost of the tree build.**  With leaf values `f` that are blank
beyond position `2^n` and blank initial memory, after building the levels `0, …, K`
(`K ≤ n`): every cell of level at most `K` holds the maximum of `f` over its block, the
cells of higher levels are still blank, and the cost is `Σ_{k ≤ K} 2^(n-k)`. -/
theorem treeBuild_spec (n : ℕ) (f : ℕ → α) (hf : ∀ p, 2 ^ n ≤ p → f p = ⊥) : ∀ K, K ≤ n →
    (∀ k ≤ K, ∀ j, (treeBuild n f (fun _ _ => ⊥) K).1 k j = (dyadicBlock k j).sup f) ∧
    (∀ k, K < k → ∀ j, (treeBuild n f (fun _ _ => ⊥) K).1 k j = ⊥) ∧
    (treeBuild n f (fun _ _ => ⊥) K).2 = ∑ k ∈ range (K + 1), 2 ^ (n - k) := by
  intro K
  induction K with
  | zero =>
    intro _
    obtain ⟨s1, s2⟩ := fillLevel_spec (fun _ _ => (⊥ : α)) 0 f (2 ^ n)
    refine ⟨fun k hk j => ?_, fun k hk j => ?_, ?_⟩
    · obtain rfl : k = 0 := by omega
      show (fillLevel (fun _ _ => ⊥) 0 f (2 ^ n)).1 0 j = _
      rw [s1, dyadicBlock_zero, Finset.sup_singleton]
      by_cases hj : j < 2 ^ n
      · rw [ite_eq_left ⟨rfl, hj⟩]
      · rw [ite_eq_right (fun h => hj h.2), hf j (by omega)]
    · show (fillLevel (fun _ _ => ⊥) 0 f (2 ^ n)).1 k j = _
      rw [s1, ite_eq_right (fun h => by omega)]
    · show (fillLevel (fun _ _ => ⊥) 0 f (2 ^ n)).2 = _
      rw [s2]
      simp
  | succ K ih =>
    intro hK
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    obtain ⟨s1, s2⟩ := fillLevel_spec (treeBuild n f (fun _ _ => ⊥) K).1 (K + 1)
      (fun j => (treeBuild n f (fun _ _ => ⊥) K).1 K (2 * j)
        ⊔ (treeBuild n f (fun _ _ => ⊥) K).1 K (2 * j + 1)) (2 ^ (n - (K + 1)))
    refine ⟨fun k hk j => ?_, fun k hk j => ?_, ?_⟩
    · show (fillLevel (treeBuild n f (fun _ _ => ⊥) K).1 (K + 1) _ _).1 k j = _
      rw [s1]
      by_cases hkK : k = K + 1
      · rw [hkK]
        by_cases hj : j < 2 ^ (n - (K + 1))
        · rw [ite_eq_left ⟨rfl, hj⟩, i1 K le_rfl, i1 K le_rfl, dyadicBlock_succ,
            Finset.sup_union]
        · rw [ite_eq_right (fun h => hj h.2), i2 (K + 1) (Nat.lt_succ_self K),
            block_sup_bot hf hK (by omega)]
      · rw [ite_eq_right (fun h => hkK h.1)]
        exact i1 k (by omega) j
    · show (fillLevel (treeBuild n f (fun _ _ => ⊥) K).1 (K + 1) _ _).1 k j = _
      rw [s1, ite_eq_right (fun h => by omega)]
      exact i2 k (by omega) j
    · show (treeBuild n f (fun _ _ => ⊥) K).2 + (fillLevel _ (K + 1) _ _).2 = _
      rw [s2, i3, sum_range_succ _ (K + 1)]

end Tree

/-! ## Costed initialisation of the heaps -/

section Init

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A] [Inhabited A]

/-- Heap of one root action: insert the tree value of every block of its cover into the
empty heap (`HeapImpl.insertAll`, computed cost). -/
def buildAction (tree : ℕ → ℕ → α) (cl : List (ℕ × ℕ)) : Heap (ℕ × ℕ) α × ℕ :=
  HeapImpl.insertAll (Heap.empty : Heap (ℕ × ℕ) α) (cl.map (fun d => (d, tree d.1 d.2)))

/-- Build the heaps of the root actions in turn.  Per action: the heap construction, one
unit per block for registering the reverse subscription, one unit for the heap record. -/
def initHeaps (tree : ℕ → ℕ → α) (covL : A → List (ℕ × ℕ)) :
    List A → (A → Heap (ℕ × ℕ) α) → (A → Heap (ℕ × ℕ) α) × ℕ
  | [], hp => (hp, 0)
  | a :: as, hp =>
    ((initHeaps tree covL as (Function.update hp a (buildAction tree (covL a)).1)).1,
     (buildAction tree (covL a)).2 + (covL a).length + 1
      + (initHeaps tree covL as (Function.update hp a (buildAction tree (covL a)).1)).2)

omit [LinearOrder α] [OrderBot α] [Inhabited A] in
lemma initHeaps_spec [LinearOrder α] [OrderBot α] (tree : ℕ → ℕ → α)
    (covL : A → List (ℕ × ℕ)) : ∀ (as : List A) (hp : A → Heap (ℕ × ℕ) α), as.Nodup →
    (∀ a ∈ as, (initHeaps tree covL as hp).1 a = (buildAction tree (covL a)).1) ∧
    (∀ a, a ∉ as → (initHeaps tree covL as hp).1 a = hp a) ∧
    (initHeaps tree covL as hp).2
      = (as.map (fun a => (buildAction tree (covL a)).2 + (covL a).length + 1)).sum := by
  intro as
  induction as with
  | nil => intro hp _; exact ⟨fun a ha => by simp at ha, fun _ _ => rfl, rfl⟩
  | cons a as ih =>
    intro hp hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨i1, i2, i3⟩ := ih (Function.update hp a (buildAction tree (covL a)).1) hnd.2
    refine ⟨fun b hb => ?_, fun b hb => ?_, ?_⟩
    · show (initHeaps tree covL as _).1 b = _
      by_cases e : b = a
      · rw [e, i2 a hnd.1, Function.update_self]
      · rcases List.mem_cons.1 hb with h | h
        · exact absurd h e
        · exact i1 b h
    · show (initHeaps tree covL as _).1 b = _
      rw [List.mem_cons, not_or] at hb
      rw [i2 b hb.2, Function.update_of_ne hb.1]
    · show _ + (initHeaps tree covL as _).2 = _
      rw [i3, List.map_cons, List.sum_cons]

/-- **Initialisation of the dual-cover index** (one endpoint): build the segment tree from
the leaf values, then the heap of every root action, then the global heap over the root
actions (keys: the roots of the action heaps). -/
def dcInit (n : ℕ) (f : ℕ → α) (covL : A → List (ℕ × ℕ)) (as : List A) : HState A α × ℕ :=
  (⟨(treeBuild n f (fun _ _ => ⊥) n).1,
    (initHeaps (treeBuild n f (fun _ _ => ⊥) n).1 covL as (fun _ => Heap.empty)).1,
    (HeapImpl.insertAll (Heap.empty : Heap A α) (as.map (fun a =>
      (a, findMax ((initHeaps (treeBuild n f (fun _ _ => ⊥) n).1 covL as
        (fun _ => Heap.empty)).1 a))))).1⟩,
   (treeBuild n f (fun _ _ => ⊥) n).2
    + (initHeaps (treeBuild n f (fun _ _ => ⊥) n).1 covL as (fun _ => Heap.empty)).2
    + (HeapImpl.insertAll (Heap.empty : Heap A α) (as.map (fun a =>
        (a, findMax ((initHeaps (treeBuild n f (fun _ _ => ⊥) n).1 covL as
          (fun _ => Heap.empty)).1 a))))).2)

/-- The abstract index state (`CostModel.DCState`) represented after initialisation. -/
def dcInitAbs (n : ℕ) (f : ℕ → α) (covL : A → List (ℕ × ℕ)) : DCState A α :=
  ⟨(treeBuild n f (fun _ _ => ⊥) n).1,
    fun _ d => (treeBuild n f (fun _ _ => ⊥) n).1 d.1 d.2,
    fun a => (covL a).toFinset.sup (fun d => (treeBuild n f (fun _ _ => ⊥) n).1 d.1 d.2)⟩

/-- **Correctness and cost of the initialisation.**  With leaf values blank beyond `2^n`,
root actions `as` without repetition, cover lists without repeated blocks and empty for
non-actions: the initialised state satisfies the index invariant `DCInv` for `f` and is
represented by the implemented heaps (`Sim`); tree cells of level above `n` are blank;
and the computed cost is at most

`(2^(n+1) - 1) + Σ_a (b_a (⌈log₂ b_a⌉ + 3) + 1) + K (⌈log₂ K⌉ + 2)`. -/
theorem dcInit_spec (n : ℕ) (f : ℕ → α) (hf : ∀ p, 2 ^ n ≤ p → f p = ⊥)
    (covL : A → List (ℕ × ℕ)) (as : List A) (hnd : as.Nodup)
    (hcn : ∀ a, (covL a).Nodup) (hout : ∀ a, a ∉ as → covL a = []) :
    DCInv n (fun a => (covL a).toFinset) f (dcInitAbs n f covL) ∧
    Sim (fun a => (covL a).toFinset) (fun a => (covL a).length) as.toFinset as.length
      (dcInit n f covL as).1 (dcInitAbs n f covL) ∧
    (∀ k, n < k → ∀ j, (dcInitAbs n f covL).tree k j = ⊥) ∧
    (dcInit n f covL as).2
      ≤ (2 ^ (n + 1) - 1)
        + (as.map (fun a => (covL a).length * (Nat.clog 2 (covL a).length + 3) + 1)).sum
        + as.length * (Nat.clog 2 as.length + 2) := by
  obtain ⟨t1, t2, t3⟩ := treeBuild_spec n f hf n le_rfl
  obtain ⟨h1, h2, h3⟩ := initHeaps_spec (treeBuild n f (fun _ _ => ⊥) n).1 covL as
    (fun _ => Heap.empty) hnd
  have hrep : ∀ a, Rep ((initHeaps (treeBuild n f (fun _ _ => ⊥) n).1 covL as
      (fun _ => Heap.empty)).1 a) (covL a).toFinset
      (fun d => (treeBuild n f (fun _ _ => ⊥) n).1 d.1 d.2) (covL a).length := by
    intro a
    by_cases ha : a ∈ as
    · rw [h1 a ha]
      exact (HeapImpl.rep_build (covL a) (hcn a) _).1
    · rw [h2 a ha, hout a ha]
      exact ⟨Heap.empty_inv, le_rfl, fun _ => rfl⟩
  obtain ⟨g1, g2⟩ := HeapImpl.rep_build as hnd (fun a => findMax ((initHeaps
    (treeBuild n f (fun _ _ => ⊥) n).1 covL as (fun _ => Heap.empty)).1 a))
  refine ⟨⟨t1, fun _ _ _ => rfl, fun _ => rfl⟩, ⟨rfl, hrep, ?_⟩, t2, ?_⟩
  · exact g1.congr (fun a _ => (hrep a).findMax)
  · have hsum : (as.map (fun a => (buildAction (treeBuild n f (fun _ _ => ⊥) n).1 (covL a)).2
          + (covL a).length + 1)).sum
        ≤ (as.map (fun a => (covL a).length * (Nat.clog 2 (covL a).length + 3) + 1)).sum := by
      apply List.sum_le_sum
      intro a _
      have := (HeapImpl.rep_build (covL a) (hcn a)
        (fun d => (treeBuild n f (fun _ _ => ⊥) n).1 d.1 d.2)).2
      have e : (covL a).length * (Nat.clog 2 (covL a).length + 3)
          = (covL a).length * (Nat.clog 2 (covL a).length + 2) + (covL a).length := by ring
      show (HeapImpl.insertAll _ _).2 + _ + 1 ≤ _
      omega
    have ht : (treeBuild n f (fun _ _ => ⊥) n).2 = 2 ^ (n + 1) - 1 := by
      rw [t3, segTree_nodes]
    show (treeBuild n f (fun _ _ => ⊥) n).2 + (initHeaps _ covL as _).2
      + (HeapImpl.insertAll _ _).2 ≤ _
    rw [ht, h3]
    omega

/-! ### Uniform initial values: linear initialisation -/

omit [DecidableEq A] [Inhabited A] [OrderBot α] in
lemma siftUp_noop {ι : Type*} [DecidableEq ι] (d : ℕ) (H : Heap ι α) (j : ℕ)
    (h : ¬ (0 < j ∧ H.ky (HeapImpl.par j) < H.ky j)) : HeapImpl.siftUp d H j = (H, 1) := by
  cases d with
  | zero => rfl
  | succ d => rw [HeapImpl.siftUp, ite_eq_right h]

/-- All stored keys equal `c`. -/
def AllKey {ι : Type*} (c : α) (H : Heap ι α) : Prop := ∀ i, i < H.n → H.ky i = c

omit [DecidableEq A] [Inhabited A] [OrderBot α] in
lemma insert_const {ι : Type*} [DecidableEq ι] {c : α} {H : Heap ι α} (hA : AllKey c H)
    (h : ι) : HeapImpl.insert H h c = (H.append h c, 2) ∧ AllKey c (H.append h c) := by
  have hall : AllKey c (H.append h c) := by
    intro i hi
    show Function.update H.ky H.n c i = c
    by_cases e : i = H.n
    · rw [e, Function.update_self]
    · rw [Function.update_of_ne e]
      exact hA i (by have : i < H.n + 1 := hi; omega)
  refine ⟨?_, hall⟩
  have hno : ¬ (0 < H.n ∧ (H.append h c).ky (HeapImpl.par H.n) < (H.append h c).ky H.n) := by
    rintro ⟨hpos, hlt⟩
    have hp := HeapImpl.par_lt hpos
    rw [hall H.n (Nat.lt_succ_self _), hall (HeapImpl.par H.n) (Nat.lt_succ_of_lt hp)] at hlt
    exact lt_irrefl _ hlt
  unfold HeapImpl.insert
  rw [siftUp_noop _ _ _ hno]

omit [DecidableEq A] [Inhabited A] [OrderBot α] in
/-- Inserting entries that all carry the key of every stored entry costs two units each:
no sift step moves. -/
lemma insertAll_const {ι : Type*} [DecidableEq ι] (c : α) : ∀ (es : List (ι × α))
    (H : Heap ι α), AllKey c H → (∀ e ∈ es, e.2 = c) →
    (HeapImpl.insertAll H es).2 = 2 * es.length := by
  intro es
  induction es with
  | nil => intro H _ _; rfl
  | cons e es ih =>
    intro H hA hes
    have hc : e.2 = c := hes e List.mem_cons_self
    obtain ⟨i1, i2⟩ := insert_const hA e.1
    have hins : HeapImpl.insert H e.1 e.2 = (H.append e.1 c, 2) := by rw [hc]; exact i1
    show (HeapImpl.insert H e.1 e.2).2 + (HeapImpl.insertAll (HeapImpl.insert H e.1 e.2).1 es).2
      = 2 * (es.length + 1)
    rw [hins, ih (H.append e.1 c) i2 (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))]
    omega

/-- **Linear initialisation from uniform terminal values** (the `M + K` terms of
`eq:dual-cover-work`).  If all terminals start with the same value `c` (the initial box),
the cover blocks are tree nodes and every action has a nonempty cover, then no insertion
sifts and the initialisation costs at most

`(2^(n+1) - 1) + Σ_a (3 b_a + 1) + 2K ≤ 4M + 3B + 3K`. -/
theorem dcInit_cost_uniform (n : ℕ) (f : ℕ → α) (c : α) (hfc : ∀ p, p < 2 ^ n → f p = c)
    (hf : ∀ p, 2 ^ n ≤ p → f p = ⊥) (covL : A → List (ℕ × ℕ)) (as : List A)
    (hnd : as.Nodup) (hcn : ∀ a, (covL a).Nodup)
    (hnodes : ∀ a, ∀ d ∈ covL a, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1))
    (hne : ∀ a ∈ as, covL a ≠ []) :
    (dcInit n f covL as).2
      ≤ (2 ^ (n + 1) - 1) + (as.map (fun a => 3 * (covL a).length + 1)).sum
        + 2 * as.length := by
  obtain ⟨t1, _, t3⟩ := treeBuild_spec n f hf n le_rfl
  obtain ⟨h1, h2, h3⟩ := initHeaps_spec (treeBuild n f (fun _ _ => ⊥) n).1 covL as
    (fun _ => Heap.empty) hnd
  have hnode : ∀ a, ∀ d ∈ covL a, (treeBuild n f (fun _ _ => ⊥) n).1 d.1 d.2 = c := by
    intro a d hd
    obtain ⟨hk, hj⟩ := hnodes a d hd
    rw [t1 d.1 hk d.2]
    have hc : ∀ p ∈ dyadicBlock d.1 d.2, f p = c := by
      intro p hp
      apply hfc
      simp only [dyadicBlock, mem_Ico] at hp
      have e : 2 ^ n = 2 ^ (n - d.1) * 2 ^ d.1 := by rw [← pow_add, Nat.sub_add_cancel hk]
      calc p < (d.2 + 1) * 2 ^ d.1 := hp.2
        _ ≤ 2 ^ (n - d.1) * 2 ^ d.1 := Nat.mul_le_mul_right _ hj
        _ = 2 ^ n := e.symm
    rw [Finset.sup_congr rfl hc]
    exact Finset.sup_const (blk_nonempty d) c
  have hempty : AllKey c (Heap.empty : Heap (ℕ × ℕ) α) :=
    fun i hi => absurd hi (Nat.not_lt_zero i)
  have hba : ∀ a, (buildAction (treeBuild n f (fun _ _ => ⊥) n).1 (covL a)).2
      = 2 * (covL a).length := by
    intro a
    unfold buildAction
    rw [insertAll_const c _ _ hempty, List.length_map]
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    exact hnode a d hd
  have hroot : ∀ a ∈ as, findMax ((initHeaps (treeBuild n f (fun _ _ => ⊥) n).1 covL as
      (fun _ => Heap.empty)).1 a) = c := by
    intro a ha
    have hrb : Rep (buildAction (treeBuild n f (fun _ _ => ⊥) n).1 (covL a)).1
        (covL a).toFinset (fun d => (treeBuild n f (fun _ _ => ⊥) n).1 d.1 d.2)
        (covL a).length := (HeapImpl.rep_build (covL a) (hcn a) _).1
    rw [h1 a ha, hrb.findMax,
      Finset.sup_congr rfl (fun d hd => hnode a d (List.mem_toFinset.1 hd))]
    apply Finset.sup_const
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (hne a ha)
    exact ⟨d, List.mem_toFinset.2 hd⟩
  have hg : (HeapImpl.insertAll (Heap.empty : Heap A α) (as.map (fun a =>
      (a, findMax ((initHeaps (treeBuild n f (fun _ _ => ⊥) n).1 covL as
        (fun _ => Heap.empty)).1 a))))).2 = 2 * as.length := by
    rw [insertAll_const c _ _ (fun i hi => absurd hi (Nat.not_lt_zero i)), List.length_map]
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    exact hroot a ha
  have ht : (treeBuild n f (fun _ _ => ⊥) n).2 = 2 ^ (n + 1) - 1 := by
    rw [t3, segTree_nodes]
  have hsum : (as.map (fun a => (buildAction (treeBuild n f (fun _ _ => ⊥) n).1 (covL a)).2
        + (covL a).length + 1)).sum
      = (as.map (fun a => 3 * (covL a).length + 1)).sum := by
    congr 1
    apply List.map_congr_left
    intro a _
    rw [hba a]
    omega
  show (treeBuild n f (fun _ _ => ⊥) n).2 + (initHeaps _ covL as _).2
    + (HeapImpl.insertAll _ _).2 ≤ _
  rw [ht, h3, hsum, hg]

end Init

/-! ## Runs of updates on implemented heaps, with the exact per-update sums -/

section RunH

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]

/-- A run of updates on implemented heaps (`HeapImpl.dcUpdateH`). -/
def dcRunH (n : ℕ) (subs : ℕ × ℕ → List A) : List (ℕ × α) → HState A α → HState A α × ℕ
  | [], s => (s, 0)
  | u :: us, s =>
    ((dcRunH n subs us (dcUpdateH n subs u.1 u.2 s).1).1,
     (dcUpdateH n subs u.1 u.2 s).2 + (dcRunH n subs us (dcUpdateH n subs u.1 u.2 s).1).2)

/-- The per-update sums of `eq:dual-cover-work` along a run starting from the tree array
`tree`:

`Σ_t [ 2h + Σ_{(d, a) ∈ 𝒩_t} (⌈log₂ b_a⌉ + c) + |𝒜_t| (⌈log₂ K⌉ + c) ]`,

with `𝒩_t = changedSubs` and `𝒜_t = affected` of update `t` (`c = 1`: charged heaps,
`c = 2`: implemented heaps). -/
def dcSum (n : ℕ) (subs : ℕ × ℕ → List A) (bsz : A → ℕ) (K c : ℕ) :
    List (ℕ × α) → (ℕ → ℕ → α) → ℕ
  | [], _ => 0
  | u :: us, tree =>
    (2 * (n + 1)
      + ((changedSubs n subs u.1 u.2 tree).map (fun e => Nat.clog 2 (bsz e.2) + c)).sum
      + (affected n subs u.1 u.2 tree).length * (Nat.clog 2 K + c))
    + dcSum n subs bsz K c us (pathUpdate u.1 u.2 tree n).1

/-- Leaf values after a run of updates. -/
def leafRun (f : ℕ → α) : List (ℕ × α) → ℕ → α
  | [] => f
  | u :: us => leafRun (Function.update f u.1 u.2) us

/-- **A run of updates** (`eq:dual-cover-work`, the update terms, exactly).  From an
implemented state representing an abstract state that satisfies the index invariant, after
any list of updates:

* the implemented state represents the abstract state of `CostModel.dcRun`, which satisfies
  the invariant for the updated leaf values, and tree cells above level `n` stay blank;
* the charged cost of `dcRun` is exactly the per-update sum `dcSum … 1`;
* the computed cost on implemented heaps is at most the per-update sum `dcSum … 2`, and at
  most twice the charged cost. -/
theorem dcRunH_spec (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (bsz : A → ℕ) (acts : Finset A) (K : ℕ) (hsub : ∀ a, ∀ d ∈ cov a, a ∈ subs d)
    (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n) : ∀ (us : List (ℕ × α)) (hs : HState A α)
    (s : DCState A α) (f : ℕ → α), Sim cov bsz acts K hs s → DCInv n cov f s →
    (∀ k, n < k → ∀ j, s.tree k j = ⊥) →
    Sim cov bsz acts K (dcRunH n subs us hs).1 (dcRun n cov subs bsz K us s).1 ∧
    DCInv n cov (leafRun f us) (dcRun n cov subs bsz K us s).1 ∧
    (∀ k, n < k → ∀ j, (dcRun n cov subs bsz K us s).1.tree k j = ⊥) ∧
    (dcRun n cov subs bsz K us s).2 = dcSum n subs bsz K 1 us s.tree ∧
    (dcRunH n subs us hs).2 ≤ dcSum n subs bsz K 2 us s.tree ∧
    (dcRunH n subs us hs).2 ≤ 2 * (dcRun n cov subs bsz K us s).2 := by
  intro us
  induction us with
  | nil => intro hs s f h hi hb; exact ⟨h, hi, hb, rfl, le_rfl, le_rfl⟩
  | cons u us ih =>
    intro hs s f h hi hb
    obtain ⟨a1, a2, a3⟩ := HeapImpl.dcUpdateH_spec n cov subs bsz acts K u.1 u.2 hs s h
    have hi' := dcUpdate_inv n cov subs bsz K u.1 u.2 f s hsub hlev hi
    have hb' : ∀ k, n < k → ∀ j, (dcUpdate n cov subs bsz K u.1 u.2 s).1.tree k j = ⊥ := by
      intro k hk j
      show (pathUpdate u.1 u.2 s.tree n).1 k j = ⊥
      rw [pathUpdate_above u.1 u.2 s.tree n k j hk]
      exact hb k hk j
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ih _ _ _ a1 hi' hb'
    have hc := dcUpdate_cost n cov subs bsz K u.1 u.2 s
    refine ⟨b1, b2, b3, ?_, ?_, ?_⟩
    · show (dcUpdate n cov subs bsz K u.1 u.2 s).2
          + (dcRun n cov subs bsz K us (dcUpdate n cov subs bsz K u.1 u.2 s).1).2
        = (2 * (n + 1)
            + ((changedSubs n subs u.1 u.2 s.tree).map (fun e => Nat.clog 2 (bsz e.2) + 1)).sum
            + (affected n subs u.1 u.2 s.tree).length * (Nat.clog 2 K + 1))
          + dcSum n subs bsz K 1 us (pathUpdate u.1 u.2 s.tree n).1
      rw [hc, b4]
      rfl
    · show (dcUpdateH n subs u.1 u.2 hs).2
          + (dcRunH n subs us (dcUpdateH n subs u.1 u.2 hs).1).2
        ≤ (2 * (n + 1)
            + ((changedSubs n subs u.1 u.2 s.tree).map (fun e => Nat.clog 2 (bsz e.2) + 2)).sum
            + (affected n subs u.1 u.2 s.tree).length * (Nat.clog 2 K + 2))
          + dcSum n subs bsz K 2 us (pathUpdate u.1 u.2 s.tree n).1
      exact Nat.add_le_add a2 b5
    · show (dcUpdateH n subs u.1 u.2 hs).2
          + (dcRunH n subs us (dcUpdateH n subs u.1 u.2 hs).1).2
        ≤ 2 * ((dcUpdate n cov subs bsz K u.1 u.2 s).2
          + (dcRun n cov subs bsz K us (dcUpdate n cov subs bsz K u.1 u.2 s).1).2)
      omega

omit [DecidableEq A] in
/-- Updates at positions below `2^n` keep the leaf values blank beyond `2^n`. -/
lemma leafRun_blank {n : ℕ} : ∀ (us : List (ℕ × α)) (f : ℕ → α),
    (∀ u ∈ us, u.1 < 2 ^ n) → (∀ p, 2 ^ n ≤ p → f p = ⊥) →
    ∀ p, 2 ^ n ≤ p → leafRun f us p = ⊥ := by
  intro us
  induction us with
  | nil => intro f _ hf; exact hf
  | cons u us ih =>
    intro f hu hf
    apply ih _ (fun u' hu' => hu u' (List.mem_cons_of_mem _ hu'))
    intro p hp
    have := hu u List.mem_cons_self
    rw [Function.update_of_ne (by omega)]
    exact hf p hp

end RunH

/-! ## Memory footprint -/

section Space

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]

/-- The nodes `(k, j)`, `k ≤ n`, `j < 2^(n-k)`, of the segment tree with `2^n` leaves. -/
def nodeSet (n : ℕ) : Finset (ℕ × ℕ) :=
  (range (n + 1)).biUnion (fun k => (range (2 ^ (n - k))).image (fun j => (k, j)))

lemma mem_nodeSet {n : ℕ} {d : ℕ × ℕ} : d ∈ nodeSet n ↔ d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1) := by
  obtain ⟨k, j⟩ := d
  simp only [nodeSet, mem_biUnion, mem_range, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', j', hj', rfl, rfl⟩
    exact ⟨by omega, hj'⟩
  · rintro ⟨hk, hj⟩
    exact ⟨k, by omega, j, hj, rfl, rfl⟩

lemma nodeSet_card_le (n : ℕ) : (nodeSet n).card ≤ 2 ^ (n + 1) - 1 := by
  rw [← segTree_nodes n]
  refine card_biUnion_le.trans (sum_le_sum (fun k _ => ?_))
  exact card_image_le.trans (by simp)

/-- **Tree footprint**: the number of non-blank cells of the tree array. -/
noncomputable def treeCells (tree : ℕ → ℕ → α) : ℕ :=
  Set.ncard {d : ℕ × ℕ | tree d.1 d.2 ≠ ⊥}

/-- A tree array that holds block maxima of leaf values blank beyond `2^n` on the levels
up to `n`, and is blank above, has at most `2^(n+1) - 1` non-blank cells. -/
lemma treeCells_le (n : ℕ) (f : ℕ → α) (hf : ∀ p, 2 ^ n ≤ p → f p = ⊥) (tree : ℕ → ℕ → α)
    (h1 : ∀ k ≤ n, ∀ j, tree k j = (dyadicBlock k j).sup f)
    (h2 : ∀ k, n < k → ∀ j, tree k j = ⊥) : treeCells tree ≤ 2 ^ (n + 1) - 1 := by
  have hsub : {d : ℕ × ℕ | tree d.1 d.2 ≠ ⊥} ⊆ (↑(nodeSet n) : Set (ℕ × ℕ)) := by
    intro d hd
    rw [mem_coe, mem_nodeSet]
    by_contra hne
    apply hd
    by_cases hk : d.1 ≤ n
    · rw [h1 d.1 hk]
      exact block_sup_bot hf hk (by
        by_contra hlt
        exact hne ⟨hk, by omega⟩)
    · exact h2 _ (by omega) _
  calc treeCells tree ≤ (↑(nodeSet n) : Set (ℕ × ℕ)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (nodeSet n).card := Set.ncard_coe_finset _
    _ ≤ 2 ^ (n + 1) - 1 := nodeSet_card_le n

/-- The reverse-subscription list of a block: the actions whose cover contains it. -/
def subsOf (as : List A) (covL : A → List (ℕ × ℕ)) (d : ℕ × ℕ) : List A :=
  as.filter (fun a => d ∈ covL a)

omit [DecidableEq A] in
/-- The reverse-subscription lists have at most `B` nodes in total. -/
lemma subs_cells_le (S : Finset (ℕ × ℕ)) (covL : A → List (ℕ × ℕ)) : ∀ as : List A,
    ∑ d ∈ S, (subsOf as covL d).length ≤ (as.map (fun a => (covL a).length)).sum := by
  intro as
  induction as with
  | nil => simp [subsOf]
  | cons a as ih =>
    have h1 : ∀ d, (subsOf (a :: as) covL d).length
        = (if d ∈ covL a then 1 else 0) + (subsOf as covL d).length := by
      intro d
      unfold subsOf
      rw [List.filter_cons]
      by_cases h : d ∈ covL a
      · simp [h]; omega
      · simp [h]
    have h2 : ∑ d ∈ S, (if d ∈ covL a then 1 else 0) ≤ (covL a).length := by
      rw [← card_filter]
      refine (card_le_card (fun d hd => ?_)).trans (List.toFinset_card_le (covL a))
      exact List.mem_toFinset.2 (mem_filter.1 hd).2
    simp only [h1, sum_add_distrib, List.map_cons, List.sum_cons]
    omega

/-- **Memory footprint of the index state** (one endpoint): non-blank tree cells, the nodes
of the cover lists, the nodes of the reverse-subscription lists of the tree nodes, the
slots of the action heaps, and the slots of the global heap. -/
noncomputable def footprint (n : ℕ) (covL : A → List (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (as : List A) (hs : HState A α) : ℕ :=
  treeCells hs.tree + (as.map (fun a => (covL a).length)).sum
    + ∑ d ∈ nodeSet n, (subs d).length
    + (as.map (fun a => (hs.hp a).n)).sum + hs.gh.n

/-- **Space of the index** (one endpoint), derived from the state: whenever the implemented
state represents an abstract state satisfying the index invariant (which holds after
initialisation and after every update, by `dcInit_spec` and `dcRunH_spec`), its footprint
is at most `(2^(n+1) - 1) + 3B + K`, with `B = Σ_a b_a` the stored incidences and `K` the
number of root actions. -/
theorem footprint_le (n : ℕ) (covL : A → List (ℕ × ℕ)) (as : List A) (f : ℕ → α)
    (hf : ∀ p, 2 ^ n ≤ p → f p = ⊥) (hs : HState A α) (s : DCState A α)
    (h : Sim (fun a => (covL a).toFinset) (fun a => (covL a).length) as.toFinset as.length
      hs s) (hi : DCInv n (fun a => (covL a).toFinset) f s)
    (hb : ∀ k, n < k → ∀ j, s.tree k j = ⊥) :
    footprint n covL (subsOf as covL) as hs
      ≤ (2 ^ (n + 1) - 1) + 3 * (as.map (fun a => (covL a).length)).sum + as.length := by
  have h1 : treeCells hs.tree ≤ 2 ^ (n + 1) - 1 := by
    rw [h.tree]
    exact treeCells_le n f hf s.tree hi.tree hb
  have h2 := subs_cells_le (nodeSet n) covL as
  have h3 : (as.map (fun a => (hs.hp a).n)).sum ≤ (as.map (fun a => (covL a).length)).sum :=
    List.sum_le_sum (fun a _ => (h.hp a).size)
  have h4 : hs.gh.n ≤ as.length := h.gh.size
  unfold footprint
  omega

/-- Records of the retained graph: one per gate, one per child-list node and one per
parent-list node. -/
def graphCells (G : Dag) : ℕ :=
  G.N + ∑ p ∈ range G.N, (G.children p).length + ∑ c ∈ range G.N, (G.parents c).length

/-- The retained graph occupies at most `|V| + 2|E|` records. -/
lemma graphCells_le {G : Dag} (hG : G.WF) :
    graphCells G ≤ G.N + 2 * ∑ p ∈ range G.N, (G.children p).length := by
  have hpar : ∑ c ∈ range G.N, (G.parents c).length
      ≤ ∑ p ∈ range G.N, (G.children p).length := by
    have e1 : ∀ c ∈ range G.N, (G.parents c).length
        = ∑ p ∈ range G.N, (if c ∈ G.children p then 1 else 0) := by
      intro c _
      rw [← card_filter, ← List.toFinset_card_of_nodup (hG.parents_nodup c)]
      congr 1
      ext p
      simp only [mem_filter, mem_range, List.mem_toFinset]
      exact ⟨fun h => ⟨hG.parent_lt c p h, (hG.parents_iff c p).1 h⟩,
        fun h => (hG.parents_iff c p).2 h.2⟩
    rw [sum_congr rfl e1, sum_comm]
    apply sum_le_sum
    intro p _
    rw [← card_filter]
    refine (card_le_card (fun c hc => ?_)).trans (List.toFinset_card_le (G.children p))
    exact List.mem_toFinset.2 (mem_filter.1 hc).2
  unfold graphCells
  omega

end Space

/-! ## The index for one endpoint: initialisation, updates, queries, work and space -/

section Index

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A] [Inhabited A]

/-- **The dual-cover index for one endpoint, end to end.**  Root actions `as` (no
repetition) with cover lists `covL` (no repeated block, blocks are tree nodes, empty for
non-actions), leaf values `f` blank beyond `2^n`, and any list `us` of updates at positions
below `2^n`.  Initialise with `dcInit`, then run the updates with `dcRunH` using the
reverse-subscription lists `subsOf`.  With `b_a = |covL a|`, `B = Σ_a b_a`, `K = |as|`:

1. queries: the root of the heap of action `a` is the maximum of the current leaf values
   over the positions covered by `a`, and the root of the global heap is the maximum of
   these over the actions (each query is one read);
2. work: initialisation plus updates cost at most
   `(2^(n+1) - 1) + Σ_a (b_a (⌈log₂ b_a⌉ + 3) + 1) + K (⌈log₂ K⌉ + 2)` plus the exact
   per-update sum `Σ_t [2h + Σ_{𝒩_t} (⌈log₂ b_a⌉ + 2) + |𝒜_t| (⌈log₂ K⌉ + 2)]`;
3. space: the footprint of the state is at most `(2^(n+1) - 1) + 3B + K`.

Since `us` is arbitrary, items 1 and 3 hold at every time of a run. -/
theorem dual_cover_index (n : ℕ) (f : ℕ → α) (hf : ∀ p, 2 ^ n ≤ p → f p = ⊥)
    (covL : A → List (ℕ × ℕ)) (as : List A) (hnd : as.Nodup) (hcn : ∀ a, (covL a).Nodup)
    (hout : ∀ a, a ∉ as → covL a = [])
    (hnodes : ∀ a, ∀ d ∈ covL a, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1))
    (us : List (ℕ × α)) (hus : ∀ u ∈ us, u.1 < 2 ^ n) :
    (∀ a, findMax ((dcRunH n (subsOf as covL) us (dcInit n f covL as).1).1.hp a)
      = ((covL a).toFinset.biUnion blk).sup (leafRun f us)) ∧
    (findMax (dcRunH n (subsOf as covL) us (dcInit n f covL as).1).1.gh
      = as.toFinset.sup (fun a => ((covL a).toFinset.biUnion blk).sup (leafRun f us))) ∧
    ((dcInit n f covL as).2 + (dcRunH n (subsOf as covL) us (dcInit n f covL as).1).2
      ≤ (2 ^ (n + 1) - 1)
        + (as.map (fun a => (covL a).length * (Nat.clog 2 (covL a).length + 3) + 1)).sum
        + as.length * (Nat.clog 2 as.length + 2)
        + dcSum n (subsOf as covL) (fun a => (covL a).length) as.length 2 us
            (treeBuild n f (fun _ _ => ⊥) n).1) ∧
    (footprint n covL (subsOf as covL) as
        (dcRunH n (subsOf as covL) us (dcInit n f covL as).1).1
      ≤ (2 ^ (n + 1) - 1) + 3 * (as.map (fun a => (covL a).length)).sum + as.length) := by
  obtain ⟨i1, i2, i3, i4⟩ := dcInit_spec n f hf covL as hnd hcn hout
  have hsub : ∀ a, ∀ d ∈ (covL a).toFinset, a ∈ subsOf as covL d := by
    intro a d hd
    have hd' := List.mem_toFinset.1 hd
    have ha : a ∈ as := by
      by_contra hna
      rw [hout a hna] at hd'
      simp at hd'
    unfold subsOf
    rw [List.mem_filter]
    exact ⟨ha, by simpa using hd'⟩
  have hlev : ∀ a, ∀ d ∈ (covL a).toFinset, d.1 ≤ n :=
    fun a d hd => (hnodes a d (List.mem_toFinset.1 hd)).1
  obtain ⟨r1, r2, r3, _, r5, _⟩ := dcRunH_spec n (fun a => (covL a).toFinset)
    (subsOf as covL) (fun a => (covL a).length) as.toFinset as.length hsub hlev us
    (dcInit n f covL as).1 (dcInitAbs n f covL) f i2 i1 i3
  obtain ⟨q1, q2⟩ := HeapImpl.query_spec n (fun a => (covL a).toFinset)
    (fun a => (covL a).length) as.toFinset as.length (leafRun f us) _ _ r1 r2 hlev
  refine ⟨q1, q2, ?_, ?_⟩
  · have e : (dcInitAbs n f covL).tree = (treeBuild n f (fun _ _ => ⊥) n).1 := rfl
    rw [e] at r5
    omega
  · exact footprint_le n covL as (leafRun f us) (leafRun_blank us f hus hf) _ _ r1 r2 r3

end Index

/-! ## `thm:charged-dual-cover`: compile, initialise, run, query -/

section Final

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The compiled cover list `C_a⁺` of the support of root action `a` (empty for gates that
are not root actions). -/
def covPlus (G : Dag) (pos : ℕ → ℕ) (M : ℕ) (order as : List ℕ) (a : ℕ) : List (ℕ × ℕ) :=
  if a ∈ as then
    (dualCompile (Nat.clog 2 M) M ((runPhase G pos order (fun _ => [])).1 a)).1.1
  else []

/-- The compiled cover list `C_a⁻` of the complement of the support of root action `a`. -/
def covMinus (G : Dag) (pos : ℕ → ℕ) (M : ℕ) (order as : List ℕ) (a : ℕ) : List (ℕ × ℕ) :=
  if a ∈ as then
    (dualCompile (Nat.clog 2 M) M ((runPhase G pos order (fun _ => [])).1 a)).1.2
  else []

lemma incidences_map {β : Type*} (g : β → List (ℕ × ℕ) × List (ℕ × ℕ)) : ∀ l : List β,
    incidences (l.map g)
      = (l.map (fun a => (g a).1.length)).sum + (l.map (fun a => (g a).2.length)).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, incidences, List.sum_cons, ih]
    omega

/-- **`thm:charged-dual-cover`, assembled** (`eq:dual-cover-work` and the space claim).

Circuit `G` with gates `order` (by nondecreasing level, closed under children), terminal
layout positions `pos` in `[0, M)`, supports `supp`, root actions `as` (gates of `order`,
no repetition).  Let `n = ⌈log₂ M⌉`, `h = n + 1`, `K = |as|`, `R_run = Σ_a r_a`.

Program: the run-merging phase and the dual-cover compiler
(`RunMerge.charged_dual_cover_compile`), giving the cover lists `C_a⁺ = covPlus` and
`C_a⁻ = covMinus` with `B` stored incidences; initialisation (`dcInit`) of one index on the
lower values `fl` with the covers `C⁺` and one on the upper values `fu` with the covers
`C⁻`; any lists `usl`, `usu` of lower and upper terminal updates; `Q` queries of one unit.

1. Covers: `C_a⁺` covers `supp a`, `C_a⁻` covers `[0, M) \ supp a`, and
   `B ≤ 2h(2 R_run + K)`.
2. Queries: at the end of the run (hence at every time, the update lists being arbitrary)
   the root of the heap of `a` in the lower index is the maximum of the current lower
   values over `supp a`, and in the upper index the maximum of the current upper values
   over the complement.
3. Work, with `P_G = Σ_{v ∈ order} gateCost v` (`eq:dual-run-compilation`):

   `W ≤ P_G + 4h(2 R_run + K) + B + 2(2^(n+1) - 1) + Σ_a (b_a⁺(⌈log₂ b_a⁺⌉ + 3) + 1)
        + Σ_a (b_a⁻(⌈log₂ b_a⁻⌉ + 3) + 1) + 2K(⌈log₂ K⌉ + 2)
        + Σ_t [2h + Σ_{𝒩_t⁺}(⌈log₂ b_a⁺⌉ + 2) + |𝒜_t⁺|(⌈log₂ K⌉ + 2)]
        + Σ_t [2h + Σ_{𝒩_t⁻}(⌈log₂ b_a⁻⌉ + 2) + |𝒜_t⁻|(⌈log₂ K⌉ + 2)] + Q`.
4. Space: the retained graph and the two index states together occupy at most
   `|V| + 2|E| + 2(2^(n+1) - 1) + 3B + 2K ≤ |V| + 2|E| + 8M + 3B + 2K` cells. -/
theorem dual_cover_work_final (G : Dag) (hG : G.WF) (pos : ℕ → ℕ) (M : ℕ) (hM1 : 1 ≤ M)
    (supp : ℕ → Finset ℕ) (order : List ℕ)
    (hsorted : order.Pairwise (fun a b => G.level a ≤ G.level b))
    (hclosed : ∀ g ∈ order, ∀ c ∈ G.children g, c ∈ order)
    (hleaf : ∀ g ∈ order, G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order, G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp)
    (as : List ℕ) (has : ∀ a ∈ as, a ∈ order) (hnd : as.Nodup)
    (fl fu : ℕ → α) (hfl : ∀ p, 2 ^ Nat.clog 2 M ≤ p → fl p = ⊥)
    (hfu : ∀ p, 2 ^ Nat.clog 2 M ≤ p → fu p = ⊥)
    (usl usu : List (ℕ × α)) (husl : ∀ u ∈ usl, u.1 < 2 ^ Nat.clog 2 M)
    (husu : ∀ u ∈ usu, u.1 < 2 ^ Nat.clog 2 M) (Q : ℕ) :
    (∀ a ∈ as,
      IsDyadicCover ((covPlus G pos M order as a).map blk).toFinset (supp a) ∧
      IsDyadicCover ((covMinus G pos M order as a).map blk).toFinset (range M \ supp a)) ∧
    ((as.map (fun a => (covPlus G pos M order as a).length)).sum
        + (as.map (fun a => (covMinus G pos M order as a).length)).sum
      ≤ 2 * (1 + Nat.clog 2 M)
        * (2 * (as.map (fun a => runs (supp a))).sum + as.length)) ∧
    (∀ a ∈ as,
      findMax ((dcRunH (Nat.clog 2 M) (subsOf as (covPlus G pos M order as)) usl
          (dcInit (Nat.clog 2 M) fl (covPlus G pos M order as) as).1).1.hp a)
        = (supp a).sup (leafRun fl usl) ∧
      findMax ((dcRunH (Nat.clog 2 M) (subsOf as (covMinus G pos M order as)) usu
          (dcInit (Nat.clog 2 M) fu (covMinus G pos M order as) as).1).1.hp a)
        = (range M \ supp a).sup (leafRun fu usu)) ∧
    ((runPhase G pos order (fun _ => [])).2
        + (compileAll (Nat.clog 2 M) M
            (as.map (runPhase G pos order (fun _ => [])).1)).2
        + (dcInit (Nat.clog 2 M) fl (covPlus G pos M order as) as).2
        + (dcRunH (Nat.clog 2 M) (subsOf as (covPlus G pos M order as)) usl
            (dcInit (Nat.clog 2 M) fl (covPlus G pos M order as) as).1).2
        + (dcInit (Nat.clog 2 M) fu (covMinus G pos M order as) as).2
        + (dcRunH (Nat.clog 2 M) (subsOf as (covMinus G pos M order as)) usu
            (dcInit (Nat.clog 2 M) fu (covMinus G pos M order as) as).1).2
        + Q * 1
      ≤ (order.map (gateCost G supp)).sum
        + 4 * (1 + Nat.clog 2 M) * (2 * (as.map (fun a => runs (supp a))).sum + as.length)
        + ((as.map (fun a => (covPlus G pos M order as a).length)).sum
            + (as.map (fun a => (covMinus G pos M order as a).length)).sum)
        + 2 * (2 ^ (Nat.clog 2 M + 1) - 1)
        + (as.map (fun a => (covPlus G pos M order as a).length
            * (Nat.clog 2 (covPlus G pos M order as a).length + 3) + 1)).sum
        + (as.map (fun a => (covMinus G pos M order as a).length
            * (Nat.clog 2 (covMinus G pos M order as a).length + 3) + 1)).sum
        + 2 * (as.length * (Nat.clog 2 as.length + 2))
        + dcSum (Nat.clog 2 M) (subsOf as (covPlus G pos M order as))
            (fun a => (covPlus G pos M order as a).length) as.length 2 usl
            (treeBuild (Nat.clog 2 M) fl (fun _ _ => ⊥) (Nat.clog 2 M)).1
        + dcSum (Nat.clog 2 M) (subsOf as (covMinus G pos M order as))
            (fun a => (covMinus G pos M order as a).length) as.length 2 usu
            (treeBuild (Nat.clog 2 M) fu (fun _ _ => ⊥) (Nat.clog 2 M)).1
        + Q) ∧
    (graphCells G
        + footprint (Nat.clog 2 M) (covPlus G pos M order as)
            (subsOf as (covPlus G pos M order as)) as
            (dcRunH (Nat.clog 2 M) (subsOf as (covPlus G pos M order as)) usl
              (dcInit (Nat.clog 2 M) fl (covPlus G pos M order as) as).1).1
        + footprint (Nat.clog 2 M) (covMinus G pos M order as)
            (subsOf as (covMinus G pos M order as)) as
            (dcRunH (Nat.clog 2 M) (subsOf as (covMinus G pos M order as)) usu
              (dcInit (Nat.clog 2 M) fu (covMinus G pos M order as) as).1).1
      ≤ G.N + 2 * ∑ p ∈ range G.N, (G.children p).length + 8 * M
        + 3 * ((as.map (fun a => (covPlus G pos M order as a).length)).sum
            + (as.map (fun a => (covMinus G pos M order as a).length)).sum)
        + 2 * as.length) := by
  have hM : M ≤ 2 ^ Nat.clog 2 M := Nat.le_pow_clog (by norm_num) M
  obtain ⟨p1, _⟩ := runPhase_spec G pos M supp hG.level_lt order hsorted hclosed hleaf hgate
    (fun _ => [])
  obtain ⟨c1, c2, c3, c4, _⟩ := charged_dual_cover_compile G pos M supp hG.level_lt order
    hsorted hclosed hleaf hgate as has
  have hP : ∀ a ∈ as, covPlus G pos M order as a
      = (dualCompile (Nat.clog 2 M) M ((runPhase G pos order (fun _ => [])).1 a)).1.1 :=
    fun a ha => by unfold covPlus; rw [ite_eq_left ha]
  have hMn : ∀ a ∈ as, covMinus G pos M order as a
      = (dualCompile (Nat.clog 2 M) M ((runPhase G pos order (fun _ => [])).1 a)).1.2 :=
    fun a ha => by unfold covMinus; rw [ite_eq_left ha]
  have hPout : ∀ a, a ∉ as → covPlus G pos M order as a = [] :=
    fun a ha => by unfold covPlus; rw [ite_eq_right ha]
  have hMout : ∀ a, a ∉ as → covMinus G pos M order as a = [] :=
    fun a ha => by unfold covMinus; rw [ite_eq_right ha]
  have hlists : ∀ a ∈ as, _ := fun a ha =>
    dualCompile_lists (Nat.clog 2 M) M hM _ (p1 a (has a ha)).1
  have hPnd : ∀ a, (covPlus G pos M order as a).Nodup := by
    intro a
    by_cases ha : a ∈ as
    · rw [hP a ha]; exact (hlists a ha).1
    · rw [hPout a ha]; exact List.nodup_nil
  have hMnd : ∀ a, (covMinus G pos M order as a).Nodup := by
    intro a
    by_cases ha : a ∈ as
    · rw [hMn a ha]; exact (hlists a ha).2.1
    · rw [hMout a ha]; exact List.nodup_nil
  have hPnodes : ∀ a, ∀ d ∈ covPlus G pos M order as a,
      d.1 ≤ Nat.clog 2 M ∧ d.2 < 2 ^ (Nat.clog 2 M - d.1) := by
    intro a d hd
    by_cases ha : a ∈ as
    · rw [hP a ha] at hd; exact (hlists a ha).2.2.1 d hd
    · rw [hPout a ha] at hd; simp at hd
  have hMnodes : ∀ a, ∀ d ∈ covMinus G pos M order as a,
      d.1 ≤ Nat.clog 2 M ∧ d.2 < 2 ^ (Nat.clog 2 M - d.1) := by
    intro a d hd
    by_cases ha : a ∈ as
    · rw [hMn a ha] at hd; exact (hlists a ha).2.2.2 d hd
    · rw [hMout a ha] at hd; simp at hd
  have hcover : ∀ a ∈ as,
      IsDyadicCover ((covPlus G pos M order as a).map blk).toFinset (supp a) ∧
      IsDyadicCover ((covMinus G pos M order as a).map blk).toFinset (range M \ supp a) := by
    intro a ha
    rw [hP a ha, hMn a ha]
    exact c1 a ha
  have hB : (as.map (fun a => (covPlus G pos M order as a).length)).sum
        + (as.map (fun a => (covMinus G pos M order as a).length)).sum
      = incidences (compileAll (Nat.clog 2 M) M
          (as.map (runPhase G pos order (fun _ => [])).1)).1 := by
    have c2' : (compileAll (Nat.clog 2 M) M (as.map (runPhase G pos order (fun _ => [])).1)).1
        = as.map (fun a => (dualCompile (Nat.clog 2 M) M
            ((runPhase G pos order (fun _ => [])).1 a)).1) := c2
    rw [c2', incidences_map]
    congr 1
    · congr 1
      exact List.map_congr_left (fun a ha => by rw [hP a ha])
    · congr 1
      exact List.map_congr_left (fun a ha => by rw [hMn a ha])
  obtain ⟨x1, _, x3, x4⟩ := dual_cover_index (Nat.clog 2 M) fl hfl
    (covPlus G pos M order as) as hnd hPnd hPout hPnodes usl husl
  obtain ⟨y1, _, y3, y4⟩ := dual_cover_index (Nat.clog 2 M) fu hfu
    (covMinus G pos M order as) as hnd hMnd hMout hMnodes usu husu
  have c3' : incidences (compileAll (Nat.clog 2 M) M
        (as.map (runPhase G pos order (fun _ => [])).1)).1
      ≤ 2 * (1 + Nat.clog 2 M)
        * (2 * (as.map (fun a => runs (supp a))).sum + as.length) := c3
  have c4' : (runPhase G pos order (fun _ => [])).2
        + (compileAll (Nat.clog 2 M) M (as.map (runPhase G pos order (fun _ => [])).1)).2
      ≤ (order.map (gateCost G supp)).sum
        + 4 * (1 + Nat.clog 2 M) * (2 * (as.map (fun a => runs (supp a))).sum + as.length)
        + incidences (compileAll (Nat.clog 2 M) M
            (as.map (runPhase G pos order (fun _ => [])).1)).1 := c4
  refine ⟨hcover, by rw [hB]; exact c3', fun a ha => ?_, ?_, ?_⟩
  · rw [x1 a, y1 a, biUnion_blk_of_cover (hcover a ha).1, biUnion_blk_of_cover (hcover a ha).2]
    exact ⟨rfl, rfl⟩
  · rw [hB]
    omega
  · have hg := graphCells_le hG
    have hn := segTree_nodes_lt M hM1
    omega

end Final

end DualCoverFinal
end JointRootCert
