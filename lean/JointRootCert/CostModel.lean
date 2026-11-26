/-
Joint Root Certification: a cost model for charged dual covers.

Manuscript: Part III, section "Efficient Algorithms and Certified Numerical Methods",
subsection `app:representation`.  Results covered:

* `thm:adaptive-oracle-coupling` / `thm:charged-dual-cover` (Exact coupling and charged
  maintenance): the compile-work claim `O((R_run + K) h + B)` (given the run lists produced
  by the graph run-merging phase `P_G`), the incidence bound `B ≤ 2h(2 R_run + K)` for the
  canonical segment-tree decomposition that is actually executed, and the update-work claim
  "`O(h)` tree work plus changed-subscription heap work" (`eq:dual-cover-work`, one update).

## Cost model and its correspondence with the unit-cost RAM

A costed program is a Lean function returning a pair `(result, cost)` with `cost : ℕ`.  The
cost is computed by the same recursion that computes the result; it is never an argument or
a hypothesis.  The cost of a composite program is the sum of the costs of its parts.

One cost unit stands for a bounded number of unit-cost RAM operations (comparisons, pointer
follows, array reads and writes):

* visiting one segment-tree node in a range query (at most four comparisons): 1 unit;
* appending one block to an output list: 1 unit;
* one step of a linear scan over a run list: 1 unit;
* recomputing one segment-tree node from its two children (two reads, one `max`, one
  write): 1 unit; comparing one node with its previous value: 1 unit;
* one indexed-heap key update in a heap of `m` keys: `⌈log₂ m⌉ + 1` units (the worst-case
  sift length of a binary heap plus the handle lookup).  Indexed heaps are a PRIMITIVE of the
  model: a heap is represented by the keys it stores and its maximum is the supremum of
  those keys (`find-max` is a read of the heap root).  The sift procedure itself is not
  implemented, so the `⌈log₂ m⌉ + 1` charge is the one modelling assumption.

Arrays are modelled as functions (`ℕ → ℕ → α` for the segment tree indexed by level and
position); a program is charged for each cell it reads or writes, not for the function.

What is NOT modelled here: the graph run-merging phase with cost `P_G`
(`eq:dual-run-compilation`), whose output (the sorted run list of each root support) is the
input of the compiler below; and the `|V| + |E|` part of the space claim.
-/
import JointRootCert.Representation

namespace JointRootCert
namespace CostModel

open Finset _root_.JointRootCert.Representation

/-! ## The segment tree: canonical dyadic decomposition with visit count -/

/-- The block of a segment-tree node given by `(level, index)`. -/
def blk (d : ℕ × ℕ) : Finset ℕ := dyadicBlock d.1 d.2

lemma dyadicBlock_zero (j : ℕ) : dyadicBlock 0 j = {j} := by
  ext x
  simp only [dyadicBlock, mem_Ico, mem_singleton, pow_zero, mul_one]
  omega

/-- A node's block is the disjoint union of its two children's blocks. -/
lemma dyadicBlock_succ (k j : ℕ) :
    dyadicBlock (k + 1) j = dyadicBlock k (2 * j) ∪ dyadicBlock k (2 * j + 1) := by
  unfold dyadicBlock
  have e1 : j * 2 ^ (k + 1) = 2 * j * 2 ^ k := by ring
  have e3 : (j + 1) * 2 ^ (k + 1) = (2 * j + 1 + 1) * 2 ^ k := by ring
  rw [e1, e3]
  exact (Ico_union_Ico_eq_Ico (Nat.mul_le_mul_right _ (by omega))
    (Nat.mul_le_mul_right _ (by omega))).symm

lemma index_of_mem_dyadicBlock {k j p : ℕ} (h : p ∈ dyadicBlock k j) : j = p / 2 ^ k := by
  simp only [dyadicBlock, mem_Ico] at h
  exact (Nat.div_eq_of_lt_le h.1 h.2).symm

lemma node_arith (k j : ℕ) :
    j * 2 ^ (k + 1) = 2 * (j * 2 ^ k) ∧ (j + 1) * 2 ^ (k + 1) = 2 * (j * 2 ^ k) + 2 * 2 ^ k ∧
    2 * j * 2 ^ k = 2 * (j * 2 ^ k) ∧ (2 * j + 1) * 2 ^ k = 2 * (j * 2 ^ k) + 2 ^ k ∧
    (2 * j + 1 + 1) * 2 ^ k = 2 * (j * 2 ^ k) + 2 * 2 ^ k ∧ 0 < 2 ^ k :=
  ⟨by ring, by ring, by ring, by ring, by ring, by positivity⟩

/-- **Canonical segment-tree range query.**  `segQuery a b k j` visits the node
`(k, j)` (block `[j 2^k, (j+1) 2^k)`) for the query interval `[a, b)`: it returns
nothing if the block is disjoint from the query, the node itself if the block is contained
in the query, and otherwise recurses into both children.  The second component counts the
nodes visited. -/
def segQuery (a b : ℕ) : ℕ → ℕ → List (ℕ × ℕ) × ℕ
  | 0, j => if a ≤ j ∧ j < b then ([(0, j)], 1) else ([], 1)
  | k + 1, j =>
    if b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a then ([], 1)
    else if a ≤ j * 2 ^ (k + 1) ∧ (j + 1) * 2 ^ (k + 1) ≤ b then ([(k + 1, j)], 1)
    else ((segQuery a b k (2 * j)).1 ++ (segQuery a b k (2 * j + 1)).1,
          1 + (segQuery a b k (2 * j)).2 + (segQuery a b k (2 * j + 1)).2)

lemma segQuery_of_disjoint (a b : ℕ) : ∀ k j, (b ≤ j * 2 ^ k ∨ (j + 1) * 2 ^ k ≤ a) →
    segQuery a b k j = ([], 1)
  | 0, j, h => by
    simp only [pow_zero, mul_one] at h
    have hn : ¬ (a ≤ j ∧ j < b) := by omega
    simp only [segQuery]
    rw [ite_eq_right hn]
  | k + 1, j, h => by
    simp only [segQuery]
    rw [ite_eq_left h]

lemma segQuery_of_contained (a b : ℕ) : ∀ k j, a ≤ j * 2 ^ k → (j + 1) * 2 ^ k ≤ b →
    segQuery a b k j = ([(k, j)], 1)
  | 0, j, h1, h2 => by
    simp only [pow_zero, mul_one] at h1 h2
    have hp : a ≤ j ∧ j < b := by omega
    simp only [segQuery]
    rw [ite_eq_left hp]
  | k + 1, j, h1, h2 => by
    have hpos : 0 < 2 ^ (k + 1) := by positivity
    have e : (j + 1) * 2 ^ (k + 1) = j * 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    have hd : ¬ (b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a) := by omega
    simp only [segQuery]
    rw [ite_eq_right hd, ite_eq_left ⟨h1, h2⟩]

lemma segQuery_split (a b k j : ℕ)
    (hd : ¬ (b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a))
    (hc : ¬ (a ≤ j * 2 ^ (k + 1) ∧ (j + 1) * 2 ^ (k + 1) ≤ b)) :
    segQuery a b (k + 1) j
      = ((segQuery a b k (2 * j)).1 ++ (segQuery a b k (2 * j + 1)).1,
          1 + (segQuery a b k (2 * j)).2 + (segQuery a b k (2 * j + 1)).2) := by
  simp only [segQuery]
  rw [ite_eq_right hd, ite_eq_right hc]

/-- **Correctness of the range query.**  The blocks returned at node `(k, j)` form a
dyadic cover of the part of `[a, b)` inside the node's block. -/
theorem segQuery_cover (a b : ℕ) : ∀ k j,
    IsDyadicCover ((segQuery a b k j).1.map blk).toFinset (Ico a b ∩ dyadicBlock k j) := by
  intro k
  induction k with
  | zero =>
    intro j
    by_cases h : a ≤ j ∧ j < b
    · have e : Ico a b ∩ dyadicBlock 0 j = dyadicBlock 0 j := by
        rw [dyadicBlock_zero]
        ext x
        simp only [mem_inter, mem_Ico, mem_singleton]
        omega
      have hq : segQuery a b 0 j = ([(0, j)], 1) := by
        simp only [segQuery]
        rw [ite_eq_left h]
      rw [e, hq]
      simpa [blk] using IsDyadicCover.single 0 j
    · have e : Ico a b ∩ dyadicBlock 0 j = ∅ := by
        rw [dyadicBlock_zero]
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        simp only [mem_inter, mem_Ico, mem_singleton] at hx
        omega
      have hq : segQuery a b 0 j = ([], 1) := by
        simp only [segQuery]
        rw [ite_eq_right h]
      rw [e, hq]
      simpa using IsDyadicCover.empty
  | succ k ih =>
    intro j
    by_cases hd : b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a
    · rw [segQuery_of_disjoint a b (k + 1) j hd]
      have e : Ico a b ∩ dyadicBlock (k + 1) j = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        simp only [mem_inter, mem_Ico, dyadicBlock] at hx
        omega
      rw [e]
      simpa using IsDyadicCover.empty
    by_cases hc : a ≤ j * 2 ^ (k + 1) ∧ (j + 1) * 2 ^ (k + 1) ≤ b
    · rw [segQuery_of_contained a b (k + 1) j hc.1 hc.2]
      have e : Ico a b ∩ dyadicBlock (k + 1) j = dyadicBlock (k + 1) j := by
        apply inter_eq_right.2
        intro x hx
        simp only [mem_Ico, dyadicBlock] at hx ⊢
        omega
      rw [e]
      simpa [blk] using IsDyadicCover.single (k + 1) j
    · simp only [segQuery_split a b k j hd hc, List.map_append, List.toFinset_append]
      rw [dyadicBlock_succ, inter_union_distrib_left]
      refine (ih (2 * j)).append (ih (2 * j + 1)) ?_
      have hdis : Disjoint (dyadicBlock k (2 * j)) (dyadicBlock k (2 * j + 1)) := by
        unfold dyadicBlock
        exact Ico_disjoint_Ico_consecutive _ _ _
      exact hdis.mono inter_subset_right inter_subset_right

/-- A query whose left end is at or before the node's left end (a prefix query) returns at
most `k + 1` blocks and visits at most `2k + 1` nodes. -/
lemma segQuery_prefix (a b : ℕ) : ∀ k j, a ≤ j * 2 ^ k →
    (segQuery a b k j).1.length ≤ k + 1 ∧ (segQuery a b k j).2 ≤ 2 * k + 1 := by
  intro k
  induction k with
  | zero =>
    intro j _
    simp only [segQuery]
    split_ifs <;> simp
  | succ k ih =>
    intro j ha
    obtain ⟨e1, e2, e3, e4, e5, hp⟩ := node_arith k j
    by_cases hd : b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a
    · rw [segQuery_of_disjoint a b (k + 1) j hd]
      constructor <;> simp
    by_cases hc' : (j + 1) * 2 ^ (k + 1) ≤ b
    · rw [segQuery_of_contained a b (k + 1) j ha hc']
      constructor <;> simp
    rw [segQuery_split a b k j hd (fun h => hc' h.2)]
    by_cases hm : b ≤ (2 * j + 1) * 2 ^ k
    · have hr := segQuery_of_disjoint a b k (2 * j + 1) (Or.inl hm)
      obtain ⟨h1, h2⟩ := ih (2 * j) (by omega)
      simp only [hr, List.length_append, List.length_nil]
      omega
    · have hl := segQuery_of_contained a b k (2 * j) (by omega) (by omega)
      obtain ⟨h1, h2⟩ := ih (2 * j + 1) (by omega)
      simp only [hl, List.length_append, List.length_cons, List.length_nil]
      omega

/-- A query whose right end is at or after the node's right end (a suffix query) returns at
most `k + 1` blocks and visits at most `2k + 1` nodes. -/
lemma segQuery_suffix (a b : ℕ) : ∀ k j, (j + 1) * 2 ^ k ≤ b →
    (segQuery a b k j).1.length ≤ k + 1 ∧ (segQuery a b k j).2 ≤ 2 * k + 1 := by
  intro k
  induction k with
  | zero =>
    intro j _
    simp only [segQuery]
    split_ifs <;> simp
  | succ k ih =>
    intro j hb
    obtain ⟨e1, e2, e3, e4, e5, hp⟩ := node_arith k j
    by_cases hd : b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a
    · rw [segQuery_of_disjoint a b (k + 1) j hd]
      constructor <;> simp
    by_cases hc' : a ≤ j * 2 ^ (k + 1)
    · rw [segQuery_of_contained a b (k + 1) j hc' hb]
      constructor <;> simp
    rw [segQuery_split a b k j hd (fun h => hc' h.1)]
    by_cases hm : (2 * j + 1) * 2 ^ k ≤ a
    · have hl := segQuery_of_disjoint a b k (2 * j) (Or.inr hm)
      obtain ⟨h1, h2⟩ := ih (2 * j + 1) (by omega)
      simp only [hl, List.length_append, List.length_nil]
      omega
    · have hr := segQuery_of_contained a b k (2 * j + 1) (by omega) (by omega)
      obtain ⟨h1, h2⟩ := ih (2 * j) (by omega)
      simp only [hr, List.length_append, List.length_cons, List.length_nil]
      omega

/-- **Block and visit bounds of the canonical decomposition.**  At a node of level `k` the
range query returns at most `2k + 1` blocks and visits at most `4k + 1` nodes, for every
query interval. -/
theorem segQuery_bound (a b : ℕ) : ∀ k j,
    (segQuery a b k j).1.length ≤ 2 * k + 1 ∧ (segQuery a b k j).2 ≤ 4 * k + 1 := by
  intro k
  induction k with
  | zero =>
    intro j
    simp only [segQuery]
    split_ifs <;> simp
  | succ k ih =>
    intro j
    obtain ⟨e1, e2, e3, e4, e5, hp⟩ := node_arith k j
    by_cases hd : b ≤ j * 2 ^ (k + 1) ∨ (j + 1) * 2 ^ (k + 1) ≤ a
    · rw [segQuery_of_disjoint a b (k + 1) j hd]
      constructor <;> simp
    by_cases hc : a ≤ j * 2 ^ (k + 1) ∧ (j + 1) * 2 ^ (k + 1) ≤ b
    · rw [segQuery_of_contained a b (k + 1) j hc.1 hc.2]
      constructor <;> simp
    rw [segQuery_split a b k j hd hc]
    by_cases hm : b ≤ (2 * j + 1) * 2 ^ k
    · have hr := segQuery_of_disjoint a b k (2 * j + 1) (Or.inl hm)
      obtain ⟨h1, h2⟩ := ih (2 * j)
      simp only [hr, List.length_append, List.length_nil]
      omega
    by_cases hm' : (2 * j + 1) * 2 ^ k ≤ a
    · have hl := segQuery_of_disjoint a b k (2 * j) (Or.inr hm')
      obtain ⟨h1, h2⟩ := ih (2 * j + 1)
      simp only [hl, List.length_append, List.length_nil]
      omega
    · obtain ⟨h1, h2⟩ := segQuery_suffix a b k (2 * j) (by omega)
      obtain ⟨h3, h4⟩ := segQuery_prefix a b k (2 * j + 1) (by omega)
      simp only [List.length_append]
      omega

/-! ## Run lists, complements, and the dual-cover compiler -/

/-- Positions described by a list of half-open intervals `[a, b)`. -/
def runSet : List (ℕ × ℕ) → Finset ℕ
  | [] => ∅
  | p :: rest => Ico p.1 p.2 ∪ runSet rest

/-- A sorted list of pairwise disjoint (possibly empty or adjacent) intervals inside
`[lo, M)`. -/
def IvlsFrom (M : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | lo, p :: rest => lo ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ M ∧ IvlsFrom M p.2 rest

/-- A run list inside `[lo, M)`: sorted nonempty intervals separated by at least one
position, i.e. the list of maximal contiguous runs of its position set.  This is the output
format of the graph run-merging phase. -/
def RunsFrom (M : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | lo, p :: rest => lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ M ∧ RunsFrom M (p.2 + 1) rest

lemma IvlsFrom.mono {M lo lo' : ℕ} {rl : List (ℕ × ℕ)} (h : lo' ≤ lo)
    (hr : IvlsFrom M lo rl) : IvlsFrom M lo' rl := by
  cases rl with
  | nil => simp [IvlsFrom]
  | cons p rest =>
    simp only [IvlsFrom] at hr ⊢
    exact ⟨h.trans hr.1, hr.2⟩

lemma RunsFrom.mono {M lo lo' : ℕ} {rl : List (ℕ × ℕ)} (h : lo' ≤ lo)
    (hr : RunsFrom M lo rl) : RunsFrom M lo' rl := by
  cases rl with
  | nil => simp [RunsFrom]
  | cons p rest =>
    simp only [RunsFrom] at hr ⊢
    exact ⟨h.trans hr.1, hr.2⟩

lemma RunsFrom.ivls {M : ℕ} {rl : List (ℕ × ℕ)} :
    ∀ {lo : ℕ}, RunsFrom M lo rl → IvlsFrom M lo rl := by
  induction rl with
  | nil => intro lo _; simp [IvlsFrom]
  | cons p rest ih =>
    intro lo h
    simp only [RunsFrom] at h
    simp only [IvlsFrom]
    exact ⟨h.1, h.2.1.le, h.2.2.1, (ih h.2.2.2).mono (Nat.le_succ _)⟩

lemma runSet_bounds {M : ℕ} {rl : List (ℕ × ℕ)} :
    ∀ {lo : ℕ}, IvlsFrom M lo rl → ∀ x ∈ runSet rl, lo ≤ x ∧ x < M := by
  induction rl with
  | nil => intro lo _ x hx; simp [runSet] at hx
  | cons p rest ih =>
    intro lo h x hx
    simp only [IvlsFrom] at h
    simp only [runSet, mem_union, mem_Ico] at hx
    rcases hx with hx | hx
    · omega
    · have := ih h.2.2.2 x hx
      omega

/-- A run list has as many entries as its position set has maximal runs. -/
theorem runs_runSet {M : ℕ} {rl : List (ℕ × ℕ)} :
    ∀ {lo : ℕ}, RunsFrom M lo rl → runs (runSet rl) = rl.length := by
  induction rl with
  | nil => intro lo _; simp [runSet, runs, runEnds]
  | cons p rest ih =>
    intro lo h
    simp only [RunsFrom] at h
    have hR : ∀ y ∈ runSet rest, p.2 + 1 ≤ y := fun y hy => (runSet_bounds h.2.2.2.ivls y hy).1
    have hrest := ih h.2.2.2
    have hnot : p.2 - 1 ∉ runEnds (runSet rest) := by
      intro hmem
      have := hR _ (mem_filter.1 hmem).1
      omega
    have heq : runEnds (runSet (p :: rest)) = insert (p.2 - 1) (runEnds (runSet rest)) := by
      ext x
      simp only [runEnds, runSet, mem_filter, mem_union, mem_Ico, mem_insert]
      constructor
      · rintro ⟨hx | hx, hx1⟩
        · left
          by_contra hne
          exact hx1 (Or.inl (by omega))
        · exact Or.inr ⟨hx, fun h' => hx1 (Or.inr h')⟩
      · rintro (hx | ⟨hx, hx1⟩)
        · refine ⟨Or.inl (by omega), ?_⟩
          rintro (h' | h')
          · omega
          · have := hR _ h'
            omega
        · refine ⟨Or.inr hx, ?_⟩
          rintro (h' | h')
          · have := hR _ hx
            omega
          · exact hx1 h'
    unfold runs at hrest ⊢
    rw [heq, card_insert_of_notMem hnot, hrest, List.length_cons]

/-- **Complement scan.**  From the run list of a support inside `[lo, M)`, list the gaps
(the runs of the complement) by one linear scan; one cost unit per run plus one. -/
def gaps (M : ℕ) : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) × ℕ
  | lo, [] => if lo < M then ([(lo, M)], 1) else ([], 1)
  | lo, p :: rest =>
    if lo < p.1 then ((lo, p.1) :: (gaps M p.2 rest).1, 1 + (gaps M p.2 rest).2)
    else ((gaps M p.2 rest).1, 1 + (gaps M p.2 rest).2)

lemma gaps_cost (M : ℕ) (rl : List (ℕ × ℕ)) : ∀ lo, (gaps M lo rl).2 = rl.length + 1 := by
  induction rl with
  | nil => intro lo; simp only [gaps]; split_ifs <;> simp
  | cons p rest ih =>
    intro lo
    simp only [gaps]
    split_ifs <;> simp only [ih, List.length_cons] <;> omega

lemma gaps_length (M : ℕ) (rl : List (ℕ × ℕ)) :
    ∀ lo, (gaps M lo rl).1.length ≤ rl.length + 1 := by
  induction rl with
  | nil => intro lo; simp only [gaps]; split_ifs <;> simp
  | cons p rest ih =>
    intro lo
    have := ih p.2
    simp only [gaps]
    split_ifs <;> simp only [List.length_cons] <;> omega

lemma gaps_ivls (M : ℕ) (rl : List (ℕ × ℕ)) :
    ∀ lo, IvlsFrom M lo rl → IvlsFrom M lo (gaps M lo rl).1 := by
  induction rl with
  | nil =>
    intro lo _
    simp only [gaps]
    split_ifs with h
    · simp [IvlsFrom, h.le]
    · simp [IvlsFrom]
  | cons p rest ih =>
    intro lo h
    simp only [IvlsFrom] at h
    have h' := ih p.2 h.2.2.2
    simp only [gaps]
    split_ifs with hlt
    · simp only [IvlsFrom]
      exact ⟨le_rfl, hlt.le, h.2.1.trans h.2.2.1, h'.mono h.2.1⟩
    · exact h'.mono (h.1.trans h.2.1)

/-- The gaps are exactly the complement of the support inside `[lo, M)`. -/
lemma gaps_set (M : ℕ) (rl : List (ℕ × ℕ)) :
    ∀ lo, IvlsFrom M lo rl → runSet (gaps M lo rl).1 = Ico lo M \ runSet rl := by
  induction rl with
  | nil =>
    intro lo _
    simp only [gaps]
    split_ifs with h
    · simp [runSet]
    · simp only [runSet, sdiff_empty]
      exact (Ico_eq_empty (by omega)).symm
  | cons p rest ih =>
    intro lo h
    simp only [IvlsFrom] at h
    have hR := runSet_bounds h.2.2.2
    have h' := ih p.2 h.2.2.2
    ext x
    have hRx : x ∈ runSet rest → p.2 ≤ x := fun hx => (hR x hx).1
    simp only [gaps]
    split_ifs with hlt
    · simp only [runSet, h', mem_union, mem_sdiff, mem_Ico]
      constructor
      · rintro (hx | ⟨hx, hx'⟩)
        · refine ⟨by omega, ?_⟩
          rintro (h1 | h1)
          · omega
          · have := hRx h1
            omega
        · refine ⟨by omega, ?_⟩
          rintro (h1 | h1)
          · omega
          · exact hx' h1
      · rintro ⟨hx, hx'⟩
        by_cases hxp : x < p.1
        · exact Or.inl ⟨hx.1, hxp⟩
        · refine Or.inr ⟨⟨?_, hx.2⟩, fun h1 => hx' (Or.inr h1)⟩
          by_contra hlt2
          exact hx' (Or.inl ⟨by omega, by omega⟩)
    · simp only [runSet, h', mem_union, mem_sdiff, mem_Ico]
      constructor
      · rintro ⟨hx, hx'⟩
        refine ⟨by omega, ?_⟩
        rintro (h1 | h1)
        · omega
        · exact hx' h1
      · rintro ⟨hx, hx'⟩
        refine ⟨⟨?_, hx.2⟩, fun h1 => hx' (Or.inr h1)⟩
        by_contra hlt2
        exact hx' (Or.inl ⟨by omega, by omega⟩)

/-- **Cover of a run list.**  Decompose every interval of the list by a range query from
the root `(n, 0)` of the segment tree with `2^n` leaves.  Cost: nodes visited plus one unit
per block written. -/
def coverRuns (n : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) × ℕ
  | [] => ([], 0)
  | p :: rest =>
    ((segQuery p.1 p.2 n 0).1 ++ (coverRuns n rest).1,
     (segQuery p.1 p.2 n 0).2 + (segQuery p.1 p.2 n 0).1.length + (coverRuns n rest).2)

lemma coverRuns_length (n : ℕ) (rl : List (ℕ × ℕ)) :
    (coverRuns n rl).1.length ≤ rl.length * (2 * n + 1) := by
  induction rl with
  | nil => simp [coverRuns]
  | cons p rest ih =>
    have := (segQuery_bound p.1 p.2 n 0).1
    simp only [coverRuns, List.length_append, List.length_cons]
    nlinarith

lemma coverRuns_cost (n : ℕ) (rl : List (ℕ × ℕ)) :
    (coverRuns n rl).2 ≤ rl.length * (4 * n + 1) + (coverRuns n rl).1.length := by
  induction rl with
  | nil => simp [coverRuns]
  | cons p rest ih =>
    have := (segQuery_bound p.1 p.2 n 0).2
    simp only [coverRuns, List.length_append, List.length_cons]
    nlinarith

theorem coverRuns_cover (n M : ℕ) (hM : M ≤ 2 ^ n) (rl : List (ℕ × ℕ)) :
    ∀ lo, IvlsFrom M lo rl →
      IsDyadicCover ((coverRuns n rl).1.map blk).toFinset (runSet rl) := by
  induction rl with
  | nil => intro lo _; simpa [coverRuns, runSet] using IsDyadicCover.empty
  | cons p rest ih =>
    intro lo h
    simp only [IvlsFrom] at h
    have hR := runSet_bounds h.2.2.2
    have hq := segQuery_cover p.1 p.2 n 0
    have e : Ico p.1 p.2 ∩ dyadicBlock n 0 = Ico p.1 p.2 := by
      apply inter_eq_left.2
      intro x hx
      simp only [mem_Ico, dyadicBlock] at hx ⊢
      omega
    rw [e] at hq
    simp only [coverRuns, runSet, List.map_append, List.toFinset_append]
    refine hq.append (ih p.2 h.2.2.2) ?_
    rw [disjoint_left]
    intro x hx hx'
    have := (hR x hx').1
    have := (mem_Ico.1 hx).2
    omega

/-- For a list of index pairs, the union of the blocks. -/
lemma biUnion_blk_of_cover {l : List (ℕ × ℕ)} {T : Finset ℕ}
    (h : IsDyadicCover (l.map blk).toFinset T) : l.toFinset.biUnion blk = T := by
  rw [← h.biUnion_eq]
  ext x
  simp

/-- **Dual-cover compiler for one root action.**  Input: the run list of the support under
the layout.  Output: the block lists `C⁺` (support) and `C⁻` (complement), and the cost. -/
def dualCompile (n M : ℕ) (rl : List (ℕ × ℕ)) : (List (ℕ × ℕ) × List (ℕ × ℕ)) × ℕ :=
  (((coverRuns n rl).1, (coverRuns n (gaps M 0 rl).1).1),
   (coverRuns n rl).2 + (gaps M 0 rl).2 + (coverRuns n (gaps M 0 rl).1).2)

/-- Correctness of `dualCompile`: `C⁺` is a dyadic cover of the support and `C⁻` of its
complement in `[0, M)`. -/
theorem dualCompile_cover (n M : ℕ) (hM : M ≤ 2 ^ n) (rl : List (ℕ × ℕ))
    (hrl : RunsFrom M 0 rl) :
    IsDyadicCover ((dualCompile n M rl).1.1.map blk).toFinset (runSet rl) ∧
    IsDyadicCover ((dualCompile n M rl).1.2.map blk).toFinset (range M \ runSet rl) := by
  refine ⟨coverRuns_cover n M hM rl 0 hrl.ivls, ?_⟩
  have h := coverRuns_cover n M hM (gaps M 0 rl).1 0 (gaps_ivls M rl 0 hrl.ivls)
  rw [gaps_set M rl 0 hrl.ivls, ← Finset.range_eq_Ico] at h
  exact h

/-- Incidences and cost of `dualCompile` for a support with `r` runs: at most
`(2n + 1)(2r + 1)` blocks are stored and the cost is at most `(4n + 2)(2r + 1)` plus the
number of blocks stored. -/
theorem dualCompile_bound (n M : ℕ) (rl : List (ℕ × ℕ)) :
    (dualCompile n M rl).1.1.length + (dualCompile n M rl).1.2.length
        ≤ (2 * n + 1) * (2 * rl.length + 1) ∧
    (dualCompile n M rl).2
        ≤ (4 * n + 2) * (2 * rl.length + 1)
          + ((dualCompile n M rl).1.1.length + (dualCompile n M rl).1.2.length) := by
  have h1 := coverRuns_length n rl
  have h2 := coverRuns_length n (gaps M 0 rl).1
  have h3 := coverRuns_cost n rl
  have h4 := coverRuns_cost n (gaps M 0 rl).1
  have h5 := gaps_length M rl 0
  have h6 := gaps_cost M rl 0
  have h7 : (gaps M 0 rl).1.length * (2 * n + 1) ≤ (rl.length + 1) * (2 * n + 1) :=
    Nat.mul_le_mul_right _ h5
  have h8 : (gaps M 0 rl).1.length * (4 * n + 1) ≤ (rl.length + 1) * (4 * n + 1) :=
    Nat.mul_le_mul_right _ h5
  simp only [dualCompile]
  constructor
  · nlinarith
  · nlinarith

/-- **The compiler for all root actions**: `dualCompile` on each run list in turn; the cost
of the loop is the sum of the costs of its iterations. -/
def compileAll (n M : ℕ) :
    List (List (ℕ × ℕ)) → List (List (ℕ × ℕ) × List (ℕ × ℕ)) × ℕ
  | [] => ([], 0)
  | rl :: rest =>
    ((dualCompile n M rl).1 :: (compileAll n M rest).1,
     (dualCompile n M rl).2 + (compileAll n M rest).2)

/-- Number of stored root-to-block incidences `B`. -/
def incidences : List (List (ℕ × ℕ) × List (ℕ × ℕ)) → ℕ
  | [] => 0
  | c :: rest => c.1.length + c.2.length + incidences rest

lemma compileAll_fst (n M : ℕ) (rls : List (List (ℕ × ℕ))) :
    (compileAll n M rls).1 = rls.map (fun rl => (dualCompile n M rl).1) := by
  induction rls with
  | nil => rfl
  | cons rl rest ih => simp only [compileAll, List.map_cons, ih]

/-- **Compile work and stored incidences** (list form).  For `K = rls.length` run lists
with `R = Σ` lengths, `compileAll` stores `B ≤ (2n + 1)(2R + K)` incidences and costs at
most `(4n + 2)(2R + K) + B`. -/
theorem compileAll_bound (n M : ℕ) (rls : List (List (ℕ × ℕ))) :
    incidences (compileAll n M rls).1
        ≤ (2 * n + 1) * (2 * (rls.map List.length).sum + rls.length) ∧
    (compileAll n M rls).2
        ≤ (4 * n + 2) * (2 * (rls.map List.length).sum + rls.length)
          + incidences (compileAll n M rls).1 := by
  induction rls with
  | nil => simp [compileAll, incidences]
  | cons rl rest ih =>
    obtain ⟨h1, h2⟩ := dualCompile_bound n M rl
    obtain ⟨h3, h4⟩ := ih
    simp only [compileAll, incidences, List.map_cons, List.sum_cons, List.length_cons]
    constructor
    · nlinarith
    · nlinarith

/-- **Charged dual covers: compile work and incidences** (`thm:charged-dual-cover`).
Let `π` be any layout of `M` terminals, `as` the list of the `K` root actions, and `rl a`
the run list of the support of `a` under `π` (the output of the run-merging phase `P_G`).
With `n = ⌈log₂ M⌉`, `h = 1 + n` and `R_run = Σ_a r_a`, the compiler `compileAll`:

* returns for each action dyadic covers of its support and of its complement;
* stores `B ≤ 2 h (2 R_run + K)` incidences;
* costs at most `4 h (2 R_run + K) + B` units, i.e. `O((R_run + K) h + B)`. -/
theorem dualCover_compile {Z A : Type*} [Fintype Z] [DecidableEq Z] {M : ℕ} (π : Z ≃ Fin M)
    (S : A → Finset Z) (as : List A) (rl : A → List (ℕ × ℕ))
    (hrl : ∀ a, RunsFrom M 0 (rl a) ∧ runSet (rl a) = layoutPos π (S a)) :
    let n := Nat.clog 2 M
    let out := compileAll n M (as.map rl)
    let Rrun := (as.map (fun a => runs (layoutPos π (S a)))).sum
    out.1 = as.map (fun a => (dualCompile n M (rl a)).1) ∧
    (∀ a, IsDyadicCover ((dualCompile n M (rl a)).1.1.map blk).toFinset (layoutPos π (S a)) ∧
      IsDyadicCover ((dualCompile n M (rl a)).1.2.map blk).toFinset (layoutPos π (S a)ᶜ)) ∧
    incidences out.1 ≤ 2 * (1 + n) * (2 * Rrun + as.length) ∧
    out.2 ≤ 4 * (1 + n) * (2 * Rrun + as.length) + incidences out.1 := by
  intro n out Rrun
  have hM : M ≤ 2 ^ n := Nat.le_pow_clog (by norm_num) M
  have hR : ((as.map rl).map List.length).sum = Rrun := by
    simp only [Rrun, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    simp only [Function.comp]
    rw [← (hrl a).2, runs_runSet (hrl a).1]
  obtain ⟨h1, h2⟩ := compileAll_bound n M (as.map rl)
  rw [hR, List.length_map] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [out, compileAll_fst, List.map_map]
    rfl
  · intro a
    have := dualCompile_cover n M hM (rl a) (hrl a).1
    rw [(hrl a).2] at this
    rw [layoutPos_compl]
    exact this
  · refine h1.trans (Nat.mul_le_mul_right _ (by omega))
  · refine h2.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)

/-! ## Update work: segment tree with subscribed indexed heaps -/

section Update

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]

/-- Write one node of the tree array. -/
def setNode (v : ℕ → ℕ → α) (k j : ℕ) (x : α) : ℕ → ℕ → α :=
  fun k' j' => if k' = k ∧ j' = j then x else v k' j'

/-- **Leaf-to-root recomputation.**  Write the new value `x` at leaf `p` and recompute the
nodes `(k, p / 2^k)`, `k = 1, …, n`, from their children.  One cost unit per node. -/
def pathUpdate (p : ℕ) (x : α) (v : ℕ → ℕ → α) : ℕ → (ℕ → ℕ → α) × ℕ
  | 0 => (setNode v 0 (p / 2 ^ 0) x, 1)
  | k + 1 =>
    (setNode (pathUpdate p x v k).1 (k + 1) (p / 2 ^ (k + 1))
        ((pathUpdate p x v k).1 k (2 * (p / 2 ^ (k + 1)))
          ⊔ (pathUpdate p x v k).1 k (2 * (p / 2 ^ (k + 1)) + 1)),
      (pathUpdate p x v k).2 + 1)

omit [LinearOrder α] [OrderBot α] in
lemma setNode_same (v : ℕ → ℕ → α) (k j : ℕ) (x : α) : setNode v k j x k j = x := by
  unfold setNode
  exact ite_eq_left ⟨rfl, rfl⟩

omit [LinearOrder α] [OrderBot α] in
lemma setNode_of_ne (v : ℕ → ℕ → α) (k j : ℕ) (x : α) {k' j' : ℕ}
    (h : ¬ (k' = k ∧ j' = j)) : setNode v k j x k' j' = v k' j' := by
  unfold setNode
  exact ite_eq_right h

omit [OrderBot α] in
lemma pathUpdate_cost (p : ℕ) (x : α) (v : ℕ → ℕ → α) (n : ℕ) :
    (pathUpdate p x v n).2 = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pathUpdate, ih]

omit [OrderBot α] in
lemma pathUpdate_above (p : ℕ) (x : α) (v : ℕ → ℕ → α) :
    ∀ n k j, n < k → (pathUpdate p x v n).1 k j = v k j := by
  intro n
  induction n with
  | zero =>
    intro k j h
    have hne : ¬ (k = 0 ∧ j = p / 2 ^ 0) := fun h' => by omega
    simp only [pathUpdate]
    rw [setNode_of_ne _ _ _ _ hne]
  | succ n ih =>
    intro k j h
    have hne : ¬ (k = n + 1 ∧ j = p / 2 ^ (n + 1)) := fun h' => by omega
    simp only [pathUpdate]
    rw [setNode_of_ne _ _ _ _ hne]
    exact ih k j (by omega)

omit [OrderBot α] in
lemma pathUpdate_off (p : ℕ) (x : α) (v : ℕ → ℕ → α) :
    ∀ n k j, j ≠ p / 2 ^ k → (pathUpdate p x v n).1 k j = v k j := by
  intro n
  induction n with
  | zero =>
    intro k j h
    have hne : ¬ (k = 0 ∧ j = p / 2 ^ 0) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    simp only [pathUpdate]
    rw [setNode_of_ne _ _ _ _ hne]
  | succ n ih =>
    intro k j h
    have hne : ¬ (k = n + 1 ∧ j = p / 2 ^ (n + 1)) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    simp only [pathUpdate]
    rw [setNode_of_ne _ _ _ _ hne]
    exact ih k j h

/-- **Correctness of the path recomputation.**  If every node of level at most `n` holds
the maximum of the leaf values `f` over its block, then after `pathUpdate` every such node
holds the maximum of the updated leaf values. -/
theorem pathUpdate_spec (p : ℕ) (x : α) (f : ℕ → α) (v : ℕ → ℕ → α) : ∀ n,
    (∀ k ≤ n, ∀ j, v k j = (dyadicBlock k j).sup f) →
    ∀ k ≤ n, ∀ j,
      (pathUpdate p x v n).1 k j = (dyadicBlock k j).sup (Function.update f p x) := by
  intro n
  induction n with
  | zero =>
    intro hv k hk j
    obtain rfl : k = 0 := by omega
    have hp0 : p / 2 ^ 0 = p := by simp
    by_cases hj : j = p
    · subst hj
      simp only [pathUpdate]
      rw [hp0, setNode_same, dyadicBlock_zero, sup_singleton, Function.update_self]
    · have hne : ¬ (0 = 0 ∧ j = p / 2 ^ 0) := by
        rw [hp0]
        exact fun h => hj h.2
      simp only [pathUpdate]
      rw [setNode_of_ne _ _ _ _ hne, hv 0 le_rfl j, dyadicBlock_zero, sup_singleton,
        sup_singleton, Function.update_of_ne hj]
  | succ n ih =>
    intro hv k hk j
    have ih' := ih (fun k hk j => hv k (by omega) j)
    by_cases hkn : k ≤ n
    · have hne : ¬ (k = n + 1 ∧ j = p / 2 ^ (n + 1)) := fun h' => by omega
      simp only [pathUpdate]
      rw [setNode_of_ne _ _ _ _ hne]
      exact ih' k hkn j
    · obtain rfl : k = n + 1 := by omega
      by_cases hj : j = p / 2 ^ (n + 1)
      · subst hj
        simp only [pathUpdate]
        rw [setNode_same, ih' n le_rfl, ih' n le_rfl, dyadicBlock_succ, sup_union]
      · have hne : ¬ (n + 1 = n + 1 ∧ j = p / 2 ^ (n + 1)) := fun h => hj h.2
        simp only [pathUpdate]
        rw [setNode_of_ne _ _ _ _ hne, pathUpdate_above p x v n (n + 1) j (by omega),
          hv (n + 1) le_rfl j]
        apply Finset.sup_congr rfl
        intro y hy
        by_cases hyp : y = p
        · subst hyp
          exact absurd (index_of_mem_dyadicBlock hy) hj
        · rw [Function.update_of_ne hyp]

/-- **Change detection.**  Compare the `n + 1` path nodes with their previous values and
list those that changed.  One cost unit per comparison. -/
def changedNodes (p : ℕ) (v v' : ℕ → ℕ → α) : ℕ → List (ℕ × ℕ) × ℕ
  | 0 => (if v' 0 (p / 2 ^ 0) = v 0 (p / 2 ^ 0) then [] else [(0, p / 2 ^ 0)], 1)
  | k + 1 =>
    (if v' (k + 1) (p / 2 ^ (k + 1)) = v (k + 1) (p / 2 ^ (k + 1))
      then (changedNodes p v v' k).1
      else (k + 1, p / 2 ^ (k + 1)) :: (changedNodes p v v' k).1,
     (changedNodes p v v' k).2 + 1)

omit [OrderBot α] in
lemma changedNodes_cost (p : ℕ) (v v' : ℕ → ℕ → α) (n : ℕ) :
    (changedNodes p v v' n).2 = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [changedNodes, ih]

omit [OrderBot α] in
lemma changedNodes_length (p : ℕ) (v v' : ℕ → ℕ → α) (n : ℕ) :
    (changedNodes p v v' n).1.length ≤ n + 1 := by
  induction n with
  | zero => simp only [changedNodes]; split_ifs <;> simp
  | succ n ih =>
    simp only [changedNodes]
    split_ifs
    · omega
    · simp only [List.length_cons]
      omega

omit [OrderBot α] in
lemma mem_changedNodes (p : ℕ) (v v' : ℕ → ℕ → α) (n k j : ℕ) :
    (k, j) ∈ (changedNodes p v v' n).1 ↔ k ≤ n ∧ j = p / 2 ^ k ∧ v' k j ≠ v k j := by
  induction n with
  | zero =>
    simp only [changedNodes]
    split_ifs with h
    · simp only [List.not_mem_nil, false_iff]
      rintro ⟨hk, hj, hne⟩
      obtain rfl : k = 0 := by omega
      subst hj
      exact hne h
    · simp only [List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨le_rfl, rfl, h⟩
      · rintro ⟨hk, hj, -⟩
        exact ⟨by omega, by obtain rfl : k = 0 := by omega
                            exact hj⟩
  | succ n ih =>
    simp only [changedNodes]
    split_ifs with h
    · rw [ih]
      constructor
      · rintro ⟨hk, r⟩
        exact ⟨by omega, r⟩
      · rintro ⟨hk, hj, hne⟩
        refine ⟨?_, hj, hne⟩
        by_contra hlt
        obtain rfl : k = n + 1 := by omega
        subst hj
        exact hne h
    · rw [List.mem_cons, ih, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨hk, r⟩)
        · exact ⟨le_rfl, rfl, h⟩
        · exact ⟨by omega, r⟩
      · rintro ⟨hk, hj, hne⟩
        by_cases hk' : k = n + 1
        · subst hk'
          exact Or.inl ⟨rfl, hj⟩
        · exact Or.inr ⟨by omega, hj, hne⟩

/-- State of the charged dual-cover index for one endpoint: the segment-tree array, the
keys stored in each root action's indexed heap (one key per subscribed block), and the keys
of the global indexed heap over root actions (one root summary per action). -/
structure DCState (A α : Type*) where
  tree : ℕ → ℕ → α
  key : A → ℕ × ℕ → α
  root : A → α

/-- **Subscription deliveries.**  For each changed block `d` and each subscribed action
`a`, set the key of `d` in the heap of `a` to the new block value.  Each delivery is one
indexed-heap update in a heap of `bsz a` keys: `⌈log₂ (bsz a)⌉ + 1` units. -/
def deliver (tree' : ℕ → ℕ → α) (bsz : A → ℕ) :
    List ((ℕ × ℕ) × A) → (A → ℕ × ℕ → α) → (A → ℕ × ℕ → α) × ℕ
  | [], key => (key, 0)
  | e :: rest, key =>
    ((deliver tree' bsz rest
        (fun a' d' => if a' = e.2 ∧ d' = e.1 then tree' e.1.1 e.1.2 else key a' d')).1,
     (deliver tree' bsz rest
        (fun a' d' => if a' = e.2 ∧ d' = e.1 then tree' e.1.1 e.1.2 else key a' d')).2
       + (Nat.clog 2 (bsz e.2) + 1))

omit [LinearOrder α] [OrderBot α] in
lemma deliver_key (tree' : ℕ → ℕ → α) (bsz : A → ℕ) :
    ∀ (L : List ((ℕ × ℕ) × A)) (key : A → ℕ × ℕ → α) (a : A) (d : ℕ × ℕ),
      (deliver tree' bsz L key).1 a d = if (d, a) ∈ L then tree' d.1 d.2 else key a d := by
  intro L
  induction L with
  | nil => intro key a d; simp [deliver]
  | cons e rest ih =>
    intro key a d
    obtain ⟨d0, a0⟩ := e
    simp only [deliver, ih, List.mem_cons, Prod.mk.injEq]
    by_cases h1 : (d, a) ∈ rest
    · simp [h1]
    · by_cases h2 : a = a0 ∧ d = d0
      · obtain ⟨rfl, rfl⟩ := h2
        simp
      · have h3 : ¬ (d = d0 ∧ a = a0) := fun h => h2 ⟨h.2, h.1⟩
        simp [h1, h2, h3]

omit [LinearOrder α] [OrderBot α] in
lemma deliver_cost (tree' : ℕ → ℕ → α) (bsz : A → ℕ) :
    ∀ (L : List ((ℕ × ℕ) × A)) (key : A → ℕ × ℕ → α),
      (deliver tree' bsz L key).2 = (L.map (fun e => Nat.clog 2 (bsz e.2) + 1)).sum := by
  intro L
  induction L with
  | nil => intro key; rfl
  | cons e rest ih =>
    intro key
    simp only [deliver, ih, List.map_cons, List.sum_cons]
    omega

/-- **Root refresh.**  For each affected action, read the maximum of its heap and update
its key in the global heap of `K` actions: `⌈log₂ K⌉ + 1` units each. -/
def refresh (cov : A → Finset (ℕ × ℕ)) (key : A → ℕ × ℕ → α) (K : ℕ) :
    List A → (A → α) → (A → α) × ℕ
  | [], root => (root, 0)
  | a :: rest, root =>
    ((refresh cov key K rest (fun a' => if a' = a then (cov a).sup (key a) else root a')).1,
     (refresh cov key K rest (fun a' => if a' = a then (cov a).sup (key a) else root a')).2
       + (Nat.clog 2 K + 1))

lemma refresh_root (cov : A → Finset (ℕ × ℕ)) (key : A → ℕ × ℕ → α) (K : ℕ) :
    ∀ (L : List A) (root : A → α) (a : A),
      (refresh cov key K L root).1 a = if a ∈ L then (cov a).sup (key a) else root a := by
  intro L
  induction L with
  | nil => intro root a; simp [refresh]
  | cons b rest ih =>
    intro root a
    simp only [refresh, ih, List.mem_cons]
    by_cases h1 : a ∈ rest
    · simp [h1]
    · by_cases h2 : a = b
      · subst h2
        simp
      · simp [h1, h2]

lemma refresh_cost (cov : A → Finset (ℕ × ℕ)) (key : A → ℕ × ℕ → α) (K : ℕ) :
    ∀ (L : List A) (root : A → α),
      (refresh cov key K L root).2 = L.length * (Nat.clog 2 K + 1) := by
  intro L
  induction L with
  | nil => intro root; simp [refresh]
  | cons b rest ih =>
    intro root
    simp only [refresh, ih, List.length_cons]
    ring

/-- The changed block subscriptions `𝒩_t` of an update: pairs (changed path node,
subscribed action), read off the reverse-incidence lists `subs`. -/
def changedSubs (n : ℕ) (subs : ℕ × ℕ → List A) (p : ℕ) (x : α) (tree : ℕ → ℕ → α) :
    List ((ℕ × ℕ) × A) :=
  (changedNodes p tree (pathUpdate p x tree n).1 n).1.flatMap
    (fun d => (subs d).map (fun a => (d, a)))

/-- The affected root actions `𝒜_t` of an update. -/
def affected (n : ℕ) (subs : ℕ × ℕ → List A) (p : ℕ) (x : α) (tree : ℕ → ℕ → α) : List A :=
  ((changedSubs n subs p x tree).map Prod.snd).dedup

/-- **One update of the charged dual-cover index** (one endpoint): terminal position `p`
receives the value `x`.  Tree work, then heap work on the changed subscriptions, then the
global heap for the affected actions. -/
def dcUpdate (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A) (bsz : A → ℕ)
    (K p : ℕ) (x : α) (s : DCState A α) : DCState A α × ℕ :=
  (⟨(pathUpdate p x s.tree n).1,
    (deliver (pathUpdate p x s.tree n).1 bsz (changedSubs n subs p x s.tree) s.key).1,
    (refresh cov
      (deliver (pathUpdate p x s.tree n).1 bsz (changedSubs n subs p x s.tree) s.key).1 K
      (affected n subs p x s.tree) s.root).1⟩,
   (pathUpdate p x s.tree n).2
    + (changedNodes p s.tree (pathUpdate p x s.tree n).1 n).2
    + (deliver (pathUpdate p x s.tree n).1 bsz (changedSubs n subs p x s.tree) s.key).2
    + (refresh cov
        (deliver (pathUpdate p x s.tree n).1 bsz (changedSubs n subs p x s.tree) s.key).1 K
        (affected n subs p x s.tree) s.root).2)

/-- Invariant of the index for leaf values `f`: tree nodes hold block maxima, heap keys
mirror the subscribed tree nodes, and root summaries are the heap maxima. -/
structure DCInv (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (f : ℕ → α) (s : DCState A α) : Prop where
  tree : ∀ k ≤ n, ∀ j, s.tree k j = (dyadicBlock k j).sup f
  key : ∀ a, ∀ d ∈ cov a, s.key a d = s.tree d.1 d.2
  root : ∀ a, s.root a = (cov a).sup (s.key a)

omit [DecidableEq A] in
/-- Under the invariant, the root summary of `a` is the maximum of the leaf values over the
positions covered by the blocks of `a`. -/
theorem DCInv.root_eq {n : ℕ} {cov : A → Finset (ℕ × ℕ)} {f : ℕ → α} {s : DCState A α}
    (h : DCInv n cov f s) (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n) (a : A) :
    s.root a = ((cov a).biUnion blk).sup f := by
  rw [h.root a, Finset.sup_biUnion]
  apply Finset.sup_congr rfl
  intro d hd
  rw [h.key a d hd, h.tree d.1 (hlev a d hd) d.2]
  rfl

omit [OrderBot α] [DecidableEq A] in
lemma mem_changedSubs (n : ℕ) (subs : ℕ × ℕ → List A) (p : ℕ) (x : α) (tree : ℕ → ℕ → α)
    (d : ℕ × ℕ) (a : A) :
    (d, a) ∈ changedSubs n subs p x tree
      ↔ d ∈ (changedNodes p tree (pathUpdate p x tree n).1 n).1 ∧ a ∈ subs d := by
  simp only [changedSubs, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨d', hd', a', ha', rfl, rfl⟩
    exact ⟨hd', ha'⟩
  · rintro ⟨hd, ha⟩
    exact ⟨d, hd, a, ha, rfl, rfl⟩

omit [OrderBot α] in
lemma mem_affected (n : ℕ) (subs : ℕ × ℕ → List A) (p : ℕ) (x : α) (tree : ℕ → ℕ → α)
    (a : A) : a ∈ affected n subs p x tree ↔ ∃ d, (d, a) ∈ changedSubs n subs p x tree := by
  simp only [affected, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨⟨d, a'⟩, h, rfl⟩
    exact ⟨d, h⟩
  · rintro ⟨d, h⟩
    exact ⟨(d, a), h, rfl⟩

/-- **Correctness of the update.**  If the reverse-incidence lists contain every
subscription (`a ∈ subs d` whenever `d ∈ cov a`) and the invariant holds for `f`, then after
`dcUpdate` it holds for `f` with position `p` set to `x`.  Only the changed subscriptions
and the affected actions were touched. -/
theorem dcUpdate_inv (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (bsz : A → ℕ) (K p : ℕ) (x : α) (f : ℕ → α) (s : DCState A α)
    (hsub : ∀ a, ∀ d ∈ cov a, a ∈ subs d) (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n)
    (h : DCInv n cov f s) :
    DCInv n cov (Function.update f p x) (dcUpdate n cov subs bsz K p x s).1 := by
  have hkey : ∀ a, ∀ d ∈ cov a,
      (deliver (pathUpdate p x s.tree n).1 bsz (changedSubs n subs p x s.tree) s.key).1 a d
        = (pathUpdate p x s.tree n).1 d.1 d.2 := by
    intro a d hd
    rw [deliver_key]
    split_ifs with hin
    · rfl
    · rw [h.key a d hd]
      by_cases hj : d.2 = p / 2 ^ d.1
      · by_contra hne
        exact hin ((mem_changedSubs n subs p x s.tree d a).2
          ⟨(mem_changedNodes p s.tree _ n d.1 d.2).2 ⟨hlev a d hd, hj, Ne.symm hne⟩,
            hsub a d hd⟩)
      · exact (pathUpdate_off p x s.tree n d.1 d.2 hj).symm
  refine ⟨pathUpdate_spec p x f s.tree n h.tree, hkey, ?_⟩
  intro a
  show (refresh cov _ K (affected n subs p x s.tree) s.root).1 a = _
  rw [refresh_root]
  split_ifs with ha
  · rfl
  · rw [h.root a]
    apply Finset.sup_congr rfl
    intro d _
    show s.key a d = (deliver _ bsz (changedSubs n subs p x s.tree) s.key).1 a d
    rw [deliver_key]
    have hin : (d, a) ∉ changedSubs n subs p x s.tree := fun hin =>
      ha ((mem_affected n subs p x s.tree a).2 ⟨d, hin⟩)
    rw [ite_eq_right hin]

/-- **Update work** (`thm:charged-dual-cover`, `eq:dual-cover-work` for one update and one
endpoint).  With `h = n + 1`, the cost of `dcUpdate` is exactly

`2 h + Σ_{(d, a) ∈ 𝒩_t} (⌈log₂ b_a⌉ + 1) + |𝒜_t| (⌈log₂ K⌉ + 1)`:

`O(h)` tree work, one heap update per changed block subscription, and one global-heap
update per affected root action. -/
theorem dcUpdate_cost (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (bsz : A → ℕ) (K p : ℕ) (x : α) (s : DCState A α) :
    (dcUpdate n cov subs bsz K p x s).2
      = 2 * (n + 1)
        + ((changedSubs n subs p x s.tree).map (fun e => Nat.clog 2 (bsz e.2) + 1)).sum
        + (affected n subs p x s.tree).length * (Nat.clog 2 K + 1) := by
  simp only [dcUpdate, pathUpdate_cost, changedNodes_cost, deliver_cost, refresh_cost]
  ring

omit [OrderBot α] [DecidableEq A] in
/-- The changed subscriptions lie on the leaf-to-root path: at most `h = n + 1` blocks
change, and an action is affected only if it subscribes to a changed block. -/
theorem changedSubs_on_path (n : ℕ) (subs : ℕ × ℕ → List A) (p : ℕ) (x : α)
    (tree : ℕ → ℕ → α) (d : ℕ × ℕ) (a : A) (h : (d, a) ∈ changedSubs n subs p x tree) :
    d.1 ≤ n ∧ d.2 = p / 2 ^ d.1 ∧ (pathUpdate p x tree n).1 d.1 d.2 ≠ tree d.1 d.2 ∧
      a ∈ subs d := by
  obtain ⟨h1, h2⟩ := (mem_changedSubs n subs p x tree d a).1 h
  obtain ⟨h3, h4, h5⟩ := (mem_changedNodes p tree _ n d.1 d.2).1 h1
  exact ⟨h3, h4, h5, h2⟩

/-- **A run of updates.**  The cost of a run is the sum of the costs of its updates. -/
def dcRun (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A) (bsz : A → ℕ)
    (K : ℕ) : List (ℕ × α) → DCState A α → DCState A α × ℕ
  | [], s => (s, 0)
  | u :: us, s =>
    ((dcRun n cov subs bsz K us (dcUpdate n cov subs bsz K u.1 u.2 s).1).1,
     (dcUpdate n cov subs bsz K u.1 u.2 s).2
       + (dcRun n cov subs bsz K us (dcUpdate n cov subs bsz K u.1 u.2 s).1).2)

/-- **Work of `T` updates** (`eq:dual-cover-work`, the `T h` and heap terms).  If every
block has at most `σ` subscribers, every action heap has at most `bmax` keys, then a run of
`T` updates costs at most `T (2h + h σ (⌈log₂ bmax⌉ + ⌈log₂ K⌉ + 2))`.  (Correctness of
each update is `dcUpdate_inv`.) -/
theorem dcRun_bound (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (bsz : A → ℕ) (K σ bmax : ℕ)
    (hσ : ∀ d, (subs d).length ≤ σ) (hb : ∀ a, bsz a ≤ bmax) :
    ∀ (us : List (ℕ × α)) (s : DCState A α),
      (dcRun n cov subs bsz K us s).2
        ≤ us.length * (2 * (n + 1)
            + (n + 1) * σ * (Nat.clog 2 bmax + Nat.clog 2 K + 2)) := by
  intro us
  induction us with
  | nil => intro s; simp [dcRun]
  | cons u us ih =>
    intro s
    have hlen : (changedSubs n subs u.1 u.2 s.tree).length ≤ (n + 1) * σ := by
      unfold changedSubs
      rw [List.length_flatMap]
      calc ((changedNodes u.1 s.tree (pathUpdate u.1 u.2 s.tree n).1 n).1.map
              (fun d => ((subs d).map (fun a => (d, a))).length)).sum
          ≤ ((changedNodes u.1 s.tree (pathUpdate u.1 u.2 s.tree n).1 n).1.map
              (fun _ => σ)).sum := by
            apply List.sum_le_sum
            intro d _
            simp only [List.length_map]
            exact hσ d
        _ = (changedNodes u.1 s.tree (pathUpdate u.1 u.2 s.tree n).1 n).1.length * σ := by
            simp
        _ ≤ (n + 1) * σ := Nat.mul_le_mul_right _ (changedNodes_length _ _ _ _)
    have hheap : ((changedSubs n subs u.1 u.2 s.tree).map
        (fun e => Nat.clog 2 (bsz e.2) + 1)).sum
        ≤ (changedSubs n subs u.1 u.2 s.tree).length * (Nat.clog 2 bmax + 1) := by
      calc _ ≤ ((changedSubs n subs u.1 u.2 s.tree).map
              (fun _ => Nat.clog 2 bmax + 1)).sum := by
            apply List.sum_le_sum
            intro e _
            exact Nat.add_le_add_right (Nat.clog_mono_right 2 (hb e.2)) 1
        _ = _ := by simp
    have haff : (affected n subs u.1 u.2 s.tree).length
        ≤ (changedSubs n subs u.1 u.2 s.tree).length := by
      unfold affected
      exact ((List.dedup_sublist _).length_le).trans (by simp)
    have hstep := dcUpdate_cost n cov subs bsz K u.1 u.2 s
    have hrest := ih (dcUpdate n cov subs bsz K u.1 u.2 s).1
    have h1 : (changedSubs n subs u.1 u.2 s.tree).length * (Nat.clog 2 bmax + 1)
        ≤ (n + 1) * σ * (Nat.clog 2 bmax + 1) := Nat.mul_le_mul_right _ hlen
    have h2 : (affected n subs u.1 u.2 s.tree).length * (Nat.clog 2 K + 1)
        ≤ (n + 1) * σ * (Nat.clog 2 K + 1) := Nat.mul_le_mul_right _ (haff.trans hlen)
    simp only [dcRun, List.length_cons]
    nlinarith

end Update

/-- Number of nodes of the shared segment tree over `2^n` leaves, levels `0, …, n`. -/
theorem segTree_nodes (n : ℕ) : ∑ k ∈ range (n + 1), 2 ^ (n - k) = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h : ∑ k ∈ range (n + 1), 2 ^ (n + 1 - k) = 2 * ∑ k ∈ range (n + 1), 2 ^ (n - k) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      have := mem_range.1 hk
      have e : n + 1 - k = (n - k) + 1 := by omega
      rw [e, pow_succ]
      ring
    have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    rw [h, ih]
    simp only [Nat.sub_self, pow_zero]
    have : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    omega

/-- With `n = ⌈log₂ M⌉` and `M ≥ 1`, the tree has fewer than `4M` nodes: the `O(M)` term of
the space bound. -/
theorem segTree_nodes_lt (M : ℕ) (hM : 1 ≤ M) : 2 ^ (Nat.clog 2 M + 1) - 1 < 4 * M := by
  have h : 2 ^ Nat.clog 2 M < 2 * M := by
    rcases Nat.lt_or_ge 1 M with h1 | h1
    · have hlt : Nat.clog 2 M - 1 < Nat.clog 2 M :=
        Nat.sub_lt (Nat.clog_pos (by norm_num) h1) (by norm_num)
      have h2 : 2 ^ (Nat.clog 2 M - 1) < M := by
        by_contra hge
        have := (Nat.clog_le_iff_le_pow (by norm_num)).2 (not_lt.1 hge)
        omega
      have e : 2 ^ Nat.clog 2 M = 2 * 2 ^ (Nat.clog 2 M - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    · have : M = 1 := by omega
      subst this
      simp
  have e : 2 ^ (Nat.clog 2 M + 1) = 2 * 2 ^ Nat.clog 2 M := by ring
  omega

/-! ## Existence of run lists -/

/-- Every set of positions inside `[lo, M)` is the position set of a run list (found by one
left-to-right scan; this is the specification of the input of `dualCompile`, not a costed
program). -/
theorem exists_runList_from (M : ℕ) : ∀ (d lo : ℕ) (T : Finset ℕ), lo + d = M →
    (∀ x ∈ T, lo ≤ x ∧ x < M) → ∃ rl, RunsFrom M lo rl ∧ runSet rl = T := by
  intro d
  induction d with
  | zero =>
    intro lo T h hT
    refine ⟨[], by simp [RunsFrom], ?_⟩
    simp only [runSet]
    symm
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have := hT x hx
    omega
  | succ d ih =>
    intro lo T h hT
    obtain ⟨rl, hrl, hset⟩ := ih (lo + 1) (T.erase lo) (by omega) (by
      intro x hx
      have h1 := hT x (mem_of_mem_erase hx)
      have h2 := ne_of_mem_erase hx
      omega)
    by_cases hlo : lo ∈ T
    · have hmem : ∀ x, x ∈ T ↔ x = lo ∨ x ∈ runSet rl := by
        intro x
        rw [hset, mem_erase]
        constructor
        · intro hx
          by_cases hxl : x = lo
          · exact Or.inl hxl
          · exact Or.inr ⟨hxl, hx⟩
        · rintro (rfl | ⟨-, hx⟩)
          · exact hlo
          · exact hx
      cases rl with
      | nil =>
        refine ⟨[(lo, lo + 1)], ?_, ?_⟩
        · simp only [RunsFrom, and_true]
          omega
        · ext x
          rw [hmem x]
          simp only [runSet, mem_union, mem_Ico, notMem_empty, or_false]
          omega
      | cons q rest =>
        simp only [RunsFrom] at hrl
        obtain ⟨hq1, hq2, hq3, hq4⟩ := hrl
        by_cases hq : q.1 = lo + 1
        · refine ⟨(lo, q.2) :: rest, ?_, ?_⟩
          · simp only [RunsFrom]
            exact ⟨le_rfl, by omega, hq3, hq4⟩
          · ext x
            rw [hmem x]
            simp only [runSet, mem_union, mem_Ico]
            constructor
            · rintro (h1 | h1)
              · by_cases hx : x = lo
                · exact Or.inl hx
                · exact Or.inr (Or.inl ⟨by omega, h1.2⟩)
              · exact Or.inr (Or.inr h1)
            · rintro (h1 | h1 | h1)
              · exact Or.inl ⟨by omega, by omega⟩
              · exact Or.inl ⟨by omega, h1.2⟩
              · exact Or.inr h1
        · refine ⟨(lo, lo + 1) :: q :: rest, ?_, ?_⟩
          · simp only [RunsFrom]
            exact ⟨le_rfl, by omega, by omega, by omega, hq2, hq3, hq4⟩
          · ext x
            rw [hmem x]
            simp only [runSet, mem_union, mem_Ico]
            constructor
            · rintro (h1 | h1)
              · exact Or.inl (by omega)
              · exact Or.inr h1
            · rintro (h1 | h1)
              · exact Or.inl ⟨by omega, by omega⟩
              · exact Or.inr h1
    · refine ⟨rl, hrl.mono (Nat.le_succ _), ?_⟩
      rw [hset, erase_eq_of_notMem hlo]

/-- Every support under every layout has a run list, so the hypothesis `hrl` of
`dualCover_compile` can always be met. -/
theorem exists_runList {Z : Type*} [DecidableEq Z] {M : ℕ} (π : Z ≃ Fin M) (S : Finset Z) :
    ∃ rl, RunsFrom M 0 rl ∧ runSet rl = layoutPos π S :=
  exists_runList_from M M 0 _ (by omega)
    (fun x hx => ⟨Nat.zero_le _, mem_range.1 (layoutPos_subset π S hx)⟩)

end CostModel
end JointRootCert
