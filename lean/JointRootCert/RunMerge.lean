/-
Joint Root Certification: the graph run-merging phase `P_G` of the dual-cover compiler.

Manuscript: Part III, subsection `app:representation`, proof of charged dual-cover
maintenance.  Results covered:

* `thm:adaptive-oracle-coupling` / `thm:charged-dual-cover` (Exact coupling and charged
  maintenance): the run-merging phase (`eq:dual-run-compilation`), which computes the run
  list of every gate's support over the layout by merging the children's run lists up the
  graph; its composition with the compiler `CostModel.compileAll`; the total compile work
  `O(P_G + (R_run + K) h + B)`; the assembled work statement `eq:dual-cover-work`; and the
  cell counts behind the space claim.

## Cost model

As in `CostModel.lean`: programs return `(result, cost)`, the cost computed by the same
recursion.  Charges: one unit per step of a two-way merge or of a coalescing scan; one unit
per child list entry read; one unit per gate.

## Difference from the manuscript

The manuscript merges the child run lists of a gate with a min-heap keyed by left
endpoints, in `O(A_v log(2 + |E(v)|))`.  Here the `k` child lists are merged by balanced
pairwise merging (`⌈log₂ k⌉` passes of two-way merges, each pass linear in the total
length): the algorithm differs, the bound `(2 A_v + k) ⌈log₂ k⌉` is of the same order.  No
heap is used in this phase.

Supports are sets of layout positions: the layout `π` enters through `pos`, the position
of each terminal gate.
-/
import JointRootCert.CostModel
import JointRootCert.CostEngines

namespace JointRootCert
namespace RunMerge

open Finset CostModel CostEngines _root_.JointRootCert.Representation

/-! ## Sorted interval lists -/

/-- Nonempty intervals inside `[0, M)`, sorted by left endpoint (overlaps allowed). -/
def SortedIvls (M : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  l.Pairwise (fun a b => a.1 ≤ b.1) ∧ ∀ p ∈ l, p.1 < p.2 ∧ p.2 ≤ M

lemma mem_runSet {l : List (ℕ × ℕ)} {x : ℕ} :
    x ∈ runSet l ↔ ∃ p ∈ l, p.1 ≤ x ∧ x < p.2 := by
  induction l with
  | nil => simp [runSet]
  | cons q rest ih =>
    simp only [runSet, mem_union, mem_Ico, ih, List.mem_cons, exists_eq_or_imp]

lemma runSet_congr {l l' : List (ℕ × ℕ)} (h : ∀ p, p ∈ l ↔ p ∈ l') : runSet l = runSet l' := by
  ext x
  rw [mem_runSet, mem_runSet]
  constructor
  · rintro ⟨p, hp, hx⟩; exact ⟨p, (h p).1 hp, hx⟩
  · rintro ⟨p, hp, hx⟩; exact ⟨p, (h p).2 hp, hx⟩

lemma runsFrom_sorted {M : ℕ} : ∀ {rl : List (ℕ × ℕ)} {lo : ℕ}, RunsFrom M lo rl →
    SortedIvls M rl ∧ ∀ p ∈ rl, lo ≤ p.1 := by
  intro rl
  induction rl with
  | nil => intro lo _; exact ⟨⟨List.Pairwise.nil, by simp⟩, by simp⟩
  | cons p rest ih =>
    intro lo h
    simp only [RunsFrom] at h
    obtain ⟨⟨i1, i2⟩, i3⟩ := ih h.2.2.2
    refine ⟨⟨List.pairwise_cons.2 ⟨fun q hq => ?_, i1⟩, ?_⟩, ?_⟩
    · have := i3 q hq; omega
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨h.2.1, h.2.2.1⟩
      · exact i2 q hq
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h.1
      · have := i3 q hq; omega

/-! ## Two-way merge by left endpoint -/

/-- Merge two lists sorted by left endpoint (fuel `f ≥ |a| + |b|`): one unit per step. -/
def mergeS : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) × ℕ
  | 0, a, b => (a ++ b, 0)
  | _ + 1, [], b => (b, 1)
  | _ + 1, p :: a, [] => (p :: a, 1)
  | f + 1, p :: a, q :: b =>
    if p.1 ≤ q.1 then (p :: (mergeS f a (q :: b)).1, (mergeS f a (q :: b)).2 + 1)
    else (q :: (mergeS f (p :: a) b).1, (mergeS f (p :: a) b).2 + 1)

theorem mergeS_spec (M : ℕ) : ∀ (f : ℕ) (a b : List (ℕ × ℕ)), a.length + b.length ≤ f →
    SortedIvls M a → SortedIvls M b →
    SortedIvls M (mergeS f a b).1 ∧ (∀ x, x ∈ (mergeS f a b).1 ↔ x ∈ a ∨ x ∈ b) ∧
    (mergeS f a b).1.length = a.length + b.length ∧
    (mergeS f a b).2 ≤ a.length + b.length + 1 := by
  intro f
  induction f with
  | zero =>
    intro a b hf ha hb
    have ha0 : a = [] := List.length_eq_zero_iff.1 (by omega)
    have hb0 : b = [] := List.length_eq_zero_iff.1 (by omega)
    subst ha0; subst hb0
    exact ⟨ha, by simp [mergeS], by simp [mergeS], by simp [mergeS]⟩
  | succ f ih =>
    intro a b hf ha hb
    cases a with
    | nil => exact ⟨hb, by simp [mergeS], by simp [mergeS], by simp [mergeS]⟩
    | cons p a =>
      cases b with
      | nil => exact ⟨ha, by simp [mergeS], by simp [mergeS], by simp [mergeS]⟩
      | cons q b =>
        have ha' : SortedIvls M a :=
          ⟨(List.pairwise_cons.1 ha.1).2, fun x hx => ha.2 x (List.mem_cons_of_mem _ hx)⟩
        have hb' : SortedIvls M b :=
          ⟨(List.pairwise_cons.1 hb.1).2, fun x hx => hb.2 x (List.mem_cons_of_mem _ hx)⟩
        simp only [List.length_cons] at hf
        by_cases hpq : p.1 ≤ q.1
        · obtain ⟨i1, i2, i3, i4⟩ := ih a (q :: b) (by simp only [List.length_cons]; omega) ha' hb
          have e : mergeS (f + 1) (p :: a) (q :: b)
              = (p :: (mergeS f a (q :: b)).1, (mergeS f a (q :: b)).2 + 1) := by
            rw [mergeS, ite_eq_left hpq]
          rw [e]
          refine ⟨⟨List.pairwise_cons.2 ⟨fun x hx => ?_, i1.1⟩, fun x hx => ?_⟩, fun x => ?_, ?_, ?_⟩
          · rcases (i2 x).1 hx with hx | hx
            · exact (List.pairwise_cons.1 ha.1).1 x hx
            · rcases List.mem_cons.1 hx with rfl | hx
              · exact hpq
              · exact hpq.trans ((List.pairwise_cons.1 hb.1).1 x hx)
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact ha.2 _ List.mem_cons_self
            · exact i1.2 x hx
          · simp only [List.mem_cons, i2]
            tauto
          · simp only [List.length_cons, i3]; omega
          · simp only [List.length_cons] at i4 ⊢; omega
        · obtain ⟨i1, i2, i3, i4⟩ := ih (p :: a) b (by simp only [List.length_cons]; omega) ha hb'
          have e : mergeS (f + 1) (p :: a) (q :: b)
              = (q :: (mergeS f (p :: a) b).1, (mergeS f (p :: a) b).2 + 1) := by
            rw [mergeS, ite_eq_right hpq]
          rw [e]
          have hqp : q.1 ≤ p.1 := by omega
          refine ⟨⟨List.pairwise_cons.2 ⟨fun x hx => ?_, i1.1⟩, fun x hx => ?_⟩, fun x => ?_, ?_, ?_⟩
          · rcases (i2 x).1 hx with hx | hx
            · rcases List.mem_cons.1 hx with rfl | hx
              · exact hqp
              · exact hqp.trans ((List.pairwise_cons.1 ha.1).1 x hx)
            · exact (List.pairwise_cons.1 hb.1).1 x hx
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact hb.2 _ List.mem_cons_self
            · exact i1.2 x hx
          · simp only [List.mem_cons, i2]
            tauto
          · simp only [List.length_cons, i3]; omega
          · simp only [List.length_cons] at i4 ⊢; omega

/-! ## Coalescing overlapping and adjacent intervals -/

/-- One scan over a list sorted by left endpoint, extending the current run `cur` while the
next interval overlaps or touches it: one unit per interval. -/
def coalesceAcc : (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) × ℕ
  | cur, [] => ([cur], 1)
  | cur, p :: rest =>
    if p.1 ≤ cur.2 then
      ((coalesceAcc (cur.1, max cur.2 p.2) rest).1,
       (coalesceAcc (cur.1, max cur.2 p.2) rest).2 + 1)
    else (cur :: (coalesceAcc p rest).1, (coalesceAcc p rest).2 + 1)

theorem coalesceAcc_spec (M : ℕ) : ∀ (rest : List (ℕ × ℕ)) (cur : ℕ × ℕ) (lo : ℕ),
    lo ≤ cur.1 → cur.1 < cur.2 → cur.2 ≤ M → SortedIvls M rest → (∀ p ∈ rest, cur.1 ≤ p.1) →
    RunsFrom M lo (coalesceAcc cur rest).1 ∧
    runSet (coalesceAcc cur rest).1 = Ico cur.1 cur.2 ∪ runSet rest ∧
    (coalesceAcc cur rest).1.length ≤ rest.length + 1 ∧
    (coalesceAcc cur rest).2 = rest.length + 1 := by
  intro rest
  induction rest with
  | nil =>
    intro cur lo h1 h2 h3 _ _
    exact ⟨by simp [coalesceAcc, RunsFrom, h1, h2, h3], by simp [coalesceAcc, runSet],
      by simp [coalesceAcc], by simp [coalesceAcc]⟩
  | cons p rest ih =>
    intro cur lo h1 h2 h3 hs hge
    have hs' : SortedIvls M rest :=
      ⟨(List.pairwise_cons.1 hs.1).2, fun x hx => hs.2 x (List.mem_cons_of_mem _ hx)⟩
    have hp := hs.2 p List.mem_cons_self
    have hcp := hge p List.mem_cons_self
    by_cases hc : p.1 ≤ cur.2
    · have e : coalesceAcc cur (p :: rest)
          = ((coalesceAcc (cur.1, max cur.2 p.2) rest).1,
             (coalesceAcc (cur.1, max cur.2 p.2) rest).2 + 1) := by
        rw [coalesceAcc, ite_eq_left hc]
      rw [e]
      obtain ⟨i1, i2, i3, i4⟩ := ih (cur.1, max cur.2 p.2) lo h1
        (lt_of_lt_of_le h2 (le_max_left _ _)) (max_le h3 hp.2) hs'
        (fun x hx => hge x (List.mem_cons_of_mem _ hx))
      refine ⟨i1, ?_, ?_, ?_⟩
      · rw [i2]
        show Ico cur.1 (max cur.2 p.2) ∪ runSet rest = Ico cur.1 cur.2 ∪ (Ico p.1 p.2 ∪ runSet rest)
        rw [← union_assoc]
        congr 1
        ext x
        simp only [mem_union, mem_Ico]
        omega
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
    · have e : coalesceAcc cur (p :: rest)
          = (cur :: (coalesceAcc p rest).1, (coalesceAcc p rest).2 + 1) := by
        rw [coalesceAcc, ite_eq_right hc]
      rw [e]
      obtain ⟨i1, i2, i3, i4⟩ := ih p (cur.2 + 1) (by omega) hp.1 hp.2 hs'
        (List.pairwise_cons.1 hs.1).1
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [RunsFrom]
        exact ⟨h1, h2, h3, i1⟩
      · show Ico cur.1 cur.2 ∪ runSet (coalesceAcc p rest).1 = _
        rw [i2]
        rfl
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

/-- Coalesce a sorted interval list into a run list. -/
def coalesce : List (ℕ × ℕ) → List (ℕ × ℕ) × ℕ
  | [] => ([], 0)
  | p :: rest => coalesceAcc p rest

theorem coalesce_spec (M : ℕ) (l : List (ℕ × ℕ)) (h : SortedIvls M l) :
    RunsFrom M 0 (coalesce l).1 ∧ runSet (coalesce l).1 = runSet l ∧
    (coalesce l).1.length ≤ l.length ∧ (coalesce l).2 = l.length := by
  cases l with
  | nil => exact ⟨by simp [coalesce, RunsFrom], rfl, le_rfl, rfl⟩
  | cons p rest =>
    have hp := h.2 p List.mem_cons_self
    exact coalesceAcc_spec M rest p 0 (Nat.zero_le _) hp.1 hp.2
      ⟨(List.pairwise_cons.1 h.1).2, fun x hx => h.2 x (List.mem_cons_of_mem _ hx)⟩
      (List.pairwise_cons.1 h.1).1

/-- **Union of two run lists**: merge by left endpoint, then coalesce. -/
def merge2 (a b : List (ℕ × ℕ)) : List (ℕ × ℕ) × ℕ :=
  ((coalesce (mergeS (a.length + b.length) a b).1).1,
   (mergeS (a.length + b.length) a b).2 + (coalesce (mergeS (a.length + b.length) a b).1).2)

/-- `merge2` returns the run list of the union, with at most `|a| + |b|` runs, in at most
`2 (|a| + |b|) + 1` steps. -/
theorem merge2_spec (M : ℕ) (a b : List (ℕ × ℕ)) (ha : RunsFrom M 0 a) (hb : RunsFrom M 0 b) :
    RunsFrom M 0 (merge2 a b).1 ∧ runSet (merge2 a b).1 = runSet a ∪ runSet b ∧
    (merge2 a b).1.length ≤ a.length + b.length ∧
    (merge2 a b).2 ≤ 2 * (a.length + b.length) + 1 := by
  obtain ⟨m1, m2, m3, m4⟩ := mergeS_spec M (a.length + b.length) a b le_rfl
    (runsFrom_sorted ha).1 (runsFrom_sorted hb).1
  obtain ⟨c1, c2, c3, c4⟩ := coalesce_spec M _ m1
  refine ⟨c1, ?_, by show (coalesce _).1.length ≤ _; omega, by show _ + _ ≤ _; omega⟩
  show runSet (coalesce _).1 = _
  rw [c2]
  ext x
  rw [mem_union, mem_runSet, mem_runSet, mem_runSet]
  constructor
  · rintro ⟨p, hp, hx⟩
    rcases (m2 p).1 hp with h | h
    · exact Or.inl ⟨p, h, hx⟩
    · exact Or.inr ⟨p, h, hx⟩
  · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
    · exact ⟨p, (m2 p).2 (Or.inl hp), hx⟩
    · exact ⟨p, (m2 p).2 (Or.inr hp), hx⟩

/-! ## Balanced `k`-way merge -/

/-- Union of the position sets of a list of run lists. -/
def unionAll (ls : List (List (ℕ × ℕ))) : Finset ℕ := (ls.map runSet).foldr (· ∪ ·) ∅

/-- Total number of runs of a list of run lists. -/
def sumLen (ls : List (List (ℕ × ℕ))) : ℕ := (ls.map List.length).sum

/-- One pass: merge the lists two by two. -/
def mergePairs : List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)) × ℕ
  | [] => ([], 0)
  | [a] => ([a], 0)
  | a :: b :: rest =>
    ((merge2 a b).1 :: (mergePairs rest).1, (merge2 a b).2 + (mergePairs rest).2)

/-- Specification of one pass. -/
def PairsSpec (M : ℕ) (ls : List (List (ℕ × ℕ))) : Prop :=
  (∀ l ∈ ls, RunsFrom M 0 l) →
    (∀ l ∈ (mergePairs ls).1, RunsFrom M 0 l) ∧ unionAll (mergePairs ls).1 = unionAll ls ∧
    sumLen (mergePairs ls).1 ≤ sumLen ls ∧ 2 * (mergePairs ls).1.length ≤ ls.length + 1 ∧
    (mergePairs ls).2 ≤ 2 * sumLen ls + ls.length

theorem mergePairs_spec (M : ℕ) : ∀ ls : List (List (ℕ × ℕ)),
    PairsSpec M ls ∧ ∀ a, PairsSpec M (a :: ls) := by
  intro ls
  induction ls with
  | nil =>
    refine ⟨fun _ => ⟨by simp [mergePairs], rfl, le_rfl, by simp [mergePairs],
      by simp [mergePairs]⟩, fun a h => ?_⟩
    exact ⟨h, rfl, le_rfl, by simp [mergePairs], by simp [mergePairs]⟩
  | cons b rest ih =>
    refine ⟨ih.2 b, fun a h => ?_⟩
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih.1 (fun l hl =>
      h l (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)))
    obtain ⟨m1, m2, m3, m4⟩ := merge2_spec M a b (h a List.mem_cons_self)
      (h b (List.mem_cons_of_mem _ List.mem_cons_self))
    have e : mergePairs (a :: b :: rest)
        = ((merge2 a b).1 :: (mergePairs rest).1, (merge2 a b).2 + (mergePairs rest).2) := rfl
    rw [e]
    refine ⟨fun l hl => ?_, ?_, ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hl with rfl | hl
      · exact m1
      · exact i1 l hl
    · show runSet (merge2 a b).1 ∪ unionAll (mergePairs rest).1
        = runSet a ∪ (runSet b ∪ unionAll rest)
      rw [m2, i2, union_assoc]
    · show (merge2 a b).1.length + sumLen (mergePairs rest).1
        ≤ a.length + (b.length + sumLen rest)
      omega
    · simp only [List.length_cons]; omega
    · show (merge2 a b).2 + (mergePairs rest).2
        ≤ 2 * (a.length + (b.length + sumLen rest)) + (rest.length + 1 + 1)
      omega

/-- **Balanced merge** of `k`-many run lists with `d` passes (`d ≥ ⌈log₂ k⌉`). -/
def mergeAll : ℕ → List (List (ℕ × ℕ)) → List (ℕ × ℕ) × ℕ
  | _, [] => ([], 0)
  | _, [a] => (a, 0)
  | 0, _ :: _ :: _ => ([], 0)
  | d + 1, a :: b :: rest =>
    ((mergeAll d (mergePairs (a :: b :: rest)).1).1,
     (mergePairs (a :: b :: rest)).2 + (mergeAll d (mergePairs (a :: b :: rest)).1).2)

/-- **Correctness and cost of the balanced merge.**  For `k ≤ 2^d` run lists with `A` runs
in total, `mergeAll d` returns the run list of the union of their position sets, with at
most `A` runs, in at most `d (2A + k)` steps. -/
theorem mergeAll_spec (M : ℕ) : ∀ (d : ℕ) (ls : List (List (ℕ × ℕ))), ls.length ≤ 2 ^ d →
    (∀ l ∈ ls, RunsFrom M 0 l) →
    RunsFrom M 0 (mergeAll d ls).1 ∧ runSet (mergeAll d ls).1 = unionAll ls ∧
    (mergeAll d ls).1.length ≤ sumLen ls ∧
    (mergeAll d ls).2 ≤ d * (2 * sumLen ls + ls.length) := by
  intro d
  induction d with
  | zero =>
    intro ls hlen h
    match ls, hlen, h with
    | [], _, _ => exact ⟨by simp [mergeAll, RunsFrom], rfl, Nat.zero_le _, by simp [mergeAll]⟩
    | [a], _, h =>
      exact ⟨h a List.mem_cons_self, by simp [mergeAll, unionAll], by simp [mergeAll, sumLen],
        by simp [mergeAll]⟩
    | _ :: _ :: _, hlen, _ => simp at hlen
  | succ d ih =>
    intro ls hlen h
    match ls, hlen, h with
    | [], _, _ => exact ⟨by simp [mergeAll, RunsFrom], rfl, Nat.zero_le _, by simp [mergeAll]⟩
    | [a], _, h =>
      exact ⟨h a List.mem_cons_self, by simp [mergeAll, unionAll], by simp [mergeAll, sumLen],
        by simp [mergeAll]⟩
    | a :: b :: rest, hlen, h =>
      obtain ⟨p1, p2, p3, p4, p5⟩ := (mergePairs_spec M (a :: b :: rest)).1 h
      have hl : (mergePairs (a :: b :: rest)).1.length ≤ 2 ^ d := by
        have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
        omega
      obtain ⟨i1, i2, i3, i4⟩ := ih _ hl p1
      have e : mergeAll (d + 1) (a :: b :: rest)
          = ((mergeAll d (mergePairs (a :: b :: rest)).1).1,
             (mergePairs (a :: b :: rest)).2
               + (mergeAll d (mergePairs (a :: b :: rest)).1).2) := rfl
      rw [e]
      refine ⟨i1, i2.trans p2, i3.trans p3, ?_⟩
      have hlen2 : (mergePairs (a :: b :: rest)).1.length ≤ (a :: b :: rest).length := by
        simp only [List.length_cons] at p4 ⊢; omega
      have hmono : d * (2 * sumLen (mergePairs (a :: b :: rest)).1
            + (mergePairs (a :: b :: rest)).1.length)
          ≤ d * (2 * sumLen (a :: b :: rest) + (a :: b :: rest).length) :=
        Nat.mul_le_mul_left _ (by omega)
      show (mergePairs (a :: b :: rest)).2 + (mergeAll d (mergePairs (a :: b :: rest)).1).2 ≤ _
      rw [Nat.succ_mul]
      omega

/-! ## The run-merging phase on a DAG -/

/-- Run list of one gate: a terminal at layout position `pos g` has the single run
`[pos g, pos g + 1)` (1 unit); an internal gate reads its child list (1 unit per child,
1 for the gate) and merges the children's run lists. -/
def gateRuns (G : Dag) (pos : ℕ → ℕ) (rl : ℕ → List (ℕ × ℕ)) (g : ℕ) : List (ℕ × ℕ) × ℕ :=
  if G.children g = [] then ([(pos g, pos g + 1)], 1)
  else
    ((mergeAll (Nat.clog 2 (G.children g).length) ((G.children g).map rl)).1,
     (mergeAll (Nat.clog 2 (G.children g).length) ((G.children g).map rl)).2
       + (G.children g).length + 1)

/-- **The run-merging phase `P_G`**: process the gates in the given (topological) order,
storing the run list of each. -/
def runPhase (G : Dag) (pos : ℕ → ℕ) :
    List ℕ → (ℕ → List (ℕ × ℕ)) → (ℕ → List (ℕ × ℕ)) × ℕ
  | [], rl => (rl, 0)
  | g :: rest, rl =>
    ((runPhase G pos rest (Function.update rl g (gateRuns G pos rl g).1)).1,
     (gateRuns G pos rl g).2
       + (runPhase G pos rest (Function.update rl g (gateRuns G pos rl g).1)).2)

/-- Work charged to gate `v` in `eq:dual-run-compilation`: `1` for a terminal; for an
internal gate `1 + |E(v)| + ⌈log₂ |E(v)|⌉ (2 A_v + |E(v)|)` with `A_v = Σ_{j ∈ E(v)} r_j`
the total run count of the children's supports. -/
def gateCost (G : Dag) (supp : ℕ → Finset ℕ) (g : ℕ) : ℕ :=
  if G.children g = [] then 1
  else 1 + (G.children g).length
    + Nat.clog 2 (G.children g).length
      * (2 * ((G.children g).map (fun c => runs (supp c))).sum + (G.children g).length)

lemma unionAll_map (rl : ℕ → List (ℕ × ℕ)) (cs : List ℕ) :
    unionAll (cs.map rl) = cs.toFinset.biUnion (fun c => runSet (rl c)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.toFinset_cons, biUnion_insert, ← ih]
    rfl

/-- One gate: if the run lists of the children are correct, so is the computed run list,
and its cost is at most `gateCost`. -/
theorem gateRuns_spec (G : Dag) (pos : ℕ → ℕ) (M : ℕ) (supp : ℕ → Finset ℕ)
    (rl : ℕ → List (ℕ × ℕ)) (g : ℕ)
    (hleaf : G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp)
    (hch : ∀ c ∈ G.children g, RunsFrom M 0 (rl c) ∧ runSet (rl c) = supp c) :
    RunsFrom M 0 (gateRuns G pos rl g).1 ∧ runSet (gateRuns G pos rl g).1 = supp g ∧
    (gateRuns G pos rl g).2 ≤ gateCost G supp g := by
  unfold gateRuns gateCost
  by_cases hl : G.children g = []
  · rw [ite_eq_left hl, ite_eq_left hl]
    obtain ⟨h1, h2⟩ := hleaf hl
    refine ⟨⟨Nat.zero_le _, Nat.lt_succ_self _, h2, trivial⟩, ?_, le_rfl⟩
    rw [h1]
    ext x
    simp only [runSet, mem_union, mem_Ico, mem_singleton, notMem_empty, or_false]
    omega
  · rw [ite_eq_right hl, ite_eq_right hl]
    have hlen : ((G.children g).map rl).length ≤ 2 ^ Nat.clog 2 (G.children g).length := by
      rw [List.length_map]
      exact Nat.le_pow_clog (by norm_num) _
    obtain ⟨m1, m2, _, m4⟩ := mergeAll_spec M _ ((G.children g).map rl) hlen (fun l hl' => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl'
      exact (hch c hc).1)
    have hsum : sumLen ((G.children g).map rl)
        = ((G.children g).map (fun c => runs (supp c))).sum := by
      unfold sumLen
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro c hc
      show (rl c).length = runs (supp c)
      rw [← (hch c hc).2, runs_runSet (hch c hc).1]
    refine ⟨m1, ?_, ?_⟩
    · rw [m2, unionAll_map, hgate hl]
      exact biUnion_congr rfl (fun c hc => (hch c (List.mem_toFinset.1 hc)).2)
    · rw [hsum, List.length_map] at m4
      omega

/-- **Correctness and cost of the run-merging phase** (`eq:dual-run-compilation`).  Let
`order` list gates by nondecreasing level and be closed under children, and let `supp`
satisfy the support equations on `order`: a terminal at position `pos g < M` has support
`{pos g}`, an internal gate has the union of its children's supports.  Then after
`runPhase` every gate of `order` stores the run list of its support, and the cost is at
most `Σ_{v ∈ order} gateCost v`, that is

`|V| + |E| + Σ_{v ∉ Z} ⌈log₂ |E(v)|⌉ (2 A_v + |E(v)|)`. -/
theorem runPhase_spec (G : Dag) (pos : ℕ → ℕ) (M : ℕ) (supp : ℕ → Finset ℕ)
    (hlev : ∀ p c, c ∈ G.children p → G.level c < G.level p) (order : List ℕ)
    (hsorted : order.Pairwise (fun a b => G.level a ≤ G.level b))
    (hclosed : ∀ g ∈ order, ∀ c ∈ G.children g, c ∈ order)
    (hleaf : ∀ g ∈ order, G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order, G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp)
    (rl0 : ℕ → List (ℕ × ℕ)) :
    (∀ g ∈ order, RunsFrom M 0 ((runPhase G pos order rl0).1 g) ∧
      runSet ((runPhase G pos order rl0).1 g) = supp g) ∧
    (runPhase G pos order rl0).2 ≤ (order.map (gateCost G supp)).sum := by
  have loop : ∀ (rest : List ℕ) (rl : ℕ → List (ℕ × ℕ)), (∀ g ∈ rest, g ∈ order) →
      rest.Pairwise (fun a b => G.level a ≤ G.level b) →
      (∀ h ∈ order, h ∉ rest → RunsFrom M 0 (rl h) ∧ runSet (rl h) = supp h) →
      (∀ h ∈ order, RunsFrom M 0 ((runPhase G pos rest rl).1 h) ∧
        runSet ((runPhase G pos rest rl).1 h) = supp h) ∧
      (runPhase G pos rest rl).2 ≤ (rest.map (gateCost G supp)).sum := by
    intro rest
    induction rest with
    | nil => intro rl _ _ h; exact ⟨fun g hg => h g hg List.not_mem_nil, le_rfl⟩
    | cons g rest ih =>
      intro rl hmem hsort hgood
      have hg : g ∈ order := hmem g List.mem_cons_self
      have hsort' := List.pairwise_cons.1 hsort
      have hch : ∀ c ∈ G.children g, RunsFrom M 0 (rl c) ∧ runSet (rl c) = supp c := by
        intro c hc
        apply hgood c (hclosed g hg c hc)
        intro hm
        have hlt := hlev g c hc
        rcases List.mem_cons.1 hm with e | hm
        · rw [e] at hlt; exact lt_irrefl _ hlt
        · have := hsort'.1 c hm; omega
      obtain ⟨s1, s2, s3⟩ := gateRuns_spec G pos M supp rl g (hleaf g hg) (hgate g hg) hch
      obtain ⟨i1, i2⟩ := ih (Function.update rl g (gateRuns G pos rl g).1)
        (fun g' hg' => hmem g' (List.mem_cons_of_mem _ hg')) hsort'.2 (by
          intro h hh hnot
          by_cases e : h = g
          · rw [e, Function.update_self]
            exact ⟨s1, s2⟩
          · rw [Function.update_of_ne e]
            exact hgood h hh (fun hm => by
              rcases List.mem_cons.1 hm with hm | hm
              · exact e hm
              · exact hnot hm))
      refine ⟨i1, ?_⟩
      show (gateRuns G pos rl g).2 + (runPhase G pos rest _).2 ≤ _
      rw [List.map_cons, List.sum_cons]
      omega
  exact loop order rl0 (fun _ h => h) hsorted (fun h hh hn => absurd hh hn)

/-! ## The full compiler and `thm:charged-dual-cover` -/

/-- **Charged dual covers: the full compiler** (`thm:charged-dual-cover`, compile part).
On a circuit `G` whose gates `order` are listed by nondecreasing level, with terminal
layout positions `pos` in `[0, M)` and supports `supp`, and root actions `as` (gates of
`order`): run the run-merging phase, then `CostModel.compileAll` on the run lists of the
root actions.  With `n = ⌈log₂ M⌉`, `h = 1 + n`, `K = |as|`, `R_run = Σ_a r_a`:

* each root action gets dyadic covers of its support and of its complement in `[0, M)`;
* the number of stored incidences is `B ≤ 2 h (2 R_run + K)`;
* the total compile cost is at most `P_G + 4 h (2 R_run + K) + B`, with
  `P_G = Σ_{v ∈ order} gateCost v` (`eq:dual-run-compilation`);
* the run lists stored during compilation have `Σ_{v ∈ order} r_v` entries in total (the
  temporary term of the peak space bound). -/
theorem charged_dual_cover_compile (G : Dag) (pos : ℕ → ℕ) (M : ℕ) (supp : ℕ → Finset ℕ)
    (hlev : ∀ p c, c ∈ G.children p → G.level c < G.level p) (order : List ℕ)
    (hsorted : order.Pairwise (fun a b => G.level a ≤ G.level b))
    (hclosed : ∀ g ∈ order, ∀ c ∈ G.children g, c ∈ order)
    (hleaf : ∀ g ∈ order, G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order, G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp)
    (as : List ℕ) (has : ∀ a ∈ as, a ∈ order) :
    let n := Nat.clog 2 M
    let ph := runPhase G pos order (fun _ => [])
    let out := compileAll n M (as.map ph.1)
    let Rrun := (as.map (fun a => runs (supp a))).sum
    (∀ a ∈ as,
      IsDyadicCover ((dualCompile n M (ph.1 a)).1.1.map blk).toFinset (supp a) ∧
      IsDyadicCover ((dualCompile n M (ph.1 a)).1.2.map blk).toFinset (range M \ supp a)) ∧
    out.1 = as.map (fun a => (dualCompile n M (ph.1 a)).1) ∧
    incidences out.1 ≤ 2 * (1 + n) * (2 * Rrun + as.length) ∧
    ph.2 + out.2
      ≤ (order.map (gateCost G supp)).sum + 4 * (1 + n) * (2 * Rrun + as.length)
        + incidences out.1 ∧
    (order.map (fun g => (ph.1 g).length)).sum = (order.map (fun g => runs (supp g))).sum := by
  intro n ph out Rrun
  have hM : M ≤ 2 ^ n := Nat.le_pow_clog (by norm_num) M
  obtain ⟨p1, p2⟩ := runPhase_spec G pos M supp hlev order hsorted hclosed hleaf hgate
    (fun _ => [])
  have hR : ((as.map ph.1).map List.length).sum = Rrun := by
    simp only [Rrun, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    show (ph.1 a).length = runs (supp a)
    rw [← (p1 a (has a ha)).2, runs_runSet (p1 a (has a ha)).1]
  obtain ⟨h1, h2⟩ := compileAll_bound n M (as.map ph.1)
  rw [hR, List.length_map] at h1 h2
  have hB : incidences out.1 ≤ 2 * (1 + n) * (2 * Rrun + as.length) :=
    h1.trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨fun a ha => ?_, ?_, hB, ?_, ?_⟩
  · have := dualCompile_cover n M hM (ph.1 a) (p1 a (has a ha)).1
    rw [(p1 a (has a ha)).2] at this
    exact this
  · simp only [out, compileAll_fst, List.map_map]
    rfl
  · have h3 : out.2 ≤ 4 * (1 + n) * (2 * Rrun + as.length) + incidences out.1 :=
      h2.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)
    have p2' : ph.2 ≤ (order.map (gateCost G supp)).sum := p2
    omega
  · congr 1
    apply List.map_congr_left
    intro g hg
    show (ph.1 g).length = runs (supp g)
    rw [← (p1 g hg).2, runs_runSet (p1 g hg).1]

/-- Cells of the retained index: the circuit arrays (`V` vertex records, `E` incidences),
the shared segment tree over `2^⌈log₂ M⌉` leaves, one heap key and one reverse-subscription
entry per stored incidence, and one global-heap key per root action. -/
def retainedCells (V E M B K : ℕ) : ℕ := V + E + (2 ^ (Nat.clog 2 M + 1) - 1) + 2 * B + K

/-- **Space of the retained index**: `O(|V| + |E| + M + B + K)` cells.  This counts the
cells of the data structures named in `retainedCells`; it is not derived from a memory
model of the programs. -/
theorem retainedCells_le (V E M B K : ℕ) (hM : 1 ≤ M) :
    retainedCells V E M B K ≤ V + E + 4 * M + 2 * B + K := by
  have := segTree_nodes_lt M hM
  unfold retainedCells
  omega

section Work

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]

/-- **A minimizer/maximizer query**: one read of the root of the global indexed heap, whose
keys are the root summaries (1 unit; the heap is the charged primitive of
`CostModel.lean`). -/
def dcQuery (acts : Finset A) (s : DCState A α) : α × ℕ := (acts.sup s.root, 1)

omit [DecidableEq A] in
/-- Under the index invariant a query returns the maximum over the actions of the maximum
terminal value over the positions covered by the action's blocks. -/
theorem dcQuery_spec (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (f : ℕ → α) (s : DCState A α)
    (acts : Finset A) (h : DCInv n cov f s) (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n) :
    (dcQuery acts s).1 = acts.sup (fun a => ((cov a).biUnion blk).sup f) ∧
    (dcQuery acts s).2 = 1 :=
  ⟨Finset.sup_congr rfl (fun a _ => h.root_eq hlev a), rfl⟩

/-- **`eq:dual-cover-work`, assembled.**  Total work of the charged dual-cover index for one
endpoint: compile work `Wc` (bounded by `charged_dual_cover_compile`), initialisation work
`Pinit` of the segment tree and the heaps (a parameter: the initial state is assumed to
satisfy the invariant), `T` updates executed by `CostModel.dcRun`, and `Q` queries of one
unit each.  If every block has at most `σ` subscribers and every action heap at most `bmax`
keys, then with `h = n + 1`

`W ≤ Wc + Pinit + T (2h + h σ (⌈log₂ bmax⌉ + ⌈log₂ K⌉ + 2)) + Q`.

The per-update heap terms `Σ_{𝒩_t} log(2 + b_a) + |𝒜_t| log(2 + K)` are bounded here by
`h σ (…)`; the exact per-update count is `CostModel.dcUpdate_cost`. -/
theorem dual_cover_work (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (bsz : A → ℕ) (K σ bmax : ℕ) (hσ : ∀ d, (subs d).length ≤ σ) (hb : ∀ a, bsz a ≤ bmax)
    (us : List (ℕ × α)) (s : DCState A α) (Wc Pinit Q : ℕ) :
    Wc + Pinit + (dcRun n cov subs bsz K us s).2 + Q * 1
      ≤ Wc + Pinit
        + us.length * (2 * (n + 1) + (n + 1) * σ * (Nat.clog 2 bmax + Nat.clog 2 K + 2))
        + Q := by
  have := dcRun_bound n cov subs bsz K σ bmax hσ hb us s
  omega

end Work

end RunMerge
end JointRootCert
