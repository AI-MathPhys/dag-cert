/-
Joint Root Certification: the lower half of `thm:coded-main` / `thm:coded-covers`
("every single-ordering dyadic root-support compiler explicitly materializing root-to-block
incidences incurs `Ω(r³)` initialization work prior to the first rollout") as a statement
about COMPILER WORK, with possibly overlapping covers.

The manuscript does not define "compiler", nor what materializing an incidence costs.  The
model fixed here is the following.

* A block is referred to by its identifier `(level, index) : BlockId`; the positions it
  covers are `dyadicBlock level index`.  The same block identifier may be used by any number
  of root actions (shared block gates are free to deduplicate).
* A compiler run is a finite trace of unit-cost instructions `Instr K Op`:
  `emit a b` appends the incidence `(a, b)` to the output list of the key `a`, and
  `other o` is any other unit-cost operation (caching, construction of deduplicated tree
  gates, heap operations, retirement, ...), with `Op` an arbitrary type.
* The output list of a key is DEFINED as what the trace emitted for it (`emitted`), and the
  work is the length of the trace (`work`).  Hence one materialized incidence costs one unit
  as a property of the program, not of an output handed over for free.
* `exec` runs an arbitrary step function (a program with arbitrary internal state) for at
  most `n` steps; its trace has length at most `n`.
* The contract (`IsListCover`) on the output list of a root support `S` under the terminal
  ordering `π`: every listed block is contained in the set of positions of `S`, and every
  position of `S` lies in some listed block.  Blocks may overlap and may be repeated.
* "One list per distinct root support": keys are the root supports themselves
  (`K = Finset (GridTerminal k)`), so two root actions with equal supports would share one
  list.  For the parity grid the `d + 1` supports are pairwise distinct
  (`ParityGrid.pgSupp_injective`), so nothing is shared.

Main results.

* `runs_le_card_of_overlapCover`, `runs_le_length_of_listCover`: blocks are at least runs,
  without disjointness and for lists with repetitions.
* `parityGrid_overlapCover_lower`, `parityGrid_listCover_lower`: the every-layout incidence
  bound `r³ ≤ 2 Σ_p |C_p|` for overlapping covers / lists.
* `compiler_work_lower`: for `r = 2^k`, `k ≥ 1`, every terminal ordering `π` of the
  `r² + 1` terminals of `ParityGrid.pgDag k` and every trace whose emitted lists, indexed by
  the distinct root supports `pgSupp k a`, meet the contract: `r³ ≤ 2 * work`.
* `compiler_work_lower_keyed` (any injective naming of the root actions, e.g. by action
  index), `compiler_total_work_lower` (work spent after the compile phase cannot reduce it),
  `compiler_program_lower` (programs given by a step function), `no_compiler_below`.
-/
import JointRootCert.ParityGrid

namespace JointRootCert
namespace LiteralK5

open Finset
open _root_.JointRootCert.Representation
open _root_.JointRootCert.ParityGrid

/-! ## Covers without disjointness -/

/-- `C` is a possibly overlapping dyadic cover of the position set `T`: every member is a
dyadic block contained in `T`, and every position of `T` lies in some member.  No
disjointness is required. -/
structure IsOverlapCover (C : Finset (Finset ℕ)) (T : Finset ℕ) : Prop where
  isBlock : ∀ B ∈ C, ∃ l j, B = dyadicBlock l j
  subset : ∀ B ∈ C, B ⊆ T
  covers : ∀ x ∈ T, ∃ B ∈ C, x ∈ B

/-- The disjoint covers of `Representation.lean` are a special case. -/
lemma IsOverlapCover.of_dyadicCover {C : Finset (Finset ℕ)} {T : Finset ℕ}
    (h : IsDyadicCover C T) : IsOverlapCover C T where
  isBlock := h.isBlock
  subset := fun _ hB => h.subset hB
  covers := by
    intro x hx
    rw [← h.biUnion_eq, mem_biUnion] at hx
    exact hx

/-- The cover condition is exactly "all members are dyadic blocks and their union is `T`". -/
lemma isOverlapCover_iff {C : Finset (Finset ℕ)} {T : Finset ℕ} :
    IsOverlapCover C T ↔ (∀ B ∈ C, ∃ l j, B = dyadicBlock l j) ∧ C.biUnion id = T := by
  constructor
  · intro h
    refine ⟨h.isBlock, ?_⟩
    ext x
    rw [mem_biUnion]
    constructor
    · rintro ⟨B, hB, hx⟩
      exact h.subset B hB hx
    · exact h.covers x
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_, ?_⟩
    · intro B hB
      rw [← h2]
      exact subset_biUnion_of_mem id hB
    · intro x hx
      rw [← h2, mem_biUnion] at hx
      exact hx

/-- **Blocks are at least runs, without disjointness.**  Each right end `x` of a run of `T`
lies in some block; a block contained in `T` that contains `x` cannot contain a larger
position (otherwise it would contain `x + 1 ∈ T`), so `x` is the maximum of that block.
Hence the run ends inject into the blocks. -/
theorem runs_le_card_of_overlapCover {C : Finset (Finset ℕ)} {T : Finset ℕ}
    (h : IsOverlapCover C T) : runs T ≤ C.card := by
  have hsub : runEnds T ⊆ C.image (fun B => B.sup id) := by
    intro x hx
    obtain ⟨hxT, hx1⟩ := mem_filter.1 hx
    obtain ⟨B, hB, hxB⟩ := h.covers x hxT
    refine mem_image.2 ⟨B, hB, ?_⟩
    apply le_antisymm
    · apply Finset.sup_le
      intro y hy
      by_contra hlt
      obtain ⟨l, j, rfl⟩ := h.isBlock B hB
      have hxB' : x ∈ dyadicBlock l j := hxB
      simp only [dyadicBlock, mem_Ico, id] at hxB' hy hlt
      have : x + 1 ∈ dyadicBlock l j := by
        simp only [dyadicBlock, mem_Ico]
        omega
      exact hx1 (h.subset _ hB this)
    · exact Finset.le_sup (f := id) hxB
  exact (card_le_card hsub).trans card_image_le

/-! ## Block identifiers and materialized lists -/

/-- A block identifier `(level, index)`.  Identifiers, not position sets, are what a
compiler writes; the same identifier can occur in the lists of many root actions. -/
abbrev BlockId := ℕ × ℕ

/-- Positions covered by a block identifier. -/
def blockOf (b : BlockId) : Finset ℕ := dyadicBlock b.1 b.2

/-- Contract on a materialized list `l` of block identifiers for the position set `T`:
every listed block is contained in `T` and every position of `T` lies in a listed block.
Overlaps and repetitions are allowed. -/
structure IsListCover (l : List BlockId) (T : Finset ℕ) : Prop where
  subset : ∀ b ∈ l, blockOf b ⊆ T
  covers : ∀ x ∈ T, ∃ b ∈ l, x ∈ blockOf b

lemma IsListCover.toOverlap {l : List BlockId} {T : Finset ℕ} (h : IsListCover l T) :
    IsOverlapCover (l.toFinset.image blockOf) T where
  isBlock := by
    intro B hB
    obtain ⟨b, -, rfl⟩ := mem_image.1 hB
    exact ⟨b.1, b.2, rfl⟩
  subset := by
    intro B hB
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hB
    exact h.subset b (List.mem_toFinset.1 hb)
  covers := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := h.covers x hx
    exact ⟨blockOf b, mem_image.2 ⟨b, List.mem_toFinset.2 hb, rfl⟩, hxb⟩

/-- A materialized list covering `T` has at least as many entries as `T` has runs. -/
theorem runs_le_length_of_listCover {l : List BlockId} {T : Finset ℕ} (h : IsListCover l T) :
    runs T ≤ l.length :=
  (runs_le_card_of_overlapCover h.toOverlap).trans
    (card_image_le.trans (List.toFinset_card_le l))

/-! ## Every-layout incidence bound for overlapping covers -/

/-- **Every-layout bound, overlapping covers.**  For `r = 2^k ≥ 2`, every ordering `π` of
the `r² + 1` terminals and every family of possibly overlapping dyadic covers of the parity
supports under `π`: `r³ ≤ 2 Σ_p |C p|`. -/
theorem parityGrid_overlapCover_lower {k : ℕ} (hk : 1 ≤ k)
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (C : ParityIndex k → Finset (Finset ℕ))
    (hC : ∀ p ∈ parityActions k, IsOverlapCover (C p) (layoutPos π (paritySupp p))) :
    (2 ^ k) ^ 3 ≤ 2 * ∑ p ∈ parityActions k, (C p).card := by
  have h3 : ((2 : ℕ) ^ k) ^ 3 = 2 ^ k * 2 ^ k * 2 ^ k := by ring
  rw [h3]
  refine (parityGrid_runs_lower hk π).trans (Nat.mul_le_mul_left 2 ?_)
  exact sum_le_sum (fun p hp => runs_le_card_of_overlapCover (hC p hp))

/-- **Every-layout bound, lists with overlaps and repetitions.** -/
theorem parityGrid_listCover_lower {k : ℕ} (hk : 1 ≤ k)
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (L : ParityIndex k → List BlockId)
    (hL : ∀ p ∈ parityActions k, IsListCover (L p) (layoutPos π (paritySupp p))) :
    (2 ^ k) ^ 3 ≤ 2 * ∑ p ∈ parityActions k, (L p).length := by
  have h3 : ((2 : ℕ) ^ k) ^ 3 = 2 ^ k * 2 ^ k * 2 ^ k := by ring
  rw [h3]
  refine (parityGrid_runs_lower hk π).trans (Nat.mul_le_mul_left 2 ?_)
  exact sum_le_sum (fun p hp => runs_le_length_of_listCover (hL p hp))

/-- The manuscript's count `r (r² - 1) / 2` (Step 2) is implied by `r³ / 2`. -/
lemma manuscript_count_le (r : ℕ) : r * (r ^ 2 - 1) ≤ r ^ 3 := by
  calc r * (r ^ 2 - 1) ≤ r * r ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = r ^ 3 := by ring

/-! ## The compiler model: traces of unit-cost instructions -/

/-- Unit-cost instructions of a compiler.  `emit a b` materializes the incidence from the
output list of key `a` to the block `b`; `other o` is any other unit-cost operation, `Op`
being an arbitrary type of operations. -/
inductive Instr (K Op : Type*) where
  | emit (a : K) (b : BlockId)
  | other (o : Op)

section Trace

variable {K Op : Type*} [DecidableEq K]

/-- The list materialized for key `a0` by a trace: the blocks of the instructions
`emit a0 _`, in order of emission.  The output is defined from the trace. -/
def emitted : List (Instr K Op) → K → List BlockId
  | [], _ => []
  | Instr.emit a b :: tr, a0 => if a = a0 then b :: emitted tr a0 else emitted tr a0
  | Instr.other _ :: tr, a0 => emitted tr a0

/-- Work of a trace: one unit per instruction. -/
def work (tr : List (Instr K Op)) : ℕ := tr.length

lemma emitted_append (tr tr' : List (Instr K Op)) (a0 : K) :
    emitted (tr ++ tr') a0 = emitted tr a0 ++ emitted tr' a0 := by
  induction tr with
  | nil => rfl
  | cons i tr ih =>
    cases i with
    | emit a b =>
      simp only [List.cons_append, emitted, ih]
      split <;> rfl
    | other o => simpa [emitted] using ih

/-- **Each emitted incidence is paid for.**  The total length of the output lists of any
set of distinct keys is at most the work of the trace. -/
theorem sum_emitted_length_le (tr : List (Instr K Op)) (keys : Finset K) :
    ∑ a ∈ keys, (emitted tr a).length ≤ work tr := by
  induction tr with
  | nil => simp [emitted, work]
  | cons i tr ih =>
    cases i with
    | emit a b =>
      have h1 : ∀ a0 ∈ keys, (emitted (Instr.emit (Op := Op) a b :: tr) a0).length
          = (emitted tr a0).length + (if a = a0 then 1 else 0) := by
        intro a0 _
        simp only [emitted]
        split <;> simp
      rw [sum_congr rfl h1, sum_add_distrib, sum_ite_eq]
      have h2 : (if a ∈ keys then 1 else 0) ≤ 1 := by split <;> omega
      simp only [work, List.length_cons] at ih ⊢
      omega
    | other o =>
      simp only [emitted, work, List.length_cons] at ih ⊢
      omega

/-- **Work bound for a trace.**  If for each key `a` of a set of distinct keys the emitted
list covers the position set `T a`, the work is at least the total number of runs. -/
theorem runs_le_work (tr : List (Instr K Op)) (keys : Finset K) (T : K → Finset ℕ)
    (h : ∀ a ∈ keys, IsListCover (emitted tr a) (T a)) :
    ∑ a ∈ keys, runs (T a) ≤ work tr :=
  (sum_le_sum (fun a ha => runs_le_length_of_listCover (h a ha))).trans
    (sum_emitted_length_le tr keys)

/-- A compiler given as a program: an arbitrary step function on an arbitrary state type,
performing one instruction per step and possibly halting.  `exec step n s` is the trace of
at most `n` steps from state `s`. -/
def exec {σ : Type*} (step : σ → Option (Instr K Op × σ)) : ℕ → σ → List (Instr K Op)
  | 0, _ => []
  | n + 1, s =>
    match step s with
    | none => []
    | some (i, s') => i :: exec step n s'

omit [DecidableEq K] in
lemma exec_length_le {σ : Type*} (step : σ → Option (Instr K Op × σ)) (n : ℕ) (s : σ) :
    work (exec step n s) ≤ n := by
  induction n generalizing s with
  | zero => simp [exec, work]
  | succ n ih =>
    simp only [exec]
    cases hs : step s with
    | none => simp [work]
    | some q =>
      obtain ⟨i, s'⟩ := q
      have := ih s'
      simp only [work, List.length_cons] at this ⊢
      omega

end Trace

/-! ## The parity-grid instance of `ParityGrid.pgDag` -/

/-- The parity actions are exactly the first `d` root actions of `pgDag k`. -/
lemma parityActions_eq_image (k : ℕ) : parityActions k = univ.image (pgIdx k) := by
  ext p
  simp only [mem_image, mem_univ, true_and]
  constructor
  · intro hp
    exact pgIdx_surj k hp
  · rintro ⟨a, rfl⟩
    exact pgIdx_mem k a

/-- Total number of runs of the root supports of `pgDag k` under any terminal ordering. -/
theorem pgSupp_runs_lower {k : ℕ} (hk : 1 ≤ k)
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1)) :
    (2 ^ k) ^ 3 ≤ 2 * ∑ a : Fin (pgD k + 1), runs (layoutPos π (pgSupp k a)) := by
  have h3 : ((2 : ℕ) ^ k) ^ 3 = 2 ^ k * 2 ^ k * 2 ^ k := by ring
  rw [h3]
  refine (parityGrid_runs_lower hk π).trans (Nat.mul_le_mul_left 2 ?_)
  rw [parityActions_eq_image, sum_image (fun a _ b _ h => pgIdx_injective k h),
    Fin.sum_univ_castSucc]
  simp only [pgSupp_castSucc]
  exact Nat.le_add_right _ _

/-- **Compiler work, keyed output.**  Let `r = 2^k`, `k ≥ 1`.  Let the output lists be
named by keys `key a`, distinct for distinct root actions `a` of `pgDag k`.  For every
terminal ordering `π` and every trace `tr` such that the list emitted for each root action
is a (possibly overlapping, possibly repeating) dyadic cover of the positions of its support
`pgSupp k a`, the work of the trace is at least `r³ / 2`. -/
theorem compiler_work_lower_keyed {k : ℕ} (hk : 1 ≤ k) {K Op : Type*} [DecidableEq K]
    (key : Fin (pgD k + 1) → K) (hkey : Function.Injective key)
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (tr : List (Instr K Op))
    (hC : ∀ a : Fin (pgD k + 1),
      IsListCover (emitted tr (key a)) (layoutPos π (pgSupp k a))) :
    (2 ^ k) ^ 3 ≤ 2 * work tr := by
  refine (pgSupp_runs_lower hk π).trans (Nat.mul_le_mul_left 2 ?_)
  have h1 : ∑ a : Fin (pgD k + 1), runs (layoutPos π (pgSupp k a))
      ≤ ∑ a : Fin (pgD k + 1), (emitted tr (key a)).length :=
    sum_le_sum (fun a _ => runs_le_length_of_listCover (hC a))
  have h2 : ∑ a : Fin (pgD k + 1), (emitted tr (key a)).length
      = ∑ x ∈ univ.image key, (emitted tr x).length := by
    rw [sum_image (fun a _ b _ h => hkey h)]
  rw [h2] at h1
  exact h1.trans (sum_emitted_length_le tr _)

/-- **Lower half of `thm:coded-main` / `thm:coded-covers` as compiler work.**  Let
`r = 2^k`, `k ≥ 1` (so in particular every power of two `r ≥ 4`).  Consider the parity-grid
DAG `pgDag k`, whose root supports are `pgSupp k a`, `a : Fin (pgD k + 1)`.  A compile phase
is a trace of unit-cost instructions whose output is one list of blocks per distinct root
support (the key of a list is the support itself).  For every terminal ordering `π` and
every trace whose list for each root support `S` is a possibly overlapping dyadic cover of
the positions of `S` under `π`: `r³ ≤ 2 * work`. -/
theorem compiler_work_lower {k : ℕ} (hk : 1 ≤ k) {Op : Type*}
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (tr : List (Instr (Finset (GridTerminal k)) Op))
    (hC : ∀ a : Fin (pgD k + 1),
      IsListCover (emitted tr (pgSupp k a)) (layoutPos π (pgSupp k a))) :
    (2 ^ k) ^ 3 ≤ 2 * work tr :=
  compiler_work_lower_keyed hk (pgSupp k) pgSupp_injective π tr hC

/-- The same statement quantified over the set of distinct root supports rather than over
root actions: the contract is imposed on each `S` in the image of `pgSupp k`. -/
theorem compiler_work_lower_supports {k : ℕ} (hk : 1 ≤ k) {Op : Type*}
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (tr : List (Instr (Finset (GridTerminal k)) Op))
    (hC : ∀ S ∈ (univ : Finset (Fin (pgD k + 1))).image (pgSupp k),
      IsListCover (emitted tr S) (layoutPos π S)) :
    (2 ^ k) ^ 3 ≤ 2 * work tr :=
  compiler_work_lower hk π tr (fun a => hC _ (mem_image_of_mem _ (mem_univ a)))

/-- The root supports are pairwise distinct, so there are exactly `d + 1 = 4 (r - 1) + 1`
lists: no two root actions can share a list. -/
theorem card_root_supports (k : ℕ) :
    ((univ : Finset (Fin (pgD k + 1))).image (pgSupp k)).card = 4 * (2 ^ k - 1) + 1 := by
  rw [card_image_of_injective _ pgSupp_injective, card_univ, Fintype.card_fin, pgD]

/-- **Later work cannot reduce compile work.**  If the compile phase `tr` meets the contract
and is followed by any further instructions `rest` (rollouts, caching, incidence
retirement, ...), the total work is still at least `r³ / 2`. -/
theorem compiler_total_work_lower {k : ℕ} (hk : 1 ≤ k) {Op : Type*}
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (tr rest : List (Instr (Finset (GridTerminal k)) Op))
    (hC : ∀ a : Fin (pgD k + 1),
      IsListCover (emitted tr (pgSupp k a)) (layoutPos π (pgSupp k a))) :
    (2 ^ k) ^ 3 ≤ 2 * work (tr ++ rest) := by
  have h := compiler_work_lower hk π tr hC
  simp only [work, List.length_append] at h ⊢
  omega

/-- **Compilers given as programs.**  A program with arbitrary state `σ` and step function
`step`, started in `s₀` and run for at most `n` unit-cost steps, whose emitted lists meet
the contract for some terminal ordering `π`, has run for `n ≥ r³ / 2` steps. -/
theorem compiler_program_lower {k : ℕ} (hk : 1 ≤ k) {Op σ : Type*}
    (step : σ → Option (Instr (Finset (GridTerminal k)) Op × σ)) (s₀ : σ) (n : ℕ)
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (hC : ∀ a : Fin (pgD k + 1),
      IsListCover (emitted (exec step n s₀) (pgSupp k a)) (layoutPos π (pgSupp k a))) :
    (2 ^ k) ^ 3 ≤ 2 * n :=
  (compiler_work_lower hk π _ hC).trans (Nat.mul_le_mul_left 2 (exec_length_le step n s₀))

/-- Contrapositive form: no trace of fewer than `r³ / 2` instructions meets the contract,
whatever the terminal ordering. -/
theorem no_compiler_below {k : ℕ} (hk : 1 ≤ k) {Op : Type*}
    (tr : List (Instr (Finset (GridTerminal k)) Op)) (hw : 2 * work tr < (2 ^ k) ^ 3) :
    ¬ ∃ π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1), ∀ a : Fin (pgD k + 1),
      IsListCover (emitted tr (pgSupp k a)) (layoutPos π (pgSupp k a)) := by
  rintro ⟨π, hC⟩
  exact absurd (compiler_work_lower hk π tr hC) (not_le.2 hw)

end LiteralK5
end JointRootCert
