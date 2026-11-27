/-
Joint Root Certification: `prop:representation-cost` (Unified Full-Cost Representation
Comparison), upper bound `eq:prop-rep-upper`, for the linked engine of `LiteralG4`, with
(1) a strict RAM accounting in which every executed array-cell read, array-cell write and
comparison is charged exactly one unit, and (2) the upfront passes `P_G` of the direct engine
computed (executed and charged) instead of given.

Manuscript result covered: `prop:representation-cost` (all three sentences), restated from
`LiteralG4` (same executed program, same states) with the strict accounting and with `P_G`
computed.

## 1. Strict accounting

`LiteralG4` charges some RAM primitives together in one unit (e.g. in `dlvL` the test `g < N`
and the head read; in `waveDLf` one flat 3 for the leaf test, the target comparison and a
`findMax` read; in the inherited heap code one unit per sift step for two comparisons, a swap
and two position writes).  Here every cost-returning definition executed by the run of
`LiteralG4` gets an **operation count** `…Ops`, defined by the same recursion over the same
states (the states are those of the `LiteralG4` definitions, so no simulation is redone), in
which each executed primitive is one unit.  Conventions of the count (a fixed RAM
implementation of each definition):

* a heap's size `n`, its arrays `hd`, `ky`, `pos`, the value, mark, count, flag, head, next,
  previous, `src`, `dst` arrays are memory; scalars (`N`, `M`, `K`, the rollout data, loop
  indices, the current leader and its value) are registers; arithmetic is free;
* a list in memory is a chain of cells (value, next): visiting a cell is 2 reads and its loop
  test 1 comparison (3 per element, 1 for the final test); creating a cell (push, append,
  emit) is 3 writes (value, next, head or tail pointer); a pop is 5 (read head, null test,
  read value and next, write head); a loop over `0, …, n-1` costs 1 comparison per index and
  1 for the exit;
* a condition is evaluated in full (no short-circuit), so its count does not depend on the
  outcome of its conjuncts;
* `Heap.swap` is 10 (4 reads, 4 writes, 2 position writes); `bigChild` 5; `findMax` 3;
* `bldL` (recursive, it reads the result of the recursive call) is charged its call frame
  (push 3, pop 5) per element;
* loops with a fuel argument count 0 at fuel 0 (the fuels never bind, `LiteralG4`);
* the stop rule `φ` is an oracle, a parameter of the algorithm like `H`: each evaluation of
  `φ` is one call charged one unit (the gap test per index in `stopOps` is the call of
  `φ (U n)` and its comparison; `φ la` is called once per query, inside the 2 units read for
  the leader);
* the `K` activity flags are written at initialisation (`WflagLS = 2 K + 1`).

Op counts: `siftUpOps`, `siftDownOps`, `updateAtOps`, `updateKeyOps`, `deleteAtOps`,
`deleteOps`, `heapLoopOps`, `heapifyOps` (heaps); `dlvOneOps`, `dlvWOps`, `dlvLOps`,
`loopDLOps`, `targetLOps`, `waveDLfOps` (waves); `setMarksOps`, `filterOps`, `clearMarksOps`,
`mergeMOps` (merge); `travEOps`, `pTravOps`, `candTravOps`, `dstAllOps` (candidates);
`retireOneLOps`, `retireListLOps` (retirement); `relTravOps`, `relGateOps`,
`releaseLoopLOps`, `disposeLOps` (cascade, disposal); `leadOps`, `stopOps`, `retOps`,
`decOps`, `qRetireLOps` (queries); `initGateBXOps`, `initPassBXOps`, the mark and count
table passes, `recsOps`, `bldLOps`, `phBOps`, `scatterOps`, `mapTOps`, `phDOps`,
`buildLinOps` (initialisation).  Each is bounded by a constant times the `LiteralG4` charge
of the same call (`…Ops_le`), with no hypothesis.

**Heap reset of a released gate.**  `LiteralG4.relGate` replaces the two heaps of the
released gate by `Heap.empty`.  The executed reset (`clearHeap`) writes `n := 0` in both heaps
(2 units) and, for every child `c` read by the traversal of the child list, `pos c := none` in
both heaps (2 units per record, counted in `relTravOps`).  `clearHeap_spec`: if the heap stores
exactly the children of the gate (`Rep`, which the engine's heaps satisfy: `SimR`,
`RetireFinal.releaseLoopH_sim`), the cleared heap has `n = 0` and an all-`none` position array,
like `Heap.empty`, and every heap operation of the engine (`findMax`, `lookup`, `updateKey`,
`delete`) gives on it the same result as on `Heap.empty`.  `heap_invariants_run` (also the
first conjunct of `representation_cost_upper_strict`): along the run, every release executed
by the cascade of every rollout (its start state is `retireListH` on the post-wave state,
`casc_sim`, via `LiteralG2.stepG`, `EngineFinal.retireListH_sim`), by every cascade from a
query state and by the disposal happens at a gate with `Rep` (`relsOK`, `dispOK`, kept by
each release: `simE_release`), so `clearHeap_spec` applies at each one (`RepOK.clear`).

**Heap construction.**  `ofKeys` writes `hd`, `ky`, `pos` for the children only
(`writePos`).  Proved: each gate of `order` finds its heap with the position array of
`Heap.empty` when it is initialised (`initOK`, from `SelRun.empty_lo/hi` and
`order_nodup`), and on such a heap the executed writes give exactly the position array of
`ofKeys` (`ofKeys_pos_exec`).  `ofKeys` is executed only at initialisation; later position
writes are those of the sifts, deletions and resets, all charged.

**Frame (arbitrary heap memory).**  `HAgree A H H'`: same size, same handle and key cells
below the size, same position cells for the handles in `A`.  Proved: `siftUp_agree`,
`siftDown_agree`, `heapLoopX_agree` (no position cell is read), `updateKey_agree`,
`delete_agree` (the position array is read only at the handle argument), `findMax_agree`;
each gives `HAgree` results at the same cost.  `ofKeysExec_agree`: the construction executed
on arbitrary heap memory agrees with `ofKeys` (and after `heapify`'s loop) on the children;
`clearHeap_agree`: the cleared heap agrees with `Heap.empty`.  **Open**: the run-level
lifting (that the whole run, with every heap replaced by an `HAgree`-related one for the
current children, has identical outputs at every time, and that every `updateKey` / `delete`
handle of the run is a current child of that gate).  The statements above therefore still
use `SelRun.empty_lo/hi` (given empty initial heaps) for the run; the per-operation
frame results are what such a lifting would compose.

Result: `WLS ≤ 23 · WLnoP` (`WLS_le`), hence `WLS ≤ 6969 · XD0` (`WLS_le_XD0`).

## 2. `P_G` computed

`LiteralG4.WL` adds the given number `R.P` to the executed initialisation.  Here
`PG` (old accounting) and `PGS` (strict) are the executed costs of the upfront passes of the
direct engine: the two heap initialisation passes (`initPassBX`), the mark table, the count
table (zeroing and the `K` root increments) and the incidence structure (`buildLin`).
`WLnoP = WL − R.P` is the total work with `R.P` left out (`WL_eq`), `XD0` is `XD` with
`P = 0`.  Proved (children gates, root actions distinct gates `< N`):
`WLnoP ≤ 303 · XD0`, `PG ≤ 27 (N + live)`, `PGS ≤ 621 (N + live)`.  `XG` / `XGS` are the right
side of `eq:prop-rep-upper` with `P_R := PG` / `PGS`; `XD0 ≤ XGS ≤ 622 · XD0`.

## What remains an input (by the proposition's own statement)

* `H` (`R.H`, through `Hsh`): the shared search work, common to all representations, added as
  a number;
* the run data: rollouts `u`, query times `q`, stopping time `τ`, root actions `rt`; all
  theorems are quantified over every run (`SelRun`) and every initial memory content of the
  arrays in `Mem`;
* **open, not yet computed**: the level-sorted initialisation order `order` (a field of
  `SelRun` with `order_all`, `order_int`, `order_sorted`, `order_nodup`; sorting by the
  given levels costs `Θ(N + L)` or `N log N`, neither in `XD0`) and the empty initial heaps
  (`SelRun.empty_lo/hi`, see Frame);
* the input circuit `G0` (its child and parent lists are read by the passes, not built).
-/

import JointRootCert.LiteralG4

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace JointRootCert
namespace LiteralG5

open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open LiteralF4 LiteralG2 LiteralG4
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH)
open Asymptotics

/-! ## 1. Heap operations -/

section HeapOps

variable {ι β : Type*} [DecidableEq ι] [LinearOrder β]

/-- `Heap.swap`: read `hd a, hd b, ky a, ky b`, write them back exchanged, write the two
positions. -/
def swapOps : ℕ := 10

/-- Sift up: test `0 < j`, read `ky (par j)`, `ky j`, compare (4); a swap (10) if it moves. -/
def siftUpOps : ℕ → Heap ι β → ℕ → ℕ
  | 0, _, _ => 0
  | d + 1, H, j =>
    if 0 < j ∧ H.ky (HeapImpl.par j) < H.ky j then
      4 + swapOps + siftUpOps d (H.swap j (HeapImpl.par j)) (HeapImpl.par j)
    else 4

lemma siftUpOps_le : ∀ (d : ℕ) (H : Heap ι β) (j : ℕ),
    siftUpOps d H j ≤ 14 * (HeapImpl.siftUp d H j).2 := by
  intro d
  induction d with
  | zero => intro H j; simp [siftUpOps]
  | succ d ih =>
    intro H j
    rw [siftUpOps, HeapImpl.siftUp]
    split_ifs
    · have := ih (H.swap j (HeapImpl.par j)) (HeapImpl.par j)
      dsimp only [swapOps]; omega
    · dsimp only; omega

/-- `bigChild`: read `n`, compare `2j+2 < n`, read the two child keys, compare. -/
def bigChildOps : ℕ := 5

/-- Sift down: read `n`, compare `2j+1 < n`, `bigChild` (5), read `ky j` and the key of the
big child, compare (10 in all); a swap (10) if it moves. -/
def siftDownOps : ℕ → Heap ι β → ℕ → ℕ
  | 0, _, _ => 0
  | d + 1, H, j =>
    if 2 * j + 1 < H.n ∧ H.ky j < H.ky (HeapImpl.bigChild H j) then
      5 + bigChildOps + swapOps
        + siftDownOps d (H.swap j (HeapImpl.bigChild H j)) (HeapImpl.bigChild H j)
    else 5 + bigChildOps

lemma siftDownOps_le : ∀ (d : ℕ) (H : Heap ι β) (j : ℕ),
    siftDownOps d H j ≤ 20 * (HeapImpl.siftDown d H j).2 := by
  intro d
  induction d with
  | zero => intro H j; simp [siftDownOps]
  | succ d ih =>
    intro H j
    rw [siftDownOps, HeapImpl.siftDown]
    split_ifs
    · have := ih (H.swap j (HeapImpl.bigChild H j)) (HeapImpl.bigChild H j)
      dsimp only [swapOps, bigChildOps]; omega
    · dsimp only [bigChildOps]; omega

lemma siftDown_pos (d : ℕ) (H : Heap ι β) (j : ℕ) : 1 ≤ (HeapImpl.siftDown d H j).2 := by
  cases d with
  | zero => simp [HeapImpl.siftDown]
  | succ d => rw [HeapImpl.siftDown]; split_ifs <;> simp

/-- Key update at a known position: read `ky i`, compare with the new key, write it (3),
then the sift. -/
def updateAtOps (H : Heap ι β) (i : ℕ) (x : β) : ℕ :=
  3 + if H.ky i ≤ x then siftUpOps (Nat.clog 2 H.n) (H.setKey i x) i
    else siftDownOps (Nat.clog 2 H.n) (H.setKey i x) i

lemma updateAtOps_le (H : Heap ι β) (i : ℕ) (x : β) :
    updateAtOps H i x + 2 ≤ 20 * (HeapImpl.updateAt H i x).2 := by
  unfold updateAtOps HeapImpl.updateAt
  split_ifs
  · have := siftUpOps_le (Nat.clog 2 H.n) (H.setKey i x) i
    dsimp only; omega
  · have := siftDownOps_le (Nat.clog 2 H.n) (H.setKey i x) i
    dsimp only; omega

/-- update-key: read `pos h`, test it (2), then the update at that position. -/
def updateKeyOps (H : Heap ι β) (h : ι) (x : β) : ℕ :=
  2 + (H.pos h).elim 0 (fun i => updateAtOps H i x)

lemma updateKeyOps_le (H : Heap ι β) (h : ι) (x : β) :
    updateKeyOps H h x ≤ 20 * (updateKey H h x).2 := by
  unfold updateKeyOps updateKey
  cases H.pos h with
  | none => simp
  | some i =>
    have := updateAtOps_le H i x
    simp only [Option.elim_some]; omega

/-- `findMax`: read `n`, compare with `0`, read `ky 0`. -/
def findMaxOps : ℕ := 3

/-- Deletion at a known position: read `n`, compare `i = n - 1` (2); for the last entry write
`n` and `pos h` (2); otherwise read `ky i`, `ky (n-1)`, compare (3), move the last entry
(read `hd (n-1)`, `ky (n-1)`, write `hd i`, `ky i`, `pos h`, `pos (hd (n-1))`, `n`: 7), sift. -/
def deleteAtOps (H : Heap ι β) (h : ι) (i : ℕ) : ℕ :=
  2 + if i = H.n - 1 then 2
    else 3 + 7 + if H.ky i ≤ H.ky (H.n - 1) then siftUpOps (Nat.clog 2 H.n) (H.moveLast h i) i
      else siftDownOps (Nat.clog 2 H.n) (H.moveLast h i) i

lemma deleteAtOps_le (H : Heap ι β) (h : ι) (i : ℕ) :
    deleteAtOps H h i + 2 ≤ 20 * (HeapImpl.deleteAt H h i).2 := by
  unfold deleteAtOps HeapImpl.deleteAt
  split_ifs
  · dsimp only; omega
  · have := siftUpOps_le (Nat.clog 2 H.n) (H.moveLast h i) i
    dsimp only; omega
  · have := siftDownOps_le (Nat.clog 2 H.n) (H.moveLast h i) i
    dsimp only; omega

/-- delete: read `pos h`, test it (2), then the deletion at that position. -/
def deleteOps (H : Heap ι β) (h : ι) : ℕ := 2 + (H.pos h).elim 0 (fun i => deleteAtOps H h i)

lemma deleteOps_le (H : Heap ι β) (h : ι) : deleteOps H h ≤ 20 * (HeapImpl.delete H h).2 := by
  unfold deleteOps HeapImpl.delete
  cases H.pos h with
  | none => simp
  | some i =>
    have := deleteAtOps_le H h i
    simp only [Option.elim_some]; omega

/-- The bottom-up loop of `heapify`: per index the loop test (1) and the sift down. -/
def heapLoopOps : ℕ → Heap ι β → ℕ
  | 0, _ => 1
  | j + 1, H => 1 + siftDownOps (Nat.clog 2 H.n) H j
      + heapLoopOps j (HeapImpl.siftDown (Nat.clog 2 H.n) H j).1

lemma heapLoopOps_le : ∀ (j : ℕ) (H : Heap ι β), heapLoopOps j H ≤ 21 * (heapLoopX j H).2 := by
  intro j
  induction j with
  | zero => intro H; simp [heapLoopOps, heapLoopX]
  | succ j ih =>
    intro H
    rw [heapLoopOps, heapLoopX]
    have h1 := siftDownOps_le (Nat.clog 2 H.n) H j
    have h2 := siftDown_pos (Nat.clog 2 H.n) H j
    have h3 := ih (HeapImpl.siftDown (Nat.clog 2 H.n) H j).1
    dsimp only; omega

variable [Inhabited ι]

/-- `heapify`: write the array (`ofKeys`: per child visit 3, read its key 1, write `hd`, `ky`,
`pos` 3; final test 1, write `n` 1), then the bottom-up loop. -/
def heapifyOps (cs : List ι) (k : ι → β) : ℕ :=
  7 * cs.length + 2 + heapLoopOps cs.length (HeapB.ofKeys cs k)

lemma heapifyOps_le (cs : List ι) (k : ι → β) : heapifyOps cs k ≤ 21 * (heapifyX cs k).2 := by
  unfold heapifyOps heapifyX
  have := heapLoopOps_le cs.length (HeapB.ofKeys cs k)
  dsimp only; omega

end HeapOps

/-! ### The reset of a released heap -/

section Reset

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The executed reset of the heap of a released gate with children `cs`: `n := 0` and
`pos c := none` for every child `c` (the other cells are not touched). -/
def clearHeap (H : Heap ℕ α) (cs : List ℕ) : Heap ℕ α :=
  ⟨0, H.hd, H.ky, fun h => if h ∈ cs then none else H.pos h⟩

/-- **The cleared heap is the empty heap for every operation of the engine**: if `H` stores
exactly the children `cs` (`Rep`), the cleared heap has `n = 0` and an all-`none` position
array (as `Heap.empty`), and `lookup`, `findMax`, `updateKey`, `delete` give the same results
as on `Heap.empty` (both heaps are left unchanged, at cost 1). -/
theorem clearHeap_spec {H : Heap ℕ α} {cs : List ℕ} {k : ℕ → α} {b : ℕ}
    (h : Rep H cs.toFinset k b) :
    (clearHeap H cs).n = (Heap.empty : Heap ℕ α).n ∧
    (clearHeap H cs).pos = (Heap.empty : Heap ℕ α).pos ∧
    (clearHeap H cs).lookup = (Heap.empty : Heap ℕ α).lookup ∧
    findMax (clearHeap H cs) = findMax (Heap.empty : Heap ℕ α) ∧
    (∀ g x, updateKey (clearHeap H cs) g x = (clearHeap H cs, 1) ∧
      updateKey (Heap.empty : Heap ℕ α) g x = (Heap.empty, 1)) ∧
    (∀ g, HeapImpl.delete (clearHeap H cs) g = (clearHeap H cs, 1) ∧
      HeapImpl.delete (Heap.empty : Heap ℕ α) g = (Heap.empty, 1)) := by
  have hpos : (clearHeap H cs).pos = (Heap.empty : Heap ℕ α).pos := by
    funext g
    show (if g ∈ cs then none else H.pos g) = none
    by_cases hg : g ∈ cs
    · rw [if_pos hg]
    · rw [if_neg hg]
      have := h.look g
      rw [if_neg (by simpa using hg)] at this
      unfold Heap.lookup at this
      cases hp : H.pos g with
      | none => rfl
      | some i => rw [hp] at this; simp at this
  have hn : (clearHeap H cs).n = (Heap.empty : Heap ℕ α).n := rfl
  refine ⟨hn, hpos, ?_, ?_, fun g x => ⟨?_, ?_⟩, fun g => ⟨?_, ?_⟩⟩
  · funext g; unfold Heap.lookup; rw [hpos]; rfl
  · unfold findMax
    rw [if_pos (show (clearHeap H cs).n = 0 from rfl), if_pos (show (Heap.empty : Heap ℕ α).n = 0 from rfl)]
  · unfold updateKey; rw [show (clearHeap H cs).pos g = none by rw [hpos]; rfl]; rfl
  · rfl
  · unfold HeapImpl.delete; rw [show (clearHeap H cs).pos g = none by rw [hpos]; rfl]; rfl
  · rfl

end Reset

/-! ## 2. Waves -/

section Waves

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- One delivery: the update-key, `findMax` (3), read the stored value of `p` and compare (2);
if it changed, write it and push `p` (4). -/
def dlvOneOps (g : ℕ) (y : α) (p : ℕ) (s : HEState α) (st : List ℕ) : ℕ :=
  updateKeyOps (s.hp p) g y + findMaxOps + 2
    + if findMax (updateKey (s.hp p) g y).1 = s.val p then 0 else 4

lemma dlvOneOps_le (g : ℕ) (y : α) (p : ℕ) (s : HEState α) (st : List ℕ) :
    dlvOneOps g y p s st ≤ 20 * (dlvOne g y p s st).2.2 := by
  have := updateKeyOps_le (s.hp p) g y
  unfold dlvOneOps dlvOne findMaxOps
  split_ifs
  · dsimp only; omega
  · dsimp only; omega

/-- Deliveries along the linked parent list: per record the null test, the read of `src e`,
the delivery and the read of `nx e`; 1 for the final null test. -/
def dlvWOps (L : Lin) (g : ℕ) (y : α) : ℕ → ℕ → HEState α → List ℕ → ℕ
  | 0, _, _, _ => 0
  | f + 1, e, s, st =>
    if e = 0 then 1
    else 3 + dlvOneOps g y (L.src e) s st
      + dlvWOps L g y f (L.P.nx e) (dlvOne g y (L.src e) s st).1 (dlvOne g y (L.src e) s st).2.1

lemma dlvWOps_le (L : Lin) (g : ℕ) (y : α) : ∀ (f e : ℕ) (s : HEState α) (st : List ℕ),
    dlvWOps L g y f e s st ≤ 20 * (dlvW L g y f e s st).2.2 := by
  intro f
  induction f with
  | zero => intro e s st; simp [dlvWOps]
  | succ f ih =>
    intro e s st
    rw [dlvWOps, dlvW]
    split_ifs
    · dsimp only; omega
    · have h1 := ih (L.P.nx e) (dlvOne g y (L.src e) s st).1 (dlvOne g y (L.src e) s st).2.1
      have h2 := dlvOneOps_le g y (L.src e) s st
      dsimp only; omega

/-- Deliveries of a popped gate: compare it with `N` (1); if `g < N`, read the head of its
parent list (1) and walk it. -/
def dlvLOps (L : Lin) (g : ℕ) (y : α) (s : HEState α) (st : List ℕ) : ℕ :=
  if g < L.N then 2 + dlvWOps L g y (L.M + 1) (L.P.hd g) s st else 1

lemma dlvLOps_le (L : Lin) (g : ℕ) (y : α) (s : HEState α) (st : List ℕ) :
    dlvLOps L g y s st ≤ 20 * (dlvL L g y s st).2.2 := by
  unfold dlvLOps dlvL
  split_ifs
  · have := dlvWOps_le L g y (L.M + 1) (L.P.hd g) s st
    dsimp only; omega
  · dsimp only; omega

/-- The stack loop: empty test (read head, null test: 2); a pop (5), the read of the stored
value (1), the record of the popped gate (a new cell: 3) and the deliveries. -/
def loopDLOps (L : Lin) : ℕ → HEState α → List ℕ → ℕ
  | 0, _, _ => 0
  | _ + 1, _, [] => 2
  | f + 1, s, g :: st => 9 + dlvLOps L g (s.val g) s st
      + loopDLOps L f (dlvL L g (s.val g) s st).1 (dlvL L g (s.val g) s st).2.1

lemma loopDLOps_le (L : Lin) : ∀ (f : ℕ) (s : HEState α) (st : List ℕ),
    loopDLOps L f s st ≤ 20 * (loopDL L f s st).2.1 := by
  intro f
  induction f with
  | zero => intro s st; simp [loopDLOps]
  | succ f ih =>
    intro s st
    cases st with
    | nil => simp [loopDLOps, loopDL]
    | cons g st =>
      rw [loopDLOps, loopDL]
      have h1 := dlvLOps_le L g (s.val g) s st
      have h2 := ih (dlvL L g (s.val g) s st).1 (dlvL L g (s.val g) s st).2.1
      dsimp only; omega

/-- The target of the wave entry: the leaf test (compare with `N`, read the head of the child
list, compare: 3), then for a leaf the comparison `g = x` and the read of the stored value (2),
otherwise `findMax` (3). -/
def targetLOps (L : Lin) (g : ℕ) : ℕ := 3 + if leafL L g = true then 2 else findMaxOps

lemma targetLOps_le (L : Lin) (g : ℕ) : targetLOps L g ≤ 6 := by
  unfold targetLOps findMaxOps; split_ifs <;> omega

/-- The wave: the target (`targetLOps`), read the stored value and compare (2); if it differs,
write it and push the entry gate (4), then the stack loop. -/
def waveDLfOps (L : Lin) (F x : ℕ) (y : α) (s : HEState α) : ℕ :=
  targetLOps L x + 2 + if targetL L x y s x = s.val x then 0
    else 4 + loopDLOps L F ⟨Function.update s.val x (targetL L x y s x), s.hp⟩ [x]

lemma waveDLfOps_le (L : Lin) (F x : ℕ) (y : α) (s : HEState α) :
    waveDLfOps L F x y s ≤ 20 * (waveDLf L F x y s).2.1 := by
  have := targetLOps_le L x
  unfold waveDLfOps waveDLf
  split_ifs
  · dsimp only; omega
  · have := loopDLOps_le L F ⟨Function.update s.val x (targetL L x y s x), s.hp⟩ [x]
    dsimp only; omega

def waveDLOps (L : Lin) (x : ℕ) (y : α) (s : HEState α) : ℕ := waveDLfOps L (L.N + 2) x y s

lemma waveDLOps_le (L : Lin) (x : ℕ) (y : α) (s : HEState α) :
    waveDLOps L x y s ≤ 20 * (waveDL L x y s).2.1 := waveDLfOps_le L (L.N + 2) x y s

end Waves

/-! ## 3. Merge, candidates, retirement, cascade, disposal -/

section Rollout

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma setMarksX_cost : ∀ (l : List ℕ) (m : ℕ → Bool), (setMarksX l m).2 = l.length + 1 := by
  intro l; induction l with
  | nil => intro m; rfl
  | cons g l ih => intro m; rw [setMarksX]; dsimp only; rw [ih, List.length_cons]

lemma clearMarksX_cost : ∀ (l : List ℕ) (m : ℕ → Bool), (clearMarksX l m).2 = l.length + 1 := by
  intro l; induction l with
  | nil => intro m; rfl
  | cons g l ih => intro m; rw [clearMarksX]; dsimp only; rw [ih, List.length_cons]

lemma filterUnmarkedX_cost (m : ℕ → Bool) : ∀ (l : List ℕ),
    (filterUnmarkedX m l).2 = l.length + 1 := by
  intro l; induction l with
  | nil => rfl
  | cons g l ih => rw [filterUnmarkedX]; dsimp only; rw [ih, List.length_cons]

lemma decAllX_cost : ∀ (l : List ℕ) (c : ℕ → ℕ), (decAllX l c).2 = l.length + 1 := by
  intro l; induction l with
  | nil => intro c; rfl
  | cons g l ih => intro c; rw [decAllX]; dsimp only; rw [ih, List.length_cons]

/-- Mark writes over a list: per element visit (3) and write (1); final test. -/
def setMarksOps (l : List ℕ) : ℕ := 4 * l.length + 1

/-- Mark clearing over a list: per element visit (3) and write (1); final test. -/
def clearMarksOps (l : List ℕ) : ℕ := 4 * l.length + 1

/-- Filter of the unmarked gates: per element visit (3), read the mark and test it (2), and
for an unmarked gate append it (3); final test. -/
def filterOps (m : ℕ → Bool) : List ℕ → ℕ
  | [] => 1
  | g :: l => 5 + (if m g then 0 else 3) + filterOps m l

lemma filterOps_le (m : ℕ → Bool) : ∀ l : List ℕ, filterOps m l ≤ 8 * l.length + 1 := by
  intro l; induction l with
  | nil => simp [filterOps]
  | cons g l ih => rw [filterOps, List.length_cons]; split_ifs <;> omega

/-- The merge of the two wave records. -/
def mergeMOps (mk : ℕ → Bool) (rl rh : List ℕ) : ℕ :=
  setMarksOps rl + filterOps (setMarksX rl mk).1 rh + clearMarksOps rl

lemma mergeMOps_le (mk : ℕ → Bool) (rl rh : List ℕ) :
    mergeMOps mk rl rh ≤ 8 * (mergeMX mk rl rh).2.2 := by
  have := filterOps_le (setMarksX rl mk).1 rh
  unfold mergeMOps mergeMX setMarksOps clearMarksOps
  dsimp only
  rw [setMarksX_cost, filterUnmarkedX_cost, clearMarksX_cost]
  omega

/-- Readback of a linked list: per record the null test (1), the emission of the record (a
new cell: 3) and the read of the next pointer (1); 1 for the final null test. -/
def travEOps (nx : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, e => if e = 0 then 1 else 5 + travEOps nx f (nx e)

lemma travEOps_le (nx : ℕ → ℕ) : ∀ (f e : ℕ), travEOps nx f e ≤ 2 * (travE nx f e).2 := by
  intro f; induction f with
  | zero => intro e; simp [travEOps]
  | succ f ih =>
    intro e; rw [travEOps, travE]
    split_ifs
    · dsimp only; omega
    · have := ih (nx e); dsimp only; omega

lemma travE_pos (nx : ℕ → ℕ) (f e : ℕ) : 1 ≤ (travE nx (f + 1) e).2 := by
  rw [travE]; split_ifs <;> simp

/-- Parent records of a merged gate: compare it with `N` (1); if `g < N`, read the head of its
parent list (1) and read the list back. -/
def pTravOps (L : Lin) (g : ℕ) : ℕ :=
  if g < L.N then 2 + travEOps L.P.nx (L.M + 1) (L.P.hd g) else 1

lemma pTravOps_le (L : Lin) (g : ℕ) : pTravOps L g ≤ 4 * (pTrav L g).2 := by
  unfold pTravOps pTrav
  split_ifs
  · have h1 := travEOps_le L.P.nx (L.M + 1) (L.P.hd g)
    have h2 := travE_pos L.P.nx L.M (L.P.hd g)
    omega
  · dsimp only; omega

/-- Candidate construction: per merged gate visit (3) and its parent records; final test. -/
def candTravOps (L : Lin) : List ℕ → ℕ
  | [] => 1
  | g :: gs => 3 + pTravOps L g + candTravOps L gs

lemma candTravOps_le (L : Lin) : ∀ m : List ℕ, candTravOps L m ≤ 4 * (candTrav L m).2 := by
  intro m; induction m with
  | nil => simp [candTravOps, candTrav]
  | cons g gs ih =>
    rw [candTravOps, candTrav]
    have := pTravOps_le L g
    dsimp only; omega

/-- Stack of the cascade: per candidate record visit (3), read `dst` (1), push (3); final
test. -/
def dstAllOps (l : List ℕ) : ℕ := 7 * l.length + 1

lemma dstAllOps_le (L : Lin) (l : List ℕ) : dstAllOps l ≤ 7 * (dstAll L l).2 := by
  unfold dstAllOps; rw [(dstAll_spec L l).2]; omega

/-- Retirement test of a record: read `src e`, `dst e`, the two values, compare (5); if it
holds, the two heap deletions and the two unlinks (exact: 5 or 6 each). -/
def retireOneLOps (e : ℕ) (x : HRState α × Lin) : ℕ :=
  5 + if x.1.hi.val (x.2.dst e) < x.1.lo.val (x.2.src e) then
      deleteOps (x.1.lo.hp (x.2.src e)) (x.2.dst e) + deleteOps (x.1.hi.hp (x.2.src e)) (x.2.dst e)
        + (x.2.C.unlink (x.2.src e) e).2 + (x.2.P.unlink (x.2.dst e) e).2
    else 0

lemma retireOneLOps_le (e : ℕ) (x : HRState α × Lin) :
    retireOneLOps e x + 3 ≤ 20 * (retireOneL e x).2 := by
  unfold retireOneLOps retireOneL
  split_ifs
  · have h1 := deleteOps_le (x.1.lo.hp (x.2.src e)) (x.2.dst e)
    have h2 := deleteOps_le (x.1.hi.hp (x.2.src e)) (x.2.dst e)
    dsimp only; omega
  · dsimp only; omega

/-- The retirement pass: per record visit (3) and the retirement test; final test. -/
def retireListLOps : List ℕ → HRState α × Lin → ℕ
  | [], _ => 1
  | e :: es, x => 3 + retireOneLOps e x + retireListLOps es (retireOneL e x).1

lemma retireListLOps_le : ∀ (ids : List ℕ) (x : HRState α × Lin),
    retireListLOps ids x ≤ 20 * (retireListL ids x).2 := by
  intro ids; induction ids with
  | nil => intro x; simp [retireListLOps, retireListL]
  | cons e es ih =>
    intro x
    rw [retireListLOps, retireListL]
    have h1 := retireOneLOps_le e x
    have h2 := ih (retireOneL e x).1
    dsimp only; omega

/-- Traversal of the child list of a released gate: per record the null test (1), read
`dst e` (1), unlink it from the parent list of its child (exact), push the child (3), clear
the position of the child in the two heaps of the gate (2), read `nx e` (1); 1 for the final
null test. -/
def relTravOps (nx own : ℕ → ℕ) : ℕ → ℕ → DL → List ℕ → ℕ
  | 0, _, _, _ => 0
  | f + 1, e, P, st =>
    if e = 0 then 1
    else 8 + (P.unlink (own e) e).2 + relTravOps nx own f (nx e) (P.unlink (own e) e).1 st

lemma relTravOps_le (nx own : ℕ → ℕ) : ∀ (f e : ℕ) (P : DL) (st : List ℕ),
    relTravOps nx own f e P st ≤ 2 * (relTrav nx own f e P st).2.2 := by
  intro f; induction f with
  | zero => intro e P st; simp [relTravOps]
  | succ f ih =>
    intro e P st
    rw [relTravOps, relTrav]
    split_ifs
    · dsimp only; omega
    · have := ih (nx e) (P.unlink (own e) e).1 st
      dsimp only; omega

/-- Release of a gate: the traversal (including the position clearing), the null head of its
child list (1) and `n := 0` in its two heaps (2). -/
def relGateOps (g : ℕ) (st : List ℕ) (x : HRState α × Lin) : ℕ :=
  relTravOps x.2.C.nx x.2.dst (x.2.M + 1) (x.2.C.hd g) x.2.P st + 3

lemma relGateOps_le (g : ℕ) (st : List ℕ) (x : HRState α × Lin) :
    relGateOps g st x ≤ 2 * (relGate g st x).2.2 := by
  have := relTravOps_le x.2.C.nx x.2.dst (x.2.M + 1) (x.2.C.hd g) x.2.P st
  unfold relGateOps relGate; dsimp only; omega

/-- The release cascade: empty test (2); a pop (5) and the release test in full (compare with
`N`, read and test the two heads, read and test the count: 7); a released gate's release. -/
def releaseLoopLOps (prot : ℕ → Bool) : ℕ → List ℕ → HRState α × Lin → ℕ
  | 0, _, _ => 0
  | _ + 1, [], _ => 2
  | f + 1, g :: st, x =>
    12 + if g < x.2.N ∧ x.2.C.hd g ≠ 0 ∧ x.2.P.hd g = 0 ∧ prot g = false then
      relGateOps g st x + releaseLoopLOps prot f (relGate g st x).2.1 (relGate g st x).1
    else releaseLoopLOps prot f st x

lemma releaseLoopLOps_le (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (x : HRState α × Lin),
    releaseLoopLOps prot f st x ≤ 3 * (releaseLoopL prot f st x).2 := by
  intro f; induction f with
  | zero => intro st x; simp [releaseLoopLOps]
  | succ f ih =>
    intro st x
    cases st with
    | nil => simp [releaseLoopLOps, releaseLoopL]
    | cons g st =>
      rw [releaseLoopLOps, releaseLoopL]
      split_ifs
      · have h1 := relGateOps_le g st x
        have h2 := ih (relGate g st x).2.1 (relGate g st x).1
        dsimp only; omega
      · have := ih st x
        dsimp only; omega

/-- The final disposal: per gate the loop test (1) and its release; final test. -/
def disposeLOps : List ℕ → HRState α × Lin → ℕ
  | [], _ => 1
  | g :: gs, x => 1 + relGateOps g [] x + disposeLOps gs (relGate g [] x).1

lemma disposeLOps_le : ∀ (gs : List ℕ) (x : HRState α × Lin),
    disposeLOps gs x ≤ 3 * (disposeL gs x).2 := by
  intro gs; induction gs with
  | nil => intro x; simp [disposeLOps, disposeL]
  | cons g gs ih =>
    intro x
    rw [disposeLOps, disposeL]
    have h1 := relGateOps_le g [] x
    have h2 := ih (relGate g [] x).1
    have h3 : 6 ≤ (relGate g [] x).2.2 := by unfold relGate; dsimp only; omega
    dsimp only; omega

/-- **One rollout of the linked engine, strict count.** -/
def relStepLOps (prot : ℕ → Bool) (u : ℕ × α × α) (s : GS α) (L : Lin) : ℕ :=
  let wl := waveDL L u.1 u.2.1 s.q.r.lo
  let wh := waveDL L u.1 u.2.2 s.q.r.hi
  let mg := mergeMX s.marks wl.2.2 wh.2.2
  let ct := candTrav L mg.1
  let rl := retireListL ct.1 (⟨s.q.r.G, wl.1, wh.1⟩, L)
  let sk := dstAll L ct.1
  waveDLOps L u.1 u.2.1 s.q.r.lo + waveDLOps L u.1 u.2.2 s.q.r.hi
    + mergeMOps s.marks wl.2.2 wh.2.2 + candTravOps L mg.1
    + retireListLOps ct.1 (⟨s.q.r.G, wl.1, wh.1⟩, L) + dstAllOps ct.1
    + releaseLoopLOps prot (relFuel rl.1.1.G sk.1) sk.1 rl.1

lemma relStepLOps_le (prot : ℕ → Bool) (u : ℕ × α × α) (s : GS α) (L : Lin) :
    relStepLOps prot u s L ≤ 20 * (relStepL prot u s L).2 := by
  unfold relStepLOps relStepL
  dsimp only
  set wl := waveDL L u.1 u.2.1 s.q.r.lo with hwl
  set wh := waveDL L u.1 u.2.2 s.q.r.hi with hwh
  set mg := mergeMX s.marks wl.2.2 wh.2.2 with hmg
  set ct := candTrav L mg.1 with hct
  set rl := retireListL ct.1 (⟨s.q.r.G, wl.1, wh.1⟩, L) with hrl
  set sk := dstAll L ct.1 with hsk
  have h1 : waveDLOps L u.1 u.2.1 s.q.r.lo ≤ 20 * wl.2.1 := waveDLOps_le L u.1 u.2.1 s.q.r.lo
  have h2 : waveDLOps L u.1 u.2.2 s.q.r.hi ≤ 20 * wh.2.1 := waveDLOps_le L u.1 u.2.2 s.q.r.hi
  have h3 : mergeMOps s.marks wl.2.2 wh.2.2 ≤ 8 * mg.2.2 := mergeMOps_le s.marks wl.2.2 wh.2.2
  have h4 : candTravOps L mg.1 ≤ 4 * ct.2 := candTravOps_le L mg.1
  have h5 : retireListLOps ct.1 (⟨s.q.r.G, wl.1, wh.1⟩, L) ≤ 20 * rl.2 :=
    retireListLOps_le ct.1 (⟨s.q.r.G, wl.1, wh.1⟩, L)
  have h6 : dstAllOps ct.1 ≤ 7 * sk.2 := dstAllOps_le L ct.1
  have h7 := releaseLoopLOps_le prot (relFuel rl.1.1.G sk.1) sk.1 rl.1
  omega

end Rollout

/-! ## 4. Queries -/

section Query

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Leader scan: per index the loop test, read the flag, test it, read the root gate and its
value (5), and if a leader exists compare with its value (1); 1 for the exit test. -/
def leadOps (L : ℕ → α) (act : ℕ → Bool) : ℕ → ℕ
  | 0 => 1
  | n + 1 => leadOps L act n + 5 + (if ((leadScanX L act n).1).isSome then 1 else 0)

lemma leadOps_le (L : ℕ → α) (act : ℕ → Bool) : ∀ n, leadOps L act n ≤ 6 * n + 1 := by
  intro n; induction n with
  | zero => simp [leadOps]
  | succ n ih => rw [leadOps]; split_ifs <;> omega

/-- Stop scan: per index the loop test, read the flag, compare with the leader index, read the
root gate and its upper value, compare the gap with `ε`, test the flag (7); exit test. -/
def stopOps (K : ℕ) : ℕ := 7 * K + 1

/-- Retirement scan: per index the loop test, read and test the flag, compare with the leader
index, read the root gate and its upper value, compare with the leader's lower value (7); if
retired, clear the flag (1) and append the gate (a new cell: 3), 4 in all; exit test. -/
def retOps (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) : ℕ → ℕ
  | 0 => 1
  | n + 1 => retOps rt a U la act n + 7
      + (if (retScanX rt a U la act n).1 n = true ∧ n ≠ a ∧ U n < la then 4 else 0)

lemma retOps_le (rt : ℕ → ℕ) (a : ℕ) (U : ℕ → α) (la : α) (act : ℕ → Bool) :
    ∀ n, retOps rt a U la act n ≤ 11 * n + 1 := by
  intro n; induction n with
  | zero => simp [retOps]
  | succ n ih => rw [retOps]; split_ifs <;> omega

/-- Decrements of the count table over the retired gates: visit (3), read and write the count
(2); final test. -/
def decOps (l : List ℕ) : ℕ := 5 * l.length + 1

/-- **One query of the linked engine, strict count**: the leader scan and the test of its
result (1); with a leader, the read of its gate and lower value (2), the stop scan, the
retirement scan, the decrements and the cascade. -/
def qRetireLOps (K : ℕ) (rt : ℕ → ℕ) (c : ℕ → ℕ) (s : HQS α) (L : Lin) : ℕ :=
  (leadScanX (fun i => s.r.lo.val (rt i)) s.act K).1.elim
    (leadOps (fun i => s.r.lo.val (rt i)) s.act K + 1)
    (fun a =>
      leadOps (fun i => s.r.lo.val (rt i)) s.act K + 1 + 2 + stopOps K
        + retOps rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act K
        + decOps (retScanX rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act K).2.1
        + releaseLoopLOps
            (pidx (decAllX (retScanX rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
              s.act K).2.1 c).1)
            (relFuel s.r.G (retScanX rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
              s.act K).2.1)
            (retScanX rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act K).2.1
            (s.r, L))

lemma qRetireLOps_le (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (c : ℕ → ℕ) (s : HQS α)
    (L : Lin) : qRetireLOps K rt c s L ≤ 5 * (qRetireL φ ε K rt c s L).2 := by
  have hl := leadOps_le (fun i => s.r.lo.val (rt i)) s.act K
  have hl2 := (leadScanX_spec (fun i => s.r.lo.val (rt i)) s.act K)
  unfold qRetireLOps qRetireL
  rw [hl2]
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => dsimp only [Option.elim]; omega
  | some a =>
    dsimp only [Option.elim]
    obtain ⟨-, -, rs3⟩ := retScanX_spec rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
      s.act K
    have hr := retOps_le rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act K
    have hc := releaseLoopLOps_le
      (pidx (decAllX (retScanX rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
        s.act K).2.1 c).1)
      (relFuel s.r.G (retScanX rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a))
        s.act K).2.1)
      (retScanX rt a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act K).2.1 (s.r, L)
    rw [stopScanX_spec, rs3, decAllX_cost]
    unfold stopOps decOps
    omega

end Query

/-! ## 5. Initialisation -/

section Init

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Initialisation of one gate: `heapify` of its children, `findMax` (3), write its value (1). -/
def initGateBXOps (G : Dag) (g : ℕ) (s : HEState α) : ℕ :=
  heapifyOps (G.children g) s.val + findMaxOps + 1

lemma initGateBXOps_le (G : Dag) (g : ℕ) (s : HEState α) :
    initGateBXOps G g s ≤ 21 * (initGateBX G g s).2 ∧ 2 ≤ (initGateBX G g s).2 := by
  have := heapifyOps_le (G.children g) s.val
  unfold initGateBXOps initGateBX heapifyX findMaxOps at *
  dsimp only at *
  omega

/-- The initialisation pass over `order`: per gate visit (3) and its initialisation; final
test. -/
def initPassBXOps (G : Dag) : List ℕ → HEState α → ℕ
  | [], _ => 1
  | g :: rest, s => 3 + initGateBXOps G g s + initPassBXOps G rest (initGateBX G g s).1

lemma initPassBXOps_le (G : Dag) : ∀ (l : List ℕ) (s : HEState α),
    initPassBXOps G l s ≤ 23 * (initPassBX G l s).2 := by
  intro l; induction l with
  | nil => intro s; simp [initPassBXOps, initPassBX]
  | cons g l ih =>
    intro s
    rw [initPassBXOps, initPassBX]
    have h1 := initGateBXOps_le G g s
    have h2 := ih (initGateBX G g s).1
    dsimp only; omega

end Init

/-! ### Construction of the incidence structure -/

section Build

lemma recs_cost (p : ℕ) : ∀ (l : List ℕ) (k : ℕ) (B : RB), (recs p l k B).2 = 4 * l.length + 1 := by
  intro l; induction l with
  | nil => intro k B; rfl
  | cons c l ih => intro k B; rw [recs]; dsimp only; rw [ih, List.length_cons]; ring

lemma bldL_cost : ∀ (es : List ℕ) (D : DL), (bldL es D).2.2 = 4 * es.length + 1 := by
  intro es; induction es with
  | nil => intro D; rfl
  | cons e es ih => intro D; rw [bldL]; dsimp only; rw [ih, List.length_cons]; ring

lemma scatter_cost (src : ℕ → ℕ) : ∀ (l : List ℕ) (T : ℕ → ℕ),
    (scatter src l T).2 = 2 * l.length + 1 := by
  intro l; induction l with
  | nil => intro T; rfl
  | cons e l ih => intro T; rw [scatter]; dsimp only; rw [ih, List.length_cons]; ring

/-- Phase B1 for one gate: per child visit (3), write `src` and `dst` (2), read the head of the
child's incoming list (1), prepend the record (3); final test. -/
def recsOps (l : List ℕ) : ℕ := 9 * l.length + 1

/-- Construction of one list (recursive): per record the visit (`v`: 3 for a list in memory,
1 for a counter range), the call frame (push 3, pop 5), write `nx e`, test the head for null,
write `pv e` (3), and, if the head is a record, write its `pv` (1); 1 for the empty list. -/
def bldLOps (v : ℕ) : List ℕ → DL → ℕ
  | [], _ => 1
  | e :: es, D => bldLOps v es D + v + 11 + (if (bldL es D).2.1 = 0 then 0 else 1)

lemma bldLOps_le (v : ℕ) (hv : v ≤ 3) : ∀ (es : List ℕ) (D : DL),
    bldLOps v es D ≤ 15 * es.length + 1 := by
  intro es; induction es with
  | nil => intro D; simp [bldLOps]
  | cons e es ih =>
    intro D; rw [bldLOps, List.length_cons]
    have := ih D
    split_ifs <;> omega

/-- The state after phase B on gate `p`. -/
def phBnext (G : Dag) (p k : ℕ) (X : RB × DL) : RB × DL :=
  ((recs p (G.children p) k X.1).1,
   ⟨Function.update (bldL (List.range' (k + 1) (G.children p).length) X.2).1.hd p
      (bldL (List.range' (k + 1) (G.children p).length) X.2).2.1,
    (bldL (List.range' (k + 1) (G.children p).length) X.2).1.nx,
    (bldL (List.range' (k + 1) (G.children p).length) X.2).1.pv⟩)

/-- Phase B: per gate the loop test (1), its records (`recsOps`), its child list (`bldLOps 1`:
the records are a counter range) and the write of its head (1); final test. -/
def phBOps (G : Dag) : List ℕ → ℕ → RB × DL → ℕ
  | [], _, _ => 1
  | p :: ps, k, X => 1 + recsOps (G.children p)
      + bldLOps 1 (List.range' (k + 1) (G.children p).length) X.2 + 1
      + phBOps G ps (k + (G.children p).length) (phBnext G p k X)

lemma phBOps_le (G : Dag) : ∀ (ps : List ℕ) (k : ℕ) (X : RB × DL),
    phBOps G ps k X ≤ 4 * (phB G ps k X).2 := by
  intro ps; induction ps with
  | nil => intro k X; simp [phBOps, phB]
  | cons p ps ih =>
    intro k X
    have e : (phB G (p :: ps) k X).2 = 1 + (recs p (G.children p) k X.1).2
        + (bldL (List.range' (k + 1) (G.children p).length) X.2).2.2 + 1
        + (phB G ps (k + (G.children p).length) (phBnext G p k X)).2 := rfl
    rw [e, phBOps, recs_cost, bldL_cost]
    have h1 := bldLOps_le 1 (by omega) (List.range' (k + 1) (G.children p).length) X.2
    have h2 := ih (k + (G.children p).length) (phBnext G p k X)
    rw [List.length_range'] at h1 ⊢
    unfold recsOps
    omega

/-- Scatter of the incoming records of a gate: per record visit (3), read `src` (1), write
the table (1); final test. -/
def scatterOps (l : List ℕ) : ℕ := 5 * l.length + 1

/-- Reading the table along the parent list: per parent visit (3), read the table (1), emit
the record (3); final test. -/
def mapTOps (l : List ℕ) : ℕ := 7 * l.length + 1

/-- The state after phase D on gate `c`. -/
def phDnext (G : Dag) (B : RB) (c : ℕ) (X : (ℕ → ℕ) × DL) : (ℕ → ℕ) × DL :=
  ((scatter B.src (B.inc c) X.1).1,
   ⟨Function.update (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.hd c
      (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).2.1,
    (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.nx,
    (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).1.pv⟩)

/-- Phase D: per gate the loop test (1), the scatter, the table reads, its parent list
(`bldLOps 3`) and the write of its head (1); final test. -/
def phDOps (G : Dag) (B : RB) : List ℕ → (ℕ → ℕ) × DL → ℕ
  | [], _ => 1
  | c :: cs, X => 1 + scatterOps (B.inc c) + mapTOps (G.parents c)
      + bldLOps 3 (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2 + 1
      + phDOps G B cs (phDnext G B c X)

lemma phDOps_le (G : Dag) (B : RB) : ∀ (cs : List ℕ) (X : (ℕ → ℕ) × DL),
    phDOps G B cs X ≤ 7 * (phD G B cs X).2 := by
  intro cs; induction cs with
  | nil => intro X; simp [phDOps, phD]
  | cons c cs ih =>
    intro X
    have e : (phD G B (c :: cs) X).2 = 1 + (scatter B.src (B.inc c) X.1).2
        + (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).2
        + (bldL (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2).2.2 + 1
        + (phD G B cs (phDnext G B c X)).2 := rfl
    rw [e, phDOps, scatter_cost, bldL_cost]
    have h1 := bldLOps_le 3 le_rfl (mapT (scatter B.src (B.inc c) X.1).1 (G.parents c)).1 X.2
    have h2 := ih (phDnext G B c X)
    rw [mapT_eq] at h1 ⊢
    simp only [List.length_map] at h1 ⊢
    unfold scatterOps mapTOps
    omega

/-- **Construction of the incidence structure, strict count**: phase A (per gate the loop test
and the write of the empty incoming list: `2 N + 1`), phase B, phase D. -/
def buildLinOps (G : Dag) (B0 : RB) (C0 P0 : DL) (T0 : ℕ → ℕ) : ℕ :=
  (2 * G.N + 1)
    + phBOps G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)
    + phDOps G (phB G (List.range G.N) 0 (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩,
        C0)).1.1 (List.range G.N) (T0, P0)

lemma buildLinOps_le (G : Dag) (B0 : RB) (C0 P0 : DL) (T0 : ℕ → ℕ) :
    buildLinOps G B0 C0 P0 T0 ≤ 7 * (buildLin G B0 C0 P0 T0).2 := by
  have h1 := phBOps_le G (List.range G.N) 0
    (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)
  have h2 := phDOps_le G (phB G (List.range G.N) 0
    (⟨B0.src, B0.dst, (clrInc (List.range G.N) B0.inc).1⟩, C0)).1.1 (List.range G.N) (T0, P0)
  have h3 := (clrInc_spec (List.range G.N) B0.inc).2.2
  rw [List.length_range] at h3
  unfold buildLinOps buildLin
  dsimp only
  omega

end Build

/-! ## 6. The run -/

section RunOps

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Strict count of the query of time `t` (if any) and of rollout `t + 1` of the linked engine
(the states are those of `LiteralG4.runSL`). -/
noncomputable def costSLOps (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α)
    (q : ℕ → Bool) (y0 : LS α) (t : ℕ) : ℕ :=
  (if q t = true then qRetireLOps K rt (runSL φ ε K rt u q y0 t).x.cnt
      (runSL φ ε K rt u q y0 t).x.s.q (runSL φ ε K rt u q y0 t).L else 0)
    + relStepLOps (pidx (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.cnt) (u (t + 1))
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.s
        (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).L

lemma costSLOps_le (φ : α → ℝ) (ε : ℝ) (K : ℕ) (rt : ℕ → ℕ) (u : ℕ → ℕ × α × α)
    (q : ℕ → Bool) (y0 : LS α) (t : ℕ) :
    costSLOps φ ε K rt u q y0 t ≤ 20 * costSL φ ε K rt u q y0 t := by
  have h1 := qRetireLOps_le φ ε K rt (runSL φ ε K rt u q y0 t).x.cnt
    (runSL φ ε K rt u q y0 t).x.s.q (runSL φ ε K rt u q y0 t).L
  have h2 := relStepLOps_le (pidx (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.cnt) (u (t + 1))
    (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).x.s (preL φ ε K rt q (runSL φ ε K rt u q y0 t) t).L
  unfold costSLOps costSL
  split_ifs <;> omega

end RunOps

/-! ## 7. Heap invariants: the resets and the construction -/

section Invariants

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Both heaps of gate `g` store exactly its children (the hypothesis of `clearHeap_spec`). -/
def RepOK (x : HRState α × Lin) (g : ℕ) : Prop :=
  (∃ k b, Rep (x.1.lo.hp g) (x.1.G.children g).toFinset k b) ∧
  (∃ k b, Rep (x.1.hi.hp g) (x.1.G.children g).toFinset k b)

/-- At a gate with `RepOK`, `clearHeap_spec` applies to both heaps (the children list is the
list read by the traversal, `AbsR.ch`). -/
lemma RepOK.clear {x : HRState α × Lin} {g : ℕ} (h : RepOK x g) :
    (clearHeap (x.1.lo.hp g) (x.1.G.children g)).pos = (Heap.empty : Heap ℕ α).pos ∧
    (clearHeap (x.1.hi.hp g) (x.1.G.children g)).pos = (Heap.empty : Heap ℕ α).pos := by
  obtain ⟨⟨k1, b1, h1⟩, ⟨k2, b2, h2⟩⟩ := h
  exact ⟨(clearHeap_spec h1).2.1, (clearHeap_spec h2).2.1⟩

lemma repOK_of_sim {x : HRState α × Lin} {s : RState α} (h : SimR x.1 s) (g : ℕ) : RepOK x g := by
  refine ⟨⟨s.lo.key g, (s.G.children g).length, ?_⟩, ⟨s.hi.key g, (s.G.children g).length, ?_⟩⟩
  · rw [h.G]; exact h.lo.hp g
  · rw [h.G]; exact h.hi.hp g

/-- Every release executed by the linked cascade happens at a gate with `RepOK`. -/
def relsOK (prot : ℕ → Bool) : ℕ → List ℕ → HRState α × Lin → Prop
  | 0, _, _ => True
  | _ + 1, [], _ => True
  | f + 1, g :: st, x =>
    if g < x.2.N ∧ x.2.C.hd g ≠ 0 ∧ x.2.P.hd g = 0 ∧ prot g = false then
      RepOK x g ∧ (relGate g st x).2.1 = x.1.G.children g ++ st ∧
        relsOK prot f (relGate g st x).2.1 (relGate g st x).1
    else relsOK prot f st x

/-- Every release executed by the final disposal happens at a gate with `RepOK`. -/
def dispOK : List ℕ → HRState α × Lin → Prop
  | [], _ => True
  | g :: gs, x => RepOK x g ∧ (relGate g [] x).2.1 = x.1.G.children g ++ [] ∧
      dispOK gs (relGate g [] x).1

lemma simR_relGate {x : HRState α × Lin} {s : RState α} (h : SimR x.1 s) (g : ℕ) (st : List ℕ) :
    SimR (relGate g st x).1.1 ⟨releaseDag s.G g, s.lo, s.hi⟩ := by
  have e : (relGate g st x).1.1 = ⟨releaseDag x.1.G g,
      ⟨x.1.lo.val, Function.update x.1.lo.hp g Heap.empty⟩,
      ⟨x.1.hi.val, Function.update x.1.hi.hp g Heap.empty⟩⟩ := rfl
  rw [e]
  exact ⟨by rw [h.G], simE_release h.lo g, simE_release h.hi g⟩

/-- **`Rep` holds at every release of a linked cascade** started from a state whose heaps
represent an abstract state (`SimR`); it is kept by each release (`simE_release`). -/
theorem relsOK_of_sim (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (x : HRState α × Lin)
    (s : RState α), SimR x.1 s → Abs x.2 x.1.G → x.1.G.WF → relsOK prot f st x := by
  intro f
  induction f with
  | zero => intro st x s _ _ _; trivial
  | succ f ih =>
    intro st x s h hA hW
    cases st with
    | nil => trivial
    | cons g st =>
      rw [relsOK]
      split_ifs with hc
      · obtain ⟨lc, lp, hr⟩ := hA
        obtain ⟨g1, -, g3, g4, -, -⟩ := relGate_spec g st x hr hW hc.1
        exact ⟨repOK_of_sim h g, g4, ih _ _ _ (simR_relGate h g st) g1 g3⟩
      · exact ih st x s h hA hW

theorem dispOK_of_sim : ∀ (gs : List ℕ) (x : HRState α × Lin) (s : RState α), SimR x.1 s →
    Abs x.2 x.1.G → x.1.G.WF → (∀ g ∈ gs, g < x.2.N) → dispOK gs x := by
  intro gs
  induction gs with
  | nil => intro _ _ _ _ _ _; trivial
  | cons g gs ih =>
    intro x s h hA hW hN
    obtain ⟨lc, lp, hr⟩ := hA
    obtain ⟨g1, g2, g3, g4, -, -⟩ := relGate_spec g [] x hr hW (hN g List.mem_cons_self)
    exact ⟨repOK_of_sim h g, g4, ih _ _ (simR_relGate h g []) g1 g3
      (fun g' hg' => by rw [g2.1]; exact hN g' (List.mem_cons_of_mem _ hg'))⟩

/-- The state with which the cascade of a rollout starts is that of `LiteralG2`'s retirement
pass on the post-wave state. -/
lemma cascIn_eq (u : ℕ × α × α) (s : GS α) (L : Lin) {lc lp : ℕ → List ℕ}
    (h : AbsR L s.q.r.G lc lp) (hG : s.q.r.G.WF) (hnd : (candG u s).Nodup) :
    (cascIn u s L).2.1 = (retireListG (candG u s) (wR u s.q.r)).1 := by
  obtain ⟨wl1, wl2, -, -⟩ := waveDL_DR h u.1 u.2.1 s.q.r.lo
  obtain ⟨wh1, wh2, -, -⟩ := waveDL_DR h u.1 u.2.2 s.q.r.hi
  obtain ⟨mg1, -, -⟩ := mergeMX_eq s.marks (waveDL L u.1 u.2.1 s.q.r.lo).2.2
    (waveDL L u.1 u.2.2 s.q.r.hi).2.2
  have hm : (mergeMX s.marks (waveDL L u.1 u.2.1 s.q.r.lo).2.2
      (waveDL L u.1 u.2.2 s.q.r.hi).2.2).1 = (mergeG u s).1 := by
    rw [mg1, wl2, wh2]; rfl
  obtain ⟨-, c2, c3, -, -⟩ := candTrav_spec h (mergeG u s).1
  have hcand : (candTrav L (mergeG u s).1).1.map (pr L) = candG u s := c2
  have hnd' : (candTrav L (mergeG u s).1).1.Nodup := by rw [← hcand] at hnd; exact hnd.of_map _
  have hw : (⟨s.q.r.G, (waveDL L u.1 u.2.1 s.q.r.lo).1,
      (waveDL L u.1 u.2.2 s.q.r.hi).1⟩ : HRState α) = wR u s.q.r := by
    rw [wl1, wh1]; rfl
  unfold cascIn
  rw [hm]
  obtain ⟨r1, -, -, -, -⟩ := retireListL_spec (candTrav L (mergeG u s).1).1
    (⟨s.q.r.G, (waveDL L u.1 u.2.1 s.q.r.lo).1, (waveDL L u.1 u.2.2 s.q.r.hi).1⟩, L) lc lp
    (by exact h) hG hnd' c3
  simp only at r1
  rw [r1, hcand, hw]

/-- The executed position writes of `ofKeys`: `pos c := some i` for the `i`-th child `c`. -/
def writePos {ι : Type*} [DecidableEq ι] : List ι → ℕ → (ι → Option ℕ) → (ι → Option ℕ)
  | [], _, P => P
  | c :: cs, i, P => writePos cs (i + 1) (Function.update P c (some i))

lemma writePos_eq {ι : Type*} [DecidableEq ι] : ∀ (cs : List ι) (i : ℕ) (P : ι → Option ℕ),
    cs.Nodup → writePos cs i P = fun h => if h ∈ cs then some (i + cs.idxOf h) else P h := by
  intro cs
  induction cs with
  | nil => intro i P _; funext h; simp [writePos]
  | cons c cs ih =>
    intro i P hnd
    obtain ⟨hc, hnd'⟩ := List.nodup_cons.1 hnd
    rw [writePos, ih (i + 1) _ hnd']
    funext h
    by_cases hh : h = c
    · subst hh
      simp [hc, Function.update_self]
    · have hm : (h ∈ c :: cs) ↔ h ∈ cs := by simp [hh]
      by_cases hin : h ∈ cs
      · rw [if_pos hin, if_pos (hm.2 hin), List.idxOf_cons_ne _ (Ne.symm hh)]
        congr 1; omega
      · rw [if_neg hin, if_neg (fun h' => hin (hm.1 h')), Function.update_of_ne hh]

/-- **The executed position writes of `ofKeys` give its position array** on a heap whose
position array is that of `Heap.empty` (children without repetition). -/
theorem ofKeys_pos_exec {ι : Type*} [DecidableEq ι] [Inhabited ι] (cs : List ι) (k : ι → α)
    (H : Heap ι α) (hH : H.pos = (Heap.empty : Heap ι α).pos) (hnd : cs.Nodup) :
    writePos cs 0 H.pos = (HeapB.ofKeys cs k).pos := by
  rw [writePos_eq cs 0 H.pos hnd, hH]
  funext h
  show _ = if h ∈ cs then some (cs.idxOf h) else none
  simp only [Nat.zero_add]
  rfl

/-- Each gate of the initialisation pass finds its heap with the position array of
`Heap.empty` when it is initialised. -/
def initOK (G : Dag) : List ℕ → HEState α → Prop
  | [], _ => True
  | g :: rest, s => (s.hp g).pos = (Heap.empty : Heap ℕ α).pos ∧ initOK G rest (initGateBX G g s).1

lemma initOK_of (G : Dag) : ∀ (l : List ℕ) (s : HEState α), l.Nodup →
    (∀ g ∈ l, (s.hp g).pos = (Heap.empty : Heap ℕ α).pos) → initOK G l s := by
  intro l
  induction l with
  | nil => intro _ _ _; trivial
  | cons g l ih =>
    intro s hnd h
    obtain ⟨hg, hnd'⟩ := List.nodup_cons.1 hnd
    refine ⟨h g List.mem_cons_self, ih _ hnd' (fun g' hg' => ?_)⟩
    have hne : g' ≠ g := fun e => hg (e ▸ hg')
    show (Function.update s.hp g (heapifyX (G.children g) s.val).1 g').pos = _
    rw [Function.update_of_ne hne]
    exact h g' (List.mem_cons_of_mem _ hg')

end Invariants

/-! ### Frame: the heap operations read only the live cells -/

section Frame

variable {ι β : Type*} [DecidableEq ι] [LinearOrder β]

/-- Two heaps agree on the cells an operation may read: the size, the handle and key cells
below the size, and the position cells of the handles in `A`. -/
def HAgree (A : ι → Prop) (H H' : Heap ι β) : Prop :=
  H.n = H'.n ∧ (∀ i, i < H.n → H.hd i = H'.hd i ∧ H.ky i = H'.ky i) ∧
    ∀ h, A h → H.pos h = H'.pos h

lemma HAgree.swap {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') {a b : ℕ}
    (ha : a < H.n) (hb : b < H.n) : HAgree A (H.swap a b) (H'.swap a b) := by
  have ha' := h.2.1 a ha
  have hb' := h.2.1 b hb
  refine ⟨h.1, fun i hi => ?_, fun x hx => ?_⟩
  · have hi' := h.2.1 i hi
    constructor
    · show (if i = a then H.hd b else if i = b then H.hd a else H.hd i)
        = (if i = a then H'.hd b else if i = b then H'.hd a else H'.hd i)
      rw [ha'.1, hb'.1, hi'.1]
    · show (if i = a then H.ky b else if i = b then H.ky a else H.ky i)
        = (if i = a then H'.ky b else if i = b then H'.ky a else H'.ky i)
      rw [ha'.2, hb'.2, hi'.2]
  · show (if x = H.hd a then some b else if x = H.hd b then some a else H.pos x)
      = (if x = H'.hd a then some b else if x = H'.hd b then some a else H'.pos x)
    rw [ha'.1, hb'.1, h.2.2 x hx]

/-- **Sift up reads no position cell** and only key cells below the size. -/
lemma siftUp_agree {A : ι → Prop} : ∀ (d : ℕ) (H H' : Heap ι β) (j : ℕ), j < H.n →
    HAgree A H H' →
    HAgree A (HeapImpl.siftUp d H j).1 (HeapImpl.siftUp d H' j).1 ∧
      (HeapImpl.siftUp d H j).2 = (HeapImpl.siftUp d H' j).2 := by
  intro d
  induction d with
  | zero => intro H H' j _ h; rw [HeapImpl.siftUp, HeapImpl.siftUp]; exact ⟨h, rfl⟩
  | succ d ih =>
    intro H H' j hj h
    rw [HeapImpl.siftUp, HeapImpl.siftUp]
    by_cases hc : 0 < j ∧ H.ky (HeapImpl.par j) < H.ky j
    · have hpn : HeapImpl.par j < H.n := lt_trans (HeapImpl.par_lt hc.1) hj
      have hc' : 0 < j ∧ H'.ky (HeapImpl.par j) < H'.ky j :=
        ⟨hc.1, by rw [← (h.2.1 _ hpn).2, ← (h.2.1 _ hj).2]; exact hc.2⟩
      rw [if_pos hc, if_pos hc']
      obtain ⟨i1, i2⟩ := ih (H.swap j (HeapImpl.par j)) (H'.swap j (HeapImpl.par j)) (HeapImpl.par j) hpn (h.swap hj hpn)
      exact ⟨i1, by dsimp only; rw [i2]⟩
    · have hc' : ¬ (0 < j ∧ H'.ky (HeapImpl.par j) < H'.ky j) := fun hc' => hc ⟨hc'.1, by
        have hpn := lt_trans (HeapImpl.par_lt hc'.1) hj
        rw [(h.2.1 _ hpn).2, (h.2.1 _ hj).2]; exact hc'.2⟩
      rw [if_neg hc, if_neg hc']; exact ⟨h, rfl⟩

lemma bigChild_agree {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') (j : ℕ) :
    HeapImpl.bigChild H j = HeapImpl.bigChild H' j := by
  unfold HeapImpl.bigChild
  by_cases hc : 2 * j + 2 < H.n
  · rw [(h.2.1 (2 * j + 1) (by omega)).2, (h.2.1 (2 * j + 2) hc).2, h.1]
  · have hc' : ¬ 2 * j + 2 < H'.n := by rw [← h.1]; exact hc
    rw [if_neg (fun h' => hc h'.1), if_neg (fun h' => hc' h'.1)]

/-- **Sift down reads no position cell** and only key cells below the size. -/
lemma siftDown_agree {A : ι → Prop} : ∀ (d : ℕ) (H H' : Heap ι β) (j : ℕ), HAgree A H H' →
    HAgree A (HeapImpl.siftDown d H j).1 (HeapImpl.siftDown d H' j).1 ∧
      (HeapImpl.siftDown d H j).2 = (HeapImpl.siftDown d H' j).2 := by
  intro d
  induction d with
  | zero => intro H H' j h; rw [HeapImpl.siftDown, HeapImpl.siftDown]; exact ⟨h, rfl⟩
  | succ d ih =>
    intro H H' j h
    have hb := bigChild_agree h j
    rw [HeapImpl.siftDown, HeapImpl.siftDown]
    by_cases hc : 2 * j + 1 < H.n ∧ H.ky j < H.ky (HeapImpl.bigChild H j)
    · have hbn := (HeapImpl.bigChild_spec H j hc.1).2.1
      have hjn : j < H.n := by omega
      have hc' : 2 * j + 1 < H'.n ∧ H'.ky j < H'.ky (HeapImpl.bigChild H' j) :=
        ⟨by rw [← h.1]; exact hc.1,
         by rw [← hb, ← (h.2.1 _ hjn).2, ← (h.2.1 _ hbn).2]; exact hc.2⟩
      rw [if_pos hc, if_pos hc', ← hb]
      obtain ⟨i1, i2⟩ := ih (H.swap j (HeapImpl.bigChild H j)) (H'.swap j (HeapImpl.bigChild H j)) (HeapImpl.bigChild H j) (h.swap hjn hbn)
      exact ⟨i1, by dsimp only; rw [i2]⟩
    · have hc' : ¬ (2 * j + 1 < H'.n ∧ H'.ky j < H'.ky (HeapImpl.bigChild H' j)) := by
        intro hc'
        have hbn := (HeapImpl.bigChild_spec H' j hc'.1).2.1
        have hjn : j < H.n := by rw [h.1]; omega
        apply hc
        refine ⟨by rw [h.1]; exact hc'.1, ?_⟩
        rw [hb, (h.2.1 _ hjn).2, (h.2.1 _ (by rw [h.1]; exact hbn)).2]; exact hc'.2
      rw [if_neg hc, if_neg hc']; exact ⟨h, rfl⟩

lemma HAgree.setKey {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') (i : ℕ) (x : β) :
    HAgree A (H.setKey i x) (H'.setKey i x) := by
  refine ⟨h.1, fun k hk => ⟨(h.2.1 k hk).1, ?_⟩, h.2.2⟩
  show Function.update H.ky i x k = Function.update H'.ky i x k
  by_cases e : k = i
  · subst e; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne e, Function.update_of_ne e]; exact (h.2.1 k hk).2

lemma updateAt_agree {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') {i : ℕ}
    (hi : i < H.n) (x : β) :
    HAgree A (HeapImpl.updateAt H i x).1 (HeapImpl.updateAt H' i x).1 ∧
      (HeapImpl.updateAt H i x).2 = (HeapImpl.updateAt H' i x).2 := by
  unfold HeapImpl.updateAt
  rw [← h.1, ← (h.2.1 i hi).2]
  have hs := h.setKey i x
  by_cases hc : H.ky i ≤ x
  · rw [if_pos hc, if_pos hc]
    obtain ⟨i1, i2⟩ := siftUp_agree (Nat.clog 2 H.n) (H.setKey i x) (H'.setKey i x) i hi hs
    exact ⟨i1, by dsimp only; rw [i2]⟩
  · rw [if_neg hc, if_neg hc]
    obtain ⟨i1, i2⟩ := siftDown_agree (Nat.clog 2 H.n) (H.setKey i x) (H'.setKey i x) i hs
    exact ⟨i1, by dsimp only; rw [i2]⟩

/-- **update-key reads the position array only at its handle.** -/
theorem updateKey_agree {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') {c : ι}
    (hA : A c) (hP : ∀ i, H.pos c = some i → i < H.n) (x : β) :
    HAgree A (updateKey H c x).1 (updateKey H' c x).1 ∧
      (updateKey H c x).2 = (updateKey H' c x).2 := by
  unfold updateKey
  rw [← h.2.2 c hA]
  cases hp : H.pos c with
  | none => exact ⟨h, rfl⟩
  | some i => exact updateAt_agree h (hP i hp) x

lemma HAgree.moveLast {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') (c : ι) {i : ℕ}
    (hi : i < H.n) : HAgree A (H.moveLast c i) (H'.moveLast c i) := by
  have hl := h.2.1 (H.n - 1) (by omega)
  refine ⟨by show H.n - 1 = H'.n - 1; rw [h.1], fun k hk => ?_, fun x hx => ?_⟩
  · have hk' : k < H.n := by have : k < H.n - 1 := hk; omega
    constructor
    · show Function.update H.hd i (H.hd (H.n - 1)) k = Function.update H'.hd i (H'.hd (H'.n - 1)) k
      rw [← h.1, ← hl.1]
      by_cases e : k = i
      · subst e; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne e, Function.update_of_ne e]; exact (h.2.1 k hk').1
    · show Function.update H.ky i (H.ky (H.n - 1)) k = Function.update H'.ky i (H'.ky (H'.n - 1)) k
      rw [← h.1, ← hl.2]
      by_cases e : k = i
      · subst e; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne e, Function.update_of_ne e]; exact (h.2.1 k hk').2
  · show (if x = c then none else if x = H.hd (H.n - 1) then some i else H.pos x)
      = (if x = c then none else if x = H'.hd (H'.n - 1) then some i else H'.pos x)
    rw [← h.1, ← hl.1, h.2.2 x hx]

lemma HAgree.dropLast {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') (c : ι) :
    HAgree A (H.dropLast c) (H'.dropLast c) := by
  refine ⟨by show H.n - 1 = H'.n - 1; rw [h.1], fun k hk => h.2.1 k (by
    have : k < H.n - 1 := hk; omega), fun x hx => ?_⟩
  show Function.update H.pos c none x = Function.update H'.pos c none x
  by_cases e : x = c
  · subst e; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne e, Function.update_of_ne e]; exact h.2.2 x hx

lemma deleteAt_agree {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') (c : ι) {i : ℕ}
    (hi : i < H.n) :
    HAgree A (HeapImpl.deleteAt H c i).1 (HeapImpl.deleteAt H' c i).1 ∧
      (HeapImpl.deleteAt H c i).2 = (HeapImpl.deleteAt H' c i).2 := by
  have hl := h.2.1 (H.n - 1) (by omega)
  unfold HeapImpl.deleteAt
  rw [← h.1, ← hl.2, ← (h.2.1 i hi).2]
  by_cases e : i = H.n - 1
  · rw [if_pos e, if_pos e]; exact ⟨h.dropLast c, rfl⟩
  · rw [if_neg e, if_neg e]
    have hm := h.moveLast c hi
    have hi' : i < (H.moveLast c i).n := by show i < H.n - 1; omega
    by_cases hc : H.ky i ≤ H.ky (H.n - 1)
    · rw [if_pos hc, if_pos hc]
      obtain ⟨i1, i2⟩ := siftUp_agree (Nat.clog 2 H.n) (H.moveLast c i) (H'.moveLast c i) i hi' hm
      exact ⟨i1, by dsimp only; rw [i2]⟩
    · rw [if_neg hc, if_neg hc]
      obtain ⟨i1, i2⟩ := siftDown_agree (Nat.clog 2 H.n) (H.moveLast c i) (H'.moveLast c i) i hm
      exact ⟨i1, by dsimp only; rw [i2]⟩

/-- **delete reads the position array only at its handle.** -/
theorem delete_agree {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') {c : ι}
    (hA : A c) (hP : ∀ i, H.pos c = some i → i < H.n) :
    HAgree A (HeapImpl.delete H c).1 (HeapImpl.delete H' c).1 ∧
      (HeapImpl.delete H c).2 = (HeapImpl.delete H' c).2 := by
  unfold HeapImpl.delete
  rw [← h.2.2 c hA]
  cases hp : H.pos c with
  | none => exact ⟨h, rfl⟩
  | some i => exact deleteAt_agree h c (hP i hp)

/-- **find-max reads no position cell.** -/
theorem findMax_agree [OrderBot β] {A : ι → Prop} {H H' : Heap ι β} (h : HAgree A H H') :
    findMax H = findMax H' := by
  unfold findMax
  rw [← h.1]
  by_cases e : H.n = 0
  · rw [if_pos e, if_pos e]
  · rw [if_neg e, if_neg e, (h.2.1 0 (by omega)).2]

/-- The bottom-up loop of `heapify` reads no position cell. -/
lemma heapLoopX_agree {A : ι → Prop} : ∀ (j : ℕ) (H H' : Heap ι β), HAgree A H H' →
    HAgree A (heapLoopX j H).1 (heapLoopX j H').1 ∧ (heapLoopX j H).2 = (heapLoopX j H').2 := by
  intro j
  induction j with
  | zero => intro H H' h; exact ⟨h, rfl⟩
  | succ j ih =>
    intro H H' h
    rw [heapLoopX, heapLoopX, ← h.1]
    obtain ⟨s1, s2⟩ := siftDown_agree (Nat.clog 2 H.n) H H' j h
    obtain ⟨i1, i2⟩ := ih _ _ s1
    exact ⟨i1, by dsimp only; rw [s2, i2]⟩

variable [Inhabited ι]

/-- **The executed construction of `ofKeys` on arbitrary heap memory** `Hm`: the handle and
key cells below the size and the positions of the children are written; every other cell
keeps its arbitrary content. -/
def ofKeysExec (Hm : Heap ι β) (cs : List ι) (k : ι → β) : Heap ι β :=
  ⟨cs.length, fun i => if i < cs.length then cs.getD i default else Hm.hd i,
    fun i => if i < cs.length then k (cs.getD i default) else Hm.ky i, writePos cs 0 Hm.pos⟩

/-- **Arbitrary initial heap memory**: the executed construction agrees with `ofKeys` on every
cell an operation may read for the children (`HAgree`), and so does the heap after the
bottom-up loop of `heapify` (same cost). -/
theorem ofKeysExec_agree (Hm : Heap ι β) (cs : List ι) (k : ι → β) (hnd : cs.Nodup) :
    HAgree (· ∈ cs) (HeapB.ofKeys cs k) (ofKeysExec Hm cs k) ∧
    HAgree (· ∈ cs) (heapLoopX cs.length (HeapB.ofKeys cs k)).1
      (heapLoopX cs.length (ofKeysExec Hm cs k)).1 ∧
    (heapLoopX cs.length (HeapB.ofKeys cs k)).2 = (heapLoopX cs.length (ofKeysExec Hm cs k)).2 := by
  have h : HAgree (· ∈ cs) (HeapB.ofKeys cs k) (ofKeysExec Hm cs k) := by
    refine ⟨rfl, fun i hi => ?_, fun x hx => ?_⟩
    · have hi' : i < cs.length := hi
      exact ⟨by show _ = if i < cs.length then _ else _; rw [if_pos hi']; rfl,
        by show _ = if i < cs.length then _ else _; rw [if_pos hi']; rfl⟩
    · show (if x ∈ cs then some (cs.idxOf x) else none) = writePos cs 0 Hm.pos x
      rw [writePos_eq cs 0 Hm.pos hnd]
      dsimp only
      rw [if_pos hx, if_pos hx, Nat.zero_add]
  exact ⟨h, heapLoopX_agree _ _ _ h⟩

end Frame

/-- **The cleared heap of a released gate agrees with `Heap.empty` on every cell an operation
may read** (`HAgree` for any handle set), when the heap stored exactly the children. -/
theorem clearHeap_agree {α : Type*} [LinearOrder α] [OrderBot α] {H : Heap ℕ α} {cs : List ℕ}
    {k : ℕ → α} {b : ℕ} (h : Rep H cs.toFinset k b) (A : ℕ → Prop) :
    HAgree A (Heap.empty : Heap ℕ α) (clearHeap H cs) :=
  ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i),
    fun x _ => by rw [(clearHeap_spec h).2.1]⟩

section Final

variable {α : Type*} [LinearOrder α] [OrderBot α]
variable (R : SelRun α) (μ : Mem) (φ : α → ℝ) (ε : ℝ)

/-- Strict count of the two heap initialisation passes. -/
def WinitLS : ℕ := initPassBXOps R.G0 R.order R.hl + initPassBXOps R.G0 R.order R.hu

/-- Strict count of the mark table pass (`clearMarksX` over `0, …, N-1`: loop test and write
per gate, exit test). -/
def WmarkLS : ℕ := 2 * R.G0.N + 1

/-- Strict count of the count table passes: zeroing (`2 N + 1`) and the `K` root increments
(loop test, read `rt i`, read and write the count: `4 K + 1`). -/
def WcntLS : ℕ := (2 * R.G0.N + 1) + (4 * R.K + 1)

/-- Strict count of the initialisation of the `K` activity flags (loop test and write per
root index, exit test). -/
def WflagLS : ℕ := 2 * R.K + 1

/-- Strict count of the construction of the incidence structure. -/
def WbuildLS : ℕ := buildLinOps R.G0 μ.B0 μ.C0 μ.P0 μ.T0

/-- Strict count of the `τ` rollouts and the queries at times `t < τ`. -/
noncomputable def WrollLS : ℕ :=
  ∑ t ∈ range R.τ, costSLOps φ ε R.K R.rt R.u R.q (y0 R μ.m0 μ.c0 (L0 R μ)) t

/-- Strict count of the query at the stopping time. -/
noncomputable def WlastLS : ℕ := if R.q R.τ = true then
    qRetireLOps R.K R.rt (runL R μ φ ε R.τ).x.cnt (runL R μ φ ε R.τ).x.s.q (runL R μ φ ε R.τ).L
  else 0

/-- Strict count of the final disposal. -/
noncomputable def WdispLS : ℕ :=
  disposeLOps (List.range R.G0.N) ((preLt R μ φ ε R.τ).x.s.q.r, (preLt R μ φ ε R.τ).L)

/-- **`P_G`, strict**: the executed cost of the upfront passes of the direct engine (heap
initialisation, mark table, count table, incidence structure), every primitive one unit. -/
def PGS : ℕ := WinitLS R + WmarkLS R + WcntLS R + WflagLS R + WbuildLS R μ

/-- **Total work of the linked engine, strict accounting**: the shared work `R.H` (an input),
the executed upfront passes `PGS`, and the strict counts of all rollouts, queries and the
disposal.  No given `P` is added. -/
noncomputable def WLS : ℕ := R.H + PGS R μ + WrollLS R μ φ ε + WlastLS R μ φ ε + WdispLS R μ φ ε

/-- **`P_G`, accounting of `LiteralG4`**: the executed cost of the same upfront passes. -/
def PG : ℕ := WinitL R + WmarkL R μ.m0 + WcntL R μ.c0 + (buildLin R.G0 μ.B0 μ.C0 μ.P0 μ.T0).2

/-- The total work `LiteralG4.WL` without the given `R.P`. -/
noncomputable def WLnoP : ℕ := R.H + PG R μ + WrollL R μ.m0 μ.c0 φ ε (L0 R μ)
  + WlastL R μ.m0 μ.c0 φ ε (L0 R μ) + WdispL R μ.m0 μ.c0 φ ε (L0 R μ)

/-- `XD` with `P = 0`: `H + n + e + (S^+ + e)(⌈log₂ D⌉ + 1)` (with `Hsh = H + τ + Q K`). -/
noncomputable def XD0 : ℕ :=
  Hsh R + R.G0.N + live R.G0 + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)

/-- The right side of `eq:prop-rep-upper` with `P_R := PG` (computed). -/
noncomputable def XG : ℕ :=
  Hsh R + PG R μ + R.G0.N + live R.G0 + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)

/-- The right side of `eq:prop-rep-upper` with `P_R := PGS` (computed, strict). -/
noncomputable def XGS : ℕ :=
  Hsh R + PGS R μ + R.G0.N + live R.G0 + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)

/-- The run with `P = 0` (all other data unchanged). -/
def R0 : SelRun α := { R with P := 0 }

variable {R}

lemma WL_eq : WL R μ φ ε = R.P + WLnoP R μ φ ε := by
  unfold WL WLnoP PG; omega

lemma WL_R0 : WL (R0 R) μ φ ε = WLnoP R μ φ ε := by
  have h : WL (R0 R) μ φ ε = 0 + R.H + WinitL R + WmarkL R μ.m0 + WcntL R μ.c0
      + (buildLin R.G0 μ.B0 μ.C0 μ.P0 μ.T0).2 + WrollL R μ.m0 μ.c0 φ ε (L0 R μ)
      + WlastL R μ.m0 μ.c0 φ ε (L0 R μ) + WdispL R μ.m0 μ.c0 φ ε (L0 R μ) := rfl
  rw [h]; unfold WLnoP PG; omega

lemma XD_R0 : XD (R0 R) = XD0 R := by
  have h : XD (R0 R) = Hsh R + 0 + R.G0.N + live R.G0
      + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1) := rfl
  rw [h]; unfold XD0; omega

/-- **Total work without the given `P`**: `WL − R.P ≤ 303 · XD0`. -/
theorem WLnoP_le (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    WLnoP R μ φ ε ≤ 303 * XD0 R := by
  rw [← WL_R0, ← XD_R0]
  exact WL_le_inj (R := R0 R) μ φ ε hcl hlt hinj

/-- **`P_G ≤ 27 (n + e)`** (accounting of `LiteralG4`). -/
theorem PG_le (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    PG R μ ≤ 27 * (R.G0.N + live R.G0) := by
  obtain ⟨-, -, -, l4⟩ := L0_spec μ hcl
  have hi : WinitL R = WinitB R + 2 * R.order.length + 2 := by
    unfold WinitL WinitB; rw [initPassBX_eq, initPassBX_eq]; ring
  have hb := (initB_facts R).2
  have ho := R.order_length_le
  obtain ⟨-, m2, -, c2⟩ := initX_eq R μ.m0 μ.c0
  have hK := K_le_N R hlt hinj
  have hN : 1 ≤ R.G0.N := by have := (R.hn 0).1; omega
  unfold PG WmarkL WcntL
  omega

/-- **Strict `P_G` against `P_G`**: `PGS ≤ 23 · PG`. -/
theorem PGS_le_PG : PGS R μ ≤ 23 * PG R μ := by
  have h1 := initPassBXOps_le R.G0 R.order R.hl
  have h2 := initPassBXOps_le R.G0 R.order R.hu
  have h3 := buildLinOps_le R.G0 μ.B0 μ.C0 μ.P0 μ.T0
  obtain ⟨-, m2, -, c2⟩ := initX_eq R μ.m0 μ.c0
  unfold PGS PG WinitLS WinitL WmarkLS WcntLS WflagLS WbuildLS WmarkL WcntL
  omega

/-- **Strict `P_G ≤ 621 (n + e)`**. -/
theorem PGS_le (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    PGS R μ ≤ 621 * (R.G0.N + live R.G0) := by
  have h1 := PGS_le_PG (R := R) μ
  have h2 := PG_le μ hcl hlt hinj
  omega

/-- **Strict total work against the accounting of `LiteralG4`**: `WLS ≤ 23 · (WL − R.P)`
(no hypothesis). -/
theorem WLS_le : WLS R μ φ ε ≤ 23 * WLnoP R μ φ ε := by
  have hP := PGS_le_PG (R := R) μ
  have hr : WrollLS R μ φ ε ≤ 20 * WrollL R μ.m0 μ.c0 φ ε (L0 R μ) := by
    unfold WrollLS WrollL
    rw [mul_sum]
    exact sum_le_sum (fun t _ => costSLOps_le φ ε R.K R.rt R.u R.q _ t)
  have hl : WlastLS R μ φ ε ≤ 5 * WlastL R μ.m0 μ.c0 φ ε (L0 R μ) := by
    unfold WlastLS WlastL runL
    split_ifs
    · exact qRetireLOps_le φ ε R.K R.rt _ _ _
    · omega
  have hd : WdispLS R μ φ ε ≤ 3 * WdispL R μ.m0 μ.c0 φ ε (L0 R μ) := by
    unfold WdispLS WdispL preLt
    exact disposeLOps_le _ _
  unfold WLS WLnoP
  omega

lemma XD0_le_XGS : XD0 R ≤ XGS R μ := by unfold XD0 XGS; omega

lemma XD0_le_XG : XD0 R ≤ XG R μ := by unfold XD0 XG; omega

/-- **`WLS ≤ 6969 · XD0`**. -/
theorem WLS_le_XD0 (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    WLS R μ φ ε ≤ 6969 * XD0 R := by
  have h1 := WLS_le (R := R) μ φ ε
  have h2 := WLnoP_le μ φ ε hcl hlt hinj
  omega

theorem XGS_le (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    XGS R μ ≤ 622 * XD0 R := by
  have h := PGS_le μ hcl hlt hinj
  unfold XGS XD0
  omega

theorem XG_le (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    XG R μ ≤ 28 * XD0 R := by
  have h := PG_le μ hcl hlt hinj
  unfold XG XD0
  omega

/-- `SimR` of the post-wave state of rollout `t + 1` (`LiteralF4.wR1`). -/
lemma simR_wR1 (t : ℕ) : SimR (wR1 R t) (waveStep (R.u (t + 1)) (R.pre t).r).1 := by
  have hP := (simR_all R t).2
  have hinv := R.pre_inv t
  have hG : (hpreR R t).r.G = (R.pre t).r.G := hP.r.G
  have hxs : (R.u (t + 1)).1 < (R.pre t).r.G.N := by rw [hinv.nEq]; exact (R.hn t).1
  obtain ⟨l1, -, -⟩ := waveD_spec hinv.wf (R.u (t + 1)).1 (R.u (t + 1)).2.1 (hpreR R t).r.lo
    (R.pre t).r.lo hxs hP.r.lo hinv.invLo
  obtain ⟨u1, -, -⟩ := waveD_spec hinv.wf (R.u (t + 1)).1 (R.u (t + 1)).2.2 (hpreR R t).r.hi
    (R.pre t).r.hi hxs hP.r.hi hinv.invHi
  refine ⟨hG, ?_, ?_⟩
  · show SimE (R.pre t).r.G (waveDR (hpreR R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1
      (hpreR R t).r.lo).1 (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1
    rw [(waveDR_eq _ _ _ _).1, hG]; exact l1
  · show SimE (R.pre t).r.G (waveDR (hpreR R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2
      (hpreR R t).r.hi).1 (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1
    rw [(waveDR_eq _ _ _ _).1, hG]; exact u1

/-- The state with which the cascade of rollout `t + 1` of the linked engine starts
represents an abstract state (`SimR`): it is `retireListH` of the candidates on the post-wave
state (`LiteralG2.stepG`), and `EngineFinal.retireListH_sim`. -/
theorem casc_sim (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N) (t : ℕ) :
    ∃ s : RState α,
      SimR (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2.1 s ∧
      Abs (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2.2
        (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2.1.G ∧
      (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2.1.G.WF := by
  obtain ⟨l1, -, -, -⟩ := L0_spec μ hcl
  have hL : Abs (L0 R μ) R.G0 := ⟨_, _, l1⟩
  obtain ⟨i1, i2, -⟩ := simL_all (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL t
  obtain ⟨p1, ⟨lc, lp, hr⟩, -⟩ := hpreL_eq t ⟨i1, i2⟩
  have hs : (hpreP R μ.m0 μ.c0 t).s = hpreG R μ.m0 t := (stepP R μ.m0 μ.c0 t).1
  obtain ⟨g1, -, g3, g4, -, g6, -⟩ := stepG R μ.m0 t
  have hwf : (hpreP R μ.m0 μ.c0 t).s.q.r.G.WF := by rw [hs]; exact hpreG_wf R μ.m0 t
  have hnd : (candG (R.u (t + 1)) (hpreP R μ.m0 μ.c0 t).s).Nodup := by rw [hs, g3]; exact g4
  rw [← p1] at hr hwf hnd
  have e := cascIn_eq (R.u (t + 1)) _ _ hr hwf hnd
  have cs := cascIn_spec (R.u (t + 1)) _ _ hr hwf hnd
  have hsim : ∃ s : RState α, SimR (cascIn (R.u (t + 1)) (hpreL R μ.m0 μ.c0 φ ε (L0 R μ) t).x.s
      (hpreL R μ.m0 μ.c0 φ ε (L0 R μ) t).L).2.1 s := by
    rw [e, p1, hs, g3]
    have hw : wR (R.u (t + 1)) (hpreG R μ.m0 t).q.r = wR1 R t := by unfold wR1; rw [g1]
    rw [hw, g6]
    exact ⟨_, (retireListH_sim (candRt R t) (simR_wR1 (R := R) t)).1⟩
  obtain ⟨s0, hs0⟩ := hsim
  exact ⟨s0, hs0, cs.1, cs.2⟩

/-- **Heap invariants along the run.**  (a) Every release executed by the cascade of every
rollout (`relStepL_casc`), by every cascade started at a query state (any protection, fuel
and stack, in particular that of `qRetireL`), and by the disposal from any pre-wave state,
happens at a gate whose two heaps store exactly its children (`relsOK`, `dispOK`; so
`clearHeap_spec` / `RepOK.clear` apply).  (b) Each gate of `order` finds its heap with the
position array of `Heap.empty` when it is initialised (`initOK`, from `SelRun.empty_lo/hi`
and `order_nodup`), and on such a heap the executed position writes of `ofKeys` give its
position array (`ofKeys_pos_exec`, children without repetition). -/
theorem heap_invariants_run (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N) :
    (∀ t, relsOK (pidx (preLt R μ φ ε t).x.cnt)
      (relFuel (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2.1.G
        (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).1)
      (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).1
      (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2) ∧
    (∀ t (prot : ℕ → Bool) (f : ℕ) (st : List ℕ),
      relsOK prot f st ((runL R μ φ ε t).x.s.q.r, (runL R μ φ ε t).L)) ∧
    (∀ t (gs : List ℕ), (∀ g ∈ gs, g < R.G0.N) →
      dispOK gs ((preLt R μ φ ε t).x.s.q.r, (preLt R μ φ ε t).L)) ∧
    initOK R.G0 R.order R.hl ∧ initOK R.G0 R.order R.hu ∧
    (∀ (s : HEState α) (g : ℕ), (s.hp g).pos = (Heap.empty : Heap ℕ α).pos →
      writePos (R.G0.children g) 0 (s.hp g).pos = (HeapB.ofKeys (R.G0.children g) s.val).pos) := by
  have hU := (representation_cost_upper_Lin μ φ ε hcl).2.1
  obtain ⟨l1, l2, -, -⟩ := L0_spec μ hcl
  have hL : Abs (L0 R μ) R.G0 := ⟨_, _, l1⟩
  refine ⟨fun t => ?_, fun t prot f st => ?_, fun t gs hgs => ?_, ?_, ?_, fun s g hs => ?_⟩
  · obtain ⟨s, hs, hA, hW⟩ := casc_sim μ φ ε hcl t
    exact relsOK_of_sim _ _ _ _ s hs hA hW
  · obtain ⟨i1, i2, -⟩ := simL_all (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL t
    have hwf : (hrunP R μ.m0 μ.c0 t).s.q.r.G.WF := by
      rw [(simP_all R μ.m0 μ.c0 t).1]; exact hrunG_wf R μ.m0 t
    rw [← i1] at i2 hwf
    exact relsOK_of_sim prot f st _ _ (hU t).2.2.2.2.1.r i2 hwf
  · obtain ⟨i1, i2, i3⟩ := simL_all (m0 := μ.m0) (c0 := μ.c0) (φ := φ) (ε := ε) hL t
    obtain ⟨p1, p2, p3⟩ := hpreL_eq t ⟨i1, i2⟩
    have hwf : (hpreP R μ.m0 μ.c0 t).s.q.r.G.WF := by
      rw [(stepP R μ.m0 μ.c0 t).1]; exact hpreG_wf R μ.m0 t
    rw [← p1] at p2 hwf
    have hNL : (hpreL R μ.m0 μ.c0 φ ε (L0 R μ) t).L.N = R.G0.N := by rw [p3.1, i3.1, l2]
    exact dispOK_of_sim gs _ _ (hU t).2.2.2.2.2.1.r p2 hwf (fun g hg => by
      show g < (hpreL R μ.m0 μ.c0 φ ε (L0 R μ) t).L.N
      rw [hNL]; exact hgs g hg)
  · exact initOK_of R.G0 R.order R.hl R.order_nodup (fun g _ => by rw [R.empty_lo g])
  · exact initOK_of R.G0 R.order R.hu R.order_nodup (fun g _ => by rw [R.empty_hi g])
  · exact ofKeys_pos_exec _ _ _ hs (R.nodup g)

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, strict accounting and
`P_G` computed**, for the linked engine of `LiteralG4` (same executed program and states;
hypotheses: the fields of the run `R`, children of `G0` are gates, the root actions are
distinct gates `< N`; any stop rule, any initial memory `μ`):

1. `WL = R.P + WLnoP` and `WLnoP ≤ 303 · XD0`: the total work of `LiteralG4` without the
   given `P`, which contains the executed upfront passes `PG`, is `O(H + n + e + (S^+ + e)
   (⌈log₂ D⌉ + 1))`;
2. `PG ≤ 27 (n + e)` and the strict `PGS ≤ 23 · PG ≤ 621 (n + e)`;
3. `WLS ≤ 23 · WLnoP ≤ 6969 · XD0`: the strict total work;
4. with `P_R := PGS` (resp. `PG`) in the right side, `XD0 ≤ XGS ≤ 622 · XD0`,
   `XD0 ≤ XG ≤ 28 · XD0`, `WLS ≤ 6969 · XGS` and `WLnoP ≤ 303 · XG`;
0. (first conjunct) the heap invariants of the strict count along the run:
   `heap_invariants_run`. -/
theorem representation_cost_upper_strict (hcl : ∀ p c, c ∈ R.G0.children p → c < R.G0.N)
    (hlt : ∀ i, i < R.K → R.rt i < R.G0.N)
    (hinj : ∀ i, i < R.K → ∀ j, j < R.K → R.rt i = R.rt j → i = j) :
    ((∀ t, relsOK (pidx (preLt R μ φ ε t).x.cnt)
      (relFuel (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2.1.G
        (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).1)
      (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).1
      (cascIn (R.u (t + 1)) (preLt R μ φ ε t).x.s (preLt R μ φ ε t).L).2) ∧
    (∀ t (prot : ℕ → Bool) (f : ℕ) (st : List ℕ),
      relsOK prot f st ((runL R μ φ ε t).x.s.q.r, (runL R μ φ ε t).L)) ∧
    (∀ t (gs : List ℕ), (∀ g ∈ gs, g < R.G0.N) →
      dispOK gs ((preLt R μ φ ε t).x.s.q.r, (preLt R μ φ ε t).L)) ∧
    initOK R.G0 R.order R.hl ∧ initOK R.G0 R.order R.hu ∧
    (∀ (s : HEState α) (g : ℕ), (s.hp g).pos = (Heap.empty : Heap ℕ α).pos →
      writePos (R.G0.children g) 0 (s.hp g).pos = (HeapB.ofKeys (R.G0.children g) s.val).pos)) ∧
    WL R μ φ ε = R.P + WLnoP R μ φ ε ∧ WLnoP R μ φ ε ≤ 303 * XD0 R ∧
    PG R μ ≤ 27 * (R.G0.N + live R.G0) ∧ PGS R μ ≤ 23 * PG R μ ∧
    PGS R μ ≤ 621 * (R.G0.N + live R.G0) ∧
    WLS R μ φ ε ≤ 23 * WLnoP R μ φ ε ∧ WLS R μ φ ε ≤ 6969 * XD0 R ∧
    XD0 R ≤ XGS R μ ∧ XGS R μ ≤ 622 * XD0 R ∧ XD0 R ≤ XG R μ ∧ XG R μ ≤ 28 * XD0 R ∧
    WLS R μ φ ε ≤ 6969 * XGS R μ ∧ WLnoP R μ φ ε ≤ 303 * XG R μ := by
  have a1 := WLnoP_le μ φ ε hcl hlt hinj
  have a2 := WLS_le_XD0 μ φ ε hcl hlt hinj
  have a3 := XD0_le_XGS (R := R) μ
  have a4 := XD0_le_XG (R := R) μ
  exact ⟨heap_invariants_run μ φ ε hcl, WL_eq μ φ ε, a1, PG_le μ hcl hlt hinj, PGS_le_PG μ, PGS_le μ hcl hlt hinj,
    WLS_le μ φ ε, a2, a3, XGS_le μ hcl hlt hinj, a4, XG_le μ hcl hlt hinj,
    by omega, by omega⟩

lemma isBigO_nat {ι : Type*} {l : Filter ι} {f g : ι → ℕ} (c : ℕ) (h : ∀ i, f i ≤ c * g i) :
    (fun i => (f i : ℝ)) =O[l] (fun i => (g i : ℝ)) := by
  apply IsBigO.of_bound (c : ℝ)
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast h i

/-- **`prop:representation-cost` as one theorem, strict accounting, `P_G` computed** (total
work `W_G = WLS`, `X_G = XGS` with `P_G = PGS` executed), when in every run the children are
gates and the root actions are distinct gates `< N`: `W_G ≤ 6969 X_G`, `P_G ≤ 621 (n + e)`,
`X_G = Θ(XD0)`, hence `W_G = O(X_G)`; on the side of `C` (unchanged from `LiteralG4`)
`P_C + S_C^- ≤ W_C`; condition (R), `X_G = o(P_C + S_C^-)`, implies `W_G = o(W_C)`. -/
theorem representation_cost_strict {β Cell ι : Type*} [DecidableEq β] [DecidableEq Cell]
    {l : Filter ι} (G : ι → SelRun α) (μ : ι → Mem) (φ : ι → α → ℝ) (ε : ι → ℝ)
    (hcl : ∀ i p c, c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j)
    (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WLS (G i) (μ i) (φ i) (ε i) ≤ 6969 * XGS (G i) (μ i)) ∧
    (∀ i, PGS (G i) (μ i) ≤ 621 * ((G i).G0.N + live (G i).G0)) ∧
    (fun i => (WLS (G i) (μ i) (φ i) (ε i) : ℝ)) =O[l] (fun i => (XGS (G i) (μ i) : ℝ)) ∧
    (fun i => (XGS (G i) (μ i) : ℝ)) =O[l] (fun i => (XD0 (G i) : ℝ)) ∧
    (fun i => (XD0 (G i) : ℝ)) =O[l] (fun i => (XGS (G i) (μ i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XGS (G i) (μ i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WLS (G i) (μ i) (φ i) (ε i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) :=
    isBigO_nat 1 (fun i => by rw [one_mul]; exact (C i).lower)
  have hW := fun i => (representation_cost_upper_strict (μ i) (φ i) (ε i) (hcl i) (hlt i)
    (hinj i)).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG : (fun i => (WLS (G i) (μ i) (φ i) (ε i) : ℝ)) =O[l] (fun i => (XGS (G i) (μ i) : ℝ)) :=
    isBigO_nat 6969 hW
  exact ⟨hW, fun i => PGS_le (μ i) (hcl i) (hlt i) (hinj i), hG,
    isBigO_nat 622 (fun i => XGS_le (μ i) (hcl i) (hlt i) (hinj i)),
    isBigO_nat 1 (fun i => by rw [one_mul]; exact XD0_le_XGS (μ i)),
    fun i => (C i).lower, fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **The same with the accounting of `LiteralG4` and `P_G` computed** (total work
`W_G = WLnoP = WL − R.P`, `X_G = XG` with `P_G = PG` executed). -/
theorem representation_cost_PG {β Cell ι : Type*} [DecidableEq β] [DecidableEq Cell]
    {l : Filter ι} (G : ι → SelRun α) (μ : ι → Mem) (φ : ι → α → ℝ) (ε : ι → ℝ)
    (hcl : ∀ i p c, c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j)
    (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WLnoP (G i) (μ i) (φ i) (ε i) ≤ 303 * XG (G i) (μ i)) ∧
    (∀ i, PG (G i) (μ i) ≤ 27 * ((G i).G0.N + live (G i).G0)) ∧
    (fun i => (WLnoP (G i) (μ i) (φ i) (ε i) : ℝ)) =O[l] (fun i => (XG (G i) (μ i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XG (G i) (μ i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WLnoP (G i) (μ i) (φ i) (ε i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) :=
    isBigO_nat 1 (fun i => by rw [one_mul]; exact (C i).lower)
  have hW := fun i => (representation_cost_upper_strict (μ i) (φ i) (ε i) (hcl i) (hlt i)
    (hinj i)).2.2.2.2.2.2.2.2.2.2.2.2.2
  have hG := isBigO_nat (l := l) 303 hW
  exact ⟨hW, fun i => PG_le (μ i) (hcl i) (hlt i) (hinj i), hG, fun i => (C i).lower,
    fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)**, strict accounting and `P_G` computed: against the retirement
engine itself as the compiled representation (`LiteralK4.engineImpl`). -/
theorem condition_R_engine_strict {β ι : Type*} [LinearOrder β] [OrderBot β] {l : Filter ι}
    (G : ι → SelRun α) (μ : ι → Mem) (φ : ι → α → ℝ) (ε : ι → ℝ)
    (hcl : ∀ i p c, c ∈ (G i).G0.children p → c < (G i).G0.N)
    (hlt : ∀ i k, k < (G i).K → (G i).rt k < (G i).G0.N)
    (hinj : ∀ i k, k < (G i).K → ∀ j, j < (G i).K → (G i).rt k = (G i).rt j → k = j)
    (RC : ι → EngineRun β)
    (hR : (fun i => (XGS (G i) (μ i) : ℝ)) =o[l]
      (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WLS (G i) (μ i) (φ i) (ε i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
  have hR' : (fun i => (XGS (G i) (μ i) : ℝ)) =o[l]
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
  have h1 := (representation_cost_strict (l := l) G μ φ ε hcl hlt hinj
    (fun i => LiteralK4.engineImpl (RC i))).2.2.2.2.2.2 hR'
  exact h1.trans_isBigO (isBigO_nat 1 (fun i => by
    rw [one_mul]; exact LiteralK4.engineImpl_W_le (RC i)))

end Final

end LiteralG5
end JointRootCert
