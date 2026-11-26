/-
Joint Root Certification: `prop:representation-coupling` (Trajectory Coupling Across
Circuit Representations) for two ARBITRARY circuits with equal root terminal supports.

Manuscript result covered:

* `prop:representation-coupling`: "unary bypass, interning of identical child sets, and
  dyadic-block replacement preserve root intervals, leaders and stopping times;
  strict-dominance retirement inside any such circuit preserves trajectory coupling".

`LiteralK1.representation_coupling_literal` needs the two circuits to have the same
internal gates (`hleaves`) and `Refines G0 G1`.  This excludes dyadic-block replacement
with FRESH block gates and root-wrapper bypass that changes the root map.  Here no relation
between the gates of the two circuits is assumed: only that every root action has the same
set of terminals below it in both circuits (`SameRootSupports`).

* `selective_supp_coupling`: for two well-formed DAG circuits `G0`, `G1` (each with its own
  root map, terminal map, candidate policy and query schedule) whose root actions have
  equal terminal supports, the Graph-Selective engines on `G0` and on `G1` produce identical
  histories, replies (alarm, leader, stop bit) and stopping times for every controller,
  reward tape and controller tape.  `interval_supp_coupling` is the same with the numerical
  reply (all root intervals) of the engine with protected roots.
* `root_bypass_coupling`: instance for root-wrapper bypass (the root map moves from a
  unary root gate to its child).
* `dyadic_block_coupling`: instance for the dyadic-block circuit `dyDag` built from the
  covers returned by `CostModel.dualCompile`: segment-tree gates over a layout of the
  terminals in `[0, 2^n)` (all fresh, absent from `G0`), and one root gate per action whose
  children are the blocks of its compiled cover `C⁺`.

The proof: each selective engine is coupled to its eager engine (`sel_answer_eq`); the two
eager engines store the running-intersection box at every terminal (`eager_stream`), so by
`exact_eq_sup` every root gate holds the maximum of the box over its terminal support in
both circuits (`root_eq_of_supp`); the oracles agree on every history and `exact_coupling`
concludes.
-/
import JointRootCert.LiteralK1
import JointRootCert.DualCoverFinal

namespace JointRootCert
namespace LiteralK9

open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK1
open _root_.JointRootCert.Representation (Controller history replyAt stopTime OracleImpl
  exact_coupling dyadicBlock IsDyadicCover)
open CostModel (blk runSet RunsFrom dualCompile dualCompile_cover biUnion_blk_of_cover
  dyadicBlock_zero dyadicBlock_succ)

/-! ## The leader-and-stop reply reads root values only at indices `< K` -/

section Scan

variable {α : Type*} [LinearOrder α]

lemma leadScan_congr {L L' : ℕ → α} (act : ℕ → Bool) : ∀ n, (∀ i, i < n → L i = L' i) →
    leadScan L act n = leadScan L' act n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have e := ih (fun i hi => h i (by omega))
    simp only [leadScan, e]
    rcases hs : leadScan L' act n with _ | a
    · rfl
    · have ha := ((leadScan_spec L' act n).2 a hs).1
      simp only [Option.elim]
      rw [h a (by omega), h n (by omega)]

omit [LinearOrder α] in
lemma stopScan_congr (φ : α → ℝ) (ε : ℝ) {U U' : ℕ → α} (la : α) (a : ℕ) (act : ℕ → Bool) :
    ∀ n, (∀ i, i < n → U i = U' i) →
    stopScan φ ε U la a act n = stopScan φ ε U' la a act n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [stopScan]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

lemma qOut_congr (φ : α → ℝ) (ε : ℝ) (K : ℕ) {L L' U U' : ℕ → α} (act : ℕ → Bool)
    (hL : ∀ i, i < K → L i = L' i) (hU : ∀ i, i < K → U i = U' i) :
    qOut φ ε K L U act = qOut φ ε K L' U' act := by
  unfold qOut
  rw [leadScan_congr act K hL]
  rcases hs : leadScan L' act K with _ | a
  · rfl
  · have ha := ((leadScan_spec L' act K).2 a hs).1
    simp only [Option.elim]
    rw [hL a ha, stopScan_congr φ ε (L' a) a act K hU]

end Scan

/-! ## Terminal supports of root actions -/

section Supp

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma suppF_nonempty {G : Dag} (hG : G.WF) : ∀ n g, G.level g < n → (suppF G n g).Nonempty := by
  intro n
  induction n with
  | zero => intro g h; omega
  | succ n ih =>
    intro g hg
    simp only [suppF]
    split_ifs with hc
    · exact Finset.singleton_nonempty g
    · obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc
      have := hG.level_lt g c hcm
      obtain ⟨x, hx⟩ := ih c (by omega)
      exact ⟨x, Finset.mem_biUnion.2 ⟨c, List.mem_toFinset.2 hcm, hx⟩⟩

/-- Every gate has a nonempty terminal support. -/
lemma supp_nonempty {G : Dag} (hG : G.WF) (g : ℕ) : (supp G g).Nonempty :=
  suppF_nonempty hG _ g (Nat.lt_succ_self _)

/-- A unary gate has the terminal support of its child. -/
lemma supp_unary {G : Dag} (hG : G.WF) {r d : ℕ} (h : G.children r = [d]) :
    supp G r = supp G d := by
  rw [supp_gate hG (by rw [h]; simp), h]
  simp

/-- **Equal root terminal supports.**  For every root action `i < K`: the terminal support
of its root gate consists of terminal leaves in both circuits, and a terminal lies below the
root of `i` in `G1` iff it lies below the root of `i` in `G0`.  Nothing is assumed about the
other gates. -/
def SameRootSupports {Z : Type*} (K : ℕ) (G0 G1 : Dag) (rt0 rt1 : ℕ → ℕ)
    (leaf0 leaf1 : Z → ℕ) : Prop :=
  ∀ i, i < K →
    (∀ g ∈ supp G0 (rt0 i), ∃ z, leaf0 z = g) ∧
    (∀ g ∈ supp G1 (rt1 i), ∃ z, leaf1 z = g) ∧
    (∀ z, leaf1 z ∈ supp G1 (rt1 i) ↔ leaf0 z ∈ supp G0 (rt0 i))

/-- Two exact valuations of two circuits that give the same value `b z` to every terminal
`z` agree at two gates with the same terminal support. -/
theorem root_eq_of_supp {Z : Type*} {G0 G1 : Dag} (hG0 : G0.WF) (hG1 : G1.WF)
    {leaf0 leaf1 : Z → ℕ} {v0 v1 : ℕ → α} (hv0 : Exact G0 v0) (hv1 : Exact G1 v1)
    (b : Z → α) (hb0 : ∀ z, v0 (leaf0 z) = b z) (hb1 : ∀ z, v1 (leaf1 z) = b z) {r0 r1 : ℕ}
    (ht0 : ∀ g ∈ supp G0 r0, ∃ z, leaf0 z = g) (ht1 : ∀ g ∈ supp G1 r1, ∃ z, leaf1 z = g)
    (hs : ∀ z, leaf1 z ∈ supp G1 r1 ↔ leaf0 z ∈ supp G0 r0) : v1 r1 = v0 r0 := by
  rw [exact_eq_sup hG1 hv1 r1, exact_eq_sup hG0 hv0 r0]
  apply le_antisymm
  · apply Finset.sup_le
    intro g hg
    obtain ⟨z, rfl⟩ := ht1 g hg
    rw [hb1, ← hb0]
    exact Finset.le_sup ((hs z).1 hg)
  · apply Finset.sup_le
    intro g hg
    obtain ⟨z, rfl⟩ := ht0 g hg
    rw [hb0, ← hb1]
    exact Finset.le_sup ((hs z).2 hg)

/-- Same terminal map and equal supports of the root gates give `SameRootSupports`. -/
theorem sameRootSupports_of_supp_eq {Z : Type*} {K : ℕ} {G0 G1 : Dag} {rt0 rt1 : ℕ → ℕ}
    {leaf : Z → ℕ} (ht : ∀ i, i < K → ∀ g ∈ supp G0 (rt0 i), ∃ z, leaf z = g)
    (hs : ∀ i, i < K → supp G1 (rt1 i) = supp G0 (rt0 i)) :
    SameRootSupports K G0 G1 rt0 rt1 leaf leaf := fun i hi =>
  ⟨ht i hi, by rw [hs i hi]; exact ht i hi, fun z => by rw [hs i hi]⟩

end Supp

/-! ## Two eager engines, then two selective engines -/

section Engines

variable {Z X : Type*} [DecidableEq Z] {α : Type*} [LinearOrder α] [OrderBot α]

/-- The eager engine keeps its invariant and its terminal gates store the
running-intersection box, along any stream of observations. -/
theorem eager_stream {G : Dag} (hG : G.WF) {leaf : Z → ℕ}
    (hleaf : ∀ z, leaf z < G.N ∧ G.children (leaf z) = []) (hinj : Function.Injective leaf)
    {lo0 hi0 : EState α} (i1 : Inv G lo0) (i2 : Inv G hi0) (ci : List (Z × X) → α × α)
    {I0 : Z → α × α} (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (obs : ℕ → Z × X) : ∀ t,
    Inv G (runState G (uS leaf ci (box0 I0) obs) (lo0, hi0) t).1 ∧
    Inv G (runState G (uS leaf ci (box0 I0) obs) (lo0, hi0) t).2 ∧
    ∀ z, (runState G (uS leaf ci (box0 I0) obs) (lo0, hi0) t).1.val (leaf z)
        = (boxAt ci (box0 I0) obs t).lo z ∧
      (runState G (uS leaf ci (box0 I0) obs) (lo0, hi0) t).2.val (leaf z)
        = (boxAt ci (box0 I0) obs t).hi z := by
  intro t
  induction t with
  | zero => exact ⟨i1, i2, hI0⟩
  | succ t ih =>
    obtain ⟨a1, a2, al⟩ := ih
    obtain ⟨_, _, f3, _, _⟩ := boxStep_facts ci (boxAt ci (box0 I0) obs t) (obs t)
    have hx := (hleaf (obs t).1).1
    obtain ⟨l1, l2, l3, _⟩ := wave_spec hG (leaf (obs t).1)
      ((boxAt ci (box0 I0) obs (t + 1)).lo (obs t).1) _ hx a1
    obtain ⟨h1, h2, h3, _⟩ := wave_spec hG (leaf (obs t).1)
      ((boxAt ci (box0 I0) obs (t + 1)).hi (obs t).1) _ hx a2
    refine ⟨l1, h1, fun z => ?_⟩
    have hls := (hleaf z).2
    by_cases hz : z = (obs t).1
    · subst hz
      exact ⟨l2 hls, h2 hls⟩
    · have hne : leaf z ≠ leaf (obs t).1 := fun h => hz (hinj h)
      exact ⟨(l3 _ hls hne).trans (((al z).1).trans (f3 z hz).1.symm),
        (h3 _ hls hne).trans (((al z).2).trans (f3 z hz).2.symm)⟩

/-- **Two eager engines on circuits with equal root supports expose the same oracle** on
every history.  No relation between the gates of `G0` and `G1` is assumed. -/
theorem eag_answer_supp {G0 G1 : Dag} (hG0 : G0.WF) (hG1 : G1.WF) {K : ℕ}
    {rt0 rt1 : ℕ → ℕ} {leaf0 leaf1 : Z → ℕ}
    (hS : SameRootSupports K G0 G1 rt0 rt1 leaf0 leaf1)
    (hleaf0 : ∀ z, leaf0 z < G0.N ∧ G0.children (leaf0 z) = [])
    (hinj0 : Function.Injective leaf0)
    (hleaf1 : ∀ z, leaf1 z < G1.N ∧ G1.children (leaf1 z) = [])
    (hinj1 : Function.Injective leaf1)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α) {lo0 hi0 lo1 hi1 : EState α}
    (i1 : Inv G0 lo0) (i2 : Inv G0 hi0) (j1 : Inv G1 lo1) (j2 : Inv G1 hi1)
    (hI0 : ∀ z, lo0.val (leaf0 z) = (I0 z).1 ∧ hi0.val (leaf0 z) = (I0 z).2)
    (hI1 : ∀ z, lo1.val (leaf1 z) = (I0 z).1 ∧ hi1.val (leaf1 z) = (I0 z).2)
    (φ : α → ℝ) (ε : ℝ) (h : List (Z × X)) :
    (eagImpl G1 K rt1 leaf1 ci I0 lo1 hi1 φ ε).answer h
      = (eagImpl G0 K rt0 leaf0 ci I0 lo0 hi0 φ ε).answer h := by
  have stream : ∀ (obs : ℕ → Z × X) (n : ℕ),
      (eagImpl G1 K rt1 leaf1 ci I0 lo1 hi1 φ ε).answer ((List.range n).map obs)
        = (eagImpl G0 K rt0 leaf0 ci I0 lo0 hi0 φ ε).answer ((List.range n).map obs) := by
    intro obs n
    obtain ⟨a1, a2, al⟩ := eager_stream hG0 hleaf0 hinj0 i1 i2 ci hI0 obs n
    obtain ⟨b1, b2, bl⟩ := eager_stream hG1 hleaf1 hinj1 j1 j2 ci hI1 obs n
    simp only [OracleImpl.answer, eagImpl]
    rw [eag_fold G1 leaf1 ci (box0 I0) _ obs n, eag_fold G0 leaf0 ci (box0 I0) _ obs n]
    refine Prod.ext rfl (qOut_congr φ ε K _ (fun i hi => ?_) (fun i hi => ?_))
    · obtain ⟨t0, t1, ts⟩ := hS i hi
      exact root_eq_of_supp hG0 hG1 (inv_exact a1) (inv_exact b1) _
        (fun z => (al z).1) (fun z => (bl z).1) t0 t1 ts
    · obtain ⟨t0, t1, ts⟩ := hS i hi
      exact root_eq_of_supp hG0 hG1 (inv_exact a2) (inv_exact b2) _
        (fun z => (al z).2) (fun z => (bl z).2) t0 t1 ts
  rcases h with _ | ⟨d, h'⟩
  · show (false, qOut φ ε K (fun i => lo1.val (rt1 i)) (fun i => hi1.val (rt1 i)) (fun _ => true))
      = (false, qOut φ ε K (fun i => lo0.val (rt0 i)) (fun i => hi0.val (rt0 i)) (fun _ => true))
    refine Prod.ext rfl (qOut_congr φ ε K _ (fun i hi => ?_) (fun i hi => ?_))
    · obtain ⟨t0, t1, ts⟩ := hS i hi
      exact root_eq_of_supp hG0 hG1 (inv_exact i1) (inv_exact j1) (fun z => (I0 z).1)
        (fun z => (hI0 z).1) (fun z => (hI1 z).1) t0 t1 ts
    · obtain ⟨t0, t1, ts⟩ := hS i hi
      exact root_eq_of_supp hG0 hG1 (inv_exact i2) (inv_exact j2) (fun z => (I0 z).2)
        (fun z => (hI0 z).2) (fun z => (hI1 z).2) t0 t1 ts
  · have := stream (fun t => (d :: h').getD t d) (d :: h').length
    rwa [list_eq_map_range] at this

/-- The numerical eager replies (all root intervals) agree as well. -/
theorem eag_answer_num_supp {G0 G1 : Dag} (hG0 : G0.WF) (hG1 : G1.WF) {K : ℕ}
    {rt0 rt1 : ℕ → ℕ} {leaf0 leaf1 : Z → ℕ}
    (hS : SameRootSupports K G0 G1 rt0 rt1 leaf0 leaf1)
    (hleaf0 : ∀ z, leaf0 z < G0.N ∧ G0.children (leaf0 z) = [])
    (hinj0 : Function.Injective leaf0)
    (hleaf1 : ∀ z, leaf1 z < G1.N ∧ G1.children (leaf1 z) = [])
    (hinj1 : Function.Injective leaf1)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α) {lo0 hi0 lo1 hi1 : EState α}
    (i1 : Inv G0 lo0) (i2 : Inv G0 hi0) (j1 : Inv G1 lo1) (j2 : Inv G1 hi1)
    (hI0 : ∀ z, lo0.val (leaf0 z) = (I0 z).1 ∧ hi0.val (leaf0 z) = (I0 z).2)
    (hI1 : ∀ z, lo1.val (leaf1 z) = (I0 z).1 ∧ hi1.val (leaf1 z) = (I0 z).2)
    (h : List (Z × X)) :
    (eagImplNum G1 K rt1 leaf1 ci I0 lo1 hi1).answer h
      = (eagImplNum G0 K rt0 leaf0 ci I0 lo0 hi0).answer h := by
  have stream : ∀ (obs : ℕ → Z × X) (n : ℕ),
      (eagImplNum G1 K rt1 leaf1 ci I0 lo1 hi1).answer ((List.range n).map obs)
        = (eagImplNum G0 K rt0 leaf0 ci I0 lo0 hi0).answer ((List.range n).map obs) := by
    intro obs n
    obtain ⟨a1, a2, al⟩ := eager_stream hG0 hleaf0 hinj0 i1 i2 ci hI0 obs n
    obtain ⟨b1, b2, bl⟩ := eager_stream hG1 hleaf1 hinj1 j1 j2 ci hI1 obs n
    simp only [OracleImpl.answer, eagImplNum]
    rw [eag_fold G1 leaf1 ci (box0 I0) _ obs n, eag_fold G0 leaf0 ci (box0 I0) _ obs n]
    refine Prod.ext rfl (funext fun i => ?_)
    obtain ⟨t0, t1, ts⟩ := hS i i.isLt
    exact Prod.ext
      (root_eq_of_supp hG0 hG1 (inv_exact a1) (inv_exact b1) _
        (fun z => (al z).1) (fun z => (bl z).1) t0 t1 ts)
      (root_eq_of_supp hG0 hG1 (inv_exact a2) (inv_exact b2) _
        (fun z => (al z).2) (fun z => (bl z).2) t0 t1 ts)
  rcases h with _ | ⟨d, h'⟩
  · show (false, fun i : Fin K => (lo1.val (rt1 i), hi1.val (rt1 i)))
      = (false, fun i : Fin K => (lo0.val (rt0 i), hi0.val (rt0 i)))
    refine Prod.ext rfl (funext fun i => ?_)
    obtain ⟨t0, t1, ts⟩ := hS i i.isLt
    exact Prod.ext
      (root_eq_of_supp hG0 hG1 (inv_exact i1) (inv_exact j1) (fun z => (I0 z).1)
        (fun z => (hI0 z).1) (fun z => (hI1 z).1) t0 t1 ts)
      (root_eq_of_supp hG0 hG1 (inv_exact i2) (inv_exact j2) (fun z => (I0 z).2)
        (fun z => (hI0 z).2) (fun z => (hI1 z).2) t0 t1 ts)
  · have := stream (fun t => (d :: h').getD t d) (d :: h').length
    rwa [list_eq_map_range] at this

/-- The two Graph-Selective oracles agree on every history. -/
theorem selective_supp_answer_eq {G0 G1 : Dag} (hG0 : G0.WF) (hG1 : G1.WF) {K : ℕ}
    {rt0 rt1 : ℕ → ℕ} {leaf0 leaf1 : Z → ℕ}
    (hS : SameRootSupports K G0 G1 rt0 rt1 leaf0 leaf1)
    {lo0 hi0 lo1 hi1 : EState α}
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (h1 : RInv G1 ⟨G1, lo1, hi1⟩)
    (hleaf0 : ∀ z, leaf0 z < G0.N ∧ G0.children (leaf0 z) = [])
    (hinj0 : Function.Injective leaf0)
    (hleaf1 : ∀ z, leaf1 z < G1.N ∧ G1.children (leaf1 z) = [])
    (hinj1 : Function.Injective leaf1)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α)
    (hI0 : ∀ z, lo0.val (leaf0 z) = (I0 z).1 ∧ hi0.val (leaf0 z) = (I0 z).2)
    (hI1 : ∀ z, lo1.val (leaf1 z) = (I0 z).1 ∧ hi1.val (leaf1 z) = (I0 z).2)
    (cand0 cand1 : RState α → RState α → List (ℕ × ℕ)) (q0 q1 : ℕ → Bool)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε) (h : List (Z × X)) :
    (selImpl G1 K rt1 cand1 q1 leaf1 ci I0 lo1 hi1 φ ε).answer h
      = (selImpl G0 K rt0 cand0 q0 leaf0 ci I0 lo0 hi0 φ ε).answer h := by
  rw [sel_answer_eq hG1 h1 hleaf1 hinj1 hI1 hK φ hφ ε hε h,
    sel_answer_eq hG0 h0 hleaf0 hinj0 hI0 hK φ hφ ε hε h]
  exact eag_answer_supp hG0 hG1 hS hleaf0 hinj0 hleaf1 hinj1 ci I0 h0.invLo h0.invHi
    h1.invLo h1.invHi hI0 hI1 φ ε h

/-- **`prop:representation-coupling`, for two arbitrary circuits.**  Let `G0` and `G1` be
well-formed max-circuit DAGs (gates may be shared; no gate of one need occur in the other),
with root maps `rt0`, `rt1` and injective terminal maps `leaf0`, `leaf1` onto leaves, whose
root actions `i < K` have equal terminal supports (`SameRootSupports`).  Let both
Graph-Selective engines start from initialised states (`RInv`, as produced by
`DagRetire.init_engine`) whose terminal gates hold the same initial box `I₀`.  Then for every
pair of strict-dominance candidate policies `cand0`, `cand1`, every pair of query schedules
`q0`, `q1`, every raw confidence-interval construction `ci`, every controller, reward tape
and controller tape, the runs monitored by the Graph-Selective engine (retirement, release,
root-action retirement) on `G0` and on `G1` have identical histories, identical replies
(alarm, leader, stopping bit) and identical stopping times.  Needs `ε ≥ 0` and `K ≥ 1`. -/
theorem selective_supp_coupling {Ω : Type*} {G0 G1 : Dag} (hG0 : G0.WF) (hG1 : G1.WF)
    {K : ℕ} {rt0 rt1 : ℕ → ℕ} {leaf0 leaf1 : Z → ℕ}
    (hS : SameRootSupports K G0 G1 rt0 rt1 leaf0 leaf1)
    {lo0 hi0 lo1 hi1 : EState α}
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (h1 : RInv G1 ⟨G1, lo1, hi1⟩)
    (hleaf0 : ∀ z, leaf0 z < G0.N ∧ G0.children (leaf0 z) = [])
    (hinj0 : Function.Injective leaf0)
    (hleaf1 : ∀ z, leaf1 z < G1.N ∧ G1.children (leaf1 z) = [])
    (hinj1 : Function.Injective leaf1)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α)
    (hI0 : ∀ z, lo0.val (leaf0 z) = (I0 z).1 ∧ hi0.val (leaf0 z) = (I0 z).2)
    (hI1 : ∀ z, lo1.val (leaf1 z) = (I0 z).1 ∧ hi1.val (leaf1 z) = (I0 z).2)
    (cand0 cand1 : RState α → RState α → List (ℕ × ℕ)) (q0 q1 : ℕ → Bool)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (ctrl : Controller Z X (Bool × Option ℕ × Bool) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (selImpl G1 K rt1 cand1 q1 leaf1 ci I0 lo1 hi1 φ ε).answer ctrl rew ω n
        = history (selImpl G0 K rt0 cand0 q0 leaf0 ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    (∀ n, replyAt (selImpl G1 K rt1 cand1 q1 leaf1 ci I0 lo1 hi1 φ ε).answer ctrl rew ω n
        = replyAt (selImpl G0 K rt0 cand0 q0 leaf0 ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    stopTime (selImpl G1 K rt1 cand1 q1 leaf1 ci I0 lo1 hi1 φ ε).answer ctrl rew ω
      = stopTime (selImpl G0 K rt0 cand0 q0 leaf0 ci I0 lo0 hi0 φ ε).answer ctrl rew ω :=
  exact_coupling _ _ (selective_supp_answer_eq hG0 hG1 hS h0 h1 hleaf0 hinj0 hleaf1 hinj1
    ci I0 hI0 hI1 cand0 cand1 q0 q1 hK φ hφ ε hε) ctrl rew ω

/-- **Numerical form**: with internal retirement and release but protected roots, the
selective engines on `G0` and on `G1` expose the same interval for every root action on
every history, hence identical runs for every controller that reads them. -/
theorem interval_supp_coupling {Ω : Type*} {G0 G1 : Dag} (hG0 : G0.WF) (hG1 : G1.WF)
    {K : ℕ} {rt0 rt1 : ℕ → ℕ} {leaf0 leaf1 : Z → ℕ}
    (hS : SameRootSupports K G0 G1 rt0 rt1 leaf0 leaf1)
    {lo0 hi0 lo1 hi1 : EState α}
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (h1 : RInv G1 ⟨G1, lo1, hi1⟩)
    (hleaf0 : ∀ z, leaf0 z < G0.N ∧ G0.children (leaf0 z) = [])
    (hinj0 : Function.Injective leaf0)
    (hleaf1 : ∀ z, leaf1 z < G1.N ∧ G1.children (leaf1 z) = [])
    (hinj1 : Function.Injective leaf1)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α)
    (hI0 : ∀ z, lo0.val (leaf0 z) = (I0 z).1 ∧ hi0.val (leaf0 z) = (I0 z).2)
    (hI1 : ∀ z, lo1.val (leaf1 z) = (I0 z).1 ∧ hi1.val (leaf1 z) = (I0 z).2)
    (cand0 cand1 : RState α → RState α → List (ℕ × ℕ))
    (ctrl : Controller Z X (Bool × (Fin K → α × α)) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (selImplNum G1 K rt1 cand1 leaf1 ci I0 lo1 hi1).answer ctrl rew ω n
        = history (selImplNum G0 K rt0 cand0 leaf0 ci I0 lo0 hi0).answer ctrl rew ω n) ∧
    (∀ n, replyAt (selImplNum G1 K rt1 cand1 leaf1 ci I0 lo1 hi1).answer ctrl rew ω n
        = replyAt (selImplNum G0 K rt0 cand0 leaf0 ci I0 lo0 hi0).answer ctrl rew ω n) ∧
    stopTime (selImplNum G1 K rt1 cand1 leaf1 ci I0 lo1 hi1).answer ctrl rew ω
      = stopTime (selImplNum G0 K rt0 cand0 leaf0 ci I0 lo0 hi0).answer ctrl rew ω := by
  apply exact_coupling
  intro h
  rw [sel_answer_num_eq hG1 h1 hleaf1 hinj1 hI1 h, sel_answer_num_eq hG0 h0 hleaf0 hinj0 hI0 h]
  exact eag_answer_num_supp hG0 hG1 hS hleaf0 hinj0 hleaf1 hinj1 ci I0 h0.invLo h0.invHi
    h1.invLo h1.invHi hI0 hI1 h

/-- **Root-wrapper bypass.**  If every root gate `rt0 i` of `G0` (`i < K`) is a unary
wrapper with child `d i`, and `G1` is any well-formed circuit with the same terminal map in
which the new root gate `rt1 i` has the terminal support of `d i` in `G0` (for instance
`G1 = G0` and `rt1 = d`, see `root_bypass_coupling_same`), then the selective runs on
`(G0, rt0)` and on `(G1, rt1)` coincide. -/
theorem root_bypass_coupling {Ω : Type*} {G0 G1 : Dag} (hG0 : G0.WF) (hG1 : G1.WF)
    {K : ℕ} {rt0 rt1 d : ℕ → ℕ} {leaf : Z → ℕ}
    (hwrap : ∀ i, i < K → G0.children (rt0 i) = [d i])
    (hsupp : ∀ i, i < K → supp G1 (rt1 i) = supp G0 (d i))
    (ht : ∀ i, i < K → ∀ g ∈ supp G0 (rt0 i), ∃ z, leaf z = g)
    {lo0 hi0 lo1 hi1 : EState α}
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (h1 : RInv G1 ⟨G1, lo1, hi1⟩)
    (hleaf0 : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = [])
    (hleaf1 : ∀ z, leaf z < G1.N ∧ G1.children (leaf z) = [])
    (hinj : Function.Injective leaf)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (hI1 : ∀ z, lo1.val (leaf z) = (I0 z).1 ∧ hi1.val (leaf z) = (I0 z).2)
    (cand0 cand1 : RState α → RState α → List (ℕ × ℕ)) (q0 q1 : ℕ → Bool)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (ctrl : Controller Z X (Bool × Option ℕ × Bool) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (selImpl G1 K rt1 cand1 q1 leaf ci I0 lo1 hi1 φ ε).answer ctrl rew ω n
        = history (selImpl G0 K rt0 cand0 q0 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    (∀ n, replyAt (selImpl G1 K rt1 cand1 q1 leaf ci I0 lo1 hi1 φ ε).answer ctrl rew ω n
        = replyAt (selImpl G0 K rt0 cand0 q0 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    stopTime (selImpl G1 K rt1 cand1 q1 leaf ci I0 lo1 hi1 φ ε).answer ctrl rew ω
      = stopTime (selImpl G0 K rt0 cand0 q0 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω := by
  have hS : SameRootSupports K G0 G1 rt0 rt1 leaf leaf :=
    sameRootSupports_of_supp_eq ht
      (fun i hi => (hsupp i hi).trans (supp_unary hG0 (hwrap i hi)).symm)
  exact selective_supp_coupling hG0 hG1 hS h0 h1 hleaf0 hinj hleaf1 hinj ci I0 hI0 hI1
    cand0 cand1 q0 q1 hK φ hφ ε hε ctrl rew ω

/-- Root-wrapper bypass on the same circuit: the root map moves from the unary wrappers
`rt0 i` to their children `d i`. -/
theorem root_bypass_coupling_same {Ω : Type*} {G0 : Dag} (hG0 : G0.WF)
    {K : ℕ} {rt0 d : ℕ → ℕ} {leaf : Z → ℕ}
    (hwrap : ∀ i, i < K → G0.children (rt0 i) = [d i])
    (ht : ∀ i, i < K → ∀ g ∈ supp G0 (rt0 i), ∃ z, leaf z = g)
    {lo0 hi0 : EState α} (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf0 : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (cand0 cand1 : RState α → RState α → List (ℕ × ℕ)) (q0 q1 : ℕ → Bool)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (ctrl : Controller Z X (Bool × Option ℕ × Bool) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (selImpl G0 K d cand1 q1 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n
        = history (selImpl G0 K rt0 cand0 q0 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    (∀ n, replyAt (selImpl G0 K d cand1 q1 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n
        = replyAt (selImpl G0 K rt0 cand0 q0 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    stopTime (selImpl G0 K d cand1 q1 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω
      = stopTime (selImpl G0 K rt0 cand0 q0 leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω :=
  root_bypass_coupling hG0 hG0 hwrap (fun _ _ => rfl) ht h0 h0 hleaf0 hleaf0 hinj ci I0
    hI0 hI0 cand0 cand1 q0 q1 hK φ hφ ε hε ctrl rew ω

end Engines

/-! ## The dyadic-block circuit compiled from `dualCompile` -/

section Dyadic

/-- Gate index of the segment-tree node `(k, j)` (level `k`, index `j < 2^(n-k)`). -/
def tnode (n k j : ℕ) : ℕ := k * 2 ^ n + j

/-- First gate index after the tree; root action `i` is gate `dyOff n + i`. -/
def dyOff (n : ℕ) : ℕ := (n + 1) * 2 ^ n

/-- Children in the dyadic-block circuit: a tree node `(k, j)` with `k ≥ 1` has the two
children `(k-1, 2j)`, `(k-1, 2j+1)`; tree nodes of level `0` are the leaves (position `p` is
gate `p`); root gate `dyOff n + i` (`i < K`) has the blocks of `cov i` as children. -/
def dyChildren (n K : ℕ) (cov : ℕ → List (ℕ × ℕ)) (g : ℕ) : List ℕ :=
  if g < dyOff n then
    (if 1 ≤ g / 2 ^ n ∧ g % 2 ^ n < 2 ^ (n - g / 2 ^ n) then
      [tnode n (g / 2 ^ n - 1) (2 * (g % 2 ^ n)), tnode n (g / 2 ^ n - 1) (2 * (g % 2 ^ n) + 1)]
     else [])
  else if g - dyOff n < K then (cov (g - dyOff n)).map (fun d => tnode n d.1 d.2) else []

/-- **The dyadic-block circuit**: segment tree over positions `[0, 2^n)` plus `K` root
gates whose children are the blocks of their covers. -/
def dyDag (n K : ℕ) (cov : ℕ → List (ℕ × ℕ)) : Dag where
  N := dyOff n + K
  children := dyChildren n K cov
  parents := fun c => (List.range (dyOff n + K)).filter (fun p => decide (c ∈ dyChildren n K cov p))
  level := fun g => if g < dyOff n then g / 2 ^ n else n + 1
  L := n + 1

lemma tnode_facts {n k j : ℕ} (hk : k ≤ n) (hj : j < 2 ^ n) :
    tnode n k j < dyOff n ∧ tnode n k j / 2 ^ n = k ∧ tnode n k j % 2 ^ n = j := by
  have hpos : 0 < 2 ^ n := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold tnode dyOff
    have : k * 2 ^ n + 2 ^ n ≤ (n + 1) * 2 ^ n := by nlinarith
    omega
  · unfold tnode
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
  · unfold tnode
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

lemma tnode_zero (n p : ℕ) : tnode n 0 p = p := by simp [tnode]

lemma pow_sub_le (n k : ℕ) : 2 ^ (n - k) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma dyChildren_node {n K : ℕ} {cov : ℕ → List (ℕ × ℕ)} {k j : ℕ} (hk : k ≤ n)
    (hj : j < 2 ^ (n - k)) :
    dyChildren n K cov (tnode n k j)
      = if 1 ≤ k then [tnode n (k - 1) (2 * j), tnode n (k - 1) (2 * j + 1)] else [] := by
  obtain ⟨a, b, c⟩ := tnode_facts (n := n) (k := k) (j := j) hk (lt_of_lt_of_le hj (pow_sub_le n k))
  unfold dyChildren
  rw [ite_eq_left a, b, c]
  by_cases h1 : 1 ≤ k
  · rw [ite_eq_left ⟨h1, hj⟩, ite_eq_left h1]
  · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]

lemma dyChildren_root {n K : ℕ} {cov : ℕ → List (ℕ × ℕ)} {i : ℕ} (hi : i < K) :
    dyChildren n K cov (dyOff n + i) = (cov i).map (fun d => tnode n d.1 d.2) := by
  unfold dyChildren
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left hi]

lemma dyChildren_lt {n K : ℕ} {cov : ℕ → List (ℕ × ℕ)} {p c : ℕ}
    (h : c ∈ dyChildren n K cov p) : p < dyOff n + K := by
  unfold dyChildren at h
  split_ifs at h with h1 h2 h3
  · omega
  · simp at h
  · omega
  · simp at h

/-- The dyadic-block circuit is well formed when every cover block is a tree node. -/
theorem dyDag_wf {n K : ℕ} {cov : ℕ → List (ℕ × ℕ)}
    (hcov : ∀ i, i < K → ∀ d ∈ cov i, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1)) :
    (dyDag n K cov).WF where
  parents_iff c p := by
    simp only [dyDag, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨dyChildren_lt h, h⟩⟩
  parents_nodup c := (List.nodup_range).filter _
  parent_lt c p h := by
    simp only [dyDag, List.mem_filter, List.mem_range] at h
    exact h.1
  level_lt p c h := by
    simp only [dyDag] at h ⊢
    have hpos : 0 < 2 ^ n := by positivity
    unfold dyChildren at h
    split_ifs at h with h1 h2 h3
    · -- tree node
      have hkn : p / 2 ^ n ≤ n := by
        have := (Nat.div_lt_iff_lt_mul hpos).2 (by unfold dyOff at h1; exact h1)
        omega
      have hp2 : 2 * 2 ^ (n - p / 2 ^ n) ≤ 2 ^ n := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hk1 : p / 2 ^ n - 1 ≤ n := by omega
      have hc : c = tnode n (p / 2 ^ n - 1) (2 * (p % 2 ^ n)) ∨
          c = tnode n (p / 2 ^ n - 1) (2 * (p % 2 ^ n) + 1) := by simpa using h
      rcases hc with rfl | rfl
      · obtain ⟨a, b, _⟩ := tnode_facts (n := n) hk1 (show 2 * (p % 2 ^ n) < 2 ^ n by omega)
        rw [ite_eq_left a, b, ite_eq_left h1]
        omega
      · obtain ⟨a, b, _⟩ := tnode_facts (n := n) hk1 (show 2 * (p % 2 ^ n) + 1 < 2 ^ n by omega)
        rw [ite_eq_left a, b, ite_eq_left h1]
        omega
    · simp at h
    · -- root gate
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
      obtain ⟨hd1, hd2⟩ := hcov _ h3 d hd
      obtain ⟨a, b, _⟩ := tnode_facts (n := n) hd1 (lt_of_lt_of_le hd2 (pow_sub_le n d.1))
      rw [ite_eq_left a, b, ite_eq_right h1]
      omega
    · simp at h
  level_le g := by
    simp only [dyDag]
    have hpos : 0 < 2 ^ n := by positivity
    split_ifs with h1
    · have := (Nat.div_lt_iff_lt_mul hpos).2 (by unfold dyOff at h1; exact h1)
      omega
    · exact le_rfl

/-- Positions `p < 2^n` are leaves of the dyadic-block circuit. -/
lemma dyDag_leaf {n K : ℕ} {cov : ℕ → List (ℕ × ℕ)} {p : ℕ} (hp : p < 2 ^ n) :
    p < (dyDag n K cov).N ∧ (dyDag n K cov).children p = [] := by
  have e := dyChildren_node (K := K) (cov := cov) (Nat.zero_le n) (j := p) (by simpa using hp)
  rw [tnode_zero] at e
  refine ⟨?_, ?_⟩
  · have := (tnode_facts (k := 0) (Nat.zero_le n) hp).1
    rw [tnode_zero] at this
    show p < dyOff n + K
    omega
  · show dyChildren n K cov p = []
    rw [e]
    simp

/-- The terminal support of the tree node `(k, j)` is its dyadic block. -/
theorem dyDag_supp_node {n K : ℕ} {cov : ℕ → List (ℕ × ℕ)}
    (hcov : ∀ i, i < K → ∀ d ∈ cov i, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1)) :
    ∀ k, k ≤ n → ∀ j, j < 2 ^ (n - k) → supp (dyDag n K cov) (tnode n k j) = dyadicBlock k j := by
  have hG := dyDag_wf hcov
  intro k
  induction k with
  | zero =>
    intro _ j hj
    have e := dyChildren_node (K := K) (cov := cov) (Nat.zero_le n) hj
    rw [supp_leaf (G := dyDag n K cov) (by show dyChildren n K cov _ = []; rw [e]; simp),
      tnode_zero, dyadicBlock_zero]
  | succ k ih =>
    intro hk j hj
    have e := dyChildren_node (K := K) (cov := cov) hk hj
    simp only [le_add_iff_nonneg_left, zero_le, ite_true, Nat.add_sub_cancel] at e
    have hj2 : 2 * j + 1 < 2 ^ (n - k) := by
      have : 2 ^ (n - k) = 2 * 2 ^ (n - (k + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    rw [supp_gate hG (by show dyChildren n K cov _ ≠ []; rw [e]; simp)]
    show (dyChildren n K cov (tnode n (k + 1) j)).toFinset.biUnion _ = _
    rw [e, dyadicBlock_succ]
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, biUnion_insert,
      singleton_biUnion]
    rw [ih (by omega) (2 * j) (by omega), ih (by omega) (2 * j + 1) hj2]

/-- The terminal support of root gate `dyOff n + i` is the union of the blocks of its
cover. -/
theorem dyDag_supp_root {n K : ℕ} {cov : ℕ → List (ℕ × ℕ)}
    (hcov : ∀ i, i < K → ∀ d ∈ cov i, d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1)) {i : ℕ} (hi : i < K)
    (hne : cov i ≠ []) :
    supp (dyDag n K cov) (dyOff n + i) = (cov i).toFinset.biUnion blk := by
  have hG := dyDag_wf hcov
  have e := dyChildren_root (n := n) (cov := cov) hi
  rw [supp_gate hG (by show dyChildren n K cov _ ≠ []; rw [e]; simpa using hne)]
  show (dyChildren n K cov (dyOff n + i)).toFinset.biUnion _ = _
  rw [e]
  ext x
  simp only [Finset.mem_biUnion, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨g, ⟨d, hd, rfl⟩, hx⟩
    obtain ⟨h1, h2⟩ := hcov i hi d hd
    exact ⟨d, hd, by rw [dyDag_supp_node hcov d.1 h1 d.2 h2] at hx; exact hx⟩
  · rintro ⟨d, hd, hx⟩
    obtain ⟨h1, h2⟩ := hcov i hi d hd
    exact ⟨_, ⟨d, hd, rfl⟩, by rw [dyDag_supp_node hcov d.1 h1 d.2 h2]; exact hx⟩

/-- The dyadic-block circuit compiled by `dualCompile` from the run lists `rl i` of the
root supports under a layout: cover `C⁺` of action `i` is `(dualCompile n M (rl i)).1.1`. -/
def dyCompiled (n M K : ℕ) (rl : ℕ → List (ℕ × ℕ)) : Dag :=
  dyDag n K (fun i => (dualCompile n M (rl i)).1.1)

variable {Z X : Type*} [DecidableEq Z] {α : Type*} [LinearOrder α] [OrderBot α]

omit [DecidableEq Z] in
/-- The compiled circuit has the root supports of `G0`. -/
theorem dyCompiled_sameRootSupports {G0 : Dag} (hG0 : G0.WF) {K n M : ℕ} (hM : M ≤ 2 ^ n)
    {rt0 : ℕ → ℕ} {leaf0 pos : Z → ℕ} (rl : ℕ → List (ℕ × ℕ))
    (hrl : ∀ i, i < K → RunsFrom M 0 (rl i)) (hposinj : Function.Injective pos)
    (ht0 : ∀ i, i < K → ∀ g ∈ supp G0 (rt0 i), ∃ z, leaf0 z = g)
    (hrun : ∀ i, i < K → ∀ p, p ∈ runSet (rl i) ↔ ∃ z, pos z = p ∧ leaf0 z ∈ supp G0 (rt0 i)) :
    (dyCompiled n M K rl).WF ∧
    SameRootSupports K G0 (dyCompiled n M K rl) rt0 (fun i => dyOff n + i) leaf0 pos := by
  have hcov : ∀ i, i < K → ∀ d ∈ (fun i => (dualCompile n M (rl i)).1.1) i,
      d.1 ≤ n ∧ d.2 < 2 ^ (n - d.1) :=
    fun i hi => (DualCoverFinal.dualCompile_lists n M hM (rl i) (hrl i hi)).2.2.1
  refine ⟨dyDag_wf hcov, fun i hi => ?_⟩
  have hU : ((dualCompile n M (rl i)).1.1).toFinset.biUnion blk = runSet (rl i) :=
    biUnion_blk_of_cover (dualCompile_cover n M hM (rl i) (hrl i hi)).1
  have hne : (dualCompile n M (rl i)).1.1 ≠ [] := by
    intro hnil
    obtain ⟨g, hg⟩ := supp_nonempty hG0 (rt0 i)
    obtain ⟨z, rfl⟩ := ht0 i hi g hg
    have hp := (hrun i hi (pos z)).2 ⟨z, rfl, hg⟩
    rw [← hU, hnil] at hp
    simp at hp
  have hs : supp (dyCompiled n M K rl) (dyOff n + i) = runSet (rl i) := by
    unfold dyCompiled
    rw [dyDag_supp_root hcov hi hne, hU]
  refine ⟨ht0 i hi, ?_, fun z => ?_⟩
  · intro g hg
    rw [hs] at hg
    obtain ⟨z, hz, _⟩ := (hrun i hi g).1 hg
    exact ⟨z, hz⟩
  · show pos z ∈ supp (dyCompiled n M K rl) (dyOff n + i) ↔ _
    rw [hs, hrun i hi]
    constructor
    · rintro ⟨z', hz', hm⟩
      rw [hposinj hz'] at hm
      exact hm
    · intro hm
      exact ⟨z, rfl, hm⟩

/-- **`prop:representation-coupling`, dyadic-block replacement with fresh block gates.**
Let `G0` be a well-formed max-circuit DAG with root map `rt0` and terminal map `leaf0`, whose
root supports consist of terminals.  Lay the terminals out by an injective `pos` into
`[0, 2^n)`, and let `rl i` be the run list (`RunsFrom M 0`, `M ≤ 2^n`) of the support of
action `i` under the layout: `p ∈ runSet (rl i)` iff `p = pos z` for a terminal `z` below
`rt0 i`.  Let `G1 = dyCompiled n M K rl` be the circuit whose root gates have as children
the blocks of the covers `C⁺` returned by `dualCompile` (all block gates are fresh).  If
both Graph-Selective engines start from initialised states holding the same initial box,
then the selective run on `G1` (terminal `z` at leaf `pos z`, action `i` at gate
`dyOff n + i`) and the selective run on `G0` have identical histories, replies and stopping
times for every controller, reward tape and controller tape. -/
theorem dyadic_block_coupling {Ω : Type*} {G0 : Dag} (hG0 : G0.WF) {K n M : ℕ}
    (hM : M ≤ 2 ^ n) {rt0 : ℕ → ℕ} {leaf0 pos : Z → ℕ} (rl : ℕ → List (ℕ × ℕ))
    (hrl : ∀ i, i < K → RunsFrom M 0 (rl i))
    (hpos : ∀ z, pos z < 2 ^ n) (hposinj : Function.Injective pos)
    (ht0 : ∀ i, i < K → ∀ g ∈ supp G0 (rt0 i), ∃ z, leaf0 z = g)
    (hrun : ∀ i, i < K → ∀ p, p ∈ runSet (rl i) ↔ ∃ z, pos z = p ∧ leaf0 z ∈ supp G0 (rt0 i))
    {lo0 hi0 lo1 hi1 : EState α}
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (h1 : RInv (dyCompiled n M K rl) ⟨dyCompiled n M K rl, lo1, hi1⟩)
    (hleaf0 : ∀ z, leaf0 z < G0.N ∧ G0.children (leaf0 z) = [])
    (hinj0 : Function.Injective leaf0)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α)
    (hI0 : ∀ z, lo0.val (leaf0 z) = (I0 z).1 ∧ hi0.val (leaf0 z) = (I0 z).2)
    (hI1 : ∀ z, lo1.val (pos z) = (I0 z).1 ∧ hi1.val (pos z) = (I0 z).2)
    (cand0 cand1 : RState α → RState α → List (ℕ × ℕ)) (q0 q1 : ℕ → Bool)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (ctrl : Controller Z X (Bool × Option ℕ × Bool) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n', history (selImpl (dyCompiled n M K rl) K (fun i => dyOff n + i) cand1 q1 pos ci I0
          lo1 hi1 φ ε).answer ctrl rew ω n'
        = history (selImpl G0 K rt0 cand0 q0 leaf0 ci I0 lo0 hi0 φ ε).answer ctrl rew ω n') ∧
    (∀ n', replyAt (selImpl (dyCompiled n M K rl) K (fun i => dyOff n + i) cand1 q1 pos ci I0
          lo1 hi1 φ ε).answer ctrl rew ω n'
        = replyAt (selImpl G0 K rt0 cand0 q0 leaf0 ci I0 lo0 hi0 φ ε).answer ctrl rew ω n') ∧
    stopTime (selImpl (dyCompiled n M K rl) K (fun i => dyOff n + i) cand1 q1 pos ci I0
        lo1 hi1 φ ε).answer ctrl rew ω
      = stopTime (selImpl G0 K rt0 cand0 q0 leaf0 ci I0 lo0 hi0 φ ε).answer ctrl rew ω := by
  obtain ⟨hG1, hS⟩ := dyCompiled_sameRootSupports hG0 hM rl hrl hposinj ht0 hrun
  exact selective_supp_coupling hG0 hG1 hS h0 h1 hleaf0 hinj0
    (fun z => dyDag_leaf (hpos z)) hposinj ci I0 hI0 hI1 cand0 cand1 q0 q1 hK φ hφ ε hε
    ctrl rew ω

end Dyadic

end LiteralK9
end JointRootCert
