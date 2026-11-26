/-
Joint Root Certification: `prop:representation-cost` (Unified Full-Cost Representation
Comparison) with the printed upper bound `eq:prop-rep-upper` and the printed condition (R),
without a level-scheduling term and without a hypothesis on the cost of a rollout.

Manuscript result covered:

* `prop:representation-cost`, all three sentences:
  `W_R = O(H + P_R + n_R + e_R + (S_R^+ + e_R) log D_R)` (`eq:prop-rep-upper`), the lower
  bound `Ω(P_C + S_C^-)` for every implementation of the incidence-delivery contract, and
  the advantage under condition (R) (`eq:representation-condition`).

## What changes with respect to `LiteralK3` / `LiteralK4`

`LiteralK3.representation_cost_upper` proves the upper bound only with an additional term
`τ(L+3)`, because its waves (`EngineFinal.waveH`) scan the level buckets `0..L`.  Here the
same run (`LiteralK3.SelRun`, unchanged: same circuit, same terminal updates, same queries,
same stopping time, same `S^+`, same `F_t`) is executed by

* the level-free wave `LiteralE7a.waveD` (changed gates on a stack, no level structure),
  inside `LiteralE7a.runSD` (Graph Selective: waves, strict-dominance retirement tests,
  heap deletions, release cascade, root queries with root-action retirement), and
* the linear initialisation `LiteralE7a.initPassB` (bottom-up heap construction).

`LiteralE7a.runSD_spec` shows that this engine represents the abstract run
`RetireFinal.runF` at every time, and that one step costs at most
`6 + 2·(deliveries) + 2·costF - 4(L+3)`, where `costF` (the abstract charge) contains
`2(L+3)` for its two level scans; so the level terms cancel exactly.  `waveD` needs, per
wave, ONE changed terminal; in this engine every rollout's update `u (t+1) = (x, l, u)` is a
single terminal `x` (one wave per endpoint), so the hypothesis of `LiteralE7a.waveD_spec`
holds, on the live (retired) circuit, through the coupled invariant `RetireFinal.CInv`.

## What `H` is

The manuscript defines `H` as "the shared work of TA-UCT rollout selection, reward sampling,
terminal interval intersection, and root-action scans through `τ`".  Here
`Hsh R = R.H + τ + R.scans`, where

* `R.H = Σ_{t ≤ τ} h t` is the given shared work (rollout selection, reward sampling: not
  modelled, as in `LiteralK3`);
* `τ`: one unit per rollout for the terminal interval intersection (the update `u (t+1)`
  is the given intersected interval; we book one unit for producing it);
* `R.scans = Σ_{t ≤ τ} [q t] · K`: one scan of the `K` root actions per root query.

The engine's work `WD R` counts `R.H` once and all its own computed work (its root scans
are three passes over `K`, its rollouts cost at least one unit each) in full; nothing is
removed from `W` to put it into `H`.  If `H` is read as `R.H` alone, the bound holds with
`H + τ + Q·K` instead (`representation_cost_upper_D`, item 7), and it holds as `O(R.X)` with
`R.X` from `LiteralK3` when every rollout has shared work at least one and every query time
shared work at least `K` (item 8).
-/
import JointRootCert.LiteralK3
import JointRootCert.LiteralK4
import JointRootCert.LiteralE7a

namespace JointRootCert
namespace LiteralK10

open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a
open HeapImpl (Heap HEState SimE)
open Asymptotics

section Engine

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α)

/-- Initial implemented state: both endpoint states initialised by `initPassB` (bottom-up
heaps), all root actions active. -/
def hq0B : HQS α :=
  ⟨⟨R.G0, (initPassB R.G0 R.order R.hl).1, (initPassB R.G0 R.order R.hu).1⟩, fun _ => true⟩

/-- State of the engine (`LiteralE7a.runSD`, waves by `waveD`) after `t` rollouts. -/
def hrunD (t : ℕ) : HQS α := runSD R.K R.rt delivV R.u R.q (hq0B R) t

/-- State of the engine immediately before the backup wave of rollout `t + 1`. -/
def hpreD (t : ℕ) : HQS α :=
  if R.q t = true then (qRetireH R.K R.rt (hrunD R t)).1 else hrunD R t

/-- Computed cost of the two initialisation passes with bottom-up heaps. -/
def WinitB : ℕ := (initPassB R.G0 R.order R.hl).2 + (initPassB R.G0 R.order R.hu).2

/-- Computed cost of the `τ` rollouts (waves by `waveD`, retirement tests, heap deletions,
release cascade) and of the queries at the times `t < τ`. -/
def WrollD : ℕ := ∑ t ∈ range R.τ, costSD R.K R.rt delivV R.u R.q (hq0B R) t

/-- Computed cost of the query at the stopping time `τ` (if `q τ`). -/
def WlastD : ℕ := if R.q R.τ = true then R.K + (qRetireH R.K R.rt (hrunD R R.τ)).2 else 0

/-- Computed cost of the final disposal pass over all gates. -/
def WdispD : ℕ := (disposeAll (List.range R.G0.N) (hpreD R R.τ).r.G).2

/-- **Total scalar work `W_R`** of the engine with `waveD` and bottom-up initialisation:
the given numbers `P` (upfront compiler passes) and `R.H` (given shared work), plus the
computed costs of initialisation, of all rollouts and queries, and of final disposal. -/
def WD : ℕ := R.P + R.H + WinitB R + WrollD R + WlastD R + WdispD R

/-- **The shared work `H`** of the manuscript: the given shared work, one unit per rollout
for the terminal interval intersection, and one scan of the `K` root actions per query. -/
def Hsh : ℕ := R.H + R.τ + R.scans

/-- The right side of `eq:prop-rep-upper`: `H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1)`. -/
noncomputable def XD : ℕ :=
  Hsh R + R.P + R.G0.N + live R.G0 + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)

lemma initB_facts :
    SimR (hq0B R).r ⟨R.G0, R.lo0, R.hi0⟩ ∧ WinitB R ≤ 4 * (R.G0.N + 2 * live R.G0) := by
  obtain ⟨l1, l2⟩ := initPassB_sim (G := R.G0) R.order R.hl ⟨R.hl.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_lo
  obtain ⟨u1, u2⟩ := initPassB_sim (G := R.G0) R.order R.hu ⟨R.hu.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_hi
  have hdeg := R.order_deg_le
  have hlen := R.order_length_le
  rw [sum_map_lin] at l2 u2
  refine ⟨⟨rfl, l1, u1⟩, ?_⟩
  unfold WinitB
  omega

lemma simD (t : ℕ) :
    SimQ (hrunD R t) (R.run t) ∧
    costSD R.K R.rt delivV R.u R.q (hq0B R) t + 4 * (R.G0.L + 3)
      ≤ 6 + 2 * volF R.K R.rt delivCand R.u R.q R.s0 t
        + 2 * costF R.K R.rt delivCand R.u R.q R.s0 t ∧
    volF R.K R.rt delivCand R.u R.q R.s0 t ≤ costSD R.K R.rt delivV R.u R.q (hq0B R) t :=
  runSD_spec (K := R.K) (rt := R.rt) R.wf R.init_facts.2.1 R.hn R.q (hq0B R).r
    (initB_facts R).1 (fun _ => true) t

lemma sim_preD (t : ℕ) : SimQ (hpreD R t) (R.pre t) := by
  unfold hpreD SelRun.pre preF
  by_cases hq : R.q t = true
  · rw [ite_eq_left hq, ite_eq_left hq]
    exact (qRetireH_sim R.K R.rt (simD R t).1).1
  · rw [ite_eq_right hq, ite_eq_right hq]
    exact (simD R t).1

/-- **The work bound without a level term.** -/
theorem WD_le : WD R ≤ 12 * XD R := by
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
  have hroll : WrollD R + R.τ * (4 * (R.G0.L + 3))
      ≤ 6 * R.τ + 2 * ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t
        + 2 * ∑ t ∈ range R.τ, costF R.K R.rt delivCand R.u R.q R.s0 t := by
    calc WrollD R + R.τ * (4 * (R.G0.L + 3))
        = ∑ t ∈ range R.τ, (costSD R.K R.rt delivV R.u R.q (hq0B R) t + 4 * (R.G0.L + 3)) := by
          unfold WrollD
          rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
      _ ≤ ∑ t ∈ range R.τ, (6 + 2 * volF R.K R.rt delivCand R.u R.q R.s0 t
          + 2 * costF R.K R.rt delivCand R.u R.q R.s0 t) :=
          sum_le_sum (fun t _ => (simD R t).2.1)
      _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, ← mul_sum,
            ← mul_sum, smul_eq_mul]
          ring
  have hlast : WlastD R + 2 * cells (R.pre R.τ).r.G
      ≤ 4 * (if R.q R.τ = true then R.K else 0) + 2 * cells (R.run R.τ).r.G := by
    unfold WlastD SelRun.pre preF
    by_cases hq : R.q R.τ = true
    · rw [ite_eq_left hq, ite_eq_left hq, ite_eq_left hq]
      have h1 := (qRetireH_sim R.K R.rt (simD R R.τ).1).2
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
  have hdisp : WdispD R ≤ R.G0.N + cells (R.pre R.τ).r.G := by
    have hG : (hpreD R R.τ).r.G = (R.pre R.τ).r.G := (sim_preD R R.τ).r.G
    have hN : (R.pre R.τ).r.G.N = R.G0.N := (R.pre_inv R.τ).nEq
    have h1 := disposeAll_cost (List.range R.G0.N) (R.pre R.τ).r.G
      (fun g hg => by rw [hN]; exact List.mem_range.1 hg)
    have h2 := live_le_cells (R.pre R.τ).r.G
    unfold WdispD
    rw [hG]
    rw [List.length_range] at h1
    omega
  have hinit := (initB_facts R).2
  have hretm := Nat.mul_le_mul_left (2 * Nat.clog 2 R.D + 4)
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
  unfold WD XD Hsh
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

end Engine

/-! ## `prop:representation-cost` -/

section Final

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, as printed.**

Hypotheses: only the fields of `R : LiteralK3.SelRun α` (the data of one run and the
structural input conditions: well-formed circuit of maximum degree `D`, duplicate-free child
lists, initialisation order sorted by level, empty initial heaps, nonempty leaf intervals,
every parentless internal gate is a root-action gate, nested terminal updates
`eq:terminal-box`).  Nothing is assumed about the shared work `h` or about costs.

The engine is Graph Selective with release of orphaned gates, executed with the level-free
wave `LiteralE7a.waveD` and the bottom-up initialisation `LiteralE7a.initPassB`.

Conclusions:

1. the engine represents the abstract run `RetireFinal.runF` (on which `S^+` and `F_t` are
   defined) at every time;
2. `F_t` (root-reachable live incidences immediately before the wave of rollout `t + 1`)
   is exactly the live incidence set of the implemented engine at that moment;
3. the reference valuations defining `b` are exact valuations of the original circuit, and
   `b_{t+1}(v) ≤ 2`;
4. the deliveries of the engine through `τ` are exactly `S^+` (`eq:s-plus-minus`), and the
   computed rollout work is at least `S^+`;
5. after the final disposal pass no incidence is left;
6. `W ≤ 12 (H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))`, with `H = Hsh R` (see the file
   header) — no term in the depth `L`;
7. the same with `H` read as the given shared work `R.H` alone:
   `W ≤ 12 (R.H + τ + Q·K + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))`;
8. if every rollout has given shared work at least one and every query time given shared
   work at least `K`, then `W ≤ 36 · R.X` (`R.X` the right side of `LiteralK3`, with `H = R.H`). -/
theorem representation_cost_upper_D {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α) :
    (∀ t, SimQ (hrunD R t) (R.run t) ∧ SimQ (hpreD R t) (R.pre t)) ∧
    (∀ t, R.F t = liveInc (hpreD R t).r.G) ∧
    (∀ t, Exact R.G0 (R.refLo t) ∧ Exact R.G0 (R.refHi t)) ∧ (∀ t v, R.b t v ≤ 2) ∧
    (∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus) ∧
    R.Splus ≤ WrollD R ∧
    (∀ p, (disposeAll (List.range R.G0.N) (hpreD R R.τ).r.G).1.children p = []) ∧
    WD R ≤ 12 * XD R ∧
    WD R ≤ 12 * (R.H + R.τ + R.scans + R.P + R.G0.N + live R.G0
      + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)) ∧
    ((∀ t, t < R.τ → 1 ≤ R.h t) → (∀ t, t ≤ R.τ → R.q t = true → R.K ≤ R.h t) →
      WD R ≤ 36 * R.X) := by
  have hK3 := representation_cost_upper R
  have hW := WD_le R
  have hvol : ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus :=
    hK3.2.2.2.1
  refine ⟨fun t => ⟨(simD R t).1, sim_preD R t⟩, fun t => ?_, hK3.2.1, hK3.2.2.1, hvol,
    ?_, fun p => ?_, hW, ?_, fun ha hb => ?_⟩
  · rw [R.F_eq t, (sim_preD R t).r.G]
  · rw [← hvol]
    exact sum_le_sum (fun t _ => (simD R t).2.2)
  · have hG : (hpreD R R.τ).r.G = (R.pre R.τ).r.G := (sim_preD R R.τ).r.G
    have hN : (R.pre R.τ).r.G.N = R.G0.N := (R.pre_inv R.τ).nEq
    rw [hG, ← hN]
    exact disposeAll_empty (R.rooted_all R.τ).2.1 p
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

/-- **`eq:prop-rep-upper` in `O` form**, for any family of runs, with no hypothesis. -/
theorem representation_cost_upper_isBigO_D {α ι : Type*} [LinearOrder α] [OrderBot α]
    {l : Filter ι} (R : ι → SelRun α) :
    (fun i => (WD (R i) : ℝ)) =O[l] (fun i => (XD (R i) : ℝ)) := by
  apply IsBigO.of_bound 12
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast WD_le (R i)

/-- **`prop:representation-cost` as one theorem, with the printed bounds.**

Let `G i` be any family of runs of the Graph-Selective engine with release
(`LiteralK3.SelRun`, executed with `waveD` and bottom-up initialisation; total work
`W_G = WD (G i)`, right side `X_G = XD (G i)` of `eq:prop-rep-upper` with `H = Hsh`), and
let `C i` be ANY family of implementations of the incidence-delivery contract
(`LiteralK4.DeliveryImpl`), over any value type and cell type.  Then

1. `W_G ≤ 12 X_G` for every `i`, i.e. `W_G = O(H + P_G + n_G + e_G + (S_G^+ + e_G) log D_G)`;
2. `P_C + S_C^- ≤ W_C` for every `i` (the bound `Ω(P_C + S_C^-)`, constant 1);
3. condition (R) as printed, `H + P_G + n_G + e_G + (S_G^+ + e_G) log D_G = o(P_C + S_C^-)`,
   implies `W_G = o(W_C)`.

No hypothesis beyond the fields of `SelRun` and `DeliveryImpl`. -/
theorem representation_cost {α β Cell ι : Type*} [LinearOrder α] [OrderBot α]
    [DecidableEq β] [DecidableEq Cell] {l : Filter ι}
    (G : ι → SelRun α) (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WD (G i) ≤ 12 * XD (G i)) ∧
    (fun i => (WD (G i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WD (G i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  have hG := representation_cost_upper_isBigO_D (l := l) G
  exact ⟨fun i => WD_le (G i), hG, fun i => (C i).lower,
    fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)**: against the retirement engine itself as the compiled
representation (`LiteralK4.engineImpl`), the conclusion bounds `W_G` against that engine's
total computed work. -/
theorem condition_R_engine_D {α β ι : Type*} [LinearOrder α] [OrderBot α] [LinearOrder β]
    [OrderBot β] {l : Filter ι} (G : ι → SelRun α) (RC : ι → EngineRun β)
    (hR : (fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WD (G i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
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
  have h1 := (representation_cost (l := l) G (fun i => LiteralK4.engineImpl (RC i))).2.2.2 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast LiteralK4.engineImpl_W_le (RC i)

end Final

end LiteralK10
end JointRootCert
