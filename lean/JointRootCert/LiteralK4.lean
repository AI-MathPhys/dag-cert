/-
Joint Root Certification: `prop:representation-cost`, the lower bound `Ω(P_C + S_C^-)` for
EVERY implementation of the incidence-delivery contract, and condition (R), as one
theorem without a hypothesis on the compiled work.

Manuscript result covered:

* `prop:representation-cost` (Unified Full-Cost Representation Comparison), second and
  third sentences: "any compiled representation `C` executing this incidence-delivery
  contract incurs at least `Ω(P_C + S_C^-)` scalar operations, even with online incidence
  retirement and shared terminal evidence.  Consequently `G` achieves an asymptotic
  total-work advantage over `C` whenever
  `H + P_G + n_G + e_G + (S_G^+ + e_G) log D_G = o(P_C + S_C^-)`" (condition (R)).

IMPORTS `JointRootCert.LiteralK3` (a new file; build it first).

## The formal contract (the manuscript does not define "this incidence-delivery contract")

`DeliveryImpl α Cell` packages an implementation `C`:

* gates `0, …, N-1`; `F t` the set of incidences `(parent, child)` live after wave `t`
  (`F t ⊆ F (t-1)`: incidences may be retired online, never created);
* `lo t v`, `hi t v`: the endpoint values of gate `v` after wave `t` (so
  `b_t(v) ∈ {0,1,2}` is determined);
* a memory `mem t : Cell → α` after wave `t`, over an arbitrary cell type, and for each
  wave a list `ops t` of scalar operations, each writing at most one cell and costing one
  unit (`DagRetire.applyOps`); `mem t` is `mem (t-1)` with `ops t` applied;
* an injective assignment `keyCell` of a memory cell to every pair (endpoint, incidence);
* upfront work `P`;
* **the contract**: at the conclusion of every wave `t ≤ τ`, for every incidence `(p, c)`
  live in `F t` and each endpoint, the key cell of `(p, c)` holds the current endpoint
  value of `c`.

`W_C := P + Σ_{t=1}^{τ} |ops t|` and `S_C^- := Σ_{t=1}^{τ} Σ_{v<N} b_t(v) d⁻_{F_t}(v)`.

`DeliveryImpl.lower` proves `P + S^- ≤ W` for every such implementation.  The structure is
inhabited by the retirement engine on implemented heaps (`engineImpl`).

The endpoint functions `lo`, `hi` are not required to be the exact evaluation of a circuit
(the bound does not use it; for a compiled circuit they are its exact evaluation, as for
`engineImpl`).  Initialisation, disposal and all work that writes no memory cell are not
counted in `W_C` beyond the given number `P`, which only makes the lower bound stronger.

## How an implementation escapes the contract

The bound is a statement about implementations that store, for every live incidence, a
per-incidence copy of the child's endpoints.  An implementation that keeps no
per-incidence keys (for example a flat or alias oracle that reads the child value through
a shared pointer when it needs it, cf. `prop:v2escape`), or one that lets key cells of
live incidences go stale and repairs them lazily, is not a `DeliveryImpl` and the bound
says nothing about it.
-/
import JointRootCert.LiteralK3

namespace JointRootCert
namespace LiteralK4

open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3
open Asymptotics

/-! ## The contract and the lower bound -/

section Contract

/-- `Σ_{v<N} b(v) d⁻_F(v) = Σ_{e ∈ F} b(child e)` when all children are gates. -/
lemma delivVol_eq_sum {N : ℕ} {F : Finset (ℕ × ℕ)} (h : ∀ e ∈ F, e.2 < N) (b : ℕ → ℕ) :
    delivVol N F b = ∑ e ∈ F, b e.2 := by
  unfold delivVol dIn
  rw [← sum_fiberwise_of_maps_to (g := fun e : ℕ × ℕ => e.2) (t := range N)
    (fun e he => mem_range.2 (h e he)) (fun e => b e.2)]
  apply sum_congr rfl
  intro v _
  symm
  calc ∑ e ∈ F.filter (fun e => e.2 = v), b e.2
      = ∑ _e ∈ F.filter (fun e => e.2 = v), b v :=
        sum_congr rfl (fun e he => by rw [(mem_filter.1 he).2])
    _ = b v * (F.filter (fun e => e.2 = v)).card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **An implementation of the incidence-delivery contract** (see the file header). -/
structure DeliveryImpl (α : Type*) [DecidableEq α] (Cell : Type*) [DecidableEq Cell] where
  /-- number of gates -/
  N : ℕ
  /-- number of waves (stopping time) -/
  τ : ℕ
  /-- upfront work -/
  P : ℕ
  /-- live incidences `(parent, child)` after wave `t` -/
  F : ℕ → Finset (ℕ × ℕ)
  /-- lower endpoint of gate `v` after wave `t` -/
  lo : ℕ → ℕ → α
  /-- upper endpoint of gate `v` after wave `t` -/
  hi : ℕ → ℕ → α
  /-- memory after wave `t` -/
  mem : ℕ → Cell → α
  /-- scalar operations of wave `t`; each writes at most one cell -/
  ops : ℕ → List (Option (Cell × α))
  /-- the key cell of an (endpoint, incidence) pair -/
  keyCell : Bool × (ℕ × ℕ) → Cell
  keyCell_inj : Function.Injective keyCell
  child_lt : ∀ t, ∀ e ∈ F t, e.2 < N
  retire : ∀ t ∈ Icc 1 τ, F t ⊆ F (t - 1)
  exec : ∀ t ∈ Icc 1 τ, mem t = applyOps (ops t) (mem (t - 1))
  /-- the delivery contract -/
  contract : ∀ t ≤ τ, ∀ e ∈ F t,
    mem t (keyCell (false, e)) = lo t e.2 ∧ mem t (keyCell (true, e)) = hi t e.2

namespace DeliveryImpl

variable {α : Type*} [DecidableEq α] {Cell : Type*} [DecidableEq Cell]
  (C : DeliveryImpl α Cell)

/-- `b_t(v) ∈ {0, 1, 2}`: the number of endpoints of gate `v` changed by wave `t ≥ 1`. -/
def b (t v : ℕ) : ℕ := bChg (C.lo (t - 1)) (C.hi (t - 1)) (C.lo t) (C.hi t) v

/-- **`S_C^-` of `eq:s-plus-minus`**: `Σ_{t=1}^{τ} Σ_{v<N} b_t(v) · d⁻_{F_t}(v)`, with
`F_t` the incidences live at the conclusion of wave `t`. -/
def Sminus : ℕ := ∑ t ∈ Icc 1 C.τ, delivVol C.N (C.F t) (C.b t)

/-- **Total work `W_C`**: upfront work plus the scalar operations of all waves. -/
def W : ℕ := C.P + ∑ t ∈ Icc 1 C.τ, (C.ops t).length

lemma b_le_two (t v : ℕ) : C.b t v ≤ 2 := bChg_le_two _ _ _ _ v

/-- **Lower bound `P_C + S_C^- ≤ W_C` for every implementation of the contract.**  No
hypothesis beyond the fields of `DeliveryImpl`: nothing is assumed about scheduling,
sharing, retirement policy or the rest of the memory. -/
theorem lower : C.P + C.Sminus ≤ C.W := by
  unfold Sminus W
  apply Nat.add_le_add_left
  apply sum_le_sum
  intro t ht
  have ht1 : 1 ≤ t ∧ t ≤ C.τ := mem_Icc.1 ht
  rw [delivVol_eq_sum (C.child_lt t)]
  have hlen := changed_le_length
    (((univ : Finset Bool) ×ˢ C.F t).map ⟨C.keyCell, C.keyCell_inj⟩) (C.ops t) (C.mem (t - 1))
  rw [← C.exec t ht, filter_map, card_map] at hlen
  refine le_trans ?_ hlen
  rw [card_filter, sum_product, Fintype.sum_bool, ← sum_add_distrib]
  apply sum_le_sum
  intro e he
  have c1 := C.contract t ht1.2 e he
  have c0 := C.contract (t - 1) (by omega) e (C.retire t ht he)
  show bChg (C.lo (t - 1)) (C.hi (t - 1)) (C.lo t) (C.hi t) e.2
    ≤ (if C.mem t (C.keyCell (true, e)) ≠ C.mem (t - 1) (C.keyCell (true, e)) then 1 else 0)
      + (if C.mem t (C.keyCell (false, e)) ≠ C.mem (t - 1) (C.keyCell (false, e))
          then 1 else 0)
  unfold bChg
  rw [add_comm]
  apply Nat.add_le_add
  · by_cases hch : C.hi t e.2 ≠ C.hi (t - 1) e.2
    · have hm : C.mem t (C.keyCell (true, e)) ≠ C.mem (t - 1) (C.keyCell (true, e)) := by
        rw [c1.2, c0.2]; exact hch
      rw [ite_eq_left hch, ite_eq_left hm]
    · rw [ite_eq_right hch]
      exact Nat.zero_le _
  · by_cases hch : C.lo t e.2 ≠ C.lo (t - 1) e.2
    · have hm : C.mem t (C.keyCell (false, e)) ≠ C.mem (t - 1) (C.keyCell (false, e)) := by
        rw [c1.1, c0.1]; exact hch
      rw [ite_eq_left hch, ite_eq_left hm]
    · rw [ite_eq_right hch]
      exact Nat.zero_le _

end DeliveryImpl

end Contract

/-! ## The contract is satisfied by the implemented engine -/

section Engine

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **The retirement engine on implemented heaps is an implementation of the contract.**
Its cells are the heap keys `(endpoint, (parent, child))` (`EngineFinal.memH`), its
operations are the key writes `EngineFinal.stepOps` of each rollout, and the contract is
`EngineFinal.rrunH_trace`. -/
def engineImpl (R : EngineRun α) : DeliveryImpl α (Bool × (ℕ × ℕ)) where
  N := R.G0.N
  τ := R.τ
  P := R.P
  F := fun t => liveInc (rrunH delivV R.u R.hs0 t).G
  lo := fun t => (rrunH delivV R.u R.hs0 t).lo.val
  hi := fun t => (rrunH delivV R.u R.hs0 t).hi.val
  mem := fun t => memH (rrunH delivV R.u R.hs0 t)
  ops := fun t => stepOps (liftCand delivV) (R.u t) (rrun (liftCand delivV) R.u R.s0 (t - 1))
  keyCell := id
  keyCell_inj := Function.injective_id
  child_lt := by
    intro t e he
    have hN : (rrunH delivV R.u R.hs0 t).G.N = R.G0.N := by
      rw [(R.sim t).G]
      exact (rrun_inv R.init_sim.2.1 R.nestedRun t).nEq
    have h2 := (mem_product.1 (mem_filter.1 he).1).2
    rw [hN] at h2
    exact mem_range.1 h2
  retire := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
    exact (rrunH_trace delivV R.u R.init_sim.1 R.init_sim.2.1 R.nestedRun).1 t'
  exec := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
    exact (rrunH_trace delivV R.u R.init_sim.1 R.init_sim.2.1 R.nestedRun).2.1 t'
  contract := fun t _ e he =>
    (rrunH_trace delivV R.u R.init_sim.1 R.init_sim.2.1 R.nestedRun).2.2.1 t e he

/-- The work of the engine as a contract implementation (its key writes) is at most its
total computed work. -/
theorem engineImpl_W_le (R : EngineRun α) : (engineImpl R).W ≤ R.W := by
  have c4 := (rrunH_trace delivV R.u R.init_sim.1 R.init_sim.2.1 R.nestedRun).2.2.2
  have hB : ∀ t ∈ Icc 1 R.τ,
      (stepOps (liftCand delivV) (R.u t) (rrun (liftCand delivV) R.u R.s0 (t - 1))).length
        ≤ stepCostH delivV R.u R.hs0 (t - 1) := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
    exact c4 t'
  have h1 : ∑ t ∈ Icc 1 R.τ,
      (stepOps (liftCand delivV) (R.u t) (rrun (liftCand delivV) R.u R.s0 (t - 1))).length
      ≤ ∑ t ∈ range R.τ, stepCostH delivV R.u R.hs0 t := by
    rw [← sum_Icc_pred]
    exact sum_le_sum hB
  show R.P + ∑ t ∈ Icc 1 R.τ,
      (stepOps (liftCand delivV) (R.u t) (rrun (liftCand delivV) R.u R.s0 (t - 1))).length
    ≤ R.P + ((initPassH R.G0 R.order R.hl).2 + (initPassH R.G0 R.order R.hu).2)
      + ∑ t ∈ range R.τ, stepCostH delivV R.u R.hs0 t
  omega

/-- The `S^-` of the engine as a contract implementation is the `S^-` of
`EngineFinal.EngineRun`. -/
theorem engineImpl_Sminus (R : EngineRun α) : (engineImpl R).Sminus = R.Sminus := by
  have hI := rrun_inv R.init_sim.2.1 R.nestedRun
  have hA : ∀ t ∈ Icc 1 R.τ,
      delivVol (engineImpl R).N ((engineImpl R).F t) ((engineImpl R).b t)
        = stepMinus delivCand R.u R.s0 (t - 1) := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (mem_Icc.1 ht).1; omega⟩
    rw [delivVol_eq_sum ((engineImpl R).child_lt (t' + 1))]
    show ∑ e ∈ liveInc (rrunH delivV R.u R.hs0 (t' + 1)).G,
        ((if (rrunH delivV R.u R.hs0 (t' + 1)).lo.val e.2
              ≠ (rrunH delivV R.u R.hs0 t').lo.val e.2 then 1 else 0)
          + (if (rrunH delivV R.u R.hs0 (t' + 1)).hi.val e.2
              ≠ (rrunH delivV R.u R.hs0 t').hi.val e.2 then 1 else 0))
      = stepMinus delivCand R.u R.s0 t'
    rw [(R.sim (t' + 1)).G, (R.sim (t' + 1)).lo.val, (R.sim (t' + 1)).hi.val,
      (R.sim t').lo.val, (R.sim t').hi.val]
    exact liveInc_delivery (hI (t' + 1)).wf _ _ _ _
  unfold DeliveryImpl.Sminus EngineRun.Sminus
  show ∑ t ∈ Icc 1 R.τ, delivVol (engineImpl R).N ((engineImpl R).F t) ((engineImpl R).b t) = _
  rw [sum_congr rfl hA, sum_Icc_pred]

end Engine

/-! ## `prop:representation-cost`: lower bound and condition (R) -/

section Final

/-- **`prop:representation-cost`, second and third sentences, as one theorem.**

Let `G i` be a family of runs of the Graph-Selective engine with release
(`LiteralK3.SelRun`, total computed work `W_G` and right side `X_G` of
`eq:prop-rep-upper` as in `LiteralK3.representation_cost_upper`), and let `C i` be ANY
family of implementations of the incidence-delivery contract (`DeliveryImpl`), over any
value type and cell type.  Then:

1. `P_C + S_C^- ≤ W_C` for every `i` (the bound `Ω(P_C + S_C^-)`, with constant 1);
2. if `τ(L+3) + Q·K + H + P_G + n_G + e_G + (S_G^+ + e_G)(⌈log₂ D_G⌉ + 1) = o(P_C + S_C^-)`
   along the filter `l`, then `W_G = o(W_C)`;
3. if the shared work of every rollout of `G` is at least the circuit depth (`ha`) and the
   shared work at every query time is at least `K` (`hb`), and condition (R) holds as
   printed, `H + P_G + n_G + e_G + (S_G^+ + e_G)(⌈log₂ D_G⌉ + 1) = o(P_C + S_C^-)`, then
   `W_G = o(W_C)`.

No hypothesis is made about `C` other than being a `DeliveryImpl`; the hypotheses `ha`,
`hb` concern `G` only and are the ones of `LiteralK3.representation_cost_upper`, item 7. -/
theorem representation_cost_lower_and_R {α β Cell ι : Type*} [LinearOrder α] [OrderBot α]
    [DecidableEq β] [DecidableEq Cell] {l : Filter ι}
    (G : ι → SelRun α) (C : ι → DeliveryImpl β Cell) :
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => ((G i).X1 : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => ((G i).W : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) ∧
    ((∀ i t, t < (G i).τ → (G i).G0.L + 3 ≤ (G i).h t) →
      (∀ i t, t ≤ (G i).τ → (G i).q t = true → (G i).K ≤ (G i).h t) →
      (fun i => ((G i).X : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => ((G i).W : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  refine ⟨fun i => (C i).lower, fun hR => ?_, fun ha hb hR => ?_⟩
  · have hG : (fun i => ((G i).W : ℝ)) =O[l] (fun i => ((G i).X1 : ℝ)) := by
      apply IsBigO.of_bound 12
      refine Filter.Eventually.of_forall (fun i => ?_)
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (representation_cost_upper (G i)).2.2.2.2.2.1
    exact (hG.trans_isLittleO hR).trans_isBigO hC
  · exact ((representation_cost_upper_isBigO G ha hb).trans_isLittleO hR).trans_isBigO hC

/-- **Non-vacuity**: condition (R) against the retirement engine itself as the compiled
representation.  With `C i` the engine of `EngineFinal.EngineRun` run on a compiled
circuit, viewed as a contract implementation through `engineImpl`, the conclusion bounds
`W_G` against the engine's total computed work `(RC i).W`. -/
theorem condition_R_engine {α β ι : Type*} [LinearOrder α] [OrderBot α] [LinearOrder β]
    [OrderBot β] {l : Filter ι} (G : ι → SelRun α) (RC : ι → EngineRun β)
    (hR : (fun i => ((G i).X1 : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => ((G i).W : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
  have hR' : (fun i => ((G i).X1 : ℝ))
      =o[l] (fun i => (((engineImpl (RC i)).P + (engineImpl (RC i)).Sminus : ℕ) : ℝ)) := by
    have e : (fun i => (((engineImpl (RC i)).P + (engineImpl (RC i)).Sminus : ℕ) : ℝ))
        = (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ)) := by
      funext i
      rw [engineImpl_Sminus]
      rfl
    rw [e]
    exact hR
  have h1 := (representation_cost_lower_and_R (l := l) G (fun i => engineImpl (RC i))).2.1 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast engineImpl_W_le (RC i)

end Final

end LiteralK4
end JointRootCert
