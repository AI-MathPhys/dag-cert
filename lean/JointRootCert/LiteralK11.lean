/-
Joint Root Certification: `prop:representation-cost` (Unified Full-Cost Representation
Comparison), upper bound `eq:prop-rep-upper`, with the construction of the retirement
candidate list charged.

Manuscript result covered: `prop:representation-cost` (all three sentences), restated from
`LiteralK10` with a larger total work.

## What changes with respect to `LiteralK10`

In `LiteralK10` the engine `LiteralE7a.runSD` reads its retirement candidates from the policy
`EngineFinal.delivV`, which is written as a filter over all `N` gates comparing the stored
values before and after the two waves of the rollout.  That construction is not charged in
`LiteralK10.WD`.  Charged literally it would cost `N` per rollout.

Here the construction is charged at the cost of producing the list from the gates the waves
changed: per rollout `t + 1`,

* `(chgList R t).length`: one unit per gate whose stored value changed in one of the two
  waves (these are exactly the gates popped from the wave stacks of `waveD`);
* `(candList R t).length`: one unit per emitted candidate incidence `(p, g)`.

`candList R t` is, by definition, the list read by the retirement pass and the release
cascade of rollout `t + 1` (`relStepD` passes `delivV` the pre-wave state `hpreD R t` and
the post-wave state `wD1 R t`), and it is the `flatMap` of the parent lists over
`chgList R t` (`candList_eq`).  The total `WDc R = WD R + WcandD R` adds these charges, and
`chgList_length_le` / `candList_length_le` bound them by the live deliveries `volF t`:
`|chgList| + |candList| ≤ 2 + 2 · volF t`.  The key fact is that every changed gate other
than the updated terminal has a changed child (exactness), so it is charged to a delivery.

The final bound is `WDc ≤ 14 · XD` (was `WD ≤ 12 · XD`).
-/
import JointRootCert.LiteralK10

namespace JointRootCert
namespace LiteralK11

open Finset CostEngines DagRetire EngineFinal RetireFinal LiteralK3 LiteralE7a LiteralK10
open HeapImpl (Heap HEState SimE)
open Asymptotics

section Count

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- A gate with a child is a gate (`< N`): it is a parent of that child. -/
lemma lt_of_children_ne {G : Dag} (hG : G.WF) {g : ℕ} (h : G.children g ≠ []) : g < G.N := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h
  exact hG.parent_lt c g ((hG.parents_iff c g).2 hc)

/-- **Changed gates are charged to deliveries.**  For two exact valuations of a well-formed
circuit whose leaves agree except possibly at `x < N`, the number of changed gates is at
most one plus the number of deliveries `Σ_{g changed} |parents g|`. -/
theorem card_changed_le {G : Dag} (hG : G.WF) {o f : ℕ → α} (ho : Exact G o)
    (hf : Exact G f) {x : ℕ} (hx : x < G.N)
    (hl : ∀ g, G.children g = [] → g ≠ x → f g = o g) :
    ((range G.N).filter (fun g => f g ≠ o g)).card
      ≤ 1 + ∑ g ∈ (range G.N).filter (fun g => f g ≠ o g), (G.parents g).length := by
  set S := (range G.N).filter (fun g => f g ≠ o g) with hS
  have hsub : S ⊆ insert x (S.biUnion (fun c => (G.parents c).toFinset)) := by
    intro g hg
    rw [hS, mem_filter] at hg
    by_cases hgx : g = x
    · rw [hgx]; exact mem_insert_self _ _
    apply mem_insert_of_mem
    have hint : G.children g ≠ [] := fun h => hg.2 (hl g h hgx)
    have hex : ∃ c ∈ G.children g, f c ≠ o c := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      exact hg.2 ((hf g hint).trans ((heapMax_congr hne).trans (ho g hint).symm))
    obtain ⟨c, hc, hfc⟩ := hex
    have hcN : c < G.N := by
      by_cases hcl : G.children c = []
      · by_cases hcx : c = x
        · rw [hcx]; exact hx
        · exact absurd (hl c hcl hcx) hfc
      · exact lt_of_children_ne hG hcl
    rw [mem_biUnion]
    exact ⟨c, by rw [hS, mem_filter]; exact ⟨mem_range.2 hcN, hfc⟩,
      List.mem_toFinset.2 ((hG.parents_iff c g).2 hc)⟩
  calc S.card ≤ (insert x (S.biUnion (fun c => (G.parents c).toFinset))).card :=
        card_le_card hsub
    _ ≤ (S.biUnion (fun c => (G.parents c).toFinset)).card + 1 := card_insert_le _ _
    _ ≤ (∑ c ∈ S, (G.parents c).toFinset.card) + 1 := by
        gcongr; exact card_biUnion_le
    _ ≤ (∑ c ∈ S, (G.parents c).length) + 1 := by
        gcongr with c; exact List.toFinset_card_le _
    _ = _ := by ring

omit [LinearOrder α] [OrderBot α] in
lemma length_filter_or_le (N : ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] :
    ((List.range N).filter (fun g => p g ∨ q g)).length
      ≤ ((range N).filter p).card + ((range N).filter q).card := by
  have h := sum_filter_or_le (fun _ => 1) p q (List.range N)
  rw [sum_range_filter (fun _ => 1) p N, sum_range_filter (fun _ => 1) q N] at h
  simpa using h

end Count

section Engine

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α)

/-- Implemented state after the two `waveD` waves of rollout `t + 1`. -/
def wD1 (t : ℕ) : HRState α := (waveStepD (R.u (t + 1)) (hpreD R t).r).1

/-- The gates whose stored value changed in one of the two waves of rollout `t + 1`. -/
def chgList (t : ℕ) : List ℕ :=
  (List.range (hpreD R t).r.G.N).filter (fun g =>
    (wD1 R t).lo.val g ≠ (hpreD R t).r.lo.val g ∨ (wD1 R t).hi.val g ≠ (hpreD R t).r.hi.val g)

/-- The retirement candidate list of rollout `t + 1`: exactly the list that `relStepD`
(through `LiteralE4.tailStep`) reads from the policy `delivV`. -/
def candList (t : ℕ) : List (ℕ × ℕ) :=
  delivV (hpreD R t).r.G (hpreD R t).r.lo.val (hpreD R t).r.hi.val
    (wD1 R t).lo.val (wD1 R t).hi.val

/-- `relStepD` at rollout `t + 1` reads the candidate list `candList R t`. -/
lemma relStepD_eq (t : ℕ) :
    relStepD R.K R.rt delivV (R.u (t + 1)) (hpreD R t)
      = ((LiteralE4.tailStep R.K R.rt (fun _ _ _ _ _ => candList R t) (hpreD R t)
            (wD1 R t)).1,
         (waveStepD (R.u (t + 1)) (hpreD R t).r).2
          + (LiteralE4.tailStep R.K R.rt (fun _ _ _ _ _ => candList R t) (hpreD R t)
              (wD1 R t)).2) := rfl

/-- The candidate list is produced from the changed gates: their parent incidences. -/
lemma candList_eq (t : ℕ) :
    candList R t = (chgList R t).flatMap
      (fun g => ((hpreD R t).r.G.parents g).map (fun p => (p, g))) := rfl

/-- Charge for building the candidate lists of all rollouts `1..τ`: one unit per changed
gate and one per emitted candidate. -/
def WcandD : ℕ := ∑ t ∈ range R.τ, ((chgList R t).length + (candList R t).length)

/-- **Total scalar work with the candidate-list construction charged.** -/
def WDc : ℕ := WD R + WcandD R

lemma cand_charge_le (t : ℕ) :
    (chgList R t).length + (candList R t).length
      ≤ 2 + 2 * volF R.K R.rt delivCand R.u R.q R.s0 t := by
  have hpS := sim_preD R t
  have hinv : CInv R.G0 R.K R.rt (R.pre t).r (R.pre t).act _ _ :=
    preF_inv (K := R.K) (rt := R.rt) (cand := delivCand) (q := R.q)
      (act0 := fun _ => true) R.wf R.init_facts.2.1 R.hn t
  have eG : (hpreD R t).r.G = (R.pre t).r.G := hpS.r.G
  have hxs : (R.u (t + 1)).1 < (R.pre t).r.G.N := by rw [hinv.nEq]; exact (R.hn t).1
  obtain ⟨l1, -, -⟩ := waveD_spec hinv.wf (R.u (t + 1)).1 (R.u (t + 1)).2.1 (hpreD R t).r.lo
    (R.pre t).r.lo hxs hpS.r.lo hinv.invLo
  obtain ⟨u1, -, -⟩ := waveD_spec hinv.wf (R.u (t + 1)).1 (R.u (t + 1)).2.2 (hpreD R t).r.hi
    (R.pre t).r.hi hxs hpS.r.hi hinv.invHi
  obtain ⟨wl1, -, wl3, -⟩ := wave_spec hinv.wf (R.u (t + 1)).1 (R.u (t + 1)).2.1
    (R.pre t).r.lo hxs hinv.invLo
  obtain ⟨wu1, -, wu3, -⟩ := wave_spec hinv.wf (R.u (t + 1)).1 (R.u (t + 1)).2.2
    (R.pre t).r.hi hxs hinv.invHi
  have vlo : (wD1 R t).lo.val
      = (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1.val := by
    show (waveD (hpreD R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (hpreD R t).r.lo).1.val = _
    rw [eG]; exact l1.val
  have vhi : (wD1 R t).hi.val
      = (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1.val := by
    show (waveD (hpreD R t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (hpreD R t).r.hi).1.val = _
    rw [eG]; exact u1.val
  -- the volume of the rollout
  obtain ⟨e1, e2, -⟩ := rstep_endpoints delivCand (R.u (t + 1)) (R.pre t).r
  have elo : (R.run (t + 1)).r.lo
      = (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1 := e1
  have ehi : (R.run (t + 1)).r.hi
      = (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1 := e2
  have hv : volF R.K R.rt delivCand R.u R.q R.s0 t
      = vol (R.pre t).r.G (R.pre t).r.lo
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1
        + vol (R.pre t).r.G (R.pre t).r.hi
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1 := by
    show vol (R.pre t).r.G (R.pre t).r.lo (R.run (t + 1)).r.lo
      + vol (R.pre t).r.G (R.pre t).r.hi (R.run (t + 1)).r.hi = _
    rw [elo, ehi]
  -- candidate list
  have hc : candList R t
      = delivCand (R.pre t).r (waveStep (R.u (t + 1)) (R.pre t).r).1 := by
    unfold candList delivV delivCand
    rw [vlo, vhi, hpS.r.lo.val, hpS.r.hi.val, eG]
    rfl
  have hcl : (candList R t).length
      ≤ vol (R.pre t).r.G (R.pre t).r.lo
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1
        + vol (R.pre t).r.G (R.pre t).r.hi
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1 := by
    rw [hc]
    exact delivCand_length (R.pre t).r (waveStep (R.u (t + 1)) (R.pre t).r).1
  -- changed gates
  have hch : (chgList R t).length
      ≤ ((range (R.pre t).r.G.N).filter (fun g =>
            (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1.val g
              ≠ (R.pre t).r.lo.val g)).card
        + ((range (R.pre t).r.G.N).filter (fun g =>
            (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1.val g
              ≠ (R.pre t).r.hi.val g)).card := by
    unfold chgList
    rw [vlo, vhi, hpS.r.lo.val, hpS.r.hi.val, eG]
    exact length_filter_or_le _ _ _
  have cl : ((range (R.pre t).r.G.N).filter (fun g =>
            (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1.val g
              ≠ (R.pre t).r.lo.val g)).card
      ≤ 1 + vol (R.pre t).r.G (R.pre t).r.lo
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.1 (R.pre t).r.lo).1 :=
    card_changed_le hinv.wf (inv_exact hinv.invLo) (inv_exact wl1) hxs wl3
  have cu : ((range (R.pre t).r.G.N).filter (fun g =>
            (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1.val g
              ≠ (R.pre t).r.hi.val g)).card
      ≤ 1 + vol (R.pre t).r.G (R.pre t).r.hi
          (wave (R.pre t).r.G (R.u (t + 1)).1 (R.u (t + 1)).2.2 (R.pre t).r.hi).1 :=
    card_changed_le hinv.wf (inv_exact hinv.invHi) (inv_exact wu1) hxs wu3
  rw [hv]
  omega

/-- The candidate-list charge over the whole run: at most `2τ + 2 S^+`. -/
theorem WcandD_le : WcandD R ≤ 2 * R.τ + 2 * R.Splus := by
  have hvol : ∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus :=
    sum_congr rfl (fun t _ => R.volF_eq t)
  calc WcandD R ≤ ∑ t ∈ range R.τ, (2 + 2 * volF R.K R.rt delivCand R.u R.q R.s0 t) :=
        sum_le_sum (fun t _ => cand_charge_le R t)
    _ = 2 * R.τ + 2 * R.Splus := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum, hvol]
        ring

/-- **The work bound with the candidate lists charged**, no level term. -/
theorem WDc_le : WDc R ≤ 14 * XD R := by
  have h1 := WD_le R
  have h2 := WcandD_le R
  have h3 : R.Splus ≤ (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1) :=
    le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  unfold WDc
  unfold XD Hsh at h1 ⊢
  generalize (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1) = Y at *
  omega

end Engine

/-! ## `prop:representation-cost` with the charged total -/

section Final

/-- **`prop:representation-cost`, upper bound `eq:prop-rep-upper`, with the candidate-list
construction charged.**

Same hypotheses as `LiteralK10.representation_cost_upper_D` (only the fields of
`R : LiteralK3.SelRun α`).  Conclusions:

1. the engine represents the abstract run `RetireFinal.runF` at every time;
2. `F_t` is the live incidence set of the implemented engine before the wave of rollout
   `t + 1`;
3. the reference valuations are exact and `b_{t+1}(v) ≤ 2`;
4. the deliveries through `τ` are exactly `S^+`, and the computed rollout work is at least
   `S^+`;
5. after the final disposal pass no incidence is left;
6. the candidate list read by rollout `t + 1` is the parent incidences of the gates changed
   by its waves, and building it (one unit per changed gate, one per candidate) costs at
   most `2 + 2 · (deliveries of rollout t + 1)`; over the run at most `2τ + 2 S^+`;
7. `WDc ≤ 14 (H + P + n + e + (S^+ + e)(⌈log₂ D⌉ + 1))`, with `H = Hsh R`, where
   `WDc = WD + (candidate-list charge)`;
8. the same with `H` written as `R.H + τ + Q·K`;
9. if every rollout has given shared work at least one and every query time given shared
   work at least `K`, then `WDc ≤ 42 · R.X`. -/
theorem representation_cost_upper_D {α : Type*} [LinearOrder α] [OrderBot α] (R : SelRun α) :
    (∀ t, SimQ (hrunD R t) (R.run t) ∧ SimQ (hpreD R t) (R.pre t)) ∧
    (∀ t, R.F t = liveInc (hpreD R t).r.G) ∧
    (∀ t, Exact R.G0 (R.refLo t) ∧ Exact R.G0 (R.refHi t)) ∧ (∀ t v, R.b t v ≤ 2) ∧
    (∑ t ∈ range R.τ, volF R.K R.rt delivCand R.u R.q R.s0 t = R.Splus) ∧
    R.Splus ≤ WrollD R ∧
    (∀ p, (disposeAll (List.range R.G0.N) (hpreD R R.τ).r.G).1.children p = []) ∧
    (∀ t, candList R t = (chgList R t).flatMap
        (fun g => ((hpreD R t).r.G.parents g).map (fun p => (p, g))) ∧
      (chgList R t).length + (candList R t).length
        ≤ 2 + 2 * volF R.K R.rt delivCand R.u R.q R.s0 t) ∧
    WcandD R ≤ 2 * R.τ + 2 * R.Splus ∧
    WDc R ≤ 14 * XD R ∧
    WDc R ≤ 14 * (R.H + R.τ + R.scans + R.P + R.G0.N + live R.G0
      + (R.Splus + live R.G0) * (Nat.clog 2 R.D + 1)) ∧
    ((∀ t, t < R.τ → 1 ≤ R.h t) → (∀ t, t ≤ R.τ → R.q t = true → R.K ≤ R.h t) →
      WDc R ≤ 42 * R.X) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, -, -, -⟩ := LiteralK10.representation_cost_upper_D R
  have hW := WDc_le R
  refine ⟨a1, a2, a3, a4, a5, a6, a7, fun t => ⟨candList_eq R t, cand_charge_le R t⟩,
    WcandD_le R, hW, ?_, fun ha hb => ?_⟩
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

/-- **`eq:prop-rep-upper` in `O` form** with the charged total, for any family of runs. -/
theorem representation_cost_upper_isBigO_D {α ι : Type*} [LinearOrder α] [OrderBot α]
    {l : Filter ι} (R : ι → SelRun α) :
    (fun i => (WDc (R i) : ℝ)) =O[l] (fun i => (XD (R i) : ℝ)) := by
  apply IsBigO.of_bound 14
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast WDc_le (R i)

/-- **`prop:representation-cost` as one theorem**, with the candidate-list construction
charged in the total work `W_G = WDc (G i)`; `C i` is any family of implementations of the
incidence-delivery contract (`LiteralK4.DeliveryImpl`).

1. `W_G ≤ 14 X_G` for every `i`, hence `W_G = O(X_G)`;
2. `P_C + S_C^- ≤ W_C` for every `i`;
3. condition (R), `X_G = o(P_C + S_C^-)`, implies `W_G = o(W_C)`. -/
theorem representation_cost {α β Cell ι : Type*} [LinearOrder α] [OrderBot α]
    [DecidableEq β] [DecidableEq Cell] {l : Filter ι}
    (G : ι → SelRun α) (C : ι → LiteralK4.DeliveryImpl β Cell) :
    (∀ i, WDc (G i) ≤ 14 * XD (G i)) ∧
    (fun i => (WDc (G i) : ℝ)) =O[l] (fun i => (XD (G i) : ℝ)) ∧
    (∀ i, (C i).P + (C i).Sminus ≤ (C i).W) ∧
    ((fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) →
      (fun i => (WDc (G i) : ℝ)) =o[l] (fun i => ((C i).W : ℝ))) := by
  have hC : (fun i => (((C i).P + (C i).Sminus : ℕ) : ℝ)) =O[l] (fun i => ((C i).W : ℝ)) := by
    apply IsBigO.of_bound 1
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
      one_mul]
    exact_mod_cast (C i).lower
  have hG := LiteralK11.representation_cost_upper_isBigO_D (l := l) G
  exact ⟨fun i => WDc_le (G i), hG, fun i => (C i).lower,
    fun hR => (hG.trans_isLittleO hR).trans_isBigO hC⟩

/-- **Non-vacuity of (R)** with the charged total: against the retirement engine itself as
the compiled representation (`LiteralK4.engineImpl`). -/
theorem condition_R_engine_D {α β ι : Type*} [LinearOrder α] [OrderBot α] [LinearOrder β]
    [OrderBot β] {l : Filter ι} (G : ι → SelRun α) (RC : ι → EngineRun β)
    (hR : (fun i => (XD (G i) : ℝ)) =o[l] (fun i => (((RC i).P + (RC i).Sminus : ℕ) : ℝ))) :
    (fun i => (WDc (G i) : ℝ)) =o[l] (fun i => ((RC i).W : ℝ)) := by
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
  have h1 := (LiteralK11.representation_cost (l := l) G
    (fun i => LiteralK4.engineImpl (RC i))).2.2.2 hR'
  refine h1.trans_isBigO ?_
  apply IsBigO.of_bound 1
  refine Filter.Eventually.of_forall (fun i => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  exact_mod_cast LiteralK4.engineImpl_W_le (RC i)

end Final

end LiteralK11
end JointRootCert
