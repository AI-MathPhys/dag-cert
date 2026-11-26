/-
Theorem `thm:ta-core` (Wide Common-Core Support Compilation Cost), the cover clause and the
flat clause as statements about work.

* **Cover clause.**  The dyadic-cover index is run as the stopping monitor of the search on
  the actual Hoeffding boxes `coreBox`.  The monitor state is a pair of dual-cover indexes
  (one for the lower, one for the upper endpoints) on the implemented heap of
  `HeapImpl.lean`.  It is initialised by the costed program `DualCoverFinal.dcInit` from the
  box at the first query; after each rollout it compares the two endpoints of the observed
  terminal with their stored values and calls `HeapImpl.dcUpdateH` exactly for the endpoints
  that changed (`cvStep`).  A root query reads the root of every action heap
  (`HeapImpl.findMax`).  It is proved that at every step the values read are the exact
  root-action endpoints (`cv_exact`), so the leader/stop output equals that of the eager and
  of the selective graph monitor at every step (`cv_stops_iff`); hence the three monitors
  have the same stopping time and recommendation.  The total work `cvTotalWork` counts:
  reading and disposing of the graph, the sampler traversal of every rollout, the compile
  phase, the two costed initialisations, every update, every query, and the disposal of the
  index; it is `O(r² log² r)` (`ta_core_literal`).
* **Flat clause.**  `flatSupp` is a costed program that materialises the flat
  root-to-terminal support of a root action from its subgraph, one unit per vertex visited
  and one cell per terminal written.  Its output is the support (`flatSupp_coreAct`) and its
  cost on the `r + 1` root actions is at least `Σ_a |S(a)| ≥ r³` (`coreFlat_cost_ge`).
  Moreover every family of explicit lists that contains the supports has at least `r³`
  cells (`flat_cells_ge`), so the bound holds for every program that writes one cell per
  unit.

The UCT search is `CoreSearch` of `UCTWork.lean` (index `Q + 2 √(log (1 + t) / N)`, as in
the manuscript's proof of this theorem).  The run lists of the supports under the contiguous
layout are given explicitly (`coreRunList`), and the compile cost is that of
`CostModel.compileAll` on them.  A query is charged `4 (r + 1)`: one read per action and
endpoint and two scans for the leader and the stopping bit.
-/
import JointRootCert.CoreCovers
import JointRootCert.DualCoverFinal

namespace JointRootCert
namespace LiteralE

open Finset
open _root_.JointRootCert.Representation _root_.JointRootCert.CostModel
open HeapImpl (Heap Rep findMax HState Sim dcUpdateH)
open DualCoverFinal (dcInit dcInitAbs)

noncomputable section

/-! ### Terminals of a circuit and the MAX value as a supremum -/

section Terms

variable {Z : Type*} [DecidableEq Z]

/-- The set of terminals below a vertex. -/
def mcTerms : MaxCirc Z → Finset Z
  | .term z => {z}
  | .unary c => mcTerms c
  | .bin c d => mcTerms c ∪ mcTerms d

/-- The MAX value of a vertex is the supremum of the terminal values over its support. -/
theorem mcEval_eq_sup (g : Z → ℝ) : ∀ c : MaxCirc Z,
    ((MaxCirc.eval g c : ℝ) : WithBot ℝ) = (mcTerms c).sup (fun z => ((g z : ℝ) : WithBot ℝ))
  | .term z => by simp [mcTerms, MaxCirc.eval]
  | .unary c => mcEval_eq_sup g c
  | .bin c d => by
      show ((max (MaxCirc.eval g c) (MaxCirc.eval g d) : ℝ) : WithBot ℝ) = _
      rw [mcTerms, Finset.sup_union, ← mcEval_eq_sup g c, ← mcEval_eq_sup g d]
      exact WithBot.coe_max _ _

theorem mcTerms_uctBal (leaf : ℕ → Z) : ∀ d lo len, 1 ≤ len → len ≤ 2 ^ d →
    mcTerms (uctBal leaf d lo len) = (Ico lo (lo + len)).image leaf
  | 0, lo, len, h1, h2 => by
      have : len = 1 := by simpa using le_antisymm h2 h1
      subst this
      simp [uctBal, mcTerms]
  | d + 1, lo, len, h1, h2 => by
      unfold uctBal
      split_ifs with h
      · have : len = 1 := le_antisymm h h1
        subst this
        simp [mcTerms]
      · have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
        rw [mcTerms, mcTerms_uctBal leaf d lo ((len + 1) / 2) (by omega) (by omega),
          mcTerms_uctBal leaf d (lo + (len + 1) / 2) (len / 2) (by omega) (by omega),
          ← Finset.image_union]
        congr 1
        have e : lo + (len + 1) / 2 + len / 2 = lo + len := by omega
        rw [e]
        exact Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)

end Terms

/-- The terminals below a root action of the common-core DAG are its support. -/
theorem mcTerms_coreAct (r : ℕ) [NeZero r] (a : Fin (r + 1)) :
    mcTerms (coreAct r a) = coreSupp r a := by
  have hpos : 1 ≤ r ^ 2 := Nat.pos_of_ne_zero (NeZero.ne _)
  unfold coreAct coreSupp
  by_cases h : (a : ℕ) < r
  · rw [dite_eq_left h, dite_eq_left h]
    have hhub : mcTerms (coreHub r) = (Ico 0 (0 + r ^ 2)).image (coreLeaf r) :=
      mcTerms_uctBal (coreLeaf r) _ 0 (r ^ 2) hpos (Nat.le_pow_clog (by norm_num) _)
    show mcTerms (coreHub r) ∪ {corePriv r ⟨a, h⟩} = _
    rw [hhub]
    ext z
    simp only [coreLoseSupp, mem_union, mem_image, mem_Ico, mem_singleton, mem_insert, mem_map,
      mem_univ, true_and, Function.Embedding.coeFn_mk, zero_add, Nat.zero_le]
    constructor
    · rintro (⟨j, -, rfl⟩ | rfl)
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨j, rfl⟩)
      · exact Or.inr rfl
      · refine Or.inl ⟨j, j.isLt, ?_⟩
        show Sum.inl (Fin.ofNat (r ^ 2) j) = Sum.inl j
        congr 1
        apply Fin.ext
        rw [Fin.val_ofNat, Nat.mod_eq_of_lt j.isLt]
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

/-! ### Leaf values of the index under the contiguous layout -/

section Leaf

variable (r : ℕ)

/-- Position of a terminal under the contiguous layout. -/
def cvPos (z : CoreZ r) : ℕ := ((coreLayout r z : Fin (r ^ 2 + r + 1)) : ℕ)

/-- Leaf values of an endpoint index: the endpoint of the terminal at each position, blank
beyond the `r² + r + 1` terminals. -/
def cvLeaf (g : CoreZ r → ℝ) (p : ℕ) : WithBot ℝ :=
  if h : p < r ^ 2 + r + 1 then ((g ((coreLayout r).symm ⟨p, h⟩) : ℝ) : WithBot ℝ) else ⊥

theorem cvPos_lt (z : CoreZ r) : cvPos r z < r ^ 2 + r + 1 := (coreLayout r z).isLt

theorem cvLeaf_pos (g : CoreZ r → ℝ) (z : CoreZ r) : cvLeaf r g (cvPos r z) = ((g z : ℝ) : WithBot ℝ) := by
  unfold cvLeaf
  rw [dite_eq_left (cvPos_lt r z)]
  have : (coreLayout r).symm ⟨cvPos r z, cvPos_lt r z⟩ = z := by
    show (coreLayout r).symm (coreLayout r z) = z
    exact (coreLayout r).symm_apply_apply z
  rw [this]

theorem cvLeaf_blank (g : CoreZ r → ℝ) (p : ℕ) (hp : 2 ^ coreN r ≤ p) : cvLeaf r g p = ⊥ := by
  unfold cvLeaf
  have : r ^ 2 + r + 1 ≤ 2 ^ coreN r := Nat.le_pow_clog (by norm_num) _
  rw [dite_eq_right (by omega)]

/-- A change of one terminal is a point update of the leaf values. -/
theorem cvLeaf_update (g g' : CoreZ r → ℝ) (z : CoreZ r) (h : ∀ w, w ≠ z → g' w = g w) :
    Function.update (cvLeaf r g) (cvPos r z) ((g' z : ℝ) : WithBot ℝ) = cvLeaf r g' := by
  funext p
  by_cases hp : p = cvPos r z
  · rw [hp, Function.update_self, cvLeaf_pos]
  · rw [Function.update_of_ne hp]
    unfold cvLeaf
    by_cases hlt : p < r ^ 2 + r + 1
    · rw [dite_eq_left hlt, dite_eq_left hlt, h]
      intro e
      apply hp
      unfold cvPos
      rw [← e, Equiv.apply_symm_apply]
    · rw [dite_eq_right hlt, dite_eq_right hlt]

theorem cvLeaf_sup (g : CoreZ r → ℝ) (S : Finset (CoreZ r)) :
    (layoutPos (coreLayout r) S).sup (cvLeaf r g) = S.sup (fun z => ((g z : ℝ) : WithBot ℝ)) := by
  unfold layoutPos
  rw [Finset.sup_image]
  exact Finset.sup_congr rfl (fun z _ => cvLeaf_pos r g z)

/-- The maximum of the leaf values over the positions of a root support is the exact MAX
value of the root action. -/
theorem cv_root_exact [NeZero r] (g : CoreZ r → ℝ) (a : Fin (r + 1)) :
    (layoutPos (coreLayout r) (coreSupp r a)).sup (cvLeaf r g)
      = ((MaxCirc.eval g (coreAct r a) : ℝ) : WithBot ℝ) := by
  rw [cvLeaf_sup, mcEval_eq_sup, mcTerms_coreAct]

end Leaf

/-! ### The dyadic-cover monitor -/

section Monitor

variable (r : ℕ)

/-- The compiled block list of the support of a root action. -/
def cvCovL (a : Fin (r + 1)) : List (ℕ × ℕ) :=
  (dualCompile (coreN r) (r ^ 2 + r + 1) (coreRunList r a)).1.1

theorem cvCovL_toFinset (a : Fin (r + 1)) : (cvCovL r a).toFinset = coreCov r a := rfl

theorem cvCovL_nodup [NeZero r] (a : Fin (r + 1)) : (cvCovL r a).Nodup :=
  (DualCoverFinal.dualCompile_lists (coreN r) (r ^ 2 + r + 1) (Nat.le_pow_clog (by norm_num) _)
    (coreRunList r a) (coreRunList_spec r a).1).1

theorem cvCovL_length_le [NeZero r] (a : Fin (r + 1)) : (cvCovL r a).length ≤ 4 * coreN r + 2 := by
  have h2 : (cvCovL r a).length ≤ (coreRunList r a).length * (2 * coreN r + 1) :=
    coverRuns_length (coreN r) (coreRunList r a)
  have h3 := (coreRunList_spec r a).2.2
  have h4 : (coreRunList r a).length * (2 * coreN r + 1) ≤ 2 * (2 * coreN r + 1) :=
    Nat.mul_le_mul_right _ h3
  omega

/-- State of the dyadic-cover monitor: the index of the lower and of the upper endpoints. -/
abbrev CvState (r : ℕ) := HState (Fin (r + 1)) (WithBot ℝ) × HState (Fin (r + 1)) (WithBot ℝ)

/-- Costed initialisation of the two indexes from the terminal table `x0`
(`DualCoverFinal.dcInit`: segment tree, action heaps, global heap). -/
def cvInit (x0 : CoreZ r → ℝ × ℝ) : CvState r × ℕ :=
  (((dcInit (coreN r) (cvLeaf r (fun z => (x0 z).1)) (cvCovL r) (List.finRange (r + 1))).1,
    (dcInit (coreN r) (cvLeaf r (fun z => (x0 z).2)) (cvCovL r) (List.finRange (r + 1))).1),
   (dcInit (coreN r) (cvLeaf r (fun z => (x0 z).1)) (cvCovL r) (List.finRange (r + 1))).2
    + (dcInit (coreN r) (cvLeaf r (fun z => (x0 z).2)) (cvCovL r) (List.finRange (r + 1))).2)

open Classical in
/-- One monitor step after a rollout that observed terminal `z`: the table changes from `x`
to `x'`.  Two comparisons (one unit each); each endpoint of `z` that actually changed is
written into its index by `dcUpdateH`. -/
def cvStep (x x' : CoreZ r → ℝ × ℝ) (z : CoreZ r) (σ : CvState r) : CvState r × ℕ :=
  ((if (x' z).1 ≠ (x z).1 then
      (dcUpdateH (coreN r) (coreSubs r) (cvPos r z) (((x' z).1 : ℝ) : WithBot ℝ) σ.1).1
    else σ.1,
    if (x' z).2 ≠ (x z).2 then
      (dcUpdateH (coreN r) (coreSubs r) (cvPos r z) (((x' z).2 : ℝ) : WithBot ℝ) σ.2).1
    else σ.2),
   2 + (if (x' z).1 ≠ (x z).1 then
      (dcUpdateH (coreN r) (coreSubs r) (cvPos r z) (((x' z).1 : ℝ) : WithBot ℝ) σ.1).2
    else 0)
    + (if (x' z).2 ≠ (x z).2 then
      (dcUpdateH (coreN r) (coreSubs r) (cvPos r z) (((x' z).2 : ℝ) : WithBot ℝ) σ.2).2
    else 0))

/-- The monitor state before the query at step `k`, for the table sequence `x` and the
observed terminals `z`. -/
def cvRun (x : ℕ → CoreZ r → ℝ × ℝ) (z : ℕ → CoreZ r) : ℕ → CvState r
  | 0 => (cvInit r (x 0)).1
  | k + 1 => (cvStep r (x k) (x (k + 1)) (z k) (cvRun x z k)).1

variable {r}

/-- Lower endpoint of a root action as read by a query: the root of its heap in the
lower-endpoint index. -/
def cvLo (σ : CvState r) (a : Fin (r + 1)) : ℝ := (findMax (σ.1.hp a)).unbotD 0

/-- Upper endpoint of a root action as read by a query. -/
def cvHi (σ : CvState r) (a : Fin (r + 1)) : ℝ := (findMax (σ.2.hp a)).unbotD 0

/-- The leader/stop output of the dyadic-cover monitor at `ε = 1/5`. -/
def cvStops (σ : CvState r) (a : Fin (r + 1)) : Prop :=
  MarginalStops univ (cvLo σ) (cvHi σ) (1 / 5) a

/-- Work of a root query: one read per action and endpoint, and two scans. -/
def cvQueryCost (r : ℕ) : ℕ := 4 * (r + 1)

/-- Invariant of the monitor: each implemented index represents an abstract index state
satisfying the index invariant for the current endpoint values. -/
def CvInv (x : CoreZ r → ℝ × ℝ) (σ : CvState r) : Prop :=
  (∃ s, Sim (coreCov r) (fun a => (cvCovL r a).length) univ (r + 1) σ.1 s ∧
      DCInv (coreN r) (coreCov r) (cvLeaf r (fun z => (x z).1)) s) ∧
    ∃ s, Sim (coreCov r) (fun a => (cvCovL r a).length) univ (r + 1) σ.2 s ∧
      DCInv (coreN r) (coreCov r) (cvLeaf r (fun z => (x z).2)) s

variable [NeZero r]

theorem cvInit_one (g : CoreZ r → ℝ) :
    (∃ s, Sim (coreCov r) (fun a => (cvCovL r a).length) univ (r + 1)
        (dcInit (coreN r) (cvLeaf r g) (cvCovL r) (List.finRange (r + 1))).1 s ∧
      DCInv (coreN r) (coreCov r) (cvLeaf r g) s) ∧
    (dcInit (coreN r) (cvLeaf r g) (cvCovL r) (List.finRange (r + 1))).2
      ≤ (2 ^ (coreN r + 1) - 1)
        + ((List.finRange (r + 1)).map
            (fun a => (cvCovL r a).length * (Nat.clog 2 (cvCovL r a).length + 3) + 1)).sum
        + (r + 1) * (Nat.clog 2 (r + 1) + 2) := by
  obtain ⟨h1, h2, -, h4⟩ := DualCoverFinal.dcInit_spec (coreN r) (cvLeaf r g)
    (cvLeaf_blank r g) (cvCovL r) (List.finRange (r + 1)) (List.nodup_finRange _)
    (cvCovL_nodup r) (fun a ha => absurd (List.mem_finRange a) ha)
  rw [List.toFinset_finRange, List.length_finRange] at h2
  rw [List.length_finRange] at h4
  exact ⟨⟨_, h2, h1⟩, h4⟩

theorem cvInit_inv (x0 : CoreZ r → ℝ × ℝ) : CvInv x0 (cvInit r x0).1 :=
  ⟨(cvInit_one _).1, (cvInit_one _).1⟩

/-- Cost bound of one index update under the representation invariant. -/
def cvUpdBound (r : ℕ) : ℕ :=
  2 * (coreN r + 1) + (r + 1) * (Nat.clog 2 (4 * coreN r + 2) + Nat.clog 2 (r + 1) + 4)

theorem cvUpdate_one (g g' : CoreZ r → ℝ) (z : CoreZ r) (hg : ∀ w, w ≠ z → g' w = g w)
    (hs : HState (Fin (r + 1)) (WithBot ℝ))
    (h : ∃ s, Sim (coreCov r) (fun a => (cvCovL r a).length) univ (r + 1) hs s ∧
      DCInv (coreN r) (coreCov r) (cvLeaf r g) s) :
    (∃ s, Sim (coreCov r) (fun a => (cvCovL r a).length) univ (r + 1)
        (dcUpdateH (coreN r) (coreSubs r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ) hs).1 s ∧
      DCInv (coreN r) (coreCov r) (cvLeaf r g') s) ∧
    (dcUpdateH (coreN r) (coreSubs r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ) hs).2
      ≤ cvUpdBound r := by
  obtain ⟨s, hsim, hinv⟩ := h
  obtain ⟨a1, a2, -⟩ := HeapImpl.dcUpdateH_spec (coreN r) (coreCov r) (coreSubs r)
    (fun a => (cvCovL r a).length) univ (r + 1) (cvPos r z) ((g' z : ℝ) : WithBot ℝ) hs s hsim
  have hinv' := dcUpdate_inv (coreN r) (coreCov r) (coreSubs r) (fun a => (cvCovL r a).length)
    (r + 1) (cvPos r z) ((g' z : ℝ) : WithBot ℝ) (cvLeaf r g) s
    (fun _ _ hd => mem_coreSubs.mpr hd) (coreCov_lev r) hinv
  rw [cvLeaf_update r g g' z hg] at hinv'
  refine ⟨⟨_, a1, hinv'⟩, a2.trans ?_⟩
  have hlen := changedSubs_length_le (coreN r) (coreCov r) (coreSubs r) (coreSubs_nodup r)
    (fun d a ha => mem_coreSubs.mp ha) (coreCov_one r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ)
    s.tree
  rw [Fintype.card_fin] at hlen
  have hheap : ((changedSubs (coreN r) (coreSubs r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ)
        s.tree).map (fun e => Nat.clog 2 (cvCovL r e.2).length + 2)).sum
      ≤ (changedSubs (coreN r) (coreSubs r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ)
        s.tree).length * (Nat.clog 2 (4 * coreN r + 2) + 2) := by
    calc _ ≤ ((changedSubs (coreN r) (coreSubs r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ)
            s.tree).map (fun _ => Nat.clog 2 (4 * coreN r + 2) + 2)).sum := by
          apply List.sum_le_sum
          intro e _
          exact Nat.add_le_add_right (Nat.clog_mono_right 2 (cvCovL_length_le r e.2)) 2
      _ = _ := by simp
  have haff : (affected (coreN r) (coreSubs r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ)
        s.tree).length
      ≤ (changedSubs (coreN r) (coreSubs r) (cvPos r z) ((g' z : ℝ) : WithBot ℝ)
        s.tree).length := by
    unfold affected
    exact ((List.dedup_sublist _).length_le).trans (by simp)
  have h1 := Nat.mul_le_mul_right (Nat.clog 2 (4 * coreN r + 2) + 2) hlen
  have h2 := Nat.mul_le_mul_right (Nat.clog 2 (r + 1) + 2) (haff.trans hlen)
  unfold cvUpdBound
  nlinarith

/-- **One monitor step preserves the invariant and costs at most `2 + 2 · cvUpdBound`.** -/
theorem cvStep_spec {x x' : CoreZ r → ℝ × ℝ} {z : CoreZ r} (hx : ∀ w, x' w ≠ x w → w = z)
    {σ : CvState r} (h : CvInv x σ) :
    CvInv x' (cvStep r x x' z σ).1 ∧ (cvStep r x x' z σ).2 ≤ 2 + 2 * cvUpdBound r := by
  classical
  have hw : ∀ w, w ≠ z → x' w = x w := fun w hne => by
    by_contra hc
    exact hne (hx w hc)
  have hL : ∀ w, w ≠ z → (fun v => (x' v).1) w = (fun v => (x v).1) w :=
    fun w hne => by show (x' w).1 = (x w).1; rw [hw w hne]
  have hU : ∀ w, w ≠ z → (fun v => (x' v).2) w = (fun v => (x v).2) w :=
    fun w hne => by show (x' w).2 = (x w).2; rw [hw w hne]
  obtain ⟨hl, hu⟩ := h
  have uL := cvUpdate_one (fun v => (x v).1) (fun v => (x' v).1) z hL σ.1 hl
  have uU := cvUpdate_one (fun v => (x v).2) (fun v => (x' v).2) z hU σ.2 hu
  unfold cvStep
  by_cases c1 : (x' z).1 ≠ (x z).1
  · by_cases c2 : (x' z).2 ≠ (x z).2
    · simp only [ite_eq_left c1, ite_eq_left c2]
      exact ⟨⟨uL.1, uU.1⟩, by have := uL.2; have := uU.2; omega⟩
    · simp only [ite_eq_left c1, ite_eq_right c2]
      refine ⟨⟨uL.1, ?_⟩, by have := uL.2; omega⟩
      have e : (fun v => (x' v).2) = fun v => (x v).2 := by
        funext w
        by_cases hwz : w = z
        · rw [hwz]; exact not_not.mp c2
        · exact hU w hwz
      rw [e]
      exact hu
  · have e1 : (fun v => (x' v).1) = fun v => (x v).1 := by
      funext w
      by_cases hwz : w = z
      · rw [hwz]; exact not_not.mp c1
      · exact hL w hwz
    by_cases c2 : (x' z).2 ≠ (x z).2
    · simp only [ite_eq_right c1, ite_eq_left c2]
      refine ⟨⟨?_, uU.1⟩, by have := uU.2; omega⟩
      rw [e1]
      exact hl
    · simp only [ite_eq_right c1, ite_eq_right c2]
      refine ⟨⟨?_, ?_⟩, by omega⟩
      · rw [e1]
        exact hl
      · have e : (fun v => (x' v).2) = fun v => (x v).2 := by
          funext w
          by_cases hwz : w = z
          · rw [hwz]; exact not_not.mp c2
          · exact hU w hwz
        rw [e]
        exact hu

/-- **The invariant holds along the run**, for every table sequence in which step `k` changes
only the observed terminal `z k`. -/
theorem cvRun_inv {x : ℕ → CoreZ r → ℝ × ℝ} {z : ℕ → CoreZ r}
    (hx : ∀ k w, x (k + 1) w ≠ x k w → w = z k) : ∀ k, CvInv (x k) (cvRun r x z k)
  | 0 => cvInit_inv (x 0)
  | k + 1 => (cvStep_spec (hx k) (cvRun_inv hx k)).1

/-- **The query reads the exact root-action intervals.**  Under the invariant, the root of
the heap of action `a` in the lower (upper) index is the exact lower (upper) endpoint of the
MAX value of `a` on the current box. -/
theorem cv_exact {x : CoreZ r → ℝ × ℝ} {σ : CvState r} (h : CvInv x σ) (a : Fin (r + 1)) :
    cvLo σ a = ((coreAct r a).ival x).1 ∧ cvHi σ a = ((coreAct r a).ival x).2 := by
  obtain ⟨⟨sl, hsl, hil⟩, ⟨su, hsu, hiu⟩⟩ := h
  have hb : (coreCov r a).biUnion blk = layoutPos (coreLayout r) (coreSupp r a) :=
    biUnion_blk_of_cover ((core_cover_compile r).1 a).1
  have q1 := (HeapImpl.query_spec (coreN r) (coreCov r) (fun a => (cvCovL r a).length) univ
    (r + 1) _ σ.1 sl hsl hil (coreCov_lev r)).1 a
  have q2 := (HeapImpl.query_spec (coreN r) (coreCov r) (fun a => (cvCovL r a).length) univ
    (r + 1) _ σ.2 su hsu hiu (coreCov_lev r)).1 a
  rw [hb, cv_root_exact] at q1 q2
  unfold cvLo cvHi
  rw [q1, q2]
  exact ⟨rfl, rfl⟩

/-- **The leader/stop output of the dyadic-cover monitor equals that of the exact graph
monitors at every step.** -/
theorem cv_stops_iff {x : ℕ → CoreZ r → ℝ × ℝ} {z : ℕ → CoreZ r}
    (hx : ∀ k w, x (k + 1) w ≠ x k w → w = z k) (k : ℕ) (a : Fin (r + 1)) :
    cvStops (cvRun r x z k) a ↔ coreStops (coreRun false (coreHub r) x k) (x k) a := by
  unfold cvStops coreStops
  rw [coreRun_act_false]
  refine marginalStops_congr (fun b _ => ?_) (fun b _ => ?_) a
  · rw [(cv_exact (cvRun_inv hx k) b).1,
      (coreRun_lo_hi false x k (by rw [coreRun_act_false]; exact mem_univ b)).1]
    rfl
  · rw [(cv_exact (cvRun_inv hx k) b).2,
      (coreRun_lo_hi false x k (by rw [coreRun_act_false]; exact mem_univ b)).2]
    rfl

/-! ### Work of the dyadic-cover monitor -/

/-- Disposal of the two indexes: one unit per tree node, heap slot and heap record. -/
def cvDispose (r : ℕ) : ℕ :=
  2 * (2 ^ (coreN r + 1) + ((List.finRange (r + 1)).map (fun a => (cvCovL r a).length + 1)).sum
    + (r + 1))

/-- Monitor work for `K` rollouts after the forced ones: compile, the two costed
initialisations, per step a query and the monitor step, the final query, disposal. -/
def cvMonWork (r : ℕ) (x : ℕ → CoreZ r → ℝ × ℝ) (z : ℕ → CoreZ r) (K : ℕ) : ℕ :=
  (compileAll (coreN r) (r ^ 2 + r + 1) ((List.finRange (r + 1)).map (coreRunList r))).2
    + (cvInit r (x 0)).2
    + ∑ k ∈ range K, (cvQueryCost r + (cvStep r (x k) (x (k + 1)) (z k) (cvRun r x z k)).2)
    + cvQueryCost r + cvDispose r

/-- Total work of the search with the dyadic-cover monitor: reading and disposing of the
graph, the sampler traversal of all `r + 1 + K` rollouts, and the monitor work. -/
def cvTotalWork (r : ℕ) [NeZero r] (β : ℕ → ℝ) (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1))
    (zt : ℕ → CoreZ r) (K : ℕ) : ℕ :=
  2 * ((coreHub r).uctSize + 3 * r + 1) + ∑ u ∈ range (r + 1 + K), coreRollout r rule u (sel u)
    + cvMonWork r (coreBox r β zt) (fun k => zt (r + 1 + k)) K

omit [NeZero r] in
/-- The Hoeffding boxes change only at the observed terminal. -/
theorem coreBox_one (β : ℕ → ℝ) (zt : ℕ → CoreZ r) (k : ℕ) (w : CoreZ r)
    (hne : coreBox r β zt (k + 1) w ≠ coreBox r β zt k w) : w = zt (r + 1 + k) := by
  by_contra hz
  apply hne
  have hc : uctCount zt (r + 1 + (k + 1)) w = uctCount zt (r + 1 + k) w := by
    show uctCount zt (r + 1 + k + 1) w = _
    rw [uctCount_succ, ite_eq_right (fun e => hz e.symm), add_zero]
  unfold coreBox coreTab
  rw [hc]

theorem cvList_sum_le {β : Type*} (l : List β) (f : β → ℕ) (c : ℕ) (h : ∀ x, f x ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  have := ccList_sum_le (l.map f) c (by
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact h b)
  rwa [List.length_map] at this

/-- **Monitor work in natural numbers.** -/
theorem cvMonWork_le {x : ℕ → CoreZ r → ℝ × ℝ} {z : ℕ → CoreZ r}
    (hx : ∀ k w, x (k + 1) w ≠ x k w → w = z k) (K : ℕ) :
    cvMonWork r x z K ≤ 30 * (1 + coreN r) * (r + 1)
      + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (16 * (coreN r + 1) ^ 2) + (r + 1) * (coreN r + 2))
      + K * (4 * (r + 1) + 18 * ((r + 1) * (coreN r + 1)))
      + 4 * (r + 1)
      + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (4 * coreN r + 3) + (r + 1)) := by
  have hcomp := (core_cover_compile r).2.2
  have htree : 2 ^ (coreN r + 1) ≤ 4 * (r ^ 2 + r + 1) := by
    have := segTree_nodes_lt (r ^ 2 + r + 1) (by omega)
    unfold coreN
    omega
  have c2 : Nat.clog 2 (r + 1) ≤ coreN r := Nat.clog_mono_right 2 (by nlinarith)
  have c1 : Nat.clog 2 (4 * coreN r + 2) ≤ 4 * coreN r + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  -- initialisation of one index
  have hinit : ∀ g : CoreZ r → ℝ,
      (dcInit (coreN r) (cvLeaf r g) (cvCovL r) (List.finRange (r + 1))).2
        ≤ 4 * (r ^ 2 + r + 1) + (r + 1) * (16 * (coreN r + 1) ^ 2)
          + (r + 1) * (coreN r + 2) := by
    intro g
    have h := (cvInit_one (r := r) g).2
    have hs := cvList_sum_le (List.finRange (r + 1))
      (fun a => (cvCovL r a).length * (Nat.clog 2 (cvCovL r a).length + 3) + 1)
      (16 * (coreN r + 1) ^ 2) (by
        intro a
        have hl := cvCovL_length_le (r := r) a
        have hc : Nat.clog 2 (cvCovL r a).length ≤ 4 * coreN r + 2 :=
          (Nat.clog_mono_right 2 hl).trans c1
        calc (cvCovL r a).length * (Nat.clog 2 (cvCovL r a).length + 3) + 1
            ≤ (4 * coreN r + 2) * (4 * coreN r + 2 + 3) + 1 :=
              Nat.add_le_add_right (Nat.mul_le_mul hl (by omega)) 1
          _ ≤ 16 * (coreN r + 1) ^ 2 := by nlinarith)
    rw [List.length_finRange] at hs
    have h3 : (r + 1) * (Nat.clog 2 (r + 1) + 2) ≤ (r + 1) * (coreN r + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hinit2 : (cvInit r (x 0)).2
      ≤ 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (16 * (coreN r + 1) ^ 2)
          + (r + 1) * (coreN r + 2)) := by
    have h1 := hinit (fun z => (x 0 z).1)
    have h2 := hinit (fun z => (x 0 z).2)
    show _ + _ ≤ _
    omega
  -- steps
  have hupd : 2 + 2 * cvUpdBound r ≤ 18 * ((r + 1) * (coreN r + 1)) := by
    unfold cvUpdBound
    have : (r + 1) * (Nat.clog 2 (4 * coreN r + 2) + Nat.clog 2 (r + 1) + 4)
        ≤ (r + 1) * (5 * coreN r + 6) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hsteps : ∑ k ∈ range K,
        (cvQueryCost r + (cvStep r (x k) (x (k + 1)) (z k) (cvRun r x z k)).2)
      ≤ K * (4 * (r + 1) + 18 * ((r + 1) * (coreN r + 1))) := by
    have : ∑ k ∈ range K,
          (cvQueryCost r + (cvStep r (x k) (x (k + 1)) (z k) (cvRun r x z k)).2)
        ≤ ∑ _k ∈ range K, (4 * (r + 1) + 18 * ((r + 1) * (coreN r + 1))) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      have := (cvStep_spec (hx k) (cvRun_inv hx k)).2
      unfold cvQueryCost
      omega
    rwa [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  -- disposal
  have hdisp : cvDispose r
      ≤ 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (4 * coreN r + 3) + (r + 1)) := by
    have hs := cvList_sum_le (List.finRange (r + 1)) (fun a => (cvCovL r a).length + 1)
      (4 * coreN r + 3) (by
        intro a
        have := cvCovL_length_le (r := r) a
        omega)
    rw [List.length_finRange] at hs
    unfold cvDispose
    omega
  unfold cvMonWork cvQueryCost
  unfold cvQueryCost at hsteps
  omega

end Monitor

/-! ### The flat clause: a costed materialisation of the flat supports -/

section Flat

variable {Z : Type*}

/-- **Materialising a flat support.**  Traverse the subgraph below a vertex and write every
terminal reached into a list: one unit per vertex visited (which includes one unit per cell
written). -/
def flatSupp : MaxCirc Z → List Z × ℕ
  | .term z => ([z], 1)
  | .unary c => ((flatSupp c).1, (flatSupp c).2 + 1)
  | .bin c d => ((flatSupp c).1 ++ (flatSupp d).1, (flatSupp c).2 + (flatSupp d).2 + 1)

theorem flatSupp_spec [DecidableEq Z] : ∀ c : MaxCirc Z,
    (flatSupp c).1.toFinset = mcTerms c ∧ (flatSupp c).1.length ≤ (flatSupp c).2
  | .term z => by simp [flatSupp, mcTerms]
  | .unary c => by
      obtain ⟨h1, h2⟩ := flatSupp_spec c
      exact ⟨h1, Nat.le_succ_of_le h2⟩
  | .bin c d => by
      obtain ⟨h1, h2⟩ := flatSupp_spec c
      obtain ⟨h3, h4⟩ := flatSupp_spec d
      refine ⟨?_, ?_⟩
      · show ((flatSupp c).1 ++ (flatSupp d).1).toFinset = mcTerms c ∪ mcTerms d
        rw [List.toFinset_append, h1, h3]
      · show ((flatSupp c).1 ++ (flatSupp d).1).length ≤ (flatSupp c).2 + (flatSupp d).2 + 1
        rw [List.length_append]
        omega

/-- Materialise the flat supports of a list of root actions in turn. -/
def flatAll {A : Type*} (g : A → MaxCirc Z) : List A → List (List Z) × ℕ
  | [] => ([], 0)
  | a :: as => ((flatSupp (g a)).1 :: (flatAll g as).1, (flatSupp (g a)).2 + (flatAll g as).2)

theorem flatAll_spec [DecidableEq Z] {A : Type*} (g : A → MaxCirc Z) : ∀ as : List A,
    (flatAll g as).1 = as.map (fun a => (flatSupp (g a)).1) ∧
      (as.map (fun a => (mcTerms (g a)).card)).sum ≤ (flatAll g as).2
  | [] => ⟨rfl, le_rfl⟩
  | a :: as => by
      obtain ⟨h1, h2⟩ := flatAll_spec g as
      obtain ⟨s1, s2⟩ := flatSupp_spec (g a)
      refine ⟨by simp only [flatAll, List.map_cons, h1], ?_⟩
      have hc : (mcTerms (g a)).card ≤ (flatSupp (g a)).1.length := by
        rw [← s1]
        exact List.toFinset_card_le _
      simp only [flatAll, List.map_cons, List.sum_cons]
      omega

end Flat

/-- The costed materialisation outputs exactly the support of each root action of the
common-core DAG. -/
theorem flatSupp_coreAct (r : ℕ) [NeZero r] (a : Fin (r + 1)) :
    (flatSupp (coreAct r a)).1.toFinset = coreSupp r a := by
  rw [(flatSupp_spec _).1, mcTerms_coreAct]

theorem coreSupp_card_sum (r : ℕ) : r ^ 3 ≤ ∑ a : Fin (r + 1), (coreSupp r a).card := by
  rw [Fin.sum_univ_castSucc]
  have h : ∀ i : Fin r, (coreSupp r (Fin.castSucc i)).card = (coreLoseSupp r i).card := by
    intro i
    unfold coreSupp
    rw [dite_eq_left (by simp)]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  exact le_trans (core_flat_support_size r).2 (Nat.le_add_right _ _)

/-- **`thm:ta-core`, flat clause, as work of the materialisation program.**  Materialising
the flat root-to-terminal supports of the `r + 1` root actions costs at least
`Σ_a |S(a)| ≥ r³` operations. -/
theorem coreFlat_cost_ge (r : ℕ) [NeZero r] :
    ∑ a : Fin (r + 1), (coreSupp r a).card ≤ (flatAll (coreAct r) (List.finRange (r + 1))).2 ∧
      r ^ 3 ≤ (flatAll (coreAct r) (List.finRange (r + 1))).2 := by
  have h := (flatAll_spec (coreAct r) (List.finRange (r + 1))).2
  have e : ((List.finRange (r + 1)).map (fun a => (mcTerms (coreAct r a)).card)).sum
      = ∑ a : Fin (r + 1), (coreSupp r a).card := by
    rw [Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro a _
    rw [mcTerms_coreAct]
  rw [e] at h
  exact ⟨h, (coreSupp_card_sum r).trans h⟩

/-- **`thm:ta-core`, flat clause, for every materialisation.**  Any family of explicit lists
containing the flat supports has at least `r³` cells; a program that writes one cell per
unit therefore costs at least `r³`. -/
theorem flat_cells_ge (r : ℕ) (out : Fin (r + 1) → List (CoreZ r))
    (h : ∀ a, coreSupp r a ⊆ (out a).toFinset) : r ^ 3 ≤ ∑ a : Fin (r + 1), (out a).length := by
  refine (coreSupp_card_sum r).trans (Finset.sum_le_sum (fun a _ => ?_))
  exact (Finset.card_le_card (h a)).trans (List.toFinset_card_le _)

/-! ### The theorem -/

/-- Arithmetic behind the work bound of `ta_core_literal`, with `ℓ = log r`, `c = coreN r`
and `T = r + 1 + τ`. -/
theorem core_work_arith {A r ℓ c T τ : ℝ} (hA : 0 < A) (hr : 2 ≤ r) (hℓ : 0.69 ≤ ℓ)
    (hc0 : 0 ≤ c) (hc : c + 1 ≤ 12 * ℓ) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T)
    (hT : T ≤ A * r * ℓ) :
    2 * (2 * r ^ 2 + 3 * r) + T * (5 * r + 5)
        + (30 * (1 + c) * (r + 1)
          + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (16 * (c + 1) ^ 2) + (r + 1) * (c + 2))
          + τ * (4 * (r + 1) + 18 * ((r + 1) * (c + 1)))
          + 4 * (r + 1)
          + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (4 * c + 3) + (r + 1)))
      ≤ (500 * A + 20000) * r ^ 2 * ℓ ^ 2 := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = r * ℓ := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hp1 : 1.38 ≤ p := by
    rw [hp]; nlinarith [mul_le_mul hr hℓ (by norm_num) hr0]
  have hrp : r ≤ 1.45 * p := by
    rw [hp]; nlinarith [mul_le_mul_of_nonneg_left hℓ hr0]
  have hℓp : 2 * ℓ ≤ p := by rw [hp]; nlinarith [mul_le_mul_of_nonneg_right hr hℓ0]
  have hr1 : r + 1 ≤ 2.2 * p := by linarith
  have hr10 : 0 ≤ r + 1 := by linarith
  have hNr1 : (c + 1) * (r + 1) ≤ 18 * p := by
    have h := mul_le_mul_of_nonneg_right hc hr10
    have e : 12 * ℓ * (r + 1) = 12 * p + 12 * ℓ := by rw [hp]; ring
    linarith
  have hN2 : (c + 1) ^ 2 * (r + 1) ≤ 216 * p ^ 2 := by
    have h1 : (c + 1) * ((c + 1) * (r + 1)) ≤ (12 * ℓ) * (18 * p) :=
      mul_le_mul hc hNr1 (by positivity) (by linarith)
    have e : (c + 1) ^ 2 * (r + 1) = (c + 1) * ((c + 1) * (r + 1)) := by ring
    have h2 : (12 * ℓ) * (18 * p) ≤ (6 * p) * (18 * p) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hr2 : r ^ 2 ≤ 2.11 * p ^ 2 := by
    have := mul_le_mul hrp hrp hr0 (by linarith)
    nlinarith
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hTp : T ≤ A * p := by rw [hp]; linarith
  have hT0 : 0 ≤ T := le_trans hτ0 hτT
  have hT1 : T * (5 * r + 5) ≤ 11 * (A * p ^ 2) := by
    have := mul_le_mul hTp (by linarith : 5 * r + 5 ≤ 11 * p) (by linarith) (by positivity)
    nlinarith
  have hτ1 : τ * (4 * (r + 1) + 18 * ((r + 1) * (c + 1))) ≤ 333 * (A * p ^ 2) := by
    have hb : 4 * (r + 1) + 18 * ((r + 1) * (c + 1)) ≤ 333 * p := by nlinarith
    have := mul_le_mul (hτT.trans hTp) hb (by positivity) (by positivity)
    nlinarith
  have e : (500 * A + 20000) * r ^ 2 * ℓ ^ 2 = 500 * (A * p ^ 2) + 20000 * p ^ 2 := by
    rw [hp]; ring
  rw [e]
  have hAp : 0 ≤ A * p ^ 2 := by positivity
  nlinarith

/-- **Theorem `thm:ta-core`, with the dyadic-cover index as the stopping monitor and the
flat clause as work.**  Fix `δ ∈ (0, 1)`.  There are constants `A, B, C` such that for every
`r ≥ 2` and every UCT search on the common-core DAG with the Hoeffding boxes
`x = coreBox r (coreRadius r δ) zt`, writing `σ k` for the state of the dyadic-cover monitor
run on these boxes (`cvRun`):

* at every step the monitor reads the exact root-action intervals, and its leader/stop
  output is that of the eager and of the selective graph monitor;
* there is one step `τ` at which the three monitors stop for the first time, all
  recommending the winning action, and `r + 1 + τ ≤ A r log r`;
* the total work of either graph monitor is at most `B r² log r`;
* the total work of the search with the dyadic-cover monitor (graph, sampler traversal,
  compile, costed initialisation, updates, queries, disposal) is at most `C r² log² r`;
* the costed materialisation of the flat supports costs at least `r³`, and every family of
  explicit lists containing the supports has at least `r³` cells. -/
theorem ta_core_literal {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r),
      CoreSearch r rule sel zt →
        (∀ k a,
          cvLo (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a
              = coreL r (coreBox r (coreRadius r δ) zt) k a ∧
            cvHi (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a
              = coreU r (coreBox r (coreRadius r δ) zt) k a) ∧
        (∀ (s : Bool) k a,
          cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a ↔
            coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
        ∃ τ : ℕ,
          cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) τ)
            (Fin.last r) ∧
          (∀ s : Bool, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
            (coreBox r (coreRadius r δ) zt τ) (Fin.last r)) ∧
          (∀ k, k < τ → ∀ a, ¬ cvStops
            (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a) ∧
          (∀ (s : Bool) k, k < τ → ∀ a,
            ¬ coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
          (∀ k a, cvStops
            (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a →
              a = Fin.last r) ∧
          ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
          (∀ s : Bool, (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ B * (r : ℝ) ^ 2 * Real.log r) ∧
          (cvTotalWork r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ C * (r : ℝ) ^ 2 * Real.log r ^ 2 ∧
          r ^ 3 ≤ (flatAll (coreAct r) (List.finRange (r + 1))).2 ∧
          ∀ out : Fin (r + 1) → List (CoreZ r), (∀ a, coreSupp r a ⊆ (out a).toFinset) →
            r ^ 3 ≤ ∑ a : Fin (r + 1), (out a).length := by
  obtain ⟨A, B, hA, hB, H⟩ := ta_core_coupled hδ0 hδ1
  refine ⟨A, B, 500 * A + 20000, hA, hB, by linarith, ?_⟩
  intro r _ hr rule sel zt h
  obtain ⟨hiff, -, τ, f1, f2, f3, f4, f5, -⟩ := H r hr rule sel zt h
  have hone := coreBox_one (r := r) (coreRadius r δ) zt
  have hcv := cv_stops_iff (r := r) hone
  have hcvs : ∀ (s : Bool) k a,
      cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a ↔
        coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
          (coreBox r (coreRadius r δ) zt k) a := by
    intro s k a
    cases s
    · exact hcv k a
    · exact (hcv k a).trans (hiff k a).symm
  refine ⟨fun k a => cv_exact (cvRun_inv hone k) a, hcvs, τ, (hcvs false τ _).mpr (f1 false), f1,
    fun k hk a hs => f2 false k hk a ((hcvs false k a).mp hs), f2,
    fun k a hs => f3 false k a ((hcvs false k a).mp hs), f4, f5, ?_, (coreFlat_cost_ge r).2,
    flat_cells_ge r⟩
  -- the work bound
  have hmon := cvMonWork_le (r := r) hone τ
  have hsize := coreHub_size r
  have hroll : ∑ u ∈ range (r + 1 + τ), coreRollout r rule u (sel u)
      ≤ (r + 1 + τ) * (5 * r + 5) := by
    have hh := coreHub_height_le r
    have : ∑ u ∈ range (r + 1 + τ), coreRollout r rule u (sel u)
        ≤ ∑ _u ∈ range (r + 1 + τ), (5 * r + 5) := by
      refine Finset.sum_le_sum (fun u _ => ?_)
      have h1 := (MaxCirc.uctWalk_snd_le (rule u) (coreAct r (sel u)) 0).trans
        (coreAct_height r (sel u))
      have h2 := coreClog_le r
      unfold coreRollout
      omega
    rwa [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  have hW : cvTotalWork r (coreRadius r δ) rule sel zt τ
      ≤ 2 * (2 * r ^ 2 + 3 * r) + (r + 1 + τ) * (5 * r + 5)
        + (30 * (1 + coreN r) * (r + 1)
          + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (16 * (coreN r + 1) ^ 2)
            + (r + 1) * (coreN r + 2))
          + τ * (4 * (r + 1) + 18 * ((r + 1) * (coreN r + 1)))
          + 4 * (r + 1)
          + 2 * (4 * (r ^ 2 + r + 1) + (r + 1) * (4 * coreN r + 3) + (r + 1))) := by
    unfold cvTotalWork
    omega
  have hWR : (cvTotalWork r (coreRadius r δ) rule sel zt τ : ℝ)
      ≤ 2 * (2 * (r : ℝ) ^ 2 + 3 * r) + ((r + 1 + τ : ℕ) : ℝ) * (5 * r + 5)
        + (30 * (1 + (coreN r : ℝ)) * (r + 1)
          + 2 * (4 * ((r : ℝ) ^ 2 + r + 1) + (r + 1) * (16 * ((coreN r : ℝ) + 1) ^ 2)
            + (r + 1) * ((coreN r : ℝ) + 2))
          + (τ : ℝ) * (4 * (r + 1) + 18 * ((r + 1) * ((coreN r : ℝ) + 1)))
          + 4 * (r + 1)
          + 2 * (4 * ((r : ℝ) ^ 2 + r + 1) + (r + 1) * (4 * (coreN r : ℝ) + 3) + (r + 1))) := by
    exact_mod_cast hW
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hℓ69 : (0.69 : ℝ) ≤ Real.log r := by
    have h1 : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hrR
    have h2 := Real.log_two_gt_d9
    linarith
  have hτT : (τ : ℝ) ≤ ((r + 1 + τ : ℕ) : ℝ) := by push_cast; linarith
  exact hWR.trans (core_work_arith hA hrR hℓ69 (Nat.cast_nonneg _) (coreN_le_log hr)
    (Nat.cast_nonneg τ) hτT f4)

/-- **`thm:ta-core`, the graph clauses.**  The shared hub (tree unfolding) has `2 r² - 1`
vertices, so the DAG has `Θ(r²)` edges, and at `ε = 1/5` the winning action is the unique
`ε`-optimal root action (`PassiveRetirement.core_unique_eps_optimal`). -/
theorem ta_core_graph (r : ℕ) [NeZero r] :
    (coreHub r).uctSize + 1 = 2 * r ^ 2 ∧
      regret (coreWinSupp r) (coreWinSupp_nonempty r) (coreReward r) ≤ 1 / 5 ∧
      ∀ i : Fin r,
        ¬ regret (coreLoseSupp r i) (coreLoseSupp_nonempty r i) (coreReward r) ≤ 1 / 5 :=
  ⟨coreHub_size r, core_unique_eps_optimal r⟩

end

end LiteralE
end JointRootCert
