/-
`thm:t4-finite-sample` (Finite-sample cost of safeguarded CD-Joint) with continuous noise.

`LiteralF1.t4_finite_sample_rademacher` discharges the hypotheses of
`LiteralF1.t4_finite_sample` only for countably-valued (Rademacher) noise, where the
adaptedness of the query sequence is automatic.  This file removes that restriction.

* `firstSat`: the least-index choice among the elements of a finite type satisfying a
  predicate; `measurable_firstSat_eq`: its level sets are finite Boolean combinations of the
  predicates, hence measurable when the predicates are.
* `measurable_cdDualCert`, `measurable_CDStep`: for a fixed design matrix and radius, the
  stopping test `cdDualCert` and the step rule `CDStep` of Algorithm `alg:cd-joint` are Borel
  predicates of the estimate `m`.  The inner minimisations over the simplex are removed by
  `isClosed_exists_mem` (projection of a closed set along a compact factor is closed) and
  `measurableSet_exists_closed_open` (the same for closed ∩ open sets, which are `F_σ`).
* `cdPol`: an explicit causal policy (least-index tie-breaking, ridge estimate, radius
  `eq:ay-radius`); `cdPol_run`: it is an infinite run of Algorithm `alg:cd-joint` on every
  noise path; `measurableSet_cdPol`, `cdPol_adapted`: its queries are Borel functions of the
  past noise, i.e. adapted to the natural filtration `nFilt`.
* `subG_hyps`, `t4_finite_sample_subG`: i.i.d. noise with an arbitrary real law `ν` whose
  moment generating function is `σ`-sub-Gaussian (`∫ exp (c x) dν ≤ exp (c² σ² / 2)`);
  every hypothesis of `LiteralF1.t4_finite_sample` holds and hence its conclusion.
  `t4_finite_sample_gaussian`: the special case `ν = N(0, 1)`, `σ = 1`.
-/
import JointRootCert.LiteralF1

namespace JointRootCert

namespace LiteralG1

open Finset MeasureTheory Matrix Filter ProbabilityTheory
open scoped ENNReal
open LiteralABC LiteralABC2 LiteralABC3 LiteralF1

/-! ### Least-index choice -/

section FirstSat

/-- The element of least rank `r` satisfying `P` (`d` if there is none). -/
noncomputable def firstSat {X : Type*} (r : X → ℕ) (P : X → Prop) (d : X) : X := by
  classical
  exact if h : ∃ a, P a then (InvImage.wf r wellFounded_lt).min {a | P a} h else d

lemma firstSat_spec {X : Type*} (r : X → ℕ) {P : X → Prop} (d : X) (h : ∃ a, P a) :
    P (firstSat r P d) := by
  unfold firstSat
  rw [dif_pos h]
  exact (InvImage.wf r wellFounded_lt).min_mem {a | P a} h

lemma firstSat_eq_iff {X : Type*} {r : X → ℕ} (hr : Function.Injective r) (P : X → Prop)
    (d a : X) :
    firstSat r P d = a ↔ (P a ∧ ∀ b, P b → r a ≤ r b) ∨ ((∀ b, ¬ P b) ∧ d = a) := by
  unfold firstSat
  by_cases h : ∃ a, P a
  · rw [dif_pos h]
    have hmem := (InvImage.wf r wellFounded_lt).min_mem {a | P a} h
    have hmin : ∀ b, P b → r ((InvImage.wf r wellFounded_lt).min {a | P a} h) ≤ r b :=
      fun b hb => not_lt.mp ((InvImage.wf r wellFounded_lt).not_lt_min {a | P a} hb)
    constructor
    · rintro rfl
      exact Or.inl ⟨hmem, hmin⟩
    · rintro (⟨ha, ham⟩ | ⟨hn, -⟩)
      · exact hr (le_antisymm (hmin a ha) (ham _ hmem))
      · exact absurd hmem (hn _)
  · rw [dif_neg h]
    push Not at h
    constructor
    · rintro rfl
      exact Or.inr ⟨h, rfl⟩
    · rintro (⟨ha, -⟩ | ⟨-, hd⟩)
      · exact absurd ha (h a)
      · exact hd

/-- **Measurability of the least-index choice.**  If each predicate `P b` is measurable, so
is each level set of `ω ↦ firstSat r (P · ω) d`. -/
lemma measurable_firstSat_eq {X α : Type*} [Countable X] [MeasurableSpace α] {r : X → ℕ}
    (hr : Function.Injective r) {P : X → α → Prop} (hP : ∀ b, Measurable (P b)) (d a : X) :
    Measurable fun ω => firstSat r (fun b => P b ω) d = a := by
  have e : (fun ω => firstSat r (fun b => P b ω) d = a) = fun ω =>
      (P a ω ∧ ∀ b, P b ω → r a ≤ r b) ∨ ((∀ b, ¬ P b ω) ∧ d = a) := by
    funext ω
    exact propext (firstSat_eq_iff hr _ d a)
  rw [e]
  exact ((hP a).and (Measurable.forall fun b => (hP b).imp measurable_const)).or
    ((Measurable.forall fun b => (hP b).not).and measurable_const)

end FirstSat

/-! ### Projections along a compact factor -/

section Proj

/-- The projection of a closed set along a compact factor is closed. -/
lemma isClosed_exists_mem {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] {K : Set P}
    (hK : IsCompact K) {F : Set (M × P)} (hF : IsClosed F) :
    IsClosed {m | ∃ p ∈ K, (m, p) ∈ F} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hG : IsClosed {q : M × K | (q.1, (q.2 : P)) ∈ F} :=
    hF.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have h := isClosedMap_fst_of_compactSpace (X := M) (Y := K) _ hG
  convert h using 1
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists, Subtype.exists, exists_and_right,
    exists_eq_right]
  constructor
  · rintro ⟨p, hp, hm⟩
    exact ⟨p, hp, hm⟩
  · rintro ⟨p, hp, hm⟩
    exact ⟨p, hp, hm⟩

/-- The projection along a compact factor of the intersection of a closed and an open set is
measurable (it is `F_σ`). -/
lemma measurableSet_exists_closed_open {M P : Type*} [PseudoEMetricSpace M]
    [PseudoEMetricSpace P] [MeasurableSpace M] [OpensMeasurableSpace M] {K : Set P}
    (hK : IsCompact K) {F U : Set (M × P)} (hF : IsClosed F) (hU : IsOpen U) :
    MeasurableSet {m | ∃ p ∈ K, (m, p) ∈ F ∧ (m, p) ∈ U} := by
  obtain ⟨C, hC, -, hCU, -⟩ := hU.exists_iUnion_isClosed
  have e : {m | ∃ p ∈ K, (m, p) ∈ F ∧ (m, p) ∈ U} =
      ⋃ k, {m | ∃ p ∈ K, (m, p) ∈ F ∩ C k} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, ← hCU]
    constructor
    · rintro ⟨p, hp, hF, k, hk⟩
      exact ⟨k, p, hp, hF, hk⟩
    · rintro ⟨k, p, hp, hF, hk⟩
      exact ⟨p, hp, hF, k, hk⟩
  rw [e]
  exact MeasurableSet.iUnion fun k => (isClosed_exists_mem hK (hF.inter (hC k))).measurableSet

lemma isClosed_forall {α ι : Type*} [TopologicalSpace α] {P : ι → α → Prop}
    (h : ∀ i, IsClosed {x | P i x}) : IsClosed {x | ∀ i, P i x} := by
  simpa only [Set.setOf_forall] using isClosed_iInter h

lemma isClosed_imp_const {α : Type*} [TopologicalSpace α] (c : Prop) {P : α → Prop}
    (h : IsClosed {x | P x}) : IsClosed {x | c → P x} := by
  by_cases hc : c
  · have e : {x | c → P x} = {x | P x} := Set.ext fun x => ⟨fun h' => h' hc, fun h' _ => h'⟩
    rw [e]; exact h
  · have e : {x | c → P x} = Set.univ := Set.eq_univ_of_forall fun x h' => absurd h' hc
    rw [e]; exact isClosed_univ

lemma isClosed_and {α : Type*} [TopologicalSpace α] {P Q : α → Prop}
    (hP : IsClosed {x | P x}) (hQ : IsClosed {x | Q x}) : IsClosed {x | P x ∧ Q x} :=
  hP.inter hQ
end Proj

/-! ### The stopping test and the step rule are Borel in the estimate -/

section CDMeas

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma continuous_cdObj2 (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (β : ℝ) (S : Finset Z) (z : Z) :
    Continuous fun q : (n → ℝ) × (S → ℝ) => cdObj V ψ q.1 β S z q.2 := by
  unfold cdObj cdContrast qinv
  simp only [dotProduct, mulVec]
  fun_prop

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma continuous_cdContrast (ψ : Z → n → ℝ) (S : Finset Z) (z : Z) :
    Continuous fun p : S → ℝ => cdContrast ψ S z p := by
  unfold cdContrast
  fun_prop

omit [DecidableEq X] in
lemma continuous_cdScore (V : Matrix n n ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (x : X) :
    Continuous fun g : n → ℝ => cdScore V φ cost g x := by
  unfold cdScore
  simp only [dotProduct]
  fun_prop

omit [DecidableEq Z] [Nonempty Z] in
/-- The test `cdDualCert` is a Borel (indeed closed) predicate of the estimate. -/
lemma measurable_cdDualCert (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (β ε : ℝ) (S : Finset Z) :
    Measurable fun m : n → ℝ => cdDualCert V ψ m β ε S := by
  unfold cdDualCert
  refine measurable_const.and (Measurable.forall fun z => measurable_const.imp ?_)
  exact measurableSet_setOfPred.1 (isClosed_exists_mem (isCompact_simplex S)
    (F := {q : (n → ℝ) × (S → ℝ) | cdObj V ψ q.1 β S z q.2 ≤ ε})
    (isClosed_le (continuous_cdObj2 V ψ β S z) continuous_const)).measurableSet

omit [DecidableEq Z] [Nonempty Z] in
/-- A predicate of the support only, existentially quantified over actions. -/
lemma measurable_exists_supp {α : Type*} [MeasurableSpace α] (supp : A → Finset Z)
    {Q : Finset Z → α → Prop} (hQ : ∀ S, Measurable (Q S)) :
    Measurable fun x => ∃ b, Q (supp b) x := by
  have e : (fun x => ∃ b, Q (supp b) x) = fun x => ∃ S : Finset Z, (∃ b, supp b = S) ∧ Q S x := by
    funext x
    refine propext ⟨fun ⟨b, hb⟩ => ⟨supp b, ⟨b, rfl⟩, hb⟩, ?_⟩
    rintro ⟨S, ⟨b, rfl⟩, hb⟩
    exact ⟨b, hb⟩
  rw [e]
  exact Measurable.exists fun S => measurable_const.and (hQ S)

/-- The body of `CDStep` for a fixed support `S`, optimistic terminal `yopt` and outside
challenger `z`. -/
def StepS (V : Matrix n n ℝ) (m : n → ℝ) (β ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ)
    (ι : Z → X) (S : Finset Z) (yopt z : Z) (x : X) : Prop :=
  ∃ p : S → ℝ,
    (∀ y, φ (ι y) ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι y))) ≤
      φ (ι yopt) ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι yopt)))) ∧
    yopt ∈ S ∧ z ∉ S ∧ p ∈ simplex S ∧
    (∀ q ∈ simplex S, cdObj V (fun z => φ (ι z)) m β S z p ≤
      cdObj V (fun z => φ (ι z)) m β S z q) ∧
    (∀ z', z' ∉ S → ∃ q ∈ simplex S,
      cdObj V (fun z => φ (ι z)) m β S z' q ≤ cdObj V (fun z => φ (ι z)) m β S z p) ∧
    ∀ x', cdScore V φ cost
        (cdSafeguard ε m (cdContrast (fun z => φ (ι z)) S z p) (φ (ι z) - φ (ι yopt))) x' ≤
      cdScore V φ cost
        (cdSafeguard ε m (cdContrast (fun z => φ (ι z)) S z p) (φ (ι z) - φ (ι yopt))) x

lemma cdSafeguard_of_le {ε : ℝ} {m g g' : n → ℝ} (h : g ⬝ᵥ m ≤ ε / 2) :
    cdSafeguard ε m g g' = g := by
  unfold cdSafeguard; exact if_pos h

lemma cdSafeguard_of_lt {ε : ℝ} {m g g' : n → ℝ} (h : ε / 2 < g ⬝ᵥ m) :
    cdSafeguard ε m g g' = g' := by
  unfold cdSafeguard; exact if_neg (not_le.mpr h)

/-- The closed conditions of `StepS` other than the score condition. -/
def stepG (V : Matrix n n ℝ) (β : ℝ) (φ : X → n → ℝ) (ι : Z → X) (S : Finset Z)
    (yopt z : Z) : Set ((n → ℝ) × (S → ℝ)) :=
  {q | ∀ y, φ (ι y) ⬝ᵥ q.1 + β * Real.sqrt (qinv V (φ (ι y))) ≤
      φ (ι yopt) ⬝ᵥ q.1 + β * Real.sqrt (qinv V (φ (ι yopt)))} ∩
    ({_q | yopt ∈ S ∧ z ∉ S} ∩
    ({q | ∀ r, r ∈ simplex S → cdObj V (fun z => φ (ι z)) q.1 β S z q.2 ≤
        cdObj V (fun z => φ (ι z)) q.1 β S z r} ∩
    {q | ∀ z', z' ∉ S → ∃ r ∈ simplex S, cdObj V (fun z => φ (ι z)) q.1 β S z' r ≤
        cdObj V (fun z => φ (ι z)) q.1 β S z q.2}))

set_option maxHeartbeats 1000000 in
omit [DecidableEq X] [Fintype Z] [Nonempty Z] in
lemma isClosed_stepG (V : Matrix n n ℝ) (β : ℝ) (φ : X → n → ℝ) (ι : Z → X) (S : Finset Z)
    (yopt z : Z) : IsClosed (stepG V β φ ι S yopt z) := by
  have hobj := continuous_cdObj2 V (fun z => φ (ι z)) β S
  have h1 : IsClosed {q : (n → ℝ) × (S → ℝ) | ∀ y,
      φ (ι y) ⬝ᵥ q.1 + β * Real.sqrt (qinv V (φ (ι y))) ≤
      φ (ι yopt) ⬝ᵥ q.1 + β * Real.sqrt (qinv V (φ (ι yopt)))} := by
    refine isClosed_forall fun y => isClosed_le ?_ ?_
    · exact (continuous_const.dotProduct continuous_fst).add continuous_const
    · exact (continuous_const.dotProduct continuous_fst).add continuous_const
  have h4 : IsClosed {q : (n → ℝ) × (S → ℝ) | ∀ r, r ∈ simplex S →
      cdObj V (fun z => φ (ι z)) q.1 β S z q.2 ≤ cdObj V (fun z => φ (ι z)) q.1 β S z r} := by
    refine isClosed_forall fun r => isClosed_imp_const (r ∈ simplex S) ?_
    have hr : Continuous fun q : (n → ℝ) × (S → ℝ) => cdObj V (fun z => φ (ι z)) q.1 β S z r :=
      by unfold cdObj cdContrast qinv; simp only [dotProduct, mulVec]; fun_prop
    exact isClosed_le (hobj z) hr
  have h5 : IsClosed {q : (n → ℝ) × (S → ℝ) | ∀ z', z' ∉ S → ∃ r ∈ simplex S,
      cdObj V (fun z => φ (ι z)) q.1 β S z' r ≤ cdObj V (fun z => φ (ι z)) q.1 β S z q.2} := by
    refine isClosed_forall fun z' => isClosed_imp_const (z' ∉ S) ?_
    have hf : Continuous fun w : ((n → ℝ) × (S → ℝ)) × (S → ℝ) =>
        cdObj V (fun z => φ (ι z)) w.1.1 β S z' w.2 :=
      by unfold cdObj cdContrast qinv; simp only [dotProduct, mulVec]; fun_prop
    have hg : Continuous fun w : ((n → ℝ) × (S → ℝ)) × (S → ℝ) =>
        cdObj V (fun z => φ (ι z)) w.1.1 β S z w.1.2 :=
      by unfold cdObj cdContrast qinv; simp only [dotProduct, mulVec]; fun_prop
    exact isClosed_exists_mem (isCompact_simplex S) (isClosed_le hf hg)
  have h2 : IsClosed {_q : (n → ℝ) × (S → ℝ) | yopt ∈ S ∧ z ∉ S} := isClosed_const
  have h := h1.inter (h2.inter (h4.inter h5))
  exact h

omit [DecidableEq X] [Nonempty Z] in
lemma measurable_StepS (V : Matrix n n ℝ) (β ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ)
    (ι : Z → X) (S : Finset Z) (yopt z : Z) (x : X) :
    Measurable fun m => StepS V m β ε φ cost ι S yopt z x := by
  have hgd : Continuous fun p : S → ℝ => cdContrast (fun z => φ (ι z)) S z p :=
    continuous_cdContrast (fun z => φ (ι z)) S z
  have hsc := continuous_cdScore V φ cost
  have hdot : Continuous fun q : (n → ℝ) × (S → ℝ) =>
      cdContrast (fun z => φ (ι z)) S z q.2 ⬝ᵥ q.1 :=
    (hgd.comp continuous_snd).dotProduct continuous_fst
  have hF1 : IsClosed (stepG V β φ ι S yopt z ∩ {q : (n → ℝ) × (S → ℝ) |
      cdContrast (fun z => φ (ι z)) S z q.2 ⬝ᵥ q.1 ≤ ε / 2 ∧
      ∀ x', cdScore V φ cost (cdContrast (fun z => φ (ι z)) S z q.2) x' ≤
        cdScore V φ cost (cdContrast (fun z => φ (ι z)) S z q.2) x}) :=
    (isClosed_stepG V β φ ι S yopt z).inter (isClosed_and (isClosed_le hdot continuous_const)
      (isClosed_forall fun x' => isClosed_le ((hsc x').comp (hgd.comp continuous_snd))
        ((hsc x).comp (hgd.comp continuous_snd))))
  have hF2 : IsClosed (stepG V β φ ι S yopt z ∩ {_q : (n → ℝ) × (S → ℝ) |
      ∀ x', cdScore V φ cost (φ (ι z) - φ (ι yopt)) x' ≤
        cdScore V φ cost (φ (ι z) - φ (ι yopt)) x}) :=
    (isClosed_stepG V β φ ι S yopt z).inter isClosed_const
  have hU : IsOpen {q : (n → ℝ) × (S → ℝ) |
      ε / 2 < cdContrast (fun z => φ (ι z)) S z q.2 ⬝ᵥ q.1} :=
    isOpen_lt continuous_const hdot
  have e : {m | StepS V m β ε φ cost ι S yopt z x} =
      {m | ∃ p ∈ simplex S, (m, p) ∈ stepG V β φ ι S yopt z ∩ {q : (n → ℝ) × (S → ℝ) |
        cdContrast (fun z => φ (ι z)) S z q.2 ⬝ᵥ q.1 ≤ ε / 2 ∧
        ∀ x', cdScore V φ cost (cdContrast (fun z => φ (ι z)) S z q.2) x' ≤
          cdScore V φ cost (cdContrast (fun z => φ (ι z)) S z q.2) x} ∧
        (m, p) ∈ (Set.univ : Set ((n → ℝ) × (S → ℝ)))} ∪
      {m | ∃ p ∈ simplex S, (m, p) ∈ stepG V β φ ι S yopt z ∩ {_q : (n → ℝ) × (S → ℝ) |
        ∀ x', cdScore V φ cost (φ (ι z) - φ (ι yopt)) x' ≤
          cdScore V φ cost (φ (ι z) - φ (ι yopt)) x} ∧
        (m, p) ∈ {q : (n → ℝ) × (S → ℝ) |
          ε / 2 < cdContrast (fun z => φ (ι z)) S z q.2 ⬝ᵥ q.1}} := by
    ext m
    constructor
    · rintro ⟨p, h1, hy, hz, hp, h4, h5, h6⟩
      by_cases hc : cdContrast (fun z => φ (ι z)) S z p ⬝ᵥ m ≤ ε / 2
      · rw [cdSafeguard_of_le hc] at h6
        exact Or.inl ⟨p, hp, ⟨⟨h1, ⟨hy, hz⟩, h4, h5⟩, hc, h6⟩, trivial⟩
      · rw [cdSafeguard_of_lt (lt_of_not_ge hc)] at h6
        exact Or.inr ⟨p, hp, ⟨⟨h1, ⟨hy, hz⟩, h4, h5⟩, h6⟩, lt_of_not_ge hc⟩
    · rintro (⟨p, hp, ⟨⟨h1, ⟨hy, hz⟩, h4, h5⟩, hc, h6⟩, -⟩ |
        ⟨p, hp, ⟨⟨h1, ⟨hy, hz⟩, h4, h5⟩, h6⟩, hc⟩)
      · refine ⟨p, h1, hy, hz, hp, h4, h5, ?_⟩
        rw [cdSafeguard_of_le hc]
        exact h6
      · refine ⟨p, h1, hy, hz, hp, h4, h5, ?_⟩
        rw [cdSafeguard_of_lt hc]
        exact h6
  refine measurableSet_setOfPred.1 ?_
  rw [e]
  exact (measurableSet_exists_closed_open (isCompact_simplex S) hF1 isOpen_univ).union
    (measurableSet_exists_closed_open (isCompact_simplex S) hF2 hU)
omit [DecidableEq X] [Nonempty Z] in
/-- **The step rule `CDStep` is a Borel predicate of the estimate** (design matrix and
radius fixed). -/
lemma measurable_CDStep (V : Matrix n n ℝ) (β ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ)
    (ι : Z → X) (supp : A → Finset Z) (x : X) :
    Measurable fun m => CDStep V m β ε φ cost ι supp x := by
  have e : (fun m => CDStep V m β ε φ cost ι supp x) =
      fun m => ∃ yopt, ∃ b, ∃ z, StepS V m β ε φ cost ι (supp b) yopt z x := rfl
  rw [e]
  exact Measurable.exists fun yopt => measurable_exists_supp supp
    (Q := fun S m => ∃ z, StepS V m β ε φ cost ι S yopt z x)
    fun S => Measurable.exists fun z => measurable_StepS V β ε φ cost ι S yopt z x

end CDMeas

/-! ### An explicit causal CD policy and its measurability -/

section Policy

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- A fixed injective ranking of the finite query set (used for tie-breaking). -/
noncomputable def rk (X : Type*) [Fintype X] : X → ℕ := fun a => (Fintype.equivFin X a : ℕ)

lemma rk_injective (X : Type*) [Fintype X] : Function.Injective (rk X) := fun _ _ h =>
  (Fintype.equivFin X).injective (Fin.ext h)

variable (lam σ δ B ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X) (supp : A → Finset Z)
  (θs : n → ℝ) (x0 : X)

/-- **One step of the CD policy.**  Given past queries `xs` and the noise path `v`, at time
`t`: if the stopping test passes (with the ridge estimate and the radius `eq:ay-radius`),
query the default `x0`; otherwise query the least-ranked `x` satisfying `CDStep`. -/
noncomputable def cdNext (xs : ℕ → X) (v : ℕ → ℝ) (t : ℕ) : X := by
  classical
  exact if CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t then x0
    else firstSat (rk X) (fun a => CDStep (design lam φ xs t) (ridgeEst lam φ θs xs v t)
      (ayRadius σ lam δ B (design lam φ xs t)) ε φ cost ι supp a) x0

/-- **The CD policy**: the query sequence generated by `cdNext` from the noise path `v`. -/
noncomputable def cdPol (v : ℕ → ℝ) : ℕ → X
  | t => cdNext lam σ δ B ε φ cost ι supp θs x0
      (fun s => if _h : s < t then cdPol v s else x0) v t
termination_by t => t

lemma cdPol_eq (v : ℕ → ℝ) (t : ℕ) :
    cdPol lam σ δ B ε φ cost ι supp θs x0 v t = cdNext lam σ δ B ε φ cost ι supp θs x0
      (fun s => if _h : s < t then cdPol lam σ δ B ε φ cost ι supp θs x0 v s else x0) v t := by
  rw [cdPol]

lemma cdNext_congr_x {xs xs' : ℕ → X} {v : ℕ → ℝ} {t : ℕ} (h : ∀ s < t, xs s = xs' s) :
    cdNext lam σ δ B ε φ cost ι supp θs x0 xs v t =
      cdNext lam σ δ B ε φ cost ι supp θs x0 xs' v t := by
  have h1 := design_congr lam φ t h
  have h2 := ridgeEst_congr2 lam φ θs (η := v) (η' := v) h (fun _ _ => rfl)
  have hc : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t ↔
      CDCertified lam φ ι supp ε xs' (ridgeEst lam φ θs xs' v)
      (fun t => ayRadius σ lam δ B (design lam φ xs' t)) t := by
    simp only [CDCertified, h1, h2]
  unfold cdNext
  by_cases hc' : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t
  · rw [if_pos hc', if_pos (hc.mp hc')]
  · rw [if_neg hc', if_neg (fun h => hc' (hc.mpr h)), h1, h2]

lemma cdNext_congr_v {xs : ℕ → X} {v v' : ℕ → ℝ} {t : ℕ} (h : ∀ s < t, v s = v' s) :
    cdNext lam σ δ B ε φ cost ι supp θs x0 xs v t =
      cdNext lam σ δ B ε φ cost ι supp θs x0 xs v' t := by
  have h2 := ridgeEst_congr2 lam φ θs (x := xs) (x' := xs) (fun _ _ => rfl) h
  have hc : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t ↔
      CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v')
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t := by
    simp only [CDCertified, h2]
  unfold cdNext
  by_cases hc' : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t
  · rw [if_pos hc', if_pos (hc.mp hc')]
  · rw [if_neg hc', if_neg (fun h => hc' (hc.mpr h)), h2]

/-- **The CD policy is causal**: `cdPol v t` depends on `v` only through `v 0, …, v (t-1)`. -/
theorem cdPol_causal (t : ℕ) : ∀ v v' : ℕ → ℝ, (∀ s < t, v s = v' s) →
    cdPol lam σ δ B ε φ cost ι supp θs x0 v t = cdPol lam σ δ B ε φ cost ι supp θs x0 v' t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v v' h
    rw [cdPol_eq, cdPol_eq]
    have e : (fun s => if _h : s < t then cdPol lam σ δ B ε φ cost ι supp θs x0 v s else x0) =
        (fun s => if _h : s < t then cdPol lam σ δ B ε φ cost ι supp θs x0 v' s else x0) := by
      funext s
      split_ifs with hs
      · exact ih s hs v v' (fun r hr => h r (hr.trans hs))
      · rfl
    rw [e]
    exact cdNext_congr_v lam σ δ B ε φ cost ι supp θs x0 h

lemma cdPol_eq' (v : ℕ → ℝ) (t : ℕ) :
    cdPol lam σ δ B ε φ cost ι supp θs x0 v t = cdNext lam σ δ B ε φ cost ι supp θs x0
      (cdPol lam σ δ B ε φ cost ι supp θs x0 v) v t := by
  rw [cdPol_eq]
  exact cdNext_congr_x lam σ δ B ε φ cost ι supp θs x0 (fun s hs => by simp only [hs,
    ↓reduceDIte])

/-- **The CD policy runs Algorithm `alg:cd-joint`**: on every noise path, the queries form an
infinite run with the ridge estimate and the radius `eq:ay-radius`.  (Supports cover the
terminals, `ε ≥ 0`.) -/
theorem cdPol_run (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    (hε : 0 ≤ ε) (v : ℕ → ℝ) :
    CDRun lam φ cost ι supp ε (cdPol lam σ δ B ε φ cost ι supp θs x0 v)
      (ridgeEst lam φ θs (cdPol lam σ δ B ε φ cost ι supp θs x0 v) v)
      (fun t => ayRadius σ lam δ B (design lam φ (cdPol lam σ δ B ε φ cost ι supp θs x0 v) t)) := by
  intro t hnc
  rw [cdPol_eq' lam σ δ B ε φ cost ι supp θs x0 v t]
  unfold cdNext
  rw [if_neg hnc]
  exact firstSat_spec _ _ (cdStep_exists _ _ _ ε φ cost ι supp hne hcov hε
    (fun a ha => hnc ⟨a, ha⟩))

lemma measurable_ridgeEst (xs : ℕ → X) (t : ℕ) :
    Measurable fun v : ℕ → ℝ => ridgeEst lam φ θs xs v t := by
  unfold ridgeEst
  refine Continuous.measurable ?_
  exact continuous_const.matrix_mulVec (continuous_finsetSum _ fun s _ =>
    (continuous_const.add (continuous_apply s)).smul continuous_const)

lemma measurable_cdNext_eq (xs : ℕ → X) (t : ℕ) (a : X) :
    Measurable fun v => cdNext lam σ δ B ε φ cost ι supp θs x0 xs v t = a := by
  set C : (ℕ → ℝ) → Prop := fun v => CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
    (fun t => ayRadius σ lam δ B (design lam φ xs t)) t with hCdef
  set P : X → (ℕ → ℝ) → Prop := fun b v => CDStep (design lam φ xs t) (ridgeEst lam φ θs xs v t)
    (ayRadius σ lam δ B (design lam φ xs t)) ε φ cost ι supp b with hPdef
  have hC : Measurable C :=
    measurable_exists_supp supp (Q := fun S v => cdDualCert (design lam φ xs t)
      (fun z => φ (ι z)) (ridgeEst lam φ θs xs v t) (ayRadius σ lam δ B (design lam φ xs t)) ε S)
      fun S => (measurable_cdDualCert _ _ _ _ S).comp (measurable_ridgeEst lam φ θs xs t)
  have hP : ∀ b, Measurable (P b) := fun b =>
    (measurable_CDStep _ _ ε φ cost ι supp b).comp (measurable_ridgeEst lam φ θs xs t)
  have e : (fun v => cdNext lam σ δ B ε φ cost ι supp θs x0 xs v t = a) =
      fun v => (C v ∧ x0 = a) ∨ (¬ C v ∧ firstSat (rk X) (fun b => P b v) x0 = a) := by
    funext v
    by_cases hc : C v
    · have : cdNext lam σ δ B ε φ cost ι supp θs x0 xs v t = x0 := by
        unfold cdNext; exact if_pos hc
      rw [this]
      exact propext ⟨fun h => Or.inl ⟨hc, h⟩, fun h => h.elim (fun h => h.2)
        (fun h => absurd hc h.1)⟩
    · have : cdNext lam σ δ B ε φ cost ι supp θs x0 xs v t = firstSat (rk X) (fun b => P b v) x0 := by
        unfold cdNext; exact if_neg hc
      rw [this]
      exact propext ⟨fun h => Or.inr ⟨hc, h⟩, fun h => h.elim (fun h => absurd h.1 hc)
        (fun h => h.2)⟩
  rw [e]
  exact (hC.and measurable_const).or
    (hC.not.and (measurable_firstSat_eq (rk_injective X) hP x0 a))

/-- **The queries of the CD policy are Borel functions of the noise path.** -/
theorem measurableSet_cdPol (t : ℕ) : ∀ a : X,
    MeasurableSet {v : ℕ → ℝ | cdPol lam σ δ B ε φ cost ι supp θs x0 v t = a} := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro a
    let ext : (Fin t → X) → ℕ → X := fun h s => if hs : s < t then h ⟨s, hs⟩ else x0
    have e : {v : ℕ → ℝ | cdPol lam σ δ B ε φ cost ι supp θs x0 v t = a} =
        ⋃ h : Fin t → X, ({v | ∀ i : Fin t, cdPol lam σ δ B ε φ cost ι supp θs x0 v i = h i} ∩
          {v | cdNext lam σ δ B ε φ cost ι supp θs x0 (ext h) v t = a}) := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hv
        refine ⟨fun i => cdPol lam σ δ B ε φ cost ι supp θs x0 v i, fun i => rfl, ?_⟩
        rw [← hv, cdPol_eq' lam σ δ B ε φ cost ι supp θs x0 v t]
        exact cdNext_congr_x lam σ δ B ε φ cost ι supp θs x0 (fun s hs => by
          simp only [ext, hs, ↓reduceDIte])
      · rintro ⟨h, hh, hn⟩
        rw [cdPol_eq' lam σ δ B ε φ cost ι supp θs x0 v t, ← hn]
        exact cdNext_congr_x lam σ δ B ε φ cost ι supp θs x0 (fun s hs => by
          simp only [ext, hs, ↓reduceDIte]
          exact hh ⟨s, hs⟩)
    rw [e]
    refine MeasurableSet.iUnion fun h => MeasurableSet.inter ?_
      (measurableSet_setOfPred.2 (measurable_cdNext_eq lam σ δ B ε φ cost ι supp θs x0 _ t a))
    exact measurableSet_setOfPred.2 (Measurable.forall fun i =>
      measurableSet_setOfPred.1 (ih i i.2 (h i)))

end Policy

/-! ### I.i.d. sub-Gaussian noise on `ℕ → ℝ` -/

section Noise

/-- `nFilt k` is generated by the first `k` coordinates of the noise path. -/
def nFilt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ)) where
  seq k := Filtration.piFinset (X := fun _ : ℕ => ℝ) (Finset.range k)
  mono' _ _ hij :=
    (Filtration.piFinset (X := fun _ : ℕ => ℝ)).mono (Finset.range_subset_range.2 hij)
  le' _ := (Filtration.piFinset (X := fun _ : ℕ => ℝ)).le _

lemma nFilt_eq (k : ℕ) : (nFilt k : MeasurableSpace (ℕ → ℝ)) =
    MeasurableSpace.comap (Finset.range k).restrict MeasurableSpace.pi := rfl

/-- A Borel set of noise paths that depends only on the first `t` coordinates is
`nFilt t`-measurable. -/
lemma measurableSet_nFilt_of_causal {t : ℕ} {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hc : ∀ v v' : ℕ → ℝ, (∀ s < t, v s = v' s) → v ∈ S → v' ∈ S) :
    MeasurableSet[nFilt t] S := by
  rw [nFilt_eq]
  let e : (Finset.range t → ℝ) → ℕ → ℝ := fun w s => if h : s ∈ Finset.range t then w ⟨s, h⟩ else 0
  have he : Measurable e := by
    refine measurable_pi_iff.mpr fun s => ?_
    by_cases h : s ∈ Finset.range t
    · simp only [e, h, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [e, h, ↓reduceDIte]
      exact measurable_const
  have hagree : ∀ v : ℕ → ℝ, ∀ s < t, e ((Finset.range t).restrict v) s = v s := by
    intro v s hs
    simp only [e, Finset.mem_range.2 hs, ↓reduceDIte, Finset.restrict]
  refine ⟨e ⁻¹' S, he hS, ?_⟩
  ext v
  simp only [Set.mem_preimage]
  exact ⟨fun h => hc _ v (hagree v) h, fun h => hc v _ (fun s hs => (hagree v s hs).symm) h⟩

/-- I.i.d. noise with law `ν`. -/
noncomputable def noiseP (ν : Measure ℝ) [IsProbabilityMeasure ν] : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => ν)

instance (ν : Measure ℝ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (noiseP ν) := by
  unfold noiseP; infer_instance

lemma noise_adapted (s : ℕ) : Measurable[nFilt (s + 1)] (fun v : ℕ → ℝ => v s) := by
  rw [nFilt_eq]
  have h : Measurable fun r : Finset.range (s + 1) → ℝ =>
      r ⟨s, Finset.mem_range.2 (Nat.lt_succ_self s)⟩ := measurable_pi_apply _
  exact h.comp (comap_measurable _)

/-- **I.i.d. noise with a `σ`-sub-Gaussian law is conditionally `σ`-sub-Gaussian** given the
past noise. -/
theorem noise_condSubG (ν : Measure ℝ) [IsProbabilityMeasure ν] {σ : ℝ}
    (hν : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2))) (s : ℕ) :
    CondSubG (noiseP ν) (nFilt s) (fun v : ℕ → ℝ => v s) σ := by
  have hiind : iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) => ω i) (noiseP ν) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ x => x) (fun _ => measurable_id)
  have hdisj : Disjoint ({s} : Finset ℕ) (Finset.range s) := by
    rw [Finset.disjoint_singleton_left]
    simp
  have hind := hiind.indepFun_finset {s} (Finset.range s) hdisj (fun i => measurable_pi_apply i)
  have hle : MeasurableSpace.comap (fun v : ℕ → ℝ => v s) (inferInstance : MeasurableSpace ℝ) ≤
      MeasurableSpace.comap (fun (a : ℕ → ℝ) (i : ({s} : Finset ℕ)) => a i)
        MeasurableSpace.pi := by
    have h1 : (fun v : ℕ → ℝ => v s) =
        (fun r : (({s} : Finset ℕ)) → ℝ => r ⟨s, Finset.mem_singleton_self s⟩) ∘
          (fun (a : ℕ → ℝ) (i : ({s} : Finset ℕ)) => a i) := rfl
    rw [h1, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  have hind' : Indep (MeasurableSpace.comap (fun v : ℕ → ℝ => v s)
      (inferInstance : MeasurableSpace ℝ)) (nFilt s) (noiseP ν) :=
    indep_of_indep_of_le_left hind hle
  refine CondSubG.of_indep (nFilt.le s) (measurable_pi_apply s) hind' fun c => ?_
  have hreal : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (c * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have h1 := lintegral_map (μ := noiseP ν) hreal (measurable_pi_apply s)
  rw [noiseP, Measure.infinitePi_map_eval] at h1
  exact h1.symm.trans_le (hν c)

/-- The standard Gaussian law has a `1`-sub-Gaussian moment generating function. -/
lemma gaussian_mgf (c : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂(gaussianReal 0 1) ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * 1 ^ 2 / 2)) := by
  have h := lintegral_exp_of_map_gaussian (μ := gaussianReal 0 1) (X := id) measurable_id
    Measure.map_id c
  rw [NNReal.coe_one, Real.sqrt_one] at h
  exact h.le

end Noise

/-! ### `thm:t4-finite-sample` with continuous sub-Gaussian noise -/

section Main

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- The queries of the CD policy (`cdPol`, default query `ι z₀` for a fixed terminal `z₀`)
on the noise space `ℕ → ℝ`. -/
noncomputable def gQ (lam σ δ B ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (θs : n → ℝ) : ℕ → (ℕ → ℝ) → X :=
  fun t v => cdPol lam σ δ B ε φ cost ι supp θs (ι (Classical.arbitrary Z)) v t

/-- The ridge estimate on the noise space. -/
noncomputable def gEst (lam : ℝ) (φ : X → n → ℝ) (θs : n → ℝ) (x : ℕ → (ℕ → ℝ) → X) :
    ℕ → (ℕ → ℝ) → n → ℝ :=
  fun t ω => ridgeEst lam φ θs (fun s => x s ω) (fun s => ω s) t

/-- The radius `eq:ay-radius` on the noise space. -/
noncomputable def gRad (σ lam δ B : ℝ) (φ : X → n → ℝ) (x : ℕ → (ℕ → ℝ) → X) :
    ℕ → (ℕ → ℝ) → ℝ :=
  fun t ω => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)

omit [DecidableEq X] in
/-- **The hypotheses of `cd_joint_literal` hold with continuous noise.**  On `ℕ → ℝ` with
i.i.d. noise of law `ν` (a probability measure on `ℝ` with
`∫ exp (c x) dν ≤ exp (c² σ² / 2)` for all `c`): the noise is adapted to `nFilt` and
conditionally `σ`-sub-Gaussian, and the explicit CD policy `gQ` is adapted (its queries are
Borel functions of the past noise) and is an infinite run of Algorithm `alg:cd-joint` with
the ridge estimate and the radius `eq:ay-radius` on every path.  (Supports cover the
terminals, `ε ≥ 0`.) -/
theorem subG_hyps (ν : Measure ℝ) [IsProbabilityMeasure ν] {σ : ℝ}
    (hν : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)))
    (lam δ B : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε : 0 ≤ ε) (θs : n → ℝ) :
    (∀ s, Measurable[nFilt (s + 1)] (fun ω : ℕ → ℝ => ω s)) ∧
    (∀ s, CondSubG (noiseP ν) (nFilt s) (fun ω : ℕ → ℝ => ω s) σ) ∧
    (∀ s x0, MeasurableSet[nFilt s] {ω | gQ lam σ δ B ε φ cost ι supp θs s ω = x0}) ∧
    ∀ ω, CDRun lam φ cost ι supp ε (fun s => gQ lam σ δ B ε φ cost ι supp θs s ω)
      (ridgeEst lam φ θs (fun s => gQ lam σ δ B ε φ cost ι supp θs s ω) (fun s => ω s))
      (fun t => ayRadius σ lam δ B (design lam φ
        (fun s => gQ lam σ δ B ε φ cost ι supp θs s ω) t)) := by
  refine ⟨noise_adapted, noise_condSubG ν hν, fun s x0 => ?_, fun ω => ?_⟩
  · exact measurableSet_nFilt_of_causal
      (measurableSet_cdPol lam σ δ B ε φ cost ι supp θs _ s x0)
      (fun v v' h hv => (cdPol_causal lam σ δ B ε φ cost ι supp θs _ s v v' h).symm.trans hv)
  · exact cdPol_run lam σ δ B ε φ cost ι supp θs _ hne hcov hε ω

/-- **`t4_finite_sample` with continuous sub-Gaussian noise.**  On `ℕ → ℝ` with i.i.d.
noise of law `ν`, any probability measure on `ℝ` with a `σ`-sub-Gaussian moment generating
function (`σ > 0`), for every fixed-feature instance whose supports cover the terminals,
`‖θ*‖ ≤ B`, `0 < δ < 1`: the explicit CD policy `gQ` is adapted, and with the ridge estimate
`gEst` and the radius `gRad` (`eq:ay-radius`) every hypothesis of
`LiteralF1.t4_finite_sample` holds (`β` positive, nondecreasing, anytime valid,
`liminf β_t² log t / t = 0`, `CDRun` on every path), and hence its conclusion. -/
theorem t4_finite_sample_subG [Nonempty n] (ν : Measure ℝ) [IsProbabilityMeasure ν] {σ : ℝ}
    (hσ : 0 < σ) (hν : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)))
    {lam δ B : ℝ} (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) :
    let x := gQ lam σ δ B ε φ cost ι supp θs
    (∀ s x0, MeasurableSet[nFilt s] {ω | x s ω = x0}) ∧
      (∀ t ω, 0 < gRad σ lam δ B φ x t ω) ∧
      (∀ ω, Monotone fun t => gRad σ lam δ B φ x t ω) ∧
      noiseP ν {ω | ∃ t, gRad σ lam δ B φ x t ω ^ 2 <
        (θs - gEst lam φ θs x t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ
          (θs - gEst lam φ θs x t ω)} ≤ ENNReal.ofReal δ ∧
      (∀ ω, Filter.liminf
        (fun t : ℕ => ((gRad σ lam δ B φ x t ω ^ 2 * Real.log t / t : ℝ) : EReal))
          atTop = 0) ∧
      (∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
        (fun t => gRad σ lam δ B φ x t ω)) ∧
    -- the conclusion of `t4_finite_sample`
    ((∀ ω, CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
        (fun t => gRad σ lam δ B φ x t ω)
        (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
          (fun t => gRad σ lam δ B φ x t ω)) ∧
      ∑ t ∈ range (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
          (fun t => gRad σ lam δ B φ x t ω)), cost (x t ω) ≤
        16 * cmax * (1 + Lsq / lam) *
          gRad σ lam δ B φ x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad σ lam δ B φ x t ω) - 1)
            ω ^ 2 / ε ^ 2 *
          Real.log ((design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
              (fun t => gRad σ lam δ B φ x t ω))).det / lam ^ Fintype.card n)) ∧
    (∀ ω, (∀ t, (θs - gEst lam φ θs x t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ
          (θs - gEst lam φ θs x t ω) ≤ gRad σ lam δ B φ x t ω ^ 2) →
      ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
              (fun t => gRad σ lam δ B φ x t ω)))
          (fun z => φ (ι z))
          (gEst lam φ θs x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad σ lam δ B φ x t ω)) ω)
          (gRad σ lam δ B φ x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad σ lam δ B φ x t ω)) ω)
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε) ∧
    noiseP ν {ω | ¬ ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
              (fun t => gRad σ lam δ B φ x t ω)))
          (fun z => φ (ι z))
          (gEst lam φ θs x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad σ lam δ B φ x t ω)) ω)
          (gRad σ lam δ B φ x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad σ lam δ B φ x t ω)) ω)
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤ ENNReal.ofReal δ) := by
  intro x
  obtain ⟨x0⟩ : Nonempty X := ⟨ι (Classical.arbitrary Z)⟩
  have hcmax : 0 ≤ cmax := (hcost x0).1.le.trans (hcost x0).2
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ x0)).trans (hφ x0)
  obtain ⟨hη, hsub, hx, hrun⟩ := subG_hyps ν hν lam δ B φ cost ι supp hne hcov hε.le θs
  obtain ⟨hpos, hmono, hcovP, -⟩ := ayRadius_generic_hyps (μ := noiseP ν) (ε := ε) (cmin := 1)
    nFilt hσ hlam hδ0 hδ1 hB φ hcmax one_pos hLsq hφ θs hθ x hx hη hsub
  have hlim : ∀ ω, Filter.liminf
      (fun t : ℕ => ((gRad σ lam δ B φ x t ω ^ 2 * Real.log t / t : ℝ) : EReal)) atTop = 0 :=
    fun ω => ayRadius_liminf (σ := σ) hlam hδ0 hδ1 φ hφ (fun s => x s ω)
  exact ⟨hx, hpos, hmono, hcovP, hlim, hrun,
    t4_finite_sample (μ := noiseP ν) hlam φ cost hcost hφ hε ι supp hne θs x
      (gEst lam φ θs x) (gRad σ lam δ B φ x) hpos hmono hcovP hlim hrun⟩

/-- **`t4_finite_sample` with i.i.d. standard Gaussian noise.**  The case
`ν = N(0, 1)` (`gaussianReal 0 1`), `σ = 1`, of `t4_finite_sample_subG`: the explicit CD
policy is adapted, every hypothesis of `LiteralF1.t4_finite_sample` holds with the ridge
estimate and the radius `eq:ay-radius`, and hence its conclusion. -/
theorem t4_finite_sample_gaussian [Nonempty n] {lam δ B : ℝ} (hlam : 0 < lam)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) :
    let x := gQ lam 1 δ B ε φ cost ι supp θs
    (∀ s x0, MeasurableSet[nFilt s] {ω | x s ω = x0}) ∧
      (∀ t ω, 0 < gRad 1 lam δ B φ x t ω) ∧
      (∀ ω, Monotone fun t => gRad 1 lam δ B φ x t ω) ∧
      noiseP (gaussianReal 0 1) {ω | ∃ t, gRad 1 lam δ B φ x t ω ^ 2 <
        (θs - gEst lam φ θs x t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ
          (θs - gEst lam φ θs x t ω)} ≤ ENNReal.ofReal δ ∧
      (∀ ω, Filter.liminf
        (fun t : ℕ => ((gRad 1 lam δ B φ x t ω ^ 2 * Real.log t / t : ℝ) : EReal))
          atTop = 0) ∧
      (∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
        (fun t => gRad 1 lam δ B φ x t ω)) ∧
    -- the conclusion of `t4_finite_sample`
    ((∀ ω, CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
        (fun t => gRad 1 lam δ B φ x t ω)
        (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
          (fun t => gRad 1 lam δ B φ x t ω)) ∧
      ∑ t ∈ range (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
          (fun t => gRad 1 lam δ B φ x t ω)), cost (x t ω) ≤
        16 * cmax * (1 + Lsq / lam) *
          gRad 1 lam δ B φ x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad 1 lam δ B φ x t ω) - 1)
            ω ^ 2 / ε ^ 2 *
          Real.log ((design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
              (fun t => gRad 1 lam δ B φ x t ω))).det / lam ^ Fintype.card n)) ∧
    (∀ ω, (∀ t, (θs - gEst lam φ θs x t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ
          (θs - gEst lam φ θs x t ω) ≤ gRad 1 lam δ B φ x t ω ^ 2) →
      ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
              (fun t => gRad 1 lam δ B φ x t ω)))
          (fun z => φ (ι z))
          (gEst lam φ θs x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad 1 lam δ B φ x t ω)) ω)
          (gRad 1 lam δ B φ x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad 1 lam δ B φ x t ω)) ω)
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε) ∧
    noiseP (gaussianReal 0 1) {ω | ¬ ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => gEst lam φ θs x t ω)
              (fun t => gRad 1 lam δ B φ x t ω)))
          (fun z => φ (ι z))
          (gEst lam φ θs x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad 1 lam δ B φ x t ω)) ω)
          (gRad 1 lam δ B φ x (cdStop lam φ ι supp ε (fun s => x s ω)
            (fun t => gEst lam φ θs x t ω) (fun t => gRad 1 lam δ B φ x t ω)) ω)
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤ ENNReal.ofReal δ) :=
  t4_finite_sample_subG (gaussianReal 0 1) one_pos gaussian_mgf hlam hδ0 hδ1 hB φ cost hcost
    hφ hε ι supp hne hcov θs hθ

end Main

end LiteralG1

end JointRootCert
