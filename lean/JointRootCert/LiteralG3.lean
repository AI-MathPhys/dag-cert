/-
`thm:t4-finite-sample` (Finite-sample cost of safeguarded CD-Joint) for Algorithm CD-Joint
(`alg:cd-joint`, with `eq:safeguard`) with its choices made sequentially, as in the
algorithm.

`LiteralG1.cdPol` picks, at an uncertified step, the least-ranked query `x` for which some
witnesses `(y_opt, b, z, p)` of `CDStep` exist.  Here each line of the algorithm is a
separate deterministic choice, made in the order of the algorithm:

* `ySel`: `y_t^opt`, the least-ranked maximiser of the optimistic index
  `φ_yᵀ m_t + β_t ‖φ_y‖_{V_t⁻¹}` (line `y_t^opt ∈ argmax …`);
* `bSel`: `b_t`, the least element, for a fixed well-order of the actions, of
  `{a | y_t^opt ∈ S(a)}` ("fixed tie breaking");
* `zSel`: `z_t`, the least-ranked maximiser over `z ∉ S(b_t)` of
  `D_t(z, S(b_t)) = min_{p ∈ Δ(S(b_t))} (g_{z,p}ᵀ m_t + β_t ‖g_{z,p}‖_{V_t⁻¹})` (`dVal`);
* `pSel`: `p_t^*`, the minimiser of `D_t(z_t, S(b_t))` of least Euclidean norm.  The
  minimisers form a nonempty compact convex set (the objective is convex because
  `‖·‖_{V⁻¹}` is a norm), so the least-norm minimiser is unique (`isPSel_unique`);
* `gSafe`: the safeguarded contrast `g_t` of `eq:safeguard`;
* `xSel`: `x_{t+1}`, the least-ranked maximiser of the score in `eq:safeguard`.

`seqStep_spec`: if no action passes the stopping test, these choices are witnesses of
`CDStep` for the query `seqStep` (so `seqStep_cdStep`).  Measurability: `ySel`, `zSel`,
`xSel` have measurable level sets (least-index choice over measurable predicates, reusing
`LiteralG1.measurable_firstSat_eq`); `bSel` is a function of `y_t^opt` only; `pSel` is a
Borel function of the estimate (`measurable_pSel`): its graph is Borel
(`measurableSet_isPSel`), and a function between Polish spaces with a Borel graph is Borel
(`measurable_of_graph`, by Suslin's theorem `AnalyticSet.measurableSet_of_compl`).

`seqPol`: the causal policy running these steps with the ridge estimate and the radius
`eq:ay-radius`; `seqPol_eq_step`, `seqPol_run`: on every noise path each uncertified query
is `seqStep` and satisfies `CDStep` with exactly the choices above; `seqPol_causal`,
`measurableSet_seqPol`: it is adapted.  `t4_finite_sample_subG_seq`,
`t4_finite_sample_gaussian_seq`: `LiteralG1.t4_finite_sample_subG` /
`t4_finite_sample_gaussian` for this policy.
-/
import JointRootCert.LiteralG1

namespace JointRootCert

namespace LiteralG3

open Finset MeasureTheory Matrix Filter ProbabilityTheory
open scoped ENNReal
open LiteralABC LiteralABC2 LiteralABC3 LiteralF1 LiteralG1

/-! ### A function with a Borel graph is Borel -/

/-- **A function between Polish spaces whose graph is Borel is Borel** (Suslin). -/
lemma measurable_of_graph {M P : Type*} [TopologicalSpace M] [PolishSpace M] [MeasurableSpace M]
    [BorelSpace M] [TopologicalSpace P] [PolishSpace P] [MeasurableSpace P] [BorelSpace P]
    {Γ : Set (M × P)} (hΓ : MeasurableSet Γ) {f : M → P} (hf : ∀ m p, (m, p) ∈ Γ ↔ f m = p) :
    Measurable f := by
  intro B hB
  have e : ∀ C : Set P, f ⁻¹' C = Prod.fst '' (Γ ∩ Set.univ ×ˢ C) := by
    intro C
    ext m
    constructor
    · intro h
      exact ⟨(m, f m), ⟨(hf m _).2 rfl, Set.mem_univ _, h⟩, rfl⟩
    · rintro ⟨⟨m', p⟩, ⟨hp, -, hC⟩, rfl⟩
      show f m' ∈ C
      rwa [(hf m' p).1 hp]
  have hA : ∀ C : Set P, MeasurableSet C → AnalyticSet (f ⁻¹' C) := fun C hC => by
    rw [e C]
    exact (hΓ.inter (MeasurableSet.univ.prod hC)).analyticSet_image measurable_fst
  refine AnalyticSet.measurableSet_of_compl (hA B hB) ?_
  rw [← Set.preimage_compl]
  exact hA _ hB.compl

/-- Dependent choice of a predicate through a countably-valued map with measurable level
sets. -/
lemma measurable_dep {α Y : Type*} [MeasurableSpace α] [Countable Y] {f : α → Y}
    (hf : ∀ y, Measurable fun ω => f ω = y) {Q : Y → α → Prop} (hQ : ∀ y, Measurable (Q y)) :
    Measurable fun ω => Q (f ω) ω := by
  have e : (fun ω => Q (f ω) ω) = fun ω => ∃ y, f ω = y ∧ Q y ω := by
    funext ω
    refine propext ⟨fun h => ⟨_, rfl, h⟩, ?_⟩
    rintro ⟨y, hy, h⟩
    subst hy
    exact h
  rw [e]
  exact Measurable.exists fun y => (hf y).and (hQ y)

/-! ### The minimising mixture `p_t^*`: least-norm minimiser -/

section PSel

variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [DecidableEq Z]

/-- `p` minimises the dual objective of `z` over the simplex of `S`. -/
def IsMinP (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β : ℝ) (S : Finset Z) (z : Z)
    (p : S → ℝ) : Prop :=
  p ∈ simplex S ∧ ∀ q ∈ simplex S, cdObj V ψ m β S z p ≤ cdObj V ψ m β S z q

/-- `p` is a minimiser of least Euclidean norm. -/
def IsPSel (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β : ℝ) (S : Finset Z) (z : Z)
    (p : S → ℝ) : Prop :=
  IsMinP V ψ m β S z p ∧ ∀ q, IsMinP V ψ m β S z q → p ⬝ᵥ p ≤ q ⬝ᵥ q

/-- **The selected mixture `p_t^*`**: the least-norm minimiser of the dual objective. -/
noncomputable def pSel (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β : ℝ) (S : Finset Z)
    (z : Z) : S → ℝ := by
  classical
  exact if h : ∃ p, IsPSel V ψ m β S z p then h.choose else 0

variable (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (β : ℝ) (S : Finset Z) (z : Z)

/-- The graph of the minimiser correspondence. -/
def gMin : Set ((n → ℝ) × (S → ℝ)) := {q | IsMinP V ψ q.1 β S z q.2}

lemma isClosed_gMin : IsClosed (gMin V ψ β S z) := by
  have hobj := continuous_cdObj2 V ψ β S z
  have h1 : IsClosed {q : (n → ℝ) × (S → ℝ) | q.2 ∈ simplex S} :=
    (isCompact_simplex S).isClosed.preimage continuous_snd
  have h2 : IsClosed {q : (n → ℝ) × (S → ℝ) | ∀ r, r ∈ simplex S →
      cdObj V ψ q.1 β S z q.2 ≤ cdObj V ψ q.1 β S z r} := by
    refine isClosed_forall fun r => isClosed_imp_const (r ∈ simplex S) ?_
    have hr : Continuous fun q : (n → ℝ) × (S → ℝ) => cdObj V ψ q.1 β S z r :=
      hobj.comp (f := fun q : (n → ℝ) × (S → ℝ) => (q.1, r)) (continuous_fst.prodMk continuous_const)
    exact isClosed_le hobj hr
  have e : gMin V ψ β S z = {q : (n → ℝ) × (S → ℝ) | q.2 ∈ simplex S} ∩
      {q : (n → ℝ) × (S → ℝ) | ∀ r, r ∈ simplex S →
        cdObj V ψ q.1 β S z q.2 ≤ cdObj V ψ q.1 β S z r} := rfl
  rw [e]
  exact h1.inter h2

lemma exists_isMinP (m : n → ℝ) (hS : S.Nonempty) : ∃ p, IsMinP V ψ m β S z p := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨p, hp, hpm⟩ := (isCompact_simplex S).exists_isMinOn
    ⟨_, single_mem_simplex (⟨i, hi⟩ : S)⟩ (continuous_cdObj V ψ m β S z).continuousOn
  exact ⟨p, hp, fun q hq => hpm hq⟩

lemma exists_isPSel (m : n → ℝ) (hS : S.Nonempty) : ∃ p, IsPSel V ψ m β S z p := by
  have hK : IsClosed {p : S → ℝ | IsMinP V ψ m β S z p} :=
    (isClosed_gMin V ψ β S z).preimage (continuous_const.prodMk continuous_id)
  have hKc : IsCompact {p : S → ℝ | IsMinP V ψ m β S z p} :=
    (isCompact_simplex S).of_isClosed_subset hK fun p hp => hp.1
  obtain ⟨p, hp, hpm⟩ := hKc.exists_isMinOn (exists_isMinP V ψ β S z m hS)
    (continuous_id.dotProduct continuous_id).continuousOn
  exact ⟨p, hp, fun q hq => hpm hq⟩

lemma isPSel_pSel (m : n → ℝ) (hS : S.Nonempty) : IsPSel V ψ m β S z (pSel V ψ m β S z) := by
  have h := exists_isPSel V ψ β S z m hS
  unfold pSel
  rw [dif_pos h]
  exact h.choose_spec

lemma qinv_smul' (c : ℝ) (a : n → ℝ) : qinv V (c • a) = c ^ 2 * qinv V a := by
  unfold qinv
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Midpoint convexity of the dual objective** (`‖·‖_{V⁻¹}` is a seminorm, `β ≥ 0`). -/
lemma cdObj_mid {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam) (hβ : 0 ≤ β) (m : n → ℝ)
    (p q : S → ℝ) :
    cdObj V ψ m β S z (fun y => (p y + q y) / 2) ≤
      (cdObj V ψ m β S z p + cdObj V ψ m β S z q) / 2 := by
  set a := cdContrast ψ S z p
  set b := cdContrast ψ S z q
  have hc : cdContrast ψ S z (fun y => (p y + q y) / 2) = (1 / 2 : ℝ) • (a + b) := by
    have hs : ∑ y : S, ((p y + q y) / 2) • ψ y =
        (1 / 2 : ℝ) • (∑ y : S, p y • ψ y + ∑ y : S, q y • ψ y) := by
      rw [← sum_add_distrib, smul_sum]
      refine sum_congr rfl fun y _ => ?_
      module
    simp only [a, b, cdContrast]
    rw [hs]
    module
  unfold cdObj
  rw [hc, qinv_smul', Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have htri := hV.sqrt_qinv_add_le hlam a b
  have hdot : ((1 / 2 : ℝ) • (a + b)) ⬝ᵥ m = (a ⬝ᵥ m + b ⬝ᵥ m) / 2 := by
    rw [smul_dotProduct, add_dotProduct, smul_eq_mul]
    ring
  rw [hdot]
  have := mul_le_mul_of_nonneg_left htri hβ
  nlinarith

/-- **Uniqueness of the least-norm minimiser.** -/
lemma isPSel_unique {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam) (hβ : 0 ≤ β)
    {m : n → ℝ} {p q : S → ℝ} (hp : IsPSel V ψ m β S z p) (hq : IsPSel V ψ m β S z q) :
    p = q := by
  set r : S → ℝ := fun y => (p y + q y) / 2 with hr
  have hrs : r ∈ simplex S := by
    refine ⟨fun y => div_nonneg (add_nonneg (hp.1.1.1 y) (hq.1.1.1 y)) two_pos.le, ?_⟩
    simp only [r]
    rw [← sum_div, sum_add_distrib, hp.1.1.2, hq.1.1.2]
    norm_num
  have hrm : IsMinP V ψ m β S z r := by
    refine ⟨hrs, fun s hs => ?_⟩
    have h1 := cdObj_mid V ψ β S z hV hlam hβ m p q
    have h2 := hp.1.2 s hs
    have h3 := hq.1.2 s hs
    simp only [r]
    linarith
  have h1 := hp.2 r hrm
  have h2 := hp.2 q hq.1
  have h3 := hq.2 p hp.1
  have hid : (p - q) ⬝ᵥ (p - q) = 2 * (p ⬝ᵥ p) + 2 * (q ⬝ᵥ q) - 4 * (r ⬝ᵥ r) := by
    simp only [dotProduct, r, Pi.sub_apply, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun y _ => ?_
    ring
  have h0 : (p - q) ⬝ᵥ (p - q) ≤ 0 := by rw [hid]; linarith
  exact sub_eq_zero.mp (eq_zero_of_dotProduct_self_nonpos h0)

/-- **The graph of `pSel` is Borel.** -/
lemma measurableSet_isPSel :
    MeasurableSet {q : (n → ℝ) × (S → ℝ) | IsPSel V ψ q.1 β S z q.2} := by
  have hG := isClosed_gMin V ψ β S z
  have hN : Continuous fun w : (n → ℝ) × (S → ℝ) => w.2 ⬝ᵥ w.2 :=
    continuous_snd.dotProduct continuous_snd
  have hC : ∀ c : ℚ, IsClosed {m : n → ℝ | ∃ r ∈ simplex S,
      (m, r) ∈ gMin V ψ β S z ∩ {w | w.2 ⬝ᵥ w.2 ≤ (c : ℝ)}} := fun c =>
    isClosed_exists_mem (isCompact_simplex S) (hG.inter (isClosed_le hN continuous_const))
  have e : {q : (n → ℝ) × (S → ℝ) | IsPSel V ψ q.1 β S z q.2} =
      gMin V ψ β S z ∩ ⋂ c : ℚ, ({w | w.2 ⬝ᵥ w.2 ≤ (c : ℝ)} ∪
        Prod.fst ⁻¹' {m : n → ℝ | ∃ r ∈ simplex S,
          (m, r) ∈ gMin V ψ β S z ∩ {w | w.2 ⬝ᵥ w.2 ≤ (c : ℝ)}}ᶜ) := by
    ext ⟨m, p⟩
    constructor
    · rintro ⟨hp, hmin⟩
      refine ⟨hp, Set.mem_iInter.2 fun c => ?_⟩
      by_cases hc : p ⬝ᵥ p ≤ c
      · exact Or.inl hc
      · right
        rintro ⟨r, -, hr, hrc⟩
        exact hc ((hmin r hr).trans hrc)
    · rintro ⟨hp, hc⟩
      refine ⟨hp, fun r hr => ?_⟩
      by_contra hlt
      have hlt' : r ⬝ᵥ r < p ⬝ᵥ p := lt_of_not_ge hlt
      obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hlt'
      rcases Set.mem_iInter.1 hc c with h | h
      · exact absurd h (not_le.mpr hc2)
      · exact h ⟨r, hr.1, hr, hc1.le⟩
  rw [e]
  refine hG.measurableSet.inter (MeasurableSet.iInter fun c => ?_)
  exact (isClosed_le hN continuous_const).measurableSet.union
    ((hC c).measurableSet.compl.preimage measurable_fst)

/-- **`p_t^*` is a Borel function of the estimate** (design matrix coercive, `β ≥ 0`,
`S` nonempty). -/
theorem measurable_pSel {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam) (hβ : 0 ≤ β)
    (hS : S.Nonempty) : Measurable fun m => pSel V ψ m β S z := by
  refine measurable_of_graph (measurableSet_isPSel V ψ β S z) fun m p => ⟨fun h => ?_, ?_⟩
  · exact isPSel_unique V ψ β S z hV hlam hβ (isPSel_pSel V ψ β S z m hS) h
  · rintro rfl
    exact isPSel_pSel V ψ β S z m hS

end PSel

/-! ### The sequential choices of Algorithm `alg:cd-joint` -/

section Choices

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*} [Nonempty A]

/-- The optimistic index `φ_yᵀ m + β ‖φ_y‖_{V⁻¹}` of a terminal. -/
noncomputable def optIdx (V : Matrix n n ℝ) (φ : X → n → ℝ) (ι : Z → X) (m : n → ℝ) (β : ℝ)
    (y : Z) : ℝ :=
  φ (ι y) ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι y)))

/-- **`y_t^opt`**: the least-ranked maximiser of the optimistic index. -/
noncomputable def ySel (V : Matrix n n ℝ) (φ : X → n → ℝ) (ι : Z → X) (m : n → ℝ) (β : ℝ) : Z :=
  firstSat (rk Z) (fun y => ∀ y', optIdx V φ ι m β y' ≤ optIdx V φ ι m β y)
    (Classical.arbitrary Z)

/-- **`b_t`**: the least action containing `y` in its support, for a fixed well-order of
the actions (`WellOrderingRel`). -/
noncomputable def bSel (supp : A → Finset Z) (y : Z) : A := by
  classical
  exact if h : ∃ a, y ∈ supp a then
    (WellOrderingRel.isWellOrder (α := A)).wf.min {a | y ∈ supp a} h
    else Classical.arbitrary A

/-- The value `D(z, S) = min_{p ∈ Δ(S)} (g_{z,p}ᵀ m + β ‖g_{z,p}‖_{V⁻¹})`. -/
noncomputable def dVal (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β : ℝ) (S : Finset Z)
    (z : Z) : ℝ :=
  sInf ((fun p => cdObj V ψ m β S z p) '' simplex S)

/-- **`z_t`**: the least-ranked maximiser of `D(·, S)` outside `S`. -/
noncomputable def zSel (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β : ℝ) (S : Finset Z) :
    Z :=
  firstSat (rk Z) (fun z => z ∉ S ∧ ∀ z', z' ∉ S → dVal V ψ m β S z' ≤ dVal V ψ m β S z)
    (Classical.arbitrary Z)

/-- **The safeguarded contrast `g_t`** of `eq:safeguard`, for support `S`, optimistic
terminal `y` and challenger `z`, with the dual contrast built from `pSel`. -/
noncomputable def gSafe (V : Matrix n n ℝ) (m : n → ℝ) (β ε : ℝ) (φ : X → n → ℝ) (ι : Z → X)
    (S : Finset Z) (y z : Z) : n → ℝ :=
  cdSafeguard ε m (cdContrast (fun z => φ (ι z)) S z (pSel V (fun z => φ (ι z)) m β S z))
    (φ (ι z) - φ (ι y))

/-- **`x_{t+1}`**: the least-ranked maximiser of the score of `g` (default `x0`). -/
noncomputable def xSel (V : Matrix n n ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (g : n → ℝ) (x0 : X) :
    X :=
  firstSat (rk X) (fun x => ∀ x', cdScore V φ cost g x' ≤ cdScore V φ cost g x) x0

/-- **One uncertified step of Algorithm `alg:cd-joint`, choices made in order**:
`y = ySel`, `b = bSel y`, `z = zSel (S(b))`, `p = pSel`, `g = gSafe`, `x = xSel g`. -/
noncomputable def seqStep (V : Matrix n n ℝ) (m : n → ℝ) (β ε : ℝ) (φ : X → n → ℝ)
    (cost : X → ℝ) (ι : Z → X) (supp : A → Finset Z) (x0 : X) : X :=
  xSel V φ cost (gSafe V m β ε φ ι (supp (bSel supp (ySel V φ ι m β))) (ySel V φ ι m β)
    (zSel V (fun z => φ (ι z)) m β (supp (bSel supp (ySel V φ ι m β))))) x0

omit [Fintype Z] [Nonempty Z] in
lemma bSel_mem (supp : A → Finset Z) {y : Z} (h : ∃ a, y ∈ supp a) : y ∈ supp (bSel supp y) := by
  classical
  unfold bSel
  rw [dif_pos h]
  exact WellFounded.min_mem _ {a | y ∈ supp a} h

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma dVal_eq {V : Matrix n n ℝ} {ψ : Z → n → ℝ} {m : n → ℝ} {β : ℝ} {S : Finset Z} {z : Z}
    {p : S → ℝ} (hp : IsMinP V ψ m β S z p) : dVal V ψ m β S z = cdObj V ψ m β S z p := by
  unfold dVal
  refine IsLeast.csInf_eq ⟨⟨p, hp.1, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact hp.2 q hq


/-- **The sequential choices are witnesses of `CDStep`.**  If no action passes the stopping
test (supports nonempty and covering, `ε ≥ 0`), then with `y = ySel`, `b = bSel y`,
`z = zSel`, `p = pSel` every clause of `CDStep` holds for the query `seqStep`. -/
theorem seqStep_spec (V : Matrix n n ℝ) (m : n → ℝ) (β ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ)
    (ι : Z → X) (supp : A → Finset Z) (x0 : X) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (hε : 0 ≤ ε)
    (hunc : ∀ a, ¬ cdDualCert V (fun z => φ (ι z)) m β ε (supp a)) :
    let y := ySel V φ ι m β
    let b := bSel supp y
    let z := zSel V (fun z => φ (ι z)) m β (supp b)
    let p := pSel V (fun z => φ (ι z)) m β (supp b) z
    (∀ y', φ (ι y') ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι y'))) ≤
      φ (ι y) ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι y)))) ∧
    y ∈ supp b ∧ z ∉ supp b ∧ p ∈ simplex (supp b) ∧
    (∀ q ∈ simplex (supp b), cdObj V (fun z => φ (ι z)) m β (supp b) z p ≤
      cdObj V (fun z => φ (ι z)) m β (supp b) z q) ∧
    (∀ z', z' ∉ supp b → ∃ q ∈ simplex (supp b),
      cdObj V (fun z => φ (ι z)) m β (supp b) z' q ≤
        cdObj V (fun z => φ (ι z)) m β (supp b) z p) ∧
    ∀ x', cdScore V φ cost
        (cdSafeguard ε m (cdContrast (fun z => φ (ι z)) (supp b) z p)
          (φ (ι z) - φ (ι y))) x' ≤
      cdScore V φ cost
        (cdSafeguard ε m (cdContrast (fun z => φ (ι z)) (supp b) z p)
          (φ (ι z) - φ (ι y))) (seqStep V m β ε φ cost ι supp x0) := by
  intro y b z p
  -- `y_t^opt`
  have hy : ∀ y', optIdx V φ ι m β y' ≤ optIdx V φ ι m β y := by
    obtain ⟨y0, -, hy0⟩ := (univ : Finset Z).exists_max_image (optIdx V φ ι m β) univ_nonempty
    exact firstSat_spec (rk Z) (P := fun y => ∀ y', optIdx V φ ι m β y' ≤ optIdx V φ ι m β y)
      _ ⟨y0, fun y' => hy0 y' (mem_univ _)⟩
  -- `b_t`
  have hb : y ∈ supp b := bSel_mem supp (hcov y)
  -- `z_t`
  have hpr : ((supp b)ᶜ).Nonempty := by
    by_contra hfull
    apply hunc b
    refine ⟨hε, fun z hz => ?_⟩
    exact absurd ⟨z, mem_compl.mpr hz⟩ hfull
  have hz : z ∉ supp b ∧ ∀ z', z' ∉ supp b →
      dVal V (fun z => φ (ι z)) m β (supp b) z' ≤ dVal V (fun z => φ (ι z)) m β (supp b) z := by
    obtain ⟨z0, hz0, hzm⟩ := ((supp b)ᶜ).exists_max_image
      (dVal V (fun z => φ (ι z)) m β (supp b)) hpr
    exact firstSat_spec (rk Z) (P := fun z => z ∉ supp b ∧ ∀ z', z' ∉ supp b →
        dVal V (fun z => φ (ι z)) m β (supp b) z' ≤ dVal V (fun z => φ (ι z)) m β (supp b) z)
      _ ⟨z0, mem_compl.mp hz0, fun z' hz' => hzm z' (mem_compl.mpr hz')⟩
  -- `p_t^*`
  have hp : IsPSel V (fun z => φ (ι z)) m β (supp b) z p := isPSel_pSel _ _ _ _ _ m (hne b)
  -- `x_{t+1}`
  have hx : ∀ x', cdScore V φ cost (gSafe V m β ε φ ι (supp b) y z) x' ≤
      cdScore V φ cost (gSafe V m β ε φ ι (supp b) y z) (seqStep V m β ε φ cost ι supp x0) := by
    obtain ⟨x1, -, hx1⟩ := (univ : Finset X).exists_max_image
      (cdScore V φ cost (gSafe V m β ε φ ι (supp b) y z)) ⟨x0, mem_univ _⟩
    exact firstSat_spec (rk X) (P := fun x => ∀ x', cdScore V φ cost
        (gSafe V m β ε φ ι (supp b) y z) x' ≤ cdScore V φ cost (gSafe V m β ε φ ι (supp b) y z) x)
      _ ⟨x1, fun x' => hx1 x' (mem_univ _)⟩
  refine ⟨hy, hb, hz.1, hp.1.1, hp.1.2, fun z' hz' => ?_, hx⟩
  obtain ⟨q, hq⟩ := exists_isMinP V (fun z => φ (ι z)) β (supp b) z' m (hne b)
  refine ⟨q, hq.1, ?_⟩
  rw [← dVal_eq hq, ← dVal_eq hp.1]
  exact hz.2 z' hz'


/-- The query `seqStep` satisfies `CDStep`. -/
theorem seqStep_cdStep (V : Matrix n n ℝ) (m : n → ℝ) (β ε : ℝ) (φ : X → n → ℝ)
    (cost : X → ℝ) (ι : Z → X) (supp : A → Finset Z) (x0 : X) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (hε : 0 ≤ ε)
    (hunc : ∀ a, ¬ cdDualCert V (fun z => φ (ι z)) m β ε (supp a)) :
    CDStep V m β ε φ cost ι supp (seqStep V m β ε φ cost ι supp x0) :=
  ⟨_, _, _, _, seqStep_spec V m β ε φ cost ι supp x0 hne hcov hε hunc⟩

/-! #### Measurability of each choice in the estimate `m` (design matrix and radius fixed) -/

omit [Fintype X] in
lemma continuous_optIdx (V : Matrix n n ℝ) (φ : X → n → ℝ) (ι : Z → X) (β : ℝ) (y : Z) :
    Continuous fun m => optIdx V φ ι m β y :=
  (continuous_const.dotProduct continuous_id).add continuous_const

omit [Fintype X] in
lemma measurable_ySel_eq (V : Matrix n n ℝ) (φ : X → n → ℝ) (ι : Z → X) (β : ℝ) (y : Z) :
    Measurable fun m => ySel V φ ι m β = y :=
  measurable_firstSat_eq (rk_injective Z) (fun y => Measurable.forall fun y' =>
    measurableSet_setOfPred.1 (measurableSet_le (continuous_optIdx V φ ι β y').measurable
      (continuous_optIdx V φ ι β y).measurable)) _ y

omit [DecidableEq Z] [Nonempty Z] in
lemma continuous_dVal (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (β : ℝ) (S : Finset Z) (z : Z) :
    Continuous fun m => dVal V ψ m β S z :=
  (isCompact_simplex S).continuous_sInf (f := fun m p => cdObj V ψ m β S z p)
    (continuous_cdObj2 V ψ β S z)

lemma measurable_zSel_eq (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (β : ℝ) (S : Finset Z) (z : Z) :
    Measurable fun m => zSel V ψ m β S = z :=
  measurable_firstSat_eq (rk_injective Z) (fun z => measurable_const.and (Measurable.forall
    fun z' => measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_le
      (continuous_dVal V ψ β S z').measurable (continuous_dVal V ψ β S z).measurable)))) _ z


omit [Fintype Z] [Nonempty Z] in
lemma measurable_gSafe (V : Matrix n n ℝ) (β ε : ℝ) (φ : X → n → ℝ) (ι : Z → X) (S : Finset Z)
    (y z : Z) (hpm : Measurable fun m => pSel V (fun z => φ (ι z)) m β S z) :
    Measurable fun m => gSafe V m β ε φ ι S y z := by
  have hG : Measurable fun m =>
      cdContrast (fun z => φ (ι z)) S z (pSel V (fun z => φ (ι z)) m β S z) :=
    (continuous_cdContrast (fun z => φ (ι z)) S z).measurable.comp hpm
  have hdot : Continuous fun q : (n → ℝ) × (n → ℝ) => q.1 ⬝ᵥ q.2 := by
    simp only [dotProduct]
    fun_prop
  have hd : Measurable fun m => cdContrast (fun z => φ (ι z)) S z
      (pSel V (fun z => φ (ι z)) m β S z) ⬝ᵥ m :=
    hdot.measurable.comp (hG.prodMk measurable_id)
  have hset : MeasurableSet {m | cdContrast (fun z => φ (ι z)) S z
      (pSel V (fun z => φ (ι z)) m β S z) ⬝ᵥ m ≤ ε / 2} :=
    measurableSet_le hd measurable_const
  have e : (fun m => gSafe V m β ε φ ι S y z) = fun m =>
      if cdContrast (fun z => φ (ι z)) S z (pSel V (fun z => φ (ι z)) m β S z) ⬝ᵥ m ≤ ε / 2
      then cdContrast (fun z => φ (ι z)) S z (pSel V (fun z => φ (ι z)) m β S z)
      else φ (ι z) - φ (ι y) := rfl
  rw [e]
  exact Measurable.ite hset hG measurable_const

lemma measurable_xSel_eq {α : Type*} [MeasurableSpace α] (V : Matrix n n ℝ) (φ : X → n → ℝ)
    (cost : X → ℝ) {g : α → n → ℝ} (hg : Measurable g) (x0 a : X) :
    Measurable fun ω => xSel V φ cost (g ω) x0 = a :=
  measurable_firstSat_eq (rk_injective X) (fun x => Measurable.forall fun x' =>
    measurableSet_setOfPred.1 (measurableSet_le ((continuous_cdScore V φ cost x').measurable.comp
      hg) ((continuous_cdScore V φ cost x).measurable.comp hg))) x0 a

/-- **The sequential step is a Borel function of the estimate** (design matrix coercive,
radius `β ≥ 0`, supports nonempty). -/
theorem measurable_seqStep_eq {lam : ℝ} (V : Matrix n n ℝ) (hV : Coercive V lam) (hlam : 0 < lam)
    (β ε : ℝ) (hβ : 0 ≤ β) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (x0 a : X) :
    Measurable fun m => seqStep V m β ε φ cost ι supp x0 = a :=
  measurable_dep (f := fun m => ySel V φ ι m β) (measurable_ySel_eq V φ ι β)
    (Q := fun y m => xSel V φ cost (gSafe V m β ε φ ι (supp (bSel supp y)) y
      (zSel V (fun z => φ (ι z)) m β (supp (bSel supp y)))) x0 = a)
    fun y => measurable_dep (f := fun m => zSel V (fun z => φ (ι z)) m β (supp (bSel supp y)))
      (measurable_zSel_eq V _ β _)
      (Q := fun z m => xSel V φ cost (gSafe V m β ε φ ι (supp (bSel supp y)) y z) x0 = a)
      fun z => measurable_xSel_eq V φ cost (measurable_gSafe V β ε φ ι _ y z
        (measurable_pSel V _ β _ z hV hlam hβ (hne _))) x0 a

end Choices

/-! ### The sequential CD policy -/

section Policy

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*} [Nonempty A]

variable (lam σ δ B ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X) (supp : A → Finset Z)
  (θs : n → ℝ) (x0 : X)

/-- **One step of the sequential CD policy.**  Given past queries `xs` and the noise path
`v`, at time `t`: if the stopping test passes (ridge estimate, radius `eq:ay-radius`), query
the default `x0`; otherwise query `seqStep`. -/
noncomputable def seqNext (xs : ℕ → X) (v : ℕ → ℝ) (t : ℕ) : X := by
  classical
  exact if CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t then x0
    else seqStep (design lam φ xs t) (ridgeEst lam φ θs xs v t)
      (ayRadius σ lam δ B (design lam φ xs t)) ε φ cost ι supp x0

/-- **The sequential CD policy**: the query sequence generated by `seqNext`. -/
noncomputable def seqPol (v : ℕ → ℝ) : ℕ → X
  | t => seqNext lam σ δ B ε φ cost ι supp θs x0
      (fun s => if _h : s < t then seqPol v s else x0) v t
termination_by t => t

lemma seqPol_eq (v : ℕ → ℝ) (t : ℕ) :
    seqPol lam σ δ B ε φ cost ι supp θs x0 v t = seqNext lam σ δ B ε φ cost ι supp θs x0
      (fun s => if _h : s < t then seqPol lam σ δ B ε φ cost ι supp θs x0 v s else x0) v t := by
  rw [seqPol]

lemma seqNext_congr_x {xs xs' : ℕ → X} {v : ℕ → ℝ} {t : ℕ} (h : ∀ s < t, xs s = xs' s) :
    seqNext lam σ δ B ε φ cost ι supp θs x0 xs v t =
      seqNext lam σ δ B ε φ cost ι supp θs x0 xs' v t := by
  have h1 := design_congr lam φ t h
  have h2 := ridgeEst_congr2 lam φ θs (η := v) (η' := v) h (fun _ _ => rfl)
  have hc : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t ↔
      CDCertified lam φ ι supp ε xs' (ridgeEst lam φ θs xs' v)
      (fun t => ayRadius σ lam δ B (design lam φ xs' t)) t := by
    simp only [CDCertified, h1, h2]
  unfold seqNext
  by_cases hc' : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t
  · rw [if_pos hc', if_pos (hc.mp hc')]
  · rw [if_neg hc', if_neg (fun h => hc' (hc.mpr h)), h1, h2]

lemma seqNext_congr_v {xs : ℕ → X} {v v' : ℕ → ℝ} {t : ℕ} (h : ∀ s < t, v s = v' s) :
    seqNext lam σ δ B ε φ cost ι supp θs x0 xs v t =
      seqNext lam σ δ B ε φ cost ι supp θs x0 xs v' t := by
  have h2 := ridgeEst_congr2 lam φ θs (x := xs) (x' := xs) (fun _ _ => rfl) h
  have hc : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t ↔
      CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v')
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t := by
    simp only [CDCertified, h2]
  unfold seqNext
  by_cases hc' : CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
      (fun t => ayRadius σ lam δ B (design lam φ xs t)) t
  · rw [if_pos hc', if_pos (hc.mp hc')]
  · rw [if_neg hc', if_neg (fun h => hc' (hc.mpr h)), h2]

/-- **The sequential CD policy is causal**: `seqPol v t` depends on `v` only through
`v 0, …, v (t-1)`. -/
theorem seqPol_causal (t : ℕ) : ∀ v v' : ℕ → ℝ, (∀ s < t, v s = v' s) →
    seqPol lam σ δ B ε φ cost ι supp θs x0 v t = seqPol lam σ δ B ε φ cost ι supp θs x0 v' t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v v' h
    rw [seqPol_eq, seqPol_eq]
    have e : (fun s => if _h : s < t then seqPol lam σ δ B ε φ cost ι supp θs x0 v s else x0) =
        (fun s => if _h : s < t then seqPol lam σ δ B ε φ cost ι supp θs x0 v' s else x0) := by
      funext s
      split_ifs with hs
      · exact ih s hs v v' (fun r hr => h r (hr.trans hs))
      · rfl
    rw [e]
    exact seqNext_congr_v lam σ δ B ε φ cost ι supp θs x0 h

lemma seqPol_eq' (v : ℕ → ℝ) (t : ℕ) :
    seqPol lam σ δ B ε φ cost ι supp θs x0 v t = seqNext lam σ δ B ε φ cost ι supp θs x0
      (seqPol lam σ δ B ε φ cost ι supp θs x0 v) v t := by
  rw [seqPol_eq]
  exact seqNext_congr_x lam σ δ B ε φ cost ι supp θs x0 (fun s hs => by simp only [hs,
    ↓reduceDIte])

/-- **Each uncertified query of the sequential policy is `seqStep`** at the current design,
ridge estimate and radius. -/
theorem seqPol_eq_step (v : ℕ → ℝ) (t : ℕ)
    (hnc : ¬ CDCertified lam φ ι supp ε (seqPol lam σ δ B ε φ cost ι supp θs x0 v)
      (ridgeEst lam φ θs (seqPol lam σ δ B ε φ cost ι supp θs x0 v) v)
      (fun t => ayRadius σ lam δ B (design lam φ (seqPol lam σ δ B ε φ cost ι supp θs x0 v) t))
      t) :
    seqPol lam σ δ B ε φ cost ι supp θs x0 v t =
      seqStep (design lam φ (seqPol lam σ δ B ε φ cost ι supp θs x0 v) t)
        (ridgeEst lam φ θs (seqPol lam σ δ B ε φ cost ι supp θs x0 v) v t)
        (ayRadius σ lam δ B (design lam φ (seqPol lam σ δ B ε φ cost ι supp θs x0 v) t))
        ε φ cost ι supp x0 := by
  rw [seqPol_eq' lam σ δ B ε φ cost ι supp θs x0 v t]
  unfold seqNext
  rw [if_neg hnc]

/-- **The sequential policy runs Algorithm `alg:cd-joint`**: on every noise path, at every
uncertified time, the query satisfies `CDStep` with the witnesses `y = ySel`, `b = bSel y`,
`z = zSel`, `p = pSel` computed from the current design, ridge estimate and radius
(`seqStep_spec`); in particular the queries form a `CDRun`.  (Supports nonempty and
covering, `ε ≥ 0`.) -/
theorem seqPol_run (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    (hε : 0 ≤ ε) (v : ℕ → ℝ) :
    CDRun lam φ cost ι supp ε (seqPol lam σ δ B ε φ cost ι supp θs x0 v)
      (ridgeEst lam φ θs (seqPol lam σ δ B ε φ cost ι supp θs x0 v) v)
      (fun t => ayRadius σ lam δ B
        (design lam φ (seqPol lam σ δ B ε φ cost ι supp θs x0 v) t)) := by
  intro t hnc
  rw [seqPol_eq_step lam σ δ B ε φ cost ι supp θs x0 v t hnc]
  exact seqStep_cdStep _ _ _ ε φ cost ι supp x0 hne hcov hε (fun a ha => hnc ⟨a, ha⟩)

lemma measurable_seqNext_eq (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hB : 0 ≤ B) (hne : ∀ a, (supp a).Nonempty) (xs : ℕ → X) (t : ℕ) (a : X) :
    Measurable fun v => seqNext lam σ δ B ε φ cost ι supp θs x0 xs v t = a := by
  set C : (ℕ → ℝ) → Prop := fun v => CDCertified lam φ ι supp ε xs (ridgeEst lam φ θs xs v)
    (fun t => ayRadius σ lam δ B (design lam φ xs t)) t with hCdef
  have hC : Measurable C :=
    measurable_exists_supp supp (Q := fun S v => cdDualCert (design lam φ xs t)
      (fun z => φ (ι z)) (ridgeEst lam φ θs xs v t) (ayRadius σ lam δ B (design lam φ xs t)) ε S)
      fun S => (measurable_cdDualCert _ _ _ _ S).comp (measurable_ridgeEst lam φ θs xs t)
  have hP : Measurable fun v => seqStep (design lam φ xs t) (ridgeEst lam φ θs xs v t)
      (ayRadius σ lam δ B (design lam φ xs t)) ε φ cost ι supp x0 = a :=
    (measurable_seqStep_eq _ (design_coercive lam φ xs t) hlam _ ε
      (ayRadius_design_pos hσ hlam hδ0 hδ1 hB φ xs t).le φ cost ι supp hne x0 a).comp
      (measurable_ridgeEst lam φ θs xs t)
  have e : (fun v => seqNext lam σ δ B ε φ cost ι supp θs x0 xs v t = a) =
      fun v => (C v ∧ x0 = a) ∨ (¬ C v ∧ seqStep (design lam φ xs t) (ridgeEst lam φ θs xs v t)
        (ayRadius σ lam δ B (design lam φ xs t)) ε φ cost ι supp x0 = a) := by
    funext v
    by_cases hc : C v
    · have : seqNext lam σ δ B ε φ cost ι supp θs x0 xs v t = x0 := by
        unfold seqNext; exact if_pos hc
      rw [this]
      exact propext ⟨fun h => Or.inl ⟨hc, h⟩, fun h => h.elim (fun h => h.2)
        (fun h => absurd hc h.1)⟩
    · have : seqNext lam σ δ B ε φ cost ι supp θs x0 xs v t = seqStep (design lam φ xs t)
          (ridgeEst lam φ θs xs v t) (ayRadius σ lam δ B (design lam φ xs t)) ε φ cost ι supp
          x0 := by
        unfold seqNext; exact if_neg hc
      rw [this]
      exact propext ⟨fun h => Or.inr ⟨hc, h⟩, fun h => h.elim (fun h => absurd h.1 hc)
        (fun h => h.2)⟩
  rw [e]
  exact (hC.and measurable_const).or (hC.not.and hP)

/-- **The queries of the sequential policy are Borel functions of the noise path.** -/
theorem measurableSet_seqPol (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hB : 0 ≤ B) (hne : ∀ a, (supp a).Nonempty) (t : ℕ) : ∀ a : X,
    MeasurableSet {v : ℕ → ℝ | seqPol lam σ δ B ε φ cost ι supp θs x0 v t = a} := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro a
    let ext : (Fin t → X) → ℕ → X := fun h s => if hs : s < t then h ⟨s, hs⟩ else x0
    have e : {v : ℕ → ℝ | seqPol lam σ δ B ε φ cost ι supp θs x0 v t = a} =
        ⋃ h : Fin t → X, ({v | ∀ i : Fin t, seqPol lam σ δ B ε φ cost ι supp θs x0 v i = h i} ∩
          {v | seqNext lam σ δ B ε φ cost ι supp θs x0 (ext h) v t = a}) := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hv
        refine ⟨fun i => seqPol lam σ δ B ε φ cost ι supp θs x0 v i, fun i => rfl, ?_⟩
        rw [← hv, seqPol_eq' lam σ δ B ε φ cost ι supp θs x0 v t]
        exact seqNext_congr_x lam σ δ B ε φ cost ι supp θs x0 (fun s hs => by
          simp only [ext, hs, ↓reduceDIte])
      · rintro ⟨h, hh, hn⟩
        rw [seqPol_eq' lam σ δ B ε φ cost ι supp θs x0 v t, ← hn]
        exact seqNext_congr_x lam σ δ B ε φ cost ι supp θs x0 (fun s hs => by
          simp only [ext, hs, ↓reduceDIte]
          exact hh ⟨s, hs⟩)
    rw [e]
    refine MeasurableSet.iUnion fun h => MeasurableSet.inter ?_
      (measurableSet_setOfPred.2 (measurable_seqNext_eq lam σ δ B ε φ cost ι supp θs x0
        hσ hlam hδ0 hδ1 hB hne _ t a))
    exact measurableSet_setOfPred.2 (Measurable.forall fun i =>
      measurableSet_setOfPred.1 (ih i i.2 (h i)))

end Policy

/-! ### `thm:t4-finite-sample` with the sequential policy -/

section Main

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*} [Nonempty A]

/-- The queries of the sequential CD policy (`seqPol`, default query `ι z₀` for a fixed
terminal `z₀`) on the noise space `ℕ → ℝ`. -/
noncomputable def gQ3 (lam σ δ B ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (θs : n → ℝ) : ℕ → (ℕ → ℝ) → X :=
  fun t v => seqPol lam σ δ B ε φ cost ι supp θs (ι (Classical.arbitrary Z)) v t

omit [DecidableEq X] in
/-- **Every uncertified query of `gQ3` is the sequential step** `seqStep` (choices `ySel`,
`bSel`, `zSel`, `pSel`, `gSafe`, `xSel` at the current design, ridge estimate and radius),
and these choices witness `CDStep` (`seqStep_spec`). -/
theorem gQ3_eq_step (lam σ δ B ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (θs : n → ℝ) (ω : ℕ → ℝ) (t : ℕ)
    (hnc : ¬ CDCertified lam φ ι supp ε (fun s => gQ3 lam σ δ B ε φ cost ι supp θs s ω)
      (fun t => gEst lam φ θs (gQ3 lam σ δ B ε φ cost ι supp θs) t ω)
      (fun t => gRad σ lam δ B φ (gQ3 lam σ δ B ε φ cost ι supp θs) t ω) t) :
    gQ3 lam σ δ B ε φ cost ι supp θs t ω =
      seqStep (design lam φ (fun s => gQ3 lam σ δ B ε φ cost ι supp θs s ω) t)
        (gEst lam φ θs (gQ3 lam σ δ B ε φ cost ι supp θs) t ω)
        (gRad σ lam δ B φ (gQ3 lam σ δ B ε φ cost ι supp θs) t ω)
        ε φ cost ι supp (ι (Classical.arbitrary Z)) :=
  seqPol_eq_step lam σ δ B ε φ cost ι supp θs _ ω t hnc

omit [DecidableEq X] in
/-- **The hypotheses of `cd_joint_literal` hold for the sequential policy with continuous
noise** (as `LiteralG1.subG_hyps`, for `gQ3`). -/
theorem subG_hyps_seq (ν : Measure ℝ) [IsProbabilityMeasure ν] {σ : ℝ} (hσ : 0 < σ)
    (hν : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)))
    {lam δ B : ℝ} (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε : 0 ≤ ε) (θs : n → ℝ) :
    (∀ s, Measurable[nFilt (s + 1)] (fun ω : ℕ → ℝ => ω s)) ∧
    (∀ s, CondSubG (noiseP ν) (nFilt s) (fun ω : ℕ → ℝ => ω s) σ) ∧
    (∀ s x0, MeasurableSet[nFilt s] {ω | gQ3 lam σ δ B ε φ cost ι supp θs s ω = x0}) ∧
    ∀ ω, CDRun lam φ cost ι supp ε (fun s => gQ3 lam σ δ B ε φ cost ι supp θs s ω)
      (ridgeEst lam φ θs (fun s => gQ3 lam σ δ B ε φ cost ι supp θs s ω) (fun s => ω s))
      (fun t => ayRadius σ lam δ B (design lam φ
        (fun s => gQ3 lam σ δ B ε φ cost ι supp θs s ω) t)) := by
  refine ⟨noise_adapted, noise_condSubG ν hν, fun s x0 => ?_, fun ω => ?_⟩
  · exact measurableSet_nFilt_of_causal
      (measurableSet_seqPol lam σ δ B ε φ cost ι supp θs _ hσ hlam hδ0 hδ1 hB hne s x0)
      (fun v v' h hv => (seqPol_causal lam σ δ B ε φ cost ι supp θs _ s v v' h).symm.trans hv)
  · exact seqPol_run lam σ δ B ε φ cost ι supp θs _ hne hcov hε ω

/-- **`t4_finite_sample` with continuous sub-Gaussian noise, sequential choices.**  As
`LiteralG1.t4_finite_sample_subG`, with the policy `gQ3` whose every uncertified step makes
the choices of Algorithm `alg:cd-joint` one after another (`gQ3_eq_step`, `seqStep_spec`):
on `ℕ → ℝ` with i.i.d. noise of a law `ν` with `σ`-sub-Gaussian moment generating function
(`σ > 0`), for every fixed-feature instance whose supports cover the terminals,
`‖θ*‖ ≤ B`, `0 < δ < 1`: `gQ3` is adapted, every hypothesis of
`LiteralF1.t4_finite_sample` holds with the ridge estimate `gEst` and the radius `gRad`
(`eq:ay-radius`), and hence its conclusion. -/
theorem t4_finite_sample_subG_seq [Nonempty n] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {σ : ℝ} (hσ : 0 < σ) (hν : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂ν ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * σ ^ 2 / 2)))
    {lam δ B : ℝ} (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) :
    let x := gQ3 lam σ δ B ε φ cost ι supp θs
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
  obtain ⟨hη, hsub, hx, hrun⟩ :=
    subG_hyps_seq ν hσ hν hlam hδ0 hδ1 hB φ cost ι supp hne hcov hε.le θs
  obtain ⟨hpos, hmono, hcovP, -⟩ := ayRadius_generic_hyps (μ := noiseP ν) (ε := ε) (cmin := 1)
    nFilt hσ hlam hδ0 hδ1 hB φ hcmax one_pos hLsq hφ θs hθ x hx hη hsub
  have hlim : ∀ ω, Filter.liminf
      (fun t : ℕ => ((gRad σ lam δ B φ x t ω ^ 2 * Real.log t / t : ℝ) : EReal)) atTop = 0 :=
    fun ω => ayRadius_liminf (σ := σ) hlam hδ0 hδ1 φ hφ (fun s => x s ω)
  exact ⟨hx, hpos, hmono, hcovP, hlim, hrun,
    t4_finite_sample (μ := noiseP ν) hlam φ cost hcost hφ hε ι supp hne θs x
      (gEst lam φ θs x) (gRad σ lam δ B φ x) hpos hmono hcovP hlim hrun⟩

/-- **`t4_finite_sample` with i.i.d. standard Gaussian noise, sequential choices.**  The
case `ν = N(0, 1)`, `σ = 1`, of `t4_finite_sample_subG_seq`. -/
theorem t4_finite_sample_gaussian_seq [Nonempty n] {lam δ B : ℝ} (hlam : 0 < lam)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) :
    let x := gQ3 lam 1 δ B ε φ cost ι supp θs
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
  t4_finite_sample_subG_seq (gaussianReal 0 1) one_pos gaussian_mgf hlam hδ0 hδ1 hB φ cost
    hcost hφ hε ι supp hne hcov θs hθ

end Main

end LiteralG3

end JointRootCert
