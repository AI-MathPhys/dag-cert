/-
# The finite-grid allocation oracle for the finite-confidence procedure

Manuscript results covered (`app:bay-finite`): `thm:v10g-expectation`, `prop:bay-finite`,
`cor:v10g-target`, `thm:v10g-discovery`, with the oracle of `eq:v10g-oracle` built as the
manuscript says ("the finite oracle constructions of Section `app:known-gauss-info` apply
because the floor is strictly positive"; "solving all remaining actions to the stated accuracy
and selecting the largest returned lower endpoint").

`LiteralD1a` proves these results with an oracle obtained from a countable dense sequence of
designs.  Here the oracle is the finite grid of `LiteralD1b`: at stage `j` and center `v` it
takes the grid of step `1/N` of the simplex, mixes every grid point with `k w⁰`, evaluates
`I_a(v, ·)` at every pair (action, floored grid point), and returns a pair of largest value,
the first in a fixed enumeration (`gridOracle`).  With
`N = ⌈2 |X| ℓ² C_R(v) / (k k₀ e_j²)⌉`, `C_R(v) = ℓ² (‖v‖ + A)² / 2` (`A` bounds one anchor
in every alternative set), the oracle meets `eq:v10g-oracle` with upper endpoint
`l + e_j²`, and its outputs are Borel functions of the center (`gridOracle_contract`,
`gridOracle_measurable`).  The final theorems are stated for this one explicit procedure
(`gridProc`), on the tape space `tapeP`, with no oracle existential.

Remaining difference from the manuscript: the values at the grid points are the exact
infima `I_a(v, w)` (an interval of width zero), not the output of a computed quadratic
solver on rational data; the manuscript's representation-error convention is not formalized.
-/
import JointRootCert.LiteralD1a
import JointRootCert.LiteralD1b

namespace JointRootCert

namespace LiteralD1c

open Finset MeasureTheory ProbabilityTheory LiteralD1 LiteralD1b
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

section GridOracle

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜]

/-- On the floor `W_k = (1 - k) Δ + k w⁰`, every floored design is within `ξ / 2` in
information of a floored grid point, once `N ≥ 2 |X| ℓ² C_R / (k κ ξ)`
(`app:known-gauss-info`: covering radius `|X| / N` and the `ℓ¹`-Lipschitz bound
`ℓ² C_R / (k κ)` on the floor). -/
lemma floor_grid_near (u : X → E) {ℓ : ℝ} (hu : ∀ x, ‖u x‖ ≤ ℓ) {Q : Set E} (hQ : Q.Nonempty)
    (v : E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {κ : ℝ} (hκ : 0 < κ)
    (hM0 : ∀ z, κ * ‖z‖ ^ 2 ≤ ‖designMap u w0 z‖ ^ 2) {k ξ CR : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hξ : 0 < ξ) (hCR : ∀ w ∈ simplex X, gInfo u Q v w ≤ CR) {N : ℕ} (hN0 : 0 < N)
    (hN : 2 * (Fintype.card X : ℝ) * ℓ ^ 2 * CR / (k * κ * ξ) ≤ N) {p : X → ℝ}
    (hp : p ∈ simplex X) :
    ∃ c ∈ gridPts X N, gInfo u Q v (floorDesign k w0 p) ≤
      gInfo u Q v (floorDesign k w0 (gridDesign N c)) + ξ / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨c, hc, hcov⟩ := grid_cover hN0 hp
  refine ⟨c, hc, ?_⟩
  have hcm : floorDesign k w0 (gridDesign N c) ∈ simplex X :=
    floorDesign_mem hk0.le hk1 hw0 (gridDesign_mem hN0 hc)
  have hwm : floorDesign k w0 p ∈ simplex X := floorDesign_mem hk0.le hk1 hw0 hp
  have hCR0 : 0 ≤ CR := gInfo_nonneg.trans (hCR _ hcm)
  have hB := info_l1_lipschitz u hu hQ v (w := floorDesign k w0 (gridDesign N c))
    (w' := floorDesign k w0 p) hcm.1 hwm.1 (mul_pos hk0 hκ)
    (floor_gram_lower u hw0.1 (gridDesign_nonneg N c) hk0.le hk1 hM0) (hCR _ hcm)
  have hdist : ∑ x, |floorDesign k w0 p x - floorDesign k w0 (gridDesign N c) x| ≤
      (Fintype.card X : ℝ) / N := by
    refine le_trans (sum_le_sum fun x _ => ?_) hcov
    have e1 : floorDesign k w0 p x - floorDesign k w0 (gridDesign N c) x =
        (1 - k) * (p x - gridDesign N c x) := by
      simp only [floorDesign]
      ring
    rw [e1, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - k), abs_sub_comm]
    have : (1 - k) * |gridDesign N c x - p x| ≤ 1 * |gridDesign N c x - p x| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have hcoef : 0 ≤ ℓ ^ 2 * CR / (k * κ) := by
    have : 0 < k * κ := mul_pos hk0 hκ
    positivity
  have hsmall : ℓ ^ 2 * CR / (k * κ) * ((Fintype.card X : ℝ) / N) ≤ ξ / 2 := by
    have hkκξ : 0 < k * κ * ξ := by positivity
    rw [div_le_iff₀ hkκξ] at hN
    have e : ℓ ^ 2 * CR / (k * κ) * ((Fintype.card X : ℝ) / N) =
        (Fintype.card X : ℝ) * ℓ ^ 2 * CR / (k * κ * N) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have := mul_le_mul_of_nonneg_left hdist hcoef
  linarith

/-- `C_R = ℓ² (R + A)² / 2` at the radius `R = ‖v‖`. -/
def cR (ℓ A0 : ℝ) (v : E) : ℝ := ℓ ^ 2 * (‖v‖ + A0) ^ 2 / 2

/-- The grid size at stage `j` and center `v`:
`N = max 1 ⌈2 |X| ℓ² C_R(v) / (k κ e_j²)⌉`. -/
def gN (X : Type*) [Fintype X] (ℓ κ A0 k : ℝ) (e : ℕ → ℝ) (j : ℕ) (v : E) : ℕ :=
  max 1 ⌈2 * (Fintype.card X : ℝ) * ℓ ^ 2 * cR ℓ A0 v / (k * κ * e j ^ 2)⌉₊

omit [DecidableEq X] [Nonempty X] [InnerProductSpace ℝ E] in
lemma gN_pos (ℓ κ A0 k : ℝ) (e : ℕ → ℝ) (j : ℕ) (v : E) : 0 < gN X ℓ κ A0 k e j v :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- A fixed enumeration of the pairs (action, grid count vector), used to break ties. -/
def pEnum (𝒜 X : Type*) [Fintype 𝒜] [Nonempty 𝒜] [Fintype X] : ℕ → 𝒜 × (X → ℕ) :=
  Classical.choose (exists_surjective_nat (𝒜 × (X → ℕ)))

omit [DecidableEq X] [Nonempty X] [DecidableEq 𝒜] in
lemma pEnum_surjective : Function.Surjective (pEnum 𝒜 X) :=
  Classical.choose_spec (exists_surjective_nat (𝒜 × (X → ℕ)))

/-- The finite set of pairs (action, grid point of step `1/N`). -/
def gridPairs (𝒜 X : Type*) [Fintype 𝒜] [Fintype X] [DecidableEq X] (N : ℕ) :
    Finset (𝒜 × (X → ℕ)) :=
  (univ : Finset 𝒜) ×ˢ gridPts X N

omit [DecidableEq 𝒜] in
lemma exists_pair_argmax (f : 𝒜 × (X → ℕ) → ℝ) (N : ℕ) :
    ∃ i, pEnum 𝒜 X i ∈ gridPairs 𝒜 X N ∧
      ∀ q ∈ gridPairs 𝒜 X N, f q ≤ f (pEnum 𝒜 X i) := by
  obtain ⟨q0, hq0, hmax⟩ := Finset.exists_max_image (gridPairs 𝒜 X N) f
    (univ_nonempty.product (gridPts_nonempty N))
  obtain ⟨i, hi⟩ := pEnum_surjective (𝒜 := 𝒜) (X := X) q0
  exact ⟨i, by rw [hi]; exact hq0, fun q hq => by rw [hi]; exact hmax q hq⟩

/-- The information of action `q.1` at the floored grid point `(1 - k) q.2 / N + k w⁰`. -/
def pval (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k : ℝ) (N : ℕ) (q : 𝒜 × (X → ℕ))
    (v : E) : ℝ :=
  gInfo u (Q q.1) v (floorDesign k w0 (gridDesign N q.2))

/-- Index (in the fixed enumeration) of the first pair of largest value on the grid. -/
def gIdx (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ) (e : ℕ → ℝ) (j : ℕ)
    (v : E) : ℕ :=
  Nat.find (exists_pair_argmax (fun q => pval u Q w0 k (gN X ℓ κ A0 k e j v) q v)
    (gN X ℓ κ A0 k e j v))

lemma gIdx_spec (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ) (e : ℕ → ℝ) (j : ℕ)
    (v : E) :
    pEnum 𝒜 X (gIdx u Q w0 k ℓ κ A0 e j v) ∈ gridPairs 𝒜 X (gN X ℓ κ A0 k e j v) ∧
      ∀ q ∈ gridPairs 𝒜 X (gN X ℓ κ A0 k e j v),
        pval u Q w0 k (gN X ℓ κ A0 k e j v) q v ≤
          pval u Q w0 k (gN X ℓ κ A0 k e j v) (pEnum 𝒜 X (gIdx u Q w0 k ℓ κ A0 e j v)) v :=
  Nat.find_spec (exists_pair_argmax (fun q => pval u Q w0 k (gN X ℓ κ A0 k e j v) q v)
    (gN X ℓ κ A0 k e j v))

/-- **The finite-grid oracle** for `eq:v10g-oracle`: action, design and lower endpoint at
stage `j` and center `v`. -/
def gridOa (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ) (e : ℕ → ℝ) :
    ℕ → E → 𝒜 :=
  fun j v => (pEnum 𝒜 X (gIdx u Q w0 k ℓ κ A0 e j v)).1

/-- The design returned by the finite-grid oracle (a floored grid point). -/
def gridOw (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ) (e : ℕ → ℝ) :
    ℕ → E → X → ℝ :=
  fun j v => floorDesign k w0 (gridDesign (gN X ℓ κ A0 k e j v)
    (pEnum 𝒜 X (gIdx u Q w0 k ℓ κ A0 e j v)).2)

/-- The lower endpoint returned by the finite-grid oracle (the largest grid value). -/
def gridOl (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ) (e : ℕ → ℝ) :
    ℕ → E → ℝ :=
  fun j v => pval u Q w0 k (gN X ℓ κ A0 k e j v) (pEnum 𝒜 X (gIdx u Q w0 k ℓ κ A0 e j v)) v

/-- The upper endpoint `l + e_j²`. -/
def gridOu (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ) (e : ℕ → ℝ) :
    ℕ → E → ℝ :=
  fun j v => gridOl u Q w0 k ℓ κ A0 e j v + e j ^ 2

/-- **The finite-grid oracle meets `eq:v10g-oracle`.**  Hypotheses: `‖u_x‖ ≤ ℓ`,
`M(w⁰) ⪰ κ I` with `κ > 0`, floor `k ∈ (0, 1]`, positive tolerances, and an anchor of norm
at most `A0` in every alternative set. -/
theorem gridOracle_contract (u : X → E) (Q : 𝒜 → Set E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X)
    {k ℓ κ A0 : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ)
    (hκ : 0 < κ) (hM0 : ∀ z, κ * ‖z‖ ^ 2 ≤ ‖designMap u w0 z‖ ^ 2)
    (hA : ∀ a, ∃ lam ∈ Q a, ‖lam‖ ≤ A0) {e : ℕ → ℝ} (he : ∀ j, 0 < e j) :
    OracleContract u Q w0 k e (gridOa u Q w0 k ℓ κ A0 e) (gridOw u Q w0 k ℓ κ A0 e)
      (gridOl u Q w0 k ℓ κ A0 e) (gridOu u Q w0 k ℓ κ A0 e) where
  design_mem j v := ⟨_, gridDesign_mem (gN_pos ℓ κ A0 k e j v)
    (Finset.mem_product.mp (gIdx_spec u Q w0 k ℓ κ A0 e j v).1).2, rfl⟩
  lo_nonneg j v := gInfo_nonneg
  lo_le j v := le_rfl
  le_hi j v a p hp := by
    obtain ⟨lam0, h0, hA0⟩ := hA a
    have hCR : ∀ w ∈ simplex X, gInfo u (Q a) v w ≤ cR ℓ A0 v := fun w hw =>
      info_le_anchor u hw hℓ.le hu h0 hA0 le_rfl
    have hN : 2 * (Fintype.card X : ℝ) * ℓ ^ 2 * cR ℓ A0 v / (k * κ * e j ^ 2) ≤
        (gN X ℓ κ A0 k e j v : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
    obtain ⟨c, hc, hnear⟩ := floor_grid_near u hu ⟨lam0, h0⟩ v hw0 hκ hM0 hk0 hk1
      (pow_pos (he j) 2) hCR (gN_pos ℓ κ A0 k e j v) hN hp
    have hmax := (gIdx_spec u Q w0 k ℓ κ A0 e j v).2 (a, c)
      (Finset.mem_product.mpr ⟨mem_univ a, hc⟩)
    have h2 : 0 ≤ e j ^ 2 := sq_nonneg _
    show gInfo u (Q a) v (floorDesign k w0 p) ≤ gridOl u Q w0 k ℓ κ A0 e j v + e j ^ 2
    have h3 : pval u Q w0 k (gN X ℓ κ A0 k e j v) (a, c) v =
        gInfo u (Q a) v (floorDesign k w0 (gridDesign (gN X ℓ κ A0 k e j v) c)) := rfl
    have h4 : gridOl u Q w0 k ℓ κ A0 e j v = pval u Q w0 k (gN X ℓ κ A0 k e j v)
        (pEnum 𝒜 X (gIdx u Q w0 k ℓ κ A0 e j v)) v := rfl
    linarith
  gap j v := (add_sub_cancel_left _ _).le

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq X] [Nonempty X] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma measurable_gN (ℓ κ A0 k : ℝ) (e : ℕ → ℝ) (j : ℕ) :
    Measurable (fun v : E => gN X ℓ κ A0 k e j v) := by
  have h2 : Measurable (fun v : E => cR ℓ A0 v) := by
    unfold cR
    exact ((((continuous_norm.add continuous_const).pow 2).const_mul _).div_const 2).measurable
  unfold gN
  exact measurable_const.max (Nat.measurable_ceil.comp ((h2.const_mul _).div_const _))

omit [DecidableEq X] [Nonempty X] [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜] in
lemma measurable_pval (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k : ℝ) (N : ℕ)
    (q : 𝒜 × (X → ℕ)) : Measurable (fun v : E => pval u Q w0 k N q v) :=
  measurable_gInfo_center u (Q q.1) _

lemma measurable_gIdx (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ) (e : ℕ → ℝ)
    (j : ℕ) : Measurable (fun v : E => gIdx u Q w0 k ℓ κ A0 e j v) := by
  unfold gIdx
  refine measurable_find _ fun i => ?_
  have hset : {v : E | pEnum 𝒜 X i ∈ gridPairs 𝒜 X (gN X ℓ κ A0 k e j v) ∧
      ∀ q ∈ gridPairs 𝒜 X (gN X ℓ κ A0 k e j v),
        pval u Q w0 k (gN X ℓ κ A0 k e j v) q v ≤
          pval u Q w0 k (gN X ℓ κ A0 k e j v) (pEnum 𝒜 X i) v} =
      ⋃ n : ℕ, ((fun v : E => gN X ℓ κ A0 k e j v) ⁻¹' {n}) ∩
        {v : E | pEnum 𝒜 X i ∈ gridPairs 𝒜 X n ∧ ∀ q ∈ gridPairs 𝒜 X n,
          pval u Q w0 k n q v ≤ pval u Q w0 k n (pEnum 𝒜 X i) v} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨n, rfl, h⟩
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun n =>
    (measurable_gN ℓ κ A0 k e j (measurableSet_singleton n)).inter ?_
  by_cases hmem : pEnum 𝒜 X i ∈ gridPairs 𝒜 X n
  · have : {v : E | pEnum 𝒜 X i ∈ gridPairs 𝒜 X n ∧ ∀ q ∈ gridPairs 𝒜 X n,
        pval u Q w0 k n q v ≤ pval u Q w0 k n (pEnum 𝒜 X i) v} =
        ⋂ q ∈ gridPairs 𝒜 X n, {v : E |
          pval u Q w0 k n q v ≤ pval u Q w0 k n (pEnum 𝒜 X i) v} := by
      ext v
      simp [hmem]
    rw [this]
    exact Finset.measurableSet_biInter _ fun q _ =>
      measurableSet_le (measurable_pval u Q w0 k n q) (measurable_pval u Q w0 k n _)
  · have : {v : E | pEnum 𝒜 X i ∈ gridPairs 𝒜 X n ∧ ∀ q ∈ gridPairs 𝒜 X n,
        pval u Q w0 k n q v ≤ pval u Q w0 k n (pEnum 𝒜 X i) v} = ∅ := by
      ext v
      simp [hmem]
    rw [this]
    exact MeasurableSet.empty

/-- **The finite-grid oracle has Borel outputs**: its lower endpoint and every coordinate of
its design are Borel functions of the center. -/
theorem gridOracle_measurable (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ κ A0 : ℝ)
    (e : ℕ → ℝ) :
    (∀ j, Measurable (gridOl u Q w0 k ℓ κ A0 e j)) ∧
      ∀ j x, Measurable (fun v => gridOw u Q w0 k ℓ κ A0 e j v x) := by
  have hpair : ∀ j, Measurable (fun v : E =>
      ((gN X ℓ κ A0 k e j v, gIdx u Q w0 k ℓ κ A0 e j v) : ℕ × ℕ)) := fun j =>
    (measurable_gN ℓ κ A0 k e j).prodMk (measurable_gIdx u Q w0 k ℓ κ A0 e j)
  refine ⟨fun j => ?_, fun j x => ?_⟩
  · have h : Measurable fun p : E × (ℕ × ℕ) => pval u Q w0 k p.2.1 (pEnum 𝒜 X p.2.2) p.1 :=
      measurable_from_prod_countable_left fun q => measurable_pval u Q w0 k q.1 (pEnum 𝒜 X q.2)
    exact Measurable.comp (g := fun p : E × (ℕ × ℕ) => pval u Q w0 k p.2.1 (pEnum 𝒜 X p.2.2) p.1)
      (f := fun v : E => (v, ((gN X ℓ κ A0 k e j v, gIdx u Q w0 k ℓ κ A0 e j v) : ℕ × ℕ)))
      h (measurable_id.prodMk (hpair j))
  · exact Measurable.comp (g := fun q : ℕ × ℕ =>
        floorDesign k w0 (gridDesign q.1 (pEnum 𝒜 X q.2).2) x)
      (f := fun v : E => ((gN X ℓ κ A0 k e j v, gIdx u Q w0 k ℓ κ A0 e j v) : ℕ × ℕ))
      Measurable.of_discrete (hpair j)

/-- **The procedure with the finite-grid oracle**: `exactProc` (exact enclosures
`Z̲_n = Z_n`, `B̄_n = B(n, δ/2)`, exact safeguard distances) with the oracle `gridOracle`
built for the reference constant `k₀`, the feature bound `ℓ` and the anchor bound `A0`. -/
def gridProc (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k ℓ k0 A0 : ℝ) (e : ℕ → ℝ) (δ : ℝ) :
    FCProc X E 𝒜 :=
  exactProc u Q w0 k e (gridOa u Q w0 k ℓ k0 A0 e) (gridOw u Q w0 k ℓ k0 A0 e)
    (gridOl u Q w0 k ℓ k0 A0 e) δ

lemma gridProc_spec (u : X → E) (Q : 𝒜 → Set E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X)
    {k ℓ k0 A0 α δ : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ)
    (hκ : 0 < k0) (hM0 : ∀ z, k0 * ‖z‖ ^ 2 ≤ ‖designMap u w0 z‖ ^ 2)
    (hA : ∀ a, ∃ lam ∈ Q a, ‖lam‖ ≤ A0) (hα0 : 0 < α) (hα1 : α ≤ 1) {e : ℕ → ℝ}
    (he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j) :
    (gridProc u Q w0 k ℓ k0 A0 e δ).Spec Q ℓ k0 α δ :=
  exactProc_spec u Q hw0 hκ hM0 he1 he2
    (gridOracle_contract u Q hw0 hk0 hk1 hℓ hu hκ hM0 hA (tol_pos hℓ hκ hα0 hα1 he1))
    (gridOracle_measurable u Q w0 k ℓ k0 A0 e).1 (gridOracle_measurable u Q w0 k ℓ k0 A0 e).2

end GridOracle

/-! ### The results for the procedure with the finite-grid oracle -/

section Final

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **Correlated finite-confidence discovery and confirmation** (`thm:v10g-expectation`) for
the explicit procedure `gridProc` (finite-grid oracle), on the tape space.

Model: finitely many queries with features `u_x`, `‖u_x‖ ≤ ℓ`; a reference design `w⁰` with
`M(w⁰) ⪰ k₀ I`; finitely many root actions with nonempty supports, each with a strict
`ε`-invalidating alternative of norm at most `A0` (the remaining branch after the hull
screen).  For every `δ, α ∈ (0, 1]` and tolerances in the manuscript's range: the procedure
meets `Spec`; it is `(ε, δ)`-safe at every parameter; and at every `θ` with `I_*(θ) > 0`,
`E_θ τ ≤ min {𝓑_δ, H_δ / k + 1}` with `C = I_*(θ)`, `C₀ = max_a I_a(θ, w⁰)`. -/
theorem grid_v10g_expectation (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) {A0 : ℝ}
    (hA : ∀ a, ∃ lam ∈ strictAlt φ (supp a) (hne a) ε, ‖lam‖ ≤ A0) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {ℓ k0 k : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k < 1) :
    ∀ (δ α : ℝ) (e : ℕ → ℝ), 0 < δ → δ ≤ 1 → 0 < α → α ≤ 1 →
      (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j) →
      (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j) →
      (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).Spec
          (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 α δ ∧
      (∀ θ : E, tapeP X {ω |
          (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).tauΩ θ ω < ⊤ ∧
          ∃ a, (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).retΩ θ ω =
            some a ∧ ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal δ) ∧
      ∀ θ : E, 0 < IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
        ∫⁻ ω, (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ).tauΩ θ ω
            ∂(tapeP X) ≤
          ENNReal.ofReal (min
            (Bdelta
              (Dbar (pilotA ℓ k0 k (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ))
                (Module.finrank ℝ E) α (Fintype.card X))
              (logBudget (aC (Module.finrank ℝ E) k
                  (cstar k * IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) δ α)
                (bC k (cstar k * IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)))
              (Fintype.card X) k α
              (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ
                (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)))
            (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ
              (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0) / k + 1)) := by
  intro δ α e hδ0 hδ1 hα0 hα1 he1 he2
  have hQ : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty := fun a =>
    let ⟨lam, hlam, _⟩ := hA a; ⟨lam, hlam⟩
  have hS := gridProc_spec u (fun a => strictAlt φ (supp a) (hne a) ε) hw0 (δ := δ) hk hk1.le
    hℓ hu hk0 hM0 hA hα0 hα1 he1 he2
  refine ⟨hS, fun θ => ?_, fun θ hI => ?_⟩
  · exact FCProc.safe_tape
      (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ)
      φ supp hne ε hw0 hk0 hM0 hk hk1.le hS θ hδ0 hδ1
  · exact FCProc.expectation_tape
      (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k ℓ k0 A0 e δ) (fun a => strictAlt φ (supp a) (hne a) ε) hQ hw0 hℓ hu hk0
      hM0 hk hk1 hα0 hα1 hδ0 hδ1 hS θ hI

/-- **`prop:bay-finite` and `cor:v10g-target`** for the explicit procedure `gridProc`
(finite-grid oracle), `k = s / 16`, pilot risk `α = 1 / (8 J²)`, on the tape space.

(1) For every `δ ∈ (0, 1]`, `J ≥ 1` and tolerances in the manuscript's range, the procedure
meets `Spec` and is `(ε, δ)`-safe at every parameter.
(2) At every `θ` with `I_*(θ) > 0` there is `K` (depending on the instance and `s`, not on
`δ`) such that for all `δ ∈ (0, 1/4]` and `1 + log(1/δ) ≤ J < 3 + log(1/δ)`:
`E_θ τ ≤ D + (1 + s) I_*(θ)⁻¹ log(1/δ) + R₁₀` and `R₁₀ ≤ K (1 + log log(1/δ))`, where
`D = (D₀ + q) / (1 - k)` does not involve `δ`. -/
theorem grid_bay_finite (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) {A0 : ℝ}
    (hA : ∀ a, ∃ lam ∈ strictAlt φ (supp a) (hne a) ε, ‖lam‖ ≤ A0) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {ℓ k0 s : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∀ (δ J : ℝ) (e : ℕ → ℝ), 0 < δ → δ ≤ 1 → 1 ≤ J →
      (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j / Real.sqrt 2 ≤ e j) →
      (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j) →
      (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e δ).Spec
          (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 (1 / (8 * J ^ 2)) δ ∧
      ∀ θ : E, tapeP X {ω |
          (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e δ).tauΩ
            θ ω < ⊤ ∧
          ∃ a, (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e
            δ).retΩ θ ω = some a ∧ ε < regret (supp a) (hne a) (env φ θ)} ≤
        ENNReal.ofReal δ) ∧
    ∀ θ : E, 0 < IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
      ∃ K : ℝ, ∀ (δ J : ℝ) (e : ℕ → ℝ), 0 < δ → δ ≤ 1 / 4 → 1 + Real.log (1 / δ) ≤ J →
        J < 3 + Real.log (1 / δ) →
        (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j / Real.sqrt 2 ≤ e j) →
        (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j) →
        ∫⁻ ω, (gridProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) ℓ k0 A0 e
            δ).tauΩ θ ω ∂(tapeP X) ≤
          ENNReal.ofReal
            (Dconst ℓ k0 s (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                (Module.finrank ℝ E) (Fintype.card X) +
              (1 + s) * (1 / IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) *
                Real.log (1 / δ) +
              Rrem ℓ k0 s (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)
                (Module.finrank ℝ E) (Fintype.card X) δ J) ∧
        Rrem ℓ k0 s (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
            (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)
            (Module.finrank ℝ E) (Fintype.card X) δ J ≤
          K * (1 + Real.log (Real.log (1 / δ))) := by
  have hk : 0 < s / 16 := by positivity
  have hk1 : s / 16 < 1 := by linarith
  have hQ : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty := fun a =>
    let ⟨lam, hlam, _⟩ := hA a; ⟨lam, hlam⟩
  have hmain := grid_v10g_expectation φ supp hne ε hA u hw0 hℓ hu hk0 hM0 hk hk1
  have hα : ∀ J : ℝ, 1 ≤ J → 0 < 1 / (8 * J ^ 2) ∧ 1 / (8 * J ^ 2) ≤ 1 := by
    intro J hJ
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    nlinarith
  refine ⟨fun δ J e hδ0 hδ1 hJ he1 he2 => ?_, fun θ hI => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hmain δ (1 / (8 * J ^ 2)) e hδ0 hδ1 (hα J hJ).1 (hα J hJ).2 he1 he2
    exact ⟨h1, h2⟩
  · have hC0 : 0 < C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0 :=
      lt_of_lt_of_le (by positivity) (C0G_ge u _ hQ θ hw0 hℓ hu hk0.le hM0)
    have hA' : 0 ≤ pilotA ℓ k0 (s / 16)
        (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) := by
      have : 0 < 1 - s / 16 := by linarith
      unfold pilotA
      positivity
    have hcs : 0 < cstar (s / 16) := by
      have : 0 < 1 - s / 16 := by linarith
      unfold cstar
      positivity
    obtain ⟨K, hK⟩ := R10_order (A := pilotA ℓ k0 (s / 16)
        (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ))
      (d := (Module.finrank ℝ E : ℝ)) (q := (Fintype.card X : ℝ))
      hA' (Nat.cast_nonneg _) hk hk1 (mul_pos hcs hI) (Nat.cast_nonneg _) hC0
    refine ⟨K, fun δ J e hδ0 hδ4 hJ1 hJ2 he1 he2 => ⟨?_, hK δ J hδ0 hδ4 hJ1 hJ2⟩⟩
    have hδ1 : δ ≤ 1 := by linarith
    have hJ : 1 ≤ J := by
      have := Real.log_nonneg ((one_le_div hδ0).mpr hδ1)
      linarith
    obtain ⟨-, -, h3⟩ := hmain δ (1 / (8 * J ^ 2)) e hδ0 hδ1 (hα J hJ).1 (hα J hJ).2 he1 he2
    refine (h3 θ hI).trans (ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans ?_))
    exact target_bound hs0 hs1 hI hδ0 hδ1 hJ hA' (Nat.cast_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Explicit discovery and a frozen near-optimal plan** (`thm:v10g-discovery`) for the
finite-grid oracle, on the tape space, with `C = I_*(θ)`.  For every pilot risk `α ∈ (0, 1]`
and tolerances in the manuscript's range, the oracle meets `eq:v10g-oracle`, and at every `θ`
with `I_*(θ) > 0`: except on an event of probability at most `α` every pilot estimate obeys
`‖v_j - θ‖ ≤ ρ_j`; on that event the pilot commits at a first stage `j`, the frozen record
satisfies `eq:v10g-plan-rate`, and the pilot used at most `D̄` observations. -/
theorem grid_v10g_discovery (u : X → E) (Q : 𝒜 → Set E) {A0 : ℝ}
    (hA : ∀ a, ∃ lam ∈ Q a, ‖lam‖ ≤ A0) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 k : ℝ}
    (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k < 1) :
    ∀ (α : ℝ) (e : ℕ → ℝ), 0 < α → α ≤ 1 →
      (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j) →
      (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j) →
      OracleContract u Q w0 k e (gridOa u Q w0 k ℓ k0 A0 e) (gridOw u Q w0 k ℓ k0 A0 e)
        (gridOl u Q w0 k ℓ k0 A0 e) (gridOu u Q w0 k ℓ k0 A0 e) ∧
      ∀ θ : E, 0 < IstarG u Q θ →
        tapeP X {ω | ¬ ∀ j : ℕ, ‖pilotV u w0 (obsTape u θ (tapeξ 0) ω) j - θ‖ ≤
          pilotRho (Module.finrank ℝ E) k0 α j} ≤ ENNReal.ofReal α ∧
        ∀ ω : Fin 3 → X × ℕ → ℝ,
          (∀ j : ℕ, ‖pilotV u w0 (obsTape u θ (tapeξ 0) ω) j - θ‖ ≤
            pilotRho (Module.finrank ℝ E) k0 α j) →
          ∃ j, commitAt e k (gridOl u Q w0 k ℓ k0 A0 e)
              (pilotV u w0 (obsTape u θ (tapeξ 0) ω)) j ∧
            cstar k * IstarG u Q θ ≤
              (Real.sqrt (gridOl u Q w0 k ℓ k0 A0 e j
                (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j)) - e j) ^ 2 ∧
            (Real.sqrt (gridOl u Q w0 k ℓ k0 A0 e j
                (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j)) - e j) ^ 2 ≤
              gInfo u (Q (gridOa u Q w0 k ℓ k0 A0 e j (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j)))
                θ (gridOw u Q w0 k ℓ k0 A0 e j (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j)) ∧
            (∑ x, (roundCount w0 (2 ^ j) x : ℝ)) ≤
              Dbar (pilotA ℓ k0 k (IstarG u Q θ)) (Module.finrank ℝ E) α (Fintype.card X) := by
  intro α e hα0 hα1 he1 he2
  have hQ : ∀ a, (Q a).Nonempty := fun a => let ⟨lam, hlam, _⟩ := hA a; ⟨lam, hlam⟩
  have hor := gridOracle_contract u Q hw0 hk hk1.le hℓ hu hk0 hM0 hA (tol_pos hℓ hk0 hα0 hα1 he1)
  refine ⟨hor, fun θ hI => ?_⟩
  obtain ⟨aS, wS, hwS, heq, -⟩ := exists_IstarG_max u Q hQ θ hw0
  obtain ⟨h1, h2⟩ := v10g_discovery u Q hQ hw0 hℓ hu hk0 hM0 hk hk1 hα0 hα1 he1 he2 hor
    (tapeξ_iIndepFun 0) (tapeξ_hasLaw 0) θ aS hwS hI heq.ge
  refine ⟨h1, fun ω hω => ?_⟩
  obtain ⟨j, hg, hmin, hr1, hr2, hD⟩ := h2 ω hω
  exact ⟨j, ⟨hg, hmin⟩, hr1, hr2, hD⟩

end Final

end

end LiteralD1c

end JointRootCert
