/-
# Correlated Gaussian information limit, as written

Manuscript result covered: `thm:bay-main-optimal` (Correlated Gaussian information limit),
with the constructions of `app:known-gauss-info`, paragraphs "Regularity of the information
game" (the finite certified oracle) and "Allocation rule".

What this file adds to `GaussianTracking.lean`.

1. **The manuscript's finite-grid oracle.**  The simplex is gridded in steps `1/N`
   (`gridPts`, `gridDesign`), with covering radius `|X|/N` in `ℓ¹` (`grid_cover`); on the
   floor `(1 - η) Δ + η w⁰` the information is `ℓ¹`-Lipschitz in the design with constant
   `ℓ² C_R / (η κ)` (`info_l1_lipschitz`); and the oracle that evaluates each floored grid
   point to an interval of width `ξ/2` and returns the point maximising the lower endpoint
   meets `eq:bay-oracle-contract` when `N ≥ 2 |X| ℓ² C_R / (η κ ξ)` (`grid_oracle_contract`).
2. **The tracker built on that oracle** (`finGridTracker`): at round `k` and estimate `θ̂` it
   uses `η = ξ = (k+1)^{-1/4}`, `R = ‖θ̂‖ + 1`, `C_R = ℓ² (R + A)² / 2`,
   `N = ⌈2 |X| ℓ² C_R / (η κ ξ)⌉`, and a finite maximisation over the grid.  It satisfies the
   contract (`finGridTracker_valid`) and is Borel measurable (`finGridTracker_meas`).
3. **The theorem with the tracker fixed before the parameter**
   (`bay_main_optimal_literal`): one tracker, uniformly correct, such that at every `θ` with
   `I_*(θ) > 0` the ratio `E_θ τ_δ / log(1/δ)` tends to `1 / I_*(θ)`; and every uniformly
   correct family has `liminf ≥ 1 / I_*(θ)`.

4. **The active-set enumeration** for one projection (`IsCandidate`, `IsRetained`,
   `retained_optimal`, `candidate_unique`, `conic_caratheodory`, `active_set_complete`):
   every retained candidate solves the projection, the candidate of an independent active
   set is unique, and some independent active set of size at most `d` has a retained
   candidate.
5. **All polynomial moments** of the last violation time (`bad_poly_all`, `lastBad_moment`).
6. **The spanning hypothesis from a span condition** (`exists_kappa_of_span`,
   `bay_main_optimal_span`).

Not formalized: the tracker's oracle uses the exact value at each of the finitely many grid
points and is not connected to the enumeration of item 4 by a computed program (the
candidate of an active set is characterised by its linear system, not by the displayed
matrix inverses); the rounding of the estimate to rational data; numerical enclosures in the
stopping rule.  Samplers in the lower bound are deterministic functions of the history.
-/
import JointRootCert.GaussianTracking

namespace JointRootCert

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LiteralD1b

open GaussStopped GaussTrack

/-! ### The grid of the simplex and its covering radius -/

section Grid

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The grid of the simplex in steps `1/N`, as count vectors `c : X → ℕ` with `∑ c = N`. -/
def gridPts (X : Type*) [Fintype X] [DecidableEq X] (N : ℕ) : Finset (X → ℕ) :=
  Finset.piAntidiag univ N

lemma mem_gridPts {N : ℕ} {c : X → ℕ} : c ∈ gridPts X N ↔ ∑ x, c x = N := by
  simp [gridPts]

/-- The grid point `c / N`. -/
def gridDesign (N : ℕ) (c : X → ℕ) : X → ℝ := fun x => (c x : ℝ) / N

lemma gridDesign_nonneg (N : ℕ) (c : X → ℕ) (x : X) : 0 ≤ gridDesign N c x := by
  unfold gridDesign
  positivity

lemma gridDesign_mem {N : ℕ} (hN : 0 < N) {c : X → ℕ} (hc : c ∈ gridPts X N) :
    gridDesign N c ∈ simplex X := by
  refine ⟨gridDesign_nonneg N c, ?_⟩
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold gridDesign
  rw [← Finset.sum_div, ← Nat.cast_sum, mem_gridPts.mp hc, div_self hN']

/-- **Covering radius of the grid** (`app:known-gauss-info`: "its covering radius is at most
`|X|/N`"): every design in the simplex is within `ℓ¹`-distance `|X|/N` of a grid point. -/
theorem grid_cover {N : ℕ} (hN : 0 < N) {w : X → ℝ} (hw : w ∈ simplex X) :
    ∃ c ∈ gridPts X N, ∑ x, |gridDesign N c x - w x| ≤ (Fintype.card X : ℝ) / N := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let f : X → ℕ := fun x => ⌊(N : ℝ) * w x⌋₊
  have hfl : ∀ x, (f x : ℝ) ≤ N * w x := fun x =>
    Nat.floor_le (mul_nonneg hNr.le (hw.1 x))
  have hfu : ∀ x, (N : ℝ) * w x < f x + 1 := fun x => Nat.lt_floor_add_one _
  have hsum : ∑ x, (N : ℝ) * w x = N := by rw [← mul_sum, hw.2, mul_one]
  have hle : ∑ x, f x ≤ N := by
    have : ((∑ x, f x : ℕ) : ℝ) ≤ N := by
      rw [Nat.cast_sum, ← hsum]
      exact sum_le_sum fun x _ => hfl x
    exact_mod_cast this
  have hr : N - ∑ x, f x ≤ (univ : Finset X).card := by
    have h1 : (N : ℝ) ≤ ((∑ x, f x : ℕ) : ℝ) + (Fintype.card X : ℝ) := by
      rw [Nat.cast_sum]
      calc (N : ℝ) = ∑ x, (N : ℝ) * w x := hsum.symm
        _ ≤ ∑ x, ((f x : ℝ) + 1) := sum_le_sum fun x _ => (hfu x).le
        _ = ∑ x, (f x : ℝ) + Fintype.card X := by
            rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    have h2 : N ≤ ∑ x, f x + Fintype.card X := by exact_mod_cast h1
    rw [card_univ]
    omega
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq hr
  let c : X → ℕ := fun x => f x + if x ∈ T then 1 else 0
  have hcsum : ∑ x, c x = N := by
    have : ∑ x, c x = ∑ x, f x + T.card := by
      simp only [c, sum_add_distrib]
      congr 1
      rw [Finset.sum_ite_mem, univ_inter, sum_const, smul_eq_mul, mul_one]
    rw [this, hT]
    omega
  refine ⟨c, mem_gridPts.mpr hcsum, ?_⟩
  have hterm : ∀ x, |gridDesign N c x - w x| ≤ 1 / N := by
    intro x
    have e1 : gridDesign N c x - w x = ((c x : ℝ) - N * w x) / N := by
      unfold gridDesign
      field_simp
    rw [e1, abs_div, abs_of_pos hNr]
    refine div_le_div_of_nonneg_right ?_ hNr.le
    rw [abs_le]
    by_cases hx : x ∈ T
    · have : (c x : ℝ) = f x + 1 := by simp [c, hx]
      rw [this]
      constructor <;> linarith [hfl x, hfu x]
    · have : (c x : ℝ) = f x := by simp [c, hx]
      rw [this]
      constructor <;> linarith [hfl x, hfu x]
  calc ∑ x, |gridDesign N c x - w x| ≤ ∑ _x : X, (1 : ℝ) / N := sum_le_sum fun x _ => hterm x
    _ = (Fintype.card X : ℝ) / N := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

end Grid

/-! ### `ℓ¹`-Lipschitz dependence on the design, and the grid oracle -/

section GridOracle

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`ℓ¹`-Lipschitz bound in the design** (`app:known-gauss-info`: "on this floor, the
information is Lipschitz in `w` with constant `ℓ² C_R / (η κ)` in `ℓ¹`: a component
minimizer has displacement norm at most `√(2 C_R / (η κ))`, and evaluating it under another
design proves the bound").  If `M(w) ⪰ μ I` and `I(θ, w) ≤ C`, then for every design `w'`,
`I(θ, w') ≤ I(θ, w) + (ℓ² C / μ) ‖w' - w‖₁`.  On the floor, `μ = η κ`. -/
theorem info_l1_lipschitz (u : X → E) {ℓ : ℝ} (hu : ∀ x, ‖u x‖ ≤ ℓ) {Q : Set E}
    (hQ : Q.Nonempty) (θ : E) {w w' : X → ℝ} (hw : ∀ x, 0 ≤ w x) (hw' : ∀ x, 0 ≤ w' x)
    {μ C : ℝ} (hμ : 0 < μ) (hM : ∀ v, μ * ‖v‖ ^ 2 ≤ ‖designMap u w v‖ ^ 2)
    (hC : gInfo u Q θ w ≤ C) :
    gInfo u Q θ w' ≤ gInfo u Q θ w + ℓ ^ 2 * C / μ * ∑ x, |w' x - w x| := by
  have hC0 : 0 ≤ C := gInfo_nonneg.trans hC
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ x, |w' x - w x| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; exact sum_nonneg fun x _ => abs_nonneg _
  rw [← hSdef]
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hden : 0 < 1 + ℓ ^ 2 * S / μ := by positivity
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = η / (1 + ℓ ^ 2 * S / μ) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; positivity
  have htη : t * (1 + ℓ ^ 2 * S / μ) = η := by rw [htdef]; exact div_mul_cancel₀ _ hden.ne'
  have hglb := rootInfo_isGLB (A := designMap u w) (θ := θ) hQ
  have hlt : rootInfo (designMap u w) Q θ ^ 2 / 2 < gInfo u Q θ w + t := by
    unfold gInfo
    linarith
  obtain ⟨_, ⟨lam, hlam, rfl⟩, hlam2⟩ := (isGLB_lt_iff hglb).mp hlt
  have hlam2' : ‖designMap u w (lam - θ)‖ ^ 2 / 2 < gInfo u Q θ w + t := hlam2
  have hvsq : ‖lam - θ‖ ^ 2 ≤ 2 * (C + t) / μ := by
    rw [le_div_iff₀ hμ]
    have := hM (lam - θ)
    nlinarith
  have hinner : ∀ x, ⟪u x, lam - θ⟫ ^ 2 ≤ ℓ ^ 2 * ‖lam - θ‖ ^ 2 := fun x => by
    have h1 := abs_real_inner_le_norm (u x) (lam - θ)
    have h2 : ‖u x‖ * ‖lam - θ‖ ≤ ℓ * ‖lam - θ‖ :=
      mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
    have h3 : ⟪u x, lam - θ⟫ ^ 2 ≤ (ℓ * ‖lam - θ‖) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le ⟪u x, lam - θ⟫]) (by linarith [le_abs_self ⟪u x, lam - θ⟫])
    rw [mul_pow] at h3
    exact h3
  have hdiff : ‖designMap u w' (lam - θ)‖ ^ 2 ≤
      ‖designMap u w (lam - θ)‖ ^ 2 + S * (ℓ ^ 2 * ‖lam - θ‖ ^ 2) := by
    rw [norm_designMap_sq u hw, norm_designMap_sq u hw', hSdef, Finset.sum_mul,
      ← sum_add_distrib]
    refine sum_le_sum fun x _ => ?_
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (w' x - w x)) (sq_nonneg ⟪u x, lam - θ⟫)
    have h2 := mul_le_mul_of_nonneg_left (hinner x) (abs_nonneg (w' x - w x))
    linarith
  have hroot : gInfo u Q θ w' ≤ ‖designMap u w' (lam - θ)‖ ^ 2 / 2 := by
    have h1 := pow_le_pow_left₀ rootInfo_nonneg
      (rootInfo_le (A := designMap u w') (θ := θ) hlam) 2
    unfold gInfo
    linarith
  have hb : S * (ℓ ^ 2 * ‖lam - θ‖ ^ 2) ≤ S * (ℓ ^ 2 * (2 * (C + t) / μ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvsq (sq_nonneg ℓ)) hS0
  have e1 : S * (ℓ ^ 2 * (2 * (C + t) / μ)) / 2 = ℓ ^ 2 * C / μ * S + t * (ℓ ^ 2 * S / μ) := by
    field_simp
  have e2 : t * (1 + ℓ ^ 2 * S / μ) = t + t * (ℓ ^ 2 * S / μ) := by ring
  linarith

/-- **The finite certified oracle** (`app:known-gauss-info`, `eq:bay-oracle-contract`).
Center `θh`, alternatives `Q` of one action, bound `I(θh, w) ≤ C_R` on the simplex, reference
design `w⁰` with `M(w⁰) ⪰ κ I`, floor `η ∈ (0, 1]`, tolerance `ξ > 0`, and
`N ≥ 2 |X| ℓ² C_R / (η κ ξ)`.  Each floored grid point `(1 - η) c/N + η w⁰` is evaluated to an
interval `[lo c, lo c + ξ/2]` containing its information, and `cs` is a grid point
maximising the lower endpoint.  Then the design `v = (1 - η) cs/N + η w⁰` and the value
`c = lo cs` satisfy `0 ≤ c ≤ I(θh, v)` and `max_w I(θh, w) - c ≤ η C_R + ξ`. -/
theorem grid_oracle_contract (u : X → E) {ℓ : ℝ} (hu : ∀ x, ‖u x‖ ≤ ℓ) {Q : Set E}
    (hQ : Q.Nonempty) (θh : E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {κ : ℝ} (hκ : 0 < κ)
    (hM0 : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) {η ξ CR : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hξ : 0 < ξ) (hCR : ∀ w ∈ simplex X, gInfo u Q θh w ≤ CR) {N : ℕ}
    (hN0 : 0 < N) (hN : 2 * (Fintype.card X : ℝ) * ℓ ^ 2 * CR / (η * κ * ξ) ≤ N)
    {lo : (X → ℕ) → ℝ} (hlo0 : ∀ c ∈ gridPts X N, 0 ≤ lo c)
    (hlo1 : ∀ c ∈ gridPts X N, lo c ≤ gInfo u Q θh (floorDesign η w0 (gridDesign N c)))
    (hlo2 : ∀ c ∈ gridPts X N,
      gInfo u Q θh (floorDesign η w0 (gridDesign N c)) ≤ lo c + ξ / 2)
    {cs : X → ℕ} (hcs : cs ∈ gridPts X N) (hmax : ∀ c ∈ gridPts X N, lo c ≤ lo cs) :
    floorDesign η w0 (gridDesign N cs) ∈ simplex X ∧ 0 ≤ lo cs ∧
      lo cs ≤ gInfo u Q θh (floorDesign η w0 (gridDesign N cs)) ∧
      ∀ w ∈ simplex X, gInfo u Q θh w - lo cs ≤ η * CR + ξ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine ⟨floorDesign_mem hη0.le hη1 hw0 (gridDesign_mem hN0 hcs), hlo0 cs hcs, hlo1 cs hcs,
    fun w hw => ?_⟩
  have hCR0 : 0 ≤ CR := gInfo_nonneg.trans (hCR w hw)
  obtain ⟨c, hc, hcov⟩ := grid_cover hN0 hw
  -- the floor loses at most `η C_R`
  have hA : gInfo u Q θh w - η * CR ≤ gInfo u Q θh (floorDesign η w0 w) :=
    floor_rate_loss u hw.1 hw0.1 hη0.le hη1 hQ θh (hCR w hw)
  -- Lipschitz step from the floored grid point to the floored design
  have hcm : floorDesign η w0 (gridDesign N c) ∈ simplex X :=
    floorDesign_mem hη0.le hη1 hw0 (gridDesign_mem hN0 hc)
  have hwm : floorDesign η w0 w ∈ simplex X := floorDesign_mem hη0.le hη1 hw0 hw
  have hB := info_l1_lipschitz u hu hQ θh (w := floorDesign η w0 (gridDesign N c))
    (w' := floorDesign η w0 w) hcm.1 hwm.1 (mul_pos hη0 hκ)
    (floor_gram_lower u hw0.1 (gridDesign_nonneg N c) hη0.le hη1 hM0) (hCR _ hcm)
  have hdist : ∑ x, |floorDesign η w0 w x - floorDesign η w0 (gridDesign N c) x| ≤
      (Fintype.card X : ℝ) / N := by
    refine le_trans (sum_le_sum fun x _ => ?_) hcov
    have e1 : floorDesign η w0 w x - floorDesign η w0 (gridDesign N c) x =
        (1 - η) * (w x - gridDesign N c x) := by
      simp only [floorDesign]
      ring
    rw [e1, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - η), abs_sub_comm]
    have : (1 - η) * |gridDesign N c x - w x| ≤ 1 * |gridDesign N c x - w x| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have hcoef : 0 ≤ ℓ ^ 2 * CR / (η * κ) := by positivity
  have hsmall : ℓ ^ 2 * CR / (η * κ) * ((Fintype.card X : ℝ) / N) ≤ ξ / 2 := by
    have hηκξ : 0 < η * κ * ξ := by positivity
    rw [div_le_iff₀ hηκξ] at hN
    have e : ℓ ^ 2 * CR / (η * κ) * ((Fintype.card X : ℝ) / N) =
        (Fintype.card X : ℝ) * ℓ ^ 2 * CR / (η * κ * N) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hB' : gInfo u Q θh (floorDesign η w0 w) ≤
      gInfo u Q θh (floorDesign η w0 (gridDesign N c)) + ξ / 2 :=
    hB.trans (by
      have := mul_le_mul_of_nonneg_left hdist hcoef
      linarith)
  have h1 := hlo2 c hc
  have h2 := hmax c hc
  linarith

end GridOracle

/-! ### The tracker with the finite-grid oracle -/

section FinGrid

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]

/-- `C_R = ℓ² (R + A)² / 2` at `R = ‖θ̂‖ + 1`. -/
def CRat (ℓ A0 : ℝ) (θh : ι → ℝ) : ℝ :=
  ℓ ^ 2 * (‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ + 1 + A0) ^ 2 / 2

/-- The grid size `N = ⌈2 |X| ℓ² C_R / (η κ ξ)⌉` (at least one) at round `k`, with
`η = ξ = (k+1)^{-1/4}`. -/
def gridN (X : Type*) [Fintype X] (ℓ κ A0 : ℝ) (k : ℕ) (θh : ι → ℝ) : ℕ :=
  max 1 ⌈2 * (Fintype.card X : ℝ) * ℓ ^ 2 * CRat ℓ A0 θh / (etaK k * κ * etaK k)⌉₊

lemma gridN_pos (ℓ κ A0 : ℝ) (k : ℕ) (θh : ι → ℝ) : 0 < gridN X ℓ κ A0 k θh :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

lemma measurable_gridN (ℓ κ A0 : ℝ) (k : ℕ) :
    Measurable (fun θh : ι → ℝ => gridN X ℓ κ A0 k θh) := by
  have h1 : Measurable (fun θh : ι → ℝ => ‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖) :=
    measurable_norm.comp (WithLp.measurable_toLp 2 _)
  have h2 : Measurable (fun θh : ι → ℝ => CRat ℓ A0 θh) := by
    unfold CRat
    exact ((((h1.add_const 1).add_const A0).pow_const 2).const_mul _).div_const 2
  unfold gridN
  exact measurable_const.max (Nat.measurable_ceil.comp ((h2.const_mul _).div_const _))

/-- A fixed enumeration of the count vectors (the fixed order used to break ties). -/
def gridEnum (X : Type*) [Fintype X] : ℕ → X → ℕ :=
  Classical.choose (exists_surjective_nat (X → ℕ))

lemma gridEnum_surjective : Function.Surjective (gridEnum X) :=
  Classical.choose_spec (exists_surjective_nat (X → ℕ))

lemma gridPts_nonempty (N : ℕ) : (gridPts X N).Nonempty := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty X›
  refine ⟨fun x => if x = x0 then N else 0, mem_gridPts.mpr ?_⟩
  simp

/-- A maximiser over the finite grid exists (in the fixed enumeration). -/
lemma exists_grid_argmax (f : (X → ℕ) → ℝ) (N : ℕ) :
    ∃ j, gridEnum X j ∈ gridPts X N ∧ ∀ c ∈ gridPts X N, f c ≤ f (gridEnum X j) := by
  obtain ⟨c0, hc0, hmax⟩ := Finset.exists_max_image (gridPts X N) f (gridPts_nonempty N)
  obtain ⟨j, hj⟩ := gridEnum_surjective c0
  exact ⟨j, by rw [hj]; exact hc0, fun c hc => by rw [hj]; exact hmax c hc⟩

/-- Exact information of the floored grid point `c / N` at round `k`. -/
def gval (uE : X → EuclideanSpace ℝ ι) (Qa : Set (EuclideanSpace ℝ ι)) (w0 : X → ℝ)
    (k N : ℕ) (c : X → ℕ) (θh : ι → ℝ) : ℝ :=
  gInfo uE Qa (WithLp.toLp 2 θh) (floorDesign (etaK k) w0 (gridDesign N c))

lemma measurable_gval (uE : X → EuclideanSpace ℝ ι) (Qa : Set (EuclideanSpace ℝ ι))
    (w0 : X → ℝ) (k N : ℕ) (c : X → ℕ) : Measurable (fun θh : ι → ℝ => gval uE Qa w0 k N c θh) :=
  measurable_gridVal uE Qa w0 (fun _ => gridDesign N c) k 0

/-- Index (in the fixed enumeration) of the first grid point maximising the value. -/
def gridIdx (uE : X → EuclideanSpace ℝ ι) (Qa : Set (EuclideanSpace ℝ ι)) (w0 : X → ℝ)
    (ℓ κ A0 : ℝ) (k : ℕ) (θh : ι → ℝ) : ℕ :=
  Nat.find (exists_grid_argmax (fun c => gval uE Qa w0 k (gridN X ℓ κ A0 k θh) c θh)
    (gridN X ℓ κ A0 k θh))

lemma gridIdx_spec (uE : X → EuclideanSpace ℝ ι) (Qa : Set (EuclideanSpace ℝ ι)) (w0 : X → ℝ)
    (ℓ κ A0 : ℝ) (k : ℕ) (θh : ι → ℝ) :
    gridEnum X (gridIdx uE Qa w0 ℓ κ A0 k θh) ∈ gridPts X (gridN X ℓ κ A0 k θh) ∧
      ∀ c ∈ gridPts X (gridN X ℓ κ A0 k θh),
        gval uE Qa w0 k (gridN X ℓ κ A0 k θh) c θh ≤
          gval uE Qa w0 k (gridN X ℓ κ A0 k θh)
            (gridEnum X (gridIdx uE Qa w0 ℓ κ A0 k θh)) θh :=
  Nat.find_spec (exists_grid_argmax (fun c => gval uE Qa w0 k (gridN X ℓ κ A0 k θh) c θh)
    (gridN X ℓ κ A0 k θh))

lemma measurable_gridIdx (uE : X → EuclideanSpace ℝ ι) (Qa : Set (EuclideanSpace ℝ ι))
    (w0 : X → ℝ) (ℓ κ A0 : ℝ) (k : ℕ) :
    Measurable (fun θh : ι → ℝ => gridIdx uE Qa w0 ℓ κ A0 k θh) := by
  unfold gridIdx
  refine measurable_find _ fun j => ?_
  have hset : {θh : ι → ℝ | gridEnum X j ∈ gridPts X (gridN X ℓ κ A0 k θh) ∧
      ∀ c ∈ gridPts X (gridN X ℓ κ A0 k θh),
        gval uE Qa w0 k (gridN X ℓ κ A0 k θh) c θh ≤
          gval uE Qa w0 k (gridN X ℓ κ A0 k θh) (gridEnum X j) θh} =
      ⋃ n : ℕ, ((fun θh : ι → ℝ => gridN X ℓ κ A0 k θh) ⁻¹' {n}) ∩
        {θh : ι → ℝ | gridEnum X j ∈ gridPts X n ∧ ∀ c ∈ gridPts X n,
          gval uE Qa w0 k n c θh ≤ gval uE Qa w0 k n (gridEnum X j) θh} := by
    ext θh
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨n, rfl, h⟩
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun n => (measurable_gridN ℓ κ A0 k (measurableSet_singleton n)).inter ?_
  by_cases hmem : gridEnum X j ∈ gridPts X n
  · have : {θh : ι → ℝ | gridEnum X j ∈ gridPts X n ∧ ∀ c ∈ gridPts X n,
        gval uE Qa w0 k n c θh ≤ gval uE Qa w0 k n (gridEnum X j) θh} =
        ⋂ c ∈ gridPts X n, {θh : ι → ℝ |
          gval uE Qa w0 k n c θh ≤ gval uE Qa w0 k n (gridEnum X j) θh} := by
      ext θh
      simp [hmem]
    rw [this]
    exact Finset.measurableSet_biInter _ fun c _ =>
      measurableSet_le (measurable_gval uE Qa w0 k n c) (measurable_gval uE Qa w0 k n _)
  · have : {θh : ι → ℝ | gridEnum X j ∈ gridPts X n ∧ ∀ c ∈ gridPts X n,
        gval uE Qa w0 k n c θh ≤ gval uE Qa w0 k n (gridEnum X j) θh} = ∅ := by
      ext θh
      simp [hmem]
    rw [this]
    exact MeasurableSet.empty

/-- **The tracker with the manuscript's finite-grid oracle.**  At round `k`, estimate `θ̂`
and action `a`, the oracle forms the grid of step `1/N`, `N = gridN`, mixes every grid
point with `η w⁰`, `η = (k+1)^{-1/4}`, evaluates the information of `a` there, and returns a
grid point of maximal value (the first in a fixed enumeration) with that value.  The
constants `ℓ`, `κ`, `A0` (feature bound, reference eigenvalue bound, anchor bound) enter
only through `N`. -/
def finGridTracker (u : X → ι → ℝ) (v : X → ℝ) (Q : 𝒜 → Set (EuclideanSpace ℝ ι))
    (w0 : X → ℝ) (γ ℓ κ A0 : ℝ) : Tracker X ι 𝒜 where
  u := u
  v := v
  Q := Q
  w0 := w0
  γ := γ
  ow k θh a := floorDesign (etaK k) w0 (gridDesign (gridN X ℓ κ A0 k θh)
    (gridEnum X (gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0
      ℓ κ A0 k θh)))
  oc k θh a := gval (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 k
    (gridN X ℓ κ A0 k θh)
    (gridEnum X (gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0
      ℓ κ A0 k θh)) θh

variable [MeasurableSpace 𝒜]

/-- The finite-grid oracle is Borel measurable in the estimate. -/
lemma finGridTracker_meas (u : X → ι → ℝ) (v : X → ℝ) (Q : 𝒜 → Set (EuclideanSpace ℝ ι))
    (w0 : X → ℝ) (γ ℓ κ A0 : ℝ) : (finGridTracker u v Q w0 γ ℓ κ A0).Meas := by
  have hpair : ∀ (k : ℕ) (a : 𝒜), Measurable (fun θh : ι → ℝ =>
      ((gridN X ℓ κ A0 k θh, gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι))
        (Q a) w0 ℓ κ A0 k θh) : ℕ × ℕ)) := by
    intro k a
    have h1 : Measurable (fun θh : ι → ℝ => gridN X ℓ κ A0 k θh) := measurable_gridN ℓ κ A0 k
    have h2 : Measurable (fun θh : ι → ℝ =>
        gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 ℓ κ A0 k θh) :=
      measurable_gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 ℓ κ A0 k
    exact h1.prodMk h2
  have hoc : ∀ (k : ℕ) (a : 𝒜), Measurable fun θh : ι → ℝ =>
      gval (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 k
        (gridN X ℓ κ A0 k θh)
        (gridEnum X (gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0
          ℓ κ A0 k θh)) θh := by
    intro k a
    have h : Measurable fun p : (ι → ℝ) × (ℕ × ℕ) =>
        gval (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 k p.2.1
          (gridEnum X p.2.2) p.1 :=
      measurable_from_prod_countable_left fun q =>
        measurable_gval (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 k q.1
          (gridEnum X q.2)
    exact Measurable.comp (g := fun p : (ι → ℝ) × (ℕ × ℕ) =>
        gval (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 k p.2.1
          (gridEnum X p.2.2) p.1)
      (f := fun θh : ι → ℝ => (θh, ((gridN X ℓ κ A0 k θh,
        gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 ℓ κ A0 k θh) :
          ℕ × ℕ)))
      h (measurable_id.prodMk (hpair k a))
  have how : ∀ (k : ℕ) (a : 𝒜), Measurable fun θh : ι → ℝ =>
      floorDesign (etaK k) w0 (gridDesign (gridN X ℓ κ A0 k θh)
        (gridEnum X (gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0
          ℓ κ A0 k θh))) := by
    intro k a
    exact Measurable.comp (g := fun q : ℕ × ℕ =>
        floorDesign (etaK k) w0 (gridDesign q.1 (gridEnum X q.2)))
      (f := fun θh : ι → ℝ => ((gridN X ℓ κ A0 k θh,
        gridIdx (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 ℓ κ A0 k θh) :
          ℕ × ℕ))
      Measurable.of_discrete (hpair k a)
  exact ⟨hoc, how⟩

/-- **The finite-grid oracle meets the contract `eq:bay-oracle-contract`**: the tracker is
`Valid`.  The proof is `grid_oracle_contract` with `η = ξ = (k+1)^{-1/4}` and
`R = ‖θ̂‖ + 1`. -/
lemma finGridTracker_valid (u : X → ι → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    (Q : 𝒜 → Set (EuclideanSpace ℝ ι)) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {γ : ℝ} (hγ : 0 < γ)
    {ℓ κ A0 : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, u x ⬝ᵥ u x ≤ ℓ ^ 2) (hκ : 0 < κ)
    (hspan : ∀ e : ι → ℝ, κ * (e ⬝ᵥ e) ≤ ∑ x, w0 x * (u x ⬝ᵥ e) ^ 2)
    (hQ : ∀ a, ∃ lam ∈ Q a, ‖lam‖ ≤ A0) :
    (finGridTracker u v Q w0 γ ℓ κ A0).Valid ℓ κ A0 := by
  have huE : ∀ x, ‖(WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)‖ ≤ ℓ := by
    intro x
    have h : ‖(WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)‖ ^ 2 ≤ ℓ ^ 2 := by
      rw [Tracker.norm_tE_sq]
      exact hu x
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hℓ.le two_ne_zero).mp h
  have hM0 : ∀ z : EuclideanSpace ℝ ι, κ * ‖z‖ ^ 2 ≤
      ‖designMap (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) w0 z‖ ^ 2 := by
    intro z
    have h2 : ‖z‖ ^ 2 = z.ofLp ⬝ᵥ z.ofLp := by
      rw [← Tracker.norm_tE_sq z.ofLp]
    have h3 := hspan z.ofLp
    have h4 : ‖designMap (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) w0 z‖ ^ 2 =
        ∑ x, w0 x * (u x ⬝ᵥ z.ofLp) ^ 2 := by
      rw [norm_designMap_sq _ hw0.1]
      refine sum_congr rfl fun x _ => ?_
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct_comm]
    rw [h4, h2]
    exact h3
  have hspec := fun (k : ℕ) (θh : ι → ℝ) (a : 𝒜) =>
    gridIdx_spec (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 ℓ κ A0 k θh
  refine ⟨hv, hw0, hγ, hℓ, hu, hκ, hspan, hQ, ?_, ?_, ?_⟩
  · intro k θh a
    exact ⟨_, gridDesign_mem (gridN_pos ℓ κ A0 k θh) (hspec k θh a).1, rfl⟩
  · intro k θh a
    exact ⟨gInfo_nonneg, le_rfl⟩
  · intro k θh a w hw
    obtain ⟨lam0, h0, hA⟩ := hQ a
    have hCR : ∀ w ∈ simplex X,
        gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) (WithLp.toLp 2 θh) w ≤
          CRat ℓ A0 θh := fun w hw =>
      info_le_anchor _ hw hℓ.le huE h0 hA (by linarith)
    have hN : 2 * (Fintype.card X : ℝ) * ℓ ^ 2 * CRat ℓ A0 θh / (etaK k * κ * etaK k) ≤
        (gridN X ℓ κ A0 k θh : ℝ) := by
      refine (Nat.le_ceil _).trans (Nat.cast_le.mpr ?_)
      exact le_max_right _ _
    have := (grid_oracle_contract (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) huE
      ⟨lam0, h0⟩ (WithLp.toLp 2 θh) hw0 hκ hM0 (etaK_pos k) (etaK_le_one k) (etaK_pos k) hCR
      (gridN_pos ℓ κ A0 k θh) hN
      (lo := fun c => gval (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 k
        (gridN X ℓ κ A0 k θh) c θh)
      (fun c _ => gInfo_nonneg) (fun c _ => le_rfl)
      (fun c _ => by
        have := (etaK_pos k).le
        show gval _ _ _ _ _ _ _ ≤ gval _ _ _ _ _ _ _ + etaK k / 2
        linarith)
      (hspec k θh a).1 (hspec k θh a).2).2.2.2 w hw
    exact this

end FinGrid

/-! ### `thm:bay-main-optimal` with the tracker fixed before the parameter -/

section Final

variable {X ι 𝒜 Z : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype 𝒜] [Nonempty 𝒜]
  [MeasurableSpace 𝒜] [MeasurableSingletonClass 𝒜] [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- `I_*(θ) = sup_a sup_{w ∈ Δ(X)} I_a(θ, w)` for the whitened features `u` and the
alternative sets `Q`. -/
def IstarE (u : X → ι → ℝ) (Q : 𝒜 → Set (EuclideanSpace ℝ ι)) (θ : ι → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a, ∃ w ∈ simplex X,
    r = gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) (WithLp.toLp 2 θ) w}

/-- **Correlated Gaussian information limit (`thm:bay-main-optimal`), as written.**

Model: finitely many queries `x` with whitened features `u_x ∈ ℝ^d` and known variances
`v_x > 0`; under the parameter `λ` the observation of `x` is `N(√(v_x) ⟨u_x, λ⟩, v_x)`.  The
dictionary is spanning: some design `w⁰` has `M(w⁰) ⪰ κ I`, `κ > 0`.  Terminals have features
`φ_z`, root actions have nonempty supports, and every action has a strict `ε`-invalidating
alternative (the branch left after the hull test).  A family `(S δ, D δ)` is uniformly
correct if for every `δ ∈ (0, 1)`, action `a` and parameter `λ` with `r_λ(a) > ε` it halts
with answer `a` with probability at most `δ`.

(1) For every `θ` with `I_*(θ) > 0`, every uniformly correct family has
`liminf_{δ ↓ 0} E_θ τ_δ / log(1/δ) ≥ 1 / I_*(θ)`.

(2) There are constants `ℓ`, `A0` such that the tracker `T = finGridTracker u v Q w⁰ 1 ℓ κ A0`
(the manuscript's allocation rule with the finite-grid oracle), which is fixed before any
parameter is chosen, is Borel measurable and satisfies:
  (a) it is uniformly correct, and under every parameter the total probability of halting
      with an answer that is not `ε`-acceptable is at most `δ`;
  (b) at every `θ` with `I_*(θ) > 0`, `E_θ τ_δ < ∞` for all `δ ∈ (0, 1)` and
      `E_θ τ_δ / log(1/δ) → 1 / I_*(θ)` as `δ ↓ 0` (equality is attained). -/
theorem bay_main_optimal_literal (u : X → ι → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {κ : ℝ} (hκ : 0 < κ)
    (hspan : ∀ e : ι → ℝ, κ * (e ⬝ᵥ e) ≤ ∑ x, w0 x * (u x ⬝ᵥ e) ^ 2)
    (φ : Z → EuclideanSpace ℝ ι) (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQne : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) :
    (∀ θ : ι → ℝ, 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
      ∀ (S : ℝ → GSampler X) (D : ℝ → GDecision 𝒜),
        (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
          law (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
            (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ) →
        ∀ c : ℝ, c < 1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤
            expTau (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v) ∧
    ∃ (ℓ A0 : ℝ)
      (hT : (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).Meas),
      (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).Valid ℓ κ A0 ∧
      (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
        law ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).sampler
            hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
          (ansSet ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
              A0).sampler hT δ)
            ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
              A0).decision hT δ) a n) ≤ ENNReal.ofReal δ) ∧
      (∀ δ, 0 < δ → δ < 1 → ∀ (lam : EuclideanSpace ℝ ι) (n : ℕ),
        law ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).sampler
            hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
          (⋃ a ∈ {a : 𝒜 | lam ∈ strictAlt φ (supp a) (hne a) ε},
            ansSet ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
                A0).sampler hT δ)
              ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
                A0).decision hT δ) a n) ≤ ENNReal.ofReal δ) ∧
      ∀ θ : ι → ℝ, 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
        (∀ δ, 0 < δ → δ < 1 →
          expTau ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
            A0).sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v ≠ ⊤) ∧
        Tendsto (fun δ : ℝ =>
            (expTau ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
              A0).sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v).toReal /
              Real.log (1 / δ))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ)) := by
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.sqrt (∑ x, u x ⬝ᵥ u x) + 1 := ⟨_, rfl⟩
  have hS0 : 0 ≤ ∑ x, u x ⬝ᵥ u x := sum_nonneg fun x _ => dotProduct_self_nonneg' (u x)
  have hℓ : 0 < ℓ := by
    rw [hℓdef]
    have := Real.sqrt_nonneg (∑ x, u x ⬝ᵥ u x)
    linarith
  have hu : ∀ x, u x ⬝ᵥ u x ≤ ℓ ^ 2 := by
    intro x
    have h1 : u x ⬝ᵥ u x ≤ ∑ x, u x ⬝ᵥ u x :=
      Finset.single_le_sum (f := fun x => u x ⬝ᵥ u x)
        (fun x _ => dotProduct_self_nonneg' (u x)) (mem_univ x)
    have h2 := Real.sq_sqrt hS0
    have h3 := Real.sqrt_nonneg (∑ x, u x ⬝ᵥ u x)
    rw [hℓdef]
    nlinarith
  choose lamA hlamA using hQne
  have hQ : ∀ a, ∃ lam ∈ strictAlt φ (supp a) (hne a) ε, ‖lam‖ ≤ ∑ a, ‖lamA a‖ := fun a =>
    ⟨lamA a, hlamA a, Finset.single_le_sum (f := fun a => ‖lamA a‖)
      (fun a _ => norm_nonneg _) (mem_univ a)⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Tracker X ι 𝒜,
      T = finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
        (∑ a, ‖lamA a‖) := ⟨_, rfl⟩
  have hT : T.Meas := by
    rw [hTdef]
    exact finGridTracker_meas _ _ _ _ _ _ _ _
  have hV : T.Valid ℓ κ (∑ a, ‖lamA a‖) := by
    rw [hTdef]
    exact finGridTracker_valid u hv _ hw0 one_pos hℓ hu hκ hspan hQ
  have hTQ : ∀ a, T.Q a = strictAlt φ (supp a) (hne a) ε := fun a => by rw [hTdef]; rfl
  have hTmean : ∀ th : ι → ℝ, T.mean th = fun x => Real.sqrt (v x) * (u x ⬝ᵥ th) := fun th => by
    rw [hTdef]
    rfl
  have hTv : T.v = v := by rw [hTdef]; rfl
  have hIeq : ∀ θ : ι → ℝ,
      IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ = T.Istar θ := by
    intro θ
    have h := T.Istar_isLUB θ hV
    have hset : {r : ℝ | ∃ a, ∃ w ∈ simplex X,
        r = gInfo T.uE (T.Q a) (WithLp.toLp 2 θ) w} =
        {r : ℝ | ∃ a, ∃ w ∈ simplex X,
          r = gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι))
            (strictAlt φ (supp a) (hne a) ε) (WithLp.toLp 2 θ) w} := by
      rw [hTdef]
      rfl
    rw [hset] at h
    exact h.csSup_eq ⟨_, Classical.arbitrary 𝒜, w0, hw0, rfl⟩
  have hsafe : ∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
      law (T.sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
        (ansSet (T.sampler hT δ) (T.decision hT δ) a n) ≤ ENNReal.ofReal δ := by
    intro δ hδ0 hδ1 a lam hlam n
    rw [← hTQ a] at hlam
    have := T.safe hT hV φ supp hne ε hTQ hδ0 hδ1 lam.ofLp a hlam n
    simpa only [hTmean, hTv] using this
  have hlower : ∀ θ : ι → ℝ, 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
      ∀ (S : ℝ → GSampler X) (D : ℝ → GDecision 𝒜),
        (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
          law (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
            (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ) →
        ∀ c : ℝ, c < 1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤
            expTau (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v := by
    intro θ hI S D hc c hcI
    rw [hIeq θ] at hI hcI
    obtain ⟨-, h2, -⟩ := T.bay_main_optimal hT θ hV φ supp hne ε hTQ hI
    simp only [hTmean, hTv] at h2
    refine h2 S D (fun δ hδ0 hδ1 a lam hlam n => ?_) c hcI
    rw [hTQ a] at hlam
    exact hc δ hδ0 hδ1 a lam hlam n
  refine ⟨hlower, ℓ, ∑ a, ‖lamA a‖, hTdef ▸ hT, ?_⟩
  subst hTdef
  refine ⟨hV, hsafe, ?_, ?_⟩
  · intro δ hδ0 hδ1 lam n
    have hj := (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
      (∑ a, ‖lamA a‖)).safe_joint hT hV φ supp hne ε hTQ hδ0 hδ1 lam.ofLp n
    simp only [hTmean, hTv] at hj
    exact hj
  · intro θ hI
    have hI' := hI
    rw [hIeq θ] at hI'
    obtain ⟨-, -, h3, h4, -⟩ := (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε)
      w0 1 ℓ κ (∑ a, ‖lamA a‖)).bay_main_optimal hT θ hV φ supp hne ε hTQ hI'
    rw [← hIeq θ] at h3
    simp only [hTmean, hTv] at h3 h4
    refine ⟨h4, ?_⟩
    have hlow := hlower θ hI _ _ hsafe
    rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨c, hac, hc⟩ := exists_between ha
      filter_upwards [hlow c hc, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ hδ01
      have hlog : 0 < Real.log (1 / δ) :=
        Real.log_pos (by rw [lt_div_iff₀ hδ01.1]; linarith [hδ01.2])
      have hfin := h4 δ hδ01.1 hδ01.2
      have h5 : c * Real.log (1 / δ) ≤ (expTau ((finGridTracker u v
          (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ (∑ a, ‖lamA a‖)).sampler hT δ)
          (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hfin).mp hδ
      rw [lt_div_iff₀ hlog]
      nlinarith
    · intro a ha
      obtain ⟨δ0, hδ0, hup⟩ := h3 ((a - 1 / IstarE u
        (fun a => strictAlt φ (supp a) (hne a) ε) θ) / 2) (by linarith)
      filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
      have := (hup δ hδ.1 hδ.2).2
      linarith

end Final

/-! ### The active-set enumeration for one quadratic projection

`app:known-gauss-info`: "Each projection can be solved in finitely many exact operations by
enumerating independent active constraint subsets of size at most `d`, including the empty
subset: for a nonempty subset `J`, solve `α_J = (D_J M⁻¹ D_Jᵀ)⁻¹ b_J` and
`v_J = M⁻¹ D_Jᵀ α_J`; retain it if `α_J ≥ 0` and `D v_J ≥ b`.  At least one succeeds by conic
Caratheodory applied to an optimal stationarity vector."

The projection is `min {½ ‖A v‖² : ⟪d y, v⟫ ≥ b y for all y}` with `M = AᵀA`.  The pair
`(v_J, α_J)` is characterised by the linear system it solves (`IsCandidate`): `α` vanishes
off `J`, `M v = Dᵀ α`, and `D_J v = b_J`. -/

section ActiveSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(v, α)` solves the linear system of the active set `J`: `α` vanishes off `J`,
`M v = Dᵀ α` (written `∑ α_y ⟪d_y, h⟫ = ⟪A v, A h⟫` for all `h`), and `⟪d_y, v⟫ = b_y` on `J`.
For `J = ∅` this forces `M v = 0`. -/
def IsCandidate (A : E →ₗ[ℝ] F) (d : ι → E) (b : ι → ℝ) (J : Finset ι) (v : E) (α : ι → ℝ) :
    Prop :=
  (∀ y, y ∉ J → α y = 0) ∧ (∀ h : E, ∑ y, α y * ⟪d y, h⟫ = ⟪A v, A h⟫) ∧ ∀ y ∈ J, ⟪d y, v⟫ = b y

/-- The candidate of `J` is retained: `α ≥ 0` and `D v ≥ b`. -/
def IsRetained (A : E →ₗ[ℝ] F) (d : ι → E) (b : ι → ℝ) (J : Finset ι) (v : E) (α : ι → ℝ) :
    Prop :=
  IsCandidate A d b J v α ∧ (∀ y, 0 ≤ α y) ∧ ∀ y, b y ≤ ⟪d y, v⟫

/-- **A retained candidate solves the projection**: it is feasible and no feasible point has
a smaller value. -/
theorem retained_optimal {A : E →ₗ[ℝ] F} {d : ι → E} {b : ι → ℝ} {J : Finset ι} {v : E}
    {α : ι → ℝ} (hR : IsRetained A d b J v α) {v' : E} (hv' : ∀ y, b y ≤ ⟪d y, v'⟫) :
    ‖A v‖ ≤ ‖A v'‖ := by
  obtain ⟨⟨hsupp, hstat, hact⟩, hα, hfeas⟩ := hR
  have h1 : ‖A v‖ ^ 2 ≤ ⟪A v, A v'⟫ := by
    have h := hstat (v' - v)
    rw [map_sub, inner_sub_right, real_inner_self_eq_norm_sq] at h
    have hnn : 0 ≤ ∑ y, α y * ⟪d y, v' - v⟫ := by
      refine sum_nonneg fun y _ => ?_
      by_cases hy : y ∈ J
      · rw [inner_sub_right, hact y hy]
        exact mul_nonneg (hα y) (sub_nonneg.mpr (hv' y))
      · rw [hsupp y hy, zero_mul]
    linarith
  have h2 := real_inner_le_norm (A v) (A v')
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ‖A v‖ := lt_of_le_of_lt (norm_nonneg _) hcon
  nlinarith [mul_pos (sub_pos.mpr hcon) hpos]

/-- **The candidate of an independent active set is unique** (so it is the pair given by the
manuscript's formulas, when `M ≻ 0`). -/
theorem candidate_unique {A : E →ₗ[ℝ] F} (hA : Function.Injective A) {d : ι → E} {b : ι → ℝ}
    {J : Finset ι} (hJ : LinearIndependent ℝ (fun y : {y // y ∈ J} => d y)) {v v' : E}
    {α α' : ι → ℝ} (h : IsCandidate A d b J v α) (h' : IsCandidate A d b J v' α') :
    v = v' ∧ α = α' := by
  obtain ⟨hs, hst, hac⟩ := h
  obtain ⟨hs', hst', hac'⟩ := h'
  have hdiff : ∀ k : E, ∑ y, (α y - α' y) * ⟪d y, k⟫ = ⟪A (v - v'), A k⟫ := by
    intro k
    rw [map_sub, inner_sub_left, ← hst k, ← hst' k, ← sum_sub_distrib]
    exact sum_congr rfl fun y _ => by ring
  have hzero : ‖A (v - v')‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, ← hdiff (v - v')]
    refine sum_eq_zero fun y _ => ?_
    by_cases hy : y ∈ J
    · rw [inner_sub_right, hac y hy, hac' y hy, sub_self, mul_zero]
    · rw [hs y hy, hs' y hy, sub_self, zero_mul]
  have hv : v = v' := by
    have h0 : A (v - v') = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hzero)
    have := (injective_iff_map_eq_zero A).mp hA _ h0
    exact sub_eq_zero.mp this
  refine ⟨hv, ?_⟩
  have hcomb : ∑ y, (α y - α' y) • d y = 0 := by
    have hall : ∀ k : E, ⟪∑ y, (α y - α' y) • d y, k⟫ = 0 := by
      intro k
      rw [sum_inner]
      have := hdiff k
      rw [hv, sub_self, map_zero, inner_zero_left] at this
      rw [← this]
      exact sum_congr rfl fun y _ => by rw [real_inner_smul_left]
    have := hall (∑ y, (α y - α' y) • d y)
    exact inner_self_eq_zero.mp this
  have hJsum : ∑ i : {y // y ∈ J}, (α i - α' i) • d i = 0 := by
    rw [Finset.sum_coe_sort J (fun y => (α y - α' y) • d y),
      Finset.sum_subset (subset_univ J) (fun y _ hy => by rw [hs y hy, hs' y hy, sub_self, zero_smul])]
    exact hcomb
  have hcoef := Fintype.linearIndependent_iff.mp hJ (fun i => α i - α' i) hJsum
  funext y
  by_cases hy : y ∈ J
  · exact sub_eq_zero.mp (hcoef ⟨y, hy⟩)
  · rw [hs y hy, hs' y hy]

/-- One step of the conic Caratheodory reduction: a nonnegative combination and a linear
relation among its active vectors give a nonnegative combination of the same vector with
strictly fewer active vectors. -/
lemma conic_step (d : ι → E) {α c : ι → ℝ} (hα : ∀ y, 0 ≤ α y) (hcs : ∀ y, α y = 0 → c y = 0)
    (hc0 : ∑ y, c y • d y = 0) {y1 : ι} (hy1 : 0 < c y1) :
    ∃ α' : ι → ℝ, (∀ y, 0 ≤ α' y) ∧ (∀ y, α y = 0 → α' y = 0) ∧
      ∑ y, α' y • d y = ∑ y, α y • d y ∧
      (univ.filter fun y => α' y ≠ 0).card < (univ.filter fun y => α y ≠ 0).card := by
  obtain ⟨y0, hy0, hmin⟩ := Finset.exists_min_image (univ.filter fun y => 0 < c y)
    (fun y => α y / c y) ⟨y1, by simp [hy1]⟩
  have hc0pos : 0 < c y0 := (mem_filter.mp hy0).2
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = α y0 / c y0 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [htdef]; exact div_nonneg (hα y0) hc0pos.le
  refine ⟨fun y => α y - t * c y, ?_, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : 0 < c y
    · have h := hmin y (mem_filter.mpr ⟨mem_univ y, hy⟩)
      rw [← htdef, le_div_iff₀ hy] at h
      show 0 ≤ α y - t * c y
      linarith
    · have : t * c y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (not_lt.mp hy)
      show 0 ≤ α y - t * c y
      linarith [hα y]
  · intro y hy
    show α y - t * c y = 0
    rw [hy, hcs y hy]
    ring
  · simp only [sub_smul, sum_sub_distrib, mul_smul]
    rw [← smul_sum, hc0, smul_zero, sub_zero]
  · apply Finset.card_lt_card
    have hsub : (univ.filter fun y => α y - t * c y ≠ 0) ⊆ (univ.filter fun y => α y ≠ 0) := by
      intro y hy
      rw [mem_filter] at hy ⊢
      refine ⟨mem_univ y, fun h0 => hy.2 ?_⟩
      rw [h0, hcs y h0]
      ring
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨y0, ?_, ?_⟩
    · rw [mem_filter]
      exact ⟨mem_univ y0, fun h0 => hc0pos.ne' (hcs y0 h0)⟩
    · rw [mem_filter]
      push Not
      intro _
      rw [htdef, div_mul_cancel₀ _ hc0pos.ne', sub_self]

/-- **Conic Caratheodory**: a nonnegative combination can be rewritten as a nonnegative
combination of linearly independent vectors among those it uses. -/
theorem conic_caratheodory (d : ι → E) : ∀ (n : ℕ) (α : ι → ℝ), (∀ y, 0 ≤ α y) →
    (univ.filter fun y => α y ≠ 0).card = n →
    ∃ α' : ι → ℝ, (∀ y, 0 ≤ α' y) ∧ (∀ y, α y = 0 → α' y = 0) ∧
      ∑ y, α' y • d y = ∑ y, α y • d y ∧
      LinearIndependent ℝ (fun y : {y // y ∈ univ.filter fun y => α' y ≠ 0} => d y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α hα hn
    by_cases hli : LinearIndependent ℝ
        (fun y : {y // y ∈ univ.filter fun y => α y ≠ 0} => d y)
    · exact ⟨α, hα, fun _ h => h, rfl, hli⟩
    · rw [Fintype.linearIndependent_iff] at hli
      push Not at hli
      obtain ⟨g, hg0, i0, hi0⟩ := hli
      let c : ι → ℝ := fun y =>
        if h : y ∈ univ.filter fun y => α y ≠ 0 then g ⟨y, h⟩ else 0
      have hcJ : ∀ i : {y // y ∈ univ.filter fun y => α y ≠ 0}, c i = g i := fun i => by
        simp only [c]
        rw [dite_eq_left_of_eq_true (eq_true i.2)]
      have hcs : ∀ y, α y = 0 → c y = 0 := fun y hy => by
        have hnot : y ∉ univ.filter fun y => α y ≠ 0 := by simp [hy]
        simp only [c]
        rw [dite_eq_right_of_eq_false (eq_false hnot)]
      have hc0 : ∑ y, c y • d y = 0 := by
        rw [← hg0, ← Finset.sum_subset (subset_univ (univ.filter fun y => α y ≠ 0))
            (fun y _ hy => by
              simp only [c]
              rw [dite_eq_right_of_eq_false (eq_false hy), zero_smul]),
          ← Finset.sum_coe_sort (univ.filter fun y => α y ≠ 0) (fun y => c y • d y)]
        exact sum_congr rfl fun i _ => by rw [hcJ i]
      have hstep : ∃ α1 : ι → ℝ, (∀ y, 0 ≤ α1 y) ∧ (∀ y, α y = 0 → α1 y = 0) ∧
          ∑ y, α1 y • d y = ∑ y, α y • d y ∧
          (univ.filter fun y => α1 y ≠ 0).card < (univ.filter fun y => α y ≠ 0).card := by
        rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · refine conic_step d hα (c := fun y => -c y) (fun y hy => by simp [hcs y hy])
            (by simp [hc0]) (y1 := (i0 : ι)) ?_
          show 0 < -c i0
          rw [hcJ i0]
          linarith
        · refine conic_step d hα hcs hc0 (y1 := (i0 : ι)) ?_
          rw [hcJ i0]
          exact hpos
      obtain ⟨α1, h1, h2, h3, h4⟩ := hstep
      rw [hn] at h4
      obtain ⟨α2, k1, k2, k3, k4⟩ := ih _ h4 α1 h1 rfl
      exact ⟨α2, k1, fun y hy => k2 y (h2 y hy), k3.trans h3, k4⟩

/-- **The enumeration succeeds** (`app:known-gauss-info`, "at least one succeeds by conic
Caratheodory applied to an optimal stationarity vector").  If the constraints are strictly
feasible, some active set `J` with linearly independent constraint vectors (hence of size at
most `d = dim E`; possibly empty) has a retained candidate.  By `retained_optimal` that
candidate solves the projection, and by `candidate_unique` it is the only solution of the
linear system of `J` when `M ≻ 0`. -/
theorem active_set_complete (A : E →ₗ[ℝ] F) (d : ι → E) (b : ι → ℝ)
    (hslater : ∃ v, ∀ y, b y < ⟪d y, v⟫) :
    ∃ (J : Finset ι) (v : E) (α : ι → ℝ),
      LinearIndependent ℝ (fun y : {y // y ∈ J} => d y) ∧ J.card ≤ Module.finrank ℝ E ∧
        IsRetained A d b J v α := by
  classical
  -- a minimizer
  obtain ⟨vs, hvs⟩ := hslater
  obtain ⟨v0, hfeas0, hmin0⟩ := exists_min_polyhedron (F := F) (univ : Finset ι) E A 0
    (fun i => innerₗ E (d i)) b ⟨vs, fun i _ => (hvs i).le⟩
  have hfeas : ∀ y, b y ≤ ⟪d y, v0⟫ := fun y => by simpa using hfeas0 y (mem_univ y)
  have hmin : ∀ v, (∀ y, b y ≤ ⟪d y, v⟫) → ‖A v0‖ ≤ ‖A v‖ := fun v hv => by
    have := hmin0 v (fun i _ => by simpa using hv i)
    simpa using this
  -- multipliers
  obtain ⟨α, hα, ν, hν, hval⟩ := quad_dual_strong A d b ⟨vs, hvs⟩ hmin
  have hstatν : ∀ h : E, ∑ y, α y * ⟪d y, h⟫ = ⟪A ν, A h⟫ := by
    intro h
    rw [← LinearMap.adjoint_inner_left, ← hν, sum_inner]
    exact sum_congr rfl fun y _ => by rw [real_inner_smul_left]
  have h1 : ∑ y, α y * b y ≤ ∑ y, α y * ⟪d y, v0⟫ :=
    sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfeas y) (hα y)
  have h2 := hstatν v0
  have hAeq : A ν = A v0 := by
    have h3 := norm_sub_sq_real (A ν) (A v0)
    have h4 : ‖A ν - A v0‖ ^ 2 ≤ 0 := by linarith
    have h5 : ‖A ν - A v0‖ = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h4 (sq_nonneg _))
    exact sub_eq_zero.mp (norm_eq_zero.mp h5)
  have hstat : ∀ h : E, ∑ y, α y * ⟪d y, h⟫ = ⟪A v0, A h⟫ := fun h => by
    rw [hstatν h, hAeq]
  have hslack : ∀ y, α y * (⟪d y, v0⟫ - b y) = 0 := by
    have hnn : ∀ y ∈ (univ : Finset ι), 0 ≤ α y * (⟪d y, v0⟫ - b y) := fun y _ =>
      mul_nonneg (hα y) (sub_nonneg.mpr (hfeas y))
    have hsum : ∑ y, α y * (⟪d y, v0⟫ - b y) = 0 := by
      have e : ∑ y, α y * (⟪d y, v0⟫ - b y) = ∑ y, α y * ⟪d y, v0⟫ - ∑ y, α y * b y := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun y _ => by ring
      have h6 : ⟪A ν, A v0⟫ = ‖A v0‖ ^ 2 := by rw [hAeq, real_inner_self_eq_norm_sq]
      have h7 : ‖A ν‖ = ‖A v0‖ := by rw [hAeq]
      rw [h7] at hval
      refine le_antisymm ?_ (sum_nonneg hnn)
      rw [e]
      linarith
    exact fun y => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum y (mem_univ y)
  -- reduce the support
  obtain ⟨α', hα', hsub, hsum', hli⟩ := conic_caratheodory d _ α hα rfl
  refine ⟨univ.filter fun y => α' y ≠ 0, v0, α', hli, ?_, ⟨?_, ?_, ?_⟩, hα', hfeas⟩
  · have := hli.fintype_card_le_finrank
    rwa [Fintype.card_coe] at this
  · intro y hy
    by_contra hne
    exact hy (mem_filter.mpr ⟨mem_univ y, hne⟩)
  · intro h
    rw [← hstat h]
    have e1 : ∑ y, α' y * ⟪d y, h⟫ = ⟪∑ y, α' y • d y, h⟫ := by
      rw [sum_inner]
      exact sum_congr rfl fun y _ => by rw [real_inner_smul_left]
    have e2 : ∑ y, α y * ⟪d y, h⟫ = ⟪∑ y, α y • d y, h⟫ := by
      rw [sum_inner]
      exact sum_congr rfl fun y _ => by rw [real_inner_smul_left]
    rw [e1, e2, hsum']
  · intro y hy
    have hne : α' y ≠ 0 := (mem_filter.mp hy).2
    have hαne : α y ≠ 0 := fun h0 => hne (hsub y h0)
    have := hslack y
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hαne
    · linarith

end ActiveSet

/-! ### All polynomial moments of the last violation time -/

section Moments

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜] [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]
variable (T : Tracker X ι 𝒜) (hT : T.Meas) (θ : ι → ℝ) {ℓ κ A0 : ℝ}

lemma exp_neg_le_factorial_div {y : ℝ} (hy : 0 < y) (m : ℕ) :
    Real.exp (-y) ≤ (Nat.factorial m : ℝ) / y ^ m := by
  have h := Real.pow_div_factorial_le_exp (x := y) hy.le m
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  have hf : (0 : ℝ) < Nat.factorial m := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h
  linarith

/-- **Concentration with every polynomial rate** (`app:known-gauss-info`, "Tracking,
estimation, and stabilization").  For every `r` there is a constant `C` with
`P(‖θ̂_k - θ‖ > (k+1)^{-1/8}) ≤ C (k+1)^{-r}` for all `k`. -/
theorem bad_poly_all (hV : T.Valid ℓ κ A0) [Nonempty ι] (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, gP (T.bad hT θ k) ≤ ENNReal.ofReal (C / ((k : ℝ) + 1) ^ r) := by
  have hκ := hV.hκ
  have hℓ := hV.hℓ
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = κ ^ 2 / (32 * Fintype.card ι * ℓ ^ 2) := ⟨_, rfl⟩
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ,
      C1 = (Fintype.card ι : ℝ) * (2 * ((Nat.factorial (4 * r) : ℝ) / c0 ^ (4 * r))) := ⟨_, rfl⟩
  have hC1pos : 0 ≤ C1 := by rw [hC1]; positivity
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, k0 = Tracker.onset (Fintype.card X) ℓ κ := ⟨_, rfl⟩
  refine ⟨C1 + ((k0 : ℝ) + 1) ^ r, by positivity, fun k => ?_⟩
  have hkr : (0 : ℝ) < ((k : ℝ) + 1) ^ r := by positivity
  rcases Nat.lt_or_ge k k0 with hlt | hge
  · refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hkr, one_mul]
    have h1 : ((k : ℝ) + 1) ^ r ≤ ((k0 : ℝ) + 1) ^ r := by
      have : (k : ℝ) ≤ k0 := by exact_mod_cast hlt.le
      exact pow_le_pow_left₀ (by positivity) (by linarith) r
    linarith
  · rw [hk0] at hge
    refine (T.bad_exp hT θ hV hge).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hc0]
    have hy : 0 < c0 * rk k ^ 4 := mul_pos hc0pos (pow_pos (rk_pos k) 4)
    have h1 := exp_neg_le_factorial_div hy (4 * r)
    have e48 : (c0 * rk k ^ 4) ^ (4 * r) = c0 ^ (4 * r) * ((k : ℝ) + 1) ^ r := by
      rw [mul_pow, ← pow_mul, ← rk_pow k, ← pow_mul]
      congr 2
      ring
    rw [e48] at h1
    have h2 : (Fintype.card ι : ℝ) * (2 * Real.exp (-(c0 * rk k ^ 4))) ≤
        C1 / ((k : ℝ) + 1) ^ r := by
      rw [hC1]
      have e : (Fintype.card ι : ℝ) * (2 * ((Nat.factorial (4 * r) : ℝ) / c0 ^ (4 * r))) /
          ((k : ℝ) + 1) ^ r =
          (Fintype.card ι : ℝ) * (2 * ((Nat.factorial (4 * r) : ℝ) /
            (c0 ^ (4 * r) * ((k : ℝ) + 1) ^ r))) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num)) hd.le
    refine h2.trans ?_
    exact div_le_div_of_nonneg_right
      (by linarith [pow_pos (by positivity : (0 : ℝ) < (k0 : ℝ) + 1) r]) hkr.le

/-- **The last violation time has all polynomial moments** (`app:known-gauss-info`: "the
last time this inequality is violated therefore has all polynomial moments").  With
`L = sup {j + 1 : ‖θ̂_j - θ‖ > (j+1)^{-1/8}}` (zero if there is no violation),
`L^p = sup_j (j+1)^p 1{violation at j}` and `E_θ L^p < ∞` for every `p`. -/
theorem lastBad_moment (hV : T.Valid ℓ κ A0) [Nonempty ι] (p : ℕ) :
    ∫⁻ ω, ⨆ j : ℕ, (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞) ^ p) ω ∂gP ≠ ⊤ := by
  obtain ⟨C, hC0, hC⟩ := bad_poly_all T hT θ hV (p + 2)
  have hle : ∫⁻ ω, ⨆ j : ℕ, (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞) ^ p) ω ∂gP ≤
      ∫⁻ ω, ∑' j : ℕ, (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞) ^ p) ω ∂gP :=
    lintegral_mono fun ω => iSup_le fun j =>
      le_tsum (fun j : ℕ => (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞) ^ p) ω) j
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_tsum
    (fun j => (measurable_const.indicator (T.measurableSet_bad hT θ j)).aemeasurable)]
  have hterm : ∀ j : ℕ,
      ∫⁻ ω, (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞) ^ p) ω ∂gP ≤
        ENNReal.ofReal (C / ((j : ℝ) + 1) ^ 2) := by
    intro j
    rw [lintegral_indicator_const (T.measurableSet_bad hT θ j)]
    calc ((j + 1 : ℕ) : ℝ≥0∞) ^ p * gP (T.bad hT θ j)
        ≤ ((j + 1 : ℕ) : ℝ≥0∞) ^ p * ENNReal.ofReal (C / ((j : ℝ) + 1) ^ (p + 2)) :=
          mul_le_mul' le_rfl (hC j)
      _ = ENNReal.ofReal (C / ((j : ℝ) + 1) ^ 2) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) _)]
          congr 1
          push_cast
          rw [pow_add, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
          ring
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hterm)
  have hsum : Summable fun j : ℕ => C / ((j : ℝ) + 1) ^ 2 := by
    have h1 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 := ((summable_nat_add_iff 1).mpr h1).mul_left C
    refine h2.congr fun j => ?_
    push_cast
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

end Moments

/-! ### The spanning-dictionary hypothesis from a span condition -/

section Span

variable {X ι 𝒜 Z : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype 𝒜] [Nonempty 𝒜]
  [MeasurableSpace 𝒜] [MeasurableSingletonClass 𝒜] [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **A spanning dictionary has a reference design with `M(w⁰) ⪰ κ I`**: if the query
features span `ℝ^d`, the uniform design `w⁰ = 1/|X|` has `κ ‖e‖² ≤ ∑_x w⁰_x (u_x · e)²` for
some `κ > 0`. -/
theorem exists_kappa_of_span (u : X → ι → ℝ) (hsp : Submodule.span ℝ (Set.range u) = ⊤) :
    (fun _ : X => 1 / (Fintype.card X : ℝ)) ∈ simplex X ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ e : ι → ℝ,
      κ * (e ⬝ᵥ e) ≤ ∑ x, 1 / (Fintype.card X : ℝ) * (u x ⬝ᵥ e) ^ 2 := by
  have hm : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hw0 : (fun _ : X => 1 / (Fintype.card X : ℝ)) ∈ simplex X := by
    refine ⟨fun _ => by positivity, ?_⟩
    rw [sum_const, card_univ, nsmul_eq_mul]
    field_simp
  refine ⟨hw0, ?_⟩
  let uE : X → EuclideanSpace ℝ ι := fun x => WithLp.toLp 2 (u x)
  have hinner : ∀ (x : X) (z : EuclideanSpace ℝ ι), ⟪uE x, z⟫ = u x ⬝ᵥ z.ofLp := by
    intro x z
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [uE, dotProduct_comm]
  have hsq : ∀ z : EuclideanSpace ℝ ι,
      ‖designMap uE (fun _ : X => 1 / (Fintype.card X : ℝ)) z‖ ^ 2 =
        ∑ x, 1 / (Fintype.card X : ℝ) * (u x ⬝ᵥ z.ofLp) ^ 2 := by
    intro z
    rw [norm_designMap_sq uE hw0.1]
    exact sum_congr rfl fun x _ => by rw [hinner]
  have hker : LinearMap.ker (designMap uE (fun _ : X => 1 / (Fintype.card X : ℝ))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    have h0 : ∑ x, 1 / (Fintype.card X : ℝ) * (u x ⬝ᵥ z.ofLp) ^ 2 = 0 := by
      rw [← hsq z, hz, norm_zero]
      norm_num
    have hterm : ∀ x, u x ⬝ᵥ z.ofLp = 0 := by
      intro x
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => by positivity : ∀ x ∈ (univ : Finset X),
          0 ≤ 1 / (Fintype.card X : ℝ) * (u x ⬝ᵥ z.ofLp) ^ 2)).mp h0 x (mem_univ x)
      have hne : (1 / (Fintype.card X : ℝ)) ≠ 0 := by positivity
      exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hne)
    have hall : ∀ w ∈ Submodule.span ℝ (Set.range u), w ⬝ᵥ z.ofLp = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, rfl⟩ := hw
        exact hterm x
      | zero => exact zero_dotProduct _
      | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
      | smul c a _ ha => rw [smul_dotProduct, ha, smul_zero]
    have hself : z.ofLp ⬝ᵥ z.ofLp = 0 := hall _ (by rw [hsp]; exact Submodule.mem_top)
    have hz0 : ‖z‖ ^ 2 = 0 := by
      rw [← hself, ← Tracker.norm_tE_sq z.ofLp]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz0)
  obtain ⟨K, hK0, hK⟩ := LinearMap.exists_antilipschitzWith _ hker
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  refine ⟨1 / (K : ℝ) ^ 2, by positivity, fun e => ?_⟩
  have h1 := hK.le_mul_dist (WithLp.toLp 2 e : EuclideanSpace ℝ ι) 0
  rw [dist_zero_right, map_zero, dist_zero_right] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, Tracker.norm_tE_sq, hsq] at h2
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), mul_comm]
  exact h2

/-- The conclusions (2a)-(2b) of `bay_main_optimal_literal` for a tracker `T`: uniform
correctness, the joint error bound, and at every `θ` with `I_*(θ) > 0` finite expected
stopping time and `E_θ τ_δ / log(1/δ) → 1 / I_*(θ)`. -/
def AttainsLimit (u : X → ι → ℝ) (v : X → ℝ) (φ : Z → EuclideanSpace ℝ ι)
    (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (T : Tracker X ι 𝒜)
    (hT : T.Meas) : Prop :=
  (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
    law (T.sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
      (ansSet (T.sampler hT δ) (T.decision hT δ) a n) ≤ ENNReal.ofReal δ) ∧
  (∀ δ, 0 < δ → δ < 1 → ∀ (lam : EuclideanSpace ℝ ι) (n : ℕ),
    law (T.sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
      (⋃ a ∈ {a : 𝒜 | lam ∈ strictAlt φ (supp a) (hne a) ε},
        ansSet (T.sampler hT δ) (T.decision hT δ) a n) ≤ ENNReal.ofReal δ) ∧
  ∀ θ : ι → ℝ, 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
    (∀ δ, 0 < δ → δ < 1 →
      expTau (T.sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v ≠ ⊤) ∧
    Tendsto (fun δ : ℝ =>
        (expTau (T.sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v).toReal /
          Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ))

/-- **`thm:bay-main-optimal` with the hypothesis "spanning query dictionary" as a span
condition.**  If the whitened query features span `ℝ^d`, then with the uniform reference
design: (1) every uniformly correct family has `liminf E_θ τ_δ / log(1/δ) ≥ 1 / I_*(θ)` at
every `θ` with `I_*(θ) > 0`; (2) for suitable constants the finite-grid tracker is Borel
measurable and attains the limit (`AttainsLimit`). -/
theorem bay_main_optimal_span (u : X → ι → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hsp : Submodule.span ℝ (Set.range u) = ⊤)
    (φ : Z → EuclideanSpace ℝ ι) (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQne : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) :
    (∀ θ : ι → ℝ, 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
      ∀ (S : ℝ → GSampler X) (D : ℝ → GDecision 𝒜),
        (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
          law (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
            (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ) →
        ∀ c : ℝ, c < 1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤
            expTau (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v) ∧
    ∃ (κ ℓ A0 : ℝ)
      (hT : (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε)
        (fun _ : X => 1 / (Fintype.card X : ℝ)) 1 ℓ κ A0).Meas),
      AttainsLimit u v φ supp hne ε
        (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε)
          (fun _ : X => 1 / (Fintype.card X : ℝ)) 1 ℓ κ A0) hT := by
  obtain ⟨hw0, κ, hκ, hspan⟩ := exists_kappa_of_span u hsp
  obtain ⟨h1, ℓ, A0, hT, -, h2⟩ := bay_main_optimal_literal u hv hw0 hκ hspan φ supp hne ε hQne
  exact ⟨h1, κ, ℓ, A0, hT, h2⟩

end Span

end LiteralD1b

end

end JointRootCert
