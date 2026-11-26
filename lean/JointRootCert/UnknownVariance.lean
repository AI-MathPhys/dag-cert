/-
Unknown-variance fixed-feature nuisance-KL results (manuscript subsections
"Unknown-variance fixed-feature nuisance-KL results" and
"Unknown-variance Gaussian tracking: construction and proofs", `app:v34-theory`).

Results covered (see the doc comment of each theorem for what is proved and what is assumed):

* `thm:v34-action-local` (Action-local optional evaluation and intersection-union root
  coverage): `halfCash_integral_le_one`, `localWealth_*`, `localWealth_supermartingale`,
  `intersection_union_coverage`.
* `thm:v34-adaptive` (Sparse four-power nuisance-KL tracking with unknown variances):
  deterministic cores only: `actGame_domination`, `score_error_of_contract`,
  `retained_design_value`, `sticky_stabilization`, `log_halfCash_ge`,
  `log_localWealth_ge`, `wealth_rate`, `lintegral_stopping_le`, `overshoot_bound`,
  `limsup_coefficient`.
* `thm:v34-converse-main` / `thm:v34-converse` (unknown-variance converse, unique correct
  action): `gaussKL_ge_nkl`, `gaussKL_profile_eq`, `transport_closure`,
  `converse_reduction`, `actGame_eq_zero_of_mem`, `tendsto_klBin_div_log`,
  `liminf_coefficient`.
* `prop:v34-work` (Global solver-call reduction): `card_fourPower_refreshes`,
  `designCalls_eq`, `nullSolves_le`, `integral_log_le_log_integral`,
  `expected_designCalls_le`, `expected_nullSolves_le`.
* `lem:v34-transport` (Uniform stability of the nuisance-KL information game):
  `nkl_sub_le`, `actGame_transport`, `actGameStar_transport`, `nuisDist`.
* `lem:v34-batch-comparison` (A uniform batch log-likelihood comparison):
  `profBracket_sub_le`, `batch_comparison`, with the profiling algebra
  `sum_sq_decomp`, `gaussian_profile_le`, `gaussian_profile_eq`, `profBracket_eq_loglik`.
* `lem:v34-concentration` (Explicit intrinsic-tape Gaussian concentration):
  `chi2_threshold_upper`, `chi2_threshold_lower`, `concentration_fixed`,
  `concentration_prefix`.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset MeasureTheory

noncomputable section

/-! ### The nuisance-profiled KL integrand -/

/-- The per-query nuisance-profiled KL information `½ log (1 + (m - t)² / v)`, with query
mean `m`, query variance `v` and alternative mean `t = h_xᵀ u`. -/
def nkl (m v t : ℝ) : ℝ := 1 / 2 * Real.log (1 + (m - t) ^ 2 / v)

lemma nkl_nonneg {v : ℝ} (hv : 0 < v) (m t : ℝ) : 0 ≤ nkl m v t := by
  unfold nkl
  have h0 : 0 ≤ (m - t) ^ 2 / v := by positivity
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + (m - t) ^ 2 / v)
  linarith

lemma nkl_self {v : ℝ} (m : ℝ) : nkl m v m = 0 := by
  simp [nkl]

/-- `a ↦ ½ log (1 + a²)` is `½`-Lipschitz. -/
lemma half_log_one_add_sq_lipschitz (a b : ℝ) :
    |1 / 2 * Real.log (1 + a ^ 2) - 1 / 2 * Real.log (1 + b ^ 2)| ≤ 1 / 2 * |a - b| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 1 / 2 * Real.log (1 + y ^ 2))
      (1 / 2 * ((2 * x) / (1 + x ^ 2))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have hpos : (1 + x ^ 2) ≠ 0 := by positivity
    exact (h1.log hpos).const_mul (1 / 2)
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖1 / 2 * ((2 * x) / (1 + x ^ 2))‖ ≤ 1 / 2 := by
    intro x _
    have hx : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have he : 1 / 2 * ((2 * x) / (1 + x ^ 2)) = x / (1 + x ^ 2) := by ring
    rw [Real.norm_eq_abs, he, abs_le]
    constructor
    · rw [le_div_iff₀ hx]; nlinarith [sq_nonneg (x + 1)]
    · rw [div_le_iff₀ hx]; nlinarith [sq_nonneg (x - 1)]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => 1 / 2 * Real.log (1 + y ^ 2))
    (fun x _ => (hd x).hasDerivWithinAt) hb convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

/-- Lipschitz dependence of the integrand on the query mean, uniformly in `t`:
`|∂ nkl / ∂ m| ≤ 1 / (2 √v)`. -/
lemma nkl_sub_mean_le {v : ℝ} (hv : 0 < v) (m m' t : ℝ) :
    |nkl m v t - nkl m' v t| ≤ |m - m'| / (2 * Real.sqrt v) := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hrw : ∀ a : ℝ, 1 + a ^ 2 / v = 1 + (a / Real.sqrt v) ^ 2 := by
    intro a
    rw [div_pow, Real.sq_sqrt hv.le]
  unfold nkl
  rw [hrw, hrw]
  refine (half_log_one_add_sq_lipschitz _ _).trans (le_of_eq ?_)
  rw [← sub_div, abs_div, abs_of_pos hs]
  have : m - t - (m' - t) = m - m' := by ring
  rw [this]
  field_simp

/-- Dependence of the integrand on the variance: for `v ≤ v'` the integrand decreases by at
most `½ log (v' / v)`. -/
lemma nkl_var_mono {v v' : ℝ} (hv : 0 < v) (hvv : v ≤ v') (m t : ℝ) :
    nkl m v' t ≤ nkl m v t ∧ nkl m v t ≤ nkl m v' t + 1 / 2 * Real.log (v' / v) := by
  have hv' : 0 < v' := lt_of_lt_of_le hv hvv
  set c := (m - t) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have h1 : (0 : ℝ) < 1 + c / v' := by positivity
  have h2 : (0 : ℝ) < 1 + c / v := by positivity
  have hle : 1 + c / v' ≤ 1 + c / v := by
    have : c / v' ≤ c / v := div_le_div_of_nonneg_left hc0 hv hvv
    linarith
  have hle2 : 1 + c / v ≤ (v' / v) * (1 + c / v') := by
    have : (v' / v) * (1 + c / v') = v' / v + c / v := by
      field_simp
    rw [this]
    have : 1 ≤ v' / v := (one_le_div hv).mpr hvv
    linarith
  unfold nkl
  constructor
  · have := Real.log_le_log h1 hle
    linarith
  · have h3 := Real.log_le_log h2 hle2
    rw [Real.log_mul (by positivity) h1.ne'] at h3
    linarith

lemma nkl_sub_var_le {v v' : ℝ} (hv : 0 < v) (hv' : 0 < v') (m t : ℝ) :
    |nkl m v t - nkl m v' t| ≤ 1 / 2 * |Real.log (v / v')| := by
  rcases le_total v v' with h | h
  · obtain ⟨h1, h2⟩ := nkl_var_mono hv h m t
    have hlog : Real.log (v / v') = -Real.log (v' / v) := by
      rw [Real.log_div hv.ne' hv'.ne', Real.log_div hv'.ne' hv.ne']; ring
    have hnn : 0 ≤ Real.log (v' / v) := Real.log_nonneg ((one_le_div hv).mpr h)
    rw [hlog, abs_neg, abs_of_nonneg hnn, abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := nkl_var_mono hv' h m t
    have hnn : 0 ≤ Real.log (v / v') := Real.log_nonneg ((one_le_div hv').mpr h)
    rw [abs_of_nonneg hnn, abs_le]
    constructor <;> linarith

/-- **Coordinate stability bound (core of Lemma `lem:v34-transport`).**  Uniformly in the
alternative mean `t`. -/
lemma nkl_sub_le {v v' : ℝ} (hv : 0 < v) (hv' : 0 < v') (m m' t : ℝ) :
    |nkl m v t - nkl m' v' t| ≤
      |m - m'| / (2 * Real.sqrt (min v v')) + 1 / 2 * |Real.log (v / v')| := by
  have hmin : 0 < min v v' := lt_min hv hv'
  have h1 := nkl_sub_mean_le hv m m' t
  have h2 := nkl_sub_var_le hv hv' m' t
  have h3 : |m - m'| / (2 * Real.sqrt v) ≤ |m - m'| / (2 * Real.sqrt (min v v')) := by
    apply div_le_div_of_nonneg_left (abs_nonneg _)
    · have := Real.sqrt_pos.mpr hmin; positivity
    · have := Real.sqrt_le_sqrt (min_le_left v v')
      linarith
  calc |nkl m v t - nkl m' v' t|
      = |(nkl m v t - nkl m' v t) + (nkl m' v t - nkl m' v' t)| := by ring_nf
    _ ≤ |nkl m v t - nkl m' v t| + |nkl m' v t - nkl m' v' t| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### Non-expansiveness of `inf`, `min`, `sup` under uniform additive perturbations -/

lemma abs_iInf_sub_iInf_le {ι : Sort*} {F G : ι → ℝ} {d c : ℝ} (hd : 0 ≤ d)
    (hF : ∀ i, c ≤ F i) (hG : ∀ i, c ≤ G i) (h : ∀ i, |F i - G i| ≤ d) :
    |(⨅ i, F i) - ⨅ i, G i| ≤ d := by
  rcases isEmpty_or_nonempty ι with he | hne
  · simp [hd]
  · have hFb : BddBelow (Set.range F) := ⟨c, by rintro _ ⟨i, rfl⟩; exact hF i⟩
    have hGb : BddBelow (Set.range G) := ⟨c, by rintro _ ⟨i, rfl⟩; exact hG i⟩
    have h1 : (⨅ i, G i) - d ≤ ⨅ i, F i :=
      le_ciInf fun i => by
        have := ciInf_le hGb i
        have := (abs_le.mp (h i)).1
        linarith
    have h2 : (⨅ i, F i) - d ≤ ⨅ i, G i :=
      le_ciInf fun i => by
        have := ciInf_le hFb i
        have := (abs_le.mp (h i)).2
        linarith
    rw [abs_le]; constructor <;> linarith

lemma abs_inf'_sub_inf'_le {Z : Type*} (J : Finset Z) (hJ : J.Nonempty) {F G : Z → ℝ} {d : ℝ}
    (h : ∀ z ∈ J, |F z - G z| ≤ d) : |J.inf' hJ F - J.inf' hJ G| ≤ d := by
  obtain ⟨zF, hzF, hF⟩ := Finset.exists_mem_eq_inf' hJ F
  obtain ⟨zG, hzG, hG⟩ := Finset.exists_mem_eq_inf' hJ G
  have h1 : J.inf' hJ G ≤ G zF := Finset.inf'_le _ hzF
  have h2 : J.inf' hJ F ≤ F zG := Finset.inf'_le _ hzG
  have h3 := abs_le.mp (h zF hzF)
  have h4 := abs_le.mp (h zG hzG)
  rw [abs_le]; constructor <;> linarith

lemma abs_iSup_sub_iSup_le {ι : Sort*} [Nonempty ι] {F G : ι → ℝ} {d : ℝ}
    (hF : BddAbove (Set.range F)) (hG : BddAbove (Set.range G)) (h : ∀ i, |F i - G i| ≤ d) :
    |(⨆ i, F i) - ⨆ i, G i| ≤ d := by
  have h1 : (⨆ i, F i) ≤ (⨆ i, G i) + d :=
    ciSup_le fun i => by
      have := le_ciSup hG i
      have := (abs_le.mp (h i)).2
      linarith
  have h2 : (⨆ i, G i) ≤ (⨆ i, F i) + d :=
    ciSup_le fun i => by
      have := le_ciSup hF i
      have := (abs_le.mp (h i)).1
      linarith
  rw [abs_le]; constructor <;> linarith

/-! ### The nuisance-KL information game (`eq:v34-general-game`) -/

section Game

variable {X : Type*} [Fintype X] {U : Type*} {Z : Type*}

/-- The weighted objective `½ ∑ₓ wₓ log (1 + (mₓ - hₓᵀu)² / vₓ)`; `pred x u` stands for
`hₓᵀ u` (no linearity is needed for the results below). -/
def nklObj (pred : X → U → ℝ) (w m v : X → ℝ) (u : U) : ℝ :=
  ∑ x, w x * nkl (m x) (v x) (pred x u)

/-- The component game `C_{a,z}(w; m, v) = inf_{u ∈ H} nklObj`.  For an empty `H` the real
infimum is `0` by Lean convention (the manuscript's value would be `+∞`); results that depend
on this assume `H.Nonempty`. -/
def compGame (H : Set U) (pred : X → U → ℝ) (w m v : X → ℝ) : ℝ :=
  ⨅ u : H, nklObj pred w m v u

/-- The action game `C_a(w; m, v) = min_{z ∈ J_a} C_{a,z}(w; m, v)`. -/
def actGame (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U) (pred : X → U → ℝ)
    (w m v : X → ℝ) : ℝ :=
  J.inf' hJ fun z => compGame (H z) pred w m v

/-- The optimal-design value `C_a^*(m, v) = max_{w ∈ Δ} C_a(w; m, v)` (as a supremum). -/
def actGameStar (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U) (pred : X → U → ℝ)
    (m v : X → ℝ) : ℝ :=
  ⨆ w : simplex X, actGame J hJ H pred w m v

/-- The perturbation size `d(m, v; m', v')` of Lemma `lem:v34-transport`. -/
def nuisDist [Nonempty X] (m v m' v' : X → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun x =>
    |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) + 1 / 2 * |Real.log (v x / v' x)|

lemma le_nuisDist [Nonempty X] (m v m' v' : X → ℝ) (x : X) :
    |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) + 1 / 2 * |Real.log (v x / v' x)| ≤
      nuisDist m v m' v' :=
  Finset.le_sup' (fun x =>
    |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) + 1 / 2 * |Real.log (v x / v' x)|)
    (mem_univ x)

lemma nuisDist_nonneg [Nonempty X] (m v m' v' : X → ℝ) : 0 ≤ nuisDist m v m' v' := by
  obtain ⟨x⟩ := ‹Nonempty X›
  refine le_trans ?_ (le_nuisDist m v m' v' x)
  positivity

lemma nklObj_nonneg {pred : X → U → ℝ} {w m v : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hv : ∀ x, 0 < v x) (u : U) : 0 ≤ nklObj pred w m v u :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (nkl_nonneg (hv x) _ _)

lemma compGame_nonneg {H : Set U} {pred : X → U → ℝ} {w m v : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hv : ∀ x, 0 < v x) : 0 ≤ compGame H pred w m v :=
  Real.iInf_nonneg fun u : H => nklObj_nonneg (pred := pred) hw hv (u : U)

lemma compGame_le {H : Set U} {pred : X → U → ℝ} {w m v : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hv : ∀ x, 0 < v x) {u : U} (hu : u ∈ H) : compGame H pred w m v ≤ nklObj pred w m v u :=
  ciInf_le (f := fun u : H => nklObj pred w m v (u : U))
    ⟨0, by rintro _ ⟨u, rfl⟩; exact nklObj_nonneg (pred := pred) hw hv (u : U)⟩ (⟨u, hu⟩ : H)

lemma le_compGame {H : Set U} (hH : H.Nonempty) {pred : X → U → ℝ} {w m v : X → ℝ} {c : ℝ}
    (h : ∀ u ∈ H, c ≤ nklObj pred w m v u) : c ≤ compGame H pred w m v := by
  have : Nonempty H := hH.to_subtype
  exact le_ciInf fun u => h u u.2

lemma actGame_nonneg {J : Finset Z} {hJ : J.Nonempty} {H : Z → Set U} {pred : X → U → ℝ}
    {w m v : X → ℝ} (hw : ∀ x, 0 ≤ w x) (hv : ∀ x, 0 < v x) :
    0 ≤ actGame J hJ H pred w m v :=
  (Finset.le_inf'_iff _ _).mpr fun _ _ => compGame_nonneg hw hv

/-- The objective changes by at most `d` under a `d`-perturbation of means and variances,
uniformly in `u`. -/
lemma nklObj_transport {pred : X → U → ℝ} {w m v m' v' : X → ℝ} {d : ℝ}
    (hw : w ∈ simplex X) (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x)
    (hd : ∀ x, |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) +
      1 / 2 * |Real.log (v x / v' x)| ≤ d) (u : U) :
    |nklObj pred w m v u - nklObj pred w m' v' u| ≤ d := by
  unfold nklObj
  rw [← Finset.sum_sub_distrib]
  calc |∑ x, (w x * nkl (m x) (v x) (pred x u) - w x * nkl (m' x) (v' x) (pred x u))|
      ≤ ∑ x, |w x * nkl (m x) (v x) (pred x u) - w x * nkl (m' x) (v' x) (pred x u)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, w x * d := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw.1 x)]
        exact mul_le_mul_of_nonneg_left
          ((nkl_sub_le (hv x) (hv' x) _ _ _).trans (hd x)) (hw.1 x)
    _ = d := by rw [← Finset.sum_mul, hw.2, one_mul]

lemma compGame_transport [Nonempty X] {H : Set U} {pred : X → U → ℝ} {w m v m' v' : X → ℝ}
    {d : ℝ} (hw : w ∈ simplex X) (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x)
    (hd : ∀ x, |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) +
      1 / 2 * |Real.log (v x / v' x)| ≤ d) :
    |compGame H pred w m v - compGame H pred w m' v'| ≤ d := by
  have hd0 : 0 ≤ d := by
    obtain ⟨x⟩ := ‹Nonempty X›
    refine le_trans ?_ (hd x)
    positivity
  exact abs_iInf_sub_iInf_le (F := fun u : H => nklObj pred w m v (u : U))
    (G := fun u : H => nklObj pred w m' v' (u : U)) (c := 0) hd0
    (fun u => nklObj_nonneg (pred := pred) hw.1 hv (u : U))
    (fun u => nklObj_nonneg (pred := pred) hw.1 hv' (u : U))
    (fun u => nklObj_transport (pred := pred) hw hv hv' hd (u : U))

/-- **Uniform stability of the nuisance-KL information game, first inequality
(Lemma `lem:v34-transport`).**  For every design `w` in the simplex,
`|C_a(w; m, v) - C_a(w; m', v')| ≤ d` whenever `d` dominates every coordinate term; in
particular for `d = nuisDist m v m' v'`.  No compactness of the invalidating sets is used. -/
theorem actGame_transport [Nonempty X] (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {w m v m' v' : X → ℝ} {d : ℝ} (hw : w ∈ simplex X)
    (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x)
    (hd : ∀ x, |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) +
      1 / 2 * |Real.log (v x / v' x)| ≤ d) :
    |actGame J hJ H pred w m v - actGame J hJ H pred w m' v'| ≤ d :=
  abs_inf'_sub_inf'_le J hJ fun _ _ => compGame_transport hw hv hv' hd

/-- The action game is bounded above over the simplex. -/
lemma actGame_bddAbove (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {m v : X → ℝ} (hv : ∀ x, 0 < v x) :
    BddAbove (Set.range fun w : simplex X => actGame J hJ H pred w m v) := by
  obtain ⟨z0, hz0⟩ := hJ
  by_cases hne : (H z0).Nonempty
  · obtain ⟨u0, hu0⟩ := hne
    refine ⟨∑ x, nkl (m x) (v x) (pred x u0), ?_⟩
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    refine (Finset.inf'_le _ hz0).trans ((compGame_le hw.1 hv hu0).trans ?_)
    refine Finset.sum_le_sum fun x _ => ?_
    have hwx : w x ≤ 1 := by
      rw [← hw.2]
      exact Finset.single_le_sum (fun y _ => hw.1 y) (mem_univ x)
    exact mul_le_of_le_one_left (nkl_nonneg (hv x) _ _) hwx
  · refine ⟨0, ?_⟩
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    refine (Finset.inf'_le _ hz0).trans (le_of_eq ?_)
    have : IsEmpty (H z0) := Set.isEmpty_coe_sort.mpr (Set.not_nonempty_iff_eq_empty.mp hne)
    exact Real.iInf_of_isEmpty _

lemma actGame_le_star (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {w m v : X → ℝ} (hw : w ∈ simplex X) (hv : ∀ x, 0 < v x) :
    actGame J hJ H pred w m v ≤ actGameStar J hJ H pred m v :=
  le_ciSup (actGame_bddAbove J hJ H pred hv) (⟨w, hw⟩ : simplex X)

/-- **Uniform stability of the nuisance-KL information game, second inequality
(Lemma `lem:v34-transport`).**  `|C_a^*(m, v) - C_a^*(m', v')| ≤ d`. -/
theorem actGameStar_transport [Nonempty X] [DecidableEq X] (J : Finset Z) (hJ : J.Nonempty)
    (H : Z → Set U) (pred : X → U → ℝ) {m v m' v' : X → ℝ} {d : ℝ}
    (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x)
    (hd : ∀ x, |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) +
      1 / 2 * |Real.log (v x / v' x)| ≤ d) :
    |actGameStar J hJ H pred m v - actGameStar J hJ H pred m' v'| ≤ d := by
  obtain ⟨x0⟩ := ‹Nonempty X›
  have : Nonempty (simplex X) := ⟨⟨_, single_mem_simplex x0⟩⟩
  exact abs_iSup_sub_iSup_le (actGame_bddAbove J hJ H pred hv)
    (actGame_bddAbove J hJ H pred hv') fun w => actGame_transport J hJ H pred w.2 hv hv' hd

/-- Lemma `lem:v34-transport` in the manuscript's form, with `d = nuisDist`. -/
theorem transport_nuisDist [Nonempty X] [DecidableEq X] (J : Finset Z) (hJ : J.Nonempty)
    (H : Z → Set U) (pred : X → U → ℝ) {m v m' v' : X → ℝ}
    (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) :
    (∀ w ∈ simplex X, |actGame J hJ H pred w m v - actGame J hJ H pred w m' v'| ≤
        nuisDist m v m' v') ∧
      |actGameStar J hJ H pred m v - actGameStar J hJ H pred m' v'| ≤ nuisDist m v m' v' :=
  ⟨fun _ hw => actGame_transport J hJ H pred hw hv hv' (le_nuisDist m v m' v'),
    actGameStar_transport J hJ H pred hv hv' (le_nuisDist m v m' v')⟩

end Game

/-! ### Batch log-likelihood comparison (Lemma `lem:v34-batch-comparison`) -/

/-- `L₀ = 40 (1 + v_min⁻¹ + v_min^{-1/2})`. -/
def L0 (vmin : ℝ) : ℝ := 40 * (1 + vmin⁻¹ + (Real.sqrt vmin)⁻¹)

lemma L0_pos {vmin : ℝ} (h : 0 < vmin) : 0 < L0 vmin := by
  unfold L0
  have := Real.sqrt_pos.mpr h
  positivity

/-- The per-query bracket in the proof of Lemma `lem:v34-batch-comparison`:
`log ((v̌ + (Ȳ - t)²) / v̂) + 1 - (v̌ + (Ȳ - μ̂)²) / v̂`, with within-batch mean `Ȳ`, within-batch
centered variance `v̌`, predictable estimates `μ̂, v̂`, and alternative mean `t = hₓᵀ u`. -/
def profBracket (ybar vchk muh vh t : ℝ) : ℝ :=
  Real.log ((vchk + (ybar - t) ^ 2) / vh) + 1 - (vchk + (ybar - muh) ^ 2) / vh

/-- At the true mean and variance the bracket is twice the nuisance-KL integrand. -/
lemma profBracket_ideal {v : ℝ} (hv : 0 < v) (μ t : ℝ) :
    profBracket μ v μ v t = 2 * nkl μ v t := by
  unfold profBracket nkl
  have h1 : (v + (μ - t) ^ 2) / v = 1 + (μ - t) ^ 2 / v := by field_simp
  have h2 : (v + (μ - μ) ^ 2) / v = 1 := by
    rw [sub_self]; field_simp; ring
  rw [h1, h2]; ring

lemma abs_log_sub_log_le {x y lo : ℝ} (hlo : 0 < lo) (hx : lo ≤ x) (hy : lo ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / lo := by
  have key : ∀ a b : ℝ, lo ≤ a → lo ≤ b → Real.log a - Real.log b ≤ |a - b| / lo := by
    intro a b ha hb
    have ha0 : 0 < a := lt_of_lt_of_le hlo ha
    have hb0 : 0 < b := lt_of_lt_of_le hlo hb
    have h1 : Real.log a - Real.log b = Real.log (a / b) :=
      (Real.log_div ha0.ne' hb0.ne').symm
    have h2 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have h3 : a / b - 1 = (a - b) / b := by field_simp
    have h4 : (a - b) / b ≤ |a - b| / lo :=
      calc (a - b) / b ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
        _ ≤ |a - b| / lo := div_le_div_of_nonneg_left (abs_nonneg _) hlo hb
    linarith
  rw [abs_le]; constructor
  · have := key y x hy hx
    rw [abs_sub_comm] at this
    linarith
  · exact key x y hx hy

lemma abs_log_add_sq_sub_le {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    |Real.log (s + a ^ 2) - Real.log (s + b ^ 2)| ≤ |a - b| / Real.sqrt s := by
  have hrw : ∀ c : ℝ, Real.log (s + c ^ 2) = Real.log s + 2 * nkl c s 0 := by
    intro c
    unfold nkl
    have : s + c ^ 2 = s * (1 + (c - 0) ^ 2 / s) := by field_simp; ring
    rw [this, Real.log_mul hs.ne' (by positivity)]
    ring
  have h := nkl_sub_mean_le hs a b 0
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  rw [hrw, hrw]
  have e : Real.log s + 2 * nkl a s 0 - (Real.log s + 2 * nkl b s 0) =
      2 * (nkl a s 0 - nkl b s 0) := by ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have e2 : |a - b| / Real.sqrt s = 2 * (|a - b| / (2 * Real.sqrt s)) := by field_simp
  rw [e2]
  linarith

/-- **Bracket deviation (core of Lemma `lem:v34-batch-comparison`).**  If the batch mean, batch
centered variance and the predictable estimates are within `ρ ≤ min {1, v_min / 8}` of the
truth, the bracket deviates from its ideal value `2 nkl` by at most `2 L₀ ρ`, uniformly over
the (unbounded) alternative mean `t`. -/
theorem profBracket_sub_le {vmin v μ ρ ybar vchk muh vh : ℝ} (hvmin : 0 < vmin)
    (hv : vmin ≤ v) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρv : ρ ≤ vmin / 8)
    (h1 : |ybar - μ| ≤ ρ) (h2 : |vchk - v| ≤ ρ) (h3 : |muh - μ| ≤ ρ) (h4 : |vh - v| ≤ ρ)
    (t : ℝ) :
    |profBracket ybar vchk muh vh t - 2 * nkl μ v t| ≤ 2 * L0 vmin * ρ := by
  have hv0 : 0 < v := lt_of_lt_of_le hvmin hv
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  obtain ⟨h4a, h4b⟩ := abs_le.mp h4
  have hlo : 0 < vmin / 2 := by positivity
  have hs : vmin / 2 ≤ vchk := by linarith
  have hvh : vmin / 2 ≤ vh := by linarith
  have hs0 : 0 < vchk := lt_of_lt_of_le hlo hs
  have hvh0 : 0 < vh := lt_of_lt_of_le hlo hvh
  set a := ybar - t with ha
  set b := μ - t with hb
  have hsqv : 0 < Real.sqrt vmin := Real.sqrt_pos.mpr hvmin
  have e1 : profBracket ybar vchk muh vh t =
      Real.log (vchk + a ^ 2) - Real.log vh + 1 - (vchk + (ybar - muh) ^ 2) / vh := by
    unfold profBracket
    rw [Real.log_div (by positivity) hvh0.ne']
  have e2 : 2 * nkl μ v t = Real.log (v + b ^ 2) - Real.log v := by
    unfold nkl
    have : 1 + (μ - t) ^ 2 / v = (v + b ^ 2) / v := by rw [hb]; field_simp
    rw [this, Real.log_div (by positivity) hv0.ne']
    ring
  -- T1
  have hsq : Real.sqrt vmin / 2 ≤ Real.sqrt vchk := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hvmin.le]
    linarith
  have T1 : |Real.log (vchk + a ^ 2) - Real.log (vchk + b ^ 2)| ≤ ρ / (Real.sqrt vmin / 2) := by
    refine (abs_log_add_sq_sub_le hs0 a b).trans ?_
    have : a - b = ybar - μ := by simp only [ha, hb]; ring
    rw [this]
    exact div_le_div₀ hρ0 h1 (by positivity) hsq
  -- T2
  have T2 : |Real.log (vchk + b ^ 2) - Real.log (v + b ^ 2)| ≤ ρ / (vmin / 2) := by
    refine (abs_log_sub_log_le hlo (by nlinarith [sq_nonneg b])
      (by nlinarith [sq_nonneg b])).trans ?_
    have : vchk + b ^ 2 - (v + b ^ 2) = vchk - v := by ring
    rw [this]
    exact div_le_div_of_nonneg_right h2 hlo.le
  -- T3
  have T3 : |Real.log vh - Real.log v| ≤ ρ / (vmin / 2) :=
    (abs_log_sub_log_le hlo hvh (by linarith)).trans (div_le_div_of_nonneg_right h4 hlo.le)
  -- T4
  have T4 : |(vchk + (ybar - muh) ^ 2) / vh - 1| ≤ 6 * ρ / (vmin / 2) := by
    have e : (vchk + (ybar - muh) ^ 2) / vh - 1 = (vchk - vh + (ybar - muh) ^ 2) / vh := by
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hvh0]
    have hd1 : ybar - muh ≤ 2 * ρ := by linarith
    have hd2 : -(2 * ρ) ≤ ybar - muh := by linarith
    have hd : (ybar - muh) ^ 2 ≤ 4 * ρ := by nlinarith
    have hnum : |vchk - vh + (ybar - muh) ^ 2| ≤ 6 * ρ := by
      rw [abs_le]; constructor
      · nlinarith [sq_nonneg (ybar - muh)]
      · linarith
    exact div_le_div₀ (by positivity) hnum hlo hvh
  have r1 : ρ / (Real.sqrt vmin / 2) = 2 * (ρ * (Real.sqrt vmin)⁻¹) := by field_simp
  have r2 : ρ / (vmin / 2) = 2 * (ρ * vmin⁻¹) := by field_simp
  have r3 : 6 * ρ / (vmin / 2) = 12 * (ρ * vmin⁻¹) := by field_simp; ring
  rw [r1] at T1
  rw [r2] at T2 T3
  rw [r3] at T4
  have p1 : 0 ≤ ρ * (Real.sqrt vmin)⁻¹ := by positivity
  have p2 : 0 ≤ ρ * vmin⁻¹ := by positivity
  obtain ⟨T1a, T1b⟩ := abs_le.mp T1
  obtain ⟨T2a, T2b⟩ := abs_le.mp T2
  obtain ⟨T3a, T3b⟩ := abs_le.mp T3
  obtain ⟨T4a, T4b⟩ := abs_le.mp T4
  have hR : 2 * L0 vmin * ρ = 80 * ρ + 80 * (ρ * vmin⁻¹) + 80 * (ρ * (Real.sqrt vmin)⁻¹) := by
    unfold L0; ring
  rw [e1, e2, hR, abs_le]
  constructor <;> linarith

section Batch

variable {X : Type*} [Fintype X] {U : Type*}

/-- The profiled batch statistic: the infimum over the component null of
`½ ∑ₓ w̃ₓ profBracket`.  By maximum-likelihood profiling of the null variances this is
`R⁻¹ log (q(Y) / U_{a,z}(Y))`; the per-query algebra behind that identification is
`sum_sq_decomp`, `gaussian_profile_le`, `gaussian_profile_eq`, `profBracket_eq_loglik`. -/
def profStat (H : Set U) (pred : X → U → ℝ) (w ybar vchk muh vh : X → ℝ) : ℝ :=
  ⨅ u : H, ∑ x, w x * (1 / 2 * profBracket (ybar x) (vchk x) (muh x) (vh x) (pred x (u : U)))

/-- **A uniform batch log-likelihood comparison (Lemma `lem:v34-batch-comparison`).**
Stated for the profiled statistic `profStat` (the manuscript's `R⁻¹ log (q / U)` after
profiling the null variances): if all batch means, batch centered variances and predictable
estimates are within `ρ ≤ min {1, v_min / 8}` of the truth, then
`|profStat - C_{a,z}(w̃; μ, v)| ≤ L₀ ρ`.  The identification of `profStat` with
`R⁻¹ log (q / U)` (interchange of the supremum over null variances with the product over query
types) is not formalized as a single statement. -/
theorem batch_comparison (H : Set U) (pred : X → U → ℝ) {w μ v ybar vchk muh vh : X → ℝ}
    {vmin ρ : ℝ} (hw : w ∈ simplex X) (hvmin : 0 < vmin) (hv : ∀ x, vmin ≤ v x)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρv : ρ ≤ vmin / 8)
    (h1 : ∀ x, |ybar x - μ x| ≤ ρ) (h2 : ∀ x, |vchk x - v x| ≤ ρ)
    (h3 : ∀ x, |muh x - μ x| ≤ ρ) (h4 : ∀ x, |vh x - v x| ≤ ρ) :
    |profStat H pred w ybar vchk muh vh - compGame H pred w μ v| ≤ L0 vmin * ρ := by
  have hv0 : ∀ x, 0 < v x := fun x => lt_of_lt_of_le hvmin (hv x)
  have hd0 : 0 ≤ L0 vmin * ρ := mul_nonneg (L0_pos hvmin).le hρ0
  have hpt : ∀ u : U,
      |(∑ x, w x * (1 / 2 * profBracket (ybar x) (vchk x) (muh x) (vh x) (pred x u))) -
        nklObj pred w μ v u| ≤ L0 vmin * ρ := by
    intro u
    unfold nklObj
    rw [← Finset.sum_sub_distrib]
    calc |∑ x, (w x * (1 / 2 * profBracket (ybar x) (vchk x) (muh x) (vh x) (pred x u)) -
            w x * nkl (μ x) (v x) (pred x u))|
        ≤ ∑ x, |w x * (1 / 2 * profBracket (ybar x) (vchk x) (muh x) (vh x) (pred x u)) -
            w x * nkl (μ x) (v x) (pred x u)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, w x * (L0 vmin * ρ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have hb := profBracket_sub_le hvmin (hv x) hρ0 hρ1 hρv (h1 x) (h2 x) (h3 x) (h4 x)
            (pred x u)
          have e : w x * (1 / 2 * profBracket (ybar x) (vchk x) (muh x) (vh x) (pred x u)) -
              w x * nkl (μ x) (v x) (pred x u) =
              w x * (1 / 2 * (profBracket (ybar x) (vchk x) (muh x) (vh x) (pred x u) -
                2 * nkl (μ x) (v x) (pred x u))) := by ring
          rw [e, abs_mul, abs_of_nonneg (hw.1 x), abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left (by linarith) (hw.1 x)
      _ = L0 vmin * ρ := by rw [← Finset.sum_mul, hw.2, one_mul]
  exact abs_iInf_sub_iInf_le
    (F := fun u : H => ∑ x, w x *
      (1 / 2 * profBracket (ybar x) (vchk x) (muh x) (vh x) (pred x (u : U))))
    (G := fun u : H => nklObj pred w μ v (u : U)) (c := -(L0 vmin * ρ)) hd0
    (fun u => by
      have := (abs_le.mp (hpt (u : U))).1
      have := nklObj_nonneg (pred := pred) (m := μ) hw.1 hv0 (u : U)
      linarith)
    (fun u => by
      have := nklObj_nonneg (pred := pred) (m := μ) hw.1 hv0 (u : U)
      linarith)
    (fun u => hpt (u : U))

end Batch

/-- Sum-of-squares decomposition of a batch about its empirical mean: with `Ȳ` the mean and
`v̌` the centered variance (denominator `n`), `∑ (yᵢ - t)² = n (v̌ + (Ȳ - t)²)`. -/
lemma sum_sq_decomp {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) (t : ℝ) :
    ∑ i ∈ s, (y i - t) ^ 2 =
      (s.card : ℝ) * ((∑ i ∈ s, (y i - (∑ i ∈ s, y i) / s.card) ^ 2) / s.card +
        ((∑ i ∈ s, y i) / s.card - t) ^ 2) := by
  have hn : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hs).ne'
  set ybar := (∑ i ∈ s, y i) / s.card with hy
  have h0 : ∑ i ∈ s, (y i - ybar) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hy]
    field_simp
    ring
  have hexp : ∀ i, (y i - t) ^ 2 =
      (y i - ybar) ^ 2 + 2 * (ybar - t) * (y i - ybar) + (ybar - t) ^ 2 := by
    intro i; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0, Finset.sum_const,
    nsmul_eq_mul]
  field_simp
  ring

/-- Profiling a Gaussian variance: for mean square `S > 0`, every variance `σ² > 0` has
per-observation log-likelihood at most the profiled value `-½ (log 2π + 1) - ½ log S`. -/
lemma gaussian_profile_le {S σ2 : ℝ} (hS : 0 < S) (hσ : 0 < σ2) :
    -(1 / 2) * Real.log (2 * Real.pi * σ2) - S / (2 * σ2) ≤
      -(1 / 2) * (Real.log (2 * Real.pi) + 1) - 1 / 2 * Real.log S := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [Real.log_mul hpi.ne' hσ.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hS hσ)
  rw [Real.log_div hS.ne' hσ.ne'] at h
  have e : S / (2 * σ2) = 1 / 2 * (S / σ2) := by field_simp
  rw [e]
  linarith

/-- The profiled value is attained at `σ² = S`. -/
lemma gaussian_profile_eq {S : ℝ} (hS : 0 < S) :
    -(1 / 2) * Real.log (2 * Real.pi * S) - S / (2 * S) =
      -(1 / 2) * (Real.log (2 * Real.pi) + 1) - 1 / 2 * Real.log S := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [Real.log_mul hpi.ne' hS.ne']
  have e : S / (2 * S) = 1 / 2 := by field_simp
  rw [e]
  ring

/-- The half-bracket is the per-observation difference between the plug-in Gaussian
log-density (mean `μ̂`, variance `v̂`) and the variance-profiled null log-likelihood at mean
`t`, after `sum_sq_decomp`. -/
lemma profBracket_eq_loglik {ybar vchk muh vh t : ℝ} (hvchk : 0 < vchk) (hvh : 0 < vh) :
    (-(1 / 2) * Real.log (2 * Real.pi * vh) - (vchk + (ybar - muh) ^ 2) / (2 * vh)) -
      (-(1 / 2) * (Real.log (2 * Real.pi) + 1) -
        1 / 2 * Real.log (vchk + (ybar - t) ^ 2)) =
      1 / 2 * profBracket ybar vchk muh vh t := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  unfold profBracket
  rw [Real.log_mul hpi.ne' hvh.ne', Real.log_div (by positivity) hvh.ne']
  have e : (vchk + (ybar - muh) ^ 2) / (2 * vh) = 1 / 2 * ((vchk + (ybar - muh) ^ 2) / vh) := by
    field_simp
  rw [e]
  ring

/-! ### Action-local wealth and intersection-union coverage (Theorem `thm:v34-action-local`) -/

/-- The half-cash profiled-likelihood e-factor `F = ½ (1 + q̲ / Ū)`. -/
def halfCash (qlo Uhi : ℝ) : ℝ := 1 / 2 * (1 + qlo / Uhi)

lemma halfCash_ge_half {qlo Uhi : ℝ} (hq : 0 ≤ qlo) (hU : 0 ≤ Uhi) :
    1 / 2 ≤ halfCash qlo Uhi := by
  unfold halfCash
  have : 0 ≤ qlo / Uhi := div_nonneg hq hU
  linarith

/-- **One-step e-factor bound.**  Let `p` be the true conditional batch density (with respect
to a reference measure `ν`) under a component null, `q` a proper predictable density,
`qlo ≤ q` a verified lower bound and `Uhi ≥ p` a verified upper bound on the null likelihood
supremum.  Then the conditional expectation of the half-cash factor is at most one.  Only the
two outward enclosure directions are used. -/
theorem halfCash_integral_le_one {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {p q qlo Uhi : Y → ℝ} (hp0 : ∀ y, 0 ≤ p y) (hpint : Integrable p ν)
    (hp1 : ∫ y, p y ∂ν = 1) (hqint : Integrable q ν) (hq1 : ∫ y, q y ∂ν ≤ 1)
    (hqlo0 : ∀ y, 0 ≤ qlo y) (hqlo : ∀ y, qlo y ≤ q y) (hU : ∀ y, p y ≤ Uhi y)
    (hmeas : AEStronglyMeasurable (fun y => p y * (qlo y / Uhi y)) ν) :
    ∫ y, p y * halfCash (qlo y) (Uhi y) ∂ν ≤ 1 := by
  have hU0 : ∀ y, 0 ≤ Uhi y := fun y => (hp0 y).trans (hU y)
  have hnn : ∀ y, 0 ≤ p y * (qlo y / Uhi y) := fun y =>
    mul_nonneg (hp0 y) (div_nonneg (hqlo0 y) (hU0 y))
  have hle : ∀ y, p y * (qlo y / Uhi y) ≤ q y := by
    intro y
    refine le_trans ?_ (hqlo y)
    rcases (hU0 y).eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using hqlo0 y
    · rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith [hqlo0 y, hU y, hp0 y]
  have hint : Integrable (fun y => p y * (qlo y / Uhi y)) ν :=
    hqint.mono' hmeas (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]; exact hle y)
  have h2 : ∫ y, p y * (qlo y / Uhi y) ∂ν ≤ 1 :=
    (integral_mono hint hqint hle).trans hq1
  have heq : (fun y => p y * halfCash (qlo y) (Uhi y)) =
      fun y => 1 / 2 * p y + 1 / 2 * (p y * (qlo y / Uhi y)) := by
    funext y; unfold halfCash; ring
  rw [heq, integral_add (hpint.const_mul _) (hint.const_mul _), integral_const_mul,
    integral_const_mul, hp1]
  linarith

/-- The action-local predictably skipped wealth `E^loc_{a,z}(j)` (`eq:v34-action-local`):
the product over batches `1, …, j` of the factor `F i` when action `a` is selected at batch
`i`, and of `1` otherwise. -/
def localWealth {A : Type*} [DecidableEq A] (F : ℕ → ℝ) (sel : ℕ → A) (a : A) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 j, if sel i = a then F i else 1

section LocalWealth

variable {A : Type*} [DecidableEq A]

@[simp] lemma localWealth_zero (F : ℕ → ℝ) (sel : ℕ → A) (a : A) : localWealth F sel a 0 = 1 := by
  simp [localWealth]

lemma localWealth_succ (F : ℕ → ℝ) (sel : ℕ → A) (a : A) (j : ℕ) :
    localWealth F sel a (j + 1) =
      localWealth F sel a j * (if sel (j + 1) = a then F (j + 1) else 1) := by
  unfold localWealth
  rw [Finset.prod_Icc_succ_top (by omega)]

/-- Wealth is resumed, never reset: a batch on which `a` is not selected leaves it unchanged. -/
lemma localWealth_skip (F : ℕ → ℝ) (sel : ℕ → A) (a : A) (j : ℕ) (h : sel (j + 1) ≠ a) :
    localWealth F sel a (j + 1) = localWealth F sel a j := by
  simp [localWealth_succ, h]

lemma localWealth_pos {F : ℕ → ℝ} {sel : ℕ → A} {a : A} {j : ℕ}
    (hF : ∀ i ∈ Finset.Icc 1 j, sel i = a → 0 < F i) : 0 < localWealth F sel a j := by
  unfold localWealth
  refine Finset.prod_pos fun i hi => ?_
  split_ifs with h
  · exact hF i hi h
  · exact one_pos

lemma localWealth_nonneg {F : ℕ → ℝ} {sel : ℕ → A} {a : A} (hF : ∀ i, 0 ≤ F i) (j : ℕ) :
    0 ≤ localWealth F sel a j := by
  unfold localWealth
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact hF i
  · exact zero_le_one

end LocalWealth

section Supermartingale

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {A : Type*} [DecidableEq A]

/-- **Action-local wealth is a nonnegative supermartingale starting at one
(Theorem `thm:v34-action-local`, first claim).**  `F i` is the e-factor of the fixed
action-component pair at batch `i`, adapted to the batch filtration `ℱ`; the selection event
`{A_{i+1} = a}` is predictable (`ℱ i`-measurable); and on that event the conditional
expectation of `F (i+1)` given `ℱ i` is at most one (supplied under the component null by
`halfCash_integral_le_one`).  Integrability of the factors and of the wealth is a regularity
hypothesis.  Nonnegativity is `localWealth_nonneg` and the initial value is
`localWealth_zero`. -/
theorem localWealth_supermartingale (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    (F : ℕ → Ω → ℝ) (sel : ℕ → Ω → A) (a : A) (hF0 : ∀ i ω, 0 ≤ F i ω)
    (hFad : ∀ i, StronglyMeasurable[ℱ i] (F i))
    (hsel : ∀ i, MeasurableSet[ℱ i] {ω | sel (i + 1) ω = a})
    (hFint : ∀ i, Integrable (F i) μ)
    (hWint : ∀ j, Integrable (fun ω => localWealth (fun i => F i ω) (fun i => sel i ω) a j) μ)
    (hcond : ∀ i, ∀ᵐ ω ∂μ, sel (i + 1) ω = a → (μ[F (i + 1)|ℱ i]) ω ≤ 1) :
    Supermartingale (fun j ω => localWealth (fun i => F i ω) (fun i => sel i ω) a j) ℱ μ := by
  set W : ℕ → Ω → ℝ := fun j ω => localWealth (fun i => F i ω) (fun i => sel i ω) a j with hW
  have hWsucc : ∀ j ω, W (j + 1) ω = W j ω * (if sel (j + 1) ω = a then F (j + 1) ω else 1) :=
    fun j ω => localWealth_succ _ _ _ _
  have hW0 : ∀ j ω, 0 ≤ W j ω := fun j ω => localWealth_nonneg (fun i => hF0 i ω) j
  have hadp : ∀ j, StronglyMeasurable[ℱ j] (W j) := by
    intro j
    induction j with
    | zero =>
      have : W 0 = fun _ => 1 := by funext ω; simp [hW]
      rw [this]; exact stronglyMeasurable_const
    | succ j ih =>
      have : W (j + 1) = fun ω => W j ω * (if sel (j + 1) ω = a then F (j + 1) ω else 1) := by
        funext ω; exact hWsucc j ω
      rw [this]
      refine (ih.mono (ℱ.mono (Nat.le_succ j))).mul ?_
      exact StronglyMeasurable.ite (ℱ.mono (Nat.le_succ j) _ (hsel j)) (hFad (j + 1))
        stronglyMeasurable_const
  refine supermartingale_nat hadp hWint fun j => ?_
  set S : Set Ω := {ω | sel (j + 1) ω = a} with hS
  have hSm : MeasurableSet[ℱ j] S := hsel j
  have hSm0 : MeasurableSet S := ℱ.le j _ hSm
  have hG : StronglyMeasurable[ℱ j] (S.indicator (W j)) := (hadp j).indicator hSm
  have hG' : StronglyMeasurable[ℱ j] (Sᶜ.indicator (W j)) := (hadp j).indicator hSm.compl
  have hdecomp : W (j + 1) = S.indicator (W j) * F (j + 1) + Sᶜ.indicator (W j) := by
    funext ω
    rw [hWsucc]
    by_cases h : ω ∈ S
    · have h' : sel (j + 1) ω = a := h
      simp [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h), h']
    · have h' : ¬ sel (j + 1) ω = a := h
      simp [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h), h']
  have hprod_eq : S.indicator (W j) * F (j + 1) = S.indicator (W (j + 1)) := by
    funext ω
    by_cases h : ω ∈ S
    · have h' : sel (j + 1) ω = a := h
      simp [Set.indicator_of_mem h, hWsucc, h']
    · simp [Set.indicator_of_notMem h]
  have hint1 : Integrable (S.indicator (W j) * F (j + 1)) μ := by
    rw [hprod_eq]; exact (hWint (j + 1)).indicator hSm0
  have hint2 : Integrable (Sᶜ.indicator (W j)) μ := (hWint j).indicator hSm0.compl
  have h1 : μ[S.indicator (W j) * F (j + 1)|ℱ j] =ᵐ[μ] S.indicator (W j) * μ[F (j + 1)|ℱ j] :=
    condExp_mul_of_stronglyMeasurable_left hG hint1 (hFint (j + 1))
  have h2 : μ[Sᶜ.indicator (W j)|ℱ j] = Sᶜ.indicator (W j) :=
    condExp_of_stronglyMeasurable (ℱ.le j) hG' hint2
  have h3 : μ[W (j + 1)|ℱ j] =ᵐ[μ]
      μ[S.indicator (W j) * F (j + 1)|ℱ j] + μ[Sᶜ.indicator (W j)|ℱ j] := by
    rw [hdecomp]; exact condExp_add hint1 hint2 _
  filter_upwards [h1, h3, hcond j] with ω e1 e3 hc
  rw [e3, Pi.add_apply, e1, h2, Pi.mul_apply]
  by_cases h : ω ∈ S
  · have hc' := hc h
    simp only [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h),
      add_zero]
    calc W j ω * (μ[F (j + 1)|ℱ j]) ω ≤ W j ω * 1 :=
          mul_le_mul_of_nonneg_left hc' (hW0 j ω)
      _ = W j ω := mul_one _
  · simp [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h)]

end Supermartingale

/-- **Intersection-union root coverage (Theorem `thm:v34-action-local`, second claim).**
`bad` is the set of incorrect root actions; for each of them `zstar a ∈ J a` is a component
whose closed null contains the truth.  The hypothesis `hVille` is Ville's inequality for the
nonnegative supermartingale `E a (zstar a)` at level `K / δ` (Mathlib has no Ville inequality
for supermartingales; the supermartingale property is `localWealth_supermartingale`).  Then
the probability that at some batch the selected action is incorrect and passes the
minimum-over-components test `∀ z ∈ J_{A_j}, E_{A_j,z}(j) ≥ K / δ` is at most `δ`.  The error is
split as `δ / K` over root actions only, with no union over the components, and the bound
holds for an arbitrary selection process `sel`. -/
theorem intersection_union_coverage {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A Z : Type*} [Fintype A] (J : A → Finset Z) (E : A → Z → ℕ → Ω → ℝ) (sel : ℕ → Ω → A)
    (bad : Finset A) (zstar : A → Z) (hz : ∀ a ∈ bad, zstar a ∈ J a) {δ : ℝ} (hδ : 0 ≤ δ)
    (hVille : ∀ a ∈ bad, μ {ω | ∃ j, (Fintype.card A : ℝ) / δ ≤ E a (zstar a) j ω} ≤
      ENNReal.ofReal (δ / Fintype.card A)) :
    μ {ω | ∃ j, sel j ω ∈ bad ∧
        ∀ z ∈ J (sel j ω), (Fintype.card A : ℝ) / δ ≤ E (sel j ω) z j ω} ≤
      ENNReal.ofReal δ := by
  have hsub : {ω | ∃ j, sel j ω ∈ bad ∧
        ∀ z ∈ J (sel j ω), (Fintype.card A : ℝ) / δ ≤ E (sel j ω) z j ω} ⊆
      ⋃ a ∈ bad, {ω | ∃ j, (Fintype.card A : ℝ) / δ ≤ E a (zstar a) j ω} := by
    rintro ω ⟨j, hbad, htest⟩
    exact Set.mem_iUnion₂.mpr ⟨sel j ω, hbad, j, htest _ (hz _ hbad)⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_sum hVille).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (bad.card : ℝ) ≤ Fintype.card A := by
    exact_mod_cast Finset.card_le_univ bad
  have hK0 : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
  have : (bad.card : ENNReal) * ENNReal.ofReal (δ / Fintype.card A) =
      ENNReal.ofReal (bad.card * (δ / Fintype.card A)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [this]
  apply ENNReal.ofReal_le_ofReal
  rcases hK0.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hδ
  · rw [← mul_div_assoc, div_le_iff₀ hpos]
    nlinarith

/-! ### Solver-call counting (Proposition `prop:v34-work`) -/

open Classical in
/-- The number of four-power refresh indices `4^k ≤ j` is `1 + ⌊log₄ j⌋`. -/
theorem card_fourPower_refreshes {j : ℕ} (hj : 1 ≤ j) :
    ((Finset.Icc 1 j).filter fun i => ∃ k : ℕ, i = 4 ^ k).card = Nat.log 4 j + 1 := by
  have himg : ((Finset.Icc 1 j).filter fun i => ∃ k : ℕ, i = 4 ^ k) =
      (Finset.range (Nat.log 4 j + 1)).image fun k => 4 ^ k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hij⟩, k, rfl⟩
      exact ⟨k, Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) hij), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨Nat.one_le_pow _ _ (by norm_num),
        Nat.pow_le_of_le_log (by omega) (Nat.lt_succ_iff.mp hk)⟩, k, rfl⟩
  rw [himg, Finset.card_image_of_injective _ (Nat.pow_right_injective (le_refl 2 |>.trans
    (by norm_num))), Finset.card_range]

open Classical in
/-- Design-game calls through batch `j`: one call per root action (`K` of them) at each
four-power refresh index. -/
def designCalls (K j : ℕ) : ℕ :=
  K * ((Finset.Icc 1 j).filter fun i => ∃ k : ℕ, i = 4 ^ k).card

/-- **`W_design(j) ≤ K (1 + ⌊log₄ j⌋)` (Proposition `prop:v34-work`), with equality.** -/
theorem designCalls_eq (K : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    designCalls K j = K * (1 + Nat.log 4 j) := by
  rw [designCalls, card_fourPower_refreshes hj, add_comm]

/-- **`W_null(j) ≤ J_max j` (Proposition `prop:v34-work`).**  Only the selected action's
components are solved at each batch. -/
theorem nullSolves_le {A Z : Type*} (J : A → Finset Z) (sel : ℕ → A) {Jmax : ℕ}
    (hJ : ∀ a, (J a).card ≤ Jmax) (j : ℕ) :
    ∑ i ∈ Finset.Icc 1 j, (J (sel i)).card ≤ Jmax * j := by
  calc ∑ i ∈ Finset.Icc 1 j, (J (sel i)).card ≤ ∑ _i ∈ Finset.Icc 1 j, Jmax :=
        Finset.sum_le_sum fun i _ => hJ _
    _ = Jmax * j := by simp [mul_comm]

/-- Jensen's inequality for the logarithm: `E log T ≤ log E T` for `T ≥ 1`. -/
theorem integral_log_le_log_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {T : Ω → ℝ} (hT1 : ∀ ω, 1 ≤ T ω) (hT : Integrable T P) :
    Integrable (fun ω => Real.log (T ω)) P ∧
      ∫ ω, Real.log (T ω) ∂P ≤ Real.log (∫ ω, T ω ∂P) := by
  have hlogint : Integrable (fun ω => Real.log (T ω)) P := by
    refine hT.mono' (Real.measurable_log.comp_aemeasurable hT.aemeasurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h0 : 0 ≤ Real.log (T ω) := Real.log_nonneg (hT1 ω)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos (hT1 ω))
    linarith
  refine ⟨hlogint, ?_⟩
  set c := ∫ ω, T ω ∂P with hc
  have hc1 : 1 ≤ c := by
    have := integral_mono (integrable_const (1 : ℝ)) hT hT1
    simpa using this
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hpt : ∀ ω, Real.log (T ω) ≤ Real.log c + (T ω / c - 1) := by
    intro ω
    have hT0 : 0 < T ω := lt_of_lt_of_le one_pos (hT1 ω)
    have := Real.log_le_sub_one_of_pos (div_pos hT0 hc0)
    rw [Real.log_div hT0.ne' hc0.ne'] at this
    linarith
  have hint2 : Integrable (fun ω => Real.log c + (T ω / c - 1)) P :=
    (integrable_const _).add ((hT.div_const c).sub (integrable_const 1))
  have h := integral_mono hlogint hint2 hpt
  have hu : P.real Set.univ = 1 := by simp
  have e : ∫ ω, Real.log c + (T ω / c - 1) ∂P = Real.log c := by
    have hfun : (fun ω => Real.log c + (T ω / c - 1)) =
        fun ω => (Real.log c - 1) + c⁻¹ * T ω := by
      funext ω; ring
    rw [hfun, integral_add (integrable_const _) (hT.const_mul _), integral_const,
      integral_const_mul, ← hc, hu]
    simp [hc0.ne']
  linarith

/-- **Expected design-game calls at stopping (Proposition `prop:v34-work`).**  `T` is the
batch index at stopping.  Hypothesis `hET`: `E T ≤ c (1 + L²)`, which the manuscript obtains
from the stopping tail `eq:v34-tail-stop` and the clock inversion (not formalized).  Then, by
Jensen's inequality, `E W_design(T) ≤ K (1 + (log c + 2 log (1 + L)) / log 4)`, which is
`O(K [1 + log (1 + L)])`. -/
theorem expected_designCalls_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (K : ℕ) {T : Ω → ℕ} (hT1 : ∀ ω, 1 ≤ T ω)
    (hT : Integrable (fun ω => (T ω : ℝ)) P) {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hET : ∫ ω, (T ω : ℝ) ∂P ≤ c * (1 + L ^ 2)) :
    ∫ ω, (designCalls K (T ω) : ℝ) ∂P ≤
      K * (1 + (Real.log c + 2 * Real.log (1 + L)) / Real.log 4) := by
  have hT1' : ∀ ω, (1 : ℝ) ≤ T ω := fun ω => by exact_mod_cast hT1 ω
  obtain ⟨hlogint, hj⟩ := integral_log_le_log_integral P hT1' hT
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hE1 : (1 : ℝ) ≤ ∫ ω, (T ω : ℝ) ∂P := by
    have := integral_mono (integrable_const (1 : ℝ)) hT hT1'
    simpa using this
  have hlogE : Real.log (∫ ω, (T ω : ℝ) ∂P) ≤ Real.log c + 2 * Real.log (1 + L) := by
    have h1 : c * (1 + L ^ 2) ≤ c * (1 + L) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hc.le
    have h2 := Real.log_le_log (lt_of_lt_of_le one_pos hE1) (hET.trans h1)
    rw [Real.log_mul hc.ne' (by positivity), Real.log_pow] at h2
    simpa using h2
  have hpt : ∀ ω, (designCalls K (T ω) : ℝ) ≤ K * (1 + Real.log (T ω) / Real.log 4) := by
    intro ω
    rw [designCalls_eq K (hT1 ω)]
    push_cast
    have h := Real.natLog_le_logb (T ω) 4
    have e : Real.logb ((4 : ℕ) : ℝ) (T ω) = Real.log (T ω) / Real.log 4 := by
      simp [Real.logb]
    rw [e] at h
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg K)
  have hint2 : Integrable (fun ω => (K : ℝ) * (1 + Real.log (T ω) / Real.log 4)) P :=
    ((integrable_const (1 : ℝ)).add (hlogint.div_const _)).const_mul _
  have hg : Measurable (fun x : ℝ => (designCalls K ⌊x⌋₊ : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (designCalls K n : ℝ))).comp Nat.measurable_floor
  have hmeas : AEMeasurable (fun ω => (designCalls K (T ω) : ℝ)) P := by
    have := hg.comp_aemeasurable hT.aemeasurable
    simpa [Function.comp_def] using this
  have hint1 : Integrable (fun ω => (designCalls K (T ω) : ℝ)) P := by
    refine hint2.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hpt ω
  have hu : P.real Set.univ = 1 := by simp
  refine (integral_mono hint1 hint2 hpt).trans ?_
  rw [integral_const_mul, integral_add (integrable_const _) (hlogint.div_const _),
    integral_div, integral_const, hu]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K)
  have := div_le_div_of_nonneg_right (hj.trans hlogE) hlog4.le
  simp only [smul_eq_mul, one_mul]
  linarith

/-- **Expected component-null solves at stopping (Proposition `prop:v34-work`).**  With
`W_null ≤ J_max T` pointwise (`nullSolves_le`) and the hypothesis `E T ≤ c (1 + L²)`,
`E W_null ≤ J_max c (1 + L²)`. -/
theorem expected_nullSolves_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T Wnull : Ω → ℝ} {Jmax c L : ℝ} (hJ : 0 ≤ Jmax) (hT : Integrable T P)
    (hW : Integrable Wnull P) (hWT : ∀ ω, Wnull ω ≤ Jmax * T ω)
    (hET : ∫ ω, T ω ∂P ≤ c * (1 + L ^ 2)) :
    ∫ ω, Wnull ω ∂P ≤ Jmax * (c * (1 + L ^ 2)) := by
  refine (integral_mono hW (hT.const_mul Jmax) hWT).trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hET hJ

/-! ### Gaussian concentration tail (Lemma `lem:v34-concentration`) -/

/-- The onset `n₀(x, r) = max {3, ⌈4 vₓ / r⌉}`. -/
def n0 (v r : ℝ) : ℕ := max 3 ⌈4 * v / r⌉₊

/-- The explicit tail `Qₓ(n, r)` of `eq:v34-concentration-tail`. -/
def Qtail (v : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  if n < n0 v r then 1
  else min 1 (2 * Real.exp (-(n * r ^ 2 / (2 * v))) +
    2 * Real.exp (-(((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2))))

lemma chi2_sqrt_term {v r n : ℝ} (hv : 0 < v) (hr : 0 ≤ r) (hn : 1 ≤ n) :
    2 * Real.sqrt ((n - 1) * ((n - 1) * r ^ 2 / (64 * v ^ 2))) = (n - 1) * r / (4 * v) := by
  have e : (n - 1) * ((n - 1) * r ^ 2 / (64 * v ^ 2)) = ((n - 1) * r / (8 * v)) ^ 2 := by
    field_simp
    ring
  have h0 : 0 ≤ (n - 1) * r / (8 * v) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hn) hr) (by positivity)
  rw [e, Real.sqrt_sq h0]
  field_simp
  ring

/-- **Upper chi-square threshold absorption.**  With `k = n - 1` degrees of freedom and
`u = (n - 1) r² / (64 v²)`, a centered variance above `v + r` puts the chi-square statistic
`n v̌ / v` above the Chernoff (Laurent-Massart) threshold `k + 2 √(k u) + 2 u`, whenever
`r ≤ v / 8`. -/
theorem chi2_threshold_upper {v r n vchk : ℝ} (hv : 0 < v) (hr0 : 0 < r) (hrv : r ≤ v / 8)
    (hn : 1 ≤ n) (h : v + r < vchk) :
    (n - 1) + 2 * Real.sqrt ((n - 1) * ((n - 1) * r ^ 2 / (64 * v ^ 2))) +
      2 * ((n - 1) * r ^ 2 / (64 * v ^ 2)) < n * vchk / v := by
  rw [chi2_sqrt_term hv hr0.le hn, lt_div_iff₀ hv]
  have e : ((n - 1) + (n - 1) * r / (4 * v) + 2 * ((n - 1) * r ^ 2 / (64 * v ^ 2))) * v =
      (n - 1) * v + (n - 1) * r / 4 + (n - 1) * (r ^ 2 / v) / 32 := by
    field_simp
    ring
  have hq : r ^ 2 / v ≤ r / 8 := by
    rw [div_le_iff₀ hv]; nlinarith
  have h1 : (n - 1) * (r ^ 2 / v) ≤ (n - 1) * (r / 8) :=
    mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hn)
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have h2 : n * (v + r) < n * vchk := mul_lt_mul_of_pos_left h hn0
  have h3 : 0 ≤ n * r := mul_nonneg hn0.le hr0.le
  rw [e]
  nlinarith

/-- **Lower chi-square threshold absorption.**  A centered variance below `v - r` puts
`n v̌ / v` below `k - 2 √(k u)` once `n ≥ 4 v / r`; this also absorbs the `(n - 1) / n` bias. -/
theorem chi2_threshold_lower {v r n vchk : ℝ} (hv : 0 < v) (hr0 : 0 < r) (hn : 1 ≤ n)
    (hnr : 4 * v / r ≤ n) (h : vchk < v - r) :
    n * vchk / v < (n - 1) - 2 * Real.sqrt ((n - 1) * ((n - 1) * r ^ 2 / (64 * v ^ 2))) := by
  rw [chi2_sqrt_term hv hr0.le hn, div_lt_iff₀ hv]
  have e : ((n - 1) - (n - 1) * r / (4 * v)) * v = (n - 1) * v - (n - 1) * r / 4 := by
    field_simp
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have h2 : n * vchk < n * (v - r) := mul_lt_mul_of_pos_left h hn0
  have h3 : 4 * v ≤ n * r := (div_le_iff₀ hr0).mp hnr
  rw [e]
  nlinarith

/-- **Explicit Gaussian concentration, fixed sample size (Lemma `lem:v34-concentration`,
first claim), in modular form.**  `Ybar` and `vchk` are the mean and centered variance
(denominator `n`) of `n` iid `N(μ, v)` observations.  Hypotheses standing in for
distributional facts not derived here: `hmean` is the Gaussian sample-mean tail, and `hup`,
`hlo` are the upper and lower chi-square Chernoff inequalities for `n v̌ / v ~ χ²_{n-1}` at
level `u = (n - 1) r² / (64 v²)`.  Proved: the threshold algebra
(`chi2_threshold_upper/lower`), the union bound, and the cap at one, giving the displayed
`Qₓ(n, r)`. -/
theorem concentration_fixed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {v r μ : ℝ} (hv : 0 < v) (hr0 : 0 < r) (hrv : r ≤ v / 8) (n : ℕ)
    (Ybar vchk : Ω → ℝ)
    (hmean : P {ω | r < |Ybar ω - μ|} ≤ ENNReal.ofReal (2 * Real.exp (-(n * r ^ 2 / (2 * v)))))
    (hup : P {ω | ((n : ℝ) - 1) +
          2 * Real.sqrt (((n : ℝ) - 1) * (((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2))) +
          2 * (((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2)) < n * vchk ω / v} ≤
        ENNReal.ofReal (Real.exp (-(((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2)))))
    (hlo : P {ω | n * vchk ω / v < ((n : ℝ) - 1) -
          2 * Real.sqrt (((n : ℝ) - 1) * (((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2)))} ≤
        ENNReal.ofReal (Real.exp (-(((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2))))) :
    P {ω | r < |Ybar ω - μ| ∨ r < |vchk ω - v|} ≤ ENNReal.ofReal (Qtail v n r) := by
  unfold Qtail
  split_ifs with hn
  · simpa using prob_le_one
  · have hn0 : n0 v r ≤ n := not_lt.mp hn
    have hn3 : 3 ≤ n := (le_max_left _ _).trans hn0
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnr : 4 * v / r ≤ n := by
      have h1 : ⌈4 * v / r⌉₊ ≤ n := (le_max_right _ _).trans hn0
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    set A := {ω | r < |Ybar ω - μ|} with hA
    set B := {ω | ((n : ℝ) - 1) +
          2 * Real.sqrt (((n : ℝ) - 1) * (((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2))) +
          2 * (((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2)) < n * vchk ω / v} with hB
    set C := {ω | n * vchk ω / v < ((n : ℝ) - 1) -
          2 * Real.sqrt (((n : ℝ) - 1) * (((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2)))} with hC
    have hsub : {ω | r < |Ybar ω - μ| ∨ r < |vchk ω - v|} ⊆ A ∪ (B ∪ C) := by
      rintro ω (h | h)
      · exact Or.inl h
      · rcases lt_abs.mp h with h' | h'
        · exact Or.inr (Or.inl (chi2_threshold_upper hv hr0 hrv hn1 (by linarith)))
        · exact Or.inr (Or.inr (chi2_threshold_lower hv hr0 hn1 hnr (by linarith)))
    have hbound : P {ω | r < |Ybar ω - μ| ∨ r < |vchk ω - v|} ≤
        ENNReal.ofReal (2 * Real.exp (-(n * r ^ 2 / (2 * v))) +
          2 * Real.exp (-(((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2)))) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      refine (add_le_add hmean ((measure_union_le _ _).trans (add_le_add hup hlo))).trans ?_
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    rcases le_total 1 (2 * Real.exp (-(n * r ^ 2 / (2 * v))) +
        2 * Real.exp (-(((n : ℝ) - 1) * r ^ 2 / (64 * v ^ 2)))) with h | h
    · rw [min_eq_left h]; simpa using prob_le_one
    · rw [min_eq_right h]; exact hbound

/-- **Union over intrinsic tape prefixes (Lemma `lem:v34-concentration`, second claim).**
If each deterministic prefix length `n ≥ N` has a bad event of probability at most `q n`, the
probability that some prefix of length `n ≥ N` is bad (in particular the one picked by a
data-dependent count) is at most `∑_{n ≥ N} q n`.  No conditioning on the adaptive sample size
is involved. -/
theorem concentration_prefix {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bad : ℕ → Set Ω)
    (q : ℕ → ℝ) (N : ℕ) (h : ∀ n, N ≤ n → P (bad n) ≤ ENNReal.ofReal (q n)) :
    P {ω | ∃ n, N ≤ n ∧ ω ∈ bad n} ≤ ∑' n, if N ≤ n then ENNReal.ofReal (q n) else 0 := by
  have hsub : {ω | ∃ n, N ≤ n ∧ ω ∈ bad n} ⊆ ⋃ n, if N ≤ n then bad n else ∅ := by
    rintro ω ⟨n, hn, hω⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [hn, ↓reduceIte]; exact hω
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
  refine tsum_le_tsum fun n => ?_
  split_ifs with hn
  · exact h n hn
  · simp

/-! ### Deterministic cores of the sharp-rate proof (Theorem `thm:v34-adaptive`) -/

section Tracking

variable {X : Type*} [Fintype X] {U : Type*} {Z : Type*}

lemma compGame_of_empty {H : Set U} (hH : ¬ H.Nonempty) (pred : X → U → ℝ) (w m v : X → ℝ) :
    compGame H pred w m v = 0 := by
  have : IsEmpty H := Set.isEmpty_coe_sort.mpr (Set.not_nonempty_iff_eq_empty.mp hH)
  exact Real.iInf_of_isEmpty _

/-- **Baseline-rounding domination (`eq:v34-domination-repaired`).**  If the deployed
frequencies satisfy `w̃ₓ ≥ c wₓ` (with `c = M_j / R_j`, from `r_{j,x} ≥ M_j w_{j,x}`), then
`C_a(w̃; μ, v) ≥ c C_a(w; μ, v)`. -/
theorem actGame_domination (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {w wt μ v : X → ℝ} {c : ℝ} (hc : 0 ≤ c) (hw : ∀ x, 0 ≤ w x)
    (hdom : ∀ x, c * w x ≤ wt x) (hv : ∀ x, 0 < v x) :
    c * actGame J hJ H pred w μ v ≤ actGame J hJ H pred wt μ v := by
  have hwt : ∀ x, 0 ≤ wt x := fun x => (mul_nonneg hc (hw x)).trans (hdom x)
  refine (Finset.le_inf'_iff _ _).mpr fun z hz => ?_
  have h1 : c * actGame J hJ H pred w μ v ≤ c * compGame (H z) pred w μ v :=
    mul_le_mul_of_nonneg_left (Finset.inf'_le _ hz) hc
  refine h1.trans ?_
  by_cases hne : (H z).Nonempty
  · refine le_compGame hne fun u hu => ?_
    refine (mul_le_mul_of_nonneg_left (compGame_le hw hv hu) hc).trans ?_
    unfold nklObj
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hdom x) (nkl_nonneg (hv x) _ _)
  · rw [compGame_of_empty hne, compGame_of_empty hne, mul_zero]

/-- **Displayed-score accuracy at a good refresh.**  The design contract
`eq:v34-design-contract` (`Ĉ ≤ C_a^*(μ̂, v̂) ≤ Ĉ + e`) and the transport lemma give
`|Ĉ - C_a^*(μ, v)| ≤ d + e`. -/
theorem score_error_of_contract [Nonempty X] [DecidableEq X] (J : Finset Z) (hJ : J.Nonempty)
    (H : Z → Set U) (pred : X → U → ℝ) {μh vh μ v : X → ℝ} {Chat e d : ℝ}
    (hvh : ∀ x, 0 < vh x) (hv : ∀ x, 0 < v x)
    (hd : ∀ x, |μh x - μ x| / (2 * Real.sqrt (min (vh x) (v x))) +
      1 / 2 * |Real.log (vh x / v x)| ≤ d)
    (h1 : Chat ≤ actGameStar J hJ H pred μh vh)
    (h2 : actGameStar J hJ H pred μh vh ≤ Chat + e) :
    |Chat - actGameStar J hJ H pred μ v| ≤ d + e := by
  have ht := abs_le.mp (actGameStar_transport J hJ H pred hvh hv hd)
  rw [abs_le]; constructor <;> linarith [ht.1, ht.2]

/-- **Value of a retained design at the truth.**  Under the design contract, the returned
design `w` satisfies `C_a(w; μ, v) ≥ C_a^*(μ, v) - 2 d - e`. -/
theorem retained_design_value [Nonempty X] [DecidableEq X] (J : Finset Z) (hJ : J.Nonempty)
    (H : Z → Set U) (pred : X → U → ℝ) {w μh vh μ v : X → ℝ} {Chat e d : ℝ}
    (hw : w ∈ simplex X) (hvh : ∀ x, 0 < vh x) (hv : ∀ x, 0 < v x)
    (hd : ∀ x, |μh x - μ x| / (2 * Real.sqrt (min (vh x) (v x))) +
      1 / 2 * |Real.log (vh x / v x)| ≤ d)
    (h1 : Chat ≤ actGame J hJ H pred w μh vh)
    (h2 : actGameStar J hJ H pred μh vh ≤ Chat + e) :
    actGameStar J hJ H pred μ v - 2 * d - e ≤ actGame J hJ H pred w μ v := by
  have ht := abs_le.mp (actGameStar_transport J hJ H pred hvh hv hd)
  have ht2 := abs_le.mp (actGame_transport J hJ H pred hw hvh hv hd)
  linarith [ht.1, ht.2, ht2.1, ht2.2]

end Tracking

/-- **Stabilization of the sticky selection rule.**  `inc k` is the incumbent before refresh
`k` and `inc (k + 1)` the action deployed after it.  The rule (`hkeep`, `hswitch`): keep the
incumbent if its displayed score is within the hysteresis `h k` of the best displayed score,
otherwise switch to some displayed maximizer (any tie-breaking, in particular lowest index).
If from refresh `k0` on all displayed scores are within `h k / 8` of the true rates `Cst` and
`h k < Δ / 4` (every suboptimal action has gap more than `4 h k`), then the action deployed
after refresh `k0` is optimal and is never changed afterwards.  No uniqueness of the optimal
action is assumed. -/
theorem sticky_stabilization {A : Type*} (score : ℕ → A → ℝ) (Cst : A → ℝ) (Cstar : ℝ)
    (h : ℕ → ℝ) (inc : ℕ → A) (k0 : ℕ) (hmax : ∀ a, Cst a ≤ Cstar) (hatt : ∃ a, Cst a = Cstar)
    (hacc : ∀ k, k0 ≤ k → ∀ a, |score k a - Cst a| < h k / 8)
    (hgap : ∀ k, k0 ≤ k → ∀ a, Cst a < Cstar → 4 * h k < Cstar - Cst a)
    (hkeep : ∀ k, (∀ b, score k b - score k (inc k) ≤ h k) → inc (k + 1) = inc k)
    (hswitch : ∀ k, (∃ b, h k < score k b - score k (inc k)) →
      ∀ b, score k b ≤ score k (inc (k + 1))) :
    Cst (inc (k0 + 1)) = Cstar ∧ ∀ k, k0 ≤ k → inc (k + 1) = inc (k0 + 1) := by
  obtain ⟨as, has⟩ := hatt
  have hpos : ∀ k, k0 ≤ k → 0 < h k := fun k hk => by
    have := (abs_nonneg _).trans_lt (hacc k hk as)
    linarith
  have claim1 : ∀ k, k0 ≤ k → Cst (inc (k + 1)) = Cstar := by
    intro k hk
    have hh := hpos k hk
    have has' := abs_lt.mp (hacc k hk as)
    by_cases hkp : ∀ b, score k b - score k (inc k) ≤ h k
    · rw [hkeep k hkp]
      by_contra hne
      have hlt : Cst (inc k) < Cstar := lt_of_le_of_ne (hmax _) hne
      have hg := hgap k hk _ hlt
      have hi := abs_lt.mp (hacc k hk (inc k))
      have := hkp as
      linarith [has'.1, hi.2]
    · push Not at hkp
      have hsw := hswitch k hkp as
      have hi := abs_lt.mp (hacc k hk (inc (k + 1)))
      by_contra hne
      have hlt : Cst (inc (k + 1)) < Cstar := lt_of_le_of_ne (hmax _) hne
      have hg := hgap k hk _ hlt
      linarith [has'.1, hi.2]
  have claim2 : ∀ k, k0 ≤ k → Cst (inc k) = Cstar → inc (k + 1) = inc k := by
    intro k hk hopt
    refine hkeep k fun b => ?_
    have hb := abs_lt.mp (hacc k hk b)
    have hi := abs_lt.mp (hacc k hk (inc k))
    have := hmax b
    have hh := hpos k hk
    linarith [hb.2, hi.1]
  refine ⟨claim1 k0 le_rfl, fun k hk => ?_⟩
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [claim2 (k + 1) (hk.trans (Nat.le_succ k)) (claim1 k hk), ih]

/-- The half-cash factor is at least half the likelihood ratio, and under the two-nat
log-enclosure contract `eq:v34-numeric-contract` its logarithm is at least
`log (q / U) - 2 - log 2`. -/
theorem log_halfCash_ge {q qlo U Uhi : ℝ} (hqlo : 0 < qlo) (hq : qlo ≤ q) (hU : 0 < U)
    (hUhi : U ≤ Uhi) (hcontract : Real.log (q / qlo) + Real.log (Uhi / U) ≤ 2) :
    Real.log (q / U) - 2 - Real.log 2 ≤ Real.log (halfCash qlo Uhi) := by
  have hq0 : 0 < q := lt_of_lt_of_le hqlo hq
  have hUhi0 : 0 < Uhi := lt_of_lt_of_le hU hUhi
  have hr : 0 < qlo / Uhi := div_pos hqlo hUhi0
  have h1 : Real.log (qlo / Uhi / 2) ≤ Real.log (halfCash qlo Uhi) := by
    apply Real.log_le_log (by positivity)
    unfold halfCash; linarith
  rw [Real.log_div hr.ne' (by norm_num), Real.log_div hqlo.ne' hUhi0.ne'] at h1
  rw [Real.log_div hq0.ne' hqlo.ne', Real.log_div hUhi0.ne' hU.ne'] at hcontract
  rw [Real.log_div hq0.ne' hU.ne']
  linarith

/-- Per-batch evidence rate: if the normalized log-likelihood ratio is at least
`C - η/4 - L₀ρ` with `L₀ρ ≤ η/16`, and `R ≥ 4 (2 + log 2) / η`, then
`log F ≥ R (C - η)`. -/
theorem log_factor_rate {logratio logF R C η Lρ : ℝ} (hη : 0 < η)
    (hF : logratio - 2 - Real.log 2 ≤ logF) (hratio : R * (C - η / 4 - Lρ) ≤ logratio)
    (hLρ : Lρ ≤ η / 16) (hR : 4 * (2 + Real.log 2) / η ≤ R) :
    R * (C - η) ≤ logF := by
  have h1 : 4 * (2 + Real.log 2) ≤ R * η := (div_le_iff₀ hη).mp hR
  have hR0 : 0 ≤ R := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ 4 * (2 + Real.log 2) / η := by positivity
    linarith
  have h2 : R * Lρ ≤ R * (η / 16) := mul_le_mul_of_nonneg_left hLρ hR0
  nlinarith

/-- **Wealth accumulation.**  If every selected-action factor is at least `½` and, on the
recent window `i ≥ H`, action `a` is selected with `log F i ≥ c R i`, then
`log E^loc_a(j) ≥ c ∑_{H ≤ i ≤ j} R i - j log 2`. -/
theorem log_localWealth_ge {A : Type*} [DecidableEq A] (F : ℕ → ℝ) (sel : ℕ → A) (a : A)
    (j H : ℕ) (R : ℕ → ℝ) (c : ℝ)
    (hhalf : ∀ i ∈ Finset.Icc 1 j, sel i = a → 1 / 2 ≤ F i)
    (hwin : ∀ i ∈ Finset.Icc 1 j, H ≤ i → sel i = a ∧ c * R i ≤ Real.log (F i)) :
    c * ∑ i ∈ (Finset.Icc 1 j).filter (fun i => H ≤ i), R i - j * Real.log 2 ≤
      Real.log (localWealth F sel a j) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold localWealth
  rw [Real.log_prod]
  · have hterm : ∀ i ∈ Finset.Icc 1 j, (if H ≤ i then c * R i else 0) - Real.log 2 ≤
        Real.log (if sel i = a then F i else 1) := by
      intro i hi
      by_cases hH : H ≤ i
      · obtain ⟨hs, hl⟩ := hwin i hi hH
        simp only [hH, hs, ↓reduceIte]; linarith
      · simp only [hH, ↓reduceIte]
        by_cases hs : sel i = a
        · have := Real.log_le_log (by norm_num) (hhalf i hi hs)
          simp only [hs, ↓reduceIte]
          rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at this
          linarith
        · simp only [hs, ↓reduceIte, Real.log_one]; linarith
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Finset.sum_filter,
      Finset.mul_sum]
    simp
  · intro i hi
    split_ifs with hs
    · have := hhalf i hi hs; linarith
    · exact one_ne_zero

/-- Rate arithmetic: `(C - η)(N_j - N_{H-1}) - j log 2 ≥ (C - 2η) N_j` once
`N_{H-1} / N_j ≤ η / (4 C)` and `j log 2 / N_j ≤ η / 4`. -/
theorem wealth_rate {C η Nj NH jlog : ℝ} (hC : 0 < C) (hη : 0 ≤ η) (hNH0 : 0 ≤ NH)
    (hNH : NH ≤ η / (4 * C) * Nj) (hjlog : jlog ≤ η / 4 * Nj) :
    (C - 2 * η) * Nj ≤ (C - η) * (Nj - NH) - jlog := by
  have h1 : C * NH ≤ η / 4 * Nj := by
    have := mul_le_mul_of_nonneg_left hNH hC.le
    have e : C * (η / (4 * C) * Nj) = η / 4 * Nj := by field_simp
    linarith
  nlinarith [mul_nonneg hη hNH0]

/-- Stopping: wealth is at least `K / δ` as soon as its logarithm is at least `log (K / δ)`. -/
theorem stop_of_log_ge {W K δ : ℝ} (hW : 0 < W) (hK : 0 < K) (hδ : 0 < δ)
    (h : Real.log (K / δ) ≤ Real.log W) : K / δ ≤ W :=
  (Real.log_le_log_iff (div_pos hK hδ) hW).mp h

/-- Pointwise survival identity `N_T = ∑_{j ≥ 0} R_{j+1} 1{T > j}`. -/
lemma survival_identity (R : ℕ → ENNReal) (T : ℕ) :
    ∑' j, R (j + 1) * (if j < T then 1 else 0) = ∑ j ∈ Finset.range T, R (j + 1) := by
  rw [tsum_eq_sum (s := Finset.range T)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp [Finset.mem_range.mp hj]
  · intro j hj
    simp [show ¬ j < T by simpa using hj]

/-- **Expected stopping time from the stopping tail (`eq:v34-finite-envelope`).**  `S j` is
the event that the procedure has not stopped by the end of batch `j`, `R (j+1)` the size of
batch `j + 1`; the stopping time is `τ = ∑_j R_{j+1} 1_{S j}` (survival identity).  If
`P (S j) ≤ p j` for `j ≥ j⋆` (hypothesis; this is `eq:v34-tail-stop`), then
`E τ ≤ N_{j⋆} + ∑_{j ≥ j⋆} R_{j+1} min {1, p_j}`. -/
theorem lintegral_stopping_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : ℕ → Set Ω) (hS : ∀ j, MeasurableSet (S j))
    (R p : ℕ → ENNReal) (jstar : ℕ) (hp : ∀ j, jstar ≤ j → P (S j) ≤ p j) :
    ∫⁻ ω, ∑' j, R (j + 1) * (S j).indicator 1 ω ∂P ≤
      ∑ j ∈ Finset.range jstar, R (j + 1) +
        ∑' j, if jstar ≤ j then R (j + 1) * min 1 (p j) else 0 := by
  have hmeas : ∀ j, Measurable fun ω => R (j + 1) * (S j).indicator (1 : Ω → ENNReal) ω :=
    fun j => (measurable_one.indicator (hS j)).const_mul _
  rw [lintegral_tsum fun j => (hmeas j).aemeasurable]
  have hterm : ∀ j, ∫⁻ ω, R (j + 1) * (S j).indicator (1 : Ω → ENNReal) ω ∂P =
      R (j + 1) * P (S j) := by
    intro j
    rw [lintegral_const_mul _ (measurable_one.indicator (hS j)), lintegral_indicator_one (hS j)]
  simp_rw [hterm]
  have hle : ∀ j, R (j + 1) * P (S j) ≤
      (if j ∈ Finset.range jstar then R (j + 1) else 0) +
        (if jstar ≤ j then R (j + 1) * min 1 (p j) else 0) := by
    intro j
    by_cases hj : jstar ≤ j
    · have hnr : j ∉ Finset.range jstar := by simpa using hj
      simp only [hj, hnr, ↓reduceIte, zero_add]
      gcongr
      exact le_min prob_le_one (hp j hj)
    · have hr : j ∈ Finset.range jstar := by simpa using hj
      simp only [hj, hr, ↓reduceIte, add_zero]
      calc R (j + 1) * P (S j) ≤ R (j + 1) * 1 := by gcongr; exact prob_le_one
        _ = R (j + 1) := mul_one _
  refine (tsum_le_tsum hle).trans (le_of_eq ?_)
  rw [tsum_add, tsum_eq_sum (s := Finset.range jstar)]
  · congr 1
    exact Finset.sum_congr rfl fun j hj => by simp only [hj, ↓reduceIte]
  · intro j hj
    simp only [hj, ↓reduceIte]

/-- **Overshoot bound for the leading coefficient.**  With `η = C s / (16 (1 + s))`, `j⋆` the
first index `≥ j₁` with `(C - 2η) N_j ≥ B`, and `R_j / N_{j-1} ≤ s / 4` beyond `j_s ≥ j₁ + 1`,
`N_{j⋆} ≤ N_{j_s} + (1 + s) B / C`. -/
theorem overshoot_bound {N : ℕ → ℝ} {C η s B : ℝ} {j1 js jstar : ℕ} (hC : 0 < C)
    (hs0 : 0 < s) (hη : η = C * s / (16 * (1 + s))) (hB : 0 ≤ B) (hN0 : ∀ j, 0 ≤ N j)
    (hmono : Monotone N) (hjs : j1 + 1 ≤ js)
    (hstep : ∀ j, js < j → N j - N (j - 1) ≤ s / 4 * N (j - 1))
    (hmin : ∀ j, j1 ≤ j → j < jstar → (C - 2 * η) * N j < B) :
    N jstar ≤ N js + (1 + s) / C * B := by
  have hterm : 0 ≤ (1 + s) / C * B := by positivity
  by_cases hle : jstar ≤ js
  · have := hmono hle
    linarith
  · have hlt : js < jstar := not_le.mp hle
    have h1 := hstep jstar hlt
    have h2 := hmin (jstar - 1) (by omega) (by omega)
    have e : (1 + s) / C * (C - 2 * η) = (8 + 7 * s) / 8 := by
      rw [hη]; field_simp; ring
    have hN' := hN0 (jstar - 1)
    have h3 : (1 + s) / C * ((C - 2 * η) * N (jstar - 1)) ≤ (1 + s) / C * B :=
      mul_le_mul_of_nonneg_left h2.le (by positivity)
    rw [← mul_assoc, e] at h3
    have := hN0 js
    nlinarith

open Filter Topology in
/-- **Asymptotic upper coefficient.**  If for every rational `s ∈ (0, 1]` there is a constant
`D s` with `E τ_δ ≤ D s + (1 + s) / C log (1/δ)` for all `δ ∈ (0, 1)`, then for every
`c > 1 / C`, eventually as `δ ↓ 0`, `E τ_δ ≤ c log (1/δ)`; that is,
`limsup E τ_δ / log (1/δ) ≤ 1 / C`. -/
theorem limsup_coefficient {Eτ : ℝ → ℝ} {C : ℝ} (hC : 0 < C) (D : ℚ → ℝ)
    (hbound : ∀ s : ℚ, 0 < s → s ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
      Eτ δ ≤ D s + (1 + (s : ℝ)) / C * Real.log (1 / δ))
    {c : ℝ} (hc : 1 / C < c) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Eτ δ ≤ c * Real.log (1 / δ) := by
  have hcC : 0 < c * C - 1 := by
    have := (div_lt_iff₀ hC).mp hc
    linarith
  obtain ⟨s, hs0, hs1⟩ := exists_rat_btwn (lt_min one_pos hcC)
  have hs0' : (0 : ℚ) < s := by exact_mod_cast hs0
  have hsle : s ≤ 1 := by exact_mod_cast (hs1.trans_le (min_le_left _ _)).le
  have hsC : (s : ℝ) < c * C - 1 := hs1.trans_le (min_le_right _ _)
  have hg : 0 < c - (1 + (s : ℝ)) / C := by
    rw [sub_pos, div_lt_iff₀ hC]; linarith
  have htop : Tendsto (fun δ : ℝ => Real.log (1 / δ)) (𝓝[>] 0) atTop := by
    have : (fun δ : ℝ => Real.log (1 / δ)) = fun δ => -Real.log δ := by
      funext δ; rw [one_div, Real.log_inv]
    rw [this]
    exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  filter_upwards [htop.eventually_ge_atTop (D s / (c - (1 + (s : ℝ)) / C)),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ hmem
  have hb := hbound s hs0' hsle δ hmem.1 hmem.2
  have h1 : D s ≤ (c - (1 + (s : ℝ)) / C) * Real.log (1 / δ) := by
    have := (div_le_iff₀ hg).mp hδ
    linarith
  linarith

/-! ### Deterministic cores of the converse (Theorems `thm:v34-converse-main`,
`thm:v34-converse`) -/

/-- Closed form of `KL (N(μ, v) ‖ N(t, s))` for variances `v, s > 0`:
`½ [log (s / v) + (v + (μ - t)²) / s - 1]`.  (Used as a definition; the identification with
the measure-theoretic KL divergence of Gaussian laws is not formalized.) -/
def gaussKL (μ v t s : ℝ) : ℝ := 1 / 2 * (Real.log (s / v) + (v + (μ - t) ^ 2) / s - 1)

/-- Profiling the alternative variance: every alternative variance `s > 0` has Gaussian KL at
least the nuisance-profiled value `½ log (1 + (μ - t)² / v)`. -/
theorem gaussKL_ge_nkl {μ v t s : ℝ} (hv : 0 < v) (hs : 0 < s) :
    nkl μ v t ≤ gaussKL μ v t s := by
  unfold nkl gaussKL
  set c := v + (μ - t) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have e : 1 + (μ - t) ^ 2 / v = c / v := by rw [hc]; field_simp
  have h := Real.log_le_sub_one_of_pos (div_pos hc0 hs)
  rw [e, Real.log_div hc0.ne' hv.ne', Real.log_div hs.ne' hv.ne']
  rw [Real.log_div hc0.ne' hs.ne'] at h
  linarith

/-- The profiled value is attained at `s = v + (μ - t)²`. -/
theorem gaussKL_profile_eq {μ v t : ℝ} (hv : 0 < v) :
    gaussKL μ v t (v + (μ - t) ^ 2) = nkl μ v t := by
  unfold nkl gaussKL
  have hc0 : 0 < v + (μ - t) ^ 2 := by positivity
  have e : 1 + (μ - t) ^ 2 / v = (v + (μ - t) ^ 2) / v := by field_simp
  rw [e, div_self hc0.ne']
  ring

/-- `inf_{s > 0} KL (N(μ, v) ‖ N(t, s)) = ½ log (1 + (μ - t)² / v)`, attained. -/
theorem gaussKL_isLeast {μ v t : ℝ} (hv : 0 < v) :
    IsLeast {k | ∃ s : ℝ, 0 < s ∧ k = gaussKL μ v t s} (nkl μ v t) :=
  ⟨⟨v + (μ - t) ^ 2, by positivity, (gaussKL_profile_eq hv).symm⟩,
    by rintro _ ⟨s, hs, rfl⟩; exact gaussKL_ge_nkl hv hs⟩

section Converse

variable {X : Type*} [Fintype X] {U : Type*} {Z : Type*}

lemma continuous_nklObj [TopologicalSpace U] {pred : X → U → ℝ}
    (hpred : ∀ x, Continuous (pred x)) (w m : X → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x) :
    Continuous (nklObj pred w m v) := by
  unfold nklObj nkl
  refine continuous_finsetSum _ fun x _ => ?_
  refine continuous_const.mul (continuous_const.mul ?_)
  refine Continuous.log ?_ fun u => ?_
  · exact continuous_const.add (((continuous_const.sub (hpred x)).pow 2).div_const _)
  · have : 0 ≤ (m x - pred x u) ^ 2 / v x := div_nonneg (sq_nonneg _) (hv x).le
    linarith

/-- **Boundary step of the converse.**  A lower bound on the nuisance-KL objective valid on a
strict invalidating set `S` extends to any set contained in its closure. -/
theorem transport_closure [TopologicalSpace U] {pred : X → U → ℝ}
    (hpred : ∀ x, Continuous (pred x)) {w m v : X → ℝ} (hv : ∀ x, 0 < v x) {S Hc : Set U}
    (hH : Hc ⊆ closure S) {κ : ℝ} (hS : ∀ u ∈ S, κ ≤ nklObj pred w m v u) :
    ∀ u ∈ Hc, κ ≤ nklObj pred w m v u := by
  have hcl : IsClosed {u | κ ≤ nklObj pred w m v u} :=
    isClosed_le continuous_const (continuous_nklObj hpred w m hv)
  intro u hu
  exact closure_minimal (fun u hu => hS u hu) hcl (hH hu)

/-- **Reduction of the unknown-variance converse (Theorem `thm:v34-converse`).**
`N x` are the expected query counts `E N_x(τ)` under the truth and `T = ∑ N x = E τ` (finite,
positive).  Hypothesis `htransport` is the stopped change-of-measure / binary data-processing
inequality `∑ₓ E Nₓ(τ) KL(N(μₓ, vₓ), N(hₓᵀu, sₓ)) ≥ κ` (with `κ = kl(1 - δ, δ)`) for every
strict alternative `u ∈ Hs z` and every alternative variance vector; it is not derived here.
`Hc z` is the closed component, contained in the closure of the strict one.  Proved: profiling
of the alternative variances, extension to the closed components, normalization
`w = N / T`, and the conclusion `E τ · C_{a⋆}(w; μ, v) ≥ κ`, hence `E τ ≥ κ / C⋆` for any
`C⋆ > 0` bounding `C_{a⋆}(·; μ, v)` on the simplex. -/
theorem converse_reduction [TopologicalSpace U] (J : Finset Z) (hJ : J.Nonempty)
    (Hc Hs : Z → Set U) (pred : X → U → ℝ) (hpred : ∀ x, Continuous (pred x))
    {μ v N : X → ℝ} {T κ Cstar : ℝ} (hv : ∀ x, 0 < v x) (hN : ∀ x, 0 ≤ N x)
    (hT : ∑ x, N x = T) (hTpos : 0 < T) (hne : ∀ z ∈ J, (Hc z).Nonempty)
    (hcl : ∀ z ∈ J, Hc z ⊆ closure (Hs z))
    (htransport : ∀ z ∈ J, ∀ u ∈ Hs z, ∀ s : X → ℝ, (∀ x, 0 < s x) →
      κ ≤ ∑ x, N x * gaussKL (μ x) (v x) (pred x u) (s x))
    (hCstar : ∀ w ∈ simplex X, actGame J hJ Hc pred w μ v ≤ Cstar) (hCpos : 0 < Cstar) :
    κ ≤ T * actGame J hJ Hc pred (fun x => N x / T) μ v ∧ κ / Cstar ≤ T := by
  have hw : (fun x => N x / T) ∈ simplex X :=
    ⟨fun x => div_nonneg (hN x) hTpos.le, by rw [← Finset.sum_div, hT, div_self hTpos.ne']⟩
  have hobj : ∀ u, nklObj pred (fun x => N x / T) μ v u = nklObj pred N μ v u / T := by
    intro u
    unfold nklObj
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hkey : κ / T ≤ actGame J hJ Hc pred (fun x => N x / T) μ v := by
    refine (Finset.le_inf'_iff _ _).mpr fun z hz => ?_
    refine le_compGame (hne z hz) ?_
    have hstrict : ∀ u ∈ Hs z, κ ≤ nklObj pred N μ v u := by
      intro u hu
      have h := htransport z hz u hu (fun x => v x + (μ x - pred x u) ^ 2)
        (fun x => by have := hv x; positivity)
      refine h.trans (le_of_eq ?_)
      unfold nklObj
      exact Finset.sum_congr rfl fun x _ => by rw [gaussKL_profile_eq (hv x)]
    intro u hu
    rw [hobj]
    exact div_le_div_of_nonneg_right (transport_closure hpred hv (hcl z hz) hstrict u hu)
      hTpos.le
  have h1 : κ ≤ T * actGame J hJ Hc pred (fun x => N x / T) μ v := by
    have := (div_le_iff₀ hTpos).mp hkey
    linarith
  refine ⟨h1, ?_⟩
  rw [div_le_iff₀ hCpos]
  have := mul_le_mul_of_nonneg_left (hCstar _ hw) hTpos.le
  linarith

/-- The same reduction with `C⋆ = C_{a⋆}^*(μ, v)` (the supremum over designs). -/
theorem converse_reduction_star [TopologicalSpace U] (J : Finset Z) (hJ : J.Nonempty)
    (Hc Hs : Z → Set U) (pred : X → U → ℝ) (hpred : ∀ x, Continuous (pred x))
    {μ v N : X → ℝ} {T κ : ℝ} (hv : ∀ x, 0 < v x) (hN : ∀ x, 0 ≤ N x)
    (hT : ∑ x, N x = T) (hTpos : 0 < T) (hne : ∀ z ∈ J, (Hc z).Nonempty)
    (hcl : ∀ z ∈ J, Hc z ⊆ closure (Hs z))
    (htransport : ∀ z ∈ J, ∀ u ∈ Hs z, ∀ s : X → ℝ, (∀ x, 0 < s x) →
      κ ≤ ∑ x, N x * gaussKL (μ x) (v x) (pred x u) (s x))
    (hCpos : 0 < actGameStar J hJ Hc pred μ v) :
    κ / actGameStar J hJ Hc pred μ v ≤ T :=
  (converse_reduction J hJ Hc Hs pred hpred hv hN hT hTpos hne hcl htransport
    (fun _ hw => actGame_le_star J hJ Hc pred hw hv) hCpos).2

/-- An incorrect action has zero information rate at the truth: if the true parameter `θ`
lies in one of its closed invalidating components, `C_a(w; μ, v) = 0` for every design. -/
theorem actGame_eq_zero_of_mem (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {w μ v : X → ℝ} (hw : ∀ x, 0 ≤ w x) (hv : ∀ x, 0 < v x) {z : Z}
    (hz : z ∈ J) {θ : U} (hθ : θ ∈ H z) (hμ : ∀ x, pred x θ = μ x) :
    actGame J hJ H pred w μ v = 0 := by
  refine le_antisymm ?_ (actGame_nonneg hw hv)
  refine (Finset.inf'_le _ hz).trans ((compGame_le hw hv hθ).trans (le_of_eq ?_))
  unfold nklObj
  exact Finset.sum_eq_zero fun x _ => by rw [hμ x, nkl_self, mul_zero]

/-- Hence `C_a^*(μ, v) = 0` for an incorrect action. -/
theorem actGameStar_eq_zero_of_mem [Nonempty X] [DecidableEq X] (J : Finset Z)
    (hJ : J.Nonempty) (H : Z → Set U) (pred : X → U → ℝ) {μ v : X → ℝ} (hv : ∀ x, 0 < v x)
    {z : Z} (hz : z ∈ J) {θ : U} (hθ : θ ∈ H z) (hμ : ∀ x, pred x θ = μ x) :
    actGameStar J hJ H pred μ v = 0 := by
  obtain ⟨x0⟩ := ‹Nonempty X›
  have : Nonempty (simplex X) := ⟨⟨_, single_mem_simplex x0⟩⟩
  unfold actGameStar
  have h : ∀ w : simplex X, actGame J hJ H pred w μ v = 0 := fun w =>
    actGame_eq_zero_of_mem J hJ H pred w.2.1 hv hz hθ hμ
  simp_rw [h]
  exact ciSup_const

end Converse

/-- The binary relative entropy `kl(p, q)`. -/
def klBin (p q : ℝ) : ℝ := p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

lemma klBin_one_sub {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    klBin (1 - δ) δ = (1 - 2 * δ) * (Real.log (1 - δ) + Real.log (1 / δ)) := by
  unfold klBin
  have h1' : (0 : ℝ) < 1 - δ := by linarith
  rw [sub_sub_cancel, Real.log_div h1'.ne' h0.ne', Real.log_div h0.ne' h1'.ne', one_div,
    Real.log_inv]
  ring

open Filter Topology in
/-- `kl(1 - δ, δ) / log (1/δ) → 1` as `δ ↓ 0`. -/
theorem tendsto_klBin_div_log :
    Tendsto (fun δ : ℝ => klBin (1 - δ) δ / Real.log (1 / δ)) (𝓝[>] 0) (𝓝 1) := by
  have htop : Tendsto (fun δ : ℝ => Real.log (1 / δ)) (𝓝[>] 0) atTop := by
    have : (fun δ : ℝ => Real.log (1 / δ)) = fun δ => -Real.log δ := by
      funext δ; rw [one_div, Real.log_inv]
    rw [this]
    exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h1 : Tendsto (fun δ : ℝ => 1 - 2 * δ) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun δ : ℝ => 1 - 2 * δ) (𝓝 0) (𝓝 (1 - 2 * 0)) :=
      (continuous_const.sub (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun δ : ℝ => Real.log (1 - δ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun δ : ℝ => Real.log (1 - δ)) 0 :=
      ContinuousAt.log (continuous_const.sub continuous_id).continuousAt (by norm_num)
    have : Tendsto (fun δ : ℝ => Real.log (1 - δ)) (𝓝 0) (𝓝 (Real.log (1 - 0))) := hc
    simpa using this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun δ : ℝ => (Real.log (1 / δ))⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hlim : Tendsto (fun δ : ℝ => (1 - 2 * δ) *
      (Real.log (1 - δ) * (Real.log (1 / δ))⁻¹ + 1)) (𝓝[>] 0) (𝓝 1) := by
    have := h1.mul ((h2.mul h3).add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [htop.eventually_gt_atTop 0,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hpos hmem
  rw [klBin_one_sub hmem.1 hmem.2]
  field_simp

open Filter Topology in
/-- **Asymptotic lower coefficient.**  If `E τ_δ ≥ kl(1 - δ, δ) / C` for `0 < δ < 1/2`, then
for every `c < 1 / C`, eventually as `δ ↓ 0`, `c log (1/δ) ≤ E τ_δ`; that is,
`liminf E τ_δ / log (1/δ) ≥ 1 / C`. -/
theorem liminf_coefficient {Eτ : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hbound : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → klBin (1 - δ) δ / C ≤ Eτ δ)
    {c : ℝ} (hc : c < 1 / C) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), c * Real.log (1 / δ) ≤ Eτ δ := by
  have hcC : c * C < 1 := by
    have := (lt_div_iff₀ hC).mp hc
    linarith
  have htop : Tendsto (fun δ : ℝ => Real.log (1 / δ)) (𝓝[>] 0) atTop := by
    have : (fun δ : ℝ => Real.log (1 / δ)) = fun δ => -Real.log δ := by
      funext δ; rw [one_div, Real.log_inv]
    rw [this]
    exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  filter_upwards [tendsto_klBin_div_log.eventually (lt_mem_nhds hcC),
    htop.eventually_gt_atTop 0,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hratio hpos hmem
  have hb := hbound δ hmem.1 hmem.2
  have h1 : c * C * Real.log (1 / δ) < klBin (1 - δ) δ := (lt_div_iff₀ hpos).mp hratio
  have h2 : c * Real.log (1 / δ) < klBin (1 - δ) δ / C := by
    rw [lt_div_iff₀ hC]; linarith
  linarith

end

end JointRootCert
