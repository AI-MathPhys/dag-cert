/-
# Known-variance Gaussian finite-confidence results on a formal model

A formal model of the whitened Gaussian linear experiment of `app:bay-finite` and the
discharge, on that model, of the probabilistic hypotheses of the deterministic cores in
`GaussianInfo.lean`.

Model.  Queries `x : X` with features `u x : E` (`E` a finite-dimensional real inner
product space, `d = finrank ℝ E`).  A noise tape is a family `ξ x i` of independent
standard Gaussians on a probability space; the `i`-th observation of query `x` is
`⟪u x, θ⟫ + ξ x i`.  A fixed design with counts `c x` uses the first `c x` observations of
each query; its least-squares estimate `olsCount` is the solution of the normal equations.

Results covered (manuscript labels):

* `thm:v10g-discovery` (Explicit discovery and a frozen near-optimal plan):
  `ols_error_chiSq`, `ols_chi_tail`, `pilot_concentration`, `pilot_commit`,
  `v10g_discovery`.
* `prop:v10g-safety-fallback` (Conditional safety and a finite-mean reference design):
  `fresh_coverage`, `ols_chernoff`, `safeguard_safe`, `safeguard_mean`,
  `confirm_safe_fixed`, `confirm_coverage`, `confirm_branch_safe`.
* `thm:v10g-expectation` (Correlated finite-confidence discovery and confirmation):
  `v10g_safe`, `main_stops_det`, `v10g_expectation`.
* `cor:v10g-target` (Finite-confidence correlated confirmation bound): `v10g_target`,
  `R10_order`, `rate_of_target`.
* `prop:bay-finite` (Finite-confidence discovery, frozen confirmation, and safeguard):
  `bay_finite`.

What is assumed and not derived: the oracle contract `OracleContract` (`eq:v10g-oracle`),
Borel measurability of the oracle's design and lower endpoint, the numerical enclosures
of the stopping statistics, and independence of the three noise tapes as random elements.
No probability space carrying the tapes is constructed.
-/
import JointRootCert.GaussianInfo
import JointRootCert.ChiSquare

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

universe uX

/-! ### Projections of a standard Gaussian vector -/

section GaussianProjection

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- The coordinates of a vector of independent standard Gaussians in an orthonormal basis
are independent standard Gaussians. -/
theorem orthonormal_coords_iid [IsProbabilityMeasure P] {ι J : Type*} [Fintype ι] [Fintype J]
    {Z : ι → Ω → ℝ} (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (b : OrthonormalBasis J ℝ (EuclideanSpace ℝ ι)) :
    iIndepFun (fun j ω => ⟪b j, (WithLp.toLp 2 (fun i => Z i ω) : EuclideanSpace ℝ ι)⟫) P ∧
      ∀ j, HasLaw (fun ω => ⟪b j, (WithLp.toLp 2 (fun i => Z i ω) : EuclideanSpace ℝ ι)⟫)
        (gaussianReal 0 1) P := by
  classical
  let V : Ω → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (fun i => Z i ω)
  let W : J → Ω → ℝ := fun j ω => b.repr (V ω) j
  have hWeq : (fun j ω => ⟪b j, (WithLp.toLp 2 (fun i => Z i ω) : EuclideanSpace ℝ ι)⟫) = W := by
    funext j ω
    simp only [W, V, b.repr_apply_apply]
  have hpi : HasLaw (fun ω i => Z i ω) (Measure.pi fun _ : ι => gaussianReal 0 1) P :=
    hind.hasLaw_pi hZ
  have hto : HasLaw (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (stdGaussian (EuclideanSpace ℝ ι)) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    ⟨(WithLp.measurable_toLp 2 _).aemeasurable, map_pi_eq_stdGaussian⟩
  have hrepr : HasLaw (b.repr : EuclideanSpace ℝ ι → EuclideanSpace ℝ J)
      (stdGaussian (EuclideanSpace ℝ J)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨b.repr.continuous.measurable.aemeasurable, stdGaussian_map b.repr⟩
  have hof : HasLaw (WithLp.ofLp : EuclideanSpace ℝ J → (J → ℝ))
      (Measure.pi fun _ : J => gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ J)) := by
    refine ⟨(WithLp.measurable_ofLp 2 _).aemeasurable, ?_⟩
    rw [← map_pi_eq_stdGaussian,
      Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _)]
    exact Measure.map_id
  have hWvec : HasLaw (fun ω j => W j ω) (Measure.pi fun _ : J => gaussianReal 0 1) P :=
    hof.comp (hrepr.comp (hto.comp hpi))
  have hWi : ∀ j, HasLaw (W j) (gaussianReal 0 1) P := fun j =>
    (measurePreserving_eval (fun _ : J => gaussianReal 0 1) j).hasLaw.comp hWvec
  have hWind : iIndepFun W P := (iIndepFun_iff_hasLaw_pi_pi hWi).mpr hWvec
  refine ⟨by rw [hWeq]; exact hWind, fun j => ?_⟩
  have h2 : (fun ω => ⟪b j, (WithLp.toLp 2 (fun i => Z i ω) : EuclideanSpace ℝ ι)⟫) = W j :=
    congrFun hWeq j
  rw [h2]
  exact hWi j

/-- **Projection of a standard Gaussian vector onto a subspace.**  If `Z` is a vector of
independent standard Gaussians and `K` a subspace of dimension `r`, then `‖P_K Z‖²` is a
sum of `r` independent squared standard Gaussians. -/
theorem exists_iid_sq_proj [IsProbabilityMeasure P] {ι : Type uX} [Fintype ι]
    {Z : ι → Ω → ℝ} (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    ∃ (J : Type uX) (g : J → Ω → ℝ) (s : Finset J), iIndepFun g P ∧
      (∀ j, HasLaw (g j) (gaussianReal 0 1) P) ∧ s.card = Module.finrank ℝ K ∧
      ∀ ω, ‖K.starProjection (WithLp.toLp 2 (fun i => Z i ω) : EuclideanSpace ℝ ι)‖ ^ 2 =
        ∑ j ∈ s, g j ω ^ 2 := by
  classical
  let bK := stdOrthonormalBasis ℝ K
  let f : Fin (Module.finrank ℝ K) → EuclideanSpace ℝ ι := fun j => (bK j : EuclideanSpace ℝ ι)
  have hf : Orthonormal ℝ f := bK.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hfinj : Function.Injective f := hf.linearIndependent.injective
  have hrange : Orthonormal ℝ ((↑) : Set.range f → EuclideanSpace ℝ ι) :=
    (orthonormal_subtype_range hfinj).mpr hf
  obtain ⟨u, b, hsub, hb⟩ := hrange.exists_orthonormalBasis_extension
  have hmem : ∀ j, f j ∈ u := fun j => hsub ⟨j, rfl⟩
  let emb : Fin (Module.finrank ℝ K) → u := fun j => ⟨f j, hmem j⟩
  have hemb : Function.Injective emb := fun a c h => by
    have h' : f a = f c := congrArg (fun z : u => (z : EuclideanSpace ℝ ι)) h
    exact hfinj h'
  obtain ⟨hWind, hWlaw⟩ := orthonormal_coords_iid hind hZ b
  refine ⟨u, _, Finset.univ.image emb, hWind, hWlaw, ?_, fun ω => ?_⟩
  · rw [card_image_of_injective _ hemb, card_univ, Fintype.card_fin]
  · rw [sum_image (fun a _ c _ h => hemb h)]
    set y : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => Z i ω) with hy
    have hPy : K.starProjection y ∈ K := K.starProjection_apply_mem y
    have h1 := bK.sum_sq_norm_inner_right (⟨K.starProjection y, hPy⟩ : K)
    have hn : ‖(⟨K.starProjection y, hPy⟩ : K)‖ = ‖K.starProjection y‖ := rfl
    rw [hn] at h1
    simp only [Submodule.coe_inner, Real.norm_eq_abs, sq_abs] at h1
    rw [← h1]
    refine sum_congr rfl (fun j _ => ?_)
    have h2 : b (emb j) = f j := by rw [hb]
    have h3 : K.starProjection (f j) = f j :=
      Submodule.starProjection_eq_self_iff.mpr (bK j).2
    have h4 : ⟪f j, y⟫ = ⟪f j, K.starProjection y⟫ := by
      rw [← Submodule.inner_starProjection_left_eq_right, h3]
    rw [h2, h4]

/-- Laurent--Massart upper tail for the squared norm of a projected standard Gaussian. -/
theorem proj_sq_tail [IsProbabilityMeasure P] {ι : Type uX} [Fintype ι]
    {Z : ι → Ω → ℝ} (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (K : Submodule ℝ (EuclideanSpace ℝ ι)) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | (Module.finrank ℝ K : ℝ) + 2 * Real.sqrt ((Module.finrank ℝ K : ℝ) * t) + 2 * t ≤
      ‖K.starProjection (WithLp.toLp 2 (fun i => Z i ω) : EuclideanSpace ℝ ι)‖ ^ 2} ≤
      Real.exp (-t) := by
  obtain ⟨J, g, s, hgi, hgl, hcard, hsq⟩ := exists_iid_sq_proj hind hZ K
  simp_rw [hsq, ← hcard]
  exact chiSq_upper_tail hgi hgl s ht

/-- Moment generating function of the squared norm of a projected standard Gaussian. -/
theorem proj_sq_mgf [IsProbabilityMeasure P] {ι : Type uX} [Fintype ι]
    {Z : ι → Ω → ℝ} (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (K : Submodule ℝ (EuclideanSpace ℝ ι)) {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun ω => ‖K.starProjection (WithLp.toLp 2 (fun i => Z i ω) : EuclideanSpace ℝ ι)‖ ^ 2)
      P t = (Real.sqrt (1 - 2 * t))⁻¹ ^ Module.finrank ℝ K := by
  obtain ⟨J, g, s, hgi, hgl, hcard, hsq⟩ := exists_iid_sq_proj hind hZ K
  simp_rw [hsq, ← hcard]
  exact mgf_sum_sq_stdGaussian hgi hgl s ht

end GaussianProjection

/-! ### Least squares under a fixed design -/

section OLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The observation map of a list of features: `v ↦ (⟪f i, v⟫)_i`. -/
noncomputable def obsMap {ι : Type*} [Fintype ι] (f : ι → E) : E →ₗ[ℝ] EuclideanSpace ℝ ι :=
  designMap f (fun _ => 1)

lemma obsMap_apply {ι : Type*} [Fintype ι] (f : ι → E) (v : E) (i : ι) :
    obsMap f v i = ⟪f i, v⟫ := by
  simp [obsMap, designMap_apply]

/-- The Gram operator `v ↦ ∑_i ⟪f i, v⟫ f i`. -/
noncomputable def gramOp {ι : Type*} [Fintype ι] (f : ι → E) : E →ₗ[ℝ] E :=
  ∑ i, (innerₗ E (f i)).smulRight (f i)

lemma gramOp_apply {ι : Type*} [Fintype ι] (f : ι → E) (v : E) :
    gramOp f v = ∑ i, ⟪f i, v⟫ • f i := by
  simp [gramOp, LinearMap.sum_apply]

lemma inner_gramOp {ι : Type*} [Fintype ι] (f : ι → E) (h v : E) :
    ⟪gramOp f h, v⟫ = ⟪obsMap f h, obsMap f v⟫ := by
  rw [obsMap, inner_designMap f (fun _ => zero_le_one), gramOp_apply]
  simp

lemma inner_toLp_obsMap {ι : Type*} [Fintype ι] (f : ι → E) (y : ι → ℝ) (v : E) :
    ⟪(WithLp.toLp 2 y : EuclideanSpace ℝ ι), obsMap f v⟫ = ⟪∑ i, y i • f i, v⟫ := by
  rw [PiLp.inner_apply, sum_inner]
  refine sum_congr rfl (fun i _ => ?_)
  rw [obsMap_apply, real_inner_smul_left]
  simp [mul_comm]

/-- The least-squares estimate: the solution of the normal equations
`(∑_i f_i f_iᵀ) θ̂ = ∑_i y_i f_i`. -/
noncomputable def olsEst {ι : Type*} [Fintype ι] (f : ι → E) (y : ι → ℝ) : E :=
  Function.invFun (gramOp f) (∑ i, y i • f i)

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma gramOp_injective {ι : Type*} [Fintype ι] (f : ι → E)
    (hinj : Function.Injective (obsMap f)) : Function.Injective (gramOp f) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 : ⟪gramOp f v, v⟫ = 0 := by rw [hv, inner_zero_left]
  rw [inner_gramOp, real_inner_self_eq_norm_sq] at h1
  have h2 : obsMap f v = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    exact norm_eq_zero.mp this
  exact (injective_iff_map_eq_zero (obsMap f)).mp hinj v h2

/-- The estimate solves the normal equations when the Gram matrix is positive definite. -/
lemma olsEst_normal {ι : Type*} [Fintype ι] (f : ι → E)
    (hinj : Function.Injective (obsMap f)) (y : ι → ℝ) :
    gramOp f (olsEst f y) = ∑ i, y i • f i :=
  Function.invFun_eq (LinearMap.injective_iff_surjective.mp (gramOp_injective f hinj) _)

/-- **The least-squares error is a projection of the noise.**  With observations
`y_i = ⟪f_i, θ⟫ + ξ_i`, `B (θ̂ - θ) = P_{range B} ξ` for the observation map `B`. -/
theorem ols_error_proj {ι : Type*} [Fintype ι] (f : ι → E)
    (hinj : Function.Injective (obsMap f)) (θ : E) (ξ : ι → ℝ) :
    obsMap f (olsEst f (fun i => ⟪f i, θ⟫ + ξ i) - θ) =
      (LinearMap.range (obsMap f)).starProjection (WithLp.toLp 2 ξ : EuclideanSpace ℝ ι) := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
  rintro _ ⟨v, rfl⟩
  rw [inner_sub_left, inner_toLp_obsMap, ← inner_gramOp, map_sub, olsEst_normal f hinj,
    gramOp_apply, ← inner_sub_left]
  have : ∑ i, ξ i • f i - (∑ i, (⟪f i, θ⟫ + ξ i) • f i - ∑ i, ⟪f i, θ⟫ • f i) = 0 := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_eq_zero (fun i _ => by rw [add_smul]; abel)
  rw [this, inner_zero_left]

variable {X : Type uX} [Fintype X]

/-- Least squares from the first `c x` observations of each query `x` of a tape `Y`. -/
noncomputable def olsCount (u : X → E) (c : X → ℕ) (Y : X → ℕ → ℝ) : E :=
  olsEst (fun p : Σ x, Fin (c x) => u p.1) (fun p => Y p.1 p.2)

omit [FiniteDimensional ℝ E] in
lemma norm_obsMap_sigma (u : X → E) (c : X → ℕ) (v : E) :
    ‖obsMap (fun p : Σ x, Fin (c x) => u p.1) v‖ ^ 2 =
      ‖designMap u (fun x => (c x : ℝ)) v‖ ^ 2 := by
  rw [obsMap, norm_designMap_sq _ (fun _ => zero_le_one),
    norm_designMap_sq _ (fun x => Nat.cast_nonneg (c x)), Fintype.sum_sigma]
  refine sum_congr rfl (fun x _ => ?_)
  simp

omit [FiniteDimensional ℝ E] in
lemma obsMap_sigma_injective (u : X → E) (c : X → ℕ)
    (hinj : Function.Injective (designMap u (fun x => (c x : ℝ)))) :
    Function.Injective (obsMap (fun p : Σ x, Fin (c x) => u p.1)) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 := norm_obsMap_sigma u c v
  rw [hv, norm_zero, zero_pow two_ne_zero] at h1
  have h2 : designMap u (fun x => (c x : ℝ)) v = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1.symm)
  exact (injective_iff_map_eq_zero _).mp hinj v h2

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- The observation tape of the Gaussian linear model: `Y x i = ⟪u x, θ⟫ + ξ x i`. -/
def obsTape (u : X → E) (θ : E) (ξ : X → ℕ → Ω → ℝ) (ω : Ω) : X → ℕ → ℝ :=
  fun x i => ⟪u x, θ⟫ + ξ x i ω

/-- **Law of the least-squares error under a fixed design** (proof of
`thm:v10g-discovery`, "the OLS error in its Gram norm has squared norm `χ²_d`").  For a
deterministic design with counts `c` and positive definite Gram matrix `G = ∑ c_x u_x u_xᵀ`,
`‖θ̂ - θ‖²_G` is a sum of `d = finrank E` independent squared standard Gaussians. -/
theorem ols_error_chiSq [IsProbabilityMeasure P] (u : X → E) (c : X → ℕ)
    (hinj : Function.Injective (designMap u (fun x => (c x : ℝ))))
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) :
    ∃ (J : Type uX) (g : J → Ω → ℝ) (s : Finset J), iIndepFun g P ∧
      (∀ j, HasLaw (g j) (gaussianReal 0 1) P) ∧ s.card = Module.finrank ℝ E ∧
      ∀ ω, ‖designMap u (fun x => (c x : ℝ)) (olsCount u c (obsTape u θ ξ ω) - θ)‖ ^ 2 =
        ∑ j ∈ s, g j ω ^ 2 := by
  have hB := obsMap_sigma_injective u c hinj
  have hemb : Function.Injective (fun p : Σ x, Fin (c x) => ((p.1, (p.2 : ℕ)) : X × ℕ)) := by
    rintro ⟨x, i⟩ ⟨x', i'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [Fin.val_inj.mp h2]
  have hind' : iIndepFun (fun p : Σ x, Fin (c x) => ξ p.1 p.2) P := hind.precomp hemb
  obtain ⟨J, g, s, hgi, hgl, hcard, hsq⟩ := exists_iid_sq_proj hind'
    (fun p => hξ p.1 p.2) (LinearMap.range (obsMap (fun p : Σ x, Fin (c x) => u p.1)))
  refine ⟨J, g, s, hgi, hgl, ?_, fun ω => ?_⟩
  · rw [hcard, LinearMap.finrank_range_of_inj hB]
  · rw [← hsq ω, ← norm_obsMap_sigma, olsCount]
    congr 1
    rw [← ols_error_proj _ hB θ]
    rfl

/-- **Chi-square tail of the least-squares error** (`app:bay-finite`,
`ℙ{½ χ²_d > ψ_d(t)} ≤ e^{-t}`, for the statistic `Q = ½ ‖θ̂ - θ‖²_G` of a fixed design). -/
theorem ols_chi_tail [IsProbabilityMeasure P] (u : X → E) (c : X → ℕ)
    (hinj : Function.Injective (designMap u (fun x => (c x : ℝ))))
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | psiD (Module.finrank ℝ E) t ≤
      ‖designMap u (fun x => (c x : ℝ)) (olsCount u c (obsTape u θ ξ ω) - θ)‖ ^ 2 / 2} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  obtain ⟨J, g, s, hgi, hgl, hcard, hsq⟩ := ols_error_chiSq u c hinj hind hξ θ
  have h := chiSq_upper_tail hgi hgl s ht
  rw [hcard] at h
  rw [← ofReal_measureReal]
  refine (ENNReal.ofReal_le_ofReal ?_).trans (ENNReal.ofReal_le_ofReal h)
  refine measureReal_mono (fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [← hsq ω]
  unfold psiD at hω
  linarith

/-- **Moment generating function of the least-squares error** (proof of
`prop:v10g-safety-fallback`, `𝔼 e^{Q/2} = 2^{d/2}` for `Q = ½ ‖θ̂ - θ‖²_G`). -/
theorem ols_mgf_half [IsProbabilityMeasure P] (u : X → E) (c : X → ℕ)
    (hinj : Function.Injective (designMap u (fun x => (c x : ℝ))))
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
      (‖designMap u (fun x => (c x : ℝ)) (olsCount u c (obsTape u θ ξ ω) - θ)‖ ^ 2 / 2 / 2)) ∂P =
      ENNReal.ofReal ((2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2)) := by
  obtain ⟨J, g, s, hgi, hgl, hcard, hsq⟩ := ols_error_chiSq u c hinj hind hξ θ
  have ht : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hm := mgf_sum_sq_stdGaussian hgi hgl s ht
  have hint := integrable_exp_mul_sum_sq hgi hgl s ht
  have hfun : ∀ ω, Real.exp (‖designMap u (fun x => (c x : ℝ))
      (olsCount u c (obsTape u θ ξ ω) - θ)‖ ^ 2 / 2 / 2) =
      Real.exp (1 / 4 * ∑ j ∈ s, g j ω ^ 2) := by
    intro ω
    rw [hsq ω]
    congr 1
    ring
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
  congr 1
  unfold mgf at hm
  rw [hm, hcard]
  have h12 : (1 : ℝ) - 2 * (1 / 4) = 1 / 2 := by norm_num
  rw [h12, ← Real.sqrt_inv, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

end OLS

/-! ### `thm:v10g-discovery`: the deterministic pilot -/

section Discovery

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {𝒜 : Type*}

/-- The information `I_a(v, w) = inf_{λ ∈ Q_a} ½ ‖λ - v‖²_{M(w)}` (`rootInfo_isGLB`). -/
noncomputable def gInfo (u : X → E) (Q : Set E) (v : E) (w : X → ℝ) : ℝ :=
  rootInfo (designMap u w) Q v ^ 2 / 2

lemma gInfo_nonneg {u : X → E} {Q : Set E} {v : E} {w : X → ℝ} : 0 ≤ gInfo u Q v w := by
  unfold gInfo; positivity

lemma sqrt_gInfo (u : X → E) (Q : Set E) (v : E) (w : X → ℝ) :
    Real.sqrt (gInfo u Q v w) = rootInfo (designMap u w) Q v / Real.sqrt 2 := by
  unfold gInfo
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq rootInfo_nonneg]

/-- The square-root parameter modulus: `|√I_a(v, w) - √I_a(θ, w)| ≤ ℓ ‖v - θ‖ / √2`. -/
lemma sqrt_gInfo_modulus (u : X → E) {w : X → ℝ} (hw : w ∈ simplex X) {ℓ : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ ℓ) (Q : Set E) (v θ : E) :
    |Real.sqrt (gInfo u Q v w) - Real.sqrt (gInfo u Q θ w)| ≤ ℓ * ‖v - θ‖ / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [sqrt_gInfo, sqrt_gInfo, ← sub_div, abs_div, abs_of_pos h2]
  exact div_le_div_of_nonneg_right (rootInfo_design_lipschitz u hw hu Q v θ) h2.le

/-- The floored design `(1 - k) p + k w⁰`; `W_k` is its image of the simplex. -/
def floorDesign (k : ℝ) (w0 p : X → ℝ) : X → ℝ := fun x => (1 - k) * p x + k * w0 x

lemma floorDesign_mem {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) {w0 p : X → ℝ}
    (hw0 : w0 ∈ simplex X) (hp : p ∈ simplex X) : floorDesign k w0 p ∈ simplex X := by
  refine ⟨fun x => add_nonneg (mul_nonneg (sub_nonneg.mpr hk1) (hp.1 x))
    (mul_nonneg hk0 (hw0.1 x)), ?_⟩
  simp only [floorDesign]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hp.2, hw0.2]
  ring

/-- Rounded cumulative counts `⌈n w_x⌉`. -/
noncomputable def roundCount (w : X → ℝ) (n : ℝ) (x : X) : ℕ := ⌈n * w x⌉₊

lemma round_gram_dominates (u : X → E) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {n : ℝ} (hn : 0 ≤ n)
    (v : E) :
    Real.sqrt n * ‖designMap u w v‖ ≤ ‖designMap u (fun x => (roundCount w n x : ℝ)) v‖ :=
  gram_dominates u hw hn (fun _ => Nat.le_ceil _) v

lemma round_gram_lower (u : X → E) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {k0 : ℝ}
    (hM : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w v‖ ^ 2) {n : ℝ} (hn : 0 ≤ n) (v : E) :
    k0 * n * ‖v‖ ^ 2 ≤ ‖designMap u (fun x => (roundCount w n x : ℝ)) v‖ ^ 2 := by
  have h1 := pow_le_pow_left₀ (by positivity) (round_gram_dominates u hw hn v) 2
  rw [mul_pow, Real.sq_sqrt hn] at h1
  have h2 := mul_le_mul_of_nonneg_left (hM v) hn
  linarith

lemma round_gram_injective (u : X → E) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {k0 : ℝ} (hk0 : 0 < k0)
    (hM : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w v‖ ^ 2) {n : ℝ} (hn : 0 < n) :
    Function.Injective (designMap u (fun x => (roundCount w n x : ℝ))) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 := round_gram_lower u hw hM hn.le v
  rw [hv, norm_zero, zero_pow two_ne_zero] at h1
  have h2 : ‖v‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < k0 * n * ‖v‖ ^ 2 := by positivity
    linarith
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _)))

/-- `u_j = log((j + 1)(j + 2) / α)` of `eq:v10g-pilot-radius`. -/
noncomputable def pilotU (α : ℝ) (j : ℕ) : ℝ := Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2) / α)

/-- `ρ_j = √(2 ψ_d(u_j) / (k₀ 2^j))` of `eq:v10g-pilot-radius`. -/
noncomputable def pilotRho (d k0 α : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (2 * psiD d (pilotU α j) / (k0 * 2 ^ j))

lemma pilotU_nonneg {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (j : ℕ) : 0 ≤ pilotU α j := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hα0]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- **The numerical contract of the allocation oracle** (`eq:v10g-oracle`).  At stage `j`
and center `v` the oracle returns an action `oa j v`, a design `ow j v ∈ W_k`, and endpoints
`0 ≤ ol j v ≤ I_a(v, w) ≤ C_k(v) ≤ ou j v` with `ou j v - ol j v ≤ e_j²`.  The inequality
`C_k(v) ≤ ou j v` is stated as `I_{a'}(v, w') ≤ ou j v` for every action `a'` and every
`w' ∈ W_k`. -/
structure OracleContract (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k : ℝ) (e : ℕ → ℝ)
    (oa : ℕ → E → 𝒜) (ow : ℕ → E → X → ℝ) (ol ou : ℕ → E → ℝ) : Prop where
  design_mem : ∀ j v, ∃ p ∈ simplex X, ow j v = floorDesign k w0 p
  lo_nonneg : ∀ j v, 0 ≤ ol j v
  lo_le : ∀ j v, ol j v ≤ gInfo u (Q (oa j v)) v (ow j v)
  le_hi : ∀ j v a, ∀ p ∈ simplex X, gInfo u (Q a) v (floorDesign k w0 p) ≤ ou j v
  gap : ∀ j v, ou j v - ol j v ≤ e j ^ 2

/-- **Commitment and the frozen plan, deterministic part of `thm:v10g-discovery`.**
Let `v j` be any sequence of centers with `‖v j - θ‖ ≤ ρ_j` for all `j` (the pilot good
event), let the tolerances satisfy `ℓ ρ_j / √2 ≤ e_j ≤ √2 ℓ ρ_j`, and let the oracle obey
`eq:v10g-oracle`.  Let `C` be at most `I_{a}(θ, w)` for some action `a` and design `w` (in
particular `C = max_{a,w} I_a(θ, w)`), `C > 0`.  Then the gate `e_j² ≤ k² l_j` of
`eq:v10g-gate` is passed at a first stage `j`; the record frozen there satisfies
`eq:v10g-plan-rate`; and the cumulative pilot counts `∑_x ⌈2^j w⁰_x⌉` are at most
`D̄` of `eq:v10g-discovery-budget` with `q = |X|`. -/
theorem pilot_commit (u : X → E) (Q : 𝒜 → Set E) (hQ : ∀ a, (Q a).Nonempty)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 k α d : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0) (hk : 0 < k) (hk1 : k < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hd : 0 ≤ d)
    {e : ℕ → ℝ} (he1 : ∀ j, ℓ * pilotRho d k0 α j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho d k0 α j)
    {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u Q w0 k e oa ow ol ou)
    (θ : E) (aS : 𝒜) {wS : X → ℝ} (hwS : wS ∈ simplex X) {C : ℝ} (hC : 0 < C)
    (hCle : C ≤ gInfo u (Q aS) θ wS)
    (v : ℕ → E) (hv : ∀ j, ‖v j - θ‖ ≤ pilotRho d k0 α j) :
    ∃ j, e j ^ 2 ≤ k ^ 2 * ol j (v j) ∧ (∀ i < j, ¬ e i ^ 2 ≤ k ^ 2 * ol i (v i)) ∧
      cstar k * C ≤ (Real.sqrt (ol j (v j)) - e j) ^ 2 ∧
      (Real.sqrt (ol j (v j)) - e j) ^ 2 ≤ gInfo u (Q (oa j (v j))) θ (ow j (v j)) ∧
      (∑ x, (roundCount w0 (2 ^ j) x : ℝ)) ≤
        Dbar (pilotA ℓ k0 k C) d α (Fintype.card X) := by
  classical
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hfloor : (1 - k) * C ≤ gInfo u (Q aS) θ (floorDesign k w0 wS) := by
    have h := floor_rate_loss u hwS.1 hw0.1 hk.le hk1.le (hQ aS) θ
      (C := gInfo u (Q aS) θ wS) le_rfl
    have h' : gInfo u (Q aS) θ wS - k * gInfo u (Q aS) θ wS ≤
        gInfo u (Q aS) θ (floorDesign k w0 wS) := h
    nlinarith
  have hρ0 : ∀ j, 0 ≤ pilotRho d k0 α j := fun j => Real.sqrt_nonneg _
  have he0 : ∀ j, 0 ≤ e j := fun j =>
    (div_nonneg (mul_nonneg hℓ.le (hρ0 j)) h2.le).trans (he1 j)
  have hmodulus : ∀ j a w, w ∈ simplex X →
      |Real.sqrt (gInfo u (Q a) (v j) w) - Real.sqrt (gInfo u (Q a) θ w)| ≤ e j :=
    fun j a w hw => (sqrt_gInfo_modulus u hw hu (Q a) (v j) θ).trans
      ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hv j) hℓ.le) h2.le).trans (he1 j))
  have hwSk : floorDesign k w0 wS ∈ simplex X := floorDesign_mem hk.le hk1.le hw0 hwS
  have horacle : ∀ j, Real.sqrt (gInfo u (Q aS) θ (floorDesign k w0 wS)) - 2 * e j ≤
      Real.sqrt (ol j (v j)) := fun j => by
    refine oracle_root_lower (hor.lo_nonneg j (v j)) (he0 j)
      (Ckv := gInfo u (Q aS) (v j) (floorDesign k w0 wS)) ?_ ?_
    · have h3 := hor.le_hi j (v j) aS wS hwS
      have h4 := hor.gap j (v j)
      linarith
    · have h3 := (abs_sub_le_iff.mp (hmodulus j aS _ hwSk)).2
      linarith
  have hesq : ∀ j, e j ^ 2 ≤
      4 * ℓ ^ 2 * psiD d (Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2) / α)) / (k0 * 2 ^ j) := fun j => by
    have hψ : 0 ≤ psiD d (pilotU α j) := psiD_nonneg hd (pilotU_nonneg hα0 hα1 j)
    have h1 := pow_le_pow_left₀ (he0 j) (he2 j) 2
    have h3 : (Real.sqrt 2 * ℓ * pilotRho d k0 α j) ^ 2 =
        4 * ℓ ^ 2 * psiD d (pilotU α j) / (k0 * 2 ^ j) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), pilotRho,
        Real.sq_sqrt (div_nonneg (by linarith) (by positivity))]
      ring
    rw [h3] at h1
    exact h1
  have hApos : 0 < pilotA ℓ k0 k C := by
    have : 0 < 1 - k := by linarith
    unfold pilotA
    positivity
  have haD : 0 ≤ aD (pilotA ℓ k0 k C) d α := by
    have := Real.log_nonneg ((one_le_div hα0).mpr hα1)
    unfold aD
    positivity
  obtain ⟨j0, hj0, hj0'⟩ := exists_pilot_stage haD
    (le_max_left 1 (4 * pilotA ℓ k0 k C) : 1 ≤ bDm (pilotA ℓ k0 k C))
  have hgate0 : e j0 ^ 2 ≤ k ^ 2 * ol j0 (v j0) := by
    have hsmall := pilot_budget_sufficient hℓ hk0 hk hk1 hC hd hα0 hα1 (he0 j0) (hesq j0)
      hfloor hj0
    exact pilot_gate_succeeds hk (he0 j0) (hor.lo_nonneg _ _) (horacle j0) hsmall
  have hex : ∃ j, e j ^ 2 ≤ k ^ 2 * ol j (v j) := ⟨j0, hgate0⟩
  have hjgate := Nat.find_spec hex
  have hjle : Nat.find hex ≤ j0 := Nat.find_min' hex hgate0
  refine ⟨Nat.find hex, hjgate, fun i hi => Nat.find_min hex hi, ?_⟩
  obtain ⟨p, hp, hpe⟩ := hor.design_mem (Nat.find hex) (v (Nat.find hex))
  have hwmem : ow (Nat.find hex) (v (Nat.find hex)) ∈ simplex X := by
    rw [hpe]; exact floorDesign_mem hk.le hk1.le hw0 hp
  have hmod : Real.sqrt (ol (Nat.find hex) (v (Nat.find hex))) - e (Nat.find hex) ≤
      Real.sqrt (gInfo u (Q (oa (Nat.find hex) (v (Nat.find hex)))) θ
        (ow (Nat.find hex) (v (Nat.find hex)))) := by
    have h1 := Real.sqrt_le_sqrt (hor.lo_le (Nat.find hex) (v (Nat.find hex)))
    have h3 := (abs_sub_le_iff.mp (hmodulus (Nat.find hex)
      (oa (Nat.find hex) (v (Nat.find hex))) _ hwmem)).1
    linarith
  obtain ⟨hr1, hr2⟩ := frozen_plan_rate hk hk1.le (he0 _) (hor.lo_nonneg _ _) hC.le gInfo_nonneg
    hjgate (horacle _) hfloor hmod
  refine ⟨hr1, hr2, ?_⟩
  have hs := (sum_ceil_counts hw0 (n := (2 : ℝ) ^ Nat.find hex) (by positivity)).2
  have hpow : (2 : ℝ) ^ Nat.find hex ≤ 2 ^ j0 := pow_le_pow_right₀ (by norm_num) hjle
  unfold Dbar bDm
  simp only [roundCount]
  linarith

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Pilot concentration** (`thm:v10g-discovery`, first sentence).  In the Gaussian linear
model with a tape of independent standard Gaussian noises, the least-squares estimates
`v_j` from the deterministic pilot designs `⌈2^j w⁰_x⌉` satisfy `‖v_j - θ‖₂ ≤ ρ_j` for all
`j` simultaneously, except on an event of probability at most `α`.  The only hypotheses
are on the model: `M(w⁰) ⪰ k₀ I` and the noise law. -/
theorem pilot_concentration [FiniteDimensional ℝ E] [IsProbabilityMeasure P] (u : X → E)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k0 : ℝ} (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    P {ω | ∃ j : ℕ, pilotRho (Module.finrank ℝ E) k0 α j <
      ‖olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω) - θ‖} ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (stage_union_bound P
    (fun j => {ω | psiD (Module.finrank ℝ E) (pilotU α j) ≤
      ‖designMap u (fun x => (roundCount w0 (2 ^ j) x : ℝ))
        (olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω) - θ)‖ ^ 2 / 2}) hα0
    (fun j => ols_chi_tail u _ (round_gram_injective u hw0.1 hk0 hM0 (by positivity)) hind hξ θ
      (pilotU_nonneg hα0 hα1 j)))
  rintro ω ⟨j, hj⟩
  rw [Set.mem_iUnion]
  refine ⟨j, ?_⟩
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_le] at hcon
  have := pilot_radius (designMap u (fun x => (roundCount w0 (2 ^ j) x : ℝ))) hk0
    (by positivity : (0 : ℝ) < 2 ^ j) (round_gram_lower u hw0.1 hM0 (by positivity)) hcon.le
  unfold pilotRho at hj
  linarith

/-- **Explicit discovery and a frozen near-optimal plan** (`thm:v10g-discovery`) for the
Gaussian linear model.

Model hypotheses: the reference design `w⁰` is in the simplex with `M(w⁰) ⪰ k₀ I`,
`‖u_x‖ ≤ ℓ`, the screened sets `Q a` are nonempty, and the pilot noise tape `ξ` consists of
independent standard Gaussians.  `d = finrank ℝ E`; `v_j` is the least-squares estimate
from the counts `⌈2^j w⁰_x⌉`.  The oracle contract `eq:v10g-oracle` is a hypothesis
(`hor`), as are the bounds on the tolerances `e_j`.

Conclusions.  (1) Except on an event of probability at most `α`, `‖v_j - θ‖ ≤ ρ_j` for all
`j`.  (2) On every path where these bounds hold, the gate is passed at a first stage `j`,
the frozen record satisfies `eq:v10g-plan-rate` with `C` any positive number that is at
most `I_a(θ, w)` for some `a` and `w` (in particular `max_{a,w} I_a(θ, w)`), and the pilot
used at most `D̄` observations. -/
theorem v10g_discovery [FiniteDimensional ℝ E] [IsProbabilityMeasure P] (u : X → E)
    (Q : 𝒜 → Set E) (hQ : ∀ a, (Q a).Nonempty)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 k α : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    (hk : 0 < k) (hk1 : k < 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    {e : ℕ → ℝ} (he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j)
    {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u Q w0 k e oa ow ol ou)
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P)
    (θ : E) (aS : 𝒜) {wS : X → ℝ} (hwS : wS ∈ simplex X) {C : ℝ} (hC : 0 < C)
    (hCle : C ≤ gInfo u (Q aS) θ wS) :
    P {ω | ¬ ∀ j : ℕ, ‖olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω) - θ‖ ≤
        pilotRho (Module.finrank ℝ E) k0 α j} ≤ ENNReal.ofReal α ∧
      ∀ ω, (∀ j : ℕ, ‖olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω) - θ‖ ≤
        pilotRho (Module.finrank ℝ E) k0 α j) →
        ∃ j, e j ^ 2 ≤ k ^ 2 * ol j (olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω)) ∧
          (∀ i < j, ¬ e i ^ 2 ≤
            k ^ 2 * ol i (olsCount u (roundCount w0 (2 ^ i)) (obsTape u θ ξ ω))) ∧
          cstar k * C ≤ (Real.sqrt (ol j (olsCount u (roundCount w0 (2 ^ j))
            (obsTape u θ ξ ω))) - e j) ^ 2 ∧
          (Real.sqrt (ol j (olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω))) - e j) ^ 2 ≤
            gInfo u (Q (oa j (olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω)))) θ
              (ow j (olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω))) ∧
          (∑ x, (roundCount w0 (2 ^ j) x : ℝ)) ≤
            Dbar (pilotA ℓ k0 k C) (Module.finrank ℝ E) α (Fintype.card X) := by
  refine ⟨?_, fun ω hω => ?_⟩
  · refine (measure_mono ?_).trans (pilot_concentration u hw0 hk0 hM0 hind hξ θ hα0 hα1)
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω ⊢
    exact hω
  · exact pilot_commit u Q hQ hw0 hℓ hu hk0 hk hk1 hα0 hα1 (Nat.cast_nonneg _) he1 he2 hor θ aS
      hwS hC hCle (fun j => olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξ ω)) hω

end Discovery

/-! ### `prop:v10g-safety-fallback`: fresh designs, safety, and the safeguard mean -/

section Fresh

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- `Q_n = ½ ‖θ̂_n - θ‖²_{G_n}` for the fresh design with counts `⌈n w_x⌉` and tape `Y`. -/
noncomputable def freshQ (u : X → E) (w : X → ℝ) (θ : E) (Y : X → ℕ → ℝ) (n : ℕ) : ℝ :=
  ‖designMap u (fun x => (roundCount w n x : ℝ)) (olsCount u (roundCount w n) Y - θ)‖ ^ 2 / 2

omit [FiniteDimensional ℝ E] in
lemma freshQ_nonneg (u : X → E) (w : X → ℝ) (θ : E) (Y : X → ℕ → ℝ) (n : ℕ) :
    0 ≤ freshQ u w θ Y n := by
  unfold freshQ; positivity

lemma boundary_succ (d β : ℝ) (j : ℕ) :
    boundary d ((j + 1 : ℕ) : ℝ) β = psiD d (Real.log (((j : ℝ) + 1) * ((j : ℝ) + 2) / β)) := by
  unfold boundary
  congr 2
  push_cast
  ring

lemma boundary_pos {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) : 0 < boundary d n β := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (2 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / β := by
    rw [le_div_iff₀ hβ0]
    nlinarith
  have h2 : 0 < Real.log ((n : ℝ) * ((n : ℝ) + 1) / β) := Real.log_pos (by linarith)
  unfold boundary psiD
  have := Real.sqrt_nonneg (d * Real.log ((n : ℝ) * ((n : ℝ) + 1) / β))
  linarith [div_nonneg hd (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Simultaneous ellipsoid coverage for a fresh fixed design** (proof of
`prop:v10g-safety-fallback`: "a union bound with risks `β/(n(n+1))` gives simultaneous
ellipsoid coverage with probability at least `1 - β`").  For a design `w` with
`M(w) ⪰ κ I`, `κ > 0`, and a tape of independent standard Gaussians: except with
probability `β`, `Q_n < B(n, β)` for every `n ≥ 1`. -/
theorem fresh_coverage [IsProbabilityMeasure P] (u : X → E) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    {κ : ℝ} (hκ : 0 < κ) (hM : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖designMap u w v‖ ^ 2)
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    P {ω | ∃ n : ℕ, 1 ≤ n ∧
      boundary (Module.finrank ℝ E) n β ≤ freshQ u w θ (obsTape u θ ξ ω) n} ≤
      ENNReal.ofReal β := by
  refine (measure_mono ?_).trans (stage_union_bound P
    (fun j => {ω | boundary (Module.finrank ℝ E) ((j + 1 : ℕ) : ℝ) β ≤
      freshQ u w θ (obsTape u θ ξ ω) (j + 1)}) hβ0 (fun j => ?_))
  · rintro ω ⟨n, hn, h⟩
    rw [Set.mem_iUnion]
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    exact ⟨j, h⟩
  · simp only [boundary_succ]
    exact ols_chi_tail u _ (round_gram_injective u hw hκ hM (by positivity)) hind hξ θ
      (pilotU_nonneg hβ0 hβ1 j)

lemma sqrt_half_inv_pow (n : ℕ) :
    (Real.sqrt (1 - 2 * (1 / 4)))⁻¹ ^ n = (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have h12 : (1 : ℝ) - 2 * (1 / 4) = 1 / 2 := by norm_num
  rw [h12, ← Real.sqrt_inv, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- **Chernoff bound for the least-squares error** (proof of `prop:v10g-safety-fallback`):
`ℙ(Q > x) ≤ 2^{d/2} e^{-x/2}` for `Q = ½ ‖θ̂ - θ‖²_G` under a fixed design. -/
theorem ols_chernoff [IsProbabilityMeasure P] (u : X → E) (c : X → ℕ)
    (hinj : Function.Injective (designMap u (fun x => (c x : ℝ))))
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) (x : ℝ) :
    P {ω | x < ‖designMap u (fun x => (c x : ℝ))
        (olsCount u c (obsTape u θ ξ ω) - θ)‖ ^ 2 / 2} ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) * Real.exp (-x / 2)) := by
  obtain ⟨J, g, s, hgi, hgl, hcard, hsq⟩ := ols_error_chiSq u c hinj hind hξ θ
  have ht : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ j ∈ s, g j ω ^ 2)
    (2 * x) (by norm_num : (0 : ℝ) ≤ 1 / 4) (integrable_exp_mul_sum_sq hgi hgl s ht)
  rw [mgf_sum_sq_stdGaussian hgi hgl s ht, hcard, sqrt_half_inv_pow] at hch
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  calc P.real {ω | x < ‖designMap u (fun x => (c x : ℝ))
        (olsCount u c (obsTape u θ ξ ω) - θ)‖ ^ 2 / 2}
      ≤ P.real {ω | 2 * x ≤ ∑ j ∈ s, g j ω ^ 2} := by
        refine measureReal_mono (fun ω hω => ?_)
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [← hsq ω]
        linarith
    _ ≤ _ := hch
    _ = _ := by
        rw [mul_comm]
        congr 2
        ring

/-! #### Stopping times and observation counts -/

open Classical in
/-- The first index at which a predicate holds, `⊤` if it never does. -/
noncomputable def firstTime (p : ℕ → Prop) : ℕ∞ :=
  if h : ∃ n, p n then (Nat.find h : ℕ∞) else ⊤

lemma firstTime_le {p : ℕ → Prop} {n : ℕ} (h : p n) : firstTime p ≤ n := by
  classical
  unfold firstTime
  split_ifs with h'
  · exact_mod_cast Nat.find_min' h' h
  · exact absurd ⟨n, h⟩ h'

lemma firstTime_eq_top {p : ℕ → Prop} (h : ∀ n, ¬ p n) : firstTime p = ⊤ := by
  unfold firstTime
  split_ifs with h'
  · obtain ⟨n, hn⟩ := h'
    exact absurd hn (h n)
  · rfl

open Classical in
lemma firstTime_eq_find {p : ℕ → Prop} (h : ∃ n, p n) :
    firstTime p = (Nat.find h : ℕ∞) := by
  unfold firstTime
  split_ifs
  rfl

/-- Observations used by the rounded design `⌈n w_x⌉` at the nominal count `N`
(`⊤` if `N = ⊤`). -/
noncomputable def roundTotal (w : X → ℝ) (N : ℕ∞) : ℝ≥0∞ :=
  if N = ⊤ then ⊤ else ((∑ x, roundCount w ((N.toNat : ℕ) : ℝ) x : ℕ) : ℝ≥0∞)

lemma roundTotal_coe (w : X → ℝ) (n : ℕ) :
    roundTotal w (n : ℕ∞) = ((∑ x, roundCount w (n : ℝ) x : ℕ) : ℝ≥0∞) := by
  simp [roundTotal]

lemma sum_roundCount_le {w : X → ℝ} (hw : w ∈ simplex X) (n : ℕ) :
    ∑ x, roundCount w (n : ℝ) x ≤ n + Fintype.card X := by
  have h := (sum_ceil_counts hw (n := (n : ℝ)) (Nat.cast_nonneg n)).2
  have h' : ((∑ x, roundCount w (n : ℝ) x : ℕ) : ℝ) ≤ ((n + Fintype.card X : ℕ) : ℝ) := by
    push_cast
    exact h
  exact_mod_cast h'

omit [FiniteDimensional ℝ E] [Fintype X] in
lemma measurable_obsTape (u : X → E) (θ : E) {ξ : X → ℕ → Ω → ℝ}
    (hξm : ∀ x i, Measurable (ξ x i)) : Measurable (obsTape u θ ξ) :=
  measurable_pi_iff.mpr (fun x => measurable_pi_iff.mpr (fun i => (hξm x i).const_add _))

omit [FiniteDimensional ℝ E] in
/-- A floored design has `M(w) ⪰ k k₀ I`. -/
lemma floor_gram_lower (u : X → E) {w0 p : X → ℝ} (hw0 : ∀ x, 0 ≤ w0 x) (hp : ∀ x, 0 ≤ p x)
    {k k0 : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    (v : E) : k * k0 * ‖v‖ ^ 2 ≤ ‖designMap u (floorDesign k w0 p) v‖ ^ 2 := by
  have hnn : ∀ x, 0 ≤ floorDesign k w0 p x := fun x =>
    add_nonneg (mul_nonneg (sub_nonneg.mpr hk1) (hp x)) (mul_nonneg hk (hw0 x))
  rw [norm_designMap_sq u hnn]
  have h1 := mul_le_mul_of_nonneg_left (hM0 v) hk
  rw [norm_designMap_sq u hw0, mul_sum] at h1
  have h2 : ∑ x, k * (w0 x * ⟪u x, v⟫ ^ 2) ≤ ∑ x, floorDesign k w0 p x * ⟪u x, v⟫ ^ 2 := by
    refine sum_le_sum (fun x _ => ?_)
    have : 0 ≤ (1 - k) * p x * ⟪u x, v⟫ ^ 2 :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hk1) (hp x)) (sq_nonneg _)
    simp only [floorDesign]
    nlinarith
  linarith

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {𝒜 : Type*}

/-- Deterministic certification step shared by both branches: a statistic `S ≥ H > 0`
that lower-bounds `½ ‖λ - θ̂‖²_G` over the strict alternatives of `a`, together with
ellipsoid coverage `½ ‖θ̂ - θ‖²_G < H`, makes `a` `ε`-acceptable at `θ`. -/
lemma certify_of_stat {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (φ : Z → E) {S : Finset Z} (hS : S.Nonempty) {ε : ℝ} (G : E →ₗ[ℝ] F)
    (hG : Function.Injective G) {θhat θ : E} {H St : ℝ} (hH : 0 < H) (hHS : H ≤ St)
    (hstat : ∀ lam ∈ strictAlt φ S hS ε, St ≤ ‖G (lam - θhat)‖ ^ 2 / 2)
    (hcov : ‖G (θhat - θ)‖ ^ 2 / 2 < H) : regret S hS (env φ θ) ≤ ε := by
  refine certified_of_threshold hS G hG hH (fun lam hl => hHS.trans (hstat lam hl)) ?_
  have : ‖G (θ - θhat)‖ = ‖G (θhat - θ)‖ := by rw [← neg_sub, map_neg, norm_neg]
  rw [this]
  exact hcov.le

/-- The stopping predicate of the reference safeguard at nominal count `n`: some action
has its lower distance enclosure above the upper boundary enclosure. -/
def sgStop (Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ) (Bbar : ℕ → ℝ) (Y : X → ℕ → ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ a, Bbar n ≤ Jlow n Y a

/-- **The reference safeguard is `(ε, δ/2)`-safe** (`prop:v10g-safety-fallback`).  The
safeguard uses the counts `⌈n w⁰_x⌉` of its own tape, lower enclosures `Jlow n Y a` of the
action distances `J_n(a) = inf_{λ ∈ Q_a} ½ ‖λ - θ̂_n‖²_{G_n}` and upper enclosures `Bbar n`
of `B(n, δ/2)`.  Except with probability `δ/2`, no action that is ever certified
(`Bbar n ≤ Jlow n Y a` at some `n ≥ 1`) has regret above `ε`. -/
theorem safeguard_safe [IsProbabilityMeasure P] (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (u : X → E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X)
    {k0 : ℝ} (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ} {Bbar : ℕ → ℝ}
    (hJ : ∀ n Y a, Jlow n Y a ≤ gInfo u (strictAlt φ (supp a) (hne a) ε)
      (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ)))
    (hB : ∀ n : ℕ, boundary (Module.finrank ℝ E) n (δ / 2) ≤ Bbar n) :
    P {ω | ∃ n : ℕ, 1 ≤ n ∧ ∃ a, Bbar n ≤ Jlow n (obsTape u θ ξ ω) a ∧
      ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal (δ / 2) := by
  refine (measure_mono ?_).trans (fresh_coverage u hw0.1 hk0 hM0 hind hξ θ
    (by linarith : (0 : ℝ) < δ / 2) (by linarith))
  rintro ω ⟨n, hn, a, hcert, hbad⟩
  refine ⟨n, hn, ?_⟩
  by_contra hcon
  push Not at hcon
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstat : ∀ lam ∈ strictAlt φ (supp a) (hne a) ε,
      gInfo u (strictAlt φ (supp a) (hne a) ε) (olsCount u (roundCount w0 n) (obsTape u θ ξ ω))
        (fun x => (roundCount w0 n x : ℝ)) ≤
      ‖designMap u (fun x => (roundCount w0 n x : ℝ))
        (lam - olsCount u (roundCount w0 n) (obsTape u θ ξ ω))‖ ^ 2 / 2 := fun lam hl => by
    have h1 := pow_le_pow_left₀ rootInfo_nonneg
      (rootInfo_le (A := designMap u (fun x => (roundCount w0 n x : ℝ)))
        (θ := olsCount u (roundCount w0 n) (obsTape u θ ξ ω)) hl) 2
    unfold gInfo
    linarith
  have := certify_of_stat φ (hne a) (ε := ε)
    (designMap u (fun x => (roundCount w0 n x : ℝ)))
    (round_gram_injective u hw0.1 hk0 hM0 hn0)
    (boundary_pos (Nat.cast_nonneg _) hn (by linarith : (0 : ℝ) < δ / 2) (by linarith))
    ((hB n).trans (hcert.trans (hJ n _ a))) hstat hcon
  linarith

/-- `Z_n = n [√l - ‖θ̂_n - v‖_{M(w)} / √2]_+²` of `eq:v10g-recycle`, for the fresh design `w`
with tape `Y` and the frozen pilot record `(v, l)`. -/
noncomputable def confirmZ (u : X → E) (w : X → ℝ) (v : E) (l : ℝ) (Y : X → ℕ → ℝ) (n : ℕ) : ℝ :=
  n * (max (Real.sqrt l - ‖designMap u w (olsCount u (roundCount w n) Y - v)‖ / Real.sqrt 2) 0) ^ 2

/-- **Conditional safety of the fresh confirmation branch** (`prop:v10g-safety-fallback`,
first sentence).  Fix any frozen record: an action `a`, a design `w ∈ W_k`, a center `v`
and a number `l ≤ I_a(v, w)`.  (This is what conditioning on a pilot history leaves; no
accuracy of the pilot and no property of the gate is assumed.)  With a fresh tape of
independent standard Gaussians, except with probability `δ/2` the statistic `Z_n` never
reaches an upper enclosure `Bbar n ≥ B(n, δ/2)` unless `a` is `ε`-acceptable. -/
theorem confirm_safe_fixed [IsProbabilityMeasure P] (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (u : X → E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X)
    {k0 k : ℝ} (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    (hk : 0 < k) (hk1 : k ≤ 1)
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (θ : E) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) {Bbar : ℕ → ℝ}
    (hB : ∀ n : ℕ, boundary (Module.finrank ℝ E) n (δ / 2) ≤ Bbar n)
    (a : 𝒜) {p : X → ℝ} (hp : p ∈ simplex X) (v : E) {l : ℝ}
    (hl : l ≤ gInfo u (strictAlt φ (supp a) (hne a) ε) v (floorDesign k w0 p)) :
    P {ω | ∃ n : ℕ, 1 ≤ n ∧ Bbar n ≤ confirmZ u (floorDesign k w0 p) v l (obsTape u θ ξ ω) n ∧
      ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal (δ / 2) := by
  have hwnn : ∀ x, 0 ≤ floorDesign k w0 p x := (floorDesign_mem hk.le hk1 hw0 hp).1
  have hMw := floor_gram_lower u hw0.1 hp.1 hk.le hk1 hM0
  refine (measure_mono ?_).trans (fresh_coverage u hwnn (mul_pos hk hk0) hMw hind hξ θ
    (by linarith : (0 : ℝ) < δ / 2) (by linarith))
  rintro ω ⟨n, hn, hcert, hbad⟩
  refine ⟨n, hn, ?_⟩
  by_contra hcon
  push Not at hcon
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlQ : ∀ lam ∈ strictAlt φ (supp a) (hne a) ε,
      l ≤ ‖designMap u (floorDesign k w0 p) (lam - v)‖ ^ 2 / 2 := fun lam hlam => by
    have h1 := pow_le_pow_left₀ rootInfo_nonneg
      (rootInfo_le (A := designMap u (floorDesign k w0 p)) (θ := v) hlam) 2
    unfold gInfo at hl
    linarith
  have := certify_of_stat φ (hne a) (ε := ε)
    (designMap u (fun x => (roundCount (floorDesign k w0 p) n x : ℝ)))
    (round_gram_injective u hwnn (mul_pos hk hk0) hMw hn0)
    (boundary_pos (Nat.cast_nonneg _) hn (by linarith : (0 : ℝ) < δ / 2) (by linarith))
    ((hB n).trans hcert)
    (frozen_recycle (designMap u (floorDesign k w0 p))
      (designMap u (fun x => (roundCount (floorDesign k w0 p) n x : ℝ))) _ hn0.le
      (round_gram_dominates u hwnn hn0.le) hlQ) hcon
  linarith

omit [FiniteDimensional ℝ E] [Fintype X] in
lemma measurableSet_sgStop [Countable 𝒜] {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ} {Bbar : ℕ → ℝ}
    (hJm : ∀ n a, Measurable (fun Y : X → ℕ → ℝ => Jlow n Y a)) (n : ℕ) :
    MeasurableSet {Y : X → ℕ → ℝ | sgStop Jlow Bbar Y n} := by
  by_cases hn : 1 ≤ n
  · have : {Y : X → ℕ → ℝ | sgStop Jlow Bbar Y n} = ⋃ a, {Y | Bbar n ≤ Jlow n Y a} := by
      ext Y; simp [sgStop, hn]
    rw [this]
    exact MeasurableSet.iUnion (fun a => measurableSet_le measurable_const (hJm n a))
  · have : {Y : X → ℕ → ℝ | sgStop Jlow Bbar Y n} = ∅ := by
      ext Y; simp [sgStop, hn]
    rw [this]
    exact MeasurableSet.empty

/-- **The safeguard stops unless the noise is large** (proof of
`prop:v10g-safety-fallback`), on the model: for a nominal count `n ≥ x_F`, if
`Q_n ≤ n C₀ / 4` then the safeguard's test fires at `n`.  `C₀` is any positive number with
`C₀ ≤ I_{a₀}(θ, w⁰)` for some action `a₀`. -/
lemma safeguard_stops_det (u : X → E) (Q : 𝒜 → Set E) (hQ : ∀ a, (Q a).Nonempty)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) (θ : E) {d δ C0 : ℝ} (hd : 0 ≤ d) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (a0 : 𝒜) (hC0 : 0 < C0) (hC0le : C0 ≤ gInfo u (Q a0) θ w0)
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ} {Bbar : ℕ → ℝ}
    (hJ : ∀ (n : ℕ) Y a, gInfo u (Q a) (olsCount u (roundCount w0 n) Y)
      (fun x => (roundCount w0 n x : ℝ)) - 1 ≤ Jlow n Y a)
    (hB : ∀ n : ℕ, Bbar n ≤ boundary d n (δ / 2) + 1) {n : ℕ}
    (hn : logBudget (aF d δ C0) (bF C0) ≤ n) (Y : X → ℕ → ℝ)
    (hQle : freshQ u w0 θ Y n ≤ n * C0 / 4) : sgStop Jlow Bbar Y n := by
  have hb1 : (1 : ℝ) ≤ bF C0 := le_max_left _ _
  obtain ⟨-, hxb, -⟩ := log_budget_inversion (aF_nonneg hd hδ0 hδ1 hC0) hb1
  have hn1r : (1 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hn1r.le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsuff := (fallback_budget_sufficient hd hδ0 hδ1 hC0 hn).1
  have h1 := fallback_stops (freshQ_nonneg u w0 θ Y n) hsuff hQle
  have h2 : (max (Real.sqrt (n * gInfo u (Q a0) θ w0) - Real.sqrt (freshQ u w0 θ Y n)) 0) ^ 2 ≤
      gInfo u (Q a0) (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ)) :=
    reference_info_lower (designMap u w0) (designMap u (fun x => (roundCount w0 n x : ℝ)))
      (hQ a0) hn0 (round_gram_dominates u hw0.1 hn0) θ (olsCount u (roundCount w0 n) Y)
  have h3 : (max (Real.sqrt (n * C0) - Real.sqrt (freshQ u w0 θ Y n)) 0) ^ 2 ≤
      (max (Real.sqrt (n * gInfo u (Q a0) θ w0) - Real.sqrt (freshQ u w0 θ Y n)) 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 (sub_le_sub_right
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hC0le hn0)) _)) 2
  refine ⟨hn1, a0, ?_⟩
  have h4 := hJ n Y a0
  have h5 := hB n
  linarith

/-- **Finite mean of the reference safeguard** (`prop:v10g-safety-fallback`,
`𝔼_θ F_δ ≤ H_δ`) on the Gaussian linear model.  The safeguard stops at the first nominal
count `n ≥ 1` at which some action has `Bbar n ≤ Jlow n Y a`, where `Jlow` is a lower
enclosure of the action distances with absolute error at most one and
`Bbar n ≤ B(n, δ/2) + 1`.  Its observation count is `F_δ = ∑_x ⌈N w⁰_x⌉` at the stopping
count `N` (`⊤` if it never stops).  `C₀` is any positive number with
`C₀ ≤ I_{a₀}(θ, w⁰)` for some `a₀` (in particular `max_a I_a(θ, w⁰)`).  Besides the model,
the hypotheses are measurability of the noise variables and of the enclosures as functions
of the tape. -/
theorem safeguard_mean [IsProbabilityMeasure P] [Countable 𝒜] (u : X → E) (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k0 : ℝ} (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    {ξ : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun p : X × ℕ => ξ p.1 p.2) P)
    (hξ : ∀ x i, HasLaw (ξ x i) (gaussianReal 0 1) P) (hξm : ∀ x i, Measurable (ξ x i))
    (θ : E) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (a0 : 𝒜) {C0 : ℝ} (hC0 : 0 < C0)
    (hC0le : C0 ≤ gInfo u (Q a0) θ w0)
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ} {Bbar : ℕ → ℝ}
    (hJm : ∀ n a, Measurable (fun Y : X → ℕ → ℝ => Jlow n Y a))
    (hJ : ∀ (n : ℕ) Y a, gInfo u (Q a) (olsCount u (roundCount w0 n) Y)
      (fun x => (roundCount w0 n x : ℝ)) - 1 ≤ Jlow n Y a)
    (hB : ∀ n : ℕ, Bbar n ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 1) :
    ∫⁻ ω, roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ ξ ω))) ∂P ≤
      ENNReal.ofReal (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0) := by
  classical
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  set xF := logBudget (aF (Module.finrank ℝ E) δ C0) (bF C0) with hxF
  have hYm : Measurable (obsTape u θ ξ) := measurable_obsTape u θ hξm
  have hstopm : ∀ n, MeasurableSet {ω | sgStop Jlow Bbar (obsTape u θ ξ ω) n} := fun n =>
    hYm (measurableSet_sgStop hJm n)
  -- tail of the non-stopping event
  have htail : ∀ n : ℕ, xF ≤ n → P {ω | ¬ sgStop Jlow Bbar (obsTape u θ ξ ω) n} ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(n * C0) / 8)) := by
    intro n hn
    have hb1 : (1 : ℝ) ≤ bF C0 := le_max_left _ _
    obtain ⟨-, hxb, -⟩ := log_budget_inversion (aF_nonneg hd hδ0 hδ1 hC0) hb1
    have hn0 : (0 : ℝ) < n := by linarith
    have hch := ols_chernoff u (roundCount w0 n) (round_gram_injective u hw0.1 hk0 hM0 hn0)
      hind hξ θ (n * C0 / 4)
    have he : -(n * C0 / 4) / 2 = -(n * C0) / 8 := by ring
    rw [he] at hch
    refine (measure_mono ?_).trans hch
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hcon
    push Not at hcon
    exact hω (safeguard_stops_det u Q hQ hw0 θ hd hδ0 hδ1 a0 hC0 hC0le hJ hB hn _ hcon)
  -- an ℕ-valued version of the stopping count
  have hp' : ∀ ω, ∃ n, sgStop Jlow Bbar (obsTape u θ ξ ω) n ∨
      ((∀ m, ¬ sgStop Jlow Bbar (obsTape u θ ξ ω) m) ∧ n = 0) := by
    intro ω
    by_cases h : ∃ n, sgStop Jlow Bbar (obsTape u θ ξ ω) n
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · push Not at h
      exact ⟨0, Or.inr ⟨h, rfl⟩⟩
  have hN'm : Measurable (fun ω => Nat.find (hp' ω)) := by
    refine measurable_find hp' (fun k => ?_)
    have : {ω | sgStop Jlow Bbar (obsTape u θ ξ ω) k ∨
        ((∀ m, ¬ sgStop Jlow Bbar (obsTape u θ ξ ω) m) ∧ k = 0)} =
        {ω | sgStop Jlow Bbar (obsTape u θ ξ ω) k} ∪
          ((⋂ m, {ω | sgStop Jlow Bbar (obsTape u θ ξ ω) m}ᶜ) ∩ {_ω | k = 0}) := by
      ext ω
      simp
    rw [this]
    exact (hstopm k).union ((MeasurableSet.iInter (fun m => (hstopm m).compl)).inter
      (MeasurableSet.const _))
  have hsub : ∀ n : ℕ, {ω | n < Nat.find (hp' ω)} ⊆
      {ω | ¬ sgStop Jlow Bbar (obsTape u θ ξ ω) n} := by
    intro n ω hω hstop
    simp only [Set.mem_ofPred_eq] at hω
    exact absurd (Nat.find_min' (hp' ω) (Or.inl hstop)) (not_le.mpr hω)
  have hmean := safeguard_mean_bound P hN'm (Fδ := fun ω => Fintype.card X + Nat.find (hp' ω))
    (q := Fintype.card X) (fun _ => le_rfl) hd hδ0 hδ1 hC0
    (fun n hn => (measure_mono (hsub n)).trans (htail n hn))
  -- the safeguard stops almost surely
  have hae : ∀ᵐ ω ∂P, ∃ n, sgStop Jlow Bbar (obsTape u θ ξ ω) n := by
    rw [ae_iff]
    have hr0 : 0 ≤ Real.exp (-(C0 / 16)) := (Real.exp_pos _).le
    have hr1 : Real.exp (-(C0 / 16)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(C0 / 16)) ^ n))
        Filter.atTop (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
    rw [ENNReal.ofReal_zero] at hlim
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    refine Filter.eventually_atTop.mpr ⟨⌈xF⌉₊, fun n hn => ?_⟩
    have hxn : xF ≤ n := (Nat.le_ceil xF).trans (by exact_mod_cast hn)
    refine (measure_mono ?_).trans ((htail n hxn).trans (ENNReal.ofReal_le_ofReal ?_))
    · intro ω hω
      simp only [Set.mem_ofPred_eq, not_exists] at hω ⊢
      exact hω n
    · have h8 := (fallback_budget_sufficient hd hδ0 hδ1 hC0 hxn).2
      have := mgf_tail_simplify (d := (Module.finrank ℝ E : ℝ)) (x := n * C0) h8
      rw [← Real.exp_nat_mul]
      have e : (n : ℝ) * -(C0 / 16) = -(n * C0) / 16 := by ring
      rw [e]
      exact this
  refine (lintegral_mono_ae ?_).trans hmean
  filter_upwards [hae] with ω hω
  rw [firstTime_eq_find hω, roundTotal_coe]
  have hfind : Nat.find hω = Nat.find (hp' ω) := by
    apply le_antisymm
    · rcases Nat.find_spec (hp' ω) with h | ⟨h, -⟩
      · exact Nat.find_min' hω h
      · exact absurd (Nat.find_spec hω) (h _)
    · exact Nat.find_min' (hp' ω) (Or.inl (Nat.find_spec hω))
  have hle := sum_roundCount_le hw0 (Nat.find hω)
  rw [← hfind]
  have : ∑ x, roundCount w0 (Nat.find hω : ℝ) x ≤ Fintype.card X + Nat.find hω := by omega
  exact_mod_cast this

end Fresh

/-! ### Measurability and conditioning on an independent tape -/

section Conditioning

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Conditioning on an independent variable.**  If `Xv` and `Yv` are independent, `A` and
`S` are measurable, and for every fixed `x ∈ A` the section event `{(x, Yv) ∈ S}` has
probability at most `β`, then `ℙ(Xv ∈ A, (Xv, Yv) ∈ S) ≤ β ℙ(Xv ∈ A)`. -/
theorem indep_section_bound [IsProbabilityMeasure P] {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳]
    [MeasurableSpace 𝒴] {Xv : Ω → 𝒳} {Yv : Ω → 𝒴} (hX : Measurable Xv) (hY : Measurable Yv)
    (hind : IndepFun Xv Yv P) {A : Set 𝒳} (hA : MeasurableSet A) {S : Set (𝒳 × 𝒴)}
    (hS : MeasurableSet S) {β : ℝ≥0∞} (h : ∀ x ∈ A, P {ω | (x, Yv ω) ∈ S} ≤ β) :
    P {ω | Xv ω ∈ A ∧ (Xv ω, Yv ω) ∈ S} ≤ β * P {ω | Xv ω ∈ A} := by
  have hmap : P.map (fun ω => (Xv ω, Yv ω)) = (P.map Xv).prod (P.map Yv) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hind
  have hT : MeasurableSet ((A ×ˢ (Set.univ : Set 𝒴)) ∩ S) := (hA.prod MeasurableSet.univ).inter hS
  have h1 : P {ω | Xv ω ∈ A ∧ (Xv ω, Yv ω) ∈ S} =
      (P.map (fun ω => (Xv ω, Yv ω))) ((A ×ˢ (Set.univ : Set 𝒴)) ∩ S) := by
    rw [Measure.map_apply (hX.prodMk hY) hT]
    congr 1
    ext ω
    simp
  have : IsProbabilityMeasure (P.map Yv) := Measure.isProbabilityMeasure_map_iff hY.aemeasurable |>.mpr inferInstance
  rw [h1, hmap, Measure.prod_apply hT]
  calc ∫⁻ x, (P.map Yv) (Prod.mk x ⁻¹' ((A ×ˢ (Set.univ : Set 𝒴)) ∩ S)) ∂(P.map Xv)
      ≤ ∫⁻ x, A.indicator (fun _ => β) x ∂(P.map Xv) := by
        refine lintegral_mono (fun x => ?_)
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx]
          refine (measure_mono (Set.preimage_mono Set.inter_subset_right)).trans ?_
          rw [Measure.map_apply hY (measurable_prodMk_left hS)]
          exact h x hx
        · have : Prod.mk x ⁻¹' ((A ×ˢ (Set.univ : Set 𝒴)) ∩ S) = ∅ := by
            ext y
            simp [hx]
          rw [this]
          simp
    _ = β * (P.map Xv) A := lintegral_indicator_const hA β
    _ = β * P {ω | Xv ω ∈ A} := by
        rw [Measure.map_apply hX hA]
        rfl

/-- Independence in the form `𝔼[g(Yv) ; Xv ∈ T] = ℙ(Xv ∈ T) 𝔼 g(Yv)`. -/
theorem setLIntegral_indepFun [IsProbabilityMeasure P] {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳]
    [MeasurableSpace 𝒴] {Xv : Ω → 𝒳} {Yv : Ω → 𝒴} (hX : Measurable Xv) (hY : Measurable Yv)
    (hind : IndepFun Xv Yv P) {T : Set 𝒳} (hT : MeasurableSet T) {g : 𝒴 → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ ω in Xv ⁻¹' T, g (Yv ω) ∂P = P (Xv ⁻¹' T) * ∫⁻ ω, g (Yv ω) ∂P := by
  refine setLIntegral_of_indep P (Mf := MeasurableSpace.comap Yv inferInstance)
    hY.comap_le (hX hT) ?_ (hg.comp (comap_measurable Yv))
  rw [IndepSets_iff]
  rintro s t ⟨B, hB, rfl⟩ ht
  rw [Set.mem_singleton_iff.mp ht, Set.inter_comm, mul_comm]
  exact hind.measure_inter_preimage_eq_mul T B hT hB

/-- The first time of a measurable family of events is measurable. -/
lemma measurable_firstTime {α : Type*} [MeasurableSpace α] {p : α → ℕ → Prop}
    (hp : ∀ n, MeasurableSet {a | p a n}) : Measurable (fun a => firstTime (p a)) := by
  classical
  refine measurable_to_countable' (fun N => ?_)
  induction N using ENat.recTopCoe with
  | top =>
    have : (fun a => firstTime (p a)) ⁻¹' {⊤} = ⋂ n, {a | p a n}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_ofPred_eq]
      constructor
      · intro h n hn
        have := firstTime_le hn
        rw [h] at this
        exact absurd this (by simp)
      · exact firstTime_eq_top
    rw [this]
    exact MeasurableSet.iInter (fun n => (hp n).compl)
  | coe n =>
    have : (fun a => firstTime (p a)) ⁻¹' {(n : ℕ∞)} =
        {a | p a n} ∩ ⋂ m, ⋂ (_ : m < n), {a | p a m}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        by_cases hex : ∃ m, p a m
        · rw [firstTime_eq_find hex, Nat.cast_inj] at h
          subst h
          exact ⟨Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
        · push Not at hex
          rw [firstTime_eq_top hex] at h
          exact absurd h (by simp)
      · rintro ⟨hn, hmin⟩
        rw [firstTime_eq_find ⟨n, hn⟩, Nat.cast_inj]
        exact le_antisymm (Nat.find_min' _ hn)
          (not_lt.mp (fun hlt => hmin _ hlt (Nat.find_spec ⟨n, hn⟩)))
    rw [this]
    exact (hp n).inter (MeasurableSet.iInter (fun m => MeasurableSet.iInter
      (fun _ => (hp m).compl)))

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma olsEst_eq_symm {ι : Type*} [Fintype ι] (f : ι → E) (hinj : Function.Injective (obsMap f))
    (y : ι → ℝ) :
    olsEst f y = (LinearEquiv.ofBijective (gramOp f) ⟨gramOp_injective f hinj,
      LinearMap.injective_iff_surjective.mp (gramOp_injective f hinj)⟩).symm
        (∑ i, y i • f i) := by
  apply gramOp_injective f hinj
  rw [olsEst_normal f hinj]
  exact (LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective (gramOp f)
    ⟨gramOp_injective f hinj,
      LinearMap.injective_iff_surjective.mp (gramOp_injective f hinj)⟩) _).symm

/-- The least-squares estimate of a positive definite design is a measurable function of
the observation tape. -/
lemma measurable_olsCount (u : X → E) (c : X → ℕ)
    (hinj : Function.Injective (designMap u (fun x => (c x : ℝ)))) :
    Measurable (fun Y : X → ℕ → ℝ => olsCount u c Y) := by
  have hB := obsMap_sigma_injective u c hinj
  have heq : (fun Y : X → ℕ → ℝ => olsCount u c Y) = fun Y =>
      (LinearEquiv.ofBijective (gramOp (fun p : Σ x, Fin (c x) => u p.1))
        ⟨gramOp_injective _ hB, LinearMap.injective_iff_surjective.mp
          (gramOp_injective _ hB)⟩).symm (∑ p : Σ x, Fin (c x), Y p.1 p.2 • u p.1) :=
    funext (fun Y => olsEst_eq_symm _ hB _)
  rw [heq]
  refine (LinearMap.continuous_of_finiteDimensional
    ((LinearEquiv.ofBijective (gramOp (fun p : Σ x, Fin (c x) => u p.1))
      ⟨gramOp_injective _ hB, LinearMap.injective_iff_surjective.mp
        (gramOp_injective _ hB)⟩).symm : E →ₗ[ℝ] E)).measurable.comp ?_
  refine Finset.measurable_sum _ (fun p _ => ?_)
  exact ((measurable_pi_apply (p.2 : ℕ)).comp (measurable_pi_apply p.1)).smul_const _

lemma measurable_olsQ (u : X → E) (θ : E) (c : X → ℕ)
    (hinj : Function.Injective (designMap u (fun x => (c x : ℝ)))) :
    Measurable (fun Y : X → ℕ → ℝ =>
      ‖designMap u (fun x => (c x : ℝ)) (olsCount u c Y - θ)‖ ^ 2 / 2) := by
  have hc := LinearMap.continuous_of_finiteDimensional (designMap u (fun x => (c x : ℝ)))
  have hcont : Continuous (fun v : E => ‖designMap u (fun x => (c x : ℝ)) (v - θ)‖ ^ 2 / 2) :=
    ((hc.comp (continuous_id.sub continuous_const)).norm.pow 2).div_const 2
  exact hcont.measurable.comp (measurable_olsCount u c hinj)

end Conditioning

/-! ### The procedure: pilot, frozen confirmation, safeguard -/

section Procedure

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {𝒜 : Type*}

/-- The pilot estimate at stage `j`: least squares from the counts `⌈2^j w⁰_x⌉` of the pilot
tape `y`. -/
noncomputable def pilotV (u : X → E) (w0 : X → ℝ) (y : X → ℕ → ℝ) (j : ℕ) : E :=
  olsCount u (roundCount w0 (2 ^ j)) y

/-- The pilot commits at stage `j`: the gate `e_j² ≤ k² l_j` of `eq:v10g-gate` holds at `j`
and at no earlier stage. -/
def commitAt (e : ℕ → ℝ) (k : ℝ) (ol : ℕ → E → ℝ) (v : ℕ → E) (j : ℕ) : Prop :=
  e j ^ 2 ≤ k ^ 2 * ol j (v j) ∧ ∀ i < j, ¬ e i ^ 2 ≤ k ^ 2 * ol i (v i)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
lemma commitAt_unique {e : ℕ → ℝ} {k : ℝ} {ol : ℕ → E → ℝ} {v : ℕ → E} {i j : ℕ}
    (hi : commitAt e k ol v i) (hj : commitAt e k ol v j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hi.1 (hj.2 i h)
  · exact h
  · exact absurd hj.1 (hi.2 j h)

lemma measurable_pilotV (u : X → E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k0 : ℝ} (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (j : ℕ) :
    Measurable (fun y : X → ℕ → ℝ => pilotV u w0 y j) :=
  measurable_olsCount u _ (round_gram_injective u hw0.1 hk0 hM0 (by positivity))

lemma measurableSet_commitAt (u : X → E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k0 : ℝ}
    (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (e : ℕ → ℝ) (k : ℝ)
    {ol : ℕ → E → ℝ} (hol : ∀ j, Measurable (ol j)) (j : ℕ) :
    MeasurableSet {y : X → ℕ → ℝ | commitAt e k ol (pilotV u w0 y) j} := by
  have hg : ∀ i, MeasurableSet {y : X → ℕ → ℝ | e i ^ 2 ≤ k ^ 2 * ol i (pilotV u w0 y i)} :=
    fun i => measurableSet_le measurable_const
      (measurable_const.mul ((hol i).comp (measurable_pilotV u hw0 hk0 hM0 i)))
  have : {y : X → ℕ → ℝ | commitAt e k ol (pilotV u w0 y) j} =
      {y | e j ^ 2 ≤ k ^ 2 * ol j (pilotV u w0 y j)} ∩
        ⋂ i, ⋂ (_ : i < j), {y | e i ^ 2 ≤ k ^ 2 * ol i (pilotV u w0 y i)}ᶜ := by
    ext y
    simp [commitAt]
  rw [this]
  exact (hg j).inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (hg i).compl)

/-- The coverage-failure event of the confirmation stream after a commitment at stage `j`
is measurable in the pair (pilot tape, confirmation tape). -/
lemma measurableSet_confBad (u : X → E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k0 k : ℝ}
    (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k)
    (hk1 : k ≤ 1) {ow : ℕ → E → X → ℝ}
    (hdes : ∀ j v, ∃ p ∈ simplex X, ow j v = floorDesign k w0 p)
    (how : ∀ j x, Measurable (fun v => ow j v x)) (θ : E) (B : ℕ → ℝ) (j : ℕ) :
    MeasurableSet {q : (X → ℕ → ℝ) × (X → ℕ → ℝ) | ∃ n : ℕ, 1 ≤ n ∧
      B n ≤ freshQ u (ow j (pilotV u w0 q.1 j)) θ q.2 n} := by
  have hcnt : ∀ n : ℕ, Measurable (fun y : X → ℕ → ℝ => fun x =>
      roundCount (ow j (pilotV u w0 y j)) n x) := fun n =>
    measurable_pi_iff.mpr (fun x => Nat.measurable_ceil.comp
      (measurable_const.mul ((how j x).comp (measurable_pilotV u hw0 hk0 hM0 j))))
  have hset : {q : (X → ℕ → ℝ) × (X → ℕ → ℝ) | ∃ n : ℕ, 1 ≤ n ∧
      B n ≤ freshQ u (ow j (pilotV u w0 q.1 j)) θ q.2 n} =
      ⋃ n : ℕ, ⋃ c : X → ℕ,
        ⋃ (_ : 1 ≤ n ∧ Function.Injective (designMap u (fun x => (c x : ℝ)))),
        ((fun y : X → ℕ → ℝ => fun x => roundCount (ow j (pilotV u w0 y j)) n x) ⁻¹' {c}) ×ˢ
          {y' : X → ℕ → ℝ | B n ≤
            ‖designMap u (fun x => (c x : ℝ)) (olsCount u c y' - θ)‖ ^ 2 / 2} := by
    ext ⟨y, y'⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨n, hn, h⟩
      obtain ⟨p, hp, hpe⟩ := hdes j (pilotV u w0 y j)
      refine ⟨n, _, ⟨hn, ?_⟩, rfl, h⟩
      rw [hpe]
      exact round_gram_injective u (floorDesign_mem hk.le hk1 hw0 hp).1 (mul_pos hk hk0)
        (floor_gram_lower u hw0.1 hp.1 hk.le hk1 hM0) (by exact_mod_cast hn)
    · rintro ⟨n, c, ⟨hn, -⟩, hc, h⟩
      subst hc
      exact ⟨n, hn, h⟩
  rw [hset]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun c =>
    MeasurableSet.iUnion fun hc => ?_
  exact (hcnt n (measurableSet_singleton c)).prod
    (measurableSet_le measurable_const (measurable_olsQ u θ c hc.2))

omit [Fintype X] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma measurable_shift (u : X → E) (θ : E) :
    Measurable (fun z : X → ℕ → ℝ => fun x i => ⟪u x, θ⟫ + z x i) :=
  measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i =>
    (((measurable_pi_apply i).comp (measurable_pi_apply x) :
      Measurable (fun z : X → ℕ → ℝ => z x i))).const_add _

/-- **Coverage of the fresh confirmation stream after a data-dependent commitment.**
The pilot tape selects the stage `j` and the frozen design `w = ow j v_j`; the confirmation
tape is independent of the pilot tape.  Except with probability `β`, on the commitment
event `Q_n < B(n, β)` for all `n ≥ 1`.  This is the step "conditional on the selected
pilot, the confirmation allocation is fixed and its fresh errors are independent Gaussian
variables", carried out by Fubini; it needs the oracle's design and lower endpoint to be
measurable functions of the center. -/
theorem confirm_coverage [IsProbabilityMeasure P] (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {k0 k : ℝ} (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k ≤ 1)
    (e : ℕ → ℝ) {ow : ℕ → E → X → ℝ} {ol : ℕ → E → ℝ}
    (hdes : ∀ j v, ∃ p ∈ simplex X, ow j v = floorDesign k w0 p)
    (hol : ∀ j, Measurable (ol j)) (how : ∀ j x, Measurable (fun v => ow j v x))
    {ξP ξC : X → ℕ → Ω → ℝ} (hξPm : ∀ x i, Measurable (ξP x i))
    (hξCm : ∀ x i, Measurable (ξC x i))
    (hindC : iIndepFun (fun p : X × ℕ => ξC p.1 p.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (θ : E) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    P {ω | ∃ j, commitAt e k ol (pilotV u w0 (obsTape u θ ξP ω)) j ∧ ∃ n : ℕ, 1 ≤ n ∧
      boundary (Module.finrank ℝ E) n β ≤
        freshQ u (ow j (pilotV u w0 (obsTape u θ ξP ω) j)) θ (obsTape u θ ξC ω) n} ≤
      ENNReal.ofReal β := by
  have hYP : Measurable (obsTape u θ ξP) := measurable_obsTape u θ hξPm
  have hYC : Measurable (obsTape u θ ξC) := measurable_obsTape u θ hξCm
  have hI : IndepFun (obsTape u θ ξP) (obsTape u θ ξC) P :=
    hPC.comp (measurable_shift u θ) (measurable_shift u θ)
  let A : ℕ → Set (X → ℕ → ℝ) := fun j => {y | commitAt e k ol (pilotV u w0 y) j}
  let S : ℕ → Set ((X → ℕ → ℝ) × (X → ℕ → ℝ)) := fun j => {q | ∃ n : ℕ, 1 ≤ n ∧
    boundary (Module.finrank ℝ E) n β ≤ freshQ u (ow j (pilotV u w0 q.1 j)) θ q.2 n}
  have hA : ∀ j, MeasurableSet (A j) := measurableSet_commitAt u hw0 hk0 hM0 e k hol
  have hS : ∀ j, MeasurableSet (S j) :=
    measurableSet_confBad u hw0 hk0 hM0 hk hk1 hdes how θ _
  have hsec : ∀ j y, P {ω | (y, obsTape u θ ξC ω) ∈ S j} ≤ ENNReal.ofReal β := by
    intro j y
    obtain ⟨p, hp, hpe⟩ := hdes j (pilotV u w0 y j)
    have := fresh_coverage u (floorDesign_mem hk.le hk1 hw0 hp).1 (mul_pos hk hk0)
      (floor_gram_lower u hw0.1 hp.1 hk.le hk1 hM0) hindC hξC θ hβ0 hβ1
    rw [← hpe] at this
    exact this
  have hj : ∀ j, P {ω | obsTape u θ ξP ω ∈ A j ∧
      (obsTape u θ ξP ω, obsTape u θ ξC ω) ∈ S j} ≤
      ENNReal.ofReal β * P (obsTape u θ ξP ⁻¹' A j) := fun j =>
    indep_section_bound hYP hYC hI (hA j) (hS j) (fun y _ => hsec j y)
  have hdisj : Pairwise (Function.onFun Disjoint fun j => obsTape u θ ξP ⁻¹' A j) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun ω hi hj' => hij (commitAt_unique hi hj'))
  calc P {ω | ∃ j, commitAt e k ol (pilotV u w0 (obsTape u θ ξP ω)) j ∧ ∃ n : ℕ, 1 ≤ n ∧
        boundary (Module.finrank ℝ E) n β ≤
          freshQ u (ow j (pilotV u w0 (obsTape u θ ξP ω) j)) θ (obsTape u θ ξC ω) n}
      ≤ P (⋃ j, {ω | obsTape u θ ξP ω ∈ A j ∧
          (obsTape u θ ξP ω, obsTape u θ ξC ω) ∈ S j}) := by
        refine measure_mono ?_
        rintro ω ⟨j, hc, hn⟩
        exact Set.mem_iUnion.mpr ⟨j, hc, hn⟩
    _ ≤ ∑' j, P {ω | obsTape u θ ξP ω ∈ A j ∧
          (obsTape u θ ξP ω, obsTape u θ ξC ω) ∈ S j} := measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal β * P (obsTape u θ ξP ⁻¹' A j) := tsum_le_tsum hj
    _ = ENNReal.ofReal β * ∑' j, P (obsTape u θ ξP ⁻¹' A j) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal β * P (⋃ j, obsTape u θ ξP ⁻¹' A j) := by
        rw [measure_iUnion hdisj (fun j => hYP (hA j))]
    _ ≤ ENNReal.ofReal β * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal β := mul_one _

omit [MeasurableSpace E] [BorelSpace E] in
/-- Deterministic certification by the frozen record (`eq:v10g-recycle` and the
radius--information implication). -/
lemma confirm_certify_det (φ : Z → E) (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (ε : ℝ) (u : X → E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k0 k : ℝ} (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k ≤ 1) (θ : E)
    (a : 𝒜) {p : X → ℝ} (hp : p ∈ simplex X) (v : E) {l : ℝ}
    (hl : l ≤ gInfo u (strictAlt φ (supp a) (hne a) ε) v (floorDesign k w0 p))
    (Y : X → ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) {H Bn : ℝ} (hH : 0 < H) (hHB : H ≤ Bn)
    (hcert : Bn ≤ confirmZ u (floorDesign k w0 p) v l Y n)
    (hcov : freshQ u (floorDesign k w0 p) θ Y n < H) :
    regret (supp a) (hne a) (env φ θ) ≤ ε := by
  have hwnn : ∀ x, 0 ≤ floorDesign k w0 p x := (floorDesign_mem hk.le hk1 hw0 hp).1
  have hMw := floor_gram_lower u hw0.1 hp.1 hk.le hk1 hM0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlQ : ∀ lam ∈ strictAlt φ (supp a) (hne a) ε,
      l ≤ ‖designMap u (floorDesign k w0 p) (lam - v)‖ ^ 2 / 2 := fun lam hlam => by
    have h1 := pow_le_pow_left₀ rootInfo_nonneg
      (rootInfo_le (A := designMap u (floorDesign k w0 p)) (θ := v) hlam) 2
    unfold gInfo at hl
    linarith
  exact certify_of_stat φ (hne a) (ε := ε)
    (designMap u (fun x => (roundCount (floorDesign k w0 p) n x : ℝ)))
    (round_gram_injective u hwnn (mul_pos hk hk0) hMw hn0) hH (hHB.trans hcert)
    (frozen_recycle (designMap u (floorDesign k w0 p))
      (designMap u (fun x => (roundCount (floorDesign k w0 p) n x : ℝ))) _ hn0.le
      (round_gram_dominates u hwnn hn0.le) hlQ) hcov

/-- **The fresh confirmation branch is `(ε, δ/2)`-safe** (`prop:v10g-safety-fallback`),
for the record selected by the pilot.  Except with probability `δ/2`, on no path does the
pilot commit and the frozen statistic `Z_n` reach an upper enclosure `Bbar n ≥ B(n, δ/2)`
at some `n ≥ 1` while the frozen action has regret above `ε`.  The pilot accuracy and the
gate are not used; only the oracle inequality `l ≤ I_a(v, w)`, `w ∈ W_k`, and
measurability of the oracle's design and lower endpoint. -/
theorem confirm_branch_safe [IsProbabilityMeasure P] (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {k0 k : ℝ} (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k ≤ 1)
    {e : ℕ → ℝ} {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e oa ow ol ou)
    (hol : ∀ j, Measurable (ol j)) (how : ∀ j x, Measurable (fun v => ow j v x))
    {ξP ξC : X → ℕ → Ω → ℝ} (hξPm : ∀ x i, Measurable (ξP x i))
    (hξCm : ∀ x i, Measurable (ξC x i))
    (hindC : iIndepFun (fun p : X × ℕ => ξC p.1 p.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (θ : E) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {Bbar : ℕ → ℝ}
    (hB : ∀ n : ℕ, boundary (Module.finrank ℝ E) n (δ / 2) ≤ Bbar n) :
    P {ω | ∃ j, commitAt e k ol (pilotV u w0 (obsTape u θ ξP ω)) j ∧ ∃ n : ℕ, 1 ≤ n ∧
      Bbar n ≤ confirmZ u (ow j (pilotV u w0 (obsTape u θ ξP ω) j))
        (pilotV u w0 (obsTape u θ ξP ω) j) (ol j (pilotV u w0 (obsTape u θ ξP ω) j))
        (obsTape u θ ξC ω) n ∧
      ε < regret (supp (oa j (pilotV u w0 (obsTape u θ ξP ω) j))) (hne _) (env φ θ)} ≤
      ENNReal.ofReal (δ / 2) := by
  refine (measure_mono ?_).trans (confirm_coverage u hw0 hk0 hM0 hk hk1 e hor.design_mem hol how
    hξPm hξCm hindC hξC hPC θ (by linarith : (0 : ℝ) < δ / 2) (by linarith))
  rintro ω ⟨j, hc, n, hn, hcert, hbad⟩
  refine ⟨j, hc, n, hn, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨p, hp, hpe⟩ := hor.design_mem j (pilotV u w0 (obsTape u θ ξP ω) j)
  have hl := hor.lo_le j (pilotV u w0 (obsTape u θ ξP ω) j)
  rw [hpe] at hl hcert hcon
  have := confirm_certify_det φ supp hne ε u hw0 hk0 hM0 hk hk1 θ _ hp _ hl _ hn
    (boundary_pos (Nat.cast_nonneg _) hn (by linarith : (0 : ℝ) < δ / 2) (by linarith))
    (hB n) hcert hcon
  linarith

/-- **The specified procedure is `(ε, δ)`-safe** (`thm:v10g-expectation`, first sentence;
`prop:bay-finite`).  Whichever branch returns, the returned action is one certified by
that branch; except with probability `δ` neither branch ever certifies an action with
regret above `ε`. -/
theorem v10g_safe [IsProbabilityMeasure P] (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {k0 k : ℝ} (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k ≤ 1)
    {e : ℕ → ℝ} {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e oa ow ol ou)
    (hol : ∀ j, Measurable (ol j)) (how : ∀ j x, Measurable (fun v => ow j v x))
    {ξP ξC ξF : X → ℕ → Ω → ℝ} (hξPm : ∀ x i, Measurable (ξP x i))
    (hξCm : ∀ x i, Measurable (ξC x i))
    (hindC : iIndepFun (fun p : X × ℕ => ξC p.1 p.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hindF : iIndepFun (fun p : X × ℕ => ξF p.1 p.2) P)
    (hξF : ∀ x i, HasLaw (ξF x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (θ : E) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {Bbar : ℕ → ℝ}
    (hB : ∀ n : ℕ, boundary (Module.finrank ℝ E) n (δ / 2) ≤ Bbar n)
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ}
    (hJ : ∀ n Y a, Jlow n Y a ≤ gInfo u (strictAlt φ (supp a) (hne a) ε)
      (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ))) :
    P ({ω | ∃ j, commitAt e k ol (pilotV u w0 (obsTape u θ ξP ω)) j ∧ ∃ n : ℕ, 1 ≤ n ∧
        Bbar n ≤ confirmZ u (ow j (pilotV u w0 (obsTape u θ ξP ω) j))
          (pilotV u w0 (obsTape u θ ξP ω) j) (ol j (pilotV u w0 (obsTape u θ ξP ω) j))
          (obsTape u θ ξC ω) n ∧
        ε < regret (supp (oa j (pilotV u w0 (obsTape u θ ξP ω) j))) (hne _) (env φ θ)} ∪
      {ω | ∃ n : ℕ, 1 ≤ n ∧ ∃ a, Bbar n ≤ Jlow n (obsTape u θ ξF ω) a ∧
        ε < regret (supp a) (hne a) (env φ θ)}) ≤ ENNReal.ofReal δ :=
  two_branch_safe P hδ0.le
    (confirm_branch_safe φ supp hne ε u hw0 hk0 hM0 hk hk1 hor hol how hξPm hξCm hindC hξC hPC θ
      hδ0 hδ1 hB)
    (safeguard_safe φ supp hne ε u hw0 hk0 hM0 hindF hξF θ hδ0 hδ1 hJ hB)

/-! #### The constant-share calendar and the expectation bound -/

/-- Global stopping time under the constant-share calendar.  After `t` global observations
the safeguard has received `⌊k t⌋` and the main procedure `t - ⌊k t⌋`.  If the main
procedure needs `m` observations to stop and the safeguard `F`, the interleaved procedure
stops at the first `t` at which one of them has received what it needs (`⊤` if never). -/
noncomputable def calTime (k : ℝ) (m F : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ t : ℕ, ⨅ _ : m ≤ ENNReal.ofReal ((t : ℝ) - ⌊k * (t : ℝ)⌋) ∨
    F ≤ ENNReal.ofReal (⌊k * (t : ℝ)⌋ : ℝ), (t : ℝ≥0∞)

lemma calTime_le_main {k : ℝ} (hk1 : k < 1) {m F : ℝ≥0∞} (mn : ℕ) (hm : m ≤ mn) :
    calTime k m F ≤ ENNReal.ofReal (mn / (1 - k) + 1) := by
  obtain ⟨t, ht1, ht2⟩ := calendar_main hk1 mn
  refine (iInf₂_le t (Or.inl ?_)).trans ?_
  · refine hm.trans ?_
    rw [← ENNReal.ofReal_natCast mn]
    exact ENNReal.ofReal_le_ofReal ht2
  · rw [← ENNReal.ofReal_natCast t]
    exact ENNReal.ofReal_le_ofReal ht1

lemma calTime_le_safe {k : ℝ} (hk0 : 0 < k) (m F : ℝ≥0∞) (hF : F = ⊤ ∨ ∃ f : ℕ, F = f) :
    calTime k m F ≤ F / ENNReal.ofReal k + 1 := by
  rcases hF with rfl | ⟨f, rfl⟩
  · rw [ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    simp
  · obtain ⟨t, ht1, ht2⟩ := calendar_safeguard hk0 f
    refine (iInf₂_le t (Or.inr ?_)).trans ?_
    · rw [← ENNReal.ofReal_natCast f]
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast ht2
    · rw [← ENNReal.ofReal_natCast t, ← ENNReal.ofReal_natCast f,
        ← ENNReal.ofReal_div_of_pos hk0, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by positivity) zero_le_one]
      exact ENNReal.ofReal_le_ofReal ht1

lemma roundTotal_top_or (w : X → ℝ) (N : ℕ∞) : roundTotal w N = ⊤ ∨ ∃ f : ℕ, roundTotal w N = f := by
  induction N using ENat.recTopCoe with
  | top => left; simp [roundTotal]
  | coe n => right; exact ⟨_, roundTotal_coe w n⟩

lemma roundTotal_le_of_le {w : X → ℝ} (hw : w ∈ simplex X) {N : ℕ∞} {n : ℕ} (h : N ≤ n) :
    roundTotal w N ≤ ((n + Fintype.card X : ℕ) : ℝ≥0∞) := by
  lift N to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top n) h
  have hmn : N ≤ n := by exact_mod_cast h
  rw [roundTotal_coe]
  refine Nat.cast_le.mpr (le_trans (sum_le_sum (fun x _ => ?_)) (sum_roundCount_le hw n))
  exact Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) (hw.1 x))

/-- Observations used by the main procedure: the pilot counts at the committing stage plus
the confirmation counts at the first nominal count `n ≥ 1` where the lower enclosure
`Zlow` of `Z_n` reaches `Bbar n` (`⊤` if the pilot never commits or confirmation never
stops). -/
noncomputable def mainObs (u : X → E) (w0 : X → ℝ) (e : ℕ → ℝ) (k : ℝ) (ow : ℕ → E → X → ℝ)
    (ol : ℕ → E → ℝ) (Zlow : ℕ → (X → ℕ → ℝ) → (X → ℕ → ℝ) → ℕ → ℝ) (Bbar : ℕ → ℝ)
    (y y' : X → ℕ → ℝ) : ℝ≥0∞ :=
  ⨅ j : ℕ, ⨅ _ : commitAt e k ol (pilotV u w0 y) j,
    ((∑ x, roundCount w0 (2 ^ j) x : ℕ) : ℝ≥0∞) +
      roundTotal (ow j (pilotV u w0 y j)) (firstTime (fun n => 1 ≤ n ∧ Bbar n ≤ Zlow j y y' n))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Discovery and confirmation on the good event** (proof of `thm:v10g-expectation`).
If every pilot estimate is within `ρ_j` of `θ` and the fresh confirmation errors satisfy
`Q_n < B(n, α)` for all `n ≥ 1`, then the main procedure stops after at most
`D̄ + x_C + q + 1` observations. -/
lemma main_stops_det (u : X → E) (Q : 𝒜 → Set E) (hQ : ∀ a, (Q a).Nonempty)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 k α δ : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0) (hk : 0 < k) (hk1 : k < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1)
    {e : ℕ → ℝ} (he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j)
    {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u Q w0 k e oa ow ol ou)
    (θ : E) (aS : 𝒜) {wS : X → ℝ} (hwS : wS ∈ simplex X) {C : ℝ} (hC : 0 < C)
    (hCle : C ≤ gInfo u (Q aS) θ wS)
    {Zlow : ℕ → (X → ℕ → ℝ) → (X → ℕ → ℝ) → ℕ → ℝ} {Bbar : ℕ → ℝ}
    (hZ : ∀ j y y' (n : ℕ), confirmZ u (ow j (pilotV u w0 y j)) (pilotV u w0 y j)
      (ol j (pilotV u w0 y j)) y' n - 1 ≤ Zlow j y y' n)
    (hBup : ∀ n : ℕ, Bbar n ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 1)
    (y y' : X → ℕ → ℝ)
    (hv : ∀ j, ‖pilotV u w0 y j - θ‖ ≤ pilotRho (Module.finrank ℝ E) k0 α j)
    (hcov : ∀ j, commitAt e k ol (pilotV u w0 y) j → ∀ n : ℕ, 1 ≤ n →
      freshQ u (ow j (pilotV u w0 y j)) θ y' n < boundary (Module.finrank ℝ E) n α) :
    ∃ m : ℕ, mainObs u w0 e k ow ol Zlow Bbar y y' ≤ m ∧
      (m : ℝ) ≤ Dbar (pilotA ℓ k0 k C) (Module.finrank ℝ E) α (Fintype.card X) +
        logBudget (aC (Module.finrank ℝ E) k (cstar k * C) δ α) (bC k (cstar k * C)) +
        Fintype.card X + 1 := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨j, hgate, hmin, hr1, hr2, hD⟩ := pilot_commit u Q hQ hw0 hℓ hu hk0 hk hk1 hα0 hα1 hd
    he1 he2 hor θ aS hwS hC hCle (pilotV u w0 y) hv
  have hcommit : commitAt e k ol (pilotV u w0 y) j := ⟨hgate, hmin⟩
  have hcs : 0 < cstar k := by
    have : 0 < 1 - k := by linarith
    unfold cstar
    positivity
  have hc0 : 0 < cstar k * C := mul_pos hcs hC
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).mpr hδ1)
  have hlα : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((one_le_div hα0).mpr hα1)
  have hbD : 0 ≤ bD (Module.finrank ℝ E) k := by unfold bD; positivity
  have hrC : 0 ≤ rC (Module.finrank ℝ E) k (cstar k * C) α := by
    unfold rC
    refine div_nonneg (add_nonneg (mul_nonneg (by linarith) ?_) (mul_nonneg (by positivity) ?_))
      hc0.le
    · exact add_nonneg (add_nonneg (mul_nonneg (by linarith) hl2) hbD) (by norm_num)
    · exact add_nonneg (mul_nonneg (by linarith) hlα) hbD
  have haC : 0 ≤ aC (Module.finrank ℝ E) k (cstar k * C) δ α := by
    unfold aC
    exact add_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hlδ) hc0.le) hrC
  have hbC : (1 : ℝ) ≤ bC k (cstar k * C) := le_max_left _ _
  obtain ⟨-, hxb, hpers⟩ := log_budget_inversion haC hbC
  set xC := logBudget (aC (Module.finrank ℝ E) k (cstar k * C) δ α) (bC k (cstar k * C)) with hxC
  set n := ⌈xC⌉₊ with hndef
  have hxn : xC ≤ n := Nat.le_ceil _
  have hn1r : (1 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hn1r.le
  have hn0 : (0 : ℝ) < n := by linarith
  have hcross := confirm_crossing hd hk hc0 hδ0 hδ1 hα0 hα1 hn1r.le (hpers n hxn)
  obtain ⟨p, hp, hpe⟩ := hor.design_mem j (pilotV u w0 y j)
  have hwmem : ow j (pilotV u w0 y j) ∈ simplex X := by
    rw [hpe]; exact floorDesign_mem hk.le hk1.le hw0 hp
  set w := ow j (pilotV u w0 y j) with hw
  set vj := pilotV u w0 y j with hvj
  set θh := olsCount u (roundCount w n) y' with hθh
  set g := ‖designMap u (fun x => (roundCount w n x : ℝ)) (θh - θ)‖ with hg
  have hQeq : freshQ u w θ y' n = g ^ 2 / 2 := rfl
  have hρ0 : 0 ≤ pilotRho (Module.finrank ℝ E) k0 α j := Real.sqrt_nonneg _
  have he0 : 0 ≤ e j := (div_nonneg (mul_nonneg hℓ.le hρ0) h2pos.le).trans (he1 j)
  have hl0 : 0 ≤ ol j vj := hor.lo_nonneg j vj
  have htri : ‖designMap u w (θh - vj)‖ ≤ g / Real.sqrt n + Real.sqrt 2 * e j := by
    have h1 : ‖designMap u w (θh - vj)‖ ≤
        ‖designMap u w (θh - θ)‖ + ‖designMap u w (θ - vj)‖ := by
      have : θh - vj = (θh - θ) + (θ - vj) := by abel
      rw [this, map_add]
      exact norm_add_le _ _
    have h2 : ‖designMap u w (θh - θ)‖ ≤ g / Real.sqrt n := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hn0)]
      rw [mul_comm]
      exact round_gram_dominates u hwmem.1 hn0.le (θh - θ)
    have h3 : ‖designMap u w (θ - vj)‖ ≤ ℓ * ‖θ - vj‖ := norm_designMap_le u hwmem hu _
    have h4 : ‖θ - vj‖ = ‖vj - θ‖ := norm_sub_rev _ _
    have h5 : ℓ * pilotRho (Module.finrank ℝ E) k0 α j ≤ Real.sqrt 2 * e j := by
      have := he1 j
      rw [div_le_iff₀ h2pos] at this
      linarith
    have h6 : ℓ * ‖vj - θ‖ ≤ ℓ * pilotRho (Module.finrank ℝ E) k0 α j :=
      mul_le_mul_of_nonneg_left (hv j) hℓ.le
    rw [h4] at h3
    linarith
  have hsl : 0 ≤ Real.sqrt (ol j vj) - e j := by
    have h1 : e j ≤ Real.sqrt (k ^ 2 * ol j vj) := Real.le_sqrt_of_sq_le hgate
    have h3 : Real.sqrt (k ^ 2 * ol j vj) ≤ Real.sqrt (ol j vj) :=
      Real.sqrt_le_sqrt (by
        have hk2 : k ^ 2 ≤ 1 := by nlinarith
        have := mul_le_mul_of_nonneg_right hk2 hl0
        linarith)
    linarith
  have hlow := confirm_stat_lower (l := ol j vj) (e := e j) hn0 (norm_nonneg _) htri
  have hQlt : g ^ 2 / 2 ≤ boundary (Module.finrank ℝ E) n α := by
    rw [← hQeq]
    exact (hcov j hcommit n hn1).le
  have hmono := confirm_stat_mono (n := (n : ℝ)) (c0 := cstar k * C)
    (sl := Real.sqrt (ol j vj) - e j) hn0.le hsl hr1 hQlt
  have hBnn : 0 ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 2 := by
    have := boundary_pos hd hn1 (by linarith : (0 : ℝ) < δ / 2) (by linarith)
    linarith
  have hstop := confirm_stops hcross hBnn (hmono.trans hlow)
  have hfire : 1 ≤ n ∧ Bbar n ≤ Zlow j y y' n := by
    refine ⟨hn1, ?_⟩
    have h1 := hZ j y y' n
    have h3 := hBup n
    have h4 : boundary (Module.finrank ℝ E) n (δ / 2) + 2 ≤ confirmZ u w vj (ol j vj) y' n :=
      hstop
    linarith
  have hNle : firstTime (fun n => 1 ≤ n ∧ Bbar n ≤ Zlow j y y' n) ≤ n := firstTime_le hfire
  refine ⟨(∑ x, roundCount w0 (2 ^ j) x) + (n + Fintype.card X), ?_, ?_⟩
  · refine (iInf₂_le j hcommit).trans ?_
    rw [Nat.cast_add]
    exact add_le_add le_rfl (roundTotal_le_of_le hwmem hNle)
  · have h1 : (n : ℝ) ≤ xC + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    push_cast
    linarith

/-- **Correlated finite-confidence discovery and confirmation** (`thm:v10g-expectation`,
`eq:v10g-finite`) for the Gaussian linear model: `𝔼_θ τ ≤ min {𝓑_δ, H_δ / k + 1}`.

Model.  Three noise tapes `ξP`, `ξC`, `ξF` (pilot, confirmation, safeguard), each a family
of independent standard Gaussians, with the pilot tape independent of the confirmation
tape and the pair independent of the safeguard tape.  The pilot commits at the first stage
whose gate holds; confirmation uses the frozen design and stops at the first `n ≥ 1` with
`Bbar n ≤ Zlow`; the safeguard stops at the first `n ≥ 1` with `Bbar n ≤ Jlow n Y a` for
some `a`; observations are interleaved by the constant-share calendar (`calTime`), and
`τ` is the global number of observations at which the first branch stops.

Hypotheses other than the model: the oracle contract `eq:v10g-oracle` with Borel
measurable design and lower endpoint; the bounds on `e_j`; the enclosures
`Z_n - 1 ≤ Zlow`, `J_n(a) - 1 ≤ Jlow`, `Bbar n ≤ B(n, δ/2) + 1`, with `Jlow` measurable in
the tape; measurability of the noise variables.  `C` and `C₀` are positive numbers with
`C ≤ I_a(θ, w)` for some `(a, w)` and `C₀ ≤ I_{a₀}(θ, w⁰)` for some `a₀`; the paper takes
the maxima. -/
theorem v10g_expectation [IsProbabilityMeasure P] [Countable 𝒜] (u : X → E) (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 k α δ : ℝ}
    (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    (hk : 0 < k) (hk1 : k < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {e : ℕ → ℝ} (he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j)
    {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u Q w0 k e oa ow ol ou)
    (hol : ∀ j, Measurable (ol j)) (how : ∀ j x, Measurable (fun v => ow j v x))
    {ξP ξC ξF : X → ℕ → Ω → ℝ}
    (hξPm : ∀ x i, Measurable (ξP x i)) (hξCm : ∀ x i, Measurable (ξC x i))
    (hξFm : ∀ x i, Measurable (ξF x i))
    (hindP : iIndepFun (fun p : X × ℕ => ξP p.1 p.2) P)
    (hξP : ∀ x i, HasLaw (ξP x i) (gaussianReal 0 1) P)
    (hindC : iIndepFun (fun p : X × ℕ => ξC p.1 p.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hindF : iIndepFun (fun p : X × ℕ => ξF p.1 p.2) P)
    (hξF : ∀ x i, HasLaw (ξF x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (hPCF : IndepFun (fun ω => ((fun x i => ξP x i ω : X → ℕ → ℝ), (fun x i => ξC x i ω : X → ℕ → ℝ)))
      (fun ω x i => ξF x i ω) P)
    (θ : E) (aS : 𝒜) {wS : X → ℝ} (hwS : wS ∈ simplex X) {C : ℝ} (hC : 0 < C)
    (hCle : C ≤ gInfo u (Q aS) θ wS) (a0 : 𝒜) {C0 : ℝ} (hC0 : 0 < C0)
    (hC0le : C0 ≤ gInfo u (Q a0) θ w0)
    {Zlow : ℕ → (X → ℕ → ℝ) → (X → ℕ → ℝ) → ℕ → ℝ} {Bbar : ℕ → ℝ}
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ}
    (hZ : ∀ j y y' (n : ℕ), confirmZ u (ow j (pilotV u w0 y j)) (pilotV u w0 y j)
      (ol j (pilotV u w0 y j)) y' n - 1 ≤ Zlow j y y' n)
    (hBup : ∀ n : ℕ, Bbar n ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 1)
    (hJm : ∀ n a, Measurable (fun Y : X → ℕ → ℝ => Jlow n Y a))
    (hJ : ∀ (n : ℕ) Y a, gInfo u (Q a) (olsCount u (roundCount w0 n) Y)
      (fun x => (roundCount w0 n x : ℝ)) - 1 ≤ Jlow n Y a) :
    ∫⁻ ω, calTime k (mainObs u w0 e k ow ol Zlow Bbar (obsTape u θ ξP ω) (obsTape u θ ξC ω))
        (roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ ξF ω)))) ∂P ≤
      ENNReal.ofReal (min
        (Bdelta (Dbar (pilotA ℓ k0 k C) (Module.finrank ℝ E) α (Fintype.card X))
          (logBudget (aC (Module.finrank ℝ E) k (cstar k * C) δ α) (bC k (cstar k * C)))
          (Fintype.card X) k α (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0))
        (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0 / k + 1)) := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hYP : Measurable (obsTape u θ ξP) := measurable_obsTape u θ hξPm
  have hYC : Measurable (obsTape u θ ξC) := measurable_obsTape u θ hξCm
  have hYF : Measurable (obsTape u θ ξF) := measurable_obsTape u θ hξFm
  have hXY : Measurable (fun ω => (obsTape u θ ξP ω, obsTape u θ ξC ω)) := hYP.prodMk hYC
  have hIF : IndepFun (fun ω => (obsTape u θ ξP ω, obsTape u θ ξC ω)) (obsTape u θ ξF) P :=
    hPCF.comp ((measurable_shift u θ).prodMap (measurable_shift u θ)) (measurable_shift u θ)
  -- the good set in tape coordinates
  let A : ℕ → Set (X → ℕ → ℝ) := fun j => {y | commitAt e k ol (pilotV u w0 y) j}
  let S : ℕ → Set ((X → ℕ → ℝ) × (X → ℕ → ℝ)) := fun j => {q | ∃ n : ℕ, 1 ≤ n ∧
    boundary (Module.finrank ℝ E) n α ≤ freshQ u (ow j (pilotV u w0 q.1 j)) θ q.2 n}
  let G0 : Set ((X → ℕ → ℝ) × (X → ℕ → ℝ)) :=
    {q | (∀ j, ‖pilotV u w0 q.1 j - θ‖ ≤ pilotRho (Module.finrank ℝ E) k0 α j) ∧
      ¬ ∃ j, q.1 ∈ A j ∧ q ∈ S j}
  have hA : ∀ j, MeasurableSet (A j) := measurableSet_commitAt u hw0 hk0 hM0 e k hol
  have hS : ∀ j, MeasurableSet (S j) :=
    measurableSet_confBad u hw0 hk0 hM0 hk hk1.le hor.design_mem how θ _
  have hG0 : MeasurableSet G0 := by
    have h1 : MeasurableSet {q : (X → ℕ → ℝ) × (X → ℕ → ℝ) |
        ∀ j, ‖pilotV u w0 q.1 j - θ‖ ≤ pilotRho (Module.finrank ℝ E) k0 α j} := by
      have : {q : (X → ℕ → ℝ) × (X → ℕ → ℝ) |
          ∀ j, ‖pilotV u w0 q.1 j - θ‖ ≤ pilotRho (Module.finrank ℝ E) k0 α j} =
          ⋂ j, {q | ‖pilotV u w0 q.1 j - θ‖ ≤ pilotRho (Module.finrank ℝ E) k0 α j} := by
        ext q; simp
      rw [this]
      exact MeasurableSet.iInter (fun j => measurableSet_le
        ((((measurable_pilotV u hw0 hk0 hM0 j).comp measurable_fst).sub measurable_const).norm)
        measurable_const)
    have h2 : MeasurableSet {q : (X → ℕ → ℝ) × (X → ℕ → ℝ) | ∃ j, q.1 ∈ A j ∧ q ∈ S j} := by
      have : {q : (X → ℕ → ℝ) × (X → ℕ → ℝ) | ∃ j, q.1 ∈ A j ∧ q ∈ S j} =
          ⋃ j, (Prod.fst ⁻¹' A j) ∩ S j := by
        ext q; simp
      rw [this]
      exact MeasurableSet.iUnion (fun j => (measurable_fst (hA j)).inter (hS j))
    exact h1.inter h2.compl
  let XY : Ω → (X → ℕ → ℝ) × (X → ℕ → ℝ) := fun ω => (obsTape u θ ξP ω, obsTape u θ ξC ω)
  have h𝒢 : MeasurableSet (XY ⁻¹' G0) := hXY hG0
  -- the safeguard bound as a function of the safeguard tape
  let γ : (X → ℕ → ℝ) → ℝ≥0∞ := fun y =>
    roundTotal w0 (firstTime (sgStop Jlow Bbar y)) / ENNReal.ofReal k + 1
  have hγ : Measurable γ :=
    (((Measurable.of_discrete (f := roundTotal w0)).comp
      (measurable_firstTime (measurableSet_sgStop hJm))).div_const _).add_const 1
  have hHnn : 0 ≤ Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0 := by
    have hb1 : (1 : ℝ) ≤ bF C0 := le_max_left _ _
    obtain ⟨-, hxb, -⟩ := log_budget_inversion (aF_nonneg hd hδ0 hδ1 hC0) hb1
    have : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
    have : 0 ≤ 16 / C0 := by positivity
    unfold Hdelta
    linarith
  have hApos : 0 < pilotA ℓ k0 k C := by
    have : 0 < 1 - k := by linarith
    unfold pilotA
    positivity
  have hDb : 0 ≤ Dbar (pilotA ℓ k0 k C) (Module.finrank ℝ E) α (Fintype.card X) := by
    have haD : 0 ≤ aD (pilotA ℓ k0 k C) (Module.finrank ℝ E) α := by
      have := Real.log_nonneg ((one_le_div hα0).mpr hα1)
      unfold aD
      positivity
    obtain ⟨-, hxb, -⟩ := log_budget_inversion haD
      (le_max_left 1 (4 * pilotA ℓ k0 k C) : 1 ≤ bDm (pilotA ℓ k0 k C))
    have : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
    have : (1 : ℝ) ≤ max 1 (4 * pilotA ℓ k0 k C) := le_max_left _ _
    unfold Dbar bDm
    linarith
  have hmainDet : ∀ ω ∈ XY ⁻¹' G0, ∃ m : ℕ,
      mainObs u w0 e k ow ol Zlow Bbar (obsTape u θ ξP ω) (obsTape u θ ξC ω) ≤ m ∧
      (m : ℝ) ≤ Dbar (pilotA ℓ k0 k C) (Module.finrank ℝ E) α (Fintype.card X) +
        logBudget (aC (Module.finrank ℝ E) k (cstar k * C) δ α) (bC k (cstar k * C)) +
        Fintype.card X + 1 := by
    rintro ω ⟨hv, hnb⟩
    refine main_stops_det u Q hQ hw0 hℓ hu hk0 hk hk1 hα0 hα1 hδ0 hδ1 he1 he2 hor θ aS hwS hC
      hCle hZ hBup _ _ hv (fun j hc n hn => ?_)
    by_contra hcon
    push Not at hcon
    exact hnb ⟨j, hc, n, hn, hcon⟩
  have hxCnn : 0 ≤ Dbar (pilotA ℓ k0 k C) (Module.finrank ℝ E) α (Fintype.card X) +
      logBudget (aC (Module.finrank ℝ E) k (cstar k * C) δ α) (bC k (cstar k * C)) +
      Fintype.card X + 1 := by
    by_cases hne : (XY ⁻¹' G0).Nonempty
    · obtain ⟨ω, hω⟩ := hne
      obtain ⟨m, -, hm⟩ := hmainDet ω hω
      exact (Nat.cast_nonneg m).trans hm
    · -- no good path: the bound is still nonnegative by the explicit budgets
      have hcs : 0 < cstar k := by
        have : 0 < 1 - k := by linarith
        unfold cstar
        positivity
      have hc0 : 0 < cstar k * C := mul_pos hcs hC
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).mpr hδ1)
      have hlα : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((one_le_div hα0).mpr hα1)
      have hbD : 0 ≤ bD (Module.finrank ℝ E) k := by unfold bD; positivity
      have hrC : 0 ≤ rC (Module.finrank ℝ E) k (cstar k * C) α := by
        unfold rC
        refine div_nonneg (add_nonneg (mul_nonneg (by linarith) ?_)
          (mul_nonneg (by positivity) ?_)) hc0.le
        · exact add_nonneg (add_nonneg (mul_nonneg (by linarith) hl2) hbD) (by norm_num)
        · exact add_nonneg (mul_nonneg (by linarith) hlα) hbD
      have haC : 0 ≤ aC (Module.finrank ℝ E) k (cstar k * C) δ α := by
        unfold aC
        exact add_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hlδ) hc0.le) hrC
      obtain ⟨-, hxb, -⟩ := log_budget_inversion haC
        (le_max_left _ _ : (1 : ℝ) ≤ bC k (cstar k * C))
      have hxb' : bC k (cstar k * C) < logBudget
          (aC (Module.finrank ℝ E) k (cstar k * C) δ α) (bC k (cstar k * C)) := hxb
      have : (1 : ℝ) ≤ bC k (cstar k * C) := le_max_left _ _
      have : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
      linarith
  have h1k : 0 < 1 - k := by linarith
  refine finite_confidence_expectation P (τ := fun ω => calTime k
      (mainObs u w0 e k ow ol Zlow Bbar (obsTape u θ ξP ω) (obsTape u θ ξC ω))
      (roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ ξF ω)))))
    (g := fun ω => γ (obsTape u θ ξF ω)) h𝒢 hk hα0.le hHnn ?_ ?_ ?_ ?_ ?_ ?_
  · have := div_nonneg hxCnn h1k.le
    linarith
  · intro ω hω
    obtain ⟨m, hm1, hm2⟩ := hmainDet ω hω
    refine (calTime_le_main hk1 m hm1).trans (ENNReal.ofReal_le_ofReal ?_)
    have := div_le_div_of_nonneg_right hm2 h1k.le
    linarith
  · intro ω
    exact calTime_le_safe hk _ _ (roundTotal_top_or _ _)
  · -- probability of the complement
    have hsub : (XY ⁻¹' G0)ᶜ ⊆
        {ω | ∃ j : ℕ, pilotRho (Module.finrank ℝ E) k0 α j <
          ‖olsCount u (roundCount w0 (2 ^ j)) (obsTape u θ ξP ω) - θ‖} ∪
        {ω | ∃ j, commitAt e k ol (pilotV u w0 (obsTape u θ ξP ω)) j ∧ ∃ n : ℕ, 1 ≤ n ∧
          boundary (Module.finrank ℝ E) n α ≤
            freshQ u (ow j (pilotV u w0 (obsTape u θ ξP ω) j)) θ (obsTape u θ ξC ω) n} := by
      intro ω hω
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      refine hω ⟨fun j => ?_, h2⟩
      by_contra hj
      push Not at hj
      exact h1 ⟨j, hj⟩
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have h1 := pilot_concentration u hw0 hk0 hM0 hindP hξP θ hα0 hα1
    have h2 := confirm_coverage u hw0 hk0 hM0 hk hk1.le e hor.design_mem hol how hξPm hξCm hindC
      hξC hPC θ hα0 hα1
    refine (add_le_add h1 h2).trans ?_
    rw [← ENNReal.ofReal_add hα0.le hα0.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- independence of the safeguard tape
    have := setLIntegral_indepFun hXY hYF hIF hG0.compl hγ
    exact this
  · -- mean of the safeguard bound
    have hmean := safeguard_mean u Q hQ hw0 hk0 hM0 hindF hξF hξFm θ hδ0 hδ1 a0 hC0 hC0le hJm hJ
      hBup
    have hsplit : ∫⁻ ω, γ (obsTape u θ ξF ω) ∂P =
        (∫⁻ ω, roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ ξF ω))) ∂P) /
          ENNReal.ofReal k + 1 := by
      simp only [γ]
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      simp only [div_eq_mul_inv]
      exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (by simpa using hk))
    rw [hsplit, ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos hk]
    gcongr

end Procedure

/-! ### `cor:v10g-target`: the order of the remainder -/

section Remainder

lemma log_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
  linarith

/-- `D_extra(J) ≤ 24 A log J`. -/
lemma Dextra_le {A d J : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d) (hJ : 1 ≤ J) :
    Dextra A d J ≤ 24 * A * Real.log J := by
  have hlam : 0 ≤ Real.log J := Real.log_nonneg hJ
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hb1 : (1 : ℝ) ≤ bDm A := le_max_left _ _
  have ha0 : 0 ≤ A * (d + 2 * Real.log 8) := by positivity
  have hden : 0 < A * (d + 2 * Real.log 8) + bDm A + 1 := by linarith
  have hx : 0 ≤ 4 * A * Real.log J / (A * (d + 2 * Real.log 8) + bDm A + 1) := by positivity
  have h1 := log_one_add_le hx
  have h2 : bDm A * (4 * A * Real.log J / (A * (d + 2 * Real.log 8) + bDm A + 1)) ≤
      4 * A * Real.log J := by
    rw [← mul_div_assoc, div_le_iff₀ hden]
    have h3 : 0 ≤ 4 * A * Real.log J := by positivity
    nlinarith [mul_nonneg h3 (by linarith : 0 ≤ A * (d + 2 * Real.log 8) + 1)]
  have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * bDm A)
  unfold Dextra
  nlinarith

/-- `r_C` at `α = 1/(8 J²)` is affine in `log J`. -/
lemma rC_split (d k c0 : ℝ) {J : ℝ} (hJ : 0 < J) :
    rC d k c0 (1 / (8 * J ^ 2)) =
      rC d k c0 (1 / 8) + 2 * (1 + 1 / k) * (1 + k) / c0 * Real.log J := by
  have h1 : Real.log (1 / (1 / (8 * J ^ 2))) = Real.log 8 + 2 * Real.log J := by
    rw [one_div_one_div, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have h2 : Real.log (1 / (1 / 8 : ℝ)) = Real.log 8 := by rw [one_div_one_div]
  unfold rC
  rw [h1, h2]
  ring

/-- `a_F` is affine in `log(1/δ)`. -/
lemma aF_split (d C0 : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    aF d δ C0 = aF d 1 C0 + 8 / C0 * Real.log (1 / δ) := by
  have h1 : Real.log (2 / δ) = Real.log 2 + Real.log (1 / δ) := by
    rw [Real.log_div (by norm_num) hδ.ne', Real.log_div one_ne_zero hδ.ne', Real.log_one]
    ring
  unfold aF
  rw [h1, div_one]
  ring

/-- **Order of the remainder** (`cor:v10g-target`, "`R₁₀ = O(1 + log log(1/δ))` as
`δ ↓ 0`" for each fixed instance and fixed `s`).  With the instance constants fixed there
is `K` such that for all `0 < δ ≤ 1/4` and every admissible `J`
(`1 + log(1/δ) ≤ J < 3 + log(1/δ)`), `R₁₀ ≤ K (1 + log log(1/δ))`.  Here `A` is the pilot
constant, `c₀ = c_* C`, `q = |X|`, and `H = H_δ`. -/
theorem R10_order {A d k c0 q C0 : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d) (hk : 0 < k) (hk1 : k < 1)
    (hc0 : 0 < c0) (hq : 0 ≤ q) (hC0 : 0 < C0) :
    ∃ K : ℝ, ∀ δ J : ℝ, 0 < δ → δ ≤ 1 / 4 → 1 + Real.log (1 / δ) ≤ J →
      J < 3 + Real.log (1 / δ) →
      R10 (Dextra A d J) (rC d k c0 (1 / (8 * J ^ 2)))
          (2 * bC k c0 * Real.log (aC d k c0 δ (1 / (8 * J ^ 2)) + bC k c0 + 1)) k J
          (Hdelta q d δ C0) ≤ K * (1 + Real.log (Real.log (1 / δ))) := by
  set r0 := rC d k c0 (1 / 8) with hr0
  set r1 := 2 * (1 + 1 / k) * (1 + k) / c0 with hr1
  set M := (1 + k) ^ 2 / c0 + r0 + r1 + bC k c0 + 1 with hM
  set f1 := aF d 1 C0 + 8 / C0 with hf1
  set h1 := q + f1 + 2 * bF C0 * (f1 + bF C0) + 2 + 16 / C0 with hh1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl8 : 0 ≤ Real.log (1 / (1 / 8 : ℝ)) := Real.log_nonneg (by norm_num)
  have hbD : 0 ≤ bD d k := by unfold bD; positivity
  have hr0n : 0 ≤ r0 := by
    rw [hr0]
    unfold rC
    refine div_nonneg (add_nonneg (mul_nonneg (by linarith) ?_)
      (mul_nonneg (by positivity) ?_)) hc0.le
    · exact add_nonneg (add_nonneg (mul_nonneg (by linarith) hl2) hbD) (by norm_num)
    · exact add_nonneg (mul_nonneg (by linarith) hl8) hbD
  have hr1n : 0 ≤ r1 := by rw [hr1]; positivity
  have hbC1 : (1 : ℝ) ≤ bC k c0 := le_max_left _ _
  have hbF1 : (1 : ℝ) ≤ bF C0 := le_max_left _ _
  have hcoef : 0 ≤ (1 + k) ^ 2 / c0 := by positivity
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have haF1 : 0 ≤ aF d 1 C0 := aF_nonneg hd one_pos le_rfl hC0
  have h8C : 0 ≤ 8 / C0 := by positivity
  have h16C : 0 ≤ 16 / C0 := by positivity
  have hf1n : 0 ≤ f1 := by rw [hf1]; linarith
  have hh1n : 0 ≤ h1 := by
    rw [hh1]
    have : 0 ≤ 2 * bF C0 * (f1 + bF C0) := by positivity
    linarith
  have h1k : 0 < 1 - k := by linarith
  refine ⟨(48 * A + (r0 + 2 * r1) + 2 * bC k c0 * (Real.log M + 2) + 1) / (1 - k) + 1 +
    h1 / (4 * k) + 1 / 4, ?_⟩
  intro δ J hδ0 hδ4 hJ1 hJ3
  set L := Real.log (1 / δ) with hL
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hL1 : 1 ≤ L := by
    have h4 : (4 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have := Real.log_le_log (by norm_num) h4
    have := Real.log_two_gt_d9
    linarith
  have hJ2 : 2 ≤ J := by linarith
  have hJ0 : 0 < J := by linarith
  set lam := Real.log J with hlam
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by linarith)
  have hlamJ : lam ≤ J := by
    have := Real.log_le_sub_one_of_pos hJ0
    linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  set T := 1 + Real.log L with hT
  have hT1 : 1 ≤ T := by linarith
  have hlamT : lam ≤ 2 * T := by
    have e1 : lam ≤ Real.log (4 * L) := Real.log_le_log hJ0 (by linarith)
    have e2 : Real.log (4 * L) = Real.log 4 + Real.log L :=
      Real.log_mul (by norm_num) (by linarith)
    have := Real.log_two_lt_d9
    linarith
  -- (1) discovery extra
  have hD : Dextra A d J ≤ 48 * A * T := by
    have e1 := Dextra_le hA hd (by linarith : (1 : ℝ) ≤ J)
    have e2 := mul_nonneg hA (sub_nonneg.mpr hlamT)
    linarith
  -- (2) r_C
  have hrCeq : rC d k c0 (1 / (8 * J ^ 2)) = r0 + r1 * lam := rC_split d k c0 hJ0
  have hrC : rC d k c0 (1 / (8 * J ^ 2)) ≤ (r0 + 2 * r1) * T := by
    rw [hrCeq]
    have e1 := mul_nonneg hr1n (sub_nonneg.mpr hlamT)
    have e2 := mul_nonneg hr0n (sub_nonneg.mpr hT1)
    linarith
  -- (3) the confirmation logarithm
  have haCeq : aC d k c0 δ (1 / (8 * J ^ 2)) = (1 + k) ^ 2 / c0 * L + (r0 + r1 * lam) := by
    unfold aC
    rw [hrCeq]
    ring
  have haCn : 0 ≤ aC d k c0 δ (1 / (8 * J ^ 2)) := by
    rw [haCeq]
    have : 0 ≤ (1 + k) ^ 2 / c0 * L := mul_nonneg hcoef (by linarith)
    have : 0 ≤ r1 * lam := mul_nonneg hr1n hlam0
    linarith
  have haCle : aC d k c0 δ (1 / (8 * J ^ 2)) + bC k c0 + 1 ≤ M * J := by
    rw [haCeq, hM]
    have e1 := mul_le_mul_of_nonneg_left (by linarith : L ≤ J) hcoef
    have e2 := mul_le_mul_of_nonneg_left hlamJ hr1n
    have e3 := mul_nonneg hr0n (by linarith : (0 : ℝ) ≤ J - 1)
    have e4 := mul_nonneg (by linarith : (0 : ℝ) ≤ bC k c0) (by linarith : (0 : ℝ) ≤ J - 1)
    linarith
  have hLC : 2 * bC k c0 * Real.log (aC d k c0 δ (1 / (8 * J ^ 2)) + bC k c0 + 1) ≤
      2 * bC k c0 * (Real.log M + 2) * T := by
    have e1 : Real.log (aC d k c0 δ (1 / (8 * J ^ 2)) + bC k c0 + 1) ≤ Real.log (M * J) :=
      Real.log_le_log (by linarith) haCle
    have e2 : Real.log (M * J) = Real.log M + lam := Real.log_mul (by linarith) hJ0.ne'
    have e3 : Real.log M + lam ≤ (Real.log M + 2) * T := by
      have := mul_nonneg hlogM (sub_nonneg.mpr hT1)
      linarith
    have e4 := mul_le_mul_of_nonneg_left (e1.trans (e2.le.trans e3))
      (by linarith : (0 : ℝ) ≤ 2 * bC k c0)
    linarith
  -- (4) the safeguard term
  have hH : Hdelta q d δ C0 ≤ h1 * J := by
    have haFeq : aF d δ C0 = aF d 1 C0 + 8 / C0 * L := aF_split d C0 hδ0
    have haFn : 0 ≤ aF d δ C0 := by
      rw [haFeq]
      have : 0 ≤ 8 / C0 * L := mul_nonneg h8C (by linarith)
      linarith
    have haFJ : aF d δ C0 ≤ f1 * J := by
      rw [haFeq, hf1]
      have e1 := mul_le_mul_of_nonneg_left (by linarith : L ≤ J) h8C
      have e2 := mul_nonneg haF1 (by linarith : (0 : ℝ) ≤ J - 1)
      linarith
    have hlog : Real.log (aF d δ C0 + bF C0 + 1) ≤ (f1 + bF C0) * J := by
      have e0 := log_one_add_le (x := aF d δ C0 + bF C0) (by linarith)
      have e : aF d δ C0 + bF C0 + 1 = 1 + (aF d δ C0 + bF C0) := by ring
      rw [e]
      have e2 := mul_nonneg (by linarith : (0 : ℝ) ≤ bF C0) (by linarith : (0 : ℝ) ≤ J - 1)
      linarith
    have e3 := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * bF C0)
    have e4 := mul_nonneg hq (by linarith : (0 : ℝ) ≤ J - 1)
    have e5 := mul_nonneg h16C (by linarith : (0 : ℝ) ≤ J - 1)
    unfold Hdelta logBudget
    rw [hh1]
    linarith
  have hHterm : Hdelta q d δ C0 / (4 * k * J ^ 2) ≤ h1 / (4 * k) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : h1 * J ≤ h1 * J ^ 2 := by
      have := mul_nonneg hh1n (mul_nonneg hJ0.le (by linarith : (0 : ℝ) ≤ J - 1))
      linarith
    have e2 := mul_le_mul_of_nonneg_right (hH.trans e1) (by positivity : (0 : ℝ) ≤ 4 * k)
    linarith
  have hJterm : 1 / (4 * J ^ 2) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hJ2' : 1 ≤ J ^ 2 := one_le_pow₀ (by linarith only [hJ2])
    linarith only [hJ2']
  have hsum : (Dextra A d J + rC d k c0 (1 / (8 * J ^ 2)) +
      2 * bC k c0 * Real.log (aC d k c0 δ (1 / (8 * J ^ 2)) + bC k c0 + 1) + 1) / (1 - k) ≤
      (48 * A + (r0 + 2 * r1) + 2 * bC k c0 * (Real.log M + 2) + 1) / (1 - k) * T := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ h1k.le
    linarith
  have hpos : 0 ≤ h1 / (4 * k) := by positivity
  have e6 := mul_nonneg hpos (sub_nonneg.mpr hT1)
  unfold R10
  linarith

/-- **From the finite-confidence bound to the rate.**  If `f δ` (the expected stopping time
at confidence `δ`) satisfies `eq:v10g-target` with a remainder of order
`1 + log log(1/δ)`, i.e. `f δ ≤ D + c log(1/δ) + K (1 + log log(1/δ))` for `0 < δ ≤ 1/4`,
then `limsup_{δ ↓ 0} f δ / log(1/δ) ≤ c`: for every `η > 0` the ratio is eventually at
most `c + η`.  With `c = (1 + s) / C` this is the rate reached by the procedure of
`app:bay-finite` at slack `s`. -/
theorem rate_of_target {f : ℝ → ℝ} {D c K : ℝ}
    (h : ∀ δ, 0 < δ → δ ≤ 1 / 4 →
      f δ ≤ D + c * Real.log (1 / δ) + K * (1 + Real.log (Real.log (1 / δ)))) :
    ∀ η > 0, ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 → f δ / Real.log (1 / δ) ≤ c + η := by
  intro η hη
  set L0 := max 1 (max (2 * (|D| + |K|) / η) ((4 * |K| / η) ^ 2)) with hL0
  have hL01 : 1 ≤ L0 := le_max_left _ _
  have hL02 : 2 * (|D| + |K|) / η ≤ L0 := (le_max_left _ _).trans (le_max_right _ _)
  have hL03 : (4 * |K| / η) ^ 2 ≤ L0 := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨min (1 / 4) (Real.exp (-L0)), lt_min (by norm_num) (Real.exp_pos _),
    fun δ hδ0 hδlt => ?_⟩
  have hδ4 : δ ≤ 1 / 4 := (hδlt.trans_le (min_le_left _ _)).le
  have hδe : δ < Real.exp (-L0) := hδlt.trans_le (min_le_right _ _)
  set L := Real.log (1 / δ) with hL
  have hLeq : L = -Real.log δ := by rw [hL, one_div, Real.log_inv]
  have hLgt : L0 < L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this
    linarith
  have hLpos : 0 < L := by linarith
  have hsq0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hsq2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
    have h1 := Real.log_le_sub_one_of_pos hsq0
    have h2 : Real.log L = 2 * Real.log (Real.sqrt L) := by
      rw [Real.log_sqrt hLpos.le]
      ring
    linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hK : K * (1 + Real.log L) ≤ |K| * (1 + 2 * Real.sqrt L) := by
    have e1 : K * (1 + Real.log L) ≤ |K| * (1 + Real.log L) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    have e2 : |K| * (1 + Real.log L) ≤ |K| * (1 + 2 * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
    linarith
  have h1 : |D| + |K| ≤ η * L / 2 := by
    rw [div_le_iff₀ hη] at hL02
    nlinarith
  have h2 : 2 * |K| * Real.sqrt L ≤ η * L / 2 := by
    have e1 : 4 * |K| / η ≤ Real.sqrt L := by
      apply Real.le_sqrt_of_sq_le
      linarith
    rw [div_le_iff₀ hη] at e1
    have e2 := mul_le_mul_of_nonneg_right e1 hsq0.le
    nlinarith
  have hf := h δ hδ0 hδ4
  rw [div_le_iff₀ hLpos]
  have hD : D ≤ |D| := le_abs_self D
  nlinarith

end Remainder

/-! ### `cor:v10g-target` and `prop:bay-finite` on the model -/

section Target

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {𝒜 : Type*}

/-- **Finite-confidence correlated confirmation bound** (`cor:v10g-target`,
`eq:v10g-target`) for the Gaussian linear model of `v10g_expectation`, with `k = s/16` and
`α = 1/(8 J²)`, `J ≥ 1`:
`𝔼_θ τ ≤ (D₀ + q)/(1 - k) + (1 + s) C⁻¹ log(1/δ) + R₁₀`.
The hypotheses are those of `v10g_expectation`.  The order of `R₁₀` is `R10_order`. -/
theorem v10g_target [IsProbabilityMeasure P] [Countable 𝒜] (u : X → E) (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 s J δ : ℝ}
    (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {e : ℕ → ℝ}
    (he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j)
    {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u Q w0 (s / 16) e oa ow ol ou)
    (hol : ∀ j, Measurable (ol j)) (how : ∀ j x, Measurable (fun v => ow j v x))
    {ξP ξC ξF : X → ℕ → Ω → ℝ}
    (hξPm : ∀ x i, Measurable (ξP x i)) (hξCm : ∀ x i, Measurable (ξC x i))
    (hξFm : ∀ x i, Measurable (ξF x i))
    (hindP : iIndepFun (fun p : X × ℕ => ξP p.1 p.2) P)
    (hξP : ∀ x i, HasLaw (ξP x i) (gaussianReal 0 1) P)
    (hindC : iIndepFun (fun p : X × ℕ => ξC p.1 p.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hindF : iIndepFun (fun p : X × ℕ => ξF p.1 p.2) P)
    (hξF : ∀ x i, HasLaw (ξF x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (hPCF : IndepFun (fun ω => ((fun x i => ξP x i ω : X → ℕ → ℝ), (fun x i => ξC x i ω : X → ℕ → ℝ)))
      (fun ω x i => ξF x i ω) P)
    (θ : E) (aS : 𝒜) {wS : X → ℝ} (hwS : wS ∈ simplex X) {C : ℝ} (hC : 0 < C)
    (hCle : C ≤ gInfo u (Q aS) θ wS) (a0 : 𝒜) {C0 : ℝ} (hC0 : 0 < C0)
    (hC0le : C0 ≤ gInfo u (Q a0) θ w0)
    {Zlow : ℕ → (X → ℕ → ℝ) → (X → ℕ → ℝ) → ℕ → ℝ} {Bbar : ℕ → ℝ}
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ}
    (hZ : ∀ j y y' (n : ℕ), confirmZ u (ow j (pilotV u w0 y j)) (pilotV u w0 y j)
      (ol j (pilotV u w0 y j)) y' n - 1 ≤ Zlow j y y' n)
    (hBup : ∀ n : ℕ, Bbar n ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 1)
    (hJm : ∀ n a, Measurable (fun Y : X → ℕ → ℝ => Jlow n Y a))
    (hJ' : ∀ (n : ℕ) Y a, gInfo u (Q a) (olsCount u (roundCount w0 n) Y)
      (fun x => (roundCount w0 n x : ℝ)) - 1 ≤ Jlow n Y a) :
    ∫⁻ ω, calTime (s / 16) (mainObs u w0 e (s / 16) ow ol Zlow Bbar (obsTape u θ ξP ω)
          (obsTape u θ ξC ω))
        (roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ ξF ω)))) ∂P ≤
      ENNReal.ofReal
        ((D0 (pilotA ℓ k0 (s / 16) C) (Module.finrank ℝ E) (Fintype.card X) + Fintype.card X) /
            (1 - s / 16) + (1 + s) * (1 / C) * Real.log (1 / δ) +
          R10 (Dextra (pilotA ℓ k0 (s / 16) C) (Module.finrank ℝ E) J)
            (rC (Module.finrank ℝ E) (s / 16) (cstar (s / 16) * C) (1 / (8 * J ^ 2)))
            (2 * bC (s / 16) (cstar (s / 16) * C) *
              Real.log (aC (Module.finrank ℝ E) (s / 16) (cstar (s / 16) * C) δ
                (1 / (8 * J ^ 2)) + bC (s / 16) (cstar (s / 16) * C) + 1))
            (s / 16) J (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0)) := by
  have hk : 0 < s / 16 := by positivity
  have hk1 : s / 16 < 1 := by linarith
  have hα0 : 0 < 1 / (8 * J ^ 2) := by positivity
  have hα1 : 1 / (8 * J ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hA : 0 ≤ pilotA ℓ k0 (s / 16) C := by
    have : 0 < 1 - s / 16 := by linarith
    unfold pilotA
    positivity
  exact (v10g_expectation u Q hQ hw0 hℓ hu hk0 hM0 hk hk1 hα0 hα1 hδ0 hδ1 he1 he2 hor hol how
    hξPm hξCm hξFm hindP hξP hindC hξC hindF hξF hPC hPCF θ aS hwS hC hCle a0 hC0 hC0le hZ hBup
    hJm hJ').trans (ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans
      (target_bound hs0 hs1 hC hδ0 hδ1 hJ hA (Nat.cast_nonneg _))))

/-- **Finite-confidence discovery, frozen confirmation, and safeguard**
(`prop:bay-finite`) for the Gaussian linear model, as the conjunction of `v10g_safe` and
`v10g_target` with the screened sets `Q a = {λ : r_λ(a) > ε}`: the procedure is
`(ε, δ)`-safe, and `𝔼_θ τ ≤ D + (1 + s) C⁻¹ log(1/δ) + R₁₀` with
`D = (D₀ + q)/(1 - s/16)` independent of `δ`.  `R₁₀ = O(1 + log log(1/δ))` is
`R10_order`. -/
theorem bay_finite [IsProbabilityMeasure P] [Countable 𝒜] (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {ℓ k0 s J δ : ℝ}
    (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {e : ℕ → ℝ}
    (he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j)
    {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (hor : OracleContract u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) e oa ow ol ou)
    (hol : ∀ j, Measurable (ol j)) (how : ∀ j x, Measurable (fun v => ow j v x))
    {ξP ξC ξF : X → ℕ → Ω → ℝ}
    (hξPm : ∀ x i, Measurable (ξP x i)) (hξCm : ∀ x i, Measurable (ξC x i))
    (hξFm : ∀ x i, Measurable (ξF x i))
    (hindP : iIndepFun (fun p : X × ℕ => ξP p.1 p.2) P)
    (hξP : ∀ x i, HasLaw (ξP x i) (gaussianReal 0 1) P)
    (hindC : iIndepFun (fun p : X × ℕ => ξC p.1 p.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hindF : iIndepFun (fun p : X × ℕ => ξF p.1 p.2) P)
    (hξF : ∀ x i, HasLaw (ξF x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (hPCF : IndepFun (fun ω => ((fun x i => ξP x i ω : X → ℕ → ℝ), (fun x i => ξC x i ω : X → ℕ → ℝ)))
      (fun ω x i => ξF x i ω) P)
    (θ : E) (aS : 𝒜) {wS : X → ℝ} (hwS : wS ∈ simplex X) {C : ℝ} (hC : 0 < C)
    (hCle : C ≤ gInfo u (strictAlt φ (supp aS) (hne aS) ε) θ wS) (a0 : 𝒜) {C0 : ℝ}
    (hC0 : 0 < C0) (hC0le : C0 ≤ gInfo u (strictAlt φ (supp a0) (hne a0) ε) θ w0)
    {Zlow : ℕ → (X → ℕ → ℝ) → (X → ℕ → ℝ) → ℕ → ℝ} {Bbar : ℕ → ℝ}
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ}
    (hZ : ∀ j y y' (n : ℕ), confirmZ u (ow j (pilotV u w0 y j)) (pilotV u w0 y j)
      (ol j (pilotV u w0 y j)) y' n - 1 ≤ Zlow j y y' n)
    (hBlo : ∀ n : ℕ, boundary (Module.finrank ℝ E) n (δ / 2) ≤ Bbar n)
    (hBup : ∀ n : ℕ, Bbar n ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 1)
    (hJm : ∀ n a, Measurable (fun Y : X → ℕ → ℝ => Jlow n Y a))
    (hJlo : ∀ (n : ℕ) Y a, gInfo u (strictAlt φ (supp a) (hne a) ε)
      (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ)) - 1 ≤ Jlow n Y a)
    (hJup : ∀ (n : ℕ) Y a, Jlow n Y a ≤ gInfo u (strictAlt φ (supp a) (hne a) ε)
      (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ))) :
    P ({ω | ∃ j, commitAt e (s / 16) ol (pilotV u w0 (obsTape u θ ξP ω)) j ∧ ∃ n : ℕ, 1 ≤ n ∧
          Bbar n ≤ confirmZ u (ow j (pilotV u w0 (obsTape u θ ξP ω) j))
            (pilotV u w0 (obsTape u θ ξP ω) j) (ol j (pilotV u w0 (obsTape u θ ξP ω) j))
            (obsTape u θ ξC ω) n ∧
          ε < regret (supp (oa j (pilotV u w0 (obsTape u θ ξP ω) j))) (hne _) (env φ θ)} ∪
        {ω | ∃ n : ℕ, 1 ≤ n ∧ ∃ a, Bbar n ≤ Jlow n (obsTape u θ ξF ω) a ∧
          ε < regret (supp a) (hne a) (env φ θ)}) ≤ ENNReal.ofReal δ ∧
    ∫⁻ ω, calTime (s / 16) (mainObs u w0 e (s / 16) ow ol Zlow Bbar (obsTape u θ ξP ω)
          (obsTape u θ ξC ω))
        (roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ ξF ω)))) ∂P ≤
      ENNReal.ofReal
        ((D0 (pilotA ℓ k0 (s / 16) C) (Module.finrank ℝ E) (Fintype.card X) + Fintype.card X) /
            (1 - s / 16) + (1 + s) * (1 / C) * Real.log (1 / δ) +
          R10 (Dextra (pilotA ℓ k0 (s / 16) C) (Module.finrank ℝ E) J)
            (rC (Module.finrank ℝ E) (s / 16) (cstar (s / 16) * C) (1 / (8 * J ^ 2)))
            (2 * bC (s / 16) (cstar (s / 16) * C) *
              Real.log (aC (Module.finrank ℝ E) (s / 16) (cstar (s / 16) * C) δ
                (1 / (8 * J ^ 2)) + bC (s / 16) (cstar (s / 16) * C) + 1))
            (s / 16) J (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0)) :=
  ⟨v10g_safe φ supp hne ε u hw0 hk0 hM0 (by positivity) (by linarith) hor hol how hξPm hξCm
      hindC hξC hindF hξF hPC θ hδ0 hδ1 hBlo hJup,
    v10g_target u _ hQ hw0 hℓ hu hk0 hM0 hs0 hs1 hJ hδ0 hδ1 he1 he2 hor hol how hξPm hξCm hξFm
      hindP hξP hindC hξC hindF hξF hPC hPCF θ aS hwS hC hCle a0 hC0 hC0le hZ hBup hJm hJlo⟩

end Target

end JointRootCert
