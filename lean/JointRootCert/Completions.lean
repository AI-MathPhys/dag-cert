/-
Completions, part 1: Theorem `thm:t4-finite-sample` (Finite-sample cost of safeguarded
CD-Joint) as one statement about runs of Algorithm `alg:cd-joint`.

* `CDStep` is the rule of Algorithm 1 at one uncertified step: a globally optimistic
  terminal, a root action containing it, the strongest outside challenger of that action
  together with its minimising inside mixture, the safeguard switch at `ε / 2`
  (`eq:safeguard`) and maximisation of the acquisition score.
* `cdDualCert` is the stopping test of Algorithm 1 in the dual form `eq:bay-main-dual`;
  `cdDualCert_iff` identifies it with worst-case regret over the confidence ellipsoid.
* `cd_joint_run`: for every run, the cost bound `eq:t4-bound`, and `ε`-optimality of the
  returned action whenever the parameter lies in the confidence ellipsoid at the stopping
  time.
* `cd_joint_finite_sample`: the same with the ridge estimator and the self-normalized
  radius `eq:ay-radius`; the only probabilistic input is conditionally sub-Gaussian noise.
-/
import JointRootCert.Assembly
import JointRootCert.SelfNormalized

namespace JointRootCert

open Finset Matrix MeasureTheory
open scoped ENNReal

section CDRun

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- The contrast `g_{z,p} = ψ_z - ∑_{y ∈ S} p_y ψ_y` in coordinates. -/
def cdContrast (ψ : Z → n → ℝ) (S : Finset Z) (z : Z) (p : S → ℝ) : n → ℝ :=
  ψ z - ∑ y, p y • ψ y

/-- The dual objective `g_{z,p}ᵀ m + β ‖g_{z,p}‖_{V⁻¹}` of `eq:bay-main-dual`. -/
noncomputable def cdObj (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β : ℝ) (S : Finset Z)
    (z : Z) (p : S → ℝ) : ℝ :=
  cdContrast ψ S z p ⬝ᵥ m + β * Real.sqrt (qinv V (cdContrast ψ S z p))

/-- The stopping test `R_t(a) ≤ ε` of Algorithm 1, computed through `eq:bay-main-dual`:
`ε ≥ 0` and every outside challenger has an inside mixture with dual objective at most
`ε`, i.e. `[max_{z ∉ S} D_t(z, S)]_+ ≤ ε`. -/
def cdDualCert (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β ε : ℝ) (S : Finset Z) : Prop :=
  0 ≤ ε ∧ ∀ z, z ∉ S → ∃ p ∈ simplex S, cdObj V ψ m β S z p ≤ ε

omit [DecidableEq n] [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma contrast_ofLp (ψ : Z → n → ℝ) (S : Finset Z) (z : Z) (p : S → ℝ) :
    (contrast (fun z => WithLp.toLp 2 (ψ z)) S z p).ofLp = cdContrast ψ S z p := by
  simp [contrast, cdContrast]

/-- **The stopping test is exact (Theorem `thm:bay-main-dual` in coordinates).**  The dual
test holds iff the regret of the support is at most `ε` for every parameter of the
confidence ellipsoid `{θ | (θ - m)ᵀ V (θ - m) ≤ β²}`. -/
theorem cdDualCert_iff {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    {S : Finset Z} (hS : S.Nonempty) {β ε : ℝ} (hβ : 0 ≤ β) (ψ : Z → n → ℝ) (m : n → ℝ) :
    cdDualCert V ψ m β ε S ↔
      ∀ θ : n → ℝ, (θ - m) ⬝ᵥ V *ᵥ (θ - m) ≤ β ^ 2 →
        regret S hS (fun z => ψ z ⬝ᵥ θ) ≤ ε := by
  have key := confidence_ellipsoid_certificate_iff (ε := ε) hV hlam hS hβ
    (fun z => WithLp.toLp 2 (ψ z)) (WithLp.toLp 2 m)
  have henv : ∀ θ : EuclideanSpace ℝ n,
      env (fun z => WithLp.toLp 2 (ψ z)) θ = fun z => ψ z ⬝ᵥ θ.ofLp := by
    intro θ
    funext z
    simp [env, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp only [contrast_ofLp, henv] at key
  unfold cdDualCert cdObj
  rw [← key]
  constructor
  · intro h θ hθ
    exact h (WithLp.toLp 2 θ) hθ
  · intro h θ hθ
    exact h θ.ofLp hθ

omit [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] [Nonempty Z] in
/-- **Dictionary representation.**  If the terminal features are dictionary features
(`ψ_z = φ_{ι z}`), the contrast against any inside mixture is a combination of dictionary
features with `ℓ¹` weight at most `2`. -/
lemma contrast_dict (φ : X → n → ℝ) (ι : Z → X) (S : Finset Z) (z : Z) (p : S → ℝ)
    (hp : p ∈ simplex S) :
    ∃ a : X → ℝ, cdContrast (fun z => φ (ι z)) S z p = ∑ x, a x • φ x ∧ ∑ x, |a x| ≤ 2 := by
  refine ⟨fun x => (if x = ι z then 1 else 0) - ∑ y : S, if x = ι y then p y else 0, ?_, ?_⟩
  · unfold cdContrast
    simp only [sub_smul, sum_sub_distrib, sum_smul, ite_smul, one_smul, zero_smul]
    rw [sum_comm]
    simp
  · calc ∑ x, |(if x = ι z then (1 : ℝ) else 0) - ∑ y : S, if x = ι y then p y else 0|
        ≤ ∑ x, ((if x = ι z then (1 : ℝ) else 0) + ∑ y : S, if x = ι y then p y else 0) := by
          refine sum_le_sum (fun x _ => ?_)
          refine (abs_sub _ _).trans ?_
          have h1 : |(if x = ι z then (1 : ℝ) else 0)| = if x = ι z then (1 : ℝ) else 0 := by
            split_ifs <;> simp
          have h2 : 0 ≤ ∑ y : S, if x = ι y then p y else 0 :=
            sum_nonneg (fun y _ => by split_ifs; exacts [hp.1 y, le_rfl])
          rw [h1, abs_of_nonneg h2]
      _ = 2 := by
          rw [sum_add_distrib, sum_comm]
          simp only [sum_ite_eq', mem_univ, ite_true]
          rw [hp.2]
          norm_num

/-- The safeguarded contrast of `eq:safeguard`: the dual contrast while its estimated
advantage is at most `ε / 2`, the direct contrast otherwise. -/
noncomputable def cdSafeguard (ε : ℝ) (m gdual gdirect : n → ℝ) : n → ℝ :=
  if gdual ⬝ᵥ m ≤ ε / 2 then gdual else gdirect

/-- **One uncertified step of Algorithm 1** with design matrix `V`, estimate `m` and radius
`β`, querying `x`.  Terminal features are `ψ_z = φ_{ι z}`.  There are

* `yopt`, a maximiser of the optimistic index `ψ_yᵀ m + β ‖ψ_y‖_{V⁻¹}` over all terminals,
* a root action `b` whose support contains `yopt` (any tie breaking),
* an outside challenger `z ∉ S(b)` and an inside mixture `p` minimising the dual objective
  of `z` (so `D(z, S(b))` is `cdObj … z p`), such that `D(z', S(b)) ≤ D(z, S(b))` for every
  outside `z'` (stated as: some mixture for `z'` has objective at most `D(z, S(b))`),

and `x` maximises the acquisition score of the safeguarded contrast. -/
def CDStep (V : Matrix n n ℝ) (m : n → ℝ) (β ε : ℝ) (φ : X → n → ℝ) (cost : X → ℝ)
    (ι : Z → X) (supp : A → Finset Z) (x : X) : Prop :=
  ∃ (yopt : Z) (b : A) (z : Z) (p : supp b → ℝ),
    (∀ y, φ (ι y) ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι y))) ≤
      φ (ι yopt) ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι yopt)))) ∧
    yopt ∈ supp b ∧ z ∉ supp b ∧ p ∈ simplex (supp b) ∧
    (∀ q ∈ simplex (supp b), cdObj V (fun z => φ (ι z)) m β (supp b) z p ≤
      cdObj V (fun z => φ (ι z)) m β (supp b) z q) ∧
    (∀ z', z' ∉ supp b → ∃ q ∈ simplex (supp b),
      cdObj V (fun z => φ (ι z)) m β (supp b) z' q ≤
        cdObj V (fun z => φ (ι z)) m β (supp b) z p) ∧
    ∀ x', cdScore V φ cost
        (cdSafeguard ε m (cdContrast (fun z => φ (ι z)) (supp b) z p)
          (φ (ι z) - φ (ι yopt))) x' ≤
      cdScore V φ cost
        (cdSafeguard ε m (cdContrast (fun z => φ (ι z)) (supp b) z p)
          (φ (ι z) - φ (ι yopt))) x

omit [Fintype Z] [Nonempty Z] in
/-- **What one uncertified step guarantees.**  If no action passes the stopping test, the
safeguarded contrast `g` of a `CDStep` satisfies the width bound `eq:cd-width-lemma`, is a
dictionary combination of `ℓ¹` weight at most `2`, and the query maximises its score. -/
theorem cdStep_spec {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    {m : n → ℝ} {β ε : ℝ} (hβ : 0 < β) (hε : 0 ≤ ε) (φ : X → n → ℝ) (cost : X → ℝ)
    (ι : Z → X) (supp : A → Finset Z) {x : X}
    (hunc : ∀ a, ¬ cdDualCert V (fun z => φ (ι z)) m β ε (supp a))
    (hstep : CDStep V m β ε φ cost ι supp x) :
    ∃ g : n → ℝ, ε ^ 2 / (4 * β ^ 2) < qinv V g ∧
      (∃ a : X → ℝ, g = ∑ y, a y • φ y ∧ ∑ y, |a y| ≤ 2) ∧
      ∀ y, cdScore V φ cost g y ≤ cdScore V φ cost g x := by
  obtain ⟨yopt, b, z, p, hopt, hyb, hzb, hp, hmin, hmax, hsel⟩ := hstep
  have hD : ε < cdObj V (fun z => φ (ι z)) m β (supp b) z p := by
    have h := hunc b
    unfold cdDualCert at h
    push Not at h
    obtain ⟨z', hz', hall⟩ := h hε
    obtain ⟨q, hq, hle⟩ := hmax z' hz'
    exact (hall q hq).trans_le hle
  -- the one-vertex mixture at the optimistic terminal
  have hsum1 : ∑ y : supp b, (if (y : Z) = yopt then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_coe_sort (supp b) (fun y => if y = yopt then (1 : ℝ) else 0)]
    simp [hyb]
  have hpv : (fun y : supp b => if (y : Z) = yopt then (1 : ℝ) else 0) ∈ simplex (supp b) :=
    ⟨fun y => by dsimp only; split_ifs <;> norm_num, hsum1⟩
  have hcv : cdContrast (fun z => φ (ι z)) (supp b) z
      (fun y : supp b => if (y : Z) = yopt then (1 : ℝ) else 0) = φ (ι z) - φ (ι yopt) := by
    unfold cdContrast
    congr 1
    rw [Finset.sum_coe_sort (supp b)
      (fun y => (if y = yopt then (1 : ℝ) else 0) • φ (ι y))]
    simp [hyb]
  by_cases hc : cdContrast (fun z => φ (ι z)) (supp b) z p ⬝ᵥ m ≤ ε / 2
  · refine ⟨cdContrast (fun z => φ (ι z)) (supp b) z p,
      cd_width hV hlam hε hβ m _ hD (Or.inl hc), contrast_dict φ ι (supp b) z p hp, ?_⟩
    simpa [cdSafeguard, hc] using hsel
  · refine ⟨φ (ι z) - φ (ι yopt), cd_width hV hlam hε hβ m _ ?_
      (Or.inr ⟨φ (ι z), φ (ι yopt), rfl, hopt z⟩), ?_, ?_⟩
    · have h := hmin _ hpv
      unfold cdObj at h hD
      rw [hcv] at h
      linarith
    · rw [← hcv]
      exact contrast_dict φ ι (supp b) z _ hpv
    · simpa [cdSafeguard, hc] using hsel

omit [DecidableEq X] in
lemma design_det_mono {lam : ℝ} (hlam : 0 < lam) (φ : X → n → ℝ) (x : ℕ → X) :
    Monotone (fun t => (design lam φ x t).det) := by
  refine monotone_nat_of_le_succ (fun t => ?_)
  rw [design_det_succ hlam]
  have h1 := (design_det_pos hlam φ x t).le
  have h2 := (design_coercive lam φ x t).qinv_nonneg hlam (φ (x t))
  nlinarith

/-- **Theorem `thm:t4-finite-sample` for a run of safeguarded CD-Joint.**

Fixed-feature model: queries `x ∈ X` with features `φ x`, `‖φ x‖² ≤ Lsq`, and costs
`0 < cost x ≤ cmax`; terminals are dictionary elements (`ι : Z → X`); `V_t = design` is the
design matrix of the queries `x 0, …, x (t-1)`; `m t` and `β t` are the estimate and the
radius at step `t`, with `β` positive and nondecreasing over the uncertified steps.

A run with `τ` queries: at each step `t < τ` no action passes the stopping test
(`cdDualCert`) and the query `x t` follows the rule `CDStep` of Algorithm 1.  Then

* the cumulative cost satisfies `eq:t4-bound`, with `β_{τ-1}`;
* if the run then returns an action `r` that passes the stopping test at time `τ`, then `r`
  is `ε`-optimal for every parameter `θ*` in the confidence ellipsoid at time `τ`
  (`(θ* - m_τ)ᵀ V_τ (θ* - m_τ) ≤ β_τ²`, the coverage event). -/
theorem cd_joint_run {lam : ℝ} (hlam : 0 < lam) (φ : X → n → ℝ) (cost : X → ℝ)
    {cmax Lsq ε : ℝ} (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax)
    (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε) (ι : Z → X) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (τ : ℕ) (x : ℕ → X) (m : ℕ → n → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ t < τ, 0 < β t) (hβmono : ∀ s t, s ≤ t → t < τ → β s ≤ β t)
    (hrun : ∀ t < τ,
      (∀ a, ¬ cdDualCert (design lam φ x t) (fun z => φ (ι z)) (m t) (β t) ε (supp a)) ∧
      CDStep (design lam φ x t) (m t) (β t) ε φ cost ι supp (x t)) :
    ∑ t ∈ range τ, cost (x t) ≤
        16 * cmax * (1 + Lsq / lam) * β (τ - 1) ^ 2 / ε ^ 2 *
          Real.log ((design lam φ x τ).det / lam ^ Fintype.card n) ∧
      ∀ (r : A) (θs : n → ℝ), 0 ≤ β τ →
        cdDualCert (design lam φ x τ) (fun z => φ (ι z)) (m τ) (β τ) ε (supp r) →
        (θs - m τ) ⬝ᵥ design lam φ x τ *ᵥ (θs - m τ) ≤ β τ ^ 2 →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε := by
  refine ⟨?_, fun r θs hβτ hcert hcov =>
    (cdDualCert_iff (design_coercive lam φ x τ) hlam (hne r) hβτ _ _).mp hcert θs hcov⟩
  obtain ⟨x0⟩ : Nonempty X := ⟨ι (Classical.arbitrary Z)⟩
  have hcmax : 0 < cmax := (hcost x0).1.trans_le (hcost x0).2
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ x0)).trans (hφ x0)
  rcases Nat.eq_zero_or_pos τ with rfl | hτ
  · simp [design_det_zero, (pow_pos hlam _).ne']
  have hspec : ∀ t, t < τ → ∃ g : n → ℝ, ε ^ 2 / (4 * β t ^ 2) < qinv (design lam φ x t) g ∧
      (∃ a : X → ℝ, g = ∑ y, a y • φ y ∧ ∑ y, |a y| ≤ 2) ∧
      ∀ y, cdScore (design lam φ x t) φ cost g y ≤ cdScore (design lam φ x t) φ cost g (x t) :=
    fun t ht => cdStep_spec (design_coercive lam φ x t) hlam (hβpos t ht) hε.le φ cost ι supp
      (hrun t ht).1 (hrun t ht).2
  choose! g hg using hspec
  exact cd_joint_cost hlam φ cost hcost hcmax hφ hLsq hε (hβpos (τ - 1) (by omega)) τ x g β
    (fun t ht => ⟨hβpos t ht, hβmono t (τ - 1) (by omega) (by omega)⟩)
    (fun t ht => (hg t ht).1.le) (fun t ht => (hg t ht).2.1) (fun t ht => (hg t ht).2.2)

end CDRun

/-! ### The run with the ridge estimator and the self-normalized radius -/

section CDProb

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- Ridge estimate `θ̂_t = V_t⁻¹ ∑_{s<t} Y_s φ_{x_s}` from the observations
`Y_s = φ_{x_s}ᵀ θ* + η_s`. -/
noncomputable def ridgeEst (lam : ℝ) (φ : X → n → ℝ) (θs : n → ℝ) (x : ℕ → X) (η : ℕ → ℝ)
    (t : ℕ) : n → ℝ :=
  (design lam φ x t)⁻¹ *ᵥ ∑ s ∈ range t, (φ (x s) ⬝ᵥ θs + η s) • φ (x s)

/-- The self-normalized radius `eq:ay-radius`:
`β = √λ B + σ √(2 log (1/δ) + log (det V / λ^d))`. -/
noncomputable def ayRadius (σ lam δ B : ℝ) (V : Matrix n n ℝ) : ℝ :=
  Real.sqrt lam * B +
    σ * Real.sqrt (2 * Real.log (1 / δ) + Real.log (V.det / lam ^ Fintype.card n))

omit [DecidableEq X] in
lemma ayRadius_design_mono {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (φ : X → n → ℝ)
    (x : ℕ → X) {s t : ℕ} (hst : s ≤ t) :
    ayRadius σ lam δ B (design lam φ x s) ≤ ayRadius σ lam δ B (design lam φ x t) := by
  unfold ayRadius
  have hpow : 0 < lam ^ Fintype.card n := pow_pos hlam _
  have h1 : (design lam φ x s).det / lam ^ Fintype.card n ≤
      (design lam φ x t).det / lam ^ Fintype.card n :=
    div_le_div_of_nonneg_right (design_det_mono hlam φ x hst) hpow.le
  have h2 := Real.log_le_log (div_pos (design_det_pos hlam φ x s) hpow) h1
  have h3 : Real.sqrt (2 * Real.log (1 / δ) +
        Real.log ((design lam φ x s).det / lam ^ Fintype.card n)) ≤
      Real.sqrt (2 * Real.log (1 / δ) +
        Real.log ((design lam φ x t).det / lam ^ Fintype.card n)) :=
    Real.sqrt_le_sqrt (by linarith)
  have h4 := mul_le_mul_of_nonneg_left h3 hσ.le
  linarith

omit [DecidableEq X] in
lemma ayRadius_design_pos {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hB : 0 ≤ B) (φ : X → n → ℝ) (x : ℕ → X) (t : ℕ) :
    0 < ayRadius σ lam δ B (design lam φ x t) := by
  unfold ayRadius
  have hpow : 0 < lam ^ Fintype.card n := pow_pos hlam _
  have h0 : (1 : ℝ) ≤ (design lam φ x t).det / lam ^ Fintype.card n := by
    rw [le_div_iff₀ hpow, one_mul, ← design_det_zero lam φ x]
    exact design_det_mono hlam φ x (Nat.zero_le t)
  have h1 : 0 ≤ Real.log ((design lam φ x t).det / lam ^ Fintype.card n) := Real.log_nonneg h0
  have h2 : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have h3 : 0 < Real.sqrt (2 * Real.log (1 / δ) +
      Real.log ((design lam φ x t).det / lam ^ Fintype.card n)) := Real.sqrt_pos.mpr (by linarith)
  have h4 : 0 ≤ Real.sqrt lam * B := mul_nonneg (Real.sqrt_nonneg _) hB
  have h5 := mul_pos hσ h3
  linarith

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Finite-sample cost of safeguarded CD-Joint (Theorem `thm:t4-finite-sample`), end to
end.**

Model.  Fixed features `φ x` with `‖φ x‖² ≤ Lsq`, costs `0 < cost x ≤ cmax`, terminals in
the dictionary (`ι`), parameter `θ*` with `‖θ*‖ ≤ B`.  The query `x s` is chosen from the
past (`hx`: predictable), and the observation is `Y_s = φ_{x_s}ᵀ θ* + η_s` with `η_s`
conditionally `σ`-sub-Gaussian given the past (`hη`, `hsub`; the manuscript has `σ = 1`).
The procedure uses the ridge estimate `ridgeEst` and the radius `ayRadius` (`eq:ay-radius`)
on the design matrix `V_t = λ I + ∑_{s<t} φ_{x_s} φ_{x_s}ᵀ`.

Procedure.  On every sample path, each of the `τ ω` queries is an uncertified step of
Algorithm 1 (`CDStep`, no action passing `cdDualCert`), and the returned action `rec ω`
passes the stopping test at time `τ ω`.

Conclusion.  Outside an event of probability at most `δ`, the returned action is
`ε`-optimal and the cumulative cost satisfies `eq:t4-bound`.

Nothing is assumed about coverage, widths or the dictionary representation; the stopping
count `τ ω` is part of the data of the run (termination is not claimed). -/
theorem cd_joint_finite_sample [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) {η : ℕ → Ω → ℝ} (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ)
    (τ : Ω → ℕ) (rec : Ω → A)
    (hrun : ∀ ω, ∀ t < τ ω,
      (∀ a, ¬ cdDualCert (design lam φ (fun s => x s ω) t) (fun z => φ (ι z))
        (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t)
        (ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)) ε (supp a)) ∧
      CDStep (design lam φ (fun s => x s ω) t)
        (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t)
        (ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)) ε φ cost ι supp (x t ω))
    (hstop : ∀ ω, cdDualCert (design lam φ (fun s => x s ω) (τ ω)) (fun z => φ (ι z))
        (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) (τ ω))
        (ayRadius σ lam δ B (design lam φ (fun s => x s ω) (τ ω))) ε (supp (rec ω))) :
    μ {ω | ¬ (regret (supp (rec ω)) (hne (rec ω)) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε ∧
        ∑ t ∈ range (τ ω), cost (x t ω) ≤
          16 * cmax * (1 + Lsq / lam) *
            ayRadius σ lam δ B (design lam φ (fun s => x s ω) (τ ω - 1)) ^ 2 / ε ^ 2 *
            Real.log ((design lam φ (fun s => x s ω) (τ ω)).det / lam ^ Fintype.card n))} ≤
      ENNReal.ofReal δ := by
  have hφm : ∀ s, Measurable[ℱ s] (fun ω => φ (x s ω)) := by
    intro s
    have hxm : @Measurable Ω X (ℱ s) ⊤ (x s) :=
      @measurable_to_countable' X Ω ⊤ _ (ℱ s) (x s) (fun x0 => hx s x0)
    exact (measurable_from_top (f := φ) : @Measurable X (n → ℝ) ⊤ _ φ).comp hxm
  refine (measure_mono ?_).trans (ay_radius_whp ℱ hσ hlam hδ0 hB (η := η)
    (φ := fun s ω => φ (x s ω)) θs hθ hφm hη hsub)
  intro ω hω
  by_contra hgood
  apply hω
  have e1 : ∀ t, ridgeDesign lam (fun s : Fin t => φ (x s ω)) =
      design lam φ (fun s => x s ω) t := fun t =>
    (ridgeDesign_fin_eq lam (fun s ω => φ (x s ω)) t ω).trans
      (design_eq_snDesign lam φ x ω t).symm
  have e2 : ∀ t, ∑ s : Fin t, (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω) =
      ∑ s ∈ range t, (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω) := fun t =>
    Fin.sum_univ_eq_sum_range (fun s => (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω)) t
  have hcov : ∀ t, Real.sqrt
      ((ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t - θs) ⬝ᵥ
        design lam φ (fun s => x s ω) t *ᵥ
          (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t - θs)) ≤
      ayRadius σ lam δ B (design lam φ (fun s => x s ω) t) := by
    intro t
    by_contra h
    apply hgood
    refine ⟨t, ?_⟩
    rw [e1, e2]
    exact not_le.mp h
  have hrad := fun t => ayRadius_design_pos (δ := δ) (B := B) hσ hlam hδ0 hδ1 hB φ
    (fun s => x s ω) t
  obtain ⟨hcostb, hcorr⟩ := cd_joint_run hlam φ cost hcost hφ hε ι supp hne (τ ω)
    (fun s => x s ω) (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
    (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))
    (fun t _ => hrad t) (fun s t hst _ => ayRadius_design_mono hσ hlam φ _ hst) (hrun ω)
  refine ⟨hcorr (rec ω) θs (hrad _).le (hstop ω) ?_, hcostb⟩
  have h := (Real.sqrt_le_iff.mp (hcov (τ ω))).2
  have hneg : θs - ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) (τ ω) =
      -(ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) (τ ω) - θs) := by
    rw [neg_sub]
  rw [hneg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  exact h

end CDProb

end JointRootCert
