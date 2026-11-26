/-
`thm:t4-finite-sample` (Finite-sample cost of safeguarded CD-Joint), reworded form, and
satisfiability of the hypotheses of `cd_joint_literal` with genuine noise.

* `t4_finite_sample`: the theorem with the reworded radius hypothesis "a positive,
  nondecreasing, anytime-valid self-normalized radius `β_t` with
  `liminf_{t→∞} β_t² log t / t = 0`".  The liminf is stated in `EReal`
  (`liminf_ereal_eq_zero_iff`: for a nonnegative sequence it is equivalent to
  `∀ C > 0, ∃ᶠ t, β_t² log t / t < C`).  A real-valued `Filter.liminf` is not used because
  it takes the junk value `0` on sequences tending to `+∞`.
  `t4_finite_sample_frequently` is the same theorem with the frequently-form hypothesis.
  `ayRadius_liminf`: the radius `eq:ay-radius` satisfies the liminf hypothesis on every path.
* Causal, adapted query sequences: `exists_causal_policy` (sequential choice of a policy that
  is causal in an exogenous path), `cdPolicy_exists` (a policy, causal in the noise path, whose
  queries form an infinite run of Algorithm `alg:cd-joint` with the ridge estimate and the
  radius `eq:ay-radius`), `policy_adapted_of_countable` (for noise with countable range,
  adapted to a filtration, the resulting queries are adapted).
* A non-degenerate instance: i.i.d. Rademacher noise on the coin-tossing space `ℕ → Bool`
  (`coinP`, `coinFilt`, `rad`), which is conditionally `1`-sub-Gaussian (`rad_condSubG`), has
  `rad s ω ^ 2 = 1` everywhere (`rad_sq`), and admits adapted runs (`rademacher_hyps`);
  `cd_joint_literal_rademacher` applies `cd_joint_literal` to it.
-/
import JointRootCert.LiteralABC3

namespace JointRootCert

namespace LiteralF1

open Finset MeasureTheory Matrix Filter ProbabilityTheory
open scoped ENNReal
open LiteralABC LiteralABC2 LiteralABC3

/-! ### The liminf condition -/

section Liminf

/-- For a nonnegative real sequence, `liminf u = 0` (in `EReal`) iff `u` is frequently below
every positive level. -/
theorem liminf_ereal_eq_zero_iff {u : ℕ → ℝ} (hu : ∀ t, 0 ≤ u t) :
    Filter.liminf (fun t => (u t : EReal)) atTop = 0 ↔
      ∀ C : ℝ, 0 < C → ∃ᶠ t in atTop, u t < C := by
  have hge : (0 : EReal) ≤ Filter.liminf (fun t => (u t : EReal)) atTop :=
    Filter.le_liminf_of_le (by isBoundedDefault)
      (Filter.Eventually.of_forall fun t => by exact_mod_cast hu t)
  constructor
  · intro h C hC
    have hlt : Filter.liminf (fun t => (u t : EReal)) atTop < (C : EReal) := by
      rw [h]; exact_mod_cast hC
    exact (Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt).mono
      fun t ht => by exact_mod_cast ht
  · intro h
    refine le_antisymm ?_ hge
    rw [Filter.liminf_le_iff]
    intro y hy
    obtain ⟨C, hC0, hCy⟩ := EReal.lt_iff_exists_real_btwn.mp hy
    exact (h C (by exact_mod_cast hC0)).mono fun t ht =>
      (by exact_mod_cast ht : (u t : EReal) < C).trans hCy

lemma radius_ratio_nonneg (β : ℕ → ℝ) (t : ℕ) : 0 ≤ β t ^ 2 * Real.log t / t :=
  div_nonneg (mul_nonneg (sq_nonneg _) (Real.log_natCast_nonneg t)) (Nat.cast_nonneg t)

/-- The frequently form of `liminf β_t² log t / t = 0` gives the hypothesis of
`cd_growth_of_frequently`. -/
theorem exists_of_frequently {β : ℕ → ℝ}
    (h : ∀ C : ℝ, 0 < C → ∃ᶠ t in atTop, β t ^ 2 * Real.log t / t < C) :
    ∀ C : ℝ, 0 < C → ∃ t : ℕ, C * β t ^ 2 * Real.log (t + 2) < t + 1 := by
  intro C hC
  obtain ⟨t, ht, ht2⟩ :=
    ((h (1 / (2 * C)) (by positivity)).and_eventually (eventually_ge_atTop 2)).exists
  refine ⟨t, ?_⟩
  have ht2' : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have htpos : (0 : ℝ) < t := by linarith
  have hlog : Real.log ((t : ℝ) + 2) ≤ 2 * Real.log t := by
    have h1 : Real.log ((t : ℝ) + 2) ≤ Real.log ((t : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1
    exact_mod_cast h1
  rw [div_lt_iff₀ htpos] at ht
  have h3 : 2 * C * (β t ^ 2 * Real.log t) < 2 * C * (1 / (2 * C) * t) :=
    mul_lt_mul_of_pos_left ht (by positivity)
  have h4 : 2 * C * (1 / (2 * C) * (t : ℝ)) = t := by field_simp
  have h5 : C * β t ^ 2 * Real.log ((t : ℝ) + 2) ≤ C * β t ^ 2 * (2 * Real.log t) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  nlinarith

end Liminf

/-! ### `thm:t4-finite-sample`, reworded -/

section T4

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Theorem `thm:t4-finite-sample`, frequently form of the liminf hypothesis.**  As
`t4_finite_sample`, with `liminf_t β_t² log t / t = 0` stated as
`∀ C > 0, ∃ᶠ t, β_t² log t / t < C` on every path. -/
theorem t4_finite_sample_frequently [Nonempty n] [IsProbabilityMeasure μ] {lam δ : ℝ}
    (hlam : 0 < lam) (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax)
    (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε) (ι : Z → X) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (θs : n → ℝ) (x : ℕ → Ω → X) (m : ℕ → Ω → n → ℝ)
    (β : ℕ → Ω → ℝ) (hβpos : ∀ t ω, 0 < β t ω) (hβmono : ∀ ω, Monotone fun t => β t ω)
    (hcov : μ {ω | ∃ t, β t ω ^ 2 <
      (θs - m t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ (θs - m t ω)} ≤ ENNReal.ofReal δ)
    (hfreq : ∀ ω, ∀ C : ℝ, 0 < C →
      ∃ᶠ t in atTop, β t ω ^ 2 * Real.log t / t < C)
    (hrun : ∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω) (fun t => m t ω)
      (fun t => β t ω)) :
    (∀ ω, CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)
        (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ∧
      ∑ t ∈ range (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω)
          (fun t => β t ω)), cost (x t ω) ≤
        16 * cmax * (1 + Lsq / lam) *
          β (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω) - 1)
            ω ^ 2 / ε ^ 2 *
          Real.log ((design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω)
              (fun t => β t ω))).det / lam ^ Fintype.card n)) ∧
    μ {ω | ¬ ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)))
          (fun z => φ (ι z))
          (m (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ω)
          (β (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ω)
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤ ENNReal.ofReal δ := by
  obtain ⟨x0⟩ : Nonempty X := ⟨ι (Classical.arbitrary Z)⟩
  have hcmax : 0 ≤ cmax := (hcost x0).1.le.trans (hcost x0).2
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ x0)).trans (hφ x0)
  obtain ⟨xm, -, hxm⟩ := (univ : Finset X).exists_min_image cost ⟨x0, mem_univ _⟩
  have hgrow : ∀ ω, ∃ T : ℕ, 16 * cmax * (1 + Lsq / lam) / ε ^ 2 * β (T - 1) ω ^ 2 *
      (Fintype.card n * Real.log (1 + T * Lsq / (Fintype.card n * lam))) < cost xm * T :=
    fun ω => cd_growth_of_frequently (n := n) (ε := ε) (β := fun t => β t ω) hlam hcmax
      (hcost xm).1 hLsq (exists_of_frequently (hfreq ω))
  exact cd_joint_generic hlam φ cost hcost (fun y => hxm y (mem_univ _)) hφ hε ι supp hne θs
    x m β hβpos hβmono hcov hgrow hrun

/-- **Finite-sample cost of safeguarded CD-Joint (Theorem `thm:t4-finite-sample`), with the
reworded radius hypothesis.**

Fixed-feature model: features `φ x` with `‖φ x‖² ≤ Lsq` (`Lsq = L_φ²`), costs
`0 < cost x ≤ c_max`, terminals in the dictionary (`ι`), true parameter `θ*`.  `m t ω` is the
estimate and `β t ω` the radius; on every path `β` is positive (`hβpos`) and nondecreasing
(`hβmono`); it is an anytime-valid self-normalized radius: with probability at least `1 - δ`,
`‖θ* - m_t‖_{V_t} ≤ β_t` for all `t` simultaneously (`hcov`); and on every path
`liminf_{t→∞} β_t² log t / t = 0` (`hliminf`, the liminf taken in `EReal`).  The queries form
an infinite run of Algorithm `alg:cd-joint` on every path (`hrun`).  Then

* on every path the stopping test passes at the stopping time `τ = cdStop` (the procedure
  returns) and the cumulative cost up to `τ` satisfies `eq:t4-bound`;
* with probability at least `1 - δ` (in particular on the coverage event), every action
  passing the test at `τ`, hence the returned one, is `ε`-optimal. -/
theorem t4_finite_sample [Nonempty n] [IsProbabilityMeasure μ] {lam δ : ℝ} (hlam : 0 < lam)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax)
    (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε) (ι : Z → X) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (θs : n → ℝ) (x : ℕ → Ω → X) (m : ℕ → Ω → n → ℝ)
    (β : ℕ → Ω → ℝ) (hβpos : ∀ t ω, 0 < β t ω) (hβmono : ∀ ω, Monotone fun t => β t ω)
    (hcov : μ {ω | ∃ t, β t ω ^ 2 <
      (θs - m t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ (θs - m t ω)} ≤ ENNReal.ofReal δ)
    (hliminf : ∀ ω, Filter.liminf
      (fun t : ℕ => ((β t ω ^ 2 * Real.log t / t : ℝ) : EReal)) atTop = 0)
    (hrun : ∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω) (fun t => m t ω)
      (fun t => β t ω)) :
    (∀ ω, CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)
        (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ∧
      ∑ t ∈ range (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω)
          (fun t => β t ω)), cost (x t ω) ≤
        16 * cmax * (1 + Lsq / lam) *
          β (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω) - 1)
            ω ^ 2 / ε ^ 2 *
          Real.log ((design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω)
              (fun t => β t ω))).det / lam ^ Fintype.card n)) ∧
    μ {ω | ¬ ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)))
          (fun z => φ (ι z))
          (m (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ω)
          (β (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ω)
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤ ENNReal.ofReal δ :=
  t4_finite_sample_frequently hlam φ cost hcost hφ hε ι supp hne θs x m β hβpos hβmono hcov
    (fun ω => (liminf_ereal_eq_zero_iff (u := fun t : ℕ => β t ω ^ 2 * Real.log t / t)
      (radius_ratio_nonneg (fun t => β t ω))).mp (hliminf ω)) hrun

omit [DecidableEq X] in
/-- **The radius `eq:ay-radius` satisfies the liminf hypothesis of `t4_finite_sample`** on
every query path: `β_t² log t / t → 0` since `β_t² = O(log t)`. -/
theorem ayRadius_liminf [Nonempty n] {σ lam δ B Lsq : ℝ} (hlam : 0 < lam) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (φ : X → n → ℝ) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (x : ℕ → X) :
    Filter.liminf (fun t : ℕ =>
      ((ayRadius σ lam δ B (design lam φ x t) ^ 2 * Real.log t / t : ℝ) : EReal)) atTop = 0 := by
  obtain ⟨x0⟩ : Nonempty X := ⟨x 0⟩
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ x0)).trans (hφ x0)
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set c : ℝ := Lsq / (Fintype.card n * lam) with hc
  have hc0 : 0 ≤ c := div_nonneg hLsq (by positivity)
  set a : ℝ := 2 * lam * B ^ 2 + 4 * σ ^ 2 * Real.log (1 / δ) +
    2 * σ ^ 2 * Fintype.card n * Real.log (1 + c) with ha
  set b : ℝ := 2 * σ ^ 2 * Fintype.card n with hb
  -- the squared radius grows at most logarithmically
  have hβ : ∀ t : ℕ, 1 ≤ t → ayRadius σ lam δ B (design lam φ x t) ^ 2 ≤ a + b * Real.log t := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    set L := Real.log ((design lam φ x t).det / lam ^ Fintype.card n) with hL
    have hL0 : 0 ≤ L := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ (pow_pos hlam _), one_mul, ← design_det_zero lam φ x]
      exact design_det_mono hlam φ x (Nat.zero_le _)
    have hLle : L ≤ Fintype.card n * (Real.log (1 + c) + Real.log t) := by
      refine (log_design_det_le hlam hLsq φ hφ x t).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hd.le
      rw [← Real.log_mul (by linarith) (by linarith)]
      refine Real.log_le_log (by positivity) ?_
      have e : (t : ℝ) * Lsq / (Fintype.card n * lam) = t * c := by rw [hc]; ring
      rw [e]
      nlinarith
    have hu : 0 ≤ 2 * Real.log (1 / δ) + L := by linarith
    have h2 : ayRadius σ lam δ B (design lam φ x t) =
        Real.sqrt lam * B + σ * Real.sqrt (2 * Real.log (1 / δ) + L) := rfl
    have h3 : ayRadius σ lam δ B (design lam φ x t) ^ 2 ≤
        2 * (Real.sqrt lam * B) ^ 2 + 2 * (σ * Real.sqrt (2 * Real.log (1 / δ) + L)) ^ 2 := by
      rw [h2]
      nlinarith [sq_nonneg (Real.sqrt lam * B - σ * Real.sqrt (2 * Real.log (1 / δ) + L))]
    have h4 : (Real.sqrt lam * B) ^ 2 = lam * B ^ 2 := by rw [mul_pow, Real.sq_sqrt hlam.le]
    have h5 : (σ * Real.sqrt (2 * Real.log (1 / δ) + L)) ^ 2 =
        σ ^ 2 * (2 * Real.log (1 / δ) + L) := by rw [mul_pow, Real.sq_sqrt hu]
    rw [h4, h5] at h3
    have h6 : σ ^ 2 * L ≤ σ ^ 2 * (Fintype.card n * (Real.log (1 + c) + Real.log t)) :=
      mul_le_mul_of_nonneg_left hLle (sq_nonneg σ)
    rw [ha, hb]
    nlinarith
  -- the comparison sequence tends to zero
  have hlim : ∀ k : ℕ, Tendsto (fun t : ℕ => Real.log t ^ k / t) atTop (nhds 0) := fun k => by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simp only [one_mul, add_zero] at h
    exact h
  have hw : Tendsto (fun t : ℕ => a * (Real.log t ^ 1 / t) + b * (Real.log t ^ 2 / t)) atTop
      (nhds 0) := by
    have := ((hlim 1).const_mul a).add ((hlim 2).const_mul b)
    simpa using this
  refine (liminf_ereal_eq_zero_iff
    (radius_ratio_nonneg (fun t => ayRadius σ lam δ B (design lam φ x t)))).mpr fun C hC => ?_
  refine Eventually.frequently ?_
  filter_upwards [hw.eventually (gt_mem_nhds hC), eventually_ge_atTop 1] with t hwt ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg ht1
  have hle : ayRadius σ lam δ B (design lam φ x t) ^ 2 * Real.log t / t ≤
      a * (Real.log t ^ 1 / t) + b * (Real.log t ^ 2 / t) := by
    have e : a * (Real.log t ^ 1 / t) + b * (Real.log t ^ 2 / t) =
        (a + b * Real.log t) * Real.log t / t := by ring
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hβ t ht) hlt) (by linarith)
  exact hle.trans_lt hwt

end T4

/-! ### Causal policies -/

section Policy

/-- **Sequential choice of a causal policy.**  `P v f t a`: "`a` is an admissible choice at
time `t`, given the exogenous path `v` and the choices `f`", depending on `v` and `f` only
through times `< t`.  If an admissible choice always exists, there is a policy `π` such that
`π v t` depends on `v` only through `v 0, …, v (t-1)` and `π v` is admissible at every time,
for every `v`. -/
theorem exists_causal_policy {V α : Type*} [Nonempty V] [Nonempty α]
    (P : (ℕ → V) → (ℕ → α) → ℕ → α → Prop)
    (hcaus : ∀ (v v' : ℕ → V) (f g : ℕ → α) t a, (∀ s < t, v s = v' s) →
      (∀ s < t, f s = g s) → P v f t a → P v' g t a)
    (hex : ∀ v f t, ∃ a, P v f t a) :
    ∃ π : (ℕ → V) → ℕ → α, (∀ v v' t, (∀ s < t, v s = v' s) → π v t = π v' t) ∧
      ∀ v t, P v (π v) t (π v t) := by
  classical
  choose c hc using hex
  obtain ⟨v0⟩ := ‹Nonempty V›
  let tr : ℕ → (ℕ → V) → ℕ → V := fun t v s => if s < t then v s else v0
  have htr : ∀ t v s, s < t → tr t v s = v s := fun t v s hs => ite_eq_left_iff.mpr (fun h => absurd hs h)
  have htr' : ∀ t v v', (∀ s < t, v s = v' s) → tr t v = tr t v' := fun t v v' h => by
    funext s
    by_cases hs : s < t
    · simp only [tr, hs, h s hs, ↓reduceIte]
    · simp only [tr, hs, ↓reduceIte]
  let Cz : ℕ → ((ℕ → V) → α) → Prop := fun t a => ∀ v v', (∀ s < t, v s = v' s) → a v = a v'
  obtain ⟨g, hg⟩ := exists_causal_seq (α := (ℕ → V) → α)
    (fun g t a => Cz t a ∧ ((∀ s < t, Cz s (g s)) → ∀ v, P v (fun s => g s v) t (a v)))
    (fun f g t a hfg hP => ⟨hP.1, fun hC v => by
      have hC' : ∀ s < t, Cz s (f s) := fun s hs => by rw [hfg s hs]; exact hC s hs
      exact hcaus v v (fun s => f s v) (fun s => g s v) t (a v) (fun _ _ => rfl)
        (fun s hs => by rw [hfg s hs]) (hP.2 hC' v)⟩)
    (fun g t => by
      by_cases hC : ∀ s < t, Cz s (g s)
      · refine ⟨fun v => c (tr t v) (fun s => g s (tr t v)) t,
          fun v v' h => by simp only [htr' t v v' h], fun _ v => ?_⟩
        refine hcaus (tr t v) v (fun s => g s (tr t v)) (fun s => g s v) t _
          (fun s hs => htr t v s hs) (fun s hs => ?_) (hc _ _ t)
        exact hC s hs _ _ (fun s' hs' => htr t v s' (by omega))
      · exact ⟨fun _ => Classical.arbitrary α, fun _ _ _ => rfl, fun h => absurd h hC⟩)
  refine ⟨fun v t => g t v, fun v v' t h => (hg t).1 v v' h, fun v t => ?_⟩
  exact (hg t).2 (fun s _ => (hg s).1) v

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

omit [Fintype X] [DecidableEq X] in
lemma ridgeEst_congr2 (lam : ℝ) (φ : X → n → ℝ) (θs : n → ℝ) {x x' : ℕ → X}
    {η η' : ℕ → ℝ} {t : ℕ} (hx : ∀ s < t, x s = x' s) (hη : ∀ s < t, η s = η' s) :
    ridgeEst lam φ θs x η t = ridgeEst lam φ θs x' η' t := by
  unfold ridgeEst
  rw [design_congr lam φ t hx]
  congr 1
  exact sum_congr rfl fun s hs => by rw [hx s (mem_range.mp hs), hη s (mem_range.mp hs)]

omit [DecidableEq X] in
/-- **A causal policy for safeguarded CD-Joint.**  With the ridge estimate and the radius
`eq:ay-radius`, there is a policy `π` mapping a noise path `v` to a query sequence `π v`, with
`π v t` depending on `v` only through `v 0, …, v (t-1)`, such that for every noise path the
queries form an infinite run of Algorithm `alg:cd-joint`.  (Supports cover the terminals,
`ε ≥ 0`.) -/
theorem cdPolicy_exists (lam σ δ B : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε : 0 ≤ ε) (θs : n → ℝ) :
    ∃ π : (ℕ → ℝ) → ℕ → X, (∀ v v' t, (∀ s < t, v s = v' s) → π v t = π v' t) ∧
      ∀ v, CDRun lam φ cost ι supp ε (π v) (ridgeEst lam φ θs (π v) v)
        (fun t => ayRadius σ lam δ B (design lam φ (π v) t)) := by
  have : Nonempty X := ⟨ι (Classical.arbitrary Z)⟩
  obtain ⟨π, hπ, hP⟩ := exists_causal_policy
    (fun v x t a => ¬ CDCertified lam φ ι supp ε x (ridgeEst lam φ θs x v)
        (fun t => ayRadius σ lam δ B (design lam φ x t)) t →
      CDStep (design lam φ x t) (ridgeEst lam φ θs x v t)
        (ayRadius σ lam δ B (design lam φ x t)) ε φ cost ι supp a)
    (fun v v' f g t a hv hfg hP => by
      have h1 := design_congr lam φ t hfg
      have h2 : ridgeEst lam φ θs f v t = ridgeEst lam φ θs g v' t :=
        ridgeEst_congr2 lam φ θs hfg hv
      simp only [CDCertified] at hP ⊢
      rw [h2, h1] at hP
      exact hP)
    (fun v f t => by
      by_cases hc : CDCertified lam φ ι supp ε f (ridgeEst lam φ θs f v)
          (fun t => ayRadius σ lam δ B (design lam φ f t)) t
      · exact ⟨Classical.arbitrary X, fun h => absurd hc h⟩
      · obtain ⟨a, ha⟩ := cdStep_exists (design lam φ f t) (ridgeEst lam φ θs f v t)
          (ayRadius σ lam δ B (design lam φ f t)) ε φ cost ι supp hne hcov hε
          (fun a h => hc ⟨a, h⟩)
        exact ⟨a, fun _ => ha⟩)
  exact ⟨π, hπ, fun v t => hP v t⟩

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

omit [Fintype X] [DecidableEq X] in
/-- **Adaptedness of a causal policy driven by countably-valued noise.**  If each noise
variable `η s` is `ℱ (s+1)`-measurable and takes countably many values, and `π` is causal,
then the queries `x t ω = π (η · ω) t` are `ℱ t`-measurable (hypothesis `hx` of
`cd_joint_literal`).  No measurability of `π` is needed. -/
theorem policy_adapted_of_countable (ℱ : Filtration ℕ m0) {η : ℕ → Ω → ℝ}
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hcnt : ∀ s, (Set.range (η s)).Countable)
    (π : (ℕ → ℝ) → ℕ → X) (hπ : ∀ v v' t, (∀ s < t, v s = v' s) → π v t = π v' t) :
    ∀ t x0, MeasurableSet[ℱ t] {ω | π (fun s => η s ω) t = x0} := by
  intro t x0
  let H : Ω → (Fin t → ℝ) := fun ω i => η i ω
  have hH : Measurable[ℱ t] H := by
    refine @measurable_pi_iff Ω (Fin t) (fun _ => ℝ) (ℱ t) _ H |>.mpr fun i => ?_
    exact (hη i).mono (ℱ.mono (by omega : (i : ℕ) + 1 ≤ t)) le_rfl
  let G : (Fin t → ℝ) → X := fun w => π (fun s => if h : s < t then w ⟨s, h⟩ else 0) t
  have hGH : ∀ ω, π (fun s => η s ω) t = G (H ω) := fun ω =>
    hπ _ _ t fun s hs => by simp only [H, hs, ↓reduceDIte]
  have hrange : (Set.range H).Countable :=
    (Set.countable_pi (π := fun _ : Fin t => ℝ) (s := fun i => Set.range (η i))
      fun i => hcnt i).mono (by rintro _ ⟨ω, rfl⟩ i; exact ⟨ω, rfl⟩)
  have hS : MeasurableSet (G ⁻¹' {x0} ∩ Set.range H) :=
    (hrange.mono Set.inter_subset_right).measurableSet
  have heq : {ω | π (fun s => η s ω) t = x0} = H ⁻¹' (G ⁻¹' {x0} ∩ Set.range H) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
      Set.mem_range, hGH]
    exact ⟨fun h => ⟨h, ω, rfl⟩, fun h => h.1⟩
  rw [heq]
  exact hH hS

end Policy

/-! ### Rademacher noise on the coin-tossing space -/

section Coin

/-- The uniform law on `Bool`. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := ⟨by
  rw [coin, smul_apply, add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

lemma lintegral_coin (f : Bool → ℝ≥0∞) : ∫⁻ b, f b ∂coin = 2⁻¹ * (f true + f false) := by
  rw [coin, lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac,
    smul_eq_mul]

/-- I.i.d. fair coins. -/
noncomputable def coinP : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => coin)

instance : IsProbabilityMeasure coinP := by unfold coinP; infer_instance

/-- `coinFilt k` is generated by the first `k` coins. -/
def coinFilt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)) where
  seq k := Filtration.piFinset (X := fun _ : ℕ => Bool) (Finset.range k)
  mono' _ _ hij :=
    (Filtration.piFinset (X := fun _ : ℕ => Bool)).mono (Finset.range_subset_range.2 hij)
  le' _ := (Filtration.piFinset (X := fun _ : ℕ => Bool)).le _

lemma coinFilt_eq (k : ℕ) : (coinFilt k : MeasurableSpace (ℕ → Bool)) =
    MeasurableSpace.comap (Finset.range k).restrict MeasurableSpace.pi := rfl

/-- Rademacher noise: `η_s = ±1` according to the `s`-th coin. -/
def rad (s : ℕ) (ω : ℕ → Bool) : ℝ := if ω s then 1 else -1

lemma rad_sq (s : ℕ) (ω : ℕ → Bool) : rad s ω ^ 2 = 1 := by
  unfold rad; split_ifs <;> norm_num

lemma measurable_coinFilt {β : Type*} [MeasurableSpace β] (k : ℕ)
    (f : ((Finset.range k) → Bool) → β) :
    Measurable[coinFilt k] (fun ω : ℕ → Bool => f ((Finset.range k).restrict ω)) := by
  rw [coinFilt_eq]
  exact (measurable_of_finite f).comp (comap_measurable _)

lemma rad_adapted (s : ℕ) : Measurable[coinFilt (s + 1)] (rad s) :=
  measurable_coinFilt (s + 1)
    (fun r => if r ⟨s, Finset.mem_range.2 (Nat.lt_succ_self s)⟩ then (1 : ℝ) else -1)

lemma measurable_rad (s : ℕ) : Measurable (rad s) :=
  (rad_adapted s).mono (coinFilt.le (s + 1)) le_rfl

lemma rad_range (s : ℕ) : (Set.range (rad s)).Countable := by
  have h : Set.range (rad s) ⊆ Set.range (fun b : Bool => if b then (1 : ℝ) else -1) := by
    rintro _ ⟨ω, rfl⟩
    exact ⟨ω s, rfl⟩
  exact ((Set.finite_range _).subset h).countable

lemma rad_mgf (s : ℕ) (c : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (c * rad s ω)) ∂coinP ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * 1 ^ 2 / 2)) := by
  have hmap : coinP.map (fun ω : ℕ → Bool => ω s) = coin :=
    Measure.infinitePi_map_eval (fun _ : ℕ => coin) s
  have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (c * rad s ω)) ∂coinP =
      ∫⁻ b, ENNReal.ofReal (Real.exp (c * (if b then 1 else -1))) ∂coin := by
    rw [← hmap, lintegral_map (measurable_of_finite _) (measurable_pi_apply s)]
    rfl
  rw [h1, lintegral_coin]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one, mul_neg]
  have e : 2⁻¹ * (ENNReal.ofReal (Real.exp c) + ENNReal.ofReal (Real.exp (-c))) =
      ENNReal.ofReal ((Real.exp c + Real.exp (-c)) / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_add (Real.exp_pos _).le
      (Real.exp_pos _).le, ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm]
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.cosh_eq, one_pow, mul_one]
  exact Real.cosh_le_exp_half_sq c

/-- Rademacher noise is conditionally `1`-sub-Gaussian given the past coins. -/
theorem rad_condSubG (s : ℕ) : CondSubG coinP (coinFilt s) (rad s) 1 := by
  have hiind : iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) => ω i) coinP :=
    iIndepFun_infinitePi (P := fun _ : ℕ => coin) (X := fun _ b => b) (fun _ => measurable_id)
  have hdisj : Disjoint ({s} : Finset ℕ) (Finset.range s) := by
    rw [Finset.disjoint_singleton_left]
    simp
  have hind := hiind.indepFun_finset {s} (Finset.range s) hdisj (fun i => measurable_pi_apply i)
  have hle : MeasurableSpace.comap (rad s) (inferInstance : MeasurableSpace ℝ) ≤
      MeasurableSpace.comap (fun (a : ℕ → Bool) (i : ({s} : Finset ℕ)) => a i)
        MeasurableSpace.pi := by
    have h1 : rad s =
        (fun r : (({s} : Finset ℕ)) → Bool =>
          if r ⟨s, Finset.mem_singleton_self s⟩ then (1 : ℝ) else -1) ∘
          (fun (a : ℕ → Bool) (i : ({s} : Finset ℕ)) => a i) := rfl
    rw [h1, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_of_finite _).comap_le
  have hind' : Indep (MeasurableSpace.comap (rad s) (inferInstance : MeasurableSpace ℝ))
      (coinFilt s) coinP :=
    indep_of_indep_of_le_left hind hle
  exact CondSubG.of_indep (coinFilt.le s) (measurable_rad s) hind' (rad_mgf s)

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

omit [DecidableEq X] in
/-- **The hypotheses of `cd_joint_literal` hold jointly with non-degenerate noise.**  On the
coin-tossing space with i.i.d. Rademacher noise `rad` (`rad s ω ^ 2 = 1` for all `s, ω`):
the noise is adapted (`hη`) and conditionally `1`-sub-Gaussian (`hsub`), and there is a query
sequence, a fixed causal function of the past noise, that is adapted (`hx`) and is an
infinite run of Algorithm `alg:cd-joint` with the ridge estimate and the radius
`eq:ay-radius` on every path (`hrun`).  (Supports cover the terminals, `ε ≥ 0`.) -/
theorem rademacher_hyps (lam δ B : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε : 0 ≤ ε) (θs : n → ℝ) :
    (∀ s ω, rad s ω ^ 2 = 1) ∧
    (∀ s, Measurable[coinFilt (s + 1)] (rad s)) ∧
    (∀ s, CondSubG coinP (coinFilt s) (rad s) 1) ∧
    ∃ x : ℕ → (ℕ → Bool) → X,
      (∀ s x0, MeasurableSet[coinFilt s] {ω | x s ω = x0}) ∧
      ∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω)
        (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
        (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t)) := by
  refine ⟨rad_sq, rad_adapted, rad_condSubG, ?_⟩
  obtain ⟨π, hπ, hrun⟩ := cdPolicy_exists lam 1 δ B φ cost ι supp hne hcov hε θs
  exact ⟨fun t ω => π (fun s => rad s ω) t,
    policy_adapted_of_countable coinFilt rad_adapted rad_range π hπ,
    fun ω => hrun (fun s => rad s ω)⟩

/-- **`cd_joint_literal` applied to Rademacher noise.**  For every instance of the
fixed-feature model whose supports cover the terminals, with i.i.d. Rademacher noise
(`σ = 1`), there is an adapted query sequence running Algorithm `alg:cd-joint` on every path,
and for it the conclusion of `cd_joint_literal` holds. -/
theorem cd_joint_literal_rademacher [Nonempty n] {lam δ B : ℝ} (hlam : 0 < lam)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) :
    ∃ x : ℕ → (ℕ → Bool) → X,
      (∀ s x0, MeasurableSet[coinFilt s] {ω | x s ω = x0}) ∧
      (∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω)
        (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
        (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t))) ∧
    coinP {ω | ¬ (CDCertified lam φ ι supp ε (fun s => x s ω)
          (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
          (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t))
          (cdStop lam φ ι supp ε (fun s => x s ω)
            (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
            (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t))) ∧
        ∑ t ∈ range (cdStop lam φ ι supp ε (fun s => x s ω)
            (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
            (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t))), cost (x t ω) ≤
          16 * cmax * (1 + Lsq / lam) *
            ayRadius 1 lam δ B (design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
                (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t)) - 1)) ^ 2 /
              ε ^ 2 *
            Real.log ((design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
                (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t)))).det /
              lam ^ Fintype.card n) ∧
        ∀ r : A,
          cdDualCert (design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
                (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t))))
            (fun z => φ (ι z))
            (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
                (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t))))
            (ayRadius 1 lam δ B (design lam φ (fun s => x s ω)
              (cdStop lam φ ι supp ε (fun s => x s ω)
                (ridgeEst lam φ θs (fun s => x s ω) (fun s => rad s ω))
                (fun t => ayRadius 1 lam δ B (design lam φ (fun s => x s ω) t)))))
            ε (supp r) →
          regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε)} ≤
      ENNReal.ofReal δ := by
  obtain ⟨-, hη, hsub, x, hx, hrun⟩ :=
    rademacher_hyps lam δ B φ cost ι supp hne hcov hε.le θs
  exact ⟨x, hx, hrun, cd_joint_literal coinFilt one_pos hlam hδ0 hδ1 hB φ cost hcost hφ hε ι
    supp hne θs hθ x hx hη hsub hrun⟩

end Coin

end LiteralF1

end JointRootCert
