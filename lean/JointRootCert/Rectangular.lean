/-
Exact rectangular shared-support certificate (Theorem `thm:shared-regret`) and the
anytime-valid root commitment (Corollary `cor:shared-regret-pac`), Appendix A.2,
together with `eq:exact-robust-regret` of the main text.

The confidence set is a box `∏_z [l z, u z]`.  Inside coordinates can be lowered to
their lower endpoints and outside coordinates raised to their upper endpoints
*simultaneously*, so the outside-support expression is attained.
-/
import JointRootCert.JointSet

namespace JointRootCert

open Finset

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {S : Finset Z} {hS : S.Nonempty} {l u f : Z → ℝ} {ε : ℝ}

/-- The outside-support certificate `[U⁻(a) - L(a)]_+` with
`U⁻(a) = max_{z ∉ S(a)} u z` and `L(a) = max_{y ∈ S(a)} l y`. -/
noncomputable def rectCert (S : Finset Z) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (l u : Z → ℝ) : ℝ :=
  max 0 (Sᶜ.sup' hSc u - S.sup' hS l)

/-- Every environment in the box has regret at most the outside-support certificate. -/
theorem regret_le_rectCert (hSc : Sᶜ.Nonempty) (hf : f ∈ Set.Icc l u) :
    regret S hS f ≤ rectCert S hS hSc l u := by
  rw [regret_le_iff]
  refine ⟨le_max_left _ _, fun z hz => ?_⟩
  have h1 : f z ≤ Sᶜ.sup' hSc u := (hf.2 z).trans (le_sup' u (mem_compl.mpr hz))
  have h2 : S.sup' hS l ≤ val S hS f :=
    sup'_le _ _ (fun y hy => (hf.1 y).trans (le_val hS f hy))
  exact le_max_of_le_right (by linarith)

/-- The adversarial environment: lower endpoints inside the support, upper endpoints
outside. -/
def worstEnv (S : Finset Z) (l u : Z → ℝ) : Z → ℝ := fun z => if z ∈ S then l z else u z

lemma worstEnv_mem (S : Finset Z) (hlu : l ≤ u) : worstEnv S l u ∈ Set.Icc l u := by
  constructor
  · intro z
    by_cases hz : z ∈ S <;> simp [worstEnv, hz, hlu z]
  · intro z
    by_cases hz : z ∈ S <;> simp [worstEnv, hz, hlu z]

/-- The adversarial environment attains the certificate. -/
theorem regret_worstEnv (hSc : Sᶜ.Nonempty) :
    regret S hS (worstEnv S l u) = rectCert S hS hSc l u := by
  have h1 : val S hS (worstEnv S l u) = S.sup' hS l :=
    sup'_congr hS rfl (fun y hy => by simp [worstEnv, hy])
  have h2 : Sᶜ.sup' hSc (worstEnv S l u) = Sᶜ.sup' hSc u :=
    sup'_congr hSc rfl (fun z hz => by simp [worstEnv, mem_compl.mp hz])
  rw [regret_eq hSc, h1, h2, rectCert]

/-- **Exact rectangular shared-support certificate (Theorem `thm:shared-regret`).**
For a nonempty box and a proper support, the worst-case regret over the box is exactly
`[max_{z ∉ S} u z - max_{y ∈ S} l y]_+`, and it is attained. -/
theorem rect_isGreatest (hlu : l ≤ u) (hSc : Sᶜ.Nonempty) :
    IsGreatest (regret S hS '' Set.Icc l u) (rectCert S hS hSc l u) :=
  ⟨⟨worstEnv S l u, worstEnv_mem S hlu, regret_worstEnv hSc⟩,
    by rintro _ ⟨f, hf, rfl⟩; exact regret_le_rectCert hSc hf⟩

/-- The same statement for the robust regret `R_C(a) = sup_{f ∈ C} r_f(a)`. -/
theorem robustRegret_box (hlu : l ≤ u) (hSc : Sᶜ.Nonempty) :
    robustRegret S hS (Set.Icc l u) = rectCert S hS hSc l u :=
  (rect_isGreatest hlu hSc).csSup_eq

/-- Full support: zero robust regret over every nonempty box, whatever the intervals. -/
theorem robustRegret_box_full (hlu : l ≤ u) (hSc : Sᶜ = ∅) :
    robustRegret S hS (Set.Icc l u) = 0 :=
  robustRegret_eq_zero_of_compl_empty _ ⟨l, le_rfl, hlu⟩ hSc

/-- The certificate holds exactly when every terminal whose upper bound exceeds
`L(a) + ε` is retained: `{z : u z > L(a) + ε} ⊆ S(a)`. -/
theorem rectCert_le_iff (hSc : Sᶜ.Nonempty) :
    rectCert S hS hSc l u ≤ ε ↔ 0 ≤ ε ∧ ∀ z, S.sup' hS l + ε < u z → z ∈ S := by
  unfold rectCert
  rw [max_le_iff, sub_le_iff_le_add, sup'_le_iff]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun z hz => ?_⟩
    by_contra hzS
    have := h z (mem_compl.mpr hzS)
    linarith
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun z hz => ?_⟩
    by_contra hlt
    exact (mem_compl.mp hz) (h z (by linarith))

/-- **Comparison with marginal action-value bounds (`eq:exact-robust-regret`).**
If every terminal outside `S(a)` is retained by some other action `b ≠ a`, the exact
certificate is at most the marginal gap `[max_{b ≠ a} max_{z ∈ S(b)} u z - L(a)]_+`.
Here `M` is any upper bound on the marginal upper values of the competing actions. -/
theorem rectCert_le_marginal {A : Type*} (supp : A → Finset Z) (a : A)
    (hsupp : supp a = S) (hcover : ∀ z, z ∉ S → ∃ b, b ≠ a ∧ z ∈ supp b)
    (hSc : Sᶜ.Nonempty) {M : ℝ} (hM : ∀ b, b ≠ a → ∀ z ∈ supp b, u z ≤ M) :
    rectCert S hS hSc l u ≤ max 0 (M - S.sup' hS l) := by
  have _ := hsupp
  unfold rectCert
  refine max_le_max le_rfl (sub_le_sub_right ?_ _)
  refine sup'_le _ _ (fun z hz => ?_)
  obtain ⟨b, hb, hzb⟩ := hcover z (mem_compl.mp hz)
  exact hM b hb z hzb

/-- Soundness of stopping: if the true means lie in the box and the certificate is at
most `ε`, the commitment is `ε`-optimal. -/
theorem regret_le_of_cert (hSc : Sᶜ.Nonempty) {μ : Z → ℝ} (hμ : μ ∈ Set.Icc l u)
    (hcert : rectCert S hS hSc l u ≤ ε) : regret S hS μ ≤ ε :=
  (regret_le_rectCert hSc hμ).trans hcert

section Anytime

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {A : Type*}

/-- **Anytime-valid root commitment (Corollary `cor:shared-regret-pac`).**

`C t ω` is the confidence set held at time `t` on the sample path `ω` (a box in the
rectangular case, an ellipsoid image in the correlated case).  `τ ω` is the time at which
the procedure stops and `rec ω` the action it returns; both may depend on the whole
sample path in an arbitrary way, which covers every adaptive sampling and stopping
policy.  The only requirements are

* simultaneous coverage: the event that the true means leave some `C t` has probability
  at most `δ`;
* the returned action is certified at the stopping time: every environment in
  `C (τ ω) ω` gives it regret at most `ε`.

Then the returned action fails to be `ε`-optimal with probability at most `δ`. -/
theorem anytime_valid_commitment (P : Measure Ω) (μ : Z → ℝ) (δ : ENNReal)
    (C : ℕ → Ω → Set (Z → ℝ)) (supp : A → Finset Z) (hsupp : ∀ a, (supp a).Nonempty)
    (τ : Ω → ℕ) (rec : Ω → A)
    (hcover : P {ω | ∃ t, μ ∉ C t ω} ≤ δ)
    (hcert : ∀ ω, ∀ f ∈ C (τ ω) ω, regret (supp (rec ω)) (hsupp (rec ω)) f ≤ ε) :
    P {ω | ε < regret (supp (rec ω)) (hsupp (rec ω)) μ} ≤ δ := by
  refine (measure_mono ?_).trans hcover
  intro ω hω
  refine ⟨τ ω, fun hmem => ?_⟩
  exact absurd (hcert ω μ hmem) (not_le.mpr hω)

/-- The rectangular instance: boxes `[l t ω, u t ω]` and the outside-support certificate. -/
theorem anytime_valid_commitment_box (P : Measure Ω) (μ : Z → ℝ) (δ : ENNReal)
    (l u : ℕ → Ω → Z → ℝ) (supp : A → Finset Z) (hsupp : ∀ a, (supp a).Nonempty)
    (hproper : ∀ a, (supp a)ᶜ.Nonempty) (τ : Ω → ℕ) (rec : Ω → A)
    (hcover : P {ω | ∃ t, μ ∉ Set.Icc (l t ω) (u t ω)} ≤ δ)
    (hcert : ∀ ω, rectCert (supp (rec ω)) (hsupp (rec ω)) (hproper (rec ω))
        (l (τ ω) ω) (u (τ ω) ω) ≤ ε) :
    P {ω | ε < regret (supp (rec ω)) (hsupp (rec ω)) μ} ≤ δ :=
  anytime_valid_commitment P μ δ (fun t ω => Set.Icc (l t ω) (u t ω)) supp hsupp τ rec hcover
    (fun ω _ hf => (regret_le_rectCert (hproper (rec ω)) hf).trans (hcert ω))

end Anytime

end JointRootCert
