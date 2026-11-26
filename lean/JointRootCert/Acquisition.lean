/-
Contrast-directed acquisition (Section 2.3, `eq:main-contrast-acquisition`, and
Appendix B.1).

Observing `Y = ⟨φ, θ⟩ + noise` with noise variance `σ²` under a Gaussian posterior with
covariance `Σ` subtracts the rank-one operator `Σ φ φᵀ Σ / (σ² + φᵀ Σ φ)`.  The variance of
a fixed contrast `g` therefore drops by exactly `(gᵀ Σ φ)² / (σ² + φᵀ Σ φ)`.
-/
import JointRootCert.Sparse

namespace JointRootCert

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Posterior covariance after one observation of the feature `φ` with noise variance
`σ²` (Gaussian conditioning, in Sherman--Morrison form). -/
noncomputable def condCov (Sig : E →ₗ[ℝ] E) (φ : E) (σ2 : ℝ) : E →ₗ[ℝ] E :=
  Sig - (1 / (σ2 + ⟪φ, Sig φ⟫)) • (LinearMap.toSpanSingleton ℝ E (Sig φ)).comp
    (innerₛₗ ℝ (Sig φ))

lemma condCov_apply (Sig : E →ₗ[ℝ] E) (φ : E) (σ2 : ℝ) (x : E) :
    condCov Sig φ σ2 x = Sig x - (⟪Sig φ, x⟫ / (σ2 + ⟪φ, Sig φ⟫)) • Sig φ := by
  simp [condCov, LinearMap.toSpanSingleton_apply, smul_smul, div_eq_mul_inv, mul_comm]

/-- **Variance reduction of a fixed contrast (`eq:main-contrast-acquisition`).**
One observation of `φ` reduces the variance of the contrast
`g` by exactly `(gᵀ Σ φ)² / (σ² + φᵀ Σ φ)`; dividing by the query cost gives the
acquisition score. -/
theorem contrast_variance_reduction (Sig : E →ₗ[ℝ] E) (φ g : E) (σ2 : ℝ) :
    ⟪g, Sig g⟫ - ⟪g, condCov Sig φ σ2 g⟫ = ⟪g, Sig φ⟫ ^ 2 / (σ2 + ⟪φ, Sig φ⟫) := by
  rw [condCov_apply, inner_sub_right, real_inner_smul_right, real_inner_comm g (Sig φ)]
  ring

/-- **The rank-one downdate is Gaussian conditioning.**  If `P` is the prior precision
(`P ∘ Σ = id`), the updated covariance inverts the updated precision
`P + σ⁻² φ φᵀ`. -/
theorem condCov_precision (Sig P : E →ₗ[ℝ] E) (hsym : ∀ x y, ⟪Sig x, y⟫ = ⟪x, Sig y⟫)
    (hP : ∀ x, P (Sig x) = x) (φ : E) {σ2 : ℝ} (hσ : σ2 ≠ 0)
    (hs : σ2 + ⟪φ, Sig φ⟫ ≠ 0) (x : E) :
    P (condCov Sig φ σ2 x) + (⟪φ, condCov Sig φ σ2 x⟫ / σ2) • φ = x := by
  rw [condCov_apply, map_sub, map_smul, hP, hP, inner_sub_right, real_inner_smul_right,
    hsym φ x]
  have key : (⟪φ, Sig x⟫ - ⟪φ, Sig x⟫ / (σ2 + ⟪φ, Sig φ⟫) * ⟪φ, Sig φ⟫) / σ2 =
      ⟪φ, Sig x⟫ / (σ2 + ⟪φ, Sig φ⟫) := by
    field_simp
    ring
  rw [key, sub_add_cancel]

end JointRootCert
