/-
Linear algebra for the finite-sample cost of CD-Joint (proof of
Theorem `thm:t4-finite-sample`, Appendix B.1).

The design matrix `V_t = λ I + ∑_s φ_{x_s} φ_{x_s}ᵀ` is symmetric and `λ`-coercive.  This
file collects what the potential argument needs about such matrices: invertibility, the
`V⁻¹`-quadratic form `‖g‖²_{V⁻¹} = gᵀ V⁻¹ g`, its Cauchy--Schwarz and triangle
inequalities, the bound `‖φ‖²_{V⁻¹} ≤ ‖φ‖² / λ`, and the matrix determinant lemma for a
rank-one update.
-/
import JointRootCert.ActiveWidth

namespace JointRootCert

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A symmetric matrix whose quadratic form dominates `lam ‖x‖²`. -/
structure Coercive (V : Matrix n n ℝ) (lam : ℝ) : Prop where
  symm : Vᵀ = V
  coer : ∀ x : n → ℝ, lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ V *ᵥ x

/-- The quadratic form of the inverse, `‖v‖²_{V⁻¹} = vᵀ V⁻¹ v`. -/
noncomputable def qinv (V : Matrix n n ℝ) (v : n → ℝ) : ℝ := v ⬝ᵥ V⁻¹ *ᵥ v

lemma dotProduct_self_nonneg' (x : n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma eq_zero_of_dotProduct_self_nonpos {x : n → ℝ} (h : x ⬝ᵥ x ≤ 0) : x = 0 := by
  have h0 : ∑ i, x i * x i = 0 := le_antisymm h (dotProduct_self_nonneg' x)
  funext i
  have := (sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (x i))).mp h0 i (mem_univ i)
  exact mul_self_eq_zero.mp this

/-- Symmetric matrices give symmetric bilinear forms. -/
lemma dotProduct_mulVec_symm {M : Matrix n n ℝ} (hM : Mᵀ = M) (x y : n → ℝ) :
    y ⬝ᵥ M *ᵥ x = x ⬝ᵥ M *ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

/-- **Cauchy--Schwarz** for a symmetric matrix with nonnegative quadratic form. -/
lemma cauchy_schwarz_matrix {M : Matrix n n ℝ} (hM : Mᵀ = M)
    (hpos : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ M *ᵥ x) (x y : n → ℝ) :
    (x ⬝ᵥ M *ᵥ y) ^ 2 ≤ (x ⬝ᵥ M *ᵥ x) * (y ⬝ᵥ M *ᵥ y) := by
  have h : ∀ s : ℝ, 0 ≤ (y ⬝ᵥ M *ᵥ y) * (s * s) + (2 * (x ⬝ᵥ M *ᵥ y)) * s + x ⬝ᵥ M *ᵥ x := by
    intro s
    have hexp : (x + s • y) ⬝ᵥ M *ᵥ (x + s • y) =
        (y ⬝ᵥ M *ᵥ y) * (s * s) + (2 * (x ⬝ᵥ M *ᵥ y)) * s + x ⬝ᵥ M *ᵥ x := by
      simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [dotProduct_mulVec_symm hM x y]
      ring
    rw [← hexp]
    exact hpos _
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith

section Coercive

variable {V : Matrix n n ℝ} {lam : ℝ}

lemma Coercive.isUnit_det (hV : Coercive V lam) (hlam : 0 < lam) : IsUnit V.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : V *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  have h1 := hV.coer (x - y)
  rw [h0, dotProduct_zero] at h1
  have h2 : (x - y) ⬝ᵥ (x - y) ≤ 0 := by
    by_contra hpos
    have := mul_pos hlam (not_le.mp hpos)
    linarith
  exact sub_eq_zero.mp (eq_zero_of_dotProduct_self_nonpos h2)

lemma Coercive.mul_inv_mulVec (hV : Coercive V lam) (hlam : 0 < lam) (x : n → ℝ) :
    V *ᵥ (V⁻¹ *ᵥ x) = x := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (hV.isUnit_det hlam), one_mulVec]

lemma Coercive.inv_symm (hV : Coercive V lam) : V⁻¹ᵀ = V⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hV.symm]

/-- `‖x‖²_{V⁻¹} = yᵀ V y` for `y = V⁻¹ x`. -/
lemma Coercive.qinv_eq (hV : Coercive V lam) (hlam : 0 < lam) (x : n → ℝ) :
    qinv V x = (V⁻¹ *ᵥ x) ⬝ᵥ V *ᵥ (V⁻¹ *ᵥ x) := by
  rw [hV.mul_inv_mulVec hlam, qinv, dotProduct_comm]

lemma Coercive.qinv_nonneg (hV : Coercive V lam) (hlam : 0 < lam) (x : n → ℝ) :
    0 ≤ qinv V x := by
  rw [hV.qinv_eq hlam]
  exact (mul_nonneg hlam.le (dotProduct_self_nonneg' _)).trans (hV.coer _)

/-- `‖x‖²_{V⁻¹} ≤ ‖x‖² / λ`. -/
lemma Coercive.qinv_le (hV : Coercive V lam) (hlam : 0 < lam) (x : n → ℝ) :
    qinv V x ≤ (x ⬝ᵥ x) / lam := by
  set y := V⁻¹ *ᵥ x with hy
  have hq : qinv V x = x ⬝ᵥ y := rfl
  have h1 : lam * (y ⬝ᵥ y) ≤ x ⬝ᵥ y := by
    have := hV.coer y
    rwa [hV.mul_inv_mulVec hlam, dotProduct_comm y x] at this
  have hcs : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
    have := cauchy_schwarz_matrix (M := (1 : Matrix n n ℝ)) (by simp)
      (fun z => by simpa using dotProduct_self_nonneg' z) x y
    simpa using this
  have hx := dotProduct_self_nonneg' x
  have hyy := dotProduct_self_nonneg' y
  rw [hq, le_div_iff₀ hlam]
  rcases le_or_gt (x ⬝ᵥ y) 0 with hneg | hpos
  · nlinarith
  · -- (x·y)² ≤ (x·x)(y·y) ≤ (x·x)(x·y)/λ
    have h2 : (x ⬝ᵥ y) * (x ⬝ᵥ y * lam) ≤ (x ⬝ᵥ y) * (x ⬝ᵥ x) := by
      have h3 : (x ⬝ᵥ x) * (lam * (y ⬝ᵥ y)) ≤ (x ⬝ᵥ x) * (x ⬝ᵥ y) :=
        mul_le_mul_of_nonneg_left h1 hx
      nlinarith
    exact le_of_mul_le_mul_left h2 hpos

/-- Cauchy--Schwarz in the `V⁻¹` geometry. -/
lemma Coercive.cauchy_schwarz_inv (hV : Coercive V lam) (hlam : 0 < lam) (x y : n → ℝ) :
    (x ⬝ᵥ V⁻¹ *ᵥ y) ^ 2 ≤ qinv V x * qinv V y :=
  cauchy_schwarz_matrix hV.inv_symm (hV.qinv_nonneg hlam) x y

/-- Triangle inequality for `‖·‖_{V⁻¹}`, in the form used by the safeguard. -/
lemma Coercive.sqrt_qinv_sub_le (hV : Coercive V lam) (hlam : 0 < lam) (x y : n → ℝ) :
    Real.sqrt (qinv V (x - y)) ≤ Real.sqrt (qinv V x) + Real.sqrt (qinv V y) := by
  have hx := hV.qinv_nonneg hlam x
  have hy := hV.qinv_nonneg hlam y
  have hcs := hV.cauchy_schwarz_inv hlam x y
  have habs : |x ⬝ᵥ V⁻¹ *ᵥ y| ≤ Real.sqrt (qinv V x) * Real.sqrt (qinv V y) := by
    rw [← Real.sqrt_mul hx]
    exact Real.abs_le_sqrt hcs
  have hexp : qinv V (x - y) = qinv V x - 2 * (x ⬝ᵥ V⁻¹ *ᵥ y) + qinv V y := by
    simp only [qinv, mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [dotProduct_mulVec_symm hV.inv_symm x y]
    ring
  have hle : qinv V (x - y) ≤ (Real.sqrt (qinv V x) + Real.sqrt (qinv V y)) ^ 2 := by
    have h1 := neg_abs_le (x ⬝ᵥ V⁻¹ *ᵥ y)
    have h2 := Real.sq_sqrt hx
    have h3 := Real.sq_sqrt hy
    rw [hexp]
    nlinarith
  calc Real.sqrt (qinv V (x - y))
      ≤ Real.sqrt ((Real.sqrt (qinv V x) + Real.sqrt (qinv V y)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (qinv V x) + Real.sqrt (qinv V y) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

lemma vecMulVec_self_mulVec (φ x : n → ℝ) : vecMulVec φ φ *ᵥ x = (φ ⬝ᵥ x) • φ := by
  ext i
  simp [vecMulVec_apply, mulVec, dotProduct, mul_sum, mul_comm, mul_left_comm]

/-- A rank-one update keeps the design matrix symmetric and coercive. -/
lemma Coercive.rank_one (hV : Coercive V lam) (φ : n → ℝ) :
    Coercive (V + vecMulVec φ φ) lam := by
  refine ⟨?_, fun x => ?_⟩
  · rw [transpose_add, hV.symm]
    congr 1
    ext i j
    simp [vecMulVec_apply, mul_comm]
  · rw [add_mulVec, dotProduct_add, vecMulVec_self_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_comm x φ]
    have := hV.coer x
    nlinarith [mul_self_nonneg (φ ⬝ᵥ x)]

lemma coercive_smul_one {lam : ℝ} : Coercive (lam • (1 : Matrix n n ℝ)) lam := by
  refine ⟨by simp, fun x => ?_⟩
  rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Matrix determinant lemma** for the design update:
`det (V + φ φᵀ) = det V · (1 + ‖φ‖²_{V⁻¹})`. -/
lemma Coercive.det_rank_one (hV : Coercive V lam) (hlam : 0 < lam) (φ : n → ℝ) :
    (V + vecMulVec φ φ).det = V.det * (1 + qinv V φ) := by
  have hfac : V + vecMulVec φ φ = V * (1 + vecMulVec (V⁻¹ *ᵥ φ) φ) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    congr 1
    ext i j
    have := congrFun (hV.mul_inv_mulVec hlam φ) i
    simp only [vecMulVec_apply, Matrix.mul_apply]
    rw [← this]
    simp only [mulVec, dotProduct, sum_mul, mul_assoc]
  rw [hfac, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, qinv]

end Coercive

end JointRootCert
