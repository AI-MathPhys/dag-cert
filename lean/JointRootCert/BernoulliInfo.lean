/-
Information-theoretic limits of root certification: the Bernoulli part.

Manuscript: Appendix "Information-Theoretic Limits of Root Certification"
(`app:group-info`), subsections `app:bernoulli-alternatives` and `app:ast-optimal`.

Results covered (see the doc comment of each theorem for the exact scope):

* `thm:active-kl-projection` "Scalar information projection for a fixed root answer".
* `thm:ast-main` "One inside witness and Bernoulli information limit": the one-witness
  reduction `eq:ast-star`, the deterministic properties of the allocation game, and two
  deterministic steps of the anytime pair certificate.  The asymptotic lower bound
  `eq:ast-lower-main`, the modulus `eq:ast-modulus`, the oracle `eq:ast-oracle`, the error
  control of the certificate and the tracker's asymptotic optimality are NOT formalized.
* `lem:active-com` "Stopped Bernoulli change of measure": the data-processing step, with the
  expected log-likelihood-ratio identity as a hypothesis.
* `thm:active-star-lb` "Non-containment tied-star lower bound": modular in the change of measure.
* `prop:ast-gap-tradeoff` "A support-margin versus information tradeoff".
* `prop:ast-discovery` "A discovery cost absent from the characteristic time": modular in the
  coupling.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset Real Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

/-! ### Binary relative entropy -/

/-- Bernoulli relative entropy `kl(p,q) = p log(p/q) + (1-p) log((1-p)/(1-q))`.
With Lean's conventions `0 * log 0 = 0`; the value is meaningful for `p ∈ [0,1]`, `q ∈ (0,1)`. -/
noncomputable def bkl (p q : ℝ) : ℝ := p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

/-- Downward-clipped divergence `d_↓(p,c) = kl(p,c)` if `p > c` and `0` otherwise. -/
noncomputable def dDown (p c : ℝ) : ℝ := if c < p then bkl p c else 0

lemma bkl_self (p : ℝ) : bkl p p = 0 := by
  unfold bkl
  have h1 : p * log (p / p) = 0 := by
    rcases eq_or_ne p 0 with h | h
    · simp [h]
    · simp [div_self h]
  have h2 : (1 - p) * log ((1 - p) / (1 - p)) = 0 := by
    rcases eq_or_ne (1 - p) 0 with h | h
    · simp [h]
    · simp [div_self h]
  rw [h1, h2, add_zero]

lemma mul_log_div_eq (p q : ℝ) (hq : q ≠ 0) : p * log (p / q) = p * log p - p * log q := by
  rcases eq_or_ne p 0 with h | h
  · simp [h]
  · rw [log_div h hq]; ring

/-- Expanded form of `kl(p,q)` for interior `q`. -/
lemma bkl_eq (p : ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    bkl p q = p * log p + (1 - p) * log (1 - p) - p * log q - (1 - p) * log (1 - q) := by
  unfold bkl
  rw [mul_log_div_eq p q hq0.ne', mul_log_div_eq (1 - p) (1 - q) (by linarith)]; ring

lemma sub_le_mul_log_div {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : p - q ≤ p * log (p / q) := by
  rcases hp.eq_or_lt with h | h
  · rw [← h]; simp [hq.le]
  · have h1 : log (q / p) ≤ q / p - 1 := log_le_sub_one_of_pos (div_pos hq h)
    have h2 : log (p / q) = - log (q / p) := by rw [← log_inv, inv_div]
    rw [h2]
    have h3 : p * (q / p - 1) = q - p := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

lemma mul_log_div_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * log (p / q) ≤ p * (p / q - 1) := by
  rcases hp.eq_or_lt with h | h
  · rw [← h]; simp
  · exact mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos h hq)) hp

/-- Gibbs' inequality for Bernoulli laws. -/
lemma bkl_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ bkl p q := by
  have h1 := sub_le_mul_log_div hp0 hq0
  have h2 := sub_le_mul_log_div (sub_nonneg.2 hp1) (sub_pos.2 hq1)
  unfold bkl; linarith

/-- Chi-square upper bound `kl(p,q) ≤ (p-q)² / (q(1-q))`. -/
lemma bkl_le_chi {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    bkl p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  have h1 := mul_log_div_le hp0 hq0
  have h2 := mul_log_div_le (sub_nonneg.2 hp1) (sub_pos.2 hq1)
  have h3 : p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) = (p - q) ^ 2 / (q * (1 - q)) := by
    have hq : q ≠ 0 := hq0.ne'
    have hq' : (1 - q) ≠ 0 := (sub_pos.2 hq1).ne'
    field_simp; ring
  unfold bkl; linarith

/-- The bound `kl(u,v) ≤ (16/3)(u-v)²` for `v ∈ [1/4,3/4]` used after `eq:active-star-bound`. -/
lemma bkl_le_sq {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 1 / 4 ≤ v) (hv1 : v ≤ 3 / 4) :
    bkl u v ≤ 16 / 3 * (u - v) ^ 2 := by
  have h := bkl_le_chi hu0 hu1 (by linarith : 0 < v) (by linarith : v < 1)
  have hv : 3 / 16 ≤ v * (1 - v) := by nlinarith
  have h2 : (u - v) ^ 2 / (v * (1 - v)) ≤ (u - v) ^ 2 / (3 / 16) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hv
  have h3 : (u - v) ^ 2 / (3 / 16) = 16 / 3 * (u - v) ^ 2 := by ring
  linarith

/-- `kl(·,d)` is nondecreasing to the right of `d`: if `d ≤ m ≤ p` then `kl(m,d) ≤ kl(p,d)`. -/
lemma bkl_mono_left {d m p : ℝ} (hd : 0 < d) (hdm : d ≤ m) (hm1 : m < 1) (hmp : m ≤ p)
    (hp1 : p ≤ 1) : bkl m d ≤ bkl p d := by
  have hd1 : d < 1 := lt_of_le_of_lt hdm hm1
  have hm0 : 0 < m := lt_of_lt_of_le hd hdm
  have h0 := bkl_nonneg (hm0.le.trans hmp) hp1 hm0 hm1
  have hA : 0 ≤ log m - log d := sub_nonneg.2 (log_le_log hd hdm)
  have hB : 0 ≤ log (1 - d) - log (1 - m) :=
    sub_nonneg.2 (log_le_log (sub_pos.2 hm1) (by linarith))
  have key : bkl p d - bkl m d
      = bkl p m + (p - m) * ((log m - log d) + (log (1 - d) - log (1 - m))) := by
    rw [bkl_eq p hd hd1, bkl_eq m hd hd1, bkl_eq p hm0 hm1]; ring
  have := mul_nonneg (sub_nonneg.2 hmp) (add_nonneg hA hB)
  linarith

/-- `kl(p,·)` moves away from its zero monotonically: if `d` lies between `p` and `x`
then `kl(p,d) ≤ kl(p,x)`. -/
lemma bkl_mono_right {p d x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hd0 : 0 < d) (hd1 : d < 1)
    (hx0 : 0 < x) (hx1 : x < 1) (h : 0 ≤ (d - x) * (p - d)) : bkl p d ≤ bkl p x := by
  have h1 : 1 - x / d ≤ log d - log x := by
    have := one_sub_inv_le_log_of_pos (div_pos hd0 hx0)
    rwa [inv_div, log_div hd0.ne' hx0.ne'] at this
  have hd' : 0 < 1 - d := sub_pos.2 hd1
  have hx' : 0 < 1 - x := sub_pos.2 hx1
  have h2 : 1 - (1 - x) / (1 - d) ≤ log (1 - d) - log (1 - x) := by
    have := one_sub_inv_le_log_of_pos (div_pos hd' hx')
    rwa [inv_div, log_div hd'.ne' hx'.ne'] at this
  have e : p * (1 - x / d) + (1 - p) * (1 - (1 - x) / (1 - d))
      = (d - x) * (p - d) / (d * (1 - d)) := by
    have := hd0.ne'
    have := hd'.ne'
    field_simp; ring
  have h3 : 0 ≤ (d - x) * (p - d) / (d * (1 - d)) := div_nonneg h (mul_pos hd0 hd').le
  have h4 := mul_le_mul_of_nonneg_left h1 hp0
  have h5 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hp1)
  rw [bkl_eq p hd0 hd1, bkl_eq p hx0 hx1]
  linarith

/-- Pinsker's inequality for interior Bernoulli parameters: `kl(p,q) ≥ 2(p-q)²`. -/
lemma pinsker {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ bkl p q := by
  set h : ℝ → ℝ := fun x => -(p * log x) - (1 - p) * log (1 - x) - 2 * (p - x) ^ 2 with hh
  have hderiv : ∀ x, 0 < x → x < 1 →
      HasDerivAt h ((x - p) * (1 - 2 * x) ^ 2 / (x * (1 - x))) x := by
    intro x hx0 hx1
    have hx' : (1 - x) ≠ 0 := (sub_pos.2 hx1).ne'
    have h1 := (hasDerivAt_log hx0.ne').const_mul p
    have h2 := (((hasDerivAt_id x).const_sub 1).log (by simpa using hx')).const_mul (1 - p)
    have h3 := (((hasDerivAt_id x).const_sub p).pow 2).const_mul 2
    have h4 := (h1.neg.sub h2).sub h3
    have h5 : HasDerivAt h
        (-(p * x⁻¹) - (1 - p) * (-1 / (1 - x)) - 2 * (2 * (p - x) ^ (2 - 1) * -1)) x := h4
    convert h5 using 1
    have := hx0.ne'
    field_simp
    ring
  have hcont : ContinuousOn h (Set.Ioo 0 1) := fun x hx =>
    (hderiv x hx.1 hx.2).continuousAt.continuousWithinAt
  have key : h p ≤ h q := by
    rcases le_total p q with hpq | hqp
    · have hsub : Set.Icc p q ⊆ Set.Ioo 0 1 := fun x hx =>
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hm : MonotoneOn h (Set.Icc p q) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc p q) (hcont.mono hsub)
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hx0 : 0 < x := by linarith [hx.1]
          have hx1 : x < 1 := by linarith [hx.2]
          rw [(hderiv x hx0 hx1).deriv]
          exact div_nonneg (mul_nonneg (by linarith [hx.1]) (sq_nonneg _))
            (mul_pos hx0 (sub_pos.2 hx1)).le
      exact hm (Set.left_mem_Icc.2 hpq) (Set.right_mem_Icc.2 hpq) hpq
    · have hsub : Set.Icc q p ⊆ Set.Ioo 0 1 := fun x hx =>
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hm : AntitoneOn h (Set.Icc q p) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc q p) (hcont.mono hsub)
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hx0 : 0 < x := by linarith [hx.1]
          have hx1 : x < 1 := by linarith [hx.2]
          rw [(hderiv x hx0 hx1).deriv]
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (sq_nonneg _))
            (mul_pos hx0 (sub_pos.2 hx1)).le
      exact hm (Set.left_mem_Icc.2 hqp) (Set.right_mem_Icc.2 hqp) hqp
  have e1 := bkl_eq p hq0 hq1
  simp only [hh] at key
  linarith

lemma continuousAt_bkl (p : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ContinuousAt (fun x => bkl p x) c := by
  have h : ContinuousAt
      (fun x => p * log p + (1 - p) * log (1 - p) - p * log x - (1 - p) * log (1 - x)) c := by
    have h1 : ContinuousAt (fun x : ℝ => log x) c := continuousAt_log hc0.ne'
    have h2 : ContinuousAt (fun x : ℝ => log (1 - x)) c :=
      (continuousAt_const.sub continuousAt_id).log (sub_pos.2 hc1).ne'
    exact (continuousAt_const.sub (continuousAt_const.mul h1)).sub (continuousAt_const.mul h2)
  refine h.congr ?_
  filter_upwards [Ioo_mem_nhds hc0 hc1] with x hx
  exact (bkl_eq p hx.1 hx.2).symm

/-! ### The clipped divergence -/

lemma dDown_of_lt {p c : ℝ} (h : c < p) : dDown p c = bkl p c := by simp [dDown, h]

lemma dDown_of_le {p c : ℝ} (h : p ≤ c) : dDown p c = 0 := by simp [dDown, not_lt.2 h]

lemma dDown_nonneg {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc0 : 0 < c) (hc1 : c < 1) :
    0 ≤ dDown p c := by
  unfold dDown
  split_ifs
  · exact bkl_nonneg hp0 hp1 hc0 hc1
  · exact le_rfl

/-- `d_↓(p, c) = kl(p, min(p, c))`: the cheapest value below the cap `c`. -/
lemma bkl_min_eq_dDown (p c : ℝ) : bkl p (min p c) = dDown p c := by
  unfold dDown
  split_ifs with h
  · rw [min_eq_right h.le]
  · rw [min_eq_left (not_lt.1 h), bkl_self]

/-- For a fixed cap `c`, `p ↦ d_↓(p,c)` is nondecreasing. -/
lemma dDown_mono_left {p p' c : ℝ} (hp0 : 0 ≤ p) (hpp : p ≤ p') (hp1 : p' ≤ 1)
    (hc0 : 0 < c) (hc1 : c < 1) : dDown p c ≤ dDown p' c := by
  rcases hpp.eq_or_lt with h | h
  · rw [h]
  · by_cases hc : c < p
    · rw [dDown_of_lt hc, dDown_of_lt (hc.trans h)]
      exact bkl_mono_left hc0 hc.le (lt_of_lt_of_le h hp1) hpp hp1
    · rw [dDown_of_le (not_lt.1 hc)]
      exact dDown_nonneg (hp0.trans hpp) hp1 hc0 hc1

/-- Any admissible inside value `x < c` costs at least `d_↓(p,c)`. -/
lemma dDown_le_bkl {p c x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx0 : 0 < x) (hxc : x < c)
    (hc1 : c < 1) : dDown p c ≤ bkl p x := by
  unfold dDown
  split_ifs with h
  · exact bkl_mono_right hp0 hp1 (hx0.trans hxc) hc1 hx0 (hxc.trans hc1)
      (mul_nonneg (sub_nonneg.2 hxc.le) (sub_nonneg.2 h.le))
  · exact bkl_nonneg hp0 hp1 hx0 (hxc.trans hc1)

/-! ### Alternatives and the scalar information projection -/

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- Invalidating alternatives of a root action with support `S` (`eq:active-alt`): interior
Bernoulli mean vectors in which some excluded terminal beats every retained terminal by more
than `ε`.  `mem_Alt_iff_sup` shows this is the manuscript's condition
`max_{z ∉ S} λ_z > max_{y ∈ S} λ_y + ε`. -/
def Alt (S : Finset Z) (ε : ℝ) : Set (Z → ℝ) :=
  {lam | (∀ i, 0 < lam i ∧ lam i < 1) ∧ ∃ z, z ∉ S ∧ ∀ y ∈ S, lam y + ε < lam z}

lemma mem_Alt_iff_sup {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {ε : ℝ}
    {lam : Z → ℝ} :
    lam ∈ Alt S ε ↔ (∀ i, 0 < lam i ∧ lam i < 1) ∧ val S hS lam + ε < Sᶜ.sup' hSc lam := by
  constructor
  · rintro ⟨hint, z, hz, hlt⟩
    refine ⟨hint, ?_⟩
    obtain ⟨y, hy, hval⟩ := exists_mem_eq_sup' hS lam
    have h1 : lam z ≤ Sᶜ.sup' hSc lam := le_sup' lam (mem_compl.2 hz)
    have h2 := hlt y hy
    have h3 : val S hS lam = lam y := hval
    linarith
  · rintro ⟨hint, hlt⟩
    obtain ⟨z, hz, hsup⟩ := exists_mem_eq_sup' hSc lam
    refine ⟨hint, z, mem_compl.1 hz, fun y hy => ?_⟩
    have := le_val hS lam hy
    linarith

/-- For `ε ≥ 0` the alternatives are exactly the interior parameters at which the action has
regret larger than `ε`. -/
lemma mem_Alt_iff_regret {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {ε : ℝ}
    (hε : 0 ≤ ε) {lam : Z → ℝ} :
    lam ∈ Alt S ε ↔ (∀ i, 0 < lam i ∧ lam i < 1) ∧ ε < regret S hS lam := by
  rw [mem_Alt_iff_sup hS hSc, regret_eq hSc, lt_max_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inr (by linarith)⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 (not_lt.2 hε)
    · exact ⟨h1, by linarith⟩

/-- Weighted information cost `∑_i v_i kl(μ_i, λ_i)` of an alternative. -/
noncomputable def infoCost (v μ lam : Z → ℝ) : ℝ := ∑ i, v i * bkl (μ i) (lam i)

/-- Scalar objective of `eq:active-projection` for the outside challenger `z` at level `θ`. -/
noncomputable def scalarObj (S : Finset Z) (ε : ℝ) (v μ : Z → ℝ) (z : Z) (θ : ℝ) : ℝ :=
  v z * bkl (μ z) θ + ∑ y ∈ S, v y * dDown (μ y) (θ - ε)

/-- `I_a^ε(μ, v) = inf_{λ ∈ Alt_ε(a)} ∑_i v_i kl(μ_i, λ_i)`. -/
noncomputable def infoRate (S : Finset Z) (ε : ℝ) (v μ : Z → ℝ) : ℝ :=
  sInf (infoCost v μ '' Alt S ε)

lemma infoCost_nonneg {v μ lam : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1)
    (hlam : ∀ i, 0 < lam i ∧ lam i < 1) : 0 ≤ infoCost v μ lam :=
  sum_nonneg fun i _ =>
    mul_nonneg (hv i) (bkl_nonneg (hμ i).1 (hμ i).2 (hlam i).1 (hlam i).2)

lemma infoCost_bddBelow {S : Finset Z} {ε : ℝ} {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) : BddBelow (infoCost v μ '' Alt S ε) :=
  ⟨0, by rintro _ ⟨lam, hl, rfl⟩; exact infoCost_nonneg hv hμ hl.1⟩

lemma scalarObj_nonneg {S : Finset Z} {ε : ℝ} {v μ : Z → ℝ} (hε : 0 ≤ ε) (hv : ∀ i, 0 ≤ v i)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) {z : Z} {θ : ℝ} (hθ : θ ∈ Set.Ioo ε 1) :
    0 ≤ scalarObj S ε v μ z θ :=
  add_nonneg (mul_nonneg (hv z) (bkl_nonneg (hμ z).1 (hμ z).2 (hε.trans_lt hθ.1) hθ.2))
    (sum_nonneg fun y _ => mul_nonneg (hv y)
      (dDown_nonneg (hμ y).1 (hμ y).2 (sub_pos.2 hθ.1) (by linarith [hθ.2])))

lemma scalarObj_bddBelow {S : Finset Z} {ε : ℝ} {v μ : Z → ℝ} (hε : 0 ≤ ε) (hv : ∀ i, 0 ≤ v i)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (z : Z) : BddBelow (scalarObj S ε v μ z '' Set.Ioo ε 1) :=
  ⟨0, by rintro _ ⟨θ, hθ, rfl⟩; exact scalarObj_nonneg hε hv hμ hθ⟩

/-- Lower-bound half of `thm:active-kl-projection`: every alternative costs at least the scalar
objective of its outside challenger `z` at level `θ = λ_z`. -/
theorem exists_scalarObj_le_infoCost {S : Finset Z} (hS : S.Nonempty) {ε : ℝ} (hε : 0 ≤ ε)
    {v μ lam : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1)
    (hlam : lam ∈ Alt S ε) :
    ∃ z, z ∉ S ∧ ∃ θ ∈ Set.Ioo ε 1, scalarObj S ε v μ z θ ≤ infoCost v μ lam := by
  obtain ⟨hint, z, hz, hlt⟩ := hlam
  obtain ⟨y0, hy0⟩ := hS
  have hθ : lam z ∈ Set.Ioo ε 1 := ⟨by linarith [hlt y0 hy0, (hint y0).1], (hint z).2⟩
  refine ⟨z, hz, lam z, hθ, ?_⟩
  have hF : ∀ i, 0 ≤ v i * bkl (μ i) (lam i) := fun i =>
    mul_nonneg (hv i) (bkl_nonneg (hμ i).1 (hμ i).2 (hint i).1 (hint i).2)
  have h1 : ∑ i ∈ insert z S, v i * bkl (μ i) (lam i) ≤ infoCost v μ lam :=
    sum_le_univ_sum_of_nonneg hF
  rw [sum_insert hz] at h1
  have h2 : ∑ y ∈ S, v y * dDown (μ y) (lam z - ε) ≤ ∑ y ∈ S, v y * bkl (μ y) (lam y) :=
    sum_le_sum fun y hy => mul_le_mul_of_nonneg_left
      (dDown_le_bkl (hμ y).1 (hμ y).2 (hint y).1 (by linarith [hlt y hy])
        (by linarith [hθ.2])) (hv y)
  unfold scalarObj
  linarith

/-- Upper-bound half of `thm:active-kl-projection`: for every outside challenger `z` and level
`θ ∈ (ε,1)` there are admissible alternatives whose cost is arbitrarily close to the scalar
objective (challenger at `θ`, inside coordinates slightly below `min(μ_y, θ-ε)`, all other
coordinates at their true means). -/
theorem exists_alt_infoCost_lt {S : Finset Z} {ε : ℝ} (hε : 0 ≤ ε) {v μ : Z → ℝ}
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {z : Z} (hz : z ∉ S) {θ : ℝ} (hθ : θ ∈ Set.Ioo ε 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ lam ∈ Alt S ε, infoCost v μ lam < scalarObj S ε v μ z θ + η := by
  set c : Z → ℝ := fun y => min (μ y) (θ - ε) with hc
  have hc0 : ∀ y, 0 < c y := fun y => lt_min (hμ y).1 (sub_pos.2 hθ.1)
  have hc1 : ∀ y, c y < 1 := fun y => lt_of_le_of_lt (min_le_left _ _) (hμ y).2
  set g : ℝ → ℝ := fun t => v z * bkl (μ z) θ + ∑ y ∈ S, v y * bkl (μ y) (c y - t) with hg
  have hg0 : g 0 = scalarObj S ε v μ z θ := by
    simp only [hg, hc, sub_zero, bkl_min_eq_dDown, scalarObj]
  have hcont : ContinuousAt g 0 := by
    refine continuousAt_const.add (tendsto_finsetSum _ fun y _ => ContinuousAt.mul continuousAt_const ?_)
    have h1 : ContinuousAt (fun x => bkl (μ y) x) ((fun t : ℝ => c y - t) 0) := by
      simpa using continuousAt_bkl (μ y) (hc0 y) (hc1 y)
    exact ContinuousAt.comp (f := fun t : ℝ => c y - t) h1
      (continuousAt_const.sub continuousAt_id)
  have he1 : ∀ᶠ t in 𝓝 (0 : ℝ), g t < g 0 + η :=
    hcont.preimage_mem_nhds (Iio_mem_nhds (lt_add_of_pos_right _ hη))
  have he2 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ S, t < c y :=
    (eventually_all_finset S).2 fun y _ => Iio_mem_nhds (hc0 y)
  have he3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g t < g 0 + η ∧ ∀ y ∈ S, t < c y) ∧ 0 < t :=
    ((he1.and he2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ⟨hgt, htc⟩, ht0⟩ := he3.exists
  let lam : Z → ℝ := fun i => if i = z then θ else if i ∈ S then c i - t else μ i
  have hlz : lam z = θ := by simp [lam]
  have hlS : ∀ y ∈ S, lam y = c y - t := fun y hy => by
    have : y ≠ z := fun h => hz (h ▸ hy)
    simp [lam, this, hy]
  have hlo : ∀ i, i ≠ z → i ∉ S → lam i = μ i := fun i h1 h2 => by simp [lam, h1, h2]
  refine ⟨lam, ⟨fun i => ?_, z, hz, fun y hy => ?_⟩, ?_⟩
  · by_cases hiz : i = z
    · rw [hiz, hlz]
      exact ⟨hε.trans_lt hθ.1, hθ.2⟩
    · by_cases hiS : i ∈ S
      · rw [hlS i hiS]
        exact ⟨by linarith [htc i hiS], by linarith [hc1 i]⟩
      · rw [hlo i hiz hiS]
        exact hμ i
  · rw [hlS y hy, hlz]
    have : c y ≤ θ - ε := min_le_right _ _
    linarith
  · have hcost : infoCost v μ lam = g t := by
      unfold infoCost
      rw [← add_sum_erase univ _ (mem_univ z), hlz]
      simp only [hg]
      congr 1
      have hsub : S ⊆ univ.erase z := fun y hy =>
        mem_erase.2 ⟨fun h => hz (h ▸ hy), mem_univ y⟩
      rw [← sum_subset hsub]
      · exact sum_congr rfl fun y hy => by rw [hlS y hy]
      · intro i hi hiS
        rw [hlo i (mem_erase.1 hi).1 hiS, bkl_self, mul_zero]
    rw [hcost, ← hg0]
    exact hgt

lemma alt_nonempty {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (Alt S ε).Nonempty := by
  obtain ⟨z, hz⟩ := hSc
  obtain ⟨lam, hlam, -⟩ := exists_alt_infoCost_lt (S := S) hε0 (v := fun _ => 0)
    (μ := fun _ => 1 / 2) (fun _ => ⟨by norm_num, by norm_num⟩) (mem_compl.1 hz)
    (θ := (ε + 1) / 2) ⟨by linarith, by linarith⟩ one_pos
  exact ⟨lam, hlam⟩

/-- The information rate is at most every scalar objective. -/
theorem infoRate_le_scalarObj {S : Finset Z} {ε : ℝ} (hε : 0 ≤ ε) {v μ : Z → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {z : Z} (hz : z ∉ S) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo ε 1) : infoRate S ε v μ ≤ scalarObj S ε v μ z θ :=
  le_of_forall_pos_le_add fun η hη => by
    obtain ⟨lam, hlam, hlt⟩ := exists_alt_infoCost_lt (S := S) (v := v) hε hμ hz hθ hη
    exact (csInf_le (infoCost_bddBelow hv fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩)
      ⟨lam, hlam, rfl⟩).trans hlt.le

/-- **Scalar information projection for a fixed root answer** (`thm:active-kl-projection`,
identity `eq:active-projection`; also `eq:ast-projection` for interior `p`).
For a proper nonempty support `S`, `0 ≤ ε < 1`, nonnegative weights `v` (not necessarily
normalized, zero weights allowed) and interior means `μ`,
`inf_{λ ∈ Alt_ε(a)} ∑_i v_i kl(μ_i,λ_i)
  = min_{z ∉ S} inf_{ε<θ<1} [v_z kl(μ_z,θ) + ∑_{y ∈ S} v_y d_↓(μ_y, θ-ε)]`.
Each terminal contributes one term to the cost regardless of how many supports contain it. -/
theorem info_projection {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) :
    infoRate S ε v μ
      = Sᶜ.inf' hSc (fun z => sInf (scalarObj S ε v μ z '' Set.Ioo ε 1)) := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hne : (Set.Ioo ε 1).Nonempty := Set.nonempty_Ioo.2 hε1
  apply le_antisymm
  · refine le_inf' _ _ fun z hz => le_csInf (hne.image _) ?_
    rintro _ ⟨θ, hθ, rfl⟩
    exact infoRate_le_scalarObj hε0 hv hμ (mem_compl.1 hz) hθ
  · refine le_csInf ((alt_nonempty hSc hε0 hε1).image _) ?_
    rintro _ ⟨lam, hlam, rfl⟩
    obtain ⟨z, hz, θ, hθ, hle⟩ := exists_scalarObj_le_infoCost hS hε0 hv hμ' hlam
    exact (inf'_le _ (mem_compl.2 hz)).trans
      ((csInf_le (scalarObj_bddBelow hε0 hv hμ' z) ⟨θ, hθ, rfl⟩).trans hle)

/-! ### Properties of the allocation game -/

lemma infoRate_nonneg {S : Finset Z} {ε : ℝ} {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) : 0 ≤ infoRate S ε v μ := by
  unfold infoRate
  refine Real.sInf_nonneg ?_
  rintro _ ⟨lam, hl, rfl⟩
  exact infoCost_nonneg hv hμ hl.1

/-- Support dominance (paragraph "Support dominance and scope"): a larger support has fewer
invalidating alternatives. -/
lemma Alt_anti {S S' : Finset Z} (h : S ⊆ S') (ε : ℝ) : Alt S' ε ⊆ Alt S ε := by
  rintro lam ⟨hint, z, hz, hlt⟩
  exact ⟨hint, z, fun hzS => hz (h hzS), fun y hy => hlt y (h hy)⟩

/-- Support dominance: if `S(a) ⊆ S(b)` then `I_b^ε ≥ I_a^ε` for every allocation. -/
theorem infoRate_mono_support {S S' : Finset Z} (h : S ⊆ S') (hSc' : S'ᶜ.Nonempty) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) : infoRate S ε v μ ≤ infoRate S' ε v μ :=
  csInf_le_csInf (infoCost_bddBelow hv hμ) ((alt_nonempty hSc' hε0 hε1).image _)
    (Set.image_mono (Alt_anti h ε))

lemma bkl_le_neg_log {p q b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : 0 < b) (hbq : b ≤ q)
    (hqb : q ≤ 1 - b) : bkl p q ≤ -log b := by
  have hq0 : 0 < q := hb.trans_le hbq
  have hq1 : q < 1 := by linarith
  have h1 : p * log p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 (log_nonpos hp0 hp1)
  have h2 : (1 - p) * log (1 - p) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (log_nonpos (by linarith) (by linarith))
  have h3 : log b ≤ log q := log_le_log hb hbq
  have h4 : log b ≤ log (1 - q) := log_le_log hb (by linarith)
  have h5 := mul_le_mul_of_nonneg_left h3 hp0
  have h6 := mul_le_mul_of_nonneg_left h4 (sub_nonneg.2 hp1)
  rw [bkl_eq p hq0 hq1]
  linarith

/-- The reference alternative of `app:ast-regularity` (inside coordinates `b_ε = (1-ε)/4`,
one challenger at `1 - b_ε`, all others `1/2`) bounds the rate by
`(∑ v) · D_ε`, `D_ε = log(1/b_ε) = log(4/(1-ε))`. -/
theorem infoRate_le_mul_log {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) :
    infoRate S ε v μ ≤ (∑ i, v i) * log (4 / (1 - ε)) := by
  obtain ⟨z, hz⟩ := hSc
  have hz' := mem_compl.1 hz
  have hb0 : 0 < (1 - ε) / 4 := by linarith
  let ref : Z → ℝ := fun i => if i ∈ S then (1 - ε) / 4 else if i = z then 1 - (1 - ε) / 4 else 1 / 2
  have hrefS : ∀ y ∈ S, ref y = (1 - ε) / 4 := fun y hy => by simp [ref, hy]
  have hrefz : ref z = 1 - (1 - ε) / 4 := by simp [ref, hz']
  have hrange : ∀ i, (1 - ε) / 4 ≤ ref i ∧ ref i ≤ 1 - (1 - ε) / 4 := by
    intro i
    dsimp only [ref]
    split_ifs <;> constructor <;> linarith
  have hmem : ref ∈ Alt S ε :=
    ⟨fun i => ⟨by linarith [(hrange i).1], by linarith [(hrange i).2]⟩, z, hz',
      fun y hy => by rw [hrefS y hy, hrefz]; linarith⟩
  have hD : -log ((1 - ε) / 4) = log (4 / (1 - ε)) := by rw [← log_inv, inv_div]
  calc infoRate S ε v μ ≤ infoCost v μ ref :=
        csInf_le (infoCost_bddBelow hv hμ) ⟨ref, hmem, rfl⟩
    _ ≤ ∑ i, v i * log (4 / (1 - ε)) := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by
          rw [← hD]
          exact bkl_le_neg_log (hμ i).1 (hμ i).2 hb0 (hrange i).1 (hrange i).2) (hv i)
    _ = (∑ i, v i) * log (4 / (1 - ε)) := (sum_mul _ _ _).symm

lemma infoCost_add_smul (a b : ℝ) (v v' μ lam : Z → ℝ) :
    infoCost (fun i => a * v i + b * v' i) μ lam
      = a * infoCost v μ lam + b * infoCost v' μ lam := by
  simp only [infoCost, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- The rate is concave in the (unnormalized) weights. -/
theorem infoRate_concave {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {v v' μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hv' : ∀ i, 0 ≤ v' i)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * infoRate S ε v μ + b * infoRate S ε v' μ
      ≤ infoRate S ε (fun i => a * v i + b * v' i) μ := by
  refine le_csInf ((alt_nonempty hSc hε0 hε1).image _) ?_
  rintro _ ⟨lam, hlam, rfl⟩
  rw [infoCost_add_smul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (csInf_le (infoCost_bddBelow hv hμ) ⟨lam, hlam, rfl⟩) ha)
    (mul_le_mul_of_nonneg_left (csInf_le (infoCost_bddBelow hv' hμ) ⟨lam, hlam, rfl⟩) hb)

/-- The rate is positively homogeneous in the weights. -/
theorem infoRate_smul (S : Finset Z) (ε : ℝ) (v μ : Z → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    infoRate S ε (fun i => a * v i) μ = a * infoRate S ε v μ := by
  have h : infoCost (fun i => a * v i) μ '' Alt S ε = a • (infoCost v μ '' Alt S ε) := by
    rw [← Set.image_smul, Set.image_image]
    refine Set.image_congr fun lam _ => ?_
    simp only [infoCost, smul_eq_mul, mul_sum, mul_assoc]
  unfold infoRate
  rw [h, Real.sInf_smul_of_nonneg ha, smul_eq_mul]

/-- Characteristic rate of a fixed answer, `C_a^ε(μ) = sup_{w ∈ Δ_M} I_a^ε(μ,w)`. -/
noncomputable def charRate (S : Finset Z) (ε : ℝ) (μ : Z → ℝ) : ℝ :=
  sSup ((fun w => infoRate S ε w μ) '' simplex Z)

lemma infoRate_le_log_of_mem_simplex {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {w μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (hw : w ∈ simplex Z) :
    infoRate S ε w μ ≤ log (4 / (1 - ε)) := by
  have := infoRate_le_mul_log hSc hε0 hε1 hw.1 hμ
  rwa [hw.2, one_mul] at this

lemma charRate_bddAbove {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) :
    BddAbove ((fun w => infoRate S ε w μ) '' simplex Z) :=
  ⟨log (4 / (1 - ε)), by
    rintro _ ⟨w, hw, rfl⟩
    exact infoRate_le_log_of_mem_simplex hSc hε0 hε1 hμ hw⟩

lemma le_charRate {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {w μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (hw : w ∈ simplex Z) :
    infoRate S ε w μ ≤ charRate S ε μ :=
  le_csSup (charRate_bddAbove hSc hε0 hε1 hμ) ⟨w, hw, rfl⟩

lemma uniform_mem_simplex : (fun _ : Z => 1 / (Fintype.card Z : ℝ)) ∈ simplex Z := by
  refine ⟨fun _ => by positivity, ?_⟩
  have : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

lemma simplex_nonempty : (simplex Z).Nonempty := ⟨_, uniform_mem_simplex⟩

/-- `0 ≤ C_a^ε(μ) ≤ D_ε`. -/
theorem charRate_mem_Icc {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) :
    0 ≤ charRate S ε μ ∧ charRate S ε μ ≤ log (4 / (1 - ε)) := by
  constructor
  · exact (infoRate_nonneg (fun _ => by positivity) hμ).trans
      (le_charRate hSc hε0 hε1 hμ uniform_mem_simplex)
  · refine csSup_le (simplex_nonempty.image _) ?_
    rintro _ ⟨w, hw, rfl⟩
    exact infoRate_le_log_of_mem_simplex hSc hε0 hε1 hμ hw

lemma le_of_forall_small {f : ℝ → ℝ} {x η0 : ℝ} (hη0 : 0 < η0) (hf : ContinuousAt f 0)
    (h : ∀ η, 0 < η → η < η0 → x ≤ f η) : x ≤ f 0 := by
  have h1 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto h1 ?_
  filter_upwards [Ioo_mem_nhdsGT hη0] with η hη using h η hη.1 hη.2

/-- If `h_a = V_a + ε - V_a^- ≤ 0` the rate vanishes for every allocation: the true parameter
is an alternative or a limit of alternatives of vanishing divergence. -/
theorem infoRate_eq_zero_of_margin_nonpos {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    {ε : ℝ} (hε0 : 0 ≤ ε) {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 < μ i ∧ μ i < 1)
    (h : val S hS μ + ε ≤ Sᶜ.sup' hSc μ) : infoRate S ε v μ = 0 := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  refine le_antisymm ?_ (infoRate_nonneg hv hμ')
  obtain ⟨z, hz, hsup⟩ := exists_mem_eq_sup' hSc μ
  have hz' := mem_compl.1 hz
  have ⟨y0, hy0⟩ := hS
  have hyz : ∀ y ∈ S, μ y + ε ≤ μ z := fun y hy => by
    have := le_val hS μ hy
    linarith
  have hcont : ContinuousAt (fun η : ℝ => v z * bkl (μ z) (μ z + η)) 0 := by
    have h1 : ContinuousAt (fun x => bkl (μ z) x) ((fun η : ℝ => μ z + η) 0) := by
      simpa using continuousAt_bkl (μ z) (hμ z).1 (hμ z).2
    exact ContinuousAt.mul continuousAt_const
      (ContinuousAt.comp (f := fun η : ℝ => μ z + η) h1 (continuousAt_const.add continuousAt_id))
  have key := le_of_forall_small (x := infoRate S ε v μ) (sub_pos.2 (hμ z).2) hcont ?_
  · simpa [bkl_self] using key
  · intro η hη0 hη1
    have hθ : μ z + η ∈ Set.Ioo ε 1 :=
      ⟨by linarith [hyz y0 hy0, (hμ y0).1], by linarith⟩
    refine (infoRate_le_scalarObj hε0 hv hμ hz' hθ).trans (le_of_eq ?_)
    unfold scalarObj
    rw [sum_eq_zero, add_zero]
    intro y hy
    rw [dDown_of_le (by linarith [hyz y hy]), mul_zero]

/-- If `h_a = V_a + ε - V_a^- > 0`, uniform allocation gives information at least
`h_a² / (2M)` (Pinsker). -/
theorem infoRate_uniform_ge {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1)
    (h : Sᶜ.sup' hSc μ < val S hS μ + ε) :
    (val S hS μ + ε - Sᶜ.sup' hSc μ) ^ 2 / (2 * (Fintype.card Z : ℝ))
      ≤ infoRate S ε (fun _ => 1 / (Fintype.card Z : ℝ)) μ := by
  have hM : 0 < (Fintype.card Z : ℝ) := by exact_mod_cast Fintype.card_pos
  generalize hMd : (Fintype.card Z : ℝ) = M at hM ⊢
  obtain ⟨j, hj, hval⟩ := exists_mem_eq_sup' hS μ
  have hvj : val S hS μ = μ j := hval
  generalize hhd : val S hS μ + ε - Sᶜ.sup' hSc μ = hh
  have hh0 : 0 < hh := by linarith
  refine le_csInf ((alt_nonempty hSc hε0 hε1).image _) ?_
  rintro _ ⟨lam, ⟨hint, z, hz, hlt⟩, rfl⟩
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  have h1 : μ z ≤ Sᶜ.sup' hSc μ := le_sup' μ (mem_compl.2 hz)
  have h2 := hlt j hj
  have hF : ∀ i, 0 ≤ 1 / M * bkl (μ i) (lam i) := fun i =>
    mul_nonneg (by positivity) (bkl_nonneg (hμ i).1.le (hμ i).2.le (hint i).1 (hint i).2)
  have h3 : ∑ i ∈ ({j, z} : Finset Z), 1 / M * bkl (μ i) (lam i)
      ≤ infoCost (fun _ => 1 / M) μ lam := sum_le_univ_sum_of_nonneg hF
  rw [sum_pair hjz] at h3
  have p1 := pinsker (hμ j).1 (hμ j).2 (hint j).1 (hint j).2
  have p2 := pinsker (hμ z).1 (hμ z).2 (hint z).1 (hint z).2
  have hab : hh < (μ j - lam j) + (lam z - μ z) := by linarith
  have h4 : hh ^ 2 ≤ 2 * (μ j - lam j) ^ 2 + 2 * (μ z - lam z) ^ 2 := by
    nlinarith [sq_nonneg ((μ j - lam j) - (lam z - μ z)),
      mul_pos (sub_pos.2 hab) (add_pos hh0 (hh0.trans hab))]
  have h5 : hh ^ 2 / (2 * M) ≤ 1 / M * (bkl (μ j) (lam j) + bkl (μ z) (lam z)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / M * (bkl (μ j) (lam j) + bkl (μ z) (lam z)) * (2 * M)
        = 2 * (bkl (μ j) (lam j) + bkl (μ z) (lam z)) := by field_simp
    rw [e]
    nlinarith [sq_nonneg hh]
  linarith

/-- The rate of a fixed answer is positive exactly when `h_a = V_a + ε - V_a^- > 0`. -/
theorem charRate_pos_iff {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) :
    0 < charRate S ε μ ↔ Sᶜ.sup' hSc μ < val S hS μ + ε := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  constructor
  · intro hpos
    by_contra hcon
    rw [not_lt] at hcon
    have : charRate S ε μ ≤ 0 := by
      refine csSup_le (simplex_nonempty.image _) ?_
      rintro _ ⟨w, hw, rfl⟩
      exact (infoRate_eq_zero_of_margin_nonpos hS hSc hε0 hw.1 hμ hcon).le
    linarith
  · intro h
    have h1 := infoRate_uniform_ge hS hSc hε0 hε1 hμ h
    have h2 := le_charRate (S := S) hSc hε0 hε1 hμ' uniform_mem_simplex
    have hM : 0 < (Fintype.card Z : ℝ) := by exact_mod_cast Fintype.card_pos
    have h3 : 0 < (val S hS μ + ε - Sᶜ.sup' hSc μ) ^ 2 / (2 * (Fintype.card Z : ℝ)) :=
      div_pos (pow_pos (by linarith) 2) (by positivity)
    linarith

/-! ### The one-witness reduction (`eq:ast-star`) -/

/-- Pair statistic `F_ε(m,q;s,t) = inf_{ε<θ<1} {s d_↓(m,θ-ε) + t kl(q,θ)}` (`eq:ast-pair`). -/
noncomputable def pairF (ε m q s t : ℝ) : ℝ :=
  sInf ((fun θ => s * dDown m (θ - ε) + t * bkl q θ) '' Set.Ioo ε 1)

/-- Star allocations: an inside weight `s` and outside weights `t_z`, `z ∉ S`, with
`s + ∑_{z ∉ S} t_z = 1`. -/
def starSet (S : Finset Z) : Set (ℝ × (Z → ℝ)) :=
  {st | 0 ≤ st.1 ∧ (∀ z, 0 ≤ st.2 z) ∧ st.1 + ∑ z ∈ Sᶜ, st.2 z = 1}

/-- Star objective `min_{z ∉ S} F_ε(μ_j, μ_z; s, t_z)` of `eq:ast-star`. -/
noncomputable def starVal (S : Finset Z) (hSc : Sᶜ.Nonempty) (ε : ℝ) (μ : Z → ℝ) (j : Z)
    (st : ℝ × (Z → ℝ)) : ℝ :=
  Sᶜ.inf' hSc fun z => pairF ε (μ j) (μ z) st.1 (st.2 z)

/-- Allocation that puts the inside weight `s` on the single terminal `j` and `t` outside. -/
def collapse (S : Finset Z) (j : Z) (s : ℝ) (t : Z → ℝ) : Z → ℝ :=
  fun i => if i ∈ S then (if i = j then s else 0) else t i

lemma collapse_sum_inside {S : Finset Z} {j : Z} (hj : j ∈ S) (s : ℝ) (t : Z → ℝ)
    (F : Z → ℝ) : ∑ y ∈ S, collapse S j s t y * F y = s * F j := by
  rw [sum_eq_single j]
  · simp [collapse, hj]
  · intro y hy hyj
    simp [collapse, hy, hyj]
  · intro h
    exact absurd hj h

lemma scalarObj_collapse {S : Finset Z} {j : Z} (hj : j ∈ S) (ε s : ℝ) (t μ : Z → ℝ) {z : Z}
    (hz : z ∉ S) (θ : ℝ) :
    scalarObj S ε (collapse S j s t) μ z θ = s * dDown (μ j) (θ - ε) + t z * bkl (μ z) θ := by
  unfold scalarObj
  have h1 : collapse S j s t z = t z := by simp [collapse, hz]
  rw [h1, collapse_sum_inside hj]
  ring

lemma collapse_nonneg {S : Finset Z} {j : Z} {s : ℝ} {t : Z → ℝ} (hs : 0 ≤ s)
    (ht : ∀ z, 0 ≤ t z) (i : Z) : 0 ≤ collapse S j s t i := by
  unfold collapse
  split_ifs
  · exact hs
  · exact le_rfl
  · exact ht i

lemma collapse_mem_simplex {S : Finset Z} {j : Z} (hj : j ∈ S) {s : ℝ} {t : Z → ℝ}
    (hst : (s, t) ∈ starSet S) : collapse S j s t ∈ simplex Z := by
  obtain ⟨hs, ht, hsum⟩ := hst
  refine ⟨collapse_nonneg hs ht, ?_⟩
  rw [← sum_add_sum_compl S]
  have h1 : ∑ i ∈ S, collapse S j s t i = s := by
    have := collapse_sum_inside hj s t (fun _ => 1)
    simpa using this
  have h2 : ∑ i ∈ Sᶜ, collapse S j s t i = ∑ i ∈ Sᶜ, t i :=
    sum_congr rfl fun i hi => by simp [collapse, mem_compl.1 hi]
  rw [h1, h2]
  exact hsum

/-- With all inside weight on one terminal `j ∈ S`, the rate is the star objective. -/
theorem infoRate_collapse {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {j : Z}
    (hj : j ∈ S) {s : ℝ} {t : Z → ℝ} (hs : 0 ≤ s) (ht : ∀ z, 0 ≤ t z) :
    infoRate S ε (collapse S j s t) μ = starVal S hSc ε μ j (s, t) := by
  rw [info_projection hS hSc hε0 hε1 (collapse_nonneg hs ht) hμ]
  unfold starVal pairF
  refine inf'_congr hSc rfl fun z hz => ?_
  congr 1
  refine Set.image_congr fun θ _ => ?_
  exact scalarObj_collapse hj ε s t μ (mem_compl.1 hz) θ

lemma sInf_image_le_sInf_image {A : Set ℝ} {f g : ℝ → ℝ} (hA : A.Nonempty)
    (hbdd : BddBelow (f '' A)) (h : ∀ x ∈ A, f x ≤ g x) : sInf (f '' A) ≤ sInf (g '' A) :=
  le_csInf (hA.image _) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (csInf_le hbdd ⟨x, hx, rfl⟩).trans (h x hx))

/-- Moving all inside weight to an inside maximizer `j` cannot decrease the rate
(monotonicity of `p ↦ d_↓(p,c)`).  This concerns prospective allocations only. -/
theorem infoRate_le_starVal {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {w μ : Z → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {j : Z} (hmax : ∀ y ∈ S, μ y ≤ μ j) :
    infoRate S ε w μ ≤ starVal S hSc ε μ j (∑ y ∈ S, w y, w) := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  rw [info_projection hS hSc hε0 hε1 hw hμ]
  unfold starVal pairF
  refine le_inf' _ _ fun z hz => (inf'_le _ hz).trans ?_
  refine sInf_image_le_sInf_image (Set.nonempty_Ioo.2 hε1) (scalarObj_bddBelow hε0 hw hμ' z)
    fun θ hθ => ?_
  have h1 : ∑ y ∈ S, w y * dDown (μ y) (θ - ε) ≤ (∑ y ∈ S, w y) * dDown (μ j) (θ - ε) := by
    rw [sum_mul]
    exact sum_le_sum fun y hy => mul_le_mul_of_nonneg_left
      (dDown_mono_left (hμ y).1.le (hmax y hy) (hμ j).2.le (sub_pos.2 hθ.1)
        (by linarith [hθ.2])) (hw y)
  show w z * bkl (μ z) θ + ∑ y ∈ S, w y * dDown (μ y) (θ - ε)
    ≤ (∑ y ∈ S, w y) * dDown (μ j) (θ - ε) + w z * bkl (μ z) θ
  linarith

/-- **One inside witness** (`thm:ast-main`, identity `eq:ast-star`).  For a proper nonempty
support, interior means and an inside maximizer `j ∈ argmax_{y ∈ S} μ_y`,
`C_a^ε = sup_{s, t ≥ 0, s + ∑_{z ∉ S} t_z = 1} min_{z ∉ S} inf_{ε<q<1}
  {s d_↓(μ_j, q-ε) + t_z kl(μ_z, q)}`.
Both sides are suprema (`sSup`); attainment of the maxima is not proved here. -/
theorem one_witness_reduction {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {j : Z}
    (hj : j ∈ S) (hmax : ∀ y ∈ S, μ y ≤ μ j) :
    charRate S ε μ = sSup (starVal S hSc ε μ j '' starSet S) := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hstar : ∀ st ∈ starSet S, starVal S hSc ε μ j st
      = infoRate S ε (collapse S j st.1 st.2) μ ∧ collapse S j st.1 st.2 ∈ simplex Z := by
    rintro ⟨s, t⟩ hst
    exact ⟨(infoRate_collapse hS hSc hε0 hε1 hμ hj hst.1 hst.2.1).symm,
      collapse_mem_simplex hj hst⟩
  have hbdd : BddAbove (starVal S hSc ε μ j '' starSet S) :=
    ⟨charRate S ε μ, by
      rintro _ ⟨st, hst, rfl⟩
      rw [(hstar st hst).1]
      exact le_charRate hSc hε0 hε1 hμ' (hstar st hst).2⟩
  apply le_antisymm
  · refine csSup_le (simplex_nonempty.image _) ?_
    rintro _ ⟨w, hw, rfl⟩
    refine le_csSup_of_le hbdd ⟨(∑ y ∈ S, w y, w), ⟨sum_nonneg fun y _ => hw.1 y, hw.1, ?_⟩, rfl⟩
      (infoRate_le_starVal hS hSc hε0 hε1 hw.1 hμ hmax)
    rw [sum_add_sum_compl]
    exact hw.2
  · have hne : (starSet S).Nonempty :=
      ⟨(1, fun _ => 0), by norm_num, fun _ => le_rfl, by simp⟩
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨st, hst, rfl⟩
    rw [(hstar st hst).1]
    exact le_charRate hSc hε0 hε1 hμ' (hstar st hst).2

/-! ### Two-arm rates with a single outside terminal -/

/-- Equal allocation on a two-arm pair: Pinsker gives `(m-q)²/2` at every level `θ`. -/
lemma two_arm_half {m q θ : ℝ} (hq0 : 0 < q) (hqm : q < m) (hm1 : m < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : (m - q) ^ 2 / 2 ≤ 1 / 2 * dDown m θ + 1 / 2 * bkl q θ := by
  have p2 := pinsker hq0 (hqm.trans hm1) hθ0 hθ1
  by_cases h : θ < m
  · rw [dDown_of_lt h]
    have p1 := pinsker (hq0.trans hqm) hm1 hθ0 hθ1
    nlinarith [sq_nonneg ((m - θ) - (θ - q))]
  · rw [dDown_of_le (not_lt.1 h)]
    nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h))
      (by linarith [not_lt.1 h] : (0 : ℝ) ≤ (θ - q) + (m - q))]

/-- If the support has a single outside terminal `z0` and an inside terminal `j` with
`μ_j > μ_{z0}`, then at `ε = 0` the rate is at least `(μ_j - μ_{z0})² / 2`
(allocate one half to `j` and one half to `z0`). -/
theorem charRate_ge_of_single_outside {S : Finset Z} (hS : S.Nonempty) {z0 : Z}
    (hSc : Sᶜ = {z0}) {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {j : Z} (hj : j ∈ S)
    (hlt : μ z0 < μ j) : (μ j - μ z0) ^ 2 / 2 ≤ charRate S 0 μ := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hSc' : Sᶜ.Nonempty := by rw [hSc]; exact singleton_nonempty z0
  have hz0 : z0 ∉ S := by
    have : z0 ∈ Sᶜ := by rw [hSc]; exact mem_singleton_self z0
    exact mem_compl.1 this
  have hjz : j ≠ z0 := fun e => hz0 (e ▸ hj)
  let w : Z → ℝ := fun i => if i = j then 1 / 2 else if i = z0 then 1 / 2 else 0
  have hwj : w j = 1 / 2 := by simp [w]
  have hwz : w z0 = 1 / 2 := by simp [w, hjz.symm]
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    dsimp only [w]
    split_ifs <;> norm_num
  have hw : w ∈ simplex Z := by
    refine ⟨hw0, ?_⟩
    have : ∑ i, w i = ∑ i ∈ ({j, z0} : Finset Z), w i := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      simp only [mem_insert, mem_singleton, not_or] at hi
      simp [w, hi.1, hi.2]
    rw [this, sum_pair hjz, hwj, hwz]
    norm_num
  refine le_trans ?_ (le_charRate hSc' le_rfl zero_lt_one hμ' hw)
  rw [info_projection hS hSc' le_rfl zero_lt_one hw0 hμ]
  refine le_inf' _ _ fun z hz => ?_
  have hzz : z = z0 := by
    rw [hSc] at hz
    exact mem_singleton.1 hz
  rw [hzz]
  refine le_csInf ((Set.nonempty_Ioo.2 zero_lt_one).image _) ?_
  rintro _ ⟨θ, hθ, rfl⟩
  have h1 : w j * dDown (μ j) (θ - 0) ≤ ∑ y ∈ S, w y * dDown (μ y) (θ - 0) :=
    single_le_sum (f := fun y => w y * dDown (μ y) (θ - 0)) (fun y _ => mul_nonneg (hw0 y)
      (dDown_nonneg (hμ y).1.le (hμ y).2.le (by simpa using hθ.1) (by simpa using hθ.2))) hj
  have h2 := two_arm_half (hμ z0).1 hlt (hμ j).2 hθ.1 hθ.2
  unfold scalarObj
  rw [hwj] at h1
  rw [hwz]
  simp only [sub_zero] at h1 ⊢
  linarith

/-! ### Regret on explicit instances -/

lemma regret_eq_zero_of_max {S : Finset Z} (hS : S.Nonempty) {f : Z → ℝ} {p0 : Z}
    (hp : p0 ∈ S) (h : ∀ z, f z ≤ f p0) : regret S hS f = 0 := by
  apply le_antisymm _ (regret_nonneg S hS f)
  rw [regret_le_iff]
  exact ⟨le_rfl, fun z _ => by
    have := le_val hS f hp
    linarith [h z]⟩

lemma lt_regret_of_outside {S : Finset Z} (hS : S.Nonempty) {f : Z → ℝ} {z : Z} {c ε : ℝ}
    (hval : ∀ y ∈ S, f y ≤ c) (hz : c + ε < f z) : ε < regret S hS f := by
  have hv : val S hS f ≤ c := sup'_le hS f hval
  have := le_gmax f z
  unfold regret
  linarith

lemma val_eq_of_max {S : Finset Z} (hS : S.Nonempty) {f : Z → ℝ} {p0 : Z} (hp : p0 ∈ S)
    (h : ∀ y ∈ S, f y ≤ f p0) : val S hS f = f p0 :=
  le_antisymm (sup'_le hS f h) (le_val hS f hp)

/-! ### Two explicit overlapping families on the terminals `none`, `some none`, `some (some i)` -/

/-- Terminal set with a shared terminal `none`, a special terminal `some none`, and a fan
`some (some i)`, `i < N`. -/
abbrev Fan (N : ℕ) := Option (Option (Fin N))

/-- The two-terminal support `{none, some none}`. -/
def pairSupp (N : ℕ) : Finset (Fan N) := {none, some none}

/-- The fan support `{none} ∪ {some (some i)}`. -/
def fanSupp (N : ℕ) : Finset (Fan N) := univ.erase (some none)

lemma pairSupp_nonempty (N : ℕ) : (pairSupp N).Nonempty := ⟨none, by simp [pairSupp]⟩

lemma fanSupp_nonempty (N : ℕ) : (fanSupp N).Nonempty := ⟨none, by simp [fanSupp]⟩

lemma fanSupp_compl (N : ℕ) : (fanSupp N)ᶜ = {some none} := by
  ext z
  simp [fanSupp]

lemma mem_fanSupp {N : ℕ} {z : Fan N} : z ∈ fanSupp N ↔ z ≠ some none := by simp [fanSupp]

lemma mem_pairSupp {N : ℕ} {z : Fan N} : z ∈ pairSupp N ↔ z = none ∨ z = some none := by
  simp [pairSupp]

/-! ### `prop:ast-gap-tradeoff` -/

/-- Means of `prop:ast-gap-tradeoff`: `μ_p = 1/2`, `μ_s = 1/2 - h`, `μ_{r_i} = 1/2 - g`
with `p = none`, `s = some none`, `r_i = some (some i)`. -/
noncomputable def gapMu (N : ℕ) (g h : ℝ) : Fan N → ℝ
  | none => 1 / 2
  | some none => 1 / 2 - h
  | some (some _) => 1 / 2 - g

lemma gapMu_p (N : ℕ) (g h : ℝ) : gapMu N g h none = 1 / 2 := rfl

lemma gapMu_s (N : ℕ) (g h : ℝ) : gapMu N g h (some none) = 1 / 2 - h := rfl

lemma gapMu_r (N : ℕ) (g h : ℝ) (i : Fin N) : gapMu N g h (some (some i)) = 1 / 2 - g := rfl

lemma gapMu_interior {N : ℕ} {g h : ℝ} (hh : 0 < h) (hhg : h < g) (hg : g ≤ 1 / 4) :
    ∀ i, 0 < gapMu N g h i ∧ gapMu N g h i < 1 := by
  rintro (_ | _ | i)
  · rw [gapMu_p]; constructor <;> norm_num
  · rw [gapMu_s]; constructor <;> linarith
  · rw [gapMu_r]; constructor <;> linarith

lemma gapMu_le_half {N : ℕ} {g h : ℝ} (hh : 0 < h) (hhg : h < g) :
    ∀ i, gapMu N g h i ≤ 1 / 2 := by
  rintro (_ | _ | i)
  · rw [gapMu_p]
  · rw [gapMu_s]; linarith
  · rw [gapMu_r]; linarith

/-- `prop:ast-gap-tradeoff`, structural part: with `S_A = {p,s}` and `S_B = {p,r_1,…,r_N}`
both actions are optimal, neither support contains the other, and the exterior margins are
`V_A - V_A^- = g > h = V_B - V_B^-`. -/
theorem gap_tradeoff_structure {N : ℕ} (hN : 0 < N) {g h : ℝ} (hh : 0 < h) (hhg : h < g)
    (hA : ((pairSupp N)ᶜ).Nonempty) (hB : ((fanSupp N)ᶜ).Nonempty) :
    regret (pairSupp N) (pairSupp_nonempty N) (gapMu N g h) = 0 ∧
    regret (fanSupp N) (fanSupp_nonempty N) (gapMu N g h) = 0 ∧
    ¬ pairSupp N ⊆ fanSupp N ∧ ¬ fanSupp N ⊆ pairSupp N ∧
    val (pairSupp N) (pairSupp_nonempty N) (gapMu N g h) - (pairSupp N)ᶜ.sup' hA (gapMu N g h) = g ∧
    val (fanSupp N) (fanSupp_nonempty N) (gapMu N g h) - (fanSupp N)ᶜ.sup' hB (gapMu N g h) = h := by
  have hpA : (none : Fan N) ∈ pairSupp N := mem_pairSupp.2 (Or.inl rfl)
  have hpB : (none : Fan N) ∈ fanSupp N := mem_fanSupp.2 (by simp)
  have hle := gapMu_le_half (N := N) hh hhg
  refine ⟨regret_eq_zero_of_max _ hpA hle, regret_eq_zero_of_max _ hpB hle, ?_, ?_, ?_, ?_⟩
  · intro hsub
    have h1 : (some none : Fan N) ∈ fanSupp N := hsub (mem_pairSupp.2 (Or.inr rfl))
    exact mem_fanSupp.1 h1 rfl
  · intro hsub
    have h1 : (some (some ⟨0, hN⟩) : Fan N) ∈ pairSupp N := hsub (mem_fanSupp.2 (by simp))
    simpa using mem_pairSupp.1 h1
  · rw [val_eq_of_max _ hpA (fun y _ => hle y), gapMu_p]
    have hsup : (pairSupp N)ᶜ.sup' hA (gapMu N g h) = 1 / 2 - g := by
      apply le_antisymm
      · refine sup'_le _ _ fun z hz => ?_
        rcases z with _ | _ | i
        · exact absurd hpA (mem_compl.1 hz)
        · exact absurd (mem_pairSupp.2 (Or.inr rfl)) (mem_compl.1 hz)
        · exact (gapMu_r N g h i).le
      · have hmem : (some (some ⟨0, hN⟩) : Fan N) ∈ (pairSupp N)ᶜ := by
          rw [mem_compl, mem_pairSupp]; simp
        exact (gapMu_r N g h ⟨0, hN⟩).ge.trans (le_sup' (gapMu N g h) hmem)
    rw [hsup]; ring
  · rw [val_eq_of_max _ hpB (fun y _ => hle y), gapMu_p]
    have hsup : (fanSupp N)ᶜ.sup' hB (gapMu N g h) = 1 / 2 - h := by
      apply le_antisymm
      · refine sup'_le _ _ fun z hz => ?_
        rw [fanSupp_compl, mem_singleton] at hz
        rw [hz, gapMu_s]
      · have hmem : (some none : Fan N) ∈ (fanSupp N)ᶜ := by
          rw [fanSupp_compl]; exact mem_singleton_self _
        exact (gapMu_s N g h).ge.trans (le_sup' (gapMu N g h) hmem)
    rw [hsup]; ring

/-- `prop:ast-gap-tradeoff`, first bound: for every allocation `w ∈ Δ`, the information for
the larger-margin answer `A` is at most `4g²/N`; hence `C_A^0(μ) ≤ 4g²/N`. -/
theorem gap_tradeoff_A {N : ℕ} (hN : 0 < N) {g h : ℝ} (hh : 0 < h) (hhg : h < g)
    (hg : g ≤ 1 / 4) : charRate (pairSupp N) 0 (gapMu N g h) ≤ 4 * g ^ 2 / N := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine csSup_le (simplex_nonempty.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  have hsum : ∑ i : Fin N, w (some (some i)) ≤ 1 := by
    have := hw.2
    rw [Fintype.sum_option, Fintype.sum_option] at this
    linarith [hw.1 none, hw.1 (some none)]
  obtain ⟨i, hi⟩ : ∃ i : Fin N, w (some (some i)) ≤ 1 / N := by
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    have h1 : ∑ _i : Fin N, (1 / (N : ℝ)) < ∑ i : Fin N, w (some (some i)) :=
      sum_lt_sum_of_nonempty univ_nonempty fun i _ => hcon i
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have : (N : ℝ) * (1 / N) = 1 := by field_simp
    linarith
  have hz : (some (some i) : Fan N) ∉ pairSupp N := by
    rw [mem_pairSupp]; simp
  have hle := infoRate_le_scalarObj (S := pairSupp N) le_rfl hw.1 (gapMu_interior hh hhg hg) hz
    (θ := 1 / 2) ⟨by norm_num, by norm_num⟩
  have hs0 : ∑ y ∈ pairSupp N, w y * dDown (gapMu N g h y) (1 / 2 - 0) = 0 := by
    apply sum_eq_zero
    intro y _
    rw [dDown_of_le (by linarith [gapMu_le_half (N := N) hh hhg y]), mul_zero]
  have hk0 : 0 ≤ bkl (1 / 2 - g) (1 / 2) :=
    bkl_nonneg (by linarith) (by linarith) (by norm_num) (by norm_num)
  have hk : bkl (1 / 2 - g) (1 / 2) ≤ 4 * g ^ 2 := by
    have := bkl_le_chi (p := 1 / 2 - g) (q := 1 / 2) (by linarith) (by linarith) (by norm_num)
      (by norm_num)
    have e : (1 / 2 - g - 1 / 2) ^ 2 / (1 / 2 * (1 - 1 / 2)) = 4 * g ^ 2 := by ring
    linarith
  unfold scalarObj at hle
  rw [hs0, add_zero, gapMu_r] at hle
  calc infoRate (pairSupp N) 0 w (gapMu N g h)
      ≤ w (some (some i)) * bkl (1 / 2 - g) (1 / 2) := hle
    _ ≤ 1 / N * (4 * g ^ 2) := mul_le_mul hi hk hk0 (by positivity)
    _ = 4 * g ^ 2 / N := by ring

/-- `prop:ast-gap-tradeoff`, second bound: `C_B^0(μ) ≥ h²/2`. -/
theorem gap_tradeoff_B {N : ℕ} {g h : ℝ} (hh : 0 < h) (hhg : h < g) (hg : g ≤ 1 / 4) :
    h ^ 2 / 2 ≤ charRate (fanSupp N) 0 (gapMu N g h) := by
  have key := charRate_ge_of_single_outside (fanSupp_nonempty N) (fanSupp_compl N)
    (gapMu_interior hh hhg hg) (j := none) (mem_fanSupp.2 (by simp))
    (by rw [gapMu_s, gapMu_p]; linarith)
  rw [gapMu_s, gapMu_p] at key
  have e : (1 / 2 - (1 / 2 - h)) ^ 2 / 2 = h ^ 2 / 2 := by ring
  linarith

/-! ### `prop:ast-discovery` -/

/-- Instances of `prop:ast-discovery` with `c = none`, `z = some none`, `x_i = some (some i)`:
`μ_c = 1/8`, `μ_z = 1/2`, `μ_{x_i} = 1/2 - g`, except that instance `j = some i` raises `x_i`
to `1/2 + g`.  `j = none` is the null instance. -/
noncomputable def discMu (N : ℕ) (g : ℝ) (j : Option (Fin N)) : Fan N → ℝ
  | none => 1 / 8
  | some none => 1 / 2
  | some (some i) => if j = some i then 1 / 2 + g else 1 / 2 - g

lemma discMu_c (N : ℕ) (g : ℝ) (j : Option (Fin N)) : discMu N g j none = 1 / 8 := rfl

lemma discMu_z (N : ℕ) (g : ℝ) (j : Option (Fin N)) : discMu N g j (some none) = 1 / 2 := rfl

lemma discMu_x (N : ℕ) (g : ℝ) (j : Option (Fin N)) (i : Fin N) :
    discMu N g j (some (some i)) = if j = some i then 1 / 2 + g else 1 / 2 - g := rfl

lemma discMu_null_x (N : ℕ) (g : ℝ) (i : Fin N) :
    discMu N g none (some (some i)) = 1 / 2 - g := by simp [discMu_x]

lemma discMu_self (N : ℕ) (g : ℝ) (i : Fin N) :
    discMu N g (some i) (some (some i)) = 1 / 2 + g := by simp [discMu_x]

lemma discMu_x_bounds (N : ℕ) {g : ℝ} (hg : 0 < g) (j : Option (Fin N)) (i : Fin N) :
    1 / 2 - g ≤ discMu N g j (some (some i)) ∧ discMu N g j (some (some i)) ≤ 1 / 2 + g := by
  rw [discMu_x]
  split_ifs <;> constructor <;> linarith

lemma discMu_interior {N : ℕ} {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8) (j : Option (Fin N)) :
    ∀ i, 0 < discMu N g j i ∧ discMu N g j i < 1 := by
  rintro (_ | _ | i)
  · rw [discMu_c]; constructor <;> norm_num
  · rw [discMu_z]; constructor <;> norm_num
  · have := discMu_x_bounds N hg j i
    constructor <;> linarith [this.1, this.2]

/-- `prop:ast-discovery`, instance structure: with `S_A = {c,x_1,…,x_N}` and `S_B = {c,z}`,
action `B` is the unique correct answer (at `ε = 0`) in the null instance, and `A` is the
unique correct answer in each `μ^j`. -/
theorem discovery_instances {N : ℕ} {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8) :
    (regret (pairSupp N) (pairSupp_nonempty N) (discMu N g none) = 0 ∧
      0 < regret (fanSupp N) (fanSupp_nonempty N) (discMu N g none)) ∧
    ∀ j : Fin N, regret (fanSupp N) (fanSupp_nonempty N) (discMu N g (some j)) = 0 ∧
      0 < regret (pairSupp N) (pairSupp_nonempty N) (discMu N g (some j)) := by
  refine ⟨⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · refine regret_eq_zero_of_max _ (p0 := some none) (mem_pairSupp.2 (Or.inr rfl)) ?_
    rintro (_ | _ | i)
    · rw [discMu_c, discMu_z]; norm_num
    · exact le_rfl
    · rw [discMu_null_x, discMu_z]; linarith
  · refine lt_regret_of_outside _ (c := 1 / 2 - g) (z := some none) ?_ ?_
    · rintro (_ | _ | i) hy
      · rw [discMu_c]; linarith
      · exact absurd rfl (mem_fanSupp.1 hy)
      · rw [discMu_null_x]
    · rw [discMu_z]; linarith
  · refine regret_eq_zero_of_max _ (p0 := some (some j)) (mem_fanSupp.2 (by simp)) ?_
    rw [discMu_self]
    rintro (_ | _ | i)
    · rw [discMu_c]; linarith
    · rw [discMu_z]; linarith
    · exact (discMu_x_bounds N hg (some j) i).2
  · refine lt_regret_of_outside _ (c := 1 / 2) (z := some (some j)) ?_ ?_
    · intro y hy
      rcases mem_pairSupp.1 hy with rfl | rfl
      · rw [discMu_c]; norm_num
      · rw [discMu_z]
    · rw [discMu_self]; linarith

/-- `prop:ast-discovery`, rate part: at every `μ^j` the correct action `A` has
`C_A^0(μ^j) ≥ g²/2`, independently of `N`. -/
theorem discovery_rate {N : ℕ} {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8) (j : Fin N) :
    g ^ 2 / 2 ≤ charRate (fanSupp N) 0 (discMu N g (some j)) := by
  have key := charRate_ge_of_single_outside (fanSupp_nonempty N) (fanSupp_compl N)
    (discMu_interior hg hg8 (some j)) (j := some (some j)) (mem_fanSupp.2 (by simp))
    (by rw [discMu_z, discMu_self]; linarith)
  rw [discMu_z, discMu_self] at key
  have e : (1 / 2 + g - 1 / 2) ^ 2 / 2 = g ^ 2 / 2 := by ring
  linarith

/-- A set of `D` distinct positive integers has sum at least `D(D+1)/2`. -/
lemma sum_distinct_pos_ge (A : Finset ℕ) (hA : ∀ x ∈ A, 1 ≤ x) :
    A.card * (A.card + 1) ≤ 2 * ∑ x ∈ A, x := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => hA x (mem_insert_of_mem hx)
    have ha1 : 1 ≤ a := hA a (mem_insert_self a s)
    have hsub : s ⊆ Finset.Icc 1 (a - 1) := fun x hx =>
      Finset.mem_Icc.2 ⟨hs x hx, by have := hlt x hx; omega⟩
    have hc : s.card ≤ a - 1 := by simpa using card_le_card hsub
    have ih' := ih hs
    rw [card_insert_of_notMem ha, sum_insert ha]
    have hc' : s.card + 1 ≤ a := by omega
    nlinarith

/-- Pathwise counting step of `prop:ast-discovery`.  `T j` is the index (from 1) of the first
request to `x_j`; requests made by time `τ` have distinct indices.  Then
`∑_j min(T_j, τ) ≥ (N+1) D / 2`, `D` the number of `x_j` requested by time `τ`. -/
lemma discovery_pathwise {N : ℕ} (τ : ℕ) (T : Fin N → ℕ) (hpos : ∀ j, 1 ≤ T j)
    (hinj : ∀ i j, T i ≤ τ → T i = T j → i = j) :
    (N + 1) * (univ.filter fun j => T j ≤ τ).card ≤ 2 * ∑ j, min (T j) τ := by
  obtain ⟨H, hH⟩ : ∃ H : Finset (Fin N), H = univ.filter fun j => T j ≤ τ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (univ.filter fun j => ¬ T j ≤ τ).card := ⟨_, rfl⟩
  have hDK : H.card + K = N := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin N))) (fun j => T j ≤ τ)
    rw [hH, hK]
    simpa using this
  have hinjH : Set.InjOn T H := by
    intro i hi j _ e
    have hi' : i ∈ H := hi
    rw [hH] at hi'
    exact hinj i j (mem_filter.1 hi').2 e
  have himg : (H.image T).card = H.card := card_image_of_injOn hinjH
  have h1 := sum_distinct_pos_ge (H.image T) (fun x hx => by
    obtain ⟨j, -, rfl⟩ := mem_image.1 hx
    exact hpos j)
  rw [himg, sum_image hinjH] at h1
  have hsubτ : H.image T ⊆ Finset.Icc 1 τ := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    rw [hH] at hj
    exact Finset.mem_Icc.2 ⟨hpos j, (mem_filter.1 hj).2⟩
  have hDτ : H.card ≤ τ := by
    have := card_le_card hsubτ
    rw [himg] at this
    simpa using this
  have hsplit : ∑ j, min (T j) τ = ∑ j ∈ H, T j + K * τ := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => T j ≤ τ), hH, hK]
    congr 1
    · exact sum_congr rfl fun j hj => min_eq_left (mem_filter.1 hj).2
    · rw [sum_congr rfl (fun j hj => min_eq_right (not_le.1 (mem_filter.1 hj).2).le),
        sum_const, smul_eq_mul]
  have e : (N + 1) * H.card = (H.card + K + 1) * H.card := by rw [hDK]
  rw [hsplit, ← hH, e]
  nlinarith [Nat.mul_le_mul_left K hDτ, Nat.zero_le (K * τ)]

section Discovery

open MeasureTheory

/-- **Discovery cost** (`prop:ast-discovery`, expectation bound), modular in the coupling.

`Ω` carries the coupled runs: the null run and, for each `j`, the run under `μ^j` driven by the
same controller randomization and the same tapes except that of `x_j`.  Supplied as hypotheses:
* `τ0`, `τ j`: stopping times of the null run and of the run under `μ^j`;
* `T j`: index (from 1) of the first request to `x_j` in the null run, any value `> τ0` if
  there is none by `τ0`; requests occurring by `τ0` have distinct indices (`hinj`);
* `htime`: the runs agree until the first request to `x_j`, so `τ_j ≥ min(T_j, τ0)`;
* `hans`: if `x_j` is not requested by `τ0`, both runs return the same answer
  (`true` = action `A`);
* `hcorr0`, `hcorr`: `δ`-correctness (the null run returns `A` and the `μ^j` run returns `B`
  with probability at most `δ`; these are the incorrect answers by `discovery_instances`).
Conclusion: some instance has `E_{μ^j} τ ≥ (N+1)/2 · (1-2δ)`. -/
theorem discovery_cost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (hN : 0 < N) {δ : ℝ}
    (τ0 : Ω → ℕ) (T τ : Fin N → Ω → ℕ) (ans0 : Ω → Bool) (ans : Fin N → Ω → Bool)
    (hτ0 : Measurable τ0) (hT : ∀ j, Measurable (T j))
    (hτint : ∀ j, Integrable (fun ω => (τ j ω : ℝ)) P)
    (hpos : ∀ j ω, 1 ≤ T j ω)
    (hinj : ∀ ω i j, T i ω ≤ τ0 ω → T i ω = T j ω → i = j)
    (htime : ∀ j ω, min (T j ω) (τ0 ω) ≤ τ j ω)
    (hans : ∀ j ω, τ0 ω < T j ω → ans j ω = ans0 ω)
    (hcorr0 : P.real {ω | ans0 ω = true} ≤ δ)
    (hcorr : ∀ j, P.real {ω | ans j ω = false} ≤ δ) :
    ∃ j, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) ≤ ∫ ω, (τ j ω : ℝ) ∂P := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let H : Fin N → Set Ω := fun j => {ω | T j ω ≤ τ0 ω}
  have hHm : ∀ j, MeasurableSet (H j) := fun j => measurableSet_le (hT j) hτ0
  have hHp : ∀ j, 1 - 2 * δ ≤ P.real (H j) := by
    intro j
    have hsub : (H j)ᶜ ⊆ {ω | ans0 ω = true} ∪ {ω | ans j ω = false} := by
      intro ω hω
      have hlt : τ0 ω < T j ω := not_le.1 hω
      have he := hans j ω hlt
      by_cases h0 : ans0 ω = true
      · exact Or.inl h0
      · right
        show ans j ω = false
        rw [he]
        simpa using h0
    have h1 : P.real (H j)ᶜ ≤ δ + δ :=
      (measureReal_mono hsub).trans
        ((measureReal_union_le _ _).trans (add_le_add hcorr0 (hcorr j)))
    rw [probReal_compl_eq_one_sub (hHm j)] at h1
    linarith
  have hpath : ∀ ω, ((N : ℝ) + 1) / 2 * ∑ j, (H j).indicator (fun _ => (1 : ℝ)) ω
      ≤ ∑ j, (τ j ω : ℝ) := by
    intro ω
    have h1 := discovery_pathwise (τ0 ω) (fun j => T j ω) (fun j => hpos j ω) (hinj ω)
    have h2 : ∑ j, min (T j ω) (τ0 ω) ≤ ∑ j, τ j ω := sum_le_sum fun j _ => htime j ω
    have h3 : (∑ j, (H j).indicator (fun _ => (1 : ℝ)) ω)
        = ((univ.filter fun j => T j ω ≤ τ0 ω).card : ℝ) := by
      rw [card_filter]
      push_cast
      exact sum_congr rfl fun j _ => by simp [H, Set.indicator_apply]
    rw [h3]
    have h4 : (((N : ℝ) + 1) * ((univ.filter fun j => T j ω ≤ τ0 ω).card : ℝ))
        ≤ 2 * ∑ j, (τ j ω : ℝ) := by
      exact_mod_cast h1.trans (Nat.mul_le_mul_left 2 h2)
    linarith
  have hind_int : ∀ j ∈ (univ : Finset (Fin N)),
      Integrable (fun ω => (H j).indicator (fun _ => (1 : ℝ)) ω) P :=
    fun j _ => (integrable_const (1 : ℝ)).indicator (hHm j)
  have hint1 : Integrable
      (fun ω => ((N : ℝ) + 1) / 2 * ∑ j, (H j).indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_finsetSum _ hind_int).const_mul _
  have hint2 : Integrable (fun ω => ∑ j, (τ j ω : ℝ)) P :=
    integrable_finsetSum _ fun j _ => hτint j
  have hmono := integral_mono hint1 hint2 hpath
  rw [integral_const_mul, integral_finsetSum _ hind_int,
    integral_finsetSum _ (fun j _ => hτint j)] at hmono
  have hind : ∀ j, ∫ ω, (H j).indicator (fun _ => (1 : ℝ)) ω ∂P = P.real (H j) := fun j => by
    rw [integral_indicator_const _ (hHm j), smul_eq_mul, mul_one]
  simp only [hind] at hmono
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have h5 : ∑ j : Fin N, ∫ ω, (τ j ω : ℝ) ∂P
      < ∑ _j : Fin N, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) :=
    sum_lt_sum_of_nonempty univ_nonempty fun j _ => hcon j
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h5
  have h6 : (N : ℝ) * (1 - 2 * δ) ≤ ∑ j : Fin N, P.real (H j) := by
    have := sum_le_sum (s := (univ : Finset (Fin N))) fun j _ => hHp j
    rwa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  nlinarith [mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1) / 2)]

end Discovery

/-! ### Convexity and the unique interior minimizer of the scalar objective -/

/-- `kl(p,·)` is convex on `(0,1)`. -/
lemma bkl_convex_comb {p x y a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    bkl p (a * x + b * y) ≤ a * bkl p x + b * bkl p y := by
  have hm : a * x + b * y ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using (convex_Ioo (0 : ℝ) 1) hx hy ha hb hab
  have L1 : a * log x + b * log y ≤ log (a * x + b * y) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx.1) (Set.mem_Ioi.2 hy.1)
      ha hb hab
    simpa only [smul_eq_mul] using this
  have L2 : a * log (1 - x) + b * log (1 - y) ≤ log (1 - (a * x + b * y)) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (sub_pos.2 hx.2))
      (Set.mem_Ioi.2 (sub_pos.2 hy.2)) ha hb hab
    simp only [smul_eq_mul] at this
    have e : a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) := by linear_combination hab
    rwa [e] at this
  rw [bkl_eq p hm.1 hm.2, bkl_eq p hx.1 hx.2, bkl_eq p hy.1 hy.2]
  have h1 := mul_le_mul_of_nonneg_left L1 hp0
  have h2 := mul_le_mul_of_nonneg_left L2 (sub_nonneg.2 hp1)
  have hC : p * log p + (1 - p) * log (1 - p)
      = a * (p * log p + (1 - p) * log (1 - p)) + b * (p * log p + (1 - p) * log (1 - p)) := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- `kl(p,·)` is strictly convex on `(0,1)` for `p > 0`. -/
lemma bkl_strict_convex_comb {p x y a b : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hxy : x ≠ y) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) :
    bkl p (a * x + b * y) < a * bkl p x + b * bkl p y := by
  have hm : a * x + b * y ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using (convex_Ioo (0 : ℝ) 1) hx hy ha.le hb.le hab
  have L1 : a * log x + b * log y < log (a * x + b * y) := by
    have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 hx.1) (Set.mem_Ioi.2 hy.1) hxy ha hb hab
    simpa only [smul_eq_mul] using this
  have L2 : a * log (1 - x) + b * log (1 - y) ≤ log (1 - (a * x + b * y)) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (sub_pos.2 hx.2))
      (Set.mem_Ioi.2 (sub_pos.2 hy.2)) ha.le hb.le hab
    simp only [smul_eq_mul] at this
    have e : a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) := by linear_combination hab
    rwa [e] at this
  rw [bkl_eq p hm.1 hm.2, bkl_eq p hx.1 hx.2, bkl_eq p hy.1 hy.2]
  have h1 := mul_lt_mul_of_pos_left L1 hp0
  have h2 := mul_le_mul_of_nonneg_left L2 (sub_nonneg.2 hp1)
  have hC : p * log p + (1 - p) * log (1 - p)
      = a * (p * log p + (1 - p) * log (1 - p)) + b * (p * log p + (1 - p) * log (1 - p)) := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- The clipped divergence `d_↓(p,·)` is convex on `(0,1)`. -/
lemma dDown_convex_comb {p x y a b : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : dDown p (a * x + b * y) ≤ a * dDown p x + b * dDown p y := by
  have hm : a * x + b * y ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using (convex_Ioo (0 : ℝ) 1) hx hy ha hb hab
  rw [← bkl_min_eq_dDown p (a * x + b * y), ← bkl_min_eq_dDown p x, ← bkl_min_eq_dDown p y]
  have hx' : min p x ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_min hp0 hx.1, (min_le_right _ _).trans_lt hx.2⟩
  have hy' : min p y ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_min hp0 hy.1, (min_le_right _ _).trans_lt hy.2⟩
  have hm' : a * min p x + b * min p y ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using (convex_Ioo (0 : ℝ) 1) hx' hy' ha hb hab
  have hd : min p (a * x + b * y) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_min hp0 hm.1, (min_le_right _ _).trans_lt hm.2⟩
  have hle : a * min p x + b * min p y ≤ min p (a * x + b * y) := by
    refine le_min ?_ ?_
    · calc a * min p x + b * min p y ≤ a * p + b * p :=
            add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
              (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)
        _ = p := by rw [← add_mul, hab, one_mul]
    · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) ha)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
  have h1 : bkl p (min p (a * x + b * y)) ≤ bkl p (a * min p x + b * min p y) :=
    bkl_mono_right hp0.le hp1 hd.1 hd.2 hm'.1 hm'.2
      (mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 (min_le_left _ _)))
  exact h1.trans (bkl_convex_comb hp0.le hp1 hx' hy' ha hb hab)

lemma sum_dDown_convex_comb {S : Finset Z} {ε : ℝ} {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {x y a b : ℝ} (hx : x ∈ Set.Ioo ε 1) (hy : y ∈ Set.Ioo ε 1)
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∑ i ∈ S, v i * dDown (μ i) (a * x + b * y - ε)
      ≤ a * ∑ i ∈ S, v i * dDown (μ i) (x - ε) + b * ∑ i ∈ S, v i * dDown (μ i) (y - ε) := by
  have hxε : x - ε ∈ Set.Ioo (0 : ℝ) 1 := ⟨sub_pos.2 hx.1, by linarith [hx.2]⟩
  have hyε : y - ε ∈ Set.Ioo (0 : ℝ) 1 := ⟨sub_pos.2 hy.1, by linarith [hy.2]⟩
  have e : a * x + b * y - ε = a * (x - ε) + b * (y - ε) := by linear_combination ε * hab
  rw [e, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have := mul_le_mul_of_nonneg_left
    (dDown_convex_comb (hμ i).1 (hμ i).2.le hxε hyε ha hb hab) (hv i)
  linarith

/-- `thm:active-kl-projection`: each scalar objective is convex on `(ε,1)`. -/
theorem scalarObj_convexOn {S : Finset Z} {ε : ℝ} (hε : 0 ≤ ε) {v μ : Z → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 < μ i ∧ μ i < 1) (z : Z) :
    ConvexOn ℝ (Set.Ioo ε 1) (scalarObj S ε v μ z) := by
  refine ⟨convex_Ioo ε 1, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hx0 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε.trans_lt hx.1, hx.2⟩
  have hy0 : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε.trans_lt hy.1, hy.2⟩
  have h1 := mul_le_mul_of_nonneg_left
    (bkl_convex_comb (hμ z).1.le (hμ z).2.le hx0 hy0 ha hb hab) (hv z)
  have h2 := sum_dDown_convex_comb (S := S) hv hμ hx hy hε ha hb hab
  unfold scalarObj
  linarith

/-- `thm:active-kl-projection`: a positive outside weight makes the scalar objective strictly
convex. -/
theorem scalarObj_strictConvexOn {S : Finset Z} {ε : ℝ} (hε : 0 ≤ ε) {v μ : Z → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {z : Z} (hvz : 0 < v z) :
    StrictConvexOn ℝ (Set.Ioo ε 1) (scalarObj S ε v μ z) := by
  refine ⟨convex_Ioo ε 1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hx0 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε.trans_lt hx.1, hx.2⟩
  have hy0 : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε.trans_lt hy.1, hy.2⟩
  have h1 := mul_lt_mul_of_pos_left
    (bkl_strict_convex_comb (hμ z).1 (hμ z).2.le hx0 hy0 hxy ha hb hab) hvz
  have h2 := sum_dDown_convex_comb (S := S) hv hμ hx hy hε ha.le hb.le hab
  unfold scalarObj
  linarith

lemma neg_log_two_le_entropy (p : ℝ) : -log 2 ≤ p * log p + (1 - p) * log (1 - p) := by
  have := binEntropy_le_log_two (p := p)
  simp only [binEntropy, log_inv] at this
  linarith

lemma bkl_ge_right {p θ : ℝ} (hp0 : 0 ≤ p) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    -log 2 - (1 - p) * log (1 - θ) ≤ bkl p θ := by
  rw [bkl_eq p hθ0 hθ1]
  have h1 := neg_log_two_le_entropy p
  have h2 : p * log θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 (log_nonpos hθ0.le hθ1.le)
  linarith

lemma bkl_ge_left {p θ : ℝ} (hp1 : p ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    -log 2 - p * log θ ≤ bkl p θ := by
  rw [bkl_eq p hθ0 hθ1]
  have h1 := neg_log_two_le_entropy p
  have h2 : (1 - p) * log (1 - θ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hp1) (log_nonpos (by linarith) (by linarith))
  linarith

/-- `thm:active-kl-projection`: if the outside weight and the total inside weight are
positive, the scalar objective attains its infimum over `(ε,1)` at an interior point
(it diverges at both ends). -/
theorem scalarObj_exists_isMinOn {S : Finset Z} (hS : S.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {z : Z}
    (hvz : 0 < v z) (hin : 0 < ∑ y ∈ S, v y) :
    ∃ θ ∈ Set.Ioo ε 1, IsMinOn (scalarObj S ε v μ z) (Set.Ioo ε 1) θ := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hθ0 : (ε + 1) / 2 ∈ Set.Ioo ε 1 := ⟨by linarith, by linarith⟩
  obtain ⟨B, hB⟩ : ∃ B, B = scalarObj S ε v μ z ((ε + 1) / 2) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact scalarObj_nonneg hε0 hv hμ' hθ0
  -- divergence at the upper end
  have hp1 : 0 < 1 - μ z := sub_pos.2 (hμ z).2
  obtain ⟨t1, ht1⟩ : ∃ t1, t1 = exp (-(B / v z + log 2 + 1) / (1 - μ z)) := ⟨_, rfl⟩
  have ht1pos : 0 < t1 := by rw [ht1]; exact exp_pos _
  have hup : ∀ θ ∈ Set.Ioo ε 1, 1 - θ < t1 → B < scalarObj S ε v μ z θ := by
    intro θ hθ hlt
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε0.trans_lt hθ.1, hθ.2⟩
    rw [ht1] at hlt
    have h1 : log (1 - θ) < -(B / v z + log 2 + 1) / (1 - μ z) :=
      (Real.log_lt_iff_lt_exp (sub_pos.2 hθ.2)).2 hlt
    have h2 : (1 - μ z) * log (1 - θ) < -(B / v z + log 2 + 1) := by
      have := mul_lt_mul_of_pos_left h1 hp1
      have e : (1 - μ z) * (-(B / v z + log 2 + 1) / (1 - μ z)) = -(B / v z + log 2 + 1) := by
        field_simp
      linarith
    have h3 := bkl_ge_right (θ := θ) (hμ' z).1 hθ'.1 hθ'.2
    have h4 : B / v z + 1 < bkl (μ z) θ := by linarith
    have h5 : B + v z < v z * bkl (μ z) θ := by
      have := mul_lt_mul_of_pos_left h4 hvz
      have e : v z * (B / v z + 1) = B + v z := by field_simp
      linarith
    have h6 : 0 ≤ ∑ y ∈ S, v y * dDown (μ y) (θ - ε) := sum_nonneg fun y _ =>
      mul_nonneg (hv y) (dDown_nonneg (hμ' y).1 (hμ' y).2 (sub_pos.2 hθ.1) (by linarith [hθ.2]))
    show B < v z * bkl (μ z) θ + ∑ y ∈ S, v y * dDown (μ y) (θ - ε)
    linarith
  -- divergence at the lower end
  obtain ⟨m, hm⟩ : ∃ m, m = S.inf' hS μ := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact (lt_inf'_iff hS).2 fun y _ => (hμ y).1
  have hmle : ∀ y ∈ S, m ≤ μ y := fun y hy => by rw [hm]; exact inf'_le μ hy
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ y ∈ S, v y := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hW]; exact hin
  obtain ⟨t0, ht0⟩ : ∃ t0, t0 = exp (-(B / W + log 2 + 1) / m) := ⟨_, rfl⟩
  have ht0pos : 0 < t0 := by rw [ht0]; exact exp_pos _
  have hlow : ∀ θ ∈ Set.Ioo ε 1, θ - ε < min t0 m → B < scalarObj S ε v μ z θ := by
    intro θ hθ hlt
    have hc0 : 0 < θ - ε := sub_pos.2 hθ.1
    have hct : θ - ε < t0 := hlt.trans_le (min_le_left _ _)
    have hcm : θ - ε < m := hlt.trans_le (min_le_right _ _)
    have hc1 : θ - ε < 1 := by linarith [hθ.2]
    rw [ht0] at hct
    have h1 : log (θ - ε) < -(B / W + log 2 + 1) / m := (Real.log_lt_iff_lt_exp hc0).2 hct
    have h2 : m * log (θ - ε) < -(B / W + log 2 + 1) := by
      have := mul_lt_mul_of_pos_left h1 hm0
      have e : m * (-(B / W + log 2 + 1) / m) = -(B / W + log 2 + 1) := by field_simp
      linarith
    have hlogneg : log (θ - ε) ≤ 0 := log_nonpos hc0.le hc1.le
    have hterm : ∀ y ∈ S, v y * (B / W + 1) ≤ v y * dDown (μ y) (θ - ε) := by
      intro y hy
      refine mul_le_mul_of_nonneg_left ?_ (hv y)
      rw [dDown_of_lt (hcm.trans_le (hmle y hy))]
      have h3 := bkl_ge_left (θ := θ - ε) (hμ' y).2 hc0 hc1
      have h4 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hmle y hy)) hlogneg
      linarith
    have hsum : W * (B / W + 1) ≤ ∑ y ∈ S, v y * dDown (μ y) (θ - ε) := by
      rw [hW, sum_mul, ← hW]
      exact sum_le_sum hterm
    have e : W * (B / W + 1) = B + W := by field_simp
    have h5 : 0 ≤ v z * bkl (μ z) θ :=
      mul_nonneg hvz.le (bkl_nonneg (hμ' z).1 (hμ' z).2 (hε0.trans_lt hθ.1) hθ.2)
    show B < v z * bkl (μ z) θ + ∑ y ∈ S, v y * dDown (μ y) (θ - ε)
    linarith
  -- minimize on a compact subinterval
  obtain ⟨α, hα⟩ : ∃ α, α = min ((ε + 1) / 2) (ε + min t0 m) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = max ((ε + 1) / 2) (1 - t1) := ⟨_, rfl⟩
  have hαε : ε < α := by
    rw [hα]
    exact lt_min hθ0.1 (by linarith [lt_min ht0pos hm0])
  have hβ1 : β < 1 := by
    rw [hβ]
    exact max_lt hθ0.2 (by linarith)
  have hαθ : α ≤ (ε + 1) / 2 := by rw [hα]; exact min_le_left _ _
  have hα2 : α ≤ ε + min t0 m := by rw [hα]; exact min_le_right _ _
  have hθβ : (ε + 1) / 2 ≤ β := by rw [hβ]; exact le_max_left _ _
  have hβ2 : 1 - t1 ≤ β := by rw [hβ]; exact le_max_right _ _
  have hsub : Set.Icc α β ⊆ Set.Ioo ε 1 := fun x hx =>
    ⟨hαε.trans_le hx.1, hx.2.trans_lt hβ1⟩
  have hcont : ContinuousOn (scalarObj S ε v μ z) (Set.Icc α β) :=
    ((scalarObj_convexOn hε0 hv hμ z).continuousOn isOpen_Ioo).mono hsub
  obtain ⟨θs, hθs, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨(ε + 1) / 2, hαθ, hθβ⟩ hcont
  have hsB : scalarObj S ε v μ z θs ≤ B := by
    rw [hB]
    exact isMinOn_iff.1 hmin _ ⟨hαθ, hθβ⟩
  refine ⟨θs, hsub hθs, isMinOn_iff.2 fun θ hθ => ?_⟩
  by_cases h1 : θ < α
  · exact hsB.trans (hlow θ hθ (by linarith)).le
  · by_cases h2 : β < θ
    · exact hsB.trans (hup θ hθ (by linarith)).le
    · exact isMinOn_iff.1 hmin _ ⟨not_lt.1 h1, not_lt.1 h2⟩

/-- `thm:active-kl-projection`: under positive outside weight and positive total inside
weight the scalar objective has exactly one minimizer in `(ε,1)`. -/
theorem scalarObj_existsUnique_isMinOn {S : Finset Z} (hS : S.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {v μ : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {z : Z}
    (hvz : 0 < v z) (hin : 0 < ∑ y ∈ S, v y) :
    ∃! θ, θ ∈ Set.Ioo ε 1 ∧ IsMinOn (scalarObj S ε v μ z) (Set.Ioo ε 1) θ := by
  obtain ⟨θ, hθ, hmin⟩ := scalarObj_exists_isMinOn hS hε0 hε1 hv hμ hvz hin
  refine ⟨θ, ⟨hθ, hmin⟩, fun θ' h' => ?_⟩
  exact (scalarObj_strictConvexOn hε0 hv hμ hvz).eq_of_isMinOn h'.2 hmin h'.1 hθ

/-! ### Deterministic steps of the anytime pair certificate (`app:ast-pair-certificate`) -/

/-- If the true pair is an alternative (`μ_z > μ_j + ε`), the pair statistic is at most the
exponent of the likelihood-ratio lower bound:
`F_ε(m,q;s,t) ≤ s kl(m, μ_j) + t kl(q, μ_z)` for empirical means `m, q ∈ [0,1]`. -/
theorem pairF_le_of_alt {ε m q s t μj μz : ℝ} (hε : 0 ≤ ε) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t) (hμj : 0 < μj) (hμz : μz < 1)
    (halt : μj + ε < μz) : pairF ε m q s t ≤ s * bkl m μj + t * bkl q μz := by
  have hθ : μz ∈ Set.Ioo ε 1 := ⟨by linarith, hμz⟩
  have hbdd : BddBelow ((fun θ => s * dDown m (θ - ε) + t * bkl q θ) '' Set.Ioo ε 1) :=
    ⟨0, by
      rintro _ ⟨θ, hθ', rfl⟩
      exact add_nonneg
        (mul_nonneg hs (dDown_nonneg hm0 hm1 (sub_pos.2 hθ'.1) (by linarith [hθ'.2])))
        (mul_nonneg ht (bkl_nonneg hq0 hq1 (hε.trans_lt hθ'.1) hθ'.2))⟩
  refine (csInf_le hbdd ⟨μz, hθ, rfl⟩).trans ?_
  have h1 : dDown m (μz - ε) ≤ bkl m μj :=
    dDown_le_bkl hm0 hm1 hμj (by linarith) (by linarith)
  exact add_le_add (mul_le_mul_of_nonneg_left h1 hs) le_rfl

/-- `C(n,k) p^k (1-p)^{n-k} ≤ 1` (used with `p = k/n` in the mixture-martingale bound). -/
lemma choose_mul_pow_le_one {n k : ℕ} (hk : k ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ 1 := by
  have h := add_pow p (1 - p) n
  rw [add_sub_cancel, one_pow] at h
  have hterm : p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ)
      ≤ ∑ m ∈ range (n + 1), p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ) :=
    single_le_sum (f := fun m => p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ))
      (fun m _ => mul_nonneg (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.2 hp1) _))
        (Nat.cast_nonneg _)) (mem_range.2 (Nat.lt_succ_of_le hk))
  rw [← h] at hterm
  linarith

/-! ### Change of measure (`lem:active-com`) -/

lemma bkl_compl (p q : ℝ) : bkl (1 - p) (1 - q) = bkl p q := by
  simp [bkl, add_comm]

/-- Real-variable core of the binary data-processing inequality: a two-point
Donsker--Varadhan bound for all `(a,b)` implies the bound by `kl(p,q)`. -/
lemma bkl_le_of_two_point {p q KL : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hpq0 : 0 < p → 0 < q) (hpq1 : p < 1 → q < 1)
    (h : ∀ a b : ℝ, a * p + b * (1 - p) - log (exp a * q + exp b * (1 - q)) ≤ KL) :
    bkl p q ≤ KL := by
  rcases hp0.eq_or_lt with h0 | h0
  · subst h0
    have hq1' : q < 1 := hpq1 zero_lt_one
    have hb : bkl 0 q = log (1 / (1 - q)) := by simp [bkl]
    rw [hb]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have key := h (log η) (log (1 / (1 - q)))
    rw [exp_log hη, exp_log (one_div_pos.2 (sub_pos.2 hq1')),
      one_div_mul_cancel (sub_pos.2 hq1').ne'] at key
    have h3 : 0 ≤ η * q := mul_nonneg hη.le hq0
    have h4 := log_le_sub_one_of_pos (by linarith : 0 < η * q + 1)
    have h5 : η * q ≤ η := mul_le_of_le_one_right hη.le hq1
    linarith
  rcases hp1.eq_or_lt with h1 | h1
  · subst h1
    have hq0' : 0 < q := hpq0 one_pos
    have hb : bkl 1 q = log (1 / q) := by simp [bkl]
    rw [hb]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have key := h (log (1 / q)) (log η)
    rw [exp_log (one_div_pos.2 hq0'), exp_log hη, one_div_mul_cancel hq0'.ne'] at key
    have h3 : 0 ≤ η * (1 - q) := mul_nonneg hη.le (sub_nonneg.2 hq1)
    have h4 := log_le_sub_one_of_pos (by linarith : 0 < 1 + η * (1 - q))
    have h5 : η * (1 - q) ≤ η := mul_le_of_le_one_right hη.le (by linarith)
    linarith
  · have hq0' := hpq0 h0
    have hq1' := hpq1 h1
    have key := h (log (p / q)) (log ((1 - p) / (1 - q)))
    rw [exp_log (div_pos h0 hq0'), exp_log (div_pos (sub_pos.2 h1) (sub_pos.2 hq1'))] at key
    have e : p / q * q + (1 - p) / (1 - q) * (1 - q) = 1 := by
      rw [div_mul_cancel₀ _ hq0'.ne', div_mul_cancel₀ _ (sub_pos.2 hq1').ne']
      ring
    rw [e, log_one] at key
    unfold bkl
    linarith

section ChangeOfMeasure

open MeasureTheory InformationTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two-valued test function: `a` on `E`, `b` on `Eᶜ`. -/
noncomputable def twoPt (E : Set Ω) (a b : ℝ) : Ω → ℝ :=
  fun ω => E.indicator (fun _ => a) ω + Eᶜ.indicator (fun _ => b) ω

lemma integrable_twoPt (R : Measure Ω) [IsFiniteMeasure R] {E : Set Ω} (hE : MeasurableSet E)
    (a b : ℝ) : Integrable (twoPt E a b) R :=
  ((integrable_const a).indicator hE).add ((integrable_const b).indicator hE.compl)

lemma integral_twoPt (R : Measure Ω) [IsProbabilityMeasure R] {E : Set Ω}
    (hE : MeasurableSet E) (a b : ℝ) :
    ∫ ω, twoPt E a b ω ∂R = a * R.real E + b * (1 - R.real E) := by
  unfold twoPt
  rw [integral_add ((integrable_const a).indicator hE) ((integrable_const b).indicator hE.compl),
    integral_indicator_const _ hE, integral_indicator_const _ hE.compl,
    probReal_compl_eq_one_sub hE]
  simp only [smul_eq_mul]
  ring

lemma exp_twoPt (E : Set Ω) (a b : ℝ) :
    (fun ω => exp (twoPt E a b ω)) = twoPt E (exp a) (exp b) := by
  funext ω
  by_cases hω : ω ∈ E <;> simp [twoPt, hω]

/-- Donsker--Varadhan lower bound for a two-valued test function. -/
lemma two_point_dv (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hint : Integrable (llr P Q) P) {E : Set Ω} (hE : MeasurableSet E)
    (a b : ℝ) :
    a * P.real E + b * (1 - P.real E) - log (exp a * Q.real E + exp b * (1 - Q.real E))
      ≤ ∫ ω, llr P Q ω ∂P := by
  have hfP : Integrable (twoPt E a b) P := integrable_twoPt P hE a b
  have hfQ : Integrable (fun ω => exp (twoPt E a b ω)) Q := by
    rw [exp_twoPt]
    exact integrable_twoPt Q hE _ _
  have hprob : IsProbabilityMeasure (Q.tilted (twoPt E a b)) := isProbabilityMeasure_tilted hfQ
  have hac : P ≪ Q.tilted (twoPt E a b) := hPQ.trans (absolutelyContinuous_tilted hfQ)
  have hnn := integral_llr_add_sub_measure_univ_nonneg hac
    (integrable_llr_tilted_right hPQ hfP hint hfQ)
  rw [integral_llr_tilted_right hPQ hfP hfQ hint, exp_twoPt, integral_twoPt Q hE,
    integral_twoPt P hE] at hnn
  simp only [probReal_univ] at hnn
  linarith

/-- **Binary data processing**: for probability measures `P ≪ Q` with integrable
log-likelihood ratio and any measurable event `E`,
`kl(P(E), Q(E)) ≤ ∫ log(dP/dQ) dP = KL(P‖Q)`. -/
theorem bkl_le_integral_llr (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hint : Integrable (llr P Q) P) {E : Set Ω}
    (hE : MeasurableSet E) : bkl (P.real E) (Q.real E) ≤ ∫ ω, llr P Q ω ∂P := by
  refine bkl_le_of_two_point measureReal_nonneg measureReal_le_one measureReal_nonneg
    measureReal_le_one ?_ ?_ (two_point_dv P Q hPQ hint hE)
  · intro hp
    by_contra hq
    have hq0 : Q.real E = 0 := le_antisymm (not_lt.1 hq) measureReal_nonneg
    have h1 : Q E = 0 := (measureReal_eq_zero_iff (measure_ne_top Q E)).1 hq0
    have h2 : P.real E = 0 := by simp [Measure.real, hPQ h1]
    linarith
  · intro hp
    by_contra hq
    have hq1 : Q.real Eᶜ = 0 := by
      rw [probReal_compl_eq_one_sub hE]
      linarith [not_lt.1 hq, measureReal_le_one (μ := Q) (s := E)]
    have h1 : Q Eᶜ = 0 := (measureReal_eq_zero_iff (measure_ne_top Q Eᶜ)).1 hq1
    have h2 : P.real Eᶜ = 0 := by simp [Measure.real, hPQ h1]
    rw [probReal_compl_eq_one_sub hE] at h2
    linarith

/-- **Stopped Bernoulli change of measure** (`lem:active-com`), modular form.
`P` and `Q` are the laws of the stopped history under the mean vectors `μ` and `lam`, and
`EN z` stands for `E_μ[N_z(τ)]`.  The hypothesis `hwald` is the expected stopped
log-likelihood-ratio identity `E_μ[log dP/dQ] = ∑_z E_μ[N_z(τ)] kl(μ_z, λ_z)` (the Wald-type
step of the manuscript's proof, which is NOT proved here); the conclusion is the stated
inequality for every event measurable at stopping. -/
theorem stopped_change_of_measure (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hint : Integrable (llr P Q) P)
    (EN μ lam : Z → ℝ) (hwald : ∫ ω, llr P Q ω ∂P = ∑ z, EN z * bkl (μ z) (lam z))
    {E : Set Ω} (hE : MeasurableSet E) :
    bkl (P.real E) (Q.real E) ≤ ∑ z, EN z * bkl (μ z) (lam z) := by
  rw [← hwald]
  exact bkl_le_integral_llr P Q hPQ hint hE

end ChangeOfMeasure

/-- **Fixed-answer transportation bound** (deterministic core of the lower-bound argument).
If the expected counts `EN ≥ 0` satisfy `K ≤ ∑_z EN_z kl(μ_z,λ_z)` for every alternative
`λ ∈ Alt_ε(a)` (as `lem:active-com` gives with `K = kl(P_μ(â=a), P_λ(â=a))`), then
`K ≤ E_μ[τ] · C_a^ε(μ)`, where `E_μ[τ] = ∑_z EN_z`.  The multiple-answer asymptotic bound
`eq:ast-lower-main` is not derived here. -/
theorem transport_lower_bound {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) {EN : Z → ℝ}
    (hEN : ∀ z, 0 ≤ EN z) {K : ℝ} (htrans : ∀ lam ∈ Alt S ε, K ≤ infoCost EN μ lam) :
    K ≤ (∑ z, EN z) * charRate S ε μ := by
  have h1 : K ≤ infoRate S ε EN μ := by
    refine le_csInf ((alt_nonempty hSc hε0 hε1).image _) ?_
    rintro _ ⟨lam, hlam, rfl⟩
    exact htrans lam hlam
  have hT0 : 0 ≤ ∑ z, EN z := sum_nonneg fun z _ => hEN z
  rcases hT0.eq_or_lt with hT | hT
  · have hz : ∀ z, EN z = 0 := fun z =>
      (sum_eq_zero_iff_of_nonneg fun z _ => hEN z).1 hT.symm z (mem_univ z)
    obtain ⟨lam, hlam⟩ := alt_nonempty (S := S) hSc hε0 hε1
    have h2 := htrans lam hlam
    have h3 : infoCost EN μ lam = 0 := by simp [infoCost, hz]
    rw [← hT, zero_mul]
    linarith
  · have hw : (fun i => EN i / ∑ z, EN z) ∈ simplex Z :=
      ⟨fun i => div_nonneg (hEN i) hT0, by rw [← sum_div, div_self hT.ne']⟩
    have h2 := le_charRate (S := S) hSc hε0 hε1 hμ hw
    have h3 := infoRate_smul S ε (fun i => EN i / ∑ z, EN z) μ hT0
    have e : (fun i => (∑ z, EN z) * (EN i / ∑ z, EN z)) = EN := by
      funext i
      field_simp
    rw [e] at h3
    rw [h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hT0)

/-! ### Non-containment tied-star lower bound (`thm:active-star-lb`) -/

/-- Support `S_{B_i} = {p, r_i}` of the star family (`p = none`, `r_i = some (some i)`);
`S_A = {p, q}` is `pairSupp N` (`q = some none`). -/
def starB (N : ℕ) (i : Fin N) : Finset (Fan N) := {none, some (some i)}

lemma starB_nonempty (N : ℕ) (i : Fin N) : (starB N i).Nonempty := ⟨none, by simp [starB]⟩

/-- Means of the tied star: `μ_p = μ_q = 1/2`, `μ_{r_i} = 1/2 - g`. -/
noncomputable def starMu (N : ℕ) (g : ℝ) : Fan N → ℝ
  | none => 1 / 2
  | some none => 1 / 2
  | some (some _) => 1 / 2 - g

lemma starMu_p (N : ℕ) (g : ℝ) : starMu N g none = 1 / 2 := rfl

lemma starMu_q (N : ℕ) (g : ℝ) : starMu N g (some none) = 1 / 2 := rfl

lemma starMu_r (N : ℕ) (g : ℝ) (i : Fin N) : starMu N g (some (some i)) = 1 / 2 - g := rfl

lemma starMu_interior {N : ℕ} {g : ℝ} (hg0 : 0 < g) (hg : g ≤ 1 / 4) :
    ∀ i, 0 < starMu N g i ∧ starMu N g i < 1 := by
  rintro (_ | _ | i)
  · rw [starMu_p]; constructor <;> norm_num
  · rw [starMu_q]; constructor <;> norm_num
  · rw [starMu_r]; constructor <;> linarith

lemma starMu_le_half {N : ℕ} {g : ℝ} (hg0 : 0 < g) : ∀ i, starMu N g i ≤ 1 / 2 := by
  rintro (_ | _ | i)
  · rw [starMu_p]
  · rw [starMu_q]
  · rw [starMu_r]; linarith

/-- Changing one coordinate of the truth costs only that coordinate's term. -/
lemma infoCost_update (v μ : Z → ℝ) (z0 : Z) (x : ℝ) :
    infoCost v μ (Function.update μ z0 x) = v z0 * bkl (μ z0) x := by
  unfold infoCost
  rw [sum_eq_single z0]
  · rw [Function.update_self]
  · intro i _ hi
    rw [Function.update_of_ne hi, bkl_self, mul_zero]
  · intro h
    exact absurd (mem_univ z0) h

/-- If an event has probability at least `1/2` under the truth and at most `δ ≤ 1/2` (but
positive) under the alternative, the binary divergence is at least `kl(1/2, δ)`. -/
lemma bkl_half_le {p x δ : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hx0 : 0 < x) (hxδ : x ≤ δ)
    (hδ : δ ≤ 1 / 2) : bkl (1 / 2) δ ≤ bkl p x := by
  have hδ0 : 0 < δ := hx0.trans_le hxδ
  have h1 : bkl (1 / 2) δ ≤ bkl p δ := bkl_mono_left hδ0 hδ (by norm_num) hp hp1
  have h2 : bkl p δ ≤ bkl p x :=
    bkl_mono_right (by linarith) hp1 hδ0 (by linarith) hx0 (by linarith)
      (mul_nonneg (sub_nonneg.2 hxδ) (by linarith))
  exact h1.trans h2

/-- **Non-containment tied-star lower bound** (`thm:active-star-lb`, `eq:active-star-bound`),
modular in the change of measure, for finite expected stopping time.

The algorithm enters only through: `EN z = E_μ[N_z(τ)]` (so `∑_z EN z = E_μ[τ]`) and
`PA lam = P_lam(â = A)`; by almost-sure halting `1 - PA lam = P_lam(â ∈ {B_1,…,B_N})`.
Hypotheses supplied by the manuscript:
* `hcorrA`, `hcorrB`: `(ε,δ)`-correctness at every interior parameter;
* `htrans`: `lem:active-com` for the event `{â = A}` (the complementary event gives the same
  inequality since `kl(1-p,1-q) = kl(p,q)`);
* `hac`: the stopped laws at interior parameters are mutually absolutely continuous, so that
  the binary divergence in `htrans` is finite/meaningful.
The hypothesis `δ ≤ 1/4` of the manuscript is used only through `δ ≤ 1/2`. -/
theorem tied_star_lower_bound {N : ℕ} {g ε δ : ℝ} (hε : 0 < ε) (hεg : ε ≤ g)
    (hg : g ≤ 1 / 4) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (EN : Fan N → ℝ) (hEN : ∀ z, 0 ≤ EN z) (PA : (Fan N → ℝ) → ℝ)
    (hPA : ∀ lam, 0 ≤ PA lam ∧ PA lam ≤ 1)
    (hcorrA : ∀ lam, (∀ i, 0 < lam i ∧ lam i < 1) →
      ε < regret (pairSupp N) (pairSupp_nonempty N) lam → PA lam ≤ δ)
    (hcorrB : ∀ lam, (∀ i, 0 < lam i ∧ lam i < 1) →
      (∀ i, ε < regret (starB N i) (starB_nonempty N i) lam) → 1 - PA lam ≤ δ)
    (hac : ∀ lam, (∀ i, 0 < lam i ∧ lam i < 1) →
      (0 < PA (starMu N g) → 0 < PA lam) ∧ (PA (starMu N g) < 1 → PA lam < 1))
    (htrans : ∀ lam, (∀ i, 0 < lam i ∧ lam i < 1) →
      bkl (PA (starMu N g)) (PA lam) ≤ infoCost EN (starMu N g) lam) :
    bkl (1 / 2) δ * min (N / bkl (1 / 2 - g) (1 / 2 + ε)) (1 / bkl (1 / 2) (1 / 2 + ε))
      ≤ ∑ z, EN z := by
  have hg0 : 0 < g := hε.trans_le hεg
  have hμ := starMu_interior (N := N) hg0 hg
  have hb0 : 0 ≤ bkl (1 / 2) δ := bkl_nonneg (by norm_num) (by norm_num) hδ0 (by linarith)
  have hkA : 0 < bkl (1 / 2 - g) (1 / 2 + ε) := by
    have p1 := pinsker (p := 1 / 2 - g) (q := 1 / 2 + ε) (by linarith) (by linarith)
      (by linarith) (by linarith)
    have e : (1 / 2 - g - (1 / 2 + ε)) ^ 2 = (g + ε) ^ 2 := by ring
    have : 0 < (g + ε) ^ 2 := pow_pos (by linarith) 2
    linarith
  have hkq : 0 < bkl (1 / 2) (1 / 2 + ε) := by
    have p1 := pinsker (p := 1 / 2) (q := 1 / 2 + ε) (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    have e : (1 / 2 - (1 / 2 + ε)) ^ 2 = ε ^ 2 := by ring
    have : 0 < ε ^ 2 := pow_pos hε 2
    linarith
  -- interior of the perturbed instances
  have hupd : ∀ (z0 : Fan N) (η : ℝ), 0 < η → η < 1 / 4 →
      ∀ i, 0 < Function.update (starMu N g) z0 (1 / 2 + ε + η) i ∧
        Function.update (starMu N g) z0 (1 / 2 + ε + η) i < 1 := by
    intro z0 η hη0 hη1 i
    by_cases hi : i = z0
    · rw [hi, Function.update_self]
      constructor <;> linarith
    · rw [Function.update_of_ne hi]
      exact hμ i
  -- continuity in the perturbation size
  have hcont : ∀ (c m : ℝ), ContinuousAt (fun η : ℝ => c * bkl m (1 / 2 + ε + η)) 0 := by
    intro c m
    have h1 : ContinuousAt (fun x => bkl m x) ((fun η : ℝ => 1 / 2 + ε + η) 0) := by
      simpa using continuousAt_bkl m (by linarith : (0 : ℝ) < 1 / 2 + ε) (by linarith)
    exact ContinuousAt.mul continuousAt_const
      (ContinuousAt.comp (f := fun η : ℝ => 1 / 2 + ε + η) h1
        (continuousAt_const.add continuousAt_id))
  have hT : ∀ z, EN z ≤ ∑ z, EN z := fun z =>
    single_le_sum (f := EN) (fun i _ => hEN i) (mem_univ z)
  by_cases hpA : 1 / 2 ≤ PA (starMu N g)
  · -- raise each `r_i` in turn
    have hi : ∀ i : Fin N, bkl (1 / 2) δ ≤ EN (some (some i)) * bkl (1 / 2 - g) (1 / 2 + ε) := by
      intro i
      have key := le_of_forall_small (x := bkl (1 / 2) δ) (η0 := 1 / 4) (by norm_num)
        (hcont (EN (some (some i))) (1 / 2 - g)) ?_
      · simpa using key
      · intro η hη0 hη1
        have hint := hupd (some (some i)) η hη0 hη1
        have hreg : ε < regret (pairSupp N) (pairSupp_nonempty N)
            (Function.update (starMu N g) (some (some i)) (1 / 2 + ε + η)) := by
          refine lt_regret_of_outside _ (c := 1 / 2) (z := some (some i)) ?_ ?_
          · intro y hy
            have hne : y ≠ some (some i) := by
              rcases mem_pairSupp.1 hy with rfl | rfl <;> simp
            rw [Function.update_of_ne hne]
            exact starMu_le_half hg0 y
          · rw [Function.update_self]
            linarith
        have hx := hcorrA _ hint hreg
        have hx0 := (hac _ hint).1 (by linarith)
        have h1 := htrans _ hint
        rw [infoCost_update, starMu_r] at h1
        exact (bkl_half_le hpA (hPA _).2 hx0 hx (by linarith)).trans h1
    have hsum : (N : ℝ) * bkl (1 / 2) δ
        ≤ (∑ i : Fin N, EN (some (some i))) * bkl (1 / 2 - g) (1 / 2 + ε) := by
      have := sum_le_sum (s := (univ : Finset (Fin N))) fun i _ => hi i
      rwa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul] at this
    have hle : ∑ i : Fin N, EN (some (some i)) ≤ ∑ z, EN z := by
      rw [Fintype.sum_option, Fintype.sum_option]
      linarith [hEN none, hEN (some none)]
    have h2 : bkl (1 / 2) δ * (N / bkl (1 / 2 - g) (1 / 2 + ε)) ≤ ∑ z, EN z := by
      rw [← mul_div_assoc, div_le_iff₀ hkA]
      nlinarith [mul_le_mul_of_nonneg_right hle hkA.le]
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hb0).trans h2
  · -- raise `q`
    have hpA' : PA (starMu N g) < 1 / 2 := not_le.1 hpA
    have hq : bkl (1 / 2) δ ≤ EN (some none) * bkl (1 / 2) (1 / 2 + ε) := by
      have key := le_of_forall_small (x := bkl (1 / 2) δ) (η0 := 1 / 4) (by norm_num)
        (hcont (EN (some none)) (1 / 2)) ?_
      · simpa using key
      · intro η hη0 hη1
        have hint := hupd (some none) η hη0 hη1
        have hreg : ∀ i, ε < regret (starB N i) (starB_nonempty N i)
            (Function.update (starMu N g) (some none) (1 / 2 + ε + η)) := by
          intro i
          refine lt_regret_of_outside _ (c := 1 / 2) (z := some none) ?_ ?_
          · intro y hy
            have hne : y ≠ some none := by
              simp only [starB, mem_insert, mem_singleton] at hy
              rcases hy with rfl | rfl <;> simp
            rw [Function.update_of_ne hne]
            exact starMu_le_half hg0 y
          · rw [Function.update_self]
            linarith
        have hx := hcorrB _ hint hreg
        have hx0 := (hac _ hint).2 (by linarith)
        have h1 := htrans _ hint
        rw [infoCost_update, starMu_q, ← bkl_compl] at h1
        exact (bkl_half_le (by linarith) (by linarith [(hPA (starMu N g)).1]) (by linarith) hx
          (by linarith)).trans h1
    have h2 : bkl (1 / 2) δ * (1 / bkl (1 / 2) (1 / 2 + ε)) ≤ ∑ z, EN z := by
      rw [← mul_div_assoc, mul_one, div_le_iff₀ hkq]
      nlinarith [mul_le_mul_of_nonneg_right (hT (some none)) hkq.le]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hb0).trans h2

/-- Quadratic form of the star bound: with `kl(u,v) ≤ (16/3)(u-v)²` on `v ∈ [1/4,3/4]`,
`min{N/kl(1/2-g,1/2+ε), 1/kl(1/2,1/2+ε)} ≥ (3/16) min{N/(g+ε)², 1/ε²}`. -/
theorem star_bound_quadratic {N : ℕ} {g ε : ℝ} (hε : 0 < ε) (hεg : ε ≤ g) (hg : g ≤ 1 / 4) :
    3 / 16 * min (N / (g + ε) ^ 2) (1 / ε ^ 2)
      ≤ min (N / bkl (1 / 2 - g) (1 / 2 + ε)) (1 / bkl (1 / 2) (1 / 2 + ε)) := by
  have hg0 : 0 < g := hε.trans_le hεg
  have k1 := bkl_le_sq (u := 1 / 2 - g) (v := 1 / 2 + ε) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have k2 := bkl_le_sq (u := 1 / 2) (v := 1 / 2 + ε) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  have e1 : (1 / 2 - g - (1 / 2 + ε)) ^ 2 = (g + ε) ^ 2 := by ring
  have e2 : (1 / 2 - (1 / 2 + ε)) ^ 2 = ε ^ 2 := by ring
  rw [e1] at k1
  rw [e2] at k2
  have p1 := pinsker (p := 1 / 2 - g) (q := 1 / 2 + ε) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have p2 := pinsker (p := 1 / 2) (q := 1 / 2 + ε) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  rw [e1] at p1
  rw [e2] at p2
  have hs1 : 0 < (g + ε) ^ 2 := pow_pos (by linarith) 2
  have hs2 : 0 < ε ^ 2 := pow_pos hε 2
  have hkA : 0 < bkl (1 / 2 - g) (1 / 2 + ε) := by linarith
  have hkq : 0 < bkl (1 / 2) (1 / 2 + ε) := by linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine le_min ?_ ?_
  · calc 3 / 16 * min (N / (g + ε) ^ 2) (1 / ε ^ 2)
        ≤ 3 / 16 * (N / (g + ε) ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ = N / (16 / 3 * (g + ε) ^ 2) := by field_simp
      _ ≤ N / bkl (1 / 2 - g) (1 / 2 + ε) := div_le_div_of_nonneg_left hN hkA k1
  · calc 3 / 16 * min (N / (g + ε) ^ 2) (1 / ε ^ 2)
        ≤ 3 / 16 * (1 / ε ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ = 1 / (16 / 3 * ε ^ 2) := by field_simp
      _ ≤ 1 / bkl (1 / 2) (1 / 2 + ε) := div_le_div_of_nonneg_left zero_le_one hkq k2

/-- When `ε ≤ g/√N` (stated as `N ε² ≤ g²`), the `N/(g+ε)²` term is the smaller one. -/
lemma star_first_term_smaller {N : ℕ} {g ε : ℝ} (hε : 0 < ε) (hg : 0 < g)
    (h : (N : ℝ) * ε ^ 2 ≤ g ^ 2) : (N : ℝ) / (g + ε) ^ 2 ≤ 1 / ε ^ 2 := by
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos hε 2)]
  nlinarith [mul_pos hg hε, sq_nonneg ε]

end JointRootCert
