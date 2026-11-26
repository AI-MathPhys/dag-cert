/-
Bernoulli information limit: regularity, the multiple-answer lower bound and the anytime
likelihood certificate.

Manuscript result covered: `thm:ast-main` "One inside witness and Bernoulli information limit"
(proof in the subsection "Bernoulli information-optimal certification for overlapping supports",
`app:ast-optimal`).  This file adds to `BernoulliInfo.lean` and `StoppedProcess.lean`:

* `app:ast-regularity`: the uniform modulus `eq:ast-modulus` (`infoRate_modulus`,
  `witness_modulus`), joint continuity (`infoRate_continuousOn`), attainment of the maxima
  (`exists_infoRate_eq_charRate`, `one_witness_reduction_max`), the parameter modulus and
  continuity of the characteristic rate (`charRate_modulus`, `charRate_continuousOn`,
  `charStar_modulus`), the `ε = 0` midpoint formula (`pairF_zero_eq`), and a finite allocation
  mesh (`exists_finite_mesh`);
* `app:ast-pair-certificate`: the anytime likelihood certificate with actual terminal counts
  (`anytime_certificate`, `certified_stopping_correct`), from a beta-mixture martingale and a
  Ville inequality proved for the sampler model (`ville_tree`);
* `app:ast-lower`: the lower bound that permits several correct answers, `eq:ast-lower-main`
  (`multi_answer_finite`, `lower_bound_multi_answer_trunc`, `lower_bound_multi_answer`,
  `lower_bound_liminf`, and the two instances `ast_lower_main` for correctness on `(0,1)^M`
  and `ast_lower_main_exact` for `ε = 0` with correctness on `𝒟_0` only);
* `app:ast-sequential`: the deterministic tracking bound of the within-epoch rule
  (`tracking_bounds`).

Model: the deterministic adaptive sampler of `StoppedProcess.lean`; probabilities and
expectations are those of the stopped history (`prob`, `probInf`, `expTime`, `expTimeInf`).
The sampler has no internal randomization.  Ville's inequality is proved directly on the tree
of stopped histories (`ville_tree`); the measure-theoretic `ville_ineq` of `Coverage.lean` is
not used.  The beta integral of the mixture martingale enters through its closed form
`1/((n+1) C(n,k))` and the recursion `betaW_succ`.  The lower bound uses Chebyshev's inequality
for the stopped centred log-likelihood ratio (`chebyshev_mart`) where the manuscript uses an
exponential maximal inequality.

Not covered: the sequential sampling rule itself (epochs, sticky label selection, forced
exploration floor), its estimation tail, label locking, and the matching upper bound of
`app:ast-sequential`; the threshold mesh and rational-arithmetic content of the allocation
oracle `eq:ast-oracle`; the witness-game modulus at boundary means `0` or `1`.
-/
import JointRootCert.StoppedProcess

namespace JointRootCert

open Finset Real Filter Topology

set_option linter.unusedSectionVars false

/-! ### Uniform regularity of the Bernoulli information game (`app:ast-regularity`) -/

section Regularity

/-- A concave function vanishing at `0` has decreasing increments; for the binary entropy:
`h(y) - h(x) ≤ h(y - x)` for `0 ≤ x ≤ y ≤ 1`. -/
lemma binEntropy_sub_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    binEntropy y - binEntropy x ≤ binEntropy (y - x) := by
  rcases (hx.trans hxy).eq_or_lt with h0 | h0
  · have hx0 : x = 0 := le_antisymm (h0 ▸ hxy) hx
    simp [← h0, hx0]
  have hc := strictConcave_binEntropy.concaveOn
  have m0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have my : y ∈ Set.Icc (0 : ℝ) 1 := ⟨h0.le, hy⟩
  have ha : 0 ≤ x / y := div_nonneg hx h0.le
  have hb : 0 ≤ (y - x) / y := div_nonneg (sub_nonneg.2 hxy) h0.le
  have hab : x / y + (y - x) / y = 1 := by field_simp; ring
  have h1 := hc.2 m0 my ha hb hab
  have h2 := hc.2 m0 my hb ha (by rw [add_comm]; exact hab)
  simp only [smul_eq_mul, mul_zero, zero_add, binEntropy_zero] at h1 h2
  have e1 : (y - x) / y * y = y - x := by field_simp
  have e2 : x / y * y = x := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  have e3 : (y - x) / y * binEntropy y + x / y * binEntropy y = binEntropy y := by
    rw [← add_mul, add_comm, hab, one_mul]
  linarith

/-- Modulus of continuity of the binary entropy: `|h(p) - h(p')| ≤ h(|p - p'|)`. -/
lemma abs_binEntropy_sub_le {p p' : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hp' : p' ∈ Set.Icc (0 : ℝ) 1) :
    |binEntropy p - binEntropy p'| ≤ binEntropy |p - p'| := by
  wlog hle : p' ≤ p generalizing p p'
  · have := this hp' hp (le_of_not_ge hle)
    rwa [abs_sub_comm, abs_sub_comm p' p] at this
  rw [abs_of_nonneg (sub_nonneg.2 hle), abs_le]
  constructor
  · have h := binEntropy_sub_le (x := 1 - p) (y := 1 - p') (by linarith [hp.2]) (by linarith)
      (by linarith [hp'.1])
    rw [binEntropy_one_sub, binEntropy_one_sub] at h
    have e : 1 - p' - (1 - p) = p - p' := by ring
    rw [e] at h
    linarith
  · exact binEntropy_sub_le hp'.1 hle hp.2

/-- `h(x) ≤ x - x log x = x log(e/x)` on `[0,1]`. -/
lemma binEntropy_le_eta {x : ℝ} (hx1 : x ≤ 1) :
    binEntropy x ≤ x - x * log x := by
  have h1 : (1 - x) * log (1 - x)⁻¹ ≤ x := by
    rcases hx1.eq_or_lt with h | h
    · simp [h]
    · have hpos : 0 < 1 - x := sub_pos.2 h
      have := log_le_sub_one_of_pos (inv_pos.2 hpos)
      have h2 := mul_le_mul_of_nonneg_left this hpos.le
      have e : (1 - x) * ((1 - x)⁻¹ - 1) = x := by field_simp; ring
      linarith
  unfold binEntropy
  rw [log_inv x]
  linarith

/-- `x ↦ x - x log x` is nondecreasing on `[0,1]`. -/
lemma eta_mono {x r : ℝ} (hx : 0 ≤ x) (hxr : x ≤ r) (hr : r ≤ 1) :
    x - x * log x ≤ r - r * log r := by
  have hr0 : 0 ≤ r := hx.trans hxr
  have hlr : log r ≤ 0 := log_nonpos hr0 hr
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    have := mul_nonneg hr0 (neg_nonneg.2 hlr)
    simp only [zero_mul, sub_zero]
    linarith
  · have hrp : 0 < r := h.trans_le hxr
    have h1 := one_sub_inv_le_log_of_pos (div_pos h hrp)
    rw [inv_div, log_div h.ne' hrp.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have e : x * (1 - r / x) = x - r := by field_simp
    rw [e] at h2
    have h3 := mul_nonneg (sub_nonneg.2 hxr) (neg_nonneg.2 hlr)
    nlinarith

lemma bkl_eq_binEntropy (p : ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    bkl p q = -binEntropy p - p * log q - (1 - p) * log (1 - q) := by
  rw [bkl_eq p hq0 hq1]
  unfold binEntropy
  rw [log_inv, log_inv]
  ring

/-- Changing the first argument of `kl(·, q)` for `q ∈ [β, 1-β]`. -/
lemma bkl_sub_le {p p' q β : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hp' : p' ∈ Set.Icc (0 : ℝ) 1)
    (hβ : 0 < β) (hβq : β ≤ q) (hqβ : q ≤ 1 - β) :
    bkl p' q - bkl p q ≤ binEntropy |p - p'| + |p - p'| * (-log β) := by
  have hq0 : 0 < q := hβ.trans_le hβq
  have hq1 : q < 1 := by linarith
  have h1 := (abs_le.1 (abs_binEntropy_sub_le hp hp')).2
  have hL1 : log β ≤ log q := log_le_log hβ hβq
  have hL2 : log β ≤ log (1 - q) := log_le_log hβ (by linarith)
  have hL3 : log q ≤ 0 := log_nonpos hq0.le hq1.le
  have hL4 : log (1 - q) ≤ 0 := log_nonpos (by linarith) (by linarith)
  have hL : |log q - log (1 - q)| ≤ -log β := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : (p - p') * (log q - log (1 - q)) ≤ |p - p'| * (-log β) := by
    calc (p - p') * (log q - log (1 - q)) ≤ |(p - p') * (log q - log (1 - q))| := le_abs_self _
      _ = |p - p'| * |log q - log (1 - q)| := abs_mul _ _
      _ ≤ |p - p'| * (-log β) := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
  rw [bkl_eq_binEntropy p' hq0 hq1, bkl_eq_binEntropy p hq0 hq1]
  have e : -binEntropy p' - p' * log q - (1 - p') * log (1 - q)
      - (-binEntropy p - p * log q - (1 - p) * log (1 - q))
      = (binEntropy p - binEntropy p') + (p - p') * (log q - log (1 - q)) := by ring
  rw [e]
  linarith

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- Modulus `ω_ε(d) = d (1 + 2 D_ε + 2 log(1/d))` of `eq:ast-modulus`, with
`D_ε = log(4/(1-ε))`; `ω_ε(0) = 0`. -/
noncomputable def omega (ε d : ℝ) : ℝ := d * (1 + 2 * log (4 / (1 - ε)) + 2 * log (1 / d))

@[simp] lemma omega_zero (ε : ℝ) : omega ε 0 = 0 := by simp [omega]

lemma omega_continuous (ε : ℝ) : Continuous (omega ε) := by
  have h : omega ε = fun d => d * (1 + 2 * log (4 / (1 - ε))) - 2 * (d * log d) := by
    funext d
    unfold omega
    rw [one_div, log_inv]
    ring
  rw [h]
  exact (continuous_id.mul continuous_const).sub (continuous_const.mul continuous_mul_log)

lemma log_four_div_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) : 0 ≤ log (4 / (1 - ε)) := by
  refine log_nonneg ?_
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma omega_nonneg {ε d : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ omega ε d := by
  unfold omega
  rcases hd0.eq_or_lt with h | h
  · simp [← h]
  · have h1 := log_four_div_nonneg hε0 hε1
    have h2 : 0 ≤ log (1 / d) := log_nonneg (by rw [le_div_iff₀ h]; linarith)
    exact mul_nonneg hd0 (by linarith)

/-- Changing means and weights at an alternative bounded away from `0` and `1`. -/
lemma infoCost_perturb {w w' p p' lam : Z → ℝ} {β r s : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hp' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1)
    (hβ : 0 < β) (hlam : ∀ i, β ≤ lam i ∧ lam i ≤ 1 - β) (hr : ∀ i, |p i - p' i| ≤ r)
    (hr1 : r ≤ 1) (hs : ∑ i, |w i - w' i| ≤ s) :
    infoCost w' p' lam ≤ infoCost w p lam + (r - r * log r) + (r + s) * (-log β) := by
  obtain ⟨i0⟩ := ‹Nonempty Z›
  have hβ1 : β ≤ 1 / 2 := by linarith [(hlam i0).1, (hlam i0).2]
  have hlogβ : 0 ≤ -log β := neg_nonneg.2 (log_nonpos hβ.le (by linarith))
  have hr0 : 0 ≤ r := (abs_nonneg _).trans (hr i0)
  have hη : 0 ≤ r - r * log r := by
    have := mul_nonneg hr0 (neg_nonneg.2 (log_nonpos hr0 hr1))
    linarith
  have hterm : ∀ i, w' i * bkl (p' i) (lam i)
      ≤ w i * bkl (p i) (lam i) + w i * ((r - r * log r) + r * (-log β))
        + |w i - w' i| * (-log β) := by
    intro i
    have hb0 := bkl_nonneg (hp' i).1 (hp' i).2 (hβ.trans_le (hlam i).1)
      (by linarith [(hlam i).2])
    have hb1 := bkl_le_neg_log (hp' i).1 (hp' i).2 hβ (hlam i).1 (hlam i).2
    have h1 := bkl_sub_le (p := p i) (p' := p' i) (hp i) (hp' i) hβ (hlam i).1 (hlam i).2
    have h2 : binEntropy |p i - p' i| ≤ r - r * log r :=
      (binEntropy_le_eta ((hr i).trans hr1)).trans
        (eta_mono (abs_nonneg _) (hr i) hr1)
    have h3 : |p i - p' i| * (-log β) ≤ r * (-log β) :=
      mul_le_mul_of_nonneg_right (hr i) hlogβ
    have h4 : bkl (p' i) (lam i) ≤ bkl (p i) (lam i) + ((r - r * log r) + r * (-log β)) := by
      linarith
    have h5 : (w' i - w i) * bkl (p' i) (lam i) ≤ |w i - w' i| * (-log β) := by
      calc (w' i - w i) * bkl (p' i) (lam i) ≤ |w' i - w i| * bkl (p' i) (lam i) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hb0
        _ = |w i - w' i| * bkl (p' i) (lam i) := by rw [abs_sub_comm]
        _ ≤ |w i - w' i| * (-log β) := mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
    have h6 := mul_le_mul_of_nonneg_left h4 (hw i)
    nlinarith
  have hsum := sum_le_sum (s := (univ : Finset Z)) fun i _ => hterm i
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul] at hsum
  have hA : (∑ i, w i) * ((r - r * log r) + r * (-log β)) ≤ (r - r * log r) + r * (-log β) := by
    have : 0 ≤ (r - r * log r) + r * (-log β) := add_nonneg hη (mul_nonneg hr0 hlogβ)
    nlinarith
  have hB : (∑ i, |w i - w' i|) * (-log β) ≤ s * (-log β) :=
    mul_le_mul_of_nonneg_right hs hlogβ
  unfold infoCost
  linarith

/-- Mixing an alternative with the reference alternative of its own component: the result is
an alternative in `[α b_ε, 1 - α b_ε]^M` whose cost exceeds the original by at most
`α D_ε`. -/
lemma exists_trunc_alt {S : Finset Z} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {w p lam : Z → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hlam : lam ∈ Alt S ε) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ lam' ∈ Alt S ε,
      (∀ i, α * ((1 - ε) / 4) ≤ lam' i ∧ lam' i ≤ 1 - α * ((1 - ε) / 4)) ∧
      infoCost w p lam' ≤ infoCost w p lam + α * log (4 / (1 - ε)) := by
  obtain ⟨hint, z, hz, hlt⟩ := hlam
  have hb0 : 0 < (1 - ε) / 4 := by linarith
  have hD : -log ((1 - ε) / 4) = log (4 / (1 - ε)) := by rw [← log_inv, inv_div]
  have hD0 := log_four_div_nonneg hε0 hε1
  let ref : Z → ℝ := fun i =>
    if i ∈ S then (1 - ε) / 4 else if i = z then 1 - (1 - ε) / 4 else 1 / 2
  have hrefS : ∀ y ∈ S, ref y = (1 - ε) / 4 := fun y hy => by simp [ref, hy]
  have hrefz : ref z = 1 - (1 - ε) / 4 := by simp [ref, hz]
  have hrange : ∀ i, (1 - ε) / 4 ≤ ref i ∧ ref i ≤ 1 - (1 - ε) / 4 := by
    intro i
    dsimp only [ref]
    split_ifs <;> constructor <;> linarith
  have hαb : 0 < α * ((1 - ε) / 4) := mul_pos hα0 hb0
  have hlo : ∀ i, α * ((1 - ε) / 4) ≤ (1 - α) * lam i + α * ref i := fun i => by
    have h1 := mul_nonneg (sub_nonneg.2 hα1) (hint i).1.le
    have h2 := mul_le_mul_of_nonneg_left (hrange i).1 hα0.le
    linarith
  have hhi : ∀ i, (1 - α) * lam i + α * ref i ≤ 1 - α * ((1 - ε) / 4) := fun i => by
    have h1 := mul_le_mul_of_nonneg_left (hint i).2.le (sub_nonneg.2 hα1)
    have h2 := mul_le_mul_of_nonneg_left (hrange i).2 hα0.le
    nlinarith
  refine ⟨fun i => (1 - α) * lam i + α * ref i, ⟨fun i => ?_, z, hz, fun y hy => ?_⟩,
    fun i => ⟨hlo i, hhi i⟩, ?_⟩
  · exact ⟨by linarith [hlo i], by linarith [hhi i]⟩
  · show (1 - α) * lam y + α * ref y + ε < (1 - α) * lam z + α * ref z
    rw [hrefS y hy, hrefz]
    have h1 := mul_le_mul_of_nonneg_left (hlt y hy).le (sub_nonneg.2 hα1)
    have h2 : α * ((1 - ε) / 4 + ε) < α * (1 - (1 - ε) / 4) :=
      mul_lt_mul_of_pos_left (by linarith) hα0
    nlinarith
  · have hterm : ∀ i, w i * bkl (p i) ((1 - α) * lam i + α * ref i)
        ≤ w i * bkl (p i) (lam i) + w i * (α * log (4 / (1 - ε))) := by
      intro i
      have hc := bkl_convex_comb (hp i).1 (hp i).2 (x := lam i) (y := ref i)
        ⟨(hint i).1, (hint i).2⟩
        ⟨by linarith [(hrange i).1], by linarith [(hrange i).2]⟩
        (sub_nonneg.2 hα1) hα0.le (by ring)
      have hb0' := bkl_nonneg (hp i).1 (hp i).2 (hint i).1 (hint i).2
      have hb1 := bkl_le_neg_log (hp i).1 (hp i).2 hb0 (hrange i).1 (hrange i).2
      rw [hD] at hb1
      have h3 : (1 - α) * bkl (p i) (lam i) ≤ bkl (p i) (lam i) := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left hb1 hα0.le
      have h5 : bkl (p i) ((1 - α) * lam i + α * ref i)
          ≤ bkl (p i) (lam i) + α * log (4 / (1 - ε)) := by linarith
      have := mul_le_mul_of_nonneg_left h5 (hw i)
      linarith
    have hsum := sum_le_sum (s := (univ : Finset Z)) fun i _ => hterm i
    rw [sum_add_distrib, ← sum_mul] at hsum
    have hA : (∑ i, w i) * (α * log (4 / (1 - ε))) ≤ α * log (4 / (1 - ε)) := by
      have : 0 ≤ α * log (4 / (1 - ε)) := mul_nonneg hα0.le hD0
      nlinarith
    unfold infoCost
    linarith

/-- One-sided form of `eq:ast-modulus`. -/
lemma infoRate_le_add_omega {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {w w' p p' : Z → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1)
    (hw' : ∀ i, 0 ≤ w' i) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hp' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1)
    {r s : ℝ} (hr : ∀ i, |p i - p' i| ≤ r) (hs : ∑ i, |w i - w' i| ≤ s) (hs0 : 0 ≤ s)
    (hd0 : 0 < r + s) (hd : r + s ≤ 1 / 2) :
    infoRate S ε w' p' ≤ infoRate S ε w p + omega ε (r + s) := by
  obtain ⟨i0⟩ := ‹Nonempty Z›
  have hr0 : 0 ≤ r := (abs_nonneg _).trans (hr i0)
  have hb0 : 0 < (1 - ε) / 4 := by linarith
  have hD : -log ((1 - ε) / 4) = log (4 / (1 - ε)) := by rw [← log_inv, inv_div]
  rw [← sub_le_iff_le_add]
  refine le_csInf ((alt_nonempty hSc hε0 hε1).image _) ?_
  rintro _ ⟨lam, hlam, rfl⟩
  obtain ⟨lam', hlam', hrange, hcost⟩ :=
    exists_trunc_alt hε0 hε1 hw hw1 hp hlam hd0 (by linarith)
  have h1 : infoRate S ε w' p' ≤ infoCost w' p' lam' :=
    csInf_le (infoCost_bddBelow hw' hp') ⟨lam', hlam', rfl⟩
  have h2 := infoCost_perturb hw hw1 hp hp' (mul_pos hd0 hb0) hrange hr (by linarith) hs
  have h3 : r - r * log r ≤ (r + s) - (r + s) * log (r + s) :=
    eta_mono hr0 (by linarith) (by linarith)
  have h4 : -log ((r + s) * ((1 - ε) / 4)) = -log (r + s) + log (4 / (1 - ε)) := by
    rw [log_mul hd0.ne' hb0.ne', ← hD]
    ring
  have h5 : omega ε (r + s)
      = (r + s) * log (4 / (1 - ε)) + ((r + s) - (r + s) * log (r + s))
        + (r + s) * (-log (r + s) + log (4 / (1 - ε))) := by
    unfold omega
    rw [one_div, log_inv]
    ring
  rw [h4] at h2
  rw [h5]
  linarith

/-- **Uniform modulus of the action game** (`eq:ast-modulus`).  For `p, p' ∈ [0,1]^M`
(empirical means at `0` or `1` allowed) and nonnegative weights `w, w'` of total mass at most
one (zero weights allowed), with `d = ‖p - p'‖_∞ + ‖w - w'‖_1 ≤ 1/2`,
`|I_a^ε(p,w) - I_a^ε(p',w')| ≤ ω_ε(d)`. -/
theorem infoRate_modulus {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {w w' p p' : Z → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1)
    (hw' : ∀ i, 0 ≤ w' i) (hw1' : ∑ i, w' i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hp' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1) (hd : ‖p - p'‖ + ∑ i, |w i - w' i| ≤ 1 / 2) :
    |infoRate S ε w p - infoRate S ε w' p'| ≤ omega ε (‖p - p'‖ + ∑ i, |w i - w' i|) := by
  have hr : ∀ i, |p i - p' i| ≤ ‖p - p'‖ := fun i => by
    have := norm_le_pi_norm (p - p') i
    simpa [Real.norm_eq_abs] using this
  have hr' : ∀ i, |p' i - p i| ≤ ‖p - p'‖ := fun i => by rw [abs_sub_comm]; exact hr i
  have hs0 : 0 ≤ ∑ i, |w i - w' i| := sum_nonneg fun i _ => abs_nonneg _
  have hs' : ∑ i, |w' i - w i| ≤ ∑ i, |w i - w' i| :=
    le_of_eq (sum_congr rfl fun i _ => abs_sub_comm _ _)
  rcases (add_nonneg (norm_nonneg (p - p')) hs0).eq_or_lt with h0 | h0
  · have hn : ‖p - p'‖ = 0 := by linarith [norm_nonneg (p - p')]
    have hss : ∑ i, |w i - w' i| = 0 := by linarith
    have hpp : p = p' := sub_eq_zero.1 (norm_eq_zero.1 hn)
    have hww : w = w' := by
      funext i
      have := (sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (w i - w' i)).1 hss i (mem_univ i)
      exact sub_eq_zero.1 (abs_eq_zero.1 this)
    rw [hpp, hww]
    simp
  · rw [abs_le]
    constructor
    · have := infoRate_le_add_omega hSc hε0 hε1 hw hw1 hw' hp hp' hr le_rfl hs0 h0 hd
      linarith
    · have := infoRate_le_add_omega hSc hε0 hε1 hw' hw1' hw hp' hp hr' hs' hs0 h0 hd
      linarith

/-- The action game is jointly continuous in weights and means on
`{w ≥ 0, ∑ w ≤ 1} × [0,1]^M`. -/
theorem infoRate_continuousOn {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    ContinuousOn (fun q : (Z → ℝ) × (Z → ℝ) => infoRate S ε q.1 q.2)
      {q | ((∀ i, 0 ≤ q.1 i) ∧ ∑ i, q.1 i ≤ 1) ∧ ∀ i, 0 ≤ q.2 i ∧ q.2 i ≤ 1} := by
  intro q0 hq0
  set g : (Z → ℝ) × (Z → ℝ) → ℝ := fun q => ‖q.2 - q0.2‖ + ∑ i, |q.1 i - q0.1 i| with hg
  have hgc : Continuous g := by
    refine ((continuous_snd.sub continuous_const).norm).add (continuous_finsetSum _ fun i _ => ?_)
    exact (((continuous_apply i).comp continuous_fst).sub continuous_const).abs
  have hg0 : g q0 = 0 := by simp [hg]
  have hT : Tendsto (fun q => omega ε (g q)) (𝓝[{q : (Z → ℝ) × (Z → ℝ) |
      ((∀ i, 0 ≤ q.1 i) ∧ ∑ i, q.1 i ≤ 1) ∧ ∀ i, 0 ≤ q.2 i ∧ q.2 i ≤ 1}] q0) (𝓝 0) := by
    have h := ((omega_continuous ε).comp hgc).tendsto q0
    simp only [Function.comp_apply, hg0, omega_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ q in 𝓝[{q : (Z → ℝ) × (Z → ℝ) |
      ((∀ i, 0 ≤ q.1 i) ∧ ∑ i, q.1 i ≤ 1) ∧ ∀ i, 0 ≤ q.2 i ∧ q.2 i ≤ 1}] q0, g q ≤ 1 / 2 := by
    have : ∀ᶠ q in 𝓝 q0, g q < 1 / 2 :=
      hgc.continuousAt.eventually (eventually_lt_nhds (by rw [hg0]; norm_num))
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun q hq => hq.le
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun q => dist_nonneg)
    ?_ hT)
  filter_upwards [hsmall, self_mem_nhdsWithin] with q hq hqs
  rw [Real.dist_eq]
  exact infoRate_modulus hSc hε0 hε1 hqs.1.1 hqs.1.2 hq0.1.1 hq0.1.2 hqs.2 hq0.2 hq

/-- **Attainment**: for means in `[0,1]^M` the maximum over the sampling simplex in the
definition of `C_a^ε` is attained. -/
theorem exists_infoRate_eq_charRate {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) :
    ∃ w ∈ simplex Z, infoRate S ε w μ = charRate S ε μ ∧
      ∀ w' ∈ simplex Z, infoRate S ε w' μ ≤ infoRate S ε w μ := by
  have hcont : ContinuousOn (fun w : Z → ℝ => infoRate S ε w μ) (simplex Z) := by
    have h := (infoRate_continuousOn (S := S) hSc hε0 hε1).comp
      (f := fun w : Z → ℝ => (w, μ)) (s := simplex Z)
      (Continuous.continuousOn (by fun_prop)) (fun w hw => ⟨⟨hw.1, hw.2.le⟩, hμ⟩)
    exact h
  obtain ⟨w, hw, hmax⟩ := (isCompact_simplex Z).exists_isMaxOn simplex_nonempty hcont
  refine ⟨w, hw, le_antisymm (le_charRate hSc hε0 hε1 hμ hw) ?_, fun w' hw' => hmax hw'⟩
  refine csSup_le (simplex_nonempty.image _) ?_
  rintro _ ⟨w', hw', rfl⟩
  exact hmax hw'

/-- **One inside witness with attained maxima** (`eq:ast-star`): for interior means and an
inside maximizer `j`, the star game attains its maximum, and the maximum equals
`C_a^ε = max_{w ∈ Δ_M} I_a^ε(μ, w)`. -/
theorem one_witness_reduction_max {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {j : Z}
    (hj : j ∈ S) (hmax : ∀ y ∈ S, μ y ≤ μ j) :
    ∃ st ∈ starSet S, starVal S hSc ε μ j st = charRate S ε μ ∧
      ∀ st' ∈ starSet S, starVal S hSc ε μ j st' ≤ starVal S hSc ε μ j st := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hle : ∀ st ∈ starSet S, starVal S hSc ε μ j st ≤ charRate S ε μ := by
    rintro ⟨s, t⟩ hst
    rw [← infoRate_collapse hS hSc hε0 hε1 hμ hj hst.1 hst.2.1]
    exact le_charRate hSc hε0 hε1 hμ' (collapse_mem_simplex hj hst)
  obtain ⟨w, hw, hwC, -⟩ := exists_infoRate_eq_charRate (S := S) hSc hε0 hε1 hμ'
  have hmem : ((∑ y ∈ S, w y, w) : ℝ × (Z → ℝ)) ∈ starSet S :=
    ⟨sum_nonneg fun y _ => hw.1 y, hw.1, by rw [sum_add_sum_compl]; exact hw.2⟩
  have hge := infoRate_le_starVal hS hSc hε0 hε1 hw.1 hμ hmax
  rw [hwC] at hge
  have heq := le_antisymm (hle _ hmem) hge
  exact ⟨_, hmem, heq, fun st' hst' => by rw [heq]; exact hle st' hst'⟩

/-- **Parameter modulus of the characteristic rate**: for `p, p' ∈ [0,1]^M` with
`‖p - p'‖_∞ ≤ 1/2`, `|C_a^ε(p) - C_a^ε(p')| ≤ ω_ε(‖p - p'‖_∞)`. -/
theorem charRate_modulus {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {p p' : Z → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hp' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1) (hd : ‖p - p'‖ ≤ 1 / 2) :
    |charRate S ε p - charRate S ε p'| ≤ omega ε ‖p - p'‖ := by
  have key : ∀ q q' : Z → ℝ, (∀ i, 0 ≤ q i ∧ q i ≤ 1) → (∀ i, 0 ≤ q' i ∧ q' i ≤ 1) →
      ‖q - q'‖ ≤ 1 / 2 → charRate S ε q ≤ charRate S ε q' + omega ε ‖q - q'‖ := by
    intro q q' hq hq' hqq
    refine csSup_le (simplex_nonempty.image _) ?_
    rintro _ ⟨w, hw, rfl⟩
    have h := infoRate_modulus (S := S) hSc hε0 hε1 hw.1 hw.2.le hw.1 hw.2.le hq hq'
      (by simpa using hqq)
    simp only [sub_self, abs_zero, sum_const_zero, add_zero] at h
    have h2 := le_charRate (S := S) hSc hε0 hε1 hq' hw
    linarith [(abs_le.1 h).2]
  rw [abs_le]
  constructor
  · have := key p' p hp' hp (by rwa [norm_sub_rev])
    rw [norm_sub_rev] at this
    linarith
  · have := key p p' hp hp' hd
    linarith

/-- The characteristic rate is continuous in the means on `[0,1]^M`. -/
theorem charRate_continuousOn {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    ContinuousOn (fun p : Z → ℝ => charRate S ε p) {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1} := by
  intro p0 hp0
  have hgc : Continuous fun p : Z → ℝ => ‖p - p0‖ := (continuous_id.sub continuous_const).norm
  have hT : Tendsto (fun p : Z → ℝ => omega ε ‖p - p0‖)
      (𝓝[{p : Z → ℝ | ∀ i, 0 ≤ p i ∧ p i ≤ 1}] p0) (𝓝 0) := by
    have h := ((omega_continuous ε).comp hgc).tendsto p0
    simp only [Function.comp_apply, sub_self, norm_zero, omega_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ p in 𝓝[{p : Z → ℝ | ∀ i, 0 ≤ p i ∧ p i ≤ 1}] p0, ‖p - p0‖ ≤ 1 / 2 := by
    have : ∀ᶠ p in 𝓝 p0, ‖p - p0‖ < 1 / 2 :=
      hgc.continuousAt.eventually (eventually_lt_nhds (by simp))
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun q hq => hq.le
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun q => dist_nonneg)
    ?_ hT)
  filter_upwards [hsmall, self_mem_nhdsWithin] with p hp hps
  rw [Real.dist_eq]
  exact charRate_modulus hSc hε0 hε1 hps hp0 hp

/-- **Modulus of a fixed witness game** (`eq:ast-modulus`, second inequality) at interior
means: `f_b(p,w) = min_{z ∉ S} F_ε(p_j, p_z; w_j, w_z)` for the witness label `b = (a,j)`,
`j ∈ S(a)`. -/
theorem witness_modulus {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {j : Z} (hj : j ∈ S) {w w' p p' : Z → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1) (hw' : ∀ i, 0 ≤ w' i) (hw1' : ∑ i, w' i ≤ 1)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hp' : ∀ i, 0 < p' i ∧ p' i < 1)
    (hd : ‖p - p'‖ + ∑ i, |w i - w' i| ≤ 1 / 2) :
    |starVal S hSc ε p j (w j, w) - starVal S hSc ε p' j (w' j, w')|
      ≤ omega ε (‖p - p'‖ + ∑ i, |w i - w' i|) := by
  have hpc : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨(hp i).1.le, (hp i).2.le⟩
  have hpc' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1 := fun i => ⟨(hp' i).1.le, (hp' i).2.le⟩
  have hs0 : 0 ≤ ∑ i, |w i - w' i| := sum_nonneg fun i _ => abs_nonneg _
  rcases (add_nonneg (norm_nonneg (p - p')) hs0).eq_or_lt with hd0 | hd0
  · have hn : ‖p - p'‖ = 0 := by linarith [norm_nonneg (p - p')]
    have hss : ∑ i, |w i - w' i| = 0 := by linarith
    have hpp : p = p' := sub_eq_zero.1 (norm_eq_zero.1 hn)
    have hww : w = w' := by
      funext i
      have := (sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (w i - w' i)).1 hss i (mem_univ i)
      exact sub_eq_zero.1 (abs_eq_zero.1 this)
    rw [hpp, hww]
    simp
  rw [← infoRate_collapse hS hSc hε0 hε1 hp hj (hw j) hw,
    ← infoRate_collapse hS hSc hε0 hε1 hp' hj (hw' j) hw']
  have hcle : ∀ (v : Z → ℝ), (∀ i, 0 ≤ v i) → ∀ i, collapse S j (v j) v i ≤ v i := by
    intro v hv i
    unfold collapse
    split_ifs with h1 h2
    · rw [h2]
    · exact hv i
    · exact le_rfl
  have hc1 : ∀ (v : Z → ℝ), (∀ i, 0 ≤ v i) → ∑ i, v i ≤ 1 → ∑ i, collapse S j (v j) v i ≤ 1 :=
    fun v hv hv1 => (sum_le_sum fun i _ => hcle v hv i).trans hv1
  have hdiff : ∀ i, |collapse S j (w j) w i - collapse S j (w' j) w' i| ≤ |w i - w' i| := by
    intro i
    unfold collapse
    split_ifs with h1 h2
    · rw [h2]
    · simp
    · exact le_rfl
  have hdiff' : ∀ i, |collapse S j (w' j) w' i - collapse S j (w j) w i| ≤ |w i - w' i| :=
    fun i => by rw [abs_sub_comm]; exact hdiff i
  have hr : ∀ i, |p i - p' i| ≤ ‖p - p'‖ := fun i => by
    have := norm_le_pi_norm (p - p') i
    simpa [Real.norm_eq_abs] using this
  have hr' : ∀ i, |p' i - p i| ≤ ‖p - p'‖ := fun i => by rw [abs_sub_comm]; exact hr i
  rw [abs_le]
  constructor
  · have := infoRate_le_add_omega (S := S) hSc hε0 hε1 (collapse_nonneg (hw j) hw)
      (hc1 w hw hw1) (collapse_nonneg (hw' j) hw') hpc hpc' hr
      (sum_le_sum fun i _ => hdiff i) hs0 hd0 hd
    linarith
  · have := infoRate_le_add_omega (S := S) hSc hε0 hε1 (collapse_nonneg (hw' j) hw')
      (hc1 w' hw' hw1') (collapse_nonneg (hw j) hw) hpc' hpc hr'
      (sum_le_sum fun i _ => hdiff' i) hs0 hd0 hd
    linarith

/-- **Finite allocation mesh** (core of the oracle `eq:ast-oracle`).  For every tolerance
`ξ > 0` there is one finite set `W` of allocations in the simplex such that, for every mean
vector `p ∈ [0,1]^M`, some `w ∈ W` satisfies
`I_a^ε(p,w) ≤ C_a^ε(p) ≤ I_a^ε(p,w) + ξ`; so `L = I_a^ε(p,w)`, `U = L + ξ` meet the contract
`0 ≤ L ≤ I_a^ε(p,w) ≤ C_a^ε(p) ≤ U`, `U - L ≤ ξ`.  The mesh is the covering step of the
manuscript's construction, with its error controlled by `eq:ast-modulus`; the threshold mesh
and the rational enclosures of the logarithms are not formalized. -/
theorem exists_finite_mesh {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ W : Finset (Z → ℝ), (∀ w ∈ W, w ∈ simplex Z) ∧
      ∀ p : Z → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
        ∃ w ∈ W, 0 ≤ infoRate S ε w p ∧ infoRate S ε w p ≤ charRate S ε p ∧
          charRate S ε p ≤ infoRate S ε w p + ξ := by
  classical
  -- a radius at which the modulus is below `ξ`
  obtain ⟨d0, hd0, hω⟩ := Metric.continuousAt_iff.1 (omega_continuous ε).continuousAt ξ hξ
  obtain ⟨d, hd, hdd0, hd2⟩ : ∃ d : ℝ, 0 < d ∧ d < d0 ∧ d ≤ 1 / 2 :=
    ⟨min (d0 / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  let U : {w : Z → ℝ // w ∈ simplex Z} → Set (Z → ℝ) :=
    fun w => {w' | ∑ i, |w' i - w.1 i| < d}
  have hUo : ∀ w, IsOpen (U w) := fun w =>
    isOpen_lt (continuous_finsetSum _ fun i _ => ((continuous_apply i).sub continuous_const).abs)
      continuous_const
  have hcov : simplex Z ⊆ ⋃ w, U w := fun w hw =>
    Set.mem_iUnion.2 ⟨⟨w, hw⟩, show ∑ i, |w i - w i| < d by simpa using hd⟩
  obtain ⟨t, ht⟩ := (isCompact_simplex Z).elim_finite_subcover U hUo hcov
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, -, rfl⟩ := mem_image.1 hw
    exact i.2
  · intro p hp
    obtain ⟨ws, hws, hmax, -⟩ := exists_infoRate_eq_charRate (S := S) hSc hε0 hε1 hp
    obtain ⟨w, hwt, hw⟩ := Set.mem_iUnion₂.1 (ht hws)
    have hwd : ∑ i, |ws i - w.1 i| < d := hw
    have hs0 : 0 ≤ ∑ i, |ws i - w.1 i| := sum_nonneg fun i _ => abs_nonneg _
    refine ⟨w.1, mem_image_of_mem _ hwt, infoRate_nonneg w.2.1 hp,
      le_charRate hSc hε0 hε1 hp w.2, ?_⟩
    have hmod := infoRate_modulus (S := S) hSc hε0 hε1 hws.1 hws.2.le w.2.1 w.2.2.le hp hp
      (by simp only [sub_self, norm_zero, zero_add]; linarith)
    simp only [sub_self, norm_zero, zero_add] at hmod
    have hsmall : |omega ε (∑ i, |ws i - w.1 i|)| < ξ := by
      have := hω (x := ∑ i, |ws i - w.1 i|) (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]
        linarith)
      rwa [Real.dist_eq, omega_zero, sub_zero] at this
    have h1 := (abs_le.1 hmod).2
    have h2 := (abs_lt.1 hsmall).2
    linarith

/-- **The `ε = 0` pair minimizer** (remark after `eq:ast-pair`): for `q < m` and `s, t > 0`
the pair statistic `F_0(m,q;s,t)` is attained at the weighted midpoint
`θ = (s m + t q)/(s + t)`, so the reduced game is the best-arm transportation cost. -/
theorem pairF_zero_eq {m q s t : ℝ} (hq0 : 0 < q) (hqm : q < m) (hm1 : m < 1) (hs : 0 < s)
    (ht : 0 < t) :
    pairF 0 m q s t
      = s * bkl m ((s * m + t * q) / (s + t)) + t * bkl q ((s * m + t * q) / (s + t)) := by
  have hst : 0 < s + t := add_pos hs ht
  obtain ⟨θs, hθs⟩ : ∃ θs : ℝ, θs = (s * m + t * q) / (s + t) := ⟨_, rfl⟩
  rw [← hθs]
  have key : s * m + t * q = (s + t) * θs := by
    rw [hθs]
    field_simp
  have hθq : q < θs := by
    have : (s + t) * q < (s + t) * θs := by nlinarith
    exact lt_of_mul_lt_mul_left this hst.le
  have hθm : θs < m := by
    have : (s + t) * θs < (s + t) * m := by nlinarith
    exact lt_of_mul_lt_mul_left this hst.le
  have hθ0 : 0 < θs := hq0.trans hθq
  have hθ1 : θs < 1 := hθm.trans hm1
  -- compensation identity
  have comp : ∀ θ : ℝ, 0 < θ → θ < 1 →
      s * bkl m θ + t * bkl q θ = s * bkl m θs + t * bkl q θs + (s + t) * bkl θs θ := by
    intro θ h0 h1
    rw [bkl_eq m h0 h1, bkl_eq q h0 h1, bkl_eq m hθ0 hθ1, bkl_eq q hθ0 hθ1, bkl_eq θs h0 h1]
    linear_combination (log θs - log θ - log (1 - θs) + log (1 - θ)) * key
  unfold pairF
  simp only [sub_zero]
  refine IsLeast.csInf_eq ⟨⟨θs, ⟨hθ0, hθ1⟩, ?_⟩, ?_⟩
  · show s * dDown m θs + t * bkl q θs = _
    rw [dDown_of_lt hθm]
  · rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
    show s * bkl m θs + t * bkl q θs ≤ s * dDown m θ + t * bkl q θ
    by_cases hθ : θ < m
    · rw [dDown_of_lt hθ, comp θ h0 h1]
      have := mul_nonneg hst.le (bkl_nonneg hθ0.le hθ1.le h0 h1)
      linarith
    · rw [dDown_of_le (not_lt.1 hθ), mul_zero, zero_add]
      have hm0 : 0 < m := hq0.trans hqm
      have h2 := comp m hm0 hm1
      rw [bkl_self, mul_zero, zero_add] at h2
      have h3 := mul_nonneg hst.le (bkl_nonneg hθ0.le hθ1.le hm0 hm1)
      have h4 : bkl q m ≤ bkl q θ :=
        bkl_mono_right hq0.le (hqm.trans hm1).le hm0 hm1 h0 h1
          (mul_nonneg_of_nonpos_of_nonpos (by linarith [not_lt.1 hθ]) (by linarith))
      have := mul_le_mul_of_nonneg_left h4 ht.le
      linarith

end Regularity

/-! ### Tracking by the within-epoch rule (`app:ast-sequential`, "Tracking and forced
exploration") -/

section Tracking

variable {ι : Type*} [DecidableEq ι]

/-- Local count of terminal `i` after `n` draws of the selection sequence `sel`. -/
def selCount (sel : ℕ → ι) (i : ι) : ℕ → ℕ
  | 0 => 0
  | n + 1 => selCount sel i n + if sel n = i then 1 else 0

variable [Fintype ι]

lemma sum_selCount (sel : ℕ → ι) : ∀ n : ℕ, ∑ i, selCount sel i n = n
  | 0 => by simp [selCount]
  | n + 1 => by simp [selCount, sum_add_distrib, sum_selCount sel n]

/-- Invariant of the merge rule: after `n` draws there is a level `q` (the last selected key)
with `v_i q - 1 ≤ n_i ≤ v_i q` for every terminal. -/
lemma tracking_level (v : ι → ℝ) (hv : ∀ i, 0 < v i) (sel : ℕ → ι)
    (hrule : ∀ n i, ((selCount sel (sel n) n : ℝ) + 1) / v (sel n)
      ≤ ((selCount sel i n : ℝ) + 1) / v i) :
    ∀ n : ℕ, ∃ q : ℝ, ∀ i, (selCount sel i n : ℝ) ≤ v i * q ∧ v i * q ≤ selCount sel i n + 1
  | 0 => ⟨0, fun i => by simp [selCount]⟩
  | n + 1 => by
      obtain ⟨q, hq⟩ := tracking_level v hv sel hrule n
      refine ⟨((selCount sel (sel n) n : ℝ) + 1) / v (sel n), fun i => ?_⟩
      have hqq : q ≤ ((selCount sel (sel n) n : ℝ) + 1) / v (sel n) := by
        rw [le_div_iff₀ (hv (sel n)), mul_comm]
        exact (hq (sel n)).2
      have hr := hrule n i
      rw [div_le_div_iff₀ (hv (sel n)) (hv i)] at hr
      by_cases hi : sel n = i
      · subst hi
        have e : v (sel n) * (((selCount sel (sel n) n : ℝ) + 1) / v (sel n))
            = (selCount sel (sel n) n : ℝ) + 1 := by
          have := (hv (sel n)).ne'
          field_simp
        simp only [selCount, ite_true, Nat.cast_add, Nat.cast_one]
        rw [e]
        constructor <;> linarith
      · simp only [selCount, ite_eq_right hi, add_zero]
        constructor
        · exact (hq i).1.trans (mul_le_mul_of_nonneg_left hqq (hv i).le)
        · rw [mul_div_assoc', div_le_iff₀ (hv (sel n))]
          linarith

/-- **Tracking bound of the within-epoch rule.**  For a positive target `v` in the simplex and
any selection sequence that always draws a terminal minimizing `(n_i + 1)/v_i` (any
tie-breaking), after `n` draws
`n v_i - 1 ≤ n_i ≤ (n + M) v_i` for every `i`, and `∑_i |n_i - n v_i| ≤ 2M`. -/
theorem tracking_bounds (v : ι → ℝ) (hv : ∀ i, 0 < v i) (hv1 : ∑ i, v i = 1) (sel : ℕ → ι)
    (hrule : ∀ n i, ((selCount sel (sel n) n : ℝ) + 1) / v (sel n)
      ≤ ((selCount sel i n : ℝ) + 1) / v i) (n : ℕ) :
    (∀ i, (n : ℝ) * v i - 1 ≤ selCount sel i n ∧
      (selCount sel i n : ℝ) ≤ ((n : ℝ) + Fintype.card ι) * v i) ∧
    ∑ i, |(selCount sel i n : ℝ) - n * v i| ≤ 2 * Fintype.card ι := by
  obtain ⟨q, hq⟩ := tracking_level v hv sel hrule n
  have hsum : ((∑ i, selCount sel i n : ℕ) : ℝ) = n := by rw [sum_selCount]
  push_cast at hsum
  have h1 : (n : ℝ) ≤ q := by
    have := sum_le_sum (s := (univ : Finset ι)) fun i _ => (hq i).1
    rw [← sum_mul, hv1, one_mul, hsum] at this
    exact this
  have h2 : q ≤ (n : ℝ) + Fintype.card ι := by
    have := sum_le_sum (s := (univ : Finset ι)) fun i _ => (hq i).2
    rw [← sum_mul, hv1, one_mul, sum_add_distrib, hsum, sum_const, card_univ, nsmul_eq_mul,
      mul_one] at this
    exact this
  have hb : ∀ i, (n : ℝ) * v i - 1 ≤ selCount sel i n ∧
      (selCount sel i n : ℝ) ≤ ((n : ℝ) + Fintype.card ι) * v i := by
    intro i
    have h3 := mul_le_mul_of_nonneg_left h1 (hv i).le
    have h4 := mul_le_mul_of_nonneg_left h2 (hv i).le
    constructor
    · linarith [(hq i).2]
    · linarith [(hq i).1]
  refine ⟨hb, ?_⟩
  have habs : ∀ i, |(selCount sel i n : ℝ) - n * v i| ≤ 1 + Fintype.card ι * v i := by
    intro i
    have hM : (0 : ℝ) ≤ Fintype.card ι * v i := mul_nonneg (Nat.cast_nonneg _) (hv i).le
    rw [abs_le]
    constructor
    · linarith [(hb i).1]
    · linarith [(hb i).2]
  calc ∑ i, |(selCount sel i n : ℝ) - n * v i|
      ≤ ∑ i, (1 + Fintype.card ι * v i) := sum_le_sum fun i _ => habs i
    _ = 2 * Fintype.card ι := by
        rw [sum_add_distrib, ← mul_sum, hv1, sum_const, card_univ, nsmul_eq_mul]
        ring

end Tracking

namespace Stopped

/-! ### An anytime likelihood certificate (`app:ast-pair-certificate`) -/

section Certificate

variable {Z : Type*}

/-- `ever P l`: the predicate `P` holds at the history `l` or at one of its prefixes (earlier
histories of the same run). -/
def ever (P : List Bool → Prop) : List Bool → Prop
  | [] => P []
  | b :: h => P (b :: h) ∨ ever P h

lemma ever_self {P : List Bool → Prop} : ∀ {l : List Bool}, P l → ever P l
  | [], h => h
  | _ :: _, h => Or.inl h

lemma ever_mono {P Q : List Bool → Prop} (hPQ : ∀ h, P h → Q h) :
    ∀ {l : List Bool}, ever P l → ever Q l
  | [], h => hPQ _ h
  | _ :: _, h => h.elim (fun h1 => Or.inl (hPQ _ h1)) (fun h1 => Or.inr (ever_mono hPQ h1))

lemma ever_exists {ι : Type*} {P : ι → List Bool → Prop} :
    ∀ {l : List Bool}, ever (fun h => ∃ q, P q h) l → ∃ q, ever (P q) l
  | [], ⟨q, hq⟩ => ⟨q, hq⟩
  | _ :: _, h => by
      rcases h with ⟨q, hq⟩ | h1
      · exact ⟨q, Or.inl hq⟩
      · obtain ⟨q, hq⟩ := ever_exists h1
        exact ⟨q, Or.inr hq⟩

lemma ever_of_mem_leaves (S : Sampler Z) {P : List Bool → Prop} :
    ∀ (n : ℕ) (h l : List Bool), l ∈ leaves S n h → ever P h → ever P l
  | 0, h, l, hl, hP => by
      rw [leaves_zero, mem_singleton] at hl
      rwa [hl]
  | n + 1, h, l, hl, hP => by
      rw [leaves_succ] at hl
      split_ifs at hl with hs
      · rw [mem_singleton] at hl
        rwa [hl]
      · rcases mem_union.1 hl with h1 | h1
        · exact ever_of_mem_leaves S n _ l h1 (Or.inr hP)
        · exact ever_of_mem_leaves S n _ l h1 (Or.inr hP)

/-- Core of Ville's inequality on the tree of stopped histories. -/
lemma ville_tree_aux (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    {M : List Bool → ℝ} (hM0 : ∀ h, 0 ≤ M h)
    (hM : ∀ h, lik S μ (true :: h) * M (true :: h) + lik S μ (false :: h) * M (false :: h)
      ≤ lik S μ h * M h) {c : ℝ} (hc : 0 < c) :
    ∀ (n : ℕ) (h : List Bool), ¬ ever (fun h => c ≤ M h) h →
      c * ∑ l ∈ leaves S n h, {l | ever (fun h => c ≤ M h) l}.indicator (lik S μ) l
        ≤ lik S μ h * M h
  | 0, h, hP => by
      have hh : h ∉ {l | ever (fun h => c ≤ M h) l} := hP
      simp only [leaves_zero, sum_singleton, Set.indicator_of_notMem hh, mul_zero]
      exact mul_nonneg (lik_pos S hμ h).le (hM0 h)
  | n + 1, h, hP => by
      have hh : h ∉ {l | ever (fun h => c ≤ M h) l} := hP
      rw [sum_leaves_succ]
      split_ifs with hs
      · simp only [Set.indicator_of_notMem hh, mul_zero]
        exact mul_nonneg (lik_pos S hμ h).le (hM0 h)
      · have hchild : ∀ b : Bool,
            c * ∑ l ∈ leaves S n (b :: h), {l | ever (fun h => c ≤ M h) l}.indicator (lik S μ) l
              ≤ lik S μ (b :: h) * M (b :: h) := by
          intro b
          by_cases hb : ever (fun h => c ≤ M h) (b :: h)
          · have hcb : c ≤ M (b :: h) := hb.elim id (fun h1 => absurd h1 hP)
            have h1 : ∑ l ∈ leaves S n (b :: h),
                {l | ever (fun h => c ≤ M h) l}.indicator (lik S μ) l ≤ lik S μ (b :: h) := by
              rw [← sum_leaves_of_harmonic S (fun h _ => lik_harmonic S μ h) n (b :: h)]
              exact sum_le_sum fun l _ => indicator_le_of_pos _ (lik_pos S hμ l)
            have hl := (lik_pos S hμ (b :: h)).le
            nlinarith
          · exact ville_tree_aux S hμ hM0 hM hc n (b :: h) hb
        have := hchild true
        have := hchild false
        have := hM h
        linarith

/-- **Ville's inequality for the stopped history.**  If `M` is a nonnegative supermartingale
along the sampler's histories under `μ` (stated through the likelihood weights), then the
probability that `M` reaches level `c` at some time up to `τ ∧ n` is at most `M(∅)/c`. -/
theorem ville_tree (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    {M : List Bool → ℝ} (hM0 : ∀ h, 0 ≤ M h)
    (hM : ∀ h, lik S μ (true :: h) * M (true :: h) + lik S μ (false :: h) * M (false :: h)
      ≤ lik S μ h * M h) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    c * prob S μ n {l | ever (fun h => c ≤ M h) l} ≤ M [] := by
  by_cases h0 : ever (fun h => c ≤ M h) ([] : List Bool)
  · have h1 : c ≤ M [] := h0
    have h2 := prob_le_one S hμ n {l | ever (fun h => c ≤ M h) l}
    nlinarith
  · have := ville_tree_aux S hμ hM0 hM hc n [] h0
    simpa [lik, prob] using this

/-- Union bound for the law of the stopped history. -/
lemma prob_le_sum_of_subset (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    {ι : Type*} (F : Finset ι) (A : Set (List Bool)) (B : ι → Set (List Bool))
    (hAB : ∀ l ∈ A, ∃ q ∈ F, l ∈ B q) : prob S μ n A ≤ ∑ q ∈ F, prob S μ n (B q) := by
  unfold prob
  rw [sum_comm]
  refine sum_le_sum fun l _ => ?_
  by_cases hl : l ∈ A
  · obtain ⟨q, hq, hlq⟩ := hAB l hl
    rw [Set.indicator_of_mem hl]
    calc lik S μ l = (B q).indicator (lik S μ) l := (Set.indicator_of_mem hlq _).symm
      _ ≤ ∑ q ∈ F, (B q).indicator (lik S μ) l :=
        single_le_sum (f := fun q => (B q).indicator (lik S μ) l)
          (fun q _ => indicator_nonneg_of_pos _ (lik_pos S hμ l)) hq
  · rw [Set.indicator_of_notMem hl]
    exact sum_nonneg fun q _ => indicator_nonneg_of_pos _ (lik_pos S hμ l)

/-! #### The beta-mixture likelihood ratio -/

/-- `∫_0^1 q^k (1-q)^{n-k} dq = 1 / ((n+1) C(n,k))`, taken as the definition. -/
noncomputable def betaW (n k : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * (n.choose k : ℝ))

lemma betaW_pos {n k : ℕ} (hk : k ≤ n) : 0 < betaW n k := by
  have : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  unfold betaW
  positivity

/-- The recursion of the beta integrals, `B(n+1,k+1) + B(n+1,k) = B(n,k)`: the mixture
likelihood is a probability mass function. -/
lemma betaW_succ {n k : ℕ} (hk : k ≤ n) : betaW (n + 1) (k + 1) + betaW (n + 1) k = betaW n k := by
  have ha : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hx : (0 : ℝ) < (n + 1).choose (k + 1) := by
    exact_mod_cast Nat.choose_pos (Nat.succ_le_succ hk)
  have hy : (0 : ℝ) < (n + 1).choose k := by
    exact_mod_cast Nat.choose_pos (hk.trans (Nat.le_succ n))
  have e1 : ((n : ℝ) + 1) * (n.choose k : ℝ) = ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  have e2 : (n.choose k : ℝ) * ((n : ℝ) + 1) = ((n + 1).choose k : ℝ) * ((n : ℝ) + 1 - k) := by
    have h := Nat.choose_mul_succ_eq n k
    have hc : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by
      rw [Nat.cast_sub (hk.trans (Nat.le_succ n))]
      push_cast
      ring
    rw [← hc]
    exact_mod_cast h
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnk : (0 : ℝ) < (n : ℝ) + 1 - k := by
    have : (k : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  have ex : ((n + 1).choose (k + 1) : ℝ) = ((n : ℝ) + 1) * (n.choose k : ℝ) / ((k : ℝ) + 1) := by
    rw [eq_div_iff hk1.ne']
    exact e1.symm
  have ey : ((n + 1).choose k : ℝ) = (n.choose k : ℝ) * ((n : ℝ) + 1) / ((n : ℝ) + 1 - k) := by
    rw [eq_div_iff hnk.ne']
    exact e2.symm
  unfold betaW
  rw [ex, ey]
  push_cast
  field_simp
  ring

variable [DecidableEq Z]

/-- Number of successes observed at terminal `z` along a history. -/
def scnt (S : Sampler Z) (z : Z) : List Bool → ℕ
  | [] => 0
  | b :: h => scnt S z h + if S.next h = z then (if b then 1 else 0) else 0

lemma scnt_le_cnt (S : Sampler Z) (z : Z) : ∀ l : List Bool, scnt S z l ≤ cnt S z l
  | [] => le_rfl
  | b :: h => by
      have := scnt_le_cnt S z h
      simp only [scnt, cnt]
      split_ifs <;> omega

/-- Empirical mean `μ̂_z = S_z / N_z`, with the arbitrary value `1/2` when `N_z = 0`. -/
noncomputable def emp (S : Sampler Z) (z : Z) (l : List Bool) : ℝ :=
  if cnt S z l = 0 then 1 / 2 else (scnt S z l : ℝ) / (cnt S z l : ℝ)

lemma emp_mem_Icc (S : Sampler Z) (z : Z) (l : List Bool) : 0 ≤ emp S z l ∧ emp S z l ≤ 1 := by
  unfold emp
  split_ifs with h
  · constructor <;> norm_num
  · have h1 : (scnt S z l : ℝ) ≤ cnt S z l := by exact_mod_cast scnt_le_cnt S z l
    have h2 : (0 : ℝ) < cnt S z l := by exact_mod_cast Nat.pos_of_ne_zero h
    exact ⟨by positivity, (div_le_one h2).2 h1⟩

/-- One-terminal mixture likelihood ratio
`∫ q^{S}(1-q)^{N-S} dq / (μ^{S}(1-μ)^{N-S})`. -/
noncomputable def armW (S : Sampler Z) (μ : Z → ℝ) (i : Z) (h : List Bool) : ℝ :=
  betaW (cnt S i h) (scnt S i h)
    / (μ i ^ scnt S i h * (1 - μ i) ^ (cnt S i h - scnt S i h))

lemma armW_nil (S : Sampler Z) (μ : Z → ℝ) (i : Z) : armW S μ i [] = 1 := by
  simp [armW, betaW, cnt, scnt]

lemma armW_pos (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (i : Z)
    (h : List Bool) : 0 < armW S μ i h := by
  have h1 : 0 < 1 - μ i := sub_pos.2 (hμ i).2
  exact div_pos (betaW_pos (scnt_le_cnt S i h)) (mul_pos (pow_pos (hμ i).1 _) (pow_pos h1 _))

lemma armW_cons_of_ne (S : Sampler Z) (μ : Z → ℝ) {i : Z} {h : List Bool} (hne : S.next h ≠ i)
    (b : Bool) : armW S μ i (b :: h) = armW S μ i h := by
  simp [armW, cnt, scnt, hne]

/-- Martingale step of the one-terminal mixture at a request to that terminal. -/
lemma armW_step (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {i : Z}
    {h : List Bool} (he : S.next h = i) :
    μ i * armW S μ i (true :: h) + (1 - μ i) * armW S μ i (false :: h) = armW S μ i h := by
  have hk := scnt_le_cnt S i h
  have h0 := (hμ i).1
  have h1 : 0 < 1 - μ i := sub_pos.2 (hμ i).2
  have c1 : cnt S i (true :: h) = cnt S i h + 1 := by simp [cnt, he]
  have c2 : cnt S i (false :: h) = cnt S i h + 1 := by simp [cnt, he]
  have s1 : scnt S i (true :: h) = scnt S i h + 1 := by simp [scnt, he]
  have s2 : scnt S i (false :: h) = scnt S i h := by simp [scnt, he]
  unfold armW
  rw [c1, c2, s1, s2, ← betaW_succ hk]
  have e1 : cnt S i h + 1 - (scnt S i h + 1) = cnt S i h - scnt S i h := by omega
  have e2 : cnt S i h + 1 - scnt S i h = (cnt S i h - scnt S i h) + 1 := by omega
  rw [e1, e2, pow_succ, pow_succ]
  have hp1 := pow_pos h0 (scnt S i h)
  have hp2 := pow_pos h1 (cnt S i h - scnt S i h)
  field_simp

/-- Pair mixture martingale `𝓜_{jz}` of `app:ast-pair-certificate`. -/
noncomputable def pairM (S : Sampler Z) (μ : Z → ℝ) (j z : Z) (h : List Bool) : ℝ :=
  armW S μ j h * armW S μ z h

lemma pairM_nil (S : Sampler Z) (μ : Z → ℝ) (j z : Z) : pairM S μ j z [] = 1 := by
  simp [pairM, armW_nil]

lemma pairM_nonneg (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (j z : Z)
    (h : List Bool) : 0 ≤ pairM S μ j z h :=
  (mul_pos (armW_pos S hμ j h) (armW_pos S hμ z h)).le

/-- The pair mixture is a martingale under `μ` for every adaptive sampling rule. -/
lemma pairM_harmonic (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {j z : Z}
    (hjz : j ≠ z) (h : List Bool) :
    lik S μ (true :: h) * pairM S μ j z (true :: h)
        + lik S μ (false :: h) * pairM S μ j z (false :: h)
      = lik S μ h * pairM S μ j z h := by
  simp only [lik, bern_true, bern_false, pairM]
  by_cases hj : S.next h = j
  · have hz : S.next h ≠ z := fun e => hjz (hj.symm.trans e)
    rw [armW_cons_of_ne S μ hz, armW_cons_of_ne S μ hz, ← armW_step S hμ hj, hj]
    ring
  · by_cases hz : S.next h = z
    · rw [armW_cons_of_ne S μ hj, armW_cons_of_ne S μ hj, ← armW_step S hμ hz, hz]
      ring
    · rw [armW_cons_of_ne S μ hj, armW_cons_of_ne S μ hj, armW_cons_of_ne S μ hz,
        armW_cons_of_ne S μ hz]
      ring

lemma exp_nat_mul_log (k : ℕ) {x : ℝ} (hx : k = 0 ∨ 0 < x) : exp (k * log x) = x ^ k := by
  rcases hx with h | h
  · simp [h]
  · rw [Real.exp_nat_mul, exp_log h]

/-- Pathwise lower bound for the maximized likelihood ratio:
`exp(n kl(k/n, q)) ≤ 1 / (C(n,k) q^k (1-q)^{n-k})`. -/
lemma exp_mul_bkl_le {n k : ℕ} (hk : k ≤ n) (hn : n ≠ 0) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    exp (n * bkl ((k : ℝ) / n) q)
      ≤ 1 / ((n.choose k : ℝ) * (q ^ k * (1 - q) ^ (n - k))) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkr : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hq1' : 0 < 1 - q := sub_pos.2 hq1
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (k : ℝ) / n := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by rw [hp]; exact (div_le_one hnr).2 hkr
  have hnp : (n : ℝ) * p = k := by rw [hp]; field_simp
  have hnp' : (n : ℝ) * (1 - p) = ((n - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, mul_sub, mul_one, hnp]
  have e1 : (n : ℝ) * bkl p q
      = (k : ℝ) * log (p / q) + ((n - k : ℕ) : ℝ) * log ((1 - p) / (1 - q)) := by
    unfold bkl
    rw [mul_add, ← mul_assoc, ← mul_assoc, hnp, hnp']
  have hA : exp ((k : ℝ) * log (p / q)) = (p / q) ^ k := by
    refine exp_nat_mul_log k ?_
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inl h
    · right
      have : (0 : ℝ) < k := by exact_mod_cast h
      exact div_pos (by rw [hp]; positivity) hq0
  have hB : exp (((n - k : ℕ) : ℝ) * log ((1 - p) / (1 - q))) = ((1 - p) / (1 - q)) ^ (n - k) := by
    refine exp_nat_mul_log (n - k) ?_
    rcases Nat.eq_zero_or_pos (n - k) with h | h
    · exact Or.inl h
    · right
      have h2 : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast h
      rw [← hnp'] at h2
      have : 0 < 1 - p := by
        by_contra hcon
        have := mul_nonpos_of_nonneg_of_nonpos hnr.le (not_lt.1 hcon)
        linarith
      exact div_pos this hq1'
  rw [e1, exp_add, hA, hB, div_pow, div_pow]
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hch := choose_mul_pow_le_one hk hp0 hp1
  have hqq : 0 < q ^ k * (1 - q) ^ (n - k) := mul_pos (pow_pos hq0 _) (pow_pos hq1' _)
  rw [div_mul_div_comm, div_le_div_iff₀ hqq (mul_pos hC hqq)]
  have : p ^ k * (1 - p) ^ (n - k) * ((n.choose k : ℝ) * (q ^ k * (1 - q) ^ (n - k)))
      = ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) * (q ^ k * (1 - q) ^ (n - k)) := by ring
  rw [this, one_mul]
  exact mul_le_of_le_one_left hqq.le hch

/-- `W_i ≥ exp(N_i kl(μ̂_i, μ_i)) / (N_i + 1)`. -/
lemma armW_ge (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (i : Z)
    (h : List Bool) :
    exp ((cnt S i h : ℝ) * bkl (emp S i h) (μ i)) / ((cnt S i h : ℝ) + 1) ≤ armW S μ i h := by
  have hk := scnt_le_cnt S i h
  by_cases hn : cnt S i h = 0
  · have hs : scnt S i h = 0 := by omega
    simp [armW, betaW, hn, hs]
  · have h1 := exp_mul_bkl_le hk hn (hμ i).1 (hμ i).2
    have hemp : emp S i h = (scnt S i h : ℝ) / (cnt S i h : ℝ) := by simp [emp, hn]
    rw [hemp]
    have hN : (0 : ℝ) < (cnt S i h : ℝ) + 1 := by positivity
    have hC : (0 : ℝ) < (cnt S i h).choose (scnt S i h) := by exact_mod_cast Nat.choose_pos hk
    have hqq : 0 < μ i ^ scnt S i h * (1 - μ i) ^ (cnt S i h - scnt S i h) :=
      mul_pos (pow_pos (hμ i).1 _) (pow_pos (sub_pos.2 (hμ i).2) _)
    have e : armW S μ i h = 1 / ((((cnt S i h).choose (scnt S i h) : ℕ) : ℝ)
        * (μ i ^ scnt S i h * (1 - μ i) ^ (cnt S i h - scnt S i h))) / ((cnt S i h : ℝ) + 1) := by
      unfold armW betaW
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h1 hN.le

variable [Fintype Z]

/-- Pair statistic `G_{jz}(t) = F_ε(μ̂_j, μ̂_z; N_j, N_z)` (`eq:ast-glr`). -/
noncomputable def certStat (S : Sampler Z) (ε : ℝ) (j z : Z) (h : List Bool) : ℝ :=
  pairF ε (emp S j h) (emp S z h) (cnt S j h) (cnt S z h)

/-- Threshold `β_{jz}(t,δ) = log(M(M-1)/δ) + log(N_j+1) + log(N_z+1)`
(`eq:ast-threshold`), `M = |Z|`. -/
noncomputable def certThr (S : Sampler Z) (δ : ℝ) (j z : Z) (h : List Bool) : ℝ :=
  log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ)
    + log ((cnt S j h : ℝ) + 1) + log ((cnt S z h : ℝ) + 1)

/-- The certification rule: some witness `j` in the support `T` passes the pair test against
every outside terminal. -/
def certifies (S : Sampler Z) (ε δ : ℝ) (T : Finset Z) (h : List Bool) : Prop :=
  ∃ j ∈ T, ∀ z, z ∉ T → certThr S δ j z h ≤ certStat S ε j z h

/-- If the true pair is an alternative, crossing the threshold forces the mixture martingale
above `M(M-1)/δ`. -/
lemma pairM_ge_of_cross (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) {j z : Z} (hjz : j ≠ z) (halt : μ j + ε < μ z) {h : List Bool}
    (hcross : certThr S δ j z h ≤ certStat S ε j z h) :
    (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ ≤ pairM S μ j z h := by
  have hcard : (2 : ℝ) ≤ Fintype.card Z := by
    have : 1 < Fintype.card Z := Fintype.one_lt_card_iff.2 ⟨j, z, hjz⟩
    exact_mod_cast this
  have hc : 0 < (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ :=
    div_pos (mul_pos (by linarith) (by linarith)) hδ
  have hNj : (0 : ℝ) < (cnt S j h : ℝ) + 1 := by positivity
  have hNz : (0 : ℝ) < (cnt S z h : ℝ) + 1 := by positivity
  have hG : certStat S ε j z h
      ≤ (cnt S j h : ℝ) * bkl (emp S j h) (μ j) + (cnt S z h : ℝ) * bkl (emp S z h) (μ z) :=
    pairF_le_of_alt hε (emp_mem_Icc S j h).1 (emp_mem_Icc S j h).2 (emp_mem_Icc S z h).1
      (emp_mem_Icc S z h).2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (hμ j).1 (hμ z).2 halt
  have h1 := armW_ge S hμ j h
  have h2 := armW_ge S hμ z h
  have hexp : (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ
        * (((cnt S j h : ℝ) + 1) * ((cnt S z h : ℝ) + 1))
      ≤ exp ((cnt S j h : ℝ) * bkl (emp S j h) (μ j))
        * exp ((cnt S z h : ℝ) * bkl (emp S z h) (μ z)) := by
    rw [← exp_add]
    have : exp (certThr S δ j z h) = (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ
        * (((cnt S j h : ℝ) + 1) * ((cnt S z h : ℝ) + 1)) := by
      unfold certThr
      rw [exp_add, exp_add, exp_log hc, exp_log hNj, exp_log hNz]
      ring
    rw [← this]
    exact exp_le_exp.2 (hcross.trans hG)
  have hprod : exp ((cnt S j h : ℝ) * bkl (emp S j h) (μ j)) / ((cnt S j h : ℝ) + 1)
        * (exp ((cnt S z h : ℝ) * bkl (emp S z h) (μ z)) / ((cnt S z h : ℝ) + 1))
      ≤ pairM S μ j z h :=
    mul_le_mul h1 h2 (div_nonneg (exp_pos _).le hNz.le) (armW_pos S hμ j h).le
  refine le_trans ?_ hprod
  rw [div_mul_div_comm, le_div_iff₀ (mul_pos hNj hNz)]
  exact hexp

/-- **Anytime likelihood certificate** (`app:ast-pair-certificate`).  For every deterministic
adaptive sampler `S` (arbitrary sampling rule and stopping rule), interior means `μ`, accuracy
`ε ≥ 0` and `δ > 0`: the probability that, at some time up to `τ ∧ n`, the pair test
`eq:ast-glr`--`eq:ast-threshold` certifies some support `T` that is `ε`-incorrect under `μ`
(`μ ∈ Alt_ε(T)`), through any witness `j ∈ T`, is at most `δ`.  This holds for every horizon
`n`, with no factor for the number of actions or of query times. -/
theorem anytime_certificate (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (n : ℕ) :
    prob S μ n {l | ever (fun h => ∃ T : Finset Z, μ ∈ Alt T ε ∧ certifies S ε δ T h) l}
      ≤ δ := by
  classical
  set c : ℝ := (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ with hcdef
  set F : Finset (Z × Z) :=
    (univ : Finset Z).offDiag.filter (fun q => μ q.1 + ε < μ q.2) with hF
  have hsub : ∀ l ∈ {l | ever (fun h => ∃ T : Finset Z, μ ∈ Alt T ε ∧ certifies S ε δ T h) l},
      ∃ q ∈ F, l ∈ {l | ever (fun h => c ≤ pairM S μ q.1 q.2 h) l} := by
    intro l hl
    have h1 : ever (fun h => ∃ q : {q : Z × Z // q ∈ F}, c ≤ pairM S μ q.1.1 q.1.2 h) l := by
      refine ever_mono (fun h => ?_) hl
      rintro ⟨T, ⟨-, z, hz, hlt⟩, j, hj, hcert⟩
      have hjz : j ≠ z := fun e => hz (e ▸ hj)
      have hq : (j, z) ∈ F := by
        rw [hF, mem_filter, mem_offDiag]
        exact ⟨⟨mem_univ _, mem_univ _, hjz⟩, hlt j hj⟩
      exact ⟨⟨(j, z), hq⟩, pairM_ge_of_cross S hμ hε hδ hjz (hlt j hj) (hcert z hz)⟩
    obtain ⟨q, hq⟩ := ever_exists h1
    exact ⟨q.1, q.2, hq⟩
  refine (prob_le_sum_of_subset S hμ n F _ _ hsub).trans ?_
  rcases F.eq_empty_or_nonempty with hFe | ⟨q0, hq0⟩
  · rw [hFe, sum_empty]
    exact hδ.le
  have hq0' := (mem_offDiag.1 (mem_filter.1 hq0).1).2.2
  have hcard : (2 : ℝ) ≤ Fintype.card Z := by
    have : 1 < Fintype.card Z := Fintype.one_lt_card_iff.2 ⟨q0.1, q0.2, hq0'⟩
    exact_mod_cast this
  have hMM : 0 < (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hc : 0 < c := div_pos hMM hδ
  have hterm : ∀ q ∈ F, prob S μ n {l | ever (fun h => c ≤ pairM S μ q.1 q.2 h) l} ≤ 1 / c := by
    intro q hq
    have hne := (mem_offDiag.1 (mem_filter.1 hq).1).2.2
    have hv := ville_tree S hμ (M := pairM S μ q.1 q.2) (pairM_nonneg S hμ q.1 q.2)
      (fun h => (pairM_harmonic S hμ hne h).le) hc n
    rw [pairM_nil] at hv
    rw [le_div_iff₀ hc]
    linarith
  have hFcard : (F.card : ℝ) ≤ (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) := by
    have h1 : F.card ≤ (univ : Finset Z).offDiag.card := card_le_card (filter_subset _ _)
    rw [offDiag_card, card_univ] at h1
    have h2 : ((Fintype.card Z * Fintype.card Z - Fintype.card Z : ℕ) : ℝ)
        = (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) := by
      rw [Nat.cast_sub (Nat.le_mul_self _)]
      push_cast
      ring
    rw [← h2]
    exact_mod_cast h1
  calc ∑ q ∈ F, prob S μ n {l | ever (fun h => c ≤ pairM S μ q.1 q.2 h) l}
      ≤ ∑ _q ∈ F, 1 / c := sum_le_sum hterm
    _ = F.card * (1 / c) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) * (1 / c) :=
        mul_le_mul_of_nonneg_right hFcard (by positivity)
    _ = δ := by
        rw [hcdef]
        generalize (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) = X at hMM ⊢
        field_simp

/-- **`δ`-correct stopping.**  If a sampler stops only when its returned support `dec l` is
certified by the pair test, then the probability that it stops and returns an `ε`-incorrect
action is at most `δ`, at every interior parameter. -/
theorem certified_stopping_correct (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (dec : List Bool → Finset Z)
    (hstop : ∀ l, S.stop l = true → certifies S ε δ (dec l) l) :
    probInf S μ {l | μ ∈ Alt (dec l) ε} ≤ δ := by
  refine ciSup_le fun n => ?_
  refine (prob_mono_set S hμ n ?_).trans (anytime_certificate S hμ hε hδ n)
  rintro l ⟨hl, hs⟩
  exact ever_self ⟨dec l, hl, hstop l hs⟩

end Certificate

/-! ### A lower bound that permits several correct answers (`app:ast-lower`) -/

section MultiAnswer

variable {Z : Type*}

lemma length_le_of_mem_leaves (S : Sampler Z) :
    ∀ (n : ℕ) (h l : List Bool), l ∈ leaves S n h → l.length ≤ h.length + n
  | 0, h, l, hl => by
      rw [leaves_zero, mem_singleton] at hl
      rw [hl]
      exact le_rfl
  | n + 1, h, l, hl => by
      rw [leaves_succ] at hl
      split_ifs at hl with hs
      · rw [mem_singleton] at hl
        rw [hl]
        omega
      · rcases mem_union.1 hl with h1 | h1
        · have := length_le_of_mem_leaves S n _ _ h1
          simp only [List.length_cons] at this
          omega
        · have := length_le_of_mem_leaves S n _ _ h1
          simp only [List.length_cons] at this
          omega

lemma prob_compl (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) (A : Set (List Bool)) :
    prob S μ n A + prob S μ n Aᶜ = 1 := by
  rw [← sum_lik_leaves S μ n]
  unfold prob
  rw [← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  by_cases h : l ∈ A <;> simp [h]

/-- Variance of the one-observation log-likelihood ratio `log(f_p(X)/f_q(X))`, `X ∼ Bern(p)`. -/
noncomputable def llrVar (p q : ℝ) : ℝ :=
  p * (log (p / q) - bkl p q) ^ 2 + (1 - p) * (log ((1 - p) / (1 - q)) - bkl p q) ^ 2

lemma llrVar_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ llrVar p q :=
  add_nonneg (mul_nonneg hp0 (sq_nonneg _)) (mul_nonneg (sub_nonneg.2 hp1) (sq_nonneg _))

variable [DecidableEq Z] [Fintype Z]

/-- The centred log-likelihood ratio `M(λ) = ℓ(λ) - ∑_z N_z kl(μ_z, λ_z)` along a history. -/
noncomputable def mart (S : Sampler Z) (μ lam : Z → ℝ) (l : List Bool) : ℝ :=
  pathLLR S μ lam l - ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z)

/-- Its predictable quadratic variation `∑_z N_z Var_z`. -/
noncomputable def qvar (S : Sampler Z) (μ lam : Z → ℝ) (l : List Bool) : ℝ :=
  ∑ z, (cnt S z l : ℝ) * llrVar (μ z) (lam z)

/-- Wald's second identity at a bounded horizon: `E_μ[M_{τ∧n}²] = E_μ[⟨M⟩_{τ∧n}]`. -/
lemma second_moment_mart (S : Sampler Z) (μ lam : Z → ℝ) (n : ℕ) :
    ∑ l ∈ leaves S n [], lik S μ l * mart S μ lam l ^ 2
      = ∑ l ∈ leaves S n [], lik S μ l * qvar S μ lam l := by
  have h0 := sum_leaves_of_harmonic S
    (g := fun l => lik S μ l * (mart S μ lam l ^ 2 - qvar S μ lam l))
    (by
      intro h _
      simp only [lik, mart, qvar, pathLLR, sum_cnt_cons, bern_true, bern_false]
      unfold llrVar bkl
      ring) n []
  have m0 : mart S μ lam [] = 0 := by simp [mart, pathLLR, cnt]
  have q0 : qvar S μ lam [] = 0 := by simp [qvar, cnt]
  rw [m0, q0] at h0
  simp only [mul_sub, sum_sub_distrib] at h0
  have e0 : lik S μ [] * (0 : ℝ) ^ 2 - lik S μ [] * 0 = 0 := by norm_num
  linarith

/-- Chebyshev's inequality for the centred log-likelihood ratio at the stopped history:
`y² P_μ(M_{τ∧n} > y) ≤ c n` when every one-step variance is at most `c`. -/
lemma chebyshev_mart (S : Sampler Z) {μ lam : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {c : ℝ}
    (hc : ∀ z, llrVar (μ z) (lam z) ≤ c) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ 2 * prob S μ n {l | y < mart S μ lam l} ≤ c * n := by
  have h1 : y ^ 2 * prob S μ n {l | y < mart S μ lam l}
      ≤ ∑ l ∈ leaves S n [], lik S μ l * mart S μ lam l ^ 2 := by
    unfold prob
    rw [mul_sum]
    refine sum_le_sum fun l _ => ?_
    have hl := (lik_pos S hμ l).le
    by_cases hm : y < mart S μ lam l
    · rw [Set.indicator_of_mem (show l ∈ {l | y < mart S μ lam l} from hm), mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy.le hm.le 2) hl
    · rw [Set.indicator_of_notMem (show l ∉ {l | y < mart S μ lam l} from hm), mul_zero]
      exact mul_nonneg hl (sq_nonneg _)
  rw [second_moment_mart] at h1
  refine h1.trans ?_
  have h2 : ∀ l ∈ leaves S n [], lik S μ l * qvar S μ lam l ≤ lik S μ l * (c * n) := by
    intro l hl
    refine mul_le_mul_of_nonneg_left ?_ (lik_pos S hμ l).le
    have hlen : (l.length : ℝ) ≤ n := by
      have := length_le_of_mem_leaves S n [] l hl
      simp only [List.length_nil, zero_add] at this
      exact_mod_cast this
    have hc0 : 0 ≤ c := by
      rcases isEmpty_or_nonempty Z with hE | ⟨⟨z⟩⟩
      · have : l.length = 0 := by
          rw [← sum_cnt S l]
          simp
        by_contra hneg
        exact absurd (llrVar_nonneg (hμ (S.next [])).1.le (hμ (S.next [])).2.le)
          (not_le.2 (lt_of_le_of_lt (hc _) (not_le.1 hneg)))
      · exact (llrVar_nonneg (hμ z).1.le (hμ z).2.le).trans (hc z)
    calc qvar S μ lam l ≤ ∑ z, (cnt S z l : ℝ) * c :=
          sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hc z) (Nat.cast_nonneg _)
      _ = c * (l.length : ℝ) := by
          rw [← sum_mul, ← Nat.cast_sum, sum_cnt, mul_comm]
      _ ≤ c * n := mul_le_mul_of_nonneg_left hlen hc0
  calc ∑ l ∈ leaves S n [], lik S μ l * qvar S μ lam l
      ≤ ∑ l ∈ leaves S n [], lik S μ l * (c * n) := sum_le_sum h2
    _ = c * n := by rw [← sum_mul, sum_lik_leaves, one_mul]

/-- Change of measure on a stopping-time event on which the log-likelihood ratio is bounded,
plus the deviation event of the centred log-likelihood ratio. -/
lemma prob_event_le (S : Sampler Z) {μ lam : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) (n : ℕ) (D : Set (List Bool)) {x b : ℝ} :
    prob S μ n ((D ∩ {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) ≤ b}) ∩ stopSet S)
      ≤ exp x * prob S lam n (D ∩ stopSet S) + prob S μ n {l | x - b < mart S μ lam l} := by
  unfold prob
  rw [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun l _ => ?_
  have h1 := lik_pos S hμ l
  have h2 := lik_pos S hlam l
  have hn2 : 0 ≤ exp x * (D ∩ stopSet S).indicator (lik S lam) l :=
    mul_nonneg (exp_pos _).le (indicator_nonneg_of_pos _ h2)
  have hn3 : 0 ≤ {l | x - b < mart S μ lam l}.indicator (lik S μ) l :=
    indicator_nonneg_of_pos _ h1
  by_cases hl : l ∈ (D ∩ {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) ≤ b}) ∩ stopSet S
  · rw [Set.indicator_of_mem hl]
    obtain ⟨⟨hD, hb⟩, hs⟩ := hl
    by_cases hx : pathLLR S μ lam l ≤ x
    · have e : lik S μ l = lik S lam l * exp (pathLLR S μ lam l) := by
        rw [← log_lik_div S hμ hlam l, exp_log (div_pos h1 h2)]
        field_simp
      rw [Set.indicator_of_mem (show l ∈ D ∩ stopSet S from ⟨hD, hs⟩)]
      have : lik S lam l * exp (pathLLR S μ lam l) ≤ exp x * lik S lam l := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (exp_le_exp.2 hx) h2.le
      linarith
    · have hm : l ∈ {l | x - b < mart S μ lam l} := by
        show x - b < mart S μ lam l
        have hb' : ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) ≤ b := hb
        unfold mart
        linarith [not_le.1 hx]
      rw [Set.indicator_of_mem hm]
      linarith
  · rw [Set.indicator_of_notMem hl]
    linarith

variable [Nonempty Z]

/-- **Finite-confidence core of the multiple-answer lower bound.**  `P` is a finite list of
pairs (answer, alternative).  Assume: each listed alternative is interior, the sampler returns
the listed answer with probability at most `δ` under it, its one-step log-likelihood-ratio
variances are at most `c`; and every answer `a` and allocation `w` has a listed alternative of
cost at most `C'`.  Then for every horizon `T` and level `x > T C'`,
`P_μ(τ ≤ T) ≤ |P| (e^x δ + c T / (x - T C')²)`. -/
theorem multi_answer_finite {A : Type*} (S : Sampler Z) (dec : List Bool → A) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (P : Finset (A × (Z → ℝ))) {δ C' c x : ℝ} (T : ℕ)
    (hPint : ∀ q ∈ P, ∀ z, 0 < q.2 z ∧ q.2 z < 1)
    (hPδ : ∀ q ∈ P, probInf S q.2 {l | dec l = q.1} ≤ δ)
    (hPc : ∀ q ∈ P, ∀ z, llrVar (μ z) (q.2 z) ≤ c)
    (hcover : ∀ a, ∀ w ∈ simplex Z, ∃ lam, (a, lam) ∈ P ∧ infoCost w μ lam ≤ C')
    (hx : T * C' < x) :
    prob S μ T (stopSet S) ≤ P.card * (exp x * δ + c * T / (x - T * C') ^ 2) := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hy : 0 < x - T * C' := sub_pos.2 hx
  -- every stopped history is assigned to a listed pair
  have hsub : ∀ l ∈ stopSet S ∩ ↑(leaves S T []),
      ∃ q ∈ P, l ∈ ({l | dec l = q.1} ∩
        {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (q.2 z) ≤ T * C'}) ∩ stopSet S := by
    rintro l ⟨hs, hl⟩
    have hlen : (l.length : ℝ) ≤ T := by
      have := length_le_of_mem_leaves S T [] l hl
      simp only [List.length_nil, zero_add] at this
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos l.length with h0 | h0
    · obtain ⟨lam, hq, hcost⟩ := hcover (dec l) _ uniform_mem_simplex
      have hC0 : 0 ≤ C' :=
        (infoCost_nonneg (fun _ => by positivity) hμ' (hPint _ hq)).trans hcost
      refine ⟨(dec l, lam), hq, ⟨rfl, ?_⟩, hs⟩
      have hz : ∀ z, cnt S z l = 0 := fun z => by
        have := sum_cnt S l
        rw [h0] at this
        exact (Finset.sum_eq_zero_iff.1 this) z (mem_univ z)
      show ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) ≤ T * C'
      simp only [hz, Nat.cast_zero, zero_mul, sum_const_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hC0
    · have hL : (0 : ℝ) < l.length := by exact_mod_cast h0
      have hw : (fun z => (cnt S z l : ℝ) / l.length) ∈ simplex Z := by
        refine ⟨fun z => by positivity, ?_⟩
        rw [← sum_div, ← Nat.cast_sum, sum_cnt, div_self hL.ne']
      obtain ⟨lam, hq, hcost⟩ := hcover (dec l) _ hw
      have hC0 : 0 ≤ C' := (infoCost_nonneg hw.1 hμ' (hPint _ hq)).trans hcost
      refine ⟨(dec l, lam), hq, ⟨rfl, ?_⟩, hs⟩
      show ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) ≤ T * C'
      have e : ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z)
          = l.length * infoCost (fun z => (cnt S z l : ℝ) / l.length) μ lam := by
        unfold infoCost
        rw [mul_sum]
        refine sum_congr rfl fun z _ => ?_
        field_simp
      rw [e]
      calc (l.length : ℝ) * infoCost (fun z => (cnt S z l : ℝ) / l.length) μ lam
          ≤ l.length * C' := mul_le_mul_of_nonneg_left hcost hL.le
        _ ≤ T * C' := mul_le_mul_of_nonneg_right hlen hC0
  have hstep : prob S μ T (stopSet S)
      ≤ ∑ q ∈ P, prob S μ T (({l | dec l = q.1} ∩
        {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (q.2 z) ≤ T * C'}) ∩ stopSet S) := by
    have h1 : prob S μ T (stopSet S) = prob S μ T (stopSet S ∩ ↑(leaves S T [])) := by
      unfold prob
      refine sum_congr rfl fun l hl => ?_
      by_cases hs : l ∈ stopSet S
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show l ∈ stopSet S ∩ _ from ⟨hs, hl⟩)]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (show l ∉ stopSet S ∩ _ from fun h => hs h.1)]
    rw [h1]
    exact prob_le_sum_of_subset S hμ T P _ _ hsub
  refine hstep.trans ?_
  have hterm : ∀ q ∈ P, prob S μ T (({l | dec l = q.1} ∩
        {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (q.2 z) ≤ T * C'}) ∩ stopSet S)
      ≤ exp x * δ + c * T / (x - T * C') ^ 2 := by
    intro q hq
    have h1 := prob_event_le S hμ (hPint q hq) T {l | dec l = q.1} (x := x) (b := T * C')
    have h2 : prob S q.2 T ({l | dec l = q.1} ∩ stopSet S) ≤ δ :=
      (prob_le_probInf S (hPint q hq) T _).trans (hPδ q hq)
    have h3 := chebyshev_mart S hμ (hPc q hq) T hy
    have h4 : prob S μ T {l | x - T * C' < mart S μ q.2 l} ≤ c * T / (x - T * C') ^ 2 := by
      rw [le_div_iff₀ (pow_pos hy 2)]
      linarith
    have h5 := mul_le_mul_of_nonneg_left h2 (exp_pos x).le
    linarith
  calc ∑ q ∈ P, prob S μ T (({l | dec l = q.1} ∩
        {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (q.2 z) ≤ T * C'}) ∩ stopSet S)
      ≤ ∑ _q ∈ P, (exp x * δ + c * T / (x - T * C') ^ 2) := sum_le_sum hterm
    _ = P.card * (exp x * δ + c * T / (x - T * C') ^ 2) := by rw [sum_const, nsmul_eq_mul]

/-- `C_*^ε(μ) = max_a C_a^ε(μ)` for a finite family of root supports. -/
noncomputable def charStar {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z) (ε : ℝ)
    (μ : Z → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun a => charRate (Sup a) ε μ

lemma charRate_le_charStar {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z) (ε : ℝ)
    (μ : Z → ℝ) (a : A) : charRate (Sup a) ε μ ≤ charStar Sup ε μ :=
  le_sup' (fun a => charRate (Sup a) ε μ) (mem_univ a)

lemma continuous_infoCost (μ lam : Z → ℝ) : Continuous fun w : Z → ℝ => infoCost w μ lam := by
  unfold infoCost
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

/-- Compactness step: a finite list of alternatives (inside a prescribed domain on which the
information infimum is unchanged) that serves every allocation up to `ζ`. -/
lemma exists_finite_alternatives {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (Dom : Set (Z → ℝ))
    (hdense : ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt S ε, lam ∈ Dom ∧
      infoCost w μ lam < infoRate S ε w μ + η) {C ζ : ℝ} (hC : charRate S ε μ ≤ C)
    (hζ : 0 < ζ) :
    ∃ Λ : Finset (Z → ℝ), (∀ lam ∈ Λ, lam ∈ Alt S ε ∧ lam ∈ Dom) ∧
      ∀ w ∈ simplex Z, ∃ lam ∈ Λ, infoCost w μ lam ≤ C + ζ := by
  classical
  let U : {lam : Z → ℝ // lam ∈ Alt S ε ∧ lam ∈ Dom} → Set (Z → ℝ) :=
    fun lam => {w | infoCost w μ lam.1 < C + ζ}
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt (continuous_infoCost μ i.1) continuous_const
  have hcov : simplex Z ⊆ ⋃ i, U i := by
    intro w hw
    obtain ⟨lam, hlam, hD, hlt⟩ := hdense w hw ζ hζ
    have := le_charRate (S := S) hSc hε0 hε1 hμ hw
    exact Set.mem_iUnion.2 ⟨⟨lam, hlam, hD⟩, show infoCost w μ lam < C + ζ by linarith⟩
  obtain ⟨t, ht⟩ := (isCompact_simplex Z).elim_finite_subcover U hUo hcov
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro lam hlam
    obtain ⟨i, -, rfl⟩ := mem_image.1 hlam
    exact i.2
  · intro w hw
    obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 (ht hw)
    exact ⟨i.1, mem_image_of_mem _ hi, le_of_lt hwi⟩

/-- Elementary limit used to pass from the finite-confidence bound to the rate. -/
lemma tendsto_rate_factor (a K c' κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun L : ℝ => (a - 1 / L) * (1 - K * (exp (-(κ / 2) * L) + c' / L))) atTop
      (𝓝 a) := by
  have h1 : Tendsto (fun L : ℝ => 1 / L) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h2 : Tendsto (fun L : ℝ => c' / L) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c'
  have h3 : Tendsto (fun L : ℝ => exp (-(κ / 2) * L)) atTop (𝓝 0) := by
    refine tendsto_exp_atBot.comp ?_
    exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h4 := (tendsto_const_nhds (x := a)).sub h1
  have h5 := (tendsto_const_nhds (x := (1 : ℝ))).sub ((h3.add h2).const_mul K)
  have h6 := h4.mul h5
  simpa using h6

/-- **Lower bound with several correct answers** (`eq:ast-lower-main`), finite-horizon form.

`S δ`, `dec δ` is a family of deterministic adaptive samplers with decision rules into a finite
family of proper root supports `Sup`.  `Dom` is the parameter domain on which correctness is
required; `hdense` says that restricting alternatives to `Dom` leaves every information
infimum unchanged (trivial for `Dom = univ`; this is the perturbation remark of the manuscript
for `ε = 0`).  `hcorr` is uniform correctness: for `0 < δ < 1` and every interior parameter in
`Dom`, the sampler stops and returns an answer that is not `ε`-incorrect with probability at
least `1 - δ`.  No fixed answer is assumed to be returned with high probability.

Conclusion: for every `c₀ < 1 / C_*^ε(μ)`, for all sufficiently small `δ` there is a horizon
`n` with `E_μ[τ_δ ∧ n] ≥ c₀ log(1/δ)`. -/
theorem lower_bound_multi_answer_trunc {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup ε μ)
    (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A) (Dom : Set (Z → ℝ))
    (hdense : ∀ a, ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt (Sup a) ε, lam ∈ Dom ∧
      infoCost w μ lam < infoRate (Sup a) ε w μ + η)
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ Dom, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (Sup (dec δ l)) ε})
    {c₀ : ℝ} (hc₀ : c₀ < 1 / charStar Sup ε μ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ n, c₀ * log (1 / δ) ≤ expTime (S δ) μ n := by
  classical
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = charStar Sup ε μ := ⟨_, rfl⟩
  rw [← hCdef] at hC hc₀
  have hc₀C : c₀ * C < 1 := by rwa [lt_div_iff₀ hC] at hc₀
  -- the slack `κ`
  obtain ⟨κ, hκ0, hκ1, hκc⟩ : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧ c₀ < (1 - κ) / C := by
    refine ⟨min (1 / 2) ((1 - c₀ * C) / 2), lt_min (by norm_num) (by linarith), min_le_left _ _,
      ?_⟩
    rw [lt_div_iff₀ hC]
    have := min_le_right (1 / 2 : ℝ) ((1 - c₀ * C) / 2)
    linarith
  have hκ' : 0 < 1 - κ := by linarith
  set ζ : ℝ := κ * C / (4 * (1 - κ)) with hζdef
  have hζ : 0 < ζ := by positivity
  -- finite lists of alternatives
  have hlist : ∀ a, ∃ Λ : Finset (Z → ℝ), (∀ lam ∈ Λ, lam ∈ Alt (Sup a) ε ∧ lam ∈ Dom) ∧
      ∀ w ∈ simplex Z, ∃ lam ∈ Λ, infoCost w μ lam ≤ C + ζ := fun a =>
    exists_finite_alternatives (hSc a) hε0 hε1 hμ' Dom (hdense a)
      (hCdef ▸ charRate_le_charStar Sup ε μ a) hζ
  choose Λ hΛ hΛcov using hlist
  set P : Finset (A × (Z → ℝ)) := univ.biUnion fun a => (Λ a).image fun lam => (a, lam) with hP
  have hPmem : ∀ q, q ∈ P ↔ q.2 ∈ Λ q.1 := by
    rintro ⟨a, lam⟩
    simp only [hP, mem_biUnion, mem_univ, true_and, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨a', lam', hl, rfl, rfl⟩
      exact hl
    · intro hl
      exact ⟨a, lam, hl, rfl, rfl⟩
  have hPint : ∀ q ∈ P, ∀ z, 0 < q.2 z ∧ q.2 z < 1 := fun q hq =>
    (hΛ q.1 q.2 ((hPmem q).1 hq)).1.1
  have hcover : ∀ a, ∀ w ∈ simplex Z, ∃ lam, (a, lam) ∈ P ∧ infoCost w μ lam ≤ C + ζ := by
    intro a w hw
    obtain ⟨lam, hl, hc⟩ := hΛcov a w hw
    exact ⟨lam, (hPmem (a, lam)).2 hl, hc⟩
  -- uniform variance bound
  set c : ℝ := ∑ q ∈ P, ∑ z, llrVar (μ z) (q.2 z) with hcdef
  have hPc : ∀ q ∈ P, ∀ z, llrVar (μ z) (q.2 z) ≤ c := by
    intro q hq z
    have h1 : llrVar (μ z) (q.2 z) ≤ ∑ z, llrVar (μ z) (q.2 z) :=
      single_le_sum (f := fun z => llrVar (μ z) (q.2 z))
        (fun z _ => llrVar_nonneg (hμ' z).1 (hμ' z).2) (mem_univ z)
    have h2 : ∑ z, llrVar (μ z) (q.2 z) ≤ c :=
      single_le_sum (f := fun q : A × (Z → ℝ) => ∑ z, llrVar (μ z) (q.2 z))
        (fun q _ => sum_nonneg fun z _ => llrVar_nonneg (hμ' z).1 (hμ' z).2) hq
    exact h1.trans h2
  have hc0 : 0 ≤ c :=
    sum_nonneg fun q _ => sum_nonneg fun z _ => llrVar_nonneg (hμ' z).1 (hμ' z).2
  -- the limit
  set c' : ℝ := 16 * c * (1 - κ) / (C * κ ^ 2) with hc'def
  have hlim := tendsto_rate_factor ((1 - κ) / C) P.card c' κ hκ0
  have hev1 : ∀ᶠ L : ℝ in atTop,
      c₀ < ((1 - κ) / C - 1 / L) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L)) :=
    hlim.eventually_const_lt hκc
  have hlim2 : Tendsto (fun L : ℝ => 1 - P.card * (exp (-(κ / 2) * L) + c' / L)) atTop
      (𝓝 1) := by
    have := tendsto_rate_factor 1 P.card c' κ hκ0
    have h1 : Tendsto (fun L : ℝ => 1 / L) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h2 : Tendsto (fun L : ℝ => c' / L) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c'
    have h3 : Tendsto (fun L : ℝ => exp (-(κ / 2) * L)) atTop (𝓝 0) := by
      refine tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ((h3.add h2).const_mul (P.card : ℝ))
  have hev2 : ∀ᶠ L : ℝ in atTop, 0 < 1 - P.card * (exp (-(κ / 2) * L) + c' / L) :=
    hlim2.eventually_const_lt zero_lt_one
  have hLtend : Tendsto (fun δ : ℝ => log (1 / δ)) (𝓝[>] 0) atTop := by
    have : Tendsto (fun δ : ℝ => -log δ) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
    refine this.congr fun δ => ?_
    rw [one_div, log_inv]
  have hδ1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hLtend.eventually hev1, hLtend.eventually hev2, hδ1] with δ h1 h2 hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  obtain ⟨L, hL⟩ : ∃ L, L = log (1 / δ) := ⟨_, rfl⟩
  rw [← hL] at h1 h2 ⊢
  have hLpos : 0 < L := by
    rw [hL]
    exact log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hδexp : δ = exp (-L) := by
    rw [hL, one_div, log_inv, neg_neg, exp_log hδ0]
  -- the horizon and the level
  set T : ℕ := ⌊(1 - κ) * L / C⌋₊ with hT
  have hTle : (T : ℝ) ≤ (1 - κ) * L / C := Nat.floor_le (by positivity)
  have hTge : (1 - κ) * L / C - 1 < T := by
    have := Nat.lt_floor_add_one ((1 - κ) * L / C)
    linarith
  set x : ℝ := (1 - κ / 2) * L with hxdef
  have hTC : (T : ℝ) * (C + ζ) ≤ (1 - κ) * L + κ * L / 4 := by
    have h := mul_le_mul_of_nonneg_right hTle (add_pos hC hζ).le
    have e : (1 - κ) * L / C * (C + ζ) = (1 - κ) * L + κ * L / 4 := by
      rw [hζdef]
      field_simp
    linarith
  have hy : κ * L / 4 ≤ x - T * (C + ζ) := by
    rw [hxdef]
    linarith
  have hyp : 0 < κ * L / 4 := by positivity
  have hx : (T : ℝ) * (C + ζ) < x := by linarith
  -- correctness at the listed alternatives
  have hPδ : ∀ q ∈ P, probInf (S δ) q.2 {l | dec δ l = q.1} ≤ δ := by
    intro q hq
    obtain ⟨hqA, hqD⟩ := hΛ q.1 q.2 ((hPmem q).1 hq)
    have hc := hcorr δ hδ0 hδ1 q.2 hqD hqA.1
    have hdis : Disjoint {l : List Bool | dec δ l = q.1}
        {l | q.2 ∉ Alt (Sup (dec δ l)) ε} :=
      Set.disjoint_left.2 fun l h1 h2 => by
        rw [Set.mem_ofPred_eq] at h1 h2
        rw [h1] at h2
        exact h2 hqA
    have := probInf_add_le_one (S δ) hqA.1 hdis
    linarith
  have hfin := multi_answer_finite (S δ) (dec δ) hμ P T hPint hPδ hPc hcover hx
  -- simplify the bound
  have hb1 : exp x * δ = exp (-(κ / 2) * L) := by
    rw [hδexp, ← exp_add, hxdef]
    congr 1
    ring
  have hb2 : c * T / (x - T * (C + ζ)) ^ 2 ≤ c' / L := by
    have h3 : c * (T : ℝ) ≤ c * ((1 - κ) * L / C) := mul_le_mul_of_nonneg_left hTle hc0
    have h4 : (κ * L / 4) ^ 2 ≤ (x - T * (C + ζ)) ^ 2 := pow_le_pow_left₀ hyp.le hy 2
    have h5 : c * T / (x - T * (C + ζ)) ^ 2 ≤ c * ((1 - κ) * L / C) / (κ * L / 4) ^ 2 :=
      div_le_div₀ (mul_nonneg hc0 (by positivity)) h3 (pow_pos hyp 2) h4
    have e : c * ((1 - κ) * L / C) / (κ * L / 4) ^ 2 = c' / L := by
      rw [hc'def]
      field_simp
      ring
    linarith
  have hprob : prob (S δ) μ T (stopSet (S δ)) ≤ P.card * (exp (-(κ / 2) * L) + c' / L) := by
    refine hfin.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [hb1]
    linarith
  have hns : 1 - P.card * (exp (-(κ / 2) * L) + c' / L)
      ≤ prob (S δ) μ T (stopSet (S δ))ᶜ := by
    have := prob_compl (S δ) μ T (stopSet (S δ))
    linarith
  have hmark := prob_not_stop_mul_le (S δ) hμ T
  refine ⟨T, ?_⟩
  have hfac := h2.le
  have h6 : ((1 - κ) * L / C - 1) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L))
      ≤ prob (S δ) μ T (stopSet (S δ))ᶜ * T := by
    calc ((1 - κ) * L / C - 1) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L))
        ≤ (T : ℝ) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L)) :=
          mul_le_mul_of_nonneg_right hTge.le hfac
      _ ≤ (T : ℝ) * prob (S δ) μ T (stopSet (S δ))ᶜ :=
          mul_le_mul_of_nonneg_left hns (Nat.cast_nonneg _)
      _ = prob (S δ) μ T (stopSet (S δ))ᶜ * T := mul_comm _ _
  have e7 : ((1 - κ) * L / C - 1) = L * ((1 - κ) / C - 1 / L) := by
    field_simp
  rw [e7, mul_assoc] at h6
  have h8 : c₀ * L ≤ L * (((1 - κ) / C - 1 / L)
      * (1 - P.card * (exp (-(κ / 2) * L) + c' / L))) := by
    rw [mul_comm c₀ L]
    exact mul_le_mul_of_nonneg_left h1.le hLpos.le
  linarith

/-- **`eq:ast-lower-main`** for the expected stopping time.  Under the hypotheses of
`lower_bound_multi_answer_trunc` and finite expected stopping time at `μ` for every `δ`
(`hB`; if it is infinite the manuscript's bound is trivial), for every `c₀ < 1 / C_*^ε(μ)`
and all sufficiently small `δ`, `E_μ[τ_δ] / log(1/δ) ≥ c₀`. -/
theorem lower_bound_multi_answer {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup ε μ)
    (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A) (Dom : Set (Z → ℝ))
    (hdense : ∀ a, ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt (Sup a) ε, lam ∈ Dom ∧
      infoCost w μ lam < infoRate (Sup a) ε w μ + η)
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ Dom, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (Sup (dec δ l)) ε})
    (hB : ∀ δ, ∃ B, ∀ n, expTime (S δ) μ n ≤ B)
    {c₀ : ℝ} (hc₀ : c₀ < 1 / charStar Sup ε μ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), c₀ ≤ expTimeInf (S δ) μ / log (1 / δ) := by
  have h := lower_bound_multi_answer_trunc Sup hSc hε0 hε1 hμ hC S dec Dom hdense hcorr hc₀
  have hδ1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [h, hδ1] with δ hn hδ
  obtain ⟨n, hn⟩ := hn
  obtain ⟨B, hB'⟩ := hB δ
  have hle : expTime (S δ) μ n ≤ expTimeInf (S δ) μ :=
    le_ciSup (f := fun n => expTime (S δ) μ n) ⟨B, by rintro _ ⟨m, rfl⟩; exact hB' m⟩ n
  have hL : 0 < log (1 / δ) := log_pos (by rw [lt_div_iff₀ hδ.1]; linarith [hδ.2])
  rw [le_div_iff₀ hL]
  linarith

/-- **`eq:ast-lower-main`** as the manuscript writes it:
`liminf_{δ ↓ 0} E_μ[τ_δ] / log(1/δ) ≥ 1 / C_*^ε(μ)`.  The lower limit is taken in the extended
reals (the ratio need not be bounded).  Hypotheses as in `lower_bound_multi_answer`. -/
theorem lower_bound_liminf {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup ε μ)
    (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A) (Dom : Set (Z → ℝ))
    (hdense : ∀ a, ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt (Sup a) ε, lam ∈ Dom ∧
      infoCost w μ lam < infoRate (Sup a) ε w μ + η)
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ Dom, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (Sup (dec δ l)) ε})
    (hB : ∀ δ, ∃ B, ∀ n, expTime (S δ) μ n ≤ B) :
    ((1 / charStar Sup ε μ : ℝ) : EReal)
      ≤ Filter.liminf (fun δ : ℝ => ((expTimeInf (S δ) μ / log (1 / δ) : ℝ) : EReal))
          (𝓝[>] 0) := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  induction c using EReal.rec with
  | bot => exact bot_le
  | coe r =>
    have hr : r < 1 / charStar Sup ε μ := EReal.coe_lt_coe_iff.1 hc
    have h := lower_bound_multi_answer Sup hSc hε0 hε1 hμ hC S dec Dom hdense hcorr hB hr
    exact Filter.le_liminf_of_le (by isBoundedDefault)
      (h.mono fun δ hδ => EReal.coe_le_coe_iff.2 hδ)
  | top => exact absurd hc (not_lt.2 le_top)

/-- For the full interior domain `𝒟_ε = (0,1)^M` (the case `ε > 0`) the density hypothesis of
the lower bound is the definition of the infimum. -/
lemma alt_dense_univ {S : Finset Z} (hSc : Sᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (w μ : Z → ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ lam ∈ Alt S ε, lam ∈ (Set.univ : Set (Z → ℝ)) ∧
      infoCost w μ lam < infoRate S ε w μ + η := by
  obtain ⟨_, ⟨lam, hlam, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt ((alt_nonempty hSc hε0 hε1).image (infoCost w μ))
      (lt_add_of_pos_right (infoRate S ε w μ) hη)
  exact ⟨lam, hlam, Set.mem_univ _, hlt⟩

/-- The domain `𝒟_0 = {Γ > 0}` of exact identification: some action's best inside terminal
strictly beats every terminal outside its support. -/
def exactDomain {A : Type*} (Sup : A → Finset Z) : Set (Z → ℝ) :=
  {lam | ∃ a, ∃ y ∈ Sup a, ∀ z, z ∉ Sup a → lam z < lam y}

/-- A strict alternative can be perturbed arbitrarily slightly to have pairwise distinct
terminal means while remaining a strict alternative. -/
lemma exists_alt_injective {S : Finset Z} {ε : ℝ} {w μ lam : Z → ℝ} (hlam : lam ∈ Alt S ε)
    {b : ℝ} (hb : infoCost w μ lam < b) :
    ∃ lam' ∈ Alt S ε, Function.Injective lam' ∧ infoCost w μ lam' < b := by
  classical
  obtain ⟨hint, z, hz, hlt⟩ := hlam
  let e : Z → ℝ := fun i => ((Fintype.equivFin Z i : ℕ) : ℝ)
  have he : Function.Injective e := fun i j hij => by
    have h0 : (((Fintype.equivFin Z i : ℕ)) : ℝ) = ((Fintype.equivFin Z j : ℕ) : ℝ) := hij
    have h1 : ((Fintype.equivFin Z i : ℕ)) = (Fintype.equivFin Z j : ℕ) := by exact_mod_cast h0
    exact (Fintype.equivFin Z).injective (Fin.ext h1)
  have hc : ∀ i, ContinuousAt (fun t : ℝ => lam i + t * e i) 0 := fun i =>
    continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hc0 : ∀ i, (fun t : ℝ => lam i + t * e i) 0 = lam i := fun i => by simp
  have ev1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < lam i + t * e i ∧ lam i + t * e i < 1 := by
    refine eventually_all.2 fun i => ?_
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < lam i + t * e i :=
      (hc i).eventually (eventually_gt_nhds (by rw [hc0]; exact (hint i).1))
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), lam i + t * e i < 1 :=
      (hc i).eventually (eventually_lt_nhds (by rw [hc0]; exact (hint i).2))
    exact h1.and h2
  have ev2 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ S, lam y + t * e y + ε < lam z + t * e z := by
    refine (eventually_all_finset S).2 fun y hy => ?_
    have hcd : ContinuousAt (fun t : ℝ => (lam z + t * e z) - (lam y + t * e y + ε)) 0 :=
      (hc z).sub ((hc y).add continuousAt_const)
    have := hcd.eventually (eventually_gt_nhds (by
      show (0 : ℝ) < (lam z + 0 * e z) - (lam y + 0 * e y + ε)
      linarith [hlt y hy]))
    exact this.mono fun t ht => by linarith
  have ev3 : ∀ᶠ t in 𝓝 (0 : ℝ), infoCost w μ (fun i => lam i + t * e i) < b := by
    have hcc : ContinuousAt (fun t : ℝ => infoCost w μ (fun i => lam i + t * e i)) 0 := by
      unfold infoCost
      refine tendsto_finsetSum _ fun i _ => ContinuousAt.mul continuousAt_const ?_
      have h1 : ContinuousAt (fun x => bkl (μ i) x) ((fun t : ℝ => lam i + t * e i) 0) := by
        rw [hc0]
        exact continuousAt_bkl (μ i) (hint i).1 (hint i).2
      exact ContinuousAt.comp (f := fun t : ℝ => lam i + t * e i) h1 (hc i)
    refine hcc.eventually (eventually_lt_nhds ?_)
    simpa using hb
  set Bad : Finset ℝ :=
    (univ : Finset (Z × Z)).image fun q => (lam q.2 - lam q.1) / (e q.1 - e q.2) with hBad
  have ev4 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∉ (Bad.erase 0 : Finset ℝ) := by
    have hcl : IsClosed ((Bad.erase 0 : Finset ℝ) : Set ℝ) := (Finset.finite_toSet _).isClosed
    have : ((Bad.erase 0 : Finset ℝ) : Set ℝ)ᶜ ∈ 𝓝 (0 : ℝ) :=
      hcl.isOpen_compl.mem_nhds (by simp)
    exact this
  have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((∀ i, 0 < lam i + t * e i ∧ lam i + t * e i < 1) ∧
        (∀ y ∈ S, lam y + t * e y + ε < lam z + t * e z) ∧
        infoCost w μ (fun i => lam i + t * e i) < b ∧ t ∉ (Bad.erase 0 : Finset ℝ)) ∧ 0 < t :=
    ((ev1.and (ev2.and (ev3.and ev4))).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ⟨h1, h2, h3, h4⟩, ht⟩ := ev.exists
  refine ⟨fun i => lam i + t * e i, ⟨h1, z, hz, h2⟩, ?_, h3⟩
  intro i j hij
  by_contra hne
  have hij' : lam i + t * e i = lam j + t * e j := hij
  have hee : e i - e j ≠ 0 := sub_ne_zero.2 fun h => hne (he h)
  have htq : t = (lam j - lam i) / (e i - e j) := by
    rw [eq_div_iff hee]
    linarith
  have hmem : t ∈ Bad := by
    rw [hBad, mem_image]
    exact ⟨(i, j), mem_univ _, htq.symm⟩
  exact h4 (mem_erase.2 ⟨ht.ne', hmem⟩)

/-- Restricting alternatives to `𝒟_0` leaves the information infimum unchanged, when the
supports cover `Z` (the perturbation remark of `app:ast-lower`). -/
lemma alt_dense_exactDomain {A : Type*} (Sup : A → Finset Z) (hcov : ∀ z, ∃ a, z ∈ Sup a)
    (a : A) (hSc : (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (w μ : Z → ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ lam ∈ Alt (Sup a) ε, lam ∈ exactDomain Sup ∧
      infoCost w μ lam < infoRate (Sup a) ε w μ + η := by
  obtain ⟨lam0, hlam0, -, hlt0⟩ := alt_dense_univ hSc hε0 hε1 w μ hη
  obtain ⟨lam, hlam, hinj, hlt⟩ := exists_alt_injective hlam0 hlt0
  refine ⟨lam, hlam, ?_, hlt⟩
  obtain ⟨y, -, hy⟩ := exists_max_image (univ : Finset Z) lam univ_nonempty
  obtain ⟨a', ha'⟩ := hcov y
  refine ⟨a', y, ha', fun z hz => lt_of_le_of_ne (hy z (mem_univ z)) fun h => ?_⟩
  exact hz (hinj h ▸ ha')

/-- **`eq:ast-lower-main` for `ε > 0` (and for any `ε ∈ [0,1)` when correctness holds on all of
`(0,1)^M`).**  Every family of samplers that is uniformly correct on the interior parameters
satisfies `liminf_{δ↓0} E_μ τ_δ / log(1/δ) ≥ 1 / C_*^ε(μ)`. -/
theorem ast_lower_main {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup ε μ)
    (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A)
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam : Z → ℝ, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (Sup (dec δ l)) ε})
    (hB : ∀ δ, ∃ B, ∀ n, expTime (S δ) μ n ≤ B) :
    ((1 / charStar Sup ε μ : ℝ) : EReal)
      ≤ Filter.liminf (fun δ : ℝ => ((expTimeInf (S δ) μ / log (1 / δ) : ℝ) : EReal))
          (𝓝[>] 0) :=
  lower_bound_liminf Sup hSc hε0 hε1 hμ hC S dec Set.univ
    (fun a w _ _ hη => alt_dense_univ (hSc a) hε0 hε1 w μ hη)
    (fun δ h0 h1 lam _ hlam => hcorr δ h0 h1 lam hlam) hB

/-- **`eq:ast-lower-main` for exact identification** (`ε = 0`): correctness is required only
on `𝒟_0 = {Γ > 0}`; the supports are proper and cover `Z`. -/
theorem ast_lower_main_exact {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ Sup a) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup 0 μ)
    (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A)
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ exactDomain Sup, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (Sup (dec δ l)) 0})
    (hB : ∀ δ, ∃ B, ∀ n, expTime (S δ) μ n ≤ B) :
    ((1 / charStar Sup 0 μ : ℝ) : EReal)
      ≤ Filter.liminf (fun δ : ℝ => ((expTimeInf (S δ) μ / log (1 / δ) : ℝ) : EReal))
          (𝓝[>] 0) :=
  lower_bound_liminf Sup hSc le_rfl zero_lt_one hμ hC S dec (exactDomain Sup)
    (fun a w _ _ hη => alt_dense_exactDomain Sup hcov a (hSc a) le_rfl zero_lt_one w μ hη)
    hcorr hB

/-- **Parameter modulus of `C_*^ε`**: `|C_*^ε(p) - C_*^ε(p')| ≤ ω_ε(‖p - p'‖_∞)` for
`p, p' ∈ [0,1]^M` with `‖p - p'‖_∞ ≤ 1/2`. -/
theorem charStar_modulus {A : Type*} [Fintype A] [Nonempty A] (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {p p' : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hp' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1) (hd : ‖p - p'‖ ≤ 1 / 2) :
    |charStar Sup ε p - charStar Sup ε p'| ≤ omega ε ‖p - p'‖ := by
  have h := fun a => abs_le.1 (charRate_modulus (hSc a) hε0 hε1 hp hp' hd)
  rw [abs_le]
  constructor
  · have : charStar Sup ε p' ≤ charStar Sup ε p + omega ε ‖p - p'‖ :=
      sup'_le _ _ fun a _ => by
        have := charRate_le_charStar Sup ε p a
        linarith [(h a).1]
    linarith
  · have : charStar Sup ε p ≤ charStar Sup ε p' + omega ε ‖p - p'‖ :=
      sup'_le _ _ fun a _ => by
        have := charRate_le_charStar Sup ε p' a
        linarith [(h a).2]
    linarith

end MultiAnswer

end Stopped

end JointRootCert
