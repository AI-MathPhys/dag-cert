/-
Seed averaging: the measure-theoretic facts used to pass from deterministic adaptive samplers
to randomised ones.

A randomised procedure is a deterministic procedure indexed by a seed `s` drawn from a
probability measure `ν`; its probabilities and expectations are `ν`-averages of those of the
deterministic procedures.  This file contains the three facts about such averages that the
randomised forms of `lem:active-com` "Stopped Bernoulli change of measure" (and of its Gaussian
analogue) rest on:

* `two_point_le_bkl`: the two-point Donsker--Varadhan inequality, converse of
  `bkl_le_of_two_point`;
* `two_point_integral` (Jensen for the two-point functional), `bkl_integral_le_of_le` and
  `bkl_integral_convex`: joint convexity of the binary divergence in integral form,
  `kl(∫ p dν, ∫ q dν) ≤ ∫ kl(p, q) dν`;
* `mono_limit`: monotone convergence for a nondecreasing sequence of real functions with
  bounded integrals (used for `E[N_z(τ ∧ n)] ↑ E[N_z(τ)]` after averaging over the seed).

Used by `Randomised.lean` (Bernoulli) and `RandomisedGauss.lean` (Gaussian).
-/
import JointRootCert.BernoulliInfo

namespace JointRootCert

namespace Rand

open MeasureTheory Filter Topology Real
open scoped ENNReal

/-- **Two-point Donsker--Varadhan inequality**: for `p, q ∈ [0,1]` with `p > 0 → q > 0` and
`p < 1 → q < 1`, and all reals `a, b`,
`a p + b (1 - p) - log (eᵃ q + eᵇ (1 - q)) ≤ kl(p, q)`. -/
theorem two_point_le_bkl {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpq0 : 0 < p → 0 < q) (hpq1 : p < 1 → q < 1) (a b : ℝ) :
    a * p + b * (1 - p) - log (exp a * q + exp b * (1 - q)) ≤ bkl p q := by
  have ha := exp_pos a
  have hb := exp_pos b
  rcases hp0.eq_or_lt with h0 | h0
  · subst h0
    have hq1' : q < 1 := hpq1 zero_lt_one
    have hb' : bkl 0 q = log (1 / (1 - q)) := by simp [bkl]
    rw [hb', one_div, log_inv]
    have h1 : exp b * (1 - q) ≤ exp a * q + exp b * (1 - q) := by
      have := mul_nonneg ha.le hq0
      linarith
    have h2 := log_le_log (mul_pos hb (sub_pos.2 hq1')) h1
    rw [log_mul hb.ne' (sub_pos.2 hq1').ne', log_exp] at h2
    linarith
  rcases hp1.eq_or_lt with h1 | h1
  · subst h1
    have hq0' : 0 < q := hpq0 one_pos
    have hb' : bkl 1 q = log (1 / q) := by simp [bkl]
    rw [hb', one_div, log_inv]
    have h1 : exp a * q ≤ exp a * q + exp b * (1 - q) := by
      have := mul_nonneg hb.le (sub_nonneg.2 hq1)
      linarith
    have h2 := log_le_log (mul_pos ha hq0') h1
    rw [log_mul ha.ne' hq0'.ne', log_exp] at h2
    linarith
  · have hq0' := hpq0 h0
    have hq1' := hpq1 h1
    have h1p : 0 < 1 - p := sub_pos.2 h1
    have h1q : 0 < 1 - q := sub_pos.2 hq1'
    have hx : 0 < exp a * q / p := div_pos (mul_pos ha hq0') h0
    have hy : 0 < exp b * (1 - q) / (1 - p) := div_pos (mul_pos hb h1q) h1p
    have J := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) h0.le
      h1p.le (by ring : p + (1 - p) = 1)
    simp only [smul_eq_mul] at J
    have e : p * (exp a * q / p) + (1 - p) * (exp b * (1 - q) / (1 - p))
        = exp a * q + exp b * (1 - q) := by
      field_simp
    rw [e] at J
    rw [log_div (mul_pos ha hq0').ne' h0.ne', log_mul ha.ne' hq0'.ne', log_exp,
      log_div (mul_pos hb h1q).ne' h1p.ne', log_mul hb.ne' h1q.ne', log_exp] at J
    unfold bkl
    rw [log_div h0.ne' hq0'.ne', log_div h1p.ne' h1q.ne']
    nlinarith

variable {Sd : Type*} [MeasurableSpace Sd]

/-- **Jensen step for the two-point functional.**  If
`a p_s + b (1 - p_s) - log (eᵃ q_s + eᵇ (1 - q_s)) ≤ K_s` for every seed `s`, then the same
inequality holds for the `ν`-averages of `p`, `q`, `K` (the logarithm is concave). -/
theorem two_point_integral (ν : Measure Sd) [IsProbabilityMeasure ν] {p q K : Sd → ℝ}
    (hp : Measurable p) (hq : Measurable q) (hp01 : ∀ s, 0 ≤ p s ∧ p s ≤ 1)
    (hq01 : ∀ s, 0 ≤ q s ∧ q s ≤ 1) (hK : Integrable K ν) (a b : ℝ)
    (h : ∀ s, a * p s + b * (1 - p s) - log (exp a * q s + exp b * (1 - q s)) ≤ K s) :
    a * (∫ s, p s ∂ν) + b * (1 - ∫ s, p s ∂ν)
        - log (exp a * (∫ s, q s ∂ν) + exp b * (1 - ∫ s, q s ∂ν)) ≤ ∫ s, K s ∂ν := by
  have ha := exp_pos a
  have hb := exp_pos b
  have hpi : Integrable p ν :=
    Integrable.of_mem_Icc 0 1 hp.aemeasurable (ae_of_all _ fun s => ⟨(hp01 s).1, (hp01 s).2⟩)
  have hqi : Integrable q ν :=
    Integrable.of_mem_Icc 0 1 hq.aemeasurable (ae_of_all _ fun s => ⟨(hq01 s).1, (hq01 s).2⟩)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (exp a) (exp b) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact lt_min ha hb
  obtain ⟨X, hX⟩ : ∃ X : Sd → ℝ, X = fun s => exp a * q s + exp b * (1 - q s) := ⟨_, rfl⟩
  have hXm : ∀ s, m ≤ X s := by
    intro s
    have h1 : m ≤ exp a := by rw [hm]; exact min_le_left _ _
    have h2 : m ≤ exp b := by rw [hm]; exact min_le_right _ _
    have h3 := mul_le_mul_of_nonneg_right h1 (hq01 s).1
    have h4 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 (hq01 s).2)
    rw [hX]
    show m ≤ exp a * q s + exp b * (1 - q s)
    nlinarith
  have hXM : ∀ s, X s ≤ exp a + exp b := by
    intro s
    have h3 := mul_le_mul_of_nonneg_left (hq01 s).2 ha.le
    have h4 := mul_le_mul_of_nonneg_left (sub_le_self 1 (hq01 s).1) hb.le
    rw [hX]
    show exp a * q s + exp b * (1 - q s) ≤ exp a + exp b
    linarith
  have hXmeas : Measurable X := by
    rw [hX]
    exact (hq.const_mul _).add ((measurable_const.sub hq).const_mul _)
  have hXi : Integrable X ν :=
    Integrable.of_mem_Icc m (exp a + exp b) hXmeas.aemeasurable
      (ae_of_all _ fun s => ⟨hXm s, hXM s⟩)
  have hlogi : Integrable (log ∘ X) ν :=
    Integrable.of_mem_Icc (log m) (log (exp a + exp b))
      (measurable_log.comp hXmeas).aemeasurable
      (ae_of_all _ fun s => ⟨log_le_log hm0 (hXm s), log_le_log (hm0.trans_le (hXm s)) (hXM s)⟩)
  have hconc : ConcaveOn ℝ (Set.Ici m) log :=
    strictConcaveOn_log_Ioi.concaveOn.subset (fun x hx => hm0.trans_le hx) (convex_Ici m)
  have hcont : ContinuousOn log (Set.Ici m) :=
    continuousOn_log.mono fun x hx => (hm0.trans_le hx).ne'
  have J := hconc.le_map_integral hcont isClosed_Ici (ae_of_all _ fun s => hXm s) hXi hlogi
  have hq1i : Integrable (fun s => 1 - q s) ν := (integrable_const (1 : ℝ)).sub hqi
  have hp1i : Integrable (fun s => 1 - p s) ν := (integrable_const (1 : ℝ)).sub hpi
  have eq1 : ∫ s, (1 - q s) ∂ν = 1 - ∫ s, q s ∂ν := by
    rw [integral_sub (integrable_const (1 : ℝ)) hqi]
    simp
  have ep1 : ∫ s, (1 - p s) ∂ν = 1 - ∫ s, p s ∂ν := by
    rw [integral_sub (integrable_const (1 : ℝ)) hpi]
    simp
  have hAi : Integrable (fun s => exp a * q s) ν := hqi.const_mul _
  have hBi : Integrable (fun s => exp b * (1 - q s)) ν := hq1i.const_mul _
  have eX : ∫ s, X s ∂ν = exp a * (∫ s, q s ∂ν) + exp b * (1 - ∫ s, q s ∂ν) := by
    rw [hX]
    show ∫ s, (exp a * q s + exp b * (1 - q s)) ∂ν = _
    rw [integral_add hAi hBi, integral_const_mul, integral_const_mul, eq1]
  rw [eX] at J
  have hCi : Integrable (fun s => a * p s) ν := hpi.const_mul _
  have hDi : Integrable (fun s => b * (1 - p s)) ν := hp1i.const_mul _
  have hEi : Integrable (fun s => a * p s + b * (1 - p s)) ν := hCi.add hDi
  have hlogi' : Integrable (fun s => log (X s)) ν := hlogi
  have hLi : Integrable (fun s => a * p s + b * (1 - p s) - log (X s)) ν := hEi.sub hlogi'
  have hmono := integral_mono hLi hK (fun s => by
    have := h s
    rw [hX]
    exact this)
  have eL : ∫ s, (a * p s + b * (1 - p s) - log (X s)) ∂ν
      = a * (∫ s, p s ∂ν) + b * (1 - ∫ s, p s ∂ν) - ∫ s, log (X s) ∂ν := by
    rw [integral_sub hEi hlogi', integral_add hCi hDi, integral_const_mul, integral_const_mul,
      ep1]
  rw [eL] at hmono
  have J' : ∫ s, log (X s) ∂ν ≤ log (exp a * (∫ s, q s ∂ν) + exp b * (1 - ∫ s, q s ∂ν)) := J
  linarith

/-- Averages of `[0,1]`-valued functions: positivity transfers along a pointwise implication. -/
lemma integral_pos_of_imp (ν : Measure Sd) [IsProbabilityMeasure ν] {p q : Sd → ℝ}
    (hp : Measurable p) (hq : Measurable q) (hp01 : ∀ s, 0 ≤ p s ∧ p s ≤ 1)
    (hq01 : ∀ s, 0 ≤ q s ∧ q s ≤ 1) (himp : ∀ᵐ s ∂ν, 0 < p s → 0 < q s)
    (h : 0 < ∫ s, p s ∂ν) : 0 < ∫ s, q s ∂ν := by
  have hpi : Integrable p ν :=
    Integrable.of_mem_Icc 0 1 hp.aemeasurable (ae_of_all _ fun s => ⟨(hp01 s).1, (hp01 s).2⟩)
  have hqi : Integrable q ν :=
    Integrable.of_mem_Icc 0 1 hq.aemeasurable (ae_of_all _ fun s => ⟨(hq01 s).1, (hq01 s).2⟩)
  rw [integral_pos_iff_support_of_nonneg (fun s => (hp01 s).1) hpi] at h
  rw [integral_pos_iff_support_of_nonneg (fun s => (hq01 s).1) hqi]
  refine h.trans_le (measure_mono_ae ?_)
  filter_upwards [himp] with s hs hsp
  have h1 : p s ≠ 0 := hsp
  have h2 : 0 < p s := lt_of_le_of_ne (hp01 s).1 (Ne.symm h1)
  exact (hs h2).ne'

/-- **Joint convexity of the binary divergence, integral form with a majorant.**  If
`kl(p_s, q_s) ≤ K_s` for every seed, with `p_s, q_s ∈ [0,1]`, `p_s > 0 → q_s > 0` and
`p_s < 1 → q_s < 1`, then `kl(∫ p dν, ∫ q dν) ≤ ∫ K dν`. -/
theorem bkl_integral_le_of_le (ν : Measure Sd) [IsProbabilityMeasure ν] {p q K : Sd → ℝ}
    (hp : Measurable p) (hq : Measurable q) (hp01 : ∀ s, 0 ≤ p s ∧ p s ≤ 1)
    (hq01 : ∀ s, 0 ≤ q s ∧ q s ≤ 1) (hpq0 : ∀ s, 0 < p s → 0 < q s)
    (hpq1 : ∀ s, p s < 1 → q s < 1) (hK : Integrable K ν)
    (h : ∀ s, bkl (p s) (q s) ≤ K s) :
    bkl (∫ s, p s ∂ν) (∫ s, q s ∂ν) ≤ ∫ s, K s ∂ν := by
  have hpi : Integrable p ν :=
    Integrable.of_mem_Icc 0 1 hp.aemeasurable (ae_of_all _ fun s => ⟨(hp01 s).1, (hp01 s).2⟩)
  have hqi : Integrable q ν :=
    Integrable.of_mem_Icc 0 1 hq.aemeasurable (ae_of_all _ fun s => ⟨(hq01 s).1, (hq01 s).2⟩)
  have hP0 : 0 ≤ ∫ s, p s ∂ν := integral_nonneg fun s => (hp01 s).1
  have hQ0 : 0 ≤ ∫ s, q s ∂ν := integral_nonneg fun s => (hq01 s).1
  have hP1 : ∫ s, p s ∂ν ≤ 1 := by
    have := integral_mono hpi (integrable_const (1 : ℝ)) fun s => (hp01 s).2
    simpa using this
  have hQ1 : ∫ s, q s ∂ν ≤ 1 := by
    have := integral_mono hqi (integrable_const (1 : ℝ)) fun s => (hq01 s).2
    simpa using this
  refine bkl_le_of_two_point hP0 hP1 hQ0 hQ1 ?_ ?_ fun a b => ?_
  · exact integral_pos_of_imp ν hp hq hp01 hq01 (ae_of_all _ hpq0)
  · intro hlt
    have ep1 : ∫ s, (1 - p s) ∂ν = 1 - ∫ s, p s ∂ν := by
      rw [integral_sub (integrable_const (1 : ℝ)) hpi]
      simp
    have eq1 : ∫ s, (1 - q s) ∂ν = 1 - ∫ s, q s ∂ν := by
      rw [integral_sub (integrable_const (1 : ℝ)) hqi]
      simp
    have h1 : 0 < ∫ s, (1 - p s) ∂ν := by
      rw [ep1]
      linarith
    have h2 : 0 < ∫ s, (1 - q s) ∂ν :=
      integral_pos_of_imp ν (p := fun s => 1 - p s) (q := fun s => 1 - q s)
        (measurable_const.sub hp) (measurable_const.sub hq)
        (fun s => ⟨sub_nonneg.2 (hp01 s).2, sub_le_self 1 (hp01 s).1⟩)
        (fun s => ⟨sub_nonneg.2 (hq01 s).2, sub_le_self 1 (hq01 s).1⟩)
        (ae_of_all _ fun s (hs : 0 < 1 - p s) => sub_pos.2 (hpq1 s (by linarith))) h1
    rw [eq1] at h2
    linarith
  · exact two_point_integral ν hp hq hp01 hq01 hK a b fun s =>
      (two_point_le_bkl (hp01 s).1 (hp01 s).2 (hq01 s).1 (hq01 s).2 (hpq0 s) (hpq1 s) a b).trans
        (h s)

/-- **Joint convexity of the binary divergence, integral form**:
`kl(∫ p dν, ∫ q dν) ≤ ∫ kl(p, q) dν` (the integral/Jensen form of `bkl_convex_comb`), for
`[0,1]`-valued `p`, `q` with `p_s > 0 → q_s > 0`, `p_s < 1 → q_s < 1` and `ν`-integrable
divergence. -/
theorem bkl_integral_convex (ν : Measure Sd) [IsProbabilityMeasure ν] {p q : Sd → ℝ}
    (hp : Measurable p) (hq : Measurable q) (hp01 : ∀ s, 0 ≤ p s ∧ p s ≤ 1)
    (hq01 : ∀ s, 0 ≤ q s ∧ q s ≤ 1) (hpq0 : ∀ s, 0 < p s → 0 < q s)
    (hpq1 : ∀ s, p s < 1 → q s < 1) (hK : Integrable (fun s => bkl (p s) (q s)) ν) :
    bkl (∫ s, p s ∂ν) (∫ s, q s ∂ν) ≤ ∫ s, bkl (p s) (q s) ∂ν :=
  bkl_integral_le_of_le ν hp hq hp01 hq01 hpq0 hpq1 hK fun _ => le_rfl

/-- **Monotone convergence with bounded integrals.**  A nondecreasing sequence of nonnegative
measurable real functions whose integrals are bounded is almost everywhere bounded, its
pointwise supremum is integrable, and the integrals converge to the integral of the
supremum. -/
theorem mono_limit (ν : Measure Sd) [IsFiniteMeasure ν] {f : ℕ → Sd → ℝ}
    (hm : ∀ n, Measurable (f n)) (h0 : ∀ n s, 0 ≤ f n s) (hmono : ∀ s, Monotone fun n => f n s)
    (hint : ∀ n, Integrable (f n) ν) {B : ℝ} (hB : ∀ n, ∫ s, f n s ∂ν ≤ B) :
    (∀ᵐ s ∂ν, BddAbove (Set.range fun n => f n s)) ∧
      Integrable (fun s => ⨆ n, f n s) ν ∧
      Tendsto (fun n => ∫ s, f n s ∂ν) atTop (𝓝 (∫ s, ⨆ n, f n s ∂ν)) := by
  have hlin : ∫⁻ s, ⨆ n, ENNReal.ofReal (f n s) ∂ν ≤ ENNReal.ofReal B := by
    rw [lintegral_iSup (fun n => (hm n).ennreal_ofReal)
      (fun i j hij s => ENNReal.ofReal_le_ofReal (hmono s hij))]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (h0 n))]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hmeasg : Measurable fun s => ⨆ n, ENNReal.ofReal (f n s) :=
    Measurable.iSup fun n => (hm n).ennreal_ofReal
  have hfin : ∀ᵐ s ∂ν, (⨆ n, ENNReal.ofReal (f n s)) < ∞ :=
    ae_lt_top hmeasg (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  have hbdd : ∀ᵐ s ∂ν, BddAbove (Set.range fun n => f n s) := by
    filter_upwards [hfin] with s hs
    refine ⟨(⨆ n, ENNReal.ofReal (f n s)).toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hs.ne).1
      (le_iSup (fun n => ENNReal.ofReal (f n s)) n)
  have hF0 : ∀ᵐ s ∂ν, 0 ≤ ⨆ n, f n s := by
    filter_upwards [hbdd] with s hs
    exact (h0 0 s).trans (le_ciSup hs 0)
  have hFm : Measurable fun s => ⨆ n, f n s := Measurable.iSup hm
  have hFi : Integrable (fun s => ⨆ n, f n s) ν := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hF0]
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
    filter_upwards [hfin, hbdd] with s hs hb
    rw [ENNReal.ofReal_le_iff_le_toReal hs.ne]
    exact ciSup_le fun n => (ENNReal.ofReal_le_iff_le_toReal hs.ne).1
      (le_iSup (fun n => ENNReal.ofReal (f n s)) n)
  refine ⟨hbdd, hFi, ?_⟩
  refine integral_tendsto_of_tendsto_of_monotone hint hFi (ae_of_all _ hmono) ?_
  filter_upwards [hbdd] with s hs
  exact tendsto_atTop_ciSup (hmono s) hs

end Rand

end JointRootCert
