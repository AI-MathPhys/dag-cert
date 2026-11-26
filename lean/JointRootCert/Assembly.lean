/-
Assembly: theorems of the other files restated with hypotheses discharged by results that
are proved elsewhere in the library.

Results covered:

* Theorem `thm:v34-action-local` (Action-local optional evaluation and intersection-union
  root coverage): `action_local_coverage`, with Ville's inequality supplied by `ville_ineq`
  and the supermartingale property by `localWealth_supermartingale`.
* Theorem `thm:puct-noisy-main` (Support-sensitive certification under recursive PUCT):
  `puct_noisy_main_tape`, with simultaneous coverage supplied by `hoeffding_tape_coverage`
  and the radius bound by `puctRadius_le_puctB`.
* Theorem `thm:active-er` (Finite-sample support-sensitive acquisition), exact-regret rule:
  `run_width_le` (width of the running-intersection Hoeffding boxes),
  `active_sample_bound_tape` (sample bound for those boxes), `erStep_width`,
  `tape_coverage`, `active_tape_end_to_end` and `active_er_end_to_end` (coverage,
  correctness and the explicit sample bound in one statement).
* Theorem `thm:active-restart` (Certified restart bound): `restart_reach_step`,
  `restart_covered_episode_within_cap`, `certified_restart_end_to_end`, for independent
  episode σ-algebras; the conditional-failure hypothesis and correctness are derived.
* Theorems `thm:bay-main-dual` and `thm:t4-finite-sample`: `exists_ellipsoid_map`
  identifies `‖Lᵀ g‖` with `√(gᵀ V⁻¹ g)` and `m + L(B₂(β))` with
  `{θ | (θ - m)ᵀ V (θ - m) ≤ β²}`; `confidence_ellipsoid_certificate_iff` and
  `cd_width_of_uncertified` connect the certificate to `cd_width`.

What each theorem still assumes is stated in its doc comment.
-/
import JointRootCert.Coverage
import JointRootCert.RecursivePUCT
import JointRootCert.UnknownVariance
import JointRootCert.Restart

namespace JointRootCert

open Finset MeasureTheory
open scoped ENNReal

/-! ### `thm:v34-action-local` without a Ville hypothesis -/

section ActionLocal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- **Intersection-union root coverage (Theorem `thm:v34-action-local`), with Ville's
inequality proved.**  `F a z i` is the e-factor of the action-component pair `(a, z)` at
batch `i` and the wealth is the action-local product `localWealth`.  For every incorrect
action `a ∈ bad` and its true-null component `zstar a ∈ J a`: the factors are nonnegative
and adapted to the batch filtration `ℱ`, the selection event `{A_{i+1} = a}` is
predictable, and on it the conditional expectation of the next factor is at most one
(`hcond`; under the component null this is `halfCash_integral_le_one`).  Integrability
(`hFint`, `hWint`) is a regularity hypothesis.  Then the probability that at some batch the
selected action is incorrect and passes the minimum-over-components test at level `K / δ`,
`K = |A|`, is at most `δ`.

Compared with `intersection_union_coverage`, the hypothesis `hVille` is gone: it is
obtained from `localWealth_supermartingale` and `ville_ineq`. -/
theorem action_local_coverage (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {A Z : Type*} [Fintype A] [DecidableEq A] (J : A → Finset Z) (F : A → Z → ℕ → Ω → ℝ)
    (sel : ℕ → Ω → A) (bad : Finset A) (zstar : A → Z) (hz : ∀ a ∈ bad, zstar a ∈ J a)
    {δ : ℝ} (hδ : 0 < δ)
    (hF0 : ∀ a ∈ bad, ∀ i ω, 0 ≤ F a (zstar a) i ω)
    (hFad : ∀ a ∈ bad, ∀ i, StronglyMeasurable[ℱ i] (F a (zstar a) i))
    (hsel : ∀ a ∈ bad, ∀ i, MeasurableSet[ℱ i] {ω | sel (i + 1) ω = a})
    (hFint : ∀ a ∈ bad, ∀ i, Integrable (F a (zstar a) i) μ)
    (hWint : ∀ a ∈ bad, ∀ j, Integrable
      (fun ω => localWealth (fun i => F a (zstar a) i ω) (fun i => sel i ω) a j) μ)
    (hcond : ∀ a ∈ bad, ∀ i, ∀ᵐ ω ∂μ, sel (i + 1) ω = a →
      (μ[F a (zstar a) (i + 1)|ℱ i]) ω ≤ 1) :
    μ {ω | ∃ j, sel j ω ∈ bad ∧ ∀ z ∈ J (sel j ω), (Fintype.card A : ℝ) / δ ≤
        localWealth (fun i => F (sel j ω) z i ω) (fun i => sel i ω) (sel j ω) j} ≤
      ENNReal.ofReal δ := by
  refine intersection_union_coverage μ J
    (fun a z j ω => localWealth (fun i => F a z i ω) (fun i => sel i ω) a j) sel bad zstar hz
    hδ.le (fun a ha => ?_)
  have hK : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  have hsm := localWealth_supermartingale μ ℱ (F a (zstar a)) sel a (hF0 a ha) (hFad a ha)
    (hsel a ha) (hFint a ha) (hWint a ha) (hcond a ha)
  have hv := ville_ineq hsm (fun j ω => localWealth_nonneg (fun i => hF0 a ha i ω) j)
    (c := (Fintype.card A : ℝ) / δ) (by positivity)
  refine hv.trans (le_of_eq ?_)
  congr 1
  simp only [localWealth_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [one_div_div]

end ActionLocal

/-! ### `thm:puct-noisy-main` from the reward-tape model -/

section PUCTTape

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {V E : Type*} [Fintype E]
  {Ω : Type*} [MeasurableSpace Ω] {A : Type*}

/-- **Support-sensitive certification under recursive PUCT (Theorem `thm:puct-noisy-main`),
with coverage proved.**  As `puct_noisy_main`, for the reward-tape model: terminal `z` is
sampled by reading its tape `X z` in order, the tape elements being `[0,1]`-valued with
mean `μ z` and independent within a tape (no independence across tapes is needed).  The
monitor's box is the running intersection of the intervals with radius `β_M(n, δ)`
(`puctRadius`), `M = |Z|`, at the terminal visit counts.  If `ε ≥ 0`, `ε + Γ > 0`,
`t ≥ t_*` and `c_* t ^ (2 ^ (-H)) ≥ 8 / (ε + Γ)² · log (4 M (t+1)² / δ)`, the event
`{τ ≤ t and Reg ≤ ε}` fails with probability at most `δ / 2`.

The only probabilistic input is the tape model (`hmeas`, `hbdd`, `hmean`, `hindep`).  The
remaining hypotheses are the search contract `PUCTRun` on every sample path, the paths to
the terminals, the definition of `Γ`, and the specification `hmon` of the stopping monitor
(it stops at the first exact `ε`-certificate and returns a certified action). -/
theorem puct_noisy_main_tape {src tgt : E → V} {root : V} {lam : E → ℝ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    (vis : Ω → ℕ → V → Prop) (ch : Ω → ℕ → V → E) (Q : Ω → E → ℕ → ℝ)
    (hrun : ∀ ω, PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω))
    (term : Z → V) (path : Z → List E) (hpath : ∀ z, IsPath src tgt (path z) root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, rectCert (supp a) (hne a) (hpr a)
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s)) ≤ ε) →
        τ ω ≤ s ∧ rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω)))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω))) ≤ ε)
    (Γ : ℝ) (hΓ : IsGreatest ((fun a => outsideMargin (supp a) (hpr a) μ) ''
      {a | val (supp a) (hne a) μ = gmax μ}) Γ)
    (hε : 0 ≤ ε) (hpos : 0 < ε + Γ) (t : ℕ) (ht : puctTstar src lam path ≤ t)
    (hcond : 8 / (ε + Γ) ^ 2 *
        Real.log (4 * (Fintype.card Z : ℝ) * ((t : ℝ) + 1) ^ 2 / δ) ≤
      puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ)) :
    P {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤
      ENNReal.ofReal (δ / 2) := by
  obtain ⟨ω0⟩ : Nonempty Ω := by
    by_contra hΩ
    rw [not_nonempty_iff] at hΩ
    have h1 : P Set.univ = 1 := measure_univ
    rw [Set.eq_empty_of_isEmpty (Set.univ : Set Ω), measure_empty] at h1
    exact zero_ne_one h1
  have ht1 : (1 : ℝ) ≤ t := by
    have h1 : (1 : ℝ) ≤ (puctTstar src lam path : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
    exact h1.trans (by exact_mod_cast ht)
  have hm : 0 < puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ) :=
    mul_pos (puctCstar_pos (hrun ω0).lam_pos path) (Real.rpow_pos_of_pos (by linarith) _)
  have hM : (1 : ℝ) ≤ (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  exact puct_noisy_main P vis ch Q hrun term path hpath H hH supp hne hpr μ hμ
    (fun ω z k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω) (puctRadius (Fintype.card Z) δ) _
    (hoeffding_tape_coverage P X μ hmeas hbdd hmean hindep hδ0 hδ1) ε τ rec hmon Γ hΓ hε hpos
    t ht (fun k hmk hkt => puctRadius_le_puctB hM hδ0 hδ1 hm hmk hkt) hcond

end PUCTTape

/-! ### `thm:active-er`: running-intersection Hoeffding boxes and the end-to-end statement -/

section ActiveTape

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- Number of queries of terminal `z` among the first `t` steps of the run `sel`
(the intrinsic count `N_t(z)`). -/
def queryCount (sel : ℕ → Z) (t : ℕ) (z : Z) : ℕ := ((range t).filter (fun s => sel s = z)).card

omit [Fintype Z] in
lemma queryCount_self (sel : ℕ → Z) (t : ℕ) : queryCount sel t (sel t) = priorCount sel t := rfl

omit [Fintype Z] in
lemma queryCount_le_succ (sel : ℕ → Z) (t : ℕ) (z : Z) :
    queryCount sel t z ≤ queryCount sel (t + 1) z :=
  card_le_card (filter_subset_filter _ (range_mono (Nat.le_succ t)))

/-- Lower endpoint `l_t(z)` of the terminal box after `t` queries: the running intersection
of `I_{z,0} = [0,1]` and the Hoeffding intervals `I_{z,k}`, `1 ≤ k ≤ N_t(z)`, built from the
tape `x z` of terminal `z`. -/
noncomputable def tapeLo (M δ : ℝ) (x : Z → ℕ → ℝ) (sel : ℕ → Z) (t : ℕ) (z : Z) : ℝ :=
  runLo (hoeffLo M δ (x z)) (queryCount sel t z)

/-- Upper endpoint `u_t(z)` of the same box. -/
noncomputable def tapeHi (M δ : ℝ) (x : Z → ℕ → ℝ) (sel : ℕ → Z) (t : ℕ) (z : Z) : ℝ :=
  runHi (hoeffHi M δ (x z)) (queryCount sel t z)

omit [Fintype Z] in
/-- The coverage event `𝓔` of a run: the means `m` lie in the box at every time. -/
def tapeCovered (M δ : ℝ) (x : Z → ℕ → ℝ) (sel : ℕ → Z) (m : Z → ℝ) : Prop :=
  ∀ t, m ∈ Set.Icc (tapeLo M δ x sel t) (tapeHi M δ x sel t)

omit [Fintype Z] in
/-- The boxes of a run are nested (instance of `box_nested`). -/
theorem tape_box_nested (M δ : ℝ) (x : Z → ℕ → ℝ) (sel : ℕ → Z) (t : ℕ) (z : Z) :
    tapeLo M δ x sel t z ≤ tapeLo M δ x sel (t + 1) z ∧
      tapeHi M δ x sel (t + 1) z ≤ tapeHi M δ x sel t z :=
  box_nested (fun z => hoeffLo M δ (x z)) (fun z => hoeffHi M δ (x z))
    (fun t z => queryCount sel t z) (fun t z => queryCount_le_succ sel t z) t z

/-- Width bound of a running-intersection Hoeffding interval after `n` observations:
`1` before any observation, `2 β(n)` afterwards. -/
noncomputable def nestedWidth (M δ : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else hoeffdingWidth M δ n

/-- **Width of the nested Hoeffding interval.**  The running intersection of `[0,1]` and
the Hoeffding intervals at counts `1, …, n` has width at most `2 β(n)` (and exactly `1` at
`n = 0`).  This is the fact "a nested Hoeffding interval based on `n` observations has
width at most `2 β(n)`" used in the proof of Theorem `thm:active-er`. -/
theorem run_width_le (M δ : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    runHi (hoeffHi M δ x) n - runLo (hoeffLo M δ x) n ≤ nestedWidth M δ n := by
  cases n with
  | zero => simp [runHi, runLo, hoeffHi, hoeffLo, nestedWidth]
  | succ k =>
    have h1 : runHi (hoeffHi M δ x) (k + 1) ≤ hoeffHi M δ x (k + 1) := min_le_right _ _
    have h2 : hoeffLo M δ x (k + 1) ≤ runLo (hoeffLo M δ x) (k + 1) := le_max_right _ _
    have hne : k + 1 ≠ 0 := Nat.succ_ne_zero k
    simp only [hoeffLo, hoeffHi, hne, ↓reduceIte] at h1 h2
    simp only [nestedWidth, hne, ↓reduceIte]
    linarith

/-- With at least `⌈(32 / r²) log (32 M / (δ r²))⌉` observations the nested width is below
`r` (`width_inversion_nat`; the count is positive, so the `n = 0` branch does not occur). -/
lemma nestedWidth_lt {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r ≤ 1) {n : ℕ} (hn : ⌈32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2))⌉₊ ≤ n) :
    nestedWidth M δ n < r := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2le : r ^ 2 ≤ 1 := by nlinarith
  have harg : 1 < 32 * M / (δ * r ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hδ1.le hr2le hr2.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hpos : 0 < 32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2)) :=
    mul_pos (by positivity) (Real.log_pos harg)
  have hn0 : n ≠ 0 := by
    have := Nat.ceil_pos.mpr hpos
    omega
  simp only [nestedWidth, hn0, ↓reduceIte]
  exact width_inversion_nat hM hδ0 hδ1 hr0 hr1 hn

/-- **Explicit sample bound for running-intersection Hoeffding boxes.**  The statement of
`active_sample_bound` with the box built from the tapes `x` along the run `sel`: if every
queried terminal is at least as wide as its threshold `ρ z ∈ (0, 1]`, the number of queries
is at most `∑_z ⌈(32 / ρ_z²) log (32 M / (δ ρ_z²))⌉`.  The hypothesis `hnest` of
`active_sample_bound` is replaced by `run_width_le`. -/
theorem active_sample_bound_tape {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (τ : ℕ) (sel : ℕ → Z) (x : Z → ℕ → ℝ) (ρ : Z → ℝ) (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ 1)
    (hcharged : ∀ t < τ, ρ (sel t) ≤
      tapeHi M δ x sel t (sel t) - tapeLo M δ x sel t (sel t)) :
    τ ≤ ∑ z, ⌈32 / ρ z ^ 2 * Real.log (32 * M / (δ * ρ z ^ 2))⌉₊ :=
  stopping_time_le_sum_budget τ sel
    (fun t => tapeHi M δ x sel t (sel t) - tapeLo M δ x sel t (sel t)) (nestedWidth M δ) ρ _
    (fun t _ => run_width_le M δ (x (sel t)) (priorCount sel t)) hcharged
    (fun z _ hn => nestedWidth_lt hM hδ0 hδ1 (hρ z).1 (hρ z).2 hn)

variable [Nonempty Z] {A : Type*}

/-- **One continuing step of Exact-Regret-DAG-LUCB** (Algorithm `alg:certify`, ER rule) on
the box `[l, u]`: some action `a` minimises the exact certificate, the certificate exceeds
`ε` (the procedure continues), `p` and `q` are optimistic inside and outside witnesses of
`a`, and the queried terminal `z` is the wider of the two.  Ties are unconstrained. -/
def ERStep (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (l u : Z → ℝ) (ε : ℝ) (z : Z) : Prop :=
  ∃ (a : A) (p q : Z),
    (∀ c, rectCert (supp a) (hne a) (hpr a) l u ≤ rectCert (supp c) (hne c) (hpr c) l u) ∧
    ε < rectCert (supp a) (hne a) (hpr a) l u ∧
    p ∈ supp a ∧ (∀ y ∈ supp a, u y ≤ u p) ∧
    q ∉ supp a ∧ (∀ y, y ∉ supp a → u y ≤ u q) ∧
    ((z = p ∧ u q - l q ≤ u p - l p) ∨ (z = q ∧ u p - l p ≤ u q - l q))

/-- The terminal queried by a continuing ER step on a box containing the true means has
width at least `max {ε, Δ_z / 2}` (`active_width`, i.e. Lemma `lem:active-width`). -/
theorem erStep_width (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) {l u μ : Z → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hμ : μ ∈ Set.Icc l u) {z : Z} (h : ERStep supp hne hpr l u ε z) :
    max ε ((gmax μ - μ z) / 2) ≤ u z - l z := by
  obtain ⟨a, p, q, hmin, hcont, hp, hpmax, hq, hqmax, hsel⟩ := h
  have hlu : l ≤ u := fun y => (hμ.1 y).trans (hμ.2 y)
  obtain ⟨h1, h2⟩ := active_width supp hne hpr hcov hlu hε a hmin hcont hp hpmax hq hqmax
  obtain ⟨h3, h4⟩ := h2 μ hμ
  rcases hsel with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · rw [max_eq_left hw] at h1
    exact max_le h1.le (h3 hw)
  · rw [max_eq_right hw] at h1
    exact max_le h1.le (h4 hw)

variable {Ω : Type*} [MeasurableSpace Ω]

omit [Nonempty Z] in
/-- **Coverage of the boxes of an adaptive run** (`hoeffding_box_coverage` for the boxes
`[tapeLo, tapeHi]`).  Whatever the run `sel`, the coverage event fails with probability at
most `δ`. -/
theorem tape_coverage (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 1 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (sel : Ω → ℕ → Z) :
    P {ω | ¬ tapeCovered M δ (fun z i => X z i ω) (sel ω) m} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (hoeffding_box_coverage hindep hmeas hbdd hmean hM hcard
    hδ0 hδ1 (fun t ω z => queryCount (sel ω) t z))
  intro ω hω
  by_contra hgood
  apply hω
  intro t
  have hz : ∀ z, m z ∈ Set.Icc (tapeLo M δ (fun z i => X z i ω) (sel ω) t z)
      (tapeHi M δ (fun z i => X z i ω) (sel ω) t z) := by
    intro z
    by_contra h
    exact hgood ⟨t, z, h⟩
  exact ⟨fun z => (hz z).1, fun z => (hz z).2⟩

/-- **Coverage, correctness and sample bound for an active sampler on Hoeffding boxes.**

Reward-tape model: `X z i` is the `i`-th observation of terminal `z`; the observations of
one terminal are independent, `[0,1]`-valued, with mean `m z`.  On the sample path `ω` the
sampler queries `sel ω t` at step `t`, makes `τ ω` queries and returns `rec ω`; its box at
time `t` is `[tapeLo, tapeHi]`, the running intersection of the Hoeffding intervals at the
current counts.  The sampler is constrained only on sample paths on which the true means
stay in every box (so the confidence-failure halt of Algorithm `alg:certify` is left
free): there, each queried terminal is at least as wide as its threshold `ρ z ∈ (0, 1]`
(`hcharged`, supplied by the width lemma of the rule in use) and the returned action has
exact certificate at most `ε` at the stopping time (`hstop`).

Conclusion: outside an event of probability at most `δ`, the returned action is
`ε`-optimal and `τ ≤ ∑_z ⌈(32 / ρ_z²) log (32 M / (δ ρ_z²))⌉`.  Coverage is not assumed:
it is `hoeffding_box_coverage`. -/
theorem active_tape_end_to_end (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (ρ : Z → ℝ) (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ 1) (ε : ℝ)
    (sel : Ω → ℕ → Z) (τ : Ω → ℕ) (rec : Ω → A)
    (hcharged : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        ∀ t < τ ω, ρ (sel ω t) ≤
          tapeHi M δ (fun z i => X z i ω) (sel ω) t (sel ω t) -
            tapeLo M δ (fun z i => X z i ω) (sel ω) t (sel ω t))
    (hstop : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (tapeLo M δ (fun z i => X z i ω) (sel ω) (τ ω))
          (tapeHi M δ (fun z i => X z i ω) (sel ω) (τ ω)) ≤ ε) :
    P {ω | ¬ (regret (supp (rec ω)) (hne (rec ω)) m ≤ ε ∧
        τ ω ≤ ∑ z, ⌈32 / ρ z ^ 2 * Real.log (32 * M / (δ * ρ z ^ 2))⌉₊)} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (tape_coverage P hindep hmeas hbdd hmean (by linarith) hcard
    hδ0 hδ1.le sel)
  intro ω hω hcovd
  exact hω ⟨regret_le_of_cert (hpr (rec ω)) (hcovd (τ ω)) (hstop ω hcovd),
    active_sample_bound_tape hM hδ0 hδ1 (τ ω) (sel ω) (fun z i => X z i ω) ρ hρ
      (hcharged ω hcovd)⟩

/-- **Exact-regret sampling, end to end (Theorem `thm:active-er`, ER bound).**

Reward-tape model as in `active_tape_end_to_end`, with `M ≥ max {2, |Z|}`, `0 < δ < 1`,
`0 < ε ≤ 1`, proper supports that cover `Z`.  The sampler is a run that, on every sample
path on which the true means stay in every box, performs a continuing ER step (`ERStep`)
on the current Hoeffding box at each of its `τ` queries and returns an action whose exact
certificate at the stopping time is at most `ε`.  Then with probability at least `1 - δ`
(failure probability at most `δ`) the returned action is `ε`-optimal and

`τ ≤ ∑_z ⌈(32 / ρ_z²) log (32 M / (δ ρ_z²))⌉`, `ρ_z = max {ε, Δ_z / 2}`, `Δ_z = μ_* - μ_z`.

No coverage, width or nesting hypothesis remains: these are `hoeffding_box_coverage`,
`active_width`, `run_width_le` and `width_inversion`. -/
theorem active_er_end_to_end (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (sel : Ω → ℕ → Z) (τ : Ω → ℕ) (rec : Ω → A)
    (hrule : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        ∀ t < τ ω, ERStep supp hne hpr (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε (sel ω t))
    (hstop : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (tapeLo M δ (fun z i => X z i ω) (sel ω) (τ ω))
          (tapeHi M δ (fun z i => X z i ω) (sel ω) (τ ω)) ≤ ε) :
    P {ω | ¬ (regret (supp (rec ω)) (hne (rec ω)) m ≤ ε ∧
        τ ω ≤ ∑ z, ⌈32 / (max ε ((gmax m - m z) / 2)) ^ 2 *
          Real.log (32 * M / (δ * (max ε ((gmax m - m z) / 2)) ^ 2))⌉₊)} ≤
      ENNReal.ofReal δ := by
  have hm01 : ∀ z, m z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    have hint : Integrable (X z 0) P := Integrable.of_mem_Icc 0 1 (hmeas z 0) (hbdd z 0)
    rw [← hmean z 0]
    constructor
    · exact integral_nonneg_of_ae ((hbdd z 0).mono fun ω h => h.1)
    · have := integral_mono_ae hint (integrable_const (1 : ℝ))
        ((hbdd z 0).mono fun ω h => h.2)
      simpa using this
  have hg1 : gmax m ≤ 1 := sup'_le _ _ (fun z _ => (hm01 z).2)
  refine active_tape_end_to_end P hindep hmeas hbdd hmean hM hcard hδ0 hδ1 supp hne hpr
    (fun z => max ε ((gmax m - m z) / 2))
    (fun z => ⟨lt_max_of_lt_left hε0, max_le hε1 (by linarith [(hm01 z).1])⟩) ε sel τ rec
    (fun ω hc t ht => erStep_width supp hne hpr hcov hε0.le (hc t) (hrule ω hc t ht)) hstop

end ActiveTape

/-! ### `thm:active-restart`: independent fresh episodes -/

section RestartModel

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}
  {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- **A covered episode `j ≥ j_*` stops within its cap `2^j`**, for the
running-intersection Hoeffding boxes at confidence `δ_j = δ / (j (j + 1))`.  This is
`restart_good_episode_within_cap` with its width hypothesis `hnest` replaced by
`run_width_le`. -/
theorem restart_covered_episode_within_cap {M δ ρmin : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) (ρ : Z → ℝ)
    (hρmin : 0 < ρmin) (hρ : ∀ z, ρmin ≤ ρ z ∧ ρ z ≤ 1) {j : ℕ} (hj : 1 ≤ j)
    (hjs : restartEpisode (∑ z, 1 / ρ z ^ 2) (Real.log (128 * M / (δ * ρmin ^ 2))) ≤ j)
    (τ : ℕ) (sel : ℕ → Z) (x : Z → ℕ → ℝ)
    (hcharged : ∀ t < τ, ρ (sel t) ≤
      tapeHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x sel t (sel t) -
        tapeLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x sel t (sel t)) :
    τ ≤ 2 ^ j := by
  obtain ⟨h1, h2, h3, h4⟩ := restart_constants hM hcard hδ0 hδ ρ hρmin hρ
  have hnum := (restart_numeric h1 h2 h3).2.2.2.2.2 j hjs
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hc0 : 0 < δ / ((j : ℝ) * ((j : ℝ) + 1)) := by positivity
  have hc1 : δ / ((j : ℝ) * ((j : ℝ) + 1)) < 1 := by
    have : δ / ((j : ℝ) * ((j : ℝ) + 1)) ≤ δ := by
      apply div_le_self hδ0.le
      nlinarith
    linarith
  have h := active_sample_bound_tape hM hc0 hc1 τ sel x ρ
    (fun z => ⟨lt_of_lt_of_le hρmin (hρ z).1, (hρ z).2⟩) hcharged
  have h' : (τ : ℝ) ≤ ∑ z, (⌈32 / ρ z ^ 2 *
      Real.log (32 * M / (δ / ((j : ℝ) * ((j : ℝ) + 1)) * ρ z ^ 2))⌉₊ : ℝ) := by
    exact_mod_cast h
  have hs := h'.trans (restart_episode_budget hM hδ0 (by linarith) ρ hρmin hρ hj)
  rw [h4] at hs
  have : (τ : ℝ) ≤ 2 ^ j := hs.trans hnum
  exact_mod_cast this

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
/-- **Reaching the next episode.**  `F i` is the event that episode `i` ends without an
output, measurable with respect to the σ-algebra `𝒢 i` of episode `i`, and the episode
σ-algebras are independent.  Episode `j + 1` is reached when episodes `1, …, j` all fail, so
`P(reach j + 1) = P(reach j) · P(F j)`. -/
theorem restart_reach_step (P : Measure Ω) (𝒢 : ℕ → MeasurableSpace Ω)
    (hind : ProbabilityTheory.iIndep 𝒢 P) (F : ℕ → Set Ω)
    (hFm : ∀ j, MeasurableSet[𝒢 j] (F j)) {q : ℝ≥0∞} {j : ℕ} (hj : 1 ≤ j)
    (hq : P (F j) ≤ q) :
    P (⋂ i ∈ Finset.Ico 1 (j + 1), F i) ≤ q * P (⋂ i ∈ Finset.Ico 1 j, F i) := by
  have e1 := hind.meas_biInter (S := Finset.Ico 1 (j + 1)) (s := F) (fun i _ => hFm i)
  have e2 := hind.meas_biInter (S := Finset.Ico 1 j) (s := F) (fun i _ => hFm i)
  rw [e1, e2, Finset.prod_Ico_succ_top hj, mul_comm]
  gcongr

/-- **Certified restart bound (Theorem `thm:active-restart`) from independent fresh
episodes.**

Model.  Episode `j ≥ 1` has its own reward tapes `X j z` (within a tape: independent,
`[0,1]`-valued, mean `m z`), its own run `sel j ω` with stopping time `σ j ω` (the number of
queries the uncapped rule makes), and boxes `[tapeLo, tapeHi]` at confidence
`δ_j = δ / (j (j + 1))`.  `𝒢 j` is the σ-algebra of episode `j`; the episodes are
independent (`hind`).  `F j` is the event that episode `j` ends without an output (timeout
at the cap `2^j` or confidence failure); it depends only on episode `j` (`hFm`).  Episode
`j` is reached on `⋂_{1 ≤ i < j} F i`.

Hypotheses on the procedure, required only on the coverage event of the episode:
* `hcharged`: every queried terminal is at least as wide as its threshold `ρ z` (the
  conclusion of `active_os_width` for `ρ_z = max {Γ + ε, Δ_z} / 2`);
* `hret`: if the rule stops within the cap, the episode returns (`ω ∉ F j`);
and on every sample path:
* `hτ`: the number of observations is at most the sum of the caps of the reached episodes;
* `hout`: when the wrapper terminates, its output `rec ω` is the action certified by the
  box of the returning episode `out ω` at that episode's stopping time.

Conclusions: `E τ < 1600 H_ρ L`; `τ < ∞` almost surely; the event that every episode is
reached is null; and the output fails to be `ε`-optimal with probability at most `δ`.

Compared with `certified_restart_bound`, the hypothesis `hfail` is derived (independence,
`tape_coverage` per episode, and `restart_covered_episode_within_cap`), and correctness is
derived from per-episode coverage (`restart_correct`).  What is still assumed about
probability is the independence of the episode σ-algebras and the measurability of each
failure event with respect to its own episode; a product-measure construction realising
this is not given. -/
theorem certified_restart_end_to_end (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Z → ℕ → Ω → ℝ}
    (hindep : ∀ j z, ProbabilityTheory.iIndepFun (X j z) P)
    (hmeas : ∀ j z i, AEMeasurable (X j z i) P)
    (hbdd : ∀ j z i, ∀ᵐ ω ∂P, X j z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ j z i, ∫ ω, X j z i ω ∂P = m z)
    (𝒢 : ℕ → MeasurableSpace Ω) (hle : ∀ j, 𝒢 j ≤ m0) (hind : ProbabilityTheory.iIndep 𝒢 P)
    {M δ ρmin : ℝ} (hM : 2 ≤ M) (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (ρ : Z → ℝ) (hρmin : 0 < ρmin) (hρ : ∀ z, ρmin ≤ ρ z ∧ ρ z ≤ 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (ε : ℝ) (sel : ℕ → Ω → ℕ → Z) (σ : ℕ → Ω → ℕ) (F : ℕ → Set Ω)
    (hFm : ∀ j, MeasurableSet[𝒢 j] (F j))
    (hcharged : ∀ j : ℕ, 1 ≤ j → ∀ ω,
      tapeCovered M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => X j z i ω) (sel j ω) m →
      ∀ t < σ j ω, ρ (sel j ω t) ≤
        tapeHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => X j z i ω) (sel j ω) t
            (sel j ω t) -
          tapeLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => X j z i ω) (sel j ω) t
            (sel j ω t))
    (hret : ∀ j : ℕ, 1 ≤ j → ∀ ω,
      tapeCovered M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => X j z i ω) (sel j ω) m →
      σ j ω ≤ 2 ^ j → ω ∉ F j)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤
      ∑' j : ℕ, (⋂ i ∈ Finset.Ico 1 j, F i).indicator (fun _ => (2 : ℝ≥0∞) ^ j) ω)
    (out : Ω → ℕ) (rec : Ω → A)
    (hout : ∀ ω, ω ∉ ⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j, F i →
      1 ≤ out ω ∧ rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
        (tapeLo M (δ / ((out ω : ℝ) * ((out ω : ℝ) + 1))) (fun z i => X (out ω) z i ω)
          (sel (out ω) ω) (σ (out ω) ω))
        (tapeHi M (δ / ((out ω : ℝ) * ((out ω : ℝ) + 1))) (fun z i => X (out ω) z i ω)
          (sel (out ω) ω) (σ (out ω) ω)) ≤ ε) :
    ∫⁻ ω, τ ω ∂P <
        ENNReal.ofReal (1600 * (∑ z, 1 / ρ z ^ 2) * Real.log (128 * M / (δ * ρmin ^ 2))) ∧
      (∀ᵐ ω ∂P, τ ω < ∞) ∧
      P (⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j, F i) = 0 ∧
      P {ω | ε < regret (supp (rec ω)) (hne (rec ω)) m} ≤ ENNReal.ofReal δ := by
  have hRm : ∀ j : ℕ, MeasurableSet (⋂ i ∈ Finset.Ico 1 j, F i) := fun j =>
    Finset.measurableSet_biInter _ (fun i _ => hle i _ (hFm i))
  obtain ⟨h1, h2, h3, -⟩ := restart_constants hM hcard hδ0 hδ ρ hρmin hρ
  have hnum := (restart_numeric h1 h2 h3).1
  have hjs1 : 1 ≤ restartEpisode (∑ z, 1 / ρ z ^ 2) (Real.log (128 * M / (δ * ρmin ^ 2))) := by
    by_contra h0
    have h00 : restartEpisode (∑ z, 1 / ρ z ^ 2) (Real.log (128 * M / (δ * ρmin ^ 2))) = 0 := by
      omega
    rw [h00, pow_zero] at hnum
    have hL1 : 1 < Real.log (128 * M / (δ * ρmin ^ 2)) := by
      refine lt_of_lt_of_le ?_ h2
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    have hHL : 1 ≤ (∑ z, 1 / ρ z ^ 2) * Real.log (128 * M / (δ * ρmin ^ 2)) := by nlinarith
    linarith
  have hconf : ∀ j : ℕ, 1 ≤ j → 0 < δ / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      δ / ((j : ℝ) * ((j : ℝ) + 1)) ≤ δ / 2 := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    refine ⟨by positivity, ?_⟩
    exact div_le_div_of_nonneg_left hδ0.le (by norm_num) (by nlinarith)
  have hmiss : ∀ j : ℕ, 1 ≤ j →
      P {ω | ¬ tapeCovered M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => X j z i ω)
        (sel j ω) m} ≤ ENNReal.ofReal (δ / ((j : ℝ) * ((j : ℝ) + 1))) := fun j hj =>
    tape_coverage P (hindep j) (hmeas j) (hbdd j) (hmean j) (by linarith) hcard (hconf j hj).1
      (by linarith [(hconf j hj).2]) (sel j)
  have hFj : ∀ j, restartEpisode (∑ z, 1 / ρ z ^ 2) (Real.log (128 * M / (δ * ρmin ^ 2))) ≤ j →
      P (F j) ≤ ENNReal.ofReal (δ / 2) := by
    intro j hj
    have hj1 : 1 ≤ j := hjs1.trans hj
    refine (measure_mono ?_).trans
      ((hmiss j hj1).trans (ENNReal.ofReal_le_ofReal (hconf j hj1).2))
    intro ω hω hc
    exact hret j hj1 ω hc (restart_covered_episode_within_cap hM hcard hδ0 hδ ρ hρmin hρ hj1 hj
      (σ j ω) (sel j ω) _ (hcharged j hj1 ω hc)) hω
  obtain ⟨hint, hzero, hfin⟩ := certified_restart_bound hM hcard hδ0 hδ ρ hρmin hρ P
    (fun j => ⋂ i ∈ Finset.Ico 1 j, F i) hRm τ hτ
    (fun j hj => restart_reach_step P 𝒢 hind F hFm (hjs1.trans hj) (hFj j hj))
  refine ⟨hint, hfin, hzero, ?_⟩
  have hsub : {ω | ε < regret (supp (rec ω)) (hne (rec ω)) m} ⊆
      (⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j, F i) ∪
        ⋃ i : ℕ, {ω | ¬ tapeCovered M (δ / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1)))
          (fun z k => X (i + 1) z k ω) (sel (i + 1) ω) m} := by
    intro ω hω
    by_cases hin : ω ∈ ⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j, F i
    · exact Or.inl hin
    · right
      obtain ⟨ho1, hcert⟩ := hout ω hin
      obtain ⟨i, hi⟩ : ∃ i, out ω = i + 1 := ⟨out ω - 1, by omega⟩
      rw [hi] at hcert
      refine Set.mem_iUnion.mpr ⟨i, fun hc => ?_⟩
      have := regret_le_of_cert (hpr (rec ω)) (hc (σ (i + 1) ω)) hcert
      exact absurd this (not_le.mpr hω)
  calc P {ω | ε < regret (supp (rec ω)) (hne (rec ω)) m}
      ≤ P ((⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j, F i) ∪
        ⋃ i : ℕ, {ω | ¬ tapeCovered M (δ / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1)))
          (fun z k => X (i + 1) z k ω) (sel (i + 1) ω) m}) := measure_mono hsub
    _ ≤ P (⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j, F i) +
        P (⋃ i : ℕ, {ω | ¬ tapeCovered M (δ / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1)))
          (fun z k => X (i + 1) z k ω) (sel (i + 1) ω) m}) := measure_union_le _ _
    _ = P (⋃ i : ℕ, {ω | ¬ tapeCovered M (δ / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1)))
          (fun z k => X (i + 1) z k ω) (sel (i + 1) ω) m}) := by rw [hzero, zero_add]
    _ ≤ ENNReal.ofReal δ := by
        refine restart_correct P hδ0.le _ _ subset_rfl (fun i => ?_)
        refine (hmiss (i + 1) (by omega)).trans (le_of_eq ?_)
        congr 1
        push_cast
        ring

end RestartModel

/-! ### `thm:t4-finite-sample` and `thm:bay-main-dual`: the two forms of the contrast norm -/

section Identification

open Matrix WithLp
open scoped MatrixOrder RealInnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A coercive symmetric matrix factors as `V = Cᵀ C` with `C` invertible. -/
lemma Coercive.exists_factor {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam)
    (hlam : 0 < lam) : ∃ C : Matrix n n ℝ, V = Cᵀ * C ∧ IsUnit C.det := by
  have hpsd : V.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
    · show Vᴴ = V
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, hV.symm]
    · rw [star_trivial]
      exact (mul_nonneg hlam.le (dotProduct_self_nonneg' x)).trans (hV.coer x)
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
  have hC' : V = Cᵀ * C := by
    rw [hC, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨C, hC', ?_⟩
  have hdet := hV.isUnit_det hlam
  rw [hC', Matrix.det_mul, Matrix.det_transpose] at hdet
  exact isUnit_of_mul_isUnit_left hdet

omit [DecidableEq n] in
lemma euclidean_norm_sq_eq_dotProduct (x : EuclideanSpace ℝ n) : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- **Identification of the two presentations of the contrast norm.**  For a symmetric
coercive design matrix `V` (`lam > 0`) there is a linear map `L` on Euclidean space such
that

* `‖Lᵀ g‖ = √(gᵀ V⁻¹ g)` for every `g` (the norm of `Ellipsoid.lean` equals the one of
  `CDJoint.lean`), and
* for every centre `m` and radius `β ≥ 0`, the set `m + L(B₂(β))` of `Ellipsoid.lean` is the
  confidence ellipsoid `{θ | (θ - m)ᵀ V (θ - m) ≤ β²}`.

`L` is `C⁻¹` for a factorisation `V = Cᵀ C`. -/
theorem exists_ellipsoid_map {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam)
    (hlam : 0 < lam) :
    ∃ L : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n,
      (∀ g : EuclideanSpace ℝ n, ‖LinearMap.adjoint L g‖ = Real.sqrt (qinv V g.ofLp)) ∧
      ∀ (m : EuclideanSpace ℝ n) (β : ℝ), 0 ≤ β →
        ellipsoid m L β = {θ | (θ - m).ofLp ⬝ᵥ V *ᵥ (θ - m).ofLp ≤ β ^ 2} := by
  obtain ⟨C, hVC, hCdet⟩ := hV.exists_factor hlam
  have hCB : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  have hBC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hCdet
  have hquad : ∀ u : n → ℝ, u ⬝ᵥ V *ᵥ u = (C *ᵥ u) ⬝ᵥ (C *ᵥ u) := by
    intro u
    rw [hVC, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hVinv : V⁻¹ = C⁻¹ * (C⁻¹)ᵀ := by
    rw [hVC, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  have hqinv : ∀ g : n → ℝ, qinv V g = ((C⁻¹)ᵀ *ᵥ g) ⬝ᵥ ((C⁻¹)ᵀ *ᵥ g) := by
    intro g
    rw [qinv, hVinv, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  refine ⟨Matrix.toEuclideanLin C⁻¹, fun g => ?_, fun m β hβ => ?_⟩
  · rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial, hqinv]
    have e : ((C⁻¹)ᵀ *ᵥ g.ofLp) ⬝ᵥ ((C⁻¹)ᵀ *ᵥ g.ofLp) =
        ‖Matrix.toEuclideanLin (C⁻¹)ᵀ g‖ ^ 2 :=
      (euclidean_norm_sq_eq_dotProduct (Matrix.toEuclideanLin (C⁻¹)ᵀ g)).symm
    rw [e, Real.sqrt_sq (norm_nonneg _)]
  · ext θ
    simp only [ellipsoid, Set.mem_image, Metric.mem_closedBall, dist_zero_right,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hsub : (m + Matrix.toEuclideanLin C⁻¹ u - m).ofLp = C⁻¹ *ᵥ u.ofLp := by
        rw [add_sub_cancel_left]
        rfl
      rw [hsub, hquad, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec,
        ← euclidean_norm_sq_eq_dotProduct]
      exact pow_le_pow_left₀ (norm_nonneg _) hu 2
    · intro hθ
      refine ⟨toLp 2 (C *ᵥ (θ - m).ofLp), ?_, ?_⟩
      · have h1 : ‖toLp 2 (C *ᵥ (θ - m).ofLp)‖ ^ 2 ≤ β ^ 2 := by
          rw [euclidean_norm_sq_eq_dotProduct, ← hquad]
          exact hθ
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) hβ two_ne_zero).mp h1
      · have h2 : Matrix.toEuclideanLin C⁻¹ (toLp 2 (C *ᵥ (θ - m).ofLp)) = θ - m := by
          rw [Matrix.toLpLin_apply]
          simp only [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
        rw [h2, add_sub_cancel]

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **Exact joint ellipsoidal certificate for the confidence ellipsoid of a design matrix
(Theorem `thm:bay-main-dual` in the notation of Theorem `thm:t4-finite-sample`).**  For a
symmetric coercive `V`, a commitment with support `S` is `ε`-acceptable for every parameter
in `{θ | (θ - m)ᵀ V (θ - m) ≤ β²}` iff `ε ≥ 0` and every excluded challenger `z` admits an
inside mixture `p` with `⟨g_{z,p}, m⟩ + β √(g_{z,p}ᵀ V⁻¹ g_{z,p}) ≤ ε`.  This is
`ellipsoid_certificate_iff` transported along `exists_ellipsoid_map`; the objective is the
one appearing in `cd_width`. -/
theorem confidence_ellipsoid_certificate_iff {V : Matrix n n ℝ} {lam : ℝ}
    (hV : Coercive V lam) (hlam : 0 < lam) {S : Finset Z} (hS : S.Nonempty) {β ε : ℝ}
    (hβ : 0 ≤ β) (φ : Z → EuclideanSpace ℝ n) (m : EuclideanSpace ℝ n) :
    (∀ θ : EuclideanSpace ℝ n, (θ - m).ofLp ⬝ᵥ V *ᵥ (θ - m).ofLp ≤ β ^ 2 →
        regret S hS (env φ θ) ≤ ε) ↔
      0 ≤ ε ∧ ∀ z, z ∉ S → ∃ p ∈ simplex S,
        (contrast φ S z p).ofLp ⬝ᵥ m.ofLp +
          β * Real.sqrt (qinv V (contrast φ S z p).ofLp) ≤ ε := by
  obtain ⟨L, hnorm, hset⟩ := exists_ellipsoid_map hV hlam
  have key := ellipsoid_certificate_iff (ε := ε) hS hβ φ m L
  rw [hset m β hβ] at key
  have hobj : ∀ z (p : S → ℝ), ellObj φ S m L β z p =
      (contrast φ S z p).ofLp ⬝ᵥ m.ofLp +
        β * Real.sqrt (qinv V (contrast φ S z p).ofLp) := by
    intro z p
    rw [ellObj, hnorm, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm]
  simp only [hobj] at key
  exact key

/-- **Width of the safeguarded contrast at an uncertified step, from the certificate.**
If the support `S` is not certified at level `ε ≥ 0` over the confidence ellipsoid of `V`,
some excluded challenger `z` has `ε < ⟨g, m⟩ + β √(gᵀ V⁻¹ g)` for *every* inside-mixture
contrast `g = g_{z,p}` (hypothesis `hD` of `cd_width`), and therefore every such contrast
that satisfies the safeguard alternative `hcase` of `cd_width` has
`‖g‖²_{V⁻¹} > ε² / (4 β²)` (`eq:cd-width-lemma`). -/
theorem cd_width_of_uncertified {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam)
    (hlam : 0 < lam) {S : Finset Z} (hS : S.Nonempty) {β ε : ℝ} (hβ : 0 < β) (hε : 0 ≤ ε)
    (φ : Z → EuclideanSpace ℝ n) (m : EuclideanSpace ℝ n)
    (hunc : ¬ ∀ θ : EuclideanSpace ℝ n, (θ - m).ofLp ⬝ᵥ V *ᵥ (θ - m).ofLp ≤ β ^ 2 →
        regret S hS (env φ θ) ≤ ε) :
    ∃ z, z ∉ S ∧ ∀ p ∈ simplex S,
      ε < (contrast φ S z p).ofLp ⬝ᵥ m.ofLp +
          β * Real.sqrt (qinv V (contrast φ S z p).ofLp) ∧
      (((contrast φ S z p).ofLp ⬝ᵥ m.ofLp ≤ ε / 2 ∨
          ∃ fz fy : n → ℝ, (contrast φ S z p).ofLp = fz - fy ∧
            fz ⬝ᵥ m.ofLp + β * Real.sqrt (qinv V fz) ≤
              fy ⬝ᵥ m.ofLp + β * Real.sqrt (qinv V fy)) →
        ε ^ 2 / (4 * β ^ 2) < qinv V (contrast φ S z p).ofLp) := by
  rw [confidence_ellipsoid_certificate_iff hV hlam hS hβ.le φ m] at hunc
  push Not at hunc
  obtain ⟨z, hz, hall⟩ := hunc hε
  exact ⟨z, hz, fun p hp => ⟨hall p hp, fun hcase =>
    cd_width hV hlam hε hβ m.ofLp _ (hall p hp) hcase⟩⟩

end Identification

end JointRootCert
