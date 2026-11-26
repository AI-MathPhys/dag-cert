/-
Literal forms of main-text and Appendix A--C statements, part 1.

* `lem:active-inversion` (Explicit confidence-width inversion): the inversion threshold
  `n_{M,δ}(r) = min {n ≥ 1 : 2 √(log (4 M n² / δ) / (2 n)) < r}` as a Lean object
  (`invCount`, `invCount_isLeast`) and the lemma as stated (`active_inversion_literal`).
* `thm:active-er` (Finite-sample support-sensitive acquisition): the three bounds with
  `n_{M,δ}` for an infinite run of Algorithm `alg:certify` and its first certified time
  (`active_er_literal`, `active_sg_literal`, `active_os_literal`), with no properness
  restriction on the supports, and halting on every history for `ε > 0`
  (`active_er_halts`, `active_sg_halts`, `active_os_halts`).
* `lem:nested-interval-valid` (Anytime validity and nesting of terminal boxes): the
  empirical-Bernstein running-intersection boxes (`eb_box_coverage`, `eb_box_nested`).
* `cor:shared-regret-pac` (Anytime-valid root commitment) with a stopping event
  (`anytime_valid_commitment_stopping`, `anytime_valid_commitment_box_stopping`).
* `lem:bay-reduction` (Joint-set reduction) for nonempty compact sets with attained maxima
  (`bay_reduction_compact`, `bay_reduction_literal`).
* `thm:t2-hull` (Feature-hull dominance), the bound
  `B · max_{z ∉ S(a)} inf_{p ∈ P_a} ‖φ_z - p‖` (`regret_le_hullGap`).
-/
import JointRootCert.Completions2
import JointRootCert.EmpiricalBernstein
import JointRootCert.FeatureHull

namespace JointRootCert

namespace LiteralABC

open Finset MeasureTheory
open scoped ENNReal

/-! ### The inversion threshold `n_{M,δ}(r)` (`eq:active-inversion`, `lem:active-inversion`) -/

section Inversion

/-- The inversion threshold `n_{M,δ}(r) = min {n ≥ 1 : 2 √(log (4 M n² / δ) / (2 n)) < r}`
of `eq:active-inversion` (the least element is `sInf` in `ℕ`; the set is nonempty for
`M ≥ 2`, `0 < δ < 1`, `r > 0`, see `invCount_isLeast`). -/
noncomputable def invCount (M δ r : ℝ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ hoeffdingWidth M δ (n : ℝ) < r}

/-- The definition written out with the manuscript's expression for the width. -/
theorem invCount_eq (M δ r : ℝ) :
    invCount M δ r =
      sInf {n : ℕ | 1 ≤ n ∧
        2 * Real.sqrt (Real.log (4 * M * (n : ℝ) ^ 2 / δ) / (2 * (n : ℝ))) < r} := rfl

lemma one_le_ceil_inversion {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    1 ≤ ⌈32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2))⌉₊ := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2le : r ^ 2 ≤ 1 := by nlinarith
  have harg : 1 < 32 * M / (δ * r ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hδ1.le hr2le hr2.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hpos : 0 < 32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2)) :=
    mul_pos (by positivity) (Real.log_pos harg)
  exact Nat.ceil_pos.mpr hpos

lemma invCount_set_nonempty {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hr0 : 0 < r) : {n : ℕ | 1 ≤ n ∧ hoeffdingWidth M δ (n : ℝ) < r}.Nonempty := by
  have hr'0 : 0 < min r 1 := lt_min hr0 one_pos
  have hr'1 : min r 1 ≤ 1 := min_le_right _ _
  refine ⟨⌈32 / (min r 1) ^ 2 * Real.log (32 * M / (δ * (min r 1) ^ 2))⌉₊,
    one_le_ceil_inversion hM hδ0 hδ1 hr'0 hr'1, ?_⟩
  exact (width_inversion_nat hM hδ0 hδ1 hr'0 hr'1 le_rfl).trans_le (min_le_left _ _)

/-- `n_{M,δ}(r)` is the least `n ≥ 1` whose width `2 β(n)` is below `r`; it exists for
`M ≥ 2`, `0 < δ < 1` and every `r > 0`. -/
theorem invCount_isLeast {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) :
    IsLeast {n : ℕ | 1 ≤ n ∧ hoeffdingWidth M δ (n : ℝ) < r} (invCount M δ r) :=
  ⟨Nat.sInf_mem (invCount_set_nonempty hM hδ0 hδ1 hr0), fun _ hn => Nat.sInf_le hn⟩

/-- **Explicit confidence-width inversion (Lemma `lem:active-inversion`), as stated.**
For `M ≥ 2`, `0 < δ < 1` and `0 < r ≤ 1`,
`n_{M,δ}(r) ≤ ⌈(32 / r²) log (32 M / (δ r²))⌉`. -/
theorem active_inversion_literal {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    invCount M δ r ≤ ⌈32 / r ^ 2 * Real.log (32 * M / (δ * r ^ 2))⌉₊ :=
  Nat.sInf_le ⟨one_le_ceil_inversion hM hδ0 hδ1 hr0 hr1,
    width_inversion_nat hM hδ0 hδ1 hr0 hr1 le_rfl⟩

/-- A running-intersection Hoeffding interval at count `n ≥ n₀ ≥ 1` is no wider than the
Hoeffding interval at count `n₀` (nesting: `runLo_mono`, `runHi_anti`). -/
lemma run_width_le_of_le (M δ : ℝ) (x : ℕ → ℝ) {n0 n : ℕ} (h0 : 1 ≤ n0) (h : n0 ≤ n) :
    runHi (hoeffHi M δ x) n - runLo (hoeffLo M δ x) n ≤ hoeffdingWidth M δ n0 := by
  have h1 : runHi (hoeffHi M δ x) n ≤ runHi (hoeffHi M δ x) n0 := runHi_anti _ h
  have h2 : runLo (hoeffLo M δ x) n0 ≤ runLo (hoeffLo M δ x) n := runLo_mono _ h
  have h3 := run_width_le M δ x n0
  have hne : n0 ≠ 0 := by omega
  simp only [nestedWidth, hne, ↓reduceIte] at h3
  linarith

variable {Z : Type*} [DecidableEq Z]

/-- Once a terminal has `n_{M,δ}(r)` observations its box is narrower than `r`, at that
time and at every later time. -/
lemma tape_width_lt {M δ r : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (x : Z → ℕ → ℝ) (sel : ℕ → Z) (t : ℕ) (z : Z)
    (h : invCount M δ r ≤ queryCount sel t z) :
    tapeHi M δ x sel t z - tapeLo M δ x sel t z < r :=
  lt_of_le_of_lt (run_width_le_of_le M δ (x z) (invCount_isLeast hM hδ0 hδ1 hr0).1.1 h)
    (invCount_isLeast hM hδ0 hδ1 hr0).1.2

/-- **Counting with the thresholds `n_{M,δ}`.**  Along an infinite selection sequence, if
at every time at which `halt` fails the queried terminal is at least as wide as
`ρ z > 0`, then `halt` holds at some time `t ≤ ∑_z n_{M,δ}(ρ_z)`. -/
theorem exists_halt_le_sum_invCount [Fintype Z] {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (x : Z → ℕ → ℝ) (sel : ℕ → Z) (ρ : Z → ℝ) (hρ : ∀ z, 0 < ρ z)
    (halt : ℕ → Prop)
    (hrule : ∀ t, ¬ halt t →
      ρ (sel t) ≤ tapeHi M δ x sel t (sel t) - tapeLo M δ x sel t (sel t)) :
    ∃ t, t ≤ ∑ z, invCount M δ (ρ z) ∧ halt t := by
  by_contra hcon
  have hall : ∀ t, t ≤ ∑ z, invCount M δ (ρ z) → ¬ halt t := fun t ht hh => hcon ⟨t, ht, hh⟩
  have hsteps := steps_le_sum_budget (∑ z, invCount M δ (ρ z) + 1) sel
    (fun z => invCount M δ (ρ z)) (fun t ht => by
      by_contra hge
      have hge' : invCount M δ (ρ (sel t)) ≤ queryCount sel t (sel t) := not_lt.mp hge
      have h1 := tape_width_lt hM hδ0 hδ1 (hρ (sel t)) x sel t (sel t) hge'
      have h2 := hrule t (hall t (by omega))
      linarith)
  omega

end Inversion

/-! ### Runs of Algorithm `alg:certify` and the first certified time -/

section Runs

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}
variable {S : Finset Z} {hS : S.Nonempty} {l u : Z → ℝ} {ε : ℝ}

/-- The exact certificate `𝓡_t(a)` for an arbitrary nonempty support: the outside-support
expression `rectCert` for a proper support and `0` for full support (Theorem
`thm:shared-regret`).  It is the robust regret over the box, see
`exactCert_eq_robustRegret`. -/
noncomputable def exactCert (S : Finset Z) (hS : S.Nonempty) (l u : Z → ℝ) : ℝ :=
  if h : Sᶜ.Nonempty then rectCert S hS h l u else 0

omit [Nonempty Z] in
lemma exactCert_of_proper (hSc : Sᶜ.Nonempty) :
    exactCert S hS l u = rectCert S hS hSc l u := by
  simp only [exactCert, hSc, ↓reduceDIte]

omit [Nonempty Z] in
lemma exactCert_of_full (hSc : ¬ Sᶜ.Nonempty) : exactCert S hS l u = 0 := by
  simp only [exactCert, hSc, ↓reduceDIte]

omit [Nonempty Z] in
lemma exactCert_nonneg : 0 ≤ exactCert S hS l u := by
  by_cases h : Sᶜ.Nonempty
  · rw [exactCert_of_proper h]
    exact le_max_left _ _
  · rw [exactCert_of_full h]

/-- For a nonempty box the exact certificate is the robust regret
`sup_{f ∈ box} r_f(a)`, for proper and full supports alike. -/
theorem exactCert_eq_robustRegret (hlu : l ≤ u) :
    exactCert S hS l u = robustRegret S hS (Set.Icc l u) := by
  by_cases h : Sᶜ.Nonempty
  · rw [exactCert_of_proper h, robustRegret_box hlu h]
  · rw [exactCert_of_full h, robustRegret_box_full hlu (not_nonempty_iff_eq_empty.mp h)]

lemma regret_le_exactCert {μ : Z → ℝ} (hμ : μ ∈ Set.Icc l u) :
    regret S hS μ ≤ exactCert S hS l u := by
  by_cases h : Sᶜ.Nonempty
  · rw [exactCert_of_proper h]
    exact regret_le_rectCert h hμ
  · rw [exactCert_of_full h]
    exact (regret_eq_zero_of_compl_empty (not_nonempty_iff_eq_empty.mp h)).le

/-- The stopping test of Algorithm `alg:certify` on the box `[l, u]`:
`min_a 𝓡(a) ≤ ε`, i.e. some action has exact certificate at most `ε`. -/
def Certified (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (l u : Z → ℝ) (ε : ℝ) :
    Prop :=
  ∃ a, exactCert (supp a) (hne a) l u ≤ ε

omit [Nonempty Z] in
/-- A full-support action passes the stopping test on every box when `ε ≥ 0`. -/
lemma certified_of_full (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hε : 0 ≤ ε)
    {a : A} (ha : ¬ (supp a)ᶜ.Nonempty) : Certified supp hne l u ε :=
  ⟨a, by rw [exactCert_of_full ha]; exact hε⟩

/-- The first time at which `p` holds (`0` if it never holds). -/
noncomputable def firstTime (p : ℕ → Prop) : ℕ := sInf {t | p t}

lemma firstTime_spec {p : ℕ → Prop} (h : ∃ t, p t) : p (firstTime p) := Nat.sInf_mem h

lemma firstTime_le {p : ℕ → Prop} {t : ℕ} (h : p t) : firstTime p ≤ t := Nat.sInf_le h

lemma not_of_lt_firstTime {p : ℕ → Prop} {t : ℕ} (h : t < firstTime p) : ¬ p t :=
  fun hp => absurd (firstTime_le hp) (not_le.mpr h)

/-- **An infinite run of Algorithm `alg:certify`** on the reward tapes `x`, with
running-intersection Hoeffding boxes `[tapeLo, tapeHi]`.  `sel t` is the terminal queried
at step `t`.  At every time at which the stopping test fails and the box is nonempty (no
confidence failure), the queried terminal obeys the selection rule `step` on the current
box.  Nothing is required at other times. -/
def ActiveRun (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (M δ ε : ℝ)
    (step : (Z → ℝ) → (Z → ℝ) → Z → Prop) (x : Z → ℕ → ℝ) (sel : ℕ → Z) : Prop :=
  ∀ t, ¬ Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε →
    tapeLo M δ x sel t ≤ tapeHi M δ x sel t →
    step (tapeLo M δ x sel t) (tapeHi M δ x sel t) (sel t)

/-- The stopping time `τ` of a run: the first time at which the stopping test passes. -/
noncomputable def stopTime (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (M δ ε : ℝ)
    (x : Z → ℕ → ℝ) (sel : ℕ → Z) : ℕ :=
  firstTime fun t => Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε

/-- The ER rule of Algorithm `alg:certify` (`ERStep`).  A continuing step occurs only when
no action is certified; for `ε ≥ 0` every support is then proper (`certified_of_full`), so
the properness proof required by `ERStep` exists. -/
def ERRule (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (l u : Z → ℝ)
    (z : Z) : Prop :=
  ∃ hpr : ∀ a, (supp a)ᶜ.Nonempty, ERStep supp hne hpr l u ε z

/-- The Safeguarded-LCB rule (`SGStep`, `eq:safeguard-gate`). -/
def SGRule (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (l u : Z → ℝ)
    (z : Z) : Prop :=
  ∃ hpr : ∀ a, (supp a)ᶜ.Nonempty, SGStep supp hne hpr l u ε z

/-- The optimistic-separation rule (`OSStep`). -/
def OSRule (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (l u : Z → ℝ)
    (z : Z) : Prop :=
  ∃ hpr : ∀ a, (supp a)ᶜ.Nonempty, OSStep supp hne hpr l u ε z

/-- **A covered run stops within `∑_z n_{M,δ}(ρ_z)` queries.**  For a run obeying `step`,
if on boxes containing the true means `m` a continuing step queries a terminal at least as
wide as `ρ z > 0`, then on a covered path the stopping time exists, is at most
`∑_z n_{M,δ}(ρ_z)`, and every action certified at the stopping time is `ε`-optimal. -/
theorem active_run_covered {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) {ε : ℝ}
    (step : (Z → ℝ) → (Z → ℝ) → Z → Prop) {x : Z → ℕ → ℝ} {sel : ℕ → Z} {m : Z → ℝ}
    (ρ : Z → ℝ) (hρ : ∀ z, 0 < ρ z)
    (hrun : ActiveRun supp hne M δ ε step x sel) (hcovd : tapeCovered M δ x sel m)
    (hwidth : ∀ l u z, m ∈ Set.Icc l u → step l u z → ρ z ≤ u z - l z) :
    (∃ t, Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε) ∧
      stopTime supp hne M δ ε x sel ≤ ∑ z, invCount M δ (ρ z) ∧
      ∀ a, exactCert (supp a) (hne a) (tapeLo M δ x sel (stopTime supp hne M δ ε x sel))
          (tapeHi M δ x sel (stopTime supp hne M δ ε x sel)) ≤ ε →
        regret (supp a) (hne a) m ≤ ε := by
  obtain ⟨t, ht, hc⟩ := exists_halt_le_sum_invCount hM hδ0 hδ1 x sel ρ hρ
    (fun t => Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε)
    (fun t hnc => hwidth _ _ _ (hcovd t)
      (hrun t hnc (fun z => ((hcovd t).1 z).trans ((hcovd t).2 z))))
  exact ⟨⟨t, hc⟩, (firstTime_le hc).trans ht,
    fun a ha => (regret_le_exactCert (hcovd _)).trans ha⟩

omit [Nonempty Z] in
/-- **Halting on every history.**  If on every nonempty box a continuing step queries a
terminal of width at least `ρ₀ > 0` (no coverage assumed), then within `∑_z n_{M,δ}(ρ₀)`
queries the run either reports a confidence failure (an empty box) or passes the stopping
test. -/
theorem active_run_halts {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) {ε : ℝ}
    (step : (Z → ℝ) → (Z → ℝ) → Z → Prop) {x : Z → ℕ → ℝ} {sel : ℕ → Z}
    {ρ0 : ℝ} (hρ0 : 0 < ρ0) (hrun : ActiveRun supp hne M δ ε step x sel)
    (hwidth : ∀ l u z, l ≤ u → step l u z → ρ0 ≤ u z - l z) :
    ∃ t, t ≤ ∑ _z : Z, invCount M δ ρ0 ∧
      (¬ tapeLo M δ x sel t ≤ tapeHi M δ x sel t ∨
        Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε) := by
  refine exists_halt_le_sum_invCount hM hδ0 hδ1 x sel (fun _ => ρ0) (fun _ => hρ0)
    (fun t => ¬ tapeLo M δ x sel t ≤ tapeHi M δ x sel t ∨
      Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε) (fun t hnh => ?_)
  have hlu : tapeLo M δ x sel t ≤ tapeHi M δ x sel t := by
    by_contra h
    exact hnh (Or.inl h)
  exact hwidth _ _ _ hlu (hrun t (fun hc => hnh (Or.inr hc)) hlu)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Coverage, stopping, correctness and the `n_{M,δ}` bound, with probability.**
Reward-tape model of `hoeffding_box_coverage`.  On every sample path the sampler is a run
(`ActiveRun`) of the rule `step`.  With probability at least `1 - δ` the stopping time
exists, is at most `∑_z n_{M,δ}(ρ_z)`, and every action certified at the stopping time (in
particular the returned minimiser) is `ε`-optimal. -/
theorem active_run_whp (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) {ε : ℝ}
    (step : (Z → ℝ) → (Z → ℝ) → Z → Prop) (ρ : Z → ℝ) (hρ : ∀ z, 0 < ρ z)
    (sel : Ω → ℕ → Z)
    (hrun : ∀ ω, ActiveRun supp hne M δ ε step (fun z i => X z i ω) (sel ω))
    (hwidth : ∀ l u z, m ∈ Set.Icc l u → step l u z → ρ z ≤ u z - l z) :
    P {ω | ¬ ((∃ t, Certified supp hne (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε) ∧
        stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω) ≤ ∑ z, invCount M δ (ρ z) ∧
        ∀ a, exactCert (supp a) (hne a)
            (tapeLo M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω)))
            (tapeHi M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω))) ≤ ε →
          regret (supp a) (hne a) m ≤ ε)} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (tape_coverage P hindep hmeas hbdd hmean (by linarith) hcard
    hδ0 hδ1.le sel)
  intro ω hω hcovd
  exact hω (active_run_covered hM hδ0 hδ1 supp hne step ρ hρ (hrun ω) hcovd hwidth)

/-! ### Theorem `thm:active-er`, the three bounds -/

/-- **Exact-regret sampling (Theorem `thm:active-er`, ER bound), as stated.**

Reward-tape model: for each terminal the observations are independent, `[0,1]`-valued,
with mean `m z`; `M ≥ max {2, |Z|}`, `0 < δ < 1`, `ε > 0`; the supports are nonempty and
cover `Z` (full supports are allowed).  On every sample path the sampler is an infinite
run of Algorithm `alg:certify` with the ER rule on running-intersection Hoeffding boxes.
With probability at least `1 - δ` (on simultaneous coverage) the stopping time `τ_ER`
exists,

`τ_ER ≤ ∑_z n_{M,δ}(max {ε, Δ_z / 2})`, `Δ_z = μ_* - μ_z`,

and every action certified at `τ_ER` is `ε`-optimal. -/
theorem active_er_literal (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε : ℝ} (hε0 : 0 < ε) (sel : Ω → ℕ → Z)
    (hrun : ∀ ω, ActiveRun supp hne M δ ε (ERRule supp hne ε) (fun z i => X z i ω) (sel ω)) :
    P {ω | ¬ ((∃ t, Certified supp hne (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε) ∧
        stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω) ≤
          ∑ z, invCount M δ (max ε ((gmax m - m z) / 2)) ∧
        ∀ a, exactCert (supp a) (hne a)
            (tapeLo M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω)))
            (tapeHi M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω))) ≤ ε →
          regret (supp a) (hne a) m ≤ ε)} ≤ ENNReal.ofReal δ :=
  active_run_whp P hindep hmeas hbdd hmean hM hcard hδ0 hδ1 supp hne (ERRule supp hne ε)
    (fun z => max ε ((gmax m - m z) / 2)) (fun _ => lt_max_of_lt_left hε0) sel hrun
    (fun _ _ _ hμ ⟨hpr, h⟩ => erStep_width supp hne hpr hcov hε0.le hμ h)

/-- **Safeguarded-LCB (Theorem `thm:active-er`, SG bound), as stated.**  Same model as
`active_er_literal`, with the Safeguarded-LCB rule:
`τ_SG ≤ ∑_z n_{M,δ}(max {ε / 2, Δ_z / 3})`. -/
theorem active_sg_literal (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε : ℝ} (hε0 : 0 < ε) (sel : Ω → ℕ → Z)
    (hrun : ∀ ω, ActiveRun supp hne M δ ε (SGRule supp hne ε) (fun z i => X z i ω) (sel ω)) :
    P {ω | ¬ ((∃ t, Certified supp hne (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε) ∧
        stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω) ≤
          ∑ z, invCount M δ (max (ε / 2) ((gmax m - m z) / 3)) ∧
        ∀ a, exactCert (supp a) (hne a)
            (tapeLo M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω)))
            (tapeHi M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω))) ≤ ε →
          regret (supp a) (hne a) m ≤ ε)} ≤ ENNReal.ofReal δ :=
  active_run_whp P hindep hmeas hbdd hmean hM hcard hδ0 hδ1 supp hne (SGRule supp hne ε)
    (fun z => max (ε / 2) ((gmax m - m z) / 3)) (fun _ => lt_max_of_lt_left (by linarith)) sel
    hrun (fun _ _ _ hμ ⟨hpr, h⟩ => sgStep_width supp hne hpr hcov hε0.le hμ h)

/-- **Optimistic separation (Theorem `thm:active-er`, OS bound), as stated.**  Same model
as `active_er_literal`, with the optimistic-separation rule, `ε ≥ 0` and `Γ + ε > 0` (so
`ε = 0` is permitted when `Γ > 0`), where `Γ = max_a [V(a) - max_{z ∉ S(a)} μ_z]` (`hΓ`;
the maximum is over proper supports, and if some support is full the run stops at time
`0`, whatever `Γ` is):
`τ_OS ≤ ∑_z n_{M,δ}(max {Γ + ε, Δ_z} / 2)`. -/
theorem active_os_literal (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε Γ : ℝ} (hε0 : 0 ≤ ε)
    (hΓ : ∀ hpr : ∀ a, (supp a)ᶜ.Nonempty,
      IsGreatest (Set.range fun a => val (supp a) (hne a) m - (supp a)ᶜ.sup' (hpr a) m) Γ)
    (hpos : 0 < Γ + ε) (sel : Ω → ℕ → Z)
    (hrun : ∀ ω, ActiveRun supp hne M δ ε (OSRule supp hne ε) (fun z i => X z i ω) (sel ω)) :
    P {ω | ¬ ((∃ t, Certified supp hne (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε) ∧
        stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω) ≤
          ∑ z, invCount M δ (max (Γ + ε) (gmax m - m z) / 2) ∧
        ∀ a, exactCert (supp a) (hne a)
            (tapeLo M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω)))
            (tapeHi M δ (fun z i => X z i ω) (sel ω)
              (stopTime supp hne M δ ε (fun z i => X z i ω) (sel ω))) ≤ ε →
          regret (supp a) (hne a) m ≤ ε)} ≤ ENNReal.ofReal δ := by
  refine active_run_whp P hindep hmeas hbdd hmean hM hcard hδ0 hδ1 supp hne (OSRule supp hne ε)
    (fun z => max (Γ + ε) (gmax m - m z) / 2)
    (fun z => by have := le_max_left (Γ + ε) (gmax m - m z); linarith) sel hrun ?_
  rintro l u z hμ ⟨hpr, h⟩
  obtain ⟨a0, ha0⟩ := (hΓ hpr).1
  have ha0' : val (supp a0) (hne a0) m - (supp a0)ᶜ.sup' (hpr a0) m = Γ := ha0
  have hw := osStep_width supp hne hpr hcov hε0 hμ a0 h
  rw [ha0'] at hw
  exact hw

omit [DecidableEq Z] [Nonempty Z] in
/-- **The explicit form of the three bounds.**  For thresholds `0 < ρ z ≤ 1` (which holds
for the three choices of Theorem `thm:active-er` when `ε ≤ 1`, the means being in `[0,1]`),
`∑_z n_{M,δ}(ρ_z) ≤ ∑_z ⌈(32 / ρ_z²) log (32 M / (δ ρ_z²))⌉` (Lemma
`lem:active-inversion` termwise). -/
theorem sum_invCount_le {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ρ : Z → ℝ)
    (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ 1) :
    ∑ z, invCount M δ (ρ z) ≤
      ∑ z, ⌈32 / ρ z ^ 2 * Real.log (32 * M / (δ * ρ z ^ 2))⌉₊ :=
  sum_le_sum fun z _ => active_inversion_literal hM hδ0 hδ1 (hρ z).1 (hρ z).2

/-- **Termination of exact-regret sampling on all nonfailed histories** (last sentence of
the proof of the ER bound): for `ε > 0`, on every tape (no coverage, no probability), a run
of the ER rule passes the stopping test or reports a confidence failure within
`∑_z n_{M,δ}(ε)` queries. -/
theorem active_er_halts {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε0 : 0 < ε) {x : Z → ℕ → ℝ} {sel : ℕ → Z}
    (hrun : ActiveRun supp hne M δ ε (ERRule supp hne ε) x sel) :
    ∃ t, t ≤ ∑ _z : Z, invCount M δ ε ∧
      (¬ tapeLo M δ x sel t ≤ tapeHi M δ x sel t ∨
        Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε) := by
  refine active_run_halts hM hδ0 hδ1 supp hne (ERRule supp hne ε) hε0 hrun ?_
  rintro l u z hlu ⟨hpr, a, p, q, hmin, hcont, hp, hpmax, hq, hqmax, hsel⟩
  obtain ⟨h1, -⟩ := active_width supp hne hpr hcov hlu hε0.le a hmin hcont hp hpmax hq hqmax
  rcases hsel with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · rw [max_eq_left hw] at h1
    exact h1.le
  · rw [max_eq_right hw] at h1
    exact h1.le

/-- **Termination of Safeguarded-LCB on all nonfailed histories**: for `ε > 0`, within
`∑_z n_{M,δ}(ε / 2)` queries. -/
theorem active_sg_halts {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε0 : 0 < ε) {x : Z → ℕ → ℝ} {sel : ℕ → Z}
    (hrun : ActiveRun supp hne M δ ε (SGRule supp hne ε) x sel) :
    ∃ t, t ≤ ∑ _z : Z, invCount M δ (ε / 2) ∧
      (¬ tapeLo M δ x sel t ≤ tapeHi M δ x sel t ∨
        Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε) := by
  refine active_run_halts hM hδ0 hδ1 supp hne (SGRule supp hne ε) (half_pos hε0) hrun ?_
  rintro l u z hlu ⟨hpr, a, p, q, hmin, hcont, hp, hpmax, hq, hqmax, hsel⟩
  rcases hsel with hER | ⟨y, hy, hymax, hg1, hg2, hsel⟩
  · obtain ⟨h1, -⟩ := active_width supp hne hpr hcov hlu hε0.le a hmin hcont hp hpmax hq hqmax
    rcases hER with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
    · rw [max_eq_left hw] at h1
      linarith
    · rw [max_eq_right hw] at h1
      linarith
  · obtain ⟨h1, -⟩ := active_sg_width supp hne hpr hcov hlu hε0.le a hmin hcont hp hpmax hq
      hqmax hy hymax hg1 hg2
    rcases hsel with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
    · rw [max_eq_left hw] at h1
      exact h1.le
    · rw [max_eq_right hw] at h1
      exact h1.le

/-- **Termination of optimistic separation on all nonfailed histories**: for `ε > 0`,
within `∑_z n_{M,δ}(ε / 2)` queries. -/
theorem active_os_halts {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε0 : 0 < ε) {x : Z → ℕ → ℝ} {sel : ℕ → Z}
    (hrun : ActiveRun supp hne M δ ε (OSRule supp hne ε) x sel) :
    ∃ t, t ≤ ∑ _z : Z, invCount M δ (ε / 2) ∧
      (¬ tapeLo M δ x sel t ≤ tapeHi M δ x sel t ∨
        Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε) := by
  refine active_run_halts hM hδ0 hδ1 supp hne (OSRule supp hne ε) (half_pos hε0) hrun ?_
  rintro l u z hlu ⟨hpr, hfail, b, p, q, hmax, hp, hpmax, hq, hqmax, hsel⟩
  obtain ⟨h1, -⟩ := active_os_width supp hne hpr hcov hlu hε0.le b hmax (hfail b) hp hpmax hq
    hqmax
  rcases hsel with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · rw [max_eq_left hw] at h1
    exact h1.le
  · rw [max_eq_right hw] at h1
    exact h1.le

end Runs

/-! ### `lem:nested-interval-valid`: empirical-Bernstein running-intersection boxes -/

section EBBox

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Lower endpoint of the empirical-Bernstein interval `I^{EB}_{z,n}` of
`app:variance-cs` on the sample path `ω` (`I_{z,0} = [0,1]`), with `L = log (2 M / δ)`. -/
noncomputable def ebLo (L : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    max 0 ((∑ i ∈ range n, ebLam L X i ω * X i ω -
        (L + ∑ i ∈ range n, (X i ω - ebMu X i ω) ^ 2 * psiE (ebLam L X i ω))) /
      ∑ i ∈ range n, ebLam L X i ω)

/-- Upper endpoint of the empirical-Bernstein interval `I^{EB}_{z,n}`. -/
noncomputable def ebHi (L : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  if n = 0 then 1 else
    min 1 ((∑ i ∈ range n, ebLam L X i ω * X i ω +
        (L + ∑ i ∈ range n, (X i ω - ebMu X i ω) ^ 2 * psiE (ebLam L X i ω))) /
      ∑ i ∈ range n, ebLam L X i ω)

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- **Anytime validity of the empirical-Bernstein terminal boxes (Lemma
`lem:nested-interval-valid`, empirical-Bernstein schedule).**  `B_t = ∏_z [l_t(z), u_t(z)]`
where `[l_t(z), u_t(z)]` is the running intersection of `[0,1]` and the intervals
`I^{EB}_{z,k}`, `1 ≤ k ≤ N_t(z)`.  In the reward-tape model (independent `[0,1]`-valued
observations with mean `m z` for each terminal) and for arbitrary path-dependent counts
`N t ω z`, `P(∃ t, μ ∉ B_t) ≤ δ`.  Here `M = |Z|` and `δ < 2 M`. -/
theorem eb_box_coverage [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ)
    (hδM : δ < 2 * Fintype.card Z) (X : Z → ℕ → Ω → ℝ) (m : Z → ℝ)
    (hXm : ∀ z i, Measurable (X z i)) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) μ)
    (hX : ∀ z i ω, X z i ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ z i, ∫ ω, X z i ω ∂μ = m z)
    (N : ℕ → Ω → Z → ℕ) :
    μ {ω | ∃ t z, m z ∉ Set.Icc
        (runLo (ebLo (Real.log (2 * Fintype.card Z / δ)) (X z) ω) (N t ω z))
        (runHi (ebHi (Real.log (2 * Fintype.card Z / δ)) (X z) ω) (N t ω z))} ≤
      ENNReal.ofReal δ := by
  have hm01 : ∀ z, m z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    have hint : Integrable (X z 0) μ :=
      Integrable.of_mem_Icc 0 1 (hXm z 0).aemeasurable (Filter.Eventually.of_forall (hX z 0))
    rw [← hmean z 0]
    constructor
    · exact integral_nonneg fun ω => (hX z 0 ω).1
    · have := integral_mono hint (integrable_const (1 : ℝ)) fun ω => (hX z 0 ω).2
      simpa using this
  refine (measure_mono ?_).trans (eb_coverage_iid hδ hδM X m hXm hindep hX hmean)
  rintro ω ⟨t, z, hnot⟩
  by_contra hgood
  apply hnot
  apply mem_run_Icc
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [ebLo, ebHi] using hm01 z
  · have hne : k ≠ 0 := by omega
    simp only [ebLo, ebHi, hne, ↓reduceIte]
    by_contra h
    exact hgood ⟨z, k, hk, h⟩

omit [Fintype Z] [Nonempty Z] in
/-- Nesting of the empirical-Bernstein boxes (instance of `box_nested`). -/
theorem eb_box_nested (L : ℝ) (X : Z → ℕ → Ω → ℝ) (ω : Ω) (N : ℕ → Z → ℕ)
    (hN : ∀ t z, N t z ≤ N (t + 1) z) (t : ℕ) (z : Z) :
    runLo (ebLo L (X z) ω) (N t z) ≤ runLo (ebLo L (X z) ω) (N (t + 1) z) ∧
      runHi (ebHi L (X z) ω) (N (t + 1) z) ≤ runHi (ebHi L (X z) ω) (N t z) :=
  box_nested (fun z => ebLo L (X z) ω) (fun z => ebHi L (X z) ω) N hN t z

end EBBox

/-! ### `cor:shared-regret-pac` with a stopping event -/

section Stopping

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}
variable {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ}

omit [DecidableEq Z] in
/-- **Anytime-valid root commitment (Corollary `cor:shared-regret-pac`), with a stopping
event.**  `out ω` is the outcome of the procedure on the sample path `ω`: `none` if it
never stops, `some (t, a)` if it stops at time `t` and returns `a`; it may depend on the
whole path in an arbitrary way (any adaptive sampling and stopping policy).  If the
confidence sets `C t ω` cover `μ` simultaneously outside an event of probability at most
`δ`, and the procedure only returns actions whose regret is at most `ε` on all of
`C t ω`, then the error event "stops and returns an action with regret above `ε`" has
probability at most `δ`. -/
theorem anytime_valid_commitment_stopping (P : Measure Ω) (μ : Z → ℝ) (δ : ENNReal)
    (C : ℕ → Ω → Set (Z → ℝ)) (supp : A → Finset Z) (hsupp : ∀ a, (supp a).Nonempty)
    (out : Ω → Option (ℕ × A))
    (hcover : P {ω | ∃ t, μ ∉ C t ω} ≤ δ)
    (hcert : ∀ ω t a, out ω = some (t, a) →
      ∀ f ∈ C t ω, regret (supp a) (hsupp a) f ≤ ε) :
    P {ω | ∃ t a, out ω = some (t, a) ∧ ε < regret (supp a) (hsupp a) μ} ≤ δ := by
  refine (measure_mono ?_).trans hcover
  rintro ω ⟨t, a, ho, hlt⟩
  exact ⟨t, fun hmem => absurd (hcert ω t a ho μ hmem) (not_le.mpr hlt)⟩

/-- **The rectangular instance, as stated**: under simultaneous coverage of the terminal
boxes (`eq:terminal-box`), returning any action whose robust regret over the current box
is at most `ε` incurs error probability at most `δ`.  Supports may be proper or full. -/
theorem anytime_valid_commitment_box_stopping (P : Measure Ω) (μ : Z → ℝ) (δ : ENNReal)
    (l u : ℕ → Ω → Z → ℝ) (supp : A → Finset Z) (hsupp : ∀ a, (supp a).Nonempty)
    (out : Ω → Option (ℕ × A))
    (hcover : P {ω | ∃ t, μ ∉ Set.Icc (l t ω) (u t ω)} ≤ δ)
    (hcert : ∀ ω t a, out ω = some (t, a) →
      robustRegret (supp a) (hsupp a) (Set.Icc (l t ω) (u t ω)) ≤ ε) :
    P {ω | ∃ t a, out ω = some (t, a) ∧ ε < regret (supp a) (hsupp a) μ} ≤ δ := by
  refine (measure_mono ?_).trans hcover
  rintro ω ⟨t, a, ho, hlt⟩
  refine ⟨t, fun hmem => ?_⟩
  have hlu : l t ω ≤ u t ω := fun z => (hmem.1 z).trans (hmem.2 z)
  have h1 : regret (supp a) (hsupp a) μ ≤ exactCert (supp a) (hsupp a) (l t ω) (u t ω) :=
    regret_le_exactCert hmem
  rw [exactCert_eq_robustRegret hlu] at h1
  have h2 := hcert ω t a ho
  linarith

end Stopping

/-! ### `lem:bay-reduction` for nonempty compact sets, with attained maxima -/

section Compact

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {S : Finset Z} {hS : S.Nonempty}

omit [DecidableEq Z] in
lemma continuous_gmax : Continuous (gmax : (Z → ℝ) → ℝ) := by
  show Continuous fun f : Z → ℝ => (univ : Finset Z).sup' univ_nonempty (fun z => f z)
  exact Continuous.finset_sup'_apply _ (fun z _ => continuous_apply z)

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma continuous_val (S : Finset Z) (hS : S.Nonempty) : Continuous (val S hS) := by
  show Continuous fun f : Z → ℝ => S.sup' hS (fun z => f z)
  exact Continuous.finset_sup'_apply _ (fun z _ => continuous_apply z)

omit [DecidableEq Z] in
lemma continuous_regret (S : Finset Z) (hS : S.Nonempty) : Continuous (regret S hS) := by
  show Continuous fun f : Z → ℝ => gmax f - val S hS f
  exact continuous_gmax.sub (continuous_val S hS)

lemma continuous_adv (S : Finset Z) (hS : S.Nonempty) (z : Z) :
    Continuous fun f : Z → ℝ => adv S hS f z := by
  simp_rw [adv_eq]
  exact (continuous_apply z).sub (continuous_val S hS)

/-- On a nonempty compact set of environments the worst-case advantage `D_C(z, S)` is a
maximum. -/
theorem robustAdv_isGreatest (C : Set (Z → ℝ)) (hC : C.Nonempty) (hCc : IsCompact C) (z : Z) :
    IsGreatest ((fun f => adv S hS f z) '' C) (robustAdv S hS C z) := by
  obtain ⟨f, hf, hmax⟩ := hCc.exists_isMaxOn hC (continuous_adv S hS z).continuousOn
  have hg : IsGreatest ((fun f => adv S hS f z) '' C) (adv S hS f z) :=
    ⟨⟨f, hf, rfl⟩, by rintro _ ⟨g, hg, rfl⟩; exact isMaxOn_iff.mp hmax g hg⟩
  have he : robustAdv S hS C z = adv S hS f z := hg.csSup_eq
  rw [he]
  exact hg

omit [DecidableEq Z] in
/-- On a nonempty compact set of environments the robust regret `R_C(a)` is a maximum. -/
theorem robustRegret_isGreatest (C : Set (Z → ℝ)) (hC : C.Nonempty) (hCc : IsCompact C) :
    IsGreatest (regret S hS '' C) (robustRegret S hS C) := by
  obtain ⟨f, hf, hmax⟩ := hCc.exists_isMaxOn hC (continuous_regret S hS).continuousOn
  have hg : IsGreatest (regret S hS '' C) (regret S hS f) :=
    ⟨⟨f, hf, rfl⟩, by rintro _ ⟨g, hg, rfl⟩; exact isMaxOn_iff.mp hmax g hg⟩
  have he : robustRegret S hS C = regret S hS f := hg.csSup_eq
  rw [he]
  exact hg

/-- **Joint-set reduction (Lemma `lem:bay-reduction`) for a nonempty compact set of
environments, with maxima.**  For a proper support, each `D_C(z, S) = max_{f ∈ C}
min_{y ∈ S} (f z - f y)` is attained, and the largest regret over `C` is attained and
equals `max {0, max_{z ∉ S} D_C(z, S)}`. -/
theorem bay_reduction_compact (C : Set (Z → ℝ)) (hC : C.Nonempty) (hCc : IsCompact C)
    (hSc : Sᶜ.Nonempty) :
    (∀ z, IsGreatest ((fun f => adv S hS f z) '' C) (robustAdv S hS C z)) ∧
      IsGreatest (regret S hS '' C) (max 0 (Sᶜ.sup' hSc (robustAdv S hS C))) := by
  refine ⟨robustAdv_isGreatest C hC hCc, ?_⟩
  have h := robustRegret_isGreatest (S := S) (hS := hS) C hC hCc
  rw [robustRegret_eq C hC ⟨_, h.2⟩ hSc] at h
  exact h

/-- "The value is zero when the exterior is empty": for full support the largest regret
over a nonempty set is `0`. -/
theorem bay_reduction_full (C : Set (Z → ℝ)) (hC : C.Nonempty) (hSc : Sᶜ = ∅) :
    IsGreatest (regret S hS '' C) 0 := by
  obtain ⟨f, hf⟩ := hC
  exact ⟨⟨f, hf, regret_eq_zero_of_compl_empty hSc⟩,
    by rintro _ ⟨g, -, rfl⟩; exact (regret_eq_zero_of_compl_empty hSc).le⟩

/-- **Joint-set reduction (Lemma `lem:bay-reduction`), as stated**: linear environments
`f_θ(z) = φ_zᵀ θ` and a nonempty compact parameter set `C ⊆ ℝ^d`.  There are numbers
`D z = D_C(z, S) = max_{θ ∈ C} min_{y ∈ S} (φ_z - φ_y)ᵀ θ` (maxima) such that
`R_C(a) = max_{θ ∈ C} r_θ(a) = max {0, max_{z ∉ S(a)} D_C(z, S(a))}`. -/
theorem bay_reduction_literal {n : Type*} [Fintype n] (φ : Z → n → ℝ) (C : Set (n → ℝ))
    (hC : C.Nonempty) (hCc : IsCompact C) (hSc : Sᶜ.Nonempty) :
    ∃ D : Z → ℝ,
      (∀ z, IsGreatest ((fun θ => S.inf' hS (fun y => (φ z - φ y) ⬝ᵥ θ)) '' C) (D z)) ∧
      IsGreatest ((fun θ => regret S hS (fun z => φ z ⬝ᵥ θ)) '' C)
        (max 0 (Sᶜ.sup' hSc D)) := by
  have hF : Continuous (fun θ : n → ℝ => (fun z => φ z ⬝ᵥ θ : Z → ℝ)) :=
    continuous_pi fun z => by
      show Continuous fun θ : n → ℝ => ∑ i, φ z i * θ i
      fun_prop
  obtain ⟨h1, h2⟩ := bay_reduction_compact (S := S) (hS := hS)
    ((fun θ : n → ℝ => (fun z => φ z ⬝ᵥ θ : Z → ℝ)) '' C) (hC.image _) (hCc.image hF) hSc
  refine ⟨robustAdv S hS ((fun θ : n → ℝ => (fun z => φ z ⬝ᵥ θ : Z → ℝ)) '' C),
    fun z => ?_, ?_⟩
  · have h := h1 z
    rw [Set.image_image] at h
    have e : (fun θ : n → ℝ => adv S hS (fun z => φ z ⬝ᵥ θ) z) =
        fun θ => S.inf' hS (fun y => (φ z - φ y) ⬝ᵥ θ) := by
      funext θ
      unfold adv
      simp only [sub_dotProduct]
    rw [← e]
    exact h
  · rw [Set.image_image] at h2
    exact h2

/-- Full support in the linear model: the largest regret over a nonempty parameter set is
`0`. -/
theorem bay_reduction_literal_full {n : Type*} [Fintype n] (φ : Z → n → ℝ) (C : Set (n → ℝ))
    (hC : C.Nonempty) (hSc : Sᶜ = ∅) :
    IsGreatest ((fun θ => regret S hS (fun z => φ z ⬝ᵥ θ)) '' C) 0 := by
  obtain ⟨θ, hθ⟩ := hC
  exact ⟨⟨θ, hθ, regret_eq_zero_of_compl_empty hSc⟩,
    by rintro _ ⟨g, -, rfl⟩; exact (regret_eq_zero_of_compl_empty hSc).le⟩

end Compact

/-! ### `thm:t2-hull`: the bound `B · max_{z ∉ S} inf_{p ∈ P_a} ‖φ_z - p‖` -/

section Hull

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Finset Z}

/-- `max_{z ∉ S(a)} inf_{p ∈ P_a} ‖φ_z - p‖` with `P_a = conv {φ_y : y ∈ S(a)}`, and zero
for an empty complement. -/
noncomputable def hullGap (φ : Z → E) (S : Finset Z) : ℝ :=
  if h : Sᶜ.Nonempty then
    Sᶜ.sup' h (fun z => Metric.infDist (φ z) (convexHull ℝ (φ '' (S : Set Z))))
  else 0

omit [Nonempty Z] in
lemma hullGap_of_proper (φ : Z → E) (h : Sᶜ.Nonempty) :
    hullGap φ S =
      Sᶜ.sup' h (fun z => Metric.infDist (φ z) (convexHull ℝ (φ '' (S : Set Z)))) := by
  simp only [hullGap, h, ↓reduceDIte]

omit [Nonempty Z] in
lemma hullGap_of_full (φ : Z → E) (h : ¬ Sᶜ.Nonempty) : hullGap φ S = 0 := by
  simp only [hullGap, h, ↓reduceDIte]

/-- **Feature-hull dominance, approximate part (Theorem `thm:t2-hull`), as stated.**
`‖θ‖_* ≤ B` implies regret at most `B · max_{z ∉ S(a)} inf_{p ∈ P_a} ‖φ_z - p‖` (zero for
an empty complement). -/
theorem regret_le_hullGap (hS : S.Nonempty) (φ : Z → E) {B : ℝ} {θ : StrongDual ℝ E}
    (hθ : ‖θ‖ ≤ B) : regret S hS (dualEnv φ θ) ≤ B * hullGap φ S := by
  by_cases h : Sᶜ.Nonempty
  · have hη : 0 ≤ hullGap φ S := by
      rw [hullGap_of_proper φ h]
      obtain ⟨z, hz⟩ := h
      exact Metric.infDist_nonneg.trans
        (le_sup' (fun z => Metric.infDist (φ z) (convexHull ℝ (φ '' (S : Set Z)))) hz)
    refine regret_le_of_hull_dist hS φ hη (fun z hz => ?_) hθ
    have hfin : (φ '' (S : Set Z)).Finite := (S.finite_toSet).image φ
    have hcomp := hfin.isCompact_convexHull (𝕜 := ℝ)
    have hne : (convexHull ℝ (φ '' (S : Set Z))).Nonempty := by
      obtain ⟨y, hy⟩ := hS
      exact ⟨φ y, subset_convexHull ℝ _ ⟨y, hy, rfl⟩⟩
    obtain ⟨w, hw, hd⟩ := hcomp.exists_infDist_eq_dist hne (φ z)
    refine ⟨w, hw, ?_⟩
    rw [← dist_eq_norm, ← hd, hullGap_of_proper φ h]
    exact le_sup' (fun z => Metric.infDist (φ z) (convexHull ℝ (φ '' (S : Set Z))))
      (mem_compl.mpr hz)
  · rw [hullGap_of_full φ h, mul_zero]
    exact (regret_eq_zero_of_compl_empty (not_nonempty_iff_eq_empty.mp h)).le

end Hull

end LiteralABC

end JointRootCert
