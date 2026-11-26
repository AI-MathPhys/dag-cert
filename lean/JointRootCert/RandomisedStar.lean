/-
The matching clause of the tied-star lower bound.

Manuscript result covered:

* `thm:active-star-lb` "Non-containment tied-star lower bound", last clause: the lower bound
  matches the `Õ(N/(g+ε)²)` scaling of `eq:active-er-bound` when `ε ≤ g/√N`.
  `star_os_upper` instantiates the optimistic-separation bound of `thm:active-er`
  (`active_os_end_to_end`) on the tied star `starMu` (gaps `Δ_p = Δ_q = 0`, `Δ_{r_i} = g`,
  separation `Γ = g`): with failure probability at most `δ` the number of queries is at most
  `(N+2) ⌈(128/(g+ε)²) log(128 M / (δ (g+ε)²))⌉`.  `tied_star_lower_bound_rand_sq` is the
  quadratic form `E τ ≥ (3/16) kl(1/2, δ) N/(g+ε)²` of the lower bound for randomised
  procedures when `N ε² ≤ g²`.  `star_matching` states the two together.

The upper bound is the high-probability bound of `thm:active-er` (on the number of queries of a
run following the optimistic-separation rule on reward tapes), not a bound on an expectation;
the lower bound is on the expected number of queries of any randomised `(ε,δ)`-correct
procedure.
-/
import JointRootCert.Randomised
import JointRootCert.Completions2

namespace JointRootCert

namespace Rand

open MeasureTheory Finset Real Stopped

set_option linter.unusedSectionVars false

section StarUpper

variable {N : ℕ}

/-- The supports of the star family are proper when `N ≥ 1`. -/
lemma starSupp_compl_nonempty (hN : 0 < N) : ∀ a, (starSupp N a)ᶜ.Nonempty
  | none => ⟨some (some ⟨0, hN⟩), by simp [starSupp, pairSupp]⟩
  | some _ => ⟨some none, by simp [starSupp, starB]⟩

/-- The supports of the star family cover the terminals. -/
lemma starSupp_cover (N : ℕ) : ∀ z : Fan N, ∃ a, z ∈ starSupp N a
  | none => ⟨none, by simp [starSupp, pairSupp]⟩
  | some none => ⟨none, by simp [starSupp, pairSupp]⟩
  | some (some i) => ⟨some i, by simp [starSupp, starB]⟩

lemma gmax_starMu {g : ℝ} (hg0 : 0 < g) : gmax (starMu N g) = 1 / 2 :=
  le_antisymm (sup'_le _ _ fun z _ => starMu_le_half hg0 z) (le_gmax (starMu N g) none)

/-- The gaps of the tied star: `Δ_p = Δ_q = 0`, `Δ_{r_i} = g`; in particular `Δ_z ≤ g`. -/
lemma star_gap {g : ℝ} (hg0 : 0 < g) :
    gmax (starMu N g) - starMu N g none = 0 ∧
    gmax (starMu N g) - starMu N g (some none) = 0 ∧
    ∀ i : Fin N, gmax (starMu N g) - starMu N g (some (some i)) = g := by
  rw [gmax_starMu hg0]
  refine ⟨by rw [starMu_p]; ring, by rw [starMu_q]; ring, fun i => by rw [starMu_r]; ring⟩

lemma val_starSupp {g : ℝ} (hg0 : 0 < g) (a : Option (Fin N)) :
    val (starSupp N a) (starSupp_nonempty N a) (starMu N g) = 1 / 2 := by
  have hmem : (none : Fan N) ∈ starSupp N a := by
    cases a <;> simp [starSupp, pairSupp, starB]
  rw [val_eq_of_max (starSupp_nonempty N a) hmem fun y _ => by
    rw [starMu_p]; exact starMu_le_half hg0 y]
  rfl

/-- The separation of the tied star is `Γ = g`, attained by the action `A`. -/
lemma star_margin (hN : 0 < N) {g : ℝ} (hg0 : 0 < g) :
    IsGreatest (Set.range fun a => val (starSupp N a) (starSupp_nonempty N a) (starMu N g)
      - (starSupp N a)ᶜ.sup' (starSupp_compl_nonempty hN a) (starMu N g)) g := by
  have hA : (starSupp N none)ᶜ.sup' (starSupp_compl_nonempty hN none) (starMu N g)
      = 1 / 2 - g := by
    refine le_antisymm (sup'_le _ _ fun z hz => ?_) ?_
    · rcases z with _ | _ | i
      · exact absurd (by simp [starSupp, pairSupp]) (mem_compl.1 hz)
      · exact absurd (by simp [starSupp, pairSupp]) (mem_compl.1 hz)
      · rw [starMu_r]
    · have hmem : (some (some ⟨0, hN⟩) : Fan N) ∈ (starSupp N none)ᶜ := by
        simp [starSupp, pairSupp]
      have := le_sup' (starMu N g) hmem
      rwa [starMu_r] at this
  have hB : ∀ i : Fin N,
      (starSupp N (some i))ᶜ.sup' (starSupp_compl_nonempty hN (some i)) (starMu N g) = 1 / 2 := by
    intro i
    refine le_antisymm (sup'_le _ _ fun z _ => starMu_le_half hg0 z) ?_
    have hmem : (some none : Fan N) ∈ (starSupp N (some i))ᶜ := by
      simp [starSupp, starB]
    have := le_sup' (starMu N g) hmem
    rwa [starMu_q] at this
  constructor
  · refine ⟨none, ?_⟩
    show val (starSupp N none) (starSupp_nonempty N none) (starMu N g)
      - (starSupp N none)ᶜ.sup' (starSupp_compl_nonempty hN none) (starMu N g) = g
    rw [val_starSupp hg0, hA]
    ring
  · rintro _ ⟨a, rfl⟩
    show val (starSupp N a) (starSupp_nonempty N a) (starMu N g)
      - (starSupp N a)ᶜ.sup' (starSupp_compl_nonempty hN a) (starMu N g) ≤ g
    rw [val_starSupp hg0]
    cases a with
    | none => rw [hA]; linarith
    | some i => rw [hB i]; linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Optimistic-separation sampling on the tied star** (`thm:active-er`, OS bound,
instantiated on the family of `thm:active-star-lb`).  Reward-tape model of
`active_os_end_to_end` with means `starMu N g`, `N ≥ 1`, `g > 0`, `M ≥ max {2, N + 2}`,
`0 < δ < 1`, `0 ≤ ε ≤ 1`.  Since `Δ_p = Δ_q = 0`, `Δ_{r_i} = g` and `Γ = g`, every terminal has
`ρ_z = max {Γ + ε, Δ_z} / 2 = (g + ε) / 2`, and with failure probability at most `δ` the
returned action is `ε`-optimal and the number of queries is at most
`(N + 2) ⌈(128 / (g + ε)²) log (128 M / (δ (g + ε)²))⌉`. -/
theorem star_os_upper (hN : 0 < N) {g : ℝ} (hg0 : 0 < g) (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Fan N → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = starMu N g z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (N : ℝ) + 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (sel : Ω → ℕ → Fan N) (τ : Ω → ℕ) (rec : Ω → Option (Fin N))
    (hrule : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) (starMu N g) →
        ∀ t < τ ω, OSStep (starSupp N) (starSupp_nonempty N) (starSupp_compl_nonempty hN)
          (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε (sel ω t))
    (hstop : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) (starMu N g) →
        rectCert (starSupp N (rec ω)) (starSupp_nonempty N (rec ω))
          (starSupp_compl_nonempty hN (rec ω))
          (tapeLo M δ (fun z i => X z i ω) (sel ω) (τ ω))
          (tapeHi M δ (fun z i => X z i ω) (sel ω) (τ ω)) ≤ ε) :
    P {ω | ¬ (regret (starSupp N (rec ω)) (starSupp_nonempty N (rec ω)) (starMu N g) ≤ ε ∧
        τ ω ≤ (N + 2) * ⌈128 / (g + ε) ^ 2 *
          Real.log (128 * M / (δ * (g + ε) ^ 2))⌉₊)} ≤ ENNReal.ofReal δ := by
  have hcard' : (Fintype.card (Fan N) : ℝ) ≤ M := by
    have : Fintype.card (Fan N) = N + 2 := by simp [Fintype.card_option]
    rw [this]
    push_cast
    exact hcard
  have h := active_os_end_to_end P hindep hmeas hbdd hmean hM hcard' hδ0 hδ1 (starSupp N)
    (starSupp_nonempty N) (starSupp_compl_nonempty hN) (starSupp_cover N) hε0 hε1
    (star_margin hN hg0) (by linarith) sel τ rec hrule hstop
  have hρ : ∀ z : Fan N, max (g + ε) (gmax (starMu N g) - starMu N g z) = g + ε := by
    intro z
    obtain ⟨h1, h2, h3⟩ := star_gap (N := N) hg0
    refine max_eq_left ?_
    rcases z with _ | _ | i
    · rw [h1]; linarith
    · rw [h2]; linarith
    · rw [h3 i]; linarith
  have hge : 0 < g + ε := by linarith
  have e1 : 32 / ((g + ε) / 2) ^ 2 = 128 / (g + ε) ^ 2 := by
    field_simp
    ring
  have e2 : 32 * M / (δ * ((g + ε) / 2) ^ 2) = 128 * M / (δ * (g + ε) ^ 2) := by
    field_simp
    ring
  have hsum : ∑ _z : Fan N, ⌈128 / (g + ε) ^ 2 * Real.log (128 * M / (δ * (g + ε) ^ 2))⌉₊
      = (N + 2) * ⌈128 / (g + ε) ^ 2 * Real.log (128 * M / (δ * (g + ε) ^ 2))⌉₊ := by
    rw [sum_const, card_univ, smul_eq_mul]
    congr 1
    simp [Fintype.card_option]
  simp only [hρ, e1, e2, hsum] at h
  exact h

end StarUpper

/-! ### The two-sided comparison -/

section Matching

variable {Sd : Type*} [MeasurableSpace Sd]

/-- **Quadratic form of the tied-star lower bound for randomised procedures**, in the regime
`ε ≤ g/√N` (stated as `N ε² ≤ g²`) where the `N/(g+ε)²` term is the smaller one:
`E_μ[τ] ≥ (3/16) kl(1/2, δ) N/(g+ε)²`.  Hypotheses as in `tied_star_lower_bound_rand`. -/
theorem tied_star_lower_bound_rand_sq {N : ℕ} {g ε δ : ℝ} (hε : 0 < ε) (hεg : ε ≤ g)
    (hg : g ≤ 1 / 4) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) (hNε : (N : ℝ) * ε ^ 2 ≤ g ^ 2)
    (ν : Measure Sd) [IsProbabilityMeasure ν]
    (R : RSampler (Fan N) Sd) (dec : Sd → List Bool → Option (Fin N))
    (hdec : ∀ l a, MeasurableSet {s | dec s l = a})
    (hcorr : ∀ lam : Fan N → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
      1 - δ ≤ rprobInf ν R lam
        (fun s => {l | regret (starSupp N (dec s l)) (starSupp_nonempty N (dec s l)) lam ≤ ε}))
    {B : ℝ} (hB : ∀ n, rexpTime ν R (starMu N g) n ≤ B) :
    3 / 16 * bkl (1 / 2) δ * (N / (g + ε) ^ 2) ≤ rexpTimeInf ν R (starMu N g) := by
  have hg0 : 0 < g := hε.trans_le hεg
  have h1 := tied_star_lower_bound_rand hε hεg hg hδ0 hδ ν R dec hdec hcorr hB
  have h2 := star_bound_quadratic (N := N) hε hεg hg
  rw [min_eq_left (star_first_term_smaller hε hg0 hNε)] at h2
  have hb0 : 0 ≤ bkl (1 / 2) δ := bkl_nonneg (by norm_num) (by norm_num) hδ0 (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hb0
  linarith

universe u v

/-- **`thm:active-star-lb`, matching clause.**  On the tied star with `N ≥ 1`,
`0 < ε ≤ g ≤ 1/4`, `0 < δ ≤ 1/4` and `ε ≤ g/√N` (`N ε² ≤ g²`):

* every randomised `(ε,δ)`-correct procedure with finite expected stopping time has
  `E_μ[τ] ≥ (3/16) kl(1/2, δ) · N/(g+ε)²`;
* every run of optimistic-separation sampling on reward tapes with means `starMu N g`
  (confidence schedule with `M ≥ N + 2`) returns, with failure probability at most `δ`, an
  `ε`-optimal action after at most `(N+2) ⌈(128/(g+ε)²) log(128 M / (δ (g+ε)²))⌉` queries.

The two bounds differ by the factor `(N+2)/N` and a logarithm: this is the
`Õ(N/(g+ε)²)` matching of `eq:active-er-bound`. -/
theorem star_matching {N : ℕ} (hN : 0 < N) {g ε δ : ℝ} (hε : 0 < ε) (hεg : ε ≤ g)
    (hg : g ≤ 1 / 4) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) (hNε : (N : ℝ) * ε ^ 2 ≤ g ^ 2) :
    (∀ (Sd' : Type u) [MeasurableSpace Sd'] (ν : Measure Sd') [IsProbabilityMeasure ν]
        (R : RSampler (Fan N) Sd') (dec : Sd' → List Bool → Option (Fin N)),
        (∀ l a, MeasurableSet {s | dec s l = a}) →
        (∀ lam : Fan N → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
          1 - δ ≤ rprobInf ν R lam (fun s =>
            {l | regret (starSupp N (dec s l)) (starSupp_nonempty N (dec s l)) lam ≤ ε})) →
        (∃ B : ℝ, ∀ n, rexpTime ν R (starMu N g) n ≤ B) →
        3 / 16 * bkl (1 / 2) δ * (N / (g + ε) ^ 2) ≤ rexpTimeInf ν R (starMu N g)) ∧
    (∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fan N → ℕ → Ω → ℝ) (M : ℝ) (sel : Ω → ℕ → Fan N) (τ : Ω → ℕ)
        (rec : Ω → Option (Fin N)),
        (∀ z, ProbabilityTheory.iIndepFun (X z) P) → (∀ z i, AEMeasurable (X z i) P) →
        (∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) →
        (∀ z i, ∫ ω, X z i ω ∂P = starMu N g z) → (N : ℝ) + 2 ≤ M →
        (∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) (starMu N g) →
          ∀ t < τ ω, OSStep (starSupp N) (starSupp_nonempty N) (starSupp_compl_nonempty hN)
            (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
            (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε (sel ω t)) →
        (∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) (starMu N g) →
          rectCert (starSupp N (rec ω)) (starSupp_nonempty N (rec ω))
            (starSupp_compl_nonempty hN (rec ω))
            (tapeLo M δ (fun z i => X z i ω) (sel ω) (τ ω))
            (tapeHi M δ (fun z i => X z i ω) (sel ω) (τ ω)) ≤ ε) →
        P {ω | ¬ (regret (starSupp N (rec ω)) (starSupp_nonempty N (rec ω)) (starMu N g) ≤ ε ∧
          τ ω ≤ (N + 2) * ⌈128 / (g + ε) ^ 2 *
            Real.log (128 * M / (δ * (g + ε) ^ 2))⌉₊)} ≤ ENNReal.ofReal δ) := by
  have hg0 : 0 < g := hε.trans_le hεg
  refine ⟨?_, ?_⟩
  · intro Sd' _ ν _ R dec hdec hcorr hB
    obtain ⟨B, hB⟩ := hB
    exact tied_star_lower_bound_rand_sq hε hεg hg hδ0 hδ hNε ν R dec hdec hcorr hB
  · intro Ω _ P _ X M sel τ rec hindep hmeas hbdd hmean hcard hrule hstop
    have hM : 2 ≤ M := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    exact star_os_upper hN hg0 P hindep hmeas hbdd hmean hM hcard hδ0 (by linarith) hε.le
      (by linarith) sel τ rec hrule hstop

end Matching

end Rand

end JointRootCert
