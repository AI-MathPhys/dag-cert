/-
# Safety fallback with the manuscript's enclosures, and the randomised information limit

Manuscript results covered:

* `prop:v10g-safety-fallback` (Conditional safety and a finite-mean reference design), all
  three clauses, with the manuscript's outward enclosures: `Z̲_n ∈ [max{0, Z_n - 1}, Z_n]`,
  `B̄_n ∈ [B(n, δ/2), B(n, δ/2) + 1]` and safeguard distances to absolute lower error at most
  one, `J̲_n(a) ∈ [J_n(a) - 1, J_n(a)]` (`safety_fallback_full`).  The space and the model are
  those of `LiteralD1.safety_fallback_literal` (which treats exact enclosures only).
* `thm:bay-main-optimal` (Correlated Gaussian information limit), the lower bound
  `eq:bay-main-optimal` for randomised procedures with the paper's `I_*(θ)` (`IstarE`) and
  query means `√(v_x) ⟨u_x, λ⟩` (`bay_main_optimal_rand`), and the combination with the
  upper bound of `LiteralD1b.bay_main_optimal_literal` (`bay_main_optimal_full`).
-/
import JointRootCert.LiteralD1a
import JointRootCert.LiteralD1b
import JointRootCert.RandomisedGauss

namespace JointRootCert

namespace LiteralF2

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

/-! ### `prop:v10g-safety-fallback` with general enclosures -/

section Safety

open LiteralD1

variable {X : Type} [Fintype X]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {𝒜 : Type} [Fintype 𝒜] [Nonempty 𝒜]
variable {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **Conditional safety and a finite-mean reference design**
(`prop:v10g-safety-fallback`), on the tape space of `LiteralD1`, with the manuscript's
enclosures.  The upper boundary enclosure `Bbar n ∈ [B(n, δ/2), B(n, δ/2) + 1]` is used by
both branches; the safeguard's lower distance enclosures satisfy
`J_n(a) - 1 ≤ Jlow n Y a ≤ J_n(a)`, where `J_n(a) = I_a(θ̂_n, ⌈n w⁰⌉)` is computed from the
safeguard tape `Y`; each frozen record carries its own lower enclosure
`Zlow Y n ∈ [max{0, Z_n - 1}, Z_n]` of the confirmation statistic `Z_n` (`confirmZ`).

(1) For every frozen record (action `a`, design `(1 - k) p + k w⁰`, center `v`, number
`l ≤ I_a(v, w)`) and every such `Zlow`, i.e. conditionally on every finite pilot history, the
confirmation branch on its fresh tape stops (`Bbar n ≤ Zlow Y n`) with an action of regret
above `ε` with probability at most `δ/2`, at every parameter.
(2) The reference safeguard certifies (`Bbar n ≤ Jlow n Y a`) an action of regret above `ε`
with probability at most `δ/2`, at every parameter.
(3) At every `θ` with `I_*(θ) > 0`, `E_θ F_δ ≤ H_δ` with `C₀ = max_a I_a(θ, w⁰)`, where
`F_δ` is the safeguard's observation count at its first stop under `Jlow, Bbar`.

Extra hypothesis beyond the manuscript: the enclosures `Jlow n · a` are measurable functions
of the safeguard tape (needed for the expectation to be the integral of a measurable count;
outward-rounded arithmetic of measurable quantities is measurable). -/
theorem safety_fallback_full (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {ℓ k0 k δ : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Bbar : ℕ → ℝ}
    (hBlo : ∀ n : ℕ, boundary (Module.finrank ℝ E) n (δ / 2) ≤ Bbar n)
    (hBhi : ∀ n : ℕ, Bbar n ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 1)
    {Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ}
    (hJlo : ∀ (n : ℕ) Y a, gInfo u (strictAlt φ (supp a) (hne a) ε)
      (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ)) - 1 ≤ Jlow n Y a)
    (hJhi : ∀ (n : ℕ) Y a, Jlow n Y a ≤ gInfo u (strictAlt φ (supp a) (hne a) ε)
      (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ)))
    (hJm : ∀ n a, Measurable (fun Y : X → ℕ → ℝ => Jlow n Y a)) :
    (∀ (θ : E) (a : 𝒜) (p : X → ℝ), p ∈ simplex X → ∀ (v : E) (l : ℝ),
        l ≤ gInfo u (strictAlt φ (supp a) (hne a) ε) v (floorDesign k w0 p) →
        ∀ Zlow : (X → ℕ → ℝ) → ℕ → ℝ,
        (∀ Y n, max 0 (confirmZ u (floorDesign k w0 p) v l Y n - 1) ≤ Zlow Y n) →
        (∀ Y n, Zlow Y n ≤ confirmZ u (floorDesign k w0 p) v l Y n) →
        tapeP X {ω | ∃ n : ℕ, 1 ≤ n ∧ Bbar n ≤ Zlow (obsTape u θ (tapeξ 1) ω) n ∧
          ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal (δ / 2)) ∧
    (∀ θ : E, tapeP X {ω | ∃ n : ℕ, 1 ≤ n ∧ ∃ a, Bbar n ≤ Jlow n (obsTape u θ (tapeξ 2) ω) a ∧
        ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal (δ / 2)) ∧
    ∀ θ : E, 0 < IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
      ∫⁻ ω, roundTotal w0 (firstTime (sgStop Jlow Bbar (obsTape u θ (tapeξ 2) ω)))
          ∂(tapeP X) ≤
        ENNReal.ofReal (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ
          (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)) := by
  refine ⟨fun θ a p hp v l hl Zlow hZlo hZhi => ?_, fun θ => ?_, fun θ hI => ?_⟩
  · refine (measure_mono ?_).trans (confirm_safe_fixed φ supp hne ε u hw0 hk0 hM0 hk hk1
      (tapeξ_iIndepFun 1) (tapeξ_hasLaw 1) θ hδ0 hδ1 hBlo a hp v hl)
    rintro ω ⟨n, hn, hc, hbad⟩
    exact ⟨n, hn, hc.trans (hZhi _ n), hbad⟩
  · exact safeguard_safe φ supp hne ε u hw0 hk0 hM0 (tapeξ_iIndepFun 2) (tapeξ_hasLaw 2) θ
      hδ0 hδ1 hJhi hBlo
  · obtain ⟨a0, h0eq, -⟩ := exists_C0G_max u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0
    have hC0 : 0 < C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0 :=
      lt_of_lt_of_le (by positivity) (C0G_ge u _ hQ θ hw0 hℓ hu hk0.le hM0)
    exact safeguard_mean u _ hQ hw0 hk0 hM0 (tapeξ_iIndepFun 2) (tapeξ_hasLaw 2)
      (measurable_tapeξ 2) θ hδ0 hδ1 a0 hC0 h0eq.ge hJm hJlo hBhi

end Safety

/-! ### `thm:bay-main-optimal` for randomised procedures -/

section Rand

open GaussStopped RandG LiteralD1b

variable {X ι 𝒜 Z : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype 𝒜] [Nonempty 𝒜]
  [MeasurableSpace 𝒜] [MeasurableSingletonClass 𝒜] [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- Each `I_a(θ, w)`, `w ∈ Δ(X)`, is at most `I_*(θ)` (`IstarE` is a supremum of a set that is
bounded above, since each alternative set is nonempty and `w_x ≤ 1`). -/
lemma gInfo_le_IstarE (u : X → ι → ℝ) (Q : 𝒜 → Set (EuclideanSpace ℝ ι))
    (hQ : ∀ a, (Q a).Nonempty) (θ : ι → ℝ) (a : 𝒜) {w : X → ℝ} (hw : w ∈ simplex X) :
    gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) (WithLp.toLp 2 θ) w ≤
      IstarE u Q θ := by
  classical
  set uE : X → EuclideanSpace ℝ ι := fun x => WithLp.toLp 2 (u x)
  set θE : EuclideanSpace ℝ ι := WithLp.toLp 2 θ
  choose lamA hlamA using hQ
  -- the bound for one action and one design
  have hone : ∀ (b : 𝒜) (w' : X → ℝ), w' ∈ simplex X →
      gInfo uE (Q b) θE w' ≤ ∑ x, ⟪uE x, lamA b - θE⟫ ^ 2 / 2 := by
    intro b w' hw'
    have h1 := pow_le_pow_left₀ rootInfo_nonneg
      (rootInfo_le (A := designMap uE w') (θ := θE) (hlamA b)) 2
    rw [norm_designMap_sq uE hw'.1] at h1
    have h2 : ∑ x, w' x * ⟪uE x, lamA b - θE⟫ ^ 2 ≤ ∑ x, ⟪uE x, lamA b - θE⟫ ^ 2 := by
      refine sum_le_sum fun x _ => ?_
      have hx1 : w' x ≤ 1 := by
        rw [← hw'.2]
        exact Finset.single_le_sum (f := w') (fun y _ => hw'.1 y) (mem_univ x)
      have := sq_nonneg ⟪uE x, lamA b - θE⟫
      nlinarith [hw'.1 x]
    unfold gInfo
    rw [← Finset.sum_div]
    linarith
  have hbdd : BddAbove {r : ℝ | ∃ a, ∃ w ∈ simplex X, r = gInfo uE (Q a) θE w} := by
    refine ⟨∑ b, ∑ x, ⟪uE x, lamA b - θE⟫ ^ 2 / 2, ?_⟩
    rintro _ ⟨b, w', hw', rfl⟩
    refine (hone b w' hw').trans ?_
    exact Finset.single_le_sum (f := fun b => ∑ x, ⟪uE x, lamA b - θE⟫ ^ 2 / 2)
      (fun b _ => sum_nonneg fun x _ => by positivity) (mem_univ b)
  exact le_csSup hbdd ⟨a, w, hw, rfl⟩

/-- **Correlated Gaussian information limit, lower bound for randomised procedures
(`thm:bay-main-optimal`, `eq:bay-main-optimal`), with the paper's `I_*(θ)`.**

Model as in `LiteralD1b.bay_main_optimal_literal`: queries `x` with whitened features
`u_x ∈ ℝ^d` and known variances `v_x > 0`, the observation of `x` under `λ` being
`N(√(v_x) ⟨u_x, λ⟩, v_x)`; `Q_a = strictAlt φ (supp a) ε`, all nonempty;
`I_*(θ) = sup_a sup_{w ∈ Δ(X)} I_a(θ, w)` (`IstarE`).  The procedures are randomised: for each
`δ` a seed law `ν δ` and seed-indexed samplers and decisions (`RandG.RGSampler`,
`RandG.RGDecision`, jointly measurable in seed and history).  Uniform correctness: under every
`λ ∈ Q_a`, the probability (over seed and observations) of having halted by any horizon `n`
with answer `a` is at most `δ`.  Conclusion, for every `θ` with `I_*(θ) > 0`:
`liminf_{δ ↓ 0} E_θ τ_δ / log(1/δ) ≥ 1 / I_*(θ)`, in the form: for every `c < 1 / I_*(θ)`,
eventually `c log(1/δ) ≤ E_θ τ_δ`. -/
theorem bay_main_optimal_rand (u : X → ι → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    (φ : Z → EuclideanSpace ℝ ι) (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQne : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty)
    (θ : ι → ℝ) (hI : 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
    {Sd : Type*} [MeasurableSpace Sd] (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RGSampler X Sd) (D : ℝ → RGDecision 𝒜 Sd)
    (hcorrect : ∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
      rprobAns (ν δ) (R δ) (D δ) a (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n ≤ δ)
    {c : ℝ} (hc : c < 1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤
      rexpTau (ν δ) (R δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v := by
  set uE : X → EuclideanSpace ℝ ι := fun x => WithLp.toLp 2 (u x) with huE
  have hin : ∀ (x : X) (z : EuclideanSpace ℝ ι), ⟪uE x, z⟫ = u x ⬝ᵥ z.ofLp := by
    intro x z
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [uE, dotProduct_comm]
  have hμ : (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) =
      fun x => Real.sqrt (v x) * ⟪uE x, (WithLp.toLp 2 θ : EuclideanSpace ℝ ι)⟫ := by
    funext x
    rw [hin]
  rw [hμ]
  refine rgauss_info_lower_bound (fun (x : X) (lam : EuclideanSpace ℝ ι) =>
      Real.sqrt (v x) * ⟪uE x, lam⟫) (fun a => strictAlt φ (supp a) (hne a) ε) hv hI
    (fun a w hw ζ hζ => ?_) ν R D ?_ hc
  · have hglb := JointRootCert.GaussTrack.gcost_isGLB uE hv hw.1
      (WithLp.toLp 2 θ : EuclideanSpace ℝ ι) (hQne a)
    have hlt : rootInfo (designMap uE w) (strictAlt φ (supp a) (hne a) ε)
        (WithLp.toLp 2 θ) ^ 2 / 2 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ + ζ := by
      have := gInfo_le_IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) hQne θ a hw
      rw [gInfo] at this
      linarith
    obtain ⟨_, ⟨lam, hlam, rfl⟩, hlam2⟩ := (isGLB_lt_iff hglb).mp hlt
    exact ⟨lam, hlam, hlam2⟩
  · intro δ hδ0 hδ1 a lam hlam n
    have := hcorrect δ hδ0 hδ1 a lam hlam n
    have hfun : (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) =
        fun x => Real.sqrt (v x) * ⟪uE x, lam⟫ := by
      funext x
      rw [hin]
    rw [hfun] at this
    exact this

/-- **Correlated Gaussian information limit (`thm:bay-main-optimal`), lower bound for
randomised procedures together with the attaining tracker.**  Model and hypotheses as in
`LiteralD1b.bay_main_optimal_literal` (spanning design `w⁰` with `M(w⁰) ⪰ κ I`, nonempty
strict alternative sets).

(1) For every `θ` with `I_*(θ) > 0`, every uniformly correct family of randomised procedures
(seed laws `ν δ`, seed-indexed samplers `R δ` and decisions `D δ`) has
`liminf_{δ ↓ 0} E_θ τ_δ / log(1/δ) ≥ 1 / I_*(θ)` (`bay_main_optimal_rand`).

(2) There are constants `ℓ`, `A0` such that the tracker
`T = finGridTracker u v Q w⁰ 1 ℓ κ A0`, fixed before the parameter, is Borel measurable,
meets the oracle contract, is uniformly correct (also jointly over answers), and at every
`θ` with `I_*(θ) > 0` has `E_θ τ_δ < ∞` and `E_θ τ_δ / log(1/δ) → 1 / I_*(θ)`
(`LiteralD1b.bay_main_optimal_literal`, part 2).  `T` is a deterministic procedure, hence
also a randomised one, so (1) and (2) together show that `1 / I_*(θ)` is the optimal
constant over randomised procedures. -/
theorem bay_main_optimal_full (u : X → ι → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {κ : ℝ} (hκ : 0 < κ)
    (hspan : ∀ e : ι → ℝ, κ * (e ⬝ᵥ e) ≤ ∑ x, w0 x * (u x ⬝ᵥ e) ^ 2)
    (φ : Z → EuclideanSpace ℝ ι) (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQne : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) :
    (∀ θ : ι → ℝ, 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
      ∀ (Sd : Type) [MeasurableSpace Sd] (ν : ℝ → Measure Sd)
        [∀ δ, IsProbabilityMeasure (ν δ)] (R : ℝ → RGSampler X Sd) (D : ℝ → RGDecision 𝒜 Sd),
        (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
          rprobAns (ν δ) (R δ) (D δ) a (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
            ≤ δ) →
        ∀ c : ℝ, c < 1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤
            rexpTau (ν δ) (R δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v) ∧
    ∃ (ℓ A0 : ℝ)
      (hT : (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).Meas),
      (finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).Valid ℓ κ A0 ∧
      (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
        law ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).sampler
            hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
          (ansSet ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
              A0).sampler hT δ)
            ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
              A0).decision hT δ) a n) ≤ ENNReal.ofReal δ) ∧
      (∀ δ, 0 < δ → δ < 1 → ∀ (lam : EuclideanSpace ℝ ι) (n : ℕ),
        law ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ A0).sampler
            hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
          (⋃ a ∈ {a : 𝒜 | lam ∈ strictAlt φ (supp a) (hne a) ε},
            ansSet ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
                A0).sampler hT δ)
              ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
                A0).decision hT δ) a n) ≤ ENNReal.ofReal δ) ∧
      ∀ θ : ι → ℝ, 0 < IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
        (∀ δ, 0 < δ → δ < 1 →
          expTau ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
            A0).sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v ≠ ⊤) ∧
        Tendsto (fun δ : ℝ =>
            (expTau ((finGridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 ℓ κ
              A0).sampler hT δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v).toReal /
              Real.log (1 / δ))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 / IstarE u (fun a => strictAlt φ (supp a) (hne a) ε) θ)) := by
  refine ⟨fun θ hI Sd _ ν _ R D hcorrect c hc =>
    bay_main_optimal_rand u hv φ supp hne ε hQne θ hI ν R D hcorrect hc, ?_⟩
  exact (bay_main_optimal_literal u hv hw0 hκ hspan φ supp hne ε hQne).2

end Rand

end

end LiteralF2

end JointRootCert
