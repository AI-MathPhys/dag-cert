/-
Completions, part 3: Corollary `cor:v35poly` (Polynomial accuracy dependence at fixed
depth).

* `log_horizon`: the horizon condition `eq:v35horizoncondition` holds for every integer
  `t ≥ D ^ (2^H) · ε ^ (-2^(H+1)) · (log (1/ε)) ^ (2^H)` with the explicit constant
  `D = polyD c_* M δ H`, for `0 < ε ≤ e⁻¹`.
* `puct_poly_horizon_full`: Theorem `thm:v35horizon` at that explicit horizon.
* `oracle_substitution_guarantee`, `circuit_substitution_guarantee`,
  `oracle_substitution_certified`: the oracle-substitution clause.  In the controller/oracle
  model of `Representation.lean`, replacing the oracle implementation by another exact one
  leaves the probability of every event of the trajectory (queries, replies, stopping time)
  unchanged, so a certification guarantee transfers.
-/
import JointRootCert.RecursivePUCT
import JointRootCert.Representation

namespace JointRootCert

open Finset MeasureTheory
open scoped ENNReal

section LogHorizon

/-- `log x ≤ a x` as soon as `x ≥ (2 / a) log (2 / a)`. -/
lemma log_le_mul_of_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (h : 2 / a * Real.log (2 / a) ≤ x) : Real.log x ≤ a * x := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < a * x / 2 by positivity)
  have h2 : Real.log (a * x / 2) = Real.log x - Real.log (2 / a) := by
    rw [show a * x / 2 = x / (2 / a) by field_simp, Real.log_div hx.ne' (by positivity)]
  have h3 : Real.log (2 / a) ≤ a * x / 2 := by
    have h4 := mul_le_mul_of_nonneg_left h (show 0 ≤ a / 2 by positivity)
    have e : a / 2 * (2 / a * Real.log (2 / a)) = Real.log (2 / a) := by field_simp
    rw [e] at h4
    linarith
  linarith

/-- The constant of the explicit horizon:
`D = 16 log (16 M / δ) / c + (64 · 2^H / c) (|log (64 · 2^H / c)| + 2)`. -/
noncomputable def polyD (cst M δ : ℝ) (H : ℕ) : ℝ :=
  16 * Real.log (16 * M / δ) / cst +
    64 * 2 ^ H / cst * (|Real.log (64 * 2 ^ H / cst)| + 2)

/-- **Polynomial accuracy dependence with an explicit logarithmic factor (Corollary
`cor:v35poly`).**  For `c > 0`, `M ≥ 1`, `0 < δ ≤ 1` and `0 < ε ≤ e⁻¹`, every integer

`t ≥ D ^ (2^H) · (1/ε) ^ (2^(H+1)) · (log (1/ε)) ^ (2^H)`,  `D = polyD c M δ H`,

satisfies the horizon condition `(8 / ε²) log (4 M (t+1)² / δ) ≤ c t ^ (2^(-H))` of
`eq:v35horizoncondition`.  The exponent of `1/ε` is exactly `2^(H+1)` and the logarithmic
factor has exponent `2^H`; `D` depends only on `c`, `M`, `δ`, `H`. -/
theorem log_horizon {cst M δ ε : ℝ} (H : ℕ) (hc : 0 < cst) (hM : 1 ≤ M) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ Real.exp (-1)) {t : ℕ}
    (ht : polyD cst M δ H ^ 2 ^ H * (1 / ε) ^ 2 ^ (H + 1) * Real.log (1 / ε) ^ 2 ^ H ≤
      (t : ℝ)) :
    8 / ε ^ 2 * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤
      cst * (t : ℝ) ^ (1 / 2 ^ H : ℝ) := by
  have hL1 : 1 ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv]
    have := (Real.log_le_iff_le_exp hε0).mpr hε1
    linarith
  have hA0 : 0 ≤ Real.log (16 * M / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; nlinarith)
  have hD : polyD cst M δ H = 16 * Real.log (16 * M / δ) / cst +
      64 * 2 ^ H / cst * (|Real.log (64 * 2 ^ H / cst)| + 2) := rfl
  generalize polyD cst M δ H = D at ht hD
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.log (16 * M / δ) := ⟨_, rfl⟩
  rw [← hA] at hA0 hD
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (1 / ε) := ⟨_, rfl⟩
  rw [← hLdef] at ht hL1
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 2 ^ H := ⟨_, rfl⟩
  have hNpos : 0 < N := by rw [hN]; positivity
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 64 * 2 ^ H / cst := ⟨_, rfl⟩
  have hGN : G = 64 * N / cst := by rw [hG, hN]
  have hGpos : 0 < G := by rw [hG]; positivity
  rw [← hG] at hD
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (1 / ε) ^ 2 := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; positivity
  have hDpos : 0 < D := by
    rw [hD]
    have h1 : 0 ≤ 16 * A / cst := by positivity
    have h2 : 0 < G * (|Real.log G| + 2) := by positivity
    linarith
  have hbase : 0 < D * E * L := by
    have : 0 < L := by linarith
    positivity
  have ht' : (D * E * L) ^ 2 ^ H ≤ (t : ℝ) := by
    have e : (D * E * L) ^ 2 ^ H = D ^ 2 ^ H * (1 / ε) ^ 2 ^ (H + 1) * L ^ 2 ^ H := by
      rw [mul_pow, mul_pow, hE, ← pow_mul, pow_succ']
    rw [e]
    exact ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (pow_pos hbase _) ht'
  have ht1 : (1 : ℝ) ≤ t := by
    have h0 : 0 < t := by exact_mod_cast htpos
    exact_mod_cast h0
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (t : ℝ) ^ (1 / 2 ^ H : ℝ) := ⟨_, rfl⟩
  have hxpos : 0 < x := by rw [hx]; exact Real.rpow_pos_of_pos htpos _
  have hxN : x ^ 2 ^ H = (t : ℝ) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    have e : (1 / 2 ^ H : ℝ) * ((2 ^ H : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [e, Real.rpow_one]
  have hDx : D * E * L ≤ x := by
    rw [← hxN] at ht'
    exact (pow_le_pow_iff_left₀ hbase.le hxpos.le (pow_pos (by norm_num) H).ne').mp ht'
  have hlogt : Real.log t = N * Real.log x := by
    rw [hx, Real.log_rpow htpos, hN]
    field_simp
  rw [← hx]
  have hlog1 : Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ A + 2 * Real.log t := by
    have hMpos : 0 < M := by linarith
    have h4 : ((t : ℝ) + 1) ^ 2 ≤ 4 * (t : ℝ) ^ 2 := by nlinarith
    have hle : 4 * M * ((t : ℝ) + 1) ^ 2 / δ ≤ 16 * M / δ * (t : ℝ) ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hδ0.le
      nlinarith [mul_le_mul_of_nonneg_left h4 hMpos.le]
    calc Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ Real.log (16 * M / δ * (t : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = A + 2 * Real.log t := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hA]
          push_cast
          ring
  have hεsq : 0 < ε ^ 2 := by positivity
  have ha : 0 < cst * ε ^ 2 / (32 * N) := by positivity
  have h2a : 2 / (cst * ε ^ 2 / (32 * N)) = G * E := by
    rw [hGN, hE]
    field_simp
    norm_num
  have hlogGE : Real.log (G * E) = Real.log G + 2 * L := by
    rw [Real.log_mul hGpos.ne' hEpos.ne', hE, Real.log_pow, hLdef]
    push_cast
    ring
  have hle1 : Real.log (G * E) ≤ (|Real.log G| + 2) * L := by
    rw [hlogGE]
    have h5 := le_abs_self (Real.log G)
    have h6 := abs_nonneg (Real.log G)
    nlinarith
  have hsplit : D * E * L = 16 * A / cst * E * L + G * (|Real.log G| + 2) * E * L := by
    rw [hD]
    ring
  have hL0 : 0 < L := by linarith
  have hfirst : 0 ≤ 16 * A / cst * E * L := by positivity
  have hsecond : 0 ≤ G * (|Real.log G| + 2) * E * L := by positivity
  have h2 : 2 / (cst * ε ^ 2 / (32 * N)) * Real.log (2 / (cst * ε ^ 2 / (32 * N))) ≤ x := by
    rw [h2a]
    calc G * E * Real.log (G * E) ≤ G * E * ((|Real.log G| + 2) * L) :=
          mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = G * (|Real.log G| + 2) * E * L := by ring
      _ ≤ D * E * L := by rw [hsplit]; linarith
      _ ≤ x := hDx
  have hlogx := log_le_mul_of_le ha hxpos h2
  have hKA : 8 / ε ^ 2 * A ≤ cst * x / 2 := by
    have h8 : 8 / ε ^ 2 * A = cst / 2 * (16 * A / cst * E) := by
      rw [hE]
      field_simp
      ring
    have h9 : 16 * A / cst * E ≤ x := by
      have h3 : 16 * A / cst * E ≤ 16 * A / cst * E * L :=
        le_mul_of_one_le_right (by positivity) hL1
      linarith
    rw [h8]
    calc cst / 2 * (16 * A / cst * E) ≤ cst / 2 * x :=
          mul_le_mul_of_nonneg_left h9 (by positivity)
      _ = cst * x / 2 := by ring
  have hKN : 8 / ε ^ 2 * (2 * (N * Real.log x)) ≤ cst * x / 2 := by
    have e : 8 / ε ^ 2 * (2 * (N * (cst * ε ^ 2 / (32 * N) * x))) = cst * x / 2 := by
      field_simp
      ring
    rw [← e]
    have hK0 : 0 ≤ 8 / ε ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogx hNpos.le) (by norm_num)) hK0
  calc 8 / ε ^ 2 * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ)
      ≤ 8 / ε ^ 2 * (A + 2 * Real.log t) :=
        mul_le_mul_of_nonneg_left hlog1 (by positivity)
    _ = 8 / ε ^ 2 * A + 8 / ε ^ 2 * (2 * (N * Real.log x)) := by rw [hlogt]; ring
    _ ≤ cst * x := by linarith

end LogHorizon

/-! ### `thm:v35horizon` at the explicit horizon -/

section PolyAssembled

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {V E : Type*} [Fintype E]
  {Ω : Type*} [MeasurableSpace Ω] {A : Type*}

/-- **Corollary `cor:v35poly`, first clause: certification within a polynomial horizon.**
Hypotheses of `puct_horizon_full` (fixed graph, positive weights, the search contract on
every path, reward tapes, monitor specification), with `0 < ε ≤ e⁻¹`.  For every integer

`t ≥ max {t_*, D ^ (2^H) · (1/ε) ^ (2^(H+1)) · (log (1/ε)) ^ (2^H)}`,
`D = polyD c_* |Z| δ H`,

the event `{τ ≤ t and Reg ≤ ε}` fails with probability at most `δ / 2`.  The constants
`t_*`, `c_*`, `D` depend on the graph, the priors and `δ` only. -/
theorem puct_poly_horizon_full {src tgt : E → V} {root : V} {lam : E → ℝ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    (vis : Ω → ℕ → V → Prop) (ch : Ω → ℕ → V → E) (Q : Ω → E → ℕ → ℝ)
    (hrun : ∀ ω, PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω))
    (term : Z → V) (path : Z → List E) (hpath : ∀ z, IsPath src tgt (path z) root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hreach : ∀ z, ∃ a, z ∈ supp a)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, exactCert (supp a) (hne a)
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s)) ≤ ε) →
        τ ω ≤ s ∧ exactCert (supp (rec ω)) (hne (rec ω))
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω)))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω))) ≤ ε)
    (t : ℕ) (ht : puctTstar src lam path ≤ t) (hε : 0 < ε) (hε1 : ε ≤ Real.exp (-1))
    (hpoly : polyD (puctCstar lam path) (Fintype.card Z) δ H ^ 2 ^ H *
        (1 / ε) ^ 2 ^ (H + 1) * Real.log (1 / ε) ^ 2 ^ H ≤ (t : ℝ)) :
    P {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤
      ENNReal.ofReal (δ / 2) := by
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω0⟩⟩
  · rw [Set.eq_empty_of_isEmpty {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)},
      measure_empty]
    exact zero_le
  have hM : (1 : ℝ) ≤ (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  exact puct_horizon_full P vis ch Q hrun term path hpath H hH supp hne hreach μ hμ X hmeas
    hbdd hmean hindep hδ0 hδ1 ε τ rec hmon t ht hε
    (log_horizon H (puctCstar_pos (hrun ω0).lam_pos path) hM hδ0 hδ1 hε hε1 hpoly)

end PolyAssembled

/-! ### Oracle substitution -/

section OracleSubstitution

open JointRootCert.Representation

variable {Z X Reply Ωc σ σ' S : Type*} [MeasurableSpace S]

/-- **Oracle substitution (Corollary `cor:v35poly`, second clause), general form.**
`s ∈ S` is the sample point; it determines the reward tape `rew s` and the controller tape
`tape s`.  The controller sees only the history and the oracle replies (this is the
`Controller` model: no implementation runtime enters its policy).  If the implementation
`J` exposes the same replies as `I` on every history, then every event of the trajectory
(observation histories, replies, stopping time) has the same probability under both
implementations. -/
theorem oracle_substitution_guarantee (P : Measure S) (I : OracleImpl σ (Z × X) Reply)
    (J : OracleImpl σ' (Z × X) Reply) (hIJ : ∀ h, J.answer h = I.answer h)
    (ctrl : Controller Z X Reply Ωc) (rew : S → ℕ → Z → X) (tape : S → Ωc)
    (good : (ℕ → List (Z × X)) → (ℕ → Reply) → ℕ∞ → Prop) :
    P {s | ¬ good (history J.answer ctrl (rew s) (tape s))
        (replyAt J.answer ctrl (rew s) (tape s)) (stopTime J.answer ctrl (rew s) (tape s))} =
      P {s | ¬ good (history I.answer ctrl (rew s) (tape s))
        (replyAt I.answer ctrl (rew s) (tape s)) (stopTime I.answer ctrl (rew s) (tape s))} := by
  congr 1
  ext s
  obtain ⟨h1, h2, h3⟩ := exact_coupling I J hIJ ctrl (rew s) (tape s)
  simp only [Set.mem_ofPred_eq, funext h1, funext h2, h3]

/-- The same for two circuit representations of the monitor with the same terminal
supports (`representation_coupling`): unary bypass, interning, dyadic-block replacement. -/
theorem circuit_substitution_guarantee {A β : Type*} [SemilatticeSup β] [OrderBot β]
    [DecidableEq Z] (P : Measure S) (box : List (Z × X) → (Z → β) × (Z → β))
    (R R' : A → MaxCircuit Z) (h : ∀ a, MaxCircuit.supp (R' a) = MaxCircuit.supp (R a))
    (ctrl : Controller Z X (A → β × β) Ωc) (rew : S → ℕ → Z → X) (tape : S → Ωc)
    (good : (ℕ → List (Z × X)) → (ℕ → (A → β × β)) → ℕ∞ → Prop) :
    P {s | ¬ good (history (circuitOracle box R') ctrl (rew s) (tape s))
        (replyAt (circuitOracle box R') ctrl (rew s) (tape s))
        (stopTime (circuitOracle box R') ctrl (rew s) (tape s))} =
      P {s | ¬ good (history (circuitOracle box R) ctrl (rew s) (tape s))
        (replyAt (circuitOracle box R) ctrl (rew s) (tape s))
        (stopTime (circuitOracle box R) ctrl (rew s) (tape s))} := by
  rw [circuitOracle_eq_of_supp_eq box R R' h]

/-- **Oracle substitution for a certification guarantee.**  `recOf` reads the recommended
action off the oracle reply.  If, with implementation `I`, the run stops within `t`
rollouts with an `ε`-optimal recommendation outside an event of probability at most `b`
(for instance `b = δ / 2` at the polynomial horizon of `puct_poly_horizon_full`), then the
same holds, with the same `t` and `b`, for every implementation `J` exposing the same
replies. -/
theorem oracle_substitution_certified {Zt A : Type*} [Fintype Zt] [DecidableEq Zt]
    [Nonempty Zt] (P : Measure S) (I : OracleImpl σ (Z × X) Reply)
    (J : OracleImpl σ' (Z × X) Reply) (hIJ : ∀ h, J.answer h = I.answer h)
    (ctrl : Controller Z X Reply Ωc) (rew : S → ℕ → Z → X) (tape : S → Ωc)
    (supp : A → Finset Zt) (hne : ∀ a, (supp a).Nonempty) (μ : Zt → ℝ) (recOf : Reply → A)
    (ε : ℝ) (t : ℕ) (b : ℝ≥0∞)
    (hI : P {s | ¬ ∃ n ≤ t, stoppedAt I.answer ctrl (rew s) (tape s) n ∧
        regret (supp (recOf (replyAt I.answer ctrl (rew s) (tape s) n)))
          (hne _) μ ≤ ε} ≤ b) :
    P {s | ¬ ∃ n ≤ t, stoppedAt J.answer ctrl (rew s) (tape s) n ∧
        regret (supp (recOf (replyAt J.answer ctrl (rew s) (tape s) n)))
          (hne _) μ ≤ ε} ≤ b := by
  refine le_of_eq_of_le ?_ hI
  exact oracle_substitution_guarantee P I J hIJ ctrl rew tape
    (fun hist rep _ => ∃ n ≤ t, ctrl.stop (hist n) (rep n) = true ∧
      regret (supp (recOf (rep n))) (hne _) μ ≤ ε)

end OracleSubstitution

end JointRootCert
