/-
Completions, part 2: Theorem `thm:active-er` (Finite-sample support-sensitive
acquisition), the Safeguarded-LCB and optimistic-separation bounds written out end to end.

* `SGStep`, `sgStep_width`, `active_sg_end_to_end`: Safeguarded-LCB, threshold
  `max {ε / 2, Δ_z / 3}`.
* `OSStep`, `osStep_width`, `active_os_end_to_end`: optimistic separation, threshold
  `max {Γ + ε, Δ_z} / 2`, for `0 ≤ ε` and `Γ + ε > 0` (so `ε = 0` is allowed when `Γ > 0`).

Both are instances of `active_tape_end_to_end`; the only probabilistic input is the
reward-tape model.

Also Theorem `thm:active-restart` (Certified restart bound) on an explicit probability
space: `restartMeasure` (product over episodes of the per-episode tape space),
`restartMeasure_iIndep`, `restartMeasure_iIndepFun`, `restartMeasure_map_eval`, and
`certified_restart_product`, which instantiates `certified_restart_end_to_end` there and
derives its width hypothesis from the optimistic-separation rule (`osStep_width`).
-/
import JointRootCert.Assembly

namespace JointRootCert

open Finset MeasureTheory
open scoped ENNReal

section ActiveRules

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- **One continuing step of Safeguarded-LCB** (Algorithm `alg:certify` with the gate
`eq:safeguard-gate`) on the box `[l, u]`.  Some action `a` minimises the exact certificate,
the certificate exceeds `ε`, and `p`, `q` are optimistic inside and outside witnesses of
`a`.  The inside witness is either `p` itself, or a lower-confidence candidate `y` (a
maximiser of the lower endpoint over `S(a)`) admitted by the gate
`w(y) ≥ max {R(a) / 2, u(p) - u(y)}`.  The queried terminal `z` is the wider of the inside
witness and `q`.  Ties are unconstrained. -/
def SGStep (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (l u : Z → ℝ) (ε : ℝ) (z : Z) : Prop :=
  ∃ (a : A) (p q : Z),
    (∀ c, rectCert (supp a) (hne a) (hpr a) l u ≤ rectCert (supp c) (hne c) (hpr c) l u) ∧
    ε < rectCert (supp a) (hne a) (hpr a) l u ∧
    p ∈ supp a ∧ (∀ y ∈ supp a, u y ≤ u p) ∧
    q ∉ supp a ∧ (∀ y, y ∉ supp a → u y ≤ u q) ∧
    (((z = p ∧ u q - l q ≤ u p - l p) ∨ (z = q ∧ u p - l p ≤ u q - l q)) ∨
      ∃ y, y ∈ supp a ∧ (∀ x ∈ supp a, l x ≤ l y) ∧
        rectCert (supp a) (hne a) (hpr a) l u / 2 ≤ u y - l y ∧ u p - u y ≤ u y - l y ∧
        ((z = y ∧ u q - l q ≤ u y - l y) ∨ (z = q ∧ u y - l y ≤ u q - l q)))

/-- The terminal queried by a continuing Safeguarded-LCB step on a box containing the true
means has width at least `max {ε / 2, Δ_z / 3}` (`active_width` and `active_sg_width`). -/
theorem sgStep_width (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) {l u μ : Z → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hμ : μ ∈ Set.Icc l u) {z : Z} (h : SGStep supp hne hpr l u ε z) :
    max (ε / 2) ((gmax μ - μ z) / 3) ≤ u z - l z := by
  obtain ⟨a, p, q, hmin, hcont, hp, hpmax, hq, hqmax, hsel⟩ := h
  have hlu : l ≤ u := fun y => (hμ.1 y).trans (hμ.2 y)
  rcases hsel with hER | ⟨y, hy, hymax, hg1, hg2, hsel⟩
  · obtain ⟨h1, h2⟩ := active_width supp hne hpr hcov hlu hε a hmin hcont hp hpmax hq hqmax
    obtain ⟨h3, h4⟩ := h2 μ hμ
    rcases hER with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
    · rw [max_eq_left hw] at h1
      have h5 := h3 hw
      have h6 := le_gmax μ z
      exact max_le (by linarith) (by linarith)
    · rw [max_eq_right hw] at h1
      have h5 := h4 hw
      have h6 := le_gmax μ z
      exact max_le (by linarith) (by linarith)
  · obtain ⟨h1, h2⟩ := active_sg_width supp hne hpr hcov hlu hε a hmin hcont hp hpmax hq hqmax
      hy hymax hg1 hg2
    obtain ⟨h3, h4⟩ := h2 μ hμ
    rcases hsel with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
    · rw [max_eq_left hw] at h1
      exact max_le h1.le (h3 hw)
    · rw [max_eq_right hw] at h1
      exact max_le h1.le (h4 hw)

/-- **One continuing step of optimistic-separation sampling** on the box `[l, u]`.  The
global exact-regret stopping test failed (every action has certificate above `ε`), the
sampling action `b` maximises the index `J(a) = U(a) - L⁻(a)` (`osIndex`), `p` and `q` are
optimistic inside and outside witnesses of `b`, and the queried terminal `z` is the wider
of the two.  Ties are unconstrained. -/
def OSStep (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (l u : Z → ℝ) (ε : ℝ) (z : Z) : Prop :=
  (∀ c, ε < rectCert (supp c) (hne c) (hpr c) l u) ∧
  ∃ (b : A) (p q : Z),
    (∀ c, osIndex (supp c) (hne c) (hpr c) l u ≤ osIndex (supp b) (hne b) (hpr b) l u) ∧
    p ∈ supp b ∧ (∀ y ∈ supp b, u y ≤ u p) ∧
    q ∉ supp b ∧ (∀ y, y ∉ supp b → u y ≤ u q) ∧
    ((z = p ∧ u q - l q ≤ u p - l p) ∨ (z = q ∧ u p - l p ≤ u q - l q))

/-- The terminal queried by a continuing optimistic-separation step on a box containing the
true means has width at least `max {Γ + ε, Δ_z} / 2`, where `Γ` is the separation
`V(a) - max_{z ∉ S(a)} μ_z` of any action `a` (in particular the largest one). -/
theorem osStep_width (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) {l u μ : Z → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hμ : μ ∈ Set.Icc l u) (a0 : A) {z : Z} (h : OSStep supp hne hpr l u ε z) :
    max (val (supp a0) (hne a0) μ - (supp a0)ᶜ.sup' (hpr a0) μ + ε) (gmax μ - μ z) / 2 ≤
      u z - l z := by
  obtain ⟨hfail, b, p, q, hmax, hp, hpmax, hq, hqmax, hsel⟩ := h
  have hlu : l ≤ u := fun y => (hμ.1 y).trans (hμ.2 y)
  obtain ⟨-, h2⟩ := active_os_width supp hne hpr hcov hlu hε b hmax (hfail b) hp hpmax hq hqmax
  obtain ⟨hΓ, h3, h4⟩ := h2 μ hμ
  have hΓ0 := hΓ a0
  rw [← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  rcases hsel with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · rw [max_eq_left hw] at hΓ0
    exact max_le hΓ0.le (h3 hw)
  · rw [max_eq_right hw] at hΓ0
    exact max_le hΓ0.le (h4 hw)

variable {Ω : Type*} [MeasurableSpace Ω]

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
/-- In the reward-tape model the means lie in `[0, 1]`. -/
lemma tape_mean_mem_Icc (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) (z : Z) : m z ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (X z 0) P := Integrable.of_mem_Icc 0 1 (hmeas z 0) (hbdd z 0)
  rw [← hmean z 0]
  constructor
  · exact integral_nonneg_of_ae ((hbdd z 0).mono fun ω h => h.1)
  · have := integral_mono_ae hint (integrable_const (1 : ℝ))
      ((hbdd z 0).mono fun ω h => h.2)
    simpa using this

/-- **Safeguarded-LCB, end to end (Theorem `thm:active-er`, SG bound).**

Reward-tape model as in `active_tape_end_to_end`, with `M ≥ max {2, |Z|}`, `0 < δ < 1`,
`0 < ε ≤ 1`, proper supports that cover `Z`.  On every sample path on which the true means
stay in every box, the sampler performs a continuing Safeguarded-LCB step (`SGStep`) on the
current Hoeffding box at each of its `τ` queries and returns an action whose exact
certificate at the stopping time is at most `ε`.  Then with failure probability at most `δ`
the returned action is `ε`-optimal and

`τ ≤ ∑_z ⌈(32 / ρ_z²) log (32 M / (δ ρ_z²))⌉`, `ρ_z = max {ε / 2, Δ_z / 3}`. -/
theorem active_sg_end_to_end (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (sel : Ω → ℕ → Z) (τ : Ω → ℕ) (rec : Ω → A)
    (hrule : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        ∀ t < τ ω, SGStep supp hne hpr (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε (sel ω t))
    (hstop : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (tapeLo M δ (fun z i => X z i ω) (sel ω) (τ ω))
          (tapeHi M δ (fun z i => X z i ω) (sel ω) (τ ω)) ≤ ε) :
    P {ω | ¬ (regret (supp (rec ω)) (hne (rec ω)) m ≤ ε ∧
        τ ω ≤ ∑ z, ⌈32 / (max (ε / 2) ((gmax m - m z) / 3)) ^ 2 *
          Real.log (32 * M / (δ * (max (ε / 2) ((gmax m - m z) / 3)) ^ 2))⌉₊)} ≤
      ENNReal.ofReal δ := by
  have hm01 := tape_mean_mem_Icc P hmeas hbdd hmean
  have hg1 : gmax m ≤ 1 := sup'_le _ _ (fun z _ => (hm01 z).2)
  refine active_tape_end_to_end P hindep hmeas hbdd hmean hM hcard hδ0 hδ1 supp hne hpr
    (fun z => max (ε / 2) ((gmax m - m z) / 3))
    (fun z => ⟨lt_max_of_lt_left (by linarith),
      max_le (by linarith) (by linarith [(hm01 z).1])⟩) ε sel τ rec
    (fun ω hc t ht => sgStep_width supp hne hpr hcov hε0.le (hc t) (hrule ω hc t ht)) hstop

/-- **Optimistic-separation sampling, end to end (Theorem `thm:active-er`, OS bound).**

Reward-tape model as in `active_tape_end_to_end`, with `M ≥ max {2, |Z|}`, `0 < δ < 1`,
proper supports that cover `Z`.  `Γ` is the largest separation
`V(a) - max_{z ∉ S(a)} μ_z` over the actions (`hΓ`).  The accuracy satisfies `0 ≤ ε ≤ 1`
and `Γ + ε > 0`; in particular `ε = 0` is allowed when `Γ > 0`.  On every sample path on
which the true means stay in every box, the sampler performs a continuing
optimistic-separation step (`OSStep`) at each of its `τ` queries and returns an action
whose exact certificate at the stopping time is at most `ε`.  Then with failure probability
at most `δ` the returned action is `ε`-optimal and

`τ ≤ ∑_z ⌈(32 / ρ_z²) log (32 M / (δ ρ_z²))⌉`, `ρ_z = max {Γ + ε, Δ_z} / 2`. -/
theorem active_os_end_to_end (P : Measure Ω) [IsProbabilityMeasure P] {X : Z → ℕ → Ω → ℝ}
    (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P) (hmeas : ∀ z i, AEMeasurable (X z i) P)
    (hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1) {m : Z → ℝ}
    (hmean : ∀ z i, ∫ ω, X z i ω ∂P = m z) {M δ : ℝ} (hM : 2 ≤ M)
    (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε Γ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hΓ : IsGreatest (Set.range fun a => val (supp a) (hne a) m - (supp a)ᶜ.sup' (hpr a) m) Γ)
    (hpos : 0 < Γ + ε)
    (sel : Ω → ℕ → Z) (τ : Ω → ℕ) (rec : Ω → A)
    (hrule : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        ∀ t < τ ω, OSStep supp hne hpr (tapeLo M δ (fun z i => X z i ω) (sel ω) t)
          (tapeHi M δ (fun z i => X z i ω) (sel ω) t) ε (sel ω t))
    (hstop : ∀ ω, tapeCovered M δ (fun z i => X z i ω) (sel ω) m →
        rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (tapeLo M δ (fun z i => X z i ω) (sel ω) (τ ω))
          (tapeHi M δ (fun z i => X z i ω) (sel ω) (τ ω)) ≤ ε) :
    P {ω | ¬ (regret (supp (rec ω)) (hne (rec ω)) m ≤ ε ∧
        τ ω ≤ ∑ z, ⌈32 / (max (Γ + ε) (gmax m - m z) / 2) ^ 2 *
          Real.log (32 * M / (δ * (max (Γ + ε) (gmax m - m z) / 2) ^ 2))⌉₊)} ≤
      ENNReal.ofReal δ := by
  have hm01 := tape_mean_mem_Icc P hmeas hbdd hmean
  have hg1 : gmax m ≤ 1 := sup'_le _ _ (fun z _ => (hm01 z).2)
  obtain ⟨a0, ha0⟩ := hΓ.1
  have ha0' : val (supp a0) (hne a0) m - (supp a0)ᶜ.sup' (hpr a0) m = Γ := ha0
  have hΓ1 : Γ ≤ 1 := by
    rw [← ha0']
    have h1 : val (supp a0) (hne a0) m ≤ 1 := (val_le_gmax _ _ m).trans hg1
    obtain ⟨z0, hz0⟩ := hpr a0
    have h2 : 0 ≤ (supp a0)ᶜ.sup' (hpr a0) m := (hm01 z0).1.trans (le_sup' m hz0)
    linarith
  refine active_tape_end_to_end P hindep hmeas hbdd hmean hM hcard hδ0 hδ1 supp hne hpr
    (fun z => max (Γ + ε) (gmax m - m z) / 2)
    (fun z => ⟨by have := le_max_left (Γ + ε) (gmax m - m z); linarith,
      by have := max_le (show Γ + ε ≤ 2 by linarith)
            (show gmax m - m z ≤ 2 by linarith [(hm01 z).1]); linarith⟩) ε sel τ rec
    (fun ω hc t ht => ?_) hstop
  have h := osStep_width supp hne hpr hcov hε0 (hc t) a0 (hrule ω hc t ht)
  rw [ha0'] at h
  exact h

end ActiveRules

/-! ### `thm:active-restart` on an explicit product space -/

section RestartProduct

open ProbabilityTheory

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- **The sample space of the restarted procedure.**  A sample point is a sequence, indexed
by the episode `j`, of fresh reward tapes `(z, i) ↦ ω j (z, i)` (the `i`-th observation of
terminal `z` in episode `j`).  The measure is the product over episodes of the product
over `(z, i)` of the reward law of terminal `z`. -/
noncomputable def restartMeasure (law : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (law z)] :
    Measure (ℕ → Z × ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun p : Z × ℕ => law p.1))

instance (law : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (law z)] :
    IsProbabilityMeasure (restartMeasure law) := by
  unfold restartMeasure
  infer_instance

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
/-- Every observation of terminal `z`, in every episode, has law `law z`. -/
lemma restartMeasure_map_eval (law : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (law z)]
    (j : ℕ) (z : Z) (i : ℕ) :
    (restartMeasure law).map (fun ω => ω j (z, i)) = law z := by
  have h : (fun ω : ℕ → Z × ℕ → ℝ => ω j (z, i)) =
      (fun x : Z × ℕ → ℝ => x (z, i)) ∘ (fun ω => ω j) := rfl
  rw [h, ← Measure.map_map (measurable_pi_apply _) (measurable_pi_apply _), restartMeasure,
    Measure.infinitePi_map_eval,
    Measure.infinitePi_map_eval (fun p : Z × ℕ => law p.1) (z, i)]

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
/-- The episode tapes `ω ↦ ω j` are independent. -/
lemma restartMeasure_iIndep (law : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (law z)] :
    iIndep (fun j : ℕ => MeasurableSpace.comap (fun ω : ℕ → Z × ℕ → ℝ => ω j) inferInstance)
      (restartMeasure law) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => Measure.infinitePi
    (fun p : Z × ℕ => law p.1)) (X := fun _ x => x) (fun _ => measurable_id)
  exact (iIndepFun_iff_iIndep _ _ _).mp h

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
/-- Within an episode, the observations of one terminal are independent. -/
lemma restartMeasure_iIndepFun (law : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (law z)]
    (j : ℕ) (z : Z) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → Z × ℕ → ℝ) => ω j (z, i)) (restartMeasure law) := by
  have h := iIndepFun_uncurry_infinitePi' (X := fun (_ : ℕ) (_ : Z × ℕ) (x : ℝ) => x)
    (fun (_ : ℕ) (p : Z × ℕ) => law p.1) (fun _ _ => measurable_id)
  exact h.precomp (g := fun i : ℕ => (j, (z, i))) (fun a b hab => by simpa using hab)

open Classical in
/-- The returning episode: the first `j ≥ 1` whose tape is not in the failure set of
episode `j` (`0` if there is none). -/
noncomputable def restartOut (failE : ℕ → Set (Z × ℕ → ℝ)) (ω : ℕ → Z × ℕ → ℝ) : ℕ :=
  if h : ∃ j, 1 ≤ j ∧ ω j ∉ failE j then Nat.find h else 0

open Classical in
omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma restartOut_spec {failE : ℕ → Set (Z × ℕ → ℝ)} {ω : ℕ → Z × ℕ → ℝ}
    (h : ∃ j, 1 ≤ j ∧ ω j ∉ failE j) :
    1 ≤ restartOut failE ω ∧ ω (restartOut failE ω) ∉ failE (restartOut failE ω) := by
  unfold restartOut
  split_ifs
  exact Nat.find_spec h

/-- Total number of observations of the restarted procedure: episode `j + 1` is run when
episodes `1, …, j` all failed, and then uses `obsE (j + 1)` observations. -/
noncomputable def restartTime (failE : ℕ → Set (Z × ℕ → ℝ)) (obsE : ℕ → (Z × ℕ → ℝ) → ℕ)
    (ω : ℕ → Z × ℕ → ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, (⋂ i ∈ Finset.Ico 1 (j + 1), {ω : ℕ → Z × ℕ → ℝ | ω i ∈ failE i}).indicator
    (fun ω => (obsE (j + 1) (ω (j + 1)) : ℝ≥0∞)) ω

/-- **Certified restart bound (Theorem `thm:active-restart`) on an explicit probability
space, for the optimistic-separation rule.**

Probability space.  `law z` is the reward law of terminal `z`: a probability measure on
`ℝ` supported in `[0, 1]` with mean `m z`.  The sample space is `ℕ → Z × ℕ → ℝ` with the
product measure `restartMeasure law`: independent episodes, each carrying fresh
independent tapes.  No independence is assumed; it is proved for this measure.

Procedure.  Episode `j ≥ 1` is a function of its own tape `x`: it queries `selE j x t`,
its uncapped rule makes `σE j x` queries, it uses `obsE j x ≤ 2^j` observations, and it
ends without output exactly on the measurable set `failE j` (timeout or confidence
failure).  On tapes whose boxes at confidence `δ_j = δ / (j (j + 1))` cover the means:
every query is a continuing optimistic-separation step (`OSStep`), and if the rule stops
within the cap the episode returns (`hret`).  An episode that returns outputs `recE j x`,
whose exact certificate at its stopping time is at most `ε` (`hsucc`).  The wrapper returns
the output of the first episode that does not fail (`restartOut`), after `restartTime`
observations.

Thresholds: `ρ_z = max {Γ + ε, Δ_z} / 2` with `Γ` the largest separation, `0 ≤ ε ≤ 1`,
`Γ + ε > 0`, `ρ_min = min_z ρ_z`, `H_ρ = ∑_z ρ_z⁻²`, `L = log (128 M / (δ ρ_min²))`.

Conclusions: `E τ < 1600 H_ρ L`; `τ < ∞` almost surely; the event that no episode returns
is null; the output is not `ε`-optimal with probability at most `δ`. -/
theorem certified_restart_product (law : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (law z)]
    {m : Z → ℝ} (hsupp : ∀ z, ∀ᵐ x ∂(law z), x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z, ∫ x, x ∂(law z) = m z)
    {M δ : ℝ} (hM : 2 ≤ M) (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε Γ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hΓ : IsGreatest (Set.range fun a => val (supp a) (hne a) m - (supp a)ᶜ.sup' (hpr a) m) Γ)
    (hpos : 0 < Γ + ε)
    (selE : ℕ → (Z × ℕ → ℝ) → ℕ → Z) (σE obsE : ℕ → (Z × ℕ → ℝ) → ℕ)
    (recE : ℕ → (Z × ℕ → ℝ) → A) (failE : ℕ → Set (Z × ℕ → ℝ))
    (hfailm : ∀ j, MeasurableSet (failE j)) (hobs : ∀ j x, obsE j x ≤ 2 ^ j)
    (hrule : ∀ j : ℕ, 1 ≤ j → ∀ x : Z × ℕ → ℝ,
      tapeCovered M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) m →
      ∀ t < σE j x, OSStep supp hne hpr
        (tapeLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) t)
        (tapeHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) t) ε
        (selE j x t))
    (hret : ∀ j : ℕ, 1 ≤ j → ∀ x : Z × ℕ → ℝ,
      tapeCovered M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) m →
      σE j x ≤ 2 ^ j → x ∉ failE j)
    (hsucc : ∀ j : ℕ, 1 ≤ j → ∀ x : Z × ℕ → ℝ, x ∉ failE j →
      rectCert (supp (recE j x)) (hne (recE j x)) (hpr (recE j x))
        (tapeLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) (σE j x))
        (tapeHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i)) (selE j x) (σE j x))
          ≤ ε) :
    ∫⁻ ω, restartTime failE obsE ω ∂(restartMeasure law) <
        ENNReal.ofReal (1600 * (∑ z, 1 / (max (Γ + ε) (gmax m - m z) / 2) ^ 2) *
          Real.log (128 * M / (δ * (univ.inf' univ_nonempty
            (fun z => max (Γ + ε) (gmax m - m z) / 2)) ^ 2))) ∧
      (∀ᵐ ω ∂(restartMeasure law), restartTime failE obsE ω < ∞) ∧
      restartMeasure law (⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j, {ω | ω i ∈ failE i}) = 0 ∧
      restartMeasure law {ω | ε < regret (supp (recE (restartOut failE ω)
        (ω (restartOut failE ω)))) (hne _) m} ≤ ENNReal.ofReal δ := by
  -- the tape model on the product space
  have hmeasX : ∀ (j : ℕ) (z : Z) (i : ℕ),
      Measurable (fun ω : ℕ → Z × ℕ → ℝ => ω j (z, i)) := fun j z i =>
    (measurable_pi_apply (z, i)).comp (measurable_pi_apply j)
  have hbdd : ∀ (j : ℕ) (z : Z) (i : ℕ), ∀ᵐ ω ∂(restartMeasure law),
      ω j (z, i) ∈ Set.Icc (0 : ℝ) 1 := by
    intro j z i
    have h := hsupp z
    rw [← restartMeasure_map_eval law j z i] at h
    exact (ae_map_iff (hmeasX j z i).aemeasurable measurableSet_Icc).mp h
  have hmeanX : ∀ (j : ℕ) (z : Z) (i : ℕ), ∫ ω, ω j (z, i) ∂(restartMeasure law) = m z := by
    intro j z i
    rw [← hmean z, ← restartMeasure_map_eval law j z i]
    exact (integral_map (hmeasX j z i).aemeasurable (f := fun x : ℝ => x)
      measurable_id.aestronglyMeasurable).symm
  have hm01 := tape_mean_mem_Icc (restartMeasure law) (X := fun z i ω => ω 0 (z, i))
    (fun z i => (hmeasX 0 z i).aemeasurable) (hbdd 0) (hmeanX 0)
  have hg1 : gmax m ≤ 1 := sup'_le _ _ (fun z _ => (hm01 z).2)
  obtain ⟨a0, ha0⟩ := hΓ.1
  have ha0' : val (supp a0) (hne a0) m - (supp a0)ᶜ.sup' (hpr a0) m = Γ := ha0
  have hΓ1 : Γ ≤ 1 := by
    rw [← ha0']
    have h1 : val (supp a0) (hne a0) m ≤ 1 := (val_le_gmax _ _ m).trans hg1
    obtain ⟨z0, hz0⟩ := hpr a0
    have h2 : 0 ≤ (supp a0)ᶜ.sup' (hpr a0) m := (hm01 z0).1.trans (le_sup' m hz0)
    linarith
  have hρpos : ∀ z, 0 < max (Γ + ε) (gmax m - m z) / 2 := fun z => by
    have := le_max_left (Γ + ε) (gmax m - m z)
    linarith
  have hρ1 : ∀ z, max (Γ + ε) (gmax m - m z) / 2 ≤ 1 := fun z => by
    have := max_le (show Γ + ε ≤ 2 by linarith)
      (show gmax m - m z ≤ 2 by linarith [(hm01 z).1])
    linarith
  have hρmin : 0 < univ.inf' univ_nonempty (fun z => max (Γ + ε) (gmax m - m z) / 2) := by
    rw [lt_inf'_iff]
    exact fun z _ => hρpos z
  refine certified_restart_end_to_end (restartMeasure law)
    (X := fun j z i ω => ω j (z, i)) (restartMeasure_iIndepFun law)
    (fun j z i => (hmeasX j z i).aemeasurable) hbdd hmeanX
    (fun j => MeasurableSpace.comap (fun ω : ℕ → Z × ℕ → ℝ => ω j) inferInstance)
    (fun j => (measurable_pi_apply j).comap_le) (restartMeasure_iIndep law)
    hM hcard hδ0 hδ (fun z => max (Γ + ε) (gmax m - m z) / 2) hρmin
    (fun z => ⟨inf'_le _ (mem_univ z), hρ1 z⟩) supp hne hpr ε
    (fun j ω => selE j (ω j)) (fun j ω => σE j (ω j)) (fun j => {ω | ω j ∈ failE j})
    (fun j => ⟨failE j, hfailm j, rfl⟩) ?_ (fun j hj ω hc hσ => hret j hj (ω j) hc hσ)
    (restartTime failE obsE) ?_ (restartOut failE)
    (fun ω => recE (restartOut failE ω) (ω (restartOut failE ω))) ?_
  · intro j hj ω hc t ht
    have h := osStep_width supp hne hpr hcov hε0 (hc t) a0 (hrule j hj (ω j) hc t ht)
    rw [ha0'] at h
    exact h
  · intro ω
    unfold restartTime
    refine le_trans (tsum_le_tsum (fun j => ?_))
      (tsum_comp_le_tsum_of_injective Nat.succ_injective
        (fun j => (⋂ i ∈ Finset.Ico 1 j, {ω : ℕ → Z × ℕ → ℝ | ω i ∈ failE i}).indicator
          (fun _ => (2 : ℝ≥0∞) ^ j) ω))
    refine Set.indicator_le_indicator ?_
    exact_mod_cast hobs (j + 1) (ω (j + 1))
  · intro ω hω
    have hex : ∃ j, 1 ≤ j ∧ ω j ∉ failE j := by
      simp only [Set.mem_iInter, not_forall] at hω
      obtain ⟨j, i, hi, hni⟩ := hω
      exact ⟨i, (Finset.mem_Ico.mp hi).1, hni⟩
    obtain ⟨h1, h2⟩ := restartOut_spec hex
    exact ⟨h1, hsucc _ h1 _ h2⟩

end RestartProduct

end JointRootCert
