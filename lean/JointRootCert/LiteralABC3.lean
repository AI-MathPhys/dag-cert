/-
Literal forms of main-text and Appendix A--C statements, part 3: four remaining gaps.

* `thm:t4-finite-sample` (Finite-sample cost of safeguarded CD-Joint) with a generic
  anytime-valid radius `β_t`: termination from a growth condition on `β`
  (`cd_generic_terminates`, `growth_of_frequently`, `cd_growth_of_frequently`), the
  end-to-end statement
  (`cd_joint_generic`), the radius `eq:ay-radius` as an instance (`ayRadius_generic_hyps`,
  `cd_joint_ay_generic`), and a run that never stops when `β_t² ≍ t`
  (`cd_growth_necessary`).
* Non-vacuity of the run predicates: `ActiveRun` for the ER, SG and OS rules of
  Algorithm `alg:certify` (`er_run_exists`, `sg_run_exists`, `os_run_exists` and their
  sample-path forms), and `CDRun` for Algorithm `alg:cd-joint` (`cdRun_exists`,
  `cdRun_exists_causal`, `cdRun_exists_ridge`).
* `thm:t3-misspec` (Valid misspecification-aware ellipsoid and safe intersection) with an
  arbitrary terminal confidence box (`t3_safe_intersection_box`).
* `lem:nested-interval-valid` (Anytime validity and nesting of terminal boxes),
  empirical-Bernstein branch, with `M ≥ |Z|` in the threshold `2M/δ` and observations in
  `[0,1]` almost surely (`eb_box_coverage_ae`).
-/
import JointRootCert.LiteralABC
import JointRootCert.LiteralABC2

namespace JointRootCert

namespace LiteralABC3

open Finset MeasureTheory Matrix
open scoped ENNReal
open LiteralABC LiteralABC2

/-! ### Sequential choice -/

section Causal

/-- **Sequential choice.**  If `P x t a` ("`a` is an admissible choice at time `t` given
the sequence `x`") depends on `x` only through `x 0, …, x (t-1)`, and an admissible choice
always exists, then some sequence makes an admissible choice at every time. -/
theorem exists_causal_seq {α : Type*} [Nonempty α] (P : (ℕ → α) → ℕ → α → Prop)
    (hcaus : ∀ f g : ℕ → α, ∀ t a, (∀ s < t, f s = g s) → P f t a → P g t a)
    (hex : ∀ f t, ∃ a, P f t a) : ∃ x : ℕ → α, ∀ t, P x t (x t) := by
  classical
  choose c hc using hex
  let F : ℕ → ℕ → α := fun k => Nat.rec (motive := fun _ => ℕ → α)
    (fun _ => Classical.arbitrary α) (fun k Fk => Function.update Fk k (c Fk k)) k
  have hF : ∀ k, F (k + 1) = Function.update (F k) k (c (F k) k) := fun k => rfl
  have hstab : ∀ k s, s < k → F k s = F (s + 1) s := by
    intro k
    induction k with
    | zero => intro s hs; omega
    | succ k ih =>
      intro s hs
      rcases (show s < k ∨ s = k by omega) with h | h
      · rw [hF, Function.update_of_ne (by omega), ih s h]
      · rw [h]
  refine ⟨fun t => F (t + 1) t, fun t => ?_⟩
  have hx : F (t + 1) t = c (F t) t := by rw [hF, Function.update_self]
  show P (fun t => F (t + 1) t) t (F (t + 1) t)
  rw [hx]
  exact hcaus (F t) _ t _ (fun s hs => hstab t s hs) (hc (F t) t)

end Causal

/-! ### Non-vacuity of `ActiveRun` (Algorithm `alg:certify`) -/

section ActiveExists

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

omit [Fintype Z] [Nonempty Z] in
lemma queryCount_congr {sel sel' : ℕ → Z} {t : ℕ} (h : ∀ s < t, sel s = sel' s) (z : Z) :
    queryCount sel t z = queryCount sel' t z := by
  unfold queryCount
  congr 1
  exact Finset.filter_congr fun s hs => by rw [h s (mem_range.mp hs)]

omit [Fintype Z] [Nonempty Z] in
lemma tapeLo_congr (M δ : ℝ) (x : Z → ℕ → ℝ) {sel sel' : ℕ → Z} {t : ℕ}
    (h : ∀ s < t, sel s = sel' s) : tapeLo M δ x sel t = tapeLo M δ x sel' t := by
  funext z
  simp only [tapeLo, queryCount_congr h z]

omit [Fintype Z] [Nonempty Z] in
lemma tapeHi_congr (M δ : ℝ) (x : Z → ℕ → ℝ) {sel sel' : ℕ → Z} {t : ℕ}
    (h : ∀ s < t, sel s = sel' s) : tapeHi M δ x sel t = tapeHi M δ x sel' t := by
  funext z
  simp only [tapeHi, queryCount_congr h z]

/-- **Runs exist for any rule that can always move.**  If on every nonempty box on which
the stopping test fails the rule `step` admits some terminal, then for every tape there is
an infinite run (`ActiveRun`) of Algorithm `alg:certify` with that rule. -/
theorem activeRun_exists (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) {M δ ε : ℝ}
    (step : (Z → ℝ) → (Z → ℝ) → Z → Prop)
    (hstep : ∀ l u, ¬ Certified supp hne l u ε → l ≤ u → ∃ z, step l u z)
    (x : Z → ℕ → ℝ) : ∃ sel, ActiveRun supp hne M δ ε step x sel := by
  obtain ⟨sel, hsel⟩ := exists_causal_seq
    (fun sel t z => ¬ Certified supp hne (tapeLo M δ x sel t) (tapeHi M δ x sel t) ε →
      tapeLo M δ x sel t ≤ tapeHi M δ x sel t →
        step (tapeLo M δ x sel t) (tapeHi M δ x sel t) z)
    (fun f g t a hfg hP => by
      rw [tapeLo_congr M δ x hfg, tapeHi_congr M δ x hfg] at hP
      exact hP)
    (fun f t => by
      by_cases h1 : Certified supp hne (tapeLo M δ x f t) (tapeHi M δ x f t) ε
      · exact ⟨Classical.arbitrary Z, fun h => absurd h1 h⟩
      by_cases h2 : tapeLo M δ x f t ≤ tapeHi M δ x f t
      · obtain ⟨z, hz⟩ := hstep _ _ h1 h2
        exact ⟨z, fun _ _ => hz⟩
      · exact ⟨Classical.arbitrary Z, fun _ h => absurd h h2⟩)
  exact ⟨sel, hsel⟩

omit [Nonempty Z] in
lemma proper_of_not_certified {supp : A → Finset Z} {hne : ∀ a, (supp a).Nonempty}
    {l u : Z → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (h : ¬ Certified supp hne l u ε) :
    ∀ a, (supp a)ᶜ.Nonempty := fun a => by
  by_contra ha
  exact h (certified_of_full supp hne hε ha)

omit [Nonempty Z] in
lemma rectCert_gt_of_not_certified {supp : A → Finset Z} {hne : ∀ a, (supp a).Nonempty}
    {l u : Z → ℝ} {ε : ℝ} (h : ¬ Certified supp hne l u ε) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (a : A) : ε < rectCert (supp a) (hne a) (hpr a) l u := by
  have h1 : ¬ exactCert (supp a) (hne a) l u ≤ ε := fun h' => h ⟨a, h'⟩
  have h2 : exactCert (supp a) (hne a) l u = rectCert (supp a) (hne a) (hpr a) l u := by
    simp only [exactCert, hpr a, ↓reduceDIte]
  rw [h2] at h1
  exact not_le.mp h1

omit [Nonempty Z] in
lemma exists_witnesses (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (u : Z → ℝ) (a : A) :
    ∃ p q : Z, p ∈ supp a ∧ (∀ y ∈ supp a, u y ≤ u p) ∧ q ∉ supp a ∧
      (∀ y, y ∉ supp a → u y ≤ u q) := by
  obtain ⟨p, hp, hpmax⟩ := (supp a).exists_max_image u (hne a)
  obtain ⟨q, hq, hqmax⟩ := (supp a)ᶜ.exists_max_image u (hpr a)
  exact ⟨p, q, hp, hpmax, mem_compl.mp hq, fun y hy => hqmax y (mem_compl.mpr hy)⟩

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma exists_wider (l u : Z → ℝ) (p q : Z) :
    ∃ z, (z = p ∧ u q - l q ≤ u p - l p) ∨ (z = q ∧ u p - l p ≤ u q - l q) := by
  rcases le_total (u q - l q) (u p - l p) with h | h
  · exact ⟨p, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨q, Or.inr ⟨rfl, h⟩⟩

omit [Nonempty Z] in
/-- The ER rule can always move: on a box where the stopping test fails (`ε ≥ 0`, finitely
many actions), some terminal satisfies `ERRule`. -/
theorem erRule_exists [Finite A] [Nonempty A] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) {l u : Z → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬ Certified supp hne l u ε) : ∃ z, ERRule supp hne ε l u z := by
  have hpr := proper_of_not_certified hε h
  obtain ⟨a, ha⟩ := Finite.exists_min (fun c => rectCert (supp c) (hne c) (hpr c) l u)
  obtain ⟨p, q, hp, hpmax, hq, hqmax⟩ := exists_witnesses supp hne hpr u a
  obtain ⟨z, hz⟩ := exists_wider l u p q
  exact ⟨z, hpr, a, p, q, ha, rectCert_gt_of_not_certified h hpr a, hp, hpmax, hq, hqmax, hz⟩

omit [Nonempty Z] in
/-- The Safeguarded-LCB rule can always move (its ER branch is always available). -/
theorem sgRule_exists [Finite A] [Nonempty A] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) {l u : Z → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬ Certified supp hne l u ε) : ∃ z, SGRule supp hne ε l u z := by
  have hpr := proper_of_not_certified hε h
  obtain ⟨a, ha⟩ := Finite.exists_min (fun c => rectCert (supp c) (hne c) (hpr c) l u)
  obtain ⟨p, q, hp, hpmax, hq, hqmax⟩ := exists_witnesses supp hne hpr u a
  obtain ⟨z, hz⟩ := exists_wider l u p q
  exact ⟨z, hpr, a, p, q, ha, rectCert_gt_of_not_certified h hpr a, hp, hpmax, hq, hqmax,
    Or.inl hz⟩

omit [Nonempty Z] in
/-- The optimistic-separation rule can always move. -/
theorem osRule_exists [Finite A] [Nonempty A] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) {l u : Z → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬ Certified supp hne l u ε) : ∃ z, OSRule supp hne ε l u z := by
  have hpr := proper_of_not_certified hε h
  obtain ⟨b, hb⟩ := Finite.exists_max (fun c => osIndex (supp c) (hne c) (hpr c) l u)
  obtain ⟨p, q, hp, hpmax, hq, hqmax⟩ := exists_witnesses supp hne hpr u b
  obtain ⟨z, hz⟩ := exists_wider l u p q
  exact ⟨z, hpr, fun c => rectCert_gt_of_not_certified h hpr c, b, p, q, hb, hp, hpmax, hq,
    hqmax, hz⟩

omit [Fintype Z] [DecidableEq Z] in
lemma nonempty_of_cover {supp : A → Finset Z} (hcov : ∀ z, ∃ a, z ∈ supp a) : Nonempty A :=
  ⟨(hcov (Classical.arbitrary Z)).choose⟩

/-- **`ActiveRun` with the ER rule is satisfiable** under the hypotheses of
`active_er_literal` (supports cover `Z`, `ε > 0`; here `ε ≥ 0` suffices) and finitely many
actions: for every tape there is a run. -/
theorem er_run_exists [Finite A] (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {M δ ε : ℝ} (hε : 0 ≤ ε) (x : Z → ℕ → ℝ) :
    ∃ sel, ActiveRun supp hne M δ ε (ERRule supp hne ε) x sel :=
  haveI := nonempty_of_cover hcov
  activeRun_exists supp hne _ (fun _ _ h _ => erRule_exists supp hne hε h) x

/-- `ActiveRun` with the Safeguarded-LCB rule is satisfiable (as `er_run_exists`). -/
theorem sg_run_exists [Finite A] (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {M δ ε : ℝ} (hε : 0 ≤ ε) (x : Z → ℕ → ℝ) :
    ∃ sel, ActiveRun supp hne M δ ε (SGRule supp hne ε) x sel :=
  haveI := nonempty_of_cover hcov
  activeRun_exists supp hne _ (fun _ _ h _ => sgRule_exists supp hne hε h) x

/-- `ActiveRun` with the optimistic-separation rule is satisfiable (as `er_run_exists`). -/
theorem os_run_exists [Finite A] (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {M δ ε : ℝ} (hε : 0 ≤ ε) (x : Z → ℕ → ℝ) :
    ∃ sel, ActiveRun supp hne M δ ε (OSRule supp hne ε) x sel :=
  haveI := nonempty_of_cover hcov
  activeRun_exists supp hne _ (fun _ _ h _ => osRule_exists supp hne hε h) x

/-- **The hypothesis `hrun` of `active_er_literal` is satisfiable**: a sampler
`sel : Ω → ℕ → Z` that is an ER run on every sample path exists (no measurability of
`sel` is required by `active_er_literal`). -/
theorem er_sampler_exists {Ω : Type*} [Finite A] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) {M δ ε : ℝ} (hε : 0 ≤ ε)
    (X : Z → ℕ → Ω → ℝ) :
    ∃ sel : Ω → ℕ → Z, ∀ ω, ActiveRun supp hne M δ ε (ERRule supp hne ε)
      (fun z i => X z i ω) (sel ω) :=
  ⟨fun ω => (er_run_exists supp hne hcov hε (fun z i => X z i ω)).choose,
    fun ω => (er_run_exists supp hne hcov hε (fun z i => X z i ω)).choose_spec⟩

/-- The hypothesis `hrun` of `active_sg_literal` is satisfiable. -/
theorem sg_sampler_exists {Ω : Type*} [Finite A] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) {M δ ε : ℝ} (hε : 0 ≤ ε)
    (X : Z → ℕ → Ω → ℝ) :
    ∃ sel : Ω → ℕ → Z, ∀ ω, ActiveRun supp hne M δ ε (SGRule supp hne ε)
      (fun z i => X z i ω) (sel ω) :=
  ⟨fun ω => (sg_run_exists supp hne hcov hε (fun z i => X z i ω)).choose,
    fun ω => (sg_run_exists supp hne hcov hε (fun z i => X z i ω)).choose_spec⟩

/-- The hypothesis `hrun` of `active_os_literal` is satisfiable. -/
theorem os_sampler_exists {Ω : Type*} [Finite A] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) {M δ ε : ℝ} (hε : 0 ≤ ε)
    (X : Z → ℕ → Ω → ℝ) :
    ∃ sel : Ω → ℕ → Z, ∀ ω, ActiveRun supp hne M δ ε (OSRule supp hne ε)
      (fun z i => X z i ω) (sel ω) :=
  ⟨fun ω => (os_run_exists supp hne hcov hε (fun z i => X z i ω)).choose,
    fun ω => (os_run_exists supp hne hcov hε (fun z i => X z i ω)).choose_spec⟩

end ActiveExists

/-! ### Non-vacuity of `CDRun` (Algorithm `alg:cd-joint`) -/

section CDExists

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

omit [Fintype n] [Fintype X] [DecidableEq X] in
lemma design_congr (lam : ℝ) (φ : X → n → ℝ) {x x' : ℕ → X} :
    ∀ t, (∀ s < t, x s = x' s) → design lam φ x t = design lam φ x' t
  | 0, _ => rfl
  | t + 1, h => by
    show design lam φ x t + vecMulVec (φ (x t)) (φ (x t)) =
      design lam φ x' t + vecMulVec (φ (x' t)) (φ (x' t))
    rw [design_congr lam φ t (fun s hs => h s (by omega)), h t (by omega)]

omit [Fintype Z] [DecidableEq Z] [Nonempty Z] in
lemma continuous_cdObj (V : Matrix n n ℝ) (ψ : Z → n → ℝ) (m : n → ℝ) (β : ℝ)
    (S : Finset Z) (z : Z) : Continuous (cdObj V ψ m β S z) := by
  unfold cdObj cdContrast qinv
  simp only [dotProduct, mulVec]
  fun_prop

omit [DecidableEq X] in
/-- **The rule `CDStep` can always move.**  If the supports cover the terminals, `ε ≥ 0`
and no action passes the stopping test, some query satisfies `CDStep`. -/
theorem cdStep_exists (V : Matrix n n ℝ) (m : n → ℝ) (β ε : ℝ) (φ : X → n → ℝ)
    (cost : X → ℝ) (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) (hε : 0 ≤ ε)
    (hunc : ∀ a, ¬ cdDualCert V (fun z => φ (ι z)) m β ε (supp a)) :
    ∃ x, CDStep V m β ε φ cost ι supp x := by
  obtain ⟨yopt, -, hyopt⟩ := (univ : Finset Z).exists_max_image
    (fun y => φ (ι y) ⬝ᵥ m + β * Real.sqrt (qinv V (φ (ι y)))) univ_nonempty
  obtain ⟨b, hb⟩ := hcov yopt
  have hpr : ((supp b)ᶜ).Nonempty := by
    by_contra hfull
    apply hunc b
    refine ⟨hε, fun z hz => ?_⟩
    exact absurd ⟨z, mem_compl.mpr hz⟩ hfull
  have hmin : ∀ z', ∃ p ∈ simplex (supp b), ∀ q ∈ simplex (supp b),
      cdObj V (fun z => φ (ι z)) m β (supp b) z' p ≤
        cdObj V (fun z => φ (ι z)) m β (supp b) z' q := by
    intro z'
    obtain ⟨i, hi⟩ := hne b
    obtain ⟨p, hp, hpm⟩ := (isCompact_simplex (supp b)).exists_isMinOn
      ⟨_, single_mem_simplex (⟨i, hi⟩ : supp b)⟩
      (continuous_cdObj V _ m β (supp b) z').continuousOn
    exact ⟨p, hp, fun q hq => hpm hq⟩
  choose P hP hPmin using hmin
  obtain ⟨z, hz, hzmax⟩ := ((supp b)ᶜ).exists_max_image
    (fun z' => cdObj V (fun z => φ (ι z)) m β (supp b) z' (P z')) hpr
  have : Nonempty X := ⟨ι yopt⟩
  obtain ⟨x, -, hx⟩ := (univ : Finset X).exists_max_image
    (cdScore V φ cost (cdSafeguard ε m (cdContrast (fun z => φ (ι z)) (supp b) z (P z))
      (φ (ι z) - φ (ι yopt)))) univ_nonempty
  exact ⟨x, yopt, b, z, P z, fun y => hyopt y (mem_univ _), hb, mem_compl.mp hz, hP z,
    hPmin z, fun z' hz' => ⟨P z', hP z', hzmax z' (mem_compl.mpr hz')⟩,
    fun x' => hx x' (mem_univ _)⟩

omit [DecidableEq X] in
/-- **`CDRun` is satisfiable when the estimate and the radius are computed from the past.**
`mF x t` and `βF x t` may depend on the query sequence `x`, but only through
`x 0, …, x (t-1)` (`hmF`, `hβF`).  If the supports cover the terminals and `ε ≥ 0`, some
query sequence is an infinite run of Algorithm `alg:cd-joint`. -/
theorem cdRun_exists_causal (lam : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε : 0 ≤ ε) (mF : (ℕ → X) → ℕ → n → ℝ) (βF : (ℕ → X) → ℕ → ℝ)
    (hmF : ∀ x x' t, (∀ s < t, x s = x' s) → mF x t = mF x' t)
    (hβF : ∀ x x' t, (∀ s < t, x s = x' s) → βF x t = βF x' t) :
    ∃ x, CDRun lam φ cost ι supp ε x (mF x) (βF x) := by
  have : Nonempty X := ⟨ι (Classical.arbitrary Z)⟩
  obtain ⟨x, hx⟩ := exists_causal_seq
    (fun x t a => ¬ CDCertified lam φ ι supp ε x (mF x) (βF x) t →
      CDStep (design lam φ x t) (mF x t) (βF x t) ε φ cost ι supp a)
    (fun f g t a hfg hP => by
      have h1 := design_congr lam φ t hfg
      have h2 := hmF f g t hfg
      have h3 := hβF f g t hfg
      unfold CDCertified at hP ⊢
      rw [h1, h2, h3] at hP
      exact hP)
    (fun f t => by
      by_cases hc : CDCertified lam φ ι supp ε f (mF f) (βF f) t
      · exact ⟨Classical.arbitrary X, fun h => absurd hc h⟩
      · obtain ⟨a, ha⟩ := cdStep_exists (design lam φ f t) (mF f t) (βF f t) ε φ cost ι
          supp hne hcov hε (fun a h => hc ⟨a, h⟩)
        exact ⟨a, fun _ => ha⟩)
  exact ⟨x, hx⟩

omit [DecidableEq X] in
/-- **`CDRun` is satisfiable** for fixed estimate and radius sequences, when the supports
cover the terminals and `ε ≥ 0` (the action type is then nonempty). -/
theorem cdRun_exists (lam : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ → n → ℝ) (β : ℕ → ℝ) :
    ∃ x, CDRun lam φ cost ι supp ε x m β :=
  cdRun_exists_causal lam φ cost ι supp hne hcov hε (fun _ => m) (fun _ => β)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

omit [Fintype X] [DecidableEq X] in
lemma ridgeEst_congr (lam : ℝ) (φ : X → n → ℝ) (θs : n → ℝ) (η : ℕ → ℝ) {x x' : ℕ → X}
    {t : ℕ} (h : ∀ s < t, x s = x' s) : ridgeEst lam φ θs x η t = ridgeEst lam φ θs x' η t := by
  unfold ridgeEst
  rw [design_congr lam φ t h]
  congr 1
  exact sum_congr rfl fun s hs => by rw [h s (mem_range.mp hs)]

omit [DecidableEq X] in
/-- **The hypothesis `hrun` of `cd_joint_literal` is satisfiable on each sample path**: with
the ridge estimate and the radius `eq:ay-radius` (both computed from the past), for every
noise path some query sequence is an infinite run.  Measurability of the resulting queries
in `ω` (hypothesis `hx` of `cd_joint_literal`) is not addressed here. -/
theorem cdRun_exists_ridge (lam σ δ B : ℝ) (φ : X → n → ℝ) (cost : X → ℝ) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a)
    {ε : ℝ} (hε : 0 ≤ ε) (θs : n → ℝ) {Ω : Type*} (η : ℕ → Ω → ℝ) :
    ∃ x : ℕ → Ω → X, ∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω)
      (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
      (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)) := by
  have h : ∀ ω, ∃ x : ℕ → X, CDRun lam φ cost ι supp ε x
      (ridgeEst lam φ θs x (fun s => η s ω)) (fun t => ayRadius σ lam δ B (design lam φ x t)) :=
    fun ω => cdRun_exists_causal lam φ cost ι supp hne hcov hε
      (fun x => ridgeEst lam φ θs x (fun s => η s ω))
      (fun x t => ayRadius σ lam δ B (design lam φ x t))
      (fun _ _ _ h => ridgeEst_congr lam φ θs _ h)
      (fun _ _ t h => by simp only [design_congr lam φ t h])
  exact ⟨fun s ω => (h ω).choose s, fun ω => (h ω).choose_spec⟩

end CDExists

/-! ### `thm:t4-finite-sample` with a generic radius -/

section CDGeneric

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}

/-- **Termination of safeguarded CD-Joint for a generic radius.**  Model of
`cd_joint_infinite_run` (`β` positive and nondecreasing), with `c_min ≤ cost x`.  If for
some `T`
`16 c_max (1 + L²/λ) / ε² · β_{T-1}² · d log (1 + T L² / (d λ)) < c_min T`,
the run passes the stopping test at some `t < T`.  (The left side bounds the cost of `T`
uncertified queries by `eq:t4-bound` and the determinant--trace inequality, the right side
bounds it below.) -/
theorem cd_generic_terminates [Nonempty n] {lam : ℝ} (hlam : 0 < lam) (φ : X → n → ℝ)
    (cost : X → ℝ) {cmax cmin Lsq ε : ℝ} (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax)
    (hcmin : ∀ x, cmin ≤ cost x) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε) (ι : Z → X)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (x : ℕ → X) (m : ℕ → n → ℝ)
    (β : ℕ → ℝ) (hβpos : ∀ t, 0 < β t) (hβmono : Monotone β)
    (hrun : CDRun lam φ cost ι supp ε x m β) {T : ℕ}
    (hT : 16 * cmax * (1 + Lsq / lam) / ε ^ 2 * β (T - 1) ^ 2 *
      (Fintype.card n * Real.log (1 + T * Lsq / (Fintype.card n * lam))) < cmin * T) :
    ∃ t < T, CDCertified lam φ ι supp ε x m β t := by
  by_contra hcon
  push Not at hcon
  have hpre := (cd_joint_infinite_run hlam φ cost hcost hφ hε ι supp hne x m β hβpos hβmono
    hrun).1 T hcon
  obtain ⟨x0⟩ : Nonempty X := ⟨ι (Classical.arbitrary Z)⟩
  have hcmax : 0 < cmax := (hcost x0).1.trans_le (hcost x0).2
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ x0)).trans (hφ x0)
  have hlog := log_design_det_le hlam hLsq φ hφ x T
  have hsum : cmin * T ≤ ∑ t ∈ range T, cost (x t) := by
    have h := Finset.card_nsmul_le_sum (range T) (fun t => cost (x t)) cmin
      (fun t _ => hcmin (x t))
    rw [card_range, nsmul_eq_mul] at h
    linarith [mul_comm cmin (T : ℝ)]
  have h1 : 0 ≤ 1 + Lsq / lam := by have := div_nonneg hLsq hlam.le; linarith
  have hK : 0 ≤ 16 * cmax * (1 + Lsq / lam) / ε ^ 2 * β (T - 1) ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcmax.le) h1) (sq_nonneg _))
      (sq_nonneg _)
  have e : 16 * cmax * (1 + Lsq / lam) * β (T - 1) ^ 2 / ε ^ 2 *
        Real.log ((design lam φ x T).det / lam ^ Fintype.card n) =
      16 * cmax * (1 + Lsq / lam) / ε ^ 2 * β (T - 1) ^ 2 *
        Real.log ((design lam φ x T).det / lam ^ Fintype.card n) := by ring
  rw [e] at hpre
  have := mul_le_mul_of_nonneg_left hlog hK
  linarith

/-- **A clean sufficient growth condition.**  If `liminf_t β_t² log t / t = 0` in the form
`∀ C > 0, ∃ t, C β_t² log (t + 2) < t + 1` (implied by `β_t² = o(t / log t)`), then the
termination condition of `cd_generic_terminates` holds for every `K, d, c ≥ 0` and
`c_min > 0`. -/
theorem growth_of_frequently {β : ℕ → ℝ} {K d c cmin : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hc : 0 ≤ c) (hcmin : 0 < cmin)
    (h : ∀ C : ℝ, 0 < C → ∃ t : ℕ, C * β t ^ 2 * Real.log (t + 2) < t + 1) :
    ∃ T : ℕ, K * β (T - 1) ^ 2 * (d * Real.log (1 + T * c)) < cmin * T := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1c : 0 ≤ Real.log (1 + c) := Real.log_nonneg (by linarith)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 1 + Real.log (1 + c) / Real.log 2 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; have := div_nonneg hl1c hl2.le; linarith
  have hC : 0 < K * d * κ / cmin + 1 := by
    have := div_nonneg (mul_nonneg (mul_nonneg hK hd) hκ0) hcmin.le
    linarith
  obtain ⟨t, ht⟩ := h _ hC
  refine ⟨t + 1, ?_⟩
  rw [Nat.add_sub_cancel]
  push_cast
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hlog2 : Real.log 2 ≤ Real.log ((t : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlt : 0 < Real.log ((t : ℝ) + 2) := hl2.trans_le hlog2
  have hA : Real.log (1 + ((t : ℝ) + 1) * c) ≤ κ * Real.log ((t : ℝ) + 2) := by
    have h0 : 0 < 1 + ((t : ℝ) + 1) * c := by have := mul_nonneg (by linarith : (0:ℝ) ≤ t + 1) hc; linarith
    have h1 : Real.log (1 + ((t : ℝ) + 1) * c) ≤ Real.log ((1 + c) * ((t : ℝ) + 2)) :=
      Real.log_le_log h0 (by nlinarith)
    rw [Real.log_mul (by linarith) (by linarith)] at h1
    have h2 : Real.log (1 + c) ≤ Real.log (1 + c) / Real.log 2 * Real.log ((t : ℝ) + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlog2 hl1c
    rw [hκ]
    nlinarith
  have hQ : 0 ≤ β t ^ 2 := sq_nonneg _
  have e1 : K * d * κ = cmin * (K * d * κ / cmin) := by field_simp
  calc K * β t ^ 2 * (d * Real.log (1 + ((t : ℝ) + 1) * c))
      ≤ K * β t ^ 2 * (d * (κ * Real.log ((t : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hd) (mul_nonneg hK hQ)
    _ = cmin * ((K * d * κ / cmin) * (β t ^ 2 * Real.log ((t : ℝ) + 2))) := by
        rw [← mul_assoc cmin, ← e1]; ring
    _ ≤ cmin * ((K * d * κ / cmin + 1) * β t ^ 2 * Real.log ((t : ℝ) + 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcmin.le
        have := mul_nonneg hQ hlt.le
        nlinarith
    _ < cmin * ((t : ℝ) + 1) := mul_lt_mul_of_pos_left ht hcmin

omit [DecidableEq n] [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Nonempty Z] in
/-- The growth hypothesis `hgrow` of `cd_joint_generic` (for one path) follows from
`∀ C > 0, ∃ t, C β_t² log (t + 2) < t + 1`, i.e. `liminf_t β_t² log t / t = 0`. -/
theorem cd_growth_of_frequently [Nonempty n] {lam : ℝ} (hlam : 0 < lam)
    {cmax cmin Lsq ε : ℝ} (hcmax : 0 ≤ cmax) (hcmin : 0 < cmin) (hLsq : 0 ≤ Lsq) {β : ℕ → ℝ}
    (h : ∀ C : ℝ, 0 < C → ∃ t : ℕ, C * β t ^ 2 * Real.log (t + 2) < t + 1) :
    ∃ T : ℕ, 16 * cmax * (1 + Lsq / lam) / ε ^ 2 * β (T - 1) ^ 2 *
      (Fintype.card n * Real.log (1 + T * Lsq / (Fintype.card n * lam))) < cmin * T := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have h1 : 0 ≤ 1 + Lsq / lam := by have := div_nonneg hLsq hlam.le; linarith
  obtain ⟨T, hT⟩ := growth_of_frequently (K := 16 * cmax * (1 + Lsq / lam) / ε ^ 2)
    (d := Fintype.card n) (c := Lsq / (Fintype.card n * lam))
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcmax) h1) (sq_nonneg _)) hd.le
    (div_nonneg hLsq (by positivity)) hcmin h
  refine ⟨T, ?_⟩
  have e : (T : ℝ) * Lsq / (Fintype.card n * lam) = T * (Lsq / (Fintype.card n * lam)) :=
    mul_div_assoc _ _ _
  rw [e]
  exact hT

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Finite-sample cost of safeguarded CD-Joint (Theorem `thm:t4-finite-sample`) for a
generic anytime-valid radius.**

Fixed-feature model: features `φ x` with `‖φ x‖² ≤ Lsq`, costs `c_min ≤ cost x ≤ c_max`,
`0 < cost x`, terminals in the dictionary (`ι`), true parameter `θ*`.  `m t ω` is any
estimate and `β t ω` any radius, positive and nondecreasing in `t` on every path (`hβpos`,
`hβmono`), and anytime valid: the ellipsoids `{θ | ‖θ - m_t‖_{V_t} ≤ β_t}` contain `θ*`
simultaneously for all `t` with probability at least `1 - δ` (`hcov`; this is the
hypothesis "an anytime-valid self-normalized radius").  On every path the radius obeys the
growth condition `hgrow` of `cd_generic_terminates`, and the queries form an infinite run
of Algorithm `alg:cd-joint` (`hrun`).  Then

* on every path the stopping test passes at the stopping time `τ = cdStop` (the procedure
  returns) and the cost up to `τ` satisfies `eq:t4-bound`;
* with probability at least `1 - δ`, every action passing the test at `τ` (in particular the
  returned minimiser) is `ε`-optimal. -/
theorem cd_joint_generic [Nonempty n] [IsProbabilityMeasure μ] {lam δ : ℝ} (hlam : 0 < lam)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax cmin Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hcmin : ∀ x, cmin ≤ cost x)
    (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε) (ι : Z → X) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (θs : n → ℝ) (x : ℕ → Ω → X) (m : ℕ → Ω → n → ℝ)
    (β : ℕ → Ω → ℝ) (hβpos : ∀ t ω, 0 < β t ω) (hβmono : ∀ ω, Monotone fun t => β t ω)
    (hcov : μ {ω | ∃ t, β t ω ^ 2 <
      (θs - m t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ (θs - m t ω)} ≤ ENNReal.ofReal δ)
    (hgrow : ∀ ω, ∃ T : ℕ, 16 * cmax * (1 + Lsq / lam) / ε ^ 2 * β (T - 1) ω ^ 2 *
      (Fintype.card n * Real.log (1 + T * Lsq / (Fintype.card n * lam))) < cmin * T)
    (hrun : ∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω) (fun t => m t ω)
      (fun t => β t ω)) :
    (∀ ω, CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)
        (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ∧
      ∑ t ∈ range (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω)
          (fun t => β t ω)), cost (x t ω) ≤
        16 * cmax * (1 + Lsq / lam) *
          β (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω) - 1)
            ω ^ 2 / ε ^ 2 *
          Real.log ((design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω)
              (fun t => β t ω))).det / lam ^ Fintype.card n)) ∧
    μ {ω | ¬ ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)))
          (fun z => φ (ι z))
          (m (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ω)
          (β (cdStop lam φ ι supp ε (fun s => x s ω) (fun t => m t ω) (fun t => β t ω)) ω)
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤ ENNReal.ofReal δ := by
  have hstop : ∀ ω, ∃ t, CDCertified lam φ ι supp ε (fun s => x s ω) (fun t => m t ω)
      (fun t => β t ω) t := fun ω => by
    obtain ⟨T, hT⟩ := hgrow ω
    obtain ⟨t, -, ht⟩ := cd_generic_terminates hlam φ cost hcost hcmin hφ hε ι supp hne
      (fun s => x s ω) (fun t => m t ω) (fun t => β t ω) (fun t => hβpos t ω) (hβmono ω)
      (hrun ω) hT
    exact ⟨t, ht⟩
  refine ⟨fun ω => ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := (cd_joint_infinite_run hlam φ cost hcost hφ hε ι supp hne
      (fun s => x s ω) (fun t => m t ω) (fun t => β t ω) (fun t => hβpos t ω) (hβmono ω)
      (hrun ω)).2 (hstop ω)
    exact ⟨h1, h2⟩
  · refine (measure_mono ?_).trans hcov
    intro ω hω
    by_contra hgood
    apply hω
    intro r hr
    have hc : ∀ t, (θs - m t ω) ⬝ᵥ design lam φ (fun s => x s ω) t *ᵥ (θs - m t ω) ≤
        β t ω ^ 2 := fun t => not_lt.mp fun h => hgood ⟨t, h⟩
    exact (cd_joint_infinite_run hlam φ cost hcost hφ hε ι supp hne
      (fun s => x s ω) (fun t => m t ω) (fun t => β t ω) (fun t => hβpos t ω) (hβmono ω)
      (hrun ω)).2 (hstop ω) |>.2.2 r θs hr (hc _)

omit [DecidableEq X] in
/-- **The radius `eq:ay-radius` obeys the growth condition** of `cd_generic_terminates` on
every query path (its square grows like `log t`). -/
theorem ayRadius_growth [Nonempty n] {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (φ : X → n → ℝ) {cmax cmin Lsq ε : ℝ}
    (hcmax : 0 ≤ cmax) (hcmin : 0 < cmin) (hLsq : 0 ≤ Lsq) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq)
    (x : ℕ → X) :
    ∃ T : ℕ, 16 * cmax * (1 + Lsq / lam) / ε ^ 2 *
        ayRadius σ lam δ B (design lam φ x (T - 1)) ^ 2 *
        (Fintype.card n * Real.log (1 + T * Lsq / (Fintype.card n * lam))) < cmin * T := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 16 * cmax * (1 + Lsq / lam) / ε ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * lam * B ^ 2 + 4 * σ ^ 2 * Real.log (1 / δ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Lsq / (Fintype.card n * lam) := ⟨_, rfl⟩
  have h1 : 0 ≤ 1 + Lsq / lam := by have := div_nonneg hLsq hlam.le; linarith
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcmax) h1) (sq_nonneg _)
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg hLsq (by positivity)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈(K * (a + 4 * b * (Fintype.card n : ℝ)) *
      (4 * (Fintype.card n : ℝ))) ^ 2 * c / cmin ^ 2 +
      K * (a + 4 * b * (Fintype.card n : ℝ)) * (4 * (Fintype.card n : ℝ)) / cmin⌉₊ :=
    ⟨_, rfl⟩
  refine ⟨N + 1, ?_⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ,
      ℓ = (Fintype.card n : ℝ) * Real.log (1 + c * ((N + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have e : (Fintype.card n : ℝ) *
      Real.log (1 + ((N + 1 : ℕ) : ℝ) * Lsq / (Fintype.card n * lam)) = ℓ := by
    rw [hℓ, hc]
    congr 2
    ring
  rw [e, ← hK]
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓ]
    refine mul_nonneg hd.le (Real.log_nonneg ?_)
    have := mul_nonneg hc0 (Nat.cast_nonneg (α := ℝ) (N + 1))
    linarith
  -- the squared radius at time `N` is at most `a + b ℓ`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log ((design lam φ x N).det / lam ^ Fintype.card n) :=
    ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (pow_pos hlam _), one_mul, ← design_det_zero lam φ x]
    exact design_det_mono hlam φ x (Nat.zero_le _)
  have hLℓ : L ≤ ℓ := by
    have h := log_design_det_le hlam hLsq φ hφ x N
    rw [← hL] at h
    refine h.trans ?_
    rw [hℓ]
    refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hd.le
    · have := div_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hLsq) (by positivity :
        (0 : ℝ) ≤ Fintype.card n * lam)
      linarith
    · rw [hc]
      have hN1 : ((N : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
      have := mul_le_mul_of_nonneg_right hN1 (div_nonneg hLsq (by positivity :
        (0 : ℝ) ≤ Fintype.card n * lam))
      have e2 : (N : ℝ) * Lsq / (Fintype.card n * lam) =
          (N : ℝ) * (Lsq / (Fintype.card n * lam)) := by ring
      rw [e2]
      linarith
  have hβN : ayRadius σ lam δ B (design lam φ x N) ^ 2 ≤ a + b * ℓ := by
    have h2 : ayRadius σ lam δ B (design lam φ x N) =
        Real.sqrt lam * B + σ * Real.sqrt (2 * Real.log (1 / δ) + L) := by
      rw [hL]
      rfl
    have hu : 0 ≤ 2 * Real.log (1 / δ) + L := by linarith
    have h3 : ayRadius σ lam δ B (design lam φ x N) ^ 2 ≤
        2 * (Real.sqrt lam * B) ^ 2 +
          2 * (σ * Real.sqrt (2 * Real.log (1 / δ) + L)) ^ 2 := by
      rw [h2]
      nlinarith [sq_nonneg (Real.sqrt lam * B - σ * Real.sqrt (2 * Real.log (1 / δ) + L))]
    have h4 : (Real.sqrt lam * B) ^ 2 = lam * B ^ 2 := by rw [mul_pow, Real.sq_sqrt hlam.le]
    have h5 : (σ * Real.sqrt (2 * Real.log (1 / δ) + L)) ^ 2 =
        σ ^ 2 * (2 * Real.log (1 / δ) + L) := by rw [mul_pow, Real.sq_sqrt hu]
    rw [h4, h5] at h3
    have h6 : σ ^ 2 * L ≤ σ ^ 2 * ℓ := mul_le_mul_of_nonneg_left hLℓ (sq_nonneg σ)
    rw [ha, hb]
    nlinarith
  by_contra hcon
  have hcon' := not_lt.mp hcon
  have hcostb : cmin * ((N + 1 : ℕ) : ℝ) ≤ K * (a + b * ℓ) * ℓ := by
    refine hcon'.trans ?_
    have := mul_le_mul_of_nonneg_left hβN hK0
    have := mul_le_mul_of_nonneg_right this hℓ0
    linarith
  have hfin := real_termination hcmin hK0 ha0 hb0 hc0 hd.le (Nat.cast_nonneg _) hℓ0
    (by rw [hℓ]) hcostb
  have hle : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    refine hfin.trans ?_
    rw [hN]
    exact Nat.le_ceil _
  have : N + 1 ≤ N := by exact_mod_cast hle
  omega

omit [DecidableEq X] in
/-- **The radius `eq:ay-radius` satisfies the hypotheses of `cd_joint_generic`.**  Model of
`cd_joint_literal` (predictable queries, conditionally `σ`-sub-Gaussian noise,
`‖θ*‖ ≤ B`, `0 < δ < 1`), with `m` the ridge estimate and `β_t` the radius
`√λ B + σ √(2 log (1/δ) + log (det V_t / λ^d))`: `β` is positive and nondecreasing on
every path, the coverage hypothesis `hcov` holds, and the growth hypothesis `hgrow` holds
for every `c_min > 0`. -/
theorem ayRadius_generic_hyps [Nonempty n] [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) {cmax cmin Lsq ε : ℝ} (hcmax : 0 ≤ cmax) (hcmin : 0 < cmin)
    (hLsq : 0 ≤ Lsq) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq)
    (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) {η : ℕ → Ω → ℝ} (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) :
    (∀ t ω, 0 < ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)) ∧
    (∀ ω, Monotone fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)) ∧
    μ {ω | ∃ t, ayRadius σ lam δ B (design lam φ (fun s => x s ω) t) ^ 2 <
      (θs - ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t) ⬝ᵥ
        design lam φ (fun s => x s ω) t *ᵥ
          (θs - ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t)} ≤
      ENNReal.ofReal δ ∧
    (∀ ω, ∃ T : ℕ, 16 * cmax * (1 + Lsq / lam) / ε ^ 2 *
        ayRadius σ lam δ B (design lam φ (fun s => x s ω) (T - 1)) ^ 2 *
        (Fintype.card n * Real.log (1 + T * Lsq / (Fintype.card n * lam))) < cmin * T) := by
  refine ⟨fun t ω => ayRadius_design_pos hσ hlam hδ0 hδ1 hB φ (fun s => x s ω) t,
    fun ω s t hst => ayRadius_design_mono hσ hlam φ (fun s => x s ω) hst, ?_,
    fun ω => ayRadius_growth hσ hlam hδ0 hδ1 φ hcmax hcmin hLsq hφ (fun s => x s ω)⟩
  have hφm : ∀ s, Measurable[ℱ s] (fun ω => φ (x s ω)) := by
    intro s
    have hxm : @Measurable Ω X (ℱ s) ⊤ (x s) :=
      @measurable_to_countable' X Ω ⊤ _ (ℱ s) (x s) (fun x0 => hx s x0)
    exact (measurable_from_top (f := φ) : @Measurable X (n → ℝ) ⊤ _ φ).comp hxm
  refine (measure_mono ?_).trans (ay_radius_whp ℱ hσ hlam hδ0 hB (η := η)
    (φ := fun s ω => φ (x s ω)) θs hθ hφm hη hsub)
  rintro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have e1 : ridgeDesign lam (fun s : Fin t => φ (x s ω)) = design lam φ (fun s => x s ω) t :=
    (ridgeDesign_fin_eq lam (fun s ω => φ (x s ω)) t ω).trans
      (design_eq_snDesign lam φ x ω t).symm
  have e2 : ∑ s : Fin t, (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω) =
      ∑ s ∈ range t, (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω) :=
    Fin.sum_univ_eq_sum_range (fun s => (φ (x s ω) ⬝ᵥ θs + η s ω) • φ (x s ω)) t
  rw [e1, e2]
  refine Real.lt_sqrt_of_sq_lt ?_
  have hneg : ∀ v : n → ℝ, θs - v = -(v - θs) := fun v => by rw [neg_sub]
  rw [hneg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at ht
  exact ht

/-- **`cd_joint_literal` recovered from the generic theorem**: with the ridge estimate and
the radius `eq:ay-radius`, on every path the run returns with the cost bound
`eq:t4-bound`, and with probability at least `1 - δ` every returned action is
`ε`-optimal. -/
theorem cd_joint_ay_generic [Nonempty n] [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (φ : X → n → ℝ) (cost : X → ℝ) {cmax Lsq ε : ℝ}
    (hcost : ∀ x, 0 < cost x ∧ cost x ≤ cmax) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq) (hε : 0 < ε)
    (ι : Z → X) (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2) {η : ℕ → Ω → ℝ} (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    (hη : ∀ s, Measurable[ℱ (s + 1)] (η s)) (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ)
    (hrun : ∀ ω, CDRun lam φ cost ι supp ε (fun s => x s ω)
      (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
      (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))) :
    (∀ ω, CDCertified lam φ ι supp ε (fun s => x s ω)
        (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
        (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))
        (cdStop lam φ ι supp ε (fun s => x s ω)
          (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
          (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)))) ∧
    μ {ω | ¬ ∀ r : A,
        cdDualCert (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω)
              (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
              (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))))
          (fun z => φ (ι z))
          (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω)
              (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
              (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t))))
          (ayRadius σ lam δ B (design lam φ (fun s => x s ω)
            (cdStop lam φ ι supp ε (fun s => x s ω)
              (ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω))
              (fun t => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)))))
          ε (supp r) →
        regret (supp r) (hne r) (fun z => φ (ι z) ⬝ᵥ θs) ≤ ε} ≤ ENNReal.ofReal δ := by
  obtain ⟨x0⟩ : Nonempty X := ⟨ι (Classical.arbitrary Z)⟩
  have hcmin0 : 0 < cost x0 := (hcost x0).1
  have hcmax : 0 ≤ cmax := hcmin0.le.trans (hcost x0).2
  have hLsq : 0 ≤ Lsq := (dotProduct_self_nonneg' (φ x0)).trans (hφ x0)
  obtain ⟨xm, -, hxm⟩ := (univ : Finset X).exists_min_image cost ⟨x0, mem_univ _⟩
  obtain ⟨hpos, hmono, hcov, hgrow⟩ := ayRadius_generic_hyps (ε := ε) ℱ hσ hlam hδ0 hδ1 hB φ
    hcmax (hcost xm).1 hLsq hφ θs hθ x hx hη hsub
  have h := cd_joint_generic (μ := μ) hlam φ cost hcost (fun y => hxm y (mem_univ _)) hφ hε ι
    supp hne θs x (fun t ω => ridgeEst lam φ θs (fun s => x s ω) (fun s => η s ω) t)
    (fun t ω => ayRadius σ lam δ B (design lam φ (fun s => x s ω) t)) hpos hmono hcov hgrow
    hrun
  exact ⟨fun ω => (h.1 ω).1, h.2⟩

end CDGeneric

/-! ### A growth condition is necessary -/

section Necessity

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- `gᵀ V_t g ≤ (λ + t L²) ‖g‖²`. -/
lemma quad_design_le {lam Lsq : ℝ} (φ : X → n → ℝ) (hφ : ∀ x, φ x ⬝ᵥ φ x ≤ Lsq)
    (x : ℕ → X) (t : ℕ) (g : n → ℝ) :
    g ⬝ᵥ design lam φ x t *ᵥ g ≤ (lam + t * Lsq) * (g ⬝ᵥ g) := by
  rw [design_eq_gram lam φ x t, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, gram_quadratic]
  have hcs : ∀ s, (φ (x s) ⬝ᵥ g) ^ 2 ≤ Lsq * (g ⬝ᵥ g) := fun s => by
    have h := cauchy_schwarz_matrix (M := (1 : Matrix n n ℝ)) (by simp)
      (fun z => by simpa using dotProduct_self_nonneg' z) (φ (x s)) g
    simp only [one_mulVec] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hφ _) (dotProduct_self_nonneg' g))
  have h := sum_le_sum fun s (_ : s ∈ range t) => hcs s
  rw [sum_const, card_range, nsmul_eq_mul] at h
  calc lam * (g ⬝ᵥ g) + ∑ s ∈ range t, (φ (x s) ⬝ᵥ g) ^ 2
      ≤ lam * (g ⬝ᵥ g) + t * (Lsq * (g ⬝ᵥ g)) := by linarith
    _ = (lam + t * Lsq) * (g ⬝ᵥ g) := by ring

omit [Fintype X] [DecidableEq X] in
/-- `‖g‖⁴ ≤ (gᵀ V g) ‖g‖²_{V⁻¹}`. -/
lemma qinv_ge {V : Matrix n n ℝ} {lam : ℝ} (hV : Coercive V lam) (hlam : 0 < lam)
    (g : n → ℝ) : (g ⬝ᵥ g) ^ 2 ≤ (g ⬝ᵥ V *ᵥ g) * qinv V g := by
  have h := cauchy_schwarz_matrix hV.symm (hV.psd hlam) g (V⁻¹ *ᵥ g)
  rw [hV.mul_inv_mulVec hlam] at h
  have e : (V⁻¹ *ᵥ g) ⬝ᵥ g = qinv V g := dotProduct_comm _ _
  rw [e] at h
  exact h

/-- Features of the two-query instance: `φ true = 1`, `φ false = 0` in dimension one. -/
def nφ : Bool → Unit → ℝ := fun b _ => if b then 1 else 0

/-- Supports of the two-action instance: `S(a) = {a}`. -/
def nsupp : Bool → Finset Bool := fun a => {a}

/-- A radius with `β_t² = (ε + 1)² (t + 1)`. -/
noncomputable def nβ (ε : ℝ) : ℕ → ℝ := fun t => (ε + 1) * Real.sqrt (t + 1)

/-- **Some growth condition on `β` is necessary for "returns".**  Instance: dimension one,
`λ = 1`, two queries with `φ true = 1`, `φ false = 0` (so `L² = 1`), unit costs, terminals
`Z = X = Bool` with `ι = id`, two actions with supports `{a}` (covering `Z`), `θ* = 0`, zero
noise.  With `ε > 0` and the radius `β_t = (ε + 1) √(t + 1)`:

* `β` is positive and nondecreasing, `β_t² = (ε + 1)² (t + 1)`;
* the ridge estimate is `0` on every query path, so the coverage event holds surely;
* infinite runs of Algorithm `alg:cd-joint` exist;
* on every query path the stopping test fails at every time: the procedure never returns.

So `cd_joint_infinite_run`'s hypotheses (positive nondecreasing anytime-valid radius) do not
imply termination; `β_t² ≍ t` already fails, while `β_t² = o(t / log t)` suffices
(`growth_of_frequently`). -/
theorem cd_growth_necessary {ε : ℝ} (hε : 0 < ε) :
    (∀ t, 0 < nβ ε t) ∧ Monotone (nβ ε) ∧ (∀ t, nβ ε t ^ 2 = (ε + 1) ^ 2 * (t + 1)) ∧
    (∀ x : ℕ → Bool, ∀ t, ridgeEst 1 nφ 0 x (fun _ => 0) t = 0) ∧
    (∀ x : ℕ → Bool, ∀ t, ((0 : Unit → ℝ) - 0) ⬝ᵥ design 1 nφ x t *ᵥ ((0 : Unit → ℝ) - 0) ≤
      nβ ε t ^ 2) ∧
    (∀ x, nφ x ⬝ᵥ nφ x ≤ 1) ∧
    (∃ x, CDRun 1 nφ (fun _ => 1) id nsupp ε x (fun _ => 0) (nβ ε)) ∧
    ∀ (x : ℕ → Bool) t, ¬ CDCertified 1 nφ id nsupp ε x (fun _ => 0) (nβ ε) t := by
  have hφ : ∀ x, nφ x ⬝ᵥ nφ x ≤ 1 := fun x => by cases x <;> simp [nφ, dotProduct]
  have hsq : ∀ t : ℕ, nβ ε t ^ 2 = (ε + 1) ^ 2 * (t + 1) := fun t => by
    unfold nβ
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  refine ⟨fun t => by unfold nβ; positivity, fun s t hst => ?_, hsq, fun x t => ?_,
    fun x t => by simp only [sub_zero, zero_dotProduct]; exact sq_nonneg _, hφ, ?_, ?_⟩
  · unfold nβ
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by linarith)
    have : (s : ℝ) ≤ t := by exact_mod_cast hst
    linarith
  · simp [ridgeEst, nφ, dotProduct]
  · exact cdRun_exists 1 nφ (fun _ => 1) id nsupp (fun a => by simp [nsupp])
      (fun z => ⟨z, by simp [nsupp]⟩) hε.le _ _
  · rintro x t ⟨a, -, hall⟩
    obtain ⟨p, hp, hle⟩ := hall (!a) (by cases a <;> simp [nsupp])
    have hg : cdContrast (fun z => nφ (id z)) (nsupp a) (!a) p = nφ (!a) - nφ a := by
      unfold cdContrast
      congr 1
      have h1 : ∀ y : ↥(nsupp a), p y • nφ (id (y : Bool)) = p y • nφ a := fun y => by
        have hy : (y : Bool) = a := Finset.mem_singleton.mp y.2
        rw [id, hy]
      rw [sum_congr rfl (fun y _ => h1 y), ← sum_smul, hp.2, one_smul]
    have hgg : (nφ (!a) - nφ a) ⬝ᵥ (nφ (!a) - nφ a) = 1 := by
      cases a <;> simp [nφ, dotProduct]
    set g := nφ (!a) - nφ a with hgdef
    have hV := design_coercive 1 nφ x t
    have hq0 := hV.qinv_nonneg one_pos g
    have hge := qinv_ge hV one_pos g
    have hle2 := quad_design_le (lam := 1) nφ hφ x t g
    rw [hgg] at hge hle2
    have hq : 1 ≤ (1 + t) * qinv (design 1 nφ x t) g := by
      have := mul_le_mul_of_nonneg_right hle2 hq0
      nlinarith
    beta_reduce at hle
    have hobj : cdObj (design 1 nφ x t) (fun z => nφ (id z)) (0 : Unit → ℝ) (nβ ε t) (nsupp a)
        (!a) p = nβ ε t * Real.sqrt (qinv (design 1 nφ x t) g) := by
      unfold cdObj
      rw [hg]
      simp [dotProduct]
    rw [hobj] at hle
    have hβ0 : 0 ≤ nβ ε t := by unfold nβ; positivity
    have hprod : nβ ε t * Real.sqrt (qinv (design 1 nφ x t) g) =
        Real.sqrt (nβ ε t ^ 2 * qinv (design 1 nφ x t) g) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ0]
    rw [hprod] at hle
    have hlt : ε < Real.sqrt (nβ ε t ^ 2 * qinv (design 1 nφ x t) g) := by
      refine Real.lt_sqrt_of_sq_lt ?_
      rw [hsq]
      have e : (ε + 1) ^ 2 * ((t : ℝ) + 1) * qinv (design 1 nφ x t) g =
          (ε + 1) ^ 2 * ((1 + t) * qinv (design 1 nφ x t) g) := by ring
      rw [e]
      nlinarith
    linarith

end Necessity

/-! ### `thm:t3-misspec` with an arbitrary terminal confidence box -/

section MisspecBox

variable {n : Type*} [Fintype n] [DecidableEq n] {Ω : Type*} {X : Type*} [Fintype X]
variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Proposition `thm:t3-misspec`, safe intersection, with an arbitrary terminal box.**

Model of `t3_misspec_radius`.  `[lo t ω, hi t ω]` is any terminal confidence box that
contains the true value vector `z ↦ m₀ + φ_zᵀ θ* + b_z` at all times with probability at
least `1 - δ/2` (`hbox`).  Its intersection with the model-based plausible value set at
level `δ/2` contains the true value vector at all times with probability at least
`1 - δ`. -/
theorem t3_safe_intersection_box [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {σ lam δ ξ B : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hB : 0 ≤ B) (hξ : 0 ≤ ξ)
    (φ : X → n → ℝ) (b : X → ℝ) (mu0 : ℝ) (θs : n → ℝ) (hθ : θs ⬝ᵥ θs ≤ B ^ 2)
    (hb : ∀ z, |b z| ≤ ξ) (x : ℕ → Ω → X)
    (hx : ∀ s x0, MeasurableSet[ℱ s] {ω | x s ω = x0})
    {α : ℕ → Ω → ℝ} (hα01 : ∀ s ω, α s ω = 0 ∨ α s ω = 1) (hα : ∀ s, Measurable[ℱ s] (α s))
    {η : ℕ → Ω → ℝ} (hη : ∀ s, Measurable[ℱ (s + 1)] (η s))
    (hsub : ∀ s, CondSubG μ (ℱ s) (η s) σ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ s ω, Y s ω = mu0 + φ (x s ω) ⬝ᵥ θs + b (x s ω) + η s ω)
    (lo hi : ℕ → Ω → X → ℝ)
    (hbox : μ {ω | ∃ t, (fun z => mu0 + φ z ⬝ᵥ θs + b z) ∉ Set.Icc (lo t ω) (hi t ω)} ≤
      ENNReal.ofReal (δ / 2)) :
    μ {ω | ∃ t, (fun z => mu0 + φ z ⬝ᵥ θs + b z) ∉
        plausibleValues mu0 ξ φ
            (inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω)
            (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
            (misRadius σ lam (δ / 2) B ξ (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
              (effCount α t ω)) ∩
          Set.Icc (lo t ω) (hi t ω)} ≤ ENNReal.ofReal δ := by
  refine safe_intersection μ hδ0.le
    (fun t ω => plausibleValues mu0 ξ φ
      (inclRLS lam α (fun s ω => φ (x s ω)) (fun s ω => Y s ω - mu0) t ω)
      (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
      (misRadius σ lam (δ / 2) B ξ (inclDesign lam α (fun s ω => φ (x s ω)) t ω)
        (effCount α t ω)))
    (fun t ω => Set.Icc (lo t ω) (hi t ω)) (fun z => mu0 + φ z ⬝ᵥ θs + b z) ?_ hbox
  refine (measure_mono ?_).trans (t3_misspec_radius ℱ hσ hlam (half_pos hδ0) hB hξ φ b mu0
    θs hθ hb x hx hα01 hα hη hsub Y hY)
  rintro ω ⟨t, hnot⟩
  refine ⟨t, ?_⟩
  by_contra hcon
  exact hnot ⟨θs, b, hb, not_lt.mp hcon, rfl⟩

end MisspecBox

/-! ### `lem:nested-interval-valid`, empirical-Bernstein branch, general `M` -/

section EBGeneral

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
lemma ebLo_congr {L : ℝ} {Y Y' : ℕ → Ω → ℝ} {ω : Ω} (h : ∀ i, Y i ω = Y' i ω) (k : ℕ) :
    ebLo L Y ω k = ebLo L Y' ω k := by
  simp only [ebLo, ebLam, ebVar, ebMu, h]

omit [MeasurableSpace Ω] in
lemma ebHi_congr {L : ℝ} {Y Y' : ℕ → Ω → ℝ} {ω : Ω} (h : ∀ i, Y i ω = Y' i ω) (k : ℕ) :
    ebHi L Y ω k = ebHi L Y' ω k := by
  simp only [ebHi, ebLam, ebVar, ebMu, h]

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- **Anytime validity of the empirical-Bernstein terminal boxes (Lemma
`lem:nested-interval-valid`, empirical-Bernstein branch), with a general `M`.**
Reward-tape model: for each terminal the observations `X z i` are independent,
a.e.-measurable, `[0,1]`-valued almost surely, with mean `m z`.  The threshold is
`L = log (2 M / δ)` for any `M ≥ |Z|` with `δ < 2 M` (so `L > 0`).  For arbitrary
path-dependent counts `N t ω z`, the running-intersection boxes contain `m` at all times
with probability at least `1 - δ`. -/
theorem eb_box_coverage_ae [IsProbabilityMeasure μ] {δ M : ℝ} (hδ : 0 < δ)
    (hM : (Fintype.card Z : ℝ) ≤ M) (hδM : δ < 2 * M) (X : Z → ℕ → Ω → ℝ) (m : Z → ℝ)
    (hmeas : ∀ z i, AEMeasurable (X z i) μ) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) μ)
    (hbdd : ∀ z i, ∀ᵐ ω ∂μ, X z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z i, ∫ ω, X z i ω ∂μ = m z) (N : ℕ → Ω → Z → ℕ) :
    μ {ω | ∃ t z, m z ∉ Set.Icc
        (runLo (ebLo (Real.log (2 * M / δ)) (X z) ω) (N t ω z))
        (runHi (ebHi (Real.log (2 * M / δ)) (X z) ω) (N t ω z))} ≤
      ENNReal.ofReal δ := by
  have hcard : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hM0 : 0 < M := hcard.trans_le hM
  -- a measurable, everywhere `[0,1]`-valued version of the observations
  set X' : Z → ℕ → Ω → ℝ := fun z i ω => max 0 (min 1 ((hmeas z i).mk _ ω)) with hX'
  have hX'm : ∀ z i, Measurable (X' z i) := fun z i =>
    measurable_const.max (measurable_const.min (hmeas z i).measurable_mk)
  have hX'01 : ∀ z i ω, X' z i ω ∈ Set.Icc (0 : ℝ) 1 := fun z i ω =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hae : ∀ z i, X z i =ᵐ[μ] X' z i := fun z i => by
    filter_upwards [(hmeas z i).ae_eq_mk, hbdd z i] with ω h1 h2
    simp only [hX', ← h1, min_eq_right h2.2, max_eq_right h2.1]
  have hindep' : ∀ z, ProbabilityTheory.iIndepFun (X' z) μ := fun z =>
    (hindep z).congr (hae z)
  have hmean' : ∀ z i, ∫ ω, X' z i ω ∂μ = m z := fun z i => by
    rw [← integral_congr_ae (hae z i), hmean]
  -- the error level `δ' = δ |Z| / M ≤ δ` has the same threshold `2 |Z| / δ' = 2 M / δ`
  set δ' : ℝ := δ * Fintype.card Z / M with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'M : δ' < 2 * Fintype.card Z := by
    rw [hδ', div_lt_iff₀ hM0]
    nlinarith
  have hδ'le : δ' ≤ δ := by
    rw [hδ', div_le_iff₀ hM0]
    nlinarith
  have hL : Real.log (2 * Fintype.card Z / δ') = Real.log (2 * M / δ) := by
    congr 1
    rw [hδ']
    field_simp
  have hcov := eb_box_coverage hδ'0 hδ'M X' m hX'm hindep' hX'01 hmean' N
  rw [hL] at hcov
  refine (measure_mono_ae ?_).trans (hcov.trans (ENNReal.ofReal_le_ofReal hδ'le))
  have hall : ∀ᵐ ω ∂μ, ∀ z i, X z i ω = X' z i ω := by
    rw [ae_all_iff]
    intro z
    rw [ae_all_iff]
    exact hae z
  filter_upwards [hall] with ω hω
  rintro ⟨t, z, hnot⟩
  refine ⟨t, z, ?_⟩
  have h1 : runLo (ebLo (Real.log (2 * M / δ)) (X z) ω) (N t ω z) =
      runLo (ebLo (Real.log (2 * M / δ)) (X' z) ω) (N t ω z) := by
    congr 1
    funext k
    exact ebLo_congr (hω z) k
  have h2 : runHi (ebHi (Real.log (2 * M / δ)) (X z) ω) (N t ω z) =
      runHi (ebHi (Real.log (2 * M / δ)) (X' z) ω) (N t ω z) := by
    congr 1
    funext k
    exact ebHi_congr (hω z) k
  rw [← h1, ← h2]
  exact hnot

end EBGeneral

end LiteralABC3

end JointRootCert
