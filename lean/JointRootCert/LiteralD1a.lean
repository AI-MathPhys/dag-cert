/-
# Known-variance Gaussian finite-confidence results, as written

Manuscript results covered (`app:bay-finite`):

* `prop:bay-finite` (Finite-confidence discovery, frozen confirmation, and safeguard);
* `thm:v10g-discovery` (Explicit discovery and a frozen near-optimal plan);
* `prop:v10g-safety-fallback` (Conditional safety and a finite-mean reference design);
* `thm:v10g-expectation` (Correlated finite-confidence discovery and confirmation);
* `cor:v10g-target` (Finite-confidence correlated confirmation bound).

What this file adds to `GaussianFinite.lean`.

1. The procedure is one object, `FCProc`: its global stopping time `FCProc.tau` (pilot,
   frozen confirmation and reference safeguard interleaved by the constant-share calendar)
   and its returned action `FCProc.ret`.  The numerical enclosures are the manuscript's:
   `Z̲_n ∈ [max{0, Z_n - 1}, Z_n]`, `B̄_n ∈ [B(n, δ/2), B(n, δ/2) + 1]`, and safeguard
   distances with lower error at most one (`FCProc.Spec`).  Safety
   (`FCProc.safe`: `P(τ < ∞ and regret(returned action) > ε) ≤ δ`) and the expectation
   bound (`FCProc.expectation`) are statements about that one object.
2. `I_*(θ) = max_{a,w} I_a(θ, w)` and `C₀ = max_a I_a(θ, w⁰)` are shown to be attained
   (`exists_IstarG_max`, `exists_C0G_max`), `C₀ ≥ k₀ I_* / ℓ²` (`C0G_ge`), and the results
   are restated with these constants.
3. The hypotheses are shown satisfiable: an oracle meeting `OracleContract` with Borel
   measurable outputs (`exists_oracle`), and one probability space `tapeP` carrying the
   pilot, confirmation and safeguard tapes with the required independence.  The final
   statements `bay_finite_literal`, `v10g_expectation_literal`, `v10g_discovery_literal`,
   `safety_fallback_literal` are on that space and have no independence or contract
   hypothesis.
4. The zero-observation hull screen for universal actions (`hull_screen_safe`,
   `screen_dichotomy`); the theorems above are for the remaining branch, in which every
   action has a strict invalidating alternative.

The enclosures of the constructed procedure are the exact values (which lie in the
manuscript's brackets); `FCProc.safe_tape` and `FCProc.expectation_tape` hold for every
procedure meeting `FCProc.Spec`.  The constructed oracle scans a dense sequence of designs
and is not a finite computation.
-/
import JointRootCert.GaussianFinite
import JointRootCert.GaussianUpper
import JointRootCert.GaussianTracking

namespace JointRootCert

namespace LiteralD1

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

universe uX

/-! ### The procedure as one object -/

section Proc

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {𝒜 : Type*}

/-- **The spanning-pilot, frozen-design, fresh-confirmation, independent-safeguard
procedure of `app:bay-finite`.**  Data: query features `u`, reference design `w0`, calendar
share `k`, pilot tolerances `e j`, the allocation oracle (`oa`, `ow`, `ol`: action, design
and lower endpoint returned at stage `j` and center `v`), the lower enclosure `Zlow` of the
confirmation statistic, the upper enclosure `Bbar` of the boundary, and the safeguard's lower
enclosures `Jlow` of the action distances. -/
structure FCProc (X : Type uX) (E : Type*) (𝒜 : Type*) where
  /-- query features -/
  u : X → E
  /-- reference design `w⁰` -/
  w0 : X → ℝ
  /-- calendar share `k = s / 16` -/
  k : ℝ
  /-- pilot tolerances `e_j` -/
  e : ℕ → ℝ
  /-- oracle action -/
  oa : ℕ → E → 𝒜
  /-- oracle design -/
  ow : ℕ → E → X → ℝ
  /-- oracle lower endpoint -/
  ol : ℕ → E → ℝ
  /-- lower enclosure `Z̲_n` (arguments: committing stage, pilot tape, confirmation tape, `n`) -/
  Zlow : ℕ → (X → ℕ → ℝ) → (X → ℕ → ℝ) → ℕ → ℝ
  /-- upper enclosure `B̄_n` -/
  Bbar : ℕ → ℝ
  /-- safeguard lower enclosures of the action distances -/
  Jlow : ℕ → (X → ℕ → ℝ) → 𝒜 → ℝ

namespace FCProc

variable (p : FCProc X E 𝒜)

/-- Observations the main branch (pilot, then confirmation) needs before it stops; `⊤` if
it never stops.  Arguments: pilot and confirmation observation tapes. -/
noncomputable def mainN (y y' : X → ℕ → ℝ) : ℝ≥0∞ :=
  mainObs p.u p.w0 p.e p.k p.ow p.ol p.Zlow p.Bbar y y'

/-- Observations the reference safeguard needs before it stops; `⊤` if it never stops. -/
noncomputable def sgN (yF : X → ℕ → ℝ) : ℝ≥0∞ :=
  roundTotal p.w0 (firstTime (sgStop p.Jlow p.Bbar yF))

/-- After `t` global observations the main branch has received what it needs. -/
def mainReady (y y' : X → ℕ → ℝ) (t : ℕ) : Prop :=
  p.mainN y y' ≤ ENNReal.ofReal ((t : ℝ) - ⌊p.k * (t : ℝ)⌋)

/-- After `t` global observations the safeguard has received what it needs. -/
def sgReady (yF : X → ℕ → ℝ) (t : ℕ) : Prop :=
  p.sgN yF ≤ ENNReal.ofReal (⌊p.k * (t : ℝ)⌋ : ℝ)

/-- **The global stopping time** `τ`: the first global observation count `t` at which one
of the two branches has received the observations it needs, under the constant-share
calendar (the safeguard has received `⌊k t⌋` of the first `t` observations). -/
noncomputable def tau (y y' yF : X → ℕ → ℝ) : ℝ≥0∞ :=
  calTime p.k (p.mainN y y') (p.sgN yF)

open Classical in
/-- The action frozen by the pilot, if the main branch ever stops. -/
noncomputable def mainAct (y y' : X → ℕ → ℝ) : Option 𝒜 :=
  if h : ∃ j, commitAt p.e p.k p.ol (pilotV p.u p.w0 y) j ∧
      ∃ n : ℕ, 1 ≤ n ∧ p.Bbar n ≤ p.Zlow j y y' n then
    some (p.oa (Classical.choose h) (pilotV p.u p.w0 y (Classical.choose h)))
  else none

open Classical in
/-- An action certified by the safeguard at its stopping count, if it ever stops. -/
noncomputable def sgAct (yF : X → ℕ → ℝ) : Option 𝒜 :=
  if h : ∃ n, sgStop p.Jlow p.Bbar yF n then some (Classical.choose (Nat.find_spec h).2)
  else none

open Classical in
/-- **The returned action**: at the global stopping time, the action of the branch that
has stopped (the frozen action of the main branch, or a certified action of the safeguard);
`none` if the procedure never stops. -/
noncomputable def ret (y y' yF : X → ℕ → ℝ) : Option 𝒜 :=
  if h : ∃ t : ℕ, p.mainReady y y' t ∨ p.sgReady yF t then
    if p.mainReady y y' (Nat.find h) then p.mainAct y y' else p.sgAct yF
  else none

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mainAct_spec {y y' : X → ℕ → ℝ} {a : 𝒜} (h : p.mainAct y y' = some a) :
    ∃ j, commitAt p.e p.k p.ol (pilotV p.u p.w0 y) j ∧
      (∃ n : ℕ, 1 ≤ n ∧ p.Bbar n ≤ p.Zlow j y y' n) ∧ a = p.oa j (pilotV p.u p.w0 y j) := by
  classical
  unfold mainAct at h
  split_ifs at h with hex
  have hs := Classical.choose_spec hex
  exact ⟨Classical.choose hex, hs.1, hs.2, (Option.some.inj h).symm⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [Fintype X] in
lemma sgAct_spec {yF : X → ℕ → ℝ} {a : 𝒜} (h : p.sgAct yF = some a) :
    ∃ n : ℕ, 1 ≤ n ∧ p.Bbar n ≤ p.Jlow n yF a := by
  classical
  unfold sgAct at h
  split_ifs at h with hex
  have hs := Classical.choose_spec (Nat.find_spec hex).2
  rw [Option.some.inj h] at hs
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, hs⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mainAct_isSome {y y' : X → ℕ → ℝ} (h : p.mainN y y' < ⊤) : (p.mainAct y y').isSome := by
  classical
  have hex : ∃ j, commitAt p.e p.k p.ol (pilotV p.u p.w0 y) j ∧
      ∃ n : ℕ, 1 ≤ n ∧ p.Bbar n ≤ p.Zlow j y y' n := by
    unfold mainN mainObs at h
    obtain ⟨j, hj⟩ := iInf_lt_iff.mp h
    obtain ⟨hc, hlt⟩ := iInf_lt_iff.mp hj
    refine ⟨j, hc, ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : firstTime (fun n => 1 ≤ n ∧ p.Bbar n ≤ p.Zlow j y y' n) = ⊤ :=
      firstTime_eq_top (fun n hn => absurd hn.2 (not_le.mpr (hcon n hn.1)))
    rw [h1] at hlt
    simp [roundTotal] at hlt
  unfold mainAct
  split_ifs
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
lemma sgAct_isSome {yF : X → ℕ → ℝ} (h : p.sgN yF < ⊤) : (p.sgAct yF).isSome := by
  classical
  have hex : ∃ n, sgStop p.Jlow p.Bbar yF n := by
    by_contra hcon
    push Not at hcon
    unfold sgN at h
    rw [firstTime_eq_top hcon] at h
    simp [roundTotal] at h
  unfold sgAct
  split_ifs
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The procedure stops (`τ < ∞`) exactly when it returns an action. -/
theorem ret_isSome_iff (y y' yF : X → ℕ → ℝ) :
    (p.ret y y' yF).isSome ↔ p.tau y y' yF < ⊤ := by
  classical
  have hiff : p.tau y y' yF < ⊤ ↔ ∃ t : ℕ, p.mainReady y y' t ∨ p.sgReady yF t := by
    unfold tau calTime
    constructor
    · intro h
      obtain ⟨t, ht⟩ := iInf_lt_iff.mp h
      obtain ⟨hc, -⟩ := iInf_lt_iff.mp ht
      exact ⟨t, hc⟩
    · rintro ⟨t, ht⟩
      exact (iInf₂_le t ht).trans_lt (ENNReal.natCast_lt_top t)
  rw [hiff]
  unfold ret
  constructor
  · intro h
    by_contra hcon
    split_ifs at h
    simp at h
  · intro hex
    split_ifs with hm
    · exact p.mainAct_isSome (lt_of_le_of_lt hm ENNReal.ofReal_lt_top)
    · have hs : p.sgReady yF (Nat.find hex) := (Nat.find_spec hex).resolve_left hm
      exact p.sgAct_isSome (lt_of_le_of_lt hs ENNReal.ofReal_lt_top)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The global stopping time is the first global count at which a branch is ready. -/
theorem tau_eq_find {y y' yF : X → ℕ → ℝ}
    (h : ∃ t : ℕ, p.mainReady y y' t ∨ p.sgReady yF t) [DecidablePred fun t : ℕ =>
      p.mainReady y y' t ∨ p.sgReady yF t] :
    p.tau y y' yF = (Nat.find h : ℕ) := by
  unfold tau calTime
  refine le_antisymm (iInf₂_le (Nat.find h) (Nat.find_spec h)) ?_
  refine le_iInf₂ (fun t ht => ?_)
  exact_mod_cast Nat.find_min' h ht

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma ret_cases {y y' yF : X → ℕ → ℝ} {a : 𝒜} (h : p.ret y y' yF = some a) :
    p.mainAct y y' = some a ∨ p.sgAct yF = some a := by
  classical
  unfold ret at h
  split_ifs at h with h1 h2
  · exact Or.inl h
  · exact Or.inr h

/-- **The requirements the manuscript places on the procedure's numerical components**
(`app:bay-finite`), for alternative sets `Q`, feature bound `ℓ`, reference constant `k₀`,
pilot risk `α` and confidence `δ`:
the tolerances satisfy `ℓ ρ_j / √2 ≤ e_j ≤ √2 ℓ ρ_j`; the oracle meets the contract
`eq:v10g-oracle` (for some upper endpoints `ou`) and its design and lower endpoint are Borel
functions of the center; `Z̲_n ∈ [max{0, Z_n - 1}, Z_n]`;
`B̄_n ∈ [B(n, δ/2), B(n, δ/2) + 1]`; and the safeguard distances are lower enclosures with
error at most one, measurable in the tape. -/
structure Spec (Q : 𝒜 → Set E) (ℓ k0 α δ : ℝ) : Prop where
  he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ p.e j
  he2 : ∀ j, p.e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j
  contract : ∃ ou : ℕ → E → ℝ, OracleContract p.u Q p.w0 p.k p.e p.oa p.ow p.ol ou
  hol : ∀ j, Measurable (p.ol j)
  how : ∀ j x, Measurable (fun v => p.ow j v x)
  hZlo : ∀ j y y' (n : ℕ), max 0 (confirmZ p.u (p.ow j (pilotV p.u p.w0 y j))
    (pilotV p.u p.w0 y j) (p.ol j (pilotV p.u p.w0 y j)) y' n - 1) ≤ p.Zlow j y y' n
  hZup : ∀ j y y' (n : ℕ), p.Zlow j y y' n ≤ confirmZ p.u (p.ow j (pilotV p.u p.w0 y j))
    (pilotV p.u p.w0 y j) (p.ol j (pilotV p.u p.w0 y j)) y' n
  hBlo : ∀ n : ℕ, boundary (Module.finrank ℝ E) n (δ / 2) ≤ p.Bbar n
  hBup : ∀ n : ℕ, p.Bbar n ≤ boundary (Module.finrank ℝ E) n (δ / 2) + 1
  hJm : ∀ n a, Measurable (fun Y : X → ℕ → ℝ => p.Jlow n Y a)
  hJlo : ∀ (n : ℕ) Y a, gInfo p.u (Q a) (olsCount p.u (roundCount p.w0 n) Y)
    (fun x => (roundCount p.w0 n x : ℝ)) - 1 ≤ p.Jlow n Y a
  hJup : ∀ (n : ℕ) Y a, p.Jlow n Y a ≤ gInfo p.u (Q a) (olsCount p.u (roundCount p.w0 n) Y)
    (fun x => (roundCount p.w0 n x : ℝ))

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **Safety of the procedure** (`thm:v10g-expectation`, first sentence; `prop:bay-finite`):
`P_θ(τ < ∞ and the returned action has regret above ε) ≤ δ`, for every parameter `θ`.
The event concerns the stopping time `tau` and the returned action `ret` of the one
procedure `p`.  Hypotheses: the model (`M(w⁰) ⪰ k₀ I`, three tapes of independent standard
Gaussians, the pilot tape independent of the confirmation tape) and `p.Spec`. -/
theorem safe [IsProbabilityMeasure P] (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (hw0 : p.w0 ∈ simplex X) {ℓ k0 α δ : ℝ}
    (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap p.u p.w0 v‖ ^ 2)
    (hk : 0 < p.k) (hk1 : p.k ≤ 1)
    (hS : p.Spec (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 α δ)
    {ξP ξC ξF : X → ℕ → Ω → ℝ} (hξPm : ∀ x i, Measurable (ξP x i))
    (hξCm : ∀ x i, Measurable (ξC x i))
    (hindC : iIndepFun (fun q : X × ℕ => ξC q.1 q.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hindF : iIndepFun (fun q : X × ℕ => ξF q.1 q.2) P)
    (hξF : ∀ x i, HasLaw (ξF x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (θ : E) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    P {ω | p.tau (obsTape p.u θ ξP ω) (obsTape p.u θ ξC ω) (obsTape p.u θ ξF ω) < ⊤ ∧
      ∃ a, p.ret (obsTape p.u θ ξP ω) (obsTape p.u θ ξC ω) (obsTape p.u θ ξF ω) = some a ∧
        ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal δ := by
  obtain ⟨ou, hor⟩ := hS.contract
  refine (measure_mono ?_).trans (v10g_safe φ supp hne ε p.u hw0 hk0 hM0 hk hk1 hor hS.hol
    hS.how hξPm hξCm hindC hξC hindF hξF hPC θ hδ0 hδ1 hS.hBlo hS.hJup)
  rintro ω ⟨-, a, hret, hbad⟩
  rcases p.ret_cases hret with hm | hs
  · obtain ⟨j, hc, ⟨n, hn, hZ⟩, rfl⟩ := p.mainAct_spec hm
    exact Or.inl ⟨j, hc, n, hn, hZ.trans (hS.hZup j _ _ n), hbad⟩
  · obtain ⟨n, hn, hJ⟩ := p.sgAct_spec hs
    exact Or.inr ⟨n, hn, a, hJ, hbad⟩

/-- **The expectation bound** (`thm:v10g-expectation`, `eq:v10g-finite`) for the stopping
time of the same procedure: `E_θ τ ≤ min {𝓑_δ, H_δ / k + 1}`.  `C` and `C₀` are positive
numbers with `C ≤ I_a(θ, w)` for some `(a, w)` and `C₀ ≤ I_{a₀}(θ, w⁰)` for some `a₀`
(`expectation_star` takes the maxima). -/
theorem expectation [IsProbabilityMeasure P] [Countable 𝒜] (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) (hw0 : p.w0 ∈ simplex X) {ℓ k0 α δ : ℝ}
    (hℓ : 0 < ℓ) (hu : ∀ x, ‖p.u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap p.u p.w0 v‖ ^ 2)
    (hk : 0 < p.k) (hk1 : p.k < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : p.Spec Q ℓ k0 α δ)
    {ξP ξC ξF : X → ℕ → Ω → ℝ}
    (hξPm : ∀ x i, Measurable (ξP x i)) (hξCm : ∀ x i, Measurable (ξC x i))
    (hξFm : ∀ x i, Measurable (ξF x i))
    (hindP : iIndepFun (fun q : X × ℕ => ξP q.1 q.2) P)
    (hξP : ∀ x i, HasLaw (ξP x i) (gaussianReal 0 1) P)
    (hindC : iIndepFun (fun q : X × ℕ => ξC q.1 q.2) P)
    (hξC : ∀ x i, HasLaw (ξC x i) (gaussianReal 0 1) P)
    (hindF : iIndepFun (fun q : X × ℕ => ξF q.1 q.2) P)
    (hξF : ∀ x i, HasLaw (ξF x i) (gaussianReal 0 1) P)
    (hPC : IndepFun (fun ω x i => ξP x i ω) (fun ω x i => ξC x i ω) P)
    (hPCF : IndepFun (fun ω => ((fun x i => ξP x i ω : X → ℕ → ℝ),
      (fun x i => ξC x i ω : X → ℕ → ℝ))) (fun ω x i => ξF x i ω) P)
    (θ : E) (aS : 𝒜) {wS : X → ℝ} (hwS : wS ∈ simplex X) {C : ℝ} (hC : 0 < C)
    (hCle : C ≤ gInfo p.u (Q aS) θ wS) (a0 : 𝒜) {C0 : ℝ} (hC0 : 0 < C0)
    (hC0le : C0 ≤ gInfo p.u (Q a0) θ p.w0) :
    ∫⁻ ω, p.tau (obsTape p.u θ ξP ω) (obsTape p.u θ ξC ω) (obsTape p.u θ ξF ω) ∂P ≤
      ENNReal.ofReal (min
        (Bdelta (Dbar (pilotA ℓ k0 p.k C) (Module.finrank ℝ E) α (Fintype.card X))
          (logBudget (aC (Module.finrank ℝ E) p.k (cstar p.k * C) δ α) (bC p.k (cstar p.k * C)))
          (Fintype.card X) p.k α (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0))
        (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ C0 / p.k + 1)) := by
  obtain ⟨ou, hor⟩ := hS.contract
  exact v10g_expectation p.u Q hQ hw0 hℓ hu hk0 hM0 hk hk1 hα0 hα1 hδ0 hδ1 hS.he1 hS.he2 hor
    hS.hol hS.how hξPm hξCm hξFm hindP hξP hindC hξC hindF hξF hPC hPCF θ aS hwS hC hCle a0 hC0
    hC0le (fun j y y' n => (le_max_right _ _).trans (hS.hZlo j y y' n)) hS.hBup hS.hJm hS.hJlo

end FCProc

end Proc

/-! ### `I_*(θ)` and `C₀` are attained maxima -/

section Star

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {𝒜 : Type*}

/-- `I_*(θ) = max_{a, w ∈ Δ(X)} I_a(θ, w)`, defined as a supremum; `exists_IstarG_max` shows
that it is an attained maximum. -/
noncomputable def IstarG (u : X → E) (Q : 𝒜 → Set E) (θ : E) : ℝ :=
  sSup {r : ℝ | ∃ a, ∃ w ∈ simplex X, r = gInfo u (Q a) θ w}

/-- `C₀ = max_a I_a(θ, w⁰)`, defined as a supremum; attained by `exists_C0G_max`. -/
noncomputable def C0G (u : X → E) (Q : 𝒜 → Set E) (θ : E) (w0 : X → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a, r = gInfo u (Q a) θ w0}

omit [InnerProductSpace ℝ E] in
lemma exists_feature_bound (u : X → E) : ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ x, ‖u x‖ ≤ ℓ :=
  ⟨∑ x, ‖u x‖ + 1, by positivity, fun x =>
    (Finset.single_le_sum (f := fun x => ‖u x‖) (fun x _ => norm_nonneg _) (mem_univ x)).trans
      (by linarith)⟩

/-- The information is continuous in the design on the simplex (from
`rootInfo_joint_continuous`). -/
lemma continuousOn_gInfo (u : X → E) {Q : Set E} (hQ : Q.Nonempty) (θ : E) :
    ContinuousOn (fun w : X → ℝ => gInfo u Q θ w) (simplex X) := by
  obtain ⟨ℓ, -, hu⟩ := exists_feature_bound u
  have hroot : ContinuousOn (fun w : X → ℝ => rootInfo (designMap u w) Q θ) (simplex X) := by
    rw [Metric.continuousOn_iff]
    intro w hw ε hε
    obtain ⟨δ, hδ, h⟩ := rootInfo_joint_continuous u hu hQ θ hw hε
    refine ⟨δ, hδ, fun w' hw' hd => ?_⟩
    rw [Real.dist_eq]
    refine h θ w' hw' (by simpa using hδ.le) (fun x => ?_)
    have h1 : dist (w' x) (w x) ≤ dist w' w := dist_le_pi_dist _ _ x
    rw [Real.dist_eq] at h1
    linarith
  unfold gInfo
  exact (hroot.pow 2).div_const 2

/-- **`I_*(θ)` is attained**: with finitely many actions, some action and some design in
the simplex have `I_a(θ, w) = I_*(θ)`, and every other pair has at most that value. -/
theorem exists_IstarG_max [Finite 𝒜] [Nonempty 𝒜] (u : X → E) (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) (θ : E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) :
    ∃ a, ∃ w ∈ simplex X, gInfo u (Q a) θ w = IstarG u Q θ ∧
      ∀ a', ∀ w' ∈ simplex X, gInfo u (Q a') θ w' ≤ IstarG u Q θ := by
  have hmax : ∀ a, ∃ w ∈ simplex X, ∀ w' ∈ simplex X, gInfo u (Q a) θ w' ≤ gInfo u (Q a) θ w :=
    fun a => (isCompact_simplex X).exists_isMaxOn ⟨w0, hw0⟩ (continuousOn_gInfo u (hQ a) θ)
  choose wA hwA hwAmax using hmax
  obtain ⟨a, ha⟩ := Finite.exists_max (fun a => gInfo u (Q a) θ (wA a))
  have hgr : IsGreatest {r : ℝ | ∃ a, ∃ w ∈ simplex X, r = gInfo u (Q a) θ w}
      (gInfo u (Q a) θ (wA a)) := by
    refine ⟨⟨a, wA a, hwA a, rfl⟩, ?_⟩
    rintro _ ⟨a', w', hw', rfl⟩
    exact (hwAmax a' w' hw').trans (ha a')
  have heq : IstarG u Q θ = gInfo u (Q a) θ (wA a) := hgr.csSup_eq
  refine ⟨a, wA a, hwA a, heq.symm, fun a' w' hw' => ?_⟩
  rw [heq]
  exact hgr.2 ⟨a', w', hw', rfl⟩

/-- **`C₀` is attained**. -/
theorem exists_C0G_max [Finite 𝒜] [Nonempty 𝒜] (u : X → E) (Q : 𝒜 → Set E) (θ : E)
    (w0 : X → ℝ) :
    ∃ a, gInfo u (Q a) θ w0 = C0G u Q θ w0 ∧ ∀ a', gInfo u (Q a') θ w0 ≤ C0G u Q θ w0 := by
  obtain ⟨a, ha⟩ := Finite.exists_max (fun a => gInfo u (Q a) θ w0)
  have hgr : IsGreatest {r : ℝ | ∃ a, r = gInfo u (Q a) θ w0} (gInfo u (Q a) θ w0) := by
    refine ⟨⟨a, rfl⟩, ?_⟩
    rintro _ ⟨a', rfl⟩
    exact ha a'
  have heq : C0G u Q θ w0 = gInfo u (Q a) θ w0 := hgr.csSup_eq
  refine ⟨a, heq.symm, fun a' => ?_⟩
  rw [heq]
  exact ha a'

/-- **`C₀ ≥ k₀ C / ℓ²`** (`app:bay-finite`, "the inherited geometry"), with `C = I_*(θ)`. -/
theorem C0G_ge [Finite 𝒜] [Nonempty 𝒜] (u : X → E) (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) (θ : E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 : ℝ}
    (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 ≤ k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) :
    k0 / ℓ ^ 2 * IstarG u Q θ ≤ C0G u Q θ w0 := by
  obtain ⟨a, w, hw, heq, -⟩ := exists_IstarG_max u Q hQ θ hw0
  obtain ⟨-, -, hC0⟩ := exists_C0G_max u Q θ w0
  refine le_trans ?_ (hC0 a)
  rw [← heq]
  have hdom : ∀ v, Real.sqrt k0 / ℓ * ‖designMap u w v‖ ≤ ‖designMap u w0 v‖ := by
    intro v
    have h1 := reference_design_dominates u hw hℓ hk0 hu hM0 v
    refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |>.2
    rw [mul_pow, div_pow, Real.sq_sqrt hk0]
    exact h1
  have h2 := rootInfo_mono_design (A := designMap u w) (G := designMap u w0) (Q := Q a)
    (θ := θ) (hQ a) (by positivity : 0 ≤ Real.sqrt k0 / ℓ) hdom
  have h3 := pow_le_pow_left₀ (mul_nonneg (by positivity) rootInfo_nonneg) h2 2
  rw [mul_pow, div_pow, Real.sq_sqrt hk0] at h3
  unfold gInfo
  have e : k0 / ℓ ^ 2 * (rootInfo (designMap u w) (Q a) θ ^ 2 / 2) =
      k0 / ℓ ^ 2 * rootInfo (designMap u w) (Q a) θ ^ 2 / 2 := by ring
  rw [e]
  linarith

end Star

/-! ### One probability space carrying the three tapes -/

section Space

variable (X : Type uX)

/-- **The probability space of the procedure**: a sample point is a triple (indexed by
`Fin 3`: pilot, confirmation, safeguard) of noise tapes `(x, i) ↦ ω b (x, i)`; the measure
is the product of standard Gaussians over all coordinates. -/
noncomputable def tapeP : Measure (Fin 3 → X × ℕ → ℝ) :=
  Measure.infinitePi (fun _ : Fin 3 => Measure.infinitePi (fun _ : X × ℕ => gaussianReal 0 1))

instance : IsProbabilityMeasure (tapeP X) := by
  unfold tapeP
  infer_instance

variable {X}

/-- The `i`-th noise of query `x` on tape `b`. -/
def tapeξ (b : Fin 3) (x : X) (i : ℕ) (ω : Fin 3 → X × ℕ → ℝ) : ℝ := ω b (x, i)

lemma measurable_tapeξ (b : Fin 3) (x : X) (i : ℕ) : Measurable (tapeξ b x i) :=
  (measurable_pi_apply (x, i)).comp (measurable_pi_apply b)

lemma tapeξ_iIndepFun (b : Fin 3) :
    iIndepFun (fun q : X × ℕ => tapeξ b q.1 q.2) (tapeP X) := by
  have h := iIndepFun_uncurry_infinitePi' (X := fun (_ : Fin 3) (_ : X × ℕ) (x : ℝ) => x)
    (fun (_ : Fin 3) (_ : X × ℕ) => gaussianReal 0 1) (fun _ _ => measurable_id)
  exact h.precomp (g := fun q : X × ℕ => (b, q)) (fun a c hac => by simpa using hac)

lemma tapeξ_hasLaw (b : Fin 3) (x : X) (i : ℕ) :
    HasLaw (tapeξ b x i) (gaussianReal 0 1) (tapeP X) := by
  refine ⟨(measurable_tapeξ b x i).aemeasurable, ?_⟩
  have h : (tapeξ b x i : (Fin 3 → X × ℕ → ℝ) → ℝ) =
      (fun f : X × ℕ → ℝ => f (x, i)) ∘ (fun ω => ω b) := rfl
  rw [h, ← Measure.map_map (measurable_pi_apply _) (measurable_pi_apply _), tapeP,
    Measure.infinitePi_map_eval,
    Measure.infinitePi_map_eval (fun _ : X × ℕ => gaussianReal 0 1) (x, i)]

lemma measurable_curryTape :
    Measurable (fun f : X × ℕ → ℝ => fun (x : X) (i : ℕ) => f (x, i)) :=
  measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i => measurable_pi_apply (x, i)

lemma tape_coord_iIndepFun :
    iIndepFun (fun (b : Fin 3) (ω : Fin 3 → X × ℕ → ℝ) => ω b) (tapeP X) :=
  iIndepFun_infinitePi (P := fun _ : Fin 3 => Measure.infinitePi
    (fun _ : X × ℕ => gaussianReal 0 1)) (X := fun _ x => x) (fun _ => measurable_id)

/-- Two distinct tapes are independent. -/
lemma tapeξ_indep {b c : Fin 3} (hbc : b ≠ c) :
    IndepFun (fun (ω : Fin 3 → X × ℕ → ℝ) x i => tapeξ b x i ω)
      (fun (ω : Fin 3 → X × ℕ → ℝ) x i => tapeξ c x i ω) (tapeP X) :=
  (tape_coord_iIndepFun.indepFun hbc).comp measurable_curryTape measurable_curryTape

/-- The pair (pilot tape, confirmation tape) is independent of the safeguard tape. -/
lemma tapeξ_indep_pair :
    IndepFun (fun (ω : Fin 3 → X × ℕ → ℝ) =>
        ((fun x i => tapeξ 0 x i ω : X → ℕ → ℝ), (fun x i => tapeξ 1 x i ω : X → ℕ → ℝ)))
      (fun (ω : Fin 3 → X × ℕ → ℝ) x i => tapeξ 2 x i ω) (tapeP X) :=
  (tape_coord_iIndepFun.indepFun_prodMk (fun _ => measurable_pi_apply _) 0 1 2
    (by decide) (by decide)).comp (measurable_curryTape.prodMap measurable_curryTape)
    measurable_curryTape

end Space

/-! ### An oracle meeting the contract `eq:v10g-oracle` with measurable outputs -/

section Oracle

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {𝒜 : Type*}

lemma measurable_gInfo_center (u : X → E) (Q : Set E) (w : X → ℝ) :
    Measurable (fun v : E => gInfo u Q v w) := by
  have h1 : Continuous (fun v : E => rootInfo (designMap u w) Q v) := by
    unfold rootInfo
    exact (Metric.continuous_infDist_pt _).comp
      (LinearMap.continuous_of_finiteDimensional (designMap u w))
  unfold gInfo
  exact ((h1.pow 2).div_const 2).measurable

/-- **The oracle contract is satisfiable with Borel outputs.**  For every floor `k ∈ (0, 1]`
and positive tolerances `e j`, there is an oracle meeting `eq:v10g-oracle` whose design and
lower endpoint are Borel functions of the center.  (The oracle scans a countable dense
sequence of designs using exact values; this shows satisfiability and is not the
manuscript's finite computation.) -/
theorem exists_oracle [Fintype 𝒜] [Nonempty 𝒜] (u : X → E) (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k : ℝ} (hk0 : 0 ≤ k)
    (hk1 : k ≤ 1) {e : ℕ → ℝ} (he : ∀ j, 0 < e j) :
    ∃ (oa : ℕ → E → 𝒜) (ow : ℕ → E → X → ℝ) (ol ou : ℕ → E → ℝ),
      OracleContract u Q w0 k e oa ow ol ou ∧ (∀ j, Measurable (ol j)) ∧
        ∀ j x, Measurable (fun v => ow j v x) := by
  classical
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hw0.2
    simp at this
  obtain ⟨d, hd, hdense⟩ := GaussTrack.exists_dense_simplex hw0
  obtain ⟨ℓ, hℓ, hu⟩ := exists_feature_bound u
  choose lamA hlamA using hQ
  -- values on the sequence and their supremum
  let gv : 𝒜 × ℕ → E → ℝ := fun i v => gInfo u (Q i.1) v (floorDesign k w0 (d i.2))
  let S : E → ℝ := fun v => ⨆ i, gv i v
  have hfl : ∀ p ∈ simplex X, floorDesign k w0 p ∈ simplex X := fun p hp =>
    floorDesign_mem hk0 hk1 hw0 hp
  have hbdd : ∀ v, BddAbove (Set.range fun i => gv i v) := by
    intro v
    refine ⟨ℓ ^ 2 * (‖v‖ + ∑ a, ‖lamA a‖) ^ 2 / 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact info_le_anchor u (hfl _ (hd i.2)) hℓ.le hu (hlamA i.1)
      (Finset.single_le_sum (f := fun a => ‖lamA a‖) (fun a _ => norm_nonneg _) (mem_univ i.1))
      le_rfl
  have hle : ∀ i v, gv i v ≤ S v := fun i v => le_ciSup (hbdd v) i
  have hgvm : ∀ i, Measurable (gv i) := fun i => measurable_gInfo_center u _ _
  have hSm : Measurable S := Measurable.iSup hgvm
  -- the supremum dominates every floored design
  have hsup : ∀ v a, ∀ p ∈ simplex X, gInfo u (Q a) v (floorDesign k w0 p) ≤ S v := by
    intro v a p hp
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hc := continuousOn_gInfo u ⟨lamA a, hlamA a⟩ v
    rw [Metric.continuousOn_iff] at hc
    obtain ⟨δ, hδ, hcδ⟩ := hc _ (hfl p hp) ε hε
    obtain ⟨n, hn⟩ := hdense p hp (δ / 2) (by positivity)
    have hdist : dist (floorDesign k w0 (d n)) (floorDesign k w0 p) < δ := by
      rw [dist_pi_lt_iff hδ]
      intro x
      rw [Real.dist_eq]
      have e1 : floorDesign k w0 (d n) x - floorDesign k w0 p x = (1 - k) * (d n x - p x) := by
        simp only [floorDesign]
        ring
      rw [e1, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - k)]
      have h1 : (1 - k) * |d n x - p x| ≤ 1 * |d n x - p x| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      linarith [hn x]
    have h2 := hcδ _ (hfl _ (hd n)) hdist
    rw [Real.dist_eq] at h2
    have h3 := (abs_lt.mp h2).1
    have h4 := hle (a, n) v
    show gInfo u (Q a) v (floorDesign k w0 p) < S v + ε
    have h5 : gv (a, n) v = gInfo u (Q a) v (floorDesign k w0 (d n)) := rfl
    linarith
  -- a near-maximal index
  have hex : ∀ j v, ∃ n, ∃ a, S v - e j ^ 2 ≤ gv (a, n) v := by
    intro j v
    have hlt : S v - e j ^ 2 < S v := by
      have := pow_pos (he j) 2
      linarith
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hlt
    exact ⟨i.2, i.1, hi.le⟩
  have hnm : ∀ j, Measurable (fun v => Nat.find (hex j v)) := fun j =>
    measurable_find _ fun n => by
      have : {v | ∃ a, S v - e j ^ 2 ≤ gv (a, n) v} = ⋃ a, {v | S v - e j ^ 2 ≤ gv (a, n) v} := by
        ext v; simp
      rw [this]
      exact MeasurableSet.iUnion fun a => measurableSet_le (hSm.sub_const _) (hgvm _)
  refine ⟨fun j v => Classical.choose (Nat.find_spec (hex j v)),
    fun j v => floorDesign k w0 (d (Nat.find (hex j v))),
    fun j v => max 0 (S v - e j ^ 2), fun j v => S v, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun j v => ⟨_, hd _, rfl⟩
  · exact fun j v => le_max_left _ _
  · exact fun j v => max_le gInfo_nonneg (Classical.choose_spec (Nat.find_spec (hex j v)))
  · exact fun j v a p hp => hsup v a p hp
  · intro j v
    have := le_max_right 0 (S v - e j ^ 2)
    linarith
  · exact fun j => measurable_const.max (hSm.sub_const _)
  · intro j x
    exact Measurable.comp (g := fun n : ℕ => floorDesign k w0 (d n) x)
      Measurable.of_discrete (hnm j)

/-- Exact values are admissible safeguard enclosures: the action distances are measurable
functions of the tape. -/
lemma measurable_exactJ (u : X → E) (Q : Set E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k0 : ℝ}
    (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (n : ℕ) :
    Measurable (fun Y : X → ℕ → ℝ => gInfo u Q (olsCount u (roundCount w0 n) Y)
      (fun x => (roundCount w0 n x : ℝ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc : roundCount w0 ((0 : ℕ) : ℝ) = fun _ => 0 := by
      funext x
      simp [roundCount]
    rw [hc]
    have hconst : ∀ Y : X → ℕ → ℝ, olsCount u (fun _ => 0) Y =
        olsCount u (fun _ => 0) (fun _ _ => 0) := by
      intro Y
      unfold olsCount olsEst
      congr 1
      rw [Fintype.sum_empty, Fintype.sum_empty]
    simp_rw [hconst]
    exact measurable_const
  · exact (measurable_gInfo_center u Q _).comp (measurable_olsCount u _
      (round_gram_injective u hw0.1 hk0 hM0 (by exact_mod_cast hn)))

end Oracle

/-! ### The results on the tape space, with `C = I_*(θ)` and `C₀ = max_a I_a(θ, w⁰)` -/

section Final

variable {X : Type uX} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {𝒜 : Type*} [Fintype 𝒜] [Nonempty 𝒜]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- The stopping time of the procedure on the tape space under the parameter `θ`: tape `0`
feeds the pilot, tape `1` the confirmation stream, tape `2` the safeguard. -/
noncomputable def FCProc.tauΩ (p : FCProc X E 𝒜) (θ : E) (ω : Fin 3 → X × ℕ → ℝ) : ℝ≥0∞ :=
  p.tau (obsTape p.u θ (tapeξ 0) ω) (obsTape p.u θ (tapeξ 1) ω) (obsTape p.u θ (tapeξ 2) ω)

/-- The returned action of the procedure on the tape space under the parameter `θ`. -/
noncomputable def FCProc.retΩ (p : FCProc X E 𝒜) (θ : E) (ω : Fin 3 → X × ℕ → ℝ) : Option 𝒜 :=
  p.ret (obsTape p.u θ (tapeξ 0) ω) (obsTape p.u θ (tapeξ 1) ω) (obsTape p.u θ (tapeξ 2) ω)

omit [Fintype 𝒜] [Nonempty 𝒜] in
/-- **Safety on the tape space**, for any procedure meeting `Spec`:
`P_θ(τ < ∞, regret of the returned action > ε) ≤ δ` for every `θ`.  No independence
hypothesis. -/
theorem FCProc.safe_tape (p : FCProc X E 𝒜) (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ) (hw0 : p.w0 ∈ simplex X) {ℓ k0 α δ : ℝ}
    (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap p.u p.w0 v‖ ^ 2)
    (hk : 0 < p.k) (hk1 : p.k ≤ 1)
    (hS : p.Spec (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 α δ)
    (θ : E) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    tapeP X {ω | p.tauΩ θ ω < ⊤ ∧ ∃ a, p.retΩ θ ω = some a ∧
      ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal δ :=
  p.safe φ supp hne ε hw0 hk0 hM0 hk hk1 hS (measurable_tapeξ 0) (measurable_tapeξ 1)
    (tapeξ_iIndepFun 1) (tapeξ_hasLaw 1) (tapeξ_iIndepFun 2) (tapeξ_hasLaw 2)
    (tapeξ_indep (by decide)) θ hδ0 hδ1

/-- **The expectation bound on the tape space** (`eq:v10g-finite`) with the manuscript's
constants `C = I_*(θ)` and `C₀ = max_a I_a(θ, w⁰)`, for any procedure meeting `Spec`:
`E_θ τ ≤ min {𝓑_δ, H_δ / k + 1}`. -/
theorem FCProc.expectation_tape (p : FCProc X E 𝒜) (Q : 𝒜 → Set E)
    (hQ : ∀ a, (Q a).Nonempty) (hw0 : p.w0 ∈ simplex X) {ℓ k0 α δ : ℝ}
    (hℓ : 0 < ℓ) (hu : ∀ x, ‖p.u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap p.u p.w0 v‖ ^ 2)
    (hk : 0 < p.k) (hk1 : p.k < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : p.Spec Q ℓ k0 α δ) (θ : E) (hI : 0 < IstarG p.u Q θ) :
    ∫⁻ ω, p.tauΩ θ ω ∂(tapeP X) ≤
      ENNReal.ofReal (min
        (Bdelta (Dbar (pilotA ℓ k0 p.k (IstarG p.u Q θ)) (Module.finrank ℝ E) α (Fintype.card X))
          (logBudget (aC (Module.finrank ℝ E) p.k (cstar p.k * IstarG p.u Q θ) δ α)
            (bC p.k (cstar p.k * IstarG p.u Q θ)))
          (Fintype.card X) p.k α
          (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ (C0G p.u Q θ p.w0)))
        (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ (C0G p.u Q θ p.w0) / p.k + 1)) := by
  obtain ⟨aS, wS, hwS, heq, -⟩ := exists_IstarG_max p.u Q hQ θ hw0
  obtain ⟨a0, h0eq, -⟩ := exists_C0G_max p.u Q θ p.w0
  have hC0 : 0 < C0G p.u Q θ p.w0 :=
    lt_of_lt_of_le (by positivity) (C0G_ge p.u Q hQ θ hw0 hℓ hu hk0.le hM0)
  exact p.expectation Q hQ hw0 hℓ hu hk0 hM0 hk hk1 hα0 hα1 hδ0 hδ1 hS
    (measurable_tapeξ 0) (measurable_tapeξ 1) (measurable_tapeξ 2)
    (tapeξ_iIndepFun 0) (tapeξ_hasLaw 0) (tapeξ_iIndepFun 1) (tapeξ_hasLaw 1)
    (tapeξ_iIndepFun 2) (tapeξ_hasLaw 2) (tapeξ_indep (by decide)) tapeξ_indep_pair θ aS hwS hI
    heq.ge a0 hC0 h0eq.ge

lemma pilotRho_pos {d k0 α : ℝ} (hd : 0 ≤ d) (hk0 : 0 < k0) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (j : ℕ) : 0 < pilotRho d k0 α j := by
  unfold pilotRho
  apply Real.sqrt_pos.mpr
  have hu : 0 < pilotU α j := by
    unfold pilotU
    apply Real.log_pos
    rw [lt_div_iff₀ hα0]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hψ : 0 < psiD d (pilotU α j) := by
    unfold psiD
    have := Real.sqrt_nonneg (d * pilotU α j)
    linarith [div_nonneg hd (by norm_num : (0 : ℝ) ≤ 2)]
  positivity

/-- The procedure with a given oracle and exact enclosures: `Z̲_n = Z_n`,
`B̄_n = B(n, δ/2)`, and exact safeguard distances.  These satisfy the manuscript's
enclosure requirements (`exactProc_spec`). -/
noncomputable def exactProc (u : X → E) (Q : 𝒜 → Set E) (w0 : X → ℝ) (k : ℝ) (e : ℕ → ℝ)
    (oa : ℕ → E → 𝒜) (ow : ℕ → E → X → ℝ) (ol : ℕ → E → ℝ) (δ : ℝ) : FCProc X E 𝒜 where
  u := u
  w0 := w0
  k := k
  e := e
  oa := oa
  ow := ow
  ol := ol
  Zlow := fun j y y' n => confirmZ u (ow j (pilotV u w0 y j)) (pilotV u w0 y j)
    (ol j (pilotV u w0 y j)) y' n
  Bbar := fun n => boundary (Module.finrank ℝ E) n (δ / 2)
  Jlow := fun n Y a => gInfo u (Q a) (olsCount u (roundCount w0 n) Y)
    (fun x => (roundCount w0 n x : ℝ))

omit [Fintype 𝒜] [Nonempty 𝒜] in
lemma exactProc_spec (u : X → E) (Q : 𝒜 → Set E) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X)
    {ℓ k0 k α δ : ℝ} (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2)
    {e : ℕ → ℝ} {oa : ℕ → E → 𝒜} {ow : ℕ → E → X → ℝ} {ol ou : ℕ → E → ℝ}
    (he1 : ∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j)
    (he2 : ∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j)
    (hor : OracleContract u Q w0 k e oa ow ol ou) (hol : ∀ j, Measurable (ol j))
    (how : ∀ j x, Measurable (fun v => ow j v x)) :
    (exactProc u Q w0 k e oa ow ol δ).Spec Q ℓ k0 α δ where
  he1 := he1
  he2 := he2
  contract := ⟨ou, hor⟩
  hol := hol
  how := how
  hZlo := fun j y y' n => by
    show max 0 (confirmZ u _ _ _ y' n - 1) ≤ confirmZ u _ _ _ y' n
    refine max_le ?_ (sub_le_self _ zero_le_one)
    unfold confirmZ
    positivity
  hZup := fun j y y' n => le_rfl
  hBlo := fun n => le_rfl
  hBup := fun n => le_add_of_nonneg_right zero_le_one
  hJm := fun n a => measurable_exactJ u (Q a) hw0 hk0 hM0 n
  hJlo := fun n Y a => sub_le_self _ zero_le_one
  hJup := fun n Y a => le_rfl

/-- A family of oracles, one for each tolerance sequence, meeting the contract with Borel
outputs whenever the tolerances are positive. -/
lemma exists_oracle_family (u : X → E) (Q : 𝒜 → Set E) (hQ : ∀ a, (Q a).Nonempty)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    ∃ (oa : (ℕ → ℝ) → ℕ → E → 𝒜) (ow : (ℕ → ℝ) → ℕ → E → X → ℝ) (ol : (ℕ → ℝ) → ℕ → E → ℝ),
      ∀ e : ℕ → ℝ, (∀ j, 0 < e j) →
        (∃ ou, OracleContract u Q w0 k e (oa e) (ow e) (ol e) ou) ∧
          (∀ j, Measurable (ol e j)) ∧ ∀ j x, Measurable (fun v => ow e j v x) := by
  classical
  have h : ∀ e : ℕ → ℝ, ∃ (oa : ℕ → E → 𝒜) (ow : ℕ → E → X → ℝ) (ol : ℕ → E → ℝ),
      (∀ j, 0 < e j) → (∃ ou, OracleContract u Q w0 k e oa ow ol ou) ∧
        (∀ j, Measurable (ol j)) ∧ ∀ j x, Measurable (fun v => ow j v x) := by
    intro e
    by_cases he : ∀ j, 0 < e j
    · obtain ⟨oa, ow, ol, ou, hor, h1, h2⟩ := exists_oracle u Q hQ hw0 hk0 hk1 he
      exact ⟨oa, ow, ol, fun _ => ⟨⟨ou, hor⟩, h1, h2⟩⟩
    · exact ⟨fun _ _ => Classical.arbitrary 𝒜, fun _ _ => w0, fun _ _ => 0,
        fun h => absurd h he⟩
  choose oa ow ol hspec using h
  exact ⟨oa, ow, ol, hspec⟩

omit [MeasurableSpace E] [BorelSpace E] [Fintype 𝒜] [Nonempty 𝒜] [FiniteDimensional ℝ E] in
lemma tol_pos {ℓ k0 α : ℝ} {d : ℕ} (hℓ : 0 < ℓ) (hk0 : 0 < k0) (hα0 : 0 < α) (hα1 : α ≤ 1)
    {e : ℕ → ℝ} (he1 : ∀ j, ℓ * pilotRho d k0 α j / Real.sqrt 2 ≤ e j) (j : ℕ) : 0 < e j := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have := pilotRho_pos (Nat.cast_nonneg d) hk0 hα0 hα1 j
  exact lt_of_lt_of_le (by positivity) (he1 j)

/-- **Correlated finite-confidence discovery and confirmation** (`thm:v10g-expectation`),
as written, on the tape space, with the oracle constructed.

Model: finitely many queries with features `u_x`, `‖u_x‖ ≤ ℓ`; a reference design `w⁰` with
`M(w⁰) ⪰ k₀ I`; finitely many root actions with nonempty supports, each with a strict
`ε`-invalidating alternative (the manuscript's "remaining branch").  The procedure is
`exactProc` with calendar share `k ∈ (0, 1)`, tolerances `e` in the manuscript's range for
the pilot risk `α`, and the constructed oracle.

Conclusions, for one and the same procedure: it meets the manuscript's requirements
(`Spec`); it is `(ε, δ)`-safe at every parameter; and at every `θ` with `I_*(θ) > 0`,
`E_θ τ ≤ min {𝓑_δ, H_δ / k + 1}` with `C = I_*(θ)` and `C₀ = max_a I_a(θ, w⁰)`.
The procedure does not depend on `θ`. -/
theorem v10g_expectation_literal (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {ℓ k0 k : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k < 1) :
    ∃ (oa : (ℕ → ℝ) → ℕ → E → 𝒜) (ow : (ℕ → ℝ) → ℕ → E → X → ℝ) (ol : (ℕ → ℝ) → ℕ → E → ℝ),
      ∀ (δ α : ℝ) (e : ℕ → ℝ), 0 < δ → δ ≤ 1 → 0 < α → α ≤ 1 →
        (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j) →
        (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j) →
        (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e (oa e) (ow e) (ol e) δ).Spec
            (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 α δ ∧
        (∀ θ : E, tapeP X {ω |
            (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e (oa e) (ow e) (ol e)
              δ).tauΩ θ ω < ⊤ ∧
            ∃ a, (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e (oa e) (ow e)
              (ol e) δ).retΩ θ ω = some a ∧ ε < regret (supp a) (hne a) (env φ θ)} ≤
          ENNReal.ofReal δ) ∧
        ∀ θ : E, 0 < IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
          ∫⁻ ω, (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e (oa e) (ow e)
              (ol e) δ).tauΩ θ ω ∂(tapeP X) ≤
            ENNReal.ofReal (min
              (Bdelta
                (Dbar (pilotA ℓ k0 k (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ))
                  (Module.finrank ℝ E) α (Fintype.card X))
                (logBudget (aC (Module.finrank ℝ E) k
                    (cstar k * IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) δ α)
                  (bC k (cstar k * IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)))
                (Fintype.card X) k α
                (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ
                  (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)))
              (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ
                (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0) / k + 1)) := by
  obtain ⟨oa, ow, ol, hfam⟩ := exists_oracle_family u
    (fun a => strictAlt φ (supp a) (hne a) ε) hQ hw0 hk.le hk1.le
  refine ⟨oa, ow, ol, fun δ α e hδ0 hδ1 hα0 hα1 he1 he2 => ?_⟩
  obtain ⟨⟨ou, hor⟩, hol, how⟩ := hfam e (tol_pos hℓ hk0 hα0 hα1 he1)
  have hS := exactProc_spec u (fun a => strictAlt φ (supp a) (hne a) ε) hw0 (δ := δ) hk0 hM0
    he1 he2 hor hol how
  refine ⟨hS, fun θ => ?_, fun θ hI => ?_⟩
  · exact FCProc.safe_tape
      (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e (oa e) (ow e) (ol e) δ)
      φ supp hne ε hw0 hk0 hM0 hk hk1.le hS θ hδ0 hδ1
  · exact FCProc.expectation_tape
      (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 k e (oa e) (ow e) (ol e) δ)
      (fun a => strictAlt φ (supp a) (hne a) ε) hQ hw0 hℓ hu hk0 hM0 hk hk1 hα0 hα1 hδ0 hδ1
      hS θ hI

/-- `D(θ, G, ε, s) = (D₀ + q) / (1 - k)` of `eq:v10g-target`, `k = s / 16`; `I` stands for
`I_*(θ)`.  It does not involve `δ`. -/
noncomputable def Dconst (ℓ k0 s I d q : ℝ) : ℝ :=
  (D0 (pilotA ℓ k0 (s / 16) I) d q + q) / (1 - s / 16)

/-- The remainder `R₁₀` of `eq:v10g-remainder` for the instance constants. -/
noncomputable def Rrem (ℓ k0 s I C0 d q δ J : ℝ) : ℝ :=
  R10 (Dextra (pilotA ℓ k0 (s / 16) I) d J)
    (rC d (s / 16) (cstar (s / 16) * I) (1 / (8 * J ^ 2)))
    (2 * bC (s / 16) (cstar (s / 16) * I) *
      Real.log (aC d (s / 16) (cstar (s / 16) * I) δ (1 / (8 * J ^ 2)) +
        bC (s / 16) (cstar (s / 16) * I) + 1))
    (s / 16) J (Hdelta q d δ C0)

/-- **Finite-confidence discovery, frozen confirmation, and safeguard** (`prop:bay-finite`,
`eq:bay-finite-main`) and **`cor:v10g-target`** (`eq:v10g-target`, `eq:v10g-remainder`), as
written, on the tape space, with the oracle constructed.

For prescribed `s ∈ (0, 1]` the procedure is `exactProc` with `k = s / 16`, pilot risk
`α = 1 / (8 J²)` and the constructed oracle; it does not depend on `θ`.

(1) For every `δ ∈ (0, 1]`, `J ≥ 1` and tolerances in the manuscript's range, the procedure
meets `Spec` and is `(ε, δ)`-safe at every parameter.

(2) At every `θ` with `I_*(θ) > 0` there is `K` (depending on the instance and `s`, not on
`δ`) such that for all `δ ∈ (0, 1/4]` and `1 + log(1/δ) ≤ J < 3 + log(1/δ)`:
`E_θ τ ≤ D + (1 + s) I_*(θ)⁻¹ log(1/δ) + R` and `R ≤ K (1 + log log(1/δ))`, where
`D = Dconst` does not involve `δ` and `R = Rrem` is `R₁₀`. -/
theorem bay_finite_literal (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {ℓ k0 s : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ (oa : (ℕ → ℝ) → ℕ → E → 𝒜) (ow : (ℕ → ℝ) → ℕ → E → X → ℝ) (ol : (ℕ → ℝ) → ℕ → E → ℝ),
      (∀ (δ J : ℝ) (e : ℕ → ℝ), 0 < δ → δ ≤ 1 → 1 ≤ J →
        (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j / Real.sqrt 2 ≤ e j) →
        (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j) →
        (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) e (oa e) (ow e)
            (ol e) δ).Spec (fun a => strictAlt φ (supp a) (hne a) ε) ℓ k0 (1 / (8 * J ^ 2)) δ ∧
        ∀ θ : E, tapeP X {ω |
            (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) e (oa e) (ow e)
              (ol e) δ).tauΩ θ ω < ⊤ ∧
            ∃ a, (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) e (oa e)
              (ow e) (ol e) δ).retΩ θ ω = some a ∧ ε < regret (supp a) (hne a) (env φ θ)} ≤
          ENNReal.ofReal δ) ∧
      ∀ θ : E, 0 < IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
        ∃ K : ℝ, ∀ (δ J : ℝ) (e : ℕ → ℝ), 0 < δ → δ ≤ 1 / 4 → 1 + Real.log (1 / δ) ≤ J →
          J < 3 + Real.log (1 / δ) →
          (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j / Real.sqrt 2 ≤ e j) →
          (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 (1 / (8 * J ^ 2)) j) →
          ∫⁻ ω, (exactProc u (fun a => strictAlt φ (supp a) (hne a) ε) w0 (s / 16) e (oa e)
              (ow e) (ol e) δ).tauΩ θ ω ∂(tapeP X) ≤
            ENNReal.ofReal
              (Dconst ℓ k0 s (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                  (Module.finrank ℝ E) (Fintype.card X) +
                (1 + s) * (1 / IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) *
                  Real.log (1 / δ) +
                Rrem ℓ k0 s (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
                  (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)
                  (Module.finrank ℝ E) (Fintype.card X) δ J) ∧
          Rrem ℓ k0 s (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ)
              (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)
              (Module.finrank ℝ E) (Fintype.card X) δ J ≤
            K * (1 + Real.log (Real.log (1 / δ))) := by
  have hk : 0 < s / 16 := by positivity
  have hk1 : s / 16 < 1 := by linarith
  obtain ⟨oa, ow, ol, hmain⟩ := v10g_expectation_literal φ supp hne ε hQ u hw0 hℓ hu hk0 hM0
    hk hk1
  have hα : ∀ J : ℝ, 1 ≤ J → 0 < 1 / (8 * J ^ 2) ∧ 1 / (8 * J ^ 2) ≤ 1 := by
    intro J hJ
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    nlinarith
  refine ⟨oa, ow, ol, fun δ J e hδ0 hδ1 hJ he1 he2 => ?_, fun θ hI => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hmain δ (1 / (8 * J ^ 2)) e hδ0 hδ1 (hα J hJ).1 (hα J hJ).2 he1 he2
    exact ⟨h1, h2⟩
  · have hC0 : 0 < C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0 :=
      lt_of_lt_of_le (by positivity) (C0G_ge u _ hQ θ hw0 hℓ hu hk0.le hM0)
    have hA : 0 ≤ pilotA ℓ k0 (s / 16)
        (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ) := by
      have : 0 < 1 - s / 16 := by linarith
      unfold pilotA
      positivity
    have hcs : 0 < cstar (s / 16) := by
      have : 0 < 1 - s / 16 := by linarith
      unfold cstar
      positivity
    obtain ⟨K, hK⟩ := R10_order (A := pilotA ℓ k0 (s / 16)
        (IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ))
      (d := (Module.finrank ℝ E : ℝ)) (q := (Fintype.card X : ℝ))
      hA (Nat.cast_nonneg _) hk hk1 (mul_pos hcs hI) (Nat.cast_nonneg _) hC0
    refine ⟨K, fun δ J e hδ0 hδ4 hJ1 hJ2 he1 he2 => ⟨?_, hK δ J hδ0 hδ4 hJ1 hJ2⟩⟩
    have hδ1 : δ ≤ 1 := by linarith
    have hJ : 1 ≤ J := by
      have := Real.log_nonneg ((one_le_div hδ0).mpr hδ1)
      linarith
    obtain ⟨-, -, h3⟩ := hmain δ (1 / (8 * J ^ 2)) e hδ0 hδ1 (hα J hJ).1 (hα J hJ).2 he1 he2
    refine (h3 θ hI).trans (ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans ?_))
    exact target_bound hs0 hs1 hI hδ0 hδ1 hJ hA (Nat.cast_nonneg _)

/-- **Explicit discovery and a frozen near-optimal plan** (`thm:v10g-discovery`), as
written, on the tape space, with the oracle constructed and `C = I_*(θ)`.  For every pilot
risk `α ∈ (0, 1]` and tolerances in the manuscript's range, at every `θ` with `I_*(θ) > 0`:
except on an event of probability at most `α` every pilot estimate obeys
`‖v_j - θ‖ ≤ ρ_j`; and on that event the pilot commits at a stage `j`, the frozen record
satisfies `eq:v10g-plan-rate`, and the pilot used at most `D̄` observations. -/
theorem v10g_discovery_literal (u : X → E) (Q : 𝒜 → Set E) (hQ : ∀ a, (Q a).Nonempty)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {ℓ k0 k : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ)
    (hk0 : 0 < k0) (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k)
    (hk1 : k < 1) :
    ∃ (oa : (ℕ → ℝ) → ℕ → E → 𝒜) (ow : (ℕ → ℝ) → ℕ → E → X → ℝ) (ol : (ℕ → ℝ) → ℕ → E → ℝ),
      ∀ (α : ℝ) (e : ℕ → ℝ), 0 < α → α ≤ 1 →
        (∀ j, ℓ * pilotRho (Module.finrank ℝ E) k0 α j / Real.sqrt 2 ≤ e j) →
        (∀ j, e j ≤ Real.sqrt 2 * ℓ * pilotRho (Module.finrank ℝ E) k0 α j) →
        (∃ ou, OracleContract u Q w0 k e (oa e) (ow e) (ol e) ou) ∧
        ∀ θ : E, 0 < IstarG u Q θ →
          tapeP X {ω | ¬ ∀ j : ℕ, ‖pilotV u w0 (obsTape u θ (tapeξ 0) ω) j - θ‖ ≤
            pilotRho (Module.finrank ℝ E) k0 α j} ≤ ENNReal.ofReal α ∧
          ∀ ω : Fin 3 → X × ℕ → ℝ,
            (∀ j : ℕ, ‖pilotV u w0 (obsTape u θ (tapeξ 0) ω) j - θ‖ ≤
              pilotRho (Module.finrank ℝ E) k0 α j) →
            ∃ j, commitAt e k (ol e) (pilotV u w0 (obsTape u θ (tapeξ 0) ω)) j ∧
              cstar k * IstarG u Q θ ≤
                (Real.sqrt (ol e j (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j)) - e j) ^ 2 ∧
              (Real.sqrt (ol e j (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j)) - e j) ^ 2 ≤
                gInfo u (Q (oa e j (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j))) θ
                  (ow e j (pilotV u w0 (obsTape u θ (tapeξ 0) ω) j)) ∧
              (∑ x, (roundCount w0 (2 ^ j) x : ℝ)) ≤
                Dbar (pilotA ℓ k0 k (IstarG u Q θ)) (Module.finrank ℝ E) α (Fintype.card X) := by
  obtain ⟨oa, ow, ol, hfam⟩ := exists_oracle_family u Q hQ hw0 hk.le hk1.le
  refine ⟨oa, ow, ol, fun α e hα0 hα1 he1 he2 => ?_⟩
  obtain ⟨⟨ou, hor⟩, -, -⟩ := hfam e (tol_pos hℓ hk0 hα0 hα1 he1)
  refine ⟨⟨ou, hor⟩, fun θ hI => ?_⟩
  obtain ⟨aS, wS, hwS, heq, -⟩ := exists_IstarG_max u Q hQ θ hw0
  obtain ⟨h1, h2⟩ := v10g_discovery u Q hQ hw0 hℓ hu hk0 hM0 hk hk1 hα0 hα1 he1 he2 hor
    (tapeξ_iIndepFun 0) (tapeξ_hasLaw 0) θ aS hwS hI heq.ge
  refine ⟨h1, fun ω hω => ?_⟩
  obtain ⟨j, hg, hmin, hr1, hr2, hD⟩ := h2 ω hω
  exact ⟨j, ⟨hg, hmin⟩, hr1, hr2, hD⟩

/-- **Conditional safety and a finite-mean reference design**
(`prop:v10g-safety-fallback`), as written, on the tape space, with exact enclosures.

(1) For every frozen record (action `a`, design `(1 - k) p + k w⁰`, center `v`, number
`l ≤ I_a(v, w)`), i.e. conditionally on every finite pilot history, the confirmation branch
on its fresh tape certifies an action of regret above `ε` with probability at most `δ/2`,
at every parameter.
(2) The reference safeguard certifies an action of regret above `ε` with probability at
most `δ/2`, at every parameter.
(3) At every `θ` with `I_*(θ) > 0`, `E_θ F_δ ≤ H_δ` with `C₀ = max_a I_a(θ, w⁰)`. -/
theorem safety_fallback_literal (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) (u : X → E) {w0 : X → ℝ}
    (hw0 : w0 ∈ simplex X) {ℓ k0 k δ : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, ‖u x‖ ≤ ℓ) (hk0 : 0 < k0)
    (hM0 : ∀ v, k0 * ‖v‖ ^ 2 ≤ ‖designMap u w0 v‖ ^ 2) (hk : 0 < k) (hk1 : k ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∀ (θ : E) (a : 𝒜) (p : X → ℝ), p ∈ simplex X → ∀ (v : E) (l : ℝ),
        l ≤ gInfo u (strictAlt φ (supp a) (hne a) ε) v (floorDesign k w0 p) →
        tapeP X {ω | ∃ n : ℕ, 1 ≤ n ∧ boundary (Module.finrank ℝ E) n (δ / 2) ≤
            confirmZ u (floorDesign k w0 p) v l (obsTape u θ (tapeξ 1) ω) n ∧
          ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal (δ / 2)) ∧
    (∀ θ : E, tapeP X {ω | ∃ n : ℕ, 1 ≤ n ∧ ∃ a, boundary (Module.finrank ℝ E) n (δ / 2) ≤
          gInfo u (strictAlt φ (supp a) (hne a) ε)
            (olsCount u (roundCount w0 n) (obsTape u θ (tapeξ 2) ω))
            (fun x => (roundCount w0 n x : ℝ)) ∧
        ε < regret (supp a) (hne a) (env φ θ)} ≤ ENNReal.ofReal (δ / 2)) ∧
    ∀ θ : E, 0 < IstarG u (fun a => strictAlt φ (supp a) (hne a) ε) θ →
      ∫⁻ ω, roundTotal w0 (firstTime (sgStop
          (fun n Y a => gInfo u (strictAlt φ (supp a) (hne a) ε)
            (olsCount u (roundCount w0 n) Y) (fun x => (roundCount w0 n x : ℝ)))
          (fun n => boundary (Module.finrank ℝ E) n (δ / 2))
          (obsTape u θ (tapeξ 2) ω))) ∂(tapeP X) ≤
        ENNReal.ofReal (Hdelta (Fintype.card X) (Module.finrank ℝ E) δ
          (C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0)) := by
  refine ⟨fun θ a p hp v l hl => ?_, fun θ => ?_, fun θ hI => ?_⟩
  · exact confirm_safe_fixed φ supp hne ε u hw0 hk0 hM0 hk hk1 (tapeξ_iIndepFun 1)
      (tapeξ_hasLaw 1) θ hδ0 hδ1 (fun n => le_rfl) a hp v hl
  · exact safeguard_safe φ supp hne ε u hw0 hk0 hM0 (tapeξ_iIndepFun 2) (tapeξ_hasLaw 2) θ
      hδ0 hδ1 (fun n Y a => le_rfl) (fun n => le_rfl)
  · obtain ⟨a0, h0eq, -⟩ := exists_C0G_max u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0
    have hC0 : 0 < C0G u (fun a => strictAlt φ (supp a) (hne a) ε) θ w0 :=
      lt_of_lt_of_le (by positivity) (C0G_ge u _ hQ θ hw0 hℓ hu hk0.le hM0)
    exact safeguard_mean u _ hQ hw0 hk0 hM0 (tapeξ_iIndepFun 2) (tapeξ_hasLaw 2)
      (measurable_tapeξ 2) θ hδ0 hδ1 a0 hC0 h0eq.ge
      (fun n a => measurable_exactJ u _ hw0 hk0 hM0 n)
      (fun n Y a => by linarith) (fun n => by linarith)

end Final

/-! ### The zero-observation hull screen -/

section Screen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **Universal answers** (`app:bay-finite`: "universal answers are returned by the existing
zero-observation screen").  If the hull screen of an action is empty (no exterior terminal
has its feature outside the hull of the inside features), the action is `ε`-acceptable at
every parameter, so returning it with no observation is safe. -/
theorem hull_screen_safe (φ : Z → E) {S : Finset Z} (hS : S.Nonempty) {ε : ℝ} (hε : 0 ≤ ε)
    (h : hullScreen φ S = ∅) (θ : E) : regret S hS (env φ θ) ≤ ε := by
  by_contra hcon
  push Not at hcon
  have hmem : θ ∈ strictAlt φ S hS ε := hcon
  rw [strictAlt_eq_iUnion hS hε, h] at hmem
  simp at hmem

/-- **The remaining branch.**  If the hull screen of an action is nonempty, the action has a
strict `ε`-invalidating alternative; this is the hypothesis `hQ` of the theorems above. -/
theorem strictAlt_nonempty_of_hullScreen (φ : Z → E) {S : Finset Z} (hS : S.Nonempty) {ε : ℝ}
    (hε : 0 ≤ ε) (h : (hullScreen φ S).Nonempty) : (strictAlt φ S hS ε).Nonempty := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨lam, hlam⟩ := (strictComp_nonempty_iff (ε := ε) hε z).mpr hz.2
  exact ⟨lam, (mem_strictAlt_iff hS hε lam).mpr ⟨z, hz.1, hlam⟩⟩

/-- The two branches are exhaustive: either some action passes the hull test (and is
returned with no observation, `hull_screen_safe`), or every action has a strict alternative
(and the procedure of `bay_finite_literal` applies). -/
theorem screen_dichotomy {𝒜 : Type*} (φ : Z → E) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) {ε : ℝ} (hε : 0 ≤ ε) :
    (∃ a, hullScreen φ (supp a) = ∅) ∨ ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty := by
  by_cases h : ∃ a, hullScreen φ (supp a) = ∅
  · exact Or.inl h
  · push Not at h
    exact Or.inr fun a => strictAlt_nonempty_of_hullScreen φ (hne a) hε (h a)

end Screen

end LiteralD1

end JointRootCert
