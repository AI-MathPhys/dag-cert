/-
Literal forms of five results of the appendix "Certification Along Passive Graph-Search
Trajectories".

* **A.** Theorem `thm:puct-noisy-main` (Support-sensitive certification under recursive
  PUCT): the full-support clause as a statement about the stopping monitor
  (`full_support_monitor_certifies`), root supports derived from the search graph
  (`rootSupp`, `rootSupp_nonempty`, `rootSupp_reach`, `exists_margin_greatest`), the theorem
  with those supports (`puct_noisy_main_literal`), and existence of runs of the recursive
  PUCT contract whose values are running averages of tape rewards, with first-edge
  tie-breaking (`exists_tapeRun`, `exists_puctRun`, `exists_puctRun_family`,
  `TapeRun.end_is_sink`).
* **B.** Lemma `lem:v2strict` (Nesting and actual endpoint changes): the running
  intersection of the clipped intervals is a no-op (`v2RunLo_eq`, `v2RunHi_eq`) and the
  whole lemma in one statement (`v2strict_literal`).
* **C.** Proposition `prop:v35rootrates` (Positive-variance root PUCT: almost-sure
  square-root counts): `v35rootrates_literal`.
* **D.** Counterexample `ce:v35prior` (Zero prior at one internal edge prevents terminal
  coverage): `zero_prior_no_coverage`, `zero_prior_dag_conclusion_fails`,
  `zero_prior_counterexample`, `zero_prior_bernoulli`.
* **E.** Reward model of `thm:onpolicy-uct` and `thm:ta-core`: tables built from observed
  rewards (`obsTab`) agree with the tables defined from the true means
  (`funObsBox_eq`, `coreObsBox_eq`), and the two theorems restated with the observed tables
  (`onpolicy_uct_funnel_observed`, `ta_core_coupled_observed`).

What each theorem assumes is stated in its doc comment.
-/
import JointRootCert.Assembly
import JointRootCert.FunnelUCT
import JointRootCert.CoreCovers

namespace JointRootCert

namespace LiteralE6

open Finset

noncomputable section

/-! ## A. `thm:puct-noisy-main` -/

/-! ### A(i). The full-support clause as a statement about the monitor -/

section FullSupport

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

lemma stepCount_zero (p : ℕ → Prop) : stepCount p 0 = 0 :=
  Nat.le_zero.mp (stepCount_le p 0)

lemma stepCount_eq_zero {p : ℕ → Prop} {t : ℕ} (h : ∀ i < t, ¬ p i) : stepCount p t = 0 := by
  by_contra hne
  have hpos : 0 < stepCount p t := Nat.pos_of_ne_zero hne
  have hmono := stepCount_mono_pred (q := fun _ => False) t (fun i hi hp => h i hi hp)
  have hF : ∀ n, stepCount (fun _ : ℕ => False) n = 0 := by
    intro n
    induction n with
    | zero => exact stepCount_zero _
    | succ n ih => rw [stepCount_succ_of_neg (fun hf => hf), ih]
  rw [hF t] at hmono
  omega

lemma visitCount_zero {V : Type*} (vis : ℕ → V → Prop) (v : V) : visitCount vis v 0 = 0 :=
  stepCount_zero _

/-- At count `0` the running interval is the initial interval `[0, 1]`. -/
lemma runLower_zero (c β : ℕ → ℝ) : runLower c β 0 = 0 := by
  unfold runLower
  apply le_antisymm
  · refine sup'_le _ _ (fun k hk => ?_)
    have hk0 : k = 0 := by
      have := mem_range.mp hk
      omega
    rw [ite_eq_left hk0]
  · have h := le_sup' (fun k => if k = 0 then (0 : ℝ) else c k - β k)
      (mem_range.mpr (Nat.succ_pos 0))
    rw [ite_eq_left rfl] at h
    exact h

lemma runUpper_zero (c β : ℕ → ℝ) : runUpper c β 0 = 1 := by
  unfold runUpper
  apply le_antisymm
  · have h := inf'_le (fun k => if k = 0 then (1 : ℝ) else c k + β k)
      (mem_range.mpr (Nat.succ_pos 0))
    rw [ite_eq_left rfl] at h
    exact h
  · refine le_inf' _ _ (fun k hk => ?_)
    have hk0 : k = 0 := by
      have := mem_range.mp hk
      omega
    rw [ite_eq_left hk0]

omit [Nonempty Z] in
/-- The exact certificate of a full support is `0` on every box. -/
lemma exactCert_full_support {S : Finset Z} (hS : S.Nonempty) (hfull : S = univ)
    (l u : Z → ℝ) : exactCert S hS l u = 0 := by
  have hc : ¬ Sᶜ.Nonempty := by
    rw [hfull]
    simp
  unfold exactCert
  exact dite_eq_right hc

omit [Nonempty Z] in
/-- The exact certificate of a proper support is the outside-support expression. -/
lemma exactCert_proper {S : Finset Z} (hS : S.Nonempty) (h : Sᶜ.Nonempty) (l u : Z → ℝ) :
    exactCert S hS l u = rectCert S hS h l u := by
  unfold exactCert
  exact dite_eq_left h

/-- **Full-support clause of `thm:puct-noisy-main`, for the monitor.**  "If a root support
equals `Z`, it is certifiable without observations."

The monitor is the exact-regret monitor of `puct_horizon`: `hmon` says that as soon as some
root action has exact certificate (`exactCert`, including the empty-complement case) at most
`ε` on the current box, the monitor has stopped, and the action it returned is certified at
its stopping time.  The box at time `s` is the running intersection at the counts
`cnt s ω z`, and no terminal has been observed at time `0` (`hcnt0`).

If some root action `a0` has `supp a0 = Z` and `ε ≥ 0`, then on every sample path: the
certificate of `a0` on the initial box `[0,1]^Z` is `0`; the monitor stops at time `0`,
that is before any observation; the action it returns is certified on the initial box; and
that action is `ε`-optimal for every mean vector in `[0,1]^Z`.  No probability is involved
and no property of the search is used. -/
theorem full_support_monitor_certifies {Ω A : Type*} (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1)
    (c : Ω → Z → ℕ → ℝ) (β : ℕ → ℝ) (cnt : ℕ → Ω → Z → ℕ) (hcnt0 : ∀ ω z, cnt 0 ω z = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, exactCert (supp a) (hne a)
          (fun z => runLower (c ω z) β (cnt s ω z))
          (fun z => runUpper (c ω z) β (cnt s ω z)) ≤ ε) →
        τ ω ≤ s ∧ exactCert (supp (rec ω)) (hne (rec ω))
          (fun z => runLower (c ω z) β (cnt (τ ω) ω z))
          (fun z => runUpper (c ω z) β (cnt (τ ω) ω z)) ≤ ε)
    (a0 : A) (hfull : supp a0 = univ) (ω : Ω) :
    exactCert (supp a0) (hne a0) (fun _ => 0) (fun _ => 1) = 0 ∧ τ ω = 0 ∧
      exactCert (supp (rec ω)) (hne (rec ω)) (fun _ => 0) (fun _ => 1) ≤ ε ∧
      regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε := by
  obtain ⟨hτ, hcert⟩ := hmon ω 0
    ⟨a0, by rw [exactCert_full_support (hne a0) hfull]; exact hε⟩
  have hτ0 : τ ω = 0 := Nat.le_zero.mp hτ
  rw [hτ0] at hcert
  simp only [hcnt0, runLower_zero, runUpper_zero] at hcert
  exact ⟨exactCert_full_support (hne a0) hfull _ _, hτ0, hcert,
    (regret_le_exactCert (hne (rec ω)) ⟨fun z => (hμ z).1, fun z => (hμ z).2⟩).trans hcert⟩

/-- The largest exterior margin over optimal root actions exists as soon as some root action
is optimal (finitely many root actions). -/
lemma exists_margin_greatest {A : Type*} [Finite A] (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty) (μ : Z → ℝ)
    (hopt : ∃ a, val (supp a) (hne a) μ = gmax μ) :
    ∃ Γ, IsGreatest ((fun a => outsideMargin (supp a) (hpr a) μ) ''
      {a | val (supp a) (hne a) μ = gmax μ}) Γ := by
  classical
  have := Fintype.ofFinite A
  obtain ⟨a0, ha0⟩ := hopt
  obtain ⟨a, ha, hmax⟩ := (univ.filter (fun a => val (supp a) (hne a) μ = gmax μ)).exists_max_image
    (fun a => outsideMargin (supp a) (hpr a) μ) ⟨a0, mem_filter.mpr ⟨mem_univ _, ha0⟩⟩
  refine ⟨_, ⟨a, (mem_filter.mp ha).2, rfl⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact hmax b (mem_filter.mpr ⟨mem_univ _, hb⟩)

end FullSupport

/-! ### A(ii). Supports derived from the search graph -/

section GraphSupport

variable {V E : Type*} [Fintype E] {Z : Type*} [Fintype Z]

/-- `w` is reachable from `v` along a directed path of the search graph. -/
def Reach (src tgt : E → V) (v w : V) : Prop := ∃ p : List E, IsPath src tgt p v w

open Classical in
/-- The terminals reachable from a vertex of the search graph. -/
def graphSupp (src tgt : E → V) (term : Z → V) (v : V) : Finset Z :=
  univ.filter (fun z => Reach src tgt v (term z))

/-- The root actions of the search graph: the edges leaving the root. -/
abbrev RootAct (src : E → V) (root : V) : Type _ := {e : E // src e = root}

/-- **Support of a root action, derived from the graph**: the terminals reachable from the
head of the root edge. -/
def rootSupp (src tgt : E → V) (root : V) (term : Z → V) (a : RootAct src root) : Finset Z :=
  graphSupp src tgt term (tgt a.1)

omit [Fintype Z] in
/-- In a DAG (given by a rank function that decreases along every edge) in which every sink
is a terminal, every vertex reaches a terminal. -/
lemma reach_terminal {src tgt : E → V} (term : Z → V) (rk : V → ℕ)
    (hrk : ∀ e, rk (tgt e) < rk (src e)) (hsink : ∀ v, outEdges src v = ∅ → ∃ z, term z = v) :
    ∀ (n : ℕ) (v : V), rk v = n → ∃ z, Reach src tgt v (term z) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    rcases (outEdges src v).eq_empty_or_nonempty with he | ⟨e, he⟩
    · obtain ⟨z, hz⟩ := hsink v he
      exact ⟨z, [], hz.symm⟩
    · have hsrc : src e = v := mem_outEdges.mp he
      have hlt : rk (tgt e) < n := by
        rw [← hv, ← hsrc]
        exact hrk e
      obtain ⟨z, p, hp⟩ := ih (rk (tgt e)) hlt (tgt e) rfl
      exact ⟨z, e :: p, hsrc, hp⟩

/-- The graph-derived support of every root action is nonempty. -/
lemma rootSupp_nonempty {src tgt : E → V} {root : V} (term : Z → V) (rk : V → ℕ)
    (hrk : ∀ e, rk (tgt e) < rk (src e)) (hsink : ∀ v, outEdges src v = ∅ → ∃ z, term z = v)
    (a : RootAct src root) : (rootSupp src tgt root term a).Nonempty := by
  classical
  obtain ⟨z, hz⟩ := reach_terminal term rk hrk hsink _ (tgt a.1) rfl
  exact ⟨z, mem_filter.mpr ⟨mem_univ _, hz⟩⟩

omit [Fintype E] in
/-- Every terminal lies in the support of some root action, as soon as it has a path from
the root and is not the root itself. -/
lemma rootSupp_reach {src tgt : E → V} {root : V} (term : Z → V) (path : Z → List E)
    (hpath : ∀ z, IsPath src tgt (path z) root (term z)) (hroot : ∀ z, term z ≠ root) (z : Z) :
    ∃ a : RootAct src root, z ∈ rootSupp src tgt root term a := by
  classical
  have hp := hpath z
  cases hpz : path z with
  | nil =>
      rw [hpz] at hp
      exact absurd (show root = term z from hp).symm (hroot z)
  | cons e p =>
      rw [hpz] at hp
      obtain ⟨hsrc, hp'⟩ := hp
      exact ⟨⟨e, hsrc⟩, mem_filter.mpr ⟨mem_univ _, p, hp'⟩⟩

end GraphSupport

section MainLiteral

open MeasureTheory

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {V E : Type*} [Fintype E]
  {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem `thm:puct-noisy-main` with graph-derived supports and all three clauses.**

The search is, on every sample path, a run of the recursive PUCT contract `PUCTRun` on a
fixed graph that is a DAG (`rk` decreases along every edge) in which every sink is a
terminal `term z`; `path z` is a root-to-terminal path of length at most `H`.  The root
actions are the edges leaving the root and the support of a root action is the set of
terminals reachable from it in this graph (`rootSupp`); these supports are nonempty by
`rootSupp_nonempty`.  Terminal `z` is sampled by reading its tape `X z` in order; the tapes
are `[0,1]`-valued with mean `μ z` and independent within a tape.  The monitor is the
exact-regret monitor on the running intersections of the intervals with radius
`β_M(n, δ)` (`puctRadius`, `M = |Z|`), started from `[0,1]`; `hmon` is its specification
(it has stopped as soon as some root action has exact certificate at most `ε`, and returns
a certified action).

Conclusions:
1. on every sample path, every terminal has at least `c_* t ^ (2 ^ (-H))` observations for
   all `t ≥ t_*`, and `c_* > 0`;
2. if some root support equals `Z`, the monitor stops at time `0` on every sample path,
   before any observation, with an `ε`-optimal action;
3. otherwise (all supports proper), with `Γ` the largest exterior margin over optimal root
   actions and `ε + Γ > 0`, for every `t ≥ t_*` satisfying `eq:puct-noisy-condition` the
   event `{τ ≤ t and Reg ≤ ε}` fails with probability at most `δ / 2`.

Clause 3 is `puct_noisy_main_tape` applied to the graph-derived supports.  `Γ` exists by
`exists_margin_greatest` and `rootSupp_reach`. -/
theorem puct_noisy_main_literal {src tgt : E → V} {root : V} {lam : E → ℝ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    (vis : Ω → ℕ → V → Prop) (ch : Ω → ℕ → V → E) (Q : Ω → E → ℕ → ℝ)
    (hrun : ∀ ω, PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω))
    (term : Z → V) (rk : V → ℕ) (hrk : ∀ e, rk (tgt e) < rk (src e))
    (hsink : ∀ v, outEdges src v = ∅ → ∃ z, term z = v)
    (path : Z → List E) (hpath : ∀ z, IsPath src tgt (path z) root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ) (hε : 0 ≤ ε) (τ : Ω → ℕ)
    (rec : Ω → RootAct src root)
    (hmon : ∀ ω s, (∃ a, exactCert (rootSupp src tgt root term a)
          (rootSupp_nonempty term rk hrk hsink a)
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s)) ≤ ε) →
        τ ω ≤ s ∧ exactCert (rootSupp src tgt root term (rec ω))
          (rootSupp_nonempty term rk hrk hsink (rec ω))
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω)))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω))) ≤ ε) :
    (0 < puctCstar lam path ∧ ∀ ω (t : ℕ), puctTstar src lam path ≤ t → ∀ z,
        puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ) ≤ visitCount (vis ω) (term z) t) ∧
    ((∃ a, rootSupp src tgt root term a = univ) → ∀ ω, τ ω = 0 ∧
        exactCert (rootSupp src tgt root term (rec ω))
          (rootSupp_nonempty term rk hrk hsink (rec ω)) (fun _ => 0) (fun _ => 1) ≤ ε ∧
        regret (rootSupp src tgt root term (rec ω))
          (rootSupp_nonempty term rk hrk hsink (rec ω)) μ ≤ ε) ∧
    (∀ (hpr : ∀ a, (rootSupp src tgt root term a)ᶜ.Nonempty) (Γ : ℝ),
      IsGreatest ((fun a => outsideMargin (rootSupp src tgt root term a) (hpr a) μ) ''
        {a | val (rootSupp src tgt root term a) (rootSupp_nonempty term rk hrk hsink a) μ
          = gmax μ}) Γ →
      0 < ε + Γ → ∀ t : ℕ, puctTstar src lam path ≤ t →
      8 / (ε + Γ) ^ 2 * Real.log (4 * (Fintype.card Z : ℝ) * ((t : ℝ) + 1) ^ 2 / δ) ≤
        puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ) →
      P {ω | ¬ (τ ω ≤ t ∧ regret (rootSupp src tgt root term (rec ω))
          (rootSupp_nonempty term rk hrk hsink (rec ω)) μ ≤ ε)} ≤ ENNReal.ofReal (δ / 2)) := by
  obtain ⟨ω0⟩ : Nonempty Ω := by
    by_contra hΩ
    rw [not_nonempty_iff] at hΩ
    have h1 : P Set.univ = 1 := measure_univ
    rw [Set.eq_empty_of_isEmpty (Set.univ : Set Ω), measure_empty] at h1
    exact zero_ne_one h1
  refine ⟨⟨puctCstar_pos (hrun ω0).lam_pos path, fun ω t ht z =>
    puct_terminal_coverage' (hrun ω) term path hpath H hH t ht z⟩, ?_, ?_⟩
  · rintro ⟨a0, hfull⟩ ω
    exact (full_support_monitor_certifies (rootSupp src tgt root term)
      (fun a => rootSupp_nonempty term rk hrk hsink a) μ hμ
      (fun ω z k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω) (puctRadius (Fintype.card Z) δ)
      (fun s ω z => visitCount (vis ω) (term z) s) (fun ω z => visitCount_zero _ _) ε hε τ rec
      hmon a0 hfull ω).2
  · intro hpr Γ hΓ hpos t ht hcond
    exact puct_noisy_main_tape P vis ch Q hrun term path hpath H hH
      (rootSupp src tgt root term) (fun a => rootSupp_nonempty term rk hrk hsink a) hpr μ hμ X
      hmeas hbdd hmean hindep hδ0 hδ1 ε τ rec
      (fun ω s hex => by
        obtain ⟨a, ha⟩ := hex
        have hx := hmon ω s ⟨a, by rw [exactCert_proper _ (hpr a)]; exact ha⟩
        rw [exactCert_proper _ (hpr (rec ω))] at hx
        exact hx)
      Γ hΓ hε hpos t ht hcond

end MainLiteral

/-! ### A(iii). Existence of runs -/

section LeastArgmax

variable {E : Type*} [LinearOrder E]

omit [LinearOrder E] in
open Classical in
lemma argmax_nonempty (A : Finset E) (hA : A.Nonempty) (f : E → ℝ) :
    (A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e)).Nonempty := by
  obtain ⟨e, he, hmax⟩ := A.exists_max_image f hA
  exact ⟨e, mem_filter.mpr ⟨he, hmax⟩⟩

open Classical in
/-- The least maximiser of `f` over `A` in the fixed linear order of `E` (canonical
first-edge tie-breaking); an arbitrary element when `A` is empty. -/
def leastArgmax [Nonempty E] (A : Finset E) (f : E → ℝ) : E :=
  if h : A.Nonempty then (A.filter (fun e => ∀ e' ∈ A, f e' ≤ f e)).min' (argmax_nonempty A h f)
  else Classical.arbitrary E

open Classical in
lemma leastArgmax_spec [Nonempty E] (A : Finset E) (hA : A.Nonempty) (f : E → ℝ) :
    leastArgmax A f ∈ A ∧ (∀ e' ∈ A, f e' ≤ f (leastArgmax A f)) ∧
      ∀ e ∈ A, (∀ e' ∈ A, f e' ≤ f e) → leastArgmax A f ≤ e := by
  unfold leastArgmax
  rw [dite_eq_left hA]
  have hm := Finset.min'_mem _ (argmax_nonempty A hA f)
  rw [mem_filter] at hm
  exact ⟨hm.1, hm.2, fun e he hmax => Finset.min'_le _ e (mem_filter.mpr ⟨he, hmax⟩)⟩

end LeastArgmax

/-- A sequence defined by a rule that reads only earlier entries exists. -/
lemma exists_causal_fix {α : Type*} [Nonempty α] (F : (ℕ → α) → ℕ → α)
    (hF : ∀ (f f' : ℕ → α) (t : ℕ), (∀ s, s < t → f s = f' s) → F f t = F f' t) :
    ∃ f : ℕ → α, ∀ t, f t = F f t := by
  obtain ⟨d⟩ := ‹Nonempty α›
  let selOf : List α → ℕ → α := fun l s => l.getD s d
  let step : List α → α := fun l => F (selOf l) l.length
  let hist : ℕ → List α := fun t => Nat.rec [] (fun _ l => l ++ [step l]) t
  have hist_succ : ∀ t, hist (t + 1) = hist t ++ [step (hist t)] := fun _ => rfl
  have hlen : ∀ t, (hist t).length = t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hist_succ, List.length_append, ih]; rfl
  have hget : ∀ t s, s < t → (hist t).getD s d = step (hist s) := by
    intro t
    induction t with
    | zero => intro s hs; exact absurd hs (Nat.not_lt_zero s)
    | succ t ih =>
      intro s hs
      rw [hist_succ]
      rcases Nat.lt_or_ge s t with h1 | h1
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h1)]
        exact ih s h1
      · have hst : s = t := by omega
        rw [List.getD_append_right _ _ _ _ (by rw [hlen]; exact h1), hlen, hst]
        simp
  refine ⟨fun t => step (hist t), fun t => ?_⟩
  show F (selOf (hist t)) (hist t).length = F (fun t => step (hist t)) t
  rw [hlen]
  exact hF _ _ t (fun s hs => hget t s hs)

section Run

variable {V E : Type*} [Fintype E]

lemma stepCount_congr {p q : ℕ → Prop} (t : ℕ) (h : ∀ i, i < t → (p i ↔ q i)) :
    stepCount p t = stepCount q t :=
  le_antisymm (stepCount_mono_pred t (fun i hi hp => (h i hi).mp hp))
    (stepCount_mono_pred t (fun i hi hq => (h i hi).mpr hq))

open Classical in
/-- Sum of `f` over the steps `i < t` at which `p` holds. -/
def stepSum (p : ℕ → Prop) (f : ℕ → ℝ) (t : ℕ) : ℝ := ∑ i ∈ (range t).filter p, f i

open Classical in
lemma stepSum_congr {p q : ℕ → Prop} {f g : ℕ → ℝ} (t : ℕ) (h : ∀ i, i < t → (p i ↔ q i))
    (hf : ∀ i, i < t → f i = g i) : stepSum p f t = stepSum q g t := by
  unfold stepSum
  have hfil : (range t).filter p = (range t).filter q :=
    filter_congr (fun i hi => h i (mem_range.mp hi))
  rw [hfil]
  exact sum_congr rfl (fun i hi => hf i (mem_range.mp (mem_filter.mp hi).1))

open Classical in
lemma stepSum_bounds (p : ℕ → Prop) (f : ℕ → ℝ) (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    0 ≤ stepSum p f t ∧ stepSum p f t ≤ (stepCount p t : ℝ) := by
  unfold stepSum stepCount
  refine ⟨sum_nonneg (fun i _ => (hf i).1), ?_⟩
  calc ∑ i ∈ (range t).filter p, f i ≤ ∑ i ∈ (range t).filter p, (1 : ℝ) :=
        sum_le_sum (fun i _ => (hf i).2)
    _ = (((range t).filter p).card : ℝ) := by simp

open Classical in
/-- The walk of one simulation: start at the root and follow the chosen outgoing edge of
the current vertex until a vertex without outgoing edges is reached (where it stays). -/
def walkV (src tgt : E → V) (root : V) (c : V → E) : ℕ → V
  | 0 => root
  | k + 1 =>
      if (outEdges src (walkV src tgt root c k)).Nonempty then
        tgt (c (walkV src tgt root c k))
      else walkV src tgt root c k

lemma walkV_zero (src tgt : E → V) (root : V) (c : V → E) : walkV src tgt root c 0 = root := rfl

open Classical in
lemma walkV_succ (src tgt : E → V) (root : V) (c : V → E) (k : ℕ) :
    walkV src tgt root c (k + 1) =
      if (outEdges src (walkV src tgt root c k)).Nonempty then
        tgt (c (walkV src tgt root c k))
      else walkV src tgt root c k := rfl

/-- The reward returned by simulation `s`: the next unused element of the tape `x v` of the
vertex `v` at which the walk of simulation `s` stands after `L` steps (its end vertex when
`L` is at least the depth of the graph, `TapeRun.end_is_sink`). -/
def runRew (src tgt : E → V) (root : V) (x : V → ℕ → ℝ) (L : ℕ) (vis : ℕ → V → Prop)
    (ch : ℕ → V → E) (s : ℕ) : ℝ :=
  x (walkV src tgt root (ch s) L) (visitCount vis (walkV src tgt root (ch s) L) s)

/-- The running average of the rewards `rew i` of the earlier simulations that traversed
the edge `e`; `0` while `e` is unvisited. -/
def runAvg (src : E → V) (rew : ℕ → ℝ) (vis : ℕ → V → Prop) (ch : ℕ → V → E) (e : E)
    (s : ℕ) : ℝ :=
  if edgeCount vis ch (src e) e s = 0 then 0
  else stepSum (fun i => vis i (src e) ∧ ch i (src e) = e) rew s /
    (edgeCount vis ch (src e) e s : ℝ)

/-- The PUCT score `Q_e + λ_e √(n_v) / (1 + N_{v,e})` of edge `e` at its tail `v`. -/
def runScore (src : E → V) (lam : E → ℝ) (Q : E → ℕ → ℝ) (vis : ℕ → V → Prop)
    (ch : ℕ → V → E) (e : E) (s : ℕ) : ℝ :=
  Q e s + lam e * √(visitCount vis (src e) s : ℝ) / (1 + (edgeCount vis ch (src e) e s : ℝ))

omit [Fintype E] in
lemma runAvg_mem (src : E → V) {rew : ℕ → ℝ} (hrew : ∀ i, rew i ∈ Set.Icc (0 : ℝ) 1)
    (vis : ℕ → V → Prop) (ch : ℕ → V → E) (e : E) (s : ℕ) :
    0 ≤ runAvg src rew vis ch e s ∧ runAvg src rew vis ch e s ≤ 1 := by
  unfold runAvg
  split_ifs with h0
  · exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨h1, h2⟩ := stepSum_bounds (fun i => vis i (src e) ∧ ch i (src e) = e) rew hrew s
    have hpos : (0 : ℝ) < (edgeCount vis ch (src e) e s : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h0
    refine ⟨div_nonneg h1 hpos.le, ?_⟩
    rw [div_le_one hpos]
    exact h2

/-- The recursive PUCT contract of `sec:v35scope` without the positivity of the weights:
all fields of `PUCTRun` except `lam_pos`. -/
structure PUCTContract (src tgt : E → V) (root : V) (lam : E → ℝ) (vis : ℕ → V → Prop)
    (ch : ℕ → V → E) (Q : E → ℕ → ℝ) : Prop where
  root_vis : ∀ s, vis s root
  ch_src : ∀ s v, vis s v → (outEdges src v).Nonempty → src (ch s v) = v
  ch_vis : ∀ s v, vis s v → (outEdges src v).Nonempty → vis s (tgt (ch s v))
  Q_mem : ∀ s e, 0 ≤ Q e s ∧ Q e s ≤ 1
  puct : ∀ s v, vis s v → ∀ e, src e = v →
    Q e s + lam e * √(visitCount vis v s : ℝ) / (1 + (edgeCount vis ch v e s : ℝ)) ≤
      Q (ch s v) s + lam (ch s v) * √(visitCount vis v s : ℝ) /
        (1 + (edgeCount vis ch v (ch s v) s : ℝ))

theorem puctRun_iff {src tgt : E → V} {root : V} {lam : E → ℝ} {vis : ℕ → V → Prop}
    {ch : ℕ → V → E} {Q : E → ℕ → ℝ} :
    PUCTRun src tgt root lam vis ch Q ↔
      PUCTContract src tgt root lam vis ch Q ∧ ∀ e, 0 < lam e :=
  ⟨fun h => ⟨⟨h.root_vis, h.ch_src, h.ch_vis, h.Q_mem, h.puct⟩, h.lam_pos⟩,
    fun h => ⟨h.2, h.1.root_vis, h.1.ch_src, h.1.ch_vis, h.1.Q_mem, h.1.puct⟩⟩

/-- **A recursive PUCT run driven by reward tapes** (`sec:v35scope`).  The contract holds;
the vertices visited by simulation `s` are exactly those of its walk from the root along
the chosen edges; and the value of an edge is the running average of the rewards returned
by the earlier simulations that traversed it, initialised to `0`, where the reward of a
simulation is the next unused element of the tape `x v` of the vertex `v` its walk has
reached after `L` steps. -/
structure TapeRun (src tgt : E → V) (root : V) (lam : E → ℝ) (x : V → ℕ → ℝ) (L : ℕ)
    (vis : ℕ → V → Prop) (ch : ℕ → V → E) (Q : E → ℕ → ℝ) : Prop where
  contract : PUCTContract src tgt root lam vis ch Q
  walk : ∀ s v, vis s v ↔ ∃ k, walkV src tgt root (ch s) k = v
  Q_avg : ∀ e s, Q e s = runAvg src (runRew src tgt root x L vis ch) vis ch e s

/-- Canonical first-edge tie-breaking: at a visited vertex the selected edge is the least
(in the fixed order of the edges) among the outgoing edges of maximal score. -/
def FirstEdgeTies [LinearOrder E] (src : E → V) (lam : E → ℝ) (vis : ℕ → V → Prop)
    (ch : ℕ → V → E) (Q : E → ℕ → ℝ) : Prop :=
  ∀ s v, vis s v → ∀ e, src e = v →
    runScore src lam Q vis ch (ch s v) s ≤ runScore src lam Q vis ch e s → ch s v ≤ e

/-- In a DAG whose rank at the root is at most `L`, the walk of every simulation of a tape
run stands at a vertex without outgoing edges after `L` steps, and that vertex is visited.
So the reward of a simulation is read from the tape of the sink it reaches. -/
theorem TapeRun.end_is_sink {src tgt : E → V} {root : V} {lam : E → ℝ} {x : V → ℕ → ℝ}
    {L : ℕ} {vis : ℕ → V → Prop} {ch : ℕ → V → E} {Q : E → ℕ → ℝ}
    (h : TapeRun src tgt root lam x L vis ch Q) (rk : V → ℕ)
    (hrk : ∀ e, rk (tgt e) < rk (src e)) (hL : rk root ≤ L) (s : ℕ) :
    outEdges src (walkV src tgt root (ch s) L) = ∅ ∧ vis s (walkV src tgt root (ch s) L) := by
  have key : ∀ k, outEdges src (walkV src tgt root (ch s) k) = ∅ ∨
      rk (walkV src tgt root (ch s) k) + k ≤ rk root := by
    intro k
    induction k with
    | zero =>
        right
        rw [walkV_zero]
        exact le_rfl
    | succ k ih =>
        rcases (outEdges src (walkV src tgt root (ch s) k)).eq_empty_or_nonempty with he | hne
        · left
          have hnn : ¬ (outEdges src (walkV src tgt root (ch s) k)).Nonempty := by
            rw [he]
            exact Finset.not_nonempty_empty
          rw [walkV_succ, ite_eq_right hnn]
          exact he
        · right
          rw [walkV_succ, ite_eq_left hne]
          rcases ih with he | hle
          · rw [he] at hne
            exact absurd hne Finset.not_nonempty_empty
          · have h1 := hrk (ch s (walkV src tgt root (ch s) k))
            rw [h.contract.ch_src s _ ((h.walk s _).mpr ⟨k, rfl⟩) hne] at h1
            omega
  refine ⟨?_, (h.walk s _).mpr ⟨L, rfl⟩⟩
  rcases key L with he | hle
  · exact he
  · by_contra hne
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h1 := hrk e
    rw [mem_outEdges.mp he] at h1
    omega

/-- Visited vertices of simulation `s` under the choice functions `ch`. -/
def simVis (src tgt : E → V) (root : V) (ch : ℕ → V → E) (s : ℕ) (v : V) : Prop :=
  ∃ k, walkV src tgt root (ch s) k = v

/-- Edge values under the choice functions `ch`: running averages of the tape rewards. -/
def simQ (src tgt : E → V) (root : V) (x : V → ℕ → ℝ) (L : ℕ) (ch : ℕ → V → E) :
    E → ℕ → ℝ :=
  fun e s => runAvg src (runRew src tgt root x L (simVis src tgt root ch) ch)
    (simVis src tgt root ch) ch e s

/-- Edge scores under the choice functions `ch`. -/
def simScore (src tgt : E → V) (root : V) (lam : E → ℝ) (x : V → ℕ → ℝ) (L : ℕ)
    (ch : ℕ → V → E) (e : E) (s : ℕ) : ℝ :=
  runScore src lam (simQ src tgt root x L ch) (simVis src tgt root ch) ch e s

/-- The score at time `t` depends only on the choices made before `t`. -/
lemma simScore_congr (src tgt : E → V) (root : V) (lam : E → ℝ) (x : V → ℕ → ℝ) (L : ℕ)
    {ch ch' : ℕ → V → E} {t : ℕ} (h : ∀ i, i < t → ch i = ch' i) (e : E) :
    simScore src tgt root lam x L ch e t = simScore src tgt root lam x L ch' e t := by
  have hvis : ∀ i, i < t → ∀ v, (simVis src tgt root ch i v ↔ simVis src tgt root ch' i v) := by
    intro i hi v
    unfold simVis
    rw [h i hi]
  have hvc : ∀ i, i ≤ t → ∀ v, visitCount (simVis src tgt root ch) v i =
      visitCount (simVis src tgt root ch') v i := by
    intro i hi v
    exact stepCount_congr i (fun j hj => hvis j (lt_of_lt_of_le hj hi) v)
  have hrew : ∀ i, i < t → runRew src tgt root x L (simVis src tgt root ch) ch i =
      runRew src tgt root x L (simVis src tgt root ch') ch' i := by
    intro i hi
    unfold runRew
    rw [h i hi, hvc i hi.le]
  have hpred : ∀ i, i < t → ((simVis src tgt root ch i (src e) ∧ ch i (src e) = e) ↔
      (simVis src tgt root ch' i (src e) ∧ ch' i (src e) = e)) := by
    intro i hi
    rw [hvis i hi, h i hi]
  have hec : edgeCount (simVis src tgt root ch) ch (src e) e t =
      edgeCount (simVis src tgt root ch') ch' (src e) e t := stepCount_congr t hpred
  have hss : stepSum (fun i => simVis src tgt root ch i (src e) ∧ ch i (src e) = e)
        (runRew src tgt root x L (simVis src tgt root ch) ch) t =
      stepSum (fun i => simVis src tgt root ch' i (src e) ∧ ch' i (src e) = e)
        (runRew src tgt root x L (simVis src tgt root ch') ch') t :=
    stepSum_congr t hpred hrew
  simp only [simScore, runScore, simQ, runAvg, hec, hss, hvc t le_rfl]

/-- **Existence of tape-driven runs (non-vacuity of the run structure).**  For every finite
edge set with a fixed linear order, every graph (`src`, `tgt`, `root`), every weight vector
`lam` (no sign condition), every family of `[0,1]`-valued tapes `x` and every `L`, there is
a run satisfying the recursive PUCT contract in which the visited vertices are the walk
from the root, the edge values are the running averages of the tape rewards, and ties are
broken towards the least edge. -/
theorem exists_tapeRun [LinearOrder E] [Nonempty E] (src tgt : E → V) (root : V)
    (lam : E → ℝ) (x : V → ℕ → ℝ) (hx : ∀ v k, x v k ∈ Set.Icc (0 : ℝ) 1) (L : ℕ) :
    ∃ (vis : ℕ → V → Prop) (ch : ℕ → V → E) (Q : E → ℕ → ℝ),
      TapeRun src tgt root lam x L vis ch Q ∧ FirstEdgeTies src lam vis ch Q := by
  have : Nonempty (V → E) := ⟨fun _ => Classical.arbitrary E⟩
  obtain ⟨ch, hch⟩ := exists_causal_fix
    (fun (ch : ℕ → V → E) (s : ℕ) (v : V) =>
      leastArgmax (outEdges src v) (fun e => simScore src tgt root lam x L ch e s))
    (fun f f' t h => by
      funext v
      have hfun : (fun e => simScore src tgt root lam x L f e t) =
          (fun e => simScore src tgt root lam x L f' e t) :=
        funext (fun e => simScore_congr src tgt root lam x L h e)
      show leastArgmax (outEdges src v) (fun e => simScore src tgt root lam x L f e t) =
        leastArgmax (outEdges src v) (fun e => simScore src tgt root lam x L f' e t)
      rw [hfun])
  have hchv : ∀ s v, ch s v =
      leastArgmax (outEdges src v) (fun e => simScore src tgt root lam x L ch e s) :=
    fun s v => congrFun (hch s) v
  refine ⟨simVis src tgt root ch, ch, simQ src tgt root x L ch,
    ⟨⟨fun s => ⟨0, rfl⟩, ?_, ?_, ?_, ?_⟩, fun _ _ => Iff.rfl, fun _ _ => rfl⟩, ?_⟩
  · intro s v _ hne
    rw [hchv s v]
    exact mem_outEdges.mp (leastArgmax_spec _ hne _).1
  · rintro s v ⟨k, hk⟩ hne
    refine ⟨k + 1, ?_⟩
    rw [walkV_succ, hk, ite_eq_left hne]
  · intro s e
    exact runAvg_mem src (fun i => hx _ _) _ _ e s
  · intro s v _ e he
    subst he
    have hspec := leastArgmax_spec (outEdges src (src e)) ⟨e, mem_outEdges.mpr rfl⟩
      (fun e' => simScore src tgt root lam x L ch e' s)
    have hsrc : src (ch s (src e)) = src e := by
      rw [hchv s (src e)]
      exact mem_outEdges.mp hspec.1
    have hmax : simScore src tgt root lam x L ch e s ≤
        simScore src tgt root lam x L ch (ch s (src e)) s := by
      rw [hchv s (src e)]
      exact hspec.2.1 e (mem_outEdges.mpr rfl)
    unfold simScore runScore at hmax
    rw [hsrc] at hmax
    exact hmax
  · intro s v _ e he hle
    subst he
    have hspec := leastArgmax_spec (outEdges src (src e)) ⟨e, mem_outEdges.mpr rfl⟩
      (fun e' => simScore src tgt root lam x L ch e' s)
    have hle' : simScore src tgt root lam x L ch
        (leastArgmax (outEdges src (src e)) (fun e' => simScore src tgt root lam x L ch e' s)) s ≤
        simScore src tgt root lam x L ch e s := by
      rw [← hchv s (src e)]
      exact hle
    rw [hchv s (src e)]
    exact hspec.2.2 e (mem_outEdges.mpr rfl) (fun e' he' => (hspec.2.1 e' he').trans hle')

/-- **Existence of `PUCTRun`s (item (iii) for `thm:puct-noisy-main`).**  Under the standing
assumptions (finite edge set, fixed strictly positive weights, `[0,1]`-valued tapes) there
is a run satisfying `PUCTRun`, driven by the tapes as in `TapeRun`, with first-edge
tie-breaking. -/
theorem exists_puctRun [LinearOrder E] [Nonempty E] (src tgt : E → V) (root : V)
    (lam : E → ℝ) (hlam : ∀ e, 0 < lam e) (x : V → ℕ → ℝ)
    (hx : ∀ v k, x v k ∈ Set.Icc (0 : ℝ) 1) (L : ℕ) :
    ∃ (vis : ℕ → V → Prop) (ch : ℕ → V → E) (Q : E → ℕ → ℝ),
      PUCTRun src tgt root lam vis ch Q ∧ TapeRun src tgt root lam x L vis ch Q ∧
        FirstEdgeTies src lam vis ch Q := by
  obtain ⟨vis, ch, Q, h, htie⟩ := exists_tapeRun src tgt root lam x hx L
  exact ⟨vis, ch, Q, puctRun_iff.mpr ⟨h.contract, hlam⟩, h, htie⟩

/-- The same for a family of tapes indexed by sample paths: there are `vis`, `ch`, `Q` as
functions of the sample path satisfying the hypothesis `hrun` of `puct_noisy_main_tape` and
`puct_noisy_main_literal`. -/
theorem exists_puctRun_family [LinearOrder E] [Nonempty E] {Ω : Type*} (src tgt : E → V)
    (root : V) (lam : E → ℝ) (hlam : ∀ e, 0 < lam e) (x : Ω → V → ℕ → ℝ)
    (hx : ∀ ω v k, x ω v k ∈ Set.Icc (0 : ℝ) 1) (L : ℕ) :
    ∃ (vis : Ω → ℕ → V → Prop) (ch : Ω → ℕ → V → E) (Q : Ω → E → ℕ → ℝ), ∀ ω,
      PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω) ∧
        TapeRun src tgt root lam (x ω) L (vis ω) (ch ω) (Q ω) ∧
        FirstEdgeTies src lam (vis ω) (ch ω) (Q ω) := by
  choose vis ch Q h using fun ω => exists_puctRun src tgt root lam hlam (x ω) (hx ω) L
  exact ⟨vis, ch, Q, h⟩

end Run

/-! ## B. `lem:v2strict` -/

section V2Strict

variable {δ μ : ℝ}

/-- Lower endpoint of the running intersection of the initial interval `[0, 1]` and the
clipped intervals `[rootPuctLo δ μ k, rootPuctHi δ μ k]`, `1 ≤ k ≤ n`. -/
def v2RunLo (δ μ : ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' ⟨0, mem_range.mpr n.succ_pos⟩
    (fun k => if k = 0 then 0 else rootPuctLo δ μ k)

/-- Upper endpoint of the same running intersection. -/
def v2RunHi (δ μ : ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).inf' ⟨0, mem_range.mpr n.succ_pos⟩
    (fun k => if k = 0 then 1 else rootPuctHi δ μ k)

lemma v2RunLo_zero (δ μ : ℝ) : v2RunLo δ μ 0 = 0 := by
  unfold v2RunLo
  apply le_antisymm
  · refine sup'_le _ _ (fun k hk => ?_)
    have hk0 : k = 0 := by
      have := mem_range.mp hk
      omega
    rw [ite_eq_left hk0]
  · have h := le_sup' (fun k => if k = 0 then (0 : ℝ) else rootPuctLo δ μ k)
      (mem_range.mpr (Nat.succ_pos 0))
    rw [ite_eq_left rfl] at h
    exact h

lemma v2RunHi_zero (δ μ : ℝ) : v2RunHi δ μ 0 = 1 := by
  unfold v2RunHi
  apply le_antisymm
  · have h := inf'_le (fun k => if k = 0 then (1 : ℝ) else rootPuctHi δ μ k)
      (mem_range.mpr (Nat.succ_pos 0))
    rw [ite_eq_left rfl] at h
    exact h
  · refine le_inf' _ _ (fun k hk => ?_)
    have hk0 : k = 0 := by
      have := mem_range.mp hk
      omega
    rw [ite_eq_left hk0]

/-- The running intersection does not change the lower endpoint. -/
theorem v2RunLo_eq (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    v2RunLo δ μ n = rootPuctLo δ μ n := by
  unfold v2RunLo
  apply le_antisymm
  · refine sup'_le _ _ (fun k hk => ?_)
    by_cases hk0 : k = 0
    · rw [ite_eq_left hk0]
      exact rootPuctLo_nonneg
    · rw [ite_eq_right hk0]
      exact rootPuctLo_mono hδ0 hδ (Nat.one_le_iff_ne_zero.mpr hk0)
        (Nat.lt_succ_iff.mp (mem_range.mp hk))
  · have h := le_sup' (fun k => if k = 0 then (0 : ℝ) else rootPuctLo δ μ k)
      (mem_range.mpr (Nat.lt_succ_self n))
    rw [ite_eq_right (Nat.one_le_iff_ne_zero.mp hn)] at h
    exact h

/-- The running intersection does not change the upper endpoint. -/
theorem v2RunHi_eq (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    v2RunHi δ μ n = rootPuctHi δ μ n := by
  unfold v2RunHi
  apply le_antisymm
  · have h := inf'_le (fun k => if k = 0 then (1 : ℝ) else rootPuctHi δ μ k)
      (mem_range.mpr (Nat.lt_succ_self n))
    rw [ite_eq_right (Nat.one_le_iff_ne_zero.mp hn)] at h
    exact h
  · refine le_inf' _ _ (fun k hk => ?_)
    by_cases hk0 : k = 0
    · rw [ite_eq_left hk0]
      exact rootPuctHi_le_one
    · rw [ite_eq_right hk0]
      exact rootPuctHi_anti hδ0 hδ (Nat.one_le_iff_ne_zero.mpr hk0)
        (Nat.lt_succ_iff.mp (mem_range.mp hk))

/-- **Lemma `lem:v2strict` (Nesting and actual endpoint changes), whole statement.**
For `δ ∈ (0, 1/2]` and the three arms with rewards `mu3 g` (`eq:v2means`; the empirical
mean on the deterministic tape of arm `a` is `mu3 g a` at every positive count):

1. `β_δ` strictly decreases on `[1, ∞)`;
2. the clipped intervals `[L_a, U_a]` at counts `1 ≤ j ≤ k` are nested, and each lies in
   the initial interval `[0, 1]`;
3. the running intersection, started from `[0, 1]`, changes none of them: at count `0` it
   is `[0, 1]`, and at every count `n ≥ 1` it equals the clipped interval at count `n`;
4. whenever `U_C < 1` at a count `j ≥ 1`, the upper endpoint of `C` (arm `2`) at every
   later count is strictly smaller.

No condition on `g` is needed. -/
theorem v2strict_literal (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (g : ℝ) :
    StrictAntiOn (rootPuctRadius δ) (Set.Ici 1) ∧
    (∀ (a : Fin 3) (j k : ℕ), 1 ≤ j → j ≤ k →
      0 ≤ rootPuctLo δ (mu3 g a) j ∧ rootPuctLo δ (mu3 g a) j ≤ rootPuctLo δ (mu3 g a) k ∧
      rootPuctHi δ (mu3 g a) k ≤ rootPuctHi δ (mu3 g a) j ∧ rootPuctHi δ (mu3 g a) j ≤ 1) ∧
    (∀ a : Fin 3, v2RunLo δ (mu3 g a) 0 = 0 ∧ v2RunHi δ (mu3 g a) 0 = 1) ∧
    (∀ (a : Fin 3) (n : ℕ), 1 ≤ n →
      v2RunLo δ (mu3 g a) n = rootPuctLo δ (mu3 g a) n ∧
      v2RunHi δ (mu3 g a) n = rootPuctHi δ (mu3 g a) n) ∧
    (∀ j k : ℕ, 1 ≤ j → j < k → rootPuctHi δ (mu3 g 2) j < 1 →
      rootPuctHi δ (mu3 g 2) k < rootPuctHi δ (mu3 g 2) j) :=
  ⟨rootPuctRadius_strictAntiOn hδ0 hδ,
    fun _ _ _ hj hjk => ⟨rootPuctLo_nonneg, rootPuctLo_mono hδ0 hδ hj hjk,
      rootPuctHi_anti hδ0 hδ hj hjk, rootPuctHi_le_one⟩,
    fun _ => ⟨v2RunLo_zero _ _, v2RunHi_zero _ _⟩,
    fun _ _ hn => ⟨v2RunLo_eq hδ0 hδ hn, v2RunHi_eq hδ0 hδ hn⟩,
    fun _ _ hj hjk h1 => rootPuctHi_strict hδ0 hδ hj hjk h1⟩

end V2Strict

/-! ## C. `prop:v35rootrates` -/

section RootRates

open MeasureTheory ProbabilityTheory

variable {ι : Type*}

/-- **Proposition `prop:v35rootrates` (Positive-variance root PUCT: almost-sure square-root
counts), one statement.**

`X i k` is the `k`-th element of the reward tape of action `i`: `[0,1]`-valued, pairwise
independent and identically distributed within the tape, with mean `∫ X i 0`.  On every
sample path the run follows the fixed-positive-prior PUCT rule `eq:v35onevertex`, where
`Q ω i n` is any value in `[0,1]` while `i` is unsampled and the empirical mean of the
first `N_i(n)` tape elements afterwards.  Then:

1. on every sample path every action is sampled infinitely often (its count eventually
   exceeds every bound);
2. almost surely, every action `i` with a positive gap (some `j` has larger mean) satisfies
   `(λ_i / (8 √2)) √t ≤ N_i(t) ≤ C √t` for all `t ≥ T_0`, where the lower constant
   `λ_i / (8 √2) > 0` and the threshold `T_0 = puctThreshold` are deterministic and the
   upper constant `C` depends on the sample path;
3. almost surely, if `j` has the unique largest mean then `t - C √t ≤ N_j(t) ≤ t` for all
   `t ≥ 1`, with `C` depending on the sample path.

No variance assumption is used (positive variance is permitted), and independence across
actions is not needed. -/
theorem v35rootrates_literal [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (lam : ι → ℝ) (hlam : ∀ j, 0 < lam j) (X : ι → ℕ → Ω → ℝ)
    (hbdd : ∀ i k ω, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (hindep : ∀ i, Pairwise (Function.onFun (fun f g => IndepFun f g P) (X i)))
    (hident : ∀ i k, IdentDistrib (X i k) (X i 0) P P)
    (sel : Ω → ℕ → ι) (Q : Ω → ι → ℕ → ℝ)
    (hQ0 : ∀ ω n j, pullCount (sel ω) j n = 0 → 0 ≤ Q ω j n ∧ Q ω j n ≤ 1)
    (hQmean : ∀ ω n j, 1 ≤ pullCount (sel ω) j n →
      Q ω j n = (pullCount (sel ω) j n : ℝ)⁻¹ *
        ∑ k ∈ range (pullCount (sel ω) j n), X j k ω)
    (hrule : ∀ ω n j,
      Q ω j n + lam j * √(n : ℝ) / (1 + (pullCount (sel ω) j n : ℝ)) ≤
        Q ω (sel ω n) n + lam (sel ω n) * √(n : ℝ) /
          (1 + (pullCount (sel ω) (sel ω n) n : ℝ))) :
    (∀ ω i (B : ℝ), ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → B ≤ (pullCount (sel ω) i t : ℝ)) ∧
    ∀ᵐ ω ∂P,
      (∀ i, (∃ j, ∫ ω', X i 0 ω' ∂P < ∫ ω', X j 0 ω' ∂P) →
        0 < lam i / (8 * √2) ∧ ∃ C : ℝ, ∀ t : ℕ, puctThreshold univ lam ≤ t →
          lam i / (8 * √2) * √(t : ℝ) ≤ (pullCount (sel ω) i t : ℝ) ∧
            (pullCount (sel ω) i t : ℝ) ≤ C * √(t : ℝ)) ∧
      (∀ j, (∀ i, i ≠ j → ∫ ω', X i 0 ω' ∂P < ∫ ω', X j 0 ω' ∂P) →
        ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t →
          (t : ℝ) - C * √(t : ℝ) ≤ (pullCount (sel ω) j t : ℝ) ∧
            (pullCount (sel ω) j t : ℝ) ≤ t) := by
  have hQ : ∀ ω n j, 0 ≤ Q ω j n ∧ Q ω j n ≤ 1 := by
    intro ω n j
    rcases Nat.eq_zero_or_pos (pullCount (sel ω) j n) with h0 | hpos
    · exact hQ0 ω n j h0
    · rw [hQmean ω n j hpos]
      have hNpos : (0 : ℝ) < (pullCount (sel ω) j n : ℝ) := by exact_mod_cast hpos
      have hs0 : 0 ≤ ∑ k ∈ range (pullCount (sel ω) j n), X j k ω :=
        sum_nonneg (fun k _ => (hbdd j k ω).1)
      have hs1 : ∑ k ∈ range (pullCount (sel ω) j n), X j k ω ≤
          (pullCount (sel ω) j n : ℝ) := by
        calc ∑ k ∈ range (pullCount (sel ω) j n), X j k ω
            ≤ ∑ k ∈ range (pullCount (sel ω) j n), (1 : ℝ) :=
              sum_le_sum (fun k _ => (hbdd j k ω).2)
          _ = (pullCount (sel ω) j n : ℝ) := by simp
      refine ⟨mul_nonneg (inv_nonneg.mpr hNpos.le) hs0, ?_⟩
      rw [inv_mul_le_iff₀ hNpos]
      linarith
  have hint : ∀ i, Integrable (X i 0) P := fun i =>
    Integrable.of_bound (hident i 0).aemeasurable_fst.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hbdd i 0 ω).1], (hbdd i 0 ω).2⟩))
  refine ⟨fun ω i B => pullCount_unbounded lam hlam (sel ω) (Q ω) (hQ ω) (hrule ω) i B, ?_⟩
  filter_upwards [root_puct_sqrt_rates_ae P lam hlam X hint hindep hident sel Q hQ hQmean
    hrule] with ω hω
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hij⟩ := hi
    obtain ⟨C, hC⟩ := hω.1 i j hij
    have hα : 0 < lam i / (8 * √2) := by
      have := hlam i
      positivity
    refine ⟨hα, C, fun t ht =>
      ⟨local_puct_revisit lam hlam (sel ω) (Q ω) (hQ ω) (hrule ω) t ht i, hC t ?_⟩⟩
    have h16 := (puctThreshold_spec univ lam (fun j _ => hlam j) (x := (t : ℝ))
      (by exact_mod_cast ht) (mem_univ i)).1
    have h1 : (1 : ℝ) ≤ (t : ℝ) := by linarith
    exact_mod_cast h1
  · obtain ⟨C, hC⟩ := hω.2 j hj
    refine ⟨C, fun t ht => ⟨hC t ht, ?_⟩⟩
    have hle : pullCount (sel ω) j t ≤ t := stepCount_le _ t
    exact_mod_cast hle

end RootRates

/-! ## D. `ce:v35prior` -/

section ZeroPrior

open MeasureTheory

/-- Tails of the two edges of the counterexample: both leave the internal node `0`. -/
def ceSrc : Fin 2 → Fin 3 := fun _ => 0

/-- Heads of the two edges: edge `0` ends in terminal `1`, edge `1` in terminal `2`. -/
def ceTgt : Fin 2 → Fin 3 := Fin.succ

/-- **Counterexample `ce:v35prior`, pathwise core.**  The graph has one internal node `0`
(the root) with two outgoing edges `0`, `1` ending in the terminals `1`, `2`; the weights
are `λ_0 ≥ 0` (the manuscript takes `λ_0 > 0`) and `λ_1 = 0`.  For every tape-driven run on
this graph (`TapeRun`: the contract of `thm:v35dag` except positivity of the weights, values
equal to running averages of the tape rewards and `0` while unvisited) with canonical
first-edge tie-breaking: edge `1` is never selected and terminal `2` is never sampled.
The tapes are arbitrary; in particular they may be Bernoulli with positive variance. -/
theorem zero_prior_no_coverage (lam : Fin 2 → ℝ) (h0 : 0 ≤ lam 0) (h1 : lam 1 = 0)
    (x : Fin 3 → ℕ → ℝ) (L : ℕ) {vis : ℕ → Fin 3 → Prop} {ch : ℕ → Fin 3 → Fin 2}
    {Q : Fin 2 → ℕ → ℝ} (h : TapeRun ceSrc ceTgt 0 lam x L vis ch Q)
    (htie : FirstEdgeTies ceSrc lam vis ch Q) :
    (∀ s, ch s 0 = 0) ∧ (∀ s, ¬ vis s 2) ∧ ∀ t, visitCount vis 2 t = 0 := by
  have hout0 : (outEdges ceSrc (0 : Fin 3)).Nonempty := ⟨0, mem_outEdges.mpr rfl⟩
  have hout : ∀ v : Fin 3, v ≠ 0 → ¬ (outEdges ceSrc v).Nonempty := by
    rintro v hv ⟨e, he⟩
    exact hv (mem_outEdges.mp he).symm
  have hsel : ∀ s, ch s 0 = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      have hec : edgeCount vis ch 0 1 s = 0 := by
        unfold edgeCount
        refine stepCount_eq_zero (fun i hi hp => ?_)
        have h2 := hp.2
        rw [ih i hi] at h2
        exact absurd h2 (by decide)
      have hQ1 : Q 1 s = 0 := by
        rw [h.Q_avg]
        unfold runAvg
        exact ite_eq_left hec
      have hs1 : runScore ceSrc lam Q vis ch 1 s = 0 := by
        unfold runScore
        rw [hQ1, h1]
        simp
      have hs0 : 0 ≤ runScore ceSrc lam Q vis ch 0 s := by
        unfold runScore
        have := (h.contract.Q_mem s 0).1
        positivity
      by_contra hne
      have hc1 : ch s 0 = 1 := Fin.eq_one_of_ne_zero _ hne
      have hle := htie s 0 (h.contract.root_vis s) 0 rfl (by rw [hc1, hs1]; exact hs0)
      rw [hc1] at hle
      exact absurd hle (by decide)
  have hwalk : ∀ s k, walkV ceSrc ceTgt 0 (ch s) (k + 1) = 1 := by
    intro s k
    induction k with
    | zero =>
        rw [walkV_succ, walkV_zero, ite_eq_left hout0, hsel s]
        rfl
    | succ k ih =>
        rw [walkV_succ, ih, ite_eq_right (hout 1 (by decide))]
  have hnv : ∀ s, ¬ vis s 2 := by
    intro s hv
    obtain ⟨k, hk⟩ := (h.walk s 2).mp hv
    cases k with
    | zero =>
        rw [walkV_zero] at hk
        exact absurd hk (by decide)
    | succ k =>
        rw [hwalk s k] at hk
        exact absurd hk (by decide)
  exact ⟨hsel, hnv, fun t => stepCount_eq_zero (fun i _ => hnv i)⟩

/-- **The conclusion of `thm:v35dag` fails** in the situation of `zero_prior_no_coverage`:
there are no `c > 0`, depth `H` and threshold `t₀` with `n_z(t) ≥ c t ^ (2 ^ (-H))` for all
`t ≥ t₀` at the terminal `z = 2`, and that terminal is not sampled infinitely often. -/
theorem zero_prior_dag_conclusion_fails (lam : Fin 2 → ℝ) (h0 : 0 ≤ lam 0) (h1 : lam 1 = 0)
    (x : Fin 3 → ℕ → ℝ) (L : ℕ) {vis : ℕ → Fin 3 → Prop} {ch : ℕ → Fin 3 → Fin 2}
    {Q : Fin 2 → ℕ → ℝ} (h : TapeRun ceSrc ceTgt 0 lam x L vis ch Q)
    (htie : FirstEdgeTies ceSrc lam vis ch Q) :
    (¬ ∃ c : ℝ, 0 < c ∧ ∃ H t0 : ℕ, ∀ t : ℕ, t0 ≤ t →
      c * (t : ℝ) ^ (1 / 2 ^ H : ℝ) ≤ (visitCount vis 2 t : ℝ)) ∧
    ¬ ∀ B : ℝ, ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → B ≤ (visitCount vis 2 t : ℝ) := by
  have hz := (zero_prior_no_coverage lam h0 h1 x L h htie).2.2
  constructor
  · rintro ⟨c, hc, H, t0, hall⟩
    have h1' := hall (t0 + 1) (Nat.le_succ t0)
    rw [hz] at h1'
    have hpos : (0 : ℝ) < ((t0 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos t0
    have := mul_pos hc (Real.rpow_pos_of_pos hpos (1 / 2 ^ H : ℝ))
    simp only [Nat.cast_zero] at h1'
    linarith
  · intro hall
    obtain ⟨t0, ht0⟩ := hall 1
    have h1' := ht0 t0 le_rfl
    rw [hz] at h1'
    simp only [Nat.cast_zero] at h1'
    linarith

/-- **Counterexample `ce:v35prior` on an arbitrary sample space.**  `B z k ω ∈ {0, 1}` is
the `k`-th reward of terminal `z` on the sample path `ω` (for instance Bernoulli tapes with
means strictly between `0` and `1`).  The tape of vertex `v` is `B 0` for terminal `1` and
`B 1` for terminal `2`.  Then:

* tape-driven runs with first-edge tie-breaking exist on every sample path, for every
  `λ_0 > 0` and `λ_1 = 0`;
* every such run satisfies all hypotheses of `thm:v35dag` except positivity of the weight
  of edge `1`: the contract `PUCTContract`, positive weight on every other edge, and a
  root-to-terminal path to each terminal;
* on every sample path (not merely almost surely) terminal `2` is never sampled, so the
  conclusion of `thm:v35dag` fails. -/
theorem zero_prior_counterexample {Ω : Type*} (lam0 : ℝ) (hlam0 : 0 < lam0)
    (B : Fin 2 → ℕ → Ω → ℝ) (hB : ∀ z k ω, B z k ω = 0 ∨ B z k ω = 1) :
    (∃ (vis : Ω → ℕ → Fin 3 → Prop) (ch : Ω → ℕ → Fin 3 → Fin 2) (Q : Ω → Fin 2 → ℕ → ℝ),
      ∀ ω, TapeRun ceSrc ceTgt 0 ![lam0, 0]
          (fun v k => if v = 1 then B 0 k ω else if v = 2 then B 1 k ω else 0) 1
          (vis ω) (ch ω) (Q ω) ∧ FirstEdgeTies ceSrc ![lam0, 0] (vis ω) (ch ω) (Q ω)) ∧
    ∀ (ω : Ω) (vis : ℕ → Fin 3 → Prop) (ch : ℕ → Fin 3 → Fin 2) (Q : Fin 2 → ℕ → ℝ),
      TapeRun ceSrc ceTgt 0 ![lam0, 0]
          (fun v k => if v = 1 then B 0 k ω else if v = 2 then B 1 k ω else 0) 1 vis ch Q →
      FirstEdgeTies ceSrc ![lam0, 0] vis ch Q →
      PUCTContract ceSrc ceTgt 0 ![lam0, 0] vis ch Q ∧
      (∀ e : Fin 2, e ≠ 1 → 0 < (![lam0, 0] : Fin 2 → ℝ) e) ∧
      (![lam0, 0] : Fin 2 → ℝ) 1 = 0 ∧
      (∀ z : Fin 2, IsPath ceSrc ceTgt [z] 0 (ceTgt z)) ∧
      (∀ s, ¬ vis s (ceTgt 1)) ∧ (∀ t, visitCount vis (ceTgt 1) t = 0) ∧
      (¬ ∃ c : ℝ, 0 < c ∧ ∃ H t0 : ℕ, ∀ t : ℕ, t0 ≤ t →
        c * (t : ℝ) ^ (1 / 2 ^ H : ℝ) ≤ (visitCount vis (ceTgt 1) t : ℝ)) ∧
      ¬ ∀ b : ℝ, ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → b ≤ (visitCount vis (ceTgt 1) t : ℝ) := by
  have hx : ∀ ω (v : Fin 3) (k : ℕ),
      (if v = 1 then B 0 k ω else if v = 2 then B 1 k ω else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    intro ω v k
    split_ifs
    · rcases hB 0 k ω with hb | hb <;> rw [hb] <;> constructor <;> norm_num
    · rcases hB 1 k ω with hb | hb <;> rw [hb] <;> constructor <;> norm_num
    · constructor <;> norm_num
  constructor
  · choose vis ch Q hrun using fun ω => exists_tapeRun ceSrc ceTgt 0 ![lam0, 0]
      (fun v k => if v = 1 then B 0 k ω else if v = 2 then B 1 k ω else 0) (hx ω) 1
    exact ⟨vis, ch, Q, hrun⟩
  · intro ω vis ch Q h htie
    have hl0 : (0 : ℝ) ≤ (![lam0, 0] : Fin 2 → ℝ) 0 := hlam0.le
    have hl1 : (![lam0, 0] : Fin 2 → ℝ) 1 = 0 := rfl
    have hnc := zero_prior_no_coverage _ hl0 hl1 _ 1 h htie
    have hfail := zero_prior_dag_conclusion_fails _ hl0 hl1 _ 1 h htie
    refine ⟨h.contract, ?_, hl1, ?_, hnc.2.1, hnc.2.2, hfail.1, hfail.2⟩
    · intro e he
      have he0 : e = 0 := by
        fin_cases e
        · rfl
        · exact absurd rfl he
      rw [he0]
      exact hlam0
    · intro z
      exact ⟨rfl, rfl⟩

/-- The two-point law on `Bool` with mass `q` at `true`. -/
def bernBool (q : ℝ) : Measure Bool :=
  ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

lemma bernBool_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsProbabilityMeasure (bernBool q) := by
  constructor
  simp only [bernBool, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma bernBool_true (q : ℝ) : bernBool q {true} = ENNReal.ofReal q := by
  simp [bernBool]

/-- **Counterexample `ce:v35prior` with Bernoulli terminals of positive variance.**  For
all success probabilities `p 0, p 1 ∈ (0, 1)` (the manuscript takes `p 0 = 1/2`) and every
`λ_0 > 0` there are a probability space, jointly independent reward tapes `B z k` with
values in `{0, 1}` and `P(B z k = 1) = p z` (so each reward has mean `p z ∈ (0, 1)` and
variance `p z (1 - p z) > 0`), and on every sample path a tape-driven PUCT run on the
two-edge graph with weights `(λ_0, 0)` and first-edge tie-breaking, such that terminal `2`
is never sampled on any sample path.  The other hypotheses of `thm:v35dag` hold by
`zero_prior_counterexample`. -/
theorem zero_prior_bernoulli (lam0 : ℝ) (hlam0 : 0 < lam0) (p : Fin 2 → ℝ)
    (hp : ∀ z, 0 < p z ∧ p z < 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : Fin 2 × ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (B i)) ∧
      (∀ i ω, B i ω = 0 ∨ B i ω = 1) ∧
      (∀ i, P {ω | B i ω = 1} = ENNReal.ofReal (p i.1)) ∧
      ProbabilityTheory.iIndepFun B P ∧
      ∃ (vis : Ω → ℕ → Fin 3 → Prop) (ch : Ω → ℕ → Fin 3 → Fin 2) (Q : Ω → Fin 2 → ℕ → ℝ),
        ∀ ω, TapeRun ceSrc ceTgt 0 ![lam0, 0]
            (fun v k => if v = 1 then B (0, k) ω else if v = 2 then B (1, k) ω else 0) 1
            (vis ω) (ch ω) (Q ω) ∧
          FirstEdgeTies ceSrc ![lam0, 0] (vis ω) (ch ω) (Q ω) ∧
          (∀ s, ¬ vis ω s (ceTgt 1)) ∧ ∀ t, visitCount (vis ω) (ceTgt 1) t = 0 := by
  have : ∀ i : Fin 2 × ℕ, IsProbabilityMeasure (bernBool (p i.1)) :=
    fun i => bernBool_prob (hp i.1).1.le (hp i.1).2.le
  obtain ⟨Ω, mΩ, P, Xb, hXm, hXlaw, hXind, hP⟩ :=
    ProbabilityTheory.exists_hasLaw_indepFun (ι := Fin 2 × ℕ) (fun _ => Bool)
      (fun i => bernBool (p i.1))
  have hval : ∀ (i : Fin 2 × ℕ) (ω : Ω),
      (if Xb i ω = true then (1 : ℝ) else 0) = 0 ∨ (if Xb i ω = true then (1 : ℝ) else 0) = 1 := by
    intro i ω
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨⟨vis, ch, Q, hrun⟩, hall⟩ := zero_prior_counterexample (Ω := Ω) lam0 hlam0
    (fun z k ω => if Xb (z, k) ω = true then (1 : ℝ) else 0) (fun z k ω => hval (z, k) ω)
  refine ⟨Ω, mΩ, P, fun i ω => if Xb i ω = true then (1 : ℝ) else 0, hP, ?_, hval, ?_, ?_,
    vis, ch, Q, fun ω => ?_⟩
  · intro i
    exact (Measurable.of_discrete (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
      (hXm i)
  · intro i
    have hset : {ω | (if Xb i ω = true then (1 : ℝ) else 0) = 1} = Xb i ⁻¹' {true} := by
      ext ω
      simp
    rw [hset, ← Measure.map_apply (hXm i) (measurableSet_singleton _), (hXlaw i).map_eq,
      bernBool_true]
  · exact hXind.comp (fun _ (b : Bool) => if b = true then (1 : ℝ) else 0)
      (fun _ => Measurable.of_discrete)
  · obtain ⟨hr, ht⟩ := hrun ω
    have hres := hall ω (vis ω) (ch ω) (Q ω) hr ht
    exact ⟨hr, ht, hres.2.2.2.2.1, hres.2.2.2.2.2.1⟩

end ZeroPrior

/-! ## E. Observed-reward tables for the funnel and common-core searches -/

section Observed

variable {Z : Type*} [DecidableEq Z]

/-- The reward observed by rollout `s`: the next unused element of the tape `X z` of the
terminal `z = term s` it reaches. -/
def obsReward (X : Z → ℕ → ℝ) (term : ℕ → Z) (s : ℕ) : ℝ :=
  X (term s) (uctCount term s (term s))

/-- Empirical mean of the rewards observed at terminal `z` among the first `t` rollouts. -/
def obsMean (X : Z → ℕ → ℝ) (term : ℕ → Z) (t : ℕ) (z : Z) : ℝ :=
  (∑ s ∈ (range t).filter (fun s => term s = z), obsReward X term s) / uctCount term t z

/-- The clipped Hoeffding interval of terminal `z` after `t` rollouts, built from the
observed rewards: `[0, 1]` when `z` is unobserved, otherwise radius `β(count)` around the
empirical mean, clipped to `[0, 1]`. -/
def obsRaw (β : ℕ → ℝ) (X : Z → ℕ → ℝ) (term : ℕ → Z) (t : ℕ) (z : Z) : ℝ × ℝ :=
  if uctCount term t z = 0 then (0, 1)
  else (max 0 (obsMean X term t z - β (uctCount term t z)),
    min 1 (obsMean X term t z + β (uctCount term t z)))

/-- The observed-reward table with running intersections: the intersection of the clipped
intervals `obsRaw` at all times `0, …, t` (time `0` contributes the initial `[0, 1]`). -/
def obsTab (β : ℕ → ℝ) (X : Z → ℕ → ℝ) (term : ℕ → Z) (t : ℕ) (z : Z) : ℝ × ℝ :=
  ((range (t + 1)).sup' ⟨0, mem_range.mpr t.succ_pos⟩ (fun s => (obsRaw β X term s z).1),
    (range (t + 1)).inf' ⟨0, mem_range.mpr t.succ_pos⟩ (fun s => (obsRaw β X term s z).2))

/-- The table defined from the true means `μ` (the common form of `funTab` and `coreTab`). -/
def detTab (β : ℕ → ℝ) (μ : Z → ℝ) (term : ℕ → Z) (t : ℕ) (z : Z) : ℝ × ℝ :=
  if uctCount term t z = 0 then (0, 1)
  else (max 0 (μ z - β (uctCount term t z)), min 1 (μ z + β (uctCount term t z)))

/-- On point-mass tapes every observed reward is the displayed reward of the terminal. -/
lemma obsReward_pointMass {X : Z → ℕ → ℝ} {μ : Z → ℝ} (hX : ∀ z k, X z k = μ z)
    (term : ℕ → Z) (s : ℕ) : obsReward X term s = μ (term s) := by
  unfold obsReward
  rw [hX]

/-- On point-mass tapes the clipped interval built from observed rewards is the one defined
from the true means. -/
lemma obsRaw_eq_detTab {X : Z → ℕ → ℝ} {μ : Z → ℝ} (hX : ∀ z k, X z k = μ z) (β : ℕ → ℝ)
    (term : ℕ → Z) (t : ℕ) (z : Z) : obsRaw β X term t z = detTab β μ term t z := by
  unfold obsRaw detTab
  by_cases h0 : uctCount term t z = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    have hmean : obsMean X term t z = μ z := by
      unfold obsMean
      exact fuMean_const term (obsReward X term) z (μ z) t
        (fun s hs => by rw [obsReward_pointMass hX, hs]) (by omega)
    rw [hmean]

/-- The intervals defined from the true means are nested when the radius is nonincreasing
on positive counts. -/
lemma detTab_nested {β : ℕ → ℝ} (hanti : ∀ j k, 1 ≤ j → j ≤ k → β k ≤ β j) (μ : Z → ℝ)
    (term : ℕ → Z) (z : Z) {s t : ℕ} (hst : s ≤ t) :
    (detTab β μ term s z).1 ≤ (detTab β μ term t z).1 ∧
      (detTab β μ term t z).2 ≤ (detTab β μ term s z).2 := by
  have hc := uctCount_mono term z hst
  unfold detTab
  by_cases h0 : uctCount term s z = 0
  · rw [ite_eq_left h0]
    by_cases h1 : uctCount term t z = 0
    · rw [ite_eq_left h1]
      exact ⟨le_rfl, le_rfl⟩
    · rw [ite_eq_right h1]
      exact ⟨le_max_left _ _, min_le_left _ _⟩
  · have h1 : uctCount term t z ≠ 0 := by omega
    rw [ite_eq_right h0, ite_eq_right h1]
    have := hanti _ _ (by omega : 1 ≤ uctCount term s z) hc
    exact ⟨max_le_max le_rfl (by linarith), min_le_min le_rfl (by linarith)⟩

/-- **Observed-reward table = true-mean table on point-mass tapes.**  If every element of
the tape of each terminal equals its displayed reward `μ z` and the radius is nonincreasing
on positive counts, then the table built from the observed rewards, with running
intersections, equals the table defined from the true means at every time.  In particular
the running intersection changes nothing. -/
theorem obsTab_eq_detTab {X : Z → ℕ → ℝ} {μ : Z → ℝ} (hX : ∀ z k, X z k = μ z) {β : ℕ → ℝ}
    (hanti : ∀ j k, 1 ≤ j → j ≤ k → β k ≤ β j) (term : ℕ → Z) (t : ℕ) (z : Z) :
    obsTab β X term t z = detTab β μ term t z := by
  unfold obsTab
  refine Prod.ext ?_ ?_
  · dsimp only
    apply le_antisymm
    · refine sup'_le _ _ (fun s hs => ?_)
      rw [obsRaw_eq_detTab hX]
      exact (detTab_nested hanti μ term z (Nat.lt_succ_iff.mp (mem_range.mp hs))).1
    · have h : (obsRaw β X term t z).1 ≤ (range (t + 1)).sup' ⟨0, mem_range.mpr t.succ_pos⟩
          (fun s => (obsRaw β X term s z).1) :=
        le_sup' (fun s => (obsRaw β X term s z).1) (mem_range.mpr (Nat.lt_succ_self t))
      rw [obsRaw_eq_detTab hX] at h
      exact h
  · dsimp only
    apply le_antisymm
    · have h : (range (t + 1)).inf' ⟨0, mem_range.mpr t.succ_pos⟩
          (fun s => (obsRaw β X term s z).2) ≤ (obsRaw β X term t z).2 :=
        inf'_le (fun s => (obsRaw β X term s z).2) (mem_range.mpr (Nat.lt_succ_self t))
      rw [obsRaw_eq_detTab hX] at h
      exact h
    · refine le_inf' _ _ (fun s hs => ?_)
      rw [obsRaw_eq_detTab hX]
      exact (detTab_nested hanti μ term z (Nat.lt_succ_iff.mp (mem_range.mp hs))).2

end Observed

/-! ### The funnel search (`thm:onpolicy-uct`) -/

section FunnelObserved

variable {δ g : ℝ}

/-- The table seen by the monitors of the funnel search at their step `k`, built from the
rewards observed along the search on the tapes `X`. -/
def funObsBox (δ : ℝ) (X : Fin 4 → ℕ → ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (k : ℕ) :
    Fin 4 → ℝ × ℝ :=
  obsTab (funRad δ) X (funTerm sel sub) (3 + k)

/-- The reward backed up by rollout `s` of a funnel search is the observed tape element. -/
theorem funnel_obsReward {X : Fin 4 → ℕ → ℝ} (hX : ∀ z k, X z k = funMu g z)
    (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (s : ℕ) :
    obsReward X (funTerm sel sub) s = funMu g (funTerm sel sub s) :=
  obsReward_pointMass hX _ s

/-- **Rewrite lemma (funnel).**  On point-mass tapes the observed-reward table equals
`funTab` at every time, for all selection sequences (in particular for every
`FunnelSearch`). -/
theorem funObsTab_eq (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {X : Fin 4 → ℕ → ℝ}
    (hX : ∀ z k, X z k = funMu g z) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) (z : Fin 4) :
    obsTab (funRad δ) X (funTerm sel sub) t z = funTab δ g sel sub t z :=
  obsTab_eq_detTab hX (fun _ _ hj hjk => funRad_anti hδ0 hδ1 hj hjk) _ t z

theorem funObsBox_eq (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {X : Fin 4 → ℕ → ℝ}
    (hX : ∀ z k, X z k = funMu g z) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) :
    funObsBox δ X sel sub = funBox δ g sel sub := by
  funext k z
  exact funObsTab_eq hδ0 hδ1 hX sel sub (3 + k) z

/-- Total work of the funnel run with the monitors reading the observed-reward table. -/
def funObsWork (s : Bool) (m : ℕ) (δ g : ℝ) (X : Fin 4 → ℕ → ℝ) (rule : ℕ → ℕ → Bool)
    (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (τ : ℕ) : ℕ :=
  ∑ t ∈ range τ, funRollout m rule sel sub t
    + monWork s (monFunnelCirc m) (funObsBox δ X sel sub) (g / 2) (τ - 3)

/-- **`thm:onpolicy-uct`, local-UCT half, with observed-reward tables.**  The statement of
`onpolicy_uct_funnel` with the monitors reading the table built from the rewards observed
along the search (empirical means, clipped Hoeffding intervals, running intersections) on
any tapes `X` whose elements all equal the displayed rewards `funMu g` (the manuscript's
point-mass reward model). -/
theorem onpolicy_uct_funnel_observed (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (m0 : ℕ) (c C : ℝ), 0 < c ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g : ℝ, g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (X : Fin 4 → ℕ → ℝ),
        (∀ z k, X z k = funMu g z) → FunnelSearch g sel sub →
        (∀ k, (monQuery (g / 2) (funObsBox δ X sel sub k)
              (monRun true (monFunnelCirc m) (funObsBox δ X sel sub) k)).1
            = (monQuery (g / 2) (funObsBox δ X sel sub k)
              (monRun false (monFunnelCirc m) (funObsBox δ X sel sub) k)).1) ∧
        (∀ k, funT0 δ - 3 < k →
          (2 : Fin 3) ∉ (monRun true (monFunnelCirc m) (funObsBox δ X sel sub) k).act) ∧
        ∃ τ : ℕ, 3 ≤ τ ∧
          (∀ k, k < τ - 3 → (monQuery (g / 2) (funObsBox δ X sel sub k)
            (monRun false (monFunnelCirc m) (funObsBox δ X sel sub) k)).1.stops = ∅) ∧
          (monQuery (g / 2) (funObsBox δ X sel sub (τ - 3))
            (monRun false (monFunnelCirc m) (funObsBox δ X sel sub) (τ - 3))).1.stops = {0} ∧
          64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < τ ∧ τ ≤ m ∧
          (funObsWork true m δ g X rule sel sub τ : ℝ) ≤ C * m ∧
          c * m * Real.log m ≤ funObsWork false m δ g X rule sel sub τ := by
  obtain ⟨m0, c, C, hc, H⟩ := onpolicy_uct_funnel hδ0 hδ1
  refine ⟨m0, c, C, hc, ?_⟩
  intro m hm g hg rule sel sub X hX h
  have e : funObsBox δ X sel sub = funBox δ g sel sub := funObsBox_eq hδ0 hδ1.le hX sel sub
  have ew : ∀ s τ, funObsWork s m δ g X rule sel sub τ = funWork s m δ g rule sel sub τ := by
    intro s τ
    unfold funObsWork funWork
    rw [e]
  simp only [e, ew]
  exact H m hm g hg rule sel sub h

end FunnelObserved

/-! ### The common-core search (`thm:ta-core`) -/

section CoreObserved

/-- The table seen by the monitors of the common-core search at their step `k`, built from
the rewards observed along the search on the tapes `X`. -/
def coreObsBox (r : ℕ) (β : ℕ → ℝ) (X : CoreZ r → ℕ → ℝ) (zt : ℕ → CoreZ r) (k : ℕ) :
    CoreZ r → ℝ × ℝ :=
  obsTab β X zt (r + 1 + k)

/-- The reward backed up by rollout `s` of a common-core search is the observed tape
element. -/
theorem core_obsReward {r : ℕ} {X : CoreZ r → ℕ → ℝ} (hX : ∀ z k, X z k = coreReward r z)
    (zt : ℕ → CoreZ r) (s : ℕ) : obsReward X zt s = coreReward r (zt s) :=
  obsReward_pointMass hX _ s

/-- **Rewrite lemma (common core).**  On point-mass tapes the observed-reward table equals
`coreTab` at every time, for every sequence of reached terminals (in particular for every
`CoreSearch`), whenever the radius is nonincreasing on positive counts. -/
theorem coreObsTab_eq {r : ℕ} {β : ℕ → ℝ} (hanti : ∀ j k, 1 ≤ j → j ≤ k → β k ≤ β j)
    {X : CoreZ r → ℕ → ℝ} (hX : ∀ z k, X z k = coreReward r z) (zt : ℕ → CoreZ r) (t : ℕ)
    (z : CoreZ r) : obsTab β X zt t z = coreTab r β zt t z :=
  obsTab_eq_detTab hX hanti _ t z

theorem coreObsBox_eq {r : ℕ} {β : ℕ → ℝ} (hanti : ∀ j k, 1 ≤ j → j ≤ k → β k ≤ β j)
    {X : CoreZ r → ℕ → ℝ} (hX : ∀ z k, X z k = coreReward r z) (zt : ℕ → CoreZ r) :
    coreObsBox r β X zt = coreBox r β zt := by
  funext k z
  exact coreObsTab_eq hanti hX zt (r + 1 + k) z

/-- Total work of the common-core run with the monitors reading the observed-reward
table. -/
def coreObsTotalWork (s : Bool) (r : ℕ) [NeZero r] (β : ℕ → ℝ) (X : CoreZ r → ℕ → ℝ)
    (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r) (K : ℕ) : ℕ :=
  2 * ((coreHub r).uctSize + 3 * r + 1) + ∑ u ∈ range (r + 1 + K), coreRollout r rule u (sel u)
    + coreWork s (coreHub r) (coreObsBox r β X zt) K

/-- **`thm:ta-core` with the two monitors coupled, with observed-reward tables.**  The
statement of `ta_core_coupled` with the monitors reading the table built from the rewards
observed along the search (empirical means, clipped Hoeffding intervals, running
intersections) on any tapes `X` whose elements all equal the displayed rewards
`coreReward`. -/
theorem ta_core_coupled_observed {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r)
        (X : CoreZ r → ℕ → ℝ), (∀ z k, X z k = coreReward r z) →
      CoreSearch r rule sel zt →
        (∀ k a, coreStops (coreRun true (coreHub r) (coreObsBox r (coreRadius r δ) X zt) k)
            (coreObsBox r (coreRadius r δ) X zt k) a ↔
          coreStops (coreRun false (coreHub r) (coreObsBox r (coreRadius r δ) X zt) k)
            (coreObsBox r (coreRadius r δ) X zt k) a) ∧
        (∀ (s : Bool) k a,
          a ∈ (coreRun s (coreHub r) (coreObsBox r (coreRadius r δ) X zt) k).act →
          (coreRun s (coreHub r) (coreObsBox r (coreRadius r δ) X zt) k).lo
              (coreObsBox r (coreRadius r δ) X zt k) a
                = coreL r (coreObsBox r (coreRadius r δ) X zt) k a ∧
            (coreRun s (coreHub r) (coreObsBox r (coreRadius r δ) X zt) k).hi
              (coreObsBox r (coreRadius r δ) X zt k) a
                = coreU r (coreObsBox r (coreRadius r δ) X zt) k a) ∧
        ∃ τ : ℕ,
          (∀ s : Bool,
            coreStops (coreRun s (coreHub r) (coreObsBox r (coreRadius r δ) X zt) τ)
              (coreObsBox r (coreRadius r δ) X zt τ) (Fin.last r)) ∧
          (∀ (s : Bool) k, k < τ → ∀ a,
            ¬ coreStops (coreRun s (coreHub r) (coreObsBox r (coreRadius r δ) X zt) k)
              (coreObsBox r (coreRadius r δ) X zt k) a) ∧
          (∀ (s : Bool) k a,
            coreStops (coreRun s (coreHub r) (coreObsBox r (coreRadius r δ) X zt) k)
              (coreObsBox r (coreRadius r δ) X zt k) a → a = Fin.last r) ∧
          ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
          (∀ s : Bool, (coreObsTotalWork s r (coreRadius r δ) X rule sel zt τ : ℝ)
            ≤ B * (r : ℝ) ^ 2 * Real.log r) ∧
          r ^ 3 ≤ ∑ i : Fin r, (coreLoseSupp r i).card := by
  obtain ⟨A, B, hA, hB, H⟩ := ta_core_coupled hδ0 hδ1
  refine ⟨A, B, hA, hB, ?_⟩
  intro r _ hr rule sel zt X hX h
  have e : coreObsBox r (coreRadius r δ) X zt = coreBox r (coreRadius r δ) zt :=
    coreObsBox_eq (fun j k hj hjk => coreRadius_anti hδ0 hδ1.le (by omega) hj hjk) hX zt
  have ew : ∀ s K, coreObsTotalWork s r (coreRadius r δ) X rule sel zt K =
      coreTotalWork s r (coreRadius r δ) rule sel zt K := by
    intro s K
    unfold coreObsTotalWork coreTotalWork
    rw [e]
  simp only [e, ew]
  exact H r hr rule sel zt h

end CoreObserved

end

end LiteralE6

end JointRootCert
