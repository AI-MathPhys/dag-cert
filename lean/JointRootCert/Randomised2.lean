/-
The unknown-variance converses for the manuscript's concrete instance, in terms of regret, for
randomised procedures.

Manuscript results covered (for procedures with internal randomisation):

* `thm:v34-converse` "Unknown-variance nuisance-KL lower bound for one correct answer":
  `rv34_converse_regret`;
* `thm:v34-converse-main` "Matching unknown-variance converse with a unique correct action":
  `rv34_converse_main_regret`.

These are the randomised versions of `LiteralD2d.Problem.v34_converse_regret` and
`LiteralD2d.Problem.v34_converse_main_regret`.  The model is that of `RandomisedGauss.lean`:
a randomised sampler `RGSampler` and decision rule `RGDecision` with seed law `ν`.
`RCorrect` is `(ε, δ)`-correctness over the fixed-feature model with arbitrary positive unknown
variances, with probabilities over observations and seed: at every parameter `u`, every
positive variance vector and every horizon, the probability of having halted with an action of
regret above `ε` at `u` is at most `δ`.  For a deterministic procedure it is
`LiteralD2d.Problem.Correct` (`rcorrect_const`).
-/
import JointRootCert.RandomisedGauss
import JointRootCert.LiteralD2d

namespace JointRootCert

namespace RandG

namespace Regret

open MeasureTheory ProbabilityTheory Finset Filter Topology GaussStopped LiteralD2d
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

variable {X A Z E : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X] [MeasurableSpace A]
  [MeasurableSingletonClass A] {Sd : Type*} [MeasurableSpace Sd]

/-- The event, jointly in the seed and the horizon-`n` transcript, "halted with an action whose
regret at `u` exceeds `ε`". -/
def wrongSet (G : Problem X A Z E) (R : RGSampler X Sd) (D : RGDecision A Sd) (u : E) (n : ℕ) :
    Set (Sd × (Fin n → ℝ)) :=
  {p | halted (R.run p.1) (List.ofFn p.2) = true ∧
    G.ε < G.reg (decAt (R.run p.1) (D.run p.1) (List.ofFn p.2)) u}

/-- `(ε, δ)`-correctness of a randomised procedure over the fixed-feature Gaussian model with
arbitrary positive unknown variances (probabilities over observations and seed). -/
def RCorrect (G : Problem X A Z E) (ν : Measure Sd) (R : RGSampler X Sd) (D : RGDecision A Sd)
    (δ : ℝ) : Prop :=
  ∀ (u : E) (s : X → ℝ), (∀ x, 0 < s x) → ∀ n : ℕ,
    rlaw ν R (fun x => G.pred x u) s n (wrongSet G R D u n) ≤ δ

/-- For a deterministic procedure, `RCorrect` is `LiteralD2d.Problem.Correct`. -/
lemma rcorrect_const (G : Problem X A Z E) (ν : Measure Sd) [IsProbabilityMeasure ν]
    (S : GSampler X) (D : GDecision A) (δ : ℝ) :
    RCorrect G ν (RGSampler.const S) (RGDecision.const D) δ ↔ G.Correct S D δ := by
  simp [RCorrect, Problem.Correct, rlaw, wrongSet, RGSampler.const, RGDecision.const]

lemma measurableSet_wrongSet [Countable A] (G : Problem X A Z E) (R : RGSampler X Sd)
    (D : RGDecision A Sd) (u : E) (n : ℕ) : MeasurableSet (wrongSet G R D u n) := by
  have e : wrongSet G R D u n = ⋃ a ∈ {a : A | G.ε < G.reg a u},
      {p : Sd × (Fin n → ℝ) | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n} := by
    ext p
    simp only [wrongSet, ansSet, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h2, h1, rfl⟩
    · rintro ⟨a, ha, h1, rfl⟩
      exact ⟨h1, ha⟩
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurableSet_jans R D a n

/-- If every action other than `a` has regret above `ε` at `u`, halting is split between
answering `a` and answering wrongly. -/
lemma rlaw_halted_le [Countable A] (G : Problem X A Z E) (ν : Measure Sd) [IsProbabilityMeasure ν]
    (R : RGSampler X Sd) (D : RGDecision A Sd) (a : A) (u : E)
    (h : ∀ b, b ≠ a → G.ε < G.reg b u) (μ v : X → ℝ) (n : ℕ) :
    rlaw ν R μ v n {p | halted (R.run p.1) (List.ofFn p.2) = true}
      ≤ rprobAns ν R D a μ v n + rlaw ν R μ v n (wrongSet G R D u n) := by
  have hA := integrable_law_real ν R μ v n (measurableSet_jans R D a n)
  have hW := integrable_law_real ν R μ v n (measurableSet_wrongSet G R D u n)
  have hle := integral_mono (integrable_law_real ν R μ v n (measurableSet_jhalt R n))
    (hA.add hW) fun s => by
      refine (measureReal_mono (fun y hy => ?_)).trans (measureReal_union_le _ _)
      by_cases hd : decAt (R.run s) (D.run s) (List.ofFn y) = a
      · exact Or.inl ⟨hy, hd⟩
      · exact Or.inr ⟨hy, h _ hd⟩
  simp only [Pi.add_apply] at hle
  rw [integral_add hA hW] at hle
  exact hle

variable [Fintype A] [Nonempty X]

/-- **Theorem `thm:v34-converse` for the paper's instance, in terms of regret, for randomised
procedures.**  The true parameter is `θ`, the true variances `v > 0`; every action other than
`astar` has regret above `ε` at `θ`; every action has an unscreened component;
`C_* = max_a C_a^* > 0` for the paper's polyhedra.  For every randomised procedure `(R, D)`
with seed law `ν` that is `(ε, δ)`-correct over the model (`RCorrect`), `δ ∈ (0, 1/2)`:
`E_{θ,v} τ ≥ kl(1 - δ, δ) / C_*` in `[0, ∞]` (expectation over observations and seed).  No
hypothesis on the stopping time. -/
theorem rv34_converse_regret (G : Problem X A Z E) (hJ : ∀ a, (G.J a).Nonempty) (astar : A)
    (θ : E) {v : X → ℝ} (hv : ∀ x, 0 < v x) (huniq : ∀ a, a ≠ astar → G.ε < G.reg a θ)
    (hCpos : 0 < univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v))
    (ν : Measure Sd) [IsProbabilityMeasure ν] (R : RGSampler X Sd) (D : RGDecision A Sd)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (hcorr : RCorrect G ν R D δ) :
    ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)) ≤
      rexpTau ν R (fun x => G.pred x θ) v := by
  classical
  set μ : X → ℝ := fun x => G.pred x θ with hμ
  by_cases htop : rexpTau ν R μ v = ⊤
  · rw [htop]; exact le_top
  have h0 : 0 ≤ actGameStar (G.J astar) (hJ astar) (G.Hc astar) G.pred μ v := by
    obtain ⟨x0⟩ := ‹Nonempty X›
    exact (actGame_nonneg (single_mem_simplex x0).1 hv).trans
      (actGame_le_star (G.J astar) (hJ astar) (G.Hc astar) G.pred (single_mem_simplex x0) hv)
  have heq := v34_Cstar_eq astar G.J hJ G.Hc G.pred hv (G.hinc_of_unique huniq) h0
  rw [heq] at hCpos ⊢
  refine rv34_converse ν R D astar (G.J astar) (hJ astar) (G.Hc astar) (G.Hs astar) G.pred
    (fun x => G.pred_continuous x) hv (fun z hz => G.Hc_nonempty hz)
    (fun z hz => G.Hc_subset_closure hz) hδ0 hδ ?_ ?_ hCpos
  · intro η hη
    set Tf := (rexpTau ν R μ v).toReal with hTf
    have hTle : ∀ n, rexpTime ν R μ v n ≤ Tf := rexpTime_le_of_ne_top ν R μ v htop
    obtain ⟨n, hn⟩ := exists_nat_gt (Tf / η)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg ENNReal.toReal_nonneg hη.le) hn
    refine ⟨n, ?_⟩
    have h1 := rnot_halted_mul_le ν R μ v n
    have h2 : 1 - rlaw ν R μ v n {p | halted (R.run p.1) (List.ofFn p.2) = true} ≤ η := by
      have h3 : Tf < n * η := (div_lt_iff₀ hη).mp hn
      have h4 : (n : ℝ) * (1 - rlaw ν R μ v n {p | halted (R.run p.1) (List.ofFn p.2) = true})
          ≤ n * η := by
        have := hTle n
        linarith
      exact le_of_mul_le_mul_left h4 hn0
    have h4 := rlaw_halted_le G ν R D astar θ huniq μ v n
    have h5 := hcorr θ v hv n
    linarith
  · intro z hz u hu s hs n
    rw [rprobAns_eq_rlaw]
    refine (rlaw_mono ν R _ s n (measurableSet_jans R D astar n)
      (measurableSet_wrongSet G R D u n) ?_).trans (hcorr u s hs n)
    rintro p ⟨hp1, hp2⟩
    refine ⟨hp1, ?_⟩
    rw [hp2]
    exact G.regret_gt_iff.mpr ⟨z, hz, hu⟩

/-- **Theorem `thm:v34-converse-main` for the paper's instance, in terms of regret, for
randomised procedures.**  Under the hypotheses of `rv34_converse_regret`, for every family of
randomised procedures `(R δ, D δ)` with seed laws `ν δ` that is `(ε, δ)`-correct over the model
for each `δ ∈ (0, 1/2)`: `E τ_δ ≥ kl(1 - δ, δ) / C_*`, and
`liminf_{δ ↓ 0} E τ_δ / log (1 / δ) ≥ 1 / C_*`, in the form: for every `c < 1 / C_*`,
eventually `c log (1 / δ) ≤ E τ_δ`. -/
theorem rv34_converse_main_regret (G : Problem X A Z E) (hJ : ∀ a, (G.J a).Nonempty)
    (astar : A) (θ : E) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    (huniq : ∀ a, a ≠ astar → G.ε < G.reg a θ)
    (hCpos : 0 < univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v))
    (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RGSampler X Sd) (D : ℝ → RGDecision A Sd)
    (hcorr : ∀ δ, 0 < δ → δ < 1 / 2 → RCorrect G (ν δ) (R δ) (D δ) δ) :
    (∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)) ≤
        rexpTau (ν δ) (R δ) (fun x => G.pred x θ) v) ∧
    ∀ c : ℝ, c < 1 / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v) →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (c * Real.log (1 / δ)) ≤ rexpTau (ν δ) (R δ) (fun x => G.pred x θ) v := by
  have hfin : ∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)) ≤
        rexpTau (ν δ) (R δ) (fun x => G.pred x θ) v := fun δ hδ0 hδ =>
    rv34_converse_regret G hJ astar θ hv huniq hCpos (ν δ) (R δ) (D δ) hδ0 hδ
      (hcorr δ hδ0 hδ)
  refine ⟨hfin, fun c hc => ?_⟩
  have hev := liminf_coefficient (Eτ := fun δ => klBin (1 - δ) δ /
    univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v))
    hCpos (fun δ _ _ => le_rfl) hc
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ h1 h2
  exact (ENNReal.ofReal_le_ofReal h1).trans (hfin δ h2.1 h2.2)

end

end Regret

end RandG

end JointRootCert
