/-
The unknown-variance results for the manuscript's concrete instance, in terms of regret
(Theorems `thm:v34-action-local`, `thm:v34-adaptive`, `thm:v34-converse-main`,
`thm:v34-converse`).

`Problem` holds the data of the fixed-feature model: terminal features `φ_z`, query features
`h_x`, the supports `S(a)` of the root actions, and `ε ≥ 0`.  From it:

* `Problem.Hc a z = {u | ∀ y ∈ S(a), ⟨φ_z - φ_y, u⟩ ≥ ε}`, the closed invalidating polyhedron
  `𝓗_{a,z}`, and `Problem.Hs a z`, its strict version;
* `Problem.pred x u = ⟨h_x, u⟩`;
* `Problem.J a`, the structurally unscreened outside components: `z ∉ S(a)` whose feature is
  outside the convex hull of the inside features, equivalently whose strict component is
  nonempty (`mem_J`, `mem_J_iff_nonempty`);
* `Problem.reg a θ`, the regret of `a` at the parameter `θ`.

Facts: `regret_gt_iff` (regret above `ε` iff `θ` lies in some unscreened strict component),
`exists_of_regret_gt` (then `θ` lies in some unscreened closed component), `regret_ge_of_mem_Hc`,
`Hc_subset_closure`, `Hc_nonempty`, `hinc_of_unique`.

Theorems, for this instance:

* `action_local_regret`: `(ε, δ)`-safety of an arbitrary predictable policy, "incorrect"
  meaning regret above `ε` (from `LiteralD2a`);
* `v34_adaptive_regret`: `thm:v34-adaptive` (from `LiteralD2c`);
* `v34_converse_regret`, `v34_converse_main_regret`: the converses, for procedures that are
  `(ε, δ)`-correct in the sense `Problem.Correct` (at every parameter and every positive
  variance vector, the probability of halting with an action of regret above `ε` is at most
  `δ`), with a unique correct action.  Samplers are deterministic functions of the history, as
  in `GaussianStopped.lean`.

This file imports `LiteralD2a` and `LiteralD2c`.
-/
import JointRootCert.LiteralD2a
import JointRootCert.LiteralD2c
import JointRootCert.GaussianStopped
import JointRootCert.GaussianInfo

namespace JointRootCert

namespace LiteralD2d

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

/-- The fixed-feature root model: terminal features `φ`, query features `h`, action supports
`supp` (nonempty), and the accuracy `ε ≥ 0`. -/
structure Problem (X A Z E : Type*) where
  φ : Z → E
  h : X → E
  supp : A → Finset Z
  hsupp : ∀ a, (supp a).Nonempty
  ε : ℝ
  hε : 0 ≤ ε

namespace Problem

variable {X A Z E : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (G : Problem X A Z E)

/-- The regret of the root action `a` at the parameter `θ`. -/
def reg (a : A) (θ : E) : ℝ := regret (G.supp a) (G.hsupp a) (env G.φ θ)

/-- The closed invalidating polyhedron `𝓗_{a,z} = {u | ∀ y ∈ S(a), ⟨φ_z - φ_y, u⟩ ≥ ε}`. -/
def Hc (a : A) (z : Z) : Set E := closedComp G.φ (G.supp a) G.ε z

/-- The strict invalidating component `{u | ∀ y ∈ S(a), ⟨φ_z - φ_y, u⟩ > ε}`. -/
def Hs (a : A) (z : Z) : Set E := strictComp G.φ (G.supp a) G.ε z

/-- The query mean `hₓᵀ u`. -/
def pred (x : X) (u : E) : ℝ := ⟪G.h x, u⟫

open Classical in
/-- The structurally unscreened outside components `J_a`. -/
def J (a : A) : Finset Z := univ.filter fun z => z ∈ hullScreen G.φ (G.supp a)

lemma mem_Hc {a : A} {z : Z} {u : E} :
    u ∈ G.Hc a z ↔ ∀ y ∈ G.supp a, G.ε ≤ ⟪G.φ z - G.φ y, u⟫ := Iff.rfl

lemma mem_Hs {a : A} {z : Z} {u : E} :
    u ∈ G.Hs a z ↔ ∀ y ∈ G.supp a, G.ε < ⟪G.φ z - G.φ y, u⟫ := Iff.rfl

lemma mem_J {a : A} {z : Z} :
    z ∈ G.J a ↔ z ∉ G.supp a ∧ G.φ z ∉ convexHull ℝ (G.φ '' (G.supp a : Set Z)) := by
  classical
  unfold J
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact Iff.rfl

/-- `J_a` consists of the outside terminals whose strict component is nonempty. -/
lemma mem_J_iff_nonempty {a : A} {z : Z} :
    z ∈ G.J a ↔ z ∉ G.supp a ∧ (G.Hs a z).Nonempty := by
  rw [mem_J]
  exact and_congr_right fun _ => (strictComp_nonempty_iff G.hε z).symm

/-- **Regret above `ε` iff the parameter lies in an unscreened strict component.** -/
theorem regret_gt_iff {a : A} {θ : E} :
    G.ε < G.reg a θ ↔ ∃ z ∈ G.J a, θ ∈ G.Hs a z := by
  classical
  have h : θ ∈ strictAlt G.φ (G.supp a) (G.hsupp a) G.ε ↔ ∃ z ∈ G.J a, θ ∈ G.Hs a z := by
    rw [strictAlt_eq_iUnion (G.hsupp a) G.hε]
    simp [J, Hs]
  exact h

/-- **If the regret of `a` exceeds `ε`, the parameter lies in one of the unscreened closed
invalidating polyhedra of `a`.** -/
theorem exists_of_regret_gt {a : A} {θ : E} (h : G.ε < G.reg a θ) :
    ∃ z ∈ G.J a, θ ∈ G.Hc a z := by
  obtain ⟨z, hz, hθ⟩ := G.regret_gt_iff.mp h
  exact ⟨z, hz, strictComp_subset_closedComp hθ⟩

/-- A parameter in a closed invalidating polyhedron of `a` gives regret at least `ε`. -/
theorem regret_ge_of_mem_Hc {a : A} {z : Z} {θ : E} (hθ : θ ∈ G.Hc a z) : G.ε ≤ G.reg a θ := by
  obtain ⟨y, hy, hval⟩ := Finset.exists_mem_eq_sup' (G.hsupp a) (env G.φ θ)
  have h1 := hθ y hy
  rw [inner_sub_eq_env] at h1
  have h2 := le_gmax (env G.φ θ) z
  have h3 : val (G.supp a) (G.hsupp a) (env G.φ θ) = env G.φ θ y := hval
  unfold reg regret
  linarith

lemma Hs_nonempty {a : A} {z : Z} (hz : z ∈ G.J a) : (G.Hs a z).Nonempty :=
  (G.mem_J_iff_nonempty.mp hz).2

lemma Hc_nonempty {a : A} {z : Z} (hz : z ∈ G.J a) : (G.Hc a z).Nonempty :=
  (G.Hs_nonempty hz).mono strictComp_subset_closedComp

/-- **Each unscreened closed component is the closure of its strict component.** -/
theorem Hc_subset_closure {a : A} {z : Z} (hz : z ∈ G.J a) : G.Hc a z ⊆ closure (G.Hs a z) :=
  (closure_strictComp (G.Hs_nonempty hz)).ge

/-- **The uniqueness encoding from "a unique correct action".**  If every action other than
`astar` has regret above `ε` at `θ`, then for each of them `θ` lies in one of its unscreened
closed components. -/
theorem hinc_of_unique {astar : A} {θ : E} (huniq : ∀ a, a ≠ astar → G.ε < G.reg a θ) :
    ∀ a, a ≠ astar → ∃ z ∈ G.J a, ∃ θ' ∈ G.Hc a z, ∀ x : X, G.pred x θ' = G.pred x θ :=
  fun a ha => by
    obtain ⟨z, hz, hθ⟩ := G.exists_of_regret_gt (huniq a ha)
    exact ⟨z, hz, θ, hθ, fun _ => rfl⟩

lemma pred_continuous (x : X) : Continuous (G.pred x) := by
  unfold pred
  fun_prop

/-- The instance of `LiteralD2c` for this model at the true parameter `θ` and the true
variances `v`. -/
def inst (hJ : ∀ a, (G.J a).Nonempty) (θ : E) (v : X → ℝ) : LiteralD2c.Instance X A Z E :=
  ⟨G.J, hJ, G.Hc, G.pred, fun x => G.pred x θ, v⟩

/-- `T` is a tracker for this model: its root-action data are the paper's. -/
structure IsTracker (G : Problem X A Z E) (T : Tracker X A Z E) : Prop where
  J_eq : T.J = G.J
  H_eq : T.H = G.Hc
  pred_eq : T.pred = G.pred

lemma inst_eq {T : Tracker X A Z E} (hT : G.IsTracker T) (hJ : ∀ a, (G.J a).Nonempty) (θ : E)
    (v : X → ℝ) : T.inst (fun x => T.pred x θ) v = G.inst hJ θ v := by
  obtain ⟨h1, h2, h3⟩ := hT
  cases T
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-! ### Theorem `thm:v34-action-local` for the instance -/

section ActionLocal

variable [Fintype X] [Fintype A] [DecidableEq A] {Ω : Type*} [MeasurableSpace Ω]

/-- **`(ε, δ)`-safety of action-local stopping, in terms of regret.**  For an arbitrary
predictable policy with sound certified bounds for the paper's polyhedra, on intrinsic tapes
`Y x n ~ N(⟨h_x, θ⟩, vₓ)` with arbitrary positive variances: the probability of stopping and
returning an action whose regret at `θ` exceeds `ε` is at most `δ`. -/
theorem action_local_regret (π : LiteralD2a.Policy X A Z) (hp : π.Predictable)
    (hs : π.Sound G.J G.Hc G.pred) (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : E) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal ⟪G.h x, θ⟫ (v x).toNNReal) P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | π.Stops G.J (tapeOf Y ω) δ ∧
        G.ε < G.reg (π.returned G.J (tapeOf Y ω) δ) θ} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans
    (LiteralD2a.Policy.safe hp hs P hYm hind θ hv (fun x n => hlaw x n) hδ)
  rintro ω ⟨hstop, hreg⟩
  exact ⟨hstop, G.exists_of_regret_gt hreg⟩

end ActionLocal

/-! ### Theorem `thm:v34-adaptive` for the instance -/

section Adaptive

variable [Fintype X] [Nonempty X] [DecidableEq X] [Fintype A] [Nonempty A] [DecidableEq A]
  {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem `thm:v34-adaptive` for the paper's instance, in terms of regret.**

`G` is the fixed-feature root model, `T` a tracker for it (`IsTracker`) meeting the oracle
contracts with Borel allocation oracles; every action has an unscreened component (`hJ`; this
is implied by `C_* < ∞`); the observations `Y x n` are measurable and jointly independent with
`Y x n ~ N(⟨h_x, θ⟩, vₓ)`, `vₓ > 0`; `C_* > 0`, where `C_*` and `D_s` are the constants of the
instance `G.inst hJ θ v` (`LiteralD2c.Instance.Cstar`, `LiteralD2c.Instance.Ds`).

1. For every `δ > 0`, the probability of stopping and returning an action whose regret at `θ`
   exceeds `ε` is at most `δ`, and the procedure stops almost surely.
2. For every `s ∈ (0, 1]` and `δ ∈ (0, 1)`,
   `E τ_δ ≤ D_s + (1 + s) / C_* · log (1 / δ)`.
3. For every `c > 1 / C_*`, eventually as `δ ↓ 0`, `E τ_δ ≤ c log (1 / δ)`. -/
theorem v34_adaptive_regret (T : Tracker X A Z E) (hT : G.IsTracker T) (hc : T.Contract)
    (hm : T.Meas) (hJ : ∀ a, (G.J a).Nonempty) (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : E) {v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal ⟪G.h x, θ⟫ (v x).toNNReal) P)
    (hC : 0 < (G.inst hJ θ v).Cstar) :
    (∀ δ : ℝ, 0 < δ →
      P {ω | LiteralD2c.Stops T (tapeOf Y ω) δ ∧
          G.ε < G.reg (LiteralD2c.returned T (tapeOf Y ω) δ) θ} ≤ ENNReal.ofReal δ ∧
      P {ω | ¬ LiteralD2c.Stops T (tapeOf Y ω) δ} = 0) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, LiteralD2c.tau T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal ((G.inst hJ θ v).Ds s +
          (1 + s) / (G.inst hJ θ v).Cstar * Real.log (1 / δ))) ∧
    ∀ c : ℝ, 1 / (G.inst hJ θ v).Cstar < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, LiteralD2c.tau T (tapeOf Y ω) δ ∂P).toReal ≤ c * Real.log (1 / δ) := by
  have hinst := G.inst_eq hT hJ θ v
  have hlaw' : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P := by
    intro x n
    rw [hT.pred_eq]
    exact hlaw x n
  have key := LiteralD2c.v34_adaptive_literal T hc hm P hYm hind θ hv0 hlaw'
    (by rw [hinst]; exact hC)
  rw [hinst] at key
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨fun δ hδ => ⟨(measure_mono ?_).trans (k1 δ hδ).1, (k1 δ hδ).2⟩, k2, k3⟩
  rintro ω ⟨hstop, hreg⟩
  refine ⟨hstop, ?_⟩
  rw [hT.J_eq, hT.H_eq]
  exact G.exists_of_regret_gt hreg

end Adaptive

/-! ### The converses for the instance -/

section Converse

open GaussStopped

variable [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X] [MeasurableSpace A]
  [MeasurableSingletonClass A]

/-- `(ε, δ)`-correctness of a procedure (sampler `S`, decision rule `D`) over the
fixed-feature Gaussian model with arbitrary positive unknown variances: at every parameter `u`
and every positive variance vector `s`, at every horizon, the probability of having halted with
an action whose regret at `u` exceeds `ε` is at most `δ`. -/
def Correct (G : Problem X A Z E) (S : GSampler X) (D : GDecision A) (δ : ℝ) : Prop :=
  ∀ (u : E) (s : X → ℝ), (∀ x, 0 < s x) → ∀ n : ℕ,
    (law S (fun x => G.pred x u) s n).real
      {y | halted S (List.ofFn y) = true ∧ G.ε < G.reg (decAt S D (List.ofFn y)) u} ≤ δ

variable [Fintype A] [Nonempty X]

/-- **Theorem `thm:v34-converse` for the paper's instance, in terms of regret.**  The true
parameter is `θ`, the true variances `v > 0`; every action other than `astar` has regret above
`ε` at `θ` (so `astar` is the only action that can be correct); every action has an unscreened
component; `C_* = max_a C_a^* > 0` for the paper's polyhedra.  For every procedure that is
`(ε, δ)`-correct over the model (`Correct`), `δ ∈ (0, 1/2)`:
`E_{θ,v} τ ≥ kl(1 - δ, δ) / C_*` in `[0, ∞]`.  No hypothesis on the stopping time: if it has
infinite expectation the bound is trivial, otherwise the procedure halts almost surely and
returns `astar` with probability at least `1 - δ`. -/
theorem v34_converse_regret (hJ : ∀ a, (G.J a).Nonempty) (astar : A) (θ : E) {v : X → ℝ}
    (hv : ∀ x, 0 < v x) (huniq : ∀ a, a ≠ astar → G.ε < G.reg a θ)
    (hCpos : 0 < univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v))
    (S : GSampler X) (D : GDecision A) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (hcorr : G.Correct S D δ) :
    ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)) ≤
      expTau S (fun x => G.pred x θ) v := by
  classical
  set μ : X → ℝ := fun x => G.pred x θ with hμ
  by_cases htop : expTau S μ v = ⊤
  · rw [htop]; exact le_top
  have h0 : 0 ≤ actGameStar (G.J astar) (hJ astar) (G.Hc astar) G.pred μ v := by
    obtain ⟨x0⟩ := ‹Nonempty X›
    exact (actGame_nonneg (single_mem_simplex x0).1 hv).trans
      (actGame_le_star (G.J astar) (hJ astar) (G.Hc astar) G.pred (single_mem_simplex x0) hv)
  have heq := v34_Cstar_eq astar G.J hJ G.Hc G.pred hv (G.hinc_of_unique huniq) h0
  rw [heq] at hCpos ⊢
  refine v34_converse S D astar (G.J astar) (hJ astar) (G.Hc astar) (G.Hs astar) G.pred
    (fun x => G.pred_continuous x) hv (fun z hz => G.Hc_nonempty hz)
    (fun z hz => G.Hc_subset_closure hz) hδ0 hδ ?_ ?_ hCpos
  · intro η hη
    set Tf := (expTau S μ v).toReal with hTf
    have hTle : ∀ n, expTime S μ v n ≤ Tf := expTime_le_of_ne_top S μ v htop
    obtain ⟨n, hn⟩ := exists_nat_gt (Tf / η)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg ENNReal.toReal_nonneg hη.le) hn
    refine ⟨n, ?_⟩
    have h1 := not_halted_mul_le S μ v n
    have h2 : (law S μ v n).real (hset S n)ᶜ ≤ η := by
      have h3 : Tf < n * η := (div_lt_iff₀ hη).mp hn
      have h4 : (n : ℝ) * (law S μ v n).real (hset S n)ᶜ ≤ n * η := by
        have := hTle n
        linarith
      exact le_of_mul_le_mul_left h4 hn0
    have h3 : (law S μ v n).real (hset S n)ᶜ = 1 - (law S μ v n).real (hset S n) :=
      probReal_compl_eq_one_sub (measurableSet_hset S n)
    have hsub : hset S n ⊆ ansSet S D astar n ∪
        {y | halted S (List.ofFn y) = true ∧ G.ε < G.reg (decAt S D (List.ofFn y)) θ} := by
      intro y hy
      by_cases hd : decAt S D (List.ofFn y) = astar
      · exact Or.inl ⟨hy, hd⟩
      · exact Or.inr ⟨hy, huniq _ hd⟩
    have h4 := (measureReal_mono (μ := law S μ v n) hsub).trans (measureReal_union_le _ _)
    have h5 := hcorr θ v hv n
    linarith
  · intro z hz u hu s hs n
    refine (measureReal_mono ?_).trans (hcorr u s hs n)
    rintro y ⟨hy1, hy2⟩
    refine ⟨hy1, ?_⟩
    rw [hy2]
    exact G.regret_gt_iff.mpr ⟨z, hz, hu⟩

/-- **Theorem `thm:v34-converse-main` for the paper's instance, in terms of regret.**  Under
the hypotheses of `v34_converse_regret`, for every family of procedures `(S δ, D δ)` that is
`(ε, δ)`-correct over the model for each `δ ∈ (0, 1/2)`:
`E τ_δ ≥ kl(1 - δ, δ) / C_*`, and `liminf_{δ ↓ 0} E τ_δ / log (1 / δ) ≥ 1 / C_*`, in the form:
for every `c < 1 / C_*`, eventually `c log (1 / δ) ≤ E τ_δ`. -/
theorem v34_converse_main_regret (hJ : ∀ a, (G.J a).Nonempty) (astar : A) (θ : E) {v : X → ℝ}
    (hv : ∀ x, 0 < v x) (huniq : ∀ a, a ≠ astar → G.ε < G.reg a θ)
    (hCpos : 0 < univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v))
    (S : ℝ → GSampler X) (D : ℝ → GDecision A)
    (hcorr : ∀ δ, 0 < δ → δ < 1 / 2 → G.Correct (S δ) (D δ) δ) :
    (∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)) ≤
        expTau (S δ) (fun x => G.pred x θ) v) ∧
    ∀ c : ℝ, c < 1 / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v) →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (c * Real.log (1 / δ)) ≤ expTau (S δ) (fun x => G.pred x θ) v := by
  have hfin : ∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v)) ≤
        expTau (S δ) (fun x => G.pred x θ) v := fun δ hδ0 hδ =>
    G.v34_converse_regret hJ astar θ hv huniq hCpos (S δ) (D δ) hδ0 hδ (hcorr δ hδ0 hδ)
  refine ⟨hfin, fun c hc => ?_⟩
  have hev := liminf_coefficient (Eτ := fun δ => klBin (1 - δ) δ /
    univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (G.J a) (hJ a) (G.Hc a) G.pred (fun x => G.pred x θ) v))
    hCpos (fun δ _ _ => le_rfl) hc
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ h1 h2
  exact (ENNReal.ofReal_le_ofReal h1).trans (hfin δ h2.1 h2.2)

end Converse

end Problem

end

end LiteralD2d

end JointRootCert
