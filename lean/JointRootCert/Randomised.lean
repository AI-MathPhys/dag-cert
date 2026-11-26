/-
Randomised adaptive Bernoulli samplers: the model, the stopped change of measure, and the
lower bounds for randomised procedures.

Manuscript results covered (all for procedures with internal randomisation):

* `lem:active-com` "Stopped Bernoulli change of measure": `rstopped_transport`.
* `thm:active-star-lb` "Non-containment tied-star lower bound": `tied_star_lower_bound_rand`.
* `prop:ast-discovery` "A discovery cost absent from the characteristic time":
  `discovery_cost_rand` (with the rate stated for `C_A` and for `C_*`).
* `thm:ast-main` "One inside witness and Bernoulli information limit", lower bound
  `eq:ast-lower-main`: `ast_lower_main_rand`, `ast_lower_main_exact_rand`; and the theorem as one
  statement (lower bound for every randomised uniformly correct procedure, and a procedure
  attaining it): `ast_main_full`, `ast_main_exact_full`.

Model.  A randomised sampler (`RSampler`) is a deterministic sampler `Stopped.Sampler` for each
value of a seed `s`, drawn once from a probability measure `ν` on a measurable space,
independently of the observations; the next terminal, the stopping decision and the answer may
depend on the seed and on the observed history, measurably in the seed.  Its probabilities and
expectations are the `ν`-averages of those of the deterministic samplers (`rprob`, `rprobInf`,
`rexpCount`, `rexpTime`, `rexpCountInf`, `rexpTimeInf`, built from `Stopped.prob`,
`Stopped.probInf`, `Stopped.expCount`, `Stopped.expTime`, `Stopped.expCountInf`,
`Stopped.expTimeInf`).  An event measurable at stopping may depend on the seed (`SeedEvent`).
A deterministic sampler is the constant family (`RSampler.const`).

Finite expected stopping time of a randomised sampler is the hypothesis
`∀ n, rexpTime ν R μ n ≤ B` (`E[τ ∧ n] ≤ B` for all `n`); under it `rexpTimeInf` is the limit
of `rexpTime` (`tendsto_rexpTime`).
-/
import JointRootCert.RandomisedCore
import JointRootCert.BernoulliLimit
import JointRootCert.Discovery
import JointRootCert.BernoulliUpper

namespace JointRootCert

namespace Rand

open MeasureTheory Finset Real Filter Topology Stopped

set_option linter.unusedSectionVars false

/-! ### The model -/

/-- A **randomised adaptive sampler**: for every seed a deterministic sampler, with the next
terminal and the stopping decision at each history measurable in the seed. -/
structure RSampler (Z : Type*) (Sd : Type*) [MeasurableSpace Sd] where
  /-- the deterministic sampler run when the seed is `s` -/
  run : Sd → Sampler Z
  meas_next : ∀ (l : List Bool) (z : Z), MeasurableSet {s | (run s).next l = z}
  meas_stop : ∀ l : List Bool, MeasurableSet {s | (run s).stop l = true}

variable {Sd : Type*} [MeasurableSpace Sd]

/-- A deterministic sampler, as a randomised sampler that ignores its seed. -/
def RSampler.const {Z : Type*} (S : Sampler Z) : RSampler Z Sd where
  run := fun _ => S
  meas_next := fun _ _ => MeasurableSet.const _
  meas_stop := fun _ => MeasurableSet.const _

/-- A family of events of the stopped history indexed by the seed, measurable in the seed. -/
def SeedEvent (E : Sd → Set (List Bool)) : Prop := ∀ l, MeasurableSet {s | l ∈ E s}

lemma SeedEvent.const (A : Set (List Bool)) : SeedEvent (fun _ : Sd => A) :=
  fun _ => MeasurableSet.const _

lemma SeedEvent.compl {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    SeedEvent fun s => (E s)ᶜ := fun l => (hE l).compl

lemma SeedEvent.inter {E F : Sd → Set (List Bool)} (hE : SeedEvent E) (hF : SeedEvent F) :
    SeedEvent fun s => E s ∩ F s := fun l => (hE l).inter (hF l)

/-- A function of the seed with countably many values and measurable fibres stays measurable
after composition with any function. -/
lemma measurable_comp_of_fibers {Y β : Type*} [Countable Y] [MeasurableSpace β] {g : Sd → Y}
    (hg : ∀ y, MeasurableSet {s | g s = y}) (f : Y → β) : Measurable fun s => f (g s) := by
  intro T _
  have : (fun s => f (g s)) ⁻¹' T = ⋃ y ∈ f ⁻¹' T, {s | g s = y} := by
    ext s
    simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun y _ => hg y

/-- Events described through a seed-measurable decision rule are seed-measurable. -/
lemma seedEvent_dec {A : Type*} [Countable A] {dec : Sd → List Bool → A}
    (hdec : ∀ l a, MeasurableSet {s | dec s l = a}) (T : A → Prop) :
    SeedEvent fun s => {l | T (dec s l)} := fun l =>
  measurableSet_setOfPred.2 (measurable_comp_of_fibers (hdec l) T)

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

lemma seedEvent_stop (R : RSampler Z Sd) : SeedEvent fun s => stopSet (R.run s) :=
  fun l => R.meas_stop l

/-! ### Measurability in the seed -/

lemma measurable_lik (R : RSampler Z Sd) (μ : Z → ℝ) :
    ∀ l : List Bool, Measurable fun s => lik (R.run s) μ l
  | [] => measurable_const
  | b :: h => by
      show Measurable fun s => lik (R.run s) μ h * bern (μ ((R.run s).next h)) b
      exact (measurable_lik R μ h).mul
        (measurable_comp_of_fibers (R.meas_next h) fun z => bern (μ z) b)

lemma measurable_cnt (R : RSampler Z Sd) (z : Z) :
    ∀ l : List Bool, Measurable fun s => (cnt (R.run s) z l : ℝ)
  | [] => by
      simp only [cnt]
      exact measurable_const
  | _ :: h => by
      show Measurable fun s =>
        ((cnt (R.run s) z h + if (R.run s).next h = z then 1 else 0 : ℕ) : ℝ)
      simp only [Nat.cast_add]
      exact (measurable_cnt R z h).add
        (measurable_comp_of_fibers (R.meas_next h) fun y => (((if y = z then 1 else 0 : ℕ)) : ℝ))

/-- A sum over the stopped histories of a seed-measurable weight is seed-measurable. -/
lemma measurable_sum_leaves (R : RSampler Z Sd) {f : Sd → List Bool → ℝ}
    (hf : ∀ l, Measurable fun s => f s l) :
    ∀ (n : ℕ) (h : List Bool), Measurable fun s => ∑ l ∈ leaves (R.run s) n h, f s l
  | 0, h => by simpa using hf h
  | n + 1, h => by
      simp_rw [sum_leaves_succ]
      exact Measurable.ite (R.meas_stop h) (hf h)
        ((measurable_sum_leaves R hf n _).add (measurable_sum_leaves R hf n _))

lemma measurable_prob (R : RSampler Z Sd) (μ : Z → ℝ) (n : ℕ) {E : Sd → Set (List Bool)}
    (hE : SeedEvent E) : Measurable fun s => prob (R.run s) μ n (E s) := by
  classical
  unfold prob
  refine measurable_sum_leaves R (f := fun s l => (E s).indicator (lik (R.run s) μ) l)
    (fun l => ?_) n []
  simp only [Set.indicator_apply]
  exact Measurable.ite (hE l) (measurable_lik R μ l) measurable_const

lemma measurable_expCount (R : RSampler Z Sd) (μ : Z → ℝ) (n : ℕ) (z : Z) :
    Measurable fun s => expCount (R.run s) μ n z := by
  unfold expCount
  exact measurable_sum_leaves R (f := fun s l => lik (R.run s) μ l * (cnt (R.run s) z l : ℝ))
    (fun l => (measurable_lik R μ l).mul (measurable_cnt R z l)) n []

lemma measurable_expTime (R : RSampler Z Sd) (μ : Z → ℝ) (n : ℕ) :
    Measurable fun s => expTime (R.run s) μ n := by
  unfold expTime
  exact measurable_sum_leaves R (f := fun s l => lik (R.run s) μ l * (l.length : ℝ))
    (fun l => (measurable_lik R μ l).mul measurable_const) n []

lemma measurable_probInf (R : RSampler Z Sd) (μ : Z → ℝ) {E : Sd → Set (List Bool)}
    (hE : SeedEvent E) : Measurable fun s => probInf (R.run s) μ (E s) := by
  unfold probInf
  exact Measurable.iSup fun n => measurable_prob R μ n (hE.inter (seedEvent_stop R))

/-- `E_μ[τ ∧ n] ≤ n`. -/
lemma expTime_le (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ) :
    expTime S μ n ≤ n := by
  unfold expTime
  calc ∑ l ∈ leaves S n [], lik S μ l * (l.length : ℝ)
      ≤ ∑ l ∈ leaves S n [], lik S μ l * (n : ℝ) := by
        refine sum_le_sum fun l hl => mul_le_mul_of_nonneg_left ?_ (lik_pos S hμ l).le
        have := length_le_of_mem_leaves S n [] l hl
        simp only [List.length_nil, zero_add] at this
        exact_mod_cast this
    _ = n := by rw [← sum_mul, sum_lik_leaves, one_mul]

lemma expTime_mono (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) :
    Monotone fun n => expTime S μ n := by
  intro m n hmn
  simp only [← sum_expCount]
  exact sum_le_sum fun z _ => expCount_mono S hμ z hmn

/-! ### Seed-averaged probabilities and expectations -/

section Averages

variable (ν : Measure Sd)

/-- `P_μ(H_{τ ∧ n} ∈ E)` for the randomised sampler: the seed-average of `Stopped.prob`. -/
noncomputable def rprob (R : RSampler Z Sd) (μ : Z → ℝ) (n : ℕ) (E : Sd → Set (List Bool)) : ℝ :=
  ∫ s, prob (R.run s) μ n (E s) ∂ν

/-- `P_μ(τ < ∞, H_τ ∈ E)` for the randomised sampler: the seed-average of `Stopped.probInf`. -/
noncomputable def rprobInf (R : RSampler Z Sd) (μ : Z → ℝ) (E : Sd → Set (List Bool)) : ℝ :=
  ∫ s, probInf (R.run s) μ (E s) ∂ν

/-- `E_μ[N_z(τ ∧ n)]` for the randomised sampler. -/
noncomputable def rexpCount (R : RSampler Z Sd) (μ : Z → ℝ) (n : ℕ) (z : Z) : ℝ :=
  ∫ s, expCount (R.run s) μ n z ∂ν

/-- `E_μ[τ ∧ n]` for the randomised sampler. -/
noncomputable def rexpTime (R : RSampler Z Sd) (μ : Z → ℝ) (n : ℕ) : ℝ :=
  ∫ s, expTime (R.run s) μ n ∂ν

/-- `E_μ[N_z(τ)]` for the randomised sampler: the seed-average of `Stopped.expCountInf`. -/
noncomputable def rexpCountInf (R : RSampler Z Sd) (μ : Z → ℝ) (z : Z) : ℝ :=
  ∫ s, expCountInf (R.run s) μ z ∂ν

/-- `E_μ[τ]` for the randomised sampler: the seed-average of `Stopped.expTimeInf`. -/
noncomputable def rexpTimeInf (R : RSampler Z Sd) (μ : Z → ℝ) : ℝ :=
  ∫ s, expTimeInf (R.run s) μ ∂ν

variable [IsProbabilityMeasure ν] (R : RSampler Z Sd) {μ : Z → ℝ}
  (hμ : ∀ z, 0 < μ z ∧ μ z < 1)

include hμ

lemma integrable_prob (n : ℕ) {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    Integrable (fun s => prob (R.run s) μ n (E s)) ν :=
  Integrable.of_mem_Icc 0 1 (measurable_prob R μ n hE).aemeasurable
    (ae_of_all _ fun s => ⟨prob_nonneg (R.run s) hμ n _, prob_le_one (R.run s) hμ n _⟩)

lemma integrable_probInf {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    Integrable (fun s => probInf (R.run s) μ (E s)) ν :=
  Integrable.of_mem_Icc 0 1 (measurable_probInf R μ hE).aemeasurable
    (ae_of_all _ fun s => ⟨probInf_nonneg (R.run s) hμ _, probInf_le_one (R.run s) hμ _⟩)

lemma integrable_expTime (n : ℕ) : Integrable (fun s => expTime (R.run s) μ n) ν :=
  Integrable.of_mem_Icc 0 n (measurable_expTime R μ n).aemeasurable
    (ae_of_all _ fun s => ⟨expTime_nonneg (R.run s) hμ n, expTime_le (R.run s) hμ n⟩)

lemma integrable_expCount (n : ℕ) (z : Z) : Integrable (fun s => expCount (R.run s) μ n z) ν :=
  Integrable.of_mem_Icc 0 n (measurable_expCount R μ n z).aemeasurable
    (ae_of_all _ fun s => ⟨expCount_nonneg (R.run s) hμ n z,
      (expCount_le_expTime (R.run s) hμ n z).trans (expTime_le (R.run s) hμ n)⟩)

lemma rprob_nonneg (n : ℕ) (E : Sd → Set (List Bool)) : 0 ≤ rprob ν R μ n E :=
  integral_nonneg fun s => prob_nonneg (R.run s) hμ n _

lemma rprob_le_one (n : ℕ) {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    rprob ν R μ n E ≤ 1 := by
  have := integral_mono (integrable_prob ν R hμ n hE) (integrable_const (1 : ℝ))
    fun s => prob_le_one (R.run s) hμ n (E s)
  simpa [rprob] using this

lemma rprobInf_nonneg (E : Sd → Set (List Bool)) : 0 ≤ rprobInf ν R μ E :=
  integral_nonneg fun s => probInf_nonneg (R.run s) hμ _

lemma rprobInf_le_one {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    rprobInf ν R μ E ≤ 1 := by
  have := integral_mono (integrable_probInf ν R hμ hE) (integrable_const (1 : ℝ))
    fun s => probInf_le_one (R.run s) hμ (E s)
  simpa [rprobInf] using this

/-- `P_μ(τ ≤ n, H_τ ∈ E) → P_μ(τ < ∞, H_τ ∈ E)` for the randomised sampler. -/
lemma tendsto_rprob {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    Tendsto (fun n => rprob ν R μ n fun s => E s ∩ stopSet (R.run s)) atTop
      (𝓝 (rprobInf ν R μ E)) := by
  unfold rprob rprobInf
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (measurable_prob R μ n (hE.inter (seedEvent_stop R))).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ fun s => ?_)
    (ae_of_all _ fun s => tendsto_probInf (R.run s) hμ (E s))
  rw [Real.norm_of_nonneg (prob_nonneg (R.run s) hμ n _)]
  exact prob_le_one (R.run s) hμ n _

lemma rprob_le_rprobInf (n : ℕ) {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    rprob ν R μ n (fun s => E s ∩ stopSet (R.run s)) ≤ rprobInf ν R μ E :=
  integral_mono (integrable_prob ν R hμ n (hE.inter (seedEvent_stop R)))
    (integrable_probInf ν R hμ hE) fun s => prob_le_probInf (R.run s) hμ n (E s)

lemma rprobInf_mono {E F : Sd → Set (List Bool)} (hE : SeedEvent E) (hF : SeedEvent F)
    (h : ∀ s, E s ⊆ F s) : rprobInf ν R μ E ≤ rprobInf ν R μ F :=
  integral_mono (integrable_probInf ν R hμ hE) (integrable_probInf ν R hμ hF)
    fun s => probInf_mono (R.run s) hμ (h s)

lemma rprobInf_add_le_one {E F : Sd → Set (List Bool)} (hE : SeedEvent E) (hF : SeedEvent F)
    (h : ∀ s, Disjoint (E s) (F s)) : rprobInf ν R μ E + rprobInf ν R μ F ≤ 1 := by
  have h12 : Integrable (fun s => probInf (R.run s) μ (E s) + probInf (R.run s) μ (F s)) ν :=
    (integrable_probInf ν R hμ hE).add (integrable_probInf ν R hμ hF)
  have e := integral_mono h12 (integrable_const (1 : ℝ))
    fun s => probInf_add_le_one (R.run s) hμ (h s)
  rw [integral_add (integrable_probInf ν R hμ hE) (integrable_probInf ν R hμ hF)] at e
  simpa [rprobInf] using e

lemma rexpTime_nonneg (n : ℕ) : 0 ≤ rexpTime ν R μ n :=
  integral_nonneg fun s => expTime_nonneg (R.run s) hμ n

lemma rexpCount_nonneg (n : ℕ) (z : Z) : 0 ≤ rexpCount ν R μ n z :=
  integral_nonneg fun s => expCount_nonneg (R.run s) hμ n z

lemma sum_rexpCount (n : ℕ) : ∑ z, rexpCount ν R μ n z = rexpTime ν R μ n := by
  unfold rexpCount rexpTime
  rw [← integral_finsetSum _ fun z _ => integrable_expCount ν R hμ n z]
  exact integral_congr_ae (ae_of_all _ fun s => sum_expCount (R.run s) μ n)

lemma rexpCount_le_rexpTime (n : ℕ) (z : Z) : rexpCount ν R μ n z ≤ rexpTime ν R μ n :=
  integral_mono (integrable_expCount ν R hμ n z) (integrable_expTime ν R hμ n)
    fun s => expCount_le_expTime (R.run s) hμ n z

lemma rexpCount_mono (z : Z) : Monotone fun n => rexpCount ν R μ n z := fun m n hmn =>
  integral_mono (integrable_expCount ν R hμ m z) (integrable_expCount ν R hμ n z)
    fun s => expCount_mono (R.run s) hμ z hmn

lemma rexpTime_mono : Monotone fun n => rexpTime ν R μ n := fun m n hmn =>
  integral_mono (integrable_expTime ν R hμ m) (integrable_expTime ν R hμ n)
    fun s => expTime_mono (R.run s) hμ hmn

/-- Markov's inequality `n · P_μ(τ > n) ≤ E_μ[τ ∧ n]` for the randomised sampler. -/
lemma rprob_not_stop_mul_le (n : ℕ) :
    rprob ν R μ n (fun s => (stopSet (R.run s))ᶜ) * n ≤ rexpTime ν R μ n := by
  unfold rprob rexpTime
  rw [← integral_mul_const]
  exact integral_mono ((integrable_prob ν R hμ n (seedEvent_stop R).compl).mul_const _)
    (integrable_expTime ν R hμ n) fun s => prob_not_stop_mul_le (R.run s) hμ n

lemma rprob_split (n : ℕ) {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    rprob ν R μ n (fun s => E s ∩ stopSet (R.run s))
      + rprob ν R μ n (fun s => (E s)ᶜ ∩ stopSet (R.run s))
      + rprob ν R μ n (fun s => (stopSet (R.run s))ᶜ) = 1 := by
  have h1 := integrable_prob ν R hμ n (hE.inter (seedEvent_stop R))
  have h2 := integrable_prob ν R hμ n (hE.compl.inter (seedEvent_stop R))
  have h3 := integrable_prob ν R hμ n (seedEvent_stop R).compl
  have h12 : Integrable (fun s => prob (R.run s) μ n (E s ∩ stopSet (R.run s))
      + prob (R.run s) μ n ((E s)ᶜ ∩ stopSet (R.run s))) ν := h1.add h2
  have e := integral_congr_ae (μ := ν) (ae_of_all _ fun s => prob_split (R.run s) μ n (E s))
  rw [integral_add h12 h3, integral_add h1 h2] at e
  simpa [rprob] using e

lemma rprob_compl (n : ℕ) {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    rprob ν R μ n E + rprob ν R μ n (fun s => (E s)ᶜ) = 1 := by
  have e := integral_congr_ae (μ := ν) (ae_of_all _ fun s => prob_compl (R.run s) μ n (E s))
  rw [integral_add (integrable_prob ν R hμ n hE) (integrable_prob ν R hμ n hE.compl)] at e
  simpa [rprob] using e

/-! ### Finite expected stopping time -/

section FiniteTime

variable {B : ℝ} (hB : ∀ n, rexpTime ν R μ n ≤ B)

include hB

/-- With finite expected stopping time, almost every seed gives a deterministic sampler with
bounded truncated expected times. -/
lemma ae_bddAbove_expTime :
    ∀ᵐ s ∂ν, BddAbove (Set.range fun n => expTime (R.run s) μ n) :=
  (mono_limit ν (f := fun n s => expTime (R.run s) μ n) (measurable_expTime R μ)
    (fun n s => expTime_nonneg (R.run s) hμ n) (fun s => expTime_mono (R.run s) hμ)
    (integrable_expTime ν R hμ) hB).1

/-- `E_μ[τ ∧ n] → E_μ[τ]` for the randomised sampler. -/
lemma tendsto_rexpTime :
    Tendsto (fun n => rexpTime ν R μ n) atTop (𝓝 (rexpTimeInf ν R μ)) :=
  (mono_limit ν (f := fun n s => expTime (R.run s) μ n) (measurable_expTime R μ)
    (fun n s => expTime_nonneg (R.run s) hμ n) (fun s => expTime_mono (R.run s) hμ)
    (integrable_expTime ν R hμ) hB).2.2

lemma rexpTime_le_rexpTimeInf (n : ℕ) : rexpTime ν R μ n ≤ rexpTimeInf ν R μ :=
  (rexpTime_mono ν R hμ).ge_of_tendsto (tendsto_rexpTime ν R hμ hB) n

/-- `E_μ[N_z(τ ∧ n)] → E_μ[N_z(τ)]` for the randomised sampler. -/
lemma tendsto_rexpCount (z : Z) :
    Tendsto (fun n => rexpCount ν R μ n z) atTop (𝓝 (rexpCountInf ν R μ z)) :=
  (mono_limit ν (f := fun n s => expCount (R.run s) μ n z) (fun n => measurable_expCount R μ n z)
    (fun n s => expCount_nonneg (R.run s) hμ n z) (fun s => expCount_mono (R.run s) hμ z)
    (fun n => integrable_expCount ν R hμ n z)
    (fun n => (rexpCount_le_rexpTime ν R hμ n z).trans (hB n))).2.2

lemma rexpCount_le_rexpCountInf (n : ℕ) (z : Z) :
    rexpCount ν R μ n z ≤ rexpCountInf ν R μ z :=
  (rexpCount_mono ν R hμ z).ge_of_tendsto (tendsto_rexpCount ν R hμ hB z) n

lemma rexpCountInf_nonneg (z : Z) : 0 ≤ rexpCountInf ν R μ z :=
  (rexpCount_nonneg ν R hμ 0 z).trans (rexpCount_le_rexpCountInf ν R hμ hB 0 z)

/-- `∑_z E_μ[N_z(τ)] = E_μ[τ]` for the randomised sampler. -/
lemma sum_rexpCountInf : ∑ z, rexpCountInf ν R μ z = rexpTimeInf ν R μ :=
  tendsto_nhds_unique
    (tendsto_finsetSum _ fun z _ => tendsto_rexpCount ν R hμ hB z)
    ((tendsto_rexpTime ν R hμ hB).congr fun n => (sum_rexpCount ν R hμ n).symm)

end FiniteTime

end Averages

/-- For a deterministic sampler the randomised quantities are the deterministic ones. -/
lemma rprobInf_const (ν : Measure Sd) [IsProbabilityMeasure ν] (S : Sampler Z) (μ : Z → ℝ)
    (A : Set (List Bool)) :
    rprobInf ν (RSampler.const S) μ (fun _ => A) = probInf S μ A := by
  simp [rprobInf, RSampler.const]

lemma rexpTime_const (ν : Measure Sd) [IsProbabilityMeasure ν] (S : Sampler Z) (μ : Z → ℝ)
    (n : ℕ) : rexpTime ν (RSampler.const S) μ n = expTime S μ n := by
  simp [rexpTime, RSampler.const]

lemma rexpTimeInf_const (ν : Measure Sd) [IsProbabilityMeasure ν] (S : Sampler Z) (μ : Z → ℝ) :
    rexpTimeInf ν (RSampler.const S) μ = expTimeInf S μ := by
  simp [rexpTimeInf, RSampler.const]

/-! ### `lem:active-com` for randomised samplers -/

section Transport

variable (ν : Measure Sd) [IsProbabilityMeasure ν] (R : RSampler Z Sd) {μ lam : Z → ℝ}

/-- Absolute continuity of the stopped laws of a randomised sampler, first half. -/
lemma rprobInf_pos_of_pos (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hlam : ∀ z, 0 < lam z ∧ lam z < 1)
    {E : Sd → Set (List Bool)} (hE : SeedEvent E) (h : 0 < rprobInf ν R μ E) :
    0 < rprobInf ν R lam E :=
  integral_pos_of_imp ν (measurable_probInf R μ hE) (measurable_probInf R lam hE)
    (fun s => ⟨probInf_nonneg (R.run s) hμ _, probInf_le_one (R.run s) hμ _⟩)
    (fun s => ⟨probInf_nonneg (R.run s) hlam _, probInf_le_one (R.run s) hlam _⟩)
    (ae_of_all _ fun s => probInf_pos_of_pos (R.run s) hlam (E s)) h

/-- Absolute continuity of the stopped laws of a randomised sampler, second half; uses that a
sampler with finite expected time under `μ` stops `μ`-almost surely. -/
lemma rprobInf_lt_one_of_lt_one (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) {B : ℝ} (hB : ∀ n, rexpTime ν R μ n ≤ B)
    {E : Sd → Set (List Bool)} (hE : SeedEvent E) (h : rprobInf ν R μ E < 1) :
    rprobInf ν R lam E < 1 := by
  have hEc := hE.compl.inter (seedEvent_stop R)
  have hEs := hE.inter (seedEvent_stop R)
  have hex : ∃ n, 0 < rprob ν R μ n (fun s => (E s)ᶜ ∩ stopSet (R.run s)) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hB0 : 0 ≤ B := (rexpTime_nonneg ν R hμ 0).trans (hB 0)
    have hd : 0 < 1 - rprobInf ν R μ E := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (B / (1 - rprobInf ν R μ E))
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hB0 hd.le) hn
    have h1 : B < n * (1 - rprobInf ν R μ E) := by rwa [div_lt_iff₀ hd] at hn
    have h2 := rprob_not_stop_mul_le ν R hμ n
    have h3 := rprob_split ν R hμ n hE
    have h4 := le_antisymm (hcon n) (rprob_nonneg ν R hμ n _)
    have h5 := rprob_le_rprobInf ν R hμ n hE
    have h6 : (1 - rprobInf ν R μ E) * n
        ≤ rprob ν R μ n (fun s => (stopSet (R.run s))ᶜ) * n :=
      mul_le_mul_of_nonneg_right (by linarith) hn0.le
    linarith [hB n]
  obtain ⟨n, hn⟩ := hex
  have hq : 0 < rprob ν R lam n (fun s => (E s)ᶜ ∩ stopSet (R.run s)) :=
    integral_pos_of_imp ν (measurable_prob R μ n hEc) (measurable_prob R lam n hEc)
      (fun s => ⟨prob_nonneg (R.run s) hμ n _, prob_le_one (R.run s) hμ n _⟩)
      (fun s => ⟨prob_nonneg (R.run s) hlam n _, prob_le_one (R.run s) hlam n _⟩)
      (ae_of_all _ fun s => prob_pos_of_pos (R.run s) hlam n _) hn
  have hle : ∀ m, rprob ν R lam m (fun s => E s ∩ stopSet (R.run s))
      ≤ 1 - rprob ν R lam n (fun s => (E s)ᶜ ∩ stopSet (R.run s)) := by
    intro m
    have hpt : ∀ s, prob (R.run s) lam m (E s ∩ stopSet (R.run s))
        ≤ 1 - prob (R.run s) lam n ((E s)ᶜ ∩ stopSet (R.run s)) := by
      intro s
      have hs := prob_split (R.run s) lam (max m n) (E s)
      have h1 := prob_stop_mono (R.run s) hlam (E s) (le_max_left m n)
      have h2 := prob_stop_mono (R.run s) hlam (E s)ᶜ (le_max_right m n)
      have h3 := prob_nonneg (R.run s) hlam (max m n) (stopSet (R.run s))ᶜ
      linarith
    have hsub : Integrable
        (fun s => 1 - prob (R.run s) lam n ((E s)ᶜ ∩ stopSet (R.run s))) ν :=
      (integrable_const (1 : ℝ)).sub (integrable_prob ν R hlam n hEc)
    have := integral_mono (integrable_prob ν R hlam m hEs) hsub hpt
    rw [integral_sub (integrable_const (1 : ℝ)) (integrable_prob ν R hlam n hEc)] at this
    simpa [rprob] using this
  have h7 : rprobInf ν R lam E ≤ 1 - rprob ν R lam n (fun s => (E s)ᶜ ∩ stopSet (R.run s)) :=
    le_of_tendsto' (tendsto_rprob ν R hlam hE) hle
  linarith

/-- Two-point Donsker--Varadhan bound for the stopped history of a randomised sampler at a
bounded horizon: the seed-wise bound `Stopped.two_point_stopped`, averaged over the seed by
concavity of the logarithm. -/
lemma two_point_rstopped (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hlam : ∀ z, 0 < lam z ∧ lam z < 1)
    (n : ℕ) {E : Sd → Set (List Bool)} (hE : SeedEvent E) (a b : ℝ) :
    a * rprob ν R μ n E + b * (1 - rprob ν R μ n E)
        - log (exp a * rprob ν R lam n E + exp b * (1 - rprob ν R lam n E))
      ≤ ∑ z, rexpCount ν R μ n z * bkl (μ z) (lam z) := by
  have hK : Integrable (fun s => ∑ z, expCount (R.run s) μ n z * bkl (μ z) (lam z)) ν :=
    integrable_finsetSum _ fun z _ => (integrable_expCount ν R hμ n z).mul_const _
  have h := two_point_integral ν (measurable_prob R μ n hE) (measurable_prob R lam n hE)
    (fun s => ⟨prob_nonneg (R.run s) hμ n _, prob_le_one (R.run s) hμ n _⟩)
    (fun s => ⟨prob_nonneg (R.run s) hlam n _, prob_le_one (R.run s) hlam n _⟩) hK a b
    (fun s => two_point_stopped (R.run s) hμ hlam n (E s) a b)
  have e : ∫ s, ∑ z, expCount (R.run s) μ n z * bkl (μ z) (lam z) ∂ν
      = ∑ z, rexpCount ν R μ n z * bkl (μ z) (lam z) := by
    rw [integral_finsetSum _ fun z _ => (integrable_expCount ν R hμ n z).mul_const _]
    exact sum_congr rfl fun z _ => integral_mul_const _ _
  rw [e] at h
  exact h

/-- **Stopped Bernoulli change of measure for a randomised sampler at a bounded horizon.** -/
theorem rstopped_transport_finite (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) (n : ℕ) {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    bkl (rprob ν R μ n E) (rprob ν R lam n E) ≤ ∑ z, rexpCount ν R μ n z * bkl (μ z) (lam z) := by
  have hK : Integrable (fun s => ∑ z, expCount (R.run s) μ n z * bkl (μ z) (lam z)) ν :=
    integrable_finsetSum _ fun z _ => (integrable_expCount ν R hμ n z).mul_const _
  have h := bkl_integral_le_of_le ν (measurable_prob R μ n hE) (measurable_prob R lam n hE)
    (fun s => ⟨prob_nonneg (R.run s) hμ n _, prob_le_one (R.run s) hμ n _⟩)
    (fun s => ⟨prob_nonneg (R.run s) hlam n _, prob_le_one (R.run s) hlam n _⟩)
    (fun s => prob_pos_of_pos (R.run s) hlam n (E s))
    (fun s hs => by
      have h1 := prob_compl (R.run s) μ n (E s)
      have h2 := prob_compl (R.run s) lam n (E s)
      have h3 : 0 < prob (R.run s) lam n (E s)ᶜ :=
        prob_pos_of_pos (R.run s) (μ := μ) hlam n _ (by linarith)
      linarith) hK
    (fun s => stopped_transport_finite (R.run s) hμ hlam n (E s))
  have e : ∫ s, ∑ z, expCount (R.run s) μ n z * bkl (μ z) (lam z) ∂ν
      = ∑ z, rexpCount ν R μ n z * bkl (μ z) (lam z) := by
    rw [integral_finsetSum _ fun z _ => (integrable_expCount ν R hμ n z).mul_const _]
    exact sum_congr rfl fun z _ => integral_mul_const _ _
  rw [e] at h
  exact h

/-- **Stopped Bernoulli change of measure for randomised samplers** (`lem:active-com`).
For a randomised adaptive sampler `R` with seed law `ν`, interior Bernoulli mean vectors
`μ, λ`, finite expected stopping time under `μ` (`hB`: `E_μ[τ ∧ n] ≤ B` for all `n`), and every
event `{τ < ∞, H_τ ∈ E}` determined by the seed and the stopped history,
`kl(P_μ(E), P_λ(E)) ≤ ∑_z E_μ[N_z(τ)] kl(μ_z, λ_z)`,
where probabilities and expected counts are averaged over the seed.  Derived from the
deterministic bound by joint convexity of the binary divergence (in its two-point form,
`two_point_integral`).  Almost-sure stopping under `λ` is not needed. -/
theorem rstopped_transport (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hlam : ∀ z, 0 < lam z ∧ lam z < 1)
    {B : ℝ} (hB : ∀ n, rexpTime ν R μ n ≤ B) {E : Sd → Set (List Bool)} (hE : SeedEvent E) :
    bkl (rprobInf ν R μ E) (rprobInf ν R lam E)
      ≤ ∑ z, rexpCountInf ν R μ z * bkl (μ z) (lam z) := by
  refine bkl_le_of_tendsto (tendsto_rprob ν R hμ hE) (tendsto_rprob ν R hlam hE)
    (rprobInf_nonneg ν R hμ E) (rprobInf_le_one ν R hμ hE) (rprobInf_nonneg ν R hlam E)
    (rprobInf_le_one ν R hlam hE) (rprobInf_pos_of_pos ν R hμ hlam hE)
    (rprobInf_lt_one_of_lt_one ν R hμ hlam hB hE) fun n a b => ?_
  exact (two_point_rstopped ν R hμ hlam n (hE.inter (seedEvent_stop R)) a b).trans
    (sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
      (rexpCount_le_rexpCountInf ν R hμ hB n z)
      (bkl_nonneg (hμ z).1.le (hμ z).2.le (hlam z).1 (hlam z).2))

end Transport

/-! ### `thm:active-star-lb` for randomised procedures -/

section Star

/-- **Non-containment tied-star lower bound for randomised procedures**
(`thm:active-star-lb`, `eq:active-star-bound`).  `R` is a randomised adaptive sampler with seed
law `ν` and `dec` its decision rule (a function of the seed and the stopped history; `none` is
the answer `A`, `some i` the answer `B_i`).  `hcorr` is `(ε,δ)`-correctness with almost-sure
stopping: at every interior parameter the procedure stops and returns an action of regret at
most `ε` with probability at least `1 - δ`.  `hB` is finiteness of the expected stopping time
at the tied star (if it is infinite the manuscript's claim is vacuous). -/
theorem tied_star_lower_bound_rand {N : ℕ} {g ε δ : ℝ} (hε : 0 < ε) (hεg : ε ≤ g)
    (hg : g ≤ 1 / 4) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (ν : Measure Sd) [IsProbabilityMeasure ν]
    (R : RSampler (Fan N) Sd) (dec : Sd → List Bool → Option (Fin N))
    (hdec : ∀ l a, MeasurableSet {s | dec s l = a})
    (hcorr : ∀ lam : Fan N → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
      1 - δ ≤ rprobInf ν R lam
        (fun s => {l | regret (starSupp N (dec s l)) (starSupp_nonempty N (dec s l)) lam ≤ ε}))
    {B : ℝ} (hB : ∀ n, rexpTime ν R (starMu N g) n ≤ B) :
    bkl (1 / 2) δ * min (N / bkl (1 / 2 - g) (1 / 2 + ε)) (1 / bkl (1 / 2) (1 / 2 + ε))
      ≤ rexpTimeInf ν R (starMu N g) := by
  classical
  have hg0 := hε.trans_le hεg
  have hμ := starMu_interior (N := N) hg0 hg
  rw [← sum_rexpCountInf ν R hμ hB]
  have hEA : SeedEvent (fun s => {l : List Bool | dec s l = none}) :=
    seedEvent_dec hdec (fun a => a = none)
  have hEG : ∀ lam : Fan N → ℝ, SeedEvent (fun s =>
      {l : List Bool | regret (starSupp N (dec s l)) (starSupp_nonempty N (dec s l)) lam ≤ ε}) :=
    fun lam => seedEvent_dec hdec
      (fun a => regret (starSupp N a) (starSupp_nonempty N a) lam ≤ ε)
  have hregA : ∀ (lam : Fan N → ℝ) (a : Option (Fin N)), a = none →
      regret (starSupp N a) (starSupp_nonempty N a) lam
        = regret (pairSupp N) (pairSupp_nonempty N) lam := by
    rintro lam _ rfl
    rfl
  have hregB : ∀ (lam : Fan N → ℝ) (a : Option (Fin N)) (i : Fin N), a = some i →
      regret (starSupp N a) (starSupp_nonempty N a) lam
        = regret (starB N i) (starB_nonempty N i) lam := by
    rintro lam _ i rfl
    rfl
  refine tied_star_lower_bound hε hεg hg hδ0 hδ (rexpCountInf ν R (starMu N g))
    (fun z => rexpCountInf_nonneg ν R hμ hB z)
    (fun lam => if (∀ i, 0 < lam i ∧ lam i < 1) then
      rprobInf ν R lam (fun s => {l | dec s l = none}) else 0)
    ?_ ?_ ?_ ?_ ?_
  · intro lam
    split_ifs with h
    · exact ⟨rprobInf_nonneg ν R h _, rprobInf_le_one ν R h hEA⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · intro lam hint hr
    simp only [ite_eq_left hint]
    have hdis : ∀ s, Disjoint {l : List Bool | dec s l = none}
        {l | regret (starSupp N (dec s l)) (starSupp_nonempty N (dec s l)) lam ≤ ε} :=
      fun s => Set.disjoint_left.2 fun l hl hG => by
        rw [Set.mem_ofPred_eq, hregA lam (dec s l) hl] at hG
        linarith
    have := rprobInf_add_le_one ν R hint hEA (hEG lam) hdis
    linarith [hcorr lam hint]
  · intro lam hint hr
    simp only [ite_eq_left hint]
    have hsub : ∀ s,
        {l | regret (starSupp N (dec s l)) (starSupp_nonempty N (dec s l)) lam ≤ ε}
        ⊆ {l : List Bool | dec s l = none} := fun s l hG => by
      by_contra hne
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 hne
      rw [Set.mem_ofPred_eq, hregB lam (dec s l) i hi] at hG
      linarith [hr i]
    linarith [rprobInf_mono ν R hint (hEG lam) hEA hsub, hcorr lam hint]
  · intro lam hint
    simp only [ite_eq_left hint, ite_eq_left hμ]
    exact ⟨rprobInf_pos_of_pos ν R hμ hint hEA, rprobInf_lt_one_of_lt_one ν R hμ hint hB hEA⟩
  · intro lam hint
    simp only [ite_eq_left hint, ite_eq_left hμ]
    exact rstopped_transport ν R hμ hint hB hEA

end Star

/-! ### `prop:ast-discovery` for randomised procedures -/

section Discovery

variable {N : ℕ}

/-- Finite-horizon core of `prop:ast-discovery` for one deterministic sampler, with the
probability of the wrong answer under each `μ^j` kept explicit (`Stopped.discovery_finite`
bounds each of them by `δ`):
`(N+1)/2 · ∑_j (P_0(τ ≤ n, H_τ ∈ B) - P_{μ^j}(τ ≤ n, H_τ ∈ B)) ≤ ∑_j E_{μ^j}[τ ∧ n]`. -/
theorem discovery_finite_seed (S : Sampler Z) {x : Fin N → Z} (hx : Function.Injective x)
    {μ0 : Z → ℝ} {μs : Fin N → Z → ℝ} (h0 : ∀ z, 0 < μ0 z ∧ μ0 z < 1)
    (hs : ∀ j z, 0 < μs j z ∧ μs j z < 1) (hagree : ∀ j z, z ≠ x j → μs j z = μ0 z)
    (B : Set (List Bool)) (n : ℕ) :
    ((N : ℝ) + 1) / 2
        * ∑ j, (prob S μ0 n (B ∩ stopSet S) - prob S (μs j) n (B ∩ stopSet S))
      ≤ ∑ j, expTime S (μs j) n := by
  have step1 : ∀ j, ∑ l ∈ leaves S n [], lik S μ0 l * (quiet S (x j) l : ℝ)
      ≤ expTime S (μs j) n := by
    intro j
    rw [← sum_lik_quiet_congr S (hagree j) n]
    exact sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
      (by exact_mod_cast quiet_le_length S (x j) l) (lik_pos S (hs j) l).le
  have step2 : ∀ j, prob S μ0 n (B ∩ stopSet S) - prob S (μs j) n (B ∩ stopSet S)
      ≤ ∑ l ∈ leaves S n [], lik S μ0 l * (if cnt S (x j) l = 0 then (0 : ℝ) else 1) := by
    intro j
    have hle : prob S (μs j) n ((B ∩ {l | cnt S (x j) l = 0}) ∩ stopSet S)
        ≤ prob S (μs j) n (B ∩ stopSet S) :=
      prob_mono_set S (hs j) n (Set.inter_subset_inter_left _ Set.inter_subset_left)
    have hpt : ∀ l ∈ leaves S n [],
        (B ∩ stopSet S).indicator (lik S μ0) l
          - ((B ∩ {l | cnt S (x j) l = 0}) ∩ stopSet S).indicator (lik S (μs j)) l
        ≤ lik S μ0 l * (if cnt S (x j) l = 0 then (0 : ℝ) else 1) := by
      intro l _
      have hp := (lik_pos S h0 l).le
      by_cases hc : cnt S (x j) l = 0
      · have e := lik_eq_of_cnt_eq_zero S (hagree j) l hc
        by_cases hB : l ∈ B <;> by_cases hst : l ∈ stopSet S <;>
          simp [Set.indicator, hc, hB, hst, e]
      · have h2 : l ∉ (B ∩ {l | cnt S (x j) l = 0}) ∩ stopSet S := fun hm => hc hm.1.2
        rw [Set.indicator_of_notMem h2, ite_eq_right hc, sub_zero, mul_one]
        exact indicator_le_of_pos _ (lik_pos S h0 l)
    have := sum_le_sum hpt
    rw [sum_sub_distrib] at this
    unfold prob at hle ⊢
    linarith
  have step3 : ((N : ℝ) + 1) / 2
        * ∑ l ∈ leaves S n [], lik S μ0 l * ((N : ℝ) - (unreq S x l).card)
      ≤ ∑ j, ∑ l ∈ leaves S n [], lik S μ0 l * (quiet S (x j) l : ℝ) := by
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun l _ => ?_
    rw [← mul_sum]
    have := quiet_pathwise S hx l
    have hp := (lik_pos S h0 l).le
    nlinarith
  have step4 : ∑ j, (prob S μ0 n (B ∩ stopSet S) - prob S (μs j) n (B ∩ stopSet S))
      ≤ ∑ l ∈ leaves S n [], lik S μ0 l * ((N : ℝ) - (unreq S x l).card) := by
    have := sum_le_sum (s := (univ : Finset (Fin N))) fun j _ => step2 j
    rw [sum_comm] at this
    refine this.trans (le_of_eq (sum_congr rfl fun l _ => ?_))
    rw [← mul_sum, sum_requested]
  calc ((N : ℝ) + 1) / 2
        * ∑ j, (prob S μ0 n (B ∩ stopSet S) - prob S (μs j) n (B ∩ stopSet S))
      ≤ ((N : ℝ) + 1) / 2
          * ∑ l ∈ leaves S n [], lik S μ0 l * ((N : ℝ) - (unreq S x l).card) :=
        mul_le_mul_of_nonneg_left step4 (by positivity)
    _ ≤ ∑ j, ∑ l ∈ leaves S n [], lik S μ0 l * (quiet S (x j) l : ℝ) := step3
    _ ≤ ∑ j, expTime S (μs j) n := sum_le_sum fun j _ => step1 j

/-- Discovery cost for a randomised sampler, general form: if the procedure stops in the
(seed-dependent) set `B` with probability at least `1 - δ` under the null instance and at most
`δ` under each `μ^j`, and has finite expected stopping time under each `μ^j`, then some `μ^j`
has `E_{μ^j} τ ≥ (N+1)/2 · (1 - 2δ)`. -/
theorem discovery_general_rand (hN : 0 < N) (ν : Measure Sd) [IsProbabilityMeasure ν]
    (R : RSampler Z Sd) {x : Fin N → Z} (hx : Function.Injective x) {μ0 : Z → ℝ}
    {μs : Fin N → Z → ℝ} (h0 : ∀ z, 0 < μ0 z ∧ μ0 z < 1) (hs : ∀ j z, 0 < μs j z ∧ μs j z < 1)
    (hagree : ∀ j z, z ≠ x j → μs j z = μ0 z) {B : Sd → Set (List Bool)} (hBm : SeedEvent B)
    {δ : ℝ} (hB0 : 1 - δ ≤ rprobInf ν R μ0 B) (hδ : ∀ j, rprobInf ν R (μs j) B ≤ δ)
    {Bd : Fin N → ℝ} (hBd : ∀ j n, rexpTime ν R (μs j) n ≤ Bd j) :
    ∃ j, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) ≤ rexpTimeInf ν R (μs j) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBs := hBm.inter (seedEvent_stop R)
  have hfin : ∀ n, ((N : ℝ) + 1) / 2
      * (N * (rprob ν R μ0 n (fun s => B s ∩ stopSet (R.run s)) - δ))
      ≤ ∑ j, rexpTimeInf ν R (μs j) := by
    intro n
    have hI : ∀ j ∈ (univ : Finset (Fin N)), Integrable (fun s =>
        prob (R.run s) μ0 n (B s ∩ stopSet (R.run s))
          - prob (R.run s) (μs j) n (B s ∩ stopSet (R.run s))) ν := fun j _ =>
      (integrable_prob ν R h0 n hBs).sub (integrable_prob ν R (hs j) n hBs)
    have hS : Integrable (fun s => ∑ j, (prob (R.run s) μ0 n (B s ∩ stopSet (R.run s))
          - prob (R.run s) (μs j) n (B s ∩ stopSet (R.run s)))) ν :=
      integrable_finsetSum _ hI
    have hL : Integrable (fun s => ((N : ℝ) + 1) / 2
        * ∑ j, (prob (R.run s) μ0 n (B s ∩ stopSet (R.run s))
          - prob (R.run s) (μs j) n (B s ∩ stopSet (R.run s)))) ν :=
      hS.const_mul _
    have hRi : Integrable (fun s => ∑ j, expTime (R.run s) (μs j) n) ν :=
      integrable_finsetSum _ fun j _ => integrable_expTime ν R (hs j) n
    have h1 := integral_mono hL hRi fun s =>
      discovery_finite_seed (R.run s) hx h0 hs hagree (B s) n
    rw [integral_const_mul, integral_finsetSum _ hI,
      integral_finsetSum _ fun j _ => integrable_expTime ν R (hs j) n] at h1
    have e : ∀ j : Fin N, ∫ s, (prob (R.run s) μ0 n (B s ∩ stopSet (R.run s))
          - prob (R.run s) (μs j) n (B s ∩ stopSet (R.run s))) ∂ν
        = rprob ν R μ0 n (fun s => B s ∩ stopSet (R.run s))
          - rprob ν R (μs j) n (fun s => B s ∩ stopSet (R.run s)) := fun j =>
      integral_sub (integrable_prob ν R h0 n hBs) (integrable_prob ν R (hs j) n hBs)
    simp only [e] at h1
    have h2 : ∑ _j : Fin N, (rprob ν R μ0 n (fun s => B s ∩ stopSet (R.run s)) - δ)
        ≤ ∑ j : Fin N, (rprob ν R μ0 n (fun s => B s ∩ stopSet (R.run s))
          - rprob ν R (μs j) n (fun s => B s ∩ stopSet (R.run s))) :=
      sum_le_sum fun j _ => by
        have := (rprob_le_rprobInf ν R (hs j) n hBm).trans (hδ j)
        linarith
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : ∑ j, ∫ s, expTime (R.run s) (μs j) n ∂ν ≤ ∑ j, rexpTimeInf ν R (μs j) :=
      sum_le_sum fun j _ => rexpTime_le_rexpTimeInf ν R (hs j) (hBd j) n
    exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans (h1.trans h3)
  have hlim : Tendsto (fun n => ((N : ℝ) + 1) / 2
      * (N * (rprob ν R μ0 n (fun s => B s ∩ stopSet (R.run s)) - δ)))
      atTop (𝓝 (((N : ℝ) + 1) / 2 * (N * (rprobInf ν R μ0 B - δ)))) :=
    (((tendsto_rprob ν R h0 hBm).sub_const δ).const_mul _).const_mul _
  have hsum : ((N : ℝ) + 1) / 2 * (N * (rprobInf ν R μ0 B - δ))
      ≤ ∑ j, rexpTimeInf ν R (μs j) := le_of_tendsto' hlim hfin
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h5 : ∑ j : Fin N, rexpTimeInf ν R (μs j)
      < ∑ _j : Fin N, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) :=
    sum_lt_sum_of_nonempty univ_nonempty fun j _ => hcon j
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h5
  have h6 : (N : ℝ) * (1 - 2 * δ) ≤ N * (rprobInf ν R μ0 B - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hNr.le
  nlinarith [mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1) / 2)]

/-- The two root supports of `prop:ast-discovery`: `true ↦ S_A = {c, x_1, …, x_N}`,
`false ↦ S_B = {c, z}`. -/
def discSupp (N : ℕ) : Bool → Finset (Fan N)
  | true => fanSupp N
  | false => pairSupp N

/-- **A discovery cost absent from the characteristic time** (`prop:ast-discovery`) for
randomised procedures.  `R` is a randomised adaptive sampler on the terminals
`c, z, x_1, …, x_N` with seed law `ν` and decision rule `dec` (`true` = action `A`,
`false` = action `B`; by `discovery_instances`, `B` is the unique correct answer under the null
instance and `A` under every `μ^j`).  Hypotheses on the procedure only: `hcorr0`, `hcorr` are
`δ`-correctness with almost-sure stopping on the `N + 1` instances; `hBd` is finiteness of the
expected stopping time at each `μ^j`.  Conclusion: some instance `μ^j` has
`E_{μ^j} τ ≥ (N+1)/2 · (1 - 2δ)`, while `C_A^0(μ^j) ≥ g²/2` and `C_*^0(μ^j) ≥ g²/2`
(`C_*^0 = max {C_A^0, C_B^0}` over the two actions `discSupp`). -/
theorem discovery_cost_rand (hN : 0 < N) {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8) {δ : ℝ}
    (ν : Measure Sd) [IsProbabilityMeasure ν] (R : RSampler (Fan N) Sd)
    (dec : Sd → List Bool → Bool) (hdec : ∀ l a, MeasurableSet {s | dec s l = a})
    (hcorr0 : 1 - δ ≤ rprobInf ν R (discMu N g none) (fun s => {l | dec s l = false}))
    (hcorr : ∀ j : Fin N,
      1 - δ ≤ rprobInf ν R (discMu N g (some j)) (fun s => {l | dec s l = true}))
    {Bd : Fin N → ℝ} (hBd : ∀ j n, rexpTime ν R (discMu N g (some j)) n ≤ Bd j) :
    ∃ j : Fin N, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) ≤ rexpTimeInf ν R (discMu N g (some j)) ∧
      g ^ 2 / 2 ≤ charRate (fanSupp N) 0 (discMu N g (some j)) ∧
      g ^ 2 / 2 ≤ charStar (discSupp N) 0 (discMu N g (some j)) := by
  have hF : SeedEvent (fun s => {l : List Bool | dec s l = false}) :=
    seedEvent_dec hdec (fun a => a = false)
  have hT : SeedEvent (fun s => {l : List Bool | dec s l = true}) :=
    seedEvent_dec hdec (fun a => a = true)
  obtain ⟨j, hj⟩ := discovery_general_rand hN ν R (x := fun j : Fin N => (some (some j) : Fan N))
    (fun i j e => by simpa using e) (discMu_interior hg hg8 none)
    (fun j => discMu_interior hg hg8 (some j)) (fun j z hz => discMu_agree N g j z hz)
    hF hcorr0 (fun j => by
      have hdis : ∀ s, Disjoint {l : List Bool | dec s l = false} {l | dec s l = true} :=
        fun s => Set.disjoint_left.2 fun l h1 h2 => by
          rw [Set.mem_ofPred_eq] at h1 h2
          rw [h1] at h2
          exact Bool.false_ne_true h2
      have := rprobInf_add_le_one ν R (discMu_interior hg hg8 (some j)) hF hT hdis
      linarith [hcorr j]) hBd
  have hr := discovery_rate hg hg8 j
  exact ⟨j, hj, hr, hr.trans (charRate_le_charStar (discSupp N) 0 (discMu N g (some j)) true)⟩

end Discovery

/-! ### The lower bound of `thm:ast-main` for randomised procedures -/

section MultiAnswer

variable [Nonempty Z]

/-- Finite-confidence core of the multiple-answer lower bound for one deterministic sampler,
with the probability of each listed wrong answer kept explicit (`Stopped.multi_answer_finite`
bounds each of them by `δ`).  `P` is a finite list of pairs (answer, alternative) whose
alternatives are interior, have one-step log-likelihood-ratio variances at most `c`, and serve
every answer and allocation at cost at most `C'`.  Then for every horizon `T` and level
`x > T C'`,
`P_μ(τ ≤ T) ≤ ∑_{(a,λ) ∈ P} (e^x P_λ(τ ≤ T, â = a) + c T / (x - T C')²)`. -/
theorem multi_answer_finite_seed {A : Type*} (S : Sampler Z) (dec : List Bool → A) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (P : Finset (A × (Z → ℝ))) {C' c x : ℝ} (T : ℕ)
    (hPint : ∀ q ∈ P, ∀ z, 0 < q.2 z ∧ q.2 z < 1)
    (hPc : ∀ q ∈ P, ∀ z, llrVar (μ z) (q.2 z) ≤ c)
    (hcover : ∀ a, ∀ w ∈ simplex Z, ∃ lam, (a, lam) ∈ P ∧ infoCost w μ lam ≤ C')
    (hx : T * C' < x) :
    prob S μ T (stopSet S) ≤ ∑ q ∈ P,
      (exp x * prob S q.2 T ({l | dec l = q.1} ∩ stopSet S) + c * T / (x - T * C') ^ 2) := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hy : 0 < x - T * C' := sub_pos.2 hx
  have hsub : ∀ l ∈ stopSet S ∩ ↑(leaves S T []),
      ∃ q ∈ P, l ∈ ({l | dec l = q.1} ∩
        {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (q.2 z) ≤ T * C'}) ∩ stopSet S := by
    rintro l ⟨hs, hl⟩
    have hlen : (l.length : ℝ) ≤ T := by
      have := length_le_of_mem_leaves S T [] l hl
      simp only [List.length_nil, zero_add] at this
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos l.length with h0 | h0
    · obtain ⟨lam, hq, hcost⟩ := hcover (dec l) _ uniform_mem_simplex
      have hC0 : 0 ≤ C' :=
        (infoCost_nonneg (fun _ => by positivity) hμ' (hPint _ hq)).trans hcost
      refine ⟨(dec l, lam), hq, ⟨rfl, ?_⟩, hs⟩
      have hz : ∀ z, cnt S z l = 0 := fun z => by
        have := sum_cnt S l
        rw [h0] at this
        exact (Finset.sum_eq_zero_iff.1 this) z (mem_univ z)
      show ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) ≤ T * C'
      simp only [hz, Nat.cast_zero, zero_mul, sum_const_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hC0
    · have hL : (0 : ℝ) < l.length := by exact_mod_cast h0
      have hw : (fun z => (cnt S z l : ℝ) / l.length) ∈ simplex Z := by
        refine ⟨fun z => by positivity, ?_⟩
        rw [← sum_div, ← Nat.cast_sum, sum_cnt, div_self hL.ne']
      obtain ⟨lam, hq, hcost⟩ := hcover (dec l) _ hw
      have hC0 : 0 ≤ C' := (infoCost_nonneg hw.1 hμ' (hPint _ hq)).trans hcost
      refine ⟨(dec l, lam), hq, ⟨rfl, ?_⟩, hs⟩
      show ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) ≤ T * C'
      have e : ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z)
          = l.length * infoCost (fun z => (cnt S z l : ℝ) / l.length) μ lam := by
        unfold infoCost
        rw [mul_sum]
        refine sum_congr rfl fun z _ => ?_
        field_simp
      rw [e]
      calc (l.length : ℝ) * infoCost (fun z => (cnt S z l : ℝ) / l.length) μ lam
          ≤ l.length * C' := mul_le_mul_of_nonneg_left hcost hL.le
        _ ≤ T * C' := mul_le_mul_of_nonneg_right hlen hC0
  have hstep : prob S μ T (stopSet S)
      ≤ ∑ q ∈ P, prob S μ T (({l | dec l = q.1} ∩
        {l | ∑ z, (cnt S z l : ℝ) * bkl (μ z) (q.2 z) ≤ T * C'}) ∩ stopSet S) := by
    have h1 : prob S μ T (stopSet S) = prob S μ T (stopSet S ∩ ↑(leaves S T [])) := by
      unfold prob
      refine sum_congr rfl fun l hl => ?_
      by_cases hs : l ∈ stopSet S
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show l ∈ stopSet S ∩ _ from ⟨hs, hl⟩)]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (show l ∉ stopSet S ∩ _ from fun h => hs h.1)]
    rw [h1]
    exact prob_le_sum_of_subset S hμ T P _ _ hsub
  refine hstep.trans (sum_le_sum fun q hq => ?_)
  have h1 := prob_event_le S hμ (hPint q hq) T {l | dec l = q.1} (x := x) (b := T * C')
  have h3 := chebyshev_mart S hμ (hPc q hq) T hy
  have h4 : prob S μ T {l | x - T * C' < mart S μ q.2 l} ≤ c * T / (x - T * C') ^ 2 := by
    rw [le_div_iff₀ (pow_pos hy 2)]
    linarith
  linarith

variable {A : Type*} [Fintype A] [Nonempty A]

/-- **Lower bound with several correct answers for randomised procedures**
(`eq:ast-lower-main`), finite-horizon form; no finiteness of the expected stopping time is
assumed.

`R δ`, `dec δ` is a family of randomised adaptive samplers (seed law `ν δ`) with decision rules
into a finite family of proper root supports `Sup`.  `Dom` is the parameter domain on which
correctness is required and `hdense` says that restricting alternatives to `Dom` leaves every
information infimum unchanged.  `hcorr` is uniform correctness: for `0 < δ < 1` and every
interior parameter in `Dom`, the procedure stops and returns an answer that is not
`ε`-incorrect with probability at least `1 - δ` (probability over observations and seed).

Conclusion: for every `c₀ < 1 / C_*^ε(μ)`, for all sufficiently small `δ` there is a horizon
`n` with `E_μ[τ_δ ∧ n] ≥ c₀ log(1/δ)`. -/
theorem lower_bound_multi_answer_trunc_rand (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup ε μ)
    (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RSampler Z Sd) (dec : ℝ → Sd → List Bool → A)
    (hdec : ∀ δ l a, MeasurableSet {s | dec δ s l = a}) (Dom : Set (Z → ℝ))
    (hdense : ∀ a, ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt (Sup a) ε, lam ∈ Dom ∧
      infoCost w μ lam < infoRate (Sup a) ε w μ + η)
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ Dom, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ rprobInf (ν δ) (R δ) lam (fun s => {l | lam ∉ Alt (Sup (dec δ s l)) ε}))
    {c₀ : ℝ} (hc₀ : c₀ < 1 / charStar Sup ε μ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ n, c₀ * log (1 / δ) ≤ rexpTime (ν δ) (R δ) μ n := by
  classical
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = charStar Sup ε μ := ⟨_, rfl⟩
  rw [← hCdef] at hC hc₀
  have hc₀C : c₀ * C < 1 := by rwa [lt_div_iff₀ hC] at hc₀
  obtain ⟨κ, hκ0, hκ1, hκc⟩ : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧ c₀ < (1 - κ) / C := by
    refine ⟨min (1 / 2) ((1 - c₀ * C) / 2), lt_min (by norm_num) (by linarith), min_le_left _ _,
      ?_⟩
    rw [lt_div_iff₀ hC]
    have := min_le_right (1 / 2 : ℝ) ((1 - c₀ * C) / 2)
    linarith
  have hκ' : 0 < 1 - κ := by linarith
  set ζ : ℝ := κ * C / (4 * (1 - κ)) with hζdef
  have hζ : 0 < ζ := by positivity
  have hlist : ∀ a, ∃ Λ : Finset (Z → ℝ), (∀ lam ∈ Λ, lam ∈ Alt (Sup a) ε ∧ lam ∈ Dom) ∧
      ∀ w ∈ simplex Z, ∃ lam ∈ Λ, infoCost w μ lam ≤ C + ζ := fun a =>
    exists_finite_alternatives (hSc a) hε0 hε1 hμ' Dom (hdense a)
      (hCdef ▸ charRate_le_charStar Sup ε μ a) hζ
  choose Λ hΛ hΛcov using hlist
  set P : Finset (A × (Z → ℝ)) := univ.biUnion fun a => (Λ a).image fun lam => (a, lam) with hP
  have hPmem : ∀ q, q ∈ P ↔ q.2 ∈ Λ q.1 := by
    rintro ⟨a, lam⟩
    simp only [hP, mem_biUnion, mem_univ, true_and, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨a', lam', hl, rfl, rfl⟩
      exact hl
    · intro hl
      exact ⟨a, lam, hl, rfl, rfl⟩
  have hPint : ∀ q ∈ P, ∀ z, 0 < q.2 z ∧ q.2 z < 1 := fun q hq =>
    (hΛ q.1 q.2 ((hPmem q).1 hq)).1.1
  have hcover : ∀ a, ∀ w ∈ simplex Z, ∃ lam, (a, lam) ∈ P ∧ infoCost w μ lam ≤ C + ζ := by
    intro a w hw
    obtain ⟨lam, hl, hc⟩ := hΛcov a w hw
    exact ⟨lam, (hPmem (a, lam)).2 hl, hc⟩
  set c : ℝ := ∑ q ∈ P, ∑ z, llrVar (μ z) (q.2 z) with hcdef
  have hPc : ∀ q ∈ P, ∀ z, llrVar (μ z) (q.2 z) ≤ c := by
    intro q hq z
    have h1 : llrVar (μ z) (q.2 z) ≤ ∑ z, llrVar (μ z) (q.2 z) :=
      single_le_sum (f := fun z => llrVar (μ z) (q.2 z))
        (fun z _ => llrVar_nonneg (hμ' z).1 (hμ' z).2) (mem_univ z)
    have h2 : ∑ z, llrVar (μ z) (q.2 z) ≤ c :=
      single_le_sum (f := fun q : A × (Z → ℝ) => ∑ z, llrVar (μ z) (q.2 z))
        (fun q _ => sum_nonneg fun z _ => llrVar_nonneg (hμ' z).1 (hμ' z).2) hq
    exact h1.trans h2
  have hc0 : 0 ≤ c :=
    sum_nonneg fun q _ => sum_nonneg fun z _ => llrVar_nonneg (hμ' z).1 (hμ' z).2
  set c' : ℝ := 16 * c * (1 - κ) / (C * κ ^ 2) with hc'def
  have hlim := tendsto_rate_factor ((1 - κ) / C) P.card c' κ hκ0
  have hev1 : ∀ᶠ L : ℝ in atTop,
      c₀ < ((1 - κ) / C - 1 / L) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L)) :=
    hlim.eventually_const_lt hκc
  have hlim2 : Tendsto (fun L : ℝ => 1 - P.card * (exp (-(κ / 2) * L) + c' / L)) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun L : ℝ => 1 / L) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h2 : Tendsto (fun L : ℝ => c' / L) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c'
    have h3 : Tendsto (fun L : ℝ => exp (-(κ / 2) * L)) atTop (𝓝 0) := by
      refine tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ((h3.add h2).const_mul (P.card : ℝ))
  have hev2 : ∀ᶠ L : ℝ in atTop, 0 < 1 - P.card * (exp (-(κ / 2) * L) + c' / L) :=
    hlim2.eventually_const_lt zero_lt_one
  have hLtend : Tendsto (fun δ : ℝ => log (1 / δ)) (𝓝[>] 0) atTop := by
    have : Tendsto (fun δ : ℝ => -log δ) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
    refine this.congr fun δ => ?_
    rw [one_div, log_inv]
  have hδ1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hLtend.eventually hev1, hLtend.eventually hev2, hδ1] with δ h1 h2 hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  obtain ⟨L, hL⟩ : ∃ L, L = log (1 / δ) := ⟨_, rfl⟩
  rw [← hL] at h1 h2 ⊢
  have hLpos : 0 < L := by
    rw [hL]
    exact log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hδexp : δ = exp (-L) := by
    rw [hL, one_div, log_inv, neg_neg, exp_log hδ0]
  set T : ℕ := ⌊(1 - κ) * L / C⌋₊ with hT
  have hTle : (T : ℝ) ≤ (1 - κ) * L / C := Nat.floor_le (by positivity)
  have hTge : (1 - κ) * L / C - 1 < T := by
    have := Nat.lt_floor_add_one ((1 - κ) * L / C)
    linarith
  set x : ℝ := (1 - κ / 2) * L with hxdef
  have hTC : (T : ℝ) * (C + ζ) ≤ (1 - κ) * L + κ * L / 4 := by
    have h := mul_le_mul_of_nonneg_right hTle (add_pos hC hζ).le
    have e : (1 - κ) * L / C * (C + ζ) = (1 - κ) * L + κ * L / 4 := by
      rw [hζdef]
      field_simp
    linarith
  have hy : κ * L / 4 ≤ x - T * (C + ζ) := by
    rw [hxdef]
    linarith
  have hyp : 0 < κ * L / 4 := by positivity
  have hx : (T : ℝ) * (C + ζ) < x := by linarith
  -- seed-measurability of the answer events
  have hEdec : ∀ a : A, SeedEvent (fun s => {l : List Bool | dec δ s l = a}) := fun a =>
    seedEvent_dec (hdec δ) (fun a' => a' = a)
  have hEalt : ∀ lam : Z → ℝ,
      SeedEvent (fun s => {l : List Bool | lam ∉ Alt (Sup (dec δ s l)) ε}) := fun lam =>
    seedEvent_dec (hdec δ) (fun a' => lam ∉ Alt (Sup a') ε)
  -- correctness at the listed alternatives, averaged over the seed
  have hPδ : ∀ q ∈ P, rprobInf (ν δ) (R δ) q.2 (fun s => {l | dec δ s l = q.1}) ≤ δ := by
    intro q hq
    obtain ⟨hqA, hqD⟩ := hΛ q.1 q.2 ((hPmem q).1 hq)
    have hc := hcorr δ hδ0 hδ1 q.2 hqD hqA.1
    have hdis : ∀ s, Disjoint {l : List Bool | dec δ s l = q.1}
        {l | q.2 ∉ Alt (Sup (dec δ s l)) ε} :=
      fun s => Set.disjoint_left.2 fun l h1 h2 => by
        rw [Set.mem_ofPred_eq] at h1 h2
        rw [h1] at h2
        exact h2 hqA
    have := rprobInf_add_le_one (ν δ) (R δ) hqA.1 (hEdec q.1) (hEalt q.2) hdis
    linarith
  -- the seed-wise bound, averaged
  have hfin : rprob (ν δ) (R δ) μ T (fun s => stopSet ((R δ).run s))
      ≤ P.card * (exp x * δ + c * T / (x - T * (C + ζ)) ^ 2) := by
    have hI : ∀ q ∈ P, Integrable (fun s =>
        exp x * prob ((R δ).run s) q.2 T ({l | dec δ s l = q.1} ∩ stopSet ((R δ).run s))
          + c * T / (x - T * (C + ζ)) ^ 2) (ν δ) := fun q hq =>
      ((integrable_prob (ν δ) (R δ) (hPint q hq) T
        ((hEdec q.1).inter (seedEvent_stop (R δ)))).const_mul _).add (integrable_const _)
    have h1 := integral_mono (integrable_prob (ν δ) (R δ) hμ T (seedEvent_stop (R δ)))
      (integrable_finsetSum _ hI) fun s =>
      multi_answer_finite_seed ((R δ).run s) (dec δ s) hμ P T hPint hPc hcover hx
    rw [integral_finsetSum _ hI] at h1
    refine h1.trans ?_
    have ecard : (P.card : ℝ) * (exp x * δ + c * T / (x - T * (C + ζ)) ^ 2)
        = ∑ _q ∈ P, (exp x * δ + c * T / (x - T * (C + ζ)) ^ 2) := by
      rw [sum_const, nsmul_eq_mul]
    rw [ecard]
    refine sum_le_sum fun q hq => ?_
    have hp := integrable_prob (ν δ) (R δ) (hPint q hq) T
      ((hEdec q.1).inter (seedEvent_stop (R δ)))
    have hp' : Integrable (fun s => exp x
        * prob ((R δ).run s) q.2 T ({l | dec δ s l = q.1} ∩ stopSet ((R δ).run s))) (ν δ) :=
      hp.const_mul _
    have e : ∫ s, (exp x
          * prob ((R δ).run s) q.2 T ({l | dec δ s l = q.1} ∩ stopSet ((R δ).run s))
          + c * T / (x - T * (C + ζ)) ^ 2) ∂(ν δ)
        = exp x * rprob (ν δ) (R δ) q.2 T
            (fun s => {l | dec δ s l = q.1} ∩ stopSet ((R δ).run s))
          + c * T / (x - T * (C + ζ)) ^ 2 := by
      rw [integral_add hp' (integrable_const _), integral_const_mul]
      simp [rprob]
    rw [e]
    have h2 : rprob (ν δ) (R δ) q.2 T
        (fun s => {l | dec δ s l = q.1} ∩ stopSet ((R δ).run s)) ≤ δ :=
      (rprob_le_rprobInf (ν δ) (R δ) (hPint q hq) T (hEdec q.1)).trans (hPδ q hq)
    have h3 := mul_le_mul_of_nonneg_left h2 (exp_pos x).le
    linarith
  have hb1 : exp x * δ = exp (-(κ / 2) * L) := by
    rw [hδexp, ← exp_add, hxdef]
    congr 1
    ring
  have hb2 : c * T / (x - T * (C + ζ)) ^ 2 ≤ c' / L := by
    have h3 : c * (T : ℝ) ≤ c * ((1 - κ) * L / C) := mul_le_mul_of_nonneg_left hTle hc0
    have h4 : (κ * L / 4) ^ 2 ≤ (x - T * (C + ζ)) ^ 2 := pow_le_pow_left₀ hyp.le hy 2
    have h5 : c * T / (x - T * (C + ζ)) ^ 2 ≤ c * ((1 - κ) * L / C) / (κ * L / 4) ^ 2 :=
      div_le_div₀ (mul_nonneg hc0 (by positivity)) h3 (pow_pos hyp 2) h4
    have e : c * ((1 - κ) * L / C) / (κ * L / 4) ^ 2 = c' / L := by
      rw [hc'def]
      field_simp
      ring
    linarith
  have hprob : rprob (ν δ) (R δ) μ T (fun s => stopSet ((R δ).run s))
      ≤ P.card * (exp (-(κ / 2) * L) + c' / L) := by
    refine hfin.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [hb1]
    linarith
  have hns : 1 - P.card * (exp (-(κ / 2) * L) + c' / L)
      ≤ rprob (ν δ) (R δ) μ T (fun s => (stopSet ((R δ).run s))ᶜ) := by
    have := rprob_compl (ν δ) (R δ) hμ T (seedEvent_stop (R δ))
    linarith
  have hmark := rprob_not_stop_mul_le (ν δ) (R δ) hμ T
  refine ⟨T, ?_⟩
  have hfac := h2.le
  have h6 : ((1 - κ) * L / C - 1) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L))
      ≤ rprob (ν δ) (R δ) μ T (fun s => (stopSet ((R δ).run s))ᶜ) * T := by
    calc ((1 - κ) * L / C - 1) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L))
        ≤ (T : ℝ) * (1 - P.card * (exp (-(κ / 2) * L) + c' / L)) :=
          mul_le_mul_of_nonneg_right hTge.le hfac
      _ ≤ (T : ℝ) * rprob (ν δ) (R δ) μ T (fun s => (stopSet ((R δ).run s))ᶜ) :=
          mul_le_mul_of_nonneg_left hns (Nat.cast_nonneg _)
      _ = rprob (ν δ) (R δ) μ T (fun s => (stopSet ((R δ).run s))ᶜ) * T := mul_comm _ _
  have e7 : ((1 - κ) * L / C - 1) = L * ((1 - κ) / C - 1 / L) := by
    field_simp
  rw [e7, mul_assoc] at h6
  have h8 : c₀ * L ≤ L * (((1 - κ) / C - 1 / L)
      * (1 - P.card * (exp (-(κ / 2) * L) + c' / L))) := by
    rw [mul_comm c₀ L]
    exact mul_le_mul_of_nonneg_left h1.le hLpos.le
  linarith

/-- **`eq:ast-lower-main` for randomised procedures**, as the manuscript writes it:
`liminf_{δ ↓ 0} E_μ[τ_δ] / log(1/δ) ≥ 1 / C_*^ε(μ)`, in the extended reals.  Hypotheses as in
`lower_bound_multi_answer_trunc_rand`, and finite expected stopping time at `μ` for every `δ`
(`hB`; if it is infinite the manuscript's bound is trivial). -/
theorem lower_bound_liminf_rand (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup ε μ)
    (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RSampler Z Sd) (dec : ℝ → Sd → List Bool → A)
    (hdec : ∀ δ l a, MeasurableSet {s | dec δ s l = a}) (Dom : Set (Z → ℝ))
    (hdense : ∀ a, ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt (Sup a) ε, lam ∈ Dom ∧
      infoCost w μ lam < infoRate (Sup a) ε w μ + η)
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ Dom, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ rprobInf (ν δ) (R δ) lam (fun s => {l | lam ∉ Alt (Sup (dec δ s l)) ε}))
    (hB : ∀ δ, ∃ B, ∀ n, rexpTime (ν δ) (R δ) μ n ≤ B) :
    ((1 / charStar Sup ε μ : ℝ) : EReal)
      ≤ Filter.liminf
          (fun δ : ℝ => ((rexpTimeInf (ν δ) (R δ) μ / log (1 / δ) : ℝ) : EReal)) (𝓝[>] 0) := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  induction c using EReal.rec with
  | bot => exact bot_le
  | coe r =>
    have hr : r < 1 / charStar Sup ε μ := EReal.coe_lt_coe_iff.1 hc
    have h := lower_bound_multi_answer_trunc_rand Sup hSc hε0 hε1 hμ hC ν R dec hdec Dom hdense
      hcorr hr
    have hδ1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [h, hδ1] with δ hn hδ
    obtain ⟨n, hn⟩ := hn
    obtain ⟨B, hB'⟩ := hB δ
    have hle := rexpTime_le_rexpTimeInf (ν δ) (R δ) hμ hB' n
    have hL : 0 < log (1 / δ) := log_pos (by rw [lt_div_iff₀ hδ.1]; linarith [hδ.2])
    refine EReal.coe_le_coe_iff.2 ?_
    rw [le_div_iff₀ hL]
    linarith
  | top => exact absurd hc (not_lt.2 le_top)

/-- **`eq:ast-lower-main` for randomised procedures, `ε > 0`** (and any `ε ∈ [0,1)` when
correctness holds on all of `(0,1)^M`).  Every family of randomised procedures that is
uniformly correct on the interior parameters satisfies
`liminf_{δ↓0} E_μ τ_δ / log(1/δ) ≥ 1 / C_*^ε(μ)`. -/
theorem ast_lower_main_rand (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup ε μ)
    (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RSampler Z Sd) (dec : ℝ → Sd → List Bool → A)
    (hdec : ∀ δ l a, MeasurableSet {s | dec δ s l = a})
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam : Z → ℝ, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ rprobInf (ν δ) (R δ) lam (fun s => {l | lam ∉ Alt (Sup (dec δ s l)) ε}))
    (hB : ∀ δ, ∃ B, ∀ n, rexpTime (ν δ) (R δ) μ n ≤ B) :
    ((1 / charStar Sup ε μ : ℝ) : EReal)
      ≤ Filter.liminf
          (fun δ : ℝ => ((rexpTimeInf (ν δ) (R δ) μ / log (1 / δ) : ℝ) : EReal)) (𝓝[>] 0) :=
  lower_bound_liminf_rand Sup hSc hε0 hε1 hμ hC ν R dec hdec Set.univ
    (fun a w _ _ hη => alt_dense_univ (hSc a) hε0 hε1 w μ hη)
    (fun δ h0 h1 lam _ hlam => hcorr δ h0 h1 lam hlam) hB

/-- **`eq:ast-lower-main` for randomised procedures, exact identification** (`ε = 0`):
correctness is required only on `𝒟_0 = {Γ > 0}`; the supports are proper and cover `Z`. -/
theorem ast_lower_main_exact_rand (Sup : A → Finset Z)
    (hSc : ∀ a, (Sup a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ Sup a) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hC : 0 < charStar Sup 0 μ)
    (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RSampler Z Sd) (dec : ℝ → Sd → List Bool → A)
    (hdec : ∀ δ l a, MeasurableSet {s | dec δ s l = a})
    (hcorr : ∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ exactDomain Sup, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ rprobInf (ν δ) (R δ) lam (fun s => {l | lam ∉ Alt (Sup (dec δ s l)) 0}))
    (hB : ∀ δ, ∃ B, ∀ n, rexpTime (ν δ) (R δ) μ n ≤ B) :
    ((1 / charStar Sup 0 μ : ℝ) : EReal)
      ≤ Filter.liminf
          (fun δ : ℝ => ((rexpTimeInf (ν δ) (R δ) μ / log (1 / δ) : ℝ) : EReal)) (𝓝[>] 0) :=
  lower_bound_liminf_rand Sup hSc le_rfl zero_lt_one hμ hC ν R dec hdec (exactDomain Sup)
    (fun a w _ _ hη => alt_dense_exactDomain Sup hcov a (hSc a) le_rfl zero_lt_one w μ hη)
    hcorr hB

end MultiAnswer

/-! ### `thm:ast-main` as one statement -/

section Main

universe u

variable {A : Type*} [Fintype A] [Nonempty A] [Nonempty Z]

/-- **`thm:ast-main` "One inside witness and Bernoulli information limit", the information
limit as one statement, for `0 < ε < 1`.**  For a finite family of root actions with proper
nonempty supports covering `Z`:

1. (lower bound, `eq:ast-lower-main`) for every family of randomised procedures (any seed
   space `Sd'`, seed laws `ν δ`, samplers `R δ`, answers `dec δ`) that is uniformly correct on
   the interior parameters, and every interior `μ`: for every `c₀ < 1 / C_*^ε(μ)` eventually
   `E_μ[τ_δ ∧ n] ≥ c₀ log(1/δ)` for some horizon `n`; and, when the expected stopping times at
   `μ` are finite, `liminf_{δ↓0} E_μ τ_δ / log(1/δ) ≥ 1 / C_*^ε(μ)`;
2. (attainment) there is a procedure, deterministic and therefore a randomised procedure with
   a point-mass seed, that is uniformly correct on the interior parameters, has finite expected
   stopping time and satisfies `lim_{δ↓0} E_μ τ_δ / log(1/δ) = 1 / C_*^ε(μ)` at every interior
   `μ`.

`C_*^ε(μ) > 0` holds at every interior `μ` because `ε > 0` and the supports cover `Z`
(`charStar_pos_of_cover`).  The one-witness formula `eq:ast-star` is `one_witness_reduction`
(`BernoulliInfo.lean`). -/
theorem ast_main_full (SupA : A → Finset Z) (hS : ∀ a, (SupA a).Nonempty)
    (hSc : ∀ a, (SupA a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ SupA a) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    (∀ (Sd' : Type u) [MeasurableSpace Sd'] (ν : ℝ → Measure Sd')
        [∀ δ, IsProbabilityMeasure (ν δ)] (R : ℝ → RSampler Z Sd')
        (dec : ℝ → Sd' → List Bool → A),
        (∀ δ l a, MeasurableSet {s | dec δ s l = a}) →
        (∀ δ, 0 < δ → δ < 1 → ∀ lam : Z → ℝ, (∀ z, 0 < lam z ∧ lam z < 1) →
          1 - δ ≤ rprobInf (ν δ) (R δ) lam
            (fun s => {l | lam ∉ Alt (SupA (dec δ s l)) ε})) →
        ∀ μ : Z → ℝ, (∀ z, 0 < μ z ∧ μ z < 1) →
          (∀ c₀ : ℝ, c₀ < 1 / charStar SupA ε μ →
            ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ n, c₀ * log (1 / δ) ≤ rexpTime (ν δ) (R δ) μ n) ∧
          ((∀ δ, ∃ B, ∀ n, rexpTime (ν δ) (R δ) μ n ≤ B) →
            ((1 / charStar SupA ε μ : ℝ) : EReal)
              ≤ Filter.liminf (fun δ : ℝ =>
                  ((rexpTimeInf (ν δ) (R δ) μ / log (1 / δ) : ℝ) : EReal)) (𝓝[>] 0))) ∧
    ∃ (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A),
      (∀ δ : ℝ, 0 < δ → ∀ lam : Z → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
        rprobInf (Measure.dirac ()) (RSampler.const (S δ)) lam
            (fun _ => {l | lam ∈ Alt (SupA (dec δ l)) ε}) ≤ δ ∧
        1 - δ ≤ rprobInf (Measure.dirac ()) (RSampler.const (S δ)) lam
            (fun _ => {l | lam ∉ Alt (SupA (dec δ l)) ε})) ∧
      ∀ μ : Z → ℝ, (∀ i, 0 < μ i ∧ μ i < 1) →
        (∀ δ : ℝ, ∃ Bd : ℝ, ∀ n,
          rexpTime (Measure.dirac ()) (RSampler.const (S δ)) μ n ≤ Bd) ∧
        Tendsto (fun δ : ℝ =>
            rexpTimeInf (Measure.dirac ()) (RSampler.const (S δ)) μ / log (1 / δ))
          (𝓝[>] 0) (𝓝 (1 / charStar SupA ε μ)) := by
  refine ⟨?_, ?_⟩
  · intro Sd' _ ν _ R dec hdec hcorr μ hμ
    have hC := charStar_pos_of_cover SupA hS hSc hcov hε0 hε1 hμ
    exact ⟨fun c₀ hc₀ => lower_bound_multi_answer_trunc_rand SupA hSc hε0.le hε1 hμ hC ν R dec
        hdec Set.univ (fun a w _ _ hη => alt_dense_univ (hSc a) hε0.le hε1 w μ hη)
        (fun δ h0 h1 lam _ hlam => hcorr δ h0 h1 lam hlam) hc₀,
      fun hB => ast_lower_main_rand SupA hSc hε0.le hε1 hμ hC ν R dec hdec hcorr hB⟩
  · obtain ⟨S, dec, h1, h2⟩ := ast_main SupA hS hSc hcov hε0 hε1
    refine ⟨S, dec, ?_, ?_⟩
    · intro δ hδ lam hlam
      rw [rprobInf_const, rprobInf_const]
      exact h1 δ hδ lam hlam
    · intro μ hμ
      simp_rw [rexpTime_const, rexpTimeInf_const]
      exact h2 μ hμ

/-- **`thm:ast-main`, the information limit as one statement, for exact identification
(`ε = 0`)** on the domain `𝒟_0 = {Γ > 0}`: the lower bound for every family of randomised
procedures that is uniformly correct on `𝒟_0`, and a (deterministic) procedure, correct on
`𝒟_0`, attaining `lim_{δ↓0} E_μ τ_δ / log(1/δ) = 1 / C_*^0(μ)` at every interior `μ ∈ 𝒟_0`.
`C_*^0 > 0` on `𝒟_0` (`charStar_pos_of_exactDomain`). -/
theorem ast_main_exact_full (SupA : A → Finset Z) (hS : ∀ a, (SupA a).Nonempty)
    (hSc : ∀ a, (SupA a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ SupA a) :
    (∀ (Sd' : Type u) [MeasurableSpace Sd'] (ν : ℝ → Measure Sd')
        [∀ δ, IsProbabilityMeasure (ν δ)] (R : ℝ → RSampler Z Sd')
        (dec : ℝ → Sd' → List Bool → A),
        (∀ δ l a, MeasurableSet {s | dec δ s l = a}) →
        (∀ δ, 0 < δ → δ < 1 → ∀ lam ∈ exactDomain SupA, (∀ z, 0 < lam z ∧ lam z < 1) →
          1 - δ ≤ rprobInf (ν δ) (R δ) lam
            (fun s => {l | lam ∉ Alt (SupA (dec δ s l)) 0})) →
        ∀ μ ∈ exactDomain SupA, (∀ z, 0 < μ z ∧ μ z < 1) →
          (∀ c₀ : ℝ, c₀ < 1 / charStar SupA 0 μ →
            ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ n, c₀ * log (1 / δ) ≤ rexpTime (ν δ) (R δ) μ n) ∧
          ((∀ δ, ∃ B, ∀ n, rexpTime (ν δ) (R δ) μ n ≤ B) →
            ((1 / charStar SupA 0 μ : ℝ) : EReal)
              ≤ Filter.liminf (fun δ : ℝ =>
                  ((rexpTimeInf (ν δ) (R δ) μ / log (1 / δ) : ℝ) : EReal)) (𝓝[>] 0))) ∧
    ∃ (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A),
      (∀ δ : ℝ, 0 < δ → ∀ lam : Z → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
        rprobInf (Measure.dirac ()) (RSampler.const (S δ)) lam
            (fun _ => {l | lam ∈ Alt (SupA (dec δ l)) 0}) ≤ δ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ lam ∈ exactDomain SupA, (∀ i, 0 < lam i ∧ lam i < 1) →
        1 - δ ≤ rprobInf (Measure.dirac ()) (RSampler.const (S δ)) lam
            (fun _ => {l | lam ∉ Alt (SupA (dec δ l)) 0})) ∧
      ∀ μ ∈ exactDomain SupA, (∀ i, 0 < μ i ∧ μ i < 1) →
        (∀ δ : ℝ, ∃ Bd : ℝ, ∀ n,
          rexpTime (Measure.dirac ()) (RSampler.const (S δ)) μ n ≤ Bd) ∧
        Tendsto (fun δ : ℝ =>
            rexpTimeInf (Measure.dirac ()) (RSampler.const (S δ)) μ / log (1 / δ))
          (𝓝[>] 0) (𝓝 (1 / charStar SupA 0 μ)) := by
  refine ⟨?_, ?_⟩
  · intro Sd' _ ν _ R dec hdec hcorr μ hD hμ
    have hC := charStar_pos_of_exactDomain SupA hS hSc hμ hD
    exact ⟨fun c₀ hc₀ => lower_bound_multi_answer_trunc_rand SupA hSc le_rfl zero_lt_one hμ hC
        ν R dec hdec (exactDomain SupA)
        (fun a w _ _ hη =>
          alt_dense_exactDomain SupA hcov a (hSc a) le_rfl zero_lt_one w μ hη) hcorr hc₀,
      fun hB => ast_lower_main_exact_rand SupA hSc hcov hμ hC ν R dec hdec hcorr hB⟩
  · obtain ⟨S, dec, h1, h2, h3⟩ := ast_main_exact SupA hS hSc hcov
    refine ⟨S, dec, ?_, ?_, ?_⟩
    · intro δ hδ lam hlam
      rw [rprobInf_const]
      exact h1 δ hδ lam hlam
    · intro δ hδ lam hD hlam
      rw [rprobInf_const]
      exact h2 δ hδ lam hD hlam
    · intro μ hD hμ
      simp_rw [rexpTime_const, rexpTimeInf_const]
      exact h3 μ hD hμ

end Main

end Rand

end JointRootCert
