/-
Randomised adaptive Gaussian samplers: the model, the stopped change of measure, and the
Gaussian lower bounds for randomised procedures.

Manuscript results covered (all for procedures with internal randomisation):

* the Gaussian analogue of `lem:active-com` (stopped change of measure):
  `rgauss_transport_finite`, `rgauss_transport`, `rgauss_stopped_transport`.
* `thm:v34-converse` "Unknown-variance nuisance-KL lower bound for one correct answer":
  `rv34_converse`.
* `thm:v34-converse-main` "Matching unknown-variance converse with a unique correct action":
  `rv34_converse_main`.
* `thm:bay-main-optimal` "Correlated Gaussian information limit", lower bound
  `eq:bay-main-optimal`: `rgauss_info_lower_bound`.

Model.  A randomised Gaussian sampler (`RGSampler`) is a deterministic sampler
`GaussStopped.GSampler` for each value of a seed `s`, drawn once from a probability measure `ν`
on a measurable space, independently of the observation noise; the next query, the stopping
decision and the answer (`RGDecision`) may depend on the seed and on the observed history,
jointly measurably.  Probabilities and expectations at horizon `n` are the `ν`-averages of those
of the deterministic samplers (`rlaw`, `rprobAns`, `rexpCnt`, `rexpTime`, built from
`GaussStopped.law`, `GaussStopped.expCnt`, `GaussStopped.expTime`), and the expected stopping
time `rexpTau` in `[0, ∞]` is the supremum over horizons, equal to the `ν`-average of
`GaussStopped.expTau` (`rexpTau_eq_lintegral`).  A deterministic sampler is the constant family
(`RGSampler.const`).
-/
import JointRootCert.RandomisedCore
import JointRootCert.GaussianStopped

namespace JointRootCert

namespace RandG

open MeasureTheory ProbabilityTheory Finset Filter Topology GaussStopped
open _root_.JointRootCert.Rand
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

/-! ### The model -/

/-- A **randomised adaptive Gaussian sampler**: for every seed a deterministic sampler, with
the next query and the stopping decision jointly measurable in the seed and the history. -/
structure RGSampler (X : Type*) [MeasurableSpace X] (Sd : Type*) [MeasurableSpace Sd] where
  /-- the deterministic sampler run when the seed is `s` -/
  run : Sd → GSampler X
  meas_next : ∀ k : ℕ, Measurable fun p : Sd × (Fin k → ℝ) => (run p.1).next (List.ofFn p.2)
  meas_stop : ∀ k : ℕ, Measurable fun p : Sd × (Fin k → ℝ) => (run p.1).stop (List.ofFn p.2)

/-- A decision rule that may depend on the seed. -/
structure RGDecision (A : Type*) [MeasurableSpace A] (Sd : Type*) [MeasurableSpace Sd] where
  /-- the decision rule used when the seed is `s` -/
  run : Sd → GDecision A
  meas_dec : ∀ k : ℕ, Measurable fun p : Sd × (Fin k → ℝ) => (run p.1).dec (List.ofFn p.2)

variable {X : Type*} [MeasurableSpace X] {Sd : Type*} [MeasurableSpace Sd]

/-- A deterministic sampler, as a randomised sampler that ignores its seed. -/
def RGSampler.const (S : GSampler X) : RGSampler X Sd where
  run := fun _ => S
  meas_next := fun k => (S.meas_next k).comp measurable_snd
  meas_stop := fun k => (S.meas_stop k).comp measurable_snd

/-- A deterministic decision rule, as one that ignores the seed. -/
def RGDecision.const {A : Type*} [MeasurableSpace A] (D : GDecision A) : RGDecision A Sd where
  run := fun _ => D
  meas_dec := fun k => (D.meas_dec k).comp measurable_snd

/-! ### Joint measurability in the seed and the transcript -/

lemma measurable_jtail (n : ℕ) :
    Measurable fun p : Sd × (Fin (n + 1) → ℝ) => (p.1, (Fin.tail p.2 : Fin n → ℝ)) :=
  measurable_fst.prodMk ((measurable_tail n).comp measurable_snd)

lemma measurableSet_jhalt (R : RGSampler X Sd) :
    ∀ n, MeasurableSet {p : Sd × (Fin n → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true}
  | 0 => by
    have : {p : Sd × (Fin 0 → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true} =
        (fun p : Sd × (Fin 0 → ℝ) => (R.run p.1).stop (List.ofFn p.2)) ⁻¹' {true} := by
      ext p
      simp [halted]
    rw [this]
    exact R.meas_stop 0 (measurableSet_singleton true)
  | n + 1 => by
    have : {p : Sd × (Fin (n + 1) → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true} =
        (fun p : Sd × (Fin (n + 1) → ℝ) => (p.1, (Fin.tail p.2 : Fin n → ℝ))) ⁻¹'
            {p : Sd × (Fin n → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true} ∪
          (fun p : Sd × (Fin (n + 1) → ℝ) => (R.run p.1).stop (List.ofFn p.2)) ⁻¹' {true} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage, Set.mem_singleton_iff]
      rw [ofFn_eq n p.2, halted, Bool.or_eq_true, ← ofFn_eq n p.2]
    rw [this]
    exact ((measurable_jtail n) (measurableSet_jhalt R n)).union
      (R.meas_stop (n + 1) (measurableSet_singleton true))

variable [MeasurableSingletonClass X] [Fintype X]

lemma measurableSet_jqset (R : RGSampler X Sd) (n : ℕ) (x : X) :
    MeasurableSet {p : Sd × (Fin n → ℝ) |
      halted (R.run p.1) (List.ofFn p.2) = false ∧ (R.run p.1).next (List.ofFn p.2) = x} := by
  have : {p : Sd × (Fin n → ℝ) |
      halted (R.run p.1) (List.ofFn p.2) = false ∧ (R.run p.1).next (List.ofFn p.2) = x} =
      {p : Sd × (Fin n → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true}ᶜ ∩
        (fun p : Sd × (Fin n → ℝ) => (R.run p.1).next (List.ofFn p.2)) ⁻¹' {x} := by
    ext p
    simp
  rw [this]
  exact (measurableSet_jhalt R n).compl.inter (R.meas_next n (measurableSet_singleton x))

lemma measurable_jcnt (R : RGSampler X Sd) (x : X) :
    ∀ n, Measurable fun p : Sd × (Fin n → ℝ) => (cnt (R.run p.1) x (List.ofFn p.2) : ℝ)
  | 0 => by simp [cnt]
  | n + 1 => by
    have : (fun p : Sd × (Fin (n + 1) → ℝ) => (cnt (R.run p.1) x (List.ofFn p.2) : ℝ)) =
        fun p => (cnt (R.run p.1) x (List.ofFn (Fin.tail p.2)) : ℝ)
          + ({q : Sd × (Fin n → ℝ) | halted (R.run q.1) (List.ofFn q.2) = false ∧
              (R.run q.1).next (List.ofFn q.2) = x}).indicator (fun _ => (1 : ℝ))
            (p.1, (Fin.tail p.2 : Fin n → ℝ)) := by
      funext p
      rw [cnt_ofFn_succ]
      rfl
    rw [this]
    exact ((measurable_jcnt R x n).comp (measurable_jtail n)).add
      ((measurable_const.indicator (measurableSet_jqset R n x)).comp (measurable_jtail n))

lemma measurable_jtime (R : RGSampler X Sd) (n : ℕ) :
    Measurable fun p : Sd × (Fin n → ℝ) => (time (R.run p.1) (List.ofFn p.2) : ℝ) := by
  simp_rw [time_eq_sum]
  exact Finset.measurable_sum _ fun x _ => measurable_jcnt R x n

/-- Joint measurability of the observation map. -/
lemma measurable_jobs (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ) :
    Measurable fun q : (Sd × (Fin n → ℝ)) × ℝ =>
      obs (R.run q.1.1) μ v (List.ofFn q.1.2) q.2 := by
  unfold obs
  refine Measurable.ite (measurable_fst (measurableSet_jhalt R n)) measurable_snd ?_
  exact (measurable_from_prod_countable_left
    (f := fun q : ℝ × X => μ q.2 + Real.sqrt (v q.2) * q.1) (fun x => by fun_prop)).comp
    (measurable_snd.prodMk ((R.meas_next n).comp measurable_fst))

/-- Joint measurability of the transcript in the seed and the noise. -/
lemma measurable_jhist (R : RGSampler X Sd) (μ v : X → ℝ) :
    ∀ n, Measurable fun p : Sd × (Fin n → ℝ) => hist (R.run p.1) μ v n p.2
  | 0 => measurable_const
  | n + 1 => by
    have ih : Measurable fun p : Sd × (Fin (n + 1) → ℝ) =>
        hist (R.run p.1) μ v n (Fin.tail p.2) :=
      (measurable_jhist R μ v n).comp (measurable_jtail n)
    have hO : Measurable fun p : Sd × (Fin (n + 1) → ℝ) =>
        obs (R.run p.1) μ v (List.ofFn (hist (R.run p.1) μ v n (Fin.tail p.2))) (p.2 0) :=
      (measurable_jobs R μ v n).comp
        ((measurable_fst.prodMk ih).prodMk ((measurable_pi_apply 0).comp measurable_snd))
    exact (measurable_cons n).comp (ih.prodMk hO)

/-- The law of the transcript of a seed-dependent event is measurable in the seed. -/
lemma measurable_law_real (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ)
    {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) :
    Measurable fun s => (law (R.run s) μ v n).real {y | (s, y) ∈ E} := by
  have hE' : MeasurableSet
      ((fun p : Sd × (Fin n → ℝ) => (p.1, hist (R.run p.1) μ v n p.2)) ⁻¹' E) :=
    (measurable_fst.prodMk (measurable_jhist R μ v n)) hE
  have h := (measurable_measure_prodMk_left
    (ν := Measure.pi fun _ : Fin n => gaussianReal 0 1) hE').ennreal_toReal
  have e : (fun s => (law (R.run s) μ v n).real {y | (s, y) ∈ E}) = fun s =>
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1) (Prod.mk s ⁻¹'
        ((fun p : Sd × (Fin n → ℝ) => (p.1, hist (R.run p.1) μ v n p.2)) ⁻¹' E))).toReal := by
    funext s
    have hEs : MeasurableSet {y : Fin n → ℝ | (s, y) ∈ E} := measurable_prodMk_left hE
    rw [← law_eq_map_hist (R.run s) μ v n,
      map_measureReal_apply (measurable_hist (R.run s) μ v n) hEs]
    rfl
  rw [e]
  exact h

/-- Expectations of jointly measurable functions of the transcript are measurable in the
seed. -/
lemma measurable_law_integral (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ)
    {f : Sd × (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    Measurable fun s => ∫ y, f (s, y) ∂(law (R.run s) μ v n) := by
  have hg : Measurable fun p : Sd × (Fin n → ℝ) => f (p.1, hist (R.run p.1) μ v n p.2) :=
    hf.comp (measurable_fst.prodMk (measurable_jhist R μ v n))
  have h := (hg.stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi fun _ : Fin n => gaussianReal 0 1)).measurable
  have e : (fun s => ∫ y, f (s, y) ∂(law (R.run s) μ v n)) = fun s =>
      ∫ ω, f (s, hist (R.run s) μ v n ω) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    funext s
    rw [← law_eq_map_hist (R.run s) μ v n]
    exact integral_map (measurable_hist (R.run s) μ v n).aemeasurable
      (hf.comp measurable_prodMk_left).aestronglyMeasurable
  rw [e]
  exact h

lemma measurable_expCnt (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ) (x : X) :
    Measurable fun s => expCnt (R.run s) μ v n x :=
  measurable_law_integral R μ v n (measurable_jcnt R x n)

lemma measurable_expTime (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ) :
    Measurable fun s => GaussStopped.expTime (R.run s) μ v n :=
  measurable_law_integral R μ v n (measurable_jtime R n)

/-- `E[τ ∧ n] ≤ n`. -/
lemma expTime_le (S : GSampler X) (μ v : X → ℝ) (n : ℕ) : GaussStopped.expTime S μ v n ≤ n := by
  have h := integral_mono (integrable_time S μ v n) (integrable_const (n : ℝ)) fun y => by
    have := time_le_length S (List.ofFn y)
    rw [List.length_ofFn] at this
    exact_mod_cast this
  simpa [GaussStopped.expTime] using h

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

lemma measurableSet_jdecAt (R : RGSampler X Sd) (D : RGDecision A Sd) (a : A) :
    ∀ n, MeasurableSet {p : Sd × (Fin n → ℝ) |
      decAt (R.run p.1) (D.run p.1) (List.ofFn p.2) = a}
  | 0 => by
    have : {p : Sd × (Fin 0 → ℝ) | decAt (R.run p.1) (D.run p.1) (List.ofFn p.2) = a} =
        (fun p : Sd × (Fin 0 → ℝ) => (D.run p.1).dec (List.ofFn p.2)) ⁻¹' {a} := by
      ext p
      simp [decAt]
    rw [this]
    exact D.meas_dec 0 (measurableSet_singleton a)
  | n + 1 => by
    have : {p : Sd × (Fin (n + 1) → ℝ) |
        decAt (R.run p.1) (D.run p.1) (List.ofFn p.2) = a} =
        ((fun p : Sd × (Fin (n + 1) → ℝ) => (p.1, (Fin.tail p.2 : Fin n → ℝ))) ⁻¹'
            {p : Sd × (Fin n → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true} ∩
          (fun p : Sd × (Fin (n + 1) → ℝ) => (p.1, (Fin.tail p.2 : Fin n → ℝ))) ⁻¹'
            {p : Sd × (Fin n → ℝ) | decAt (R.run p.1) (D.run p.1) (List.ofFn p.2) = a}) ∪
        (((fun p : Sd × (Fin (n + 1) → ℝ) => (p.1, (Fin.tail p.2 : Fin n → ℝ))) ⁻¹'
            {p : Sd × (Fin n → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true})ᶜ ∩
          (fun p : Sd × (Fin (n + 1) → ℝ) => (D.run p.1).dec (List.ofFn p.2)) ⁻¹' {a}) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_compl_iff, Set.mem_singleton_iff]
      conv_lhs => rw [ofFn_eq n p.2, decAt, ← ofFn_eq n p.2]
      cases hh : halted (R.run p.1) (List.ofFn (Fin.tail p.2)) <;> simp
    rw [this]
    have h1 := (measurable_jtail n) (measurableSet_jhalt R n)
    exact (h1.inter ((measurable_jtail n) (measurableSet_jdecAt R D a n))).union
      (h1.compl.inter (D.meas_dec (n + 1) (measurableSet_singleton a)))

/-- The event "halted by `n` with answer `a`", jointly in the seed and the transcript. -/
lemma measurableSet_jans (R : RGSampler X Sd) (D : RGDecision A Sd) (a : A) (n : ℕ) :
    MeasurableSet {p : Sd × (Fin n → ℝ) | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n} :=
  (measurableSet_jhalt R n).inter (measurableSet_jdecAt R D a n)

lemma measurableSet_jnans (R : RGSampler X Sd) (D : RGDecision A Sd) (a : A) (n : ℕ) :
    MeasurableSet {p : Sd × (Fin n → ℝ) | p.2 ∈ nansSet (R.run p.1) (D.run p.1) a n} :=
  (measurableSet_jhalt R n).inter (measurableSet_jdecAt R D a n).compl

/-! ### Seed-averaged probabilities and expectations -/

section Averages

variable (ν : Measure Sd)

/-- Probability, for the randomised sampler at horizon `n`, of a seed-dependent event of the
transcript: the seed-average of `GaussStopped.law`. -/
def rlaw (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ) (E : Set (Sd × (Fin n → ℝ))) : ℝ :=
  ∫ s, (law (R.run s) μ v n).real {y | (s, y) ∈ E} ∂ν

/-- Probability that the randomised procedure has halted by `n` with answer `a`. -/
def rprobAns (R : RGSampler X Sd) (D : RGDecision A Sd) (a : A) (μ v : X → ℝ) (n : ℕ) : ℝ :=
  ∫ s, (law (R.run s) μ v n).real (ansSet (R.run s) (D.run s) a n) ∂ν

/-- Expected number of queries of type `x` before `τ ∧ n`, for the randomised sampler. -/
def rexpCnt (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∫ s, expCnt (R.run s) μ v n x ∂ν

/-- `E[τ ∧ n]` for the randomised sampler. -/
def rexpTime (R : RGSampler X Sd) (μ v : X → ℝ) (n : ℕ) : ℝ :=
  ∫ s, GaussStopped.expTime (R.run s) μ v n ∂ν

/-- Expected stopping time of the randomised sampler, `sup_n E[τ ∧ n]`, in `[0, ∞]`. -/
def rexpTau (R : RGSampler X Sd) (μ v : X → ℝ) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (rexpTime ν R μ v n)

lemma rprobAns_eq_rlaw (R : RGSampler X Sd) (D : RGDecision A Sd) (a : A) (μ v : X → ℝ)
    (n : ℕ) : rprobAns ν R D a μ v n
      = rlaw ν R μ v n {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n} := rfl

variable [IsProbabilityMeasure ν] (R : RGSampler X Sd) (μ v : X → ℝ)

lemma integrable_law_real (n : ℕ) {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) :
    Integrable (fun s => (law (R.run s) μ v n).real {y | (s, y) ∈ E}) ν :=
  Integrable.of_mem_Icc 0 1 (measurable_law_real R μ v n hE).aemeasurable
    (ae_of_all _ fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)

lemma integrable_expTime (n : ℕ) :
    Integrable (fun s => GaussStopped.expTime (R.run s) μ v n) ν :=
  Integrable.of_mem_Icc 0 n (measurable_expTime R μ v n).aemeasurable
    (ae_of_all _ fun s => ⟨expTime_nonneg (R.run s) μ v n, expTime_le (R.run s) μ v n⟩)

lemma integrable_expCnt (n : ℕ) (x : X) : Integrable (fun s => expCnt (R.run s) μ v n x) ν :=
  Integrable.of_mem_Icc 0 n (measurable_expCnt R μ v n x).aemeasurable
    (ae_of_all _ fun s => ⟨expCnt_nonneg (R.run s) μ v n x,
      (expCnt_le_expTime (R.run s) μ v n x).trans (expTime_le (R.run s) μ v n)⟩)

lemma rlaw_nonneg (n : ℕ) (E : Set (Sd × (Fin n → ℝ))) : 0 ≤ rlaw ν R μ v n E :=
  integral_nonneg fun _ => measureReal_nonneg

lemma rlaw_le_one (n : ℕ) {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) :
    rlaw ν R μ v n E ≤ 1 := by
  have := integral_mono (integrable_law_real ν R μ v n hE) (integrable_const (1 : ℝ))
    fun _ => measureReal_le_one
  simpa [rlaw] using this

lemma rlaw_mono (n : ℕ) {E F : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (h : E ⊆ F) : rlaw ν R μ v n E ≤ rlaw ν R μ v n F :=
  integral_mono (integrable_law_real ν R μ v n hE) (integrable_law_real ν R μ v n hF)
    fun _ => measureReal_mono fun _ hy => h hy

lemma rlaw_compl (n : ℕ) {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) :
    rlaw ν R μ v n Eᶜ = 1 - rlaw ν R μ v n E := by
  have e : ∀ s, (law (R.run s) μ v n).real {y | (s, y) ∈ Eᶜ}
      = 1 - (law (R.run s) μ v n).real {y | (s, y) ∈ E} := fun s =>
    probReal_compl_eq_one_sub (measurable_prodMk_left hE)
  unfold rlaw
  rw [integral_congr_ae (ae_of_all _ e),
    integral_sub (integrable_const (1 : ℝ)) (integrable_law_real ν R μ v n hE)]
  simp

lemma rexpTime_nonneg (n : ℕ) : 0 ≤ rexpTime ν R μ v n :=
  integral_nonneg fun s => expTime_nonneg (R.run s) μ v n

lemma rexpCnt_nonneg (n : ℕ) (x : X) : 0 ≤ rexpCnt ν R μ v n x :=
  integral_nonneg fun s => expCnt_nonneg (R.run s) μ v n x

lemma sum_rexpCnt (n : ℕ) : ∑ x, rexpCnt ν R μ v n x = rexpTime ν R μ v n := by
  unfold rexpCnt rexpTime
  rw [← integral_finsetSum _ fun x _ => integrable_expCnt ν R μ v n x]
  exact integral_congr_ae (ae_of_all _ fun s => sum_expCnt (R.run s) μ v n)

lemma rexpCnt_le_rexpTime (n : ℕ) (x : X) : rexpCnt ν R μ v n x ≤ rexpTime ν R μ v n :=
  integral_mono (integrable_expCnt ν R μ v n x) (integrable_expTime ν R μ v n)
    fun s => expCnt_le_expTime (R.run s) μ v n x

lemma rexpCnt_mono (x : X) : Monotone fun n => rexpCnt ν R μ v n x := fun m n hmn =>
  integral_mono (integrable_expCnt ν R μ v m x) (integrable_expCnt ν R μ v n x)
    fun s => expCnt_mono (R.run s) μ v x hmn

lemma rexpTime_le_of_ne_top (h : rexpTau ν R μ v ≠ ⊤) (n : ℕ) :
    rexpTime ν R μ v n ≤ (rexpTau ν R μ v).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal h).1
    (le_iSup (fun n => ENNReal.ofReal (rexpTime ν R μ v n)) n)

/-- The expected stopping time of the randomised sampler is the seed-average of the expected
stopping times `GaussStopped.expTau` of the deterministic samplers. -/
theorem rexpTau_eq_lintegral : rexpTau ν R μ v = ∫⁻ s, expTau (R.run s) μ v ∂ν := by
  unfold rexpTau expTau
  rw [lintegral_iSup (fun n => (measurable_expTime R μ v n).ennreal_ofReal)
    (fun i j hij s => ENNReal.ofReal_le_ofReal (GaussStopped.expTime_mono (R.run s) μ v hij))]
  refine iSup_congr fun n => ?_
  unfold rexpTime
  exact ofReal_integral_eq_lintegral_ofReal (integrable_expTime ν R μ v n)
    (ae_of_all _ fun s => expTime_nonneg (R.run s) μ v n)

end Averages

/-- For a deterministic procedure the randomised quantities are the deterministic ones. -/
lemma rprobAns_const (ν : Measure Sd) [IsProbabilityMeasure ν] (S : GSampler X)
    (D : GDecision A) (a : A) (μ v : X → ℝ) (n : ℕ) :
    rprobAns ν (RGSampler.const S) (RGDecision.const D) a μ v n
      = (law S μ v n).real (ansSet S D a n) := by
  simp [rprobAns, RGSampler.const, RGDecision.const]

lemma rexpTau_const (ν : Measure Sd) [IsProbabilityMeasure ν] (S : GSampler X) (μ v : X → ℝ) :
    rexpTau ν (RGSampler.const S) μ v = expTau S μ v := by
  simp [rexpTau, rexpTime, expTau, RGSampler.const]

/-! ### The stopped Gaussian change of measure for randomised samplers -/

section Transport

variable (ν : Measure Sd) [IsProbabilityMeasure ν] (R : RGSampler X Sd) {μ v μ' v' : X → ℝ}

lemma rlaw_pos_of_pos (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) (n : ℕ)
    {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) (h : 0 < rlaw ν R μ v n E) :
    0 < rlaw ν R μ' v' n E :=
  integral_pos_of_imp ν (measurable_law_real R μ v n hE) (measurable_law_real R μ' v' n hE)
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (ae_of_all _ fun s => measureReal_pos_of_pos (R.run s) hv hv' n) h

lemma integral_expCnt_gaussKL (n : ℕ) :
    ∫ s, ∑ x, expCnt (R.run s) μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) ∂ν
      = ∑ x, rexpCnt ν R μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  rw [integral_finsetSum _ fun x _ => (integrable_expCnt ν R μ v n x).mul_const _]
  exact sum_congr rfl fun x _ => integral_mul_const _ _

/-- Two-point Donsker--Varadhan bound for the transcript of a randomised sampler at a finite
horizon: the seed-wise bound averaged over the seed by concavity of the logarithm. -/
lemma two_point_rgauss (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) (n : ℕ)
    {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) (a b : ℝ) :
    a * rlaw ν R μ v n E + b * (1 - rlaw ν R μ v n E)
        - Real.log (Real.exp a * rlaw ν R μ' v' n E + Real.exp b * (1 - rlaw ν R μ' v' n E))
      ≤ ∑ x, rexpCnt ν R μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hK : Integrable
      (fun s => ∑ x, expCnt (R.run s) μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x)) ν :=
    integrable_finsetSum _ fun x _ => (integrable_expCnt ν R μ v n x).mul_const _
  have h := two_point_integral ν (measurable_law_real R μ v n hE)
    (measurable_law_real R μ' v' n hE)
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩) hK a b (fun s => by
      have hae := llr_ae_eq (R.run s) (μ := μ) (μ' := μ') hv hv' n
      have hint : Integrable (llr (law (R.run s) μ v n) (law (R.run s) μ' v' n))
          (law (R.run s) μ v n) :=
        (integrable_congr hae).2 (integrable_llr (R.run s) hv hv' n)
      have h := two_point_dv _ _ (law_absolutelyContinuous (R.run s) hv hv' n) hint
        (measurable_prodMk_left hE : MeasurableSet {y | (s, y) ∈ E}) a b
      rw [integral_congr_ae hae, wald_identity (R.run s) hv hv' n] at h
      exact h)
  rw [integral_expCnt_gaussKL] at h
  exact h

/-- **Transportation inequality for a randomised Gaussian sampler at a finite horizon.**  For
every jointly measurable event `E` of the seed and the transcript at horizon `n`,
`kl(P_{μ,v}(E), P_{μ',v'}(E)) ≤ ∑ₓ E_{μ,v}[Nₓ(τ ∧ n)] · KL(N(μₓ, vₓ) ‖ N(μ'ₓ, v'ₓ))`,
probabilities and expected counts averaged over the seed.  From the deterministic
`gauss_transport_finite` by joint convexity of the binary divergence. -/
theorem rgauss_transport_finite (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) (n : ℕ)
    {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) :
    bkl (rlaw ν R μ v n E) (rlaw ν R μ' v' n E) ≤
      ∑ x, rexpCnt ν R μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hK : Integrable
      (fun s => ∑ x, expCnt (R.run s) μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x)) ν :=
    integrable_finsetSum _ fun x _ => (integrable_expCnt ν R μ v n x).mul_const _
  have h := bkl_integral_le_of_le ν (measurable_law_real R μ v n hE)
    (measurable_law_real R μ' v' n hE)
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (fun s => measureReal_pos_of_pos (R.run s) hv hv' n)
    (fun s hs => by
      have hEs : MeasurableSet {y : Fin n → ℝ | (s, y) ∈ E} := measurable_prodMk_left hE
      have h1 : 0 < (law (R.run s) μ v n).real {y | (s, y) ∈ E}ᶜ := by
        rw [probReal_compl_eq_one_sub hEs]
        linarith
      have h2 := measureReal_pos_of_pos (R.run s) (μ' := μ') hv hv' n h1
      rw [probReal_compl_eq_one_sub hEs] at h2
      linarith) hK
    (fun s => gauss_transport_finite (R.run s) hv hv' n (measurable_prodMk_left hE))
  rw [integral_expCnt_gaussKL] at h
  exact h

/-- If a seed-dependent event has probability at least `p ≥ δ` under the first parameter and at
most `δ < 1` under the second, the transported information is at least `kl(p, δ)`. -/
lemma rbkl_le_of_event (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) (n : ℕ)
    {E : Set (Sd × (Fin n → ℝ))} (hE : MeasurableSet E) {p δ : ℝ}
    (hδ0 : 0 < δ) (hδp : δ ≤ p) (hp1 : p < 1) (hp : p ≤ rlaw ν R μ v n E)
    (hq : rlaw ν R μ' v' n E ≤ δ) :
    bkl p δ ≤ ∑ x, rexpCnt ν R μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hP1 : rlaw ν R μ v n E ≤ 1 := rlaw_le_one ν R μ v n hE
  have hQ0 : 0 < rlaw ν R μ' v' n E := rlaw_pos_of_pos ν R hv hv' n hE (by linarith)
  have h1 : bkl p δ ≤ bkl (rlaw ν R μ v n E) δ := bkl_mono_left hδ0 hδp hp1 hp hP1
  have h2 : bkl (rlaw ν R μ v n E) δ ≤ bkl (rlaw ν R μ v n E) (rlaw ν R μ' v' n E) :=
    bkl_mono_right (by linarith) hP1 hδ0 (by linarith) hQ0 (by linarith)
      (mul_nonneg (sub_nonneg.2 hq) (by linarith))
  exact (h1.trans h2).trans (rgauss_transport_finite ν R hv hv' n hE)

/-- **Transportation inequality for an unbounded stopping time, randomised sampler** (the
randomised form of `gauss_transport`).  `E n` is the horizon-`n` version of an event of the
stopped run.  If its probability under `(μ, v)` approaches at least `1 - δ` along the horizons,
its probability under `(μ', v')` is at most `δ` at every horizon, and `N x` bounds the expected
counts uniformly in `n`, then `kl(1 - δ, δ) ≤ ∑ₓ Nₓ · KL(N(μₓ, vₓ) ‖ N(μ'ₓ, v'ₓ))`. -/
theorem rgauss_transport (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x)
    (E : ∀ n, Set (Sd × (Fin n → ℝ))) (hE : ∀ n, MeasurableSet (E n))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) {N : X → ℝ}
    (hP : ∀ η > 0, ∃ n, 1 - δ - η ≤ rlaw ν R μ v n (E n))
    (hQ : ∀ n, rlaw ν R μ' v' n (E n) ≤ δ)
    (hN : ∀ n x, rexpCnt ν R μ v n x ≤ N x) :
    bkl (1 - δ) δ ≤ ∑ x, N x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  refine bkl_le_of_forall_small hδ0 hδ fun η hη0 hη1 => ?_
  obtain ⟨n, hn⟩ := hP η hη0
  refine (rbkl_le_of_event ν R hv hv' n (hE n) hδ0 (by linarith) (by linarith) hn
    (hQ n)).trans ?_
  exact sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_right (hN n x) (gaussKL_nonneg (hv x) (hv' x))

end Transport

/-! ### The unbounded run -/

section Unbounded

variable (ν : Measure Sd) [IsProbabilityMeasure ν] (R : RGSampler X Sd) (D : RGDecision A Sd)
  {μ v μ' v' : X → ℝ}

lemma rprobAns_mono (a : A) (μ v : X → ℝ) : Monotone fun n => rprobAns ν R D a μ v n := by
  intro m n hmn
  have hm : Integrable
      (fun s => (law (R.run s) μ v m).real (ansSet (R.run s) (D.run s) a m)) ν :=
    integrable_law_real ν R μ v m (measurableSet_jans R D a m)
  have hn : Integrable
      (fun s => (law (R.run s) μ v n).real (ansSet (R.run s) (D.run s) a n)) ν :=
    integrable_law_real ν R μ v n (measurableSet_jans R D a n)
  exact integral_mono hm hn fun s => law_ansSet_mono (R.run s) (D.run s) a μ v hmn

/-- Markov's inequality `n · P(τ > n) ≤ E[τ ∧ n]` for the randomised sampler. -/
lemma rnot_halted_mul_le (μ v : X → ℝ) (n : ℕ) :
    (n : ℝ) * (1 - rlaw ν R μ v n {p | halted (R.run p.1) (List.ofFn p.2) = true})
      ≤ rexpTime ν R μ v n := by
  have hH := integrable_law_real ν R μ v n (measurableSet_jhalt R n)
  have h1 : Integrable (fun s => 1 - (law (R.run s) μ v n).real
      {y | (s, y) ∈ {p : Sd × (Fin n → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true}}) ν :=
    (integrable_const (1 : ℝ)).sub hH
  have hsub : Integrable (fun s => (n : ℝ) * (1 - (law (R.run s) μ v n).real
      {y | (s, y) ∈ {p : Sd × (Fin n → ℝ) | halted (R.run p.1) (List.ofFn p.2) = true}})) ν :=
    h1.const_mul _
  have h := integral_mono hsub (integrable_expTime ν R μ v n) fun s => by
    have h1 := not_halted_mul_le (R.run s) μ v n
    rw [probReal_compl_eq_one_sub (measurableSet_hset (R.run s) n)] at h1
    exact h1
  rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hH] at h
  simpa [rlaw, rexpTime] using h

/-- **Stopped Gaussian change of measure for an unbounded stopping time, randomised sampler**
(Gaussian analogue of `lem:active-com`).  For a randomised sampler with finite expected stopping
time under `(μ, v)` (`hB`: `E_{μ,v}[τ ∧ n] ≤ B` for all `n`) and the event "halts and returns
`a`",
`kl(P_{μ,v}(E), P_{μ',v'}(E)) ≤ ∑ₓ E_{μ,v}[Nₓ(τ)] · KL(N(μₓ, vₓ) ‖ N(μ'ₓ, v'ₓ))`,
where probabilities and expected counts are averaged over the seed and those of the unbounded
run are the suprema (limits) of their horizon-`n` values. -/
theorem rgauss_stopped_transport (a : A) (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) {B : ℝ}
    (hB : ∀ n, rexpTime ν R μ v n ≤ B) :
    bkl (⨆ n, rprobAns ν R D a μ v n) (⨆ n, rprobAns ν R D a μ' v' n) ≤
      ∑ x, (⨆ n, rexpCnt ν R μ v n x) * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hmono := fun m w : X → ℝ => rprobAns_mono ν R D a m w
  simp only [rprobAns_eq_rlaw] at hmono ⊢
  have bddp : ∀ m w : X → ℝ, BddAbove (Set.range fun n =>
      rlaw ν R m w n {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n}) := fun m w =>
    ⟨1, by rintro _ ⟨n, rfl⟩; exact rlaw_le_one ν R m w n (measurableSet_jans R D a n)⟩
  have bddc : ∀ x, BddAbove (Set.range fun n => rexpCnt ν R μ v n x) := fun x =>
    ⟨B, by rintro _ ⟨n, rfl⟩; exact (rexpCnt_le_rexpTime ν R μ v n x).trans (hB n)⟩
  have hp := tendsto_atTop_ciSup (hmono μ v) (bddp μ v)
  have hq := tendsto_atTop_ciSup (hmono μ' v') (bddp μ' v')
  refine Stopped.bkl_le_of_tendsto hp hq
    (le_ciSup_of_le (bddp μ v) 0 (rlaw_nonneg ν R μ v 0 _))
    (ciSup_le fun n => rlaw_le_one ν R μ v n (measurableSet_jans R D a n))
    (le_ciSup_of_le (bddp μ' v') 0 (rlaw_nonneg ν R μ' v' 0 _))
    (ciSup_le fun n => rlaw_le_one ν R μ' v' n (measurableSet_jans R D a n))
    ?_ ?_ fun n a' b' => ?_
  · intro hP
    obtain ⟨n, hn⟩ : ∃ n, 0 < rlaw ν R μ v n
        {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n} := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have := ciSup_le hcon
      linarith
    exact (rlaw_pos_of_pos ν R hv hv' n (measurableSet_jans R D a n) hn).trans_le
      (le_ciSup (bddp μ' v') n)
  · intro hP
    obtain ⟨n, hn⟩ : ∃ n, 0 < rlaw ν R μ v n
        {p | p.2 ∈ nansSet (R.run p.1) (D.run p.1) a n} := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have hd : 0 < 1 - ⨆ n, rlaw ν R μ v n
          {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n} := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (B / (1 - ⨆ n, rlaw ν R μ v n
        {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n}))
      have h1 : B < n * (1 - ⨆ n, rlaw ν R μ v n
          {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n}) := by
        rwa [div_lt_iff₀ hd] at hn
      have h2 := rnot_halted_mul_le ν R μ v n
      have h3 : rlaw ν R μ v n {p | halted (R.run p.1) (List.ofFn p.2) = true} ≤
          rlaw ν R μ v n {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n}
            + rlaw ν R μ v n {p | p.2 ∈ nansSet (R.run p.1) (D.run p.1) a n} := by
        have hA := integrable_law_real ν R μ v n (measurableSet_jans R D a n)
        have hN := integrable_law_real ν R μ v n (measurableSet_jnans R D a n)
        have hAN : Integrable (fun s =>
            (law (R.run s) μ v n).real
              {y | (s, y) ∈ {p : Sd × (Fin n → ℝ) | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n}}
            + (law (R.run s) μ v n).real
              {y | (s, y) ∈ {p : Sd × (Fin n → ℝ) |
                p.2 ∈ nansSet (R.run p.1) (D.run p.1) a n}}) ν := hA.add hN
        have h := integral_mono (integrable_law_real ν R μ v n (measurableSet_jhalt R n)) hAN
          fun s => by
            refine (measureReal_mono (fun y hy => ?_)).trans (measureReal_union_le _ _)
            by_cases hd : decAt (R.run s) (D.run s) (List.ofFn y) = a
            · exact Or.inl ⟨hy, hd⟩
            · exact Or.inr ⟨hy, hd⟩
        rw [integral_add hA hN] at h
        exact h
      have h5 := le_ciSup (bddp μ v) n
      have h6 := hcon n
      have h7 : (1 - ⨆ n, rlaw ν R μ v n {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n}) ≤
          1 - rlaw ν R μ v n {p | halted (R.run p.1) (List.ofFn p.2) = true} := by
        have h5' : rlaw ν R μ v n {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n} ≤
            ⨆ n, rlaw ν R μ v n {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a n} := h5
        linarith
      have h8 := mul_le_mul_of_nonneg_left h7 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith [hB n]
    have hq' := rlaw_pos_of_pos ν R (μ' := μ') hv hv' n (measurableSet_jnans R D a n) hn
    have hle : ∀ m, rlaw ν R μ' v' m {p | p.2 ∈ ansSet (R.run p.1) (D.run p.1) a m} ≤
        1 - rlaw ν R μ' v' n {p | p.2 ∈ nansSet (R.run p.1) (D.run p.1) a n} := by
      intro m
      have hN := integrable_law_real ν R μ' v' n (measurableSet_jnans R D a n)
      have hsub : Integrable (fun s => 1 - (law (R.run s) μ' v' n).real
          {y | (s, y) ∈ {p : Sd × (Fin n → ℝ) |
            p.2 ∈ nansSet (R.run p.1) (D.run p.1) a n}}) ν :=
        (integrable_const (1 : ℝ)).sub hN
      have h := integral_mono (integrable_law_real ν R μ' v' m (measurableSet_jans R D a m))
        hsub fun s => by
          have h1 := law_ansSet_mono (R.run s) (D.run s) a μ' v' (le_max_left m n)
          have h2 := law_nansSet_mono (R.run s) (D.run s) a μ' v' (le_max_right m n)
          have hdisj : Disjoint (ansSet (R.run s) (D.run s) a (max m n))
              (nansSet (R.run s) (D.run s) a (max m n)) :=
            Set.disjoint_left.2 fun y h1 h2 => h2.2 h1.2
          have h3 := measureReal_union (μ := law (R.run s) μ' v' (max m n)) hdisj
            (measurableSet_nansSet (R.run s) (D.run s) a (max m n))
          have h4 : (law (R.run s) μ' v' (max m n)).real
              (ansSet (R.run s) (D.run s) a (max m n)
                ∪ nansSet (R.run s) (D.run s) a (max m n)) ≤ 1 := measureReal_le_one
          have h1' : (law (R.run s) μ' v' m).real (ansSet (R.run s) (D.run s) a m) ≤
              (law (R.run s) μ' v' (max m n)).real (ansSet (R.run s) (D.run s) a (max m n)) :=
            h1
          have h2' : (law (R.run s) μ' v' n).real (nansSet (R.run s) (D.run s) a n) ≤
              (law (R.run s) μ' v' (max m n)).real
                (nansSet (R.run s) (D.run s) a (max m n)) := h2
          show (law (R.run s) μ' v' m).real (ansSet (R.run s) (D.run s) a m) ≤
            1 - (law (R.run s) μ' v' n).real (nansSet (R.run s) (D.run s) a n)
          linarith
      rw [integral_sub (integrable_const (1 : ℝ)) hN] at h
      simpa [rlaw] using h
    have := ciSup_le hle
    linarith
  · exact (two_point_rgauss ν R hv hv' n (measurableSet_jans R D a n) a' b').trans
      (sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (le_ciSup (bddc x) n)
        (gaussKL_nonneg (hv x) (hv' x)))

end Unbounded

/-! ### `thm:v34-converse` and `thm:v34-converse-main` for randomised procedures -/

section Converse

variable {U : Type*} {Z : Type*}

/-- **Unknown-variance nuisance-KL lower bound for one correct answer (`thm:v34-converse`,
finite-confidence part), for randomised procedures.**  `R` is a randomised adaptive sampler with
seed law `ν` and decision rule `D`; `(μ, v)` are the true query means and variances; `Hs z` are
the strict invalidating components of the action `astar` and `Hc z` the closed ones.
Hypotheses on the procedure only (probabilities over observations and seed):
* `hcorrect`: under the truth the probability of halting with answer `astar` is at least
  `1 - δ` (as a supremum over horizons);
* `hwrong`: under every strict alternative mean `pred · u` with arbitrary positive variances
  the probability of halting with answer `astar` is at most `δ` at every horizon.
Conclusion: `E_{μ,v}[τ] ≥ kl(1 - δ, δ) / C_{a⋆}^*(μ, v)` in `[0, ∞]`. -/
theorem rv34_converse [TopologicalSpace U] (ν : Measure Sd) [IsProbabilityMeasure ν]
    (R : RGSampler X Sd) (D : RGDecision A Sd) (astar : A)
    (J : Finset Z) (hJ : J.Nonempty) (Hc Hs : Z → Set U) (pred : X → U → ℝ)
    (hpred : ∀ x, Continuous (pred x)) {μ v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hne : ∀ z ∈ J, (Hc z).Nonempty) (hcl : ∀ z ∈ J, Hc z ⊆ closure (Hs z))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (hcorrect : ∀ η > 0, ∃ n, 1 - δ - η ≤ rprobAns ν R D astar μ v n)
    (hwrong : ∀ z ∈ J, ∀ u ∈ Hs z, ∀ s : X → ℝ, (∀ x, 0 < s x) → ∀ n,
      rprobAns ν R D astar (fun x => pred x u) s n ≤ δ)
    (hCpos : 0 < actGameStar J hJ Hc pred μ v) :
    ENNReal.ofReal (klBin (1 - δ) δ / actGameStar J hJ Hc pred μ v) ≤ rexpTau ν R μ v := by
  by_cases htop : rexpTau ν R μ v = ⊤
  · rw [htop]; exact le_top
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [div_le_iff₀ hCpos]
  change bkl (1 - δ) δ ≤ _
  refine bkl_le_of_forall_small hδ0 hδ fun η hη0 hη1 => ?_
  obtain ⟨n, hn⟩ := hcorrect η hη0
  have hκ : 0 < bkl (1 - δ - η) δ := by
    have := pinsker (p := 1 - δ - η) (q := δ) (by linarith) (by linarith) hδ0 (by linarith)
    have h2 : 0 < 2 * (1 - δ - η - δ) ^ 2 := by
      have : 0 < 1 - δ - η - δ := by linarith
      positivity
    linarith
  have htr : ∀ z ∈ J, ∀ u ∈ Hs z, ∀ s : X → ℝ, (∀ x, 0 < s x) →
      bkl (1 - δ - η) δ ≤ ∑ x, rexpCnt ν R μ v n x * gaussKL (μ x) (v x) (pred x u) (s x) :=
    fun z hz u hu s hs => rbkl_le_of_event ν R (μ' := fun x => pred x u) hv hs n
      (measurableSet_jans R D astar n) hδ0 (by linarith) (by linarith) hn
      (hwrong z hz u hu s hs n)
  have hTpos : 0 < rexpTime ν R μ v n := by
    rcases (rexpTime_nonneg ν R μ v n).eq_or_lt with h0 | h0
    · exfalso
      have hz0 : ∀ x, rexpCnt ν R μ v n x = 0 := fun x =>
        (sum_eq_zero_iff_of_nonneg fun x _ => rexpCnt_nonneg ν R μ v n x).1
          ((sum_rexpCnt ν R μ v n).trans h0.symm) x (mem_univ x)
      obtain ⟨z, hz⟩ := hJ
      have hsne : (Hs z).Nonempty := by
        have := (hne z hz).mono (hcl z hz)
        exact closure_nonempty_iff.1 this
      obtain ⟨u, hu⟩ := hsne
      have := htr z hz u hu (fun _ => 1) (fun _ => one_pos)
      simp only [hz0, zero_mul, sum_const_zero] at this
      linarith
    · exact h0
  have h := (converse_reduction J hJ Hc Hs pred hpred hv (fun x => rexpCnt_nonneg ν R μ v n x)
    (sum_rexpCnt ν R μ v n) hTpos hne hcl htr
    (fun _ hw => actGame_le_star J hJ Hc pred hw hv) hCpos).2
  rw [div_le_iff₀ hCpos] at h
  exact h.trans (mul_le_mul_of_nonneg_right (rexpTime_le_of_ne_top ν R μ v htop n) hCpos.le)

/-- **`thm:v34-converse` / `thm:v34-converse-main` for randomised procedures**, with
`C_* = max_a C_a^*(μ, v)` over a finite action family.  `astar` is the unique correct action:
every other action is incorrect at the truth (`hinc`).  For each `δ ∈ (0, 1/2)` the randomised
procedure `(R δ, D δ)` with seed law `ν δ` is `δ`-correct in the sense of `hcorrect` and
`hwrong` (see `rv34_converse`).  Conclusions: `E τ_δ ≥ kl(1 - δ, δ) / C_*` for every
`δ ∈ (0, 1/2)`, and `liminf_{δ ↓ 0} E τ_δ / log (1/δ) ≥ 1 / C_*` in the form: for every
`c < 1 / C_*`, eventually `c log (1/δ) ≤ E τ_δ`. -/
theorem rv34_converse_main [TopologicalSpace U] [Fintype A] [Nonempty X] (astar : A)
    (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty) (Hc Hs : A → Z → Set U) (pred : X → U → ℝ)
    (hpred : ∀ x, Continuous (pred x)) {μ v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hne : ∀ z ∈ J astar, (Hc astar z).Nonempty)
    (hcl : ∀ z ∈ J astar, Hc astar z ⊆ closure (Hs astar z))
    (hinc : ∀ a, a ≠ astar → ∃ z ∈ J a, ∃ θ ∈ Hc a z, ∀ x, pred x θ = μ x)
    (hCpos : 0 < univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v))
    (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RGSampler X Sd) (D : ℝ → RGDecision A Sd)
    (hcorrect : ∀ δ, 0 < δ → δ < 1 / 2 → ∀ η > 0, ∃ n,
      1 - δ - η ≤ rprobAns (ν δ) (R δ) (D δ) astar μ v n)
    (hwrong : ∀ δ, 0 < δ → δ < 1 / 2 → ∀ z ∈ J astar, ∀ u ∈ Hs astar z, ∀ s : X → ℝ,
      (∀ x, 0 < s x) → ∀ n,
        rprobAns (ν δ) (R δ) (D δ) astar (fun x => pred x u) s n ≤ δ) :
    (∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v)) ≤ rexpTau (ν δ) (R δ) μ v) ∧
    ∀ c : ℝ, c < 1 / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v) →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (c * Real.log (1 / δ)) ≤ rexpTau (ν δ) (R δ) μ v := by
  classical
  have h0 : 0 ≤ actGameStar (J astar) (hJ astar) (Hc astar) pred μ v := by
    obtain ⟨x0⟩ := ‹Nonempty X›
    exact (actGame_nonneg (single_mem_simplex x0).1 hv).trans
      (actGame_le_star (J astar) (hJ astar) (Hc astar) pred (single_mem_simplex x0) hv)
  have heq := v34_Cstar_eq astar J hJ Hc pred hv hinc h0
  rw [heq] at hCpos ⊢
  have hfin : ∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / actGameStar (J astar) (hJ astar) (Hc astar) pred μ v)
        ≤ rexpTau (ν δ) (R δ) μ v := fun δ hδ0 hδ =>
    rv34_converse (ν δ) (R δ) (D δ) astar (J astar) (hJ astar) (Hc astar) (Hs astar) pred hpred
      hv hne hcl hδ0 hδ (hcorrect δ hδ0 hδ) (hwrong δ hδ0 hδ) hCpos
  refine ⟨hfin, fun c hc => ?_⟩
  have hev := liminf_coefficient (Eτ := fun δ => klBin (1 - δ) δ /
    actGameStar (J astar) (hJ astar) (Hc astar) pred μ v) hCpos (fun δ _ _ => le_rfl) hc
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ h1 h2
  exact (ENNReal.ofReal_le_ofReal h1).trans (hfin δ h2.1 h2.2)

end Converse

/-! ### `thm:bay-main-optimal` (lower bound) for randomised procedures -/

section KnownVariance

variable {U : Type*}

/-- **Stopping early is unlikely**, for one deterministic sampler, with the probability of each
listed wrong answer kept explicit (`GaussStopped.early_stop_bound` bounds each of them by
`δ`).  Fix `α ∈ (0, 1)`, `ζ = α I / (4 (1 - α))` and finite lists `Λ a` of alternatives that
cover every design at cost below `I + ζ`.  For any `T ≤ (1 - α) log (1/δ) / I`,
`P_θ(τ ≤ T) ≤ ∑ₐ ∑_{u ∈ Λ a} (e^{(1 - α/2) log(1/δ)} P_u(τ ≤ T + 1, â = a) + δ^κ)` with
`κ = α² I / (64 (I + ζ) (1 - α))`. -/
lemma early_stop_seed [Fintype A] [Nonempty X] (S : GSampler X) (D : GDecision A)
    (pred : X → U → ℝ) {μ v : X → ℝ} (hv : ∀ x, 0 < v x)
    {I ζ α δ : ℝ} (hI : 0 < I) (hα0 : 0 < α) (hα1 : α < 1)
    (hζ : ζ = α * I / (4 * (1 - α))) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Λ : A → Finset U)
    (hcov : ∀ a, ∀ w ∈ simplex X, ∃ u ∈ Λ a, gcost μ v pred w u < I + ζ)
    (T : ℕ) (hT : (T : ℝ) ≤ (1 - α) * Real.log (1 / δ) / I) :
    (law S μ v (T + 1)).real {y | halted S (List.ofFn (Fin.tail y)) = true} ≤
      ∑ a, ∑ u ∈ Λ a, (Real.exp ((1 - α / 2) * Real.log (1 / δ))
          * (law S (fun x => pred x u) v (T + 1)).real (ansSet S D a (T + 1))
        + δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α)))) := by
  classical
  obtain ⟨Lδ, hLδ⟩ : ∃ Lδ : ℝ, Lδ = Real.log (1 / δ) := ⟨_, rfl⟩
  rw [← hLδ] at hT ⊢
  have hL : 0 < Lδ := by
    rw [hLδ]; exact Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have h1α : 0 < 1 - α := by linarith
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  have hIζ : 0 < I + ζ := by linarith
  obtain ⟨Kbar, hKbar⟩ : ∃ Kbar : ℝ, Kbar = (I + ζ) * ((1 - α) * Lδ / I) := ⟨_, rfl⟩
  have hKpos : 0 < Kbar := by rw [hKbar]; positivity
  have hK2 : Kbar = (1 - α) * Lδ + α * Lδ / 4 := by
    rw [hKbar, hζ]; field_simp
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = α * Lδ / 4 := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  let base : A → U → Set (Fin (T + 1) → ℝ) := fun a u =>
    {y | halted S (List.ofFn (Fin.tail y)) = true ∧ decAt S D (List.ofFn y) = a ∧
      driftL S μ (fun x => pred x u) v (List.ofFn y) ≤ (I + ζ) * (time S (List.ofFn y) : ℝ)}
  let Mf : U → (Fin (T + 1) → ℝ) → ℝ := fun u y =>
    llrL S μ v (fun x => pred x u) v (List.ofFn y) - driftL S μ (fun x => pred x u) v (List.ofFn y)
  let B1 : A → U → Set (Fin (T + 1) → ℝ) := fun a u => base a u ∩ {y | Mf u y ≤ c1}
  let B2 : A → U → Set (Fin (T + 1) → ℝ) := fun a u => base a u ∩ {y | c1 < Mf u y}
  have hbase : ∀ a u, MeasurableSet (base a u) := fun a u =>
    ((measurable_tail T) (measurableSet_hset S T)).inter
      ((measurableSet_decAt S D a (T + 1)).inter
        (measurableSet_le (measurable_drift S μ _ v (T + 1))
          (measurable_const.mul (measurable_time S (T + 1)))))
  have hMf : ∀ u, Measurable (Mf u) := fun u =>
    (measurable_llr S μ v _ v (T + 1)).sub (measurable_drift S μ _ v (T + 1))
  have hB1 : ∀ a u, MeasurableSet (B1 a u) := fun a u =>
    (hbase a u).inter (measurableSet_le (hMf u) measurable_const)
  have hB2 : ∀ a u, MeasurableSet (B2 a u) := fun a u =>
    (hbase a u).inter (measurableSet_lt measurable_const (hMf u))
  have htime : ∀ y : Fin (T + 1) → ℝ, halted S (List.ofFn (Fin.tail y)) = true →
      (time S (List.ofFn y) : ℝ) ≤ (1 - α) * Lδ / I := by
    intro y hy
    have h1 : time S (List.ofFn y) ≤ T := by
      rw [ofFn_eq T y, time, hy]
      have := time_le_length S (List.ofFn (Fin.tail y))
      rw [List.length_ofFn] at this
      simpa using this
    exact le_trans (by exact_mod_cast h1) hT
  have hdrift : ∀ a u, ∀ y ∈ base a u,
      driftL S μ (fun x => pred x u) v (List.ofFn y) ≤ Kbar := by
    intro a u y hy
    rw [hKbar]
    exact hy.2.2.trans (mul_le_mul_of_nonneg_left (htime y hy.1) hIζ.le)
  -- first kind of event: change of measure to the invalidating alternative
  have hP1 : ∀ a u, law S μ v (T + 1) (B1 a u) ≤
      ENNReal.ofReal (Real.exp ((1 - α / 2) * Lδ))
        * law S (fun x => pred x u) v (T + 1) (ansSet S D a (T + 1)) := by
    intro a u
    refine (change_of_measure_bound (law S μ v (T + 1)) (law S (fun x => pred x u) v (T + 1))
      (L := fun y => llrL S μ v (fun x => pred x u) v (List.ofFn y))
      (law_eq_withDensity S hv hv (T + 1)) (hB1 a u) (c := (1 - α / 2) * Lδ) ?_).trans ?_
    · intro y hy
      have h1 := hdrift a u y hy.1
      have h2 : Mf u y ≤ c1 := hy.2
      have h3 : llrL S μ v (fun x => pred x u) v (List.ofFn y) =
          driftL S μ (fun x => pred x u) v (List.ofFn y) + Mf u y := by
        simp only [Mf]; ring
      rw [h3]
      rw [hK2] at h1
      rw [hc1] at h2
      linarith
    · have hsub : B1 a u ⊆ ansSet S D a (T + 1) := by
        intro y hy
        refine ⟨?_, hy.1.2.1⟩
        rw [ofFn_eq T y, halted, hy.1.1]
        rfl
      gcongr
  -- second kind of event: change of measure to a tilted mean vector
  have hP2 : ∀ a u, law S μ v (T + 1) (B2 a u) ≤
      ENNReal.ofReal (δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α)))) := by
    intro a u
    obtain ⟨η, hη⟩ : ∃ η : ℝ, η = c1 / (2 * Kbar) := ⟨_, rfl⟩
    have hηpos : 0 < η := by rw [hη]; positivity
    have hcm := change_of_measure_bound (law S μ v (T + 1))
      (law S (fun x => μ x + η * (μ x - pred x u)) v (T + 1))
      (L := fun y => llrL S μ v (fun x => μ x + η * (μ x - pred x u)) v (List.ofFn y))
      (law_eq_withDensity S hv hv (T + 1)) (hB2 a u)
      (c := -(α ^ 2 * I / (64 * (I + ζ) * (1 - α))) * Lδ) (fun y hy => by
        have h1 := hdrift a u y hy.1
        have h2 : c1 < Mf u y := hy.2
        rw [llrL_tilt S μ (fun x => pred x u) v (fun x => (hv x).ne') η]
        have e1 : η ^ 2 * driftL S μ (fun x => pred x u) v (List.ofFn y) ≤ η ^ 2 * Kbar :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg η)
        have e2 : η * c1 ≤ η * Mf u y := mul_le_mul_of_nonneg_left h2.le hηpos.le
        have e3 : η ^ 2 * Kbar - η * c1 = -(α ^ 2 * I / (64 * (I + ζ) * (1 - α))) * Lδ := by
          rw [hη, hc1, hKbar]; field_simp; ring
        have e4 : Mf u y = llrL S μ v (fun x => pred x u) v (List.ofFn y) -
            driftL S μ (fun x => pred x u) v (List.ofFn y) := rfl
        rw [e4] at e2
        linarith)
    refine hcm.trans ?_
    have hexp : Real.exp (-(α ^ 2 * I / (64 * (I + ζ) * (1 - α))) * Lδ) =
        δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α))) := by
      rw [Real.rpow_def_of_pos hδ0, hLδ, one_div, Real.log_inv]
      congr 1; ring
    rw [hexp]
    calc ENNReal.ofReal (δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α)))) *
          law S (fun x => μ x + η * (μ x - pred x u)) v (T + 1) (B2 a u)
        ≤ ENNReal.ofReal (δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α)))) * 1 := by
          gcongr; exact prob_le_one
      _ = _ := mul_one _
  -- covering
  have hcover : {y : Fin (T + 1) → ℝ | halted S (List.ofFn (Fin.tail y)) = true} ⊆
      ⋃ a ∈ (univ : Finset A), ⋃ u ∈ Λ a, (B1 a u ∪ B2 a u) := by
    intro y hy
    have hy' : halted S (List.ofFn (Fin.tail y)) = true := hy
    obtain ⟨u, hu, hd⟩ : ∃ u ∈ Λ (decAt S D (List.ofFn y)),
        driftL S μ (fun x => pred x u) v (List.ofFn y) ≤
          (I + ζ) * (time S (List.ofFn y) : ℝ) := by
      by_cases hτ : time S (List.ofFn y) = 0
      · obtain ⟨x0⟩ := ‹Nonempty X›
        obtain ⟨u, hu, -⟩ := hcov (decAt S D (List.ofFn y)) _ (single_mem_simplex x0)
        refine ⟨u, hu, ?_⟩
        have h0 : ∀ x, cnt S x (List.ofFn y) = 0 := by
          have := sum_cnt S (List.ofFn y)
          rw [hτ] at this
          exact fun x => (sum_eq_zero_iff.1 this) x (mem_univ x)
        rw [driftL_eq_sum, hτ]
        simp only [h0, Nat.cast_zero, zero_mul, sum_const_zero, mul_zero]
        exact le_rfl
      · have hτpos : (0 : ℝ) < time S (List.ofFn y) := by
          exact_mod_cast Nat.pos_of_ne_zero hτ
        have hw : (fun x => (cnt S x (List.ofFn y) : ℝ) / (time S (List.ofFn y) : ℝ))
            ∈ simplex X := by
          refine ⟨fun x => by positivity, ?_⟩
          rw [← sum_div, ← time_eq_sum, div_self hτpos.ne']
        obtain ⟨u, hu, hlt⟩ := hcov (decAt S D (List.ofFn y)) _ hw
        refine ⟨u, hu, ?_⟩
        have hg : gcost μ v pred
            (fun x => (cnt S x (List.ofFn y) : ℝ) / (time S (List.ofFn y) : ℝ)) u =
            driftL S μ (fun x => pred x u) v (List.ofFn y) / (time S (List.ofFn y) : ℝ) := by
          rw [driftL_eq_sum, sum_div]
          unfold gcost
          exact sum_congr rfl fun x _ => by ring
        rw [hg, div_lt_iff₀ hτpos] at hlt
        exact hlt.le
    simp only [Set.mem_iUnion]
    refine ⟨decAt S D (List.ofFn y), mem_univ _, u, hu, ?_⟩
    rcases le_or_gt (Mf u y) c1 with hM | hM
    · exact Or.inl ⟨⟨hy', rfl, hd⟩, hM⟩
    · exact Or.inr ⟨⟨hy', rfl, hd⟩, hM⟩
  have henn : law S μ v (T + 1) {y | halted S (List.ofFn (Fin.tail y)) = true} ≤
      ∑ a, ∑ u ∈ Λ a, (ENNReal.ofReal (Real.exp ((1 - α / 2) * Lδ))
          * law S (fun x => pred x u) v (T + 1) (ansSet S D a (T + 1))
        + ENNReal.ofReal (δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α))))) :=
    calc law S μ v (T + 1) {y | halted S (List.ofFn (Fin.tail y)) = true}
        ≤ law S μ v (T + 1) (⋃ a ∈ (univ : Finset A), ⋃ u ∈ Λ a, (B1 a u ∪ B2 a u)) :=
          measure_mono hcover
      _ ≤ ∑ a, law S μ v (T + 1) (⋃ u ∈ Λ a, (B1 a u ∪ B2 a u)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ a, ∑ u ∈ Λ a, law S μ v (T + 1) (B1 a u ∪ B2 a u) :=
          sum_le_sum fun a _ => measure_biUnion_finset_le _ _
      _ ≤ _ := sum_le_sum fun a _ => sum_le_sum fun u _ =>
          (measure_union_le _ _).trans (add_le_add (hP1 a u) (hP2 a u))
  -- back to real numbers
  have hterm : ∀ (a : A) (u : U), 0 ≤ Real.exp ((1 - α / 2) * Lδ)
        * (law S (fun x => pred x u) v (T + 1)).real (ansSet S D a (T + 1))
      + δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α))) := fun a u =>
    add_nonneg (mul_nonneg (Real.exp_pos _).le measureReal_nonneg) (Real.rpow_nonneg hδ0.le _)
  refine ENNReal.toReal_le_of_le_ofReal
    (sum_nonneg fun a _ => sum_nonneg fun u _ => hterm a u) (henn.trans (le_of_eq ?_))
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ => sum_nonneg fun u _ => hterm a u]
  refine sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun u _ => hterm a u]
  refine sum_congr rfl fun u _ => ?_
  rw [ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
      (Real.rpow_nonneg hδ0.le _), ENNReal.ofReal_mul (Real.exp_pos _).le, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Correlated Gaussian information limit, lower bound (`thm:bay-main-optimal`,
`eq:bay-main-optimal`), for randomised procedures.**
Known query variances `v`, true query means `μ`; an alternative `u` has query means
`pred · u`; `Alt a` is the set of alternatives under which the action `a` is not
`ε`-correct.  `I` is any upper bound for the information rates
`I_a(θ, w) = inf_{u ∈ Alt a} gcost μ v pred w u` over all actions and designs (`hinfo`), in
particular `I = I_*(θ) = max_a max_w I_a(θ, w)`.  The randomised procedures `(R δ, D δ)` with
seed laws `ν δ` are uniformly correct in the sense used by the proof (`hcorrect`): under every
alternative in `Alt a` the probability (over observations and seed) of halting with answer `a`
is at most `δ`, at every horizon.  No assumption is made on which answers are correct at the
truth.
Conclusion: `liminf_{δ ↓ 0} E_θ[τ_δ] / log (1/δ) ≥ 1 / I`, in the form: for every `c < 1 / I`,
eventually `c log (1/δ) ≤ E_θ[τ_δ]`. -/
theorem rgauss_info_lower_bound [Fintype A] [Nonempty X] (pred : X → U → ℝ) (Alt : A → Set U)
    {μ v : X → ℝ} (hv : ∀ x, 0 < v x) {I : ℝ} (hI : 0 < I)
    (hinfo : ∀ a, ∀ w ∈ simplex X, ∀ ζ > 0, ∃ u ∈ Alt a, gcost μ v pred w u < I + ζ)
    (ν : ℝ → Measure Sd) [∀ δ, IsProbabilityMeasure (ν δ)]
    (R : ℝ → RGSampler X Sd) (D : ℝ → RGDecision A Sd)
    (hcorrect : ∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ u ∈ Alt a, ∀ n,
      rprobAns (ν δ) (R δ) (D δ) a (fun x => pred x u) v n ≤ δ)
    {c : ℝ} (hc : c < 1 / I) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c * Real.log (1 / δ)) ≤ rexpTau (ν δ) (R δ) μ v := by
  classical
  rcases le_or_gt c 0 with hc0 | hc0
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    have : c * Real.log (1 / δ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc0
        (Real.log_nonneg (by rw [le_div_iff₀ hδ.1]; linarith [hδ.2]))
    rw [ENNReal.ofReal_of_nonpos this]
    exact zero_le
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c * I := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr]; exact (lt_div_iff₀ hI).1 hc
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (1 - r) / 2 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have h1α : 0 < 1 - α := by linarith
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = α * I / (4 * (1 - α)) := ⟨_, rfl⟩
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  choose Λ hΛ hcov using fun a =>
    exists_finite_cover pred (Alt a) (μ := μ) (v := v) (c := I + ζ)
      (fun w hw => hinfo a w hw ζ hζ0)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = α ^ 2 * I / (64 * (I + ζ) * (1 - α)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨Nn, hNn⟩ : ∃ Nn : ℕ, Nn = ∑ a, (Λ a).card := ⟨_, rfl⟩
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℝ, ε0 = (1 - r) / (1 + r) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    rw [hε0]; exact div_pos (by linarith) (by linarith)
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (Nn : ℝ) * (δ ^ (α / 2) + δ ^ κ) ≤ ε0 := by
    have h1 : Tendsto (fun δ : ℝ => δ ^ (α / 2)) (𝓝 0) (𝓝 0) := by
      have := (Real.continuous_rpow_const (q := α / 2) (by positivity)).tendsto 0
      rwa [Real.zero_rpow (by positivity)] at this
    have h2 : Tendsto (fun δ : ℝ => δ ^ κ) (𝓝 0) (𝓝 0) := by
      have := (Real.continuous_rpow_const (q := κ) hκ0.le).tendsto 0
      rwa [Real.zero_rpow hκ0.ne'] at this
    have h3 : Tendsto (fun δ : ℝ => (Nn : ℝ) * (δ ^ (α / 2) + δ ^ κ)) (𝓝[>] 0) (𝓝 0) := by
      have := ((h1.add h2).const_mul (Nn : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact (h3.eventually (gt_mem_nhds hε0pos)).mono fun _ h => h.le
  filter_upwards [hsmall, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hsm hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  obtain ⟨Lδ, hLδ⟩ : ∃ Lδ : ℝ, Lδ = Real.log (1 / δ) := ⟨_, rfl⟩
  have hL : 0 < Lδ := by
    rw [hLδ]; exact Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  rw [← hLδ]
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = ⌊(1 - α) * Lδ / I⌋₊ := ⟨_, rfl⟩
  have hT : (T : ℝ) ≤ (1 - α) * Lδ / I := by
    rw [hTdef]; exact Nat.floor_le (by positivity)
  have hT' : (1 - α) * Lδ / I < (T : ℝ) + 1 := by
    rw [hTdef]; exact Nat.lt_floor_add_one _
  -- the early-stopping event, jointly in the seed and the transcript
  have hEH : MeasurableSet {p : Sd × (Fin (T + 1) → ℝ) |
      halted ((R δ).run p.1) (List.ofFn (Fin.tail p.2)) = true} :=
    (measurable_jtail T) (measurableSet_jhalt (R δ) T)
  have hHi : Integrable (fun s => (law ((R δ).run s) μ v (T + 1)).real
      {y | halted ((R δ).run s) (List.ofFn (Fin.tail y)) = true}) (ν δ) :=
    integrable_law_real (ν δ) (R δ) μ v (T + 1) hEH
  have hAi : ∀ (a : A) (u : U), Integrable (fun s =>
      (law ((R δ).run s) (fun x => pred x u) v (T + 1)).real
        (ansSet ((R δ).run s) ((D δ).run s) a (T + 1))) (ν δ) := fun a u =>
    integrable_law_real (ν δ) (R δ) (fun x => pred x u) v (T + 1)
      (measurableSet_jans (R δ) (D δ) a (T + 1))
  -- the seed-wise bound
  have hseed : ∀ s, (law ((R δ).run s) μ v (T + 1)).real
      {y | halted ((R δ).run s) (List.ofFn (Fin.tail y)) = true} ≤
      ∑ a, ∑ u ∈ Λ a, (Real.exp ((1 - α / 2) * Lδ)
          * (law ((R δ).run s) (fun x => pred x u) v (T + 1)).real
              (ansSet ((R δ).run s) ((D δ).run s) a (T + 1)) + δ ^ κ) := fun s => by
    have h := early_stop_seed ((R δ).run s) ((D δ).run s) pred hv hI hα0 hα1 hζ hδ0 hδ1 Λ hcov
      T (by rw [← hLδ]; exact hT)
    rw [← hLδ, ← hκ] at h
    exact h
  have hIu : ∀ (a : A), ∀ u ∈ Λ a, Integrable (fun s => Real.exp ((1 - α / 2) * Lδ)
      * (law ((R δ).run s) (fun x => pred x u) v (T + 1)).real
          (ansSet ((R δ).run s) ((D δ).run s) a (T + 1)) + δ ^ κ) (ν δ) := fun a u _ =>
    ((hAi a u).const_mul _).add (integrable_const _)
  have hIa : ∀ a ∈ (univ : Finset A), Integrable (fun s => ∑ u ∈ Λ a,
      (Real.exp ((1 - α / 2) * Lδ)
        * (law ((R δ).run s) (fun x => pred x u) v (T + 1)).real
            (ansSet ((R δ).run s) ((D δ).run s) a (T + 1)) + δ ^ κ)) (ν δ) := fun a _ =>
    integrable_finsetSum _ (hIu a)
  have hint := integral_mono hHi (integrable_finsetSum _ hIa) hseed
  rw [integral_finsetSum _ hIa] at hint
  have hterm : ∀ a : A, ∫ s, ∑ u ∈ Λ a, (Real.exp ((1 - α / 2) * Lδ)
        * (law ((R δ).run s) (fun x => pred x u) v (T + 1)).real
            (ansSet ((R δ).run s) ((D δ).run s) a (T + 1)) + δ ^ κ) ∂(ν δ)
      ≤ ∑ _u ∈ Λ a, (δ ^ (α / 2) + δ ^ κ) := by
    intro a
    rw [integral_finsetSum _ (hIu a)]
    refine sum_le_sum fun u hu => ?_
    have hc1 : Integrable (fun s => Real.exp ((1 - α / 2) * Lδ)
        * (law ((R δ).run s) (fun x => pred x u) v (T + 1)).real
            (ansSet ((R δ).run s) ((D δ).run s) a (T + 1))) (ν δ) := (hAi a u).const_mul _
    have e : ∫ s, (Real.exp ((1 - α / 2) * Lδ)
          * (law ((R δ).run s) (fun x => pred x u) v (T + 1)).real
              (ansSet ((R δ).run s) ((D δ).run s) a (T + 1)) + δ ^ κ) ∂(ν δ)
        = Real.exp ((1 - α / 2) * Lδ)
            * rprobAns (ν δ) (R δ) (D δ) a (fun x => pred x u) v (T + 1) + δ ^ κ := by
      rw [integral_add hc1 (integrable_const _), integral_const_mul]
      simp [rprobAns]
    rw [e]
    have h1 := hcorrect δ hδ0 hδ1 a u (hΛ a u hu) (T + 1)
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos ((1 - α / 2) * Lδ)).le
    have h3 : Real.exp ((1 - α / 2) * Lδ) * δ = δ ^ (α / 2) := by
      rw [hLδ]; exact exp_log_inv_mul hδ0
    linarith
  have esum : ∑ a, ∑ _u ∈ Λ a, (δ ^ (α / 2) + δ ^ κ) = (Nn : ℝ) * (δ ^ (α / 2) + δ ^ κ) := by
    rw [hNn]
    push_cast
    rw [sum_mul]
    exact sum_congr rfl fun a _ => by rw [sum_const, nsmul_eq_mul]
  have hreal : ∫ s, (law ((R δ).run s) μ v (T + 1)).real
      {y | halted ((R δ).run s) (List.ofFn (Fin.tail y)) = true} ∂(ν δ) ≤ ε0 :=
    (hint.trans (sum_le_sum fun a _ => hterm a)).trans (esum.le.trans hsm)
  -- Markov, averaged over the seed
  have hge : ((T : ℝ) + 1) * (1 - ∫ s, (law ((R δ).run s) μ v (T + 1)).real
      {y | halted ((R δ).run s) (List.ofFn (Fin.tail y)) = true} ∂(ν δ))
      ≤ rexpTime (ν δ) (R δ) μ v (T + 1) := by
    have h1 : Integrable (fun s => 1 - (law ((R δ).run s) μ v (T + 1)).real
        {y | halted ((R δ).run s) (List.ofFn (Fin.tail y)) = true}) (ν δ) :=
      (integrable_const (1 : ℝ)).sub hHi
    have h2 : Integrable (fun s => ((T : ℝ) + 1) * (1 - (law ((R δ).run s) μ v (T + 1)).real
        {y | halted ((R δ).run s) (List.ofFn (Fin.tail y)) = true})) (ν δ) := h1.const_mul _
    have h := integral_mono h2 (integrable_expTime (ν δ) (R δ) μ v (T + 1)) fun s =>
      expTime_ge ((R δ).run s) μ v T
    rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hHi] at h
    simpa [rexpTime] using h
  have hfin : c * Lδ ≤ rexpTime (ν δ) (R δ) μ v (T + 1) := by
    have e1 : c * Lδ = (1 - α) * Lδ / I * (1 - ε0) := by
      have hc' : c = r / I := by rw [hr]; field_simp
      have h1r : (1 : ℝ) + r ≠ 0 := by linarith
      rw [hc', hε0, hα]; field_simp; ring
    have h1ε : 0 ≤ 1 - ε0 := by
      rw [hε0, sub_nonneg, div_le_one (by linarith)]; linarith
    rw [e1]
    refine le_trans ?_ hge
    exact mul_le_mul hT'.le (by linarith) h1ε (by positivity)
  exact (ENNReal.ofReal_le_ofReal hfin).trans
    (le_iSup (fun n => ENNReal.ofReal (rexpTime (ν δ) (R δ) μ v n)) (T + 1))

end KnownVariance

end

end RandG

end JointRootCert
