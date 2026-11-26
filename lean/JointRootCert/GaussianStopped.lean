/-
Stopped adaptive Gaussian sampling: change of measure, Wald identity, transportation
inequality, and the two lower bounds that rest on them.

Manuscript results covered:

* the Gaussian analogue of `lem:active-com` (stopped change of measure), which the manuscript
  uses without a number in the proofs of `thm:v34-converse` and `thm:bay-main-optimal`:
  `law_eq_map_hist` (the model), `law_eq_withDensity` (explicit density), `wald_identity`,
  `gauss_transport_finite`, `gauss_transport_noise` (finite horizon), `gauss_transport`,
  `gauss_stopped_transport` (unbounded stopping time).
* `thm:v34-converse` / `thm:v34-converse-main` "Unknown-variance nuisance-KL lower bound for one
  correct answer": `v34_converse`, `v34_Cstar_eq`, `v34_converse_main`.
* `thm:bay-main-optimal` "Correlated Gaussian information limit", lower-bound half:
  `early_stop_bound`, `gauss_info_lower_bound`.  The Gaussian exponential maximal bound of the
  manuscript's proof is replaced by a second change of measure, to a mean vector tilted along
  the line through the truth and the alternative (`llrL_tilt`).  The upper-bound half
  (existence of a tracker attaining equality) is not treated here.

Model.  A sampler is a pair of functions of the observed history (a `List ℝ`, most recent
observation first): the next query type and whether to stop.  The policy is deterministic.
Under a parameter `(μ, v)` (mean and variance of each query type) the observation at a
non-halted history `h` is `μ (next h) + √(v (next h)) · g` for a fresh standard Gaussian `g`.
After the sampler has halted the transcript is continued with standard Gaussian noise that does
not depend on the parameter, so that the transcript is defined at every deterministic horizon
`n` and its law `law S μ v n` is a probability measure on `Fin n → ℝ` (coordinate `0` is the
most recent observation).  `law_eq_map_hist` proves that `law S μ v n` is the law of the
transcript `hist S μ v n` computed from i.i.d. standard Gaussian noise on the product space
`Measure.pi (fun _ : Fin n => gaussianReal 0 1)`.

Not covered: internal randomization of the sampler before stopping; a single probability space
carrying the unbounded run (quantities of the unbounded run are suprema / limits over the
horizon, as in `StoppedProcess.lean`).
-/
import JointRootCert.StoppedProcess
import JointRootCert.GaussianInfo
import JointRootCert.UnknownVariance

namespace JointRootCert

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace GaussStopped

/-- An adaptive sampler on real-valued histories (most recent observation first). -/
structure GSampler (X : Type*) [MeasurableSpace X] where
  /-- the query type chosen after a history -/
  next : List ℝ → X
  /-- whether to stop at a history -/
  stop : List ℝ → Bool
  meas_next : ∀ k : ℕ, Measurable fun y : Fin k → ℝ => next (List.ofFn y)
  meas_stop : ∀ k : ℕ, Measurable fun y : Fin k → ℝ => stop (List.ofFn y)

variable {X : Type*} [MeasurableSpace X]

/-- The sampler has stopped at this history or at an earlier one. -/
def halted (S : GSampler X) : List ℝ → Bool
  | [] => S.stop []
  | y :: h => halted S h || S.stop (y :: h)

/-- The halted histories of length `n`. -/
def hset (S : GSampler X) (n : ℕ) : Set (Fin n → ℝ) := {y | halted S (List.ofFn y) = true}

lemma measurable_cons (n : ℕ) :
    Measurable fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_snd
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_fst

lemma measurable_tail (n : ℕ) :
    Measurable fun y : Fin (n + 1) → ℝ => (Fin.tail y : Fin n → ℝ) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

lemma ofFn_eq (n : ℕ) (y : Fin (n + 1) → ℝ) :
    List.ofFn y = y 0 :: List.ofFn (Fin.tail y) := by
  rw [List.ofFn_succ]; rfl

lemma measurableSet_hset (S : GSampler X) : ∀ n, MeasurableSet (hset S n)
  | 0 => by
    have : hset S 0 = {_y | S.stop [] = true} := by
      ext y; simp [hset, halted]
    rw [this]; exact MeasurableSet.const _
  | n + 1 => by
    have : hset S (n + 1) = (fun y => Fin.tail y) ⁻¹' (hset S n) ∪
        (fun y : Fin (n + 1) → ℝ => S.stop (List.ofFn y)) ⁻¹' {true} := by
      ext y
      simp only [hset, Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage,
        Set.mem_singleton_iff]
      rw [ofFn_eq n y, halted, Bool.or_eq_true, ← ofFn_eq n y]
    rw [this]
    exact ((measurable_tail n) (measurableSet_hset S n)).union
      (S.meas_stop (n + 1) (measurableSet_singleton true))

variable [MeasurableSingletonClass X] [Fintype X]

/-- Law of the next observation after history `h` under the parameter `(μ, v)`: standard
Gaussian padding once halted, otherwise `N(μ_x, v_x)` for the queried type `x`. -/
def stepM (S : GSampler X) (μ v : X → ℝ) (h : List ℝ) : Measure ℝ :=
  if halted S h then gaussianReal 0 1 else gaussianReal (μ (S.next h)) (v (S.next h)).toNNReal

instance (S : GSampler X) (μ v : X → ℝ) (h : List ℝ) : IsProbabilityMeasure (stepM S μ v h) := by
  unfold stepM; split_ifs <;> infer_instance

/-- The kernel of query laws indexed by the query type. -/
def typeKernel (μ v : X → ℝ) : Kernel X ℝ :=
  Kernel.ofFunOfCountable fun x => gaussianReal (μ x) (v x).toNNReal

instance (μ v : X → ℝ) : IsMarkovKernel (typeKernel (X := X) μ v) :=
  ⟨fun x => by change IsProbabilityMeasure (gaussianReal (μ x) (v x).toNNReal); infer_instance⟩

open scoped Classical in
/-- The one-step transition kernel from histories of length `n`. -/
def kern (S : GSampler X) (μ v : X → ℝ) (n : ℕ) : Kernel (Fin n → ℝ) ℝ :=
  Kernel.piecewise (measurableSet_hset S n) (Kernel.const _ (gaussianReal 0 1))
    (Kernel.comap (typeKernel μ v) _ (S.meas_next n))

instance (S : GSampler X) (μ v : X → ℝ) (n : ℕ) : IsMarkovKernel (kern S μ v n) := by
  unfold kern; infer_instance

lemma kern_apply (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (y : Fin n → ℝ) :
    kern S μ v n y = stepM S μ v (List.ofFn y) := by
  classical
  unfold kern stepM
  rw [Kernel.piecewise_apply]
  by_cases hy : y ∈ hset S n
  · have hy' : halted S (List.ofFn y) = true := hy
    simp [hy, hy']
  · have hy' : ¬ halted S (List.ofFn y) = true := hy
    simp only [hy, hy', ite_false, Kernel.comap_apply]
    rfl

/-- **Law of the transcript at horizon `n`** under the parameter `(μ, v)`. -/
def law (S : GSampler X) (μ v : X → ℝ) : (n : ℕ) → Measure (Fin n → ℝ)
  | 0 => Measure.dirac (fun _ => 0)
  | n + 1 => ((law S μ v n) ⊗ₘ (kern S μ v n)).map
      (fun p => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ))

instance law_prob (S : GSampler X) (μ v : X → ℝ) : ∀ n, IsProbabilityMeasure (law S μ v n)
  | 0 => by unfold law; infer_instance
  | n + 1 => by
    have := law_prob S μ v n
    rw [law]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_cons n).aemeasurable).2 inferInstance

lemma law_succ (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    law S μ v (n + 1) = ((law S μ v n) ⊗ₘ (kern S μ v n)).map
      (fun p => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)) := rfl

/-- Consistency of the horizons: forgetting the last observation of the `(n+1)`-transcript
gives the `n`-transcript. -/
theorem law_map_tail (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    (law S μ v (n + 1)).map (fun y => (Fin.tail y : Fin n → ℝ)) = law S μ v n := by
  rw [law_succ, Measure.map_map (measurable_tail n) (measurable_cons n)]
  have : ((fun y : Fin (n + 1) → ℝ => (Fin.tail y : Fin n → ℝ)) ∘
      fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)) = Prod.fst := by
    funext p; simp
  rw [this]
  exact Measure.fst_compProd _ _

/-- One-step disintegration of the transcript law (Tonelli form). -/
theorem lintegral_law_succ (S : GSampler X) (μ v : X → ℝ) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F y ∂(law S μ v (n + 1)) =
      ∫⁻ y', ∫⁻ t, F (Fin.cons t y') ∂(stepM S μ v (List.ofFn y')) ∂(law S μ v n) := by
  rw [law_succ, lintegral_map hF (measurable_cons n),
    Measure.lintegral_compProd (f := fun p => F (Fin.cons p.2 p.1)) (hF.comp (measurable_cons n))]
  simp_rw [kern_apply]

/-! ### The transcript as a function of standard Gaussian noise -/

/-- The observation produced from the noise value `g` after history `h`. -/
def obs (S : GSampler X) (μ v : X → ℝ) (h : List ℝ) (g : ℝ) : ℝ :=
  if halted S h then g else μ (S.next h) + Real.sqrt (v (S.next h)) * g

/-- The transcript at horizon `n` as a function of the noise vector (coordinate `0` is the
most recent). -/
def hist (S : GSampler X) (μ v : X → ℝ) : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _ => fun _ => 0
  | n + 1, ω => Fin.cons (obs S μ v (List.ofFn (hist S μ v n (Fin.tail ω))) (ω 0))
      (hist S μ v n (Fin.tail ω))

lemma map_obs (S : GSampler X) (μ v : X → ℝ) (h : List ℝ) :
    (gaussianReal 0 1).map (obs S μ v h) = stepM S μ v h := by
  unfold obs stepM
  cases hh : halted S h
  swap
  · simp
  · simp only [Bool.false_eq_true, ite_false]
    set m := μ (S.next h)
    set c := Real.sqrt (v (S.next h))
    have h1 : (fun g : ℝ => m + c * g) = (fun t => m + t) ∘ (fun g => c * g) := rfl
    rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    congr 1
    · simp
    · ext
      rcases le_total 0 (v (S.next h)) with h0 | h0
      · simp [c, Real.sq_sqrt h0, Real.coe_toNNReal _ h0]
      · simp [c, Real.sqrt_eq_zero_of_nonpos h0, Real.toNNReal_of_nonpos h0]

lemma measurable_obs_right (S : GSampler X) (μ v : X → ℝ) (h : List ℝ) :
    Measurable (obs S μ v h) := by
  unfold obs; split_ifs <;> fun_prop

/-- Joint measurability of a one-step quantity that is `a` once halted and depends on the
queried type otherwise. -/
lemma measurable_step {β : Type*} [MeasurableSpace β] (S : GSampler X) (n : ℕ) {a : ℝ → β}
    {f : ℝ × X → β} (ha : Measurable a) (hf : ∀ x, Measurable fun t => f (t, x)) :
    Measurable fun p : (Fin n → ℝ) × ℝ =>
      if halted S (List.ofFn p.1) then a p.2 else f (p.2, S.next (List.ofFn p.1)) := by
  refine Measurable.ite (measurable_fst (measurableSet_hset S n)) (ha.comp measurable_snd) ?_
  exact (measurable_from_prod_countable_left hf).comp
    (measurable_snd.prodMk ((S.meas_next n).comp measurable_fst))

lemma measurable_obs (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    Measurable fun p : (Fin n → ℝ) × ℝ => obs S μ v (List.ofFn p.1) p.2 := by
  unfold obs
  exact measurable_step S n (a := fun g => g) (f := fun q => μ q.2 + Real.sqrt (v q.2) * q.1)
    measurable_id (fun x => by fun_prop)

lemma measurable_hist (S : GSampler X) (μ v : X → ℝ) : ∀ n, Measurable (hist S μ v n)
  | 0 => measurable_const
  | n + 1 => by
    have ih := (measurable_hist S μ v n).comp (measurable_tail n)
    exact (measurable_cons n).comp
      (ih.prodMk ((measurable_obs S μ v n).comp (ih.prodMk (measurable_pi_apply 0))))

/-- **The transcript law is the law of the transcript computed from i.i.d. standard Gaussian
noise.** -/
theorem law_eq_map_hist (S : GSampler X) (μ v : X → ℝ) :
    ∀ n, (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (hist S μ v n) = law S μ v n
  | 0 => by
    rw [Measure.pi_of_empty (fun _ : Fin 0 => gaussianReal 0 1) (fun _ => 0),
      Measure.map_dirac' (measurable_hist S μ v 0)]
    rfl
  | n + 1 => by
    have ih := law_eq_map_hist S μ v n
    have he : (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) =
        (gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0).map_eq
    obtain ⟨G, hGdef⟩ : ∃ G : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ), G = fun q =>
      Fin.cons (obs S μ v (List.ofFn (hist S μ v n q.2)) q.1) (hist S μ v n q.2) := ⟨_, rfl⟩
    have hH : Measurable fun q : ℝ × (Fin n → ℝ) => hist S μ v n q.2 :=
      (measurable_hist S μ v n).comp measurable_snd
    have hG : Measurable G := by
      rw [hGdef]
      exact (measurable_cons n).comp
        (hH.prodMk ((measurable_obs S μ v n).comp (hH.prodMk measurable_fst)))
    have hcomp : hist S μ v (n + 1) =
        G ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) := by
      funext ω
      simp only [hist, hGdef, Function.comp_apply, MeasurableEquiv.piFinSuccAbove_apply]
      rfl
    rw [hcomp, ← Measure.map_map hG (MeasurableEquiv.measurable _), he, law_succ, ← ih]
    ext s hs
    have hs' := (measurable_cons n) hs
    rw [Measure.map_apply hG hs, Measure.map_apply (measurable_cons n) hs,
      Measure.prod_apply_symm (hG hs), Measure.compProd_apply hs',
      lintegral_map (Kernel.measurable_kernel_prodMk_left hs') (measurable_hist S μ v n)]
    refine lintegral_congr fun ω' => ?_
    rw [kern_apply, ← map_obs,
      Measure.map_apply (measurable_obs_right S μ v _) (measurable_prodMk_left hs'), hGdef]
    rfl

/-! ### Density of one parameter with respect to another -/

/-- The log density ratio `log (dN(m, v) / dN(m', v'))` at `t`. -/
def qf (m v m' v' t : ℝ) : ℝ :=
  1 / 2 * Real.log (v' / v) - (t - m) ^ 2 / (2 * v) + (t - m') ^ 2 / (2 * v')

lemma measurable_qf (m v m' v' : ℝ) : Measurable (qf m v m' v') := by
  unfold qf; fun_prop

lemma gaussianPDFReal_eq_mul_exp_qf {m v m' v' : ℝ} (hv : 0 < v) (hv' : 0 < v') (t : ℝ) :
    gaussianPDFReal m v.toNNReal t =
      gaussianPDFReal m' v'.toNNReal t * Real.exp (qf m v m' v' t) := by
  have hq : qf m v m' v' t = Real.log (Real.sqrt (v' / v)) + -(t - m) ^ 2 / (2 * v)
      + (t - m') ^ 2 / (2 * v') := by
    rw [Real.log_sqrt (by positivity)]; unfold qf; ring
  have hs : 0 < Real.sqrt (v' / v) := Real.sqrt_pos.2 (by positivity)
  have e2 : Real.exp (-(t - m') ^ 2 / (2 * v')) * Real.exp ((t - m') ^ 2 / (2 * v')) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  have hsv := Real.sqrt_pos.2 hv
  have hsv' := Real.sqrt_pos.2 hv'
  have h2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have e3 : (Real.sqrt (2 * Real.pi * v'))⁻¹ * Real.sqrt (v' / v)
      = (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    rw [Real.sqrt_div hv'.le, Real.sqrt_mul (by positivity) v', Real.sqrt_mul (by positivity) v]
    field_simp
  simp only [gaussianPDFReal, Real.coe_toNNReal _ hv.le, Real.coe_toNNReal _ hv'.le]
  rw [hq, Real.exp_add, Real.exp_add, Real.exp_log hs]
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(t - m) ^ 2 / (2 * v))
      = ((Real.sqrt (2 * Real.pi * v'))⁻¹ * Real.sqrt (v' / v)) *
        (Real.exp (-(t - m') ^ 2 / (2 * v')) * Real.exp ((t - m') ^ 2 / (2 * v'))) *
        Real.exp (-(t - m) ^ 2 / (2 * v)) := by rw [e3, e2]; ring
    _ = _ := by ring

/-- One Gaussian law as a density with respect to another. -/
lemma gaussianReal_eq_withDensity {m v m' v' : ℝ} (hv : 0 < v) (hv' : 0 < v') :
    gaussianReal m v.toNNReal = (gaussianReal m' v'.toNNReal).withDensity
      (fun t => ENNReal.ofReal (Real.exp (qf m v m' v' t))) := by
  have h1 : v.toNNReal ≠ 0 := by simpa using hv
  have h2 : v'.toNNReal ≠ 0 := by simpa using hv'
  have hm : Measurable fun t => ENNReal.ofReal (Real.exp (qf m v m' v' t)) :=
    (Real.measurable_exp.comp (measurable_qf m v m' v')).ennreal_ofReal
  rw [gaussianReal_of_var_ne_zero _ h1, gaussianReal_of_var_ne_zero _ h2,
    ← withDensity_mul _ (measurable_gaussianPDF _ _) hm]
  congr 1
  funext t
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_eq_mul_exp_qf hv hv']

/-- The log-likelihood-ratio increment of one observation `t` after history `h`: zero once
halted, otherwise the Gaussian log density ratio at the queried type. -/
def stepLLR (S : GSampler X) (μ v μ' v' : X → ℝ) (h : List ℝ) (t : ℝ) : ℝ :=
  if halted S h then 0
  else qf (μ (S.next h)) (v (S.next h)) (μ' (S.next h)) (v' (S.next h)) t

/-- **Log-likelihood ratio of the transcript** between `(μ, v)` and `(μ', v')`: the sum of the
Gaussian log density ratios along the realized queries up to stopping. -/
def llrL (S : GSampler X) (μ v μ' v' : X → ℝ) : List ℝ → ℝ
  | [] => 0
  | t :: h => llrL S μ v μ' v' h + stepLLR S μ v μ' v' h t

lemma measurable_stepLLR (S : GSampler X) (μ v μ' v' : X → ℝ) (n : ℕ) :
    Measurable fun p : (Fin n → ℝ) × ℝ => stepLLR S μ v μ' v' (List.ofFn p.1) p.2 := by
  unfold stepLLR
  exact measurable_step S n (a := fun _ => (0 : ℝ))
    (f := fun q => qf (μ q.2) (v q.2) (μ' q.2) (v' q.2) q.1) measurable_const
    (fun x => measurable_qf (μ x) (v x) (μ' x) (v' x))

lemma llrL_ofFn_succ (S : GSampler X) (μ v μ' v' : X → ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    llrL S μ v μ' v' (List.ofFn y) = llrL S μ v μ' v' (List.ofFn (Fin.tail y))
      + stepLLR S μ v μ' v' (List.ofFn (Fin.tail y)) (y 0) := by
  rw [ofFn_eq n y]; rfl

lemma measurable_llr (S : GSampler X) (μ v μ' v' : X → ℝ) :
    ∀ n, Measurable fun y : Fin n → ℝ => llrL S μ v μ' v' (List.ofFn y)
  | 0 => by simp [llrL]
  | n + 1 => by
    simp_rw [llrL_ofFn_succ]
    exact ((measurable_llr S μ v μ' v' n).comp (measurable_tail n)).add
      ((measurable_stepLLR S μ v μ' v' n).comp
        ((measurable_tail n).prodMk (measurable_pi_apply 0)))

lemma stepM_eq_withDensity (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (h : List ℝ) :
    stepM S μ v h = (stepM S μ' v' h).withDensity
      (fun t => ENNReal.ofReal (Real.exp (stepLLR S μ v μ' v' h t))) := by
  unfold stepM stepLLR
  cases hh : halted S h
  · simp only [Bool.false_eq_true, ite_false]
    exact gaussianReal_eq_withDensity (hv _) (hv' _)
  · have : (fun _ : ℝ => ENNReal.ofReal (Real.exp 0)) = 1 := by funext; simp
    simp only [ite_true, this, withDensity_one]

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : Measure α) {φ : α → β} (hφ : Measurable φ) {F : β → ℝ≥0∞} (hF : Measurable F) :
    (m.withDensity (fun a => F (φ a))).map φ = (m.map φ).withDensity F := by
  ext s hs
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs,
    setLIntegral_map hs hF hφ]

/-- **Explicit density of the transcript law.**  For positive variances, the law of the
transcript under `(μ, v)` has density `exp (llrL)` with respect to its law under `(μ', v')`,
where `llrL` is the sum of the Gaussian log density ratios along the realized queries. -/
theorem law_eq_withDensity (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) :
    ∀ n, law S μ v n = (law S μ' v' n).withDensity
      (fun y => ENNReal.ofReal (Real.exp (llrL S μ v μ' v' (List.ofFn y))))
  | 0 => by
    have : (fun y : Fin 0 → ℝ =>
        ENNReal.ofReal (Real.exp (llrL S μ v μ' v' (List.ofFn y)))) = 1 := by
      funext y; simp [llrL]
    rw [this, withDensity_one]; rfl
  | n + 1 => by
    have ih := law_eq_withDensity S (μ := μ) (μ' := μ') hv hv' n
    have hg : Measurable (Function.uncurry fun (y' : Fin n → ℝ) (t : ℝ) =>
        ENNReal.ofReal (Real.exp (stepLLR S μ v μ' v' (List.ofFn y') t))) :=
      (Real.measurable_exp.comp (measurable_stepLLR S μ v μ' v' n)).ennreal_ofReal
    have hρ : ∀ k, Measurable fun y : Fin k → ℝ =>
        ENNReal.ofReal (Real.exp (llrL S μ v μ' v' (List.ofFn y))) := fun k =>
      (Real.measurable_exp.comp (measurable_llr S μ v μ' v' k)).ennreal_ofReal
    have hk : kern S μ v n = (kern S μ' v' n).withDensity (fun y' t =>
        ENNReal.ofReal (Real.exp (stepLLR S μ v μ' v' (List.ofFn y') t))) := by
      ext y' : 1
      rw [Kernel.withDensity_apply _ hg, kern_apply, kern_apply, stepM_eq_withDensity S hv hv']
    have : IsSFiniteKernel ((kern S μ' v' n).withDensity (fun y' t =>
        ENNReal.ofReal (Real.exp (stepLLR S μ v μ' v' (List.ofFn y') t)))) := by
      rw [← hk]; infer_instance
    rw [law_succ, law_succ, ← map_withDensity_comp _ (measurable_cons n) (hρ (n + 1)), hk]
    conv_lhs => rw [ih]
    rw [Measure.withDensity_compProd_withDensity (hρ n) hg]
    congr 2
    funext p
    rw [List.ofFn_cons, llrL, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-! ### Counts and the Wald identity -/

open scoped Classical in
/-- Number of queries of type `x` made before halting along the history. -/
def cnt (S : GSampler X) (x : X) : List ℝ → ℕ
  | [] => 0
  | _ :: h => cnt S x h + if halted S h = false ∧ S.next h = x then 1 else 0

/-- Number of observations taken before halting (`τ ∧ n` for a history of length `n`). -/
def time (S : GSampler X) : List ℝ → ℕ
  | [] => 0
  | _ :: h => time S h + if halted S h then 0 else 1

/-- Histories of length `n` at which the sampler has not halted and queries `x` next. -/
def qset (S : GSampler X) (n : ℕ) (x : X) : Set (Fin n → ℝ) :=
  {y | halted S (List.ofFn y) = false ∧ S.next (List.ofFn y) = x}

lemma measurableSet_qset (S : GSampler X) (n : ℕ) (x : X) : MeasurableSet (qset S n x) := by
  have : qset S n x = (hset S n)ᶜ ∩ (fun y : Fin n → ℝ => S.next (List.ofFn y)) ⁻¹' {x} := by
    ext y; simp [qset, hset]
  rw [this]
  exact (measurableSet_hset S n).compl.inter (S.meas_next n (measurableSet_singleton x))

lemma cnt_ofFn_succ (S : GSampler X) (x : X) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    (cnt S x (List.ofFn y) : ℝ) = cnt S x (List.ofFn (Fin.tail y))
      + (qset S n x).indicator (fun _ => (1 : ℝ)) (Fin.tail y) := by
  classical
  rw [ofFn_eq n y, cnt]
  by_cases h : Fin.tail y ∈ qset S n x
  · have h' : halted S (List.ofFn (Fin.tail y)) = false ∧ S.next (List.ofFn (Fin.tail y)) = x := h
    simp [h, h']
  · have h' : ¬ (halted S (List.ofFn (Fin.tail y)) = false ∧
        S.next (List.ofFn (Fin.tail y)) = x) := h
    simp [h, h']

lemma measurable_cnt (S : GSampler X) (x : X) :
    ∀ n, Measurable fun y : Fin n → ℝ => (cnt S x (List.ofFn y) : ℝ)
  | 0 => by simp [cnt]
  | n + 1 => by
    simp_rw [cnt_ofFn_succ]
    exact ((measurable_cnt S x n).comp (measurable_tail n)).add
      ((measurable_const.indicator (measurableSet_qset S n x)).comp (measurable_tail n))

lemma cnt_le_length (S : GSampler X) (x : X) : ∀ h : List ℝ, cnt S x h ≤ h.length
  | [] => by simp [cnt]
  | _ :: h => by
    have := cnt_le_length S x h
    rw [cnt, List.length_cons]
    split_ifs <;> omega

lemma integrable_cnt (S : GSampler X) (μ v : X → ℝ) (x : X) (n : ℕ) :
    Integrable (fun y : Fin n → ℝ => (cnt S x (List.ofFn y) : ℝ)) (law S μ v n) := by
  refine ⟨(measurable_cnt S x n).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := n) (ae_of_all _ fun y => ?_)⟩
  rw [Real.norm_natCast]
  have := cnt_le_length S x (List.ofFn y)
  rw [List.length_ofFn] at this
  exact_mod_cast this

/-- Expected number of queries of type `x` before `τ ∧ n`. -/
def expCnt (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∫ y, (cnt S x (List.ofFn y) : ℝ) ∂(law S μ v n)

lemma integrable_comp_tail (S : GSampler X) (μ v : X → ℝ) (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f (law S μ v n)) :
    Integrable (fun y : Fin (n + 1) → ℝ => f (Fin.tail y)) (law S μ v (n + 1)) := by
  rw [← law_map_tail S μ v n] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable (measurable_tail n).aemeasurable).1 hf

lemma integral_comp_tail (S : GSampler X) (μ v : X → ℝ) (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (law S μ v n)) :
    ∫ y, f (Fin.tail y) ∂(law S μ v (n + 1)) = ∫ y, f y ∂(law S μ v n) := by
  conv_rhs => rw [← law_map_tail S μ v n]
  rw [← law_map_tail S μ v n] at hf
  exact (integral_map (measurable_tail n).aemeasurable hf).symm

lemma expCnt_succ (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (x : X) :
    expCnt S μ v (n + 1) x = expCnt S μ v n x + (law S μ v n).real (qset S n x) := by
  have hi : Integrable ((qset S n x).indicator fun _ => (1 : ℝ)) (law S μ v n) :=
    (integrable_const _).indicator (measurableSet_qset S n x)
  unfold expCnt
  simp_rw [cnt_ofFn_succ]
  rw [integral_add (integrable_comp_tail S μ v n (integrable_cnt S μ v x n))
      (integrable_comp_tail S μ v n hi),
    integral_comp_tail S μ v n (integrable_cnt S μ v x n).aestronglyMeasurable,
    integral_comp_tail S μ v n hi.aestronglyMeasurable,
    integral_indicator_const _ (measurableSet_qset S n x), smul_eq_mul, mul_one]

lemma expCnt_nonneg (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (x : X) : 0 ≤ expCnt S μ v n x :=
  integral_nonneg fun _ => Nat.cast_nonneg _

lemma qf_eq (m v m' v' : ℝ) : qf m v m' v' = fun t =>
    (1 / 2 * Real.log (v' / v) - m ^ 2 / (2 * v) + m' ^ 2 / (2 * v'))
      + (m / v - m' / v') * t + (-(1 / (2 * v)) + 1 / (2 * v')) * t ^ 2 := by
  funext t; unfold qf; ring

lemma integral_sq_gaussianReal (m : ℝ) (w : ℝ≥0) :
    ∫ t, t ^ 2 ∂(gaussianReal m w) = w + m ^ 2 := by
  have h := variance_eq_sub (μ := gaussianReal m w) (memLp_id_gaussianReal' 2 (by simp))
  rw [variance_id_gaussianReal] at h
  have h1 : (gaussianReal m w)[id ^ 2] = ∫ t, t ^ 2 ∂(gaussianReal m w) := rfl
  have h2 : (gaussianReal m w)[id] = m := integral_id_gaussianReal
  rw [h1, h2] at h
  linarith

lemma integrable_qf (m v m' v' m₀ : ℝ) (w : ℝ≥0) :
    Integrable (qf m v m' v') (gaussianReal m₀ w) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal m₀ w) :=
    (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl
  have hsq : Integrable (fun t : ℝ => t ^ 2) (gaussianReal m₀ w) :=
    (memLp_id_gaussianReal' 2 (by simp)).integrable_sq
  rw [qf_eq]
  exact ((integrable_const _).add (hid.const_mul _)).add (hsq.const_mul _)

/-- The expected log density ratio is the closed-form Gaussian KL divergence `gaussKL`. -/
lemma integral_qf {m v m' v' : ℝ} (hv : 0 < v) (hv' : 0 < v') :
    ∫ t, qf m v m' v' t ∂(gaussianReal m v.toNNReal) = gaussKL m v m' v' := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal m v.toNNReal) :=
    (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl
  have hsq : Integrable (fun t : ℝ => t ^ 2) (gaussianReal m v.toNNReal) :=
    (memLp_id_gaussianReal' 2 (by simp)).integrable_sq
  simp only [qf_eq]
  set A := 1 / 2 * Real.log (v' / v) - m ^ 2 / (2 * v) + m' ^ 2 / (2 * v') with hA
  set B := m / v - m' / v' with hB
  set C := -(1 / (2 * v)) + 1 / (2 * v') with hC
  have iB : Integrable (fun t : ℝ => B * t) (gaussianReal m v.toNNReal) := hid.const_mul _
  have iC : Integrable (fun t : ℝ => C * t ^ 2) (gaussianReal m v.toNNReal) := hsq.const_mul _
  have iA : Integrable (fun t : ℝ => A + B * t) (gaussianReal m v.toNNReal) :=
    (integrable_const _).add iB
  rw [integral_add iA iC, integral_add (integrable_const _) iB, integral_const_mul,
    integral_const_mul, integral_sq_gaussianReal, integral_id_gaussianReal, integral_const,
    probReal_univ, one_smul, Real.coe_toNNReal _ hv.le, hA, hB, hC]
  unfold gaussKL
  field_simp
  ring

lemma integrable_stepLLR (S : GSampler X) (μ v μ' v' : X → ℝ) (h : List ℝ) :
    Integrable (stepLLR S μ v μ' v' h) (stepM S μ v h) := by
  unfold stepLLR stepM
  cases hh : halted S h
  · simp only [Bool.false_eq_true, ite_false]
    exact integrable_qf _ _ _ _ _ _
  · simp only [ite_true]
    exact integrable_zero _ _ _

lemma integral_stepLLR (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (h : List ℝ) :
    ∫ t, stepLLR S μ v μ' v' h t ∂(stepM S μ v h) =
      if halted S h then 0
      else gaussKL (μ (S.next h)) (v (S.next h)) (μ' (S.next h)) (v' (S.next h)) := by
  unfold stepLLR stepM
  cases hh : halted S h
  · simp only [Bool.false_eq_true, ite_false]
    exact integral_qf (hv _) (hv' _)
  · simp

/-- A constant bounding the expected absolute one-step log-likelihood ratio. -/
def stepBound (μ v μ' v' : X → ℝ) : ℝ :=
  ∑ x, ∫ t, ‖qf (μ x) (v x) (μ' x) (v' x) t‖ ∂(gaussianReal (μ x) (v x).toNNReal)

lemma integral_norm_stepLLR_le (S : GSampler X) (μ v μ' v' : X → ℝ) (h : List ℝ) :
    ∫ t, ‖stepLLR S μ v μ' v' h t‖ ∂(stepM S μ v h) ≤ stepBound μ v μ' v' := by
  have h0 : ∀ x ∈ (univ : Finset X),
      0 ≤ ∫ t, ‖qf (μ x) (v x) (μ' x) (v' x) t‖ ∂(gaussianReal (μ x) (v x).toNNReal) :=
    fun x _ => integral_nonneg fun _ => norm_nonneg _
  unfold stepLLR stepM stepBound
  cases hh : halted S h
  · simp only [Bool.false_eq_true, ite_false]
    exact single_le_sum h0 (mem_univ (S.next h))
  · simp only [ite_true, norm_zero, integral_zero]
    exact sum_nonneg h0

lemma klstep_eq_sum (S : GSampler X) (n : ℕ) (K : X → ℝ) (y : Fin n → ℝ) :
    (if halted S (List.ofFn y) then 0 else K (S.next (List.ofFn y))) =
      ∑ x, (qset S n x).indicator (fun _ => K x) y := by
  classical
  cases hh : halted S (List.ofFn y)
  · simp only [Bool.false_eq_true, ite_false]
    rw [sum_eq_single (S.next (List.ofFn y))]
    · simp [qset, hh]
    · intro x _ hx
      simp [qset, hh, Ne.symm hx]
    · simp
  · simp [qset, hh]

/-- The last observation's log-likelihood ratio: integrability and expectation. -/
lemma step_wald (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) :
    Integrable (fun y : Fin (n + 1) → ℝ =>
        stepLLR S μ v μ' v' (List.ofFn (Fin.tail y)) (y 0)) (law S μ v (n + 1)) ∧
      ∫ y, stepLLR S μ v μ' v' (List.ofFn (Fin.tail y)) (y 0) ∂(law S μ v (n + 1)) =
        ∑ x, (law S μ v n).real (qset S n x) * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hg' := measurable_stepLLR S μ v μ' v' n
  have hF : Measurable fun y : Fin (n + 1) → ℝ =>
      stepLLR S μ v μ' v' (List.ofFn (Fin.tail y)) (y 0) :=
    hg'.comp ((measurable_tail n).prodMk (measurable_pi_apply 0))
  have hint' : Integrable (fun p : (Fin n → ℝ) × ℝ => stepLLR S μ v μ' v' (List.ofFn p.1) p.2)
      ((law S μ v n) ⊗ₘ (kern S μ v n)) := by
    refine (Measure.integrable_compProd_iff hg'.aestronglyMeasurable).2
      ⟨ae_of_all _ fun y' => ?_, ?_, ?_⟩
    · rw [kern_apply]; exact integrable_stepLLR S μ v μ' v' _
    · exact (hg'.norm.stronglyMeasurable.integral_kernel_prod_right'
        (κ := kern S μ v n)).aestronglyMeasurable
    · refine HasFiniteIntegral.of_bounded (C := stepBound μ v μ' v') (ae_of_all _ fun y' => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), kern_apply]
      exact integral_norm_stepLLR_le S μ v μ' v' _
  constructor
  · rw [law_succ]
    refine (integrable_map_measure hF.aestronglyMeasurable
      (measurable_cons n).aemeasurable).2 ?_
    refine hint'.congr (ae_of_all _ fun p => ?_)
    simp [Fin.tail_cons]
  · rw [law_succ, integral_map (measurable_cons n).aemeasurable hF.aestronglyMeasurable]
    simp only [Fin.tail_cons, Fin.cons_zero]
    rw [Measure.integral_compProd hint']
    simp_rw [kern_apply, integral_stepLLR S hv hv',
      klstep_eq_sum S n (fun x => gaussKL (μ x) (v x) (μ' x) (v' x))]
    rw [integral_finsetSum _ fun x _ =>
      (integrable_const _).indicator (measurableSet_qset S n x)]
    simp_rw [integral_indicator_const _ (measurableSet_qset S n _), smul_eq_mul]

theorem wald_aux (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) :
    ∀ n, Integrable (fun y : Fin n → ℝ => llrL S μ v μ' v' (List.ofFn y)) (law S μ v n) ∧
      ∫ y, llrL S μ v μ' v' (List.ofFn y) ∂(law S μ v n) =
        ∑ x, expCnt S μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x)
  | 0 => by
    constructor
    · simp [llrL]
    · simp [llrL, expCnt, cnt]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := wald_aux S (μ := μ) (μ' := μ') hv hv' n
    obtain ⟨s1, s2⟩ := step_wald S (μ := μ) (μ' := μ') hv hv' n
    have h1 := integrable_comp_tail S μ v n ih1
    constructor
    · simp_rw [llrL_ofFn_succ]
      exact h1.add s1
    · simp_rw [llrL_ofFn_succ]
      rw [integral_add h1 s1, integral_comp_tail S μ v n ih1.aestronglyMeasurable, ih2, s2]
      simp_rw [expCnt_succ, add_mul]
      rw [sum_add_distrib]

/-- The transcript log-likelihood ratio is integrable under the first parameter. -/
theorem integrable_llr (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) :
    Integrable (fun y : Fin n → ℝ => llrL S μ v μ' v' (List.ofFn y)) (law S μ v n) :=
  (wald_aux S hv hv' n).1

/-- **Wald identity for the stopped Gaussian likelihood ratio.**
`E_{μ,v}[log-likelihood ratio at τ ∧ n] = ∑ₓ E_{μ,v}[Nₓ(τ ∧ n)] · KL(N(μₓ, vₓ) ‖ N(μ'ₓ, v'ₓ))`,
with the closed form `gaussKL` for the Gaussian divergence. -/
theorem wald_identity (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) :
    ∫ y, llrL S μ v μ' v' (List.ofFn y) ∂(law S μ v n) =
      ∑ x, expCnt S μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) :=
  (wald_aux S hv hv' n).2

/-! ### Transportation inequality -/

lemma law_absolutelyContinuous (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) : law S μ v n ≪ law S μ' v' n := by
  rw [law_eq_withDensity S (μ := μ) (μ' := μ') hv hv' n]
  exact withDensity_absolutelyContinuous _ _

/-- Mathlib's log-likelihood ratio of the two transcript laws is the explicit `llrL`. -/
lemma llr_ae_eq (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) :
    llr (law S μ v n) (law S μ' v' n) =ᵐ[law S μ v n]
      fun y => llrL S μ v μ' v' (List.ofFn y) := by
  have hm : Measurable fun y : Fin n → ℝ =>
      ENNReal.ofReal (Real.exp (llrL S μ v μ' v' (List.ofFn y))) :=
    (Real.measurable_exp.comp (measurable_llr S μ v μ' v' n)).ennreal_ofReal
  have h1 := Measure.rnDeriv_withDensity (law S μ' v' n) hm
  rw [← law_eq_withDensity S (μ := μ) (μ' := μ') hv hv' n] at h1
  filter_upwards [(law_absolutelyContinuous S hv hv' n).ae_eq h1] with y hy
  rw [llr, hy, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

/-- **Transportation inequality at a finite horizon.**  For every measurable event `E` of the
transcript at horizon `n` (in particular every event determined by the stopped history),
`kl(P_{μ,v}(E), P_{μ',v'}(E)) ≤ ∑ₓ E_{μ,v}[Nₓ(τ ∧ n)] · KL(N(μₓ, vₓ) ‖ N(μ'ₓ, v'ₓ))`. -/
theorem gauss_transport_finite (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) :
    bkl ((law S μ v n).real E) ((law S μ' v' n).real E) ≤
      ∑ x, expCnt S μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hae := llr_ae_eq S (μ := μ) (μ' := μ') hv hv' n
  have hint : Integrable (llr (law S μ v n) (law S μ' v' n)) (law S μ v n) :=
    (integrable_congr hae).2 (integrable_llr S hv hv' n)
  have h := bkl_le_integral_llr _ _ (law_absolutelyContinuous S hv hv' n) hint hE
  rwa [integral_congr_ae hae, wald_identity S hv hv' n] at h

/-- The same inequality with the probabilities computed on the noise space: `E` is an event of
the transcript, `hist S μ v n` the transcript computed from i.i.d. standard Gaussian noise. -/
theorem gauss_transport_noise (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) :
    bkl ((Measure.pi fun _ : Fin n => gaussianReal 0 1).real (hist S μ v n ⁻¹' E))
        ((Measure.pi fun _ : Fin n => gaussianReal 0 1).real (hist S μ' v' n ⁻¹' E)) ≤
      ∑ x, (∫ ω, (cnt S x (List.ofFn (hist S μ v n ω)) : ℝ)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) *
        gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have h := gauss_transport_finite S (μ := μ) (μ' := μ') hv hv' n hE
  have e1 : ∀ m w : X → ℝ, (law S m w n).real E =
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real (hist S m w n ⁻¹' E) := fun m w => by
    rw [← law_eq_map_hist S m w n, map_measureReal_apply (measurable_hist S m w n) hE]
  have e3 : ∀ x, expCnt S μ v n x = ∫ ω, (cnt S x (List.ofFn (hist S μ v n ω)) : ℝ)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := fun x => by
    unfold expCnt
    rw [← law_eq_map_hist S μ v n]
    exact integral_map (measurable_hist S μ v n).aemeasurable
      (measurable_cnt S x n).aestronglyMeasurable
  rw [e1, e1] at h
  simp_rw [e3] at h
  exact h

lemma gaussKL_nonneg {m v m' v' : ℝ} (hv : 0 < v) (hv' : 0 < v') : 0 ≤ gaussKL m v m' v' :=
  (nkl_nonneg hv m m').trans (gaussKL_ge_nkl hv hv')

lemma continuousAt_bkl_left {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousAt (fun x => bkl x q) p := by
  unfold bkl
  have h1 : ContinuousAt (fun x : ℝ => Real.log (x / q)) p := by
    by_cases hq : q = 0
    · simp [hq]; exact continuousAt_const
    · exact (continuousAt_id.div_const q).log (div_ne_zero hp0.ne' hq)
  have h2 : ContinuousAt (fun x : ℝ => Real.log ((1 - x) / (1 - q))) p := by
    by_cases hq : 1 - q = 0
    · simp [hq]; exact continuousAt_const
    · have h3 : ContinuousAt (fun x : ℝ => 1 - x) p := continuousAt_const.sub continuousAt_id
      have h4 : (1 : ℝ) - p ≠ 0 := by linarith
      exact (h3.div_const _).log (div_ne_zero h4 hq)
  exact (continuousAt_id.mul h1).add ((continuousAt_const.sub continuousAt_id).mul h2)

/-- If an event has probability above `p > δ` under the first parameter and at most `δ < 1`
under the second, the transported information is at least `kl(p, δ)`. -/
lemma bkl_le_of_event (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) {p δ : ℝ}
    (hδ0 : 0 < δ) (hδp : δ ≤ p) (hp1 : p < 1) (hp : p ≤ (law S μ v n).real E)
    (hq : (law S μ' v' n).real E ≤ δ) :
    bkl p δ ≤ ∑ x, expCnt S μ v n x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hP1 : (law S μ v n).real E ≤ 1 := measureReal_le_one
  have hQ0 : 0 < (law S μ' v' n).real E := by
    by_contra hcon
    have h0 : (law S μ' v' n).real E = 0 := le_antisymm (not_lt.1 hcon) measureReal_nonneg
    have h1 : law S μ' v' n E = 0 := (measureReal_eq_zero_iff (measure_ne_top _ E)).1 h0
    have h2 : (law S μ v n).real E = 0 := by
      simp [Measure.real, law_absolutelyContinuous S hv hv' n h1]
    linarith
  have h1 : bkl p δ ≤ bkl ((law S μ v n).real E) δ :=
    bkl_mono_left hδ0 hδp hp1 hp hP1
  have h2 : bkl ((law S μ v n).real E) δ ≤
      bkl ((law S μ v n).real E) ((law S μ' v' n).real E) :=
    bkl_mono_right (by linarith) hP1 hδ0 (by linarith) hQ0 (by linarith)
      (mul_nonneg (sub_nonneg.2 hq) (by linarith))
  exact (h1.trans h2).trans (gauss_transport_finite S hv hv' n hE)

/-- **Transportation inequality for an unbounded stopping time.**  `E n` is the horizon-`n`
version of an event of the stopped run (for instance "halted by `n` with answer `a`").  If its
probability under `(μ, v)` approaches at least `1 - δ` along the horizons, its probability under
`(μ', v')` is at most `δ` at every horizon, and `N x` bounds the expected counts
`E_{μ,v}[Nₓ(τ ∧ n)]` uniformly in `n` (finite expected stopping time), then
`kl(1 - δ, δ) ≤ ∑ₓ Nₓ · KL(N(μₓ, vₓ) ‖ N(μ'ₓ, v'ₓ))`. -/
theorem gauss_transport (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (E : ∀ n, Set (Fin n → ℝ)) (hE : ∀ n, MeasurableSet (E n))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) {N : X → ℝ}
    (hP : ∀ η > 0, ∃ n, 1 - δ - η ≤ (law S μ v n).real (E n))
    (hQ : ∀ n, (law S μ' v' n).real (E n) ≤ δ)
    (hN : ∀ n x, expCnt S μ v n x ≤ N x) :
    bkl (1 - δ) δ ≤ ∑ x, N x * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have hcont : Tendsto (fun η : ℝ => bkl (1 - δ - η) δ) (𝓝[>] 0) (𝓝 (bkl (1 - δ) δ)) := by
    have h1 : ContinuousAt (fun x => bkl x δ) (1 - δ) :=
      continuousAt_bkl_left (by linarith) (by linarith)
    have h2 : Tendsto (fun η : ℝ => 1 - δ - η) (𝓝 0) (𝓝 (1 - δ)) := by
      have : Tendsto (fun η : ℝ => 1 - δ - η) (𝓝 0) (𝓝 (1 - δ - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      simpa using this
    exact (h1.tendsto.comp h2).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - 2 * δ by linarith)] with η hη
  obtain ⟨n, hn⟩ := hP η hη.1
  refine (bkl_le_of_event S hv hv' n (hE n) hδ0 (by linarith [hη.2]) (by linarith [hη.1]) hn
    (hQ n)).trans ?_
  exact sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_right (hN n x) (gaussKL_nonneg (hv x) (hv' x))

/-! ### Stopping time, answers -/

lemma sum_cnt (S : GSampler X) : ∀ h : List ℝ, ∑ x, cnt S x h = time S h
  | [] => by simp [cnt, time]
  | _ :: h => by
    classical
    simp only [cnt, time, sum_add_distrib, sum_cnt S h]
    congr 1
    cases hh : halted S h <;> simp

lemma time_le_length (S : GSampler X) : ∀ h : List ℝ, time S h ≤ h.length
  | [] => by simp [time]
  | _ :: h => by
    have := time_le_length S h
    rw [time, List.length_cons]
    split_ifs <;> omega

/-- Expected number of observations before `τ ∧ n`. -/
def expTime (S : GSampler X) (μ v : X → ℝ) (n : ℕ) : ℝ :=
  ∫ y, (time S (List.ofFn y) : ℝ) ∂(law S μ v n)

lemma sum_expCnt (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    ∑ x, expCnt S μ v n x = expTime S μ v n := by
  unfold expCnt expTime
  rw [← integral_finsetSum _ fun x _ => integrable_cnt S μ v x n]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [← sum_cnt S (List.ofFn y)]
  push_cast
  rfl

lemma expTime_nonneg (S : GSampler X) (μ v : X → ℝ) (n : ℕ) : 0 ≤ expTime S μ v n :=
  integral_nonneg fun _ => Nat.cast_nonneg _

/-- Expected stopping time of the unbounded run, `E_{μ,v}[τ] = sup_n E_{μ,v}[τ ∧ n]`, in
`[0, ∞]`. -/
def expTau (S : GSampler X) (μ v : X → ℝ) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal (expTime S μ v n)

lemma expTime_le_of_ne_top (S : GSampler X) (μ v : X → ℝ) (h : expTau S μ v ≠ ⊤) (n : ℕ) :
    expTime S μ v n ≤ (expTau S μ v).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal h).1 (le_iSup (fun n => ENNReal.ofReal (expTime S μ v n)) n)

/-- A decision rule: the answer read off the history at the stopping time. -/
structure GDecision (A : Type*) [MeasurableSpace A] where
  /-- the answer returned at a history -/
  dec : List ℝ → A
  meas_dec : ∀ k : ℕ, Measurable fun y : Fin k → ℝ => dec (List.ofFn y)

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The answer returned at the stopping time, read from a (possibly longer) transcript. -/
def decAt (S : GSampler X) (D : GDecision A) : List ℝ → A
  | [] => D.dec []
  | t :: h => if halted S h then decAt S D h else D.dec (t :: h)

/-- The horizon-`n` event "the sampler has halted and returned `a`". -/
def ansSet (S : GSampler X) (D : GDecision A) (a : A) (n : ℕ) : Set (Fin n → ℝ) :=
  {y | halted S (List.ofFn y) = true ∧ decAt S D (List.ofFn y) = a}

lemma measurableSet_decAt (S : GSampler X) (D : GDecision A) (a : A) :
    ∀ n, MeasurableSet {y : Fin n → ℝ | decAt S D (List.ofFn y) = a}
  | 0 => by
    have : {y : Fin 0 → ℝ | decAt S D (List.ofFn y) = a} = {_y | D.dec [] = a} := by
      ext y; simp [decAt]
    rw [this]; exact MeasurableSet.const _
  | n + 1 => by
    have : {y : Fin (n + 1) → ℝ | decAt S D (List.ofFn y) = a} =
        ((fun y => Fin.tail y) ⁻¹' (hset S n) ∩
          (fun y => Fin.tail y) ⁻¹' {y : Fin n → ℝ | decAt S D (List.ofFn y) = a}) ∪
        (((fun y => Fin.tail y) ⁻¹' (hset S n))ᶜ ∩
          (fun y : Fin (n + 1) → ℝ => D.dec (List.ofFn y)) ⁻¹' {a}) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_compl_iff, Set.mem_singleton_iff, hset]
      conv_lhs => rw [ofFn_eq n y, decAt, ← ofFn_eq n y]
      cases hh : halted S (List.ofFn (Fin.tail y)) <;> simp
    rw [this]
    have h1 := (measurable_tail n) (measurableSet_hset S n)
    exact (h1.inter ((measurable_tail n) (measurableSet_decAt S D a n))).union
      (h1.compl.inter (D.meas_dec (n + 1) (measurableSet_singleton a)))

lemma measurableSet_ansSet (S : GSampler X) (D : GDecision A) (a : A) (n : ℕ) :
    MeasurableSet (ansSet S D a n) :=
  (measurableSet_hset S n).inter (measurableSet_decAt S D a n)

/-! ### Monotonicity in the horizon

The quantities of the unbounded run are suprema over the horizon; these lemmas show that the
horizon-`n` values are nondecreasing, so the suprema are limits. -/

lemma expCnt_mono (S : GSampler X) (μ v : X → ℝ) (x : X) :
    Monotone fun n => expCnt S μ v n x :=
  monotone_nat_of_le_succ fun n => by
    rw [expCnt_succ]
    linarith [measureReal_nonneg (μ := law S μ v n) (s := qset S n x)]

lemma expTime_mono (S : GSampler X) (μ v : X → ℝ) : Monotone fun n => expTime S μ v n := by
  intro m n h
  simp only [← sum_expCnt]
  exact sum_le_sum fun x _ => expCnt_mono S μ v x h

lemma law_ansSet_mono (S : GSampler X) (D : GDecision A) (a : A) (μ v : X → ℝ) :
    Monotone fun n => (law S μ v n).real (ansSet S D a n) :=
  monotone_nat_of_le_succ fun n => by
    have hsub : (fun y : Fin (n + 1) → ℝ => (Fin.tail y : Fin n → ℝ)) ⁻¹' (ansSet S D a n) ⊆
        ansSet S D a (n + 1) := by
      intro y hy
      obtain ⟨h1, h2⟩ := hy
      refine ⟨?_, ?_⟩
      · rw [ofFn_eq n y, halted, h1]; rfl
      · rw [ofFn_eq n y, decAt, h1]; simpa using h2
    calc (law S μ v n).real (ansSet S D a n)
        = (law S μ v (n + 1)).real
            ((fun y : Fin (n + 1) → ℝ => (Fin.tail y : Fin n → ℝ)) ⁻¹' (ansSet S D a n)) := by
          rw [← law_map_tail S μ v n,
            map_measureReal_apply (measurable_tail n) (measurableSet_ansSet S D a n)]
      _ ≤ _ := measureReal_mono hsub

/-! ### `thm:v34-converse` for the sampler model -/

section Converse

variable {U : Type*} {Z : Type*}

/-- Passage `η ↓ 0` in the first argument of the binary divergence. -/
lemma bkl_le_of_forall_small {δ K : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (h : ∀ η, 0 < η → η < 1 - 2 * δ → bkl (1 - δ - η) δ ≤ K) : bkl (1 - δ) δ ≤ K := by
  have hcont : Tendsto (fun η : ℝ => bkl (1 - δ - η) δ) (𝓝[>] 0) (𝓝 (bkl (1 - δ) δ)) := by
    have h1 : ContinuousAt (fun x => bkl x δ) (1 - δ) :=
      continuousAt_bkl_left (by linarith) (by linarith)
    have h2 : Tendsto (fun η : ℝ => 1 - δ - η) (𝓝 0) (𝓝 (1 - δ)) := by
      have : Tendsto (fun η : ℝ => 1 - δ - η) (𝓝 0) (𝓝 (1 - δ - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      simpa using this
    exact (h1.tendsto.comp h2).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - 2 * δ by linarith)] with η hη
  exact h η hη.1 hη.2

/-- **Unknown-variance nuisance-KL lower bound for one correct answer
(`thm:v34-converse`, finite-confidence part), for the sampler model.**
`S` is an adaptive sampler with decision rule `D`; `(μ, v)` are the true query means and
variances; `Hs z` are the strict invalidating components of the action `astar` and `Hc z` the
closed ones.  Hypotheses on the procedure only:
* `hcorrect`: under the truth the probability of halting with answer `astar` is at least
  `1 - δ` (as a supremum over horizons);
* `hwrong`: under every strict alternative mean `pred · u` with arbitrary positive variances
  the probability of halting with answer `astar` is at most `δ` at every horizon.
Conclusion: `E_{μ,v}[τ] ≥ kl(1 - δ, δ) / C_{a⋆}^*(μ, v)` in `[0, ∞]`. -/
theorem v34_converse [TopologicalSpace U] (S : GSampler X) (D : GDecision A) (astar : A)
    (J : Finset Z) (hJ : J.Nonempty) (Hc Hs : Z → Set U) (pred : X → U → ℝ)
    (hpred : ∀ x, Continuous (pred x)) {μ v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hne : ∀ z ∈ J, (Hc z).Nonempty) (hcl : ∀ z ∈ J, Hc z ⊆ closure (Hs z))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (hcorrect : ∀ η > 0, ∃ n, 1 - δ - η ≤ (law S μ v n).real (ansSet S D astar n))
    (hwrong : ∀ z ∈ J, ∀ u ∈ Hs z, ∀ s : X → ℝ, (∀ x, 0 < s x) → ∀ n,
      (law S (fun x => pred x u) s n).real (ansSet S D astar n) ≤ δ)
    (hCpos : 0 < actGameStar J hJ Hc pred μ v) :
    ENNReal.ofReal (klBin (1 - δ) δ / actGameStar J hJ Hc pred μ v) ≤ expTau S μ v := by
  by_cases htop : expTau S μ v = ⊤
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
      bkl (1 - δ - η) δ ≤ ∑ x, expCnt S μ v n x * gaussKL (μ x) (v x) (pred x u) (s x) :=
    fun z hz u hu s hs => bkl_le_of_event S (μ' := fun x => pred x u) hv hs n
      (measurableSet_ansSet S D astar n) hδ0 (by linarith) (by linarith) hn
      (hwrong z hz u hu s hs n)
  have hTpos : 0 < expTime S μ v n := by
    rcases (expTime_nonneg S μ v n).eq_or_lt with h0 | h0
    · exfalso
      have hz0 : ∀ x, expCnt S μ v n x = 0 := fun x =>
        (sum_eq_zero_iff_of_nonneg fun x _ => expCnt_nonneg S μ v n x).1
          ((sum_expCnt S μ v n).trans h0.symm) x (mem_univ x)
      obtain ⟨z, hz⟩ := hJ
      have hsne : (Hs z).Nonempty := by
        have := (hne z hz).mono (hcl z hz)
        exact closure_nonempty_iff.1 this
      obtain ⟨u, hu⟩ := hsne
      have := htr z hz u hu (fun _ => 1) (fun _ => one_pos)
      simp only [hz0, zero_mul, sum_const_zero] at this
      linarith
    · exact h0
  have h := (converse_reduction J hJ Hc Hs pred hpred hv (fun x => expCnt_nonneg S μ v n x)
    (sum_expCnt S μ v n) hTpos hne hcl htr
    (fun _ hw => actGame_le_star J hJ Hc pred hw hv) hCpos).2
  rw [div_le_iff₀ hCpos] at h
  exact h.trans (mul_le_mul_of_nonneg_right (expTime_le_of_ne_top S μ v htop n) hCpos.le)

/-- **Identification `C_* = C_{a⋆}^*`** (last step of the proof of `thm:v34-converse`): if every
action other than `astar` is incorrect at the truth (the true parameter lies in one of its
closed invalidating components) then the maximum of `C_a^*` over the action family is attained
at `astar`. -/
theorem v34_Cstar_eq [Fintype A] [Nonempty X] (astar : A) (J : A → Finset Z)
    (hJ : ∀ a, (J a).Nonempty) (H : A → Z → Set U) (pred : X → U → ℝ) {μ v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hinc : ∀ a, a ≠ astar → ∃ z ∈ J a, ∃ θ ∈ H a z, ∀ x, pred x θ = μ x)
    (hpos : 0 ≤ actGameStar (J astar) (hJ astar) (H astar) pred μ v) :
    univ.sup' ⟨astar, mem_univ astar⟩ (fun a => actGameStar (J a) (hJ a) (H a) pred μ v) =
      actGameStar (J astar) (hJ astar) (H astar) pred μ v := by
  classical
  refine le_antisymm (sup'_le _ _ fun a _ => ?_)
    (le_sup' (fun a => actGameStar (J a) (hJ a) (H a) pred μ v) (mem_univ astar))
  by_cases ha : a = astar
  · subst ha; exact le_rfl
  · obtain ⟨z, hz, θ, hθ, hμ⟩ := hinc a ha
    rw [actGameStar_eq_zero_of_mem (J a) (hJ a) (H a) pred hv hz hθ hμ]
    exact hpos

/-- **`thm:v34-converse` / `thm:v34-converse-main` for the sampler model**, with
`C_* = max_a C_a^*(μ, v)` over a finite action family.  `astar` is the unique correct action:
every other action is incorrect at the truth (`hinc`).  For each `δ ∈ (0, 1/2)` the procedure
`(S δ, D δ)` is `δ`-correct in the sense of `hcorrect` and `hwrong` (see `v34_converse`).
Conclusions: `E τ_δ ≥ kl(1 - δ, δ) / C_*` for every `δ ∈ (0, 1/2)`, and
`liminf_{δ ↓ 0} E τ_δ / log (1/δ) ≥ 1 / C_*` in the form: for every `c < 1 / C_*`, eventually
`c log (1/δ) ≤ E τ_δ`. -/
theorem v34_converse_main [TopologicalSpace U] [Fintype A] [Nonempty X] (astar : A)
    (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty) (Hc Hs : A → Z → Set U) (pred : X → U → ℝ)
    (hpred : ∀ x, Continuous (pred x)) {μ v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hne : ∀ z ∈ J astar, (Hc astar z).Nonempty)
    (hcl : ∀ z ∈ J astar, Hc astar z ⊆ closure (Hs astar z))
    (hinc : ∀ a, a ≠ astar → ∃ z ∈ J a, ∃ θ ∈ Hc a z, ∀ x, pred x θ = μ x)
    (hCpos : 0 < univ.sup' ⟨astar, mem_univ astar⟩
      (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v))
    (S : ℝ → GSampler X) (D : ℝ → GDecision A)
    (hcorrect : ∀ δ, 0 < δ → δ < 1 / 2 → ∀ η > 0, ∃ n,
      1 - δ - η ≤ (law (S δ) μ v n).real (ansSet (S δ) (D δ) astar n))
    (hwrong : ∀ δ, 0 < δ → δ < 1 / 2 → ∀ z ∈ J astar, ∀ u ∈ Hs astar z, ∀ s : X → ℝ,
      (∀ x, 0 < s x) → ∀ n,
        (law (S δ) (fun x => pred x u) s n).real (ansSet (S δ) (D δ) astar n) ≤ δ) :
    (∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v)) ≤ expTau (S δ) μ v) ∧
    ∀ c : ℝ, c < 1 / univ.sup' ⟨astar, mem_univ astar⟩
        (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v) →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤ expTau (S δ) μ v := by
  classical
  have hle : actGameStar (J astar) (hJ astar) (Hc astar) pred μ v ≤
      univ.sup' ⟨astar, mem_univ astar⟩ (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v) :=
    le_sup' (fun a => actGameStar (J a) (hJ a) (Hc a) pred μ v) (mem_univ astar)
  have h0 : 0 ≤ actGameStar (J astar) (hJ astar) (Hc astar) pred μ v := by
    obtain ⟨x0⟩ := ‹Nonempty X›
    exact (actGame_nonneg (single_mem_simplex x0).1 hv).trans
      (actGame_le_star (J astar) (hJ astar) (Hc astar) pred (single_mem_simplex x0) hv)
  have heq := v34_Cstar_eq astar J hJ Hc pred hv hinc h0
  rw [heq] at hCpos ⊢
  have hfin : ∀ δ, 0 < δ → δ < 1 / 2 →
      ENNReal.ofReal (klBin (1 - δ) δ / actGameStar (J astar) (hJ astar) (Hc astar) pred μ v)
        ≤ expTau (S δ) μ v := fun δ hδ0 hδ =>
    v34_converse (S δ) (D δ) astar (J astar) (hJ astar) (Hc astar) (Hs astar) pred hpred hv
      hne hcl hδ0 hδ (hcorrect δ hδ0 hδ) (hwrong δ hδ0 hδ) hCpos
  refine ⟨hfin, fun c hc => ?_⟩
  have hev := liminf_coefficient (Eτ := fun δ => klBin (1 - δ) δ /
    actGameStar (J astar) (hJ astar) (Hc astar) pred μ v) hCpos (fun δ _ _ => le_rfl) hc
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ h1 h2
  exact (ENNReal.ofReal_le_ofReal h1).trans (hfin δ h2.1 h2.2)

end Converse

/-! ### `thm:bay-main-optimal` (lower bound) for the sampler model -/

section KnownVariance

variable {U : Type*}

/-- Known-variance information cost of the alternative `u` under the design `w`:
`½ ∑ₓ wₓ (μₓ - pred x u)² / vₓ`, i.e. `½ ‖θ - ϑ‖²_{M(w)}` in the manuscript's notation. -/
def gcost (μ v : X → ℝ) (pred : X → U → ℝ) (w : X → ℝ) (u : U) : ℝ :=
  ∑ x, w x * ((μ x - pred x u) ^ 2 / (2 * v x))

/-- Drift part `∑ₓ Nₓ (μₓ - μ'ₓ)² / (2 vₓ)` of the known-variance log-likelihood ratio. -/
def driftL (S : GSampler X) (μ μ' v : X → ℝ) : List ℝ → ℝ
  | [] => 0
  | _ :: h => driftL S μ μ' v h +
      if halted S h then 0 else (μ (S.next h) - μ' (S.next h)) ^ 2 / (2 * v (S.next h))

lemma driftL_eq_sum (S : GSampler X) (μ μ' v : X → ℝ) :
    ∀ h : List ℝ, driftL S μ μ' v h = ∑ x, (cnt S x h : ℝ) * ((μ x - μ' x) ^ 2 / (2 * v x))
  | [] => by simp [driftL, cnt]
  | _ :: h => by
    classical
    simp only [driftL, cnt, driftL_eq_sum S μ μ' v h]
    push_cast
    simp only [add_mul, sum_add_distrib]
    congr 1
    cases hh : halted S h <;> simp

lemma measurable_drift (S : GSampler X) (μ μ' v : X → ℝ) (n : ℕ) :
    Measurable fun y : Fin n → ℝ => driftL S μ μ' v (List.ofFn y) := by
  simp_rw [driftL_eq_sum]
  exact Finset.measurable_sum _ fun x _ => (measurable_cnt S x n).mul_const _

lemma time_eq_sum (S : GSampler X) (h : List ℝ) : (time S h : ℝ) = ∑ x, (cnt S x h : ℝ) := by
  rw [← sum_cnt S h]; push_cast; rfl

lemma measurable_time (S : GSampler X) (n : ℕ) :
    Measurable fun y : Fin n → ℝ => (time S (List.ofFn y) : ℝ) := by
  simp_rw [time_eq_sum]
  exact Finset.measurable_sum _ fun x _ => measurable_cnt S x n

lemma integrable_time (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    Integrable (fun y : Fin n → ℝ => (time S (List.ofFn y) : ℝ)) (law S μ v n) := by
  simp_rw [time_eq_sum]
  exact integrable_finsetSum _ fun x _ => integrable_cnt S μ v x n

/-- Tilting the alternative along the line through `μ` and `μ'`: the log-likelihood ratio
against `μ + η (μ - μ')` is `η² · drift - η · (martingale part)`. -/
lemma llrL_tilt (S : GSampler X) (μ μ' v : X → ℝ) (hv : ∀ x, v x ≠ 0) (η : ℝ) :
    ∀ h : List ℝ, llrL S μ v (fun x => μ x + η * (μ x - μ' x)) v h =
      η ^ 2 * driftL S μ μ' v h - η * (llrL S μ v μ' v h - driftL S μ μ' v h)
  | [] => by simp [llrL, driftL]
  | t :: h => by
    simp only [llrL, driftL]
    rw [llrL_tilt S μ μ' v hv η h]
    unfold stepLLR
    cases hh : halted S h
    · simp only [Bool.false_eq_true, ite_false]
      unfold qf
      rw [div_self (hv _), Real.log_one]
      have := hv (S.next h)
      field_simp
      ring
    · simp only [ite_true]; ring

lemma continuous_gcost (μ v : X → ℝ) (pred : X → U → ℝ) (u : U) :
    Continuous fun w : X → ℝ => gcost μ v pred w u := by
  unfold gcost
  exact continuous_finsetSum _ fun x _ => (continuous_apply x).mul continuous_const

/-- Compactness of the design simplex: finitely many alternatives cover all designs. -/
lemma exists_finite_cover (pred : X → U → ℝ) (Alt : Set U) {μ v : X → ℝ} {c : ℝ}
    (hinfo : ∀ w ∈ simplex X, ∃ u ∈ Alt, gcost μ v pred w u < c) :
    ∃ Λ : Finset U, (∀ u ∈ Λ, u ∈ Alt) ∧ ∀ w ∈ simplex X, ∃ u ∈ Λ, gcost μ v pred w u < c := by
  classical
  have hopen : ∀ u : Alt, IsOpen {w : X → ℝ | gcost μ v pred w u < c} := fun u =>
    isOpen_lt (continuous_gcost μ v pred u) continuous_const
  obtain ⟨t, ht⟩ := (isCompact_simplex X).elim_finite_subcover _ hopen (fun w hw => by
    obtain ⟨u, hu, h⟩ := hinfo w hw
    exact Set.mem_iUnion.2 ⟨⟨u, hu⟩, h⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro u hu
    obtain ⟨u', -, rfl⟩ := Finset.mem_image.1 hu
    exact u'.2
  · intro w hw
    have := ht hw
    simp only [Set.mem_iUnion] at this
    obtain ⟨u, hut, h⟩ := this
    exact ⟨u.1, Finset.mem_image_of_mem _ hut, h⟩

lemma time_of_not_halted (S : GSampler X) :
    ∀ h : List ℝ, halted S h = false → time S h = h.length
  | [], _ => by simp [time]
  | _ :: h, hh => by
    rw [halted, Bool.or_eq_false_iff] at hh
    rw [time, time_of_not_halted S h hh.1, hh.1]
    simp

/-- `E[τ ∧ (T+1)] ≥ (T + 1) · P(τ > T)`. -/
lemma expTime_ge (S : GSampler X) (μ v : X → ℝ) (T : ℕ) :
    ((T : ℝ) + 1) * (1 - (law S μ v (T + 1)).real
        {y | halted S (List.ofFn (Fin.tail y)) = true}) ≤ expTime S μ v (T + 1) := by
  have hB : MeasurableSet {y : Fin (T + 1) → ℝ | halted S (List.ofFn (Fin.tail y)) = true} :=
    (measurable_tail T) (measurableSet_hset S T)
  have h1 : ∫ y, ({y : Fin (T + 1) → ℝ | halted S (List.ofFn (Fin.tail y)) = true}ᶜ).indicator
      (fun _ => (T : ℝ) + 1) y ∂(law S μ v (T + 1)) ≤ expTime S μ v (T + 1) := by
    refine integral_mono ((integrable_const _).indicator hB.compl) (integrable_time S μ v _)
      fun y => ?_
    by_cases hy : halted S (List.ofFn (Fin.tail y)) = true
    · have : y ∉ {y : Fin (T + 1) → ℝ | halted S (List.ofFn (Fin.tail y)) = true}ᶜ := by
        simpa using hy
      rw [Set.indicator_of_notMem this]
      exact Nat.cast_nonneg _
    · have hy' : halted S (List.ofFn (Fin.tail y)) = false := by simpa using hy
      have hmem : y ∈ {y : Fin (T + 1) → ℝ | halted S (List.ofFn (Fin.tail y)) = true}ᶜ := hy
      rw [Set.indicator_of_mem hmem, ofFn_eq T y, time, time_of_not_halted S _ hy', hy',
        List.length_ofFn]
      simp
  rw [integral_indicator_const _ hB.compl, probReal_compl_eq_one_sub hB, smul_eq_mul] at h1
  linarith [mul_comm ((T : ℝ) + 1) (1 - (law S μ v (T + 1)).real
    {y | halted S (List.ofFn (Fin.tail y)) = true})]

/-- **Stopping early is unlikely** (core of the multiple-answer lower bound).  Fix
`α ∈ (0, 1)`, `ζ = α I / (4 (1 - α))` and finite lists `Λ a` of alternatives invalidating `a`
that cover every design at cost below `I + ζ`.  For a `δ`-correct procedure and any
`T ≤ (1 - α) log (1/δ) / I`, the probability under the truth of halting within `T`
observations is at most `(∑ₐ |Λ a|) · (δ^{α/2} + δ^κ)` with
`κ = α² I / (64 (I + ζ) (1 - α))`. -/
lemma early_stop_bound [Fintype A] [Nonempty X] (S : GSampler X) (D : GDecision A)
    (pred : X → U → ℝ) (Alt : A → Set U) {μ v : X → ℝ} (hv : ∀ x, 0 < v x)
    {I ζ α δ : ℝ} (hI : 0 < I) (hα0 : 0 < α) (hα1 : α < 1)
    (hζ : ζ = α * I / (4 * (1 - α))) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Λ : A → Finset U) (hΛ : ∀ a, ∀ u ∈ Λ a, u ∈ Alt a)
    (hcov : ∀ a, ∀ w ∈ simplex X, ∃ u ∈ Λ a, gcost μ v pred w u < I + ζ)
    (hcorrect : ∀ a, ∀ u ∈ Alt a, ∀ n,
      law S (fun x => pred x u) v n (ansSet S D a n) ≤ ENNReal.ofReal δ)
    (T : ℕ) (hT : (T : ℝ) ≤ (1 - α) * Real.log (1 / δ) / I) :
    law S μ v (T + 1) {y | halted S (List.ofFn (Fin.tail y)) = true} ≤
      ∑ a, ∑ _u ∈ Λ a, (ENNReal.ofReal (δ ^ (α / 2)) +
        ENNReal.ofReal (δ ^ (α ^ 2 * I / (64 * (I + ζ) * (1 - α))))) := by
  classical
  obtain ⟨Lδ, hLδ⟩ : ∃ Lδ : ℝ, Lδ = Real.log (1 / δ) := ⟨_, rfl⟩
  rw [← hLδ] at hT
  have hL : 0 < Lδ := by
    rw [hLδ]; exact Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have h1α : 0 < 1 - α := by linarith
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  have hIζ : 0 < I + ζ := by linarith
  -- the bound on the drift and its two expressions
  obtain ⟨Kbar, hKbar⟩ : ∃ Kbar : ℝ, Kbar = (I + ζ) * ((1 - α) * Lδ / I) := ⟨_, rfl⟩
  have hKpos : 0 < Kbar := by rw [hKbar]; positivity
  have hK2 : Kbar = (1 - α) * Lδ + α * Lδ / 4 := by
    rw [hKbar, hζ]; field_simp
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = α * Lδ / 4 := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  -- the events
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
  -- pointwise facts on halted transcripts
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
  have hP1 : ∀ a, ∀ u ∈ Λ a, law S μ v (T + 1) (B1 a u) ≤ ENNReal.ofReal (δ ^ (α / 2)) := by
    intro a u hu
    refine lower_bound_event (law S μ v (T + 1)) (law S (fun x => pred x u) v (T + 1))
      (L := fun y => llrL S μ v (fun x => pred x u) v (List.ofFn y))
      (law_eq_withDensity S hv hv (T + 1)) (hB1 a u) hδ0 ?_ ?_
    · intro y hy
      have h1 := hdrift a u y hy.1
      have h2 : Mf u y ≤ c1 := hy.2
      have h3 : llrL S μ v (fun x => pred x u) v (List.ofFn y) =
          driftL S μ (fun x => pred x u) v (List.ofFn y) + Mf u y := by
        simp only [Mf]; ring
      rw [h3, ← hLδ]
      rw [hK2] at h1
      rw [hc1] at h2
      linarith
    · refine (measure_mono fun y hy => ?_).trans (hcorrect a u (hΛ a u hu) (T + 1))
      refine ⟨?_, hy.1.2.1⟩
      rw [ofFn_eq T y, halted, hy.1.1]
      rfl
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
  calc law S μ v (T + 1) {y | halted S (List.ofFn (Fin.tail y)) = true}
      ≤ law S μ v (T + 1) (⋃ a ∈ (univ : Finset A), ⋃ u ∈ Λ a, (B1 a u ∪ B2 a u)) :=
        measure_mono hcover
    _ ≤ ∑ a, law S μ v (T + 1) (⋃ u ∈ Λ a, (B1 a u ∪ B2 a u)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ a, ∑ u ∈ Λ a, law S μ v (T + 1) (B1 a u ∪ B2 a u) :=
        sum_le_sum fun a _ => measure_biUnion_finset_le _ _
    _ ≤ _ := sum_le_sum fun a _ => sum_le_sum fun u hu =>
        (measure_union_le _ _).trans (add_le_add (hP1 a u hu) (hP2 a u))

/-- **Correlated Gaussian information limit, lower bound (`thm:bay-main-optimal`,
`eq:bay-main-optimal`), for the sampler model.**
Known query variances `v`, true query means `μ`; an alternative `u` has query means
`pred · u`; `Alt a` is the set of alternatives under which the action `a` is not
`ε`-correct.  `I` is any upper bound for the information rates
`I_a(θ, w) = inf_{u ∈ Alt a} gcost μ v pred w u` over all actions and designs (`hinfo`), in
particular `I = I_*(θ) = max_a max_w I_a(θ, w)`.  The procedures `(S δ, D δ)` are uniformly
correct in the sense used by the proof (`hcorrect`): under every alternative in `Alt a` the
probability of halting with answer `a` is at most `δ`, at every horizon.  No assumption is
made on which answers are correct at the truth.
Conclusion: `liminf_{δ ↓ 0} E_θ[τ_δ] / log (1/δ) ≥ 1 / I`, in the form: for every `c < 1 / I`,
eventually `c log (1/δ) ≤ E_θ[τ_δ]`. -/
theorem gauss_info_lower_bound [Fintype A] [Nonempty X] (pred : X → U → ℝ) (Alt : A → Set U)
    {μ v : X → ℝ} (hv : ∀ x, 0 < v x) {I : ℝ} (hI : 0 < I)
    (hinfo : ∀ a, ∀ w ∈ simplex X, ∀ ζ > 0, ∃ u ∈ Alt a, gcost μ v pred w u < I + ζ)
    (S : ℝ → GSampler X) (D : ℝ → GDecision A)
    (hcorrect : ∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ u ∈ Alt a, ∀ n,
      law (S δ) (fun x => pred x u) v n (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ)
    {c : ℝ} (hc : c < 1 / I) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤ expTau (S δ) μ v := by
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
  have hB := early_stop_bound (S δ) (D δ) pred Alt hv hI hα0 hα1 hζ hδ0 hδ1 Λ hΛ hcov
    (hcorrect δ hδ0 hδ1) T (by rw [← hLδ]; exact hT)
  have hreal : (law (S δ) μ v (T + 1)).real
      {y | halted (S δ) (List.ofFn (Fin.tail y)) = true} ≤ ε0 := by
    refine le_trans (ENNReal.toReal_le_of_le_ofReal ?_ (hB.trans (le_of_eq ?_))) hsm
    · have := Real.rpow_nonneg hδ0.le (α / 2)
      have := Real.rpow_nonneg hδ0.le κ
      positivity
    · simp only [sum_const, nsmul_eq_mul]
      rw [← sum_mul, ← hκ, ← ENNReal.ofReal_add (Real.rpow_nonneg hδ0.le _)
        (Real.rpow_nonneg hδ0.le _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, hNn]
      push_cast
      rfl
  have hge := expTime_ge (S δ) μ v T
  have hfin : c * Lδ ≤ expTime (S δ) μ v (T + 1) := by
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
    (le_iSup (fun n => ENNReal.ofReal (expTime (S δ) μ v n)) (T + 1))

end KnownVariance

/-! ### Transportation inequality for the unbounded run, general probabilities -/

section Unbounded

/-- The horizon-`n` event "the sampler has halted and returned an answer other than `a`". -/
def nansSet (S : GSampler X) (D : GDecision A) (a : A) (n : ℕ) : Set (Fin n → ℝ) :=
  {y | halted S (List.ofFn y) = true ∧ decAt S D (List.ofFn y) ≠ a}

lemma measurableSet_nansSet (S : GSampler X) (D : GDecision A) (a : A) (n : ℕ) :
    MeasurableSet (nansSet S D a n) :=
  (measurableSet_hset S n).inter (measurableSet_decAt S D a n).compl

lemma law_nansSet_mono (S : GSampler X) (D : GDecision A) (a : A) (μ v : X → ℝ) :
    Monotone fun n => (law S μ v n).real (nansSet S D a n) :=
  monotone_nat_of_le_succ fun n => by
    have hsub : (fun y : Fin (n + 1) → ℝ => (Fin.tail y : Fin n → ℝ)) ⁻¹' (nansSet S D a n) ⊆
        nansSet S D a (n + 1) := by
      intro y hy
      obtain ⟨h1, h2⟩ := hy
      refine ⟨?_, ?_⟩
      · rw [ofFn_eq n y, halted, h1]; rfl
      · rw [ofFn_eq n y, decAt, h1]; simpa using h2
    calc (law S μ v n).real (nansSet S D a n)
        = (law S μ v (n + 1)).real
            ((fun y : Fin (n + 1) → ℝ => (Fin.tail y : Fin n → ℝ)) ⁻¹' (nansSet S D a n)) := by
          rw [← law_map_tail S μ v n,
            map_measureReal_apply (measurable_tail n) (measurableSet_nansSet S D a n)]
      _ ≤ _ := measureReal_mono hsub

/-- `n · P(τ > n) ≤ E[τ ∧ n]`. -/
lemma not_halted_mul_le (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    (n : ℝ) * (law S μ v n).real (hset S n)ᶜ ≤ expTime S μ v n := by
  have h1 : ∫ y, ((hset S n)ᶜ).indicator (fun _ => (n : ℝ)) y ∂(law S μ v n) ≤
      expTime S μ v n := by
    refine integral_mono ((integrable_const _).indicator (measurableSet_hset S n).compl)
      (integrable_time S μ v n) fun y => ?_
    by_cases hy : y ∈ (hset S n)ᶜ
    · have hy' : halted S (List.ofFn y) = false := by simpa [hset] using hy
      rw [Set.indicator_of_mem hy, time_of_not_halted S _ hy', List.length_ofFn]
    · rw [Set.indicator_of_notMem hy]; exact Nat.cast_nonneg _
  rw [integral_indicator_const _ (measurableSet_hset S n).compl, smul_eq_mul] at h1
  linarith [mul_comm (n : ℝ) ((law S μ v n).real (hset S n)ᶜ)]

lemma expCnt_le_expTime (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (x : X) :
    expCnt S μ v n x ≤ expTime S μ v n := by
  rw [← sum_expCnt]
  exact single_le_sum (fun x _ => expCnt_nonneg S μ v n x) (mem_univ x)

lemma measureReal_pos_of_pos (S : GSampler X) {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x)
    (hv' : ∀ x, 0 < v' x) (n : ℕ) {E : Set (Fin n → ℝ)} (h : 0 < (law S μ v n).real E) :
    0 < (law S μ' v' n).real E := by
  by_contra hcon
  have h0 : (law S μ' v' n).real E = 0 := le_antisymm (not_lt.1 hcon) measureReal_nonneg
  have h1 : law S μ' v' n E = 0 := (measureReal_eq_zero_iff (measure_ne_top _ E)).1 h0
  have h2 : (law S μ v n).real E = 0 := by
    simp [Measure.real, law_absolutelyContinuous S hv hv' n h1]
  linarith

/-- **Stopped Gaussian change of measure for an unbounded stopping time** (Gaussian analogue of
`lem:active-com`).  For a sampler with finite expected stopping time under `(μ, v)`
(`hB`: `E_{μ,v}[τ ∧ n] ≤ B` for all `n`) and the event "halts and returns `a`",
`kl(P_{μ,v}(E), P_{μ',v'}(E)) ≤ ∑ₓ E_{μ,v}[Nₓ(τ)] · KL(N(μₓ, vₓ) ‖ N(μ'ₓ, v'ₓ))`.
Probabilities and expected counts of the unbounded run are the suprema (limits, by
`law_ansSet_mono`, `expCnt_mono`) of their horizon-`n` values.  Almost-sure stopping under
`(μ', v')` is not needed. -/
theorem gauss_stopped_transport (S : GSampler X) (D : GDecision A) (a : A)
    {μ v μ' v' : X → ℝ} (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) {B : ℝ}
    (hB : ∀ n, expTime S μ v n ≤ B) :
    bkl (⨆ n, (law S μ v n).real (ansSet S D a n))
        (⨆ n, (law S μ' v' n).real (ansSet S D a n)) ≤
      ∑ x, (⨆ n, expCnt S μ v n x) * gaussKL (μ x) (v x) (μ' x) (v' x) := by
  have bddp : ∀ m w : X → ℝ,
      BddAbove (Set.range fun n => (law S m w n).real (ansSet S D a n)) := fun m w =>
    ⟨1, by rintro _ ⟨n, rfl⟩; exact measureReal_le_one⟩
  have bddc : ∀ x, BddAbove (Set.range fun n => expCnt S μ v n x) := fun x =>
    ⟨B, by rintro _ ⟨n, rfl⟩; exact (expCnt_le_expTime S μ v n x).trans (hB n)⟩
  have hp := tendsto_atTop_ciSup (law_ansSet_mono S D a μ v) (bddp μ v)
  have hq := tendsto_atTop_ciSup (law_ansSet_mono S D a μ' v') (bddp μ' v')
  refine Stopped.bkl_le_of_tendsto hp hq
    (le_ciSup_of_le (bddp μ v) 0 measureReal_nonneg) (ciSup_le fun n => measureReal_le_one)
    (le_ciSup_of_le (bddp μ' v') 0 measureReal_nonneg) (ciSup_le fun n => measureReal_le_one)
    ?_ ?_ fun n a' b' => ?_
  · intro hP
    obtain ⟨n, hn⟩ : ∃ n, 0 < (law S μ v n).real (ansSet S D a n) := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : (⨆ n, (law S μ v n).real (ansSet S D a n)) ≤ 0 := ciSup_le hcon
      linarith
    exact (measureReal_pos_of_pos S hv hv' n hn).trans_le (le_ciSup (bddp μ' v') n)
  · intro hP
    obtain ⟨n, hn⟩ : ∃ n, 0 < (law S μ v n).real (nansSet S D a n) := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have hd : 0 < 1 - ⨆ n, (law S μ v n).real (ansSet S D a n) := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (B / (1 - ⨆ n, (law S μ v n).real (ansSet S D a n)))
      have h1 : B < n * (1 - ⨆ n, (law S μ v n).real (ansSet S D a n)) := by
        rwa [div_lt_iff₀ hd] at hn
      have h2 := not_halted_mul_le S μ v n
      have h3 : (law S μ v n).real (hset S n) ≤
          (law S μ v n).real (ansSet S D a n) + (law S μ v n).real (nansSet S D a n) := by
        refine (measureReal_mono (fun y hy => ?_)).trans (measureReal_union_le _ _)
        by_cases hd : decAt S D (List.ofFn y) = a
        · exact Or.inl ⟨hy, hd⟩
        · exact Or.inr ⟨hy, hd⟩
      have h4 : (law S μ v n).real (hset S n)ᶜ = 1 - (law S μ v n).real (hset S n) :=
        probReal_compl_eq_one_sub (measurableSet_hset S n)
      have h5 := le_ciSup (bddp μ v) n
      have h6 := hcon n
      have h7 : (1 - ⨆ n, (law S μ v n).real (ansSet S D a n)) ≤
          (law S μ v n).real (hset S n)ᶜ := by
        linarith
      have h8 := mul_le_mul_of_nonneg_left h7 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith [hB n]
    have hq' := measureReal_pos_of_pos S (μ' := μ') hv hv' n hn
    have hle : ∀ m, (law S μ' v' m).real (ansSet S D a m) ≤
        1 - (law S μ' v' n).real (nansSet S D a n) := by
      intro m
      have h1 := law_ansSet_mono S D a μ' v' (le_max_left m n)
      have h2 := law_nansSet_mono S D a μ' v' (le_max_right m n)
      have hdisj : Disjoint (ansSet S D a (max m n)) (nansSet S D a (max m n)) :=
        Set.disjoint_left.2 fun y h1 h2 => h2.2 h1.2
      have h3 := measureReal_union (μ := law S μ' v' (max m n)) hdisj
        (measurableSet_nansSet S D a (max m n))
      have h4 : (law S μ' v' (max m n)).real
          (ansSet S D a (max m n) ∪ nansSet S D a (max m n)) ≤ 1 := measureReal_le_one
      linarith
    have := ciSup_le hle
    linarith
  · have hae := llr_ae_eq S (μ := μ) (μ' := μ') hv hv' n
    have hint : Integrable (llr (law S μ v n) (law S μ' v' n)) (law S μ v n) :=
      (integrable_congr hae).2 (integrable_llr S hv hv' n)
    have h := two_point_dv _ _ (law_absolutelyContinuous S hv hv' n) hint
      (measurableSet_ansSet S D a n) a' b'
    rw [integral_congr_ae hae, wald_identity S hv hv' n] at h
    exact h.trans (sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (le_ciSup (bddc x) n) (gaussKL_nonneg (hv x) (hv' x)))

end Unbounded

end GaussStopped

end

end JointRootCert
