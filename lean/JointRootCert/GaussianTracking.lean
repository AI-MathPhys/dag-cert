/-
# Known-variance Gaussian information limit: the tracking procedure and the upper bound

Manuscript result: `thm:bay-main-optimal` (Correlated Gaussian information limit), the
upper-bound half ("Constructive optimal allocation and proof of the sharp limit":
allocation rule; tracking, estimation and stabilization; `eq:bay-information-growth`;
expected upper bound), the safety of the likelihood stopping rule (the paragraph after
`lem:bay-cs`), and the theorem itself, combined with the lower bound
`gauss_info_lower_bound` of `GaussianStopped.lean`.

Main statements:

* `gcost_eq_design`, `gcost_isGLB`: the coordinate cost `gcost` of `GaussianStopped.lean`
  is `½ ‖λ - θ‖²_{M(w)}` and its infimum over alternatives is `½ rootInfo²`, so the lower
  and upper halves refer to the same `I_a(θ, w)`.
* `Tracker.sampler`, `Tracker.decision`: the likelihood-certified information tracker as a
  `GSampler` (exploration floor `η_t = t^{-1/4}`, selector slack `ζ_t = t^{-1/16}`, plug-in
  design from an allocation oracle, deficit tracking, stopping when `G_t` is invertible and
  some `J_t(a) ≥ H_t(δ)`).
* `Tracker.bad_poly`: `P(‖θ̂_k - θ‖ > (k+1)^{-1/8}) ≤ C (k+1)^{-3}` along the adaptive run.
* `Tracker.sel_eq`, `Tracker.plan_quality`, `Tracker.stat_growth`,
  `Tracker.growth_package`: stabilisation of the selected action, near-optimality of the
  plug-in design and the information-growth inequality.
* `Tracker.lintegral_Tbad_ne_top`, `Tracker.pathwise`: the pathwise domination
  `τ_δ ≤ max {T_s, ⌈log(1/δ) / (I_* - 2s)⌉}` by an integrable time.
* `Tracker.upper_half`, `Tracker.expTau_ne_top`: the upper rate and finite expectation.
* `Tracker.safe_joint`, `Tracker.safe`: uniform `δ`-correctness.
* `Tracker.bay_main_optimal`: the theorem for any oracle meeting the contract;
  `gaussian_information_limit`: the theorem with an oracle constructed.

Model.  Samplers are those of `GaussianStopped.lean` (deterministic functions of the
observed history; expectations are suprema over the horizon).  The unbounded run is
realised on the tape space `ℕ → ℝ` of i.i.d. standard Gaussian noise (`gP`); `map_hist_rev`
identifies the horizon-`n` transcript law with the image of the tape law, and `coupling`
relates a stopped sampler to its unstopped run.  Parameters live in `ℝ^d = ι → ℝ`
(`EuclideanSpace ℝ ι` for the geometry); features are whitened, the observation of `x`
under `λ` is `N(√(v_x) ⟨u_x, λ⟩, v_x)`.

What is assumed.  In `Tracker.bay_main_optimal`: the oracle contract
`eq:bay-oracle-contract` (`Tracker.Valid`: floor, `0 ≤ c ≤ I_a(θ̂, v)`,
`max_w I_a(θ̂, w) - c ≤ η C_R + ξ`) and Borel measurability of the oracle in the estimate
(`Tracker.Meas`).  `gaussian_information_limit` removes both by constructing an oracle
from a countable dense sequence of designs with exact values (`gridTracker`); this is an
existence argument, not the manuscript's finite grid.  In both: a reference design with
`M(w⁰) ⪰ κ I`, every action has a strict `ε`-invalidating alternative (no universal
action), and `I_*(θ) > 0`.

Differences from the manuscript's text: rounds are indexed from `0` (round `t = k + 1`);
ties are broken by a fixed choice function on finite sets rather than by fixed orders; the
tracking loss is `ρ_k = m (m - 1) ℓ² / (κ E_k)`, `E_k = ∑_{j<k} η_j`, which does not need
`min_x w⁰_x > 0`; `eq:bay-information-growth` is proved in root form (`stat_growth`); the
stopping rule uses the exact `J_t` and `H_t` (verified numerical enclosures are not
modelled).
-/
import JointRootCert.GaussianUpper
import JointRootCert.GaussianStopped
import JointRootCert.SelfNormalized
import JointRootCert.GaussianFinite
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

namespace JointRootCert

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace GaussTrack

open GaussStopped

/-! ### Stage 1: the coordinate cost `gcost` is the squared `rootInfo` cost -/

section CostLink

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- With whitened features `u_x` (so that the mean of query `x` under the parameter `λ` is
`√(v_x) ⟨u_x, λ⟩`), the coordinate cost `gcost` of `GaussianStopped.lean` is
`½ ‖λ - θ‖²_{M(w)}`. -/
theorem gcost_eq_design (u : X → E) {v : X → ℝ} (hv : ∀ x, 0 < v x) {w : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) (θ lam : E) :
    gcost (fun x => Real.sqrt (v x) * ⟪u x, θ⟫) v (fun x l => Real.sqrt (v x) * ⟪u x, l⟫) w lam =
      ‖designMap u w (lam - θ)‖ ^ 2 / 2 := by
  rw [norm_designMap_sq u hw, gcost, Finset.sum_div]
  refine sum_congr rfl fun x _ => ?_
  have hs := Real.sq_sqrt (hv x).le
  have h1 : (Real.sqrt (v x) * ⟪u x, θ⟫ - Real.sqrt (v x) * ⟪u x, lam⟫) ^ 2 =
      v x * ⟪u x, lam - θ⟫ ^ 2 := by
    rw [inner_sub_right, ← mul_sub, mul_pow, hs]
    ring
  rw [h1]
  have := (hv x).ne'
  field_simp

/-- **Stage 1.**  The information rate of `GaussianStopped.lean`,
`inf_{λ ∈ Q} gcost θ w λ`, is `½ rootInfo²`: the lower bound `gauss_info_lower_bound` and the
upper bound below refer to the same `I_a(θ, w)`. -/
theorem gcost_isGLB (u : X → E) {v : X → ℝ} (hv : ∀ x, 0 < v x) {w : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) (θ : E) {Q : Set E} (hQ : Q.Nonempty) :
    IsGLB ((fun lam => gcost (fun x => Real.sqrt (v x) * ⟪u x, θ⟫) v
        (fun x l => Real.sqrt (v x) * ⟪u x, l⟫) w lam) '' Q)
      (rootInfo (designMap u w) Q θ ^ 2 / 2) := by
  have h : (fun lam => gcost (fun x => Real.sqrt (v x) * ⟪u x, θ⟫) v
      (fun x l => Real.sqrt (v x) * ⟪u x, l⟫) w lam) =
      fun lam => ‖designMap u w (lam - θ)‖ ^ 2 / 2 := funext (gcost_eq_design u hv hw θ)
  rw [h]
  exact rootInfo_isGLB hQ

end CostLink

/-! ### The noise tape: one probability space for the unbounded run -/

/-- The law of an i.i.d. standard Gaussian noise tape. -/
def gP : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure gP := by unfold gP; infer_instance

/-- The first `n` noise values, most recent first. -/
def rev (n : ℕ) (ω : ℕ → ℝ) : Fin n → ℝ := fun i => ω (n - 1 - i)

lemma measurable_rev (n : ℕ) : Measurable (rev n) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

lemma map_rev (n : ℕ) : gP.map (rev n) = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hinj : Function.Injective (fun i : Fin n => n - 1 - (i : ℕ)) := by
    intro i j h
    have := i.2
    have := j.2
    simp only at h
    ext
    omega
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => gaussianReal 0 1) hinj
  rw [Measure.infinitePi_eq_pi (μ := fun _ : Fin n => gaussianReal 0 1)] at h
  exact h

lemma tail_rev (n : ℕ) (ω : ℕ → ℝ) : Fin.tail (rev (n + 1) ω) = rev n ω := by
  funext i
  simp only [Fin.tail, rev, Fin.val_succ]
  congr 1
  omega

section Sampler

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X]

/-- The transcript of the first `n` observations of the sampler `S` on the noise tape `ω`
(most recent first), padded after halting as in `GaussianStopped.lean`. -/
def tr (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (ω : ℕ → ℝ) : List ℝ :=
  List.ofFn (hist S μ v n (rev n ω))

lemma tr_zero (S : GSampler X) (μ v : X → ℝ) (ω : ℕ → ℝ) : tr S μ v 0 ω = [] := by
  simp [tr]

lemma tr_succ (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (ω : ℕ → ℝ) :
    tr S μ v (n + 1) ω = obs S μ v (tr S μ v n ω) (ω n) :: tr S μ v n ω := by
  have h : hist S μ v (n + 1) (rev (n + 1) ω) =
      Fin.cons (obs S μ v (List.ofFn (hist S μ v n (Fin.tail (rev (n + 1) ω))))
        (rev (n + 1) ω 0)) (hist S μ v n (Fin.tail (rev (n + 1) ω))) := rfl
  unfold tr
  rw [h, List.ofFn_cons, tail_rev]
  have h0 : rev (n + 1) ω 0 = ω n := by simp [rev]
  rw [h0]

/-- The law of the transcript at horizon `n` is the image of the tape law. -/
theorem map_hist_rev (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    gP.map (fun ω => hist S μ v n (rev n ω)) = law S μ v n := by
  rw [← law_eq_map_hist, ← map_rev, Measure.map_map (measurable_hist S μ v n) (measurable_rev n)]
  rfl

lemma law_apply_tape (S : GSampler X) (μ v : X → ℝ) (n : ℕ) {B : Set (Fin n → ℝ)}
    (hB : MeasurableSet B) : law S μ v n B = gP {ω | hist S μ v n (rev n ω) ∈ B} := by
  have hm : Measurable (fun ω => hist S μ v n (rev n ω)) :=
    (measurable_hist S μ v n).comp (measurable_rev n)
  rw [← map_hist_rev, Measure.map_apply hm hB]
  rfl

lemma expTime_eq_tape (S : GSampler X) (μ v : X → ℝ) (n : ℕ) :
    expTime S μ v n = ∫ ω, (time S (tr S μ v n ω) : ℝ) ∂gP := by
  have hm : Measurable (fun ω => hist S μ v n (rev n ω)) :=
    (measurable_hist S μ v n).comp (measurable_rev n)
  unfold expTime
  rw [← map_hist_rev, integral_map hm.aemeasurable (measurable_time S n).aestronglyMeasurable]
  rfl

/-- The same allocation rule, never stopped. -/
def free (S : GSampler X) : GSampler X where
  next := S.next
  stop := fun _ => false
  meas_next := S.meas_next
  meas_stop := fun _ => measurable_const

lemma halted_free (S : GSampler X) : ∀ h : List ℝ, halted (free S) h = false
  | [] => rfl
  | _ :: h => by rw [halted, halted_free S h]; rfl

/-- The unstopped run of the allocation rule of `S` on the noise tape. -/
def run (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (ω : ℕ → ℝ) : List ℝ := tr (free S) μ v n ω

lemma run_zero (S : GSampler X) (μ v : X → ℝ) (ω : ℕ → ℝ) : run S μ v 0 ω = [] :=
  tr_zero _ _ _ _

lemma run_succ (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (ω : ℕ → ℝ) :
    run S μ v (n + 1) ω =
      (μ (S.next (run S μ v n ω)) + Real.sqrt (v (S.next (run S μ v n ω))) * ω n) ::
        run S μ v n ω := by
  unfold run
  rw [tr_succ]
  congr 1
  unfold obs
  rw [halted_free]
  rfl

lemma length_run (S : GSampler X) (μ v : X → ℝ) (n : ℕ) (ω : ℕ → ℝ) :
    (run S μ v n ω).length = n := by
  simp [run, tr]

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

/-- **Coupling of the stopped sampler with its unstopped run.**  Until `S` halts its
transcript is the unstopped run; once it has halted, the halting time is the first `k` at
which the stopping rule fires along the unstopped run, and the answer is read there. -/
lemma coupling (S : GSampler X) (D : GDecision A) (μ v : X → ℝ) (ω : ℕ → ℝ) : ∀ n,
    (halted S (tr S μ v n ω) = false → tr S μ v n ω = run S μ v n ω ∧
        time S (tr S μ v n ω) = n ∧ ∀ j ≤ n, S.stop (run S μ v j ω) = false) ∧
    (halted S (tr S μ v n ω) = true → ∃ k ≤ n, S.stop (run S μ v k ω) = true ∧
        (∀ j < k, S.stop (run S μ v j ω) = false) ∧ time S (tr S μ v n ω) = k ∧
        decAt S D (tr S μ v n ω) = D.dec (run S μ v k ω))
  | 0 => by
    rw [tr_zero, run_zero]
    refine ⟨fun h => ⟨rfl, rfl, fun j hj => ?_⟩, fun h => ⟨0, le_rfl, ?_, ?_, rfl, rfl⟩⟩
    · have : j = 0 := by omega
      subst this
      rw [run_zero]
      exact h
    · rw [run_zero]
      exact h
    · intro j hj
      omega
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := coupling S D μ v ω n
    rw [tr_succ]
    cases hh : halted S (tr S μ v n ω)
    · obtain ⟨e1, e2, e3⟩ := ih1 hh
      have hy : obs S μ v (tr S μ v n ω) (ω n) :: tr S μ v n ω = run S μ v (n + 1) ω := by
        rw [run_succ, ← e1]
        unfold obs
        rw [hh]
        rfl
      have hhal : halted S (run S μ v (n + 1) ω) = S.stop (run S μ v (n + 1) ω) := by
        rw [← hy, halted, hh, Bool.false_or]
      have htime : time S (run S μ v (n + 1) ω) = n + 1 := by
        rw [← hy, time, hh, e2]
        rfl
      rw [hy]
      refine ⟨fun h => ⟨rfl, htime, fun j hj => ?_⟩, fun h => ⟨n + 1, le_rfl, ?_, ?_, htime, ?_⟩⟩
      · rcases Nat.lt_or_ge j (n + 1) with hlt | hge
        · exact e3 j (by omega)
        · have : j = n + 1 := by omega
          subst this
          rw [← hhal]
          exact h
      · rw [← hhal]
        exact h
      · intro j hj
        exact e3 j (by omega)
      · rw [← hy, decAt, hh]
        rfl
    · obtain ⟨k, hk, e1, e2, e3, e4⟩ := ih2 hh
      have hhal : halted S (obs S μ v (tr S μ v n ω) (ω n) :: tr S μ v n ω) = true := by
        rw [halted, hh, Bool.true_or]
      refine ⟨fun h => ?_, fun _ => ⟨k, by omega, e1, e2, ?_, ?_⟩⟩
      · rw [hhal] at h
        exact absurd h (by simp)
      · rw [time, hh, e3]
        rfl
      · rw [decAt, hh, ← e4]
        rfl

/-- If the stopping rule fires by time `k` along the unstopped run, the sampler has taken at
most `k` observations at every horizon. -/
lemma time_le_of_stop (S : GSampler X) (μ v : X → ℝ) (ω : ℕ → ℝ) {k : ℕ}
    (h : ∃ j ≤ k, S.stop (run S μ v j ω) = true) (n : ℕ) : time S (tr S μ v n ω) ≤ k := by
  obtain ⟨j, hj, hs⟩ := h
  obtain ⟨c1, c2⟩ := coupling S (⟨fun _ => (), fun _ => measurable_const⟩ : GDecision Unit) μ v ω n
  cases hh : halted S (tr S μ v n ω)
  · obtain ⟨-, e2, e3⟩ := c1 hh
    rw [e2]
    by_contra hcon
    have := e3 j (by omega)
    rw [hs] at this
    exact absurd this (by simp)
  · obtain ⟨k', -, e1, e2, e3, -⟩ := c2 hh
    rw [e3]
    by_contra hcon
    have := e2 j (by omega)
    rw [hs] at this
    exact absurd this (by simp)

/-- If the sampler has halted with answer `a`, the stopping rule fired at some time along the
unstopped run and the decision rule returned `a` there. -/
lemma ans_of_halted (S : GSampler X) (D : GDecision A) (μ v : X → ℝ) (ω : ℕ → ℝ) (n : ℕ)
    {a : A} (h1 : halted S (tr S μ v n ω) = true) (h2 : decAt S D (tr S μ v n ω) = a) :
    ∃ k, S.stop (run S μ v k ω) = true ∧ D.dec (run S μ v k ω) = a := by
  obtain ⟨k, -, e1, -, -, e4⟩ := (coupling S D μ v ω n).2 h1
  exact ⟨k, e1, by rw [← e4, h2]⟩

end Sampler

/-! ### The filtration of the tape and the conditional law of the next noise value -/

/-- `tapeFilt k` is generated by the first `k` noise values. -/
def tapeFilt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ)) where
  seq k := Filtration.piFinset (X := fun _ : ℕ => ℝ) (Finset.range k)
  mono' i j hij :=
    (Filtration.piFinset (X := fun _ : ℕ => ℝ)).mono (Finset.range_subset_range.2 hij)
  le' k := (Filtration.piFinset (X := fun _ : ℕ => ℝ)).le _

lemma tapeFilt_eq (k : ℕ) : (tapeFilt k : MeasurableSpace (ℕ → ℝ)) =
    MeasurableSpace.comap (Finset.range k).restrict MeasurableSpace.pi := rfl

lemma measurable_tapeFilt_of_restrict {β : Type*} [MeasurableSpace β] (k : ℕ)
    {f : ((Finset.range k) → ℝ) → β} (hf : Measurable f) :
    Measurable[tapeFilt k] (fun ω : ℕ → ℝ => f ((Finset.range k).restrict ω)) := by
  rw [tapeFilt_eq]
  exact hf.comp (comap_measurable _)

lemma measurable_tapeFilt_coord {j k : ℕ} (hjk : j < k) :
    Measurable[tapeFilt k] (fun ω : ℕ → ℝ => ω j) :=
  measurable_tapeFilt_of_restrict k
    (f := fun r => r ⟨j, Finset.mem_range.2 hjk⟩) (measurable_pi_apply _)

lemma measurable_tapeFilt_rev (k : ℕ) : Measurable[tapeFilt k] (rev k) := by
  have hf : Measurable (fun (r : (Finset.range k) → ℝ) (i : Fin k) =>
      r ⟨k - 1 - i, Finset.mem_range.2 (by have := i.2; omega)⟩) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  exact measurable_tapeFilt_of_restrict k hf

/-- A measurable function of the unstopped transcript of length `k` is measurable with
respect to the first `k` noise values. -/
lemma measurable_tapeFilt_hist {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] {β : Type*} [MeasurableSpace β] (S : GSampler X) (μ v : X → ℝ) (k : ℕ)
    {F : (Fin k → ℝ) → β} (hF : Measurable F) :
    Measurable[tapeFilt k] (fun ω => F (hist S μ v k (rev k ω))) :=
  (hF.comp (measurable_hist S μ v k)).comp (measurable_tapeFilt_rev k)

/-- The next noise value is conditionally standard Gaussian, hence `1`-sub-Gaussian, given the
first `k` noise values. -/
lemma condSubG_coord (k : ℕ) : CondSubG gP (tapeFilt k) (fun ω : ℕ → ℝ => ω k) 1 := by
  have hiind : iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) => ω i) gP :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => x)
      (fun _ => measurable_id)
  have hdisj : Disjoint ({k} : Finset ℕ) (Finset.range k) := by
    rw [Finset.disjoint_singleton_left]
    simp
  have hind := hiind.indepFun_finset {k} (Finset.range k) hdisj (fun i => measurable_pi_apply i)
  have hle : MeasurableSpace.comap (fun ω : ℕ → ℝ => ω k) (inferInstance : MeasurableSpace ℝ) ≤
      MeasurableSpace.comap (fun (a : ℕ → ℝ) (i : ({k} : Finset ℕ)) => a i)
        MeasurableSpace.pi := by
    have h1 : (fun ω : ℕ → ℝ => ω k) =
        (fun r : (({k} : Finset ℕ)) → ℝ => r ⟨k, Finset.mem_singleton_self k⟩) ∘
          (fun (a : ℕ → ℝ) (i : ({k} : Finset ℕ)) => a i) := rfl
    rw [h1, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  have hind' : Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ => ω k)
      (inferInstance : MeasurableSpace ℝ)) (tapeFilt k) gP :=
    indep_of_indep_of_le_left hind hle
  have hlaw : gP.map (fun ω : ℕ → ℝ => ω k) = gaussianReal 0 1 :=
    Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) k
  have h := CondSubG.of_indep_gaussian (μ := gP) (X := fun ω : ℕ → ℝ => ω k) (v := 1)
    (measurable_pi_apply k) hlaw (tapeFilt.le k) hind'
  simpa using h

open Matrix
open scoped Classical

/-! ### The tracking procedure as a sampler -/

/-- A fixed choice function on finite sets: the tie-breaking rule.  (The manuscript fixes
orders on actions and experiments and takes the first element; any fixed choice function on
finite sets serves.) -/
def pick {α : Type*} [Nonempty α] (s : Finset α) : α :=
  if h : s.Nonempty then h.choose else Classical.arbitrary α

lemma pick_mem {α : Type*} [Nonempty α] {s : Finset α} (h : s.Nonempty) : pick s ∈ s := by
  unfold pick
  rw [dite_eq_left]
  exact h.choose_spec

lemma measurable_pick {β α : Type*} [MeasurableSpace β] [Fintype α] [Nonempty α]
    [MeasurableSpace α] (f : β → Finset α) (hf : ∀ a, MeasurableSet {b | a ∈ f b}) :
    Measurable (fun b => pick (f b)) := by
  have hs : ∀ s : Finset α, MeasurableSet (f ⁻¹' {s}) := by
    intro s
    have : f ⁻¹' {s} = ⋂ a, {b | a ∈ f b ↔ a ∈ s} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      exact Finset.ext_iff
    rw [this]
    refine MeasurableSet.iInter fun a => ?_
    by_cases ha : a ∈ s
    · have e : {b | a ∈ f b ↔ a ∈ s} = {b | a ∈ f b} := by
        ext b; simp [ha]
      rw [e]
      exact hf a
    · have e : {b | a ∈ f b ↔ a ∈ s} = {b | a ∈ f b}ᶜ := by
        ext b; simp [ha]
      rw [e]
      exact (hf a).compl
  intro t _
  have : (fun b => pick (f b)) ⁻¹' t = ⋃ s ∈ {s : Finset α | pick s ∈ t}, f ⁻¹' {s} := by
    ext b
    simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun s _ => hs s

/-- `r_k = (k + 1)^{1/16}`; the schedules of the allocation rule are powers of `r_k`. -/
def rk (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ ((1 : ℝ) / 16)

lemma rk_pos (k : ℕ) : 0 < rk k := Real.rpow_pos_of_pos (by positivity) _

lemma rk_pow (k : ℕ) : rk k ^ 16 = (k : ℝ) + 1 := by
  unfold rk
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

lemma one_le_rk (k : ℕ) : 1 ≤ rk k :=
  Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num)

lemma rk_mono : Monotone rk := fun i j h =>
  Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ h) (by norm_num)

/-- Exploration and oracle tolerance `η_t = ξ_t = t^{-1/4}` at round `t = k + 1`. -/
def etaK (k : ℕ) : ℝ := (rk k)⁻¹ ^ 4

/-- Selector slack `ζ_t = t^{-1/16}` at round `t = k + 1`. -/
def zetaK (k : ℕ) : ℝ := (rk k)⁻¹

lemma etaK_eq (k : ℕ) : etaK k = ((k : ℝ) + 1) ^ (-(1 : ℝ) / 4) := by
  unfold etaK rk
  rw [← Real.rpow_neg_one, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

lemma zetaK_eq (k : ℕ) : zetaK k = ((k : ℝ) + 1) ^ (-(1 : ℝ) / 16) := by
  unfold zetaK rk
  rw [← Real.rpow_neg_one, ← Real.rpow_mul (by positivity)]
  norm_num

lemma etaK_pos (k : ℕ) : 0 < etaK k := pow_pos (inv_pos.mpr (rk_pos k)) 4

lemma etaK_le_one (k : ℕ) : etaK k ≤ 1 :=
  pow_le_one₀ (inv_pos.mpr (rk_pos k)).le (inv_le_one_of_one_le₀ (one_le_rk k))

/-- The data of the tracking procedure: whitened query features `u`, query variances `v`,
alternative sets `Q a`, reference design `w0`, mixing parameter `γ`, and the allocation
oracle (design `ow` and lower value `oc`), called with the round index and the estimate. -/
structure Tracker (X ι 𝒜 : Type*) where
  /-- whitened features `u_x = h_x / σ_x` -/
  u : X → ι → ℝ
  /-- query variances `σ_x²` -/
  v : X → ℝ
  /-- alternatives invalidating each action -/
  Q : 𝒜 → Set (EuclideanSpace ℝ ι)
  /-- reference design -/
  w0 : X → ℝ
  /-- mixing parameter of the confidence sequence -/
  γ : ℝ
  /-- oracle design `v_t(a)` -/
  ow : ℕ → (ι → ℝ) → 𝒜 → X → ℝ
  /-- oracle lower value `c_t(a)` -/
  oc : ℕ → (ι → ℝ) → 𝒜 → ℝ

/-- State of the procedure: counts `N_x`, cumulative targets `W_x`, and `b = ∑ Y_s u_{X_s}`. -/
abbrev TState (X ι : Type*) := (X → ℕ) × (X → ℝ) × (ι → ℝ)

/-- Index maximizing a score, with fixed tie-breaking. -/
def amax {X : Type*} [Fintype X] [Nonempty X] (d : X → ℝ) : X :=
  pick (univ.filter fun x => ∀ x', d x' ≤ d x)

lemma amax_spec {X : Type*} [Fintype X] [Nonempty X] (d : X → ℝ) (x' : X) : d x' ≤ d (amax d) := by
  have hne : (univ.filter fun x => ∀ x', d x' ≤ d x).Nonempty := by
    obtain ⟨x, -, hx⟩ := Finset.exists_max_image univ d univ_nonempty
    exact ⟨x, by simpa using fun x' => hx x' (mem_univ _)⟩
  have := pick_mem hne
  simp only [mem_filter, mem_univ, true_and] at this
  exact this x'

namespace Tracker

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]
variable (T : Tracker X ι 𝒜)

/-- Features as vectors of `ℝ^d` with its Euclidean norm. -/
def uE (x : X) : EuclideanSpace ℝ ι := WithLp.toLp 2 (T.u x)

/-- Query means under the parameter `θ`: `√(v_x) ⟨u_x, θ⟩`. -/
def mean (θ : ι → ℝ) (x : X) : ℝ := Real.sqrt (T.v x) * (T.u x ⬝ᵥ θ)

/-- Gram matrix `G = ∑_x N_x u_x u_xᵀ` of the counts `N`. -/
def Gm (N : X → ℕ) : Matrix ι ι ℝ := ∑ x, (N x : ℝ) • vecMulVec (T.u x) (T.u x)

/-- The estimate `θ̂ = G⁻¹ b` (zero while `G` is singular). -/
def est (N : X → ℕ) (b : ι → ℝ) : ι → ℝ := (T.Gm N)⁻¹ *ᵥ b

/-- Actions passing the eligibility test `√(2 c(a)) ≥ max_b √(2 c(b)) - ζ`. -/
def elig (k : ℕ) (θh : ι → ℝ) : Finset 𝒜 :=
  univ.filter fun a => ∀ b, Real.sqrt (2 * T.oc k θh b) - zetaK k ≤ Real.sqrt (2 * T.oc k θh a)

/-- The selected action `a_t`. -/
def selA (k : ℕ) (θh : ι → ℝ) : 𝒜 := pick (T.elig k θh)

/-- The target design `v_t = v_t(a_t)`. -/
def plan (k : ℕ) (θh : ι → ℝ) : X → ℝ := T.ow k θh (T.selA k θh)

/-- The experiment queried at round `k + 1`: it maximizes `∑_{s ≤ t} v_s(x) - N_x(t - 1)`. -/
def nextQ (k : ℕ) (s : TState X ι) : X :=
  amax fun x => s.2.1 x + T.plan k (T.est s.1 s.2.2) x - (s.1 x : ℝ)

/-- State update after observing `y` at round `k + 1`. -/
def upd (k : ℕ) (s : TState X ι) (y : ℝ) : TState X ι :=
  (Function.update s.1 (T.nextQ k s) (s.1 (T.nextQ k s) + 1),
    s.2.1 + T.plan k (T.est s.1 s.2.2),
    s.2.2 + (y / Real.sqrt (T.v (T.nextQ k s))) • T.u (T.nextQ k s))

/-- The state after a history (most recent observation first). -/
def st : List ℝ → TState X ι
  | [] => (0, 0, 0)
  | y :: h => T.upd h.length (st h) y

/-- The stopping statistic `J_t(a) = t I_a(θ̂_t, N(t)/t) = inf_{λ ∈ Q_a} ½ ‖λ - θ̂_t‖²_{G_t}`. -/
def stat (a : 𝒜) (s : TState X ι) : ℝ :=
  gInfo T.uE (T.Q a) (WithLp.toLp 2 (T.est s.1 s.2.2)) (fun x => (s.1 x : ℝ))

/-- The threshold `H_t(δ)` of `eq:bay-gaussian-cs`. -/
def thr (δ : ℝ) (s : TState X ι) : ℝ := mixThreshold δ T.γ (T.Gm s.1) s.2.2

/-- The stopping rule: `G_t` is invertible and some `J_t(a) ≥ H_t(δ)`. -/
def stopP (δ : ℝ) (s : TState X ι) : Prop :=
  (∃ lam, 0 < lam ∧ Coercive (T.Gm s.1) lam) ∧ ∃ a, T.thr δ s ≤ T.stat a s

/-- The certified actions. -/
def certSet (δ : ℝ) (s : TState X ι) : Finset 𝒜 := univ.filter fun a => T.thr δ s ≤ T.stat a s

/-- Borel measurability of the oracle in the estimate. -/
structure Meas [MeasurableSpace 𝒜] : Prop where
  oc : ∀ k a, Measurable fun θh => T.oc k θh a
  ow : ∀ k a, Measurable fun θh => T.ow k θh a

variable [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]

lemma measurable_est_right (N : X → ℕ) : Measurable fun b : ι → ℝ => T.est N b := by
  refine measurable_pi_iff.mpr fun i => ?_
  show Measurable fun b : ι → ℝ => ∑ j, (T.Gm N)⁻¹ i j * b j
  exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _

lemma measurable_est : Measurable fun p : (X → ℕ) × (ι → ℝ) => T.est p.1 p.2 :=
  measurable_from_prod_countable_right fun N => T.measurable_est_right N

lemma measurable_proj : Measurable fun s : TState X ι => ((s.1, s.2.2) : (X → ℕ) × (ι → ℝ)) :=
  measurable_fst.prodMk (measurable_snd.comp measurable_snd)

lemma measurable_est' : Measurable fun s : TState X ι => T.est s.1 s.2.2 :=
  Measurable.comp (g := fun p : (X → ℕ) × (ι → ℝ) => T.est p.1 p.2)
    (f := fun s : TState X ι => ((s.1, s.2.2) : (X → ℕ) × (ι → ℝ))) T.measurable_est
    measurable_proj

lemma measurable_selA (hT : T.Meas) (k : ℕ) : Measurable (T.selA k) := by
  refine measurable_pick _ fun a => ?_
  have : {θh | a ∈ T.elig k θh} = ⋂ b, {θh | Real.sqrt (2 * T.oc k θh b) - zetaK k ≤
      Real.sqrt (2 * T.oc k θh a)} := by
    ext θh
    simp [elig]
  rw [this]
  exact MeasurableSet.iInter fun b =>
    measurableSet_le (((hT.oc k b).const_mul 2).sqrt.sub_const _) ((hT.oc k a).const_mul 2).sqrt

lemma measurable_plan (hT : T.Meas) (k : ℕ) : Measurable (T.plan k) := by
  have h : Measurable fun p : (ι → ℝ) × 𝒜 => T.ow k p.1 p.2 :=
    measurable_from_prod_countable_left fun a => hT.ow k a
  exact h.comp (measurable_id.prodMk (T.measurable_selA hT k))

lemma measurable_amax {β : Type*} [MeasurableSpace β] {d : β → X → ℝ} (hd : Measurable d) :
    Measurable fun b => amax (d b) := by
  refine measurable_pick _ fun x => ?_
  have : {b | x ∈ univ.filter fun x'' => ∀ x', d b x' ≤ d b x''} =
      ⋂ x', {b | d b x' ≤ d b x} := by
    ext b
    simp
  rw [this]
  exact MeasurableSet.iInter fun x' =>
    measurableSet_le ((measurable_pi_apply x').comp hd) ((measurable_pi_apply x).comp hd)

lemma measurable_nextQ (hT : T.Meas) (k : ℕ) : Measurable (T.nextQ k) := by
  refine measurable_amax (measurable_pi_iff.mpr fun x => ?_)
  have h1 : Measurable fun s : TState X ι => s.2.1 x :=
    (measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)
  have h2 : Measurable fun s : TState X ι => T.plan k (T.est s.1 s.2.2) x :=
    (measurable_pi_apply x).comp ((T.measurable_plan hT k).comp T.measurable_est')
  have h3 : Measurable fun s : TState X ι => ((s.1 x : ℕ) : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_pi_apply x).comp measurable_fst)
  exact (h1.add h2).sub h3

lemma measurable_upd (hT : T.Meas) (k : ℕ) :
    Measurable fun p : TState X ι × ℝ => T.upd k p.1 p.2 := by
  have hx : Measurable fun p : TState X ι × ℝ => T.nextQ k p.1 :=
    (T.measurable_nextQ hT k).comp measurable_fst
  unfold upd
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · have hg : Measurable fun q : (X → ℕ) × X => Function.update q.1 q.2 (q.1 q.2 + 1) :=
      Measurable.of_discrete
    exact hg.comp ((measurable_fst.comp measurable_fst).prodMk hx)
  · refine measurable_pi_iff.mpr fun x => ?_
    exact ((measurable_pi_apply x).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).add
      ((measurable_pi_apply x).comp
        (((T.measurable_plan hT k).comp T.measurable_est').comp measurable_fst))
  · have hg : Measurable fun q : ((ι → ℝ) × ℝ) × X =>
        q.1.1 + (q.1.2 / Real.sqrt (T.v q.2)) • T.u q.2 := by
      refine measurable_from_prod_countable_left fun x => ?_
      refine measurable_pi_iff.mpr fun i => ?_
      show Measurable fun q : (ι → ℝ) × ℝ => q.1 i + q.2 / Real.sqrt (T.v x) * T.u x i
      exact ((measurable_pi_apply i).comp measurable_fst).add
        ((measurable_snd.div_const _).mul_const _)
    have hf : Measurable fun p : TState X ι × ℝ =>
        (((p.1.2.2, p.2), T.nextQ k p.1) : ((ι → ℝ) × ℝ) × X) :=
      (((measurable_snd.comp measurable_snd).comp measurable_fst).prodMk measurable_snd).prodMk hx
    exact Measurable.comp (g := fun q : ((ι → ℝ) × ℝ) × X =>
        q.1.1 + (q.1.2 / Real.sqrt (T.v q.2)) • T.u q.2)
      (f := fun p : TState X ι × ℝ => (((p.1.2.2, p.2), T.nextQ k p.1) : ((ι → ℝ) × ℝ) × X))
      hg hf

lemma st_ofFn_succ (k : ℕ) (y : Fin (k + 1) → ℝ) :
    T.st (List.ofFn y) = T.upd k (T.st (List.ofFn (Fin.tail y))) (y 0) := by
  rw [ofFn_eq k y, st, List.length_ofFn]

lemma measurable_st (hT : T.Meas) : ∀ k, Measurable fun y : Fin k → ℝ => T.st (List.ofFn y)
  | 0 => by
    have : (fun y : Fin 0 → ℝ => T.st (List.ofFn y)) = fun _ => T.st [] := by
      funext y
      simp
    rw [this]
    exact measurable_const
  | k + 1 => by
    have e : (fun y : Fin (k + 1) → ℝ => T.st (List.ofFn y)) =
        (fun p : TState X ι × ℝ => T.upd k p.1 p.2) ∘
          (fun y : Fin (k + 1) → ℝ => (T.st (List.ofFn (Fin.tail y)), y 0)) := by
      funext y
      exact T.st_ofFn_succ k y
    rw [e]
    have h1 : Measurable fun y : Fin (k + 1) → ℝ => T.st (List.ofFn (Fin.tail y)) :=
      Measurable.comp (g := fun y : Fin k → ℝ => T.st (List.ofFn y)) (measurable_st hT k)
        (measurable_tail k)
    exact (T.measurable_upd hT k).comp (h1.prodMk (measurable_pi_apply 0))

lemma measurable_thr (δ : ℝ) : Measurable (T.thr δ) := by
  have h : Measurable fun p : (X → ℕ) × (ι → ℝ) => mixThreshold δ T.γ (T.Gm p.1) p.2 := by
    refine measurable_from_prod_countable_right fun N => ?_
    have hq : ∀ M : Matrix ι ι ℝ, Measurable fun b : ι → ℝ => b ⬝ᵥ M *ᵥ b := fun M =>
      measurable_qform measurable_id measurable_const measurable_id
    show Measurable fun b : ι → ℝ => Real.log (1 / δ) +
      1 / 2 * Real.log (1 + T.γ⁻¹ • T.Gm N).det +
      1 / 2 * (b ⬝ᵥ (T.Gm N)⁻¹ *ᵥ b - b ⬝ᵥ (T.Gm N + T.γ • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ b)
    exact (((hq (T.Gm N)⁻¹).sub (hq (T.Gm N + T.γ • (1 : Matrix ι ι ℝ))⁻¹)).const_mul
      (1 / 2)).const_add (Real.log (1 / δ) + 1 / 2 * Real.log (1 + T.γ⁻¹ • T.Gm N).det)
  exact Measurable.comp (g := fun p : (X → ℕ) × (ι → ℝ) => mixThreshold δ T.γ (T.Gm p.1) p.2)
    (f := fun s : TState X ι => ((s.1, s.2.2) : (X → ℕ) × (ι → ℝ))) h measurable_proj

lemma measurable_stat (a : 𝒜) : Measurable (T.stat a) := by
  have h : Measurable fun p : (X → ℕ) × (ι → ℝ) =>
      gInfo T.uE (T.Q a) (WithLp.toLp 2 (T.est p.1 p.2)) (fun x => (p.1 x : ℝ)) := by
    refine measurable_from_prod_countable_right fun N => ?_
    have h1 : Measurable fun b : ι → ℝ => (WithLp.toLp 2 (T.est N b) : EuclideanSpace ℝ ι) :=
      Measurable.comp (g := fun z : ι → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ ι))
        (f := fun b : ι → ℝ => T.est N b) (WithLp.measurable_toLp 2 _)
        (T.measurable_est_right N)
    have h2 : Continuous (designMap T.uE fun x => (N x : ℝ)) :=
      LinearMap.continuous_of_finiteDimensional _
    have h3 : Measurable fun b : ι → ℝ =>
        designMap T.uE (fun x => (N x : ℝ)) (WithLp.toLp 2 (T.est N b)) :=
      Measurable.comp (g := fun z : EuclideanSpace ℝ ι => designMap T.uE (fun x => (N x : ℝ)) z)
        (f := fun b : ι → ℝ => (WithLp.toLp 2 (T.est N b) : EuclideanSpace ℝ ι))
        h2.measurable h1
    have h4 : Measurable fun b : ι → ℝ =>
        Metric.infDist (designMap T.uE (fun x => (N x : ℝ)) (WithLp.toLp 2 (T.est N b)))
          (designMap T.uE (fun x => (N x : ℝ)) '' T.Q a) :=
      Measurable.comp (g := fun z : EuclideanSpace ℝ X =>
          Metric.infDist z (designMap T.uE (fun x => (N x : ℝ)) '' T.Q a))
        (f := fun b : ι → ℝ => designMap T.uE (fun x => (N x : ℝ)) (WithLp.toLp 2 (T.est N b)))
        (Metric.continuous_infDist_pt _).measurable h3
    exact (h4.pow_const 2).div_const 2
  exact Measurable.comp (g := fun p : (X → ℕ) × (ι → ℝ) =>
      gInfo T.uE (T.Q a) (WithLp.toLp 2 (T.est p.1 p.2)) (fun x => (p.1 x : ℝ)))
    (f := fun s : TState X ι => ((s.1, s.2.2) : (X → ℕ) × (ι → ℝ))) h measurable_proj

lemma measurableSet_stopP (δ : ℝ) : MeasurableSet {s : TState X ι | T.stopP δ s} := by
  have h1 : MeasurableSet {s : TState X ι | ∃ lam, 0 < lam ∧ Coercive (T.Gm s.1) lam} :=
    measurable_fst
      (MeasurableSet.of_discrete (s := {N : X → ℕ | ∃ lam, 0 < lam ∧ Coercive (T.Gm N) lam}))
  have h2 : MeasurableSet {s : TState X ι | ∃ a, T.thr δ s ≤ T.stat a s} := by
    have : {s : TState X ι | ∃ a, T.thr δ s ≤ T.stat a s} =
        ⋃ a, {s | T.thr δ s ≤ T.stat a s} := by
      ext s
      simp
    rw [this]
    exact MeasurableSet.iUnion fun a => measurableSet_le (T.measurable_thr δ) (T.measurable_stat a)
  exact h1.inter h2

/-- **The likelihood-certified information tracker** at confidence `δ`, as a sampler: query
the experiment with the largest deficit of the cumulative target designs; stop when `G_t`
is invertible and some `J_t(a) ≥ H_t(δ)`. -/
def sampler (hT : T.Meas) (δ : ℝ) : GSampler X where
  next h := T.nextQ h.length (T.st h)
  stop h := if T.stopP δ (T.st h) then true else false
  meas_next k := by
    have : (fun y : Fin k → ℝ => T.nextQ (List.ofFn y).length (T.st (List.ofFn y))) =
        fun y => T.nextQ k (T.st (List.ofFn y)) := by
      funext y
      rw [List.length_ofFn]
    rw [this]
    exact (T.measurable_nextQ hT k).comp (T.measurable_st hT k)
  meas_stop k :=
    Measurable.ite ((T.measurable_st hT k) (T.measurableSet_stopP δ)) measurable_const
      measurable_const

/-- The answer returned at stopping: a certified action. -/
def decision (hT : T.Meas) (δ : ℝ) : GDecision 𝒜 where
  dec h := pick (T.certSet δ (T.st h))
  meas_dec k := by
    refine measurable_pick _ fun a => ?_
    have : {y : Fin k → ℝ | a ∈ T.certSet δ (T.st (List.ofFn y))} =
        (fun y : Fin k → ℝ => T.st (List.ofFn y)) ⁻¹' {s | T.thr δ s ≤ T.stat a s} := by
      ext y
      simp [certSet]
    rw [this]
    exact (T.measurable_st hT k) (measurableSet_le (T.measurable_thr δ) (T.measurable_stat a))

lemma sampler_stop_iff (hT : T.Meas) (δ : ℝ) (h : List ℝ) :
    (T.sampler hT δ).stop h = true ↔ T.stopP δ (T.st h) := by
  simp [sampler]

/-- The allocation rule does not depend on `δ`. -/
lemma free_sampler (hT : T.Meas) (δ δ' : ℝ) : free (T.sampler hT δ) = free (T.sampler hT δ') :=
  rfl

/-- The unstopped run of the allocation rule under the parameter `θ`. -/
def path (hT : T.Meas) (θ : ι → ℝ) (n : ℕ) (ω : ℕ → ℝ) : List ℝ :=
  run (T.sampler hT 1) (T.mean θ) T.v n ω

lemma run_eq_path (hT : T.Meas) (δ : ℝ) (θ : ι → ℝ) (n : ℕ) (ω : ℕ → ℝ) :
    run (T.sampler hT δ) (T.mean θ) T.v n ω = T.path hT θ n ω := rfl

end Tracker

namespace Tracker

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]
variable [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]
variable (T : Tracker X ι 𝒜)

/-- The hypotheses on the model and the oracle contract `eq:bay-oracle-contract`.
`ℓ` bounds the feature norms, `κ` is the least eigenvalue bound of the reference design
(`M(w⁰) ⪰ κ I`), `A0` bounds one anchor in each alternative set. -/
structure Valid (ℓ κ A0 : ℝ) : Prop where
  hv : ∀ x, 0 < T.v x
  hw0 : T.w0 ∈ simplex X
  hγ : 0 < T.γ
  hℓ : 0 < ℓ
  hu : ∀ x, T.u x ⬝ᵥ T.u x ≤ ℓ ^ 2
  hκ : 0 < κ
  hspan : ∀ e : ι → ℝ, κ * (e ⬝ᵥ e) ≤ ∑ x, T.w0 x * (T.u x ⬝ᵥ e) ^ 2
  hQ : ∀ a, ∃ lam ∈ T.Q a, ‖lam‖ ≤ A0
  floor : ∀ k θh a, ∃ p ∈ simplex X,
    T.ow k θh a = fun x => (1 - etaK k) * p x + etaK k * T.w0 x
  lower : ∀ k θh a, 0 ≤ T.oc k θh a ∧
    T.oc k θh a ≤ gInfo T.uE (T.Q a) (WithLp.toLp 2 θh) (T.ow k θh a)
  near : ∀ k θh a, ∀ w ∈ simplex X,
    gInfo T.uE (T.Q a) (WithLp.toLp 2 θh) w - T.oc k θh a ≤
      etaK k * (ℓ ^ 2 * (‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ + 1 + A0) ^ 2 / 2) + etaK k

variable (hT : T.Meas) (θ : ι → ℝ)

/-- State after `k` observations of the unstopped run. -/
def S (k : ℕ) (ω : ℕ → ℝ) : TState X ι := T.st (T.path hT θ k ω)

/-- The experiment queried at step `k` (rounds are indexed from `0`). -/
def qry (k : ℕ) (ω : ℕ → ℝ) : X := T.nextQ k (T.S hT θ k ω)

/-- The estimate `θ̂_k` after `k` observations. -/
def thetaHat (k : ℕ) (ω : ℕ → ℝ) : ι → ℝ := T.est (T.S hT θ k ω).1 (T.S hT θ k ω).2.2

/-- The target design used at step `k`. -/
def pl (k : ℕ) (ω : ℕ → ℝ) : X → ℝ := T.plan k (T.thetaHat hT θ k ω)

lemma path_succ (k : ℕ) (ω : ℕ → ℝ) :
    T.path hT θ (k + 1) ω =
      (T.mean θ (T.qry hT θ k ω) + Real.sqrt (T.v (T.qry hT θ k ω)) * ω k) ::
        T.path hT θ k ω := by
  have h : (T.sampler hT 1).next (run (T.sampler hT 1) (T.mean θ) T.v k ω) =
      T.qry hT θ k ω := by
    show T.nextQ (run (T.sampler hT 1) (T.mean θ) T.v k ω).length
      (T.st (run (T.sampler hT 1) (T.mean θ) T.v k ω)) = _
    rw [length_run]
    rfl
  unfold path
  rw [run_succ, h]

lemma S_zero (ω : ℕ → ℝ) : T.S hT θ 0 ω = (0, 0, 0) := by
  unfold S path
  rw [run_zero]
  rfl

lemma S_succ (k : ℕ) (ω : ℕ → ℝ) :
    T.S hT θ (k + 1) ω = T.upd k (T.S hT θ k ω)
      (T.mean θ (T.qry hT θ k ω) + Real.sqrt (T.v (T.qry hT θ k ω)) * ω k) := by
  have hl : (T.path hT θ k ω).length = k := length_run _ _ _ _ _
  unfold S
  rw [path_succ]
  show T.upd (T.path hT θ k ω).length (T.st (T.path hT θ k ω)) _ = _
  rw [hl]

lemma N_succ' (k : ℕ) (ω : ℕ → ℝ) :
    (T.S hT θ (k + 1) ω).1 = Function.update (T.S hT θ k ω).1 (T.qry hT θ k ω)
      ((T.S hT θ k ω).1 (T.qry hT θ k ω) + 1) := by
  rw [S_succ]
  rfl

lemma N_succ (k : ℕ) (ω : ℕ → ℝ) (x' : X) :
    (T.S hT θ (k + 1) ω).1 x' =
      (T.S hT θ k ω).1 x' + if T.qry hT θ k ω = x' then 1 else 0 := by
  rw [N_succ']
  by_cases h : T.qry hT θ k ω = x'
  · subst h
    simp
  · simp [h, Function.update_of_ne (Ne.symm h)]

lemma N_eq_pulls (ω : ℕ → ℝ) : ∀ (k : ℕ) (x : X),
    (T.S hT θ k ω).1 x = pulls (fun j => T.qry hT θ j ω) x k
  | 0, x => by
    rw [S_zero]
    simp [pulls]
  | k + 1, x => by
    rw [N_succ, pulls_succ, N_eq_pulls ω k x]

lemma W_succ (k : ℕ) (ω : ℕ → ℝ) :
    (T.S hT θ (k + 1) ω).2.1 = (T.S hT θ k ω).2.1 + T.pl hT θ k ω := by
  rw [S_succ]
  rfl

lemma W_eq (ω : ℕ → ℝ) : ∀ (k : ℕ) (x : X),
    (T.S hT θ k ω).2.1 x = cumTarget (fun j => T.pl hT θ j ω) x k
  | 0, x => by
    rw [S_zero]
    simp [cumTarget]
  | k + 1, x => by
    rw [W_succ, cumTarget, sum_range_succ, Pi.add_apply, W_eq ω k x]
    rfl

lemma b_succ (hv : ∀ x, 0 < T.v x) (k : ℕ) (ω : ℕ → ℝ) :
    (T.S hT θ (k + 1) ω).2.2 = (T.S hT θ k ω).2.2 +
      (T.u (T.qry hT θ k ω) ⬝ᵥ θ + ω k) • T.u (T.qry hT θ k ω) := by
  rw [S_succ]
  show (T.S hT θ k ω).2.2 + ((T.mean θ (T.qry hT θ k ω) +
    Real.sqrt (T.v (T.qry hT θ k ω)) * ω k) / Real.sqrt (T.v (T.qry hT θ k ω))) •
      T.u (T.qry hT θ k ω) = _
  have hs : Real.sqrt (T.v (T.qry hT θ k ω)) ≠ 0 := (Real.sqrt_pos.mpr (hv _)).ne'
  congr 2
  unfold mean
  field_simp

lemma Gm_update (N : X → ℕ) (x : X) :
    T.Gm (Function.update N x (N x + 1)) = T.Gm N + vecMulVec (T.u x) (T.u x) := by
  have h : ∀ x', ((Function.update N x (N x + 1) x' : ℕ) : ℝ) =
      (N x' : ℝ) + if x' = x then 1 else 0 := by
    intro x'
    by_cases hx : x' = x
    · subst hx
      simp
    · simp [hx]
  unfold Gm
  simp_rw [h, add_smul, sum_add_distrib]
  congr 1
  simp [ite_smul]

lemma Gm_zero : T.Gm (0 : X → ℕ) = 0 := by
  simp [Gm]

lemma Gm_eq (ω : ℕ → ℝ) : ∀ k : ℕ,
    T.Gm (T.S hT θ k ω).1 = gram (fun j => T.u (T.qry hT θ j ω)) k
  | 0 => by
    rw [S_zero]
    simp [Gm, gram]
  | k + 1 => by
    rw [N_succ', Gm_update, Gm_eq ω k, gram, gram, sum_range_succ]

/-- The noise sum `S_k = ∑_{j < k} ν_j u_{X_j}`. -/
def noiseSum (k : ℕ) (ω : ℕ → ℝ) : ι → ℝ := ∑ j ∈ range k, ω j • T.u (T.qry hT θ j ω)

lemma b_decomp (hv : ∀ x, 0 < T.v x) (ω : ℕ → ℝ) : ∀ k : ℕ,
    (T.S hT θ k ω).2.2 = T.Gm (T.S hT θ k ω).1 *ᵥ θ + T.noiseSum hT θ k ω
  | 0 => by
    rw [S_zero]
    simp [Gm, noiseSum]
  | k + 1 => by
    rw [b_succ T hT θ hv, N_succ', Gm_update, b_decomp hv ω k, noiseSum, noiseSum,
      sum_range_succ, add_mulVec, vecMulVec_self_mulVec, add_smul]
    abel

lemma b_eq (hv : ∀ x, 0 < T.v x) (ω : ℕ → ℝ) : ∀ k : ℕ,
    (T.S hT θ k ω).2.2 =
      bayB (fun j ω => T.u (T.qry hT θ j ω)) (fun j ω => ω j) θ k ω
  | 0 => by
    rw [S_zero]
    simp [bayB]
  | k + 1 => by
    rw [b_succ T hT θ hv, b_eq hv ω k, bayB, bayB, sum_range_succ]

lemma Gm_symm (N : X → ℕ) : (T.Gm N)ᵀ = T.Gm N := by
  unfold Gm
  rw [transpose_sum]
  refine sum_congr rfl fun x _ => ?_
  ext i j
  simp [vecMulVec_apply, mul_comm]

lemma quad_Gm (N : X → ℕ) (e : ι → ℝ) :
    e ⬝ᵥ T.Gm N *ᵥ e = ∑ x, (N x : ℝ) * (T.u x ⬝ᵥ e) ^ 2 := by
  unfold Gm
  rw [sum_mulVec, dotProduct_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [smul_mulVec, vecMulVec_self_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm e (T.u x)]
  ring

variable {ℓ κ A0 : ℝ}

lemma dot_sq_le (hV : T.Valid ℓ κ A0) (x : X) (e : ι → ℝ) :
    (T.u x ⬝ᵥ e) ^ 2 ≤ ℓ ^ 2 * (e ⬝ᵥ e) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (T.u x) e
  have h1 : ∑ i, T.u x i ^ 2 = T.u x ⬝ᵥ T.u x := by
    simp [dotProduct, sq]
  have h2 : ∑ i, e i ^ 2 = e ⬝ᵥ e := by
    simp [dotProduct, sq]
  rw [h1, h2] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hV.hu x) (dotProduct_self_nonneg' e))

lemma plan_mem (hV : T.Valid ℓ κ A0) (k : ℕ) (θh : ι → ℝ) : T.plan k θh ∈ simplex X := by
  obtain ⟨p, hp, he⟩ := hV.floor k θh (T.selA k θh)
  unfold plan
  rw [he]
  exact floorDesign_mem (etaK_pos k).le (etaK_le_one k) hV.hw0 hp

lemma plan_ge (hV : T.Valid ℓ κ A0) (k : ℕ) (θh : ι → ℝ) (x : X) :
    etaK k * T.w0 x ≤ T.plan k θh x := by
  obtain ⟨p, hp, he⟩ := hV.floor k θh (T.selA k θh)
  unfold plan
  rw [he]
  have := mul_nonneg (sub_nonneg.mpr (etaK_le_one k)) (hp.1 x)
  simp only
  linarith

/-- **Tracking discrepancy** along the run: `-(m - 1) ≤ N_x(k) - W_x(k) ≤ 1`. -/
lemma track (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) (x : X) :
    -((Fintype.card X : ℝ) - 1) ≤ ((T.S hT θ k ω).1 x : ℝ) - (T.S hT θ k ω).2.1 x ∧
      ((T.S hT θ k ω).1 x : ℝ) - (T.S hT θ k ω).2.1 x ≤ 1 := by
  have h := tracking_discrepancy (fun j => T.pl hT θ j ω) (fun j => T.plan_mem hV _ _)
    (fun j => T.qry hT θ j ω) (fun t x' => ?_) k x
  · rwa [← N_eq_pulls, ← W_eq] at h
  · have h1 := amax_spec (fun x => (T.S hT θ t ω).2.1 x +
      T.plan t (T.est (T.S hT θ t ω).1 (T.S hT θ t ω).2.2) x - ((T.S hT θ t ω).1 x : ℝ)) x'
    have hc : ∀ y, cumTarget (fun j => T.pl hT θ j ω) y (t + 1) =
        (T.S hT θ t ω).2.1 y + T.plan t (T.est (T.S hT θ t ω).1 (T.S hT θ t ω).2.2) y := by
      intro y
      rw [cumTarget, sum_range_succ, W_eq]
      rfl
    rw [hc, hc, ← N_eq_pulls, ← N_eq_pulls]
    exact h1

/-- Cumulative exploration `E_k = ∑_{j < k} η_j`. -/
def cumEta (k : ℕ) : ℝ := ∑ j ∈ range k, etaK j

lemma cumEta_nonneg (k : ℕ) : 0 ≤ cumEta k := sum_nonneg fun j _ => (etaK_pos j).le

lemma etaK_anti {j k : ℕ} (h : j ≤ k) : etaK k ≤ etaK j := by
  unfold etaK
  exact pow_le_pow_left₀ (inv_pos.mpr (rk_pos k)).le
    (inv_anti₀ (rk_pos j) (rk_mono h)) 4

lemma cumEta_ge {k : ℕ} (hk : 1 ≤ k) : rk k ^ 12 / 2 ≤ cumEta k := by
  have h1 : (k : ℝ) * etaK k ≤ cumEta k := by
    unfold cumEta
    calc (k : ℝ) * etaK k = ∑ _j ∈ range k, etaK k := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ range k, etaK j :=
          sum_le_sum fun j hj => etaK_anti (Finset.mem_range.1 hj).le
  have hr := rk_pow k
  have hr0 := rk_pos k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : rk k ^ 12 / 2 ≤ (k : ℝ) * etaK k := by
    unfold etaK
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hr0 4)]
    have e : rk k ^ 12 / 2 * rk k ^ 4 = rk k ^ 16 / 2 := by ring
    rw [e, hr]
    linarith
  linarith

lemma W_ge (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) (x : X) :
    T.w0 x * cumEta k ≤ (T.S hT θ k ω).2.1 x := by
  rw [W_eq, cumTarget, cumEta, mul_sum]
  refine sum_le_sum fun j _ => ?_
  have := T.plan_ge hV j (T.thetaHat hT θ j ω) x
  unfold pl
  linarith

/-- `G_k ⪰ (κ E_k - m (m - 1) ℓ²) I` on every path: the exploration floor and the tracking
bound make the Gram matrix invertible after a deterministic onset. -/
lemma coercive_run (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) :
    Coercive (T.Gm (T.S hT θ k ω).1)
      (κ * cumEta k - (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1) * ℓ ^ 2) := by
  refine ⟨T.Gm_symm _, fun e => ?_⟩
  rw [quad_Gm]
  have hm : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 1 := by
    have : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
    linarith
  have hee := dotProduct_self_nonneg' e
  have h1 : ∑ x, (T.w0 x * cumEta k - ((Fintype.card X : ℝ) - 1)) * (T.u x ⬝ᵥ e) ^ 2 ≤
      ∑ x, ((T.S hT θ k ω).1 x : ℝ) * (T.u x ⬝ᵥ e) ^ 2 := by
    refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := (T.track hT θ hV ω k x).1
    have := T.W_ge hT θ hV ω k x
    linarith
  have h2 : ∑ x, (T.w0 x * cumEta k - ((Fintype.card X : ℝ) - 1)) * (T.u x ⬝ᵥ e) ^ 2 =
      cumEta k * ∑ x, T.w0 x * (T.u x ⬝ᵥ e) ^ 2 -
        ((Fintype.card X : ℝ) - 1) * ∑ x, (T.u x ⬝ᵥ e) ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  have h3 : ∑ x, (T.u x ⬝ᵥ e) ^ 2 ≤ (Fintype.card X : ℝ) * (ℓ ^ 2 * (e ⬝ᵥ e)) := by
    calc ∑ x, (T.u x ⬝ᵥ e) ^ 2 ≤ ∑ _x : X, ℓ ^ 2 * (e ⬝ᵥ e) :=
          sum_le_sum fun x _ => T.dot_sq_le hV x e
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have h4 := mul_le_mul_of_nonneg_left (hV.hspan e) (cumEta_nonneg k)
  have h5 := mul_le_mul_of_nonneg_left h3 hm
  rw [h2] at h1
  nlinarith

/-- The error equation `G_k (θ̂_k - θ) = S_k` at invertible `G_k`. -/
lemma err_eq (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hc : Coercive (T.Gm (T.S hT θ k ω).1) lam) :
    T.Gm (T.S hT θ k ω).1 *ᵥ (T.thetaHat hT θ k ω - θ) = T.noiseSum hT θ k ω := by
  have h1 : T.Gm (T.S hT θ k ω).1 *ᵥ T.thetaHat hT θ k ω = (T.S hT θ k ω).2.2 :=
    hc.mul_inv_mulVec hlam _
  rw [mulVec_sub, h1, T.b_decomp hT θ hV.hv ω k]
  abel

/-- Deterministic estimation error: if every coordinate of the noise sum is at most `a` in
absolute value and `G_k ⪰ lam I`, then `lam² ‖θ̂_k - θ‖² ≤ d a²`. -/
lemma err_bound (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) {lam a : ℝ} (hlam : 0 < lam)
    (hc : Coercive (T.Gm (T.S hT θ k ω).1) lam)
    (ha : ∀ i, |T.noiseSum hT θ k ω i| ≤ a) :
    lam ^ 2 * ((T.thetaHat hT θ k ω - θ) ⬝ᵥ (T.thetaHat hT θ k ω - θ)) ≤
      (Fintype.card ι : ℝ) * a ^ 2 := by
  set e := T.thetaHat hT θ k ω - θ with he
  set s := T.noiseSum hT θ k ω with hs
  have h1 : lam * (e ⬝ᵥ e) ≤ e ⬝ᵥ s := by
    have := hc.coer e
    rwa [T.err_eq hT θ hV ω k hlam hc] at this
  have h2 : (e ⬝ᵥ s) ^ 2 ≤ (e ⬝ᵥ e) * (s ⬝ᵥ s) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq univ e s
    have e1 : ∑ i, e i ^ 2 = e ⬝ᵥ e := by simp [dotProduct, sq]
    have e2 : ∑ i, s i ^ 2 = s ⬝ᵥ s := by simp [dotProduct, sq]
    rw [e1, e2] at h
    exact h
  have h3 : s ⬝ᵥ s ≤ (Fintype.card ι : ℝ) * a ^ 2 := by
    calc s ⬝ᵥ s = ∑ i, s i ^ 2 := by simp [dotProduct, sq]
      _ ≤ ∑ _i : ι, a ^ 2 := sum_le_sum fun i _ => by
          have := ha i
          exact sq_le_sq' (by linarith [neg_abs_le (s i)]) (by linarith [le_abs_self (s i)])
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hee := dotProduct_self_nonneg' e
  have hss := dotProduct_self_nonneg' s
  rcases hee.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    positivity
  · have h4 : (lam * (e ⬝ᵥ e)) ^ 2 ≤ (e ⬝ᵥ e) * (s ⬝ᵥ s) :=
      (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    have h5 : lam ^ 2 * (e ⬝ᵥ e) ≤ s ⬝ᵥ s := by
      have h6 : (lam * (e ⬝ᵥ e)) ^ 2 = (e ⬝ᵥ e) * (lam ^ 2 * (e ⬝ᵥ e)) := by ring
      rw [h6] at h4
      exact le_of_mul_le_mul_left h4 hpos
    linarith

end Tracker

namespace Tracker

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]
variable [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]
variable (T : Tracker X ι 𝒜) (hT : T.Meas) (θ : ι → ℝ) {ℓ κ A0 : ℝ}

/-! ### Stage 2: concentration of the estimate along the run -/

lemma measurable_S (k : ℕ) : Measurable[tapeFilt k] (T.S hT θ k) :=
  measurable_tapeFilt_hist (free (T.sampler hT 1)) (T.mean θ) T.v k (T.measurable_st hT k)

lemma measurable_qry (k : ℕ) : Measurable[tapeFilt k] (T.qry hT θ k) :=
  (T.measurable_nextQ hT k).comp (T.measurable_S hT θ k)

lemma measurable_S' (k : ℕ) : Measurable (T.S hT θ k) :=
  (T.measurable_S hT θ k).mono (tapeFilt.le k) le_rfl

lemma measurable_thetaHat (k : ℕ) : Measurable (T.thetaHat hT θ k) :=
  T.measurable_est'.comp (T.measurable_S' hT θ k)

lemma noiseSum_apply (k : ℕ) (ω : ℕ → ℝ) (i : ι) :
    T.noiseSum hT θ k ω i = ∑ j ∈ range k, ω j * T.u (T.qry hT θ j ω) i := by
  simp [noiseSum, Finset.sum_apply]

/-- One-sided coordinate Chernoff bound for the noise sum with predictable Gaussian
increments. -/
lemma noise_tail_one (hV : T.Valid ℓ κ A0) {k : ℕ} (hk : 1 ≤ k) (i : ι) {sg : ℝ}
    (hsg : sg ^ 2 = 1) {a : ℝ} (ha : 0 < a) :
    gP.real {ω | a < sg * T.noiseSum hT θ k ω i} ≤ Real.exp (-(a ^ 2 / (2 * k * ℓ ^ 2))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓ := hV.hℓ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = a / (k * ℓ ^ 2) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  obtain ⟨vv, hvv⟩ : ∃ vv : ι → ℝ, vv = Pi.single i (sg * c) := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → (ℕ → ℝ) → ι → ℝ, φ = fun s ω => T.u (T.qry hT θ s ω) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℕ → (ℕ → ℝ) → ℝ, η = fun s ω => ω s := ⟨_, rfl⟩
  have hM : Supermartingale (expMart 1 vv η φ) tapeFilt gP := by
    refine expMart_supermartingale tapeFilt one_pos vv (fun s => ?_) (fun s => ?_) (fun s => ?_)
    · rw [hφ]
      exact (Measurable.of_discrete (f := T.u)).comp (T.measurable_qry hT θ s)
    · rw [hη]
      exact measurable_tapeFilt_coord (Nat.lt_succ_self s)
    · rw [hη]
      exact condSubG_coord s
  have hint : ∫ ω, expMart 1 vv η φ k ω ∂gP ≤ 1 := by
    have h := hM.setIntegral_le (Nat.zero_le k) (s := Set.univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    have h0 : expMart 1 vv η φ 0 = fun _ => 1 := by
      funext ω
      simp [expMart]
    rw [h0] at h
    simpa using h
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := gP)
    (ae_of_all _ fun ω => (Real.exp_pos _).le) (hM.integrable k)
    (Real.exp (a ^ 2 / (2 * k * ℓ ^ 2)))
  have hsub : {ω | a < sg * T.noiseSum hT θ k ω i} ⊆
      {ω | Real.exp (a ^ 2 / (2 * k * ℓ ^ 2)) ≤ expMart 1 vv η φ k ω} := by
    intro ω hω
    have hω' : a < sg * T.noiseSum hT θ k ω i := hω
    show Real.exp (a ^ 2 / (2 * k * ℓ ^ 2)) ≤ expMart 1 vv η φ k ω
    unfold expMart
    apply Real.exp_le_exp.mpr
    have hdot : ∀ s, vv ⬝ᵥ φ s ω = sg * c * T.u (T.qry hT θ s ω) i := fun s => by
      rw [hvv, hφ, single_dotProduct]
    have hsq : ∀ s, (T.u (T.qry hT θ s ω) i) ^ 2 ≤ ℓ ^ 2 := fun s => by
      refine le_trans ?_ (hV.hu (T.qry hT θ s ω))
      have := Finset.single_le_sum (f := fun j => T.u (T.qry hT θ s ω) j * T.u (T.qry hT θ s ω) j)
        (fun j _ => mul_self_nonneg _) (mem_univ i)
      simpa [dotProduct, sq] using this
    have hterm : ∀ s ∈ range k, sg * c * (ω s * T.u (T.qry hT θ s ω) i) - c ^ 2 * ℓ ^ 2 / 2 ≤
        η s ω * (vv ⬝ᵥ φ s ω) / 1 - (vv ⬝ᵥ φ s ω) ^ 2 / 2 := by
      intro s _
      rw [hdot, hη]
      have h1 : (sg * c * T.u (T.qry hT θ s ω) i) ^ 2 =
          c ^ 2 * (T.u (T.qry hT θ s ω) i) ^ 2 := by
        rw [mul_pow, mul_pow, hsg, one_mul]
      rw [h1, div_one]
      have := mul_le_mul_of_nonneg_left (hsq s) (sq_nonneg c)
      linarith
    have hsum := sum_le_sum hterm
    rw [sum_sub_distrib, ← mul_sum, ← T.noiseSum_apply hT θ k ω i, sum_const, card_range,
      nsmul_eq_mul] at hsum
    refine le_trans ?_ hsum
    have e1 : a ^ 2 / (2 * k * ℓ ^ 2) = c * a - k * (c ^ 2 * ℓ ^ 2 / 2) := by
      rw [hc]
      field_simp
      ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hω'.le hcpos.le
    linarith
  have h1 : Real.exp (a ^ 2 / (2 * k * ℓ ^ 2)) * gP.real {ω | a < sg * T.noiseSum hT θ k ω i} ≤
      1 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le).trans
      (hmark.trans hint)
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
  linarith

/-- Coordinate Chernoff bound: `P(∃ i, |S_{k,i}| > a) ≤ 2 d exp (-a² / (2 k ℓ²))`. -/
lemma noise_tail (hV : T.Valid ℓ κ A0) {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) :
    gP {ω | ∃ i, a < |T.noiseSum hT θ k ω i|} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * Real.exp (-(a ^ 2 / (2 * k * ℓ ^ 2))))) := by
  have hone : ∀ i, gP {ω | a < |T.noiseSum hT θ k ω i|} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * k * ℓ ^ 2)))) := by
    intro i
    have hsub : {ω | a < |T.noiseSum hT θ k ω i|} ⊆
        {ω | a < 1 * T.noiseSum hT θ k ω i} ∪ {ω | a < (-1) * T.noiseSum hT θ k ω i} := by
      intro ω hω
      have hω' : a < |T.noiseSum hT θ k ω i| := hω
      rcases lt_abs.mp hω' with h | h
      · left
        show a < 1 * T.noiseSum hT θ k ω i
        linarith
      · right
        show a < (-1) * T.noiseSum hT θ k ω i
        linarith
    have h1 := T.noise_tail_one hT θ hV hk i (sg := 1) (by norm_num) ha
    have h2 := T.noise_tail_one hT θ hV hk i (sg := -1) (by norm_num) ha
    have h3 : gP.real {ω | a < |T.noiseSum hT θ k ω i|} ≤
        2 * Real.exp (-(a ^ 2 / (2 * k * ℓ ^ 2))) := by
      have := (measureReal_mono (μ := gP) hsub).trans (measureReal_union_le _ _)
      linarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top gP _)]
    exact ENNReal.ofReal_le_ofReal h3
  have hU : {ω | ∃ i, a < |T.noiseSum hT θ k ω i|} = ⋃ i, {ω | a < |T.noiseSum hT θ k ω i|} := by
    ext ω
    simp
  rw [hU]
  refine (measure_iUnion_fintype_le gP _).trans ?_
  calc ∑ i : ι, gP {ω | a < |T.noiseSum hT θ k ω i|}
      ≤ ∑ _i : ι, ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * k * ℓ ^ 2)))) :=
        sum_le_sum fun i _ => hone i
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * Real.exp (-(a ^ 2 / (2 * k * ℓ ^ 2))))) := by
        rw [sum_const, card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- Squared estimation error `‖θ̂_k - θ‖₂²`. -/
def errSq (k : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (T.thetaHat hT θ k ω - θ) ⬝ᵥ (T.thetaHat hT θ k ω - θ)

lemma measurable_errSq (k : ℕ) : Measurable (T.errSq hT θ k) :=
  measurable_dotProduct ((T.measurable_thetaHat hT θ k).sub measurable_const)
    ((T.measurable_thetaHat hT θ k).sub measurable_const)

/-- The estimate is bad at time `k` if `‖θ̂_k - θ‖ > (k + 1)^{-1/8}`. -/
def bad (k : ℕ) : Set (ℕ → ℝ) := {ω | (rk k)⁻¹ ^ 4 < T.errSq hT θ k ω}

lemma measurableSet_bad (k : ℕ) : MeasurableSet (T.bad hT θ k) :=
  measurableSet_lt measurable_const (T.measurable_errSq hT θ k)

/-- Deterministic onset after which `G_k ⪰ (κ/4) (k+1)^{3/4} I`. -/
def onset (m : ℕ) (ℓ κ : ℝ) : ℕ := ⌈(4 * ((m : ℝ) * ((m : ℝ) - 1) * ℓ ^ 2) / κ) ^ 2⌉₊ + 1

lemma Coercive_mono {V : Matrix ι ι ℝ} {lam lam' : ℝ} (h : Coercive V lam) (hl : lam' ≤ lam) :
    Coercive V lam' :=
  ⟨h.symm, fun x => (mul_le_mul_of_nonneg_right hl (dotProduct_self_nonneg' x)).trans (h.coer x)⟩

lemma coercive_onset (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) {k : ℕ}
    (hk : onset (Fintype.card X) ℓ κ ≤ k) :
    Coercive (T.Gm (T.S hT θ k ω).1) (κ * rk k ^ 12 / 4) := by
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 _) hk
  refine Coercive_mono (T.coercive_run hT θ hV ω k) ?_
  have hE := cumEta_ge hk1
  have hκ := hV.hκ
  have hr1 := one_le_rk k
  obtain ⟨cm, hcm⟩ : ∃ cm : ℝ, cm = (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1) * ℓ ^ 2 :=
    ⟨_, rfl⟩
  have hcm0 : 0 ≤ cm := by
    have : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
    rw [hcm]
    have h1 : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 1 := by linarith
    positivity
  rw [← hcm]
  have hk2 : (4 * cm / κ) ^ 2 ≤ (k : ℝ) + 1 := by
    have h1 : (4 * cm / κ) ^ 2 ≤ ⌈(4 * cm / κ) ^ 2⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(4 * cm / κ) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ k := by
      have : onset (Fintype.card X) ℓ κ = ⌈(4 * cm / κ) ^ 2⌉₊ + 1 := by rw [onset, hcm]
      rw [← this]
      exact_mod_cast hk
    push_cast at h2
    linarith
  have h8 : 4 * cm / κ ≤ rk k ^ 8 := by
    have h1 : (rk k ^ 8) ^ 2 = (k : ℝ) + 1 := by rw [← pow_mul]; exact rk_pow k
    rw [← h1] at hk2
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hk2
  have h12 : rk k ^ 8 ≤ rk k ^ 12 := pow_le_pow_right₀ hr1 (by norm_num)
  have h3 : 4 * cm ≤ κ * rk k ^ 12 := by
    have := (div_le_iff₀ hκ).mp (h8.trans h12)
    linarith
  have h4 := mul_le_mul_of_nonneg_left hE hκ.le
  linarith

/-- **Stage 2 (concentration).**  After the onset, the estimate is bad with probability at
most `2 d exp (-c₀ (k+1)^{1/4})`, `c₀ = κ² / (32 d ℓ²)`. -/
lemma bad_exp (hV : T.Valid ℓ κ A0) [Nonempty ι] {k : ℕ} (hk : onset (Fintype.card X) ℓ κ ≤ k) :
    gP (T.bad hT θ k) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) *
      (2 * Real.exp (-(κ ^ 2 / (32 * Fintype.card ι * ℓ ^ 2) * rk k ^ 4)))) := by
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 _) hk
  have hκ := hV.hκ
  have hℓ := hV.hℓ
  have hr0 := rk_pos k
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = κ * rk k ^ 12 / 4 := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = lam * (rk k)⁻¹ ^ 2 / Real.sqrt (Fintype.card ι) := ⟨_, rfl⟩
  have hsd : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.mpr hd
  have ha0 : 0 < a := by rw [ha]; positivity
  have hda : (Fintype.card ι : ℝ) * a ^ 2 = lam ^ 2 * (rk k)⁻¹ ^ 4 := by
    rw [ha, div_pow, Real.sq_sqrt hd.le]
    field_simp
  have hsub : T.bad hT θ k ⊆ {ω | ∃ i, a < |T.noiseSum hT θ k ω i|} := by
    intro ω hω
    by_contra hcon
    have hall : ∀ i, |T.noiseSum hT θ k ω i| ≤ a := by
      intro i
      by_contra hi
      exact hcon ⟨i, not_le.mp hi⟩
    have hc := T.coercive_onset hT θ hV ω hk
    rw [← hlam] at hc
    have hb := T.err_bound hT θ hV ω k hlam0 hc hall
    rw [hda] at hb
    have hb' : T.errSq hT θ k ω ≤ (rk k)⁻¹ ^ 4 :=
      le_of_mul_le_mul_left hb (by positivity)
    have hω' : (rk k)⁻¹ ^ 4 < T.errSq hT θ k ω := hω
    linarith
  refine (measure_mono hsub).trans ((T.noise_tail hT θ hV hk1 ha0).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ hd.le
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  have hk16 : (k : ℝ) ≤ rk k ^ 16 := by rw [rk_pow]; linarith
  have ha2 : a ^ 2 = κ ^ 2 * rk k ^ 20 / (16 * Fintype.card ι) := by
    have h1 : a ^ 2 = lam ^ 2 * (rk k)⁻¹ ^ 4 / Fintype.card ι := by
      rw [← hda]
      field_simp
    rw [h1, hlam]
    field_simp
    ring
  rw [ha2, le_div_iff₀ (by positivity)]
  have e : κ ^ 2 / (32 * Fintype.card ι * ℓ ^ 2) * rk k ^ 4 * (2 * k * ℓ ^ 2) =
      κ ^ 2 * rk k ^ 4 * k / (16 * Fintype.card ι) := by
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : κ ^ 2 * rk k ^ 4 * k ≤ κ ^ 2 * rk k ^ 4 * rk k ^ 16 :=
    mul_le_mul_of_nonneg_left hk16 (by positivity)
  have e2 : κ ^ 2 * rk k ^ 4 * rk k ^ 16 = κ ^ 2 * rk k ^ 20 := by ring
  linarith

/-- `exp (-c r⁴) ≤ 12! / (c¹² r⁴⁸)`. -/
lemma exp_neg_le_poly {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    Real.exp (-(c * r ^ 4)) ≤ (Nat.factorial 12 : ℝ) / (c ^ 12 * r ^ 48) := by
  have h := Real.pow_div_factorial_le_exp (x := c * r ^ 4) (by positivity) 12
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  have hf : (0 : ℝ) < Nat.factorial 12 := by exact_mod_cast Nat.factorial_pos 12
  rw [div_le_iff₀ hf] at h
  have e : (c * r ^ 4) ^ 12 = c ^ 12 * r ^ 48 := by ring
  rw [e] at h
  linarith

/-- **Stage 2, polynomial form.**  There is a constant `C` (depending on the instance only)
with `P(‖θ̂_k - θ‖ > (k+1)^{-1/8}) ≤ C (k+1)^{-3}` for every `k`. -/
theorem bad_poly (hV : T.Valid ℓ κ A0) [Nonempty ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, gP (T.bad hT θ k) ≤ ENNReal.ofReal (C / ((k : ℝ) + 1) ^ 3) := by
  have hκ := hV.hκ
  have hℓ := hV.hℓ
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = κ ^ 2 / (32 * Fintype.card ι * ℓ ^ 2) := ⟨_, rfl⟩
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ, C1 = (Fintype.card ι : ℝ) * (2 * ((Nat.factorial 12 : ℝ) / c0 ^ 12)) :=
    ⟨_, rfl⟩
  have hC1pos : 0 ≤ C1 := by rw [hC1]; positivity
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, k0 = onset (Fintype.card X) ℓ κ := ⟨_, rfl⟩
  refine ⟨C1 + ((k0 : ℝ) + 1) ^ 3, by positivity, fun k => ?_⟩
  have hk3 : (0 : ℝ) < ((k : ℝ) + 1) ^ 3 := by positivity
  rcases Nat.lt_or_ge k k0 with hlt | hge
  · refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hk3, one_mul]
    have h1 : ((k : ℝ) + 1) ^ 3 ≤ ((k0 : ℝ) + 1) ^ 3 := by
      have : (k : ℝ) ≤ k0 := by exact_mod_cast hlt.le
      exact pow_le_pow_left₀ (by positivity) (by linarith) 3
    linarith
  · rw [hk0] at hge
    refine (T.bad_exp hT θ hV hge).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hc0]
    have h1 := exp_neg_le_poly hc0pos (rk_pos k)
    have e48 : rk k ^ 48 = ((k : ℝ) + 1) ^ 3 := by
      rw [← rk_pow k, ← pow_mul]
    rw [e48] at h1
    have h2 : (Fintype.card ι : ℝ) * (2 * Real.exp (-(c0 * rk k ^ 4))) ≤ C1 / ((k : ℝ) + 1) ^ 3 := by
      rw [hC1]
      have e : (Fintype.card ι : ℝ) * (2 * ((Nat.factorial 12 : ℝ) / c0 ^ 12)) / ((k : ℝ) + 1) ^ 3 =
          (Fintype.card ι : ℝ) * (2 * ((Nat.factorial 12 : ℝ) / (c0 ^ 12 * ((k : ℝ) + 1) ^ 3))) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num)) hd.le
    refine h2.trans ?_
    exact div_le_div_of_nonneg_right (by linarith [pow_pos (by positivity : (0:ℝ) < (k0 : ℝ) + 1) 3])
      hk3.le

end Tracker

namespace Tracker

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]
variable [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]
variable (T : Tracker X ι 𝒜) (hT : T.Meas) (θ : ι → ℝ) {ℓ κ A0 : ℝ}

/-! ### Stage 3a: scores, the oracle contract in root form, stabilisation of the selector -/

lemma norm_tE_sq (e : ι → ℝ) : ‖(WithLp.toLp 2 e : EuclideanSpace ℝ ι)‖ ^ 2 = e ⬝ᵥ e := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

lemma inner_uE (x : X) (z : EuclideanSpace ℝ ι) : ⟪T.uE x, z⟫ = T.u x ⬝ᵥ z.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [uE, dotProduct_comm]

lemma norm_uE_le (hV : T.Valid ℓ κ A0) (x : X) : ‖T.uE x‖ ≤ ℓ := by
  have h : ‖T.uE x‖ ^ 2 ≤ ℓ ^ 2 := by
    unfold uE
    rw [norm_tE_sq]
    exact hV.hu x
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hV.hℓ.le two_ne_zero).mp h

/-- `‖z‖²_{M(w)} = ∑_x w_x (u_x · z)²`. -/
lemma dm_sq {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (z : EuclideanSpace ℝ ι) :
    ‖designMap T.uE w z‖ ^ 2 = ∑ x, w x * (T.u x ⬝ᵥ z.ofLp) ^ 2 := by
  rw [norm_designMap_sq T.uE hw]
  exact sum_congr rfl fun x _ => by rw [inner_uE]

/-- `√(2 I_a(z, w))`. -/
def root (a : 𝒜) (z : EuclideanSpace ℝ ι) (w : X → ℝ) : ℝ :=
  rootInfo (designMap T.uE w) (T.Q a) z

/-- `√(2 max_w I_a(z, w))`, the root score of the action `a` at the parameter `z`. -/
def Rs (a : 𝒜) (z : EuclideanSpace ℝ ι) : ℝ := sSup ((fun w => T.root a z w) '' simplex X)

lemma root_nonneg (a : 𝒜) (z : EuclideanSpace ℝ ι) (w : X → ℝ) : 0 ≤ T.root a z w :=
  rootInfo_nonneg

lemma gInfo_eq (a : 𝒜) (z : EuclideanSpace ℝ ι) (w : X → ℝ) :
    gInfo T.uE (T.Q a) z w = T.root a z w ^ 2 / 2 := rfl

lemma A0_nonneg (hV : T.Valid ℓ κ A0) : 0 ≤ A0 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty 𝒜)
  obtain ⟨lam0, -, hA⟩ := hV.hQ a
  exact (norm_nonneg _).trans hA

lemma root_le_bound (hV : T.Valid ℓ κ A0) (a : 𝒜) (z : EuclideanSpace ℝ ι) {w : X → ℝ}
    (hw : w ∈ simplex X) : T.root a z w ≤ ℓ * (‖z‖ + A0) := by
  obtain ⟨lam0, h0, hA⟩ := hV.hQ a
  exact rootInfo_le_anchor T.uE hw hV.hℓ.le (T.norm_uE_le hV) h0 hA le_rfl

lemma bddAbove_root (hV : T.Valid ℓ κ A0) (a : 𝒜) (z : EuclideanSpace ℝ ι) :
    BddAbove ((fun w => T.root a z w) '' simplex X) := by
  refine ⟨ℓ * (‖z‖ + A0), ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact T.root_le_bound hV a z hw

lemma root_le_Rs (hV : T.Valid ℓ κ A0) (a : 𝒜) (z : EuclideanSpace ℝ ι) {w : X → ℝ}
    (hw : w ∈ simplex X) : T.root a z w ≤ T.Rs a z :=
  le_csSup (T.bddAbove_root hV a z) ⟨w, hw, rfl⟩

lemma Rs_le (hV : T.Valid ℓ κ A0) (a : 𝒜) (z : EuclideanSpace ℝ ι) {c : ℝ}
    (h : ∀ w ∈ simplex X, T.root a z w ≤ c) : T.Rs a z ≤ c := by
  refine csSup_le ⟨_, T.w0, hV.hw0, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

lemma Rs_nonneg (hV : T.Valid ℓ κ A0) (a : 𝒜) (z : EuclideanSpace ℝ ι) : 0 ≤ T.Rs a z :=
  (T.root_nonneg a z T.w0).trans (T.root_le_Rs hV a z hV.hw0)

lemma root_lip (hV : T.Valid ℓ κ A0) (a : 𝒜) (z z' : EuclideanSpace ℝ ι) {w : X → ℝ}
    (hw : w ∈ simplex X) : |T.root a z w - T.root a z' w| ≤ ℓ * ‖z - z'‖ :=
  rootInfo_design_lipschitz T.uE hw (T.norm_uE_le hV) (T.Q a) z z'

/-- The root score is `ℓ`-Lipschitz in the parameter (`eq:bay-root-lipschitz` for the
maximum over designs). -/
lemma Rs_lip (hV : T.Valid ℓ κ A0) (a : 𝒜) (z z' : EuclideanSpace ℝ ι) :
    |T.Rs a z - T.Rs a z'| ≤ ℓ * ‖z - z'‖ := by
  have key : ∀ y y' : EuclideanSpace ℝ ι, T.Rs a y ≤ T.Rs a y' + ℓ * ‖y - y'‖ := by
    intro y y'
    refine T.Rs_le hV a y fun w hw => ?_
    have h1 := (abs_sub_le_iff.mp (T.root_lip hV a y y' hw)).1
    have h2 := T.root_le_Rs hV a y' hw
    linarith
  rw [abs_sub_le_iff]
  constructor
  · linarith [key z z']
  · have := key z' z
    rw [norm_sub_rev] at this
    linarith

lemma ow_mem (hV : T.Valid ℓ κ A0) (k : ℕ) (θh : ι → ℝ) (a : 𝒜) : T.ow k θh a ∈ simplex X := by
  obtain ⟨p, hp, he⟩ := hV.floor k θh a
  rw [he]
  exact floorDesign_mem (etaK_pos k).le (etaK_le_one k) hV.hw0 hp

/-- Oracle contract, lower side, in root form: `√(2 c) ≤ √(2 I_a(θ̂, v))`. -/
lemma shat_le (hV : T.Valid ℓ κ A0) (k : ℕ) (θh : ι → ℝ) (a : 𝒜) :
    Real.sqrt (2 * T.oc k θh a) ≤ T.root a (WithLp.toLp 2 θh) (T.ow k θh a) := by
  have h := (hV.lower k θh a).2
  rw [gInfo_eq] at h
  rw [Real.sqrt_le_iff]
  exact ⟨T.root_nonneg _ _ _, by linarith⟩

/-- The oracle tolerance at round `k + 1` for the estimate `θh`. -/
def tol (ℓ A0 : ℝ) (k : ℕ) (θh : ι → ℝ) : ℝ :=
  etaK k * (ℓ ^ 2 * (‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ + 1 + A0) ^ 2 / 2) + etaK k

lemma tol_nonneg (ℓ A0 : ℝ) (k : ℕ) (θh : ι → ℝ) : 0 ≤ tol ℓ A0 k θh := by
  unfold tol
  have := (etaK_pos k).le
  positivity

/-- Oracle contract, upper side, in root form. -/
lemma Rs_le_shat (hV : T.Valid ℓ κ A0) (k : ℕ) (θh : ι → ℝ) (a : 𝒜) :
    T.Rs a (WithLp.toLp 2 θh) ≤
      Real.sqrt (2 * T.oc k θh a) + Real.sqrt (2 * tol ℓ A0 k θh) := by
  refine T.Rs_le hV a _ fun w hw => ?_
  have h := hV.near k θh a w hw
  rw [gInfo_eq] at h
  have hc := (hV.lower k θh a).1
  have hK := tol_nonneg ℓ A0 k θh
  obtain ⟨c, hcdef⟩ : ∃ c, c = T.oc k θh a := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = tol ℓ A0 k θh := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = T.root a (WithLp.toLp 2 θh) w := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hrdef]; exact T.root_nonneg _ _ _
  have hle : r ^ 2 / 2 - c ≤ K := by
    rw [hrdef, hcdef, hKdef]
    exact h
  rw [← hcdef] at hc
  rw [← hKdef] at hK
  rw [← hcdef, ← hKdef, ← hrdef]
  have h1 : r ^ 2 ≤ 2 * c + 2 * K := by linarith
  have h2 : r ≤ Real.sqrt (2 * c + 2 * K) := by
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hr0] at this
  have h3 : Real.sqrt (2 * c + 2 * K) ≤ Real.sqrt (2 * c) + Real.sqrt (2 * K) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e1 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * c by positivity)
    have e2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * K by positivity)
    nlinarith [mul_nonneg (Real.sqrt_nonneg (2 * c)) (Real.sqrt_nonneg (2 * K))]
  linarith

/-- `C_R` on the ball of radius `‖θ‖ + 1`. -/
def Cbar (ℓ A0 : ℝ) (θ : ι → ℝ) : ℝ :=
  ℓ ^ 2 * (‖(WithLp.toLp 2 θ : EuclideanSpace ℝ ι)‖ + 2 + A0) ^ 2 / 2

/-- Constant of the uniform score error `O_θ(t^{-1/8})`. -/
def K1 (ℓ A0 : ℝ) (θ : ι → ℝ) : ℝ := Real.sqrt (2 * (Cbar ℓ A0 θ + 1)) + ℓ

lemma Cbar_nonneg (ℓ A0 : ℝ) (θ : ι → ℝ) : 0 ≤ Cbar ℓ A0 θ := by
  unfold Cbar
  positivity

lemma sqrt_tol_le (hV : T.Valid ℓ κ A0) {k : ℕ} {θh : ι → ℝ}
    (hgood : ‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι) - WithLp.toLp 2 θ‖ ≤ (rk k)⁻¹ ^ 2) :
    Real.sqrt (2 * tol ℓ A0 k θh) ≤ (rk k)⁻¹ ^ 2 * Real.sqrt (2 * (Cbar ℓ A0 θ + 1)) := by
  have hA := T.A0_nonneg hV
  have hρ0 : 0 ≤ (rk k)⁻¹ ^ 2 := by positivity
  have hρ1 : (rk k)⁻¹ ^ 2 ≤ 1 :=
    pow_le_one₀ (inv_pos.mpr (rk_pos k)).le (inv_le_one_of_one_le₀ (one_le_rk k))
  have hn : ‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ ≤
      ‖(WithLp.toLp 2 θ : EuclideanSpace ℝ ι)‖ + 1 := by
    have := norm_le_norm_add_norm_sub' (WithLp.toLp 2 θh : EuclideanSpace ℝ ι) (WithLp.toLp 2 θ)
    linarith
  have h1 : tol ℓ A0 k θh ≤ etaK k * (Cbar ℓ A0 θ + 1) := by
    unfold tol Cbar
    have h2 : (‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ + 1 + A0) ^ 2 ≤
        (‖(WithLp.toLp 2 θ : EuclideanSpace ℝ ι)‖ + 2 + A0) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : ℓ ^ 2 * (‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ + 1 + A0) ^ 2 / 2 ≤
        ℓ ^ 2 * (‖(WithLp.toLp 2 θ : EuclideanSpace ℝ ι)‖ + 2 + A0) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left h2 (sq_nonneg ℓ)
      linarith
    have := mul_le_mul_of_nonneg_left h3 (etaK_pos k).le
    linarith
  have he : etaK k = ((rk k)⁻¹ ^ 2) ^ 2 := by
    unfold etaK
    ring
  calc Real.sqrt (2 * tol ℓ A0 k θh)
      ≤ Real.sqrt (((rk k)⁻¹ ^ 2) ^ 2 * (2 * (Cbar ℓ A0 θ + 1))) := by
        apply Real.sqrt_le_sqrt
        rw [← he]
        linarith
    _ = (rk k)⁻¹ ^ 2 * Real.sqrt (2 * (Cbar ℓ A0 θ + 1)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hρ0]

/-- The true root score of an action. -/
def sc (a : 𝒜) : ℝ := T.Rs a (WithLp.toLp 2 θ)

/-- **Uniform score error.**  If `‖θ̂ - θ‖ ≤ (k+1)^{-1/8}` then
`|√(2 c_t(a)) - √(2 max_w I_a(θ, w))| ≤ K₁ (k+1)^{-1/8}`. -/
lemma score_err (hV : T.Valid ℓ κ A0) {k : ℕ} {θh : ι → ℝ}
    (hgood : ‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι) - WithLp.toLp 2 θ‖ ≤ (rk k)⁻¹ ^ 2)
    (a : 𝒜) : |Real.sqrt (2 * T.oc k θh a) - T.sc θ a| ≤ K1 ℓ A0 θ * (rk k)⁻¹ ^ 2 := by
  have h1 := T.shat_le hV k θh a
  have h2 := T.root_le_Rs hV a (WithLp.toLp 2 θh) (T.ow_mem hV k θh a)
  have h3 := T.Rs_le_shat hV k θh a
  have h4 := abs_sub_le_iff.mp (T.Rs_lip hV a (WithLp.toLp 2 θh) (WithLp.toLp 2 θ))
  have h5 := T.sqrt_tol_le θ hV hgood
  have h6 := mul_le_mul_of_nonneg_left hgood hV.hℓ.le
  unfold sc K1
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

/-- The truly maximizing actions. -/
def Astar : Finset 𝒜 := univ.filter fun a => ∀ b, T.sc θ b ≤ T.sc θ a

lemma Astar_nonempty : (T.Astar θ).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image univ (T.sc θ) univ_nonempty
  exact ⟨a, by simpa [Astar] using fun b => ha b (mem_univ _)⟩

/-- The action at which the selector stabilises: `a† = min argmax_a max_w I_a(θ, w)` for
the fixed tie-breaking rule. -/
def aDag : 𝒜 := pick (T.Astar θ)

/-- `√(2 I_*(θ))`. -/
def Rmax : ℝ := T.sc θ (T.aDag θ)

/-- `I_*(θ) = max_a max_w I_a(θ, w)`. -/
def Istar : ℝ := T.Rmax θ ^ 2 / 2

lemma sc_le_Rmax (b : 𝒜) : T.sc θ b ≤ T.Rmax θ := by
  have := pick_mem (T.Astar_nonempty θ)
  simp only [Astar, mem_filter, mem_univ, true_and] at this
  exact this b

lemma exists_gap : ∃ Δ : ℝ, 0 < Δ ∧ ∀ a, a ∉ T.Astar θ → T.sc θ a + Δ ≤ T.Rmax θ := by
  by_cases h : (univ.filter fun a => a ∉ T.Astar θ).Nonempty
  · obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image _ (fun a => T.Rmax θ - T.sc θ a) h
    have ha0' : a0 ∉ T.Astar θ := by simpa using ha0
    have hpos : 0 < T.Rmax θ - T.sc θ a0 := by
      simp only [Astar, mem_filter, mem_univ, true_and, not_forall, not_le] at ha0'
      obtain ⟨b, hb⟩ := ha0'
      have := T.sc_le_Rmax θ b
      linarith
    refine ⟨_, hpos, fun a ha => ?_⟩
    have := hmin a (by simpa using ha)
    linarith
  · refine ⟨1, one_pos, fun a ha => ?_⟩
    exact absurd ⟨a, by simpa using ha⟩ h

/-- **The selector stabilises.**  On a good round late enough that `2 K₁ ≤ (k+1)^{1/16}`
and `2 (k+1)^{-1/16} < Δ`, the eligible set is the set of true maximisers and the selected
action is `a†`. -/
lemma sel_eq (hV : T.Valid ℓ κ A0) {k : ℕ} {θh : ι → ℝ}
    (hgood : ‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι) - WithLp.toLp 2 θ‖ ≤ (rk k)⁻¹ ^ 2)
    {Δ : ℝ} (hΔ : ∀ a, a ∉ T.Astar θ → T.sc θ a + Δ ≤ T.Rmax θ)
    (h1 : 2 * K1 ℓ A0 θ ≤ rk k) (h2 : 2 * (rk k)⁻¹ < Δ) : T.selA k θh = T.aDag θ := by
  have hr := rk_pos k
  have hri : 0 < (rk k)⁻¹ := inv_pos.mpr hr
  have hζ : 2 * (K1 ℓ A0 θ * (rk k)⁻¹ ^ 2) ≤ zetaK k := by
    unfold zetaK
    have h3 : 2 * K1 ℓ A0 θ * (rk k)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hr]
      exact h1
    have := mul_le_mul_of_nonneg_right h3 hri.le
    nlinarith
  obtain ⟨hs1, hs2⟩ := selector_stable (T.sc θ) (fun a => Real.sqrt (2 * T.oc k θh a))
    (fun a => T.score_err θ hV hgood a) hζ
  have helig : T.elig k θh = T.Astar θ := by
    ext a
    simp only [elig, Astar, mem_filter, mem_univ, true_and]
    constructor
    · intro ha
      by_contra hcon
      have hnot : a ∉ T.Astar θ := by simpa [Astar] using hcon
      have hgap := hΔ a hnot
      have hlt : T.sc θ a + zetaK k + 2 * (K1 ℓ A0 θ * (rk k)⁻¹ ^ 2) < T.sc θ (T.aDag θ) := by
        have : zetaK k = (rk k)⁻¹ := rfl
        have hR : T.Rmax θ = T.sc θ (T.aDag θ) := rfl
        linarith
      have := hs2 a (T.aDag θ) hlt
      have := ha (T.aDag θ)
      linarith
    · intro ha b
      exact hs1 a ha b
  unfold selA aDag
  rw [helig]

/-- **The plug-in design is near-optimal.**  On a good round at which `a†` is selected,
`√(2 I_{a†}(θ, v_t)) ≥ √(2 I_*(θ)) - 2 K₁ (k+1)^{-1/8}`. -/
lemma plan_quality (hV : T.Valid ℓ κ A0) {k : ℕ} {θh : ι → ℝ}
    (hgood : ‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι) - WithLp.toLp 2 θ‖ ≤ (rk k)⁻¹ ^ 2)
    (hsel : T.selA k θh = T.aDag θ) :
    T.Rmax θ - 2 * K1 ℓ A0 θ * (rk k)⁻¹ ^ 2 ≤
      T.root (T.aDag θ) (WithLp.toLp 2 θ) (T.plan k θh) := by
  have hpl : T.plan k θh = T.ow k θh (T.aDag θ) := by
    unfold plan
    rw [hsel]
  rw [hpl]
  have h1 := T.shat_le hV k θh (T.aDag θ)
  have h2 := (abs_sub_le_iff.mp (T.root_lip hV (T.aDag θ) (WithLp.toLp 2 θh) (WithLp.toLp 2 θ)
    (T.ow_mem hV k θh (T.aDag θ)))).1
  have h3 := (abs_sub_le_iff.mp (T.score_err θ hV hgood (T.aDag θ))).2
  have h6 := mul_le_mul_of_nonneg_left hgood hV.hℓ.le
  have hK : ℓ ≤ K1 ℓ A0 θ := by
    unfold K1
    linarith [Real.sqrt_nonneg (2 * (Cbar ℓ A0 θ + 1))]
  have hρ0 : 0 ≤ (rk k)⁻¹ ^ 2 := by positivity
  have h7 := mul_le_mul_of_nonneg_right hK hρ0
  have hR : T.Rmax θ = T.sc θ (T.aDag θ) := rfl
  linarith

end Tracker

/-- Superadditivity of the information in the design: `∑_j 2 I(θ, w_j) ≤ 2 I(θ, ∑_j w_j)`
(the infimum of a sum is at least the sum of the infima). -/
lemma rootInfo_sum_sq_le {X E J : Type*} [Fintype X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : X → E) (s : Finset J) (w : J → X → ℝ)
    (hw : ∀ j ∈ s, ∀ x, 0 ≤ w j x) {Q : Set E} (hQ : Q.Nonempty) (θ : E) :
    ∑ j ∈ s, rootInfo (designMap u (w j)) Q θ ^ 2 ≤
      rootInfo (designMap u (fun x => ∑ j ∈ s, w j x)) Q θ ^ 2 := by
  have hW : ∀ x, 0 ≤ ∑ j ∈ s, w j x := fun x => sum_nonneg fun j hj => hw j hj x
  have h0 : 0 ≤ ∑ j ∈ s, rootInfo (designMap u (w j)) Q θ ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have h1 : Real.sqrt (∑ j ∈ s, rootInfo (designMap u (w j)) Q θ ^ 2) ≤
      rootInfo (designMap u (fun x => ∑ j ∈ s, w j x)) Q θ := by
    rw [le_rootInfo_iff hQ]
    intro lam hl
    rw [Real.sqrt_le_iff]
    refine ⟨norm_nonneg _, ?_⟩
    rw [norm_designMap_sq u hW]
    calc ∑ j ∈ s, rootInfo (designMap u (w j)) Q θ ^ 2
        ≤ ∑ j ∈ s, ‖designMap u (w j) (lam - θ)‖ ^ 2 :=
          sum_le_sum fun j _ => pow_le_pow_left₀ rootInfo_nonneg (rootInfo_le hl) 2
      _ = ∑ j ∈ s, ∑ x, w j x * ⟪u x, lam - θ⟫ ^ 2 :=
          sum_congr rfl fun j hj => norm_designMap_sq u (hw j hj) _
      _ = ∑ x, (∑ j ∈ s, w j x) * ⟪u x, lam - θ⟫ ^ 2 := by
          rw [sum_comm]
          exact sum_congr rfl fun x _ => by rw [sum_mul]
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rwa [Real.sq_sqrt h0] at this

namespace Tracker

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]
variable [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]
variable (T : Tracker X ι 𝒜) (hT : T.Meas) (θ : ι → ℝ) {ℓ κ A0 : ℝ}

/-! ### Stage 3b: the information-growth inequality `eq:bay-information-growth` -/

lemma good_norm {k : ℕ} {ω : ℕ → ℝ} (h : ω ∉ T.bad hT θ k) :
    ‖(WithLp.toLp 2 (T.thetaHat hT θ k ω) : EuclideanSpace ℝ ι) - WithLp.toLp 2 θ‖ ≤
      (rk k)⁻¹ ^ 2 := by
  have h1 : T.errSq hT θ k ω ≤ (rk k)⁻¹ ^ 4 := not_lt.mp h
  have h2 : ‖(WithLp.toLp 2 (T.thetaHat hT θ k ω) : EuclideanSpace ℝ ι) - WithLp.toLp 2 θ‖ ^ 2 =
      T.errSq hT θ k ω := by
    rw [← WithLp.toLp_sub, norm_tE_sq]
    rfl
  have h3 : ((rk k)⁻¹ ^ 2) ^ 2 = (rk k)⁻¹ ^ 4 := by ring
  rw [← h2, ← h3] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

lemma W_design (ω : ℕ → ℝ) (k : ℕ) :
    (T.S hT θ k ω).2.1 = fun x => ∑ j ∈ range k, T.pl hT θ j ω x := by
  funext x
  rw [W_eq]
  rfl

lemma Q_nonempty (hV : T.Valid ℓ κ A0) (a : 𝒜) : (T.Q a).Nonempty := by
  obtain ⟨lam0, h0, -⟩ := hV.hQ a
  exact ⟨lam0, h0⟩

/-- Information accumulated by the cumulative target: if the designs used on `[T0, k)` each
have root information at least `c` for the action `a`, then
`2 I_a(θ, W(k)) ≥ (k - T0) c²`. -/
lemma root_W_ge (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (a : 𝒜) {T0 k : ℕ} (hT0 : T0 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c)
    (h : ∀ j, T0 ≤ j → j < k → c ≤ T.root a (WithLp.toLp 2 θ) (T.pl hT θ j ω)) :
    ((k : ℝ) - T0) * c ^ 2 ≤ T.root a (WithLp.toLp 2 θ) (T.S hT θ k ω).2.1 ^ 2 := by
  have hsup := rootInfo_sum_sq_le T.uE (range k) (fun j => T.pl hT θ j ω)
    (fun j _ x => (T.plan_mem hV j _).1 x) (T.Q_nonempty hV a) (WithLp.toLp 2 θ)
  rw [← T.W_design hT θ ω k] at hsup
  refine le_trans ?_ hsup
  have hsub : Finset.Ico T0 k ⊆ range k := fun j hj =>
    Finset.mem_range.2 (Finset.mem_Ico.1 hj).2
  calc ((k : ℝ) - T0) * c ^ 2 = ∑ _j ∈ Finset.Ico T0 k, c ^ 2 := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hT0]
    _ ≤ ∑ j ∈ Finset.Ico T0 k, rootInfo (designMap T.uE (T.pl hT θ j ω)) (T.Q a)
          (WithLp.toLp 2 θ) ^ 2 := by
        refine sum_le_sum fun j hj => pow_le_pow_left₀ hc0 ?_ 2
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hj
        exact h j h1 h2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-- The constant `m (m - 1) ℓ²` of the tracking loss. -/
def cmC (m : ℕ) (ℓ : ℝ) : ℝ := (m : ℝ) * ((m : ℝ) - 1) * ℓ ^ 2

/-- Tracking domination `M(N(k)) ⪰ (1 - ρ_k) M(W(k))` with `ρ_k = m (m-1) ℓ² / (κ E_k)`,
in the form `(κ E_k - m (m-1) ℓ²) ‖z‖²_{M(W)} ≤ κ E_k ‖z‖²_{M(N)}`. -/
lemma N_dom (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) (z : EuclideanSpace ℝ ι) :
    (κ * cumEta k - cmC (Fintype.card X) ℓ) * ‖designMap T.uE (T.S hT θ k ω).2.1 z‖ ^ 2 ≤
      κ * cumEta k * ‖designMap T.uE (fun x => ((T.S hT θ k ω).1 x : ℝ)) z‖ ^ 2 := by
  have hW0 : ∀ x, 0 ≤ (T.S hT θ k ω).2.1 x := fun x =>
    (mul_nonneg (hV.hw0.1 x) (cumEta_nonneg k)).trans (T.W_ge hT θ hV ω k x)
  rw [T.dm_sq hW0, T.dm_sq (fun x => Nat.cast_nonneg _)]
  have hm : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 1 := by
    have : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ x, (T.S hT θ k ω).2.1 x * (T.u x ⬝ᵥ z.ofLp) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ x, ((T.S hT θ k ω).1 x : ℝ) * (T.u x ⬝ᵥ z.ofLp) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Sq, hSq⟩ : ∃ Sq : ℝ, Sq = ∑ x, (T.u x ⬝ᵥ z.ofLp) ^ 2 := ⟨_, rfl⟩
  obtain ⟨zz, hzz⟩ : ∃ zz : ℝ, zz = z.ofLp ⬝ᵥ z.ofLp := ⟨_, rfl⟩
  have hzz0 : 0 ≤ zz := by rw [hzz]; exact dotProduct_self_nonneg' _
  have h1 : A - B ≤ ((Fintype.card X : ℝ) - 1) * Sq := by
    rw [hA, hB, hSq, ← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun x _ => ?_
    have := (T.track hT θ hV ω k x).1
    have hq := sq_nonneg (T.u x ⬝ᵥ z.ofLp)
    nlinarith
  have h2 : Sq ≤ (Fintype.card X : ℝ) * (ℓ ^ 2 * zz) := by
    rw [hSq, hzz]
    calc ∑ x, (T.u x ⬝ᵥ z.ofLp) ^ 2 ≤ ∑ _x : X, ℓ ^ 2 * (z.ofLp ⬝ᵥ z.ofLp) :=
          sum_le_sum fun x _ => T.dot_sq_le hV x _
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have h3 : κ * cumEta k * zz ≤ A := by
    rw [hA, hzz]
    have h4 := mul_le_mul_of_nonneg_left (hV.hspan z.ofLp) (cumEta_nonneg k)
    have h5 : ∑ x, T.w0 x * cumEta k * (T.u x ⬝ᵥ z.ofLp) ^ 2 ≤
        ∑ x, (T.S hT θ k ω).2.1 x * (T.u x ⬝ᵥ z.ofLp) ^ 2 :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (T.W_ge hT θ hV ω k x) (sq_nonneg _)
    have h6 : ∑ x, T.w0 x * cumEta k * (T.u x ⬝ᵥ z.ofLp) ^ 2 =
        cumEta k * ∑ x, T.w0 x * (T.u x ⬝ᵥ z.ofLp) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun x _ => by ring
    rw [h6] at h5
    nlinarith
  rw [← hA, ← hB]
  have hκE : 0 ≤ κ * cumEta k := mul_nonneg hV.hκ.le (cumEta_nonneg k)
  have h7 : ((Fintype.card X : ℝ) - 1) * Sq ≤ cmC (Fintype.card X) ℓ * zz := by
    unfold cmC
    have := mul_le_mul_of_nonneg_left h2 hm
    nlinarith
  have hcm0 : 0 ≤ cmC (Fintype.card X) ℓ := by
    unfold cmC
    positivity
  have h8 : κ * cumEta k * (A - B) ≤ cmC (Fintype.card X) ℓ * A := by
    calc κ * cumEta k * (A - B) ≤ κ * cumEta k * (cmC (Fintype.card X) ℓ * zz) :=
          mul_le_mul_of_nonneg_left (h1.trans h7) hκE
      _ = cmC (Fintype.card X) ℓ * (κ * cumEta k * zz) := by ring
      _ ≤ cmC (Fintype.card X) ℓ * A := mul_le_mul_of_nonneg_left h3 hcm0
  linarith

/-- `G_k ⪯ k ℓ² I`. -/
lemma N_upper (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) (z : EuclideanSpace ℝ ι) :
    ‖designMap T.uE (fun x => ((T.S hT θ k ω).1 x : ℝ)) z‖ ≤ Real.sqrt k * (ℓ * ‖z‖) := by
  have hsq : ‖designMap T.uE (fun x => ((T.S hT θ k ω).1 x : ℝ)) z‖ ^ 2 ≤
      (Real.sqrt k * (ℓ * ‖z‖)) ^ 2 := by
    rw [T.dm_sq (fun x => Nat.cast_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg k), mul_pow]
    have hz : ‖z‖ ^ 2 = z.ofLp ⬝ᵥ z.ofLp := by
      have := norm_tE_sq z.ofLp
      simpa using this
    rw [hz]
    calc ∑ x, ((T.S hT θ k ω).1 x : ℝ) * (T.u x ⬝ᵥ z.ofLp) ^ 2
        ≤ ∑ x, ((T.S hT θ k ω).1 x : ℝ) * (ℓ ^ 2 * (z.ofLp ⬝ᵥ z.ofLp)) :=
          sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (T.dot_sq_le hV x _) (Nat.cast_nonneg _)
      _ = (k : ℝ) * (ℓ ^ 2 * (z.ofLp ⬝ᵥ z.ofLp)) := by
          rw [← sum_mul]
          congr 1
          have := sum_pulls (fun j => T.qry hT θ j ω) k
          simp_rw [← T.N_eq_pulls hT θ ω k] at this
          exact this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hV.hℓ.le (norm_nonneg _))) two_ne_zero).mp hsq

/-- **Information growth (`eq:bay-information-growth`), root form.**  Suppose all rounds
in `[T0, k]` are good, `T0` is late enough for the selector to have stabilised and for the
plug-in designs to have root information at least `q √(2 I_*)`, `T0 ≤ (1 - q²) k`, the
tracking loss satisfies `ρ_k ≤ 1 - q²` and the final centre perturbation is at most `g`.
Then `√(2 J_k(a†)) ≥ √k (q³ √(2 I_*) - g)`. -/
lemma stat_growth (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) {T0 k : ℕ} {q g Δ : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hT0k : T0 ≤ k) (hfrac : (T0 : ℝ) ≤ (1 - q ^ 2) * k)
    (hgood : ∀ j, T0 ≤ j → j ≤ k → ω ∉ T.bad hT θ j)
    (hΔ : ∀ a, a ∉ T.Astar θ → T.sc θ a + Δ ≤ T.Rmax θ)
    (h2K : 2 * K1 ℓ A0 θ ≤ rk T0) (hΔ' : 2 * (rk T0)⁻¹ < Δ)
    (hqual : 2 * K1 ℓ A0 θ * (rk T0)⁻¹ ^ 2 ≤ (1 - q) * T.Rmax θ)
    (hρ : cmC (Fintype.card X) ℓ ≤ (1 - q ^ 2) * (κ * cumEta k)) (hE : 0 < cumEta k)
    (hpert : ℓ * (rk k)⁻¹ ^ 2 ≤ g) :
    Real.sqrt k * (q ^ 3 * T.Rmax θ - g) ≤
      T.root (T.aDag θ) (WithLp.toLp 2 (T.thetaHat hT θ k ω))
        (fun x => ((T.S hT θ k ω).1 x : ℝ)) := by
  have hK1 : 0 ≤ K1 ℓ A0 θ := by
    unfold K1
    have := Real.sqrt_nonneg (2 * (Cbar ℓ A0 θ + 1))
    linarith [hV.hℓ]
  have hR0 : 0 ≤ T.Rmax θ := T.Rs_nonneg hV _ _
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  -- step 1: plug-in designs on [T0, k)
  have hstep : ∀ j, T0 ≤ j → j < k →
      q * T.Rmax θ ≤ T.root (T.aDag θ) (WithLp.toLp 2 θ) (T.pl hT θ j ω) := by
    intro j hj1 hj2
    have hg := T.good_norm hT θ (hgood j hj1 hj2.le)
    have hrj : rk T0 ≤ rk j := rk_mono hj1
    have hinv : (rk j)⁻¹ ≤ (rk T0)⁻¹ := inv_anti₀ (rk_pos T0) hrj
    have hsel := T.sel_eq θ hV hg hΔ (h2K.trans hrj) (by linarith)
    have hpq := T.plan_quality θ hV hg hsel
    have hinv2 : (rk j)⁻¹ ^ 2 ≤ (rk T0)⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_pos.mpr (rk_pos j)).le hinv 2
    have := mul_le_mul_of_nonneg_left hinv2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK1)
    unfold pl
    linarith
  -- step 2: the cumulative target
  have hW := T.root_W_ge hT θ hV ω (T.aDag θ) hT0k (mul_nonneg hq0.le hR0) hstep
  have hW2 : (Real.sqrt k * (q * (q * T.Rmax θ))) ^ 2 ≤
      T.root (T.aDag θ) (WithLp.toLp 2 θ) (T.S hT θ k ω).2.1 ^ 2 := by
    refine le_trans ?_ hW
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    have h1 : q ^ 2 * (k : ℝ) ≤ (k : ℝ) - T0 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (q * T.Rmax θ))
    have e : (k : ℝ) * (q * (q * T.Rmax θ)) ^ 2 = q ^ 2 * (k : ℝ) * (q * T.Rmax θ) ^ 2 := by ring
    rw [e]
    exact h2
  have hW3 : Real.sqrt k * (q * (q * T.Rmax θ)) ≤
      T.root (T.aDag θ) (WithLp.toLp 2 θ) (T.S hT θ k ω).2.1 :=
    (pow_le_pow_iff_left₀ (by positivity) (T.root_nonneg _ _ _) two_ne_zero).mp hW2
  -- step 3: tracking domination
  have hκE : 0 < κ * cumEta k := mul_pos hV.hκ hE
  have hdom : ∀ z : EuclideanSpace ℝ ι, q * ‖designMap T.uE (T.S hT θ k ω).2.1 z‖ ≤
      ‖designMap T.uE (fun x => ((T.S hT θ k ω).1 x : ℝ)) z‖ := by
    intro z
    have h1 := T.N_dom hT θ hV ω k z
    have h2 : q ^ 2 * (κ * cumEta k) * ‖designMap T.uE (T.S hT θ k ω).2.1 z‖ ^ 2 ≤
        (κ * cumEta k - cmC (Fintype.card X) ℓ) *
          ‖designMap T.uE (T.S hT θ k ω).2.1 z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have h3 : (q * ‖designMap T.uE (T.S hT θ k ω).2.1 z‖) ^ 2 ≤
        ‖designMap T.uE (fun x => ((T.S hT θ k ω).1 x : ℝ)) z‖ ^ 2 := by
      have h4 : κ * cumEta k * (q * ‖designMap T.uE (T.S hT θ k ω).2.1 z‖) ^ 2 ≤
          κ * cumEta k * ‖designMap T.uE (fun x => ((T.S hT θ k ω).1 x : ℝ)) z‖ ^ 2 := by
        have e : κ * cumEta k * (q * ‖designMap T.uE (T.S hT θ k ω).2.1 z‖) ^ 2 =
            q ^ 2 * (κ * cumEta k) * ‖designMap T.uE (T.S hT θ k ω).2.1 z‖ ^ 2 := by ring
        rw [e]
        exact h2.trans h1
      exact le_of_mul_le_mul_left h4 hκE
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h3
  have hN : q * T.root (T.aDag θ) (WithLp.toLp 2 θ) (T.S hT θ k ω).2.1 ≤
      T.root (T.aDag θ) (WithLp.toLp 2 θ) (fun x => ((T.S hT θ k ω).1 x : ℝ)) :=
    rootInfo_mono_design (T.Q_nonempty hV _) hq0.le hdom
  -- step 4: the final centre perturbation
  have hgk := T.good_norm hT θ (hgood k hT0k le_rfl)
  have hlip := (abs_sub_le_iff.mp (rootInfo_lipschitz
    (designMap T.uE (fun x => ((T.S hT θ k ω).1 x : ℝ))) (T.Q (T.aDag θ))
    (WithLp.toLp 2 θ) (WithLp.toLp 2 (T.thetaHat hT θ k ω)))).1
  have hup := T.N_upper hT θ hV ω k
    ((WithLp.toLp 2 θ : EuclideanSpace ℝ ι) - WithLp.toLp 2 (T.thetaHat hT θ k ω))
  rw [norm_sub_rev] at hup
  have h5 : Real.sqrt k * (ℓ * ‖(WithLp.toLp 2 (T.thetaHat hT θ k ω) : EuclideanSpace ℝ ι) -
      WithLp.toLp 2 θ‖) ≤ Real.sqrt k * g :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hgk hV.hℓ.le).trans hpert) hsk
  have h6 := mul_le_mul_of_nonneg_left hW3 hq0.le
  have e : q * (Real.sqrt k * (q * (q * T.Rmax θ))) = Real.sqrt k * (q ^ 3 * T.Rmax θ) := by ring
  rw [e] at h6
  unfold root at hN h6 ⊢
  unfold root at hW3
  linarith

end Tracker

namespace Tracker

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]
variable [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]
variable (T : Tracker X ι 𝒜) (hT : T.Meas) (θ : ι → ℝ) {ℓ κ A0 : ℝ}

lemma rk_ge_of_pow {B : ℝ} (hB : 0 ≤ B) {k : ℕ} (h : B ^ 16 ≤ (k : ℝ) + 1) : B ≤ rk k := by
  rw [← rk_pow k] at h
  exact (pow_le_pow_iff_left₀ hB (rk_pos k).le (by norm_num)).mp h

lemma inv_sq_le_inv (k : ℕ) : (rk k)⁻¹ ^ 2 ≤ (rk k)⁻¹ := by
  have h0 : 0 < (rk k)⁻¹ := inv_pos.mpr (rk_pos k)
  have h1 : (rk k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_rk k)
  nlinarith

/-- **Stage 3 (information growth, packaged).**  For every rate slack `0 < s < I_*(θ)` there
are a deterministic time `K0` and `q ∈ (0, 1)` such that, on every path, whenever all rounds
in `[T0, k]` are good with `K0 ≤ T0 ≤ (1 - q²) k`, the stopping statistic of `a†` satisfies
`J_k(a†) ≥ (I_*(θ) - s) k`. -/
theorem growth_package (hV : T.Valid ℓ κ A0) {s : ℝ} (hs : 0 < s) (hsI : s < T.Istar θ) :
    ∃ K0 : ℕ, ∃ q : ℝ, 0 < q ∧ q < 1 ∧ onset (Fintype.card X) ℓ κ ≤ K0 ∧
      ∀ (ω : ℕ → ℝ) (T0 k : ℕ), K0 ≤ T0 → T0 ≤ k → (T0 : ℝ) ≤ (1 - q ^ 2) * k →
        (∀ j, T0 ≤ j → j ≤ k → ω ∉ T.bad hT θ j) →
        (T.Istar θ - s) * k ≤ T.stat (T.aDag θ) (T.S hT θ k ω) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = T.Rmax θ := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; exact T.Rs_nonneg hV _ _
  have hI : T.Istar θ = R ^ 2 / 2 := by rw [hR]; rfl
  have hRpos : 0 < R := by
    rcases hR0.eq_or_lt with h0 | hpos
    · rw [hI, ← h0] at hsI
      norm_num at hsI
      linarith
    · exact hpos
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = Real.sqrt (2 * (T.Istar θ - s)) := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβ]; exact Real.sqrt_nonneg _
  have hβsq : β ^ 2 = 2 * (T.Istar θ - s) := by
    rw [hβ, Real.sq_sqrt (by linarith)]
  have hβR : β < R := by
    have : β ^ 2 < R ^ 2 := by rw [hβsq, hI]; linarith
    exact (pow_lt_pow_iff_left₀ hβ0 hR0 two_ne_zero).mp this
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (R - β) / (6 * R) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; exact div_pos (by linarith) (by positivity)
  have hxR : x * (6 * R) = R - β := by rw [hx]; field_simp
  have hx1 : x ≤ 1 / 6 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - x := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (R - β) / 2 := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hg0 : 0 < g := by rw [hg]; linarith
  have hqβ : β ≤ q ^ 3 * R - g := by
    have h1 : 1 - 3 * x ≤ q ^ 3 := by
      rw [hq]
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 3 - x)]
    have h2 := mul_le_mul_of_nonneg_right h1 hR0
    rw [hg]
    nlinarith
  obtain ⟨Δ, hΔ0, hΔ⟩ := T.exists_gap θ
  have hK1 : 0 ≤ K1 ℓ A0 θ := by
    unfold K1
    have := Real.sqrt_nonneg (2 * (Cbar ℓ A0 θ + 1))
    linarith [hV.hℓ]
  have hκ := hV.hκ
  have hℓ := hV.hℓ
  have hq2 : 0 < 1 - q ^ 2 := by nlinarith
  have hcm0 : 0 ≤ cmC (Fintype.card X) ℓ := by
    have : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
    have h1 : (0 : ℝ) ≤ (Fintype.card X : ℝ) - 1 := by linarith
    unfold cmC
    positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * K1 ℓ A0 θ + (2 / Δ + 1) + 2 * K1 ℓ A0 θ / ((1 - q) * R) +
      2 * cmC (Fintype.card X) ℓ / (κ * (1 - q ^ 2)) + ℓ / g + 1 := ⟨_, rfl⟩
  have hq1' : 0 < 1 - q := by linarith
  have t1 : 0 ≤ 2 * K1 ℓ A0 θ := by positivity
  have t2 : 0 ≤ 2 / Δ + 1 := by positivity
  have t3 : 0 ≤ 2 * K1 ℓ A0 θ / ((1 - q) * R) := by positivity
  have t4 : 0 ≤ 2 * cmC (Fintype.card X) ℓ / (κ * (1 - q ^ 2)) := by positivity
  have t5 : 0 ≤ ℓ / g := by positivity
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  refine ⟨max (onset (Fintype.card X) ℓ κ) ⌈B ^ 16⌉₊, q, hq0, hq1, le_max_left _ _, ?_⟩
  intro ω T0 k hK0 hT0k hfrac hgood
  have hons : onset (Fintype.card X) ℓ κ ≤ T0 := (le_max_left _ _).trans hK0
  have hk1 : 1 ≤ k := le_trans (le_trans (Nat.le_add_left 1 _) hons) hT0k
  have hBT0 : B ≤ rk T0 := by
    apply rk_ge_of_pow hB0
    have h1 : B ^ 16 ≤ (⌈B ^ 16⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈B ^ 16⌉₊ : ℕ) : ℝ) ≤ T0 := by exact_mod_cast (le_max_right _ _).trans hK0
    linarith
  have hBk : B ≤ rk k := hBT0.trans (rk_mono hT0k)
  have hr0 := rk_pos T0
  have hrk := rk_pos k
  have hinv0 : 0 < (rk T0)⁻¹ := inv_pos.mpr hr0
  have hinvk : 0 < (rk k)⁻¹ := inv_pos.mpr hrk
  have h2K : 2 * K1 ℓ A0 θ ≤ rk T0 := by rw [hB] at hBT0; linarith
  have hΔ' : 2 * (rk T0)⁻¹ < Δ := by
    have h1 : 2 / Δ + 1 ≤ rk T0 := by rw [hB] at hBT0; linarith
    have h2 : 2 / Δ < rk T0 := by linarith
    rw [div_lt_iff₀ hΔ0] at h2
    rw [← div_eq_mul_inv, div_lt_iff₀ hr0]
    linarith
  have hqual : 2 * K1 ℓ A0 θ * (rk T0)⁻¹ ^ 2 ≤ (1 - q) * T.Rmax θ := by
    rw [← hR]
    have h1 : 2 * K1 ℓ A0 θ / ((1 - q) * R) ≤ rk T0 := by rw [hB] at hBT0; linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : 2 * K1 ℓ A0 θ * (rk T0)⁻¹ ≤ (1 - q) * R := by
      rw [← div_eq_mul_inv, div_le_iff₀ hr0]
      linarith
    have h3 := mul_le_mul_of_nonneg_left (inv_sq_le_inv T0) t1
    linarith
  have hEk := cumEta_ge hk1
  have hr1 := one_le_rk k
  have hEpos : 0 < cumEta k := by
    have : 0 < rk k ^ 12 / 2 := by positivity
    linarith
  have hρ : cmC (Fintype.card X) ℓ ≤ (1 - q ^ 2) * (κ * cumEta k) := by
    have h1 : 2 * cmC (Fintype.card X) ℓ / (κ * (1 - q ^ 2)) ≤ rk k := by rw [hB] at hBk; linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : rk k ≤ rk k ^ 12 := le_self_pow₀ hr1 (by norm_num)
    have h3 : rk k / 2 ≤ cumEta k := by linarith
    have h4 : 0 < κ * (1 - q ^ 2) := by positivity
    nlinarith
  have hpert : ℓ * (rk k)⁻¹ ^ 2 ≤ g := by
    have h1 : ℓ / g ≤ rk k := by rw [hB] at hBk; linarith
    rw [div_le_iff₀ hg0] at h1
    have h2 : ℓ * (rk k)⁻¹ ≤ g := by
      rw [← div_eq_mul_inv, div_le_iff₀ hrk]
      linarith
    have h3 := mul_le_mul_of_nonneg_left (inv_sq_le_inv k) hℓ.le
    linarith
  have hmain := T.stat_growth hT θ hV ω hq0 hq1 hT0k hfrac hgood hΔ h2K hΔ' hqual hρ hEpos hpert
  rw [← hR] at hmain
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have h1 : Real.sqrt k * β ≤ T.root (T.aDag θ) (WithLp.toLp 2 (T.thetaHat hT θ k ω))
      (fun x => ((T.S hT θ k ω).1 x : ℝ)) :=
    (mul_le_mul_of_nonneg_left hqβ hsk).trans hmain
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k), hβsq] at h2
  have hstat : T.stat (T.aDag θ) (T.S hT θ k ω) =
      T.root (T.aDag θ) (WithLp.toLp 2 (T.thetaHat hT θ k ω))
        (fun x => ((T.S hT θ k ω).1 x : ℝ)) ^ 2 / 2 := rfl
  rw [hstat]
  linarith

/-! ### Stage 4: pathwise domination by an integrable time -/

/-- Constant term of the threshold bound after the last bad time. -/
def c2C (d : ℕ) (ℓ γ : ℝ) (θ : ι → ℝ) : ℝ :=
  (d : ℝ) / 2 * Real.log (max 1 (ℓ ^ 2 / (d * γ))) +
    γ / 2 * (‖(WithLp.toLp 2 θ : EuclideanSpace ℝ ι)‖ + 1) ^ 2

lemma c2C_nonneg (d : ℕ) {ℓ γ : ℝ} (hγ : 0 < γ) (θ : ι → ℝ) : 0 ≤ c2C d ℓ γ θ := by
  unfold c2C
  have h1 : 0 ≤ Real.log (max 1 (ℓ ^ 2 / (d * γ))) := Real.log_nonneg (le_max_left _ _)
  positivity

/-- After the onset and on a good round, `H_k(δ) ≤ log(1/δ) + (d/2) log(1 + k) + c₂`. -/
lemma thr_le (hV : T.Valid ℓ κ A0) [Nonempty ι] (ω : ℕ → ℝ) (k : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hc : Coercive (T.Gm (T.S hT θ k ω).1) lam) (hgood : ω ∉ T.bad hT θ k) (δ : ℝ) :
    T.thr δ (T.S hT θ k ω) ≤ Real.log (1 / δ) +
      (Fintype.card ι : ℝ) / 2 * Real.log (1 + k) + c2C (Fintype.card ι) ℓ T.γ θ := by
  have hγ := hV.hγ
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc' : Coercive (gram (fun j => T.u (T.qry hT θ j ω)) k) lam := by
    rw [← T.Gm_eq hT θ ω k]
    exact hc
  have h := mixThreshold_le (fun j => T.u (T.qry hT θ j ω)) k (δ := δ) (fun s => hV.hu _) hc' hlam
    hγ (T.S hT θ k ω).2.2
  rw [← T.Gm_eq hT θ ω k] at h
  have hθ : ((T.Gm (T.S hT θ k ω).1)⁻¹ *ᵥ (T.S hT θ k ω).2.2) ⬝ᵥ
      ((T.Gm (T.S hT θ k ω).1)⁻¹ *ᵥ (T.S hT θ k ω).2.2) =
      ‖(WithLp.toLp 2 (T.thetaHat hT θ k ω) : EuclideanSpace ℝ ι)‖ ^ 2 := by
    rw [norm_tE_sq]
    rfl
  rw [hθ] at h
  have hn := T.good_norm hT θ hgood
  have hρ1 : (rk k)⁻¹ ^ 2 ≤ 1 :=
    pow_le_one₀ (inv_pos.mpr (rk_pos k)).le (inv_le_one_of_one_le₀ (one_le_rk k))
  have hnorm : ‖(WithLp.toLp 2 (T.thetaHat hT θ k ω) : EuclideanSpace ℝ ι)‖ ≤
      ‖(WithLp.toLp 2 θ : EuclideanSpace ℝ ι)‖ + 1 := by
    have := norm_le_norm_add_norm_sub' (WithLp.toLp 2 (T.thetaHat hT θ k ω) : EuclideanSpace ℝ ι)
      (WithLp.toLp 2 θ)
    linarith
  have hsq : ‖(WithLp.toLp 2 (T.thetaHat hT θ k ω) : EuclideanSpace ℝ ι)‖ ^ 2 ≤
      (‖(WithLp.toLp 2 θ : EuclideanSpace ℝ ι)‖ + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ℓ ^ 2 / (Fintype.card ι * T.γ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hlog : Real.log (1 + k * ℓ ^ 2 / (Fintype.card ι * T.γ)) ≤
      Real.log (1 + k) + Real.log (max 1 c) := by
    have hm1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
    have hmc : c ≤ max 1 c := le_max_right _ _
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have e : (k : ℝ) * ℓ ^ 2 / (Fintype.card ι * T.γ) = k * c := by rw [hcdef]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hmc hk0]
  unfold thr
  unfold c2C
  rw [← hcdef]
  have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / 2)
  have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ T.γ / 2)
  linarith

/-- The stopping time of the tracker at confidence `δ` on the noise tape, in `[0, ∞]`. -/
def tauE (δ : ℝ) (ω : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ n, ((time (T.sampler hT δ) (tr (T.sampler hT δ) (T.mean θ) T.v n ω) : ℕ) : ℝ≥0∞)

lemma tauE_le_of_stop {δ : ℝ} {ω : ℕ → ℝ} {k : ℕ} (h : T.stopP δ (T.S hT θ k ω)) :
    T.tauE hT θ δ ω ≤ k := by
  refine iSup_le fun n => ?_
  have hs : (T.sampler hT δ).stop (run (T.sampler hT δ) (T.mean θ) T.v k ω) = true := by
    rw [sampler_stop_iff]
    exact h
  exact_mod_cast time_le_of_stop (T.sampler hT δ) (T.mean θ) T.v ω ⟨k, le_rfl, hs⟩ n

/-- The expected stopping time of `GaussianStopped.lean` is at most the expectation of the
stopping time on the tape. -/
lemma expTau_le (δ : ℝ) :
    expTau (T.sampler hT δ) (T.mean θ) T.v ≤ ∫⁻ ω, T.tauE hT θ δ ω ∂gP := by
  unfold expTau
  refine iSup_le fun n => ?_
  rw [expTime_eq_tape]
  have hmeas : Measurable fun ω : ℕ → ℝ =>
      (time (T.sampler hT δ) (tr (T.sampler hT δ) (T.mean θ) T.v n ω) : ℝ) :=
    (measurable_time (T.sampler hT δ) n).comp
      ((measurable_hist (T.sampler hT δ) (T.mean θ) T.v n).comp (measurable_rev n))
  have hint : Integrable (fun ω : ℕ → ℝ =>
      (time (T.sampler hT δ) (tr (T.sampler hT δ) (T.mean θ) T.v n ω) : ℝ)) gP := by
    refine Integrable.mono' (integrable_const (n : ℝ)) hmeas.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_natCast]
    have := time_le_length (T.sampler hT δ) (tr (T.sampler hT δ) (T.mean θ) T.v n ω)
    have hl : (tr (T.sampler hT δ) (T.mean θ) T.v n ω).length = n := by simp [tr]
    rw [hl] at this
    exact_mod_cast this
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => Nat.cast_nonneg _)]
  refine lintegral_mono fun ω => ?_
  rw [ENNReal.ofReal_natCast]
  exact le_iSup (fun n => ((time (T.sampler hT δ)
    (tr (T.sampler hT δ) (T.mean θ) T.v n ω) : ℕ) : ℝ≥0∞)) n

/-- A time after which the estimate is good forever: `∑_j (j + 1) 1{bad_j}`, which dominates
the last bad time. -/
def Tbad (ω : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞)) ω

lemma le_Tbad {j : ℕ} {ω : ℕ → ℝ} (h : ω ∈ T.bad hT θ j) :
    ((j + 1 : ℕ) : ℝ≥0∞) ≤ T.Tbad hT θ ω := by
  have := le_tsum
    (fun j : ℕ => (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞)) ω) j
  unfold Tbad
  rwa [Set.indicator_of_mem h] at this

/-- **The last bad time is integrable.** -/
theorem lintegral_Tbad_ne_top (hV : T.Valid ℓ κ A0) [Nonempty ι] :
    ∫⁻ ω, T.Tbad hT θ ω ∂gP ≠ ⊤ := by
  obtain ⟨C, hC0, hC⟩ := T.bad_poly hT θ hV
  unfold Tbad
  rw [lintegral_tsum
    (fun j => (measurable_const.indicator (T.measurableSet_bad hT θ j)).aemeasurable)]
  have hterm : ∀ j : ℕ,
      ∫⁻ ω, (T.bad hT θ j).indicator (fun _ => ((j + 1 : ℕ) : ℝ≥0∞)) ω ∂gP ≤
        ENNReal.ofReal (C / ((j : ℝ) + 1) ^ 2) := by
    intro j
    rw [lintegral_indicator_const (T.measurableSet_bad hT θ j)]
    calc ((j + 1 : ℕ) : ℝ≥0∞) * gP (T.bad hT θ j)
        ≤ ((j + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (C / ((j : ℝ) + 1) ^ 3) :=
          mul_le_mul' le_rfl (hC j)
      _ = ENNReal.ofReal (C / ((j : ℝ) + 1) ^ 2) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          push_cast
          field_simp
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hterm)
  have hsum : Summable fun j : ℕ => C / ((j : ℝ) + 1) ^ 2 := by
    have h1 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 := ((summable_nat_add_iff 1).mpr h1).mul_left C
    refine h2.congr fun j => ?_
    push_cast
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-- **Stage 4, core.**  For every rate slack `0 < s < I_*` there is an integrable time `T_s`,
independent of `δ`, such that on every path the tracker at any confidence `δ` has stopped by
`max {T_s, n}` for every `n` beyond which the linear information growth `(I_* - s) t`
dominates the threshold bound `log(1/δ) + (d/2) log(1 + t) + c₂`. -/
theorem pathwise_core (hV : T.Valid ℓ κ A0) [Nonempty ι] {s : ℝ} (hs : 0 < s)
    (hsI : s < T.Istar θ) :
    ∃ Tf : (ℕ → ℝ) → ℝ≥0∞, ∫⁻ ω, Tf ω ∂gP ≠ ⊤ ∧
      ∀ (δ : ℝ) (n : ℕ), (∀ t : ℝ, (n : ℝ) ≤ t →
          Real.log (1 / δ) + (Fintype.card ι : ℝ) / 2 * Real.log (1 + t) +
            c2C (Fintype.card ι) ℓ T.γ θ ≤ (T.Istar θ - s) * t) →
        ∀ ω, T.tauE hT θ δ ω ≤ max (Tf ω) (n : ℝ≥0∞) := by
  obtain ⟨K0, q, hq0, hq1, hons, hgrow⟩ := T.growth_package hT θ hV hs hsI
  have hq2 : 0 < 1 - q ^ 2 := by nlinarith
  have hq2' : 1 - q ^ 2 ≤ 1 := by nlinarith
  refine ⟨fun ω => ENNReal.ofReal (1 / (1 - q ^ 2)) *
    (T.Tbad hT θ ω + ((K0 + 1 : ℕ) : ℝ≥0∞)) + 1, ?_, ?_⟩
  · rw [lintegral_add_right _ measurable_const,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_right _ measurable_const]
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨T.lintegral_Tbad_ne_top hT θ hV, ENNReal.natCast_ne_top _⟩),
      ENNReal.one_ne_top⟩
  · intro δ n hnlin ω
    beta_reduce
    by_cases htop : T.Tbad hT θ ω = ⊤
    · have hpos : ENNReal.ofReal (1 / (1 - q ^ 2)) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      have : ENNReal.ofReal (1 / (1 - q ^ 2)) *
          (T.Tbad hT θ ω + ((K0 + 1 : ℕ) : ℝ≥0∞)) + 1 = ⊤ := by
        rw [htop, top_add, ENNReal.mul_top hpos, top_add]
      rw [this]
      simp
    · obtain ⟨tb, htb⟩ : ∃ tb : ℝ, tb = (T.Tbad hT θ ω).toReal := ⟨_, rfl⟩
      have htb0 : 0 ≤ tb := by rw [htb]; exact ENNReal.toReal_nonneg
      obtain ⟨Tn, hTn⟩ : ∃ Tn : ℕ, Tn = ⌈tb⌉₊ := ⟨_, rfl⟩
      have hTn1 : tb ≤ Tn := by rw [hTn]; exact Nat.le_ceil _
      have hTn2 : (Tn : ℝ) < tb + 1 := by rw [hTn]; exact Nat.ceil_lt_add_one htb0
      have hgoodj : ∀ j, Tn ≤ j → ω ∉ T.bad hT θ j := by
        intro j hj hbad
        have h1 := T.le_Tbad hT θ hbad
        have h2 := ENNReal.toReal_mono htop h1
        rw [← htb, ENNReal.toReal_natCast] at h2
        push_cast at h2
        have h3 : (Tn : ℝ) ≤ j := by exact_mod_cast hj
        linarith
      obtain ⟨T0, hT0⟩ : ∃ T0 : ℕ, T0 = max K0 Tn := ⟨_, rfl⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌈(T0 : ℝ) / (1 - q ^ 2)⌉₊ := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max a n := ⟨_, rfl⟩
      have hT0nn : (0 : ℝ) ≤ T0 := Nat.cast_nonneg _
      have ha1 : (T0 : ℝ) / (1 - q ^ 2) ≤ a := by rw [ha]; exact Nat.le_ceil _
      have ha2 : (a : ℝ) < (T0 : ℝ) / (1 - q ^ 2) + 1 := by
        rw [ha]
        exact Nat.ceil_lt_add_one (by positivity)
      have hak : (a : ℝ) ≤ k := by
        have : a ≤ k := by rw [hk]; exact le_max_left _ _
        exact_mod_cast this
      have hnk : (n : ℝ) ≤ k := by
        have : n ≤ k := by rw [hk]; exact le_max_right _ _
        exact_mod_cast this
      have hfrac : (T0 : ℝ) ≤ (1 - q ^ 2) * k := by
        have h1 := (div_le_iff₀ hq2).mp (ha1.trans hak)
        linarith
      have hT0k' : (T0 : ℝ) ≤ k := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      have hT0k : T0 ≤ k := by exact_mod_cast hT0k'
      have hK0T0 : K0 ≤ T0 := by rw [hT0]; exact le_max_left _ _
      have hTnT0 : Tn ≤ T0 := by rw [hT0]; exact le_max_right _ _
      have hgood : ∀ j, T0 ≤ j → j ≤ k → ω ∉ T.bad hT θ j := fun j hj _ =>
        hgoodj j (hTnT0.trans hj)
      have hstat := hgrow ω T0 k hK0T0 hT0k hfrac hgood
      have hcoer := T.coercive_onset hT θ hV ω (hons.trans (hK0T0.trans hT0k))
      have hlampos : 0 < κ * rk k ^ 12 / 4 := by
        have := hV.hκ
        have := rk_pos k
        positivity
      have hthr := T.thr_le hT θ hV ω k hlampos hcoer (hgood k hT0k le_rfl) δ
      have hlin' := hnlin (k : ℝ) hnk
      have hstop : T.stopP δ (T.S hT θ k ω) :=
        ⟨⟨_, hlampos, hcoer⟩, T.aDag θ, by linarith⟩
      refine (T.tauE_le_of_stop hT θ hstop).trans ?_
      rw [hk, (Nat.mono_cast (α := ℝ≥0∞)).map_max]
      refine max_le_max ?_ le_rfl
      -- `a ≤ T_s`
      have hTnE : (Tn : ℝ≥0∞) ≤ T.Tbad hT θ ω + 1 := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_toReal htop, ← htb, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add htb0 zero_le_one]
        exact ENNReal.ofReal_le_ofReal hTn2.le
      have hT0E : (T0 : ℝ≥0∞) ≤ T.Tbad hT θ ω + ((K0 + 1 : ℕ) : ℝ≥0∞) := by
        have h1 : T0 ≤ K0 + Tn := by
          rw [hT0]
          exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
        calc (T0 : ℝ≥0∞) ≤ ((K0 + Tn : ℕ) : ℝ≥0∞) := by exact_mod_cast h1
          _ = (K0 : ℝ≥0∞) + Tn := by push_cast; rfl
          _ ≤ (K0 : ℝ≥0∞) + (T.Tbad hT θ ω + 1) := by gcongr
          _ = T.Tbad hT θ ω + ((K0 + 1 : ℕ) : ℝ≥0∞) := by
              push_cast
              ring
      calc (a : ℝ≥0∞) = ENNReal.ofReal (a : ℝ) := (ENNReal.ofReal_natCast a).symm
        _ ≤ ENNReal.ofReal (1 / (1 - q ^ 2) * (T0 : ℝ) + 1) := by
            apply ENNReal.ofReal_le_ofReal
            have e : 1 / (1 - q ^ 2) * (T0 : ℝ) = (T0 : ℝ) / (1 - q ^ 2) := by ring
            rw [e]
            exact ha2.le
        _ = ENNReal.ofReal (1 / (1 - q ^ 2)) * (T0 : ℝ≥0∞) + 1 := by
            rw [ENNReal.ofReal_add (by positivity) zero_le_one,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal (1 / (1 - q ^ 2)) *
              (T.Tbad hT θ ω + ((K0 + 1 : ℕ) : ℝ≥0∞)) + 1 := by gcongr

/-- **Stage 4 (pathwise domination).**  For every rate slack `s ∈ (0, I_*/2)` there are an
integrable time `T_s`, independent of `δ`, and `δ₀ > 0` such that for all `δ < δ₀`, on every
path, `τ_δ ≤ max {T_s, ⌈log(1/δ) / (I_* - 2s)⌉}`. -/
theorem pathwise (hV : T.Valid ℓ κ A0) [Nonempty ι] {s : ℝ} (hs : 0 < s)
    (hsI : 2 * s < T.Istar θ) :
    ∃ (Tf : (ℕ → ℝ) → ℝ≥0∞) (δ0 : ℝ), 0 < δ0 ∧ ∫⁻ ω, Tf ω ∂gP ≠ ⊤ ∧
      ∀ δ, 0 < δ → δ < δ0 → ∀ ω, T.tauE hT θ δ ω ≤
        max (Tf ω) ((⌈Real.log (1 / δ) / (T.Istar θ - 2 * s)⌉₊ : ℕ) : ℝ≥0∞) := by
  obtain ⟨Tf, hTf, hcore⟩ := T.pathwise_core hT θ hV hs (by linarith)
  obtain ⟨δ0, hδ0, hlin⟩ := linear_beats_log (I := T.Istar θ) (s := s)
    (c1 := (Fintype.card ι : ℝ) / 2) (c2 := c2C (Fintype.card ι) ℓ T.γ θ) hs hsI
    (c2C_nonneg _ hV.hγ θ)
  refine ⟨Tf, δ0, hδ0, hTf, fun δ hδ hδlt ω => hcore δ _ (fun t ht => ?_) ω⟩
  exact hlin δ hδ hδlt t ((Nat.le_ceil _).trans ht)

/-- The expected stopping time of the tracker is finite at every confidence `δ ∈ (0, 1)`
("the same eventual linear-versus-logarithmic comparison proves finite expectation for
every fixed `δ`"). -/
theorem expTau_ne_top (hV : T.Valid ℓ κ A0) [Nonempty ι] (hI : 0 < T.Istar θ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) : expTau (T.sampler hT δ) (T.mean θ) T.v ≠ ⊤ := by
  obtain ⟨Tf, hTf, hcore⟩ := T.pathwise_core hT θ hV (s := T.Istar θ / 4) (by positivity)
    (by linarith)
  obtain ⟨δ2, hδ2, hlin⟩ := linear_beats_log (I := T.Istar θ) (s := T.Istar θ / 4)
    (c1 := (Fintype.card ι : ℝ) / 2) (c2 := c2C (Fintype.card ι) ℓ T.γ θ) (by positivity)
    (by linarith) (c2C_nonneg _ hV.hγ θ)
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min δ2 δ / 2 := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; exact half_pos (lt_min hδ2 hδ0)
  have hδ'2 : δ' < δ2 := by
    rw [hδ']
    linarith [min_le_left δ2 δ, lt_min hδ2 hδ0]
  have hδ'δ : δ' ≤ δ := by
    rw [hδ']
    linarith [min_le_right δ2 δ, lt_min hδ2 hδ0]
  have hlog : Real.log (1 / δ) ≤ Real.log (1 / δ') :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδ'0 hδ'δ)
  have hpath := hcore δ ⌈Real.log (1 / δ') / (T.Istar θ - 2 * (T.Istar θ / 4))⌉₊ (fun t ht => by
    have := hlin δ' hδ'0 hδ'2 t ((Nat.le_ceil _).trans ht)
    linarith)
  have hle : ∫⁻ ω, T.tauE hT θ δ ω ∂gP ≤ ∫⁻ ω, (Tf ω +
      ((⌈Real.log (1 / δ') / (T.Istar θ - 2 * (T.Istar θ / 4))⌉₊ : ℕ) : ℝ≥0∞)) ∂gP :=
    lintegral_mono fun ω => (hpath ω).trans
      (max_le (le_add_of_nonneg_right bot_le) (le_add_of_nonneg_left bot_le))
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one] at hle
  exact ne_top_of_le_ne_top
    (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hTf, ENNReal.natCast_ne_top _⟩) hle)
    (T.expTau_le hT θ δ)

/-! ### Stage 5: the upper half -/

/-- **Stage 5 (upper half of `thm:bay-main-optimal`).**
`limsup_{δ ↓ 0} E_θ τ_δ / log(1/δ) ≤ 1 / I_*(θ)` for the tracker: for every `η > 0`,
eventually the expected stopping time is finite and the ratio is at most `1/I_* + η`. -/
theorem upper_half (hV : T.Valid ℓ κ A0) [Nonempty ι] (hI : 0 < T.Istar θ) :
    ∀ η > 0, ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 →
      expTau (T.sampler hT δ) (T.mean θ) T.v ≠ ⊤ ∧
        (expTau (T.sampler hT δ) (T.mean θ) T.v).toReal / Real.log (1 / δ) ≤
          1 / T.Istar θ + η := by
  intro η hη
  obtain ⟨δ1, hδ1, hrate⟩ := upper_half_of_pathwise gP hI (T.tauE hT θ)
    (fun s hs hsI => T.pathwise hT θ hV hs hsI) η hη
  obtain ⟨Tf, δ2, hδ2, hTf, hpath⟩ := T.pathwise hT θ hV (s := T.Istar θ / 4) (by positivity)
    (by linarith)
  refine ⟨min (min δ1 δ2) 1, lt_min (lt_min hδ1 hδ2) one_pos, fun δ hδ hlt => ?_⟩
  have hlt1 : δ < δ1 := hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hlt2 : δ < δ2 := hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlt3 : δ < 1 := hlt.trans_le (min_le_right _ _)
  have hfin : ∫⁻ ω, T.tauE hT θ δ ω ∂gP ≠ ⊤ := by
    have hle : ∫⁻ ω, T.tauE hT θ δ ω ∂gP ≤ ∫⁻ ω, (Tf ω +
        ((⌈Real.log (1 / δ) / (T.Istar θ - 2 * (T.Istar θ / 4))⌉₊ : ℕ) : ℝ≥0∞)) ∂gP :=
      lintegral_mono fun ω => (hpath δ hδ hlt2 ω).trans
        (max_le (le_add_of_nonneg_right bot_le) (le_add_of_nonneg_left bot_le))
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one] at hle
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hTf, ENNReal.natCast_ne_top _⟩) hle
  have hle := T.expTau_le hT θ δ
  have hne : expTau (T.sampler hT δ) (T.mean θ) T.v ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  refine ⟨hne, ?_⟩
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have h1 := ENNReal.toReal_mono hfin hle
  exact (div_le_div_of_nonneg_right h1 hL.le).trans (hrate δ hδ hlt1)

end Tracker

/-- `det (I + G_t / γ) ≥ 1` for a Gram matrix, by the matrix determinant lemma. -/
lemma one_le_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ℝ} (hγ : 0 < γ)
    (u : ℕ → ι → ℝ) : ∀ t : ℕ, 1 ≤ (1 + γ⁻¹ • gram u t).det := by
  have hco : ∀ t, Coercive (1 + γ⁻¹ • gram u t) 1 := by
    intro t
    refine ⟨?_, fun x => ?_⟩
    · rw [transpose_add, transpose_one, transpose_smul, gram_symm]
    · rw [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
        one_mul, gram_quadratic]
      have : 0 ≤ γ⁻¹ * ∑ s ∈ range t, (u s ⬝ᵥ x) ^ 2 :=
        mul_nonneg (inv_pos.mpr hγ).le (sum_nonneg fun _ _ => sq_nonneg _)
      linarith
  intro t
  induction t with
  | zero => simp [gram]
  | succ t ih =>
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt γ⁻¹ := ⟨_, rfl⟩
    have hcc : c * c = γ⁻¹ := by rw [hc]; exact Real.mul_self_sqrt (inv_pos.mpr hγ).le
    have hstep : (1 : Matrix ι ι ℝ) + γ⁻¹ • gram u (t + 1) =
        (1 + γ⁻¹ • gram u t) + vecMulVec (c • u t) (c • u t) := by
      have h1 : vecMulVec (c • u t) (c • u t) = γ⁻¹ • vecMulVec (u t) (u t) := by
        ext i j
        simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
        rw [← hcc]
        ring
      rw [h1, gram, gram, sum_range_succ, smul_add, add_assoc]
    rw [hstep, (hco t).det_rank_one one_pos]
    have hq := (hco t).qinv_nonneg one_pos (c • u t)
    nlinarith

namespace Tracker

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]
variable [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒜]
variable (T : Tracker X ι 𝒜) (hT : T.Meas) (θ : ι → ℝ) {ℓ κ A0 : ℝ}

/-! ### Stage 6: safety -/

/-- The threshold `H_k(δ)` is positive when `G_k` is invertible and `δ < 1`. -/
lemma thr_pos (hV : T.Valid ℓ κ A0) (ω : ℕ → ℝ) (k : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hc : Coercive (T.Gm (T.S hT θ k ω).1) lam) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < T.thr δ (T.S hT θ k ω) := by
  unfold thr mixThreshold
  have h1 : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have h2 : 0 ≤ Real.log (1 + T.γ⁻¹ • T.Gm (T.S hT θ k ω).1).det := by
    rw [T.Gm_eq hT θ ω k]
    exact Real.log_nonneg (one_le_det_gram hV.hγ _ k)
  have h3 := (mixGap_bounds hc hlam hV.hγ (T.S hT θ k ω).2.2).1
  linarith

lemma designMap_injective (N : X → ℕ) {lam : ℝ} (hlam : 0 < lam) (hc : Coercive (T.Gm N) lam) :
    Function.Injective (designMap T.uE (fun x => (N x : ℝ))) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  have h1 : ‖designMap T.uE (fun x => (N x : ℝ)) z‖ ^ 2 = z.ofLp ⬝ᵥ T.Gm N *ᵥ z.ofLp := by
    rw [T.dm_sq (fun x => Nat.cast_nonneg _), quad_Gm]
  rw [hz, norm_zero] at h1
  have h2 := hc.coer z.ofLp
  have h3 : z.ofLp ⬝ᵥ z.ofLp ≤ 0 := by
    by_contra hpos
    have := mul_pos hlam (not_le.mp hpos)
    nlinarith
  have h4 := eq_zero_of_dotProduct_self_nonpos h3
  ext i
  have := congrFun h4 i
  simpa using this

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **Stage 6 (safety).**  Let the alternative sets be the strict invalidating alternatives
of the root actions, `Q_a = {λ : r_λ(a) > ε}`.  Under every parameter `θ'`, the tracker at
confidence `δ` halts with an answer that is not `ε`-acceptable at `θ'` with probability at
most `δ`, at every horizon.  The proof is the coverage of the confidence sequence `C_t(δ)`
(`bay_cs_coverage_subgaussian`) together with `certified_of_threshold`; no property of the
allocation is used. -/
theorem safe_joint (hV : T.Valid ℓ κ A0) (φ : Z → EuclideanSpace ℝ ι) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, T.Q a = strictAlt φ (supp a) (hne a) ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (θ' : ι → ℝ) (n : ℕ) :
    law (T.sampler hT δ) (T.mean θ') T.v n
      (⋃ a ∈ {a : 𝒜 | (WithLp.toLp 2 θ' : EuclideanSpace ℝ ι) ∈ T.Q a},
        ansSet (T.sampler hT δ) (T.decision hT δ) a n) ≤ ENNReal.ofReal δ := by
  have hmeas : MeasurableSet (⋃ a ∈ {a : 𝒜 | (WithLp.toLp 2 θ' : EuclideanSpace ℝ ι) ∈ T.Q a},
      ansSet (T.sampler hT δ) (T.decision hT δ) a n) :=
    MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
      measurableSet_ansSet (T.sampler hT δ) (T.decision hT δ) a n
  rw [law_apply_tape _ _ _ _ hmeas]
  have hcov := bay_cs_coverage_subgaussian (μ := gP) tapeFilt hδ0 hV.hγ
    (u := fun s ω => T.u (T.qry hT θ' s ω)) (ν := fun s ω => ω s) θ'
    (fun s => (Measurable.of_discrete (f := T.u)).comp (T.measurable_qry hT θ' s))
    (fun s => measurable_tapeFilt_coord (Nat.lt_succ_self s)) (fun s => condSubG_coord s)
  refine (measure_mono ?_).trans hcov
  intro ω hω
  obtain ⟨a, hθ', hmemA⟩ := Set.mem_iUnion₂.mp hω
  have hθ'' : (WithLp.toLp 2 θ' : EuclideanSpace ℝ ι) ∈ T.Q a := hθ'
  have h1 : halted (T.sampler hT δ) (tr (T.sampler hT δ) (T.mean θ') T.v n ω) = true := hmemA.1
  have h2 : decAt (T.sampler hT δ) (T.decision hT δ)
      (tr (T.sampler hT δ) (T.mean θ') T.v n ω) = a := hmemA.2
  obtain ⟨k, hk1, hk2⟩ := ans_of_halted (T.sampler hT δ) (T.decision hT δ) (T.mean θ') T.v ω n
    h1 h2
  rw [sampler_stop_iff] at hk1
  have hk1' : T.stopP δ (T.S hT θ' k ω) := hk1
  obtain ⟨⟨lam, hlam, hco⟩, a', ha'⟩ := hk1'
  have hmem : a ∈ T.certSet δ (T.S hT θ' k ω) := by
    have hpk : pick (T.certSet δ (T.S hT θ' k ω)) = a := hk2
    rw [← hpk]
    exact pick_mem ⟨a', by simp [certSet, ha']⟩
  have hthr : T.thr δ (T.S hT θ' k ω) ≤ T.stat a (T.S hT θ' k ω) := by
    simpa [certSet] using hmem
  by_contra hnot
  have hle : 1 / 2 * ((θ' - T.thetaHat hT θ' k ω) ⬝ᵥ
      T.Gm (T.S hT θ' k ω).1 *ᵥ (θ' - T.thetaHat hT θ' k ω)) ≤ T.thr δ (T.S hT θ' k ω) := by
    by_contra hlt
    rw [not_le] at hlt
    refine hnot ⟨k, ⟨lam, hlam, ?_⟩, ?_⟩
    · rw [← T.Gm_eq hT θ' ω k]
      exact hco
    · rw [← T.Gm_eq hT θ' ω k, ← T.b_eq hT θ' hV.hv ω k]
      exact hlt
  have hG := T.designMap_injective (T.S hT θ' k ω).1 hlam hco
  have hH := T.thr_pos hT θ' hV ω k hlam hco hδ0 hδ1
  have hstopc : ∀ l ∈ strictAlt φ (supp a) (hne a) ε, T.thr δ (T.S hT θ' k ω) ≤
      ‖designMap T.uE (fun x => ((T.S hT θ' k ω).1 x : ℝ))
        (l - WithLp.toLp 2 (T.thetaHat hT θ' k ω))‖ ^ 2 / 2 := by
    intro l hl
    rw [← hQ a] at hl
    refine hthr.trans ?_
    have h3 := rootInfo_le (A := designMap T.uE (fun x => ((T.S hT θ' k ω).1 x : ℝ)))
      (θ := (WithLp.toLp 2 (T.thetaHat hT θ' k ω) : EuclideanSpace ℝ ι)) hl
    have h4 := pow_le_pow_left₀ rootInfo_nonneg h3 2
    have hst : T.stat a (T.S hT θ' k ω) =
        rootInfo (designMap T.uE (fun x => ((T.S hT θ' k ω).1 x : ℝ))) (T.Q a)
          (WithLp.toLp 2 (T.thetaHat hT θ' k ω)) ^ 2 / 2 := rfl
    rw [hst]
    linarith
  have hcovE : ‖designMap T.uE (fun x => ((T.S hT θ' k ω).1 x : ℝ))
      ((WithLp.toLp 2 θ' : EuclideanSpace ℝ ι) - WithLp.toLp 2 (T.thetaHat hT θ' k ω))‖ ^ 2 / 2 ≤
      T.thr δ (T.S hT θ' k ω) := by
    rw [← WithLp.toLp_sub, T.dm_sq (fun x => Nat.cast_nonneg _), ← quad_Gm]
    have e : (WithLp.toLp 2 (θ' - T.thetaHat hT θ' k ω) : EuclideanSpace ℝ ι).ofLp =
        θ' - T.thetaHat hT θ' k ω := rfl
    rw [e]
    linarith
  have hcert := certified_of_threshold (hne a)
    (designMap T.uE (fun x => ((T.S hT θ' k ω).1 x : ℝ))) hG hH hstopc hcovE
  rw [hQ a] at hθ''
  have hbad : ε < regret (supp a) (hne a) (env φ (WithLp.toLp 2 θ')) := hθ''
  linarith

/-- Safety, one action at a time (the form used as the hypothesis of the lower bound). -/
theorem safe (hV : T.Valid ℓ κ A0) (φ : Z → EuclideanSpace ℝ ι) (supp : 𝒜 → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, T.Q a = strictAlt φ (supp a) (hne a) ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (θ' : ι → ℝ) (a : 𝒜) (hθ' : (WithLp.toLp 2 θ' : EuclideanSpace ℝ ι) ∈ T.Q a) (n : ℕ) :
    law (T.sampler hT δ) (T.mean θ') T.v n
      (ansSet (T.sampler hT δ) (T.decision hT δ) a n) ≤ ENNReal.ofReal δ :=
  (measure_mono (Set.subset_biUnion_of_mem
    (s := {a : 𝒜 | (WithLp.toLp 2 θ' : EuclideanSpace ℝ ι) ∈ T.Q a})
    (u := fun a => ansSet (T.sampler hT δ) (T.decision hT δ) a n) hθ')).trans
    (T.safe_joint hT hV φ supp hne ε hQ hδ0 hδ1 θ' n)

/-! ### Stage 7: the theorem -/

lemma mean_eq (θ : ι → ℝ) :
    T.mean θ = fun x => Real.sqrt (T.v x) * ⟪T.uE x, (WithLp.toLp 2 θ : EuclideanSpace ℝ ι)⟫ := by
  funext x
  rw [inner_uE]
  rfl

lemma mean_ofLp_eq :
    (fun (x : X) (lam : EuclideanSpace ℝ ι) => T.mean lam.ofLp x) =
      fun x lam => Real.sqrt (T.v x) * ⟪T.uE x, lam⟫ := by
  funext x lam
  rw [inner_uE]
  rfl

/-- `I_*(θ)` bounds every `I_a(θ, w)`. -/
lemma info_le_Istar (hV : T.Valid ℓ κ A0) (a : 𝒜) {w : X → ℝ} (hw : w ∈ simplex X) :
    gInfo T.uE (T.Q a) (WithLp.toLp 2 θ) w ≤ T.Istar θ := by
  rw [gInfo_eq]
  have h1 := T.root_le_Rs hV a (WithLp.toLp 2 θ) hw
  have h2 := T.sc_le_Rmax θ a
  have h3 : T.root a (WithLp.toLp 2 θ) w ≤ T.Rmax θ := h1.trans h2
  have h4 := pow_le_pow_left₀ (T.root_nonneg _ _ _) h3 2
  unfold Istar
  linarith

/-- `I_*(θ) = max_a max_w I_a(θ, w)`, as a least upper bound. -/
theorem Istar_isLUB (hV : T.Valid ℓ κ A0) :
    IsLUB {r : ℝ | ∃ a, ∃ w ∈ simplex X, r = gInfo T.uE (T.Q a) (WithLp.toLp 2 θ) w}
      (T.Istar θ) := by
  constructor
  · rintro _ ⟨a, w, hw, rfl⟩
    exact T.info_le_Istar θ hV a hw
  · intro c hc
    by_contra hlt
    rw [not_le] at hlt
    have hc0 : 0 ≤ c := by
      have := hc ⟨T.aDag θ, T.w0, hV.hw0, rfl⟩
      exact gInfo_nonneg.trans this
    have hR0 : 0 ≤ T.Rmax θ := T.Rs_nonneg hV _ _
    have h1 : Real.sqrt (2 * c) < T.Rmax θ := by
      rw [Real.sqrt_lt' ]
      · unfold Istar at hlt
        linarith
      · rcases hR0.eq_or_lt with h0 | hpos
        · unfold Istar at hlt
          rw [← h0] at hlt
          norm_num at hlt
          linarith
        · exact hpos
    have hne : ((fun w => T.root (T.aDag θ) (WithLp.toLp 2 θ) w) '' simplex X).Nonempty :=
      ⟨_, T.w0, hV.hw0, rfl⟩
    obtain ⟨_, ⟨w, hw, rfl⟩, hgt⟩ := exists_lt_of_lt_csSup hne h1
    have h2 := hc ⟨T.aDag θ, w, hw, rfl⟩
    rw [gInfo_eq] at h2
    have h3 : 2 * c < T.root (T.aDag θ) (WithLp.toLp 2 θ) w ^ 2 := by
      have := Real.lt_sq_of_sqrt_lt hgt
      linarith
    linarith

/-- **Correlated Gaussian information limit (`thm:bay-main-optimal`).**

Model: queries `x` with whitened features `u_x ∈ ℝ^d` and known variances `v_x > 0`; under
the parameter `λ` the observation of `x` is `N(√(v_x) ⟨u_x, λ⟩, v_x)`.  Root actions `a`
have supports `supp a` among terminals with features `φ`; `Q_a = {λ : r_λ(a) > ε}`.
`I_*(θ) = max_a max_w I_a(θ, w)` (`Istar_isLUB`), assumed positive.

Conclusions:
1. the tracker `T.sampler` with decision `T.decision` is uniformly `δ`-correct;
2. every uniformly correct family of procedures has
   `liminf E_θ τ_δ / log(1/δ) ≥ 1 / I_*(θ)`;
3. the tracker has `limsup E_θ τ_δ / log(1/δ) ≤ 1 / I_*(θ)`;
4. its expected stopping time is finite for every `δ ∈ (0, 1)`;
5. hence the tracker attains equality.

Hypotheses: `T.Valid` (positive variances, bounded features, a reference design with
`M(w⁰) ⪰ κ I`, an anchor in each alternative set, and the oracle contract
`eq:bay-oracle-contract`) and `T.Meas` (Borel measurability of the oracle in the
estimate). -/
theorem bay_main_optimal (hV : T.Valid ℓ κ A0) [Nonempty ι] (φ : Z → EuclideanSpace ℝ ι)
    (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQ : ∀ a, T.Q a = strictAlt φ (supp a) (hne a) ε) (hI : 0 < T.Istar θ) :
    (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ T.Q a, ∀ n,
        law (T.sampler hT δ) (T.mean lam.ofLp) T.v n
          (ansSet (T.sampler hT δ) (T.decision hT δ) a n) ≤ ENNReal.ofReal δ) ∧
    (∀ (S : ℝ → GSampler X) (D : ℝ → GDecision 𝒜),
        (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ T.Q a, ∀ n,
          law (S δ) (T.mean lam.ofLp) T.v n (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ) →
        ∀ c : ℝ, c < 1 / T.Istar θ → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
          ENNReal.ofReal (c * Real.log (1 / δ)) ≤ expTau (S δ) (T.mean θ) T.v) ∧
    (∀ η > 0, ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 →
        expTau (T.sampler hT δ) (T.mean θ) T.v ≠ ⊤ ∧
          (expTau (T.sampler hT δ) (T.mean θ) T.v).toReal / Real.log (1 / δ) ≤
            1 / T.Istar θ + η) ∧
    (∀ δ, 0 < δ → δ < 1 → expTau (T.sampler hT δ) (T.mean θ) T.v ≠ ⊤) ∧
    (∀ c : ℝ, c < 1 / T.Istar θ → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (c * Real.log (1 / δ)) ≤
          expTau (T.sampler hT δ) (T.mean θ) T.v) := by
  have hsafe : ∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ T.Q a, ∀ n,
      law (T.sampler hT δ) (T.mean lam.ofLp) T.v n
        (ansSet (T.sampler hT δ) (T.decision hT δ) a n) ≤ ENNReal.ofReal δ := by
    intro δ hδ0 hδ1 a lam hlam n
    exact T.safe hT hV φ supp hne ε hQ hδ0 hδ1 lam.ofLp a hlam n
  have hlower : ∀ (S : ℝ → GSampler X) (D : ℝ → GDecision 𝒜),
      (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ T.Q a, ∀ n,
        law (S δ) (T.mean lam.ofLp) T.v n (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ) →
      ∀ c : ℝ, c < 1 / T.Istar θ → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (c * Real.log (1 / δ)) ≤ expTau (S δ) (T.mean θ) T.v := by
    intro S D hcorrect c hc
    refine gauss_info_lower_bound (fun (x : X) (lam : EuclideanSpace ℝ ι) => T.mean lam.ofLp x)
      T.Q hV.hv hI (fun a w hw ζ hζ => ?_) S D hcorrect hc
    have hglb := gcost_isGLB T.uE hV.hv hw.1 (WithLp.toLp 2 θ : EuclideanSpace ℝ ι)
      (T.Q_nonempty hV a)
    rw [← T.mean_eq θ, ← T.mean_ofLp_eq] at hglb
    have hlt : rootInfo (designMap T.uE w) (T.Q a) (WithLp.toLp 2 θ) ^ 2 / 2 < T.Istar θ + ζ := by
      have := T.info_le_Istar θ hV a hw
      rw [gInfo] at this
      linarith
    obtain ⟨_, ⟨lam, hlam, rfl⟩, hlam2⟩ := (isGLB_lt_iff hglb).mp hlt
    exact ⟨lam, hlam, hlam2⟩
  exact ⟨hsafe, hlower, T.upper_half hT θ hV hI,
    fun δ hδ0 hδ1 => T.expTau_ne_top hT θ hV hI hδ0 hδ1,
    hlower (T.sampler hT) (T.decision hT) hsafe⟩

end Tracker

/-! ### A measurable allocation oracle satisfying the contract

The manuscript obtains the oracle from a finite grid of the simplex.  Here a countable dense
sequence of designs is used instead: the oracle returns the first floored design of the
sequence whose exact value is within `η` of the supremum over the sequence.  This is not a
finite computation; it shows that the contract `Tracker.Valid` together with the
measurability `Tracker.Meas` can be met, so that the theorem is not vacuous. -/

section Oracle

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]

lemma exists_dense_simplex {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) :
    ∃ d : ℕ → X → ℝ, (∀ j, d j ∈ simplex X) ∧
      ∀ p ∈ simplex X, ∀ ε > 0, ∃ j, ∀ x, |d j x - p x| ≤ ε := by
  have hne : Nonempty (simplex X) := ⟨⟨w0, hw0⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (simplex X)
  refine ⟨fun j => (u j).1, fun j => (u j).2, fun p hp ε hε => ?_⟩
  obtain ⟨j, hj⟩ := hu.exists_dist_lt ⟨p, hp⟩ hε
  refine ⟨j, fun x => ?_⟩
  have h1 : dist ((u j).1 x) (p x) ≤ dist (u j).1 p := dist_le_pi_dist _ _ x
  have h2 : dist (u j).1 p = dist (u j) ⟨p, hp⟩ := rfl
  rw [Real.dist_eq] at h1
  rw [dist_comm] at hj
  linarith

/-- Exact value of the `j`-th floored design of the dense sequence. -/
def gridVal (uE : X → EuclideanSpace ℝ ι) (Qa : Set (EuclideanSpace ℝ ι)) (w0 : X → ℝ)
    (d : ℕ → X → ℝ) (k : ℕ) (θh : ι → ℝ) (j : ℕ) : ℝ :=
  gInfo uE Qa (WithLp.toLp 2 θh) (floorDesign (etaK k) w0 (d j))

lemma measurable_gridVal (uE : X → EuclideanSpace ℝ ι) (Qa : Set (EuclideanSpace ℝ ι))
    (w0 : X → ℝ) (d : ℕ → X → ℝ) (k j : ℕ) :
    Measurable fun θh : ι → ℝ => gridVal uE Qa w0 d k θh j := by
  have h2 : Continuous (designMap uE (floorDesign (etaK k) w0 (d j))) :=
    LinearMap.continuous_of_finiteDimensional _
  have h3 : Measurable fun θh : ι → ℝ =>
      designMap uE (floorDesign (etaK k) w0 (d j)) (WithLp.toLp 2 θh) :=
    Measurable.comp (g := fun z : EuclideanSpace ℝ ι =>
        designMap uE (floorDesign (etaK k) w0 (d j)) z)
      (f := fun θh : ι → ℝ => (WithLp.toLp 2 θh : EuclideanSpace ℝ ι))
      h2.measurable (WithLp.measurable_toLp 2 _)
  have h4 : Measurable fun θh : ι → ℝ =>
      Metric.infDist (designMap uE (floorDesign (etaK k) w0 (d j)) (WithLp.toLp 2 θh))
        (designMap uE (floorDesign (etaK k) w0 (d j)) '' Qa) :=
    Measurable.comp (g := fun z : EuclideanSpace ℝ X =>
        Metric.infDist z (designMap uE (floorDesign (etaK k) w0 (d j)) '' Qa))
      (f := fun θh : ι → ℝ => designMap uE (floorDesign (etaK k) w0 (d j)) (WithLp.toLp 2 θh))
      (Metric.continuous_infDist_pt _).measurable h3
  exact (h4.pow_const 2).div_const 2

variable (uE : X → EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hu : ∀ x, ‖uE x‖ ≤ ℓ)
  {Qa : Set (EuclideanSpace ℝ ι)} {lam0 : EuclideanSpace ℝ ι} (h0 : lam0 ∈ Qa) {A0 : ℝ}
  (hA : ‖lam0‖ ≤ A0) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {d : ℕ → X → ℝ}
  (hd : ∀ j, d j ∈ simplex X)
  (hdense : ∀ p ∈ simplex X, ∀ ε > 0, ∃ j, ∀ x, |d j x - p x| ≤ ε)

include hℓ hu h0 hA hw0 hd in
lemma gridVal_bdd (k : ℕ) (θh : ι → ℝ) :
    BddAbove (Set.range fun j => gridVal uE Qa w0 d k θh j) := by
  refine ⟨ℓ ^ 2 * (‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ + A0) ^ 2 / 2, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact info_le_anchor uE (floorDesign_mem (etaK_pos k).le (etaK_le_one k) hw0 (hd j)) hℓ hu h0
    hA le_rfl

lemma exists_grid_near (Qa : Set (EuclideanSpace ℝ ι)) (w0 : X → ℝ) (d : ℕ → X → ℝ) (k : ℕ)
    (θh : ι → ℝ) :
    ∃ j, (⨆ j, gridVal uE Qa w0 d k θh j) - etaK k ≤ gridVal uE Qa w0 d k θh j := by
  have h : (⨆ j, gridVal uE Qa w0 d k θh j) - etaK k < ⨆ j, gridVal uE Qa w0 d k θh j := by
    linarith [etaK_pos k]
  obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup h
  exact ⟨j, hj.le⟩

include hℓ hu h0 hA hw0 hd hdense in
/-- By density and continuity in the design, the supremum over the sequence dominates every
floored design. -/
lemma le_grid_sup (k : ℕ) (θh : ι → ℝ) {w : X → ℝ} (hw : w ∈ simplex X) :
    gInfo uE Qa (WithLp.toLp 2 θh) (floorDesign (etaK k) w0 w) ≤
      ⨆ j, gridVal uE Qa w0 d k θh j := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ⨆ j, gridVal uE Qa w0 d k θh j := ⟨_, rfl⟩
  have hbdd := gridVal_bdd uE hℓ hu h0 hA hw0 hd k θh
  have hjle : ∀ j, gridVal uE Qa w0 d k θh j ≤ M := fun j => by
    rw [hM]
    exact le_ciSup hbdd j
  have hM0 : 0 ≤ M := gInfo_nonneg.trans (hjle 0)
  have hη0 := (etaK_pos k).le
  have hη1 := etaK_le_one k
  have hfw : floorDesign (etaK k) w0 w ∈ simplex X := floorDesign_mem hη0 hη1 hw0 hw
  rw [← hM]
  have hroot : rootInfo (designMap uE (floorDesign (etaK k) w0 w)) Qa (WithLp.toLp 2 θh) ≤
      Real.sqrt (2 * M) := by
    refine le_of_forall_pos_lt_add fun e he => ?_
    obtain ⟨δ, hδ, hcont⟩ := rootInfo_joint_continuous uE hu ⟨lam0, h0⟩
      (WithLp.toLp 2 θh : EuclideanSpace ℝ ι) hfw he
    obtain ⟨j, hj⟩ := hdense w hw δ hδ
    have hclose : ∀ x, |floorDesign (etaK k) w0 (d j) x - floorDesign (etaK k) w0 w x| ≤ δ := by
      intro x
      have e1 : floorDesign (etaK k) w0 (d j) x - floorDesign (etaK k) w0 w x =
          (1 - etaK k) * (d j x - w x) := by
        simp only [floorDesign]
        ring
      rw [e1, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - etaK k)]
      have h1 : (1 - etaK k) * |d j x - w x| ≤ 1 * |d j x - w x| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      linarith [hj x]
    have h1 := hcont (WithLp.toLp 2 θh) (floorDesign (etaK k) w0 (d j))
      (floorDesign_mem hη0 hη1 hw0 (hd j)) (by simpa using hδ.le) hclose
    have h2 := (abs_lt.mp h1).1
    have h3 : rootInfo (designMap uE (floorDesign (etaK k) w0 (d j))) Qa (WithLp.toLp 2 θh) ≤
        Real.sqrt (2 * M) := by
      have h4 := hjle j
      unfold gridVal gInfo at h4
      have h5 : rootInfo (designMap uE (floorDesign (etaK k) w0 (d j))) Qa
          (WithLp.toLp 2 θh) ^ 2 ≤ 2 * M := by linarith
      have := Real.sqrt_le_sqrt h5
      rwa [Real.sqrt_sq rootInfo_nonneg] at this
    linarith
  unfold gInfo
  have h6 := pow_le_pow_left₀ rootInfo_nonneg hroot 2
  rw [Real.sq_sqrt (by positivity)] at h6
  linarith

end Oracle

section Build

variable {X ι 𝒜 : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype ι] [DecidableEq ι]
  [Fintype 𝒜] [Nonempty 𝒜]

/-- The tracker whose oracle scans a dense sequence `d` of designs. -/
def gridTracker (u : X → ι → ℝ) (v : X → ℝ) (Q : 𝒜 → Set (EuclideanSpace ℝ ι)) (w0 : X → ℝ)
    (γ : ℝ) (d : ℕ → X → ℝ) : Tracker X ι 𝒜 where
  u := u
  v := v
  Q := Q
  w0 := w0
  γ := γ
  ow k θh a := floorDesign (etaK k) w0 (d (Nat.find
    (exists_grid_near (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh)))
  oc k θh a := gridVal (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh
    (Nat.find
      (exists_grid_near (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh))

variable [MeasurableSpace 𝒜]

lemma gridTracker_meas (u : X → ι → ℝ) (v : X → ℝ) (Q : 𝒜 → Set (EuclideanSpace ℝ ι))
    (w0 : X → ℝ) (γ : ℝ) (d : ℕ → X → ℝ) : (gridTracker u v Q w0 γ d).Meas := by
  have hJ : ∀ (k : ℕ) (a : 𝒜), Measurable fun θh : ι → ℝ => Nat.find
      (exists_grid_near (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh) :=
    fun k a => measurable_find _ fun j =>
      measurableSet_le ((Measurable.iSup fun j => measurable_gridVal _ _ _ _ _ j).sub_const _)
        (measurable_gridVal _ _ _ _ _ j)
  constructor
  · intro k a
    have h : Measurable fun p : (ι → ℝ) × ℕ =>
        gridVal (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k p.1 p.2 :=
      measurable_from_prod_countable_left fun j => measurable_gridVal _ _ _ _ _ j
    exact Measurable.comp (g := fun p : (ι → ℝ) × ℕ =>
        gridVal (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k p.1 p.2)
      (f := fun θh : ι → ℝ => (θh, Nat.find (exists_grid_near
        (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh)))
      h (measurable_id.prodMk (hJ k a))
  · intro k a
    exact Measurable.comp (g := fun j : ℕ => floorDesign (etaK k) w0 (d j))
      (f := fun θh : ι → ℝ => Nat.find (exists_grid_near
        (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh))
      Measurable.of_discrete (hJ k a)

lemma gridTracker_valid (u : X → ι → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    (Q : 𝒜 → Set (EuclideanSpace ℝ ι)) {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {γ : ℝ} (hγ : 0 < γ)
    {ℓ κ A0 : ℝ} (hℓ : 0 < ℓ) (hu : ∀ x, u x ⬝ᵥ u x ≤ ℓ ^ 2) (hκ : 0 < κ)
    (hspan : ∀ e : ι → ℝ, κ * (e ⬝ᵥ e) ≤ ∑ x, w0 x * (u x ⬝ᵥ e) ^ 2)
    (hQ : ∀ a, ∃ lam ∈ Q a, ‖lam‖ ≤ A0) {d : ℕ → X → ℝ} (hd : ∀ j, d j ∈ simplex X)
    (hdense : ∀ p ∈ simplex X, ∀ ε > 0, ∃ j, ∀ x, |d j x - p x| ≤ ε) :
    (gridTracker u v Q w0 γ d).Valid ℓ κ A0 := by
  have huE : ∀ x, ‖(WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)‖ ≤ ℓ := by
    intro x
    have h : ‖(WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)‖ ^ 2 ≤ ℓ ^ 2 := by
      rw [Tracker.norm_tE_sq]
      exact hu x
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hℓ.le two_ne_zero).mp h
  refine ⟨hv, hw0, hγ, hℓ, hu, hκ, hspan, hQ, ?_, ?_, ?_⟩
  · intro k θh a
    exact ⟨_, hd _, rfl⟩
  · intro k θh a
    exact ⟨gInfo_nonneg, le_rfl⟩
  · intro k θh a w hw
    obtain ⟨lam0, h0, hA⟩ := hQ a
    have hη0 := (etaK_pos k).le
    have hη1 := etaK_le_one k
    obtain ⟨C, hC⟩ : ∃ C : ℝ,
        C = ℓ ^ 2 * (‖(WithLp.toLp 2 θh : EuclideanSpace ℝ ι)‖ + 1 + A0) ^ 2 / 2 := ⟨_, rfl⟩
    have hCle : rootInfo (designMap (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) w)
        (Q a) (WithLp.toLp 2 θh) ^ 2 / 2 ≤ C := by
      rw [hC]
      exact info_le_anchor _ hw hℓ.le huE h0 hA (by linarith)
    have hfl := floor_rate_loss (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) hw.1 hw0.1
      hη0 hη1 ⟨lam0, h0⟩ (WithLp.toLp 2 θh : EuclideanSpace ℝ ι) hCle
    have hsup := le_grid_sup (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) hℓ.le huE h0 hA
      hw0 hd hdense k θh hw
    have hfind := Nat.find_spec
      (exists_grid_near (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh)
    have e1 : gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a)
        (WithLp.toLp 2 θh) (floorDesign (etaK k) w0 w) =
        rootInfo (designMap (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι))
          (fun x => (1 - etaK k) * w x + etaK k * w0 x)) (Q a) (WithLp.toLp 2 θh) ^ 2 / 2 := rfl
    rw [e1] at hsup
    rw [← hC]
    show gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) (WithLp.toLp 2 θh) w -
      gridVal (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι)) (Q a) w0 d k θh
        (Nat.find (exists_grid_near (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι))
          (Q a) w0 d k θh)) ≤ etaK k * C + etaK k
    unfold gInfo
    linarith

end Build

/-! ### The theorem for the model, with the oracle constructed -/

section Final

variable {X ι 𝒜 Z : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype 𝒜] [Nonempty 𝒜]
  [MeasurableSpace 𝒜] [MeasurableSingletonClass 𝒜] [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **Correlated Gaussian information limit (`thm:bay-main-optimal`), with no hypothesis on
an oracle.**

Model: finitely many queries `x` with whitened features `u_x ∈ ℝ^d` and known variances
`v_x > 0`; under the parameter `λ` the observation of `x` is `N(√(v_x) ⟨u_x, λ⟩, v_x)`.  The
dictionary is spanning: some design `w⁰` has `M(w⁰) ⪰ κ I`, `κ > 0`.  Terminals `z` have
features `φ_z`, root actions `a` have nonempty supports, and every action has a strict
`ε`-invalidating alternative.  `I` is `I_*(θ) = sup_a sup_w I_a(θ, w)`, assumed positive.
A family of procedures is uniformly correct if for every `δ ∈ (0, 1)`, action `a` and
parameter `λ` with `r_λ(a) > ε`, it halts with answer `a` with probability at most `δ`.

Then (1) every uniformly correct family has `liminf_{δ ↓ 0} E_θ τ_δ / log(1/δ) ≥ 1/I`, and
(2) there is a uniformly correct family (the likelihood-certified information tracker), which
moreover halts with any answer that is not `ε`-acceptable with total probability at most
`δ` under every parameter, with finite expected stopping time for every `δ ∈ (0, 1)` and
`limsup_{δ ↓ 0} E_θ τ_δ / log(1/δ) ≤ 1/I`. -/
theorem gaussian_information_limit (u : X → ι → ℝ) {v : X → ℝ} (hv : ∀ x, 0 < v x)
    {w0 : X → ℝ} (hw0 : w0 ∈ simplex X) {κ : ℝ} (hκ : 0 < κ)
    (hspan : ∀ e : ι → ℝ, κ * (e ⬝ᵥ e) ≤ ∑ x, w0 x * (u x ⬝ᵥ e) ^ 2)
    (φ : Z → EuclideanSpace ℝ ι) (supp : 𝒜 → Finset Z) (hne : ∀ a, (supp a).Nonempty) (ε : ℝ)
    (hQne : ∀ a, (strictAlt φ (supp a) (hne a) ε).Nonempty) (θ : ι → ℝ) {I : ℝ}
    (hIlub : IsLUB {r : ℝ | ∃ a, ∃ w ∈ simplex X,
      r = gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι))
        (strictAlt φ (supp a) (hne a) ε) (WithLp.toLp 2 θ) w} I)
    (hI : 0 < I) :
    (∀ (S : ℝ → GSampler X) (D : ℝ → GDecision 𝒜),
        (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
          law (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
            (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ) →
        ∀ c : ℝ, c < 1 / I → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * Real.log (1 / δ)) ≤
          expTau (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v) ∧
    ∃ (S : ℝ → GSampler X) (D : ℝ → GDecision 𝒜),
      (∀ δ, 0 < δ → δ < 1 → ∀ a, ∀ lam ∈ strictAlt φ (supp a) (hne a) ε, ∀ n,
        law (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
          (ansSet (S δ) (D δ) a n) ≤ ENNReal.ofReal δ) ∧
      (∀ δ, 0 < δ → δ < 1 → ∀ (lam : EuclideanSpace ℝ ι) (n : ℕ),
        law (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ lam.ofLp)) v n
          (⋃ a ∈ {a : 𝒜 | lam ∈ strictAlt φ (supp a) (hne a) ε}, ansSet (S δ) (D δ) a n) ≤
            ENNReal.ofReal δ) ∧
      (∀ δ, 0 < δ → δ < 1 → expTau (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v ≠ ⊤) ∧
      ∀ η > 0, ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 →
        expTau (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v ≠ ⊤ ∧
          (expTau (S δ) (fun x => Real.sqrt (v x) * (u x ⬝ᵥ θ)) v).toReal /
            Real.log (1 / δ) ≤ 1 / I + η := by
  obtain ⟨d, hd, hdense⟩ := exists_dense_simplex hw0
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.sqrt (∑ x, u x ⬝ᵥ u x) + 1 := ⟨_, rfl⟩
  have hS0 : 0 ≤ ∑ x, u x ⬝ᵥ u x := sum_nonneg fun x _ => dotProduct_self_nonneg' (u x)
  have hℓ : 0 < ℓ := by
    rw [hℓdef]
    have := Real.sqrt_nonneg (∑ x, u x ⬝ᵥ u x)
    linarith
  have hu : ∀ x, u x ⬝ᵥ u x ≤ ℓ ^ 2 := by
    intro x
    have h1 : u x ⬝ᵥ u x ≤ ∑ x, u x ⬝ᵥ u x :=
      Finset.single_le_sum (f := fun x => u x ⬝ᵥ u x)
        (fun x _ => dotProduct_self_nonneg' (u x)) (mem_univ x)
    have h2 := Real.sq_sqrt hS0
    have h3 := Real.sqrt_nonneg (∑ x, u x ⬝ᵥ u x)
    rw [hℓdef]
    nlinarith
  choose lamA hlamA using hQne
  have hQ : ∀ a, ∃ lam ∈ strictAlt φ (supp a) (hne a) ε, ‖lam‖ ≤ ∑ a, ‖lamA a‖ := fun a =>
    ⟨lamA a, hlamA a, Finset.single_le_sum (f := fun a => ‖lamA a‖)
      (fun a _ => norm_nonneg _) (mem_univ a)⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Tracker X ι 𝒜,
      T = gridTracker u v (fun a => strictAlt φ (supp a) (hne a) ε) w0 1 d := ⟨_, rfl⟩
  have hT : T.Meas := by
    rw [hTdef]
    exact gridTracker_meas _ _ _ _ _ _
  have hV : T.Valid ℓ κ (∑ a, ‖lamA a‖) := by
    rw [hTdef]
    exact gridTracker_valid u hv _ hw0 one_pos hℓ hu hκ hspan hQ hd hdense
  have hTQ : ∀ a, T.Q a = strictAlt φ (supp a) (hne a) ε := fun a => by rw [hTdef]; rfl
  have hTmean : ∀ th : ι → ℝ, T.mean th = fun x => Real.sqrt (v x) * (u x ⬝ᵥ th) := fun th => by
    rw [hTdef]
    rfl
  have hTv : T.v = v := by rw [hTdef]; rfl
  have hIeq : T.Istar θ = I := by
    have h := T.Istar_isLUB θ hV
    have hset : {r : ℝ | ∃ a, ∃ w ∈ simplex X,
        r = gInfo T.uE (T.Q a) (WithLp.toLp 2 θ) w} =
        {r : ℝ | ∃ a, ∃ w ∈ simplex X,
          r = gInfo (fun x => (WithLp.toLp 2 (u x) : EuclideanSpace ℝ ι))
            (strictAlt φ (supp a) (hne a) ε) (WithLp.toLp 2 θ) w} := by
      rw [hTdef]
      rfl
    rw [hset] at h
    exact h.unique hIlub
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    T.bay_main_optimal hT θ hV φ supp hne ε hTQ (by rw [hIeq]; exact hI)
  rw [hIeq] at h2 h3
  simp only [hTmean, hTv] at h1 h2 h3 h4
  refine ⟨fun S D hc c hcI => ?_, T.sampler hT, T.decision hT, ?_, ?_, h4, h3⟩
  · refine h2 S D (fun δ hδ0 hδ1 a lam hlam n => ?_) c hcI
    rw [hTQ a] at hlam
    exact hc δ hδ0 hδ1 a lam hlam n
  · intro δ hδ0 hδ1 a lam hlam n
    rw [← hTQ a] at hlam
    exact h1 δ hδ0 hδ1 a lam hlam n
  · intro δ hδ0 hδ1 lam n
    have hj := T.safe_joint hT hV φ supp hne ε hTQ hδ0 hδ1 lam.ofLp n
    simp only [hTmean, hTv] at hj
    have hset : {a : 𝒜 | (WithLp.toLp 2 lam.ofLp : EuclideanSpace ℝ ι) ∈ T.Q a} =
        {a : 𝒜 | lam ∈ strictAlt φ (supp a) (hne a) ε} := by
      ext a
      show (WithLp.toLp 2 lam.ofLp : EuclideanSpace ℝ ι) ∈ T.Q a ↔ _
      rw [hTQ a]
      rfl
    rw [hset] at hj
    exact hj

end Final

end GaussTrack

end

end JointRootCert
