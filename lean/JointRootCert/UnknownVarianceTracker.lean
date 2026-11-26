/-
Unknown-variance Gaussian tracking: a formal model of the sparse four-power tracker and its
sharp rate (manuscript, Theorem `thm:v34-adaptive` "Sparse four-power nuisance-KL tracking with
unknown variances", construction and proof in `app:v34-theory`).

Model.  One probability space carries the intrinsic observation tapes `Y x n` (`n`-th
observation of query type `x`), independent `N(μ_x, v_x)` within each type.  The tracker
(`Tracker`) is a deterministic function of a tape realization `y : X → ℕ → ℝ`:

* the state after batch `j` (`Tracker.state`) holds the per-type counts, the deployed action
  and its design;
* batch `i` of type `x` is the tape segment starting at the current count, of length
  `r_{i,x} = alloc i w x` (`Tracker.rr`, `Tracker.yb`);
* the predictor estimates are those of `eq:v34-predictor-estimates` (`predMean`, `predVar`,
  with the deterministic truncation `truncVar`);
* at a four-power batch `4^k` the design oracle is called at the current estimates and the
  sticky incumbent rule with hysteresis `h_k = (k + 1)^{-1/2}` is applied (`Tracker.refInc`,
  `Tracker.step`);
* the action-local wealth uses the half-cash factor of the certified bounds on the plug-in
  Gaussian predictor density and on the null envelope (`Tracker.wealth`); the test of
  Theorem `thm:v34-action-local` is `Tracker.test`, and `Tracker.running δ j` says that the
  `δ`-procedure has not stopped by the end of batch `j`.  Allocation, estimation and testing
  do not depend on `δ` (counterfactual continuation).

The numerical oracles are explicit functions (fields of `Tracker`) and are only assumed to
satisfy the manuscript's contracts (`Tracker.Contract`): the design contract
`eq:v34-design-contract` with `e_k = 1 / (k + 1)`, the two-nat enclosure contract
`eq:v34-numeric-contract`, the rounding rule `r_{j,x} ≥ b_j`, `r_{j,x} ≥ M_j w_{j,x}`,
`∑ₓ r_{j,x} = R_j`, and a tie-breaking rule that returns a displayed maximizer.

Results:

* `good_tape_stops`: the pathwise inclusion.  On a tape whose prefix statistics, segment
  statistics and refresh-time prefix statistics are good from `H_j` on (`GoodTape`), the
  stopping test has fired by batch `j` once `(C_* - 2 η) N_j ≥ log (K / δ)`.  Chains
  `sticky_stabilization`, `refresh_score_error`, `refresh_design_value`, `truncVar_eq_self`,
  `batch_loglik_identification` and `good_window_stops`.
* `tail_of_good`: `P(not good) ≤ p_j`, from the Gaussian law of the tapes alone.
* `v34_adaptive_rate`: both halves of `eq:v34-sharp-rate` for the model, with hypotheses on the
  model only.

Difference from the manuscript.  The batch term of the tail `p_j` is
`∑_{i ≥ H_j} (N_{i-1} + 1)(R_i + 1) Qₓ(b_i, ρ)` (`explicitTailW (segW m)`) instead of
`∑_{i ≥ H_j} Qₓ(b_i, ρ)`: a batch is a segment of an intrinsic tape at a data-dependent
position and of data-dependent length, and it is controlled by a union over all deterministic
segments instead of by a conditional fresh-batch argument.  The tail is still summable
(`tail_summabilityW_refreshRadius`), so the rate statement is unchanged; the constant `D_s`
is the one of `eq:v34-discovery-constant` with this larger `p_j`.

Not proved here: `(ε, δ)`-correctness of this tracker on intrinsic tapes.  It is
`action_local_coverage_gaussian` (`UnknownVarianceBatch.lean`) when each batch is read from a
fresh tape independent of the past; transferring it to segments of intrinsic tapes at
predictable positions needs a strong-Markov-type identification that is not formalized.
-/
import JointRootCert.UnknownVarianceTail
import JointRootCert.UnknownVarianceBatch

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ### Prefix statistics and the predictor estimates -/

/-- Mean of the first `n` entries of a tape. -/
def prefMean (t : ℕ → ℝ) (n : ℕ) : ℝ := (∑ i ∈ range n, t i) / n

/-- Centered variance (denominator `n`) of the first `n` entries of a tape. -/
def prefVar (t : ℕ → ℝ) (n : ℕ) : ℝ := (∑ i ∈ range n, (t i - prefMean t n) ^ 2) / n

lemma not_tapeBad_iff {μ v r : ℝ} {n : ℕ} {t : ℕ → ℝ} :
    ¬ tapeBad μ v r n t ↔ |prefMean t n - μ| ≤ r ∧ |prefVar t n - v| ≤ r := by
  simp only [tapeBad, prefMean, prefVar, not_or, not_lt]

/-- The historical mean estimate `μ̂` of `eq:v34-predictor-estimates`, from `n` past
observations. -/
def predMean (t : ℕ → ℝ) (n : ℕ) : ℝ := if 1 ≤ n then prefMean t n else 0

/-- The truncated historical variance estimate `v̂` of `eq:v34-predictor-estimates` used
before batch `j`, from `n` past observations. -/
def predVar (j : ℕ) (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then truncVar (j : ℝ) (prefVar t n) else 1

/-- The hysteresis `h_k = (k + 1)^{-1/2}`. -/
def hyst (k : ℕ) : ℝ := 1 / Real.sqrt ((k : ℝ) + 1)

lemma hyst_pos (k : ℕ) : 0 < hyst k := by
  unfold hyst
  have : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma hyst_mul_self (k : ℕ) : hyst k * hyst k = 1 / ((k : ℝ) + 1) := by
  unfold hyst
  have h0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt h0]

lemma exists_hyst_lt {ε : ℝ} (hε : 0 < ε) : ∃ k0 : ℕ, ∀ k, k0 ≤ k → hyst k < ε := by
  refine ⟨⌈(1 / ε) ^ 2⌉₊, fun k hk => ?_⟩
  have h1 : (1 / ε) ^ 2 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have h2 : 1 / ε < Real.sqrt ((k : ℝ) + 1) := by
    rw [Real.lt_sqrt (by positivity)]
    linarith
  have h3 : 0 < Real.sqrt ((k : ℝ) + 1) := lt_trans (by positivity) h2
  unfold hyst
  rw [div_lt_iff₀ h3]
  have := (div_lt_iff₀ hε).mp h2
  linarith

/-- If the prefix statistics are within `r ≤ v_min / 8` of the truth, there are at least two
past observations and the batch index is beyond the truncation onset, the predictor estimates
are the prefix statistics and are within `r` of the truth. -/
lemma pred_close {vmin vmax v μ r : ℝ} {t : ℕ → ℝ} {n j : ℕ} (hvmin : 0 < vmin)
    (hv : vmin ≤ v) (hvmax : v ≤ vmax) (hr : r ≤ vmin / 8) (hn : 2 ≤ n)
    (hj : 2 + 2 * max vmax vmin⁻¹ ≤ (j : ℝ)) (hgood : ¬ tapeBad μ v r n t) :
    |predMean t n - μ| ≤ r ∧ |predVar j t n - v| ≤ r := by
  obtain ⟨h1, h2⟩ := not_tapeBad_iff.mp hgood
  have hn1 : 1 ≤ n := by omega
  unfold predMean predVar
  simp only [hn1, hn, ↓reduceIte]
  rw [truncVar_eq_self hvmin hv hvmax hr h2 hj]
  exact ⟨h1, h2⟩

/-! ### Schedule bookkeeping -/

lemma cumB_succ (j : ℕ) : cumB (j + 1) = cumB j + baseB (j + 1) := by
  unfold cumB
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma cumB_mono : Monotone cumB := fun _ _ hab =>
  Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hab)

lemma cumN_eq_add_sum (m a : ℕ) {j : ℕ} (haj : a ≤ j) :
    cumN m j = cumN m a + ∑ i ∈ Icc (a + 1) j, batchR m i := by
  induction j, haj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [cumN_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

lemma sum_window_batchR (m : ℕ) {H j : ℕ} (hH : 1 ≤ H) (hHj : H ≤ j) :
    ∑ i ∈ (Icc 1 j).filter (fun i => H ≤ i), (batchR m i : ℝ) =
      (cumN m j : ℝ) - cumN m (H - 1) := by
  have hf : (Icc 1 j).filter (fun i => H ≤ i) = Icc (H - 1 + 1) j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have h := cumN_eq_add_sum m (H - 1) (j := j) (by omega)
  rw [hf, h]
  push_cast
  ring

/-! ### The tracker -/

/-- The data of the tracker of Theorem `thm:v34-adaptive`: the root-action structure
(`J a` the unscreened components of action `a`, `H a z` the closed invalidating null,
`pred x u = hₓᵀ u`) and the numerical oracles, as explicit functions.

* `design k m v a`, `score k m v a`: the design `w_a^k` and the displayed score `Ĉ_a^k`
  returned by the certified oracle at refresh `k` for the estimates `(m, v)`;
* `pick`: the tie-breaking rule choosing a displayed maximizer;
* `alloc j w`: the integer batch counts `r_{j,·}` for the nominal design `w`;
* `qlo j r μ̂ v̂ y`: the certified lower bound on the plug-in predictor density of a batch `y`
  with sizes `r`;
* `Uhi a z j r μ̂ v̂ y`: the certified upper bound on the component-null likelihood supremum;
* `init`: the initial incumbent. -/
structure Tracker (X A Z U : Type*) where
  J : A → Finset Z
  hJ : ∀ a, (J a).Nonempty
  H : A → Z → Set U
  pred : X → U → ℝ
  design : ℕ → (X → ℝ) → (X → ℝ) → A → X → ℝ
  score : ℕ → (X → ℝ) → (X → ℝ) → A → ℝ
  pick : (A → ℝ) → A
  alloc : ℕ → (X → ℝ) → X → ℕ
  qlo : ℕ → (X → ℕ) → (X → ℝ) → (X → ℝ) → (X → ℕ → ℝ) → ℝ
  Uhi : A → Z → ℕ → (X → ℕ) → (X → ℝ) → (X → ℝ) → (X → ℕ → ℝ) → ℝ
  init : A

/-- The state of the tracker after a batch: per-type observation counts, the deployed action
and its nominal design. -/
structure TState (X A : Type*) where
  cnt : X → ℕ
  inc : A
  w : X → ℝ

namespace Tracker

variable {X A Z U : Type*}

/-- The contracts the manuscript imposes on the oracles.

* `score_le`, `star_le`: the design contract `eq:v34-design-contract`,
  `Ĉ ≤ C_a(w; μ̂, v̂) ≤ C_a^*(μ̂, v̂) ≤ Ĉ + e_k` with `e_k = 1 / (k + 1)`, for positive
  variance estimates; `design_mem`: the returned design is feasible;
* `pick_max`: the tie-breaking rule returns a displayed maximizer (for instance the one of
  lowest index);
* `alloc_sum`, `alloc_base`, `alloc_dom`: the denominator-free schedule with baseline and
  rounding, `∑ₓ r_{j,x} = R_j`, `r_{j,x} ≥ b_j`, `r_{j,x} ≥ M_j w_x`;
* `qlo_nonneg`, `Uhi_nonneg`, `qlo_pos`, `qlo_le`, `Uhi_ge`, `two_nat`: the numerical contract
  `eq:v34-numeric-contract`; the enclosure of the null envelope and the two-nat bound are
  required only on nondegenerate batches (positive within-batch centered variances). -/
structure Contract [Fintype X] (T : Tracker X A Z U) : Prop where
  H_nonempty : ∀ a, ∀ z ∈ T.J a, (T.H a z).Nonempty
  design_mem : ∀ (k : ℕ) (m v : X → ℝ) (a : A), T.design k m v a ∈ simplex X
  score_le : ∀ (k : ℕ) (m v : X → ℝ) (a : A), (∀ x, 0 < v x) →
    T.score k m v a ≤ actGame (T.J a) (T.hJ a) (T.H a) T.pred (T.design k m v a) m v
  star_le : ∀ (k : ℕ) (m v : X → ℝ) (a : A), (∀ x, 0 < v x) →
    actGameStar (T.J a) (T.hJ a) (T.H a) T.pred m v ≤ T.score k m v a + 1 / ((k : ℝ) + 1)
  pick_max : ∀ (f : A → ℝ) (b : A), f b ≤ f (T.pick f)
  alloc_sum : ∀ (j : ℕ) (w : X → ℝ), w ∈ simplex X →
    ∑ x, T.alloc j w x = batchR (Fintype.card X) j
  alloc_base : ∀ (j : ℕ) (w : X → ℝ) (x : X), w ∈ simplex X → baseB j ≤ T.alloc j w x
  alloc_dom : ∀ (j : ℕ) (w : X → ℝ) (x : X), w ∈ simplex X →
    (clockM j : ℝ) * w x ≤ T.alloc j w x
  qlo_nonneg : ∀ j r mh vh y, 0 ≤ T.qlo j r mh vh y
  Uhi_nonneg : ∀ a z j r mh vh y, 0 ≤ T.Uhi a z j r mh vh y
  qlo_pos : ∀ j r mh vh y, (∀ x, 0 < vh x) → 0 < T.qlo j r mh vh y
  qlo_le : ∀ j r mh vh y, (∀ x, 0 < vh x) → T.qlo j r mh vh y ≤ batchDens r mh vh y
  Uhi_ge : ∀ a z j r mh vh y, z ∈ T.J a → (∀ x, 0 < batchVar r y x) →
    nullEnv (T.H a z) T.pred r y ≤ T.Uhi a z j r mh vh y
  two_nat : ∀ a z j r mh vh y, z ∈ T.J a → (∀ x, 0 < vh x) → (∀ x, 0 < batchVar r y x) →
    Real.log (batchDens r mh vh y / T.qlo j r mh vh y) +
      Real.log (T.Uhi a z j r mh vh y / nullEnv (T.H a z) T.pred r y) ≤ 2

variable (T : Tracker X A Z U) (y : X → ℕ → ℝ)

open Classical in
/-- The sticky incumbent rule at refresh `k`: keep the incumbent if its displayed score is
within `h_k` of every displayed score, otherwise switch to the displayed maximizer chosen by
the tie-breaking rule. -/
def refInc (k : ℕ) (mh vh : X → ℝ) (inc : A) : A :=
  if ∀ b, T.score k mh vh b - T.score k mh vh inc ≤ hyst k then inc
  else T.pick (T.score k mh vh)

lemma refInc_keep {k : ℕ} {mh vh : X → ℝ} {inc : A}
    (h : ∀ b, T.score k mh vh b - T.score k mh vh inc ≤ hyst k) :
    T.refInc k mh vh inc = inc := by
  unfold refInc
  split_ifs
  rfl

lemma refInc_switch (hpick : ∀ (f : A → ℝ) (b : A), f b ≤ f (T.pick f)) {k : ℕ}
    {mh vh : X → ℝ} {inc : A}
    (h : ∃ b, hyst k < T.score k mh vh b - T.score k mh vh inc) (b : A) :
    T.score k mh vh b ≤ T.score k mh vh (T.refInc k mh vh inc) := by
  unfold refInc
  split_ifs with h'
  · obtain ⟨b', hb'⟩ := h
    exact absurd (h' b') (not_le.mpr hb')
  · exact hpick _ b

/-- One batch: at a four-power batch index the design oracle is called at the current
predictor estimates and the incumbent is updated; then the batch is allocated. -/
def step (j : ℕ) (s : TState X A) : TState X A :=
  if 4 ^ Nat.log 4 (j + 1) = j + 1 then
    ⟨fun x => s.cnt x + T.alloc (j + 1)
        (T.design (Nat.log 4 (j + 1)) (fun x => predMean (y x) (s.cnt x))
          (fun x => predVar (j + 1) (y x) (s.cnt x))
          (T.refInc (Nat.log 4 (j + 1)) (fun x => predMean (y x) (s.cnt x))
            (fun x => predVar (j + 1) (y x) (s.cnt x)) s.inc)) x,
      T.refInc (Nat.log 4 (j + 1)) (fun x => predMean (y x) (s.cnt x))
        (fun x => predVar (j + 1) (y x) (s.cnt x)) s.inc,
      T.design (Nat.log 4 (j + 1)) (fun x => predMean (y x) (s.cnt x))
        (fun x => predVar (j + 1) (y x) (s.cnt x))
        (T.refInc (Nat.log 4 (j + 1)) (fun x => predMean (y x) (s.cnt x))
          (fun x => predVar (j + 1) (y x) (s.cnt x)) s.inc)⟩
  else ⟨fun x => s.cnt x + T.alloc (j + 1) s.w x, s.inc, s.w⟩

/-- The state after batch `j` on the tape `y`.  Batch `1 = 4^0` is a refresh, so the initial
design is never deployed. -/
def state : ℕ → TState X A
  | 0 => ⟨fun _ => 0, T.init, fun _ => 0⟩
  | j + 1 => T.step y j (state j)

/-- Observation counts before batch `i`. -/
def cntB (i : ℕ) : X → ℕ := (T.state y (i - 1)).cnt

/-- The action selected (deployed and tested) at batch `i`. -/
def sel (i : ℕ) : A := (T.state y i).inc

/-- The nominal design deployed at batch `i`. -/
def wnom (i : ℕ) : X → ℝ := (T.state y i).w

/-- The integer batch counts `r_{i,·}`. -/
def rr (i : ℕ) : X → ℕ := T.alloc i (T.wnom y i)

/-- The predictor mean estimates `μ̂_{·,i-1}` used at batch `i`. -/
def muh (i : ℕ) : X → ℝ := fun x => predMean (y x) (T.cntB y i x)

/-- The predictor variance estimates `v̂_{·,i-1}` used at batch `i`. -/
def vhh (i : ℕ) : X → ℝ := fun x => predVar i (y x) (T.cntB y i x)

/-- The observations of batch `i`: for each type, the tape segment starting at the current
count. -/
def yb (i : ℕ) : X → ℕ → ℝ := fun x ℓ => y x (T.cntB y i x + ℓ)

/-- The certified lower bound on the predictor density at batch `i`. -/
def qloV (i : ℕ) : ℝ := T.qlo i (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i)

/-- The certified upper bound on the null envelope of `(a, z)` at batch `i`. -/
def UhiV (a : A) (z : Z) (i : ℕ) : ℝ :=
  T.Uhi a z i (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i)

/-- The action-local wealth `E^loc_{a,z}(j)` of the tracker (`eq:v34-action-local`). -/
def wealth [DecidableEq A] (a : A) (z : Z) (j : ℕ) : ℝ :=
  localWealth (fun i => halfCash (T.qloV y i) (T.UhiV y a z i)) (T.sel y) a j

/-- The stopping test of Theorem `thm:v34-action-local` at batch `j` for confidence `δ`:
every component wealth of the selected action is at least `K / δ`, `K = |A|`. -/
def test [DecidableEq A] [Fintype A] (δ : ℝ) (j : ℕ) : Prop :=
  ∀ z ∈ T.J (T.sel y j), (Fintype.card A : ℝ) / δ ≤ T.wealth y (T.sel y j) z j

/-- The `δ`-procedure has not stopped by the end of batch `j` (`τ_δ > N_j`). -/
def running [DecidableEq A] [Fintype A] (δ : ℝ) (j : ℕ) : Prop :=
  ∀ i ∈ Icc 1 j, ¬ T.test y δ i

/-! #### Basic facts about a run -/

lemma step_cnt (j : ℕ) (s : TState X A) (x : X) :
    (T.step y j s).cnt x = s.cnt x + T.alloc (j + 1) (T.step y j s).w x := by
  unfold step
  split_ifs <;> rfl

lemma step_not_refresh {j : ℕ} (s : TState X A) (h : 4 ^ Nat.log 4 (j + 1) ≠ j + 1) :
    (T.step y j s).inc = s.inc ∧ (T.step y j s).w = s.w := by
  unfold step
  simp only [h, ↓reduceIte, and_self]

lemma step_refresh_inc {j k : ℕ} (s : TState X A) (h : 4 ^ k = j + 1) :
    (T.step y j s).inc = T.refInc k (fun x => predMean (y x) (s.cnt x))
      (fun x => predVar (j + 1) (y x) (s.cnt x)) s.inc := by
  have hk : Nat.log 4 (j + 1) = k := by rw [← h, Nat.log_pow (by norm_num)]
  unfold step
  simp only [hk, h, ↓reduceIte]

lemma step_refresh_w {j k : ℕ} (s : TState X A) (h : 4 ^ k = j + 1) :
    (T.step y j s).w = T.design k (fun x => predMean (y x) (s.cnt x))
      (fun x => predVar (j + 1) (y x) (s.cnt x)) (T.step y j s).inc := by
  have hk : Nat.log 4 (j + 1) = k := by rw [← h, Nat.log_pow (by norm_num)]
  unfold step
  simp only [hk, h, ↓reduceIte]

lemma four_pow_pos (k : ℕ) : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)

/-- At refresh `k` the deployed design is the one returned for the deployed action. -/
lemma refresh_w (k : ℕ) :
    T.wnom y (4 ^ k) = T.design k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) (T.sel y (4 ^ k)) := by
  obtain ⟨j, hj⟩ : ∃ j, 4 ^ k = j + 1 := ⟨4 ^ k - 1, by have := four_pow_pos k; omega⟩
  simp only [wnom, sel, hj]
  exact T.step_refresh_w y (T.state y j) hj

lemma refresh_keep (k : ℕ)
    (h : ∀ b, T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) b -
      T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) (T.state y (4 ^ k - 1)).inc ≤ hyst k) :
    T.sel y (4 ^ k) = (T.state y (4 ^ k - 1)).inc := by
  obtain ⟨j, hj⟩ : ∃ j, 4 ^ k = j + 1 := ⟨4 ^ k - 1, by have := four_pow_pos k; omega⟩
  simp only [sel, hj, Nat.add_sub_cancel] at h ⊢
  exact (T.step_refresh_inc y (T.state y j) hj).trans (T.refInc_keep h)

lemma refresh_switch (hpick : ∀ (f : A → ℝ) (b : A), f b ≤ f (T.pick f)) (k : ℕ)
    (h : ∃ b, hyst k < T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) b -
      T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) (T.state y (4 ^ k - 1)).inc) (b : A) :
    T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) b ≤
      T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) (T.sel y (4 ^ k)) := by
  obtain ⟨j, hj⟩ : ∃ j, 4 ^ k = j + 1 := ⟨4 ^ k - 1, by have := four_pow_pos k; omega⟩
  simp only [sel, hj, Nat.add_sub_cancel] at h ⊢
  have e : (T.state y (j + 1)).inc =
      T.refInc k (T.muh y (j + 1)) (T.vhh y (j + 1)) (T.state y j).inc :=
    T.step_refresh_inc y (T.state y j) hj
  rw [e]
  exact T.refInc_switch hpick h b

/-- Between two refreshes the deployed action and design do not change. -/
lemma const_between (k i : ℕ) (h1 : 4 ^ k ≤ i) (h2 : i < 4 ^ (k + 1)) :
    T.sel y i = T.sel y (4 ^ k) ∧ T.wnom y i = T.wnom y (4 ^ k) := by
  induction i, h1 using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ i hi ih =>
    obtain ⟨e1, e2⟩ := ih (by omega)
    have hlog : Nat.log 4 (i + 1) = k :=
      Nat.log_eq_of_pow_le_of_lt_pow (by omega) h2
    have hne : 4 ^ Nat.log 4 (i + 1) ≠ i + 1 := by
      rw [hlog]
      omega
    obtain ⟨s1, s2⟩ := T.step_not_refresh y (T.state y i) hne
    exact ⟨s1.trans e1, s2.trans e2⟩

lemma cnt_succ (j : ℕ) (x : X) :
    (T.state y (j + 1)).cnt x = (T.state y j).cnt x + T.rr y (j + 1) x :=
  T.step_cnt y j (T.state y j) x

section Counts

variable [Fintype X] (hc : T.Contract)
include hc

lemma wnom_mem {i : ℕ} (hi : 1 ≤ i) : T.wnom y i ∈ simplex X := by
  have h1 : 4 ^ Nat.log 4 i ≤ i := Nat.pow_log_le_self 4 (by omega)
  have h2 : i < 4 ^ (Nat.log 4 i + 1) := Nat.lt_pow_succ_log_self (by norm_num) i
  rw [(T.const_between y _ i h1 h2).2, T.refresh_w y]
  exact hc.design_mem _ _ _ _

lemma cumB_le_cnt (j : ℕ) (x : X) : cumB j ≤ (T.state y j).cnt x := by
  induction j with
  | zero => simp [cumB]
  | succ j ih =>
    rw [cumB_succ, T.cnt_succ y]
    exact Nat.add_le_add ih (hc.alloc_base _ _ x (T.wnom_mem y hc (by omega)))

lemma sum_rr {i : ℕ} (hi : 1 ≤ i) : ∑ x, T.rr y i x = batchR (Fintype.card X) i :=
  hc.alloc_sum _ _ (T.wnom_mem y hc hi)

lemma sum_cnt (j : ℕ) : ∑ x, (T.state y j).cnt x = cumN (Fintype.card X) j := by
  induction j with
  | zero => simp [state, cumN]
  | succ j ih =>
    rw [cumN_succ, ← ih, ← T.sum_rr y hc (by omega : 1 ≤ j + 1), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => T.cnt_succ y j x

lemma cnt_le (j : ℕ) (x : X) : (T.state y j).cnt x ≤ cumN (Fintype.card X) j := by
  rw [← T.sum_cnt y hc j]
  exact Finset.single_le_sum (f := fun x => (T.state y j).cnt x) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ x)

lemma rr_le {i : ℕ} (hi : 1 ≤ i) (x : X) : T.rr y i x ≤ batchR (Fintype.card X) i := by
  rw [← T.sum_rr y hc hi]
  exact Finset.single_le_sum (f := fun x => T.rr y i x) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ x)

lemma baseB_le_rr {i : ℕ} (hi : 1 ≤ i) (x : X) : baseB i ≤ T.rr y i x :=
  hc.alloc_base _ _ x (T.wnom_mem y hc hi)

end Counts

end Tracker

/-! ### The good event and the pathwise inclusion -/

/-- The good event behind `eq:v34-tail-stop`, as a property of a tape realization, for
`H = H_j`: for every query type,

* every prefix of length at least `𝔟_{H-1}` has statistics within `ρ` of the truth;
* for every batch index `i ≥ H`, every tape segment starting at most at `N_{i-1}` and of
  length between `b_i` and `R_i` has statistics within `ρ` of the truth;
* for every refresh `4^k ≥ H`, every prefix of length at least `𝔟_{4^k - 1}` has statistics
  within `ρ_k` of the truth. -/
def GoodTape {X : Type*} (μ v : X → ℝ) (ρ : ℝ) (ρk : ℕ → ℝ) (m H : ℕ) (y : X → ℕ → ℝ) : Prop :=
  (∀ x n, cumB (H - 1) ≤ n → ¬ tapeBad (μ x) (v x) ρ n (y x)) ∧
  (∀ x i, H ≤ i → ∀ s r, s ≤ cumN m (i - 1) → baseB i ≤ r → r ≤ batchR m i →
    ¬ tapeBad (μ x) (v x) ρ r (fun ℓ => y x (s + ℓ))) ∧
  (∀ x k, H ≤ 4 ^ k → ∀ n, cumB (4 ^ k - 1) ≤ n → ¬ tapeBad (μ x) (v x) (ρk k) n (y x))

section Pathwise

variable {X A Z U : Type*} [Fintype X] [Nonempty X] [DecidableEq X] [Fintype A] [DecidableEq A]

/-- **Pathwise inclusion behind `eq:v34-tail-stop`.**  Fix a tape realization `y`, the true
means and variances `(μ, v)` with `v_min ≤ vₓ ≤ v_max`, `C = C_* = max_a C_a^*(μ, v) > 0`,
and `0 < η ≤ 8 C`.  Radii: `ρ ≤ min {1, v_min / 8}` with `L₀ ρ ≤ η / 16`, and `ρ_k ≤ v_min / 8`.
`k₀` is the refresh onset of the manuscript (`e_k + L₀ ρ_k < h_k / 8`,
`2 L₀ ρ_k + e_k ≤ η / 8`, `4 h_k < C_* - C_a^*` for every suboptimal `a`), and `L` a threshold
with `L ≥ 2`, `L ≥ 2 + 2 max {v_max, v_min⁻¹}`, `L ≥ 4^{k₀}`.  The batch index `j ≥ 16`
satisfies the deterministic onset inequalities of the manuscript (as produced by
`exists_schedule_onset`) and `(C_* - 2 η) N_j ≥ log (K / δ)`.

If the tape is good from `H_j` on (`GoodTape`), then the stopping test has fired at batch `j`.
The proof is the manuscript's: good refreshes give accurate displayed scores
(`refresh_score_error`, with the truncation inactive by `truncVar_eq_self`), the sticky rule
stabilizes on one optimal action (`sticky_stabilization`) whose retained designs are
near-optimal (`refresh_design_value`), and the batch evidence on the window `[H_j, j]`
(`batch_loglik_identification`, `good_window_stops`) pushes every component wealth of that
action above `K / δ`. -/
theorem good_tape_stops (T : Tracker X A Z U) (hc : T.Contract) (y : X → ℕ → ℝ)
    {μ v : X → ℝ} {vmin vmax ρ C η δ : ℝ} {ρk : ℕ → ℝ}
    (hvmin : 0 < vmin) (hv : ∀ x, vmin ≤ v x) (hvmax : ∀ x, v x ≤ vmax) (hC : 0 < C)
    (hCmax : ∀ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v ≤ C)
    (hCatt : ∃ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v = C)
    (hη : 0 < η) (hηC : η ≤ 8 * C)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρv : ρ ≤ vmin / 8) (hρη : L0 vmin * ρ ≤ η / 16)
    (hρk0 : ∀ k, 0 ≤ ρk k) (hρkv : ∀ k, ρk k ≤ vmin / 8) {k0 : ℕ}
    (hk0a : ∀ k : ℕ, k0 ≤ k → L0 vmin * ρk k + 1 / ((k : ℝ) + 1) < hyst k / 8)
    (hk0b : ∀ k : ℕ, k0 ≤ k → 2 * (L0 vmin * ρk k) + 1 / ((k : ℝ) + 1) ≤ η / 8)
    (hk0c : ∀ k : ℕ, k0 ≤ k → ∀ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v < C →
      4 * hyst k < C - actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v)
    {L : ℕ} (hL2 : 2 ≤ L) (hLv : 2 + 2 * max vmax vmin⁻¹ ≤ (L : ℝ)) (hLk : 4 ^ k0 ≤ L)
    {j : ℕ} (hj : 16 ≤ j) (hH : L ≤ refH j) (hbH : L ≤ cumB (refH j - 1))
    (hNH : (cumN (Fintype.card X) (refH j - 1) : ℝ) ≤ η / (4 * C) * cumN (Fintype.card X) j)
    (hjlog : (j : ℝ) * Real.log 2 ≤ η / 4 * cumN (Fintype.card X) j)
    (hon : ∀ i, refH j ≤ i → L ≤ i ∧
      (Fintype.card X : ℝ) * baseB i ≤ η / (8 * C) * batchR (Fintype.card X) i ∧
      4 * (2 + Real.log 2) / η ≤ batchR (Fintype.card X) i)
    (hδ : 0 < δ)
    (hstop : Real.log ((Fintype.card A : ℝ) / δ) ≤ (C - 2 * η) * cumN (Fintype.card X) j)
    (hgood : GoodTape μ v ρ ρk (Fintype.card X) (refH j) y) :
    T.test y δ j := by
  obtain ⟨hg1, hg2, hg3⟩ := hgood
  set m := Fintype.card X with hm
  set H := refH j with hHdef
  set kH := Nat.log 4 (j / 4) with hkH
  have hHk : H = 4 ^ kH := rfl
  have hH1 : 1 ≤ H := refH_pos j
  have hHj : H ≤ j := by have := (refH_bounds hj).2; omega
  have hv0 : ∀ x, 0 < v x := fun x => hvmin.trans_le (hv x)
  have hA : Nonempty A := ⟨hCatt.choose⟩
  have hK : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  -- refreshes `k ≥ k_H`
  have hkfacts : ∀ k, kH ≤ k → H ≤ 4 ^ k ∧ k0 ≤ k := by
    intro k hk
    have h1 : H ≤ 4 ^ k := by
      rw [hHk]
      exact Nat.pow_le_pow_right (by norm_num) hk
    exact ⟨h1, (Nat.pow_le_pow_iff_right (by norm_num : 1 < 4)).mp ((hLk.trans hH).trans h1)⟩
  have hLreal : ∀ i : ℕ, L ≤ i → 2 + 2 * max vmax vmin⁻¹ ≤ (i : ℝ) := fun i hi =>
    hLv.trans (by exact_mod_cast hi)
  have hcntL : ∀ i, H ≤ i → ∀ x, 2 ≤ T.cntB y i x ∧ cumB (H - 1) ≤ T.cntB y i x := by
    intro i hi x
    have h1 : cumB (H - 1) ≤ cumB (i - 1) := cumB_mono (by omega)
    have h2 : cumB (i - 1) ≤ T.cntB y i x := T.cumB_le_cnt y hc (i - 1) x
    exact ⟨by omega, h1.trans h2⟩
  -- accuracy of the estimates at a refresh
  have hrefresh : ∀ k, kH ≤ k → ∀ x,
      |T.muh y (4 ^ k) x - μ x| ≤ ρk k ∧ |T.vhh y (4 ^ k) x - v x| ≤ ρk k := by
    intro k hk x
    obtain ⟨hHk', -⟩ := hkfacts k hk
    obtain ⟨h2, -⟩ := hcntL (4 ^ k) hHk' x
    have hb : cumB (4 ^ k - 1) ≤ T.cntB y (4 ^ k) x := T.cumB_le_cnt y hc (4 ^ k - 1) x
    exact pred_close hvmin (hv x) (hvmax x) (hρkv k) h2 (hLreal _ (hH.trans hHk'))
      (hg3 x k hHk' _ hb)
  have hvhpos : ∀ k, kH ≤ k → ∀ x, 0 < T.vhh y (4 ^ k) x := by
    intro k hk x
    have h1 := (abs_le.mp (hrefresh k hk x).2).1
    have h2 := hv x
    have h3 := hρkv k
    linarith
  -- displayed scores
  have hacc : ∀ k, kH ≤ k → ∀ a,
      |T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) a -
        actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v| < hyst k / 8 := by
    intro k hk a
    have hvh := hvhpos k hk
    have h1 := (hc.score_le k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) a hvh).trans
      (actGame_le_star (T.J a) (T.hJ a) (T.H a) T.pred (hc.design_mem k _ _ a) hvh)
    have h2 := hc.star_le k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) a hvh
    have h3 := refresh_score_error (T.J a) (T.hJ a) (T.H a) T.pred hvmin hv (hρk0 k) (hρkv k)
      (fun x => (hrefresh k hk x).1) (fun x => (hrefresh k hk x).2) h1 h2
    exact h3.trans_lt (hk0a k (hkfacts k hk).2)
  -- stabilization of the sticky rule
  have hincsucc : ∀ k, (T.state y (4 ^ (k + 1) - 1)).inc = T.sel y (4 ^ k) := by
    intro k
    have e : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
    have h4 := Tracker.four_pow_pos k
    exact (T.const_between y k (4 ^ (k + 1) - 1) (by omega) (by omega)).1
  obtain ⟨hopt, hconst⟩ := sticky_stabilization
    (fun k a => T.score k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) a)
    (fun a => actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v) C hyst
    (fun k => (T.state y (4 ^ k - 1)).inc) kH hCmax hCatt hacc
    (fun k hk a ha => hk0c k (hkfacts k hk).2 a ha)
    (fun k hkeep => by
      show (T.state y (4 ^ (k + 1) - 1)).inc = _
      rw [hincsucc]
      exact T.refresh_keep y k hkeep)
    (fun k hsw b => by
      show _ ≤ T.score k _ _ (T.state y (4 ^ (k + 1) - 1)).inc
      rw [hincsucc]
      exact T.refresh_switch y hc.pick_max k hsw b)
  set ad : A := (T.state y (4 ^ (kH + 1) - 1)).inc with had
  -- the deployed action and design on the window
  have hsel : ∀ i, H ≤ i → T.sel y i = ad ∧ ∃ k, kH ≤ k ∧
      T.wnom y i = T.design k (T.muh y (4 ^ k)) (T.vhh y (4 ^ k)) ad := by
    intro i hi
    have h1 : 4 ^ Nat.log 4 i ≤ i := Nat.pow_log_le_self 4 (by omega)
    have h2 : i < 4 ^ (Nat.log 4 i + 1) := Nat.lt_pow_succ_log_self (by norm_num) i
    have hkk : kH ≤ Nat.log 4 i := by
      have h3 : Nat.log 4 (4 ^ kH) ≤ Nat.log 4 i := Nat.log_mono_right (hHk ▸ hi)
      rwa [Nat.log_pow (by norm_num)] at h3
    obtain ⟨e1, e2⟩ := T.const_between y _ i h1 h2
    have e3 : T.sel y (4 ^ Nat.log 4 i) = ad := by
      rw [← hincsucc]
      exact hconst _ hkk
    refine ⟨e1.trans e3, Nat.log 4 i, hkk, ?_⟩
    rw [e2, T.refresh_w y, e3]
  have hval : ∀ i, H ≤ i →
      C - η / 8 ≤ actGame (T.J ad) (T.hJ ad) (T.H ad) T.pred (T.wnom y i) μ v := by
    intro i hi
    obtain ⟨-, k, hkk, hw⟩ := hsel i hi
    have hvh := hvhpos k hkk
    rw [hw]
    have h1 := refresh_design_value (T.J ad) (T.hJ ad) (T.H ad) T.pred
      (hc.design_mem k _ _ ad) hvmin hv (hρk0 k) (hρkv k)
      (fun x => (hrefresh k hkk x).1) (fun x => (hrefresh k hkk x).2)
      (hc.score_le k _ _ ad hvh) (hc.star_le k _ _ ad hvh)
    have h2 := hk0b k (hkfacts k hkk).2
    have h3 : actGameStar (T.J ad) (T.hJ ad) (T.H ad) T.pred μ v = C := hopt
    linarith
  -- batch-level facts on the window
  have hRsum : ∀ i, 1 ≤ i → (∑ x, (T.rr y i x : ℝ)) = batchR m i := fun i hi => by
    have := T.sum_rr y hc hi
    exact_mod_cast this
  have hRpos : ∀ i, H ≤ i → (0 : ℝ) < batchR m i := fun i hi => by
    have h1 := (hon i hi).2.2
    have h2 : (0 : ℝ) < 4 * (2 + Real.log 2) / η := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      positivity
    linarith
  have hbstat : ∀ i, H ≤ i → ∀ x,
      |batchMean (T.rr y i) (T.yb y i) x - μ x| ≤ ρ ∧
        |batchVar (T.rr y i) (T.yb y i) x - v x| ≤ ρ := by
    intro i hi x
    have hi1 : 1 ≤ i := hH1.trans hi
    exact not_tapeBad_iff.mp (hg2 x i hi (T.cntB y i x) (T.rr y i x)
      (T.cnt_le y hc (i - 1) x) (T.baseB_le_rr y hc hi1 x) (T.rr_le y hc hi1 x))
  have hpstat : ∀ i, H ≤ i → ∀ x,
      |T.muh y i x - μ x| ≤ ρ ∧ |T.vhh y i x - v x| ≤ ρ := by
    intro i hi x
    obtain ⟨h2, h3⟩ := hcntL i hi x
    exact pred_close hvmin (hv x) (hvmax x) hρv h2 (hLreal i (hon i hi).1) (hg1 x _ h3)
  have hvchk : ∀ i, H ≤ i → ∀ x, 0 < batchVar (T.rr y i) (T.yb y i) x := by
    intro i hi x
    have h1 := (abs_le.mp (hbstat i hi x).2).1
    have h2 := hv x
    linarith
  have hvhp : ∀ i, H ≤ i → ∀ x, 0 < T.vhh y i x := by
    intro i hi x
    have h1 := (abs_le.mp (hpstat i hi x).2).1
    have h2 := hv x
    linarith
  have hRdef : ∀ i, (batchR m i : ℝ) = clockM i + (m : ℝ) * baseB i := fun i => by
    simp only [batchR]
    push_cast
    ring
  -- the window argument
  have hwin := good_window_stops (T.J ad) (T.hJ ad) (T.H ad) T.pred (μ := μ) (v := v)
    (vmin := vmin) (ρ := ρ) (C := C) (η := η) (K := (Fintype.card A : ℝ)) (δ := δ)
    (T.sel y) ad j H (fun i => (batchR m i : ℝ)) (fun i => (clockM i : ℝ) / batchR m i)
    (T.wnom y) (fun i x => (T.rr y i x : ℝ) / batchR m i)
    (fun i => batchMean (T.rr y i) (T.yb y i)) (fun i => batchVar (T.rr y i) (T.yb y i))
    (T.muh y) (T.vhh y)
    (fun i => batchDens (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i)) (T.qloV y)
    (fun z i => nullEnv (T.H ad z) T.pred (T.rr y i) (T.yb y i)) (fun z i => T.UhiV y ad z i)
    (Nj := (cumN m j : ℝ)) (NH := (cumN m (H - 1) : ℝ))
    hvmin hv hρ0 hρ1 hρv hρη hC hη hηC hK hδ
    (fun i _ => hc.qlo_nonneg _ _ _ _ _)
    (fun z _ i _ => hc.Uhi_nonneg _ _ _ _ _ _ _)
    (fun i _ hi => (hsel i hi).1)
    (fun i _ hi => by
      have hR := hRpos i hi
      refine ⟨fun x => div_nonneg (Nat.cast_nonneg _) hR.le, ?_⟩
      rw [← Finset.sum_div, hRsum i (hH1.trans hi), div_self hR.ne'])
    (fun i _ hi x => (T.wnom_mem y hc (hH1.trans hi)).1 x)
    (fun i _ hi => by
      have hR := hRpos i hi
      have h1 := (hon i hi).2.1
      rw [le_div_iff₀ hR]
      have h2 := hRdef i
      have e : (1 - η / (8 * C)) * (batchR m i : ℝ) =
          batchR m i - η / (8 * C) * batchR m i := by ring
      rw [e]
      linarith)
    (fun i _ hi x => by
      have hR := hRpos i hi
      have h1 := hc.alloc_dom i _ x (T.wnom_mem y hc (hH1.trans hi))
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right h1 hR.le)
    (fun i _ hi => hval i hi)
    (fun i _ hi x => (hbstat i hi x).1) (fun i _ hi x => (hbstat i hi x).2)
    (fun i _ hi x => (hpstat i hi x).1) (fun i _ hi x => (hpstat i hi x).2)
    (fun z hz i _ hi => by
      have hid := batch_loglik_identification (H := T.H ad z) (pred := T.pred)
        (r := T.rr y i) (y := T.yb y i) (muh := T.muh y i) (vh := T.vhh y i)
        (hc.H_nonempty ad z hz) (hvchk i hi) (hvhp i hi)
      rw [hRsum i (hH1.trans hi)] at hid
      exact hid)
    (fun i _ hi => ⟨hc.qlo_pos _ _ _ _ _ (hvhp i hi), hc.qlo_le _ _ _ _ _ (hvhp i hi)⟩)
    (fun z hz i _ hi => ⟨nullEnv_pos (hc.H_nonempty ad z hz) (hvchk i hi),
      hc.Uhi_ge _ _ _ _ _ _ _ hz (hvchk i hi)⟩)
    (fun z hz i _ hi => hc.two_nat _ _ _ _ _ _ _ hz (hvhp i hi) (hvchk i hi))
    (fun i _ hi => (hon i hi).2.2)
    (sum_window_batchR m hH1 hHj) (Nat.cast_nonneg _) hNH hjlog hstop
  -- the test at batch `j`
  have hselj : T.sel y j = ad := (hsel j hHj).1
  intro z hz
  rw [hselj] at hz ⊢
  exact hwin z hz

end Pathwise

/-! ### The tail bound -/

section TailBound

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [Fintype X]

/-- The probability that a tape segment of deterministic position and length is bad. -/
lemma segment_bad_le (P : Measure Ω) [IsProbabilityMeasure P] {μ v r : ℝ} (hv : 0 < v)
    (hr0 : 0 < r) (hrv : r ≤ v / 8) {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal μ v.toNNReal) P) (s n : ℕ) :
    P {ω | tapeBad μ v r n (fun ℓ => Y (s + ℓ) ω)} ≤ ENNReal.ofReal (Qtail v n r) :=
  gaussian_concentration_fixed hv hr0 hrv n (Y := fun ℓ => Y (s + ℓ))
    (hind.precomp (add_right_injective s)) (fun i => hY (s + i))

/-- **Union bound behind `eq:v34-tail-stop`, from the Gaussian law of the intrinsic tapes
alone.**  `Y x` is the intrinsic tape of query type `x`: independent `N(μₓ, vₓ)`
observations (no independence across types is needed).  If on an event `S` the tape is not
good from `H` on, then `P(S) ≤ p`, the explicit tail `explicitTailW (segW m)`: the prefix and
refresh terms are those of `eq:v34-explicit-tail`; the batch term is a union over all tape
segments a batch `i ≥ H` can occupy, `(N_{i-1} + 1)(R_i + 1)` segments, each bad with
probability at most `Qₓ(b_i, ρ)` since `Q` is nonincreasing beyond `n₀ ≤ b_i`. -/
theorem tail_of_good (P : Measure Ω) [IsProbabilityMeasure P] {μ v : X → ℝ}
    (hv : ∀ x, 0 < v x) {ρ : ℝ} {ρk : ℕ → ℝ} (hρ0 : 0 < ρ) (hρv : ∀ x, ρ ≤ v x / 8)
    (hρk0 : ∀ k, 0 < ρk k) (hρkv : ∀ k x, ρk k ≤ v x / 8) {Y : X → ℕ → Ω → ℝ}
    (hind : ∀ x, iIndepFun (Y x) P)
    (hY : ∀ x i, HasLaw (Y x i) (gaussianReal (μ x) (v x).toNNReal) P) (m H : ℕ)
    (hn0 : ∀ x i, H ≤ i → n0 (v x) ρ ≤ baseB i) (S : Set Ω)
    (hS : ∀ ω ∈ S, ¬ GoodTape μ v ρ ρk m H (fun x n => Y x n ω)) :
    P S ≤ explicitTailW (segW m) v ρ ρk H := by
  classical
  have hincl : S ⊆ ⋃ x, ({ω | ∃ n, cumB (H - 1) ≤ n ∧ tapeBad (μ x) (v x) ρ n (fun i => Y x i ω)} ∪
      {ω | ∃ i, H ≤ i ∧ ω ∈ {ω | ∃ s r, s ≤ cumN m (i - 1) ∧ baseB i ≤ r ∧ r ≤ batchR m i ∧
        tapeBad (μ x) (v x) ρ r (fun ℓ => Y x (s + ℓ) ω)}} ∪
      {ω | ∃ k, H ≤ 4 ^ k ∧ ∃ n, cumB (4 ^ k - 1) ≤ n ∧
        tapeBad (μ x) (v x) (ρk k) n (fun i => Y x i ω)}) := by
    intro ω hω
    have hng := hS ω hω
    by_contra hcon
    apply hng
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or, not_and]
      at hcon
    refine ⟨fun x n hn => (hcon x).1.1 n hn, fun x i hi s r hs hr1 hr2 => ?_,
      fun x k hk n hn => (hcon x).2 k hk n hn⟩
    exact (hcon x).1.2 i hi s r hs hr1 hr2
  refine (measure_mono hincl).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  unfold explicitTailW
  refine Finset.sum_le_sum fun x _ => ?_
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ?_ ?_)) ?_)
  · exact prefix_concentration_tail P (hv x) hρ0 (hρv x) (hind x) (hY x) _
  · refine concentration_prefix P _ (fun i => segW m i * Qtail (v x) (baseB i) ρ) H
      fun i hi => ?_
    -- union over the segments
    set Sg : Finset (ℕ × ℕ) := range (cumN m (i - 1) + 1) ×ˢ range (batchR m i + 1) with hSg
    have hsub : {ω | ∃ s r, s ≤ cumN m (i - 1) ∧ baseB i ≤ r ∧ r ≤ batchR m i ∧
        tapeBad (μ x) (v x) ρ r (fun ℓ => Y x (s + ℓ) ω)} ⊆
        ⋃ p ∈ Sg, (if baseB i ≤ p.2 then
          {ω | tapeBad (μ x) (v x) ρ p.2 (fun ℓ => Y x (p.1 + ℓ) ω)} else ∅) := by
      rintro ω ⟨s, r, hs, hr1, hr2, hbad⟩
      refine Set.mem_iUnion₂.mpr ⟨(s, r), ?_, ?_⟩
      · rw [hSg, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨by omega, by omega⟩
      · simp only [hr1, ↓reduceIte]
        exact hbad
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    have hterm : ∀ p ∈ Sg, P (if baseB i ≤ p.2 then
        {ω | tapeBad (μ x) (v x) ρ p.2 (fun ℓ => Y x (p.1 + ℓ) ω)} else ∅) ≤
        ENNReal.ofReal (Qtail (v x) (baseB i) ρ) := by
      intro p _
      split_ifs with hp
      · exact (segment_bad_le P (hv x) hρ0 (hρv x) (hind x) (hY x) p.1 p.2).trans
          (ENNReal.ofReal_le_ofReal (Qtail_anti (hv x) (hn0 x i hi) hp))
      · simp
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (segW_nonneg m i)]
    congr 1
    rw [hSg, Finset.card_product, Finset.card_range, Finset.card_range]
    unfold segW
    rw [ENNReal.ofReal_natCast]
  · have hsub : {ω | ∃ k, H ≤ 4 ^ k ∧ ∃ n, cumB (4 ^ k - 1) ≤ n ∧
          tapeBad (μ x) (v x) (ρk k) n (fun i => Y x i ω)} ⊆
        ⋃ k, if H ≤ 4 ^ k then
          {ω | ∃ n, cumB (4 ^ k - 1) ≤ n ∧ ω ∈ prefixBad (Y x) (μ x) (v x) (ρk k) n}
          else ∅ := by
      rintro ω ⟨k, hk, hω⟩
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      simp only [hk, ↓reduceIte]
      exact hω
    refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
    refine tsum_le_tsum fun k => ?_
    split_ifs with hk
    · exact prefix_concentration_tail P (hv x) (hρk0 k) (hρkv k x) (hind x) (hY x) _
    · simp

end TailBound

/-! ### Assembly: the sharp rate for the tracker -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Nonempty X]
  [DecidableEq X] [Fintype A] [DecidableEq A]

/-- **Tail of the stopping time, `eq:v34-tail-stop`, for the tracker.**  For every
`η ∈ (0, 8 C_*]` there is a deterministic onset `j₁` such that, with the manuscript's radii
`ρ = min {1, v_min / 8, η / (16 L₀)}` and `ρ_k = refreshRadius v_min k`, and
`p_j = explicitTailW (segW m) v ρ ρ_k H_j`,
`P(τ_δ > N_j) ≤ p_j` whenever `j ≥ j₁` and `(C_* - 2 η) N_j ≥ log (K / δ)`, and
`∑_{j ≥ j₁} R_{j+1} min {1, p_j} < ∞`.  (Outer measure of the event; no measurability of the
oracles is assumed.) -/
theorem tracker_tail (T : Tracker X A Z U) (hc : T.Contract) (P : Measure Ω)
    [IsProbabilityMeasure P] {μ v : X → ℝ} (hv0 : ∀ x, 0 < v x) {Y : X → ℕ → Ω → ℝ}
    (hind : ∀ x, iIndepFun (Y x) P)
    (hY : ∀ x i, HasLaw (Y x i) (gaussianReal (μ x) (v x).toNNReal) P) {C : ℝ} (hC : 0 < C)
    (hCmax : ∀ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v ≤ C)
    (hCatt : ∃ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v = C)
    {η : ℝ} (hη : 0 < η) (hηC : η ≤ 8 * C) :
    ∃ (j1 : ℕ) (p : ℕ → ℝ≥0∞),
      (∑' j, if j1 ≤ j then ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) * min 1 (p j)
        else 0) ≠ ∞ ∧
      ∀ δ : ℝ, 0 < δ → ∀ j, j1 ≤ j →
        Real.log ((Fintype.card A : ℝ) / δ) ≤ (C - 2 * η) * cumN (Fintype.card X) j →
          P {ω | T.running (fun x n => Y x n ω) δ j} ≤ p j := by
  classical
  set m := Fintype.card X with hm
  -- extreme variances
  obtain ⟨xm, -, hxm⟩ := Finset.exists_min_image univ v univ_nonempty
  obtain ⟨xM, -, hxM⟩ := Finset.exists_max_image univ v univ_nonempty
  set vmin := v xm with hvmin_def
  set vmax := v xM with hvmax_def
  have hvmin : 0 < vmin := hv0 xm
  have hv : ∀ x, vmin ≤ v x := fun x => hxm x (Finset.mem_univ x)
  have hvmax : ∀ x, v x ≤ vmax := fun x => hxM x (Finset.mem_univ x)
  have hL0 := L0_pos hvmin
  -- radii
  set ρ := min 1 (min (vmin / 8) (η / (16 * L0 vmin))) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρv : ρ ≤ vmin / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hρη : L0 vmin * ρ ≤ η / 16 := by
    have h1 : ρ ≤ η / (16 * L0 vmin) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 := mul_le_mul_of_nonneg_left h1 hL0.le
    have e : L0 vmin * (η / (16 * L0 vmin)) = η / 16 := by field_simp
    linarith
  set ρk := refreshRadius vmin with hρkdef
  have hρk0 : ∀ k, 0 < ρk k := refreshRadius_pos hvmin
  have hρkv : ∀ k, ρk k ≤ vmin / 8 := refreshRadius_le_vmin vmin
  have hρkh : ∀ k, L0 vmin * ρk k ≤ hyst k / 64 := by
    intro k
    have h1 := refreshRadius_le_hyst vmin k
    have h2 := mul_le_mul_of_nonneg_left h1 hL0.le
    have e : L0 vmin * (1 / Real.sqrt ((k : ℝ) + 1) / (64 * L0 vmin)) = hyst k / 64 := by
      unfold hyst
      field_simp
    linarith
  -- the gap of the suboptimal actions
  set gap : A → ℝ := fun a =>
    if actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v < C then
      (C - actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v) / 4 else 1 with hgap
  have hgap0 : ∀ a, 0 < gap a := fun a => by
    simp only [hgap]
    split_ifs with h
    · linarith
    · exact one_pos
  have hA : Nonempty A := ⟨hCatt.choose⟩
  obtain ⟨ag, -, hag⟩ := Finset.exists_min_image univ gap univ_nonempty
  -- the refresh onset
  obtain ⟨k0, hk0⟩ := exists_hyst_lt
    (lt_min (by norm_num : (0 : ℝ) < 7 / 64) (lt_min (by positivity : 0 < η / 8) (hgap0 ag)))
  have hk0a : ∀ k : ℕ, k0 ≤ k → L0 vmin * ρk k + 1 / ((k : ℝ) + 1) < hyst k / 8 := by
    intro k hk
    have h1 : hyst k < 7 / 64 := (hk0 k hk).trans_le (min_le_left _ _)
    have h2 := hyst_pos k
    have h3 := hρkh k
    rw [← hyst_mul_self]
    nlinarith
  have hk0b : ∀ k : ℕ, k0 ≤ k → 2 * (L0 vmin * ρk k) + 1 / ((k : ℝ) + 1) ≤ η / 8 := by
    intro k hk
    have h1 : hyst k < 7 / 64 := (hk0 k hk).trans_le (min_le_left _ _)
    have h1' : hyst k < η / 8 :=
      (hk0 k hk).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have h2 := hyst_pos k
    have h3 := hρkh k
    rw [← hyst_mul_self]
    nlinarith
  have hk0c : ∀ k : ℕ, k0 ≤ k → ∀ a,
      actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v < C →
      4 * hyst k < C - actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v := by
    intro k hk a ha
    have h1 : hyst k < gap ag :=
      (hk0 k hk).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : gap ag ≤ gap a := hag a (Finset.mem_univ a)
    have h3 : gap a = (C - actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v) / 4 := by
      simp only [hgap, ha, ↓reduceIte]
    linarith
  -- the threshold `L` and the schedule onset
  set L : ℕ := 2 + ⌈2 + 2 * max vmax vmin⁻¹⌉₊ + 4 ^ k0 + ∑ x, n0 (v x) ρ with hL
  have h4k := Tracker.four_pow_pos k0
  have hL2 : 2 ≤ L := by omega
  have hLv : 2 + 2 * max vmax vmin⁻¹ ≤ (L : ℝ) := by
    have h1 : ⌈2 + 2 * max vmax vmin⁻¹⌉₊ ≤ L := by omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hLk : 4 ^ k0 ≤ L := by omega
  have hLn : ∀ x, n0 (v x) ρ ≤ L := fun x => by
    have := Finset.single_le_sum (f := fun x => n0 (v x) ρ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ x)
    omega
  obtain ⟨j1, hj16, hj1⟩ := exists_schedule_onset m hC hη L
  refine ⟨j1, fun j => explicitTailW (segW m) v ρ ρk (refH j),
    tail_summabilityW_refreshRadius m hv0 hρ0 hvmin (by positivity) (segW_le m) j1,
    fun δ hδ j hj hstop => ?_⟩
  obtain ⟨hH, hbH, hNH, hjlog, hon⟩ := hj1 j hj
  refine tail_of_good P hv0 hρ0 (fun x => hρv.trans (by have := hv x; linarith)) hρk0
    (fun k x => (hρkv k).trans (by have := hv x; linarith)) hind hY m (refH j)
    (fun x i hi => (hLn x).trans (hon i hi).2.1) _ (fun ω hω hgood => ?_)
  have htest := good_tape_stops T hc (fun x n => Y x n ω) hvmin hv hvmax hC hCmax hCatt hη hηC
    hρ0.le hρ1 hρv hρη (fun k => (hρk0 k).le) hρkv hk0a hk0b hk0c hL2 hLv hLk
    (hj16.trans hj) hH hbH hNH hjlog
    (fun i hi => ⟨(hon i hi).1, (hon i hi).2.2.1, (hon i hi).2.2.2⟩) hδ hstop hgood
  exact hω j (Finset.mem_Icc.mpr ⟨by have := hj16.trans hj; omega, le_rfl⟩) htest

/-- **Sharp rate of the sparse four-power tracker (Theorem `thm:v34-adaptive`,
`eq:v34-sharp-rate`), for the model of this file.**

Hypotheses, all on the model: the tracker `T` satisfies the oracle contracts
(`Tracker.Contract`); the intrinsic tapes `Y x` are independent `N(μₓ, vₓ)` observations with
`vₓ > 0` (independence within each query type suffices); `C = C_* = max_a C_a^*(μ, v) > 0`
(`hCmax`, `hCatt`; in particular `C_* < ∞`).  No uniqueness of the optimal action or design.

Conclusion.  With `R_j` the batch sizes of the denominator-free schedule for `m = |X|` query
types, `K = |A|`, and `E τ_δ = E ∑_j R_{j+1} 1{τ_δ > N_j}` (survival identity; the event
`{τ_δ > N_j}` is `Tracker.running δ j`):

* for every rational `s ∈ (0, 1]` there is `D_s ≥ 0`, independent of `δ`, with
  `E τ_δ ≤ D_s + (1 + s) / C_* · log (1 / δ)` for all `δ ∈ (0, 1)`;
* `limsup_{δ ↓ 0} E τ_δ / log (1 / δ) ≤ 1 / C_*`, in the form: for every `c > 1 / C_*`,
  eventually `E τ_δ ≤ c log (1 / δ)`.

No measurability of the oracles is assumed; the integral is the lower Lebesgue integral, which
is the expectation whenever the events `{τ_δ > N_j}` are measurable.  The constant is
`D_s = N_{j_s} + ∑_{j ≥ j₁} R_{j+1} min {1, p_j} + (1 + s) / C_* · log K` as in
`eq:v34-discovery-constant`, with the tail `p_j` of `tracker_tail`. -/
theorem v34_adaptive_rate (T : Tracker X A Z U) (hc : T.Contract) (P : Measure Ω)
    [IsProbabilityMeasure P] {μ v : X → ℝ} (hv0 : ∀ x, 0 < v x) {Y : X → ℕ → Ω → ℝ}
    (hind : ∀ x, iIndepFun (Y x) P)
    (hY : ∀ x i, HasLaw (Y x i) (gaussianReal (μ x) (v x).toNNReal) P) {C : ℝ} (hC : 0 < C)
    (hCmax : ∀ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v ≤ C)
    (hCatt : ∃ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred μ v = C) :
    (∀ s : ℚ, 0 < s → s ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, ∑' j, ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) *
          {ω | T.running (fun x n => Y x n ω) δ j}.indicator 1 ω ∂P ≤
        ENNReal.ofReal (D + (1 + (s : ℝ)) / C * Real.log (1 / δ))) ∧
    ∀ c : ℝ, 1 / C < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, ∑' j, ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) *
          {ω | T.running (fun x n => Y x n ω) δ j}.indicator 1 ω ∂P).toReal ≤
        c * Real.log (1 / δ) := by
  classical
  set m := Fintype.card X with hm
  have hA : Nonempty A := ⟨hCatt.choose⟩
  have hK : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  set S0 : ℝ → ℕ → Set Ω := fun δ j => {ω | T.running (fun x n => Y x n ω) δ j} with hS0
  set S : ℝ → ℕ → Set Ω := fun δ j => toMeasurable P (S0 δ j) with hSdef
  have hmain := sharp_rate_schedule P m S (fun δ j => measurableSet_toMeasurable _ _) hC hK
    (fun s hs0 hs1 => by
      have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
      have hη : 0 < C * (s : ℝ) / (16 * (1 + (s : ℝ))) := by positivity
      have hηC : C * (s : ℝ) / (16 * (1 + (s : ℝ))) ≤ 8 * C := by
        rw [div_le_iff₀ (by positivity)]
        have hs1' : (s : ℝ) ≤ 1 := by exact_mod_cast hs1
        nlinarith
      obtain ⟨j1, p, hfin, htl⟩ := tracker_tail T hc P hv0 hind hY hC hCmax hCatt hη hηC
      refine ⟨j1, p, hfin, fun δ hδ0 _ j hj hcr => ?_⟩
      rw [hSdef]
      simp only
      rw [measure_toMeasurable]
      exact htl δ hδ0 j hj hcr)
  have hmono : ∀ δ : ℝ,
      ∫⁻ ω, ∑' j, ENNReal.ofReal (batchR m (j + 1)) * (S0 δ j).indicator 1 ω ∂P ≤
        ∫⁻ ω, ∑' j, ENNReal.ofReal (batchR m (j + 1)) * (S δ j).indicator 1 ω ∂P := by
    intro δ
    refine lintegral_mono fun ω => tsum_le_tsum fun j => ?_
    have hind : (S0 δ j).indicator (1 : Ω → ℝ≥0∞) ω ≤ (S δ j).indicator 1 ω := by
      by_cases h : ω ∈ S0 δ j
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (subset_toMeasurable P _ h)]
      · rw [Set.indicator_of_notMem h]
        exact zero_le
    exact mul_le_mul_of_nonneg_left hind zero_le
  have hfirst : ∀ s : ℚ, 0 < s → s ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, ∑' j, ENNReal.ofReal (batchR m (j + 1)) * (S0 δ j).indicator 1 ω ∂P ≤
        ENNReal.ofReal (D + (1 + (s : ℝ)) / C * Real.log (1 / δ)) := by
    intro s hs0 hs1
    obtain ⟨D, hD0, hD⟩ := hmain.1 s hs0 hs1
    exact ⟨D, hD0, fun δ hδ0 hδ1 => (hmono δ).trans (hD δ hδ0 hδ1)⟩
  refine ⟨hfirst, fun c hcc => ?_⟩
  choose! D hD0 hD using hfirst
  refine limsup_coefficient (Eτ := fun δ =>
    (∫⁻ ω, ∑' j, ENNReal.ofReal (batchR m (j + 1)) * (S0 δ j).indicator 1 ω ∂P).toReal)
    hC D (fun s hs0 hs1 δ hδ0 hδ1 => ?_) hcc
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    linarith
  have hnn : 0 ≤ D s + (1 + (s : ℝ)) / C * Real.log (1 / δ) := by
    have := hD0 s hs0 hs1
    have : 0 ≤ (1 + (s : ℝ)) / C * Real.log (1 / δ) := by positivity
    linarith
  exact ENNReal.toReal_le_of_le_ofReal hnn (hD s hs0 hs1 δ hδ0 hδ1)

end Assembly

end

end JointRootCert
