/-
Theorem `thm:v34-action-local` (Action-local optional evaluation and intersection-union root
coverage), as stated in the manuscript: for ARBITRARY predictable action and allocation
policies on per-query intrinsic Gaussian tapes with unknown variances.

Model.  One probability space carries the intrinsic tapes `Y x n` (`n`-th observation of query
type `x`), jointly independent, `Y x n ~ N(pred x θ, vₓ)` with arbitrary `vₓ > 0`.  A policy
(`Policy`) is a function of the tape realization: at batch `i` it chooses an action `act i`,
batch sizes `size i` (any natural numbers, zero and one included), the parameters `(muh i, vh i)`
of a Gaussian batch density, a certified lower bound `qlo i` on that density and certified upper
bounds `Uhi a z i` on the component-null likelihood suprema.  Batch `i` of type `x` is the tape
segment starting at the number of observations of that type consumed so far.

* `Policy.Predictable`: the choices made for batch `i + 1` only depend on the observations
  consumed by the end of batch `i`, the certified bounds only read those observations and the
  batch itself, and everything is Borel.
* `Policy.Sound`: the two outward enclosures.  `0 ≤ qlo ≤ q` for the Gaussian density
  `q = batchDens size muh vh` with `vh > 0`, and `Uhi a z ≥ p_{u,s}` for every `u ∈ H a z` and
  every positive variance vector `s`.  The upper bound takes values in `[0, ∞]`, so the
  hypothesis holds at every batch, degenerate or not, and is satisfiable
  (`exists_policy`).  The factor is `½ (1 + qlo / Uhi)` with the convention `qlo / ∞ = 0`,
  which is the manuscript's "on a degenerate numerical input set `F = 1/2`".

Results.

* `Policy.wealth_supermartingale`, `Policy.wealth_zero`, `Policy.wealth_nonneg`: under every
  component null and all positive variances, the action-local wealth is a nonnegative
  supermartingale started at one, for the filtration of consumed observations.
* `Policy.coverage`, `Policy.safe`: `(ε, δ)`-safety at level `δ / K` per root action with no
  union over components, as a bound on the event that the test ever passes with an incorrect
  selected action, and for the formal stopping batch and returned action.
* `v34_action_local`: both claims in one statement.
* `exists_policy`: the hypotheses are satisfiable with nonempty batches and an upper bound that
  is finite on nondegenerate batches.
-/
import JointRootCert.UnknownVarianceCorrect

namespace JointRootCert

namespace LiteralD2a

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- An action and allocation policy with certified bounds, as a function of the tape
realization `y : X → ℕ → ℝ`.

* `act i y`: the action selected (and tested) at batch `i`;
* `size i y x`: the number of observations of type `x` in batch `i`;
* `muh i y`, `vh i y`: means and variances of the Gaussian batch density `q_i`;
* `qlo i (y, s)`: the certified lower bound on `q_i` at the batch `s`;
* `Uhi a z i (y, s)`: the certified upper bound on the component-null likelihood supremum of
  `(a, z)` at the batch `s`, in `[0, ∞]`.

In the second argument of `qlo` and `Uhi`, `s x ℓ` is the `ℓ`-th observation of type `x` in
the batch. -/
structure Policy (X A Z : Type*) where
  act : ℕ → (X → ℕ → ℝ) → A
  size : ℕ → (X → ℕ → ℝ) → X → ℕ
  muh : ℕ → (X → ℕ → ℝ) → X → ℝ
  vh : ℕ → (X → ℕ → ℝ) → X → ℝ
  qlo : ℕ → (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ
  Uhi : A → Z → ℕ → (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ≥0∞

namespace Policy

variable {X A Z : Type*} (π : Policy X A Z)

/-- Observations of each type consumed by the end of batch `j`. -/
def cnt : ℕ → (X → ℕ → ℝ) → X → ℕ
  | 0, _ => fun _ => 0
  | j + 1, y => fun x => cnt j y x + π.size (j + 1) y x

lemma cnt_succ (j : ℕ) (y : X → ℕ → ℝ) (x : X) :
    π.cnt (j + 1) y x = π.cnt j y x + π.size (j + 1) y x := rfl

lemma cnt_mono (y : X → ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) (x : X) : π.cnt i y x ≤ π.cnt j y x := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    rw [π.cnt_succ]
    omega

/-- The observations of batch `i`: for each type, the tape read from the count before the
batch.  The batch consists of the first `size i y x` entries of type `x`. -/
def seg (i : ℕ) (y : X → ℕ → ℝ) : X → ℕ → ℝ := tapeShift (π.cnt (i - 1) y) y

/-- The half-cash factor `F_{a,z,i} = ½ (1 + q̲_i(Y_i) / Ū_{a,z,i}(Y_i))`, with `q̲ / ∞ = 0`. -/
def factor (a : A) (z : Z) (i : ℕ) (y : X → ℕ → ℝ) : ℝ :=
  halfCash (π.qlo i (y, π.seg i y)) (π.Uhi a z i (y, π.seg i y)).toReal

/-- The action-local wealth `E^loc_{a,z}(j)` of `eq:v34-action-local`. -/
def wealth [DecidableEq A] (y : X → ℕ → ℝ) (a : A) (z : Z) (j : ℕ) : ℝ :=
  localWealth (fun i => π.factor a z i y) (fun i => π.act i y) a j

/-- The stopping test at batch `j`: every component wealth of the selected action is at least
`K / δ`, `K = |A|`. -/
def test [DecidableEq A] [Fintype A] (J : A → Finset Z) (y : X → ℕ → ℝ) (δ : ℝ) (j : ℕ) : Prop :=
  ∀ z ∈ J (π.act j y), (Fintype.card A : ℝ) / δ ≤ π.wealth y (π.act j y) z j

/-- The procedure stops: the test passes at some completed batch. -/
def Stops [DecidableEq A] [Fintype A] (J : A → Finset Z) (y : X → ℕ → ℝ) (δ : ℝ) : Prop :=
  ∃ j, 1 ≤ j ∧ π.test J y δ j

open Classical in
/-- The first completed batch at which the test passes (`0` if there is none). -/
def stopBatch [DecidableEq A] [Fintype A] (J : A → Finset Z) (y : X → ℕ → ℝ) (δ : ℝ) : ℕ :=
  if h : π.Stops J y δ then Nat.find h else 0

/-- The returned action: the one selected at the stopping batch. -/
def returned [DecidableEq A] [Fintype A] (J : A → Finset Z) (y : X → ℕ → ℝ) (δ : ℝ) : A :=
  π.act (π.stopBatch J y δ) y

/-- Predictability.  The action and the batch sizes of batch `i + 1` only depend on the
observations consumed by the end of batch `i`; the certified bounds of batch `i + 1` only
depend on those observations and on the batch; all of them are Borel. -/
structure Predictable (π : Policy X A Z) : Prop where
  act_congr : ∀ (i : ℕ) (y y' : X → ℕ → ℝ), (∀ x n, n < π.cnt i y x → y x n = y' x n) →
    π.act (i + 1) y = π.act (i + 1) y'
  size_congr : ∀ (i : ℕ) (y y' : X → ℕ → ℝ), (∀ x n, n < π.cnt i y x → y x n = y' x n) →
    π.size (i + 1) y = π.size (i + 1) y'
  qlo_congr : ∀ (i : ℕ) (y y' s s' : X → ℕ → ℝ), (∀ x n, n < π.cnt i y x → y x n = y' x n) →
    (∀ x ℓ, ℓ < π.size (i + 1) y x → s x ℓ = s' x ℓ) →
    π.qlo (i + 1) (y, s) = π.qlo (i + 1) (y', s')
  Uhi_congr : ∀ (a : A) (z : Z) (i : ℕ) (y y' s s' : X → ℕ → ℝ),
    (∀ x n, n < π.cnt i y x → y x n = y' x n) →
    (∀ x ℓ, ℓ < π.size (i + 1) y x → s x ℓ = s' x ℓ) →
    π.Uhi a z (i + 1) (y, s) = π.Uhi a z (i + 1) (y', s')
  act_meas : ∀ (i : ℕ) (a : A), MeasurableSet {y | π.act i y = a}
  size_meas : ∀ (i : ℕ) (r : X → ℕ), MeasurableSet {y | π.size i y = r}
  qlo_meas : ∀ i : ℕ, Measurable (π.qlo i)
  Uhi_meas : ∀ (a : A) (z : Z) (i : ℕ), Measurable (π.Uhi a z i)

/-- The outward enclosures, for root-action data `(J, H, pred)` (`pred x u = hₓᵀ u`).
`q = batchDens size muh vh` is a proper Gaussian batch density (`vh > 0`), `0 ≤ qlo ≤ q`, and,
when `a` is the selected action and `z ∈ J a`, `Uhi a z` dominates the batch density `p_{u,s}`
for every `u ∈ H a z` and every positive variance vector `s`.  No accuracy is required. -/
structure Sound [Fintype X] {U : Type*} (π : Policy X A Z) (J : A → Finset Z)
    (H : A → Z → Set U) (pred : X → U → ℝ) : Prop where
  vh_pos : ∀ (i : ℕ) (y : X → ℕ → ℝ) (x : X), 0 < π.vh i y x
  qlo_nonneg : ∀ (i : ℕ) (p : (X → ℕ → ℝ) × (X → ℕ → ℝ)), 0 ≤ π.qlo i p
  qlo_le : ∀ (i : ℕ) (y s : X → ℕ → ℝ),
    π.qlo i (y, s) ≤ batchDens (π.size i y) (π.muh i y) (π.vh i y) s
  Uhi_ge : ∀ (a : A) (z : Z) (i : ℕ) (y s : X → ℕ → ℝ), π.act i y = a → z ∈ J a →
    ∀ u ∈ H a z, ∀ σ : X → ℝ, (∀ x, 0 < σ x) →
      ENNReal.ofReal (batchDens (π.size i y) (fun x => pred x u) σ s) ≤ π.Uhi a z i (y, s)

/-! ### A policy only reads the observations it has consumed -/

section Congr

variable {π}

lemma cnt_congr (hp : π.Predictable) {y y' : X → ℕ → ℝ} (j : ℕ)
    (h : ∀ x n, n < π.cnt j y x → y x n = y' x n) :
    ∀ k, k ≤ j + 1 → π.cnt k y' = π.cnt k y := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have e := ih (by omega)
    have hs : π.size (k + 1) y = π.size (k + 1) y' :=
      hp.size_congr k y y' fun x n hn => h x n (lt_of_lt_of_le hn (π.cnt_mono y (by omega) x))
    funext x
    show π.cnt k y' x + π.size (k + 1) y' x = π.cnt k y x + π.size (k + 1) y x
    rw [e, hs]

lemma cnt_tapeTrunc (hp : π.Predictable) (i : ℕ) (y : X → ℕ → ℝ) :
    ∀ k, k ≤ i + 1 → π.cnt k (tapeTrunc (π.cnt i y) y) = π.cnt k y :=
  cnt_congr hp i fun _ _ hn => (tapeTrunc_of_lt hn).symm

lemma cnt_tapeTrunc_iff (hp : π.Predictable) (i : ℕ) (y : X → ℕ → ℝ) (c : X → ℕ) :
    π.cnt i (tapeTrunc c y) = c ↔ π.cnt i y = c := by
  constructor
  · intro h
    have := cnt_congr hp (y := tapeTrunc c y) (y' := y) i
      (fun x n hn => by rw [h] at hn; exact tapeTrunc_of_lt hn) i (by omega)
    rw [this]
    exact h
  · intro h
    have := cnt_tapeTrunc hp i y i (by omega)
    rw [h] at this
    exact this

/-- The action and the factor of batch `k + 1` are determined by the observations consumed by
the end of batch `k + 1`. -/
lemma factor_congr (hp : π.Predictable) (a : A) (z : Z) (k : ℕ) {y y' : X → ℕ → ℝ}
    (h : ∀ x n, n < π.cnt (k + 1) y x → y x n = y' x n) :
    π.act (k + 1) y' = π.act (k + 1) y ∧ π.factor a z (k + 1) y' = π.factor a z (k + 1) y := by
  have hpast : ∀ x n, n < π.cnt k y x → y x n = y' x n := fun x n hn =>
    h x n (lt_of_lt_of_le hn (π.cnt_mono y (by omega) x))
  have hc : π.cnt k y' = π.cnt k y := cnt_congr hp k hpast k (by omega)
  have hseg : ∀ x ℓ, ℓ < π.size (k + 1) y x →
      tapeShift (π.cnt k y) y x ℓ = tapeShift (π.cnt k y) y' x ℓ := by
    intro x ℓ hℓ
    refine h x _ ?_
    rw [π.cnt_succ]
    omega
  refine ⟨(hp.act_congr k y y' hpast).symm, ?_⟩
  show halfCash (π.qlo (k + 1) (y', tapeShift (π.cnt k y') y'))
      (π.Uhi a z (k + 1) (y', tapeShift (π.cnt k y') y')).toReal =
    halfCash (π.qlo (k + 1) (y, tapeShift (π.cnt k y) y))
      (π.Uhi a z (k + 1) (y, tapeShift (π.cnt k y) y)).toReal
  rw [hc, hp.qlo_congr k y y' _ _ hpast hseg, hp.Uhi_congr a z k y y' _ _ hpast hseg]

end Congr

/-- The observations consumed by the end of batch `i`. -/
def stopTape (i : ℕ) (y : X → ℕ → ℝ) : X → ℕ → ℝ := tapeTrunc (π.cnt i y) y

section StopTape

variable {π}

lemma stopTape_stopTape_succ (hp : π.Predictable) (i : ℕ) (y : X → ℕ → ℝ) :
    π.stopTape i (π.stopTape (i + 1) y) = π.stopTape i y := by
  have h1 : π.cnt i (π.stopTape (i + 1) y) = π.cnt i y := by
    refine cnt_congr hp (y := y) i (fun x n hn => ?_) i (by omega)
    exact (tapeTrunc_of_lt (lt_of_lt_of_le hn (π.cnt_mono y (by omega) x))).symm
  unfold stopTape at h1 ⊢
  rw [h1]
  exact tapeTrunc_tapeTrunc (fun x => π.cnt_mono y (by omega) x) y

lemma stopTape_stopTape (hp : π.Predictable) (i : ℕ) (y : X → ℕ → ℝ) :
    π.stopTape i (π.stopTape i y) = π.stopTape i y := by
  have h1 : π.cnt i (π.stopTape i y) = π.cnt i y := cnt_tapeTrunc hp i y i (by omega)
  unfold stopTape at h1 ⊢
  rw [h1]
  exact tapeTrunc_tapeTrunc (fun x => le_rfl) y

lemma wealth_stopTape [DecidableEq A] (hp : π.Predictable) (a : A) (z : Z) (j : ℕ)
    (y : X → ℕ → ℝ) : π.wealth (π.stopTape j y) a z j = π.wealth y a z j := by
  unfold wealth localWealth
  refine Finset.prod_congr rfl fun l hl => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  obtain ⟨e1, e2⟩ := factor_congr hp a z k (y := y) (y' := π.stopTape j y) fun x n hn =>
    (tapeTrunc_of_lt (lt_of_lt_of_le hn (π.cnt_mono y h2 x))).symm
  show (if π.act (k + 1) (π.stopTape j y) = a then π.factor a z (k + 1) (π.stopTape j y) else 1) =
    (if π.act (k + 1) y = a then π.factor a z (k + 1) y else 1)
  rw [e1, e2]

end StopTape

/-! ### Measurability of a run -/

section Meas

variable {π} [Finite X]

lemma measurableSet_cnt (hp : π.Predictable) (j : ℕ) (c : X → ℕ) :
    MeasurableSet {y : X → ℕ → ℝ | π.cnt j y = c} := by
  induction j generalizing c with
  | zero =>
    have : {y : X → ℕ → ℝ | π.cnt 0 y = c} = {_y | (fun _ : X => (0 : ℕ)) = c} := rfl
    rw [this]
    exact MeasurableSet.const _
  | succ j ih =>
    refine measurableSet_comp_countable
      (D := fun y : X → ℕ → ℝ => (π.cnt j y, π.size (j + 1) y))
      (measurableSet_pair_fiber ih (hp.size_meas (j + 1)))
      (Q := fun d _ => (fun x => d.1 x + d.2 x) = c) (fun d => MeasurableSet.const _)
      (fun y => Iff.rfl)

lemma measurable_stopTape (hp : π.Predictable) (i : ℕ) : Measurable (π.stopTape i) :=
  measurable_comp_countable (measurableSet_cnt hp i) (Ψ := fun c y => tapeTrunc c y)
    (fun c => measurable_tapeTrunc c) (fun _ => rfl)

lemma measurable_factor (hp : π.Predictable) (a : A) (z : Z) (k : ℕ) :
    Measurable fun y : X → ℕ → ℝ => π.factor a z (k + 1) y := by
  refine measurable_comp_countable (measurableSet_cnt hp k)
    (Ψ := fun c y => halfCash (π.qlo (k + 1) (y, tapeShift c y))
      (π.Uhi a z (k + 1) (y, tapeShift c y)).toReal) (fun c => ?_) (fun y => rfl)
  have hpair : Measurable fun y : X → ℕ → ℝ => (y, tapeShift c y) :=
    measurable_id.prodMk (measurable_tapeShift c)
  exact measurable_halfCash ((hp.qlo_meas (k + 1)).comp hpair)
    (ENNReal.measurable_toReal.comp ((hp.Uhi_meas a z (k + 1)).comp hpair))

lemma measurable_wealth [DecidableEq A] (hp : π.Predictable) (a : A) (z : Z) (j : ℕ) :
    Measurable fun y : X → ℕ → ℝ => π.wealth y a z j := by
  unfold wealth localWealth
  refine Finset.measurable_prod _ fun l hl => ?_
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Finset.mem_Icc.mp hl).1; omega⟩
  exact Measurable.ite (hp.act_meas (k + 1) a) (measurable_factor hp a z k) measurable_const

end Meas

/-! ### The factor as a function of the consumed block and of the next segment -/

/-- The multiplier of batch `k + 1` for the pair `(a, z)` as a function of a tape `t` (the
consumed block) and of the batch `s`. -/
def frozen [DecidableEq A] (a : A) (z : Z) (k : ℕ) (p : (X → ℕ → ℝ) × (X → ℕ → ℝ)) : ℝ :=
  if π.act (k + 1) p.1 = a then halfCash (π.qlo (k + 1) p) (π.Uhi a z (k + 1) p).toReal else 1

section Frozen

variable {π} [DecidableEq A]

lemma measurable_frozen (hp : π.Predictable) (a : A) (z : Z) (k : ℕ) :
    Measurable (π.frozen a z k) :=
  Measurable.ite (measurable_fst (hp.act_meas (k + 1) a))
    (measurable_halfCash (hp.qlo_meas (k + 1))
      (ENNReal.measurable_toReal.comp (hp.Uhi_meas a z (k + 1)))) measurable_const

lemma frozen_eq (hp : π.Predictable) (a : A) (z : Z) (k : ℕ) (y : X → ℕ → ℝ) :
    π.frozen a z k (tapeTrunc (π.cnt k y) y, tapeShift (π.cnt k y) y) =
      if π.act (k + 1) y = a then π.factor a z (k + 1) y else 1 := by
  have hpast : ∀ x n, n < π.cnt k y x → y x n = tapeTrunc (π.cnt k y) y x n :=
    fun _ _ hn => (tapeTrunc_of_lt hn).symm
  have e1 := hp.act_congr k y _ hpast
  have e2 := hp.qlo_congr k y _ (tapeShift (π.cnt k y) y) (tapeShift (π.cnt k y) y) hpast
    (fun _ _ _ => rfl)
  have e3 := hp.Uhi_congr a z k y _ (tapeShift (π.cnt k y) y) (tapeShift (π.cnt k y) y) hpast
    (fun _ _ _ => rfl)
  show (if π.act (k + 1) (tapeTrunc (π.cnt k y) y) = a then
      halfCash (π.qlo (k + 1) (tapeTrunc (π.cnt k y) y, tapeShift (π.cnt k y) y))
        (π.Uhi a z (k + 1) (tapeTrunc (π.cnt k y) y, tapeShift (π.cnt k y) y)).toReal else 1) = _
  rw [← e1, ← e2, ← e3]
  rfl

variable [Fintype X] {U : Type*} {J : A → Finset Z} {H : A → Z → Set U} {pred : X → U → ℝ}

omit [DecidableEq A] in
lemma factor_ge_half (hs : π.Sound J H pred) (a : A) (z : Z) (i : ℕ) (y : X → ℕ → ℝ) :
    1 / 2 ≤ π.factor a z i y :=
  halfCash_ge_half (hs.qlo_nonneg i _) ENNReal.toReal_nonneg

lemma wealth_nonneg (hs : π.Sound J H pred) (y : X → ℕ → ℝ) (a : A) (z : Z) (j : ℕ) :
    0 ≤ π.wealth y a z j :=
  localWealth_nonneg (fun i => by have := factor_ge_half hs a z i y; linarith) j

omit [Fintype X] in
@[simp] lemma wealth_zero (y : X → ℕ → ℝ) (a : A) (z : Z) : π.wealth y a z 0 = 1 :=
  localWealth_zero _ _ _

lemma frozen_nonneg (hs : π.Sound J H pred) (a : A) (z : Z) (k : ℕ)
    (p : (X → ℕ → ℝ) × (X → ℕ → ℝ)) : 0 ≤ π.frozen a z k p := by
  unfold frozen
  split_ifs
  · have := halfCash_ge_half (hs.qlo_nonneg (k + 1) p)
      (ENNReal.toReal_nonneg (a := π.Uhi a z (k + 1) p))
    linarith
  · exact zero_le_one

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Under the component null `θ ∈ H a z`, every section of the multiplier of batch `k + 1`
integrates to at most one against the law of the next segment: `E[q̲ / Ū] ≤ ∫ q = 1`. -/
lemma lintegral_frozen_le_one (hs : π.Sound J H pred) (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (pred x θ) (v x).toNNReal) P)
    {a : A} {z : Z} (hz : z ∈ J a) (hθ : θ ∈ H a z) (k : ℕ) (c : X → ℕ) (t : X → ℕ → ℝ) :
    ∫⁻ s, ENNReal.ofReal (π.frozen a z k (t, s))
      ∂(P.map fun ω => tapeShift c (tapeOf Y ω)) ≤ 1 := by
  have hS : Measurable (fun ω => tapeShift c (tapeOf Y ω)) :=
    (measurable_tapeShift c).comp (measurable_tapeOf hYm)
  have : IsProbabilityMeasure (P.map fun ω => tapeShift c (tapeOf Y ω)) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  have hdef : ∀ s, π.frozen a z k (t, s) =
      if π.act (k + 1) t = a then
        halfCash (π.qlo (k + 1) (t, s)) (π.Uhi a z (k + 1) (t, s)).toReal
      else 1 := fun s => rfl
  by_cases h : π.act (k + 1) t = a
  · set r := π.size (k + 1) t with hr
    set mean : X → ℝ := fun x => pred x θ with hmean
    have hvh : ∀ x, 0 < π.vh (k + 1) t x := fun x => hs.vh_pos _ _ _
    have hm1 : Measurable fun s : X → ℕ → ℝ => ENNReal.ofReal
        (batchDens r (π.muh (k + 1) t) (π.vh (k + 1) t) s / batchDens r mean v s) :=
      ENNReal.measurable_ofReal.comp
        ((measurable_batchDens _ _ _).div (measurable_batchDens _ _ _))
    have hbound : ∀ s, ENNReal.ofReal (π.frozen a z k (t, s)) ≤
        ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) * ENNReal.ofReal
          (batchDens r (π.muh (k + 1) t) (π.vh (k + 1) t) s / batchDens r mean v s) := by
      intro s
      have hp : 0 < batchDens r mean v s := batchDens_pos _ _ hv s
      have hq0 : 0 ≤ batchDens r (π.muh (k + 1) t) (π.vh (k + 1) t) s := batchDens_nonneg _ _ _ _
      have hr0 : 0 ≤ batchDens r (π.muh (k + 1) t) (π.vh (k + 1) t) s / batchDens r mean v s :=
        div_nonneg hq0 hp.le
      have hU := hs.Uhi_ge a z (k + 1) t s h hz θ hθ v hv
      have hle : π.qlo (k + 1) (t, s) / (π.Uhi a z (k + 1) (t, s)).toReal ≤
          batchDens r (π.muh (k + 1) t) (π.vh (k + 1) t) s / batchDens r mean v s := by
        by_cases htop : π.Uhi a z (k + 1) (t, s) = ⊤
        · rw [htop, ENNReal.toReal_top, div_zero]
          exact hr0
        · exact div_le_div₀ hq0 (hs.qlo_le (k + 1) t s) hp
            ((ENNReal.ofReal_le_iff_le_toReal htop).mp hU)
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num)
        (by positivity), hdef s, ite_eq_left h]
      apply ENNReal.ofReal_le_ofReal
      unfold halfCash
      linarith
    have hind2 : iIndepFun (fun (p : X × ℕ) ω => tapeShift c (tapeOf Y ω) p.1 p.2) P :=
      hind.precomp (shift_injective c)
    have hlaw2 : ∀ x ℓ, HasLaw (fun ω => tapeShift c (tapeOf Y ω) x ℓ)
        (gaussianReal (mean x) (v x).toNNReal) P := fun x ℓ => hlaw x (c x + ℓ)
    refine (lintegral_mono hbound).trans (le_of_eq ?_)
    rw [lintegral_add_left measurable_const, lintegral_const_mul _ hm1, lintegral_const,
      lintegral_map hm1 hS,
      lintegral_batch_ratio_eq_one P (Y := fun ω => tapeShift c (tapeOf Y ω)) hv hind2 hlaw2
        r (π.muh (k + 1) t) hvh, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  · have hΦ : ∀ s, π.frozen a z k (t, s) = 1 := fun s => by rw [hdef s, ite_eq_right h]
    simp [hΦ]

end Frozen

/-! ### The supermartingale -/

section Super

variable {π} [Fintype X] [DecidableEq A] {Ω : Type*} [MeasurableSpace Ω]

/-- The filtration generated by the observations the policy has consumed: `ℱ_i` is generated by
the tape stopped at the per-type counts after batch `i`. -/
def obsFiltration (hp : π.Predictable) {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n)) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq i := MeasurableSpace.comap (fun ω => π.stopTape i (tapeOf Y ω)) inferInstance
  mono' := by
    refine monotone_nat_of_le_succ fun i => ?_
    have hfun : (fun ω => π.stopTape i (tapeOf Y ω)) =
        (π.stopTape i) ∘ (fun ω => π.stopTape (i + 1) (tapeOf Y ω)) := by
      funext ω
      exact (stopTape_stopTape_succ hp i (tapeOf Y ω)).symm
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_stopTape hp i).comap_le
  le' i := ((measurable_stopTape hp i).comp (measurable_tapeOf hYm)).comap_le

variable {U : Type*} {J : A → Finset Z} {H : A → Z → Set U} {pred : X → U → ℝ}

/-- **Theorem `thm:v34-action-local`, first claim.**  For an arbitrary predictable policy with
sound certified bounds, on jointly independent intrinsic tapes `Y x n ~ N(pred x θ, vₓ)` with
arbitrary positive variances, under the component null `θ ∈ H a z` (`z ∈ J a`): the
action-local wealth `E^loc_{a,z}` is a supermartingale for the filtration of consumed
observations.  It is nonnegative (`wealth_nonneg`) and starts at one (`wealth_zero`).  The
conditional inequality comes from adaptive-segment freshness
(`lintegral_adaptive_segment_le`). -/
theorem wealth_supermartingale (hp : π.Predictable) (hs : π.Sound J H pred) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (pred x θ) (v x).toNNReal) P)
    {a : A} {z : Z} (hz : z ∈ J a) (hθ : θ ∈ H a z) :
    Supermartingale (fun j ω => π.wealth (tapeOf Y ω) a z j) (π.obsFiltration hp hYm) P := by
  classical
  set W : ℕ → (X → ℕ → ℝ) → ℝ := fun j y => π.wealth y a z j with hW
  have hW0 : ∀ j y, 0 ≤ W j y := fun j y => wealth_nonneg hs y a z j
  have hWm : ∀ j, Measurable (W j) := fun j => measurable_wealth hp a z j
  have hWloc : ∀ j y, W j (π.stopTape j y) = W j y := fun j y => wealth_stopTape hp a z j y
  have htp : Measurable (tapeOf Y) := measurable_tapeOf hYm
  -- the one-step inequality
  have hstep : ∀ (i : ℕ) (g : (X → ℕ → ℝ) → ℝ≥0∞), Measurable g →
      (∀ y, g (π.stopTape i y) = g y) →
      ∫⁻ ω, g (tapeOf Y ω) * ENNReal.ofReal (W (i + 1) (tapeOf Y ω)) ∂P ≤
        ∫⁻ ω, g (tapeOf Y ω) * ENNReal.ofReal (W i (tapeOf Y ω)) ∂P := by
    intro i g hg hgloc
    have h := lintegral_adaptive_segment_le P hYm hind (N := fun y => π.cnt i y)
      (measurableSet_cnt hp i) (fun y c => cnt_tapeTrunc_iff hp i y c)
      (g := fun y => g y * ENNReal.ofReal (W i y))
      (hg.mul (ENNReal.measurable_ofReal.comp (hWm i)))
      (fun y => by
        show g (π.stopTape i y) * ENNReal.ofReal (W i (π.stopTape i y)) = _
        rw [hgloc, hWloc i y])
      (Φ := fun _ p => ENNReal.ofReal (π.frozen a z i p))
      (fun _ => ENNReal.measurable_ofReal.comp (measurable_frozen hp a z i))
      (fun c t => lintegral_frozen_le_one hs P hYm hind θ hv hlaw hz hθ i c t)
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun ω => ?_
    show g (tapeOf Y ω) * ENNReal.ofReal (W (i + 1) (tapeOf Y ω)) =
      g (tapeOf Y ω) * ENNReal.ofReal (W i (tapeOf Y ω)) *
        ENNReal.ofReal (π.frozen a z i (tapeTrunc (π.cnt i (tapeOf Y ω)) (tapeOf Y ω),
            tapeShift (π.cnt i (tapeOf Y ω)) (tapeOf Y ω)))
    rw [frozen_eq hp a z i (tapeOf Y ω), mul_assoc, ← ENNReal.ofReal_mul (hW0 i _)]
    congr 2
    exact localWealth_succ _ _ _ _
  have hWle : ∀ j, ∫⁻ ω, ENNReal.ofReal (W j (tapeOf Y ω)) ∂P ≤ 1 := by
    intro j
    induction j with
    | zero => simp [hW]
    | succ j ih =>
      have := hstep j (fun _ => 1) measurable_const (fun _ => rfl)
      simp only [one_mul] at this
      exact this.trans ih
  have hWint : ∀ j, Integrable (fun ω => W j (tapeOf Y ω)) P := fun j =>
    integrable_of_lintegral_ofReal_le_one ((hWm j).comp htp).aestronglyMeasurable
      (fun ω => hW0 j _) (hWle j)
  have hadp : StronglyAdapted (π.obsFiltration hp hYm) (fun j ω => W j (tapeOf Y ω)) := by
    intro j
    have e : (fun ω => W j (tapeOf Y ω)) = (W j) ∘ (fun ω => π.stopTape j (tapeOf Y ω)) := by
      funext ω
      exact (hWloc j _).symm
    show StronglyMeasurable[MeasurableSpace.comap (fun ω => π.stopTape j (tapeOf Y ω))
      inferInstance] (fun ω => W j (tapeOf Y ω))
    rw [e]
    exact ((hWm j).comp (comap_measurable _)).stronglyMeasurable
  refine supermartingale_of_setIntegral_succ_le hadp hWint (fun i s hs' => ?_)
  have hs'' : MeasurableSet[MeasurableSpace.comap (fun ω => π.stopTape i (tapeOf Y ω))
      inferInstance] s := hs'
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs''
  have hs0 : MeasurableSet ((fun ω => π.stopTape i (tapeOf Y ω)) ⁻¹' B) :=
    ((measurable_stopTape hp i).comp htp) hB
  set g : (X → ℕ → ℝ) → ℝ≥0∞ := fun y => B.indicator 1 (π.stopTape i y) with hg
  have hgm : Measurable g := (measurable_one.indicator hB).comp (measurable_stopTape hp i)
  have hgloc : ∀ y, g (π.stopTape i y) = g y := fun y => by
    simp only [hg, stopTape_stopTape hp]
  have hgin : ∀ y, π.stopTape i y ∈ B → g y = 1 := fun y hy =>
    Set.indicator_of_mem hy (1 : (X → ℕ → ℝ) → ℝ≥0∞)
  have hgout : ∀ y, π.stopTape i y ∉ B → g y = 0 := fun y hy =>
    Set.indicator_of_notMem hy (1 : (X → ℕ → ℝ) → ℝ≥0∞)
  have hg1 : ∀ y, g y ≤ 1 := fun y => by
    by_cases hy : π.stopTape i y ∈ B
    · rw [hgin y hy]
    · rw [hgout y hy]
      exact zero_le_one
  have key := hstep i g hgm hgloc
  have conv : ∀ j, ∫ ω in (fun ω => π.stopTape i (tapeOf Y ω)) ⁻¹' B, W j (tapeOf Y ω) ∂P =
      (∫⁻ ω, g (tapeOf Y ω) * ENNReal.ofReal (W j (tapeOf Y ω)) ∂P).toReal := by
    intro j
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => hW0 j _)
      ((hWm j).comp htp).aestronglyMeasurable]
    congr 1
    rw [← lintegral_indicator hs0]
    refine lintegral_congr fun ω => ?_
    by_cases hω : π.stopTape i (tapeOf Y ω) ∈ B
    · have hω' : ω ∈ (fun ω => π.stopTape i (tapeOf Y ω)) ⁻¹' B := hω
      rw [Set.indicator_of_mem hω', hgin _ hω, one_mul]
    · have hω' : ω ∉ (fun ω => π.stopTape i (tapeOf Y ω)) ⁻¹' B := hω
      rw [Set.indicator_of_notMem hω', hgout _ hω, zero_mul]
  show ∫ ω in (fun ω => π.stopTape i (tapeOf Y ω)) ⁻¹' B, W (i + 1) (tapeOf Y ω) ∂P ≤
    ∫ ω in (fun ω => π.stopTape i (tapeOf Y ω)) ⁻¹' B, W i (tapeOf Y ω) ∂P
  rw [conv, conv]
  refine ENNReal.toReal_mono ?_ key
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => ?_)
    ((hWle i).trans_lt ENNReal.one_lt_top))
  calc g (tapeOf Y ω) * ENNReal.ofReal (W i (tapeOf Y ω))
      ≤ 1 * ENNReal.ofReal (W i (tapeOf Y ω)) := by gcongr; exact hg1 _
    _ = ENNReal.ofReal (W i (tapeOf Y ω)) := one_mul _

variable [Fintype A]

/-- **Theorem `thm:v34-action-local`, second claim: intersection-union coverage.**  Same model
as `wealth_supermartingale`.  An action `a` is incorrect at `θ` when `θ` lies in one of its
closed invalidating components `H a z`, `z ∈ J a`.  The probability that at some batch the
selected action is incorrect and passes the minimum-over-components test
`∀ z ∈ J_{A_j}, E^loc_{A_j,z}(j) ≥ K / δ` is at most `δ`: Ville's inequality at level `δ / K`
for one component of each incorrect action, and a union over actions only. -/
theorem coverage (hp : π.Predictable) (hs : π.Sound J H pred) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (pred x θ) (v x).toNNReal) P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ j, (∃ z ∈ J (π.act j (tapeOf Y ω)), θ ∈ H (π.act j (tapeOf Y ω)) z) ∧
        π.test J (tapeOf Y ω) δ j} ≤ ENNReal.ofReal δ := by
  classical
  set V : A → Set Ω := fun a =>
    if h : ∃ z, z ∈ J a ∧ θ ∈ H a z then
      {ω | ∃ j, (Fintype.card A : ℝ) / δ ≤ π.wealth (tapeOf Y ω) a h.choose j}
    else ∅ with hVdef
  have hV : ∀ a, P (V a) ≤ ENNReal.ofReal (δ / Fintype.card A) := by
    intro a
    by_cases h : ∃ z, z ∈ J a ∧ θ ∈ H a z
    · have hK : (0 : ℝ) < Fintype.card A := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
      have hsm := wealth_supermartingale hp hs P hYm hind θ hv hlaw h.choose_spec.1
        h.choose_spec.2
      have hvl := ville_ineq hsm (fun j ω => wealth_nonneg hs _ _ _ _)
        (c := (Fintype.card A : ℝ) / δ) (by positivity)
      have hVa : V a = {ω | ∃ j, (Fintype.card A : ℝ) / δ ≤
          π.wealth (tapeOf Y ω) a h.choose j} := by
        simp only [hVdef, h, ↓reduceDIte]
      rw [hVa]
      refine hvl.trans (le_of_eq ?_)
      congr 1
      simp only [wealth_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
      rw [one_div_div]
    · have hVa : V a = ∅ := by simp only [hVdef, h, ↓reduceDIte]
      rw [hVa]
      simp
  have hincl : {ω | ∃ j, (∃ z ∈ J (π.act j (tapeOf Y ω)), θ ∈ H (π.act j (tapeOf Y ω)) z) ∧
        π.test J (tapeOf Y ω) δ j} ⊆ ⋃ a, V a := by
    rintro ω ⟨j, hbad, htest⟩
    have h : ∃ z, z ∈ J (π.act j (tapeOf Y ω)) ∧ θ ∈ H (π.act j (tapeOf Y ω)) z := by
      obtain ⟨z, hz, hθ⟩ := hbad
      exact ⟨z, hz, hθ⟩
    refine Set.mem_iUnion.mpr ⟨π.act j (tapeOf Y ω), ?_⟩
    have hVa : V (π.act j (tapeOf Y ω)) = {ω' | ∃ j', (Fintype.card A : ℝ) / δ ≤
        π.wealth (tapeOf Y ω') (π.act j (tapeOf Y ω)) h.choose j'} := by
      simp only [hVdef, h, ↓reduceDIte]
    rw [hVa]
    exact ⟨j, htest _ h.choose_spec.1⟩
  have hsum : ∑ a : A, P (V a) ≤ ENNReal.ofReal δ := by
    rcases isEmpty_or_nonempty A with hA | hA
    · simp
    · have hK : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
      refine (Finset.sum_le_sum fun a _ => hV a).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
  exact (measure_mono hincl).trans ((measure_iUnion_fintype_le _ _).trans hsum)

omit [Fintype X] in
lemma stopBatch_spec {y : X → ℕ → ℝ} {δ : ℝ} (h : π.Stops J y δ) :
    1 ≤ π.stopBatch J y δ ∧ π.test J y δ (π.stopBatch J y δ) ∧
      ∀ i, 1 ≤ i → i < π.stopBatch J y δ → ¬ π.test J y δ i := by
  classical
  have e : π.stopBatch J y δ = Nat.find h := by
    unfold stopBatch
    exact dite_eq_left h
  rw [e]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2,
    fun i hi hlt htest => Nat.find_min h hlt ⟨hi, htest⟩⟩

/-- **`(ε, δ)`-safety with a formal stopping batch.**  Stop at the first completed batch at
which the selected action passes the test (`stopBatch`) and return that action (`returned`).
The probability that the procedure stops and returns an incorrect action is at most `δ`. -/
theorem safe (hp : π.Predictable) (hs : π.Sound J H pred) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (pred x θ) (v x).toNNReal) P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | π.Stops J (tapeOf Y ω) δ ∧ ∃ z ∈ J (π.returned J (tapeOf Y ω) δ),
        θ ∈ H (π.returned J (tapeOf Y ω) δ) z} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (coverage hp hs P hYm hind θ hv hlaw hδ)
  rintro ω ⟨hstop, hbad⟩
  exact ⟨π.stopBatch J (tapeOf Y ω) δ, hbad, (stopBatch_spec hstop).2.1⟩

end Super

end Policy

/-! ### The theorem as one statement, and non-vacuity -/

section Main

variable {X A Z U : Type*} [Fintype X] [Fintype A] [DecidableEq A] {Ω : Type*}
  [MeasurableSpace Ω]

/-- **Theorem `thm:v34-action-local` (Action-local optional evaluation and intersection-union
root coverage).**

Data: root-action structure `(J, H, pred)` with `pred x u = hₓᵀ u`, `H a z` the closed
invalidating component and `J a` the unscreened components of action `a`; an arbitrary policy
`π` that is predictable (`Policy.Predictable`) and whose certified bounds satisfy the two
outward enclosures (`Policy.Sound`); intrinsic tapes `Y x n`, jointly independent with
`Y x n ~ N(pred x θ, vₓ)` for an arbitrary positive variance vector `v`.

Conclusions.

1. For every action `a` and every component `z ∈ J a` whose null contains the truth
   (`θ ∈ H a z`), the action-local wealth `E^loc_{a,z}` is a supermartingale for the filtration
   of consumed observations, it is nonnegative and `E^loc_{a,z}(0) = 1`.
2. For every `δ > 0`, the probability that the procedure which stops at the first completed
   batch where `min_{z ∈ J_{A_j}} E^loc_{A_j,z}(j) ≥ K / δ` (`K = |A|`) stops and returns an
   incorrect action is at most `δ`.

The level is `δ / K` per root action; no union over components is taken.  At batch `j` the
test and the wealth update only involve the bounds `Uhi (A_j) z j`, `z ∈ J (A_j)`. -/
theorem v34_action_local (π : Policy X A Z) (hp : π.Predictable) (J : A → Finset Z)
    (H : A → Z → Set U) (pred : X → U → ℝ) (hs : π.Sound J H pred) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (pred x θ) (v x).toNNReal) P) :
    (∀ a z, z ∈ J a → θ ∈ H a z →
      Supermartingale (fun j ω => π.wealth (tapeOf Y ω) a z j) (π.obsFiltration hp hYm) P ∧
        (∀ j ω, 0 ≤ π.wealth (tapeOf Y ω) a z j) ∧ ∀ ω, π.wealth (tapeOf Y ω) a z 0 = 1) ∧
    ∀ δ : ℝ, 0 < δ →
      P {ω | π.Stops J (tapeOf Y ω) δ ∧ ∃ z ∈ J (π.returned J (tapeOf Y ω) δ),
          θ ∈ H (π.returned J (tapeOf Y ω) δ) z} ≤ ENNReal.ofReal δ :=
  ⟨fun _ _ hz hθ => ⟨Policy.wealth_supermartingale hp hs P hYm hind θ hv hlaw hz hθ,
      fun _ _ => Policy.wealth_nonneg hs _ _ _ _, fun _ => Policy.wealth_zero _ _ _⟩,
    fun _ hδ => Policy.safe hp hs P hYm hind θ hv hlaw hδ⟩

open Classical in
/-- A policy with batches of two observations per query type: constant action, standard normal
predictor with the exact density as lower bound, and the exact null envelope as upper bound on
nondegenerate batches (`∞` on degenerate ones). -/
def demoPolicy (H : A → Z → Set U) (pred : X → U → ℝ) (a0 : A) : Policy X A Z where
  act _ _ := a0
  size _ _ _ := 2
  muh _ _ _ := 0
  vh _ _ _ := 1
  qlo _ p := batchDens (fun _ => 2) (fun _ => 0) (fun _ => 1) p.2
  Uhi a z _ p :=
    if ∀ x, 0 < batchVar (fun _ : X => 2) p.2 x then
      ENNReal.ofReal (guardedEnv (H a z) pred (fun _ => 2) p.2)
    else ⊤

omit [Fintype A] [DecidableEq A] in
/-- **The hypotheses of `v34_action_local` are satisfiable with nonempty batches.**  For every
root-action data there is a predictable policy with sound certified bounds, all of whose
batches contain two observations of every query type, and whose upper bounds are finite on
every nondegenerate batch. -/
theorem exists_policy (J : A → Finset Z) (H : A → Z → Set U) (pred : X → U → ℝ) (a0 : A) :
    ∃ π : Policy X A Z, π.Predictable ∧ π.Sound J H pred ∧ (∀ i y x, π.size i y x = 2) ∧
      ∀ a z i y s, (∀ x, 0 < batchVar (π.size i y) s x) → π.Uhi a z i (y, s) ≠ ⊤ := by
  classical
  have hnd : MeasurableSet {s : X → ℕ → ℝ | ∀ x, 0 < batchVar (fun _ : X => 2) s x} := by
    have : {s : X → ℕ → ℝ | ∀ x, 0 < batchVar (fun _ : X => 2) s x} =
        ⋂ x, {s : X → ℕ → ℝ | 0 < batchVar (fun _ : X => 2) s x} := by
      ext s
      simp
    rw [this]
    exact MeasurableSet.iInter fun x =>
      measurableSet_lt measurable_const (continuous_batchVar _ x).measurable
  have hVc : ∀ {s s' : X → ℕ → ℝ}, (∀ (x : X) (ℓ : ℕ), ℓ < 2 → s x ℓ = s' x ℓ) →
      ((∀ x, 0 < batchVar (fun _ : X => 2) s x) ↔ ∀ x, 0 < batchVar (fun _ : X => 2) s' x) := by
    intro s s' h
    constructor
    · intro h1 x
      rw [← batchVar_congr (r := fun _ : X => 2) h x]
      exact h1 x
    · intro h1 x
      rw [batchVar_congr (r := fun _ : X => 2) h x]
      exact h1 x
  refine ⟨demoPolicy H pred a0, ?_, ?_, fun _ _ _ => rfl, ?_⟩
  · refine
      { act_congr := fun _ _ _ _ => rfl
        size_congr := fun _ _ _ _ => rfl
        qlo_congr := fun _ _ _ s s' _ h => batchDens_congr (r := fun _ : X => 2) h
        Uhi_congr := fun a z _ _ _ s s' _ h => ?_
        act_meas := fun _ a => (MeasurableSet.const (a0 = a) :
          MeasurableSet {_y : X → ℕ → ℝ | a0 = a})
        size_meas := fun _ r => (MeasurableSet.const ((fun _ : X => 2) = r) :
          MeasurableSet {_y : X → ℕ → ℝ | (fun _ : X => 2) = r})
        qlo_meas := fun _ => (measurable_batchDens _ _ _).comp measurable_snd
        Uhi_meas := fun a z _ => ?_ }
    · have h' : ∀ (x : X) (ℓ : ℕ), ℓ < 2 → s x ℓ = s' x ℓ := h
      show (if ∀ x, 0 < batchVar (fun _ : X => 2) s x then
          ENNReal.ofReal (guardedEnv (H a z) pred (fun _ => 2) s) else ⊤) =
        (if ∀ x, 0 < batchVar (fun _ : X => 2) s' x then
          ENNReal.ofReal (guardedEnv (H a z) pred (fun _ => 2) s') else ⊤)
      rw [guardedEnv_congr (H a z) pred (r := fun _ : X => 2) h']
      by_cases hs : ∀ x, 0 < batchVar (fun _ : X => 2) s x
      · rw [ite_eq_left hs, ite_eq_left ((hVc h').mp hs)]
      · rw [ite_eq_right hs, ite_eq_right fun h2 => hs ((hVc h').mpr h2)]
    · exact Measurable.ite (measurable_snd hnd)
        (ENNReal.measurable_ofReal.comp
          ((measurable_guardedEnv (H a z) pred (fun _ => 2)).comp measurable_snd))
        measurable_const
  · refine
      { vh_pos := fun _ _ _ => one_pos
        qlo_nonneg := fun _ _ => batchDens_nonneg _ _ _ _
        qlo_le := fun _ _ _ => le_rfl
        Uhi_ge := fun a z _ _ s _ _ u hu σ hσ => ?_ }
    show _ ≤ (if ∀ x, 0 < batchVar (fun _ : X => 2) s x then
        ENNReal.ofReal (guardedEnv (H a z) pred (fun _ => 2) s) else ⊤)
    by_cases hs : ∀ x, 0 < batchVar (fun _ : X => 2) s x
    · rw [ite_eq_left hs, guardedEnv_of_nondeg hs]
      exact ENNReal.ofReal_le_ofReal (batchDens_le_nullEnv hs hu hσ)
    · rw [ite_eq_right hs]
      exact le_top
  · intro a z _ _ s hs
    have hs' : ∀ x, 0 < batchVar (fun _ : X => 2) s x := hs
    show (if ∀ x, 0 < batchVar (fun _ : X => 2) s x then
        ENNReal.ofReal (guardedEnv (H a z) pred (fun _ => 2) s) else ⊤) ≠ ⊤
    rw [ite_eq_left hs']
    exact ENNReal.ofReal_ne_top

end Main

end

end LiteralD2a

end JointRootCert
