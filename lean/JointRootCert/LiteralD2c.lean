/-
Theorem `thm:v34-adaptive` (Sparse four-power nuisance-KL tracking with unknown variances) with
the manuscript's discovery constant and the manuscript's tail.

* `Instance`: the fixed instance `(J, H, pred, μ, v)`; `Instance.Cstar`, `Instance.eta`,
  `Instance.rho`, `Instance.rhoK`, `Instance.k0`, `Instance.j1`, `Instance.pTail`,
  `Instance.jS` and `Instance.Ds` are the constants of the proof, defined from the instance and
  the batch schedule only: `Ds` is `eq:v34-discovery-constant` and `pTail` is
  `eq:v34-explicit-tail`.  `Tracker.inst` is the instance of a tracker at given true means and
  variances; it only depends on the root-action data `(J, H, pred)` of the tracker.
* `batch_bad_le`: the conditional fresh-batch bound.  The batch of a tracker at index `i` is a
  segment of an intrinsic tape at a data-dependent position and of data-dependent length; by
  adaptive-segment freshness (`lintegral_adaptive_segment`) its statistics are bad with
  probability at most `Qₓ(b_i, ρ)`.  No union over deterministic segments.
* `good_run_stops`: the pathwise inclusion of `good_tape_stops`, requiring good statistics only
  for the batches the tracker actually reads (`GoodRun`).
* `tail_stop` (`eq:v34-tail-stop`), `tail_summability_instance` (`eq:v34-tail-summability`).
* `Stops`, `stopBatch`, `tau`, `returned`: the stopping batch, the stopping time `τ_δ` in
  observations and the returned action; `tau_eq_tsum` is the survival identity and
  `tau_eq_sum_cnt` identifies `τ_δ` with the number of observations consumed.
* `v34_correct`, `stops_ae`, `v34_finite_confidence`, and `v34_adaptive_literal`: the theorem.

Hypotheses on the tracker: `Tracker.Contract` (the oracle contracts) and `Tracker.Meas` (Borel
allocation oracles), both satisfiable (`exists_tracker_contract_meas`).  The observations are
measurable and jointly independent.
-/
import JointRootCert.UnknownVarianceCorrect

namespace JointRootCert

namespace LiteralD2c

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ### The good event for the batches actually read, and the pathwise inclusion -/

/-- The good event behind `eq:v34-tail-stop` for a tracker `T`, as a property of a tape
realization, for `H = H_j`: for every query type,

* every prefix of length at least `𝔟_{H-1}` has statistics within `ρ` of the truth;
* for every batch index `i ≥ H`, the batch read by the tracker has statistics within `ρ` of the
  truth;
* for every refresh `4^k ≥ H`, every prefix of length at least `𝔟_{4^k - 1}` has statistics
  within `ρ_k` of the truth. -/
def GoodRun {X A Z U : Type*} (T : Tracker X A Z U) (μ v : X → ℝ) (ρ : ℝ) (ρk : ℕ → ℝ) (H : ℕ)
    (y : X → ℕ → ℝ) : Prop :=
  (∀ x n, cumB (H - 1) ≤ n → ¬ tapeBad (μ x) (v x) ρ n (y x)) ∧
  (∀ x i, H ≤ i → ¬ tapeBad (μ x) (v x) ρ (T.rr y i x) (T.yb y i x)) ∧
  (∀ x k, H ≤ 4 ^ k → ∀ n, cumB (4 ^ k - 1) ≤ n → ¬ tapeBad (μ x) (v x) (ρk k) n (y x))

section Pathwise

variable {X A Z U : Type*} [Fintype X] [Nonempty X] [DecidableEq X] [Fintype A] [DecidableEq A]

/-- **Pathwise inclusion behind `eq:v34-tail-stop`.**  Same statement and proof as
`good_tape_stops`, with the good event `GoodRun`: batch statistics are only required for the
batches the tracker reads. -/
theorem good_run_stops (T : Tracker X A Z U) (hc : T.Contract) (y : X → ℕ → ℝ)
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
    (hgood : GoodRun T μ v ρ ρk (refH j) y) :
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
    exact not_tapeBad_iff.mp (hg2 x i hi)
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

/-! ### The conditional fresh-batch bound -/

section Fresh

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Fintype A]

lemma measurableSet_batchBad (T : Tracker X A Z U) (hm : T.Meas) (μ0 v0 ρ : ℝ) (k : ℕ) (x : X) :
    MeasurableSet {y : X → ℕ → ℝ | tapeBad μ0 v0 ρ (T.rr y (k + 1) x) (T.yb y (k + 1) x)} := by
  refine measurableSet_comp_countable
    (D := fun y : X → ℕ → ℝ => ((T.state y k).cnt, T.rr y (k + 1)))
    (measurableSet_pair_fiber (T.measurableSet_cnt hm k) (T.measurableSet_rr hm (k + 1)))
    (Q := fun d y => tapeBad μ0 v0 ρ (d.2 x) (tapeShift d.1 y x))
    (fun d => ?_) (fun y => Iff.rfl)
  exact ((measurable_pi_apply x).comp (measurable_tapeShift d.1))
    (measurableSet_tapeBad μ0 v0 ρ (d.2 x))

/-- **Conditional fresh-batch bound (second term of `eq:v34-explicit-tail`).**  On jointly
independent intrinsic tapes `Y x n ~ N(meanₓ, vₓ)`, the batch of type `x` read by the tracker
at index `i` (a tape segment at a data-dependent position, of data-dependent length at least
`b_i ≥ n₀`) has its mean or centered variance more than `ρ` away from the truth with
probability at most `Qₓ(b_i, ρ)`.  The position and the length are frozen by adaptive-segment
freshness; there is no union over segments. -/
theorem batch_bad_le (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {mean v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (mean x) (v x).toNNReal) P) {ρ : ℝ}
    (hρ0 : 0 < ρ) (x : X) (hρv : ρ ≤ v x / 8) {i : ℕ} (hi : 1 ≤ i)
    (hn0 : n0 (v x) ρ ≤ baseB i) :
    P {ω | tapeBad (mean x) (v x) ρ (T.rr (tapeOf Y ω) i x) (T.yb (tapeOf Y ω) i x)} ≤
      ENNReal.ofReal (Qtail (v x) (baseB i) ρ) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hindx : iIndepFun (Y x) P :=
    hind.precomp (g := fun n : ℕ => ((x, n) : X × ℕ)) fun n n' h => (Prod.mk.inj h).2
  set E : Set ((X → ℕ → ℝ) × (X → ℕ → ℝ)) :=
    {p | tapeBad (mean x) (v x) ρ (T.rr p.1 (k + 1) x) (p.2 x)} with hE
  have hEm : MeasurableSet E := by
    refine measurableSet_comp_countable
      (D := fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) => T.rr p.1 (k + 1))
      (fun r => measurable_fst (T.measurableSet_rr hm (k + 1) r))
      (Q := fun r p => tapeBad (mean x) (v x) ρ (r x) (p.2 x)) (fun r => ?_) (fun p => Iff.rfl)
    have hf : Measurable fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) => p.2 x :=
      (measurable_pi_apply x).comp measurable_snd
    exact hf (measurableSet_tapeBad (mean x) (v x) ρ (r x))
  set G : (X → ℕ) → (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ≥0∞ := fun _ => E.indicator 1 with hG
  have hGm : ∀ c, Measurable (G c) := fun _ => measurable_one.indicator hEm
  have hfresh := lintegral_adaptive_segment P hYm hind (N := fun y => (T.state y k).cnt)
    (T.measurableSet_cnt hm k) (fun y c => T.cnt_tapeTrunc_iff k y c) hGm
  set S : Set Ω := {ω | tapeBad (mean x) (v x) ρ (T.rr (tapeOf Y ω) (k + 1) x)
    (T.yb (tapeOf Y ω) (k + 1) x)} with hS
  have hSm : MeasurableSet S :=
    (measurable_tapeOf hYm) (measurableSet_batchBad T hm (mean x) (v x) ρ k x)
  have hval : ∀ ω, G ((T.state (tapeOf Y ω) k).cnt)
      (tapeTrunc ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω),
        tapeShift ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω)) = S.indicator 1 ω := by
    intro ω
    have hrr : T.rr (tapeTrunc (T.state (tapeOf Y ω) k).cnt (tapeOf Y ω)) (k + 1) =
        T.rr (tapeOf Y ω) (k + 1) := by
      unfold Tracker.rr Tracker.wnom
      rw [T.state_tapeTrunc k (tapeOf Y ω) (k + 1) le_rfl]
    have hiff : ((tapeTrunc ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω),
        tapeShift ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω)) :
          (X → ℕ → ℝ) × (X → ℕ → ℝ)) ∈ E ↔ ω ∈ S := by
      show tapeBad (mean x) (v x) ρ
          (T.rr (tapeTrunc (T.state (tapeOf Y ω) k).cnt (tapeOf Y ω)) (k + 1) x)
          (tapeShift ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω) x) ↔
        tapeBad (mean x) (v x) ρ (T.rr (tapeOf Y ω) (k + 1) x) (T.yb (tapeOf Y ω) (k + 1) x)
      rw [hrr]
      exact Iff.rfl
    show E.indicator 1 _ = S.indicator 1 ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mpr hω)]
      rfl
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (hiff.mp h))]
  have hinner : ∀ ω, ∫⁻ s, G ((T.state (tapeOf Y ω) k).cnt)
      (tapeTrunc ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω), s)
        ∂(P.map fun ω' => tapeShift ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω')) ≤
      ENNReal.ofReal (Qtail (v x) (baseB (k + 1)) ρ) := by
    intro ω
    set c := (T.state (tapeOf Y ω) k).cnt with hcdef
    set t := tapeTrunc c (tapeOf Y ω) with ht
    set r := T.rr t (k + 1) x with hr
    have hSh : Measurable (fun ω' => tapeShift c (tapeOf Y ω')) :=
      (measurable_tapeShift c).comp (measurable_tapeOf hYm)
    have hsec : MeasurableSet {s : X → ℕ → ℝ | tapeBad (mean x) (v x) ρ r (s x)} := by
      have hf : Measurable fun s : X → ℕ → ℝ => s x := measurable_pi_apply x
      exact hf (measurableSet_tapeBad (mean x) (v x) ρ r)
    have hfun : (fun s => G c (t, s)) =
        {s : X → ℕ → ℝ | tapeBad (mean x) (v x) ρ r (s x)}.indicator 1 := by
      funext s
      show E.indicator 1 (t, s) = _
      by_cases hs : tapeBad (mean x) (v x) ρ r (s x)
      · have h1 : ((t, s) : (X → ℕ → ℝ) × (X → ℕ → ℝ)) ∈ E := hs
        have h2 : s ∈ {s : X → ℕ → ℝ | tapeBad (mean x) (v x) ρ r (s x)} := hs
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        rfl
      · have h1 : ((t, s) : (X → ℕ → ℝ) × (X → ℕ → ℝ)) ∉ E := hs
        have h2 : s ∉ {s : X → ℕ → ℝ | tapeBad (mean x) (v x) ρ r (s x)} := hs
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    rw [hfun, lintegral_indicator_one hsec, Measure.map_apply hSh hsec]
    exact (segment_bad_le P (hv x) hρ0 hρv hindx (hlaw x) (c x) r).trans
      (ENNReal.ofReal_le_ofReal (Qtail_anti (hv x) hn0 (T.baseB_le_rr t hc (by omega) x)))
  calc P S = ∫⁻ ω, S.indicator 1 ω ∂P := (lintegral_indicator_one hSm).symm
    _ = ∫⁻ ω, G ((T.state (tapeOf Y ω) k).cnt)
          (tapeTrunc ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω),
            tapeShift ((T.state (tapeOf Y ω) k).cnt) (tapeOf Y ω)) ∂P :=
        lintegral_congr fun ω => (hval ω).symm
    _ = _ := hfresh
    _ ≤ ∫⁻ _ω, ENNReal.ofReal (Qtail (v x) (baseB (k + 1)) ρ) ∂P := lintegral_mono hinner
    _ = ENNReal.ofReal (Qtail (v x) (baseB (k + 1)) ρ) := by simp

/-- **Union bound behind `eq:v34-tail-stop` with the manuscript's tail.**  If on an event `S`
the run of the tracker is not good from `H` on, then `P(S) ≤ p`, the explicit tail
`eq:v34-explicit-tail`: a union over intrinsic tape prefixes (first and third terms) and over
conditionally fresh batches (second term, `batch_bad_le`). -/
theorem tail_of_goodRun (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {μ v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (μ x) (v x).toNNReal) P)
    {ρ : ℝ} {ρk : ℕ → ℝ} (hρ0 : 0 < ρ) (hρv : ∀ x, ρ ≤ v x / 8)
    (hρk0 : ∀ k, 0 < ρk k) (hρkv : ∀ k x, ρk k ≤ v x / 8) {H : ℕ} (hH : 1 ≤ H)
    (hn0 : ∀ x i, H ≤ i → n0 (v x) ρ ≤ baseB i) (S : Set Ω)
    (hS : ∀ ω ∈ S, ¬ GoodRun T μ v ρ ρk H (tapeOf Y ω)) :
    P S ≤ explicitTail v ρ ρk cumB baseB H := by
  classical
  have hindx : ∀ x, iIndepFun (Y x) P := fun x =>
    hind.precomp (g := fun n : ℕ => ((x, n) : X × ℕ)) fun n n' h => (Prod.mk.inj h).2
  have hincl : S ⊆ ⋃ x,
      ({ω | ∃ n, cumB (H - 1) ≤ n ∧ ω ∈ prefixBad (Y x) (μ x) (v x) ρ n} ∪
      {ω | ∃ i, H ≤ i ∧ ω ∈ {ω | tapeBad (μ x) (v x) ρ (T.rr (tapeOf Y ω) i x)
        (T.yb (tapeOf Y ω) i x)}} ∪
      {ω | ∃ k, H ≤ 4 ^ k ∧ ∃ n, cumB (4 ^ k - 1) ≤ n ∧
        ω ∈ prefixBad (Y x) (μ x) (v x) (ρk k) n}) := by
    intro ω hω
    have hng := hS ω hω
    by_contra hcon
    apply hng
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or, not_and]
      at hcon
    exact ⟨fun x n hn => (hcon x).1.1 n hn, fun x i hi => (hcon x).1.2 i hi,
      fun x k hk n hn => (hcon x).2 k hk n hn⟩
  refine (measure_mono hincl).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  unfold explicitTail
  refine Finset.sum_le_sum fun x _ => ?_
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ?_ ?_)) ?_)
  · exact prefix_concentration_tail P (hv x) hρ0 (hρv x) (hindx x) (hlaw x) _
  · exact concentration_prefix P _ (fun i => Qtail (v x) (baseB i) ρ) H fun i hi =>
      batch_bad_le T hc hm P hYm hind hv hlaw hρ0 x (hρv x) (hH.trans hi) (hn0 x i hi)
  · have hsub : {ω | ∃ k, H ≤ 4 ^ k ∧ ∃ n, cumB (4 ^ k - 1) ≤ n ∧
          ω ∈ prefixBad (Y x) (μ x) (v x) (ρk k) n} ⊆
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
    · exact prefix_concentration_tail P (hv x) (hρk0 k) (hρkv k x) (hindx x) (hlaw x) _
    · simp

end Fresh

/-! ### The instance and its constants -/

/-- The fixed instance of Theorem `thm:v34-adaptive`: root-action data (`J a` the unscreened
components of action `a`, `H a z` the closed invalidating component, `pred x u = hₓᵀ u`), the
true query means `mean x = hₓᵀ θ_*` and the true query variances `var x = σₓ²`. -/
structure Instance (X A Z U : Type*) where
  J : A → Finset Z
  hJ : ∀ a, (J a).Nonempty
  H : A → Z → Set U
  pred : X → U → ℝ
  mean : X → ℝ
  var : X → ℝ

/-- The instance of a tracker at true means `μ` and variances `v`.  It only involves the
root-action data of the tracker, not its oracles. -/
def _root_.JointRootCert.Tracker.inst {X A Z U : Type*} (T : Tracker X A Z U) (μ v : X → ℝ) :
    Instance X A Z U := ⟨T.J, T.hJ, T.H, T.pred, μ, v⟩

lemma two_mul_le_cumB (n : ℕ) : 2 * n ≤ cumB n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cumB_succ]
    have := two_le_baseB (n + 1)
    omega

namespace Instance

variable {X A Z U : Type*} [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
  (I : Instance X A Z U)

/-- The information rate `C_a^*` of action `a`. -/
def rate (a : A) : ℝ := actGameStar (I.J a) (I.hJ a) (I.H a) I.pred I.mean I.var

/-- `C_* = max_a C_a^*`. -/
def Cstar : ℝ := univ.sup' univ_nonempty I.rate

/-- `v_min = min_x vₓ`. -/
def vmin : ℝ := univ.inf' univ_nonempty I.var

/-- `max_x vₓ`. -/
def vmax : ℝ := univ.sup' univ_nonempty I.var

/-- `η = C_* s / (16 (1 + s))`. -/
def eta (s : ℝ) : ℝ := I.Cstar * s / (16 * (1 + s))

/-- The batch radius `ρ = min {1, v_min / 8, η / (16 L₀)}` (`eq:v34-batch-radius`). -/
def rho (η : ℝ) : ℝ := min 1 (min (I.vmin / 8) (η / (16 * L0 I.vmin)))

/-- The refresh radius `ρ_k = min {1, v_min / 8, h_k / (64 L₀)}` (`eq:v34-refresh-radius`). -/
def rhoK (k : ℕ) : ℝ := refreshRadius I.vmin k

/-- The conditions defining the refresh onset `k₀`: `e_k + L₀ ρ_k < h_k / 8`,
`2 L₀ ρ_k + e_k ≤ η / 8`, `h_k < Δ / 4` (as `4 h_k < C_* - C_a^*` for every suboptimal `a`),
and `4^k ≥ 2 + 2 max {max_x vₓ, v_min⁻¹}`. -/
def RefreshOK (η : ℝ) (k : ℕ) : Prop :=
  L0 I.vmin * I.rhoK k + 1 / ((k : ℝ) + 1) < hyst k / 8 ∧
  2 * (L0 I.vmin * I.rhoK k) + 1 / ((k : ℝ) + 1) ≤ η / 8 ∧
  (∀ a, I.rate a < I.Cstar → 4 * hyst k < I.Cstar - I.rate a) ∧
  2 + 2 * max I.vmax I.vmin⁻¹ ≤ (4 : ℝ) ^ k

open Classical in
/-- The least `k₀` such that `RefreshOK` holds for all `k ≥ k₀`. -/
def k0 (η : ℝ) : ℕ := if h : ∃ k0 : ℕ, ∀ k, k0 ≤ k → I.RefreshOK η k then Nat.find h else 0

/-- `max_x n₀(x, ρ)`. -/
def nmax (η : ℝ) : ℕ := univ.sup fun x => n0 (I.var x) (I.rho η)

/-- The deterministic inequalities defining the onset `j₁`, at the index `j`:
`H_j ≥ 4^{k₀}`, `𝔟_{H_j - 1} ≥ max_x n₀(x, ρ)`, `N_{H_j - 1} / N_j ≤ η / (4 C_*)`,
`j log 2 / N_j ≤ η / 4`, and for every `i ≥ H_j`: `b_i ≥ max_x n₀(x, ρ)`,
`i ≥ 2 + 2 max {max_x vₓ, v_min⁻¹}`, `m b_i / R_i ≤ η / (8 C_*)`,
`R_i ≥ 4 (2 + log 2) / η`. -/
def OnsetOK (η : ℝ) (j : ℕ) : Prop :=
  4 ^ I.k0 η ≤ refH j ∧ I.nmax η ≤ cumB (refH j - 1) ∧
  (cumN (Fintype.card X) (refH j - 1) : ℝ) ≤ η / (4 * I.Cstar) * cumN (Fintype.card X) j ∧
  (j : ℝ) * Real.log 2 ≤ η / 4 * cumN (Fintype.card X) j ∧
  ∀ i, refH j ≤ i → I.nmax η ≤ baseB i ∧ 2 + 2 * max I.vmax I.vmin⁻¹ ≤ (i : ℝ) ∧
    (Fintype.card X : ℝ) * baseB i ≤ η / (8 * I.Cstar) * batchR (Fintype.card X) i ∧
    4 * (2 + Real.log 2) / η ≤ batchR (Fintype.card X) i

open Classical in
/-- The onset `j₁(η, θ_*, v, G) ≥ 16`: the least index from which `OnsetOK` holds. -/
def j1 (η : ℝ) : ℕ :=
  if h : ∃ j1 : ℕ, 16 ≤ j1 ∧ ∀ j, j1 ≤ j → I.OnsetOK η j then Nat.find h else 0

/-- The explicit tail `p_j` of `eq:v34-explicit-tail`. -/
def pTail (η : ℝ) (j : ℕ) : ℝ≥0∞ := explicitTail I.var (I.rho η) I.rhoK cumB baseB (refH j)

/-- `∑_{j ≥ j₁} R_{j+1} min {1, p_j}` (`eq:v34-tail-summability`). -/
def tailSum (η : ℝ) : ℝ≥0∞ :=
  ∑' j, if I.j1 η ≤ j then ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) *
    min 1 (I.pTail η j) else 0

open Classical in
/-- `j_s ≥ j₁ + 1`: the first index such that `R_j / N_{j-1} ≤ s / 4` at every later index. -/
def jS (s : ℝ) : ℕ :=
  if h : ∃ js : ℕ, I.j1 (I.eta s) + 1 ≤ js ∧ ∀ j, js < j →
      (batchR (Fintype.card X) j : ℝ) ≤ s / 4 * cumN (Fintype.card X) (j - 1)
  then Nat.find h else 0

/-- **The discovery constant `D_s` of `eq:v34-discovery-constant`:**
`D_s = N_{j_s} + ∑_{j ≥ j₁} R_{j+1} min {1, p_j} + (1 + s) / C_* · log K`. -/
def Ds (s : ℝ) : ℝ :=
  cumN (Fintype.card X) (I.jS s) + (I.tailSum (I.eta s)).toReal +
    (1 + s) / I.Cstar * Real.log (Fintype.card A)

/-! #### Existence of the onsets -/

omit [Nonempty X] in
lemma rate_le_Cstar (a : A) : I.rate a ≤ I.Cstar := Finset.le_sup' I.rate (Finset.mem_univ a)

omit [Nonempty X] in
lemma exists_rate_eq_Cstar : ∃ a, I.rate a = I.Cstar := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' univ_nonempty I.rate
  exact ⟨a, ha.symm⟩

omit [Fintype A] [Nonempty A] in
lemma vmin_le (x : X) : I.vmin ≤ I.var x := Finset.inf'_le I.var (Finset.mem_univ x)

omit [Fintype A] [Nonempty A] in
lemma le_vmax (x : X) : I.var x ≤ I.vmax := Finset.le_sup' I.var (Finset.mem_univ x)

omit [Fintype A] [Nonempty A] in
lemma vmin_pos (hv : ∀ x, 0 < I.var x) : 0 < I.vmin := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_inf' univ_nonempty I.var
  have : I.vmin = I.var x := hx
  rw [this]
  exact hv x

omit [Fintype A] [Nonempty A] in
lemma rho_pos (hv : ∀ x, 0 < I.var x) {η : ℝ} (hη : 0 < η) : 0 < I.rho η := by
  have h1 := I.vmin_pos hv
  have h2 := L0_pos h1
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

lemma exists_k0 (hv : ∀ x, 0 < I.var x) {η : ℝ} (hη : 0 < η) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k → I.RefreshOK η k := by
  classical
  have hvmin := I.vmin_pos hv
  have hL0 := L0_pos hvmin
  have hρkh : ∀ k, L0 I.vmin * I.rhoK k ≤ hyst k / 64 := by
    intro k
    have h1 := refreshRadius_le_hyst I.vmin k
    have h2 := mul_le_mul_of_nonneg_left h1 hL0.le
    have e : L0 I.vmin * (1 / Real.sqrt ((k : ℝ) + 1) / (64 * L0 I.vmin)) = hyst k / 64 := by
      unfold hyst
      field_simp
    unfold rhoK
    linarith
  set gap : A → ℝ := fun a =>
    if I.rate a < I.Cstar then (I.Cstar - I.rate a) / 4 else 1 with hgap
  have hgap0 : ∀ a, 0 < gap a := fun a => by
    simp only [hgap]
    split_ifs with h
    · linarith
    · exact one_pos
  obtain ⟨ag, -, hag⟩ := Finset.exists_min_image univ gap univ_nonempty
  obtain ⟨ka, hka⟩ := exists_hyst_lt
    (lt_min (by norm_num : (0 : ℝ) < 7 / 64) (lt_min (by positivity : 0 < η / 8) (hgap0 ag)))
  refine ⟨max ka ⌈2 + 2 * max I.vmax I.vmin⁻¹⌉₊, fun k hk => ⟨?_, ?_, ?_, ?_⟩⟩
  · have h1 : hyst k < 7 / 64 := (hka k ((le_max_left _ _).trans hk)).trans_le (min_le_left _ _)
    have h2 := hyst_pos k
    have h3 := hρkh k
    rw [← hyst_mul_self]
    nlinarith
  · have h0 := hka k ((le_max_left _ _).trans hk)
    have h1 : hyst k < 7 / 64 := h0.trans_le (min_le_left _ _)
    have h1' : hyst k < η / 8 := h0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have h2 := hyst_pos k
    have h3 := hρkh k
    rw [← hyst_mul_self]
    nlinarith
  · intro a ha
    have h1 : hyst k < gap ag :=
      (hka k ((le_max_left _ _).trans hk)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : gap ag ≤ gap a := hag a (Finset.mem_univ a)
    have h3 : gap a = (I.Cstar - I.rate a) / 4 := by
      simp only [hgap, ha, ↓reduceIte]
    linarith
  · have h1 : ⌈2 + 2 * max I.vmax I.vmin⁻¹⌉₊ ≤ k := (le_max_right _ _).trans hk
    have h2 : k < 4 ^ k := Nat.lt_pow_self (by norm_num)
    have h3 : ((⌈2 + 2 * max I.vmax I.vmin⁻¹⌉₊ : ℕ) : ℝ) ≤ (4 : ℝ) ^ k := by
      exact_mod_cast h1.trans h2.le
    exact (Nat.le_ceil _).trans h3

open Classical in
lemma k0_spec (hv : ∀ x, 0 < I.var x) {η : ℝ} (hη : 0 < η) :
    ∀ k, I.k0 η ≤ k → I.RefreshOK η k := by
  have h := I.exists_k0 hv hη
  have e : I.k0 η = Nat.find h := by
    unfold k0
    exact dite_eq_left h
  rw [e]
  exact Nat.find_spec h

lemma exists_j1 (hC : 0 < I.Cstar) {η : ℝ} (hη : 0 < η) :
    ∃ j1 : ℕ, 16 ≤ j1 ∧ ∀ j, j1 ≤ j → I.OnsetOK η j := by
  obtain ⟨j1, h16, hj1⟩ := exists_schedule_onset (Fintype.card X) hC hη
    (4 ^ I.k0 η + I.nmax η + ⌈2 + 2 * max I.vmax I.vmin⁻¹⌉₊)
  refine ⟨j1, h16, fun j hj => ?_⟩
  obtain ⟨hH, hbH, hNH, hjlog, hon⟩ := hj1 j hj
  refine ⟨((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans hH,
    ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans hbH, hNH, hjlog, fun i hi => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hon i hi
  refine ⟨((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans h2, ?_, h3, h4⟩
  have h5 : ⌈2 + 2 * max I.vmax I.vmin⁻¹⌉₊ ≤ i := (Nat.le_add_left _ _).trans h1
  exact (Nat.le_ceil _).trans (by exact_mod_cast h5)

open Classical in
lemma j1_spec (hC : 0 < I.Cstar) {η : ℝ} (hη : 0 < η) :
    16 ≤ I.j1 η ∧ ∀ j, I.j1 η ≤ j → I.OnsetOK η j := by
  have h := I.exists_j1 hC hη
  have e : I.j1 η = Nat.find h := by
    unfold j1
    exact dite_eq_left h
  rw [e]
  exact Nat.find_spec h

omit [Fintype A] [Nonempty A] [Nonempty X] in
lemma exists_jS_aux (j1 : ℕ) {s : ℝ} (hs : 0 < s) :
    ∃ js : ℕ, j1 + 1 ≤ js ∧ ∀ j, js < j →
      (batchR (Fintype.card X) j : ℝ) ≤ s / 4 * cumN (Fintype.card X) (j - 1) := by
  obtain ⟨j0, hj0⟩ := eventually_atTop.mp
    ((tendsto_batchR_div_cumN (Fintype.card X)).eventually
      (gt_mem_nhds (show (0 : ℝ) < s / 4 by positivity)))
  refine ⟨max j0 (j1 + 1), le_max_right _ _, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi0 : j0 ≤ i := by
    have := le_max_left j0 (j1 + 1)
    omega
  have hi1 : 1 ≤ i := by
    have := le_max_right j0 (j1 + 1)
    omega
  have hNpos : (0 : ℝ) < cumN (Fintype.card X) i := by
    have h := two_mul_cumN_ge (Fintype.card X) i
    have h' : (i : ℝ) * (i + 1) ≤ 2 * cumN (Fintype.card X) i := by exact_mod_cast h
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    nlinarith
  have := (div_lt_iff₀ hNpos).mp (hj0 i hi0)
  simp only [Nat.add_sub_cancel]
  linarith

open Classical in
lemma jS_spec {s : ℝ} (hs : 0 < s) :
    I.j1 (I.eta s) + 1 ≤ I.jS s ∧ ∀ j, I.jS s < j →
      (batchR (Fintype.card X) j : ℝ) ≤ s / 4 * cumN (Fintype.card X) (j - 1) := by
  have h := exists_jS_aux (X := X) (I.j1 (I.eta s)) hs
  have e : I.jS s = Nat.find h := by
    unfold jS
    exact dite_eq_left h
  rw [e]
  exact Nat.find_spec h

/-- **`eq:v34-tail-summability`:** `∑_{j ≥ j₁} R_{j+1} min {1, p_j} < ∞`, for the tail `p_j` of
`eq:v34-explicit-tail` and every `η > 0`. -/
theorem tail_summability_instance (hv : ∀ x, 0 < I.var x) {η : ℝ} (hη : 0 < η) :
    I.tailSum η ≠ ∞ :=
  tail_summability_refreshRadius (Fintype.card X) hv (I.rho_pos hv hη) (I.vmin_pos hv) (I.j1 η)

end Instance

/-! ### The stopping tail `eq:v34-tail-stop` -/

section TailStop

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Nonempty X]
  [DecidableEq X] [Fintype A] [Nonempty A] [DecidableEq A]

/-- **`eq:v34-tail-stop` for the tracker, with the manuscript's tail.**  For a tracker meeting
the oracle contracts with Borel allocation oracles, on measurable, jointly independent
intrinsic tapes `Y x n ~ N(μₓ, vₓ)`, `vₓ > 0`, with `C_* > 0` and `0 < η ≤ 8 C_*`:
`P(τ_δ > N_j) ≤ min {1, p_j}` whenever `j ≥ j₁` and `(C_* - 2 η) N_j ≥ log (K / δ)`, where
`j₁ = Instance.j1` and `p_j = Instance.pTail` (`eq:v34-explicit-tail`) are those of the
instance `T.inst μ v`. -/
theorem tail_stop (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {μ v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (μ x) (v x).toNNReal) P)
    (hC : 0 < (T.inst μ v).Cstar) {η : ℝ} (hη : 0 < η) (hηC : η ≤ 8 * (T.inst μ v).Cstar)
    {δ : ℝ} (hδ : 0 < δ) {j : ℕ} (hj : (T.inst μ v).j1 η ≤ j)
    (hstop : Real.log ((Fintype.card A : ℝ) / δ) ≤
      ((T.inst μ v).Cstar - 2 * η) * cumN (Fintype.card X) j) :
    P {ω | T.running (tapeOf Y ω) δ j} ≤ min 1 ((T.inst μ v).pTail η j) := by
  classical
  set I := T.inst μ v with hI
  have hvI : ∀ x, 0 < I.var x := hv0
  have hvmin : 0 < I.vmin := I.vmin_pos hvI
  have hv : ∀ x, I.vmin ≤ v x := fun x => I.vmin_le x
  have hvmax : ∀ x, v x ≤ I.vmax := fun x => I.le_vmax x
  have hL0 := L0_pos hvmin
  have hρ0 : 0 < I.rho η := I.rho_pos hvI hη
  have hρ1 : I.rho η ≤ 1 := min_le_left _ _
  have hρv : I.rho η ≤ I.vmin / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hρη : L0 I.vmin * I.rho η ≤ η / 16 := by
    have h1 : I.rho η ≤ η / (16 * L0 I.vmin) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 := mul_le_mul_of_nonneg_left h1 hL0.le
    have e : L0 I.vmin * (η / (16 * L0 I.vmin)) = η / 16 := by field_simp
    linarith
  have hρk0 : ∀ k, 0 < I.rhoK k := refreshRadius_pos hvmin
  have hρkv : ∀ k, I.rhoK k ≤ I.vmin / 8 := refreshRadius_le_vmin I.vmin
  have hk0 := I.k0_spec hvI hη
  obtain ⟨hj16, hj1⟩ := I.j1_spec hC hη
  obtain ⟨hHk, hbH, hNH, hjlog, hon⟩ := hj1 j hj
  have hHv : 2 + 2 * max I.vmax I.vmin⁻¹ ≤ (refH j : ℝ) := (hon (refH j) le_rfl).2.1
  have hH2 : 2 ≤ refH j := by
    have h1 : 0 < I.vmax := (hv0 (Classical.arbitrary X)).trans_le (hvmax _)
    have h2 : I.vmax ≤ max I.vmax I.vmin⁻¹ := le_max_left _ _
    have h3 : (2 : ℝ) < refH j := by linarith
    have h4 : 2 < refH j := by exact_mod_cast h3
    omega
  have hbH' : refH j ≤ cumB (refH j - 1) := by
    have := two_mul_le_cumB (refH j - 1)
    omega
  have hn0 : ∀ x i, refH j ≤ i → n0 (v x) (I.rho η) ≤ baseB i := fun x i hi =>
    (Finset.le_sup (f := fun x => n0 (I.var x) (I.rho η)) (Finset.mem_univ x)).trans
      (hon i hi).1
  refine le_min prob_le_one ?_
  refine tail_of_goodRun T hc hm P hYm hind hv0 hlaw hρ0
    (fun x => hρv.trans (by have := hv x; linarith)) hρk0
    (fun k x => (hρkv k).trans (by have := hv x; linarith)) (refH_pos j) hn0 _
    (fun ω hω hgood => ?_)
  have htest := good_run_stops T hc (tapeOf Y ω) hvmin hv hvmax hC
    (fun a => I.rate_le_Cstar a) I.exists_rate_eq_Cstar hη hηC
    hρ0.le hρ1 hρv hρη (fun k => (hρk0 k).le) hρkv
    (fun k hk => (hk0 k hk).1) (fun k hk => (hk0 k hk).2.1) (fun k hk => (hk0 k hk).2.2.1)
    hH2 hHv hHk (hj16.trans hj) le_rfl hbH' hNH hjlog
    (fun i hi => ⟨hi, (hon i hi).2.2.1, (hon i hi).2.2.2⟩) hδ hstop hgood
  exact hω j (Finset.mem_Icc.mpr ⟨by have := hj16.trans hj; omega, le_rfl⟩) htest

end TailStop

/-! ### The stopping time, the returned action, and the theorem -/

section Stopping

variable {X A Z U : Type*} [Fintype A] [DecidableEq A]

/-- The `δ`-procedure stops: the test passes at some completed batch. -/
def Stops (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : Prop := ∃ j, 1 ≤ j ∧ T.test y δ j

open Classical in
/-- The first completed batch at which the test passes (`0` if there is none). -/
def stopBatch (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : ℕ :=
  if h : Stops T y δ then Nat.find h else 0

/-- The returned action: the one selected at the stopping batch. -/
def returned (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : A := T.sel y (stopBatch T y δ)

open Classical in
/-- The stopping time `τ_δ`, in observations: `N_{T_δ}` for the stopping batch `T_δ`, and `∞`
if the procedure never stops. -/
def tau [Fintype X] (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  if Stops T y δ then ((cumN (Fintype.card X) (stopBatch T y δ) : ℕ) : ℝ≥0∞) else ⊤

variable (T : Tracker X A Z U) (y : X → ℕ → ℝ) (δ : ℝ)

open Classical in
lemma stopBatch_spec (h : Stops T y δ) :
    1 ≤ stopBatch T y δ ∧ T.test y δ (stopBatch T y δ) ∧
      ∀ j, T.running y δ j ↔ j < stopBatch T y δ := by
  have e : stopBatch T y δ = Nat.find h := by
    unfold stopBatch
    exact dite_eq_left h
  rw [e]
  refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun j => ⟨fun hr => ?_, fun hlt i hi htest => ?_⟩⟩
  · by_contra hcon
    have hs := Nat.find_spec h
    exact hr _ (Finset.mem_Icc.mpr ⟨hs.1, not_lt.mp hcon⟩) hs.2
  · have hi' := Finset.mem_Icc.mp hi
    have : Nat.find h ≤ i := Nat.find_min' h ⟨hi'.1, htest⟩
    omega

lemma running_of_not_stops (h : ¬ Stops T y δ) (j : ℕ) : T.running y δ j :=
  fun i hi htest => h ⟨i, (Finset.mem_Icc.mp hi).1, htest⟩

lemma cumN_eq_sum_range (m n : ℕ) : cumN m n = ∑ j ∈ Finset.range n, batchR m (j + 1) := by
  induction n with
  | zero => simp [cumN]
  | succ n ih => rw [cumN_succ, Finset.sum_range_succ, ih]

open Classical in
/-- **Survival identity:** `τ_δ = ∑_{j ≥ 0} R_{j+1} 1{τ_δ > N_j}`. -/
theorem tau_eq_tsum [Fintype X] :
    tau T y δ = ∑' j, ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) *
      (if T.running y δ j then (1 : ℝ≥0∞) else 0) := by
  by_cases h : Stops T y δ
  · obtain ⟨-, -, hrun⟩ := stopBatch_spec T y δ h
    have e : tau T y δ = ((cumN (Fintype.card X) (stopBatch T y δ) : ℕ) : ℝ≥0∞) := by
      unfold tau
      exact ite_eq_left h
    rw [e, cumN_eq_sum_range]
    have h1 := survival_identity (fun j => ENNReal.ofReal (batchR (Fintype.card X) j))
      (stopBatch T y δ)
    push_cast
    simp only [ENNReal.ofReal_natCast] at h1
    rw [← h1]
    refine tsum_congr fun j => ?_
    rw [ENNReal.ofReal_natCast]
    by_cases hj : j < stopBatch T y δ
    · rw [ite_eq_left ((hrun j).mpr hj), ite_eq_left hj]
    · rw [ite_eq_right (fun hr => hj ((hrun j).mp hr)), ite_eq_right hj]
  · have e : tau T y δ = ⊤ := by
      unfold tau
      exact ite_eq_right h
    rw [e]
    refine (top_unique ?_).symm
    calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ _ := tsum_le_tsum fun j => by
          rw [ite_eq_left (running_of_not_stops T y δ h j), mul_one, ← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have : 1 ≤ batchR (Fintype.card X) (j + 1) :=
            le_trans (by omega) (le_batchR (Fintype.card X) (j + 1))
          exact_mod_cast this

/-- When the procedure stops, `τ_δ` is the number of observations the tracker has consumed by
the end of its stopping batch. -/
theorem tau_eq_sum_cnt [Fintype X] (hc : T.Contract) (h : Stops T y δ) :
    tau T y δ = ((∑ x, (T.state y (stopBatch T y δ)).cnt x : ℕ) : ℝ≥0∞) := by
  classical
  have e : tau T y δ = ((cumN (Fintype.card X) (stopBatch T y δ) : ℕ) : ℝ≥0∞) := by
    unfold tau
    exact ite_eq_left h
  rw [e, T.sum_cnt y hc]

end Stopping

section Final

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Nonempty X]
  [DecidableEq X] [Fintype A] [Nonempty A] [DecidableEq A]

omit [Nonempty X] [DecidableEq X] [Nonempty A] in
/-- **`(ε, δ)`-correctness with a formal stopping time and returned action.**  The probability
that the tracker stops and returns an incorrect action (one of whose closed invalidating
components contains the truth) is at most `δ`. -/
theorem v34_correct (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | Stops T (tapeOf Y ω) δ ∧ ∃ z ∈ T.J (returned T (tapeOf Y ω) δ),
        θ ∈ T.H (returned T (tapeOf Y ω) δ) z} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (T.coverage hc hm P hind θ hv hlaw hδ)
  rintro ω ⟨hstop, hbad⟩
  exact ⟨stopBatch T (tapeOf Y ω) δ, hbad, (stopBatch_spec T _ δ hstop).2.1⟩

/-- **The tracker stops almost surely**, for every `δ > 0`. -/
theorem stops_ae (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {μ v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (μ x) (v x).toNNReal) P)
    (hC : 0 < (T.inst μ v).Cstar) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ¬ Stops T (tapeOf Y ω) δ} = 0 := by
  set I := T.inst μ v with hI
  set η : ℝ := I.Cstar / 4 with hη
  have hη0 : 0 < η := by positivity
  have hηC : η ≤ 8 * I.Cstar := by rw [hη]; linarith
  have hκ : 0 < I.Cstar - 2 * η := by rw [hη]; linarith
  have hfin := I.tail_summability_instance hv0 hη0
  have htend := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfin
  obtain ⟨ja, hja⟩ := eventually_atTop.mp
    ((tendsto_cumN_atTop (Fintype.card X)).eventually_ge_atTop
      (Real.log ((Fintype.card A : ℝ) / δ) / (I.Cstar - 2 * η)))
  refine le_antisymm ?_ zero_le
  refine ge_of_tendsto htend (eventually_atTop.mpr ⟨max ja (I.j1 η), fun j hj => ?_⟩)
  have hj1 : I.j1 η ≤ j := (le_max_right _ _).trans hj
  have hstop : Real.log ((Fintype.card A : ℝ) / δ) ≤
      (I.Cstar - 2 * η) * cumN (Fintype.card X) j := by
    have := (div_le_iff₀ hκ).mp (hja j ((le_max_left _ _).trans hj))
    linarith
  have h1 := tail_stop T hc hm P hYm hind hv0 hlaw hC hη0 hηC hδ hj1 hstop
  have hsub : {ω | ¬ Stops T (tapeOf Y ω) δ} ⊆ {ω | T.running (tapeOf Y ω) δ j} :=
    fun ω hω => running_of_not_stops T _ δ hω j
  refine (measure_mono hsub).trans (h1.trans ?_)
  show min 1 (I.pTail η j) ≤ (if I.j1 η ≤ j then
    ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) * min 1 (I.pTail η j) else 0)
  rw [ite_eq_left hj1]
  have hR : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have : 1 ≤ batchR (Fintype.card X) (j + 1) :=
      le_trans (by omega) (le_batchR (Fintype.card X) (j + 1))
    exact_mod_cast this
  calc min 1 (I.pTail η j) = 1 * min 1 (I.pTail η j) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hR zero_le

/-- **Finite-confidence bound of `eq:v34-sharp-rate` with the manuscript's constant.**  For
every real `s > 0` (in particular every rational `s ∈ (0, 1]`), every tracker meeting the oracle contracts with Borel
allocation oracles, and every probability space carrying measurable, jointly independent
intrinsic tapes `Y x n ~ N(μₓ, vₓ)`, `vₓ > 0`, with `C_* > 0`:
`E τ_δ ≤ D_s + (1 + s) / C_* · log (1 / δ)` for all `δ ∈ (0, 1)`, where
`D_s = (T.inst μ v).Ds s` is `eq:v34-discovery-constant`.  `D_s` is a function of the instance
`(J, H, pred, μ, v)` and of the schedule; it does not depend on `δ`, on the oracles of the
tracker, or on the probability space.  The expectation is the lower integral of
`τ_δ : Ω → [0, ∞]`. -/
theorem v34_finite_confidence (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas)
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {μ v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (μ x) (v x).toNNReal) P)
    (hC : 0 < (T.inst μ v).Cstar) {s : ℝ} (hs0 : 0 < s) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    ∫⁻ ω, tau T (tapeOf Y ω) δ ∂P ≤
      ENNReal.ofReal ((T.inst μ v).Ds s + (1 + s) / (T.inst μ v).Cstar * Real.log (1 / δ)) := by
  classical
  set I := T.inst μ v with hI
  set m := Fintype.card X with hm'
  set η := I.eta s with hη
  have hη0 : 0 < η := by rw [hη]; unfold Instance.eta; positivity
  have hηC : η ≤ 8 * I.Cstar := by
    rw [hη]
    unfold Instance.eta
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hK : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hfin := I.tail_summability_instance hv0 hη0
  obtain ⟨hjs, hstep⟩ := I.jS_spec hs0
  set S : ℕ → Set Ω := fun j => toMeasurable P {ω | T.running (tapeOf Y ω) δ j} with hS
  have hcum : ∀ j, ∑ i ∈ Icc 1 j, (batchR m i : ℝ) = cumN m j := fun j => by
    simp [cumN]
  set B := Real.log ((Fintype.card A : ℝ) / δ) with hB
  have hBeq : B = Real.log (Fintype.card A : ℝ) + Real.log (1 / δ) := by
    rw [hB, Real.log_div (by linarith) hδ0.ne', one_div, Real.log_inv]
    ring
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    linarith
  have hB0 : 0 ≤ B := by
    rw [hBeq]
    have := Real.log_nonneg hK
    linarith
  have hmain := expected_stopping_le P S (fun j => measurableSet_toMeasurable _ _)
    (fun j => (batchR m j : ℝ)) (fun j => Nat.cast_nonneg _) (I.pTail η)
    (C := I.Cstar) (η := η) (s := s) (B := B) (Sig := (I.tailSum η).toReal)
    (j1 := I.j1 η) (js := I.jS s) hC hs0 rfl hB0 ENNReal.toReal_nonneg
    (by simp only [hcum]; exact tendsto_cumN_atTop m) hjs
    (fun j hj => by rw [hcum]; exact hstep j hj)
    (fun j hj hcr => by
      rw [hcum] at hcr
      rw [hS]
      simp only
      rw [measure_toMeasurable]
      exact (tail_stop T hc hm P hYm hind hv0 hlaw hC hη0 hηC hδ0 hj hcr).trans
        (min_le_right _ _))
    (by rw [ENNReal.ofReal_toReal hfin]; exact le_rfl)
  have hlhs : ∫⁻ ω, tau T (tapeOf Y ω) δ ∂P ≤
      ∫⁻ ω, ∑' j, ENNReal.ofReal (batchR m (j + 1)) * (S j).indicator 1 ω ∂P := by
    refine lintegral_mono fun ω => ?_
    rw [tau_eq_tsum]
    refine tsum_le_tsum fun j => mul_le_mul_of_nonneg_left ?_ zero_le
    by_cases hr : T.running (tapeOf Y ω) δ j
    · have hmem : ω ∈ S j := subset_toMeasurable P _ hr
      rw [ite_eq_left hr, Set.indicator_of_mem hmem]
      simp
    · rw [ite_eq_right hr]
      exact zero_le
  refine hlhs.trans (hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  rw [hcum, hBeq]
  unfold Instance.Ds
  ring

/-- **Theorem `thm:v34-adaptive` (Sparse four-power nuisance-KL tracking with unknown
variances), with the manuscript's constant, tail and stopping time.**

Hypotheses.  The tracker `T` meets the oracle contracts (`Tracker.Contract`) and its
allocation oracles are Borel (`Tracker.Meas`); the observations `Y x n` are measurable and
jointly independent with `Y x n ~ N(pred x θ, vₓ)`, `vₓ > 0`; and `C_* > 0`, where
`C_* = max_a C_a^*` at the true means and variances (`Instance.Cstar`; finite by definition).

Conclusions, with `τ_δ = tau` the number of observations at the first completed batch passing
the test and `returned` the action selected there:

1. `(ε, δ)`-correctness: for every `δ > 0`, the probability of stopping with an incorrect
   action is at most `δ`, and the procedure stops almost surely;
2. for every real `s ∈ (0, 1]` and `δ ∈ (0, 1)`,
   `E τ_δ ≤ D_s + (1 + s) / C_* · log (1 / δ)` with the instance constant
   `D_s = Instance.Ds` of `eq:v34-discovery-constant`;
3. for every `c > 1 / C_*`, eventually as `δ ↓ 0`, `E τ_δ ≤ c log (1 / δ)`, that is
   `limsup E τ_δ / log (1 / δ) ≤ 1 / C_*`. -/
theorem v34_adaptive_literal (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas)
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P)
    (hC : 0 < (T.inst (fun x => T.pred x θ) v).Cstar) :
    (∀ δ : ℝ, 0 < δ →
      P {ω | Stops T (tapeOf Y ω) δ ∧ ∃ z ∈ T.J (returned T (tapeOf Y ω) δ),
          θ ∈ T.H (returned T (tapeOf Y ω) δ) z} ≤ ENNReal.ofReal δ ∧
      P {ω | ¬ Stops T (tapeOf Y ω) δ} = 0) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, tau T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal ((T.inst (fun x => T.pred x θ) v).Ds s +
          (1 + s) / (T.inst (fun x => T.pred x θ) v).Cstar * Real.log (1 / δ))) ∧
    ∀ c : ℝ, 1 / (T.inst (fun x => T.pred x θ) v).Cstar < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, tau T (tapeOf Y ω) δ ∂P).toReal ≤ c * Real.log (1 / δ) := by
  set I := T.inst (fun x => T.pred x θ) v with hI
  have hfc : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, tau T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal (I.Ds s + (1 + s) / I.Cstar * Real.log (1 / δ)) :=
    fun s hs0 _ δ hδ0 hδ1 =>
      v34_finite_confidence T hc hm P hYm hind hv0 hlaw hC hs0 hδ0 hδ1
  have hK : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hD0 : ∀ s : ℝ, 0 < s → 0 ≤ I.Ds s := by
    intro s hs
    unfold Instance.Ds
    have h1 : 0 ≤ (1 + s) / I.Cstar * Real.log (Fintype.card A) := by
      have := Real.log_nonneg hK
      positivity
    have h2 : (0 : ℝ) ≤ cumN (Fintype.card X) (I.jS s) := Nat.cast_nonneg _
    have h3 : 0 ≤ (I.tailSum (I.eta s)).toReal := ENNReal.toReal_nonneg
    linarith
  refine ⟨fun δ hδ => ⟨v34_correct T hc hm P hind θ hv0 hlaw hδ,
    stops_ae T hc hm P hYm hind hv0 hlaw hC hδ⟩, hfc, fun c hcc => ?_⟩
  refine limsup_coefficient (Eτ := fun δ => (∫⁻ ω, tau T (tapeOf Y ω) δ ∂P).toReal) hC
    (fun s : ℚ => I.Ds (s : ℝ)) (fun s hs0 hs1 δ hδ0 hδ1 => ?_) hcc
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs1' : (s : ℝ) ≤ 1 := by exact_mod_cast hs1
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    linarith
  have hnn : 0 ≤ I.Ds s + (1 + (s : ℝ)) / I.Cstar * Real.log (1 / δ) := by
    have := hD0 s hs0'
    have : 0 ≤ (1 + (s : ℝ)) / I.Cstar * Real.log (1 / δ) := by positivity
    linarith
  exact ENNReal.toReal_le_of_le_ofReal hnn (hfc s hs0' hs1' δ hδ0 hδ1)

end Final

end

end LiteralD2c

end JointRootCert
