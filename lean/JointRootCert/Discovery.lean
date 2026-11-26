/-
Discovery cost for an adaptive Bernoulli sampler.

Manuscript result covered:

* `prop:ast-discovery` "A discovery cost absent from the characteristic time":
  `discovery_cost_sampler` proves the expectation bound with hypotheses on the sampler only
  (`δ`-correctness on the `N+1` instances), and `discovery_cost_sampler_rate` adds the rate bound
  `C_A^0(μ^j) ≥ g²/2` of `discovery_rate`.

Model: the deterministic adaptive sampler of `StoppedProcess.lean`.  The manuscript couples the
null run and the run under `μ^j` through shared reward tapes; the two runs agree until the first
request to `x_j`.  Here the consequence of that coupling is proved directly on the laws of the
stopped histories: a history in which `x_j` has not been requested has the same likelihood under
the null instance and under `μ^j` (`lik_eq_of_cnt_eq_zero`), hence every functional of the
history that only accumulates before the first request to `x_j` has the same expectation under
both (`valueFn_congr`, `sum_leaves_acc`).  This replaces the hypotheses `hpos`, `hinj`, `htime`,
`hans` of `discovery_cost`; no coupled probability space is assumed.
-/
import JointRootCert.StoppedProcess

namespace JointRootCert

open Finset Real Filter Topology

set_option linter.unusedSectionVars false

namespace Stopped

section Discovery

variable {Z : Type*} [DecidableEq Z]

/-- Additive functional of a history: the sum of `φ` over its proper prefixes. -/
def acc (φ : List Bool → ℝ) : List Bool → ℝ
  | [] => 0
  | _ :: h => acc φ h + φ h

/-- Expected future increment of `acc φ` over at most `n` further rounds, started at `h`. -/
noncomputable def valueFn (S : Sampler Z) (μ : Z → ℝ) (φ : List Bool → ℝ) :
    ℕ → List Bool → ℝ
  | 0, _ => 0
  | n + 1, h =>
      if S.stop h then 0
      else φ h + μ (S.next h) * valueFn S μ φ n (true :: h)
        + (1 - μ (S.next h)) * valueFn S μ φ n (false :: h)

/-- The expectation of an additive functional of the stopped history. -/
lemma sum_leaves_acc (S : Sampler Z) (μ : Z → ℝ) (φ : List Bool → ℝ) :
    ∀ (n : ℕ) (h : List Bool),
      ∑ l ∈ leaves S n h, lik S μ l * acc φ l = lik S μ h * (acc φ h + valueFn S μ φ n h)
  | 0, h => by simp [valueFn]
  | n + 1, h => by
      rw [sum_leaves_succ]
      by_cases hs : S.stop h = true
      · simp [valueFn, hs]
      · rw [ite_eq_right hs, sum_leaves_acc S μ φ n, sum_leaves_acc S μ φ n]
        simp only [valueFn, hs, lik, acc, bern_true, bern_false]
        simp only [Bool.false_eq_true, ite_false]
        ring

lemma cnt_cons_pos (S : Sampler Z) (x : Z) (b : Bool) {h : List Bool} (hc : cnt S x h ≠ 0) :
    cnt S x (b :: h) ≠ 0 := by
  simp only [cnt]
  omega

/-- A functional that stops accumulating once `x` has been requested has no future increment
after the first request. -/
lemma valueFn_eq_zero (S : Sampler Z) (μ : Z → ℝ) {φ : List Bool → ℝ} {x : Z}
    (hφ : ∀ h, cnt S x h ≠ 0 → φ h = 0) :
    ∀ (n : ℕ) (h : List Bool), cnt S x h ≠ 0 → valueFn S μ φ n h = 0
  | 0, _, _ => rfl
  | n + 1, h, hc => by
      simp only [valueFn]
      split_ifs
      · rfl
      · rw [hφ h hc, valueFn_eq_zero S μ hφ n _ (cnt_cons_pos S x true hc),
          valueFn_eq_zero S μ hφ n _ (cnt_cons_pos S x false hc)]
        ring

/-- Two mean vectors that differ only at `x` give the same expectation to every functional that
stops accumulating at the first request to `x`. -/
lemma valueFn_congr (S : Sampler Z) {μ μ' : Z → ℝ} {φ : List Bool → ℝ} {x : Z}
    (hμ : ∀ z, z ≠ x → μ z = μ' z) (hφ : ∀ h, cnt S x h ≠ 0 → φ h = 0) :
    ∀ (n : ℕ) (h : List Bool), valueFn S μ φ n h = valueFn S μ' φ n h
  | 0, _ => rfl
  | n + 1, h => by
      simp only [valueFn]
      split_ifs with hs
      · rfl
      · by_cases hx : S.next h = x
        · have hc : ∀ b, cnt S x (b :: h) ≠ 0 := fun b => by
            simp only [cnt, hx, ite_true]
            omega
          rw [valueFn_eq_zero S μ hφ n _ (hc true), valueFn_eq_zero S μ hφ n _ (hc false),
            valueFn_eq_zero S μ' hφ n _ (hc true), valueFn_eq_zero S μ' hφ n _ (hc false)]
          ring
        · rw [hμ _ hx, valueFn_congr S hμ hφ n, valueFn_congr S hμ hφ n]

/-- A history in which `x` has not been requested has the same likelihood under two mean vectors
that differ only at `x`. -/
lemma lik_eq_of_cnt_eq_zero (S : Sampler Z) {μ μ' : Z → ℝ} {x : Z}
    (hμ : ∀ z, z ≠ x → μ z = μ' z) :
    ∀ l : List Bool, cnt S x l = 0 → lik S μ l = lik S μ' l
  | [], _ => rfl
  | b :: h, hc => by
      simp only [cnt] at hc
      have h1 : cnt S x h = 0 := by omega
      have h2 : S.next h ≠ x := by
        intro e
        rw [ite_eq_left e] at hc
        omega
      simp only [lik]
      rw [lik_eq_of_cnt_eq_zero S hμ h h1, hμ _ h2]

/-- Number of rounds of the history that were requested while `x` had not yet been requested:
`min(T_x, |l|)` with `T_x` the index (from 1) of the first request to `x`. -/
def quiet (S : Sampler Z) (x : Z) : List Bool → ℕ
  | [] => 0
  | _ :: h => quiet S x h + if cnt S x h = 0 then 1 else 0

lemma quiet_le_length (S : Sampler Z) (x : Z) : ∀ l : List Bool, quiet S x l ≤ l.length
  | [] => le_rfl
  | _ :: h => by
      have := quiet_le_length S x h
      simp only [quiet, List.length_cons]
      split_ifs <;> omega

lemma quiet_eq_acc (S : Sampler Z) (x : Z) :
    ∀ l : List Bool, (quiet S x l : ℝ) = acc (fun h => if cnt S x h = 0 then 1 else 0) l
  | [] => by simp [quiet, acc]
  | _ :: h => by
      simp only [quiet, acc, Nat.cast_add, quiet_eq_acc S x h]
      split_ifs <;> simp

/-- `E_μ[min(T_x, τ ∧ n)]` does not depend on the mean of `x`. -/
lemma sum_lik_quiet_congr (S : Sampler Z) {μ μ' : Z → ℝ} {x : Z}
    (hμ : ∀ z, z ≠ x → μ z = μ' z) (n : ℕ) :
    ∑ l ∈ leaves S n [], lik S μ l * (quiet S x l : ℝ)
      = ∑ l ∈ leaves S n [], lik S μ' l * (quiet S x l : ℝ) := by
  simp only [quiet_eq_acc]
  rw [sum_leaves_acc, sum_leaves_acc, valueFn_congr S hμ (fun h hc => ite_eq_right hc) n []]
  simp [lik]

variable {N : ℕ}

/-- The terminals among `x_1, …, x_N` not yet requested in a history. -/
def unreq (S : Sampler Z) (x : Fin N → Z) (l : List Bool) : Finset (Fin N) :=
  univ.filter fun j => cnt S (x j) l = 0

lemma mem_unreq (S : Sampler Z) (x : Fin N → Z) (l : List Bool) (j : Fin N) :
    j ∈ unreq S x l ↔ cnt S (x j) l = 0 := by
  simp [unreq]

lemma cnt_cons (S : Sampler Z) (z : Z) (b : Bool) (h : List Bool) :
    cnt S z (b :: h) = cnt S z h + if S.next h = z then 1 else 0 := rfl

lemma unreq_cons_subset (S : Sampler Z) (x : Fin N → Z) (b : Bool) (h : List Bool) :
    unreq S x (b :: h) ⊆ unreq S x h := by
  intro j hj
  rw [mem_unreq, cnt_cons] at hj
  rw [mem_unreq]
  omega

lemma card_unreq_le (S : Sampler Z) {x : Fin N → Z} (hx : Function.Injective x) (b : Bool)
    (h : List Bool) : (unreq S x h).card ≤ (unreq S x (b :: h)).card + 1 := by
  have h1 := card_le_card_sdiff_add_card (s := unreq S x h) (t := unreq S x (b :: h))
  have h2 : (unreq S x h \ unreq S x (b :: h)).card ≤ 1 := by
    refine card_le_one.2 fun i hi j hj => hx ?_
    have key : ∀ k ∈ unreq S x h \ unreq S x (b :: h), S.next h = x k := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.1 hk
      rw [mem_unreq] at hk1
      rw [mem_unreq, cnt_cons] at hk2
      by_contra hne
      rw [ite_eq_right hne] at hk2
      omega
    rw [← key i hi, ← key j hj]
  omega

lemma card_unreq_le_card (S : Sampler Z) (x : Fin N → Z) (l : List Bool) :
    (unreq S x l).card ≤ N := by
  simpa using card_le_univ (unreq S x l)

/-- Pathwise counting step of `prop:ast-discovery`: with `K` the number of unrequested `x_j`,
`(N - K)(N + K + 1) ≤ 2 ∑_j min(T_j, |l|)`. -/
lemma quiet_invariant (S : Sampler Z) {x : Fin N → Z} (hx : Function.Injective x) :
    ∀ l : List Bool,
      ((N : ℝ) - (unreq S x l).card) * ((N : ℝ) + (unreq S x l).card + 1)
        ≤ 2 * ∑ j, (quiet S (x j) l : ℝ)
  | [] => by
      have : (unreq S x ([] : List Bool)).card = N := by simp [unreq, cnt]
      simp [this, quiet]
  | b :: h => by
      have ih := quiet_invariant S hx h
      have hsum : ∑ j, (quiet S (x j) (b :: h) : ℝ)
          = ∑ j, (quiet S (x j) h : ℝ) + (unreq S x h).card := by
        simp only [quiet, Nat.cast_add, sum_add_distrib]
        congr 1
        rw [unreq, card_filter]
        push_cast
        rfl
      have h1 : ((unreq S x (b :: h)).card : ℝ) ≤ (unreq S x h).card := by
        exact_mod_cast card_le_card (unreq_cons_subset S x b h)
      have h2 : ((unreq S x h).card : ℝ) ≤ (unreq S x (b :: h)).card + 1 := by
        exact_mod_cast card_unreq_le S hx b h
      have h3 : (0 : ℝ) ≤ (unreq S x (b :: h)).card := Nat.cast_nonneg _
      rw [hsum]
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (add_nonneg h3 (h3.trans h1))]

/-- Pathwise: `(N+1) · #{j : x_j requested} ≤ 2 ∑_j min(T_j, |l|)`. -/
lemma quiet_pathwise (S : Sampler Z) {x : Fin N → Z} (hx : Function.Injective x)
    (l : List Bool) :
    ((N : ℝ) + 1) * ((N : ℝ) - (unreq S x l).card) ≤ 2 * ∑ j, (quiet S (x j) l : ℝ) := by
  have h1 := quiet_invariant S hx l
  have h2 : ((unreq S x l).card : ℝ) ≤ N := by exact_mod_cast card_unreq_le_card S x l
  have h3 : (0 : ℝ) ≤ (unreq S x l).card := Nat.cast_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.2 h2) h3]

lemma sum_requested (S : Sampler Z) (x : Fin N → Z) (l : List Bool) :
    ∑ j : Fin N, (if cnt S (x j) l = 0 then (0 : ℝ) else 1) = (N : ℝ) - (unreq S x l).card := by
  have h1 : ∑ j : Fin N, (if cnt S (x j) l = 0 then (1 : ℝ) else 0) = (unreq S x l).card := by
    rw [unreq, card_filter]
    push_cast
    rfl
  have h2 : ∑ j : Fin N, ((if cnt S (x j) l = 0 then (0 : ℝ) else 1)
      + (if cnt S (x j) l = 0 then (1 : ℝ) else 0)) = N := by
    rw [sum_congr rfl (fun j _ => by split_ifs <;> simp : ∀ j ∈ (univ : Finset (Fin N)),
      (if cnt S (x j) l = 0 then (0 : ℝ) else 1) + (if cnt S (x j) l = 0 then (1 : ℝ) else 0)
        = 1)]
    simp
  rw [sum_add_distrib, h1] at h2
  linarith

variable [Fintype Z]

/-- **Finite-horizon core of `prop:ast-discovery`.**  `μ0` is the null instance, `μs j` differs
from it only at the terminal `x j`; `B` is the set of histories at which the answer that is
correct under `μ0` is returned.  If under every `μs j` the sampler stops in `B` with probability
at most `δ`, then for every horizon `n`
`∑_j E_{μ^j}[τ ∧ n] ≥ (N+1)/2 · N · (P_0(τ ≤ n, H_τ ∈ B) - δ)`. -/
theorem discovery_finite (S : Sampler Z) {x : Fin N → Z} (hx : Function.Injective x)
    {μ0 : Z → ℝ} {μs : Fin N → Z → ℝ} (h0 : ∀ z, 0 < μ0 z ∧ μ0 z < 1)
    (hs : ∀ j z, 0 < μs j z ∧ μs j z < 1) (hagree : ∀ j z, z ≠ x j → μs j z = μ0 z)
    (B : Set (List Bool)) {δ : ℝ} (hδ : ∀ j, probInf S (μs j) B ≤ δ) (n : ℕ) :
    ((N : ℝ) + 1) / 2 * (N * (prob S μ0 n (B ∩ stopSet S) - δ)) ≤ ∑ j, expTime S (μs j) n := by
  -- step 1: expected time dominates the expected time before the first request to `x j`
  have step1 : ∀ j, ∑ l ∈ leaves S n [], lik S μ0 l * (quiet S (x j) l : ℝ)
      ≤ expTime S (μs j) n := by
    intro j
    rw [← sum_lik_quiet_congr S (hagree j) n]
    exact sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
      (by exact_mod_cast quiet_le_length S (x j) l) (lik_pos S (hs j) l).le
  -- step 2: probability that `x j` is requested by `τ ∧ n`
  have step2 : ∀ j, prob S μ0 n (B ∩ stopSet S) - δ
      ≤ ∑ l ∈ leaves S n [], lik S μ0 l * (if cnt S (x j) l = 0 then (0 : ℝ) else 1) := by
    intro j
    have hle : prob S (μs j) n ((B ∩ {l | cnt S (x j) l = 0}) ∩ stopSet S) ≤ δ :=
      ((prob_le_probInf S (hs j) n _).trans
        (probInf_mono S (hs j) Set.inter_subset_left)).trans (hδ j)
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
  -- step 3: pathwise counting
  have step3 : ((N : ℝ) + 1) / 2
        * ∑ l ∈ leaves S n [], lik S μ0 l * ((N : ℝ) - (unreq S x l).card)
      ≤ ∑ j, ∑ l ∈ leaves S n [], lik S μ0 l * (quiet S (x j) l : ℝ) := by
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun l _ => ?_
    rw [← mul_sum]
    have := quiet_pathwise S hx l
    have hp := (lik_pos S h0 l).le
    nlinarith
  have step4 : (N : ℝ) * (prob S μ0 n (B ∩ stopSet S) - δ)
      ≤ ∑ l ∈ leaves S n [], lik S μ0 l * ((N : ℝ) - (unreq S x l).card) := by
    have := sum_le_sum (s := (univ : Finset (Fin N))) fun j _ => step2 j
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_comm] at this
    refine this.trans (le_of_eq (sum_congr rfl fun l _ => ?_))
    rw [← mul_sum, sum_requested]
  calc ((N : ℝ) + 1) / 2 * (N * (prob S μ0 n (B ∩ stopSet S) - δ))
      ≤ ((N : ℝ) + 1) / 2
          * ∑ l ∈ leaves S n [], lik S μ0 l * ((N : ℝ) - (unreq S x l).card) :=
        mul_le_mul_of_nonneg_left step4 (by positivity)
    _ ≤ ∑ j, ∑ l ∈ leaves S n [], lik S μ0 l * (quiet S (x j) l : ℝ) := step3
    _ ≤ ∑ j, expTime S (μs j) n := sum_le_sum fun j _ => step1 j

/-- Discovery cost, general form: if the sampler stops in `B` with probability at least `1 - δ`
under the null instance and at most `δ` under each `μ^j`, and has finite expected stopping time
under each `μ^j`, then some `μ^j` has `E_{μ^j} τ ≥ (N+1)/2 · (1 - 2δ)`. -/
theorem discovery_general (hN : 0 < N) (S : Sampler Z) {x : Fin N → Z}
    (hx : Function.Injective x) {μ0 : Z → ℝ} {μs : Fin N → Z → ℝ}
    (h0 : ∀ z, 0 < μ0 z ∧ μ0 z < 1) (hs : ∀ j z, 0 < μs j z ∧ μs j z < 1)
    (hagree : ∀ j z, z ≠ x j → μs j z = μ0 z) (B : Set (List Bool)) {δ : ℝ}
    (hB0 : 1 - δ ≤ probInf S μ0 B) (hδ : ∀ j, probInf S (μs j) B ≤ δ)
    {Bd : Fin N → ℝ} (hBd : ∀ j n, expTime S (μs j) n ≤ Bd j) :
    ∃ j, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) ≤ expTimeInf S (μs j) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ∀ j n, expTime S (μs j) n ≤ expTimeInf S (μs j) := fun j n =>
    le_ciSup (f := fun n => expTime S (μs j) n)
      ⟨Bd j, by rintro _ ⟨m, rfl⟩; exact hBd j m⟩ n
  have hfin : ∀ n, ((N : ℝ) + 1) / 2 * (N * (prob S μ0 n (B ∩ stopSet S) - δ))
      ≤ ∑ j, expTimeInf S (μs j) := fun n =>
    (discovery_finite S hx h0 hs hagree B hδ n).trans (sum_le_sum fun j _ => hle j n)
  have hlim : Tendsto (fun n => ((N : ℝ) + 1) / 2 * (N * (prob S μ0 n (B ∩ stopSet S) - δ)))
      atTop (𝓝 (((N : ℝ) + 1) / 2 * (N * (probInf S μ0 B - δ)))) :=
    (((tendsto_probInf S h0 B).sub_const δ).const_mul _).const_mul _
  have hsum : ((N : ℝ) + 1) / 2 * (N * (probInf S μ0 B - δ)) ≤ ∑ j, expTimeInf S (μs j) :=
    le_of_tendsto' hlim hfin
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h5 : ∑ j : Fin N, expTimeInf S (μs j)
      < ∑ _j : Fin N, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) :=
    sum_lt_sum_of_nonempty univ_nonempty fun j _ => hcon j
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h5
  have h6 : (N : ℝ) * (1 - 2 * δ) ≤ N * (probInf S μ0 B - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hNr.le
  nlinarith [mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1) / 2)]

end Discovery

/-! ### `prop:ast-discovery` -/

lemma discMu_agree (N : ℕ) (g : ℝ) (j : Fin N) :
    ∀ z : Fan N, z ≠ some (some j) → discMu N g (some j) z = discMu N g none z := by
  rintro (_ | _ | i) hz
  · rfl
  · rfl
  · have hij : j ≠ i := fun e => hz (by rw [e])
    simp [discMu_x, hij]

/-- **A discovery cost absent from the characteristic time** (`prop:ast-discovery`, expectation
bound) for a deterministic adaptive sampler `S` on the terminals `c, z, x_1, …, x_N` with
decision rule `dec` (`true` = action `A` with support `{c, x_1, …, x_N}`, `false` = action `B`
with support `{c, z}`; by `discovery_instances`, `B` is the unique correct answer under the
null instance and `A` under every `μ^j`).

Hypotheses on the sampler only: `hcorr0`, `hcorr` are `δ`-correctness with almost-sure stopping
on the `N + 1` instances (the sampler stops and returns the correct answer with probability at
least `1 - δ`); `hBd` is finiteness of the expected stopping time at each `μ^j` (if one of them
is infinite the manuscript's claim holds trivially).  Conclusion: some instance `μ^j` has
`E_{μ^j} τ ≥ (N+1)/2 · (1 - 2δ)`. -/
theorem discovery_cost_sampler {N : ℕ} (hN : 0 < N) {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    {δ : ℝ} (S : Sampler (Fan N)) (dec : List Bool → Bool)
    (hcorr0 : 1 - δ ≤ probInf S (discMu N g none) {l | dec l = false})
    (hcorr : ∀ j : Fin N, 1 - δ ≤ probInf S (discMu N g (some j)) {l | dec l = true})
    {Bd : Fin N → ℝ} (hBd : ∀ j n, expTime S (discMu N g (some j)) n ≤ Bd j) :
    ∃ j : Fin N, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) ≤ expTimeInf S (discMu N g (some j)) := by
  refine discovery_general hN S (x := fun j : Fin N => (some (some j) : Fan N))
    (fun i j e => by simpa using e) (discMu_interior hg hg8 none)
    (fun j => discMu_interior hg hg8 (some j)) (fun j z hz => discMu_agree N g j z hz)
    {l | dec l = false} hcorr0 (fun j => ?_) hBd
  have hdis : Disjoint {l : List Bool | dec l = false} {l | dec l = true} :=
    Set.disjoint_left.2 fun l h1 h2 => by
      rw [Set.mem_ofPred_eq] at h1 h2
      rw [h1] at h2
      exact Bool.false_ne_true h2
  have := probInf_add_le_one S (discMu_interior hg hg8 (some j)) hdis
  linarith [hcorr j]

/-- `prop:ast-discovery` without the finiteness hypothesis: for some instance `μ^j` the
truncated expectations `E_{μ^j}[τ ∧ n]` exceed every number below `(N+1)/2 · (1 - 2δ)`
(so `E_{μ^j} τ`, finite or not, is at least that bound). -/
theorem discovery_cost_sampler' {N : ℕ} (hN : 0 < N) {g : ℝ} (hg : 0 < g) (hg8 : g ≤ 1 / 8)
    {δ : ℝ} (S : Sampler (Fan N)) (dec : List Bool → Bool)
    (hcorr0 : 1 - δ ≤ probInf S (discMu N g none) {l | dec l = false})
    (hcorr : ∀ j : Fin N, 1 - δ ≤ probInf S (discMu N g (some j)) {l | dec l = true}) :
    ∃ j : Fin N, ∀ c < ((N : ℝ) + 1) / 2 * (1 - 2 * δ),
      ∃ n, c < expTime S (discMu N g (some j)) n := by
  by_contra hcon
  simp only [not_exists, not_forall, not_lt] at hcon
  choose c hc hcn using hcon
  obtain ⟨j, hj⟩ := discovery_cost_sampler hN hg hg8 S dec hcorr0 hcorr (Bd := c) hcn
  have : expTimeInf S (discMu N g (some j)) ≤ c j := ciSup_le fun n => hcn j n
  linarith [hc j]

/-- **`prop:ast-discovery`**, both displayed bounds: under the hypotheses of
`discovery_cost_sampler`, some instance `μ^j` has `E_{μ^j} τ ≥ (N+1)/2 · (1 - 2δ)` and
`C_A^0(μ^j) ≥ g²/2` (the rate of its unique correct action; `g ∈ (0,1/8]` does not depend on
`N`). -/
theorem discovery_cost_sampler_rate {N : ℕ} (hN : 0 < N) {g : ℝ} (hg : 0 < g)
    (hg8 : g ≤ 1 / 8) {δ : ℝ} (S : Sampler (Fan N)) (dec : List Bool → Bool)
    (hcorr0 : 1 - δ ≤ probInf S (discMu N g none) {l | dec l = false})
    (hcorr : ∀ j : Fin N, 1 - δ ≤ probInf S (discMu N g (some j)) {l | dec l = true})
    {Bd : Fin N → ℝ} (hBd : ∀ j n, expTime S (discMu N g (some j)) n ≤ Bd j) :
    ∃ j : Fin N, ((N : ℝ) + 1) / 2 * (1 - 2 * δ) ≤ expTimeInf S (discMu N g (some j)) ∧
      g ^ 2 / 2 ≤ charRate (fanSupp N) 0 (discMu N g (some j)) := by
  obtain ⟨j, hj⟩ := discovery_cost_sampler hN hg hg8 S dec hcorr0 hcorr hBd
  exact ⟨j, hj, discovery_rate hg hg8 j⟩

end Stopped

end JointRootCert
