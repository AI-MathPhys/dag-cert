/-
Stopped adaptive sampling processes and the Bernoulli change of measure.

Manuscript results covered:

* `lem:active-com` "Stopped Bernoulli change of measure": proved for a deterministic adaptive
  sampler, first at every finite horizon (`wald_identity`, `stopped_transport_finite`) and then
  for an unbounded stopping time with finite expected value (`stopped_transport`).
* `thm:active-star-lb` "Non-containment tied-star lower bound": `tied_star_lower_bound_sampler`
  removes the hypotheses `htrans`, `hac` of `tied_star_lower_bound`.
* the fixed-answer transportation bound `transport_lower_bound`:
  `transport_lower_bound_sampler` removes its hypothesis `htrans`.

Model.  A sampler is a pair of functions of the observed outcome history (a `List Bool`, most
recent observation first): the next terminal to query and whether to stop.  The policy is
deterministic, so the queried terminals are functions of the outcomes.  The law of the history
stopped at `τ ∧ n` under a mean vector `μ` is the finitely supported weight `lik S μ` on the
finite set `leaves S n []` of stopped histories; the weight of a history is the product of the
Bernoulli likelihoods of its observations.  Section "Reward-table model" proves that this is the
law of the stopped history when the outcomes are read from a table of independent Bernoulli
variables (`table_law_stopped_history`).

Not covered: internal randomization of the sampler, and the Gaussian analogue used by
`thm:v34-converse` (`converse_reduction` keeps its hypothesis `htransport`).
-/
import JointRootCert.BernoulliInfo

namespace JointRootCert

open Finset Real Filter Topology

set_option linter.unusedSectionVars false

namespace Stopped

/-! ### Finite Kullback--Leibler data processing -/

/-- Donsker--Varadhan bound for a two-valued test function on a finite probability space. -/
lemma two_point_le_sum {ι : Type*} (s : Finset ι) (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    (hq : ∀ i ∈ s, 0 < q i) (hp1 : ∑ i ∈ s, p i = 1) (hq1 : ∑ i ∈ s, q i = 1) (A : Set ι)
    (a b : ℝ) :
    a * (∑ i ∈ s, A.indicator p i) + b * (1 - ∑ i ∈ s, A.indicator p i)
        - log (exp a * (∑ i ∈ s, A.indicator q i) + exp b * (1 - ∑ i ∈ s, A.indicator q i))
      ≤ ∑ i ∈ s, p i * log (p i / q i) := by
  classical
  set f : ι → ℝ := fun i => if i ∈ A then a else b with hf
  have hP : (1 : ℝ) - ∑ i ∈ s, A.indicator p i = ∑ i ∈ s, (p i - A.indicator p i) := by
    rw [sum_sub_distrib, hp1]
  have hQ : (1 : ℝ) - ∑ i ∈ s, A.indicator q i = ∑ i ∈ s, (q i - A.indicator q i) := by
    rw [sum_sub_distrib, hq1]
  have e1 : a * (∑ i ∈ s, A.indicator p i) + b * (1 - ∑ i ∈ s, A.indicator p i)
      = ∑ i ∈ s, p i * f i := by
    rw [hP, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ A <;> simp [hf, hi, mul_comm]
  have e2 : exp a * (∑ i ∈ s, A.indicator q i) + exp b * (1 - ∑ i ∈ s, A.indicator q i)
      = ∑ i ∈ s, p i * (q i * exp (f i) / p i) := by
    rw [hQ, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i hi' => ?_
    have := (hp i hi').ne'
    have e : p i * (q i * exp (f i) / p i) = q i * exp (f i) := by field_simp
    rw [e]
    by_cases hi : i ∈ A <;> simp [hf, hi, mul_comm]
  have J := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := s) (w := p)
    (p := fun i => q i * exp (f i) / p i) (fun i hi => (hp i hi).le) hp1
    (fun i hi => div_pos (mul_pos (hq i hi) (exp_pos _)) (hp i hi))
  simp only [smul_eq_mul] at J
  have e3 : ∑ i ∈ s, p i * log (q i * exp (f i) / p i)
      = ∑ i ∈ s, p i * f i - ∑ i ∈ s, p i * log (p i / q i) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [log_div (mul_pos (hq i hi) (exp_pos _)).ne' (hp i hi).ne',
      log_mul (hq i hi).ne' (exp_pos _).ne', log_exp, log_div (hp i hi).ne' (hq i hi).ne']
    ring
  rw [e1, e2]
  linarith

lemma indicator_le_of_pos {ι : Type*} (A : Set ι) {r : ι → ℝ} {i : ι} (h : 0 < r i) :
    A.indicator r i ≤ r i := by
  by_cases hi : i ∈ A <;> simp [hi, h.le]

lemma indicator_nonneg_of_pos {ι : Type*} (A : Set ι) {r : ι → ℝ} {i : ι} (h : 0 < r i) :
    0 ≤ A.indicator r i := by
  by_cases hi : i ∈ A <;> simp [hi, h.le]

/-- If an event has positive `p`-mass it has positive `q`-mass (both weights positive). -/
lemma sum_indicator_pos_of_pos {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 < q i) (A : Set ι) (h : 0 < ∑ i ∈ s, A.indicator p i) :
    0 < ∑ i ∈ s, A.indicator q i := by
  have hex : ∃ i ∈ s, i ∈ A := by
    by_contra hcon
    have : ∑ i ∈ s, A.indicator p i = 0 :=
      sum_eq_zero fun i hi => Set.indicator_of_notMem (fun hiA => hcon ⟨i, hi, hiA⟩) _
    linarith
  obtain ⟨i, hi, hiA⟩ := hex
  have h1 : A.indicator q i ≤ ∑ j ∈ s, A.indicator q j :=
    single_le_sum (f := A.indicator q) (fun j hj => indicator_nonneg_of_pos A (hq j hj)) hi
  rw [Set.indicator_of_mem hiA] at h1
  exact (hq i hi).trans_le h1

/-- **Finite binary data processing** (log-sum inequality): for two positive probability
weights on a finite set and any event `A`, `kl(p(A), q(A)) ≤ ∑ p log(p/q)`. -/
theorem bkl_le_sum_log {ι : Type*} (s : Finset ι) (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    (hq : ∀ i ∈ s, 0 < q i) (hp1 : ∑ i ∈ s, p i = 1) (hq1 : ∑ i ∈ s, q i = 1) (A : Set ι) :
    bkl (∑ i ∈ s, A.indicator p i) (∑ i ∈ s, A.indicator q i)
      ≤ ∑ i ∈ s, p i * log (p i / q i) := by
  refine bkl_le_of_two_point
    (sum_nonneg fun i hi => indicator_nonneg_of_pos A (hp i hi))
    (hp1 ▸ sum_le_sum fun i hi => indicator_le_of_pos A (hp i hi))
    (sum_nonneg fun i hi => indicator_nonneg_of_pos A (hq i hi))
    (hq1 ▸ sum_le_sum fun i hi => indicator_le_of_pos A (hq i hi))
    (sum_indicator_pos_of_pos s p q hq A) ?_
    (two_point_le_sum s p q hp hq hp1 hq1 A)
  intro hP
  have hex : ∃ i ∈ s, i ∉ A := by
    by_contra hcon
    have : ∑ i ∈ s, A.indicator p i = ∑ i ∈ s, p i :=
      sum_congr rfl fun i hi => Set.indicator_of_mem (by
        by_contra hiA
        exact hcon ⟨i, hi, hiA⟩) _
    rw [this, hp1] at hP
    exact lt_irrefl _ hP
  obtain ⟨i, hi, hiA⟩ := hex
  rw [← hq1]
  refine sum_lt_sum (fun j hj => indicator_le_of_pos A (hq j hj)) ⟨i, hi, ?_⟩
  rw [Set.indicator_of_notMem hiA]
  exact hq i hi

/-- Passage to the limit in the two-point characterization of the binary divergence. -/
lemma bkl_le_of_tendsto {p q : ℕ → ℝ} {P Q K : ℝ} (hp : Tendsto p atTop (𝓝 P))
    (hq : Tendsto q atTop (𝓝 Q)) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hpq0 : 0 < P → 0 < Q) (hpq1 : P < 1 → Q < 1)
    (h : ∀ n a b, a * p n + b * (1 - p n) - log (exp a * q n + exp b * (1 - q n)) ≤ K) :
    bkl P Q ≤ K := by
  refine bkl_le_of_two_point hP0 hP1 hQ0 hQ1 hpq0 hpq1 fun a b => ?_
  have hpos : exp a * Q + exp b * (1 - Q) ≠ 0 := by
    have ha := exp_pos a
    have hb := exp_pos b
    have : 0 < exp a * Q + exp b * (1 - Q) := by
      rcases hQ0.eq_or_lt with h0 | h0
      · rw [← h0]; simpa using hb
      · have := mul_pos ha h0
        have := mul_nonneg hb.le (sub_nonneg.2 hQ1)
        linarith
    exact this.ne'
  have hT : Tendsto (fun n => a * p n + b * (1 - p n)
      - log (exp a * q n + exp b * (1 - q n))) atTop
      (𝓝 (a * P + b * (1 - P) - log (exp a * Q + exp b * (1 - Q)))) :=
    ((hp.const_mul a).add ((hp.const_sub 1).const_mul b)).sub
      (((hq.const_mul (exp a)).add ((hq.const_sub 1).const_mul (exp b))).log hpos)
  exact le_of_tendsto' hT fun n => h n a b

/-! ### Samplers, stopped histories and their law -/

/-- Likelihood of one Bernoulli(`p`) observation. -/
noncomputable def bern (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

@[simp] lemma bern_true (p : ℝ) : bern p true = p := by simp [bern]

@[simp] lemma bern_false (p : ℝ) : bern p false = 1 - p := by simp [bern]

lemma bern_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (b : Bool) : 0 < bern p b := by
  cases b
  · rw [bern_false]; linarith
  · rw [bern_true]; exact h0

/-- A deterministic adaptive sampler: the next terminal and the stopping decision are functions
of the observed outcomes (most recent first). -/
structure Sampler (Z : Type*) where
  /-- terminal queried after observing the history -/
  next : List Bool → Z
  /-- whether the sampler stops at the history -/
  stop : List Bool → Bool

variable {Z : Type*}

/-- Probability under `μ` of observing the outcome sequence `l` (in the order in which the
sampler requests it): the product of the Bernoulli likelihoods of the observations. -/
noncomputable def lik (S : Sampler Z) (μ : Z → ℝ) : List Bool → ℝ
  | [] => 1
  | b :: h => lik S μ h * bern (μ (S.next h)) b

/-- Histories reachable from `h` when the sampler is run for at most `n` further rounds and
frozen when it stops: the possible values of the history stopped at `τ ∧ (|h| + n)`. -/
def leaves (S : Sampler Z) : ℕ → List Bool → Finset (List Bool)
  | 0, h => {h}
  | n + 1, h => if S.stop h then {h} else leaves S n (true :: h) ∪ leaves S n (false :: h)

@[simp] lemma leaves_zero (S : Sampler Z) (h : List Bool) : leaves S 0 h = {h} := rfl

lemma leaves_succ (S : Sampler Z) (n : ℕ) (h : List Bool) :
    leaves S (n + 1) h
      = if S.stop h then {h} else leaves S n (true :: h) ∪ leaves S n (false :: h) := rfl

lemma suffix_of_mem_leaves (S : Sampler Z) :
    ∀ (n : ℕ) (h l : List Bool), l ∈ leaves S n h → h <:+ l
  | 0, h, l, hl => by
      rw [leaves_zero, mem_singleton] at hl
      subst hl
      exact List.suffix_rfl
  | n + 1, h, l, hl => by
      rw [leaves_succ] at hl
      split_ifs at hl with hs
      · rw [mem_singleton] at hl
        subst hl
        exact List.suffix_rfl
      · rcases mem_union.1 hl with h1 | h1
        · exact (List.suffix_cons _ _).trans (suffix_of_mem_leaves S n _ _ h1)
        · exact (List.suffix_cons _ _).trans (suffix_of_mem_leaves S n _ _ h1)

/-- A leaf at which the sampler has not stopped has used all `n` rounds. -/
lemma length_of_mem_leaves (S : Sampler Z) :
    ∀ (n : ℕ) (h l : List Bool), l ∈ leaves S n h → ¬ S.stop l → l.length = h.length + n
  | 0, h, l, hl, _ => by
      rw [leaves_zero, mem_singleton] at hl
      subst hl
      rfl
  | n + 1, h, l, hl, hns => by
      rw [leaves_succ] at hl
      split_ifs at hl with hs
      · rw [mem_singleton] at hl
        subst hl
        exact absurd hs hns
      · rcases mem_union.1 hl with h1 | h1
        · have := length_of_mem_leaves S n _ _ h1 hns
          simp only [List.length_cons] at this
          omega
        · have := length_of_mem_leaves S n _ _ h1 hns
          simp only [List.length_cons] at this
          omega

lemma disjoint_leaves (S : Sampler Z) (n : ℕ) (h : List Bool) :
    Disjoint (leaves S n (true :: h)) (leaves S n (false :: h)) := by
  rw [Finset.disjoint_left]
  intro l h1 h2
  have s1 := suffix_of_mem_leaves S n _ _ h1
  have s2 := suffix_of_mem_leaves S n _ _ h2
  have h3 : (true :: h) <:+ (false :: h) := List.suffix_of_suffix_length_le s1 s2 (by simp)
  have h4 := h3.eq_of_length (by simp)
  simp at h4

lemma sum_leaves_succ (S : Sampler Z) (n : ℕ) (h : List Bool) (f : List Bool → ℝ) :
    ∑ l ∈ leaves S (n + 1) h, f l
      = if S.stop h then f h
        else ∑ l ∈ leaves S n (true :: h), f l + ∑ l ∈ leaves S n (false :: h), f l := by
  rw [leaves_succ]
  split_ifs
  · simp
  · exact sum_union (disjoint_leaves S n h)

/-- Optional stopping at a bounded time, as a finite induction: a weight that is conserved by
one further observation at every non-stopped history is conserved by stopping. -/
lemma sum_leaves_of_harmonic (S : Sampler Z) {g : List Bool → ℝ}
    (hg : ∀ h, ¬ S.stop h → g (true :: h) + g (false :: h) = g h) :
    ∀ (n : ℕ) (h : List Bool), ∑ l ∈ leaves S n h, g l = g h
  | 0, h => by simp
  | n + 1, h => by
      rw [sum_leaves_succ]
      split_ifs with hs
      · rfl
      · rw [sum_leaves_of_harmonic S hg n, sum_leaves_of_harmonic S hg n, hg h hs]

/-- Sub-harmonic weights have nondecreasing stopped sums. -/
lemma sum_leaves_mono (S : Sampler Z) {g : List Bool → ℝ}
    (hg : ∀ h, ¬ S.stop h → g h ≤ g (true :: h) + g (false :: h)) :
    ∀ (n : ℕ) (h : List Bool), ∑ l ∈ leaves S n h, g l ≤ ∑ l ∈ leaves S (n + 1) h, g l
  | 0, h => by
      rw [sum_leaves_succ S 0 h]
      split_ifs with hs
      · simp
      · simpa using hg h hs
  | n + 1, h => by
      rw [sum_leaves_succ S (n + 1) h, sum_leaves_succ S n h]
      split_ifs with hs
      · exact le_rfl
      · exact add_le_add (sum_leaves_mono S hg n _) (sum_leaves_mono S hg n _)

lemma lik_harmonic (S : Sampler Z) (μ : Z → ℝ) (h : List Bool) :
    lik S μ (true :: h) + lik S μ (false :: h) = lik S μ h := by
  simp only [lik, bern_true, bern_false]
  ring

lemma lik_pos (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) :
    ∀ l : List Bool, 0 < lik S μ l
  | [] => by simp [lik]
  | b :: h => mul_pos (lik_pos S hμ h) (bern_pos (hμ _).1 (hμ _).2 b)

/-- The weights `lik S μ` on the stopped histories of horizon `n` sum to one. -/
theorem sum_lik_leaves (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) :
    ∑ l ∈ leaves S n [], lik S μ l = 1 :=
  sum_leaves_of_harmonic S (fun h _ => lik_harmonic S μ h) n []

/-- `P_μ(H_{τ ∧ n} ∈ A)`: probability that the history stopped at `τ ∧ n` lies in `A`. -/
noncomputable def prob (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) (A : Set (List Bool)) : ℝ :=
  ∑ l ∈ leaves S n [], A.indicator (lik S μ) l

/-- Log-likelihood ratio of a history: the sum of the one-observation log ratios. -/
noncomputable def pathLLR (S : Sampler Z) (μ lam : Z → ℝ) : List Bool → ℝ
  | [] => 0
  | b :: h => pathLLR S μ lam h + log (bern (μ (S.next h)) b / bern (lam (S.next h)) b)

lemma log_lik_div (S : Sampler Z) {μ lam : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) :
    ∀ l : List Bool, log (lik S μ l / lik S lam l) = pathLLR S μ lam l
  | [] => by simp [lik, pathLLR]
  | b :: h => by
      have h1 := lik_pos S hμ h
      have h2 := lik_pos S hlam h
      have h3 := bern_pos (hμ (S.next h)).1 (hμ (S.next h)).2 b
      have h4 := bern_pos (hlam (S.next h)).1 (hlam (S.next h)).2 b
      rw [lik, lik, pathLLR, ← log_lik_div S hμ hlam h, mul_div_mul_comm,
        log_mul (div_pos h1 h2).ne' (div_pos h3 h4).ne']

section Counts

variable [DecidableEq Z]

/-- `N_z` along a history: the number of observations taken at terminal `z`. -/
def cnt (S : Sampler Z) (z : Z) : List Bool → ℕ
  | [] => 0
  | _ :: h => cnt S z h + if S.next h = z then 1 else 0

/-- `E_μ[N_z(τ ∧ n)]`. -/
noncomputable def expCount (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) (z : Z) : ℝ :=
  ∑ l ∈ leaves S n [], lik S μ l * (cnt S z l : ℝ)

/-- `E_μ[τ ∧ n]`. -/
noncomputable def expTime (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) : ℝ :=
  ∑ l ∈ leaves S n [], lik S μ l * (l.length : ℝ)

variable [Fintype Z]

lemma sum_cnt_cons (S : Sampler Z) (k : Z → ℝ) (b : Bool) (h : List Bool) :
    ∑ z, (cnt S z (b :: h) : ℝ) * k z = ∑ z, (cnt S z h : ℝ) * k z + k (S.next h) := by
  simp only [cnt, Nat.cast_add, add_mul, sum_add_distrib]
  congr 1
  simp

lemma sum_cnt (S : Sampler Z) : ∀ l : List Bool, ∑ z, cnt S z l = l.length
  | [] => by simp [cnt]
  | b :: h => by simp [cnt, sum_add_distrib, sum_cnt S h]

lemma sum_expCount (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) :
    ∑ z, expCount S μ n z = expTime S μ n := by
  unfold expCount expTime
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [← mul_sum, ← Nat.cast_sum, sum_cnt]

/-- **Wald identity for the stopped log-likelihood ratio** at a bounded horizon:
`E_μ[log(dP_μ/dP_λ)(H_{τ∧n})] = ∑_z E_μ[N_z(τ∧n)] kl(μ_z, λ_z)`. -/
theorem wald_identity (S : Sampler Z) {μ lam : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) (n : ℕ) :
    ∑ l ∈ leaves S n [], lik S μ l * log (lik S μ l / lik S lam l)
      = ∑ z, expCount S μ n z * bkl (μ z) (lam z) := by
  have h0 := sum_leaves_of_harmonic S
    (g := fun l => lik S μ l * (pathLLR S μ lam l - ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z)))
    (by
      intro h _
      simp only [lik, pathLLR, sum_cnt_cons, bern_true, bern_false]
      unfold bkl
      ring) n []
  simp only [lik, pathLLR, cnt, Nat.cast_zero, zero_mul, sum_const_zero, sub_self, mul_zero]
    at h0
  have h1 : ∑ l ∈ leaves S n [], lik S μ l * log (lik S μ l / lik S lam l)
      = ∑ l ∈ leaves S n [], lik S μ l * pathLLR S μ lam l :=
    sum_congr rfl fun l _ => by rw [log_lik_div S hμ hlam l]
  have h2 : ∑ z, expCount S μ n z * bkl (μ z) (lam z)
      = ∑ l ∈ leaves S n [], lik S μ l * ∑ z, (cnt S z l : ℝ) * bkl (μ z) (lam z) := by
    unfold expCount
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun l _ => sum_congr rfl fun z _ => by ring
  rw [h1, h2]
  simp only [mul_sub, sum_sub_distrib] at h0
  linarith

/-- Two-point Donsker--Varadhan bound for the stopped history at a bounded horizon. -/
lemma two_point_stopped (S : Sampler Z) {μ lam : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) (n : ℕ) (A : Set (List Bool)) (a b : ℝ) :
    a * prob S μ n A + b * (1 - prob S μ n A)
        - log (exp a * prob S lam n A + exp b * (1 - prob S lam n A))
      ≤ ∑ z, expCount S μ n z * bkl (μ z) (lam z) := by
  rw [← wald_identity S hμ hlam n]
  exact two_point_le_sum _ _ _ (fun l _ => lik_pos S hμ l) (fun l _ => lik_pos S hlam l)
    (sum_lik_leaves S μ n) (sum_lik_leaves S lam n) A a b

/-- **Stopped Bernoulli change of measure at a bounded horizon** (`lem:active-com` for the
stopping time `τ ∧ n`): for interior mean vectors `μ, λ` and every event `A` determined by the
history stopped at `τ ∧ n`,
`kl(P_μ(A), P_λ(A)) ≤ ∑_z E_μ[N_z(τ ∧ n)] kl(μ_z, λ_z)`. -/
theorem stopped_transport_finite (S : Sampler Z) {μ lam : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (hlam : ∀ z, 0 < lam z ∧ lam z < 1) (n : ℕ)
    (A : Set (List Bool)) :
    bkl (prob S μ n A) (prob S lam n A) ≤ ∑ z, expCount S μ n z * bkl (μ z) (lam z) := by
  rw [← wald_identity S hμ hlam n]
  exact bkl_le_sum_log _ _ _ (fun l _ => lik_pos S hμ l) (fun l _ => lik_pos S hlam l)
    (sum_lik_leaves S μ n) (sum_lik_leaves S lam n) A

end Counts

/-! ### Unbounded stopping times with finite expectation -/

section Limit

/-- Histories at which the sampler has stopped. -/
def stopSet (S : Sampler Z) : Set (List Bool) := {l | S.stop l = true}

lemma prob_nonneg (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    (A : Set (List Bool)) : 0 ≤ prob S μ n A :=
  sum_nonneg fun l _ => indicator_nonneg_of_pos A (lik_pos S hμ l)

lemma prob_le_one (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    (A : Set (List Bool)) : prob S μ n A ≤ 1 := by
  rw [← sum_lik_leaves S μ n]
  exact sum_le_sum fun l _ => indicator_le_of_pos A (lik_pos S hμ l)

lemma prob_mono_set (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    {A A' : Set (List Bool)} (h : A ⊆ A') : prob S μ n A ≤ prob S μ n A' := by
  refine sum_le_sum fun l _ => ?_
  have := (lik_pos S hμ l).le
  by_cases h1 : l ∈ A
  · simp [h1, h h1]
  · by_cases h2 : l ∈ A' <;> simp [h1, h2, this]

lemma prob_add_le_one (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    {A A' : Set (List Bool)} (h : Disjoint A A') : prob S μ n A + prob S μ n A' ≤ 1 := by
  rw [← sum_lik_leaves S μ n]
  unfold prob
  rw [← sum_add_distrib]
  refine sum_le_sum fun l _ => ?_
  have := (lik_pos S hμ l).le
  by_cases h1 : l ∈ A
  · have h2 : l ∉ A' := Set.disjoint_left.1 h h1
    simp [h1, h2]
  · by_cases h2 : l ∈ A' <;> simp [h1, h2, this]

/-- At horizon `n`: stopped in `A`, stopped outside `A`, or not yet stopped. -/
lemma prob_split (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) (A : Set (List Bool)) :
    prob S μ n (A ∩ stopSet S) + prob S μ n (Aᶜ ∩ stopSet S) + prob S μ n (stopSet S)ᶜ = 1 := by
  rw [← sum_lik_leaves S μ n]
  unfold prob
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  by_cases h1 : l ∈ A <;> by_cases h2 : l ∈ stopSet S <;> simp [h1, h2]

/-- `P_μ(τ ≤ n, H_τ ∈ A)` is nondecreasing in `n`. -/
lemma prob_stop_mono (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (A : Set (List Bool)) {m n : ℕ} (hmn : m ≤ n) :
    prob S μ m (A ∩ stopSet S) ≤ prob S μ n (A ∩ stopSet S) := by
  have hmono : Monotone fun n => prob S μ n (A ∩ stopSet S) := by
    refine monotone_nat_of_le_succ fun n => ?_
    refine sum_leaves_mono S (g := (A ∩ stopSet S).indicator (lik S μ)) (fun h hs => ?_) n []
    have h0 : h ∉ A ∩ stopSet S := fun hh => hs hh.2
    rw [Set.indicator_of_notMem h0]
    exact add_nonneg (indicator_nonneg_of_pos _ (lik_pos S hμ _))
      (indicator_nonneg_of_pos _ (lik_pos S hμ _))
  exact hmono hmn

lemma prob_pos_of_pos (S : Sampler Z) {μ lam : Z → ℝ} (hlam : ∀ z, 0 < lam z ∧ lam z < 1)
    (n : ℕ) (A : Set (List Bool)) (h : 0 < prob S μ n A) : 0 < prob S lam n A :=
  sum_indicator_pos_of_pos _ _ _ (fun l _ => lik_pos S hlam l) A h

/-- `P_μ(τ < ∞, H_τ ∈ A)`, the limit of the nondecreasing sequence `P_μ(τ ≤ n, H_τ ∈ A)`. -/
noncomputable def probInf (S : Sampler Z) (μ : Z → ℝ) (A : Set (List Bool)) : ℝ :=
  ⨆ n, prob S μ n (A ∩ stopSet S)

lemma prob_bddAbove (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (A : Set (List Bool)) : BddAbove (Set.range fun n => prob S μ n (A ∩ stopSet S)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact prob_le_one S hμ n _⟩

lemma tendsto_probInf (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (A : Set (List Bool)) :
    Tendsto (fun n => prob S μ n (A ∩ stopSet S)) atTop (𝓝 (probInf S μ A)) :=
  tendsto_atTop_ciSup (fun _ _ h => prob_stop_mono S hμ A h) (prob_bddAbove S hμ A)

lemma prob_le_probInf (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    (A : Set (List Bool)) : prob S μ n (A ∩ stopSet S) ≤ probInf S μ A :=
  le_ciSup (prob_bddAbove S hμ A) n

lemma probInf_nonneg (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (A : Set (List Bool)) : 0 ≤ probInf S μ A :=
  (prob_nonneg S hμ 0 _).trans (prob_le_probInf S hμ 0 A)

lemma probInf_le_one (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (A : Set (List Bool)) : probInf S μ A ≤ 1 :=
  ciSup_le fun n => prob_le_one S hμ n _

lemma probInf_mono (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    {A A' : Set (List Bool)} (h : A ⊆ A') : probInf S μ A ≤ probInf S μ A' :=
  ciSup_le fun n => (prob_mono_set S hμ n (Set.inter_subset_inter_left _ h)).trans
    (prob_le_probInf S hμ n A')

lemma probInf_add_le_one (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    {A A' : Set (List Bool)} (h : Disjoint A A') : probInf S μ A + probInf S μ A' ≤ 1 :=
  le_of_tendsto' ((tendsto_probInf S hμ A).add (tendsto_probInf S hμ A')) fun n =>
    prob_add_le_one S hμ n (h.mono Set.inter_subset_left Set.inter_subset_left)

/-- Absolute continuity of the stopped laws, first half. -/
lemma probInf_pos_of_pos (S : Sampler Z) {μ lam : Z → ℝ} (hlam : ∀ z, 0 < lam z ∧ lam z < 1)
    (A : Set (List Bool)) (h : 0 < probInf S μ A) : 0 < probInf S lam A := by
  have hex : ∃ n, 0 < prob S μ n (A ∩ stopSet S) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : probInf S μ A ≤ 0 := ciSup_le hcon
    linarith
  obtain ⟨n, hn⟩ := hex
  exact (prob_pos_of_pos S hlam n _ hn).trans_le (prob_le_probInf S hlam n A)

variable [DecidableEq Z]

lemma expCount_nonneg (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    (z : Z) : 0 ≤ expCount S μ n z :=
  sum_nonneg fun l _ => mul_nonneg (lik_pos S hμ l).le (Nat.cast_nonneg _)

lemma expTime_nonneg (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ) :
    0 ≤ expTime S μ n :=
  sum_nonneg fun l _ => mul_nonneg (lik_pos S hμ l).le (Nat.cast_nonneg _)

lemma expCount_mono (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (z : Z) :
    Monotone fun n => expCount S μ n z := by
  refine monotone_nat_of_le_succ fun n => ?_
  refine sum_leaves_mono S (g := fun l => lik S μ l * (cnt S z l : ℝ)) (fun h _ => ?_) n []
  have h1 := (lik_pos S hμ h).le
  have e : lik S μ (true :: h) * (cnt S z (true :: h) : ℝ)
        + lik S μ (false :: h) * (cnt S z (false :: h) : ℝ)
      = lik S μ h * ((cnt S z h : ℝ) + ((if S.next h = z then 1 else 0 : ℕ) : ℝ)) := by
    simp only [lik, cnt, bern_true, bern_false, Nat.cast_add]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Nat.cast_nonneg _)) h1

/-- Markov's inequality `n · P_μ(τ > n) ≤ E_μ[τ ∧ n]`. -/
lemma prob_not_stop_mul_le (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ) :
    prob S μ n (stopSet S)ᶜ * n ≤ expTime S μ n := by
  unfold prob expTime
  rw [sum_mul]
  refine sum_le_sum fun l hl => ?_
  by_cases h : l ∈ stopSet S
  · rw [Set.indicator_of_notMem (show l ∉ (stopSet S)ᶜ from fun hc => hc h), zero_mul]
    exact mul_nonneg (lik_pos S hμ l).le (Nat.cast_nonneg _)
  · have hlen := length_of_mem_leaves S n [] l hl h
    simp only [List.length_nil, zero_add] at hlen
    rw [Set.indicator_of_mem (show l ∈ (stopSet S)ᶜ from h), hlen]

variable [Fintype Z]

lemma expCount_le_expTime (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (n : ℕ)
    (z : Z) : expCount S μ n z ≤ expTime S μ n := by
  rw [← sum_expCount]
  exact single_le_sum (f := fun z => expCount S μ n z) (fun i _ => expCount_nonneg S hμ n i)
    (mem_univ z)

/-- `E_μ[N_z(τ)]`, the limit of the nondecreasing sequence `E_μ[N_z(τ ∧ n)]`. -/
noncomputable def expCountInf (S : Sampler Z) (μ : Z → ℝ) (z : Z) : ℝ :=
  ⨆ n, expCount S μ n z

/-- `E_μ[τ]`, the limit of the nondecreasing sequence `E_μ[τ ∧ n]`. -/
noncomputable def expTimeInf (S : Sampler Z) (μ : Z → ℝ) : ℝ := ⨆ n, expTime S μ n

lemma expCount_bddAbove (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {B : ℝ}
    (hB : ∀ n, expTime S μ n ≤ B) (z : Z) :
    BddAbove (Set.range fun n => expCount S μ n z) :=
  ⟨B, by rintro _ ⟨n, rfl⟩; exact (expCount_le_expTime S hμ n z).trans (hB n)⟩

lemma tendsto_expCountInf (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {B : ℝ}
    (hB : ∀ n, expTime S μ n ≤ B) (z : Z) :
    Tendsto (fun n => expCount S μ n z) atTop (𝓝 (expCountInf S μ z)) :=
  tendsto_atTop_ciSup (expCount_mono S hμ z) (expCount_bddAbove S hμ hB z)

lemma expCount_le_expCountInf (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    {B : ℝ} (hB : ∀ n, expTime S μ n ≤ B) (n : ℕ) (z : Z) :
    expCount S μ n z ≤ expCountInf S μ z :=
  le_ciSup (expCount_bddAbove S hμ hB z) n

lemma expCountInf_nonneg (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {B : ℝ}
    (hB : ∀ n, expTime S μ n ≤ B) (z : Z) : 0 ≤ expCountInf S μ z :=
  (expCount_nonneg S hμ 0 z).trans (expCount_le_expCountInf S hμ hB 0 z)

lemma tendsto_expTimeInf (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {B : ℝ}
    (hB : ∀ n, expTime S μ n ≤ B) :
    Tendsto (fun n => expTime S μ n) atTop (𝓝 (expTimeInf S μ)) := by
  refine tendsto_atTop_ciSup ?_ ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  intro m n hmn
  simp only [← sum_expCount]
  exact sum_le_sum fun z _ => expCount_mono S hμ z hmn

/-- `∑_z E_μ[N_z(τ)] = E_μ[τ]`. -/
lemma sum_expCountInf (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {B : ℝ}
    (hB : ∀ n, expTime S μ n ≤ B) : ∑ z, expCountInf S μ z = expTimeInf S μ :=
  tendsto_nhds_unique
    (tendsto_finsetSum _ fun z _ => tendsto_expCountInf S hμ hB z)
    ((tendsto_expTimeInf S hμ hB).congr fun n => (sum_expCount S μ n).symm)

/-- Absolute continuity of the stopped laws, second half; uses that a sampler with finite
expected time under `μ` stops `μ`-almost surely. -/
lemma probInf_lt_one_of_lt_one (S : Sampler Z) {μ lam : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) {B : ℝ} (hB : ∀ n, expTime S μ n ≤ B)
    (A : Set (List Bool)) (h : probInf S μ A < 1) : probInf S lam A < 1 := by
  have hex : ∃ n, 0 < prob S μ n (Aᶜ ∩ stopSet S) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hB0 : 0 ≤ B := (expTime_nonneg S hμ 0).trans (hB 0)
    have hd : 0 < 1 - probInf S μ A := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (B / (1 - probInf S μ A))
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hB0 hd.le) hn
    have h1 : B < n * (1 - probInf S μ A) := by rwa [div_lt_iff₀ hd] at hn
    have h2 := prob_not_stop_mul_le S hμ n
    have h3 := prob_split S μ n A
    have h4 := le_antisymm (hcon n) (prob_nonneg S hμ n _)
    have h5 := prob_le_probInf S hμ n A
    have h6 : (1 - probInf S μ A) * n ≤ prob S μ n (stopSet S)ᶜ * n :=
      mul_le_mul_of_nonneg_right (by linarith) hn0.le
    linarith [hB n]
  obtain ⟨n, hn⟩ := hex
  have hq := prob_pos_of_pos S hlam n _ hn
  have hle : ∀ m, prob S lam m (A ∩ stopSet S) ≤ 1 - prob S lam n (Aᶜ ∩ stopSet S) := by
    intro m
    have hs := prob_split S lam (max m n) A
    have h1 := prob_stop_mono S hlam A (le_max_left m n)
    have h2 := prob_stop_mono S hlam Aᶜ (le_max_right m n)
    have h3 := prob_nonneg S hlam (max m n) (stopSet S)ᶜ
    linarith
  have h7 : probInf S lam A ≤ 1 - prob S lam n (Aᶜ ∩ stopSet S) := ciSup_le hle
  linarith

/-- **Stopped Bernoulli change of measure** (`lem:active-com`).
For a deterministic adaptive sampler `S`, interior Bernoulli mean vectors `μ, λ`, finite
expected stopping time under `μ` (`hB`: `E_μ[τ ∧ n] ≤ B` for all `n`), and every event
`{τ < ∞, H_τ ∈ A}` determined by the stopped history,
`kl(P_μ(E), P_λ(E)) ≤ ∑_z E_μ[N_z(τ)] kl(μ_z, λ_z)`.
Almost-sure stopping under `λ` is not needed.  Probabilities and expectations of the unbounded
stopped process are the limits `probInf`, `expCountInf` of their bounded-horizon values. -/
theorem stopped_transport (S : Sampler Z) {μ lam : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) {B : ℝ} (hB : ∀ n, expTime S μ n ≤ B)
    (A : Set (List Bool)) :
    bkl (probInf S μ A) (probInf S lam A) ≤ ∑ z, expCountInf S μ z * bkl (μ z) (lam z) := by
  refine bkl_le_of_tendsto (tendsto_probInf S hμ A) (tendsto_probInf S hlam A)
    (probInf_nonneg S hμ A) (probInf_le_one S hμ A) (probInf_nonneg S hlam A)
    (probInf_le_one S hlam A) (probInf_pos_of_pos S hlam A)
    (probInf_lt_one_of_lt_one S hμ hlam hB A) fun n a b => ?_
  exact (two_point_stopped S hμ hlam n _ a b).trans (sum_le_sum fun z _ =>
    mul_le_mul_of_nonneg_right (expCount_le_expCountInf S hμ hB n z)
      (bkl_nonneg (hμ z).1.le (hμ z).2.le (hlam z).1 (hlam z).2))

/-- **Fixed-answer transportation bound for a sampler** (`transport_lower_bound` with its
hypothesis `htrans` derived from the sampler model).  If the event `A` (for instance
`{â = a}`) has probability at least `1 - δ` under `μ` and at most `δ` under every alternative
`λ ∈ Alt_ε(a)`, with `0 < δ ≤ 1/2`, then `kl(1-δ, δ) ≤ E_μ[τ] · C_a^ε(μ)`. -/
theorem transport_lower_bound_sampler [Nonempty Z] {Sa : Finset Z} (hSc : Saᶜ.Nonempty)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1)
    (S : Sampler Z) {B : ℝ} (hB : ∀ n, expTime S μ n ≤ B) (A : Set (List Bool)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hA : 1 - δ ≤ probInf S μ A)
    (hAlt : ∀ lam ∈ Alt Sa ε, probInf S lam A ≤ δ) :
    bkl (1 - δ) δ ≤ expTimeInf S μ * charRate Sa ε μ := by
  rw [← sum_expCountInf S hμ hB]
  refine transport_lower_bound hSc hε0 hε1 (fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩)
    (fun z => expCountInf_nonneg S hμ hB z) fun lam hlam => ?_
  have hp1 := probInf_le_one S hμ A
  have hx0 : 0 < probInf S lam A := probInf_pos_of_pos S hlam.1 A (by linarith)
  have h1 : bkl (1 - δ) δ ≤ bkl (probInf S μ A) δ :=
    bkl_mono_left hδ0 (by linarith) (by linarith) hA hp1
  have h2 : bkl (probInf S μ A) δ ≤ bkl (probInf S μ A) (probInf S lam A) :=
    bkl_mono_right (by linarith) hp1 hδ0 (by linarith) hx0 (by linarith [hAlt lam hlam])
      (mul_nonneg (sub_nonneg.2 (hAlt lam hlam)) (by linarith))
  exact (h1.trans h2).trans (stopped_transport S hμ hlam.1 hB A)

end Limit

/-! ### The tied-star lower bound for a sampler -/

/-- Supports of the star family indexed by the answer: `none ↦ S_A`, `some i ↦ S_{B_i}`. -/
def starSupp (N : ℕ) : Option (Fin N) → Finset (Fan N)
  | none => pairSupp N
  | some i => starB N i

lemma starSupp_nonempty (N : ℕ) : ∀ a, (starSupp N a).Nonempty
  | none => pairSupp_nonempty N
  | some i => starB_nonempty N i

/-- **Non-containment tied-star lower bound** (`thm:active-star-lb`, `eq:active-star-bound`)
for a deterministic adaptive sampler `S` with decision rule `dec` (a function of the stopped
history; `none` is the answer `A`, `some i` the answer `B_i`).
`hcorr` is `(ε,δ)`-correctness with almost-sure stopping: at every interior parameter the
sampler stops and returns an action of regret at most `ε` with probability at least `1 - δ`.
`hB` is finiteness of the expected stopping time at the tied star (if it is infinite the
manuscript's claim is vacuous).  The change of measure and the absolute-continuity facts
assumed by `tied_star_lower_bound` are derived from the model. -/
theorem tied_star_lower_bound_sampler {N : ℕ} {g ε δ : ℝ} (hε : 0 < ε) (hεg : ε ≤ g)
    (hg : g ≤ 1 / 4) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (S : Sampler (Fan N)) (dec : List Bool → Option (Fin N))
    (hcorr : ∀ lam : Fan N → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
      1 - δ ≤ probInf S lam
        {l | regret (starSupp N (dec l)) (starSupp_nonempty N (dec l)) lam ≤ ε})
    {B : ℝ} (hB : ∀ n, expTime S (starMu N g) n ≤ B) :
    bkl (1 / 2) δ * min (N / bkl (1 / 2 - g) (1 / 2 + ε)) (1 / bkl (1 / 2) (1 / 2 + ε))
      ≤ expTimeInf S (starMu N g) := by
  classical
  have hg0 := hε.trans_le hεg
  have hμ := starMu_interior (N := N) hg0 hg
  rw [← sum_expCountInf S hμ hB]
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
  refine tied_star_lower_bound hε hεg hg hδ0 hδ (expCountInf S (starMu N g))
    (fun z => expCountInf_nonneg S hμ hB z)
    (fun lam => if (∀ i, 0 < lam i ∧ lam i < 1) then probInf S lam {l | dec l = none} else 0)
    ?_ ?_ ?_ ?_ ?_
  · intro lam
    split_ifs with h
    · exact ⟨probInf_nonneg S h _, probInf_le_one S h _⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · intro lam hint hr
    simp only [ite_eq_left hint]
    have hdis : Disjoint {l : List Bool | dec l = none}
        {l | regret (starSupp N (dec l)) (starSupp_nonempty N (dec l)) lam ≤ ε} :=
      Set.disjoint_left.2 fun l hl hG => by
        rw [Set.mem_ofPred_eq, hregA lam (dec l) hl] at hG
        linarith
    have := probInf_add_le_one S hint hdis
    linarith [hcorr lam hint]
  · intro lam hint hr
    simp only [ite_eq_left hint]
    have hsub : {l | regret (starSupp N (dec l)) (starSupp_nonempty N (dec l)) lam ≤ ε}
        ⊆ {l : List Bool | dec l = none} := fun l hG => by
      by_contra hne
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 hne
      rw [Set.mem_ofPred_eq, hregB lam (dec l) i hi] at hG
      linarith [hr i]
    linarith [probInf_mono S hint hsub, hcorr lam hint]
  · intro lam hint
    simp only [ite_eq_left hint, ite_eq_left hμ]
    exact ⟨probInf_pos_of_pos S hint _, probInf_lt_one_of_lt_one S hμ hint hB _⟩
  · intro lam hint
    simp only [ite_eq_left hint, ite_eq_left hμ]
    exact stopped_transport S hμ hint hB _

/-! ### Reward-table model

The weights `lik S μ` on `leaves S n []` were introduced directly.  Here they are derived from a
product-measure model.  A table `x : Fin n → Z → Bool` holds, for each round `t < n` and each
terminal `z`, an outcome `x t z`; under `μ` the entries are independent with
`x t z ∼ Bernoulli(μ_z)`, so the table has probability `tableW μ n x = ∏_t ∏_z bern (μ z) (x t z)`
(the mass function of the product measure).  At round `t` the sampler observes the entry of row
`t` at the terminal it queries; `run S n h x` is the resulting history stopped at `τ ∧ n`. -/

section Table

variable [Fintype Z] [DecidableEq Z]

/-- Probability of a table under independent `Bernoulli(μ_z)` entries. -/
noncomputable def tableW (μ : Z → ℝ) (n : ℕ) (x : Fin n → Z → Bool) : ℝ :=
  ∏ t, ∏ z, bern (μ z) (x t z)

/-- History obtained from `h` by running the sampler on the table for at most `n` rounds. -/
def run (S : Sampler Z) : (n : ℕ) → List Bool → (Fin n → Z → Bool) → List Bool
  | 0, h, _ => h
  | n + 1, h, x => if S.stop h then h else run S n (x 0 (S.next h) :: h) (Fin.tail x)

lemma run_mem_leaves (S : Sampler Z) :
    ∀ (n : ℕ) (h : List Bool) (x : Fin n → Z → Bool), run S n h x ∈ leaves S n h
  | 0, h, _ => by simp [run]
  | n + 1, h, x => by
      rw [leaves_succ]
      by_cases hs : S.stop h = true
      · simp [run, hs]
      · have := run_mem_leaves S n (x 0 (S.next h) :: h) (Fin.tail x)
        rw [ite_eq_right hs]
        have hr : run S (n + 1) h x = run S n (x 0 (S.next h) :: h) (Fin.tail x) := by
          simp [run, hs]
        rw [hr]
        cases hb : x 0 (S.next h) <;> rw [hb] at this <;> simp [this]

/-- Marginal of one row on one coordinate. -/
lemma sum_row_marginal (μ : Z → ℝ) (a : Z) (T : Bool → ℝ) :
    ∑ r : Z → Bool, (∏ z, bern (μ z) (r z)) * T (r a) = ∑ b, bern (μ a) b * T b := by
  have h1 : ∀ r : Z → Bool, (∏ z, bern (μ z) (r z)) * T (r a)
      = ∏ z, (bern (μ z) (r z) * if z = a then T (r z) else 1) := by
    intro r
    rw [prod_mul_distrib]
    congr 1
    rw [prod_ite_eq' univ a (fun z => T (r z))]
    simp
  simp only [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Z => (univ : Finset Bool))
    (fun z b => bern (μ z) b * if z = a then T b else 1)
  rw [Fintype.piFinset_univ] at h2
  rw [← h2, prod_eq_single a]
  · simp
  · intro z _ hz
    simp [hz]
  · intro h
    exact absurd (mem_univ a) h

lemma sum_row (μ : Z → ℝ) : ∑ r : Z → Bool, ∏ z, bern (μ z) (r z) = 1 := by
  rcases isEmpty_or_nonempty Z with hE | ⟨⟨a⟩⟩
  · simp
  · have := sum_row_marginal μ a (fun _ => 1)
    simpa using this

lemma sum_cons {n : ℕ} (F : (Fin (n + 1) → Z → Bool) → ℝ) :
    ∑ x, F x = ∑ r : Z → Bool, ∑ x' : Fin n → Z → Bool, F (Fin.cons r x') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Z → Bool) _ _ fun _ => rfl).symm

lemma tableW_cons (μ : Z → ℝ) {n : ℕ} (r : Z → Bool) (x' : Fin n → Z → Bool) :
    tableW μ (n + 1) (Fin.cons r x') = (∏ z, bern (μ z) (r z)) * tableW μ n x' := by
  unfold tableW
  rw [Fin.prod_univ_succ]
  simp

lemma sum_tableW (μ : Z → ℝ) : ∀ n : ℕ, ∑ x, tableW μ n x = 1
  | 0 => by simp [tableW]
  | n + 1 => by
      rw [sum_cons]
      simp only [tableW_cons, ← mul_sum, sum_tableW μ n, mul_one]
      exact sum_row μ

/-- **The stopped history of the reward-table model has law `lik S μ` on `leaves S n []`.**
Started from a history `h`, the total probability of the tables whose stopped history is `l`,
multiplied by the weight of `h`, is `lik S μ l` if `l ∈ leaves S n h` and `0` otherwise. -/
theorem table_law_stopped_history_from (S : Sampler Z) (μ : Z → ℝ) :
    ∀ (n : ℕ) (h l : List Bool),
      lik S μ h * ∑ x : Fin n → Z → Bool, (if run S n h x = l then tableW μ n x else 0)
        = if l ∈ leaves S n h then lik S μ l else 0
  | 0, h, l => by
      by_cases hl : h = l
      · subst hl
        simp [run, tableW]
      · have hl' : l ≠ h := fun e => hl e.symm
        simp [run, hl, hl']
  | n + 1, h, l => by
      rw [sum_cons, leaves_succ]
      by_cases hs : S.stop h = true
      · simp only [run, hs, ite_true, tableW_cons]
        by_cases hl : h = l
        · subst hl
          simp only [ite_true, ← mul_sum, sum_tableW μ n, mul_one, sum_row μ, mem_singleton]
        · have hl' : l ≠ h := fun e => hl e.symm
          simp [hl, hl']
      · have hrun : ∀ (r : Z → Bool) (x' : Fin n → Z → Bool),
            run S (n + 1) h (Fin.cons r x') = run S n (r (S.next h) :: h) x' := by
          intro r x'
          simp [run, hs]
        have hrow : ∀ r : Z → Bool,
            ∑ x' : Fin n → Z → Bool,
                (if run S (n + 1) h (Fin.cons r x') = l then tableW μ (n + 1) (Fin.cons r x')
                  else 0)
              = (∏ z, bern (μ z) (r z))
                * (fun b : Bool => ∑ x' : Fin n → Z → Bool,
                    (if run S n (b :: h) x' = l then tableW μ n x' else 0)) (r (S.next h)) := by
          intro r
          beta_reduce
          rw [mul_sum]
          refine sum_congr rfl fun x' _ => ?_
          rw [hrun, tableW_cons]
          split_ifs <;> simp
        simp only [hrow]
        rw [sum_row_marginal μ (S.next h)
          (fun b => ∑ x' : Fin n → Z → Bool, if run S n (b :: h) x' = l then tableW μ n x' else 0),
          Fintype.sum_bool, ite_eq_right hs, mul_add]
        have i1 := table_law_stopped_history_from S μ n (true :: h) l
        have i2 := table_law_stopped_history_from S μ n (false :: h) l
        simp only [lik, bern_true, bern_false] at i1 i2
        simp only [bern_true, bern_false]
        have hd := Finset.disjoint_left.1 (disjoint_leaves S n h)
        by_cases m1 : l ∈ leaves S n (true :: h)
        · have m2 : l ∉ leaves S n (false :: h) := hd m1
          rw [ite_eq_left m1] at i1
          rw [ite_eq_right m2] at i2
          rw [ite_eq_left (mem_union_left _ m1)]
          linarith
        · rw [ite_eq_right m1] at i1
          by_cases m2 : l ∈ leaves S n (false :: h)
          · rw [ite_eq_left m2] at i2
            rw [ite_eq_left (mem_union_right _ m2)]
            linarith
          · rw [ite_eq_right m2] at i2
            rw [ite_eq_right (by simp [m1, m2])]
            linarith

/-- The law of the history stopped at `τ ∧ n` in the reward-table model: the probability of the
tables producing the history `l` is `lik S μ l` if `l` is a stopped history of horizon `n` and
`0` otherwise. -/
theorem table_law_stopped_history (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) (l : List Bool) :
    ∑ x : Fin n → Z → Bool, (if run S n [] x = l then tableW μ n x else 0)
      = if l ∈ leaves S n [] then lik S μ l else 0 := by
  have := table_law_stopped_history_from S μ n [] l
  simpa [lik] using this

/-- Consequently `prob S μ n A` is the table probability of `{x | run S n [] x ∈ A}`. -/
theorem prob_eq_table (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) (A : Set (List Bool)) :
    prob S μ n A = ∑ x : Fin n → Z → Bool, (run S n [] ⁻¹' A).indicator (tableW μ n) x := by
  classical
  have hx : ∀ x : Fin n → Z → Bool, (run S n [] ⁻¹' A).indicator (tableW μ n) x
      = ∑ l ∈ leaves S n [],
          if run S n [] x = l then A.indicator (fun _ => tableW μ n x) l else 0 := by
    intro x
    rw [sum_ite_eq (leaves S n []) (run S n [] x), ite_eq_left (run_mem_leaves S n [] x)]
    by_cases hA : run S n [] x ∈ A <;> simp [hA]
  simp only [hx]
  rw [sum_comm]
  unfold prob
  refine sum_congr rfl fun l hl => ?_
  have ht := table_law_stopped_history S μ n l
  rw [ite_eq_left hl] at ht
  by_cases hA : l ∈ A
  · simp only [Set.indicator_of_mem hA]
    exact ht.symm
  · simp [hA]

end Table

end Stopped

end JointRootCert
