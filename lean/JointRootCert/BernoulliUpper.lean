/-
The matching upper bound of the Bernoulli information limit.

Manuscript result covered: `thm:ast-main` "One inside witness and Bernoulli information limit",
the clause "a likelihood-certified tracker attains equality" (`app:ast-regularity`,
`app:ast-sequential`).  Together with `BernoulliLimit.lean` (lower bound, certificate) this
gives the limit `lim_{δ↓0} E_μ τ_δ / log(1/δ) = 1 / C_*^ε(μ)`:

* `ast_main` (`0 < ε < 1`, supports covering `Z`) and `ast_main_exact` (`ε = 0` on
  `𝒟_0 = {Γ > 0}`): existence of a `δ`-correct procedure with finite expected stopping time
  attaining the limit; `ast_main_labels` is the same statement for the explicit sampler
  `astSampler O δ` over an abstract system of witness labels.

The proof follows the manuscript's construction:

1. oracle `eq:ast-oracle`: the witness game `witF` and its rate `witC` with their modulus,
   superadditivity and the identification `max_b C_b = C_a` (`witC_eq_charRate`); the contract
   is the structure `AllocOracle`; `exists_witness_mesh` and `exists_allocOracle` build an
   oracle from a finite simplex mesh;
2. the procedure `astSampler` (epochs `t_k = 2^k - 1`, schedules `h_k, ξ_k, γ_k`, sticky label
   `eq:ast-sticky`, the within-epoch merge rule, tests at square times); tracking within an
   epoch (`epoch_track`), multi-epoch tracking `eq:ast-tracking` (`tracking_any`) and the floor
   `eq:ast-floor` (`count_floor`);
3. concentration of the empirical means along the run (`Stopped.prob_dev_le`,
   `Stopped.prob_bad_le`, `estimation_tail`), from Hoeffding's lemma for one Bernoulli
   observation and Ville's inequality on the tree of stopped histories;
4. label locking and the allocation rate `eq:ast-allocation-rate` (`plan_lock`,
   `eventually_epoch_good`) and the power bound `eq:ast-power` (`stop_of_good`);
5. the tail of the stopping time, finite expectation and the upper rate
   (`prob_not_stopped_le`, `expTime_le`, `ast_upper_rate`);
6. correctness (`ast_correct`, `ast_returns_correct`) and the limit (`ast_main_labels`).

Model and deviations from the manuscript (none changes the statement proved):

* the sampler is a deterministic function of the outcome history (`Stopped.Sampler`);
  probabilities and expectations are those of the stopped history, as in
  `StoppedProcess.lean`;
* the witness game of a label `(a, j)` is defined as the information rate of the allocation
  collapsed onto `j` inside `S(a)`; it is the manuscript's `min_z F_ε(p_j,p_z;w_j,w_z)` at
  interior means (`witF_eq_starVal`); at empirical vectors with a coordinate equal to `0` or
  `1` this identification is not proved (it concerns only what the oracle optimizes there);
* the oracle of `exists_allocOracle` evaluates the witness game exactly on a finite simplex
  mesh; the threshold mesh and the rational enclosures of logarithms are not modelled, and the
  certificate is tested with exact values of `G` and `β` (no `±1` enclosures);
* labels are ordered by a fixed enumeration, and ties of the merge rule are broken by a fixed
  choice function;
* the estimation tail is `∑_{s=u}^{q} 2M exp(-√s/(4M))`, without the factor `s` of the
  manuscript's `R_M` (no union over intrinsic counts is needed); `t^{-1/8}` and `t^{3/4}` are
  written with nested square roots (`rad_eq_rpow`);
* `eq:ast-power` is proved in the form `(u² - (2u+1))(C - η) - u² η` for an arbitrary `η > 0`
  and `u` large, rather than with the explicit sequences `ā(u)` and `ω_ε(t^{-1/8} + d_M(t))`.
-/
import JointRootCert.BernoulliLimit
import JointRootCert.Coverage

namespace JointRootCert

open Finset Real Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Stopped

/-! ### Tools on the tree of stopped histories -/

section TreeTools

variable {Z : Type*}

/-- `ever P l` holds exactly when `P` holds at some earlier history of the run (a suffix of the
list, since the most recent observation comes first). -/
lemma ever_iff_exists_suffix {P : List Bool → Prop} :
    ∀ {l : List Bool}, ever P l ↔ ∃ h, h <:+ l ∧ P h
  | [] => by
      constructor
      · intro h
        exact ⟨[], List.suffix_rfl, h⟩
      · rintro ⟨h, hs, hP⟩
        rw [List.suffix_nil] at hs
        subst hs
        exact hP
  | b :: l => by
      constructor
      · rintro (h | h)
        · exact ⟨b :: l, List.suffix_rfl, h⟩
        · obtain ⟨g, hg, hP⟩ := ever_iff_exists_suffix.1 h
          exact ⟨g, hg.trans (List.suffix_cons _ _), hP⟩
      · rintro ⟨g, hg, hP⟩
        rcases List.suffix_cons_iff.1 hg with h1 | h1
        · subst h1
          exact Or.inl hP
        · exact Or.inr (ever_iff_exists_suffix.2 ⟨g, h1, hP⟩)

/-- A stopped history of horizon `n` has no stopped proper prefix. -/
lemma not_stop_of_mem_leaves (S : Sampler Z) :
    ∀ (n : ℕ) (h l : List Bool), l ∈ leaves S n h → ∀ g : List Bool, h <:+ g → g <:+ l →
      g ≠ l → S.stop g = false
  | 0, h, l, hl, g, hhg, hgl, hne => by
      rw [leaves_zero, mem_singleton] at hl
      subst hl
      exact absurd (hgl.eq_of_length (le_antisymm hgl.length_le hhg.length_le)) hne
  | n + 1, h, l, hl, g, hhg, hgl, hne => by
      rw [leaves_succ] at hl
      by_cases hs : S.stop h = true
      · rw [ite_eq_left hs, mem_singleton] at hl
        subst hl
        exact absurd (hgl.eq_of_length (le_antisymm hgl.length_le hhg.length_le)) hne
      · rw [ite_eq_right hs] at hl
        have hs' : S.stop h = false := by simpa using hs
        have key : ∀ b : Bool, l ∈ leaves S n (b :: h) → S.stop g = false := by
          intro b hb
          have hbl := suffix_of_mem_leaves S n _ _ hb
          rcases List.suffix_or_suffix_of_suffix hgl hbl with h1 | h1
          · rcases List.suffix_cons_iff.1 h1 with h2 | h2
            · subst h2
              exact not_stop_of_mem_leaves S n _ l hb _ List.suffix_rfl hgl hne
            · have : g = h := h2.eq_of_length (le_antisymm h2.length_le hhg.length_le)
              rw [this]
              exact hs'
          · exact not_stop_of_mem_leaves S n _ l hb g h1 hgl hne
        rcases mem_union.1 hl with h1 | h1
        · exact key true h1
        · exact key false h1

/-- `E[τ ∧ (n+1)] = E[τ ∧ n] + P(τ > n)`, from a general starting history. -/
lemma sum_leaves_length_succ (S : Sampler Z) (μ : Z → ℝ) :
    ∀ (n : ℕ) (h : List Bool),
      ∑ l ∈ leaves S (n + 1) h, lik S μ l * (l.length : ℝ)
        = ∑ l ∈ leaves S n h, lik S μ l * (l.length : ℝ)
          + ∑ l ∈ leaves S n h, (stopSet S)ᶜ.indicator (lik S μ) l
  | 0, h => by
      rw [sum_leaves_succ]
      by_cases hs : S.stop h = true
      · have hh : h ∉ (stopSet S)ᶜ := fun hc => hc hs
        simp [hs, Set.indicator_of_notMem hh]
      · have hh : h ∈ (stopSet S)ᶜ := hs
        simp only [hs, leaves_zero, sum_singleton, Set.indicator_of_mem hh, lik, bern_true,
          bern_false, List.length_cons, Nat.cast_add, Nat.cast_one]
        simp only [Bool.false_eq_true, ite_false]
        ring
  | n + 1, h => by
      rw [sum_leaves_succ S (n + 1) h, sum_leaves_succ S n h, sum_leaves_succ S n h]
      by_cases hs : S.stop h = true
      · have hh : h ∉ (stopSet S)ᶜ := fun hc => hc hs
        simp [hs, Set.indicator_of_notMem hh]
      · simp only [hs, Bool.false_eq_true, ite_false]
        rw [sum_leaves_length_succ S μ n (true :: h), sum_leaves_length_succ S μ n (false :: h)]
        ring

variable [DecidableEq Z]

lemma expTime_succ (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) :
    expTime S μ (n + 1) = expTime S μ n + prob S μ n (stopSet S)ᶜ :=
  sum_leaves_length_succ S μ n []

/-- `E[τ ∧ n] = ∑_{T < n} P(τ > T)`. -/
lemma expTime_eq_sum (S : Sampler Z) (μ : Z → ℝ) :
    ∀ n : ℕ, expTime S μ n = ∑ T ∈ range n, prob S μ T (stopSet S)ᶜ
  | 0 => by simp [expTime, lik]
  | n + 1 => by rw [expTime_succ, sum_range_succ, expTime_eq_sum S μ n]

/-- Probabilities only depend on the event restricted to the stopped histories. -/
lemma prob_inter_leaves (S : Sampler Z) (μ : Z → ℝ) (n : ℕ) (A : Set (List Bool)) :
    prob S μ n A = prob S μ n (A ∩ ↑(leaves S n [])) := by
  unfold prob
  refine sum_congr rfl fun l hl => ?_
  by_cases hs : l ∈ A
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show l ∈ A ∩ _ from ⟨hs, hl⟩)]
  · rw [Set.indicator_of_notMem hs,
      Set.indicator_of_notMem (show l ∉ A ∩ _ from fun h => hs h.1)]

end TreeTools

/-! ### Hoeffding concentration along an adaptive run -/

section HoeffdingTwoPoint

open MeasureTheory ProbabilityTheory

/-- **Hoeffding's lemma for one Bernoulli observation**:
`p e^{t(1-p)} + (1-p) e^{-tp} ≤ e^{t²/8}`. -/
lemma bernoulli_mgf_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    p * exp (t * (1 - p)) + (1 - p) * exp (t * (0 - p)) ≤ exp (t ^ 2 / 8) := by
  let ν : Measure Bool :=
    ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false
  have hν : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    simp only [ν, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp0 (by linarith)]
    simp
  let X : Bool → ℝ := fun b => (if b then 1 else 0) - p
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂ν = p * f true + (1 - p) * f false := by
    intro f
    rw [integral_fintype Integrable.of_finite]
    have e1 : ν.real {true} = p := by
      simp [ν, Measure.real, ENNReal.toReal_ofReal hp0]
    have e2 : ν.real {false} = 1 - p := by
      simp [ν, Measure.real, ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 - p by linarith)]
    simp [e1, e2]
  have hmean : ν[X] = 0 := by
    rw [hint]
    simp only [X]
    simp
    ring
  have hb : ∀ᵐ b ∂ν, X b ∈ Set.Icc (0 - p) (1 - p) := by
    refine Filter.Eventually.of_forall fun b => ?_
    cases b <;> simp [X]
  have h := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := ν) (X := X)
    (measurable_of_finite X).aemeasurable hb hmean).mgf_le t
  have e : mgf X ν t = p * exp (t * (1 - p)) + (1 - p) * exp (t * (0 - p)) := by
    unfold mgf
    rw [hint]
    simp [X]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  have : ‖(1 - p) - (0 - p)‖ = 1 := by simp
  push_cast
  rw [this]
  ring

end HoeffdingTwoPoint

section Concentration

variable {Z : Type*} [DecidableEq Z]

/-- Hoeffding exponential process of terminal `i`:
`exp(λ (S_i - μ_i N_i) - λ² N_i / 8)`. -/
noncomputable def hoefW (S : Sampler Z) (μ : Z → ℝ) (i : Z) (lam : ℝ) (h : List Bool) : ℝ :=
  exp (lam * ((scnt S i h : ℝ) - μ i * (cnt S i h : ℝ)) - lam ^ 2 / 8 * (cnt S i h : ℝ))

lemma hoefW_nil (S : Sampler Z) (μ : Z → ℝ) (i : Z) (lam : ℝ) : hoefW S μ i lam [] = 1 := by
  simp [hoefW, cnt, scnt]

/-- The Hoeffding process is a supermartingale under `μ` for every adaptive sampling rule. -/
lemma hoefW_super (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (i : Z) (lam : ℝ)
    (h : List Bool) :
    lik S μ (true :: h) * hoefW S μ i lam (true :: h)
        + lik S μ (false :: h) * hoefW S μ i lam (false :: h)
      ≤ lik S μ h * hoefW S μ i lam h := by
  by_cases he : S.next h = i
  · have e1 : hoefW S μ i lam (true :: h)
        = hoefW S μ i lam h * (exp (lam * (1 - μ i)) * exp (-(lam ^ 2 / 8))) := by
      unfold hoefW
      rw [← exp_add, ← exp_add]
      congr 1
      simp [cnt, scnt, he]
      ring
    have e2 : hoefW S μ i lam (false :: h)
        = hoefW S μ i lam h * (exp (lam * (0 - μ i)) * exp (-(lam ^ 2 / 8))) := by
      unfold hoefW
      rw [← exp_add, ← exp_add]
      congr 1
      simp [cnt, scnt, he]
      ring
    have key := bernoulli_mgf_le (hμ i).1.le (hμ i).2.le lam
    have hE : exp (lam ^ 2 / 8) * exp (-(lam ^ 2 / 8)) = 1 := by
      rw [← exp_add]
      simp
    have h1 : (μ i * exp (lam * (1 - μ i)) + (1 - μ i) * exp (lam * (0 - μ i)))
        * exp (-(lam ^ 2 / 8)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right key (exp_pos (-(lam ^ 2 / 8))).le
      rwa [hE] at this
    have hW : 0 ≤ lik S μ h * hoefW S μ i lam h :=
      mul_nonneg (lik_pos S hμ h).le (exp_pos _).le
    rw [e1, e2]
    simp only [lik, bern_true, bern_false, he]
    calc lik S μ h * μ i * (hoefW S μ i lam h * (exp (lam * (1 - μ i)) * exp (-(lam ^ 2 / 8))))
          + lik S μ h * (1 - μ i)
            * (hoefW S μ i lam h * (exp (lam * (0 - μ i)) * exp (-(lam ^ 2 / 8))))
        = lik S μ h * hoefW S μ i lam h
          * ((μ i * exp (lam * (1 - μ i)) + (1 - μ i) * exp (lam * (0 - μ i)))
            * exp (-(lam ^ 2 / 8))) := by ring
      _ ≤ lik S μ h * hoefW S μ i lam h * 1 := mul_le_mul_of_nonneg_left h1 hW
      _ = lik S μ h * hoefW S μ i lam h := mul_one _
  · have e : ∀ b : Bool, hoefW S μ i lam (b :: h) = hoefW S μ i lam h := by
      intro b
      simp [hoefW, cnt, scnt, he]
    rw [e, e, ← add_mul, lik_harmonic]

/-- **Deviation of one empirical mean at one time, under adaptive counts.**  If every history
of length `s` has at least `m > 0` observations of terminal `i`, then the probability that the
run passes through a history of length `s` at which `|μ̂_i - μ_i| > r` is at most
`2 exp(-2 r² m)`.  No union over the possible counts is needed. -/
lemma prob_dev_le (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (i : Z) (s : ℕ)
    {r m : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hfloor : ∀ h : List Bool, h.length = s → m ≤ (cnt S i h : ℝ)) (n : ℕ) :
    prob S μ n {l | ever (fun h => h.length = s ∧ r < |emp S i h - μ i|) l}
      ≤ 2 * exp (-(2 * r ^ 2 * m)) := by
  set c : ℝ := exp (2 * r ^ 2 * m) with hc
  have hcpos : 0 < c := exp_pos _
  have hsub : ∀ l ∈ {l | ever (fun h => h.length = s ∧ r < |emp S i h - μ i|) l},
      ∃ q ∈ (univ : Finset Bool),
        l ∈ {l | ever (fun h => c ≤ hoefW S μ i (if q then 4 * r else -(4 * r)) h) l} := by
    intro l hl
    obtain ⟨h, hsuf, hlen, hdev⟩ := ever_iff_exists_suffix.1 hl
    have hN := hfloor h hlen
    have hNpos : (0 : ℝ) < cnt S i h := hm.trans_le hN
    have hne : cnt S i h ≠ 0 := by
      intro h0
      rw [h0] at hNpos
      simp at hNpos
    have hemp : emp S i h = (scnt S i h : ℝ) / (cnt S i h : ℝ) := by simp [emp, hne]
    have hmN : 2 * r ^ 2 * m ≤ 2 * r ^ 2 * (cnt S i h : ℝ) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    rcases lt_abs.1 hdev with h1 | h1
    · refine ⟨true, mem_univ _, ever_iff_exists_suffix.2 ⟨h, hsuf, ?_⟩⟩
      have hx : r * (cnt S i h : ℝ) < (scnt S i h : ℝ) - μ i * (cnt S i h : ℝ) := by
        rw [hemp, lt_sub_iff_add_lt, lt_div_iff₀ hNpos] at h1
        linarith
      have h4 := mul_le_mul_of_nonneg_left hx.le (show (0 : ℝ) ≤ 4 * r by positivity)
      simp only [ite_true, hoefW, hc]
      refine exp_le_exp.2 ?_
      nlinarith
    · refine ⟨false, mem_univ _, ever_iff_exists_suffix.2 ⟨h, hsuf, ?_⟩⟩
      have hx : r * (cnt S i h : ℝ) < μ i * (cnt S i h : ℝ) - (scnt S i h : ℝ) := by
        rw [hemp, neg_sub, lt_sub_iff_add_lt, add_comm, ← lt_sub_iff_add_lt,
          div_lt_iff₀ hNpos] at h1
        linarith
      have h4 := mul_le_mul_of_nonneg_left hx.le (show (0 : ℝ) ≤ 4 * r by positivity)
      simp only [Bool.false_eq_true, ite_false, hoefW, hc]
      refine exp_le_exp.2 ?_
      nlinarith
  refine (prob_le_sum_of_subset S hμ n (univ : Finset Bool) _ _ hsub).trans ?_
  have hterm : ∀ q : Bool,
      prob S μ n {l | ever (fun h => c ≤ hoefW S μ i (if q then 4 * r else -(4 * r)) h) l}
        ≤ exp (-(2 * r ^ 2 * m)) := by
    intro q
    have hv := ville_tree S hμ (M := hoefW S μ i (if q then 4 * r else -(4 * r)))
      (fun h => (exp_pos _).le) (fun h => hoefW_super S hμ i _ h) hcpos n
    rw [hoefW_nil] at hv
    rw [exp_neg, ← hc, ← one_div, le_div_iff₀ hcpos]
    linarith
  calc ∑ q : Bool,
        prob S μ n {l | ever (fun h => c ≤ hoefW S μ i (if q then 4 * r else -(4 * r)) h) l}
      ≤ ∑ _q : Bool, exp (-(2 * r ^ 2 * m)) := sum_le_sum fun q _ => hterm q
    _ = 2 * exp (-(2 * r ^ 2 * m)) := by simp

variable [Fintype Z]

/-- **Uniform-in-time estimation tail.**  If at every time `s ∈ [u, q]` every terminal has at
least `m s > 0` observations, then the probability that some empirical mean deviates by more
than `r s` at some time `s ∈ [u, q]` of the run is at most
`∑_{s=u}^{q} 2 M exp(-2 r_s² m_s)`. -/
lemma prob_bad_le (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (u q : ℕ)
    (r m : ℕ → ℝ) (hr : ∀ s ∈ Icc u q, 0 < r s) (hm : ∀ s ∈ Icc u q, 0 < m s)
    (hfloor : ∀ s ∈ Icc u q, ∀ (i : Z) (h : List Bool), h.length = s → m s ≤ (cnt S i h : ℝ))
    (n : ℕ) :
    prob S μ n {l | ever (fun h => u ≤ h.length ∧ h.length ≤ q ∧
        ∃ i, r h.length < |emp S i h - μ i|) l}
      ≤ ∑ s ∈ Icc u q, (Fintype.card Z : ℝ) * (2 * exp (-(2 * r s ^ 2 * m s))) := by
  have hsub : ∀ l ∈ {l | ever (fun h => u ≤ h.length ∧ h.length ≤ q ∧
        ∃ i, r h.length < |emp S i h - μ i|) l},
      ∃ x ∈ (Icc u q) ×ˢ (univ : Finset Z),
        l ∈ {l | ever (fun h => h.length = x.1 ∧ r x.1 < |emp S x.2 h - μ x.2|) l} := by
    intro l hl
    obtain ⟨h, hsuf, hu, hq, i, hi⟩ := ever_iff_exists_suffix.1 hl
    exact ⟨(h.length, i), mem_product.2 ⟨mem_Icc.2 ⟨hu, hq⟩, mem_univ _⟩,
      ever_iff_exists_suffix.2 ⟨h, hsuf, rfl, hi⟩⟩
  refine (prob_le_sum_of_subset S hμ n _ _ _ hsub).trans ?_
  rw [sum_product]
  refine sum_le_sum fun s hs => ?_
  calc ∑ i : Z, prob S μ n {l | ever (fun h => h.length = s ∧ r s < |emp S i h - μ i|) l}
      ≤ ∑ _i : Z, 2 * exp (-(2 * r s ^ 2 * m s)) :=
        sum_le_sum fun i _ => prob_dev_le S hμ i s (hr s hs) (hm s hs) (hfloor s hs i) n
    _ = (Fintype.card Z : ℝ) * (2 * exp (-(2 * r s ^ 2 * m s))) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

end Concentration

end Stopped

/-! ### The witness game and the allocation oracle (`app:ast-regularity`, `eq:ast-oracle`) -/

section WitnessGame

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- Witness game `f_b(p,w)` for the label `b = (a,j)` with support `S = S(a)` and witness
`j ∈ S`: the information rate of the allocation that keeps, inside `S`, only the weight of `j`.
At interior means this is `min_{z ∉ S} F_ε(p_j, p_z; w_j, w_z)` (`witF_eq_starVal`). -/
noncomputable def witF (S : Finset Z) (j : Z) (ε : ℝ) (p w : Z → ℝ) : ℝ :=
  infoRate S ε (collapse S j (w j) w) p

/-- Witness rate `C_b(p) = sup_{w ∈ Δ_M} f_b(p,w)`. -/
noncomputable def witC (S : Finset Z) (j : Z) (ε : ℝ) (p : Z → ℝ) : ℝ :=
  sSup ((fun w => witF S j ε p w) '' simplex Z)

lemma collapse_self_le (S : Finset Z) (j : Z) {w : Z → ℝ} (hw : ∀ i, 0 ≤ w i) (i : Z) :
    collapse S j (w j) w i ≤ w i := by
  unfold collapse
  split_ifs with h1 h2
  · rw [h2]
  · exact hw i
  · exact le_rfl

lemma collapse_self_sum_le (S : Finset Z) (j : Z) {w : Z → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∑ i, collapse S j (w j) w i ≤ ∑ i, w i :=
  sum_le_sum fun i _ => collapse_self_le S j hw i

lemma collapse_self_abs_sub (S : Finset Z) (j : Z) (w w' : Z → ℝ) (i : Z) :
    |collapse S j (w j) w i - collapse S j (w' j) w' i| ≤ |w i - w' i| := by
  unfold collapse
  split_ifs with h1 h2
  · rw [h2]
  · simp
  · exact le_rfl

lemma collapse_self_lin (S : Finset Z) (j : Z) (a b : ℝ) (w w' : Z → ℝ) :
    collapse S j (a * w j + b * w' j) (fun i => a * w i + b * w' i)
      = fun i => a * collapse S j (w j) w i + b * collapse S j (w' j) w' i := by
  funext i
  unfold collapse
  split_ifs <;> ring

variable {S : Finset Z} {ε : ℝ}

lemma witF_nonneg (j : Z) {p w : Z → ℝ} (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    0 ≤ witF S j ε p w :=
  infoRate_nonneg (collapse_nonneg (hw j) hw) hp

lemma witF_le_mul_log (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z) {p w : Z → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    witF S j ε p w ≤ (∑ i, w i) * log (4 / (1 - ε)) :=
  (infoRate_le_mul_log hSc hε0 hε1 (collapse_nonneg (hw j) hw) hp).trans
    (mul_le_mul_of_nonneg_right (collapse_self_sum_le S j hw) (log_four_div_nonneg hε0 hε1))

/-- The witness game is superadditive (concave and homogeneous) in the weights. -/
lemma witF_superadd (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z) {p w w' : Z → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw' : ∀ i, 0 ≤ w' i) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * witF S j ε p w + b * witF S j ε p w'
      ≤ witF S j ε p (fun i => a * w i + b * w' i) := by
  have h := infoRate_concave (S := S) hSc hε0 hε1 (v := collapse S j (w j) w)
    (v' := collapse S j (w' j) w') (collapse_nonneg (hw j) hw)
    (collapse_nonneg (hw' j) hw') hp ha hb
  unfold witF
  rw [collapse_self_lin]
  exact h

lemma witF_smul (j : Z) (p w : Z → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    witF S j ε p (fun i => a * w i) = a * witF S j ε p w := by
  unfold witF
  have h := collapse_self_lin S j a 0 w w
  simp only [zero_mul, add_zero] at h
  rw [h, infoRate_smul S ε _ p ha]

/-- One-sided modulus of the witness game (`eq:ast-modulus`, second inequality), for means in
`[0,1]^M` and weights of total mass at most one. -/
lemma witF_le_add_omega (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z)
    {w w' p p' : Z → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1) (hw' : ∀ i, 0 ≤ w' i)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hp' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1) {r s : ℝ}
    (hr : ∀ i, |p i - p' i| ≤ r) (hs : ∑ i, |w i - w' i| ≤ s) (hs0 : 0 ≤ s)
    (hd0 : 0 < r + s) (hd : r + s ≤ 1 / 2) :
    witF S j ε p' w' ≤ witF S j ε p w + omega ε (r + s) :=
  infoRate_le_add_omega hSc hε0 hε1 (collapse_nonneg (hw j) hw)
    ((collapse_self_sum_le S j hw).trans hw1) (collapse_nonneg (hw' j) hw') hp hp' hr
    ((sum_le_sum fun i _ => collapse_self_abs_sub S j w w' i).trans hs) hs0 hd0 hd

lemma witC_bddAbove (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z) {p : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : BddAbove ((fun w => witF S j ε p w) '' simplex Z) :=
  ⟨log (4 / (1 - ε)), by
    rintro _ ⟨w, hw, rfl⟩
    have := witF_le_mul_log hSc hε0 hε1 j hw.1 hp
    rwa [hw.2, one_mul] at this⟩

lemma witF_le_witC (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z) {p w : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hw : w ∈ simplex Z) : witF S j ε p w ≤ witC S j ε p :=
  le_csSup (witC_bddAbove hSc hε0 hε1 j hp) ⟨w, hw, rfl⟩

lemma witC_le_log (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z) {p : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : witC S j ε p ≤ log (4 / (1 - ε)) := by
  refine csSup_le (simplex_nonempty.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  have := witF_le_mul_log hSc hε0 hε1 j hw.1 hp
  rwa [hw.2, one_mul] at this

/-- Parameter modulus of the witness rate. -/
lemma witC_le_add_omega (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z)
    {p p' : Z → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hp' : ∀ i, 0 ≤ p' i ∧ p' i ≤ 1) {r : ℝ}
    (hr : ∀ i, |p i - p' i| ≤ r) (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    witC S j ε p' ≤ witC S j ε p + omega ε r := by
  refine csSup_le (simplex_nonempty.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  have h := witF_le_add_omega hSc hε0 hε1 j hw.1 hw.2.le hw.1 hp hp' hr
    (s := 0) (by simp) le_rfl (by linarith) (by linarith)
  rw [add_zero] at h
  linarith [witF_le_witC (S := S) hSc hε0 hε1 j hp hw]

/-- Rates of sub-normalized allocations are below the characteristic rate. -/
lemma infoRate_le_charRate_of_sum_le_one (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {v p : Z → ℝ} (hv : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    infoRate S ε v p ≤ charRate S ε p := by
  have hC := (charRate_mem_Icc (S := S) hSc hε0 hε1 hp).1
  have hc0 : 0 ≤ ∑ i, v i := sum_nonneg fun i _ => hv i
  rcases hc0.eq_or_lt with h0 | h0
  · have hz : ∀ i, v i = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg fun i _ => hv i).1 h0.symm i (mem_univ i)
    have hv' : v = fun i => 0 * v i := by
      funext i
      rw [hz i, mul_zero]
    rw [hv', infoRate_smul S ε v p le_rfl, zero_mul]
    exact hC
  · have hv' : v = fun i => (∑ i, v i) * (v i / ∑ i, v i) := by
      funext i
      field_simp
    have hmem : (fun i => v i / ∑ i, v i) ∈ simplex Z :=
      ⟨fun i => div_nonneg (hv i) hc0, by rw [← sum_div, div_self h0.ne']⟩
    rw [hv', infoRate_smul S ε _ p hc0]
    have h1 := le_charRate (S := S) hSc hε0 hε1 hp hmem
    nlinarith

lemma witC_le_charRate (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z) {p : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : witC S j ε p ≤ charRate S ε p := by
  refine csSup_le (simplex_nonempty.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  exact infoRate_le_charRate_of_sum_le_one hSc hε0 hε1 (collapse_nonneg (hw.1 j) hw.1)
    ((collapse_self_sum_le S j hw.1).trans hw.2.le) hp

/-- **`max_b C_b = C_a`**: at interior means, the witness rate of an inside maximizer equals the
characteristic rate of the action (the one-witness reduction `eq:ast-star`). -/
lemma witC_eq_charRate (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {j : Z} (hj : j ∈ S)
    (hmax : ∀ y ∈ S, μ y ≤ μ j) : witC S j ε μ = charRate S ε μ := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  refine le_antisymm (witC_le_charRate hSc hε0 hε1 j hμ') ?_
  obtain ⟨⟨s, t⟩, hst, heq, -⟩ := one_witness_reduction_max hS hSc hε0 hε1 hμ hj hmax
  have hmem := collapse_mem_simplex hj hst
  have hidem : collapse S j (collapse S j s t j) (collapse S j s t) = collapse S j s t := by
    funext i
    unfold collapse
    by_cases hi : i ∈ S <;> simp [hi, hj]
  have h1 : witF S j ε μ (collapse S j s t) = charRate S ε μ := by
    unfold witF
    rw [hidem, infoRate_collapse hS hSc hε0 hε1 hμ hj hst.1 hst.2.1]
    exact heq
  rw [← h1]
  exact witF_le_witC hSc hε0 hε1 j hμ' hmem

/-- At interior means the witness game is the paper's `min_{z ∉ S} F_ε(p_j,p_z;w_j,w_z)`. -/
lemma witF_eq_starVal (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {p : Z → ℝ} (hp : ∀ i, 0 < p i ∧ p i < 1) {j : Z} (hj : j ∈ S) {w : Z → ℝ}
    (hw : ∀ i, 0 ≤ w i) : witF S j ε p w = starVal S hSc ε p j (w j, w) :=
  infoRate_collapse hS hSc hε0 hε1 hp hj (hw j) hw

lemma witF_le_pairF (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {p : Z → ℝ} (hp : ∀ i, 0 < p i ∧ p i < 1) {j : Z} (hj : j ∈ S) {w : Z → ℝ}
    (hw : ∀ i, 0 ≤ w i) {z : Z} (hz : z ∉ S) :
    witF S j ε p w ≤ pairF ε (p j) (p z) (w j) (w z) := by
  rw [witF_eq_starVal hS hSc hε0 hε1 hp hj hw]
  exact inf'_le (fun z => pairF ε (p j) (p z) (w j) (w z)) (mem_compl.2 hz)

/-- **Finite allocation mesh for a witness label** (simplex-mesh step of `eq:ast-oracle`): for
every tolerance `ξ > 0` one finite set `W` of allocations serves every mean vector in
`[0,1]^M` up to `ξ`. -/
theorem exists_witness_mesh (hSc : Sᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Z) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ W : Finset (Z → ℝ), W.Nonempty ∧ (∀ w ∈ W, w ∈ simplex Z) ∧
      ∀ p : Z → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
        ∃ w ∈ W, witC S j ε p ≤ witF S j ε p w + ξ := by
  classical
  obtain ⟨d0, hd0, hω⟩ :=
    Metric.continuousAt_iff.1 (omega_continuous ε).continuousAt (ξ / 2) (by linarith)
  obtain ⟨d, hd, hdd0, hd2⟩ : ∃ d : ℝ, 0 < d ∧ d < d0 ∧ d ≤ 1 / 2 :=
    ⟨min (d0 / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  have hωd : omega ε d < ξ / 2 := by
    have := hω (x := d) (by rw [Real.dist_eq, sub_zero, abs_of_pos hd]; exact hdd0)
    rw [Real.dist_eq, omega_zero, sub_zero] at this
    exact (abs_lt.1 this).2
  let U : {w : Z → ℝ // w ∈ simplex Z} → Set (Z → ℝ) :=
    fun w => {w' | ∑ i, |w.1 i - w' i| < d}
  have hUo : ∀ w, IsOpen (U w) := fun w =>
    isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_const.sub (continuous_apply i)).abs)
      continuous_const
  have hcov : simplex Z ⊆ ⋃ w, U w := fun w hw =>
    Set.mem_iUnion.2 ⟨⟨w, hw⟩, show ∑ i, |w i - w i| < d by simpa using hd⟩
  obtain ⟨t, ht⟩ := (isCompact_simplex Z).elim_finite_subcover U hUo hcov
  have hserve : ∀ p : Z → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
      ∃ w ∈ t.image Subtype.val, witC S j ε p ≤ witF S j ε p w + ξ := by
    intro p hp
    have hlt : witC S j ε p - ξ / 2 < witC S j ε p := by linarith
    obtain ⟨_, ⟨ws, hws, rfl⟩, hgt⟩ := exists_lt_of_lt_csSup (simplex_nonempty.image _) hlt
    obtain ⟨w, hwt, hw⟩ := Set.mem_iUnion₂.1 (ht hws)
    have hwd : ∑ i, |w.1 i - ws i| < d := hw
    refine ⟨w.1, mem_image_of_mem _ hwt, ?_⟩
    have hmod := witF_le_add_omega hSc hε0 hε1 j w.2.1 w.2.2.le hws.1 hp hp
      (r := 0) (s := d) (by simp) hwd.le hd.le (by linarith) (by linarith)
    rw [zero_add] at hmod
    have hgt' : witC S j ε p - ξ / 2 < witF S j ε p ws := hgt
    linarith
  refine ⟨t.image Subtype.val, ?_, ?_, hserve⟩
  · obtain ⟨w, hw, -⟩ := hserve (fun _ => 1 / 2) (fun _ => ⟨by norm_num, by norm_num⟩)
    exact ⟨w, hw⟩
  · intro w hw
    obtain ⟨i, -, rfl⟩ := mem_image.1 hw
    exact i.2

end WitnessGame

/-! ### Allocation oracles -/

section Oracle

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **The oracle contract `eq:ast-oracle`.**  For every mean vector `p ∈ [0,1]^M`, tolerance
`ξ > 0` and witness label `b` (support `Sup b`, witness `wit b`), the oracle returns
`(w_b, L_b, U_b)` with `w_b ∈ Δ_M`,
`0 ≤ L_b ≤ f_b(p, w_b) ≤ C_b(p) ≤ U_b` and `U_b - L_b ≤ ξ`. -/
structure AllocOracle (Sup : B → Finset Z) (wit : B → Z) (ε : ℝ) where
  /-- returned allocation -/
  w : (Z → ℝ) → ℝ → B → Z → ℝ
  /-- certified lower value -/
  L : (Z → ℝ) → ℝ → B → ℝ
  /-- certified upper value -/
  U : (Z → ℝ) → ℝ → B → ℝ
  w_mem : ∀ p ξ b, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → 0 < ξ → w p ξ b ∈ simplex Z
  L_nonneg : ∀ p ξ b, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → 0 < ξ → 0 ≤ L p ξ b
  L_le : ∀ p ξ b, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → 0 < ξ →
    L p ξ b ≤ witF (Sup b) (wit b) ε p (w p ξ b)
  le_U : ∀ p ξ b, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → 0 < ξ → witC (Sup b) (wit b) ε p ≤ U p ξ b
  gap : ∀ p ξ b, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → 0 < ξ → U p ξ b - L p ξ b ≤ ξ

/-- **A finite-mesh oracle meeting the contract `eq:ast-oracle`.**  It evaluates the witness
game on the finite allocation mesh of `exists_witness_mesh` and returns a mesh point of largest
value, `L` that value and `U = L + ξ`.  The evaluation of the scalar infimum itself (the
threshold mesh and rational logarithm enclosures of the manuscript) is not modelled: `L` is the
exact value of the witness game. -/
theorem exists_allocOracle (Sup : B → Finset Z) (wit : B → Z) {ε : ℝ}
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Nonempty (AllocOracle Sup wit ε) := by
  classical
  have hmesh : ∀ (b : B) (ξ : ℝ), ∃ W : Finset (Z → ℝ), W.Nonempty ∧
      (∀ w ∈ W, w ∈ simplex Z) ∧ (0 < ξ → ∀ p : Z → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
        ∃ w ∈ W, witC (Sup b) (wit b) ε p ≤ witF (Sup b) (wit b) ε p w + ξ) := by
    intro b ξ
    by_cases hξ : 0 < ξ
    · obtain ⟨W, h1, h2, h3⟩ := exists_witness_mesh (hSc b) hε0 hε1 (wit b) hξ
      exact ⟨W, h1, h2, fun _ => h3⟩
    · exact ⟨{fun _ => 1 / (Fintype.card Z : ℝ)}, singleton_nonempty _,
        fun w hw => by rw [mem_singleton.1 hw]; exact uniform_mem_simplex,
        fun h => absurd h hξ⟩
  choose W hWne hWmem hWserve using hmesh
  have hbest : ∀ (p : Z → ℝ) (ξ : ℝ) (b : B), ∃ w ∈ W b ξ, ∀ w' ∈ W b ξ,
      witF (Sup b) (wit b) ε p w' ≤ witF (Sup b) (wit b) ε p w := fun p ξ b =>
    exists_max_image (W b ξ) (fun w => witF (Sup b) (wit b) ε p w) (hWne b ξ)
  choose wb hwb hwbmax using hbest
  refine ⟨{
    w := wb
    L := fun p ξ b => witF (Sup b) (wit b) ε p (wb p ξ b)
    U := fun p ξ b => witF (Sup b) (wit b) ε p (wb p ξ b) + ξ
    w_mem := fun p ξ b _ _ => hWmem b ξ _ (hwb p ξ b)
    L_nonneg := fun p ξ b hp _ => witF_nonneg (wit b) (hWmem b ξ _ (hwb p ξ b)).1 hp
    L_le := fun p ξ b _ _ => le_rfl
    le_U := fun p ξ b hp hξ => by
      obtain ⟨w', hw', hle⟩ := hWserve b ξ hξ p hp
      have := hwbmax p ξ b w' hw'
      linarith
    gap := fun p ξ b _ _ => by simp }⟩

end Oracle

/-! ### The sequential procedure (`app:ast-sequential`) -/

section Epochs

/-- Index of the epoch containing the draw made after `t` observations:
`2^k - 1 ≤ t < 2^{k+1} - 1`. -/
def epochOf (t : ℕ) : ℕ := Nat.log 2 (t + 1)

/-- Epoch `k` begins after `t_k = 2^k - 1` observations. -/
def epochStart (k : ℕ) : ℕ := 2 ^ k - 1

lemma epochStart_succ (k : ℕ) : epochStart (k + 1) = epochStart k + 2 ^ k := by
  unfold epochStart
  have := Nat.one_le_two_pow (n := k)
  rw [pow_succ]
  omega

lemma epochStart_add_one (k : ℕ) : epochStart k + 1 = 2 ^ k := by
  unfold epochStart
  have := Nat.one_le_two_pow (n := k)
  omega

lemma epochStart_epochOf_le (t : ℕ) : epochStart (epochOf t) ≤ t := by
  unfold epochStart epochOf
  have := Nat.pow_log_le_self 2 (show t + 1 ≠ 0 by omega)
  omega

lemma lt_epochStart_add (t : ℕ) : t < epochStart (epochOf t) + 2 ^ epochOf t := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (t + 1)
  have h1 := Nat.one_le_two_pow (n := Nat.log 2 (t + 1))
  unfold epochStart epochOf
  rw [Nat.succ_eq_add_one, pow_succ] at h
  omega

lemma epochOf_add {k d : ℕ} (hd : d < 2 ^ k) : epochOf (epochStart k + d) = k := by
  unfold epochOf epochStart
  have := Nat.one_le_two_pow (n := k)
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
  · omega
  · rw [pow_succ]
    omega

lemma epochOf_epochStart (k : ℕ) : epochOf (epochStart k) = k := by
  have := epochOf_add (k := k) (d := 0) (Nat.two_pow_pos k)
  simpa using this

/-- Tie tolerance `h_k = 2^{-⌊k/16⌋}`. -/
noncomputable def hSched (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k / 16)

/-- Oracle tolerance `ξ_k = 2^{-⌊k/8⌋-4}`. -/
noncomputable def xiSched (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k / 8 + 4)

/-- Forced-exploration weight `γ_k = 2^{-⌊k/4⌋}`. -/
noncomputable def gamSched (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k / 4)

lemma hSched_pos (k : ℕ) : 0 < hSched k := by unfold hSched; positivity

lemma xiSched_pos (k : ℕ) : 0 < xiSched k := by unfold xiSched; positivity

lemma gamSched_pos (k : ℕ) : 0 < gamSched k := by unfold gamSched; positivity

lemma gamSched_le_one (k : ℕ) : gamSched k ≤ 1 := by
  unfold gamSched
  exact pow_le_one₀ (by norm_num) (by norm_num)

end Epochs

section Procedure

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype B] [LinearOrder B]
  [Nonempty B]

open Classical in
/-- The first label (in the fixed order of labels) satisfying `P`. -/
noncomputable def firstLabel (P : B → Prop) : B :=
  if h : (univ.filter P).Nonempty then (univ.filter P).min' h else Classical.arbitrary B

lemma firstLabel_congr {P Q : B → Prop} (h : ∀ b, P b ↔ Q b) :
    firstLabel P = firstLabel Q := by
  have : P = Q := funext fun b => propext (h b)
  rw [this]

open Classical in
lemma firstLabel_spec {P : B → Prop} (h : ∃ b, P b) : P (firstLabel P) := by
  have hne : (univ.filter P).Nonempty := by
    obtain ⟨b, hb⟩ := h
    exact ⟨b, by simp [hb]⟩
  unfold firstLabel
  rw [dite_eq_left hne]
  exact (mem_filter.1 (min'_mem _ hne)).2

/-- The within-epoch rule: a terminal minimizing `(n_i + 1) / v_i`, with a fixed choice among
minimizers. -/
noncomputable def pick (v : Z → ℝ) (n : Z → ℕ) : Z :=
  Classical.choose (exists_min_image univ (fun i => ((n i : ℝ) + 1) / v i) univ_nonempty)

lemma pick_spec (v : Z → ℝ) (n : Z → ℕ) (i : Z) :
    ((n (pick v n) : ℝ) + 1) / v (pick v n) ≤ ((n i : ℝ) + 1) / v i :=
  (Classical.choose_spec
    (exists_min_image univ (fun i => ((n i : ℝ) + 1) / v i) univ_nonempty)).2 i (mem_univ i)

variable {Sup : B → Finset Z} {wit : B → Z} {ε : ℝ}

/-- Sticky label selection `eq:ast-sticky`:
`b_k = min{b : U_b^k ≥ max_c L_c^k - h_k}` from the oracle outputs at the epoch-start
empirical vector `p`. -/
noncomputable def planLab (O : AllocOracle Sup wit ε) (k : ℕ) (p : Z → ℝ) : B :=
  firstLabel fun b =>
    (univ.sup' univ_nonempty fun c => O.L p (xiSched k) c) - hSched k ≤ O.U p (xiSched k) b

/-- Epoch target `v^k = (1 - γ_k) w_{b_k}^k + γ_k 1/M` (`eq:ast-sticky`). -/
noncomputable def planTgt (O : AllocOracle Sup wit ε) (k : ℕ) (p : Z → ℝ) : Z → ℝ := fun i =>
  (1 - gamSched k) * O.w p (xiSched k) (planLab O k p) i
    + gamSched k * (1 / (Fintype.card Z : ℝ))

lemma planTgt_ge (O : AllocOracle Sup wit ε) (k : ℕ) {p : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Z) :
    gamSched k * (1 / (Fintype.card Z : ℝ)) ≤ planTgt O k p i := by
  have hw := (O.w_mem p (xiSched k) (planLab O k p) hp (xiSched_pos k)).1 i
  have := mul_nonneg (sub_nonneg.2 (gamSched_le_one k)) hw
  unfold planTgt
  linarith

lemma planTgt_pos (O : AllocOracle Sup wit ε) (k : ℕ) {p : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Z) : 0 < planTgt O k p i := by
  have hM : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have : 0 < gamSched k * (1 / (Fintype.card Z : ℝ)) :=
    mul_pos (gamSched_pos k) (by positivity)
  exact this.trans_le (planTgt_ge O k hp i)

lemma planTgt_sum (O : AllocOracle Sup wit ε) (k : ℕ) {p : Z → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : ∑ i, planTgt O k p i = 1 := by
  have hw := (O.w_mem p (xiSched k) (planLab O k p) hp (xiSched_pos k)).2
  have hM : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold planTgt
  rw [sum_add_distrib, ← mul_sum, hw, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- Successes at terminal `z` in a transcript (terminals `ts`, outcomes `h`). -/
def lsucc : List Z → List Bool → Z → ℕ
  | a :: ts, b :: h, z => lsucc ts h z + if a = z then (if b then 1 else 0) else 0
  | [], _, _ => 0
  | _ :: _, [], _ => 0

/-- Empirical mean of a transcript, `1/2` at an unsampled terminal. -/
noncomputable def lemp (ts : List Z) (h : List Bool) (z : Z) : ℝ :=
  if ts.count z = 0 then 1 / 2 else (lsucc ts h z : ℝ) / (ts.count z : ℝ)

/-- The next terminal, from the terminals `ts` and outcomes `h` observed so far: within epoch
`k` the target is computed from the data at the epoch start and the local counts are those of
the current epoch. -/
noncomputable def rule (O : AllocOracle Sup wit ε) (ts : List Z) (h : List Bool) : Z :=
  pick (planTgt O (epochOf h.length)
      (lemp (ts.drop (h.length - epochStart (epochOf h.length)))
        (h.drop (h.length - epochStart (epochOf h.length)))))
    (fun i => (ts.take (h.length - epochStart (epochOf h.length))).count i)

/-- The terminals requested along a history of outcomes. -/
noncomputable def trace (O : AllocOracle Sup wit ε) : List Bool → List Z
  | [] => []
  | _ :: h => rule O (trace O h) h :: trace O h

/-- Label in force for the draw made at history `g`, from the transcript. -/
noncomputable def lLab (O : AllocOracle Sup wit ε) (g : List Bool) : B :=
  planLab O (epochOf g.length)
    (lemp ((trace O g).drop (g.length - epochStart (epochOf g.length)))
      (g.drop (g.length - epochStart (epochOf g.length))))

open Classical in
/-- The stopping rule: at the square times `t = ℓ²`, `ℓ ≥ 1`, test the label that was in force
for the last draw with the pair statistic `eq:ast-glr` and the threshold `eq:ast-threshold`
(exact values; no numerical enclosures). -/
noncomputable def stopRule (O : AllocOracle Sup wit ε) (δ : ℝ) : List Bool → Bool
  | [] => false
  | b :: g =>
      decide (IsSquare (g.length + 1) ∧ ∀ z, z ∉ Sup (lLab O g) →
        log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ)
            + log (((trace O (b :: g)).count (wit (lLab O g)) : ℝ) + 1)
            + log (((trace O (b :: g)).count z : ℝ) + 1)
          ≤ pairF ε (lemp (trace O (b :: g)) (b :: g) (wit (lLab O g)))
              (lemp (trace O (b :: g)) (b :: g) z)
              ((trace O (b :: g)).count (wit (lLab O g))) ((trace O (b :: g)).count z))

/-- **The procedure of `app:ast-sequential`** as a deterministic adaptive sampler, for an
allocation oracle `O` meeting `eq:ast-oracle` and confidence parameter `δ`. -/
noncomputable def astSampler (O : AllocOracle Sup wit ε) (δ : ℝ) : Stopped.Sampler Z :=
  ⟨fun h => rule O (trace O h) h, stopRule O δ⟩

open Stopped

variable (O : AllocOracle Sup wit ε) (δ : ℝ)

lemma cnt_eq_count (z : Z) : ∀ h : List Bool, cnt (astSampler O δ) z h = (trace O h).count z
  | [] => rfl
  | b :: h => by
      show cnt (astSampler O δ) z h + (if rule O (trace O h) h = z then 1 else 0)
        = (rule O (trace O h) h :: trace O h).count z
      rw [List.count_cons, cnt_eq_count z h]
      simp

lemma scnt_eq_lsucc (z : Z) :
    ∀ h : List Bool, scnt (astSampler O δ) z h = lsucc (trace O h) h z
  | [] => rfl
  | b :: h => by
      show scnt (astSampler O δ) z h
          + (if rule O (trace O h) h = z then (if b then 1 else 0) else 0)
        = lsucc (rule O (trace O h) h :: trace O h) (b :: h) z
      rw [scnt_eq_lsucc z h]
      rfl

lemma emp_eq_lemp (z : Z) (h : List Bool) :
    emp (astSampler O δ) z h = lemp (trace O h) h z := by
  unfold emp lemp
  rw [cnt_eq_count, scnt_eq_lsucc]

lemma trace_drop : ∀ (h : List Bool) (d : ℕ), trace O (h.drop d) = (trace O h).drop d
  | [], d => by simp [trace]
  | b :: h, 0 => rfl
  | b :: h, d + 1 => by
      show trace O (h.drop d) = (trace O h).drop d
      exact trace_drop h d

/-- The history at the start of the current epoch. -/
def epochHist (h : List Bool) : List Bool :=
  h.drop (h.length - epochStart (epochOf h.length))

/-- Vector of empirical means at a history. -/
noncomputable def empVec (S : Sampler Z) (h : List Bool) : Z → ℝ := fun z => emp S z h

lemma empVec_mem (S : Sampler Z) (h : List Bool) (i : Z) :
    0 ≤ empVec S h i ∧ empVec S h i ≤ 1 := emp_mem_Icc S i h

/-- Label in force for the draw made at history `h`. -/
noncomputable def curLab (h : List Bool) : B :=
  planLab O (epochOf h.length) (empVec (astSampler O δ) (epochHist h))

/-- Target vector in force for the draw made at history `h`. -/
noncomputable def curTgt (h : List Bool) : Z → ℝ :=
  planTgt O (epochOf h.length) (empVec (astSampler O δ) (epochHist h))

lemma lemp_drop_eq (h : List Bool) (d : ℕ) :
    lemp ((trace O h).drop d) (h.drop d) = empVec (astSampler O δ) (h.drop d) := by
  funext z
  unfold empVec
  rw [emp_eq_lemp, trace_drop]

lemma lLab_eq (g : List Bool) : lLab O g = curLab O δ g := by
  unfold lLab curLab epochHist
  rw [lemp_drop_eq O δ]

/-- The sampling rule in terms of the sampler's own counts. -/
lemma next_eq (h : List Bool) :
    (astSampler O δ).next h
      = pick (curTgt O δ h)
          (fun i => cnt (astSampler O δ) i h - cnt (astSampler O δ) i (epochHist h)) := by
  show rule O (trace O h) h = _
  unfold rule curTgt epochHist
  rw [lemp_drop_eq O δ]
  congr 1
  funext i
  rw [cnt_eq_count, cnt_eq_count, trace_drop]
  have h1 := List.take_append_drop (h.length - epochStart (epochOf h.length)) (trace O h)
  have h2 := congrArg (List.count i) h1
  rw [List.count_append] at h2
  omega

lemma stop_nil : (astSampler O δ).stop [] = false := rfl

/-- The stopping rule in terms of the certificate statistic and threshold. -/
lemma stop_cons_iff (b : Bool) (g : List Bool) :
    (astSampler O δ).stop (b :: g) = true ↔
      IsSquare (g.length + 1) ∧ ∀ z, z ∉ Sup (curLab O δ g) →
        certThr (astSampler O δ) δ (wit (curLab O δ g)) z (b :: g)
          ≤ certStat (astSampler O δ) ε (wit (curLab O δ g)) z (b :: g) := by
  show stopRule O δ (b :: g) = true ↔ _
  unfold stopRule
  rw [decide_eq_true_iff, lLab_eq O δ]
  unfold certThr certStat
  simp only [emp_eq_lemp, cnt_eq_count]

end Procedure

/-! ### Tracking and forced exploration (`eq:ast-tracking`, `eq:ast-floor`) -/

section Tracking

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype B] [LinearOrder B]
  [Nonempty B] {Sup : B → Finset Z} {wit : B → Z} {ε : ℝ}

open Stopped

lemma epoch_data {k d : ℕ} {g : List Bool} (hd : d < 2 ^ k)
    (hlen : g.length = epochStart k + d) : epochOf g.length = k ∧ epochHist g = g.drop d := by
  have hk : epochOf g.length = k := by rw [hlen]; exact epochOf_add hd
  refine ⟨hk, ?_⟩
  unfold epochHist
  rw [hk, hlen]
  congr 1
  omega

lemma curTgt_epoch (O : AllocOracle Sup wit ε) (δ : ℝ) {k d : ℕ} {g : List Bool}
    (hd : d < 2 ^ k) (hlen : g.length = epochStart k + d) :
    curTgt O δ g = planTgt O k (empVec (astSampler O δ) (g.drop d)) := by
  obtain ⟨hk, hh⟩ := epoch_data hd hlen
  unfold curTgt
  rw [hk, hh]

lemma curLab_epoch (O : AllocOracle Sup wit ε) (δ : ℝ) {k d : ℕ} {g : List Bool}
    (hd : d < 2 ^ k) (hlen : g.length = epochStart k + d) :
    curLab O δ g = planLab O k (empVec (astSampler O δ) (g.drop d)) := by
  obtain ⟨hk, hh⟩ := epoch_data hd hlen
  unfold curLab
  rw [hk, hh]

lemma curTgt_pos (O : AllocOracle Sup wit ε) (δ : ℝ) (h : List Bool) (i : Z) :
    0 < curTgt O δ h i :=
  planTgt_pos O _ (empVec_mem _ _) i

lemma curTgt_sum (O : AllocOracle Sup wit ε) (δ : ℝ) (h : List Bool) :
    ∑ i, curTgt O δ h i = 1 :=
  planTgt_sum O _ (empVec_mem _ _)

/-- Invariant of the within-epoch merge rule: after `d` draws of an epoch there is a level `q`
with `v_i q - 1 ≤ n_i ≤ v_i q` for the local counts `n_i`. -/
lemma epoch_level (O : AllocOracle Sup wit ε) (δ : ℝ) :
    ∀ (d k : ℕ) (g : List Bool), d ≤ 2 ^ k → g.length = epochStart k + d →
      ∃ n : Z → ℕ,
        (∀ i, cnt (astSampler O δ) i g = cnt (astSampler O δ) i (g.drop d) + n i) ∧
        ∃ q : ℝ, ∀ i,
          (n i : ℝ) ≤ planTgt O k (empVec (astSampler O δ) (g.drop d)) i * q ∧
          planTgt O k (empVec (astSampler O δ) (g.drop d)) i * q ≤ (n i : ℝ) + 1
  | 0, k, g, _, _ => ⟨fun _ => 0, fun i => by simp, 0, fun i => by simp⟩
  | d + 1, k, g, hd, hlen => by
      cases g with
      | nil =>
        simp only [List.length_nil] at hlen
        omega
      | cons b g' =>
        have hlen' : g'.length = epochStart k + d := by
          simp only [List.length_cons] at hlen
          omega
        have hd' : d < 2 ^ k := hd
        obtain ⟨n', hn', q', hq'⟩ := epoch_level O δ d k g' hd'.le hlen'
        have hdrop : (b :: g').drop (d + 1) = g'.drop d := rfl
        rw [hdrop]
        obtain ⟨v, hv⟩ : ∃ v, v = planTgt O k (empVec (astSampler O δ) (g'.drop d)) := ⟨_, rfl⟩
        rw [← hv] at hq' ⊢
        have hvpos : ∀ i, 0 < v i := fun i => by
          rw [hv]
          exact planTgt_pos O k (empVec_mem _ _) i
        have hnext : (astSampler O δ).next g' = pick v n' := by
          rw [next_eq, curTgt_epoch O δ hd' hlen', (epoch_data hd' hlen').2, ← hv]
          congr 1
          funext i
          rw [hn' i]
          simp
        obtain ⟨s, hs⟩ : ∃ s, s = pick v n' := ⟨_, rfl⟩
        have hpick : ∀ i, ((n' s : ℝ) + 1) / v s ≤ ((n' i : ℝ) + 1) / v i := fun i => by
          rw [hs]
          exact pick_spec v n' i
        rw [← hs] at hnext
        refine ⟨fun i => n' i + if s = i then 1 else 0, fun i => ?_,
          ((n' s : ℝ) + 1) / v s, fun i => ?_⟩
        · show cnt (astSampler O δ) i g' + (if (astSampler O δ).next g' = i then 1 else 0) = _
          rw [hnext, hn' i, add_assoc]
        · have hqq : q' ≤ ((n' s : ℝ) + 1) / v s := by
            rw [le_div_iff₀ (hvpos s), mul_comm]
            exact (hq' s).2
          have hr := hpick i
          rw [div_le_div_iff₀ (hvpos s) (hvpos i)] at hr
          by_cases hi : s = i
          · subst hi
            have e : v s * (((n' s : ℝ) + 1) / v s) = (n' s : ℝ) + 1 := by
              have := (hvpos s).ne'
              field_simp
            simp only [ite_true, Nat.cast_add, Nat.cast_one]
            rw [e]
            constructor <;> linarith
          · simp only [ite_eq_right hi, add_zero]
            constructor
            · exact (hq' i).1.trans (mul_le_mul_of_nonneg_left hqq (hvpos i).le)
            · rw [mul_div_assoc', div_le_iff₀ (hvpos s)]
              linarith

/-- **Tracking within one epoch**: after `d ≤ 2^k` draws of epoch `k` with target `v`, the local
counts satisfy `d v_i - 1 ≤ n_i` and `∑_i |n_i - d v_i| ≤ 2M`. -/
lemma epoch_track (O : AllocOracle Sup wit ε) (δ : ℝ) {d k : ℕ} {g : List Bool}
    (hd : d ≤ 2 ^ k) (hlen : g.length = epochStart k + d) :
    ∃ n : Z → ℕ,
      (∀ i, cnt (astSampler O δ) i g = cnt (astSampler O δ) i (g.drop d) + n i) ∧
      (∀ i, (d : ℝ) * planTgt O k (empVec (astSampler O δ) (g.drop d)) i - 1 ≤ n i) ∧
      ∑ i, |(n i : ℝ) - d * planTgt O k (empVec (astSampler O δ) (g.drop d)) i|
        ≤ 2 * (Fintype.card Z : ℝ) := by
  obtain ⟨n, hn, q, hq⟩ := epoch_level O δ d k g hd hlen
  obtain ⟨v, hv⟩ : ∃ v, v = planTgt O k (empVec (astSampler O δ) (g.drop d)) := ⟨_, rfl⟩
  rw [← hv] at hq ⊢
  have hvpos : ∀ i, 0 < v i := fun i => by
    rw [hv]
    exact planTgt_pos O k (empVec_mem _ _) i
  have hv1 : ∑ i, v i = 1 := by
    rw [hv]
    exact planTgt_sum O k (empVec_mem _ _)
  have hsumN : ∑ i, n i = d := by
    have h1 := sum_cnt (astSampler O δ) g
    have h2 := sum_cnt (astSampler O δ) (g.drop d)
    rw [List.length_drop] at h2
    have h3 : ∑ i, cnt (astSampler O δ) i g
        = ∑ i, cnt (astSampler O δ) i (g.drop d) + ∑ i, n i := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => hn i
    omega
  have hsum : ∑ i, (n i : ℝ) = d := by exact_mod_cast hsumN
  have h1 : (d : ℝ) ≤ q := by
    have := sum_le_sum (s := (univ : Finset Z)) fun i _ => (hq i).1
    rw [← sum_mul, hv1, one_mul, hsum] at this
    exact this
  have h2 : q ≤ (d : ℝ) + Fintype.card Z := by
    have := sum_le_sum (s := (univ : Finset Z)) fun i _ => (hq i).2
    rw [← sum_mul, hv1, one_mul, sum_add_distrib, hsum, sum_const, card_univ, nsmul_eq_mul,
      mul_one] at this
    exact this
  have hb : ∀ i, (d : ℝ) * v i - 1 ≤ n i ∧ (n i : ℝ) ≤ ((d : ℝ) + Fintype.card Z) * v i := by
    intro i
    have h3 := mul_le_mul_of_nonneg_left h1 (hvpos i).le
    have h4 := mul_le_mul_of_nonneg_left h2 (hvpos i).le
    constructor
    · linarith [(hq i).2]
    · linarith [(hq i).1]
  refine ⟨n, hn, fun i => (hb i).1, ?_⟩
  have habs : ∀ i, |(n i : ℝ) - d * v i| ≤ 1 + Fintype.card Z * v i := by
    intro i
    have hM : (0 : ℝ) ≤ Fintype.card Z * v i := mul_nonneg (Nat.cast_nonneg _) (hvpos i).le
    rw [abs_le]
    constructor
    · linarith [(hb i).1]
    · linarith [(hb i).2]
  calc ∑ i, |(n i : ℝ) - d * v i|
      ≤ ∑ i, (1 + Fintype.card Z * v i) := sum_le_sum fun i _ => habs i
    _ = 2 * Fintype.card Z := by
        rw [sum_add_distrib, ← mul_sum, hv1, sum_const, card_univ, nsmul_eq_mul]
        ring

/-- `W(t)`: the sum of the target vectors over the first `t` scheduled draws. -/
noncomputable def Wt (O : AllocOracle Sup wit ε) (δ : ℝ) : List Bool → Z → ℝ
  | [], _ => 0
  | _ :: h, i => Wt O δ h i + curTgt O δ h i

lemma Wt_nonneg (O : AllocOracle Sup wit ε) (δ : ℝ) : ∀ (h : List Bool) (i : Z), 0 ≤ Wt O δ h i
  | [], _ => le_rfl
  | _ :: h, i => add_nonneg (Wt_nonneg O δ h i) (curTgt_pos O δ h i).le

lemma Wt_sum (O : AllocOracle Sup wit ε) (δ : ℝ) :
    ∀ h : List Bool, ∑ i, Wt O δ h i = h.length
  | [] => by simp [Wt]
  | _ :: h => by
      simp only [Wt, sum_add_distrib, Wt_sum O δ h, curTgt_sum, List.length_cons,
        Nat.cast_add, Nat.cast_one]

lemma Wt_epoch (O : AllocOracle Sup wit ε) (δ : ℝ) :
    ∀ (d k : ℕ) (g : List Bool), d ≤ 2 ^ k → g.length = epochStart k + d → ∀ i,
      Wt O δ g i = Wt O δ (g.drop d) i
        + d * planTgt O k (empVec (astSampler O δ) (g.drop d)) i
  | 0, k, g, _, _ => fun i => by simp
  | d + 1, k, g, hd, hlen => by
      cases g with
      | nil =>
        simp only [List.length_nil] at hlen
        omega
      | cons b g' =>
        have hlen' : g'.length = epochStart k + d := by
          simp only [List.length_cons] at hlen
          omega
        have hd' : d < 2 ^ k := hd
        intro i
        have ih := Wt_epoch O δ d k g' hd'.le hlen' i
        have hdrop : (b :: g').drop (d + 1) = g'.drop d := rfl
        rw [hdrop]
        show Wt O δ g' i + curTgt O δ g' i = _
        rw [ih, curTgt_epoch O δ hd' hlen']
        push_cast
        ring

lemma tracking_step (O : AllocOracle Sup wit ε) (δ : ℝ) {d k : ℕ} {g : List Bool}
    (hd : d ≤ 2 ^ k) (hlen : g.length = epochStart k + d) {X : ℝ}
    (hprev : ∑ i, |(cnt (astSampler O δ) i (g.drop d) : ℝ) - Wt O δ (g.drop d) i| ≤ X) :
    ∑ i, |(cnt (astSampler O δ) i g : ℝ) - Wt O δ g i| ≤ X + 2 * (Fintype.card Z : ℝ) := by
  obtain ⟨n, hn, -, hsum⟩ := epoch_track O δ hd hlen
  have hW := Wt_epoch O δ d k g hd hlen
  have hterm : ∀ i, |(cnt (astSampler O δ) i g : ℝ) - Wt O δ g i|
      ≤ |(cnt (astSampler O δ) i (g.drop d) : ℝ) - Wt O δ (g.drop d) i|
        + |(n i : ℝ) - d * planTgt O k (empVec (astSampler O δ) (g.drop d)) i| := by
    intro i
    rw [hW i, hn i]
    push_cast
    refine le_trans (le_of_eq ?_) (abs_add_le _ _)
    congr 1
    ring
  calc ∑ i, |(cnt (astSampler O δ) i g : ℝ) - Wt O δ g i|
      ≤ ∑ i, (|(cnt (astSampler O δ) i (g.drop d) : ℝ) - Wt O δ (g.drop d) i|
        + |(n i : ℝ) - d * planTgt O k (empVec (astSampler O δ) (g.drop d)) i|) :=
        sum_le_sum fun i _ => hterm i
    _ ≤ X + 2 * (Fintype.card Z : ℝ) := by
        rw [sum_add_distrib]
        linarith

lemma tracking_boundary (O : AllocOracle Sup wit ε) (δ : ℝ) :
    ∀ (k : ℕ) (g : List Bool), g.length = epochStart k →
      ∑ i, |(cnt (astSampler O δ) i g : ℝ) - Wt O δ g i| ≤ 2 * (Fintype.card Z : ℝ) * k
  | 0, g, hlen => by
      have : g = [] := List.length_eq_zero_iff.1 (by simpa [epochStart] using hlen)
      subst this
      simp [cnt, Wt]
  | k + 1, g, hlen => by
      rw [epochStart_succ] at hlen
      have hlen0 : (g.drop (2 ^ k)).length = epochStart k := by
        rw [List.length_drop]
        omega
      have ih := tracking_boundary O δ k _ hlen0
      have := tracking_step O δ le_rfl hlen ih
      push_cast
      linarith

/-- **Multi-epoch tracking** (`eq:ast-tracking`):
`‖N(t) - W(t)‖_1 ≤ 2M(1 + ⌊log_2(t+1)⌋)` at every history. -/
theorem tracking_any (O : AllocOracle Sup wit ε) (δ : ℝ) (h : List Bool) :
    ∑ i, |(cnt (astSampler O δ) i h : ℝ) - Wt O δ h i|
      ≤ 2 * (Fintype.card Z : ℝ) * ((epochOf h.length : ℝ) + 1) := by
  have h1 := epochStart_epochOf_le h.length
  have h2 := lt_epochStart_add h.length
  have hlen : h.length = epochStart (epochOf h.length)
      + (h.length - epochStart (epochOf h.length)) := by omega
  have hd : h.length - epochStart (epochOf h.length) ≤ 2 ^ epochOf h.length := by omega
  have hlen0 : (h.drop (h.length - epochStart (epochOf h.length))).length
      = epochStart (epochOf h.length) := by
    rw [List.length_drop]
    omega
  have := tracking_step O δ hd hlen (tracking_boundary O δ _ _ hlen0)
  linarith

lemma cnt_drop_le (S : Sampler Z) (i : Z) :
    ∀ (h : List Bool) (d : ℕ), cnt S i (h.drop d) ≤ cnt S i h
  | [], d => by simp
  | b :: h, 0 => le_rfl
  | b :: h, d + 1 => by
      show cnt S i (h.drop d) ≤ cnt S i h + _
      exact (cnt_drop_le S i h d).trans (Nat.le_add_right _ _)

lemma cnt_le_length (S : Sampler Z) (i : Z) (h : List Bool) : cnt S i h ≤ h.length := by
  rw [← sum_cnt S h]
  exact single_le_sum (f := fun z => cnt S z h) (fun _ _ => Nat.zero_le _) (mem_univ i)

/-- Arithmetic of the exploration floor. -/
lemma floor_num {t m M : ℕ} (h1 : t + 1 < 2 ^ (m + 2)) (h2 : 25 * M ^ 2 ≤ t) (hM : 1 ≤ M) :
    √(t : ℝ) * √(√(t : ℝ)) / (8 * (M : ℝ))
      ≤ 2 ^ m * ((1 / 2 : ℝ) ^ (m / 4) * (1 / (M : ℝ))) - 1 := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = √(t : ℝ) * √(√(t : ℝ)) := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx4 : x ^ 4 = (t : ℝ) ^ 3 := by
    have e1 : √(t : ℝ) ^ 2 = t := Real.sq_sqrt ht0
    have e2 : √(√(t : ℝ)) ^ 2 = √(t : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc x ^ 4 = (√(t : ℝ) ^ 2) ^ 2 * ((√(√(t : ℝ)) ^ 2) ^ 2) := by rw [hx]; ring
      _ = (t : ℝ) ^ 3 := by rw [e1, e2, e1]; ring
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = m - m / 4 := ⟨_, rfl⟩
  have hdiv : m / 4 * 4 ≤ m := Nat.div_mul_le_self m 4
  have hem : e + m / 4 = m := by omega
  have hpow : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m / 4) = 2 ^ e := by
    have e2m : (2 : ℝ) ^ m = 2 ^ e * 2 ^ (m / 4) := by rw [← pow_add, hem]
    rw [e2m, mul_assoc, ← mul_pow]
    norm_num
  have hnat : t ^ 3 ≤ 81 * 2 ^ (4 * e) := by
    have ht : t ≤ 4 * 2 ^ m := by
      have : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
      omega
    calc t ^ 3 ≤ (4 * 2 ^ m) ^ 3 := Nat.pow_le_pow_left ht 3
      _ = 64 * 2 ^ (3 * m) := by rw [mul_pow, ← pow_mul, mul_comm m 3]; norm_num
      _ ≤ 64 * 2 ^ (4 * e) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ 81 * 2 ^ (4 * e) := Nat.mul_le_mul_right _ (by norm_num)
  have hx3 : x ≤ 3 * 2 ^ e := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    rw [hx4]
    have : ((t ^ 3 : ℕ) : ℝ) ≤ ((81 * 2 ^ (4 * e) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this
    calc (t : ℝ) ^ 3 ≤ 81 * 2 ^ (4 * e) := this
      _ = (3 * 2 ^ e) ^ 4 := by rw [mul_pow, ← pow_mul, mul_comm e 4]; norm_num
  have hx5 : 5 * (M : ℝ) ≤ x := by
    have hs1 : 5 * (M : ℝ) ≤ √(t : ℝ) := by
      rw [Real.le_sqrt (by positivity) ht0]
      have : ((25 * M ^ 2 : ℕ) : ℝ) ≤ t := by exact_mod_cast h2
      push_cast at this
      nlinarith
    have hs2 : (1 : ℝ) ≤ √(t : ℝ) := by nlinarith
    have hs3 : (1 : ℝ) ≤ √(√(t : ℝ)) := by
      rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]
      simpa using hs2
    rw [hx]
    nlinarith [Real.sqrt_nonneg (t : ℝ)]
  rw [← mul_assoc, hpow]
  have e1 : x / (3 * (M : ℝ)) - x / (8 * (M : ℝ)) = 5 * x / (24 * (M : ℝ)) := by
    field_simp
    ring
  have e2 : (1 : ℝ) ≤ 5 * x / (24 * (M : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have e3 : x / (3 * (M : ℝ)) ≤ 2 ^ e * (1 / (M : ℝ)) := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ e * (1 / (M : ℝ)) * (3 * (M : ℝ)) = 3 * 2 ^ e := by field_simp
    rw [this]
    exact hx3
  linarith

/-- **Exploration floor** (`eq:ast-floor`): `N_i(t) ≥ t^{3/4} / (8M)` for every terminal, at
every history of length `t ≥ 25 M²` (`t^{3/4}` is written `√t · √√t`). -/
theorem count_floor (O : AllocOracle Sup wit ε) (δ : ℝ) (h : List Bool) (i : Z)
    (ht : 25 * Fintype.card Z ^ 2 ≤ h.length) :
    √(h.length : ℝ) * √(√(h.length : ℝ)) / (8 * (Fintype.card Z : ℝ))
      ≤ (cnt (astSampler O δ) i h : ℝ) := by
  have hM : 1 ≤ Fintype.card Z := Fintype.card_pos
  have ht1 : 25 ≤ h.length := by nlinarith
  have hk : 0 < epochOf h.length := Nat.log_pos (by norm_num) (by omega)
  obtain ⟨m, hm⟩ : ∃ m, epochOf h.length = m + 1 := ⟨epochOf h.length - 1, by omega⟩
  have h1 := epochStart_epochOf_le h.length
  have h2 := lt_epochStart_add h.length
  rw [hm] at h1 h2
  have h3 := epochStart_succ m
  have h4 := epochStart_add_one m
  set g := h.drop (h.length - epochStart (m + 1)) with hg
  have hlen : g.length = epochStart m + 2 ^ m := by
    rw [hg, List.length_drop]
    omega
  obtain ⟨n, hn, hlow, -⟩ := epoch_track O δ le_rfl hlen
  have hge := planTgt_ge O m (empVec_mem (astSampler O δ) (g.drop (2 ^ m))) i
  have hc1 : (n i : ℝ) ≤ cnt (astSampler O δ) i h := by
    have a1 : n i ≤ cnt (astSampler O δ) i g := by rw [hn i]; exact Nat.le_add_left _ _
    have a2 := cnt_drop_le (astSampler O δ) i h (h.length - epochStart (m + 1))
    exact_mod_cast a1.trans a2
  have hnum := floor_num (t := h.length) (m := m) (M := Fintype.card Z)
    (by rw [pow_succ, pow_succ] at *; omega) ht hM
  have hlow' := hlow i
  push_cast at hlow'
  have hmul := mul_le_mul_of_nonneg_left hge (show (0 : ℝ) ≤ 2 ^ m by positivity)
  unfold gamSched at hmul
  linarith

end Tracking

/-! ### A summable estimation tail -/

section Tail

/-- Estimation radius `t^{-1/8}`, written `1 / √√√t`. -/
noncomputable def rad (t : ℕ) : ℝ := 1 / √(√(√(t : ℝ)))

lemma rad_pos {t : ℕ} (ht : 1 ≤ t) : 0 < rad t := by
  have h0 : (0 : ℝ) < t := by exact_mod_cast ht
  unfold rad
  exact div_pos one_pos (Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 h0)))

lemma rad_eq_rpow (t : ℕ) : rad t = (t : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  unfold rad
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h0,
    ← Real.rpow_mul h0, Real.rpow_neg h0, one_div]
  norm_num

lemma tendsto_rad : Tendsto rad atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℕ => √(√(√(t : ℝ)))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  exact tendsto_const_nhds.div_atTop h

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype B] [LinearOrder B]
  [Nonempty B] {Sup : B → Finset Z} {wit : B → Z} {ε : ℝ}

open Stopped

/-- The bad event: at some time `s ∈ [u, q]` of the run some empirical mean is farther than
`s^{-1/8}` from its mean. -/
def badSet (S : Sampler Z) (μ : Z → ℝ) (u q : ℕ) : Set (List Bool) :=
  {l | ever (fun h => u ≤ h.length ∧ h.length ≤ q ∧
    ∃ i, rad h.length < |emp S i h - μ i|) l}

/-- **Estimation tail of the procedure.**  For `u ≥ 25 M²` the probability of the bad event on
`[u, q]` is at most `∑_{s=u}^{q} 2M exp(-√s/(4M))` (each term is at most the manuscript's
`2M s exp(-√s/(4M))`; the union over intrinsic counts is not needed).  The adaptive counts
enter through the deterministic floor `eq:ast-floor`. -/
theorem estimation_tail (O : AllocOracle Sup wit ε) (δ : ℝ) {μ : Z → ℝ}
    (hμ : ∀ z, 0 < μ z ∧ μ z < 1) (u q : ℕ) (hu : 25 * Fintype.card Z ^ 2 ≤ u) (n : ℕ) :
    prob (astSampler O δ) μ n (badSet (astSampler O δ) μ u q)
      ≤ ∑ s ∈ Icc u q,
          2 * (Fintype.card Z : ℝ) * exp (-(√(s : ℝ) / (4 * (Fintype.card Z : ℝ)))) := by
  have hM : 1 ≤ Fintype.card Z := Fintype.card_pos
  have hMr : (0 : ℝ) < Fintype.card Z := by exact_mod_cast hM
  have hs1 : ∀ s ∈ Icc u q, 1 ≤ s := fun s hs => by
    have := (mem_Icc.1 hs).1
    nlinarith
  have hpos : ∀ s ∈ Icc u q, (0 : ℝ) < s := fun s hs => by exact_mod_cast hs1 s hs
  have h := prob_bad_le (astSampler O δ) hμ u q rad
    (fun s => √(s : ℝ) * √(√(s : ℝ)) / (8 * (Fintype.card Z : ℝ)))
    (fun s hs => rad_pos (hs1 s hs))
    (fun s hs => div_pos (mul_pos (Real.sqrt_pos.2 (hpos s hs))
      (Real.sqrt_pos.2 (Real.sqrt_pos.2 (hpos s hs)))) (by positivity))
    (fun s hs i h hlen => by
      have := count_floor O δ h i (by rw [hlen]; exact hu.trans (mem_Icc.1 hs).1)
      rwa [hlen] at this) n
  refine h.trans (le_of_eq (sum_congr rfl fun s hs => ?_))
  have ha : 0 < √(√(s : ℝ)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 (hpos s hs))
  have e : 2 * rad s ^ 2 * (√(s : ℝ) * √(√(s : ℝ)) / (8 * (Fintype.card Z : ℝ)))
      = √(s : ℝ) / (4 * (Fintype.card Z : ℝ)) := by
    unfold rad
    rw [div_pow, one_pow, Real.sq_sqrt ha.le]
    field_simp
    ring
  rw [e]
  ring

end Tail

/-! ### Locking a label despite ties (`eq:ast-allocation-rate`) -/

section Locking

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype B] [LinearOrder B]
  [Nonempty B]

/-- `max_b C_b(μ)`; equal to `C_*^ε(μ)` for the labels `(a, j)`, `j ∈ S(a)`. -/
noncomputable def witStar (Sup : B → Finset Z) (wit : B → Z) (ε : ℝ) (μ : Z → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun b => witC (Sup b) (wit b) ε μ

/-- The first label attaining `max_b C_b(μ)`. -/
noncomputable def bStar (Sup : B → Finset Z) (wit : B → Z) (ε : ℝ) (μ : Z → ℝ) : B :=
  firstLabel fun b => witC (Sup b) (wit b) ε μ = witStar Sup wit ε μ

lemma witC_le_witStar (Sup : B → Finset Z) (wit : B → Z) (ε : ℝ) (μ : Z → ℝ) (b : B) :
    witC (Sup b) (wit b) ε μ ≤ witStar Sup wit ε μ :=
  le_sup' (fun b => witC (Sup b) (wit b) ε μ) (mem_univ b)

lemma bStar_opt (Sup : B → Finset Z) (wit : B → Z) (ε : ℝ) (μ : Z → ℝ) :
    witC (Sup (bStar Sup wit ε μ)) (wit (bStar Sup wit ε μ)) ε μ = witStar Sup wit ε μ := by
  obtain ⟨b, -, hb⟩ := exists_mem_eq_sup' (univ_nonempty (α := B))
    (fun b => witC (Sup b) (wit b) ε μ)
  exact firstLabel_spec (P := fun b => witC (Sup b) (wit b) ε μ = witStar Sup wit ε μ)
    ⟨b, hb.symm⟩

variable {Sup : B → Finset Z} {wit : B → Z} {ε : ℝ}

/-- The gap `Δ` between the optimal and the inferior labels. -/
lemma exists_label_gap (Sup : B → Finset Z) (wit : B → Z) (ε : ℝ) (μ : Z → ℝ) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ b, witC (Sup b) (wit b) ε μ ≠ witStar Sup wit ε μ →
      witC (Sup b) (wit b) ε μ + Δ ≤ witStar Sup wit ε μ := by
  classical
  set F := (univ : Finset B).filter fun b => witC (Sup b) (wit b) ε μ ≠ witStar Sup wit ε μ
    with hF
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨1, one_pos, fun b hb => ?_⟩
    have : b ∈ F := by rw [hF, mem_filter]; exact ⟨mem_univ b, hb⟩
    rw [hFe] at this
    simp at this
  · obtain ⟨b0, hb0, hmin⟩ := exists_min_image F
      (fun b => witStar Sup wit ε μ - witC (Sup b) (wit b) ε μ) hFne
    have hne := (mem_filter.1 hb0).2
    have hlt : witC (Sup b0) (wit b0) ε μ < witStar Sup wit ε μ :=
      lt_of_le_of_ne (witC_le_witStar Sup wit ε μ b0) hne
    refine ⟨witStar Sup wit ε μ - witC (Sup b0) (wit b0) ε μ, by linarith, fun b hb => ?_⟩
    have hbF : b ∈ F := by rw [hF, mem_filter]; exact ⟨mem_univ b, hb⟩
    have := hmin b hbF
    linarith

/-- **Label locking and allocation rate for one epoch** (`eq:ast-allocation-rate`).  If the
epoch-start empirical vector `p` is within `r` of `μ`, with `2ω(r) ≤ h_k` and
`h_k + 2ω(r) + 2ξ_k < Δ`, then the sticky rule selects exactly `b_*`, and the epoch target
satisfies `f_{b_*}(μ, v^k) ≥ C - (γ_k D_ε + 2ω(r) + ξ_k)`. -/
theorem plan_lock (O : AllocOracle Sup wit ε) (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) {μ p : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {r Δ : ℝ} (hr : ∀ i, |μ i - p i| ≤ r) (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) (k : ℕ)
    (hΔ : ∀ b, witC (Sup b) (wit b) ε μ ≠ witStar Sup wit ε μ →
      witC (Sup b) (wit b) ε μ + Δ ≤ witStar Sup wit ε μ)
    (h1 : 2 * omega ε r ≤ hSched k) (h2 : hSched k + 2 * omega ε r + 2 * xiSched k < Δ) :
    planLab O k p = bStar Sup wit ε μ ∧
      witStar Sup wit ε μ - (gamSched k * log (4 / (1 - ε)) + 2 * omega ε r + xiSched k)
        ≤ witF (Sup (bStar Sup wit ε μ)) (wit (bStar Sup wit ε μ)) ε μ (planTgt O k p) := by
  have hξ := xiSched_pos k
  have hr' : ∀ i, |p i - μ i| ≤ r := fun i => by rw [abs_sub_comm]; exact hr i
  obtain ⟨C, hC⟩ : ∃ C, C = witStar Sup wit ε μ := ⟨_, rfl⟩
  rw [← hC] at hΔ ⊢
  -- consequences of the contract
  have hLle : ∀ c, O.L p (xiSched k) c ≤ C + omega ε r := by
    intro c
    have a1 := O.L_le p (xiSched k) c hp hξ
    have a2 := witF_le_witC (hSc c) hε0 hε1 (wit c) hp (O.w_mem p (xiSched k) c hp hξ)
    have a3 := witC_le_add_omega (hSc c) hε0 hε1 (wit c) hμ hp hr hr0 hr1
    have a4 := witC_le_witStar Sup wit ε μ c
    linarith
  have hUge : ∀ b, witC (Sup b) (wit b) ε μ - omega ε r ≤ O.U p (xiSched k) b := by
    intro b
    have a1 := O.le_U p (xiSched k) b hp hξ
    have a3 := witC_le_add_omega (hSc b) hε0 hε1 (wit b) hp hμ hr' hr0 hr1
    linarith
  have hUle : ∀ b, O.U p (xiSched k) b
      ≤ witC (Sup b) (wit b) ε μ + omega ε r + xiSched k := by
    intro b
    have a0 := O.gap p (xiSched k) b hp hξ
    have a1 := O.L_le p (xiSched k) b hp hξ
    have a2 := witF_le_witC (hSc b) hε0 hε1 (wit b) hp (O.w_mem p (xiSched k) b hp hξ)
    have a3 := witC_le_add_omega (hSc b) hε0 hε1 (wit b) hμ hp hr hr0 hr1
    linarith
  have hbs := bStar_opt Sup wit ε μ
  rw [← hC] at hbs
  have hmaxle : (univ.sup' univ_nonempty fun c => O.L p (xiSched k) c) ≤ C + omega ε r :=
    sup'_le _ _ fun c _ => hLle c
  have hmaxge : C - omega ε r - xiSched k
      ≤ univ.sup' univ_nonempty fun c => O.L p (xiSched k) c := by
    have a0 := O.gap p (xiSched k) (bStar Sup wit ε μ) hp hξ
    have a1 := hUge (bStar Sup wit ε μ)
    have a2 : O.L p (xiSched k) (bStar Sup wit ε μ)
        ≤ univ.sup' univ_nonempty fun c => O.L p (xiSched k) c :=
      le_sup' (fun c => O.L p (xiSched k) c) (mem_univ _)
    rw [hbs] at a1
    linarith
  have hlab : planLab O k p = bStar Sup wit ε μ := by
    unfold planLab bStar
    refine firstLabel_congr fun b => ?_
    rw [← hC]
    constructor
    · intro hpass
      by_contra hne
      have := hΔ b hne
      have := hUle b
      linarith
    · intro hopt
      have := hUge b
      rw [hopt] at this
      linarith
  refine ⟨hlab, ?_⟩
  -- allocation rate
  set bs := bStar Sup wit ε μ with hbsdef
  have hwmem := O.w_mem p (xiSched k) bs hp hξ
  have hD0 := log_four_div_nonneg hε0 hε1
  have b1 : witF (Sup bs) (wit bs) ε p (O.w p (xiSched k) bs)
      ≤ witF (Sup bs) (wit bs) ε μ (O.w p (xiSched k) bs) + omega ε r := by
    have := witF_le_add_omega (hSc bs) hε0 hε1 (wit bs) hwmem.1 hwmem.2.le hwmem.1 hμ hp hr
      (s := 0) (by simp) le_rfl (by linarith) (by linarith)
    rwa [add_zero] at this
  have b2 := O.L_le p (xiSched k) bs hp hξ
  have b3 := O.gap p (xiSched k) bs hp hξ
  have b4 := hUge bs
  rw [hbs] at b4
  have b5 : witF (Sup bs) (wit bs) ε μ (O.w p (xiSched k) bs) ≤ log (4 / (1 - ε)) := by
    have := witF_le_mul_log (hSc bs) hε0 hε1 (wit bs) hwmem.1 hμ
    rwa [hwmem.2, one_mul] at this
  have b6 := witF_superadd (hSc bs) hε0 hε1 (wit bs) (p := μ) hwmem.1
    (w' := fun _ => 1 / (Fintype.card Z : ℝ)) (fun _ => by positivity) hμ
    (sub_nonneg.2 (gamSched_le_one k)) (gamSched_pos k).le
  have b7 : 0 ≤ witF (Sup bs) (wit bs) ε μ (fun _ => 1 / (Fintype.card Z : ℝ)) :=
    witF_nonneg (wit bs) (fun _ => by positivity) hμ
  have b8 : planTgt O k p = fun i => (1 - gamSched k) * O.w p (xiSched k) bs i
      + gamSched k * (1 / (Fintype.card Z : ℝ)) := by
    unfold planTgt
    rw [hlab]
  rw [b8]
  have hγ0 := (gamSched_pos k).le
  have b9 := mul_nonneg hγ0 b7
  have b10 := mul_le_mul_of_nonneg_left b5 hγ0
  nlinarith

lemma tendsto_div_const_atTop {c : ℕ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => k / c) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * c, fun n hn => (Nat.le_div_iff_mul_le hc).2 hn⟩

lemma tendsto_hSched : Tendsto hSched atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
    (tendsto_div_const_atTop (by norm_num))

lemma tendsto_gamSched : Tendsto gamSched atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
    (tendsto_div_const_atTop (by norm_num))

lemma tendsto_xiSched : Tendsto xiSched atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
    (tendsto_atTop_atTop.2 fun b => ⟨b * 8, fun n hn => by
      have := (Nat.le_div_iff_mul_le (show 0 < 8 by norm_num)).2 hn
      omega⟩)

lemma tendsto_epochStart : Tendsto epochStart atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun n hn => by
    have := Nat.lt_two_pow_self (n := n)
    unfold epochStart
    omega⟩

/-- `ω_ε(r) ≤ √r / 4` for small `r > 0`. -/
lemma eventually_omega_le_sqrt (ε : ℝ) : ∀ᶠ r in 𝓝[>] (0 : ℝ), omega ε r ≤ √r / 4 := by
  have h1 : Tendsto (fun x : ℝ => log x * x ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have h2 : Tendsto (fun x : ℝ => √x) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have h3 : Tendsto (fun x : ℝ => √x * (1 + 2 * log (4 / (1 - ε))) - 2 * (log x * x ^ (1 / 2 : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
    have := (h2.mul_const (1 + 2 * log (4 / (1 - ε)))).sub (h1.const_mul 2)
    simpa using this
  have h4 : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      √x * (1 + 2 * log (4 / (1 - ε))) - 2 * (log x * x ^ (1 / 2 : ℝ)) < 1 / 4 :=
    h3.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [h4, self_mem_nhdsWithin] with x hx hx0
  have hx0' : (0 : ℝ) < x := hx0
  have hs : 0 < √x := Real.sqrt_pos.2 hx0'
  have hxx : x = √x * √x := (Real.mul_self_sqrt hx0'.le).symm
  rw [← Real.sqrt_eq_rpow] at hx
  have e : omega ε x = √x * (√x * (1 + 2 * log (4 / (1 - ε))) - 2 * (log x * √x)) := by
    unfold omega
    rw [one_div, log_inv]
    nth_rewrite 1 [hxx]
    ring
  rw [e]
  nlinarith

/-- `√(rad(2^k - 1)) ≤ 2 h_k`: the estimation radius at an epoch start against the tie
tolerance. -/
lemma sqrt_rad_le_hSched {k : ℕ} (hk : 1 ≤ k) : √(rad (epochStart k)) ≤ 2 * hSched k := by
  have ht1 : 1 ≤ epochStart k := by
    have := Nat.lt_two_pow_self (n := k)
    unfold epochStart
    omega
  have ht0 : (0 : ℝ) < (epochStart k : ℝ) := by exact_mod_cast ht1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = √(√(√(√(epochStart k : ℝ)))) := ⟨_, rfl⟩
  have hy0 : 0 < y := by
    rw [hy]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 ht0)))
  have hy16 : y ^ 16 = (epochStart k : ℝ) := by
    have e1 : y ^ 2 = √(√(√(epochStart k : ℝ))) := by rw [hy]; exact Real.sq_sqrt (by positivity)
    have e2 : √(√(√(epochStart k : ℝ))) ^ 2 = √(√(epochStart k : ℝ)) :=
      Real.sq_sqrt (by positivity)
    have e3 : √(√(epochStart k : ℝ)) ^ 2 = √(epochStart k : ℝ) := Real.sq_sqrt (by positivity)
    have e4 : √(epochStart k : ℝ) ^ 2 = (epochStart k : ℝ) := Real.sq_sqrt ht0.le
    calc y ^ 16 = (((y ^ 2) ^ 2) ^ 2) ^ 2 := by ring
      _ = (epochStart k : ℝ) := by rw [e1, e2, e3, e4]
  have hrad : √(rad (epochStart k)) = 1 / y := by
    unfold rad
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, hy]
  rw [hrad]
  -- `2^(k/16) ≤ 2 y`
  have hnat : (2 ^ (k / 16)) ^ 16 ≤ 65536 * epochStart k := by
    have h1 : (2 ^ (k / 16)) ^ 16 ≤ 2 ^ k := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self k 16)
    have h2 := epochStart_add_one k
    omega
  have hreal : ((2 : ℝ) ^ (k / 16)) ^ 16 ≤ (2 * y) ^ 16 := by
    have : (((2 ^ (k / 16)) ^ 16 : ℕ) : ℝ) ≤ ((65536 * epochStart k : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at this
    calc ((2 : ℝ) ^ (k / 16)) ^ 16 ≤ 65536 * (epochStart k : ℝ) := this
      _ = (2 * y) ^ 16 := by rw [mul_pow, hy16]; norm_num
  have hle : (2 : ℝ) ^ (k / 16) ≤ 2 * y :=
    le_of_pow_le_pow_left₀ (n := 16) (by norm_num) (by positivity) hreal
  have hp : (0 : ℝ) < 2 ^ (k / 16) := by positivity
  unfold hSched
  rw [one_div, one_div, inv_pow, ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hy0 hp]
  linarith

/-- **Eventual locking**: for every `η > 0`, from some epoch on, whenever the epoch-start
empirical vector is within `t_k^{-1/8}` of `μ`, the selected label is `b_*` and
`f_{b_*}(μ, v^k) ≥ C - η`. -/
theorem eventually_epoch_good (O : AllocOracle Sup wit ε) (hSc : ∀ b, (Sup b)ᶜ.Nonempty)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ} (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) {η : ℝ}
    (hη : 0 < η) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ p : Z → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
      (∀ i, |μ i - p i| ≤ rad (epochStart k)) →
      planLab O k p = bStar Sup wit ε μ ∧
        witStar Sup wit ε μ - η
          ≤ witF (Sup (bStar Sup wit ε μ)) (wit (bStar Sup wit ε μ)) ε μ (planTgt O k p) := by
  obtain ⟨Δ, hΔ0, hΔ⟩ := exists_label_gap Sup wit ε μ
  have hr : Tendsto (fun k => rad (epochStart k)) atTop (𝓝 0) :=
    tendsto_rad.comp tendsto_epochStart
  have hrpos : ∀ᶠ k in atTop, 0 < rad (epochStart k) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    refine rad_pos ?_
    have := Nat.lt_two_pow_self (n := k)
    unfold epochStart
    omega
  have hr' : Tendsto (fun k => rad (epochStart k)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hr, hrpos⟩
  have hω : Tendsto (fun k => omega ε (rad (epochStart k))) atTop (𝓝 0) := by
    have := ((omega_continuous ε).tendsto 0).comp hr
    rw [omega_zero] at this
    exact this
  have e1 : ∀ᶠ k in atTop, omega ε (rad (epochStart k)) ≤ √(rad (epochStart k)) / 4 :=
    hr'.eventually (eventually_omega_le_sqrt ε)
  have e2 : ∀ᶠ k in atTop, rad (epochStart k) ≤ 1 / 2 :=
    hr.eventually (eventually_le_nhds (by norm_num))
  have e3 : ∀ᶠ k in atTop,
      hSched k + 2 * omega ε (rad (epochStart k)) + 2 * xiSched k < Δ := by
    have := (tendsto_hSched.add (hω.const_mul 2)).add (tendsto_xiSched.const_mul 2)
    simp only [mul_zero, add_zero] at this
    exact this.eventually (eventually_lt_nhds hΔ0)
  have e4 : ∀ᶠ k in atTop,
      gamSched k * log (4 / (1 - ε)) + 2 * omega ε (rad (epochStart k)) + xiSched k < η := by
    have := ((tendsto_gamSched.mul_const (log (4 / (1 - ε)))).add (hω.const_mul 2)).add
      tendsto_xiSched
    simp only [mul_zero, zero_mul, add_zero] at this
    exact this.eventually (eventually_lt_nhds hη)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    ((((e1.and e2).and e3).and e4).and (hrpos.and (eventually_ge_atTop 1)))
  refine ⟨k₀, fun k hk p hp hclose => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5, a6⟩ := hk₀ k hk
  have a7 := sqrt_rad_le_hSched a6
  obtain ⟨hlab, hrate⟩ := plan_lock O hSc hε0 hε1 hμ hp hclose a5 a2 k hΔ (by linarith) a3
  exact ⟨hlab, by linarith⟩

end Locking

/-! ### Power of the certificate on the good event (`eq:ast-power`) -/

section Power

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype B] [LinearOrder B]
  [Nonempty B] {Sup : B → Finset Z} {wit : B → Z} {ε : ℝ}

open Stopped

lemma sq_le_two_pow : ∀ k : ℕ, (k + 1) ^ 2 ≤ 4 * 2 ^ k
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | k + 3 => by
      have := sq_le_two_pow (k + 2)
      have e : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by ring
      have h2 : (k + 3 + 1) ^ 2 ≤ 2 * (k + 2 + 1) ^ 2 := by nlinarith [Nat.zero_le k]
      rw [e]
      linarith

lemma epochOf_sq_le (u : ℕ) : epochOf (u * u) + 1 ≤ 2 * (u + 1) := by
  have h1 := sq_le_two_pow (epochOf (u * u))
  have h2 : 2 ^ epochOf (u * u) ≤ u * u + 1 := Nat.pow_log_le_self 2 (by omega)
  by_contra hcon
  have h3 : 2 * (u + 1) + 1 ≤ epochOf (u * u) + 1 := by omega
  have h4 := Nat.pow_le_pow_left h3 2
  nlinarith

lemma epoch_of_long {u t k₀ : ℕ} (ht : 2 * u + 1 ≤ t) (hu : 2 ^ k₀ ≤ u + 1) :
    k₀ ≤ epochOf t ∧ u ≤ epochStart (epochOf t) := by
  have h1 := lt_epochStart_add t
  have h2 := epochStart_add_one (epochOf t)
  have h3 : u + 1 < 2 ^ epochOf t := by omega
  refine ⟨?_, by omega⟩
  have h4 : 2 ^ k₀ < 2 ^ epochOf t := lt_of_le_of_lt hu h3
  exact ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h4).le

/-- **Power of the certificate** (`eq:ast-power` and the stopping condition that follows it).
Fix `η ∈ (0, C]`, `C = max_b C_b(μ)`.  There is `U₀`, not depending on `δ`, such that for
`u ≥ U₀`: at a history of length `u²` all of whose prefixes of length at least `u` have every
empirical mean within `t^{-1/8}` of its mean, the label in force is `b_*`, its statistic is at
least `(u² - (2u+1))(C - η) - u² η`, and the procedure stops as soon as this exceeds
`log(M(M-1)/δ) + 2 log(u² + 1)`. -/
theorem stop_of_good (O : AllocOracle Sup wit ε) (hwit : ∀ b, wit b ∈ Sup b)
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) {η : ℝ} (hη : 0 < η) (hηC : η ≤ witStar Sup wit ε μ) :
    ∃ U₀ : ℕ, ∀ (δ : ℝ) (u : ℕ), U₀ ≤ u → ∀ h : List Bool, h.length = u * u →
      (∀ g : List Bool, g <:+ h → u ≤ g.length →
        ∀ i, |emp (astSampler O δ) i g - μ i| ≤ rad g.length) →
      log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ)
          + 2 * log ((u : ℝ) * u + 1)
        ≤ ((u : ℝ) * u - (2 * u + 1)) * (witStar Sup wit ε μ - η) - (u : ℝ) * u * η →
      (astSampler O δ).stop h = true := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  have hMpos : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  obtain ⟨k₀, hk₀⟩ := eventually_epoch_good O hSc hε0 hε1 hμ' hη
  obtain ⟨d0, hd0, hω⟩ := Metric.continuousAt_iff.1 (omega_continuous ε).continuousAt η hη
  obtain ⟨i₀, -, hi₀⟩ := exists_min_image (univ : Finset Z) (fun i => min (μ i) (1 - μ i))
    univ_nonempty
  have hm0 : 0 < min (μ i₀) (1 - μ i₀) := lt_min (hμ i₀).1 (by linarith [(hμ i₀).2])
  -- eventual conditions on `u`
  have hsq : Tendsto (fun u : ℕ => u * u) atTop atTop :=
    tendsto_atTop_mono (fun u => Nat.le_mul_self u) tendsto_id
  have hT : Tendsto (fun u : ℕ => rad (u * u) + 8 * (Fintype.card Z : ℝ) / (u : ℝ)) atTop
      (𝓝 0) := by
    have := (tendsto_rad.comp hsq).add
      (tendsto_const_div_atTop_nhds_zero_nat (8 * (Fintype.card Z : ℝ)))
    simpa using this
  have ev1 : ∀ᶠ u : ℕ in atTop,
      rad (u * u) + 8 * (Fintype.card Z : ℝ) / (u : ℝ) < min d0 (1 / 2) :=
    hT.eventually (eventually_lt_nhds (lt_min hd0 (by norm_num)))
  have ev2 : ∀ᶠ u : ℕ in atTop, rad (u * u) < min (μ i₀) (1 - μ i₀) :=
    (tendsto_rad.comp hsq).eventually (eventually_lt_nhds hm0)
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.1
    ((ev1.and ev2).and (eventually_ge_atTop (max 3 (2 ^ k₀))))
  refine ⟨U₀, fun δ u hu h hlen hgood hthr => ?_⟩
  obtain ⟨⟨c1, c2⟩, c3⟩ := hU₀ u hu
  have hu3 : 3 ≤ u := (le_max_left _ _).trans c3
  have huk : 2 ^ k₀ ≤ u + 1 := ((le_max_right _ _).trans c3).trans (Nat.le_succ u)
  have hur : (3 : ℝ) ≤ u := by exact_mod_cast hu3
  obtain ⟨C, hC⟩ : ∃ C, C = witStar Sup wit ε μ := ⟨_, rfl⟩
  obtain ⟨bs, hbs⟩ : ∃ bs, bs = bStar Sup wit ε μ := ⟨_, rfl⟩
  rw [← hC] at hthr hηC
  rw [← hC, ← hbs] at hk₀
  have hq : 2 * u + 2 ≤ u * u := by nlinarith
  have hqr : ((h.length : ℕ) : ℝ) = (u : ℝ) * u := by rw [hlen]; push_cast; ring
  have hq0 : (0 : ℝ) < (u : ℝ) * u := by positivity
  cases h with
  | nil =>
    simp only [List.length_nil] at hlen
    omega
  | cons b g =>
    have hglen : g.length + 1 = u * u := by simpa using hlen
    -- E1: the label is locked and the targets have rate at least `C - η`
    have hE1 : ∀ g' : List Bool, g' <:+ b :: g → 2 * u + 1 ≤ g'.length →
        curLab O δ g' = bs ∧ C - η ≤ witF (Sup bs) (wit bs) ε μ (curTgt O δ g') := by
      intro g' hsuf hlong
      obtain ⟨hk, hst⟩ := epoch_of_long hlong huk
      have a1 := epochStart_epochOf_le g'.length
      have a2 := lt_epochStart_add g'.length
      have hd : g'.length - epochStart (epochOf g'.length) < 2 ^ epochOf g'.length := by omega
      have hlen' : g'.length = epochStart (epochOf g'.length)
          + (g'.length - epochStart (epochOf g'.length)) := by omega
      rw [curLab_epoch O δ hd hlen', curTgt_epoch O δ hd hlen']
      refine hk₀ _ hk _ (empVec_mem _ _) fun i => ?_
      have hl0 : (g'.drop (g'.length - epochStart (epochOf g'.length))).length
          = epochStart (epochOf g'.length) := by
        rw [List.length_drop]
        omega
      have := hgood _ ((List.drop_suffix _ g').trans hsuf) (by rw [hl0]; exact hst) i
      rw [hl0] at this
      rw [abs_sub_comm]
      exact this
    -- E2: information accumulated by the targets
    have hE2 : ∀ g' : List Bool, g' <:+ b :: g →
        ((g'.length : ℝ) - (2 * u + 1)) * (C - η)
          ≤ witF (Sup bs) (wit bs) ε μ (Wt O δ g') := by
      intro g'
      induction g' with
      | nil =>
        intro _
        have h0 : 0 ≤ witF (Sup bs) (wit bs) ε μ (Wt O δ []) :=
          witF_nonneg (wit bs) (Wt_nonneg O δ []) hμ'
        have h1 : (((([] : List Bool).length : ℕ) : ℝ) - (2 * u + 1)) * (C - η) ≤ 0 := by
          simp only [List.length_nil, Nat.cast_zero]
          nlinarith
        linarith
      | cons b' g'' ih =>
        intro hsuf
        have hsuf' : g'' <:+ b :: g := (List.suffix_cons b' g'').trans hsuf
        have ih' := ih hsuf'
        have hW : Wt O δ (b' :: g'') = fun i => 1 * Wt O δ g'' i + 1 * curTgt O δ g'' i := by
          funext i
          simp [Wt]
        have hsup := witF_superadd (hSc bs) hε0 hε1 (wit bs) (p := μ) (Wt_nonneg O δ g'')
          (fun i => (curTgt_pos O δ g'' i).le) hμ' zero_le_one zero_le_one
        rw [← hW, one_mul, one_mul] at hsup
        have hnn : 0 ≤ witF (Sup bs) (wit bs) ε μ (curTgt O δ g'') :=
          witF_nonneg (wit bs) (fun i => (curTgt_pos O δ g'' i).le) hμ'
        have hcast : (((b' :: g'').length : ℕ) : ℝ) = (g''.length : ℝ) + 1 := by
          simp
        rw [hcast]
        by_cases hl : 2 * u + 1 ≤ g''.length
        · obtain ⟨-, hrate⟩ := hE1 g'' hsuf' hl
          have e : ((g''.length : ℝ) + 1 - (2 * u + 1)) * (C - η)
              = ((g''.length : ℝ) - (2 * u + 1)) * (C - η) + (C - η) := by ring
          rw [e]
          linarith
        · have hl' : g''.length + 1 ≤ 2 * u + 1 := by omega
          have hl'' : (g''.length : ℝ) + 1 ≤ 2 * u + 1 := by exact_mod_cast hl'
          have h0 : 0 ≤ witF (Sup bs) (wit bs) ε μ (Wt O δ (b' :: g'')) :=
            witF_nonneg (wit bs) (Wt_nonneg O δ _) hμ'
          have h1 : ((g''.length : ℝ) + 1 - (2 * u + 1)) * (C - η) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          linarith
    -- E3: from the targets to the actual counts and empirical means
    obtain ⟨hh, hhdef⟩ : ∃ hh : List Bool, hh = b :: g := ⟨_, rfl⟩
    rw [← hhdef] at hgood hE2 hlen hqr
    have hgoodh := hgood hh List.suffix_rfl (by rw [hlen]; exact Nat.le_mul_self u)
    rw [hlen] at hgoodh
    have hNsum : ∑ i, (cnt (astSampler O δ) i hh : ℝ) = (u : ℝ) * u := by
      rw [← hqr]
      exact_mod_cast sum_cnt (astSampler O δ) hh
    have hWsum : ∑ i, Wt O δ hh i = (u : ℝ) * u := by rw [Wt_sum, hqr]
    have hw1 : ∑ i, (cnt (astSampler O δ) i hh : ℝ) / ((u : ℝ) * u) ≤ 1 := by
      rw [← sum_div, hNsum, div_self hq0.ne']
    have htrack := tracking_any O δ hh
    rw [hlen] at htrack
    have hs : ∑ i, |(cnt (astSampler O δ) i hh : ℝ) / ((u : ℝ) * u)
        - Wt O δ hh i / ((u : ℝ) * u)| ≤ 8 * (Fintype.card Z : ℝ) / (u : ℝ) := by
      have e : ∀ i, |(cnt (astSampler O δ) i hh : ℝ) / ((u : ℝ) * u)
          - Wt O δ hh i / ((u : ℝ) * u)|
          = |(cnt (astSampler O δ) i hh : ℝ) - Wt O δ hh i| / ((u : ℝ) * u) := fun i => by
        rw [← sub_div, abs_div, abs_of_pos hq0]
      simp only [e]
      rw [← sum_div, div_le_div_iff₀ hq0 (by linarith)]
      have hep : ((epochOf (u * u) : ℝ) + 1) ≤ 2 * ((u : ℝ) + 1) := by
        exact_mod_cast epochOf_sq_le u
      have h5 : ∑ i, |(cnt (astSampler O δ) i hh : ℝ) - Wt O δ hh i|
          ≤ 2 * (Fintype.card Z : ℝ) * (2 * ((u : ℝ) + 1)) :=
        htrack.trans (mul_le_mul_of_nonneg_left hep (by positivity))
      have h6 : 2 * (Fintype.card Z : ℝ) * (2 * ((u : ℝ) + 1)) * (u : ℝ)
          ≤ 8 * (Fintype.card Z : ℝ) * ((u : ℝ) * u) := by
        have := mul_le_mul_of_nonneg_left (show (u : ℝ) + 1 ≤ 2 * u by linarith)
          (show (0 : ℝ) ≤ 4 * (Fintype.card Z : ℝ) * u by positivity)
        nlinarith [this]
      have h7 := mul_le_mul_of_nonneg_right h5 (show (0 : ℝ) ≤ u by positivity)
      linarith
    have hradpos : 0 < rad (u * u) := rad_pos (by nlinarith)
    have hsmall := lt_min_iff.1 c1
    have hmod := witF_le_add_omega (hSc bs) hε0 hε1 (wit bs)
      (w := fun i => (cnt (astSampler O δ) i hh : ℝ) / ((u : ℝ) * u))
      (w' := fun i => Wt O δ hh i / ((u : ℝ) * u))
      (p := empVec (astSampler O δ) hh) (p' := μ)
      (fun i => by positivity) hw1 (fun i => div_nonneg (Wt_nonneg O δ hh i) hq0.le)
      (empVec_mem _ _) hμ' hgoodh hs (by positivity) (by positivity) hsmall.2.le
    have hωη : omega ε (rad (u * u) + 8 * (Fintype.card Z : ℝ) / (u : ℝ)) ≤ η := by
      have hpos : 0 < rad (u * u) + 8 * (Fintype.card Z : ℝ) / (u : ℝ) := by positivity
      have := hω (x := rad (u * u) + 8 * (Fintype.card Z : ℝ) / (u : ℝ))
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hsmall.1)
      rw [Real.dist_eq, omega_zero, sub_zero] at this
      exact (abs_lt.1 this).2.le
    have hsc1 : witF (Sup bs) (wit bs) ε μ (Wt O δ hh)
        = (u : ℝ) * u * witF (Sup bs) (wit bs) ε μ (fun i => Wt O δ hh i / ((u : ℝ) * u)) := by
      rw [← witF_smul (wit bs) μ _ hq0.le]
      congr 1
      funext i
      field_simp
    have hsc2 : witF (Sup bs) (wit bs) ε (empVec (astSampler O δ) hh)
          (fun i => (cnt (astSampler O δ) i hh : ℝ))
        = (u : ℝ) * u * witF (Sup bs) (wit bs) ε (empVec (astSampler O δ) hh)
          (fun i => (cnt (astSampler O δ) i hh : ℝ) / ((u : ℝ) * u)) := by
      rw [← witF_smul (wit bs) _ _ hq0.le]
      congr 1
      funext i
      field_simp
    have hE3 : ((u : ℝ) * u - (2 * u + 1)) * (C - η) - (u : ℝ) * u * η
        ≤ witF (Sup bs) (wit bs) ε (empVec (astSampler O δ) hh)
          (fun i => (cnt (astSampler O δ) i hh : ℝ)) := by
      have a1 := hE2 hh (by rw [hhdef])
      rw [hqr, hsc1] at a1
      rw [hsc2]
      have a2 : (u : ℝ) * u * witF (Sup bs) (wit bs) ε μ
            (fun i => Wt O δ hh i / ((u : ℝ) * u))
          ≤ (u : ℝ) * u * (witF (Sup bs) (wit bs) ε (empVec (astSampler O δ) hh)
            (fun i => (cnt (astSampler O δ) i hh : ℝ) / ((u : ℝ) * u)) + η) :=
        mul_le_mul_of_nonneg_left (by linarith) hq0.le
      linarith
    -- E4: the empirical means are interior
    have hint : ∀ i, 0 < empVec (astSampler O δ) hh i ∧ empVec (astSampler O δ) hh i < 1 := by
      intro i
      have a1 := abs_le.1 (hgoodh i)
      have a2 := hi₀ i (mem_univ i)
      have a3 := min_le_left (μ i) (1 - μ i)
      have a4 := min_le_right (μ i) (1 - μ i)
      unfold empVec at a1 ⊢
      constructor <;> linarith
    -- the stopping rule fires
    rw [hhdef] at hint hE3
    rw [stop_cons_iff]
    refine ⟨⟨u, hglen⟩, fun z hz => ?_⟩
    have hlab : curLab O δ g = bs :=
      (hE1 g (List.suffix_cons b g) (by omega)).1
    rw [hlab] at hz ⊢
    have hstat := witF_le_pairF ⟨wit bs, hwit bs⟩ (hSc bs) hε0 hε1 hint
      (hwit bs) (w := fun i => (cnt (astSampler O δ) i (b :: g) : ℝ))
      (fun i => Nat.cast_nonneg _) hz
    have hcl : ∀ i, log ((cnt (astSampler O δ) i (b :: g) : ℝ) + 1)
        ≤ log ((u : ℝ) * u + 1) := by
      intro i
      refine Real.log_le_log (by positivity) ?_
      have := cnt_le_length (astSampler O δ) i (b :: g)
      have h' : (cnt (astSampler O δ) i (b :: g) : ℝ) ≤ ((b :: g).length : ℝ) := by
        exact_mod_cast this
      rw [hhdef] at hqr
      linarith
    unfold certThr certStat
    have := hcl (wit bs)
    have := hcl z
    unfold empVec at hstat hE3
    linarith

end Power

/-! ### Finite expectation and the matching upper rate -/

section Expectation

/-- The estimation tail on `[⌊√T⌋, ⌊√T⌋²]` is `O(T^{-2})`. -/
lemma tail_sum_le {M T : ℕ} (hM : 1 ≤ M) (hT : 1 ≤ T) :
    ∑ s ∈ Icc (Nat.sqrt T) (Nat.sqrt T * Nat.sqrt T),
        2 * (M : ℝ) * exp (-(√(s : ℝ) / (4 * (M : ℝ))))
      ≤ 128 * (M : ℝ) * (48 * (M : ℝ)) ^ 12 / (T : ℝ) ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u, u = Nat.sqrt T := ⟨_, rfl⟩
  rw [← hu]
  have hu1 : 1 ≤ u := by rw [hu]; exact Nat.sqrt_pos.2 hT
  have hle : u * u ≤ T := by rw [hu]; exact Nat.sqrt_le T
  have hlt : T < (u + 1) * (u + 1) := by rw [hu]; exact Nat.lt_succ_sqrt T
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hur : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = √(u : ℝ) / (4 * (M : ℝ)) := ⟨_, rfl⟩
  have hy0 : 0 < y := by
    rw [hy]
    exact div_pos (Real.sqrt_pos.2 (by linarith)) (by positivity)
  have hterm : ∀ s ∈ Icc u (u * u),
      2 * (M : ℝ) * exp (-(√(s : ℝ) / (4 * (M : ℝ)))) ≤ 2 * (M : ℝ) * exp (-y) := by
    intro s hs
    have h1 : (u : ℝ) ≤ s := by exact_mod_cast (mem_Icc.1 hs).1
    have h2 := Real.sqrt_le_sqrt h1
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
    rw [neg_le_neg_iff, hy]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hcard : ((Icc u (u * u)).card : ℝ) ≤ T := by
    rw [Nat.card_Icc]
    have : u * u + 1 - u ≤ T := by omega
    exact_mod_cast this
  have hsum : ∑ s ∈ Icc u (u * u), 2 * (M : ℝ) * exp (-(√(s : ℝ) / (4 * (M : ℝ))))
      ≤ T * (2 * (M : ℝ) * exp (-y)) := by
    calc ∑ s ∈ Icc u (u * u), 2 * (M : ℝ) * exp (-(√(s : ℝ) / (4 * (M : ℝ))))
        ≤ ∑ _s ∈ Icc u (u * u), 2 * (M : ℝ) * exp (-y) := sum_le_sum hterm
      _ = ((Icc u (u * u)).card : ℝ) * (2 * (M : ℝ) * exp (-y)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ T * (2 * (M : ℝ) * exp (-y)) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hexp : exp (-y) ≤ (48 * (M : ℝ)) ^ 12 / (u : ℝ) ^ 6 := by
    have h12 : (y / 12) ^ 12 ≤ exp y := by
      have := add_one_le_exp (y / 12)
      calc (y / 12) ^ 12 ≤ (exp (y / 12)) ^ 12 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 12
        _ = exp y := by
            rw [← exp_nat_mul]
            congr 1
            push_cast
            ring
    have e : (y / 12) ^ 12 = (u : ℝ) ^ 6 / (48 * (M : ℝ)) ^ 12 := by
      have hs : √(u : ℝ) ^ 12 = (u : ℝ) ^ 6 := by
        calc √(u : ℝ) ^ 12 = (√(u : ℝ) ^ 2) ^ 6 := by ring
          _ = (u : ℝ) ^ 6 := by rw [Real.sq_sqrt (by positivity)]
      rw [hy, div_div, div_pow, hs]
      congr 1
      ring
    rw [e, div_le_iff₀ (by positivity)] at h12
    rw [exp_neg, ← one_div, div_le_div_iff₀ (exp_pos y) (by positivity)]
    linarith
  have hT3 : (T : ℝ) ^ 3 ≤ 64 * (u : ℝ) ^ 6 := by
    have h4 : (T : ℝ) ≤ 4 * (u : ℝ) ^ 2 := by
      have : T ≤ 4 * u ^ 2 := by nlinarith
      exact_mod_cast this
    calc (T : ℝ) ^ 3 ≤ (4 * (u : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h4 3
      _ = 64 * (u : ℝ) ^ 6 := by ring
  refine hsum.trans ?_
  have hu6 : 0 < (u : ℝ) ^ 6 := by positivity
  have hA : (0 : ℝ) < (48 * (M : ℝ)) ^ 12 := by positivity
  calc (T : ℝ) * (2 * (M : ℝ) * exp (-y))
      ≤ T * (2 * (M : ℝ) * ((48 * (M : ℝ)) ^ 12 / (u : ℝ) ^ 6)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity))
          (by positivity)
    _ ≤ 128 * (M : ℝ) * (48 * (M : ℝ)) ^ 12 / (T : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have e2 : (T : ℝ) * (2 * (M : ℝ) * ((48 * (M : ℝ)) ^ 12 / (u : ℝ) ^ 6)) * (T : ℝ) ^ 2
            = 2 * (M : ℝ) * (48 * (M : ℝ)) ^ 12 * ((T : ℝ) ^ 3 / (u : ℝ) ^ 6) := by
          field_simp
        rw [e2]
        have h64 : (T : ℝ) ^ 3 / (u : ℝ) ^ 6 ≤ 64 := by
          rw [div_le_iff₀ hu6]
          exact hT3
        calc 2 * (M : ℝ) * (48 * (M : ℝ)) ^ 12 * ((T : ℝ) ^ 3 / (u : ℝ) ^ 6)
            ≤ 2 * (M : ℝ) * (48 * (M : ℝ)) ^ 12 * 64 :=
              mul_le_mul_of_nonneg_left h64 (by positivity)
          _ = 128 * (M : ℝ) * (48 * (M : ℝ)) ^ 12 := by ring

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype B] [LinearOrder B]
  [Nonempty B] {Sup : B → Finset Z} {wit : B → Z} {ε : ℝ}

open Stopped

/-- **Tail of the stopping time.**  Fix `η₀ > 0`.  There is `T₁`, not depending on `δ`, such
that for every `T ≥ T₁` with `log(M(M-1)/δ) ≤ C T / (1 + η₀)`,
`P_μ(τ_δ > T) ≤ 128 M (48M)^{12} / T²`. -/
theorem prob_not_stopped_le (O : AllocOracle Sup wit ε) (hwit : ∀ b, wit b ∈ Sup b)
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) (hC : 0 < witStar Sup wit ε μ) {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ T₁ : ℕ, 1 ≤ T₁ ∧ ∀ (δ : ℝ) (T : ℕ), T₁ ≤ T →
      log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ)
        ≤ witStar Sup wit ε μ * T / (1 + η₀) →
      prob (astSampler O δ) μ T (stopSet (astSampler O δ))ᶜ
        ≤ 128 * (Fintype.card Z : ℝ) * (48 * (Fintype.card Z : ℝ)) ^ 12 / (T : ℝ) ^ 2 := by
  obtain ⟨C, hCdef⟩ : ∃ C, C = witStar Sup wit ε μ := ⟨_, rfl⟩
  rw [← hCdef] at hC ⊢
  obtain ⟨c1, hc1⟩ : ∃ c1, c1 = C / (1 + η₀) := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hc1lt : c1 < C := by
    rw [hc1, div_lt_iff₀ (by linarith)]
    nlinarith
  obtain ⟨η, hηdef⟩ : ∃ η, η = (C - c1) / 4 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith
  have hηC : η ≤ C := by rw [hηdef]; linarith
  obtain ⟨m, hmdef⟩ : ∃ m, m = (C - c1) / 2 := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; linarith
  obtain ⟨U₀, hU₀⟩ := stop_of_good O hwit hSc hε0 hε1 hμ hη (by rw [← hCdef]; exact hηC)
  rw [← hCdef] at hU₀
  have hM : 1 ≤ Fintype.card Z := Fintype.card_pos
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : ℕ, U₁ = max (max U₀ (25 * Fintype.card Z ^ 2))
      (max 1 ⌈(4 + 5 * C) / m⌉₊) := ⟨_, rfl⟩
  have hU1 : 1 ≤ U₁ := by rw [hU₁]; exact (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨U₁ * U₁, Nat.one_le_iff_ne_zero.2 (by positivity), fun δ T hT hβ => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u, u = Nat.sqrt T := ⟨_, rfl⟩
  have huU : U₁ ≤ u := by rw [hu]; exact Nat.le_sqrt.2 hT
  have hu0 : U₀ ≤ u := by
    rw [hU₁] at huU
    exact ((le_max_left _ _).trans (le_max_left _ _)).trans huU
  have hu25 : 25 * Fintype.card Z ^ 2 ≤ u := by
    rw [hU₁] at huU
    exact ((le_max_right _ _).trans (le_max_left _ _)).trans huU
  have hu1 : 1 ≤ u := hU1.trans huU
  have hum : (4 + 5 * C) / m ≤ u := by
    have h1 : ⌈(4 + 5 * C) / m⌉₊ ≤ u := by
      rw [hU₁] at huU
      exact ((le_max_right _ _).trans (le_max_right _ _)).trans huU
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hle : u * u ≤ T := by rw [hu]; exact Nat.sqrt_le T
  have hlt : T < (u + 1) * (u + 1) := by rw [hu]; exact Nat.lt_succ_sqrt T
  have hT1 : 1 ≤ T := le_trans (by nlinarith) hle
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (u : ℝ) := ⟨_, rfl⟩
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hu1
  -- the threshold condition at `u`
  have hthr : log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ)
        + 2 * log ((u : ℝ) * u + 1)
      ≤ ((u : ℝ) * u - (2 * u + 1)) * (C - η) - (u : ℝ) * u * η := by
    rw [← hx]
    have hTx : (T : ℝ) ≤ x * x + 2 * x := by
      have : T ≤ u * u + 2 * u := by nlinarith
      rw [hx]
      exact_mod_cast this
    have hβ' : log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ)
        ≤ c1 * (x * x + 2 * x) := by
      have : C * (T : ℝ) / (1 + η₀) = c1 * T := by rw [hc1]; ring
      rw [this] at hβ
      exact hβ.trans (mul_le_mul_of_nonneg_left hTx hc1pos.le)
    have hlog : log (x * x + 1) ≤ 2 * x := by
      have h1 : log (x * x + 1) ≤ log ((x + 1) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      have h2 : log ((x + 1) ^ 2) = 2 * log (x + 1) := by
        rw [Real.log_pow]
        norm_num
      have h3 : log (x + 1) ≤ x := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x + 1 by linarith)
        linarith
      linarith
    have hmx : 4 + 5 * C ≤ m * x := by
      rw [div_le_iff₀ hm] at hum
      rw [hx]
      linarith
    have p1 : (4 + 5 * C) * x ≤ m * x * x := mul_le_mul_of_nonneg_right hmx (by linarith)
    have p2 : c1 * x ≤ C * x := mul_le_mul_of_nonneg_right hc1lt.le (by linarith)
    have p3 : C * 1 ≤ C * x := mul_le_mul_of_nonneg_left hx1 hC.le
    have p4 : 0 ≤ η * x := mul_nonneg hη.le (by linarith)
    rw [hηdef] at p4 ⊢
    rw [hmdef] at p1
    nlinarith
  -- on the good event the run has stopped
  rw [prob_inter_leaves]
  have hsub : (stopSet (astSampler O δ))ᶜ ∩ ↑(leaves (astSampler O δ) T [])
      ⊆ badSet (astSampler O δ) μ u (u * u) := by
    rintro l ⟨hns, hl⟩
    by_contra hbad
    have hgood : ∀ g : List Bool, g <:+ l → u ≤ g.length → g.length ≤ u * u →
        ∀ i, |emp (astSampler O δ) i g - μ i| ≤ rad g.length := by
      intro g hg h1 h2 i
      by_contra hc
      exact hbad (ever_iff_exists_suffix.2 ⟨g, hg, h1, h2, i, not_le.1 hc⟩)
    have hns' : ¬ (astSampler O δ).stop l = true := hns
    have hlen := length_of_mem_leaves (astSampler O δ) T [] l hl hns'
    simp only [List.length_nil, zero_add] at hlen
    have hhlen : (l.drop (T - u * u)).length = u * u := by
      rw [List.length_drop]
      omega
    have hsuf : l.drop (T - u * u) <:+ l := List.drop_suffix _ _
    have hstop := hU₀ δ u hu0 (l.drop (T - u * u)) hhlen
      (fun g hg hug i => hgood g (hg.trans hsuf) hug (hg.length_le.trans_eq hhlen) i) hthr
    by_cases he : l.drop (T - u * u) = l
    · rw [he] at hstop
      exact hns' hstop
    · have := not_stop_of_mem_leaves (astSampler O δ) T [] l hl _ List.nil_suffix hsuf he
      rw [hstop] at this
      exact Bool.noConfusion this
  refine (prob_mono_set (astSampler O δ) hμ T hsub).trans ?_
  refine (estimation_tail O δ hμ u (u * u) hu25 T).trans ?_
  rw [hu]
  exact tail_sum_le hM hT1

/-- **Finite expectation with an explicit leading term.**  For every `η₀ > 0` there is a
constant `K₀`, not depending on `δ`, with
`E_μ[τ_δ ∧ n] ≤ max(0, (1 + η₀) log(M(M-1)/δ) / C) + K₀` for every `δ` and `n`. -/
theorem expTime_le (O : AllocOracle Sup wit ε) (hwit : ∀ b, wit b ∈ Sup b)
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) (hC : 0 < witStar Sup wit ε μ) {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ K₀ : ℝ, ∀ (δ : ℝ) (n : ℕ),
      expTime (astSampler O δ) μ n
        ≤ max 0 ((1 + η₀) * log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ)
            / witStar Sup wit ε μ) + K₀ := by
  obtain ⟨T₁, hT₁, htail⟩ := prob_not_stopped_le O hwit hSc hε0 hε1 hμ hC hη₀
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = 128 * (Fintype.card Z : ℝ) * (48 * (Fintype.card Z : ℝ)) ^ 12 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  rw [← hK] at htail
  have hsummable : Summable fun T : ℕ => 1 / (T : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  refine ⟨T₁ + 1 + K * ∑' T : ℕ, 1 / (T : ℝ) ^ 2, fun δ n => ?_⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ,
      β = log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ) := ⟨_, rfl⟩
  rw [← hβ]
  obtain ⟨C, hCdef⟩ : ∃ C, C = witStar Sup wit ε μ := ⟨_, rfl⟩
  rw [← hCdef] at hC htail ⊢
  obtain ⟨Ts, hTs⟩ : ∃ Ts : ℕ, Ts = max T₁ ⌈(1 + η₀) * β / C⌉₊ := ⟨_, rfl⟩
  have hTs1 : (Ts : ℝ) ≤ max 0 ((1 + η₀) * β / C) + T₁ + 1 := by
    have h1 : (⌈(1 + η₀) * β / C⌉₊ : ℝ) ≤ max 0 ((1 + η₀) * β / C) + 1 := by
      rcases le_or_gt ((1 + η₀) * β / C) 0 with h | h
      · rw [Nat.ceil_eq_zero.2 h]
        have := le_max_left (0 : ℝ) ((1 + η₀) * β / C)
        simp only [Nat.cast_zero]
        linarith
      · have := Nat.ceil_lt_add_one h.le
        have := le_max_right 0 ((1 + η₀) * β / C)
        linarith
    have h2 : (Ts : ℝ) ≤ (T₁ : ℝ) + ⌈(1 + η₀) * β / C⌉₊ := by
      rw [hTs]
      have : max T₁ ⌈(1 + η₀) * β / C⌉₊ ≤ T₁ + ⌈(1 + η₀) * β / C⌉₊ :=
        max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
      exact_mod_cast this
    linarith
  have hp : ∀ T : ℕ, Ts ≤ T →
      prob (astSampler O δ) μ T (stopSet (astSampler O δ))ᶜ ≤ K / (T : ℝ) ^ 2 := by
    intro T hT
    have hT1 : T₁ ≤ T := (by rw [hTs]; exact le_max_left _ _ : T₁ ≤ Ts).trans hT
    have hT2 : (1 + η₀) * β / C ≤ T := by
      have : ⌈(1 + η₀) * β / C⌉₊ ≤ T :=
        (by rw [hTs]; exact le_max_right _ _ : ⌈(1 + η₀) * β / C⌉₊ ≤ Ts).trans hT
      exact (Nat.le_ceil _).trans (by exact_mod_cast this)
    refine htail δ T hT1 ?_
    rw [← hβ]
    rw [div_le_iff₀ hC] at hT2
    rw [le_div_iff₀ (by linarith)]
    linarith
  have key : ∀ n : ℕ, expTime (astSampler O δ) μ n
      ≤ (min n Ts : ℕ) + K * ∑ T ∈ range n, 1 / (T : ℝ) ^ 2 := by
    intro n
    induction n with
    | zero => simp [expTime, lik]
    | succ n ih =>
      rw [expTime_succ, sum_range_succ, mul_add]
      have hstep : prob (astSampler O δ) μ n (stopSet (astSampler O δ))ᶜ
          ≤ ((min (n + 1) Ts : ℕ) : ℝ) - ((min n Ts : ℕ) : ℝ) + K * (1 / (n : ℝ) ^ 2) := by
        have hnn : 0 ≤ K * (1 / (n : ℝ) ^ 2) := by positivity
        rcases lt_or_ge n Ts with h | h
        · have e1 : min (n + 1) Ts = n + 1 := min_eq_left h
          have e2 : min n Ts = n := min_eq_left h.le
          rw [e1, e2]
          push_cast
          have := prob_le_one (astSampler O δ) hμ n (stopSet (astSampler O δ))ᶜ
          linarith
        · have e1 : min (n + 1) Ts = Ts := min_eq_right (h.trans (Nat.le_succ n))
          have e2 : min n Ts = Ts := min_eq_right h
          rw [e1, e2]
          have := hp n h
          rw [mul_one_div]
          linarith
      linarith
  have h1 := key n
  have h2 : ∑ T ∈ range n, 1 / (T : ℝ) ^ 2 ≤ ∑' T : ℕ, 1 / (T : ℝ) ^ 2 :=
    hsummable.sum_le_tsum _ fun T _ => by positivity
  have h3 : ((min n Ts : ℕ) : ℝ) ≤ Ts := by exact_mod_cast min_le_right n Ts
  have h4 := mul_le_mul_of_nonneg_left h2 hK0
  linarith

end Expectation

/-! ### Correctness, almost-sure termination and the limit of `thm:ast-main` -/

section Final

variable {Z B : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype B] [LinearOrder B]
  [Nonempty B] {Sup : B → Finset Z} {wit : B → Z} {ε : ℝ}

open Stopped

/-- The label returned at a stopped history: the label in force for the last draw. -/
noncomputable def astLabel (O : AllocOracle Sup wit ε) (δ : ℝ) (l : List Bool) : B :=
  curLab O δ l.tail

lemma ast_certifies (O : AllocOracle Sup wit ε) (δ : ℝ) (hwit : ∀ b, wit b ∈ Sup b)
    (l : List Bool) (hs : (astSampler O δ).stop l = true) :
    certifies (astSampler O δ) ε δ (Sup (astLabel O δ l)) l := by
  cases l with
  | nil =>
    rw [stop_nil] at hs
    exact Bool.noConfusion hs
  | cons b g => exact ⟨wit (curLab O δ g), hwit _, ((stop_cons_iff O δ b g).1 hs).2⟩

/-- **`δ`-correctness of the procedure**, at every interior parameter and for every oracle:
the probability of stopping with an `ε`-incorrect answer is at most `δ`. -/
theorem ast_correct (O : AllocOracle Sup wit ε) {δ : ℝ} (hδ : 0 < δ)
    (hwit : ∀ b, wit b ∈ Sup b) (hε0 : 0 ≤ ε) {lam : Z → ℝ}
    (hlam : ∀ z, 0 < lam z ∧ lam z < 1) :
    probInf (astSampler O δ) lam {l | lam ∈ Alt (Sup (astLabel O δ l)) ε} ≤ δ :=
  certified_stopping_correct (astSampler O δ) hlam hε0 hδ (fun l => Sup (astLabel O δ l))
    (ast_certifies O δ hwit)

/-- A sampler with bounded expected stopping time stops almost surely:
`P(τ < ∞, H_τ ∈ A) + P(τ < ∞, H_τ ∉ A) = 1`. -/
lemma probInf_add_compl (S : Sampler Z) {μ : Z → ℝ} (hμ : ∀ z, 0 < μ z ∧ μ z < 1) {Bd : ℝ}
    (hB : ∀ n, expTime S μ n ≤ Bd) (A : Set (List Bool)) :
    probInf S μ A + probInf S μ Aᶜ = 1 := by
  have ht : Tendsto (fun n => prob S μ n (stopSet S)ᶜ) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => prob_nonneg S hμ n _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat Bd)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn0]
    exact (prob_not_stop_mul_le S hμ n).trans (hB n)
  have hs := (tendsto_probInf S hμ A).add (tendsto_probInf S hμ Aᶜ)
  have hs' : Tendsto (fun n => prob S μ n (A ∩ stopSet S) + prob S μ n (Aᶜ ∩ stopSet S)) atTop
      (𝓝 (1 - 0)) := by
    refine (tendsto_const_nhds.sub ht).congr fun n => ?_
    have := prob_split S μ n A
    linarith
  rw [sub_zero] at hs'
  exact tendsto_nhds_unique hs hs'

lemma card_ge_two (hwit : ∀ b, wit b ∈ Sup b) (hSc : ∀ b, (Sup b)ᶜ.Nonempty) :
    (2 : ℝ) ≤ Fintype.card Z := by
  obtain ⟨b⟩ := ‹Nonempty B›
  obtain ⟨z, hz⟩ := hSc b
  have hne : wit b ≠ z := fun h => (mem_compl.1 hz) (h ▸ hwit b)
  have : 1 < Fintype.card Z := Fintype.one_lt_card_iff.2 ⟨wit b, z, hne⟩
  exact_mod_cast this

/-- **Finite expected stopping time** at every interior instance with `max_b C_b(μ) > 0`, for
every value of the confidence parameter. -/
theorem ast_finite_expectation (O : AllocOracle Sup wit ε) (hwit : ∀ b, wit b ∈ Sup b)
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) (hC : 0 < witStar Sup wit ε μ) (δ : ℝ) :
    ∃ Bd : ℝ, ∀ n, expTime (astSampler O δ) μ n ≤ Bd := by
  obtain ⟨K₀, hK₀⟩ := expTime_le O hwit hSc hε0 hε1 hμ hC (η₀ := 1) one_pos
  exact ⟨_, fun n => hK₀ δ n⟩

/-- **The procedure returns an `ε`-correct answer with probability at least `1 - δ`** (it
stops almost surely and the certified answer is wrong with probability at most `δ`). -/
theorem ast_returns_correct (O : AllocOracle Sup wit ε) (hwit : ∀ b, wit b ∈ Sup b)
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) {lam : Z → ℝ}
    (hlam : ∀ i, 0 < lam i ∧ lam i < 1) (hC : 0 < witStar Sup wit ε lam) {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ probInf (astSampler O δ) lam {l | lam ∉ Alt (Sup (astLabel O δ l)) ε} := by
  obtain ⟨Bd, hB⟩ := ast_finite_expectation O hwit hSc hε0 hε1 hlam hC δ
  have h1 := probInf_add_compl (astSampler O δ) hlam hB
    {l | lam ∈ Alt (Sup (astLabel O δ l)) ε}
  have h2 := ast_correct O hδ hwit hε0 hlam
  have h3 : {l : List Bool | lam ∈ Alt (Sup (astLabel O δ l)) ε}ᶜ
      = {l | lam ∉ Alt (Sup (astLabel O δ l)) ε} := rfl
  rw [h3] at h1
  linarith

/-- **Matching upper rate** (`limsup_{δ↓0} E_μ τ_δ / log(1/δ) ≤ 1 / max_b C_b(μ)`): for every
`c > 1 / max_b C_b(μ)`, eventually `E_μ τ_δ / log(1/δ) ≤ c`. -/
theorem ast_upper_rate (O : AllocOracle Sup wit ε) (hwit : ∀ b, wit b ∈ Sup b)
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε < 1) {μ : Z → ℝ}
    (hμ : ∀ i, 0 < μ i ∧ μ i < 1) (hC : 0 < witStar Sup wit ε μ) {c : ℝ}
    (hc : 1 / witStar Sup wit ε μ < c) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), expTimeInf (astSampler O δ) μ / log (1 / δ) ≤ c := by
  obtain ⟨C, hCdef⟩ : ∃ C, C = witStar Sup wit ε μ := ⟨_, rfl⟩
  have hK := fun η₀ hη₀ => expTime_le O hwit hSc hε0 hε1 hμ hC (η₀ := η₀) hη₀
  rw [← hCdef] at hC hc hK
  have hcC : 1 < c * C := by rwa [div_lt_iff₀ hC] at hc
  obtain ⟨η₀, hη₀def⟩ : ∃ η₀, η₀ = (c * C - 1) / 2 := ⟨_, rfl⟩
  have hη₀ : 0 < η₀ := by rw [hη₀def]; linarith
  have hlt : (1 + η₀) / C < c := by
    rw [div_lt_iff₀ hC, hη₀def]
    linarith
  obtain ⟨K₀, hK₀⟩ := hK η₀ hη₀
  have hM2 := card_ge_two hwit hSc
  have hMM : 0 < (Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  obtain ⟨a, ha⟩ : ∃ a, a = log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1)) :=
    ⟨_, rfl⟩
  -- the limit in `L = log(1/δ)`
  have hlim : Tendsto (fun L : ℝ => (1 + η₀) / C + ((1 + η₀) * a / C + K₀) / L) atTop
      (𝓝 ((1 + η₀) / C)) := by
    have h1 : Tendsto (fun L : ℝ => ((1 + η₀) * a / C + K₀) / L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using tendsto_const_nhds.add h1
  have hev1 : ∀ᶠ L : ℝ in atTop, (1 + η₀) / C + ((1 + η₀) * a / C + K₀) / L < c :=
    hlim.eventually (eventually_lt_nhds hlt)
  have hev2 : ∀ᶠ L : ℝ in atTop, max 0 (-a) < L := eventually_gt_atTop _
  have hLtend : Tendsto (fun δ : ℝ => log (1 / δ)) (𝓝[>] 0) atTop := by
    have : Tendsto (fun δ : ℝ => -log δ) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
    refine this.congr fun δ => ?_
    rw [one_div, log_inv]
  filter_upwards [hLtend.eventually hev1, hLtend.eventually hev2, self_mem_nhdsWithin]
    with δ h1 h2 hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  obtain ⟨L, hL⟩ : ∃ L, L = log (1 / δ) := ⟨_, rfl⟩
  rw [← hL] at h1 h2 ⊢
  have hL0 : 0 < L := lt_of_le_of_lt (le_max_left _ _) h2
  have haL : 0 < a + L := by
    have := lt_of_le_of_lt (le_max_right 0 (-a)) h2
    linarith
  have hβ : log ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) - 1) / δ) = a + L := by
    rw [log_div hMM.ne' hδ0.ne', ha, hL, one_div, log_inv]
    ring
  have hbound : expTimeInf (astSampler O δ) μ ≤ (1 + η₀) * (a + L) / C + K₀ := by
    refine ciSup_le fun n => ?_
    have := hK₀ δ n
    rw [hβ, max_eq_right (by positivity)] at this
    exact this
  rw [div_le_iff₀ hL0]
  have e : ((1 + η₀) / C + ((1 + η₀) * a / C + K₀) / L) * L
      = (1 + η₀) * (a + L) / C + K₀ := by
    field_simp
    ring
  have := mul_lt_mul_of_pos_right h1 hL0
  rw [e] at this
  linarith

/-- `max_b C_b(μ) ≤ max_b C_{a(b)}(μ)`, with equality when every inside terminal of every
labelled support is the witness of some label with the same support (the labels are all pairs
`(a, j)`, `j ∈ S(a)`): the one-witness reduction. -/
theorem witStar_eq_charStar (hwit : ∀ b, wit b ∈ Sup b) (hSc : ∀ b, (Sup b)ᶜ.Nonempty)
    (hfull : ∀ b, ∀ j ∈ Sup b, ∃ b', Sup b' = Sup b ∧ wit b' = j) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) :
    witStar Sup wit ε μ = charStar Sup ε μ := by
  have hμ' : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := fun i => ⟨(hμ i).1.le, (hμ i).2.le⟩
  apply le_antisymm
  · refine sup'_le _ _ fun b _ => ?_
    exact (witC_le_charRate (hSc b) hε0 hε1 (wit b) hμ').trans (charRate_le_charStar Sup ε μ b)
  · refine sup'_le _ _ fun b _ => ?_
    obtain ⟨j, hj, hmax⟩ := exists_max_image (Sup b) μ ⟨wit b, hwit b⟩
    obtain ⟨b', hS', hw'⟩ := hfull b j hj
    have h1 := witC_eq_charRate (S := Sup b) ⟨wit b, hwit b⟩ (hSc b) hε0 hε1 hμ hj hmax
    have h2 := witC_le_witStar Sup wit ε μ b'
    rw [hS', hw'] at h2
    linarith

/-- **`thm:ast-main`, equality of the rate, for a system of witness labels.**

Labels `b` carry a proper support `Sup b` and a witness `wit b ∈ Sup b`, and every inside
terminal is the witness of a label with the same support (`hfull`).  `Dom` is the parameter
domain; `hdense` says that restricting alternatives to `Dom` does not change the information
infima, and `hpos` that `C_*^ε > 0` on `Dom`.  Then for every oracle `O` meeting the contract
`eq:ast-oracle`, the procedure `astSampler O δ` with answer `astLabel O δ` is `δ`-correct on
`Dom` (used through `ast_returns_correct`), has finite expected stopping time, and at every
interior `μ` with `C_*^ε(μ) > 0`
`lim_{δ↓0} E_μ τ_δ / log(1/δ) = 1 / C_*^ε(μ)`. -/
theorem ast_main_labels (O : AllocOracle Sup wit ε) (hwit : ∀ b, wit b ∈ Sup b)
    (hSc : ∀ b, (Sup b)ᶜ.Nonempty)
    (hfull : ∀ b, ∀ j ∈ Sup b, ∃ b', Sup b' = Sup b ∧ wit b' = j) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (Dom : Set (Z → ℝ))
    (hdense : ∀ (μ : Z → ℝ) (b : B), ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt (Sup b) ε,
      lam ∈ Dom ∧ infoCost w μ lam < infoRate (Sup b) ε w μ + η)
    (hpos : ∀ lam ∈ Dom, (∀ i, 0 < lam i ∧ lam i < 1) → 0 < charStar Sup ε lam)
    {μ : Z → ℝ} (hμ : ∀ i, 0 < μ i ∧ μ i < 1) (hC : 0 < charStar Sup ε μ) :
    Tendsto (fun δ : ℝ => expTimeInf (astSampler O δ) μ / log (1 / δ)) (𝓝[>] 0)
      (𝓝 (1 / charStar Sup ε μ)) := by
  have heq := fun (lam : Z → ℝ) (hlam : ∀ i, 0 < lam i ∧ lam i < 1) =>
    witStar_eq_charStar hwit hSc hfull hε0 hε1 hlam
  have hCw : 0 < witStar Sup wit ε μ := by rw [heq μ hμ]; exact hC
  have hB : ∀ δ : ℝ, ∃ Bd : ℝ, ∀ n, expTime (astSampler O δ) μ n ≤ Bd := fun δ =>
    ast_finite_expectation O hwit hSc hε0 hε1 hμ hCw δ
  have hcorr : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ lam ∈ Dom, (∀ z, 0 < lam z ∧ lam z < 1) →
      1 - δ ≤ probInf (astSampler O δ) lam {l | lam ∉ Alt (Sup (astLabel O δ l)) ε} := by
    intro δ hδ0 _ lam hD hlam
    exact ast_returns_correct O hwit hSc hε0 hε1 hlam (by rw [heq lam hlam]; exact hpos lam hD hlam)
      hδ0
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hmid : (a + 1 / charStar Sup ε μ) / 2 < 1 / charStar Sup ε μ := by linarith
    have h := lower_bound_multi_answer Sup hSc hε0 hε1 hμ hC (fun δ => astSampler O δ)
      (fun δ => astLabel O δ) Dom (hdense μ) hcorr hB hmid
    filter_upwards [h] with δ hδ
    linarith
  · have hmid : 1 / witStar Sup wit ε μ < (a + 1 / charStar Sup ε μ) / 2 := by
      rw [heq μ hμ]
      linarith
    have h := ast_upper_rate O hwit hSc hε0 hε1 hμ hCw hmid
    filter_upwards [h] with δ hδ
    linarith

end Final

/-! ### `thm:ast-main` for a family of root actions -/

section Actions

variable {Z A : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype A] [Nonempty A]

open Stopped

/-- For `ε > 0` and supports covering `Z`, `C_*^ε > 0` at every interior parameter
(`Γ ≥ 0`). -/
lemma charStar_pos_of_cover (SupA : A → Finset Z) (hS : ∀ a, (SupA a).Nonempty)
    (hSc : ∀ a, (SupA a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ SupA a) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {lam : Z → ℝ} (hlam : ∀ i, 0 < lam i ∧ lam i < 1) :
    0 < charStar SupA ε lam := by
  obtain ⟨zs, -, hzs⟩ := exists_max_image (univ : Finset Z) lam univ_nonempty
  obtain ⟨a, ha⟩ := hcov zs
  refine lt_of_lt_of_le ?_ (charRate_le_charStar SupA ε lam a)
  rw [charRate_pos_iff (hS a) (hSc a) hε0.le hε1 hlam]
  have h1 : (SupA a)ᶜ.sup' (hSc a) lam ≤ lam zs := sup'_le _ _ fun z _ => hzs z (mem_univ z)
  have h2 := le_val (hS a) lam ha
  linarith

/-- On `𝒟_0 = {Γ > 0}`, `C_*^0 > 0`. -/
lemma charStar_pos_of_exactDomain (SupA : A → Finset Z) (hS : ∀ a, (SupA a).Nonempty)
    (hSc : ∀ a, (SupA a)ᶜ.Nonempty) {lam : Z → ℝ} (hlam : ∀ i, 0 < lam i ∧ lam i < 1)
    (hD : lam ∈ exactDomain SupA) : 0 < charStar SupA 0 lam := by
  obtain ⟨a, y, hy, hlt⟩ := hD
  refine lt_of_lt_of_le ?_ (charRate_le_charStar SupA 0 lam a)
  rw [charRate_pos_iff (hS a) (hSc a) le_rfl zero_lt_one hlam, add_zero]
  have h1 : (SupA a)ᶜ.sup' (hSc a) lam < lam y :=
    (sup'_lt_iff _).2 fun z hz => hlt z (mem_compl.1 hz)
  exact h1.trans_le (le_val (hS a) lam hy)

/-- Common form of the two cases of `thm:ast-main`.  The procedure is `astSampler O δ` for the
witness labels `{(a, j) : j ∈ S(a)}` (in a fixed enumeration order) and an oracle `O` meeting
`eq:ast-oracle` (one exists by `exists_allocOracle`); the answer is the action of the label in
force at the last draw. -/
theorem ast_main_aux (SupA : A → Finset Z) (hS : ∀ a, (SupA a).Nonempty)
    (hSc : ∀ a, (SupA a)ᶜ.Nonempty) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (Dom : Set (Z → ℝ))
    (hdense : ∀ (μ : Z → ℝ) (a : A), ∀ w ∈ simplex Z, ∀ η > 0, ∃ lam ∈ Alt (SupA a) ε,
      lam ∈ Dom ∧ infoCost w μ lam < infoRate (SupA a) ε w μ + η)
    (hpos : ∀ lam ∈ Dom, (∀ i, 0 < lam i ∧ lam i < 1) → 0 < charStar SupA ε lam) :
    ∃ (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A),
      (∀ δ : ℝ, 0 < δ → ∀ lam : Z → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
        probInf (S δ) lam {l | lam ∈ Alt (SupA (dec δ l)) ε} ≤ δ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ lam ∈ Dom, (∀ i, 0 < lam i ∧ lam i < 1) →
        1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (SupA (dec δ l)) ε}) ∧
      ∀ μ ∈ Dom, (∀ i, 0 < μ i ∧ μ i < 1) →
        (∀ δ : ℝ, ∃ Bd : ℝ, ∀ n, expTime (S δ) μ n ≤ Bd) ∧
        Tendsto (fun δ : ℝ => expTimeInf (S δ) μ / log (1 / δ)) (𝓝[>] 0)
          (𝓝 (1 / charStar SupA ε μ)) := by
  classical
  let B : Type _ := {q : A × Z // q.2 ∈ SupA q.1}
  let _ : LinearOrder B :=
    LinearOrder.lift' (Fintype.equivFin B) (Fintype.equivFin B).injective
  have : Nonempty B := by
    obtain ⟨a⟩ := ‹Nonempty A›
    obtain ⟨j, hj⟩ := hS a
    exact ⟨⟨(a, j), hj⟩⟩
  let Sup : B → Finset Z := fun b => SupA b.1.1
  let wit : B → Z := fun b => b.1.2
  have hwit : ∀ b, wit b ∈ Sup b := fun b => b.2
  have hScB : ∀ b, (Sup b)ᶜ.Nonempty := fun b => hSc b.1.1
  have hfull : ∀ b, ∀ j ∈ Sup b, ∃ b', Sup b' = Sup b ∧ wit b' = j := fun b j hj =>
    ⟨⟨(b.1.1, j), hj⟩, rfl, rfl⟩
  have hcs : ∀ lam : Z → ℝ, charStar Sup ε lam = charStar SupA ε lam := by
    intro lam
    apply le_antisymm
    · exact sup'_le _ _ fun b _ => charRate_le_charStar SupA ε lam b.1.1
    · refine sup'_le _ _ fun a _ => ?_
      obtain ⟨j, hj⟩ := hS a
      exact charRate_le_charStar Sup ε lam ⟨(a, j), hj⟩
  have hw : ∀ lam : Z → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
      witStar Sup wit ε lam = charStar SupA ε lam := fun lam hlam => by
    rw [witStar_eq_charStar hwit hScB hfull hε0 hε1 hlam, hcs]
  obtain ⟨O⟩ := exists_allocOracle Sup wit hScB hε0 hε1
  refine ⟨fun δ => astSampler O δ, fun δ l => (astLabel O δ l).1.1, ?_, ?_, ?_⟩
  · intro δ hδ lam hlam
    exact ast_correct O hδ hwit hε0 hlam
  · intro δ hδ lam hD hlam
    exact ast_returns_correct O hwit hScB hε0 hε1 hlam
      (by rw [hw lam hlam]; exact hpos lam hD hlam) hδ
  · intro μ hD hμ
    have hC := hpos μ hD hμ
    refine ⟨fun δ => ast_finite_expectation O hwit hScB hε0 hε1 hμ
      (by rw [hw μ hμ]; exact hC) δ, ?_⟩
    have h := ast_main_labels O hwit hScB hfull hε0 hε1 Dom
      (fun μ b => hdense μ b.1.1)
      (fun lam hl hlam => by rw [hcs]; exact hpos lam hl hlam) hμ (by rw [hcs]; exact hC)
    rw [hcs] at h
    exact h

/-- **`thm:ast-main` "One inside witness and Bernoulli information limit", the limit, for
`0 < ε < 1`.**  For a finite family of root actions with proper nonempty supports covering
`Z`, there is a procedure (a family of deterministic adaptive samplers `S δ` with answers
`dec δ`) such that:

* at every interior parameter `λ` and every `δ > 0`, it stops with an `ε`-incorrect answer
  with probability at most `δ`, and stops with an answer that is not `ε`-incorrect with
  probability at least `1 - δ`;
* at every interior `μ` the expected stopping time is finite and
  `lim_{δ↓0} E_μ τ_δ / log(1/δ) = 1 / C_*^ε(μ)`.

The lower-bound half of the limit holds for every uniformly correct family
(`Stopped.ast_lower_main`); the upper half is `ast_upper_rate` for this procedure. -/
theorem ast_main (SupA : A → Finset Z) (hS : ∀ a, (SupA a).Nonempty)
    (hSc : ∀ a, (SupA a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ SupA a) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A),
      (∀ δ : ℝ, 0 < δ → ∀ lam : Z → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
        probInf (S δ) lam {l | lam ∈ Alt (SupA (dec δ l)) ε} ≤ δ ∧
        1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (SupA (dec δ l)) ε}) ∧
      ∀ μ : Z → ℝ, (∀ i, 0 < μ i ∧ μ i < 1) →
        (∀ δ : ℝ, ∃ Bd : ℝ, ∀ n, expTime (S δ) μ n ≤ Bd) ∧
        Tendsto (fun δ : ℝ => expTimeInf (S δ) μ / log (1 / δ)) (𝓝[>] 0)
          (𝓝 (1 / charStar SupA ε μ)) := by
  obtain ⟨S, dec, h1, h2, h3⟩ := ast_main_aux SupA hS hSc hε0.le hε1 Set.univ
    (fun μ a w _ η hη => alt_dense_univ (hSc a) hε0.le hε1 w μ hη)
    (fun lam _ hlam => charStar_pos_of_cover SupA hS hSc hcov hε0 hε1 hlam)
  exact ⟨S, dec, fun δ hδ lam hlam => ⟨h1 δ hδ lam hlam, h2 δ hδ lam (Set.mem_univ _) hlam⟩,
    fun μ hμ => h3 μ (Set.mem_univ _) hμ⟩

/-- **`thm:ast-main`, the limit, for exact identification (`ε = 0`)** on the domain
`𝒟_0 = {Γ > 0}`: the procedure is `δ`-correct on `𝒟_0`, and at every interior `μ ∈ 𝒟_0` its
expected stopping time is finite with
`lim_{δ↓0} E_μ τ_δ / log(1/δ) = 1 / C_*^0(μ)`. -/
theorem ast_main_exact (SupA : A → Finset Z) (hS : ∀ a, (SupA a).Nonempty)
    (hSc : ∀ a, (SupA a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ SupA a) :
    ∃ (S : ℝ → Sampler Z) (dec : ℝ → List Bool → A),
      (∀ δ : ℝ, 0 < δ → ∀ lam : Z → ℝ, (∀ i, 0 < lam i ∧ lam i < 1) →
        probInf (S δ) lam {l | lam ∈ Alt (SupA (dec δ l)) 0} ≤ δ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ lam ∈ exactDomain SupA, (∀ i, 0 < lam i ∧ lam i < 1) →
        1 - δ ≤ probInf (S δ) lam {l | lam ∉ Alt (SupA (dec δ l)) 0}) ∧
      ∀ μ ∈ exactDomain SupA, (∀ i, 0 < μ i ∧ μ i < 1) →
        (∀ δ : ℝ, ∃ Bd : ℝ, ∀ n, expTime (S δ) μ n ≤ Bd) ∧
        Tendsto (fun δ : ℝ => expTimeInf (S δ) μ / log (1 / δ)) (𝓝[>] 0)
          (𝓝 (1 / charStar SupA 0 μ)) :=
  ast_main_aux SupA hS hSc le_rfl zero_lt_one (exactDomain SupA)
    (fun μ a w _ η hη => alt_dense_exactDomain SupA hcov a (hSc a) le_rfl zero_lt_one w μ hη)
    (fun lam hD hlam => charStar_pos_of_exactDomain SupA hS hSc hlam hD)

end Actions

end JointRootCert
