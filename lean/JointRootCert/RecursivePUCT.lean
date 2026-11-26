/-
Noisy recursive PUCT: terminal coverage and certification
(Appendix `app:noisy-puct-proofs`).

Manuscript results covered:

* `thm:v35local` (Uniform local PUCT revisit bound under changing values):
  `local_puct_core`, `local_puct_revisit`.
* `thm:v35dag` (Pathwise terminal coverage under recursive local PUCT):
  `edge_step`, `path_coverage`, `puct_terminal_coverage`, `terminal_sampled_unboundedly`.
* `lem:v35width` (Anytime coverage and a usable width bound): `hoeffding_tape_coverage`
  (the probability bound), `running_box_covers`, `running_box_width`,
  `running_box_width_bt`, `puctRadius_le_puctB` (the deterministic part).
* `thm:v35horizon` (High-probability on-policy PUCT certification horizon):
  `puct_horizon`, `puct_horizon_full`, `exists_horizon`.
* `cor:v35poly` (Polynomial accuracy dependence at fixed depth): `horizon_condition_of_poly`,
  `poly_horizon` (explicit polynomial thresholds only; the oracle-substitution clause is
  not formalized).
* `prop:v35rootrates` (Positive-variance root PUCT: almost-sure square-root counts):
  `pullCount_unbounded`, `root_puct_upper`, `root_puct_best_arm`, `root_puct_sqrt_rates_ae`.
* `ce:v35prior` (Zero prior at one internal edge prevents terminal coverage):
  `zero_prior_never_selected`, `zero_prior_run_exists`.
* `thm:puct-noisy-main` (Support-sensitive certification under recursive PUCT):
  `rectCert_le_of_width`, `puct_noisy_certification`, `puct_noisy_main`.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert

open Finset

/-! ### Counting steps -/

section Count

open Classical in
/-- Number of steps `s < t` at which `p s` holds. -/
noncomputable def stepCount (p : ℕ → Prop) (t : ℕ) : ℕ := ((range t).filter p).card

lemma stepCount_mono_time (p : ℕ → Prop) {s t : ℕ} (h : s ≤ t) :
    stepCount p s ≤ stepCount p t := by
  classical
  unfold stepCount
  exact card_le_card (filter_subset_filter _ (range_mono h))

lemma stepCount_mono_pred {p q : ℕ → Prop} (t : ℕ) (h : ∀ s < t, p s → q s) :
    stepCount p t ≤ stepCount q t := by
  classical
  unfold stepCount
  refine card_le_card (fun x hx => ?_)
  rw [mem_filter, mem_range] at hx ⊢
  exact ⟨hx.1, h x hx.1 hx.2⟩

lemma stepCount_le (p : ℕ → Prop) (t : ℕ) : stepCount p t ≤ t := by
  classical
  unfold stepCount
  exact (card_filter_le _ _).trans (card_range t).le

lemma stepCount_of_forall {p : ℕ → Prop} (t : ℕ) (h : ∀ s < t, p s) : stepCount p t = t := by
  classical
  unfold stepCount
  rw [filter_true_of_mem (fun x hx => h x (mem_range.mp hx)), card_range]

lemma stepCount_succ_of_pos {p : ℕ → Prop} {t : ℕ} (h : p t) :
    stepCount p (t + 1) = stepCount p t + 1 := by
  classical
  unfold stepCount
  rw [range_add_one, filter_insert]
  simp only [h, ↓reduceIte]
  rw [card_insert_of_notMem (by simp)]

lemma stepCount_succ_of_neg {p : ℕ → Prop} {t : ℕ} (h : ¬ p t) :
    stepCount p (t + 1) = stepCount p t := by
  classical
  unfold stepCount
  rw [range_add_one, filter_insert]
  simp only [h, ↓reduceIte]

lemma stepCount_lt_of_lt {p : ℕ → Prop} {s t : ℕ} (hs : p s) (hst : s < t) :
    stepCount p s < stepCount p t := by
  have h1 := stepCount_succ_of_pos hs
  have h2 := stepCount_mono_time p (show s + 1 ≤ t from hst)
  omega

/-- A set of steps `≤ s0` that all satisfy `p` has at most `stepCount p s0 + 1` elements. -/
lemma card_le_stepCount_succ (p : ℕ → Prop) (F : Finset ℕ) (s0 : ℕ)
    (h : ∀ s ∈ F, s ≤ s0 ∧ p s) : F.card ≤ stepCount p s0 + 1 := by
  classical
  unfold stepCount
  refine (card_le_card (t := insert s0 ((range s0).filter p)) (fun s hs => ?_)).trans
    (card_insert_le _ _)
  obtain ⟨h1, h2⟩ := h s hs
  rcases h1.eq_or_lt with rfl | hlt
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr hlt, h2⟩)

/-- All but at most `m` of the `p`-steps before `t` have at least `m` earlier `p`-steps. -/
lemma stepCount_le_card_window (p : ℕ → Prop) (t m : ℕ) (W : Finset ℕ)
    (hW : ∀ s < t, p s → m ≤ stepCount p s → s ∈ W) : stepCount p t ≤ W.card + m := by
  classical
  set L := (range t).filter (fun s => p s ∧ stepCount p s < m) with hL
  have hLm : L.card ≤ m := by
    have := card_le_card_of_injOn (s := L) (t := range m) (fun s => stepCount p s)
      (fun s hs => by
        rw [mem_coe, hL, mem_filter] at hs
        exact mem_coe.mpr (mem_range.mpr hs.2.2))
      (fun a ha b hb hab => by
        rw [mem_coe, hL, mem_filter] at ha hb
        simp only at hab
        rcases lt_trichotomy a b with hlt | heq | hgt
        · have := stepCount_lt_of_lt ha.2.1 hlt
          omega
        · exact heq
        · have := stepCount_lt_of_lt hb.2.1 hgt
          omega)
    simpa using this
  have hsub : (range t).filter p ⊆ W ∪ L := by
    intro s hs
    rw [mem_filter, mem_range] at hs
    by_cases hm : m ≤ stepCount p s
    · exact mem_union_left _ (hW s hs.1 hs.2 hm)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr hs.1, hs.2, not_le.mp hm⟩)
  have h1 : stepCount p t ≤ (W ∪ L).card := by
    unfold stepCount
    exact card_le_card hsub
  have h2 := card_union_le W L
  omega

end Count

/-! ### The local revisit bound (`thm:v35local`) -/

section Local

variable {ι : Type*}

/-- **Local PUCT revisit bound, embedded form (core of `thm:v35local`).**

A node with action set `A` and weights `lam j > 0` is *active* at some of the global steps
(`act s`); at an active step it selects `sel s ∈ A`.  Its local clock is
`stepCount act s` and the count of action `j` is `stepCount (fun r => act r ∧ sel r = j) s`.
At every active step `s < t` the selected action maximises
`Q j s + lam j * √(local clock) / (1 + count j)` over `j ∈ A`, with `Q j s ∈ [0,1]`
otherwise arbitrary.  If the local clock `n` at time `t` satisfies `16 ≤ n`,
`128 ≤ lam i ² n` and `16 Λ² ≤ n`, then action `i` has been selected at least
`lam i / (8 √2) * √n` times.  Taking `act` identically true gives the statement on the
node's own clock (`local_puct_revisit`). -/
theorem local_puct_core (A : Finset ι) (lam : ι → ℝ) (hlam : ∀ j ∈ A, 0 < lam j)
    (act : ℕ → Prop) (sel : ℕ → ι) (Q : ι → ℕ → ℝ) (t : ℕ)
    (hsel : ∀ s < t, act s → sel s ∈ A)
    (hQ : ∀ s < t, act s → ∀ j ∈ A, 0 ≤ Q j s ∧ Q j s ≤ 1)
    (hrule : ∀ s < t, act s → ∀ j ∈ A,
      Q j s + lam j * √(stepCount act s : ℝ) /
          (1 + (stepCount (fun r => act r ∧ sel r = j) s : ℝ)) ≤
        Q (sel s) s + lam (sel s) * √(stepCount act s : ℝ) /
          (1 + (stepCount (fun r => act r ∧ sel r = sel s) s : ℝ)))
    {i : ι} (hi : i ∈ A)
    (h16 : (16 : ℝ) ≤ stepCount act t) (hi128 : 128 ≤ lam i ^ 2 * (stepCount act t : ℝ))
    (hΛ : 16 * (∑ j ∈ A, lam j) ^ 2 ≤ (stepCount act t : ℝ)) :
    lam i / (8 * √2) * √(stepCount act t : ℝ) ≤
      (stepCount (fun r => act r ∧ sel r = i) t : ℝ) := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  set n := stepCount act t with hn
  set r := √(n : ℝ) with hr
  have hnpos : (0 : ℝ) < n := by linarith
  have hr2 : r ^ 2 = n := Real.sq_sqrt hnpos.le
  have hrpos : 0 < r := Real.sqrt_pos.mpr hnpos
  set c := √(2 : ℝ) with hc
  have hc2 : c ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by norm_num)
  have hli := hlam i hi
  have h8 : 8 * c ≤ lam i * r := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, hc2, hr2]
    linarith
  set a := lam i * r / c with ha
  have ha8 : 8 ≤ a := by
    rw [ha, le_div_iff₀ hcpos]
    exact h8
  have hαa : lam i / (8 * c) * r = a / 8 := by
    rw [ha]
    field_simp
  rw [hαa] at hcon
  -- the window: active steps whose local clock is at least `m = ⌈n / 2⌉`
  set m := (n + 1) / 2 with hm
  set W := (range t).filter (fun s => act s ∧ m ≤ stepCount act s) with hWdef
  have hWcard : n ≤ W.card + m :=
    stepCount_le_card_window act t m W
      (fun s hs h1 h2 => mem_filter.mpr ⟨mem_range.mpr hs, h1, h2⟩)
  have hm_le : (m : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
    have : (m : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := Nat.cast_div_le
    simpa using this
  have hm_ge : (n : ℝ) / 2 ≤ m := by
    have : n ≤ 2 * m := by omega
    have : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast this
    linarith
  -- at every window step the selected action has a large exploration bonus
  have hstep : ∀ s ∈ W, 3 * (1 + (stepCount (fun r => act r ∧ sel r = sel s) s : ℝ)) <
      lam (sel s) * r := by
    intro s hs
    rw [hWdef, mem_filter, mem_range] at hs
    obtain ⟨hst, hact, hms⟩ := hs
    have hselA := hsel s hst hact
    have hlj := hlam _ hselA
    set ns := stepCount act s with hns
    have hns_le : (ns : ℝ) ≤ n := by exact_mod_cast stepCount_mono_time act hst.le
    have hns_ge : (n : ℝ) / 2 ≤ ns := hm_ge.trans (by exact_mod_cast hms)
    have hsq1 : r / c ≤ √(ns : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, hr2, hc2]
      exact hns_ge
    have hsq2 : √(ns : ℝ) ≤ r := Real.sqrt_le_sqrt hns_le
    have hNi : (stepCount (fun r => act r ∧ sel r = i) s : ℝ) < a / 8 :=
      lt_of_le_of_lt (by exact_mod_cast stepCount_mono_time _ hst.le) hcon
    have hbi : 4 < lam i * √(ns : ℝ) / (1 + (stepCount (fun r => act r ∧ sel r = i) s : ℝ)) := by
      rw [lt_div_iff₀ (by positivity)]
      have h1 : a ≤ lam i * √(ns : ℝ) := by
        have := mul_le_mul_of_nonneg_left hsq1 hli.le
        rw [ha]
        calc lam i * r / c = lam i * (r / c) := by ring
          _ ≤ _ := this
      linarith
    have hr1 := hrule s hst hact i hi
    have hQi := (hQ s hst hact i hi).1
    have hQj := (hQ s hst hact _ hselA).2
    have hbj : 3 < lam (sel s) * √(ns : ℝ) /
        (1 + (stepCount (fun r => act r ∧ sel r = sel s) s : ℝ)) := by linarith
    rw [lt_div_iff₀ (by positivity)] at hbj
    have := mul_le_mul_of_nonneg_left hsq2 hlj.le
    linarith
  -- so each action is selected at most `lam j * r / 3` times inside the window
  have hfib : ∀ j ∈ A, ((W.filter (fun s => sel s = j)).card : ℝ) ≤ lam j * r / 3 := by
    intro j hj
    have hlj := hlam j hj
    rcases (W.filter (fun s => sel s = j)).eq_empty_or_nonempty with he | hne
    · rw [he, card_empty, Nat.cast_zero]
      positivity
    · set s0 := (W.filter (fun s => sel s = j)).max' hne with hs0
      have hs0mem := max'_mem _ hne
      rw [← hs0, mem_filter] at hs0mem
      have hcard : (W.filter (fun s => sel s = j)).card ≤
          stepCount (fun r => act r ∧ sel r = j) s0 + 1 := by
        refine card_le_stepCount_succ _ _ s0 (fun s hs => ⟨le_max' _ s hs, ?_⟩)
        rw [mem_filter, hWdef, mem_filter] at hs
        exact ⟨hs.1.2.1, hs.2⟩
      have hcardR : ((W.filter (fun s => sel s = j)).card : ℝ) ≤
          (stepCount (fun r => act r ∧ sel r = j) s0 : ℝ) + 1 := by exact_mod_cast hcard
      have h3 := hstep s0 hs0mem.1
      rw [hs0mem.2] at h3
      linarith
  have hsum : (W.card : ℝ) ≤ (∑ j ∈ A, lam j) * r / 3 := by
    have hmaps : ∀ s ∈ W, sel s ∈ A := by
      intro s hs
      rw [hWdef, mem_filter, mem_range] at hs
      exact hsel s hs.1 hs.2.1
    rw [card_eq_sum_card_fiberwise hmaps]
    push_cast
    calc ∑ j ∈ A, ((W.filter (fun s => sel s = j)).card : ℝ) ≤ ∑ j ∈ A, lam j * r / 3 :=
          sum_le_sum hfib
      _ = (∑ j ∈ A, lam j) * r / 3 := by rw [sum_mul, sum_div]
  have hΛ0 : 0 ≤ ∑ j ∈ A, lam j := sum_nonneg (fun j hj => (hlam j hj).le)
  have h4Λ : 4 * (∑ j ∈ A, lam j) ≤ r := by
    by_contra h
    rw [not_le] at h
    have := mul_lt_mul'' h h hrpos.le hrpos.le
    nlinarith
  have hWn : (n : ℝ) ≤ W.card + m := by exact_mod_cast hWcard
  nlinarith

/-- Number of selections of action `i` strictly before local time `n`. -/
noncomputable def pullCount (sel : ℕ → ι) (i : ι) (n : ℕ) : ℕ := stepCount (fun r => sel r = i) n

/-- The counts sum to the local time, `∑_i N_i(n) = n` (`eq:v35onevertex`). -/
lemma sum_pullCount [Fintype ι] (sel : ℕ → ι) (n : ℕ) : ∑ i, pullCount sel i n = n := by
  classical
  have h := card_eq_sum_card_fiberwise (f := sel) (s := range n) (t := univ)
    (fun s _ => mem_univ _)
  rw [card_range] at h
  refine (h.trans (sum_congr rfl (fun i _ => ?_))).symm
  unfold pullCount stepCount
  congr

/-- `λ_* = min_i λ_i` over a finite action set (`1` for the empty set). -/
noncomputable def lamMin (A : Finset ι) (lam : ι → ℝ) : ℝ :=
  if h : A.Nonempty then A.inf' h lam else 1

/-- The threshold `T_0 = ⌈max {16, 128 / λ_*², 16 Λ²}⌉` of `eq:v35threshold`. -/
noncomputable def puctThreshold (A : Finset ι) (lam : ι → ℝ) : ℕ :=
  ⌈max 16 (max (128 / lamMin A lam ^ 2) (16 * (∑ j ∈ A, lam j) ^ 2))⌉₊

lemma puctThreshold_spec (A : Finset ι) (lam : ι → ℝ) (hlam : ∀ j ∈ A, 0 < lam j) {x : ℝ}
    (hx : (puctThreshold A lam : ℝ) ≤ x) {i : ι} (hi : i ∈ A) :
    16 ≤ x ∧ 128 ≤ lam i ^ 2 * x ∧ 16 * (∑ j ∈ A, lam j) ^ 2 ≤ x := by
  have h := (Nat.le_ceil _).trans hx
  have hA : A.Nonempty := ⟨i, hi⟩
  have hmin_pos : 0 < lamMin A lam := by
    simp only [lamMin, hA, ↓reduceDIte, lt_inf'_iff]
    exact hlam
  have hmin_le : lamMin A lam ≤ lam i := by
    simp only [lamMin, hA, ↓reduceDIte]
    exact inf'_le lam hi
  have h1 : 16 ≤ x := (le_max_left _ _).trans h
  have h2 : 128 / lamMin A lam ^ 2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans h
  have h3 : 16 * (∑ j ∈ A, lam j) ^ 2 ≤ x :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans h
  refine ⟨h1, ?_, h3⟩
  rw [div_le_iff₀ (by positivity)] at h2
  have hsq : lamMin A lam ^ 2 ≤ lam i ^ 2 := pow_le_pow_left₀ hmin_pos.le hmin_le 2
  have hx0 : 0 ≤ x := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hx0]

/-- **Uniform local PUCT revisit bound under changing values (Theorem `thm:v35local`).**

`k ≥ 0` actions with weights `lam i > 0`; `sel n` is the action selected at local time `n`
and `pullCount sel i n` its count before time `n` (so `∑_i N_i(n) = n`, `sum_pullCount`).
The values `Q i n ∈ [0,1]` are arbitrary and may change with `n`; every maximiser is
admissible.  Then `N_i(t) ≥ λ_i / (8 √2) · √t` for every `t ≥ T_0` and every `i`. -/
theorem local_puct_revisit [Fintype ι] (lam : ι → ℝ) (hlam : ∀ j, 0 < lam j)
    (sel : ℕ → ι) (Q : ι → ℕ → ℝ) (hQ : ∀ n j, 0 ≤ Q j n ∧ Q j n ≤ 1)
    (hrule : ∀ n j, Q j n + lam j * √(n : ℝ) / (1 + (pullCount sel j n : ℝ)) ≤
      Q (sel n) n + lam (sel n) * √(n : ℝ) / (1 + (pullCount sel (sel n) n : ℝ)))
    (t : ℕ) (ht : puctThreshold univ lam ≤ t) (i : ι) :
    lam i / (8 * √2) * √(t : ℝ) ≤ (pullCount sel i t : ℝ) := by
  have hcl : ∀ s, stepCount (fun _ : ℕ => True) s = s := fun s =>
    stepCount_of_forall s (fun _ _ => trivial)
  have hpc : ∀ j s, stepCount (fun r => True ∧ sel r = j) s = pullCount sel j s := by
    intro j s
    unfold pullCount
    simp only [true_and]
  obtain ⟨h1, h2, h3⟩ := puctThreshold_spec univ lam (fun j _ => hlam j)
    (x := (t : ℝ)) (by exact_mod_cast ht) (mem_univ i)
  have := local_puct_core univ lam (fun j _ => hlam j) (fun _ => True) sel Q t
    (fun _ _ _ => mem_univ _) (fun s _ _ j _ => hQ s j)
    (fun s _ _ j _ => by rw [hcl, hpc, hpc]; exact hrule s j) (mem_univ i)
    (by rw [hcl]; exact h1) (by rw [hcl]; exact h2) (by rw [hcl]; exact h3)
  rw [hcl, hpc] at this
  exact this

end Local

/-! ### Propagation through a finite DAG (`thm:v35dag`) -/

section DAG

variable {V E : Type*} [Fintype E]

open Classical in
/-- The fixed list `E(v)` of outgoing edges of a vertex. -/
noncomputable def outEdges (src : E → V) (v : V) : Finset E := univ.filter (fun e => src e = v)

/-- Number of simulations `s < t` that visit `v` (the local clock of `v`; for a terminal,
its number of samples `n_z(t)`). -/
noncomputable def visitCount (vis : ℕ → V → Prop) (v : V) (t : ℕ) : ℕ :=
  stepCount (fun s => vis s v) t

/-- Number of simulations `s < t` that visit `v` and leave it through `e`. -/
noncomputable def edgeCount (vis : ℕ → V → Prop) (ch : ℕ → V → E) (v : V) (e : E) (t : ℕ) : ℕ :=
  stepCount (fun s => vis s v ∧ ch s v = e) t

/-- **The fixed-graph recursive PUCT contract (`sec:v35scope`).**

`src`, `tgt` give the endpoints of the edges; a vertex is terminal when it has no outgoing
edge.  `vis s v` says that simulation `s` visits `v` (a simulation visits a vertex at most
once, and a transposed vertex has one shared visit table) and `ch s v` is the outgoing edge
it then follows.  Every simulation starts at the root; a simulation visiting a nonterminal
`v` follows an outgoing edge of `v` to its head, chosen as any maximiser of
`Q e s + lam e * √(n_v) / (1 + N_{v,e})`, where `n_v` and `N_{v,e}` count earlier
simulations.  The backed-up values `Q e s ∈ [0,1]` are otherwise arbitrary. -/
structure PUCTRun (src tgt : E → V) (root : V) (lam : E → ℝ) (vis : ℕ → V → Prop)
    (ch : ℕ → V → E) (Q : E → ℕ → ℝ) : Prop where
  lam_pos : ∀ e, 0 < lam e
  root_vis : ∀ s, vis s root
  ch_src : ∀ s v, vis s v → (outEdges src v).Nonempty → src (ch s v) = v
  ch_vis : ∀ s v, vis s v → (outEdges src v).Nonempty → vis s (tgt (ch s v))
  Q_mem : ∀ s e, 0 ≤ Q e s ∧ Q e s ≤ 1
  puct : ∀ s v, vis s v → ∀ e, src e = v →
    Q e s + lam e * √(visitCount vis v s : ℝ) / (1 + (edgeCount vis ch v e s : ℝ)) ≤
      Q (ch s v) s + lam (ch s v) * √(visitCount vis v s : ℝ) /
        (1 + (edgeCount vis ch v (ch s v) s : ℝ))

variable {src tgt : E → V} {root : V} {lam : E → ℝ} {vis : ℕ → V → Prop} {ch : ℕ → V → E}
  {Q : E → ℕ → ℝ}

lemma mem_outEdges {e : E} {v : V} : e ∈ outEdges src v ↔ src e = v := by
  classical
  simp [outEdges]

/-- At a nonterminal vertex the edge counts sum to the vertex's visit count, also under
transpositions. -/
lemma sum_edgeCount (h : PUCTRun src tgt root lam vis ch Q) (v : V)
    (hv : (outEdges src v).Nonempty) (t : ℕ) :
    ∑ e ∈ outEdges src v, edgeCount vis ch v e t = visitCount vis v t := by
  classical
  unfold edgeCount visitCount stepCount
  have hmaps : ∀ s ∈ (range t).filter (fun s => vis s v), ch s v ∈ outEdges src v := by
    intro s hs
    rw [mem_filter] at hs
    exact mem_outEdges.mpr (h.ch_src s v hs.2 hv)
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl (fun e _ => ?_)
  rw [filter_filter]
  congr

/-- One edge of the induction: if the tail of `e` has been visited at least `x ≥ T_v` times,
the head of `e` has been visited at least `λ_e / (8 √2) · √x` times. -/
lemma edge_step (h : PUCTRun src tgt root lam vis ch Q) (e : E) (t : ℕ) {x : ℝ}
    (hT : (puctThreshold (outEdges src (src e)) lam : ℝ) ≤ x)
    (hx : x ≤ visitCount vis (src e) t) :
    lam e / (8 * √2) * √x ≤ visitCount vis (tgt e) t := by
  set v := src e with hv
  have heA : e ∈ outEdges src v := mem_outEdges.mpr rfl
  have hne : (outEdges src v).Nonempty := ⟨e, heA⟩
  obtain ⟨h1, h2, h3⟩ := puctThreshold_spec (outEdges src v) lam (fun j _ => h.lam_pos j)
    (hT.trans hx) heA
  have hcore := local_puct_core (outEdges src v) lam (fun j _ => h.lam_pos j)
    (fun s => vis s v) (fun s => ch s v) Q t
    (fun s _ hs => mem_outEdges.mpr (h.ch_src s v hs hne))
    (fun s _ _ j _ => h.Q_mem s j)
    (fun s _ hs j hj => h.puct s v hs j (mem_outEdges.mp hj)) heA h1 h2 h3
  have hmono : edgeCount vis ch v e t ≤ visitCount vis (tgt e) t := by
    refine stepCount_mono_pred t (fun s _ hs => ?_)
    have := h.ch_vis s v hs.1 hne
    rwa [hs.2] at this
  have hmonoR : (edgeCount vis ch v e t : ℝ) ≤ visitCount vis (tgt e) t := by exact_mod_cast hmono
  have hsq : √x ≤ √(visitCount vis v t : ℝ) := Real.sqrt_le_sqrt hx
  have hα : 0 ≤ lam e / (8 * √2) := by
    have := h.lam_pos e
    positivity
  calc lam e / (8 * √2) * √x ≤ lam e / (8 * √2) * √(visitCount vis v t : ℝ) :=
        mul_le_mul_of_nonneg_left hsq hα
    _ ≤ (edgeCount vis ch v e t : ℝ) := hcore
    _ ≤ _ := hmonoR

/-- `IsPath src tgt p v z`: the edge list `p` is a directed path from `v` to `z`. -/
def IsPath (src tgt : E → V) : List E → V → V → Prop
  | [], v, z => v = z
  | e :: p, v, z => src e = v ∧ IsPath src tgt p (tgt e) z

/-- The path constants of `eq:v35constants`: `pathConst lam p 1 = C_{z,d_z}` for a path `p`
of length `d_z`, with `C_{z,0} = 1` and `C_{z,j} = λ_{e_j} / (8 √2) · √C_{z,j-1}`. -/
noncomputable def pathConst (lam : E → ℝ) : List E → ℝ → ℝ
  | [], c => c
  | e :: p, c => pathConst lam p (lam e / (8 * √2) * √c)

/-- `pathThreshold src lam p 1 0 = max_{0 ≤ j < d} (T_{v_j} / C_{z,j}) ^ (2 ^ j)`
(`0` for the empty path), the inner maximum of `eq:v35tstar`. -/
noncomputable def pathThreshold (src : E → V) (lam : E → ℝ) : List E → ℝ → ℕ → ℝ
  | [], _, _ => 0
  | e :: p, c, j =>
      max (((puctThreshold (outEdges src (src e)) lam : ℝ) / c) ^ (2 ^ j))
        (pathThreshold src lam p (lam e / (8 * √2) * √c) (j + 1))

omit [Fintype E] in
lemma pathConst_pos (hlam : ∀ e, 0 < lam e) :
    ∀ (p : List E) (c : ℝ), 0 < c → 0 < pathConst lam p c
  | [], c, hc => hc
  | e :: p, c, hc => by
      have := hlam e
      exact pathConst_pos hlam p _ (by positivity)

lemma le_iterate_sqrt : ∀ (j : ℕ) (x t : ℝ), x ^ (2 ^ j) ≤ t → x ≤ Real.sqrt^[j] t
  | 0, x, t, h => by simpa using h
  | j + 1, x, t, h => by
      rw [Function.iterate_succ_apply']
      apply Real.le_sqrt_of_sq_le
      apply le_iterate_sqrt j
      rw [← pow_mul, ← pow_succ']
      exact h

lemma iterate_sqrt_eq_rpow {t : ℝ} (ht : 0 ≤ t) :
    ∀ j : ℕ, Real.sqrt^[j] t = t ^ (1 / 2 ^ j : ℝ)
  | 0 => by simp
  | j + 1 => by
      rw [Function.iterate_succ_apply', iterate_sqrt_eq_rpow ht j, Real.sqrt_eq_rpow,
        ← Real.rpow_mul ht]
      congr 1
      rw [pow_succ]
      field_simp

/-- Induction along a fixed path (proof of `thm:v35dag`), with `√^[j] t = t ^ (2 ^ (-j))`. -/
lemma path_coverage (h : PUCTRun src tgt root lam vis ch Q) (t : ℕ) :
    ∀ (p : List E) (v z : V) (c : ℝ) (j : ℕ), 0 < c → IsPath src tgt p v z →
      pathThreshold src lam p c j ≤ t → c * Real.sqrt^[j] (t : ℝ) ≤ visitCount vis v t →
      pathConst lam p c * Real.sqrt^[j + p.length] (t : ℝ) ≤ visitCount vis z t
  | [], v, z, c, j, _, hp, _, hv => by
      have hvz : v = z := hp
      subst hvz
      simpa [pathConst] using hv
  | e :: p, v, z, c, j, hc, hp, hthr, hv => by
      obtain ⟨hsrc, hp'⟩ := hp
      have hthr1 : ((puctThreshold (outEdges src (src e)) lam : ℝ) / c) ^ (2 ^ j) ≤ t :=
        (le_max_left _ _).trans hthr
      have hthr2 : pathThreshold src lam p (lam e / (8 * √2) * √c) (j + 1) ≤ t :=
        (le_max_right _ _).trans hthr
      have hT := le_iterate_sqrt j _ _ hthr1
      rw [div_le_iff₀ hc] at hT
      rw [← hsrc] at hv
      have hstep := edge_step h e t (x := c * Real.sqrt^[j] (t : ℝ))
        (by rw [mul_comm]; exact hT) hv
      rw [Real.sqrt_mul hc.le, ← Function.iterate_succ_apply' Real.sqrt, ← mul_assoc] at hstep
      have hc' : 0 < lam e / (8 * √2) * √c := by
        have := h.lam_pos e
        positivity
      have := path_coverage h t p (tgt e) z _ (j + 1) hc' hp' hthr2 hstep
      have hlen : j + (e :: p).length = j + 1 + p.length := by
        rw [List.length_cons]
        omega
      rw [hlen]
      exact this

variable {Zt : Type*} [Fintype Zt] [Nonempty Zt]

/-- `c_* = min_z C_{z,d_z}` of `eq:v35tstar`. -/
noncomputable def puctCstar (lam : E → ℝ) (P : Zt → List E) : ℝ :=
  univ.inf' univ_nonempty (fun z => pathConst lam (P z) 1)

/-- `t_* = ⌈max {1, max_z max_{j < d_z} (T_{v_j} / C_{z,j}) ^ (2 ^ j)}⌉` of `eq:v35tstar`. -/
noncomputable def puctTstar (src : E → V) (lam : E → ℝ) (P : Zt → List E) : ℕ :=
  ⌈max 1 (univ.sup' univ_nonempty (fun z => pathThreshold src lam (P z) 1 0))⌉₊

omit [Fintype E] in
lemma puctCstar_pos (hlam : ∀ e, 0 < lam e) (P : Zt → List E) : 0 < puctCstar lam P := by
  unfold puctCstar
  rw [lt_inf'_iff]
  exact fun z _ => pathConst_pos hlam _ _ one_pos

/-- **Pathwise terminal coverage under recursive local PUCT (Theorem `thm:v35dag`).**

`term z` are the terminals, `P z` one chosen directed path from the root to `term z`, of
length `d_z ≤ H`.  For every run satisfying the contract `PUCTRun` (hence every outcome
sequence), every `t ≥ t_*` and every terminal,
`n_z(t) ≥ C_{z,d_z} t ^ (2 ^ (-d_z)) ≥ c_* t ^ (2 ^ (-H))`, and `c_* > 0`. -/
theorem puct_terminal_coverage (h : PUCTRun src tgt root lam vis ch Q) (term : Zt → V)
    (P : Zt → List E) (hP : ∀ z, IsPath src tgt (P z) root (term z)) (H : ℕ)
    (hH : ∀ z, (P z).length ≤ H) (t : ℕ) (ht : puctTstar src lam P ≤ t) (z : Zt) :
    pathConst lam (P z) 1 * (t : ℝ) ^ (1 / 2 ^ (P z).length : ℝ) ≤ visitCount vis (term z) t ∧
      puctCstar lam P * (t : ℝ) ^ (1 / 2 ^ H : ℝ) ≤
        pathConst lam (P z) 1 * (t : ℝ) ^ (1 / 2 ^ (P z).length : ℝ) := by
  have htR : max 1 (univ.sup' univ_nonempty (fun z => pathThreshold src lam (P z) 1 0)) ≤
      (t : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast ht)
  have ht1 : (1 : ℝ) ≤ t := (le_max_left _ _).trans htR
  have hthr : pathThreshold src lam (P z) 1 0 ≤ t :=
    ((le_sup' (fun z => pathThreshold src lam (P z) 1 0) (mem_univ z)).trans
      (le_max_right _ _)).trans htR
  have hroot : visitCount vis root t = t := stepCount_of_forall t (fun s _ => h.root_vis s)
  have hcov := path_coverage h t (P z) root (term z) 1 0 one_pos (hP z) hthr
    (by rw [hroot]; simp)
  rw [zero_add, iterate_sqrt_eq_rpow (by linarith)] at hcov
  refine ⟨hcov, ?_⟩
  have hC : puctCstar lam P ≤ pathConst lam (P z) 1 :=
    inf'_le (fun z => pathConst lam (P z) 1) (mem_univ z)
  have hexp : (1 / 2 ^ H : ℝ) ≤ 1 / 2 ^ (P z).length :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (hH z))
  have hpow : (t : ℝ) ^ (1 / 2 ^ H : ℝ) ≤ (t : ℝ) ^ (1 / 2 ^ (P z).length : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 hexp
  exact mul_le_mul hC hpow (by positivity) (pathConst_pos h.lam_pos _ _ one_pos).le

/-- Combined form: `n_z(t) ≥ c_* t ^ (2 ^ (-H))` for all `t ≥ t_*`. -/
theorem puct_terminal_coverage' (h : PUCTRun src tgt root lam vis ch Q) (term : Zt → V)
    (P : Zt → List E) (hP : ∀ z, IsPath src tgt (P z) root (term z)) (H : ℕ)
    (hH : ∀ z, (P z).length ≤ H) (t : ℕ) (ht : puctTstar src lam P ≤ t) (z : Zt) :
    puctCstar lam P * (t : ℝ) ^ (1 / 2 ^ H : ℝ) ≤ visitCount vis (term z) t :=
  (puct_terminal_coverage h term P hP H hH t ht z).2.trans
    (puct_terminal_coverage h term P hP H hH t ht z).1

/-- Every terminal is sampled infinitely often: its count eventually exceeds any bound. -/
theorem terminal_sampled_unboundedly (h : PUCTRun src tgt root lam vis ch Q) (term : Zt → V)
    (P : Zt → List E) (hP : ∀ z, IsPath src tgt (P z) root (term z)) (z : Zt) (B : ℝ) :
    ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → B ≤ visitCount vis (term z) t := by
  have hC : 0 < pathConst lam (P z) 1 := pathConst_pos h.lam_pos _ _ one_pos
  refine ⟨max (puctTstar src lam P)
    ⌈(max 0 (B / pathConst lam (P z) 1)) ^ (2 ^ (P z).length)⌉₊, fun t ht => ?_⟩
  have ht1 := (le_max_left _ _).trans ht
  have ht2 : (max 0 (B / pathConst lam (P z) 1)) ^ (2 ^ (P z).length) ≤ (t : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans ht)
  have hcov := (puct_terminal_coverage h term P hP (univ.sup (fun z => (P z).length))
    (fun z => le_sup (f := fun z => (P z).length) (mem_univ z)) t ht1 z).1
  have hx := le_iterate_sqrt _ _ _ ht2
  rw [iterate_sqrt_eq_rpow (Nat.cast_nonneg t)] at hx
  have hB : B ≤ pathConst lam (P z) 1 * max 0 (B / pathConst lam (P z) 1) := by
    have : B / pathConst lam (P z) 1 ≤ max 0 (B / pathConst lam (P z) 1) := le_max_right _ _
    rwa [div_le_iff₀ hC, mul_comm] at this
  exact hB.trans ((mul_le_mul_of_nonneg_left hx hC.le).trans hcov)

end DAG

/-! ### Zero prior at one edge (`ce:v35prior`) -/

section Counterexample

/-- The PUCT score `Q_i(n) + λ_i √n / (1 + N_i(n))` of `eq:v35onevertex`. -/
noncomputable def puctScore {ι : Type*} (lam : ι → ℝ) (sel : ℕ → ι) (Q : ι → ℕ → ℝ) (i : ι)
    (n : ℕ) : ℝ :=
  Q i n + lam i * √(n : ℝ) / (1 + (pullCount sel i n : ℝ))

/-- **Zero prior at one internal edge prevents terminal coverage (Counterexample
`ce:v35prior`).**  A node has two edges `0`, `1` with `λ_1 = 0` (and `λ_0 ≥ 0`; the
manuscript takes `λ_0 > 0`).  The value of edge `1` is zero while it is unvisited, the value
of edge `0` is nonnegative (for instance a running mean of rewards in `[0,1]`), selection is
by maximal score, and ties are broken in favour of edge `0`.  Then edge `1` is never
selected, so the terminal behind it is never sampled. -/
theorem zero_prior_never_selected (lam : Fin 2 → ℝ) (h0 : 0 ≤ lam 0) (h1 : lam 1 = 0)
    (sel : ℕ → Fin 2) (Q : Fin 2 → ℕ → ℝ) (hQ0 : ∀ n, 0 ≤ Q 0 n)
    (hinit : ∀ n, pullCount sel 1 n = 0 → Q 1 n = 0)
    (hrule : ∀ n j, puctScore lam sel Q j n ≤ puctScore lam sel Q (sel n) n)
    (htie : ∀ n, puctScore lam sel Q 0 n = puctScore lam sel Q 1 n → sel n = 0) (n : ℕ) :
    sel n = 0 ∧ pullCount sel 1 n = 0 := by
  have hkey : ∀ n, pullCount sel 1 n = 0 → sel n = 0 := by
    intro n hn
    by_contra hne
    have hsel : sel n = 1 := Fin.eq_one_of_ne_zero _ hne
    have hs1 : puctScore lam sel Q 1 n = 0 := by
      unfold puctScore
      rw [hinit n hn, h1]
      simp
    have hs0 : 0 ≤ puctScore lam sel Q 0 n := by
      unfold puctScore
      have := hQ0 n
      positivity
    have hr := hrule n 0
    rw [hsel, hs1] at hr
    exact hne (htie n (by rw [hs1]; exact le_antisymm hr hs0))
  have hcount : ∀ n, pullCount sel 1 n = 0 := by
    intro n
    induction n with
    | zero => exact Nat.le_zero.mp (stepCount_le _ 0)
    | succ n ih =>
        have hsel := hkey n ih
        have : pullCount sel 1 (n + 1) = pullCount sel 1 n :=
          stepCount_succ_of_neg (by rw [hsel]; decide)
        rw [this, ih]
  exact ⟨hkey n (hcount n), hcount n⟩

/-- The hypotheses of `zero_prior_never_selected` are satisfiable. -/
theorem zero_prior_run_exists (lam : Fin 2 → ℝ) (h0 : 0 ≤ lam 0) (h1 : lam 1 = 0) :
    ∃ (sel : ℕ → Fin 2) (Q : Fin 2 → ℕ → ℝ), (∀ n i, 0 ≤ Q i n ∧ Q i n ≤ 1) ∧
      (∀ n, pullCount sel 1 n = 0 → Q 1 n = 0) ∧
      (∀ n j, puctScore lam sel Q j n ≤ puctScore lam sel Q (sel n) n) ∧
      (∀ n, puctScore lam sel Q 0 n = puctScore lam sel Q 1 n → sel n = 0) := by
  refine ⟨fun _ => 0, fun _ _ => 0, fun _ _ => ⟨le_rfl, zero_le_one⟩, fun _ _ => rfl,
    fun n j => ?_, fun _ _ => rfl⟩
  have hs0 : 0 ≤ puctScore lam (fun _ => 0) (fun _ _ => 0) 0 n := by
    unfold puctScore
    positivity
  fin_cases j
  · exact le_rfl
  · have hs1 : puctScore lam (fun _ => 0) (fun _ _ => 0) 1 n = 0 := by
      unfold puctScore
      rw [h1]
      simp
    show puctScore lam (fun _ => 0) (fun _ _ => 0) 1 n ≤ _
    rw [hs1]
    exact hs0

end Counterexample

/-! ### Confidence widths along the trajectory (`lem:v35width`) -/

section Width

/-- The intrinsic-count radius `β_M(n, δ) = √(log (4 M n (n+1) / δ) / (2 n))` of
`eq:v35radius`. -/
noncomputable def puctRadius (M δ : ℝ) (n : ℕ) : ℝ :=
  √(Real.log (4 * M * n * (n + 1) / δ) / (2 * n))

/-- `b_t = √(log (4 M (t+1)² / δ) / (2 m))` of `eq:v35boxwidth`. -/
noncomputable def puctB (M δ m : ℝ) (t : ℕ) : ℝ :=
  √(Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) / (2 * m))

lemma sqrt_log_div_le {a b n m : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) (hm : 0 < m)
    (hmn : m ≤ n) : √(Real.log a / (2 * n)) ≤ √(Real.log b / (2 * m)) := by
  apply Real.sqrt_le_sqrt
  exact div_le_div₀ (Real.log_nonneg hb) (Real.log_le_log ha hab) (by positivity) (by linarith)

lemma one_le_puctB_arg {M δ : ℝ} (hM : 1 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (t : ℕ) :
    1 ≤ 4 * M * ((t : ℝ) + 1) ^ 2 / δ := by
  rw [one_le_div hδ0]
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : (1 : ℝ) ≤ ((t : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul hM h1 zero_le_one (by linarith : (0 : ℝ) ≤ M)]

/-- A terminal with `m ≤ n ≤ t` samples has radius at most `b_t`. -/
lemma puctRadius_le_puctB {M δ m : ℝ} (hM : 1 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 < m)
    {n t : ℕ} (hmn : m ≤ n) (hnt : n ≤ t) : puctRadius M δ n ≤ puctB M δ m t := by
  have hn : (0 : ℝ) < n := lt_of_lt_of_le hm hmn
  have hntR : (n : ℝ) ≤ t := by exact_mod_cast hnt
  have hMpos : 0 < M := by linarith
  refine sqrt_log_div_le (by positivity) ?_ (one_le_puctB_arg hM hδ0 hδ1 t) hm hmn
  apply div_le_div_of_nonneg_right _ hδ0.le
  have h1 : (n : ℝ) * (n + 1) ≤ ((t : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hMpos.le]

/-- The same for the radius `β(n) = √(log (4 M n² / δ) / (2 n))` of
`lem:nested-interval-valid`, which is half of `hoeffdingWidth`. -/
lemma hoeffdingRadius_le_puctB {M δ m : ℝ} (hM : 1 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) {n t : ℕ} (hmn : m ≤ n) (hnt : n ≤ t) :
    hoeffdingWidth M δ n / 2 ≤ puctB M δ m t := by
  have hn : (0 : ℝ) < n := lt_of_lt_of_le hm hmn
  have hntR : (n : ℝ) ≤ t := by exact_mod_cast hnt
  have hMpos : 0 < M := by linarith
  unfold hoeffdingWidth
  rw [mul_div_cancel_left₀ _ (two_ne_zero)]
  refine sqrt_log_div_le (by positivity) ?_ (one_le_puctB_arg hM hδ0 hδ1 t) hm hmn
  apply div_le_div_of_nonneg_right _ hδ0.le
  have h1 : (n : ℝ) ^ 2 ≤ ((t : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hMpos.le]

/-- Lower endpoint of the running intersection of `I_{z,0} = [0,1]` and the clipped
intervals `I_{z,k} = [c k - β k, c k + β k] ∩ [0,1]`, `1 ≤ k ≤ n`. -/
noncomputable def runLower (c β : ℕ → ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' ⟨0, mem_range.mpr n.succ_pos⟩ (fun k => if k = 0 then 0 else c k - β k)

/-- Upper endpoint of the same running intersection. -/
noncomputable def runUpper (c β : ℕ → ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).inf' ⟨0, mem_range.mpr n.succ_pos⟩ (fun k => if k = 0 then 1 else c k + β k)

/-- On the coverage event the running interval contains the mean; in particular it is
nonempty and the failure flag never fires (`lem:v35width`). -/
lemma running_box_covers {c β : ℕ → ℝ} {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hcov : ∀ k, 1 ≤ k → |c k - μ| ≤ β k) (n : ℕ) :
    runLower c β n ≤ μ ∧ μ ≤ runUpper c β n := by
  constructor
  · refine sup'_le _ _ (fun k _ => ?_)
    split_ifs with hk
    · exact hμ.1
    · have := abs_le.mp (hcov k (Nat.one_le_iff_ne_zero.mpr hk))
      linarith
  · refine le_inf' _ _ (fun k _ => ?_)
    split_ifs with hk
    · exact hμ.2
    · have := abs_le.mp (hcov k (Nat.one_le_iff_ne_zero.mpr hk))
      linarith

/-- **Usable width bound (`eq:v35boxwidth`).**  On the coverage event, if the latest radius
is at most `b`, the running interval lies within `2 b` of the mean. -/
lemma running_box_width {c β : ℕ → ℝ} {μ : ℝ} (hcov : ∀ k, 1 ≤ k → |c k - μ| ≤ β k) {n : ℕ}
    (hn : 1 ≤ n) {b : ℝ} (hb : β n ≤ b) :
    μ - 2 * b ≤ runLower c β n ∧ runUpper c β n ≤ μ + 2 * b := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hc := abs_le.mp (hcov n hn)
  constructor
  · have h := le_sup' (fun k => if k = 0 then 0 else c k - β k)
      (mem_range.mpr (Nat.lt_succ_self n))
    simp only [hn0, ↓reduceIte] at h
    unfold runLower
    linarith
  · have h := inf'_le (fun k => if k = 0 then 1 else c k + β k)
      (mem_range.mpr (Nat.lt_succ_self n))
    simp only [hn0, ↓reduceIte] at h
    unfold runUpper
    linarith

/-- **Lemma `lem:v35width`, second claim (`eq:v35boxwidth`).**  On the coverage event for
the radius `β_M(·, δ)`, a terminal with `m ≤ n ≤ t` samples, `m > 0`, has running interval
`μ - 2 b_t ≤ ℓ ≤ μ ≤ u ≤ μ + 2 b_t`. -/
lemma running_box_width_bt {c : ℕ → ℝ} {μ M δ m : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hM : 1 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 < m)
    (hcov : ∀ k, 1 ≤ k → |c k - μ| ≤ puctRadius M δ k) {n t : ℕ} (hmn : m ≤ n)
    (hnt : n ≤ t) :
    μ - 2 * puctB M δ m t ≤ runLower c (puctRadius M δ) n ∧
      runLower c (puctRadius M δ) n ≤ μ ∧ μ ≤ runUpper c (puctRadius M δ) n ∧
      runUpper c (puctRadius M δ) n ≤ μ + 2 * puctB M δ m t := by
  have hn : 1 ≤ n := by
    by_contra h0
    have h1 : n = 0 := by omega
    rw [h1] at hmn
    simp only [Nat.cast_zero] at hmn
    linarith
  have hw := running_box_width hcov hn (puctRadius_le_puctB hM hδ0 hδ1 hm hmn hnt)
  have hc := running_box_covers hμ hcov n
  exact ⟨hw.1, hc.1, hc.2, hw.2⟩

/-- If `m ≥ (8 / e²) L` then `4 √(L / (2 m)) ≤ e`. -/
lemma four_sqrt_le {L m e : ℝ} (hm : 0 < m) (he : 0 < e) (h : 8 / e ^ 2 * L ≤ m) :
    4 * √(L / (2 * m)) ≤ e := by
  have h' : 8 * L ≤ m * e ^ 2 := by
    rwa [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h
  have hs : √(L / (2 * m)) ≤ e / 4 := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
    have : (e / 4) ^ 2 * (2 * m) = m * e ^ 2 / 8 := by ring
    rw [this]
    linarith
  linarith

end Width

/-! ### Certification along the trajectory (`thm:v35horizon`, `thm:puct-noisy-main`) -/

section Certification

open MeasureTheory

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- The exterior support margin `μ_* - max_{z ∉ S} μ_z` of a proper support. -/
noncomputable def outsideMargin (S : Finset Z) (hSc : Sᶜ.Nonempty) (μ : Z → ℝ) : ℝ :=
  gmax μ - Sᶜ.sup' hSc μ

lemma outsideMargin_nonneg (S : Finset Z) (hSc : Sᶜ.Nonempty) (μ : Z → ℝ) :
    0 ≤ outsideMargin S hSc μ :=
  sub_nonneg.mpr (sup'_le _ _ (fun z _ => le_gmax μ z))

/-- If every terminal is reachable from some root action, an optimal root action exists. -/
lemma exists_optimal_action {A : Type*} (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hreach : ∀ z, ∃ a, z ∈ supp a) (μ : Z → ℝ) : ∃ a, val (supp a) (hne a) μ = gmax μ := by
  obtain ⟨z, -, hz⟩ := exists_mem_eq_sup' (univ_nonempty (α := Z)) μ
  obtain ⟨a, ha⟩ := hreach z
  refine ⟨a, le_antisymm (val_le_gmax _ _ _) ?_⟩
  have h1 : gmax μ = μ z := hz
  rw [h1]
  exact le_val (hne a) μ ha

/-- **Certificate of an optimal action from the width bound.**  If every interval lies
within `2 b` of its mean and `S` is the support of an optimal action, the exact
outside-support certificate is at most `[4 b - (μ_* - max_{z ∉ S} μ_z)]_+`. -/
theorem rectCert_le_of_width {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    {μ l u : Z → ℝ} {b : ℝ} (hl : ∀ z, μ z - 2 * b ≤ l z) (hu : ∀ z, u z ≤ μ z + 2 * b)
    (hopt : val S hS μ = gmax μ) :
    rectCert S hS hSc l u ≤ max 0 (4 * b - outsideMargin S hSc μ) := by
  unfold rectCert outsideMargin
  apply max_le_max le_rfl
  have h1 : Sᶜ.sup' hSc u ≤ Sᶜ.sup' hSc μ + 2 * b :=
    sup'_le _ _ (fun z hz => (hu z).trans (by have := le_sup' μ hz; linarith))
  obtain ⟨y, hy, hval⟩ := exists_mem_eq_sup' hS μ
  have h2 : gmax μ - 2 * b ≤ S.sup' hS l := by
    have h3 := le_sup' l hy
    have h4 := hl y
    unfold val at hopt
    rw [hval] at hopt
    linarith
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {A : Type*}

/-- **Certification by a fixed time: deterministic and probabilistic assembly (core of
`thm:v35horizon` and `thm:puct-noisy-main`).**

Objects: `c ω z k` is the empirical mean of the first `k` elements of the tape of terminal
`z`, `β k` the radius at intrinsic count `k`, `cnt s ω z` the number of samples of `z`
after `s` simulations; the confidence box at time `s` is the running intersection
`[runLower, runUpper]` at count `cnt s ω z`.

Hypotheses standing in for other parts of the paper:
* `hcover`: the simultaneous intrinsic-count coverage event fails with probability at most
  `δ'` (`hoeffding_tape_coverage` supplies `δ' = δ / 2` for the radius `puctRadius`);
* `hmon`: the monitor.  Whenever some action has exact certificate at most `ε` at a time
  `s`, the monitor has stopped by then (`τ ω ≤ s`) and the action `rec ω` it returned is
  certified at its stopping time;
* `hcnt`: at the fixed time `t` every terminal has been sampled, with radius at most `b`
  (supplied by `puct_terminal_coverage` and `puctRadius_le_puctB`);
* `a` is an optimal root action and `4 b ≤ ε + (μ_* - max_{z ∉ S(a)} μ_z)`.

Conclusion: outside an event of probability at most `δ'`, the monitor stops by time `t` and
its action is `ε`-optimal. -/
theorem puct_certification_core (P : Measure Ω) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty) (μ : Z → ℝ)
    (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (c : Ω → Z → ℕ → ℝ) (β : ℕ → ℝ)
    (cnt : ℕ → Ω → Z → ℕ) (δ' : ENNReal)
    (hcover : P {ω | ∃ z k, 1 ≤ k ∧ β k < |c ω z k - μ z|} ≤ δ')
    (ε : ℝ) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, rectCert (supp a) (hne a) (hpr a)
          (fun z => runLower (c ω z) β (cnt s ω z))
          (fun z => runUpper (c ω z) β (cnt s ω z)) ≤ ε) →
        τ ω ≤ s ∧ rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (fun z => runLower (c ω z) β (cnt (τ ω) ω z))
          (fun z => runUpper (c ω z) β (cnt (τ ω) ω z)) ≤ ε)
    (t : ℕ) (b : ℝ) (hcnt : ∀ ω z, 1 ≤ cnt t ω z ∧ β (cnt t ω z) ≤ b)
    (a : A) (hopt : val (supp a) (hne a) μ = gmax μ)
    (hb : 4 * b ≤ ε + outsideMargin (supp a) (hpr a) μ) (hε : 0 ≤ ε) :
    P {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤ δ' := by
  refine (measure_mono ?_).trans hcover
  intro ω hω
  by_contra hfail
  have hcov : ∀ z k, 1 ≤ k → |c ω z k - μ z| ≤ β k := by
    intro z k hk
    by_contra hlt
    exact hfail ⟨z, k, hk, not_le.mp hlt⟩
  apply hω
  have hcert := rectCert_le_of_width (hne a) (hpr a)
    (l := fun z => runLower (c ω z) β (cnt t ω z))
    (u := fun z => runUpper (c ω z) β (cnt t ω z)) (b := b)
    (fun z => (running_box_width (hcov z) (hcnt ω z).1 (hcnt ω z).2).1)
    (fun z => (running_box_width (hcov z) (hcnt ω z).1 (hcnt ω z).2).2) hopt
  obtain ⟨hτ, hrec⟩ := hmon ω t ⟨a, hcert.trans (max_le hε (by linarith))⟩
  exact ⟨hτ, regret_le_of_cert (hpr (rec ω))
    ⟨fun z => (running_box_covers (hμ z) (hcov z) _).1,
      fun z => (running_box_covers (hμ z) (hcov z) _).2⟩ hrec⟩

/-- **Support-sensitive certification from terminal counts (second half of
`thm:puct-noisy-main`).**  As `puct_certification_core`, with `b = b_t`: every terminal has
between `m > 0` and `t` samples at time `t`, the radius obeys `β k ≤ b_t` for
`m ≤ k ≤ t`, and
`m ≥ 8 / (ε + Γ_a)² · log (4 M (t+1)² / δ)` for an optimal action `a` with margin `Γ_a`,
`ε + Γ_a > 0` (this is `eq:puct-noisy-condition` with `m = c_* t ^ (2 ^ (-H))`).  The case
`ε = 0`, `Γ_a > 0` is included. -/
theorem puct_noisy_certification (P : Measure Ω) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty) (μ : Z → ℝ)
    (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (c : Ω → Z → ℕ → ℝ) (β : ℕ → ℝ)
    (cnt : ℕ → Ω → Z → ℕ) (δ' : ENNReal)
    (hcover : P {ω | ∃ z k, 1 ≤ k ∧ β k < |c ω z k - μ z|} ≤ δ')
    (ε : ℝ) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, rectCert (supp a) (hne a) (hpr a)
          (fun z => runLower (c ω z) β (cnt s ω z))
          (fun z => runUpper (c ω z) β (cnt s ω z)) ≤ ε) →
        τ ω ≤ s ∧ rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (fun z => runLower (c ω z) β (cnt (τ ω) ω z))
          (fun z => runUpper (c ω z) β (cnt (τ ω) ω z)) ≤ ε)
    (t : ℕ) {M δ m : ℝ} (hm : 0 < m)
    (hβ : ∀ k : ℕ, m ≤ k → k ≤ t → β k ≤ puctB M δ m t)
    (hcnt : ∀ ω z, m ≤ cnt t ω z ∧ cnt t ω z ≤ t)
    (a : A) (hopt : val (supp a) (hne a) μ = gmax μ) (hε : 0 ≤ ε)
    (hpos : 0 < ε + outsideMargin (supp a) (hpr a) μ)
    (hcond : 8 / (ε + outsideMargin (supp a) (hpr a) μ) ^ 2 *
      Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ m) :
    P {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤ δ' := by
  refine puct_certification_core P supp hne hpr μ hμ c β cnt δ' hcover ε τ rec hmon t
    (puctB M δ m t) (fun ω z => ⟨?_, hβ _ (hcnt ω z).1 (hcnt ω z).2⟩) a hopt
    (four_sqrt_le hm hpos hcond) hε
  have h := (hcnt ω z).1
  by_contra h0
  have h1 : cnt t ω z = 0 := by omega
  rw [h1] at h
  simp only [Nat.cast_zero] at h
  linarith

/-- The exact minimum-regret certificate of a root support over a box, including the
empty-complement case of `thm:shared-regret`: the outside-support expression for a proper
support and `0` for a full support. -/
noncomputable def exactCert (S : Finset Z) (hS : S.Nonempty) (l u : Z → ℝ) : ℝ :=
  if h : Sᶜ.Nonempty then rectCert S hS h l u else 0

lemma regret_le_exactCert {S : Finset Z} (hS : S.Nonempty) {l u μ : Z → ℝ}
    (hμ : μ ∈ Set.Icc l u) : regret S hS μ ≤ exactCert S hS l u := by
  unfold exactCert
  split_ifs with h
  · exact regret_le_rectCert h hμ
  · exact (regret_eq_zero_of_compl_empty (not_nonempty_iff_eq_empty.mp h)).le

lemma exactCert_le_of_width {S : Finset Z} (hS : S.Nonempty) {μ l u : Z → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hl : ∀ z, μ z - 2 * b ≤ l z) (hu : ∀ z, u z ≤ μ z + 2 * b)
    (hopt : val S hS μ = gmax μ) : exactCert S hS l u ≤ 4 * b := by
  unfold exactCert
  split_ifs with h
  · have := outsideMargin_nonneg S h μ
    exact (rectCert_le_of_width hS h hl hu hopt).trans (max_le (by linarith) (by linarith))
  · linarith

/-- **High-probability on-policy PUCT certification horizon, from terminal counts
(`thm:v35horizon`).**  Root supports may be proper or full (`exactCert`).  With the radius
`β_M(n, δ)` of `eq:v35radius`, every terminal reachable from some root action, `ε > 0`, and
at time `t` every terminal sampled between `m` and `t` times with
`m ≥ (8 / ε²) log (4 M (t+1)² / δ)` (this is `eq:v35horizoncondition` with
`m = c_* t ^ (2 ^ (-H))`, the count bound being `puct_terminal_coverage'`): outside the
coverage-failure event, of probability at most `δ'`, the monitor has stopped by `t` with an
`ε`-optimal action.  `hcover` and `hmon` are as in `puct_certification_core`;
`puct_horizon_full` removes `hcover` and the count hypothesis. -/
theorem puct_horizon (P : Measure Ω) (supp : A → Finset Z)
    (hne : ∀ a, (supp a).Nonempty) (hreach : ∀ z, ∃ a, z ∈ supp a) (μ : Z → ℝ)
    (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (c : Ω → Z → ℕ → ℝ) {M δ : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (cnt : ℕ → Ω → Z → ℕ) (δ' : ENNReal)
    (hcover : P {ω | ∃ z k, 1 ≤ k ∧ puctRadius M δ k < |c ω z k - μ z|} ≤ δ')
    (ε : ℝ) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, exactCert (supp a) (hne a)
          (fun z => runLower (c ω z) (puctRadius M δ) (cnt s ω z))
          (fun z => runUpper (c ω z) (puctRadius M δ) (cnt s ω z)) ≤ ε) →
        τ ω ≤ s ∧ exactCert (supp (rec ω)) (hne (rec ω))
          (fun z => runLower (c ω z) (puctRadius M δ) (cnt (τ ω) ω z))
          (fun z => runUpper (c ω z) (puctRadius M δ) (cnt (τ ω) ω z)) ≤ ε)
    (t : ℕ) {m : ℝ} (hm : 0 < m) (hcnt : ∀ ω z, m ≤ cnt t ω z ∧ cnt t ω z ≤ t)
    (hε : 0 < ε) (hcond : 8 / ε ^ 2 * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ m) :
    P {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤ δ' := by
  obtain ⟨a, hopt⟩ := exists_optimal_action supp hne hreach μ
  have hb : 4 * puctB M δ m t ≤ ε := four_sqrt_le hm hε hcond
  have hb0 : 0 ≤ puctB M δ m t := Real.sqrt_nonneg _
  refine (measure_mono ?_).trans hcover
  intro ω hω
  by_contra hfail
  have hcov : ∀ z k, 1 ≤ k → |c ω z k - μ z| ≤ puctRadius M δ k := by
    intro z k hk
    by_contra hlt
    exact hfail ⟨z, k, hk, not_le.mp hlt⟩
  apply hω
  have h1 : ∀ z, 1 ≤ cnt t ω z := by
    intro z
    have h := (hcnt ω z).1
    by_contra h0
    have h1 : cnt t ω z = 0 := by omega
    rw [h1] at h
    simp only [Nat.cast_zero] at h
    linarith
  have hw := fun z => running_box_width (hcov z) (h1 z)
    (puctRadius_le_puctB hM hδ0 hδ1 hm (hcnt ω z).1 (hcnt ω z).2)
  have hcert := exactCert_le_of_width (hne a)
    (l := fun z => runLower (c ω z) (puctRadius M δ) (cnt t ω z))
    (u := fun z => runUpper (c ω z) (puctRadius M δ) (cnt t ω z)) hb0
    (fun z => (hw z).1) (fun z => (hw z).2) hopt
  obtain ⟨hτ, hrec⟩ := hmon ω t ⟨a, hcert.trans hb⟩
  exact ⟨hτ, (regret_le_exactCert (hne (rec ω))
    ⟨fun z => (running_box_covers (hμ z) (hcov z) _).1,
      fun z => (running_box_covers (hμ z) (hcov z) _).2⟩).trans hrec⟩

/-- A root support equal to `Z` is certifiable without observations: its regret is zero in
every environment (first clause of `thm:puct-noisy-main`; this is `regret_univ`). -/
theorem full_support_certified (f : Z → ℝ) : regret (univ : Finset Z) univ_nonempty f = 0 :=
  regret_univ f

end Certification

/-! ### The combined statement (`thm:puct-noisy-main`) -/

section Main

open MeasureTheory

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {V E : Type*} [Fintype E]
  {Ω : Type*} [MeasurableSpace Ω] {A : Type*}

/-- **Support-sensitive certification under recursive PUCT (Theorem `thm:puct-noisy-main`).**

For every sample path `ω` the search is a run satisfying the contract `PUCTRun` on a fixed
graph with fixed positive weights; `term z` are the terminals, `path z` a root-to-terminal
path of length at most `H`; the monitor's box at time `s` is the running intersection at
the terminal counts `visitCount (vis ω) (term z) s`.  `Γ` is the largest exterior margin
over optimal root actions (all supports proper).  If `ε ≥ 0`, `ε + Γ > 0`, `t ≥ t_*` and
`c_* t ^ (2 ^ (-H)) ≥ 8 / (ε + Γ)² · log (4 M (t+1)² / δ)` (`eq:puct-noisy-condition`), then
outside the coverage-failure event, of probability at most `δ'`, the monitor has stopped by
time `t` with an `ε`-optimal action.

Hypotheses standing in for other results: `hcover` (simultaneous coverage,
`lem:nested-interval-valid` or `hoeffding_tape_coverage`), `hmon` (the monitor stops at the
first exact `ε`-certificate and returns a certified action) and `hβ` (the radius is at most
`b_t` on the relevant counts; `puctRadius_le_puctB` and `hoeffdingRadius_le_puctB` give this
for the two radii used in the manuscript).  The terminal counts are not assumed: they come
from `puct_terminal_coverage'`. -/
theorem puct_noisy_main {src tgt : E → V} {root : V} {lam : E → ℝ} (P : Measure Ω)
    (vis : Ω → ℕ → V → Prop) (ch : Ω → ℕ → V → E) (Q : Ω → E → ℕ → ℝ)
    (hrun : ∀ ω, PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω))
    (term : Z → V) (path : Z → List E) (hpath : ∀ z, IsPath src tgt (path z) root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (c : Ω → Z → ℕ → ℝ) (β : ℕ → ℝ)
    (δ' : ENNReal) (hcover : P {ω | ∃ z k, 1 ≤ k ∧ β k < |c ω z k - μ z|} ≤ δ')
    (ε : ℝ) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, rectCert (supp a) (hne a) (hpr a)
          (fun z => runLower (c ω z) β (visitCount (vis ω) (term z) s))
          (fun z => runUpper (c ω z) β (visitCount (vis ω) (term z) s)) ≤ ε) →
        τ ω ≤ s ∧ rectCert (supp (rec ω)) (hne (rec ω)) (hpr (rec ω))
          (fun z => runLower (c ω z) β (visitCount (vis ω) (term z) (τ ω)))
          (fun z => runUpper (c ω z) β (visitCount (vis ω) (term z) (τ ω))) ≤ ε)
    (Γ : ℝ) (hΓ : IsGreatest ((fun a => outsideMargin (supp a) (hpr a) μ) ''
      {a | val (supp a) (hne a) μ = gmax μ}) Γ)
    (hε : 0 ≤ ε) (hpos : 0 < ε + Γ) {M δ : ℝ} (t : ℕ) (ht : puctTstar src lam path ≤ t)
    (hβ : ∀ k : ℕ, puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ) ≤ k → k ≤ t →
      β k ≤ puctB M δ (puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ)) t)
    (hcond : 8 / (ε + Γ) ^ 2 * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤
      puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ)) :
    P {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤ δ' := by
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω0⟩⟩
  · rw [Set.eq_empty_of_isEmpty {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)},
      measure_empty]
    exact zero_le
  obtain ⟨⟨a, hopt, hΓa⟩, -⟩ := hΓ
  simp only at hΓa
  subst hΓa
  have ht1 : (1 : ℝ) ≤ t := by
    have h1 : (1 : ℝ) ≤ (puctTstar src lam path : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
    exact h1.trans (by exact_mod_cast ht)
  have hm : 0 < puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ) :=
    mul_pos (puctCstar_pos (hrun ω0).lam_pos path) (Real.rpow_pos_of_pos (by linarith) _)
  exact puct_noisy_certification P supp hne hpr μ hμ c β
    (fun s ω z => visitCount (vis ω) (term z) s) δ' hcover ε τ rec hmon t hm hβ
    (fun ω z => ⟨puct_terminal_coverage' (hrun ω) term path hpath H hH t ht z,
      stepCount_le _ t⟩) a hopt hε hpos hcond

end Main

/-! ### Polynomial accuracy dependence (`cor:v35poly`) -/

section Poly

/-- **Sufficient polynomial conditions for the horizon inequality.**  For `t ≥ 1` and any
`s > 0`, the inequality `K log (4 M (t+1)² / δ) ≤ c t ^ r` follows from
`t ^ r ≥ 2 K log (16 M / δ) / c` and `t ^ (r - s) ≥ 4 K / (c s)`. -/
theorem horizon_condition_of_poly {cst K M δ r s : ℝ} {t : ℕ} (hc : 0 < cst) (hK : 0 ≤ K)
    (hM : 0 < M) (hδ : 0 < δ) (hs : 0 < s) (ht : 1 ≤ t)
    (h1 : 2 * K * Real.log (16 * M / δ) / cst ≤ (t : ℝ) ^ r)
    (h2 : 4 * K / (cst * s) ≤ (t : ℝ) ^ (r - s)) :
    K * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ cst * (t : ℝ) ^ r := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hlog1 : Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤
      Real.log (16 * M / δ) + 2 * Real.log t := by
    have h4 : ((t : ℝ) + 1) ^ 2 ≤ 4 * (t : ℝ) ^ 2 := by nlinarith
    have hle : 4 * M * ((t : ℝ) + 1) ^ 2 / δ ≤ 16 * M / δ * (t : ℝ) ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hδ.le
      nlinarith [mul_le_mul_of_nonneg_left h4 hM.le]
    calc Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ Real.log (16 * M / δ * (t : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log (16 * M / δ) + 2 * Real.log t := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
          push_cast
          ring
  have hlog2 : Real.log t ≤ (t : ℝ) ^ s / s := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htpos s)
    rw [Real.log_rpow htpos] at h
    rw [le_div_iff₀ hs]
    linarith
  have hts : (t : ℝ) ^ (r - s) * (t : ℝ) ^ s = (t : ℝ) ^ r := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have h1' : 2 * K * Real.log (16 * M / δ) ≤ (t : ℝ) ^ r * cst := by
    rwa [div_le_iff₀ hc] at h1
  have h2' : 4 * K ≤ (t : ℝ) ^ (r - s) * (cst * s) := by
    rwa [div_le_iff₀ (by positivity)] at h2
  have h3 := mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg htpos.le s)
  have h3' : 4 * K * (t : ℝ) ^ s ≤ cst * s * (t : ℝ) ^ r := by
    calc 4 * K * (t : ℝ) ^ s ≤ (t : ℝ) ^ (r - s) * (cst * s) * (t : ℝ) ^ s := h3
      _ = cst * s * ((t : ℝ) ^ (r - s) * (t : ℝ) ^ s) := by ring
      _ = cst * s * (t : ℝ) ^ r := by rw [hts]
  have h4 : 2 * K * ((t : ℝ) ^ s / s) ≤ cst * (t : ℝ) ^ r / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hs]
    linarith
  have h5 : K * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤
      K * (Real.log (16 * M / δ) + 2 * ((t : ℝ) ^ s / s)) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  linarith

/-- **Polynomial accuracy dependence at fixed depth (Corollary `cor:v35poly`, explicit
form).**  With `K = 8 / ε²` (or `8 / (ε + Γ)²`), `r = 2 ^ (-H)` and `cst = c_*`, the
horizon condition `K log (4 M (t+1)² / δ) ≤ c_* t ^ r` holds for every integer
`t ≥ max {1, (2 K log (16 M / δ) / c_*) ^ (1 / r), (4 K / (c_* s)) ^ (1 / (r - s))}`, for
any `0 < s < r`.  The first threshold has degree `2 / r = 2 ^ (H+1)` in `1 / ε` and the
second degree `2 / (r - s)`, which tends to `2 ^ (H+1)` as `s → 0`. -/
theorem poly_horizon {cst K M δ r s : ℝ} {t : ℕ} (hc : 0 < cst) (hK : 0 ≤ K) (hM : 0 < M)
    (hδ : 0 < δ) (hs : 0 < s) (hsr : s < r) (ht : 1 ≤ t)
    (hta : (max 0 (2 * K * Real.log (16 * M / δ) / cst)) ^ r⁻¹ ≤ (t : ℝ))
    (htb : (4 * K / (cst * s)) ^ (r - s)⁻¹ ≤ (t : ℝ)) :
    K * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ cst * (t : ℝ) ^ r := by
  have hr : 0 < r := by linarith
  have hrs : 0 < r - s := by linarith
  refine horizon_condition_of_poly hc hK hM hδ hs ht ?_ ?_
  · calc 2 * K * Real.log (16 * M / δ) / cst
        ≤ max 0 (2 * K * Real.log (16 * M / δ) / cst) := le_max_right _ _
      _ = ((max 0 (2 * K * Real.log (16 * M / δ) / cst)) ^ r⁻¹) ^ r :=
          (Real.rpow_inv_rpow (le_max_left _ _) hr.ne').symm
      _ ≤ (t : ℝ) ^ r :=
          Real.rpow_le_rpow (Real.rpow_nonneg (le_max_left _ _) _) hta hr.le
  · have hx : 0 ≤ 4 * K / (cst * s) := by positivity
    calc 4 * K / (cst * s) = ((4 * K / (cst * s)) ^ (r - s)⁻¹) ^ (r - s) :=
          (Real.rpow_inv_rpow hx hrs.ne').symm
      _ ≤ (t : ℝ) ^ (r - s) := Real.rpow_le_rpow (Real.rpow_nonneg hx _) htb hrs.le

/-- A finite horizon satisfying the condition always exists (last claim of
`thm:v35horizon`): the condition holds for all sufficiently large `t`. -/
theorem exists_horizon {cst K M δ r : ℝ} (hc : 0 < cst) (hK : 0 ≤ K) (hM : 0 < M)
    (hδ : 0 < δ) (hr : 0 < r) :
    ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t →
      K * Real.log (4 * M * ((t : ℝ) + 1) ^ 2 / δ) ≤ cst * (t : ℝ) ^ r := by
  refine ⟨max 1 (max ⌈(max 0 (2 * K * Real.log (16 * M / δ) / cst)) ^ r⁻¹⌉₊
    ⌈(4 * K / (cst * (r / 2))) ^ (r - r / 2)⁻¹⌉₊), fun t ht => ?_⟩
  have h1 : 1 ≤ t := (le_max_left _ _).trans ht
  have h2 := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have h3 := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
  exact poly_horizon hc hK hM hδ (by linarith : 0 < r / 2) (by linarith) h1
    ((Nat.le_ceil _).trans (by exact_mod_cast h2)) ((Nat.le_ceil _).trans (by exact_mod_cast h3))

end Poly

/-! ### Root-bandit specialisation (`prop:v35rootrates`) -/

section RootRates

variable {ι : Type*}

lemma exists_forall_le_mul_sqrt {α : ℝ} (hα : 0 < α) (B : ℝ) :
    ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → B ≤ α * √(t : ℝ) := by
  refine ⟨⌈(B / α) ^ 2⌉₊, fun t ht => ?_⟩
  have h1 : (B / α) ^ 2 ≤ (t : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast ht)
  have h2 := Real.le_sqrt_of_sq_le h1
  rwa [div_le_iff₀ hα, mul_comm] at h2

/-- Under the local PUCT rule every action is sampled infinitely often, on every sequence
of bounded values (first claim of `prop:v35rootrates`). -/
theorem pullCount_unbounded [Fintype ι] (lam : ι → ℝ) (hlam : ∀ j, 0 < lam j)
    (sel : ℕ → ι) (Q : ι → ℕ → ℝ) (hQ : ∀ n j, 0 ≤ Q j n ∧ Q j n ≤ 1)
    (hrule : ∀ n j, Q j n + lam j * √(n : ℝ) / (1 + (pullCount sel j n : ℝ)) ≤
      Q (sel n) n + lam (sel n) * √(n : ℝ) / (1 + (pullCount sel (sel n) n : ℝ)))
    (i : ι) (B : ℝ) : ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → B ≤ (pullCount sel i t : ℝ) := by
  have hα : 0 < lam i / (8 * √2) := by
    have := hlam i
    positivity
  obtain ⟨t0, ht0⟩ := exists_forall_le_mul_sqrt hα B
  exact ⟨max t0 (puctThreshold univ lam), fun t ht =>
    (ht0 t ((le_max_left _ _).trans ht)).trans
      (local_puct_revisit lam hlam sel Q hQ hrule t ((le_max_right _ _).trans ht) i)⟩

/-- **Deterministic upper bound (core of `prop:v35rootrates`).**  If from time `s0` on the
value of `j` exceeds that of `i` by at least `Δ / 2 > 0`, and `i` is only selected when
its score is at least that of `j`, then `N_i(t) ≤ max {N_i(s0), 2 λ_i √t / Δ}`. -/
theorem root_puct_upper (lam : ι → ℝ) (sel : ℕ → ι) (Q : ι → ℕ → ℝ) {i j : ι}
    (hli : 0 ≤ lam i) (hlj : 0 ≤ lam j) {Δ : ℝ} (hΔ : 0 < Δ) (s0 : ℕ)
    (hrule : ∀ n, s0 ≤ n → sel n = i →
      Q j n + lam j * √(n : ℝ) / (1 + (pullCount sel j n : ℝ)) ≤
        Q i n + lam i * √(n : ℝ) / (1 + (pullCount sel i n : ℝ)))
    (hgap : ∀ n, s0 ≤ n → Δ / 2 ≤ Q j n - Q i n) (t : ℕ) :
    (pullCount sel i t : ℝ) ≤ max (pullCount sel i s0 : ℝ) (2 * lam i * √(t : ℝ) / Δ) := by
  induction t with
  | zero => exact le_max_of_le_left (by exact_mod_cast stepCount_mono_time _ (Nat.zero_le _))
  | succ t ih =>
      by_cases hts : t + 1 ≤ s0
      · exact le_max_of_le_left (by exact_mod_cast stepCount_mono_time _ hts)
      · have hst : s0 ≤ t := by omega
        have hsq : √(t : ℝ) ≤ √((t + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ t)
        have hmul := mul_le_mul_of_nonneg_left hsq hli
        by_cases hsel : sel t = i
        · have hN : pullCount sel i (t + 1) = pullCount sel i t + 1 :=
            stepCount_succ_of_pos hsel
          have h := hrule t hst hsel
          have hg := hgap t hst
          have hbj : 0 ≤ lam j * √(t : ℝ) / (1 + (pullCount sel j t : ℝ)) := by positivity
          have h5 : Δ / 2 ≤ lam i * √(t : ℝ) / (1 + (pullCount sel i t : ℝ)) := by linarith
          rw [le_div_iff₀ (by positivity)] at h5
          apply le_max_of_le_right
          rw [le_div_iff₀ hΔ, hN]
          have hcast : ((pullCount sel i t + 1 : ℕ) : ℝ) = (pullCount sel i t : ℝ) + 1 := by
            push_cast
            ring
          rw [hcast]
          linarith
        · have hN : pullCount sel i (t + 1) = pullCount sel i t := stepCount_succ_of_neg hsel
          rw [hN]
          refine ih.trans (max_le_max le_rfl ?_)
          apply div_le_div_of_nonneg_right _ hΔ.le
          linarith

/-- The same bound in the form `N_i(t) = O(√t)`. -/
theorem root_puct_sqrt_upper (lam : ι → ℝ) (sel : ℕ → ι) (Q : ι → ℕ → ℝ) {i j : ι}
    (hli : 0 ≤ lam i) (hlj : 0 ≤ lam j) {Δ : ℝ} (hΔ : 0 < Δ) (s0 : ℕ)
    (hrule : ∀ n, s0 ≤ n → sel n = i →
      Q j n + lam j * √(n : ℝ) / (1 + (pullCount sel j n : ℝ)) ≤
        Q i n + lam i * √(n : ℝ) / (1 + (pullCount sel i n : ℝ)))
    (hgap : ∀ n, s0 ≤ n → Δ / 2 ≤ Q j n - Q i n) :
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → (pullCount sel i t : ℝ) ≤ C * √(t : ℝ) := by
  refine ⟨(pullCount sel i s0 : ℝ) + 2 * lam i / Δ, fun t ht => ?_⟩
  have h := root_puct_upper lam sel Q hli hlj hΔ s0 hrule hgap t
  have hsq : 1 ≤ √(t : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast ht
  have hN0 : (0 : ℝ) ≤ pullCount sel i s0 := Nat.cast_nonneg _
  have hc : 0 ≤ 2 * lam i / Δ := by positivity
  refine h.trans (max_le ?_ ?_)
  · nlinarith
  · have : 2 * lam i * √(t : ℝ) / Δ = 2 * lam i / Δ * √(t : ℝ) := by ring
    rw [this]
    nlinarith

/-- If every other action has at most `C i √t` samples, action `j` has at least
`t - (∑_{i ≠ j} C i) √t` (last claim of `prop:v35rootrates`). -/
theorem root_puct_best_arm [Fintype ι] [DecidableEq ι] (sel : ℕ → ι) (j : ι) (C : ι → ℝ)
    (t : ℕ) (hC : ∀ i, i ≠ j → (pullCount sel i t : ℝ) ≤ C i * √(t : ℝ)) :
    (t : ℝ) - (∑ i ∈ univ.erase j, C i) * √(t : ℝ) ≤ (pullCount sel j t : ℝ) := by
  have hsum : ((∑ i, pullCount sel i t : ℕ) : ℝ) = t := by rw [sum_pullCount]
  rw [← add_sum_erase univ _ (mem_univ j)] at hsum
  push_cast at hsum
  have hle : ∑ i ∈ univ.erase j, (pullCount sel i t : ℝ) ≤
      (∑ i ∈ univ.erase j, C i) * √(t : ℝ) := by
    rw [sum_mul]
    exact sum_le_sum (fun i hi => hC i (ne_of_mem_erase hi))
  linarith

open MeasureTheory ProbabilityTheory Filter Topology in
/-- **Positive-variance root PUCT: almost-sure square-root counts (Proposition
`prop:v35rootrates`).**

`X i k` is the `k`-th element of the reward tape of action `i`; each tape is integrable,
pairwise independent and identically distributed, with mean `∫ X i 0`.  On every sample
path the run follows the local PUCT rule, with `Q ω i n ∈ [0,1]` equal to the empirical
mean of the first `N_i(n)` tape elements once `N_i(n) ≥ 1` (which holds for tapes in
`[0,1]`).  Almost surely:

* every action `i` with `∫ X i 0 < ∫ X j 0` for some `j` satisfies `N_i(t) ≤ C √t` for all
  `t ≥ 1`; together with `local_puct_revisit`, which gives `N_i(t) ≥ λ_i / (8 √2) √t` for
  `t ≥ T_0` on every path, this is `N_i(t) = Θ(√t)`;
* if `j` has the unique largest mean, `N_j(t) ≥ t - C √t` for all `t ≥ 1`.

No variance assumption is used, and independence across actions is not needed. -/
theorem root_puct_sqrt_rates_ae [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : ι → ℝ) (hlam : ∀ j, 0 < lam j) (X : ι → ℕ → Ω → ℝ)
    (hint : ∀ i, Integrable (X i 0) P)
    (hindep : ∀ i, Pairwise (Function.onFun (fun f g => IndepFun f g P) (X i)))
    (hident : ∀ i k, IdentDistrib (X i k) (X i 0) P P)
    (sel : Ω → ℕ → ι) (Q : Ω → ι → ℕ → ℝ) (hQ : ∀ ω n j, 0 ≤ Q ω j n ∧ Q ω j n ≤ 1)
    (hQmean : ∀ ω n j, 1 ≤ pullCount (sel ω) j n →
      Q ω j n = (pullCount (sel ω) j n : ℝ)⁻¹ *
        ∑ k ∈ range (pullCount (sel ω) j n), X j k ω)
    (hrule : ∀ ω n j,
      Q ω j n + lam j * √(n : ℝ) / (1 + (pullCount (sel ω) j n : ℝ)) ≤
        Q ω (sel ω n) n + lam (sel ω n) * √(n : ℝ) /
          (1 + (pullCount (sel ω) (sel ω n) n : ℝ))) :
    ∀ᵐ ω ∂P,
      (∀ i j, ∫ ω', X i 0 ω' ∂P < ∫ ω', X j 0 ω' ∂P →
        ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → (pullCount (sel ω) i t : ℝ) ≤ C * √(t : ℝ)) ∧
      (∀ j, (∀ i, i ≠ j → ∫ ω', X i 0 ω' ∂P < ∫ ω', X j 0 ω' ∂P) →
        ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → (t : ℝ) - C * √(t : ℝ) ≤ (pullCount (sel ω) j t : ℝ)) := by
  classical
  filter_upwards [ae_all_iff.mpr
    (fun i => strong_law_ae (X i) (hint i) (hindep i) (hident i))] with ω hω
  have hN : ∀ i, Tendsto (fun t => pullCount (sel ω) i t) atTop atTop := by
    intro i
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨t0, ht0⟩ := pullCount_unbounded lam hlam (sel ω) (Q ω) (hQ ω) (hrule ω) i b
    exact ⟨t0, fun t ht => by exact_mod_cast ht0 t ht⟩
  have hQlim : ∀ i, Tendsto (fun t => Q ω i t) atTop (𝓝 (∫ ω', X i 0 ω' ∂P)) := by
    intro i
    have h1 := (hω i).comp (hN i)
    refine Tendsto.congr' ?_ h1
    filter_upwards [(hN i).eventually_ge_atTop 1] with t ht
    simp only [Function.comp_apply, smul_eq_mul]
    exact (hQmean ω t i ht).symm
  have hfirst : ∀ i j, ∫ ω', X i 0 ω' ∂P < ∫ ω', X j 0 ω' ∂P →
      ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → (pullCount (sel ω) i t : ℝ) ≤ C * √(t : ℝ) := by
    intro i j hij
    have hΔ : 0 < ∫ ω', X j 0 ω' ∂P - ∫ ω', X i 0 ω' ∂P := by linarith
    have hsub := (hQlim j).sub (hQlim i)
    have hev : ∀ᶠ t in atTop,
        (∫ ω', X j 0 ω' ∂P - ∫ ω', X i 0 ω' ∂P) / 2 ≤ Q ω j t - Q ω i t :=
      hsub.eventually_const_le (by linarith)
    obtain ⟨s0, hs0⟩ := eventually_atTop.mp hev
    exact root_puct_sqrt_upper lam (sel ω) (Q ω) (hlam i).le (hlam j).le hΔ s0
      (fun n _ hsel => by
        have := hrule ω n j
        rwa [hsel] at this) hs0
  refine ⟨hfirst, fun j hj => ?_⟩
  have hex : ∀ i, ∃ C : ℝ, i ≠ j → ∀ t : ℕ, 1 ≤ t →
      (pullCount (sel ω) i t : ℝ) ≤ C * √(t : ℝ) := by
    intro i
    by_cases h : i = j
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨C, hC⟩ := hfirst i j (hj i h)
      exact ⟨C, fun _ => hC⟩
  choose C hC using hex
  exact ⟨∑ i ∈ univ.erase j, C i, fun t ht =>
    root_puct_best_arm (sel ω) j C t (fun i hi => hC i hi t ht)⟩

end RootRates

/-! ### Simultaneous coverage by Hoeffding's inequality (`lem:v35width`) -/

section Hoeffding

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two-sided Hoeffding bound for the mean of `n ≥ 1` independent `[0,1]`-valued variables
with common mean `m`. -/
lemma puct_hoeffding_two_sided {P : Measure Ω} [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (m : ℝ)
    (hmeas : ∀ k, AEMeasurable (Y k) P) (hbdd : ∀ k, ∀ᵐ ω ∂P, Y k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ k, ∫ ω, Y k ω ∂P = m) (hindep : iIndepFun Y P) {n : ℕ} (hn : 1 ≤ n) {β : ℝ}
    (hβ : 0 ≤ β) :
    P {ω | β < |(n : ℝ)⁻¹ * ∑ k ∈ range n, Y k ω - m|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * n * β ^ 2)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : ∀ k, HasSubgaussianMGF (fun ω => Y k ω - m) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro k
    have h := hasSubgaussianMGF_of_mem_Icc (hmeas k) (hbdd k)
    rwa [hmean k] at h
  have hsubneg : ∀ k, HasSubgaussianMGF (fun ω => m - Y k ω) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro k
    have h := (hsub k).neg
    have heq : (-fun ω => Y k ω - m) = fun ω => m - Y k ω := by
      funext ω
      simp
    rwa [heq] at h
  have hindU : iIndepFun (fun k ω => Y k ω - m) P :=
    hindep.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m)
  have hindL : iIndepFun (fun k ω => m - Y k ω) P :=
    hindep.comp (fun _ x => m - x) (fun _ => measurable_const.sub measurable_id)
  have hε : (0 : ℝ) ≤ n * β := by positivity
  have hU := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindU (n := n) (fun k _ => hsub k) hε
  have hL := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindL (n := n) (fun k _ => hsubneg k) hε
  have hexp : -(n * β) ^ 2 / (2 * n * (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ)) =
      -2 * n * β ^ 2 := by
    simp only [sub_zero, nnNorm_one, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    field_simp
  rw [hexp] at hU hL
  have hsumU : ∀ ω, ∑ k ∈ range n, (Y k ω - m) = ∑ k ∈ range n, Y k ω - n * m := by
    intro ω
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hsumL : ∀ ω, ∑ k ∈ range n, (m - Y k ω) = n * m - ∑ k ∈ range n, Y k ω := by
    intro ω
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hsubset : {ω | β < |(n : ℝ)⁻¹ * ∑ k ∈ range n, Y k ω - m|} ⊆
      {ω | (n : ℝ) * β ≤ ∑ k ∈ range n, (Y k ω - m)} ∪
        {ω | (n : ℝ) * β ≤ ∑ k ∈ range n, (m - Y k ω)} := by
    intro ω hω
    replace hω : β < |(n : ℝ)⁻¹ * ∑ k ∈ range n, Y k ω - m| := hω
    have hid : (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k ∈ range n, Y k ω - m) =
        ∑ k ∈ range n, Y k ω - n * m := by
      field_simp
    rcases lt_abs.mp hω with h | h
    · left
      show (n : ℝ) * β ≤ ∑ k ∈ range n, (Y k ω - m)
      rw [hsumU, ← hid]
      exact (mul_le_mul_of_nonneg_left h.le hnpos.le)
    · right
      show (n : ℝ) * β ≤ ∑ k ∈ range n, (m - Y k ω)
      rw [hsumL]
      have := mul_le_mul_of_nonneg_left h.le hnpos.le
      linarith
  have hUe : P {ω | (n : ℝ) * β ≤ ∑ k ∈ range n, (Y k ω - m)} ≤
      ENNReal.ofReal (Real.exp (-2 * n * β ^ 2)) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hU
  have hLe : P {ω | (n : ℝ) * β ≤ ∑ k ∈ range n, (m - Y k ω)} ≤
      ENNReal.ofReal (Real.exp (-2 * n * β ^ 2)) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hL
  calc P {ω | β < |(n : ℝ)⁻¹ * ∑ k ∈ range n, Y k ω - m|}
      ≤ P ({ω | (n : ℝ) * β ≤ ∑ k ∈ range n, (Y k ω - m)} ∪
          {ω | (n : ℝ) * β ≤ ∑ k ∈ range n, (m - Y k ω)}) := measure_mono hsubset
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * n * β ^ 2)) +
          ENNReal.ofReal (Real.exp (-2 * n * β ^ 2)) := add_le_add hUe hLe
    _ = ENNReal.ofReal (2 * Real.exp (-2 * n * β ^ 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]

lemma sum_range_one_div_mul_succ (n : ℕ) :
    ∑ k ∈ range (n + 1), 1 / ((k : ℝ) * (k + 1)) = 1 - 1 / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      field_simp
      ring

lemma sum_range_one_div_mul_succ_le (n : ℕ) :
    ∑ k ∈ range n, 1 / ((k : ℝ) * (k + 1)) ≤ 1 := by
  rcases n with _ | n
  · simp
  · rw [sum_range_one_div_mul_succ]
    have : (0 : ℝ) ≤ 1 / (n + 1) := by positivity
    linarith

/-- **Anytime coverage (first claim of Lemma `lem:v35width`).**  `X z k` is the `k`-th
element of the tape of terminal `z`: `[0,1]`-valued, with mean `μ z`, the elements of one
tape being independent.  With `M = |Z|` and the radius `β_M(n, δ)` of `eq:v35radius`, the
event that some empirical tape mean leaves its interval at some intrinsic count `k ≥ 1` has
probability at most `δ / 2`.  The event is indexed by deterministic intrinsic counts, so it
covers every adaptive sampling and stopping rule. -/
theorem hoeffding_tape_coverage (P : Measure Ω) [IsProbabilityMeasure P] {Z : Type*}
    [Fintype Z] [Nonempty Z] (X : Z → ℕ → Ω → ℝ) (μ : Z → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, iIndepFun (X z) P) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    P {ω | ∃ z k, 1 ≤ k ∧ puctRadius (Fintype.card Z) δ k <
        |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|} ≤ ENNReal.ofReal (δ / 2) := by
  set M : ℝ := (Fintype.card Z : ℝ) with hMdef
  have hM : 1 ≤ M := by
    rw [hMdef]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  have hMpos : 0 < M := by linarith
  set d : ℝ := δ / (2 * M) with hd
  have hdpos : 0 < d := by positivity
  have hterm : ∀ z k, P {ω | 1 ≤ k ∧ puctRadius M δ k <
      |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|} ≤
        ENNReal.ofReal (d * (1 / ((k : ℝ) * (k + 1)))) := by
    intro z k
    by_cases hk : 1 ≤ k
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hset : {ω | 1 ≤ k ∧ puctRadius M δ k <
          |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|} =
          {ω | puctRadius M δ k < |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|} := by
        ext ω
        simp [hk]
      rw [hset]
      have hβ0 : 0 ≤ puctRadius M δ k := Real.sqrt_nonneg _
      refine (puct_hoeffding_two_sided (X z) (μ z) (hmeas z) (hbdd z) (hmean z) (hindep z) hk
        (β := puctRadius M δ k) hβ0).trans (le_of_eq ?_)
      congr 1
      have harg : 1 ≤ 4 * M * k * (k + 1) / δ := by
        rw [one_le_div hδ0]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith [mul_le_mul hM hk1 zero_le_one hMpos.le]
      have hargpos : 0 < 4 * M * k * (k + 1) / δ := by linarith
      have hsq : puctRadius M δ k ^ 2 = Real.log (4 * M * k * (k + 1) / δ) / (2 * k) := by
        unfold puctRadius
        exact Real.sq_sqrt (div_nonneg (Real.log_nonneg harg) (by positivity))
      have hexp : -2 * (k : ℝ) * puctRadius M δ k ^ 2 =
          -Real.log (4 * M * k * (k + 1) / δ) := by
        rw [hsq]
        field_simp
      rw [hexp, Real.exp_neg, Real.exp_log hargpos, hd]
      field_simp
      ring
    · have hset : {ω | 1 ≤ k ∧ puctRadius M δ k <
          |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|} = ∅ := by
        ext ω
        simp [hk]
      rw [hset, measure_empty]
      exact zero_le
  have hunion : {ω | ∃ z k, 1 ≤ k ∧ puctRadius M δ k <
      |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|} =
      ⋃ z, ⋃ k, {ω | 1 ≤ k ∧ puctRadius M δ k <
        |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|} := by
    ext ω
    simp
  have hz : ∀ z, P (⋃ k, {ω | 1 ≤ k ∧ puctRadius M δ k <
      |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|}) ≤ ENNReal.ofReal d := by
    intro z
    refine (measure_iUnion_le _).trans ((tsum_le_tsum (hterm z)).trans ?_)
    refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), ← mul_sum]
    apply ENNReal.ofReal_le_ofReal
    have := sum_range_one_div_mul_succ_le n
    nlinarith
  rw [hunion]
  calc P (⋃ z, ⋃ k, {ω | 1 ≤ k ∧ puctRadius M δ k <
        |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|})
      ≤ ∑' z, P (⋃ k, {ω | 1 ≤ k ∧ puctRadius M δ k <
        |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|}) := measure_iUnion_le _
    _ = ∑ z, P (⋃ k, {ω | 1 ≤ k ∧ puctRadius M δ k <
        |(k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω - μ z|}) := tsum_fintype _
    _ ≤ ∑ _z : Z, ENNReal.ofReal d := sum_le_sum (fun z _ => hz z)
    _ = ENNReal.ofReal (δ / 2) := by
        rw [sum_const, card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        rw [hd, ← hMdef]
        field_simp

end Hoeffding

/-! ### `thm:v35horizon`, assembled -/

section Assembled

open MeasureTheory

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {V E : Type*} [Fintype E]
  {Ω : Type*} [MeasurableSpace Ω] {A : Type*}

/-- **High-probability on-policy PUCT certification horizon (Theorem `thm:v35horizon`),
assembled.**  A fixed graph with fixed positive weights; on every sample path the search
satisfies the contract `PUCTRun`; terminal `z` is sampled by reading its tape `X z` in
order, the tape elements being `[0,1]`-valued with mean `μ z` and independent within a
tape; the monitor uses the running intersections with radius `β_M(n, δ)`, `M = |Z|`, stops
at the first exact `ε`-certificate and returns a certified action (`hmon`).  For every
`t ≥ t_*` with `c_* t ^ (2 ^ (-H)) ≥ (8 / ε²) log (4 M (t+1)² / δ)`, the event
`{τ ≤ t and Reg ≤ ε}` fails with probability at most `δ / 2`. -/
theorem puct_horizon_full {src tgt : E → V} {root : V} {lam : E → ℝ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    (vis : Ω → ℕ → V → Prop) (ch : Ω → ℕ → V → E) (Q : Ω → E → ℕ → ℝ)
    (hrun : ∀ ω, PUCTRun src tgt root lam (vis ω) (ch ω) (Q ω))
    (term : Z → V) (path : Z → List E) (hpath : ∀ z, IsPath src tgt (path z) root (term z))
    (H : ℕ) (hH : ∀ z, (path z).length ≤ H)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hreach : ∀ z, ∃ a, z ∈ supp a)
    (μ : Z → ℝ) (hμ : ∀ z, μ z ∈ Set.Icc (0 : ℝ) 1) (X : Z → ℕ → Ω → ℝ)
    (hmeas : ∀ z k, AEMeasurable (X z k) P)
    (hbdd : ∀ z k, ∀ᵐ ω ∂P, X z k ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z k, ∫ ω, X z k ω ∂P = μ z) (hindep : ∀ z, ProbabilityTheory.iIndepFun (X z) P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ε : ℝ) (τ : Ω → ℕ) (rec : Ω → A)
    (hmon : ∀ ω s, (∃ a, exactCert (supp a) (hne a)
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) s)) ≤ ε) →
        τ ω ≤ s ∧ exactCert (supp (rec ω)) (hne (rec ω))
          (fun z => runLower (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω)))
          (fun z => runUpper (fun k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω)
            (puctRadius (Fintype.card Z) δ) (visitCount (vis ω) (term z) (τ ω))) ≤ ε)
    (t : ℕ) (ht : puctTstar src lam path ≤ t) (hε : 0 < ε)
    (hcond : 8 / ε ^ 2 * Real.log (4 * (Fintype.card Z : ℝ) * ((t : ℝ) + 1) ^ 2 / δ) ≤
      puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ)) :
    P {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)} ≤
      ENNReal.ofReal (δ / 2) := by
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω0⟩⟩
  · rw [Set.eq_empty_of_isEmpty {ω | ¬ (τ ω ≤ t ∧ regret (supp (rec ω)) (hne (rec ω)) μ ≤ ε)},
      measure_empty]
    exact zero_le
  have ht1 : (1 : ℝ) ≤ t := by
    have h1 : (1 : ℝ) ≤ (puctTstar src lam path : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
    exact h1.trans (by exact_mod_cast ht)
  have hm : 0 < puctCstar lam path * (t : ℝ) ^ (1 / 2 ^ H : ℝ) :=
    mul_pos (puctCstar_pos (hrun ω0).lam_pos path) (Real.rpow_pos_of_pos (by linarith) _)
  have hM : (1 : ℝ) ≤ (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  exact puct_horizon P supp hne hreach μ hμ
    (fun ω z k => (k : ℝ)⁻¹ * ∑ i ∈ range k, X z i ω) hM hδ0 hδ1
    (fun s ω z => visitCount (vis ω) (term z) s) _
    (hoeffding_tape_coverage P X μ hmeas hbdd hmean hindep hδ0 hδ1) ε τ rec hmon t hm
    (fun ω z => ⟨puct_terminal_coverage' (hrun ω) term path hpath H hH t ht z,
      stepCount_le _ t⟩) hε hcond

end Assembled

end JointRootCert
