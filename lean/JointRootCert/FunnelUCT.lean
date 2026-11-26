/-
The local-UCT half of Theorem `thm:onpolicy-uct` / `thm:selective-separation` (Selective
vs. eager maintenance separations on UCT and Root-PUCT funnels) of the appendix
"Certification Along Passive Graph-Search Trajectories".  The Root-PUCT half is
`v2separation_monitors` in `MonitorWork.lean`.

* The recursive model (`FunnelSearch`): local UCT (`c = 1`) at the root over the three root
  actions and local UCT at the binary split below the funnel action, each with the
  empirical means of the observed returns and its own visit clock; the two exits return
  `3/20` and `1/5`, the direct action `4/5`, the near rival `4/5 - g`.  The root-level value
  facts that `FunnelRoot` (in `UCTWork.lean`) takes as fields are derived
  (`FunnelSearch.funnelRoot`); such searches exist (`exists_funnelSearch`).
* Step 2, constant-time retirement (`funnel_counts_const`, `funnel_retired`): there is a
  rollout count `t₀` depending only on `δ` after which the direct action and both exits
  have radius at most `1/4`, and the selective monitor has retired the funnel action.
* Step 3, `τ ≤ m` (`funnel_stops_at_m`): for all large `m` the stopping test passes after
  `m` rollouts.
* Step 4, revisits (`funnel_changes_ge`): after `t₀` every rollout through the funnel
  strictly changes the interval of the visited exit.
* The assembled statement (`onpolicy_uct_funnel`): for `g = (1/4) m^{-1/16}`, `ε = g/2` and
  all large `m`, both monitors expose the same output at every step, the common stopping
  time satisfies `(64/9) m^{1/8} < τ ≤ m`, the selective total work is at most `C m` and the
  eager total work at least `c m log m`.

* The alternating ladder (`ladder_cover_lower`): only the cover count, `m²/2` blocks for
  the internal dyadic covers, under an explicit reading of a family that the manuscript
  does not define.

The UCT index is the one used in the proof, `Q + √(log (1 + t) / N)` with `t` the number
of earlier visits of the node, as in `UCTWork.lean`; the manuscript's displayed definition
`eq:uct-index` has `log N_t(v)`.  The confidence radius is the Hoeffding radius for the four
canonical terminals of the funnel.  Work is computed in the cost model of `MonitorWork.lean`.
-/
import JointRootCert.UCTWork
import JointRootCert.MonitorWork
import JointRootCert.Representation

namespace JointRootCert

open Finset

noncomputable section

/-! ### The recursive funnel model -/

/-- Exit terminal of the split arm `e`: arm `0` leads to terminal `2`, arm `1` to terminal
`3`. -/
def funExit (e : Fin 2) : Fin 4 := if e = 0 then 2 else 3

/-- Deterministic rewards of the four canonical terminals: `4/5` (direct action `b`),
`4/5 - g` (near rival `a'`), `3/20` and `1/5` (the two exits of the funnel). -/
def funMu (g : ℝ) (z : Fin 4) : ℝ :=
  if z = 0 then 4 / 5 else if z = 1 then 4 / 5 - g else if z = 2 then 3 / 20 else 1 / 5

/-- Terminal reached by rollout `s`: root actions `0` and `1` are terminal vertices; a
rollout through the funnel action `2` takes, at the split, the arm chosen at the split's
current visit number (the number of earlier rollouts through the funnel) and then reaches
that arm's exit whatever path it takes inside the fan. -/
def funTerm (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (s : ℕ) : Fin 4 :=
  if sel s = 2 then funExit (sub (uctCount sel s 2)) else Fin.castSucc (sel s)

private theorem funAux :
    ∀ (a : Fin 3) (e : Fin 2),
      ((if a = 2 then funExit e else Fin.castSucc a) = 0 ↔ a = 0) ∧
      ((if a = 2 then funExit e else Fin.castSucc a) = 1 ↔ a = 1) ∧
      ∀ e' : Fin 2, ((if a = 2 then funExit e else Fin.castSucc a) = funExit e' ↔
        a = 2 ∧ e = e') := by
  decide

/-- **Recursive local UCT on the two-exit funnel** (`c = 1`).  `sel s` is the root action
of rollout `s` and `sub j` the arm taken at the `j`-th visit of the split below the funnel
action.  The root is a UCT node over the three root actions and the split a UCT node over
its two arms; the empirical mean of an edge is the average of the rewards observed through
it, and each node uses its own number of earlier visits.  The choices inside the two fans
do not affect the terminal reached and are left arbitrary. -/
structure FunnelSearch (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) : Prop where
  root : UCTRun 1 (fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a),
    funMu g (funTerm sel sub s)) / uctCount sel t a) sel
  split : UCTRun 1 (fun j e => (∑ i ∈ (range j).filter (fun i => sub i = e),
    funMu g (funExit (sub i))) / uctCount sub j e) sub

theorem funMu_exit (g : ℝ) (e : Fin 2) :
    3 / 20 ≤ funMu g (funExit e) ∧ funMu g (funExit e) ≤ 1 / 5 := by
  unfold funExit
  split_ifs <;> simp [funMu] <;> norm_num

theorem funMu_bounds {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5) (z : Fin 4) :
    0 ≤ funMu g z ∧ funMu g z ≤ 1 := by
  unfold funMu
  split_ifs <;> constructor <;> linarith

section Means

variable {ι : Type*} [DecidableEq ι]

/-- An edge whose returns all equal `μ` has empirical mean `μ` once it has been tried. -/
theorem fuMean_const (sel : ℕ → ι) (v : ℕ → ℝ) (a : ι) (μ : ℝ) (t : ℕ)
    (hv : ∀ s, sel s = a → v s = μ) (hpos : 1 ≤ uctCount sel t a) :
    (∑ s ∈ (range t).filter (fun s => sel s = a), v s) / uctCount sel t a = μ := by
  have hs : ∑ s ∈ (range t).filter (fun s => sel s = a), v s = uctCount sel t a * μ := by
    rw [Finset.sum_congr rfl (fun s hs => hv s (Finset.mem_filter.mp hs).2), Finset.sum_const,
      nsmul_eq_mul]
    rfl
  have hne : (uctCount sel t a : ℝ) ≠ 0 := by exact_mod_cast (by omega : uctCount sel t a ≠ 0)
  rw [hs, mul_div_cancel_left₀ _ hne]

/-- An edge whose returns lie in `[0, hi]` has empirical mean in `[0, hi]` (the mean of an
untried edge is `0`). -/
theorem fuMean_bounds (sel : ℕ → ι) (v : ℕ → ℝ) (a : ι) {hi : ℝ} (t : ℕ)
    (hv : ∀ s, sel s = a → 0 ≤ v s ∧ v s ≤ hi) (hhi : 0 ≤ hi) :
    0 ≤ (∑ s ∈ (range t).filter (fun s => sel s = a), v s) / uctCount sel t a ∧
      (∑ s ∈ (range t).filter (fun s => sel s = a), v s) / uctCount sel t a ≤ hi := by
  have h0 : 0 ≤ ∑ s ∈ (range t).filter (fun s => sel s = a), v s :=
    Finset.sum_nonneg (fun s hs => (hv s (Finset.mem_filter.mp hs).2).1)
  have h1 : ∑ s ∈ (range t).filter (fun s => sel s = a), v s ≤ uctCount sel t a * hi := by
    have := Finset.sum_le_sum (s := (range t).filter (fun s => sel s = a)) (f := v)
      (g := fun _ => hi) (fun s hs => (hv s (Finset.mem_filter.mp hs).2).2)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  refine ⟨div_nonneg h0 (Nat.cast_nonneg _), ?_⟩
  rcases Nat.eq_zero_or_pos (uctCount sel t a) with hz | hp
  · rw [hz, Nat.cast_zero, div_zero]
    exact hhi
  · rw [div_le_iff₀ (by exact_mod_cast hp)]
    linarith [mul_comm (uctCount sel t a : ℝ) hi]

end Means

variable {g : ℝ} {sel : ℕ → Fin 3} {sub : ℕ → Fin 2}

/-- The root value table used with `FunnelRoot`: the deterministic returns of the two
terminal root actions and the empirical mean of the funnel action. -/
def funQ (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) (a : Fin 3) : ℝ :=
  if a = 2 then (∑ s ∈ (range t).filter (fun s => sel s = 2), funMu g (funTerm sel sub s))
    / uctCount sel t 2
  else funMu g (Fin.castSucc a)

/-- Once a root action has been tried, its empirical mean is `funQ`. -/
theorem funQ_eq (g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) {t : ℕ} {a : Fin 3}
    (hpos : 1 ≤ uctCount sel t a) :
    (∑ s ∈ (range t).filter (fun s => sel s = a), funMu g (funTerm sel sub s))
      / uctCount sel t a = funQ g sel sub t a := by
  unfold funQ
  by_cases ha : a = 2
  · subst ha
    rw [ite_eq_left rfl]
  · rw [ite_eq_right ha]
    exact fuMean_const sel _ a _ t (fun s hs => by rw [funTerm, hs, ite_eq_right ha]) hpos

/-- **Derived value facts.**  The root of a recursive funnel search is a `FunnelRoot`: the
direct action has value `4/5`, the near rival `4/5 - g`, and the empirical mean of the
funnel action lies in `[0, 1/5]` at all times, whatever the split does. -/
theorem FunnelSearch.funnelRoot (h : FunnelSearch g sel sub) :
    FunnelRoot g (funQ g sel sub) sel where
  uct := ⟨h.root.forced, fun t ht j => by
    have := h.root.greedy t ht j
    rw [funQ_eq g sel sub (h.root.one_le j ht),
      funQ_eq g sel sub (h.root.one_le (sel t) ht)] at this
    exact this⟩
  qb := fun t => by simp [funQ, funMu]
  qa := fun t => by simp [funQ, funMu]
  qC0 := fun t => by
    rw [funQ, ite_eq_left rfl]
    exact (fuMean_bounds sel _ 2 t (fun s hs => by
      rw [funTerm, ite_eq_left hs]
      exact ⟨by linarith [(funMu_exit g (sub (uctCount sel s 2))).1],
        (funMu_exit g (sub (uctCount sel s 2))).2⟩) (by norm_num)).1
  qC1 := fun t => by
    rw [funQ, ite_eq_left rfl]
    exact (fuMean_bounds sel _ 2 t (fun s hs => by
      rw [funTerm, ite_eq_left hs]
      exact ⟨by linarith [(funMu_exit g (sub (uctCount sel s 2))).1],
        (funMu_exit g (sub (uctCount sel s 2))).2⟩) (by norm_num)).2

/-- The empirical means at the split lie in `[0, 1]`. -/
theorem FunnelSearch.split_bounds (_h : FunnelSearch g sel sub) (j : ℕ) (e : Fin 2) :
    0 ≤ (∑ i ∈ (range j).filter (fun i => sub i = e), funMu g (funExit (sub i)))
        / uctCount sub j e ∧
      (∑ i ∈ (range j).filter (fun i => sub i = e), funMu g (funExit (sub i)))
        / uctCount sub j e ≤ 1 :=
  fuMean_bounds sub _ e j (fun i _ => ⟨by linarith [(funMu_exit g (sub i)).1],
    by linarith [(funMu_exit g (sub i)).2]⟩) zero_le_one

/-! ### Terminal counts -/

/-- Number of observations of terminal `z` among the first `t` rollouts. -/
def funCnt (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) (z : Fin 4) : ℕ :=
  uctCount (funTerm sel sub) t z

theorem funCnt_zero (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) :
    funCnt sel sub t 0 = uctCount sel t 0 := by
  unfold funCnt uctCount
  congr 1
  exact Finset.filter_congr (fun s _ => (funAux (sel s) _).1)

theorem funCnt_one (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) :
    funCnt sel sub t 1 = uctCount sel t 1 := by
  unfold funCnt uctCount
  congr 1
  exact Finset.filter_congr (fun s _ => (funAux (sel s) _).2.1)

/-- The exit of arm `e` has been observed as often as the split has chosen `e` among its
first `N_C(t)` visits. -/
theorem funCnt_exit (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (e : Fin 2) :
    ∀ t, funCnt sel sub t (funExit e) = uctCount sub (uctCount sel t 2) e
  | 0 => by simp [funCnt, uctCount]
  | t + 1 => by
      have ih := funCnt_exit sel sub e t
      unfold funCnt at ih ⊢
      have hiff : funTerm sel sub t = funExit e ↔ sel t = 2 ∧ sub (uctCount sel t 2) = e :=
        (funAux (sel t) (sub (uctCount sel t 2))).2.2 e
      rw [uctCount_succ (funTerm sel sub) t (funExit e), ih, uctCount_succ sel t 2]
      by_cases h2 : sel t = 2
      · rw [ite_eq_left h2, uctCount_succ]
        congr 1
        by_cases he : sub (uctCount sel t 2) = e
        · rw [ite_eq_left he, ite_eq_left (hiff.mpr ⟨h2, he⟩)]
        · rw [ite_eq_right he, ite_eq_right (fun hh => he (hiff.mp hh).2)]
      · rw [ite_eq_right h2, add_zero, ite_eq_right (fun hh => h2 (hiff.mp hh).1), add_zero]

theorem funCnt_mono (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (z : Fin 4) {s t : ℕ} (hst : s ≤ t) :
    funCnt sel sub s z ≤ funCnt sel sub t z := uctCount_mono _ z hst

/-! ### Radius and terminal tables -/

private theorem fu_exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

/-- The Hoeffding width strictly decreases on `[1, ∞)` for `M ≥ 2` and `δ ∈ (0, 1]`. -/
theorem fuWidth_strictAntiOn {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    StrictAntiOn (hoeffdingWidth M δ) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < 4 * M / δ := div_pos (by linarith) hδ0
  have hc : 2 < Real.log (4 * M / δ) := by
    rw [Real.lt_log_iff_exp_lt hc0]
    refine lt_of_lt_of_le fu_exp_two_lt_eight ?_
    rw [le_div_iff₀ hδ0]
    nlinarith
  have ex : ∀ z : ℝ, 0 < z →
      Real.log (4 * M * z ^ 2 / δ) = Real.log (4 * M / δ) + 2 * Real.log z := by
    intro z hz
    rw [show 4 * M * z ^ 2 / δ = 4 * M / δ * z ^ 2 by ring,
      Real.log_mul hc0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hr : Real.log (y / x) < y / x - 1 :=
    Real.log_lt_sub_one_of_pos (by positivity) (by
      intro h
      rw [div_eq_one_iff_eq hx0.ne'] at h
      exact hxy.ne' h)
  rw [Real.log_div hy0.ne' hx0.ne'] at hr
  have h1 : x * Real.log y < x * Real.log x + y - x := by
    have h2 := mul_lt_mul_of_pos_left hr hx0
    have h3 : x * (y / x - 1) = y - x := by field_simp
    rw [h3] at h2
    linarith
  have hsq : Real.sqrt (Real.log (4 * M * y ^ 2 / δ) / (2 * y))
      < Real.sqrt (Real.log (4 * M * x ^ 2 / δ) / (2 * x)) := by
    apply Real.sqrt_lt_sqrt
    · rw [ex y hy0]
      exact div_nonneg (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ y)])
        (by positivity)
    · rw [ex x hx0, ex y hy0, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hc),
        mul_nonneg (sub_pos.mpr hxy).le hlx]
  show hoeffdingWidth M δ y < hoeffdingWidth M δ x
  unfold hoeffdingWidth
  linarith

/-- The confidence radius `β(n) = √(log (16 n² / δ) / (2n))` for the four canonical
terminals of the funnel. -/
def funRad (δ : ℝ) (n : ℕ) : ℝ := hoeffdingWidth 4 δ n / 2

theorem funRad_nonneg (δ : ℝ) (n : ℕ) : 0 ≤ funRad δ n := by
  unfold funRad hoeffdingWidth
  have := Real.sqrt_nonneg (Real.log (4 * 4 * (n : ℝ) ^ 2 / δ) / (2 * n))
  linarith

variable {δ : ℝ}

/-- The radius strictly decreases with the count. -/
theorem funRad_strict (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    funRad δ k < funRad δ j := by
  have := (fuWidth_strictAntiOn (M := 4) (by norm_num) hδ0 hδ1)
    (Set.mem_Ici.mpr (by exact_mod_cast hj : (1 : ℝ) ≤ (j : ℝ)))
    (Set.mem_Ici.mpr (by exact_mod_cast hj.trans hjk.le : (1 : ℝ) ≤ (k : ℝ)))
    (by exact_mod_cast hjk : (j : ℝ) < (k : ℝ))
  unfold funRad
  linarith

theorem funRad_anti (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    funRad δ k ≤ funRad δ j := by
  rcases Nat.eq_or_lt_of_le hjk with h | h
  · rw [h]
  · exact (funRad_strict hδ0 hδ1 hj h).le

/-- A count from which the radius is at most `1/4`. -/
def funK0 (δ : ℝ) : ℕ :=
  max 1 ⌈32 / (1 / 2 : ℝ) ^ 2 * Real.log (32 * 4 / (δ * (1 / 2 : ℝ) ^ 2))⌉₊

theorem funK0_pos (δ : ℝ) : 1 ≤ funK0 δ := le_max_left _ _

theorem funRad_le_quarter (hδ0 : 0 < δ) (hδ1 : δ < 1) {n : ℕ} (hn : funK0 δ ≤ n) :
    funRad δ n ≤ 1 / 4 := by
  have hx : 32 / (1 / 2 : ℝ) ^ 2 * Real.log (32 * 4 / (δ * (1 / 2 : ℝ) ^ 2)) ≤ (n : ℝ) := by
    have h1 : ⌈32 / (1 / 2 : ℝ) ^ 2 * Real.log (32 * 4 / (δ * (1 / 2 : ℝ) ^ 2))⌉₊ ≤ n :=
      le_trans (le_max_right _ _) hn
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have := width_inversion (M := 4) (by norm_num) hδ0 hδ1 (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) hx
  unfold funRad
  linarith

/-- The terminal observation table after `t` rollouts: `[0, 1]` for an unsampled terminal,
otherwise the clipped interval of radius `β(count)` around the deterministic mean. -/
def funTab (δ g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) (z : Fin 4) : ℝ × ℝ :=
  if funCnt sel sub t z = 0 then (0, 1)
  else (max 0 (funMu g z - funRad δ (funCnt sel sub t z)),
    min 1 (funMu g z + funRad δ (funCnt sel sub t z)))

/-- The table seen by the monitors at their step `k`: after the three forced root rollouts
and `k` further ones. -/
def funBox (δ g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (k : ℕ) : Fin 4 → ℝ × ℝ :=
  funTab δ g sel sub (3 + k)

theorem funTab_lo_le (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (t : ℕ) (z : Fin 4) : (funTab δ g sel sub t z).1 ≤ funMu g z := by
  obtain ⟨h0, -⟩ := funMu_bounds hg0 hg z
  have hb := funRad_nonneg δ (funCnt sel sub t z)
  unfold funTab
  split_ifs
  · exact h0
  · exact max_le h0 (by linarith)

theorem funTab_hi_ge (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (t : ℕ) (z : Fin 4) : funMu g z ≤ (funTab δ g sel sub t z).2 := by
  obtain ⟨-, h1⟩ := funMu_bounds hg0 hg z
  have hb := funRad_nonneg δ (funCnt sel sub t z)
  unfold funTab
  split_ifs
  · exact h1
  · exact le_min h1 (by linarith)

theorem funTab_of_pos (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) {t : ℕ} {z : Fin 4}
    (hc : 1 ≤ funCnt sel sub t z) :
    funTab δ g sel sub t z = (max 0 (funMu g z - funRad δ (funCnt sel sub t z)),
      min 1 (funMu g z + funRad δ (funCnt sel sub t z))) := by
  unfold funTab
  rw [ite_eq_right (by omega)]

/-- **Nested nonempty boxes.** -/
theorem funTab_nested (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5)
    (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) :
    (∀ z s t, s ≤ t → (funTab δ g sel sub s z).1 ≤ (funTab δ g sel sub t z).1 ∧
        (funTab δ g sel sub t z).2 ≤ (funTab δ g sel sub s z).2) ∧
      ∀ t z, (funTab δ g sel sub t z).1 ≤ (funTab δ g sel sub t z).2 := by
  constructor
  · intro z s t hst
    have hc := funCnt_mono sel sub z hst
    unfold funTab
    by_cases h0 : funCnt sel sub s z = 0
    · rw [ite_eq_left h0]
      by_cases h1 : funCnt sel sub t z = 0
      · rw [ite_eq_left h1]
        exact ⟨le_rfl, le_rfl⟩
      · rw [ite_eq_right h1]
        exact ⟨le_max_left _ _, min_le_left _ _⟩
    · have h1 : funCnt sel sub t z ≠ 0 := by omega
      rw [ite_eq_right h0, ite_eq_right h1]
      have := funRad_anti hδ0 hδ1 (by omega : 1 ≤ funCnt sel sub s z) hc
      exact ⟨max_le_max le_rfl (by linarith), min_le_min le_rfl (by linarith)⟩
  · intro t z
    exact (funTab_lo_le hg0 hg sel sub t z).trans (funTab_hi_ge hg0 hg sel sub t z)

/-! ### Exact root-action intervals on the funnel -/

namespace MaxCirc

variable {Z : Type*}

/-- The MAX value is monotone in the environment. -/
theorem fuEval_mono {f g : Z → ℝ} (h : ∀ z, f z ≤ g z) : ∀ c : MaxCirc Z, eval f c ≤ eval g c
  | term z => h z
  | unary c => fuEval_mono h c
  | bin c d => max_le_max (fuEval_mono h c) (fuEval_mono h d)

end MaxCirc

/-- The exact intervals of the three root actions of the funnel: the terminal intervals of
`b` and `a'`, and the MAX of the two exit intervals for the funnel action. -/
theorem funCirc_ival (m : ℕ) (x : Fin 4 → ℝ × ℝ) :
    (monFunnelCirc m 0).ival x = x 0 ∧ (monFunnelCirc m 1).ival x = x 1 ∧
      (monFunnelCirc m 2).ival x = (max (x 2).1 (x 3).1, max (x 2).2 (x 3).2) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : monFunnelCirc m 0 = .term 0 := by simp [monFunnelCirc]
    rw [e]
    rfl
  · have e : monFunnelCirc m 1 = .term 1 := by simp [monFunnelCirc]
    rw [e]
    rfl
  · rw [monFunnelCirc_two]
    show monJoin ((monFunnelFan m 2).ival x) ((monFunnelFan m 3).ival x) = _
    rw [MaxCirc.ival_of_onlyTerm x (c := monFunnelFan m 2) (monFanZ_onlyTerm _ _ _),
      MaxCirc.ival_of_onlyTerm x (c := monFunnelFan m 3) (monFanZ_onlyTerm _ _ _)]
    rfl

/-- The exact root-action intervals of the funnel are nested and nonempty along the
search, as `monRun_outputs` requires. -/
theorem funnel_nested (m : ℕ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5)
    (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) :
    (∀ a s t, s ≤ t → monL (monFunnelCirc m) (funBox δ g sel sub) s a
        ≤ monL (monFunnelCirc m) (funBox δ g sel sub) t a) ∧
    (∀ a s t, s ≤ t → monU (monFunnelCirc m) (funBox δ g sel sub) t a
        ≤ monU (monFunnelCirc m) (funBox δ g sel sub) s a) ∧
    ∀ t a, monL (monFunnelCirc m) (funBox δ g sel sub) t a
        ≤ monU (monFunnelCirc m) (funBox δ g sel sub) t a := by
  obtain ⟨hmono, hne⟩ := funTab_nested hδ0 hδ1 hg0 hg sel sub
  refine ⟨fun a s t hst => ?_, fun a s t hst => ?_, fun t a => ?_⟩
  · show MaxCirc.eval (fun z => (funBox δ g sel sub s z).1) (monFunnelCirc m a)
      ≤ MaxCirc.eval (fun z => (funBox δ g sel sub t z).1) (monFunnelCirc m a)
    exact MaxCirc.fuEval_mono (fun z => (hmono z (3 + s) (3 + t) (by omega)).1) _
  · show MaxCirc.eval (fun z => (funBox δ g sel sub t z).2) (monFunnelCirc m a)
      ≤ MaxCirc.eval (fun z => (funBox δ g sel sub s z).2) (monFunnelCirc m a)
    exact MaxCirc.fuEval_mono (fun z => (hmono z (3 + s) (3 + t) (by omega)).2) _
  · show MaxCirc.eval (fun z => (funBox δ g sel sub t z).1) (monFunnelCirc m a)
      ≤ MaxCirc.eval (fun z => (funBox δ g sel sub t z).2) (monFunnelCirc m a)
    exact MaxCirc.fuEval_mono (fun z => hne (3 + t) z) _

private theorem fu_fin3 (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ a, P a := by
  intro a
  fin_cases a
  exacts [h0, h1, h2]

theorem funL_zero (m : ℕ) (x : ℕ → Fin 4 → ℝ × ℝ) (k : ℕ) :
    monL (monFunnelCirc m) x k 0 = (x k 0).1 := by
  unfold monL
  rw [(funCirc_ival m (x k)).1]

theorem funU_zero (m : ℕ) (x : ℕ → Fin 4 → ℝ × ℝ) (k : ℕ) :
    monU (monFunnelCirc m) x k 0 = (x k 0).2 := by
  unfold monU
  rw [(funCirc_ival m (x k)).1]

theorem funL_one (m : ℕ) (x : ℕ → Fin 4 → ℝ × ℝ) (k : ℕ) :
    monL (monFunnelCirc m) x k 1 = (x k 1).1 := by
  unfold monL
  rw [(funCirc_ival m (x k)).2.1]

theorem funU_one (m : ℕ) (x : ℕ → Fin 4 → ℝ × ℝ) (k : ℕ) :
    monU (monFunnelCirc m) x k 1 = (x k 1).2 := by
  unfold monU
  rw [(funCirc_ival m (x k)).2.1]

theorem funL_two (m : ℕ) (x : ℕ → Fin 4 → ℝ × ℝ) (k : ℕ) :
    monL (monFunnelCirc m) x k 2 = max (x k 2).1 (x k 3).1 := by
  unfold monL
  rw [(funCirc_ival m (x k)).2.2]

theorem funU_two (m : ℕ) (x : ℕ → Fin 4 → ℝ × ℝ) (k : ℕ) :
    monU (monFunnelCirc m) x k 2 = max (x k 2).2 (x k 3).2 := by
  unfold monU
  rw [(funCirc_ival m (x k)).2.2]

theorem funMu_zero (g : ℝ) : funMu g 0 = 4 / 5 := by simp [funMu]

theorem funMu_one (g : ℝ) : funMu g 1 = 4 / 5 - g := by simp [funMu]

theorem funMu_two (g : ℝ) : funMu g 2 = 3 / 20 := by simp [funMu]

theorem funMu_three (g : ℝ) : funMu g 3 = 1 / 5 := by simp [funMu]

/-- The upper endpoint of the direct action never drops below `4/5`. -/
theorem funU_zero_ge (m : ℕ) (hg0 : 0 ≤ g) (hg : g ≤ 1 / 4) (sel : ℕ → Fin 3)
    (sub : ℕ → Fin 2) (k : ℕ) :
    4 / 5 ≤ monU (monFunnelCirc m) (funBox δ g sel sub) k 0 := by
  rw [funU_zero]
  have := funTab_hi_ge (δ := δ) hg0 (by linarith) sel sub (3 + k) 0
  rw [funMu_zero] at this
  exact this

/-- The lower endpoints of the near rival and of the funnel action never exceed
`4/5 - g`. -/
theorem funL_rival_le (m : ℕ) (hg0 : 0 ≤ g) (hg : g ≤ 1 / 4) (sel : ℕ → Fin 3)
    (sub : ℕ → Fin 2) (k : ℕ) :
    ∀ a : Fin 3, a ≠ 0 → monL (monFunnelCirc m) (funBox δ g sel sub) k a ≤ 4 / 5 - g := by
  have h4 : g ≤ 4 / 5 := by linarith
  refine fu_fin3 _ (fun h => absurd rfl h) (fun _ => ?_) (fun _ => ?_)
  · rw [funL_one]
    have := funTab_lo_le (δ := δ) hg0 h4 sel sub (3 + k) 1
    rw [funMu_one] at this
    exact this
  · rw [funL_two]
    have h2 := funTab_lo_le (δ := δ) hg0 h4 sel sub (3 + k) 2
    have h3 := funTab_lo_le (δ := δ) hg0 h4 sel sub (3 + k) 3
    rw [funMu_two] at h2
    rw [funMu_three] at h3
    exact max_le (by unfold funBox; linarith) (by unfold funBox; linarith)

/-! ### Existence of recursive funnel searches -/

/-- Recursive funnel searches exist for every `g`: the model is not vacuous. -/
theorem exists_funnelSearch (g : ℝ) : ∃ sel sub, FunnelSearch g sel sub := by
  obtain ⟨sub, hsub⟩ := exists_uctRun (ι := Fin 2) 1
    (fun sub j e => (∑ i ∈ (range j).filter (fun i => sub i = e), funMu g (funExit (sub i)))
      / uctCount sub j e)
    (by
      intro sub sub' t hss
      funext e
      have hf : (range t).filter (fun i => sub i = e) = (range t).filter (fun i => sub' i = e) :=
        Finset.filter_congr (fun s hs => by rw [hss s (mem_range.mp hs)])
      have hc : uctCount sub t e = uctCount sub' t e := by
        unfold uctCount
        rw [hf]
      show (∑ i ∈ (range t).filter (fun i => sub i = e), funMu g (funExit (sub i)))
          / (uctCount sub t e : ℝ)
        = (∑ i ∈ (range t).filter (fun i => sub' i = e), funMu g (funExit (sub' i)))
          / (uctCount sub' t e : ℝ)
      rw [hc, hf]
      congr 1
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [hss s (mem_range.mp (Finset.mem_filter.mp hs).1)])
  obtain ⟨sel, hsel⟩ := exists_uctRun (ι := Fin 3) 1
    (fun sel t a => (∑ s ∈ (range t).filter (fun s => sel s = a), funMu g (funTerm sel sub s))
      / uctCount sel t a)
    (by
      intro sel sel' t hss
      funext a
      have hf : (range t).filter (fun s => sel s = a) = (range t).filter (fun s => sel' s = a) :=
        Finset.filter_congr (fun s hs => by rw [hss s (mem_range.mp hs)])
      have hc : uctCount sel t a = uctCount sel' t a := by
        unfold uctCount
        rw [hf]
      show (∑ s ∈ (range t).filter (fun s => sel s = a), funMu g (funTerm sel sub s))
          / (uctCount sel t a : ℝ)
        = (∑ s ∈ (range t).filter (fun s => sel' s = a), funMu g (funTerm sel' sub s))
          / (uctCount sel' t a : ℝ)
      rw [hc, hf]
      congr 1
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hs' : s < t := mem_range.mp (Finset.mem_filter.mp hs).1
      have hcnt : uctCount sel s 2 = uctCount sel' s 2 := by
        unfold uctCount
        congr 1
        exact Finset.filter_congr (fun u hu => by rw [hss u (lt_trans (mem_range.mp hu) hs')])
      unfold funTerm
      rw [hss s hs', hcnt])
  exact ⟨sel, sub, hsel, hsub⟩

/-- The terminal of a rollout is the one reached by a walk through the funnel DAG that
takes the split arm chosen by `sub` and any path inside the fan. -/
theorem funTerm_walk (m : ℕ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (s : ℕ) (rule : ℕ → Bool)
    (hrule : rule 0 = decide (sub (uctCount sel s 2) = 0)) :
    ((monFunnelCirc m (sel s)).monWalk rule 0).1 = funTerm sel sub s := by
  unfold funTerm
  by_cases h2 : sel s = 2
  · rw [ite_eq_left h2, h2, monFunnelCirc_two]
    by_cases he : sub (uctCount sel s 2) = 0
    · have hr : rule 0 = true := by rw [hrule]; exact decide_eq_true he
      simp only [MaxCirc.monWalk, hr, Bool.cond_true]
      rw [MaxCirc.monWalk_fst_of_onlyTerm rule (monFunnelFan m 2) 1 (monFanZ_onlyTerm _ _ _),
        he]
      rfl
    · have hr : rule 0 = false := by rw [hrule]; exact decide_eq_false he
      simp only [MaxCirc.monWalk, hr, Bool.cond_false]
      rw [MaxCirc.monWalk_fst_of_onlyTerm rule (monFunnelFan m 3) 1 (monFanZ_onlyTerm _ _ _)]
      unfold funExit
      rw [ite_eq_right he]
  · rw [ite_eq_right h2]
    have e : monFunnelCirc m (sel s) = .term (Fin.castSucc (sel s)) := by
      simp [monFunnelCirc, h2]
    rw [e]
    rfl

/-! ### Steps 1-2: fairness and constant-time counts -/

/-- **Window condition, explicit.**  For `t ≥ (6K + 2)²`,
`K (log (1 + t) + 1) < t - ⌊t/2⌋`. -/
theorem fu_window {K : ℝ} (hK : 0 ≤ K) {t : ℕ} (ht : (6 * K + 2) ^ 2 ≤ (t : ℝ)) :
    K * (Real.log (1 + t) + 1) < (t : ℝ) - (t / 2 : ℕ) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (1 + (t : ℝ)) := ⟨_, rfl⟩
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hss : s * s = 1 + (t : ℝ) := by
    rw [hs]
    exact Real.mul_self_sqrt (by linarith)
  have hs6 : 6 * K + 2 ≤ s := by
    have h1 : Real.sqrt ((6 * K + 2) ^ 2) ≤ Real.sqrt (1 + (t : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_sq (by linarith)] at h1
    rw [hs]
    exact h1
  have hs0 : 0 < s := by linarith
  have hlog : Real.log (1 + (t : ℝ)) ≤ 2 * (s - 1) := by
    rw [← hss, Real.log_mul hs0.ne' hs0.ne']
    have := Real.log_le_sub_one_of_pos hs0
    linarith
  have hhalf : ((t / 2 : ℕ) : ℝ) ≤ (t : ℝ) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := t) (n := 2)
    simpa using this
  have h1 : K * (Real.log (1 + (t : ℝ)) + 1) ≤ K * (2 * s) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  nlinarith [mul_le_mul_of_nonneg_right hs6 hs0.le, mul_nonneg hK hs0.le]

theorem fu_log_ge {c : ℝ} {t : ℕ} (h : 2 * ⌈Real.exp c⌉₊ ≤ t) :
    c ≤ Real.log (1 + ((t / 2 : ℕ) : ℝ)) := by
  have h1 : ⌈Real.exp c⌉₊ ≤ t / 2 := by omega
  have h2 : Real.exp c ≤ ((t / 2 : ℕ) : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

theorem FunnelSearch.Q_bounds (h : FunnelSearch g sel sub) (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5)
    (t : ℕ) : ∀ i : Fin 3, 0 ≤ funQ g sel sub t i ∧ funQ g sel sub t i ≤ 4 / 5 := by
  have hR := h.funnelRoot
  refine fu_fin3 _ ?_ ?_ ?_
  · rw [hR.qb]
    norm_num
  · rw [hR.qa]
    constructor <;> linarith
  · exact ⟨hR.qC0 t, by linarith [hR.qC1 t]⟩

/-- **Step 1 at the root.**  After `t ≥ 400` rollouts every root action has been selected
more than `(1/4) log (1 + ⌊t/2⌋)` times. -/
theorem FunnelSearch.root_fair (h : FunnelSearch g sel sub) (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5)
    {t : ℕ} (ht : 400 ≤ t) (a : Fin 3) :
    Real.log (1 + ((t / 2 : ℕ) : ℝ)) < 4 * uctCount sel t a := by
  have hR := h.funnelRoot
  have hw := fu_window (K := 3) (by norm_num) (t := t) (by
    norm_num
    exact_mod_cast ht)
  have := hR.uct.fairness one_pos (fun t i => (h.Q_bounds hg0 hg t i).1)
    (fun t i => ((h.Q_bounds hg0 hg t i).2).trans (by norm_num)) (t := t)
    (by rw [Fintype.card_fin]; omega)
    (by rw [Fintype.card_fin, one_pow, one_mul]; exact_mod_cast hw) a
  rwa [one_pow, one_mul] at this

/-- **Step 1 at the split.**  After `j ≥ 196` visits of the split each of its arms has been
taken more than `(1/4) log (1 + ⌊j/2⌋)` times. -/
theorem FunnelSearch.split_fair (h : FunnelSearch g sel sub) {j : ℕ} (hj : 196 ≤ j)
    (e : Fin 2) : Real.log (1 + ((j / 2 : ℕ) : ℝ)) < 4 * uctCount sub j e := by
  have hw := fu_window (K := 2) (by norm_num) (t := j) (by
    norm_num
    exact_mod_cast hj)
  have := h.split.fairness one_pos (fun j e => (h.split_bounds j e).1)
    (fun j e => (h.split_bounds j e).2) (t := j) (by rw [Fintype.card_fin]; omega)
    (by rw [Fintype.card_fin, one_pow, one_mul]; exact_mod_cast hw) e
  rwa [one_pow, one_mul] at this

/-- Number of visits of the split after which both exits have `funK0 δ` observations. -/
def funJ (δ : ℝ) : ℕ := max 196 (2 * ⌈Real.exp (4 * (funK0 δ : ℝ))⌉₊)

/-- **The constant cutoff `t₀`** of Step 2: it depends on `δ` only, not on the width `m` of
the funnel nor on the gap `g`. -/
def funT0 (δ : ℝ) : ℕ := max 400 (2 * ⌈Real.exp (4 * (funJ δ : ℝ))⌉₊)

theorem funT0_ge (δ : ℝ) : 400 ≤ funT0 δ := le_max_left _ _

/-- **Step 2: counts at the constant cutoff.**  After `t ≥ t₀` rollouts the direct action
and both exits of the funnel have at least `funK0 δ` observations, uniformly in `m` and
`g`. -/
theorem funnel_counts_const (h : FunnelSearch g sel sub) (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5)
    {t : ℕ} (ht : funT0 δ ≤ t) :
    funK0 δ ≤ funCnt sel sub t 0 ∧ funK0 δ ≤ funCnt sel sub t 2 ∧
      funK0 δ ≤ funCnt sel sub t 3 := by
  have ht400 : 400 ≤ t := le_trans (funT0_ge δ) ht
  have hT2 : 2 * ⌈Real.exp (4 * (funJ δ : ℝ))⌉₊ ≤ funT0 δ := le_max_right _ _
  have hJ2 : 2 * ⌈Real.exp (4 * (funK0 δ : ℝ))⌉₊ ≤ funJ δ := le_max_right _ _
  have hJ196 : 196 ≤ funJ δ := le_max_left _ _
  have hlog : 4 * (funJ δ : ℝ) ≤ Real.log (1 + ((t / 2 : ℕ) : ℝ)) :=
    fu_log_ge (le_trans hT2 ht)
  have hroot : ∀ a, funJ δ < uctCount sel t a := by
    intro a
    have h1 := h.root_fair hg0 hg ht400 a
    have h2 : (funJ δ : ℝ) < uctCount sel t a := by linarith
    exact_mod_cast h2
  have hKJ : funK0 δ ≤ funJ δ := by
    have h1 : (funK0 δ : ℝ) ≤ Real.exp (4 * (funK0 δ : ℝ)) := by
      have h3 := Real.add_one_le_exp (4 * (funK0 δ : ℝ))
      have h4 : (0 : ℝ) ≤ funK0 δ := Nat.cast_nonneg _
      linarith
    have h2 : funK0 δ ≤ ⌈Real.exp (4 * (funK0 δ : ℝ))⌉₊ := by
      exact_mod_cast le_trans h1 (Nat.le_ceil _)
    omega
  have hexit : ∀ e : Fin 2, funK0 δ ≤ funCnt sel sub t (funExit e) := by
    intro e
    rw [funCnt_exit]
    have hj := hroot 2
    have hf := h.split_fair (j := uctCount sel t 2) (by omega) e
    have hl : 4 * (funK0 δ : ℝ) ≤ Real.log (1 + ((uctCount sel t 2 / 2 : ℕ) : ℝ)) :=
      fu_log_ge (le_trans hJ2 hj.le)
    have h2 : (funK0 δ : ℝ) < uctCount sub (uctCount sel t 2) e := by linarith
    exact_mod_cast h2.le
  refine ⟨?_, hexit 0, hexit 1⟩
  rw [funCnt_zero]
  exact hKJ.trans (hroot 0).le

/-- **Step 2: intervals at the constant cutoff.**  After `t ≥ t₀` rollouts the lower
endpoint of the direct action is at least `11/20` and the upper endpoints of both exits are
at most `9/20`. -/
theorem funnel_box_const (h : FunnelSearch g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5) {t : ℕ} (ht : funT0 δ ≤ t) :
    11 / 20 ≤ (funTab δ g sel sub t 0).1 ∧ (funTab δ g sel sub t 2).2 ≤ 9 / 20 ∧
      (funTab δ g sel sub t 3).2 ≤ 9 / 20 := by
  obtain ⟨c0, c2, c3⟩ := funnel_counts_const (δ := δ) h hg0 hg ht
  have hK := funK0_pos δ
  have r0 := funRad_le_quarter hδ0 hδ1 c0
  have r2 := funRad_le_quarter hδ0 hδ1 c2
  have r3 := funRad_le_quarter hδ0 hδ1 c3
  rw [funTab_of_pos sel sub (hK.trans c0), funTab_of_pos sel sub (hK.trans c2),
    funTab_of_pos sel sub (hK.trans c3), funMu_zero, funMu_two, funMu_three]
  refine ⟨le_max_of_le_right (by linarith), (min_le_right _ _).trans (by linarith),
    (min_le_right _ _).trans (by linarith)⟩

/-- The direct action is never retired by the selective monitor. -/
theorem funnel_b_active (m : ℕ) (hg0 : 0 < g) (hg : g ≤ 1 / 4) (sel : ℕ → Fin 3)
    (sub : ℕ → Fin 2) :
    ∀ k, (0 : Fin 3) ∈ (monRun true (monFunnelCirc m) (funBox δ g sel sub) k).act
  | 0 => Finset.mem_univ _
  | k + 1 => by
      rw [mem_monRun_act_succ]
      refine ⟨funnel_b_active m hg0 hg sel sub k, ?_⟩
      rintro ⟨a, -, hne, hlt⟩
      have h1 := funU_zero_ge (δ := δ) m hg0.le hg sel sub k
      have h2 := funL_rival_le (δ := δ) m hg0.le hg sel sub k a hne
      linarith

/-- **Step 2: constant-time retirement of the dominated funnel.**  The selective monitor
retires the funnel action at the step `t₀ - 3` at the latest, where `t₀ = funT0 δ` does not
depend on the width `m` nor on the gap `g`: the funnel action is inactive at every later
step. -/
theorem funnel_retired (m : ℕ) (h : FunnelSearch g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg0 : 0 < g) (hg : g ≤ 1 / 4) :
    ∀ k, funT0 δ - 3 < k →
      (2 : Fin 3) ∉ (monRun true (monFunnelCirc m) (funBox δ g sel sub) k).act := by
  have hT := funT0_ge δ
  have hstep : (2 : Fin 3) ∉
      (monRun true (monFunnelCirc m) (funBox δ g sel sub) (funT0 δ - 3 + 1)).act := by
    rw [mem_monRun_act_succ]
    rintro ⟨-, hno⟩
    apply hno
    refine ⟨0, funnel_b_active m hg0 hg sel sub _, by decide, ?_⟩
    obtain ⟨b0, b2, b3⟩ := funnel_box_const (δ := δ) h hδ0 hδ1 hg0.le (by linarith)
      (t := 3 + (funT0 δ - 3)) (by omega)
    rw [funU_two, funL_zero]
    have hmax : max (funBox δ g sel sub (funT0 δ - 3) 2).2 (funBox δ g sel sub (funT0 δ - 3) 3).2
        ≤ 9 / 20 := max_le b2 b3
    have hb0 : 11 / 20 ≤ (funBox δ g sel sub (funT0 δ - 3) 0).1 := b0
    linarith
  intro k hk
  induction k, (show funT0 δ - 3 + 1 ≤ k from hk) using Nat.le_induction with
  | base => exact hstep
  | succ k _ ih => exact fun hmem => ih (by omega) (monRun_act_anti _ _ k hmem)

/-! ### The stopping test on the funnel -/

/-- The stopping test at step `k` with leader `a` and `ε = g/2`, from the exact
root-action intervals (the output of both monitors, `monRun_outputs`). -/
def funStops (m : ℕ) (δ g : ℝ) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (k : ℕ) (a : Fin 3) :
    Prop :=
  MarginalStops univ (monL (monFunnelCirc m) (funBox δ g sel sub) k)
    (monU (monFunnelCirc m) (funBox δ g sel sub) k) (g / 2) a

/-- Only the direct action can be certified. -/
theorem funStops_leader {m : ℕ} (hg0 : 0 < g) (hg : g ≤ 1 / 4) {k : ℕ} {a : Fin 3}
    (hs : funStops m δ g sel sub k a) : a = 0 := by
  by_contra ha
  have h1 := hs.2 0 (mem_univ _) (Ne.symm ha)
  have h2 := funU_zero_ge (δ := δ) m hg0.le hg sel sub k
  have h3 := funL_rival_le (δ := δ) m hg0.le hg sel sub k a ha
  linarith

/-- **Sufficient condition for stopping.**  If the direct action has radius at most `g/2`,
the near rival radius at most `g`, and both exits have upper endpoint at most `9/20`, the
stopping test passes with the direct action as leader. -/
theorem funStops_of_radii {m : ℕ} (hg0 : 0 < g) (hg : g ≤ 1 / 4) {k : ℕ}
    (hb1 : 1 ≤ funCnt sel sub (3 + k) 0)
    (hb : funRad δ (funCnt sel sub (3 + k) 0) ≤ g / 2)
    (ha1 : 1 ≤ funCnt sel sub (3 + k) 1)
    (ha : funRad δ (funCnt sel sub (3 + k) 1) ≤ g)
    (h2 : (funTab δ g sel sub (3 + k) 2).2 ≤ 9 / 20)
    (h3 : (funTab δ g sel sub (3 + k) 3).2 ≤ 9 / 20) :
    funStops m δ g sel sub k 0 := by
  have hL0 : 4 / 5 - g / 2 ≤ monL (monFunnelCirc m) (funBox δ g sel sub) k 0 := by
    rw [funL_zero]
    show 4 / 5 - g / 2 ≤ (funTab δ g sel sub (3 + k) 0).1
    rw [funTab_of_pos sel sub hb1, funMu_zero]
    exact le_max_of_le_right (by linarith)
  have hrest := funL_rival_le (δ := δ) m hg0.le hg sel sub k
  refine ⟨⟨mem_univ _, fun b _ => ?_, fun b _ _ => Fin.zero_le b⟩, ?_⟩
  · by_cases hb0 : b = 0
    · rw [hb0]
    · linarith [hrest b hb0]
  · intro b _
    revert b
    refine fu_fin3 _ (fun _ h => absurd rfl h) (fun _ _ => ?_) (fun _ _ => ?_)
    · rw [funU_one]
      have hU : (funBox δ g sel sub k 1).2 ≤ 4 / 5 := by
        show (funTab δ g sel sub (3 + k) 1).2 ≤ 4 / 5
        rw [funTab_of_pos sel sub ha1, funMu_one]
        exact (min_le_right _ _).trans (by linarith)
      linarith
    · rw [funU_two]
      have hU : max (funBox δ g sel sub k 2).2 (funBox δ g sel sub k 3).2 ≤ 9 / 20 :=
        max_le h2 h3
      linarith

/-- **Step 3: `τ = Ω(m^{1/8})`.**  With `g = (1/4) m^{-1/16}`, a successful stopping test
after `3 + k` rollouts forces `3 + k > (64/9) m^{1/8}`. -/
theorem funStops_horizon (h : FunnelSearch g sel sub) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) (hgdef : g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ))) (hg0 : 0 < g)
    (hg : g ≤ 1 / 4) {k : ℕ} (hs : funStops m δ g sel sub k 0) :
    64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < ((3 + k : ℕ) : ℝ) := by
  have hnb1 : 1 ≤ uctCount sel (3 + k) 0 :=
    h.root.one_le 0 (by rw [Fintype.card_fin]; omega)
  have hnbτ : uctCount sel (3 + k) 0 ≤ 3 + k := uctCount_le_time sel (3 + k) 0
  have hU : 4 / 5 - g ≤ (funBox δ g sel sub k 1).2 := by
    have := funTab_hi_ge (δ := δ) hg0.le (by linarith) sel sub (3 + k) 1
    rw [funMu_one] at this
    exact this
  have hstop := hs.2 1 (mem_univ _) (by decide)
  rw [funU_one, funL_zero] at hstop
  have hL : (funBox δ g sel sub k 0).1
      = max 0 (4 / 5 - hoeffdingWidth 4 δ (uctCount sel (3 + k) 0 : ℕ) / 2) := by
    show (funTab δ g sel sub (3 + k) 0).1 = _
    rw [funTab_of_pos sel sub (by rw [funCnt_zero]; exact hnb1), funMu_zero, funCnt_zero]
    rfl
  rw [hL] at hstop
  have hU' : 4 / 5 - 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) ≤ (funBox δ g sel sub k 1).2 := by
    rw [← hgdef]
    exact hU
  have hstop' : (funBox δ g sel sub k 1).2
      - max 0 (4 / 5 - hoeffdingWidth 4 δ (uctCount sel (3 + k) 0 : ℕ) / 2)
        ≤ 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) / 2 := by
    rw [← hgdef]
    exact hstop
  exact funnel_horizon_lower_m (M := 4) (by norm_num) hδ0 hδ1 (by exact_mod_cast hm) hnb1 hnbτ
    hU' hstop'

/-! ### Step 3: the stopping test passes after `m` rollouts -/

/-- Size bookkeeping for `m = a^16`, `a ≥ 2`. -/
theorem fu_scale {a : ℝ} (ha : 2 ≤ a) {m : ℕ} (hm : (m : ℝ) = a ^ 16) :
    Real.log (1 + (m : ℝ)) ≤ 16 * a ∧
      16 * Real.log a - Real.log 2 ≤ Real.log (1 + ((m / 2 : ℕ) : ℝ)) ∧
      Real.log (1 + ((m / 2 : ℕ) : ℝ)) ≤ 16 * a ∧ 8192 * a ^ 3 ≤ (m : ℝ) ∧
      16384 * a ^ 2 ≤ (m : ℝ) := by
  have ha0 : 0 < a := by linarith
  have hl2 := Real.log_two_lt_d9
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hm]
    exact one_le_pow₀ (by linarith)
  have hloga : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
  have h1 : Real.log (1 + (m : ℝ)) ≤ 16 * a := by
    have h2 : Real.log (1 + (m : ℝ)) ≤ Real.log (2 * a ^ 16) :=
      Real.log_le_log (by linarith) (by rw [← hm]; linarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
    push_cast at h2
    linarith
  have hc : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
    have : m ≤ 2 * (m / 2) + 1 := by omega
    exact_mod_cast this
  have hc0 : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcm : ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
  have h2 : 16 * Real.log a - Real.log 2 ≤ Real.log (1 + ((m / 2 : ℕ) : ℝ)) := by
    have h3 : Real.log (a ^ 16 / 2) ≤ Real.log (1 + ((m / 2 : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) (by rw [← hm]; linarith)
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h3
    push_cast at h3
    exact h3
  have h3 : Real.log (1 + ((m / 2 : ℕ) : ℝ)) ≤ 16 * a :=
    (Real.log_le_log (by linarith) (by linarith)).trans h1
  have h13 : (8192 : ℝ) ≤ a ^ 13 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ha 13
    norm_num at this
    exact this
  have h14 : (16384 : ℝ) ≤ a ^ 14 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ha 14
    norm_num at this
    exact this
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rw [hm, show a ^ 16 = a ^ 13 * a ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right h13 (by positivity)
  · rw [hm, show a ^ 16 = a ^ 14 * a ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right h14 (by positivity)

/-- **Radius of the near rival.**  With `g = 1/(4a)`: a count `N > 4 a² L`, where `L` is of
order `16 log a`, has radius at most `g`, as soon as `2 log a ≥ log (65536/δ) + 1`. -/
theorem fu_rival_radius (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {a L : ℝ} (ha : 2 ≤ a)
    (hLlo : 16 * Real.log a - Real.log 2 ≤ L) (hLhi : L ≤ 16 * a)
    (hD : Real.log (65536 / δ) + 1 ≤ 2 * Real.log a) {N : ℕ} (hN : 4 * a ^ 2 * L < N) :
    funRad δ N ≤ 1 / (4 * a) := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hloga : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) ha
  have hL10 : 10 ≤ L := by linarith
  have ha0 : 0 < a := by linarith
  have ha4 : 4 ≤ a ^ 2 := by nlinarith
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℝ, N0 = 4 * a ^ 2 * L := ⟨_, rfl⟩
  rw [← hN0] at hN
  have hN01 : 1 ≤ N0 := by
    rw [hN0]
    nlinarith
  have hanti := (fuWidth_strictAntiOn (M := 4) (by norm_num) hδ0 hδ1).antitoneOn
    (Set.mem_Ici.mpr hN01) (Set.mem_Ici.mpr (by linarith : (1 : ℝ) ≤ (N : ℝ))) hN.le
  have hlogL : Real.log L ≤ Real.log 16 + Real.log a := by
    rw [← Real.log_mul (by norm_num) ha0.ne']
    exact Real.log_le_log (by linarith) hLhi
  have hδne : δ ≠ 0 := hδ0.ne'
  have hLne : L ≠ 0 := by linarith
  have hsplit : Real.log (4 * 4 * N0 ^ 2 / δ)
      = Real.log (256 / δ) + 4 * Real.log a + 2 * Real.log L := by
    rw [hN0, show 4 * 4 * (4 * a ^ 2 * L) ^ 2 / δ = 256 / δ * a ^ 4 * L ^ 2 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h65 : Real.log (65536 / δ) = Real.log (256 / δ) + 2 * Real.log 16 := by
    rw [show (65536 : ℝ) / δ = 256 / δ * 16 ^ 2 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hkey : Real.log (4 * 4 * N0 ^ 2 / δ) ≤ L / 2 := by
    rw [hsplit]
    linarith
  have hsq : Real.sqrt (Real.log (4 * 4 * N0 ^ 2 / δ) / (2 * N0)) ≤ 1 / (4 * a) := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith)]
    have e : (1 / (4 * a)) ^ 2 * (2 * N0) = L / 2 := by
      rw [hN0]
      field_simp
      ring
    linarith
  unfold funRad
  unfold hoeffdingWidth at hanti ⊢
  linarith

/-- **Step 3: certification has occurred by `T = m`.**  There is a size threshold `a₀`
(depending on `δ` only) such that for `m = a^16` with `a ≥ a₀`, `m ≥ t₀`, and
`g = 1/(4a) = (1/4) m^{-1/16}`, the stopping test passes with the direct action as leader
after `m` rollouts of any recursive funnel search. -/
theorem funnel_stops_at_m (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ a0 : ℝ, 2 ≤ a0 ∧ ∀ (m : ℕ) (a : ℝ), a0 ≤ a → (m : ℝ) = a ^ 16 → funT0 δ ≤ m →
      ∀ (sel : ℕ → Fin 3) (sub : ℕ → Fin 2), FunnelSearch (1 / (4 * a)) sel sub →
        funStops m δ (1 / (4 * a)) sel sub (m - 3) 0 := by
  refine ⟨max 2 (max (Real.log (2048 / δ)) (Real.exp ((Real.log (65536 / δ) + 1) / 2))),
    le_max_left _ _, ?_⟩
  intro m a ha0 hm hT sel sub h
  have ha : 2 ≤ a := le_trans (le_max_left _ _) ha0
  have hD1 : Real.log (2048 / δ) ≤ a :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha0
  have hD2 : Real.exp ((Real.log (65536 / δ) + 1) / 2) ≤ a :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha0
  have hapos : 0 < a := by linarith
  have hane : a ≠ 0 := hapos.ne'
  have hδne : δ ≠ 0 := hδ0.ne'
  have hD : Real.log (65536 / δ) + 1 ≤ 2 * Real.log a := by
    have := (Real.le_log_iff_exp_le hapos).mpr hD2
    linarith
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = 1 / (4 * a) := ⟨_, rfl⟩
  rw [← hgdef] at h ⊢
  have hg0 : 0 < g := by
    rw [hgdef]
    positivity
  have hg8 : g ≤ 1 / 8 := by
    rw [hgdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hg2 : g ^ 2 = 1 / (16 * a ^ 2) := by
    rw [hgdef]
    field_simp
    ring
  obtain ⟨s1, s2, s3, s4, -⟩ := fu_scale ha hm
  have hT400 := funT0_ge δ
  have hm3 : 3 ≤ m := by omega
  have e : 3 + (m - 3) = m := by omega
  have hR := h.funnelRoot
  obtain ⟨c1, c2, -, c4⟩ := funnel_counts hR hg0 (by linarith) hm3
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = a ^ 3 := ⟨_, rfl⟩
  have ha2 : 4 ≤ a ^ 2 := by nlinarith
  have hP8 : 8 ≤ P := by
    rw [hP]
    nlinarith
  have hPa : 4 * a ≤ P := by
    rw [hP]
    nlinarith
  rw [← hP] at s4
  have hlogg : Real.log (1 + (m : ℝ)) / g ^ 2 ≤ 256 * P := by
    have e1 : Real.log (1 + (m : ℝ)) / g ^ 2 = 16 * a ^ 2 * Real.log (1 + (m : ℝ)) := by
      rw [hg2]
      field_simp
    rw [e1]
    calc 16 * a ^ 2 * Real.log (1 + (m : ℝ)) ≤ 16 * a ^ 2 * (16 * a) :=
          mul_le_mul_of_nonneg_left s1 (by positivity)
      _ = 256 * P := by rw [hP]; ring
  have hNa : (uctCount sel m 1 : ℝ) ≤ 1 + 256 * P := c2.trans (max_le (by linarith) (by linarith))
  have hNC : (uctCount sel m 2 : ℝ) ≤ 1 + 45 * a := by
    have h9 : Real.log (1 + (m : ℝ)) / (3 / 5) ^ 2 ≤ 45 * a := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    exact c1.trans (max_le (by linarith) (by linarith))
  have hsum : (uctCount sel m 0 : ℝ) + uctCount sel m 1 + uctCount sel m 2 = m := by
    have := uctCount_sum sel m
    rw [Fin.sum_univ_three] at this
    exact_mod_cast this
  have hNb : 7900 * P ≤ (uctCount sel m 0 : ℝ) := by linarith
  -- the direct action
  have hbrad : funRad δ (funCnt sel sub (3 + (m - 3)) 0) ≤ g / 2 := by
    rw [e, funCnt_zero]
    have hlog2 : Real.log (32 * 4 / (δ * g ^ 2)) ≤ 3 * a := by
      rw [hg2, show 32 * 4 / (δ * (1 / (16 * a ^ 2))) = 2048 / δ * a ^ 2 by
        field_simp
        ring, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have := Real.log_le_sub_one_of_pos hapos
      push_cast
      linarith
    have hx : 32 / g ^ 2 * Real.log (32 * 4 / (δ * g ^ 2)) ≤ (uctCount sel m 0 : ℝ) := by
      have e2 : 32 / g ^ 2 = 512 * a ^ 2 := by
        rw [hg2]
        field_simp
        ring
      rw [e2]
      calc 512 * a ^ 2 * Real.log (32 * 4 / (δ * g ^ 2)) ≤ 512 * a ^ 2 * (3 * a) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = 1536 * P := by rw [hP]; ring
        _ ≤ _ := by linarith
    have := width_inversion (M := 4) (by norm_num) hδ0 hδ1 hg0 (by linarith) hx
    unfold funRad
    linarith
  -- the near rival
  have hwin : 3 * (Real.log (1 + (m : ℝ)) / g ^ 2 + 1) < (m : ℝ) - (m / 2 : ℕ) := by
    have hhalf : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := m) (n := 2)
      simpa using this
    linarith
  have hriv := c4 (by omega) hwin
  have hN1 : 4 * a ^ 2 * Real.log (1 + ((m / 2 : ℕ) : ℝ)) < (uctCount sel m 1 : ℝ) := by
    rw [hg2] at hriv
    have e3 : 4 * (1 / (16 * a ^ 2)) * (uctCount sel m 1 : ℝ)
        = (uctCount sel m 1 : ℝ) / (4 * a ^ 2) := by
      field_simp
      ring
    rw [e3, lt_div_iff₀ (by positivity)] at hriv
    linarith
  have harad : funRad δ (funCnt sel sub (3 + (m - 3)) 1) ≤ g := by
    rw [e, funCnt_one, hgdef]
    exact fu_rival_radius hδ0 hδ1.le ha s2 s3 hD hN1
  -- the exits
  obtain ⟨-, b2, b3⟩ := funnel_box_const (δ := δ) h hδ0 hδ1 hg0.le (by linarith) hT
  have hb1 : 1 ≤ funCnt sel sub (3 + (m - 3)) 0 := by
    rw [e, funCnt_zero]
    exact h.root.one_le 0 (by rw [Fintype.card_fin]; exact hm3)
  have ha1 : 1 ≤ funCnt sel sub (3 + (m - 3)) 1 := by
    rw [e, funCnt_one]
    exact h.root.one_le 1 (by rw [Fintype.card_fin]; exact hm3)
  exact funStops_of_radii hg0 (by linarith) hb1 hbrad ha1 harad (by rw [e]; exact b2)
    (by rw [e]; exact b3)

/-! ### Step 4: exit-changing revisits -/

/-- After the cutoff, an observation of a terminal with mean at most `1/5` strictly lowers
its upper endpoint, so its stored interval changes. -/
theorem funTab_change_at (hδ0 : 0 < δ) (hδ1 : δ < 1) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    {t : ℕ} {z : Fin 4} (hμ : funMu g z ≤ 1 / 5) (hc : funK0 δ ≤ funCnt sel sub t z)
    (hsucc : funCnt sel sub (t + 1) z = funCnt sel sub t z + 1) :
    funTab δ g sel sub (t + 1) z ≠ funTab δ g sel sub t z := by
  intro heq
  have hK := funK0_pos δ
  have h1 := congrArg Prod.snd heq
  rw [funTab_of_pos sel sub (by omega), funTab_of_pos sel sub (hK.trans hc)] at h1
  have h2 : min 1 (funMu g z + funRad δ (funCnt sel sub (t + 1) z))
      = min 1 (funMu g z + funRad δ (funCnt sel sub t z)) := h1
  have r1 := funRad_le_quarter hδ0 hδ1 hc
  have r2 := funRad_le_quarter hδ0 hδ1 (n := funCnt sel sub (t + 1) z) (by omega)
  rw [min_eq_right (by linarith), min_eq_right (by linarith), hsucc] at h2
  have := funRad_strict hδ0 hδ1.le (j := funCnt sel sub t z) (k := funCnt sel sub t z + 1)
    (hK.trans hc) (Nat.lt_succ_self _)
  linarith

/-- **Step 4: every revisit after the cutoff changes an exit interval.**  A rollout
through the funnel at a time `t ≥ t₀` strictly changes the interval of the exit it
reaches. -/
theorem funTab_change (h : FunnelSearch g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg0 : 0 ≤ g)
    (hg : g ≤ 4 / 5) {t : ℕ} (ht : funT0 δ ≤ t) (h2 : sel t = 2) :
    funTab δ g sel sub (t + 1) 2 ≠ funTab δ g sel sub t 2 ∨
      funTab δ g sel sub (t + 1) 3 ≠ funTab δ g sel sub t 3 := by
  obtain ⟨-, c2, c3⟩ := funnel_counts_const (δ := δ) h hg0 hg ht
  have hterm : funTerm sel sub t = funExit (sub (uctCount sel t 2)) := by
    unfold funTerm
    rw [ite_eq_left h2]
  by_cases he : sub (uctCount sel t 2) = 0
  · have hz : funTerm sel sub t = 2 := by
      rw [hterm, he]
      rfl
    refine Or.inl (funTab_change_at hδ0 hδ1 sel sub (by rw [funMu_two]; norm_num) c2 ?_)
    unfold funCnt
    rw [uctCount_succ, ite_eq_left hz]
  · have hz : funTerm sel sub t = 3 := by
      rw [hterm]
      unfold funExit
      rw [ite_eq_right he]
    refine Or.inr (funTab_change_at hδ0 hδ1 sel sub (by rw [funMu_three]) c3 ?_)
    unfold funCnt
    rw [uctCount_succ, ite_eq_left hz]

open Classical in
/-- **Step 4: number of exit-changing updates.**  Among the first `K ≥ t₀ - 3` monitor
steps, at least `N_C(3 + K) - N_C(t₀)` change the interval of an exit: every rollout through
the funnel after the cutoff does. -/
theorem funnel_changes_ge (h : FunnelSearch g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg0 : 0 ≤ g) (hg : g ≤ 4 / 5) :
    ∀ K, funT0 δ - 3 ≤ K →
      uctCount sel (3 + K) 2 ≤ ((range K).filter (fun k =>
          funBox δ g sel sub (k + 1) 2 ≠ funBox δ g sel sub k 2 ∨
            funBox δ g sel sub (k + 1) 3 ≠ funBox δ g sel sub k 3)).card
        + uctCount sel (funT0 δ) 2 := by
  have hT := funT0_ge δ
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    have e : 3 + (funT0 δ - 3) = funT0 δ := by omega
    rw [e]
    exact Nat.le_add_left _ _
  | succ K hK ih =>
    have e : 3 + (K + 1) = 3 + K + 1 := rfl
    rw [e, uctCount_succ, Finset.range_add_one, Finset.filter_insert]
    by_cases h2 : sel (3 + K) = 2
    · have hch : funBox δ g sel sub (K + 1) 2 ≠ funBox δ g sel sub K 2 ∨
          funBox δ g sel sub (K + 1) 3 ≠ funBox δ g sel sub K 3 :=
        funTab_change h hδ0 hδ1 hg0 hg (t := 3 + K) (by omega) h2
      rw [ite_eq_left h2, ite_eq_left hch, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [ite_eq_right h2, add_zero]
      refine ih.trans (Nat.add_le_add_right ?_ _)
      split_ifs
      · exact Finset.card_le_card (Finset.subset_insert _ _)
      · exact le_rfl

/-! ### Total work and the assembled separation -/

theorem monFanZ_height {Z : Type*} (z : Z) : ∀ d m, (monFanZ z d m).monHeight ≤ d + 1
  | 0, _ => le_rfl
  | d + 1, m => by
      unfold monFanZ
      split_ifs
      · show 0 + 1 ≤ d + 1 + 1
        omega
      · have h1 := monFanZ_height z d ((m + 1) / 2)
        have h2 := monFanZ_height z d (m / 2)
        show max _ _ + 1 ≤ d + 1 + 1
        omega

/-- Sampler work of rollout `t`: five root- and terminal-local steps and two steps (descent
and backup) per traversed edge; a rollout through the funnel traverses the split edge and a
path inside the chosen fan under the arbitrary rule `rule t`. -/
def funRollout (m : ℕ) (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) (t : ℕ) : ℕ :=
  5 + 2 * (if sel t = 2 then
    1 + ((monFunnelFan m (funExit (sub (uctCount sel t 2)))).monWalk (rule t) 1).2 else 0)

theorem funRollout_le (m : ℕ) (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2)
    (t : ℕ) :
    funRollout m rule sel sub t ≤ 5 + (if sel t = 2 then 2 * (Nat.clog 2 m + 2) else 0) := by
  unfold funRollout
  split_ifs
  · have hw := (MaxCirc.monWalk_snd_le (rule t)
      (monFunnelFan m (funExit (sub (uctCount sel t 2)))) 1).trans (monFanZ_height _ _ _)
    omega
  · omega

theorem funRollout_sum_le (m : ℕ) (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2) :
    ∀ τ, ∑ t ∈ range τ, funRollout m rule sel sub t
      ≤ 5 * τ + 2 * (Nat.clog 2 m + 2) * uctCount sel τ 2
  | 0 => by simp
  | τ + 1 => by
      have ih := funRollout_sum_le m rule sel sub τ
      have hs := funRollout_le m rule sel sub τ
      rw [Finset.sum_range_succ, uctCount_succ]
      by_cases h2 : sel τ = 2
      · rw [ite_eq_left h2] at hs ⊢
        have e : 2 * (Nat.clog 2 m + 2) * (uctCount sel τ 2 + 1)
            = 2 * (Nat.clog 2 m + 2) * uctCount sel τ 2 + 2 * (Nat.clog 2 m + 2) := by ring
        rw [e]
        omega
      · rw [ite_eq_right h2] at hs ⊢
        have e : uctCount sel τ 2 + 0 = uctCount sel τ 2 := rfl
        rw [e]
        omega

/-- Total work of a run of `τ` rollouts with the selective (`s = true`) or the eager
(`s = false`) monitor: the sampler's traversals and the monitor work (build, queries,
retirement, waves, disposal). -/
def funWork (s : Bool) (m : ℕ) (δ g : ℝ) (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3)
    (sub : ℕ → Fin 2) (τ : ℕ) : ℕ :=
  ∑ t ∈ range τ, funRollout m rule sel sub t
    + monWork s (monFunnelCirc m) (funBox δ g sel sub) (g / 2) (τ - 3)

/-- **Step 4, selective side.**  If the stopping count `τ` is at most `m = a^16` (`a ≥ 8`,
`g ≤ 1/4`), the total work with the selective monitor is at most `(12 (t₀ - 3) + 42) m`. -/
theorem funnel_selective_work (h : FunnelSearch g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg0 : 0 < g) (hg4 : g ≤ 1 / 4) {a : ℝ} (ha8 : 8 ≤ a) {m : ℕ} (ha16 : (m : ℝ) = a ^ 16)
    (rule : ℕ → ℕ → Bool) {τ : ℕ} (hτ3 : 3 ≤ τ) (hτm : τ ≤ m) :
    (funWork true m δ g rule sel sub τ : ℝ) ≤ (12 * ((funT0 δ - 3 : ℕ) : ℝ) + 42) * m := by
  have hapos : 0 < a := by linarith
  obtain ⟨s1, -, -, -, s5⟩ := fu_scale (by linarith : (2 : ℝ) ≤ a) ha16
  have hmR : (1 : ℝ) ≤ m := by
    rw [ha16]
    exact one_le_pow₀ (by linarith)
  have hm1 : 1 ≤ m := by exact_mod_cast hmR
  have hτR : (τ : ℝ) ≤ m := by exact_mod_cast hτm
  have hret := funnel_retired (δ := δ) m h hδ0 hδ1 hg0 hg4
  have hfw := (funnel_work hm1 (funBox δ g sel sub) (g / 2) (τ - 3)).2 (funT0 δ - 3) hret
  have hsamp := funRollout_sum_le m rule sel sub τ
  have hNC : (uctCount sel τ 2 : ℝ) ≤ 46 * a := by
    obtain ⟨c1, -, -, -⟩ := funnel_counts h.funnelRoot hg0 (by linarith) (t := τ) hτ3
    have hlog : Real.log (1 + (τ : ℝ)) ≤ 16 * a :=
      (Real.log_le_log (by positivity) (by linarith)).trans s1
    have h9 : Real.log (1 + (τ : ℝ)) / (3 / 5) ^ 2 ≤ 45 * a := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    exact c1.trans (max_le (by linarith) (by linarith))
  have hclog : ((Nat.clog 2 m : ℕ) : ℝ) + 2 ≤ 49 * a := by
    have h1 := monClog_le_log hm1
    have h2 : Real.log (2 * (m : ℝ)) = Real.log 2 + 16 * Real.log a := by
      rw [ha16, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have hl := Real.log_le_sub_one_of_pos hapos
    have hl2 := Real.log_two_lt_d9
    rw [h2] at h1
    linarith
  have hprod : 2 * (((Nat.clog 2 m : ℕ) : ℝ) + 2) * (uctCount sel τ 2 : ℝ) ≤ m := by
    have h1 : (((Nat.clog 2 m : ℕ) : ℝ) + 2) * (uctCount sel τ 2 : ℝ) ≤ 49 * a * (46 * a) :=
      mul_le_mul hclog hNC (Nat.cast_nonneg _) (by linarith)
    linarith [sq_nonneg a]
  have hK3 : ((τ - 3 : ℕ) : ℝ) ≤ τ := by exact_mod_cast Nat.sub_le τ 3
  have hW : (funWork true m δ g rule sel sub τ : ℝ)
      ≤ (5 * (τ : ℝ) + 2 * (((Nat.clog 2 m : ℕ) : ℝ) + 2) * (uctCount sel τ 2 : ℝ))
        + ((12 * ((funT0 δ - 3 : ℕ) : ℝ) + 12) * m + 16 * ((τ - 3 : ℕ) : ℝ) + 8) := by
    unfold funWork
    have := Nat.add_le_add hsamp hfw
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ ((funT0 δ - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Step 4, eager side.**  If the stopping count satisfies `τ > (64/9) a²` with
`m = a^16`, `a ≥ 8` and `log a ≥ 4 t₀`, the total work with the eager monitor is at least
`(1/64) m log m`: each of the `N_C(τ) - N_C(t₀) ≥ (log a)/4` revisits of the funnel after
the cutoff is delivered across at least `m` incidences. -/
theorem funnel_eager_work (h : FunnelSearch g sel sub) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg0 : 0 < g) (hg4 : g ≤ 1 / 4) {a : ℝ} (ha8 : 8 ≤ a) {m : ℕ} (ha16 : (m : ℝ) = a ^ 16)
    (rule : ℕ → ℕ → Bool) {τ : ℕ} (hτa : 64 / 9 * a ^ 2 < (τ : ℝ))
    (hloga : 4 * (funT0 δ : ℝ) ≤ Real.log a) :
    1 / 64 * (m : ℝ) * Real.log m ≤ funWork false m δ g rule sel sub τ := by
  have hapos : 0 < a := by linarith
  have hmR : (1 : ℝ) ≤ m := by
    rw [ha16]
    exact one_le_pow₀ (by linarith)
  have hm1 : 1 ≤ m := by exact_mod_cast hmR
  have hT400 := funT0_ge δ
  have hT0R : (0 : ℝ) ≤ funT0 δ := Nat.cast_nonneg _
  have hT0a : (funT0 δ : ℝ) ≤ a := by
    have h1 := Real.log_le_sub_one_of_pos hapos
    linarith
  have haa : a * 8 ≤ a * a := mul_le_mul_of_nonneg_left ha8 hapos.le
  have hT0τ : funT0 δ < τ := by
    have : (funT0 δ : ℝ) < τ := by linarith [sq a]
    exact_mod_cast this
  have hfair := h.root_fair hg0.le (by linarith) (t := τ) (hT400.trans hT0τ.le) 2
  have hc : (τ : ℝ) ≤ 2 * ((τ / 2 : ℕ) : ℝ) + 1 := by
    have : τ ≤ 2 * (τ / 2) + 1 := by omega
    exact_mod_cast this
  have hLτ : 2 * Real.log a ≤ Real.log (1 + ((τ / 2 : ℕ) : ℝ)) := by
    have h1 : Real.log (a ^ 2) ≤ Real.log (1 + ((τ / 2 : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith [sq_nonneg a])
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  have hNT0 : (uctCount sel (funT0 δ) 2 : ℝ) ≤ funT0 δ := by
    exact_mod_cast uctCount_le_time sel (funT0 δ) 2
  have hlogm : Real.log m = 16 * Real.log a := by
    rw [ha16, Real.log_pow]
    push_cast
    ring
  have hdiff : Real.log a / 4 ≤ (uctCount sel τ 2 : ℝ) - uctCount sel (funT0 δ) 2 := by
    linarith
  have hch := funnel_changes_ge h hδ0 hδ1 hg0.le (by linarith) (τ - 3) (by omega)
  have e : 3 + (τ - 3) = τ := by omega
  rw [e] at hch
  have hmonoC : uctCount sel (funT0 δ) 2 ≤ uctCount sel τ 2 :=
    uctCount_mono sel 2 hT0τ.le
  have hfw := (funnel_work hm1 (funBox δ g sel sub) (g / 2) (τ - 3)).1
  have hnat : m * (uctCount sel τ 2 - uctCount sel (funT0 δ) 2)
      ≤ monWork false (monFunnelCirc m) (funBox δ g sel sub) (g / 2) (τ - 3) :=
    (Nat.mul_le_mul_left m (Nat.sub_le_iff_le_add.mpr hch)).trans hfw
  have hreal : (m : ℝ) * ((uctCount sel τ 2 : ℝ) - uctCount sel (funT0 δ) 2)
      ≤ (funWork false m δ g rule sel sub τ : ℝ) := by
    have h1 : ((m * (uctCount sel τ 2 - uctCount sel (funT0 δ) 2) : ℕ) : ℝ)
        ≤ (funWork false m δ g rule sel sub τ : ℝ) := by
      unfold funWork
      exact_mod_cast hnat.trans (Nat.le_add_left _ _)
    rw [Nat.cast_mul, Nat.cast_sub hmonoC] at h1
    exact h1
  have hfin : (m : ℝ) * (Real.log a / 4)
      ≤ (m : ℝ) * ((uctCount sel τ 2 : ℝ) - uctCount sel (funT0 δ) 2) :=
    mul_le_mul_of_nonneg_left hdiff (by linarith)
  rw [hlogm]
  linarith

/-- **Theorem `thm:onpolicy-uct` / `thm:selective-separation`, local-UCT half.**  Fix
`δ ∈ (0, 1)`.  There are a size `m₀` and constants `c > 0`, `C` depending only on `δ` such
that for every `m ≥ m₀`, with `g = (1/4) m^{-1/16}` and `ε = g/2`, for every recursive UCT
search on the two-exit funnel of width `m` (every tie-breaking at the root and at the split,
every path rule inside the fans):

* the selective and the eager monitor expose the same output at every step;
* the selective monitor has retired the funnel action at every step after `t₀ - 3`, where
  `t₀ = funT0 δ` does not depend on `m`;
* the common first stopping count `τ` exists, the stopping set there is `{b}`, and
  `(64/9) m^{1/8} < τ ≤ m`;
* `W_selective ≤ C m`;
* `W_eager ≥ c m log m`.

The works `funWork` (sampler traversals plus monitor work) are computed by the cost model of
`MonitorWork.lean`.  No value fact, count bound or accounting inequality is assumed. -/
theorem onpolicy_uct_funnel (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (m0 : ℕ) (c C : ℝ), 0 < c ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g : ℝ, g = 1 / 4 * (m : ℝ) ^ (-(1 / 16 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (sub : ℕ → Fin 2), FunnelSearch g sel sub →
        (∀ k, (monQuery (g / 2) (funBox δ g sel sub k)
              (monRun true (monFunnelCirc m) (funBox δ g sel sub) k)).1
            = (monQuery (g / 2) (funBox δ g sel sub k)
              (monRun false (monFunnelCirc m) (funBox δ g sel sub) k)).1) ∧
        (∀ k, funT0 δ - 3 < k →
          (2 : Fin 3) ∉ (monRun true (monFunnelCirc m) (funBox δ g sel sub) k).act) ∧
        ∃ τ : ℕ, 3 ≤ τ ∧
          (∀ k, k < τ - 3 → (monQuery (g / 2) (funBox δ g sel sub k)
            (monRun false (monFunnelCirc m) (funBox δ g sel sub) k)).1.stops = ∅) ∧
          (monQuery (g / 2) (funBox δ g sel sub (τ - 3))
            (monRun false (monFunnelCirc m) (funBox δ g sel sub) (τ - 3))).1.stops = {0} ∧
          64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < τ ∧ τ ≤ m ∧
          (funWork true m δ g rule sel sub τ : ℝ) ≤ C * m ∧
          c * m * Real.log m ≤ funWork false m δ g rule sel sub τ := by
  classical
  obtain ⟨a0, ha02, Hstop⟩ := funnel_stops_at_m hδ0 hδ1
  obtain ⟨T0, hT0def⟩ : ∃ T0 : ℕ, T0 = funT0 δ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = max a0 (max 8 (Real.exp (4 * (T0 : ℝ)))) := ⟨_, rfl⟩
  have hAa0 : a0 ≤ A := by rw [hA]; exact le_max_left _ _
  have hA8 : 8 ≤ A := by rw [hA]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAe : Real.exp (4 * (T0 : ℝ)) ≤ A := by
    rw [hA]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨⌈A ^ 16⌉₊, 1 / 64, 12 * ((T0 - 3 : ℕ) : ℝ) + 42, by norm_num, ?_⟩
  intro m hm g hgdef rule sel sub h
  -- the scale `a = m^{1/16}`
  have hAm : A ^ 16 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hAm
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (m : ℝ) ^ (1 / 16 : ℝ) := ⟨_, rfl⟩
  have hAa : A ≤ a := by
    have h1 := Real.rpow_le_rpow (by positivity) hAm (by norm_num : (0 : ℝ) ≤ 1 / 16)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at h1
    norm_num at h1
    rw [ha]
    exact h1
  have ha16 : (m : ℝ) = a ^ 16 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
    norm_num
  have ha8 : 8 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hg' : g = 1 / (4 * a) := by
    rw [hgdef, Real.rpow_neg hmpos.le, ← ha]
    field_simp
  have hm8 : (m : ℝ) ^ (1 / 8 : ℝ) = a ^ 2 := by
    rw [ha, ← Real.rpow_two, ← Real.rpow_mul hmpos.le]
    norm_num
  have hg0 : 0 < g := by
    rw [hg']
    positivity
  have hg4 : g ≤ 1 / 4 := by
    rw [hg', div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨s1, -, -, -, s5⟩ := fu_scale (by linarith : (2 : ℝ) ≤ a) ha16
  have hT0R : (0 : ℝ) ≤ T0 := Nat.cast_nonneg _
  have hT0a : (T0 : ℝ) ≤ a := by
    have h1 := Real.add_one_le_exp (4 * (T0 : ℝ))
    linarith
  have hloga : 4 * (T0 : ℝ) ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le hapos]
    linarith
  have haa : a * 8 ≤ a * a := mul_le_mul_of_nonneg_left ha8 hapos.le
  have ham : a ≤ (m : ℝ) := by linarith [sq a]
  have hT0m : T0 ≤ m := by exact_mod_cast hT0a.trans ham
  have hT400 : 400 ≤ T0 := by
    rw [hT0def]
    exact funT0_ge δ
  have hm1 : 1 ≤ m := by omega
  -- the stopping time
  have hstopm : funStops m δ g sel sub (m - 3) 0 := by
    rw [hg'] at h ⊢
    exact Hstop m a (hAa0.trans hAa) ha16 (by rw [← hT0def]; exact hT0m) sel sub h
  have hex : ∃ k, ∃ b, funStops m δ g sel sub k b := ⟨m - 3, 0, hstopm⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Nat.find hex := ⟨_, rfl⟩
  have hκm : κ ≤ m - 3 := by
    rw [hκ]
    exact Nat.find_min' hex ⟨0, hstopm⟩
  obtain ⟨b, hb⟩ := Nat.find_spec hex
  rw [← hκ] at hb
  have hb0 : b = 0 := funStops_leader hg0 hg4 hb
  rw [hb0] at hb
  have hmin : ∀ k, k < κ → ∀ b', ¬ funStops m δ g sel sub k b' := by
    intro k hk b' hs
    rw [hκ] at hk
    exact Nat.find_min hex hk ⟨b', hs⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = 3 + κ := ⟨_, rfl⟩
  have hτκ : τ - 3 = κ := by omega
  have hτ3 : 3 ≤ τ := by omega
  have hτm : τ ≤ m := by omega
  rw [← hτκ] at hb hmin
  have hτlow : 64 / 9 * (m : ℝ) ^ (1 / 8 : ℝ) < (τ : ℝ) := by
    have := funStops_horizon h hδ0 hδ1.le hm1 hgdef hg0 hg4 hb
    have e : 3 + (τ - 3) = τ := by omega
    rw [e] at this
    exact this
  obtain ⟨hL, hU, hne⟩ := funnel_nested (δ := δ) m hδ0 hδ1.le hg0.le (by linarith) sel sub
  have hout := fun k => monRun_outputs (circ := monFunnelCirc m) (x := funBox δ g sel sub)
    hL hU hne (ε := g / 2) (by linarith) k
  have hret := funnel_retired (δ := δ) m h hδ0 hδ1 hg0 hg4
  have hτR : (τ : ℝ) ≤ m := by exact_mod_cast hτm
  have hτa : 64 / 9 * a ^ 2 < (τ : ℝ) := by
    rw [hm8] at hτlow
    exact hτlow
  refine ⟨fun k => (hout k).1, hret, τ, hτ3, ?_, ?_, hτlow, hτm, ?_, ?_⟩
  · intro k hk
    rw [(hout k).2]
    exact Set.eq_empty_iff_forall_notMem.mpr (fun b' hb' => hmin k hk b' hb')
  · rw [(hout (τ - 3)).2]
    exact Set.eq_singleton_iff_unique_mem.mpr
      ⟨hb, fun b' hb' => funStops_leader hg0 hg4 hb'⟩
  · rw [hT0def]
    exact funnel_selective_work h hδ0 hδ1 hg0 hg4 ha8 ha16 rule hτ3 hτm
  · exact funnel_eager_work h hδ0 hδ1 hg0 hg4 ha8 ha16 rule hτa (by rw [← hT0def]; exact hloga)

/-! ### The alternating ladder: the cover count

The last paragraph of the proof mentions an "alternating ladder of size `m`" whose dominated
part has `Θ(m)` disjoint runs at every depth.  The manuscript does not define this family.
The statement below is the counting core under one explicit reading: the terminals of the
ladder are laid out in rung order, the two terminals of rung `i` at positions `2i` and
`2i + 1`, and the internal vertex at depth `j` of one rail has the support
`{2i : j ≤ i < m}` (the terminals of its own parity at the rungs below it). -/

/-- Support of the depth-`j` vertex of one rail of the alternating ladder of size `m`, as a
set of positions. -/
def ladderSupp (m j : ℕ) : Finset ℕ := (Ico j m).image (fun i => 2 * i)

/-- Alternating parity: the support at depth `j` consists of `m - j` runs of length one. -/
theorem ladderSupp_runs (m j : ℕ) : Representation.runs (ladderSupp m j) = m - j := by
  unfold Representation.runs Representation.runEnds
  have hall : (ladderSupp m j).filter (fun x => x + 1 ∉ ladderSupp m j) = ladderSupp m j := by
    apply Finset.filter_true_of_mem
    intro x hx hx1
    unfold ladderSupp at hx hx1
    rw [mem_image] at hx hx1
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨i', -, h⟩ := hx1
    omega
  rw [hall]
  unfold ladderSupp
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have h' : 2 * a = 2 * b := h
    omega), Nat.card_Ico]

private theorem ladder_sum (m : ℕ) : (∑ j ∈ range m, (m - j)) * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have e : ∑ j ∈ range m, (m + 1 - (j + 1)) = ∑ j ∈ range m, (m - j) :=
      Finset.sum_congr rfl (fun j _ => by omega)
    rw [e, Nat.sub_zero, Nat.add_mul, ih]
    ring

/-- **`Ω(m²)` blocks for the internal dyadic covers of the alternating ladder.**  Any choice
of dyadic covers `C j` of the supports at the depths `j < m` stores at least `m²/2` blocks
in total, so writing them takes at least that many steps. -/
theorem ladder_cover_lower (m : ℕ) (C : ℕ → Finset (Finset ℕ))
    (hC : ∀ j, j < m → Representation.IsDyadicCover (C j) (ladderSupp m j)) :
    m ^ 2 ≤ 2 * ∑ j ∈ range m, (C j).card := by
  have h1 : ∑ j ∈ range m, (m - j) ≤ ∑ j ∈ range m, (C j).card :=
    Finset.sum_le_sum (fun j hj => by
      rw [← ladderSupp_runs m j]
      exact Representation.runs_le_card_of_cover (hC j (mem_range.mp hj)))
  have h2 := ladder_sum m
  nlinarith

end

end JointRootCert
