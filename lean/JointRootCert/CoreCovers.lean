/-
Completions of Theorem `thm:ta-core` (Wide Common-Core Support Compilation Cost) of the
appendix "Certification Along Passive Graph-Search Trajectories".

`UCTWork.lean` proves `ta_core` (stopping within `A r log r` rollouts, the winner is
recommended, graph-monitor work at most `B r² log r`, flat supports of size at least `r³`).
This file adds the three remaining clauses.

* Exactness of the stored intervals of the shared-hub monitor (`coreRun_exact`,
  `coreRun_lo_hi`): for every sequence of terminal tables, every active root action of the
  eager and of the selective monitor stores the exact interval `MaxCirc.ival` of its
  subgraph.  The eager monitor keeps every action active (`coreRun_act_false`).
* Equality of the two monitors' stopping tests and stopping times (`core_stops_iff`,
  `ta_core_coupled`): under nested nonempty terminal boxes the selective monitor's active
  sets form a retirement run in the sense of `thm:decision-retirement`
  (`coreRun_retireRun`), so both monitors pass the stopping test at the same steps with the
  same leader.  Nestedness of the Hoeffding boxes is proved (`coreWidth_strictAntiOn`,
  `coreBox_nested`).
* The dyadic-cover clause (`core_cover_compile`, `coreCoverWork_le`, `ta_core_full`): under
  the layout that indexes the `r²` core leaves contiguously (`coreLayout`) every root
  support has at most two runs; the dual-cover compiler of `CostModel.lean` on the explicit
  run lists returns dyadic covers of all supports and complements with at most
  `10 (1 + n) (r + 1)` incidences at cost at most `30 (1 + n) (r + 1)`, `n = ⌈log₂ M⌉`; an
  update of the charged index over the support covers costs at most `5 (n + 1) (r + 2)`
  (`dcRun_cover_bound`: disjoint blocks give at most one changed subscription per root
  action), and the index invariant, hence the equality of every root summary with the
  maximum over the support, is preserved (`dcRun_inv`, `coreCov_root_eq`).  Along the
  certified horizon this is `O(r² log² r)`.

The UCT index is the one of the proof of the theorem, `Q + 2 √(log (1 + t) / N)`, as in
`UCTWork.lean` (the manuscript's displayed definition has `log N_t(v)`).

Cost model: that of `UCTWork.lean` for the graph monitors and of `CostModel.lean` for the
covers (indexed heaps are a primitive charged `⌈log₂ m⌉ + 1` per key update).  Initializing
the segment tree and the heap keys of one endpoint index is charged one unit per cell by
definition in `coreCoverWork`; it is not a costed program.
-/
import JointRootCert.UCTWork
import JointRootCert.MonitorWork
import JointRootCert.CostModel

namespace JointRootCert

open Finset

noncomputable section

/-! ### Exactness of the stored intervals -/

namespace MaxCirc

variable {Z : Type*}

/-- The MAX value is monotone in the environment. -/
theorem ccEval_mono {f g : Z → ℝ} (h : ∀ z, f z ≤ g z) : ∀ c : MaxCirc Z, eval f c ≤ eval g c
  | term z => h z
  | unary c => ccEval_mono h c
  | bin c d => max_le_max (ccEval_mono h c) (ccEval_mono h d)

end MaxCirc

namespace UctNode

variable {Z : Type*}

/-- Every stored interval is the one computed from the children. -/
def Good (x : Z → ℝ × ℝ) : UctNode Z → Prop
  | term _ => True
  | unary v c => v = c.val x ∧ Good x c
  | bin v c d => v = uctJoin (c.val x) (d.val x) ∧ Good x c ∧ Good x d

/-- A consistent monitor graph stores the exact interval at its top vertex. -/
theorem val_eq_ival (x : Z → ℝ × ℝ) : ∀ n : UctNode Z, n.Good x → n.val x = n.shape.ival x
  | term _, _ => rfl
  | unary v c, h => by
      have h' : v = c.val x ∧ Good x c := h
      show v = c.shape.ival x
      rw [h'.1, val_eq_ival x c h'.2]
  | bin v c d, h => by
      have h' : v = uctJoin (c.val x) (d.val x) ∧ Good x c ∧ Good x d := h
      show v = uctJoin (c.shape.ival x) (d.shape.ival x)
      rw [h'.1, val_eq_ival x c h'.2.1, val_eq_ival x d h'.2.2]

end UctNode

section WaveExact

variable {Z : Type*}

theorem uctBuild_good (x : Z → ℝ × ℝ) : ∀ c : MaxCirc Z, (uctBuild x c).Good x
  | .term _ => trivial
  | .unary c => ⟨rfl, uctBuild_good x c⟩
  | .bin c d => ⟨rfl, uctBuild_good x c, uctBuild_good x d⟩

/-- **A wave keeps the stored intervals exact.**  If the stored intervals are consistent
with the old table `x` and `chg` flags exactly the terminals whose interval changed, the
wave returns a graph consistent with the new table `x'` and reports whether the exact
interval of the top vertex changed. -/
theorem uctWave_good {x x' : Z → ℝ × ℝ} {chg : Z → Bool}
    (hchg : ∀ z, chg z = decide (x' z ≠ x z)) :
    ∀ n : UctNode Z, n.Good x →
      (uctWave x' chg n).1.Good x' ∧
        (uctWave x' chg n).2.1 = decide (n.shape.ival x' ≠ n.shape.ival x)
  | .term z, _ => ⟨trivial, hchg z⟩
  | .unary v c, h => by
      obtain ⟨hv, hc⟩ : v = c.val x ∧ c.Good x := h
      obtain ⟨ih1, ih3⟩ := uctWave_good hchg c hc
      have hval := UctNode.val_eq_ival x' _ ih1
      rw [uctWave_shape] at hval
      have hv' : v = c.shape.ival x := hv.trans (UctNode.val_eq_ival x c hc)
      by_cases hf : (uctWave x' chg c).2.1 = true
      · rw [uctWave, ite_eq_left hf]
        refine ⟨⟨rfl, ih1⟩, ?_⟩
        show decide ((uctWave x' chg c).1.val x' ≠ v) = _
        rw [hval, hv']
        rfl
      · have heq : c.shape.ival x' = c.shape.ival x := by
          rw [ih3] at hf
          by_contra hne
          exact hf (decide_eq_true hne)
        rw [uctWave, ite_eq_right hf]
        refine ⟨⟨?_, ih1⟩, ?_⟩
        · rw [hval, heq, hv']
        · show false = decide (c.shape.ival x' ≠ c.shape.ival x)
          simp [heq]
  | .bin v c d, h => by
      obtain ⟨hv, hc, hd⟩ : v = uctJoin (c.val x) (d.val x) ∧ c.Good x ∧ d.Good x := h
      obtain ⟨ic1, ic3⟩ := uctWave_good hchg c hc
      obtain ⟨id1, id3⟩ := uctWave_good hchg d hd
      have hvalc := UctNode.val_eq_ival x' _ ic1
      rw [uctWave_shape] at hvalc
      have hvald := UctNode.val_eq_ival x' _ id1
      rw [uctWave_shape] at hvald
      have hv' : v = uctJoin (c.shape.ival x) (d.shape.ival x) := by
        rw [hv, UctNode.val_eq_ival x c hc, UctNode.val_eq_ival x d hd]
      have hcd : ∀ y : Z → ℝ × ℝ, (MaxCirc.bin c.shape d.shape).ival y
          = uctJoin (c.shape.ival y) (d.shape.ival y) := fun _ => rfl
      by_cases hf : (uctWave x' chg c).2.1 = true ∨ (uctWave x' chg d).2.1 = true
      · rw [uctWave, ite_eq_left hf]
        refine ⟨⟨rfl, ic1, id1⟩, ?_⟩
        show decide (uctJoin ((uctWave x' chg c).1.val x') ((uctWave x' chg d).1.val x') ≠ v)
          = decide ((MaxCirc.bin c.shape d.shape).ival x' ≠ (MaxCirc.bin c.shape d.shape).ival x)
        rw [hvalc, hvald, hv', hcd, hcd]
      · have hfc : (uctWave x' chg c).2.1 ≠ true := fun h => hf (Or.inl h)
        have hfd : (uctWave x' chg d).2.1 ≠ true := fun h => hf (Or.inr h)
        have heqc : c.shape.ival x' = c.shape.ival x := by
          rw [ic3] at hfc
          by_contra hne
          exact hfc (decide_eq_true hne)
        have heqd : d.shape.ival x' = d.shape.ival x := by
          rw [id3] at hfd
          by_contra hne
          exact hfd (decide_eq_true hne)
        rw [uctWave, ite_eq_right hf]
        refine ⟨⟨?_, ic1, id1⟩, ?_⟩
        · rw [hvalc, hvald, heqc, heqd, hv']
        · show false
            = decide ((MaxCirc.bin c.shape d.shape).ival x' ≠ (MaxCirc.bin c.shape d.shape).ival x)
          rw [hcd, hcd, heqc, heqd]
          simp

end WaveExact

section CoreExact

variable {r : ℕ}

/-- Exactness invariant of the shared-hub monitors: the hub graph, while held, is consistent
with the terminal table, and the top vertex of every active losing action stores the exact
interval of its subgraph (the MAX of the hub and its private leaf); the hub is held as long
as a losing action is active. -/
def CoreExact (hub : MaxCirc (CoreZ r)) (x : CoreZ r → ℝ × ℝ) (σ : CoreMon r) : Prop :=
  (∀ n, σ.hub = some n → n.shape = hub ∧ n.Good x) ∧
    ∀ i : Fin r, Fin.castSucc i ∈ σ.act →
      σ.hub ≠ none ∧ σ.top i = uctJoin (hub.ival x) (x (corePriv r i))

variable {hub : MaxCirc (CoreZ r)} {x x' : CoreZ r → ℝ × ℝ} {σ : CoreMon r}

theorem coreRetire_exact (s : Bool) (h : CoreExact hub x σ) :
    CoreExact hub x (coreRetire s x σ).1 := by
  classical
  cases s
  · exact h
  · refine ⟨fun n hn => ?_, fun i hi => ?_⟩
    · have hn' : (if ∃ i : Fin r, Fin.castSucc i ∈ coreKeep x σ then σ.hub else none) = some n :=
        hn
      split_ifs at hn'
      exact h.1 n hn'
    · have hi' : Fin.castSucc i ∈ coreKeep x σ := hi
      have hact : Fin.castSucc i ∈ σ.act := by
        unfold coreKeep at hi'
        exact (mem_filter.mp hi').1
      refine ⟨?_, (h.2 i hact).2⟩
      show (if ∃ i : Fin r, Fin.castSucc i ∈ coreKeep x σ then σ.hub else none) ≠ none
      rw [ite_eq_left ⟨i, hi'⟩]
      exact (h.2 i hact).1

theorem coreWave_exact {chg : CoreZ r → Bool} (hchg : ∀ z, chg z = decide (x' z ≠ x z))
    (h : CoreExact hub x σ) : CoreExact hub x' (coreWave x' chg σ).1 := by
  classical
  have hnew : ∀ n, coreHubNew x' chg σ = some n → n.shape = hub ∧ n.Good x' := by
    intro n hn
    unfold coreHubNew at hn
    cases ho : σ.hub with
    | none => rw [ho] at hn; exact absurd hn (by simp)
    | some n0 =>
      rw [ho] at hn
      have e : (uctWave x' chg n0).1 = n := Option.some_inj.mp hn
      obtain ⟨hs, hg⟩ := h.1 n0 ho
      rw [← e]
      exact ⟨(uctWave_shape x' chg n0).trans hs, (uctWave_good hchg n0 hg).1⟩
  refine ⟨hnew, fun i hi => ?_⟩
  have hi' : Fin.castSucc i ∈ σ.act := hi
  obtain ⟨hne, htop⟩ := h.2 i hi'
  obtain ⟨n0, ho⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨hs, hg⟩ := h.1 n0 ho
  have hflag : coreHubFlag x' chg σ = decide (hub.ival x' ≠ hub.ival x) := by
    unfold coreHubFlag
    rw [ho, ← hs]
    exact (uctWave_good hchg n0 hg).2
  have hval : coreHubVal x' (coreHubNew x' chg σ) = hub.ival x' := by
    unfold coreHubVal coreHubNew
    rw [ho]
    show ((uctWave x' chg n0).1).val x' = _
    rw [UctNode.val_eq_ival x' _ (uctWave_good hchg n0 hg).1, uctWave_shape, hs]
  refine ⟨?_, ?_⟩
  · show coreHubNew x' chg σ ≠ none
    unfold coreHubNew
    rw [ho]
    simp
  · show (if Fin.castSucc i ∈ σ.act ∧
          (coreHubFlag x' chg σ = true ∨ chg (corePriv r i) = true) then
        uctJoin (coreHubVal x' (coreHubNew x' chg σ)) (x' (corePriv r i)) else σ.top i) = _
    by_cases hc : coreHubFlag x' chg σ = true ∨ chg (corePriv r i) = true
    · rw [ite_eq_left ⟨hi', hc⟩, hval]
    · rw [ite_eq_right (fun h => hc h.2), htop]
      have h1 : hub.ival x' = hub.ival x := by
        by_contra hne'
        exact hc (Or.inl (by rw [hflag]; exact decide_eq_true hne'))
      have h2 : x' (corePriv r i) = x (corePriv r i) := by
        by_contra hne'
        exact hc (Or.inr (by rw [hchg]; exact decide_eq_true hne'))
      rw [h1, h2]

/-- **Exactness of the stored intervals, invariant.**  For every sequence of terminal
tables, both monitors satisfy `CoreExact` at every step. -/
theorem coreRun_exact (s : Bool) (hub : MaxCirc (CoreZ r)) (x : ℕ → CoreZ r → ℝ × ℝ) :
    ∀ k, CoreExact hub (x k) (coreRun s hub x k)
  | 0 => by
      refine ⟨fun n hn => ?_, fun i _ => ⟨?_, ?_⟩⟩
      · have e : uctBuild (x 0) hub = n := Option.some_inj.mp hn
        rw [← e]
        exact ⟨uctBuild_shape _ _, uctBuild_good _ _⟩
      · show some (uctBuild (x 0) hub) ≠ none
        simp
      · show uctJoin ((uctBuild (x 0) hub).val (x 0)) (x 0 (corePriv r i)) = _
        rw [UctNode.val_eq_ival _ _ (uctBuild_good _ _), uctBuild_shape]
  | k + 1 => coreWave_exact (fun _ => rfl) (coreRetire_exact s (coreRun_exact s hub x k))

/-- The eager monitor keeps every root action active. -/
theorem coreRun_act_false (hub : MaxCirc (CoreZ r)) (x : ℕ → CoreZ r → ℝ × ℝ) :
    ∀ k, (coreRun false hub x k).act = univ
  | 0 => rfl
  | k + 1 => coreRun_act_false hub x k

variable [NeZero r]

/-- Exact lower endpoint of root action `a` at step `k`: the MAX of the terminal lower
endpoints over the subgraph below `a`. -/
def coreL (r : ℕ) [NeZero r] (x : ℕ → CoreZ r → ℝ × ℝ) (k : ℕ) (a : Fin (r + 1)) : ℝ :=
  ((coreAct r a).ival (x k)).1

/-- Exact upper endpoint of root action `a` at step `k`. -/
def coreU (r : ℕ) [NeZero r] (x : ℕ → CoreZ r → ℝ × ℝ) (k : ℕ) (a : Fin (r + 1)) : ℝ :=
  ((coreAct r a).ival (x k)).2

/-- **Exactness of the stored intervals** (`thm:ta-core`, shared-hub monitor).  For every
sequence of terminal tables and every step, the interval that the selective (`s = true`)
or the eager (`s = false`) monitor stores for an active root action is the exact interval
of its subgraph.  For the eager monitor every action is active (`coreRun_act_false`). -/
theorem coreRun_lo_hi (s : Bool) (x : ℕ → CoreZ r → ℝ × ℝ) (k : ℕ) {a : Fin (r + 1)}
    (ha : a ∈ (coreRun s (coreHub r) x k).act) :
    (coreRun s (coreHub r) x k).lo (x k) a = coreL r x k a ∧
      (coreRun s (coreHub r) x k).hi (x k) a = coreU r x k a := by
  have hex := coreRun_exact s (coreHub r) x k
  unfold CoreMon.lo CoreMon.hi coreL coreU coreAct
  by_cases h : (a : ℕ) < r
  · have ha' : Fin.castSucc (⟨a, h⟩ : Fin r) ∈ (coreRun s (coreHub r) x k).act := by
      have e : Fin.castSucc (⟨a, h⟩ : Fin r) = a := Fin.ext rfl
      rw [e]
      exact ha
    simp only [dite_eq_left h]
    rw [(hex.2 _ ha').2]
    exact ⟨rfl, rfl⟩
  · simp only [dite_eq_right h]
    exact ⟨rfl, rfl⟩

/-! ### Coupling of the two monitors -/

/-- Under nested nonempty terminal boxes, the active sets of the selective shared-hub
monitor form a retirement run for the exact root-action intervals
(`thm:decision-retirement`). -/
theorem coreRun_retireRun (x : ℕ → CoreZ r → ℝ × ℝ)
    (hmono : ∀ z s t, s ≤ t → (x s z).1 ≤ (x t z).1 ∧ (x t z).2 ≤ (x s z).2)
    (hne : ∀ t z, (x t z).1 ≤ (x t z).2) :
    RetireRun (coreL r x) (coreU r x) (fun k => (coreRun true (coreHub r) x k).act) where
  nestedL := fun a s t hst => by
    show MaxCirc.eval (fun z => (x s z).1) (coreAct r a)
      ≤ MaxCirc.eval (fun z => (x t z).1) (coreAct r a)
    exact MaxCirc.ccEval_mono (fun z => (hmono z s t hst).1) _
  nestedU := fun a s t hst => by
    show MaxCirc.eval (fun z => (x t z).2) (coreAct r a)
      ≤ MaxCirc.eval (fun z => (x s z).2) (coreAct r a)
    exact MaxCirc.ccEval_mono (fun z => (hmono z s t hst).2) _
  nonempty := fun t a => by
    show MaxCirc.eval (fun z => (x t z).1) (coreAct r a)
      ≤ MaxCirc.eval (fun z => (x t z).2) (coreAct r a)
    exact MaxCirc.ccEval_mono (fun z => hne t z) _
  init := rfl
  anti := by
    classical
    intro t b hb
    have hb' : b ∈ coreKeep (x t) (coreRun true (coreHub r) x t) := hb
    unfold coreKeep at hb'
    exact (mem_filter.mp hb').1
  retire := by
    classical
    intro t b hb1 hb2
    by_contra hcon
    apply hb1
    show b ∈ coreKeep (x t) (coreRun true (coreHub r) x t)
    unfold coreKeep
    rw [mem_filter]
    refine ⟨hb2, ?_⟩
    rintro ⟨a, ha, hne', hlt⟩
    apply hcon
    refine ⟨a, ha, hne', ?_⟩
    rw [← (coreRun_lo_hi true x t hb2).2, ← (coreRun_lo_hi true x t ha).1]
    exact hlt

/-- **The two monitors pass the stopping test at the same steps with the same leader.**
For nested nonempty terminal boxes, at every step and for every root action `a`, the
stopping test of the selective monitor passes with leader `a` iff that of the eager monitor
does. -/
theorem core_stops_iff (x : ℕ → CoreZ r → ℝ × ℝ)
    (hmono : ∀ z s t, s ≤ t → (x s z).1 ≤ (x t z).1 ∧ (x t z).2 ≤ (x s z).2)
    (hne : ∀ t z, (x t z).1 ≤ (x t z).2) (k : ℕ) (a : Fin (r + 1)) :
    coreStops (coreRun true (coreHub r) x k) (x k) a ↔
      coreStops (coreRun false (coreHub r) x k) (x k) a := by
  have hR := coreRun_retireRun x hmono hne
  unfold coreStops
  rw [marginalStops_congr (fun b hb => (coreRun_lo_hi true x k hb).1)
      (fun b hb => (coreRun_lo_hi true x k hb).2) a,
    marginalStops_congr (fun b hb => (coreRun_lo_hi false x k hb).1)
      (fun b hb => (coreRun_lo_hi false x k hb).2) a, coreRun_act_false]
  exact (hR.stops_iff (by norm_num) k a).symm

end CoreExact

/-! ### Nestedness of the Hoeffding boxes -/

private theorem cc_exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

/-- The Hoeffding width `2 √(log (4 M x² / δ) / (2x))` strictly decreases on `[1, ∞)` for
`M ≥ 2` and `δ ∈ (0, 1]`. -/
theorem coreWidth_strictAntiOn {M δ : ℝ} (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    StrictAntiOn (hoeffdingWidth M δ) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < 4 * M / δ := div_pos (by linarith) hδ0
  have hc : 2 < Real.log (4 * M / δ) := by
    rw [Real.lt_log_iff_exp_lt hc0]
    refine lt_of_lt_of_le cc_exp_two_lt_eight ?_
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

/-- The radius of the common-core boxes does not increase with the count. -/
theorem coreRadius_anti {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {r : ℕ} (hr : 1 ≤ r) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) : coreRadius r δ k ≤ coreRadius r δ j := by
  have hM : (2 : ℝ) ≤ ((r ^ 2 + r + 1 : ℕ) : ℝ) := by
    have : 2 ≤ r ^ 2 + r + 1 := by nlinarith
    exact_mod_cast this
  have := (coreWidth_strictAntiOn hM hδ0 hδ1).antitoneOn
    (Set.mem_Ici.mpr (by exact_mod_cast hj : (1 : ℝ) ≤ (j : ℝ)))
    (Set.mem_Ici.mpr (by exact_mod_cast hj.trans hjk : (1 : ℝ) ≤ (k : ℝ)))
    (by exact_mod_cast hjk : (j : ℝ) ≤ (k : ℝ))
  unfold coreRadius
  linarith

/-- **Nested nonempty boxes.**  For a nonnegative radius that does not increase with the
count, the terminal tables of the common-core search are nested and nonempty. -/
theorem coreBox_nested {r : ℕ} {β : ℕ → ℝ} (hβ0 : ∀ n, 0 ≤ β n)
    (hanti : ∀ j k, 1 ≤ j → j ≤ k → β k ≤ β j) (zt : ℕ → CoreZ r) :
    (∀ z s t, s ≤ t → (coreBox r β zt s z).1 ≤ (coreBox r β zt t z).1 ∧
        (coreBox r β zt t z).2 ≤ (coreBox r β zt s z).2) ∧
      ∀ t z, (coreBox r β zt t z).1 ≤ (coreBox r β zt t z).2 := by
  have hμ : ∀ z, 0 ≤ coreReward r z ∧ coreReward r z ≤ 1 := by
    intro z
    rcases z with c | p | u
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  constructor
  · intro z s t hst
    have hc : uctCount zt (r + 1 + s) z ≤ uctCount zt (r + 1 + t) z :=
      uctCount_mono zt z (by omega)
    unfold coreBox coreTab
    by_cases h0 : uctCount zt (r + 1 + s) z = 0
    · rw [ite_eq_left h0]
      by_cases h1 : uctCount zt (r + 1 + t) z = 0
      · rw [ite_eq_left h1]
        exact ⟨le_rfl, le_rfl⟩
      · rw [ite_eq_right h1]
        exact ⟨le_max_left _ _, min_le_left _ _⟩
    · have h1 : uctCount zt (r + 1 + t) z ≠ 0 := by omega
      rw [ite_eq_right h0, ite_eq_right h1]
      have := hanti _ _ (by omega) hc
      exact ⟨max_le_max le_rfl (by linarith), min_le_min le_rfl (by linarith)⟩
  · intro t z
    unfold coreBox coreTab
    obtain ⟨h0, h1⟩ := hμ z
    have hb := hβ0 (uctCount zt (r + 1 + t) z)
    split_ifs
    · exact zero_le_one
    · exact le_min (max_le zero_le_one (by linarith)) (max_le (by linarith) (by linarith))

/-- **Theorem `thm:ta-core`, with the two monitors coupled.**  Fix `δ ∈ (0, 1)`.  There are
constants `A, B` such that for every `r ≥ 2` and every UCT search on the common-core DAG
with the Hoeffding boxes:

* at every step the stopping test of the selective monitor passes with leader `a` iff that
  of the eager monitor does, and each monitor stores the exact interval of every root action
  that it keeps active;
* there is ONE step `τ` at which both monitors stop for the first time, both recommending
  the winning action, with `r + 1 + τ ≤ A r log r`;
* the total work of either monitor up to `τ` is at most `B r² log r`;
* the flat supports of the losing actions have total size at least `r³`. -/
theorem ta_core_coupled {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r),
      CoreSearch r rule sel zt →
        (∀ k a, coreStops (coreRun true (coreHub r) (coreBox r (coreRadius r δ) zt) k)
            (coreBox r (coreRadius r δ) zt k) a ↔
          coreStops (coreRun false (coreHub r) (coreBox r (coreRadius r δ) zt) k)
            (coreBox r (coreRadius r δ) zt k) a) ∧
        (∀ (s : Bool) k a, a ∈ (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k).act →
          (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k).lo
              (coreBox r (coreRadius r δ) zt k) a = coreL r (coreBox r (coreRadius r δ) zt) k a ∧
            (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k).hi
              (coreBox r (coreRadius r δ) zt k) a
                = coreU r (coreBox r (coreRadius r δ) zt) k a) ∧
        ∃ τ : ℕ,
          (∀ s : Bool, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
            (coreBox r (coreRadius r δ) zt τ) (Fin.last r)) ∧
          (∀ (s : Bool) k, k < τ → ∀ a,
            ¬ coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
          (∀ (s : Bool) k a, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
            (coreBox r (coreRadius r δ) zt k) a → a = Fin.last r) ∧
          ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
          (∀ s : Bool, (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ B * (r : ℝ) ^ 2 * Real.log r) ∧
          r ^ 3 ≤ ∑ i : Fin r, (coreLoseSupp r i).card := by
  obtain ⟨A, B, hA, hB, H⟩ := ta_core hδ0 hδ1
  refine ⟨A, B, hA, hB, ?_⟩
  intro r _ hr rule sel zt h
  obtain ⟨hmono, hne⟩ := coreBox_nested (coreRadius_nonneg r δ)
    (fun j k hj hjk => coreRadius_anti hδ0 hδ1.le (by omega) hj hjk) zt
  have hiff := core_stops_iff (coreBox r (coreRadius r δ) zt) hmono hne
  obtain ⟨τ, f1, f2, f3, f4, f5, f6⟩ := H r hr rule sel zt h false
  obtain ⟨τ', t1, t2, t3, -, t5, -⟩ := H r hr rule sel zt h true
  have hττ : τ' = τ := by
    rcases Nat.lt_trichotomy τ' τ with hlt | heq | hgt
    · exact absurd ((hiff τ' _).mp t1) (f2 τ' hlt _)
    · exact heq
    · exact absurd ((hiff τ _).mpr f1) (t2 τ hgt _)
  subst hττ
  refine ⟨hiff, fun s k a ha => coreRun_lo_hi s _ k ha, τ', ?_, ?_, ?_, f4, ?_, f6⟩
  · intro s
    cases s
    · exact f1
    · exact t1
  · intro s
    cases s
    · exact f2
    · exact t2
  · intro s
    cases s
    · exact f3
    · exact t3
  · intro s
    cases s
    · exact f5
    · exact t5

/-! ### The dyadic-cover clause -/

section Covers

open _root_.JointRootCert.Representation _root_.JointRootCert.CostModel

theorem ccBlk_card (d : ℕ × ℕ) : (blk d).card = 2 ^ d.1 := by
  simp only [blk, dyadicBlock, Nat.card_Ico]
  rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

/-- Every position lies in the blocks of its leaf-to-root path. -/
theorem ccMem_blk_path (p k : ℕ) : p ∈ blk (k, p / 2 ^ k) := by
  have hpos : 0 < 2 ^ k := by positivity
  simp only [blk, dyadicBlock, mem_Ico]
  refine ⟨Nat.div_mul_le_self p (2 ^ k), ?_⟩
  rw [Nat.add_mul, one_mul]
  exact Nat.lt_div_mul_add hpos

theorem ccList_sum_le (l : List ℕ) (c : ℕ) (h : ∀ x ∈ l, x ≤ c) : l.sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (List.mem_cons_self)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.sum_cons, List.length_cons]
    nlinarith

theorem changedNodes_nodup {α : Type*} [LinearOrder α] (p : ℕ) (v v' : ℕ → ℕ → α) :
    ∀ n, (changedNodes p v v' n).1.Nodup
  | 0 => by
      simp only [changedNodes]
      split_ifs <;> simp
  | n + 1 => by
      have ih := changedNodes_nodup p v v' n
      simp only [changedNodes]
      split_ifs
      · exact ih
      · refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih⟩
        have := ((mem_changedNodes p v v' n _ _).mp hmem).1
        omega

/-- **Changed subscriptions under disjoint covers.**  If the blocks subscribed by each root
action are pairwise disjoint (so two subscribed blocks containing the same position have the
same level) and the reverse-incidence lists have no repetitions, an update changes at most
one subscription per root action. -/
theorem changedSubs_length_le {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [Fintype A]
    [DecidableEq A] (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (hnd : ∀ d, (subs d).Nodup) (hmem : ∀ d a, a ∈ subs d → d ∈ cov a)
    (hone : ∀ p a d d', d ∈ cov a → d' ∈ cov a → p ∈ blk d → p ∈ blk d' → d.1 = d'.1)
    (p : ℕ) (x : α) (tree : ℕ → ℕ → α) :
    (changedSubs n subs p x tree).length ≤ Fintype.card A := by
  have hlen : (changedSubs n subs p x tree).length
      = ((changedSubs n subs p x tree).map Prod.snd).length := by rw [List.length_map]
  rw [hlen]
  apply List.Nodup.length_le_card
  have e : (changedSubs n subs p x tree).map Prod.snd
      = (changedNodes p tree (pathUpdate p x tree n).1 n).1.flatMap subs := by
    unfold changedSubs
    rw [List.map_flatMap]
    congr 1
    funext d
    simp
  rw [e, List.nodup_flatMap]
  refine ⟨fun d _ => hnd d, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (changedNodes_nodup p tree _ n)
  intro d d' hd hd' hne
  show List.Disjoint (subs d) (subs d')
  intro a ha ha'
  obtain ⟨-, h2, -⟩ := (mem_changedNodes p tree _ n d.1 d.2).mp hd
  obtain ⟨-, h2', -⟩ := (mem_changedNodes p tree _ n d'.1 d'.2).mp hd'
  have hp : p ∈ blk d := by
    have := ccMem_blk_path p d.1
    rw [← h2] at this
    exact this
  have hp' : p ∈ blk d' := by
    have := ccMem_blk_path p d'.1
    rw [← h2'] at this
    exact this
  have h1 := hone p a d d' (hmem d a ha) (hmem d' a ha') hp hp'
  apply hne
  exact Prod.ext h1 (by rw [h2, h2', h1])

/-- **Work of a run of updates under disjoint covers.**  With `|A|` root actions whose
heaps have at most `bmax` keys, a run of `T` updates costs at most
`T (2h + |A| (⌈log₂ bmax⌉ + ⌈log₂ K⌉ + 2))`, `h = n + 1`. -/
theorem dcRun_cover_bound {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [Fintype A]
    [DecidableEq A] (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A) (bsz : A → ℕ)
    (K bmax : ℕ) (hnd : ∀ d, (subs d).Nodup) (hmem : ∀ d a, a ∈ subs d → d ∈ cov a)
    (hone : ∀ p a d d', d ∈ cov a → d' ∈ cov a → p ∈ blk d → p ∈ blk d' → d.1 = d'.1)
    (hb : ∀ a, bsz a ≤ bmax) :
    ∀ (us : List (ℕ × α)) (s : DCState A α),
      (dcRun n cov subs bsz K us s).2
        ≤ us.length * (2 * (n + 1)
            + Fintype.card A * (Nat.clog 2 bmax + Nat.clog 2 K + 2)) := by
  intro us
  induction us with
  | nil => intro s; simp [dcRun]
  | cons u us ih =>
    intro s
    have hlen := changedSubs_length_le n cov subs hnd hmem hone u.1 u.2 s.tree
    have hheap : ((changedSubs n subs u.1 u.2 s.tree).map
        (fun e => Nat.clog 2 (bsz e.2) + 1)).sum
        ≤ (changedSubs n subs u.1 u.2 s.tree).length * (Nat.clog 2 bmax + 1) := by
      calc _ ≤ ((changedSubs n subs u.1 u.2 s.tree).map
              (fun _ => Nat.clog 2 bmax + 1)).sum := by
            apply List.sum_le_sum
            intro e _
            exact Nat.add_le_add_right (Nat.clog_mono_right 2 (hb e.2)) 1
        _ = _ := by simp
    have haff : (affected n subs u.1 u.2 s.tree).length
        ≤ (changedSubs n subs u.1 u.2 s.tree).length := by
      unfold affected
      exact ((List.dedup_sublist _).length_le).trans (by simp)
    have hstep := dcUpdate_cost n cov subs bsz K u.1 u.2 s
    have hrest := ih (dcUpdate n cov subs bsz K u.1 u.2 s).1
    have h1 : (changedSubs n subs u.1 u.2 s.tree).length * (Nat.clog 2 bmax + 1)
        ≤ Fintype.card A * (Nat.clog 2 bmax + 1) := Nat.mul_le_mul_right _ hlen
    have h2 : (affected n subs u.1 u.2 s.tree).length * (Nat.clog 2 K + 1)
        ≤ Fintype.card A * (Nat.clog 2 K + 1) := Nat.mul_le_mul_right _ (haff.trans hlen)
    simp only [dcRun, List.length_cons]
    nlinarith

/-- A run of updates preserves the invariant of the charged index: after the run every tree
node, heap key and root summary is the one of the updated leaf values. -/
theorem dcRun_inv {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]
    (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A) (bsz : A → ℕ) (K : ℕ)
    (hsub : ∀ a, ∀ d ∈ cov a, a ∈ subs d) (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n) :
    ∀ (us : List (ℕ × α)) (f : ℕ → α) (s : DCState A α), DCInv n cov f s →
      DCInv n cov (us.foldl (fun f u => Function.update f u.1 u.2) f)
        (dcRun n cov subs bsz K us s).1 := by
  intro us
  induction us with
  | nil => intro f s h; exact h
  | cons u us ih =>
    intro f s h
    exact ih _ _ (dcUpdate_inv n cov subs bsz K u.1 u.2 f s hsub hlev h)

/-! #### The contiguous layout of the common-core terminals -/

/-- The layout that indexes the `r²` core leaves contiguously: core leaf `j` at position
`j`, the private leaf of the losing action `i` at `r² + i`, the winning terminal at
`r² + r`. -/
def coreLayout (r : ℕ) : CoreZ r ≃ Fin (r ^ 2 + r + 1) :=
  (Equiv.sumCongr (Equiv.refl _)
      (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1)))).trans
    ((Equiv.sumAssoc _ _ _).symm.trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv))

theorem coreLayout_core (r : ℕ) (j : Fin (r ^ 2)) :
    ((coreLayout r (Sum.inl j) : Fin (r ^ 2 + r + 1)) : ℕ) = j := by
  simp [coreLayout]

theorem coreLayout_priv (r : ℕ) (i : Fin r) :
    ((coreLayout r (Sum.inr (Sum.inl i)) : Fin (r ^ 2 + r + 1)) : ℕ) = r ^ 2 + i := by
  simp [coreLayout]

theorem coreLayout_win (r : ℕ) :
    ((coreLayout r (Sum.inr (Sum.inr ())) : Fin (r ^ 2 + r + 1)) : ℕ) = r ^ 2 + r := by
  simp [coreLayout]

/-- Support of a root action: the losing actions `0, …, r - 1` and the winning action `r`. -/
def coreSupp (r : ℕ) (a : Fin (r + 1)) : Finset (CoreZ r) :=
  if h : (a : ℕ) < r then coreLoseSupp r ⟨a, h⟩ else coreWinSupp r

theorem coreLayout_losePos (r : ℕ) (i : Fin r) :
    layoutPos (coreLayout r) (coreLoseSupp r i) = insert (r ^ 2 + (i : ℕ)) (range (r ^ 2)) := by
  ext s
  simp only [layoutPos, coreLoseSupp, mem_image, mem_insert, mem_map, mem_univ, true_and,
    Function.Embedding.coeFn_mk, mem_range]
  constructor
  · rintro ⟨z, (rfl | ⟨j, rfl⟩), rfl⟩
    · exact Or.inl (coreLayout_priv r i)
    · exact Or.inr (by rw [coreLayout_core]; exact j.isLt)
  · rintro (rfl | hs)
    · exact ⟨_, Or.inl rfl, coreLayout_priv r i⟩
    · exact ⟨Sum.inl ⟨s, hs⟩, Or.inr ⟨⟨s, hs⟩, rfl⟩, coreLayout_core r _⟩

theorem coreLayout_winPos (r : ℕ) :
    layoutPos (coreLayout r) (coreWinSupp r) = {r ^ 2 + r} := by
  simp [layoutPos, coreWinSupp, coreLayout_win]

/-- The run list of a root support under the contiguous layout: one or two runs. -/
def coreRunList (r : ℕ) (a : Fin (r + 1)) : List (ℕ × ℕ) :=
  if (a : ℕ) < r then
    (if (a : ℕ) = 0 then [(0, r ^ 2 + 1)] else [(0, r ^ 2), (r ^ 2 + a, r ^ 2 + a + 1)])
  else [(r ^ 2 + r, r ^ 2 + r + 1)]

/-- **Each root support decomposes into at most two contiguous intervals** under the
contiguous layout, and `coreRunList` is its run list. -/
theorem coreRunList_spec (r : ℕ) [NeZero r] (a : Fin (r + 1)) :
    RunsFrom (r ^ 2 + r + 1) 0 (coreRunList r a) ∧
      runSet (coreRunList r a) = layoutPos (coreLayout r) (coreSupp r a) ∧
      (coreRunList r a).length ≤ 2 := by
  have hr : 1 ≤ r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hq : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  unfold coreRunList coreSupp
  by_cases h : (a : ℕ) < r
  · rw [ite_eq_left h, dite_eq_left h, coreLayout_losePos]
    by_cases h0 : (a : ℕ) = 0
    · rw [ite_eq_left h0]
      refine ⟨?_, ?_, by simp⟩
      · simp only [RunsFrom, and_true]
        omega
      · ext s
        simp only [runSet, mem_union, mem_Ico, notMem_empty, or_false, mem_insert, mem_range]
        omega
    · rw [ite_eq_right h0]
      refine ⟨?_, ?_, by simp⟩
      · simp only [RunsFrom, and_true]
        omega
      · ext s
        simp only [runSet, mem_union, mem_Ico, notMem_empty, or_false, mem_insert, mem_range]
        omega
  · rw [ite_eq_right h, dite_eq_right h, coreLayout_winPos]
    refine ⟨?_, ?_, by simp⟩
    · simp only [RunsFrom, and_true]
      omega
    · ext s
      simp only [runSet, mem_union, mem_Ico, notMem_empty, or_false, mem_singleton]
      omega

/-- Height parameter of the segment tree: `n = ⌈log₂ M⌉` for `M = r² + r + 1` terminals. -/
def coreN (r : ℕ) : ℕ := Nat.clog 2 (r ^ 2 + r + 1)

/-- **`thm:ta-core`, dyadic-cover clause: compilation.**  Under the contiguous layout the
dual-cover compiler of `CostModel.lean`, run on the explicit run lists of the `r + 1` root
supports, returns for each root action dyadic covers of its support and of its complement,
stores at most `10 (1 + n) (r + 1)` incidences and costs at most `30 (1 + n) (r + 1)`
steps. -/
theorem core_cover_compile (r : ℕ) [NeZero r] :
    (∀ a, IsDyadicCover
        ((dualCompile (coreN r) (r ^ 2 + r + 1) (coreRunList r a)).1.1.map blk).toFinset
        (layoutPos (coreLayout r) (coreSupp r a)) ∧
      IsDyadicCover
        ((dualCompile (coreN r) (r ^ 2 + r + 1) (coreRunList r a)).1.2.map blk).toFinset
        (layoutPos (coreLayout r) (coreSupp r a)ᶜ)) ∧
    incidences (compileAll (coreN r) (r ^ 2 + r + 1)
        ((List.finRange (r + 1)).map (coreRunList r))).1 ≤ 10 * (1 + coreN r) * (r + 1) ∧
    (compileAll (coreN r) (r ^ 2 + r + 1)
        ((List.finRange (r + 1)).map (coreRunList r))).2 ≤ 30 * (1 + coreN r) * (r + 1) := by
  obtain ⟨-, h2, h3, h4⟩ := dualCover_compile (coreLayout r) (coreSupp r)
    (List.finRange (r + 1)) (coreRunList r)
    (fun a => ⟨(coreRunList_spec r a).1, (coreRunList_spec r a).2.1⟩)
  have hR : ((List.finRange (r + 1)).map
      (fun a => runs (layoutPos (coreLayout r) (coreSupp r a)))).sum ≤ 2 * (r + 1) := by
    have := ccList_sum_le ((List.finRange (r + 1)).map
      (fun a => runs (layoutPos (coreLayout r) (coreSupp r a)))) 2 (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
        rw [← (coreRunList_spec r a).2.1, runs_runSet (coreRunList_spec r a).1]
        exact (coreRunList_spec r a).2.2)
    rw [List.length_map, List.length_finRange] at this
    omega
  rw [List.length_finRange] at h3 h4
  have h3' : incidences (compileAll (coreN r) (r ^ 2 + r + 1)
        ((List.finRange (r + 1)).map (coreRunList r))).1
      ≤ 2 * (1 + coreN r) * (2 * ((List.finRange (r + 1)).map
        (fun a => runs (layoutPos (coreLayout r) (coreSupp r a)))).sum + (r + 1)) := h3
  have h4' : (compileAll (coreN r) (r ^ 2 + r + 1)
        ((List.finRange (r + 1)).map (coreRunList r))).2
      ≤ 4 * (1 + coreN r) * (2 * ((List.finRange (r + 1)).map
        (fun a => runs (layoutPos (coreLayout r) (coreSupp r a)))).sum + (r + 1))
        + incidences (compileAll (coreN r) (r ^ 2 + r + 1)
          ((List.finRange (r + 1)).map (coreRunList r))).1 := h4
  have hA : 2 * (1 + coreN r) * (2 * ((List.finRange (r + 1)).map
        (fun a => runs (layoutPos (coreLayout r) (coreSupp r a)))).sum + (r + 1))
      ≤ 2 * (1 + coreN r) * (5 * (r + 1)) := Nat.mul_le_mul_left _ (by omega)
  have hB : 4 * (1 + coreN r) * (2 * ((List.finRange (r + 1)).map
        (fun a => runs (layoutPos (coreLayout r) (coreSupp r a)))).sum + (r + 1))
      ≤ 4 * (1 + coreN r) * (5 * (r + 1)) := Nat.mul_le_mul_left _ (by omega)
  have e1 : 2 * (1 + coreN r) * (5 * (r + 1)) = 10 * (1 + coreN r) * (r + 1) := by ring
  have e2 : 4 * (1 + coreN r) * (5 * (r + 1)) = 20 * (1 + coreN r) * (r + 1) := by ring
  have e3 : 30 * (1 + coreN r) * (r + 1)
      = 20 * (1 + coreN r) * (r + 1) + 10 * (1 + coreN r) * (r + 1) := by ring
  refine ⟨h2, by omega, by omega⟩

/-! #### The charged index over the support covers -/

/-- The blocks (level, index) covering the support of root action `a`. -/
def coreCov (r : ℕ) (a : Fin (r + 1)) : Finset (ℕ × ℕ) :=
  (dualCompile (coreN r) (r ^ 2 + r + 1) (coreRunList r a)).1.1.toFinset

/-- Reverse-incidence list of a block: the root actions subscribed to it. -/
def coreSubs (r : ℕ) (d : ℕ × ℕ) : List (Fin (r + 1)) :=
  (univ.filter (fun a => d ∈ coreCov r a)).toList

theorem coreCov_blk_mem {r : ℕ} {a : Fin (r + 1)} {d : ℕ × ℕ} (hd : d ∈ coreCov r a) :
    blk d ∈ ((dualCompile (coreN r) (r ^ 2 + r + 1) (coreRunList r a)).1.1.map blk).toFinset :=
  List.mem_toFinset.mpr (List.mem_map_of_mem (List.mem_toFinset.mp hd))

/-- Two blocks of one support cover that contain the same position have the same level
(the blocks of a cover are pairwise disjoint). -/
theorem coreCov_one (r : ℕ) [NeZero r] (p : ℕ) (a : Fin (r + 1)) (d d' : ℕ × ℕ)
    (hd : d ∈ coreCov r a) (hd' : d' ∈ coreCov r a) (hp : p ∈ blk d) (hp' : p ∈ blk d') :
    d.1 = d'.1 := by
  by_contra hne
  have hC := ((core_cover_compile r).1 a).1
  have hbne : blk d ≠ blk d' := by
    intro e
    have := congrArg Finset.card e
    rw [ccBlk_card, ccBlk_card] at this
    exact hne (Nat.pow_right_injective (le_refl 2) this)
  exact Finset.disjoint_left.mp
    (hC.pairwiseDisjoint _ (coreCov_blk_mem hd) _ (coreCov_blk_mem hd') hbne) hp hp'

theorem coreCov_lev (r : ℕ) [NeZero r] (a : Fin (r + 1)) (d : ℕ × ℕ) (hd : d ∈ coreCov r a) :
    d.1 ≤ coreN r := by
  have hC := ((core_cover_compile r).1 a).1
  have hsub : blk d ⊆ range (2 ^ coreN r) :=
    (hC.subset (coreCov_blk_mem hd)).trans ((layoutPos_subset _ _).trans
      (range_subset_range.mpr (Nat.le_pow_clog (by norm_num) _)))
  exact (dyadicBlock_node hsub).1

theorem coreCov_card_le (r : ℕ) [NeZero r] (a : Fin (r + 1)) :
    (coreCov r a).card ≤ 4 * coreN r + 2 := by
  have h1 : (coreCov r a).card ≤ (coverRuns (coreN r) (coreRunList r a)).1.length :=
    List.toFinset_card_le _
  have h2 := coverRuns_length (coreN r) (coreRunList r a)
  have h3 := (coreRunList_spec r a).2.2
  have h4 : (coreRunList r a).length * (2 * coreN r + 1) ≤ 2 * (2 * coreN r + 1) :=
    Nat.mul_le_mul_right _ h3
  omega

theorem coreSubs_nodup (r : ℕ) (d : ℕ × ℕ) : (coreSubs r d).Nodup := Finset.nodup_toList _

theorem mem_coreSubs {r : ℕ} {d : ℕ × ℕ} {a : Fin (r + 1)} :
    a ∈ coreSubs r d ↔ d ∈ coreCov r a := by
  unfold coreSubs
  rw [Finset.mem_toList, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- **The covers index returns the exact support maxima.**  Whenever the invariant of the
charged index holds for leaf values `f` (it is preserved by every run of updates,
`dcRun_inv`), the root summary of action `a` is the maximum of `f` over the positions of the
support of `a`: the same root-action endpoint as the graph monitors store. -/
theorem coreCov_root_eq (r : ℕ) [NeZero r] {α : Type*} [LinearOrder α] [OrderBot α]
    {f : ℕ → α} {s : DCState (Fin (r + 1)) α} (h : DCInv (coreN r) (coreCov r) f s)
    (a : Fin (r + 1)) : s.root a = (layoutPos (coreLayout r) (coreSupp r a)).sup f := by
  rw [h.root_eq (coreCov_lev r) a]
  congr 1
  exact biUnion_blk_of_cover ((core_cover_compile r).1 a).1

/-- Invariant preservation for the common-core covers index along any run of updates. -/
theorem coreCov_run_inv (r : ℕ) [NeZero r] {α : Type*} [LinearOrder α] [OrderBot α]
    (us : List (ℕ × α)) (f : ℕ → α) (s : DCState (Fin (r + 1)) α)
    (h : DCInv (coreN r) (coreCov r) f s) :
    DCInv (coreN r) (coreCov r) (us.foldl (fun f u => Function.update f u.1 u.2) f)
      (dcRun (coreN r) (coreCov r) (coreSubs r) (fun a => (coreCov r a).card) (r + 1) us s).1 :=
  dcRun_inv _ _ _ _ _ (fun _ _ hd => mem_coreSubs.mpr hd) (coreCov_lev r) us f s h

/-- Work of the dyadic-cover monitor on the common-core family: compiling the dual covers of
all root supports, initializing the two endpoint indexes (segment tree and heap keys, one
unit per cell, charged by definition), and running the update lists `usL` (lower endpoints)
and `usU` (upper endpoints) through the charged index over the support covers. -/
def coreCoverWork (r : ℕ) {α : Type*} [LinearOrder α] [OrderBot α] (usL usU : List (ℕ × α))
    (sL sU : DCState (Fin (r + 1)) α) : ℕ :=
  (compileAll (coreN r) (r ^ 2 + r + 1) ((List.finRange (r + 1)).map (coreRunList r))).2
    + 2 * (2 ^ (coreN r + 1) + incidences (compileAll (coreN r) (r ^ 2 + r + 1)
        ((List.finRange (r + 1)).map (coreRunList r))).1)
    + (dcRun (coreN r) (coreCov r) (coreSubs r) (fun a => (coreCov r a).card) (r + 1) usL sL).2
    + (dcRun (coreN r) (coreCov r) (coreSubs r) (fun a => (coreCov r a).card) (r + 1) usU sU).2

/-- **`thm:ta-core`, dyadic-cover clause: work.**  For any update lists and initial states,
`W_covers ≤ 50 (n + 1) (r + 1) + 8 (r² + r + 1) + (|usL| + |usU|) · 5 (n + 1) (r + 2)`. -/
theorem coreCoverWork_le (r : ℕ) [NeZero r] {α : Type*} [LinearOrder α] [OrderBot α]
    (usL usU : List (ℕ × α)) (sL sU : DCState (Fin (r + 1)) α) :
    coreCoverWork r usL usU sL sU ≤ 50 * (coreN r + 1) * (r + 1) + 8 * (r ^ 2 + r + 1)
      + (usL.length + usU.length) * (5 * (coreN r + 1) * (r + 2)) := by
  obtain ⟨-, hinc, hcomp⟩ := core_cover_compile r
  have hrun : ∀ (us : List (ℕ × α)) (s : DCState (Fin (r + 1)) α),
      (dcRun (coreN r) (coreCov r) (coreSubs r) (fun a => (coreCov r a).card) (r + 1) us s).2
        ≤ us.length * (5 * (coreN r + 1) * (r + 2)) := by
    intro us s
    have h := dcRun_cover_bound (coreN r) (coreCov r) (coreSubs r)
      (fun a => (coreCov r a).card) (r + 1) (4 * coreN r + 2) (coreSubs_nodup r)
      (fun d a ha => mem_coreSubs.mp ha) (coreCov_one r) (coreCov_card_le r) us s
    rw [Fintype.card_fin] at h
    have c1 : Nat.clog 2 (4 * coreN r + 2) ≤ 4 * coreN r + 2 :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    have c2 : Nat.clog 2 (r + 1) ≤ coreN r := Nat.clog_mono_right 2 (by nlinarith)
    have c3 : 2 * (coreN r + 1)
          + (r + 1) * (Nat.clog 2 (4 * coreN r + 2) + Nat.clog 2 (r + 1) + 2)
        ≤ 5 * (coreN r + 1) * (r + 2) := by
      have : (r + 1) * (Nat.clog 2 (4 * coreN r + 2) + Nat.clog 2 (r + 1) + 2)
          ≤ (r + 1) * (5 * coreN r + 4) := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    exact h.trans (Nat.mul_le_mul_left _ c3)
  have hL := hrun usL sL
  have hU := hrun usU sU
  have htree : 2 ^ (coreN r + 1) ≤ 4 * (r ^ 2 + r + 1) := by
    have := segTree_nodes_lt (r ^ 2 + r + 1) (by omega)
    unfold coreN
    omega
  unfold coreCoverWork
  have e1 : (usL.length + usU.length) * (5 * (coreN r + 1) * (r + 2))
      = usL.length * (5 * (coreN r + 1) * (r + 2))
        + usU.length * (5 * (coreN r + 1) * (r + 2)) := by ring
  have e2 : 50 * (coreN r + 1) * (r + 1)
      = 30 * (1 + coreN r) * (r + 1) + 2 * (10 * (1 + coreN r) * (r + 1)) := by ring
  omega

/-- `⌈log₂ (r² + r + 1)⌉ + 1 ≤ 12 log r` for `r ≥ 2`. -/
theorem coreN_le_log {r : ℕ} (hr : 2 ≤ r) : ((coreN r : ℕ) : ℝ) + 1 ≤ 12 * Real.log r := by
  have h := monClog_le_log (m := r ^ 2 + r + 1) (by omega)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have h2 : Real.log (2 * ((r ^ 2 + r + 1 : ℕ) : ℝ)) ≤ Real.log ((r : ℝ) ^ 4) := by
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg (r : ℝ))]
  rw [Real.log_pow] at h2
  push_cast at h
  push_cast at h2
  unfold coreN
  linarith

/-- **Theorem `thm:ta-core`, all clauses.**  Fix `δ ∈ (0, 1)`.  There are constants
`A, B, C` such that for every `r ≥ 2` and every UCT search (`c = 2`, any tie-breaking, any
path rule below the root) on the common-core DAG with `r + 1` root actions and the Hoeffding
boxes for its `r² + r + 1` terminals there is a step `τ` with:

* both the selective and the eager graph monitor stop at `τ` and not before, recommending
  the winning action;
* `r + 1 + τ ≤ A r log r`;
* the total work of either graph monitor is at most `B r² log r`;
* the flat supports of the losing actions have total size at least `r³`;
* under the contiguous layout, the dual-cover compiler returns dyadic covers of every root
  support and of its complement, and the work of the dyadic-cover monitor (compile,
  initialization, and the charged index for the two endpoints) on any update lists of at
  most `r + 1 + τ` updates each, from any initial states, is at most `C r² log² r`.

The index invariant along such a run, and with it the equality of every root summary with
the maximum over the support, is `coreCov_run_inv` and `coreCov_root_eq`.  The equivalence
of the two graph monitors' tests at every step and the exactness of their stored intervals
are in `ta_core_coupled`. -/
theorem ta_core_full {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin (r + 1)) (zt : ℕ → CoreZ r),
      CoreSearch r rule sel zt →
        ∃ τ : ℕ,
          (∀ s : Bool, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
            (coreBox r (coreRadius r δ) zt τ) (Fin.last r)) ∧
          (∀ (s : Bool) k, k < τ → ∀ a,
            ¬ coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
          ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
          (∀ s : Bool, (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ B * (r : ℝ) ^ 2 * Real.log r) ∧
          r ^ 3 ≤ ∑ i : Fin r, (coreLoseSupp r i).card ∧
          (∀ a, IsDyadicCover
              ((dualCompile (coreN r) (r ^ 2 + r + 1) (coreRunList r a)).1.1.map blk).toFinset
              (layoutPos (coreLayout r) (coreSupp r a)) ∧
            IsDyadicCover
              ((dualCompile (coreN r) (r ^ 2 + r + 1) (coreRunList r a)).1.2.map blk).toFinset
              (layoutPos (coreLayout r) (coreSupp r a)ᶜ)) ∧
          ∀ (α : Type) [LinearOrder α] [OrderBot α] (usL usU : List (ℕ × α))
            (sL sU : DCState (Fin (r + 1)) α),
            usL.length ≤ r + 1 + τ → usU.length ≤ r + 1 + τ →
            (coreCoverWork r usL usU sL sU : ℝ) ≤ C * (r : ℝ) ^ 2 * Real.log r ^ 2 := by
  obtain ⟨A, B, hA, hB, H⟩ := ta_core_coupled hδ0 hδ1
  refine ⟨A, B, 240 * A + 940, hA, hB, by linarith, ?_⟩
  intro r _ hr rule sel zt h
  obtain ⟨-, -, τ, f1, f2, -, f4, f5, f6⟩ := H r hr rule sel zt h
  refine ⟨τ, f1, f2, f4, f5, f6, (core_cover_compile r).1, ?_⟩
  intro α _ _ usL usU sL sU hLlen hUlen
  have hW := coreCoverWork_le r usL usU sL sU
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log r := ⟨_, rfl⟩
  have hN := coreN_le_log hr
  rw [← hℓ] at hN f4 ⊢
  have hℓ69 : (0.69 : ℝ) ≤ ℓ := by
    have h1 : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hrR
    have h2 := Real.log_two_gt_d9
    rw [hℓ]
    linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (coreN r : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = (usL.length : ℝ) + usU.length := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ((r + 1 + τ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hTdef] at f4
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hS : S ≤ 2 * T := by
    have h1 : (usL.length : ℝ) ≤ T := by rw [hTdef]; exact_mod_cast hLlen
    have h2 : (usU.length : ℝ) ≤ T := by rw [hTdef]; exact_mod_cast hUlen
    rw [hSdef]
    linarith
  have hWR : (coreCoverWork r usL usU sL sU : ℝ)
      ≤ 50 * N * (r + 1) + 8 * ((r : ℝ) ^ 2 + r + 1) + S * (5 * N * (r + 2)) := by
    rw [hNdef, hSdef]
    exact_mod_cast hW
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hp : 1 ≤ (r : ℝ) * ℓ := by nlinarith
  have hp2 : (r : ℝ) * ℓ ≤ ((r : ℝ) * ℓ) ^ 2 := by nlinarith
  have a1 : N * ((r : ℝ) + 1) ≤ 12 * ℓ * (3 / 2 * r) :=
    mul_le_mul hN (by linarith) (by linarith) (by linarith)
  have a2 : N * ((r : ℝ) + 2) ≤ 12 * ℓ * (2 * r) :=
    mul_le_mul hN (by linarith) (by linarith) (by linarith)
  have hℓ2 : (0.47 : ℝ) ≤ ℓ ^ 2 := by nlinarith
  have a3 : 8 * ((r : ℝ) ^ 2 + r + 1) ≤ 40 * ((r : ℝ) ^ 2 * ℓ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hℓ2 (sq_nonneg (r : ℝ))]
  have a4 : S * (5 * N * (r + 2)) ≤ 2 * T * (120 * (ℓ * r)) := by
    refine mul_le_mul hS ?_ (by nlinarith [mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ (r : ℝ) + 2)])
      (by linarith)
    nlinarith
  have a5 : T * (ℓ * r) ≤ A * r * ℓ * (ℓ * r) :=
    mul_le_mul_of_nonneg_right f4 (by nlinarith)
  have e : (240 * A + 940) * (r : ℝ) ^ 2 * ℓ ^ 2
      = 240 * (A * r * ℓ * (ℓ * r)) + 900 * ((r : ℝ) * ℓ) ^ 2 + 40 * ((r : ℝ) ^ 2 * ℓ ^ 2) := by
    ring
  nlinarith

end Covers

end

end JointRootCert
