/-
Proposition `prop:v34-work` (Global solver-call reduction under sparse refreshes and
action-local evidence), with operational call counts.

`LiteralD2b.designWork` and `LiteralD2b.nullWork` are counting formulas.  Here the tracker of
`thm:v34-adaptive` (`Tracker.step`, with its four-power refresh schedule, sticky incumbent rule,
allocation and action-local wealth/test) is re-implemented as a costed program that accesses the
design oracle and the component-null oracle only through call primitives carrying a counter:

* `designCall k m v a` returns the oracle's pair `(w_a^k, Ĉ_a^k)` and costs one design call;
* `nullCall a z i r μ̂ v̂ y` returns the certified null bound `Û_{a,z}` and costs one null call;
* `mapCall f l` runs `f` on every element of the list `l` and adds up the costs.

`cstep` is one batch: if the refresh schedule fires it queries `designCall` once for each root
action (the list `univ.toList`), builds the score and design table from the answers only, applies
the sticky rule to the table, and deploys the tabled design of the chosen action; it then
allocates the batch, queries `nullCall` once for each component of `J(A_j)` of the selected
action, and updates that action's component wealths from the answers.  `crun j` runs `j`
batches from the initial state; `ctest` is the stopping test evaluated on the program's own
wealth table.  The counters `dc`, `nc` are produced by execution.

Results.
* `crun_st`, `crun_wl`, `ctest_iff`: the program's state equals `Tracker.state`, its wealths
  equal `Tracker.wealth` on the components of each action, and its test is `Tracker.test`.
* `cStops_iff`, `cStopBatch_eq`, `cReturned_eq`, `cTau_eq`: its stopping event, stopping batch,
  returned action and stopping time are those of `LiteralD2c`, so `v34_adaptive_costed`
  (the conclusions of `LiteralD2c.v34_adaptive_literal`) holds for it.
* `crun_dc`: design calls through batch `j ≥ 1` equal `K (1 + ⌊log₄ j⌋)`;
  `crun_nc`, `crun_nc_le`: null calls through batch `j` equal `∑_{i ≤ j} |J(A_i)| ≤ J_max j`.
* `v34_work_full`: the proposition with these operational counts at stopping and the
  expectation bounds of `LiteralD2e.v34_work_inst` (instance constant `cWork`).
-/
import JointRootCert.LiteralD2e

namespace JointRootCert

namespace LiteralF7

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ### Costed computations -/

/-- A value together with the number of design-oracle calls `dc` and component-null-oracle
calls `nc` made to produce it. -/
structure Costed (α : Type*) where
  val : α
  dc : ℕ
  nc : ℕ

/-- Run `f` on each element of a list, returning the answers keyed by the element and the
total cost. -/
def mapCall {α β : Type*} (f : α → Costed β) : List α → Costed (List (α × β))
  | [] => ⟨[], 0, 0⟩
  | a :: t => ⟨(a, (f a).val) :: (mapCall f t).val, (f a).dc + (mapCall f t).dc,
      (f a).nc + (mapCall f t).nc⟩

lemma mapCall_val {α β : Type*} (f : α → Costed β) (l : List α) :
    (mapCall f l).val = l.map fun a => (a, (f a).val) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [mapCall, ih]

lemma mapCall_dc {α β : Type*} (f : α → Costed β) {d : ℕ} (h : ∀ a, (f a).dc = d)
    (l : List α) : (mapCall f l).dc = d * l.length := by
  induction l with
  | nil => simp [mapCall]
  | cons a t ih => simp only [mapCall, ih, h, List.length_cons]; ring

lemma mapCall_nc {α β : Type*} (f : α → Costed β) {n : ℕ} (h : ∀ a, (f a).nc = n)
    (l : List α) : (mapCall f l).nc = n * l.length := by
  induction l with
  | nil => simp [mapCall]
  | cons a t ih => simp only [mapCall, ih, h, List.length_cons]; ring

/-- Lookup in an answer table (first matching key; default `d`). -/
def lookup {α β : Type*} [DecidableEq α] (d : β) : List (α × β) → α → β
  | [], _ => d
  | p :: t, a => if p.1 = a then p.2 else lookup d t a

lemma lookup_map {α β : Type*} [DecidableEq α] (g : α → β) (d : β) {l : List α} {a : α}
    (h : a ∈ l) : lookup d (l.map fun b => (b, g b)) a = g a := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [List.map_cons, lookup]
    by_cases hb : b = a
    · subst hb; simp
    · rw [ite_eq_right hb]
      exact ih ((List.mem_cons.mp h).resolve_left (Ne.symm hb))

/-! ### The costed tracker -/

variable {X A Z U : Type*}

/-- The program state: the tracker state, the component wealth table, and the two call
counters. -/
structure CState (X A Z : Type*) where
  st : TState X A
  wl : A → Z → ℝ
  dc : ℕ
  nc : ℕ

variable (T : Tracker X A Z U)

/-- One certified design-game call for action `a` at refresh `k`: returns the design and the
displayed score; costs one design call. -/
def designCall (k : ℕ) (m v : X → ℝ) (a : A) : Costed ((X → ℝ) × ℝ) :=
  ⟨(T.design k m v a, T.score k m v a), 1, 0⟩

/-- One component-null likelihood solve for `(a, z)` at batch `i`: returns the certified upper
bound `Û_{a,z}`; costs one null call. -/
def nullCall (a : A) (z : Z) (i : ℕ) (r : X → ℕ) (mh vh : X → ℝ) (yb : X → ℕ → ℝ) :
    Costed ℝ :=
  ⟨T.Uhi a z i r mh vh yb, 0, 1⟩

variable [Fintype A] [DecidableEq A]

/-- A refresh at index `k`: call the design oracle once for every root action, then choose the
incumbent by the sticky rule applied to the returned scores, and deploy the returned design of
the chosen action.  Only the answer table is used. -/
def refreshPhase (k : ℕ) (mh vh : X → ℝ) (inc : A) : Costed (A × (X → ℝ)) :=
  let r := mapCall (designCall T k mh vh) (Finset.univ : Finset A).toList
  let sc : A → ℝ := fun b => (lookup ((fun _ => 0), 0) r.val b).2
  let inc' := if ∀ b, sc b - sc inc ≤ hyst k then inc else T.pick sc
  ⟨(inc', (lookup ((fun _ => 0), 0) r.val inc').1), r.dc, r.nc⟩

/-- The design phase of batch `j + 1`: a refresh exactly when the schedule fires, otherwise
keep the incumbent and its design at no cost. -/
def designPhase (y : X → ℕ → ℝ) (j : ℕ) (s : TState X A) : Costed (A × (X → ℝ)) :=
  if 4 ^ Nat.log 4 (j + 1) = j + 1 then
    refreshPhase T (Nat.log 4 (j + 1)) (fun x => predMean (y x) (s.cnt x))
      (fun x => predVar (j + 1) (y x) (s.cnt x)) s.inc
  else ⟨(s.inc, s.w), 0, 0⟩

variable [DecidableEq Z]

/-- One batch `j + 1` of the costed tracker: design phase, allocation, one null call per
component of the selected action, and the update of that action's component wealths. -/
def cstep (y : X → ℕ → ℝ) (j : ℕ) (c : CState X A Z) : CState X A Z :=
  let s := c.st
  let mh : X → ℝ := fun x => predMean (y x) (s.cnt x)
  let vh : X → ℝ := fun x => predVar (j + 1) (y x) (s.cnt x)
  let d := designPhase T y j s
  let r := T.alloc (j + 1) d.val.2
  let yb : X → ℕ → ℝ := fun x ℓ => y x (s.cnt x + ℓ)
  let q := T.qlo (j + 1) r mh vh yb
  let nl := mapCall (fun z => nullCall T d.val.1 z (j + 1) r mh vh yb) (T.J d.val.1).toList
  { st := ⟨fun x => s.cnt x + r x, d.val.1, d.val.2⟩
    wl := fun a z => if a = d.val.1 ∧ z ∈ T.J d.val.1 then
      c.wl a z * halfCash q (lookup 0 nl.val z) else c.wl a z
    dc := c.dc + d.dc + nl.dc
    nc := c.nc + d.nc + nl.nc }

/-- The costed tracker after `j` batches. -/
def crun (y : X → ℕ → ℝ) : ℕ → CState X A Z
  | 0 => ⟨⟨fun _ => 0, T.init, fun _ => 0⟩, fun _ _ => 1, 0, 0⟩
  | j + 1 => cstep T y j (crun y j)

/-- The stopping test evaluated on the program's wealth table. -/
def ctest (y : X → ℕ → ℝ) (δ : ℝ) (j : ℕ) : Prop :=
  ∀ z ∈ T.J (crun T y j).st.inc, (Fintype.card A : ℝ) / δ ≤ (crun T y j).wl (crun T y j).st.inc z

/-! ### The program computes the tracker -/

variable (y : X → ℕ → ℝ)

omit [DecidableEq Z] in
lemma refreshPhase_val (k : ℕ) (mh vh : X → ℝ) (inc : A) :
    (refreshPhase T k mh vh inc).val =
      (T.refInc k mh vh inc, T.design k mh vh (T.refInc k mh vh inc)) := by
  have hl : ∀ b, lookup ((fun _ => 0), 0)
      (mapCall (designCall T k mh vh) (Finset.univ : Finset A).toList).val b =
      (T.design k mh vh b, T.score k mh vh b) := by
    intro b
    rw [mapCall_val]
    exact lookup_map (fun a => (designCall T k mh vh a).val) _ (Finset.mem_toList.mpr
      (Finset.mem_univ b))
  simp only [refreshPhase, hl]
  unfold Tracker.refInc
  by_cases h : ∀ b, T.score k mh vh b - T.score k mh vh inc ≤ hyst k
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

omit [DecidableEq Z] in
lemma refreshPhase_dc (k : ℕ) (mh vh : X → ℝ) (inc : A) :
    (refreshPhase T k mh vh inc).dc = Fintype.card A := by
  simp only [refreshPhase]
  rw [mapCall_dc _ (d := 1) (fun _ => rfl), Finset.length_toList, one_mul, Finset.card_univ]

omit [DecidableEq Z] in
lemma refreshPhase_nc (k : ℕ) (mh vh : X → ℝ) (inc : A) :
    (refreshPhase T k mh vh inc).nc = 0 := by
  simp only [refreshPhase]
  rw [mapCall_nc _ (n := 0) (fun _ => rfl), zero_mul]

omit [DecidableEq Z] in
/-- The design phase returns the incumbent and design of `Tracker.step`. -/
lemma designPhase_val (j : ℕ) (s : TState X A) :
    (designPhase T y j s).val = ((T.step y j s).inc, (T.step y j s).w) := by
  unfold designPhase Tracker.step
  by_cases h : 4 ^ Nat.log 4 (j + 1) = j + 1
  · rw [ite_eq_left h, ite_eq_left h, refreshPhase_val]
  · rw [ite_eq_right h, ite_eq_right h]

omit [DecidableEq Z] in
lemma designPhase_dc (j : ℕ) (s : TState X A) :
    (designPhase T y j s).dc = if 4 ^ Nat.log 4 (j + 1) = j + 1 then Fintype.card A else 0 := by
  unfold designPhase
  split_ifs
  · exact refreshPhase_dc T _ _ _ _
  · rfl

omit [DecidableEq Z] in
lemma designPhase_nc (j : ℕ) (s : TState X A) : (designPhase T y j s).nc = 0 := by
  unfold designPhase
  split_ifs
  · exact refreshPhase_nc T _ _ _ _
  · rfl

/-- **The program's tracker state is `Tracker.state`.** -/
theorem crun_st (j : ℕ) : (crun T y j).st = T.state y j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hd := designPhase_val T y j (T.state y j)
    show (cstep T y j (crun T y j)).st = T.step y j (T.state y j)
    simp only [cstep, ih, hd]
    have e : T.step y j (T.state y j) = ⟨(T.step y j (T.state y j)).cnt,
        (T.step y j (T.state y j)).inc, (T.step y j (T.state y j)).w⟩ := rfl
    rw [e]
    congr 1
    funext x
    exact (T.step_cnt y j (T.state y j) x).symm

lemma crun_inc (j : ℕ) : (crun T y j).st.inc = T.sel y j := by
  rw [crun_st]; rfl

/-- **The program's component wealths are the tracker's action-local wealths.** -/
theorem crun_wl (j : ℕ) (a : A) {z : Z} (hz : z ∈ T.J a) :
    (crun T y j).wl a z = T.wealth y a z j := by
  induction j with
  | zero => simp [crun, Tracker.wealth]
  | succ j ih =>
    have hd := designPhase_val T y j (T.state y j)
    have hsel : T.sel y (j + 1) = (T.step y j (T.state y j)).inc := rfl
    show (cstep T y j (crun T y j)).wl a z = T.wealth y a z (j + 1)
    unfold Tracker.wealth
    rw [localWealth_succ]
    simp only [cstep, crun_st, hd]
    rw [← Tracker.wealth, ← ih, ← hsel]
    by_cases ha : a = T.sel y (j + 1)
    · subst ha
      have hz' : z ∈ (T.J (T.sel y (j + 1))).toList := Finset.mem_toList.mpr hz
      rw [ite_eq_left ⟨rfl, hz⟩, ite_eq_left rfl, mapCall_val,
        lookup_map (fun z => (nullCall T _ z (j + 1) _ _ _ _).val) 0 hz']
      rfl
    · rw [ite_eq_right (fun h => ha h.1), ite_eq_right (Ne.symm ha), mul_one]

/-- **The program's test is the tracker's stopping test.** -/
theorem ctest_iff (δ : ℝ) (j : ℕ) : ctest T y δ j ↔ T.test y δ j := by
  unfold ctest Tracker.test
  rw [crun_inc]
  constructor
  · intro h z hz
    rw [← crun_wl T y j _ hz]
    exact h z hz
  · intro h z hz
    rw [crun_wl T y j _ hz]
    exact h z hz

/-! ### The call counters -/

lemma refreshCount_succ (j : ℕ) :
    LiteralD2b.refreshCount (j + 1) =
      LiteralD2b.refreshCount j + if 4 ^ Nat.log 4 (j + 1) = j + 1 then 1 else 0 := by
  unfold LiteralD2b.refreshCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_Icc_succ_top (by omega)]

/-- Design calls made by the program through batch `j`: `K` times the number of refreshes. -/
theorem crun_dc_eq (j : ℕ) :
    (crun T y j).dc = LiteralD2b.designWork (Fintype.card A) j := by
  induction j with
  | zero => simp [crun, LiteralD2b.designWork, LiteralD2b.refreshCount]
  | succ j ih =>
    show (cstep T y j (crun T y j)).dc = _
    simp only [cstep]
    rw [ih, designPhase_dc, mapCall_dc _ (d := 0) (fun _ => rfl), zero_mul, add_zero,
      LiteralD2b.designWork, LiteralD2b.designWork, refreshCount_succ, mul_add]
    split_ifs <;> simp

/-- **`W_design(j) = K (1 + ⌊log₄ j⌋)`** for the program's own counter, `j ≥ 1`. -/
theorem crun_dc {j : ℕ} (hj : 1 ≤ j) :
    (crun T y j).dc = Fintype.card A * (1 + Nat.log 4 j) := by
  rw [crun_dc_eq, LiteralD2b.designWork_eq _ hj]

/-- Null calls made by the program through batch `j`: `∑_{i ≤ j} |J(A_i)|`. -/
theorem crun_nc (j : ℕ) : (crun T y j).nc = LiteralD2b.nullWork T y j := by
  induction j with
  | zero => simp [crun, LiteralD2b.nullWork]
  | succ j ih =>
    have hd := designPhase_val T y j (T.state y j)
    have hsel : T.sel y (j + 1) = (T.step y j (T.state y j)).inc := rfl
    show (cstep T y j (crun T y j)).nc = _
    simp only [cstep]
    rw [ih, designPhase_nc, mapCall_nc _ (n := 1) (fun _ => rfl), one_mul, add_zero,
      Finset.length_toList, crun_st, hd, ← hsel, LiteralD2b.nullWork, LiteralD2b.nullWork,
      Finset.sum_Icc_succ_top (by omega)]

/-- **`W_null(j) ≤ J_max j`** for the program's own counter. -/
theorem crun_nc_le {Jmax : ℕ} (hJ : ∀ a, (T.J a).card ≤ Jmax) (j : ℕ) :
    (crun T y j).nc ≤ Jmax * j := by
  rw [crun_nc]
  exact LiteralD2b.nullWork_le T y hJ j

/-! ### Stopping of the program -/

variable (δ : ℝ)

/-- The program stops: its test passes at some completed batch. -/
def CStops : Prop := ∃ j, 1 ≤ j ∧ ctest T y δ j

open Classical in
/-- The program's stopping batch (`0` if it never stops). -/
def cStopBatch : ℕ := if h : CStops T y δ then Nat.find h else 0

/-- The action the program returns: its incumbent at the stopping batch. -/
def cReturned : A := (crun T y (cStopBatch T y δ)).st.inc

open Classical in
/-- The program's stopping time in observations (`∞` if it never stops): the total count of
observations in its state at the stopping batch. -/
def cTau [Fintype X] : ℝ≥0∞ :=
  if CStops T y δ then ((∑ x, (crun T y (cStopBatch T y δ)).st.cnt x : ℕ) : ℝ≥0∞) else ⊤

open Classical in
/-- The program's batch index at stopping (`∞` if it never stops). -/
def cStopIdx : ℝ≥0∞ := if h : CStops T y δ then ((Nat.find h : ℕ) : ℝ≥0∞) else ⊤

open Classical in
/-- Design calls the program has made when it stops (`∞` if it never stops). -/
def cDesignStop : ℝ≥0∞ := if h : CStops T y δ then (((crun T y (Nat.find h)).dc : ℕ) : ℝ≥0∞)
  else ⊤

open Classical in
/-- Null calls the program has made when it stops (`∞` if it never stops). -/
def cNullStop : ℝ≥0∞ := if h : CStops T y δ then (((crun T y (Nat.find h)).nc : ℕ) : ℝ≥0∞)
  else ⊤

lemma find_congr {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (hp : ∃ n, p n)
    (hq : ∃ n, q n) (h : ∀ n, p n ↔ q n) : Nat.find hp = Nat.find hq :=
  le_antisymm (Nat.find_min' hp ((h _).mpr (Nat.find_spec hq)))
    (Nat.find_min' hq ((h _).mp (Nat.find_spec hp)))

lemma cStops_iff : CStops T y δ ↔ LiteralD2c.Stops T y δ := by
  unfold CStops LiteralD2c.Stops
  simp only [ctest_iff]

lemma cStops_iff_b : CStops T y δ ↔ LiteralD2b.Stops T y δ := by
  unfold CStops LiteralD2b.Stops
  simp only [ctest_iff]

/-- The program stops at the tracker's stopping batch. -/
theorem cStopBatch_eq : cStopBatch T y δ = LiteralD2c.stopBatch T y δ := by
  classical
  unfold cStopBatch LiteralD2c.stopBatch
  by_cases h : CStops T y δ
  · have h' := (cStops_iff T y δ).mp h
    rw [dite_eq_left h, dite_eq_left h']
    exact find_congr _ _ fun n => and_congr Iff.rfl (ctest_iff T y δ n)
  · have h' : ¬ LiteralD2c.Stops T y δ := fun h' => h ((cStops_iff T y δ).mpr h')
    rw [dite_eq_right h, dite_eq_right h']

/-- The program returns the tracker's returned action. -/
theorem cReturned_eq : cReturned T y δ = LiteralD2c.returned T y δ := by
  unfold cReturned LiteralD2c.returned
  rw [crun_inc, cStopBatch_eq]

/-- The program's stopping time (observations consumed) is the tracker's `τ_δ`, for a
tracker meeting the oracle contracts. -/
theorem cTau_eq [Fintype X] (hc : T.Contract) : cTau T y δ = LiteralD2c.tau T y δ := by
  classical
  unfold cTau LiteralD2c.tau
  by_cases h : CStops T y δ
  · have h' := (cStops_iff T y δ).mp h
    rw [ite_eq_left h, ite_eq_left h', crun_st, cStopBatch_eq, ← LiteralD2c.tau_eq_sum_cnt T y δ hc h']
    have e : LiteralD2c.tau T y δ =
        ((cumN (Fintype.card X) (LiteralD2c.stopBatch T y δ) : ℕ) : ℝ≥0∞) := by
      unfold LiteralD2c.tau; rw [ite_eq_left h']
    rw [e]
  · have h' : ¬ LiteralD2c.Stops T y δ := fun h' => h ((cStops_iff T y δ).mpr h')
    rw [ite_eq_right h, ite_eq_right h']

lemma cStopIdx_eq : cStopIdx T y δ = LiteralD2b.stopIdx T y δ := by
  classical
  unfold cStopIdx LiteralD2b.stopIdx
  by_cases h : CStops T y δ
  · have h' := (cStops_iff_b T y δ).mp h
    rw [dite_eq_left h, dite_eq_left h', find_congr (p := fun n => 1 ≤ n ∧ ctest T y δ n)
      (q := fun n => 1 ≤ n ∧ T.test y δ n) h h' fun n => and_congr Iff.rfl (ctest_iff T y δ n)]
  · have h' : ¬ LiteralD2b.Stops T y δ := fun h' => h ((cStops_iff_b T y δ).mpr h')
    rw [dite_eq_right h, dite_eq_right h']

/-- The design calls counted by the program at stopping equal `LiteralD2b.designWorkStop`. -/
lemma cDesignStop_eq : cDesignStop T y δ = LiteralD2b.designWorkStop (Fintype.card A) T y δ := by
  classical
  unfold cDesignStop LiteralD2b.designWorkStop
  by_cases h : CStops T y δ
  · have h' := (cStops_iff_b T y δ).mp h
    rw [dite_eq_left h, dite_eq_left h', find_congr (p := fun n => 1 ≤ n ∧ ctest T y δ n)
      (q := fun n => 1 ≤ n ∧ T.test y δ n) h h' fun n => and_congr Iff.rfl (ctest_iff T y δ n),
      crun_dc_eq]
  · have h' : ¬ LiteralD2b.Stops T y δ := fun h' => h ((cStops_iff_b T y δ).mpr h')
    rw [dite_eq_right h, dite_eq_right h']

/-- The null calls counted by the program at stopping equal `LiteralD2b.nullWorkStop`. -/
lemma cNullStop_eq : cNullStop T y δ = LiteralD2b.nullWorkStop T y δ := by
  classical
  unfold cNullStop LiteralD2b.nullWorkStop
  by_cases h : CStops T y δ
  · have h' := (cStops_iff_b T y δ).mp h
    rw [dite_eq_left h, dite_eq_left h', find_congr (p := fun n => 1 ≤ n ∧ ctest T y δ n)
      (q := fun n => 1 ≤ n ∧ T.test y δ n) h h' fun n => and_congr Iff.rfl (ctest_iff T y δ n),
      crun_nc]
  · have h' : ¬ LiteralD2b.Stops T y δ := fun h' => h ((cStops_iff_b T y δ).mpr h')
    rw [dite_eq_right h, dite_eq_right h']

/-! ### The theorems for the costed program -/

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] [Fintype X] [Nonempty X] [DecidableEq X] [Nonempty A]

/-- **`thm:v34-adaptive` for the costed program.**  The conclusions of
`LiteralD2c.v34_adaptive_literal`, stated for the program's stopping event `CStops`, returned
action `cReturned` and stopping time `cTau`, under the same hypotheses. -/
theorem v34_adaptive_costed (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas)
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P)
    (hC : 0 < (T.inst (fun x => T.pred x θ) v).Cstar) :
    (∀ δ : ℝ, 0 < δ →
      P {ω | CStops T (tapeOf Y ω) δ ∧ ∃ z ∈ T.J (cReturned T (tapeOf Y ω) δ),
          θ ∈ T.H (cReturned T (tapeOf Y ω) δ) z} ≤ ENNReal.ofReal δ ∧
      P {ω | ¬ CStops T (tapeOf Y ω) δ} = 0) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, cTau T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal ((T.inst (fun x => T.pred x θ) v).Ds s +
          (1 + s) / (T.inst (fun x => T.pred x θ) v).Cstar * Real.log (1 / δ))) ∧
    ∀ c : ℝ, 1 / (T.inst (fun x => T.pred x θ) v).Cstar < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, cTau T (tapeOf Y ω) δ ∂P).toReal ≤ c * Real.log (1 / δ) := by
  have h := LiteralD2c.v34_adaptive_literal T hc hm P hYm hind θ hv0 hlaw hC
  simp only [cStops_iff, cReturned_eq, cTau_eq _ _ _ hc]
  exact h

/-- **Proposition `prop:v34-work` with operational counts.**  `K = |A|`, `J_max` bounds
`|J_a|`, `L_δ = 1 + log (1 + log (1 / δ))`; `crun` is the costed tracker, whose counters `dc`
and `nc` count the design-oracle and component-null-oracle calls it executes.

1. On every tape, through batch `j ≥ 1` the program makes exactly `K (1 + ⌊log₄ j⌋)` design
   calls, and through batch `j` at most `J_max j` null calls.
2. Model of `LiteralD2c.v34_finite_confidence` (oracle contracts, Borel allocation oracles,
   measurable jointly independent tapes `Y x n ~ N(μₓ, vₓ)` with `vₓ > 0`, `C_* > 0`): for all
   `δ ∈ (0, 1)`, with the program's stopping batch index `cStopIdx` and its call counters at
   stopping `cDesignStop`, `cNullStop`,
   `E T_δ ≤ c (1 + L_δ²)`, `E W_design(T_δ) ≤ c K (1 + log (1 + L_δ))`,
   `E W_null(T_δ) ≤ c J_max (1 + L_δ²)`,
   with the instance constant `c = LiteralD2e.cWork (T.inst μ v)`.

Expectations are lower integrals of `[0, ∞]`-valued functions. -/
theorem v34_work_full (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas)
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {μ v : X → ℝ}
    (hv0 : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (μ x) (v x).toNNReal) P)
    (hC : 0 < (T.inst μ v).Cstar) {Jmax : ℕ} (hJmax : ∀ a, (T.J a).card ≤ Jmax) :
    (∀ (y : X → ℕ → ℝ) (j : ℕ), 1 ≤ j → (crun T y j).dc = Fintype.card A * (1 + Nat.log 4 j)) ∧
    (∀ (y : X → ℕ → ℝ) (j : ℕ), (crun T y j).nc ≤ Jmax * j) ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, cStopIdx T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal (LiteralD2e.cWork (T.inst μ v) * (1 + LiteralD2b.Ldelta δ ^ 2)) ∧
      ∫⁻ ω, cDesignStop T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal (LiteralD2e.cWork (T.inst μ v) *
          (Fintype.card A * (1 + Real.log (1 + LiteralD2b.Ldelta δ)))) ∧
      ∫⁻ ω, cNullStop T (tapeOf Y ω) δ ∂P ≤
        ENNReal.ofReal (LiteralD2e.cWork (T.inst μ v) *
          (Jmax * (1 + LiteralD2b.Ldelta δ ^ 2))) := by
  have h := (LiteralD2e.v34_work_inst T hc hm P hYm hind hv0 hlaw hC hJmax).2.2
  refine ⟨fun y j hj => crun_dc T y hj, fun y j => crun_nc_le T y hJmax j, fun δ hδ0 hδ1 => ?_⟩
  simp only [cStopIdx_eq, cDesignStop_eq, cNullStop_eq]
  exact h δ hδ0 hδ1

end Expect

end

end LiteralF7

end JointRootCert
