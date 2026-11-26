/-
A concrete instance of Theorem `thm:active-restart` (Certified restart bound).

`certified_restart_product` (Completions2) takes the episode procedure as data
(`selE`, `σE`, `obsE`, `recE`, `failE`) together with hypotheses on it.  Here the procedure is
defined explicitly, without any choice over histories:

* `lArg f d l`: the first maximiser of `f` on the list `d :: l` (left-to-right scan, strict
  improvement only).  Lists are `Finset.sort` of finite sets in a linear order, so ties go to
  the least element.
* `osPick`: one optimistic-separation step on a box `[l, u]`: the action `b` maximising the
  index `osIndex`, the optimistic inside witness `p` and outside witness `q` of `b`, and the
  wider of the two.
* `cnt`, `selR`: the run on an episode tape `x : Z × ℕ → ℝ`, with the running-intersection
  Hoeffding box of confidence `δ_j = δ / (j (j + 1))` built from the counts.
* `stopTime`: the first `t ≤ 2^j` at which some action has exact certificate `≤ ε`
  (`certAt`) or the box is empty at some terminal, `l z > u z` (`boxEmpty`, confidence
  failure), and `2^j + 1` if there is none (timeout).  `epObs = min σ 2^j`;
  `epFail = {2^j < σ} ∪ {box empty at σ}` (timeout or confidence failure, as in the restart
  wrapper of the manuscript); `epRec` the action of least certificate at the stopping time.

We prove that the stopping count, the number of observations, the queried terminals, the
recommendation and the failure set are measurable functions of the tape
(`epStop_measurable`, `epObs_measurable`, `epSel_measurableSet`, `epRec_measurableSet`,
`epFail_measurableSet`), that the procedure satisfies every hypothesis of
`certified_restart_product` for every `0 ≤ ε ≤ 1` with `Γ + ε > 0` (`ep_hobs`, `ep_hrule`,
`ep_hret`, `ep_hsucc`), and conclude `active_restart_instance`.
-/
import JointRootCert.Completions2

namespace JointRootCert
namespace LiteralF6

open Finset MeasureTheory
open scoped ENNReal

/-! ### First maximiser in a list -/

/-- `lArg f d l`: scan `d :: l` from the left, replacing the current element only on strict
improvement of `f`; the result is the first maximiser of `f` on `d :: l`. -/
noncomputable def lArg {α : Type*} (f : α → ℝ) : α → List α → α
  | d, [] => d
  | d, a :: l => lArg f (if f d < f a then a else d) l

lemma lArg_mem {α : Type*} (f : α → ℝ) :
    ∀ (d : α) (l : List α), lArg f d l = d ∨ lArg f d l ∈ l
  | d, [] => Or.inl rfl
  | d, a :: l => by
    have e : lArg f d (a :: l) = lArg f (if f d < f a then a else d) l := rfl
    rw [e]
    rcases lArg_mem f (if f d < f a then a else d) l with h | h
    · split_ifs at h ⊢ with hlt
      · rw [h]; exact Or.inr List.mem_cons_self
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

lemma lArg_ge {α : Type*} (f : α → ℝ) :
    ∀ (d : α) (l : List α), f d ≤ f (lArg f d l) ∧ ∀ a ∈ l, f a ≤ f (lArg f d l)
  | d, [] => ⟨le_rfl, fun a ha => by simp at ha⟩
  | d, a :: l => by
    obtain ⟨h1, h2⟩ := lArg_ge f (if f d < f a then a else d) l
    have e : lArg f d (a :: l) = lArg f (if f d < f a then a else d) l := rfl
    rw [e]
    have hd : f d ≤ f (if f d < f a then a else d) := by
      split_ifs with h
      · exact h.le
      · exact le_rfl
    have ha : f a ≤ f (if f d < f a then a else d) := by
      split_ifs with h
      · exact le_rfl
      · exact not_lt.mp h
    refine ⟨hd.trans h1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha.trans h1
    · exact h2 b hb

/-! ### Measurability of finite-valued selections -/

section Meas

variable {X : Type*} [MeasurableSpace X]

/-- Selection by a finite-valued (countable-valued) measurable index. -/
lemma measurableSet_sel {γ : Type*} [Countable γ] {d : X → γ}
    (hd : ∀ c, MeasurableSet {x | d x = c}) {P : γ → X → Prop}
    (hP : ∀ c, MeasurableSet {x | P c x}) : MeasurableSet {x | P (d x) x} := by
  have h : {x | P (d x) x} = ⋃ c, {x | d x = c} ∩ {x | P c x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨d x, rfl, h⟩, fun ⟨c, hc, h⟩ => by rwa [hc]⟩
  rw [h]
  exact MeasurableSet.iUnion fun c => (hd c).inter (hP c)

lemma measurableSet_ite_eq {β : Type*} {P : X → Prop} [DecidablePred P]
    (hP : MeasurableSet {x | P x}) {f g : X → β} (b : β) (hf : MeasurableSet {x | f x = b})
    (hg : MeasurableSet {x | g x = b}) :
    MeasurableSet {x | (if P x then f x else g x) = b} := by
  have h : {x | (if P x then f x else g x) = b} =
      ({x | P x} ∩ {x | f x = b}) ∪ ({x | P x}ᶜ ∩ {x | g x = b}) := by
    ext x
    by_cases hx : P x <;> simp [hx]
  rw [h]
  exact (hP.inter hf).union (hP.compl.inter hg)

lemma lArg_meas {α : Type*} [Countable α] {F : X → α → ℝ}
    (hF : ∀ a, Measurable fun x => F x a) :
    ∀ (l : List α) {d : X → α}, (∀ c, MeasurableSet {x | d x = c}) →
      ∀ c, MeasurableSet {x | lArg (F x) (d x) l = c}
  | [], d, hd => hd
  | a :: l, d, hd => by
    have e : ∀ x, lArg (F x) (d x) (a :: l) =
        lArg (F x) (if F x (d x) < F x a then a else d x) l := fun x => rfl
    simp only [e]
    refine lArg_meas hF l (d := fun x => if F x (d x) < F x a then a else d x) ?_
    intro c
    have hlt : MeasurableSet {x | F x (d x) < F x a} :=
      measurableSet_sel hd (P := fun b x => F x b < F x a)
        (fun b => measurableSet_lt (hF b) (hF a))
    exact measurableSet_ite_eq hlt c (MeasurableSet.const _) (hd c)

lemma measurable_sup'_apply {Z : Type*} {S : Finset Z} (hS : S.Nonempty) {g : X → Z → ℝ}
    (hg : ∀ z, Measurable fun x => g x z) : Measurable fun x => S.sup' hS (g x) := by
  have h := Finset.measurable_sup' hS (f := fun z x => g x z) (fun z _ => hg z)
  convert h using 1
  funext x
  rw [Finset.sup'_apply]

end Meas

/-! ### The optimistic-separation step with fixed tie-breaking -/

section OSRule

variable {Z : Type*} [Fintype Z] [LinearOrder Z] {A : Type*} [Fintype A] [LinearOrder A]
  [Nonempty A]
variable (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)

/-- Sampling action: first maximiser of the index `J(c) = U(c) - L⁻(c)`. -/
noncomputable def osB (l u : Z → ℝ) : A :=
  lArg (fun c => osIndex (supp c) (hne c) (hpr c) l u) (univ.min' univ_nonempty)
    (univ.sort (· ≤ ·))

/-- Optimistic inside witness of `b`: first maximiser of `u` on `S(b)`. -/
noncomputable def osP (u : Z → ℝ) (b : A) : Z :=
  lArg u ((supp b).min' (hne b)) ((supp b).sort (· ≤ ·))

/-- Optimistic outside witness of `b`: first maximiser of `u` off `S(b)`. -/
noncomputable def osQ (u : Z → ℝ) (b : A) : Z :=
  lArg u ((supp b)ᶜ.min' (hpr b)) ((supp b)ᶜ.sort (· ≤ ·))

/-- The wider of `p` and `q` (`p` on ties). -/
noncomputable def wider (l u : Z → ℝ) (p q : Z) : Z := if u q - l q ≤ u p - l p then p else q

/-- The terminal queried by the optimistic-separation step on the box `[l, u]`. -/
noncomputable def osPick (l u : Z → ℝ) : Z :=
  wider l u (osP supp hne u (osB supp hne hpr l u)) (osQ supp hpr u (osB supp hne hpr l u))

/-- The action returned at a stop: first minimiser of the exact certificate. -/
noncomputable def recA (l u : Z → ℝ) : A :=
  lArg (fun c => -rectCert (supp c) (hne c) (hpr c) l u) (univ.min' univ_nonempty)
    (univ.sort (· ≤ ·))

/-- The global certification test: some action has exact certificate at most `ε`. -/
def certAt (ε : ℝ) (l u : Z → ℝ) : Prop := ∃ c, rectCert (supp c) (hne c) (hpr c) l u ≤ ε

/-- Confidence failure: the box is empty at some terminal. -/
def boxEmpty (l u : Z → ℝ) : Prop := ∃ z, u z < l z

/-- The episode's stopping test: certification or confidence failure. -/
def stopAt (ε : ℝ) (l u : Z → ℝ) : Prop := certAt supp hne hpr ε l u ∨ boxEmpty l u

/-- When the stopping test fails, `osPick` is a continuing optimistic-separation step. -/
theorem osPick_step (l u : Z → ℝ) (ε : ℝ)
    (hfail : ∀ c, ε < rectCert (supp c) (hne c) (hpr c) l u) :
    OSStep supp hne hpr l u ε (osPick supp hne hpr l u) := by
  refine ⟨hfail, osB supp hne hpr l u, osP supp hne u (osB supp hne hpr l u),
    osQ supp hpr u (osB supp hne hpr l u), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    unfold osB
    exact (lArg_ge (fun c => osIndex (supp c) (hne c) (hpr c) l u) _ _).2 c ((mem_sort (· ≤ ·)).mpr (mem_univ c))
  · rcases lArg_mem u ((supp (osB supp hne hpr l u)).min' (hne _))
      ((supp (osB supp hne hpr l u)).sort (· ≤ ·)) with h | h
    · unfold osP; rw [h]; exact min'_mem _ _
    · unfold osP; exact (mem_sort (· ≤ ·)).mp h
  · intro y hy
    exact (lArg_ge _ _ _).2 y ((mem_sort (· ≤ ·)).mpr hy)
  · rcases lArg_mem u ((supp (osB supp hne hpr l u))ᶜ.min' (hpr _))
      ((supp (osB supp hne hpr l u))ᶜ.sort (· ≤ ·)) with h | h
    · unfold osQ; rw [h]; exact mem_compl.mp (min'_mem _ _)
    · unfold osQ; exact mem_compl.mp ((mem_sort (· ≤ ·)).mp h)
  · intro y hy
    exact (lArg_ge _ _ _).2 y ((mem_sort (· ≤ ·)).mpr (mem_compl.mpr hy))
  · unfold osPick wider
    split_ifs with h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, (not_le.mp h).le⟩

theorem recA_le (l u : Z → ℝ) (c : A) :
    rectCert (supp (recA supp hne hpr l u)) (hne _) (hpr _) l u ≤
      rectCert (supp c) (hne c) (hpr c) l u := by
  have h := (lArg_ge (fun c => -rectCert (supp c) (hne c) (hpr c) l u)
    (univ.min' univ_nonempty) (univ.sort (· ≤ ·))).2 c ((mem_sort (· ≤ ·)).mpr (mem_univ c))
  unfold recA
  linarith

section Meas

variable {X : Type*} [MeasurableSpace X] {l u : X → Z → ℝ}
  (hl : ∀ z, Measurable fun x => l x z) (hu : ∀ z, Measurable fun x => u x z)
include hl hu

omit [Fintype A] [LinearOrder A] [Nonempty A] in
lemma rectCert_meas (c : A) :
    Measurable fun x => rectCert (supp c) (hne c) (hpr c) (l x) (u x) := by
  unfold rectCert
  exact measurable_const.max
    ((measurable_sup'_apply (hpr c) hu).sub (measurable_sup'_apply (hne c) hl))

lemma osPick_meas (z : Z) : MeasurableSet {x | osPick supp hne hpr (l x) (u x) = z} := by
  have hb : ∀ c, MeasurableSet {x | osB supp hne hpr (l x) (u x) = c} := by
    refine lArg_meas (F := fun x c => osIndex (supp c) (hne c) (hpr c) (l x) (u x))
      (fun c => ?_) _ (fun _ => MeasurableSet.const _)
    unfold osIndex
    exact (measurable_sup'_apply (hne c) hu).sub (measurable_sup'_apply (hpr c) hl)
  have hp : ∀ y, MeasurableSet {x | osP supp hne (u x) (osB supp hne hpr (l x) (u x)) = y} :=
    fun y => measurableSet_sel hb (P := fun c x => osP supp hne (u x) c = y)
      (fun c => lArg_meas (F := u) hu _ (fun _ => MeasurableSet.const _) y)
  have hq : ∀ y, MeasurableSet {x | osQ supp hpr (u x) (osB supp hne hpr (l x) (u x)) = y} :=
    fun y => measurableSet_sel hb (P := fun c x => osQ supp hpr (u x) c = y)
      (fun c => lArg_meas (F := u) hu _ (fun _ => MeasurableSet.const _) y)
  have hpq : ∀ c : Z × Z, MeasurableSet {x | (osP supp hne (u x) (osB supp hne hpr (l x) (u x)),
      osQ supp hpr (u x) (osB supp hne hpr (l x) (u x))) = c} := by
    rintro ⟨a, b⟩
    have h : {x | (osP supp hne (u x) (osB supp hne hpr (l x) (u x)),
        osQ supp hpr (u x) (osB supp hne hpr (l x) (u x))) = (a, b)} =
        {x | osP supp hne (u x) (osB supp hne hpr (l x) (u x)) = a} ∩
          {x | osQ supp hpr (u x) (osB supp hne hpr (l x) (u x)) = b} := by
      ext x
      simp [Prod.ext_iff]
    rw [h]
    exact (hp a).inter (hq b)
  exact measurableSet_sel hpq (P := fun c x => wider (l x) (u x) c.1 c.2 = z)
    (fun c => measurableSet_ite_eq (measurableSet_le (((hu c.2).sub (hl c.2)))
      ((hu c.1).sub (hl c.1))) z (MeasurableSet.const _) (MeasurableSet.const _))

lemma recA_meas (a : A) : MeasurableSet {x | recA supp hne hpr (l x) (u x) = a} :=
  lArg_meas (F := fun x c => -rectCert (supp c) (hne c) (hpr c) (l x) (u x))
    (fun c => (rectCert_meas supp hne hpr hl hu c).neg) _ (fun _ => MeasurableSet.const _) a

omit [Fintype A] [LinearOrder A] [Nonempty A] in
lemma boxEmpty_meas : MeasurableSet {x | boxEmpty (l x) (u x)} := by
  simp only [boxEmpty, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun z => measurableSet_lt (hu z) (hl z)

omit [Nonempty A] in
lemma stopAt_meas (ε : ℝ) : MeasurableSet {x | stopAt supp hne hpr ε (l x) (u x)} := by
  unfold stopAt
  rw [Set.ofPred_or]
  refine MeasurableSet.union ?_ (boxEmpty_meas hl hu)
  simp only [certAt, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun c =>
    measurableSet_le (rectCert_meas supp hne hpr hl hu c) measurable_const

end Meas

/-! ### The episode run on a tape -/

/-- Lower endpoint of the running-intersection Hoeffding box at the count vector `N`. -/
noncomputable def boxLo (M δ : ℝ) (x : Z × ℕ → ℝ) (N : Z → ℕ) (z : Z) : ℝ :=
  runLo (hoeffLo M δ (fun i => x (z, i))) (N z)

/-- Upper endpoint of the same box. -/
noncomputable def boxHi (M δ : ℝ) (x : Z × ℕ → ℝ) (N : Z → ℕ) (z : Z) : ℝ :=
  runHi (hoeffHi M δ (fun i => x (z, i))) (N z)

/-- The terminal queried when the counts are `N`. -/
noncomputable def pickAt (M δ : ℝ) (x : Z × ℕ → ℝ) (N : Z → ℕ) : Z :=
  osPick supp hne hpr (boxLo M δ x N) (boxHi M δ x N)

/-- Query counts of the run on the tape `x` after `t` steps. -/
noncomputable def cnt (M δ : ℝ) (x : Z × ℕ → ℝ) : ℕ → Z → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun z => cnt M δ x t z + if pickAt supp hne hpr M δ x (cnt M δ x t) = z then 1 else 0

/-- The terminal queried at step `t` of the run on the tape `x`. -/
noncomputable def selR (M δ : ℝ) (x : Z × ℕ → ℝ) (t : ℕ) : Z :=
  pickAt supp hne hpr M δ x (cnt supp hne hpr M δ x t)

lemma queryCount_selR (M δ : ℝ) (x : Z × ℕ → ℝ) :
    ∀ t z, queryCount (selR supp hne hpr M δ x) t z = cnt supp hne hpr M δ x t z
  | 0, z => by simp [queryCount, cnt]
  | t + 1, z => by
    have h : ∀ s, queryCount (selR supp hne hpr M δ x) s z =
        ∑ r ∈ range s, if selR supp hne hpr M δ x r = z then 1 else 0 :=
      fun s => card_filter _ _
    rw [h, sum_range_succ, ← h, queryCount_selR M δ x t z]
    rfl

lemma tapeLo_selR (M δ : ℝ) (x : Z × ℕ → ℝ) (t : ℕ) :
    tapeLo M δ (fun z i => x (z, i)) (selR supp hne hpr M δ x) t =
      boxLo M δ x (cnt supp hne hpr M δ x t) := by
  funext z
  simp only [tapeLo, boxLo, queryCount_selR]

lemma tapeHi_selR (M δ : ℝ) (x : Z × ℕ → ℝ) (t : ℕ) :
    tapeHi M δ (fun z i => x (z, i)) (selR supp hne hpr M δ x) t =
      boxHi M δ x (cnt supp hne hpr M δ x t) := by
  funext z
  simp only [tapeHi, boxHi, queryCount_selR]

open Classical in
/-- Stopping count of an episode with cap `K`: the first `t ≤ K` at which the stopping test
holds on the box after `t` queries, and `K + 1` if there is none. -/
noncomputable def stopTime (M δ ε : ℝ) (K : ℕ) (x : Z × ℕ → ℝ) : ℕ :=
  Nat.find (p := fun t => K < t ∨ stopAt supp hne hpr ε (boxLo M δ x (cnt supp hne hpr M δ x t))
    (boxHi M δ x (cnt supp hne hpr M δ x t))) ⟨K + 1, Or.inl (Nat.lt_succ_self K)⟩

/-! ### Episode `j` of the restarted procedure -/

/-- Queried terminals of episode `j` (box confidence `δ / (j (j + 1))`). -/
noncomputable def epSel (M δ : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) : ℕ → Z :=
  selR supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x

/-- Stopping count of episode `j` (cap `2^j`). -/
noncomputable def epStop (M δ ε : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) : ℕ :=
  stopTime supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) ε (2 ^ j) x

/-- Observations used by episode `j`. -/
noncomputable def epObs (M δ ε : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) : ℕ :=
  min (epStop supp hne hpr M δ ε j x) (2 ^ j)

/-- Output of episode `j`: the action of least certificate on the box at the stop. -/
noncomputable def epRec (M δ ε : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) : A :=
  recA supp hne hpr
    (boxLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x
      (cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x (epStop supp hne hpr M δ ε j x)))
    (boxHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x
      (cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x (epStop supp hne hpr M δ ε j x)))

/-- Failure set of episode `j`: timeout (the cap `2^j` is reached without stopping) or
confidence failure (the box at the stopping time is empty at some terminal). -/
def epFail (M δ ε : ℝ) (j : ℕ) : Set (Z × ℕ → ℝ) :=
  {x | 2 ^ j < epStop supp hne hpr M δ ε j x ∨
    boxEmpty (boxLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x
      (cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x (epStop supp hne hpr M δ ε j x)))
      (boxHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x
      (cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x (epStop supp hne hpr M δ ε j x)))}

/-! ### Measurability -/

omit [Fintype Z] [LinearOrder Z] [Nonempty A] in
lemma measurable_hoeffLo (M δ : ℝ) (z : Z) (k : ℕ) :
    Measurable fun x : Z × ℕ → ℝ => hoeffLo M δ (fun i => x (z, i)) k := by
  unfold hoeffLo
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte]; exact measurable_const
  · simp only [hk, ↓reduceIte]
    exact ((Finset.measurable_sum _ fun i _ => measurable_pi_apply (z, i)).div_const _).sub_const _

omit [Fintype Z] [LinearOrder Z] [Nonempty A] in
lemma measurable_hoeffHi (M δ : ℝ) (z : Z) (k : ℕ) :
    Measurable fun x : Z × ℕ → ℝ => hoeffHi M δ (fun i => x (z, i)) k := by
  unfold hoeffHi
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte]; exact measurable_const
  · simp only [hk, ↓reduceIte]
    exact ((Finset.measurable_sum _ fun i _ => measurable_pi_apply (z, i)).div_const _).add_const _

set_option linter.unusedSectionVars false in
omit [LinearOrder Z] [Nonempty A] in
lemma measurable_boxLo (M δ : ℝ) (N : Z → ℕ) (z : Z) :
    Measurable fun x : Z × ℕ → ℝ => boxLo M δ x N z := by
  unfold boxLo
  generalize N z = n
  induction n with
  | zero => exact measurable_hoeffLo M δ z 0
  | succ k ih => exact ih.max (measurable_hoeffLo M δ z (k + 1))

set_option linter.unusedSectionVars false in
omit [LinearOrder Z] [Nonempty A] in
lemma measurable_boxHi (M δ : ℝ) (N : Z → ℕ) (z : Z) :
    Measurable fun x : Z × ℕ → ℝ => boxHi M δ x N z := by
  unfold boxHi
  generalize N z = n
  induction n with
  | zero => exact measurable_hoeffHi M δ z 0
  | succ k ih => exact ih.min (measurable_hoeffHi M δ z (k + 1))

lemma cnt_meas (M δ : ℝ) :
    ∀ (t : ℕ) (N : Z → ℕ), MeasurableSet {x | cnt supp hne hpr M δ x t = N}
  | 0, N => by
    show MeasurableSet {_x | (fun _ : Z => (0 : ℕ)) = N}
    exact MeasurableSet.const _
  | t + 1, N => by
    refine measurableSet_sel (cnt_meas M δ t)
      (P := fun N0 x => (fun z => N0 z + if pickAt supp hne hpr M δ x N0 = z then 1 else 0) = N)
      (fun N0 => ?_)
    exact measurableSet_sel
      (osPick_meas supp hne hpr (measurable_boxLo M δ N0) (measurable_boxHi M δ N0))
      (P := fun z0 _ => (fun z => N0 z + if z0 = z then 1 else 0) = N)
      (fun _ => MeasurableSet.const _)

lemma selR_meas (M δ : ℝ) (t : ℕ) (z : Z) :
    MeasurableSet {x | selR supp hne hpr M δ x t = z} :=
  measurableSet_sel (cnt_meas supp hne hpr M δ t) (P := fun N x => pickAt supp hne hpr M δ x N = z)
    (fun N => osPick_meas supp hne hpr (measurable_boxLo M δ N) (measurable_boxHi M δ N) z)

open Classical in
lemma stopTime_measurable (M δ ε : ℝ) (K : ℕ) :
    Measurable (stopTime supp hne hpr M δ ε K) := by
  have hQ : ∀ t, MeasurableSet {x : Z × ℕ → ℝ | K < t ∨ stopAt supp hne hpr ε
      (boxLo M δ x (cnt supp hne hpr M δ x t)) (boxHi M δ x (cnt supp hne hpr M δ x t))} := by
    intro t
    rw [Set.ofPred_or]
    exact (MeasurableSet.const _).union (measurableSet_sel (cnt_meas supp hne hpr M δ t)
      (P := fun N x => stopAt supp hne hpr ε (boxLo M δ x N) (boxHi M δ x N))
      (fun N => stopAt_meas supp hne hpr (measurable_boxLo M δ N) (measurable_boxHi M δ N) ε))
  refine measurable_to_countable' fun n => ?_
  have h : stopTime supp hne hpr M δ ε K ⁻¹' {n} =
      {x : Z × ℕ → ℝ | K < n ∨ stopAt supp hne hpr ε (boxLo M δ x (cnt supp hne hpr M δ x n))
        (boxHi M δ x (cnt supp hne hpr M δ x n))} ∩
      ⋂ k ∈ range n, {x : Z × ℕ → ℝ | K < k ∨ stopAt supp hne hpr ε
        (boxLo M δ x (cnt supp hne hpr M δ x k)) (boxHi M δ x (cnt supp hne hpr M δ x k))}ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, stopTime, Nat.find_eq_iff,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, mem_range]
  rw [h]
  exact (hQ n).inter (Finset.measurableSet_biInter _ fun k _ => (hQ k).compl)

/-- The stopping count of episode `j` is measurable. -/
theorem epStop_measurable (M δ ε : ℝ) (j : ℕ) : Measurable (epStop supp hne hpr M δ ε j) :=
  stopTime_measurable supp hne hpr M _ ε _

/-- The number of observations of episode `j` is measurable. -/
theorem epObs_measurable (M δ ε : ℝ) (j : ℕ) : Measurable (epObs supp hne hpr M δ ε j) :=
  (Measurable.of_discrete (f := fun n : ℕ => min n (2 ^ j))).comp
    (epStop_measurable supp hne hpr M δ ε j)

/-- Every query of episode `j` is a measurable function of the tape. -/
theorem epSel_measurableSet (M δ : ℝ) (j t : ℕ) (z : Z) :
    MeasurableSet {x | epSel supp hne hpr M δ j x t = z} :=
  selR_meas supp hne hpr M _ t z

/-- The counts at the stopping time of episode `j` are a measurable function of the tape. -/
lemma epCnt_meas (M δ ε : ℝ) (j : ℕ) (N : Z → ℕ) :
    MeasurableSet {x | cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x
      (epStop supp hne hpr M δ ε j x) = N} :=
  measurableSet_sel (fun n => epStop_measurable supp hne hpr M δ ε j (measurableSet_singleton n))
    (P := fun n x => cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x n = N)
    (fun n => cnt_meas supp hne hpr M _ n N)

/-- The failure set of episode `j` is measurable. -/
theorem epFail_measurableSet (M δ ε : ℝ) (j : ℕ) :
    MeasurableSet (epFail supp hne hpr M δ ε j) := by
  unfold epFail
  rw [Set.ofPred_or]
  exact (epStop_measurable supp hne hpr M δ ε j measurableSet_Ioi).union
    (measurableSet_sel (epCnt_meas supp hne hpr M δ ε j)
      (P := fun N x => boxEmpty (boxLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x N)
        (boxHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x N))
      (fun N => boxEmpty_meas (measurable_boxLo _ _ N) (measurable_boxHi _ _ N)))

/-- The output of episode `j` is a measurable function of the tape. -/
theorem epRec_measurableSet (M δ ε : ℝ) (j : ℕ) (a : A) :
    MeasurableSet {x | epRec supp hne hpr M δ ε j x = a} := by
  have hN := epCnt_meas supp hne hpr M δ ε j
  exact measurableSet_sel hN (P := fun N x => recA supp hne hpr
      (boxLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x N)
      (boxHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x N) = a)
    (fun N => recA_meas supp hne hpr (measurable_boxLo _ _ N) (measurable_boxHi _ _ N) a)

/-! ### Dependence on finitely many coordinates -/

omit [Fintype Z] [LinearOrder Z] [Fintype A] [LinearOrder A] [Nonempty A] in
lemma hoeffLo_congr (M δ : ℝ) {y y' : ℕ → ℝ} {n : ℕ} (h : ∀ i < n, y i = y' i) :
    ∀ k ≤ n, hoeffLo M δ y k = hoeffLo M δ y' k := by
  intro k hk
  unfold hoeffLo
  rw [Finset.sum_congr rfl (fun i hi => h i (lt_of_lt_of_le (mem_range.mp hi) hk))]

omit [Fintype Z] [LinearOrder Z] [Fintype A] [LinearOrder A] [Nonempty A] in
lemma hoeffHi_congr (M δ : ℝ) {y y' : ℕ → ℝ} {n : ℕ} (h : ∀ i < n, y i = y' i) :
    ∀ k ≤ n, hoeffHi M δ y k = hoeffHi M δ y' k := by
  intro k hk
  unfold hoeffHi
  rw [Finset.sum_congr rfl (fun i hi => h i (lt_of_lt_of_le (mem_range.mp hi) hk))]

omit [Fintype Z] [LinearOrder Z] [Fintype A] [LinearOrder A] [Nonempty A] in
lemma runLo_congr {lo lo' : ℕ → ℝ} {n : ℕ} (h : ∀ k ≤ n, lo k = lo' k) :
    runLo lo n = runLo lo' n := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ k ih =>
    show max (runLo lo k) (lo (k + 1)) = max (runLo lo' k) (lo' (k + 1))
    rw [ih (fun i hi => h i (by omega)), h (k + 1) le_rfl]

omit [Fintype Z] [LinearOrder Z] [Fintype A] [LinearOrder A] [Nonempty A] in
lemma runHi_congr {hi hi' : ℕ → ℝ} {n : ℕ} (h : ∀ k ≤ n, hi k = hi' k) :
    runHi hi n = runHi hi' n := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ k ih =>
    show min (runHi hi k) (hi (k + 1)) = min (runHi hi' k) (hi' (k + 1))
    rw [ih (fun i hi => h i (by omega)), h (k + 1) le_rfl]

set_option linter.unusedSectionVars false in
omit [LinearOrder Z] [Fintype A] [LinearOrder A] [Nonempty A] in
lemma box_congr (M δ : ℝ) {x x' : Z × ℕ → ℝ} {n : ℕ}
    (h : ∀ z i, i < n → x (z, i) = x' (z, i)) {N : Z → ℕ} (hN : ∀ z, N z ≤ n) :
    boxLo M δ x N = boxLo M δ x' N ∧ boxHi M δ x N = boxHi M δ x' N := by
  constructor
  · funext z
    exact runLo_congr (hoeffLo_congr M δ (fun i hi => h z i (lt_of_lt_of_le hi (hN z))))
  · funext z
    exact runHi_congr (hoeffHi_congr M δ (fun i hi => h z i (lt_of_lt_of_le hi (hN z))))

lemma cnt_le (M δ : ℝ) (x : Z × ℕ → ℝ) : ∀ t z, cnt supp hne hpr M δ x t z ≤ t
  | 0, _ => le_rfl
  | t + 1, z => by
    have ih := cnt_le M δ x t z
    show cnt supp hne hpr M δ x t z +
      (if pickAt supp hne hpr M δ x (cnt supp hne hpr M δ x t) = z then 1 else 0) ≤ t + 1
    split_ifs <;> omega

lemma cnt_congr (M δ : ℝ) {x x' : Z × ℕ → ℝ} {n : ℕ}
    (h : ∀ z i, i < n → x (z, i) = x' (z, i)) :
    ∀ t ≤ n, cnt supp hne hpr M δ x t = cnt supp hne hpr M δ x' t
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := cnt_congr M δ h t (by omega)
    obtain ⟨hb, hb'⟩ := box_congr M δ h (N := cnt supp hne hpr M δ x t)
      (fun z => (cnt_le supp hne hpr M δ x t z).trans (by omega))
    show (fun z => cnt supp hne hpr M δ x t z +
        if pickAt supp hne hpr M δ x (cnt supp hne hpr M δ x t) = z then 1 else 0) =
      (fun z => cnt supp hne hpr M δ x' t z +
        if pickAt supp hne hpr M δ x' (cnt supp hne hpr M δ x' t) = z then 1 else 0)
    rw [← ih]
    unfold pickAt
    rw [hb, hb']

/-- The box after `t ≤ n` queries depends only on the coordinates `(z, i)`, `i < n`. -/
lemma boxAt_congr (M δ : ℝ) {x x' : Z × ℕ → ℝ} {n : ℕ}
    (h : ∀ z i, i < n → x (z, i) = x' (z, i)) {t : ℕ} (ht : t ≤ n) :
    boxLo M δ x (cnt supp hne hpr M δ x t) = boxLo M δ x' (cnt supp hne hpr M δ x' t) ∧
      boxHi M δ x (cnt supp hne hpr M δ x t) = boxHi M δ x' (cnt supp hne hpr M δ x' t) := by
  rw [← cnt_congr supp hne hpr M δ h t ht]
  exact box_congr M δ h (fun z => (cnt_le supp hne hpr M δ x t z).trans ht)

open Classical in
lemma stopTime_le (M δ ε : ℝ) (K : ℕ) (x : Z × ℕ → ℝ) :
    stopTime supp hne hpr M δ ε K x ≤ K + 1 :=
  Nat.find_min' _ (Or.inl (Nat.lt_succ_self K))

open Classical in
lemma stopTime_congr (M δ ε : ℝ) (K : ℕ) {x x' : Z × ℕ → ℝ}
    (h : ∀ z i, i < K + 1 → x (z, i) = x' (z, i)) :
    stopTime supp hne hpr M δ ε K x = stopTime supp hne hpr M δ ε K x' := by
  have hQ : ∀ t, (K < t ∨ stopAt supp hne hpr ε (boxLo M δ x (cnt supp hne hpr M δ x t))
      (boxHi M δ x (cnt supp hne hpr M δ x t))) ↔
      (K < t ∨ stopAt supp hne hpr ε (boxLo M δ x' (cnt supp hne hpr M δ x' t))
      (boxHi M δ x' (cnt supp hne hpr M δ x' t))) := by
    intro t
    by_cases hKt : K < t
    · simp [hKt]
    · obtain ⟨hb, hb'⟩ := boxAt_congr supp hne hpr M δ h (t := t) (by omega)
      rw [hb, hb']
  have hs := Nat.find_spec (p := fun t => K < t ∨ stopAt supp hne hpr ε
    (boxLo M δ x (cnt supp hne hpr M δ x t)) (boxHi M δ x (cnt supp hne hpr M δ x t)))
    ⟨K + 1, Or.inl (Nat.lt_succ_self K)⟩
  have hm := fun k (hk : k < stopTime supp hne hpr M δ ε K x) => Nat.find_min (p := fun t =>
    K < t ∨ stopAt supp hne hpr ε (boxLo M δ x (cnt supp hne hpr M δ x t))
      (boxHi M δ x (cnt supp hne hpr M δ x t))) ⟨K + 1, Or.inl (Nat.lt_succ_self K)⟩ hk
  symm
  unfold stopTime
  rw [Nat.find_eq_iff]
  exact ⟨(hQ _).mp hs, fun k hk hk' => hm k hk ((hQ k).mpr hk')⟩

/-- **Episode `j` reads only the coordinates `(z, i)` with `i ≤ 2^j` of its tape**: two
tapes that agree there have the same stopping count, observations, output, failure status,
and the same queries `t ≤ 2^j`. -/
theorem ep_local (M δ ε : ℝ) (j : ℕ) {x x' : Z × ℕ → ℝ}
    (h : ∀ z i, i ≤ 2 ^ j → x (z, i) = x' (z, i)) :
    epStop supp hne hpr M δ ε j x = epStop supp hne hpr M δ ε j x' ∧
      epObs supp hne hpr M δ ε j x = epObs supp hne hpr M δ ε j x' ∧
      epRec supp hne hpr M δ ε j x = epRec supp hne hpr M δ ε j x' ∧
      (x ∈ epFail supp hne hpr M δ ε j ↔ x' ∈ epFail supp hne hpr M δ ε j) ∧
      ∀ t ≤ 2 ^ j, epSel supp hne hpr M δ j x t = epSel supp hne hpr M δ j x' t := by
  have h' : ∀ z i, i < 2 ^ j + 1 → x (z, i) = x' (z, i) := fun z i hi => h z i (by omega)
  have hσ : epStop supp hne hpr M δ ε j x = epStop supp hne hpr M δ ε j x' :=
    stopTime_congr supp hne hpr M _ ε _ h'
  have hle : epStop supp hne hpr M δ ε j x ≤ 2 ^ j + 1 :=
    stopTime_le supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) ε (2 ^ j) x
  obtain ⟨hb, hb'⟩ := boxAt_congr supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) h' hle
  refine ⟨hσ, by unfold epObs; rw [hσ], ?_, ?_, fun t ht => ?_⟩
  · unfold epRec
    rw [hb, hb', ← hσ]
  · unfold epFail
    simp only [Set.mem_ofPred_eq]
    rw [hb, hb', ← hσ]
  · obtain ⟨hb, hb'⟩ := boxAt_congr supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) h'
      (t := t) (by omega)
    show osPick supp hne hpr _ _ = osPick supp hne hpr _ _
    rw [hb, hb']

/-! ### The hypotheses of `certified_restart_product` -/

theorem ep_hobs (M δ ε : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) :
    epObs supp hne hpr M δ ε j x ≤ 2 ^ j :=
  min_le_right _ _

open Classical in
theorem ep_hrule (M δ ε : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) :
    ∀ t < epStop supp hne hpr M δ ε j x, OSStep supp hne hpr
      (tapeLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i))
        (epSel supp hne hpr M δ j x) t)
      (tapeHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i))
        (epSel supp hne hpr M δ j x) t) ε
      (epSel supp hne hpr M δ j x t) := by
  intro t ht
  have hmin := Nat.find_min _ ht
  unfold epSel
  rw [tapeLo_selR, tapeHi_selR]
  refine osPick_step supp hne hpr _ _ ε (fun c => not_le.mp fun hc => hmin (Or.inr (Or.inl ⟨c, hc⟩)))

/-- On the coverage event an episode that stops within its cap does not fail: the box
contains the means, so it is not empty. -/
theorem ep_hret (M δ ε : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) {m : Z → ℝ}
    (hc : tapeCovered M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i))
      (epSel supp hne hpr M δ j x) m) :
    epStop supp hne hpr M δ ε j x ≤ 2 ^ j → x ∉ epFail supp hne hpr M δ ε j := by
  intro h h'
  rcases h' with h' | ⟨z, hz⟩
  · exact absurd h' (not_lt.mpr h)
  · have hcσ := hc (epStop supp hne hpr M δ ε j x)
    unfold epSel at hcσ
    rw [tapeLo_selR, tapeHi_selR] at hcσ
    have h1 := hcσ.1 z
    have h2 := hcσ.2 z
    linarith

open Classical in
theorem ep_hsucc (M δ ε : ℝ) (j : ℕ) (x : Z × ℕ → ℝ) (hx : x ∉ epFail supp hne hpr M δ ε j) :
    rectCert (supp (epRec supp hne hpr M δ ε j x)) (hne _) (hpr _)
      (tapeLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i))
        (epSel supp hne hpr M δ j x) (epStop supp hne hpr M δ ε j x))
      (tapeHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) (fun z i => x (z, i))
        (epSel supp hne hpr M δ j x) (epStop supp hne hpr M δ ε j x)) ≤ ε := by
  have hspec := Nat.find_spec (p := fun t => 2 ^ j < t ∨ stopAt supp hne hpr ε
    (boxLo M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x
      (cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x t))
    (boxHi M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x
      (cnt supp hne hpr M (δ / ((j : ℝ) * ((j : ℝ) + 1))) x t)))
    ⟨2 ^ j + 1, Or.inl (Nat.lt_succ_self _)⟩
  rcases hspec with h | ⟨c, hc⟩ | he
  · exact absurd (Or.inl h) hx
  · unfold epSel
    rw [tapeLo_selR, tapeHi_selR]
    exact (recA_le supp hne hpr _ _ c).trans hc
  · exact absurd (Or.inr he) hx

end OSRule

/-! ### The certified restart bound for the concrete procedure -/

/-- **Certified restart bound (Theorem `thm:active-restart`) for an explicit procedure.**

Same probability space and constants as `certified_restart_product`: reward laws `law z` on
`[0, 1]` with means `m z`, `M ≥ max {2, |Z|}`, `0 < δ ≤ 1/4`, proper supports covering `Z`,
`0 ≤ ε ≤ 1`, `Γ` the largest separation, `Γ + ε > 0`.  The finite sets `Z` and `A` carry a
linear order, used only for tie-breaking (`[Nonempty A]` follows from the cover; it is an
instance argument because the definitions use it).

Episode `j` is the explicit optimistic-separation sampler `epSel` on its tape, with Hoeffding
boxes of confidence `δ / (j (j + 1))`, stopped at the first certificate, at the first empty
box (confidence failure), or after `2^j` queries (`epStop`, `epObs`, `epRec`); it fails on
timeout or confidence failure (`epFail`).  For this procedure:
`E τ < 1600 H_ρ L`, `τ < ∞` almost surely, the event that no episode returns is null, and
the output is not `ε`-optimal with probability at most `δ`. -/
theorem active_restart_instance {Z : Type*} [Fintype Z] [LinearOrder Z] [Nonempty Z]
    {A : Type*} [Fintype A] [LinearOrder A] [Nonempty A]
    (law : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (law z)]
    {m : Z → ℝ} (hsupp : ∀ z, ∀ᵐ x ∂(law z), x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ z, ∫ x, x ∂(law z) = m z)
    {M δ : ℝ} (hM : 2 ≤ M) (hcard : (Fintype.card Z : ℝ) ≤ M) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty) (hpr : ∀ a, (supp a)ᶜ.Nonempty)
    (hcov : ∀ z, ∃ a, z ∈ supp a) {ε Γ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hΓ : IsGreatest (Set.range fun a => val (supp a) (hne a) m - (supp a)ᶜ.sup' (hpr a) m) Γ)
    (hpos : 0 < Γ + ε) :
    ∫⁻ ω, restartTime (epFail supp hne hpr M δ ε) (epObs supp hne hpr M δ ε) ω
        ∂(restartMeasure law) <
        ENNReal.ofReal (1600 * (∑ z, 1 / (max (Γ + ε) (gmax m - m z) / 2) ^ 2) *
          Real.log (128 * M / (δ * (univ.inf' univ_nonempty
            (fun z => max (Γ + ε) (gmax m - m z) / 2)) ^ 2))) ∧
      (∀ᵐ ω ∂(restartMeasure law),
        restartTime (epFail supp hne hpr M δ ε) (epObs supp hne hpr M δ ε) ω < ∞) ∧
      restartMeasure law (⋂ j : ℕ, ⋂ i ∈ Finset.Ico 1 j,
        {ω | ω i ∈ epFail supp hne hpr M δ ε i}) = 0 ∧
      restartMeasure law {ω | ε < regret (supp (epRec supp hne hpr M δ ε
        (restartOut (epFail supp hne hpr M δ ε) ω)
        (ω (restartOut (epFail supp hne hpr M δ ε) ω)))) (hne _) m} ≤ ENNReal.ofReal δ :=
  certified_restart_product law hsupp hmean hM hcard hδ0 hδ supp hne hpr hcov hε0 hε1 hΓ hpos
    (epSel supp hne hpr M δ) (epStop supp hne hpr M δ ε) (epObs supp hne hpr M δ ε)
    (epRec supp hne hpr M δ ε) (epFail supp hne hpr M δ ε)
    (epFail_measurableSet supp hne hpr M δ ε) (ep_hobs supp hne hpr M δ ε)
    (fun j _ x _ => ep_hrule supp hne hpr M δ ε j x)
    (fun j _ x hc => ep_hret supp hne hpr M δ ε j x hc)
    (fun j _ x hx => ep_hsucc supp hne hpr M δ ε j x hx)

end LiteralF6
end JointRootCert
