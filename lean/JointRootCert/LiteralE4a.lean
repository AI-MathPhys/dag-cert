/-
Joint Root Certification: prerequisites for the literal form of `eq:ram-work-bounds`.

Manuscript result covered (with `LiteralE4.lean`, which imports this file):

* `prop:uct-coupling` (Safe permanent retirement; also labelled `prop:ta-coupled`,
  `thm:protected-pruning`, `thm:decision-retirement`), the remark "but not necessarily the
  numerical marginal gap", and the work display `eq:ram-work-bounds` of its proof.

IMPORTS `JointRootCert.RetireFinal`.  Build order: `LiteralE4a`, then `LiteralE4`.

Contents.

1. `gap_not_preserved`: an explicit `RetireRun` on three actions in which the leader and the
   stopping bit over the active actions agree with those over all actions, while the
   numerical marginal gap `max_{b ≠ leader} U(b) - L(leader)` differs (`-9` against `-5`).
2. Completeness of the reference-counted release cascade `RetireFinal.releaseLoop`:
   with the fuel `relFuel` it reaches its fixed point (`releaseLoop_exact`): a gate keeps
   its child list iff it is reachable from a protected gate through live incidences, and
   every other gate is released.
3. A wave scheduler that does not scan empty level buckets (`waveS`).  The pending levels
   are kept in an implemented indexed heap (`HeapImpl.Heap`, keyed by `L - level`, so that
   find-max returns the lowest pending level).  `waveS_spec`: the wave ends in exactly the
   state of `HeapImpl.waveH`, and its computed cost is at most
   `4 + 2 Σ_{changed g} dcost g + 2 (⌈log₂ (L+1)⌉ + 3) · (deliveries)` and at least the
   number of deliveries.  There is no additive `L` term; the price is a worklist charge of
   `2(⌈log₂ (L+1)⌉ + 3)` per delivery (one level-queue insertion attempt and at most one
   later extraction, each executed by the implemented heap).

Cost model: as in `CostEngines.lean` / `HeapImpl.lean`.  New unit charges: testing whether
a level is already queued (1 unit per delivery), testing whether the level queue is empty
and reading its root (1 unit per extraction, 1 unit at the end of the wave).  Level-queue
insertions and deletions are executed by `HeapImpl.insert` / `HeapImpl.delete` and their
cost is computed.
-/
import JointRootCert.RetireFinal

namespace JointRootCert
namespace LiteralE4

open Finset CostEngines DagRetire EngineFinal RetireFinal
open HeapImpl (Heap HEState SimE Rep waveH findMax)

/-! ## 1. The numerical marginal gap is not preserved by root-action retirement -/

section GapExample

/-- Lower bounds of the example: action `0` has `L = 10`, the others `L = 0`. -/
def exL (a : Fin 3) : ℝ := if a = 0 then 10 else 0

/-- Upper bounds of the example: `U(0) = 10`, `U(1) = 5`, `U(2) = 1`. -/
def exU (a : Fin 3) : ℝ := if a = 0 then 10 else if a = 1 then 5 else 1

/-- Active sets of the example: all actions at time `0`; action `1` is retired at time `0`
(rule (ii): `U(1) = 5 < 10 = L(0)`), action `2` is kept. -/
def exAct (t : ℕ) : Finset (Fin 3) := if t = 0 then univ else {0, 2}

/-- The numerical marginal gap `max_{b ∈ s, b ≠ a} U(b) - L(a)` of `eq:cert-gap`, computed
over the action set `s` with leader `a`. -/
noncomputable def margGap {A : Type*} [DecidableEq A] (s : Finset A) (L U : A → ℝ) (a : A)
    (h : (s.erase a).Nonempty) : ℝ := (s.erase a).sup' h U - L a

lemma fin3_cases : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide

lemma exAct_succ (t : ℕ) : exAct (t + 1) = {0, 2} := ite_eq_right (Nat.succ_ne_zero t)

lemma exL_zero : exL 0 = 10 := ite_eq_left rfl
lemma exL_one : exL 1 = 0 := ite_eq_right (by decide)
lemma exL_two : exL 2 = 0 := ite_eq_right (by decide)
lemma exU_zero : exU 0 = 10 := ite_eq_left rfl
lemma exU_one : exU 1 = 5 := by
  unfold exU
  rw [ite_eq_right (by decide), ite_eq_left rfl]
lemma exU_two : exU 2 = 1 := by
  unfold exU
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]

/-- The example is a `RetireRun`: constant (hence nested) nonempty intervals, and the only
retirement is that of action `1` at time `0`, witnessed by the active action `0`. -/
theorem ex_retireRun : RetireRun (fun _ => exL) (fun _ => exU) exAct where
  nestedL := fun _ _ _ _ => le_rfl
  nestedU := fun _ _ _ _ => le_rfl
  nonempty := by
    intro _ a
    rcases fin3_cases a with rfl | rfl | rfl
    · rw [exL_zero, exU_zero]
    · rw [exL_one, exU_one]; norm_num
    · rw [exL_two, exU_two]; norm_num
  init := ite_eq_left rfl
  anti := by
    intro t
    rw [exAct_succ]
    cases t with
    | zero => exact subset_univ _
    | succ t => rw [exAct_succ]
  retire := by
    intro t b hb1 _
    rw [exAct_succ] at hb1
    have hb : b = 1 := by
      rcases fin3_cases b with rfl | rfl | rfl
      · exact absurd (by decide) hb1
      · rfl
      · exact absurd (by decide) hb1
    subst hb
    refine ⟨0, ?_, by decide, ?_⟩
    · cases t with
      | zero => exact mem_univ _
      | succ t => rw [exAct_succ]; decide
    · show exU 1 < exL 0
      rw [exL_zero, exU_one]; norm_num

/-- **`prop:uct-coupling`, "but not necessarily the numerical marginal gap".**  In the
`RetireRun` `ex_retireRun` (nested nonempty intervals, rule (ii) applied once), at time `1`:

* action `0` is the canonical lower-bound leader over all actions and over the active ones;
* for every `ε ≥ 0` the marginal stopping bit holds over all actions and over the active
  ones (as `RetireRun.stops_iff` guarantees);
* the numerical marginal gap over all actions is `-5` (attained by the retired action
  `1`), the one over the active actions is `-9`. -/
theorem gap_not_preserved :
    RetireRun (fun _ => exL) (fun _ => exU) exAct ∧
    LowLeader univ exL 0 ∧ LowLeader (exAct 1) exL 0 ∧
    (∀ ε : ℝ, 0 ≤ ε → MarginalStops univ exL exU ε 0 ∧ MarginalStops (exAct 1) exL exU ε 0) ∧
    ∃ (h1 : ((univ : Finset (Fin 3)).erase 0).Nonempty) (h2 : ((exAct 1).erase 0).Nonempty),
      margGap univ exL exU 0 h1 = -5 ∧ margGap (exAct 1) exL exU 0 h2 = -9 := by
  have hLL : LowLeader univ exL 0 := by
    refine ⟨mem_univ _, fun b _ => ?_, fun b _ _ => Fin.zero_le b⟩
    rcases fin3_cases b with rfl | rfl | rfl
    · exact le_rfl
    · rw [exL_one, exL_zero]; norm_num
    · rw [exL_two, exL_zero]; norm_num
  have hMS : ∀ ε : ℝ, 0 ≤ ε → MarginalStops univ exL exU ε 0 := by
    intro ε hε
    refine ⟨hLL, fun b _ hb => ?_⟩
    rcases fin3_cases b with rfl | rfl | rfl
    · exact absurd rfl hb
    · rw [exU_one, exL_zero]; linarith
    · rw [exU_two, exL_zero]; linarith
  have h1 : ((univ : Finset (Fin 3)).erase 0).Nonempty := ⟨1, by decide⟩
  have e1 : exAct 1 = {0, 2} := exAct_succ 0
  have h2 : ((exAct 1).erase 0).Nonempty := ⟨2, by rw [e1]; decide⟩
  refine ⟨ex_retireRun, hLL, (ex_retireRun.lowLeader_iff 1 0).1 hLL,
    fun ε hε => ⟨hMS ε hε, (ex_retireRun.stops_iff hε 1 0).1 (hMS ε hε)⟩, h1, h2, ?_, ?_⟩
  · unfold margGap
    have hs : (univ.erase (0 : Fin 3)).sup' h1 exU = 5 := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro b hb
        rcases fin3_cases b with rfl | rfl | rfl
        · exact absurd hb (by decide)
        · rw [exU_one]
        · rw [exU_two]; norm_num
      · have := Finset.le_sup' exU (show (1 : Fin 3) ∈ univ.erase 0 by decide)
        rwa [exU_one] at this
    rw [hs, exL_zero]; norm_num
  · unfold margGap
    have hs : ((exAct 1).erase (0 : Fin 3)).sup' h2 exU = 1 := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro b hb
        rw [e1] at hb
        rcases fin3_cases b with rfl | rfl | rfl
        · exact absurd hb (by decide)
        · exact absurd hb (by decide)
        · rw [exU_two]
      · have := Finset.le_sup' exU (show (2 : Fin 3) ∈ (exAct 1).erase 0 by rw [e1]; decide)
        rwa [exU_two] at this
    rw [hs, exL_zero]; norm_num

end GapExample

/-! ## 2. Completeness of the release cascade -/

section Cascade

/-- An orphan: a gate that still has children, has no live parent and is not protected.
This is exactly the release condition of `RetireFinal.releaseLoop`. -/
def Orphan (prot : ℕ → Bool) (G : Dag) (g : ℕ) : Prop :=
  G.children g ≠ [] ∧ G.parents g = [] ∧ prot g = false

/-- A gate is anchored if it is reachable from a protected gate through live incidences. -/
inductive Anch (prot : ℕ → Bool) (G : Dag) : ℕ → Prop
  | root {g : ℕ} : prot g = true → Anch prot G g
  | step {p c : ℕ} : Anch prot G p → c ∈ G.children p → Anch prot G c

variable {prot : ℕ → Bool} {G : Dag}

lemma not_anch_of_orphan (hG : G.WF) {g : ℕ} (h : Orphan prot G g) : ¬ Anch prot G g := by
  intro ha
  cases ha with
  | root hp =>
    rw [h.2.2] at hp
    exact Bool.false_ne_true hp
  | step hp hc =>
    have := (hG.parents_iff g _).2 hc
    rw [h.2.1] at this
    exact List.not_mem_nil this

lemma anch_release {g0 : ℕ} (hg0 : ¬ Anch prot G g0) {g : ℕ} (h : Anch prot G g) :
    Anch prot (releaseDag G g0) g := by
  induction h with
  | root hp => exact Anch.root hp
  | @step p c hp hc ih =>
    refine Anch.step ih (mem_release_children.2 ⟨hc, ?_⟩)
    intro e
    rw [e] at hp
    exact hg0 hp

lemma anch_mono {G' : Dag} (hsub : ∀ p, (G'.children p).Sublist (G.children p)) {g : ℕ}
    (h : Anch prot G' g) : Anch prot G g := by
  induction h with
  | root hp => exact Anch.root hp
  | @step p c _ hc ih => exact Anch.step ih ((hsub p).subset hc)

/-- **Safety of the cascade, for every fuel**: an anchored gate keeps its child list. -/
theorem releaseLoop_safe (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (G : Dag), G.WF →
    ∀ g, Anch prot G g → (releaseLoop prot f st G).1.children g = G.children g := by
  intro f
  induction f with
  | zero => intro st G _ g _; rfl
  | succ f ih =>
    intro st G hG g hg
    cases st with
    | nil => rfl
    | cons g0 st =>
      rw [RetireFinal.releaseLoop]
      by_cases hc : G.children g0 ≠ [] ∧ G.parents g0 = [] ∧ prot g0 = false
      · rw [ite_eq_left hc]
        have hna : ¬ Anch prot G g0 := not_anch_of_orphan hG hc
        refine (ih (G.children g0 ++ st) (releaseDag G g0) (releaseDag_wf hG g0) g
          (anch_release hna hg)).trans ?_
        show (if g = g0 then [] else G.children g) = G.children g
        rw [ite_eq_right]
        intro e
        rw [e] at hg
        exact hna hg
      · rw [ite_eq_right hc]
        exact ih st G hG g hg

/-- **The cascade reaches its fixed point.**  If the stack contains every orphan and the
fuel exceeds `2 · cells G + |stack|` (as `relFuel` does), no orphan is left. -/
theorem releaseLoop_orphanFree (prot : ℕ → Bool) : ∀ (f : ℕ) (st : List ℕ) (G : Dag), G.WF →
    2 * cells G + st.length < f → (∀ g, Orphan prot G g → g ∈ st) →
    ∀ g, ¬ Orphan prot (releaseLoop prot f st G).1 g := by
  intro f
  induction f with
  | zero => intro st G _ hf; omega
  | succ f ih =>
    intro st G hG hf hst
    cases st with
    | nil => exact fun g ho => List.not_mem_nil (hst g ho)
    | cons g0 st =>
      rw [List.length_cons] at hf
      rw [RetireFinal.releaseLoop]
      by_cases hc : G.children g0 ≠ [] ∧ G.parents g0 = [] ∧ prot g0 = false
      · rw [ite_eq_left hc]
        obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc.1
        have hgN : g0 < G.N := hG.parent_lt c g0 ((hG.parents_iff c g0).2 hcm)
        have hcell := cells_release hgN hc.1
        refine ih (G.children g0 ++ st) (releaseDag G g0) (releaseDag_wf hG g0)
          (by rw [List.length_append]; omega) ?_
        intro g' ho
        obtain ⟨o1, o2, o3⟩ := ho
        have o1' : (if g' = g0 then [] else G.children g') ≠ [] := o1
        have hne : g' ≠ g0 := fun e => o1' (ite_eq_left e)
        rw [ite_eq_right hne] at o1'
        by_cases hm : g' ∈ G.children g0
        · exact List.mem_append_left _ hm
        · have o2' : (if g' ∈ G.children g0 then (G.parents g').filter (· ≠ g0)
              else G.parents g') = [] := o2
          rw [ite_eq_right hm] at o2'
          rcases List.mem_cons.1 (hst g' ⟨o1', o2', o3⟩) with e | e
          · exact absurd e hne
          · exact List.mem_append_right _ e
      · rw [ite_eq_right hc]
        refine ih st G hG (by omega) ?_
        intro g' ho
        rcases List.mem_cons.1 (hst g' ho) with e | e
        · rw [e] at ho
          exact absurd ho hc
        · exact e

/-- In a circuit without orphans every gate that has children is anchored. -/
lemma anch_of_orphanFree (hG : G.WF) (hof : ∀ g, ¬ Orphan prot G g) :
    ∀ g, G.children g ≠ [] → Anch prot G g := by
  have key : ∀ n g, G.L - G.level g < n → G.children g ≠ [] → Anch prot G g := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg hc
      by_cases hp : prot g = true
      · exact Anch.root hp
      · have hp' : prot g = false := by simpa using hp
        have hpar : G.parents g ≠ [] := fun e => hof g ⟨hc, e, hp'⟩
        obtain ⟨p, hpm⟩ := List.exists_mem_of_ne_nil _ hpar
        have hcm := (hG.parents_iff g p).1 hpm
        have h1 := hG.level_lt p g hcm
        have h2 := hG.level_le p
        exact Anch.step (ih p (by omega) (List.ne_nil_of_mem hcm)) hcm
  exact fun g hc => key (G.L - G.level g + 1) g (Nat.lt_succ_self _) hc

/-- **Completeness of the reference-counted release cascade.**  Let the stack contain every
orphan of the well-formed circuit `G` and let the fuel exceed `2 · cells G + |stack|`.
Then the cascade stops at its fixed point, and it has released exactly the gates that are
not reachable from a protected gate through live incidences:

* an anchored gate keeps its child list (nothing else is released);
* every gate that is not anchored has an empty child list (it was a leaf or is released);
* the result has no orphan. -/
theorem releaseLoop_exact (prot : ℕ → Bool) (f : ℕ) (st : List ℕ) (G : Dag) (hG : G.WF)
    (hf : 2 * cells G + st.length < f) (hst : ∀ g, Orphan prot G g → g ∈ st) :
    (∀ g, Anch prot G g → (releaseLoop prot f st G).1.children g = G.children g) ∧
    (∀ g, ¬ Anch prot G g → (releaseLoop prot f st G).1.children g = []) ∧
    (∀ g, ¬ Orphan prot (releaseLoop prot f st G).1 g) := by
  have hof := releaseLoop_orphanFree prot f st G hG hf hst
  obtain ⟨a1, _, _, _, a5, _, _⟩ := releaseLoop_spec prot f st G hG
  refine ⟨releaseLoop_safe prot f st G hG, fun g hna => ?_, hof⟩
  by_contra hne
  exact hna (anch_mono a5 (anch_of_orphanFree a1 hof g hne))

/-- The fuel `relFuel` of the engine is sufficient. -/
lemma relFuel_enough (G : Dag) (st : List ℕ) : 2 * cells G + st.length < relFuel G st := by
  unfold relFuel
  omega

end Cascade

/-! ### The cascade inside the engine -/

section CascadeRun

variable {α : Type*} [LinearOrder α] [OrderBot α]

omit [OrderBot α] in
lemma orphan_retireOne (prot : ℕ → Bool) (e : ℕ × ℕ) (s : RState α) (g : ℕ)
    (h : Orphan prot (retireOne e s).1.G g) : Orphan prot s.G g ∨ g = e.2 := by
  unfold retireOne at h
  by_cases hc : e.2 ∈ s.G.children e.1 ∧ s.hi.val e.2 < s.lo.val e.1
  · rw [ite_eq_left hc] at h
    obtain ⟨o1, o2, o3⟩ := h
    by_cases hg : g = e.2
    · exact Or.inr hg
    · left
      have o2' : (if g = e.2 then (s.G.parents g).filter (· ≠ e.1) else s.G.parents g) = [] :=
        o2
      rw [ite_eq_right hg] at o2'
      refine ⟨fun e' => o1 ?_, o2', o3⟩
      have hsub := retire_children_sublist s.G e.1 e.2 g
      rw [e'] at hsub
      exact List.sublist_nil.1 hsub
  · rw [ite_eq_right hc] at h
    exact Or.inl h

omit [OrderBot α] in
lemma orphan_retireList (prot : ℕ → Bool) : ∀ (L : List (ℕ × ℕ)) (s : RState α) (g : ℕ),
    Orphan prot (retireList L s).1.G g → Orphan prot s.G g ∨ g ∈ L.map Prod.snd := by
  intro L
  induction L with
  | nil => intro s g h; exact Or.inl h
  | cons e es ih =>
    intro s g h
    rcases ih (retireOne e s).1 g h with h1 | h1
    · rcases orphan_retireOne prot e s g h1 with h2 | h2
      · exact Or.inl h2
      · right
        rw [List.map_cons, h2]
        exact List.mem_cons_self
    · right
      rw [List.map_cons]
      exact List.mem_cons_of_mem _ h1

variable {K : ℕ} {rt : ℕ → ℕ}

/-- One rollout of the Graph-Selective engine leaves no orphan: the cascade started from
the children of the tested incidences, with fuel `relFuel`, reaches its fixed point. -/
theorem relStep_orphanFree (cand : RState α → RState α → List (ℕ × ℕ)) (u : ℕ × α × α)
    (s : QS α) (hwf : s.r.G.WF) (h : ∀ g, ¬ Orphan (protOf K rt s.act) s.r.G g) :
    ∀ g, ¬ Orphan (protOf K rt (relStep K rt cand u s).1.act) (relStep K rt cand u s).1.r.G g := by
  have hwfw : (waveStep u s.r).1.G.WF := hwf
  obtain ⟨g1, _, _⟩ := retireList_G (cand s.r (waveStep u s.r).1) (waveStep u s.r).1 hwfw
  refine releaseLoop_orphanFree (protOf K rt s.act) _ _ _ g1 (relFuel_enough _ _) ?_
  intro g ho
  rcases orphan_retireList (protOf K rt s.act) (cand s.r (waveStep u s.r).1)
    (waveStep u s.r).1 g ho with h1 | h1
  · exact absurd h1 (h g)
  · exact h1

omit [OrderBot α] in
/-- Root-action retirement at a query leaves no orphan: the cascade started from the gates
of the deactivated actions, with fuel `relFuel`, reaches its fixed point. -/
theorem qRetire_orphanFree (s : QS α) (hwf : s.r.G.WF)
    (h : ∀ g, ¬ Orphan (protOf K rt s.act) s.r.G g) :
    ∀ g, ¬ Orphan (protOf K rt (qRetire K rt s).1.act) (qRetire K rt s).1.r.G g := by
  unfold qRetire
  cases leadScan (fun i => s.r.lo.val (rt i)) s.act K with
  | none => exact h
  | some a =>
    refine releaseLoop_orphanFree _ _ _ _ hwf (relFuel_enough _ _) ?_
    intro g ho
    obtain ⟨o1, o2, o3⟩ := ho
    have hold : protOf K rt s.act g = true := by
      by_contra hne
      exact h g ⟨o1, o2, by simpa using hne⟩
    unfold protOf at hold
    rw [List.any_eq_true] at hold
    obtain ⟨i, hi, hia⟩ := hold
    rw [Bool.and_eq_true, decide_eq_true_eq] at hia
    have hiK := List.mem_range.1 hi
    have hd : deact K a (fun i => s.r.hi.val (rt i)) (s.r.lo.val (rt a)) s.act i = false := by
      by_contra hne
      exact protOf_false o3 i hiK (by simpa using hne) hia.2
    have hc := (deact_false_iff K a _ _ s.act i hia.1).1 hd
    unfold retiredRoots
    rw [List.mem_map]
    exact ⟨i, List.mem_filter.2 ⟨hi, decide_eq_true ⟨hia.1, hc.2.1, hc.2.2⟩⟩, hia.2⟩

variable {G0 : Dag} {cand : RState α → RState α → List (ℕ × ℕ)} {u : ℕ → ℕ × α × α}
  {q : ℕ → Bool} {lo0 hi0 : EState α} {act0 : ℕ → Bool}

/-- **The cascade is complete along the run** (`prop:uct-coupling`: "reference counting may
release a node only if it no longer lies in the active descendants of any protected original
root action", together with the converse).  Assume that initially every parentless internal
gate is the gate of an active root action.  Then at every time the live circuit of the
Graph-Selective engine has no orphan. -/
theorem runF_orphanFree (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩)
    (hof : ∀ g, ¬ Orphan (protOf K rt act0) G0 g) : ∀ t g,
    ¬ Orphan (protOf K rt (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).act)
      (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G g := by
  intro t
  induction t with
  | zero => exact hof
  | succ t ih =>
    have hrun := runF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0) hG h0 hn t
    show ∀ g, ¬ Orphan (protOf K rt (relStep K rt cand (u (t + 1)) _).1.act)
      (relStep K rt cand (u (t + 1)) _).1.r.G g
    by_cases hq : q t = true
    · rw [ite_eq_left hq]
      exact relStep_orphanFree cand _ _ (qRetire_cost (K := K) (rt := rt) hrun.wf).1
        (qRetire_orphanFree _ hrun.wf ih)
    · rw [ite_eq_right hq]
      exact relStep_orphanFree cand _ _ hrun.wf ih

/-- **Exactly the orphaned gates are released.**  Under the hypothesis of
`runF_orphanFree`, at every time every gate that still has live children is reachable from
the gate of an active root action through live incidences; in particular every gate that
is not so reachable has been released (or is a terminal). -/
theorem runF_live_anchored (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩)
    (hof : ∀ g, ¬ Orphan (protOf K rt act0) G0 g) (t g : ℕ)
    (hg : (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G.children g ≠ []) :
    Anch (protOf K rt (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).act)
      (runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G g :=
  anch_of_orphanFree
    (runF_inv (K := K) (rt := rt) (cand := cand) (q := q) (act0 := act0) hG h0 hn t).wf
    (runF_orphanFree hG h0 hn hof t) g hg

end CascadeRun

/-! ## 3. A wave scheduler without empty-bucket scans -/

section Sparse

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Worklist charge per delivery and per extraction: `⌈log₂ (L + 1)⌉ + 3`. -/
def kap (G : Dag) : ℕ := Nat.clog 2 (G.L + 1) + 3

/-- **Queue a level.**  Test whether level `l` is already in the level queue (1 unit, a read
of the position map); if not, insert it with key `L - l` by `HeapImpl.insert` (computed
cost). -/
def qPush (G : Dag) (Q : Heap ℕ ℕ) (l : ℕ) : Heap ℕ ℕ × ℕ :=
  if Q.pos l = none then
    ((HeapImpl.insert Q l (G.L - l)).1, (HeapImpl.insert Q l (G.L - l)).2 + 1)
  else (Q, 1)

/-- Queue the levels of the gates of a list. -/
def qPushAll (G : Dag) : List ℕ → Heap ℕ ℕ → Heap ℕ ℕ × ℕ
  | [], Q => (Q, 0)
  | p :: ps, Q =>
    ((qPushAll G ps (qPush G Q (G.level p)).1).1,
     (qPush G Q (G.level p)).2 + (qPushAll G ps (qPush G Q (G.level p)).1).2)

/-- The buckets after pushing the gates of a list (the bucket component of
`CostEngines.push` and `HeapImpl.pushH`). -/
def bkPush (G : Dag) : List ℕ → (ℕ → List ℕ) → ℕ → List ℕ
  | [], bk => bk
  | p :: ps, bk => bkPush G ps (fun l => if l = G.level p then p :: bk l else bk l)

/-- The level queue stores exactly the levels `l` with `ℓ ≤ l ≤ L` whose bucket is
nonempty, with key `L - l`. -/
structure QOK (G : Dag) (Q : Heap ℕ ℕ) (ℓ : ℕ) (bk : ℕ → List ℕ) : Prop where
  inv : Q.Inv
  look : ∀ l, Q.lookup l = if ℓ ≤ l ∧ l ≤ G.L ∧ bk l ≠ [] then some (G.L - l) else none

lemma QOK.size {G : Dag} {Q : Heap ℕ ℕ} {ℓ : ℕ} {bk : ℕ → List ℕ} (h : QOK G Q ℓ bk) :
    Q.n ≤ G.L + 1 := by
  have h1 := heap_size_le_card h.inv
    ((range (G.L + 1)).filter (fun l => ℓ ≤ l ∧ bk l ≠ [])) (fun l => G.L - l) (by
      intro l
      rw [h.look l]
      by_cases hc : ℓ ≤ l ∧ l ≤ G.L ∧ bk l ≠ []
      · rw [ite_eq_left hc, ite_eq_left (mem_filter.2 ⟨mem_range.2 (by omega), hc.1, hc.2.2⟩)]
      · rw [ite_eq_right hc, ite_eq_right]
        intro hm
        obtain ⟨m1, m2, m3⟩ := mem_filter.1 hm
        have := mem_range.1 m1
        exact hc ⟨m2, by omega, m3⟩)
  have h2 := card_filter_le (range (G.L + 1)) (fun l => ℓ ≤ l ∧ bk l ≠ [])
  rw [card_range] at h2
  omega

lemma qPush_spec {G : Dag} {Q : Heap ℕ ℕ} {ℓ : ℕ} {bk : ℕ → List ℕ} (h : QOK G Q ℓ bk)
    (p : ℕ) (hl : ℓ ≤ G.level p) (hL : G.level p ≤ G.L) :
    QOK G (qPush G Q (G.level p)).1 ℓ (fun l => if l = G.level p then p :: bk l else bk l) ∧
    (qPush G Q (G.level p)).2 ≤ kap G ∧ 1 ≤ (qPush G Q (G.level p)).2 := by
  unfold qPush
  by_cases hp : Q.pos (G.level p) = none
  · rw [ite_eq_left hp]
    obtain ⟨i1, i2, i3⟩ := HeapImpl.insert_spec h.inv (G.level p) (G.L - G.level p) hp
    have hc := HeapImpl.insert_cost Q (G.level p) (G.L - G.level p)
    have hQ' : QOK G (HeapImpl.insert Q (G.level p) (G.L - G.level p)).1 ℓ
        (fun l => if l = G.level p then p :: bk l else bk l) := by
      refine ⟨i1, fun l => ?_⟩
      rw [i3 l, h.look l]
      by_cases e : l = G.level p
      · rw [e]
        simp [hl, hL]
      · simp [e]
    have hsz := hQ'.size
    rw [i2] at hsz
    have hm := Nat.clog_mono_right 2 hsz
    refine ⟨hQ', ?_, Nat.le_add_left _ _⟩
    show (HeapImpl.insert Q (G.level p) (G.L - G.level p)).2 + 1 ≤ kap G
    unfold kap
    omega
  · rw [ite_eq_right hp]
    refine ⟨⟨h.inv, fun l => ?_⟩, ?_, le_rfl⟩
    · rw [h.look l]
      by_cases e : l = G.level p
      · have hlk : Q.lookup (G.level p) ≠ none := by
          unfold Heap.lookup
          cases hq : Q.pos (G.level p) with
          | none => exact absurd hq hp
          | some i => simp
        have hcond : ℓ ≤ G.level p ∧ G.level p ≤ G.L ∧ bk (G.level p) ≠ [] := by
          by_contra hn
          rw [h.look, ite_eq_right hn] at hlk
          exact hlk rfl
        rw [e, ite_eq_left hcond]
        simp [hl, hL]
      · simp [e]
    · show 1 ≤ kap G
      unfold kap
      omega

theorem qPushAll_spec {G : Dag} (ℓ : ℕ) : ∀ (ps : List ℕ) (Q : Heap ℕ ℕ) (bk : ℕ → List ℕ),
    QOK G Q ℓ bk → (∀ p ∈ ps, ℓ ≤ G.level p ∧ G.level p ≤ G.L) →
    QOK G (qPushAll G ps Q).1 ℓ (bkPush G ps bk) ∧
    (qPushAll G ps Q).2 ≤ kap G * ps.length ∧ ps.length ≤ (qPushAll G ps Q).2 := by
  intro ps
  induction ps with
  | nil => intro Q bk h _; exact ⟨h, Nat.zero_le _, Nat.zero_le _⟩
  | cons p ps ih =>
    intro Q bk h hps
    obtain ⟨a1, a2, a3⟩ := qPush_spec h p (hps p List.mem_cons_self).1
      (hps p List.mem_cons_self).2
    obtain ⟨b1, b2, b3⟩ := ih _ _ a1 (fun q hq => hps q (List.mem_cons_of_mem _ hq))
    refine ⟨b1, ?_, ?_⟩
    · show (qPush G Q (G.level p)).2 + (qPushAll G ps (qPush G Q (G.level p)).1).2
        ≤ kap G * (ps.length + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · show ps.length + 1 ≤ (qPush G Q (G.level p)).2
        + (qPushAll G ps (qPush G Q (G.level p)).1).2
      omega

omit [OrderBot α] in
lemma pushH_bk (G : Dag) (g : ℕ) (y : α) : ∀ (ps : List ℕ) (hp : ℕ → Heap ℕ α)
    (bk : ℕ → List ℕ), (HeapImpl.pushH G g y ps hp bk).2.1 = bkPush G ps bk := by
  intro ps
  induction ps with
  | nil => intro hp bk; rfl
  | cons p ps ih =>
    intro hp bk
    show (HeapImpl.pushH G g y ps (Function.update hp p (HeapImpl.updateKey (hp p) g y).1)
      (fun l => if l = G.level p then p :: bk l else bk l)).2.1
      = bkPush G ps (fun l => if l = G.level p then p :: bk l else bk l)
    exact ih _ _

lemma bkPush_len (G : Dag) (I : Finset ℕ) : ∀ (ps : List ℕ) (bk : ℕ → List ℕ),
    (∀ p ∈ ps, G.level p ∈ I) →
    ∑ l ∈ I, (bkPush G ps bk l).length = ∑ l ∈ I, (bk l).length + ps.length := by
  intro ps
  induction ps with
  | nil => intro bk _; simp [bkPush]
  | cons p ps ih =>
    intro bk hI
    have hp : G.level p ∈ I := hI p (List.mem_cons.2 (Or.inl rfl))
    show ∑ l ∈ I, (bkPush G ps (fun l => if l = G.level p then p :: bk l else bk l) l).length
      = _
    rw [ih _ (fun q hq => hI q (List.mem_cons_of_mem _ hq))]
    have hlen : ∀ l, (if l = G.level p then p :: bk l else bk l).length
        = (bk l).length + (if l = G.level p then 1 else 0) := by
      intro l
      split_ifs <;> simp
    simp only [hlen, sum_add_distrib, sum_ite_eq', hp, ite_true, List.length_cons]
    omega

/-- State after gate `g` takes its target value and delivers it (as in
`HeapImpl.procListH`). -/
def chgSt (G : Dag) (x : ℕ) (y : α) (s : HEState α) (bk : ℕ → List ℕ) (g : ℕ) : HEState α :=
  ⟨fun g' => if g' = g then HeapImpl.targetH G x y s g else s.val g',
    (HeapImpl.pushH G g (HeapImpl.targetH G x y s g) (G.parents g) s.hp bk).1⟩

/-- **Processing one bucket, with the level queue.**  As `HeapImpl.procListH`; in addition
every delivery to a parent `p` queues the level of `p` (`qPush`). -/
def procListS (G : Dag) (x : ℕ) (y : α) :
    List ℕ → HEState α → (ℕ → List ℕ) → Heap ℕ ℕ → HEState α × (ℕ → List ℕ) × Heap ℕ ℕ × ℕ
  | [], s, bk, Q => (s, bk, Q, 0)
  | g :: rest, s, bk, Q =>
    if HeapImpl.targetH G x y s g = s.val g then
      ((procListS G x y rest s bk Q).1, (procListS G x y rest s bk Q).2.1,
        (procListS G x y rest s bk Q).2.2.1, (procListS G x y rest s bk Q).2.2.2 + 1)
    else
      ((procListS G x y rest (chgSt G x y s bk g) (bkPush G (G.parents g) bk)
          (qPushAll G (G.parents g) Q).1).1,
       (procListS G x y rest (chgSt G x y s bk g) (bkPush G (G.parents g) bk)
          (qPushAll G (G.parents g) Q).1).2.1,
       (procListS G x y rest (chgSt G x y s bk g) (bkPush G (G.parents g) bk)
          (qPushAll G (G.parents g) Q).1).2.2.1,
       (procListS G x y rest (chgSt G x y s bk g) (bkPush G (G.parents g) bk)
          (qPushAll G (G.parents g) Q).1).2.2.2 + 1
        + (HeapImpl.pushH G g (HeapImpl.targetH G x y s g) (G.parents g) s.hp bk).2.2
        + (qPushAll G (G.parents g) Q).2)

/-- `procListS` computes the state and the buckets of `HeapImpl.procListH`. -/
lemma procListS_sim (G : Dag) (x : ℕ) (y : α) : ∀ (rest : List ℕ) (s : HEState α)
    (bk : ℕ → List ℕ) (Q : Heap ℕ ℕ),
    (procListS G x y rest s bk Q).1 = (HeapImpl.procListH G x y rest s bk).1 ∧
    (procListS G x y rest s bk Q).2.1 = (HeapImpl.procListH G x y rest s bk).2.1 := by
  intro rest
  induction rest with
  | nil => intro s bk Q; exact ⟨rfl, rfl⟩
  | cons g rest ih =>
    intro s bk Q
    by_cases heq : HeapImpl.targetH G x y s g = s.val g
    · rw [procListS, HeapImpl.procListH, ite_eq_left heq, ite_eq_left heq]
      exact ih s bk Q
    · rw [procListS, HeapImpl.procListH, ite_eq_right heq, ite_eq_right heq, pushH_bk]
      exact ih _ _ _

/-- **One bucket with the level queue**: the queue invariant is kept, the extra cost over
`procListH` is at most `kap G` per delivery, and every delivery costs at least one unit. -/
theorem procListS_spec (G : Dag) (x : ℕ) (y : α) (ℓ : ℕ) : ∀ (rest : List ℕ) (s : HEState α)
    (bk : ℕ → List ℕ) (Q : Heap ℕ ℕ), QOK G Q ℓ bk →
    (∀ g ∈ rest, ∀ p ∈ G.parents g, ℓ ≤ G.level p ∧ G.level p ≤ G.L) →
    QOK G (procListS G x y rest s bk Q).2.2.1 ℓ (procListS G x y rest s bk Q).2.1 ∧
    (procListS G x y rest s bk Q).2.2.2 + kap G * pendSum G ℓ bk
      ≤ (HeapImpl.procListH G x y rest s bk).2.2
        + kap G * pendSum G ℓ (procListS G x y rest s bk Q).2.1 ∧
    pendSum G ℓ (procListS G x y rest s bk Q).2.1
      ≤ pendSum G ℓ bk + (procListS G x y rest s bk Q).2.2.2 := by
  intro rest
  induction rest with
  | nil => intro s bk Q h _; exact ⟨h, le_rfl, Nat.le_add_right _ _⟩
  | cons g rest ih =>
    intro s bk Q h hr
    by_cases heq : HeapImpl.targetH G x y s g = s.val g
    · rw [procListS, HeapImpl.procListH, ite_eq_left heq, ite_eq_left heq]
      obtain ⟨i1, i2, i3⟩ := ih s bk Q h (fun g' hg' => hr g' (List.mem_cons_of_mem _ hg'))
      refine ⟨i1, ?_, ?_⟩
      · show (procListS G x y rest s bk Q).2.2.2 + 1 + kap G * pendSum G ℓ bk
          ≤ (HeapImpl.procListH G x y rest s bk).2.2 + 1
            + kap G * pendSum G ℓ (procListS G x y rest s bk Q).2.1
        omega
      · show pendSum G ℓ (procListS G x y rest s bk Q).2.1
          ≤ pendSum G ℓ bk + ((procListS G x y rest s bk Q).2.2.2 + 1)
        omega
    · rw [procListS, HeapImpl.procListH, ite_eq_right heq, ite_eq_right heq, pushH_bk]
      obtain ⟨q1, q2, q3⟩ := qPushAll_spec ℓ (G.parents g) Q bk h (hr g List.mem_cons_self)
      have hlen : pendSum G ℓ (bkPush G (G.parents g) bk)
          = pendSum G ℓ bk + (G.parents g).length := by
        unfold pendSum
        apply bkPush_len
        intro p hp
        have := hr g List.mem_cons_self p hp
        rw [mem_Ico]
        omega
      obtain ⟨i1, i2, i3⟩ := ih (chgSt G x y s bk g) (bkPush G (G.parents g) bk)
        (qPushAll G (G.parents g) Q).1 q1 (fun g' hg' => hr g' (List.mem_cons_of_mem _ hg'))
      rw [hlen, Nat.mul_add] at i2
      rw [hlen] at i3
      refine ⟨i1, ?_, ?_⟩
      · show (procListS G x y rest (chgSt G x y s bk g) (bkPush G (G.parents g) bk)
            (qPushAll G (G.parents g) Q).1).2.2.2 + 1
            + (HeapImpl.pushH G g (HeapImpl.targetH G x y s g) (G.parents g) s.hp bk).2.2
            + (qPushAll G (G.parents g) Q).2 + kap G * pendSum G ℓ bk
          ≤ (HeapImpl.procListH G x y rest (chgSt G x y s bk g)
              (bkPush G (G.parents g) bk)).2.2 + 1
            + (HeapImpl.pushH G g (HeapImpl.targetH G x y s g) (G.parents g) s.hp bk).2.2
            + kap G * pendSum G ℓ (procListS G x y rest (chgSt G x y s bk g)
                (bkPush G (G.parents g) bk) (qPushAll G (G.parents g) Q).1).2.1
        omega
      · show pendSum G ℓ (procListS G x y rest (chgSt G x y s bk g)
            (bkPush G (G.parents g) bk) (qPushAll G (G.parents g) Q).1).2.1
          ≤ pendSum G ℓ bk + ((procListS G x y rest (chgSt G x y s bk g)
            (bkPush G (G.parents g) bk) (qPushAll G (G.parents g) Q).1).2.2.2 + 1
            + (HeapImpl.pushH G g (HeapImpl.targetH G x y s g) (G.parents g) s.hp bk).2.2
            + (qPushAll G (G.parents g) Q).2)
        omega

/-- **Extract the lowest pending level and process its bucket.** -/
def popS (G : Dag) (x : ℕ) (y : α) (s : HEState α) (bk : ℕ → List ℕ) (Q : Heap ℕ ℕ) :
    HEState α × (ℕ → List ℕ) × Heap ℕ ℕ × ℕ :=
  procListS G x y (bk (G.L - findMax Q)) s bk (HeapImpl.delete Q (G.L - findMax Q)).1

/-- **Sparse sweep.**  While the level queue is nonempty (test and root read: 1 unit):
delete its root (the lowest pending level, `HeapImpl.delete`, computed cost) and process
the bucket of that level.  The first argument is recursion fuel (`L + 1` suffices, since
the extracted levels increase strictly); it is not charged. -/
def sweepS (G : Dag) (x : ℕ) (y : α) :
    ℕ → HEState α → (ℕ → List ℕ) → Heap ℕ ℕ → HEState α × ℕ
  | 0, s, _, _ => (s, 0)
  | f + 1, s, bk, Q =>
    if Q.n = 0 then (s, 1)
    else
      ((sweepS G x y f (popS G x y s bk Q).1 (popS G x y s bk Q).2.1
          (popS G x y s bk Q).2.2.1).1,
       (sweepS G x y f (popS G x y s bk Q).1 (popS G x y s bk Q).2.1
          (popS G x y s bk Q).2.2.1).2
        + 1 + (HeapImpl.delete Q (G.L - findMax Q)).2 + (popS G x y s bk Q).2.2.2)

/-- The initial buckets of a wave: the updated terminal `x` on the bucket of its level. -/
def bk0 (G : Dag) (x : ℕ) : ℕ → List ℕ := fun l => if l = G.level x then [x] else []

/-- **One backup wave with the sparse scheduler**: process the updated terminal `x`
(with an empty level queue), then run the sparse sweep; one unit for the set-up. -/
def waveS (G : Dag) (x : ℕ) (y : α) (s : HEState α) : HEState α × ℕ :=
  ((sweepS G x y (G.L + 1)
      (procListS G x y [x] s (bk0 G x) (Heap.empty : Heap ℕ ℕ)).1
      (procListS G x y [x] s (bk0 G x) (Heap.empty : Heap ℕ ℕ)).2.1
      (procListS G x y [x] s (bk0 G x) (Heap.empty : Heap ℕ ℕ)).2.2.1).1,
   (sweepS G x y (G.L + 1)
      (procListS G x y [x] s (bk0 G x) (Heap.empty : Heap ℕ ℕ)).1
      (procListS G x y [x] s (bk0 G x) (Heap.empty : Heap ℕ ℕ)).2.1
      (procListS G x y [x] s (bk0 G x) (Heap.empty : Heap ℕ ℕ)).2.2.1).2
    + 1 + (procListS G x y [x] s (bk0 G x) (Heap.empty : Heap ℕ ℕ)).2.2.2)

/-! ### Relation with the level sweep -/

lemma wl_succ (G : Dag) (x : ℕ) (y : α) (l : ℕ) (s : EState α) (bk : ℕ → List ℕ) :
    waveLevels G x y (l + 1) s bk
      = ((procList G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
            (waveLevels G x y l s bk).2.1).1,
         (procList G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
            (waveLevels G x y l s bk).2.1).2.1,
         (waveLevels G x y l s bk).2.2 + 1
          + (procList G x y ((waveLevels G x y l s bk).2.1 l) (waveLevels G x y l s bk).1
              (waveLevels G x y l s bk).2.1).2.2) := rfl

lemma wlH_succ (G : Dag) (x : ℕ) (y : α) (l : ℕ) (s : HEState α) (bk : ℕ → List ℕ) :
    HeapImpl.waveLevelsH G x y (l + 1) s bk
      = ((HeapImpl.procListH G x y ((HeapImpl.waveLevelsH G x y l s bk).2.1 l)
            (HeapImpl.waveLevelsH G x y l s bk).1 (HeapImpl.waveLevelsH G x y l s bk).2.1).1,
         (HeapImpl.procListH G x y ((HeapImpl.waveLevelsH G x y l s bk).2.1 l)
            (HeapImpl.waveLevelsH G x y l s bk).1 (HeapImpl.waveLevelsH G x y l s bk).2.1).2.1,
         (HeapImpl.waveLevelsH G x y l s bk).2.2 + 1
          + (HeapImpl.procListH G x y ((HeapImpl.waveLevelsH G x y l s bk).2.1 l)
              (HeapImpl.waveLevelsH G x y l s bk).1
              (HeapImpl.waveLevelsH G x y l s bk).2.1).2.2) := rfl

/-- The level sweep does nothing but count on a run of empty buckets. -/
lemma skipA (G : Dag) (x : ℕ) (y : α) (s : EState α) (bk : ℕ → List ℕ) (ℓ : ℕ) :
    ∀ m, ℓ ≤ m → (∀ l, ℓ ≤ l → l < m → (waveLevels G x y ℓ s bk).2.1 l = []) →
    (waveLevels G x y m s bk).1 = (waveLevels G x y ℓ s bk).1 ∧
    (waveLevels G x y m s bk).2.1 = (waveLevels G x y ℓ s bk).2.1 ∧
    (waveLevels G x y m s bk).2.2 + ℓ = (waveLevels G x y ℓ s bk).2.2 + m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ m hm ih =>
    intro hb
    obtain ⟨i1, i2, i3⟩ := ih (fun l h1 h2 => hb l h1 (by omega))
    have hbm : (waveLevels G x y m s bk).2.1 m = [] := by
      rw [i2]
      exact hb m hm (Nat.lt_succ_self m)
    rw [wl_succ, hbm]
    refine ⟨i1, i2, ?_⟩
    show (waveLevels G x y m s bk).2.2 + 1 + 0 + ℓ = (waveLevels G x y ℓ s bk).2.2 + (m + 1)
    omega

lemma skipH (G : Dag) (x : ℕ) (y : α) (s : HEState α) (bk : ℕ → List ℕ) (ℓ : ℕ) :
    ∀ m, ℓ ≤ m → (∀ l, ℓ ≤ l → l < m → (HeapImpl.waveLevelsH G x y ℓ s bk).2.1 l = []) →
    (HeapImpl.waveLevelsH G x y m s bk).1 = (HeapImpl.waveLevelsH G x y ℓ s bk).1 ∧
    (HeapImpl.waveLevelsH G x y m s bk).2.1 = (HeapImpl.waveLevelsH G x y ℓ s bk).2.1 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro _; exact ⟨rfl, rfl⟩
  | succ m hm ih =>
    intro hb
    obtain ⟨i1, i2⟩ := ih (fun l h1 h2 => hb l h1 (by omega))
    have hbm : (HeapImpl.waveLevelsH G x y m s bk).2.1 m = [] := by
      rw [i2]
      exact hb m hm (Nat.lt_succ_self m)
    rw [wlH_succ, hbm]
    exact ⟨i1, i2⟩

/-! ### Counting the deliveries of a bucket -/

variable {G : Dag} {x : ℕ} {y : α}

omit [OrderBot α] in
lemma vol_step {s0 s : EState α} {g : ℕ} (hgN : g < G.N) (hs0 : s.val g = s0.val g)
    (v : ℕ → α) (k : ℕ → ℕ → α) (hv : ∀ h', h' ≠ g → v h' = s.val h') (hvg : v g ≠ s.val g) :
    vol G s0 ⟨v, k⟩ = vol G s0 s + (G.parents g).length := by
  have hfil : (range G.N).filter (fun h' => v h' ≠ s0.val h')
      = insert g ((range G.N).filter (fun h' => s.val h' ≠ s0.val h')) := by
    ext h'
    simp only [mem_filter, mem_range, mem_insert]
    by_cases hh : h' = g
    · subst hh
      constructor
      · exact fun _ => Or.inl rfl
      · exact fun _ => ⟨hgN, by rw [← hs0]; exact hvg⟩
    · rw [hv h' hh]
      constructor
      · exact fun h1 => Or.inr h1
      · rintro (h1 | h1)
        · exact absurd h1 hh
        · exact h1
  have hnot : g ∉ (range G.N).filter (fun h' => s.val h' ≠ s0.val h') := by
    intro hm
    exact (mem_filter.1 hm).2 hs0
  change ∑ g' ∈ (range G.N).filter (fun h' => v h' ≠ s0.val h'), (G.parents g').length = _
  rw [hfil, sum_insert hnot, add_comm]
  rfl

/-- **One bucket: number of deliveries.**  The agenda entries created at higher levels are
exactly the deliveries of the gates that changed. -/
theorem procList_vol (hG : G.WF) (s0 : EState α) (ℓ : ℕ) :
    ∀ (rest : List ℕ) (s : EState α) (bk : ℕ → List ℕ), PInv G x y s0 ℓ rest s bk →
      pendSum G (ℓ + 1) (procList G x y rest s bk).2.1 + vol G s0 s
        = pendSum G (ℓ + 1) bk + vol G s0 (procList G x y rest s bk).1 := by
  intro rest
  induction rest with
  | nil => intro s bk _; rfl
  | cons g rest ih =>
    intro s bk h
    by_cases heq : target G x y s g = s.val g
    · rw [procList_same rest heq]
      exact ih s bk (h.step_same heq)
    · rw [procList_change rest heq]
      have h2 := ih _ _ (h.step_change hG heq)
      have hgl : G.level g = ℓ ∧ g < G.N := h.rst g (List.mem_cons.2 (Or.inl rfl))
      have hs0 : s.val g = s0.val g := by
        by_contra hc
        exact heq (h.chg g hc).2.1.symm
      have e1 := vol_step (G := G) (s0 := s0) (s := s) hgl.2 hs0 (stepVal G x y s g)
        (push G g (target G x y s g) (G.parents g) s.key bk).1
        (fun h' hh => by unfold stepVal; exact ite_eq_right hh)
        (by unfold stepVal; rw [ite_eq_left rfl]; exact heq)
      have e2 : pendSum G (ℓ + 1) (push G g (target G x y s g) (G.parents g) s.key bk).2.1
          = pendSum G (ℓ + 1) bk + (G.parents g).length := by
        unfold pendSum
        apply push_len
        intro p hp
        have := hG.level_lt p g ((hG.parents_iff g p).1 hp)
        have := hG.level_le p
        rw [mem_Ico]
        omega
      show pendSum G (ℓ + 1) (procList G x y rest
            ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
            (push G g (target G x y s g) (G.parents g) s.key bk).2.1).2.1 + vol G s0 s
        = pendSum G (ℓ + 1) bk + vol G s0 (procList G x y rest
            ⟨stepVal G x y s g, (push G g (target G x y s g) (G.parents g) s.key bk).1⟩
            (push G g (target G x y s g) (G.parents g) s.key bk).2.1).1
      omega

/-! ### The sparse sweep computes the level sweep -/

/-- **The sparse sweep.**  Started at position `ℓ` of the level sweep with a level queue
holding the nonempty buckets from `ℓ` on, it ends in the final state of the level sweep;
the cost statement is in "cost to go" form. -/
theorem sweepS_spec (hG : G.WF) {hs : HEState α} {s0 : EState α} (bkI : ℕ → List ℕ)
    (hsim : SimE G hs s0)
    (hP : ∀ ℓ, ℓ ≤ G.L + 1 → PInv G x y s0 ℓ ((waveLevels G x y ℓ s0 bkI).2.1 ℓ)
      (waveLevels G x y ℓ s0 bkI).1 (waveLevels G x y ℓ s0 bkI).2.1) :
    ∀ (f ℓ : ℕ) (Q : Heap ℕ ℕ), ℓ ≤ G.L + 1 → G.L + 1 ≤ ℓ + f →
      QOK G Q ℓ (waveLevels G x y ℓ s0 bkI).2.1 →
      (sweepS G x y f (HeapImpl.waveLevelsH G x y ℓ hs bkI).1
          (HeapImpl.waveLevelsH G x y ℓ hs bkI).2.1 Q).1
        = (HeapImpl.waveLevelsH G x y (G.L + 1) hs bkI).1 ∧
      (sweepS G x y f (HeapImpl.waveLevelsH G x y ℓ hs bkI).1
          (HeapImpl.waveLevelsH G x y ℓ hs bkI).2.1 Q).2
          + 2 * (waveLevels G x y ℓ s0 bkI).2.2 + 2 * (G.L + 1)
          + 2 * (kap G * vol G s0 (waveLevels G x y ℓ s0 bkI).1)
        ≤ 1 + 2 * (waveLevels G x y (G.L + 1) s0 bkI).2.2 + 2 * ℓ
          + 2 * (kap G * vol G s0 (waveLevels G x y (G.L + 1) s0 bkI).1)
          + kap G * pendSum G ℓ (waveLevels G x y ℓ s0 bkI).2.1 ∧
      vol G s0 (waveLevels G x y (G.L + 1) s0 bkI).1
        ≤ (sweepS G x y f (HeapImpl.waveLevelsH G x y ℓ hs bkI).1
            (HeapImpl.waveLevelsH G x y ℓ hs bkI).2.1 Q).2
          + vol G s0 (waveLevels G x y ℓ s0 bkI).1 := by
  intro f
  induction f with
  | zero =>
    intro ℓ Q h1 h2 _
    have e : ℓ = G.L + 1 := by omega
    subst e
    refine ⟨rfl, ?_, ?_⟩
    · show 0 + _ + _ + _ ≤ _
      omega
    · show _ ≤ 0 + _
      omega
  | succ f ih =>
    intro ℓ Q h1 h2 hQ
    obtain ⟨_, hbkeq, _⟩ := HeapImpl.waveLevelsH_spec G x y hs s0 bkI hsim ℓ
    rw [sweepS]
    by_cases hn : Q.n = 0
    · rw [ite_eq_left hn]
      have hemp : ∀ l, ℓ ≤ l → l < G.L + 1 → (waveLevels G x y ℓ s0 bkI).2.1 l = [] := by
        intro l hl1 hl2
        by_contra hne
        have hlk := hQ.look l
        rw [ite_eq_left ⟨hl1, by omega, hne⟩] at hlk
        unfold Heap.lookup at hlk
        cases hp : Q.pos l with
        | none => rw [hp] at hlk; simp at hlk
        | some i =>
          have := (hQ.inv.posOK.bwd l i hp).1
          omega
      obtain ⟨a1, _, a3⟩ := skipA G x y s0 bkI ℓ (G.L + 1) h1 hemp
      obtain ⟨b1, _⟩ := skipH G x y hs bkI ℓ (G.L + 1) h1 (by rw [hbkeq]; exact hemp)
      rw [a1]
      refine ⟨b1.symm, ?_, ?_⟩
      · show 1 + _ + _ + _ ≤ _
        omega
      · show _ ≤ 1 + _
        omega
    · rw [ite_eq_right hn]
      obtain ⟨fm1, fm2⟩ := HeapImpl.findMax_spec hQ.inv
      obtain ⟨h, hh⟩ := fm2 (Nat.pos_of_ne_zero hn)
      have hcond : ℓ ≤ h ∧ h ≤ G.L ∧ (waveLevels G x y ℓ s0 bkI).2.1 h ≠ [] := by
        by_contra hc
        rw [hQ.look h, ite_eq_right hc] at hh
        exact absurd hh (by simp)
      have hlkne : Q.lookup h ≠ none := by
        rw [hQ.look h, ite_eq_left hcond]
        simp
      rw [hQ.look h, ite_eq_left hcond] at hh
      have hk : G.L - h = findMax Q := Option.some.inj hh
      have hℓ' : G.L - findMax Q = h := by omega
      have hmin : ∀ l, ℓ ≤ l → l < h → (waveLevels G x y ℓ s0 bkI).2.1 l = [] := by
        intro l hl1 hl2
        by_contra hne
        have := fm1 l (G.L - l) (by rw [hQ.look l, ite_eq_left ⟨hl1, by omega, hne⟩])
        omega
      obtain ⟨a1, a2, a3⟩ := skipA G x y s0 bkI ℓ h hcond.1 hmin
      obtain ⟨b1, b2⟩ := skipH G x y hs bkI ℓ h hcond.1 (by rw [hbkeq]; exact hmin)
      obtain ⟨simh, bkh, _⟩ := HeapImpl.waveLevelsH_spec G x y hs s0 bkI hsim h
      obtain ⟨_, bkh1, _⟩ := HeapImpl.waveLevelsH_spec G x y hs s0 bkI hsim (h + 1)
      have hPh := hP h (by omega)
      obtain ⟨d1, _, d3⟩ := HeapImpl.delete_spec hQ.inv h hlkne
      have dcost := HeapImpl.delete_cost Q h
      have hsz := hQ.size
      have hdc : (HeapImpl.delete Q h).2 + 1 ≤ kap G := by
        have := Nat.clog_mono_right 2 hsz
        unfold kap
        omega
      have hQd : QOK G (HeapImpl.delete Q h).1 (h + 1) (waveLevels G x y h s0 bkI).2.1 := by
        rw [a2]
        refine ⟨d1, fun l => ?_⟩
        rw [d3 l]
        by_cases e : l = h
        · rw [ite_eq_left e, ite_eq_right (fun c => by have := c.1; omega)]
        · rw [ite_eq_right e, hQ.look l]
          by_cases c : h + 1 ≤ l ∧ l ≤ G.L ∧ (waveLevels G x y ℓ s0 bkI).2.1 l ≠ []
          · rw [ite_eq_left c, ite_eq_left ⟨by omega, c.2.1, c.2.2⟩]
          · rw [ite_eq_right c, ite_eq_right]
            intro c'
            by_cases hlt : l < h
            · exact c'.2.2 (hmin l c'.1 hlt)
            · exact c ⟨by omega, c'.2.1, c'.2.2⟩
      have hrest : ∀ g ∈ (waveLevels G x y h s0 bkI).2.1 h, ∀ p ∈ G.parents g,
          h + 1 ≤ G.level p ∧ G.level p ≤ G.L := by
        intro g hg p hp
        have := (hPh.rst g hg).1
        have := hG.level_lt p g ((hG.parents_iff g p).1 hp)
        exact ⟨by omega, hG.level_le p⟩
      obtain ⟨s1, s2⟩ := procListS_sim G x y ((waveLevels G x y h s0 bkI).2.1 h)
        (HeapImpl.waveLevelsH G x y h hs bkI).1 (waveLevels G x y h s0 bkI).2.1
        (HeapImpl.delete Q h).1
      obtain ⟨p1, p2, p3⟩ := procListS_spec G x y (h + 1) ((waveLevels G x y h s0 bkI).2.1 h)
        (HeapImpl.waveLevelsH G x y h hs bkI).1 (waveLevels G x y h s0 bkI).2.1
        (HeapImpl.delete Q h).1 hQd hrest
      obtain ⟨_, _, ph3⟩ := HeapImpl.procListH_spec G x y ((waveLevels G x y h s0 bkI).2.1 h)
        (HeapImpl.waveLevelsH G x y h hs bkI).1 (waveLevels G x y h s0 bkI).1
        (waveLevels G x y h s0 bkI).2.1 simh
      have pv := procList_vol hG s0 h _ _ _ hPh
      have eS : popS G x y (HeapImpl.waveLevelsH G x y ℓ hs bkI).1
          (HeapImpl.waveLevelsH G x y ℓ hs bkI).2.1 Q
          = procListS G x y ((waveLevels G x y h s0 bkI).2.1 h)
            (HeapImpl.waveLevelsH G x y h hs bkI).1 (waveLevels G x y h s0 bkI).2.1
            (HeapImpl.delete Q h).1 := by
        unfold popS
        rw [hℓ', ← b1, ← b2, bkh]
      have e1 : (procListS G x y ((waveLevels G x y h s0 bkI).2.1 h)
          (HeapImpl.waveLevelsH G x y h hs bkI).1 (waveLevels G x y h s0 bkI).2.1
          (HeapImpl.delete Q h).1).1 = (HeapImpl.waveLevelsH G x y (h + 1) hs bkI).1 := by
        rw [s1, wlH_succ, bkh]
      have e2 : (procListS G x y ((waveLevels G x y h s0 bkI).2.1 h)
          (HeapImpl.waveLevelsH G x y h hs bkI).1 (waveLevels G x y h s0 bkI).2.1
          (HeapImpl.delete Q h).1).2.1 = (HeapImpl.waveLevelsH G x y (h + 1) hs bkI).2.1 := by
        rw [s2, wlH_succ, bkh]
      have wA : (waveLevels G x y (h + 1) s0 bkI).2.2 = (waveLevels G x y h s0 bkI).2.2 + 1
          + (procList G x y ((waveLevels G x y h s0 bkI).2.1 h) (waveLevels G x y h s0 bkI).1
              (waveLevels G x y h s0 bkI).2.1).2.2 := by rw [wl_succ]
      have wv : (waveLevels G x y (h + 1) s0 bkI).1
          = (procList G x y ((waveLevels G x y h s0 bkI).2.1 h) (waveLevels G x y h s0 bkI).1
              (waveLevels G x y h s0 bkI).2.1).1 := by rw [wl_succ]
      have wb : (waveLevels G x y (h + 1) s0 bkI).2.1
          = (procList G x y ((waveLevels G x y h s0 bkI).2.1 h) (waveLevels G x y h s0 bkI).1
              (waveLevels G x y h s0 bkI).2.1).2.1 := by rw [wl_succ]
      rw [← wv, ← wb] at pv
      rw [e2, bkh1] at p2 p3
      have hQ'' : QOK G (procListS G x y ((waveLevels G x y h s0 bkI).2.1 h)
          (HeapImpl.waveLevelsH G x y h hs bkI).1 (waveLevels G x y h s0 bkI).2.1
          (HeapImpl.delete Q h).1).2.2.1 (h + 1) (waveLevels G x y (h + 1) s0 bkI).2.1 := by
        rw [← bkh1, ← e2]
        exact p1
      obtain ⟨i1, i2, i3⟩ := ih (h + 1) _ (by omega) (by omega) hQ''
      have hsub : pendSum G h (waveLevels G x y h s0 bkI).2.1
          ≤ pendSum G ℓ (waveLevels G x y ℓ s0 bkI).2.1 := by
        rw [a2]
        unfold pendSum
        exact sum_le_sum_of_subset (Ico_subset_Ico hcond.1 le_rfl)
      have hsp : pendSum G h (waveLevels G x y h s0 bkI).2.1
          = ((waveLevels G x y h s0 bkI).2.1 h).length
            + pendSum G (h + 1) (waveLevels G x y h s0 bkI).2.1 := by
        unfold pendSum
        exact Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      have hpos : 1 ≤ ((waveLevels G x y h s0 bkI).2.1 h).length := by
        rw [a2]
        exact List.length_pos_iff.2 hcond.2.2
      have hκ1 := Nat.mul_le_mul_left (kap G)
        (show 1 + pendSum G (h + 1) (waveLevels G x y h s0 bkI).2.1
          ≤ pendSum G ℓ (waveLevels G x y ℓ s0 bkI).2.1 by omega)
      rw [Nat.mul_add, Nat.mul_one] at hκ1
      have pvκ := congrArg (fun z => kap G * z) pv
      simp only [Nat.mul_add] at pvκ
      rw [eS, hℓ', e1, e2, ← a1]
      refine ⟨i1, ?_, ?_⟩
      · have key : ∀ (sw dc cS cA cH Al Ah Ah1 AL L h ℓ κ kvh kvh1 kvL kp0 kp1 kpl : ℕ),
            sw + 2 * Ah1 + 2 * (L + 1) + 2 * kvh1 ≤ 1 + 2 * AL + 2 * (h + 1) + 2 * kvL + kp1 →
            Ah1 = Ah + 1 + cA → Ah + ℓ = Al + h → cS + kp0 ≤ cH + kp1 → cH ≤ 2 * cA →
            kp1 + kvh = kp0 + kvh1 → κ + kp0 ≤ kpl → dc + 1 ≤ κ →
            sw + 1 + dc + cS + 2 * Al + 2 * (L + 1) + 2 * kvh
              ≤ 1 + 2 * AL + 2 * ℓ + 2 * kvL + kpl := by
          intros
          omega
        exact key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i2 wA a3 p2 ph3 pvκ hκ1 hdc
      · have key : ∀ (sw dc cS vL vh vh1 p0 p1 : ℕ), vL ≤ sw + vh1 → p1 + vh = p0 + vh1 →
            p1 ≤ p0 + cS → vL ≤ sw + 1 + dc + cS + vh := by
          intros
          omega
        exact key _ _ _ _ _ _ _ _ i3 pv p3

/-- **The wave with the sparse scheduler** (`eq:ram-work-bounds`, one endpoint, without a
level-scan term).  From an implemented state representing a state that satisfies the
engine invariant:

* `waveS` ends in exactly the state of the level-bucket wave `HeapImpl.waveH` (so all
  correctness statements about `waveH` / `CostEngines.wave` apply to it);
* its computed cost is at most `4 + 2 Σ_{g changed} dcost g + 2 κ · (deliveries)`, with
  `κ = ⌈log₂ (L + 1)⌉ + 3` the worklist charge;
* its computed cost is at least the number of deliveries. -/
theorem waveS_spec (hG : G.WF) (x : ℕ) (y : α) (hs : HEState α) (s0 : EState α)
    (hx : x < G.N) (h : SimE G hs s0) (h0 : Inv G s0) :
    (waveS G x y hs).1 = (waveH G x y hs).1 ∧
    (waveS G x y hs).2 ≤ 4 + 2 * chgSum G s0 (wave G x y s0).1
      + 2 * (kap G * vol G s0 (wave G x y s0).1) ∧
    vol G s0 (wave G x y s0).1 ≤ (waveS G x y hs).2 := by
  have hbkt : ∀ l, ∀ g ∈ bk0 G x l, G.level g = l ∧ g < G.N := by
    intro l g hg
    unfold bk0 at hg
    by_cases hl : l = G.level x
    · rw [ite_eq_left hl, List.mem_singleton] at hg
      rw [hg]
      exact ⟨hl.symm, hx⟩
    · rw [ite_eq_right hl] at hg
      exact absurd hg List.not_mem_nil
  have hbx : bk0 G x (G.level x) = [x] := by
    unfold bk0
    exact ite_eq_left rfl
  have hxb : x ∈ bk0 G x (G.level x) := by
    rw [hbx]
    exact List.mem_singleton.2 rfl
  have hP0 : PInv G x y s0 0 (bk0 G x 0) s0 (bk0 G x) := by
    refine ⟨h0.keys, ?_, ?_, fun _ _ _ => rfl, hbkt, fun g hg => hbkt 0 g hg⟩
    · intro g
      by_cases hl : G.children g = []
      · by_cases hgx : g = x
        · rw [hgx]
          by_cases hlev : G.level x = 0
          · exact Or.inr (Or.inl ⟨hlev, by rw [← hlev]; exact hxb⟩)
          · exact Or.inr (Or.inr ⟨by omega, hxb⟩)
        · left
          unfold target
          rw [ite_eq_left hl, ite_eq_right hgx]
      · left
        unfold target
        rw [ite_eq_right hl]
        exact h0.gate g hl
    · intro g hg
      exact absurd rfl hg
  have hP : ∀ ℓ, ℓ ≤ G.L + 1 → PInv G x y s0 ℓ ((waveLevels G x y ℓ s0 (bk0 G x)).2.1 ℓ)
      (waveLevels G x y ℓ s0 (bk0 G x)).1 (waveLevels G x y ℓ s0 (bk0 G x)).2.1 :=
    fun ℓ hℓ => (waveLevels_spec hG s0 (bk0 G x) hP0 ℓ hℓ).1
  have hAL := (waveLevels_spec hG s0 (bk0 G x) hP0 (G.L + 1) le_rfl).2
  have hpend0 : pendSum G 0 (bk0 G x) = 1 := by
    unfold pendSum
    have hlen : ∀ l, (bk0 G x l).length = if l = G.level x then 1 else 0 := by
      intro l
      unfold bk0
      split_ifs <;> simp
    have hmem : G.level x ∈ Ico 0 (G.L + 1) := by
      have := hG.level_le x
      rw [mem_Ico]
      omega
    simp only [hlen, sum_ite_eq', hmem, ite_true]
  have hpendL : pendSum G (G.L + 1) (waveLevels G x y (G.L + 1) s0 (bk0 G x)).2.1 = 0 := by
    unfold pendSum
    simp
  have hlxL : G.level x ≤ G.L := hG.level_le x
  have hemp : ∀ l, 0 ≤ l → l < G.level x → bk0 G x l = [] := by
    intro l _ hl
    unfold bk0
    exact ite_eq_right (by omega)
  obtain ⟨a1, a2, a3⟩ := skipA G x y s0 (bk0 G x) 0 (G.level x) (Nat.zero_le _) hemp
  obtain ⟨b1, b2⟩ := skipH G x y hs (bk0 G x) 0 (G.level x) (Nat.zero_le _) hemp
  have a1' : (waveLevels G x y (G.level x) s0 (bk0 G x)).1 = s0 := a1
  have a2' : (waveLevels G x y (G.level x) s0 (bk0 G x)).2.1 = bk0 G x := a2
  have a3' : (waveLevels G x y (G.level x) s0 (bk0 G x)).2.2 = G.level x := by
    have e : (waveLevels G x y 0 s0 (bk0 G x)).2.2 = 0 := rfl
    omega
  have b1' : (HeapImpl.waveLevelsH G x y (G.level x) hs (bk0 G x)).1 = hs := b1
  have b2' : (HeapImpl.waveLevelsH G x y (G.level x) hs (bk0 G x)).2.1 = bk0 G x := b2
  have hQ0 : QOK G (Heap.empty : Heap ℕ ℕ) (G.level x + 1) (bk0 G x) := by
    refine ⟨Heap.empty_inv, fun l => ?_⟩
    rw [ite_eq_right]
    · rfl
    · intro c
      apply c.2.2
      unfold bk0
      exact ite_eq_right (by have := c.1; omega)
  have hrest : ∀ g ∈ [x], ∀ p ∈ G.parents g,
      G.level x + 1 ≤ G.level p ∧ G.level p ≤ G.L := by
    intro g hg p hp
    rw [List.mem_singleton] at hg
    rw [hg] at hp
    have := hG.level_lt p x ((hG.parents_iff x p).1 hp)
    exact ⟨by omega, hG.level_le p⟩
  obtain ⟨s1, s2⟩ := procListS_sim G x y [x] hs (bk0 G x) (Heap.empty : Heap ℕ ℕ)
  obtain ⟨p1, p2, p3⟩ := procListS_spec G x y (G.level x + 1) [x] hs (bk0 G x)
    (Heap.empty : Heap ℕ ℕ) hQ0 hrest
  obtain ⟨_, _, ph3⟩ := HeapImpl.procListH_spec G x y [x] hs s0 (bk0 G x) h
  have hPx := hP (G.level x) (by omega)
  rw [a1', a2', hbx] at hPx
  have pv := procList_vol hG s0 (G.level x) [x] s0 (bk0 G x) hPx
  have wA : (waveLevels G x y (G.level x + 1) s0 (bk0 G x)).2.2
      = G.level x + 1 + (procList G x y [x] s0 (bk0 G x)).2.2 := by
    rw [wl_succ, a1', a2', hbx, a3']
  have wv : (waveLevels G x y (G.level x + 1) s0 (bk0 G x)).1
      = (procList G x y [x] s0 (bk0 G x)).1 := by
    rw [wl_succ, a1', a2', hbx]
  have wb : (waveLevels G x y (G.level x + 1) s0 (bk0 G x)).2.1
      = (procList G x y [x] s0 (bk0 G x)).2.1 := by
    rw [wl_succ, a1', a2', hbx]
  obtain ⟨_, bk1, _⟩ := HeapImpl.waveLevelsH_spec G x y hs s0 (bk0 G x) h (G.level x + 1)
  have e1 : (procListS G x y [x] hs (bk0 G x) (Heap.empty : Heap ℕ ℕ)).1
      = (HeapImpl.waveLevelsH G x y (G.level x + 1) hs (bk0 G x)).1 := by
    rw [s1, wlH_succ, b1', b2', hbx]
  have e2 : (procListS G x y [x] hs (bk0 G x) (Heap.empty : Heap ℕ ℕ)).2.1
      = (HeapImpl.waveLevelsH G x y (G.level x + 1) hs (bk0 G x)).2.1 := by
    rw [s2, wlH_succ, b1', b2', hbx]
  have hQ1 : QOK G (procListS G x y [x] hs (bk0 G x) (Heap.empty : Heap ℕ ℕ)).2.2.1
      (G.level x + 1) (waveLevels G x y (G.level x + 1) s0 (bk0 G x)).2.1 := by
    rw [← bk1, ← e2]
    exact p1
  obtain ⟨i1, i2, i3⟩ := sweepS_spec (x := x) (y := y) hG (bk0 G x) h hP (G.L + 1)
    (G.level x + 1) _ (by omega) (by omega) hQ1
  rw [← e1, ← e2] at i1 i2 i3
  have hv0 : vol G s0 s0 = 0 := by simp [vol]
  have hp0 : pendSum G (G.level x + 1) (bk0 G x) = 0 := by
    unfold pendSum
    apply sum_eq_zero
    intro l hl
    unfold bk0
    rw [ite_eq_right (by have := (mem_Ico.1 hl).1; omega)]
    rfl
  rw [← wv, ← wb, hv0, hp0] at pv
  rw [e2, bk1, hp0] at p2 p3
  have hpv : pendSum G (G.level x + 1) (waveLevels G x y (G.level x + 1) s0 (bk0 G x)).2.1
      = vol G s0 (waveLevels G x y (G.level x + 1) s0 (bk0 G x)).1 := by omega
  rw [hpv] at p2 p3 i2
  rw [Nat.mul_zero] at p2
  have ew : (wave G x y s0).1 = (waveLevels G x y (G.L + 1) s0 (bk0 G x)).1 := rfl
  have ewH : (waveH G x y hs).1 = (HeapImpl.waveLevelsH G x y (G.L + 1) hs (bk0 G x)).1 := rfl
  rw [ew, ewH]
  refine ⟨i1, ?_, ?_⟩
  · have key : ∀ (sw c1 cH cA A1 AL L lx chg kv1 kvL pL : ℕ),
        sw + 2 * A1 + 2 * (L + 1) + 2 * kv1 ≤ 1 + 2 * AL + 2 * (lx + 1) + 2 * kvL + kv1 →
        A1 = lx + 1 + cA → c1 + 0 ≤ cH + kv1 → cH ≤ 2 * cA →
        AL + pL = L + 1 + 1 + chg → pL = 0 →
        sw + 1 + c1 ≤ 4 + 2 * chg + 2 * kvL := by
      intros
      omega
    exact key _ _ _ _ _ _ _ _ _ _ _ _ i2 wA p2 ph3 (hpend0 ▸ hAL) hpendL
  · have key : ∀ (sw c1 vL v1 : ℕ), vL ≤ sw + v1 → v1 ≤ 0 + c1 → vL ≤ sw + 1 + c1 := by
      intros
      omega
    exact key _ _ _ _ i3 p3

end Sparse

end LiteralE4
end JointRootCert
