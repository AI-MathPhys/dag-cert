/-
A cost model for interval monitors on all-MAX circuits, and the work-separation results of
the appendix "Certification Along Passive Graph-Search Trajectories" that rest on it.

* Proposition `prop:uct-coupling` (Safe permanent retirement), work bounds
  `eq:ram-work-bounds`: `monWork_false_eq`, `monWork_true_eq`, `ram_work_bounds`.
* Theorem `thm:v2separation` (Root-PUCT work separation from uninformative
  initialization): `MonGraphRun.trace` (the root process of the `m`-leaf graph is the
  three-terminal process), `v2_outputs` (both monitors expose the same leader and stopping
  sets, equal to the check `Stop3`), `v2Work_selective_le`, `v2Work_selective_ge`,
  `v2Work_full_ge`, `v2Work_full_le` (the accounting inequalities), `v2separation_monitors`.
* Corollary `cor:v2quarter` (One explicit polynomial instance): `v2quarter_monitors`.
* Proposition `prop:v2escape` (The family does not lower-bound all numerical oracles):
  `monAlias_spec`, `v2escape`.
* Theorem `thm:onpolicy-uct` (Selective vs. eager maintenance separations on UCT and
  Root-PUCT funnels): the Root-PUCT half is `v2separation_monitors`; for the local-UCT half
  only the cost-model part of Step 4 on the two-exit funnel is here (`funnel_work`), the
  UCT process facts are in `UCTWork.lean`.

The cost model.  A monitor graph is a tree-shaped all-MAX circuit (`MaxCirc`, unary and
binary vertices; vertices are shared only at terminals, which live in a common terminal
table).  Each internal vertex stores its interval (`MonNode`).  The work of an operation is
a natural number returned by the function that performs it:

* building, releasing or disposing of a circuit: one step per vertex (`MaxCirc.monSize`);
* a propagation wave (`monWave`): a delivery across an incidence whose child endpoint
  changed costs `⌈log₂ d⌉ + 1` where `d ∈ {1, 2}` is the out-degree of the parent (an
  indexed-heap update at the parent); nothing else is charged;
* a root query (`monQuery`): two scans of the active actions, one step per action;
* retirement checks (`monRetire`): three steps per active action, plus the release of the
  circuits of the retired actions;
* a rollout (`monRollout`): two steps per traversed edge (descent and backup) plus five
  root- and terminal-local steps.

Scans are charged by the number of elements scanned and do not model exact real
arithmetic, as in the manuscript's endpoint-operation model.
-/
import JointRootCert.PassiveRetirement
import JointRootCert.RootPUCT

namespace JointRootCert

open Finset

noncomputable section

/-! ### Circuits: size, height, walks, exact intervals -/

namespace MaxCirc

variable {Z : Type*}

/-- Number of vertices of the tree unfolding (terminal occurrences included). -/
def monSize : MaxCirc Z → ℕ
  | term _ => 1
  | unary c => monSize c + 1
  | bin c d => monSize c + monSize d + 1

/-- Number of incidences (parent, child). -/
def monEdges : MaxCirc Z → ℕ
  | term _ => 0
  | unary c => monEdges c + 1
  | bin c d => monEdges c + monEdges d + 2

/-- Longest path to a terminal. -/
def monHeight : MaxCirc Z → ℕ
  | term _ => 0
  | unary c => monHeight c + 1
  | bin c d => max (monHeight c) (monHeight d) + 1

/-- A rollout below a vertex: at depth `d` a binary vertex takes its first child if
`rule d` and its second child otherwise.  Returns the terminal reached and the number of
edges traversed. -/
def monWalk (rule : ℕ → Bool) : ℕ → MaxCirc Z → Z × ℕ
  | _, term z => (z, 0)
  | d, unary c => ((monWalk rule (d + 1) c).1, (monWalk rule (d + 1) c).2 + 1)
  | d, bin c e =>
      bif rule d then ((monWalk rule (d + 1) c).1, (monWalk rule (d + 1) c).2 + 1)
      else ((monWalk rule (d + 1) e).1, (monWalk rule (d + 1) e).2 + 1)

theorem monEdges_lt_monSize : ∀ c : MaxCirc Z, c.monEdges + 1 ≤ c.monSize
  | term _ => le_rfl
  | unary c => by
      have := monEdges_lt_monSize c
      simp only [monEdges, monSize]
      omega
  | bin c d => by
      have := monEdges_lt_monSize c
      have := monEdges_lt_monSize d
      simp only [monEdges, monSize]
      omega

theorem monWalk_snd_le (rule : ℕ → Bool) :
    ∀ (c : MaxCirc Z) (d : ℕ), (monWalk rule d c).2 ≤ c.monHeight
  | term _, _ => le_rfl
  | unary c, d => by
      have := monWalk_snd_le rule c (d + 1)
      simp only [monWalk, monHeight]
      omega
  | bin c e, d => by
      have h1 := monWalk_snd_le rule c (d + 1)
      have h2 := monWalk_snd_le rule e (d + 1)
      cases hr : rule d <;> simp only [monWalk, monHeight, hr, Bool.cond_true, Bool.cond_false] <;> omega

theorem monWalk_fst_of_onlyTerm {z : Z} (rule : ℕ → Bool) :
    ∀ (c : MaxCirc Z) (d : ℕ), OnlyTerm z c → (monWalk rule d c).1 = z
  | term _, _, h => h
  | unary c, d, h => monWalk_fst_of_onlyTerm rule c (d + 1) h
  | bin c e, d, h => by
      have h' : OnlyTerm z c ∧ OnlyTerm z e := h
      cases hr : rule d
      · simp only [monWalk, hr, Bool.cond_false]
        exact monWalk_fst_of_onlyTerm rule e (d + 1) h'.2
      · simp only [monWalk, hr, Bool.cond_true]
        exact monWalk_fst_of_onlyTerm rule c (d + 1) h'.1

/-- The exact interval of the vertex on the box with terminal intervals `x z = (l z, u z)`:
MAX is coordinatewise monotone, so the endpoints are the MAX values of the endpoints. -/
def ival (x : Z → ℝ × ℝ) (c : MaxCirc Z) : ℝ × ℝ :=
  (eval (fun z => (x z).1) c, eval (fun z => (x z).2) c)

theorem ival_of_onlyTerm {z : Z} (x : Z → ℝ × ℝ) {c : MaxCirc Z} (h : OnlyTerm z c) :
    ival x c = x z := by
  unfold ival
  rw [eval_of_onlyTerm _ c h, eval_of_onlyTerm _ c h]

end MaxCirc

/-! ### Monitor vertices and propagation waves -/

/-- Interval of a MAX vertex from the intervals of two children. -/
def monJoin (p q : ℝ × ℝ) : ℝ × ℝ := (max p.1 q.1, max p.2 q.2)

/-- A monitor graph: an all-MAX circuit whose internal vertices store an interval. -/
inductive MonNode (Z : Type*) where
  | term : Z → MonNode Z
  | unary : ℝ × ℝ → MonNode Z → MonNode Z
  | bin : ℝ × ℝ → MonNode Z → MonNode Z → MonNode Z

namespace MonNode

variable {Z : Type*}

/-- The underlying circuit. -/
def shape : MonNode Z → MaxCirc Z
  | term z => .term z
  | unary _ c => .unary (shape c)
  | bin _ c d => .bin (shape c) (shape d)

/-- The interval stored at the vertex (read from the terminal table at a terminal). -/
def val (x : Z → ℝ × ℝ) : MonNode Z → ℝ × ℝ
  | term z => x z
  | unary v _ => v
  | bin v _ _ => v

/-- Every stored interval is the one computed from the children. -/
def Good (x : Z → ℝ × ℝ) : MonNode Z → Prop
  | term _ => True
  | unary v c => v = c.val x ∧ Good x c
  | bin v c d => v = monJoin (c.val x) (d.val x) ∧ Good x c ∧ Good x d

theorem val_eq_ival (x : Z → ℝ × ℝ) : ∀ n : MonNode Z, n.Good x → n.val x = n.shape.ival x
  | term _, _ => rfl
  | unary v c, h => by
      have h' : v = c.val x ∧ Good x c := h
      show v = c.shape.ival x
      rw [h'.1, val_eq_ival x c h'.2]
  | bin v c d, h => by
      have h' : v = monJoin (c.val x) (d.val x) ∧ Good x c ∧ Good x d := h
      show v = monJoin (c.shape.ival x) (d.shape.ival x)
      rw [h'.1, val_eq_ival x c h'.2.1, val_eq_ival x d h'.2.2]

end MonNode

section Wave

variable {Z : Type*}

/-- Build the monitor graph of a circuit from the terminal table. -/
def monBuild (x : Z → ℝ × ℝ) : MaxCirc Z → MonNode Z
  | .term z => .term z
  | .unary c => .unary ((monBuild x c).val x) (monBuild x c)
  | .bin c d =>
      .bin (monJoin ((monBuild x c).val x) ((monBuild x d).val x)) (monBuild x c) (monBuild x d)

theorem monBuild_good (x : Z → ℝ × ℝ) : ∀ c : MaxCirc Z, (monBuild x c).Good x
  | .term _ => trivial
  | .unary c => ⟨rfl, monBuild_good x c⟩
  | .bin c d => ⟨rfl, monBuild_good x c, monBuild_good x d⟩

theorem monBuild_shape (x : Z → ℝ × ℝ) : ∀ c : MaxCirc Z, (monBuild x c).shape = c
  | .term _ => rfl
  | .unary c => congrArg MaxCirc.unary (monBuild_shape x c)
  | .bin c d => by
      show MaxCirc.bin (monBuild x c).shape (monBuild x d).shape = MaxCirc.bin c d
      rw [monBuild_shape x c, monBuild_shape x d]

open Classical in
/-- A propagation wave in reverse topological order.  `x` is the new terminal table and
`chg z` says whether the interval of terminal `z` changed.  A vertex receives a delivery
from each child whose interval changed and is then recomputed; a delivery costs `1` at a
unary parent and `2` at a binary parent (`⌈log₂ d⌉ + 1` for out-degree `d`).  Returns the
new graph, whether the interval of its top vertex changed, and the work. -/
def monWave (x : Z → ℝ × ℝ) (chg : Z → Bool) : MonNode Z → MonNode Z × Bool × ℕ
  | .term z => (.term z, chg z, 0)
  | .unary v c =>
      if (monWave x chg c).2.1 then
        (.unary ((monWave x chg c).1.val x) (monWave x chg c).1,
          decide ((monWave x chg c).1.val x ≠ v), (monWave x chg c).2.2 + 1)
      else (.unary v (monWave x chg c).1, false, (monWave x chg c).2.2)
  | .bin v c d =>
      if (monWave x chg c).2.1 = true ∨ (monWave x chg d).2.1 = true then
        (.bin (monJoin ((monWave x chg c).1.val x) ((monWave x chg d).1.val x))
            (monWave x chg c).1 (monWave x chg d).1,
          decide (monJoin ((monWave x chg c).1.val x) ((monWave x chg d).1.val x) ≠ v),
          (monWave x chg c).2.2 + (monWave x chg d).2.2
            + (if (monWave x chg c).2.1 then 2 else 0) + (if (monWave x chg d).2.1 then 2 else 0))
      else (.bin v (monWave x chg c).1 (monWave x chg d).1, false,
        (monWave x chg c).2.2 + (monWave x chg d).2.2)

open Classical in
/-- Number of incidences of the circuit whose child interval differs between the terminal
tables `x` and `x'` (the changed-endpoint deliveries of one wave). -/
def monDeliv (x x' : Z → ℝ × ℝ) : MaxCirc Z → ℕ
  | .term _ => 0
  | .unary c => monDeliv x x' c + if c.ival x' ≠ c.ival x then 1 else 0
  | .bin c d =>
      monDeliv x x' c + monDeliv x x' d + (if c.ival x' ≠ c.ival x then 1 else 0)
        + (if d.ival x' ≠ d.ival x then 1 else 0)

open Classical in
/-- The same deliveries, each weighted by the heap charge of its parent. -/
def monDelivCost (x x' : Z → ℝ × ℝ) : MaxCirc Z → ℕ
  | .term _ => 0
  | .unary c => monDelivCost x x' c + if c.ival x' ≠ c.ival x then 1 else 0
  | .bin c d =>
      monDelivCost x x' c + monDelivCost x x' d + (if c.ival x' ≠ c.ival x then 2 else 0)
        + (if d.ival x' ≠ d.ival x then 2 else 0)

theorem monDeliv_le_cost (x x' : Z → ℝ × ℝ) :
    ∀ c : MaxCirc Z, monDeliv x x' c ≤ monDelivCost x x' c
  | .term _ => le_rfl
  | .unary c => by
      have := monDeliv_le_cost x x' c
      simp only [monDeliv, monDelivCost]
      omega
  | .bin c d => by
      have := monDeliv_le_cost x x' c
      have := monDeliv_le_cost x x' d
      simp only [monDeliv, monDelivCost]
      split_ifs <;> omega

theorem monDelivCost_le_two (x x' : Z → ℝ × ℝ) :
    ∀ c : MaxCirc Z, monDelivCost x x' c ≤ 2 * monDeliv x x' c
  | .term _ => le_rfl
  | .unary c => by
      have := monDelivCost_le_two x x' c
      simp only [monDeliv, monDelivCost]
      split_ifs <;> omega
  | .bin c d => by
      have := monDelivCost_le_two x x' c
      have := monDelivCost_le_two x x' d
      simp only [monDeliv, monDelivCost]
      split_ifs <;> omega

theorem monDeliv_le_edges (x x' : Z → ℝ × ℝ) :
    ∀ c : MaxCirc Z, monDeliv x x' c ≤ c.monEdges
  | .term _ => le_rfl
  | .unary c => by
      have := monDeliv_le_edges x x' c
      simp only [monDeliv, MaxCirc.monEdges]
      split_ifs <;> omega
  | .bin c d => by
      have := monDeliv_le_edges x x' c
      have := monDeliv_le_edges x x' d
      simp only [monDeliv, MaxCirc.monEdges]
      split_ifs <;> omega

/-- If the single terminal below the vertex did not change, the wave delivers nothing. -/
theorem monDelivCost_eq_zero_of_onlyTerm {z : Z} {x x' : Z → ℝ × ℝ} (hx : x' z = x z) :
    ∀ c : MaxCirc Z, MaxCirc.OnlyTerm z c → monDelivCost x x' c = 0
  | .term _, _ => rfl
  | .unary c, h => by
      have h' : MaxCirc.OnlyTerm z c := h
      simp [monDelivCost, monDelivCost_eq_zero_of_onlyTerm hx c h',
        MaxCirc.ival_of_onlyTerm _ h', hx]
  | .bin c d, h => by
      have h' : MaxCirc.OnlyTerm z c ∧ MaxCirc.OnlyTerm z d := h
      simp [monDelivCost, monDelivCost_eq_zero_of_onlyTerm hx c h'.1,
        monDelivCost_eq_zero_of_onlyTerm hx d h'.2, MaxCirc.ival_of_onlyTerm _ h'.1,
        MaxCirc.ival_of_onlyTerm _ h'.2, hx]

/-- If the single terminal below the vertex changed, every incidence carries a delivery. -/
theorem monDeliv_of_onlyTerm_ne {z : Z} {x x' : Z → ℝ × ℝ} (hx : x' z ≠ x z) :
    ∀ c : MaxCirc Z, MaxCirc.OnlyTerm z c → monDeliv x x' c = c.monEdges
  | .term _, _ => rfl
  | .unary c, h => by
      have h' : MaxCirc.OnlyTerm z c := h
      simp [monDeliv, MaxCirc.monEdges, monDeliv_of_onlyTerm_ne hx c h',
        MaxCirc.ival_of_onlyTerm _ h', hx]
  | .bin c d, h => by
      have h' : MaxCirc.OnlyTerm z c ∧ MaxCirc.OnlyTerm z d := h
      simp [monDeliv, MaxCirc.monEdges, monDeliv_of_onlyTerm_ne hx c h'.1,
        monDeliv_of_onlyTerm_ne hx d h'.2, MaxCirc.ival_of_onlyTerm _ h'.1,
        MaxCirc.ival_of_onlyTerm _ h'.2, hx]

/-- **Correctness and exact cost of a wave.**  If the stored intervals are consistent with
the old table `x` and `chg` flags exactly the terminals whose interval changed, the wave
returns a graph of the same shape consistent with the new table `x'`, reports whether the
top interval changed, and its work is exactly the weighted number of changed-endpoint
deliveries. -/
theorem monWave_spec {x x' : Z → ℝ × ℝ} {chg : Z → Bool}
    (hchg : ∀ z, chg z = decide (x' z ≠ x z)) :
    ∀ n : MonNode Z, n.Good x →
      (monWave x' chg n).1.Good x' ∧ (monWave x' chg n).1.shape = n.shape ∧
      (monWave x' chg n).2.1 = decide (n.shape.ival x' ≠ n.shape.ival x) ∧
      (monWave x' chg n).2.2 = monDelivCost x x' n.shape
  | .term z, _ => ⟨trivial, rfl, hchg z, rfl⟩
  | .unary v c, h => by
      obtain ⟨hv, hc⟩ : v = c.val x ∧ c.Good x := h
      obtain ⟨ih1, ih2, ih3, ih4⟩ := monWave_spec hchg c hc
      have hval := MonNode.val_eq_ival x' _ ih1
      rw [ih2] at hval
      have hv' : v = c.shape.ival x := hv.trans (MonNode.val_eq_ival x c hc)
      by_cases hf : (monWave x' chg c).2.1 = true
      · have hne : c.shape.ival x' ≠ c.shape.ival x := by
          rw [ih3] at hf
          exact of_decide_eq_true hf
        rw [monWave, ite_eq_left hf]
        refine ⟨⟨rfl, ih1⟩, congrArg MaxCirc.unary ih2, ?_, ?_⟩
        · show decide ((monWave x' chg c).1.val x' ≠ v) = _
          rw [hval, hv']
          rfl
        · show (monWave x' chg c).2.2 + 1 = _
          rw [ih4]
          simp [MonNode.shape, monDelivCost, hne]
      · have heq : c.shape.ival x' = c.shape.ival x := by
          rw [ih3] at hf
          by_contra hne
          exact hf (decide_eq_true hne)
        rw [monWave, ite_eq_right hf]
        refine ⟨⟨?_, ih1⟩, congrArg MaxCirc.unary ih2, ?_, ?_⟩
        · rw [hval, heq, hv']
        · show false = decide (c.shape.ival x' ≠ c.shape.ival x)
          simp [heq]
        · show (monWave x' chg c).2.2 = _
          rw [ih4]
          simp [MonNode.shape, monDelivCost, heq]
  | .bin v c d, h => by
      obtain ⟨hv, hc, hd⟩ : v = monJoin (c.val x) (d.val x) ∧ c.Good x ∧ d.Good x := h
      obtain ⟨ic1, ic2, ic3, ic4⟩ := monWave_spec hchg c hc
      obtain ⟨id1, id2, id3, id4⟩ := monWave_spec hchg d hd
      have hvalc := MonNode.val_eq_ival x' _ ic1
      rw [ic2] at hvalc
      have hvald := MonNode.val_eq_ival x' _ id1
      rw [id2] at hvald
      have hv' : v = monJoin (c.shape.ival x) (d.shape.ival x) := by
        rw [hv, MonNode.val_eq_ival x c hc, MonNode.val_eq_ival x d hd]
      have hcd : ∀ y : Z → ℝ × ℝ, (MaxCirc.bin c.shape d.shape).ival y
          = monJoin (c.shape.ival y) (d.shape.ival y) := fun _ => rfl
      by_cases hf : (monWave x' chg c).2.1 = true ∨ (monWave x' chg d).2.1 = true
      · rw [monWave, ite_eq_left hf]
        refine ⟨⟨rfl, ic1, id1⟩, ?_, ?_, ?_⟩
        · show MaxCirc.bin _ _ = MaxCirc.bin _ _
          rw [ic2, id2]
        · show decide (monJoin ((monWave x' chg c).1.val x') ((monWave x' chg d).1.val x') ≠ v)
            = decide ((MaxCirc.bin c.shape d.shape).ival x' ≠ (MaxCirc.bin c.shape d.shape).ival x)
          rw [hvalc, hvald, hv', hcd, hcd]
        · show (monWave x' chg c).2.2 + (monWave x' chg d).2.2
              + (if (monWave x' chg c).2.1 = true then 2 else 0)
              + (if (monWave x' chg d).2.1 = true then 2 else 0)
            = monDelivCost x x' (MaxCirc.bin c.shape d.shape)
          rw [ic4, id4, ic3, id3]
          simp [monDelivCost]
      · have hfc : (monWave x' chg c).2.1 ≠ true := fun h => hf (Or.inl h)
        have hfd : (monWave x' chg d).2.1 ≠ true := fun h => hf (Or.inr h)
        have heqc : c.shape.ival x' = c.shape.ival x := by
          rw [ic3] at hfc
          by_contra hne
          exact hfc (decide_eq_true hne)
        have heqd : d.shape.ival x' = d.shape.ival x := by
          rw [id3] at hfd
          by_contra hne
          exact hfd (decide_eq_true hne)
        rw [monWave, ite_eq_right hf]
        refine ⟨⟨?_, ic1, id1⟩, ?_, ?_, ?_⟩
        · rw [hvalc, hvald, heqc, heqd, hv']
        · show MaxCirc.bin _ _ = MaxCirc.bin _ _
          rw [ic2, id2]
        · show false
            = decide ((MaxCirc.bin c.shape d.shape).ival x' ≠ (MaxCirc.bin c.shape d.shape).ival x)
          rw [hcd, hcd, heqc, heqd]
          simp
        · show (monWave x' chg c).2.2 + (monWave x' chg d).2.2
            = monDelivCost x x' (MaxCirc.bin c.shape d.shape)
          rw [ic4, id4]
          simp [monDelivCost, heqc, heqd]

end Wave

/-! ### The leader-and-stop monitor with optional root retirement -/

/-- State of a monitor over root actions `A`: the active actions and, for each action, its
monitor graph (`none` once released). -/
structure MonState (A Z : Type*) where
  act : Finset A
  nodes : A → Option (MonNode Z)

/-- Interface output: the canonical lower-bound leaders (at most one) and the leaders at
which the stopping test passes. -/
structure MonOut (A : Type*) where
  leaders : Set A
  stops : Set A

section Monitor

variable {A Z : Type*}

/-- Stored lower endpoint of a root action. -/
def MonState.lo (σ : MonState A Z) (x : Z → ℝ × ℝ) (a : A) : ℝ :=
  (σ.nodes a).elim 0 (fun n => (n.val x).1)

/-- Stored upper endpoint of a root action. -/
def MonState.hi (σ : MonState A Z) (x : Z → ℝ × ℝ) (a : A) : ℝ :=
  (σ.nodes a).elim 1 (fun n => (n.val x).2)

/-- Number of vertices of a possibly released monitor graph. -/
def monOptSize (o : Option (MonNode Z)) : ℕ := o.elim 0 (fun n => n.shape.monSize)

/-- Root query: canonical leader and stopping test over the active actions, from the stored
endpoints.  Work: two scans of the active actions. -/
def monQuery [LinearOrder A] (ε : ℝ) (x : Z → ℝ × ℝ) (σ : MonState A Z) : MonOut A × ℕ :=
  (⟨{a | LowLeader σ.act (σ.lo x) a}, {a | MarginalStops σ.act (σ.lo x) (σ.hi x) ε a}⟩,
    2 * σ.act.card)

open Classical in
/-- Actions that survive the retirement rule of `thm:decision-retirement`: `b` is retired
when some other active action `a` has `U b < L a`. -/
def monKeep (x : Z → ℝ × ℝ) (σ : MonState A Z) : Finset A :=
  σ.act.filter (fun b => ¬ ∃ a ∈ σ.act, a ≠ b ∧ σ.hi x b < σ.lo x a)

/-- Retirement step.  The selective monitor (`s = true`) retires dominated actions and
releases their monitor graphs; work: three steps per active action (two for the two largest
lower endpoints, one for the test) plus one step per released vertex.  The full monitor
(`s = false`) does nothing. -/
def monRetire [DecidableEq A] (s : Bool) (x : Z → ℝ × ℝ) (σ : MonState A Z) :
    MonState A Z × ℕ :=
  bif s then
    (⟨monKeep x σ, fun a => if a ∈ monKeep x σ then σ.nodes a else none⟩,
      3 * σ.act.card + ∑ a ∈ σ.act \ monKeep x σ, monOptSize (σ.nodes a))
  else (σ, 0)

/-- Propagate a terminal-table change through every live monitor graph. -/
def monWaveAll [Fintype A] (x' : Z → ℝ × ℝ) (chg : Z → Bool) (σ : MonState A Z) :
    MonState A Z × ℕ :=
  (⟨σ.act, fun a => (σ.nodes a).map (fun n => (monWave x' chg n).1)⟩,
    ∑ a, (σ.nodes a).elim 0 (fun n => (monWave x' chg n).2.2))

/-- Invariant: active actions carry a consistent monitor graph of the right shape, retired
actions carry none. -/
def MonInv (circ : A → MaxCirc Z) (x : Z → ℝ × ℝ) (σ : MonState A Z) : Prop :=
  (∀ a ∈ σ.act, ∃ n, σ.nodes a = some n ∧ n.Good x ∧ n.shape = circ a) ∧
    ∀ a, a ∉ σ.act → σ.nodes a = none

variable {circ : A → MaxCirc Z} {x x' : Z → ℝ × ℝ} {σ : MonState A Z}

theorem MonInv.lo_eq (h : MonInv circ x σ) {a : A} (ha : a ∈ σ.act) :
    σ.lo x a = ((circ a).ival x).1 := by
  obtain ⟨n, hn1, hn2, hn3⟩ := h.1 a ha
  unfold MonState.lo
  rw [hn1, ← hn3, ← MonNode.val_eq_ival x n hn2]
  rfl

theorem MonInv.hi_eq (h : MonInv circ x σ) {a : A} (ha : a ∈ σ.act) :
    σ.hi x a = ((circ a).ival x).2 := by
  obtain ⟨n, hn1, hn2, hn3⟩ := h.1 a ha
  unfold MonState.hi
  rw [hn1, ← hn3, ← MonNode.val_eq_ival x n hn2]
  rfl

theorem MonInv.optSize_eq (h : MonInv circ x σ) {a : A} (ha : a ∈ σ.act) :
    monOptSize (σ.nodes a) = (circ a).monSize := by
  obtain ⟨n, hn1, -, hn3⟩ := h.1 a ha
  unfold monOptSize
  rw [hn1, ← hn3]
  rfl

theorem MonInv.mem_monKeep (h : MonInv circ x σ) (b : A) :
    b ∈ monKeep x σ ↔
      b ∈ σ.act ∧ ¬ ∃ a ∈ σ.act, a ≠ b ∧ ((circ b).ival x).2 < ((circ a).ival x).1 := by
  classical
  unfold monKeep
  rw [mem_filter]
  refine and_congr_right (fun hb => not_congr (exists_congr (fun a => and_congr_right
    (fun ha => and_congr_right (fun _ => ?_)))))
  rw [h.hi_eq hb, h.lo_eq ha]

theorem monRetire_inv [DecidableEq A] (s : Bool) (h : MonInv circ x σ) :
    MonInv circ x (monRetire s x σ).1 := by
  cases s
  · exact h
  · refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have ha' : a ∈ monKeep x σ := ha
      have ha'' : a ∈ σ.act := ((h.mem_monKeep a).mp ha').1
      obtain ⟨n, hn1, hn2, hn3⟩ := h.1 a ha''
      refine ⟨n, ?_, hn2, hn3⟩
      show (if a ∈ monKeep x σ then σ.nodes a else none) = some n
      rw [ite_eq_left ha', hn1]
    · have ha' : a ∉ monKeep x σ := ha
      show (if a ∈ monKeep x σ then σ.nodes a else none) = none
      rw [ite_eq_right ha']

theorem monWaveAll_inv [Fintype A] {chg : Z → Bool} (hchg : ∀ z, chg z = decide (x' z ≠ x z))
    (h : MonInv circ x σ) : MonInv circ x' (monWaveAll x' chg σ).1 := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have ha' : a ∈ σ.act := ha
    obtain ⟨n, hn1, hn2, hn3⟩ := h.1 a ha'
    obtain ⟨s1, s2, -, -⟩ := monWave_spec hchg n hn2
    refine ⟨(monWave x' chg n).1, ?_, s1, s2.trans hn3⟩
    show (σ.nodes a).map (fun n => (monWave x' chg n).1) = _
    rw [hn1]
    rfl
  · have ha' : a ∉ σ.act := ha
    show (σ.nodes a).map (fun n => (monWave x' chg n).1) = none
    rw [h.2 a ha']
    rfl

theorem monWaveAll_cost [Fintype A] {chg : Z → Bool} (hchg : ∀ z, chg z = decide (x' z ≠ x z))
    (h : MonInv circ x σ) :
    (monWaveAll x' chg σ).2 = ∑ a ∈ σ.act, monDelivCost x x' (circ a) := by
  have e := Finset.sum_subset (subset_univ σ.act)
    (f := fun a => (σ.nodes a).elim 0 (fun n => (monWave x' chg n).2.2))
    (fun a _ ha => by rw [h.2 a ha]; rfl)
  show ∑ a, (σ.nodes a).elim 0 (fun n => (monWave x' chg n).2.2) = _
  rw [← e]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  obtain ⟨n, hn1, hn2, hn3⟩ := h.1 a ha
  obtain ⟨-, -, -, s4⟩ := monWave_spec hchg n hn2
  rw [hn1, ← hn3, ← s4]
  rfl

theorem MonInv.sum_optSize [Fintype A] (h : MonInv circ x σ) :
    ∑ a, monOptSize (σ.nodes a) = ∑ a ∈ σ.act, (circ a).monSize := by
  have e := Finset.sum_subset (subset_univ σ.act) (f := fun a => monOptSize (σ.nodes a))
    (fun a _ ha => by rw [h.2 a ha]; rfl)
  rw [← e]
  exact Finset.sum_congr rfl (fun a ha => h.optSize_eq ha)

theorem lowLeader_congr [LinearOrder A] {s : Finset A} {L L' : A → ℝ}
    (h : ∀ b ∈ s, L b = L' b) (a : A) : LowLeader s L a ↔ LowLeader s L' a := by
  unfold LowLeader
  refine and_congr_right (fun ha => ?_)
  rw [h a ha]
  refine and_congr (forall₂_congr (fun b hb => by rw [h b hb]))
    (forall₂_congr (fun b hb => by rw [h b hb]))

theorem marginalStops_congr [LinearOrder A] {s : Finset A} {L L' U U' : A → ℝ} {ε : ℝ}
    (hL : ∀ b ∈ s, L b = L' b) (hU : ∀ b ∈ s, U b = U' b) (a : A) :
    MarginalStops s L U ε a ↔ MarginalStops s L' U' ε a := by
  unfold MarginalStops
  rw [lowLeader_congr hL a]
  refine and_congr_right (fun hl => ?_)
  rw [hL a hl.1]
  exact forall₂_congr (fun b hb => by rw [hU b hb])

/-- The output of a query in terms of the exact action intervals. -/
theorem MonInv.query_out [LinearOrder A] (h : MonInv circ x σ) (ε : ℝ) :
    (monQuery ε x σ).1 = ⟨{a | LowLeader σ.act (fun a => ((circ a).ival x).1) a},
      {a | MarginalStops σ.act (fun a => ((circ a).ival x).1)
        (fun a => ((circ a).ival x).2) ε a}⟩ := by
  have hL : ∀ b ∈ σ.act, σ.lo x b = ((circ b).ival x).1 := fun b hb => h.lo_eq hb
  have hU : ∀ b ∈ σ.act, σ.hi x b = ((circ b).ival x).2 := fun b hb => h.hi_eq hb
  exact congrArg₂ MonOut.mk (Set.ext (fun a => lowLeader_congr hL a))
    (Set.ext (fun a => marginalStops_congr hL hU a))

end Monitor

/-! ### Runs of the two monitors and their work -/

section Run

variable {A Z : Type*} [Fintype A] [LinearOrder A]

open Classical in
/-- Which terminal intervals change between step `k` and step `k + 1`. -/
def monChg (x : ℕ → Z → ℝ × ℝ) (k : ℕ) (z : Z) : Bool := decide (x (k + 1) z ≠ x k z)

/-- The monitor state before the query at step `k`, along the sequence `x` of terminal
tables: build at step `0`; at each step query, retire (selective only), then propagate the
next terminal update. -/
def monRun (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) : ℕ → MonState A Z
  | 0 => ⟨univ, fun a => some (monBuild (x 0) (circ a))⟩
  | k + 1 => (monWaveAll (x (k + 1)) (monChg x k) (monRetire s (x k) (monRun s circ x k)).1).1

/-- Monitor work of step `k`: query, retirement, terminal-table update (one step) and the
wave. -/
def monStepCost (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) (k : ℕ) : ℕ :=
  (monQuery ε (x k) (monRun s circ x k)).2 + (monRetire s (x k) (monRun s circ x k)).2
    + (monWaveAll (x (k + 1)) (monChg x k) (monRetire s (x k) (monRun s circ x k)).1).2 + 1

/-- Total monitor work for `K` terminal updates: build, the `K` steps, the final query and
the disposal of the remaining monitor graphs. -/
def monWork (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) (K : ℕ) : ℕ :=
  ∑ a, (circ a).monSize + ∑ k ∈ range K, monStepCost s circ x ε k
    + (monQuery ε (x K) (monRun s circ x K)).2
    + ∑ a, monOptSize ((monRun s circ x K).nodes a)

/-- Exact lower and upper endpoints of the root actions at step `k`. -/
def monL (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (k : ℕ) (a : A) : ℝ := ((circ a).ival (x k)).1

/-- Exact upper endpoints of the root actions at step `k`. -/
def monU (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (k : ℕ) (a : A) : ℝ := ((circ a).ival (x k)).2

variable {circ : A → MaxCirc Z} {x : ℕ → Z → ℝ × ℝ}

theorem monRun_inv (s : Bool) (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) :
    ∀ k, MonInv circ (x k) (monRun s circ x k)
  | 0 => ⟨fun _ _ => ⟨_, rfl, monBuild_good _ _, monBuild_shape _ _⟩,
      fun a ha => absurd (mem_univ a) ha⟩
  | k + 1 => monWaveAll_inv (fun _ => rfl) (monRetire_inv s (monRun_inv s circ x k))

theorem monRun_act_false (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) :
    ∀ k, (monRun false circ x k).act = univ
  | 0 => rfl
  | k + 1 => monRun_act_false circ x k

theorem monRun_act_succ (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (k : ℕ) :
    (monRun true circ x (k + 1)).act = monKeep (x k) (monRun true circ x k) := rfl

theorem mem_monRun_act_succ (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (k : ℕ) (b : A) :
    b ∈ (monRun true circ x (k + 1)).act ↔ b ∈ (monRun true circ x k).act ∧
      ¬ ∃ a ∈ (monRun true circ x k).act, a ≠ b ∧ monU circ x k b < monL circ x k a := by
  rw [monRun_act_succ]
  exact (monRun_inv true circ x k).mem_monKeep b

theorem monRun_act_anti (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (k : ℕ) :
    (monRun true circ x (k + 1)).act ⊆ (monRun true circ x k).act :=
  fun b hb => ((mem_monRun_act_succ circ x k b).mp hb).1

/-- The selective monitor's active sets form a retirement run in the sense of
`thm:decision-retirement`, as soon as the exact action intervals are nested and nonempty. -/
theorem monRun_retireRun (hL : ∀ a s t, s ≤ t → monL circ x s a ≤ monL circ x t a)
    (hU : ∀ a s t, s ≤ t → monU circ x t a ≤ monU circ x s a)
    (hne : ∀ t a, monL circ x t a ≤ monU circ x t a) :
    RetireRun (monL circ x) (monU circ x) (fun k => (monRun true circ x k).act) where
  nestedL := hL
  nestedU := hU
  nonempty := hne
  init := rfl
  anti := monRun_act_anti circ x
  retire := by
    intro t b hb1 hb2
    by_contra hcon
    exact hb1 ((mem_monRun_act_succ circ x t b).mpr ⟨hb2, hcon⟩)

/-- **Both monitors expose the same leader and stopping bit** (`prop:ta-coupled` for the
leader-and-stop interface): at every step the output of the selective monitor equals the
output of the full monitor, which is the canonical leader and marginal stopping test
computed from the exact intervals of all root actions. -/
theorem monRun_outputs [Nonempty A] (hL : ∀ a s t, s ≤ t → monL circ x s a ≤ monL circ x t a)
    (hU : ∀ a s t, s ≤ t → monU circ x t a ≤ monU circ x s a)
    (hne : ∀ t a, monL circ x t a ≤ monU circ x t a) {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    (monQuery ε (x k) (monRun true circ x k)).1 = (monQuery ε (x k) (monRun false circ x k)).1 ∧
      (monQuery ε (x k) (monRun false circ x k)).1 =
        ⟨{a | LowLeader univ (monL circ x k) a},
          {a | MarginalStops univ (monL circ x k) (monU circ x k) ε a}⟩ := by
  have hR := monRun_retireRun hL hU hne
  have hfull : (monQuery ε (x k) (monRun false circ x k)).1 =
      ⟨{a | LowLeader univ (monL circ x k) a},
        {a | MarginalStops univ (monL circ x k) (monU circ x k) ε a}⟩ := by
    rw [(monRun_inv false circ x k).query_out ε, monRun_act_false]
    rfl
  refine ⟨?_, hfull⟩
  rw [hfull, (monRun_inv true circ x k).query_out ε]
  exact congrArg₂ MonOut.mk (Set.ext (fun a => (hR.lowLeader_iff k a).symm))
    (Set.ext (fun a => (hR.stops_iff hε k a).symm))

/-- **Exact work of the full (eager) monitor**: twice the graph size (build and disposal),
one terminal-table step per update, `2 |A|` per root query, and the weighted
changed-endpoint deliveries of every wave over all root actions. -/
theorem monWork_false_eq (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) (K : ℕ) :
    monWork false circ x ε K = 2 * ∑ a, (circ a).monSize + K + 2 * Fintype.card A * (K + 1)
      + ∑ k ∈ range K, ∑ a, monDelivCost (x k) (x (k + 1)) (circ a) := by
  have hstep : ∀ k, monStepCost false circ x ε k
      = 2 * Fintype.card A + ∑ a, monDelivCost (x k) (x (k + 1)) (circ a) + 1 := by
    intro k
    have hw := monWaveAll_cost (chg := monChg x k) (x' := x (k + 1)) (fun _ => rfl)
      (monRun_inv false circ x k)
    rw [monRun_act_false] at hw
    show 2 * (monRun false circ x k).act.card + 0
      + (monWaveAll (x (k + 1)) (monChg x k) (monRun false circ x k)).2 + 1 = _
    rw [hw, monRun_act_false, Finset.card_univ]
    omega
  have hq : (monQuery ε (x K) (monRun false circ x K)).2 = 2 * Fintype.card A := by
    show 2 * (monRun false circ x K).act.card = _
    rw [monRun_act_false, Finset.card_univ]
  have hd := (monRun_inv false circ x K).sum_optSize
  rw [monRun_act_false] at hd
  unfold monWork
  rw [hq, hd]
  simp only [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

private theorem monRun_release_telescope (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) :
    ∀ K, ∑ k ∈ range K,
        ∑ a ∈ (monRun true circ x k).act \ (monRun true circ x (k + 1)).act, (circ a).monSize
      + ∑ a ∈ (monRun true circ x K).act, (circ a).monSize = ∑ a, (circ a).monSize
  | 0 => by simp [monRun]
  | K + 1 => by
      have ih := monRun_release_telescope circ x K
      have hs := Finset.sum_sdiff (f := fun a => (circ a).monSize) (monRun_act_anti circ x K)
      rw [Finset.sum_range_succ]
      omega

/-- **Exact work of the selective monitor**: as for the full monitor, except that every
release is paid once (so build, releases and disposal together cost twice the graph size),
queries and retirement checks cost five steps per active action, and waves run only through
the graphs of the actions still active. -/
theorem monWork_true_eq (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) (K : ℕ) :
    monWork true circ x ε K = 2 * ∑ a, (circ a).monSize + K
      + ∑ k ∈ range K, 5 * (monRun true circ x k).act.card
      + 2 * (monRun true circ x K).act.card
      + ∑ k ∈ range K, ∑ a ∈ (monRun true circ x (k + 1)).act,
          monDelivCost (x k) (x (k + 1)) (circ a) := by
  have hstep : ∀ k, monStepCost true circ x ε k
      = 5 * (monRun true circ x k).act.card
        + ∑ a ∈ (monRun true circ x k).act \ (monRun true circ x (k + 1)).act, (circ a).monSize
        + ∑ a ∈ (monRun true circ x (k + 1)).act, monDelivCost (x k) (x (k + 1)) (circ a)
        + 1 := by
    intro k
    have hinv := monRun_inv true circ x k
    have hw := monWaveAll_cost (chg := monChg x k) (x' := x (k + 1)) (fun _ => rfl)
      (monRetire_inv true hinv)
    have hr : (monRetire true (x k) (monRun true circ x k)).2
        = 3 * (monRun true circ x k).act.card
          + ∑ a ∈ (monRun true circ x k).act \ (monRun true circ x (k + 1)).act,
              (circ a).monSize := by
      show 3 * (monRun true circ x k).act.card
          + ∑ a ∈ (monRun true circ x k).act \ monKeep (x k) (monRun true circ x k),
              monOptSize ((monRun true circ x k).nodes a) = _
      rw [← monRun_act_succ]
      congr 1
      exact Finset.sum_congr rfl (fun a ha => hinv.optSize_eq (mem_sdiff.mp ha).1)
    unfold monStepCost
    rw [hr, hw]
    show 2 * (monRun true circ x k).act.card + _ + _ + 1 = _
    have : (monRetire true (x k) (monRun true circ x k)).1.act
        = (monRun true circ x (k + 1)).act := rfl
    rw [this]
    ring
  have hd := (monRun_inv true circ x K).sum_optSize
  have htel := monRun_release_telescope circ x K
  unfold monWork
  rw [hd]
  show _ + _ + 2 * (monRun true circ x K).act.card + _ = _
  simp only [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

/-- **`eq:ram-work-bounds` in this cost model.**  For `K` rollouts with a root query after
each, on tree-shaped circuits of out-degree at most two (so the heap charge is at most `2`):
with `G` the number of graph vertices, `S₀` the changed-endpoint deliveries over all
incidences and `S` those over the incidences of the actions still active,

* `S₀ ≤ W_eager ≤ 2 G + K + 2 |A| (K + 1) + 2 S₀`,
* `W_live ≤ 2 G + K + 5 |A| (K + 1) + 2 S` and `S ≤ S₀`.

The lower bound is the message-volume lower bound of the full-incidence implementation.
Releases of retired actions are paid once and are part of the `2 G` term.  The rule (i) of
`thm:protected-pruning` (retiring internal incidences) is not implemented by this monitor,
so `R` counts root retirements only. -/
theorem ram_work_bounds (circ : A → MaxCirc Z) (x : ℕ → Z → ℝ × ℝ) (ε : ℝ) (K : ℕ) :
    (∑ k ∈ range K, ∑ a, monDeliv (x k) (x (k + 1)) (circ a) ≤ monWork false circ x ε K) ∧
    (monWork false circ x ε K ≤ 2 * ∑ a, (circ a).monSize + K + 2 * Fintype.card A * (K + 1)
      + 2 * ∑ k ∈ range K, ∑ a, monDeliv (x k) (x (k + 1)) (circ a)) ∧
    (monWork true circ x ε K ≤ 2 * ∑ a, (circ a).monSize + K + 5 * Fintype.card A * (K + 1)
      + 2 * ∑ k ∈ range K, ∑ a ∈ (monRun true circ x (k + 1)).act,
          monDeliv (x k) (x (k + 1)) (circ a)) ∧
    (∑ k ∈ range K, ∑ a ∈ (monRun true circ x (k + 1)).act, monDeliv (x k) (x (k + 1)) (circ a)
      ≤ ∑ k ∈ range K, ∑ a, monDeliv (x k) (x (k + 1)) (circ a)) := by
  have hcard : ∀ k, (monRun true circ x k).act.card ≤ Fintype.card A :=
    fun k => Finset.card_le_univ _
  have key1 : ∑ k ∈ range K, ∑ a, monDelivCost (x k) (x (k + 1)) (circ a)
      ≤ 2 * ∑ k ∈ range K, ∑ a, monDeliv (x k) (x (k + 1)) (circ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => monDelivCost_le_two _ _ _)
  have key2 : ∑ k ∈ range K, ∑ a ∈ (monRun true circ x (k + 1)).act,
        monDelivCost (x k) (x (k + 1)) (circ a)
      ≤ 2 * ∑ k ∈ range K, ∑ a ∈ (monRun true circ x (k + 1)).act,
        monDeliv (x k) (x (k + 1)) (circ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => monDelivCost_le_two _ _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [monWork_false_eq]
    refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum
      (fun a _ => monDeliv_le_cost _ _ _))) (Nat.le_add_left _ _)
  · rw [monWork_false_eq]
    omega
  · rw [monWork_true_eq]
    have h1 : ∑ k ∈ range K, 5 * (monRun true circ x k).act.card
        ≤ ∑ _k ∈ range K, 5 * Fintype.card A :=
      Finset.sum_le_sum (fun k _ => Nat.mul_le_mul_left 5 (hcard k))
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
    have h3 := hcard K
    have e : 5 * Fintype.card A * (K + 1) = K * (5 * Fintype.card A) + 5 * Fintype.card A := by
      ring
    omega
  · exact Finset.sum_le_sum (fun k _ =>
      Finset.sum_le_sum_of_subset (Finset.subset_univ _))

end Run

/-! ### The `m`-leaf graph of `sec:v2separation` -/

section MLeaf

/-- Balanced binary fan-out with `m` unary leaves `b₁, …, b_m`, each pointing to the
terminal `z = 2`; `d` bounds the recursion depth. -/
def monFanAux : ℕ → ℕ → MaxCirc (Fin 3)
  | 0, _ => .unary (.term 2)
  | d + 1, m =>
      if m ≤ 1 then .unary (.term 2)
      else .bin (monFanAux d ((m + 1) / 2)) (monFanAux d (m / 2))

/-- The subgraph below the root action `C`: a balanced binary tree with `m` unary leaves,
all pointing to the terminal `z` (for `m = 1` the single unary vertex `b₁`). -/
def monFan (m : ℕ) : MaxCirc (Fin 3) := monFanAux (Nat.clog 2 m) m

theorem monFanAux_onlyTerm : ∀ d m, MaxCirc.OnlyTerm 2 (monFanAux d m)
  | 0, _ => rfl
  | d + 1, m => by
      unfold monFanAux
      split_ifs
      · rfl
      · exact ⟨monFanAux_onlyTerm d _, monFanAux_onlyTerm d _⟩

theorem monFanAux_height : ∀ d m, (monFanAux d m).monHeight ≤ d + 1
  | 0, _ => le_rfl
  | d + 1, m => by
      unfold monFanAux
      split_ifs
      · show 1 ≤ d + 1 + 1
        omega
      · have h1 := monFanAux_height d ((m + 1) / 2)
        have h2 := monFanAux_height d (m / 2)
        show max _ _ + 1 ≤ d + 1 + 1
        omega

theorem monFanAux_count : ∀ d m, 1 ≤ m → m ≤ 2 ^ d →
    (monFanAux d m).monEdges + 2 = 3 * m ∧ (monFanAux d m).monSize + 1 = 3 * m
  | 0, m, h1, h2 => by
      have : m = 1 := by
        rw [pow_zero] at h2
        omega
      subst this
      exact ⟨rfl, rfl⟩
  | d + 1, m, h1, h2 => by
      unfold monFanAux
      split_ifs with hm
      · have : m = 1 := by omega
        subst this
        exact ⟨rfl, rfl⟩
      · rw [pow_succ] at h2
        obtain ⟨a1, a2⟩ := monFanAux_count d ((m + 1) / 2) (by omega) (by omega)
        obtain ⟨b1, b2⟩ := monFanAux_count d (m / 2) (by omega) (by omega)
        constructor
        · show (monFanAux d ((m + 1) / 2)).monEdges + (monFanAux d (m / 2)).monEdges + 2 + 2
            = 3 * m
          omega
        · show (monFanAux d ((m + 1) / 2)).monSize + (monFanAux d (m / 2)).monSize + 1 + 1
            = 3 * m
          omega

/-- The fan has `m` unary and `m - 1` binary vertices: `3m - 2` incidences, `3m - 1`
vertices of the unfolding, and height at most `⌈log₂ m⌉ + 1`. -/
theorem monFan_count {m : ℕ} (hm : 1 ≤ m) :
    (monFan m).monEdges + 2 = 3 * m ∧ (monFan m).monSize + 1 = 3 * m :=
  monFanAux_count _ m hm (Nat.le_pow_clog (by norm_num) m)

theorem monFan_height (m : ℕ) : (monFan m).monHeight ≤ Nat.clog 2 m + 1 :=
  monFanAux_height _ m

/-- The subgraph below each root action: `A = 0` and `B = 1` are terminal vertices, `C = 2`
is the fan. -/
def monRootCirc (m : ℕ) (a : Fin 3) : MaxCirc (Fin 3) := if a = 2 then monFan m else .term a

theorem monRootCirc_onlyTerm (m : ℕ) (a : Fin 3) : MaxCirc.OnlyTerm a (monRootCirc m a) := by
  unfold monRootCirc
  split_ifs with h
  · subst h
    exact monFanAux_onlyTerm _ _
  · rfl

theorem monRootCirc_zero (m : ℕ) : monRootCirc m 0 = .term 0 := by simp [monRootCirc]

theorem monRootCirc_one (m : ℕ) : monRootCirc m 1 = .term 1 := by simp [monRootCirc]

theorem monRootCirc_two (m : ℕ) : monRootCirc m 2 = monFan m := by simp [monRootCirc]

/-- The graph has `Θ(m)` vertices. -/
theorem monRootCirc_size {m : ℕ} (hm : 1 ≤ m) : ∑ a, (monRootCirc m a).monSize = 3 * m + 1 := by
  have := (monFan_count hm).2
  rw [Fin.sum_univ_three, monRootCirc_zero, monRootCirc_one, monRootCirc_two]
  show 1 + 1 + (monFan m).monSize = 3 * m + 1
  omega

/-! #### The search process on the graph is the three-terminal process -/

/-- A run of the root-PUCT controller on the `m`-leaf graph with point-mass rewards
`mu3 g` at the three terminals.  `N t a` and `S t a` are the controller's count and reward
sum of root action `a` after `t` rollouts; `rule t` is the path rule used below the root at
rollout `t` (arbitrary: any deterministic local rule).  One forced rollout through each
action, then at each `t ≥ 3` an action maximizing the index computed from the *empirical*
mean `S/N` is selected, the path below it is walked to a terminal, and the reward of the
terminal reached is observed. -/
structure MonGraphRun (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool) (N : ℕ → Fin 3 → ℕ)
    (S : ℕ → Fin 3 → ℝ) (sel : ℕ → Fin 3) : Prop where
  initN : ∀ a, N 3 a = 1
  initS : ∀ a : Fin 3, S 3 a = mu3 g ((monRootCirc m a).monWalk (rule a) 0).1
  stepN : ∀ t, 3 ≤ t → ∀ a, N (t + 1) a = N t a + if sel t = a then 1 else 0
  stepS : ∀ t, 3 ≤ t → ∀ a, S (t + 1) a
    = S t a + if sel t = a then mu3 g ((monRootCirc m a).monWalk (rule t) 0).1 else 0
  greedy : ∀ t, 3 ≤ t → ∀ j, S t j / N t j + Real.sqrt t / (1 + N t j)
    ≤ S t (sel t) / N t (sel t) + Real.sqrt t / (1 + N t (sel t))

section GraphRun

variable {m : ℕ} {g : ℝ} {rule : ℕ → ℕ → Bool} {N : ℕ → Fin 3 → ℕ} {S : ℕ → Fin 3 → ℝ}
  {sel : ℕ → Fin 3}

/-- Every rollout through the root action `a` reaches the terminal `a` (below `C` every
path reaches `z`), whatever the path rule. -/
theorem monRootCirc_walk (m : ℕ) (r : ℕ → Bool) (a : Fin 3) :
    ((monRootCirc m a).monWalk r 0).1 = a :=
  MaxCirc.monWalk_fst_of_onlyTerm r _ 0 (monRootCirc_onlyTerm m a)

theorem MonGraphRun.sum_eq (h : MonGraphRun m g rule N S sel) :
    ∀ t, 3 ≤ t → ∀ a, S t a = N t a * mu3 g a := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro a
    rw [h.initS, h.initN, monRootCirc_walk]
    simp
  | succ t ht ih =>
    intro a
    rw [h.stepS t ht, h.stepN t ht, ih a, monRootCirc_walk]
    split_ifs <;> push_cast <;> ring

theorem MonGraphRun.one_le (h : MonGraphRun m g rule N S sel) :
    ∀ t, 3 ≤ t → ∀ a, 1 ≤ N t a := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro a; rw [h.initN]
  | succ t ht ih => intro a; rw [h.stepN t ht]; exact (ih a).trans (Nat.le_add_right _ _)

/-- **Identification with the three-terminal process (`thm:v2separation`, first step).**
On the `m`-leaf graph the empirical root means are exactly `mu3 g`, and the root counts
and selections form a trace of the three-terminal root-PUCT process analysed in
`RootPUCT.lean`. -/
theorem MonGraphRun.trace (h : MonGraphRun m g rule N S sel) :
    RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) N sel where
  init := fun i => by rw [Fintype.card_fin]; exact h.initN i
  step := fun t ht i => h.stepN t (by rwa [Fintype.card_fin] at ht) i
  greedy := by
    intro t ht j
    rw [Fintype.card_fin] at ht
    have hq : ∀ a, S t a / N t a = mu3 g a := by
      intro a
      have hpos : (N t a : ℝ) ≠ 0 := by
        have := h.one_le t ht a
        exact_mod_cast (by omega : N t a ≠ 0)
      rw [h.sum_eq t ht a, mul_div_cancel_left₀ _ hpos]
    have := h.greedy t ht j
    rw [hq, hq] at this
    unfold rootPuctIndex
    simp only [one_mul]
    exact this

/-- Runs exist for every size, gap and path rule. -/
theorem exists_monGraphRun (m : ℕ) (g : ℝ) (rule : ℕ → ℕ → Bool) :
    ∃ N S sel, MonGraphRun m g rule N S sel := by
  obtain ⟨n, sel, h⟩ := exists_rootPUCTTrace (mu3 g) (fun _ : Fin 3 => (1 : ℝ))
  have hc : ∀ t, 3 ≤ t → Fintype.card (Fin 3) ≤ t := fun t ht => by
    rw [Fintype.card_fin]; exact ht
  refine ⟨n, fun t a => n t a * mu3 g a, sel, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have := h.init a
    rwa [Fintype.card_fin] at this
  · intro a
    have := h.init a
    rw [Fintype.card_fin] at this
    rw [this, monRootCirc_walk]
    simp
  · exact fun t ht a => h.step t (hc t ht) a
  · intro t ht a
    rw [h.step t (hc t ht) a, monRootCirc_walk]
    split_ifs <;> push_cast <;> ring
  · intro t ht j
    have hq : ∀ a, (n t a : ℝ) * mu3 g a / n t a = mu3 g a := by
      intro a
      have hpos : (n t a : ℝ) ≠ 0 := by
        have := h.one_le a (hc t ht)
        exact_mod_cast (by omega : n t a ≠ 0)
      rw [mul_div_cancel_left₀ _ hpos]
    have := h.greedy t (hc t ht) j
    unfold rootPuctIndex at this
    simp only [one_mul] at this
    show (n t j : ℝ) * mu3 g j / n t j + _ ≤ (n t (sel t) : ℝ) * mu3 g (sel t) / n t (sel t) + _
    rw [hq, hq]
    exact this

end GraphRun

/-! #### The two monitors along the run -/

/-- The common terminal observation table after `t` observations: the clipped interval
`eq:v2radius` of each terminal at its count (the count of terminal `a` is the root count
`N t a` and its empirical mean is `mu3 g a`, by `MonGraphRun.trace` and
`MonGraphRun.sum_eq`). -/
def monTab (δ g : ℝ) (N : ℕ → Fin 3 → ℕ) (t : ℕ) (z : Fin 3) : ℝ × ℝ :=
  (L3 δ g (N t) z, U3 δ g (N t) z)

/-- The table seen by the monitors at their step `k`, i.e. after `3 + k` observations. -/
def monBox (δ g : ℝ) (N : ℕ → Fin 3 → ℕ) (k : ℕ) : Fin 3 → ℝ × ℝ := monTab δ g N (3 + k)

variable {δ g : ℝ} {N : ℕ → Fin 3 → ℕ} {sel : ℕ → Fin 3}

theorem monL_box (m : ℕ) (δ g : ℝ) (N : ℕ → Fin 3 → ℕ) (k : ℕ) (a : Fin 3) :
    monL (monRootCirc m) (monBox δ g N) k a = L3 δ g (N (3 + k)) a := by
  unfold monL
  rw [MaxCirc.ival_of_onlyTerm _ (monRootCirc_onlyTerm m a)]
  rfl

theorem monU_box (m : ℕ) (δ g : ℝ) (N : ℕ → Fin 3 → ℕ) (k : ℕ) (a : Fin 3) :
    monU (monRootCirc m) (monBox δ g N) k a = U3 δ g (N (3 + k)) a := by
  unfold monU
  rw [MaxCirc.ival_of_onlyTerm _ (monRootCirc_onlyTerm m a)]
  rfl

private theorem card3_le (k : ℕ) : Fintype.card (Fin 3) ≤ 3 + k := by
  rw [Fintype.card_fin]
  omega

theorem marginalStops_univ_iff (L U : Fin 3 → ℝ) (ε : ℝ) (a : Fin 3) :
    MarginalStops univ L U ε a ↔ RootPuctStops L U ε a := by
  simp [MarginalStops, RootPuctStops, LowLeader, RootPuctLeader]

section Outputs

variable (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8)
  (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) N sel)

include hδ0 hδ h in
theorem v2_nestedL (m : ℕ) (a : Fin 3) (s t : ℕ) (hst : s ≤ t) :
    monL (monRootCirc m) (monBox δ g N) s a ≤ monL (monRootCirc m) (monBox δ g N) t a := by
  rw [monL_box, monL_box]
  exact rootPuctLo_mono hδ0 hδ (h.one_le a (card3_le s))
    (h.mono a (card3_le s) (by omega))

include hδ0 hδ h in
theorem v2_nestedU (m : ℕ) (a : Fin 3) (s t : ℕ) (hst : s ≤ t) :
    monU (monRootCirc m) (monBox δ g N) t a ≤ monU (monRootCirc m) (monBox δ g N) s a := by
  rw [monU_box, monU_box]
  exact rootPuctHi_anti hδ0 hδ (h.one_le a (card3_le s))
    (h.mono a (card3_le s) (by omega))

include hg hg8 in
theorem v2_nonempty (m : ℕ) (t : ℕ) (a : Fin 3) :
    monL (monRootCirc m) (monBox δ g N) t a ≤ monU (monRootCirc m) (monBox δ g N) t a := by
  rw [monL_box, monU_box]
  have h1 : L3 δ g (N (3 + t)) a ≤ mu3 g a := rootPuctLo_le_mean (mu3_nonneg hg8 a)
  have h2 : mu3 g a ≤ U3 δ g (N (3 + t)) a :=
    mean_le_puctHi ((mu3_le hg.le a).trans (by norm_num))
  exact h1.trans h2

include hδ0 hδ hg hg8 h in
/-- **`thm:v2separation`: identical leaders and stopping bits.**  At every observation
count `3 + k` the decision-selective monitor and the full incidence monitor expose the same
output; its stopping set is the set of leaders at which the three-terminal check `Stop3`
succeeds, and its leader set is the canonical lower-bound leader of the three-terminal
process.  Since the controller never reads anything else, sampled paths, observations and
stopping times coincide. -/
theorem v2_outputs (m k : ℕ) :
    (monQuery (g / 2) (monBox δ g N k) (monRun true (monRootCirc m) (monBox δ g N) k)).1
        = (monQuery (g / 2) (monBox δ g N k) (monRun false (monRootCirc m) (monBox δ g N) k)).1 ∧
      (monQuery (g / 2) (monBox δ g N k)
          (monRun false (monRootCirc m) (monBox δ g N) k)).1.stops
        = {a | Stop3 δ g (N (3 + k)) a} ∧
      (monQuery (g / 2) (monBox δ g N k)
          (monRun false (monRootCirc m) (monBox δ g N) k)).1.leaders
        = {a | RootPuctLeader (L3 δ g (N (3 + k))) a} := by
  obtain ⟨e1, e2⟩ := monRun_outputs (circ := monRootCirc m) (x := monBox δ g N)
    (v2_nestedL hδ0 hδ h m) (v2_nestedU hδ0 hδ h m) (v2_nonempty hg hg8 m)
    (ε := g / 2) (by linarith) k
  have hLf : monL (monRootCirc m) (monBox δ g N) k = L3 δ g (N (3 + k)) :=
    funext (monL_box m δ g N k)
  have hUf : monU (monRootCirc m) (monBox δ g N) k = U3 δ g (N (3 + k)) :=
    funext (monU_box m δ g N k)
  refine ⟨e1, ?_, ?_⟩
  · rw [e2, hLf, hUf]
    ext a
    exact marginalStops_univ_iff _ _ _ a
  · rw [e2, hLf]
    ext a
    simp [LowLeader, RootPuctLeader]

include hg hg8 in
/-- The optimal action `A` is never retired by the selective monitor. -/
theorem v2_A_active (m : ℕ) :
    ∀ k, (0 : Fin 3) ∈ (monRun true (monRootCirc m) (monBox δ g N) k).act
  | 0 => mem_univ _
  | k + 1 => by
      refine (mem_monRun_act_succ _ _ k 0).mpr ⟨v2_A_active m k, ?_⟩
      rintro ⟨a, -, -, hlt⟩
      rw [monU_box, monL_box] at hlt
      have h1 : L3 δ g (N (3 + k)) a ≤ 3 / 4 :=
        (rootPuctLo_le_mean (mu3_nonneg hg8 a)).trans (mu3_le hg.le a)
      have h2 : (3 / 4 : ℝ) ≤ U3 δ g (N (3 + k)) 0 :=
        mean_le_puctHi (μ := mu3 g 0) (by rw [mu3_zero]; norm_num)
      linarith

include hg hg8 in
/-- Once `U_C < L_A` at observation count `T`, the selective monitor has retired `C` (and
released the fan) at every later count. -/
theorem v2_C_retired (m : ℕ) {T : ℕ} (hT : 3 ≤ T) (hcut : U3 δ g (N T) 2 < L3 δ g (N T) 0) :
    ∀ k, T < 3 + k → (2 : Fin 3) ∉ (monRun true (monRootCirc m) (monBox δ g N) k).act := by
  have base : (2 : Fin 3) ∉ (monRun true (monRootCirc m) (monBox δ g N) (T - 3 + 1)).act := by
    intro hmem
    refine ((mem_monRun_act_succ _ _ (T - 3) 2).mp hmem).2
      ⟨0, v2_A_active hg hg8 m (T - 3), by decide, ?_⟩
    rw [monU_box, monL_box]
    have e : 3 + (T - 3) = T := by omega
    rw [e]
    exact hcut
  have all : ∀ j, (2 : Fin 3) ∉
      (monRun true (monRootCirc m) (monBox δ g N) (T - 3 + 1 + j)).act := by
    intro j
    induction j with
    | zero => exact base
    | succ j ih => exact fun hmem => ih (monRun_act_anti _ _ _ hmem)
  intro k hk
  have e : k = T - 3 + 1 + (k - (T - 3 + 1)) := by omega
  rw [e]
  exact all _

end Outputs

/-- A uniform time at which `U_C < L_A` (the retirement witness used by the selective
monitor), independent of `g` and of the trace; cf. `cut3_uniform`. -/
theorem cutA_uniform (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ T : ℕ, 6 ≤ T ∧ ∀ g : ℝ, 0 < g → g ≤ 1 / 8 → ∀ (n : ℕ → Fin 3 → ℕ) (sel : ℕ → Fin 3),
      RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) n sel → U3 δ g (n T) 2 < L3 δ g (n T) 0 := by
  obtain ⟨F, hF⟩ : ∃ F, F = 512 * Real.log (1536 / δ) := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      rw [le_div_iff₀ hδ0]
      linarith))
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = ⌈(2 * F + 50) ^ 2⌉₊ := ⟨_, rfl⟩
  have hT_lo : (2 * F + 50) ^ 2 ≤ T := by rw [hT]; exact Nat.le_ceil _
  have hsqrt : 2 * F + 50 ≤ Real.sqrt T := by
    rw [Real.le_sqrt (by linarith) (Nat.cast_nonneg T)]
    exact hT_lo
  have hT6 : 6 ≤ T := by
    have : (6 : ℝ) ≤ T := by nlinarith
    exact_mod_cast this
  refine ⟨T, hT6, ?_⟩
  intro g hg hg8 n sel h
  have hnA := trace3_nA hg.le h hT6
  have hnC := trace3_nC' hg.le h hT6 (by linarith)
  have hcA : F ≤ n T 0 := by nlinarith
  have hcC : F ≤ n T 2 := by linarith
  rw [hF] at hcA hcC
  have hA := rootPuctRadius_le_eighth hδ0 hδ hcA
  have hC := rootPuctRadius_le_eighth hδ0 hδ hcC
  have hLA : 5 / 8 ≤ L3 δ g (n T) 0 := by
    show 5 / 8 ≤ max 0 (3 / 4 - rootPuctRadius δ (n T 0))
    exact le_max_of_le_right (by linarith)
  have hUC : U3 δ g (n T) 2 ≤ 3 / 8 := by
    show min 1 (1 / 4 + rootPuctRadius δ (n T 2)) ≤ 3 / 8
    exact (min_le_right _ _).trans (by linarith)
  linarith

/-! #### Work of the complete runs -/

/-- Work of one rollout through root action `a` at time `t`: three root index evaluations,
one step down and one step back up per traversed edge, and the root and terminal table
updates. -/
def monRollout (m : ℕ) (rule : ℕ → ℕ → Bool) (t : ℕ) (a : Fin 3) : ℕ :=
  2 * ((monRootCirc m a).monWalk (rule t) 0).2 + 5

theorem monRollout_le (m : ℕ) (rule : ℕ → ℕ → Bool) (t : ℕ) (a : Fin 3) :
    monRollout m rule t a ≤ 5 + if a = 2 then 2 * (Nat.clog 2 m + 1) else 0 := by
  unfold monRollout monRootCirc
  split_ifs with ha
  · have := (MaxCirc.monWalk_snd_le (rule t) (monFan m) 0).trans (monFan_height m)
    omega
  · simp [MaxCirc.monWalk]

/-- Total work of the run stopped at observation count `τ`, with the selective
(`s = true`) or the full (`s = false`) monitor: reading and initializing the graph and its
final disposal, the three forced rollouts, the rollouts at times `3, …, τ - 1`, and the
monitor work (build, terminal-table updates, waves, retirement, a query after every
observation, disposal). -/
def v2Work (s : Bool) (m : ℕ) (δ g : ℝ) (rule : ℕ → ℕ → Bool) (N : ℕ → Fin 3 → ℕ)
    (sel : ℕ → Fin 3) (τ : ℕ) : ℕ :=
  2 * ∑ a, (monRootCirc m a).monSize + ∑ a : Fin 3, monRollout m rule a a
    + ∑ t ∈ Ico 3 τ, monRollout m rule t (sel t)
    + monWork s (monRootCirc m) (monBox δ g N) (g / 2) (τ - 3)

theorem RootPUCTTrace.count_Ico {ι : Type*} [Fintype ι] [DecidableEq ι] {μ lam : ι → ℝ}
    {n : ℕ → ι → ℕ} {sel : ℕ → ι} (h : RootPUCTTrace μ lam n sel) (i : ι) {s t : ℕ}
    (hs : Fintype.card ι ≤ s) (hst : s ≤ t) :
    n t i = n s i + ∑ u ∈ Ico s t, if sel u = i then 1 else 0 := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    rw [h.step t (hs.trans hst), ih, Finset.sum_Ico_succ_top hst]
    ring

section Costs

variable (h : RootPUCTTrace (mu3 g) (fun _ => (1 : ℝ)) N sel)

theorem v2_sum_delivCost (m : ℕ) (x x' : Fin 3 → ℝ × ℝ) :
    ∑ a, monDelivCost x x' (monRootCirc m a) = monDelivCost x x' (monFan m) := by
  rw [Fin.sum_univ_three, monRootCirc_zero, monRootCirc_one, monRootCirc_two]
  show 0 + 0 + _ = _
  omega

include h in
/-- A wave of the full monitor costs at most `6m`, and nothing unless `C` was observed. -/
theorem v2_wave_le {m : ℕ} (hm : 1 ≤ m) (t : ℕ) (ht : 3 ≤ t) :
    monDelivCost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m)
      ≤ if sel t = 2 then 6 * m else 0 := by
  split_ifs with hsel
  · have h1 := monDelivCost_le_two (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m)
    have h2 := monDeliv_le_edges (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m)
    have h3 := (monFan_count hm).1
    omega
  · have hstep := h.step t (by rw [Fintype.card_fin]; exact ht) 2
    rw [ite_eq_right hsel, add_zero] at hstep
    have hx : monTab δ g N (t + 1) 2 = monTab δ g N t 2 := by
      unfold monTab L3 U3
      rw [hstep]
    exact le_of_eq (monDelivCost_eq_zero_of_onlyTerm hx (monFan m) (monFanAux_onlyTerm _ _))

/-- A wave of the full monitor after an observation that changes `U_z` crosses all `m`
incidences `(b_i, z)`: its work is at least `m`. -/
theorem v2_wave_ge {m : ℕ} (hm : 1 ≤ m) (t : ℕ)
    (hlt : U3 δ g (N (t + 1)) 2 < U3 δ g (N t) 2) :
    m ≤ monDelivCost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m) := by
  have hx : monTab δ g N (t + 1) 2 ≠ monTab δ g N t 2 := by
    intro e
    have e2 : U3 δ g (N (t + 1)) 2 = U3 δ g (N t) 2 := congrArg Prod.snd e
    exact absurd e2 (ne_of_lt hlt)
  have h1 := monDeliv_le_cost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m)
  have h2 := monDeliv_of_onlyTerm_ne hx (monFan m) (monFanAux_onlyTerm _ _)
  have h3 := (monFan_count hm).1
  omega

private theorem sum_ite_lt_le (K T c : ℕ) :
    ∑ k ∈ range K, (if k < T then c else 0) ≤ T * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  calc ((range K).filter (fun k => k < T)).card ≤ (range T).card :=
        Finset.card_le_card (fun k hk => by
          rw [mem_filter] at hk
          exact mem_range.mpr hk.2)
    _ = T := Finset.card_range T

private theorem v2_rollouts_le (m : ℕ) (rule : ℕ → ℕ → Bool) (sel : ℕ → Fin 3) (τ : ℕ) :
    ∑ a : Fin 3, monRollout m rule a a + ∑ t ∈ Ico 3 τ, monRollout m rule t (sel t)
      ≤ 15 + 2 * (Nat.clog 2 m + 1) + 5 * (τ - 3)
        + 2 * (Nat.clog 2 m + 1) * ∑ t ∈ Ico 3 τ, (if sel t = 2 then 1 else 0) := by
  have h1 : ∑ a : Fin 3, monRollout m rule a a ≤ 15 + 2 * (Nat.clog 2 m + 1) := by
    rw [Fin.sum_univ_three]
    have a0 := monRollout_le m rule ((0 : Fin 3) : ℕ) 0
    have a1 := monRollout_le m rule ((1 : Fin 3) : ℕ) 1
    have a2 := monRollout_le m rule ((2 : Fin 3) : ℕ) 2
    simp only [Fin.reduceEq, ite_true, ite_false] at a0 a1 a2
    omega
  have h2 : ∑ t ∈ Ico 3 τ, monRollout m rule t (sel t)
      ≤ ∑ t ∈ Ico 3 τ, (5 + 2 * (Nat.clog 2 m + 1) * (if sel t = 2 then 1 else 0)) := by
    refine Finset.sum_le_sum (fun t _ => ?_)
    have := monRollout_le m rule t (sel t)
    split_ifs at this ⊢ with hs <;> omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, ← Finset.mul_sum]
    at h2
  omega

include h in
/-- **`eq:v2fullaccounting`, in natural numbers.**  Work of the selective run:
`W_selective ≤ (12 + 6 T₀) m + 21 τ + 2 (⌈log₂ m⌉ + 1) n_C(τ) + 25`, where `T₀` is any
observation count at which `U_C < L_A`. -/
theorem v2Work_selective_le (hg : 0 < g) (hg8 : g ≤ 1 / 8) {m : ℕ} (hm : 1 ≤ m)
    (rule : ℕ → ℕ → Bool) {T0 : ℕ} (hT0 : 3 ≤ T0)
    (hcut : U3 δ g (N T0) 2 < L3 δ g (N T0) 0) {τ : ℕ} (hτ : 3 ≤ τ) :
    v2Work true m δ g rule N sel τ
      ≤ (12 + 6 * T0) * m + 21 * τ + 2 * (Nat.clog 2 m + 1) * N τ 2 + 25 := by
  have hG := monRootCirc_size hm
  have hroll := v2_rollouts_le m rule sel τ
  have hcnt := h.count_Ico 2 (s := 3) (t := τ) (by rw [Fintype.card_fin]) hτ
  have hN3 : N 3 2 = 1 := by
    have := h.init 2
    rwa [Fintype.card_fin] at this
  rw [hN3] at hcnt
  have hcard : ∀ k, (monRun true (monRootCirc m) (monBox δ g N) k).act.card ≤ 3 := fun k => by
    have := Finset.card_le_univ (monRun true (monRootCirc m) (monBox δ g N) k).act
    rwa [Fintype.card_fin] at this
  have h5 : ∑ k ∈ range (τ - 3), 5 * (monRun true (monRootCirc m) (monBox δ g N) k).act.card
      ≤ 15 * (τ - 3) := by
    have : ∑ k ∈ range (τ - 3), 5 * (monRun true (monRootCirc m) (monBox δ g N) k).act.card
        ≤ ∑ _k ∈ range (τ - 3), 15 :=
      Finset.sum_le_sum (fun k _ => by have := hcard k; omega)
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    omega
  have hw : ∑ k ∈ range (τ - 3), ∑ a ∈ (monRun true (monRootCirc m) (monBox δ g N) (k + 1)).act,
        monDelivCost (monBox δ g N k) (monBox δ g N (k + 1)) (monRootCirc m a)
      ≤ T0 * (6 * m) := by
    refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (sum_ite_lt_le (τ - 3) T0 (6 * m))
    by_cases hk : k < T0
    · rw [ite_eq_left hk]
      refine le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) ?_
      rw [v2_sum_delivCost]
      refine le_trans (v2_wave_le h hm (3 + k) (by omega)) ?_
      split_ifs <;> omega
    · rw [ite_eq_right hk]
      have hC := v2_C_retired hg hg8 m hT0 hcut (k + 1) (by omega)
      refine le_of_eq (Finset.sum_eq_zero (fun a ha => ?_))
      have ha2 : a ≠ 2 := fun e => hC (e ▸ ha)
      have : monRootCirc m a = .term a := by simp [monRootCirc, ha2]
      rw [this]
      rfl
  have hc := hcard (τ - 3)
  unfold v2Work
  rw [monWork_true_eq, hG]
  have e : 2 * (Nat.clog 2 m + 1) * N τ 2 = 2 * (Nat.clog 2 m + 1)
      + 2 * (Nat.clog 2 m + 1) * ∑ t ∈ Ico 3 τ, (if sel t = 2 then 1 else 0) := by
    rw [hcnt]
    ring
  have e2 : (12 + 6 * T0) * m = 12 * m + T0 * (6 * m) := by ring
  omega

/-- The selective run pays at least the size of the graph. -/
theorem v2Work_selective_ge {m : ℕ} (hm : 1 ≤ m) (rule : ℕ → ℕ → Bool) (τ : ℕ) :
    m ≤ v2Work true m δ g rule N sel τ := by
  have hG := monRootCirc_size hm
  unfold v2Work
  rw [hG]
  omega

private theorem v2_full_waves (m : ℕ) (τ : ℕ) :
    ∑ k ∈ range (τ - 3), ∑ a, monDelivCost (monBox δ g N k) (monBox δ g N (k + 1))
        (monRootCirc m a)
      = ∑ t ∈ Ico 3 τ, monDelivCost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m) := by
  rw [Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl (fun k _ => v2_sum_delivCost m _ _)

include h in
/-- Work of the full run: `W_full ≤ 12 m + 12 τ + 2 (⌈log₂ m⌉ + 1) n_C(τ) + 6 m n_C(τ) + 25`. -/
theorem v2Work_full_le {m : ℕ} (hm : 1 ≤ m) (rule : ℕ → ℕ → Bool) {τ : ℕ} (hτ : 3 ≤ τ) :
    v2Work false m δ g rule N sel τ
      ≤ 12 * m + 12 * τ + 2 * (Nat.clog 2 m + 1) * N τ 2 + 6 * m * N τ 2 + 25 := by
  have hG := monRootCirc_size hm
  have hroll := v2_rollouts_le m rule sel τ
  have hcnt := h.count_Ico 2 (s := 3) (t := τ) (by rw [Fintype.card_fin]) hτ
  have hN3 : N 3 2 = 1 := by
    have := h.init 2
    rwa [Fintype.card_fin] at this
  rw [hN3] at hcnt
  have hw : ∑ t ∈ Ico 3 τ, monDelivCost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m)
      ≤ 6 * m * ∑ t ∈ Ico 3 τ, (if sel t = 2 then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun t ht => ?_)
    have := v2_wave_le (δ := δ) h hm t (Finset.mem_Ico.mp ht).1
    split_ifs at this ⊢ <;> omega
  unfold v2Work
  rw [monWork_false_eq, hG, v2_full_waves, Fintype.card_fin]
  have e : 2 * (Nat.clog 2 m + 1) * N τ 2 = 2 * (Nat.clog 2 m + 1)
      + 2 * (Nat.clog 2 m + 1) * ∑ t ∈ Ico 3 τ, (if sel t = 2 then 1 else 0) := by
    rw [hcnt]
    ring
  have e2 : 6 * m * N τ 2 = 6 * m + 6 * m * ∑ t ∈ Ico 3 τ, (if sel t = 2 then 1 else 0) := by
    rw [hcnt]
    ring
  omega

include h in
/-- **Delivery lower bound for the full monitor.**  If every observation of `C` from
count `tc` on strictly changes `U_z`, then `m (n_C(τ) - n_C(tc)) ≤ W_full`. -/
theorem v2Work_full_ge {m : ℕ} (hm : 1 ≤ m) (rule : ℕ → ℕ → Bool) {tc τ : ℕ} (htc : 3 ≤ tc)
    (htcτ : tc ≤ τ)
    (hstrict : ∀ s, tc ≤ s → sel s = 2 → U3 δ g (N (s + 1)) 2 < U3 δ g (N s) 2) :
    m * (N τ 2 - N tc 2) ≤ v2Work false m δ g rule N sel τ := by
  have hcnt := h.count_Ico 2 (s := tc) (t := τ) (by rw [Fintype.card_fin]; exact htc) htcτ
  have hsub : N τ 2 - N tc 2 = ∑ t ∈ Ico tc τ, (if sel t = 2 then 1 else 0) := by omega
  have h1 : m * (N τ 2 - N tc 2)
      ≤ ∑ t ∈ Ico tc τ, monDelivCost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m) := by
    rw [hsub, Finset.mul_sum]
    refine Finset.sum_le_sum (fun t ht => ?_)
    split_ifs with hs
    · rw [mul_one]
      exact v2_wave_ge hm t (hstrict t (Finset.mem_Ico.mp ht).1 hs)
    · rw [mul_zero]
      exact Nat.zero_le _
  have h2 : ∑ t ∈ Ico tc τ, monDelivCost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m)
      ≤ ∑ t ∈ Ico 3 τ, monDelivCost (monTab δ g N t) (monTab δ g N (t + 1)) (monFan m) :=
    Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left htc)
  unfold v2Work
  rw [monWork_false_eq, v2_full_waves]
  omega

end Costs

end MLeaf

/-! ### Theorem `thm:v2separation` and Corollary `cor:v2quarter`, assembled -/

section Assembly

/-- `⌈log₂ m⌉ + 1 ≤ 3 log (2m)` for `m ≥ 1`. -/
theorem monClog_le_log {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.clog 2 m : ℕ) : ℝ) + 1 ≤ 3 * Real.log (2 * m) := by
  have hl2 := Real.log_two_gt_d9
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm'
  have h2m : Real.log (2 * m) = Real.log 2 + Real.log m :=
    Real.log_mul (by norm_num) (by positivity)
  have key : (Nat.clog 2 m : ℝ) * Real.log 2 ≤ Real.log (2 * m) := by
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · have hp := Nat.pow_pred_clog_lt_self 2 h1
      have hpos := Nat.clog_pos (b := 2) (by norm_num) h1
      have hp' : (2 : ℝ) ^ (Nat.clog 2 m).pred < m := by exact_mod_cast hp
      have hlog := Real.log_lt_log (by positivity) hp'
      rw [Real.log_pow] at hlog
      have hc : (Nat.clog 2 m : ℝ) = ((Nat.clog 2 m).pred : ℝ) + 1 := by
        have : Nat.clog 2 m = (Nat.clog 2 m).pred + 1 := by
          rw [Nat.pred_eq_sub_one]
          omega
        exact_mod_cast this
      rw [hc, h2m]
      nlinarith
    · have : m = 1 := by omega
      subst this
      rw [Nat.clog_one_right, Nat.cast_zero, zero_mul, h2m]
      linarith
  have hc0 : (0 : ℝ) ≤ Nat.clog 2 m := Nat.cast_nonneg _
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Nat.clog 2 m : ℝ) + 1)
    (by linarith : (0 : ℝ) ≤ Real.log 2 - 2 / 3)]

/-- **Theorem `thm:v2separation` (Root-PUCT work separation from uninformative
initialization).**  Fix `δ ∈ (0, 1/2]` and `α ∈ (0, 1/2)`.  There are a size `m₀` and
constants depending only on `δ, α` such that for every `m ≥ m₀`, with `g = m^{-α}` and
`ε = g/2`, for every run of the root-PUCT controller on the `m`-leaf graph (every
tie-breaking, every path rule):

* the selective and the full monitor expose the same output after every observation;
* the common first stopping count `τ` exists, the stopping set there is `{A}`, and
  `cτ m^{2α} log² m ≤ τ ≤ Cτ m^{2α} log² m` (`eq:v2taum`);
* there is a count `tc < τ` (the first cut of `prop:v2postcut`) with
  `cH m^α log m ≤ n_C(τ) - n_C(tc) ≤ CH m^α log m` (`eq:v2hm`);
* `m ≤ W_selective ≤ C₁ m` (`eq:v2wselective`);
* `cH m^{1+α} log m ≤ W_full ≤ C₂ m^{1+α} log m` (`eq:v2wfull`).

The works `v2Work` are computed by the cost model of this file.  No accounting inequality
is assumed. -/
theorem v2separation_monitors {δ α : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α < 1 / 2) :
    ∃ (m0 : ℕ) (cτ Cτ cH CH C1 C2 : ℝ), 0 < cτ ∧ 0 < cH ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-α) →
      ∀ (rule : ℕ → ℕ → Bool) (N : ℕ → Fin 3 → ℕ) (S : ℕ → Fin 3 → ℝ) (sel : ℕ → Fin 3),
      MonGraphRun m g rule N S sel →
        (∀ k, (monQuery (g / 2) (monBox δ g N k)
            (monRun true (monRootCirc m) (monBox δ g N) k)).1
          = (monQuery (g / 2) (monBox δ g N k)
            (monRun false (monRootCirc m) (monBox δ g N) k)).1) ∧
        ∃ tc τ : ℕ, 3 ≤ tc ∧ tc < τ ∧
          (∀ k, k < τ - 3 → (monQuery (g / 2) (monBox δ g N k)
            (monRun false (monRootCirc m) (monBox δ g N) k)).1.stops = ∅) ∧
          (monQuery (g / 2) (monBox δ g N (τ - 3))
            (monRun false (monRootCirc m) (monBox δ g N) (τ - 3))).1.stops = {0} ∧
          cτ * (m : ℝ) ^ (2 * α) * Real.log m ^ 2 ≤ τ ∧
          (τ : ℝ) ≤ Cτ * (m : ℝ) ^ (2 * α) * Real.log m ^ 2 ∧
          cH * (m : ℝ) ^ α * Real.log m ≤ (N τ 2 : ℝ) - N tc 2 ∧
          (N τ 2 : ℝ) - N tc 2 ≤ CH * (m : ℝ) ^ α * Real.log m ∧
          (m : ℝ) ≤ v2Work true m δ g rule N sel τ ∧
          (v2Work true m δ g rule N sel τ : ℝ) ≤ C1 * m ∧
          cH * (m : ℝ) ^ (1 + α) * Real.log m ≤ v2Work false m δ g rule N sel τ ∧
          (v2Work false m δ g rule N sel τ : ℝ) ≤ C2 * (m : ℝ) ^ (1 + α) * Real.log m := by
  obtain ⟨T, g0, C, hg0, hC, H⟩ := v2separation_horizon hδ0 hδ
  obtain ⟨T0, hT06, hcutA⟩ := cutA_uniform hδ0 hδ
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = max 8 (max (1 / g0) (36 * (1 + (T : ℝ)) / α)) := ⟨_, rfl⟩
  have hX8 : 8 ≤ X := by rw [hX]; exact le_max_left _ _
  have hXg : 1 / g0 ≤ X := by
    rw [hX]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hXT : 36 * (1 + (T : ℝ)) / α ≤ X := by
    rw [hX]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hsC : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have hT0R : (0 : ℝ) ≤ T0 := Nat.cast_nonneg _
  have hTR : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  refine ⟨max 3 ⌈X ^ (1 / α)⌉₊, 16 / 81 * α ^ 2, C * α ^ 2, α / 36, 2 * Real.sqrt C * α,
    (37 + 6 * T0) * (1 + (C * α ^ 2 + 2 * (2 * Real.sqrt C * α + T)) / ((1 - 2 * α) / 2) ^ 2),
    37 * (1 + (C * α ^ 2 + 2 * (2 * Real.sqrt C * α + T)) / ((1 - 2 * α) / 2) ^ 2
      + (2 * Real.sqrt C * α + T)),
    by positivity, by positivity, ?_⟩
  intro m hm g hgdef rule N S sel hrun
  subst hgdef
  have htr := hrun.trace
  have hm3 : 3 ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := by omega
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hmpos : (0 : ℝ) < m := by linarith
  have hXm : X ^ (1 / α) ≤ m := by
    have : ⌈X ^ (1 / α)⌉₊ ≤ m := le_trans (le_max_right _ _) hm
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have hXa : X ≤ (m : ℝ) ^ α := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hXm hα0.le
    rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hα0.ne', Real.rpow_one] at h1
    exact h1
  have hℓ1 : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hmpos]
    have := Real.exp_one_lt_d9
    linarith
  have hgpos : 0 < (m : ℝ) ^ (-α) := Real.rpow_pos_of_pos hmpos _
  have hg8 : (m : ℝ) ^ (-α) ≤ 1 / 8 := by
    rw [Real.rpow_neg hmpos.le, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  obtain ⟨tc, τ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    H α hα0 m hmpos (by linarith) N sel htr
  have htcτ : tc < τ := h8 (by linarith)
  have hout := fun k => v2_outputs hδ0 hδ hgpos hg8 htr m k
  -- abbreviations
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (m : ℝ) ^ α := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log m := ⟨_, rfl⟩
  rw [← ha, ← hℓ] at h11 h12
  rw [← ha] at hXa
  rw [← hℓ] at hℓ1
  have ha8 : 8 ≤ a := by linarith
  have haℓ : 1 ≤ a * ℓ := by nlinarith
  have hαa : 36 * (1 + (T : ℝ)) ≤ α * a := by
    have := hXT.trans hXa
    rw [div_le_iff₀ hα0] at this
    linarith
  have hP : α * a ≤ α * a * ℓ := by
    nlinarith [mul_nonneg (mul_nonneg hα0.le (by linarith : (0 : ℝ) ≤ a))
      (by linarith : (0 : ℝ) ≤ ℓ - 1)]
  have hHlo : α / 36 * a * ℓ ≤ (N τ 2 : ℝ) - N tc 2 := by linarith
  have hntc : (N tc 2 : ℝ) ≤ T := by
    have := (htr.count_le_time 2 (by rw [Fintype.card_fin]; exact h1)).trans h2
    exact_mod_cast this
  have hnC : (N τ 2 : ℝ) ≤ (2 * Real.sqrt C * α + T) * a * ℓ := by
    have : (T : ℝ) ≤ T * (a * ℓ) := le_mul_of_one_le_right hTR haℓ
    linarith
  have hn0 : (0 : ℝ) ≤ N τ 2 := Nat.cast_nonneg _
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg _
  have hlog := monClog_le_log hm1
  have hL2 : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  have hnL : 0 ≤ (N τ 2 : ℝ) * Real.log (2 * m) := mul_nonneg hn0 hL2
  have hcn : 2 * (((Nat.clog 2 m : ℕ) : ℝ) + 1) * N τ 2 ≤ 6 * (N τ 2 * Real.log (2 * m)) := by
    have := mul_le_mul_of_nonneg_right hlog hn0
    linarith
  -- accounting for the selective run
  have hsel : (v2Work true m δ ((m : ℝ) ^ (-α)) rule N sel τ : ℝ)
      ≤ (37 + 6 * T0) * (m + τ + N τ 2 * Real.log (2 * m)) := by
    have := v2Work_selective_le (δ := δ) htr hgpos hg8 hm1 rule (by omega : 3 ≤ T0)
      (hcutA _ hgpos hg8 N sel htr) h5
    have hS : (v2Work true m δ ((m : ℝ) ^ (-α)) rule N sel τ : ℝ)
        ≤ (12 + 6 * T0) * m + 21 * τ + 2 * (((Nat.clog 2 m : ℕ) : ℝ) + 1) * N τ 2 + 25 := by
      exact_mod_cast this
    have q1 := mul_nonneg hT0R hτ0
    have q2 := mul_nonneg hT0R hnL
    have q3 := mul_nonneg hT0R hmpos.le
    linarith
  -- accounting for the full run
  have hfull_up : (v2Work false m δ ((m : ℝ) ^ (-α)) rule N sel τ : ℝ)
      ≤ 37 * (m + τ + m * N τ 2 + N τ 2 * Real.log (2 * m)) := by
    have := v2Work_full_le (δ := δ) htr hm1 rule h5
    have hS : (v2Work false m δ ((m : ℝ) ^ (-α)) rule N sel τ : ℝ)
        ≤ 12 * m + 12 * τ + 2 * (((Nat.clog 2 m : ℕ) : ℝ) + 1) * N τ 2 + 6 * m * N τ 2 + 25 := by
      exact_mod_cast this
    have q1 := mul_nonneg hmpos.le hn0
    linarith
  have hfull_lo : (m : ℝ) * ((N τ 2 : ℝ) - N tc 2)
      ≤ v2Work false m δ ((m : ℝ) ^ (-α)) rule N sel τ := by
    have := v2Work_full_ge (δ := δ) htr hm1 rule h1 htcτ.le h13
    have hmono : N tc 2 ≤ N τ 2 := htr.mono 2 (by rw [Fintype.card_fin]; exact h1) htcτ.le
    have hS : ((m * (N τ 2 - N tc 2) : ℕ) : ℝ)
        ≤ v2Work false m δ ((m : ℝ) ^ (-α)) rule N sel τ := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub hmono] at hS
    exact hS
  have hwork := v2separation_work (α := α) (m := m) (τ := τ) (nC := N τ 2)
    (H := (N τ 2 : ℝ) - N tc 2) (Cτ := C * α ^ 2) (Cn := 2 * Real.sqrt C * α + T)
    (cH := α / 36) (c1 := 37 + 6 * T0) (c2 := 37) hα0 hα hmR (by positivity) (by positivity)
    (by positivity) (by norm_num) hn0
    h10
    (by rw [← ha, ← hℓ]; exact hnC) (by rw [← ha, ← hℓ]; exact hHlo) hsel hfull_lo hfull_up
  refine ⟨fun k => (hout k).1, tc, τ, h1, htcτ, ?_, ?_, h9, h10, ?_, ?_, ?_, hwork.1,
    hwork.2.1, hwork.2.2⟩
  · intro k hk
    rw [(hout k).2.1]
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact h7 (3 + k) b (by omega) (by omega)
  · rw [(hout (τ - 3)).2.1]
    have e : 3 + (τ - 3) = τ := by omega
    rw [e]
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · exact stop3_leader_eq hgpos hg8
    · rintro rfl
      exact h6
  · rw [ha, hℓ] at hHlo
    exact hHlo
  · rw [ha, hℓ] at h12
    exact h12
  · exact_mod_cast v2Work_selective_ge (δ := δ) (g := (m : ℝ) ^ (-α)) (N := N) (sel := sel)
      hm1 rule τ

/-- **Corollary `cor:v2quarter` (One explicit polynomial instance).**  With
`g_m = m^{-1/4}`: `τ = Θ(m^{1/2} log² m)`, `W_selective = Θ(m)`,
`W_full = Θ(m^{5/4} log m)`, with the same stopping count and stopping set `{A}` for both
monitors. -/
theorem v2quarter_monitors {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ (m0 : ℕ) (cτ Cτ c C1 C2 : ℝ), 0 < cτ ∧ 0 < c ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-(1 / 4 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (N : ℕ → Fin 3 → ℕ) (S : ℕ → Fin 3 → ℝ) (sel : ℕ → Fin 3),
      MonGraphRun m g rule N S sel →
        (∀ k, (monQuery (g / 2) (monBox δ g N k)
            (monRun true (monRootCirc m) (monBox δ g N) k)).1
          = (monQuery (g / 2) (monBox δ g N k)
            (monRun false (monRootCirc m) (monBox δ g N) k)).1) ∧
        ∃ τ : ℕ, 3 ≤ τ ∧
          (∀ k, k < τ - 3 → (monQuery (g / 2) (monBox δ g N k)
            (monRun false (monRootCirc m) (monBox δ g N) k)).1.stops = ∅) ∧
          (monQuery (g / 2) (monBox δ g N (τ - 3))
            (monRun false (monRootCirc m) (monBox δ g N) (τ - 3))).1.stops = {0} ∧
          cτ * (m : ℝ) ^ (1 / 2 : ℝ) * Real.log m ^ 2 ≤ τ ∧
          (τ : ℝ) ≤ Cτ * (m : ℝ) ^ (1 / 2 : ℝ) * Real.log m ^ 2 ∧
          (m : ℝ) ≤ v2Work true m δ g rule N sel τ ∧
          (v2Work true m δ g rule N sel τ : ℝ) ≤ C1 * m ∧
          c * (m : ℝ) ^ (5 / 4 : ℝ) * Real.log m ≤ v2Work false m δ g rule N sel τ ∧
          (v2Work false m δ g rule N sel τ : ℝ) ≤ C2 * (m : ℝ) ^ (5 / 4 : ℝ) * Real.log m := by
  obtain ⟨m0, cτ, Cτ, cH, CH, C1, C2, hcτ, hcH, H⟩ :=
    v2separation_monitors hδ0 hδ (α := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨m0, cτ, Cτ, cH, C1, C2, hcτ, hcH, ?_⟩
  intro m hm g hg rule N S sel hrun
  obtain ⟨hout, tc, τ, h1, h2, h3, h4, h5, h6, -, -, h9, h10, h11, h12⟩ :=
    H m hm g hg rule N S sel hrun
  have e1 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
  rw [e1] at h5 h6
  rw [e2] at h11 h12
  exact ⟨hout, τ, by omega, h3, h4, h5, h6, h9, h10, h11, h12⟩

end Assembly

/-! ### Proposition `prop:v2escape`: the alias monitor -/

section Escape

variable {A Z : Type*} [DecidableEq Z]

/-- Preprocessing of the alias monitor: traverse the circuit once and return its unique
reachable terminal, if there is exactly one.  Work: one step per vertex. -/
def monAlias : MaxCirc Z → Option Z × ℕ
  | .term z => (some z, 1)
  | .unary c => ((monAlias c).1, (monAlias c).2 + 1)
  | .bin c d =>
      ((monAlias c).1.bind (fun z => (monAlias d).1.bind (fun w => if z = w then some z else none)),
        (monAlias c).2 + (monAlias d).2 + 1)

theorem monAlias_cost : ∀ c : MaxCirc Z, (monAlias c).2 = c.monSize
  | .term _ => rfl
  | .unary c => by
      show (monAlias c).2 + 1 = c.monSize + 1
      rw [monAlias_cost c]
  | .bin c d => by
      show (monAlias c).2 + (monAlias d).2 + 1 = c.monSize + d.monSize + 1
      rw [monAlias_cost c, monAlias_cost d]

/-- The preprocessing returns `z` exactly when `z` is the only terminal below the vertex. -/
theorem monAlias_spec : ∀ (c : MaxCirc Z) (z : Z), (monAlias c).1 = some z ↔ MaxCirc.OnlyTerm z c
  | .term w, z => by
      show some w = some z ↔ w = z
      exact Option.some_inj
  | .unary c, z => monAlias_spec c z
  | .bin c d, z => by
      show (monAlias c).1.bind (fun z => (monAlias d).1.bind
        (fun w => if z = w then some z else none)) = some z
        ↔ MaxCirc.OnlyTerm z c ∧ MaxCirc.OnlyTerm z d
      rw [← monAlias_spec c z, ← monAlias_spec d z]
      cases hc : (monAlias c).1 with
      | none => simp
      | some z1 =>
        cases hd : (monAlias d).1 with
        | none => simp
        | some w =>
          by_cases hzw : z1 = w
          · subst hzw
            simp
          · simp only [Option.bind_some, ite_eq_right hzw, Option.some.injEq]
            constructor
            · intro h
              exact absurd h (by simp)
            · rintro ⟨rfl, rfl⟩
              exact absurd rfl hzw

/-- The interval vector exposed by the alias monitor: read the terminal table at the alias
of each action. -/
def monAliasVec (circ : A → MaxCirc Z) (x : Z → ℝ × ℝ) (a : A) : Option (ℝ × ℝ) :=
  (monAlias (circ a)).1.map x

/-- Monitor work of the alias implementation for `K` terminal updates: the preprocessing,
then one terminal-table step per update and one table read per action for each complete
interval-vector query (one query after the build and after every update). -/
def monAliasWork [Fintype A] (circ : A → MaxCirc Z) (K : ℕ) : ℕ :=
  ∑ a, (monAlias (circ a)).2 + ∑ _k ∈ range K, (1 + Fintype.card A) + Fintype.card A

/-- **Proposition `prop:v2escape` (The family does not lower-bound all numerical
oracles).**  On the `m`-leaf graph:

* the preprocessing finds the alias `a` for every root action `a` (`z` for `C`), and the
  alias vector is the exact root-action interval vector `ival` for every terminal table;
* on any box `[l, u]` the exact interval of action `a` is `[l a, u a]`;
* the alias vector equals the complete interval vector stored by the full monitor at every
  step of every run;
* the alias monitor's work for `K` updates is `3m + 4K + 4`, i.e. `O(m + τ)`.

Hence the lower bound `W_full ≥ m · H` of `v2separation_monitors` is a property of the
full-incidence architecture, not of exact interval maintenance. -/
theorem v2escape {m : ℕ} (hm : 1 ≤ m) :
    (∀ (x : Fin 3 → ℝ × ℝ) (a : Fin 3),
      monAliasVec (monRootCirc m) x a = some ((monRootCirc m a).ival x)) ∧
    (∀ (l u : Fin 3 → ℝ), l ≤ u → ∀ a : Fin 3,
      IsLeast ((fun y => MaxCirc.eval y (monRootCirc m a)) '' Set.Icc l u) (l a) ∧
        IsGreatest ((fun y => MaxCirc.eval y (monRootCirc m a)) '' Set.Icc l u) (u a)) ∧
    (∀ (x : ℕ → Fin 3 → ℝ × ℝ) (k : ℕ) (a : Fin 3),
      monAliasVec (monRootCirc m) (x k) a
        = some ((monRun false (monRootCirc m) x k).lo (x k) a,
            (monRun false (monRootCirc m) x k).hi (x k) a)) ∧
    ∀ K, monAliasWork (monRootCirc m) K = 3 * m + 4 * K + 4 := by
  have hal : ∀ a : Fin 3, (monAlias (monRootCirc m a)).1 = some a :=
    fun a => (monAlias_spec _ a).mpr (monRootCirc_onlyTerm m a)
  have hvec : ∀ (x : Fin 3 → ℝ × ℝ) (a : Fin 3),
      monAliasVec (monRootCirc m) x a = some ((monRootCirc m a).ival x) := by
    intro x a
    unfold monAliasVec
    rw [hal a, MaxCirc.ival_of_onlyTerm x (monRootCirc_onlyTerm m a)]
    rfl
  refine ⟨hvec, ?_, ?_, ?_⟩
  · intro l u hlu a
    exact MaxCirc.interval_of_onlyTerm (monRootCirc_onlyTerm m a) hlu
  · intro x k a
    have hinv := monRun_inv false (monRootCirc m) x k
    have ha : a ∈ (monRun false (monRootCirc m) x k).act := by
      rw [monRun_act_false]
      exact mem_univ a
    rw [hvec, hinv.lo_eq ha, hinv.hi_eq ha]
  · intro K
    unfold monAliasWork
    simp only [monAlias_cost]
    rw [monRootCirc_size hm, Finset.sum_const, Finset.card_range, smul_eq_mul, Fintype.card_fin]
    ring

end Escape

/-! ### Monitor work on the two-exit funnel (`thm:onpolicy-uct`, Step 4) -/

section FunnelWork

/-- Balanced binary fan-out with `m` unary leaves over the terminal `z`. -/
def monFanZ {Z : Type*} (z : Z) : ℕ → ℕ → MaxCirc Z
  | 0, _ => .unary (.term z)
  | d + 1, m =>
      if m ≤ 1 then .unary (.term z)
      else .bin (monFanZ z d ((m + 1) / 2)) (monFanZ z d (m / 2))

theorem monFanZ_onlyTerm {Z : Type*} (z : Z) : ∀ d m, MaxCirc.OnlyTerm z (monFanZ z d m)
  | 0, _ => rfl
  | d + 1, m => by
      unfold monFanZ
      split_ifs
      · rfl
      · exact ⟨monFanZ_onlyTerm z d _, monFanZ_onlyTerm z d _⟩

theorem monFanZ_count {Z : Type*} (z : Z) : ∀ d m, 1 ≤ m → m ≤ 2 ^ d →
    (monFanZ z d m).monEdges + 2 = 3 * m ∧ (monFanZ z d m).monSize + 1 = 3 * m
  | 0, m, h1, h2 => by
      have : m = 1 := by
        rw [pow_zero] at h2
        omega
      subst this
      exact ⟨rfl, rfl⟩
  | d + 1, m, h1, h2 => by
      unfold monFanZ
      split_ifs with hm
      · have : m = 1 := by omega
        subst this
        exact ⟨rfl, rfl⟩
      · rw [pow_succ] at h2
        obtain ⟨a1, a2⟩ := monFanZ_count z d ((m + 1) / 2) (by omega) (by omega)
        obtain ⟨b1, b2⟩ := monFanZ_count z d (m / 2) (by omega) (by omega)
        constructor
        · show (monFanZ z d ((m + 1) / 2)).monEdges + (monFanZ z d (m / 2)).monEdges + 2 + 2
            = 3 * m
          omega
        · show (monFanZ z d ((m + 1) / 2)).monSize + (monFanZ z d (m / 2)).monSize + 1 + 1
            = 3 * m
          omega

/-- The two fans of the two-exit funnel of width `m`: `m` bottom-layer parents over each of
the exits `2` and `3`. -/
def monFunnelFan (m : ℕ) (z : Fin 4) : MaxCirc (Fin 4) := monFanZ z (Nat.clog 2 m) m

/-- The two-exit dominated funnel: root actions `b = 0` and `a' = 1` are terminal vertices
(terminals `0` and `1`), and `C = 2` is a binary split over two fans whose exits are the
terminals `2` and `3`. -/
def monFunnelCirc (m : ℕ) (a : Fin 3) : MaxCirc (Fin 4) :=
  if a = 2 then .bin (monFunnelFan m 2) (monFunnelFan m 3) else .term (Fin.castSucc a)

theorem monFunnelCirc_two (m : ℕ) :
    monFunnelCirc m 2 = .bin (monFunnelFan m 2) (monFunnelFan m 3) := by simp [monFunnelCirc]

theorem monFunnelCirc_size {m : ℕ} (hm : 1 ≤ m) :
    ∑ a, (monFunnelCirc m a).monSize = 6 * m + 1 := by
  have h2 := (monFanZ_count (2 : Fin 4) _ m hm (Nat.le_pow_clog (by norm_num) m)).2
  have h3 := (monFanZ_count (3 : Fin 4) _ m hm (Nat.le_pow_clog (by norm_num) m)).2
  have e0 : monFunnelCirc m 0 = .term 0 := by simp [monFunnelCirc]
  have e1 : monFunnelCirc m 1 = .term 1 := by simp [monFunnelCirc]
  rw [Fin.sum_univ_three, e0, e1, monFunnelCirc_two]
  show 1 + 1 + ((monFanZ (2 : Fin 4) (Nat.clog 2 m) m).monSize
    + (monFanZ (3 : Fin 4) (Nat.clog 2 m) m).monSize + 1) = 6 * m + 1
  omega

open Classical in
/-- **Step 4 of the proof of `thm:selective-separation`: the cost-model half.**  On the
two-exit funnel of width `m`, for every sequence `x` of terminal tables and `K` updates:

* *eager*: every update that changes the interval of an exit is delivered across the `m`
  incidences of that exit's bottom-layer parents, so
  `m · #{k < K : an exit interval changes at step k} ≤ W_eager`;
* *selective*: if the funnel action `C` is not active after step `k0`, then
  `W_selective ≤ (12 k0 + 12) m + 16 K + 8`.

This is monitor work (build, updates, waves, queries, retirement, disposal); the sampler's
traversal is not included.  With `K = τ ≤ m`, a retirement step `k0 = O(1)` and `Ω(log m)`
exit-changing revisits it gives `O(m)` versus `Ω(m log m)`; those three facts about the
recursive UCT process are not proved here. -/
theorem funnel_work {m : ℕ} (hm : 1 ≤ m) (x : ℕ → Fin 4 → ℝ × ℝ) (ε : ℝ) (K : ℕ) :
    (m * ((range K).filter (fun k => x (k + 1) 2 ≠ x k 2 ∨ x (k + 1) 3 ≠ x k 3)).card
      ≤ monWork false (monFunnelCirc m) x ε K) ∧
    ∀ k0, (∀ k, k0 < k → (2 : Fin 3) ∉ (monRun true (monFunnelCirc m) x k).act) →
      monWork true (monFunnelCirc m) x ε K ≤ (12 * k0 + 12) * m + 16 * K + 8 := by
  have hc2 := monFanZ_count (2 : Fin 4) _ m hm (Nat.le_pow_clog (by norm_num) m)
  have hc3 := monFanZ_count (3 : Fin 4) _ m hm (Nat.le_pow_clog (by norm_num) m)
  have hG := monFunnelCirc_size hm
  constructor
  · rw [monWork_false_eq]
    have hstep : ∀ k, (if x (k + 1) 2 ≠ x k 2 ∨ x (k + 1) 3 ≠ x k 3 then m else 0)
        ≤ ∑ a, monDelivCost (x k) (x (k + 1)) (monFunnelCirc m a) := by
      intro k
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun a => monDelivCost (x k) (x (k + 1)) (monFunnelCirc m a))
        (fun _ _ => Nat.zero_le _) (mem_univ (2 : Fin 3)))
      show _ ≤ monDelivCost (x k) (x (k + 1)) (monFunnelCirc m 2)
      rw [monFunnelCirc_two]
      refine le_trans ?_ (monDeliv_le_cost _ _ _)
      have hsplit : monDeliv (x k) (x (k + 1)) (monFunnelFan m 2)
            + monDeliv (x k) (x (k + 1)) (monFunnelFan m 3)
          ≤ monDeliv (x k) (x (k + 1)) (.bin (monFunnelFan m 2) (monFunnelFan m 3)) := by
        show _ ≤ monDeliv (x k) (x (k + 1)) (monFunnelFan m 2)
          + monDeliv (x k) (x (k + 1)) (monFunnelFan m 3) + _ + _
        omega
      split_ifs with hcond
      · rcases hcond with h2 | h3
        · have := monDeliv_of_onlyTerm_ne h2 (monFunnelFan m 2) (monFanZ_onlyTerm _ _ _)
          have e : (monFunnelFan m 2).monEdges + 2 = 3 * m := hc2.1
          omega
        · have := monDeliv_of_onlyTerm_ne h3 (monFunnelFan m 3) (monFanZ_onlyTerm _ _ _)
          have e : (monFunnelFan m 3).monEdges + 2 = 3 * m := hc3.1
          omega
      · exact Nat.zero_le _
    have hsum : m * ((range K).filter (fun k => x (k + 1) 2 ≠ x k 2 ∨ x (k + 1) 3 ≠ x k 3)).card
        = ∑ k ∈ range K, (if x (k + 1) 2 ≠ x k 2 ∨ x (k + 1) 3 ≠ x k 3 then m else 0) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
        mul_comm]
    rw [hsum]
    exact le_trans (Finset.sum_le_sum (fun k _ => hstep k)) (Nat.le_add_left _ _)
  · intro k0 hret
    rw [monWork_true_eq, hG]
    have hcard : ∀ k, (monRun true (monFunnelCirc m) x k).act.card ≤ 3 := fun k => by
      have := Finset.card_le_univ (monRun true (monFunnelCirc m) x k).act
      rwa [Fintype.card_fin] at this
    have h5 : ∑ k ∈ range K, 5 * (monRun true (monFunnelCirc m) x k).act.card ≤ 15 * K := by
      have : ∑ k ∈ range K, 5 * (monRun true (monFunnelCirc m) x k).act.card
          ≤ ∑ _k ∈ range K, 15 :=
        Finset.sum_le_sum (fun k _ => by have := hcard k; omega)
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
      omega
    have hw : ∑ k ∈ range K, ∑ a ∈ (monRun true (monFunnelCirc m) x (k + 1)).act,
          monDelivCost (x k) (x (k + 1)) (monFunnelCirc m a) ≤ k0 * (12 * m) := by
      refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (sum_ite_lt_le K k0 (12 * m))
      by_cases hk : k < k0
      · rw [ite_eq_left hk]
        have hterm : ∀ a : Fin 3, a ≠ 2 →
            monDelivCost (x k) (x (k + 1)) (monFunnelCirc m a) = 0 := by
          intro a ha
          have : monFunnelCirc m a = .term (Fin.castSucc a) := by simp [monFunnelCirc, ha]
          rw [this]
          rfl
        refine le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) ?_
        rw [Fin.sum_univ_three, hterm 0 (by decide), hterm 1 (by decide), monFunnelCirc_two]
        have h1 := monDelivCost_le_two (x k) (x (k + 1))
          (.bin (monFunnelFan m 2) (monFunnelFan m 3))
        have h2 := monDeliv_le_edges (x k) (x (k + 1))
          (.bin (monFunnelFan m 2) (monFunnelFan m 3))
        have e : (MaxCirc.bin (monFunnelFan m 2) (monFunnelFan m 3)).monEdges
            = (monFunnelFan m 2).monEdges + (monFunnelFan m 3).monEdges + 2 := rfl
        have e2 : (monFunnelFan m 2).monEdges + 2 = 3 * m := hc2.1
        have e3 : (monFunnelFan m 3).monEdges + 2 = 3 * m := hc3.1
        omega
      · rw [ite_eq_right hk]
        have hC := hret (k + 1) (by omega)
        refine le_of_eq (Finset.sum_eq_zero (fun a ha => ?_))
        have ha2 : a ≠ 2 := fun e => hC (e ▸ ha)
        have : monFunnelCirc m a = .term (Fin.castSucc a) := by simp [monFunnelCirc, ha2]
        rw [this]
        rfl
    have hc := hcard K
    have e : (12 * k0 + 12) * m = k0 * (12 * m) + 12 * m := by ring
    omega

end FunnelWork

end

end JointRootCert
